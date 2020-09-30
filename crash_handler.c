/*
 * crash_handler.c - a program to record crashes into crash report files
 *
 * Copyright 2011,2012 Sony Network Entertainment
 *
 * Author: Tim Bird <tim.bird (at) am.sony.com>
 *
 * Lots of stuff copied from Android debuggerd:
 * system/debuggerd/debuggerd.c
**
** Copyright 2006, The Android Open Source Project
**
** Licensed under the Apache License, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     http://www.apache.org/licenses/LICENSE-2.0
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
*/
/************************
 *  Install this program as the crash_handler for a Linux system with:
 *  $ cp crash_handler /tmp
 *  $ /tmp/crash_handler install
 *  # 'tmp' can be any directory
 *  test with:
 *  $ /tmp/fault-test
 *  $ cat /tmp/crash_reports/crash_report_0x
 *  # where x is the latest crash_report
 ************************
*********************************************/

//#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <sys/ptrace.h>
#include <stdarg.h>
#include <signal.h>
#include <asm/ptrace.h>
#include <sys/wait.h>
#include <sys/user.h>
#include <sys/klog.h>
#include <dirent.h>

#include <libunwind-ptrace.h>

#include "utility.h"
#include "crash_handler.h"

#define VERSION 0
#define REVISION 8

/****************************************
 * compile-time configurable items
 ****************************************/
#define MAX_CRASH_REPORTS   32
#define CRASH_REPORT_DIR    "/var/crash_reports"
#define CRASH_REPORT_FILENAME   "crash_report"

#define DO_CRASH_JOURNAL    1
#define CRASH_JOURNAL_FILENAME  "/var/crash_journal"

/* set to 1 to save a full core file for each crash report */
#define DO_CORE_FILE    0

/****************************************/

#if DO_CRASH_JOURNAL
extern void record_crash_to_journal(char *filename, int pid, char *name);
#else
#define record_crash_to_journal(a,b,c)
#endif

#define BUF_SIZE 512
#define ROOT_UID 0
#define ROOT_GID 0

int report_fd = -1;
int ts_num = -1;
mapinfo stack_map;
int nerrors = 0;
int verbose = 1;
int print_names = 1;

static const int nerrors_max = 100;

enum
{
    INSTRUCTION,
    SYSCALL,
    TRIGGER
} trace_mode = SYSCALL;

#define panic(args...)                      \
    do { fprintf (stderr, args); ++nerrors; } while (0)

static int killed;

void klog_fmt(const char *fmt, ...)
{
    int fd;
    pid_t pid;
    char format[BUF_SIZE];
    char buf[BUF_SIZE];
    int len;

    va_list ap;
    va_start(ap, fmt);

    pid = getpid();
    fd = open("/dev/kmsg", O_WRONLY);
    if (fd < 0)
    {
        va_end(ap);
        return;
    }

    sprintf(format, "<21> [%d] ", pid);
    strncat(format, fmt, BUF_SIZE);
    format[BUF_SIZE-1] = 0;

    vsnprintf(buf, sizeof(buf), format, ap);
    buf[BUF_SIZE-1] = 0;

    len = strlen(buf);
    write(fd, buf, len);
    close(fd);
    va_end(ap);
}


/* Log information into the crash_report */
void report_out(int rfd, const char *fmt, ...)
{
    char buf[BUF_SIZE];

    va_list ap;
    va_start(ap, fmt);

    if (rfd >= 0)
    {
        int len;
        vsnprintf(buf, sizeof(buf), fmt, ap);
        len = strlen(buf);
        write(rfd, buf, len);
    }

    va_end(ap);
}

#define typecheck(x,y) {    \
    typeof(x) __dummy1;     \
    typeof(y) __dummy2;     \
    (void)(&__dummy1 == &__dummy2); }


/* Similar to getline(), except gets process pid task IDs.
 * Returns positive (number of TIDs in list) if success,
 * otherwise 0 with errno set. */
size_t get_tids(pid_t **const listptr, size_t *const sizeptr, const pid_t pid)
{
    char     dirname[64];
    DIR     *dir;
    pid_t   *list;
    size_t   size, used = 0;

    if (!listptr || !sizeptr || pid < (pid_t)1)
    {
        errno = EINVAL;
        return (size_t)0;
    }

    if (*sizeptr > 0)
    {
        list = *listptr;
        size = *sizeptr;
    }
    else
    {
        list = *listptr = NULL;
        size = *sizeptr = 0;
    }

    if (snprintf(dirname, sizeof dirname, "/proc/%d/task/", (int)pid) >= (int)sizeof dirname)
    {
        errno = ENOTSUP;
        return (size_t)0;
    }

    dir = opendir(dirname);
    if (!dir)
    {
        errno = ESRCH;
        return (size_t)0;
    }

    while (1)
    {
        struct dirent *ent;
        int            value;
        char           dummy;

        errno = 0;
        ent = readdir(dir);
        if (!ent)
        {
            break;
        }

        /* Parse TIDs. Ignore non-numeric entries. */
        if (sscanf(ent->d_name, "%d%c", &value, &dummy) != 1)
        {
            continue;
        }

        /* Ignore obviously invalid entries. */
        if (value < 1)
        {
            continue;
        }

        /* Make sure there is room for another TID. */
        if (used >= size)
        {
            size = (used | 127) + 128;
            list = realloc(list, size * sizeof list[0]);

            if (!list)
            {
                closedir(dir);
                errno = ENOMEM;
                return (size_t)0;
            }

            *listptr = list;
            *sizeptr = size;
        }

        /* Add to list. */
        list[used++] = (pid_t)value;
    }

    if (errno)
    {
        const int saved_errno = errno;
        closedir(dir);
        errno = saved_errno;
        return (size_t)0;
    }

    if (closedir(dir))
    {
        errno = EIO;
        return (size_t)0;
    }

    /* None? */
    if (used < 1)
    {
        errno = ESRCH;
        return (size_t)0;
    }

    /* Make sure there is room for a terminating (pid_t)0. */
    if (used >= size)
    {
        size = used + 1;
        list = realloc(list, size * sizeof list[0]);
        if (!list)
        {
            errno = ENOMEM;
            return (size_t)0;
        }
        *listptr = list;
        *sizeptr = size;
    }

    /* Terminate list; done. */
    list[used] = (pid_t)0;
    errno = 0;
    return used;
}

/*
 * find_and_open_crash_report - find an available crash report slot, if any,
 * of the form 'crash_report_XX where XX is 00 to MAX_CRASH_REPORTS-1,
 * inclusive. If no file is available, we reuse the least-recently-modified
 * file.
 */
static int find_and_open_crash_report(void)
{
    time_t mtime = ULONG_MAX;
    struct stat sb;
    char path[128];
    int fd, i, oldest = 0;

    /*
     * XXX: Android stat.st_mtime may not be time_t.
     * This check will generate a warning in that case.
     */
    typecheck(mtime, sb.st_mtime);

    /* FIXTHIS - should probably create leading directories also */
    mkdir(CRASH_REPORT_DIR, 0755);

    /*
     * In a single wolf-like pass, find an available slot and, in case none
     * exist, find and record the least-recently-modified file.
     */
    for (i = 0; i < MAX_CRASH_REPORTS; i++)
    {
        snprintf(path, sizeof(path),
        CRASH_REPORT_DIR"/"CRASH_REPORT_FILENAME"_%02d", i);
        ts_num = i;

        if (!stat(path, &sb))
        {
            if (sb.st_mtime < mtime)
            {
                oldest = i;
                mtime = sb.st_mtime;
            }
            continue;
        }

        if (errno != ENOENT)
        {
            continue;
        }

        fd = open(path, O_CREAT | O_EXCL | O_WRONLY, 0644);
        if (fd < 0)
        {
            continue;   /* raced ? */
        }

        fchown(fd, ROOT_UID, ROOT_GID);
        return fd;
    }

    /* we didn't find an available file, so we clobber the oldest one */
    snprintf(path, sizeof(path), CRASH_REPORT_DIR"/"CRASH_REPORT_FILENAME"_%02d", i);
    ts_num = oldest;

    fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0644);
    fchown(fd, ROOT_UID, ROOT_GID);

    return fd;
}

void dump_task_info(pid_t pid, unsigned sig, unsigned uid, unsigned gid)
{
    char path[256];
    char buffer[1024];
    char cmdline[1024];
    char name[20];
    char *s;
    int fd;
    int count;

    strcpy(cmdline, "UNKNOWN");
    sprintf(path, "/proc/%d/cmdline", pid);
    fd = open(path, O_RDONLY);

    if (fd >= 0)
    {
        count = read(fd, buffer, 1024);
        DLOG("count=%d\n", count);
        strncpy(cmdline, buffer, 1024);
        cmdline[1023] = 0;
        DLOG("cmdline=%s\n", cmdline);
        close(fd);
    }
    else
    {
        DLOG("problem opening %s\n", path);
    }

    sprintf(path, "/proc/%d/status", pid);
    fd = open(path, O_RDONLY);

    if (fd >= 0)
    {
        count = read(fd, buffer, 1024);
        DLOG("count=%d\n", count);
        /* first line is: Name:\t<name>\n */
        s = strchr(buffer, '\n');
        *s = 0;
        strcpy(name, buffer+6);
        DLOG("name=%s\n", name);
        close(fd);
    }
    else
    {
        DLOG("problem opening %s\n", path);
    }

    LOG("[task info]\n");
    LOG("pid: %u, uid: %u, gid: %u \n", pid, uid, gid);
    LOG("cmdline: %s\n", cmdline);
    LOG("name: %s\n", name);
    LOG("signal: %u\n", sig);
    LOG("================\n\n");

    record_crash_to_journal(CRASH_JOURNAL_FILENAME, pid, cmdline);
}

// 6f000000-6f01e000 rwxp 00000000 00:0c 16389419   /system/lib/libcomposer.so
// 012345678901234567890123456789012345678901234567890123456789
// 0         1         2         3         4         5

/*
 * parse a memory map line
 * Note: only executable maps are returned.  Other maps (data, stack, etc.)
 * are ignored
 */
mapinfo *parse_maps_line(char *line)
{
    mapinfo *mi;
    int len = strlen(line);

    if (len < 1)
    {
        return 0;
    }
    /* cut trailing \n */
    line[--len] = 0;

    if (len < 50)
    {
        return 0;
    }

    /* capture size of stack */
    if (strcmp(line + 49, "[stack]")==0)
    {
        stack_map.start = strtoul(line, 0, 16);
        stack_map.end = strtoul(line+9, 0, 16);
        strcpy(stack_map.name, line + 49);
        return 0;
    }

    /* ignore non-executable segments */
    if (line[20] != 'x')
    {
        return 0;
    }

    mi = malloc(sizeof(mapinfo) + (len - 47));
    if (mi == 0)
    {
        return 0;
    }

    mi->start = strtoul(line, 0, 16);
    mi->end = strtoul(line + 9, 0, 16);
    /* To be filled in by parse_exidx_info if the mapped section starts with
     * elf_header
     */
    mi->exidx_start = mi->exidx_end = 0;
    mi->next = 0;
    strcpy(mi->name, line + 49);

    return mi;
}

void free_mapinfo_list(mapinfo *milist)
{
    while (milist)
    {
        mapinfo *next = milist->next;
        free(milist);
        milist = next;
    }
}

mapinfo *get_mapinfo_list(pid_t pid)
{
    char data[1024];
    FILE *fp;
    mapinfo *milist = 0;

    sprintf(data, "/proc/%d/maps", pid);
    fp = fopen(data, "r");
    if (fp)
    {
        while (fgets(data, 1024, fp))
        {
            LOG(" %s", data);
            mapinfo *mi = parse_maps_line(data);
            if (mi)
            {
                mi->next = milist;
                milist = mi;
            }
        }
        fclose(fp);
    }

    return milist;
}

void dump_registers(int pid)
{
#if defined(__arm__)
    struct pt_regs r;
#elif defined(__x86_64__)
    struct user_regs_struct r;
#endif

    LOG("[registers]\n");
    if (ptrace(PTRACE_GETREGS, pid, 0, &r))
    {
        LOG("cannot get registers: %d (%s)\n", errno, strerror(errno));
        LOG("\n");
        return;
    }

#if defined(__arm__)
    LOG(" r0 %08x  r1 %08x  r2 %08x  r3 %08x\n",
         r.ARM_r0, r.ARM_r1, r.ARM_r2, r.ARM_r3);
    LOG(" r4 %08x  r5 %08x  r6 %08x  r7 %08x\n",
         r.ARM_r4, r.ARM_r5, r.ARM_r6, r.ARM_r7);
    LOG(" r8 %08x  r9 %08x  10 %08x  fp %08x\n",
         r.ARM_r8, r.ARM_r9, r.ARM_r10, r.ARM_fp);
    LOG(" ip %08x  sp %08x  lr %08x  pc %08x  cpsr %08x\n",
         r.ARM_ip, r.ARM_sp, r.ARM_lr, r.ARM_pc, r.ARM_cpsr);
#elif defined(__x86_64__)
    LOG(" r15 %08x  r14 %08x  r13 %08x  r12 %08x\n",
         r.r15, r.r14, r.r13, r.r12);
    LOG(" r11 %08x  r10 %08x  r9  %08x  r8 %08x\n",
         r.r11, r.r10, r.r9, r.r8);
    LOG(" rbp %08x  rbx %08x  rax %08x  rcx %08x\n",
         r.rbp, r.rbx, r.rax, r.rcx);
    LOG(" rdx %08x  rsi %08x  rdi %08x  orig_rax %08x rip %08x\n",
         r.rdx, r.rsi, r.rdi, r.orig_rax, r.rip);
    LOG(" cs  %08x  eflags %08x  rsp %08x  ss %08x fs_base %08x\n",
         r.cs, r.eflags, r.rsp, r.ss, r.fs_base);
    LOG(" gs_base %08x  ds %08x  es %08x   fs %08x gs %08x\n",
         r.gs_base, r.ds, r.es, r.fs, r.gs);
#else

#endif
    LOG("\n");
}

const char *get_signame(int sig)
{
    switch(sig)
    {
    case SIGILL:     return "SIGILL";
    case SIGABRT:    return "SIGABRT";
    case SIGBUS:     return "SIGBUS";
    case SIGFPE:     return "SIGFPE";
    case SIGSEGV:    return "SIGSEGV";
    case SIGSTKFLT:  return "SIGSTKFLT";
    default:         return "?";
    }
}

void dump_fault_addr(int pid, int sig)
{
    siginfo_t si;

    LOG("[exception info]\n");
    memset(&si, 0, sizeof(si));
    if (ptrace(PTRACE_GETSIGINFO, pid, 0, &si))
    {
        LOG("cannot get siginfo: %d (%s) \n", errno, strerror(errno));
    }
    else
    {
        LOG("signal %d (%s), fault addr %08x\n",
            sig, get_signame(sig), si.si_addr);
    }
    LOG("\n");
}

#if defined(__arm__)
int dump_pc_code(int pid)
{
    struct pt_regs r;
    int *start, *end;
    int val;
    int *i;

    LOG("[code around PC]\n");
    if (ptrace(PTRACE_GETREGS, pid, 0, &r))
    {
        LOG("cannot get registers: %d (%s)\n", errno, strerror(errno));
        return;
    }

    start = (int *)r.ARM_pc-0x10;
    end = (int *)r.ARM_pc+0x10;
    for (i = start; i < end; i++)
    {
        val = get_remote_word(pid, i);
        LOG("0x%08lx: %08lx", (unsigned long)i, val);
        LOG((unsigned long)i==r.ARM_pc ? " <-- PC\n" : "\n");
    }
}
#endif

#define MAX_LOG_TAIL_TO_SAVE    4000

void dump_klog_tail()
{
    char *buffer;
    char *start;
    int size;
    int len;

    LOG("[kernel log]\n");

    size = klogctl(10, NULL, 0);
    buffer = malloc(size);
    if (!buffer)
    {
        return;
    }
    size = klogctl(3, buffer, size);
    start = buffer;

    /* put tail end of buffer into log */
    if (size > MAX_LOG_TAIL_TO_SAVE)
    {
        len = MAX_LOG_TAIL_TO_SAVE;
        start = buffer+size-len;
    }
    else
    {
        len = size;
    }

    /* FIXTHIS - it would be good to filter out crash_handler
     * log messages here
     */
    write(report_fd, start, len);
    free(buffer);
}

bool do_backtrace(pid_t pid, pid_t tid, unsigned sig)
{
    unw_word_t ip, sp, start_ip = 0, off;
    int n = 0, ret;
    unw_proc_info_t pi;
    unw_cursor_t c;
    char buf[512];
    size_t len;
    unw_addr_space_t addr_space = NULL;
    struct UPT_info *upt_info = NULL;

    char path[256];
    char thread_name[32];
    int fd;

    strcpy(thread_name, "UNKNOWN");
    sprintf(path, "/proc/%d/task/%d/comm", pid, tid);
    fd = open(path, O_RDONLY);

    if (fd >= 0)
    {
        char buffer[32];
        read(fd, buffer, 32);
        strncpy(thread_name, buffer, 32);
        thread_name[31] = 0;
        thread_name[strcspn(thread_name, "\n")] = 0;
        close(fd);
    }
    else
    {
        DLOG("Problem opening %s\n", path);
    }

    LOG("[thread]\n");
    LOG("name: %s\n", thread_name);
    LOG("tid: %d\n\n", tid);

    addr_space = unw_create_addr_space(&_UPT_accessors, 0);
    if (!addr_space)
    {
        LOG("unw_create_addr_space() failed");
        return false;
    }

    upt_info = (struct UPT_info*)_UPT_create(tid);

    if (!upt_info)
    {
        LOG("Failed to create upt info.");
        unw_destroy_addr_space(addr_space);
        return false;
    }

    if (sig)
    {
        dump_fault_addr(tid, sig); /* uses ptrace */
    }

    dump_registers(tid); /* uses ptrace */

#if defined(__arm__)
    dump_pc_code(tid); /* uses ptrace */
#endif

    LOG("[call stack]\n");

    ret = unw_init_remote(&c, addr_space, upt_info);
    if (ret < 0)
    {
        LOG("unw_init_remote() failed: ret=%d code=", ret);

        if (ret == UNW_EINVAL)
        {
            LOG("UNW_EINVAL\n");
        }
        else if (ret == UNW_EUNSPEC)
        {
            LOG("UNW_EUNSPEC\n");
        }
        else if (ret == UNW_EBADREG)
        {
            LOG("UNW_EBADREG\n");
        }
        else
        {
            LOG("UNKNOWN\n");
        }

        LOG("\n");

        _UPT_destroy(upt_info);
        unw_destroy_addr_space(addr_space);
        return false;
    }

    do
    {
        unw_word_t ip, sp, offset;
        char symbol[4096];

        if (unw_get_reg(&c, UNW_REG_IP, &ip) < 0)
        {
            LOG("ERROR: cannot read program counter\n");
            break;
        }

        if (unw_get_reg(&c, UNW_REG_SP, &sp) < 0)
        {
            LOG("ERROR: cannot read stack pointer\n");
            break;
        }

        if (unw_get_proc_name(&c, symbol, sizeof(symbol), &offset) < 0)
        {
            strcpy(symbol, "??");
        }

        LOG("#%-2d 0x%016" PRIxPTR " sp=0x%016" PRIxPTR " (%s+0x%" PRIxPTR ")\n",
            ++n,
            ip,
            sp,
            symbol,
            offset);
    } while (unw_step(&c) > 0);

    LOG("================\n\n");

    if (upt_info)
    {
        _UPT_destroy(upt_info);
    }

    if (addr_space)
    {
        unw_destroy_addr_space(addr_space);
    }

    return true;
}

int generate_crash_report(pid_t pid, unsigned sig, unsigned uid, unsigned gid)
{
    mapinfo *milist;

    pid_t *tid = 0;
    size_t tids = 0;
    size_t tids_max = 0;
    size_t t = 0;
    long   r;

    dump_task_info(pid, sig, uid, gid); /* uses /proc */

    LOG("[memory maps]\n");
    /* get_mapinfo_list retrieves list and outputs to LOG */
    milist = get_mapinfo_list(pid); /* uses /proc */
    LOG("================\n\n");

    if (!milist)
    {
        LOG("crash_handler:  failed to load memory maps\n");
    }

    // Sieze main thead first
    if (ptrace(PTRACE_SEIZE, pid, (void *)0, (void *)0) != 0)
    {
        LOG("crash_handler:  failed to seize main thead, %s\n", strerror(errno));
        return 1;
    }

    // Put main thread into ptrace-stop state.
    if (ptrace(PTRACE_INTERRUPT, pid, (void *)0, (void *)0) != 0)
    {
        LOG("crash_handler:  failed to interrupt main thread, %s\n", strerror(errno));
        ptrace(PTRACE_DETACH, pid, (void *)0, (void *)0);
        return 1;
    }

    tids = get_tids(&tid, &tids_max, pid);
    if (!tids)
    {
        LOG("crash_handler:  failed to get list of thread ids\n");
    }

    for (t = 0; t < tids; t++)
    {
        // Skip main thread
        if (pid == tid[t])
        {
            continue;
        }

        do
        {
            r = ptrace(PTRACE_SEIZE, tid[t], (void *)0, (void *)0);
        }
        while (r == -1L && (errno == EBUSY || errno == EFAULT || errno == ESRCH));

        if (r == -1L)
        {
            LOG("crash_handler:  failed to attach to thread id, %s\n", strerror(errno));
            const int saved_errno = errno;
            while (t-- > 0)
            {
                do
                {
                    r = ptrace(PTRACE_DETACH, tid[t], (void *)0, (void *)0);
                }
                while (r == -1L && (errno == EBUSY || errno == EFAULT || errno == ESRCH));
            }
            tids = 0;
            errno = saved_errno;
            break;
        }

        // Put the task into ptrace-stop state.
        if (ptrace(PTRACE_INTERRUPT, tid[t], (void *)0, (void *)0) != 0)
        {
            LOG("crash_handler:  failed to interrupt thread id, %s\n", strerror(errno));
            continue;
        }
    }

    for (t = 0; t < tids; t++)
    {
        do_backtrace(pid, tid[t], pid == tid[t] ? sig : 0);
    }

    for (t = 0; t < tids; t++)
    {
        do
        {
            r = ptrace(PTRACE_DETACH, tid[t], (void *)0, (void *)0);
        }
        while (r == -1 && (errno == EBUSY || errno == EFAULT || errno == ESRCH));
    }
    tids = 0;

    dump_klog_tail();

    LOG("--- done ---\n");

    free_mapinfo_list(milist);

    return 0;
}


int main(int argc, char *argv[])
{
#if DO_CORE_FILE
    int tot, j;
    ssize_t nread;
    char buf[BUF_SIZE];
    char path[128];
    int core_out_fd;
#endif

    FILE *fp;

    pid_t pid;
    unsigned int sig;
    unsigned int uid;
    unsigned int gid;

    // check for install argument
    if (argc == 2 && strcmp(argv[1], "--install") == 0)
    {
        char actualpath[PATH_MAX];
        char *ptr;

        fp = fopen("/proc/sys/kernel/core_pattern", "w");
        if (!fp)
        {
            perror("Could not open core_pattern for installation\n");
            exit(1);
        }

        ptr = realpath(argv[0], actualpath);
        if (!ptr)
        {
            fprintf(stderr, "Couldn't find real path for %s\n", argv[0]);
            fclose(fp);
        }
        else
        {
            /* set the core_pattern */
            fprintf(fp, "|%s %%p %%s %%u %%g\n", actualpath);
            fclose(fp);
        }

        fp = fopen("/proc/sys/kernel/core_pipe_limit", "w");
        if (!fp)
        {
            perror("Could not open core_pipe_limit for installation\n");
            exit(1);
        }
        fprintf(fp, "1\n");
        fclose(fp);
        printf("Installation done\n");
        return 0;
    }

    if (argc == 2 && strcmp(argv[1], "--version") == 0)
    {
        printf("crash_handler v%d.%d\n", VERSION, REVISION);
        return 0;
    }

    if (argc < 3)
    {
        printf("Usage: crash_handler <pid> <sig> <uid> <gid>\n\n");
        printf("Under normal usage, the crash_handler is called directly\n");
        printf("by the Linux kernel, as is passed paramters as specified\n");
        printf("by /proc/sys/kernel/core_pattern.\n\n");

        printf("However, a few convenience options are provided:\n");
        printf("--install   Install crash_handler (register with kernel).\n");
        printf("            That is, to install the crash_handler program\n");
        printf("            on a system, copy the program to /tmp and do:\n");
        printf("              $ /tmp/crash_handler --install\n");
        printf("--version   show version information\n\n");
        return -1;
    }

    // parse args from command line
    pid = atoi(argv[1]);
    sig = atoi(argv[2]);
    uid = atoi(argv[3]);
    gid = atoi(argv[4]);

    report_fd = find_and_open_crash_report();

    // this MUST be done before reading the core from standard in
    generate_crash_report(pid, sig, uid, gid);

#if DO_CORE_FILE
    /* save the core file, alongside the crash_report file */
    snprintf(path, sizeof(path), CRASH_REPORT_DIR"/core_%02d", ts_num);
    core_out_fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0644);

    /* Count bytes in standard input (the core dump) */
    tot = 0;
    while ((nread = read(STDIN_FILENO, buf, BUF_SIZE)) > 0)
    {
        if (core_out_fd>=0)
        {
            write(core_out_fd, buf, nread);
        }
        tot += nread;
    }

    fprintf(fp, "Total bytes in core dump: %d\n", tot);
    LOG("Total bytes in core dump: %d\n", tot);

    if (core_out_fd >= 0)
    {
        close(core_out_fd);
    }
#endif  /* DO_CORE_FILE */

    if (report_fd >= 0)
    {
        fsync(report_fd);
        close(report_fd);
    }

    exit(EXIT_SUCCESS);
}
