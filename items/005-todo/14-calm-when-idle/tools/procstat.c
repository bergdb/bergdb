/*
 * 005-13, follow-up: what an idle process costs. Prints, for each PID, the counters of
 * proc_pid_rusage (RUSAGE_INFO_V6): CPU time (user + system, ns), the part on P-cores,
 * package idle wakeups and interrupt wakeups, instructions, cycles and the energy the
 * kernel attributes to the process (ri_energy_nj, nJ). The counters are cumulative since
 * the process started; take two snapshots and subtract.
 * Build: cc -O2 -o procstat procstat.c      Usage: procstat PID...
 */
#include <libproc.h>
#include <mach/mach_time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>

int main(int argc, char **argv) {
    mach_timebase_info_data_t tb;
    mach_timebase_info(&tb);
    for (int i = 1; i < argc; i++) {
        int pid = atoi(argv[i]);
        struct rusage_info_v6 ri;
        if (proc_pid_rusage(pid, RUSAGE_INFO_V6, (rusage_info_t *) &ri) != 0) {
            printf("pid=%d error\n", pid);
            continue;
        }
        /* ri_user_time and ri_system_time are in mach absolute time units. */
        unsigned long long cpu = (ri.ri_user_time + ri.ri_system_time) * tb.numer / tb.denom;
        unsigned long long pcpu = (ri.ri_user_ptime + ri.ri_system_ptime) * tb.numer / tb.denom;
        printf("pid=%d cpu_ns=%llu pcpu_ns=%llu pkg_idle_wkups=%llu interrupt_wkups=%llu "
               "instructions=%llu cycles=%llu energy_nj=%llu penergy_nj=%llu billed_energy=%llu "
               "raw_user=%llu raw_system=%llu timebase=%u/%u\n",
               pid, cpu, pcpu, (unsigned long long) ri.ri_pkg_idle_wkups,
               (unsigned long long) ri.ri_interrupt_wkups, (unsigned long long) ri.ri_instructions,
               (unsigned long long) ri.ri_cycles, (unsigned long long) ri.ri_energy_nj,
               (unsigned long long) ri.ri_penergy_nj, (unsigned long long) ri.ri_billed_energy,
               (unsigned long long) ri.ri_user_time, (unsigned long long) ri.ri_system_time,
               tb.numer, tb.denom);
    }
    return 0;
}
