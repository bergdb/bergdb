package bergdb.nanotest;

import java.util.Locale;

/**
 * What a test needs to know of the platform it runs on (bergdb 006-18-03): whether it is
 * Android, a skip of a test that checks something only a JVM has, and whether a thread waits
 * for a lock, which java.lang.management tells on a JVM and Thread.getState() in part on
 * Android.
 *
 * <p>A test skips itself with skipOnAndroid(reason), at its start, before it makes anything
 * that it would have to stop. The runner counts it as skipped, neither passed nor failed, and
 * prints the reason (ConsoleUI). A test that checks what BergDB promises on Android too is
 * made to run there instead.</p>
 *
 * @author Frans Lundberg
 */
public final class Platform {
    private Platform() {}

    /** Thrown by a test that does not apply on this platform; see the class comment. */
    public static final class Skipped extends RuntimeException {
        private static final long serialVersionUID = 1L;

        public Skipped(String reason) {
            super(reason);
        }
    }

    private static final boolean ANDROID = android0();

    private static boolean android0() {
        String vm = System.getProperty("java.vm.name");     // "Dalvik" on ART
        return vm != null && vm.toLowerCase(Locale.US).contains("dalvik");
    }

    /** Whether this runs on Android. */
    public static boolean android() {
        return ANDROID;
    }

    /** Skips the test on Android: 'reason' says what it checks that only a JVM has. */
    public static void skipOnAndroid(String reason) {
        if (ANDROID) {
            throw new Skipped("not on Android: " + reason);
        }
    }

    /**
     * Whether 'thread' is in 'state' (WAITING, BLOCKED), waiting for or blocked on a lock
     * whose class name starts with 'lockClass', by one ThreadInfo of java.lang.management.
     * On Android, which lacks that package and so cannot tell the lock, whether the thread is
     * in 'state' (Thread.getState()).
     */
    public static boolean waitsFor(Thread thread, Thread.State state, String lockClass) {
        if (ANDROID) {
            return thread.getState() == state;
        }
        java.lang.management.ThreadInfo info =
                java.lang.management.ManagementFactory.getThreadMXBean().getThreadInfo(
                        thread.getId());
        return info != null && info.getThreadState() == state && info.getLockName() != null
                && info.getLockName().startsWith(lockClass);
    }
}
