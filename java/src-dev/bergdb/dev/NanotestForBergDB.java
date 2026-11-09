package bergdb.dev;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.WeakHashMap;
import java.util.concurrent.CountDownLatch;

import bergdb.common.AssertStatus;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.CommandLine;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.IPack;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestRunner;

/**
 * Common BergDB code to run a set of nano tests from command line.
 * 
 * @author Frans Lundberg
 */
public class NanotestForBergDB {
    private final String[] args;
    private final Set<Class<?>> classes;
    private final Set<String> groups;
    private boolean checkStopped = false;
    
    public NanotestForBergDB(String[] args, IPack[] ipacks, Set<String> groups) {
        this.args = args;
        this.classes = createSetOfClasses(ipacks);
        this.groups = groups;
    }
    
    /**
     * Makes go() check, after the tests, that every database a test started has been
     * stopped (bergdb 005-55); Unit, F and Night use it. Nothing stops a database that is
     * dropped, as Db has no finalize(): a test that does not stop or close its database
     * leaves its storage threads, its user indexes' build and cleanup threads, its open files
     * and its memory until the JVM exits. See StoppedCheck.
     */
    public void checkDatabasesStopped() {
        checkStopped = true;
    }
    
    public void go() {
        if (args.length > 0 && args[0].equals("help")) {
            System.out.println(getHelp());
            return;
        }
        
        CommandLine c = new CommandLine(args);
        
        if (c.has("help")) {
            System.out.println(getHelp());
            return;
        }
        
        ConsoleUI ui = checkStopped ? new StoppedCheck() : new ConsoleUI();
        ui.applyOptions(c);
        
        System.out.print(getHeader());
        
        if (!AssertStatus.enabled()) {
            System.out.println("NOTE: assertions disabled, use -ea to enable.");
        }
        
        String classPatternString = ".*";
        if (c.hasOne("c")) {
            classPatternString = c.getOne("c");
        }
        
        String methodPatternString = ".*";
        if (c.has("m")) {
            methodPatternString = c.getOne("m");
        }
        
        Set<Class<?>> classesChosen = new ClassFilter(classPatternString).filter(classes);
        MethodFilter methodFilter = new MethodFilter(methodPatternString, groups);
        
        TestRunner testRunner = new TestRunner(ui, classesChosen, methodFilter);
        testRunner.run();
    }
    
    /**
     * Prints header, override if needed.
     */
    public String getHeader() {
        StringBuilder b = new StringBuilder();
        
        b.append("\n======== " + this.getClass().getSimpleName() + ": " + groupsToString() + " ========\n");
        
        String computer = Util.hostname();
        String time = Util.dateAndTime();
        String jvm = System.getProperty("java.vm.name") + " " + System.getProperty("java.runtime.version");
        
        if (jvm.startsWith("Java HotSpot")) {
            jvm = jvm.substring(5);
        }
        
        b.append("On " + computer + " " + time + ", " + jvm + "\n");
        
        return b.toString();
    }
    
    /**
     * Prints header, override if needed.
     */
    public String getHelp() {
        StringBuilder b = new StringBuilder();
        b.append("---- help ----\n");
        b.append("Options:\n");
        b.append("-c <classPattern>  A regexp for the name of the classes to include.\n");
        b.append("-m <methodPattern>  A regexp for the method names to include.\n");
        b.append("-s  Be silent (quiet)\n");
        b.append("-d  Print less, only dots and result.\n");
        b.append("-v  Be verbose\n");
        b.append("-vv  Be max verbose\n");
        b.append("-help  Print this help\n");
        b.append("\n");
        b.append("If methodPattern is missing, all test methods of the selected classes will run.\n");
        b.append("If classPattern is missing, all classes with test methods will be tested.\n");
        return b.toString();
    }
    
    private String groupsToString() {
        StringBuilder b = new StringBuilder();
        for (String g : groups) {
            b.append(g + " ");
        }
        
        return b.toString().trim();
    }
    
    private Set<Class<?>> createSetOfClasses(IPack[] ipacks) {
        Set<Class<?>> classes = new HashSet<Class<?>>();
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                classes.add(c);
            }
        }
        return classes;
    }
    
    /**
     * The check of checkDatabasesStopped() (bergdb 005-55). After each test it notes the
     * database threads that are alive, each with the test after which it was first seen: the
     * storage threads (BufferedStream's consumers, "BufferedStream-consumer-N"), the eviction
     * threads ("bergdb-evictor"), and since 2026-11-09 (bergdb 020-21, 4) the user indexes'
     * build and cleanup threads ("IndexBuild-NAME-GEN", "IndexCleanup-NAME-GEN"), which a
     * database's close ends. At the end, before the report, it waits at most 5 seconds for
     * the closes that stop() started (bergdb 005-35), then fails a last test,
     * databasesStopped, if any of those threads is still alive, with the tests that left
     * them.
     */
    private static class StoppedCheck extends ConsoleUI {
        private static final long WAIT_MILLIS = 5000;
        private final Map<Thread, String> testOf = new WeakHashMap<Thread, String>();
        private String test;
        
        public void testAboutToRun(String longMethodName) {
            test = longMethodName;
            super.testAboutToRun(longMethodName);
        }
        
        public void testDone(Throwable t) {
            for (Thread th : databaseThreads()) {
                if (!testOf.containsKey(th)) {
                    testOf.put(th, test);
                }
            }
            super.testDone(t);
        }
        
        public void done() {
            classAboutToRun(NanotestForBergDB.class);
            testAboutToRun(NanotestForBergDB.class.getName() + ".databasesStopped");
            testDone(databasesStopped());
            classDone();
            super.done();
        }
        
        /** Null if no database thread is alive within WAIT_MILLIS. */
        private Throwable databasesStopped() {
            long end = System.currentTimeMillis() + WAIT_MILLIS;
            List<Thread> alive = databaseThreads();
            while (!alive.isEmpty() && System.currentTimeMillis() < end) {
                try {
                    Thread.sleep(50);
                } catch (InterruptedException e) {
                    return e;
                }
                alive = databaseThreads();
            }
            
            if (alive.isEmpty()) {
                return null;
            }
            
            Map<String, Integer> byTest = new TreeMap<String, Integer>();
            for (Thread th : alive) {
                String name = testOf.get(th) == null ? "no test" : testOf.get(th);
                Integer count = byTest.get(name);
                byTest.put(name, count == null ? 1 : count + 1);
            }
            return new AssertionError(alive.size() + " storage, eviction or index threads alive "
                    + "after the tests: databases not stopped, by the test that left them: "
                    + byTest);
        }
        
        /** The live threads of databases: storage, eviction, index builds and cleanups. */
        private static List<Thread> databaseThreads() {
            List<Thread> list = new ArrayList<Thread>();
            for (Thread th : Thread.getAllStackTraces().keySet()) {
                String name = th.getName();
                if (name.startsWith("BufferedStream-consumer-") || name.equals("bergdb-evictor")
                        || name.startsWith("IndexBuild-") || name.startsWith("IndexCleanup-")) {
                    list.add(th);
                }
            }
            return list;
        }
    }
    
    
    // ======== Tests ========
    
    /**
     * bergdb 020-21, 4 (020-13, section 6, recommendation 3): the check finds a user index's
     * build and cleanup threads ("IndexBuild-NAME-GEN", "IndexCleanup-NAME-GEN"), which a
     * database runs in the background and its close ends, as it finds the storage and
     * eviction threads. It did not, so a test that left a build running passed the gate.
     */
    @Nano
    private static void testIndexThreadsChecked() throws InterruptedException {
        final CountDownLatch done = new CountDownLatch(1);
        List<Thread> threads = new ArrayList<Thread>();
        for (String name : new String[] {"IndexBuild-t-1", "IndexCleanup-t-1"}) {
            Thread th = new Thread(() -> {
                try {
                    done.await();
                } catch (InterruptedException e) {
                    // Ends.
                }
            }, name);
            th.setDaemon(true);
            th.start();
            threads.add(th);
        }
        try {
            List<Thread> found = StoppedCheck.databaseThreads();
            for (Thread th : threads) {
                Assert.assertTrue(th.getName() + " not found", found.contains(th));
            }
        } finally {
            done.countDown();
            for (Thread th : threads) {
                th.join();
            }
        }
    }
}
