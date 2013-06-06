package kissdb.test.java;

import java.util.HashMap;
import java.util.Random;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

/**
 * Memory requirements for storing many equal strings in Java.
 * 
 * @author Frans Lundberg
 */
public class StringMemory {
    
    @SuppressWarnings("unchecked")
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        int N = 1000;
        long m0, m1;
        String[] strings;
        
        strings = new String[N];
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            strings[i] = "Hello, my name is Frans Lundberg and " +
                    "I am a happy little guy living in Poland!";
        }
        m1 = usedMemory();
        c.report("memoryString", 1.0*(m1-m0)/N);
        c.report("longStringLength", strings[0].length());
        
        
        strings = new String[N];
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            strings[i] = "Hello, my name is Frans Lundberg and " +
                    "I am a happy little guy living in Poland!" + i;
        }
        m1 = usedMemory();
        c.report("memoryStringPlusI", 1.0*(m1-m0)/N);
        
        
        strings = new String[N];
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            strings[i] = "Hello, my name is Frans Lundberg and " +
                    "I am a happy little guy living in Poland!" + (i/10);
        }
        m1 = usedMemory();
        c.report("memoryStringPlusIDividedBy10", 1.0*(m1-m0)/N);
        
        
        Random random = new Random(0);
        strings = new String[N];
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            String s = "Hello, my name is Frans Lundberg and " +
                    "I am a happy little guy living in Poland!";
            if (random.nextDouble() < 0.50) {
                s = s + i;
            }
            strings[i] = s;
        }
        m1 = usedMemory();
        c.report("memoryStringSometimeIAdded", 1.0*(m1-m0)/N);
        
        
        strings = new String[N];
        String s = "Hello, my name is Frans Lundberg and " +
                "I am a happy little guy living in Poland!";
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            strings[i] = s + "";
        }
        m1 = usedMemory();
        c.report("memoryStringConcatEmpty", 1.0*(m1-m0)/N);
        
        
        // Lots of HashMaps representing "objects" with same field names.
        HashMap<String, Long>[] maps = new HashMap[N];
        
        HashMap<String, Long> map;
        @SuppressWarnings("unused")
        String s1 = "thisIsAnUnusuallyLongNameOfAField-thisFieldNameIsAlsoQuiteLong";
        
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            map = new HashMap<String, Long>();
            map.put("thisIsAnUnusuallyLongNameOfAField", new Long(i));
            //map.put(s1.split("-")[0], i);
            map.put("thisFieldNameIsAlsoQuiteLong", new Long(0));
            //map.put(s1.split("-")[1], new Long(0));
            maps[i] = map;
        }
        m1 = usedMemory();
        c.report("memoryPerHashMapWithLongKeyStrings", 1.0*(m1-m0)/N);
        
        
        maps = new HashMap[N];
        m0 = usedMemory();
        for (int i = 0; i < N; i++) {
            map = new HashMap<String, Long>();
            map.put("a", new Long(i));
            map.put("b", new Long(0));
            maps[i] = map;
        }
        m1 = usedMemory();
        c.report("memoryPerHashMapWithShortKeyStrings", 1.0*(m1-m0)/N);
    }
    
    private static long usedMemory() {
        Runtime r = Runtime.getRuntime();
        gc();
        return r.maxMemory() - r.freeMemory();
    }

    private static void gc() {
        for (int i = 0; i < 5; i++) {
            System.gc();
        }
    }
}

/*
Java does optimize String in a special way.
Sometimes it does not matter whether a key String is long or short.
Sometimes there is a difference.

Results of string concatenation, or strings returned from methods do not
seem to be optimized the same way as explicit strings in the source code.
*/