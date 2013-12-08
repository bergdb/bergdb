package frans;

/**
 * Class to test access time (latency) for cache and RAM.
 * Sequential access and random access of values in a long[] array.
 * 
 * @author Frans Lundberg
 */
public class MemoryAccess {
    static final int SIZE_CACHE = 100000;           // 100003 is prime. Total: 0.8 MB.
    static final long REPS1_CACHE = 10 * 1000;      // for seq
    static final long REPS2_CACHE = 100 * 1000000;  // for random
    static final int SIZE_RAM = 500 * SIZE_CACHE;   // 400 MB of data
    static final long REPS1_RAM = 10;               // for seq
    static final long REPS2_RAM = 10 * 1000000;     // for random 
    
    /**
     * Sequential memory accesses to a long[] array. 
     * 'size' must be SIZE_CACHE or SIZE_RAM.
     */
    Result seq(final int size) {
        long[] data = new long[size];
        
        for (int i = 0; i < data.length; i++) {
            data[i] = 1;
        }
        
        long t0 = 0;
        long sum = 0;
        long count;
        
        t0 = System.nanoTime();
        
        if (size == SIZE_CACHE) {
            count = SIZE_CACHE * REPS1_CACHE;
            for (int k = 0; k < REPS1_CACHE; k++) {
                for (int i = 0; i < SIZE_CACHE; i++) {                
                    sum += data[i];
                }
            }
        } else if (size == SIZE_RAM) {
            count = SIZE_RAM * REPS1_RAM;
            for (int k = 0; k < REPS1_RAM; k++) {
                for (int i = 0; i < SIZE_RAM; i++) {                
                    sum += data[i];
                }
            }
        } else {
            throw new Error("Bad size: " + size);
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        return new Result(count, time, sum);
    }
    
    
    /**
     * Random memory access to a long[] array. 
     * 'size' must be SIZE_CACHE or SIZE_RAM.
     */
    Result random(final int size) {
        long[] data = new long[size];
        long t0;
        long sum = 0;
        long index = 0;
        long count;
        
        for (int i = 0; i < size; i++) {
            data[i] = 1L;
        }
        
        t0 = System.nanoTime();
        
        if (size == SIZE_CACHE) {
            count = REPS2_CACHE;
            for (int k = 0; k < REPS2_CACHE; k++) {             
                sum += data[(int)(index % SIZE_CACHE)];
                index += 836413;
            }
        } else if (size == SIZE_RAM) {
            count = REPS2_RAM;
            for (int k = 0; k < REPS2_RAM; k++) {
                sum += data[(int)(index % SIZE_RAM)];
                index += 836413;
            }
        } else {
            throw new Error("Bad size: " + size);
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        return new Result(count, time, sum);
    }
    
    void runTest(String name, TestMethod test) {
        int reps = 8;
        double minTime = Double.MAX_VALUE;
        Result winner = null;
        
        System.out.println("---- " + name + " ----");
        
        for (int i = 0; i < reps; i++) {
            Result res = test.run();
            if (res.time < minTime) {
                winner = res;
            }
        }
        
        System.out.println(winner.toString());
    }
    
    /** To store the result. */
    static class Result {
        long count;
        long sum;
        double time;
        
        Result(long count, double time, long sum) {
            this.count = count;
            this.time = time;
            this.sum = sum;
        }
        
        public String toString() {
            double nanos = (time * 1e9) / count;
            return String.format("Access time %.2f ns, time: %.3f s (sum:%d).\n", nanos, time, sum);
        }
    }
    
    static interface TestMethod {
        public Result run();
    }
    
    void go() {
        runTest("cacheSeq", new TestMethod() {
            public Result run() {
                return seq(SIZE_CACHE);
            }
        });
        
        runTest("cacheRan", new TestMethod() {
            public Result run() {
                return random(SIZE_CACHE);
            }
        });
        
        runTest("ramSeq", new TestMethod() { 
            public Result run() {
                return seq(SIZE_RAM);
            }
        });
        
        runTest("ramRan", new TestMethod() {
            public Result run() {
                return random(SIZE_RAM);
            }
        });
    }
    
    public static void main(String[] args) {
        new MemoryAccess().go();
    }
}

/*
131106
======

"sequential" / "random" access are better terms. Now used.
Refactored. Result:

    Test        Access time
    cacheSeq     0.33 ns,  0.69 cycles
    cacheRan     3.16 ns,  6.64 cycles
    ramSeq       0.56 ns,  1.37 cycles
    ramRan      20.07 ns, 42.16 cycles

On my computer "Cissi":
    Ubuntu 12.04, CPU: Intel(R) Core(TM) i7-3687U CPU @ 2.10GHz, Cache: 4096 KiB.
    Java version:
        Oracle JVM 1.7.0_25.
        Java HotSpot(TM) 64-Bit Server VM (build 23.25-b01, mixed mode)

sudo cat /proc/cpuinfo | grep "cache"   -->
  cache size    : 4096 KB
sudo cat /proc/cpuinfo | fgrep 'cpu MHz'
  Max freq: cpu MHz : 2101.000  <--> 0.476 ns / cycle
  
*/
