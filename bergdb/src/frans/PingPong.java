package frans;

import java.io.PrintStream;
import java.util.Random;

/**
 * Class to test access time (latency) from Java to: 
 * cache and RAM. Liniear order and "random" order of memory access.
 * 
 * @author Frans Lundberg
 */
public class PingPong {
    PrintStream out = System.out;
    
    static final int DATA_SIZE_CACHE = 100003;
    static final int DATA_SIZE_RAM = 500 * DATA_SIZE_CACHE;
    
    /**
     * Access to data in cache (800k) sequentially.
     */
    void cache1() {
        long[] data = new long[DATA_SIZE_CACHE];     
            // Fits comfortable in Cissi's 4096 kB cache.
            // 100003 is a prime number.
        
        Random r = new Random(0);
        
        for (int i = 0; i < data.length; i++) {
            //data[i] = r.nextLong();
            data[i] = 1;
        }
        
        int reps = 20000;
        long t0 = 0;
        long sum = 0;
        
        t0 = System.nanoTime();
        
        for (int k = 0; k < reps; k++) {
            for (int i = 0; i < DATA_SIZE_CACHE - 8; ) {                
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        long count = reps * (DATA_SIZE_CACHE - 8);
        
        out.println("---- cache1() ----");
        out.printf( "Access time %.3g s, time: %.6f s (sum:%d, count:%d).\n", time / count, time, sum, count);
    }
    
    
    /**
     * Measures random access time to access 64-bit of data in a 800k byte 
     * large array of longs.
     */
    void cache2() {
        long[] data = new long[DATA_SIZE_CACHE];     
            // Fits comfortable in Cissi's 4096 kB cache.
            // 100003 is a prime number.
            //  83641 is also prime. 
        
        Random r = new Random(0);
        
        for (int i = 0; i < data.length; i++) {
            //data[i] = r.nextLong();
            data[i] = 1;
        }
        
        int index = 200;
        int n = 50*1000000;
        long t0;
        long sum = 0;
        
        t0 = System.nanoTime();
        
        for (int i = 0; i < n; i++) {
            index = (index + 83641) % DATA_SIZE_CACHE;
            sum += data[index];
            
            index = (index + 83641) % DATA_SIZE_CACHE;
            sum += data[index];
            
            index = (index + 83641) % DATA_SIZE_CACHE;
            sum += data[index];
            
            index = (index + 83641) % DATA_SIZE_CACHE;
            sum += data[index];
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        long count = 4 * n;
        
        out.println("---- cache2() ----");
        out.printf( "Access time %.3g s, time: %.6f s (sum:%d).\n", time / count, time, sum);
    }
    
    /**
     * RAM access, ordered.
     */
    void ram1() {
        long[] data = new long[DATA_SIZE_CACHE * 500];   // 50M longs, 400M bytes
        
        Random r = new Random(0);
        
        for (int i = 0; i < data.length; i++) {
            //data[i] = r.nextLong();
            data[i] = 1L;
        }
        
        int reps = 10000;
        long t0 = 0;
        long sum = 0;
        
        t0 = System.nanoTime();
        
        for (int k = 0; k < reps; k++) {
            for (int i = 0; i < DATA_SIZE_CACHE - 8; ) {                
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
                sum += data[i++];
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        long count = reps * DATA_SIZE_CACHE;
        
        out.println("---- ram1() ----");
        out.printf( "Access time %.3g s, time: %.6f s (sum:%d, count:%d)\n", time / count, time, sum, count);
    }
    
    /**
     * RAM access, unordered.
     */
    void ram2() {
        long[] data = new long[DATA_SIZE_CACHE * 500];   // 50M longs, 400M bytes
        
        Random r = new Random(0);
        
        for (int i = 0; i < data.length; i++) {
            //data[i] = r.nextLong();
            data[i] = 1L;
        }
        
        int reps = 20;
        long t0 = 0;
        long sum = 0;
        int index = 0;
        
        t0 = System.nanoTime();
        
        for (int k = 0; k < reps; k++) {
            for (int i = 0; i < DATA_SIZE_CACHE; i++) {                
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
                sum += data[index];  index = (index + 836413) % DATA_SIZE_RAM;
            }
        }
        
        double time = (System.nanoTime() - t0) * 1e-9;
        long count = reps * DATA_SIZE_CACHE;
        
        out.println("---- ram2() ----");
        out.printf( "Access time %.3g s, time: %.6f s (sum:%d, count:%d)\n", time / count, time, sum, count);
    }
    
    public static void main(String[] args) {
        PingPong p = new PingPong();
        
        //for (int i = 0; i < 10; i++)  p.cache1();
        for (int i = 0; i < 10; i++)  p.cache2();
        //for (int i = 0; i < 10; i++)  p.ram2();
    }
}

/*

131105. On Cissi.

sudo cat /proc/cpuinfo | grep "cache"   -->
  cache size    : 4096 KB
sudo cat /proc/cpuinfo | fgrep 'cpu MHz'
  Max freq: cpu MHz : 2101.000  <--> 0.476 ns / cycle

cache1:
  0.334 ns (0.70 cycles)
cache2:
  4.03 ns (8.5 cycles)
ram1:
  0.331 ns (0.70 cycles).
ram2:
  0.161 us = 161 ns (486 cycles)
  
Sometimes less than a cycle, maybe SSE4 used.

Run command:
  $ j frans.PingPong; sudo cat /proc/cpuinfo | fgrep 'cpu MHz'

Java version (j = java -server ...):
  $ j -version
  java version "1.7.0_25"
  Java(TM) SE Runtime Environment (build 1.7.0_25-b15)
  Java HotSpot(TM) 64-Bit Server VM (build 23.25-b01, mixed mode)

*/
