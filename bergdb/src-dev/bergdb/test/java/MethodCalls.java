package bergdb.test.java;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;

/**
 * Tests performance of static vs dynamic method dispatch.
 * Also compares to no method call at all (inlining) and inlined with 
 * loop unrolling.
 */
public class MethodCalls {
    private static int n = 10000;
    private static int size = 1000;
    
    @T("perf")
    public static void dynamicDispatch(TestEnvironment c) {
        A[] as = new A[size];
        int sum = 0;
        
        for (int i = 0; i < size; i++) {
            if (i % 3 == 0) {
                as[i] = new A2();
            } else {
                as[i] = new A1();
            }
        }
        
        // Warm-up
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; j++) {
                sum += as[j].op(i,  j);
            }
        }
        
        sum = 0;
        long nano = System.nanoTime();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; j++) {
                sum += as[j].op(i,  j);
            }
        }
        nano = System.nanoTime() - nano;
        
        c.report("timePerOp", 1e-9*nano / (n*size));
        c.report("sum", sum);
    }
    
    @T("perf")
    public static void staticDispatch(TestEnvironment c) {
        B[] bs = new B[size];
        int sum = 0;
        
        for (int i = 0; i < size; i++) {
            bs[i] = new B();
        }
        
        // Warm-up
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; j++) {
                sum += bs[j].op(i,  j);
            }
        }
        
        sum = 0;
        long nano = System.nanoTime();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; j++) {
                sum += bs[j].op(i,  j);
            }
        }
        nano = System.nanoTime() - nano;
        
        c.report("timePerOp", 1e-9*nano / (n*size));
        c.report("sum", sum);
    }
    
    @T("perf")
    public static void inline(TestEnvironment c) {
        B[] bs = new B[size];
        int sum = 0;
        
        for (int i = 0; i < size; i++) {
            bs[i] = new B();
        }
        
        // Warm-up
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; j++) {
                sum += i + j;
            }
        }
        
        sum = 0;
        long nano = System.nanoTime();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; j++) {
                sum += i + j;
            }
        }
        nano = System.nanoTime() - nano;
        
        c.report("timePerOp", 1e-9*nano / (n*size));
        c.report("sum", sum);
    }
    
    @T("perf")
    public static void inlineLoopUnroll(TestEnvironment c) {
        B[] bs = new B[size];
        int sum = 0;
        
        for (int i = 0; i < size; i++) {
            bs[i] = new B();
        }
        
        // Warm-up
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; ) {
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
            }
        }
        
        sum = 0;
        long nano = System.nanoTime();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < size; ) {
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
                sum += i + j++;
            }
        }
        nano = System.nanoTime() - nano;
        
        c.report("timePerOp", 1e-9*nano / (n*size));
        c.report("sum", sum);
    }
    
    interface A {
        int op(int a, int b);
    }
    
    static class A1 implements A { 
        public int op(int a, int b) {
            return a+b; 
        }
    }
    
    static class A2 implements A { 
        public int op(int a, int b) {
            return -a+b; 
        } 
    }
    
    static class B {
        public final int op(int a, int b) {
            return a+b; 
        }
    }
}

/*
Values on Rose laptop (32-bit), 2012-05-09.

$ java -cp . -server -Xmx1200m com.bergdb.main.Run run com.bergdb.main.RunPerf com.bergdb.perf.DynamicDispatch
com.bergdb.perf.DynamicDispatch.dynamicDispatch.timePerOp: 1.03427398E-8
com.bergdb.perf.DynamicDispatch.dynamicDispatch.sum: 118503520
com.bergdb.perf.DynamicDispatch.dynamicDispatch.exeTime: 0.20567266
com.bergdb.perf.DynamicDispatch.staticDispatch.timePerOp: 5.5015448E-9
com.bergdb.perf.DynamicDispatch.staticDispatch.sum: -844574848
com.bergdb.perf.DynamicDispatch.staticDispatch.exeTime: 0.13420331200000002
com.bergdb.perf.DynamicDispatch.inline.timePerOp: 4.5418835E-9
com.bergdb.perf.DynamicDispatch.inline.sum: -844574848
com.bergdb.perf.DynamicDispatch.inline.exeTime: 0.094580882
com.bergdb.perf.DynamicDispatch.inlineLoopUnroll.timePerOp: 3.1639989E-9
com.bergdb.perf.DynamicDispatch.inlineLoopUnroll.sum: -844574848
com.bergdb.perf.DynamicDispatch.inlineLoopUnroll.exeTime: 0.073500059

About twice as fast with static dispatch, 5 vs 10 nanosec. This is neglectable
most of the time. Inlining and loop unrolling will still increase performance
a bit. Unrolled, we have 3 ns.
In general, method dispatch is very fast. Typically, there is no need to even
consider the overhead of a method call or using dynamic dispatch.
*/
