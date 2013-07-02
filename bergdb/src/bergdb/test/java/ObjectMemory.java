package bergdb.test.java;

import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;

public class ObjectMemory {

    @T("perf")
    public static void run(TestCollector c) throws Exception {
        Object[] objects;
        long m0, m1, m2;
        int N = 10000;
        
        m0 = mem();
        objects = new Object[N];
        m1 = mem();
        
        c.report("memPerObjectRef", (double)(m1-m0) / (double) N);
        
        m1 = mem();
        for (int i = 0; i < N; i++) {
            objects[i] = new Object();
        }
        
        m2 = mem();
        double diff = m2 - m1;
        
        c.report("memPerObject", diff / N);
        
        objects = new Object[N];
        
        m1 = mem();
        for (int i = 0; i < N; i++) {
            objects[i] = new OneLongFieldClass();
        }
        
        m2 = mem();
        diff = m2 - m1;
        
        c.report("memPerOneFieldObject", diff / N);
    }
    
    private static long mem() {
        Runtime rt = Runtime.getRuntime();
        for (int i = 0; i < 5; i++) {
            System.gc();
        }
        
        return -rt.freeMemory();
    }

    static class OneLongFieldClass {
        long field;
    }
}

/*
120523 on virtual machine, 64-bit Ubuntu, "linda".
$ java -server -cp bergdb.jar com.bergdb.perf.Starter
com.bergdb.perf.ObjectMemory.memPerObjectRef = 8.0024
com.bergdb.perf.ObjectMemory.memPerObject = 16.0
com.bergdb.perf.ObjectMemory.memPerOneFieldObject = 24.0

120523 on my Rose notebook.
$ java -cp p/KissDB/ -server -Xmx1000m com.bergdb.perf.Starter
com.bergdb.perf.ObjectMemory.memPerObjectRef = 4.0016
com.bergdb.perf.ObjectMemory.memPerObject = 8.024
com.bergdb.perf.ObjectMemory.memPerOneFieldObject = 16.0312

080924 on my Acer Extensa 32-bit laptop
com.bergdb.perf.ObjectMemory.memPerObjectRef = 4.0016
com.bergdb.perf.ObjectMemory.memPerObject = 8.0
*/