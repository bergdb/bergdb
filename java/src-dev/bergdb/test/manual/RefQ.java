package bergdb.test.manual;

import java.lang.ref.PhantomReference;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;

/**
 * Testing Java's reference queues and weak / phantom references.
 * 
 * @author Frans Lundberg
 */
@SuppressWarnings({"unused", "rawtypes"})
public class RefQ {    
    ReferenceQueue<A> queue = new ReferenceQueue<A>();
    int size = 100;
    
    void go() throws InterruptedException {
        Reference[] refs;
        
        refs = createRefs1();
        //refs = createRefs2();
        
        //setRefsToNull(refs);
        setMostRefsToNull(refs);
        
        System.out.println("== Q before gc");
        printQ();
        
        System.gc();
        
        System.out.println("== Q after gc");
        printQ(); 
        
        Thread.sleep(1000);
        System.gc();
        
        System.out.println("== Q after sleep + gc");
        printQ(); 
    }
    
    private void setRefsToNull(Reference[] refs) {
        for (int i = 0; i < refs.length; i++) {
            refs[i] = null;
        }
    }
    
    private void setMostRefsToNull(Reference[] refs) {
        for (int i = 0; i < refs.length; i++) {
            if (i % 10 != 3) refs[i] = null;
        }
    }

    Reference[] createRefs1() {
        MyRef1[] refs = new MyRef1[size];
        for (int i = 0; i < refs.length; i++) {
            A a = new A("A" + i);
            refs[i] = new MyRef1(a, queue, a.name);
        }
        
        return refs;
    }
    
    Reference[] createRefs2() {
        MyRef2[] refs = new MyRef2[size];
        for (int i = 0; i < refs.length; i++) {
            A a = new A("A" + i);
            refs[i] = new MyRef2(a, queue, a.name);
        }
        
        return refs;
    }
    
    void printQ() {
        Reference<? extends A> ref = queue.poll();
        if (ref == null) {
            System.out.println("Empty queue.");
        }
        
        while (ref != null) {
            System.out.println("From Q, ref: " + ref);
            assert ref.get() == null;
            ref = queue.poll();
        }
    }

    public static void main(String[] args) throws Exception {
        new RefQ().go();
    }
    
    public class A {
        String name;
        
        A(String s) {
            this.name = s;
        }
        
        public String toString() {
            return name;
        }
    }
    
    public static class MyRef1 extends PhantomReference<A> {
        String name;
        
        public MyRef1(A referent, ReferenceQueue<? super A> q, String name) {
            super(referent, q);
            this.name = name;
        }
        
        public String toString() {
            return "ref1:" + name;
        }
    }
    
    public static class MyRef2 extends WeakReference<A> {
        String name;
        
        public MyRef2(A referent, ReferenceQueue<? super A> q, String name) {
            super(referent, q);
            this.name = name;
        }
        
        public String toString() {
            return "ref2:" + name;
        }
    }
}

/*

150811
======

Notes on ref queues. Conclusions based on observations.
Cissis, JVM 1.7.0_76.

When GC is run, Reference's are put on their queue only when the 
reference is reachable from other objects (not to be garbage collected).
If a Reference is eligible for garbage collection, its referent will not be 
put on its reference queue.

Conclusions for BergDB: we must keep reference to Reference<ValueNode>.
This is a hassle. In effect, we must manage also small ValueNodes the same 
way (or very similar way) as other nodes if we require perfect control over 
cache size.

*/