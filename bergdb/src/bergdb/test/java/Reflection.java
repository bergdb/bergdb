package bergdb.test.java;

import java.lang.reflect.Field;

import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;


/**
 * How long time does it take to set field of an object 
 * using reflection.
 * 
 * @author Frans Lundberg
 */
public class Reflection {
    private Field[] fields;
    
    public Reflection() throws Exception {
        fields = new Field[3];
        fields[0] = Customer.class.getDeclaredField("personID");
        fields[1] = Customer.class.getDeclaredField("firstName");
        fields[2] = Customer.class.getDeclaredField("creationTime");
        for (Field f : fields) {
            f.setAccessible(true);
        }
    }
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        long t0, t1;
        int n = 1000000;
        double time;
        Customer cust = new Customer();
        Reflection r = new Reflection();
        
        t0 = System.nanoTime();
        for (int i=0; i<n; i++) {
            r.setFields(cust);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9;
        c.report("timePerField", (time/n/3));
        
        t0 = System.nanoTime();
        for (int i=0; i<n; i++) {
            r.setFields2(cust);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9;
        c.report("timePerField2", (time/n/3));
    }
    
    private void setFields(Customer c) throws IllegalAccessException {
        Class<? extends Customer> clazz = c.getClass();
        Field[] fields = clazz.getDeclaredFields();
        for (Field f : fields) {
            f.setAccessible(true);     // makes it possible to access private fields
            String name = f.getName();
            switch(name.charAt(0)) {
            case 'p':
                f.set(c, "197503148888");
                break;
            case 'f':
                f.set(c, "Fransiscus");
                break;
            case 'c':
                f.setLong(c, 123456789);
                break;
            }
        }
    }
    
    private void setFields2(Customer c) throws IllegalAccessException {
        fields[0].set(c, "197503148888");
        fields[1].set(c, "Fransiscus");
        fields[2].setLong(c, 123456789);
    }

    @SuppressWarnings("unused")
    static class Customer {
        private String personID;
        private String firstName;
        private long creationTime;
    }
}


/*
NOTES 120319

Ran on my little Rose laptop.
$ java -cp . -server com.bergdb.perf.Reflection
com.bergdb.perf.Reflection.timePerField = 4.40E-7
com.bergdb.perf.Reflection.timePerField2 = 1.12E-7
JVM Oracle, 1.7.0 on Ubuntu.
Slow compare to 2010 measurement, but faster on Linda. Something like 1.28E-7, 2.34E-8
(0.128 us, 0.023 us).

NOTES 100711

Reflection is not that slow. Tests on Acer Laptop Extensa 5220. Ubuntu 10.04.

Some output...
com.bergdb.perf.Reflection.timePerField = 1.8E-7  = 180 ns
com.bergdb.perf.Reflection.timePerField2 = 6.2E-8 =  62 ns

Conclusions:
1. "Caching" fields can have a significant performance improvement. Note that we still have to
  do some search (lookup field name from database -> Field).
2. Faster than I thought. For a typical object with 10 fields, we can set all fields
  via reflection in 620 ns = 0.6 us.
  Everything below 1 us per object will normally not limit total performance. A million objects
  per second is GOOD :-)
*/
