package bergdb.common;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
//import java.lang.management.ClassLoadingMXBean;
//import java.lang.management.ManagementFactory;
//import java.lang.management.ThreadMXBean;
import java.util.Enumeration;
import java.util.Properties;

/**
 * This class is able to generate random data (not evenly distributed) with
 * enough entropy to use it as a seed for a random number generator. The reason
 * for creating this class is that /dev/random on some Linux systems may not 
 * generate new random data fast enough and block seeding from SecureRandom and Random classes.
 * 
 * @author Frans Lundberg
 */
public class SeedGenerator {
    // 1302 Frans: addJMXData() no longer used because of IKVM issues. We want to avoid
    // the dependency of one more IKVM DLL.
    //
    
    private byte[] seed;
    private int offset;

    /**
     * Initializes seed generator with some entropy based on current time, JMX data, 
     * JVM memory available and so forth.
     */
    public SeedGenerator() {
        seed = new byte[128];
        addTimeData();
        addRandomOffset();
        //addJMXData();
        addRuntimeData();
        addTimeData();
        addRandomOffset();
        //addJMXData();
        addRuntimeData();
        addTimeData();
        addRuntimeData();
        addTimeData();
    }
    
    /**
     * Slower than constructor, but generates more entropy.
     */
    public void moreEntropy() {
        addMachineData();
        
        addTimeData();
        addRandomOffset();
        //addJMXData();
        addRuntimeData();
        addTimeData();
        
        System.gc();
        
        addRandomOffset();
        //addJMXData();
        addRuntimeData();
        addTimeData();
        addRuntimeData();
        addTimeData();
    }

    /**
     * Just to avoid not writing much to certain offsets.
     */
    private synchronized void addRandomOffset() {
        offset = offset + (int) (Math.random() * 8.0);
        if (offset >= seed.length) {
            offset = offset % seed.length;
        }
    }

    /**
     * Adds data based on system clock and system counter.
     */
    private void addTimeData() {
        addData(System.nanoTime());
        addData(System.currentTimeMillis());
        addData(System.nanoTime());
    }

    /**
     * Adds data specific to this machine.
     */
    private void addMachineData() {
        ByteArrayOutputStream bout;
        DataOutputStream out;
        Enumeration<Object> keys;

        bout = new ByteArrayOutputStream();
        out = new DataOutputStream(bout);

        try {
            Properties p = System.getProperties();
            keys = p.keys();
            while (keys.hasMoreElements()) {
                out.writeUTF(p.getProperty((String) keys.nextElement()));
            }
            out.close();
        } catch (IOException e) {
            throw new Error("neven happens, writing to memory");
        }

        addData(bout.toByteArray());
    }

    /**
     * Adds data from a JMX - java management extension objects.
     */
    /*private void addJMXData() {
        ClassLoadingMXBean clBean;
        ThreadMXBean tBean;
        long[] ids;

        clBean = ManagementFactory.getClassLoadingMXBean();
        tBean = ManagementFactory.getThreadMXBean();

        addData(clBean.getTotalLoadedClassCount());
        addData(clBean.getUnloadedClassCount());
        addData(clBean.getLoadedClassCount());

        addData(tBean.getCurrentThreadCpuTime());
        addData(tBean.getCurrentThreadUserTime());
        addData(tBean.getTotalStartedThreadCount());
        addData(tBean.getDaemonThreadCount());
        addData(tBean.getPeakThreadCount());
        addData(tBean.getThreadCount());
        addRandomOffset();

        ids = tBean.getAllThreadIds();
        for (int i = 0; i < ids.length; i++) {
            addData(ids[i]);
        }
    }*/

    /**
     * Adds data from Runtime state.
     */
    private void addRuntimeData() {
        Runtime rt = Runtime.getRuntime();
        addData(rt.freeMemory());
        addData(rt.maxMemory());
        addData(rt.totalMemory());
    }

    private synchronized void addData(byte[] bytes) {
        for (int i = 0; i < bytes.length; i++) {
            seed[offset] += bytes[i];
            offset++;
            if (offset >= seed.length) {
                offset = 0;
            }
        }
    }

    private void addData(long value) {
        byte[] bytes = new byte[8];
        Bytes.longToBytesBE(value, bytes, 0);
        addData(bytes);
    }

    /**
     * Adds some entropy and returns a copy of the current seed data (128 byte array).
     */
    public synchronized byte[] getSeed() {
        addTimeData();
        addRandomOffset();
        //addJMXData();
        return (byte[]) seed.clone();
    }

    /**
     * For testing.
     */
    public static void main(String[] args) {
        int n = 10;
        long t = System.nanoTime();
        
        for (int i = 0; i < n; i++) {
            new SeedGenerator().getSeed();
        }
        
        t = System.nanoTime() - t;
        System.out.println("Time per run: " + (1e-9*t / n));
    }
}