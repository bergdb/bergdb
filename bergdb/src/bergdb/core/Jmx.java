package bergdb.core;

import java.lang.management.ManagementFactory;

import javax.management.InstanceAlreadyExistsException;
import javax.management.MBeanRegistrationException;
import javax.management.MBeanServer;
import javax.management.MalformedObjectNameException;
import javax.management.NotCompliantMBeanException;
import javax.management.ObjectName;

import bergdb.common.Bug;
import bergdb.pub.Clock;


/**
 * This class is a container for inner classes and interfaces that constitutes MBeans used
 * to monitor and control a DB instance.
 * 
 * @author Frans Lundberg
 */
public class Jmx {
    /**
     * For monitoring the database. For advanced users, monitors Core Layer.
     * The 'H' suffix for some methods is for a more human-readable version of what is 
     * returned from the method without the suffix.
     * 
     * @author Frans Lundberg
     */
    public interface DbMonitorMBean {
        public long getTime();
        public String getTimeH();
        public String dbTimeToString(long dbTime);
        public long getStreamSize();
        public int getDirtyNodeCount();
        public int getStartupDistance();
        public void setStartupDistance(int newDistance);
        public String getStartupDistanceH();
        public double getDirtyFraction100();
        public double getDirtyFraction1000();
        public long getRetainDuration();
        public String getRetainDurationH();
        public void setRetainDuration(long durationTimeUnits);
        public void setRetainDurationInSeconds(int seconds);
        public void setRetainDurationInDays(int days);
        public double getActualRetainDurationInSeconds();
        public double getActualRetainDurationInDays();
        public long getFirstLookupTime();
        public String getFirstLookupTimeH();
        public long getCachedMemoryValue();
        public long getKvCount();
        public long getTransactionCount();
        public long getGetOpCount();
        public long getReclaimIterationCount();
        public double getReclaimInternalFraction();
        public void setReclaimInternalFraction(double internalFraction);
        public String[] getDummyStrings();
    }
    
    /**
     * An MBean that monitors a specific DB instance.
     * Many get methods acquires DB.writeLock, so that will affect performance if called frequently.
     * 
     * @see DbMonitorMBean
     * @author Frans Lundberg
     */
    public static class DbMonitor implements DbMonitorMBean {
        private Db db;
        private DirtyNodes2 dirtyNodes;
        private Object dbWriteLock;
        private MBeanServer mbs;
        
        public DbMonitor(Db db) {
            if (db == null) {
                throw new IllegalArgumentException("db == null not allowed");
            }
            this.db = db;
            this.dirtyNodes = db.getDirtyNodes();
            if (dirtyNodes == null) {
                throw new Bug("db.getDirtyNodes() == null");
            }
            this.dbWriteLock = db.getWriteLock();
            if (dbWriteLock == null) {
                throw new Bug("db.getWriteLock() == null");
            }
        }
        
        /**
         * Returns the current database time in time units (see Clock).
         */
        public long getTime() {
            return db.getTime();
        }
        
        /**
         * Returns the current database time in a human-readable string with date and
         * time. UTC time zone is used.
         */
        public String getTimeH() {
            return DbUtil.dbTimeToUtc(db.getTime());
        }
        
        /**
         * Utility method to convert DB time units to a human-readable string.
         */
        public String dbTimeToString(long dbTime) {
            return DbUtil.dbTimeToUtc(dbTime);
        }
        
        /**
         * Returns the current size of the DB stream in bytes.
         * This is the total number of bytes ever written to the stream, not necessarily the size
         * of the part of the stream that is still available (not pretruncated).
         */
        public long getStreamSize() {
            return db.getStreamLength();
        }
        
        public int getDirtyNodeCount() {
            synchronized (dbWriteLock) {
                return dirtyNodes.getSize();
            }
        }
        
        public int getStartupDistance() {
            return db.getStartupDistance();
        }
        
        public void setStartupDistance(int newDistance) {
            db.setStartupDistance(newDistance);
        }
        
        public String getStartupDistanceH() {
            return db.getStartupDistanceH();
        }
        
        public double getDirtyFraction100() {
            return db.getDirtyFraction100();
        }
        
        public double getDirtyFraction1000() {
            return db.getDirtyFraction1000();
        }
        
        public long getRetainDuration() {
            return db.getRetainDuration();
        }
        
        public String getRetainDurationH() {
            long d = db.getRetainDuration();
            long days = d / (24 * 3600 * Clock.UNITS_PER_SEC);
            d = d - days * (24 * 3600 * Clock.UNITS_PER_SEC);
            double secs = (double) d / Clock.UNITS_PER_SEC;
            return days + " days, " + secs + " s";
        }
        
        
        public void setRetainDuration(long durationTimeUnits) {
            db.setRetainDuration(durationTimeUnits);
        }
        
        public void setRetainDurationInSeconds(int seconds) {
            long units = seconds * Clock.UNITS_PER_SEC;
            setRetainDuration(units);
        }
        
        public void setRetainDurationInDays(int days) {
            long units = days * 24 * 3600 * Clock.UNITS_PER_SEC;
            setRetainDuration(units);
        }
        
        public double getActualRetainDurationInSeconds() {
            long duration = db.getTime() - db.getFirstAvailableLookupTime();
            return ((double) duration) / Clock.UNITS_PER_SEC;
        }
        
        public double getActualRetainDurationInDays() {
            long duration = db.getTime() - db.getFirstAvailableLookupTime();
            return duration / (Clock.UNITS_PER_SEC * (24.0 * 3600.0));
        }
        
        public long getFirstLookupTime() {
            return db.getFirstAvailableLookupTime();
        }
        
        public String getFirstLookupTimeH() {
            long time = db.getFirstAvailableLookupTime();
            return DbUtil.dbTimeToUtc(time);
        }
        
        public long getCachedMemoryValue() {
            return db.getCachedMemoryValue();
        }
        
        public long getKvCount() {
            return db.getKvCount();
        }
        
        public long getTransactionCount() {
            return db.getTransactionCount();
        }
        
        public long getGetOpCount() {
            return db.getGetOpCount();
        }
        
        public long getReclaimIterationCount() {
            return db.getReclaimIterationCount();
        }
        
        public double getReclaimInternalFraction() {
            return db.getInternalFraction();
        }
        
        public void setReclaimInternalFraction(double internalFraction) {
            db.setReclaimInternalFraction(internalFraction);
        }
        
        /**
         * Returns a String array with the elements "first" and "second".
         * Used to test whether the JMX client can display string arrays properly.
         */
        public String[] getDummyStrings() {
            return new String[] {"first", "second"};
        }
        
        /**
         * Registers the MBean with the default platform MBean server.
         * 
         * @throws InstanceAlreadyExistsException
         * @throws MBeanRegistrationException
         * @throws NotCompliantMBeanException
         * @throws MalformedObjectNameException
         * @throws NullPointerException
         */
        public void register() throws InstanceAlreadyExistsException, 
                MBeanRegistrationException, NotCompliantMBeanException, 
                MalformedObjectNameException, NullPointerException {
            mbs = ManagementFactory.getPlatformMBeanServer();
            mbs.registerMBean(this, new ObjectName("com.bergdb.db:type=Jmx.DBMonitor"));
        }
    }
    
    /**
     * MBean interface for Speed as required by the JMX specification.
     */
    public static interface SpeedMBean {
        public double getStreamSizeSpeed();
        public double getStreamSizeSpeedM();
        public double getCachedMemoryValueSpeed();
        public double getCachedMemoryValueSpeedM();
        public double getTransactionSpeed();
        public double getKvSpeed();
        public double getGetSpeed();
    }
    
    /**
     * This MBean measures speed of values (change/s) from DB. Values are measured every 4 
     * seconds and change per sec (speed) computed based on that.
     */
    public static class Speed implements Runnable, SpeedMBean {
        volatile boolean stop = false;
        volatile double streamSizeSpeed = 0.0;
        volatile double cachedMemoryValueSpeed = 0.0;
        volatile double transactionSpeed = 0.0;
        volatile double kvSpeed = 0.0;
        volatile double getSpeed = 0.0;
        
        public static final String NAME = "com.bergdb.db:type=Jmx.Speed";
        private Db db;
        private Thread thread;
        
        public Speed(Db db) {
            this.db = db;
        }
        
        public double getStreamSizeSpeed() {
            return streamSizeSpeed;
        }
        
        public double getStreamSizeSpeedM() {
            return streamSizeSpeed * 1e-6;
        }
        
        public double getCachedMemoryValueSpeed() {
            return cachedMemoryValueSpeed;
        }
        
        public double getCachedMemoryValueSpeedM() {
            return cachedMemoryValueSpeed * 1e-6;
        }
        
        public double getTransactionSpeed() {
            return transactionSpeed;
        }
        
        public double getKvSpeed() {
            return kvSpeed;
        }
        
        public double getGetSpeed() {
            return getSpeed;
        }
        
        /**
         * Starts the monitoring thread and registers the object with the platform MBeanServer.
         */
        public synchronized void registerAndStart() throws Exception {
            stop = false;
            if (thread != null) {
                return;    // already running
            }
            
            thread = new Thread(this);
            thread.setName("DBMonitor.MThread");
            thread.setPriority(Thread.NORM_PRIORITY - 1);
            thread.setDaemon(true);
            
            MBeanServer mbs = ManagementFactory.getPlatformMBeanServer();
            mbs.registerMBean(this, new ObjectName(NAME));
            
            thread.start();
        }
        
        public synchronized void stop() throws Exception {
            stop = true;
            try {
                thread.join();
            } catch (InterruptedException e) {
                // empty
            }
            
            MBeanServer mbs = ManagementFactory.getPlatformMBeanServer();
            mbs.unregisterMBean(new ObjectName(NAME));
            thread = null;
        }
        
        public void run() {
            A: while (!stop) {
                
                long time = System.nanoTime();
                
                long streamSize = db.getStreamLength();
                long cachedMemoryValue = db.getCachedMemoryValue();
                long transactionCount = db.getTransactionCount();
                long kvCount = db.getKvCount();
                long getCount = db.getGetOpCount();
                
                for (int i = 0; i < 4; i++) {
                    if (stop) {
                        break A;
                    }
                    
                    try {
                        Thread.sleep(1000);
                    } catch (InterruptedException e) {
                        break A;
                    }
                }
                
                time = System.nanoTime() - time;
                double secs = time * 1e-9;
                
                streamSizeSpeed = (db.getStreamLength() - streamSize) / secs;
                cachedMemoryValueSpeed = (db.getCachedMemoryValue() - cachedMemoryValue) / secs;
                kvSpeed = (db.getKvCount() - kvCount) / secs;
                transactionSpeed = (db.getTransactionCount() - transactionCount) / secs;
                getSpeed = (db.getGetOpCount() - getCount) / secs;
            }
        }
    }
}
