package bergdb.core;

import java.lang.management.ManagementFactory;

import javax.management.InstanceAlreadyExistsException;
import javax.management.MBeanRegistrationException;
import javax.management.MBeanServer;
import javax.management.MalformedObjectNameException;
import javax.management.NotCompliantMBeanException;
import javax.management.ObjectName;

import bergdb.pub.util.Clock;


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
        public int getStartupDistance();
        public void setStartupDistance(int newDistance);
        public long getRetainDuration();
        public String getRetainDurationH();
        /**
         * Sets the retain duration through Db.setRetainDuration, which keeps it in the
         * stream (bergdb 015-87); so do the two setters below.
         */
        public void setRetainDuration(long durationTimeUnits);
        public void setRetainDurationInSeconds(int seconds);
        public void setRetainDurationInDays(int days);
        public double getActualRetainDurationInSeconds();
        public double getActualRetainDurationInDays();
        public long getFirstLookupTime();
        public String getFirstLookupTimeH();
        public long getCacheSizeIndicator();
        public void setCacheSizeIndicator(long sizeIndicator);
        public long getCacheTotalSize();
        public long getKvCount();
        public long getTransactionCount();
        public long getGetOpCount();
        public long getReclaimIterationCount();
        /** Reclaim's internal fraction as it is used, a multiple of 2^-16 (bergdb 005-79). */
        public double getReclaimInternalFraction();
        /**
         * Sets reclaim's internal fraction through Db.setReclaimInternalFraction: 0.001 to
         * 0.90, NaN and other values refused; kept as the nearest multiple of 2^-16, so 0.25
         * exactly and 0.1 as 0.100006 (bergdb 005-79); kept in the stream (bergdb 015-87).
         */
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
        private final Db db;
        private MBeanServer mbs;
        
        public DbMonitor(Db db) {
            if (db == null) {
                throw new IllegalArgumentException("db == null not allowed");
            }
            this.db = db;
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
            mbs.registerMBean(this, new ObjectName("bergdb.core.Db:type=Jmx.DBMonitor"));
        }
        
        /**
         * Returns the current database time in time units (see Clock).
         */
        public long getTime() {
            return db.currentTime();
        }
        
        /**
         * Returns the current database time in a human-readable string with date and
         * time. UTC time zone is used.
         */
        public String getTimeH() {
            return DbUtil.dbTimeToUtc(db.currentTime());
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
        
        public int getStartupDistance() {
            return db.getStartupDistance();
        }
        
        public void setStartupDistance(int newDistance) {
            db.setStartupDistance(newDistance);
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
            long units = Math.multiplyExact((long) seconds, Clock.UNITS_PER_SEC);
            setRetainDuration(units);
        }
        
        public void setRetainDurationInDays(int days) {
            // In long (2026-10-21, bergdb 005-20): days * 24 * 3600 was an int, so 99,999
            // days gave 578.5 days.
            long units;
            try {
                units = Math.multiplyExact(days * 24L * 3600, Clock.UNITS_PER_SEC);
            } catch (ArithmeticException e) {
                throw new IllegalArgumentException("Too many days, " + days + ".");
            }
            setRetainDuration(units);
        }
        
        public double getActualRetainDurationInSeconds() {
            long duration = db.currentTime() - db.getFirstAvailableLookupTime();
            return ((double) duration) / Clock.UNITS_PER_SEC;
        }
        
        public double getActualRetainDurationInDays() {
            long duration = db.currentTime() - db.getFirstAvailableLookupTime();
            return duration / (Clock.UNITS_PER_SEC * (24.0 * 3600.0));
        }
        
        public long getFirstLookupTime() {
            return db.getFirstAvailableLookupTime();
        }
        
        public String getFirstLookupTimeH() {
            long time = db.getFirstAvailableLookupTime();
            return DbUtil.dbTimeToUtc(time);
        }
        
        /** The capacity controller's budget (bergdb item 001, WP J7; Eviction). */
        public long getCacheSizeIndicator() {
            return db.getCacheSizeIndicator();
        }
        
        /** Sets the capacity controller's budget too (bergdb item 001, WP J7; 005-52). */
        public void setCacheSizeIndicator(long sizeIndicator) {
            db.setCacheSizeIndicator(sizeIndicator);
        }
        
        /**
         * The resident bytes as the capacity controller counts them (Residents; bergdb item
         * 001, WPs J1 and J7). Before 2026-10-18 Cache3's total size, which never moved (M40).
         */
        public long getCacheTotalSize() {
            return db.internal().cache().residents().bytes();
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
    }
    
    /**
     * MBean interface for Speed as required by the JMX specification.
     */
    public static interface SpeedMBean {
        public double getStreamSizeSpeed();
        public double getStreamSizeSpeedM();
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
        
        /**
         * Stops the monitoring thread, waits for it to end, and unregisters the object. An
         * interrupt does not cut the wait short; the caller's interrupt flag is kept (bergdb
         * 015-38, as 005-46's rule says).
         */
        public synchronized void stop() throws Exception {
            stop = true;
            boolean interrupted = false;
            try {
                while (true) {
                    try {
                        thread.join();
                        break;
                    } catch (InterruptedException e) {
                        interrupted = true;
                    }
                }
                
                MBeanServer mbs = ManagementFactory.getPlatformMBeanServer();
                mbs.unregisterMBean(new ObjectName(NAME));
                thread = null;
            } finally {
                if (interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        }
        
        public void run() {
            A: while (!stop) {
                
                long time = System.nanoTime();
                
                long streamSize = db.getStreamLength();
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
                        // Goes on: only stop() ends the thread (bergdb 015-38, 005-46).
                    }
                }
                
                time = System.nanoTime() - time;
                double secs = time * 1e-9;
                
                streamSizeSpeed = (db.getStreamLength() - streamSize) / secs;
                kvSpeed = (db.getKvCount() - kvCount) / secs;
                transactionSpeed = (db.getTransactionCount() - transactionCount) / secs;
                getSpeed = (db.getGetOpCount() - getCount) / secs;
            }
        }
    }
}
