package bergdb.pubimp;

import java.util.WeakHashMap;
import java.util.function.Consumer;

import bergdb.core.Db;
import bergdb.core.StartInfo;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.IndexBuilder;
import bergdb.pub.StartupInfo;
import bergdb.pub.Time;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamException;
import bergdb.storage.StreamIoException;

/**
 * Implementation of pub.Database, a started database. 
 * See pub.Database for Javadoc.
 * 
 * @see bergdb.pub.Database
 * @author Frans Lundberg
 */
public class DatabaseImp implements Database {
    //
    // The ConnectionInitializer is not much used. We prepare to have a flexible way of 
    // initializing state that can be customized by the Pub user. But is it required?
    //
    private final Db db;
    private StartInfoImp startupInfo;
    private final IndexManager indexManager;
    private final ConnectionInitializer connectionInitializer;
        // "final" for now. Could become a setting.
    private final KvToObjectConverter kvToObjectConverter;
        // "final" for now, could become a setting.
    private final WeakHashMap<Thread, Connection> threadLocalConnections;
        // Weak keys: an ended thread's connection goes once the collector has taken the
        // thread, at the map's next use (bergdb 015-60). Not a ThreadLocal, whose value in a
        // long-lived thread would keep a stopped database.
    
    private DatabaseImp(final Db db) {
        synchronized (this) {
            assert db != null;
            this.db = db;
            this.threadLocalConnections = new WeakHashMap<Thread, Connection>();
            
            this.indexManager = new IndexManager();
            
            this.connectionInitializer = new ConnectionInitializer() {
                public void initialize(Connection connection) {
                    connection.setLookupTime(Time.MAX);
                }
            };
            
            this.kvToObjectConverter = new KvToObjectImp();
        }
    }
    
    /**
     * A start that fails on the storage throws the storage's exception, a StreamIoException
     * or a StreamFormatException (bergdb 020-24-08, U8-2): as DatabaseBuilder.start() says,
     * and as the start's steps before the Db is active throw it. Until 020-24-08, a read
     * that failed in the Db's last step (Reclaim.initFromDb) or in the index manager's scans,
     * or a failure of the storage in the background that such a read met, as the start's
     * own write on a full disk, failed the database that was starting, and the start threw
     * a DbFailedException, "Cannot call getOne(): the database failed (the cause) and must
     * be restarted." or "A read failed on the storage (the cause). [...] must be
     * restarted.", whose Javadoc is about a running database.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalDbStateException  If db has been started already.
     */
    static synchronized DatabaseImp createAndStart(final Db db) {
        @SuppressWarnings("unused")
        StartInfo startInfo;
        DatabaseImp database;
        
        // When anything throws, the Db is closed (2026-10-24, bergdb 005-32): a database
        // whose index manager failed to initialize ran on until the garbage collector stopped
        // it. A start that throws has closed its storage already (Db.start()).
        try {
            database = new DatabaseImp(db);
        
            long t0 = System.nanoTime();
            startInfo = db.start();
            double startTime = (System.nanoTime() - t0) * 1e-9;
            
            final Consumer<Db> hook = testHookAfterStart;
            if (hook != null) {
                hook.accept(db);
            }
            
            database.indexManager.start(database);       // bergdb 020-10, section 4.5
            database.startupInfo = new StartInfoImp(startTime);
        } catch (RuntimeException | Error e) {
            Throwable thrown = e;
            if (e instanceof DbFailedException && e.getCause() instanceof StreamException) {
                thrown = e.getCause();      // The storage's exception (bergdb 020-24-08, U8-2).
            }
            try {
                db.close();
            } catch (RuntimeException | Error e2) {
                if (e2 != thrown) {
                    thrown.addSuppressed(e2);
                }
            }
            if (thrown != e) {
                throw (StreamException) thrown;
            }
            throw e;
        }
        
        return database;
    }
    
    /**
     * For tests (bergdb 005-32): if set, createAndStart() calls it with the Db right after
     * db.start().
     */
    static volatile Consumer<Db> testHookAfterStart = null;
    
    
    /**
     * The Core's Db under this database. Internal, not API (bergdb 020-10, section 7): for BergDB's tests and tools, which src-dev and
     * stress hold.
     */
    public final Db getDb() {
        return db;
    }
    
    final IndexManager getIndexManager() {
        return indexManager;
    }
    
    final KvToObjectConverter getKvToObjectConverter() {
        return this.kvToObjectConverter;
    }
    
    public Connection connection() {
        Connection c;
        
        synchronized (threadLocalConnections) {
            Thread current = Thread.currentThread();
            
            c = threadLocalConnections.get(current);
            if (c == null) {
                c = new ConnectionImp(this);
            }
            threadLocalConnections.put(current, c);
        }
        
        assert c != null;
        this.connectionInitializer.initialize(c);
        return c;
    }
    
    public Connection newConnection() {
        return new ConnectionImp(DatabaseImp.this);
    }
    
    /**
     * @throws StreamIoException
     */
    public void sync() {
        db.sync(0, SyncLevel.ORDINARY);
    }
    
    /**
     * @throws StreamIoException
     */
    public void sync(SyncLevel syncLevel) {
        db.sync(0, syncLevel);
    }
    
    public StartupInfo getStartupInfo() {
        return startupInfo;
    }
    
    public synchronized void stop() {
        synchronized (threadLocalConnections) {
            threadLocalConnections.clear();
        }
        
        db.stop();
    }
    
    /**
     * Not synchronized, unlike stop(): it waits for the close, and a stop() from another
     * thread meanwhile returns at once.
     */
    public void close() {
        synchronized (threadLocalConnections) {
            threadLocalConnections.clear();
        }
        
        db.close();
    }
    
    public final Time currentTime() {
        // This method may change the state of db.
        
        return Time.units(db.currentTime());
    }
    
    public final Duration getRetainDuration() {
        return Duration.units(db.getRetainDuration());
    }
    
    public boolean maintain() {
        return db.maintain();
    }

    public void setRetainDuration(Duration retainDuration) {
        if (retainDuration == null) {
            // bergdb 020-21, 3: as every null argument of the API, not a NullPointerException.
            throw new IllegalArgumentException("retainDuration == null not allowed");
        }
        long units = retainDuration.units();
        
        if (units < 1 * Clock.UNITS_PER_SEC) {
            throw new IllegalArgumentException("retainDuration too small, must be at least " 
                    + "one second.");
        }
        
        db.setRetainDuration(units);
    }

    public int getStartupDistanceInMb() {
        return (int) Math.round(db.getStartupDistance() / 1e6);
    }

    public void setStartupDistanceInMb(int startupDistanceInMb) {
        int mb = DatabaseBuilderImp.clampStartupDistanceInMb(startupDistanceInMb);
        db.setStartupDistance(mb * 1000000);
    }

    public int getCacheSizeInMb() {
        return (int) Math.min(Integer.MAX_VALUE, Math.round(db.getCacheSizeIndicator() / 1e6));
    }

    public void setCacheSizeInMb(int cacheSizeInMb) {
        int mb = DatabaseBuilderImp.clampCacheSizeInMb(cacheSizeInMb);
        db.setCacheSizeIndicator(mb * 1000000L);
    }
    
    public final Time getFirstAvailableLookupTime() {
        return Time.units(db.getFirstAvailableLookupTime());
    }
    
    /**
     * @throws IllegalArgumentException  If the name breaks bergdb 020-10, section 3.1's rule.
     */
    public IndexBuilder indexBuilder(String indexName) {
        IndexKeys.checkName(indexName);
        return new IndexBuilderImp(indexName, this);
    }
    
    /**
     * @throws NoSuchIndexException
     * @throws DbException
     */
    public void deleteIndex(String indexName) {
        indexManager.delete(indexName);
    }
    
    /**
     * @throws NoSuchIndexException
     */
    public Job indexJob(String indexName) {
        return indexManager.job(indexName);
    }
}
