package bergdb.pubimp;

import java.util.List;
import java.util.WeakHashMap;
import java.util.function.Consumer;

import bergdb.core.Db;
import bergdb.core.DbStoppingException;
import bergdb.core.StartInfo;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.StartupInfo;
import bergdb.pub.Time;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
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
            
            // Note: we could dependency inject CollatorFactory instead of letting this class itself
            // determine based on whether a class in bergdb.pubimpicu exists.
            // Injecting it would increase testability.
            this.indexManager = new IndexManager(new OptionalIcuCollatorFactory());
            
            this.connectionInitializer = new ConnectionInitializer() {
                public void initialize(Connection connection) {
                    connection.setLookupTime(Time.MAX);
                }
            };
            
            this.kvToObjectConverter = new KvToObjectImp();
        }
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalDbStateException  If db has been started already.
     */
    public static synchronized DatabaseImp createAndStart(final Db db) {
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
            
            ConnectionImp connection = new ConnectionImp(database);
            database.indexManager.initFromDatabase(connection);
            List<Job> jobs = database.indexManager.finishOngoingJobs(database);        
            database.startupInfo = new StartInfoImp(jobs, startTime);
        } catch (RuntimeException | Error e) {
            try {
                db.close();
            } catch (RuntimeException | Error e2) {
                e.addSuppressed(e2);
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
     * For tests (bergdb 015-21): if set, deleteIndexInternal() calls it with "call" once the
     * index is deleting, before it starts or finds the index's job; and a deletion job calls
     * it with "start" when it starts its work, in its thread, also when it takes it again
     * (bergdb 019-38).
     */
    volatile Consumer<String> testHookDelete = null;
    
    /**
     * Not Pub API.
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
    
    public void setRetainDuration(Duration retainDuration) {
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
    
    public IndexBuilder indexBuilder(String indexName) {
        IndexManager.checkIndexName(indexName);
        if (indexManager.hasIndex(indexName)) {
            throw new IndexAlreadyExistsException("Index '" + indexName + "' already exists.");
        }
        return new IndexBuilderImp(indexName, this);
    }
    
    /**
     * @throws NoSuchIndexException
     * @throws DbException
     */
    public Job deleteIndex(final String indexName) {        
        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }
        
        return deleteIndexInternal(indexName);
    }
    
    /**
     * Like deleteIndex(), but no checks. Used internally, not for Pub API user.
     * 
     * @throws NoSuchIndexException
     * @throws DbException
     */
    public Job deleteIndexInternal(final String indexName) {
        final ConnectionImp connection = new ConnectionImp(this);
        final Db db = connection.getDb();
        final IndexManager.Index index;
        
        index = indexManager.ensureDeletingState(connection, indexName);
            // After this method returns, there should be no more index entries added to the
            // index directory (IKP/i/<indexName>/).
        sync(SyncLevel.ORDINARY);
        
        final Consumer<String> callHook = testHookDelete;
        if (callHook != null) {
            callHook.accept("call");
        }
        
        final long[] deletedCounter = new long[1];    
            // Shared between anonymous classes and removeIndexEntries()
        final boolean[] done = new boolean[1];      // Set at the end of the work (bergdb 019-40)
        
        final Thread thread = new Thread(new Runnable() {
            public void run() {
                long retryWait = RwTransaction.FIRST_SLEEP;
                while (true) {
                    try {
                        final Consumer<String> hook = testHookDelete;
                        if (hook != null) {
                            hook.accept("start");
                        }
                        indexManager.deleteIndexEntries(indexName, db, deletedCounter);
                        indexManager.deleteIndexInfo(connection, index);
                        sync(SyncLevel.ORDINARY);
                        done[0] = true;
                    } catch (DbStoppingException e) {
                        // empty, delete job will continue when database is started again.
                    } catch (DbFailedException e) {
                        // empty, the database has failed (bergdb 005-01); the delete job will
                        // continue when the database is started again.
                    } catch (StreamIoException e) {
                        // empty, this will only happen when database is stopping, so it is
                        // expected. The delete job will continue when database is started again.
                    } catch (IllegalDbStateException e) {
                        // empty, the database has stopped; the delete job will continue when
                        // the database is started again.
                    } catch (DbException | LookupTimeNotAvailableException e) {
                        // A refusal of a transaction of the job, or an expired read: not a
                        // failure. The job takes its work again after a wait, as after a
                        // conflict (2026-11-06, bergdb 019-38; docs/levels.md, section 3).
                        // Since 019-10 it failed the database; before, it ended the thread.
                        retryWait = IndexBuilderImp.waitToRetry(retryWait);
                        continue;
                    } catch (Throwable e) {
                        // Anything else, a bug or an Error, fails the database, as on BergDB's
                        // other threads (2026-11-06, bergdb 019-10; 010-01, P7).
                        db.internal().fail(e);
                    }
                    return;
                }
            }
        });
        thread.setPriority(Thread.MIN_PRIORITY);
        thread.setDaemon(true);
        thread.setName(DatabaseImp.class.getSimpleName() + "-delete-" 
                + indexName + "-" + thread.getId());
        
        final Job job = new Job() {
            public JobStatus getStatus() {
                final int progress = thread.isAlive() ? -1 : 100;
                final boolean stopped = progress == 100 && !done[0];  // After isAlive().
                final long count = deletedCounter[0];
                
                return new JobStatus() {
                    public int progress() {
                        return progress;
                    }

                    public String note() {
                        if (stopped) {
                            // A stop, a close or a failure ended the thread (bergdb 019-40,
                            // 015-61); the deletion goes on at the next start. It said "Done!".
                            return "Stopped: the deletion of index '" + indexName + "' goes on "
                                    + "at the next start; " + count + " entries deleted so far.";
                        }
                        String result = progress == 100 ? 
                                "Done! Deleted '" + indexName + "', " + count + " index entries were deleted."
                                : "Working on deleting index '" + indexName + "', deleted " + count + " entries.";
                        return result;
                    }
                };
            }

            public JobStatus join() {
                return join(0);
            }

            public JobStatus join(int millis) {
                try {
                    thread.join(millis);
                } catch (InterruptedException e) {
                    // The caller was interrupted: the wait ends, the job goes on (2026-10-27,
                    // bergdb 005-46). It threw an Error.
                    Thread.currentThread().interrupt();
                }
                return getStatus();
            }
        };
        
        return indexManager.startDeletionJob(index, job, thread);
    }
}
