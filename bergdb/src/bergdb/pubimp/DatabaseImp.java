package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.DbStoppingException;
import bergdb.pub.Clock;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.IllegalDbStateException;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.pub.StorageInfo;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamIoException;
import bergdb.stream.FileStream;

/**
 * Implementation of pub.Database. See pub.Database for Javadoc.
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
    private volatile boolean started;
    private final IndexManager indexManager;
    private final ConnectionInitializer connectionInitializer;
        // "final" for now. Could become a setting.
    private final KvToObject kvToObject;
        // "final" for now, could become a setting.
    private final ClassToObject classToObject;
        // "final" for now, could become a setting.
    private final HashMap<Thread, Connection> threadLocalConnections;
    
    public DatabaseImp(final Db db) {
        synchronized (this) {
            assert db != null;
            this.db = db;
            this.threadLocalConnections = new HashMap<Thread, Connection>();
            
            // Note: we could dependency inject CollatorFactory instead of letting this class itself
            // determine based on whether a class in bergdb.pubimpicu exists.
            // Injecting it would increase testability.
            this.indexManager = new IndexManager(new OptionalIcuCollatorFactory());
            
            this.connectionInitializer = new ConnectionInitializer() {
                public void initialize(Connection connection) {
                    connection.setLookupTime(Long.MAX_VALUE);
                }
            };
            
            KvToObjectImp k = new KvToObjectImp();
            this.kvToObject = k;
            this.classToObject = k;
            
            this.started = false;
        }
    }
    
    public final Db getDb() {
        return db;
    }
    
    final IndexManager getIndexManager() {
        return indexManager;
    }
    
    final KvToObject getKvToObject() {
        return this.kvToObject;
    }
    
    final ClassToObject getClassToObject() {
        return this.classToObject;
    }
    
    /**
     * @throws IllegalDbStateException
     */
    public Connection connection() {
        if (!started) {
            throw new IllegalDbStateException("start() must be called first.");
        }
        
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
    
    /**
     * @throws IllegalDbStateException
     */
    public Connection newConnection() {
        if (!started) {
            throw new IllegalDbStateException("start() must be called first.");
        }
        
        return new ConnectionImp(DatabaseImp.this);
    }
    
    /**
     * @throws IllegalDbStateException
     * @throws StreamIoException
     */
    public void sync() {
        if (!started) {
            throw new IllegalDbStateException("start() must be called first.");
        }
        
        db.sync();
    }
    
    /**
     * @throws IllegalDbStateException
     * @throws StreamIoException
     */
    public void syncStrong() {
        if (!started) {
            throw new IllegalDbStateException("start() must be called first.");
        }
        
        db.syncStrong();
    }
    
    /**
     * @throws IllegalDbStateException
     * @throws StreamIoException
     */
    public void syncInternal() {
        db.sync();
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalDbStateException  If start() has been called already.
     * @throws BadReplicaException
     */
    public synchronized List<Job> start() {
        if (started) {
            throw new IllegalDbStateException("start() was already called, cannot start " +
            		"database again.");
        }
        
        db.start();
        
        ConnectionImp connection = new ConnectionImp(this);
        indexManager.initFromDatabase(connection);
        List<Job> jobs = indexManager.finishOngoingJobs(this);        
        this.started = true;
        return jobs;
    }
    
    public synchronized void stop() {
        synchronized (threadLocalConnections) {
            threadLocalConnections.clear();
        }
        
        db.stop();
    }
    
    public synchronized void close() {
        synchronized (threadLocalConnections) {
            threadLocalConnections.clear();
        }
        
        db.close();
    }
    
    public Job addReplica(String name, String dir) throws IOException {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        if (name.length() == 0) {
            throw new IllegalArgumentException("Empty string not allowed for 'name'.");
        }
        
        if (dir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        
        if (dir.length() == 0) {
            throw new IllegalArgumentException("Empty string not allowed for 'dir'.");
        }
        
        FileStream stream = new FileStream(new File(dir));
        int bufferSize = StorageManager.DEFAULT_REPLICA_BUFFER_SIZE;
        int bufferTime = StorageManager.DEFAULT_REPLICA_BUFFER_TIME;
        return db.addReplica(name, stream, bufferSize, bufferTime);
    }
    
    public void removeReplica(String name) {
        db.removeReplica(name);
    }
    
    public StorageInfo[] getStorageInfos() {
        return db.getStorageInfos();
    }
    
    public final long getTime() {
        return db.getTime();
    }
    
    public final long getRetainDuration() {
        return db.getRetainDuration();
    }
    
    public void setRetainDuration(long retainDuration) {
        long limit = 1 * Clock.UNITS_PER_SEC;
        
        if (retainDuration < 1 * Clock.UNITS_PER_SEC) {
            throw new IllegalArgumentException("retainDuration too small, must be at least " 
                    + limit + ".");
        }
        
        db.setRetainDuration(retainDuration);
    }
    
    public final long getFirstAvailableLookupTime() {
        return db.getTime();
    }
    
    public IndexBuilder indexBuilder(String indexName) {
        if (!started) {
            throw new IllegalStateException("start() must be called first.");
        }
        
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
        if (!started) {
            throw new IllegalStateException("start() must be called first.");
        }
        
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
        syncInternal();
        
        final long[] deletedCounter = new long[1];    
            // Shared between anonymous classes and removeIndexEntries()
        
        final Thread thread = new Thread(new Runnable() {
            public void run() {
                try {
                    indexManager.deleteIndexEntries(indexName, db, deletedCounter);
                    indexManager.deleteIndexInfo(connection, index);
                    syncInternal();
                } catch (DbStoppingException e) {
                    // empty, delete job will continue when database is started again.
                } catch (StreamIoException e) {
                    // empty, this will only happen when database is stopping, so it is
                    // expected. The delete job will continue when database is started again.
                }
            }
        });
        thread.setPriority(Thread.MIN_PRIORITY);
        thread.setDaemon(true);
        thread.setName(DatabaseImp.class.getSimpleName() + "-delete-" 
                + indexName + "-" + thread.getId());
        thread.start();
        
        return new Job() {
            public JobStatus getStatus() {
                final int progress = thread.isAlive() ? -1 : 100;
                final long count = deletedCounter[0];
                
                return new JobStatus() {
                    public int progress() {
                        return progress;
                    }

                    public String note() {
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
                    throw new Error("Unexpected interrupt of internal thread: " 
                            + thread.toString() + ".");
                }
                return getStatus();
            }
        };
    }
}
