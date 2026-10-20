package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.DbStoppingException;
import bergdb.core.StartInfo;
import bergdb.core.SyncLevel;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.StartupInfo;
import bergdb.pub.Time;
import bergdb.pub.util.Clock;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.StorageInfo;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamIoException;
import bergdb.stream.FileStream;

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
    private final ClassToObject classToObject;
        // "final" for now, could become a setting.
    private final HashMap<Thread, Connection> threadLocalConnections;
    
    private DatabaseImp(final Db db) {
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
                    connection.setLookupTime(Time.MAX);
                }
            };
            
            KvToObjectImp k = new KvToObjectImp();
            this.kvToObjectConverter = k;
            this.classToObject = k;
        }
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalDbStateException  If db has been started already.
     * @throws BadReplicaException
     */
    public static synchronized DatabaseImp createAndStart(final Db db) {
        @SuppressWarnings("unused")
        StartInfo startInfo;
        DatabaseImp database = new DatabaseImp(db);
        
        long t0 = System.nanoTime();
        startInfo = db.start();
        double startTime = (System.nanoTime() - t0) * 1e-9;
        
        ConnectionImp connection = new ConnectionImp(database);
        database.indexManager.initFromDatabase(connection);
        List<Job> jobs = database.indexManager.finishOngoingJobs(database);        
        database.startupInfo = new StartInfoImp(jobs, startTime);
        
        return database;
    }
    
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
    
    final ClassToObject getClassToObject() {
        return this.classToObject;
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
        
        final long[] deletedCounter = new long[1];    
            // Shared between anonymous classes and removeIndexEntries()
        
        final Thread thread = new Thread(new Runnable() {
            public void run() {
                try {
                    indexManager.deleteIndexEntries(indexName, db, deletedCounter);
                    indexManager.deleteIndexInfo(connection, index);
                    sync(SyncLevel.ORDINARY);
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
