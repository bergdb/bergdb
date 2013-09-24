package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;

import bergdb.common.EventToWaitFor;
import bergdb.core.DbStoppingException;
import bergdb.core.GetMany;
import bergdb.core.KeyTransformation;
import bergdb.core.Keys;
import bergdb.core.Kvt;
import bergdb.pub.Action;
import bergdb.pub.BadFormatException;
import bergdb.pub.DataFormatException;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.pub.RwEnvironment;
import bergdb.pub.Transaction;
import bergdb.storage.StreamIoException;

/**
 * @see bergdb.pub.IndexBuilder
 * @author Frans Lundberg
 */
public class IndexBuilderImp implements IndexBuilder {
    private boolean createInited = false;
    private final List<String> dirList;
    private List<CompositePart> parts;
    private CompositePart currentPart;
    private final IndexManager indexManager;
    private final ConnectionImp connection;
    private final String indexName;
    private IndexManager.Index index;       // The index that was created.
    private int bunchSize = 25;             // How many index entries to create in one bunch - in one transaction.
    
    public IndexBuilderImp(String indexName, DatabaseImp database) {
        assert indexName != null;
        assert database != null;
        
        this.indexName = indexName;
        this.indexManager = database.getIndexManager();
        this.connection = new ConnectionImp(database);
        parts = new ArrayList<CompositePart>();
        dirList = new ArrayList<String>();
    }
    
    /**
     * Returns the created index; not part of the Pub API.
     */
    public IndexManager.Index getIndex() {
        return index;
    }
    
    public IndexBuilder nextCompositeLevel() {
        CompositePart part = new CompositePart();
        parts.add(part);
        this.currentPart = part;
        return this;
    }

    public IndexBuilder type(String indexTypeString) {
        if (indexTypeString == null) {
            throw new IllegalArgumentException("'indexTypeString' == null not allowed");
        }
        
        if (!indexManager.typeSupported(indexTypeString)) {
            throw new IllegalArgumentException("Index type '" + indexTypeString
                    + "' not supported.");
        }
        
        nextCompositeLevel();
        
        this.currentPart.typeString = indexTypeString;
        return this;
    }

    public IndexBuilder dir(String udir) {
        String idir = PubKeys.udir2idir(udir);    // throws BadFormatException
        
        if (dirList.size() >= 127) {
            throw new IllegalArgumentException("To many directories, more than 127 is not allowed.");
        }
        
        if (createInited) {
            throw new IllegalStateException("Dir cannot be added when index creation started, " +
                    "dir: " + udir + ".");
        } 
        
 //System.out.println("idir = " + idir);
        
        dirList.add(idir);
        return this;
    }

    public IndexBuilder field(String field) {
        if (field == null) {
            throw new IllegalArgumentException("field == null not allowed");
        }
        
        if (field.length() == 0) {
            throw new IllegalArgumentException("The empty string for 'field' is not allowed.");
        }
        
        if (field.contains(" ")) {
            throw new IllegalArgumentException("Field name cannot contain a space, " +
            		"'" + field + "'.");
        }
        
        if (field.contains(",")) {
            throw new IllegalArgumentException("Field name cannot contain a comma, '" 
                    + field + "'.");
        }
        
        if (currentPart == null) {
            throw new IllegalStateException("Call type() before field().");
        }
        
        if (currentPart.fields.size() >= 127) {
            throw new IllegalArgumentException("To many fields, more than 127 is not allowed, " +
            		"field: " + field + ".");
        }
        
        if (createInited) {
            throw new IllegalStateException("Field cannot be added when index creation started, " +
            		"field: " + field + ".");
        }
        
        currentPart.fields.add(field);
        return this;
    }
    
    public void bunchSize(int size) {
        if (size < 1) {
            throw new IllegalArgumentException("Bad bunch size: " + size + ".");
        }
        this.bunchSize = size;
    }
    
    /**
     * Checks that state is OK for createFast() and start(), throws IllegalStateException to 
     * the Pub API user if appropriate.
     * 
     * @throws IllegalStateException
     */
    private void checkStateBeforeCreate() {
        if (createInited) {
            throw new IllegalStateException("Cannot call create method (createFast/start) again.");
        }
        
        if (dirList.size() == 0) {
            throw new IllegalStateException("No directory specified, cannot create index '" 
                    + indexName + "'.");
        }
        
        if (parts.size() == 0) {
            throw new IllegalStateException("No index type specified, cannot create index '"
                    + indexName + "'.");
        }
        
        for (int i = 0; i < parts.size(); i++) {
            CompositePart part = parts.get(i);
            if (part.fields.size() == 0) {
                String message = parts.size() == 1 ? 
                        "No fields specified, cannot create index '" + indexName + "'."
                      : "No fields specified for index composite part " 
                         + i + " (index type: " + part.typeString + "), cannot create index '"
                         + indexName + "'.";
                throw new IllegalStateException(message);
            }
        }
    }
    
    /**
     * Package access is for testing only. Otherwise should have been private access.
     * 
     * @throws IndexAlreadyExistsException
     */
    IndexCreateState createInit() throws IndexAlreadyExistsException {
        String[] dirs = dirList.toArray(new String[0]);
        String[][] fields = new String[parts.size()][];
        String[] typeStrings = new String[parts.size()];
        
        for (int i = 0; i < parts.size(); i++) {
            CompositePart part = parts.get(i);
            assert part != null;
            fields[i] = part.fields.toArray(new String[0]);
            assert fields[i].length > 0;
            typeStrings[i] = part.typeString;
            assert part.typeString != null;
            assert part.typeString.length() > 0;
        }
        
        createInited = true;
        
        index = indexManager.addIndex(connection, indexName, dirs, fields, typeStrings);
        assert index.getState() == IndexManager.Index.STATE_CREATING;
        
        IndexCreateState createState = new IndexCreateState(index);
        return createState;
    }

    /**
     * @throws IndexAlreadyExistsException
     * @throws IllegalStateException
     */
    public void createFast() {
        checkStateBeforeCreate();
        createInit();
        indexManager.setIndexStateToActive(connection, index);
        assert index.getState() == IndexManager.Index.STATE_ACTIVE;
    }
    
    private EventToWaitFor createInThread_waitEvent;
    
    /**
     * Used for testing only.
     */
    public void createInThreadWaitEvent(EventToWaitFor event) {
        createInThread_waitEvent = event;
    }
    
    /**
     * @throws IndexAlreadyExistsException
     * @throws IllegalStateException
     */
    public Job start() {
        checkStateBeforeCreate();
        final IndexCreateState createState = createInit();
        final Thread thread = createInThread(createState);
        
        return new Job() {
            public JobStatus getStatus() {
                return createState.getJobStatus();
            }

            public JobStatus join() {
                return join(0);
            }

            public JobStatus join(int ms) {
                // It would be possible for BergDB user to interrupt this this.
                // Threads are globally accessible through Thread.getAllStackTraces(), or ThreadGroup.
                
                try {
                    thread.join(ms);
                } catch (InterruptedException e) {
                    throw new Error("Internal database thread unexpectedly interruped. thread: " 
                            + thread);
                }
                return createState.getJobStatus();
            }
        };
    }
    
    /**
     * @throws IndexAlreadyExistsException
     */
    public Thread createInThread(final IndexCreateState createState) {
        final EventToWaitFor event = createInThread_waitEvent;   // Event used for testing.
        
        Thread t = new Thread(new Runnable() {
            public void run() {
                if (event != null) {
                    event.waitForEvent();
                }
                
                while (!createState.isDone) {
                    long t0 = System.nanoTime();
                    
                    try {
                        createStep(createState);
                    } catch (StreamIoException e) {
                        // Empty. This is expected if the database is stopped.
                        // The index creation will continue when the database is restarted.
                    } catch (DbStoppingException e) {
                        // Empty. This is expected if the database is being stopped.
                        // The index creation will continue when the database is restarted.
                    }
                    
                    long duration = (System.nanoTime() - t0);
                    
                    if (!createState.isDone) {
                        // Sleep 50 % of the step time to keep index creation in the background.
                        long ms = duration / 1000000;
                        int nanos = (int) (duration % 1000000);
                        try {
                            Thread.sleep(ms / 2, nanos / 2);
                        } catch (InterruptedException e) {
                            throw new Error("Internal thread was interrupted.");
                        }
                    }
                }
            }
        });
        
        t.setPriority(Thread.MIN_PRIORITY);
        t.setDaemon(true);
        t.setName("IndexBuilderImp-CreateIndex-" + createState.index.getName() + "-" + t.getId());
        t.start();
        return t;
    }
    
    /**
     * Takes one step in index creation.
     * Dividing the work into steps is useful for testing.
     * 
     * @throws DataFormatException
     */
    public void createStep(final IndexCreateState createState) throws DataFormatException {
        if (createState.isDone) {
            return;
        }
        
        final String dir = createState.index.dirs[createState.dirId];
        final long[] dirKey = Keys.toSegments(dir);
        final int dirIndex = createState.dirId;
        final boolean[] isDone = new boolean[1];
        final long[] processedEntries = new long[1];
        
        if (createState.startKey == null) {
            createState.startKey = Keys.toSegments(dir);
        }
        
        final GetMany[] gArray = new GetMany[] { null };
        
        isDone[0] = false;
        
        Transaction transaction = connection.rw(new Action() {
            public void run(final RwEnvironment environment) {
                final RwEnvironmentImp env = (RwEnvironmentImp) environment;
                processedEntries[0] = 0;
                
                GetMany g = new GetMany();
                gArray[0] = g;
                g.startKey = createState.startKey;
                g.inclusive = false;
                    
                // Stop condition allows iteration until 100 KVs, eod(), or end of directory.
                
                g.stopCondition = new GetMany.StopCondition() {
                    private int count = 0;
                    private final int maxCount = IndexBuilderImp.this.bunchSize;
                    
                    public int handleKvt(Kvt kvt) {
                        int result = GetMany.StopCondition.ADD;
                        processedEntries[0]++;
                        
                        String keyString = Keys.toString(kvt.key);   
                            // TODO X LATER Consider Keys.toString() here, dangerous (?), not all keys are strings!
                        if (!keyString.endsWith(".obj")) {
                            result = GetMany.StopCondition.CONTINUE;
                            return result;
                        }
                        
                        count++;
                        if (count == maxCount) {
                            result = GetMany.StopCondition.ADD_AND_STOP;
                        }
                        
                        if (!Keys.isPrefix(dirKey, kvt.key)) {
                            result = GetMany.StopCondition.STOP;
                            isDone[0] = true;
                        }
                    
                        return result;
                    }
                    
                    public void eod() {
                        isDone[0] = true;
                    }
                };
                
                env.getMany(g);
                
                for (Kvt kvt : g.result) {
                    String keyname = Keys.toString(kvt.key).substring(dir.length());
                    DbObject dbo;
                    
                    try {
                        dbo = new DbObject(kvt.value, null);
                    } catch (BadFormatException e) {
                        throw new DataFormatException(e.getMessage());
                    }
                    
                    RwEnvironmentImp.setIndexEntry(dbo, keyname, createState.index, dirIndex, new RwEnvironmentImp.IndexSetter() {
                        public void setIndexKey(byte[] indexKey, KeyTransformation kt) {
                            env.set(indexKey, new byte[0], kt);
                        }
                    }, false);
                }
            }
        });
        
        try {
            transaction.execute();
        } catch (DbStoppingException e) {
            // Special case, index creation while database is stopping.
            // This is fine, index creation will continue once database is started 
            // again.
            
            createState.isDone = true;
            return;
        }
        
        if (isDone[0]) {
            if (createState.dirId == createState.index.dirs.length - 1) {
                createState.update(true, createState.processedEntries + processedEntries[0]);
                    // Done with all directories
                indexManager.setIndexStateToActive(connection, createState.index);
            } else {
                createState.update(false, createState.processedEntries + processedEntries[0]);
                createState.dirId++;
                createState.startKey = Keys.toSegments(createState.index.dirs[createState.dirId]);
            }
        } else {
            // There is more from current directory (from index.dirs[createState.dirId]).
            createState.update(false, createState.processedEntries + processedEntries[0]);
            GetMany g = gArray[0];
            createState.startKey = g.result.get(g.result.size() - 1).key;
        }
    }
    
    private static class CompositePart {
        String typeString;
        List<String> fields;
        
        public CompositePart() {
            this.typeString = null;
            this.fields = new ArrayList<String>();
        }
    }
    
    static class IndexCreateState {
        public final IndexManager.Index index;
        public long processedEntries = 0;
        
        // dirId to use for next step
        public int dirId;
        
        // startKey to use for next step
        public long[] startKey;
        
        public boolean isDone;
        
        public IndexCreateState(IndexManager.Index index) {
            assert index != null;
            assert index.dirs.length > 0;
            
            synchronized (this) {
                this.dirId = 0;
                this.index = index;
                this.startKey = Keys.toSegments(index.dirs[dirId]);
                this.isDone = false;
            }
        }
        
        /**
         * Atomic update to fields needed to getJobStatus().
         */
        public synchronized void update(boolean isDone, long processedEntries) {
            this.isDone = isDone;
            this.processedEntries = processedEntries;
        }
        
        public synchronized JobStatus getJobStatus() {
            // May be called from any thread. Synch accordingly.
            
            final int progress = isDone ? 100 : -1;
            
            return new JobStatus() {
                public int progress() {
                    return progress;
                }

                public String note() {
                    String result = 
                            progress == 100 ? 
                              "Done! Processed " + processedEntries + " entries for index: " 
                                    + index.getName() + "." 
                            : "Working, processed " + processedEntries + " entries for index: " 
                                    + index.getName() + ".";
                    return result;
                }
            };
            
        }
    }
}
