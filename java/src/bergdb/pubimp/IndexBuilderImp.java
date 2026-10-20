package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;

import bergdb.common.EventToWaitFor;
import bergdb.core.DbStoppingException;
import bergdb.core.KeyTransformation;
import bergdb.dag.GetMany;
import bergdb.dag.GetMany.StopCondition;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.Action;
import bergdb.pub.DataFormatException;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.RwEnvironment;
import bergdb.pub.util.BadFormatException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
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
    private int bunchSize;                  // Max index entries to create in one bunch - in one transaction.
    
    public IndexBuilderImp(String indexName, DatabaseImp database) {
        assert indexName != null;
        assert database != null;
        
        bunchSize = 25;
        this.indexName = indexName;
        indexManager = database.getIndexManager();
        connection = new ConnectionImp(database);
        parts = new ArrayList<CompositePart>();
        dirList = new ArrayList<String>();
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

    /**
     * @throws BadFormatException
     */
    public IndexBuilder dir(String udir) {
        String idir = PubKeys.udir2idir(udir);    // throws BadFormatException
        
        if (dirList.size() >= 127) {
            throw new IllegalArgumentException("To many directories, more than 127 is not allowed.");
        }
        
        if (createInited) {
            throw new IllegalStateException("Dir cannot be added when index creation started, " +
                    "dir: " + udir + ".");
        } 
        
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
        
        currentPart.fields.add(new FieldRef(field));
        return this;
    }
    
    /**
     * @param fieldSpec String with dots to separate the parts.
     */
    public IndexBuilder nestedField(String fieldSpec) {
        if (fieldSpec == null) {
            throw new IllegalArgumentException("fieldSpec == null not allowed");
        }
        
        String[] parts = fieldSpec.split("\\.");
        return nestedField(parts);
    }
    
    public IndexBuilder nestedField(String[] fieldParts) {
        if (fieldParts == null) {
            throw new IllegalArgumentException("fieldParts == null not allowed");
        }
        
        if (fieldParts.length == 0) {
            throw new IllegalArgumentException("The empty array for 'fieldParts' is not allowed.");
        }
        
        if (currentPart == null) {
            throw new IllegalStateException("Call type() before field().");
        }
        
        if (currentPart.fields.size() >= 127) {
            throw new IllegalArgumentException("To many fields, more than 127 is not allowed.");
        }
        
        if (createInited) {
            throw new IllegalStateException("Field cannot be added when index creation started.");
        }
        
        currentPart.fields.add(new FieldRef(fieldParts));
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
     * Package access is for testing only. Otherwise would have been private.
     * 
     * @throws IndexAlreadyExistsException
     */
    IndexCreateState createInit() throws IndexAlreadyExistsException {
        String[] dirs = dirList.toArray(new String[0]);
        FieldRef[][] fields = new FieldRef[parts.size()][];
        String[] typeStrings = new String[parts.size()];
        
        for (int i = 0; i < parts.size(); i++) {
            CompositePart part = parts.get(i);
            assert part != null;
            fields[i] = part.fields.toArray(new FieldRef[0]);
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
     * Starts the index creation in a new low-priority thread.
     * 
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
                // It would be possible for BergDB user to interrupt this.
                // Threads are globally accessible through ThreadGroup.
                
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
     * Creates a new thread which will create the index.
     * 
     * @throws IndexAlreadyExistsException
     */
    Thread createInThread(final IndexCreateState createState) {
        // Event used for testing.
        final EventToWaitFor event = createInThread_waitEvent;   
        
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
                        break;
                    } catch (DbStoppingException e) {
                        // Empty. This is expected if the database is being stopped.
                        // The index creation will continue when the database is restarted.
                        break;
                    }
                    
                    long duration = (System.nanoTime() - t0);
                    
                    if (!createState.isDone) {
                        sleepFiftyPercentOfDuration(duration);
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
     * Sleeps 50 per cent of the given duration, but never longer than 1 second.
     * 
     * @param duration  The duration in nanoseconds; determines how long to sleep.
     */
    private static void sleepFiftyPercentOfDuration(long duration) throws Error {
        final long maxMillis = 1000;
        long ms = duration / 1000000;
        int nanos = (int) (duration % 1000000);
        
        long msToSleep = ms / 2;
        int nanosToSleep = nanos / 2;
        
        if (msToSleep > maxMillis) {
            ms = maxMillis;
            nanos = 0;
        }
        
        try {
            Thread.sleep(msToSleep, nanosToSleep);
        } catch (InterruptedException e) {
            throw new Error("Internal thread was interrupted.");
        }
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
        
        if (createState.startKey == null) {
            createState.startKey = Keys.toSegments(dir);
        }
        
        final TheStopCondition stopCondition = 
                new TheStopCondition(dirKey, IndexBuilderImp.this.bunchSize);
        
        final GetMany g = connection.getDb().newGetMany();
        g.startKey = createState.startKey;
        g.inclusive = false;
        g.stopCondition = stopCondition;
        
        Action action = new Action() {
            void reset() {
                g.result.clear();
                stopCondition.reset();
            }
            
            public void run(final RwEnvironment environment) {
                // Resetting stuff is important; an Action may be rerun.
                
                reset();
                
                final RwEnvironmentImp env = (RwEnvironmentImp) environment;
                
                env.getMany(g);
                
                RwEnvironmentImp.IndexSetter indexSetter = new RwEnvironmentImp.IndexSetter() {
                    public void setIndexKey(byte[] indexKey, KeyTransformation kt) {
                        env.set(indexKey, new byte[0], kt);
                    }
                };

                for (Kvt kvt : g.result) {
                    String keyname = Keys.toString(kvt.key).substring(dir.length());
                    DbObject dbo;
                    
                    try {
                        dbo = new DbObject(kvt.value, null);
                    } catch (BadFormatException e) {
                        // We silently ignore values that are not DbObjects.
                        // Most non-object values will not get to this anyway.
                        // There is filtering in TheStopCondition; only values starting
                        // with DbObject.MAGIC bytes are returned with env.getMany() call.
                        continue;
                    }
                    
                    RwEnvironmentImp.setIndexEntry(dbo, keyname, createState.index, dirIndex, 
                            indexSetter, false);
                }
            }
        };
        
        try {
            connection.rw(action);
        } catch (DbStoppingException e) {
            // Special case, index creation while database is stopping.
            // This is fine, index creation will continue once database is started again.
            
            createState.isDone = true;
            return;
        }
        
        handleStepResult(createState, stopCondition, g);
    }

    private void handleStepResult(final IndexCreateState createState,
            final TheStopCondition stopCondition, final GetMany g) {
        if (stopCondition.isDone()) {
            if (createState.dirId == createState.index.dirs.length - 1) {
                // Done with all directories.
                createState.update(true, createState.processedEntries + stopCondition.getProcessedEntries());
                indexManager.setIndexStateToActive(connection, createState.index);
            } else {
                // Done with one directory, prepare to process next directory.
                createState.update(false, createState.processedEntries + stopCondition.getProcessedEntries());
                createState.dirId++;
                createState.startKey = Keys.toSegments(createState.index.dirs[createState.dirId]);
            }
        } else {
            // There is more to process from current directory.
            createState.update(false, createState.processedEntries + stopCondition.getProcessedEntries());
            createState.startKey = g.result.get(g.result.size() - 1).key;
        }
    }
    
    private static class CompositePart {
        String typeString;
        List<FieldRef> fields;
        
        public CompositePart() {
            this.typeString = null;
            this.fields = new ArrayList<FieldRef>();
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
            // May be called from any thread; synch accordingly.
            
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
    
    /**
     * Stop condition for GetMany when building an index.
     * Stops when maxCount is reached or if we do not have the dirKey prefix
     * any longer.
     */
    private static class TheStopCondition implements StopCondition {
        private final int maxCount;
        private final long[] dirKey;        
        private int count = 0;
        private int processedEntries = 0;
        private boolean isDone = false;
        
        public TheStopCondition(long[] dirKey, int maxCount) {
            this.maxCount = maxCount;
            this.dirKey = dirKey;
        }
        
        /**
         * Resets the object to the state it was in when
         * first constructed.
         */
        public void reset() {
            count = 0;
            processedEntries = 0;
            isDone = false;
        }
        
        public int handleKvt(Kvt kvt) {
            int result = GetMany.StopCondition.ADD;
            processedEntries++;
            
            String keyString = Keys.toString(kvt.key);
            boolean isObject = Entries.isProbablyDbObject(keyString, kvt.value);
            
            if (!isObject) {
                result = GetMany.StopCondition.CONTINUE;
                return result;
            }
            
            count++;
            if (count == maxCount) {
                result = GetMany.StopCondition.ADD_AND_STOP;
            }
            
            if (!Keys.isPrefix(dirKey, kvt.key)) {
                result = GetMany.StopCondition.STOP;
                isDone = true;
            }
        
            return result;
        }
        
        public void eod() {
            isDone = true;
        }
        
        public boolean isDone() {
            return isDone;
        }
        
        public int getProcessedEntries() {
            return processedEntries;
        }
        
        public String toString() {
            return getClass().getSimpleName() + ":maxCount=" + maxCount;
        }
    }
}
