package bergdb.core;

import java.io.IOException;

import bergdb.common.Bug;
import bergdb.common.ProgressListener;
import bergdb.common.Util;
import bergdb.pub.BadReplicaException;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StorageManager;
import bergdb.stream.AppendOnlyStream;

/**
 * Methods to help the Db implementation.
 * 
 * @author Frans Lundberg
 */
public class DbHelper {

    private DbHelper() {}
    
    /**
     * Reads stream ID of replicaStream and compares with mainId; throws
     * exception if IDs do not match.
     * 
     * @throws BadReplicaException
     *      If the stream length is greater than 0 and the IDs are not equal.
     */
    static void checkReplicaId(byte[] mainId, final AppendOnlyStream replicaStream) {
        if (replicaStream.getLength() == 0) {
            return;
        }

        RecoverableStream rStream = new RecoverableStream(replicaStream, new MetaBlock());
        MetaBlock meta = rStream.readLastValidMetaBlock();
        if (meta == null) {
            throw new BadReplicaException("Found no valid meta block in replica stream; " +
            		"replica length: " + replicaStream.getLength() + ".");
        }
        
        byte[] replicaId = meta.getId();
        
        if (replicaId == null) {
            throw new Bug("replicaId == null");
        }
        
        if (mainId == null) {
            throw new Bug("mainId == null");
        }
        
        if (replicaId.length == 0) {
            throw new Bug("replicaId.length == 0");
        }
        
        if (mainId.length == 0) {
            throw new Bug("mainId.length == 0");
        }

        if (!Util.areEqual(mainId, replicaId)) {
            throw new BadReplicaException("ID of replica stream (" + Util.toHexString(replicaId)
                    + ") does not match database ID (" + Util.toHexString(mainId) + ").");
        }
    }
    
    /**
     * Helper class for the Db.addReplica() method.
     */
    static class AddReplicaClass {
        // progressValue and progressNote are sync protected by progressLock.
        
        Db db;
        StorageManager storageManager;
        final Object progressLock = new Object();
        final int[] progressValue = new int[] { 0 };
        final String[] progressNote = new String[] { "About to start to synch." };

        private AddReplicaClass(StorageManager storageManager, Db db) {
            this.storageManager = storageManager;
        }
        
        static Job addReplica(StorageManager storageManager, Db db, String name, AppendOnlyStream replicaStream, 
                int bufferSize, int bufferTime) throws IOException {
            AddReplicaClass add = new AddReplicaClass(storageManager, db);
            return add.addReplica(name, replicaStream, bufferSize, bufferTime);
        }
        
        private Job addReplica(String name, AppendOnlyStream replicaStream, 
                int bufferSize, int bufferTime) throws IOException {
        
            final ProgressListener progressListener = new ProgressListener() {
                public void progress(int myProgressValue, String myProgressNote) {
                    synchronized (progressLock) {
                        if (myProgressValue == 100) {
                            progressValue[0] = 99;
                            progressNote[0] = "Almost done, waiting for syncString...";
                        } else {
                            progressValue[0] = myProgressValue;
                            progressNote[0] = myProgressNote;
                        }
                    }
                }
            };

            final StorageManager.SynchingStorage ss = storageManager.addReplica(name, replicaStream,
                    bufferSize, bufferTime);
    
            final Thread syncThread = new Thread(new Runnable() {
                public void run() {
                    storageManager.syncReplica(ss, progressListener);
                    Trans trans = Trans.builder().put(Db.DUMMY_KEY, new byte[0]).build();
                    db.execute(trans);
                    db.syncStrong(trans.lastPos);
    
                    synchronized (progressLock) {
                        progressValue[0] = 100;
                        progressNote[0] = "Done!";
                    }
                }
            });
            syncThread.setName("db-addReplica-sync-" + name + "-" + syncThread.getId());
            syncThread.setPriority(Thread.NORM_PRIORITY - 1);
            syncThread.start();
    
            // Adaptor, adapts Thread + ProgressListener to a Job.
            
            Job job = new Job() {
                public JobStatus getStatus() {
                    final int pValue;
                    final String pNote;
    
                    synchronized (progressLock) {
                        pValue = progressValue[0];
                        pNote = progressNote[0];
                    }
    
                    return new JobStatus() {
                        public int progress() {
                            return pValue;
                        }
    
                        public String note() {
                            return pNote;
                        }
                    };
                }
    
                public JobStatus join() {
                    return join(0);
                }
    
                public JobStatus join(int millis) {
                    try {
                        syncThread.join(millis);
                    } catch (InterruptedException e) {
                        throw new Error("Internal thread unexpectedly interrupted.");
                    }
                    return getStatus();
                }
            };
            
            return job;
        }
    }
}
