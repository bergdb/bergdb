package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;

import bergdb.common.Bug;
import bergdb.common.Create;
import bergdb.common.ProgressListener;
import bergdb.common.Util;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.KeyNodeTester;
import bergdb.dag.Pointer;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.BadReplicaException;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StorageManager;
import bergdb.stream.AppendOnlyStream;

/**
 * Methods to help the Db implementation.
 * This class should only be used by Db.
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
        
        final Db db;
        final StorageManager storageManager;
        final Object progressLock = new Object();
        final int[] progressValue = new int[] { 0 };
        final String[] progressNote = new String[] { "About to start to synch." };

        // TODO LATER Make sure this class is tested.
        
        private AddReplicaClass(StorageManager storageManager, Db db) {
            this.storageManager = storageManager;
            this.db = db;
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
                    Trans trans = db.trans().put(DbConstants.DUMMY_KEY, new byte[0]).build();
                    db.execute(trans);
                    db.sync(trans.lastPos, SyncLevel.STRONG);
    
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

    /**
     * Returns true if the node has at least one in-memory child
     * that is dirty.
     */
    static boolean hasDirtyChild(Node node) {
        int count = node.getSize();
        Pointer p = new Pointer();
        
        for (int i = 0; i < count; i++) {
            node.getPointer(i, p);
            if (!p.isNull()) {
                Node child = node.getPointerNode(i);
                if (child != null && child.isDirty()) {
                    return true;
                }
            }
        }
        
        return false;
    }

    /**
     * Adds nodes that are still dirty to got-dirty nodes.
     * A node is still dirty after being written to stream if any of its 
     * children is dirty.
     */
    static int handleStillDirtyNodes(Iterator<Node> input, TransSeq.NodeSink output) {
        int stillDirtyCount = 0;
        
        while (input.hasNext()) {
            Node node = input.next();
            
            if (!node.isDirty() && hasDirtyChild(node)) {
                node.setDirty(true);
                output.addNode(node);
                stillDirtyCount++;
            }
        }
        
        return stillDirtyCount;
    }
    
    
    // ======== Testing ========
    
    @Nano private static void testHandleStillDirtyNodes1() {
        KeyNodeTester tester = new KeyNodeTester();
        KeyNode k1 = tester.createT2();
        KeyNode k2 = tester.t2Pointers[0];   // child of k1
        KeyNode k3 = tester.t2Pointers[1];   // child of k1
        KeyNode k4 = new KeyNode();
        
        k1.setDirty(false);
        k2.setDirty(true);
        k3.setDirty(false);
        k4.setDirty(false);
        
        Iterator<Node> iter = Create.list((Node) k1, k2, k3, k4).iterator();
        final ArrayList<Node> nodes = new ArrayList<Node>();
        
        TransSeq.NodeSink output = new TransSeq.NodeSink() {
            public void addNode(Node node) {
                nodes.add(node);
            }
        };
        
        handleStillDirtyNodes(iter, output);
        
        Assert.assertEquals(1, nodes.size());
        Assert.assertEquals(k1, nodes.get(0));
        Assert.assertTrue(k1.isDirty());
        Assert.assertTrue(k2.isDirty());
        Assert.assertFalse(k3.isDirty());
        Assert.assertFalse(k4.isDirty());
    }
}
