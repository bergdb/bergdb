package bergdb.core;

import java.lang.ref.ReferenceQueue;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.common.AssertStatus;
import bergdb.core.Cache.DbInfo;
import bergdb.core.Cache2.AlreadyHasNode;
import bergdb.core.Cache2.Evictor;
import bergdb.core.Cache2.NodeReference;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;

/**
 * A deterministic node cache; size is known, weak references are *not* used.
 * The cache ensures there is never more than one Node object with a given
 * node id.
 * 
 * @author Frans Lundberg
 */
public class Cache3 implements Cache {
    //
    // Simple, non-optimal implementation to start with. 
    // Cache-global locking to start with.
    // What synchronization do we need here? Any? Cache-global? Let consumers do it?
    // Same interface as Cache2 to start with.
    //
    
    private static final long INITIAL_CACHE_SIZE = 10*1000;
    private final PointerLocks pointerLocks;
    private final Cache.DbInfo dbInfo;
    private final Object lock;
    private long sizeIndicator;
    private long totalSize;     // total cache size estimation, in bytes
    private long putSize;
    private final HashMap<Long, Node> map;

    public Cache3(PointerLocks pointerLocks, Cache.DbInfo dbInfo) {
        assert pointerLocks != null;
        assert dbInfo != null;
        
        this.lock = new Object();
        this.pointerLocks = pointerLocks;
        this.dbInfo = dbInfo;
        this.totalSize = INITIAL_CACHE_SIZE;
        this.putSize = INITIAL_CACHE_SIZE;
        this.map = new HashMap<Long, Node>();
        
        synchronized (lock) {}
    }
    
    /**
     * Sets the user-suggested size of the cache (in bytes).
     */
    public void setSizeIndicator(long sizeIndicator) {
        assert sizeIndicator > 0;
        
        if (sizeIndicator < 4*1000000) {
            sizeIndicator = 4*1000000;
        }
        
        synchronized (lock) {
            this.sizeIndicator = sizeIndicator;
        }
    }
    
    public long getSizeIndicator() {
        synchronized (lock) {
            return sizeIndicator;
        }
    }

    public void cleanupAllRefQueues() {
        // not applicable for this implementation.
    }
    
    public void putIndexNode(Node node) {
        putNode(node);
    }
    
    public void putValueNode(ValueNode node) {
        putNode(node);
    }
    
    public Node getIndexNode(long id) {
        return getNode(id);
    }
    
    public ValueNode getValueNode(long id) {
        return (ValueNode) getNode(id);
    }
    
    public Object getIndexLockObject(long id) {
        return lock;
    }
    
    public Object getValueLockObject(long id) {
        return lock;
    }
    
    public long totalSize() {
        synchronized (lock) {
            return totalSize;
        }
    }

    public long putSize() {
        synchronized (lock) {
            return putSize;
        }
    }
    
    private void putNode(Node node) {
        // Note that memory size *does* change for key nodes.
        
        int memorySize = node.getMemSize();
        long id = node.getId();
        
        synchronized (lock) {
            Node previous = map.put(id, node);
            if (previous != null) {
                throw new AlreadyHasNode("Already has node with id " + id);
            }
            
            totalSize += memorySize;
        }
    }
    
    private Node getNode(long id) {
        synchronized (lock) {
            return map.get(id);
        }
    }
    
    public static class AlreadyHasNode extends AssertionError {
        private static final long serialVersionUID = 1L;
        
        public AlreadyHasNode(String message) {
            super(message);
        }
    }
}
