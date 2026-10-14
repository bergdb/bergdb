package bergdb.core;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;

public interface Cache {

    /**
     * User-suggested maximum cache size in bytes.
     */
    public void setSizeIndicator(long sizeIndicator);

    /**
     * Gets actual suggested maximum cache size (in bytes).
     */
    public long getSizeIndicator();

    public void putIndexNode(Node node);

    public void putValueNode(ValueNode node);

    public Node getIndexNode(long id);

    public ValueNode getValueNode(long id);

    public Object getIndexLockObject(long id);

    public Object getValueLockObject(long id);

    public long totalSize();

    public long putSize();

    /**
     * Source of dynamic information about the database state
     * needed by the cache implementation. Easy to mock.
     */
    public interface DbInfo {
        public long getStartupPosForEvict();
        public PointerLocks getPointerLocks();
    }
    
}
