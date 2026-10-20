package bergdb.core;

import bergdb.dag.KeyNode;
import bergdb.dag.TopNode;

/**
 * Interface to the collection of dirty nodes.
 * 
 * @author Frans Lundberg
 */
public interface IDirtyNodes {

    
    /**
     * The method subset of core.TransNodes needed by this class.
     * This type is useful to minimize dependency, good for testing / mocks.
     */
    public static interface TransNodesForMe {
        public void addTopNode(TopNode node);
        public void addKeyNode(KeyNode node);
    }
}