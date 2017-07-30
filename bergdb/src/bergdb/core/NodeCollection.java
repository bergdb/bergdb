package bergdb.core;

import bergdb.dag.Dag.CachePolicy;
import bergdb.dag.Dag.PointerListener;
import bergdb.dag.AccessData;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.PointerFollower;

/**
 * A node collection for Db to use.
 * An instance of this class adds a cache to NodeStream
 * and implements PointerFollower for Db.
 * 
 * @author Frans Lundberg
 */
public class NodeCollection implements PointerFollower {
    //
    // Idea is to split into 1000 maps and do evict by
    // map scan (whole map, but that's 1/1000 of whole cache).
    //
    
    private NodeStream nodeStream;
    private Cache3 cache;
    private PointerLocks pointerLocks;
    
    public NodeCollection(Cache.DbInfo dbInfo, NodeStream nodeStream) {
        this.nodeStream = nodeStream;
        this.cache = new Cache3(dbInfo);
        this.pointerLocks = dbInfo.getPointerLocks();
    }

    public Node followPointer(Node predecessor, int pointerIndex, long accessData,
            PointerListener pointerListener, CachePolicy cachePolicy) {
        //
        // It is possible that concurrent threads will read same node 
        // from stream and try to add it to the cache. That is why we need to use existing 
        // node from cache if there is one there. See [synchronized (cacheLock)]
        // clauses in this method.
        //
        // Note, it is possible to avoid holding 'lock' while reading from stream, 
        // I believe. The node in the stream is immutable. 
        // So, the algo would be to first acquire 'lock', then if pointer is
        // a memory pointer (isMem() == true), just set access data and call 
        // listener.pointerFollowed().
        // If it is a stream pointer, release 'lock', read node, and acquire lock 
        // again. Then do the same, if isMem() do the same as above, else handle
        // the stream pointer case, but now we have read the node already and can 
        // quickly do what we should without blocking I/O call while holding 'lock'.
        //
        
        Node result;
        assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
        assert predecessor != null : "predecessor is null";
        assert accessData == 0 || AccessData.isValid(accessData);

        final Object pointerLock = pointerLocks.getLock(predecessor, pointerIndex);

        synchronized (pointerLock) {
            Node pointerNode = predecessor.getPointerNode(pointerIndex);
            long pointerPos = predecessor.getPointerPos(pointerIndex);

            assert !Pointer.isNull(pointerNode, pointerPos) : "Pointer is null: " + pointerNode
                    + ", " + pointerPos;

            if (Pointer.isMem(pointerNode)) {
                result = pointerNode;
                if (accessData != 0) {
                    predecessor.setPointerAccessData(pointerIndex, accessData);
                }
                
                pointerListener.pointerFollowed(
                        predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            
            } else {
                assert pointerPos >= 0 && pointerPos % 2 == 0 
                        : "bad pointerPos (" + pointerPos + "), to read from stream"
                          + ", pointerIndex:" + pointerIndex + ", predecessor:" + predecessor.print();
                
                NodeHeader header = nodeStream.readNodeHeader(pointerPos);
                long id = header.id();
                
                result = cache.getNode(id);
                
                if (result == null) {
                    result = nodeStream.readNode(pointerPos);
                    
                    assert result.getId() == header.id() 
                            : "ids differ, " + result.getId() + " != " + header.id();
                    assert result.getType() == header.type()
                            : "types differ, " + result.getType() + ", " + header.type();
                    
                    if (cachePolicy.shouldCache(result)) {
                        cache.pointerCreated(predecessor, pointerIndex, result);
                        predecessor.setPointer(pointerIndex, result, accessData);
                    }
                    
                    pointerListener.pointerFollowed(
                            predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
                }
            }
        }
        
        return result;
    }
}
