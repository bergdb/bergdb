package bergdb.core;

import java.util.Random;

import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.EvictData;
import bergdb.dag.Node;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;

/**
 * Handles node eviction for Db. Tightly coupled with Db. Performance-sensitive.
 * 
 * @author Frans Lundberg
 */
public class Evictor {
    Dag dag;
    EvictBoss evictBoss;
    Random evictRandom;
    Db.ExecuteData x;
    Db.Aux aux;
    
    /**
     * Dag must be set later.
     */
    Evictor(Db.Internal internal, EvictBoss evictBoss) {
        evictRandom = new Random(0);      // pseudo-random, but deterministic
        dag = internal.dag();
        this.evictBoss = evictBoss;
        x = internal.x();
        aux = internal.aux();
        
        if (evictBoss == null) throw new IllegalArgumentException("evictBoss == null not allowed");
        if (x == null) throw new IllegalStateException("x is null");
        if (aux == null) throw new IllegalStateException("aux is null");
    }

    /** Call this method to set the Dag before the evict methods. */
    public void setDag(Dag dag) {
        this.dag = dag;
    }

    public final void possiblyEvict(EvictData ed) {
        // Synch note: concurrent access is supported.

        if (evictBoss.evictShouldRun()) {
            evict(ed);
        }
    }

    /**
     * Runs the evict algorithm.
     * 
     * @param ed  Operation-local data.
     */
    public final void evict(EvictData ed) {
        // Synch note: concurrent access by multiple threads is supported
        // by this method. The implement can assume that the EvictData, ed, 
        // is specific for each thread. 'ed' is not shared between concurrent threads.
        
        ed.pointerCount = 0;
        ed.evictCount = 0;
        ed.startupPos = x.startupPos.getForEvict();
        evictInner(ed);
        evictBoss.reportEvict(ed);
    }

    private void evictInner(EvictData ed) {
        //
        // node ----> next1 ---> next2
        //
        // Synch note: concurrent access must be supported by this method.
        // Multiple concurrent readers, one writer.
        // rand is used to somewhat randomly choose nodes to evict.
        // For performance, a single call to evictRandom.nextInt() is used.
        // To increased randomness, the rand value is increased between each time it is used.
        //
        
        final Pointer pointer = ed.tempPointer;

        Node node = dag.getSuperRoot();
        Node next1;
        Node next2;
        long limit = aux.cachedMemoryValue.get() - evictBoss.getCacheDuration();
        
        ed.accessTimeLimit = limit < 0 ? 0 : limit;
            // Nodes accessed after accessTimeLimit are not evictable.
        
        int rand = Math.abs(evictRandom.nextInt());
            // random int used as randomness for this evict operation.
        
        getEvictPointer(node, rand, pointer);
        rand += 31;
        next1 = pointer.node;

        if (next1 == null) {
            // Only superRoot is cached, nothing to evict.
            assert node.getMemoryPointerCount() == 0 : "Count is " + node.getMemoryPointerCount()
                    + " for node " + node + ".";
            return;
        }

        while (true) {
            getEvictPointer(next1, rand, pointer);
            rand += 17;
            next2 = pointer.node;

            if (next2 == null) {
                break;
            }

            // Here we go to the next deeper level.

            node = next1;
            next1 = next2;
            next2 = null;
        }

        // We have selected a node to process.
        evictPointers(node, ed);
    }
    
    private void getEvictPointer(Node node, int rand, Pointer p) {
        int length = node.getSize();
        int index;
        p.node = null;
        p.index = -1;
        
        for (int i = 0; i < length; i++) {
            index = rand % length;
            assert index >= 0 && index < length;
            
            synchronized (dag.getPointerLock(node, index)) {
                node.getPointer(index, p);
            }
            
            if (p.node != null) {
                p.index = index;
                break;
            }
            
            rand += 1;
        }
    }

    /**
     * Evicts all evictable pointers from 'node'.
     */
    private void evictPointers(Node node, EvictData ed) {
        //
        // Iterates the pointers and evicts a pointee that fullfills all conditions:
        // * pointee != null (is a memory pointer)
        // * Spos of pointee is not Spos.NULL
        // * Spos of pointee is smaller than current startup pos of database.
        // * Access time of pointer is LTE ed.accessTimeLimit (pointer not recently accessed).
        //
        
        long spos = node.getSpos();
        if (!Spos.isValid(spos) || spos >= ed.startupPos) {
            return;
        }
        
        int count = node.getSize();
        for (int i = 0; i < count; i++) {
            synchronized (dag.getPointerLock(node, i)) {
                Node pointee = node.getPointerNode(i); 
                
                if (pointee != null) {
                    long pointeePos = pointee.getSpos();
                    if (pointeePos != Spos.NULL
                            && pointeePos % 8 == 0  // NOTE this condition added with "vpos" approach ("vpos" branch)
                            && pointeePos < ed.startupPos
                            && AccessData.getAccessTime(node.getPointerAccessData(i)) 
                                    <= ed.accessTimeLimit) {
                        
                        node.setPointer(i, null, pointeePos);
                        ed.evictCount += 1;
                    }
                }
            }
        }
    }
}
