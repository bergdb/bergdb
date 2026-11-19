package frans;

import bergdb.core.Db;
import bergdb.core.TestClock;
import bergdb.core.TestNodeSize;
import bergdb.stream.MemoryStream;

/**
 * Printing some dag examples for documentation.
 */
@SuppressWarnings("unused")
public class DagExamples {
    // See also class dev.DagExamples.
    
    private void go(String[] args) {
        //primordial();
        //one();
        //twoTopNodes();
        //twoInOne();
        //twoInTwo();
        notATree();
    }
    
    private void primordial() {
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).clock(clock).mainStream(new MemoryStream()).start();
        db.printDag(System.out);
    }
    
    private void one() {
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).clock(clock).mainStream(new MemoryStream()).start();
        db.execute(db.trans().put("key", "value").build());
        db.printDag(System.out);
    }
    
    private void twoInOne() {
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).clock(clock).mainStream(new MemoryStream()).start();
        db.execute(db.trans().put("k1", "value1").put("k2", "value2").build());
        db.printDag(System.out);
    }
    
    private void twoInTwo() {
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).clock(clock).mainStream(new MemoryStream()).start();
        db.execute(db.trans().put("k1", "value1"));
        db.execute(db.trans().put("k2", "value2"));
        db.printDag(System.out);
    }
    
    private void twoTopNodes() {
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).clock(clock).mainStream(new MemoryStream()).start();
        for (int i = 0; i < 4; i++) {
            db.execute(db.trans().put("key", "value" + (i+2)).build());
        }
        db.printDag(System.out);
    }
    
    /**
     * Minimal dag that is not a tree.
     */
    private void notATree() {
        // Until record format 8 this caused one space split of type 2 (space-split-2).
        // PE now plans the batch and cuts a full leaf's live list into new nodes.
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).clock(clock).mainStream(new MemoryStream()).start();
        for (int i = 0; i < 5; i++) {
            String index = "" + (i + 2);
            db.execute(db.trans().put("prefix-k" + index, "value" + index).build());
        }
        db.printDag(System.out);
    }
    
    public static void main(String[] args) throws Exception {
        new DagExamples().go(args);
    }
}
