package bergdb.dev;

import bergdb.core.Db;
import bergdb.core.CoreTestClock;
import bergdb.core.TestNodeSize;

/**
 * Executable class that prints examples of the db graph.
 * 
 * @author Frans Lundberg
 */
public class PrintableDagExamples {
    public void run() {
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        System.out.println("---- Empty database ----");
        System.out.println("Db at initial state.\n");
        db.printDag(System.out);
        System.out.println();
        
        
        clock.setTime(10);
        System.out.println("---- One KV ----");
        System.out.println("k1 = v1 added around t = 10\n");
        db.execute(db.trans().put("k1", "v1").build());
        db.printDag(System.out);
        System.out.println();
        
        
        clock = new CoreTestClock();
        db = Db.builder().testSetup().clock(clock).start();
        db.execute(db.trans().put("r/library/sublibrary/theFinalDirectory/LongKey", "v").build());
        System.out.println("---- One long key ----");
        db.printDag(System.out);
        System.out.println();
        
        
        clock = new CoreTestClock();
        db = Db.builder().testSetup().clock(clock).start();
        db.execute(db.trans().put("a-14-long-key-", "v14").build());
        System.out.println("---- One 14-byte long key ----");
        db.printDag(System.out);
        System.out.println();
        
        
        clock = new CoreTestClock();
        db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("theprefix-key1", "v1").build());
        clock.setTime(20);
        db.execute(db.trans().put("theprefix-key2", "v2").build());
        System.out.println("---- Two keys, same prefix ----");
        System.out.println("Same prefix, two keys, two segements long. Added after t=10 and 20.\n");
        db.printDag(System.out);
        System.out.println();
        
        
        clock = new CoreTestClock();
        db = TestNodeSize.builder(8).testSetup().clock(clock).start();
        for (int i = 0; i < 7; i++) {
            clock.setTime(1000 + i * 10);
            db.execute(db.trans().put("k" + i, "v" + i).build());
        }
        System.out.println("---- 7 short keys ----");
        System.out.println("Causes one split since maxNodeSize8(). 7 different times.\n");
        db.printDag(System.out);
        System.out.println();
    }
    
    public static void main(String[] args) {
        new PrintableDagExamples().run();
    }
}
