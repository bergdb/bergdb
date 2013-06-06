package kissdb.dev;

import kissdb.core.Db;
import kissdb.core.KTestClock;
import kissdb.core.Trans;

/**
 * Executable class that prints examples of the DB tree.
 * 
 * @author Frans Lundberg
 */
public class PrintExamples {
    public void run() {
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        System.out.println("---- Empty DB ----");
        System.out.println("DB at initial state.\n");
        db.printGraph(System.out);
        System.out.println();
        
        
        clock.setTime(10);
        System.out.println("---- One KV ----");
        System.out.println("k1 = v1 added around t = 10\n");
        db.execute(Trans.builder().set("k1", "v1"));
        db.printGraph(System.out);
        System.out.println();
        
        
        clock = new KTestClock();
        db = Db.builder().testSetup().clock(clock).start();
        db.execute(Trans.builder().set("r/library/sublibrary/theFinalDirectory/LongKey", "v"));
        System.out.println("---- One long key ----");
        db.printGraph(System.out);
        System.out.println();
        
        
        clock = new KTestClock();
        db = Db.builder().testSetup().clock(clock).start();
        db.execute(Trans.builder().set("a-14-long-key-", "v14"));
        System.out.println("---- One 14-byte long key ----");
        db.printGraph(System.out);
        System.out.println();
        
        
        clock = new KTestClock();
        db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(Trans.builder().set("theprefix-key1", "v1"));
        clock.setTime(20);
        db.execute(Trans.builder().set("theprefix-key2", "v2"));
        System.out.println("---- Two keys, same prefix ----");
        System.out.println("Same prefix, two keys, two segements long. Added after t=10 and 20.\n");
        db.printGraph(System.out);
        System.out.println();
        
        
        clock = new KTestClock();
        db = Db.builder().testSetup().clock(clock).maxNodeSize8().start();
        for (int i = 0; i < 7; i++) {
            clock.setTime(1000 + i * 10);
            db.execute(Trans.builder().set("k" + i, "v" + i));
        }
        System.out.println("---- 7 short keys ----");
        System.out.println("Causes one split since maxNodeSize8(). 7 different times.\n");
        db.printGraph(System.out);
        System.out.println();
    }
    
    public static void main(String[] args) {
        new PrintExamples().run();
    }
}
