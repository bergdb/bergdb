package bergdb.test;

import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;

/**
 * Test to reproduce Bug141109.
 * Two top nodes with same topNodeId added in same transaction.
 * -ea was required to fail test.
 * Bug was fixed by changing Db.writePrimordialTransaction() so it does not leak
 * node instance reference created in the method. The method should just write to
 * the db stream.
 * 
 * @author Frans Lundberg
 */
public class Bug141109 {

    @Nano
    private static void t1() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(2);
        
        Db db = Db.builder().mainStream(stream).clock(clock).start();
        db.setStartupDistance(10*1000);
        int valueSize = 1000;
        
        for (int i = 0; i < 20; i++) {
            long time = 100 + i * 10;
            clock.setTime(time);
            //System.out.println("time: " + time);
            
            Trans trans = db.trans().put("k", new byte[valueSize]).build();
            db.execute(trans);
        }
        db.stop();
    }
}
