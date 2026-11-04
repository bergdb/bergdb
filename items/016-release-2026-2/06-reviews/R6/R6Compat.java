package bergdb.core;

import java.io.File;
import bergdb.common.StringUtil;
import bergdb.stream.FileStream;

/**
 * R6's check of MetaBlock's compatibility claim (bergdb 016-06/R6): "an older version
 * neither checks nor reads those bytes [the node size], and it copies a block it read
 * whole, so it starts such a stream as before and passes the field on". Run with a jar:
 * R6Compat DIR STEP; step "a" creates and puts /a, "b" puts /b, "c" reads both and puts /c.
 * Compiled once against 2026.1's API (no try-with-resources), run with either jar.
 */
public class R6Compat {
    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        dir.mkdirs();
        Db db = Db.builder().stream("main", new FileStream(dir), 100 * 1000, 10)
                .clock(new CoreTestClock()).noEvict().retainForever().testId()
                .startupDistance(1000).start();
        String step = args[1];
        System.out.println(step + ": /a=" + str(DbUtil.get(db, Long.MAX_VALUE, "/a"))
                + ", /b=" + str(DbUtil.get(db, Long.MAX_VALUE, "/b"))
                + ", length " + db.getStreamLength());
        for (int i = 0; i < 300; i++) {
            db.execute(db.trans().put("/" + step, step + i));
            db.execute(db.trans().put("/" + step + "/" + (i % 17), "x" + i));
        }
        db.stop();
        Thread.sleep(1000);
    }

    private static String str(byte[] v) {
        return v == null ? "null" : StringUtil.toString(v);
    }
}
