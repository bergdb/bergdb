package bergdb.core;

/**
 * R6's probe for DbStarter.canonicalNode's Javadoc (bergdb 016-06/R6): "a delete of a key
 * that does not exist makes the nodes on its path dirty, but it is not stored". After 200
 * puts with a startup distance of 2,000 (so index nodes are written and clean), a
 * transaction that deletes a key that does not exist: its got-dirty nodes and its record.
 */
public class R6NonexistentDeleteProbe {
    public static void main(String[] args) throws Exception {
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup().clock(clock).maxNodeSize8()
                .startupDistance(2000).start()) {
            for (int i = 0; i < 200; i++) {
                clock.setTime(10 + i);
                db.execute(db.trans().put("/k/" + (1000 + i), "v" + i));
            }
            clock.setTime(1000);
            long before = db.getStreamLength();
            Trans t = db.trans().delete("/k/1050x").build();
            db.execute(t);
            TransSeq.TransInfo last = db.internal().transSeq().last();
            System.out.println("delete of a key that does not exist: record of " 
                    + (db.getStreamLength() - before) + " bytes, got-dirty nodes in its TransInfo: "
                    + (last != null && last.tpos == t.tpos ? last.gotDirtyNodes.size() : -1));
        }
    }
}
