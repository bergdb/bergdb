package bergdb.core;

/**
 * The maintenance that a record carries (bergdb 031-06): the boundary between Db, which
 * appends one record an action, and reclaim, which decides what a record carries besides the
 * action's own writes. Every accepted action appends exactly one record: a commit
 * (Db.execute), a setter that commits, or a part of Db.maintain(budget). A commit's record and
 * a part's carry what plan() gives; a setter's and BergDB's own internal records carry
 * nothing. Nothing is written between two records, so a crash, a stop or a restart at a
 * record boundary comes between two actions.
 *
 * <p>Db calls plan() under the write lock, after the last check that may refuse the action
 * and before its go point; it only reads (the stream before the record, the record's time,
 * the action's KVs) and changes no memory of the implementation's. A refusal of the action
 * after it, by a stop, leaves nothing to undo. Db merges the plan's KVs with the action's,
 * appends the record, and then calls apply(), which brings the implementation's memory to
 * the state after the record, as a start reads it off the stream (Reclaim.initFromDb). All
 * policy, when an iteration begins, a step's size, when to cut, is inside plan().</p>
 *
 * <p>Reclaim implements it; NONE is the empty implementation, whose records carry nothing
 * (DbBuilder.maintenance; for tests).</p>
 */
interface Maintenance {

    /**
     * What the record of the action 't' carries, or null for nothing. 't' is a commit (a user
     * transaction that is not a setter's) or a part of maintain() (Trans.part); its time t.tt
     * is taken. 'kvs' are the action's KVs as they will be put, after its key and value
     * transformations, in key order: a copy at one of their keys is left out of the plan, as
     * the action's write leaves the key a value node of its own or none (031-06, rule 6).
     * Reads only. An exception from it fails the database (010-01, P7), but a
     * DbStoppingException, which refuses the action with nothing written.
     */
    Plan plan(Trans t, Kv[] kvs);

    /**
     * After the record of 't' has been appended, under the write lock: the implementation's
     * memory from 'plan' (null if the record carried nothing), as a start would read it off
     * the stream, and a pending physical cut made once the stream is durable past it.
     */
    void apply(Plan plan, Trans t);

    /**
     * The KVs a record carries besides its action's, and what Db needs to write them. Made
     * by plan(), read by Db, given back to apply().
     */
    abstract class Plan {
        /** The stream's length before the record, its position (031-06: L0). */
        long l0;

        /**
         * The KVs, in key order, one a key, none at a key of the action's: reclaim's copies,
         * the row and the table. A value transformation of one (Kv.planned) runs in
         * Db.putKvs after the touch.
         */
        Kv[] kvs;

        /** The keys of the copies, sorted, or null: stored with the copy mark. */
        long[][] copyKeys;

        /**
         * The keys whose paths the touch makes dirty before the batch (Trans.touch;
         * Db.touchPaths): the copies' and the row's, or null for no touch.
         */
        long[][] touchKeys;

        /** For the touch's statistics (Trans.touchCount), or null. */
        Reclaim.TouchCount touchCount;
        long touchOldBefore;

        /** Trans.maintainTakeTo for the record, or -1 (a part's M4). */
        long takeTo = -1;

        /** The bytes the plan's scan read, by deterministic counts (a part's cost). */
        long readBytes;
    }

    /** The empty maintenance: no record carries any (bergdb 031-06). */
    Maintenance NONE = new Maintenance() {
        public Plan plan(Trans t, Kv[] kvs) {
            return null;
        }

        public void apply(Plan plan, Trans t) {
        }
    };
}
