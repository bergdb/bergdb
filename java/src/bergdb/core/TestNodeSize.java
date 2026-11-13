package bergdb.core;

/**
 * For BergDB's own tests only (bergdb 026-08): Db.builder() with the maximum node size 8, 14,
 * 30 or 62, for the tests outside bergdb.core (the Pub layer's tests, the stress programs
 * outside the package, src-dev). Every database a user makes has the node size 30, and
 * DbBuilder has no public method to set another; the tests in bergdb.core call DbBuilder's
 * package-private maxNodeSize8() to maxNodeSize62(). Not part of the Core API (Db, "The Core
 * API"). A database made at a size other than 30 carries no promise that a later release
 * reads it.
 */
public final class TestNodeSize {
    private TestNodeSize() {
    }

    /**
     * Db.builder() with the maximum node size 'size'.
     *
     * @throws IllegalArgumentException  If size is not 8, 14, 30 or 62.
     */
    public static DbBuilder builder(int size) {
        DbBuilder b = Db.builder();
        switch (size) {
        case 8:
            return b.maxNodeSize8();
        case 14:
            return b.maxNodeSize14();
        case 30:
            return b.maxNodeSize30();
        case 62:
            return b.maxNodeSize62();
        default:
            throw new IllegalArgumentException("Node size " + size + ": 8, 14, 30 or 62.");
        }
    }
}
