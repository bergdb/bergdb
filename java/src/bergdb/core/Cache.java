package bergdb.core;

public interface Cache {

    /**
     * Source of dynamic information about the database state
     * needed by the cache implementation. Easy to mock. No methods since bergdb item 009,
     * step 3d: its one method gave the pointer locks (PointerLocks), which handles do not
     * use.
     */
    public interface DbInfo {
    }
    
}
