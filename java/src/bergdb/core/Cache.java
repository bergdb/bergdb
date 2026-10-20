package bergdb.core;

public interface Cache {

    /**
     * Source of dynamic information about the database state
     * needed by the cache implementation. Easy to mock.
     */
    public interface DbInfo {
        public PointerLocks getPointerLocks();
    }
    
}
