package bergdb.core;

/**
 * State of the database (Db).
 * The only state transitions allowed are ZERO -> STARTING -> ACTIVE -> STOPPING,
 * and ACTIVE -> FAILED -> STOPPING.
 */
public enum DbState {
    ZERO,
    STARTING,
    ACTIVE,

    /**
     * A transaction threw after its go point (bergdb 005-01): the database refuses every
     * transaction and read until it is restarted. See Db.execute().
     */
    FAILED,

    STOPPING;
}
