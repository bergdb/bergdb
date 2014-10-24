package bergdb.core;

/**
 * State of the database (Db).
 * The only state transitions allowed are ZERO -> STARTING -> ACTIVE -> STOPPING.
 */
public enum DbState {
    ZERO,
    STARTING,
    ACTIVE,
    STOPPING;
}
