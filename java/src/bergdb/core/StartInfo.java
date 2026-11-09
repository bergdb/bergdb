package bergdb.core;

/**
 * Info about the database startup.
 * Use by Core, not directly exposed to Pub API.
 * 
 * @author Frans Lundberg
 */
public class StartInfo {
    /** The startup position, from which the start read the startup section's transactions. */
    public long startPos;
    
    /** The startup distance in force, in bytes (Db.getStartupDistance()). */
    public int startupDistance;
    
    /** Transaction time of the first transaction of the startup transactions. */
    public long startTime;
    
    /** Number of startup transactions. */
    public int transCount;
    
    /** Last pos of last transaction of the startup transactions. */
    public long lastPos;
}
