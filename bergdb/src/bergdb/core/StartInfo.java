package bergdb.core;

/**
 * Info about the database startup.
 * Use by Core, not directly exposed to Pub API.
 * 
 * @author Frans Lundberg
 */
public class StartInfo {
    public long startPos;
    public int startupDistance;
    
    /** Transaction time of the first transaction of the startup transactions. */
    public long startTime;
    
    /** Number of startup transactions. */
    public int transCount;
    
    /** Last pos of last transaction of the startup transactions. */
    public long lastPos;
}
