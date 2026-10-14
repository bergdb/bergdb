package bergdb.pubimp;

import bergdb.dag.Klong;

/**
 * Used to handle package dependencies: pub can access stuff in pubimp, 
 * not in bergdb.dag directly.
 */
public class ClockConstants {    
    private ClockConstants() {}
    public static final long MIN_TIME = Klong.MIN_TIME;
    public static final long MAX_TIME = Klong.MAX_TIME;
}
