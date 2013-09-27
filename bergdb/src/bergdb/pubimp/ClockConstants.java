package bergdb.pubimp;

import bergdb.coreds.Klong;

/**
 * We want pub to access stuff in pubimp, not in coreds directly.
 */
public class ClockConstants {
    public static final long MIN_TIME = Klong.MIN_TIME;
    public static final long MAX_TIME = Klong.MAX_TIME;
}
