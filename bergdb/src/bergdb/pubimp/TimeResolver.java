package bergdb.pubimp;

import java.util.TimeZone;

/**
 * <p>An instance of this class can resolve a <i>time string</i> to a time value
 * in database units (100 ns units since epoch).
 * The format of the time string loosely follows ISO 8601.</p>
 * 
 * <pre>
 * The following examples with comments should define the time format completely.
 * 
 * ABSOLUTE TIME
 * 
 * "2013-08-19 14:29:10.1234567"    -- 19 Aug 2013 at 14:29:10.1234567.
 * "2013-08-19 14:29"               -- 19 Aug 2013 at 14:29:00. 
 * "2013-08-19"                     -- 19 Aug 2013 at 00:00:00.
 * "2013-08"                        -- 1 Aug 2013 at 00:00:00.
 * "2013-01"                        -- 1 Jan 2013 at 00:00:00.
 * 
 * RELATIVE TIME
 * 
 * "08-19 14:29:10.1234567"         -- The last time, the time was 14:29:10.1234567 on 19th of August.
 * "08-19 14:29"                    -- The last time, the time was 14:29:00 on 18th of August.
 * "08-19"                          -- The last time, the time was 00:00:00 on 18th of August.
 * "xx-13 14:29:10.1234567"         -- The last time, the time was 14:29:10.1234567 on the 19th of 
 *                                     any month (the current month or the previous).   
 * "xx-13 14:29"                    -- The last time, the time was 14:29:00 the 19th of 
 *                                     any month (the current month or the previous).
 * "xx-13"                          -- The last time, the time was 00:00:00 on the 13th of any
 *                                     month (the current month or the previous one.
 * "14:29:10.1234567"               -- The last time, the time was 14:29:10.1234567.
 * "14:29"                          -- The last time, the time was 14:29.
 * 
 * "mon"                            -- The last time, the time was 00:00:00 on a Monday.
 * "mon 14:29:10.1234567"           -- The last time, the time was 14:29:10.1234567 on a Monday.
 * "mon 14:29"                      -- The last time, the time was 14:29:00 on a Monday.
 * 
 * MINUS-TIME
 * 
 * "Minus-time" is a negative offset to the current time in one of the following units: 
 * s, min, h, day, week.
 * 
 * "-1.5 s"                         -- 1.5 seconds ago.
 * "-30 min"                        -- 30 minutes ago.
 * "-2 h"                           -- 2 hours ago. 
 * "-3 day"                         -- 3 days ago (1 day = 24.0 hours).
 * "-1 week"                        -- 1 week (7 days) ago.
 * 
 * MINUS-TIME PREFIX
 * 
 * A minus-time expression can be followed by a RELATIVE TIME. In this case, the resulting time
 * is the same as if the negative time duration was first subtracted from the current time, 
 * and then the resulting time was used together with the RELATIVE TIME to resolve the time.
 * 
 * "-1 week monday 14:29"           -- The last time, except for within the last 24x7 hours, that
 *                                     the time was 14:29.
 * 
 * SPECIAL
 * 
 * "yesterday"                      -- Same as "-1 day 00:00".
 * "now"                            -- The current time.
 * </pre>
 * 
 * @author Frans Lundberg
 */
public class TimeResolver {
    private final TimeZone timeZone;
    
    public TimeResolver(TimeZone timeZone) {
        if (timeZone == null) {
            throw new IllegalArgumentException("timeZone == null not allowed");
        }
        this.timeZone = timeZone;
    }
    
    /**
     * This method resolves a time string (like "yesterday", "2013-08-30" or "now") to a time
     * value in database time units (100 ns units since epoch).
     * 
     * @param currentTime
     * @param timeString
     * @return The resolved time in database time units.
     * @throws IllegalArgumentException
     */
    public long getTime(long currentTime, String timeString) throws IllegalArgumentException {
        return -1;
    }
}

/*

Time string format
==================

Formal syntax definition.

time-string = absolute / relative / minus / special 

absolute = absolute-date [" " time]

    absolute-date = "YYYY-MM-DD" / "YYYY-MM"

    time = "HH:MM:SS.d" / "HH:MM"

relative = relative-day [time] / [relative-day] time

    relative-day = "MM-DD" / "xx-DD" / "mon" / "tue" / "wed" / "thu" / "fri" / "sat" / "sun"
    
minus = "-" number " " unit [" " relative]

    unit = "s" / "min" / "h" / "day" / "week" / "year"

*/