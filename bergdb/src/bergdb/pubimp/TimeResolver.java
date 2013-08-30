package bergdb.pubimp;

import java.util.Calendar;
import java.util.GregorianCalendar;
import java.util.Locale;
import java.util.TimeZone;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;
import bergdb.pub.Clock;

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
    private static final TimeZone UTC = TimeZone.getTimeZone("UTC");
    private static final long MILLIS_TO_UNITS = Clock.UNITS_PER_SEC / 1000;
    private final TimeZone timeZone;
    
    /**
     * Creates a TimeResolver with UTC time zone.
     */
    public TimeResolver() {
        this(UTC);
    }
    
    /**
     * Creates a TimeResult with the given time zone.
     */
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
     * @throws BadFormatException
     */
    public long getTime(long currentTime, String timeString) throws BadFormatException {
        if (timeString == null) {
            throw new IllegalArgumentException("timeString == null is not allowed");
        }
        
        int length = timeString.length();
        
        if (length == 0) {
            throw new BadFormatException("empty string is not allowed for a timeString");
        }
        
        if (length < 3) {
            throw new BadFormatException("Time string is too short, was: " + timeString + ".");
        }
        
        char first = timeString.charAt(0);
        
        switch (first) {
        case '-':
            return minus(currentTime, timeString);
        case 'y':
        case 'n':
            return special(currentTime, timeString);
        }
            
        if (length > 4 && timeString.charAt(4) == '-') {
            return absolute(timeString);
        } else {
            return relative(currentTime, timeString);
        }
    }
        
    private long absolute(String timeString) {
        long length = timeString.length();
        int year = 0;
        int month = 0;
        int date = 0;
        int h = 0;
        int min = 0;
        int s = 0;
        int millis = 0;
        long change = 0;    // smaller then millis
        
        
        if (length < 7) {
            throw new BadFormatException("Bad time string, too short, was: '" + timeString + "'.");
        }
        
        try {
            year = Integer.parseInt(timeString.substring(0, 4));
        } catch (NumberFormatException e) {
            throw new BadFormatException("Bad time string, was: '" + timeString + "'.");
        }
        
        if (timeString.charAt(4) != '-') {
            throw new BadFormatException("Bad time string, expected '-' as 5th char, was: '" + timeString + "'.");
        }
        
        month = parseZeroPadded(timeString.substring(5, 7), timeString);
        if (month < 0) {
            throw new BadFormatException("Bad absolute time string, bad month, was: '" + timeString + "'.");
        }
        
        if (length > 7) {
            if (length < 10) {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            if (timeString.charAt(7) != '-') {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            date = parseZeroPadded(timeString.substring(8, 10), timeString);
            // Let's allowed "overflow" for now, like: 2013-02-50".
        }
        
        if (length > 10) {
            if (length < 16) {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            char c = timeString.charAt(10);
            if (c != ' ' && c != 'T') {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            h = parseZeroPadded(timeString.substring(11, 13), timeString);
            if (timeString.charAt(13) != ':') {
                throw new BadFormatException("Bad absolute time string, expected ':' at 13, was: '" + timeString + "'.");
            }
            
            min = parseZeroPadded(timeString.substring(14, 16), timeString);
        }
        
        if (length > 16) {
            if (length < 19) {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            if (timeString.charAt(16) != ':') {
                throw new BadFormatException("Bad absolute time string, expected ':' at 16, was: '" + timeString + "'.");
            }
            
            double seconds = parseZeroPaddedDouble(timeString.substring(17), timeString);
            double floor = Math.floor(seconds);
            s = (int) floor;
            double fraction = seconds - floor;
            if (fraction > 1.0) {
                throw new AssertionError("fraction: " + fraction + ", seconds = " + seconds);
            }
            
            fraction = 1000.0 * fraction;
            double milliFloor = Math.floor(fraction);
            double milliFraction = fraction - milliFloor;
            if (milliFraction > 1.0) {
                throw new AssertionError("milliFraction: " + milliFraction + ", seconds = " + seconds);
            }
            
            millis = (int) milliFloor;
            change = (long) (milliFraction * MILLIS_TO_UNITS);
        }
        
        GregorianCalendar c = new GregorianCalendar(timeZone, Locale.US);
        c.setTimeInMillis(0);
        c.set(Calendar.YEAR, year);
        c.set(Calendar.MONTH, month - 1);     // 0 = January
        c.set(Calendar.DATE, date);
        c.set(Calendar.HOUR_OF_DAY, h);
        c.set(Calendar.MINUTE, min);
        c.set(Calendar.SECOND, s);
        c.set(Calendar.MILLISECOND, millis);
        
        long result = c.getTimeInMillis() * MILLIS_TO_UNITS + change;
        return result;
    }
    
    private long relative(long currentTime, String timeString) {
        // TODO A. implement.
        throw new RuntimeException("NOT implemented!");
    }
    
    private long minus(long currentTime, String timeString) {
        // TODO A. Implement
        throw new RuntimeException("NOT implemented!");
    }
    
    private long special(long currentTime, String timeString) {
        if (timeString.equals("now")) {
            return currentTime;
        } else if (timeString.equals("yesterday")) {
            return getTime(currentTime, "-1 day 00:00");
        } else {
            throw new BadFormatException("Bad time string, got: '" + timeString + "'.");
        }
    }
    
    /**
     * Parse a possibly zero-padded integer. Max one zero as padding assumed.
     */
    private int parseZeroPadded(String s, String timeString) {
        if (s.startsWith("0")) {
            s = s.substring(1);
        }
        
        int result = -1;
        try {
            result = Integer.parseInt(s);
        } catch (NumberFormatException e) {
            throw new BadFormatException("Bad time string: '" + timeString + "'.");
        }
        
        return result;
    }
    
    /**
     * Parse a possibly zero-padded integer. Max one zero as padding assumed.
     */
    private double parseZeroPaddedDouble(String s, String timeString) {
        if (s.startsWith("0")) {
            s = s.substring(1);
        }
        
        double result = -1;
        try {
            result = Double.parseDouble(s);
        } catch (NumberFormatException e) {
            throw new BadFormatException("Bad time string: '" + timeString + "'.");
        }
        
        return result;
    }
    
    
    @T
    public static void testAbsolute0() {
        String[] ok = new String[]{
                "2013-01-02 12:02:12.1234567", 
                "2013-01-02", 
                "2013-12-12 12:00", 
                "1999-02-10 12:00:01"};
        
        String[] bad = new String[]{
                "", 
                "2013-x1", 
                "2013-03-10 12:33-30", 
                "2013-03-10 12",
                "2013-03-10 12:30:",
                "2013-03-10 "};
        
        TimeResolver r = new TimeResolver();
        long currentTime = 1000*1000*1000 * MILLIS_TO_UNITS;  // not needed for absolute times
        
        for (String s : ok) {
            r.getTime(currentTime, s);
        }
        
        Exception ex = null;
        for (String s : bad) {
            ex = null;
            try {
                r.getTime(currentTime, s);
            } catch (BadFormatException e) {
                ex = e;
            }
            
            if (ex == null) {
                throw new AssertionError("Exception expected for string: " + s);
            }
        }
    }
    
    @T
    public static void testAbsolute1() {
        long millis = Util.getMillisSinceEpoch(UTC, 2013, 3, 14, 16, 10, 20, 500);        
        String ts = "2013-03-14 16:10:20.500";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, new TimeResolver().getTime(0, ts));
    }
    
    @T
    public static void testAbsolute2() {
        long millis = Util.getMillisSinceEpoch(UTC, 2000, 1, 1, 0, 0, 0, 0);   
        TimeResolver t = new TimeResolver();
        
        String ts = "2000-01-01 00:00:00.000";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t.getTime(0, ts));
        
        ts = "2000-01-01 00:00:00";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t.getTime(0, ts));
        
        ts = "2000-01-01 00:00";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t.getTime(0, ts));
    }
    
    @T
    public static void testAbsolute3() {
        // Resolves units - 10,000 time units in one millisecond.
        
        long millis = Util.getMillisSinceEpoch(UTC, 2000, 1, 1, 0, 0, 0, 0);    
        TimeResolver t = new TimeResolver();
        String ts = "2000-01-01 00:00:00.0000123";
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t.getTime(0, ts));
        
        ts = "2000-01-01 00:00:00.0000123456";
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t.getTime(0, ts));
        
        ts = "2000-01-01 00:00:00.00001239";
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t.getTime(0, ts));
    }
    
    @T
    public static void testSpecial0() {
        TimeResolver r = new TimeResolver();
        long current = 1 * 1000*1000*1000 * MILLIS_TO_UNITS + 123;
        long result = r.getTime(current, "now");
        Assert.assertEquals(current, result);
    }
    
    // @T   TODO enable
    public static void tSpecial1() {
        TimeResolver r = new TimeResolver();
        long current = 1 * 1000*1000*1000 * MILLIS_TO_UNITS + 123;
        long r1 = r.getTime(current, "yesterday");
        long r2 = r.getTime(current, "-1 day 00:00");
        Assert.assertEquals(r2, r1);
    }
    
    public static void main(String[] args) {
        testAbsolute0();
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
    
special = "yesterday" / "now"

*/