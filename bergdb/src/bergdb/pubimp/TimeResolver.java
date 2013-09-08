package bergdb.pubimp;

import java.util.Calendar;
import java.util.GregorianCalendar;
import java.util.Locale;
import java.util.TimeZone;

import bergdb.common.Util;
import bergdb.core.SystemClock;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;
import bergdb.pub.Clock;

/**
 * <p>An instance of this class can resolve a <i>time string</i> to a time value
 * in database units (100 ns units since epoch).
 * The format of the time string loosely follows ISO 8601.
 * This class is not thread-safe. The gregorian calendar is used (the most common one).
 * Leap seconds are never considered. One day is always 24*3600 s, one minute is 60 s and one
 * hour is always 3600 s.</p>
 * 
 * <pre>
 * The following examples with comments define the time format.
 * 
 * ABSOLUTE-TIME
 * 
 * "2013-08-19 14:29:10.1234567"    -- 19 Aug 2013 at 14:29:10.1234567.
 * "2013-08-19 14:29"               -- 19 Aug 2013 at 14:29:00. 
 * "2013-08-19"                     -- 19 Aug 2013 at 00:00:00.
 * "2013-08"                        -- 1 Aug 2013 at 00:00:00.
 * "2013-01"                        -- 1 Jan 2013 at 00:00:00.
 * 
 * TIME-OF-DAY
 * 
 * "14:29:10.1234567"               -- Today at 14:29:10.1234567.
 * "14:29"                          -- Today at 14:29.
 * 
 * MINUS-TIME
 * 
 * "Minus-time" is a negative offset to the current time in one of the following units: s, m, h, 
 * d (second, minute, hour, day).
 * 
 * "-1.5 s"                         -- 1.5 seconds ago.
 * "-30 m"                          -- 30 minutes ago.
 * "-2 h"                           -- 2 hours ago. 
 * "-3 d"                           -- 3 days ago (1 day = 24.0 hours).
 * 
 * MINUS-TIME PLUS TIME-OF-DAY
 * 
 * A minus-time expression can be followed by a RELATIVE TIME. In this case, the resulting time
 * is the same as if the negative time duration was first subtracted from the current time, 
 * and then the resulting time was used together with the RELATIVE TIME to resolve the time.
 * 
 * "-2 d 14:29"                     -- The day before yesterday at 14:29:00.
 * 
 * SPECIAL
 * 
 * "now"                            -- The current time.
 * 
 * MORE FORMAL
 * The syntax for a time-string can be more formally be described by this ABNF:
 * 
 * time-string = absolute / time-of-day / minus / "now" 
 * absolute = absolute-date [SPACE time-of-day]
 * absolute-date = "YYYY-MM-DD" / "YYYY-MM"
 * time-of-day = "HH:MM:SS.d" / "HH:MM"
 * minus = "-" number SPACE unit [SPACE time]
 * unit = "s" / "m" / "h" / "d"
 * </pre>
 * 
 * @author Frans Lundberg
 */
public class TimeResolver {
    // Let's try to implement the whole thing as a function. 
    // resolve(currentTime, timeZone, timeString)... Would be thread-safe.
    //
    
    private static final TimeZone UTC = TimeZone.getTimeZone("UTC");
    private static final long MILLIS_TO_UNITS = Clock.UNITS_PER_SEC / 1000;
    private final TimeData td;
    private final GregorianCalendar calendar;
    
    /**
     * Parse data, keeps parse state.
     */
    private static class TimeData {
        int year;
        int month;
        int date;
        int hour;
        int minute;
        double second;
    }
    
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
        this.td = new TimeData();
        this.calendar = new GregorianCalendar(timeZone, Locale.US);
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
    public long resolve(long currentTime, String timeString) throws BadFormatException {
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
        
        if (length == 3 && timeString.equals("now")) {
            return currentTime;
        }
        
        char first = timeString.charAt(0);
        if (first == '-') {
            return minus(currentTime, timeString);
        }
        
        if (length > 4 && timeString.charAt(4) == '-') {
            return absolute(timeString);
        } else {
            if (first >= '0' && first <= '9') {
                return timeOfDay(currentTime, timeString);
            } else {
                throw new BadFormatException("Bad time string, was: '" + timeString + "'.");
            }
        }
    }
    
    private long absolute(String timeString) {
        long length = timeString.length();
        
        if (length < 7) {
            throw new BadFormatException("Bad time string, too short, was: '" + timeString + "'.");
        }
        
        try {
            td.year = Integer.parseInt(timeString.substring(0, 4));
        } catch (NumberFormatException e) {
            throw new BadFormatException("Bad time string, was: '" + timeString + "'.");
        }
        
        if (timeString.charAt(4) != '-') {
            throw new BadFormatException("Bad time string, expected '-' as 5th char, was: '" + timeString + "'.");
        }
        
        td.month = parseZeroPadded(timeString.substring(5, 7), timeString);
        if (td.month < 0) {
            throw new BadFormatException("Bad absolute time string, bad month, was: '" + timeString + "'.");
        }
        
        if (length > 7) {
            if (length < 10) {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            if (timeString.charAt(7) != '-') {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            td.date = parseZeroPadded(timeString.substring(8, 10), timeString);
            // Let's allowed "overflow" for now, like: 2013-02-50".
        } else {
            td.date = 1;
        }
        
        if (length > 10) {
            if (length < 16) {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            char c = timeString.charAt(10);
            if (c != ' ' && c != 'T') {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            parseTime(timeString, 11);
            
        } else {
            td.hour = 0;
            td.minute = 0;
            td.second = 0.0;
        }
        
        return computeTimeUnits();
    }
    
    /**
     * Converts from TimeData to GregorianCalendar to time units.
     */
    private long computeTimeUnits() {
        calendar.setTimeInMillis(0);
        calendar.set(Calendar.YEAR, td.year);
        calendar.set(Calendar.MONTH, td.month - 1);
        calendar.set(Calendar.DATE, td.date);
        calendar.set(Calendar.HOUR_OF_DAY, td.hour);
        calendar.set(Calendar.MINUTE, td.minute);
        
        double floor = Math.floor(td.second);
        int second = (int) floor;
        double fraction = td.second - floor;
        if (fraction > 1.0) {
            throw new AssertionError("fraction: " + fraction + ", td.second = " + td.second);
        }
        
        fraction = 1000.0 * fraction;
        double milliFloor = Math.floor(fraction);
        double milliFraction = fraction - milliFloor;
        if (milliFraction > 1.0) {
            throw new AssertionError("milliFraction: " + milliFraction + ", td.second = " + td.second);
        }
        
        int millis = (int) milliFloor;
        long change = (long) (milliFraction * MILLIS_TO_UNITS);
        
        calendar.set(Calendar.SECOND, second);
        calendar.set(Calendar.MILLISECOND, millis);
        
        long result = calendar.getTimeInMillis() * MILLIS_TO_UNITS + change;
        return result;
    }
    
    /**
     * Converts from TimeData to GregorianCalendar to time units.
     * currentTime is used to compute "today".
     */
    private long computeTimeUnitsB(long currentTime) {
        calendar.setTimeInMillis(currentTime / TimeResolver.MILLIS_TO_UNITS);
        calendar.set(Calendar.HOUR_OF_DAY, td.hour);
        calendar.set(Calendar.MINUTE, td.minute);
        
        double floor = Math.floor(td.second);
        int second = (int) floor;
        double fraction = td.second - floor;
        if (fraction > 1.0) {
            throw new AssertionError("fraction: " + fraction + ", td.second = " + td.second);
        }
        
        fraction = 1000.0 * fraction;
        double milliFloor = Math.floor(fraction);
        double milliFraction = fraction - milliFloor;
        if (milliFraction > 1.0) {
            throw new AssertionError("milliFraction: " + milliFraction + ", td.second = " + td.second);
        }
        
        int millis = (int) milliFloor;
        long change = (long) (milliFraction * MILLIS_TO_UNITS);
        
        calendar.set(Calendar.SECOND, second);
        calendar.set(Calendar.MILLISECOND, millis);
        
        long result = calendar.getTimeInMillis() * MILLIS_TO_UNITS + change;
        return result;
    }
    
    private long timeOfDay(long currentTime, String timeString) {
        parseTime(timeString, 0);
        return computeTimeUnitsB(currentTime);
    }
    
    /**
     * Parses a time string of the format HH:MM[:SS.sss], writes result to this.td.
     * Sets td.hour, td.minute, td.second or throws BadFormatException.
     */
    private void parseTime(String timeString, int offset) throws BadFormatException {
        int length = timeString.length() - offset;
        
        if (length < 5) {
            throw new BadFormatException("Bad time string, was: '" + timeString + "'.");
        }
        
        td.hour = parseZeroPadded(timeString.substring(offset + 0, offset + 2), timeString);
        offset += 2;
        
        if (timeString.charAt(offset) != ':') {
            throw new BadFormatException("Bad time string, expected ':', was: '" + timeString + "'.");
        }
        offset += 1;
        
        td.minute = parseZeroPadded(timeString.substring(offset, offset + 2), timeString);
        offset += 2;
        
        // If there are seconds
        if (length > 5) {
            if (length < 8) {
                throw new BadFormatException("Bad time string, was: '" + timeString + "'.");
            }
            
            if (timeString.charAt(offset) != ':') {
                throw new BadFormatException("Bad time string, expected ':', was: '" + timeString + "'.");
            }
            offset += 1;
            
            td.second = parseZeroPaddedDouble(timeString.substring(offset), timeString);
        } else {
            td.second = 0.0;
        }
    }
    
    private long minus(long currentTime, String timeString) {
        String[] parts = timeString.split(" ");
        if (parts.length < 2) {
            throw new BadFormatException("Bad minus time string: '" + timeString + "'.");
        }
        
        double number = 0.0;
        try {
            number = Double.parseDouble(parts[0]);
        } catch (NumberFormatException e) {
            throw new BadFormatException("Bad minus time string: '" + timeString + "'.");
        }
        
        if (number > 0.0) {
            throw new BadFormatException("Bad minus time string: '" + timeString + "'.");
        }
        
        String unit = parts[1];
        if (unit.length() != 1) {
            throw new BadFormatException("Bad minus time string, unexpected unit, was: '" + timeString + "'.");
        }
        
        char unitChar = unit.charAt(0);
        double factor;
        
        switch (unitChar) {
        case 's':
            factor = Clock.UNITS_PER_SEC;
            break;
        case 'm':
            factor = Clock.UNITS_PER_SEC * 60.0;
            break;
        case 'h':
            factor = Clock.UNITS_PER_SEC * 3600.0;
            break;
        case 'd':
            factor = Clock.UNITS_PER_SEC * 3600.0 * 24.0;
            break;
        default:
            throw new BadFormatException("Bad minus time string, bad unit, was: '" + timeString + "'.");
        }
        
        double deltaTime = number * factor;
        long time = currentTime + ((long) deltaTime);
        if (time < 0) {
            throw new BadFormatException("Time out of range (negative: " + time 
                    + "), time string was: '" + timeString + "'.");
        }
        
        // If time of day comes after minus expression.
        if (parts.length > 2) {
            parseTime(timeString, parts[0].length() + 1 + parts[1].length() + 1);
            time = computeTimeUnitsB(time);
        }
        
        return time;
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
            r.resolve(currentTime, s);
        }
        
        Exception ex = null;
        for (String s : bad) {
            ex = null;
            try {
                r.resolve(currentTime, s);
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
        Assert.assertEquals(millis * MILLIS_TO_UNITS, new TimeResolver().resolve(0, ts));
    }
    
    @T
    public static void testAbsolute2() {
        long millis = Util.getMillisSinceEpoch(UTC, 2000, 1, 1, 0, 0, 0, 0);   
        TimeResolver t = new TimeResolver();
        
        String ts = "2000-01-01 00:00:00.000";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t.resolve(0, ts));
        
        ts = "2000-01-01 00:00:00";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t.resolve(0, ts));
        
        ts = "2000-01-01 00:00";
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t.resolve(0, ts));
    }
    
    @T
    public static void testAbsolute3() {
        // Resolves units - 10,000 time units in one millisecond.
        
        long millis = Util.getMillisSinceEpoch(UTC, 2000, 1, 1, 0, 0, 0, 0);    
        TimeResolver t = new TimeResolver();
        String ts = "2000-01-01 00:00:00.0000123";
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t.resolve(0, ts));
        
        ts = "2000-01-01 00:00:00.0000123456";
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t.resolve(0, ts));
        
        ts = "2000-01-01 00:00:00.00001239";
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t.resolve(0, ts));
    }
    
    @T
    public static void testSpecial0() {
        TimeResolver r = new TimeResolver();
        long current = 1 * 1000*1000*1000 * MILLIS_TO_UNITS + 123;
        long result = r.resolve(current, "now");
        Assert.assertEquals(current, result);
    }
    
    @T
    public static void tSpecial1() {
        TimeResolver r = new TimeResolver();
        long current = new SystemClock().getTime();
        long result = r.resolve(current, "now");
        Assert.assertEquals(current, result);
    }
    
    @T
    public static void testTimeOfDay0() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2010-03-14 13:20:10.0010023");
        long t2 = r.resolve(t1, "09:20:40.5000123");
        
        long millis = Util.getMillisSinceEpoch(UTC, 2010, 3, 14, 9, 20, 40, 500);
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t2);
    }
    
    @T
    public static void testTimeOfDay1() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2010-03-14 03:01");
        long t2 = r.resolve(t1, "09:20:40.5000123");
        
        long millis = Util.getMillisSinceEpoch(UTC, 2010, 3, 14, 9, 20, 40, 500);
        Assert.assertEquals(millis * MILLIS_TO_UNITS + 123, t2);
    }
    
    @T
    public static void testTimeOfDay2() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2010-03-14 03:01");
        long t2 = r.resolve(t1, "09:20");
        
        long millis = Util.getMillisSinceEpoch(UTC, 2010, 3, 14, 9, 20, 0, 0);
        Assert.assertEquals(millis * MILLIS_TO_UNITS, t2);
    }
    
    @T
    public static void testMinus0() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2010-03-14 03:01:10");
        long t2 = r.resolve(t1, "-10 s");
        Assert.assertEquals(10 * Clock.UNITS_PER_SEC, t1 - t2);
    }
    
    @T
    public static void testMinus1() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2010-03-14 03:01:10");
        long t2 = r.resolve(t1, "-10 m");
        Assert.assertEquals(Clock.UNITS_PER_SEC * 600, t1 - t2);
    }
    
    @T
    public static void testMinus2() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2010-03-14 03:01:10");
        long t2 = r.resolve(t1, "-1 d 13:00:01");
        long t3 = r.resolve(0, "2010-03-13 13:00:01");
        
        Assert.assertEquals(t3, t2);
    }
    
    @T
    public static void testMinus3() {
        TimeResolver r = new TimeResolver();
        long t1 = r.resolve(0, "2013-09-01 03:01:10");
        long t2 = r.resolve(t1, "-1 d 09:00");
        long t3 = r.resolve(0, "2013-08-31 09:00:00");
        
        Assert.assertEquals(t3, t2);
    }
    
    public static void main(String[] args) {
        testAbsolute0();
    }
}

