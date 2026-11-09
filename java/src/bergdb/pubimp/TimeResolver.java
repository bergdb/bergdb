package bergdb.pubimp;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.time.YearMonth;
import java.util.Calendar;
import java.util.GregorianCalendar;
import java.util.Locale;
import java.util.TimeZone;

import bergdb.common.Util;
import bergdb.core.SystemClock;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Time;
import bergdb.pub.util.BadFormatException;
import bergdb.pub.util.Clock;

/**
 * <p>The methods resolve() and resolveAbsolute() resolve a <i>time string</i> to a time value
 * in clock units (100 ns units since epoch), by the format and the rules of
 * bergdb.pub.Time.resolve(TimeZone, Time, String), whose Javadoc defines them. The Gregorian
 * calendar is used (the ordinary Western calendar). Leap seconds are never considered. One
 * day is always 24*3600 seconds, one minute is 60 seconds and one hour is always 3600
 * seconds.</p>
 * 
 * <p>The parse is strict (bergdb 020-21, 1; Frans, 2026-11-09): each field is ASCII digits
 * of its length, and in its range, the day within its month; a minus time's number is
 * digits with an optional fraction; nothing else is taken, and a time outside Time's range
 * is refused too, each with BadFormatException. Until 2026-11-09 a lenient calendar rolled a
 * field over ("2013-13-01" was 2014-01-01, "25:00" the next day), the seconds and a minus
 * time's number were Java doubles ("00:00:1e1", "-1d s", "-NaN s"), and a time outside the
 * range was an IllegalArgumentException (bergdb 020-13, section 4.2; 020-19, Q1).</p>
 * 
 * @author Frans Lundberg
 */
public class TimeResolver {
    //
    // Let's try to implement the whole thing as a function. 
    // resolve(currentTime, timeZone, timeString)... Would be thread-safe.
    //
    
    /** UTC time zone. */
    static final TimeZone UTC = TimeZone.getTimeZone("UTC");
    private static final long UNITS_PER_MILLISECOND = Clock.UNITS_PER_SEC / 1000;
    private static final long MAX_UNITS = Time.MAX.units();
    private final TimeData td;
    private final GregorianCalendar calendar;
    
    /**
     * Stores parse state.
     */
    private static class TimeData {
        int year;
        int month;
        int date;
        int hour;
        int minute;
        int second;
        long fraction;          // The fraction of the second in clock units, 0 to 10^7
    }
    
    /**
     * Creates a TimeResolver with the given time zone.
     */
    private TimeResolver(TimeZone timeZone) {
        if (timeZone == null) {
            throw new IllegalArgumentException("timeZone == null not allowed");
        }
        this.td = new TimeData();
        this.calendar = new GregorianCalendar(timeZone, Locale.US);
    }
    
    /**
     * This method resolves a time string (like "-1 d", "2013-08-30" or "now") to a time
     * value in database time units (100 ns units since epoch). Internal, not API (bergdb
     * 020-10, section 7): for bergdb.pub.Time.resolve.
     * 
     * @param currentTime  In database units.
     * @param timeString  The time string to resolve.
     * @return The resolved time in database time units, within Time's range.
     * @throws BadFormatException  If the time string does not follow the format, or its
     *      time is outside Time's range.
     */
    public static long resolve(TimeZone timeZone, long currentTime, String timeString) throws BadFormatException {
        return new TimeResolver(timeZone).reallyResolve(currentTime, timeString);
    }
    
    /**
     * Resolves a time string the must be absolute; no current time is needed. Internal, not
     * API (bergdb 020-10, section 7): for bergdb.pub.Time.utc.
     */
    public static long resolveAbsolute(TimeZone timeZone, String timeString) {
        if (timeString == null) {
            // bergdb 021-01: as resolve() refuses it, not a NullPointerException.
            throw new IllegalArgumentException("timeString == null is not allowed");
        }
        return new TimeResolver(timeZone).reallyResolveAbsolute(timeString);
    }
    
    private long reallyResolve(long currentTime, String timeString) throws BadFormatException {
        if (timeString == null) {
            throw new IllegalArgumentException("timeString == null is not allowed");
        }
        
        int length = timeString.length();
        
        if (length == 0) {
            throw new BadFormatException("Empty string is not allowed for a timeString.");
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
            return reallyResolveAbsolute(timeString);
        } else {
            return timeOfDay(currentTime, timeString);
        }
    }
    
    /** YYYY-MM, YYYY-MM-DD, or YYYY-MM-DD and a time of day after ' ' or 'T'. */
    private long reallyResolveAbsolute(String timeString) {
        int length = timeString.length();
        
        if (length < 7) {
            throw new BadFormatException("Bad time string, too short, was: '" + timeString + "'.");
        }
        
        if (timeString.charAt(4) != '-') {
            throw new BadFormatException("Bad time string, expected '-' as 5th char, was: '" + timeString + "'.");
        }
        
        td.year = digits(timeString, 0, 4, 0, 9999, "year");
        td.month = digits(timeString, 5, 2, 1, 12, "month");
        
        if (length > 7) {
            if (length < 10) {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            if (timeString.charAt(7) != '-') {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            int days = YearMonth.of(td.year, td.month).lengthOfMonth();
            td.date = digits(timeString, 8, 2, 1, days, "day");
        } else {
            td.date = 1;
        }
        
        if (length > 10) {
            char c = timeString.charAt(10);
            if (c != ' ' && c != 'T') {
                throw new BadFormatException("Bad absolute time string, was: '" + timeString + "'.");
            }
            
            parseTime(timeString, 11);
            
        } else {
            td.hour = 0;
            td.minute = 0;
            td.second = 0;
            td.fraction = 0;
        }
        
        calendar.setTimeInMillis(0);
        calendar.set(Calendar.YEAR, td.year);
        calendar.set(Calendar.MONTH, td.month - 1);
        calendar.set(Calendar.DATE, td.date);
        return inRange(computeTimeUnits(), timeString);
    }
    
    /**
     * The time of the calendar's date with td's time of day, in the calendar's time zone.
     */
    private long computeTimeUnits() {
        calendar.set(Calendar.HOUR_OF_DAY, td.hour);
        calendar.set(Calendar.MINUTE, td.minute);
        calendar.set(Calendar.SECOND, td.second);
        calendar.set(Calendar.MILLISECOND, 0);
        return calendar.getTimeInMillis() * UNITS_PER_MILLISECOND + td.fraction;
    }
    
    /**
     * The time with td's time of day on the date of 'time' in the calendar's time zone.
     */
    private long computeTimeUnitsB(long time) {
        calendar.setTimeInMillis(time / TimeResolver.UNITS_PER_MILLISECOND);
        return computeTimeUnits();
    }
    
    private long timeOfDay(long currentTime, String timeString) {
        parseTime(timeString, 0);
        return inRange(computeTimeUnitsB(currentTime), timeString);
    }
    
    /**
     * Parses a time of day, HH:MM, HH:MM:SS or HH:MM:SS.d with one digit or more, from offset
     * to the end of the string, and writes it to td: hour 00 to 23, minute and second 00 to
     * 59, and the fraction rounded to clock units, half up, which may round up to a whole
     * second (10^7 units).
     * 
     * @throws BadFormatException  If the string does not follow the format, or a field is
     *      outside its range.
     */
    private void parseTime(String timeString, int offset) throws BadFormatException {
        int length = timeString.length() - offset;
        
        if (length != 5 && length != 8 && length < 10) {
            throw new BadFormatException("Bad time string, was: '" + timeString + "'.");
        }
        
        td.hour = digits(timeString, offset, 2, 0, 23, "hour");
        expect(timeString, offset + 2, ':');
        td.minute = digits(timeString, offset + 3, 2, 0, 59, "minute");
        td.second = 0;
        td.fraction = 0;
        
        if (length > 5) {
            expect(timeString, offset + 5, ':');
            td.second = digits(timeString, offset + 6, 2, 0, 59, "second");
            if (length > 8) {
                expect(timeString, offset + 8, '.');
                td.fraction = fraction(timeString, offset + 9);
            }
        }
    }
    
    /**
     * A minus time: '-', a number of digits with an optional fraction ('.' and digits), a
     * space and a unit; then, optionally, a space and a time of day.
     */
    private long minus(long currentTime, String timeString) {
        int end = 1;
        while (end < timeString.length() && isDigit(timeString.charAt(end))) {
            end++;
        }
        if (end == 1) {
            throw new BadFormatException("Bad minus time string, expected a digit after '-': '"
                    + timeString + "'.");
        }
        if (end < timeString.length() && timeString.charAt(end) == '.') {
            int start = ++end;
            while (end < timeString.length() && isDigit(timeString.charAt(end))) {
                end++;
            }
            if (end == start) {
                throw new BadFormatException("Bad minus time string, expected a digit after "
                        + "'.': '" + timeString + "'.");
            }
        }
        BigDecimal number = new BigDecimal(timeString.substring(1, end));    // Digits only
        
        if (timeString.length() < end + 2 || timeString.charAt(end) != ' ') {
            throw new BadFormatException("Bad minus time string, expected a space and a unit "
                    + "after the number: '" + timeString + "'.");
        }
        long factor = parseUnit(timeString.charAt(end + 1), timeString);
        
        // The duration exactly, rounded to clock units half up, as a fraction of a second is
        // (bergdb 020-23, Y1): through a double and a cast, "-0.0000021 s" was 20 units.
        BigDecimal delta = number.multiply(BigDecimal.valueOf(factor))
                .setScale(0, RoundingMode.HALF_UP);
        if (delta.compareTo(BigDecimal.valueOf(currentTime)) > 0) {
            throw new BadFormatException("Time out of range, before 1970, time string was: '"
                    + timeString + "'.");
        }
        long time = currentTime - delta.longValueExact();
        
        // If time of day comes after minus expression.
        if (timeString.length() > end + 2) {
            expect(timeString, end + 2, ' ');
            parseTime(timeString, end + 3);
            time = inRange(computeTimeUnitsB(time), timeString);
        }
        
        return time;
    }

    /** The clock units of the unit. */
    private long parseUnit(char unitChar, String timeString) {
        long factor;
        
        switch (unitChar) {
        case 's':
            factor = Clock.UNITS_PER_SEC;
            break;
        case 'm':
            factor = Clock.UNITS_PER_SEC * 60;
            break;
        case 'h':
            factor = Clock.UNITS_PER_SEC * 3600;
            break;
        case 'd':
            factor = Clock.UNITS_PER_SEC * 3600 * 24;
            break;
        default:
            throw new BadFormatException("Bad minus time string, bad unit, was: '" + timeString + "'.");
        }
        return factor;
    }
    
    /**
     * The number of 'count' ASCII digits at 'offset', which must be from 'min' to 'max'.
     * 
     * @throws BadFormatException  If a char is not an ASCII digit, the string ends before
     *      them, or the number is outside min to max.
     */
    private static int digits(String timeString, int offset, int count, int min, int max,
            String field) {
        if (timeString.length() < offset + count) {
            throw new BadFormatException("Bad time string, the " + field + " is cut: '"
                    + timeString + "'.");
        }
        int result = 0;
        for (int i = offset; i < offset + count; i++) {
            char c = timeString.charAt(i);
            if (!isDigit(c)) {
                throw new BadFormatException("Bad time string, the " + field + " is not "
                        + count + " digits: '" + timeString + "'.");
            }
            result = 10 * result + (c - '0');
        }
        if (result < min || result > max) {
            throw new BadFormatException("Bad time string, the " + field + " " 
                    + timeString.substring(offset, offset + count) + " is outside " + min 
                    + " to " + max + ": '" + timeString + "'.");
        }
        return result;
    }
    
    /**
     * The digits from 'offset' to the end, one at least, as a fraction of a second in clock
     * units, rounded half up: 0 to 10^7.
     */
    private static long fraction(String timeString, int offset) {
        int length = timeString.length();
        if (offset >= length) {
            throw new BadFormatException("Bad time string, expected a digit after '.': '"
                    + timeString + "'.");
        }
        long units = 0;
        for (int i = offset; i < length; i++) {
            char c = timeString.charAt(i);
            if (!isDigit(c)) {
                throw new BadFormatException("Bad time string, the fraction of the second is "
                        + "not digits: '" + timeString + "'.");
            }
            int k = i - offset;
            if (k < 7) {
                units = 10 * units + (c - '0');
            } else if (k == 7 && c >= '5') {
                units++;
            }
        }
        for (int k = length - offset; k < 7; k++) {
            units *= 10;
        }
        return units;
    }
    
    private static void expect(String timeString, int offset, char c) {
        if (offset >= timeString.length() || timeString.charAt(offset) != c) {
            throw new BadFormatException("Bad time string, expected '" + c + "' as char " 
                    + (offset + 1) + ": '" + timeString + "'.");
        }
    }
    
    private static boolean isDigit(char c) {
        return c >= '0' && c <= '9';
    }
    
    /** The time, if within Time's range, 0 to 2^56 - 1 units. */
    private static long inRange(long time, String timeString) {
        if (time < 0 || time > MAX_UNITS) {
            throw new BadFormatException("Time out of range, before 1970 or after "
                    + Time.MAX + " UTC: '" + timeString + "'.");
        }
        return time;
    }
   
    
    // ======== Tests ========
    
    @Nano
    private static void testAbsolute0() {
        String[] ok = new String[]{
                "2013-01-02 12:02:12.1234567",
                "2013-01-02T12:02:12.1234567",
                "2013-01-02", 
                "2013-12-12 12:00", 
                "1999-02-10 12:00:01"};
        
        String[] bad = new String[]{
                "", 
                "2013-01-02W12:02:12.1234567",
                "2013-x1", 
                "2013-03-10 12:33-30", 
                "2013-03-10 12",
                "2013-03-10 12:30:",
                "2013-03-10 "};
        
        long currentTime = 1000*1000*1000 * UNITS_PER_MILLISECOND;  // not needed for absolute times
        
        for (String s : ok) {
            TimeResolver.resolve(UTC, currentTime, s);
        }
        
        Exception ex = null;
        for (String s : bad) {
            ex = null;
            try {
                TimeResolver.resolve(UTC, currentTime, s);
            } catch (BadFormatException e) {
                ex = e;
            }
            
            if (ex == null) {
                throw new AssertionError("Exception expected for string: " + s);
            }
        }
    }
    
    @Nano
    private static void testAbsolute1() {
        long millis = Util.getMillisSinceEpoch(UTC, 2013, 3, 14, 16, 10, 20, 500);        
        String ts = "2013-03-14 16:10:20.500";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND, TimeResolver.resolve(UTC, 0, ts));
    }
    
    @Nano
    private static void testAbsolute2() {
        long millis = Util.getMillisSinceEpoch(UTC, 2000, 1, 1, 0, 0, 0, 0);   
        
        String ts = "2000-01-01 00:00:00.000";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND, TimeResolver.resolve(UTC, 0, ts));
        
        ts = "2000-01-01 00:00:00";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND, TimeResolver.resolveAbsolute(UTC, ts));
        
        ts = "2000-01-01 00:00";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND, TimeResolver.resolve(UTC, 0, ts));
    }
    
    @Nano
    private static void testAbsolute3() {
        // Resolves units - 10,000 time units in one millisecond.
        
        long millis = Util.getMillisSinceEpoch(UTC, 2000, 1, 1, 0, 0, 0, 0);    
        
        String ts = "2000-01-01 00:00:00.0000123";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND + 123, TimeResolver.resolve(UTC, 0, ts));
        
        ts = "2000-01-01 00:00:00.0000123456";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND + 123, TimeResolver.resolve(UTC, 0, ts));
        
        ts = "2000-01-01 00:00:00.00001239";
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND + 124, TimeResolver.resolve(UTC, 0, ts));
    }
    
    @Nano
    private static void testSpecial0() {
        long current = 1 * 1000*1000*1000 * UNITS_PER_MILLISECOND + 123;
        long result = TimeResolver.resolve(UTC, current, "now");
        Assert.assertEquals(current, result);
    }
    
    @Nano
    private static void tSpecial1() {
        long current = new SystemClock().getTime();
        long result = TimeResolver.resolve(UTC, current, "now");
        Assert.assertEquals(current, result);
    }
    
    @Nano
    private static void testTimeOfDay0() {
        long t1 = TimeResolver.resolve(UTC, 0, "2010-03-14 13:20:10.0010023");
        long t2 = TimeResolver.resolve(UTC, t1, "09:20:40.5000123");
        
        long millis = Util.getMillisSinceEpoch(UTC, 2010, 3, 14, 9, 20, 40, 500);
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND + 123, t2);
    }
    
    @Nano
    private static void testTimeOfDay1() {
        long t1 = TimeResolver.resolve(UTC, 0, "2010-03-14 03:01");
        long t2 = TimeResolver.resolve(UTC, t1, "09:20:40.5000123");
        
        long millis = Util.getMillisSinceEpoch(UTC, 2010, 3, 14, 9, 20, 40, 500);
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND + 123, t2);
    }
    
    @Nano
    private static void testTimeOfDay2() {
        long t1 = TimeResolver.resolve(UTC, 0, "2010-03-14 03:01");
        long t2 = TimeResolver.resolve(UTC, t1, "09:20");
        
        long millis = Util.getMillisSinceEpoch(UTC, 2010, 3, 14, 9, 20, 0, 0);
        Assert.assertEquals(millis * UNITS_PER_MILLISECOND, t2);
    }
    
    @Nano
    private static void testTimeOfDay3() {
        long t1 = TimeResolver.resolve(UTC, 0, "1975-03-14");
        long t2 = TimeResolver.resolve(UTC, t1, "09:20");
        long t3 = TimeResolver.resolve(UTC, t1, "09:20:00.00000019");
        Assert.assertEquals(2, t3 - t2);
    }
    
    @Nano
    private static void testMinus0() {
        long t1 = TimeResolver.resolve(UTC, 0, "2010-03-14 03:01:10");
        long t2 = TimeResolver.resolve(UTC, t1, "-10 s");
        Assert.assertEquals(10 * Clock.UNITS_PER_SEC, t1 - t2);
    }
    
    @Nano
    private static void testMinus1() {
        long t1 = TimeResolver.resolve(UTC, 0, "2010-03-14 03:01:10");
        long t2 = TimeResolver.resolve(UTC, t1, "-10 m");
        Assert.assertEquals(Clock.UNITS_PER_SEC * 600, t1 - t2);
    }
    
    @Nano
    private static void testMinus2() {
        long t1 = TimeResolver.resolve(UTC, 0, "2010-03-14 03:01:10");
        long t2 = TimeResolver.resolve(UTC, t1, "-1 d 13:00:01");
        long t3 = TimeResolver.resolve(UTC, 0, "2010-03-13 13:00:01");
        Assert.assertEquals(t3, t2);
    }
    
    @Nano
    private static void testMinus3() {
        long t1 = TimeResolver.resolve(UTC, 0, "2013-09-01 03:01:10");
        long t2 = TimeResolver.resolve(UTC, t1, "-1 d 09:00");
        long t3 = TimeResolver.resolve(UTC, 0, "2013-08-31 09:00:00");
        Assert.assertEquals(t3, t2);
    }

    /**
     * bergdb 005-21: seconds that do not fit an int, or are not numbers, are refused; since
     * 2026-11-09 (bergdb 020-21, 1) also seconds of 60 or more, which rolled over to the next
     * minute ("00:00:75" was "00:01:15").
     */
    @Nano
    private static void testBadSeconds() {
        String[] bad = {"2013-01-01 00:00:3000000000", "2013-01-01 00:00:1e300",
                "2013-01-01 00:00:NaN", "2013-01-01 00:00:Infinity", "2013-01-01 00:00:-5",
                "2013-01-01 00:00:75", "2013-01-01 00:00:60", "2013-01-01 00:00:99.5"};
        for (String s : bad) {
            try {
                resolveAbsolute(UTC, s);
                throw new AssertionError("no exception for " + s);
            } catch (BadFormatException e) {
                // Expected.
            }
        }
        Assert.assertEquals(resolveAbsolute(UTC, "2013-01-01 00:01:00") - Clock.UNITS_PER_SEC,
                resolveAbsolute(UTC, "2013-01-01 00:00:59"));
    }
    
    /** bergdb 005-21: Time.millis() refuses a value whose units overflow a long. */
    @Nano
    private static void testTimeMillisOverflow() {
        try {
            bergdb.pub.Time.millis(1844674407370956L);
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
        Assert.assertEquals(10000L, bergdb.pub.Time.millis(1).units());
    }
    
    @Nano
    private static void testOneUnit() {
        long units = resolveAbsolute(UTC, "1970-01-01 00:00:00.0000001");
        Assert.assertEquals(1L, units);
    }
}

