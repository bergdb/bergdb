package bergdb.pub;

import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Locale;
import java.util.TimeZone;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pubimp.TimeResolver;

/**
 * A Time instance represents a time instance measure by the database
 * clock (see Clock).
 * The resolution of a Time instance is one "clock unit", that is 100 nanoseconds.
 * Internally, the time is stored as the number of 100 nanoseconds that
 * has passed since 00:00:00.0, 1 Jan 1970 UMT (Unix Epoch). 
 * Leap seconds are not counted; a day is always 24*60*60 seconds.
 * The minimum valid time value is 0 clock units (UTC 1970-01-01 00:00:00); 
 * the maximum valid time value is 2^56-1 clock units (UTC 2198-05-04 23:50:04).
 * 
 * @see Clock
 * @author Frans Lundberg
 */
public class Time {
    // 2^56 - 1 = 72057594037927935
    
    private final long units;
    
    private static final long UNITS_PER_MILLISECOND = Clock.UNITS_PER_SEC / 1000;
    private static final long MIN_IN_UNITS = 0;
    private static final long MAX_IN_UNITS = 72057594037927935L;
    
    /**
     * The maximum possible Time value.
     * Corresponds to UTC 2198-05-04 23:50:04.
     */
    public static final Time MAX = new Time(MAX_IN_UNITS);
    
    /**
     * The UTC time zone.
     */
    public static final TimeZone UTC = TimeZone.getTimeZone("UTC");
    
    
    private Time(long units) {
        if (units < MIN_IN_UNITS || units > MAX_IN_UNITS) {
            throw new IllegalArgumentException("Time ouf of range, units: " + units + ".");
        }
        this.units = units;
    }
    
    /**
     * Creates and returns a Time instance based on the number of clock units 
     * that has passed since Unix Epoch.
     */
    public static Time units(long units) {
        return new Time(units);
    }
    
    /**
     * Creates and returns a Time instance based on the number of milliseconds
     * that has passed since Unix Epoch.
     */
    public static Time millis(long millis) {
        return new Time(millis * UNITS_PER_MILLISECOND);
    }
    
    /**
     * Resolves an absolut time string using UTC time zone.
     * 
     * @see #resolve(TimeZone, Time, String)
     */
    public static Time utc(String timeString) {
        return resolve(Time.UTC, timeString);
    }
    
    /**
     * Resolves the time string using the given time zone.
     * Since this method takes no current time, the time string must
     * be an absolute time (time string rule ABSOLUTE-TIME).
     * 
     * @see #resolve(TimeZone, Time, String)
     */
    public static Time resolve(TimeZone timeZone, String timeString) {
        long units = TimeResolver.resolveAbsolute(UTC, timeString);
        return Time.units(units);
    }
    
    /**
     * <p>This method resolves a <i>time string</i> to an absolute time
     * given a time zone and the current time. The current time is needed
     * when a non-absolut time string is used.</p>
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
     * A minus-time expression can be followed by a TIME-OF-DAY. In this case, the resulting time
     * is the same as if the negative time duration was first subtracted from the current time, 
     * and then the resulting time was used together with the TIME-OF-DAY to resolve the time.
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
     * <p>The format of the time string loosely follows ISO 8601.
     * This class is not thread-safe. The Gregorian calendar is used (the ordinary Western calendar).
     * Leap seconds are never considered. One day is always 24*3600 seconds, 
     * one minute is 60 seconds and one hour is always 3600 seconds.</p>
     */
    public static Time resolve(TimeZone timeZone, Time now, String timeString) {
        long units = TimeResolver.resolve(timeZone, now.units(), timeString);
        return Time.units(units);
    }
    
    /**
     * Adds a Duration to this Time and returns a new Time with the result.
     */
    public Time add(Duration duration) {
        return new Time(this.units + duration.units());
    }
    
    /**
     * Subtracts a Duraction from this Time and returns a new Time with the result.
     */
    public Time substract(Duration duration) {
        return new Time(this.units - duration.units());
    }
    
    /**
     * Returns true if this time, t, satisfies: t0 <= t <= t1.
     */
    public boolean isBetween(Time t0, Time t1) {
        return this.units >= t0.units && this.units <= t1.units;
    }
    
    /**
     * Returns the number of clock units that has passed since Unix Epoch.
     */
    public long units() {
        return units;
    }
    
    /**
     * Returns a Date given this Time instance. The returned Date object is 
     * created by rounding the time to the closest smaller millisecond value.
     * The returned Date has lower resolution than a Time instance.
     */
    public Date getDate() {
        return new Date(units / UNITS_PER_MILLISECOND);
    }

    @Override
    public int hashCode() {
        // Generated by Eclipse.
        final int prime = 31;
        int result = 1;
        result = prime * result + (int) (units ^ (units >>> 32));
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        // Generated by Eclipse.
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Time other = (Time) obj;
        if (units != other.units)
            return false;
        return true;
    }
    
    public String toString() {
        return toUtcString();
    }
    
    private static final SimpleDateFormat UTC_DATE_FORMAT;
    static { 
        UTC_DATE_FORMAT = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS", Locale.US);
        UTC_DATE_FORMAT.setTimeZone(TimeZone.getTimeZone("UTC"));
    }
    
    /**
     * Returns the time in UTC formatted like this: yyyy-MM-dd HH:mm:ss.SSSSSSS. 
     * For example: 2000-01-01 18:01:12.1234567.
     */
    public String toUtcString() {       
        long millis = units / Time.UNITS_PER_MILLISECOND;
        long unitsLeft = units % Time.UNITS_PER_MILLISECOND;
        String firstPart = UTC_DATE_FORMAT.format(new Date(millis));
        String secondPart = String.format(Locale.US, "%04d", unitsLeft);
        return firstPart + secondPart;
    }
    
    
    // ======== Tests ========
    
    @Nano
    private static void testIsBetween() {
        Time t1 = Time.utc("2000-01-01 00:00:01.0000000");
        Time t2 = Time.utc("2000-01-01 00:00:02.0000000");
        Time t3 = Time.utc("2000-01-01 00:00:00.0000000");
        Time t4 = Time.utc("2000-01-01 00:00:01.0000000");
        Time t5 = Time.utc("2000-01-01 00:00:01.3000000");
        Time t6 = Time.utc("2000-01-01 00:00:02.3000000");
        
        Assert.assertFalse(t3.isBetween(t1, t2));
        Assert.assertTrue(t4.isBetween(t1, t2));
        Assert.assertTrue(t5.isBetween(t1, t2));
        Assert.assertFalse(t6.isBetween(t1, t2));       
    }
    
    @Nano
    private static void testToUtcString() {
        Time time = Time.utc("2000-01-01 18:01:12.1234567");
        Assert.assertEquals(67, time.units() % 100);
        Assert.assertEquals("2000-01-01 18:01:12.1234567", time.toUtcString());
    }
    
    @Nano
    private static void testToUtcStringRoundUp() {
        Time time = Time.utc("2000-01-01 18:01:12.123456789");
        Assert.assertEquals("2000-01-01 18:01:12.1234568", time.toUtcString());
    }
    
    @Nano
    private static void testToUtcStringRoundDown() {
        Time time = Time.utc("2000-01-01 18:01:12.123456701");
        Assert.assertEquals("2000-01-01 18:01:12.1234567", time.toUtcString());
    }
    
    @Nano
    private static void testEquals1() {
        Time t0 = Time.MAX;
        Time t1 = Time.units(72057594037927936L - 1L);
        Assert.assertTrue(t0.equals(t1));
    }
    
    @Nano
    private static void testEquals2() {
        Time t0 = Time.units(1);
        Time t1 = Time.units(2);
        Assert.assertFalse(t0.equals(t1));
    }
    
    @Nano
    private static void testAdd() {
        Time t0 = Time.units(0);
        Time t1 = t0.add(Duration.seconds(1.0));
        Assert.assertEquals(Clock.UNITS_PER_SEC, t1.units - t0.units());
    }
    
    @Nano
    private static void testMillis() {
        Time t1 = Time.millis(1000);
        Time t2 = Time.units(Clock.UNITS_PER_SEC);
        Assert.assertTrue(t1.equals(t2));
    }
    
    @Nano
    private static void testResolve1() {
        Time t1 = Time.utc("2014-01-01 00:00:00.000000");
        Time t2 = Time.utc("2014-01-01 00:00:00.000001");
        Time t3 = t1.add(Duration.seconds(1e-6));
        Assert.assertEquals(t2, t3);
    }
    
    @Nano
    private static void testResolve2() {
        Time t1 = Time.utc("1970-01-01");
        Assert.assertEquals(0, t1.units());
    }
    
    @Nano
    private static void testResolve3() {
        Time t1 = Time.utc("2000-01");
        Time t2 = Time.utc("2000-01-01 00:00:00.000");
        Assert.assertEquals(t2, t1);
    }
    
    @Nano
    private static void testResolve4() {
        //  09 Sep 2001 01:46:40 UTC = 1000L*1000*1000 Unix time (s).
        
        TimeZone zone = TimeZone.getTimeZone("UTC");
        Time t1 = Time.millis(1000L * 1000L*1000*1000);
        Time t2 = Time.resolve(zone, "2001-09-09 01:46:40");
        Assert.assertEquals(t1, t2);
    }
    
    @Nano
    private static void testResolve5() {
        //  09 Sep 2001 01:46:40 UTC = 1000L*1000*1000 Unix time (s).
        
        TimeZone zone = TimeZone.getTimeZone("UTC");
        Time t1 = Time.resolve(zone, "2001-09-09 01:46:40");
        Time t2 = Time.resolve(zone, t1, "-1 d 14:00:00");
        Time t3 = Time.resolve(zone, "2001-09-08 14:00");
        Assert.assertEquals(t3, t2);
    }

    
}
