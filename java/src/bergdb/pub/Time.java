package bergdb.pub;

import java.time.Instant;
import java.time.ZoneOffset;
import java.time.format.DateTimeFormatter;
import java.util.Locale;
import java.util.TimeZone;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.BadFormatException;
import bergdb.pub.util.Clock;
import bergdb.pubimp.TimeResolver;

/**
 * A Time instance represents a time instance measured by the database
 * clock (see Clock).
 * The resolution of a Time instance is one "clock unit", that is 100 nanoseconds.
 * Internally, the time is stored as the number of 100 nanoseconds that
 * has passed since 00:00:00.0, 1 Jan 1970 UTC (Unix Epoch). 
 * Leap seconds are not counted; a day is always 24*60*60 seconds.
 * The minimum valid time value is 0 clock units (UTC 1970-01-01 00:00:00); 
 * the maximum valid time value is 2^56-1 clock units (UTC 2198-05-04 23:50:03.7927935).
 * A Time is immutable, and its methods may be called from any thread.
 * 
 * @see Clock
 * @author Frans Lundberg
 */
public class Time {
    // 2^56 - 1 = 72057594037927935
    
    private final long units;
    
    private static final long UNITS_PER_MILLISECOND = Clock.UNITS_PER_SEC / 1000;
    static final long MIN_IN_UNITS = 0;
    static final long MAX_IN_UNITS = 72057594037927935L;
    
    /**
     * The maximum possible Time value.
     * Corresponds to UTC 2198-05-04 23:50:03.7927935.
     */
    public static final Time MAX = new Time(MAX_IN_UNITS);
    
    /**
     * The UTC time zone.
     */
    public static final TimeZone UTC = TimeZone.getTimeZone("UTC");
    
    
    private Time(long units) {
        if (units < MIN_IN_UNITS || units > MAX_IN_UNITS) {
            throw new IllegalArgumentException("Time out of range, units: " + units + ".");
        }
        this.units = units;
    }
    
    /**
     * Creates and returns a Time instance based on the number of clock units 
     * that has passed since Unix Epoch.
     * 
     * @throws IllegalArgumentException If units is outside Time's range, 0 to 2^56 - 1.
     */
    public static Time units(long units) {
        return new Time(units);
    }
    
    /**
     * Creates and returns a Time instance based on the number of milliseconds
     * that has passed since Unix Epoch.
     * 
     * @throws IllegalArgumentException If the time is outside Time's range (bergdb 005-21).
     */
    public static Time millis(long millis) {
        // Checked (2026-10-21, bergdb 005-21): the product wrapped, so a large value could
        // give a time in 1970 instead of an exception.
        final long units;
        try {
            units = Math.multiplyExact(millis, UNITS_PER_MILLISECOND);
        } catch (ArithmeticException e) {
            throw new IllegalArgumentException("Time out of range, millis: " + millis + ".");
        }
        return new Time(units);
    }
    
    /**
     * Resolves an absolute time string using UTC time zone.
     * 
     * @throws BadFormatException If the time string is not an absolute time string by the
     *             format of resolve(TimeZone, Time, String), a field is outside its range, or
     *             the time is outside Time's range, before 1970 or after 2198-05-04
     *             23:50:03.7927935 UTC.
     * @throws IllegalArgumentException If timeString is null.
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
     * @throws BadFormatException If the time string is not an absolute time string, a field
     *             is outside its range, or the time is outside Time's range, as for utc().
     * @throws IllegalArgumentException If timeZone or timeString is null.
     * @see #resolve(TimeZone, Time, String)
     */
    public static Time resolve(TimeZone timeZone, String timeString) {
        // The given zone, not UTC, since 2026-11-05 (bergdb 015-57).
        long units = TimeResolver.resolveAbsolute(timeZone, timeString);
        return Time.units(units);
    }
    
    /**
     * <p>This method resolves a <i>time string</i> to an absolute time
     * given a time zone and the current time. The current time is needed
     * when a non-absolute time string is used.</p>
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
     * "2013-08 14:29"                  -- 1 Aug 2013 at 14:29:00.
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
     * absolute = date [(SPACE / "T") time-of-day]
     * date = year "-" month ["-" day]
     * time-of-day = hour ":" minute [":" second ["." 1*DIGIT]]
     * minus = "-" 1*DIGIT ["." 1*DIGIT] SPACE unit [SPACE time-of-day]
     * unit = "s" / "m" / "h" / "d"
     * year = 4DIGIT
     * month = 2DIGIT                   -- 01 to 12.
     * day = 2DIGIT                     -- 01 to the month's last day: 28, 29, 30 or 31.
     * hour = 2DIGIT                    -- 00 to 23.
     * minute = 2DIGIT                  -- 00 to 59.
     * second = 2DIGIT                  -- 00 to 59.
     * DIGIT = "0" to "9"               -- ASCII digits only.
     * SPACE = " "                      -- One space, U+0020.
     * </pre>
     * 
     * <p>The format of the time string loosely follows ISO 8601.
     * The Gregorian calendar is used (the ordinary Western calendar).
     * Leap seconds are never considered. One day is always 24*3600 seconds, 
     * one minute is 60 seconds and one hour is always 3600 seconds.</p>
     * 
     * <p>The parse is strict (bergdb 020-21, 1): a string is taken only as the format above
     * gives it, with each field in its range. A field is not rolled over: "2013-02-30",
     * "2013-13", "24:00" and "12:60" are refused, not taken as 2013-03-02, 2014-01, the next
     * day's 00:00 and 13:00. A fraction of a second, and a minus time's duration, its number
     * times its unit taken exactly, are rounded to Time's resolution, 100 ns, half up.</p>
     * 
     * <p>A local time that a change to or from summer time skips or repeats in the time
     * zone is not refused: it is taken as standard time, as java.util.GregorianCalendar takes
     * it (bergdb 020-24-01, U1-9). In Europe/Stockholm, "2026-03-29 02:30", which the clocks
     * skip, is 01:30 UTC, the time they show as 03:30; "2026-10-25 02:30", which they show
     * twice, is 01:30 UTC, the second time. A time of day, also after a minus time, is taken
     * so too.</p>
     * 
     * @throws BadFormatException If the time string does not follow the format above, or a
     *             field is outside its range; or if the time is outside Time's range, before
     *             1970 or after 2198-05-04 23:50:03.7927935 UTC, as an absolute time or a
     *             time of day, or a minus time that goes back before Unix Epoch.
     * @throws IllegalArgumentException If timeZone, now or timeString is null.
     */
    public static Time resolve(TimeZone timeZone, Time now, String timeString) {
        if (now == null) {
            throw new IllegalArgumentException("now == null not allowed");
        }
        long units = TimeResolver.resolve(timeZone, now.units(), timeString);
        return Time.units(units);
    }
    
    /**
     * Adds a Duration to this Time and returns a new Time with the result.
     * 
     * @throws IllegalArgumentException If the result is outside Time's range, or if duration
     *             is null (bergdb 020-25, C2).
     */
    public Time add(Duration duration) {
        if (duration == null) {
            // As every null argument of the API (bergdb 020-25, C2; 020-21, 3).
            throw new IllegalArgumentException("duration == null not allowed");
        }
        return new Time(this.units + duration.units());
    }
    
    /**
     * Returns true if this time, t, satisfies: {@code t0 <= t <= t1}.
     * 
     * @throws IllegalArgumentException If t0 or t1 is null (bergdb 020-25, C2).
     */
    public boolean isBetween(Time t0, Time t1) {
        if (t0 == null || t1 == null) {
            throw new IllegalArgumentException("t0 == null or t1 == null not allowed");
        }
        return this.units >= t0.units && this.units <= t1.units;
    }
    
    /**
     * Returns the number of clock units that has passed since Unix Epoch.
     */
    public long units() {
        return units;
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
    
    /**
     * Immutable and thread-safe; a static SimpleDateFormat, which is neither, gave threads
     * that formatted at once wrong strings and exceptions (bergdb 015-63).
     */
    private static final DateTimeFormatter UTC_DATE_FORMAT = 
            DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSS", Locale.US)
            .withZone(ZoneOffset.UTC);
    
    /**
     * Returns the time in UTC formatted like this: yyyy-MM-dd HH:mm:ss.SSSSSSS. 
     * For example: 2000-01-01 18:01:12.1234567.
     */
    public String toUtcString() {       
        long millis = units / Time.UNITS_PER_MILLISECOND;
        long unitsLeft = units % Time.UNITS_PER_MILLISECOND;
        String firstPart = UTC_DATE_FORMAT.format(Instant.ofEpochMilli(millis));
        String secondPart = String.format(Locale.US, "%04d", unitsLeft);
        return firstPart + secondPart;
    }
    
    
    // ======== Tests ========
    
    /**
     * bergdb 021-01: utc() and both resolve() throw BadFormatException for a bad time string,
     * and IllegalArgumentException for a null one, a null zone or a null current time.
     */
    @Nano
    private static void testResolveThrows() {
        final Time now = Time.utc("2000-01-01 12:00");
        final Runnable[] bad = {
                () -> Time.utc("20a0-01-01"),
                () -> Time.utc("yesterday"),
                () -> Time.resolve(UTC, "2000-01-0"),
                () -> Time.resolve(UTC, now, "-2 x"),
                () -> Time.resolve(UTC, now, ""),
        };
        for (int i = 0; i < bad.length; i++) {
            try {
                bad[i].run();
                throw new AssertionError("no BadFormatException, case " + i);
            } catch (BadFormatException e) {
                // Expected.
            }
        }
        final Runnable[] nulls = {
                () -> Time.utc(null),
                () -> Time.resolve(UTC, null),
                () -> Time.resolve(null, "2000-01-01"),
                () -> Time.resolve(UTC, now, null),
                () -> Time.resolve(null, now, "now"),
                () -> Time.resolve(UTC, null, "now"),
        };
        for (int i = 0; i < nulls.length; i++) {
            try {
                nulls[i].run();
                throw new AssertionError("no IllegalArgumentException, case " + i);
            } catch (IllegalArgumentException e) {
                // Expected.
            }
        }
    }
    
    /**
     * bergdb 020-21, 1 (020-13, section 4.2; 020-19, Q1): a time string is parsed strictly. A
     * field outside its range is refused with BadFormatException, as is a string that breaks
     * the format in another way, or whose time is outside Time's range; before, the calendar
     * rolled such a field over ("2013-13-01" was 2014-01-01, "25:00" the next day), the
     * seconds and a minus time's number were read as Java doubles ("1e1", "-1d s", "-NaN s"),
     * and a time outside the range threw IllegalArgumentException.
     */
    @Nano
    private static void testStrictTimeStrings() {
        final Time now = Time.utc("2020-06-15 12:00");
        final String[] bad = {
                // A field outside its range.
                "2013-00", "2013-13", "2013-00-10", "2013-13-01", "2013-01-00", "2013-01-32",
                "2013-02-29", "2100-02-29", "2013-02-30", "2013-04-31",
                "2013-01-01 24:00", "2013-01-01 25:00", "2013-01-01 12:60",
                "2013-01-01 23:59:60", "2013-01-01 00:00:75", "2013-01-01T24:00:00",
                "24:00", "25:00", "12:60", "00:00:60", "-1 d 25:00", "-1 d 23:60",
                // Not ASCII digits, or not the format.
                "2013-+1-01", "+013-01-01", "2013-1-01", "2013-01-1 ", "2013-01-01 1:00",
                "2013-01-01 00:00:1e1", "2013-01-01 00:00:0x1p3", "2013-01-01 00:00:05.",
                "2013-01-01 00:00:00 ", "2013-01-01 00:00:.5", "2013-01-01 00:00:00.5e3",
                "2013-01-01 00:00:+5", "2013-01-01 00:00:5", "2013-01-01 00:00:00.-5",
                "٢٠١٣-01-01", "2013-01-01t00:00", "now ", " now",
                "-1d s", "-NaN s", "-Infinity s", "-0x1p3 s", "-1e3 s", "-.5 s", "-1. s",
                "-+1 s", "--1 s", "-1 s ", "-1  s", "-1 x", "-1 s x", "-1 s 1:00",
                "-1 s  12:00", "-1 s 12:00 ",
                // A time outside Time's range.
                "1969-12-31", "1969-12-31 23:59:59.9999999", "2198-05-05", "2199-01-01",
                "0000-01-01", "9999-12-31", "-30000 d", "-99999999999999999999 d",
        };
        for (String s : bad) {
            for (int call = 0; call < 3; call++) {
                Time t;
                try {
                    t = call == 0 ? Time.resolve(UTC, now, s)
                            : call == 1 ? Time.utc(s) : Time.resolve(UTC, s);
                } catch (BadFormatException e) {
                    continue;
                }
                throw new AssertionError("'" + s + "' not refused by call " + call + ": " + t);
            }
        }
        try {
            Time.resolve(TimeZone.getTimeZone("Europe/Stockholm"), "1970-01-01 00:59");
            throw new AssertionError("1969-12-31 23:59 UTC not refused");
        } catch (BadFormatException e) {
            // Expected.
        }
        
        // Accepted, the edges included.
        final long day = 86400 * Clock.UNITS_PER_SEC;
        Assert.assertEquals(0, Time.utc("1970-01-01").units());
        Assert.assertEquals(Time.MAX, Time.utc("2198-05-04 23:50:03.7927935"));
        Assert.assertEquals(Time.utc("2012-03-01").units() - day, Time.utc("2012-02-29").units());
        Assert.assertEquals(Time.utc("2000-03-01").units() - day, Time.utc("2000-02-29").units());
        Assert.assertEquals(Time.utc("2014-01-01").units() - Clock.UNITS_PER_SEC,
                Time.utc("2013-12-31 23:59:59").units());
        Assert.assertEquals(Time.utc("2013-12-31 23:59:59").units() + 9999999,
                Time.utc("2013-12-31T23:59:59.9999999").units());
        Assert.assertEquals(Time.utc("2013-06-01").units() + 1,
                Time.utc("2013-06-01 00:00:00.00000005").units());
        Assert.assertEquals(Time.utc("2013-06-01"), Time.utc("2013-06-01 00:00:00.00000004"));
        Assert.assertEquals(Time.utc("2013-06-02"), Time.utc("2013-06-01 23:59:59.99999999"));
        Assert.assertEquals(Time.utc("2013-06-01 00:00"), Time.utc("2013-06"));
        Assert.assertEquals(now, Time.resolve(UTC, now, "now"));
        Assert.assertEquals(now, Time.resolve(UTC, now, "-0 s"));
        Assert.assertEquals(Time.utc("2020-06-15 11:59:58.5"), Time.resolve(UTC, now, "-1.5 s"));
        Assert.assertEquals(Time.utc("2020-06-15 11:30"), Time.resolve(UTC, now, "-30 m"));
        Assert.assertEquals(Time.utc("2020-06-13 14:29"), Time.resolve(UTC, now, "-2 d 14:29"));
        Assert.assertEquals(Time.utc("2020-06-15 00:00"), Time.resolve(UTC, now, "00:00"));
        Assert.assertEquals(Time.utc("2020-06-15 23:59:59.5"),
                Time.resolve(UTC, now, "23:59:59.5"));
    }
    
    /**
     * bergdb 020-23, Y1 (Codex's review of 020-21): a minus time's duration is its decimal
     * number times its unit, exactly, rounded to clock units half up, as a fraction of a
     * second is. The number went through a double and the product was truncated: "-0.0000021
     * s" was 20 units, not 21, "-900719925.4740993 s" one unit off, and Time.MAX minus
     * MAX's own seconds was refused as negative (-1) instead of giving 1970-01-01.
     */
    @Nano
    private static void testMinusTimeExact() {
        final Time now = Time.utc("2020-06-15 12:00");
        final String[] strings = {"-0.00000004 s", "-0.00000005 s", "-0.00000015 s",
                "-0.00000029 s", "-0.0000021 s", "-1.00000005 s", "-900719925.4740993 s",
                "-0.5 m", "-0.00000001 m", "-1.5 h", "-0.00000001 d", "-0 s", "-0.0 d"};
        final long[] units = {0, 1, 2, 3, 21, 10000001, 9007199254740993L,
                300000000, 6, 54000000000L, 8640, 0, 0};
        for (int i = 0; i < strings.length; i++) {
            Assert.assertEquals(strings[i], units[i],
                    now.units() - Time.resolve(UTC, now, strings[i]).units());
        }
        Assert.assertEquals(Time.units(0), Time.resolve(UTC, Time.MAX, "-7205759403.7927935 s"));
        Assert.assertEquals(Time.units(0), Time.resolve(UTC, Time.MAX, "-7205759403.79279345 s"));
        Assert.assertEquals(Time.units(1), Time.resolve(UTC, Time.MAX, "-7205759403.7927934 s"));
        for (String s : new String[] {"-7205759403.7927936 s", "-7205759403.79279355 s",
                "-1" + "0".repeat(400) + " d"}) {
            try {
                Time t = Time.resolve(UTC, Time.MAX, s);
                throw new AssertionError("'" + s + "' not refused: " + t);
            } catch (BadFormatException e) {
                // Expected: before 1970.
            }
        }
    }
    
    /**
     * bergdb 020-23, Y2 (Codex's review of 020-21): the grammar's "date = year "-" month
     * ["-" day]" takes a time of day after a year and a month too, on the month's first day;
     * the parse wanted a day before a time of day.
     */
    @Nano
    private static void testMonthWithTimeOfDay() {
        final Time now = Time.utc("2020-06-15 12:00");
        Assert.assertEquals(Time.utc("2020-06-01 12:34"), Time.utc("2020-06 12:34"));
        Assert.assertEquals(Time.utc("2020-06-01 12:34:56.1234567"),
                Time.utc("2020-06T12:34:56.1234567"));
        Assert.assertEquals(Time.utc("2020-06-01 12:34:56"),
                Time.resolve(UTC, "2020-06 12:34:56"));
        Assert.assertEquals(Time.utc("2020-06-01 12:34"), Time.resolve(UTC, now, "2020-06T12:34"));
        Assert.assertEquals(Time.utc("2020-06-01 10:34"),
                Time.resolve(TimeZone.getTimeZone("Europe/Stockholm"), "2020-06 12:34"));
        for (String s : new String[] {"2020-06 ", "2020-06T", "2020-06 1:00", "2020-06x12:34",
                "2020-06  12:34", "2020-06 24:00", "2020-06 12:34 ", "2020-13 12:00",
                "1969-12 23:59"}) {
            try {
                Time t = Time.resolve(UTC, now, s);
                throw new AssertionError("'" + s + "' not refused: " + t);
            } catch (BadFormatException e) {
                // Expected.
            }
        }
    }
    
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
    
    /**
     * Regression test for bergdb 015-63 (016-06's R8-F8): toUtcString() used one static
     * SimpleDateFormat, which is not thread-safe, so threads that formatted at once got
     * another thread's string or an exception.
     */
    @Nano
    private static void testToUtcStringFromThreads() throws InterruptedException {
        final int n = 8;
        final java.util.concurrent.atomic.AtomicInteger wrong = 
                new java.util.concurrent.atomic.AtomicInteger();
        final java.util.concurrent.atomic.AtomicReference<String> example = 
                new java.util.concurrent.atomic.AtomicReference<String>();
        Thread[] threads = new Thread[n];
        for (int k = 0; k < n; k++) {
            final int year = 2000 + k * 7;
            threads[k] = new Thread(() -> {
                String s = year + "-0" + (1 + year % 9) + "-1" + (year % 10) 
                        + " 1" + (year % 10) + ":2" + (year % 10) + ":3" + (year % 10) + ".1234567";
                Time t = Time.utc(s);
                for (int i = 0; i < 20000; i++) {
                    String got;
                    try {
                        got = t.toString();
                    } catch (RuntimeException e) {
                        got = e.toString();
                    }
                    if (!got.equals(s)) {
                        wrong.incrementAndGet();
                        example.compareAndSet(null, "expected " + s + ", got " + got);
                    }
                }
            });
        }
        for (Thread t : threads) {
            t.start();
        }
        for (Thread t : threads) {
            t.join();
        }
        Assert.assertEquals("wrong strings, e.g. " + example.get(), 0, wrong.get());
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
    
    /**
     * Regression test for bergdb 015-57 (016-06's R8-F2): resolve(TimeZone, String) resolved
     * in UTC, whatever time zone was given.
     */
    @Nano
    private static void testResolveUsesTheTimeZone() {
        TimeZone stockholm = TimeZone.getTimeZone("Europe/Stockholm");
        Assert.assertEquals(Time.utc("2013-08-19 12:29"),          // Summer time, UTC+2.
                Time.resolve(stockholm, "2013-08-19 14:29"));
        Assert.assertEquals(Time.utc("2013-01-19 13:29"),          // Winter, UTC+1.
                Time.resolve(stockholm, "2013-01-19 14:29"));
    }

    
}
