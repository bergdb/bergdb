package bergdb.core;

import bergdb.stream.MemoryStream;

/** Review probe (s4, 028-67): a stream whose meta blocks say version 155, at several lengths. */
public class S4Version155Probe {
    public static void main(String[] args) throws Exception {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            for (int i = 0; i < 4; i++) {
                clock.setTime(10 + i);
                db.execute(db.trans().put("v" + i, new byte[90000]));
            }
        }
        long n = s.getLength();
        for (long len : new long[] {8, 100, 128, 200, 300, 600, 200100, n}) {
            MemoryStream m = s.copy();
            m.truncate(len);
            for (long b = 0; b + 8 <= len; b += 200000) {
                MemoryStream.TestAccess.write(m, new byte[] {(byte) 155, 0, 0, 0}, b + 4);
            }
            try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
                System.out.println(len + ": STARTED");
            } catch (RuntimeException e) {
                System.out.println(len + ": " + e.getClass().getSimpleName() + ", written "
                        + (m.getLength() - len) + ": " + e.getMessage().substring(0, 90));
            }
        }
    }
}
