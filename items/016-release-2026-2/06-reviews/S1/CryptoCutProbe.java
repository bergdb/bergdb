package bergdb.pubimp;

import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.BadCryptoKey;
import bergdb.stream.MemoryStream;

/**
 * Review 016-06/S1: an encrypted database through the Pub API, its stream cut at every byte
 * of a range (a crash that loses the tail), started with a wrong key (BadCryptoKey, the
 * stream unchanged) and then with the right one (it starts; every transaction that ends at
 * or before the cut is there, none after it; a put after the start reads back). The range:
 * the last 300 bytes, and 200 bytes on each side of the meta block at 200,000.
 */
public class CryptoCutProbe {
    public static void main(String[] args) throws Exception {
        CryptoKey key = CryptoKey.generate();
        CryptoKey wrong = CryptoKey.generate();
        MemoryStream m = new MemoryStream();
        Database db = builder(m, key).start();
        Connection c = db.connection();
        int n = 0;
        long[] ends = new long[400];
        while (n < ends.length && m.getLength() < 260000) {
            c.put("/k" + n + ".txt", "v" + n + "-" + "x".repeat(n % 7 == 0 ? 3000 : 300));
            c.sync();
            ends[n] = m.getLength();
            n++;
        }
        db.close();
        long length = m.getLength();
        System.out.println("transactions " + n + ", stream " + length);
        int starts = 0, faults = 0;
        for (long cut = 199800; cut <= length; cut++) {
            if (cut > 200200 && cut < length - 300) cut = length - 300;
            MemoryStream s = m.copy();
            s.truncate(cut);
            byte[] before = bytes(s);
            try {
                builder(s, wrong).start().close();
                faults++; System.out.println(cut + ": a wrong key started");
            } catch (BadCryptoKey e) {
                // right
            } catch (RuntimeException e) {
                faults++; System.out.println(cut + ": wrong key: " + e);
            }
            if (!java.util.Arrays.equals(before, bytes(s))) {
                faults++; System.out.println(cut + ": the wrong key's start changed the stream");
            }
            s = s.copy();   // the failed start closed s; a closed MemoryStream refuses appends
            try {
                Database d = builder(s, key).start();
                Connection cc = d.connection();
                for (int i = 0; i < n; i++) {
                    String v = cc.get("/k" + i + ".txt", String.class);
                    boolean expected = ends[i] <= cut;
                    if ((v != null) != expected) {
                        faults++; System.out.println(cut + ": /k" + i + " " + (v != null) + ", expected " + expected);
                        break;
                    }
                }
                cc.put("/after.txt", "a");
                cc.sync();
                if (!"a".equals(cc.get("/after.txt", String.class))) { faults++; System.out.println(cut + ": put after"); }
                d.close();
                s = s.copy();
                Database d2 = builder(s, key).start();
                if (!"a".equals(d2.connection().get("/after.txt", String.class))) { faults++; System.out.println(cut + ": restart"); }
                d2.close();
            } catch (RuntimeException e) {
                faults++; System.out.println(cut + ": right key: " + e);
            }
            starts++;
        }
        System.out.println("cuts " + starts + ", faults " + faults);
    }

    static DatabaseBuilderImp builder(MemoryStream s, CryptoKey key) {
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        b.mainStream(s);
        b.cryptoKey(key);
        return b;
    }

    static byte[] bytes(MemoryStream s) throws Exception {
        byte[] b = new byte[(int) s.getLength()];
        s.read(0, b, 0, b.length);
        return b;
    }
}
