package bergdb.stream;

import java.util.Arrays;
import java.util.Random;

import bergdb.common.Salsa;

/**
 * Review 016-06/S1: every byte at stream position p is the plain byte XOR the Salsa20
 * keystream byte p of (key, nonce), whatever the appends' sizes, and after the stream is cut
 * at any byte and a new SalsaStream appends after the cut, as a start after a crash does.
 * The reference is one Salsa object run over the whole plain text. Also reads at random
 * positions and lengths, getLength, and a wrong key.
 */
public class SalsaCutProbe {
    public static void main(String[] args) throws Exception {
        Random r = new Random(args.length > 0 ? Long.parseLong(args[0]) : 1);
        int rounds = 0, bad = 0;
        for (int round = 0; round < 3000; round++) {
            byte[] nonce = new byte[8]; r.nextBytes(nonce);
            byte[] key = new byte[32]; r.nextBytes(key);
            MemoryStream m = new MemoryStream();
            int total = 1 + r.nextInt(5000);
            byte[] plain = new byte[total]; r.nextBytes(plain);
            int written = 0;
            SalsaStream s = new SalsaStream(m, nonce, key);
            while (written < total) {
                if (r.nextInt(4) == 0 && written > 0) {
                    // A crash: the tail after a random byte is lost; a start makes a new stream.
                    int cut = r.nextInt(written + 1);
                    m.truncate(cut);
                    written = cut;
                    s = new SalsaStream(m, nonce, key);
                }
                int n = Math.min(total - written, 1 + r.nextInt(300));
                s.append(plain, written, n);
                written += n;
                if (s.getLength() != written) { bad++; System.out.println("getLength " + s.getLength() + " != " + written); }
            }
            // The stored bytes against the reference keystream.
            byte[] stored = new byte[total];
            m.read(0, stored, 0, total);
            byte[] expected = new byte[total];
            new Salsa(nonce, key).append(plain, 0, expected, 0, total);
            if (!Arrays.equals(stored, expected)) { bad++; System.out.println("round " + round + ": stored bytes differ"); }
            // Reads at random positions through a new stream.
            SalsaStream s2 = new SalsaStream(m, nonce, key);
            for (int k = 0; k < 20; k++) {
                int pos = r.nextInt(total);
                int len = 1 + r.nextInt(total - pos);
                byte[] got = new byte[len];
                s2.read(pos, got, 0, len);
                if (!Arrays.equals(got, Arrays.copyOfRange(plain, pos, pos + len))) {
                    bad++; System.out.println("round " + round + ": read " + pos + "+" + len);
                }
            }
            // A wrong key reads other bytes.
            byte[] key2 = key.clone(); key2[r.nextInt(32)] ^= 1;
            byte[] got = new byte[Math.min(16, total)];
            new SalsaStream(m, nonce, key2).read(0, got, 0, got.length);
            if (got.length >= 8 && Arrays.equals(got, Arrays.copyOf(plain, got.length))) { bad++; System.out.println("wrong key reads plain"); }
            rounds++;
        }
        System.out.println("rounds " + rounds + ", faults " + bad);
    }
}
