package bergdb.cross;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.ByteBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import bergdb.dag.Keys;

/**
 * A cross workload, parsed (bergdb 012-05, section 3, which defines the format,
 * "bergdb-workload 1"). Run.java executes it on Java's Db, C's bergdb-run on C's; both read
 * the same text. This class only parses and decodes; it has no Db.
 */
public final class Workload {
    /** One line of the workload: its words, the line number, and its segment. */
    public static final class Line {
        public final int number;        // 1-based line number in the file
        public final String[] words;
        public final int segment;       // segments are separated by restart lines
        public final int trans;         // for a t line: its index among the t lines, else -1

        Line(int number, String[] words, int segment, int trans) {
            this.number = number;
            this.words = words;
            this.segment = segment;
            this.trans = trans;
        }

        public String cmd() {
            return words[0];
        }

        public BadWorkload error(String message) {
            return new BadWorkload("workload line " + number + ": " + message);
        }
    }

    /** A workload that breaks the format's rules. */
    public static final class BadWorkload extends IllegalArgumentException {
        private static final long serialVersionUID = 1L;

        public BadWorkload(String message) {
            super(message);
        }
    }

    // The settings ("set" lines): maxnode, sd and budget applied at every start; retain and
    // fraction once, after the creation's start, as the stream keeps them (bergdb 015-87;
    // 022-01, D3). -1 or null: not set.
    public int maxNode = 30;
    public int startupDistance = -1;
    public long retain = -1;            // Long.MAX_VALUE for forever
    public String fraction = null;      // as written; parsed with Double.parseDouble
    public long budget = -1;

    public final List<Line> lines = new ArrayList<Line>();
    public int segments = 1;
    public int transCount = 0;

    public static Workload read(File file) throws IOException {
        BufferedReader r = new BufferedReader(new InputStreamReader(new FileInputStream(file),
                StandardCharsets.UTF_8), 1 << 16);
        try {
            return parse(r);
        } catch (NumberFormatException e) {
            throw new BadWorkload(e.getMessage());
        } finally {
            r.close();
        }
    }

    static Workload parse(BufferedReader r) throws IOException {
        Workload w = new Workload();
        boolean header = false;
        boolean settingsDone = false;
        int number = 0;
        int segment = 0;
        for (String text; (text = r.readLine()) != null; ) {
            number++;
            String[] words = words(text);
            if (words.length == 0) {
                continue;
            }
            if (!header) {
                if (!(words.length == 2 && words[0].equals("bergdb-workload")
                        && words[1].equals("1"))) {
                    throw new BadWorkload("workload line " + number
                            + ": expected \"bergdb-workload 1\"");
                }
                header = true;
                continue;
            }
            String cmd = words[0];
            int trans = -1;
            if (cmd.equals("set")) {
                if (settingsDone) {
                    throw new BadWorkload("workload line " + number
                            + ": a set line after the first operation");
                }
                w.setting(number, words);
                continue;
            }
            if (!cmd.equals("clock")) {
                settingsDone = true;
            }
            Line line;
            switch (cmd) {
            case "t":
                trans = w.transCount++;
                checkTrans(number, words);
                break;
            case "clock":
                need(number, words, 2);
                time(number, words[1]);
                break;
            case "now":
            case "sync":
                need(number, words, 1);
                break;
            case "restart":
                need(number, words, 1);
                line = new Line(number, words, segment, -1);
                w.lines.add(line);
                segment++;
                w.segments++;
                continue;
            case "setsd":
                need(number, words, 2);
                Integer.parseInt(words[1]);
                break;
            case "setretain":
                need(number, words, 2);
                retain(number, words[1]);
                break;
            case "setfraction":
                need(number, words, 2);
                Double.parseDouble(words[1]);
                break;
            case "setbudget":
                need(number, words, 2);
                Long.parseLong(words[1]);
                break;
            case "check":
                need(number, words, 2);
                lookupTime(number, words[1]);
                break;
            case "get":
                if (words.length < 3) {
                    throw new BadWorkload("workload line " + number
                            + ": get TIME KEY...");
                }
                lookupTime(number, words[1]);
                for (int i = 2; i < words.length; i++) {
                    key(words[i]);
                }
                break;
            default:
                throw new BadWorkload("workload line " + number
                        + ": unknown command " + cmd);
            }
            w.lines.add(new Line(number, words, segment, trans));
        }
        if (!header) {
            throw new BadWorkload("empty workload");
        }
        return w;
    }

    /** The words of a line: split on white space; a word that starts with '#' ends it. */
    static String[] words(String text) {
        List<String> result = new ArrayList<String>();
        for (String s : text.trim().split("[ \t]+")) {
            if (s.isEmpty()) {
                continue;
            }
            if (s.charAt(0) == '#') {
                break;
            }
            result.add(s);
        }
        return result.toArray(new String[0]);
    }

    private void setting(int number, String[] words) {
        need(number, words, 3);
        String v = words[2];
        switch (words[1]) {
        case "maxnode":
            maxNode = Integer.parseInt(v);
            if (maxNode != 8 && maxNode != 14 && maxNode != 30 && maxNode != 62) {
                throw new BadWorkload("workload line " + number
                        + ": maxnode 8, 14, 30 or 62");
            }
            break;
        case "sd":
            startupDistance = Integer.parseInt(v);
            break;
        case "retain":
            retain = retain(number, v);
            break;
        case "fraction":
            Double.parseDouble(v);
            fraction = v;
            break;
        case "budget":
            budget = Long.parseLong(v);
            break;
        default:
            throw new BadWorkload("workload line " + number
                    + ": unknown setting " + words[1]);
        }
    }

    static long retain(int number, String v) {
        return v.equals("forever") ? Long.MAX_VALUE : Long.parseLong(v);
    }

    private static void need(int number, String[] words, int n) {
        if (words.length != n) {
            throw new BadWorkload("workload line " + number + ": " + words[0]
                    + " takes " + (n - 1) + " argument(s)");
        }
    }

    static long time(int number, String s) {
        long t = Long.parseLong(s);
        if (t < 0) {
            throw new BadWorkload("workload line " + number + ": negative time");
        }
        return t;
    }

    /** A lookup time: a number, or "latest" (Long.MAX_VALUE). */
    public static long lookupTime(int number, String s) {
        return s.equals("latest") ? Long.MAX_VALUE : time(number, s);
    }

    private static void checkTrans(int number, String[] words) {
        if (words.length < 2) {
            throw new BadWorkload("workload line " + number + ": t TIME|- OPS");
        }
        if (!words[1].equals("-")) {
            time(number, words[1]);
        }
        int i = 2;
        while (i < words.length) {
            if (words[i].equals("p") && i + 2 < words.length) {
                key(words[i + 1]);
                value(words[i + 2]);
                i += 3;
            } else if (words[i].equals("d") && i + 1 < words.length) {
                key(words[i + 1]);
                i += 2;
            } else {
                throw new BadWorkload("workload line " + number
                        + ": bad operation at word " + (i + 1));
            }
        }
    }

    // ======== Keys and values ========

    /** Decodes %XX escapes (two hex digits) into bytes; other characters as UTF-8. */
    static byte[] unescape(String s) {
        ByteArrayOutputStream out = new ByteArrayOutputStream(s.length());
        byte[] utf8 = s.getBytes(StandardCharsets.UTF_8);
        for (int i = 0; i < utf8.length; i++) {
            byte b = utf8[i];
            if (b == '%') {
                if (i + 2 >= utf8.length) {
                    throw new BadWorkload("bad escape in " + s);
                }
                out.write((hex(utf8[i + 1], s) << 4) | hex(utf8[i + 2], s));
                i += 2;
            } else {
                out.write(b);
            }
        }
        return out.toByteArray();
    }

    private static int hex(byte c, String s) {
        if (c >= '0' && c <= '9') return c - '0';
        if (c >= 'a' && c <= 'f') return c - 'a' + 10;
        if (c >= 'A' && c <= 'F') return c - 'A' + 10;
        throw new BadWorkload("bad hex digit in " + s);
    }

    /**
     * The bkey of a key word: the ikey's UTF-8 bytes (with %XX escapes), which must be valid
     * UTF-8 and not empty, converted as Keys.toBytes(String).
     */
    public static byte[] key(String word) {
        byte[] ikey = unescape(word);
        String s;
        try {
            s = StandardCharsets.UTF_8.newDecoder()
                    .onMalformedInput(CodingErrorAction.REPORT)
                    .onUnmappableCharacter(CodingErrorAction.REPORT)
                    .decode(ByteBuffer.wrap(ikey)).toString();
        } catch (CharacterCodingException e) {
            throw new BadWorkload("key not UTF-8: " + word);
        }
        if (s.isEmpty()) {
            throw new BadWorkload("empty key");
        }
        return Keys.toBytes(s);
    }

    /** The bytes of a value word: s:TEXT, x:HEX, z:N or r:SEED:N. */
    public static byte[] value(String word) {
        if (word.startsWith("s:")) {
            return unescape(word.substring(2));
        }
        if (word.startsWith("x:")) {
            String h = word.substring(2);
            if (h.length() % 2 != 0) {
                throw new BadWorkload("odd hex length: " + word);
            }
            byte[] b = new byte[h.length() / 2];
            for (int i = 0; i < b.length; i++) {
                b[i] = (byte) ((hexChar(h.charAt(2 * i), word) << 4)
                        | hexChar(h.charAt(2 * i + 1), word));
            }
            return b;
        }
        if (word.startsWith("z:")) {
            return new byte[size(word.substring(2), word)];
        }
        if (word.startsWith("r:")) {
            String[] parts = word.split(":");
            if (parts.length != 3) {
                throw new BadWorkload("r:SEED:N expected: " + word);
            }
            return random(Long.parseUnsignedLong(parts[1]), size(parts[2], word));
        }
        throw new BadWorkload("bad value: " + word);
    }

    private static int hexChar(char c, String s) {
        return hex((byte) c, s);
    }

    private static int size(String s, String word) {
        int n = Integer.parseInt(s);
        if (n < 0) {
            throw new BadWorkload("negative size: " + word);
        }
        return n;
    }

    /**
     * The bytes of r:SEED:N: xorshift64* from the state SEED (0x9E3779B97F4A7C15 if SEED is
     * 0); each step x ^= x >>> 12; x ^= x << 25; x ^= x >>> 27; and the word
     * x * 0x2545F4914F6CDD1D gives 8 bytes, least significant first; the last word is cut
     * to what N needs.
     */
    public static byte[] random(long seed, int n) {
        long x = seed == 0 ? 0x9E3779B97F4A7C15L : seed;
        byte[] b = new byte[n];
        for (int i = 0; i < n; i += 8) {
            x ^= x >>> 12;
            x ^= x << 25;
            x ^= x >>> 27;
            long w = x * 0x2545F4914F6CDD1DL;
            for (int k = 0; k < 8 && i + k < n; k++) {
                b[i + k] = (byte) (w >>> (8 * k));
            }
        }
        return b;
    }

    /**
     * The text of a bkey, as Run and Dump print it: byte 1 as '/'; any other byte b as the
     * ikey byte c = b - 2 (mod 256), printed as the character c if it is 0x21 to 0x7e but
     * '%', '/', '=' and '#', else as %XX (upper case). One text per bkey.
     */
    public static String keyText(byte[] bkey) {
        StringBuilder sb = new StringBuilder(bkey.length + 8);
        for (byte x : bkey) {
            int b = x & 0xff;
            if (b == 1) {
                sb.append('/');
                continue;
            }
            int c = (b - 2) & 0xff;
            if (c >= 0x21 && c <= 0x7e && c != '%' && c != '/' && c != '=' && c != '#') {
                sb.append((char) c);
            } else {
                sb.append('%').append(HEX_UPPER[c >> 4]).append(HEX_UPPER[c & 15]);
            }
        }
        return sb.toString();
    }

    private static final char[] HEX_UPPER = "0123456789ABCDEF".toCharArray();
}
