package bergdb.pubimp;

import bergdb.common.Bug;
import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Class with static methods for handling database keys.
 * 
 * @author Frans Lundberg
 */
public class PubKeys {
    
    private PubKeys() {}
    
    public static final char FILE_PREFIX = '-';
    
    public static final char DIR_PREFIX = 'd';
    
    /**
     * Converts a ukey to an ikey according to doc/2013-key-encoding.txt.
     * This method should always be applied to all keys as they cross the border between
     * the user application and the Pub Layer.
     * 
     * A key with a lone surrogate is invalid (bergdb 015-49, S2-F24): the UTF-8 encoding of
     * the key (Keys.toBytes) writes it as '?', so that the key and the one with '?' in its
     * place were one stored key; until 2026-11-05 it was taken.
     *
     * @param ukey The input ukey (user string key).
     * @return The ukey converted to an ikey.
     * @throws IllegalArgumentException  If ukey is null or invalid.
     */
    public static final String u2i(String ukey) throws IllegalArgumentException {
        if (ukey == null) {
            throw new IllegalArgumentException("null is not a valid key.");
        }
        
        int length = ukey.length();
        
        if (length == 0) {
            throw new IllegalArgumentException("The empty string is not a valid key.");
        }
        
        if (ukey.charAt(0) != '/') {
            throw new IllegalArgumentException("Key does not start with mandatory '/', key: " + ukey);
        }
        
        if (length < 2) { 
            throw new IllegalArgumentException("Key is too short: " + ukey);
        }

        if (hasLoneSurrogate(ukey)) {
            throw new IllegalArgumentException("Key has a lone surrogate, a char of "
                    + "U+D800 to U+DFFF that is not part of a surrogate pair (bergdb 015-49, "
                    + "S2-F24).");
        }
        
        String ikey = createIKey(ukey);
        return ikey;
    }

    private static String createIKey(String ukey) {
        int length = ukey.length();
        StringBuilder b = new StringBuilder();
        
        int lastSlashIndex = ukey.lastIndexOf('/');
        if (lastSlashIndex == -1) {
            throw new Bug("Cannot happen, ukey: " + ukey);
        }
        
        if (lastSlashIndex == length - 1) {
            throw new IllegalArgumentException("Key is not allowed to end with a '/', was: " + ukey);
        }
        
        int slashIndex = Integer.MIN_VALUE;
        
        for (int i = 0; i < length; i++) {
            char c = ukey.charAt(i);
            
            if (c == '/') {
                if (slashIndex == i - 1) {
                    throw new IllegalArgumentException("ukey cannot contain \"//\", was: " + ukey);
                }
                slashIndex = i;
                b.append(c);
                b.append(slashIndex == lastSlashIndex ? FILE_PREFIX : DIR_PREFIX);
            } else {
                b.append(c);
            }
        }
        
        return b.toString();
    }
    
    /**
     * True if 's' has a lone surrogate: a char of U+D800 to U+DFFF that is not part of a
     * surrogate pair, a high surrogate followed by a low one (bergdb 015-49, S2-F24). Its
     * UTF-8 encoding writes such a char as '?'. BergDB refuses such a string in a key, a
     * value and an object (bergdb 021-04); the check is StringUtil's, which the Core uses.
     */
    public static boolean hasLoneSurrogate(String s) {
        return StringUtil.hasLoneSurrogate(s);
    }

    /**
     * Converts a directory ukey to a directory ikey according to doc/2013-key-encoding.txt.
     * 
     * @throws IllegalArgumentException  If udir is null or empty, does not start or end with
     *      '/', or contains "//" anywhere. As u2i() does for a key; it was a
     *      BadFormatException (2026-10-25, bergdb 005-43). Also if it has a lone surrogate, as
     *      a key (bergdb 015-49, S2-F24). Until 2026-11-08 a directory that did not start
     *      with '/', or that ended with "//", was taken, such as "p/" and "/p//" (bergdb
     *      021-09): every caller relies on this method for what a directory is.
     */
    public static final String udir2idir(String udir) throws IllegalArgumentException {
        
        if (udir == null) {
            throw new IllegalArgumentException("null is not a valid dir.");
        }
        
        if (udir.length() == 0) {
            throw new IllegalArgumentException("The empty string is not a valid dir.");
        }
        
        int length = udir.length();
        
        if (udir.charAt(0) != '/') {
            throw new IllegalArgumentException("udir must start with '/', was: " + udir);
        }
        
        if (udir.charAt(length - 1) != '/') {
            throw new IllegalArgumentException("udir must end with '/', was: " + udir);
        }
        
        if (udir.contains("//")) {
            throw new IllegalArgumentException("udir cannot contain \"//\", was: " + udir);
        }

        if (hasLoneSurrogate(udir)) {
            throw new IllegalArgumentException("udir has a lone surrogate, a char of "
                    + "U+D800 to U+DFFF that is not part of a surrogate pair (bergdb 015-49, "
                    + "S2-F24).");
        }
        
        StringBuilder b = new StringBuilder();
        
        for (int i = 0; i < length - 1; i++) {
            char c = udir.charAt(i);
            
            if (c == '/') {
                b.append('/');
                b.append(DIR_PREFIX);
            } else {
                b.append(c);
            }
        }
        
        // last char is a '/' - no added 'd' wanted.
        b.append(udir.charAt(length - 1));     
        
        String idir = b.toString();
        return idir;
    }
    
    /**
     * Converts an ikey that was created from a ukey, back to the original ukey.
     * 
     * @throws IllegalArgumentException if ikey is not a valid ikey created from a ukey.
     */
    public static String i2u(String ikey) {
        if (ikey == null) {
            throw new IllegalArgumentException("ikey == null not allowed");
        }
        
        int length = ikey.length();
        
        if (length < 2) {
            throw new IllegalArgumentException("invalid ikey, too short, was: " + ikey);
        }
        
        if (ikey.charAt(0) != '/') {
            throw new IllegalArgumentException("an ikey should start with '/'");
        }
        
        StringBuilder b = new StringBuilder();
        boolean gotSlash = false;
        
        for (int i = 0; i < length; i++) {
            char c = ikey.charAt(i);
            if (gotSlash) {
                if (c == DIR_PREFIX || c == FILE_PREFIX) {
                    // fine :-)
                    gotSlash = false;
                } else {
                    throw new IllegalArgumentException("ikey cannot be converted to valid ukey, ikey: " + ikey);
                }
            } else {
                gotSlash = c == '/';
                b.append(c);
            }
        }
        
        String ukey = b.toString();
        return ukey;
    }
    
    
    // ======== Tests ========
    
    @Nano
    public static void testU2I_1() {
        String ukey = "/db1/customers/c001";
        String expected = "/ddb1/dcustomers/-c001";
        Assert.assertEquals(expected, PubKeys.u2i(ukey));
    }
    
    private static char ARABIC_LETTER_JEEM = '\u062c';
    
    @Nano
    public static void testU2I_2() {
        String[] ukeys = new String[] {
                "/a",
                "/dir/Special Chars: \u0000\u0001\u0002",
                "/ÅÄÖ-" + ARABIC_LETTER_JEEM + "/\u0000.txt"
        };
        
        String[] expected = new String[] {
                "/-a",
                "/ddir/-Special Chars: \u0000\u0001\u0002",
                "/dÅÄÖ-" + ARABIC_LETTER_JEEM + "/-\u0000.txt"
        };
        
        for (int i = 0; i < ukeys.length; i++) {
            Assert.assertEquals(expected[i], PubKeys.u2i(ukeys[i]));
        }
    }
    
    private static void assertI2uException(String ukey) {
        Exception ex = null;
        
        try {
            u2i(ukey);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @Nano
    public static void testToIkey2() {
        assertI2uException("");
        assertI2uException(null);
        assertI2uException("/dir/dir2//double-slash/not-allowed.txt");
        assertI2uException("/slash at end not allowed/");
    }
    
    /**
     * bergdb 015-49, S2-F24: a key or a directory with a lone surrogate is refused; one with
     * a surrogate pair is taken, its ikey as before.
     */
    @Nano
    public static void testLoneSurrogateRefused() {
        String[] badKeys = {"/a\uD800", "/\uDC00", "/a\uD800/b", "/a/b\uDBFF", "/\uDC00\uD800"};
        for (String ukey : badKeys) {
            assertI2uException(ukey);
        }
        String[] badDirs = {"/a\uD800/", "/\uDC00/b/"};
        for (String udir : badDirs) {
            try {
                udir2idir(udir);
                throw new AssertionError("taken, " + udir);
            } catch (IllegalArgumentException e) {
                // Expected.
            }
        }
        Assert.assertEquals("/da/-\uD83D\uDE00", u2i("/a/\uD83D\uDE00"));
        Assert.assertEquals("/d\uD83D\uDE00/", udir2idir("/\uD83D\uDE00/"));
        Assert.assertTrue(!hasLoneSurrogate("x\uD83D\uDE00y"));
        Assert.assertTrue(hasLoneSurrogate("x\uD83D"));
        Assert.assertTrue(hasLoneSurrogate("\uDE00x"));
        Assert.assertTrue(hasLoneSurrogate("\uD83D\uD83D\uDE00"));
    }

    /**
     * bergdb 005-43: a bad directory is an IllegalArgumentException, as a bad key is. Since
     * 021-09 also one that does not start with '/', or has "//" at its end ("p/", "a/b/",
     * "//", "/p//"), which were taken.
     */
    @Nano
    public static void testUdir2idirRefusesBadDirs() {
        String[] bad = {null, "", "/a", "a", "/a//b/", "a/", "p/", "a/b/", "//", "/a//", "///",
                "a//", "/a/b//", "/a\ud800/"};
        for (String udir : bad) {
            try {
                udir2idir(udir);
                throw new AssertionError("taken, " + udir);
            } catch (IllegalArgumentException e) {
                // Expected.
            }
        }
        Assert.assertEquals("/", udir2idir("/"));
        Assert.assertEquals("/da/", udir2idir("/a/"));
        Assert.assertEquals("/da/db/", udir2idir("/a/b/"));
        Assert.assertEquals("/d#i/", udir2idir("/#i/"));
        Assert.assertEquals("/da.b/", udir2idir("/a.b/"));
        assertDirRefused("p/", "start with '/'");
        assertDirRefused("/p//", "\"//\"");
        assertDirRefused("//", "\"//\"");
    }

    private static void assertDirRefused(String udir, String rule) {
        try {
            udir2idir(udir);
            throw new AssertionError("taken, " + udir);
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(rule)
                    && e.getMessage().contains(udir));
        }
    }

    /**
     * bergdb 021-09: every caller of udir2idir refuses what it refuses, with
     * IllegalArgumentException: IndexBuilder.dir(), UsePrimaryBuilder.dir() and an index's
     * definition (bergdb 020-10, section 4.2); the root "/" is taken by each.
     */
    @Nano
    public static void testDirCallersRefuseBadDirs() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            for (String udir : new String[] {"p/", "a/b/", "//", "/p//", "/p//q/", ""}) {
                assertThrowsArg("IndexBuilder.dir(" + udir + ")",
                        () -> db.indexBuilder("n").dir(udir));
                assertThrowsArg("UsePrimaryBuilder.dir(" + udir + ")",
                        () -> c.usePrimary(String.class).dir(udir));
                assertThrowsArg("IndexDefinition, dir " + udir,
                        () -> new IndexDefinition("n", udir, 1, false, new String[] {"long"},
                        new String[][] {{"a"}}));
            }
            db.indexBuilder("n").dir("/");
            c.usePrimary(String.class).dir("/").kvs();
            Assert.assertEquals("/", new IndexDefinition("n", "/", 1, false,
                    new String[] {"long"}, new String[][] {{"a"}}).idir());
        } finally {
            db.close();
        }
    }

    private static void assertThrowsArg(String what, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            return;
        }
        throw new AssertionError(what + ": taken");
    }
}
