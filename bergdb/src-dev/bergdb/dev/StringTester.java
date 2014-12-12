package bergdb.dev;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Test how java strings work. Tests are for determining how strings are handled with
 * exotic JVMs (read: IKVM, GCJ).
 * 
 * @author Frans Lundberg
 */
public class StringTester {

    @Nano
    public static void testNull0() {
        String s = "pre\u0000post";
        Assert.assertEquals(8, s.length());
    }
    
    @Nano
    public static void testConcat0() {
        String s1 = "\u0000post";
        String s2 = "pre";
        String s3 = s2 + s1;
        Assert.assertEquals("pre\u0000post", s3);
    }
    
    @Nano
    public static void testConcat1() {
        String s1 = "\u0000\u0001\u0002\u0003";
        String s2 = "txt";
        String s3 = s1 + s2 + s1;
        Assert.assertEquals("\u0000\u0001\u0002\u0003txt\u0000\u0001\u0002\u0003", s3);
    }
    
    @Nano
    public static void testIndexOf() {
        String s = "pre\u0000abc\u0000end";
        Assert.assertEquals(3, s.indexOf('\u0000'));
        Assert.assertEquals(7, s.lastIndexOf('\u0000'));
        String s2 = "preabcend";
        Assert.assertEquals(-1, s2.lastIndexOf('\u0000'));
        Assert.assertEquals(-1, s2.indexOf('\u0000'));
    }
    
    public static void printControl() {
        System.out.println("---- printControl ----");
        System.out.println("Prints ASCII control chars, 0 - 34.");
        for (int i = 0; i <= 34; i++) {
            byte b = (byte) i;
            String hex = Util.toHexString(new byte[]{b});
            hex = "0x" + hex;
            System.out.println(i + ", " + hex + ", BEFORE'" + ((char) i + "'AFTER"));
        }
        
        System.out.println("0000 escaped: '\u0000'");
        System.out.println("0001 escaped: '\u0001'");
        System.out.println("0002 escaped: '\u0002'");
        System.out.println("0003 escaped: '\u0003'");
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) {
        printControl();
    }
}
