package bergdb.nanotest;

/**
 * Static utility methods to assert expected conditions.
 * 
 * @author Frans Lundberg
 */
public class Assert {
    private Assert() {}
    
    public static void assertEquals(String about, String expected, String actual) {
        if (!expected.equals(actual)) {
            throw new AssertionError(about + ", expected '" + expected + "', got '" + actual + "'.");
        }
    }
    
    public static void assertEquals(String expected, String actual) {
        if (!expected.equals(actual)) {
            throw new AssertionError("Expected '" + expected + "', got '" + actual + "'.");
        }
    }

    public static void assertEquals(boolean expected, boolean actual) {
        if (expected != actual) {
            throw new AssertionError("Expected " + expected + ", got " + actual + ".");
        }
    }
    
    public static void assertEquals(char expected, char actual) {
        if (actual != expected) {
            throw new AssertionError("Expected " + expected + ", got " + actual + ".");
        }
    }

    public static void assertFalse(boolean actual) {
        if (actual) {
            throw new AssertionError("Expected actual == false, was true.");
        }
    }

    public static void assertEquals(long expected, long actual) {
        if (actual != expected) {
            throw new AssertionError("Expected " + expected + ", got " + actual + ".");
        }
    }

    public static void assertNull(Object value) {
        if (value != null) {
            throw new AssertionError("Expected null, but got non-null value.");
        }
    }

    public static void assertEquals(Object expected, Object actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null, got non-null object: " + actual);
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected an object, got null.");
        }
        
        if (!actual.equals(expected)) {
            throw new AssertionError("Expected " + expected + ", got " + actual + ".");
        }
    }
    
    public static void assertEquals(String about, Object expected, Object actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError(about + ", expected null, got non-null object.");
            }
        }
        
        if (actual == null) {
            throw new AssertionError(about + ", expected an object, got null.");
        }
        
        if (!actual.equals(expected)) {
            throw new AssertionError(about + ", expected " + expected + ", got " + actual + ".");
        }
    }
    
    public static void assertEquals(String about, long expected, long actual) {
        if (actual != expected) {
            throw new AssertionError(about + ", expected " + expected + ", got " + actual + ".");
        }
    }
    
    public static void assertArrayEquals(boolean[] expected, boolean[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + (expected[i]) 
                        + " while actual[" + i + "] = " + (actual[i]));
            }
        }
    }
    
    public static void assertArrayEquals(byte[] expected, byte[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + ((int)expected[i]) 
                        + " while actual[" + i + "] = " + ((int)actual[i]));
            }
        }
    }
    
    public static boolean arrayEquals(byte[] expected, byte[] actual) {
        if (expected == null) {
            return actual == null ? true : false;
        }
        
        if (actual == null) {
            return false;
        }
        
        if (expected.length != actual.length) {
            return false;
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                return false;
            }
        }
        
        return true;
    }
    
    public static void assertArrayEquals(char[] expected, char[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + ((int)expected[i]) 
                        + " while actual[" + i + "] = " + ((int)actual[i]));
            }
        }
    }
    
    public static void assertArrayEquals(short[] expected, short[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + ((int)expected[i]) 
                        + " while actual[" + i + "] = " + ((int)actual[i]));
            }
        }
    }

    public static void assertArrayEquals(String about, byte[] expected,
            byte[] actual) {
        try {
            assertArrayEquals(expected, actual);
        } catch (AssertionError e) {
            throw new AssertionError(about + ". " + e.getMessage());
        }
    }
    
    public static void assertArrayEquals(int[] expected, int[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + ((int)expected[i]) 
                        + " while actual[" + i + "] = " + ((int)actual[i]));
            }
        }
    }

    public static void assertArrayEquals(long[] expected, long[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + expected[i] 
                        + " while actual[" + i + "] = " + actual[i]);
            }
        }
    }
    
    public static void assertArrayEquals(float[] expected, float[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + ((int)expected[i]) 
                        + " while actual[" + i + "] = " + ((int)actual[i]));
            }
        }
    }

    
    public static void assertArrayEquals(double[] expected, double[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            if (expected[i] != actual[i]) {
                throw new AssertionError("expected[" + i + "] = " + ((int)expected[i]) 
                        + ", but actual[" + i + "] = " + ((int)actual[i]));
            }
        }
    }

    public static void assertArrayEquals(String[] expected, String[] actual) {
        if (expected == null) {
            if (actual == null) {
                return;
            } else {
                throw new AssertionError("Expected null array, got non-null array of size " 
                        + actual.length + ".");
            }
        }
        
        if (actual == null) {
            throw new AssertionError("Expected non-null array, got null.");
        }
        
        if (expected.length != actual.length) {
            throw new AssertionError("Expected array has length " + expected.length 
                    + ", actual array has length " + actual.length + ".");
        }
        
        for (int i = 0; i < expected.length; i++) {
            String ex = expected[i];
            String ac = actual[i];
            
            if (ex == null) {
                if (ac == null) {
                    continue;
                } else {
                    throw new AssertionError("expected[" + i + "] = " + ex 
                            + ", but actual[" + i + "] = " + ac);
                }
            }
            
            if (!ex.equals(ac)) {
                throw new AssertionError("expected[" + i + "] = " + ex 
                        + ", but actual[" + i + "] = " + ac);
            }
        }
    }

    public static void assertTrue(String message, boolean b) {
        if (!b) {
            throw new AssertionError(message + ", expected true, but was false.");
        }
    }

    public static void assertTrue(boolean b) {
        if (!b) {
            throw new AssertionError("Expected true, but was false.");
        }
    }

    public static void assertEquals(double expected, double actual, double tolerance) {
        double diff = Math.abs(actual - expected);
        if (diff > tolerance) {
            throw new AssertionError("Expected " + expected + ", got " + actual + ".");
        }
    }
}
