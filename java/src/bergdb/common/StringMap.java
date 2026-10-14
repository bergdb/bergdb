package bergdb.common;

import java.util.HashMap;
import java.util.Map;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Simple string-string map that can be easily serialized to a string and deserialized 
 * from a string. The serialized form, is similar to Java's property files, but even simpler.
 * 
 * @author Frans Lundberg
 */
public class StringMap {
    private final Map<String, String> map;
    
    /**
     * Creates an empty string map.
     */
    public StringMap() {
        map = new HashMap<String, String>();
    }

    /**
     * Creates a StringMap instance based on parsing the string 's'.
     */
    public StringMap(String s) {
        this();
        parse(s);
    }
    
    public void parse(String s) {
        String[] lines = s.split("\n");
        for (String line : lines) {
            line = line.trim();
            int index = line.indexOf('=');
            if (index == -1 || index == 0) {
                continue;
            }
            
            String key = line.substring(0, index);
            String value = line.substring(index + 1);
            
            if (key.length() > 0) {
                map.put(key, value);
            }
        }
    }
    
    public void put(String key, String value) {
        assert key != null;
        assert value != null;
        assert key.length() > 0;
        
        map.put(key, value);
    }
    
    /**
     * Returns the string value given its key. If there is no value for the speccified key, 
     * null is returned.
     */
    public String get(String key) {
        assert key != null;
        assert !key.contains("=");
        return map.get(key);
    }
    
    public boolean hasLong(String key) {
        String s = map.get(key);
        boolean result = true;
        
        if (s == null) {
            result = false;
        } else {
            try {
                Long.parseLong(s);
            } catch (NumberFormatException e) {
                result = false;
            }
        }
        
        return result;
    }
    
    /**
     * Gets a long.
     * 
     * @throws NumberFormatException
     */
    public long getLong(String key) {
        String s = map.get(key);
        if (s == null) {
            throw new NumberFormatException("No value for key " + key);
        }
        
        long result = Long.parseLong(s);
        return result;
    }
    
    public String serialize() {
        StringBuilder b = new StringBuilder();
        
        for (Map.Entry<String, String> entry : map.entrySet()) {
            b.append(entry.getKey() + "=" + entry.getValue() + "\n");
        }
        
        return b.toString();
    }
    
    
    // ======== Tests ========
    
    @Nano
    public static void test1() {
        StringMap m = new StringMap("k1=v1\nk2=v2\n");
        
        Assert.assertEquals("v1", m.get("k1"));
        Assert.assertEquals("v2", m.get("k2"));
    }
    
    @Nano
    public static void test2() {
        StringMap m = new StringMap();
        m.put("name", "Nalia");
        m.put("id", "1234");
        Assert.assertEquals("Nalia", m.get("name"));
        Assert.assertEquals("1234", m.get("id"));
        
        StringMap m2 = new StringMap(m.serialize());
        Assert.assertEquals("Nalia", m2.get("name"));
        Assert.assertEquals("1234", m2.get("id"));
    }
    
    @Nano
    public static void testLong() {
        StringMap m = new StringMap();
        m.put("name", "Nalia");
        m.put("id", "1234");
        
        Assert.assertTrue(m.hasLong("id"));
        Assert.assertFalse(m.hasLong("name"));
        Assert.assertFalse(m.hasLong("x"));
        Assert.assertEquals(1234L, m.getLong("id"));
    }
}
