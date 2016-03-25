package bergdb.nanotest;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * A very simple command line parser.
 * Example: -group a -verbose -users alan peter
 * Three options, one with a single value (-group), one with zero values (-verbose)
 * and one with two values (-users).
 * There are more capable implementations in external libraries.
 * This class can be used to avoid a dependency.
 * 
 * Also see https://github.com/franslundberg/java-cut/blob/master/src/cut/CommandLine.java.
 * 
 * @author Frans Lundberg
 */
public class CommandLine {
    // There are more capable implementations in external libraries.
    // This class avoids a dependency.
    
    private static final String[] empty = new String[0];
    private final HashMap<String, String[]> map;
    private final String[] args;
    
    /**
     * Creates an immutable CommandLine object from args.
     */
    public CommandLine(String[] args) {
        this.args = args.clone();
        map = new HashMap<String, String[]>();
        
        String name = null;
        List<String> values = null;
        
        for (String arg : args) {
            if (isName(arg)) {
                putOptionToMap(name, values);
                
                name = createName(arg);
                values = new ArrayList<String>();
            } else {
                if (name != null) {
                    values.add(arg);
                }
            }
        }
        
        putOptionToMap(name, values);
    }
    
    /**
     * Has zero of more values with the given option name.
     */
    public boolean has(String name) {
        return valueCount(name) >= 0;
    }
    
    public boolean hasOne(String name) {
        return valueCount(name) == 1;
    }
    
    public String[] get(String name) {
        return map.get(name);
    }
    
    public String getOne(String name) {
        return valueCount(name) > 0 ? get(name)[0] : null;
    }
    
    /**
     * Number of values given option name.
     * 
     * @return The number of values or -1 if the option does not exist.
     */
    public int valueCount(String name) {
        String[] arr = map.get(name);
        return arr == null ? -1 : arr.length;
    }
    
    public int optionCount() {
        return map.size();
    }
    
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (String s : args) {
            b.append(s + " ");
        }
        
        return b.toString().trim();
    }

    private void putOptionToMap(String name, List<String> values) {
        if (name != null) {
            map.put(name, values.toArray(empty));
        }
    }

    private boolean isName(String arg) {
        return arg.length() > 1 && arg.startsWith("-");
    }

    private String createName(String arg) {
        assert isName(arg);
        return arg.substring(1);
    }
    
    
    // ======== Tests ========
    
    @Nano
    private static void testNoOptions() {
        CommandLine line = new CommandLine(new String[0]);
        
        Assert.assertEquals(-1, line.valueCount("opt"));
        Assert.assertEquals(0, line.optionCount());
    }
    
    @Nano
    private static void testOneOption() {
        CommandLine line = new CommandLine(new String[]{"-groups", "unit"});
        
        Assert.assertEquals("valueCount", 1, line.valueCount("groups"));
        Assert.assertEquals("optionCount", 1, line.optionCount());
        Assert.assertEquals("unit", line.getOne("groups"));
        Assert.assertEquals("unit", line.get("groups")[0]);
    }
    
    @Nano
    private static void testMultipleValues() {
        CommandLine line = new CommandLine(new String[]{"-groups", "unit", "f"});
        
        Assert.assertEquals(2, line.valueCount("groups"));
        Assert.assertEquals(1, line.optionCount());
        Assert.assertEquals("getOne", "unit", line.getOne("groups"));
        Assert.assertEquals("get0", "unit", line.get("groups")[0]);
        Assert.assertEquals("get1", "f", line.get("groups")[1]);
    }
    
    @Nano
    public static void valuesWithNoOptionShouldBeIgnored() {
        CommandLine line = new CommandLine(new String[]{"value1", "value2"});
        Assert.assertEquals(0, line.optionCount());
    }
}
