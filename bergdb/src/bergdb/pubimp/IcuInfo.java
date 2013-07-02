package bergdb.pubimp;

/**
 * Info about whether current VM has access to ICU or not.
 * 
 * @author Frans Lundberg
 */
public class IcuInfo {
    // Lazy init of hasIcu boolean.
    
    private static volatile boolean isSet = false;
    private static boolean hasIcu = false;
    private static String icuClass = "bergdb.icu50.text.Collator";
    
    public static boolean hasIcu() {
        if (!isSet) {
            // This code may run concurrently in multiple thread (not likely, but possible).
            // All threads will set hasIcu to same value, so this is fine.
            // We could even make "isSet" non-volatile, like Java's String.hashCode() code.
            
            try {
                Class.forName(icuClass);
                hasIcu = true;
            } catch (ClassNotFoundException e) {
                hasIcu = false;
            }
            
            isSet = true;
        }
        
        return hasIcu;
    }
}
