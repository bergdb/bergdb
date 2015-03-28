package bergdb.pubimp;

/**
 * A collator factory based on the internally available code (not on ICU collators).
 * 
 * @author Frans Lundberg
 */
public class BergCollatorFactory implements CollatorFactory {
    
    public BergCollatorFactory() {
    }

    public KCollator createCollator(String typeString) {
        KCollator result = null;
  
        if (typeString.equals("string") || typeString.equals("string/unicode")) {
            result = UnicodeCollator.INSTANCE;
        }
        
        return result;
    }

    /**
     * Check of index type string.
     */
    public boolean typeSupported(String type) {
        if (type == null || type.length() == 0) {
            return false;
        }
        
        char first = type.charAt(0);
        boolean result = false;
        
        switch (first) {
        case 'l':
            if (type.equals("long")) {
                result = true;
            }
            break;
            
        case 'd':
            if (type.equals("double")) {
                result = true;
            }
            break;
            
        case 's':
            if (type.equals("string") || type.equals("string/unicode")) {
                result = true;
            }
            break;
        }
        
        return result;
    }
}
