package bergdb.pubimp;

/**
 * DbObject field reference.
 * Can be a direct field name or a reference to a nested field.
 * 
 * @author Frans Lundberg
 */
public class FieldRef {
    private final String[] parts;
    
    public FieldRef(String name) {
        assert name != null;
        parts = new String[]{name};
    }
    
    public FieldRef(String[] parts) {
        assert parts != null;
        assert parts.length > 0;
        this.parts = parts.clone();
    }
    
    public boolean isNested() {
        return parts.length > 1;
    }
    
    public String getName() {
        if (parts.length == 1) {
            return parts[0];
        }
        
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < parts.length; i++) {
            b.append(parts[i]);
            if (i != parts.length - 1) {
                b.append(".");
            }
        }
        return b.toString();
    }
    
    public String[] getNameParts() {
        // A little bad style, but good for permformance to 
        // give directly to DbObject.has(String[]) / get().
        return parts;
    }
    
    public String toString() {
        if (parts.length == 1) {
            return parts[0];
        }
        
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < parts.length; i++) {
            b.append(parts[i]);
            if (i != parts.length - 1) {
                b.append(".");
            }
        }
        return b.toString();
    }
}
