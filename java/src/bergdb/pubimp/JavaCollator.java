package bergdb.pubimp;

import java.text.Collator;

/**
 * Uses a Java standard Collator object to get the sort bytes.
 * 
 * @author Frans Lundberg
 */
public class JavaCollator implements KCollator {
    private Collator collator;

    public JavaCollator(Collator collator) {
        assert collator != null;
        this.collator = collator;
    }
    
    public byte[] getSortBytes(String s) {
        return collator.getCollationKey(s).toByteArray();
    }
}
