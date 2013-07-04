package bergdb.pubimpicu;


import bergdb.pubimp.KCollator;
import bergdb.icu50.text.Collator;

/**
 * Uses a Collator from ICU4J to get the sort bytes of strings.
 * 
 * @author Frans Lundberg
 */
public class IcuKCollator implements KCollator {
    private Collator collator;
    
    public IcuKCollator(Collator collator) {
        this.collator = collator;
    }
    
    public byte[] getSortBytes(String s) {
        assert s != null;
        return collator.getCollationKey(s).toByteArray();
    }
}
