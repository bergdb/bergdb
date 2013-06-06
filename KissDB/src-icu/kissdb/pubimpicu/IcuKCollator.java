package kissdb.pubimpicu;


import kissdb.icu50.text.Collator;
import kissdb.pubimp.KCollator;

/**
 * Uses a Collator from ICU4J to get the sort bytes of strings.
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
