package bergdb.pubimp;

import bergdb.graph.Keys;

/**
 * Special handling for the primary key.
 * 
 * @author Frans Lundberg
 */
public class PrimaryKeyCollator implements KCollator {
    public byte[] getSortBytes(String s) {
        return Keys.toBytes(s);
    }
}
