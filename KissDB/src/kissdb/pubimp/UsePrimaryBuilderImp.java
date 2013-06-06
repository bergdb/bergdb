package kissdb.pubimp;

import kissdb.pub.Database;
import kissdb.pub.Kv;
import kissdb.pub.NoSuchIndexException;
import kissdb.pub.UsePrimaryBuilder;

/**
 * This implementation mostly uses a wrapped IndexIterBuilderImp class.
 * 
 * @author Frans Lundberg
 */
public class UsePrimaryBuilderImp<TYPE> implements UsePrimaryBuilder<TYPE> {
    private UseIndexBuilderImp<TYPE> builder;
    
    /**
     * @throws NoSuchIndexException if no index with the name exists.
     */
    public UsePrimaryBuilderImp(ConnectionImp connection, Class<TYPE> type, 
            long wantedLookupTime) {
        builder = new UseIndexBuilderImp<TYPE>(connection, Database.PRIMARY, type, wantedLookupTime);
    }
    
    public UsePrimaryBuilder<TYPE> dir(String udir) {
        String idir = PubKeys.udir2idir(udir);
        String prefix = idir + "-";     // "-" to iterate files only. We focus on that.
        builder.prefix(prefix);
        return this;
    }
    
    public UsePrimaryBuilder<TYPE> dirInternal(String idir) {
        String prefix = idir + "-";     // "-" to iterate files only. We focus on that.
        builder.prefix(prefix);
        return this;
    }
    
    public UsePrimaryBuilder<TYPE> inclusive(boolean inclusive) {
        builder.inclusive(inclusive);
        return this;
    }

    public UsePrimaryBuilder<TYPE> backward() {
        builder.backward();
        return this;
    }

    public UsePrimaryBuilder<TYPE> startAt(String value) {
        builder.startAt(value);
        return this;
    }

    public Iterable<TYPE> objects() {
        return builder.objects();
    }

    public Iterable<Kv<TYPE>> kvs() {
        return builder.kvs();
    }
}
