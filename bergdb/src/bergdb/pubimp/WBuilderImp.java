package bergdb.pubimp;

import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;

/**
 * The WBuilder implementation.
 * A thin wrapper around RwEnvironmentImp.
 * 
 * @see bergdb.pub.WBuilder
 * @author Frans Lundberg
 */
public class WBuilderImp implements WBuilder {
    private ConnectionImp connection;
    private RwEnvironmentImp env;
    
    public WBuilderImp(ConnectionImp connection) {
        assert connection != null;
        this.connection = connection;
        this.env = new RwEnvironmentImp(connection);
    }
    
    /**
     * @throws IllegalArgumentException  
     *      If 'key' is null or otherwise invalid, or if object is null.
     */
    public WBuilder put(String ukey, Object object) {
        env.put(ukey, object);
        return this;
    }
    
    /**
     * @throws MissingKeyFieldException
     */
    public WBuilder put(Object object) {
        env.put(object);
        return this;
    }

    public WBuilder delete(String ukey) {
        env.delete(ukey);
        return this;
    }
    
    public WBuilder vkeyRead(long hash) {
        env.vkeyRead(hash);
        return this;
    }

    //public Transaction build() {
    //    Transaction trans = new WTransaction(env, connection);
    //    return trans;
    //}

    /**
     * @throws DbException if the database is faulty.
     */
    public Transaction execute() {
        WTransaction t = new WTransaction(env, connection);
        t.execute();
        return t;
    }
}
