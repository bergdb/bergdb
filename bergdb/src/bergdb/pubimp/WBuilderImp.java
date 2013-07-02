package bergdb.pubimp;

import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;

/**
 * The WBuilder implementation.
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
     * @throws BadFormatException
     */
    public WBuilder set(String ukey, Object object) {
        env.set(ukey, object);
        return this;
    }
    
    /**
     * @throws MissingKeyFieldException
     */
    public WBuilder set(Object object) {
        env.set(object);
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

    public Transaction build() {
        Transaction trans = new WTransaction(env, connection);
        return trans;
    }

    /**
     * @throws DbException if the database is faulty.
     */
    public Transaction execute() {
        Transaction t = build();
        t.execute();
        return t;
    }
}
