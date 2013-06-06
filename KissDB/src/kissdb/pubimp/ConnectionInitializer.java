package kissdb.pubimp;

import kissdb.pub.Connection;

/**
 * Used to initialize a Connection to a preferred default state.
 * 
 * @author Frans Lundberg
 */
// Not yet moved to Pub API. Maybe not needed? We do not know yet.
public interface ConnectionInitializer {
    public void initialize(Connection connection);
}
