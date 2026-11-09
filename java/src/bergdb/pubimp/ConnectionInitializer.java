package bergdb.pubimp;

import bergdb.pub.Connection;

/**
 * Used to initialize a Connection to a preferred default state.
 * 
 * @author Frans Lundberg
 */
// Not yet moved to Pub API. Maybe not needed? We do not know yet.
interface ConnectionInitializer {
    public void initialize(Connection connection);
}
