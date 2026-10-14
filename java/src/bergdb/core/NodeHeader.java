package bergdb.core;

/**
 * Header for a node in the database stream.
 * Immutable.
 * 
 * @author Frans Lundberg
 */
public final class NodeHeader {
    private final byte type;
    private final long id;
    
    public NodeHeader(byte type, long id) {
        this.type = type;
        this.id = id;
    }
    
    public final byte type() {
        return type;
    }
    
    public final long id() {
        return id;
    }
}
