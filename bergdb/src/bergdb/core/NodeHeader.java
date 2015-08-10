package bergdb.core;

/**
 * Header for a node in the database stream.
 * Immutable.
 * 
 * @author Frans Lundberg
 */
public class NodeHeader {
    private final byte type;
    private final long id;
    
    public NodeHeader(byte type, long id) {
        this.type = type;
        this.id = id;
    }
    
    public byte getType() {
        return type;
    }
    
    public long getId() {
        return id;
    }
}
