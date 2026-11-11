package bergdb.dag;

public interface PointerFollower {
    public Node followPointer(Node predecessor, int pointerIndex, OpData opData);
    
    /**
     * The exception for a cycle that a descent or a scan met (OpData.descentTo(),
     * GetMany's chain): damage of the stream, which this package does not know. Db's
     * followers (NodeCollection) give a StreamFormatException, as for other damage that a
     * follow finds; by default, an IllegalStateException.
     */
    public default RuntimeException cycle(String message) {
        return new IllegalStateException(message);
    }
}
