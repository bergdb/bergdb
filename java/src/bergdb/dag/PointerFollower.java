package bergdb.dag;

public interface PointerFollower {
    public Node followPointer(Node predecessor, int pointerIndex, OpData opData);
}
