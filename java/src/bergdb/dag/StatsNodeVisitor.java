package bergdb.dag;

public class StatsNodeVisitor implements NodeVisitor {
    public long topCount = 0;
    public long keyCount = 0;
    public long valueCount = 0;
    
    public void visit(TopNode node) {
        topCount++;
        handle(node);
    }

    public void visit(KeyNode node) {
        keyCount++;
        handle(node);
    }

    public void visit(ValueNode node) {
        valueCount++;
        handle(node);
    }
    
    /**
     * Override for common action for all node types.
     */
    public void handle(Node node) {}
}
