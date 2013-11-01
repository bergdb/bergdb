package bergdb.dag;

/**
 * Node visitor interface.
 */
public interface NodeVisitor {
    public void visit(TopNode node);
    public void visit(KeyNode node);
    public void visit(ValueNode node);
}
