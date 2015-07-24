package bergdb.dag;

public interface PointerVisitor {
    public void visit(Node from, Pointer pointer);
}
