package bergdb.dag;

public interface PointerVisitor {
    public void visit(INode from, Pointer pointer);
}
