package bergdb.dag;

public interface PointerVisitor {
    /** 
     * Called once when a node is visited before any call to visitPointer 
     * for that node.
     */
    public void visitNode(Node node);
    
    public void visitPointer(Node from, Pointer pointer);
}
