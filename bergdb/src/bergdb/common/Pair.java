package bergdb.common;

/**
 * 2-tuple implementation.
 * This class and Triplet forms a very simple tuple library for KissDB. 
 * If we need more feature, we should switch to http://www.javatuples.org/.
 * 
 * @param <T0>
 * @param <T1>
 * @author Frans Lundberg
 */
public class Pair<T0, T1> {
    private T0 v0;
    private T1 v1;
    
    public Pair(T0 v0, T1 v1) {
        this.v0 = v0;
        this.v1 = v1;
    }
    
    public T0 getValue0() {
        return v0;
    }
    
    public final T1 getValue1() {
        return v1;
    }
}
