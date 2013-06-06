package kissdb.common;

import java.io.PrintStream;

/**
 * A PrintStream that that is like a black hole. It receives data, but nothing gets away from
 * it; it is consumed by the "black hole" :-)
 */
public class NullPrintStream extends PrintStream {
    public NullPrintStream() {
        super(new NullOutputStream());
    }
}
