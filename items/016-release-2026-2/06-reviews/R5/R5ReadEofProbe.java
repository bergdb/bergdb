package bergdb.core;

import java.io.EOFException;
import java.io.IOException;
import bergdb.storage.BufferedStream;
import bergdb.stream.MemoryStream;

/** AppendOnlyStream.read documents EOFException for a request past the end. */
public class R5ReadEofProbe {
    public static void main(String[] args) throws Exception {
        Object lock = new Object();
        BufferedStream b;
        synchronized (lock) {
            b = new BufferedStream(new MemoryStream(), 1000, 10);
            b.start();
            b.append(new byte[] {42}, 0, 1);
        }
        try {
            IOException failure = null;
            try { b.read(1, new byte[1], 0, 1); }
            catch (IOException e) { failure = e; }
            if (failure == null) throw new AssertionError("read past end unexpectedly succeeded");
            System.out.println("read(position=1,length=1), streamLength=1: "
                    + failure.getClass().getName() + "; isEOFException="
                    + (failure instanceof EOFException));
            if (failure instanceof EOFException) {
                throw new AssertionError("expected BASE exception-contract mismatch not reproduced");
            }
        } finally { synchronized (lock) { b.close(); } }
    }
}
