package bergdb.stream;

import java.io.IOException;

/**
 * A test stream that enforces pretruncate exactly, written 2026-10-13 for the
 * level 3 tests (docs/levels.md). It wraps a MemoryStream; after
 * pretruncate(p), getFirstPos() is p and a read of any byte below p throws.
 * MemoryStream drops whole 1 MB arrays and FileStream whole files, so a read
 * just below the cut would otherwise pass unnoticed.
 *
 * For a restart, make a new CutStream from copy(): db.stop() closes this one.
 */
public class CutStream implements AppendOnlyStream {
    final MemoryStream inner;
    private long cut;
    private long lengthAtCut;       // the stream length when the last cut was made

    public CutStream() {
        this(new MemoryStream(), 0, 0);
    }

    private CutStream(MemoryStream inner, long cut, long lengthAtCut) {
        this.inner = inner;
        this.cut = cut;
        this.lengthAtCut = lengthAtCut;
    }

    /** A copy of the bytes and the cut, open for appends. */
    public synchronized CutStream copy() {
        return new CutStream(inner.copy(), cut, lengthAtCut);
    }
    
    /** The stream length when the last cut was made; a crash cannot lose bytes before it. */
    public synchronized long getLengthAtCut() {
        return lengthAtCut;
    }
    
    /** Removes bytes from the end, as a crash; see MemoryStream.truncate(). */
    public synchronized void truncate(long newLength) {
        if (newLength < lengthAtCut) {
            throw new IllegalArgumentException("truncate to " + newLength 
                    + ", before the length at the last cut, " + lengthAtCut);
        }
        inner.truncate(newLength);
    }

    public synchronized long getCut() {
        return cut;
    }

    public synchronized long getLength() {
        return inner.getLength();
    }

    public synchronized long getFirstPos() {
        return Math.max(cut, inner.getFirstPos());
    }

    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        synchronized (this) {
            if (position < cut && length > 0) {
                throw new ReadBelowFirstPosException("CutStream: read of " + length
                        + " bytes at " + position + ", below the cut at " + cut);
            }
        }
        inner.read(position, dest, destOffset, length);
    }

    public void append(byte[] source, int sourceOffset, int length) throws IOException {
        inner.append(source, sourceOffset, length);
    }

    public synchronized void pretruncate(long position) throws IOException {
        if (position < cut) {
            throw new IOException("CutStream: pretruncate to " + position
                    + ", below the earlier cut at " + cut);
        }
        if (position > inner.getLength()) {
            throw new IOException("CutStream: pretruncate to " + position
                    + ", beyond the length " + inner.getLength());
        }
        cut = position;
        lengthAtCut = inner.getLength();
        inner.pretruncate(position);
    }

    public void close() throws IOException {
        inner.close();
    }
}
