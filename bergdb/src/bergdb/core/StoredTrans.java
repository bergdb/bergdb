package bergdb.core;

import java.util.ArrayList;

import bergdb.common.Bytes;
import bergdb.dag.INode;
import bergdb.dag.ValueNode;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

// TODO B. Should we use this? Not used now, 140124.

/**
 * This class deserializes transaction data from the database stream
 * in the constructor. An object of this class represents what is stored
 * in the stream. It is immutable.
 * 
 * @see TransSerializer
 * @author Frans Lundberg
 */
public class StoredTrans {
    public final long transTime;
    public final long transPos;         // first spos of transaction (tpos)
    public final long transSize;        // byte size of transaction (not including meta blocks)
    public final long lastPos;          // the spos of the last byte of the transaction
    public final StoredNode[] nodes;
    public final byte[][] keys;
    
    private int offset;   // internal data, only for parsing in constructor
    
    /**
     * @throws StreamFormatException
     * @throws IllegalArgumentException
     */
    public StoredTrans(long transPos, byte[] buffer) {
        if (buffer == null) {
            throw new IllegalArgumentException("buffer == null not allowed");
        }
        
        if (buffer.length < 16+1) {
            throw new StreamFormatException("buffer too short, " + buffer.length);
        }
        
        if (transPos < 0) {
            throw new IllegalArgumentException("transPos < 0, " + transPos);
        }
        
        this.transPos = transPos;
        
        offset = 0;
        int byteSize = Bytes.bytesToIntLE(buffer, offset);
        offset += 4;
        
        if (byteSize != buffer.length) {
            throw new StreamFormatException("Incompatiable sizes, " 
                    + byteSize + " != " + buffer.length);
        }
        
        offset += 4;      // 4 unused bytes
        
        transTime = Bytes.bytesToLongLE(buffer, offset);
        offset += 8;
        
        // Parse nodes
        
        ArrayList<StoredNode> nodeList = new ArrayList<StoredNode>();
        while (true) {
            StoredNode stored = next(buffer);
            if (stored == null) {
                break;
            }
            
            nodeList.add(stored);
        }
        
        nodes = nodeList.toArray(new StoredNode[nodeList.size()]);
        
        // Parse keys
        
        int keyCount = Bytes.bytesToIntLE(buffer, offset);

        offset += 4;
        if (keyCount < 0) {
            throw new StreamFormatException("keyCount < 0, " + keyCount);
        }
        
        ArrayList<byte[]> keyList = new ArrayList<byte[]>();
        for (int i = 0; i < keyCount; i++) {
            int keySize = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            if (keySize < 0) {
                throw new StreamFormatException("Bad keySize, " + keySize + ", offset=" + offset);
            }
            
            byte[] keyBytes = new byte[keySize];
            System.arraycopy(buffer, offset, keyBytes, 0, keySize);
            offset += keySize;
            
            keyList.add(keyBytes);
        }
        
        this.transSize = offset;
        this.lastPos = RecoverableStream.getSpos(transPos, offset - 1);
        
        keys = keyList.toArray(new byte[keyList.size()][]);
    }
    
    /**
     * @throws StreamFormatException
     */
    private StoredNode next(byte[] buffer) {
        // TODO E. Do we need two ways of returning null?
        
        StoredNode storedNode = new StoredNode();
        
        if (offset + 4 >= buffer.length) {
            return null;
        }
        
        int nodeSize = Bytes.bytesToIntLE(buffer, offset);
        if (nodeSize == 0) {
            offset += 4;
            return null;
        }
        
        long spos = RecoverableStream.getSpos(transPos, offset);
        NodeStream.bytesToNode(spos, buffer, offset, nodeSize, storedNode);
        
        offset += nodeSize;
        return storedNode;
    }
    
    /**
     * Converts the stored transation to a Trans object.
     * 
     * @throws StreamFormatException
     */
    public Trans toTrans() {
        Trans.Builder b = Trans.builder();
        
        int valueCount = 0;
        for (StoredNode s : nodes) {
            byte type = s.node.getType();
            if (type == INode.TYPE_VALUE || type == INode.TYPE_DELETE) {
                valueCount++;
            }
        }
        
        if (keys.length != valueCount) {
            throw new StreamFormatException("keys.length does not match number of value nodes, " 
                    + keys.length + ", " + valueCount);
        }
        
        int offset = 0;
        
        for (StoredNode s : nodes) {
            byte type = s.node.getType();
            if (type == INode.TYPE_VALUE) {
                byte[] value = ((ValueNode) s.node).getValue();
                if (value == null) {
                    throw new IllegalStateException("ValueNode with null value not allowed, " + s.node);
                }
                b.put(keys[offset], value);
                offset++;
            } else if (type == INode.TYPE_DELETE) {
                b.delete(keys[offset]);
                offset++;
            }
        }
        
        Trans result = b.build();
        result.time = this.transTime;
        
        return result;
    }
    
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("tt:" + transTime + ", transPos:" + transPos);
        b.append(", nodeCount:" + this.nodes.length + ", keyCount:" + this.keys.length);
        return b.toString();
    }
}
