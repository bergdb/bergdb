package bergdb.coreds;

/**
 * An instance of this class keep a list (sequence) of node sets in the
 * startup interval. Each node set contains the key/top nodes of a particular 
 * transaction.
 * This class is not thread-safe, use external synchronization.
 * Normally, and object of this class is protected by Db.writeLock.
 * 
 * @author Frans Lundberg
 */
public class TransSequence {

}
