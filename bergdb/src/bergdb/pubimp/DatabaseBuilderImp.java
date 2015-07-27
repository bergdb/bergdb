package bergdb.pubimp;

import java.io.File;
import java.io.IOException;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.EvictBoss;
import bergdb.pub.Clock;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.SalsaStream;

/**
 * This class is used to build a Database instance.
 * Use like this: <code>Database d = Builder.database().settingX().start();</code>
 * to create a Database.
 * 
 * @author Frans Lundberg
 */
public class DatabaseBuilderImp implements DatabaseBuilder {
    private final DbBuilder dbBuilder;
    private CryptoKey cryptoKey = null;
    
    public DatabaseBuilderImp() {
        dbBuilder = Db.builder();
    }
    
    /**
     * Creates and returns a database builder object that is used to create a database.
     */
    public static DatabaseBuilder database() {
        return new DatabaseBuilderImp();
    }
    
    /**
     * Returns the internal Db.Builder object.
     * Not part of Pub API.
     */
    public DbBuilder getDbBuilder() {
        return dbBuilder;
    }
    
    public DatabaseBuilder memory() {
        dbBuilder.mainStream(new MemoryStream());
        return this;
    }
    
    public DatabaseBuilder cryptoKey(CryptoKey cryptoKey) {
        this.cryptoKey = cryptoKey;
        return this;
    }
    
    public DatabaseBuilder replica(String name, String dir) throws IOException {
        FileStream stream = new FileStream(new File(dir));
        int bufferSize = StorageManager.DEFAULT_REPLICA_BUFFER_SIZE;
        int bufferTime = StorageManager.DEFAULT_BUFFER_TIME;
        dbBuilder.stream(name, stream, bufferSize, bufferTime);
        return this;
    }
    
    public DatabaseBuilder dir(String dirname) {
        File d = new File(dirname);
        return dir(d);
    }
    
    public DatabaseBuilder dir(File dir) {
        FileStream stream;
        try {
            stream = new FileStream(dir);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
        dbBuilder.mainStream(stream);
        return this;
    }
    
    public DatabaseBuilder clock(final Clock clock) {
        dbBuilder.clock(clock);
        return this;
    }
    
    public DatabaseBuilder retainDuration(Duration retainDuration) {
        dbBuilder.retainDuration(retainDuration.units());
        return this;
    }
    
    /**
     * Not part of Pub API.
     */
    public DatabaseBuilder mainStream(final AppendOnlyStream stream) {
        dbBuilder.mainStream(stream);
        return this;
    }
    
    /**
     * Not part of Pub API.
     */
    public DatabaseBuilder stream(String name, AppendOnlyStream stream) {
        dbBuilder.stream(name, stream);
        return this;
    }
    
    /**
     * Not part of Pub API.
     */
    public DatabaseBuilder noReclaim() {
        dbBuilder.retainForever();
        return this;
    }
    
    public DatabaseBuilder evictBoss(EvictBoss evictBoss) {
        dbBuilder.evictBoss(evictBoss);
        return this;
    }
    
    public Database start() {
        if (cryptoKey != null) {
            handleCryptoKey();
        }
        
        Db db = dbBuilder.build();
        return DatabaseImp.createAndStart(db);
    }

    private void handleCryptoKey() {
        if (dbBuilder.getStreamCount() == 0) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        AppendOnlyStream aos = dbBuilder.getMainStream();
        String algo = cryptoKey.getAlgo();
        
        if (!algo.equals("salsa")) {
            throw new IllegalStateException("Cannot encrypt with algorithm '" + algo + "'. Not supported.");
        }
        
        byte[] keyData = cryptoKey.getKeyData();
        if (keyData.length != 40) {
            throw new IllegalStateException("Unexpected keyData length, " + keyData.length + ".");
        }
        
        SalsaStream salsa;
        
        try {
            salsa = new SalsaStream(aos, Util.subarray(keyData, 0, 8), Util.subarray(keyData, 8, 32));
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
        // Note, that we do not handle buffer size, buffer time. Using defaults.
        // This is fine now (July 2015) since those parameters are not yet exposed to Pub API.
        
        dbBuilder.mainStream(salsa);
    }
}
