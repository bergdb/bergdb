package bergdb.pubimp;

import java.io.File;
import java.io.IOException;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
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
        // By default, half of max memory used by database cache.
        
        dbBuilder = Db.builder();
        
        long max = Runtime.getRuntime().maxMemory();
        if (max != Long.MAX_VALUE) {
            dbBuilder.targetCacheSize(max / 2);
        }
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
        if (!cryptoKey.isNull()) {
            this.cryptoKey = cryptoKey;
        }
        
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
    
    public DatabaseBuilder startupDistanceInMb(int startupDistanceInMb) {
        if (startupDistanceInMb < 5) {
            startupDistanceInMb = 5;
        }
        
        if (startupDistanceInMb > 1000) {
            startupDistanceInMb = 1000;
        }
        
        dbBuilder.startupDistance(startupDistanceInMb * 1000000);
        return this;
    }
    
    public DatabaseBuilder targetCacheSizeInMb(int targetCacheSizeInMb) {
        // Note: we might want to clamp depending on startupDistance? 2 x startupDistance perhaps.
        
        if (targetCacheSizeInMb < 10) {
            targetCacheSizeInMb = 10;
        }
        
        dbBuilder.targetCacheSize(targetCacheSizeInMb * 1000000L);
        return this;
    }
    
    public Database start() {
        handleCryptoKeyAndCreatedTxt();
        
        Db db = dbBuilder.build();
        return DatabaseImp.createAndStart(db);
    }

    private void handleCryptoKeyAndCreatedTxt() {
        // Note, that we do not handle buffer size, buffer time. Using defaults.
        // This is fine now (July 2015) since those parameters are not yet exposed to Pub API.
        
        if (dbBuilder.getStreamCount() == 0) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        AppendOnlyStream aos = dbBuilder.getMainStream();
        
        if (this.cryptoKey == null) {
            if (aos instanceof FileStream) {
                FileStream fileStream = (FileStream) aos;
                dbBuilder.createdTxt(fileStream.getDir(), null);
            }
        } else {
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
                byte[] nonce = Util.subarray(keyData, 0, 8);
                byte[] key = Util.subarray(keyData, 8, 32);
                salsa = new SalsaStream(aos, nonce, key);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            
            if (aos instanceof FileStream) {
                FileStream fileStream = (FileStream) aos;
                dbBuilder.createdTxt(fileStream.getDir(), cryptoKey.toStringWithMaskedKey());
            }
            
            dbBuilder.mainStream(salsa);
        }
    }
    
    
    // ======== Testing ========
    
    @Nano private static void testStartupDistance1() {
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.startupDistanceInMb(7);
        Assert.assertEquals(7*1000000, b.getDbBuilder().getStartupDistance());
    }
    
    @Nano private static void testStartupDistance2() {
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.startupDistanceInMb(2);
        Assert.assertEquals(5*1000000, b.getDbBuilder().getStartupDistance());
    }
}
