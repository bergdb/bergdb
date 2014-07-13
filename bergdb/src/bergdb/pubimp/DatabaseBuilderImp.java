package bergdb.pubimp;

import java.io.File;
import java.io.IOException;

import bergdb.core.Db;
import bergdb.core.IEvictBoss;
import bergdb.pub.Clock;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.storage.StorageManager;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * This class is used to build a Database instance.
 * Use code like this: <code>Database db = Builder.database().settingX().build();</code>
 * to create a Database.
 * 
 * @author Frans Lundberg
 */
public class DatabaseBuilderImp implements DatabaseBuilder {
    
    private Db.Builder dbBuilder;
    
    public DatabaseBuilderImp() {
        dbBuilder = Db.builder();
    }
    
    /**
     * Returns the internal Db.Builder object.
     * Not part of Pub API.
     */
    public Db.Builder getDbBuilder() {
        return dbBuilder;
    }
    
    /* (non-Javadoc)
     * @see com.bergdb.pub.IBuilder#memory()
     */
    public DatabaseBuilder memory() {
        dbBuilder.mainStream(new MemoryStream());
        return this;
    }
    
    public DatabaseBuilder replica(String name, String dir) throws IOException {
        FileStream stream = new FileStream(new File(dir));
        int bufferSize = StorageManager.DEFAULT_REPLICA_BUFFER_SIZE;
        int bufferTime = StorageManager.DEFAULT_BUFFER_TIME;
        dbBuilder.stream(name, stream, bufferSize, bufferTime);
        return this;
    }
    
    public DatabaseBuilder dir(String dirname) throws IOException {
        File d = new File(dirname);
        return dir(d);
    }
    
    public DatabaseBuilder dir(File dir) throws IOException {
        // NOTE We could allow/document more specific subclasses of IOException
        // that are thrown by FileStream.create().
        FileStream stream = new FileStream(dir);
        dbBuilder.mainStream(stream);
        return this;
    }
    
    public DatabaseBuilder clock(final Clock clock) {
        dbBuilder.clock(clock);
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
    
    public DatabaseBuilder evictBoss(IEvictBoss evictBoss) {
        dbBuilder.evictBoss(evictBoss);
        return this;
    }
    
    public Database start() {
        return DatabaseImp.createAndStart(dbBuilder.build());
    }
    
    /**
     * Creates and returns a database builder object that is used to create a database.
     */
    public static DatabaseBuilder database() {
        return new DatabaseBuilderImp();
    }
}
