package bergdb.pub;

/**
 * Immutable information about the start of the database.
 * 
 * @author Frans Lundberg
 */
public interface StartupInfo {
    
    /**
     * Returns the number of seconds that the database's own start took: the recovery, which
     * reads the stream from its last startup position, up to the startup distance from its
     * end (DatabaseBuilder.startupDistanceInMb()), and makes the database ready from it
     * (bergdb 020-24-10, U10-7). It leaves out what start() does before and after that: the
     * checks of the directory, its creation and lock, the opening of the stream's files and
     * created.txt, the making of the storage with its write buffer and thread, and the start
     * of the user indexes. So it is less than the time that start() takes: a third to a half
     * of it for small databases, where these steps take about as long as the recovery. For
     * the whole time, measure the call of start().
     */
    public double getStartupDuration();
}
