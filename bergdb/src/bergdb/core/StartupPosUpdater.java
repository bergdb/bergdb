package bergdb.core;

public interface StartupPosUpdater {
    public long newStartupPos(
            long current, long streamLength, int startupDistance, 
            PosOfTransBeforeFunction posFunction);
}
