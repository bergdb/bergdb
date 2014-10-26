package bergdb.core;

public interface StartupPosUpdater {
    public long newStartupPos(
            long current, long streamLength, int startupDistance, 
            PosOfTransBeforeFunction posFunction);
    
    /**
     * Updater for testing; each new start pos is set manually.
     */
    public static class TestUpdater implements StartupPosUpdater {
        private long nextPos = -1;
        
        /** Sets next pos, or -1 for no change. */
        public void setNextPos(long pos) {
            this.nextPos = pos;
        }

        public long newStartupPos(long current, long streamLength, int startupDistance,
                PosOfTransBeforeFunction posFunction) {
            if (nextPos == -1) {
                return current;
            } else {
                return nextPos;
            }
        }
    }
}
