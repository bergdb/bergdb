package bergdb.pubimp;

import bergdb.pub.StartupInfo;

/**
 * Information about the database startup. The jobs of the user indexes' builds are
 * Database.indexJob(name)'s since 2026-11-09 (bergdb 020-10, section 3.2).
 * 
 * @author Frans Lundberg
 */
class StartInfoImp implements StartupInfo {
    private double startTime;
    
    public StartInfoImp(double startTime) {
        this.startTime = startTime;
    }
    
    public double getStartupDuration() {
       return startTime;
    }
}
