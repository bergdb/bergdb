package bergdb.pubimp;

import java.util.List;

import bergdb.pub.StartupInfo;
import bergdb.pub.util.Job;

/**
 * Information about the database startup.
 * 
 * @author Frans Lundberg
 */
public class StartInfoImp implements StartupInfo {
    private Job[] startJobs;
    private double startTime;
    
    public StartInfoImp(List<Job> startJobs, double startTime) {
        this.startJobs = startJobs.toArray(new Job[startJobs.size()]);
        this.startTime = startTime;
    }
    
    public Job[] getStartupJobs() {
        return startJobs.clone();
    }
    
    public double getStartupDuration() {
       return startTime;
    }
}
