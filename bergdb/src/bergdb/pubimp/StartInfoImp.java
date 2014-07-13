package bergdb.pubimp;

import java.util.List;

import bergdb.pub.Job;
import bergdb.pub.StartInfo;

/**
 * Information about the database startup.
 * 
 * @author Frans Lundberg
 */
public class StartInfoImp implements StartInfo {
    private Job[] startJobs;
    private double startTime;
    
    public StartInfoImp(List<Job> startJobs, double startTime) {
        this.startJobs = startJobs.toArray(new Job[startJobs.size()]);
        this.startTime = startTime;
    }
    
    public Job[] getStartJobs() {
        return startJobs.clone();
    }
    
    public double getStartTime() {
       return startTime;
    }
}
