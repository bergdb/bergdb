package bergdb.core;

import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/** E bounds the scan, but the final touch still goes to the end. */
public final class ReclaimTail {
    public static void main(String[] args) {
        CoreTestClock clock = new CoreTestClock();
        long now=10*Clock.UNITS_PER_SEC;
        clock.setTime(now);
        Db db=Db.builder().testSetup(new CutStream()).clock(clock).startupDistance(2000).start();
        Reclaim rc=db.internal().reclaim();
        Reclaim.Stats stats=rc.enableStats();
        byte[] value=new byte[10];
        for(int i=0;i<5000;i+=100) {
            clock.setTime(now+=10000);
            Trans.Builder b=db.trans();
            for(int j=i;j<i+100;j++) b.put(String.format("/a/%09d",j),value);
            db.execute(b.build());
        }
        db.setRetainDuration(1000*Clock.UNITS_PER_SEC);
        clock.setTime(now+=10000);
        db.execute(db.trans().put("/a/sentinel",value).build());
        System.out.println("end="+Keys.toString(rc.currentIteration().endKey));
        int next=0;
        long maxCallDirtiedBytes=0;
        for(int i=0;rc.getIterationCount()==0 && i<300;i++) {
            clock.setTime(now+=10000);
            Trans.Builder b=db.trans();
            for(int j=0;j<1000;j++,next++)
                b.put(String.format("/z/%09d/tail/tail/tail",next),value);
            long before=stats.iterations.isEmpty() ? 0 : stats.iterations.get(0).dirtiedBytes;
            db.execute(b.build());
            maxCallDirtiedBytes=Math.max(maxCallDirtiedBytes,
                stats.iterations.get(0).dirtiedBytes-before);
        }
        Reclaim.Stats.Iteration st=stats.iterations.get(0);
        System.out.println("completed="+rc.getIterationCount()+" appendedKeys="+next
            +" steps="+st.steps+" scanned="+st.kvs+" maxScanNodes="+st.maxStepNodes
            +" maxStepDirtied="+st.maxStepDirtied+" totalDirtiedBytes="+st.dirtiedBytes
            +" maxCallDirtiedBytes="+maxCallDirtiedBytes);
        db.close();
    }
}
