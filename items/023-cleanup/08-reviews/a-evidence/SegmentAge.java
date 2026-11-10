package bergdb.core;

import java.util.*;
import bergdb.dag.*;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/** An old delete in the first leaf of a long key's segment chain. */
public final class SegmentAge {
    public static void main(String[] args) {
        CoreTestClock clock=new CoreTestClock();
        long now=10*Clock.UNITS_PER_SEC;
        clock.setTime(now);
        Db db=Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
            .startupDistance(10000).start();
        String prefix="coldpre";
        String live=prefix+"abcdefg".repeat(12)+"tail";
        String deleted=prefix+"abc";
        db.execute(db.trans().put(live,"live").put(deleted,"gone").build());
        clock.setTime(now+=10000);
        db.execute(db.trans().delete(deleted).build());
        long ended=db.currentTime();
        Set<Long> original=new TreeSet<>();
        for(KeyNode n:RoutingAge.current(db).values()) {
            long del=n.getDeleteBitmapAtTime(Klong.MAX_TIME,n.getSize());
            for(int i=0;i<n.getSize();i++)
                if(Klong.isKey(n.getKlong(i)) && Klong.isDeleted(del,i)) original.add(n.getId());
        }
        System.out.println("deletedAt="+ended+" candidates="+original+" longBytes="+live.length());
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        long lastCut=0,cuts=0;
        for(int i=0;i<20000;i++) {
            clock.setTime(now+=100000);
            db.execute(db.trans().put("/a",new byte[20000]).build());
            long cut=db.getFirstAvailablePos();
            if(cut>lastCut) {
                lastCut=cut; cuts++;
                if(cuts%100==0) {
                    Set<Long> still=new TreeSet<>(original);
                    still.retainAll(RoutingAge.current(db).keySet());
                    System.out.println("cuts="+cuts+" oldDeleteNodes="+still
                        +" firstTime="+db.getFirstAvailableLookupTime()+" dead="
                        +(db.getFirstAvailableLookupTime()>ended));
                }
            }
        }
        GetData gd=db.newGetData();
        System.out.println("live="+new String(db.getOne(Long.MAX_VALUE,Keys.toSegments(live),gd))
            +" deleted="+db.getOne(Long.MAX_VALUE,Keys.toSegments(deleted),db.newGetData())
            +" keptNew="+Dag.statKeptNew);
        db.close();
    }
}
