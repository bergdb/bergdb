package bergdb.core;

import java.util.*;
import bergdb.dag.*;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/** Follow the identities of nodes holding delete bits after repeated cuts. */
public final class RoutingAge {
    static String key(int n) { return String.format("k%05d", n); }
    static Map<Long, KeyNode> current(Db db) {
        Map<Long, KeyNode> result = new TreeMap<>();
        PointerFollower inner = db.internal().nodeCollection().maintenance();
        GetMany g = db.newGetMany();
        g.gd.pointerFollower = (p,i,op) -> {
            Node n = inner.followPointer(p,i,op);
            if (n instanceof KeyNode) result.put(n.getId(), (KeyNode)n);
            return n;
        };
        db.getMany(g);
        return result;
    }
    public static void main(String[] args) {
        CoreTestClock clock = new CoreTestClock();
        long now = 10 * Clock.UNITS_PER_SEC;
        clock.setTime(now);
        Db db = Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
                .startupDistance(10000).start();
        final int fill = 8192;
        for (int i=0;i<fill;i+=64) {
            clock.setTime(now += 10000);
            Trans.Builder b=db.trans();
            for(int j=i;j<Math.min(fill,i+64);j++) b.put(key(j),new byte[100]);
            db.execute(b.build());
        }
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        int first = args.length > 0 ? Integer.parseInt(args[0]) : 2048;
        int last = args.length > 1 ? Integer.parseInt(args[1]) : 4096;
        for (int i=first;i<last;i+=64) {
            clock.setTime(now += 10000);
            Trans.Builder b=db.trans();
            for(int j=i;j<Math.min(last,i+64);j++) b.delete(key(j));
            db.execute(b.build());
        }
        long deletedAt = db.currentTime();
        Map<Long,KeyNode> candidates = new TreeMap<>();
        for(KeyNode n:current(db).values()) {
            if (n.isSegmentLeaf()) continue;
            long del = n.getDeleteBitmapAtTime(Klong.MAX_TIME,n.getSize());
            boolean deleted=false;
            for(int j=0;j<n.getSize();j++)
                if(Klong.isKey(n.getKlong(j)) && Klong.isDeleted(del,j)) deleted=true;
            if(deleted) candidates.put(n.getId(),n);
        }
        System.out.println("candidates="+candidates.keySet()+" deletedAt="+deletedAt);
        Reclaim rc = db.internal().reclaim();
        long cutCount=0, lastCut=0;
        byte[] drive=new byte[20000];
        for(int i=0;i<(args.length > 2 ? Integer.parseInt(args[2]) : 60000) && !candidates.isEmpty();i++) {
            clock.setTime(now += 100000);
            db.execute(db.trans().put("/a",drive).build());
            long cut=rc.getFirstAvailablePos();
            if(cut != lastCut) {
                cutCount++;
                lastCut=cut;
                Map<Long,KeyNode> c=current(db);
                candidates.keySet().retainAll(c.keySet());
                if(cutCount<=12 || cutCount%10==0 || candidates.isEmpty())
                    System.out.println("cuts="+cutCount+" iterations="+rc.getIterationCount()
                        +" oldNodesStillCurrent="+candidates.keySet()+" dead="
                        +(rc.getFirstAvailableLookupTime()>deletedAt)+" drive="+(i+1));
            }
        }
        System.out.println("keptNew="+Dag.statKeptNew+" originalCandidatesRemaining="+candidates.keySet());
        db.close();
    }
}
