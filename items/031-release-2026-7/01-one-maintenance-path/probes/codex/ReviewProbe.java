package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import java.lang.reflect.Field;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.dag.Keys;

/** Independent review probes. Only snapshots are crashed; production sources unchanged. */
public class ReviewProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final AtomicLong time = new AtomicLong(SEC);
    static final Clock clock = time::get;
    static final String BIG = "/zz/big";
    static final Field tableF, rowsF;
    static {
        try {
            tableF = Reclaim.class.getDeclaredField("table"); tableF.setAccessible(true);
            rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
            rowsF.setAccessible(true);
        } catch (Exception ex) { throw new RuntimeException(ex); }
    }
    @SuppressWarnings("unchecked")
    static List<Reclaim.IterationInfo> rows(Db d) throws Exception {
        return (List<Reclaim.IterationInfo>) rowsF.get(tableF.get(d.internal().reclaim()));
    }
    static Reclaim.IterationInfo last(Db d) throws Exception {
        List<Reclaim.IterationInfo> r = rows(d);
        return r.isEmpty() ? null : r.get(r.size()-1);
    }
    static Db start(CutStream s) { return Db.builder().testSetup(s).clock(clock).start(); }
    static void tick() { time.addAndGet(MS); }
    static void exec(Db d, Trans.Builder b) { tick(); d.execute(b.build()); }
    static void drive(Db d, int n) { for (int i=0;i<n;i++) { tick(); d.maintain(); } }
    static void state(String label, Db d) throws Exception {
        Reclaim r=d.internal().reclaim(); Reclaim.IterationInfo it=last(d);
        System.out.println(label+": length="+d.getStreamLength()+" fp="+d.getFirstAvailablePos()
            +" w="+r.appW+" stored="+r.appWStored+" last="+(it==null ? "none" :
              it.pStart+" rewritten="+it.rewritten+" done="+it.done+" cut="+it.cut));
    }
    static final class Snap implements Db.TestHooks {
        final Db db; final CutStream stream; CutStream copy; long tt, pos, next;
        boolean stop;
        Snap(Db d, CutStream s) { db=d; stream=s; }
        public void transExecuted(Db.ExecuteData x) {
            if (x.trans.isInternal() || next!=0) return;
            tt=x.trans.tt; pos=x.trans.tpos; next=x.trans.nextPos;
            if (stop) db.stop();
        }
        void finish() {
            if (stop) db.close(); else db.sync(SyncLevel.ORDINARY);
            copy=stream.copy(); copy.truncate(next);
        }
        public void valueNodeCreated(ValueNode n,long[] k) {}
        public void nodeTouched(Node n) {}
        public void nodeReplaced(Node n) {}
    }
    static void recovery(String variant) throws Exception {
        CutStream s=new CutStream(); Db d=start(s);
        d.setStartupDistance(1000000); d.setRetainDuration(SEC);
        // Two large live values make rewrites large; the later puts make multiple epochs.
        for (int round=0;round<6;round++) {
            exec(d,d.trans().put(BIG,new byte[1500000]));
            exec(d,d.trans().put("/aa/big",new byte[1500000]));
            time.addAndGet(SEC/3);
            drive(d,5);
        }
        drive(d,20000); state("quiet base",d);
        Snap snap=new Snap(d,s); snap.stop=variant.equals("stop"); Db.testHooks=snap;
        exec(d,d.trans().delete(BIG).delete("/aa/big"));
        Db.testHooks=null; snap.finish();
        state("uninterrupted delete",d);
        CutStream trustedStream=snap.copy.copy(); Db trusted=start(trustedStream);
        Db recovered=start(snap.copy);
        state("first recovery",recovered);
        long expected=recovered.internal().reclaim().appW;
        CutStream second;
        if (variant.equals("empty")) {
            Snap next=new Snap(recovered,snap.copy); Db.testHooks=next;
            exec(recovered,recovered.trans()); Db.testHooks=null; next.finish();
            state("after empty transaction",recovered);
            second=next.copy; recovered.close();
        } else {
            tick(); recovered.setRetainDuration(2*SEC); trusted.setRetainDuration(2*SEC);
            state("after setter",recovered);
            recovered.close(); second=snap.copy.copy();
        }
        recovered=start(second); state("second recovery",recovered);
        for(String key:new String[]{BIG,"/aa/big"}) {
            if(recovered.getOne(Long.MAX_VALUE,Keys.toSegments(key),recovered.newGetData())!=null)
                throw new AssertionError("delete was not recovered");
        }
        System.out.println("w lost="+(expected!=recovered.internal().reclaim().appW));
        long len=recovered.getStreamLength();
        for(int i=0;i<100000;i++) { tick(); recovered.maintain(); trusted.maintain(); }
        state("empty after 100 seconds",recovered);
        state("same recovered prefix, no extra restart",trusted);
        System.out.println("written after second recovery="+(recovered.getStreamLength()-len));
        if (!snap.stop) { drive(d,50000); state("uninterrupted empty",d); }
        recovered.close(); trusted.close(); d.close();
    }
    static void crashBytes() throws Exception {
        CutStream s=new CutStream(); Db a=start(s);
        a.setStartupDistance(10000); a.setRetainDuration(SEC);
        // First iteration begins, followed by first app record which changes w.
        exec(a,a.trans().put("/a",new byte[50000]));
        state("before snapshot",a);
        Snap snap=new Snap(a,s); Db.testHooks=snap;
        exec(a,a.trans().put("/b",new byte[100])); Db.testHooks=null; snap.finish();
        a.sync(SyncLevel.ORDINARY);
        Db b=start(snap.copy); state("crash reopened",b);
        time.addAndGet(SEC);
        exec(a,a.trans().put("/c",new byte[100]));
        // Same accepted user transaction, at exactly the same test-clock time.
        b.execute(b.trans().put("/c",new byte[100]).build());
        a.sync(SyncLevel.ORDINARY); b.sync(SyncLevel.ORDINARY);
        state("uninterrupted result",a); state("crashed result",b);
        byte[] x=new byte[(int)s.getLength()], y=new byte[(int)snap.copy.getLength()];
        s.read(0,x,0,x.length); snap.copy.read(0,y,0,y.length);
        int at=0; while(at<Math.min(x.length,y.length)&&x[at]==y[at]) at++;
        System.out.println("same bytes="+Arrays.equals(x,y)+" first difference="+at
            +" captured user record="+snap.pos+" tt="+snap.tt);
        a.close(); b.close();
    }
    static void small(int n,int valueSize,int sd) throws Exception {
        CutStream s=new CutStream(); Db d=start(s);
        d.setStartupDistance(sd); d.setRetainDuration(SEC);
        for(int round=0;round<10;round++) for(int i=0;i<n;i+=100) {
            Trans.Builder tx=d.trans();
            for(int k=i;k<Math.min(n,i+100);k++) tx.put("/k/"+k,new byte[valueSize]);
            time.addAndGet(SEC/100); d.execute(tx.build());
        }
        drive(d,20000); state("small live quiet",d);
        for(int i=0;i<n;i+=100) {
            Trans.Builder tx=d.trans();
            for(int k=i;k<Math.min(n,i+100);k++) tx.delete("/k/"+k);
            exec(d,tx);
        }
        drive(d,20000); state("small empty",d);
        long len=d.getStreamLength(); drive(d,20000);
        System.out.println("extra writes="+(d.getStreamLength()-len)
            +" kept="+(d.getStreamLength()-d.getFirstAvailablePos()));
        d.close();
    }
    public static void main(String[] args) throws Exception {
        switch(args[0]) {
            case "recovery": recovery(args.length>1?args[1]:"setter"); break;
            case "bytes": crashBytes(); break;
            case "small": small(Integer.parseInt(args[1]),Integer.parseInt(args[2]),Integer.parseInt(args[3])); break;
            default: throw new IllegalArgumentException(args[0]);
        }
    }
}
