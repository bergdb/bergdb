package bergdb.core;

import java.lang.reflect.Field;
import java.util.HashMap;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/** The cache's backing arrays, which resident-node counts do not include. */
public final class CacheCapacity {
    static Field mapsField, tableField;
    static String key(int n) { return String.format("%07d/a",n); }
    static long slots(Db db) throws Exception {
        long slots=0;
        Object[] maps=(Object[])mapsField.get(db.internal().cache());
        for(Object map:maps) {
            Object[] table=(Object[])tableField.get(map);
            if(table!=null) slots+=table.length;
        }
        return slots;
    }
    static void show(String where, Db db) throws Exception {
        System.out.println(where+" resident="+db.internal().cache().residents().objects()
            +" handles="+db.internal().cache().handles().size()+" slots="+slots(db)
            +" first="+db.getFirstAvailablePos()+" firstTime="+db.getFirstAvailableLookupTime()
            +" now="+db.currentTime()+" length="+db.getStreamLength());
    }
    public static void main(String[] args) throws Exception {
        mapsField=Cache3.class.getDeclaredField("maps"); mapsField.setAccessible(true);
        tableField=HashMap.class.getDeclaredField("table"); tableField.setAccessible(true);
        CoreTestClock clock=new CoreTestClock();
        long now=10*Clock.UNITS_PER_SEC;
        clock.setTime(now);
        Db db=Db.builder().testSetup(new CutStream()).clock(clock).startupDistance(100000)
            .cacheSizeIndicator(1000000000).start();
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        int count=args.length==0?100000:Integer.parseInt(args[0]);
        db.execute(db.trans().put("/a","live").build());
        for(int i=0;i<count;i+=100) {
            clock.setTime(now+=10000);
            Trans.Builder b=db.trans();
            for(int j=i;j<Math.min(count,i+100);j++) b.put(key(j),new byte[10]);
            db.execute(b.build());
        }
        show("filled",db);
        for(int i=0;i<count;i+=100) {
            clock.setTime(now+=10000);
            Trans.Builder b=db.trans();
            for(int j=i;j<Math.min(count,i+100);j++) b.delete(key(j));
            db.execute(b.build());
        }
        for(int i=0;i<12000;i++) {
            clock.setTime(now+=10000);
            db.execute(db.trans().put("/a",new byte[1000]).build());
        }
        show("after-drive",db);
        db.close();
    }
}
