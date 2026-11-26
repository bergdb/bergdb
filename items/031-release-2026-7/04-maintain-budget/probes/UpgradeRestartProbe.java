package bergdb.core;
import java.util.*;import java.util.concurrent.atomic.AtomicLong;import bergdb.stream.CutStream;
import bergdb.pub.util.Clock;import bergdb.pub.util.SyncLevel;import bergdb.dag.Keys;
/**
 * bergdb 031-04, Codex's review, finding 1: a stream written by main or 2026.6 (UpgradeProbe
 * write), opened twice on the prototype; calls of maintain(100), one a millisecond, on both,
 * and the second copy restarted after each call: the two streams must stay the same (P2).
 *   java -ea -cp out:bergdb.jar bergdb.core.UpgradeRestartProbe FILE
 */
public class UpgradeRestartProbe {
 static String value(Db d,String k){byte[] b=d.getOne(Long.MAX_VALUE,Keys.toSegments("/#i/dreclaim/"+k),d.newGetData());return b==null?"":new String(b);}
 public static void main(String[] args)throws Exception{
  CutStream sa=new CutStream();AtomicLong tm=new AtomicLong();
  try(java.io.DataInputStream in=new java.io.DataInputStream(new java.io.FileInputStream(args[0]))){tm.set(in.readLong());long first=in.readLong();byte[] raw=new byte[in.readInt()];in.readFully(raw);sa.append(new byte[(int)first],0,(int)first);sa.append(raw,0,raw.length);if(first>0)sa.pretruncate(first);}
  Db a=Db.builder().testSetup(sa).clock(tm::get).start();
  a.sync(SyncLevel.ORDINARY);CutStream sb=sa.copy();Db b=Db.builder().testSetup(sb).clock(tm::get).start();
  for(int op=0;op<30;op++){
   tm.addAndGet(Clock.UNITS_PER_SEC/1000);a.maintain(100);b.maintain(100);
   a.sync(SyncLevel.ORDINARY);b.close();sb=sb.copy();b=Db.builder().testSetup(sb).clock(tm::get).start();
   long aa=a.internal().reclaim().appA,ba=b.internal().reclaim().appA;
   System.out.println("call "+op+" A="+aa+" B(restart)="+ba+" tableA="+value(a,"-table.txt").contains("a=")+" currentA="+value(a,"-current.txt").contains("a=")+" lenA="+sa.getLength()+" lenB="+sb.getLength());
   byte[] xa=new byte[(int)(sa.getLength()-sa.getFirstPos())],xb=new byte[(int)(sb.getLength()-sb.getFirstPos())];sa.read(sa.getFirstPos(),xa,0,xa.length);sb.read(sb.getFirstPos(),xb,0,xb.length);
   if(!Arrays.equals(xa,xb)){System.out.println("P2 FAIL after completed call "+op);break;}
  }
  a.close();b.close();
 }
}
