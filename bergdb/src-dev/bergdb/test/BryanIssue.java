package bergdb.test;

import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import bergdb.core.DagComparison;
import bergdb.core.DbBuilder;
import bergdb.core.DbUtil;
import bergdb.core.TransSeq;
import bergdb.dag.Dag;
import bergdb.dag.DagChecksum;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pubimp.DatabaseBuilderImp;
import bergdb.pubimp.DatabaseImp;
import bergdb.stream.MemoryStream;

/**
 * ISSUE151111, reported by Bryan (e-mail address removed).
 * This code is inspired by code in his bug report; thank you!
 * 
 * @author Frans Lundberg
 */
public class BryanIssue {
    protected PrintStream out;
    protected MemoryStream memoryStream;
    protected TestEnvironment env;
    protected Dag prevDag;
    protected TransSeq prevTransSeq;
    
    @Nano("f")
    private static void testIt(TestEnvironment env) throws Exception {
        new BryanIssue(env).go();
    }
    
    public BryanIssue(TestEnvironment env) {
        this.env = env;
        this.out = env.out();
        this.memoryStream = new MemoryStream();
        this.prevDag = null;
    }

    private void go() throws Exception {
        int id = 0;
        
        for (int i = 0; i < 6; i++) {
            id = runJob(id + 1);
            memoryStream = memoryStream.copy();
        }
    }
    
    public void initDb(DatabaseBuilder builder) throws IOException {
        DbBuilder b = ((DatabaseBuilderImp) builder).getDbBuilder();
        b.mainStream(memoryStream);
        b.testSetupExceptStream();
        b.retainForever();
    }   

    public int runJob(final int startId) throws Exception {
        final int n = 1000;        
        final int lastId = startId + n;
        int currentId = startId;
        
        DatabaseBuilder builder = Factory.database();
        initDb(builder);
        
        Database d = builder.start();
        try {
            out.format("\n---- STARTED ----\n");
            out.println(String.format("Db checksum: %d", dbChecksum(d)));
            out.println(String.format("Dag checksum: %d", dagChecksum(d)));
            compareDags(d);
            compareTransSeqs(d);
            
            Connection c = d.connection();
            
            out.println("db time: " + c.currentTime().units());
    
            // Iterates existing data
            List<Integer> list = new ArrayList<Integer>();
            for (Dummy f : c.usePrimary(Dummy.class).objects()) {
                list.add(f.id);
            }
            out.println(String.format("Iterated: %d items", list.size()));
    
            // Deletes existing entries
            for (Integer id : list) {
                c.delete(toKey(id));
            }
            out.println(String.format("Deleted: %d items", list.size()));
    
            // Creates more entries
            while (currentId < lastId) {
                Dummy f = createDummy(currentId);
                c.put(toKey(f.id), f);
                currentId++;
            }
            d.sync();
            out.println(String.format("Created: %d items", n));
            out.println("---- Before stop():");
            out.println(String.format("Db checksum: %d", dbChecksum(d)));
            out.println(String.format("Dag checksum: %d", dagChecksum(d)));
        } finally {
            d.stop();
            out.println(String.format("STOP lastId = %d", lastId));
        }

        return lastId;
    }
    
    private long dbChecksum(Database d) {
        return DbUtil.checksum(((DatabaseImp) d).getDb());
    }
    
    private long dagChecksum(Database d) {
        Dag dag = ((DatabaseImp) d).getDb().internal().dag();
        return new DagChecksum(dag).compute();
    }
    
    private void compareDags(Database d) {
        Dag dag = ((DatabaseImp) d).getDb().internal().dag();
        
        if (prevDag != null) {
            DagComparison comp = new DagComparison(prevDag, dag);
            boolean equal = comp.compare();
            if (equal) {
                out.println("Restarted dag compared equal to prevDag");
                
                long c1 = new DagChecksum(prevDag).compute();
                long c2 = new DagChecksum(dag).compute();
                out.println("  dag checksums: " + c1 + ", " + c2);
                
            } else {
                out.println("WARNING: Restarted dag NOT equal to prevDag");
            }
        }
        
        prevDag = dag;
    }
    
    private void compareTransSeqs(Database d) {
        TransSeq seq = ((DatabaseImp) d).getDb().internal().transSeq();
        
        if (prevTransSeq != null) {
            long c1 = prevTransSeq.checksum();
            long c2 = seq.checksum();
            
            if (c1 == c2) {
                out.println("Restarted TransSeq checksum equal to prev");
            } else {
                out.println("WARNING: Restarted TransSeq NOT equal to prevTransSeq");
            }
            
            out.println("  TransSeq checksums: " + c1 + ", " + c2);
        }
        
        prevTransSeq = seq;
    }
    
    public static String toKey(int id) {
        return String.format("/%d", id);
    }
    
    public static Dummy createDummy(int id) {
        Dummy d = new Dummy();
        d.id = id;
        d.data = new byte[20*1000];
        return d;
    }
    
    public static class Dummy {
        public int id;
        public byte[] data;
    }
}

/*

151115
======

Does not depende on startup distance 10M and 1000M gives same result: 
    bergdb.storage.StreamFormatException: unknown node type, 0, spos: 20119641, node header bytes: 0000000200000094

What we know:
* Happens when stream bigger than startup distance.
* Always a vpos (odd spos).
* Could not reduce to less than 3 db startups.
* Does not depend on evict.
* The followPointer when exception is thrown is from a vpos KeyNode to a vpos node.
* Happens at db startup (DbStarter.rerunTransactions() included in stack).

*/