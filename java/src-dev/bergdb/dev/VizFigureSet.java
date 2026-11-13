package bergdb.dev;

import java.io.File;
import java.io.IOException;

import bergdb.core.Db;
import bergdb.core.TestNodeSize;
import bergdb.core.Trans;

/**
 * Executable class to create a set of GraphViz figures from DB graphs.
 * To create SVG files, execute: [dot -Tsvg -O *.gv] in output directory.
 * 
 * @author Frans Lundberg
 */
public class VizFigureSet {
    private File dir;
    
    private String filename(String shortFilename) {
        return new File(dir, shortFilename).getPath();
    }
    
    public void emptyDb() throws IOException {
        Db db = Db.builder().testSetup().start();
        VizFigure f = new VizFigure();
        f.go(db.internal().dag(), filename("emptyDb.gv"), true);
    }
    
    public void oneKv() throws IOException {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("k", "v").build());
        VizFigure f = new VizFigure();
        f.go(db.internal().dag(), filename("oneKv.gv"), true);
    }
    
    public void tenShortInOneTrans() throws IOException {
        Db db = TestNodeSize.builder(8).testSetup().start();
        Trans.Builder b = db.trans();
        for (int i = 0; i < 10; i++) {
            b.put("k" + i, "v" + i);
        }
        db.execute(b.build());
        VizFigure f = new VizFigure();
        f.go(db.internal().dag(), filename("tenShortInOneTrans.gv"), true);
    }
    
    public void tenShortInTenTrans() throws IOException {
        Db db = TestNodeSize.builder(8).testSetup().start();
        for (int i = 0; i < 10; i++) {
            db.execute(db.trans().put("k" + i, "v" + i).build());
        }
        VizFigure f = new VizFigure();
        f.go(db.internal().dag(), filename("tenShortInTenTrans.gv"), true);
    }
    
    public void addedAndDeleted() throws IOException {
        Db db = TestNodeSize.builder(8).testSetup().start();
        db.execute(db.trans().put("a", "v-a").build());
        db.execute(db.trans().delete("a").build());
        VizFigure f = new VizFigure();
        f.go(db.internal().dag(), filename("addedAndDeleted.gv"), true);
    }
    
    public void go(String[] args) throws IOException {
        dir = new File("temp-VizFigureSet");
        if (!dir.exists()) {
            if (!dir.mkdir()) {
                throw new IOException("Could not create " + dir.getPath() + ".");
            }
        }
        
        emptyDb();
        oneKv();
        tenShortInOneTrans();
        tenShortInTenTrans();
        addedAndDeleted();
    }
    
    public static void main(String[] args) throws IOException {
        new VizFigureSet().go(args);
    }
}
