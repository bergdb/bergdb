package bergdb.test.java;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.RandomAccessFile;

import bergdb.nanotest.T;


/**
 * Test possibilities and performance of underlying filesystem.
 * 
 * @author Frans Lundberg
 */
public class Files {

    @T("perf")
    public static void readWriteAndReadOnly() throws IOException {
        //File f = File.createTempFile(this.getClass().getName(), ".temp");
        File f = new File("./Files_temp.data");
        FileOutputStream out = new FileOutputStream(f);
        out.write(123);
        out.flush();
        out.getChannel().force(true);
        
        //FileOutputStream out2 = new FileOutputStream(f);
        //out2.write(124);
        //out2.flush();
        //out2.getChannel().force(true);
        
        RandomAccessFile r = new RandomAccessFile(f, "r");
        r.seek(0);
        //System.out.println(r.read());
        
        out.close();
        r.seek(0);
        //System.out.println(r.read());
        r.close();
        
        //out2.close();
    }
}

/*
$ java -version
java version "1.6.0_06"
Java(TM) SE Runtime Environment (build 1.6.0_06-b02)
Java HotSpot(TM) Client VM (build 10.0-b22, mixed mode, sharing)

Yes, we can have one open file for reading "r" and another for writing
(FileOutputStream) without exceptions.

And, surprisingly, we can have multiple open writers (FileOutputStream)
to the SAME file!
*/
