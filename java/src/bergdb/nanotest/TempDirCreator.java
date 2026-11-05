package bergdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Creator for temporary test directories removed when test ends.
 * 
 * @author Frans Lundberg
 */
public class TempDirCreator {
    private List<File> currentTempDirs = new ArrayList<File>();
    private File tmpDir = null;
    private Random random;
    
    public TempDirCreator() {
        // Sets this.tmpDir if possible.
        
        random = new Random();
        
        // The JVM's temporary directory (bergdb 015-11): its default is /tmp
        // on Linux, and -Djava.io.tmpdir moves it, for example off a small tmpfs.
        String tmpPath = System.getProperty("java.io.tmpdir");
        File tmp = tmpPath == null ? null : new File(tmpPath);
        if (tmp != null && tmp.isDirectory()) {
            File file = new File(tmp, "bergdb-TempDirCreator-" + System.currentTimeMillis() + ".temp");
            file.deleteOnExit();
            
            try {
                file.createNewFile();
                tmpDir = tmp;
            } catch (IOException e) {
                // Empty
            } finally {
                file.delete();
            }
        }
    }
    
    public File createTempDir() throws IOException {
        int randomInt;
        File file;
        
        randomInt = Math.abs(random.nextInt());
        
        if (tmpDir != null) {
            // Using the directory java.io.tmpdir names.
            file = new File(tmpDir, "temp-bergdb-" + randomInt);
        } else {
            // Using current directory
            file = new File("temp-bergdb-" + randomInt);
        }
        assert file != null;
        
        boolean created = file.mkdir();
        if (!created) {
            throw new IOException("Could not create " + file.getPath() + ".");
        }
        
        currentTempDirs.add(file);
        assert file != null;
        return file;
    }
    
    public void deleteTempDirs() {
        for (File dir : currentTempDirs) {
            try {
                delete(dir);
            } catch (IOException e) {
                // Nothing we can do.
            }
        }
        
        currentTempDirs.clear();
    }
    
    /**
     * Deletes a single file or a whole directory, if 'file' is a directory.
     * An IOException is thrown if the file(s) cannot be deleted.
     * If 'file' does not exist, or is 'null' this method returns silently.
     * 
     * @param file The file or directory to delete.
     * @throws IOException 
     */
    private static void delete(File file) throws IOException {
        boolean ok;

        if(file == null) {
            return;
        }
        
        if(!file.exists()) {
            return;
        }
        
        if(file.isDirectory()) {
            File[] files;
            
            files = file.listFiles();
            for(int i=0; i<files.length; i++) {
                delete(files[i]);
            }
            ok = file.delete();
            if(!ok) {
                throw new IOException("Cannot delete file: " + file + ".");
            }
        } else {
            ok = file.delete();
            if(!ok) {
                throw new IOException("Cannot delete file " + file + ".");
            }
        }
    }
    
    // ======== Tests ========
    
    static void test0() throws IOException {
        TempDirCreator c = new TempDirCreator();
        c.createTempDir();
        c.createTempDir();
        c.deleteTempDirs();
    }
    
    /** bergdb 015-11: the directories are made in java.io.tmpdir, not in /tmp. */
    static void testUsesJavaIoTmpdir() throws IOException {
        File tmp = new File(System.getProperty("java.io.tmpdir")).getCanonicalFile();
        TempDirCreator c = new TempDirCreator();
        try {
            File dir = c.createTempDir();
            Assert.assertEquals("the parent of a temporary directory", 
                    tmp.getPath(), dir.getCanonicalFile().getParentFile().getPath());
        } finally {
            c.deleteTempDirs();
        }
    }
}
