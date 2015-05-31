package bergdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

/**
 * Handles a test run by reporting to a console.
 * 
 * @author Frans Lundberg
 */
public class ConsoleUI implements TestRunConsumer {
    private List<Prop> props = new ArrayList<Prop>();
    protected String currentMethodName = null;
    private List<File> currentTempDirs = new ArrayList<File>();
    protected int total = 0;
    protected int failed = 0;
    protected long nanoTime;
    protected double exeTime;  // Time in sec to execute test method.
    protected double totalExeTime = 0.0;
    protected PrintStream baseOut;
    private PrintStream testOut;
    private Class<?> currentClass;
    
    // verbose levels
    
    private final int LEVEL_SILENT = 0;
    private final int LEVEL_DOTS = 1;
    private final int LEVEL_CLASSES = 2;
    private final int LEVEL_METHODS = 3;
    private final int LEVEL_PROPS = 4;
    private final int LEVEL_MAX = 5;
    private int level;
    
    /**
     * ConsoleIO with default settings.
     */
    public ConsoleUI() {
        this.level = LEVEL_CLASSES;
        this.baseOut = System.out;
        this.testOut = new NullPrintStream();
    }
    
    /**
     * Print only result summary, very silent.
     */
    public ConsoleUI silent() {
        this.level = LEVEL_SILENT;
        this.testOut = new NullPrintStream();
        return this;
    }
    
    /** Prints less than default, just a dot per test. */
    public ConsoleUI dots() {
        this.level = LEVEL_DOTS;
        this.testOut = new NullPrintStream();
        return this;
    }
    
    /** Prints more than default, prints each method name. */
    public ConsoleUI printMethods() {
        this.level = LEVEL_METHODS;
        this.testOut = new NullPrintStream();
        return this;
    }
    
    public ConsoleUI maxVerbose() {
        this.level = LEVEL_MAX;
        this.testOut = baseOut;
        return this;
    }
    
    /**
     * Applies the options from a CommandLine.
     */
    public ConsoleUI applyOptions(CommandLine c) {
        if (c.has("s")) silent();
        if (c.has("dots")) dots();
        if (c.has("d")) dots();
        if (c.has("v")) printMethods();
        if (c.has("vv")) maxVerbose();
        return this;
    }
    
    public void report(String name, Object value) {
        Prop p = new Prop();
        p.name = currentMethodName == null ? name : currentMethodName + "." + name;
        p.value = value;
        props.add(p);
        
        if (level >= LEVEL_PROPS) {
            baseOut.println("* " + p.name + ": " + p.value);
        }
    }

    public void aboutToRun(int classCount) {
    }

    public void done() {
        if (level == LEVEL_DOTS) {
            baseOut.println();
        }
        baseOut.print(this.getReport());
    }
    
    public void classAboutToRun(Class<?> clazz) {
        currentClass = clazz;
        
        if (level > LEVEL_DOTS && level < LEVEL_METHODS) {
            baseOut.print(currentClass.getName() + " ");
        }
    }
    
    public void classDone() {
        if (level == LEVEL_CLASSES) {
            baseOut.println();
        }
    }
    
    public void testAboutToRun(String longMethodName) {
        currentMethodName = longMethodName;
        currentTempDirs.clear();
        
        if (level >= LEVEL_PROPS) {
            baseOut.println("==== " + longMethodName + " ====");
        }
        nanoTime = System.nanoTime();
    }
    
    public void testDone(Throwable t) {
        exeTime = 1e-9 * (System.nanoTime() - nanoTime);
        report("exeTime", exeTime);
        totalExeTime += exeTime;
        deleteTempDirs();
        total++;
        
        if (t == null) {
            // if test OK
            
            if (level > LEVEL_SILENT) {
                if (level >= LEVEL_METHODS) {
                    long rounded = Math.round(exeTime * 1000.0);
                    baseOut.println(currentMethodName + ": " + rounded);    // milliseconds
                } else {
                    baseOut.print(".");
                }
            }
        } else {
            failed++;
            
            Throwable exception = t;
            if (t instanceof java.lang.reflect.InvocationTargetException) {
                exception = t.getCause();
            }
            
            if (level > LEVEL_SILENT) {
                if (currentMethodName == null) {
                    baseOut.println("FAILED!");
                } else {
                    baseOut.println("FAILED! " + currentMethodName);
                }
                
                exception.printStackTrace(baseOut);
            }
        }
    }
    
    protected void deleteTempDirs() {
        for (File dir : currentTempDirs) {
            try {
                delete(dir);
            } catch (IOException e) {
                baseOut.println("Warning: could not delete " + dir.getPath() + ".");
            }
        }
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
    
    public void reportOK() {
        testDone(null);
    }

    public int getTotal() {
        return total;
    }
    
    public int getFailed() {
        return failed;
    }
    
    public double getTotalExeTime() {
        return totalExeTime;
    }
    
    public List<Prop> getProps() {
        return props;
    }
    
    public long getLong(String name) {
        Object obj = getProp(name);
        if (obj instanceof Long) {
            return (Long) obj;
        } else {
            throw new IllegalArgumentException("No such Long prop");
        }
    }
    
    public double getDouble(String name) {
        Object obj = getProp(name);
        if (obj instanceof Double) {
            return (Double) obj;
        } else {
            throw new IllegalArgumentException("No such Double prop");
        }
    }
    
    public Object getProp(String name) {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        for (Prop p : props) {
            if (p.name.equals(name)) {
                return p.value;
            }
        }
        
        return null;
    }
    
    public String getReport() {
        //
        // Because of GCJ problems, String.format and printf are avoided.
        //
        
        String result;
        double rounded = Math.round(10.0 * totalExeTime) / 10.0;
        
        if (failed == 0 && total > 0) {
            result = "RESULT: SUCCESS. " + total + " successful tests in " + rounded + " s.\n";
        } else {
            result = "RESULT: FAILED. Total: " + total + ", failed: " + failed 
                    + ". Time: " + rounded + " s.\n";
        }
        
        return result;
    }
    
    public PrintStream out() {
        return testOut;
    }
    
    /**
     * A named property. Reported in test methods. A list of Props is returned
     * by getProps().
     */
    public static class Prop {
        public String name;
        public Object value;
        
        public String toString() {
            return name + ": " + value;
        }
    }
}
