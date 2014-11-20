package bergdb.coredev;

import bergdb.nanotest.ConsoleUI;

/**
 * A test run consumer designed for BergDB unit tests.
 * 
 * @author Frans Lundberg
 */
public class BergDBTestRunConsumer extends ConsoleUI {
    private int classCount = 0;
    private Class<?> currentClass;
    private boolean firstTestOfClass;
    private static final int SLOW_LIMIT = 500;   // ms limit, if exceeded print time
    
    public BergDBTestRunConsumer() {
        super(ConsoleUI.builder().printProps(false).printMethods(false));
    }
    
    public void setClassCount(int classCount) {
        this.classCount = classCount;
    }
    
    public void classAboutToRun(Class<?> clazz) {
        currentClass = clazz;
        firstTestOfClass = true;
    }
    
    public void classDone() {
        if (!firstTestOfClass) {
            baseOut.println();
        }
    }
    
    public void testDone(Throwable t) {
        exeTime = 1e-9 * (System.nanoTime() - nanoTime);
        report("exeTime", exeTime);
        totalExeTime += exeTime;
        deleteTempDirs();
        total++;
        boolean manyClasses = classCount > 10;
        
        if (firstTestOfClass && manyClasses) {
            baseOut.print(currentClass.getName() + " ");
            firstTestOfClass = false;
        }
        
        if (t == null) {
            
            // if test OK
            if (getPrintMethods()) {
                long rounded = Math.round(exeTime * 1000.0);
                
                if (manyClasses) {
                    if (rounded > SLOW_LIMIT) {
                        baseOut.print("(" + rounded + ")");
                    } else {
                        baseOut.print(".");
                    }
                } else {
                    baseOut.println(currentMethodName + ": " + rounded);    // milliseconds
                }
            }
        } else {
            failed++;
            
            Throwable exception = t;
            if (t instanceof java.lang.reflect.InvocationTargetException) {
                exception = t.getCause();
            }
            
            baseOut.println("\nFAILED! " + currentMethodName);
            exception.printStackTrace(baseOut);
        }
    }
}
