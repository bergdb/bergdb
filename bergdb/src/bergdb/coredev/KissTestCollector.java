package bergdb.coredev;

import bergdb.nanotest.BasicCollector;

/**
 * A test result collector designed for KissDB unit tests.
 * 
 * @author Frans Lundberg
 */
public class KissTestCollector extends BasicCollector {
    private int classCount = 0;
    private Class<?> currentClass;
    private boolean firstTestOfClass;
    private static final int SLOW_LIMIT = 500;   // ms limit, if exceeded print time
    
    public KissTestCollector() {
        super();
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
            if (printMethods) {
                long rounded = Math.round(exeTime * 1000.0);
                /*String shortMethodName = currentMethodName;
                int dotIndex = currentMethodName.lastIndexOf('.');
                if (dotIndex > 0 && dotIndex < currentMethodName.length() - 1) {
                    shortMethodName = currentMethodName.substring(dotIndex + 1);
                }*/
                
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
