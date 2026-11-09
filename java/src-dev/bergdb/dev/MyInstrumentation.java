package bergdb.dev;

import java.lang.instrument.Instrumentation;

/**
 * Used for intrumentation.
 * Inspired by http://stackoverflow.com/questions/52353/in-java-what-is-the-best-way-to-determine-the-size-of-an-object.
 * 
 * @see ObjectSize
 * @author Frans Lundberg
 */
public class MyInstrumentation {
    // Note: Class name was used in build.xml (gone since 2026.4).
    
    private static Instrumentation inst;

    public static void premain(String args, Instrumentation inst) {
        MyInstrumentation.inst = inst;
    }
    
    public static Instrumentation getInstrumentation() {
        return inst;
    }
}

/*
This class must be put into a jar (inst.jar) with MANIFEST.MF containing:

    Premain-Class: bergdb.dev.MyInstrumentation

Then run instrumented application like this:

    java -javaagent:inst.jar ...
*/