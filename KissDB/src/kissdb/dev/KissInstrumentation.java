package kissdb.dev;

import java.lang.instrument.Instrumentation;

/**
 * Used for intrumentation.
 * Inspired by http://stackoverflow.com/questions/52353/in-java-what-is-the-best-way-to-determine-the-size-of-an-object.
 * 
 * @see ObjectSize
 * @author Frans Lundberg
 */
public class KissInstrumentation {
    private static Instrumentation inst;

    public static void premain(String args, Instrumentation inst) {
        KissInstrumentation.inst = inst;
    }
    
    public static Instrumentation getInstrumentation() {
        return inst;
    }
}

/*
This class must be put into a jar (inst.jar) with MANIFEST.MF containing:

    Premain-Class: com.kissdb.dev.KissInstrumentation

Then run instrumented application like this:

    java -javaagent:inst.jar ...
*/