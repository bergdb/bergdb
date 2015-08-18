package bergdb.dev;

import java.lang.instrument.Instrumentation;

import bergdb.dag.KeyNode;
import bergdb.dag.ValueNode;

/**
 * Executable class that prints the JVM memory sizes of different objects.
 * Only used for development purpose.
 * The class must be executed with the "-javaagent:inst.jar" JVM flag.
 * 
 * @author Frans Lundberg
 */
public class ObjectSize {
    private final Instrumentation inst;
    
    public ObjectSize() {
        inst = MyInstrumentation.getInstrumentation();
        if (inst == null) {
            throw new IllegalStateException(
                    "MyInstrumentation.getInstrumentation() returned null. Use -javaagent properly.");
        }
    }
    
    public long getObjectSize(Object o) {
        return inst.getObjectSize(o);
    }
    
    public void go() {
        System.out.println("Object: " + getObjectSize(new Object()));
        System.out.println("KeyNode: " + getObjectSize(new KeyNode()));
        System.out.println("ValueNode (empty): " + getObjectSize(new ValueNode(new byte[0])));
        System.out.println("A: " + getObjectSize(new A()));
        System.out.println("NonStatic: " + getObjectSize(new ObjectSize().new NonStatic()));
        System.out.println("B1: " + getObjectSize(new B1()));
        System.out.println("B4: " + getObjectSize(new B4()));
        System.out.println("B8: " + getObjectSize(new B8()));
        System.out.println("B9: " + getObjectSize(new B9()));
        Booleans b = new Booleans();
        System.out.println("Booleans: " + getObjectSize(b));
        System.out.println("Booleans.field: " + getObjectSize(b.field));
        
        for (int i = 0; i < 16; i++) {
            long size = getObjectSize(new byte[i]);
            long overhead = size - i;
            System.out.println("byte[" + i + "]: " + size + " (" + overhead + ")");
        }
        
        for (int i = 0; i < 8; i++) {
            long size = getObjectSize(new long[i]);
            long overhead = size - 8*i;
            System.out.println("long[" + i + "]: " + size + " (" + overhead + ")");
        }
    }
    
    /**
     * Prints object sizes. Must be run with KissInstrumentation 
     * as "-javaagent".
     */
    public static void main(String[] args) {
        new ObjectSize().go();
    }
    
    public static class A {
    }
    
    public class NonStatic {}
    
    public static class B1 {
        boolean b;
    }
    
    public static class B4 {
        boolean b1, b2, b3, b4;
    }
    
    public static class B8 {
        boolean b1, b2, b3, b4, b5, b6, b7, b8;
    }
    
    public static class B9 {
        boolean b1, b2, b3, b4, b5, b6, b7, b8, b9;
    }
    
    public static class Booleans {
        boolean[] field = new boolean[80];
    }
}

/*

Example output, 140712

$ java -javaagent:out/inst.jar -cp out/bergdb.jar bergdb.dev.ObjectSize
Object: 16
Node: 48
A: 16
NonStatic: 16
B1: 16
B4: 16
B8: 24
B9: 24
Booleans: 16
Booleans.field: 96
byte[0]: 16 (16)
byte[1]: 24 (23)
byte[2]: 24 (22)
byte[3]: 24 (21)
byte[4]: 24 (20)
byte[5]: 24 (19)
byte[6]: 24 (18)
byte[7]: 24 (17)
byte[8]: 24 (16)
byte[9]: 32 (23)
byte[10]: 32 (22)
byte[11]: 32 (21)
byte[12]: 32 (20)
byte[13]: 32 (19)
byte[14]: 32 (18)
byte[15]: 32 (17)
long[0]: 16 (16)
long[1]: 24 (16)
long[2]: 32 (16)
long[3]: 40 (16)
long[4]: 48 (16)
long[5]: 56 (16)
long[6]: 64 (16)
long[7]: 72 (16)

*/
