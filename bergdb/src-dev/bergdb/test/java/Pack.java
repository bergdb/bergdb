package bergdb.test.java;

import bergdb.nanotest.IPack;

/**
 * Information about this package.
 */
public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        AllocateByteBuffer.class,
        ArrayVsHash.class,
        AtomicVsLockVsVolatileCounters.class,
        BytesToByteBuffer.class,
        BytesToLong.class,
        ChecksumPerf.class,
        Ciphers.class,
        CloneArray.class,
        CopyBytes.class,
        Environment.class,
        Files.class,
        FileSystemCache.class,
        Hash.class,
        JudyNode.class,
        JudyNode.Tester.class,
        JudyPerf.class,
        MacPerf.class,
        MemoryOfLongVsCustomClass.class,
        MethodCalls.class,
        NioBuffer.class,
        ObjectMemory.class,
        Pack.class,
        ParseIntegers.class,
        RandomPerf.class,
        ReadFromByteBuffer.class,
        Reflection.class,
        SecureHash.class,
        StringHash.class,
        StringMemory.class,
        SystemClock.class,
        Zip.class,
        ZipDeltaInts.class,
        ZipObject.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
