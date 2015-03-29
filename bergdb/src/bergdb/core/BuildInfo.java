package bergdb.core;

import bergdb.common.Util;

/**
 * Information about the build. BuildInfoTemplate.txt is a source code template for the 
 * generated file BuildInfo.java. Do not edit BuildInfo.java.
 * 
 * @author Frans Lundberg
 */
public class BuildInfo {
    // Note, Util.identity() used to avoid compiler inlining.
    
    private BuildInfo() {}
    
    /**
     * BergDB release int, for example "132".
     */
    public static final int RELEASE_INT = Util.identity(152);
    
    /**
     * BergDB version ID, for example "2013.2".
     */
    public static final String RELEASE = Util.identity("2015.2");
    
    /**
     * BergDB build ID, for example "2013.2.130401.1400".
     */
    public static final String BUILD = Util.identity("2015.2.150329.0021");
    
    /**
     * Prints build information to System.out.
     */
    public static void main(String[] args) {
        System.out.println("release: " + RELEASE);
        System.out.println("releaseInt: " + RELEASE_INT);
        System.out.println("build: " + BUILD);
    }
}

/*
Use something like the following in ANT build script:

<copy file="p/bergdb/in/BuildInfoTemplate.txt" 
        toFile="p/bergdb/src/bergdb/db/BuildInfo.java"
        overwrite="true">
    <filterset begintoken="{{" endtoken="}}">
        <filter token="time" value="${time}"/>
        ...
    </filterset>
</copy>
*/
