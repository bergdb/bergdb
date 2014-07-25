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
    public static final int releaseInt = Util.identity(141);
    
    /**
     * BergDB version ID, for example "2013.2".
     */
    public static final String release = Util.identity("2014.1");
    
    /**
     * BergDB build ID, for example "2013.2.130401.1400".
     */
    public static final String build = Util.identity("2014.1.140725.1026");
    
    /**
     * Prints build information to System.out.
     */
    public static void main(String[] args) {
        System.out.println("release: " + release);
        System.out.println("releaseInt: " + releaseInt);
        System.out.println("build: " + build);
    }
}

/*
Use like the following in ANT build script:

<copy file="p/bergdb/in/BuildInfoTemplate.txt" 
        toFile="p/bergdb/src/bergdb/db/BuildInfo.java"
        overwrite="true">
    <filterset begintoken="{{" endtoken="}}">
        <filter token="time" value="${time}"/>
        ...
    </filterset>
</copy>
*/
