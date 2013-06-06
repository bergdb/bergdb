package kissdb.core;

import kissdb.common.Util;

/**
 * Information about the build. BuildInfoTemplate.txt is a source code template for the 
 * generated file BuildInfo.java. Do not edit BuildInfo.java.
 * 
 * @author Frans Lundberg
 */
public class BuildInfo {
    // Note, Util.identity() used to avoid compiler inlining.
    
    /**
     * KissDB version, pattern yyyy.n. yyyy = release year (major version number), 
     * n = release number for the year (minor version number).
     * For example: "2013.2".
     */
    public static final String version = Util.identity("2013.1");
    
    /**
     * KissDB version int, for example "132".
     */
    public static final int versionInt = Util.identity(131);
    
    /**
     * KissDB version ID, for example "2013.2.130401".
     */
    public static final String release = Util.identity("2013.1.130606");
    
    /**
     * KissDB build ID, for example "2013.2.130401.1400".
     */
    public static final String build = Util.identity("2013.1.130606.2336");
    
    /**
     * Prints build information to System.out.
     */
    public static void main(String[] args) {
        System.out.println("version: " + version);
        System.out.println("versionInt: " + versionInt);
        System.out.println("release: " + release);
        System.out.println("build: " + build);
    }
}

/*
Use like the following in ANT build script:

<copy file="p/KissDB/in/BuildInfoTemplate.txt" 
        toFile="p/KissDB/src/kissdb/db/BuildInfo.java"
        overwrite="true">
    <filterset begintoken="{{" endtoken="}}">
        <filter token="time" value="${time}"/>
        ...
    </filterset>
</copy>
*/
