package kissdb.dev;

import java.io.PrintWriter;

import kissdb.pubimp.IcuInfo;

/**
 * Development tool, print information about the environment. Add info printed when needed.
 * 
 * @author Frans Lundberg
 */
public class Info extends kissdb.coredev.Info {
    /**
     * Entry point for external caller.
     */
    @Override
    public void go(PrintWriter out) {
        super.go(out);
        
        out.println("---- Layer Pub ----");
        out.println(IcuInfo.class.getSimpleName() + ".hasIcu(): " + IcuInfo.hasIcu());
        out.println();
        
        out.flush();
    }
    
    public static void main(String[] args) throws Exception {
        new Info().go(args);
    }
}

/*
130227 Created kissdb.dbdev.Info.
*/