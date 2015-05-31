package bergdb.coredev;

import bergdb.common.Create;
import bergdb.common.IPack;

/**
 * This class has a main method used to run the unit tests for the Core BergDB classes.
 * 
 * @author Frans Lundberg
 */
public class CoreUnit {
    
    /**
     * Core classes to be tested.
     */
    private static IPack[] ipacks = new IPack[]{
        new bergdb.common.Pack(),
        new bergdb.core.Pack(),
        new bergdb.stream.Pack()
    };
    
    /**
     * Runs the unit tests (nano tests in group "unit").
     */
    public static void main(String[] args) {
        Nano nano = new Nano(args, ipacks, Create.setOfStrings("unit"));
        nano.go();
    }
}
