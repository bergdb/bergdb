package bergdb.core;

/**
 * Deterministic power-loss recovery at the production FileStream persistence
 * boundaries. java -ea -Xmx2g -cp build/bergdb.jar:build/stress
 * bergdb.core.PowerLossTest [firstSeed [rounds [transactions [perEvent]]]]
 * Loss of unforced bytes/names can coexist with surviving prefix deletion.
 * These are fault-model tests, not a claim of physical power cycling.
 * Each seed runs twice: with per-append forces, and without them (bergdb 005-47), where the
 * hole images are counted, not failed, a known limit (bergdb 014-01).
 */
public class PowerLossTest {
    public static void main(String[] args) throws Exception {
        int first = args.length > 0 ? Integer.parseInt(args[0]) : 1;
        int rounds = args.length > 1 ? Integer.parseInt(args[1]) : 8;
        int transactions = args.length > 2 ? Integer.parseInt(args[2]) : 1500;
        int perEvent = args.length > 3 ? Integer.parseInt(args[3]) : 3;
        int checked = 0, checkedOff = 0, holesRecovered = 0, holesFailed = 0;
        for (int i = first; i < first + rounds; i++) {
            checked += FileStreamPowerLossTester.runTrace(i, transactions, perEvent, false, false, false);
            int[] off = FileStreamPowerLossTester.runTraceWithoutAppendForces(i, transactions, 
                    perEvent, null, false);
            checkedOff += off[0];
            holesRecovered += off[1];
            holesFailed += off[2];
        }
        FileStreamPowerLossTester.testWeakenedForceOrderingIsDetected();
        FileStreamPowerLossTester.testWeakenedForcesWithoutAppendForcesAreDetected();
        System.out.println("POWERLOSS OK: " + rounds + " seeds, " + checked + " cold recoveries; "
                + "without per-append forces " + checkedOff + ", and of " + (holesRecovered + holesFailed)
                + " hole images " + holesRecovered + " recovered, " + holesFailed 
                + " failed (a known limit, bergdb 014-01); negative controls caught");
    }
}
