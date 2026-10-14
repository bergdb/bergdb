package bergdb.stream;

/**
 * Deterministic power-loss recovery at the production FileStream persistence
 * boundaries. java -ea -Xmx2g -cp build/bergdb.jar:build/stress
 * bergdb.stream.PowerLossTest [firstSeed [rounds [transactions [perEvent]]]]
 * Loss of unforced bytes/names can coexist with surviving prefix deletion.
 * These are fault-model tests, not a claim of physical power cycling.
 */
public class PowerLossTest {
    public static void main(String[] args) throws Exception {
        int first = args.length > 0 ? Integer.parseInt(args[0]) : 1;
        int rounds = args.length > 1 ? Integer.parseInt(args[1]) : 8;
        int transactions = args.length > 2 ? Integer.parseInt(args[2]) : 1500;
        int perEvent = args.length > 3 ? Integer.parseInt(args[3]) : 3;
        int checked = 0;
        for (int i = first; i < first + rounds; i++) {
            checked += FileStreamPowerLossTester.runTrace(i, transactions, perEvent, false, false, false);
        }
        FileStreamPowerLossTester.testWeakenedForceOrderingIsDetected();
        System.out.println("POWERLOSS OK: " + rounds + " seeds, " + checked + " cold recoveries; negative controls caught");
    }
}
