package bergdb.dev;

/*

TODO Consider if we could make rw-transactions composable? How to make
two payments and a log entry in one transaction using the single-payment 
+ new log entry code?
Key is RwEnvironment and WBuilder. Should we have WriteInterface as common interface?

TODO X LATER Consider how bergdb.storage could be made independent of bergdb.pub.
bergdb.shared? bergdb.pub.shared? Shared between pub and lower-level code.
Only interfaces and exceptions should be there, no real implementation - just interface stuff
needed to quickly share things without the need for pubimp to convert everything.
Would be a bit tedious to replace every exception thrown from core in pubimp.

*/

/**
 * Dummy class for development notes. todo, note, xxx capitalized.
 * 
 * @author Frans Lundberg
 */
public class DummyForNotes {}
