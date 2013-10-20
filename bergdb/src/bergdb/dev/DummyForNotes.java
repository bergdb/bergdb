package bergdb.dev;

/*

TODO B. Have special classes for ReadSync and WriteLock. Good for debug (monitoring 
with jvisualvm).

TODO C. Fix waitForD1(), waitForD2(), .sync() naming. Available from where?
Database or Connection or both?
Call them sync() and syncHard()? sync()/syncExtra(), sync(), sync()/sync2() (also sync1() == sync())
Allows for sync3() to be added. sync()/sync1() is used for "sync level 1". sync2() is called
to use "sync level 2".
sync() / syncStrong(). Allows for addition of syncStrongest(). Levels: ORDINARY / STRONG / STRONGEST.

TODO D. Consider if we could make rw-transactions composable? How to make
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
