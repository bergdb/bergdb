package frans.bryan;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.TestClock;

import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

public class DbTest
{
  public static void main(String[] args)
    throws Exception
  {
    int id = 0;

    if (args.length == 0) {
        System.out.println("first arg: path-to-db");
        return;
    }
    
    while (true)
    {
      id = runJob(id + 1, args[0]);
      // Orig:
      // Thread.sleep(10000);
      Thread.sleep(100);
    }
  }

  public static int runJob(final int startId, String path)
  {
    final int count = 10000;
    final int lastId = startId + count;
    int currentId = startId;

    // Orig:
    // Database db = Factory.database().create(path).retainDuration(Duration.seconds(10.0)).start();
    Database db = Factory.database().create(path).clock(new TestClock()).start();
    db.setRetainDuration(Duration.seconds(10.0));   // bergdb 015-87: no builder value
    
    Connection conn = db.connection();

    //
    // Iterate existing data...
    //
    List<Integer> list = new ArrayList<Integer>();
    for (Foobar f : conn.usePrimary(Foobar.class).dir("/").objects())
    {
      list.add(f.getId());
    }

    System.out.println(String.format("Iterated: %d items", list.size()));

    //
    // Delete all existing entries...
    //
    for (Integer id : list)
    {
      conn.delete(Foobar.toString(id));
    }

    System.out.println(String.format("Deleted: %d items", list.size()));

    //
    // Create more entries...
    //
    while (currentId < lastId)
    {
      Foobar fb = DbTest.createFoobar(currentId);
      conn.put(fb.toString(), fb);

      ++currentId;
    }

    System.out.println(String.format("Created: %d items", count));

    //
    // Stop the databases.
    //
    db.sync();
    db.stop();

    System.out.println(String.format("SHUTDOWN lastId = %d", lastId));

    return lastId;
  }

  public static Foobar createFoobar(int id)
  {
    UUID uuid = UUID.randomUUID();

    return new Foobar(
      id,
      String.format("FoobarName_%d", id),
      uuid.toString(),
      false,
      true,
      true,
      String.format("This is some pseudo-random data %s %s", id, uuid));
  }
}