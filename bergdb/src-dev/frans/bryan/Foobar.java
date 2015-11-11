package frans.bryan;

public class Foobar
{
  public int id;
  public String name;
  public String uuid;
  public boolean flag1;
  public boolean flag2;
  public boolean flag3;
  public String data;

  public Foobar()
  {
  }

  public Foobar(
    final int id,
    final String name,
    final String uuid,
    final boolean flag1,
    final boolean flag2,
    final boolean flag3,
    final String data)
  {
    this.id = id;
    this.name = name;
    this.uuid = uuid;
    this.flag1 = flag1;
    this.flag2 = flag2;
    this.flag3 = flag3;
    this.data = data;
  }

  public int getId()
  {
    return id;
  }

  public String getName()
  {
    return name;
  }

  public String getUuid()
  {
    return uuid;
  }

  public boolean isFlag1()
  {
    return flag1;
  }

  public boolean isFlag2()
  {
    return flag2;
  }

  public boolean isFlag3()
  {
    return flag3;
  }

  public String getData()
  {
    return data;
  }

  public long toSize()
  {
    return 4 + this.name.length() + uuid.length() +  6 + data.length();
  }

  @Override
  public String toString()
  {
    return Foobar.toStr(this.getId());
  }

  public static String toStr(int id)
  {
    return String.format("/%d", id);
  }
}