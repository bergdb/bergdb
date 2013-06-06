package kissdb.common;

/**
 * Implementing class can warn the user.
 */
public interface IWarner {
    public void warn(String message, Throwable t);
}
