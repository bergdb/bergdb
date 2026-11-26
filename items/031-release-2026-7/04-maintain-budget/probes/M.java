package bergdb.core;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * bergdb 031-04's shim, so that one probe runs on main and on the prototype: a call is
 * maintain(B) on the prototype (B from -Dbudget, 100 by default), maintain() on main. In
 * package bergdb.core; compiled with the probes against either jar.
 */
final class M {
    static final int B = Integer.getInteger("budget", 100);
    static final Method BUDGETED = method("maintain", int.class), PLAIN = method("maintain");
    static final boolean MAIN = BUDGETED == null;

    private M() {}

    private static Method method(String name, Class<?>... types) {
        try {
            return Db.class.getMethod(name, types);
        } catch (NoSuchMethodException e) {
            return null;
        }
    }

    /** One call; true if it wrote, or on main if it returned true. */
    static boolean call(Db d) {
        return call(d, B);
    }

    /** One call with the budget b (ignored on main). */
    static boolean call(Db d, int b) {
        final long l = d.getStreamLength();
        try {
            if (BUDGETED != null) {
                BUDGETED.invoke(d, b);
                return d.getStreamLength() != l;
            }
            return (Boolean) PLAIN.invoke(d) || d.getStreamLength() != l;
        } catch (InvocationTargetException e) {
            if (e.getCause() instanceof RuntimeException) throw (RuntimeException) e.getCause();
            if (e.getCause() instanceof Error) throw (Error) e.getCause();
            throw new RuntimeException(e.getCause());
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    /** a (bergdb 031-04), w (031-03), or Long.MIN_VALUE on main. */
    static long appW(Db d) {
        try {
            return Reclaim.class.getDeclaredField("appA").getLong(d.internal().reclaim());
        } catch (ReflectiveOperationException e) {
            // main, or 031-03
        }
        try {
            return Reclaim.class.getDeclaredField("appW").getLong(d.internal().reclaim());
        } catch (ReflectiveOperationException e) {
            return Long.MIN_VALUE;
        }
    }
}
