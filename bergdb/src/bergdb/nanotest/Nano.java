package bergdb.nanotest;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;
import java.lang.annotation.ElementType;
import java.lang.annotation.RetentionPolicy;

/**
 * Indicates that the annotated method is a Nanotest method.
 * This is optional, any static void method with a name that starts with "test"
 * and takes zero parameters or one TestEnvironment parameter
 * is considered a Nanotest method.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface Nano {
    String value() default "unit";
}
