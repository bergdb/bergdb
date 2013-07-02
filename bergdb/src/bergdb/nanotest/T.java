package bergdb.nanotest;

import java.lang.annotation.*;

/**
 * Indicates that the annotated method is a Nanotest method.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.METHOD)
public @interface T {
    String value() default "unit";
}
