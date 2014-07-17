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

/*
The name "T" can be discussed. "T" is often used as a type parameter.
Naming it "Test" is not suitable if one would want to combine nano tests with jUnit 
tests (org.junit.Test annotation). Alternatives: "Nano" / "N" / "Nanotest" for Nano test.
*/
