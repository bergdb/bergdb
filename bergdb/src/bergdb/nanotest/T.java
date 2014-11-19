package bergdb.nanotest;

import java.lang.annotation.*;

// TODO C. Should we even use this annotation? Not really required, is it?
// TODO C. Should we have @NotNano annotation. For static void testXxx methods 
// that are NOT Nano tests. Or @NotNano?

/**
 * Indicates that the annotated method is a Nanotest method.
 * This is optional, any static void method with a name that starts with "test"
 * and takes zero or one param with a TestEnvironment param is considered a Nanotest method.
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
