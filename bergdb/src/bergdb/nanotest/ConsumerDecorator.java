package bergdb.nanotest;

import java.io.PrintStream;

/**
 * Useful to decorate a existing TestRunConsumer by overriding a method or two.
 * 
 * @author Frans Lundberg
 */
public class ConsumerDecorator implements TestRunConsumer {
    private final TestRunConsumer base;
    
    public ConsumerDecorator(TestRunConsumer base) {
        this.base = base;
    }
    
    public void starting() {
        base.starting();
    }

    public void classAboutToRun(Class<?> clazz) {
        base.classAboutToRun(clazz);
    }

    public void classDone() {
        base.classDone();
    }

    public void testAboutToRun(String longMethodName) {
        base.testAboutToRun(longMethodName);
    }

    public void report(String name, Object value) {
        base.report(name, value);
    }

    public PrintStream out() {
        return base.out();
    }

    public void testDone(Throwable t) {
        base.testDone(t);
    }

    public void done() {
        base.done();
    }
}
