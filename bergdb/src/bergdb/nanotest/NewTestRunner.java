package bergdb.nanotest;

import java.util.HashSet;
import java.util.regex.Pattern;

// TODO C. Work on this

/**
 * Takes a set of class and a TestRunConsumer and runs the
 * nano tests in the classes and reports the results to the TestRunConsumer.
 * 
 * @author Frans Lundberg
 */
public class NewTestRunner {
    private Builder b;
    
    private NewTestRunner(Builder b) {
        this.b = b;
    }
    
    private void run() {
        
    }
    
    public Builder builder(TestRunConsumer consumer) { 
        Builder b = new Builder();
        b.consumer = consumer;
        return b;
    }
    
    public static class Builder {
        private TestRunConsumer consumer;
        private boolean printProps = true;
        private boolean printMethods = true;
        private boolean printStart = false;
        private HashSet<Class> classes;
        private Pattern methodPattern = Pattern.compile(".*");    // matches any method name
        
        private Builder() {}
        
        public Builder printProps(boolean b) {
            printProps = b;
            return this;
        }
        
        public Builder printMethods(boolean b) {
            printMethods = b;
            return this;
        }
        
        public Builder printStart(boolean b) {
            printStart = b;
            return this;
        }
        
        public Builder addClass(Class<?> c) {
            classes.add(c);
            return this;
        }
        
        public Builder methodPattern(String pattern) {
            this.methodPattern = Pattern.compile(pattern);
            return this;
        }
        
        public NewTestRunner build() {
            return new NewTestRunner(this);
        }
    }
}
