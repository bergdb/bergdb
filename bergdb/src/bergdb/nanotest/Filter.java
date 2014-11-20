package bergdb.nanotest;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;

// TODO LATER Use this class, reduce number of params in TestRunner constr.

public class Filter {
    private final Builder b;
    
    private Filter(Builder b) {
        this.b = b;
    }
    
    public static Builder builder() {
        return new Builder();
    }
    
    public static class Builder {
        private Pattern classRegex = Pattern.compile(".*");
        private Pattern methodRegex = Pattern.compile(".*");
        private Set<String> groups = new HashSet<String>();
        
        private Builder() {        
        }
        
        public Builder classRegex(String s) {
            assert s != null;
            classRegex = Pattern.compile(s);
            return this;
        }
        
        public Builder methodRegex(String s) {
            assert s != null;
            methodRegex = Pattern.compile(s);
            return this;
        }
        
        public Builder addGroup(String s) {
            groups.add(s);
            return this;
        }
        
        public Filter build() {
            return new Filter(this);
        }
    }
}
