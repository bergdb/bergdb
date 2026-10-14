package bergdb.pubimp;

import bergdb.core.InternalDataException;

/**
 * Inner classes of this class is used to store data in the database.
 * Static conversion methods are used to convert between ordinary Java objects and data objects.
 * 
 * @author Frans Lundberg
 */
public class Data {
    
    private Data() {}
    
    /**
     * Class used for storing index info as internal data.
     */
    public static class Index {
        //
        // NOTE this will not handle DbObject fields that contain "," or ".".
        // These characters are used as special characters to separate strings.
        // Would be better to change this to use String[][] for fields, 
        // or even String[][][] for nested fields. Not backward-compatible however.
        //
        
        public String[] dirs;
        
        /**
         * An array of fields names for each composite level; comma-separated and those
         * values may be dot-separated (for nested fields).
         */
        public String[] fields;
        
        public String[] typeStrings;
        
        public String state;        // One of "creating" / "active" / "deleting".
        
        /**
         * Field added for 2015.2 release, set to 1.
         */
        public int version = 1;     
        
        public Index() {}
        
        /**
         * Checks object state after reading it from database.
         * 
         * @throws InternalDataException
         */
        public void check(IndexManager indexManager) throws InternalDataException {
            checkDirs();
            int levels = checkFields();
            checkTypeStrings(indexManager, levels);
            checkState();
        }

        private void checkState() {
            if (state == null) {
                throw new InternalDataException("'state' == null");
            }
            
            if (state.length() < 1) {
                throw new InternalDataException("state.length() < 1: '" + state + "'.");
            }
            
            char c = state.charAt(0);
            
            switch (c) {
            case 'c':
                if (!state.equals("creating")) {
                    throw new InternalDataException("Bad index 'state': " + state + ".");
                }
                break;
            case 'a':
                if (!state.equals("active")) {
                    throw new InternalDataException("Bad index 'state': " + state + ".");
                }
                break;
            case 'd':
                if (!state.equals("deleting")) {
                    throw new InternalDataException("Bad index 'state': " + state + ".");
                }
                break;
            default:
                throw new InternalDataException("Bad index 'state': " + state + ".");
            }
        }

        private void checkTypeStrings(IndexManager indexManager, int levels) {
            if (typeStrings.length != levels) {
                throw new InternalDataException("fields.length != typeStrings.length (" 
                        + typeStrings.length + ")");
            }
            
            for (int i = 0; i < typeStrings.length; i++) {
                if (!indexManager.typeSupported(typeStrings[i])) {
                    throw new InternalDataException("Type string '" + typeStrings[i] + "' not " +
                    		"supported.");
                }
            }
        }

        private int checkFields() {
            if (fields == null) {
                throw new InternalDataException("'fields' is null.");
            }
            
            if (fields.length == 0) {
                throw new InternalDataException("'fields.length' == 0");
            }
            
            int levels = fields.length;     // number of composite index levels
            
            for (int i = 0; i < levels; i++) {
                String fieldString = fields[i];
                String[] f = fieldString.split(",");
                
                if (f.length == 0) {
                    throw new InternalDataException("fields[" + i + "] has zero parts.");
                }
                
                for (int j = 0; j < f.length; j++) {
                    String s = f[j];
                    if (s == null) {
                        throw new InternalDataException("fields[" + i + "][" + j + "] is null.");
                    }
                    if (s.length() == 0) {
                        throw new InternalDataException(
                                "fields[" + i + "][" + j + "].length() == 0.");
                    }
                }
            }
            return levels;
        }

        private void checkDirs() {
            if (dirs == null) {
                throw new InternalDataException("'dirs' is null");
            }
            
            if (dirs.length == 0) {
                throw new InternalDataException("Length of 'dirs' is 0.");
            }
            
            for (int i = 0; i < dirs.length; i++) {
                String dir = dirs[i];
                if (dir == null) {
                    throw new InternalDataException("dir[" + i + "] is null.");
                }
                
                if (dir.length() == 0) {
                    throw new InternalDataException("dir[" + i + "] has length == 0.");
                }
            }
        }
    }
    
    public static Data.Index createIndexDo(IndexManager.Index index) {
        assert index != null;
        assert index.fields != null;
        assert index.typeStrings != null;
        assert index.fields.length > 0;
        assert index.typeStrings.length > 0;
        assert index.fields.length == index.typeStrings.length;
        
        Index indexDo = new Index();
        indexDo.dirs = index.dirs.clone();
        
        indexDo.fields = new String[index.fields.length];
        for (int i = 0; i < index.fields.length; i++) {
            StringBuilder b = new StringBuilder();
            for (int j = 0; j < index.fields[i].length; j++) {
                b.append(index.fields[i][j].getName());
                if (i != index.fields[i].length - 1) {
                    b.append(",");         // Comma-separated list of field names.
                }
            }
            indexDo.fields[i] = b.toString();
        }
        
        indexDo.typeStrings = index.typeStrings.clone();
        indexDo.state = index.getStateString();
        
        return indexDo;
    }
    
    public static IndexManager.Index createIndex(String indexName, Data.Index indexDo, 
            IndexManager indexManager) throws InternalDataException {
        // Input params should have been checked already.
        
        FieldRef[][] fields = new FieldRef[indexDo.fields.length][];
        for (int i = 0; i < indexDo.fields.length; i++) {
            String[] parts = indexDo.fields[i].split(",");
            
            fields[i] = new FieldRef[parts.length];
            for (int j = 0; j < parts.length; j++) {
                String part = parts[j];
                String[] bits = part.split("\\.");
                fields[i][j] = new FieldRef(bits);
            }
        }
        
        IndexManager.Index index = new IndexManager.Index(indexName, indexDo.dirs, fields, 
                indexDo.typeStrings, indexManager);
        
        if (indexDo.state.equals("creating")) {
            index.setState(IndexManager.Index.STATE_CREATING);
        } else if (indexDo.state.equals("active")) {
            index.setState(IndexManager.Index.STATE_ACTIVE);
        } else if (indexDo.state.equals("deleting")) {
            index.setState(IndexManager.Index.STATE_DELETING);
        } else {
            throw new InternalDataException("Bad index info object, bad 'status' string: '" 
                    + indexDo.state + "'.");
        }
        
        return index;
    }
}
