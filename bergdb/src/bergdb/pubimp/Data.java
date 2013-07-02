package bergdb.pubimp;

import bergdb.core.InternalDataException;

/**
 * Inner classes of this class is used to store data in the database.
 * Static conversion method are used to convert between ordinary Java objects and data objects.
 * 
 * @author Frans Lundberg
 */
public class Data {
    // 130308 Frans: Changed "String[][] fields" to "String[] fields".
    
    /**
     * Class used for storing index info as internal data.
     */
    public static class Index {
        public String[] dirs;
        public String[] fields;     // An array of fields names for each composite level.
        public String[] typeStrings;
        public String state;       // One of "creating" / "active" / "deleting".
        
        public Index() {}
        
        /**
         * Checks object state after read from database.
         * 
         * @throws InternalDataException
         */
        public void check(IndexManager indexManager) throws InternalDataException {
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
                b.append(index.fields[i][j]);
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
        
        String[][] fields = new String[indexDo.fields.length][];
        for (int i = 0; i < indexDo.fields.length; i++) {
            fields[i] = indexDo.fields[i].split(",");
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
