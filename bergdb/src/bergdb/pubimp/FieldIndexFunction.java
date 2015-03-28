package bergdb.pubimp;

import bergdb.common.Bug;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pubimp.IndexManager.Index;

/**
 * An IndexFunction based on a field specification.
 * 
 * @author Frans Lundberg
 */
public class FieldIndexFunction implements IndexFunction {
    private String[] typeStrings;
    private String[][] fields;
    private String[][] fieldCombinations;
    private int combinationCount;
    private final int levelCount;
    final char[] types;              // TYPE_x
    final KCollator[] kcollators;    // Non-null when type == TYPE_STRING;
    private final CollatorFactory collatorFactory;
    
    public FieldIndexFunction(String[][] fields, String[] typeStrings, CollatorFactory collatorFactory) {
        this.fields = fields;
        this.typeStrings = typeStrings;
        this.levelCount = typeStrings.length;
        combinationCount = computeCombinationCount();
        fieldCombinations = computeFieldCombinations();
        this.types = new char[levelCount];
        this.kcollators = new KCollator[levelCount];
        this.collatorFactory = collatorFactory;
        handleIndexLevels();
    }
    
    public String[] getTypes() {
        return typeStrings;
    }

    public void computeSortBytes(DbObject dbo, SortBytesBuilder b) {
        for (int i = 0; i < fieldCombinations.length; i++) {
            computeSortBytes(i, dbo, b);
        }
    }
    
    /**
     * Returns the the sort bytes for a particular Index, entry index, and DbObject.
     * This method determines what index entries an object should have when written to the database.
     */
    private void computeSortBytes(int combinationIndex, 
            DbObject dbo, SortBytesBuilder b) {
        // Both long and int fields are indexed in a "long" index.
        // Both double and float fields are indexed in a "double" index.

        final String[] fieldCombination = fieldCombinations[combinationIndex];
        boolean gotAnEntry = true;

        for (int j = 0; j < levelCount; j++) {
            String field = fieldCombination[j];
            char type = types[j];
            boolean fieldUsed = false;

            switch (type) {
            case Index.TYPE_LONG:
                if (dbo.has(field, 'l')) {
                    b.addLong(dbo.getLong(field));
                    fieldUsed = true;
                } else if (dbo.has(field, 'i')) {
                    b.addLong(dbo.getInt(field));
                    fieldUsed = true;
                }
                break;

            case Index.TYPE_DOUBLE:
                if (dbo.has(field, 'd')) {
                    b.addDouble(dbo.getDouble(field));
                    fieldUsed = true;
                }
                break;

            case Index.TYPE_STRING:
                if (dbo.has(field, 's')) {
                    String stringValue = dbo.getString(field);
                    b.addString(stringValue, kcollators[j]);
                    fieldUsed = true;
                }
                break;

            default:
                throw new Bug("Bad index type: " + type + ". field:" + field);
            }

            if (!fieldUsed) {
                gotAnEntry = false;
                b.clearEntry();
                break;
            }
        }
        
        if (gotAnEntry) {
            b.entryDone();
        }
    }

    
    private int computeCombinationCount() {
        int cCount = 1;
        for (int i = 0; i < levelCount; i++) {
            cCount = cCount * fields[i].length;
        }
        return cCount;
    }

    private String[][] computeFieldCombinations() {
        String[][] fieldComb = new String[combinationCount][];
        int[] indexArray = new int[levelCount];
        int[] sizeArray = new int[levelCount];
        for (int i = 0; i < levelCount; i++) {
            sizeArray[i] = fields[i].length;
        }
        int combinationIndex = 0;
        
        for (int i = 0; i < combinationCount; i++) {
            String[] combination = new String[levelCount];
            for (int j = 0; j < levelCount; j++) {
                combination[j] = fields[j][indexArray[j]];
            }
            
            fieldComb[combinationIndex++] = combination;
            
            boolean increased = nextIndexArray(indexArray, sizeArray);
            if (i < combinationCount - 1) {
                assert increased : "'increased' was false, levels=" + levelCount + ", i=" + i;
            }
        }
        
        return fieldComb;
    }
    
    private boolean nextIndexArray(int[] indexArray, int[] sizeArray) {
        int levels = indexArray.length;
        assert sizeArray.length == levels;
        boolean increased = false;
        
        for (int i = levels - 1; i >= 0; i--) {
            if (indexArray[i] == sizeArray[i] - 1) {
                continue;
            } else {
                indexArray[i]++;
                for (int j = i + 1; j < levels; j++) {
                    indexArray[j] = 0;
                }
                
                increased = true;
                break;
            }
        }
        return increased;
    }
    
    private void handleIndexLevels() {        
        for (int level = 0; level < levelCount; level++) {
            String typeString = typeStrings[level];
            char type = 'X';
            KCollator kc = null;
        
            char first = typeString.charAt(0);
            switch (first) {
            case 'l':
                if (!typeString.equals("long")) {
                    throw new IllegalArgumentException("Unsupported index type: " + typeString);
                }
                
                type = Index.TYPE_LONG;
                break;
                
            case 'd':
                if (!typeString.equals("double")) {
                    throw new IllegalArgumentException("Unsupported index type: " + typeString);
                }
                
                type = Index.TYPE_DOUBLE;
                break;
                
            case 's':   
                kc = collatorFactory.createCollator(typeString);
                if (kc == null) {
                    throw new IllegalArgumentException("Unsupported index type: " + typeString);
                }
                type = Index.TYPE_STRING;
                break;
                
            default:
                throw new IllegalArgumentException("Unsupported index type: " + typeString);
            }
            
            assert type != 'X';
            this.types[level] = type;
            this.kcollators[level] = kc;
        }
    }
    
    public static class Tester {
        private Tester() {}
        
        @Nano
        public static void testConstructor1() {
            BergCollatorFactory f = new BergCollatorFactory();
            String[][] fields = {{"account"}, {"time"}};
            String[] types = {"long", "long"};
            
            
            FieldIndexFunction function = new FieldIndexFunction(fields, types, f);            
            Assert.assertEquals(1, function.combinationCount);
        }
        
        @Nano
        public static void testConstructor2() {
            BergCollatorFactory f = new BergCollatorFactory();
            String[][] fields = {{"from", "to"}, {"time", "rTime"}};
            String[] types = {"long", "long"};
            
            FieldIndexFunction function = new FieldIndexFunction(fields, types, f); 
            Assert.assertEquals(4, function.combinationCount);
            Assert.assertEquals(4, function.fieldCombinations.length);
            
            Assert.assertEquals("from", function.fieldCombinations[0][0]);
            Assert.assertEquals("time", function.fieldCombinations[0][1]);
            
            Assert.assertEquals("from", function.fieldCombinations[1][0]);
            Assert.assertEquals("rTime", function.fieldCombinations[1][1]);
            
            Assert.assertEquals("to", function.fieldCombinations[2][0]);
            Assert.assertEquals("time", function.fieldCombinations[2][1]);
            
            Assert.assertEquals("to", function.fieldCombinations[3][0]);
            Assert.assertEquals("rTime", function.fieldCombinations[3][1]);
        }
    }
}
