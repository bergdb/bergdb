package bergdb.dag;

/**
 * Specialized data structure for storing pointer indexes to the nodes accessed.
 * 
 * @author Frans Lundberg
 */
public class Choices {
    private static final int INITIAL_SIZE = 32;
    public int size;
    public byte[] choices;
    
    public Choices() {
        size = 0;
        choices = new byte[INITIAL_SIZE];
    }
    
    public final int getSize() {
        return size;
    }
    
    public final int getChoice(int index) {
        if (index >= size) {
            throw new IndexOutOfBoundsException("index = " + index + ", size = " + size);
        }
        return choices[index];
    }
    
    /**
     * Sets size to 0.
     */
    public final void clear() {
        if (choices.length > 256) {
            choices = new byte[INITIAL_SIZE];
        }
        size = 0;
    }
    
    public final byte get(int index) {
        return choices[index];
    }
    
    public byte[] getChoices() {
        byte[] result = new byte[size];
        getChoices(result, 0);
        return result;
    }
    
    public void getChoices(byte[] dest, int offset) {
        assert dest != null;
        assert dest.length - offset >= size;
        System.arraycopy(this.choices, 0, dest, offset, size);
    }
    
    public String toString() {
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < size; i++) {
            b.append((int) choices[i]);
            if (i < size - 1) {
                b.append(" ");
            }
        }
        b.append("]");
        return b.toString();
    }
    
    /**
     * Adds a pointer index (a choice).
     */
    public final void add(int choice) {
        assert choice >= -1 && choice < 128 : "Bad choice value, " + choice + ".";
        
        size++;
        if (choices.length < size) enlargeArray();
        choices[size - 1] = (byte) choice;
    }
    
    private void enlargeArray() {        
        byte[] newChoices = new byte[choices.length * 2];
        System.arraycopy(choices,  0, newChoices, 0, choices.length);
        choices = newChoices;
    }
}
