package bergdb.pubimp;

/**
 * An implementation of this interface can create a template object given a Class parameter.
 * 
 * @author Frans Lundberg
 */
public interface ClassToObject {
    
    /**
     * Creates and returns a new object of the specified class.
     * The newly created object is typically used as a template; its fields will be set
     * through reflection to match data in the database.
     * 
     * @throws ObjectCreationException  If the objection could not be created.
     */
    public <TYPE> TYPE newObject(Class<TYPE> c);
}
