package kissdb.pubimp;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

import kissdb.common.Bug;

/**
 * An object factory that creates object from the zero-argument constructor of the 
 * specified class. The constructor may be private of package access, it will still be used
 * to create objects through reflection.
 * 
 * @author Frans Lundberg
 */
public class BlankConstructorFactory implements ObjectFactory {
    private Constructor<?> constructor;
    
    /**
     * @throws IllegalArgumentException If 'clazz' has no default constructor or
     * there is another reason objects of the 'clazz' cannot be created.
     */
    public BlankConstructorFactory(Class<?> clazz) {
        assert clazz != null;
        
        try {
            this.constructor = clazz.getDeclaredConstructor();
        } catch (NoSuchMethodException e1) {
            throw new IllegalArgumentException("No zero-argument constructor exists in class " 
                    + clazz.getName() + ".");
        } catch (SecurityException e1) {
            throw new IllegalArgumentException(e1);
        }
        
        constructor.setAccessible(true);
        
        try {
            constructor.newInstance();
        } catch (SecurityException e) {
            throw new IllegalArgumentException(e);
        } catch (InstantiationException e) {
            throw new IllegalArgumentException(e);
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(e);
        } catch (IllegalArgumentException e) {
            throw new Bug("Never happens");
        } catch (InvocationTargetException e) {
            throw new IllegalArgumentException(e);
        }
    }
    
    /**
     * Creates and returns a new object.
     */
    public Object createObject() {
        // Everything already tested in constructor, no exception should be thrown here.
        
        Object object;
        try {
            object = constructor.newInstance();
        } catch (SecurityException e) {
            throw new Bug(e);
        } catch (InstantiationException e) {
            throw new Bug(e);
        } catch (IllegalAccessException e) {
            throw new Bug(e);
        } catch (IllegalArgumentException e) {
            throw new Bug(e);
        } catch (InvocationTargetException e) {
            throw new Bug(e);
        }
        
        return object;
    }
}