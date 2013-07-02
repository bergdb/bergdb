package bergdb.pubimp;

import bergdb.common.Bug;

/**
 * Provides a way to use the ICU code without a Java reference to that code.
 * This factory will use ICU package (com.bergdb.pubimpicu.IcuCollatorFactory) if available, 
 * otherwise it default to use BergCollatorFactory.
 *
 * @author Frans Lundberg
 */
public class OptionalIcuCollatorFactory implements CollatorFactory {
    private CollatorFactory factory;
    
    public OptionalIcuCollatorFactory() {
        factory = init();
    }
    
    private CollatorFactory init() {
        Class<?> clazz;
        CollatorFactory factory;
        
        if (!IcuInfo.hasIcu()) {
            factory = new BergCollatorFactory();
        } else {
            String className = "bergdb.pubimpicu.IcuCollatorFactory";
            
            try {
                clazz = Class.forName(className);
            } catch (ClassNotFoundException e) {
                return new BergCollatorFactory();
            }
            
            Object factoryObject;
            
            try {
                factoryObject = clazz.newInstance();
                factory = (CollatorFactory) factoryObject;
            } catch (InstantiationException e) {
                throw new Bug("Should not happen, " + e.toString());
            } catch (IllegalAccessException e) {
                throw new Bug("Should not happen, " + e.toString());
            } catch (ClassCastException e) {
                throw new Bug("Class " + className + " does not implement CollatorFactory.");
            }
        }
        
        return factory;
    }

    public KCollator createCollator(String typeString) {
        return factory.createCollator(typeString);
    }

    public boolean typeSupported(String typeString) {
        return factory.typeSupported(typeString);
    }
}
