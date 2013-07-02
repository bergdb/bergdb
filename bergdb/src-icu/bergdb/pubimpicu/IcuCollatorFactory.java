package bergdb.pubimpicu;

import java.util.HashSet;

import bergdb.common.Bug;
import bergdb.pubimp.CollatorFactory;
import bergdb.pubimp.KCollator;
import bergdb.pubimp.BergCollatorFactory;
import kissdb.icu50.text.Collator;        // TODO X Will need change soon.
import kissdb.icu50.util.ULocale;         // TODO X Will need change soon.

/**
 * A factory to create ICU implementations of KCollatory.
 * 
 * @see bergdb.pubimp.KCollator
 * @author Frans Lundberg
 */
public class IcuCollatorFactory implements CollatorFactory {
    private final HashSet<String> collationLocales;
        // Available collation locales (languages) from ICU.
    private BergCollatorFactory bergdbCollatorFactory;

    public IcuCollatorFactory() {
        collationLocales = new HashSet<String>();
        
        // Printed by class icu50/bergdb.icu50.frans.PrintLanguages.
        String[] array = {
                "af", "ar", "as", "az", "be", "bg", "bn", "bs", "ca", "chr", "cs", "cy", "da", 
                "de", "dz", "ee", "el", "en", "eo", "es", "et", "fa", "fi", "fil", "fo", "fr", 
                "ga", "gu", "ha", "haw", "he", "hi", "hr", "hu", "hy", "id", "ig", "is", "it", 
                "ja", "ka", "kk", "kl", "km", "kn", "ko", "kok", "ln", "lt", "lv", "mk", "ml", 
                "mr", "ms", "mt", "my", "nb", "nl", "nn", "om", "or", "pa", "pl", "ps", "pt", 
                "ro", "ru", "si", "sk", "sl", "sq", "sr", "sv", "sw", "ta", "te", "th", "to", 
                "tr", "uk", "ur", "vi", "yo", "zh", "zu"};
        
        for (String s : array) {
            collationLocales.add(s);
        }
        
        bergdbCollatorFactory = new BergCollatorFactory();
    }
    
    
    public KCollator createCollator(String typeString) {
        if (typeString == null) {
            throw new IllegalArgumentException("typeString == null not allowed");
        }
        
        KCollator result = this.bergdbCollatorFactory.createCollator(typeString);
        if (result != null) {
            return result;
        }
        
        if (!typeString.startsWith("string/")) {
            return null;
        }
        
        typeString = typeString.substring("string/".length());
        if (typeString.length() == 0) {
            return null;
        }
        
        String[] parts = typeString.split("/");
        if (parts.length < 1 || parts.length > 2) {
            return null;
        }
        
        String localeString = parts[0];
        if (!collationLocales.contains(localeString)) {
            return null;
        }
        
        Collator collator = Collator.getInstance(new ULocale(localeString));
        if (collator == null) {
            throw new Bug("collator == null, " + localeString);
        }
        
        if (parts.length == 1) {
            collator.setStrength(Collator.PRIMARY);
        } else {
            String l = parts[1];
            if (l.length() != 2) {
                return null;
            }
            if (l.charAt(0) != 'L') {
                return null;
            }
            
            char c1 = l.charAt(1);
            
            switch (c1) {
            case '1':
                collator.setStrength(Collator.PRIMARY);
                break;
            case '2':
                collator.setStrength(Collator.SECONDARY);
                break;
            case '3':
                collator.setStrength(Collator.TERTIARY);
                break;
            case '4':
                collator.setStrength(Collator.QUATERNARY);
                break;
            case 'n':
                collator.setStrength(Collator.IDENTICAL);
                break;
            default:
                return null;
            }
        }
        
        result = new IcuKCollator(collator);
        return result;
    }


    public boolean typeSupported(String typeString) {
        if (typeString == null) {
            throw new IllegalArgumentException("typeString == null not allowed");
        }
        
        if (bergdbCollatorFactory.typeSupported(typeString)) {
            return true;
        }
        
        if (!typeString.startsWith("string/")) {
            return false;
        }
        
        typeString = typeString.substring("string/".length());
        if (typeString.length() == 0) {
            return false;
        }
        
        String[] parts = typeString.split("/");
        if (parts.length < 1 || parts.length > 2) {
            return false;
        }
        
        String localeString = parts[0];
        if (!collationLocales.contains(localeString)) {
            return false;
        }
        
        if (parts.length > 1) {
            String strength = parts[1];
            if (strength.length() != 2) {
                return false;
            }
            
            if (strength.charAt(0) != 'L') {
                return false;
            }
            
            char c1 = strength.charAt(1);
            
            switch (c1) {
            case '1':
            case '2':
            case '3':
            case '4':
            case 'n':
                break;
            default:
                return false;
            }
        }
        
        return true;
    }
}
