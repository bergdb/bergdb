package bergdb.pub;

import bergdb.pub.util.Job;

/**
 * <p>A builder to create a database index.
 * It is mandatory to call the three methods: dir(), type(), and field()  
 * before calling createFast() or start() to create the index.
 * The type() method must be called before field().</p>
 *
 * <p>Experimental in 2026.3, with known faults; it may change in a later release (bergdb
 * 018-01, D6).</p>
 * 
 * <p>An example of creating an index that indexes employee salaries (long field 'salary' of 
 * Employee objects) could look like this:</p>
 * 
 * <code>database.indexBuilder("employee-salary").dir("employees/").type("long").field("salary").createFast();</code>
 * 
 * <p>The builder supports the creation of ordinary indexes, but also composite
 * indexes that consists of multiple parts. To create a composite index, call type()
 * followed by field() more than once before eventually calling createFast() or 
 * start(). The call to type() starts a new composite index level. The following calls to 
 * field() apply to the nearest preceding call to type().</p>
 * 
 * <p>dir() can be called multiple times to create an index that spans multiple directories.</p>
 * 
 * <p>field() can be called multiple times to create one index that indexes multiple fields
 * of the objects.</p>
 * 
 * <p>The allowed method call sequence is described by the following ABNF
 * (http://en.wikipedia.org/wiki/Augmented_Backus%E2%80%93Naur_Form). "1*" means "one or more".</p>
 * 
 * <pre>
 *     callSequence = 1*dir 1*(type 1*field) (createFast / start)
 * </pre>
 * 
 * @author Frans Lundberg
 */
public interface IndexBuilder {
    
    /**
     * The type of the index; the main type is one of: "long", "double", "string".
     * 
     * <p>The "long" index type applies to object fields of Java type "long". This index type
     * sorts objects according to the numerical value of their long fields.</p>
     * 
     * <p>The "double" index type applies to object fields of Java type "double". This index type
     * sorts object according to the numerical value of their double fields. Sorting of 
     * Double.POSITIVE_INFINITY and Double.NEGATIVE_INFINITY works as expected. Sorting of
     * Double.NaN (not-a-number) double values are are not supported (result is unspecified).</p>
     * 
     * <p>The "string" index type applies to object fields of Java type "String".
     * This index types sorts objects according to the alphabetical order of the strings.
     * Without anything else appended to it, "string" creates an index that sorts strings 
     * lexicographically by the Unicode code points of the characters in the string.
     * Alternatively, the equivalent "string/unicode" can be used for this sort order.
     * For natural language strings, this sort is often not suitable. Different languages have 
     * different conventions for how to sort strings in alphabetical order.
     * Therefore, a language parameter can be optionally be appended to "string" to create a
     * string index for a particular language. For example, "string/sv" will create an index
     * that sorts strings according to the conventions of the Swedish language.</p>
     * 
     * <p>A specific way to sort strings is often called a "collation". BergDB uses ICU
     * (http://icu-project.org/) for collation support (release 50.1). 
     * ICU has a large collection of collation implementations that follows the UCA (Unicode 
     * Collation Algorithm) standard, available at http://www.unicode.org/reports/tr10/.</p>
     * 
     * <p>The following collations (languages) are supported by BergDB 
     * (in addition to "string/unicode"):</p>
     * 
     * <pre>
     * af   Afrikaans
     * ar   Arabic
     * as   Assamese
     * az   Azerbaijani
     * be   Belarusian
     * bg   Bulgarian
     * bn   Bengali
     * bs   Bosnian
     * ca   Catalan
     * chr  Cherokee
     * cs   Czech
     * cy   Welsh
     * da   Danish
     * de   German
     * dz   Dzongkha
     * ee   Ewe
     * el   Greek
     * en   English
     * eo   Esperanto
     * es   Spanish
     * et   Estonian
     * fa   Persian
     * fi   Finnish
     * fil  Filipino
     * fo   Faroese
     * fr   French
     * ga   Irish
     * gu   Gujarati
     * ha   Hausa
     * haw  Hawaiian
     * he   Hebrew
     * hi   Hindi
     * hr   Croatian
     * hu   Hungarian
     * hy   Armenian
     * id   Indonesian
     * ig   Igbo
     * is   Icelandic
     * it   Italian
     * ja   Japanese
     * ka   Georgian
     * kk   Kazakh
     * kl   Kalaallisut
     * km   Khmer
     * kn   Kannada
     * ko   Korean
     * kok  Konkani
     * ln   Lingala
     * lt   Lithuanian
     * lv   Latvian
     * mk   Macedonian
     * ml   Malayalam
     * mr   Marathi
     * ms   Malay
     * mt   Maltese
     * my   Burmese
     * nb   Norwegian Bokmål
     * nl   Dutch
     * nn   Norwegian Nynorsk
     * om   Oromo
     * or   Oriya
     * pa   Punjabi
     * pl   Polish
     * ps   Pashto
     * pt   Portuguese
     * ro   Romanian
     * ru   Russian
     * si   Sinhala
     * sk   Slovak
     * sl   Slovenian
     * sq   Albanian
     * sr   Serbian
     * sv   Swedish
     * sw   Swahili
     * ta   Tamil
     * te   Telugu
     * th   Thai
     * to   Tongan
     * tr   Turkish
     * uk   Ukrainian
     * ur   Urdu
     * vi   Vietnamese
     * yo   Yoruba
     * zh   Chinese
     * zu   Zulu
     * </pre>
     * 
     * <p>The language code (2-3 characters) is used to specify the language for a string index.
     * Optionally a string index type string can include the <em>comparison level</em> to use.
     * See http://www.unicode.org/reports/tr10/#Multi_Level_Comparison. The default is L1.
     * This is the most efficient comparison level (smallest index), but sometimes one of the 
     * other levels (L2, L3, L4, Ln) is required.</p>
     * 
     * <p>Examples of valid index type strings:</p>
     * 
     * <pre>
     *   long             - Sorts integer values of long fields.
     *   double           - Sorts floating point values of double fields.
     *   string           - Unicode code point sort.
     *   string/unicode   - Unicode code point sort.
     *   string/en        - English language, comparison level L1.
     *   string/sv        - Swedish language, comparison level L1.
     *   string/sv/L3     - Swedish language, comparison level L3.
     *   string/zh/L2     - Chinese language, comparison level L2.
     *   string/pl        - Polish language, comparison level L1.
     * </pre>
     * 
     * <p>Note, alternative builds of BergDB may exclude ICU support and therefore will 
     * only support the "string/unicode" collator. This means that indexes created with ICU 
     * collators with a standard BergDB build, can be impossible to use by software using 
     * an alternative (constrained) BergDB library.</p>
     */
    public IndexBuilder type(String indexTypeString);
    
    /**
     * Adds an index to the directories to index. At least one call to this method is 
     * required.
     * 
     * @param dir  The directory, null is not allowed. Must end with '/'.
     * @throws IllegalArgumentException  If dir is null or empty, does not end with '/', or
     *      contains "//".
     */
    public IndexBuilder dir(String dir);
    
    /**
     * Adds a field to the fields to index.
     * At least one call to a field method is required per composite part.
     * 
     * @param field  The field name, null or the empty string is not allowed.
     */
    public IndexBuilder field(String field);
    
    /**
     * Adds a nested field to the fields to index.
     * This is a utility methods using dots to separate the parts.
     * If a dot could be part of a field name itself, do not use this method.
     * 
     * @param fieldSpec  
     *      A string with dots to separate the parts. Example: "car.dimensions.length".
     */
    public IndexBuilder nestedField(String fieldSpec);
    
    /**
     * Adds a nested field to the fields to index.
     * 
     * @param fieldParts 
     *      The parts of the nested field. 
     *      Example: new String[]{"car", "dimensions", "length"}.
     */
    public IndexBuilder nestedField(String[] fieldParts);
    
    /** 
     * Creates this index immediately and makes it active without adding index entries for existing 
     * database objects. Only new objects (added/updated) will be indexed.
     */
    public void createFast();
    
    /**
     * Creates a new index in a background job. The index state will be CREATING
     * until the job finishes and the index state becomes ACTIVE. 
     * The index cannot be used until the job finishes.
     * If the database is stopped before the index has been created, the index creation process
     * will automatically continue when the database is started again.
     * If the index is deleted before the job finishes, the job stops without making the index
     * active, and writes nothing to an index created later with the same name; its status then
     * has progress 100 and a note that says that the index was deleted.
     * 
     * @throws IndexAlreadyExistsException if an index with this name already exists.
     */
    public Job start();
}
