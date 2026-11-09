package bergdb.pubimp;

import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

import bergdb.common.StringUtil;
import bergdb.pub.DbArray;
import bergdb.pub.DbBoolean;
import bergdb.pub.DbByteArray;
import bergdb.pub.DbDouble;
import bergdb.pub.DbLong;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.DbValue;
import bergdb.pub.ObjectCreationException;

/**
 * The binding between Data Objects and DbObjects in Java: layer 2 of bergdb 020-02, section
 * 5.1b, by the rules of bergdb 020-09 ("Data Objects and DbObjects: the conversion rules").
 *
 * <ul>
 * <li>The class check (020-09, section 3): a Data Object class is public, with a public
 *     no-argument constructor; it stores its public, non-static, non-transient fields and
 *     those of its superclasses, each of a type on the closed list; any other instance field
 *     is transient. The result is kept per class for the JVM's life (a ClassValue).</li>
 * <li>The put, toDbObject() (020-09, section 4): exact, by each field's declared type; a null
 *     field left out; a null array element, a value of another class than its field's, a
 *     cycle and a container above level 16 refused with IllegalArgumentException, naming
 *     the path, before anything is written.</li>
 * <li>The get, toJavaObject() (020-09, section 5): best effort, by name; a value that fits
 *     the field's type is set exactly, else the nearest value, integers clamped; the type's
 *     zero where no sensible conversion exists; never a throw for the data.
 *     ObjectCreationException for a class that is not a Data Object and for a constructor
 *     that throws.</li>
 * </ul>
 *
 * <p>No setAccessible() and no deep reflection: a Data Object's constructor and stored fields
 * are public.</p>
 *
 * <p>Internal, not API. The class, toDbObject(), toJavaObject() and convert() are public for
 * bergdb.pub's DbObject and DbArray, which call them (bergdb 020-10, step B3).</p>
 *
 * @author Frans Lundberg
 */
public final class DataObjects {
    private DataObjects() {}

    /** The field that wraps an array put at the top (020-09, section 4.6). */
    static final String ARRAY_FIELD = "array";

    /** The field that wraps a primitive or a wrapper put at the top (020-09, section 4.6). */
    static final String PRIMITIVE_FIELD = "p";

    private static final byte[] ARRAY_NAME = {'a', 'r', 'r', 'a', 'y'};
    private static final byte[] PRIMITIVE_NAME = {'p'};

    // ======== The class check (020-09, section 3) ========

    /** A stored field of a Data Object class (020-09, V3). */
    static final class StoredField {
        final Field field;
        final String name;
        final byte[] nameBytes;
        final Class<?> type;

        StoredField(Field field, byte[] nameBytes) {
            this.field = field;
            this.name = field.getName();
            this.nameBytes = nameBytes;
            this.type = field.getType();
        }
    }

    /**
     * The check of one class by itself (V1 to V8, V10, and that each field's type is on the
     * closed list or a class to check in its turn): valid with its stored fields and its
     * constructor, or not valid with the reason.
     */
    static final class ClassInfo {
        final Class<?> c;
        final String reason;                // null if valid
        final Throwable cause;              // a LinkageError met in the check, or null
        final Constructor<?> constructor;
        final StoredField[] fields;         // in the order of their names' UTF-8 bytes

        private ClassInfo(Class<?> c, String reason, Throwable cause,
                Constructor<?> constructor, StoredField[] fields) {
            this.c = c;
            this.reason = reason;
            this.cause = cause;
            this.constructor = constructor;
            this.fields = fields;
        }

        static ClassInfo refused(Class<?> c, String reason) {
            return new ClassInfo(c, reason, null, null, null);
        }
    }

    /** Where a class reached from another is not a Data Object (020-09, section 3.3). */
    static final class Fault {
        final Class<?> c;           // the class that is not a Data Object
        final String path;          // where it is, from the class checked; "" for that class
        final String reason;
        final Throwable cause;

        Fault(Class<?> c, String path, String reason, Throwable cause) {
            this.c = c;
            this.path = path;
            this.reason = reason;
            this.cause = cause;
        }

        /** The message: the class, its place below 'prefix', the reason. */
        String message(String prefix) {
            String at = join(prefix, path);
            return "The class " + c.getName() + (at.isEmpty() ? "" : " at '" + at + "'")
                    + " is not a Data Object: " + reason + " (bergdb 020-09, section 3).";
        }
    }

    private static final ClassValue<ClassInfo> INFOS = new ClassValue<ClassInfo>() {
        protected ClassInfo computeValue(Class<?> c) {
            try {
                return checkClass(c);
            } catch (LinkageError e) {      // a class that does not load: C's fault (3.3)
                return new ClassInfo(c, "a class it uses could not be loaded, " + e, e, null,
                        null);
            }
        }
    };

    /** The result of the check of a class and every class it reaches: null if valid. */
    private static final ClassValue<Fault[]> FAULTS = new ClassValue<Fault[]>() {
        protected Fault[] computeValue(Class<?> c) {
            return new Fault[] {checkReached(c)};
        }
    };

    /** The class's own check, as INFOS keeps it. */
    static ClassInfo info(Class<?> c) {
        return INFOS.get(c);
    }

    /**
     * The fault of the class 'c' or of a class it reaches through its fields' types, or null
     * if 'c' is a Data Object class (020-09, section 3.2, V9: recursively, each class once).
     */
    static Fault fault(Class<?> c) {
        return FAULTS.get(c)[0];
    }

    /**
     * True for the types that are not classes to check: on the list by themselves. Not void,
     * which is no type of a value.
     */
    private static boolean isScalarType(Class<?> t) {
        return (t.isPrimitive() && t != void.class) || t == String.class || t == Boolean.class
                || t == Byte.class || t == Short.class || t == Character.class
                || t == Integer.class || t == Long.class || t == Float.class
                || t == Double.class;
    }
    
    /** True for the integer types of 020-09, section 2 but char: stored as the integer. */
    private static boolean isIntegerType(Class<?> t) {
        return t == byte.class || t == short.class || t == int.class || t == long.class
                || t == Byte.class || t == Short.class || t == Integer.class
                || t == Long.class;
    }

    /** The type with every array dimension taken off: byte for byte[][], int for int[]. */
    private static Class<?> base(Class<?> t) {
        while (t.isArray()) {
            t = t.getComponentType();
        }
        return t;
    }

    /** A depth-first walk over the classes that 'c' reaches through its fields' types. */
    private static Fault checkReached(Class<?> c) {
        Set<Class<?>> seen = new HashSet<Class<?>>();
        List<Class<?>> todo = new ArrayList<Class<?>>();
        List<String> paths = new ArrayList<String>();
        todo.add(c);
        paths.add("");
        seen.add(c);
        while (!todo.isEmpty()) {
            Class<?> d = todo.remove(todo.size() - 1);
            String path = paths.remove(paths.size() - 1);
            ClassInfo info = info(d);
            if (info.reason != null) {
                return new Fault(d, path, info.reason, info.cause);
            }
            int top = todo.size();
            for (StoredField f : info.fields) {     // the first field to reach a class names it
                Class<?> b = base(f.type);
                if (!isScalarType(b) && seen.add(b)) {
                    todo.add(top, b);               // so taken first from the end
                    paths.add(top, join(path, f.name));
                }
            }
        }
        return null;
    }

    private static String join(String path, String name) {
        return path.isEmpty() ? name : name.isEmpty() ? path : path + "." + name;
    }

    /** V1 to V8 and V10 for 'c' itself (020-09, section 3.2). */
    private static ClassInfo checkClass(Class<?> c) {
        if (c.isPrimitive() || c.isArray()) {
            return ClassInfo.refused(c, "a primitive or an array is not a class of fields");
        }
        if (c.isInterface()) {
            return ClassInfo.refused(c, "it is an interface (V2)");
        }
        if (c.isEnum() || Enum.class.isAssignableFrom(c)) {
            return ClassInfo.refused(c, "it is an enum (V2)");
        }
        if (Record.class.isAssignableFrom(c)) {
            return ClassInfo.refused(c, "it is a record, which 2026.4 does not store (V2)");
        }
        if (isPlatformClass(c)) {
            return ClassInfo.refused(c, "it is a class of the Java platform (V5)");
        }
        for (Class<?> d = c.getSuperclass(); d != null && d != Object.class; 
                d = d.getSuperclass()) {
            if (isPlatformClass(d)) {
                return ClassInfo.refused(c, "it extends " + d.getName() + ", a class of the "
                        + "Java platform (V5)");
            }
        }
        if (c.isAnonymousClass() || c.isLocalClass()) {
            return ClassInfo.refused(c, "it is an anonymous or a local class, never public "
                    + "(V1)");
        }
        if (!Modifier.isPublic(c.getModifiers())) {
            return ClassInfo.refused(c, "it is not public (V1)");
        }
        if (c.isMemberClass() && !Modifier.isStatic(c.getModifiers())) {
            return ClassInfo.refused(c, "it is an inner class, not static (V1)");
        }
        if (Modifier.isAbstract(c.getModifiers())) {
            return ClassInfo.refused(c, "it is abstract (V2)");
        }
        if (!c.getModule().isExported(c.getPackageName(), DataObjects.class.getModule())) {
            return ClassInfo.refused(c, "its package " + c.getPackageName() + " is not "
                    + "exported to BergDB (V6)");
        }
        Constructor<?> constructor;
        try {
            constructor = c.getConstructor();
        } catch (NoSuchMethodException e) {
            return ClassInfo.refused(c, "it has no public no-argument constructor (V2)");
        }

        List<StoredField> fields = new ArrayList<StoredField>();
        Set<String> names = new HashSet<String>();
        for (Class<?> d = c; d != Object.class && d != null; d = d.getSuperclass()) {
            for (Field f : d.getDeclaredFields()) {
                int m = f.getModifiers();
                if (Modifier.isStatic(m) || f.isSynthetic() || Modifier.isTransient(m)) {
                    continue;
                }
                String name = f.getName();
                if (!Modifier.isPublic(m)) {
                    return ClassInfo.refused(c, "its field '" + name + "' is not public and "
                            + "not transient (V3)");
                }
                if (Modifier.isFinal(m)) {
                    return ClassInfo.refused(c, "its field '" + name + "' is final; a get "
                            + "could not set it (V3)");
                }
                if (!Modifier.isPublic(d.getModifiers())) {
                    return ClassInfo.refused(c, "its field '" + name + "' is declared by "
                            + d.getName() + ", which is not public (V4)");
                }
                if (StringUtil.hasLoneSurrogate(name)) {
                    return ClassInfo.refused(c, "its field '" + name + "' has a name with a "
                            + "lone surrogate (V7)");
                }
                byte[] nameBytes = name.getBytes(StandardCharsets.UTF_8);
                if (nameBytes.length > ObjectFormat.MAX_NAME) {
                    return ClassInfo.refused(c, "its field '" + name + "' has a name of "
                            + nameBytes.length + " bytes in UTF-8; a name has 1 to "
                            + ObjectFormat.MAX_NAME + " (V7)");
                }
                if (!names.add(name)) {
                    return ClassInfo.refused(c, "two of its fields are named '" + name
                            + "', one hiding the other (V8)");
                }
                if (isTypeVariable(f.getGenericType())) {
                    return ClassInfo.refused(c, "its field '" + name + "' is of a type "
                            + "variable, " + f.getGenericType().getTypeName() + ", which "
                            + "BergDB does not store (V9)");
                }
                Class<?> b = base(f.getType());
                if (b == Object.class || (!isScalarType(b) && !candidate(b))) {
                    return ClassInfo.refused(c, "its field '" + name + "' is of the type "
                            + f.getType().getTypeName() + ", which BergDB does not store (V9)");
                }
                fields.add(new StoredField(f, nameBytes));
            }
        }
        if (fields.size() > ObjectFormat.MAX_FIELDS) {
            return ClassInfo.refused(c, "it has " + fields.size() + " stored fields, more "
                    + "than " + ObjectFormat.MAX_FIELDS + " (V10)");
        }
        StoredField[] sorted = fields.toArray(new StoredField[0]);
        Arrays.sort(sorted, (x, y) -> Arrays.compareUnsigned(x.nameBytes, y.nameBytes));
        return new ClassInfo(c, null, null, constructor, sorted);
    }

    /** A class of the Java platform: of the bootstrap or the platform class loader (V5). */
    private static boolean isPlatformClass(Class<?> c) {
        ClassLoader loader = c.getClassLoader();
        return loader == null || loader == ClassLoader.getPlatformClassLoader();
    }
    
    /** A type variable, or an array of one, of any dimensions (V9). */
    private static boolean isTypeVariable(Type t) {
        while (t instanceof GenericArrayType) {
            t = ((GenericArrayType) t).getGenericComponentType();
        }
        return t instanceof TypeVariable;
    }
    
    /**
     * Whether a field's base type may be a Data Object class, to be checked in its turn: not
     * Object, DbObject, DbArray or another DbValue (V9). Interfaces, enums, records and
     * platform classes are refused by their own check, which names them.
     */
    private static boolean candidate(Class<?> t) {
        return !DbValue.class.isAssignableFrom(t);
    }

    /**
     * Checks a class given to a get (020-09, sections 3.3 and 5.9): a primitive or a
     * wrapper; an array class whose element type is on the list; or a Data Object class.
     *
     * @throws ObjectCreationException  If not, naming the class, the place and the reason.
     */
    static void checkGet(Class<?> c) {
        if (c == null) {
            throw new IllegalArgumentException("c == null not allowed");
        }
        Class<?> b = base(c);
        if (isScalarType(b)) {
            return;
        }
        Fault f = fault(b);
        if (f != null) {
            throw new ObjectCreationException(f.message(""), f.cause);
        }
    }

    // ======== The put: Data Object to DbObject, exact (020-09, section 4) ========

    /**
     * The DbObject of 'x', by 020-09, section 4.6: a wrapper as an object with the field p,
     * an array (not a byte[]) as an object with the field array, a Data Object as an object
     * of its stored fields; a DbObject as it is.
     *
     * @throws IllegalArgumentException  If 'x' or a value in it cannot be stored exactly
     *      (020-09, section 4.7), naming the path, before anything is written.
     */
    public static DbObject toDbObject(Object x) {
        if (x == null) {
            throw new IllegalArgumentException("object == null not allowed: BergDB stores no "
                    + "null (bergdb 020-09, section 4.3)");
        }
        if (x instanceof DbObject) {
            return (DbObject) x;
        }
        Class<?> c = x.getClass();
        Put put = new Put();
        DbObject.Builder b = new DbObject.Builder();
        if (c.isArray() && c != byte[].class) {
            Class<?> e = base(c);
            Fault f = isScalarType(e) ? null : fault(e);
            if (f != null) {
                throw new IllegalArgumentException(f.message(""));
            }
            put.enter(null);
            b.addArray(ARRAY_FIELD, (DbArray) put.value(c, x));
            put.leave();
        } else if (isScalarType(c)) {
            put.enter(null);
            b.addDbValue(PRIMITIVE_FIELD, put.value(c, x));
            put.leave();
        } else {
            Fault f = fault(c);
            if (f != null) {
                throw new IllegalArgumentException(f.message(""));
            }
            return put.object(info(c), x);
        }
        return b.build();
    }

    /**
     * A put's walk: the containers on the path from the top, one a level (020-07, R14), with
     * the step taken from each, a field's name or an element's index; and the objects on it,
     * for the cycle check (005-23).
     */
    private static final class Put {
        private final List<Object> objects = new ArrayList<Object>();
        private final List<String> steps = new ArrayList<String>();
        private final IdentityHashMap<Object, Boolean> set = new IdentityHashMap<Object, Boolean>();

        /**
         * Enters a container, one level deeper, reached by the step set in the level above;
         * 'object' null for one not checked for cycles.
         */
        void enter(Object object) {
            if (object != null && set.containsKey(object)) {
                int first = 0;
                for (int i = 0; i < objects.size(); i++) {
                    if (objects.get(i) == object) {
                        first = i;
                        break;
                    }
                }
                throw new IllegalArgumentException("The object has a reference cycle: the "
                        + object.getClass().getName() + " at " + describe(objects.size())
                        + " is also at " + describe(first) + " (bergdb 020-09, section 4.5).");
            }
            if (objects.size() >= ObjectFormat.MAX_LEVELS) {
                throw new IllegalArgumentException("The object is nested deeper than "
                        + ObjectFormat.MAX_LEVELS + " levels of objects and arrays, at '"
                        + describe(objects.size()) + "' (bergdb 020-09, section 4.7).");
            }
            objects.add(object);
            if (object != null) {
                set.put(object, Boolean.TRUE);
            }
            steps.add("");
        }

        void leave() {
            int last = objects.size() - 1;
            Object object = objects.remove(last);
            if (object != null) {
                set.remove(object);
            }
            steps.remove(last);
        }

        /** Sets the step being taken in the innermost container. */
        void step(String step) {
            steps.set(steps.size() - 1, step);
        }

        /** The path to the container at level 'depth' + 1 (0: the top). */
        String describe(int depth) {
            if (depth == 0 || (depth == 1 && steps.get(0).isEmpty())) {
                return "the top";
            }
            StringBuilder b = new StringBuilder();
            for (int i = 0; i < depth; i++) {
                if (depth > 12 && i == 5) {
                    append(b, "(" + (depth - 10) + " more)");
                    i = depth - 5;
                }
                append(b, steps.get(i));
            }
            return b.toString();
        }

        /** The path to the value being converted now. */
        String here() {
            String p = describe(steps.size());
            return p.equals("the top") ? "" : p;
        }

        private static void append(StringBuilder b, String step) {
            if (b.length() > 0 && !step.startsWith("[")) {
                b.append('.');
            }
            b.append(step);
        }

        /** The object of Data Object class 'info', its stored fields in name order. */
        DbObject object(ClassInfo info, Object o) {
            DbObject.Builder b = new DbObject.Builder();
            enter(o);
            for (StoredField f : info.fields) {
                step(f.name);
                Object v;
                try {
                    v = f.field.get(o);
                } catch (IllegalAccessException e) {
                    throw new IllegalArgumentException("The field '" + here() + "' cannot be "
                            + "read: " + e, e);
                }
                if (v == null) {
                    continue;       // left out: absent (020-09, section 4.3)
                }
                b.addDbValue(f.name, value(f.type, v));
            }
            leave();
            return b.build();
        }

        /** The value 'v', not null, of the declared type 't' (020-09, section 4.2). */
        DbValue value(Class<?> t, Object v) {
            if (t == boolean.class || t == Boolean.class) {
                return new DbBoolean((Boolean) v);
            } else if (t == char.class || t == Character.class) {
                return new DbLong((Character) v);
            } else if (t == float.class || t == Float.class) {
                return new DbDouble((Float) v);
            } else if (t == double.class || t == Double.class) {
                return new DbDouble((Double) v);
            } else if (isIntegerType(t)) {
                return new DbLong(((Number) v).longValue());
            } else if (t == String.class) {
                String s = (String) v;
                if (StringUtil.hasLoneSurrogate(s)) {
                    throw new IllegalArgumentException("The string at '" + here() + "' has a "
                            + "lone surrogate, a char of U+D800 to U+DFFF that is not part of "
                            + "a surrogate pair. BergDB stores every string as well-formed "
                            + "UTF-8, which cannot hold one (bergdb 021-04); store such data "
                            + "as a byte[] or a char[].");
                }
                return new DbString(s);
            } else if (t == byte[].class) {
                return new DbByteArray((byte[]) v);
            } else if (t.isArray()) {
                return array(t, v);
            }
            if (v.getClass() != t) {
                throw new IllegalArgumentException("The value at '" + here() + "' is a "
                        + v.getClass().getName() + ", not a " + t.getName() + ", the field's "
                        + "type (bergdb 020-09, section 4.5).");
            }
            return object(info(t), v);
        }

        /** The array 'v' of the declared type 't', element by element (020-09, 4.4). */
        DbArray array(Class<?> t, Object v) {
            if (v.getClass() != t) {
                throw new IllegalArgumentException("The value at '" + here() + "' is a "
                        + v.getClass().getTypeName() + ", not a " + t.getTypeName()
                        + ", the field's type (bergdb 020-09, section 4.4).");
            }
            Class<?> e = t.getComponentType();
            DbArray.Builder b = new DbArray.Builder();
            int n = Array.getLength(v);
            enter(v);
            for (int i = 0; i < n; i++) {
                step("[" + i + "]");
                Object element = Array.get(v, i);
                if (element == null) {
                    throw new IllegalArgumentException("The array element at '" + here()
                            + "' is null: BergDB stores no null, and an array has no absent "
                            + "element (bergdb 020-09, section 4.3).");
                }
                b.add(value(e, element));
            }
            leave();
            return b.build();
        }
    }

    // ======== The get: DbObject to Data Object, best effort (020-09, section 5) ========

    /**
     * The object at 'p' of checked bytes (its type byte; 1 for a stored value) as an object of
     * 'c', by 020-09, section 5.9: a primitive or a wrapper from the field p, an array from
     * the field array, null if it is absent; a Data Object class by section 5.3. The bytes
     * are read, never changed or kept: a stored value's (KvToObjectImp, after the full
     * check) or a DbObject's own (DbObject.toJavaObject), so a get makes no copy of them
     * (2026-11-09, the review of 020-10, B3).
     *
     * @throws ObjectCreationException  If 'c' is not a Data Object class or a class it reaches
     *      is not (020-09, section 3.3), or a constructor throws (section 5.2).
     */
    @SuppressWarnings("unchecked")
    public static <T> T toJavaObject(byte[] b, int p, Class<T> c) {
        checkGet(c);
        if (isScalarType(c) || c.isArray()) {
            byte[] name = c.isArray() ? ARRAY_NAME : PRIMITIVE_NAME;
            int q = ObjectFormat.find(b, p, ObjectFormat.objectEnd(b, p), name);
            return q < 0 ? null : (T) convert(b, q, c);
        }
        return (T) make(b, p, c);
    }

    /** A new 'c' with the stored fields of the object at 'p' (020-09, section 5.3). */
    private static Object make(byte[] b, int p, Class<?> c) {
        ClassInfo info = info(c);
        Object o;
        try {
            o = info.constructor.newInstance();
        } catch (InvocationTargetException e) {
            Throwable t = e.getCause();
            if (t instanceof VirtualMachineError) {
                throw (VirtualMachineError) t;
            }
            throw new ObjectCreationException("The constructor of " + c.getName() + " threw "
                    + t + " (bergdb 020-09, section 5.2).", t);
        } catch (ExceptionInInitializerError e) {
            throw new ObjectCreationException("The class " + c.getName() + " could not be "
                    + "initialized: " + e.getCause() + " (bergdb 020-09, section 5.2).", e);
        } catch (LinkageError e) {
            // At a get after the first that met its initializer's exception: "Could not
            // initialize class" (a NoClassDefFoundError), the class's fault as the first.
            throw new ObjectCreationException("The class " + c.getName() + " could not be "
                    + "initialized or linked: " + e + " (bergdb 020-09, section 5.2).", e);
        } catch (InstantiationException | IllegalAccessException e) {
            throw new ObjectCreationException("A " + c.getName() + " could not be made: " + e
                    + " (bergdb 020-09, section 5.2).", e);
        } catch (VirtualMachineError e) {
            throw e;
        } catch (Error e) {
            // An Error that a static initializer threw, of the class or of a superclass: Java
            // passes it as it is, and wraps only an Exception in an
            // ExceptionInInitializerError (JLS 12.4.2). The class's fault as that one (the
            // Codex review's X2, bergdb 020-14: it escaped the get, and failed the database
            // in rw()).
            throw new ObjectCreationException("The class " + c.getName() + " could not be "
                    + "initialized: " + e + " (bergdb 020-09, section 5.2).", e);
        }
        int end = ObjectFormat.objectEnd(b, p);
        for (StoredField f : info.fields) {
            int q = ObjectFormat.find(b, p, end, f.nameBytes);
            if (q >= 0) {
                try {
                    f.field.set(o, convert(b, q, f.type));
                } catch (IllegalAccessException e) {
                    throw new ObjectCreationException("The field '" + f.name + "' of "
                            + c.getName() + " could not be set: " + e, e);
                }
            }
        }
        return o;
    }

    /**
     * The value at 'p' of checked bytes as the type 't', by 020-09, section 5.4: exact if it
     * fits, else the nearest value, else the type's zero; boxed for a primitive type.
     */
    public static Object convert(byte[] b, int p, Class<?> t) {
        if (t == boolean.class || t == Boolean.class) {
            return toBoolean(b, p);
        } else if (t == double.class || t == Double.class) {
            return toDouble(b, p);
        } else if (t == float.class || t == Float.class) {
            return toFloat(b, p);
        } else if (t == long.class || t == Long.class) {
            return toLong(b, p);
        } else if (t == int.class || t == Integer.class) {
            return (int) clamp(toLong(b, p), Integer.MIN_VALUE, Integer.MAX_VALUE);
        } else if (t == short.class || t == Short.class) {
            return (short) clamp(toLong(b, p), Short.MIN_VALUE, Short.MAX_VALUE);
        } else if (t == byte.class || t == Byte.class) {
            return (byte) clamp(toLong(b, p), Byte.MIN_VALUE, Byte.MAX_VALUE);
        } else if (t == char.class || t == Character.class) {
            return (char) clamp(toLong(b, p), Character.MIN_VALUE, Character.MAX_VALUE);
        } else if (t == String.class) {
            return toStringValue(b, p);
        } else if (t == byte[].class) {
            switch (ObjectFormat.typeAt(b, p)) {
            case 's':
            case 'b':
                return ObjectFormat.bytesAt(b, p);
            case 'a':
                return toArray(b, p, t);
            default:
                return null;
            }
        } else if (t.isArray()) {
            return ObjectFormat.typeAt(b, p) == 'a' ? toArray(b, p, t) : null;
        }
        return ObjectFormat.isObjectAt(b, p) ? make(b, p, t) : null;
    }

    /** A new array of the type 't', element by element (020-09, section 5.7). */
    private static Object toArray(byte[] b, int p, Class<?> t) {
        Class<?> e = t.getComponentType();
        int n = 0;
        for (int q = p + 1; (b[q] & 0xff) != ObjectFormat.ARRAY_END;
                q = ObjectFormat.valueEnd(b, q)) {
            n++;
        }
        Object a = Array.newInstance(e, n);
        int i = 0;
        for (int q = p + 1; (b[q] & 0xff) != ObjectFormat.ARRAY_END;
                q = ObjectFormat.valueEnd(b, q)) {
            Array.set(a, i++, convert(b, q, e));
        }
        return a;
    }

    static long clamp(long v, long least, long greatest) {
        return v < least ? least : v > greatest ? greatest : v;
    }

    /** As boolean: an integer not 0; a double not 0 and not NaN; Boolean.parseBoolean(). */
    static boolean toBoolean(byte[] b, int p) {
        switch (ObjectFormat.typeAt(b, p)) {
        case 'n':
            return ObjectFormat.booleanAt(b, p);
        case 'l':
            return ObjectFormat.integerAt(b, p) != 0;
        case 'd': {
            double x = Double.longBitsToDouble(ObjectFormat.doubleBitsAt(b, p));
            return x != 0.0 && !Double.isNaN(x);
        }
        case 's':
            return Boolean.parseBoolean(ObjectFormat.stringAt(b, p));
        default:
            return false;
        }
    }

    /**
     * As a long, before it is clamped to a narrower integer type (020-09, sections 5.4 and
     * 5.5): an integer; a double by Java's narrowing (toward zero, NaN 0, saturated); a
     * boolean 1 or 0; a text by section 5.5; else 0.
     */
    static long toLong(byte[] b, int p) {
        switch (ObjectFormat.typeAt(b, p)) {
        case 'l':
            return ObjectFormat.integerAt(b, p);
        case 'd':
            return (long) Double.longBitsToDouble(ObjectFormat.doubleBitsAt(b, p));
        case 'n':
            return ObjectFormat.booleanAt(b, p) ? 1 : 0;
        case 's':
            return parseLong(ObjectFormat.stringAt(b, p));
        default:
            return 0;
        }
    }

    /**
     * A text as an integer (020-09, section 5.5): trimmed; an optional sign and ASCII digits
     * exactly, saturated to long's range; else Double.parseDouble() and Java's narrowing;
     * else 0.
     */
    static long parseLong(String s) {
        String t = s.trim();
        int i = 0;
        boolean negative = false;
        if (i < t.length() && (t.charAt(i) == '+' || t.charAt(i) == '-')) {
            negative = t.charAt(i) == '-';
            i++;
        }
        boolean digits = i < t.length();
        for (int k = i; k < t.length() && digits; k++) {
            char c = t.charAt(k);
            digits = c >= '0' && c <= '9';
        }
        if (digits) {
            long v = 0;     // negative, to reach Long.MIN_VALUE
            for (int k = i; k < t.length(); k++) {
                int d = t.charAt(k) - '0';
                if (v < (Long.MIN_VALUE + d) / 10) {
                    return negative ? Long.MIN_VALUE : Long.MAX_VALUE;
                }
                v = v * 10 - d;
            }
            if (negative) {
                return v;
            }
            return v == Long.MIN_VALUE ? Long.MAX_VALUE : -v;
        }
        try {
            return (long) Double.parseDouble(t);
        } catch (NumberFormatException e) {
            return 0;
        }
    }

    /** As float (020-09, section 5.4): Float.parseFloat() for a text, rounded once. */
    static float toFloat(byte[] b, int p) {
        switch (ObjectFormat.typeAt(b, p)) {
        case 'l':
            return (float) ObjectFormat.integerAt(b, p);
        case 'd':
            return (float) Double.longBitsToDouble(ObjectFormat.doubleBitsAt(b, p));
        case 'n':
            return ObjectFormat.booleanAt(b, p) ? 1f : 0f;
        case 's':
            try {
                return Float.parseFloat(ObjectFormat.stringAt(b, p));
            } catch (NumberFormatException e) {
                return 0f;
            }
        default:
            return 0f;
        }
    }

    /** As double (020-09, section 5.4): its bits as stored for a double. */
    static double toDouble(byte[] b, int p) {
        switch (ObjectFormat.typeAt(b, p)) {
        case 'l':
            return (double) ObjectFormat.integerAt(b, p);
        case 'd':
            return Double.longBitsToDouble(ObjectFormat.doubleBitsAt(b, p));
        case 'n':
            return ObjectFormat.booleanAt(b, p) ? 1.0 : 0.0;
        case 's':
            try {
                return Double.parseDouble(ObjectFormat.stringAt(b, p));
            } catch (NumberFormatException e) {
                return 0.0;
            }
        default:
            return 0.0;
        }
    }

    /** As String (020-09, sections 5.4 and 5.6); null for an array or an object. */
    static String toStringValue(byte[] b, int p) {
        switch (ObjectFormat.typeAt(b, p)) {
        case 's':
            return ObjectFormat.stringAt(b, p);
        case 'l':
            return Long.toString(ObjectFormat.integerAt(b, p));
        case 'd':
            return Double.toString(Double.longBitsToDouble(ObjectFormat.doubleBitsAt(b, p)));
        case 'n':
            return ObjectFormat.booleanAt(b, p) ? "true" : "false";
        case 'b':
            return new String(ObjectFormat.bytesAt(b, p), StandardCharsets.UTF_8);
        default:
            return null;
        }
    }
}
