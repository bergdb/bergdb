import com.sun.source.tree.*;
import com.sun.source.util.*;

import javax.lang.model.element.*;
import javax.lang.model.type.*;
import javax.lang.model.util.*;
import javax.tools.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.stream.*;

/**
 * A source index for 005-10: every declaration in the BergDB sources (class,
 * method, constructor, field, initializer) with its position, and every
 * reference from one declaration to another, as javac resolves them. Unlike
 * the class files, it sees the uses of compile-time constants.
 *
 * Usage: java Index.java <out dir> <classpath> <source dir>...
 * Writes decls.tsv and refs.tsv.
 */
public class Index {
    static Trees trees;
    static Elements elements;
    static Types types;
    static final Map<Element, Integer> ids = new HashMap<>();
    static final List<String> declRows = new ArrayList<>();
    static final Map<Integer, List<Element>> overridden = new HashMap<>();
    static final Set<String> refRows = new LinkedHashSet<>();

    public static void main(String[] args) throws Exception {
        Path out = Paths.get(args[0]);
        String cp = args[1];
        List<File> files = new ArrayList<>();
        for (int i = 2; i < args.length; i++) {
            try (Stream<Path> s = Files.walk(Paths.get(args[i]))) {
                s.filter(p -> p.toString().endsWith(".java")).sorted()
                        .forEach(p -> files.add(p.toFile()));
            }
        }
        JavaCompiler jc = ToolProvider.getSystemJavaCompiler();
        StandardJavaFileManager fm = jc.getStandardFileManager(null, null, StandardCharsets.UTF_8);
        List<String> opts = Arrays.asList("--release", "8", "-cp", cp, "-proc:none",
                "-encoding", "UTF-8", "-nowarn", "-Xlint:-options", "-implicit:none");
        DiagnosticCollector<JavaFileObject> diags = new DiagnosticCollector<>();
        JavacTask task = (JavacTask) jc.getTask(null, fm, diags, opts, null,
                fm.getJavaFileObjectsFromFiles(files));
        Iterable<? extends CompilationUnitTree> units = task.parse();
        task.analyze();
        for (Diagnostic<?> d : diags.getDiagnostics()) {
            if (d.getKind() == Diagnostic.Kind.ERROR) {
                System.err.println(d);
            }
        }
        trees = Trees.instance(task);
        elements = task.getElements();
        types = task.getTypes();

        // First pass: declarations; second pass: references.
        for (CompilationUnitTree cu : units) {
            new Decls(cu).scan(cu, null);
        }
        for (CompilationUnitTree cu : units) {
            new Refs(cu).scan(cu, null);
        }
        // The methods each method overrides: ids of ours, or "lib".
        for (int i = 0; i < declRows.size(); i++) {
            List<Element> ov = overridden.get(i);
            String col = "";
            if (ov != null) {
                col = ov.stream().map(x -> ids.containsKey(x) ? String.valueOf(ids.get(x)) : "lib")
                        .distinct().collect(Collectors.joining(","));
            }
            declRows.set(i, declRows.get(i) + "\t" + col);
        }
        Files.createDirectories(out);
        Files.write(out.resolve("decls.tsv"), declRows, StandardCharsets.UTF_8);
        Files.write(out.resolve("refs.tsv"), refRows, StandardCharsets.UTF_8);
        System.out.println(files.size() + " files, " + declRows.size() + " declarations, "
                + refRows.size() + " references");
    }

    static String binaryName(TypeElement t) {
        return elements.getBinaryName(t).toString();
    }

    static String typeName(TypeMirror t) {
        TypeMirror e = types.erasure(t);
        if (e.getKind() == TypeKind.ARRAY) {
            return typeName(((ArrayType) e).getComponentType()) + "[]";
        }
        if (e.getKind() == TypeKind.DECLARED) {
            return binaryName((TypeElement) ((DeclaredType) e).asElement());
        }
        return e.toString();
    }

    /** Owner class, name and parameter types: how ProGuard names a member. */
    static String key(Element e) {
        switch (e.getKind()) {
            case CLASS: case INTERFACE: case ENUM: case ANNOTATION_TYPE:
                return binaryName((TypeElement) e) + "\t<class>";
            case METHOD: case CONSTRUCTOR: {
                ExecutableElement m = (ExecutableElement) e;
                String params = m.getParameters().stream().map(p -> typeName(p.asType()))
                        .collect(Collectors.joining(","));
                String name = e.getKind() == ElementKind.CONSTRUCTOR ? "<init>" : e.getSimpleName().toString();
                return binaryName((TypeElement) e.getEnclosingElement()) + "\t" + name + "(" + params + ")";
            }
            case FIELD: case ENUM_CONSTANT:
                return binaryName((TypeElement) e.getEnclosingElement()) + "\t" + e.getSimpleName();
            default:
                return null;
        }
    }

    static abstract class Base extends TreePathScanner<Void, Void> {
        final CompilationUnitTree cu;
        final SourcePositions pos;
        final LineMap lines;
        final String file;

        Base(CompilationUnitTree cu) {
            this.cu = cu;
            this.pos = trees.getSourcePositions();
            this.lines = cu.getLineMap();
            this.file = cu.getSourceFile().toUri().getPath();
        }

        /** The innermost declaration (member or class) that holds the current path. */
        Element enclosing() {
            for (TreePath p = getCurrentPath(); p != null; p = p.getParentPath()) {
                Tree t = p.getLeaf();
                if (t instanceof MethodTree || t instanceof ClassTree) {
                    Element e = trees.getElement(p);
                    if (e != null && ids.containsKey(e)) {
                        return e;
                    }
                }
                if (t instanceof VariableTree) {
                    Element e = trees.getElement(p);
                    if (e != null && (e.getKind() == ElementKind.FIELD
                            || e.getKind() == ElementKind.ENUM_CONSTANT) && ids.containsKey(e)) {
                        return e;
                    }
                }
                if (t instanceof BlockTree && p.getParentPath() != null
                        && p.getParentPath().getLeaf() instanceof ClassTree) {
                    // An initializer block: it belongs to the class.
                    continue;
                }
            }
            return null;
        }
    }

    static class Decls extends Base {
        Decls(CompilationUnitTree cu) { super(cu); }

        void declare(Tree t, Element e) {
            if (e == null || ids.containsKey(e)) {
                return;
            }
            String k = key(e);
            if (k == null) {
                return;
            }
            int id = ids.size();
            ids.put(e, id);
            long start = pos.getStartPosition(cu, t);
            long end = pos.getEndPosition(cu, t);
            Element enc = e.getEnclosingElement();
            Integer encId = enc == null ? null : ids.get(enc);
            String mods = e.getModifiers().stream().map(Modifier::toString).collect(Collectors.joining(" "));
            boolean constant = e instanceof VariableElement && ((VariableElement) e).getConstantValue() != null;
            boolean implicit = start < 0 || (t instanceof MethodTree && isImplicitConstructor((MethodTree) t, e));
            declRows.add(id + "\t" + e.getKind() + "\t" + k + "\t" + file + "\t"
                    + (start < 0 ? -1 : lines.getLineNumber(start)) + "\t"
                    + (end < 0 ? -1 : lines.getLineNumber(end)) + "\t" + start + "\t" + end + "\t"
                    + mods + "\t" + constant + "\t" + implicit + "\t" + (encId == null ? -1 : encId));
            if (e.getKind() == ElementKind.METHOD) {
                overridden.put(id, overriddenBy((ExecutableElement) e));
            }
        }

        List<Element> overriddenBy(ExecutableElement m) {
            TypeElement owner = (TypeElement) m.getEnclosingElement();
            List<Element> result = new ArrayList<>();
            Deque<TypeMirror> todo = new ArrayDeque<>(types.directSupertypes(owner.asType()));
            Set<String> seen = new HashSet<>();
            while (!todo.isEmpty()) {
                TypeMirror t = todo.pop();
                if (t.getKind() != TypeKind.DECLARED) {
                    continue;
                }
                TypeElement te = (TypeElement) ((DeclaredType) t).asElement();
                if (!seen.add(te.getQualifiedName().toString())) {
                    continue;
                }
                for (Element x : te.getEnclosedElements()) {
                    if (x.getKind() == ElementKind.METHOD
                            && elements.overrides(m, (ExecutableElement) x, owner)) {
                        result.add(x);
                    }
                }
                todo.addAll(types.directSupertypes(t));
            }
            return result;
        }

        boolean isImplicitConstructor(MethodTree t, Element e) {
            if (e.getKind() != ElementKind.CONSTRUCTOR) {
                return false;
            }
            long start = pos.getStartPosition(cu, t);
            long end = pos.getEndPosition(cu, t);
            // javac adds a default constructor at the position of the class.
            Tree cls = getCurrentPath().getParentPath().getLeaf();
            return start == pos.getStartPosition(cu, cls) || end < 0;
        }

        @Override public Void visitClass(ClassTree t, Void v) {
            declare(t, trees.getElement(getCurrentPath()));
            return super.visitClass(t, v);
        }

        @Override public Void visitMethod(MethodTree t, Void v) {
            declare(t, trees.getElement(getCurrentPath()));
            return super.visitMethod(t, v);
        }

        @Override public Void visitVariable(VariableTree t, Void v) {
            Element e = trees.getElement(getCurrentPath());
            if (e != null && (e.getKind() == ElementKind.FIELD || e.getKind() == ElementKind.ENUM_CONSTANT)) {
                declare(t, e);
            }
            return super.visitVariable(t, v);
        }
    }

    static class Refs extends Base {
        Refs(CompilationUnitTree cu) { super(cu); }

        void ref(Element to) {
            if (to == null) {
                return;
            }
            if (to.getKind() == ElementKind.CONSTRUCTOR || to.getKind() == ElementKind.METHOD
                    || to.getKind() == ElementKind.FIELD || to.getKind() == ElementKind.ENUM_CONSTANT
                    || to.getKind().isClass() || to.getKind().isInterface()) {
                Integer toId = ids.get(to);
                if (to instanceof ExecutableElement && toId == null) {
                    return;
                }
                if (toId == null) {
                    return;
                }
                Element from = enclosing();
                int fromId = from == null ? -1 : ids.get(from);
                if (fromId != toId) {
                    refRows.add(fromId + "\t" + toId);
                }
            }
        }

        @Override public Void visitIdentifier(IdentifierTree t, Void v) {
            ref(trees.getElement(getCurrentPath()));
            return super.visitIdentifier(t, v);
        }

        @Override public Void visitMemberSelect(MemberSelectTree t, Void v) {
            ref(trees.getElement(getCurrentPath()));
            return super.visitMemberSelect(t, v);
        }

        @Override public Void visitMemberReference(MemberReferenceTree t, Void v) {
            ref(trees.getElement(getCurrentPath()));
            return super.visitMemberReference(t, v);
        }

        @Override public Void visitNewClass(NewClassTree t, Void v) {
            ref(trees.getElement(getCurrentPath()));
            return super.visitNewClass(t, v);
        }
    }
}
