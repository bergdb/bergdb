package kissdb.dev;

/**
 * Dummy class to test Javadoc.
 * 
 * @version beta
 * @since 2013.2
 * @author Frans Lundberg
 */
public class DummyForJavadoc {
    
    /**
     * This methods is in beta - not stable yet.
     *
     * @since 2013.1
     */
    public void method1() {}
}

/*
== 130404 ==
Thought on API doc. How to select subset of public methods for an API. 
It would be nice to be able to have multiple APIs from same code. Multiple
subsets of included methods.

Maybe marked with Javadoc tags like this:

@api pub   - Marks class/interface/methods as part of "pub" API.
@api !pub  - Marker that says that class/interface/method is not part of "pub" API.

Not difficult to add to Javadoc tool (so it is accepted and included in html),
but special doclet required to make method appear or not based on tag.

== Javadoc ==
Note. "@version beta" seems like a good way to indicate a beta-feature that is not part
of the stable public interface. Introducing our own tag requires options when making the Javadoc.
We could have "@version alpha" too, but I believe this is not necessary. We can implement methods
in implementing classes (kissdb.pubimp) requiring a cast to try "alpha" stuff.

Classes/interfaces/methods marked with @beta can change their API, or be removed. They should
not be considered a part of the ordinary stable API, even if they are included in a stable release.

If a beta feature is later included, the @version tag is replaced by a "@since 2013.4" tag 
(as an example).

Note! @beta for method results in Javadoc tool warning:

[javadoc] /f/files/kissdb/p/KissDB/src/kissdb/dev/DummyForJavadoc.java:18: 
warning - Tag @version cannot be used in method documentation.  It can only be used in 
the following types of documentation: overview, package, class/interface.

*/