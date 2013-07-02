/*
NOTE, taken from http://www.javapractices.com/topic/TopicAction.do?Id=28.
"Implementing hashCode", Feb 2012.
 */

package bergdb.common;

import java.lang.reflect.Array;

/**
* Collected methods which allow easy implementation of <code>hashCode</code>.
*
* Example use case:
* <pre>
*  public int hashCode(){
*    int result = HashCodeUtil.SEED;
*    //collect the contributions of various fields
*    result = HashCodeUtil.hash(result, fPrimitive);
*    result = HashCodeUtil.hash(result, fObject);
*    result = HashCodeUtil.hash(result, fArray);
*    return result;
*  }
* </pre>
*/
public final class HashCodeUtil {

  /**
  * An initial value for a <code>hashCode</code>, to which is added contributions
  * from fields. Using a non-zero value decreases collisons of <code>hashCode</code>
  * values.
  */
  public static final int SEED = 23;

  /**
  * booleans.
  */
  public static long hash(long aSeed, boolean aBoolean ) {
    return firstTerm( aSeed ) + ( aBoolean ? 1 : 0 );
  }

  /**
  * chars.
  */
  public static long hash(long aSeed, char aChar ) {
    return firstTerm(aSeed) + aChar;
  }

  /**
  * ints.
  */
  public static long hash(long aSeed, int aInt ) {
    /*
    * Implementation Note
    * Note that byte and short are handled by this method, through
    * implicit conversion.
    */
    return firstTerm(aSeed) + aInt;
  }

  /**
  * longs.
  */
  public static long hash( int aSeed , long aLong ) {
    return firstTerm(aSeed)  + aLong;
  }

  /**
  * floats.
  */
  public static long hash(long aSeed , float aFloat ) {
    return hash(aSeed, Float.floatToIntBits(aFloat) );
  }

  /**
  * doubles.
  */
  public static long hash( int aSeed , double aDouble ) {
    return hash( aSeed, Double.doubleToLongBits(aDouble) );
  }

  /**
  * <code>aObject</code> is a possibly-null object field, and possibly an array.
  *
  * If <code>aObject</code> is an array, then each element may be a primitive
  * or a possibly-null object.
  */
  public static long hash(long aSeed , Object aObject ) {
    long result = aSeed;
    if ( aObject == null) {
      result = hash(result, 0);
    }
    else if ( ! isArray(aObject) ) {
      result = hash(result, aObject.hashCode());
    }
    else {
      int length = Array.getLength(aObject);
      for ( int idx = 0; idx < length; ++idx ) {
        Object item = Array.get(aObject, idx);
        //recursive call!
        result = hash(result, item);
      }
    }
    return result;
  }


  /// PRIVATE ///
  private static final long fODD_PRIME_NUMBER = 37;

  private static final long firstTerm(long aSeed ){
    return fODD_PRIME_NUMBER * aSeed;
  }

  private static boolean isArray(Object aObject){
    return aObject.getClass().isArray();
  }
}
