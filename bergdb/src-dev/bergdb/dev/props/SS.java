package bergdb.dev.props;

import java.util.Locale;

/**
 * The SS (stream size) property; the geometric mean of SS1, SS2, SS3, and SS4.
 * 
 * @author Frans Lundberg
 */
public class SS {
    String shortResultText;
    String longResultText;
    
    public double go() {
        double ss1 = new SS1().go();
        double ss2 = new SS2().go();
        double ss3 = new SS3().go();
        double ss4 = new SS4().go();
        double geoMean = Math.pow(ss1 * ss2 * ss3 * ss4, 1.0 / 4.0);
        
        longResultText = String.format(Locale.US, "SS:%.2f (%.2f, %.2f, %.2f, %.2f)", 
                geoMean, ss1, ss2, ss3, ss4);
        shortResultText = String.format(Locale.US, "SS:%.2f", geoMean);
        
        return geoMean;
    }
    
    public static void main(String[] args) {
        SS ss = new SS();
        ss.go();
        System.out.println(ss.longResultText);
    }
}

/*

150515 got: SS:1.48 (1.16, 1.26, 1.60, 2.06)

150422 got: SS:1.56 (1.25, 1.34, 1.66, 2.12)

*/