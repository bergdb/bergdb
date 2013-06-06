package kissdb.dev;

import javax.swing.JButton;
import javax.swing.JFrame;

/**
 * Executable class that displays a window with "Hello world!". Can be used to test whether 
 * the Java graphics environment works.
 * 
 * @author Frans Lundberg
 */
public class Swing {
    public static void main(String[] args) {
        System.out.println("==== " + Swing.class.getName() + " ====");
        System.out.println("Displays a JFrame with a button in it.");
        
        JFrame f = new JFrame(Swing.class.getName());
        f.getContentPane().add(new JButton("Hello world from Swing."));
        f.pack();
        f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        f.setVisible(true);
    }
}
