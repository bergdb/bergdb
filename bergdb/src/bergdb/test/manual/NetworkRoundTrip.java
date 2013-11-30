package bergdb.test.manual;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;

import javax.net.ServerSocketFactory;
import javax.net.SocketFactory;

/**
 * Tests TCP network round-trip time.
 * 
 * @author Frans Lundberg
 */
public class NetworkRoundTrip {
    String ip;
    int port;
    
    void go(String[] args) throws IOException {
        String runType = args[0];
        
        ip = "127.0.0.1";
        port = 12300;
        
        if (args.length > 1) {
            ip = args[1];
        }
        
        if (args.length > 2) {
            port = Integer.parseInt(args[2]);
        }
        
        if (runType.equals("server")) {
            server();
        } else if (runType.equals("client")) {
            client();
        } else {
            throw new RuntimeException("Bad run time, should be server/client.");
        }
    }
    
    void server() throws IOException {
        InetAddress address = InetAddress.getByName(ip);
        ServerSocket ss = ServerSocketFactory.getDefault()
                .createServerSocket(port, 123, address);
        
        while (true) {
            ss.setPerformancePreferences(0, 10, 0);
            
            final Socket socket = ss.accept();
            System.out.println("Client " + socket.getRemoteSocketAddress().toString() + " connected.");
            socket.setPerformancePreferences(0, 10, 0);
            socket.setTcpNoDelay(true);
            
            Thread t = new Thread(new Runnable() {
                public void run() {
                    try {
                        serviceClient(socket);
                    } catch (IOException e) {
                        try {
                            socket.close();
                        } catch (IOException e1) {
                            // empty
                        }
                    }
                }
            });
           
            t.setDaemon(true);
            t.start();
        }
    }
    
    /**
     * Services a client connection.
     * @throws IOException 
     */
    void serviceClient(Socket socket) throws IOException {
        InputStream in = socket.getInputStream();
        OutputStream out = socket.getOutputStream();
        
        while (true) {
            int b = in.read();
            out.write(b);
            out.flush();
        }
    }
    
    void client() throws UnknownHostException, IOException {
        Socket socket = SocketFactory.getDefault().createSocket();
        
        socket.setPerformancePreferences(0, 10, 0);
        socket.setTcpNoDelay(true);
        InetSocketAddress address = new InetSocketAddress(ip, port);
        socket.connect(address, 2000);
        
        InputStream in = socket.getInputStream();
        OutputStream out = socket.getOutputStream();
        
        pingPong(in, out, 10);
        
        long t0 = System.nanoTime();
        double time = 0.0;
        long count = 0;
        int bunchSize = 10;
        
        while (true) {
            pingPong(in, out, bunchSize);
            count += bunchSize;
            time = (System.nanoTime() - t0) * 1e-9;
            if (time > 2.0) {
                break;
            }
        }
        
        System.out.printf("Time: %.2f s. Per round-trip: %.6f s.\n", time, time / count);
    }
    
    void pingPong(InputStream in, OutputStream out, int n) throws IOException {
        for (int i = 0; i < n; i++) {
            byte data = (byte) (i % 128);
            
            out.write(data);
            out.flush();
            int b = in.read();
            
            if (b != data) {
                throw new RuntimeException("Bad response from server, expected " 
                        + data + ", got " + b);
            }
        }
    }

    public static void main(String[] args) throws IOException {
        if (args.length < 1) {
            System.out.println("One of:");
            System.out.println("  server [<ip> [<port>]]");
            System.out.println("  client [<ip> [<port>]]");
            System.out.println("Default ip parameter is 127.0.0.1, default port is 12300");
            return;
        }
        
        new NetworkRoundTrip().go(args);
    }
}

/*

131130. Typical round-trip time on cissi: 52 us. Not bad :-).
Server started with: [$ j bergdb.test.java.NetworkRoundTrip server &]
I get the same result when I comment out calls to setPerformancePreferences() and setTcpNoDelay().

*/