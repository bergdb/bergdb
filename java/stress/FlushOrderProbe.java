package bergdb.stream;

import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;

/** A small native-tracing workload: creation, rotation, durable append and deletion. */
public class FlushOrderProbe {
    public static void main(String[] args) throws Exception {
        File root = Files.createTempDirectory("bergdb-flush-probe-").toFile();
        File dir = new File(root, "parent/data");
        FileStream stream = new FileStream(dir);
        byte[] data = new byte[650000];
        Arrays.fill(data, (byte) 42);
        try {
            stream.append(data, 0, data.length);
            stream.pretruncate(400000);
        } finally { stream.close(); }
        stream = new FileStream(dir);
        try {
            byte[] tail = new byte[250000];
            stream.read(400000, tail, 0, tail.length);
            for (byte b : tail) if (b != 42) throw new AssertionError("wrong surviving byte");
            if (stream.getLength() != 650000 || stream.getFirstPos() != 400000) {
                throw new AssertionError("wrong recovered file positions");
            }
            System.out.println("FILESYSTEM " + Files.getFileStore(dir.toPath()).type());
        } finally { stream.close(); }
        System.out.println("DATA_DIRECTORY " + root.getAbsolutePath());
        System.out.println("FLUSH PROBE OK");
    }
}
