package bergdb.storage;

public class BadMagicBytes extends StreamFormatException {
    private static final long serialVersionUID = 1L;

    public BadMagicBytes(String message) {
        super(message);
    }
}
