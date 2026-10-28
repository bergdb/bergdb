/*
 * err: the library's errors (bergdb 012-06). A function that can fail
 * returns an enum err_code, ERR_OK (0) or the error, and fills the struct
 * err its caller gives: the code; the exception that Java throws in the
 * same case, by its simple class name (Java's semantics in C, rule 12: an
 * exception becomes a return code), which the tests compare and the
 * scanner prints; and a text. No allocation: the text is in the struct, cut
 * at its size. Prefix err_.
 *
 * The codes follow 012-03's plan of the API's error enum (IO, FORMAT, ARG,
 * NOT_AVAILABLE, NOMEM, ...); include/bergdb.h maps them once it exists.
 * Java's exceptions of the reader, and their codes:
 *
 *   IOException, EOFException, StreamIoException          ERR_IO
 *   StreamFormatException, VersioningStreamException,
 *   BadMagicBytes, StreamChecksumException                ERR_FORMAT
 *   BadDirStateException (a directory whose files are
 *   not in a valid state; an IOException in Java)          ERR_FORMAT
 *   ReadBelowFirstPosException                             ERR_NOT_AVAILABLE
 *   IllegalArgumentException                               ERR_ARG
 *   what Java throws on corrupt bytes without meaning to:
 *   ArrayIndexOutOfBoundsException, NegativeArraySize-
 *   Exception, and an AssertionError of an assert on the
 *   stream's bytes (Java runs with -ea in its gates and
 *   its scanner, so the assert is a check there)           ERR_FORMAT
 *   OutOfMemoryError (a failed allocation)                 ERR_NOMEM
 *
 * And of the writer (012-09):
 *
 *   DbException of a limit (DbClock's range, 005-18; the
 *   record limit, 005-17; the dirty nodes, 005-31; the top
 *   node ordinals, 005-02)                                 ERR_LIMIT
 *   DirectoryInUseException (FileStream's lock, 005-63)    ERR_IN_USE
 *   RerunException (the STM)                               ERR_RERUN
 *   IllegalDbStateException, DbStoppingException           ERR_STATE
 *   DbFailedException (005-01, 005-30)                     ERR_FAILED
 *   DatabaseNotCreatedException (005-33)                   ERR_NOT_CREATED
 */
#ifndef BERGDB_ERR_H
#define BERGDB_ERR_H

#include <stdarg.h>

enum err_code {
    ERR_OK = 0,
    ERR_IO,             /* a read failed, or the end of the stream */
    ERR_FORMAT,         /* the stream is corrupt, or of another version */
    ERR_ARG,            /* an argument out of range, as IllegalArgumentException */
    ERR_NOT_AVAILABLE,  /* a position before the stream's first position */
    ERR_NOMEM,          /* an allocation failed */
    ERR_LIMIT,          /* a limit of the database refuses a transaction (012-09: Java's
                           DbException, BERGDB_LIMIT): a clock time out of range, no
                           time left (005-18) */
    ERR_IN_USE,         /* another stream holds the directory's lock (012-09: Java's
                           DirectoryInUseException, BERGDB_IN_USE) */
    ERR_RERUN,          /* the STM refuses a transaction (012-09 proper: Java's
                           RerunException, BERGDB_RERUN) */
    ERR_STATE,          /* the database is not active (IllegalDbStateException,
                           DbStoppingException; BERGDB_STATE) */
    ERR_FAILED,         /* the database has failed (DbFailedException; BERGDB_FAILED) */
    ERR_NOT_CREATED     /* an incomplete creation (DatabaseNotCreatedException, 005-33;
                           BERGDB_NOT_CREATED) */
};

#define ERR_TEXT 240

struct err {
    enum err_code code;
    const char *java;       /* Java's exception, its simple class name; "" for ERR_OK */
    char text[ERR_TEXT];    /* what failed, as Java's message says it where it can */
};

/* Sets the error and returns its code. The text is formatted as by
 * printf. */
enum err_code err_set(struct err *e, enum err_code code, const char *java,
        const char *format, ...);

/* As err_set, with a va_list. */
enum err_code err_setv(struct err *e, enum err_code code, const char *java,
        const char *format, va_list args);

/* Clears the error: ERR_OK, no exception, an empty text. */
void err_clear(struct err *e);

/* The name of a code: "OK", "IO", "FORMAT", ... */
const char *err_code_name(enum err_code code);

#endif
