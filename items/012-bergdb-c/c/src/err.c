/* err: the library's errors; see err.h. */
#include "err.h"
#include <stdio.h>

enum err_code err_setv(struct err *e, enum err_code code, const char *java,
        const char *format, va_list args) {
    e->code = code;
    e->java = java;
    vsnprintf(e->text, sizeof e->text, format, args);
    return code;
}

enum err_code err_set(struct err *e, enum err_code code, const char *java,
        const char *format, ...) {
    va_list args;
    va_start(args, format);
    err_setv(e, code, java, format, args);
    va_end(args);
    return code;
}

void err_clear(struct err *e) {
    e->code = ERR_OK;
    e->java = "";
    e->text[0] = '\0';
}

const char *err_code_name(enum err_code code) {
    switch (code) {
    case ERR_OK: return "OK";
    case ERR_IO: return "IO";
    case ERR_FORMAT: return "FORMAT";
    case ERR_ARG: return "ARG";
    case ERR_NOT_AVAILABLE: return "NOT_AVAILABLE";
    case ERR_NOMEM: return "NOMEM";
    case ERR_LIMIT: return "LIMIT";
    case ERR_IN_USE: return "IN_USE";
    }
    return "?";
}
