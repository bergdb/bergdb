/*
 * recover: a start's recovery of the stream, with its fill, ported from
 * Java's RecoverableStream.recover (bergdb 012-10; 012-02, 4.4): the last
 * valid meta block read before anything is written (005-40); a meta block
 * that the end of the stream cuts, or is at, completed from the fill-out
 * template (invalid, its last byte 0); the in-memory block a copy of the
 * last valid one; and the record that the end cuts, from the record that
 * block names: its size field and byte 4 completed if fewer than 5 of its
 * bytes exist (transHeaderFixBytes), the rest zeros, appended through
 * rs_append without its checks, so that the meta blocks it reaches are
 * written from the in-memory block, valid, as Java writes them. The record
 * so completed ends in 0: failed, skipped by every walk. Prefix rcv_.
 *
 * What a start writes: the creation on an empty stream (the database's,
 * 012-09) and this fill after a crash; nothing else (012-02, 8.14). The
 * fill goes to the stream's write buffer, written at the next flush, sync
 * or close, as Java's BufferedStream writes it.
 */
#ifndef BERGDB_RECOVER_H
#define BERGDB_RECOVER_H

#include "err.h"
#include "rstream.h"

/* RecoverableStream.recover on r's stream: *plan what it found and did (as
 * rs_plan_recovery's, whose numbers it must equal). Refused before anything
 * is written: no valid meta block (ERR_FORMAT, "StreamFormatException"), a
 * block with bad magic bytes or another version (rs_read_meta_block's). A
 * bad size of the cut record ("Bad transaction size") is refused after the
 * meta block's fill, as Java's. The stream's errors as they are. */
enum err_code rcv_recover(struct rs *r, struct rs_recovery *plan, struct err *e);

#endif
