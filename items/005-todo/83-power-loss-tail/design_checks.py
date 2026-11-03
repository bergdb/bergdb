#!/usr/bin/env python3
"""Item-local arithmetic/framing checks for 005-83, proposal sections 3–6.

This is not a database parser or filesystem emulator. Assertions deliberately
remain active without relying on Python's optional assert statement.
"""
import hashlib
import struct

DB_ID = bytes(range(16))
HEADER = 64
FOOTER = 48
MIN_RECORD = 120
MAX_RECORD = 2**31 - 9  # Integer.MAX_VALUE - 8
W = 8_000_000
META_DISTANCE = 200_000
checks = 0


def require(condition, message):
    global checks
    checks += 1
    if not condition:
        raise RuntimeError(message)


def digest(domain, data, identity=DB_ID):
    return hashlib.sha256(b"bergdb155/" + domain + b"\0" + identity + data).digest()


def encode_record(position, tt, body):
    # Toy body: node terminator + zero got-dirty count, then arbitrary payload.
    # It exercises framing only; the payload is not a production node encoding.
    body = bytes(8) + body
    body += bytes((-len(body)) % 8)
    size = HEADER + len(body) + FOOTER
    header = bytearray(HEADER)
    struct.pack_into("<IBBHQQqQQ", header, 0,
                     size, 6, 0, HEADER, tt, 128, -1, position, 0)
    header[48:64] = digest(b"header", header)[:16]
    footer = bytearray(FOOTER)
    struct.pack_into("<I", footer, 32, size)
    footer[36:40] = b"bEND"
    footer[47] = 10
    record = header + body + footer
    record[-FOOTER:-FOOTER + 32] = digest(b"record", record)
    return bytes(record)


class Damaged(Exception):
    pass


class Refused(Exception):
    pass


def decode_record(data, position, identity=DB_ID):
    if len(data) < HEADER:
        raise Damaged("short header")
    header = bytearray(data[:HEADER])
    stored_header_hash = bytes(header[48:64])
    header[48:64] = bytes(16)
    if digest(b"header", header, identity)[:16] != stored_header_hash:
        raise Damaged("header digest")
    size, version, kind, hsize, tt, sp, top, ownpos, reserved = struct.unpack_from(
        "<IBBHQQqQQ", header)
    if version != 6 or kind != 0 or hsize != HEADER:
        raise Refused("unsupported valid header")
    if size < MIN_RECORD or size > MAX_RECORD or size % 8:
        raise Refused("digest-valid impossible size")
    if ownpos != position or reserved:
        raise Refused("digest-valid impossible position/reserved")
    if size > len(data):  # Subtraction/length check, never allocate declared size.
        raise Damaged("incomplete body")
    record = bytearray(data[:size])
    repeated = struct.unpack_from("<I", record, size - FOOTER + 32)[0]
    if repeated != size or record[-12:-8] != b"bEND" or record[-1] != 10:
        raise Damaged("footer")
    if any(record[-8:-1]):
        raise Damaged("footer reserved")
    stored_hash = bytes(record[-FOOTER:-FOOTER + 32])
    record[-FOOTER:-FOOTER + 32] = bytes(32)
    if digest(b"record", record, identity) != stored_hash:
        raise Damaged("whole record digest")
    return size, tt


def encode_meta(position, last_position):
    meta = bytearray(128)
    meta[:4] = b"berg"
    struct.pack_into("<IQQ", meta, 4, 155, 100, last_position)
    meta[24:40] = DB_ID
    struct.pack_into("<IHQI", meta, 40, 50_000_000, 8, position, W)
    meta[127] = 10
    meta[95:127] = digest(b"meta", meta, b"")
    return bytes(meta)


def valid_meta(data, position):
    if len(data) != 128:
        return False
    meta = bytearray(data)
    stored = bytes(meta[95:127])
    meta[95:127] = bytes(32)
    return (stored == digest(b"meta", meta, b"")
            and struct.unpack_from("<Q", meta, 46)[0] == position
            and struct.unpack_from("<I", meta, 54)[0] == W
            and meta[:4] == b"berg" and meta[127] == 10)


def rejected(data, position=128):
    try:
        decode_record(data, position)
        return False
    except (Damaged, Refused):
        return True


def prefix_end(data, start=128):
    offset = 0
    times = []
    while offset < len(data):
        try:
            size, tt = decode_record(data[offset:], start + offset)
        except Damaged:
            break
        times.append(tt)
        offset += size
    return start + offset, times


def check_frames():
    count = 0
    for body_size in (0, 1, 8, 63, 512, 4096):
        frame = encode_record(128, 100, bytes((i % 251) + 1 for i in range(body_size)))
        require(decode_record(frame, 128) == (len(frame), 100), "round trip")
        for index in range(len(frame)):
            changed = bytearray(frame)
            changed[index] ^= 1
            require(rejected(changed), "one-byte bit flip escaped detection")
            count += 1
        for length in range(len(frame)):
            require(rejected(frame[:length]), "incomplete frame accepted")
        for index, value in enumerate(frame):
            if value:
                changed = bytearray(frame)
                changed[index] = 0
                require(rejected(changed), "zero hole escaped detection")
        require(rejected(frame, 136), "copied frame position accepted")
        try:
            decode_record(frame, 128, bytes(16))
        except Damaged:
            pass
        else:
            raise RuntimeError("wrong database identity accepted")
    # Valid header declaring an enormous incomplete body: bounded read check.
    frame = bytearray(encode_record(128, 100, b""))
    struct.pack_into("<I", frame, 0, MAX_RECORD - MAX_RECORD % 8)
    frame[48:64] = bytes(16)
    frame[48:64] = digest(b"header", frame[:HEADER])[:16]
    require(rejected(frame), "huge incomplete record accepted")
    meta = encode_meta(200_000, 128)
    require(valid_meta(meta, 200_000), "meta round trip")
    require(not valid_meta(meta, 400_000), "copied meta accepted")
    for index in range(128):
        changed = bytearray(meta)
        changed[index] ^= 1
        require(not valid_meta(changed, 200_000), "meta bit flip accepted")
    print(f"Framing: {count} single-bit changes; all cuts, zero holes and meta changes rejected")


def check_prefix():
    first = encode_record(128, 100, b"acknowledged")
    second = encode_record(128 + len(first), 101, b"depends on first")
    third = encode_record(128 + len(first) + len(second), 102, b"depends on second")
    changed = bytearray(second)
    changed[HEADER + 8] ^= 1
    image = first + changed + third
    end, times = prefix_end(image)
    require((end, times) == (128 + len(first), [100]), "skipped failed record")
    require(decode_record(third, 128 + len(first) + len(second))[1] == 102,
            "negative control later record must be valid")
    # A later checksummed meta pointing at third does not certify second.
    later_meta = encode_meta(200_000, 128 + len(first) + len(second))
    require(valid_meta(later_meta, 200_000), "negative control later meta")
    print("Prefix: first bad record stops recovery despite intact later record/meta")


def anchor_end(c, w, spacing, size):
    target = c - w
    if target < size:
        return 0  # Retain creation area.
    return ((target - size) // spacing) * spacing + size


def check_anchor_geometry():
    cases = 0
    # Scaled units: W=4, meta size=1, distance=2. F can advance inside
    # a still-uncommitted huge record; E may then lie well before F.
    for c in range(25):
        for forced in range(c, 41):
            for length in range(forced, forced + 5):
                end = anchor_end(c, 4, 2, 1)
                require(end <= max(0, length - 4), "anchor may be unforced")
                for recovered in range(c, length + 1):
                    require(end <= max(0, recovered - 4), "repair lost anchor")
                    cases += 1
    c, d, length, w = 5_000, 22_000, 23_500, 4_096
    unsafe = anchor_end(d, w, 512, 128)
    safe = anchor_end(c, w, 512, 128)
    require(unsafe > c, "D-based negative case disappeared")
    require(safe <= max(0, c - w), "C-based retained anchor unsafe")
    # A write larger than W can damage bytes below L-W.
    f, length, assumed_w = 100, 200, 8
    damaged_position = 110
    require(f <= damaged_position < length - assumed_w, "uncapped negative case")
    print(f"Anchors: {cases} recovery-length cases preserve the C-based anchor")
    print(f"Negative controls: D-based anchor ends at {unsafe}, beyond recovered EOF {c}; "
          f"C-based anchor ends at {safe}; uncapped writes invalidate L-W")


def check_removals():
    def contiguous(names):
        return names == list(range(len(names)))
    names = list(range(6))
    for victim in (5, 4, 3):
        names.remove(victim)
        require(contiguous(names), "highest-first removal made a hole")
    wrong_order = list(range(6))
    wrong_order.remove(3)
    require(not contiguous(wrong_order), "lowest-first negative case")
    print("Removal: every highest-first interruption leaves a prefix; lowest-first does not")


def main():
    check_frames()
    check_prefix()
    check_anchor_geometry()
    check_removals()
    print(f"DESIGN CHECKS OK ({checks} conditions; model only, not production recovery)")


if __name__ == "__main__":
    main()
