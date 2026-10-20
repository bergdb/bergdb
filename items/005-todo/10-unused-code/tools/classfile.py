"""A minimal Java class file reader: names, members, annotations, references.

Enough for the 005-10 analysis: the class's name, super class, interfaces,
source file, its fields and methods with their access flags, descriptors
and Nano annotations, and the classes its constant pool names.
"""

import os
import re
import struct

ACC_PUBLIC, ACC_PRIVATE, ACC_PROTECTED, ACC_STATIC = 0x1, 0x2, 0x4, 0x8
ACC_FINAL, ACC_SYNTHETIC, ACC_BRIDGE = 0x10, 0x1000, 0x40
ACC_INTERFACE, ACC_ABSTRACT, ACC_ANNOTATION, ACC_ENUM = 0x200, 0x400, 0x2000, 0x4000


class Reader:
    def __init__(self, data):
        self.d = data
        self.p = 0

    def u1(self):
        v = self.d[self.p]
        self.p += 1
        return v

    def u2(self):
        v = struct.unpack_from(">H", self.d, self.p)[0]
        self.p += 2
        return v

    def u4(self):
        v = struct.unpack_from(">I", self.d, self.p)[0]
        self.p += 4
        return v

    def bytes(self, n):
        v = self.d[self.p:self.p + n]
        self.p += n
        return v


def parse(path):
    r = Reader(open(path, "rb").read())
    assert r.u4() == 0xCAFEBABE, path
    r.u2()
    major = r.u2()
    n = r.u2()
    cp = [None] * n
    i = 1
    while i < n:
        tag = r.u1()
        if tag == 1:
            cp[i] = ("utf8", r.bytes(r.u2()).decode("utf-8", "replace"))
        elif tag in (3, 4):
            cp[i] = ("num", r.u4())
        elif tag in (5, 6):
            cp[i] = ("num", r.bytes(8))
            i += 1
        elif tag == 7:
            cp[i] = ("class", r.u2())
        elif tag == 8:
            cp[i] = ("string", r.u2())
        elif tag in (9, 10, 11):
            cp[i] = ({9: "field", 10: "method", 11: "imethod"}[tag], r.u2(), r.u2())
        elif tag == 12:
            cp[i] = ("nat", r.u2(), r.u2())
        elif tag == 15:
            cp[i] = ("mhandle", r.u1(), r.u2())
        elif tag == 16:
            cp[i] = ("mtype", r.u2())
        elif tag in (17, 18):
            cp[i] = ("dyn", r.u2(), r.u2())
        elif tag in (19, 20):
            cp[i] = ("modpkg", r.u2())
        else:
            raise ValueError("bad tag %d in %s" % (tag, path))
        i += 1

    def utf(k):
        return cp[k][1]

    def cname(k):
        return utf(cp[k][1]).replace("/", ".")

    access = r.u2()
    this = cname(r.u2())
    sk = r.u2()
    sup = cname(sk) if sk else None
    interfaces = [cname(r.u2()) for _ in range(r.u2())]

    def annotation():
        t = utf(r.u2())
        vals = {}
        for _ in range(r.u2()):
            name = utf(r.u2())
            vals[name] = element()
        return (t, vals)

    def element():
        tag = chr(r.u1())
        if tag in "BCDFIJSZ":
            r.u2()
            return None
        if tag == "s":
            return utf(r.u2())
        if tag == "e":
            r.u2()
            return utf(r.u2())
        if tag == "c":
            return utf(r.u2())
        if tag == "@":
            return annotation()
        if tag == "[":
            return [element() for _ in range(r.u2())]
        raise ValueError(tag)

    def attributes():
        out = {}
        for _ in range(r.u2()):
            name = utf(r.u2())
            length = r.u4()
            end = r.p + length
            if name in ("RuntimeVisibleAnnotations", "RuntimeInvisibleAnnotations"):
                out.setdefault("annotations", []).extend(
                    annotation() for _ in range(r.u2()))
            elif name == "SourceFile":
                out["source"] = utf(r.u2())
            elif name == "ConstantValue":
                out["constant"] = True
            elif name == "InnerClasses":
                inner = []
                for _ in range(r.u2()):
                    ic, oc, nm, fl = r.u2(), r.u2(), r.u2(), r.u2()
                    inner.append((cname(ic), cname(oc) if oc else None,
                                  utf(nm) if nm else None, fl))
                out["inner"] = inner
            elif name == "LineNumberTable":
                lines = []
                for _ in range(r.u2()):
                    r.u2()
                    lines.append(r.u2())
                out["lines"] = lines
            elif name == "Code":
                r.u2(); r.u2()
                r.bytes(r.u4())
                for _ in range(r.u2()):
                    r.bytes(8)
                out.update(attributes())
            r.p = end
        return out

    def members():
        out = []
        for _ in range(r.u2()):
            acc = r.u2()
            name = utf(r.u2())
            desc = utf(r.u2())
            attrs = attributes()
            out.append({"access": acc, "name": name, "desc": desc,
                        "annotations": attrs.get("annotations", []),
                        "constant": attrs.get("constant", False),
                        "lines": attrs.get("lines", [])})
        return out

    fields = members()
    methods = members()
    attrs = attributes()

    refs = set()
    for e in cp:
        if e and e[0] == "class":
            refs.add(utf(e[1]))
        if e and e[0] == "utf8":
            for m in re.finditer(r"L([\w/$]+);", e[1]):
                refs.add(m.group(1))
    refs = {x.replace("/", ".") for x in refs if not x.startswith("[")}
    strings = [utf(e[1]) for e in cp if e and e[0] == "string"]
    return {"name": this, "major": major, "access": access, "super": sup,
            "interfaces": interfaces, "source": attrs.get("source"),
            "inner": attrs.get("inner", []), "fields": fields,
            "methods": methods, "refs": refs - {this}, "strings": strings,
            "annotations": attrs.get("annotations", [])}


def walk(root, skip=()):
    for d, dirs, files in os.walk(root):
        rel = os.path.relpath(d, root)
        if any(rel == s or rel.startswith(s + os.sep) for s in skip):
            continue
        for f in files:
            if f.endswith(".class"):
                yield os.path.join(d, f)
