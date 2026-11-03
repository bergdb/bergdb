#!/usr/bin/env python3
"""Independently check 005-83's image mutations and summarize the experiment."""
import collections
import csv
import json
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
rows = list(csv.DictReader((root / 'results.tsv').open(), delimiter='\t'))


def files(path):
    return {p.name: p.read_bytes() for p in sorted(path.glob('*.bergdb'))}


def first(name):
    return int(name[:14]) * 100000


def byte_at(image, pos):
    for name, data in image.items():
        offset = pos - first(name)
        if 0 <= offset < len(data):
            return data[offset]
    raise AssertionError(('missing byte', pos))


def node_bytes(image, pos):
    def spos(offset):
        # Advance over meta blocks, independently of Java's getSpos implementation.
        p = pos
        while offset:
            available = 200000 - p % 200000
            step = min(available, offset)
            p += step
            offset -= step
            if p % 200000 == 0:
                p += 128
        return p
    size = int.from_bytes(bytes(byte_at(image, spos(i)) for i in range(4)), 'little', signed=True)
    return bytes(byte_at(image, spos(i)) for i in range(size))


def checksum(data):
    a = b = 0
    for i, value in enumerate(data):
        a = (a + (0 if i in (6, 7) else value)) % 255
        b = (b + a) % 255
    return a | b << 8


checked = set()
force_checks = checksum_checks = marker_checks = 0
for row in rows:
    key = row['scenario'], row['image']
    if key in checked:
        continue
    checked.add(key)
    source = root / row['scenario']
    forced, capture = files(source / 'forced'), files(source / 'capture')
    image = files(source / row['image'] / 'image')
    preserved = all(name in image and image[name][:len(data)] == data
                    for name, data in forced.items())
    if row['kind'] == 'negative':
        assert not preserved, ('negative control did not lose forced data', key)
        continue
    assert preserved, ('previously forced data changed', key)
    force_checks += 1
    start, count = int(row['damage_start']), int(row['damage_bytes'])
    if row['kind'] == 'hole':
        assert set(image) == set(capture)
        assert start >= int(row['forced_end'])
        assert start + count <= int(row['captured_end'])
        for name, old in capture.items():
            new = image[name]
            assert len(old) == len(new)
            lo, hi = max(0, start - first(name)), min(len(old), start + count - first(name))
            if lo < hi:
                assert new[:lo] == old[:lo] and new[hi:] == old[hi:]
                assert new[lo:hi] == bytes(hi-lo)
            else:
                assert new == old
        with (source / 'transactions.tsv').open() as stream:
            later = [t for t in csv.DictReader(stream, delimiter='\t')
                     if start + count <= int(t['last']) < int(row['captured_end'])]
        assert later, ('no later record marker retained', key)
        for tx in later:
            assert byte_at(image, int(tx['last'])) == 10
            marker_checks += 1
        if row['image'] in ('zero-value-512', 'zero-node-checksum'):
            manifest = dict(re.findall(r'(\w+)=([^\s]+)', (source/'capture.txt').read_text()))
            pos = int(manifest['target_blob'])
            old, new = node_bytes(capture, pos), node_bytes(image, pos)
            assert checksum(old) == int.from_bytes(old[6:8], 'little')
            assert checksum(new) != int.from_bytes(new[6:8], 'little')
            checksum_checks += 1
    elif row['kind'] == 'control':
        if row['image'] == 'full':
            assert image == capture
        else:
            for name, data in image.items():
                assert data == capture[name][:len(data)]
                assert first(name) + len(data) <= start

controls = [r for r in rows if r['kind'] == 'control']
negatives = [r for r in rows if r['kind'] == 'negative']
holes = [r for r in rows if r['kind'] == 'hole']
assert all(r['outcome'] == 'RECOVERED' and r['continued'] == 'true' for r in controls)
assert all(r['outcome'] == 'ACK_LOSS' for r in negatives)
assert not any(r['outcome'] == 'PROBE_LIMIT' for r in rows)

summary = {
    'rows': len(rows), 'distinct_images': len(checked),
    'control_checks': len(controls), 'negative_controls_detected': len(negatives),
    'hole_images': len({(r['scenario'], r['image']) for r in holes}),
    'hole_checks': len(holes),
    'hole_recovered': sum(r['outcome'] == 'RECOVERED' for r in holes),
    'hole_failures_by_stage': dict(collections.Counter(r['stage'] for r in holes
                                                       if r['outcome'] != 'RECOVERED')),
    'forced_prefix_image_checks': force_checks,
    'independent_node_checksum_checks': checksum_checks,
    'later_commit_markers_checked': marker_checks,
    'writes_accepted_after_getTrans_error': [r['scenario'] + '/' + r['image'] for r in rows
                                           if r['post_error_write'] == 'accepted'],
    'corrupt_input': [{k: r[k] for k in ('scenario', 'outcome', 'stage', 'recovered_time',
                                       'recovery_writes', 'growth_after_start', 'logical_growth')}
                      for r in rows if r['kind'] == 'corrupt-input'],
}
(root / 'analysis.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
