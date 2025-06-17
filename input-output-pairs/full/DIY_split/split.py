#!/usr/bin/env python3
import re
import sys
import os

# Recognized suffixes (without the .c)
KNOWN_SUFFIXES = ['_nl', '_fb', '_fbp']

def split_and_emit(infile):
    in_dir, in_file = os.path.split(infile)
    in_dir = in_dir or '.'
    base, ext = os.path.splitext(in_file)

    # peel off any known suffix
    core, suffix = base, ext
    for s in KNOWN_SUFFIXES:
        if base.endswith(s):
            core = base[:-len(s)]
            suffix = s + ext
            break

    text = open(infile).read()
    # split on separator lines
    chunks = re.split(r'(?m)^\s*//\s*-{3,}.*$', text)
    if len(chunks) < 2:
        print("Error: no separators found!", file=sys.stderr)
        sys.exit(1)

    header = chunks[0].rstrip() + '\n\n'

    for chunk in chunks[1:]:
        if not chunk.strip():
            continue

        # find signature line, skipping /***/ blocks and // comments
        sig = None
        in_block = False
        for line in chunk.splitlines():
            stripped = line.strip()
            if in_block:
                if '*/' in stripped:
                    in_block = False
                continue
            if stripped.startswith('/*'):
                if '*/' not in stripped:
                    in_block = True
                continue
            if not stripped or stripped.startswith('//'):
                continue
            sig = stripped
            break

        if not sig:
            print("Warning: no signature found, skipping chunk", file=sys.stderr)
            continue

        # New regex: pick the last identifier before '('
        m = re.match(r'.*\b([A-Za-z_]\w*)\s*\(.*', sig)
        if not m:
            print(f"Warning: couldn’t parse function name from:\n  {sig}", file=sys.stderr)
            continue
        func = m.group(1)

        out_name = f"{core}_{func}{suffix}"
        out_path = os.path.join(in_dir, out_name)

        with open(out_path, 'w') as of:
            of.write(header)
            of.write(chunk.lstrip('\n'))
        print(f"Wrote {out_path}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <manually_split_c_file>", file=sys.stderr)
        sys.exit(1)
    split_and_emit(sys.argv[1])

# // ----------------------------------------------------------------------