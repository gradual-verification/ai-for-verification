#!/usr/bin/env python3
import os
import sys
from pathlib import Path
from subprocess import run, PIPE, STDOUT

def iter_c_files(root: Path):
    """Yield .c files under root, in a stable (sorted) order."""
    root = root.resolve()
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(dirnames)
        for name in sorted(filenames):
            if name.endswith(".c"):
                yield Path(dirpath) / name


def run_verifast(cfile, rel):
    try:
        proc = run(["verifast", "-uppercase_type_params_carry_typeid", "-fno-strict-aliasing", str(cfile)], stdout=PIPE,
                   stderr=STDOUT, text=True)
        # Print VeriFast's combined stdout/stderr exactly as produced
        if not ("0 errors found" in proc.stdout
                or "Cannot prove" in proc.stdout
                or "No matching" in proc.stdout
                or "Loop invariant required" in proc.stdout
                or "Function leaks heap chunks" in proc.stdout):
            print(proc.stdout, end="" if proc.stdout.endswith("\n") else "\n")

    except Exception as e:
        print(f"[error] failed to run verifast on {rel}: {e}")


def run_gcc(cfile, rel):
    try:
        proc = run(["gcc", "-fsyntax-only", "-w", str(cfile)], stdout=PIPE, stderr=STDOUT, text=True)
        # Print gcc's combined stdout/stderr exactly as produced
        print(proc.stdout, end="" if proc.stdout.endswith("\n") else "\n")

    except Exception as e:
        print(f"[error] failed to run gcc on {rel}: {e}")


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {Path(sys.argv[0]).name} <directory>", file=sys.stderr)
        sys.exit(2)

    root = Path(sys.argv[1]).resolve()
    if not root.exists():
        print(f"error: directory not found: {root}", file=sys.stderr)
        sys.exit(2)

    found_any = False
    for cfile in iter_c_files(root):
        found_any = True
        rel = cfile.resolve().relative_to(root)

        # A tiny header so you know which file the next output belongs to.
        # Remove the next line if you truly want *only* VeriFast's raw output.
        print(f"\n=== {rel} ===")
        run_verifast(cfile, rel)
        #run_gcc(cfile, rel)

    if not found_any:
        print("No .c files found.")

if __name__ == "__main__":
    main()
