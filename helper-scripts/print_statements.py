#!/usr/bin/env python3
"""Prints the statement of every result and the body of every definition in src/, module by
module, so that two builds can be compared with diff.

For each .v file under src/, the script collects the top-level names it declares (lemmas,
theorems, definitions, inductives, records, classes, instances, parameters, conjectures), then
asks Rocq for each one: `Check` for results and parameters, which prints the statement, and
`Print` for definitions and inductives, which prints the body too. Names are fully qualified,
so a name that exists in two modules is reported for each. Tactics and notations are skipped,
since they are not statements.

Run it from the repository root after `make`, with the same Rocq toolchain as the build:

    python3 helper-scripts/print_statements.py > statements.txt

Run it before and after a refactoring and diff the two files. Lines that only differ in a
module path mean a move; a name that disappears is a removal, and the diff shows nothing else
when every statement is unchanged. Use `--src DIR` to point at another checkout's src/.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

LOGICAL_ROOT = "ComhCoq"

CHECK_KINDS = {
    "Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition", "Example",
    "Parameter", "Parameters", "Axiom", "Axioms", "Conjecture", "Instance",
}
PRINT_KINDS = {
    "Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Record",
    "Class", "Variant", "Structure",
}
KINDS = CHECK_KINDS | PRINT_KINDS

DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:#\[[^\]]*\][ \t]*)?(?:Local[ \t]+|Global[ \t]+|Program[ \t]+)?"
    r"(" + "|".join(sorted(KINDS)) + r")[ \t]+([A-Za-z_][A-Za-z0-9_']*)"
)
MUTUAL_RE = re.compile(r"(?m)^[ \t]*with[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*[:(]")


def strip_comments(text):
    """Removes Rocq's nestable (* ... *) comments, keeping line breaks."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        else:
            if depth == 0 or text[i] == "\n":
                out.append(text[i])
            i += 1
    return "".join(out)


def declared_names(path):
    """Yields (kind, name) for each top-level declaration in a .v file, in file order."""
    text = strip_comments(open(path, encoding="utf-8").read())
    seen = set()
    for match in DECL_RE.finditer(text):
        kind, name = match.group(1), match.group(2)
        if name not in seen:
            seen.add(name)
            yield kind, name
    # A mutual inductive's or fixpoint's companions are introduced by `with`.
    for match in MUTUAL_RE.finditer(text):
        name = match.group(1)
        if name not in seen:
            seen.add(name)
            yield "Inductive", name


def module_of(path, src):
    rel = os.path.relpath(path, src)[: -len(".v")]
    return LOGICAL_ROOT + "." + rel.replace(os.sep, ".")


def rocq_output(module, names, src, workdir):
    """Compiles a throwaway file of Check/Print commands and returns Rocq's output."""
    lines = ["Require Import %s." % module]
    for kind, name in names:
        qualified = "%s.%s" % (module, name)
        if kind in PRINT_KINDS:
            lines.append('Print %s.' % qualified)
        else:
            lines.append('Check @%s.' % qualified)
    vfile = os.path.join(workdir, "print_statements_tmp.v")
    with open(vfile, "w", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")
    result = subprocess.run(
        ["rocq", "c", "-q", "-R", src, LOGICAL_ROOT, vfile],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
    )
    # Warnings name the throwaway file; hide its random directory so runs can be diffed.
    return result.returncode, result.stdout.replace(workdir, "<tmp>")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--src", default="src", help="the src/ folder to read (default: src)")
    args = parser.parse_args()
    src = os.path.abspath(args.src)

    files = []
    for root, _dirs, names in os.walk(src):
        for name in names:
            if name.endswith(".v"):
                files.append(os.path.join(root, name))
    files.sort(key=lambda p: module_of(p, src))

    failed = False
    with tempfile.TemporaryDirectory() as workdir:
        for path in files:
            module = module_of(path, src)
            names = sorted(set(declared_names(path)), key=lambda kn: kn[1])
            if not names:
                continue
            code, output = rocq_output(module, names, src, workdir)
            output = "\n".join(
                line for line in output.splitlines()
                if not line.startswith("[WARNING] Running as root")
            )
            print("=" * 78)
            print("== %s (%d names)" % (module, len(names)))
            print("=" * 78)
            print(output.rstrip())
            print()
            if code != 0:
                failed = True
                print("!! rocq exited with status %d for %s" % (code, module), file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
