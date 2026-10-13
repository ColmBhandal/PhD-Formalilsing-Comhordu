#!/usr/bin/env python3
"""Summarise what the top-level `safety` theorem still rests on, as Markdown.

Runs `Print Assumptions safety` against the compiled project (run `make` first) and
groups the result into: model axioms (ComhBasics, deliberate), Parameter stubs,
unproved project lemmas (Admitted / Conjecture), and standard-library axioms.
Also counts every `Admitted` / `Conjecture` in src/, whether or not `safety` uses it.

Usage: python3 scripts/assumptions.py   (from the repository root)
"""
import collections
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "src")


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def print_assumptions():
    with tempfile.TemporaryDirectory() as d:
        v = os.path.join(d, "PrintSafety.v")
        with open(v, "w") as f:
            f.write("From ComhCoq Require Import Main.\nPrint Assumptions safety.\n")
        r = subprocess.run(["rocq", "compile", "-R", SRC, "ComhCoq", v],
                           capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("rocq compile failed:\n" + r.stderr + r.stdout)
    names = []
    for line in r.stdout.splitlines():
        if line and not line[0].isspace() and line != "Axioms:":
            names.append(line.split()[0])
    return names


def source_counts():
    admitted, conjectures = collections.Counter(), collections.Counter()
    for dirpath, _, files in os.walk(SRC):
        for fn in sorted(files):
            if fn.endswith(".v") and "Extras" not in dirpath:
                body = strip_comments(open(os.path.join(dirpath, fn)).read())
                admitted[fn] = len(re.findall(r"\bAdmitted\s*\.", body))
                conjectures[fn] = len(re.findall(r"^\s*Conjecture\b", body, re.M))
    return admitted, conjectures


def main():
    names = print_assumptions()
    groups = collections.defaultdict(list)
    for n in names:
        mod = n.split(".")[0]
        if mod == "ComhBasics":
            groups["Model axioms (ComhBasics, deliberate)"].append(n)
        elif n in ("EntAuxDefs.reachableEnt", "EntAuxDefs.nextModeEnt", "EntAuxDefs.inPosEnt",
                   "NetAuxBasics.currModeNet", "NetAuxBasics.nextModeNet"):
            groups["Parameter stubs"].append(n)
        elif mod in ("ClassicalDedekindReals", "ProofIrrelevance", "FunctionalExtensionality",
                     "Eqdep", "Classical_Prop", "ClassicalEpsilon", "IndefiniteDescription",
                     "Description", "ClassicalUniqueChoice", "PropExtensionality", "JMeq"):
            groups["Standard-library axioms"].append(n)
        else:
            groups["Unproved project lemmas (Admitted / Conjecture)"].append(n)
    admitted, conjectures = source_counts()

    print("## Assumptions under `safety`\n")
    print(f"**{len(names)}** assumptions in total.\n")
    print("| Kind | Count |\n|---|---|")
    for k in ("Unproved project lemmas (Admitted / Conjecture)", "Parameter stubs",
              "Model axioms (ComhBasics, deliberate)", "Standard-library axioms"):
        print(f"| {k} | {len(groups[k])} |")
    print(f"\nWhole codebase: **{sum(admitted.values())}** `Admitted`, "
          f"**{sum(conjectures.values())}** `Conjecture`.\n")
    print("<details><summary>Unproved lemmas under safety, by file</summary>\n")
    byfile = collections.Counter(n.split(".")[0] for n in groups["Unproved project lemmas (Admitted / Conjecture)"])
    for f, c in byfile.most_common():
        print(f"- `{f}`: {c}")
    print("\n</details>\n")
    print("<details><summary>Full list</summary>\n\n```")
    for n in names:
        print(n)
    print("```\n</details>")


if __name__ == "__main__":
    main()
