#!/usr/bin/env python3
# Copyright (c) 2026 Ralf Stephan. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Ralf Stephan
"""Generate comparator's statements of record from the development.

Reads the certified theorems from `comparator/theorems.txt` and writes

* `Challenge/<module>.lean`, one module per module of the development that owns a compared
  declaration, and `Challenge.lean` importing them all;
* `ChallengeFlat.lean`, the same statements in one module importing only Mathlib (Palomar's
  shape of a Challenge);
* `comparator/std3.json` and `comparator/std3-flat.json`.

Nothing here is written by hand, and nothing is paraphrased: every definition in the compared
closure, and every theorem a compared definition mentions, is copied from its source file
character for character, docstrings and comments dropped; every certified theorem is copied up to
its `:=` and given a `sorry` proof. Each copied module keeps the source file's `namespace`,
`section`, `open` and `variable` commands that some copied declaration follows, and nothing else.
Why the shapes are as they are — load order, the auxiliary-proof cache, `private` names — is in
`COMPARATOR.md`.

Usage, from the repository root, after `lake build`:

    python3 scripts/make-challenge.py
    python3 scripts/make-challenge.py --paper CorvajaZannier2004

With `--paper P`, the certified theorems are read from `comparator/<p>.txt` (`<p>` the kebab-case
form of `P`, e.g. `corvaja-zannier-2004`), the development also includes the library `P`, and only
the flat shape is written: `ChallengeP.lean` and `comparator/<p>.json`, against the hand-written
re-export `SolutionP.lean`. The libraries' own outputs are left alone.

The data pass runs `lake env lean` on a generated metaprogram that imports both libraries; it
honours `LEAN_NUM_THREADS`, and a memory cap belongs outside, e.g. `systemd-run --user --scope -p
MemoryMax=…`.
"""
import collections
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPER = sys.argv[sys.argv.index("--paper") + 1] if "--paper" in sys.argv else None
SLUG = re.sub(r"(?<=[a-z])(?=[A-Z0-9])", "-", PAPER).lower() if PAPER else None
DEV_ROOTS = ("ArithmeticHeights", "DiophantineApproximation") + ((PAPER,) if PAPER else ())
DATA = os.path.join(ROOT, ".lake", "challenge-data" + (f"-{PAPER}" if PAPER else ""))
THEOREMS = os.path.join(ROOT, "comparator", f"{SLUG}.txt" if PAPER else "theorems.txt")
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]

HEADER = """/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
"""

# The metaprogram of the data pass. For the certified theorems it writes the compared closure —
# every declaration of the two libraries reached from a theorem's *type*, following the types and
# values of definitions and the proofs of theorems, which is exactly what comparator walks — and
# for the whole development every declaration's line range and the import graph.
METAPROGRAM = r'''
open Lean Elab Command

def challengeOwner (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if [DEV_ROOTS].any (·.isPrefixOf m) then some m else none

def challengeClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut stack : Array Name := (env.find? root).get!.type.getUsedConstants
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if (challengeOwner env n).isNone then continue
    out := out.push n
    stack := stack ++ ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    match ci with
    | .inductInfo i => stack := stack ++ i.ctors.toArray
    | .ctorInfo c => stack := stack.push c.induct
    | _ => pure ()
  return out

elab "#challengeData " dir:str : command => do
  let env ← getEnv
  let dir := dir.getString
  let names := (← IO.FS.lines (dir ++ "/theorems.txt")).filter (· ≠ "")
  let mut rows : Array String := #[]
  let mut done : NameSet := {}
  for s in names do
    let root := s.toName
    unless env.contains root do throwError "not a declaration: {root}"
    for c in (challengeClosure env root).push root do
      if done.contains c then continue
      done := done.insert c
      let some m := challengeOwner env c | continue
      if isPrivateName c then
        throwError "{root} reaches the private constant {c}; comparator cannot compare it"
      let kind := if (env.find? c).get!.isThm then "thm" else "def"
      let tgt := if c == root then "TARGET" else "dep"
      let range := match ← findDeclarationRanges? c with
        | some r => s!"{r.range.pos.line}\t{r.range.endPos.line}"
        | none => "-\t-"
      rows := rows.push s!"{m}\t{range}\t{kind}\t{tgt}\t{c}"
  IO.FS.writeFile (dir ++ "/closure.tsv") (String.intercalate "\n" rows.toList)
  let mut decls : Array String := #[]
  for (c, _) in env.constants.map₁.toList do
    let some m := challengeOwner env c | continue
    if let some r ← findDeclarationRanges? c then
      decls := decls.push s!"{m}\t{r.range.pos.line}\t{r.range.endPos.line}"
  IO.FS.writeFile (dir ++ "/decls.tsv") (String.intercalate "\n" decls.toList)
  let mut graph : Array String := #[]
  for i in [0:env.header.moduleNames.size] do
    for imp in env.header.moduleData[i]!.imports do
      graph := graph.push s!"{env.header.moduleNames[i]!}\t{imp.module}\t{imp.isExported}"
  IO.FS.writeFile (dir ++ "/graph.tsv") (String.intercalate "\n" graph.toList)
'''


def is_dev(mod):
    return mod.split(".")[0] in DEV_ROOTS


def path_of(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def read_theorems():
    """The certified theorems, in file order; `#` starts a comment."""
    out = []
    for line in open(THEOREMS):
        line = line.split("#", 1)[0].strip()
        if line:
            out.append(line)
    return out


def run_data_pass(theorems):
    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, "theorems.txt"), "w") as f:
        f.write("\n".join(theorems) + "\n")
    modules = sorted(
        os.path.relpath(os.path.join(d, f), ROOT)[:-len(".lean")].replace(os.sep, ".")
        for r in DEV_ROOTS for d, _, fs in os.walk(os.path.join(ROOT, r)) for f in fs
        if f.endswith(".lean"))
    roots = ", ".join(f"`{r}" for r in DEV_ROOTS)
    src = "".join(f"import {m}\n" for m in modules) + \
        METAPROGRAM.replace("[DEV_ROOTS]", f"[{roots}]") + \
        f'#challengeData "{DATA}"\n'
    prog = os.path.join(DATA, "ChallengeData.lean")
    with open(prog, "w") as f:
        f.write(src)
    threads = os.environ.get("LEAN_NUM_THREADS", "3")
    subprocess.run(["lake", "env", "lean", f"-j{threads}", prog], cwd=ROOT, check=True)


# ---------------------------------------------------------------------------------------------
# imports

IMPORT_RE = re.compile(r"^(public )?(meta )?import (\S+)\s*$")


def read_imports(mod):
    out = []
    for line in open(path_of(mod)):
        m = IMPORT_RE.match(line)
        if m:
            out.append((m.group(3), bool(m.group(1))))
    return out


def resolve(mod, chal_set):
    """The imports of the challenge copy of `mod`, in the source's load order, each `True` when
    public. An import of a development module that has a challenge copy becomes an import of the
    copy; one that has none is replaced by its own imports, recursively, at the same place, so
    that the Mathlib modules load in the same order. An import is public only along a path of
    public imports."""
    res = {}

    def walk(m, pub, stack):
        for imp, ipub in read_imports(m):
            p = pub and ipub
            if not is_dev(imp):
                res[imp] = res.get(imp, False) or p
            elif imp in chal_set:
                key = "Challenge." + imp
                res[key] = res.get(key, False) or p
            elif imp not in stack:
                walk(imp, p, stack | {imp})

    walk(mod, True, {mod})
    return res


def load_order(roots):
    """The Mathlib modules the development imports directly, in the order Lean loads the
    development from `roots`: a depth-first walk over each file's imports in file order."""
    order, seen = [], set()

    def walk(m):
        for imp, _ in read_imports(m):
            if imp in seen:
                continue
            seen.add(imp)
            if is_dev(imp):
                walk(imp)
            else:
                order.append(imp)

    for r in roots:
        if r not in seen:
            seen.add(r)
            walk(r)
    return order


def reduce_imports(mods, roots):
    """`mods` maps each Mathlib module to `True` (public) or `False`. Keep the development's load
    order; drop a module only when an import earlier in that order already loads it, which does
    not move it, and makes it visible (publicly, when it is a public import)."""
    edges, pedges = collections.defaultdict(set), collections.defaultdict(set)
    for row in open(os.path.join(DATA, "graph.tsv")):
        x, y, pub = row.rstrip("\n").split("\t")
        edges[x].add(y)
        if pub == "true":
            pedges[x].add(y)
    cache = {}

    def closure(m, g):
        if (m, id(g)) not in cache:
            seen, todo = set(), [m]
            while todo:
                for y in g[todo.pop()]:
                    if y not in seen:
                        seen.add(y)
                        todo.append(y)
            cache[(m, id(g))] = seen
        return cache[(m, id(g))]

    kept, loaded = [], set()
    for m in load_order(roots):
        if m not in mods:
            continue
        pub = mods[m]
        visible = any(m in closure(o, pedges) for o, opub in kept if opub or not pub)
        if not (m in loaded and visible):
            kept.append((m, pub))
        loaded |= {m} | closure(m, edges)
    missing = set(mods) - {m for m, _ in kept} - loaded
    if missing:
        raise SystemExit(f"make-challenge: lost imports {sorted(missing)}")
    return kept


# ---------------------------------------------------------------------------------------------
# bodies

CONTEXT_RE = re.compile(
    r"^(namespace|section|end|open|variable|universe|noncomputable section|@\[expose\] public "
    r"section|public section|local notation|notation|scoped|local infix|attribute \[local)")
OPEN_RE = re.compile(r"^(namespace|section|noncomputable section|public section|"
                     r"@\[expose\] public section)\b\s*(\S*)")
OPENERS = "([{⟨⦃"
CLOSERS = ")]}⟩⦄"


def strip_doc(text):
    """Drop a leading doc comment and full-line `--` comments."""
    text = text.lstrip("\n")
    if text.startswith("/--"):
        depth, i = 0, 0
        while i < len(text):
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
                if depth == 0:
                    break
            else:
                i += 1
        text = text[i:].lstrip("\n")
    return "\n".join(l for l in text.split("\n") if not l.strip().startswith("--"))


def statement(text):
    """Cut a theorem at its top-level `:=` and give it a `sorry` proof."""
    depth = 0
    for i, c in enumerate(text):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return text[:i].rstrip() + " := by\n  sorry"
    raise SystemExit("make-challenge: no top-level := in\n" + text)


def body(mod, needed, decls):
    """The module's copied declarations and context commands, as ("decl"|"ctx", text) items."""
    lines = open(path_of(mod)).read().split("\n")
    n = len(lines)
    covered = [False] * (n + 2)
    for s, e in decls[mod]:
        for l in range(s, e + 1):
            covered[l] = True
    keep = {s: (e, tgt) for s, e, tgt in needed[mod]}
    out, pending, l = [], [], 1          # `pending`: `… in` prefixes awaiting their declaration
    while l <= n:
        line = lines[l - 1]
        if l in keep:
            e, tgt = keep[l]
            text = strip_doc("\n".join(lines[l - 1:e]))
            out.append(("decl", "\n".join(pending + [statement(text) if tgt else text])))
            pending, l = [], e + 1
        elif covered[l]:
            pending = []
            while l <= n and covered[l] and l not in keep:
                l += 1
        elif CONTEXT_RE.match(line):
            block = [line]
            l += 1
            while l <= n and lines[l - 1].startswith((" ", "\t")) and not covered[l]:
                block.append(lines[l - 1])
                l += 1
            text = "\n".join(block)
            if re.search(r"\bin\s*$", text):
                pending.append(text)
            else:
                pending = []
                out.append(("ctx", text))
        elif re.match(r"^(omit|include|set_option|open)\b.*\bin\s*$", line):
            pending.append(line)
            l += 1
        elif line.startswith("/-"):
            depth = 0
            while l <= n:
                depth += lines[l - 1].count("/-") - lines[l - 1].count("-/")
                l += 1
                if depth <= 0:
                    break
        else:
            l += 1
    return out


def tree(items):
    """Nest the items into blocks `["block", header, children, closed]`."""
    root, stack, headers = [], [], []
    stack.append(root)
    for kind, text in items:
        if kind == "ctx" and OPEN_RE.match(text):
            node = ["block", text, [], False]
            stack[-1].append(node)
            stack.append(node[2])
            headers.append(node)
        elif kind == "ctx" and re.match(r"^end\b", text):
            headers.pop()[3] = True
            stack.pop()
        else:
            stack[-1].append((kind, text))
    return root


def render(nodes, close):
    """Drop the context commands no declaration follows and the blocks holding no declaration;
    with `close`, also end the blocks the source leaves open at the end of the file."""
    out, has_decl = [], False
    for idx, node in enumerate(nodes):
        if node[0] == "block":
            inner, d = render(node[2], close)
            if d:
                has_decl = True
                m = OPEN_RE.match(node[1])
                out.append(node[1])
                out.extend(inner)
                if node[3] or close:
                    name = m.group(2) if m.group(1) in ("namespace", "section") else ""
                    out.append(("end " + name).rstrip())
        elif node[0] == "decl":
            has_decl = True
            out.append(node[1])
        elif any(n[0] == "decl" or (n[0] == "block" and render(n[2], close)[1])
                 for n in nodes[idx + 1:]):
            out.append(node[1])
    return out, has_decl


def render_text(items, close):
    return "\n".join(render(tree(items), close)[0])


# Groups of instances of equal priority that the development does not choose between uniformly.
# Lean tries such instances in load order, the later-loaded first, and the libraries' modules load
# Mathlib in different orders, so the same goal elaborates with one instance in some modules and
# with another in the rest. One file has one load order; where it ranks a group differently from a
# module's own, that module's part of the flat file restores the module's ranking locally: the
# module's first choice keeps the common priority and the others go below it, one step each, in
# the module's order. Lowering rather than raising leaves every instance outside the group where
# it was — a more specific one such as `Rat.nontrivial` is tried before all of these at equal
# priority, and raising `EuclideanDomain.toNontrivial` would overrule it. Each group lists every
# candidate comparator has seen chosen, with its module and the common priority. See
# `COMPARATOR.md`.
TIES = [
    ([("Module.FaithfullyFlat.faithfulSMul", "Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra"),
      ("instFaithfulSMul_1", "Mathlib.Algebra.Algebra.IsSimpleRing"),
      ("Module.Free.instFaithfulSMulOfNontrivial", "Mathlib.LinearAlgebra.FreeModule.Basic")],
     1000),
    ([("EuclideanDomain.toNontrivial", "Mathlib.Algebra.EuclideanDomain.Defs"),
      ("IsLocalRing.toNontrivial", "Mathlib.RingTheory.LocalRing.Defs")], 1000),
    ([("SubgroupClass.toSubmonoidClass", "Mathlib.Algebra.Group.Subgroup.Defs"),
      ("SubsemiringClass.toSubmonoidClass", "Mathlib.Algebra.Ring.Subsemiring.Defs")], 1000),
]


def post_order(roots, edges):
    """Module → position in the order Lean loads `roots` and everything they import."""
    seen, out = set(), []
    stack = [(r, False) for r in reversed(roots)]
    while stack:
        m, expanded = stack.pop()
        if expanded:
            out.append(m)
        elif m not in seen:
            seen.add(m)
            stack.append((m, True))
            stack.extend((c, False) for c in reversed(edges[m]) if c not in seen)
    return {m: i for i, m in enumerate(out)}


def pins(mod, flat_imports, edges):
    """The `attribute [local instance …]` lines the flat file needs for `mod`'s part."""
    dev = post_order(edges[mod], edges)
    flat = post_order(["Init"] + flat_imports, edges)
    out = []
    for group, prio in TIES:
        group = [(x, mx) for x, mx in group if mx in dev and mx in flat]
        want = sorted(group, key=lambda c: -dev[c[1]])       # the module's order, first tried first
        have = sorted(group, key=lambda c: -flat[c[1]])
        if want != have:
            # every candidate after the module's first choice below `prio`, in the module's order
            for k, (x, _) in enumerate(want[1:], 1):
                out.append(f"attribute [local instance {prio - k}] {x}")
    return out


# The auxiliary-lemma cache (`Lean.Meta.auxLemmasExt`, "a mere cache, keep local") lives for one
# module. Clearing it between the former modules of the flat file makes each of them mint its own
# `_proof_` constants, as the development's modules do. See `COMPARATOR.md`.
RESET = "run_cmd Lean.modifyEnv (Lean.Meta.auxLemmasExt.setState · {})"

FLAT_DOC = """/-!
# Siegel's lemma, Roth's theorem and the Subspace Theorem: the statements of record

Generated by `scripts/make-challenge.py` from the libraries `ArithmeticHeights` and
`DiophantineApproximation`; do not edit. Each `-- <module>` part repeats, verbatim, the definitions
of that module the certified theorems mention, and states the theorems with `sorry`. Each part
opens by clearing Lean's auxiliary-proof cache, as a module boundary does, and some lower
instances locally to restore their module's tie-break. See `COMPARATOR.md`.
-/

"""


PAPER_DOC = """/-!
# {paper}: the statements of record

Generated by `scripts/make-challenge.py --paper {paper}` from the library
`{paper}` and the libraries it builds on; do not edit. Each `-- <module>` part repeats,
verbatim, the definitions of that module the certified theorems mention, and states the theorems
with `sorry`. Each part opens by clearing Lean's auxiliary-proof cache, as a module boundary does,
and some lower instances locally to restore their module's tie-break. See `COMPARATOR.md`.
-/

"""


def main():
    theorems = read_theorems()
    if "--no-data" not in sys.argv:
        run_data_pass(theorems)
    needed = collections.defaultdict(list)
    for row in open(os.path.join(DATA, "closure.tsv")):
        mod, s, e, _kind, tgt, _name = row.rstrip("\n").split("\t")
        if s != "-":
            needed[mod].append((int(s), int(e), tgt == "TARGET"))
    decls = collections.defaultdict(list)
    for row in open(os.path.join(DATA, "decls.tsv")):
        mod, s, e = row.rstrip("\n").split("\t")
        decls[mod].append((int(s), int(e)))
    chal_set = set(needed)
    deps = {m: [i[len("Challenge."):] for i in resolve(m, chal_set) if i.startswith("Challenge.")]
            for m in chal_set}
    order, done = [], set()

    def visit(m):
        if m not in done:
            done.add(m)
            for d in deps[m]:
                visit(d)
            order.append(m)

    for m in sorted(chal_set):
        visit(m)
    items = {m: body(m, needed, decls) for m in order}

    stale = []
    for d, _, fs in ([] if PAPER else os.walk(os.path.join(ROOT, "Challenge"))):
        for f in fs:
            mod = os.path.relpath(os.path.join(d, f), ROOT)[:-len(".lean")].replace(os.sep, ".")
            if mod[len("Challenge."):] not in chal_set:
                stale.append(os.path.join(d, f))
    for m in ([] if PAPER else order):
        dest = os.path.join(ROOT, "Challenge", *m.split(".")) + ".lean"
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w") as f:
            f.write(HEADER + "module\n\n" + "".join(
                f"{'public ' if p else ''}import {i}\n" for i, p in resolve(m, chal_set).items())
                + "\n" + render_text(items[m], False) + "\n")
    if not PAPER:
        with open(os.path.join(ROOT, "Challenge.lean"), "w") as f:
            f.write(HEADER + "".join(f"import Challenge.{m}\n" for m in order))
    flat_name = f"Challenge{PAPER}" if PAPER else "ChallengeFlat"
    sol_name = f"Solution{PAPER}" if PAPER else "Solution"

    flat_imps = {}
    for m in order:
        for i, p in resolve(m, chal_set).items():
            if not i.startswith("Challenge."):
                flat_imps[i] = flat_imps.get(i, False) or p
    roots = [mm.group(1) for mm in (re.match(r"^import (\S+)", l)
             for l in open(os.path.join(ROOT, sol_name + ".lean"))) if mm]
    flat_list = reduce_imports(flat_imps, roots)
    edges = collections.defaultdict(list)
    for row in open(os.path.join(DATA, "graph.tsv")):
        x, y, _ = row.rstrip("\n").split("\t")
        if y not in edges[x]:
            edges[x].append(y)
    parts = []
    for m in order:
        text = render_text(items[m], True)
        pinned = pins(m, [i for i, _ in flat_list], edges)
        if pinned:
            text = "\n".join(pinned) + "\n" + text
        loose = pinned or any(n[0] == "ctx" for n in tree(items[m]))
        parts.append(f"-- {m}\n{RESET}\n" + (f"section\n{text}\nend" if loose else text))
    with open(os.path.join(ROOT, flat_name + ".lean"), "w") as f:
        f.write(HEADER + "module\n\n" + "".join(
            f"{'public ' if p else ''}import {i}\n" for i, p in flat_list)
            + "\n" + (PAPER_DOC.format(paper=PAPER) if PAPER else FLAT_DOC)
            + "\n".join(parts) + "\n")

    lanes = ([(flat_name, f"{SLUG}.json")] if PAPER else
             [("Challenge", "std3.json"), ("ChallengeFlat", "std3-flat.json")])
    for chal, name in lanes:
        cfg = {"challenge_module": chal, "solution_module": sol_name,
               "theorem_names": theorems, "permitted_axioms": AXIOMS, "enable_nanoda": False}
        with open(os.path.join(ROOT, "comparator", name), "w") as f:
            f.write(json.dumps(cfg, indent=2, ensure_ascii=False) + "\n")

    flat = open(os.path.join(ROOT, flat_name + ".lean"), encoding="utf-8").read()
    print(f"make-challenge: {len(theorems)} theorems, {len(order)} challenge modules; "
          f"{flat_name}.lean is {flat.count(chr(10))} lines, {len(flat.encode())} bytes")
    for s in stale:
        print(f"make-challenge: stale, delete by hand: {os.path.relpath(s, ROOT)}")


main()
