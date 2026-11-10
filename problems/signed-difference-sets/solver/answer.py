"""Objects and Lean answers for found sets (standard library only).

`answer.py object <run output> <instance id> <object id>`: writes objects/O<id>.txt from
the run's line for that Instance (`id key yes nodes time coords± …`).
`answer.py lean <object id> <instance id>`: writes lean/SignedDifferenceSets/Answer/N<id>.lean,
whose `hasSDS` Lean checks by `decide`.
`answer.py fast <object id> <instance id>`: the same through `checkSet` and `decide +kernel`,
for sets too large for `decide`.
`answer.py split <object id> <instance id> <parts>`: as `fast`, the shifts in `parts` ranges.
`answer.py contract <instance id> <d1,…,dr> [depth]`: writes Answer/N<id>.lean proving no SDS by
contraction along ∏ ZMod mᵢ → ∏ ZMod dᵢ (`not_hasSDS_of_noVector`, `decide +kernel`); a search
of more than SPLIT_NODES nodes is split by prefix (`noVector_of_top`) into kernel checks of at most
BATCH_NODES nodes, in part modules `Answer/N<id>/PartNN.lean` of at most PART_NODES nodes over a
shared `Answer/N<id>/Check.lean`, joined in `Answer/N<id>.lean`.
"""
import csv
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ANSWER_DIR = ROOT / "lean" / "SignedDifferenceSets" / "Answer"
LEAN_DIR = ROOT / "lean"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


def instance_key(instance: str) -> str:
    with open(ROOT / "instances.csv", newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row["id"] == instance:
                return row["key"]
    sys.exit(f"{instance} not in instances.csv")


def parse_key(key: str):
    m = KEY.fullmatch(key)
    v, k, lam = map(int, m.groups()[:3])
    return v, k, lam, [int(x) for x in m.group(4).split(",")]


def write_object(run_file: str, instance: str, obj: str) -> None:
    key = instance_key(instance)
    v, k, lam, shape = parse_key(key)
    for line in open(run_file, encoding="utf-8"):
        parts = line.split()
        if parts[:3] == [instance, key, "yes"]:
            lines = [f"{'x'.join(f'C{m}' for m in shape)} ({v},{k},{lam})"]
            for t in parts[5:]:
                lines.append(f"{' '.join(t[:-1].split('.'))} {t[-1]}")
            (ROOT / "objects" / f"{obj}.txt").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
            return
    sys.exit(f"no set for {instance} in {run_file}")


def read_object(obj: str):
    first, *rest = (ROOT / "objects" / f"{obj}.txt").read_text(encoding="utf-8").splitlines()
    shape = [int(m) for m in re.findall(r"C(\d+)", first.split()[0])]
    v, k, lam = map(int, re.search(r"\((\d+),(\d+),(-?\d+)\)", first).groups())
    signs = {}
    for line in rest:
        *coords, sign = line.split()
        signs[tuple(map(int, coords))] = 1 if sign == "+" else -1
    return shape, v, k, lam, signs


def table(shape, signs, prefix=()):
    """Nested `![…]` literal indexed by the coordinates, first factor outermost."""
    if len(prefix) == len(shape):
        return str(signs.get(prefix, 0))
    entries = [table(shape, signs, prefix + (c,)) for c in range(shape[len(prefix)])]
    if prefix:
        return f"![{', '.join(entries)}]"
    # Top level: one outer entry per line (16 signs per line for a cyclic group).
    step = 16 if len(shape) == 1 else 1
    rows = [", ".join(entries[i : i + step]) for i in range(0, len(entries), step)]
    return "![" + ",\n    ".join(rows) + "]"


def write_lean(obj: str, instance: str) -> None:
    shape, v, k, lam, signs = read_object(obj)
    key = instance_key(instance)
    assert parse_key(key) == (v, k, lam, shape), f"{obj} does not answer {key}"
    group = " × ".join(f"ZMod {m}" for m in shape)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    proj = ["p"] if len(shape) == 1 else [f"p{'.2' * i}.1" for i in range(len(shape) - 1)] + [
        f"p{'.2' * (len(shape) - 1)}"
    ]
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    text = f"""module

public import SignedDifferenceSets.Check

/-!
# {instance}: a ({v}, {k}, {lam}) SDS in {pretty}

Open in Gordon's table (`{key}`, 2026-11-05). The set is object {obj}
(`objects/{obj}.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.{instance}

/-- Object {obj}: the sign of each element, first coordinate outermost. -/
def sds : {group} → SignType := fun p =>
  ({table(shape, signs)})
    {' '.join(proj)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS {k} {lam_lean} sds := by decide

/-- {instance}: {pretty} has a signed difference set with parameters ({v}, {k}, {lam}). -/
theorem hasSDS : HasSDS ({group}) {k} {lam_lean} := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.{instance}
"""
    (ANSWER_DIR / f"{instance}.lean").write_text(text, encoding="utf-8", newline="\n")


def masks(shape, signs):
    """Bit masks (plus, minus) over the element numbers of `Indexed`: mixed radix, first
    coordinate most significant."""
    plus = minus = 0
    for coords, sign in signs.items():
        i = 0
        for c, m in zip(coords, shape):
            i = i * m + c
        if sign > 0:
            plus |= 1 << i
        else:
            minus |= 1 << i
    return plus, minus


def write_fast(obj: str, instance: str) -> None:
    shape, v, k, lam, signs = read_object(obj)
    key = instance_key(instance)
    assert parse_key(key) == (v, k, lam, shape), f"{obj} does not answer {key}"
    group = " × ".join(f"ZMod {m}" for m in shape)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    plus, minus = masks(shape, signs)
    text = f"""module

public import SignedDifferenceSets.SetCheck

/-!
# {instance}: a ({v}, {k}, {lam}) SDS in {pretty}

Open in Gordon's table (`{key}`, 2026-11-05). The set is object {obj}
(`objects/{obj}.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.{instance}

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object {obj}'s plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := {plus:#x}

set_option linter.style.longLine false in
/-- Object {obj}'s minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := {minus:#x}

/-- Object {obj}: the sign of each element. -/
def sds : {group} → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS {k} {lam_lean} sds :=
  isSDS_of_checkSet (G := {group})
    (P := plus) (N := minus) (by decide +kernel)

/-- {instance}: {pretty} has a signed difference set with
parameters ({v}, {k}, {lam}). -/
theorem hasSDS :
    HasSDS ({group}) {k} {lam_lean} :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.{instance}
"""
    (ANSWER_DIR / f"{instance}.lean").write_text(text, encoding="utf-8", newline="\n")


def write_split(obj: str, instance: str, parts: str) -> None:
    """As `write_fast`, with the shifts checked in `parts` ranges, one `decide +kernel` each,
    which bounds the kernel's memory per declaration (N58470, v = 455: one check passed 8.8 GB)."""
    shape, v, k, lam, signs = read_object(obj)
    key = instance_key(instance)
    assert parse_key(key) == (v, k, lam, shape), f"{obj} does not answer {key}"
    group = " × ".join(f"ZMod {m}" for m in shape)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    plus, minus = masks(shape, signs)
    n = int(parts)
    bounds = [v * i // n for i in range(n + 1)]
    chunks = "\n".join(f"""set_option maxRecDepth 100000 in
/-- Shifts {lo} to {hi - 1}. -/
theorem shifts{i + 1} :
    allFrom (shiftOk ({group}) {lam_lean} plus minus) {lo} {hi - lo} =
      true := by
  decide +kernel
""" for i, (lo, hi) in enumerate(zip(bounds, bounds[1:])))
    joined = "".join(f"  have h := allFrom_append h shifts{i}\n" for i in range(2, n + 1))
    text = f"""module

public import SignedDifferenceSets.SetCheckSplit

/-!
# {instance}: a ({v}, {k}, {lam}) SDS in {pretty}

Open in Gordon's table (`{key}`, 2026-11-05). The set is object {obj}
(`objects/{obj}.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in {n} ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.{instance}

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object {obj}'s plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := {plus:#x}

set_option linter.style.longLine false in
/-- Object {obj}'s minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := {minus:#x}

/-- Object {obj}: the sign of each element. -/
def sds : {group} → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count :
    countOk ({group}) {k} plus minus = true := by
  decide +kernel

{chunks}
theorem isSDS : IsSDS {k} {lam_lean} sds := by
  have h := shifts1
{joined}  exact isSDS_of_checkSplit count h

/-- {instance}: {pretty} has a signed difference set with
parameters ({v}, {k}, {lam}). -/
theorem hasSDS :
    HasSDS ({group}) {k} {lam_lean} :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.{instance}
"""
    (ANSWER_DIR / f"{instance}.lean").write_text(text, encoding="utf-8", newline="\n")


# The kernel keeps about 0.1 MB per search node of one declaration (N79: 51,596 nodes, 7.5 GB).
SPLIT_NODES = 60_000
BRANCH_NODES = 20_000
BATCH_NODES = 25_000  # nodes per `decide +kernel` in a split contraction answer (the kernel keeps ~0.1 MB per node; 300,000 peaked at 11 GB)
PART_NODES = 500_000  # nodes per part module (N6970 in one module of 1.5M nodes: killed at 8.8 GB)


def prefix_nodes(n, c, Q, s, depth):
    """Search nodes below each prefix of `depth` coordinates that `noVectorTop` leaves to its
    own check, mirroring `go` (a missing prefix fails the build, it cannot prove anything)."""
    def cut(rem, sm, sq):
        r, d = Q - sq, s - sm
        return r < 0 or rem * r < d * d or rem * c < abs(d)

    def size(rem, top, sm, sq):
        if rem == 0 or cut(rem, sm, sq):
            return 1
        return 1 + sum(size(rem - 1, top, sm + x, sq + x * x)
                       for x in range(-top, top + 1) if x * x <= Q - sq)

    counts = {}

    def walk(prefix, rem, top, sm, sq):
        if len(prefix) == depth:
            counts[tuple(prefix)] = size(rem, top, sm, sq)
        elif rem > 0 and not cut(rem, sm, sq):
            for x in range(-top, top + 1):
                if x * x <= Q - sq:
                    walk(prefix + [x], rem - 1, top, sm + x, sq + x * x)

    if not cut(n, 0, 0):
        for x in range(-c, c + 1):
            if x * x <= Q:
                walk([x], n - 1, abs(x), x, x * x)
    return counts


def proj_term(shape, divisors):
    """`Proj` built factor by factor, products nested to the right like the key's type."""
    casts = [f".cast {d} (by norm_num)" for d in divisors]
    term = casts[-1]
    for cast in reversed(casts[:-1]):
        term = f".prod ({cast})\n    ({term})"
    return term


def write_contract(instance: str, divisors: str, depth: str = "") -> None:
    """`depth` (optional) fixes the prefix depth: fewer prefixes keep the join's coverage check small."""
    key = instance_key(instance)
    v, k, lam, shape = parse_key(key)
    ds = [int(d) for d in divisors.split(",")]
    assert len(ds) == len(shape) and all(m % d == 0 for m, d in zip(shape, ds)), divisors
    n = math.prod(ds)
    c, s = v // n, math.isqrt(k + lam * (v - 1))
    assert s * s == k + lam * (v - 1), "C1 fails"
    group = " × ".join(f"ZMod {m}" for m in shape)
    quotient = " × ".join(f"ZMod {d}" for d in ds)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    pretty_h = " × ".join(f"C{str(d).translate(SUB)}" for d in ds if d > 1)
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    proj = f"""/-- The projection {pretty} → {pretty_h}, factor by factor. -/
def proj : Proj ({group}) ({quotient}) :=
  {proj_term(shape, ds)}
"""
    doc = f"""Open in Gordon's table (`{key}`, 2026-11-05).
Contract along {pretty} → {pretty_h} (C3): fibres of {c} elements, so the coset
sums lie in [−{c}, {c}], have square sum {k} + {lam} · {c - 1} = {k + lam * (c - 1)}, sum ±{s} and
autocorrelation {lam} · {c} = {lam * c} at every shift ≠ 0; `noVector` (`decide +kernel`)
finds no such vector. Quotient from E5; this file is generated by `solver/answer.py`."""
    theorem = f"""/-- {instance}: {pretty} has no signed difference set with parameters ({v}, {k}, {lam}). -/
theorem not_hasSDS : ¬ HasSDS ({group}) {k} {lam_lean} :=
  not_hasSDS_of_noVector proj {c} {s} (by simp [Fintype.card_prod, ZMod.card])
    (by norm_num [Fintype.card_prod, ZMod.card])"""
    write_search(instance, "SignedDifferenceSets.Answer", ["SignedDifferenceSets.ContractionCheck"],
                 f"{instance}: no ({v}, {k}, {lam}) SDS in {pretty}", doc, proj,
                 f"Indexed.size ({quotient})", f"Indexed.addIdx ({quotient})",
                 f"({c} : ℕ)\n    (({k} : ℕ) + ({lam_lean} : ℤ) * (({c} : ℕ) - 1)) (({lam_lean} : ℤ) * ({c} : ℕ)) ({k} : ℕ) {s}",
                 "the contraction and the subtree check", "Instance's search arguments (those `not_hasSDS_of_noVector` asks for)",
                 n, c, k + lam * (c - 1), s, theorem, depth=depth)


def write_search(name: str, prefix: str, imports: list, title: str, doc: str, header: str, size: str, add: str,
                 args: str, check_title: str, check_doc: str, n: int, c: int, q: int, s: int, theorem: str,
                 close: str = "", depth: str = "", tool: str = "solver/answer.py",
                 split_nodes: int = SPLIT_NODES, top_depth: str = "") -> None:
    """A `noVector` search on `n` elements (bound `c`, square sum `q`, sum `s`) closing `theorem`, whose next argument
    is the search (`close` follows it): one module `<prefix>.<name>` when it has at most SPLIT_NODES nodes, else
    `<name>/Check` (`header`, `check` = `below <size> <add> <args>`, `decodePrefix`), part modules of at most
    PART_NODES nodes in kernel checks of at most BATCH_NODES, and the join `<prefix>.<name>` (`split_nodes` replaces
    SPLIT_NODES). With `top_depth` the split has two levels (`write_search_tree`)."""
    if top_depth:
        return write_search_tree(name, prefix, imports, title, doc, header, size, add, args, check_title, check_doc,
                                 n, c, q, s, theorem, close, int(depth), int(top_depth), tool)
    ns = f"{prefix}.{name}"
    folder = "/".join(prefix.split(".")[1:] + [name])
    total = sum(prefix_nodes(n, c, q, s, 1).values()) + 1
    if total <= split_nodes:
        write_module(name, imports, title, doc, f"""{header}
set_option maxRecDepth 100000 in
-- `decide +kernel` runs the vector search.
{theorem} (by decide +kernel){close}""", ns=ns, prefix=prefix)
        return
    depth = int(depth) if depth else next(d for d in range(2, n + 1)
                                          if max(prefix_nodes(n, c, q, s, d).values()) <= BRANCH_NODES)
    counts = prefix_nodes(n, c, q, s, depth)
    batches, cur, size_ = [], [], 0  # as evenrows.py: one `decide +kernel` per batch of prefixes
    for pre, cnt in counts.items():
        if cur and size_ + cnt > BATCH_NODES:
            batches.append((cur, size_))
            cur, size_ = [], 0
        cur.append(pre)
        size_ += cnt
    batches.append((cur, size_))
    parts, cur, size_ = [], [], 0  # batch indices per part module
    for j, (_, cnt) in enumerate(batches):
        if cur and size_ + cnt > PART_NODES:
            parts.append(cur)
            cur, size_ = [], 0
        cur.append(j)
        size_ += cnt
    parts.append(cur)
    base = 2 * c + 1  # a prefix is one ℕ: its coordinates plus c as base-(2c+1) digits (ℤ list literals elaborate slowly)

    def code(p):
        return sum((x + c) * base ** i for i, x in enumerate(p))

    def wrapped(pieces, indent, width=98):
        out, line = [], indent
        for piece in pieces:
            if len(line) + len(piece) > width and line.strip():
                out.append(line.rstrip())
                line = indent
            line += piece
        return "\n".join(out + [line])

    sub = LEAN_DIR / prefix.replace(".", "/") / name
    sub.mkdir(parents=True, exist_ok=True)
    for old in sub.glob("Part*.lean"):
        old.unlink()
    shared = f"Shared by `{folder}/PartNN.lean` (the prefix batches) and `{folder}.lean` (the join);"
    if len(shared) > 100:
        shared = f"Shared by `{folder}/PartNN.lean` (the prefix batches)\nand `{folder}.lean` (the join);"
    below_call = f"  below ({size}) ({add}) {args} p"
    if any(len(line) > 100 for line in below_call.split("\n")):
        below_call = f"  below ({size})\n    ({add})\n    {args} p"
    write_module(f"{name}/Check", imports, f"{name}: {check_title}",
                 f"{shared}\n"
                 f"generated by `{tool}`.",
                 f"""{header}
/-- `below` with this {check_doc}. -/
abbrev check (p : List ℤ) : Bool :=
{below_call}

/-- A prefix stored as one number: coordinate `i` plus {c} is its base-{base} digit `i`. -/
def decodePrefix (x : ℕ) : List ℤ :=
  (List.range {depth}).map fun i => ((x / {base} ^ i % {base} : ℕ) : ℤ) - {c}""", ns=ns, prefix=prefix)
    for num, js in enumerate(parts):
        body = "\n\n".join(
            f"/-- Prefixes, batch {j} ({batches[j][1]} nodes). -/\n"
            f"def batch{j} : List (List ℤ) :=\n  List.map decodePrefix [\n"
            + wrapped([f"{code(p)}, " for p in batches[j][0][:-1]] + [f"{code(batches[j][0][-1])}]"], "    ") + "\n\n"
            f"set_option maxRecDepth 100000 in\ntheorem below{j} : ∀ p ∈ batch{j}, check p = true := by\n  decide +kernel"
            for j in js)
        write_module(f"{name}/Part{num:02d}", [f"{ns}.Check"], f"{name}: prefix batches {js[0]}–{js[-1]}",
                     f"{sum(batches[j][1] for j in js)} search nodes in {len(js)} kernel checks of at most {BATCH_NODES};\n"
                     f"generated by `{tool}`.",
                     f"-- one kernel check at a time: the subtree checks together hold too much memory\n"
                     f"set_option Elab.async false\n\n{body}", ns=ns, prefix=prefix)
    plist = wrapped([f"batch{j} ++ " for j in range(len(batches) - 1)] + [f"batch{len(batches) - 1}"], "  ", 96)
    anon = wrapped([f"below{j}, " for j in range(len(batches) - 1)] + [f"below{len(batches) - 1}⟩"],
                   "            ").replace("            ", "          exact ⟨", 1)
    write_module(name, [f"{ns}.Part{num:02d}" for num in range(len(parts))], title,
                 doc + f"\nThe {total} search nodes are checked in {len(batches)} batches over {len(parts)} part modules\n"
                 f"(`{folder}/PartNN.lean`).",
                 f"""/-- The prefixes of {depth} coordinates, the batches in order. -/
def prefixes : List (List ℤ) :=
{plist}

set_option maxHeartbeats 4000000 in
-- elaborating the join over the batches
set_option maxRecDepth 100000 in
{theorem}
    (noVector_of_top (P := prefixes) (d := {depth - 1}) (by decide)
      (by decide +kernel) fun p hp => by
        have h : ∀ p ∈ prefixes, check p = true := by
          simp only [prefixes, List.forall_mem_append{", and_assoc" if len(batches) > 2 else ""}]
{anon}
        exact h p hp){close}""", ns=ns, prefix=prefix)


def wrap(pieces, indent, width=98):
    """`pieces` joined into lines of at most `width` characters, each starting with `indent`."""
    out, line = [], indent
    for piece in pieces:
        if len(line) + len(piece) > width and line.strip():
            out.append(line.rstrip())
            line = indent
        line += piece
    return "\n".join(out + [line])


def write_search_tree(name, prefix, imports, title, doc, header, size, add, args, check_title, check_doc, n, c, q, s,
                      theorem, close, depth, top_depth, tool):
    """`write_search` on two levels: the join covers the prefixes of `top_depth` coordinates (the groups); group `i`'s
    theorem covers the prefixes of `depth` coordinates below it (`below_of_top`), checked in batches that stay inside
    the group, in the part module of the group's last batch (which imports the parts with its other batches). Both
    coverage checks grow with the square of their list, so the two levels keep each list short."""
    ns = f"{prefix}.{name}"
    folder = "/".join(prefix.split(".")[1:] + [name])
    total = sum(prefix_nodes(n, c, q, s, 1).values()) + 1
    counts = prefix_nodes(n, c, q, s, depth)
    tops = list(prefix_nodes(n, c, q, s, top_depth))
    kids = {t: [] for t in tops}
    for pre in counts:
        kids[pre[:top_depth]].append(pre)
    batches, group_batches = [], []  # batch: (prefixes, nodes); per group its batch indices
    for t in tops:
        mine, cur, size_ = [], [], 0
        for pre in kids[t]:
            if cur and size_ + counts[pre] > BATCH_NODES:
                mine.append(len(batches))
                batches.append((cur, size_))
                cur, size_ = [], 0
            cur.append(pre)
            size_ += counts[pre]
        if cur:
            mine.append(len(batches))
            batches.append((cur, size_))
        group_batches.append(mine)
    parts, cur, size_ = [], {"batches": [], "groups": []}, 0
    part_of = {}
    for g, mine in enumerate(group_batches):
        for j in mine:
            if (cur["batches"] or cur["groups"]) and size_ + batches[j][1] > PART_NODES:
                parts.append(cur)
                cur, size_ = {"batches": [], "groups": []}, 0
            cur["batches"].append(j)
            part_of[j] = len(parts)
            size_ += batches[j][1]
        cur["groups"].append(g)
    parts.append(cur)
    base = 2 * c + 1

    def code(p):
        return sum((x + c) * base ** i for i, x in enumerate(p))

    sub = LEAN_DIR / prefix.replace(".", "/") / name
    sub.mkdir(parents=True, exist_ok=True)
    for old in sub.glob("Part*.lean"):
        old.unlink()
    below_call = f"  below ({size}) ({add}) {args} p"
    if any(len(line) > 100 for line in below_call.split("\n")):
        below_call = f"  below ({size})\n    ({add})\n    {args} p"
    write_module(f"{name}/Check", imports + ["SignedDifferenceSets.VectorSearchTree"], f"{name}: {check_title}",
                 f"Shared by `{folder}/PartNN.lean` (the groups and their batches)\nand `{folder}.lean` (the join);"
                 f" generated by `{tool}`.",
                 f"""{header}
/-- `below` with this {check_doc}. -/
abbrev check (p : List ℤ) : Bool :=
{below_call}

/-- A prefix of {depth} coordinates as one number: coordinate `i` plus {c} is base-{base} digit `i`. -/
def decodePrefix (x : ℕ) : List ℤ :=
  (List.range {depth}).map fun i => ((x / {base} ^ i % {base} : ℕ) : ℤ) - {c}

/-- A group's prefix of {top_depth} coordinates, stored as `decodePrefix`'s. -/
def decodeTop (x : ℕ) : List ℤ :=
  (List.range {top_depth}).map fun i => ((x / {base} ^ i % {base} : ℕ) : ℤ) - {c}""", ns=ns, prefix=prefix)

    def all_of(names):
        if not names:
            return "(by simp)"
        if len(names) == 1:
            return names[0]
        assoc = ", and_assoc" if len(names) > 2 else ""
        tup = wrap([f"{x}, " for x in names[:-1]] + [f"{names[-1]}⟩"], "        ", 93).replace("        ", "      exact ⟨", 1)
        return f"(by\n      simp only [List.forall_mem_append{assoc}]\n{tup})"

    for num, part in enumerate(parts):
        items = []
        for j in part["batches"]:
            items.append(
                f"/-- Prefixes, batch {j} ({batches[j][1]} nodes). -/\n"
                f"def batch{j} : List (List ℤ) :=\n  List.map decodePrefix [\n"
                + wrap([f"{code(p)}, " for p in batches[j][0][:-1]] + [f"{code(batches[j][0][-1])}]"], "    ") + "\n\n"
                f"set_option maxRecDepth 100000 in\ntheorem below{j} : ∀ p ∈ batch{j}, check p = true := by\n"
                f"  decide +kernel")
        for g in part["groups"]:
            mine = group_batches[g]
            plist = "[]" if not mine else " ++ ".join(f"batch{j}" for j in mine)
            if len(plist) > 60:
                plist = "\n      " + wrap([f"batch{j} ++ " for j in mine[:-1]] + [f"batch{mine[-1]}"], "      ", 96).lstrip()
            items.append(
                f"/-- Group {g}: the prefix `{list(tops[g])}`, {sum(len(batches[j][0]) for j in mine)} prefixes below it. -/\n"
                f"def top{g} : List ℤ := decodeTop {code(tops[g])}\n\n"
                f"set_option maxRecDepth 100000 in\ntheorem group{g} : check top{g} = true :=\n"
                f"  below_of_top (P := {plist}) (d := {depth - top_depth})\n"
                f"    (by decide) (by decide) (by decide +kernel)\n"
                f"    {all_of([f'below{j}' for j in mine])}")
        deps = sorted({part_of[j] for g in part["groups"] for j in group_batches[g]} - {num})
        nodes = sum(batches[j][1] for j in part["batches"])
        write_module(f"{name}/Part{num:02d}", [f"{ns}.Check"] + [f"{ns}.Part{d:02d}" for d in deps],
                     f"{name}: batches and groups, part {num}",
                     f"{nodes} search nodes in {len(part['batches'])} kernel checks of at most {BATCH_NODES} and "
                     f"{len(part['groups'])} group\nchecks; generated by `{tool}`.",
                     f"-- one kernel check at a time: the subtree checks together hold too much memory\n"
                     f"set_option Elab.async false\n\n" + "\n\n".join(items), ns=ns, prefix=prefix)
    plist = wrap([f"top{g}, " for g in range(len(tops) - 1)] + [f"top{len(tops) - 1}]"], "  ", 96).replace("  ", "  [", 1)
    tup = wrap([f"group{g}, " for g in range(len(tops) - 1)] + [f"group{len(tops) - 1}⟩"],
               "            ", 93).replace("            ", "          exact ⟨", 1)
    write_module(name, [f"{ns}.Part{num:02d}" for num in range(len(parts))], title,
                 doc + f"\nThe {total} search nodes are checked in {len(batches)} batches under {len(tops)} groups over "
                 f"{len(parts)} part\nmodules (`{folder}/PartNN.lean`).",
                 f"""/-- The groups' prefixes of {top_depth} coordinates. -/
def prefixes : List (List ℤ) :=
{plist}

set_option maxHeartbeats 4000000 in
-- elaborating the join over the groups
set_option maxRecDepth 100000 in
{theorem}
    (noVector_of_top (P := prefixes) (d := {top_depth - 1}) (by decide)
      (by decide +kernel) fun p hp => by
        have h : ∀ p ∈ prefixes, check p = true := by
          simp only [prefixes, List.forall_mem_cons, List.forall_mem_nil, and_true]
{tup}
        exact h p hp){close}""", ns=ns, prefix=prefix)


def write_module(name: str, imports: list, title: str, doc: str, body: str, ns: str = "",
                 prefix: str = "SignedDifferenceSets.Answer") -> None:
    """`<prefix>/<name>.lean` (under `lean/`): a module with public imports, a doc-string and `body` in namespace `ns`."""
    ns = ns or f"{prefix}.{name}"
    imps = "".join(f"public import {m}\n" for m in imports)
    path = LEAN_DIR / prefix.replace(".", "/") / f"{name}.lean"
    path.write_text(f"""module

{imps}
/-!
# {title}

{doc}
-/

@[expose] public section

namespace {ns}

{body}

end {ns}
""", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    cmd, *args = sys.argv[1:]
    {"object": write_object, "lean": write_lean, "fast": write_fast, "split": write_split,
     "contract": write_contract}[
        cmd
    ](*args)
