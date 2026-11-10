"""Parse the 66 row files (MaCountRows, MaDividedResRows): theorem type, w, cert. Own code."""
import re, os, csv, glob
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
LEAN = os.path.join(ROOT, "lean", "SignedDifferenceSets")

def lean_val(s):
    s = s.replace("⟨", "(").replace("⟩", ")").replace("[", "[").strip()
    return eval(s)  # only digits, brackets, commas, minus signs (checked below)

def parse(path):
    t = open(path, encoding="utf-8").read()
    th = re.search(r"theorem not_hasSDS : ¬ HasSDS \((.+?)\) (-?\d+|\(-\d+\)) (-?\d+|\(-\d+\)) :=", t)
    grp = th[1]
    gms = [int(x) for x in re.findall(r"ZMod (\d+)", grp)]
    assert re.fullmatch(r"ZMod \d+( × ZMod \d+)*", grp), grp
    k = int(th[2].strip("()")); lam = int(th[3].strip("()"))
    w = re.search(r"\(w := (⟨.*?⟩)\)", t)[1]
    c = re.search(r"\(c := (⟨.*?⟩)\)", t, re.S)[1]
    for s in (w, c):
        assert re.fullmatch(r"[⟨⟩\[\]\(\)0-9,\s\-]*", s), s
    W = lean_val(w); C = lean_val(c)
    nth = len(re.findall(r"theorem ", t))
    return dict(path=path, gms=gms, k=k, lam=lam, w=W, c=C, ntheorems=nth, text=t)

def rows():
    out = {}
    for sub in ("MaCountRows", "MaDividedResRows"):
        for f in glob.glob(os.path.join(LEAN, sub, "N*.lean")):
            out[(sub, os.path.basename(f)[:-5])] = parse(f)
    return out

def instances():
    d = {}
    for r in csv.DictReader(open(os.path.join(ROOT, "instances.csv"), encoding="utf-8")):
        m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", r["key"])
        d[r["id"]] = dict(v=int(m[1]), k=int(m[2]), lam=int(m[3]), ms=[int(x) for x in m[4].split(",")],
                          status=r["status"], source=r["source"])
    return d
