import subprocess, re, glob, os, collections

root = "/home/narin/src/analysis"
os.chdir(root)

def counts(rev):
    env = dict(os.environ, LEAN_PATH="Analysis/")
    out = subprocess.run(["python3","scripts/count_live_sorries.py",rev,"--per-file"],
                         capture_output=True,text=True,env=env).stdout
    d={}
    for line in out.splitlines():
        line=line.strip()
        m=re.match(r"(\d+)\s+Analysis/(.+\.lean)$",line)
        if m: d[m.group(2)] = int(m.group(1))
    return d

ours = counts("HEAD")
up   = counts("origin/main")

# all section files present at HEAD
files = subprocess.run(["git","ls-tree","-r","--name-only","HEAD","--","Analysis/"],
                       capture_output=True,text=True).stdout.splitlines()
files = [f[len("Analysis/"):] for f in files if f.endswith(".lean") and f!="Analysis.lean"]

def title(f):
    try:
        txt=open("Analysis/"+f).read()
    except: return ""
    m=re.search(r"#\s*Analysis I,\s*(.+)", txt)
    if m:
        t=m.group(1).strip()
        # strip leading "Section X.Y:" / "Chapter ..." to keep just the descriptive title
        t=re.sub(r"^(Section|Chapter|Appendix)\s+[\w.]+\s*:?\s*", "", t)
        return t
    return ""

def chapter_key(f):
    m=re.match(r"Section_(\d+)_",f)
    if m: return ("S", int(m.group(1)))
    if f.startswith("MeasureTheory/"): return ("M", 0)
    if f.startswith("Appendix_"): return ("A",0)
    return ("Z", f)

def sec_label(f):
    m=re.match(r"Section_(\d+)_(\d+(?:_\w+)?)\.lean",f)
    if m: return f"{m.group(1)}.{m.group(2).replace('_','.')}"
    m=re.match(r"Section_(\d+)_epilogue\.lean",f)
    if m: return f"{m.group(1)}.epilogue"
    m=re.match(r"Appendix_([AB])_(\d+)\.lean",f)
    if m: return f"{m.group(1)}.{m.group(2)}"
    f2=f.replace("MeasureTheory/","").replace(".lean","")
    m=re.match(r"Section_(\d+)_(\d+)_(\d+)",f2)
    if m: return f"MT {m.group(1)}.{m.group(2)}.{m.group(3)}"
    return f.replace(".lean","")

chapters = {
 1:"Chapter 2 — Natural numbers", 2:"Chapter 2 — Natural numbers",
 3:"Chapter 3 — Set theory", 4:"Chapter 4 — Integers and rationals",
 5:"Chapter 5 — Real numbers", 6:"Chapter 6 — Limits of sequences",
 7:"Chapter 7 — Series", 8:"Chapter 8 — Infinite sets",
 9:"Chapter 9 — Continuous functions on ℝ", 10:"Chapter 10 — Differentiation",
 11:"Chapter 11 — The Riemann integral",
}

rows=collections.defaultdict(list)
tot_solved=tot_total=0
for f in files:
    u=up.get(f,0); o=ours.get(f,0)
    total=max(u,o)          # exercises in this section
    if total==0:            # no exercises here
        continue
    solved=total-o
    tot_solved+=solved; tot_total+=total
    ck=chapter_key(f)
    rows[ck].append((sec_label(f), title(f), solved, total, o))

# group headers
def group_name(ck):
    if ck[0]=="S": return chapters.get(ck[1], f"Chapter {ck[1]}")
    if ck[0]=="M": return "Measure Theory (Chapter 1, draft)"
    if ck[0]=="A": return "Appendices"
    return "Other"

order=sorted(rows.keys(), key=lambda k:(0 if k[0]=="S" else 1 if k[0]=="A" else 2, k[1] if isinstance(k[1],int) else 99, str(k[1])))

lines=[]
lines.append("# Analysis I — Lean formalization (exercise solutions fork)")
lines.append("")
lines.append("A fork of **[teorth/analysis](https://github.com/teorth/analysis)** "
             "(Terence Tao's *Analysis I*, formalized in Lean 4) in which the exercises — "
             "rendered upstream as `sorry`s — are being filled in with compiler-verified proofs.")
lines.append("")
lines.append("The upstream repository deliberately leaves exercises as `sorry` and does not host "
             "solutions; this fork is an independent solving effort. `lake build` is green at every commit.")
lines.append("")
pct = round(100*tot_solved/tot_total) if tot_total else 0
lines.append(f"**Progress: {tot_solved} / {tot_total} exercises solved ({pct}%).** "
             f"Counts are *live* `sorry`s (proof-term `sorry`, excluding any in comments); "
             "“Total” is the number upstream leaves open in that section.")
lines.append("")

cur=None
for ck in order:
    g=group_name(ck)
    if g!=cur:
        cur=g
        lines.append(f"## {g}")
        lines.append("")
        lines.append("| Section | Title | Solved | Remaining | Status |")
        lines.append("|---|---|---:|---:|:--:|")
    def sortkey(r):
        lead=0 if r[0].startswith("A.") else 1 if r[0].startswith("B.") else 0
        nums=re.findall(r"\d+", r[0])
        return [lead]+([int(x) for x in nums] if nums else [999])
    for sec,ttl,solved,total,rem in sorted(rows[ck], key=sortkey):
        status="✅" if rem==0 else ("🟡" if solved>0 else "⬜")
        lines.append(f"| {sec} | {ttl} | {solved}/{total} | {rem} | {status} |")
    lines.append("")

lines.append("---")
lines.append("")
lines.append("*Legend: ✅ section complete · 🟡 partially solved · ⬜ untouched. "
             "Generated from a `lake build`-green tree; see `scripts/count_live_sorries.py`.*")

open("README.md","w").write("\n".join(lines)+"\n")
print("wrote README.md;", tot_solved,"/",tot_total, "solved across", sum(len(v) for v in rows.values()), "sections")
