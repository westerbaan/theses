#!/usr/bin/env python3
"""Build the Sorry Map: one box per thesis statement, coloured by proof status.

Inputs, both relative to `lean/`:

  docs/status.txt    written by `scripts/StatusDump.lean` — `module|name|status`
  docs/why-open.csv  `name|category|blocker|reason`, one row per open statement

Output:

  docs/sorry-map.html

Colours follow the authors' spec: green proved, **yellow blocked on another
sorry**, red otherwise — and each red carries a mark for *why* it is open, so
the categories are legible without hovering.

Granularity is one box per **thesis statement**, keyed off the `**DISP**` number
in each declaration's doc comment, not per Lean theorem: the tree has ~4000
theorems and ~1600 of them transcribe a numbered point, so a per-theorem map
drowns the ~100 open ones in auxiliary lemmas.

⚠ Every *open* declaration is included whether or not a DISP number was found.
The DISP scan misses a handful (private declarations whose doc comment carries
no number), and a map that hides a `sorry` is worse than no map.

Usage, from `lean/`:

    lake env lean scripts/StatusDump.lean     # refresh docs/status.txt
    python3 scripts/sorry_map.py              # rebuild docs/sorry-map.html

Keeping `docs/why-open.csv` current is manual: when a statement closes its row
becomes inert, and when a `blocked` row's blocker is proved the row goes stale.
The script reports both, so run it after every batch and fix what it flags.
"""

import collections
import glob
import html
import re
import subprocess
import sys

DOCS = "docs/"
CHAPTERS = [
    ("Thesis A · C*-algebras", "Theses.A.CStar",
     ["Basic", "Positive", "Representation", "Matrices", "TowardsVN"]),
    ("Thesis A · von Neumann algebras", "Theses.A.VN",
     ["Basic", "Completeness", "Projections", "Division", "NormalFunctionals"]),
    ("Thesis A · Processes", "Theses.A.Proc",
     ["Measurement", "Tensor", "Duplicators", "QuantumLambda"]),
    ("Thesis B · Dilations", "Theses.B.Dils",
     ["HilbertModules", "SelfDualCompletion", "SelfDual", "Kaplansky",
      "Stinespring", "Paschke", "Pure"]),
    ("Thesis B · Effectuses", "Theses.B.Eff",
     ["EffectAlgebras", "StatesPredicates", "Effectus", "Quotients",
      "Comparisons", "Dagger", "DiamondAmp", "WStarCat"]),
]
CATEGORIES = [
    ("proved", "proved outright"),
    ("blocked", "waits on another sorry — hover shows which"),
    ("costed", "analysed and costed; not yet built"),
    ("open", "no analysis recorded; not attempted"),
    ("cited", "thesis cites the literature; nothing to transcribe"),
    ("awaiting-ruling", "needs an author decision"),
    ("false", "false as printed; kept as a record"),
]


def disp_numbers():
    """Map each theorem name to the `**DISP**` number in its doc comment."""
    out = {}
    for path in glob.glob("Theses/[AB]/*/*.lean"):
        doc = []
        for line in open(path).read().split("\n"):
            if line.startswith("/--"):
                doc = [line]
            elif doc:
                doc.append(line)
            m = re.match(r"(?:private |protected |noncomputable )*theorem"
                         r"\s+([A-Za-z_][A-Za-z0-9_'′ᵣ!]*)", line)
            if m:
                d = re.search(r"\*\*(\d+[IVXa-z]+)\*\*", " ".join(doc[-45:]))
                if d:
                    out[m.group(1)] = d.group(1)
                doc = []
    return out



AUDIT_COMMIT = "4d92c75"   # the commit at which the statement audit was complete


def audit_rows():
    """`lean_name` -> (stmt, proof, note, status) from docs/audit/*.csv.

    Rows flagged by the audit carry a seventh field, written by the
    re-verification of 2026-08-21: `repaired`, `open`, or `left-<reason>`.
    Only a row that is neither `repaired` nor `left-benign` still marks a real
    mismatch, so only those are drawn.  Rows with six fields predate the
    re-verification (or were never flagged) and carry no status.
    """
    out = {}
    for path in sorted(glob.glob(DOCS + "audit/*.csv")):
        for i, line in enumerate(open(path, encoding="utf-8")):
            f = line.rstrip("\n").split("|")
            if i == 0 or len(f) not in (6, 7):
                continue
            status = ""
            if len(f) == 7:
                status = re.split(r"[\s:,]", f[6].strip(), maxsplit=1)[0].rstrip("-")
            name = f[1].strip()
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'\u2032\u1d63!.]*", name):
                continue          # rows naming an `example`, a structure field, …
            out.setdefault(name.split(".")[-1],
                           (f[3].strip(), f[4].strip(), f[5].strip(), status))
    return out


#: a flagged row still counts as a mismatch unless it is one of these
SETTLED = ("repaired", "left-benign")


def touched_since_audit():
    """Declaration names appearing in the diff since the audit finished."""
    d = subprocess.run(["git", "diff", AUDIT_COMMIT + "..HEAD", "--", "Theses"],
                       capture_output=True, text=True).stdout
    return set(re.findall(r"^[+-]\s*(?:private |protected |noncomputable )*"
                          r"(?:theorem|def|structure|class|instance)\s+"
                          r"([A-Za-z_][A-Za-z0-9_'\u2032\u1d63!]*)", d, re.M))

def load():
    why = {}
    for line in open(DOCS + "why-open.csv"):
        p = line.rstrip("\n").split("|")
        if len(p) >= 4:
            why[p[0]] = (p[1], p[2], p[3])
    rows = [l.split("|") for l in
            open(DOCS + "status.txt").read().strip().split("\n")]
    return why, rows


def audit(why, rows):
    """Report stale classification rows — the failure mode this map has hit twice."""
    open_now = {r[1].split(".")[-1] for r in rows if r[2] != "green"}
    known = {r[1].split(".")[-1] for r in rows}
    missing = sorted(n for n in open_now
                     if n not in why and not any(k.endswith("." + n) for k in why))
    stale = [(p[0], p[2]) for p in
             (l.rstrip("\n").split("|") for l in open(DOCS + "why-open.csv"))
             if len(p) >= 4 and p[1] == "blocked" and p[0] in open_now
             and p[2].strip() and p[2] in known and p[2] not in open_now]
    if missing:
        print(f"  ⚠ {len(missing)} open statements have no classification: "
              f"{', '.join(missing[:8])}{' …' if len(missing) > 8 else ''}")
    if stale:
        print(f"  ⚠ {len(stale)} 'blocked' rows name a blocker that is now proved:")
        for a, b in stale:
            print(f"      {a} → {b}")
    if not missing and not stale:
        print("  classification is current")


def main():
    why, rows = load()
    n2d = disp_numbers()
    aud = audit_rows()
    touched = touched_since_audit()
    print(f"{len(rows)} theorems, {len(n2d)} carry a DISP number")
    audit(why, rows)
    flagged = [v for v in aud.values() if v[0] != "ok"]
    st = collections.Counter(v[3] or "unverified" for v in flagged)
    print(f"  statement audit: {len(aud)} rows joined by name, {len(flagged)} flagged; "
          + ", ".join(f"{n} {k}" for k, n in sorted(st.items(), key=lambda x: -x[1])))

    items = collections.defaultdict(list)
    for mod, full, status in rows:
        short = full.split(".")[-1]
        if status == "green":
            if short in n2d:
                items[mod].append((n2d[short], short, "proved", "", ""))
        else:
            w = (why.get(short) or why.get(".".join(full.split(".")[-2:]))
                 or ("open", "", "no classification recorded"))
            items[mod].append((n2d.get(short, "—"), short, w[0], w[1], w[2]))

    counts = collections.Counter(i[2] for v in items.values() for i in v)
    total = sum(counts.values())
    proved, blocked = counts["proved"], counts["blocked"]
    sorry = total - proved - blocked

    def sort_key(t):
        m = re.match(r"(\d+)", t[0])
        return (int(m.group(1)) if m else 9999, t[0], t[1])

    sections = []
    acount = collections.Counter()
    pcount = collections.Counter()
    for title, prefix, files in CHAPTERS:
        mods = [f"{prefix}.{f}" for f in files if f"{prefix}.{f}" in items]
        c = collections.Counter(i[2] for m in mods for i in items[m])
        n = sum(c.values())
        rest = n - c["proved"]
        rows_html = []
        for m in mods:
            it = sorted(items[m], key=sort_key)
            fc = collections.Counter(i[2] for i in it)
            still = len(it) - fc["proved"]
            def box(d, nm, cat, bl, rs):
                av, ap, an, st = aud.get(nm, ("", "", "", ""))
                live = bool(av) and av != "ok" and st not in SETTLED
                if live:
                    acount[av] += 1
                route = ap == "route"
                if route:
                    pcount[av or "ok"] += 1
                mark = (" aud" if live else "") + (" prt" if route else "")
                return (f'<i class="b k-{cat}{mark}" tabindex="0" '
                        f'data-d="{html.escape(d)}" data-n="{html.escape(nm)}" '
                        f'data-c="{cat}" data-k="{html.escape(bl)}" '
                        f'data-r="{html.escape(rs)}" data-a="{av}" data-ap="{ap}" '
                        f'data-s="{html.escape(st)}" '
                        f'data-t="{"1" if nm in touched else ""}" '
                        f'data-an="{html.escape(an[:400])}">'
                        f'{"<i class=pw></i>" if route else ""}</i>')
            boxes = "".join(box(*t) for t in it)
            tail = ""
            if fc["blocked"]:
                tail += f' · <s class=y>{fc["blocked"]} blocked</s>'
            if still - fc["blocked"]:
                tail += f' · <s class=r>{still - fc["blocked"]} sorry</s>'
            if not still:
                tail += " · <s class=ok>complete</s>"
            rows_html.append(
                f'<div class="file{"" if still else " clean"}"><div class="fh">'
                f'<span class="fn">{m.split(".")[-1]}</span>'
                f'<span class="fc">{len(it)}{tail}</span></div>'
                f'<div class="grid">{boxes}</div></div>')
        head = ""
        if c["blocked"]:
            head += f' · <s class=y>{c["blocked"]}</s>'
        if rest - c["blocked"]:
            head += f' · <s class=r>{rest - c["blocked"]}</s>'
        if not rest:
            head += " · <s class=ok>complete</s>"
        sections.append(f'<section><h2>{title}<span class="sc">{n}{head}</span>'
                        f'</h2>{"".join(rows_html)}</section>')

    abad = sum(acount.values())
    pbad = sum(pcount.values())
    achips = "".join(
        f'<button class="acat" data-acat="{k}" aria-pressed="false">'
        f'<i class="sw aud"></i>stmt {k} <b>{acount[k]}</b></button>'
        for k in ("weaker", "stronger", "differs", "unsure") if acount[k])
    chips = "".join(
        f'<button class="cat" data-cat="{k}" aria-pressed="false">'
        f'<i class="sw k-{k}"></i>{k} <b>{counts[k]}</b></button>'
        for k, _ in CATEGORIES if counts[k] and k != "proved")
    legend = "".join(
        f'<tr><td><i class="sw k-{k}"></i></td><td><code>{k}</code></td>'
        f'<td class=num>{counts[k]}</td><td>{d}</td></tr>'
        for k, d in CATEGORIES if counts[k])

    commit = subprocess.run(["git", "log", "-1", "--format=%h %ad", "--date=short"],
                            capture_output=True, text=True).stdout.strip()

    doc = TEMPLATE.format(
        abad=abad, achips=achips, aaudited=len(aud), pbad=pbad,
        total=total, proved=proved, blocked=blocked, sorry=sorry,
        pct=proved / total * 100, blkpct=blocked / total * 100,
        sorrypct=sorry / total * 100, commit=commit,
        legend=legend, chips=chips, sections="".join(sections))
    open(DOCS + "sorry-map.html", "w").write(doc)
    print(f"wrote {DOCS}sorry-map.html — {total} boxes: "
          f"{proved} proved, {blocked} blocked, {sorry} sorry; "
          f"{abad} carry a statement-audit flag, "
          f"{pbad} a proof-route flag")


TEMPLATE = '''<title>Sorry Map</title>
<style>
:root{{--ground:#f6f7f9;--panel:#fff;--ink:#1b1e24;--dim:#697079;--rule:#e3e5ea;--ok:#8fc7a6;--okd:#2f9e5f;--bad:#d43d4f;--warn:#e6a41c;--accent:#4c5fd7;--accent2:#0d8f8f}}
@media(prefers-color-scheme:dark){{:root:not([data-theme=light]){{--ground:#0f1116;--panel:#171a21;--ink:#e7e9ed;--dim:#8d949f;--rule:#252a33;--ok:#31543f;--okd:#3fbf76;--bad:#ff5d6c;--warn:#f5b62f;--accent:#8492f5;--accent2:#3fd0c9}}}}
:root[data-theme=dark]{{--ground:#0f1116;--panel:#171a21;--ink:#e7e9ed;--dim:#8d949f;--rule:#252a33;--ok:#31543f;--okd:#3fbf76;--bad:#ff5d6c;--warn:#f5b62f;--accent:#8492f5;--accent2:#3fd0c9}}
*{{box-sizing:border-box}}
body{{background:var(--ground);color:var(--ink);font:15px/1.55 system-ui,-apple-system,"Segoe UI",sans-serif;margin:0;padding:0 20px 96px}}
.wrap{{max-width:1120px;margin:0 auto}}
header{{padding:40px 0 16px}} h1{{font-size:31px;letter-spacing:-.021em;margin:0 0 5px}}
.prov{{color:var(--dim);font:12.5px ui-monospace,SFMono-Regular,Menlo,monospace}}
.sum{{display:flex;flex-wrap:wrap;gap:30px;align-items:flex-end;padding:20px 0 12px}}
.big{{font:600 28px/1 ui-monospace,SFMono-Regular,Menlo,monospace;font-variant-numeric:tabular-nums}}
.lab{{color:var(--dim);font-size:11.5px;text-transform:uppercase;letter-spacing:.09em;margin-top:5px}}
.bar{{display:flex;height:8px;border-radius:4px;overflow:hidden;margin:4px 0 22px;background:var(--rule)}}
table{{border-collapse:collapse;width:100%;margin:0 0 20px;font-size:13.5px}}
td{{padding:6px 10px 6px 0;border-bottom:1px solid var(--rule);color:var(--dim);vertical-align:middle}}
td code{{font:12.5px ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--ink)}}
td.num{{font:600 12.5px ui-monospace,SFMono-Regular,Menlo,monospace;font-variant-numeric:tabular-nums;color:var(--ink);text-align:right;width:52px}}
td:first-child{{width:26px}}
.tools{{position:sticky;top:0;z-index:5;background:var(--ground);padding:11px 0;border-bottom:1px solid var(--rule);display:flex;gap:8px;align-items:center;flex-wrap:wrap}}
button{{font:inherit;font-size:12.5px;color:var(--ink);background:var(--panel);border:1px solid var(--rule);border-radius:999px;padding:4px 12px;cursor:pointer;display:inline-flex;align-items:center;gap:6px}}
button b{{font-variant-numeric:tabular-nums;color:var(--dim);font-weight:600}}
button[aria-pressed=true]{{border-color:var(--accent);color:var(--accent);font-weight:600}}
button[aria-pressed=true] b{{color:var(--accent)}}
button:focus-visible,.b:focus-visible{{outline:2px solid var(--accent);outline-offset:2px}}
section{{margin:30px 0 0}}
h2{{font-size:16.5px;margin:0 0 11px;display:flex;gap:11px;align-items:baseline;flex-wrap:wrap;border-bottom:1px solid var(--rule);padding-bottom:8px}}
.sc{{color:var(--dim);font:12.5px ui-monospace,SFMono-Regular,Menlo,monospace;font-variant-numeric:tabular-nums;font-weight:400}}
.file{{background:var(--panel);border:1px solid var(--rule);border-radius:10px;padding:13px 15px;margin-bottom:9px}}
.fh{{display:flex;justify-content:space-between;gap:12px;align-items:baseline;margin-bottom:11px}}
.fn{{font:13.5px ui-monospace,SFMono-Regular,Menlo,monospace}}
.fc{{font:12px ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--dim);font-variant-numeric:tabular-nums}}
s{{text-decoration:none;font-weight:600}} s.r{{color:var(--bad)}} s.y{{color:var(--warn)}} s.ok{{color:var(--okd)}}
.grid{{display:flex;flex-wrap:wrap;gap:4px}}
.b,.sw{{width:15px;height:15px;border-radius:3px;display:block;position:relative;flex:none}}
.sw{{display:inline-block;vertical-align:-3px}}
.k-proved{{background:var(--ok)}} .k-blocked{{background:var(--warn)}}
.k-costed{{background:var(--bad)}} .k-open{{background:var(--bad)}}
.k-open::after{{content:"";position:absolute;inset:4px;background:var(--panel);border-radius:1px}}
.k-cited{{background:transparent;box-shadow:inset 0 0 0 2.5px var(--bad)}}
.k-awaiting-ruling{{background:var(--bad);box-shadow:0 0 0 2px var(--accent)}}
.k-false{{background:var(--bad);background-image:linear-gradient(45deg,transparent 42%,var(--panel) 42%,var(--panel) 58%,transparent 58%)}}
.aud::before{{content:"";position:absolute;top:0;right:0;width:0;height:0;
border:5px solid transparent;border-top-color:var(--accent);border-right-color:var(--accent);border-radius:0 3px 0 0}}
.sw.aud{{background:var(--rule)}}
.pw{{content:"";position:absolute;left:0;bottom:0;width:0;height:0;
border:5px solid transparent;border-bottom-color:var(--accent2);border-left-color:var(--accent2);border-radius:0 0 0 3px}}
.sw.prt{{background:var(--rule);position:relative}}
.sw.prt::after{{content:"";position:absolute;left:0;bottom:0;width:0;height:0;
border:5px solid transparent;border-bottom-color:var(--accent2);border-left-color:var(--accent2);border-radius:0 0 0 3px}}
.b:hover,.b:focus-visible{{transform:scale(1.7);z-index:2}}
body.only .b.k-proved{{display:none}} body.only .file.clean{{display:none}}
body.filt .b:not(.on){{display:none}} body.filt .file.clean{{display:none}}
body.aonly .b:not(.aud){{display:none}}
body.ponly .b:not(.prt){{display:none}}
.read{{position:fixed;left:0;right:0;bottom:0;background:var(--panel);border-top:1px solid var(--rule);padding:9px 20px;font:12.5px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--dim);min-height:54px}}
.read b{{color:var(--ink)}} .read u{{text-decoration:none;color:var(--accent)}}
@media(prefers-reduced-motion:reduce){{.b:hover,.b:focus-visible{{transform:none}}}}
</style>
<div class="wrap"><header><h1>Sorry Map</h1>
<div class="prov">{total} thesis statements · Lean 4 + Mathlib · commit {commit}</div></header>
<div class="sum">
<div><div class="big" style="color:var(--okd)">{proved}</div><div class="lab">proved</div></div>
<div><div class="big" style="color:var(--warn)">{blocked}</div><div class="lab">blocked on a sorry</div></div>
<div><div class="big" style="color:var(--bad)">{sorry}</div><div class="lab">sorry</div></div>
<div><div class="big">{pct:.1f}%</div><div class="lab">axiom-clean</div></div>
<div><div class="big" style="color:var(--accent)">{abad}</div><div class="lab">statement ≠ source</div></div>
<div><div class="big" style="color:var(--accent2)">{pbad}</div><div class="lab">proof ≠ thesis&#39;s</div></div></div>
<div class="bar"><i style="background:var(--okd);width:{pct:.3f}%"></i><i style="background:var(--warn);width:{blkpct:.3f}%"></i><i style="background:var(--bad);width:{sorrypct:.3f}%"></i></div>
<table><tbody>{legend}
<tr><td><i class="sw aud"></i></td><td><code>stmt ≠ source</code></td><td class=num>{abad}</td>
<td>corner wedge: this rendering still does not match its thesis point, independently of whether it is proved. The statement audit of 2026-08-20 checked {aaudited} declarations and flagged 253; all 30 modules were then repaired, and every flagged row was <b>re-verified against the tree on 2026-08-21</b>. A wedge means the row came back <code>open</code> (repairable, nothing blocking), <code>left-thesis</code> (the printed point is defective, so matching it would import a falsehood), <code>left-ruling</code> (an open question in <code>QUESTIONS.md</code> governs it) or <code>left-cost</code> (costed and declined). Rows that came back <code>repaired</code> or <code>left-benign</code> — a true generalisation the thesis's setting supplies — carry no wedge. Hover for the verdict, the finding and the current status.</td></tr>
<tr><td><i class="sw prt"></i></td><td><code>proof ≠ thesis&#39;s</code></td><td class=num>{pbad}</td>
<td>lower-left wedge: the statement is the thesis&#39;s, but the Lean proof does not follow the printed argument. This is the audit&#39;s <code>proof</code> column, which the proof-route passes of 2026-08-22/25 maintain: a row loses the wedge when its proof is put back on the thesis&#39;s route, and only then. A wedge is not by itself a defect — the thesis sometimes gives no proof at all, sometimes the printed route is the one an erratum corrects, and sometimes Mathlib states the same step — but it does mean the argument you read in the thesis is not the argument the machine checked. Hover for the finding and the reason it stands.</td></tr>
</tbody></table>
<div class="tools"><button id="a" aria-pressed="true">All {total}</button><button id="o" aria-pressed="false">Unproved {blocked}+{sorry}</button><button id="ab" aria-pressed="false"><i class="sw aud"></i>stmt ≠ source <b>{abad}</b></button><button id="pb" aria-pressed="false"><i class="sw prt"></i>proof ≠ thesis&#39;s <b>{pbad}</b></button>{chips}{achips}</div>
{sections}</div>
<div class="read" id="rd">Hover or focus a box for its thesis number, category and reason.</div>
<script>
const rd=document.getElementById('rd'),a=document.getElementById('a'),o=document.getElementById('o');
function show(e){{const t=e.target.closest('.b');if(!t)return;const c=t.dataset.c,a=t.dataset.a;
let h='<b>'+t.dataset.d+'</b> &nbsp; '+t.dataset.n+(c=='proved'?' &nbsp; <em>proved</em>':
'<br><u>'+c+'</u>'+(t.dataset.k?' → '+t.dataset.k:'')+' &nbsp; '+t.dataset.r);
if(a&&a!='ok')h+='<br><u>stmt '+a+'</u>'+(t.dataset.ap?' · proof '+t.dataset.ap:'')+
(t.dataset.s?' · <b>'+t.dataset.s+'</b>':'')+
(t.dataset.t?' · <em>declaration changed since the audit</em>':'')+' &nbsp; '+t.dataset.an;
else if(t.dataset.ap=='route')h+='<br><u>proof route</u>'+
(t.dataset.s?' · <b>'+t.dataset.s+'</b>':'')+
(t.dataset.t?' · <em>declaration changed since the audit</em>':'')+' &nbsp; '+t.dataset.an;
rd.innerHTML=h;}}
document.addEventListener('mouseover',show);document.addEventListener('focusin',show);
const cats=[...document.querySelectorAll('.cat')],acats=[...document.querySelectorAll('.acat')],ab=document.getElementById('ab'),pb=document.getElementById('pb');
function clr(){{cats.forEach(c=>c.ariaPressed='false');acats.forEach(c=>c.ariaPressed='false');ab.ariaPressed='false';pb.ariaPressed='false';document.querySelectorAll('.b.on').forEach(b=>b.classList.remove('on'))}}
a.onclick=()=>{{clr();document.body.className='';a.ariaPressed='true';o.ariaPressed='false'}};
o.onclick=()=>{{clr();document.body.className='only';o.ariaPressed='true';a.ariaPressed='false'}};
cats.forEach(c=>c.onclick=()=>{{clr();a.ariaPressed='false';o.ariaPressed='false';c.ariaPressed='true';
document.querySelectorAll('.b.k-'+c.dataset.cat).forEach(b=>b.classList.add('on'));document.body.className='filt'}});
ab.onclick=()=>{{clr();a.ariaPressed='false';o.ariaPressed='false';ab.ariaPressed='true';document.body.className='aonly'}};
pb.onclick=()=>{{clr();a.ariaPressed='false';o.ariaPressed='false';pb.ariaPressed='true';document.body.className='ponly'}};
acats.forEach(c=>c.onclick=()=>{{clr();a.ariaPressed='false';o.ariaPressed='false';c.ariaPressed='true';
document.querySelectorAll('.b[data-a="'+c.dataset.acat+'"]').forEach(b=>b.classList.add('on'));document.body.className='filt'}});
</script>'''


if __name__ == "__main__":
    sys.exit(main())
