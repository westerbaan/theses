#!/usr/bin/env python3
"""Rebuild `.olean`s that are older than their source, in dependency order.

Why this exists.  A single `lean` process on this tree peaks at 7.2 GB RSS on a
14 GB swapless box (see `scripts/lean1.sh`), so a full `lake build` is not
something that can be run while agents are working -- and `lake build` is banned
outright while any agent holds the tree, because killing one mid-flight leaves
another module's olean missing.  The consequence is that staleness accumulates
silently: the source is committed, every single-file compile of that file passes,
and yet nothing downstream can see the new declarations.

That is not hypothetical.  On 2026-08-29 `Pure.olean` was 46 minutes older than
`Pure.lean`, so the entire `ProcPure` section -- both directions of the
A/Proc-to-B/Dils purity bridge, committed hours earlier -- was invisible to every
compile in the tree.  An agent that needed it found out by getting an unknown
identifier.  Four more modules were stale at the same moment.

Nothing warns about this.  `lean` does not check whether an olean it loads is
older than the source beside it; it loads what is there.  So the check has to be
explicit, and this is it.

Rebuilds go through `lean1.sh`, which holds the compile lock, and each new olean
is written to a temporary file and moved into place, so an agent's concurrent
compile either sees the old one whole or the new one whole.

    scripts/refresh_oleans.py            # report what is stale
    scripts/refresh_oleans.py --write    # rebuild it, in dependency order
"""

import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve()
LEAN = HERE.parents[1]
BUILD = LEAN / ".lake" / "build" / "lib" / "lean"
IMPORT = re.compile(r'^import\s+([\w.]+)', re.M)


def modules():
    return {str(p.relative_to(LEAN).with_suffix("")).replace("/", "."): p
            for p in sorted((LEAN / "Theses").rglob("*.lean"))}


def olean(mod):
    return BUILD / (mod.replace(".", "/") + ".olean")


def stale(mods):
    """Modules whose olean is older than their source, or missing entirely."""
    out = []
    for mod, src in mods.items():
        o = olean(mod)
        if not o.exists():
            out.append((mod, None))
        elif o.stat().st_mtime < src.stat().st_mtime:
            out.append((mod, int((src.stat().st_mtime - o.stat().st_mtime) / 60)))
    return out


def order(targets, mods):
    """Topological order over the targets, following imports within the tree."""
    deps = {m: {i for i in IMPORT.findall(mods[m].read_text()) if i in targets}
            for m in targets}
    out, seen, stack = [], set(), set()
    def visit(m):
        if m in seen:
            return
        if m in stack:                      # import cycles cannot happen in Lean
            raise SystemExit(f"import cycle at {m}")
        stack.add(m)
        for d in sorted(deps[m]):
            visit(d)
        stack.discard(m)
        seen.add(m)
        out.append(m)
    for m in sorted(targets):
        visit(m)
    return out


def dirty():
    """Modules whose source has uncommitted changes -- an agent may be mid-edit.

    Rebuilding one of these would install an olean for a state that exists nowhere
    but this working tree, and possibly for a half-written file.  They are reported
    and skipped; the next run picks them up once the work is committed.
    """
    r = subprocess.run(["git", "status", "--porcelain", "--", "Theses"],
                       cwd=LEAN, capture_output=True, text=True)
    out = set()
    for line in r.stdout.splitlines():
        path = line[3:].strip().strip('"')
        if path.endswith(".lean"):
            rel = pathlib.Path(path)
            if rel.parts and rel.parts[0] == "lean":
                rel = pathlib.Path(*rel.parts[1:])
            out.add(str(rel.with_suffix("")).replace("/", "."))
    return out


def main():
    mods = modules()
    bad = stale(mods)
    if not bad:
        print(f"{len(mods)} modules, every olean at least as new as its source")
        return 0
    for mod, mins in sorted(bad):
        age = "MISSING" if mins is None else f"{mins} min older than source"
        print(f"STALE    {mod}  ({age})")
    if "--write" not in sys.argv:
        print(f"\n{len(bad)} of {len(mods)} oleans are stale; nothing downstream can see "
              f"their recent declarations.  Re-run with --write to rebuild them.")
        return 1

    held = dirty()
    targets = {m for m, _ in bad}
    skipped = sorted(targets & held)
    for m in skipped:
        print(f"SKIP     {m} -- source has uncommitted changes, may be mid-edit")
    targets -= held
    if not targets:
        print("\nnothing to rebuild: every stale module is being edited")
        return 1
    seq = order(targets, mods)
    print(f"\nrebuilding {len(seq)} in dependency order, one at a time through the "
          f"compile lock")
    failed = []
    for i, mod in enumerate(seq, 1):
        dest = olean(mod)
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = dest.with_suffix(".olean.rebuilding")
        rel = mods[mod].relative_to(LEAN)
        print(f"  [{i}/{len(seq)}] {mod} ", end="", flush=True)
        r = subprocess.run([str(HERE.parent / "lean1.sh"), "-o", str(tmp), str(rel)],
                           cwd=LEAN, capture_output=True, text=True)
        if r.returncode != 0 or not tmp.exists():
            tmp.unlink(missing_ok=True)
            failed.append(mod)
            print("FAILED -- olean left untouched")
            for line in (r.stdout + r.stderr).splitlines():
                if "error" in line:
                    print(f"        {line}")
            continue
        tmp.replace(dest)                   # atomic within the build directory
        print("ok")
    if failed:
        print(f"\n{len(seq) - len(failed)} rebuilt, {len(failed)} FAILED: "
              f"{', '.join(failed)}")
        return 1
    tail = f"; {len(skipped)} skipped as mid-edit" if skipped else ""
    print(f"\n{len(seq)} rebuilt{tail}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
