#!/usr/bin/env python3
"""Run every consistency check in this directory and summarise.

The checks accumulated one at a time, each answering a question someone had got
wrong, and there is now no single way to ask "is the bookkeeping sound?".  This
is that way.  Run it from `lean/`.

    python3 scripts/check_all.py            # summary lines only
    python3 scripts/check_all.py --full     # each check's own output too

What each one guards, and how strict it is:

* `audit_check`      -- the audit rows against the tree.  **Exact**, seven
                        checks, and must read zero.
* `coverage`         -- every claim of the five chapters has a row.
* `cite_check`       -- `label, file.tex:N` citations land in the labelled
                        point.  **Exact**, must read zero.
* `cite_check --disp`-- the same for what a DISP tag locates.  **Exact**.
* `cite_check --bare`-- bare `file.tex:N` read against the declaration they sit
                        in.  A **measurement**, not a defect list: nothing in a
                        bare reference says what it points at.
* `limb_check`       -- `docs/DEAD-LIMBS.md`'s dead-claims re-counted against
                        the tree.  Exact for the claims it can parse, which is
                        bullet heads and first table cells only.
* `vn_setting_check` -- doc comments claiming a von Neumann setting the type
                        does not have.  Needs `docs/binders.txt`, which
                        `BinderDump.lean` writes.
* `xref_check`       -- `docs/FILE.md §N` references resolve.  Qualified ones
                        only; a bare `§N` may mean another document.
* `lean_line_check`  -- `name` (`File.lean:N`) references against where the
                        declaration is.  **Exact** for the named form, which is
                        repairable with `--write` because the name pins the
                        target; bare `.lean:N` references are counted only.
* `errata_check`     -- `ERRATA.md` against its own three rules.  STATUS,
                        NOPOINT and DUP are exact; PHANTOM is a shortlist.
* `questions_check`  -- references to `QUESTIONS.md` questions that are gone.

A non-zero exit from a **shortlist** check is not a failure, and this runner
says which is which rather than adding them all up.
"""

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent

# (label, argv, exact?, pick)  -- `exact` means a non-zero exit is a real
# failure; `pick` is a substring identifying the line worth showing, for the
# checks whose last line is not their summary (`coverage.py` ends with a usage
# hint, so the naive tail reports the hint and not the numbers).
CHECKS = [
    ("audit_check",       ["audit_check.py"],            True),
    ("coverage",          ["coverage.py"],               True, "TOTAL"),
    ("cite_check",        ["cite_check.py"],             True),
    ("cite_check --disp", ["cite_check.py", "--disp"],   True),
    ("cite_check --bare", ["cite_check.py", "--bare"],   False),
    ("limb_check",        ["limb_check.py"],             True),
    ("vn_setting_check",  ["vn_setting_check.py"],       True),
    ("xref_check",        ["xref_check.py"],             True),
    ("lean_line_check",   ["lean_line_check.py"],        True),
    ("errata_check",      ["errata_check.py"],           False),
    ("questions_check",   ["questions_check.py"],        False),
    # guards the SELF_DESCRIBING exemption that question_check applies: it must
    # still report a bare "(see QUESTIONS **B5**)".  Widening that vocabulary is
    # how the check silently stops checking anything.
    ("questions --self-test", ["questions_check.py", "--self-test"], True),
    # a note, not an exact check: staleness is the normal state while work is in
    # flight.  It is listed so it cannot go unnoticed -- `Pure.olean` was 46 minutes
    # stale on 2026-08-29 and the whole ProcPure section was invisible to every
    # compile in the tree, with nothing anywhere reporting it.
    ("olean_staleness",   ["refresh_oleans.py"],         False),
    # status fields that match more than one verdict, so which one they report is
    # decided by VERDICTS' table order rather than by the row.  A note: many are
    # honest append-only histories.  The point is that nothing distinguished those
    # from the ones the ordering gets backwards.
    ("verdict_conflicts", ["sorry_map.py", "--conflicts"], False),
]


def main():
    full = "--full" in sys.argv
    width = max(len(c[0]) for c in CHECKS)
    failed = []
    for entry in CHECKS:
        label, argv, exact = entry[0], entry[1], entry[2]
        pick = entry[3] if len(entry) > 3 else None
        r = subprocess.run([sys.executable, str(HERE / argv[0])] + argv[1:],
                           cwd=LEAN, capture_output=True, text=True)
        tail = [l for l in r.stdout.strip().splitlines() if l.strip()]
        if pick:
            hit = [l for l in tail if pick in l]
            summary = hit[-1].strip() if hit else (tail[-1] if tail else "(no output)")
        else:
            summary = tail[-1] if tail else "(no output)"
        bad = exact and r.returncode != 0
        mark = "FAIL" if bad else ("note" if r.returncode else " ok ")
        print(f"[{mark}] {label:<{width}}  {summary}")
        if full and len(tail) > 1:
            for l in tail[:-1]:
                print(f"         {l}")
        if bad:
            failed.append(label)
    print()
    if failed:
        print("FAILING: " + ", ".join(failed))
    else:
        print("every exact check is clean; `note` lines are shortlists, not failures")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
