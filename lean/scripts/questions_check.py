#!/usr/bin/env python3
"""Check that every reference to `QUESTIONS.md` names a question that is there.

`QUESTIONS.md` says of itself: "**Everything in this file is open.**  Once a
question is answered *and* the answer is implemented, its section is **deleted**
rather than marked resolved".  So a reference to a question is a reference to
something that can vanish, and the tree, the audit rows and the other documents
all cite them by key -- `QUESTIONS.md B5`, `QUESTIONS B10`, `question A12`.

Nothing checked those.  A pointer to a deleted question is worse than a broken
link: it tells the next reader that a decision is pending when it has been
taken, which is exactly the mistake `docs/DECISIONS.md` §4 exists to undo.

The keys the preamble records as deleted are listed here so a hit can say
whether the question was answered or never existed.  Keep the list in step with
the file; it is prose there and cannot be parsed reliably -- and note that it is
already **incomplete**: `D6`, `B11`, `D1`, `D5`, `A6`, `A7`, `D4`, `A5` and `B1`
are cited across the tree and are in neither the file nor the list.

**Historical documents are counted apart, not reported.**  `PROVING-LOG.md` and
the `*-survey.md` files are dated records of what was true when they were
written, and a question that was open then is correctly cited there; 84 of the
first run's 163 hits were `PROVING-LOG.md` alone.  What is a defect is a live
pointer -- in a doc comment, an audit row, `ERRATA.md`, or a current document --
telling the next reader that a decision is pending when it has been taken.
"""

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve()
ROOT = HERE.parents[2]
LEAN = HERE.parents[1]

SECTION = re.compile(r'^#{2,4}\s+([A-Z]\d{1,2})\.')
# "QUESTIONS.md B5", "QUESTIONS B10", "QUESTIONS.md, A12", "question A12"
CITE = re.compile(r'(?:QUESTIONS(?:\.md)?|question)\b[^A-Za-z0-9\n]{0,12}([A-Z]\d{1,2})\b')

# recorded in QUESTIONS.md's own preamble as deleted once answered
DELETED = {
    "B2": "2026-08-16", "B4": "2026-08-16", "B5": "2026-08-16", "B6": "2026-08-16",
    "B7": "2026-08-16", "B9": "2026-08-16", "D2": "2026-08-16", "D3": "2026-08-16",
    "A4": "2026-08-21", "A3": "2026-08-26",
    # traced through the removal commits on 2026-08-29 and added to the file's
    # own preamble at the same time; the ruling is in each commit's message
    "B1": "2026-08-16 (227ce6e)", "A6": "2026-08-16 (ffd073b)",
    "B11": "2026-08-16 (ffd073b)", "D1": "2026-08-16 (43e270f)",
    "D4": "2026-08-16 (3aa13e7)", "D5": "2026-08-16 (3aa13e7)",
    "A5": "2026-08-17 (3b4ba57)", "D6": "2026-08-18 (abc3af3)",
    "A7": "2026-08-19 (5f19f62)",
}


def sections():
    return {m.group(1) for m in
            (SECTION.match(l) for l in (LEAN / "QUESTIONS.md").read_text().splitlines()) if m}


def main():
    have = sections()
    targets = sorted(list(LEAN.rglob("Theses/**/*.lean"))
                     + list((LEAN / "docs" / "audit").glob("*.csv"))
                     + list((LEAN / "docs").glob("*.md"))
                     + [LEAN / "ERRATA.md", LEAN / "PROVING-LOG.md"])
    historical = lambda p: p.name == "PROVING-LOG.md" or p.name.endswith("-survey.md")
    dead, ok, logged = [], 0, 0
    for path in targets:
        if ".lake" in path.parts or path.name == "QUESTIONS.md":
            continue
        rel = path.relative_to(ROOT)
        for i, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
            for m in CITE.finditer(line):
                key = m.group(1)
                if key in have:
                    ok += 1
                    continue
                if historical(path):
                    logged += 1
                    continue
                if (rel, i, key) not in [(a, b, c) for a, b, c, _ in dead]:
                    dead.append((rel, i, key, DELETED.get(key)))

    for rel, i, key, when in dead:
        why = (f"deleted {when} as answered" if when else "no such question, and the preamble "
               f"does not record it as deleted")
        print(f"GONE     {rel}:{i}  cites QUESTIONS.md {key} -- {why}")
    print(f"\n{len(have)} questions open; {ok} references resolve, {len(dead)} live pointers "
          f"name a question that is not there, {logged} more are in the historical logs and are "
          f"not defects")
    return 1 if dead else 0


if __name__ == "__main__":
    sys.exit(main())
