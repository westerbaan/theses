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

**Self-describing citations are not defects either.**  That last sentence is the
actual test, and applying it on 2026-08-29 showed the checker was over-reporting.
A current document may name a deleted question precisely *in order to say it was
deleted* -- `ERRATA.md` rows carrying "*(Moved here from `QUESTIONS.md` A3 on
2026-08-26, when A3 was deleted as answered.)*", `docs/DECISIONS.md`'s
"`QUESTIONS.md` A7 was deleted, and 2a, 3, ...", a struck-through follow-up item
reading "~~**Delete `QUESTIONS.md` A3**~~", `docs/STATEMENT-AUDIT.md`'s "QUESTIONS
**B6** already had repaired for 192III.1/.2 in session 10".  None of these sends
the reader anywhere; each tells them the decision is *taken*, which is what the
checker wants.  Flagging them trains the reader to ignore the output.

So a citation is exempt when its own sentence narrates the deletion, the move or
the past session.  The test is deliberately narrow -- a marker within 200
characters of the key -- because the failure it must keep catching is a bare
"(see QUESTIONS **A7**)", which has no such marker.  Two of those were live in
`ERRATA.md` when this exemption was written and were repaired rather than
exempted, by naming where the answer went.
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


# A citation is self-describing -- and so not a defect -- when the text around it
# says the question is gone or narrates a finished action, rather than sending the
# reader to it.  Kept narrow on purpose: a bare "(see QUESTIONS **A7**)" matches
# none of these and is still reported.
SELF_DESCRIBING = re.compile(
    r"was deleted|deleted as answered|is deleted|now deleted|Moved here from"
    r"|moved out of|answered and (?:deleted|removed)|closed as answered"
    # "deleted 2026-08-19 in 5f19f62", "deleted 2026-08-16 as answered" -- the form
    # a repaired pointer takes once it names when the question went and where the
    # answer landed, which is the shape we want repairs to converge on
    r"|deleted\s+\d{4}-\d{2}-\d{2}"
    r"|~~|already had|in session \d+",
    re.IGNORECASE)
WINDOW = 200


def self_describing(line, m):
    """True when the prose around citation `m` narrates its deletion or its past."""
    return bool(SELF_DESCRIBING.search(
        line[max(0, m.start() - WINDOW):min(len(line), m.end() + WINDOW)]))


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
    dead, ok, logged, narrated = [], 0, 0, 0
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
                if self_describing(line, m):
                    narrated += 1
                    continue
                if (rel, i, key) not in [(a, b, c) for a, b, c, _ in dead]:
                    dead.append((rel, i, key, DELETED.get(key)))

    for rel, i, key, when in dead:
        why = (f"deleted {when} as answered" if when else "no such question, and the preamble "
               f"does not record it as deleted")
        print(f"GONE     {rel}:{i}  cites QUESTIONS.md {key} -- {why}")
    print(f"\n{len(have)} questions open; {ok} references resolve, {len(dead)} live pointers "
          f"name a question that is not there, {logged} more are in the historical logs and "
          f"{narrated} narrate their own deletion -- neither is a defect")
    return 1 if dead else 0


if __name__ == "__main__":
    sys.exit(main())
