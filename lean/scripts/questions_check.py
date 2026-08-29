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
the file; it is prose there and cannot be parsed reliably.  It once warned that
`D6`, `B11`, `D1`, `D5`, `A6`, `A7`, `D4`, `A5` and `B1` were cited across the
tree while being in neither the file nor the list -- all nine were traced to
their removal commits on 2026-08-29 and are in `DELETED` below, so the warning
is retired.  The list is complete as of then; the next deletion has to be added
by hand.

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
# The marker vocabulary is taken from what the tree actually writes, not guessed.
# Collecting it on 2026-08-29 across the then-31 hits showed the rows overwhelmingly
# DO record the answer -- "B6 is no longer an open question: Bas answered it on
# 2026-08-15", "deleted from QUESTIONS.md the same day at 43e270f", "B4 is no longer
# there, and its finding was ...", "(QUESTIONS D6, now closed)".  A first, narrower
# pass matched almost none of these and left the checker still crying wolf.
SELF_DESCRIBING = re.compile(
    # the question is gone, and the text says so
    r"was deleted|is deleted|now deleted|deleted as answered|deleted from QUESTIONS"
    r"|no longer exists|no longer there|no longer an open question|no longer open"
    r"|now closed|closed as answered|Moved here from|moved out of"
    # "deleted 2026-08-19 in 5f19f62" -- the form a repaired pointer takes once it
    # names when the question went and where the answer landed
    r"|deleted\s+(?:on\s+)?\d{4}-\d{2}-\d{2}"
    # the question was answered, and the text carries the answer
    r"|answered (?:it|on|by|and)|was answered|is answered|ANSWERED"
    r"|is settled|settled by|settled,|not pending|the ruling that closed"
    # a struck-through follow-up item is a completed one
    r"|~~"
    # past-tense narration of a repair a now-deleted question drove
    r"|already had|in session \d+",
    re.IGNORECASE)
WINDOW = 400


CONTEXT_LINES = 4


def self_describing(lines, i, key, hits):
    """True when the prose near ANY mention of `key` narrates its deletion or past.

    Scanning per-occurrence rather than per-line matters both ways.  An audit row is
    one very long line covering one declaration, so a marker anywhere in it should
    not exempt an unrelated key elsewhere in the same row -- hence the window.  But a
    row may also mention the same key twice, recording the deletion at only one of
    them; exempting one mention and flagging the other is noise, so a marker near any
    occurrence of the key clears them all.

    The window spans neighbouring LINES, not just the citing one.  Audit rows are a
    single long line, but a Lean doc comment is hard-wrapped, and there the sentence
    that records the answer routinely sits three or four lines below the key -- which
    is exactly how `SelfDual.lean`'s B5 paragraph read on 2026-08-29, answering the
    question in the same breath as naming it and still being reported.
    """
    lo = max(0, i - CONTEXT_LINES)
    before = "\n".join(lines[lo:i])
    ctx = "\n".join(lines[lo:i + CONTEXT_LINES + 1])
    base = len(before) + (1 if before else 0)
    for h in hits:
        a, b = base + h.start(), base + h.end()
        if SELF_DESCRIBING.search(ctx[max(0, a - WINDOW):min(len(ctx), b + WINDOW)]):
            return True
    return False


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
        lines = path.read_text(errors="replace").splitlines()
        for i, line in enumerate(lines, 1):
            by_key = {}
            for m in CITE.finditer(line):
                by_key.setdefault(m.group(1), []).append(m)
            for m in CITE.finditer(line):
                key = m.group(1)
                if key in have:
                    ok += 1
                    continue
                if historical(path):
                    logged += 1
                    continue
                if self_describing(lines, i - 1, key, by_key[key]):
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


def self_test():
    """The exemption is a heuristic, so guard the thing it must never swallow.

    A bare "(see QUESTIONS **B5**)" -- a live forward-pointer to a deleted question,
    with nothing around it saying the question is gone -- is the whole reason this
    checker exists.  Widening the marker vocabulary on 2026-08-29 took the report
    from 31 hits to 2, and a widening that goes one step further stops catching
    anything at all without ever failing loudly.  This makes it fail loudly.
    """
    target = LEAN / "docs" / "STATEMENT-AUDIT.md"
    orig = target.read_text()
    probe = "\n\nSelf-test probe, removed immediately (see QUESTIONS **B5**).\n"
    try:
        target.write_text(orig + probe)
        have = sections()
        lines = (orig + probe).splitlines()
        i = next(j for j, l in enumerate(lines) if "Self-test probe" in l)
        by_key = {}
        for m in CITE.finditer(lines[i]):
            by_key.setdefault(m.group(1), []).append(m)
        caught = "B5" not in have and not self_describing(lines, i, "B5", by_key["B5"])
    finally:
        target.write_text(orig)
    assert target.read_text() == orig, "self-test failed to restore STATEMENT-AUDIT.md"
    if not caught:
        print("SELF-TEST FAILED: a bare '(see QUESTIONS **B5**)' is no longer reported; "
              "the SELF_DESCRIBING vocabulary has been widened too far")
        return 1
    print("self-test passed: a bare forward-pointer to a deleted question is still reported")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main())
