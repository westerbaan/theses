#!/usr/bin/env python3
"""Check the 158V counterexample of `B/Dils/Kaplansky.lean`, in exact arithmetic.

Three `sorry`s in that file are `sorry` because **158V is false as printed**, and
the whole of the evidence is a computation carried out on paper.  There were four
until 2026-08-29, when this script's own output overturned one of them: it prints
`omega_0(A_2) = 0`, and `Kaplansky.lean` read that as one functional failing to
see `A_2`.  It is not that -- `A_2` is true, and `kaplansky_hilbmod_A_2` is now
proved.  What the four values actually show is an asymmetry: the estimates whose
*varying* resolvent multiplies the small vector (`A_1`, `A_1'`, `A_2'`) fail, and
the one whose varying resolvent multiplies the bounded vector (`A_2`) does not.
The checks below are unchanged; only their reading is.  Everything in
it lives in the span of `e₁, e₂, eₙ`, so it is a 3×3 matrix computation and can
be reproduced exactly over ℚ.  This does that.

The witness (`Kaplansky.lean`, the ⚠ block): `ℬ = B(ℓ²)`, `X = ℬ` over itself
with the tree's **mirrored** inner product `⟨a,b⟩ = b a*`, and

    y₀ = |e₁⟩⟨e₂|,   yₙ = |e₁ + eₙ⟩⟨e₂|   (n ≥ 2),   ω₀ = ⟨e₁, · e₁⟩.

All six recorded values reproduce, `omega_0(A_2) = 0` among them -- and that
zero is the true value of a convergent term, not a blind spot.  Two of them only reproduce once the *side*
of the module action is read the way the mirrored inner product forces, which is
not the side the prose writes them on — see the two `CONVENTION` notes below.
That is why this is a script and not a sentence.

This is not a Lean proof.  It is an exact-arithmetic check of the paper
argument, and `docs/DECISIONS.md` §1.3 still records the falsity as
disproved-on-paper.
"""

from fractions import Fraction as F

N = 3                                   # basis e₁, e₂, eₙ

I = [[F(int(i == j)) for j in range(N)] for i in range(N)]


def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(N)) for j in range(N)] for i in range(N)]


def add(A, B):
    return [[A[i][j] + B[i][j] for j in range(N)] for i in range(N)]


def sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(N)] for i in range(N)]


def smul(c, A):
    return [[c * A[i][j] for j in range(N)] for i in range(N)]


def star(A):                            # real entries throughout
    return [[A[j][i] for j in range(N)] for i in range(N)]


def kb(u, v):                           # |u⟩⟨v|
    return [[F(u[i]) * F(v[j]) for j in range(N)] for i in range(N)]


def inv(A):
    M = [row[:] + I[i][:] for i, row in enumerate(A)]
    for c in range(N):
        piv = next(r for r in range(c, N) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(N):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [row[N:] for row in M]


e1, e2, en, w = [1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 0, 1]
y0, yn = kb(e1, e2), kb(w, e2)

inner = lambda a, b: mul(b, star(a))    # the tree's mirrored ⟨a,b⟩ = b a*
inv1p = lambda b: inv(add(I, b))
w0 = lambda A: A[0][0]                  # ω₀ = ⟨e₁, · e₁⟩

P, Q = inner(y0, y0), inner(yn, yn)

CHECKS = []


def check(name, got, want):
    CHECKS.append((name, got, want, got == want))


check("⟨yₙ−y₀, yₙ−y₀⟩ = pₙ", inner(sub(yn, y0), sub(yn, y0)), kb(en, en))

A1 = sub(mul(mul(P, inv1p(P)), inv1p(P)), mul(inv1p(Q), mul(P, inv1p(P))))
A1p = sub(mul(mul(Q, inv1p(Q)), inv1p(Q)), mul(inv1p(P), mul(Q, inv1p(Q))))
A2 = mul(mul(inv1p(P), inner(yn, sub(yn, y0))), inv1p(Q))
A2p = mul(mul(inv1p(Q), inner(y0, sub(y0, yn))), inv1p(P))

check("ω₀(A₁) = −1/12", w0(A1), F(-1, 12))
check("ω₀(A₁') = −1/18", w0(A1p), F(-1, 18))
check("ω₀(A₂) = 0", w0(A2), F(0))
check("ω₀(A₂') = 1/6", w0(A2p), F(1, 6))

# CONVENTION 1.  The ⚠ block writes `h y = y·2/(1+⟨y,y⟩)`, the scalar on the
# right.  With ⟨a,b⟩ = b a* the module action is on the LEFT, and the scalar on
# the right gives ω₀ = 0 rather than 1/9.
h = lambda y: smul(F(2), mul(inv1p(inner(y, y)), y))
d = sub(h(y0), h(yn))
check("ω₀(⟨hy₀−hyₙ, hy₀−hyₙ⟩) = 1/9", w0(inner(d, d)), F(1, 9))
check("…and it is 4(A₁+A₁'+A₂+A₂')", 4 * w0(add(add(A1, A1p), add(A2, A2p))), F(1, 9))

# CONVENTION 2.  The ⚠ block quotes `kaplanskytodo2`'s failing half as
# `⟨y₀, yₙ−y₀⟩(1+⟨yₙ,yₙ⟩)⁻¹`, in the *thesis's* argument order.  Read in the
# tree's mirrored order that expression has ω₀ = 0; the −1/3 belongs to the
# other order, which is what the thesis's ⟨y₀, yₙ−y₀⟩ mirrors to.
todo2 = mul(inner(sub(yn, y0), y0), inv1p(Q))
check("kaplanskytodo2's half = |e₁⟩⟨eₙ| − ⅓|e₁⟩⟨w|",
      todo2, sub(kb(e1, en), smul(F(1, 3), kb(e1, w))))
check("…with ω₀ = −1/3", w0(todo2), F(-1, 3))

if __name__ == "__main__":
    bad = 0
    for name, got, want, ok in CHECKS:
        g = got if isinstance(got, F) else "…"
        print(f"{'ok  ' if ok else 'FAIL'}  {name}" + (f"   (got {g})" if not ok else ""))
        bad += not ok
    print(f"\n{len(CHECKS) - bad} of {len(CHECKS)} recorded values reproduce exactly")
    raise SystemExit(1 if bad else 0)
