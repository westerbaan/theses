import Papers.EJA.PureRoot
import Papers.EJA.Dagger

/-!
# EJA 40, unconditionally

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex` (Theorem 40,
main.tex:916).

`Dagger.lean` proves EJA 40 from the hypothesis `PureRootHyp` (a
⋄-self-adjoint root of a pure map may be taken pure; equivalently, via
`eja34Literal_of_pureRoot`, EJA 34 for ⋄-positivity read literally).
`PureRoot.lean` proves the stronger statement that such a root *is* pure
(`diaSA_root_isPure`).  This file joins the two: `pureRootHyp` discharges the
hypothesis, and `eja40_unconditional` is EJA 40 with no hypothesis.
-/

universe u

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra CategoryTheory Opposite

set_option warn.classDefReducibility false

attribute [local instance] ejapsuHasFiniteCoproducts ejapsuPCM ejapsuFinPAC
  ejapsuEffectusPartialForm ejapsu_diamondEffectus

/-- The hypothesis of `eja40_of_pureRoot`, proved: take the root itself, which
is pure by `diaSA_root_isPure`. -/
theorem pureRootHyp : PureRootHyp.{u} := fun _E f hf hff =>
  ⟨f, diaSA_root_isPure f (f ≫ f) hff rfl hf, hf, rfl⟩

/-- EJA 34 for ⋄-positivity read literally (Def 32, the root not assumed
pure), in the form `eja40` takes it. -/
theorem eja34Literal : Eja34Literal.{u} := eja34Literal_of_pureRoot pureRootHyp

/-- **EJA 40** (main.tex:916, Theorem), unconditionally: `EJA_psuᵒᵖ` is an
`&`-effectus with `asrt_p = Q_{√p}`, a †′-effectus, and a †-effectus (as
defined in thesis B §215).  This is `eja40` with its hypothesis `Eja34Literal`
discharged by `eja34Literal` (via `diaSA_root_isPure`, `PureRoot.lean`). -/
theorem eja40_unconditional :
    letI := ejapsu_andThenEffectus eja34Literal.{u}
    (∀ {X : EJAPsu.{u}ᵒᵖ} (p : Pred X) (x : X.unop.carrier),
      (asrt p).unop.toLinearMap x = ejaU (ejaSqrt (ejapsuVal p)) x) ∧
    DaggerPrimeEffectus (EJAPsu.{u}ᵒᵖ) ∧ Nonempty (DaggerEffectus (EJAPsu.{u}ᵒᵖ)) :=
  eja40 eja34Literal

end Papers.EJA
