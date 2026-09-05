/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 1–1713.

  §Definition and Examples  (parsecs 20–60: C*-algebras, Hilbert spaces,
                             bounded operators, B(H))
  §The Basics               (parsecs 70–110: self-adjoint elements, positive
                             elements, morphisms, invertibles, spectrum,
                             spectral permanence)

All statements of parsecs 20–110 are proved.  See CONVENTIONS.md for the
numbering (**4V** = parsec 40, point 50) and naming conventions.
-/
import Theses.Common

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule

namespace Theses.A.CStar

/-! ## Parsec 30: Definition and first examples

**3I** (cstar.tex:84, Definition): a *C*-algebra* is a complex vector space
with an associative bilinear multiplication, a unit, an involution `(·)*`,
and a complete submultiplicative norm satisfying the C*-identity
`‖a* a‖ = ‖a‖²`.  In Mathlib this (unital, as everywhere in the thesis)
notion is the class `CStarAlgebra A`; a *commutative* C*-algebra (**3I**,
last clause) is `CommCStarAlgebra A`.

**3III** (cstar.tex:135, Example): ℂ is a commutative C*-algebra —
Mathlib instance below.

**3IV** (cstar.tex:145, Example): a *C*-subalgebra* — a norm-closed
unital ∗-subalgebra — is in Mathlib a `StarSubalgebra ℂ A` that is
`IsClosed` as a set (each such is again a C*-algebra).

**3V** (`cstar-product`, cstar.tex:159, Example): the direct sum
`⊕ᵢ 𝒜ᵢ = {a ∈ Π 𝒜ᵢ | supᵢ ‖a i‖ < ∞}` with coordinatewise operations and
supremum norm is a C*-algebra; in Mathlib this is `lp (fun i => 𝒜 i) ∞`
(with its `CStarRing` instance).  In particular `ℓ∞(X)`, the bounded
functions on a set `X`, is `lp (fun _ : X => ℂ) ∞`.

**3VI** (cstar.tex:195, Example): the bounded continuous functions
`BC(X)` on a topological space (`BoundedContinuousFunction X ℂ`) and the
continuous functions `C(X)` on a compact Hausdorff space (`C(X, ℂ)`) are
commutative C*-algebras — Mathlib instances.

**3VII** (`cstar-matrices-example`, cstar.tex:214, Example): the n×n
complex matrices with conjugate-transpose involution and operator norm
form a C*-algebra; in Mathlib the matrix type carrying this C*-norm is
`CStarMatrix (Fin n) (Fin n) ℂ`.

**3VIII** (cstar.tex:255, Remark): `⊕ₖ M_{n_k}` is a finite-dimensional
C*-algebra, and every finite-dimensional C*-algebra is of this form
(proved at 84II, vn.tex).
-/

/-- **3III** (cstar.tex:135, Example): ℂ is a *commutative* C*-algebra
(with conjugation as involution and modulus as norm). -/
noncomputable example : CommCStarAlgebra ℂ := inferInstance

/-- **3VII** (`cstar-matrices-example`, cstar.tex:214, Example), the point of
the Example: for `n > 1` the C*-algebra `M_n = CStarMatrix (Fin n) (Fin n) ℂ`
is **non-commutative** — it is the thesis's first example of one, and that is
the whole reason the Example is there.

The C*-structure itself is Mathlib's, and is recorded by the
general-coefficient `example` at 33I.4 in `A/CStar/Matrices.lean`;
what is asserted here is only the failure of commutativity, exhibited on the
matrix units `e₀₁` and `e₁₀`, whose products `e₀₁e₁₀ = e₀₀` and
`e₁₀e₀₁ = e₁₁` differ in the `(0,0)` entry.  `n > 1` is what makes the two
indices available, and it is necessary: `M_1 ≅ ℂ` is commutative.

*Definition/Example, so the thesis gives no proof.* -/
theorem cstar_matrices_noncommutative {n : ℕ} (hn : 1 < n) :
    ∃ A B : CStarMatrix (Fin n) (Fin n) ℂ, A * B ≠ B * A := by
  classical
  set i : Fin n := ⟨0, by omega⟩ with hi
  set j : Fin n := ⟨1, hn⟩ with hj
  have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
  refine ⟨CStarMatrix.ofMatrix (Matrix.single i j 1),
    CStarMatrix.ofMatrix (Matrix.single j i 1), fun h => ?_⟩
  have hmul : ∀ a b : Matrix (Fin n) (Fin n) ℂ,
      CStarMatrix.ofMatrix a * CStarMatrix.ofMatrix b = CStarMatrix.ofMatrix (a * b) :=
    fun _ _ => rfl
  rw [hmul, hmul] at h
  have h' : Matrix.single i j (1 : ℂ) * Matrix.single j i 1
      = Matrix.single j i (1 : ℂ) * Matrix.single i j 1 :=
    CStarMatrix.ofMatrix.injective h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one] at h'
  have hentry := congrFun (congrFun h' i) i
  rw [Matrix.single_apply_same, Matrix.single_apply_of_row_ne (Ne.symm hij)] at hentry
  exact one_ne_zero hentry

/-! ## Parsec 40 (`hilb`): Hilbert spaces and bounded operators -/

section Operators

variable {𝒳 𝒴 𝒵 : Type*}
  [NormedAddCommGroup 𝒳] [NormedSpace ℂ 𝒳]
  [NormedAddCommGroup 𝒴] [NormedSpace ℂ 𝒴]
  [NormedAddCommGroup 𝒵] [NormedSpace ℂ 𝒵]

/-! **4I** (`example-hilb`, cstar.tex:279, Example): the bounded operators
`B(H)` on a Hilbert space form a C*-algebra (composition, adjoint, identity,
operator norm) — in Mathlib, `H →L[ℂ] H` with `ContinuousLinearMap.adjoint`
as star.  A *concrete C*-algebra* is a closed `StarSubalgebra` of it.

**4II** (`bounded-linear-maps`, cstar.tex:300, Definition): bound, bounded
operator, operator norm `‖T‖`, and the space `B(𝒳,𝒴)` of bounded operators —
in Mathlib `𝒳 →L[ℂ] 𝒴` with its operator norm. -/

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 1:
the operator norm on `B(𝒳,𝒴)` is, indeed, a norm: it is nonnegative,
definite, absolutely homogeneous, and satisfies the triangle inequality.
(All four are packaged in Mathlib by the `NormedAddCommGroup (𝒳 →L[ℂ] 𝒴)`
instance; we spell them out, as the exercise asks.) -/
theorem boundedOperators_basic_1 (T T' : 𝒳 →L[ℂ] 𝒴) (c : ℂ) :
    0 ≤ ‖T‖ ∧ (‖T‖ = 0 ↔ T = 0) ∧ ‖c • T‖ = ‖c‖ * ‖T‖ ∧
      ‖T + T'‖ ≤ ‖T‖ + ‖T'‖ := by
  -- the solution's three observations, each run through "‖·‖ is the *least* bound"
  have hsmul : ∀ (d : ℂ) (S : 𝒳 →L[ℂ] 𝒴), ‖d • S‖ ≤ ‖d‖ * ‖S‖ := by
    intro d S
    refine (d • S).opNorm_le_bound (by positivity) fun x => ?_
    show ‖d • S x‖ ≤ ‖d‖ * ‖S‖ * ‖x‖
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (S.le_opNorm x) (norm_nonneg d)
  refine ⟨norm_nonneg T, ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · -- `‖T‖ = 0` makes `0` a bound, so `‖T x‖ ≤ 0`, so `T x = 0` for every `x`
    ext x
    have hx : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    rw [h, zero_mul] at hx
    simpa using le_antisymm hx (norm_nonneg _)
  · subst h
    refine le_antisymm ((0 : 𝒳 →L[ℂ] 𝒴).opNorm_le_bound le_rfl fun x => by simp) (norm_nonneg _)
  · -- `r ↦ |c| r` carries bounds of `T` to bounds of `c • T`, and `r ↦ |c|⁻¹ r` back
    refine le_antisymm (hsmul c T) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have h := hsmul c⁻¹ (c • T)
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
      have h2 := mul_le_mul_of_nonneg_left h (norm_nonneg c)
      rwa [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul] at h2
  · -- `‖T‖ + ‖T'‖` is a bound for `T + T'`, and `‖T + T'‖` is the least one
    refine (T + T').opNorm_le_bound (by positivity) fun x => ?_
    calc ‖(T + T') x‖ ≤ ‖T x‖ + ‖T' x‖ := norm_add_le _ _
      _ ≤ ‖T‖ * ‖x‖ + ‖T'‖ * ‖x‖ := add_le_add (T.le_opNorm x) (T'.le_opNorm x)
      _ = (‖T‖ + ‖T'‖) * ‖x‖ := by ring

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 2:
`‖S ∘ T‖ ≤ ‖S‖ ‖T‖` for bounded operators `T : 𝒳 → 𝒴`, `S : 𝒴 → 𝒵`. -/
theorem boundedOperators_basic_2 (S : 𝒴 →L[ℂ] 𝒵) (T : 𝒳 →L[ℂ] 𝒴) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := by
  -- the solution's estimate: `‖STx‖ ≤ ‖S‖ ‖Tx‖ ≤ ‖S‖ ‖T‖ ‖x‖`, so `‖S‖ ‖T‖` is a bound
  refine (S.comp T).opNorm_le_bound (by positivity) fun x => ?_
  calc ‖(S.comp T) x‖ ≤ ‖S‖ * ‖T x‖ := S.le_opNorm (T x)
    _ ≤ ‖S‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg S)
    _ = ‖S‖ * ‖T‖ * ‖x‖ := by ring

/-- **4III** (`bounded-operators-basic`, cstar.tex:326, Exercise), part 3:
the identity operator is bounded by 1. -/
theorem boundedOperators_basic_3 : ‖(ContinuousLinearMap.id ℂ 𝒳)‖ ≤ 1 :=
  -- the solution's line: `‖id x‖ ≡ ‖x‖ ≤ 1·‖x‖`, so `1` is a bound
  (ContinuousLinearMap.id ℂ 𝒳).opNorm_le_bound zero_le_one fun x => by simp

/-- **4IV** (`operator-norm-ball`, cstar.tex:343, Exercise):
`r ‖T‖ = sup { ‖T x‖ : ‖x‖ ≤ r }` for a bounded operator `T` and
`r ∈ [0,∞)`. -/
theorem operatorNorm_ball (T : 𝒳 →L[ℂ] 𝒴) (r : ℝ) (hr : 0 ≤ r) :
    r * ‖T‖ = ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
  by
    have hzero : ‖(0 : 𝒳)‖ ≤ r := by simpa using hr
    have hne : Nonempty {x : 𝒳 // ‖x‖ ≤ r} := ⟨⟨0, hzero⟩⟩
    have hle : ∀ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ ≤ r * ‖T‖ := by
      intro x
      calc ‖T x‖ ≤ ‖T‖ * ‖(x : 𝒳)‖ := T.le_opNorm _
        _ ≤ ‖T‖ * r := mul_le_mul_of_nonneg_left x.2 (norm_nonneg T)
        _ = r * ‖T‖ := mul_comm _ _
    have hbdd : BddAbove (Set.range fun x : {x : 𝒳 // ‖x‖ ≤ r} => ‖T x‖) := by
      refine ⟨r * ‖T‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle x
    refine le_antisymm ?_ (ciSup_le hle)
    -- `0 ≤ ⨆`, witnessed by `x = 0`
    have hS0 : (0 : ℝ) ≤ ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
      le_ciSup_of_le hbdd ⟨0, hzero⟩ (by simp)
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · have hz : r * ‖T‖ = 0 := by rw [← hr0]; ring
      rw [hz]; exact hS0
    -- For `0 < r`, bound `‖T‖` by `(⨆)/r` by rescaling `x` to norm exactly `r`.
    have hTle : ‖T‖ ≤ (⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖) / r := by
      refine T.opNorm_le_bound (by positivity) fun x => ?_
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hy : ‖(r / ‖x‖ : ℝ) • x‖ ≤ r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            div_mul_cancel₀ _ (ne_of_gt hxn)]
        have hTy : ‖T ((r / ‖x‖ : ℝ) • x)‖ ≤ ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ :=
          le_ciSup_of_le hbdd ⟨(r / ‖x‖ : ℝ) • x, hy⟩ le_rfl
        rw [T.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)] at hTy
        rw [div_mul_eq_mul_div, le_div_iff₀ hr0]
        calc ‖T x‖ * r = (r / ‖x‖ * ‖T x‖) * ‖x‖ := by field_simp
          _ ≤ (⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖) * ‖x‖ :=
              mul_le_mul_of_nonneg_right hTy (norm_nonneg x)
    calc r * ‖T‖ ≤ r * ((⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖) / r) :=
          mul_le_mul_of_nonneg_left hTle hr
      _ = ⨆ x : {x : 𝒳 // ‖x‖ ≤ r}, ‖T x‖ := by field_simp

/-- **4V** (`operator-norm-complete`, cstar.tex:359, Lemma): the operator
norm on `B(𝒳,𝒴)` is complete when `𝒴` is complete.  (Mathlib has this as the
`ContinuousLinearMap.completeSpace` instance; the proof below is the Lemma's
own Cauchy-sequence argument, point **4VI**.) -/
theorem operatorNorm_complete [CompleteSpace 𝒴] : CompleteSpace (𝒳 →L[ℂ] 𝒴) := by
  -- the Lemma's own proof (point 4VI): a Cauchy sequence is pointwise Cauchy,
  -- the pointwise limit is linear, and the ε/2-estimate makes it bounded and
  -- the limit in the operator norm
  refine Metric.complete_of_cauchySeq_tendsto fun T hT => ?_
  -- `‖Tₙx - Tₘx‖ ≤ ‖Tₙ - Tₘ‖ ‖x‖`, so `(Tₙx)ₙ` is Cauchy, hence convergent
  have hpt : ∀ x : 𝒳, CauchySeq fun n => T n x := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
    · refine ⟨0, fun m _ n _ => ?_⟩
      have hx0 : x = 0 := by rw [← norm_eq_zero]; exact hx.symm
      simp [hx0, hε]
    · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hT (ε / ‖x‖) (by positivity)
      refine ⟨N, fun m hm n hn => ?_⟩
      have h := hN m hm n hn
      rw [dist_eq_norm] at h ⊢
      calc ‖T m x - T n x‖ = ‖(T m - T n) x‖ := rfl
        _ ≤ ‖T m - T n‖ * ‖x‖ := (T m - T n).le_opNorm x
        _ < ε / ‖x‖ * ‖x‖ := by exact mul_lt_mul_of_pos_right h hx
        _ = ε := by field_simp
  choose S hS using fun x => cauchySeq_tendsto_of_complete (hpt x)
  -- the pointwise limit is linear, by continuity of addition and scalar multiplication
  have hadd : ∀ x z : 𝒳, S (x + z) = S x + S z := by
    intro x z
    exact tendsto_nhds_unique (hS (x + z))
      (Filter.Tendsto.congr (fun n => (map_add (T n) x z).symm) ((hS x).add (hS z)))
  have hsmul : ∀ (c : ℂ) (x : 𝒳), S (c • x) = c • S x := by
    intro c x
    exact tendsto_nhds_unique (hS (c • x))
      (Filter.Tendsto.congr (fun n => ((T n).map_smul c x).symm) ((hS x).const_smul c))
  set L : 𝒳 →ₗ[ℂ] 𝒴 :=
    { toFun := S, map_add' := hadd, map_smul' := fun c x => hsmul c x } with hL
  -- the ε/2-estimate: for `n ≥ N`, `‖(S - Tₙ)x‖ ≤ ε‖x‖` for every `x`
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ∀ x : 𝒳, ‖S x - T n x‖ ≤ ε * ‖x‖ := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hT (ε / 2) (by positivity)
    refine ⟨N, fun n hn x => ?_⟩
    -- for each `x` pick `m ≥ N` with `‖Sx - Tₘx‖ ≤ (ε/2)‖x‖`
    have hgoal : ∀ δ : ℝ, 0 < δ → ‖S x - T n x‖ ≤ ε * ‖x‖ + δ := by
      intro δ hδ
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (hS x) δ hδ
      obtain ⟨m, hmN, hmM⟩ : ∃ m, N ≤ m ∧ M ≤ m := ⟨max N M, le_max_left _ _, le_max_right _ _⟩
      have h1 : ‖S x - T m x‖ < δ := by
        have := hM m hmM
        rwa [dist_eq_norm'] at this
      have h2 : ‖T m x - T n x‖ ≤ ε / 2 * ‖x‖ := by
        calc ‖T m x - T n x‖ = ‖(T m - T n) x‖ := rfl
          _ ≤ ‖T m - T n‖ * ‖x‖ := (T m - T n).le_opNorm x
          _ ≤ ε / 2 * ‖x‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
              have := hN m hmN n hn
              rw [dist_eq_norm] at this
              exact this.le
      calc ‖S x - T n x‖ ≤ ‖S x - T m x‖ + ‖T m x - T n x‖ := by
            simpa using norm_sub_le_norm_sub_add_norm_sub (S x) (T m x) (T n x)
        _ ≤ δ + ε / 2 * ‖x‖ := add_le_add h1.le h2
        _ ≤ ε * ‖x‖ + δ := by nlinarith [norm_nonneg x, hε.le]
    exact le_of_forall_pos_le_add fun δ hδ => hgoal δ hδ
  -- `S` is bounded, so it is a continuous linear map
  obtain ⟨N₀, hN₀⟩ := hkey 1 one_pos
  have hbound : ∀ x : 𝒳, ‖L x‖ ≤ (1 + ‖T N₀‖) * ‖x‖ := by
    intro x
    have h1 := hN₀ N₀ le_rfl x
    have h2 : ‖T N₀ x‖ ≤ ‖T N₀‖ * ‖x‖ := (T N₀).le_opNorm x
    calc ‖L x‖ = ‖S x‖ := rfl
      _ ≤ ‖S x - T N₀ x‖ + ‖T N₀ x‖ := by simpa using norm_le_norm_sub_add _ _
      _ ≤ 1 * ‖x‖ + ‖T N₀‖ * ‖x‖ := add_le_add h1 h2
      _ = (1 + ‖T N₀‖) * ‖x‖ := by ring
  refine ⟨L.mkContinuous (1 + ‖T N₀‖) hbound, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hkey (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hle : ‖T n - L.mkContinuous (1 + ‖T N₀‖) hbound‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have h := hN n hn x
    calc ‖(T n - L.mkContinuous (1 + ‖T N₀‖) hbound) x‖ = ‖S x - T n x‖ := by
          rw [← norm_neg]
          congr 1
          simp [L]
      _ ≤ ε / 2 * ‖x‖ := h
  linarith

/-! **4VII** (`bounded-operators-banach-algebra`, cstar.tex:401): `B(𝒳)` on a
complete normed vector space `𝒳` satisfies all requirements of a C*-algebra
not involving the involution, i.e. it is a *Banach algebra* — in Mathlib the
`NormedRing (𝒳 →L[ℂ] 𝒳)` and `CompleteSpace` instances. -/

end Operators

section PreHilbert

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! **4VIII** (`hilb-def`, cstar.tex:416, Definition): inner product,
definiteness, pre-Hilbert space, Hilbert space — in Mathlib
`[NormedAddCommGroup H] [InnerProductSpace ℂ H]` (the inner product is
definite by construction), with `[CompleteSpace H]` for Hilbert spaces.
The remaining notion, *adjointness* of a pair of operators between
pre-Hilbert spaces, is defined here (for bare functions, so that it applies
to unbounded operators as in **4XI** as well as to `→L[ℂ]` maps).

**4IX** (`hilb-basic-examples`, cstar.tex:461, Example): `ℂ^N`
(`EuclideanSpace ℂ (Fin N)`) is a Hilbert space; the finitely-supported
sequences `c₀₀` are a non-complete pre-Hilbert space; `ℓ²` is treated
in **6II**. -/

/-- **4VIII** (`hilb-def`, cstar.tex:416, Definition): `T : H → K` is
*adjoint to* `S : K → H` when `⟪T x, y⟫ = ⟪x, S y⟫` for all `x ∈ H`,
`y ∈ K`. -/
def IsAdjointTo (T : H → K) (S : K → H) : Prop :=
  ∀ (x : H) (y : K), ⟪T x, y⟫ = ⟪x, S y⟫

/-- **4VIII** (`hilb-def`, cstar.tex:416, Definition): an operator is
*adjointable* when it is adjoint to some operator. -/
def Adjointable (T : H → K) : Prop :=
  ∃ S : K → H, IsAdjointTo T S

/-- **4X** (`uniqueness-adjoint`, cstar.tex:496, Exercise), part 1: vectors
of a pre-Hilbert space with `⟪y, x⟫ = ⟪y, x'⟫` for all `y` are equal. -/
theorem uniqueness_adjoint_1 (x x' : H) (h : ∀ y : H, ⟪y, x⟫ = ⟪y, x'⟫) :
    x = x' := by
  -- the solution's `y := x - x'`: `‖y‖² = ⟪y,y⟫ = ⟪y,x⟫ - ⟪y,x'⟫ = 0`
  have hy : (⟪x - x', x - x'⟫ : ℂ) = 0 := by
    rw [inner_sub_right, h (x - x'), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hy)

/-- **4X** (`uniqueness-adjoint`, cstar.tex:496, Exercise), part 2: every
operator between pre-Hilbert spaces has at most one adjoint. -/
theorem uniqueness_adjoint_2 (T : H → K) (S S' : K → H)
    (hS : IsAdjointTo T S) (hS' : IsAdjointTo T S') : S = S' :=
  by
    funext y
    exact ext_inner_left ℂ fun x => by rw [← hS x y, hS' x y]

/-- **4XII** (cstar.tex:520, Exercise), part 1: if `T` is adjoint to `S`
then `S` is adjoint to `T` (so `T** = T`). -/
theorem isAdjointTo_symm (T : H → K) (S : K → H) (h : IsAdjointTo T S) :
    IsAdjointTo S T :=
  by
    intro y x
    simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) (h x y).symm

/-- **4XII** (cstar.tex:520, Exercise), part 2 (sums): `(T + T')* = T* + T'*`
for adjointable operators on a pre-Hilbert space. -/
theorem isAdjointTo_add (T T' : H → K) (S S' : K → H)
    (h : IsAdjointTo T S) (h' : IsAdjointTo T' S') :
    IsAdjointTo (T + T') (S + S') :=
  by
    intro x y
    simp [inner_add_left, inner_add_right, h x y, h' x y]

/-- **4XII** (cstar.tex:520, Exercise), part 2 (scalars):
`(λ T)* = conj λ · T*`. -/
theorem isAdjointTo_smul (T : H → K) (S : K → H) (z : ℂ)
    (h : IsAdjointTo T S) :
    IsAdjointTo (fun x => z • T x) (fun y => (starRingEnd ℂ) z • S y) :=
  by
    intro x y
    simp [inner_smul_left, inner_smul_right, h x y, mul_comm]

/-- **4XII** (cstar.tex:520, Exercise), part 3: `S ∘ T` is adjoint to
`T* ∘ S*`, i.e. `(ST)* = T* S*`. -/
theorem isAdjointTo_comp {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] (T : H → K) (T' : K → H) (S : K → L) (S' : L → K)
    (hT : IsAdjointTo T T') (hS : IsAdjointTo S S') :
    IsAdjointTo (S ∘ T) (T' ∘ S') :=
  by
    intro x z
    simp only [Function.comp_apply]
    rw [hS, hT]

/-- **4XIII** (`positive-2x2matrix`, cstar.tex:540, Lemma), part 1: if the
2×2 matrix `[[p, c̄], [c, q]]` is positive (i.e. `(ū v̄) A (u v)ᵀ ≥ 0` for
all `u, v ∈ ℂ`), then `p, q ≥ 0`. -/
theorem positive_2x2matrix_1 (p q c : ℂ)
    (h : ∀ u v : ℂ, 0 ≤ (starRingEnd ℂ) u * (p * u + (starRingEnd ℂ) c * v)
      + (starRingEnd ℂ) v * (c * u + q * v)) :
    0 ≤ p ∧ 0 ≤ q :=
  by
    exact ⟨by simpa using h 1 0, by simpa using h 0 1⟩

/-- **4XIII** (`positive-2x2matrix`, cstar.tex:540, Lemma), part 2: for a
positive 2×2 matrix `[[p, c̄], [c, q]]` we have `|c|² ≤ p q`. -/
theorem positive_2x2matrix_2 (p q c : ℂ)
    (h : ∀ u v : ℂ, 0 ≤ (starRingEnd ℂ) u * (p * u + (starRingEnd ℂ) c * v)
      + (starRingEnd ℂ) v * (c * u + q * v)) :
    ((‖c‖ : ℂ)) ^ 2 ≤ p * q :=
  by
    obtain ⟨hp0, hq0⟩ := positive_2x2matrix_1 p q c h
    have key : ∀ t : ℝ,
        (0 : ℂ) ≤ p * (‖c‖ : ℂ) ^ 2 * (t : ℂ) ^ 2 + 2 * (‖c‖ : ℂ) ^ 2 * (t : ℂ) + q := by
      intro t
      have H := h ((t : ℂ) * (starRingEnd ℂ) c) 1
      have e : (starRingEnd ℂ) ((t : ℂ) * (starRingEnd ℂ) c)
              * (p * ((t : ℂ) * (starRingEnd ℂ) c) + (starRingEnd ℂ) c * 1)
            + (starRingEnd ℂ) 1 * (c * ((t : ℂ) * (starRingEnd ℂ) c) + q * 1)
          = p * (‖c‖ : ℂ) ^ 2 * (t : ℂ) ^ 2 + 2 * (‖c‖ : ℂ) ^ 2 * (t : ℂ) + q := by
        simp only [map_mul, Complex.conj_conj, map_one, one_mul, mul_one,
          Complex.conj_ofReal]
        rw [← Complex.conj_mul' c]
        ring
      rwa [e] at H
    rw [Complex.nonneg_iff] at hp0 hq0
    obtain ⟨hpre, hpim⟩ := hp0
    obtain ⟨hqre, hqim⟩ := hq0
    have hp : p = (p.re : ℂ) := by apply Complex.ext <;> simp [← hpim]
    have hq : q = (q.re : ℂ) := by apply Complex.ext <;> simp [← hqim]
    have keyR : ∀ t : ℝ, 0 ≤ p.re * ‖c‖ ^ 2 * t ^ 2 + 2 * ‖c‖ ^ 2 * t + q.re := by
      intro t
      have H := key t
      rw [Complex.nonneg_iff] at H
      simpa [Complex.add_re, Complex.mul_re, ← Complex.ofReal_pow, ← hpim] using H.1
    have hK0 : (0 : ℝ) ≤ ‖c‖ ^ 2 := by positivity
    have main : ‖c‖ ^ 2 ≤ p.re * q.re := by
      rcases eq_or_lt_of_le hpre with hP | hP
      · have hKz : ‖c‖ ^ 2 = 0 := by
          by_contra hne
          have hKpos : 0 < ‖c‖ ^ 2 := lt_of_le_of_ne hK0 (Ne.symm hne)
          have hcne : ‖c‖ ≠ 0 := by
            intro h0
            rw [h0] at hKpos
            simp at hKpos
          have hx := keyR (-(q.re + 1) / (2 * ‖c‖ ^ 2))
          rw [← hP, zero_mul, zero_mul, zero_add] at hx
          rw [show 2 * ‖c‖ ^ 2 * (-(q.re + 1) / (2 * ‖c‖ ^ 2)) = -(q.re + 1) by
            field_simp] at hx
          linarith
        rw [hKz, ← hP]
        simp
      · have hne : p.re ≠ 0 := ne_of_gt hP
        have hx := keyR (-1 / p.re)
        field_simp at hx
        nlinarith [hx, hP, hK0]
    rw [hp, hq]
    exact_mod_cast main

/-! **4XV** (`inner-product-basic`, cstar.tex:590, Exercise): the formula
`‖x‖ = √⟪x,x⟫` defines a seminorm on a complex vector space `V` carrying an
inner product, and a norm when that inner product is definite; and it
satisfies the four listed identities.  The exercise is stated for an
arbitrary — in particular possibly *indefinite* — inner product, which in
Mathlib is a `PreInnerProductSpace.Core ℂ V` (`InnerProductSpace.Core` adds
definiteness, and `InnerProductSpace ℂ H` is the definite, normed case).  We
follow the exercise and work over a `PreInnerProductSpace.Core ℂ V`, writing
`innerNorm x` for the formula `√⟪x,x⟫`. -/

section IndefiniteInner

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [c : PreInnerProductSpace.Core ℂ V]

attribute [local instance] InnerProductSpace.Core.toPreInner'

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise): the formula
`‖x‖ = √⟪x,x⟫`, for a possibly indefinite inner product on a complex vector
space. -/
noncomputable def innerNorm (x : V) : ℝ := Real.sqrt (RCLike.re (⟪x, x⟫ : ℂ))

/-- `‖x‖² = ⟪x,x⟫`, the defining property of `innerNorm`. -/
theorem innerNorm_sq (x : V) : innerNorm x ^ 2 = RCLike.re (⟪x, x⟫ : ℂ) :=
  Real.sq_sqrt InnerProductSpace.Core.inner_self_nonneg

theorem innerNorm_nonneg (x : V) : 0 ≤ innerNorm x := Real.sqrt_nonneg _

theorem innerNorm_sq_coe (x : V) : ((innerNorm x : ℂ)) ^ 2 = ⟪x, x⟫ := by
  rw [← Complex.ofReal_pow, innerNorm_sq]
  exact InnerProductSpace.Core.inner_self_ofReal_re x

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 1: the
Cauchy–Schwarz inequality `|⟪x,y⟫|² ≤ ⟪x,x⟫ ⟪y,y⟫`. -/
theorem inner_product_basic_1 (x y : V) :
    ‖(⟪x, y⟫ : ℂ)‖ ^ 2 ≤ RCLike.re (⟪x, x⟫ : ℂ) * RCLike.re (⟪y, y⟫ : ℂ) := by
  -- the exercise's hint: apply **4XIII** to the positive matrix `[[⟪x,x⟫, ⟪x,y⟫], [⟪y,x⟫, ⟪y,y⟫]]`
  have hpos : ∀ u v : ℂ,
      0 ≤ (starRingEnd ℂ) u * ((⟪x, x⟫ : ℂ) * u + (starRingEnd ℂ) (⟪y, x⟫ : ℂ) * v)
        + (starRingEnd ℂ) v * ((⟪y, x⟫ : ℂ) * u + (⟪y, y⟫ : ℂ) * v) := by
    intro u v
    have hexp : (starRingEnd ℂ) u * ((⟪x, x⟫ : ℂ) * u + (starRingEnd ℂ) (⟪y, x⟫ : ℂ) * v)
        + (starRingEnd ℂ) v * ((⟪y, x⟫ : ℂ) * u + (⟪y, y⟫ : ℂ) * v)
        = (⟪u • x + v • y, u • x + v • y⟫ : ℂ) := by
      rw [InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ)]
      rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ),
        InnerProductSpace.Core.inner_conj_symm (𝕜 := ℂ) x y]
      ring
    have hre : (0 : ℝ) ≤ RCLike.re (⟪u • x + v • y, u • x + v • y⟫ : ℂ) :=
      InnerProductSpace.Core.inner_self_nonneg
    have heq := InnerProductSpace.Core.inner_self_ofReal_re (𝕜 := ℂ) (u • x + v • y)
    rw [hexp, ← heq]
    exact Complex.zero_le_real.mpr hre
  have hmain := positive_2x2matrix_2 (⟪x, x⟫ : ℂ) (⟪y, y⟫ : ℂ) (⟪y, x⟫ : ℂ) hpos
  have hp : ((RCLike.re (⟪x, x⟫ : ℂ) : ℝ) : ℂ) = (⟪x, x⟫ : ℂ) :=
    InnerProductSpace.Core.inner_self_ofReal_re (𝕜 := ℂ) x
  have hq : ((RCLike.re (⟪y, y⟫ : ℂ) : ℝ) : ℂ) = (⟪y, y⟫ : ℂ) :=
    InnerProductSpace.Core.inner_self_ofReal_re (𝕜 := ℂ) y
  have hc : ‖(⟪y, x⟫ : ℂ)‖ = ‖(⟪x, y⟫ : ℂ)‖ :=
    InnerProductSpace.Core.norm_inner_symm (𝕜 := ℂ) y x
  rw [hc, ← hp, ← hq, ← Complex.ofReal_pow, ← Complex.ofReal_mul] at hmain
  exact_mod_cast hmain

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), main clause:
`‖x‖ = √⟪x,x⟫` is a seminorm — nonnegative, absolutely homogeneous, and
subadditive (the triangle inequality, proved as the exercise's hint
suggests, from Cauchy–Schwarz). -/
theorem inner_product_seminorm (x y : V) (l : ℂ) :
    0 ≤ innerNorm x ∧ innerNorm (l • x) = ‖l‖ * innerNorm x ∧
      innerNorm (x + y) ≤ innerNorm x + innerNorm y := by
  refine ⟨innerNorm_nonneg x, ?_, ?_⟩
  · have e : RCLike.re (⟪l • x, l • x⟫ : ℂ) = ‖l‖ ^ 2 * RCLike.re (⟪x, x⟫ : ℂ) := by
      rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
        InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ), ← mul_assoc,
        RCLike.conj_mul]
      simp [← Complex.ofReal_pow]
    rw [innerNorm, innerNorm, e, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg l)]
  · have hcs : ‖(⟪x, y⟫ : ℂ)‖ ≤ innerNorm x * innerNorm y := by
      have h1 := inner_product_basic_1 x y
      rw [← innerNorm_sq, ← innerNorm_sq] at h1
      nlinarith [norm_nonneg (⟪x, y⟫ : ℂ), innerNorm_nonneg x, innerNorm_nonneg y,
        mul_nonneg (innerNorm_nonneg x) (innerNorm_nonneg y)]
    have hre : RCLike.re (⟪x, y⟫ : ℂ) ≤ innerNorm x * innerNorm y :=
      le_trans (RCLike.re_le_norm _) hcs
    have hre' : RCLike.re (⟪y, x⟫ : ℂ) ≤ innerNorm x * innerNorm y := by
      rw [← InnerProductSpace.Core.inner_re_symm (𝕜 := ℂ)]
      exact hre
    have expand : RCLike.re (⟪x + y, x + y⟫ : ℂ)
        = RCLike.re (⟪x, x⟫ : ℂ) + RCLike.re (⟪x, y⟫ : ℂ) + RCLike.re (⟪y, x⟫ : ℂ)
          + RCLike.re (⟪y, y⟫ : ℂ) := by
      rw [InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ)]
      simp
    have hle : RCLike.re (⟪x + y, x + y⟫ : ℂ) ≤ (innerNorm x + innerNorm y) ^ 2 := by
      rw [expand, ← innerNorm_sq, ← innerNorm_sq]
      nlinarith [hre, hre']
    calc innerNorm (x + y) = Real.sqrt (RCLike.re (⟪x + y, x + y⟫ : ℂ)) := rfl
      _ ≤ Real.sqrt ((innerNorm x + innerNorm y) ^ 2) := Real.sqrt_le_sqrt hle
      _ = innerNorm x + innerNorm y :=
          Real.sqrt_sq (add_nonneg (innerNorm_nonneg x) (innerNorm_nonneg y))

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), main clause:
`‖x‖ = √⟪x,x⟫` is a *norm* when the inner product is definite. -/
theorem inner_product_norm_of_definite (hdef : ∀ z : V, (⟪z, z⟫ : ℂ) = 0 → z = 0) (x : V) :
    innerNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    refine hdef x ?_
    have h2 : RCLike.re (⟪x, x⟫ : ℂ) = 0 := by
      have := innerNorm_sq x
      rw [h] at this
      simpa using this.symm
    rw [← InnerProductSpace.Core.inner_self_ofReal_re (𝕜 := ℂ) x, h2]
    simp
  · rintro rfl
    rw [innerNorm, InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ)]
    simp

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 2:
Pythagoras' theorem: `‖x‖² + ‖y‖² = ‖x + y‖²` when `⟪x,y⟫ = 0`. -/
theorem inner_product_basic_2 (x y : V) (h : (⟪x, y⟫ : ℂ) = 0) :
    innerNorm x ^ 2 + innerNorm y ^ 2 = innerNorm (x + y) ^ 2 := by
  have hyx : (⟪y, x⟫ : ℂ) = 0 := by
    rw [← InnerProductSpace.Core.inner_conj_symm (𝕜 := ℂ), h, map_zero]
  rw [innerNorm_sq, innerNorm_sq, innerNorm_sq,
    InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ), h, hyx]
  simp

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 3: the
parallelogram law. -/
theorem inner_product_basic_3 (x y : V) :
    innerNorm x ^ 2 + innerNorm y ^ 2
      = (innerNorm (x + y) ^ 2 + innerNorm (x - y) ^ 2) / 2 := by
  rw [innerNorm_sq, innerNorm_sq, innerNorm_sq, innerNorm_sq,
    InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ),
    InnerProductSpace.Core.inner_sub_sub_self (𝕜 := ℂ)]
  simp
  ring

/-- **4XV** (`inner-product-basic`, cstar.tex:590, Exercise), part 4: the
polarisation identity `⟪x,y⟫ = ¼ ∑_{n<4} iⁿ ‖iⁿ x + y‖²`. -/
theorem inner_product_basic_4 (x y : V) :
    (⟪x, y⟫ : ℂ) = (∑ n ∈ Finset.range 4,
      Complex.I ^ n * ((innerNorm ((Complex.I ^ n : ℂ) • x + y) : ℂ)) ^ 2) / 4 := by
  have expand : ∀ n : ℕ, ((innerNorm ((Complex.I ^ n : ℂ) • x + y) : ℂ)) ^ 2
      = ⟪x, x⟫ + (starRingEnd ℂ) (Complex.I ^ n) * ⟪x, y⟫
        + Complex.I ^ n * ⟪y, x⟫ + ⟪y, y⟫ := by
    intro n
    rw [innerNorm_sq_coe, InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ),
      InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
      InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ),
      InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ),
      InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
    rw [← mul_assoc, RCLike.conj_mul]
    simp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, expand]
  simp only [pow_zero, pow_one, map_one, map_pow, Complex.conj_I, Complex.I_sq]
  ring_nf
  simp [Complex.ext_iff]
  constructor <;> ring

end IndefiniteInner

/-- Auxiliary: Pythagoras' theorem (**4XV**.2) in the definite, normed case,
where `‖·‖` is the norm of the pre-Hilbert space `H` itself. -/
private theorem norm_add_sq_of_inner_eq_zero (x y : H) (h : ⟪x, y⟫ = 0) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = ‖x + y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ) x y, h]
  simp

/-- Auxiliary: the parallelogram law (**4XV**.3) in the definite, normed
case, where `‖·‖` is the norm of the pre-Hilbert space `H` itself.  As in the
solution, it is the average of the two expansions of `‖x ± y‖²`. -/
private theorem norm_add_sq_add_norm_sub_sq (x y : H) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [norm_add_sq (𝕜 := ℂ) x y, norm_sub_sq (𝕜 := ℂ) x y]
  ring

/-- Auxiliary: if `A` is adjoint to `B` (as bounded operators on a pre-Hilbert
space) then `‖A‖ ≤ ‖B‖`.  Used for both parts of **4XVI**. -/
private theorem norm_le_of_isAdjointTo (A B : H →L[ℂ] H)
    (hAB : IsAdjointTo (⇑A) (⇑B)) : ‖A‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound A (norm_nonneg B) fun x => ?_
  have e1 : (‖A x‖ : ℝ) ^ 2 = ‖(⟪x, B (A x)⟫ : ℂ)‖ := by
    rw [← hAB x (A x), inner_self_eq_norm_sq_to_K]
    simp
  have e2 : ‖(⟪x, B (A x)⟫ : ℂ)‖ ≤ ‖x‖ * (‖B‖ * ‖A x‖) :=
    (norm_inner_le_norm (𝕜 := ℂ) x (B (A x))).trans
      (by gcongr; exact B.le_opNorm (A x))
  rw [← e1] at e2
  nlinarith [norm_nonneg (A x), norm_nonneg x, norm_nonneg B,
    mul_nonneg (norm_nonneg B) (norm_nonneg x)]

/-- Auxiliary: the adjoint of a bounded operator on a pre-Hilbert space is
itself linear and bounded (by `‖T‖`), so that it is an element of `B(H)`.
This is the part of **4XVI** that the thesis leaves implicit when it writes
`‖T*‖`: linearity is **4X**-style uniqueness reasoning, and boundedness is
the estimate `‖T*y‖² = ⟪T T* y, y⟫ ≤ ‖T‖ ‖T*y‖ ‖y‖`. -/
private noncomputable def adjointCLM (T : H →L[ℂ] H) (S : H → H)
    (h : IsAdjointTo (⇑T) S) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := S
      map_add' := fun y z => ext_inner_left ℂ fun x => by
        rw [← h x (y + z), inner_add_right, inner_add_right, ← h x y, ← h x z]
      map_smul' := fun c y => ext_inner_left ℂ fun x => by
        rw [RingHom.id_apply, inner_smul_right, ← h x y, ← h x (c • y), inner_smul_right] }
    ‖T‖ fun y => by
      show (‖S y‖ : ℝ) ≤ ‖T‖ * ‖y‖
      have key : (‖S y‖ : ℝ) ^ 2 = ‖(⟪T (S y), y⟫ : ℂ)‖ := by
        rw [h (S y) y, inner_self_eq_norm_sq_to_K]
        simp
      have e2 : ‖(⟪T (S y), y⟫ : ℂ)‖ ≤ ‖T‖ * ‖S y‖ * ‖y‖ :=
        (norm_inner_le_norm (𝕜 := ℂ) (T (S y)) y).trans
          (by gcongr; exact T.le_opNorm (S y))
      nlinarith [norm_nonneg (S y), norm_nonneg y, norm_nonneg T,
        mul_nonneg (norm_nonneg T) (norm_nonneg y)]

private theorem coe_adjointCLM (T : H →L[ℂ] H) (S : H → H)
    (h : IsAdjointTo (⇑T) S) : ⇑(adjointCLM T S h) = S := rfl

/-- Auxiliary: the C*-identity for a pair of bounded operators that are
adjoint to one another — the computation of **4XVI**, with the adjoint
already bundled as an element of `B(H)` by `adjointCLM`. -/
private theorem cstar_identity_aux (T S : H →L[ℂ] H)
    (h : IsAdjointTo T S) : ‖S.comp T‖ = ‖T‖ ^ 2 :=
  by
    have hST : ‖S‖ = ‖T‖ := le_antisymm (norm_le_of_isAdjointTo S T (isAdjointTo_symm T S h))
      (norm_le_of_isAdjointTo T S h)
    refine le_antisymm ?_ ?_
    · calc ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le S T
        _ = ‖T‖ ^ 2 := by rw [hST, sq]
    · have h1 : ∀ x : H, ‖T x‖ ≤ Real.sqrt ‖S.comp T‖ * ‖x‖ := by
        intro x
        have e1 : (‖T x‖ : ℝ) ^ 2 = ‖(⟪x, (S.comp T) x⟫ : ℂ)‖ := by
          rw [show (S.comp T) x = S (T x) from rfl, ← h x (T x), inner_self_eq_norm_sq_to_K]
          simp
        have e2 : ‖(⟪x, (S.comp T) x⟫ : ℂ)‖ ≤ ‖x‖ * (‖S.comp T‖ * ‖x‖) :=
          (norm_inner_le_norm (𝕜 := ℂ) x _).trans (by gcongr; exact (S.comp T).le_opNorm x)
        have e3 : (‖T x‖ : ℝ) ^ 2 ≤ ‖S.comp T‖ * ‖x‖ ^ 2 := by
          rw [e1]
          nlinarith [e2]
        calc ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖S.comp T‖ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt e3
          _ = Real.sqrt ‖S.comp T‖ * ‖x‖ := by
              rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      have h2 := ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) h1
      nlinarith [Real.sq_sqrt (norm_nonneg (S.comp T)), Real.sqrt_nonneg ‖S.comp T‖,
        norm_nonneg T]

/-- **4XVI** (`operators-cstar-identity`, cstar.tex:642, Lemma), part 1: for
a bounded adjointable operator `T` on a pre-Hilbert space — the adjoint `S`
being, a priori, an arbitrary map `H → H` — the adjoint is itself a bounded
operator and `‖T* T‖ = ‖T‖²` (the C*-identity). -/
theorem operators_cstar_identity_1 (T : H →L[ℂ] H) (S : H → H)
    (h : IsAdjointTo (⇑T) S) :
    ∃ S' : H →L[ℂ] H, ⇑S' = S ∧ ‖S'.comp T‖ = ‖T‖ ^ 2 :=
  ⟨adjointCLM T S h, coe_adjointCLM T S h, cstar_identity_aux T (adjointCLM T S h) h⟩

/-- **4XVI** (`operators-cstar-identity`, cstar.tex:642, Lemma), part 2:
`‖T*‖ = ‖T‖` — again with the adjoint only assumed to be a map `H → H`,
its boundedness being part of the conclusion. -/
theorem operators_cstar_identity_2 (T : H →L[ℂ] H) (S : H → H)
    (h : IsAdjointTo (⇑T) S) :
    ∃ S' : H →L[ℂ] H, ⇑S' = S ∧ ‖S'‖ = ‖T‖ :=
  ⟨adjointCLM T S h, coe_adjointCLM T S h,
    le_antisymm
      (norm_le_of_isAdjointTo _ T (isAdjointTo_symm _ _ h))
      (norm_le_of_isAdjointTo T _ h)⟩

/-- **4XVIII** (cstar.tex:666, Exercise): for a Hilbert space `H` the
adjointable operators form a closed *linear subspace* of `B(H)`.  The
subspace clause is the closure of adjointability under `0`, sums and
scalars, i.e. **4XII**.

Closedness is proved as solution `parsec-40.180` does, with the material of
parsec 40 alone: if `Tₙ → T` with each `Tₙ` adjointable, then the adjoints
`Tₙ*` are Cauchy because `‖Tₙ* - Tₘ*‖ = ‖(Tₙ - Tₘ)*‖ = ‖Tₙ - Tₘ‖`
(**4XVI**.2), so they converge to some `S` by completeness of `B(H)`
(**4V**), and `⟪T x, y⟫ = lim ⟪Tₙ x, y⟫ = lim ⟪x, Tₙ* y⟫ = ⟪x, S y⟫` by
continuity of the inner product.  It does not go through **5XI**, that
*every* bounded operator on a Hilbert space is adjointable, which belongs
to the next parsec. -/
theorem adjointable_isClosed [CompleteSpace H] :
    IsClosed {T : H →L[ℂ] H | Adjointable (⇑T)} ∧
      ∃ M : Submodule ℂ (H →L[ℂ] H),
        (M : Set (H →L[ℂ] H)) = {T : H →L[ℂ] H | Adjointable (⇑T)} :=
  by
    constructor
    · refine IsSeqClosed.isClosed fun Tn T hmem hconv => ?_
      choose S hS using hmem
      -- the adjoints, as bounded operators (**4XVI**)
      set A : ℕ → (H →L[ℂ] H) := fun n => adjointCLM (Tn n) (S n) (hS n) with hA
      have hadj : ∀ n, IsAdjointTo (⇑(Tn n)) (⇑(A n)) := by
        intro n
        rw [hA, coe_adjointCLM]
        exact hS n
      have hsub : ∀ n m, IsAdjointTo (⇑(Tn n - Tn m)) (⇑(A n - A m)) := by
        intro n m x y
        simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right,
          hadj n x y, hadj m x y]
      -- `‖Tₙ* - Tₘ*‖ = ‖Tₙ - Tₘ‖`, so the adjoints are Cauchy
      have hnorm : ∀ n m, ‖A n - A m‖ = ‖Tn n - Tn m‖ := fun n m =>
        le_antisymm (norm_le_of_isAdjointTo _ _ (isAdjointTo_symm _ _ (hsub n m)))
          (norm_le_of_isAdjointTo _ _ (hsub n m))
      have hcauchyT : CauchySeq Tn := hconv.cauchySeq
      have hcauchyA : CauchySeq A := by
        rw [Metric.cauchySeq_iff] at hcauchyT ⊢
        intro ε hε
        obtain ⟨N, hN⟩ := hcauchyT ε hε
        refine ⟨N, fun m hm n hn => ?_⟩
        rw [dist_eq_norm, hnorm, ← dist_eq_norm]
        exact hN m hm n hn
      -- `B(H)` is complete (**4V**), so they converge; the limit is adjoint to `T`
      obtain ⟨S', hS'⟩ := cauchySeq_tendsto_of_complete hcauchyA
      have heval : ∀ (Un : ℕ → (H →L[ℂ] H)) (U : H →L[ℂ] H),
          Filter.Tendsto Un Filter.atTop (nhds U) → ∀ z : H,
            Filter.Tendsto (fun n => Un n z) Filter.atTop (nhds (U z)) := by
        intro Un U hU z
        exact (((ContinuousLinearMap.apply ℂ H z).continuous).tendsto U).comp hU
      refine ⟨⇑S', fun x y => ?_⟩
      have h1 : Filter.Tendsto (fun n => (⟪(Tn n) x, y⟫ : ℂ)) Filter.atTop (nhds ⟪T x, y⟫) :=
        (heval Tn T hconv x).inner tendsto_const_nhds
      have h2 : Filter.Tendsto (fun n => (⟪x, (A n) y⟫ : ℂ)) Filter.atTop (nhds ⟪x, S' y⟫) :=
        tendsto_const_nhds.inner (heval A S' hS' y)
      refine tendsto_nhds_unique h1 ?_
      simpa only [hadj _ x y] using h2
    · refine ⟨{ carrier := {T : H →L[ℂ] H | Adjointable (⇑T)}
                add_mem' := ?_
                zero_mem' := ?_
                smul_mem' := ?_ }, rfl⟩
      · rintro T T' ⟨S, hS⟩ ⟨S', hS'⟩
        refine ⟨S + S', fun x y => ?_⟩
        simp only [ContinuousLinearMap.add_apply, Pi.add_apply, inner_add_left,
          inner_add_right, hS x y, hS' x y]
      · exact ⟨fun _ => 0, fun x y => by simp⟩
      · rintro c T ⟨S, hS⟩
        refine ⟨fun y => (starRingEnd ℂ) c • S y, fun x y => ?_⟩
        simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, hS x y]

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise): the operator
`|x⟩⟨y| : z ↦ ⟪y, z⟫ x` on a Hilbert space, bounded by construction. -/
noncomputable def ketbra (x y : H) : H →L[ℂ] H :=
  (innerSL ℂ y).smulRight x

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise), part 1: `|x⟩⟨y|` maps `z`
to `⟪y, z⟫ x` and has operator norm `‖x‖ ‖y‖`. -/
theorem ketbra_norm (x y : H) : ‖ketbra x y‖ = ‖x‖ * ‖y‖ := by
  -- the solution's two-sided estimate
  have happ : ∀ z : H, ketbra x y z = (⟪y, z⟫ : ℂ) • x := fun z => rfl
  refine le_antisymm ?_ ?_
  · -- `‖ |x⟩⟨y| z ‖ = |⟪y,z⟫| ‖x‖ ≤ ‖y‖ ‖z‖ ‖x‖`, so `‖x‖ ‖y‖` is a bound
    refine (ketbra x y).opNorm_le_bound (by positivity) fun z => ?_
    rw [happ z, norm_smul]
    calc ‖(⟪y, z⟫ : ℂ)‖ * ‖x‖ ≤ (‖y‖ * ‖z‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm y z) (norm_nonneg x)
      _ = ‖x‖ * ‖y‖ * ‖z‖ := by ring
  · -- and `‖ |x⟩⟨y| ‖ ‖y‖ ≥ ‖ |x⟩⟨y| y ‖ = ‖y‖² ‖x‖`, even when `‖y‖ = 0`
    have hle : ‖ketbra x y y‖ ≤ ‖ketbra x y‖ * ‖y‖ := (ketbra x y).le_opNorm y
    have hyy : ‖(⟪y, y⟫ : ℂ)‖ = ‖y‖ ^ 2 := by
      simp [inner_self_eq_norm_sq_to_K, norm_pow]
    rw [happ y, norm_smul, hyy] at hle
    rcases eq_or_lt_of_le (norm_nonneg y) with hy | hy
    · rw [← hy]
      simp
    · nlinarith [norm_nonneg x, norm_nonneg (ketbra x y)]

/-- **4XIX** (`ketbra`, cstar.tex:671, Exercise), part 2: `|x⟩⟨y|` is
adjointable, with `(|x⟩⟨y|)* = |y⟩⟨x|`. -/
theorem ketbra_adjoint (x y : H) :
    IsAdjointTo (⇑(ketbra x y)) (⇑(ketbra y x)) :=
  by
    intro z w
    simp [ketbra, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

/-! ## Parsec 50 (`hilb-adjoint`): projections, Riesz representation, B(H)

**5I** (`adjoinables-cstar-algebra`, cstar.tex:689): the adjointable
operators on a Hilbert space form a C*-algebra; to see that `B(H)` is one
it remains to show every bounded operator is adjointable (**5XI**). -/

/-- **5II** (`projection-on-closed-linear-subspace`, cstar.tex:702,
Definition): `y` is a *projection of `x` on* a linear subspace `C` when
`y ∈ C` and `‖x - y‖ = min { ‖x - y'‖ : y' ∈ C }`. -/
def IsProjectionOn (C : Submodule ℂ H) (x y : H) : Prop :=
  y ∈ C ∧ ∀ y' ∈ C, ‖x - y‖ ≤ ‖x - y'‖

/-- Auxiliary (**5IV**): the Pythagoras identity for the distance from `x` to
a point of the line `ℂe` spanned by a unit vector `e`. -/
private theorem norm_sub_smul_sq (x e : H) (he : ‖e‖ = 1) (c : ℂ) :
    ‖x - c • e‖ ^ 2 = ‖x - ⟪e, x⟫ • e‖ ^ 2 + ‖⟪e, x⟫ - c‖ ^ 2 := by
  have hee : (⟪e, e⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have horth : (⟪x - ⟪e, x⟫ • e, (⟪e, x⟫ - c) • e⟫ : ℂ) = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_smul_left, hee, mul_one, inner_conj_symm,
      sub_self, mul_zero]
  have hsplit : x - c • e = (x - ⟪e, x⟫ • e) + (⟪e, x⟫ - c) • e := by
    rw [sub_smul]; abel
  have hp := norm_add_sq_of_inner_eq_zero (x - ⟪e, x⟫ • e) ((⟪e, x⟫ - c) • e) horth
  rw [← hsplit] at hp
  rw [← hp, norm_smul, he, mul_one]

/-- Auxiliary for **5III**: every element of `c₀₀` — the span of the
coordinate vectors `lp.single 2 n z` — vanishes from some index on.  This is
the "since `y` is in `c₀₀`, there's `N` such that `yₙ = 0` for all `n > N`"
of solution `parsec-50.30`. -/
private theorem c00_eventually_zero {f : lp (fun _ : ℕ => ℂ) 2}
    (hf : f ∈ Submodule.span ℂ
      {g : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, g = lp.single 2 n z}) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → f n = 0 :=
  by
    induction hf using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨m, z, rfl⟩ := hg
        refine ⟨m, fun n hn => ?_⟩
        have hne : n ≠ m := by omega
        simp [hne]
    | zero => exact ⟨0, fun n _ => by simp⟩
    | add g h _ _ ihg ihh =>
        obtain ⟨N₁, hN₁⟩ := ihg
        obtain ⟨N₂, hN₂⟩ := ihh
        refine ⟨max N₁ N₂, fun n hn => ?_⟩
        have h₁ := hN₁ n (lt_of_le_of_lt (le_max_left N₁ N₂) hn)
        have h₂ := hN₂ n (lt_of_le_of_lt (le_max_right N₁ N₂) hn)
        simp [h₁, h₂]
    | smul c g _ ih =>
        obtain ⟨N, hN⟩ := ih
        exact ⟨N, fun n hn => by simp [hN n hn]⟩

/-- Auxiliary for **5III**: the truncation of `x` at `N` — the element `y'`
of `c₀₀` that solution `parsec-50.30` compares `y` with — agrees with `x` up
to `N`. -/
private theorem c00_trunc_apply_le (x : lp (fun _ : ℕ => ℂ) 2) {N n : ℕ} (h : n ≤ N) :
    (∑ k ∈ Finset.range (N + 1), lp.single 2 k (x k) : lp (fun _ : ℕ => ℂ) 2) n = x n :=
  by
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_single]
    rw [Finset.sum_pi_single, ite_eq_left (by simp only [Finset.mem_range]; omega)]

/-- Auxiliary for **5III**: the truncation of `x` at `N` vanishes after `N`. -/
private theorem c00_trunc_apply_gt (x : lp (fun _ : ℕ => ℂ) 2) {N n : ℕ} (h : ¬ n ≤ N) :
    (∑ k ∈ Finset.range (N + 1), lp.single 2 k (x k) : lp (fun _ : ℕ => ℂ) 2) n = 0 :=
  by
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_single]
    rw [Finset.sum_pi_single, ite_eq_right (by simp only [Finset.mem_range]; omega)]

/-- Auxiliary for **5III**: the truncation of `x` at `N` lies in `c₀₀`. -/
private theorem c00_trunc_mem (x : lp (fun _ : ℕ => ℂ) 2) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), lp.single 2 k (x k) : lp (fun _ : ℕ => ℂ) 2)
      ∈ Submodule.span ℂ {g : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, g = lp.single 2 n z} :=
  sum_mem fun k _ => Submodule.subset_span ⟨k, _, rfl⟩

/-- Auxiliary for **5III**: in `ℓ²` a vector dominated coordinatewise by
another, and strictly smaller in one coordinate, has strictly smaller norm.
This is the comparison of two `ℓ²` sums that solution `parsec-50.30` makes by
splitting off a finite prefix. -/
private theorem lp_two_norm_lt {f g : lp (fun _ : ℕ => ℂ) 2} (m : ℕ)
    (h : ∀ n : ℕ, ‖f n‖ ≤ ‖g n‖) (hm : ‖f m‖ < ‖g m‖) : ‖f‖ < ‖g‖ :=
  by
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have hf := lp.hasSum_norm hp f
    have hg := lp.hasSum_norm hp g
    have hlt : ‖f‖ ^ (2 : ENNReal).toReal < ‖g‖ ^ (2 : ENNReal).toReal := by
      rw [← hf.tsum_eq, ← hg.tsum_eq]
      exact Summable.tsum_lt_tsum_of_nonneg (i := m)
        (fun n => Real.rpow_nonneg (norm_nonneg _) _)
        (fun n => Real.rpow_le_rpow (norm_nonneg _) (h n) hp.le)
        (Real.rpow_lt_rpow (norm_nonneg _) hm hp) hg.summable
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).mp hlt

/-- **5III** (cstar.tex:713, Exercise): in `ℓ²` the only vectors having a
projection on the (non-closed) subspace `c₀₀` of finitely supported
sequences are the vectors of `c₀₀` themselves.  (Here `c₀₀` is the span of
the coordinate vectors `lp.single 2 n z`.) -/
theorem projection_on_c00 (x : lp (fun _ : ℕ => ℂ) 2) :
    (∃ y, IsProjectionOn
        (Submodule.span ℂ {f : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, f = lp.single 2 n z})
        x y) ↔
      x ∈ Submodule.span ℂ
        {f : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, f = lp.single 2 n z} :=
  by
    constructor
    · rintro ⟨y, hy⟩
      -- Solution `parsec-50.30`, by contradiction: let `x ∈ ℓ² \ c₀₀`, so that
      -- `xₙ ≠ 0` for infinitely many `n`, and let `y ∈ c₀₀` be closest to `x`.
      by_contra hx
      -- "Since `y` is in `c₀₀`, there's `N` such that `yₙ = 0` for all `n > N`."
      obtain ⟨N, hN⟩ := c00_eventually_zero hy.1
      -- `x` is not eventually zero, or it would be its own truncation, in `c₀₀`.
      have hinf : ∀ M : ℕ, ∃ m : ℕ, M < m ∧ x m ≠ 0 := by
        intro M
        by_contra hcon
        have hzero : ∀ m : ℕ, M < m → x m = 0 := by
          intro m hm
          by_contra hne
          exact hcon ⟨m, hm, hne⟩
        refine hx ?_
        have hxe : x = ∑ k ∈ Finset.range (M + 1), lp.single 2 k (x k) := by
          refine lp.ext (funext fun n => ?_)
          by_cases hn : n ≤ M
          · rw [c00_trunc_apply_le x hn]
          · rw [c00_trunc_apply_gt x hn]
            exact hzero n (by omega)
        rw [hxe]
        exact c00_trunc_mem x M
      -- "We claim that `xₙ = yₙ` for all `n ≤ N`": otherwise the truncation
      -- `y'` of `x` at `N` — which agrees with `x` up to `N` and vanishes
      -- after it, so that `‖x - y'‖² = ∑_{n>N} |xₙ|²` — is strictly closer to
      -- `x` than `y` is, contradicting minimality.
      have hagree : ∀ n : ℕ, n ≤ N → x n = y n := by
        intro n hn
        by_contra hne
        have hlt : ‖x - ∑ k ∈ Finset.range (N + 1), lp.single 2 k (x k)‖ < ‖x - y‖ := by
          refine lp_two_norm_lt n (fun m => ?_) ?_
          · simp only [lp.coeFn_sub, Pi.sub_apply]
            by_cases hm : m ≤ N
            · rw [c00_trunc_apply_le x hm, sub_self, norm_zero]
              exact norm_nonneg _
            · exact le_of_eq (by rw [c00_trunc_apply_gt x hm, hN m (by omega)])
          · simp only [lp.coeFn_sub, Pi.sub_apply]
            rw [c00_trunc_apply_le x hn, sub_self, norm_zero]
            exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        exact absurd (hy.2 _ (c00_trunc_mem x N)) (not_le.mpr hlt)
      -- "In particular, `y = y'`."
      have hyeq : y = ∑ k ∈ Finset.range (N + 1), lp.single 2 k (x k) := by
        refine lp.ext (funext fun n => ?_)
        by_cases hn : n ≤ N
        · rw [c00_trunc_apply_le x hn]
          exact (hagree n hn).symm
        · rw [c00_trunc_apply_gt x hn]
          exact hN n (by omega)
      -- "It's now easy to find a better approximation of `x` in `c₀₀` than `y`":
      -- an `M > N` with `x M ≠ 0` makes the truncation `y''` of `x` at `M`
      -- satisfy `‖x - y''‖² = ∑_{n>M} |xₙ|² < ∑_{n>N} |xₙ|² = ‖x - y'‖²`,
      -- the term `|x_M|²` being dropped.
      obtain ⟨M, hMN, hxM⟩ := hinf N
      have hlt : ‖x - ∑ k ∈ Finset.range (M + 1), lp.single 2 k (x k)‖ < ‖x - y‖ := by
        rw [hyeq]
        refine lp_two_norm_lt M (fun m => ?_) ?_
        · simp only [lp.coeFn_sub, Pi.sub_apply]
          by_cases hm : m ≤ M
          · rw [c00_trunc_apply_le x hm, sub_self, norm_zero]
            exact norm_nonneg _
          · have hm' : ¬ m ≤ N := by omega
            exact le_of_eq (by rw [c00_trunc_apply_gt x hm, c00_trunc_apply_gt x hm'])
        · simp only [lp.coeFn_sub, Pi.sub_apply]
          rw [c00_trunc_apply_le x (le_refl M), sub_self, norm_zero,
            c00_trunc_apply_gt x (by omega : ¬ M ≤ N), sub_zero]
          exact norm_pos_iff.mpr hxM
      exact absurd (hy.2 _ (c00_trunc_mem x M)) (not_le.mpr hlt)
    · intro hx
      exact ⟨x, hx, fun y' _ => by simpa using norm_nonneg (x - y')⟩

/-- **5IV** (cstar.tex:726, Lemma): for a unit vector `e` of a pre-Hilbert
space, `⟪e, x⟫ e` is a projection of `x` on the line `ℂe`. -/
theorem projection_on_line (x e : H) (he : ‖e‖ = 1) :
    IsProjectionOn (ℂ ∙ e) x (⟪e, x⟫ • e) :=
  by
    refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e), ?_⟩
    intro y' hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    have hkey := norm_sub_smul_sq x e he c
    nlinarith [norm_nonneg (x - ⟪e, x⟫ • e), norm_nonneg (x - c • e),
      norm_nonneg ((⟪e, x⟫ : ℂ) - c), sq_nonneg (‖(⟪e, x⟫ : ℂ) - c‖)]

/-- **5IV** (cstar.tex:726, Lemma), uniqueness part: `⟪e, x⟫ e` is the
*unique* projection of `x` on `ℂe`. -/
theorem projection_on_line_unique (x e : H) (he : ‖e‖ = 1) (y : H)
    (hy : IsProjectionOn (ℂ ∙ e) x y) : y = ⟪e, x⟫ • e :=
  by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy.1
    subst hc
    have h1 := hy.2 ((⟪e, x⟫ : ℂ) • e)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    have hkey := norm_sub_smul_sq x e he c
    have h2 : ‖(⟪e, x⟫ : ℂ) - c‖ ≤ 0 := by
      nlinarith [norm_nonneg (x - c • e), norm_nonneg (x - (⟪e, x⟫ : ℂ) • e),
        norm_nonneg ((⟪e, x⟫ : ℂ) - c)]
    have h3 := le_antisymm h2 (norm_nonneg _)
    rw [norm_eq_zero, sub_eq_zero] at h3
    rw [h3]

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 1: a
projection `y` of `x` on a linear subspace `C` is a projection of `x` on
the line `ℂy`. -/
theorem hilb_projection_basic_1 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) : IsProjectionOn (ℂ ∙ y) x y :=
  by
    refine ⟨Submodule.mem_span_singleton_self y, ?_⟩
    intro y' hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    exact h.2 _ (C.smul_mem c h.1)

/-- Auxiliary: the claim solution `parsec-50.60` makes first — a projection
`y` of `x` on `C` has `‖y‖² = ⟪y, x⟫`, i.e. `⟪y, x - y⟫ = 0`.  By **5VI**.1
`y` is a projection of `x` on the line `ℂy = ℂe`, `e := y/‖y‖`, and **5IV**
says that projection is `⟪e, x⟫ e`. -/
private theorem IsProjectionOn.inner_self_sub_eq_zero {C : Submodule ℂ H} {x y : H}
    (h : IsProjectionOn C x y) : ⟪y, x - y⟫ = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hn : (‖y‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hy
  obtain ⟨e, hne, hspan⟩ : ∃ e : H, ‖e‖ = 1 ∧ (ℂ ∙ e) = (ℂ ∙ y) := by
    refine ⟨((‖y‖⁻¹ : ℝ) : ℂ) • y, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ hn]
    · exact Submodule.span_singleton_smul_eq (Ne.isUnit (by simpa using inv_ne_zero hn)) _
  have hproj : IsProjectionOn (ℂ ∙ e) x y := by
    rw [hspan]; exact hilb_projection_basic_1 C x y h
  have hy_eq := projection_on_line_unique x e hne y hproj
  have hee : (⟪e, e⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hne]
    norm_num
  rw [hy_eq, inner_sub_right, inner_smul_left, inner_smul_left, inner_smul_right, hee,
    mul_one]
  ring

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 2: the
projection of `x` on `C` is unique, and `⟪y, x - y⟫ = 0`. -/
theorem hilb_projection_basic_2 (C : Submodule ℂ H) (x y y' : H)
    (h : IsProjectionOn C x y) (h' : IsProjectionOn C x y') :
    y' = y ∧ ⟪y, x - y⟫ = 0 :=
  by
    refine ⟨?_, h.inner_self_sub_eq_zero⟩
    -- the solution's translation: both `0` and `y' - y` are projections of
    -- `x - y` on `C`, so they have the same distance to `x - y`, and
    -- Pythagoras on `⟪y'-y, (x-y)-(y'-y)⟫ = 0` forces `y' - y = 0`
    have hzC : y' - y ∈ C := Submodule.sub_mem _ h'.1 h.1
    have hz0 : IsProjectionOn C (x - y) 0 := by
      refine ⟨Submodule.zero_mem C, fun w hw => ?_⟩
      rw [sub_zero, show x - y - w = x - (y + w) by abel]
      exact h.2 _ (Submodule.add_mem _ h.1 hw)
    have hzz : IsProjectionOn C (x - y) (y' - y) := by
      refine ⟨hzC, fun w hw => ?_⟩
      rw [show x - y - (y' - y) = x - y' by abel, show x - y - w = x - (y + w) by abel]
      exact h'.2 _ (Submodule.add_mem _ h.1 hw)
    have horth : (⟪x - y - (y' - y), y' - y⟫ : ℂ) = 0 := by
      have h0 := hzz.inner_self_sub_eq_zero
      simpa only [inner_conj_symm, map_zero] using congrArg (starRingEnd ℂ) h0
    have hsum := norm_add_sq_of_inner_eq_zero (x - y - (y' - y)) (y' - y) horth
    rw [show x - y - (y' - y) + (y' - y) = x - y by abel] at hsum
    have hle1 : ‖x - y - (y' - y)‖ ≤ ‖x - y‖ := by
      simpa using hzz.2 0 (Submodule.zero_mem C)
    have hle2 : ‖x - y‖ ≤ ‖x - y - (y' - y)‖ := by
      simpa using hz0.2 _ hzC
    have hAC : ‖x - y - (y' - y)‖ = ‖x - y‖ := le_antisymm hle1 hle2
    have hzero : ‖y' - y‖ ^ 2 = 0 := by rw [hAC] at hsum; linarith
    have hz : y' - y = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero)
    exact sub_eq_zero.mp hz

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 3:
`y + c` is the projection of `x + c` on `C` for every `c ∈ C`. -/
theorem hilb_projection_basic_3 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) (c : H) (hc : c ∈ C) :
    IsProjectionOn C (x + c) (y + c) :=
  by
    refine ⟨Submodule.add_mem _ h.1 hc, ?_⟩
    intro y' hy'
    rw [show x + c - (y + c) = x - y by abel, show x + c - y' = x - (y' - c) by abel]
    exact h.2 _ (Submodule.sub_mem _ hy' hc)

/-- **5VI** (`hilb-projection-basic`, cstar.tex:755, Exercise), part 4:
`⟪y', x - y⟫ = 0` for every `y' ∈ C`. -/
theorem hilb_projection_basic_4 (C : Submodule ℂ H) (x y : H)
    (h : IsProjectionOn C x y) (y' : H) (hy' : y' ∈ C) :
    ⟪y', x - y⟫ = 0 :=
  by
    -- the solution's trick: `y' = y + (y' - y)` is a projection of
    -- `x' := x + (y' - y)` on `C` by part 3, and `x' - y' = x - y`
    have h3 := hilb_projection_basic_3 C x y h (y' - y) (Submodule.sub_mem _ hy' h.1)
    have h0 := h3.inner_self_sub_eq_zero
    rw [show y + (y' - y) = y' by abel, show x + (y' - y) - y' = x - y by abel] at h0
    exact h0

/-- **5VII** (`projection-theorem`, cstar.tex:766, Projection Theorem): every
vector `x` of a Hilbert space has a unique projection `y` on a closed linear
subspace `C`.  (Mathlib packages the projection as
`Submodule.orthogonalProjection`; the proof below is the Theorem's own.) -/
theorem projection_theorem [CompleteSpace H] (C : Submodule ℂ H)
    (hC : IsClosed (C : Set H)) (x : H) :
    ∃! y, IsProjectionOn C x y := by
  -- the Theorem's own proof: a minimising sequence is Cauchy by the
  -- parallelogram law (**4XV**.3), its limit lies in the closed `C`, and
  -- uniqueness comes from **5VI**.2
  have hne : Nonempty C := ⟨⟨0, C.zero_mem⟩⟩
  have hbdd : BddBelow (Set.range fun y' : C => ‖x - (y' : H)‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  set r : ℝ := ⨅ y' : C, ‖x - (y' : H)‖ with hrdef
  have hrle : ∀ y' : C, r ≤ ‖x - (y' : H)‖ := fun y' => ciInf_le hbdd y'
  have hr0 : 0 ≤ r := le_ciInf fun y' => norm_nonneg _
  -- a minimising sequence `y₁, y₂, … ∈ C` with `‖x - yₙ‖ → r`
  have hpick : ∀ n : ℕ, ∃ w : C, ‖x - (w : H)‖ < r + 1 / (n + 1 : ℝ) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    exact exists_lt_of_ciInf_lt (by rw [← hrdef]; linarith)
  choose y hy using hpick
  -- the parallelogram law bounds `‖yₙ - yₘ‖²`
  have hpar : ∀ n m : ℕ, ‖((y n : H)) - ((y m : H))‖ ^ 2
      ≤ 2 * ‖x - (y n : H)‖ ^ 2 + 2 * ‖x - (y m : H)‖ ^ 2 - 4 * r ^ 2 := by
    intro n m
    set u : H := x - (y n : H) with hu
    set v : H := x - (y m : H) with hv
    have huv : u - v = (y m : H) - (y n : H) := by rw [hu, hv]; abel
    have hmidmem : ((2 : ℂ)⁻¹ : ℂ) • ((y n : H) + (y m : H)) ∈ C :=
      C.smul_mem _ (C.add_mem (y n).2 (y m).2)
    have hsum : u + v = (2 : ℂ) • (x - ((2 : ℂ)⁻¹ : ℂ) • ((y n : H) + (y m : H))) := by
      rw [hu, hv, smul_sub, smul_smul, mul_inv_cancel₀ (two_ne_zero), one_smul]
      module
    have hge : 2 * r ≤ ‖u + v‖ := by
      rw [hsum, norm_smul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      exact mul_le_mul_of_nonneg_left (hrle ⟨_, hmidmem⟩) (by norm_num)
    have hp := norm_add_sq_add_norm_sub_sq u v
    have hnuv : ‖u - v‖ = ‖(y n : H) - (y m : H)‖ := by
      rw [huv, ← norm_neg]
      congr 1
      abel
    rw [hnuv] at hp
    nlinarith [hge, hr0, norm_nonneg (u + v)]
  -- hence the sequence is Cauchy
  have hcauchy : CauchySeq fun n => ((y n : H)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hlim : Filter.Tendsto
        (fun N : ℕ => 4 * (2 * r * (1 / (N + 1 : ℝ)) + (1 / (N + 1 : ℝ)) ^ 2))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun N : ℕ => (1 / (N + 1 : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := ((h1.const_mul (2 * r)).add (h1.mul h1)).const_mul 4
      simpa [sq] using h2
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdm : 1 / (m + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast Nat.succ_le_succ hm]
    have hdn : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast Nat.succ_le_succ hn]
    have hbm := hy m
    have hbn := hy n
    have hd0 : (0 : ℝ) < 1 / (N + 1 : ℝ) := by positivity
    have hNb := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hNb
    have hmain := hpar m n
    rw [dist_eq_norm]
    nlinarith [hmain, hbm, hbn, hdm, hdn, hr0, hd0, hNb, norm_nonneg ((y m : H) - (y n : H)),
      hrle (y m), hrle (y n), hε]
  -- its limit is in `C`, and realises the infimum
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hzC : z ∈ C := hC.mem_of_tendsto hz (Filter.Eventually.of_forall fun n => (y n).2)
  have hnormtend : Filter.Tendsto (fun n => ‖x - (y n : H)‖) Filter.atTop (nhds ‖x - z‖) :=
    (continuous_norm.tendsto _).comp ((tendsto_const_nhds).sub hz)
  have hrz : ‖x - z‖ = r := by
    refine le_antisymm ?_ (hrle ⟨z, hzC⟩)
    refine le_of_tendsto_of_tendsto hnormtend ?_
      (Filter.Eventually.of_forall fun n => (hy n).le)
    simpa using (tendsto_const_nhds (x := r)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hproj : IsProjectionOn C x z := by
    refine ⟨hzC, fun y' hy' => ?_⟩
    rw [hrz]
    exact hrle ⟨y', hy'⟩
  exact ⟨z, hproj, fun w hw => (hilb_projection_basic_2 C x z w hproj hw).1⟩

/-- **5VII** (`projection-theorem`, cstar.tex:766, Projection Theorem),
second part: the projection `y` of `x` on `C` satisfies `⟪y', y⟫ = ⟪y', x⟫`
for all `y' ∈ C`. -/
theorem projection_theorem_inner [CompleteSpace H] (C : Submodule ℂ H)
    (hC : IsClosed (C : Set H)) (x y : H) (h : IsProjectionOn C x y) :
    ∀ y' ∈ C, ⟪y', y⟫ = ⟪y', x⟫ :=
  by
    intro y' hy'
    have hzero := hilb_projection_basic_4 C x y h y' hy'
    rw [inner_sub_right, sub_eq_zero] at hzero
    exact hzero.symm

/-- **5IX** (`riesz-representation-theorem`, cstar.tex:811, Riesz'
Representation Theorem): for every bounded linear map `f : H → ℂ` on a
Hilbert space there is a unique `x ∈ H` with `⟪x, ·⟫ = f`.  (Mathlib has
this as `InnerProductSpace.toDual`; the proof below is the Theorem's own
construction, via the projection on `ker f`.) -/
theorem riesz_representation_theorem [CompleteSpace H] (f : H →L[ℂ] ℂ) :
    ∃! x : H, ∀ z : H, ⟪x, z⟫ = f z := by
  -- the Theorem's own construction, via the projection on `ker f`
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases eq_or_ne f 0 with rfl | hf
    · exact ⟨0, fun z => by simp⟩
    · -- pick `x'` with `f x' = 1`
      obtain ⟨w, hw⟩ : ∃ w : H, f w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hf (by ext w; simpa using hcon w)
      obtain ⟨x', hx'⟩ : ∃ x' : H, f x' = 1 :=
        ⟨(f w)⁻¹ • w, by simp [inv_mul_cancel₀ hw]⟩
      -- `ker f` is closed because `f` is bounded, so `x'` has a projection `y` on it
      set C : Submodule ℂ H := LinearMap.ker (f : H →ₗ[ℂ] ℂ) with hC
      have hCclosed : IsClosed (C : Set H) := f.isClosed_ker
      obtain ⟨y, hy, -⟩ := projection_theorem C hCclosed x'
      set x'' : H := x' - y with hx''
      have hyker : f y = 0 := hy.1
      have hfx'' : f x'' = 1 := by rw [hx'', map_sub, hx', hyker, sub_zero]
      have horth : ∀ y' ∈ C, (⟪x'', y'⟫ : ℂ) = 0 := by
        intro y' hy'
        rw [← inner_conj_symm, hilb_projection_basic_4 C x' y hy y' hy', map_zero]
      have hx''ne : x'' ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hfx''
        exact zero_ne_one hfx''
      have hnorm : ‖x''‖ ^ 2 ≠ 0 := by positivity
      refine ⟨((‖x''‖ ^ 2 : ℝ)⁻¹ : ℂ) • x'', fun z => ?_⟩
      -- `z - f z · x''` lies in `ker f`, so `0 = ⟪x'', z⟫ - f z ‖x''‖²`
      have hmem : z - f z • x'' ∈ C := by
        simp [hC, LinearMap.mem_ker, map_sub, map_smul, hfx'']
      have hself : (⟪x'', x''⟫ : ℂ) = ((‖x''‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; norm_num
      have h0 := horth _ hmem
      rw [inner_sub_right, inner_smul_right, hself, sub_eq_zero] at h0
      rw [inner_smul_left, h0]
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
  · intro x1 x2 h1 h2
    refine uniqueness_adjoint_1 x1 x2 fun z => ?_
    rw [← inner_conj_symm z x1, ← inner_conj_symm z x2, h1 z, h2 z]

/-- **5XI** (`bounded-operator-adjoinable`, cstar.tex:842, Exercise): every
bounded operator on a Hilbert space is adjointable.

The exercise's own construction: for each `y` the functional `z ↦ ⟪y, T z⟫`
is bounded, so by Riesz (**5IX**) there is a unique `S y` with
`⟪S y, z⟫ = ⟪y, T z⟫`; conjugating gives `⟪T x, y⟫ = ⟪x, S y⟫`, and `S` is a
*bounded* operator by **4XVI**. -/
theorem bounded_operator_adjoinable [CompleteSpace H] (T : H →L[ℂ] H) :
    ∃ S : H →L[ℂ] H, IsAdjointTo (⇑T) (⇑S) :=
  by
    have hR : ∀ y : H, ∃ w : H, ∀ z : H, (⟪w, z⟫ : ℂ) = ⟪y, T z⟫ := by
      intro y
      obtain ⟨w, hw, -⟩ := riesz_representation_theorem ((innerSL ℂ y).comp T)
      exact ⟨w, fun z => by simpa using hw z⟩
    choose S hS using hR
    have hadj : IsAdjointTo (⇑T) S := by
      intro x y
      calc (⟪T x, y⟫ : ℂ) = (starRingEnd ℂ) ⟪y, T x⟫ := (inner_conj_symm _ _).symm
        _ = (starRingEnd ℂ) ⟪S y, x⟫ := by rw [hS y x]
        _ = ⟪x, S y⟫ := inner_conj_symm _ _
    exact ⟨adjointCLM T S hadj, by rw [coe_adjointCLM]; exact hadj⟩

/-! **5XII** (cstar.tex:854): thus the bounded operators on a Hilbert space
form a C*-algebra `B(H)` — Mathlib's `CStarAlgebra (H →L[ℂ] H)` instance. -/

end PreHilbert

/-! ## Parsec 60: the Hilbert direct sum -/

section HilbSum

variable {ι : Type*} {Hi : ι → Type*} [∀ i, NormedAddCommGroup (Hi i)]
  [∀ i, InnerProductSpace ℂ (Hi i)] [∀ i, CompleteSpace (Hi i)]

set_option linter.unusedSectionVars false in
/-- **6II** (`hilb-sum`, cstar.tex:873, Proposition), part 1: for members
`x, y` of the direct sum `⊕ᵢ Hᵢ = {x ∈ Π Hᵢ | ∑ᵢ ‖xᵢ‖² < ∞}` (Mathlib:
`lp Hi 2`) the sum `∑ᵢ ⟪xᵢ, yᵢ⟫` defining the inner product converges. -/
theorem hilb_sum_summable (x y : lp Hi 2) :
    Summable fun i => ⟪(x : ∀ i, Hi i) i, (y : ∀ i, Hi i) i⟫ := by
  -- the Proposition's own argument: the Cauchy tail criterion, closed by
  -- Cauchy--Schwarz on each finite subset
  classical
  have hsq : ∀ z : lp Hi 2, Summable fun i => ‖(z : ∀ i, Hi i) i‖ ^ 2 := by
    intro z
    have h := (lp.memℓp z).summable (p := 2) (by norm_num)
    simpa using h
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s₁, hs₁⟩ := summable_iff_vanishing_norm.mp (hsq x) (ε / 2) (by positivity)
  obtain ⟨s₂, hs₂⟩ := summable_iff_vanishing_norm.mp (hsq y) (ε / 2) (by positivity)
  refine ⟨s₁ ∪ s₂, fun t ht => ?_⟩
  have hA : ∑ i ∈ t, ‖(x : ∀ i, Hi i) i‖ ^ 2 ≤ ε / 2 := by
    have h := hs₁ t (ht.mono_right Finset.subset_union_left)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h.le
  have hB : ∑ i ∈ t, ‖(y : ∀ i, Hi i) i‖ ^ 2 ≤ ε / 2 := by
    have h := hs₂ t (ht.mono_right Finset.subset_union_right)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h.le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq t (fun i => ‖(x : ∀ i, Hi i) i‖)
    (fun i => ‖(y : ∀ i, Hi i) i‖)
  have hbound : ‖∑ i ∈ t, (⟪(x : ∀ i, Hi i) i, (y : ∀ i, Hi i) i⟫ : ℂ)‖
      ≤ ∑ i ∈ t, ‖(x : ∀ i, Hi i) i‖ * ‖(y : ∀ i, Hi i) i‖ :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => norm_inner_le_norm _ _)
  have hS0 : (0 : ℝ) ≤ ∑ i ∈ t, ‖(x : ∀ i, Hi i) i‖ * ‖(y : ∀ i, Hi i) i‖ := by positivity
  have hA0 : (0 : ℝ) ≤ ∑ i ∈ t, ‖(x : ∀ i, Hi i) i‖ ^ 2 := by positivity
  have hB0 : (0 : ℝ) ≤ ∑ i ∈ t, ‖(y : ∀ i, Hi i) i‖ ^ 2 := by positivity
  nlinarith [hcs, hbound, hS0, hA0, hB0, hA, hB, hε]

set_option linter.unusedSectionVars false in
/-- **6II** (`hilb-sum`, cstar.tex:873, Proposition), part 2: `⊕ᵢ Hᵢ` with
the inner product `⟪x, y⟫ = ∑ᵢ ⟪xᵢ, yᵢ⟫` is a Hilbert space (i.e. the
resulting norm is complete).  (Mathlib has this as `lp.completeSpace`, and
the inner product itself as the `InnerProductSpace` instance on `lp Hi 2`;
the proof below is the Proposition's own coordinatewise-limit argument.) -/
theorem hilb_sum_complete : CompleteSpace (lp Hi 2) := by
  -- the Proposition's own proof: a Cauchy sequence converges coordinatewise,
  -- the coordinatewise limit lies in `⊕ᵢ Hᵢ` because its finite partial sums
  -- are bounded, and the convergence is in norm because each finite partial
  -- sum of `∑ᵢ ‖x∞ᵢ - xₙᵢ‖²` is reached through a large `m`
  have hp2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have he : ((2 : ENNReal).toReal) = (2 : ℝ) := by norm_num
  have hrw : ∀ y : ℝ, 0 ≤ y → y ^ ((2 : ENNReal).toReal) = y ^ 2 := by
    intro y hy
    rw [he, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine Metric.complete_of_cauchySeq_tendsto fun x hx => ?_
  -- coordinatewise Cauchy, hence coordinatewise convergent
  have hcoord : ∀ i, CauchySeq fun n => (x n : ∀ i, Hi i) i := by
    intro i
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hx ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm] at h ⊢
    calc ‖(x m : ∀ i, Hi i) i - (x n : ∀ i, Hi i) i‖
        = ‖((x m - x n : lp Hi 2) : ∀ i, Hi i) i‖ := by rw [lp.coeFn_sub]; rfl
      _ ≤ ‖x m - x n‖ := lp.norm_apply_le_norm (by norm_num) _ i
      _ < ε := h
  choose g hg using fun i => cauchySeq_tendsto_of_complete (hcoord i)
  -- the sequence is bounded, so the finite partial sums of `∑ ‖x∞ᵢ‖²` are
  obtain ⟨R, hR0, hR⟩ := cauchySeq_bdd hx
  set C : ℝ := ‖x 0‖ + R with hC
  have hCn : ∀ n, ‖x n‖ ≤ C := by
    intro n
    have h := hR n 0
    rw [dist_eq_norm] at h
    have : ‖x n‖ - ‖x 0‖ ≤ ‖x n - x 0‖ := norm_sub_norm_le _ _
    linarith
  have hsq : ∀ (n : ℕ) (s : Finset ι), ∑ i ∈ s, ‖(x n : ∀ i, Hi i) i‖ ^ 2 ≤ C ^ 2 := by
    intro n s
    have h := lp.sum_rpow_le_norm_rpow hp2 (x n) s
    rw [Finset.sum_congr rfl (fun i _ => hrw _ (norm_nonneg _)), hrw _ (norm_nonneg _)] at h
    have h2 : ‖x n‖ ^ 2 ≤ C ^ 2 := by
      have := hCn n
      nlinarith [norm_nonneg (x n)]
    linarith
  have hmem : Memℓp g 2 := by
    refine memℓp_gen' (C := C ^ 2) fun s => ?_
    rw [Finset.sum_congr rfl (fun i _ => hrw _ (norm_nonneg _))]
    have htend : Filter.Tendsto
        (fun n => ∑ i ∈ s, ‖(x n : ∀ i, Hi i) i‖ ^ 2) Filter.atTop
        (nhds (∑ i ∈ s, ‖g i‖ ^ 2)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      exact (((hg i).norm).pow 2)
    exact le_of_tendsto htend (Filter.Eventually.of_forall fun n => hsq n s)
  refine ⟨⟨g, hmem⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hx (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  set y : lp Hi 2 := ⟨g, hmem⟩ with hy
  have hdiff : ∀ i, ((x n - y : lp Hi 2) : ∀ i, Hi i) i = (x n : ∀ i, Hi i) i - g i := by
    intro i
    rw [lp.coeFn_sub]
    rfl
  have hpartial : ∀ s : Finset ι,
      ∑ i ∈ s, ‖(x n : ∀ i, Hi i) i - g i‖ ^ 2 ≤ (ε / 2) ^ 2 := by
    intro s
    have htend : Filter.Tendsto
        (fun m => ∑ i ∈ s, ‖(x n : ∀ i, Hi i) i - (x m : ∀ i, Hi i) i‖ ^ 2)
        Filter.atTop (nhds (∑ i ∈ s, ‖(x n : ∀ i, Hi i) i - g i‖ ^ 2)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      exact ((tendsto_const_nhds.sub (hg i)).norm.pow 2)
    refine le_of_tendsto htend (Filter.eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have hnm : ‖x n - x m‖ < ε / 2 := by
      have := hN n hn m hm
      rwa [dist_eq_norm] at this
    have h1 : ∑ i ∈ s, ‖(x n : ∀ i, Hi i) i - (x m : ∀ i, Hi i) i‖ ^ 2 ≤ ‖x n - x m‖ ^ 2 := by
      have h := lp.sum_rpow_le_norm_rpow hp2 (x n - x m) s
      rw [Finset.sum_congr rfl (fun i _ => hrw _ (norm_nonneg _)), hrw _ (norm_nonneg _)] at h
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lp.coeFn_sub]
      rfl
    nlinarith [norm_nonneg (x n - x m), hε]
  have hsummable : Summable fun i => ‖((x n - y : lp Hi 2) : ∀ i, Hi i) i‖ ^ 2 := by
    have h := (lp.memℓp (x n - y)).summable hp2
    refine h.congr fun i => ?_
    exact hrw _ (norm_nonneg _)
  have hle : ‖x n - y‖ ^ 2 ≤ (ε / 2) ^ 2 := by
    have hnorm : ‖x n - y‖ ^ 2 = ∑' i, ‖((x n - y : lp Hi 2) : ∀ i, Hi i) i‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum hp2 (x n - y)
      rw [hrw _ (norm_nonneg _)] at h
      rw [h]
      exact tsum_congr fun i => hrw _ (norm_nonneg _)
    rw [hnorm]
    refine hsummable.tsum_le_of_sum_le fun s => ?_
    refine le_trans (le_of_eq ?_) (hpartial s)
    exact Finset.sum_congr rfl fun i _ => by rw [hdiff i]
  have : ‖x n - y‖ ≤ ε / 2 := by nlinarith [norm_nonneg (x n - y), hε]
  linarith


end HilbSum

/-! ## Parsec 70: self-adjoint elements

**7II** (cstar.tex:989, Definition): `a` is *self-adjoint* when `a* = a`
(Mathlib: `IsSelfAdjoint a`, and `selfAdjoint 𝒜` for the set); the *real*
and *imaginary parts* are `Re a = (a + a*)/2` and `Im a = (a - a*)/2i`
(Mathlib: `realPart`/`imaginaryPart`, notation `ℜ`/`ℑ` in the
`ComplexStarModule` scope, valued in `selfAdjoint 𝒜`). -/

section Involution

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 1:
`ℜa` and `ℑa` are self-adjoint (automatic here from their type) and
`a = ℜa + i·ℑa`. -/
theorem cstar_involution_basic_1 (a : 𝒜) :
    a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) := by
  -- the solution's computation: `2(ℜa + i·ℑa) = (a + a*) + (a - a*) = 2a`
  rw [realPart_apply_coe, imaginaryPart_apply_coe, smul_smul]
  rw [show Complex.I * -Complex.I = 1 by simp, one_smul, ← smul_add,
    show a + star a + (a - star a) = (2 : ℝ) • a by rw [two_smul]; abel,
    smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 2:
if `a = b + i·c` with `b, c` self-adjoint then `b = ℜa` and `c = ℑa`. -/
theorem cstar_involution_basic_2 (a b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) (h : a = b + Complex.I • c) :
    b = (ℜ a : 𝒜) ∧ c = (ℑ a : 𝒜) := by
  -- the solution: `a* = b - ic`, so `2ℜa = a + a* = 2b` and `2iℑa = a - a* = 2ic`
  have hstar : star a = b - Complex.I • c := by
    rw [h, star_add, star_smul, hb.star_eq, hc.star_eq]
    simp [sub_eq_add_neg]
  constructor
  · rw [realPart_apply_coe, hstar, h,
      show b + Complex.I • c + (b - Complex.I • c) = (2 : ℝ) • b by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  · rw [imaginaryPart_apply_coe, hstar, h,
      show b + Complex.I • c - (b - Complex.I • c) = (2 : ℝ) • (Complex.I • c) by
        rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul, smul_smul,
      show -Complex.I * Complex.I = 1 by simp, one_smul]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 3:
`ℜ(a*) = ℜa` and `ℑ(a*) = -ℑa`. -/
theorem cstar_involution_basic_3 (a : 𝒜) :
    (ℜ (star a) : 𝒜) = (ℜ a : 𝒜) ∧ (ℑ (star a) : 𝒜) = -(ℑ a : 𝒜) :=
  by
    -- the solution deduces this from parts 1 and 2: `a* = ℜa + i·(-ℑa)`
    have hstar : star a = (ℜ a : 𝒜) + Complex.I • (-(ℑ a : 𝒜)) := by
      conv_lhs => rw [cstar_involution_basic_1 a]
      rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
      simp
    obtain ⟨h1, h2⟩ := cstar_involution_basic_2 (star a) (ℜ a : 𝒜) (-(ℑ a : 𝒜))
      (ℜ a).property ((ℑ a).property.neg) hstar
    exact ⟨h1.symm, h2.symm⟩

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 4:
`a` is self-adjoint iff `ℜa = a` iff `ℑa = 0`. -/
theorem cstar_involution_basic_4 (a : 𝒜) :
    (IsSelfAdjoint a ↔ (ℜ a : 𝒜) = a) ∧ (IsSelfAdjoint a ↔ (ℑ a : 𝒜) = 0) := by
  -- the solution's chain: `a = a*` iff `a + a* = 2a` iff `ℜa = a`; and
  -- `a = a*` iff `a - a* = 0` iff `ℑa = 0`
  have hsum : (ℜ a : 𝒜) = a ↔ a + star a = (2 : ℝ) • a := by
    rw [realPart_apply_coe]
    constructor
    · intro h
      have h2 := congrArg (fun z : 𝒜 => (2 : ℝ) • z) h
      simpa [smul_smul] using h2
    · intro h
      rw [h, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  have hdif : (ℑ a : 𝒜) = 0 ↔ a - star a = 0 := by
    rw [imaginaryPart_apply_coe]
    constructor
    · intro h
      have h2 : ((2 : ℝ)⁻¹ • (a - star a)) = 0 := by
        have := congrArg (fun z : 𝒜 => Complex.I • z) h
        simpa [smul_smul] using this
      have := congrArg (fun z : 𝒜 => (2 : ℝ) • z) h2
      simpa [smul_smul] using this
    · intro h
      rw [h]
      simp
  refine ⟨⟨fun ha => ?_, fun ha => ?_⟩, ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · refine hsum.mpr ?_
    rw [ha.star_eq, two_smul]
  · have h := hsum.mp ha
    rw [two_smul] at h
    exact add_left_cancel h
  · refine hdif.mpr ?_
    rw [ha.star_eq, sub_self]
  · have h := hdif.mp ha
    exact (sub_eq_zero.mp h).symm

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 5:
`a ↦ ℜa` and `a ↦ ℑa` are ℝ-linear maps `𝒜 → 𝒜`, i.e. additive and
ℝ-homogeneous.  (In Mathlib they are bundled as `𝒜 →ₗ[ℝ] selfAdjoint 𝒜`;
the proof below is the solution's own reason instead — `(·)*` is ℝ-linear,
so the defining formulas `ℜa = ½(a + a*)`, `ℑa = -i·½(a - a*)` are.) -/
theorem cstar_involution_basic_5 (a b : 𝒜) (r : ℝ) :
    (ℜ (a + b) : 𝒜) = (ℜ a : 𝒜) + (ℜ b : 𝒜) ∧
      (ℑ (a + b) : 𝒜) = (ℑ a : 𝒜) + (ℑ b : 𝒜) ∧
      (ℜ (r • a) : 𝒜) = r • (ℜ a : 𝒜) ∧
      (ℑ (r • a) : 𝒜) = r • (ℑ a : 𝒜) := by
  -- the solution's reason: `(·)*` is ℝ-linear, so the formulas
  -- `ℜa = ½(a + a*)` and `ℑa = -i·½(a - a*)` are ℝ-linear in `a`
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [realPart_apply_coe, realPart_apply_coe, realPart_apply_coe, star_add]
    module
  · rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, imaginaryPart_apply_coe,
      star_add]
    module
  · rw [realPart_apply_coe, realPart_apply_coe, star_smul, star_trivial]
    module
  · rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_smul, star_trivial]
    module

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 6:
`ℑa = -ℜ(ia)` and `ℜa = ℑ(ia)`. -/
theorem cstar_involution_basic_6 (a : 𝒜) :
    (ℑ a : 𝒜) = -(ℜ (Complex.I • a) : 𝒜) ∧
      (ℜ a : 𝒜) = (ℑ (Complex.I • a) : 𝒜) := by
  -- the solution: apply part 2 to `i·a = i(ℜa + i·ℑa) = -ℑa + i·ℜa`
  have h : Complex.I • a = -(ℑ a : 𝒜) + Complex.I • (ℜ a : 𝒜) := by
    conv_lhs => rw [cstar_involution_basic_1 a]
    rw [smul_add, smul_smul, show Complex.I * Complex.I = -1 by simp]
    module
  obtain ⟨h1, h2⟩ := cstar_involution_basic_2 (Complex.I • a) (-(ℑ a : 𝒜)) (ℜ a : 𝒜)
    ((ℑ a).property.neg) (ℜ a).property h
  exact ⟨by rw [← h1, neg_neg], h2⟩

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 7:
`a* a` is self-adjoint, and
`a* a = (ℜa)² + (ℑa)² + i(ℜa·ℑa - ℑa·ℜa)`. -/
theorem cstar_involution_basic_7 (a : 𝒜) :
    IsSelfAdjoint (star a * a) ∧
      star a * a = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 +
        Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) :=
  by
    refine ⟨IsSelfAdjoint.star_mul_self a, ?_⟩
    have ha : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) := (realPart_add_I_smul_imaginaryPart a).symm
    have has : star a = (ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜) := by
      conv_lhs => rw [ha]
      rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
      simp [sub_eq_add_neg]
    calc star a * a
        = ((ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜)) * ((ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜)) := by
          rw [← has, ← ha]
      _ = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 +
            Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
          rw [sub_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
            mul_smul_comm, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_sub, sq, sq]
          abel

/-- The computation of the solution to **7III**.8 (asols.tex,
`parsec-70.30`(8)), instantiated at the solution's own witnesses: for
linearly independent `x`, `y` with `⟪x,y⟫ ≠ 0`, the operators
`b := |x⟩⟨x|` and `c := |y⟩⟨y|` do not commute, "because then
`|⟪x,y⟫|² x = bcx = cbx = ⟪y,x⟫‖x‖² y`, contradicting the linear
independence of `x` and `y`".  Here `x = e₀` and `y = e₀ + e₁` in `ℂ²`,
so `b = !![1,0;0,0]`, `c = !![1,1;1,1]`, and the two scalars
`|⟪x,y⟫|²` and `⟪y,x⟫‖x‖²` are both `1`.

Used both by **7III**.8 `cstar_involution_basic_8` and — through point 10,
`cstar_involution_basic_10`, exactly as the solution to **9X**.3 does — by
`cstar_positive_3`. -/
private theorem ketbra_e0_e0e1_not_commute :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1]
      ≠ !![1, 1; 1, 1] * !![1, 0; 0, 0] :=
  by
    set x : Fin 2 → ℂ := ![1, 0] with hx
    set y : Fin 2 → ℂ := ![1, 1] with hy
    -- `x` and `y` are linearly independent
    have hind : LinearIndependent ℂ ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrFun hst 1
      have h0 := congrFun hst 0
      simp [hx, hy] at h0 h1
      refine ⟨?_, h1⟩
      simp [h1] at h0
      simpa using h0
    intro hcomm
    -- `bcx = |⟪x,y⟫|² x` and `cbx = ⟪y,x⟫ ‖x‖² y`, both scalars being `1`
    have hbc : Matrix.mulVec ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1]) x
        = (1 : ℂ) • x := by
      ext i
      fin_cases i <;>
        simp [hx, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
    have hcb : Matrix.mulVec ((!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0]) x
        = (1 : ℂ) • y := by
      ext i
      fin_cases i <;>
        simp [hx, hy, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
    -- so `1 • x = 1 • y`, contradicting the linear independence of `x` and `y`
    have hkey : (1 : ℂ) • x = (1 : ℂ) • y := by rw [← hbc, ← hcb, hcomm]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hind) 1 (-1) (by rw [hkey]; module)).1

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 8:
real and imaginary part need not commute: an example in the 2×2 matrices. -/
theorem cstar_involution_basic_8 :
    ∃ a : Matrix (Fin 2) (Fin 2) ℂ,
      (ℜ a : Matrix (Fin 2) (Fin 2) ℂ) * (ℑ a : Matrix (Fin 2) (Fin 2) ℂ) ≠
        (ℑ a : Matrix (Fin 2) (Fin 2) ℂ) * (ℜ a : Matrix (Fin 2) (Fin 2) ℂ) :=
  by
    -- The solution's own reduction (asols.tex, `parsec-70.30`(8)): "It suffices
    -- to find self-adjoint elements `b` and `c` of some C*-algebra `𝒜` with
    -- `bc ≠ cb`, because then `a := b + ic` will do the job."  Its witnesses are
    -- `b = |x⟩⟨x|` and `c = |y⟩⟨y|` for linearly independent `x, y` with
    -- `⟪x,y⟫ ≠ 0`; here `x = e₀` and `y = e₀ + e₁`, for which
    -- `|x⟩⟨x| = !![1,0;0,0]` and `|y⟩⟨y| = !![1,1;1,1]` — the same pair as in
    -- **9X**.3 `cstar_positive_3`.  That they do not commute is the solution's
    -- own linear-independence argument, in `ketbra_e0_e0e1_not_commute` above.
    have hb : IsSelfAdjoint (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      show star _ = _
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hc : IsSelfAdjoint (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
      show star _ = _
      ext i j; fin_cases i <;> fin_cases j <;> simp
    refine ⟨(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        + Complex.I • (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
    rw [map_add, map_add, realPart_I_smul, imaginaryPart_I_smul,
      hb.imaginaryPart, hc.imaginaryPart]
    simp only [neg_zero, add_zero, zero_add]
    rw [hb.coe_realPart, hc.coe_realPart]
    exact ketbra_e0_e0e1_not_commute

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 9:
`a* a + a a* = 2((ℜa)² + (ℑa)²)`. -/
theorem cstar_involution_basic_9 (a : 𝒜) :
    star a * a + a * star a = 2 * ((ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2) :=
  by
    -- the solution's "combine point 3 and point 7": point 7 at `a*` computes
    -- `a a*`, and point 3 turns `ℜ(a*), ℑ(a*)` into `ℜa, -ℑa`
    have h7 := (cstar_involution_basic_7 a).2
    have h7' := (cstar_involution_basic_7 (star a)).2
    obtain ⟨hre, him⟩ := cstar_involution_basic_3 a
    rw [star_star, hre, him] at h7'
    rw [h7, h7']
    have e1 : (-(ℑ a : 𝒜)) ^ 2 = (ℑ a : 𝒜) ^ 2 := by noncomm_ring
    have e2 : (ℜ a : 𝒜) * (-(ℑ a : 𝒜)) - (-(ℑ a : 𝒜)) * (ℜ a : 𝒜)
        = -((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by noncomm_ring
    rw [e1, e2, smul_neg, two_mul]
    abel

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 10:
for self-adjoint `b, c` the product `bc` is self-adjoint iff `bc = cb`. -/
theorem cstar_involution_basic_10 (b c : 𝒜) (hb : IsSelfAdjoint b)
    (hc : IsSelfAdjoint c) : IsSelfAdjoint (b * c) ↔ b * c = c * b :=
  by
    rw [isSelfAdjoint_iff, star_mul, hb.star_eq, hc.star_eq]
    exact eq_comm

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 11:
`‖a*‖ = ‖a‖`, by the exercise's own hint: `‖a‖² = ‖a* a‖ ≤ ‖a*‖ ‖a‖` gives
`‖a‖ ≤ ‖a*‖`, and applying that to `a*` gives the other inequality. -/
theorem cstar_involution_basic_11 (a : 𝒜) : ‖star a‖ = ‖a‖ :=
  by
    have key : ∀ b : 𝒜, ‖b‖ ≤ ‖star b‖ := by
      intro b
      rcases eq_or_lt_of_le (norm_nonneg b) with h0 | h0
      · rw [← h0]
        exact norm_nonneg _
      · have h1 : ‖star b * b‖ = ‖b‖ * ‖b‖ := CStarRing.norm_star_mul_self
        have h2 : ‖star b * b‖ ≤ ‖star b‖ * ‖b‖ := norm_mul_le _ _
        rw [h1] at h2
        exact le_of_mul_le_mul_right (by linarith) h0
    have h := key (star a)
    rw [star_star] at h
    exact le_antisymm h (key a)

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 12:
`‖ℜa‖ ≤ ‖a‖` and `‖ℑa‖ ≤ ‖a‖`. -/
theorem cstar_involution_basic_12 (a : 𝒜) :
    ‖(ℜ a : 𝒜)‖ ≤ ‖a‖ ∧ ‖(ℑ a : 𝒜)‖ ≤ ‖a‖ :=
  by
    -- the solution's estimate: `‖½(a ± a*)‖ ≤ ½(‖a‖ + ‖a*‖) = ‖a‖`, by part 11
    have hstar : ‖star a‖ = ‖a‖ := cstar_involution_basic_11 a
    constructor
    · rw [realPart_apply_coe, norm_smul, Real.norm_eq_abs]
      have := norm_add_le a (star a)
      rw [hstar] at this
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      linarith
    · rw [imaginaryPart_apply_coe, norm_smul, norm_smul, Real.norm_eq_abs, norm_neg,
        Complex.norm_I, one_mul]
      have := norm_sub_le a (star a)
      rw [hstar] at this
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      linarith

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 13:
`‖a²‖ = ‖a‖²` for self-adjoint `a`. -/
theorem cstar_involution_basic_13 (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a ^ 2‖ = ‖a‖ ^ 2 :=
  by
    have h : a ^ 2 = star a * a := by rw [ha.star_eq, sq]
    rw [h, CStarRing.norm_star_mul_self, sq]

/-- **7III** (`cstar-involution-basic`, cstar.tex:1007, Exercise), part 13
(counterexample): `‖a²‖ ≠ ‖a‖²` may occur for non-self-adjoint `a`
(e.g. `[[0,1],[0,0]]` as an operator on ℂ²). -/
theorem cstar_involution_basic_13' :
    ∃ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      ‖T ^ 2‖ ≠ ‖T‖ ^ 2 :=
  by
    refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
    have hsq : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = 0 := by
      rw [pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ]
    have h1 : (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) ^ 2 = 0 := by
      rw [← map_pow, hsq, map_zero]
    have h2 : Matrix.toEuclideanCLM (𝕜 := ℂ)
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
      intro hc
      have hM : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
        have := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm hc
        simpa using this
      have := congrFun (congrFun hM 0) 1
      simp at this
    rw [h1, norm_zero]
    intro hc
    exact h2 (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hc.symm))

/-! ## Parsec 80: scalars in a C*-algebra

**8I** (cstar.tex:1060, Notation): for `λ ∈ ℂ` we write `λ` also for the
element `λ·1` of `𝒜`; in Lean this is `algebraMap ℂ 𝒜 λ`. -/

/-- **8II** (cstar.tex:1071, Exercise), part 1: in the trivial C*-algebra
`{0}` we have `‖1‖ = 0 ≠ 1`. -/
theorem scalar_norm_1 [Subsingleton 𝒜] : ‖(1 : 𝒜)‖ = 0 :=
  by
    rw [Subsingleton.elim (1 : 𝒜) 0, norm_zero]

/-- Auxiliary for **8II**: `‖1‖ = ‖1*1‖ = ‖1‖²`, so `‖1‖` is either `1` or
`0`.  This is the observation solution `parsec-80.20` makes once and then
uses in both part 2 and part 3, in place of a case split on whether `𝒜` is
trivial. -/
private theorem norm_one_eq_one_or_zero : ‖(1 : 𝒜)‖ = 1 ∨ ‖(1 : 𝒜)‖ = 0 := by
  have h1 : ‖(1 : 𝒜)‖ * ‖(1 : 𝒜)‖ = ‖(1 : 𝒜)‖ := by
    rw [← CStarRing.norm_star_mul_self (x := (1 : 𝒜)), star_one, mul_one]
  rcases mul_eq_zero.mp (show ‖(1 : 𝒜)‖ * (‖(1 : 𝒜)‖ - 1) = 0 by nlinarith) with h | h
  · exact Or.inr h
  · exact Or.inl (by linarith)

/-- **8II** (cstar.tex:1071, Exercise), part 2: `‖λ·1‖ ≤ |λ|` for every
scalar `λ ∈ ℂ`. -/
theorem scalar_norm_2 (z : ℂ) : ‖algebraMap ℂ 𝒜 z‖ ≤ ‖z‖ :=
  by
    have hle : ‖(1 : 𝒜)‖ ≤ 1 := by
      rcases norm_one_eq_one_or_zero (𝒜 := 𝒜) with h | h
      · exact le_of_eq h
      · rw [h]; norm_num
    rw [Algebra.algebraMap_eq_smul_one, norm_smul]
    calc ‖z‖ * ‖(1 : 𝒜)‖ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg z)
      _ = ‖z‖ := mul_one _

/-- **8II** (cstar.tex:1071, Exercise), part 3: `‖λ·1‖ = |λ|` holds when
both sides are interpreted as elements of `𝒜`. -/
theorem scalar_norm_3 (z : ℂ) :
    algebraMap ℂ 𝒜 (‖algebraMap ℂ 𝒜 z‖ : ℂ) = algebraMap ℂ 𝒜 (‖z‖ : ℂ) :=
  by
    -- the solution's reduction: it suffices that `‖1‖·1 = 1`, which holds in
    -- both cases of `norm_one_eq_one_or_zero`
    have hkey : algebraMap ℂ 𝒜 ((‖(1 : 𝒜)‖ : ℝ) : ℂ) = 1 := by
      rcases norm_one_eq_one_or_zero (𝒜 := 𝒜) with h | h
      · rw [h]; simp
      · have h0 : (1 : 𝒜) = 0 := norm_eq_zero.mp h
        rw [h, Complex.ofReal_zero, map_zero, h0]
    have hnorm : ‖algebraMap ℂ 𝒜 z‖ = ‖z‖ * ‖(1 : 𝒜)‖ := by
      rw [Algebra.algebraMap_eq_smul_one, norm_smul]
    rw [hnorm, Complex.ofReal_mul, map_mul, hkey, mul_one]

end Involution

/-! ## Parsec 90: positive elements -/

section CxPositive

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **9II** (`cx-positive`, cstar.tex:1106, Exercise): for a self-adjoint
`f ∈ C(X)`, `X` compact Hausdorff, the following are equivalent:
(1) `f(X) ⊆ [0,∞)`; (2) `f = g²` for some self-adjoint `g`;
(3) `f = g* g` for some `g`; (4) `‖f - t‖ ≤ t` for some `t ∈ ℝ`;
(5) `‖f - t‖ ≤ t` for all `t ≥ ‖f‖/2`. -/
theorem cx_positive (f : C(X, ℂ)) (hf : IsSelfAdjoint f) :
    List.TFAE [
      ∀ x, 0 ≤ f x,
      ∃ g : C(X, ℂ), IsSelfAdjoint g ∧ f = g ^ 2,
      ∃ g : C(X, ℂ), f = star g * g,
      ∃ t : ℝ, ‖f - algebraMap ℂ C(X, ℂ) (t : ℂ)‖ ≤ t,
      ∀ t : ℝ, ‖f‖ / 2 ≤ t → ‖f - algebraMap ℂ C(X, ℂ) (t : ℂ)‖ ≤ t] :=
  by
    have hstar : ∀ x, (starRingEnd ℂ) (f x) = f x := by
      intro x
      have h := hf.star_eq
      have := congrArg (fun g : C(X, ℂ) => g x) h
      simpa using this
    have him : ∀ x, (f x).im = 0 := by
      intro x
      have h := hstar x
      rw [Complex.ext_iff] at h
      have := h.2
      simp only [Complex.conj_im] at this
      linarith
    tfae_have 1 → 2 := by
      intro h1
      have hcont : Continuous fun x => ((Real.sqrt (f x).re : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp
          (Real.continuous_sqrt.comp (Complex.continuous_re.comp f.continuous))
      refine ⟨⟨_, hcont⟩, ?_, ?_⟩
      · ext x
        simp
      · ext x
        have hre : 0 ≤ (f x).re := (Complex.nonneg_iff.mp (h1 x)).1
        have hsq : ((Real.sqrt (f x).re : ℝ) : ℂ) ^ 2 = ((f x).re : ℂ) := by
          rw [← Complex.ofReal_pow, Real.sq_sqrt hre]
        have hfx : f x = ((f x).re : ℂ) := by
          apply Complex.ext <;> simp [him x]
        simp only [ContinuousMap.pow_apply, ContinuousMap.coe_mk]
        rw [hsq]
        exact hfx
    tfae_have 2 → 3 := by
      rintro ⟨g, hg, rfl⟩
      exact ⟨g, by rw [hg.star_eq, sq]⟩
    tfae_have 3 → 1 := by
      rintro ⟨g, rfl⟩ x
      have hx : (star g * g) x = (starRingEnd ℂ) (g x) * g x := by simp
      rw [hx, Complex.conj_mul', ← Complex.ofReal_pow]
      simp [Complex.nonneg_iff]
    tfae_have 1 → 5 := by
      intro h1 t ht
      have ht0 : 0 ≤ t := le_trans (by positivity) ht
      rw [ContinuousMap.norm_le _ ht0]
      intro x
      have hre : 0 ≤ (f x).re := (Complex.nonneg_iff.mp (h1 x)).1
      have hfx : f x = ((f x).re : ℂ) := by
        apply Complex.ext <;> simp [him x]
      have hle : (f x).re ≤ ‖f‖ := by
        have h := ContinuousMap.norm_coe_le_norm f x
        rw [hfx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre] at h
        exact h
      have hval : (f - algebraMap ℂ C(X, ℂ) (t : ℂ)) x = f x - (t : ℂ) := by simp
      rw [hval, hfx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    tfae_have 5 → 4 := fun h5 => ⟨‖f‖ / 2, h5 _ le_rfl⟩
    tfae_have 4 → 1 := by
      rintro ⟨t, ht⟩ x
      have hpt : ‖(f - algebraMap ℂ C(X, ℂ) (t : ℂ)) x‖ ≤ t :=
        le_trans (ContinuousMap.norm_coe_le_norm _ x) ht
      have hval : (f - algebraMap ℂ C(X, ℂ) (t : ℂ)) x = f x - (t : ℂ) := by simp
      rw [hval] at hpt
      have hfx : f x = ((f x).re : ℂ) := by
        apply Complex.ext <;> simp [him x]
      rw [hfx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hpt
      rw [Complex.nonneg_iff]
      exact ⟨by linarith [(abs_le.mp hpt).1], (him x).symm⟩
    tfae_finish

/-- The key step of the solution to **9III** (asols `parsec-90.30`): an
`f ∈ C(X,ℂ)` is invertible precisely when it is nowhere zero, the inverse
being given pointwise by `x ↦ f x⁻¹`.

Mathlib has this as `ContinuousMap.isUnit_iff_forall_ne_zero`, but reaches
it by a different route from the solution's — `ContinuousMap.unitsLift`
together with `NormedRing.inverse_continuousAt`, the continuity of inversion
in a Banach algebra, four declarations and some forty lines — whereas the
solution says only "with inverse given by `f⁻¹(x) = f(x)⁻¹`", which over `ℂ`
is `Continuous.inv₀`.  The proof below is the solution's own. -/
theorem cx_isUnit_iff_forall_ne_zero (f : C(X, ℂ)) : IsUnit f ↔ ∀ x, f x ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ x hx
    have h := ContinuousMap.congr_fun u.mul_inv x
    simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply] at h
    rw [hx, zero_mul] at h
    exact zero_ne_one h
  · intro h
    exact ⟨⟨f, ⟨(⇑f)⁻¹, f.continuous.inv₀ h⟩,
      by ext x; simpa using mul_inv_cancel₀ (h x),
      by ext x; simpa using inv_mul_cancel₀ (h x)⟩, rfl⟩

/-- **9III** (cstar.tex:1123, Exercise): `λ ∈ f(X)` iff `f - λ` is not
invertible in `C(X)`. -/
theorem cx_mem_range_iff_not_isUnit (f : C(X, ℂ)) (z : ℂ) :
    (∃ x, f x = z) ↔ ¬IsUnit (f - algebraMap ℂ C(X, ℂ) z) :=
  by
    rw [cx_isUnit_iff_forall_ne_zero]
    simp only [not_forall, not_not, ContinuousMap.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa using hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simpa using hx⟩

end CxPositive

section Positive

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Auxiliary: the two ways of viewing a real scalar as an element of a
C*-algebra agree. -/
theorem algebraMap_real_eq (r : ℝ) : algebraMap ℝ 𝒜 r = algebraMap ℂ 𝒜 (r : ℂ) := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ 𝒜, Complex.coe_algebraMap]

/-- Auxiliary: a real scalar is a self-adjoint element of a C*-algebra. -/
theorem isSelfAdjoint_algebraMap_ofReal (r : ℝ) :
    IsSelfAdjoint (algebraMap ℂ 𝒜 (r : ℂ)) := by
  rw [← algebraMap_real_eq]
  exact IsSelfAdjoint.algebraMap 𝒜 (IsSelfAdjoint.all r)

/-- Auxiliary: a nonnegative real scalar is a positive element.

This lemma sits *below* the **9IV** bridge `cstar_positive_def` (it is used,
through `algebraMap_ofReal_mono`, in the proof of **17VI**.3a), so it cannot
be read off the thesis's `‖r - r‖ ≤ r`; `√r·1` is its own square root. -/
theorem algebraMap_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) :
    (0 : 𝒜) ≤ algebraMap ℂ 𝒜 (r : ℂ) := by
  have he : algebraMap ℂ 𝒜 (r : ℂ)
      = star (algebraMap ℂ 𝒜 (Real.sqrt r : ℂ)) * algebraMap ℂ 𝒜 (Real.sqrt r : ℂ) := by
    rw [← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal, ← map_mul,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  rw [he]
  exact star_mul_self_nonneg _

/-- Auxiliary: `r ↦ r·1` is monotone. -/
theorem algebraMap_ofReal_mono {s t : ℝ} (h : s ≤ t) :
    algebraMap ℂ 𝒜 (s : ℂ) ≤ algebraMap ℂ 𝒜 (t : ℂ) := by
  rw [← sub_nonneg, ← map_sub, ← Complex.ofReal_sub]
  exact algebraMap_ofReal_nonneg (by linarith)

/-- Auxiliary (**17VI**.3a): for a self-adjoint element, `‖a‖ ≤ r` iff
`-r ≤ a ≤ r`.

**This is the parsec-90 order bridge, and it is the one place in parsecs
20–220 where the development enters Mathlib's continuous functional
calculus.**  Everything in the `Positive` section below — 9IV, 9VII, 9X.1,
9X.2, 9X.4, 9X.5d, 9X.5e — and 10IV with it funnels through this lemma
alone; 9X.5b (`OrderClosedTopology`) and 9X.3 (the order on `B(ℂ²)`, forced by
its statement) are the only other entries.

It is *not* repairable here.  The thesis proves it at parsec 170 (asols
`parsec-170.60`(3)): `‖a‖ ≤ λ` iff `|μ| ≤ λ` for all `μ ∈ spec(a)` — by
**16II** `norm_spectrum` — iff `spec(λ-a)`, `spec(λ+a) ⊆ [0,∞)` iff (**17V**)
`λ-a` and `λ+a` are positive.  16II rests on parsecs 120–150, and reading
"positive" as Mathlib's `0 ≤` is **25I**, which rests on the square root
(parsec 230); both live in `A/CStar/Positive.lean`, which *imports this file*.
The thesis's own, CFC-free proof of this very statement is already in the tree
there, as `positive_basic_2_3a`.  Undoing the knot means moving this section
below parsec 250, which is a statement-level decision, not a proof one. -/
theorem norm_le_iff_neg_algebraMap_le {a : 𝒜} (ha : IsSelfAdjoint a) {r : ℝ}
    (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ (-(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)) := by
  have hle : a ≤ algebraMap ℂ 𝒜 (‖a‖ : ℂ) := by
    rw [← algebraMap_real_eq]
    exact ha.le_algebraMap_norm_self
  have hge : -(algebraMap ℂ 𝒜 (‖a‖ : ℂ)) ≤ a := by
    rw [← algebraMap_real_eq]
    exact ha.neg_algebraMap_norm_le_self
  constructor
  · intro h
    exact ⟨le_trans (neg_le_neg (algebraMap_ofReal_mono h)) hge,
      le_trans hle (algebraMap_ofReal_mono h)⟩
  · rintro ⟨h1, h2⟩
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · rw [Subsingleton.elim a 0, norm_zero]
      exact hr
    · have h2' : a ≤ algebraMap ℝ 𝒜 r := by
        rw [algebraMap_real_eq]
        exact h2
      have h1' : algebraMap ℝ 𝒜 (-r) ≤ a := by
        rw [algebraMap_real_eq, Complex.ofReal_neg, map_neg]
        exact h1
      rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := a) ha with hmem | hmem
      · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (a := a) ha).mp h2' ‖a‖ hmem
      · have h3 := (algebraMap_le_iff_le_spectrum (R := ℝ) (a := a) ha).mp h1' (-‖a‖) hmem
        linarith

/-- **9IV** (`cstar-positive-def`, cstar.tex:1130, Definition): a
self-adjoint `a` is *positive* when `‖a - t‖ ≤ t` for some `t ∈ ℝ`, and
`a ≤ b` means `b - a` is positive.  In this formalization the canonical
order of Mathlib's `[PartialOrder 𝒜] [StarOrderedRing 𝒜]` is used instead;
this lemma records that the two definitions agree.
(**9IVa**, cstar.tex:1143: the interval `[a,b]` is `Set.Icc a b`.) -/
theorem cstar_positive_def (a : 𝒜) (ha : IsSelfAdjoint a) :
    0 ≤ a ↔ ∃ t : ℝ, ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t :=
  by
    constructor
    · intro h
      refine ⟨‖a‖, ?_⟩
      have hsa : IsSelfAdjoint (a - algebraMap ℂ 𝒜 (‖a‖ : ℂ)) :=
        ha.sub (isSelfAdjoint_algebraMap_ofReal ‖a‖)
      rw [norm_le_iff_neg_algebraMap_le hsa (norm_nonneg a)]
      constructor
      · rw [le_sub_iff_add_le, neg_add_cancel]
        exact h
      · rw [sub_le_iff_le_add]
        refine le_trans ?_ (le_add_of_nonneg_left (algebraMap_ofReal_nonneg (norm_nonneg a)))
        -- `a ≤ ‖a‖` is again the case `r = ‖a‖` of **17VI**.3a, not a second
        -- appeal to Mathlib's `le_algebraMap_norm_self`
        exact ((norm_le_iff_neg_algebraMap_le ha (norm_nonneg a)).mp le_rfl).2
    · rintro ⟨t, ht⟩
      have ht0 : 0 ≤ t := le_trans (norm_nonneg _) ht
      have hsa : IsSelfAdjoint (a - algebraMap ℂ 𝒜 (t : ℂ)) :=
        ha.sub (isSelfAdjoint_algebraMap_ofReal t)
      have hkey := ((norm_le_iff_neg_algebraMap_le hsa ht0).mp ht).1
      rwa [le_sub_iff_add_le, neg_add_cancel] at hkey

/-- Auxiliary form of the scalar clause of **9X**.1 (`cstar-positive`,
cstar.tex:1209, Exercise, part 1): a nonnegative real multiple of a positive
element is positive.

This is the solution's own argument (asols.tex, `parsec-90.100`(1)), read
through the bridge **9IV** `cstar_positive_def`: pick `t ∈ ℝ` with
`‖a - t‖ ≤ t`; then `r a` is self-adjoint and
`‖r a - r t‖ = r ‖a - t‖ ≤ r t`, so `r a` is positive.  (`cstar_positive_1`
below states the same clause under its thesis name.) -/
theorem ofReal_smul_nonneg {a : 𝒜} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ (r : ℂ) • a := by
  have hasa : IsSelfAdjoint a := .of_nonneg ha
  have hc : IsSelfAdjoint ((r : ℝ) : ℂ) := Complex.conj_ofReal r
  have hrsa : IsSelfAdjoint ((r : ℂ) • a) := hc.smul hasa
  obtain ⟨t, ht⟩ := (cstar_positive_def a hasa).mp ha
  refine (cstar_positive_def _ hrsa).mpr ⟨r * t, ?_⟩
  have he : (r : ℂ) • a - algebraMap ℂ 𝒜 ((r * t : ℝ) : ℂ)
      = (r : ℂ) • (a - algebraMap ℂ 𝒜 (t : ℂ)) := by
    rw [smul_sub]
    congr 1
    rw [Algebra.smul_def, ← map_mul, Complex.ofReal_mul]
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left ht hr

/-! **9VI** (cstar.tex:1180, Example): a bounded operator `T` on a Hilbert
space is positive iff `⟪x, Tx⟫ ≥ 0` for all `x` — stated at **25V**. -/

/-- **9VII** (`cstar-positive-sum`, cstar.tex:1185, Lemma): the sum of two
positive elements of a C*-algebra is positive.

The proof is the thesis's own estimate, read through the bridge **9IV**:
if `‖a - t‖ ≤ t` and `‖b - s‖ ≤ s` then
`‖(a+b) - (t+s)‖ ≤ ‖a - t‖ + ‖b - s‖ ≤ t + s`. -/
theorem cstar_positive_sum (a b : 𝒜) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + b :=
  by
    have hasa : IsSelfAdjoint a := .of_nonneg ha
    have hbsa : IsSelfAdjoint b := .of_nonneg hb
    obtain ⟨t, ht⟩ := (cstar_positive_def a hasa).mp ha
    obtain ⟨s, hs⟩ := (cstar_positive_def b hbsa).mp hb
    refine (cstar_positive_def (a + b) (hasa.add hbsa)).mpr ⟨t + s, ?_⟩
    have he : a + b - algebraMap ℂ 𝒜 ((t + s : ℝ) : ℂ)
        = (a - algebraMap ℂ 𝒜 (t : ℂ)) + (b - algebraMap ℂ 𝒜 (s : ℂ)) := by
      rw [show ((t + s : ℝ) : ℂ) = ((t : ℝ) : ℂ) + ((s : ℝ) : ℂ) by push_cast; ring, map_add]
      abel
    rw [he]
    calc ‖(a - algebraMap ℂ 𝒜 (t : ℂ)) + (b - algebraMap ℂ 𝒜 (s : ℂ))‖
        ≤ ‖a - algebraMap ℂ 𝒜 (t : ℂ)‖ + ‖b - algebraMap ℂ 𝒜 (s : ℂ)‖ := norm_add_le _ _
      _ ≤ t + s := add_le_add ht hs

/-- **9IX** (cstar.tex:1197, Exercise): if `a` is an *effect*
(`0 ≤ a ≤ 1`), then so is its *orthosupplement* `a^⊥ := 1 - a`. -/
theorem effect_orthosupplement (a : 𝒜) (ha : a ∈ effects 𝒜) :
    1 - a ∈ effects 𝒜 :=
  by
    simp only [effects, Set.mem_Icc] at ha ⊢
    exact ⟨sub_nonneg.mpr ha.2, sub_le_self 1 ha.1⟩

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 1, scalar
clause: a nonnegative real multiple of a positive element is positive.
(The whole of part 1 is `cstar_positive_1_cone` below; this clause is
stated separately because it is the one the rest of the tree applies.) -/
theorem cstar_positive_1 (a : 𝒜) (ha : 0 ≤ a) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ (r : ℂ) • a :=
  ofReal_smul_nonneg ha hr

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 1: the
positive elements form a *cone* — `0` is positive, `a + b` is positive for
positive `a`, `b` (**9VII**), and `r a` is positive for positive `a` and
`r ∈ [0,∞)` — and, as the exercise asks one to conclude, `≤` is a preorder
(reflexivity and transitivity are derived here from the cone properties,
not from the ambient `PartialOrder` instance). -/
theorem cstar_positive_1_cone :
    (0 : 𝒜) ≤ 0 ∧
      (∀ a b : 𝒜, 0 ≤ a → 0 ≤ b → 0 ≤ a + b) ∧
      (∀ (a : 𝒜) (r : ℝ), 0 ≤ a → 0 ≤ r → 0 ≤ (r : ℂ) • a) ∧
      (∀ a : 𝒜, a ≤ a) ∧
      (∀ a b c : 𝒜, a ≤ b → b ≤ c → a ≤ c) :=
  by
    -- the solution's own argument (asols.tex, `parsec-90.100`(1)): `0` is
    -- positive "because `0* = 0` and `‖0 - 0‖ ≤ 0`"; `a + b` is **9VII**
    -- (`parsec-90.70`); `r a` is the scalar clause above.  "Since `0` is
    -- positive, we have `a ≤ a` for all `a`.  Further, when `a ≤ b ≤ c`, then
    -- `b - a` and `c - b` are positive, so `c - a ≡ (c - b) + (b - a)` is
    -- positive, that is `a ≤ c`."
    have hzero : (0 : 𝒜) ≤ 0 :=
      (cstar_positive_def 0 (IsSelfAdjoint.zero 𝒜)).mpr ⟨0, by simp⟩
    refine ⟨hzero, fun a b ha hb => cstar_positive_sum a b ha hb,
      fun a r ha hr => cstar_positive_1 a ha r hr, fun a => ?_, fun a b c hab hbc => ?_⟩
    · have h : (0 : 𝒜) ≤ a - a := le_of_le_of_eq hzero (sub_self a).symm
      exact sub_nonneg.mp h
    · have h := cstar_positive_sum (c - b) (b - a) (sub_nonneg.mpr hbc) (sub_nonneg.mpr hab)
      have e : c - b + (b - a) = c - a := by abel
      rw [e] at h
      exact sub_nonneg.mp h

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 2: `1` is
positive and `-‖a‖ ≤ a ≤ ‖a‖` for self-adjoint `a` (so `1` is an order
unit of `sa(𝒜)`). -/
theorem cstar_positive_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    (0 : 𝒜) ≤ 1 ∧ -(algebraMap ℂ 𝒜 (‖a‖ : ℂ)) ≤ a ∧
      a ≤ algebraMap ℂ 𝒜 (‖a‖ : ℂ) :=
  by
    -- The solution's own argument (asols.tex, `parsec-90.100`(2)), read through
    -- the bridge **9IV** `cstar_positive_def`: `1` is self-adjoint and positive
    -- because `‖1 - 1‖ ≤ 1`; and `a + ‖a‖` and `‖a‖ - a` are self-adjoint and
    -- positive because `‖(a + ‖a‖) - ‖a‖‖ = ‖a‖ ≤ ‖a‖` and
    -- `‖(‖a‖ - a) - ‖a‖‖ = ‖-a‖ = ‖a‖ ≤ ‖a‖`.  Whence `-‖a‖ ≤ a ≤ ‖a‖`.
    have hnorm : IsSelfAdjoint (algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)) :=
      isSelfAdjoint_algebraMap_ofReal ‖a‖
    have hone : (0 : 𝒜) ≤ 1 := by
      refine (cstar_positive_def 1 (IsSelfAdjoint.one 𝒜)).mpr ⟨1, ?_⟩
      norm_num
    have hadd : (0 : 𝒜) ≤ a + algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) := by
      refine (cstar_positive_def _ (ha.add hnorm)).mpr ⟨‖a‖, ?_⟩
      simpa using le_refl ‖a‖
    have hsub : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) - a := by
      refine (cstar_positive_def _ (hnorm.sub ha)).mpr ⟨‖a‖, ?_⟩
      simpa using le_refl ‖a‖
    refine ⟨hone, ?_, sub_nonneg.mp hsub⟩
    have h := sub_nonneg.mp (by simpa [sub_neg_eq_add] using hadd :
      (0 : 𝒜) ≤ a - -(algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ)))
    exact h

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 3: the product
of two positive elements need not be positive (example among the operators
on ℂ²). -/
theorem cstar_positive_3 :
    ∃ a b : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      0 ≤ a ∧ 0 ≤ b ∧ ¬(0 ≤ a * b) :=
  by
    -- The solution's witnesses are `|x⟩⟨x|` and `|y⟩⟨y|` for a non-orthogonal
    -- linearly independent pair `x, y` in a Hilbert space; here `x = e₀` and
    -- `y = e₀ + e₁` in `ℂ²`, for which `|x⟩⟨x| = !![1,0;0,0]` and
    -- `|y⟩⟨y| = !![1,1;1,1]`.  Positivity is the solution's own computation:
    -- `|x⟩⟨x|² = ‖x‖²·|x⟩⟨x|`, whence `‖ |x⟩⟨x| - ‖x‖² ‖² = ‖x‖² ‖ |x⟩⟨x| - ‖x‖² ‖`
    -- and so `‖ |x⟩⟨x| - ‖x‖² ‖ ≤ ‖x‖²`, which is positivity by **9IV**.
    have key : ∀ (p : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
        (c : ℝ), 0 ≤ c → IsSelfAdjoint p → p * p = (c : ℂ) • p → 0 ≤ p := by
      intro p c hc hp hsq
      refine (cstar_positive_def p hp).mpr ⟨c, ?_⟩
      set q := p - algebraMap ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
        ((c : ℝ) : ℂ) with hqdef
      have hqsa : IsSelfAdjoint q := hp.sub (isSelfAdjoint_algebraMap_ofReal c)
      -- `q² = -c·q`, since `p² = c·p`
      have hq2 : q * q = ((-c : ℝ) : ℂ) • q := by
        rw [hqdef, Algebra.algebraMap_eq_smul_one]
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
          hsq, smul_smul, smul_sub]
        push_cast
        module
      -- the C*-identity turns that into `‖q‖² = c‖q‖`
      have hnq : ‖q‖ * ‖q‖ = c * ‖q‖ := by
        have h1 : ‖q * q‖ = ‖q‖ * ‖q‖ := by
          have h2 := CStarRing.norm_star_mul_self (x := q)
          rwa [hqsa.star_eq] at h2
        rw [← h1, hq2, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg hc]
      rcases eq_or_lt_of_le (norm_nonneg q) with h | h
      · rw [← h]; exact hc
      · exact le_of_eq (mul_right_cancel₀ (ne_of_gt h) hnq)
    have hPsa : star (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hQsa : star (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hP : IsSelfAdjoint
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) := by
      show star _ = _
      rw [← map_star, hPsa]
    have hQ : IsSelfAdjoint
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ)) := by
      show star _ = _
      rw [← map_star, hQsa]
    refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ),
      ?_, ?_, ?_⟩
    · -- `x = e₀`, `‖x‖² = 1`
      refine key _ 1 zero_le_one hP ?_
      · have hsq : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0]
            = ((1 : ℂ)) • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_succ]
        rw [← map_mul, hsq, map_smul]
        norm_num
    · -- `y = e₀ + e₁`, `‖y‖² = 2`
      refine key _ 2 (by norm_num) hQ ?_
      · have hsq : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1]
            = ((2 : ℂ)) • (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_succ]
          all_goals ring
        rw [← map_mul, hsq, map_smul]
        norm_num
    · -- The solution's closing step: the product "isn't even self-adjoint, as we
      -- saw in the solution to `parsec-70.30`(10)" — that is, by point 10
      -- (`cstar_involution_basic_10`) it would have to commute, and by point 8
      -- the two do not, on the linear independence of `x` and `y`.
      intro hle
      have hcomm := (cstar_involution_basic_10 _ _ hP hQ).mp hle.isSelfAdjoint
      have hcomm' : Matrix.toEuclideanCLM (𝕜 := ℂ)
            ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, 1])
          = Matrix.toEuclideanCLM (𝕜 := ℂ)
            ((!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0]) := by
        rw [map_mul, map_mul]
        exact hcomm
      exact ketbra_e0_e0e1_not_commute
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective hcomm')

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4: the *order
(semi)norm* `‖a‖ₒ = inf { λ ≥ 0 : -λ ≤ a ≤ λ }` on the self-adjoint
elements. -/
noncomputable def orderNorm (a : 𝒜) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ -(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)}

/-- Auxiliary: the set `{λ ∈ [0,∞) : -λ ≤ a ≤ λ}` of which `‖a‖ₒ` is the
infimum.  The clauses of **9X**.4 are proved below directly from the order,
as solution `parsec-90.100`(4) does — *not* by rewriting `‖·‖ₒ` into `‖·‖`
along **9X**.5d, which is the fact the thesis defers to parsec 170. -/
private def orderNormSet (a : 𝒜) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧ -(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)}

private theorem orderNorm_eq_sInf (a : 𝒜) : orderNorm a = sInf (orderNormSet a) := rfl

private theorem orderNormSet_bddBelow (a : 𝒜) : BddBelow (orderNormSet a) :=
  ⟨0, fun _ hr => hr.1⟩

/-- Auxiliary: `‖a‖` itself is one of the bounds, by **9X**.2 — so the set is
nonempty and `‖a‖ₒ ≤ ‖a‖`. -/
private theorem norm_mem_orderNormSet {a : 𝒜} (ha : IsSelfAdjoint a) :
    ‖a‖ ∈ orderNormSet a :=
  ⟨norm_nonneg a, (cstar_positive_2 a ha).2.1, (cstar_positive_2 a ha).2.2⟩

private theorem orderNormSet_nonempty {a : 𝒜} (ha : IsSelfAdjoint a) :
    (orderNormSet a).Nonempty :=
  ⟨‖a‖, norm_mem_orderNormSet ha⟩

private theorem orderNorm_le_of_mem {a : 𝒜} {r : ℝ} (hr : r ∈ orderNormSet a) :
    orderNorm a ≤ r :=
  csInf_le (orderNormSet_bddBelow a) hr

private theorem orderNorm_nonneg {a : 𝒜} (ha : IsSelfAdjoint a) : 0 ≤ orderNorm a :=
  le_csInf (orderNormSet_nonempty ha) fun _ hr => hr.1

/-- Auxiliary: a bound `λ ∈ [0,∞)` for `a` that is within `ε` of `‖a‖ₒ`. -/
private theorem exists_mem_orderNormSet_lt {a : 𝒜} (ha : IsSelfAdjoint a) {ε : ℝ}
    (hε : 0 < ε) : ∃ r ∈ orderNormSet a, r < orderNorm a + ε := by
  refine exists_lt_of_csInf_lt (orderNormSet_nonempty ha) ?_
  rw [← orderNorm_eq_sInf]
  linarith

private theorem smul_algebraMap_ofReal (r t : ℝ) :
    (r : ℂ) • algebraMap ℂ 𝒜 (t : ℂ) = algebraMap ℂ 𝒜 ((r * t : ℝ) : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
    Complex.ofReal_mul]

/-- Auxiliary (**9X**.1): multiplication by a nonnegative real is monotone. -/
private theorem smul_le_smul_ofReal {a b : 𝒜} (h : a ≤ b) {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) • a ≤ (r : ℂ) • b := by
  have h1 := ofReal_smul_nonneg (sub_nonneg.mpr h) hr
  rwa [smul_sub, sub_nonneg] at h1

/-- Auxiliary: `‖r a‖ₒ = r ‖a‖ₒ` for `r > 0`, by the two inequalities of
solution `parsec-90.100`(4): scaling a bound for `a` by `r` bounds `r a`,
and conversely by scaling with `r⁻¹`. -/
private theorem orderNorm_smul_pos {a : 𝒜} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 < r) :
    orderNorm ((r : ℂ) • a) = r * orderNorm a := by
  have hsmul : ∀ (b : 𝒜) (s : ℝ), 0 < s → IsSelfAdjoint b →
      orderNorm ((s : ℂ) • b) ≤ s * orderNorm b := by
    intro b s hs hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨l, hl, hlt⟩ := exists_mem_orderNormSet_lt hb (div_pos hε hs)
    have hmem : s * l ∈ orderNormSet ((s : ℂ) • b) := by
      refine ⟨mul_nonneg hs.le hl.1, ?_, ?_⟩
      · have h1 := smul_le_smul_ofReal hl.2.1 hs.le
        rwa [smul_neg, smul_algebraMap_ofReal] at h1
      · have h2 := smul_le_smul_ofReal hl.2.2 hs.le
        rwa [smul_algebraMap_ofReal] at h2
    have hle := orderNorm_le_of_mem hmem
    have : s * l < s * (orderNorm b + ε / s) := mul_lt_mul_of_pos_left hlt hs
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hs)] at this
    linarith
  have hrsa : IsSelfAdjoint ((r : ℂ) • a) := by
    refine IsSelfAdjoint.smul ?_ ha
    rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  refine le_antisymm (hsmul a r hr ha) ?_
  have hback := hsmul ((r : ℂ) • a) r⁻¹ (inv_pos.mpr hr) hrsa
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hr), Complex.ofReal_one,
    one_smul] at hback
  have hfin := mul_le_mul_of_nonneg_left hback hr.le
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul] at hfin

private theorem orderNorm_neg (a : 𝒜) : orderNorm (-a) = orderNorm a := by
  have hset : orderNormSet (-a) = orderNormSet a := by
    ext r
    constructor
    · rintro ⟨hr, h1, h2⟩
      exact ⟨hr, neg_le.mp h2, neg_le_neg_iff.mp h1⟩
    · rintro ⟨hr, h1, h2⟩
      exact ⟨hr, neg_le_neg h2, neg_le.mpr h1⟩
  rw [orderNorm_eq_sInf, orderNorm_eq_sInf, hset]

private theorem orderNorm_zero : orderNorm (0 : 𝒜) = 0 := by
  have hmem : (0 : ℝ) ∈ orderNormSet (0 : 𝒜) := by
    refine ⟨le_rfl, ?_, ?_⟩ <;> simp
  exact le_antisymm (orderNorm_le_of_mem hmem) (orderNorm_nonneg (IsSelfAdjoint.zero 𝒜))

/-- Auxiliary (**9X**.5d): the order seminorm of a self-adjoint element is
its norm. -/
theorem orderNorm_eq_norm {a : 𝒜} (ha : IsSelfAdjoint a) : orderNorm a = ‖a‖ := by
  have hset : {r : ℝ | 0 ≤ r ∧ -(algebraMap ℂ 𝒜 (r : ℂ)) ≤ a ∧ a ≤ algebraMap ℂ 𝒜 (r : ℂ)}
      = Set.Ici ‖a‖ := by
    ext r
    constructor
    · rintro ⟨hr, h1, h2⟩
      exact (norm_le_iff_neg_algebraMap_le ha hr).mpr ⟨h1, h2⟩
    · intro hr
      have hr0 : 0 ≤ r := (norm_nonneg a).trans hr
      exact ⟨hr0, (norm_le_iff_neg_algebraMap_le ha hr0).mp hr⟩
  rw [orderNorm, hset, csInf_Ici]

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4a: `‖·‖ₒ` is
a seminorm on `sa(𝒜)`: subadditive and absolutely homogeneous. -/
theorem orderNorm_seminorm (a b : 𝒜) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (r : ℝ) :
    orderNorm (a + b) ≤ orderNorm a + orderNorm b ∧
      orderNorm ((r : ℂ) • a) = |r| * orderNorm a :=
  by
    constructor
    · -- subadditivity: `-λ ≤ a ≤ λ` and `-μ ≤ b ≤ μ` give `-(λ+μ) ≤ a+b ≤ λ+μ`,
      -- and one takes the infimum over such `λ` and `μ`
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨l, hl, hlt⟩ := exists_mem_orderNormSet_lt ha (half_pos hε)
      obtain ⟨m, hm, hmt⟩ := exists_mem_orderNormSet_lt hb (half_pos hε)
      have hsum : ((l + m : ℝ) : ℂ) = ((l : ℝ) : ℂ) + ((m : ℝ) : ℂ) := by push_cast; ring
      have hmem : l + m ∈ orderNormSet (a + b) := by
        refine ⟨by linarith [hl.1, hm.1], ?_, ?_⟩
        · rw [hsum, map_add, neg_add]
          exact add_le_add hl.2.1 hm.2.1
        · rw [hsum, map_add]
          exact add_le_add hl.2.2 hm.2.2
      have hle := orderNorm_le_of_mem hmem
      linarith
    · -- absolute homogeneity, by cases on the sign of `r`
      rcases lt_trichotomy r 0 with hr | hr | hr
      · have hneg : ((r : ℝ) : ℂ) • a = -((((-r : ℝ)) : ℂ) • a) := by
          rw [← neg_smul, ← Complex.ofReal_neg, neg_neg]
        rw [hneg, orderNorm_neg, orderNorm_smul_pos ha (neg_pos.mpr hr),
          abs_of_neg hr]
      · rw [hr]
        simp [orderNorm_zero]
      · rw [orderNorm_smul_pos ha hr, abs_of_pos hr]

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4b:
`‖a‖ₒ ≤ ‖a‖` for self-adjoint `a`. -/
theorem orderNorm_le_norm (a : 𝒜) (ha : IsSelfAdjoint a) :
    orderNorm a ≤ ‖a‖ :=
  -- as in the solution: `‖a‖` is itself one of the bounds, by **9X**.2
  orderNorm_le_of_mem (norm_mem_orderNormSet ha)

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 4c:
`0 ≤ a ≤ b` implies `‖a‖ₒ ≤ ‖b‖ₒ`. -/
theorem orderNorm_mono (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) :
    orderNorm a ≤ orderNorm b :=
  by
    -- directly from the order: every bound for `b` is a bound for `a`, since
    -- `-λ ≤ 0 ≤ a ≤ b ≤ λ`
    have hb' : IsSelfAdjoint b := .of_nonneg (ha.trans hab)
    rw [orderNorm_eq_sInf b]
    refine le_csInf (orderNormSet_nonempty hb') fun r hr => ?_
    refine orderNorm_le_of_mem ⟨hr.1, ?_, hab.trans hr.2.2⟩
    refine le_trans ?_ ha
    rw [neg_nonpos]
    exact algebraMap_ofReal_nonneg hr.1

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5a: `a²` is
positive for self-adjoint `a` (proved later, at 17V/25I). -/
theorem cstar_positive_5a (a : 𝒜) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 :=
  by
    have h : a ^ 2 = star a * a := by rw [ha.star_eq, sq]
    rw [h]
    exact star_mul_self_nonneg a

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5b: a limit of
positive elements is positive. -/
theorem cstar_positive_5b (a : 𝒜) (f : ℕ → 𝒜) (hf : ∀ n, 0 ≤ f n)
    (hlim : Filter.Tendsto f Filter.atTop (nhds a)) : 0 ≤ a :=
  by
    exact ge_of_tendsto hlim (.of_forall hf)

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5c: if
`a ≥ -1/n` for all `n ∈ ℕ`, then `a ≥ 0`. -/
theorem cstar_positive_5c (a : 𝒜) (ha : IsSelfAdjoint a)
    (h : ∀ n : ℕ, -(algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹) ≤ a) : 0 ≤ a :=
  by
    -- The hypothesis says `0 ≤ a + 1/(n+1)`, and `a + 1/(n+1) → a`; so this is
    -- **9X**.5b — the closedness of the positive cone — which is what the thesis
    -- delivers for the whole of **9X**.5 when it returns to it at **17VI**.2.
    -- (Mathlib's `StarOrderedRing.nonneg_iff_spectrum_nonneg` would also do
    -- it, but it is the CFC-backed form of **25I**, a second and independent
    -- entry into that machinery for a fact the section already has.)
    have hstep : ∀ n : ℕ, (0 : 𝒜) ≤ a + algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹ := by
      intro n
      have hn := sub_nonneg.mpr (h n)
      rwa [sub_neg_eq_add] at hn
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hc : Filter.Tendsto (fun r : ℝ => algebraMap ℂ 𝒜 (r : ℂ)) (nhds 0) (nhds 0) := by
      have hcont := (continuous_algebraMap ℝ 𝒜).tendsto (0 : ℝ)
      rw [map_zero] at hcont
      exact Filter.Tendsto.congr (fun r => algebraMap_real_eq r) hcont
    have hs : Filter.Tendsto (fun n : ℕ => algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹)
        Filter.atTop (nhds 0) := by
      have he : (fun n : ℕ => algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹)
          = fun n : ℕ => algebraMap ℂ 𝒜 ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
        funext n; congr 1; push_cast; ring
      rw [he]
      exact hc.comp h0
    refine cstar_positive_5b a (fun n => a + algebraMap ℂ 𝒜 ((n : ℂ) + 1)⁻¹) hstep ?_
    simpa using Filter.Tendsto.add tendsto_const_nhds hs

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5d:
`‖a‖ = ‖a‖ₒ` for self-adjoint `a`. -/
theorem cstar_positive_5d (a : 𝒜) (ha : IsSelfAdjoint a) :
    ‖a‖ = orderNorm a :=
  (orderNorm_eq_norm ha).symm

/-- **9X** (`cstar-positive`, cstar.tex:1209, Exercise), part 5e: `a = 0`
when `0 ≤ a ≤ 0` (antisymmetry). -/
theorem cstar_positive_5e (a : 𝒜) (h0 : 0 ≤ a) (h1 : a ≤ 0) : a = 0 :=
  by
    -- not by `le_antisymm` — that would read the claim off the `PartialOrder`
    -- instance in the binder.  Instead: `-0 ≤ a ≤ 0` gives `‖a‖ ≤ 0` by
    -- **17VI**.3a, which is where the thesis proves this point (17VI.1).
    have hsa : IsSelfAdjoint a := .of_nonneg h0
    have hle : ‖a‖ ≤ 0 := by
      refine (norm_le_iff_neg_algebraMap_le hsa le_rfl).mpr ⟨?_, ?_⟩
      · rw [Complex.ofReal_zero, map_zero, neg_zero]
        exact h0
      · rw [Complex.ofReal_zero, map_zero]
        exact h1
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg a))

end Positive

/-! ## Parsec 100: morphisms of C*-algebras -/

section Maps

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 1: a linear map
between C*-algebras is *multiplicative* when it preserves products. -/
def IsMultiplicativeMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ a b : 𝒜, f (a * b) = f a * f b

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 2: a linear map is
*involution preserving* when `f(a*) = f(a)*`. -/
def IsInvolutionPreserving (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ a : 𝒜, f (star a) = star (f a)

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 3: a linear map is
*unital* when `f 1 = 1`.  (Part 4, *subunital* `f 1 ≤ 1`, is
`Theses.Subunital` from `Theses.Common`.) -/
def IsUnitalMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  f 1 = 1

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 5: a linear map is
*positive* when it maps positive elements to positive elements.
(Mathlib's bundled version: `𝒜 →ₚ[ℂ] ℬ`, `PositiveLinearMap`.) -/
def IsPositiveMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ a : 𝒜, 0 ≤ a → 0 ≤ f a

/-- **10II** (`maps`, cstar.tex:1267, Definition), part 6: a linear map is
*completely positive* when `∑_{i,j} bᵢ* f(aᵢ* aⱼ) bⱼ ≥ 0` for all
`a₁,…,aₙ ∈ 𝒜` and `b₁,…,bₙ ∈ ℬ`.  (Mathlib's bundled version:
`𝒜 →CP ℬ`, `CompletelyPositiveMap`.)

**10III** (cstar.tex:1305): the abbreviations pu, miu, cpsu, … for
combinations of these properties, and the categories `CStar_miu` etc.;
miu-maps are Mathlib's ∗-homomorphisms `𝒜 →⋆ₐ[ℂ] ℬ` (see `Theses.MIUMap`). -/
def IsCompletelyPositiveMap (f : 𝒜 →ₗ[ℂ] ℬ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → 𝒜) (b : Fin n → ℬ),
    0 ≤ ∑ i, ∑ j, star (b i) * f (star (a i) * a j) * b j

/-- **10IV** (`cstar-p-implies-i`, cstar.tex:1338, Lemma (p⇒i)): a positive
linear map between C*-algebras is involution preserving.

The proof is the thesis's own: for self-adjoint `x` both `‖x‖` and `‖x‖ - x`
are positive by **9X**.2, so `f x = f ‖x‖ - f (‖x‖ - x)` is a difference of
positive — hence self-adjoint — elements; then `f(ℜa)` and `f(ℑa)` are self
adjoint, and `f(a*) = f(ℜa) - i f(ℑa) = (f a)*`. -/
theorem cstar_p_implies_i (f : 𝒜 →ₗ[ℂ] ℬ) (hf : IsPositiveMap f) :
    IsInvolutionPreserving f :=
  by
    have hsa : ∀ x : 𝒜, IsSelfAdjoint x → IsSelfAdjoint (f x) := by
      intro x hx
      have h1 : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 (‖x‖ : ℂ) :=
        algebraMap_ofReal_nonneg (norm_nonneg x)
      have h2 : (0 : 𝒜) ≤ algebraMap ℂ 𝒜 (‖x‖ : ℂ) - x :=
        sub_nonneg.mpr (cstar_positive_2 x hx).2.2
      have h3 := (IsSelfAdjoint.of_nonneg (hf _ h1)).sub (IsSelfAdjoint.of_nonneg (hf _ h2))
      rwa [← map_sub,
        show algebraMap ℂ 𝒜 (‖x‖ : ℂ) - (algebraMap ℂ 𝒜 (‖x‖ : ℂ) - x) = x from by abel] at h3
    intro a
    have ha : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) := (realPart_add_I_smul_imaginaryPart a).symm
    have has : star a = (ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜) := by
      conv_lhs => rw [ha]
      rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
      simp [sub_eq_add_neg]
    have h1 := hsa _ (ℜ a).property
    have h2 := hsa _ (ℑ a).property
    rw [has, map_sub, map_smul]
    conv_rhs => rw [ha]
    rw [map_add, map_smul, star_add, star_smul, h1.star_eq, h2.star_eq]
    simp [sub_eq_add_neg]

end Order

end Maps

/-! ## Parsec 110: invertible elements and the spectrum -/

section Invertibles

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **11II** (`geometric`, cstar.tex:1404, Lemma), part 1: for `‖a‖ < 1`
the geometric series `∑ aⁿ` converges absolutely. -/
theorem geometric_1 (a : 𝒜) (ha : ‖a‖ < 1) :
    Summable fun n : ℕ => ‖a ^ n‖ := by
  -- the Lemma's own comparison: `∑ ‖a‖ⁿ = (1-‖a‖)⁻¹ < ∞`, and `‖aⁿ‖ ≤ ‖a‖ⁿ`
  have hgeo : Summable fun n : ℕ => ‖a‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg a) ha
  refine hgeo.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := CStarRing.norm_star_mul_self (x := (1 : 𝒜))
    rw [star_one, one_mul] at h
    simpa using by nlinarith [norm_nonneg (1 : 𝒜)]
  · exact norm_pow_le' a hn

/-- **11II** (`geometric`, cstar.tex:1404, Lemma), part 2: for `‖a‖ < 1`
the element `a^⊥ = 1 - a` is invertible with inverse `∑ₙ aⁿ`. -/
theorem geometric_2 (a : 𝒜) (ha : ‖a‖ < 1) :
    IsUnit (1 - a) ∧ (1 - a) * ∑' n : ℕ, a ^ n = 1 ∧
      (∑' n : ℕ, a ^ n) * (1 - a) = 1 := by
  -- the Lemma's own partial-sum limit: `aᴺ → 0`, `∑ aⁿ` converges since `∑ ‖a‖ⁿ` does,
  -- and one takes the norm limit on both sides of `(1-a)(1+a+⋯+aᴺ) = 1-aᴺ`
  have hsummable : Summable fun n : ℕ => a ^ n := (geometric_1 a ha).of_norm
  have hazero : Filter.Tendsto (fun N : ℕ => a ^ N) Filter.atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have htend : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a ^ n)
      Filter.atTop (nhds (∑' n : ℕ, a ^ n)) := hsummable.hasSum.tendsto_sum_nat
  have hone : Filter.Tendsto (fun N : ℕ => 1 - a ^ N) Filter.atTop (nhds (1 : 𝒜)) := by
    simpa using (tendsto_const_nhds (x := (1 : 𝒜)) (f := Filter.atTop (α := ℕ))).sub hazero
  have hL : (1 - a) * ∑' n : ℕ, a ^ n = 1 :=
    tendsto_nhds_unique (htend.const_mul (1 - a))
      (Filter.Tendsto.congr (fun N => (mul_neg_geom_sum a N).symm) hone)
  have hR : (∑' n : ℕ, a ^ n) * (1 - a) = 1 :=
    tendsto_nhds_unique (htend.mul_const (1 - a))
      (Filter.Tendsto.congr (fun N => (geom_sum_mul_neg a N).symm) hone)
  exact ⟨⟨⟨1 - a, ∑' n : ℕ, a ^ n, hL, hR⟩, rfl⟩, hL, hR⟩

/-- **11VI** (`spectrum-bounded`, cstar.tex:1451, Exercise), part 1:
`a - λ` is invertible for every `λ ∈ ℂ` with `‖a‖ < |λ|`.

The proof is the solution's own: `‖a λ⁻¹‖ = |λ|⁻¹ ‖a‖ < 1`, so `1 - a λ⁻¹`
is invertible by **11II**.2, and hence so is `λ - a = λ (1 - a λ⁻¹)`. -/
theorem spectrum_bounded_1 (a : 𝒜) (z : ℂ) (h : ‖a‖ < ‖z‖) :
    IsUnit (a - algebraMap ℂ 𝒜 z) :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · exact isUnit_of_subsingleton _
    · have hnormalg : ∀ w : ℂ, ‖algebraMap ℂ 𝒜 w‖ = ‖w‖ := fun w => by
        rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg a) h
      have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
      have h1 : ‖a * algebraMap ℂ 𝒜 z⁻¹‖ < 1 := by
        refine lt_of_le_of_lt (norm_mul_le _ _) ?_
        rw [hnormalg, norm_inv, ← div_eq_mul_inv, div_lt_one hzpos]
        exact h
      have hu : IsUnit (1 - a * algebraMap ℂ 𝒜 z⁻¹) := (geometric_2 _ h1).1
      have hzu : IsUnit (algebraMap ℂ 𝒜 z) := (Ne.isUnit hz0).map (algebraMap ℂ 𝒜)
      have hfac : algebraMap ℂ 𝒜 z * (1 - a * algebraMap ℂ 𝒜 z⁻¹) = algebraMap ℂ 𝒜 z - a := by
        rw [mul_sub, mul_one, ← mul_assoc, Algebra.commutes, mul_assoc, ← map_mul,
          mul_inv_cancel₀ hz0, map_one, mul_one]
      have hprod := hzu.mul hu
      rw [hfac] at hprod
      simpa using hprod.neg

/-- **11VI** (`spectrum-bounded`, cstar.tex:1451, Exercise), part 2:
`a - b` is invertible when `b` is invertible and `a` is small compared
to `b`.  The hypothesis is the errata-corrected bound `‖a‖ < ‖b⁻¹‖⁻¹`
(erratum `parsec-110.60`), which is what cstar.tex prints. -/
theorem spectrum_bounded_2 (a : 𝒜) (b : 𝒜ˣ)
    (h : ‖a‖ < ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖⁻¹) :
    IsUnit (a - (b : 𝒜)) :=
  by
    have hb0 : ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖ ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at h
      exact absurd h (not_lt.mpr (norm_nonneg a))
    have hpos : 0 < ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
    have h1 : ‖((b⁻¹ : 𝒜ˣ) : 𝒜) * a‖ < 1 := by
      refine lt_of_le_of_lt (norm_mul_le _ _) ?_
      have h2 := mul_lt_mul_of_pos_left h hpos
      rwa [mul_inv_cancel₀ hb0] at h2
    have hu : IsUnit (1 - ((b⁻¹ : 𝒜ˣ) : 𝒜) * a) := ⟨Units.oneSub _ h1, rfl⟩
    have h3 : IsUnit ((b : 𝒜) * (1 - ((b⁻¹ : 𝒜ˣ) : 𝒜) * a)) := b.isUnit.mul hu
    rw [mul_sub, mul_one, ← mul_assoc] at h3
    simp only [Units.mul_inv, one_mul] at h3
    simpa using h3.neg

/-- **11VI** (`spectrum-bounded`, cstar.tex:1451, Exercise), part 3: the
invertible elements form an open subset of `𝒜`.

The proof is the solution's own: around an invertible `b` take the radius
`ε := ‖(-b)⁻¹‖⁻¹`; every `y` with `‖y - b‖ < ε` is invertible by part 2,
because `y = (y - b) - (-b)`. -/
theorem spectrum_bounded_3 : IsOpen {b : 𝒜 | IsUnit b} :=
  by
    rcases subsingleton_or_nontrivial 𝒜 with hs | hs
    · have h : {b : 𝒜 | IsUnit b} = Set.univ :=
        Set.eq_univ_of_forall fun b => isUnit_of_subsingleton b
      rw [h]
      exact isOpen_univ
    rw [Metric.isOpen_iff]
    rintro x hx
    obtain ⟨u, rfl⟩ := hx
    have hpos : 0 < ‖(((-u)⁻¹ : 𝒜ˣ) : 𝒜)‖ := Units.norm_pos _
    refine ⟨‖(((-u)⁻¹ : 𝒜ˣ) : 𝒜)‖⁻¹, inv_pos.mpr hpos, fun y hy => ?_⟩
    rw [mem_ball_iff_norm] at hy
    have h := spectrum_bounded_2 (y - (u : 𝒜)) (-u) hy
    have he : y - (u : 𝒜) - ((-u : 𝒜ˣ) : 𝒜) = y := by
      rw [Units.val_neg, sub_neg_eq_add, sub_add_cancel]
    rwa [he] at h

/-- **11VII** (`geometric-convergence`, cstar.tex:1467, Lemma): for
self-adjoint `a` the series `∑ₙ aⁿ` converges iff `‖a‖ < 1` (and then
converges absolutely, see **11II**). -/
theorem geometric_convergence (a : 𝒜) (ha : IsSelfAdjoint a) :
    (Summable fun n : ℕ => a ^ n) ↔ ‖a‖ < 1 :=
  by
    constructor
    · intro hs
      by_contra hcon
      push_neg at hcon
      have hpow : ∀ k : ℕ, ‖a ^ 2 ^ k‖ = ‖a‖ ^ 2 ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hsa : IsSelfAdjoint (a ^ 2 ^ k) := ha.pow _
          have he : a ^ 2 ^ (k + 1) = (a ^ 2 ^ k) ^ 2 := by
            rw [← pow_mul, ← pow_succ]
          rw [he, cstar_involution_basic_13 _ hsa, ih, ← pow_mul, ← pow_succ]
      have h1 : ∀ k : ℕ, (1 : ℝ) ≤ ‖a ^ 2 ^ k‖ := by
        intro k
        rw [hpow k]
        exact one_le_pow₀ hcon
      have hnorm : Filter.Tendsto (fun n : ℕ => ‖a ^ n‖) Filter.atTop (nhds 0) := by
        simpa using hs.tendsto_atTop_zero.norm
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm 1 one_pos
      have h2 := hN (2 ^ N) (Nat.le_of_lt (Nat.lt_two_pow_self))
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h2
      linarith [h1 N]
    · intro h
      exact summable_geometric_of_norm_lt_one h

/-- Auxiliary (**11XI**, the first half of the proof of **11X**): inversion is
continuous at `1` — if `‖1 - a‖ ≤ ½` then `a` is invertible and
`‖1 - a⁻¹‖ ≤ 2‖1 - a‖`. -/
private theorem cstar_inv_continuous_at_one (a : 𝒜) (ha : ‖1 - a‖ ≤ 1 / 2) :
    IsUnit a ∧ ‖1 - Ring.inverse a‖ ≤ 2 * ‖1 - a‖ := by
  set c : 𝒜 := 1 - a with hc
  have hac : a = 1 - c := by rw [hc]; abel
  have hlt : ‖c‖ < 1 := lt_of_le_of_lt ha (by norm_num)
  obtain ⟨-, hL, hR⟩ := geometric_2 c hlt
  have hnormsum : Summable fun n : ℕ => ‖c ^ n‖ := geometric_1 c hlt
  have hsum : Summable fun n : ℕ => c ^ n := hnormsum.of_norm
  -- `a = 1 - c` is invertible with `a⁻¹ = ∑ₙ cⁿ` by **11II**
  set u : 𝒜ˣ := ⟨1 - c, ∑' n : ℕ, c ^ n, hL, hR⟩ with hu
  have hUnit : IsUnit a := by rw [hac]; exact ⟨u, rfl⟩
  have hinv : Ring.inverse a = ∑' n : ℕ, c ^ n := by
    rw [hac, show (1 : 𝒜) - c = (u : 𝒜) from rfl, Ring.inverse_unit]
    rfl
  refine ⟨hUnit, ?_⟩
  -- `1 - a⁻¹ = -∑_{n≥1} cⁿ`, whose norm is at most `‖c‖(1-‖c‖)⁻¹ ≤ 2‖c‖`
  have hsplit : (∑' n : ℕ, c ^ n) = 1 + ∑' n : ℕ, c ^ (n + 1) := by
    simpa using hsum.tsum_eq_zero_add
  have heq : (1 : 𝒜) - Ring.inverse a = -∑' n : ℕ, c ^ (n + 1) := by
    rw [hinv, hsplit]
    abel
  have hs1 : Summable fun n : ℕ => c ^ (n + 1) := hsum.comp_injective (add_left_injective 1)
  have hs1n : Summable fun n : ℕ => ‖c ^ (n + 1)‖ :=
    hnormsum.comp_injective (add_left_injective 1)
  have hgeo : Summable fun n : ℕ => ‖c‖ ^ (n + 1) := by
    have := (summable_geometric_of_lt_one (norm_nonneg c) hlt)
    exact this.comp_injective (add_left_injective 1)
  have hbound : ‖∑' n : ℕ, c ^ (n + 1)‖ ≤ ∑' n : ℕ, ‖c‖ ^ (n + 1) := by
    refine le_trans (norm_tsum_le_tsum_norm hs1n) ?_
    exact hs1n.tsum_le_tsum (fun n => norm_pow_le' c (Nat.succ_pos n)) hgeo
  have hgeoval : (∑' n : ℕ, ‖c‖ ^ (n + 1)) = ‖c‖ * (1 - ‖c‖)⁻¹ := by
    have h := tsum_geometric_of_lt_one (norm_nonneg c) hlt
    calc (∑' n : ℕ, ‖c‖ ^ (n + 1)) = ∑' n : ℕ, ‖c‖ * ‖c‖ ^ n := by
          refine tsum_congr fun n => ?_
          rw [pow_succ, mul_comm]
      _ = ‖c‖ * ∑' n : ℕ, ‖c‖ ^ n := tsum_mul_left
      _ = ‖c‖ * (1 - ‖c‖)⁻¹ := by rw [h]
  have hhalf : (1 - ‖c‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  rw [heq, norm_neg]
  calc ‖∑' n : ℕ, c ^ (n + 1)‖ ≤ ∑' n : ℕ, ‖c‖ ^ (n + 1) := hbound
    _ = ‖c‖ * (1 - ‖c‖)⁻¹ := hgeoval
    _ ≤ ‖c‖ * 2 := mul_le_mul_of_nonneg_left hhalf (norm_nonneg c)
    _ = 2 * ‖1 - a‖ := by rw [hc]; ring

/-- Auxiliary (**11XII**, the second half of the proof of **11X**): if `a` is
invertible and `‖a - b‖ ≤ ½‖a⁻¹‖⁻¹` then `b` is invertible and
`‖a⁻¹ - b⁻¹‖ ≤ 2‖a - b‖‖a⁻¹‖²`. -/
private theorem cstar_inv_continuous_estimate (a b : 𝒜) (ha : IsUnit a)
    (hab : ‖a - b‖ ≤ 1 / 2 * ‖Ring.inverse a‖⁻¹) :
    IsUnit b ∧ ‖Ring.inverse a - Ring.inverse b‖
      ≤ 2 * ‖a - b‖ * ‖Ring.inverse a‖ ^ 2 := by
  set A : 𝒜 := Ring.inverse a with hA
  have hAa : A * a = 1 := Ring.inverse_mul_cancel a ha
  have haA : a * A = 1 := Ring.mul_inverse_cancel a ha
  have hAunit : IsUnit A := ⟨⟨A, a, hAa, haA⟩, rfl⟩
  -- `1 - A b = A (a - b)`, of norm at most `‖A‖ ‖a-b‖ ≤ ½`
  have hd : (1 : 𝒜) - A * b = A * (a - b) := by rw [mul_sub, hAa]
  have hdnorm : ‖(1 : 𝒜) - A * b‖ ≤ 1 / 2 := by
    rw [hd]
    refine le_trans (norm_mul_le _ _) ?_
    rcases eq_or_lt_of_le (norm_nonneg A) with hA0 | hA0
    · rw [← hA0, zero_mul]
      norm_num
    · calc ‖A‖ * ‖a - b‖ ≤ ‖A‖ * (1 / 2 * ‖A‖⁻¹) :=
            mul_le_mul_of_nonneg_left hab (norm_nonneg A)
        _ = 1 / 2 := by field_simp
  obtain ⟨hABunit, hABest⟩ := cstar_inv_continuous_at_one (A * b) hdnorm
  set W : 𝒜 := Ring.inverse (A * b) with hW
  have hWl : W * (A * b) = 1 := Ring.inverse_mul_cancel _ hABunit
  have hWr : (A * b) * W = 1 := Ring.mul_inverse_cancel _ hABunit
  -- `b` is invertible, with `b⁻¹ = W A`
  have hbW : b * (W * A) = 1 := by
    have h1 : a * (A * b * W) = a := by rw [hWr, mul_one]
    have h2 : b * W = a := by
      rw [← mul_assoc, ← mul_assoc, haA, one_mul] at h1
      exact h1
    rw [← mul_assoc, h2, haA]
  have hWb : (W * A) * b = 1 := by rw [mul_assoc]; exact hWl
  have hbUnit : IsUnit b := ⟨⟨b, W * A, hbW, hWb⟩, rfl⟩
  have hbinv : Ring.inverse b = W * A := by
    have : Ring.inverse ((⟨b, W * A, hbW, hWb⟩ : 𝒜ˣ) : 𝒜) = _ := Ring.inverse_unit _
    simpa using this
  refine ⟨hbUnit, ?_⟩
  -- `a⁻¹ - b⁻¹ = (1 - (A b)⁻¹) A`
  have hsplit : A - Ring.inverse b = (1 - W) * A := by
    rw [hbinv, sub_mul, one_mul]
  rw [hsplit]
  calc ‖(1 - W) * A‖ ≤ ‖1 - W‖ * ‖A‖ := norm_mul_le _ _
    _ ≤ (2 * ‖1 - A * b‖) * ‖A‖ := mul_le_mul_of_nonneg_right hABest (norm_nonneg A)
    _ ≤ (2 * (‖A‖ * ‖a - b‖)) * ‖A‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg A)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [hd]
        exact norm_mul_le _ _
    _ = 2 * ‖a - b‖ * ‖A‖ ^ 2 := by ring

/-- **11X** (`cstar-inv-continuous`, cstar.tex:1508, Lemma): the assignment
`a ↦ a⁻¹` is continuous on the set of invertible elements. -/
theorem cstar_inv_continuous :
    ContinuousOn (Ring.inverse : 𝒜 → 𝒜) {a : 𝒜 | IsUnit a} := by
  -- the Lemma's two-step estimate: continuity at `1`, then everywhere
  rcases subsingleton_or_nontrivial 𝒜 with hs | hs
  · have he : (Ring.inverse : 𝒜 → 𝒜) = fun _ => 0 := by
      funext x
      exact Subsingleton.elim _ _
    rw [he]
    exact continuousOn_const
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set K : ℝ := ‖Ring.inverse a‖ with hK
  have hKpos : 0 < K := by
    rw [hK, norm_pos_iff]
    intro h0
    have h := Ring.mul_inverse_cancel a ha
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  refine ⟨min (1 / 2 * K⁻¹) (ε / (2 * K ^ 2 + 1)), ?_, ?_⟩
  · exact lt_min (by positivity) (by positivity)
  · intro b _ hdist
    rw [dist_eq_norm] at hdist
    have h1 : ‖a - b‖ ≤ 1 / 2 * K⁻¹ := by
      rw [← norm_neg, neg_sub]
      exact le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))
    obtain ⟨-, hest⟩ := cstar_inv_continuous_estimate a b ha h1
    rw [dist_eq_norm']
    have h2 : ‖a - b‖ < ε / (2 * K ^ 2 + 1) := by
      rw [← norm_neg, neg_sub]
      exact lt_of_lt_of_le hdist (min_le_right _ _)
    have h3 : 2 * ‖a - b‖ * K ^ 2 < ε := by
      have hden : (0 : ℝ) < 2 * K ^ 2 + 1 := by positivity
      have h4 := (lt_div_iff₀ hden).mp h2
      nlinarith [norm_nonneg (a - b), sq_nonneg K]
    exact lt_of_le_of_lt hest h3


/-- **11XIII** (cstar.tex:1548, Lemma): `a - i` is invertible for
self-adjoint `a`.

The proof is the thesis's own trick: write `a - i = (a + ni) - (n+1)i` for
`n` large, and apply **11VI**.2, the bound being
`‖a+ni‖² = ‖(a+ni)*(a+ni)‖ = ‖a²+n²‖ ≤ ‖a‖²+n² < (n+1)²`.  The `n` is chosen
for `‖a‖² < 2n+1`, which is what the strict step needs and what cstar.tex
prints (erratum `parsec-110.140`). -/
theorem selfAdjoint_sub_I_isUnit (a : 𝒜) (ha : IsSelfAdjoint a) :
    IsUnit (a - algebraMap ℂ 𝒜 Complex.I) := by
  rcases subsingleton_or_nontrivial 𝒜 with hs | hs
  · exact isUnit_of_subsingleton _
  have hnormalg : ∀ z : ℂ, ‖algebraMap ℂ 𝒜 z‖ = ‖z‖ := fun z => by
    rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]
  obtain ⟨n, hn⟩ := exists_nat_gt (‖a‖ ^ 2)
  set N : ℝ := (n : ℝ) with hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg n
  set c : 𝒜 := algebraMap ℂ 𝒜 ((N : ℂ) * Complex.I) with hc
  have hAstar : star (a + c) = a - c := by
    rw [star_add, ha.star_eq, hc, ← algebraMap_star_comm]
    have : star ((N : ℂ) * Complex.I) = -((N : ℂ) * Complex.I) := by simp
    rw [this, map_neg, ← sub_eq_add_neg]
  have hAA : star (a + c) * (a + c) = a ^ 2 + algebraMap ℂ 𝒜 ((N : ℂ) ^ 2) := by
    rw [hAstar]
    have hcomm : c * a = a * c := Algebra.commutes _ a
    have hcc : c * c = - algebraMap ℂ 𝒜 ((N : ℂ) ^ 2) := by
      rw [hc, ← map_mul, ← map_neg]
      congr 1
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc (N : ℂ) * Complex.I * ((N : ℂ) * Complex.I)
          = (N : ℂ) * (N : ℂ) * (Complex.I * Complex.I) := by ring
        _ = -((N : ℂ) ^ 2) := by rw [hI]; ring
    calc (a - c) * (a + c) = a * a + (a * c - c * a) - c * c := by noncomm_ring
      _ = a ^ 2 + algebraMap ℂ 𝒜 ((N : ℂ) ^ 2) := by rw [hcomm, hcc]; noncomm_ring
  have hnormsq : ‖a + c‖ ^ 2 ≤ ‖a‖ ^ 2 + N ^ 2 := by
    have h1 : ‖a + c‖ ^ 2 = ‖a ^ 2 + algebraMap ℂ 𝒜 ((N : ℂ) ^ 2)‖ := by
      rw [← hAA, CStarRing.norm_star_mul_self]
      ring
    rw [h1]
    calc ‖a ^ 2 + algebraMap ℂ 𝒜 ((N : ℂ) ^ 2)‖
        ≤ ‖a ^ 2‖ + ‖algebraMap ℂ 𝒜 ((N : ℂ) ^ 2)‖ := norm_add_le _ _
      _ = ‖a‖ ^ 2 + N ^ 2 := by
          rw [cstar_involution_basic_13 a ha, hnormalg]
          congr 1
          rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
  have hlt : ‖a + c‖ < N + 1 := by
    nlinarith [norm_nonneg (a + c), hn, hN0]
  have hw : ((N + 1 : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  set w : ℂ := ((N + 1 : ℝ) : ℂ) * Complex.I with hwdef
  let b : 𝒜ˣ :=
    { val := algebraMap ℂ 𝒜 w
      inv := algebraMap ℂ 𝒜 w⁻¹
      val_inv := by rw [← map_mul, mul_inv_cancel₀ hw, map_one]
      inv_val := by rw [← map_mul, inv_mul_cancel₀ hw, map_one] }
  have hbinv : ((b⁻¹ : 𝒜ˣ) : 𝒜) = algebraMap ℂ 𝒜 w⁻¹ := rfl
  have hbnorm : ‖((b⁻¹ : 𝒜ˣ) : 𝒜)‖⁻¹ = N + 1 := by
    rw [hbinv, hnormalg, norm_inv, inv_inv, hwdef, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmain := spectrum_bounded_2 (a + c) b (by rw [hbnorm]; exact hlt)
  have heq : (a + c) - (b : 𝒜) = a - algebraMap ℂ 𝒜 Complex.I := by
    show (a + algebraMap ℂ 𝒜 ((N : ℂ) * Complex.I)) - algebraMap ℂ 𝒜 w
        = a - algebraMap ℂ 𝒜 Complex.I
    have hz : (N : ℂ) * Complex.I - w = -Complex.I := by
      rw [hwdef]; push_cast; ring
    rw [add_sub_assoc, ← map_sub, hz, map_neg, ← sub_eq_add_neg]
  rwa [heq] at hmain

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1570, Exercise),
part 1: `a - λ` is invertible for self-adjoint `a` and `λ ∈ ℂ \ ℝ`. -/
theorem spectrum_self_adjoint_real_1 (a : 𝒜) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (a - algebraMap ℂ 𝒜 z) := by
  -- the solution's reduction to **11XIII**: `a - λ = (Im λ) · ((a - Re λ)/(Im λ) - i)`
  have hxsa : IsSelfAdjoint (algebraMap ℂ 𝒜 ((z.re : ℝ) : ℂ)) := by
    show star _ = _
    rw [← algebraMap_star_comm]
    simp
  have hasub : IsSelfAdjoint (a - algebraMap ℂ 𝒜 ((z.re : ℝ) : ℂ)) := ha.sub hxsa
  have hyne : ((z.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  set b : 𝒜 := algebraMap ℂ 𝒜 (((z.im : ℝ) : ℂ))⁻¹ * (a - algebraMap ℂ 𝒜 ((z.re : ℝ) : ℂ))
    with hb
  have hbsa : IsSelfAdjoint b := by
    have hinvsa : IsSelfAdjoint (algebraMap ℂ 𝒜 (((z.im : ℝ) : ℂ))⁻¹) := by
      show star _ = _
      rw [← algebraMap_star_comm]
      simp
    rw [hb]
    show star _ = _
    rw [star_mul, hasub.star_eq, hinvsa.star_eq, Algebra.commutes]
  have hunit := selfAdjoint_sub_I_isUnit b hbsa
  have hyu : IsUnit (algebraMap ℂ 𝒜 ((z.im : ℝ) : ℂ)) :=
    (Ne.isUnit hyne).map (algebraMap ℂ 𝒜)
  have hprod := hyu.mul hunit
  have heq : algebraMap ℂ 𝒜 ((z.im : ℝ) : ℂ) * (b - algebraMap ℂ 𝒜 Complex.I)
      = a - algebraMap ℂ 𝒜 z := by
    rw [hb, mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hyne, map_one, one_mul,
      ← map_mul, sub_sub, ← map_add]
    congr 2
    rw [Complex.ext_iff]
    constructor <;> simp
  rwa [heq] at hprod

/-- Auxiliary: every point of the spectrum of a self-adjoint element is real.
This is the thesis's **11XXI**.1, which the thesis reads off from **11XV**.1,
and that is how it is obtained here — so that everything in this file that
uses reality of the spectrum runs on the thesis's own chain
**11XIII** → **11XV**.1, and not on Mathlib's independent
`IsSelfAdjoint.mem_spectrum_eq_re` (which goes through `exp` and the
unitaries).  Public since 2026-09-05 so that `Positive.lean` and
`Representation.lean` run on the same chain (`docs/BOOTSTRAP-SIZING.md`). -/
theorem mem_spectrum_eq_re_of_isSelfAdjoint {a : 𝒜} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z ∈ spectrum ℂ a) : z = (z.re : ℂ) := by
  by_contra hcon
  have him : z.im ≠ 0 := fun h0 => hcon (Complex.ext rfl (by simp [h0]))
  exact (spectrum.mem_iff.mp hz)
    (by simpa using (spectrum_self_adjoint_real_1 a ha z him).neg)

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1570, Exercise),
part 2: `aⁿ - λ` is invertible for self-adjoint `a`, even `n` (in
particular `n = 2`) and `λ ∈ ℂ \ [0,∞)`. -/
theorem spectrum_self_adjoint_real_2 (a : 𝒜) (ha : IsSelfAdjoint a)
    (n : ℕ) (hn : Even n) (z : ℂ) (hz : ∀ r : ℝ, 0 ≤ r → z ≠ r) :
    IsUnit (a ^ n - algebraMap ℂ 𝒜 z) :=
  by
    -- the solution's own argument, for `n = 2m`: for non-real `λ` this is part 1
    -- applied to the self-adjoint `aⁿ`; and for `λ ∈ (-∞,0)`, writing
    -- `λ = -s²`, one factors `aⁿ - λ = (aᵐ - si)(aᵐ + si)`, both factors being
    -- invertible by part 1 because `aᵐ` is self-adjoint.
    by_cases him : z.im = 0
    · obtain ⟨m, hm⟩ := hn
      have hbsa : IsSelfAdjoint (a ^ m) := ha.pow m
      have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
      have hneg : z.re < 0 := by
        by_contra hcon
        push_neg at hcon
        exact hz z.re hcon hzre
      set s : ℝ := Real.sqrt (-z.re) with hsdef
      have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
      have hsr : s * s = -z.re := by
        rw [hsdef]
        exact Real.mul_self_sqrt (by linarith)
      have hsc : (s : ℂ) * (s : ℂ) = -(z.re : ℂ) := by exact_mod_cast congrArg Complex.ofReal hsr
      have hsq : ((s : ℂ) * Complex.I) * ((s : ℂ) * Complex.I) = z := by
        rw [show ((s : ℂ) * Complex.I) * ((s : ℂ) * Complex.I)
            = ((s : ℂ) * (s : ℂ)) * (Complex.I * Complex.I) by ring, hsc, Complex.I_mul_I,
          show -(z.re : ℂ) * (-1 : ℂ) = (z.re : ℂ) from by ring]
        exact hzre.symm
      have h1 : IsUnit (a ^ m - algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I)) :=
        spectrum_self_adjoint_real_1 (a ^ m) hbsa _ (by simpa using ne_of_gt hs0)
      have h2 : IsUnit (a ^ m - algebraMap ℂ 𝒜 (-((s : ℂ) * Complex.I))) :=
        spectrum_self_adjoint_real_1 (a ^ m) hbsa _ (by simpa using ne_of_lt (neg_neg_iff_pos.mpr hs0))
      have hcomm : algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I) * a ^ m
          = a ^ m * algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I) := Algebra.commutes _ _
      have he : (a ^ m - algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I))
            * (a ^ m - algebraMap ℂ 𝒜 (-((s : ℂ) * Complex.I)))
          = a ^ n - algebraMap ℂ 𝒜 z := by
        rw [map_neg, sub_neg_eq_add, hm, pow_add]
        calc (a ^ m - algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I))
              * (a ^ m + algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I))
            = a ^ m * a ^ m
              + (a ^ m * algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I)
                - algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I) * a ^ m)
              - algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I)
                  * algebraMap ℂ 𝒜 ((s : ℂ) * Complex.I) := by noncomm_ring
          _ = a ^ m * a ^ m - algebraMap ℂ 𝒜 z := by
              rw [hcomm, ← map_mul, hsq]
              abel
      rw [← he]
      exact h1.mul h2
    · -- `λ ∉ ℝ`: part 1, applied to the self-adjoint element `aⁿ`
      exact spectrum_self_adjoint_real_1 (a ^ n) (ha.pow n) z him

/-- Auxiliary for **11XV**.3: the solution's factorisation of `Xⁿ + 1` over `ℂ`
(asols.tex, `parsec-110.150`(3), whose hint's sign the erratum
`parsec-110.150` corrects).  With `α = e^{πi/n}` the `n` roots of `Xⁿ + 1`
are the `α^{2k+1}` for `0 ≤ k < n`; the one at `2k+1 = n` is `α^n = -1`,
contributing the factor `X + 1`, and every other one is non-real. -/
private theorem X_pow_add_one_eq_mul_prod (n : ℕ) (hn : Odd n) :
    ∃ (s : Finset ℕ) (w : ℕ → ℂ), (∀ i ∈ s, (w i).im ≠ 0) ∧
      (Polynomial.X : Polynomial ℂ) ^ n + 1
        = (Polynomial.X + 1) * ∏ i ∈ s, (Polynomial.X - Polynomial.C (w i)) := by
  classical
  obtain ⟨m, hm⟩ := hn
  have hn0 : 0 < n := by omega
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  set α : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / (n : ℂ)) with hαdef
  -- `α ^ j = e^{jπi/n}`, so its imaginary part is `sin (jπ/n)`
  have hpow : ∀ j : ℕ,
      α ^ j = Complex.exp ((((j : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro j
    rw [hαdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hαn : α ^ n = -1 := by
    rw [hαdef, ← Complex.exp_nat_mul,
      show (n : ℂ) * ((Real.pi : ℂ) * Complex.I / (n : ℂ)) = (Real.pi : ℂ) * Complex.I by
        field_simp]
    exact Complex.exp_pi_mul_I
  -- `α²` is a primitive `n`-th root of unity, and `α ^ n = -1`, so
  -- `Xⁿ + 1 = ∏_{i<n} (X - (α²)ⁱ α)` — and `(α²)ⁱ α = α^{2i+1}`
  have hprim : IsPrimitiveRoot (α ^ 2) n := by
    have hsq : α ^ 2 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := by
      rw [hαdef, sq, ← Complex.exp_add]
      congr 1
      ring
    rw [hsq]
    exact Complex.isPrimitiveRoot_exp n hn0.ne'
  have hfac := X_pow_sub_C_eq_prod hprim hn0 hαn
  have hC : (Polynomial.C (-1 : ℂ)) = -1 := by simp
  rw [hC, sub_neg_eq_add] at hfac
  have hidx : ∀ i : ℕ, (α ^ 2) ^ i * α = α ^ (2 * i + 1) := by
    intro i
    rw [← pow_mul, ← pow_succ]
  simp only [hidx] at hfac
  have hmem : m ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  -- every root but `α ^ n` is non-real: `Im α^{2i+1} = sin((2i+1)π/n)`, which
  -- vanishes only if `n ∣ 2i+1`, and `0 < 2i+1 < 2n` then forces `2i+1 = n`
  have hw : ∀ i ∈ (Finset.range n).erase m, (α ^ (2 * i + 1)).im ≠ 0 := by
    intro i hi
    obtain ⟨hine, hir⟩ := Finset.mem_erase.mp hi
    have hilt : i < n := Finset.mem_range.mp hir
    rw [hpow (2 * i + 1), Complex.exp_ofReal_mul_I_im]
    intro h0
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h0
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have h3 : ((k : ℝ) * Real.pi) * (n : ℝ) = ((2 * i + 1 : ℕ) : ℝ) * Real.pi := by
      rw [hk]; field_simp
    have hkn : (k : ℝ) * (n : ℝ) = ((2 * i + 1 : ℕ) : ℝ) := by
      apply mul_right_cancel₀ hpi
      rw [← h3]; ring
    have hkz : k * (n : ℤ) = 2 * (i : ℤ) + 1 := by exact_mod_cast hkn
    have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn0
    have hiz : (i : ℤ) < (n : ℤ) := by exact_mod_cast hilt
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hk1 : k = 1 := by
      rcases lt_trichotomy k 1 with hlt | heq | hgt
      · exfalso
        have hle : k * (n : ℤ) ≤ 0 * (n : ℤ) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hnz)
        rw [zero_mul] at hle
        linarith
      · exact heq
      · exfalso
        have hle : (2 : ℤ) * (n : ℤ) ≤ k * (n : ℤ) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hnz)
        linarith
    rw [hk1, one_mul] at hkz
    have hmz : (n : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
    exact hine (by omega)
  have hprod : (Polynomial.X : Polynomial ℂ) ^ n + 1
      = (Polynomial.X + 1) * ∏ i ∈ (Finset.range n).erase m,
          (Polynomial.X - Polynomial.C (α ^ (2 * i + 1))) := by
    rw [hfac, ← Finset.mul_prod_erase _ _ hmem]
    congr 1
    show Polynomial.X - Polynomial.C (α ^ (2 * m + 1)) = Polynomial.X + 1
    rw [show 2 * m + 1 = n from hm.symm, hαn]
    simp
  exact ⟨(Finset.range n).erase m, fun i => α ^ (2 * i + 1), hw, hprod⟩

/-- Auxiliary for **11XV**.3: a product of factors `b - λ` with every `λ`
non-real is invertible, by part 1. -/
private theorem isUnit_aeval_prod {b : 𝒜} (hb : IsSelfAdjoint b) (w : ℕ → ℂ)
    (s : Finset ℕ) (hw : ∀ i ∈ s, (w i).im ≠ 0) :
    IsUnit (Polynomial.aeval b (∏ i ∈ s, (Polynomial.X - Polynomial.C (w i)))) := by
  classical
  revert hw
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert j t hj ih =>
      intro hw
      rw [Finset.prod_insert hj, map_mul]
      refine IsUnit.mul ?_ (ih fun i hi => hw i (Finset.mem_insert_of_mem hi))
      have h1 : Polynomial.aeval b (Polynomial.X - Polynomial.C (w j))
          = b - algebraMap ℂ 𝒜 (w j) := by simp
      rw [h1]
      exact spectrum_self_adjoint_real_1 b hb (w j) (hw j (Finset.mem_insert_self j t))

/-- Auxiliary for **11XV**.3, the heart of the solution's argument: for
self-adjoint `b` and odd `n`, `b + 1` is invertible iff `bⁿ + 1` is.  Indeed
`bⁿ + 1 = (b + 1) · ∏_{2k+1 ≠ n} (b - α^{2k+1})` with `α = e^{πi/n}`, and
every factor of that product is invertible by part 1. -/
private theorem isUnit_add_one_iff_pow_add_one {b : 𝒜} (hb : IsSelfAdjoint b) (n : ℕ)
    (hn : Odd n) : IsUnit (b + 1) ↔ IsUnit (b ^ n + 1) := by
  obtain ⟨s, w, hw, hfac⟩ := X_pow_add_one_eq_mul_prod n hn
  obtain ⟨u, hu⟩ := isUnit_aeval_prod hb w s hw
  have hmul : b ^ n + 1 = (b + 1) * (u : 𝒜) := by
    have h := congrArg (Polynomial.aeval b) hfac
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_one] at h
    rw [h, hu]
  constructor
  · intro h
    rw [hmul]
    exact h.mul u.isUnit
  · intro h
    have hcancel : (b ^ n + 1) * ((u⁻¹ : 𝒜ˣ) : 𝒜) = b + 1 := by
      rw [hmul, mul_assoc, u.mul_inv, mul_one]
    rw [← hcancel]
    exact h.mul u⁻¹.isUnit

/-- **11XV** (`spectrum-self-adjoint-real`, cstar.tex:1570, Exercise),
part 3: for self-adjoint `a` and *odd* `n`: `aⁿ - λ` is invertible for all
`λ ∈ ℂ \ [0,∞)` iff `a - λ` is invertible for all `λ ∈ ℂ \ [0,∞)`. -/
theorem spectrum_self_adjoint_real_3 (a : 𝒜) (ha : IsSelfAdjoint a)
    (n : ℕ) (hn : Odd n) :
    (∀ z : ℂ, (∀ r : ℝ, 0 ≤ r → z ≠ r) → IsUnit (a ^ n - algebraMap ℂ 𝒜 z)) ↔
      (∀ z : ℂ, (∀ r : ℝ, 0 ≤ r → z ≠ r) → IsUnit (a - algebraMap ℂ 𝒜 z)) :=
  by
    -- the solution's own argument: for `λ ∉ ℝ` both sides hold by part 1, so
    -- only `λ = -t` with `t > 0` is at issue; there `a + t = t·(b+1)` and
    -- `aⁿ + tⁿ = tⁿ·(bⁿ+1)` for `b := a/t`, and `b + 1` is invertible iff
    -- `bⁿ + 1` is, by the factorisation `bⁿ + 1 = ∏ₖ (b - ζ^{2k+1})`.
    have hn0 : 0 < n := hn.pos
    have hcancel : ∀ (c : ℂ) (x : 𝒜), c ≠ 0 →
        (IsUnit (algebraMap ℂ 𝒜 c * x) ↔ IsUnit x) := by
      intro c x hc
      obtain ⟨v, hv⟩ := (Ne.isUnit hc).map (algebraMap ℂ 𝒜)
      rw [← hv]
      exact Units.isUnit_units_mul v x
    -- a real `λ ∉ [0,∞)` is `-t` with `t > 0`
    have hreal : ∀ z : ℂ, z.im = 0 → (∀ r : ℝ, 0 ≤ r → z ≠ r) →
        ∃ t : ℝ, 0 < t ∧ z = -((t : ℝ) : ℂ) := by
      intro z him hz
      have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
      have hneg : z.re < 0 := by
        by_contra hcon
        push_neg at hcon
        exact hz z.re hcon hzr
      refine ⟨-z.re, by linarith, ?_⟩
      conv_lhs => rw [hzr]
      push_cast
      ring
    -- the solution's scaling step: for `t > 0`, `a + t` is invertible iff
    -- `aⁿ + tⁿ` is, since both are `t^·` times `b + 1` resp. `bⁿ + 1`
    have key : ∀ t : ℝ, 0 < t →
        (IsUnit (a + algebraMap ℂ 𝒜 ((t : ℝ) : ℂ)) ↔
          IsUnit (a ^ n + algebraMap ℂ 𝒜 (((t ^ n : ℝ)) : ℂ))) := by
      intro t ht
      have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hcast : (((t ^ n : ℝ)) : ℂ) = ((t : ℝ) : ℂ) ^ n := by push_cast; ring
      have htnc : (((t ^ n : ℝ)) : ℂ) ≠ 0 := by rw [hcast]; exact pow_ne_zero n htc
      have hinvsa : IsSelfAdjoint (algebraMap ℂ 𝒜 (((t : ℝ) : ℂ))⁻¹) := by
        show star _ = _
        rw [← algebraMap_star_comm]
        simp
      set b : 𝒜 := algebraMap ℂ 𝒜 (((t : ℝ) : ℂ))⁻¹ * a with hbdef
      have hbsa : IsSelfAdjoint b := by
        rw [hbdef]
        show star _ = _
        rw [star_mul, ha.star_eq, hinvsa.star_eq, Algebra.commutes]
      have hab : algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) * b = a := by
        rw [hbdef, ← mul_assoc, ← map_mul, mul_inv_cancel₀ htc, map_one, one_mul]
      have hcomm : Commute (algebraMap ℂ 𝒜 ((t : ℝ) : ℂ)) b :=
        Algebra.commute_algebraMap_left _ _
      have h1 : a + algebraMap ℂ 𝒜 ((t : ℝ) : ℂ)
          = algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) * (b + 1) := by
        rw [mul_add, mul_one, hab]
      have h2 : a ^ n + algebraMap ℂ 𝒜 (((t ^ n : ℝ)) : ℂ)
          = algebraMap ℂ 𝒜 (((t ^ n : ℝ)) : ℂ) * (b ^ n + 1) := by
        rw [mul_add, mul_one, hcast, map_pow, ← hcomm.mul_pow, hab]
      rw [h1, h2, hcancel _ (b + 1) htc, hcancel _ (b ^ n + 1) htnc]
      exact isUnit_add_one_iff_pow_add_one hbsa n hn
    constructor
    · -- `aⁿ - λ` invertible for all `λ ∉ [0,∞)` gives the same for `a - λ`
      intro h z hz
      by_cases him : z.im = 0
      · obtain ⟨t, ht, rfl⟩ := hreal z him hz
        have hsub : a - algebraMap ℂ 𝒜 (-((t : ℝ) : ℂ))
            = a + algebraMap ℂ 𝒜 ((t : ℝ) : ℂ) := by
          rw [map_neg, sub_neg_eq_add]
        rw [hsub, key t ht]
        have hz' : ∀ r : ℝ, 0 ≤ r → (-(((t ^ n : ℝ)) : ℂ)) ≠ (r : ℂ) := by
          intro r hr hcon
          have hr' : -(t ^ n) = r := by exact_mod_cast hcon
          have : (0 : ℝ) < t ^ n := pow_pos ht n
          linarith
        have hfin := h (-(((t ^ n : ℝ)) : ℂ)) hz'
        rwa [map_neg, sub_neg_eq_add] at hfin
      · exact spectrum_self_adjoint_real_1 a ha z him
    · -- and conversely; here `t > 0` is written as `sⁿ` with `s > 0`
      intro h z hz
      by_cases him : z.im = 0
      · obtain ⟨t, ht, rfl⟩ := hreal z him hz
        obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ t = s ^ n :=
          ⟨t ^ ((n : ℝ))⁻¹, Real.rpow_pos_of_pos ht _,
            (Real.rpow_inv_natCast_pow ht.le hn0.ne').symm⟩
        have hsub : a ^ n - algebraMap ℂ 𝒜 (-(((s ^ n : ℝ)) : ℂ))
            = a ^ n + algebraMap ℂ 𝒜 (((s ^ n : ℝ)) : ℂ) := by
          rw [map_neg, sub_neg_eq_add]
        rw [hsub, ← key s hs]
        have hz' : ∀ r : ℝ, 0 ≤ r → (-((s : ℝ) : ℂ)) ≠ (r : ℂ) := by
          intro r hr hcon
          have hr' : -s = r := by exact_mod_cast hcon
          linarith
        have hfin := h (-((s : ℝ) : ℂ)) hz'
        rwa [map_neg, sub_neg_eq_add] at hfin
      · exact spectrum_self_adjoint_real_1 (a ^ n) (ha.pow n) z him

variable {ℬ : Type*} [CStarAlgebra ℬ]

/-- **11XVI** (`inverse-permanence`, cstar.tex:1595, Proposition): if a
self-adjoint element `a` of a closed ∗-subalgebra `𝒮` of a C*-algebra `ℬ`
has an inverse in `ℬ`, then `a⁻¹ ∈ 𝒮`.

The proof is the thesis's own: `a + i/n` is invertible *in `𝒮`* — which is
itself a C*-algebra — by **11XV**.1, since `a` is self-adjoint; those
inverses converge to `a⁻¹` in `ℬ` by **11X**; and `𝒮` is closed. -/
theorem inverse_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : ℬ) (ha : a ∈ 𝒮)
    (hsa : IsSelfAdjoint a) (hu : IsUnit a) :
    Ring.inverse a ∈ 𝒮 :=
  by
    haveI : CompleteSpace 𝒮 := h𝒮.completeSpace_coe
    -- the shifts `a + i/(n+1)`, as elements of `𝒮` and of `ℬ`
    set z : ℕ → ℂ := fun n => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I with hz
    have hmemS : ∀ n : ℕ, a + algebraMap ℂ ℬ (z n) ∈ 𝒮 :=
      fun n => add_mem ha (algebraMap_mem 𝒮 _)
    have hbsa : IsSelfAdjoint (⟨a, ha⟩ : 𝒮) := Subtype.ext hsa
    have him : ∀ n : ℕ, (-z n).im ≠ 0 := by
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp only [hz, Complex.neg_im, Complex.im_ofReal_mul, Complex.I_im, mul_one]
      simpa using ne_of_gt (inv_pos.mpr hpos)
    have hsub : ∀ n, ((⟨a, ha⟩ : 𝒮) - algebraMap ℂ 𝒮 (-z n) : 𝒮)
        = (⟨a + algebraMap ℂ ℬ (z n), hmemS n⟩ : 𝒮) := by
      intro n
      ext
      simp [sub_eq_add_neg, ← map_neg]
    -- each shift is invertible in `𝒮`, by 11XV.1 applied inside the C*-algebra `𝒮`
    -- (this is the only place the self-adjointness of `a` is used)
    have hbu : ∀ n : ℕ, IsUnit ((⟨a + algebraMap ℂ ℬ (z n), hmemS n⟩ : 𝒮)) := by
      intro n
      have h := spectrum_self_adjoint_real_1 (⟨a, ha⟩ : 𝒮) hbsa (-z n) (him n)
      rwa [hsub n] at h
    have hunit : ∀ n : ℕ, IsUnit (a + algebraMap ℂ ℬ (z n)) := fun n => by
      simpa using (hbu n).map (𝒮.subtype)
    -- their inverses lie in `𝒮`
    have hmem : ∀ n : ℕ, Ring.inverse (a + algebraMap ℂ ℬ (z n)) ∈ 𝒮 := by
      intro n
      obtain ⟨u, hu2⟩ := hbu n
      have hau : ((u : 𝒮) : ℬ) = a + algebraMap ℂ ℬ (z n) := congrArg Subtype.val hu2
      have h1 : (a + algebraMap ℂ ℬ (z n)) * ((↑(u⁻¹) : 𝒮) : ℬ) = 1 := by
        rw [← hau, ← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
      have key : Ring.inverse (a + algebraMap ℂ ℬ (z n)) = ((↑(u⁻¹) : 𝒮) : ℬ) := by
        calc Ring.inverse (a + algebraMap ℂ ℬ (z n))
            = Ring.inverse (a + algebraMap ℂ ℬ (z n))
                * ((a + algebraMap ℂ ℬ (z n)) * ((↑(u⁻¹) : 𝒮) : ℬ)) := by rw [h1, mul_one]
          _ = (Ring.inverse (a + algebraMap ℂ ℬ (z n)) * (a + algebraMap ℂ ℬ (z n)))
                * ((↑(u⁻¹) : 𝒮) : ℬ) := (mul_assoc _ _ _).symm
          _ = ((↑(u⁻¹) : 𝒮) : ℬ) := by
              rw [Ring.inverse_mul_cancel _ (hunit n), one_mul]
      rw [key]
      exact SetLike.coe_mem _
    -- and converge to `a⁻¹`
    have hz0 : Filter.Tendsto z Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : ∀ n : ℕ, ‖z n‖ = 1 / ((n : ℝ) + 1) := by
        intro n
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [hz]
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos), one_div]
      simpa only [this] using tendsto_one_div_add_atTop_nhds_zero_nat
    have hshift : Filter.Tendsto (fun n : ℕ => a + algebraMap ℂ ℬ (z n))
        Filter.atTop (nhds a) := by
      have hc : Filter.Tendsto (fun n : ℕ => algebraMap ℂ ℬ (z n)) Filter.atTop (nhds 0) := by
        have h := ((continuous_algebraMap ℂ ℬ).tendsto (0 : ℂ)).comp hz0
        rw [map_zero] at h
        exact h
      simpa using Filter.Tendsto.const_add a hc
    have hlim : Filter.Tendsto (fun n : ℕ => Ring.inverse (a + algebraMap ℂ ℬ (z n)))
        Filter.atTop (nhds (Ring.inverse a)) := by
      have hcont : ContinuousAt (Ring.inverse : ℬ → ℬ) a := by
        have h := NormedRing.inverse_continuousAt (R := ℬ) hu.unit
        rwa [hu.unit_spec] at h
      exact hcont.tendsto.comp hshift
    exact h𝒮.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

/-- **11XVIII** (`improved-inverse-permanence`, cstar.tex:1616, Exercise):
the self-adjointness assumption in **11XVI** may be dropped.  Following the
exercise's hint, we apply **11XVI** to the self-adjoint element `a* a`. -/
theorem improved_inverse_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : ℬ) (ha : a ∈ 𝒮) (hu : IsUnit a) :
    Ring.inverse a ∈ 𝒮 :=
  by
    have hstar : star a ∈ 𝒮 := star_mem ha
    have h1 : IsUnit (star a * a) := (hu.star).mul hu
    have h2 : Ring.inverse (star a * a) ∈ 𝒮 :=
      inverse_permanence 𝒮 h𝒮 (star a * a) (mul_mem hstar ha)
        (IsSelfAdjoint.star_mul_self a) h1
    have key : Ring.inverse a = Ring.inverse (star a * a) * star a := by
      have hleft : (Ring.inverse (star a * a) * star a) * a = 1 := by
        rw [mul_assoc]
        exact Ring.inverse_mul_cancel _ h1
      calc Ring.inverse a = ((Ring.inverse (star a * a) * star a) * a) * Ring.inverse a := by
            rw [hleft, one_mul]
        _ = (Ring.inverse (star a * a) * star a) * (a * Ring.inverse a) := by
            rw [mul_assoc]
        _ = Ring.inverse (star a * a) * star a := by
            rw [Ring.mul_inverse_cancel a hu, mul_one]
    rw [key]
    exact mul_mem h2 hstar

/-! **11XIX** (`spectrum-of-element`, cstar.tex:1623, Definition): the
*spectrum* of `a` is the set of `λ ∈ ℂ` for which `a - λ` is not
invertible — Mathlib's `spectrum ℂ a`. -/

/-- **11XX** (cstar.tex:1633, Exercise), part 1: the spectrum of a
continuous function `f`, as an element of the C*-algebra `C(X)`, is its
image.  (Mathlib has this as `ContinuousMap.spectrum_eq_range`; the proof
below is the solution's own chain, through **9III**.) -/
theorem spectrum_continuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (f : C(X, ℂ)) :
    spectrum ℂ f = Set.range f := by
  -- the solution's chain, through **9III** `cx_mem_range_iff_not_isUnit`
  ext z
  rw [spectrum.mem_iff, ← neg_sub f (algebraMap ℂ C(X, ℂ) z), IsUnit.neg_iff,
    ← cx_mem_range_iff_not_isUnit]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩⟩

/-- **11XX** (cstar.tex:1633, Exercise), part 2: the spectrum of a square
matrix `A ∈ Mₙ` is its set of eigenvalues. -/
theorem spectrum_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A = {z : ℂ | ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = z • v} :=
  by
    ext z
    have key : ∀ v : Fin n → ℂ,
        (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z - A).mulVec v = 0 ↔
          A.mulVec v = z • v := by
      intro v
      rw [Matrix.sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      exact eq_comm
    rw [Set.mem_setOf_eq, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff]
    exact exists_congr fun v => and_congr_right fun _ => key v

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 1: the
spectrum of a self-adjoint element is real. -/
theorem spectrum_basic_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ a ⊆ Set.range ((↑) : ℝ → ℂ) :=
  by
    intro z hz
    exact ⟨z.re, (mem_spectrum_eq_re_of_isSelfAdjoint ha hz).symm⟩

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 1
(counterexample): the converse fails, e.g. `spec [[0,2],[0,0]] = {0}`
while the matrix is not self-adjoint. -/
theorem spectrum_basic_1' :
    spectrum ℂ (!![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = {0} :=
  by
    -- the solution's own argument (asols.tex, `parsec-110.210`(1)): "we must
    -- show that `0` is the only eigenvalue of `(0 2; 0 0)`, that is, that `0`
    -- is the only root of the characteristic polynomial
    -- `det((0 2; 0 0) - λ) = λ²`, which is so."
    ext z
    rw [Set.mem_singleton_iff, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not]
    have hdet : (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z
        - !![0, 2; 0, 0]).det = z ^ 2 := by
      have hmat : (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z
          - !![0, 2; 0, 0]) = !![z, -2; 0, z] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one]
      rw [hmat, Matrix.det_fin_two_of]
      ring
    rw [hdet, pow_eq_zero_iff two_ne_zero]

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 1
(counterexample), the clause that makes it one: `(0 2; 0 0)` is *not*
self-adjoint.  Without this, `spectrum_basic_1'` is only a computation; with
it the pair witnesses the Exercise's claim that the converse of part 1 — that
a real spectrum forces self-adjointness — does not hold. -/
theorem spectrum_basic_1'_not_isSelfAdjoint :
    ¬ IsSelfAdjoint (!![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) :=
  by
    intro h
    -- the `(0,1)` entry of `M* = M` reads `star (M 1 0) = M 0 1`, i.e. `0 = 2`
    have h01 := congrFun (congrFun h.star_eq 0) 1
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h01
    norm_num at h01

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 2:
`spec(a²) ⊆ [0,∞)` for self-adjoint `a`. -/
theorem spectrum_basic_2 (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ (a ^ 2) ⊆ {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = r} :=
  by
    -- as the thesis has it: this is **11XV**.2 for `n = 2`
    intro z hz
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have hne : ∀ r : ℝ, 0 ≤ r → z ≠ r := fun r hr => hcon r hr
    exact (spectrum.mem_iff.mp hz)
      (by simpa using (spectrum_self_adjoint_real_2 a ha 2 even_two z hne).neg)

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 3:
`|λ| ≤ ‖a‖` for every `λ ∈ spec(a)`. -/
theorem spectrum_basic_3 (a : 𝒜) (z : ℂ) (hz : z ∈ spectrum ℂ a) :
    ‖z‖ ≤ ‖a‖ :=
  by
    -- as the thesis has it: this is the contrapositive of **11VI**.1
    by_contra hcon
    push_neg at hcon
    exact (spectrum.mem_iff.mp hz) (by simpa using (spectrum_bounded_1 a z hcon).neg)

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 4: the
spectrum is closed, hence compact. -/
theorem spectrum_basic_4 (a : 𝒜) :
    IsClosed (spectrum ℂ a) ∧ IsCompact (spectrum ℂ a) :=
  by
    -- the thesis's own order: closed because the invertibles are open (**11VI**.3),
    -- and compact because it is closed and bounded (part 3)
    have hpre : spectrum ℂ a
        = (fun z : ℂ => algebraMap ℂ 𝒜 z - a) ⁻¹' {b : 𝒜 | IsUnit b}ᶜ := by
      ext z
      simp [spectrum.mem_iff]
    have hclosed : IsClosed (spectrum ℂ a) := by
      rw [hpre]
      exact spectrum_bounded_3.isClosed_compl.preimage
        ((continuous_algebraMap ℂ 𝒜).sub continuous_const)
    refine ⟨hclosed, Metric.isCompact_of_isClosed_isBounded hclosed ?_⟩
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := ‖a‖)).subset fun z hz => ?_
    simpa using spectrum_basic_3 a z hz

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 5:
`spec(a + z) = { λ + z : λ ∈ spec(a) }` for `z ∈ ℂ`. -/
theorem spectrum_basic_5 (a : 𝒜) (z : ℂ) :
    spectrum ℂ (a + algebraMap ℂ 𝒜 z) = (fun w => w + z) '' spectrum ℂ a :=
  by
    have hEq : ∀ w : ℂ, algebraMap ℂ 𝒜 w - (a + algebraMap ℂ 𝒜 z)
        = algebraMap ℂ 𝒜 (w - z) - a := by
      intro w
      rw [map_sub]
      abel
    ext w
    simp only [Set.mem_image, spectrum.mem_iff, hEq]
    constructor
    · intro hw
      exact ⟨w - z, hw, by ring⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv

/-- **11XXI** (`spectrum-basic`, cstar.tex:1649, Exercise), part 6:
`spec(a⁻¹) = { λ⁻¹ : λ ∈ spec(a) }` for invertible `a`. -/
theorem spectrum_basic_6 (a : 𝒜ˣ) :
    spectrum ℂ ((a⁻¹ : 𝒜ˣ) : 𝒜) = (fun z => z⁻¹) '' spectrum ℂ (a : 𝒜) := by
  -- the solution's factorisation `λ - a = λ a (a⁻¹ - λ⁻¹)`, here with `λ = w⁻¹`
  have key : ∀ w : ℂ, w ≠ 0 →
      (w ∈ spectrum ℂ ((a⁻¹ : 𝒜ˣ) : 𝒜) ↔ w⁻¹ ∈ spectrum ℂ (a : 𝒜)) := by
    intro w hw
    have hcomm : algebraMap ℂ 𝒜 w⁻¹ * (a : 𝒜) * algebraMap ℂ 𝒜 w = (a : 𝒜) := by
      rw [Algebra.commutes w⁻¹ ((a : 𝒜)), mul_assoc, ← map_mul, inv_mul_cancel₀ hw,
        map_one, mul_one]
    have hfac : algebraMap ℂ 𝒜 w⁻¹ * (a : 𝒜) * (((a⁻¹ : 𝒜ˣ) : 𝒜) - algebraMap ℂ 𝒜 w)
        = algebraMap ℂ 𝒜 w⁻¹ - (a : 𝒜) := by
      rw [mul_sub, hcomm, mul_assoc, Units.mul_inv, mul_one]
    have hwu : IsUnit (algebraMap ℂ 𝒜 w⁻¹) :=
      (Ne.isUnit (inv_ne_zero hw)).map (algebraMap ℂ 𝒜)
    obtain ⟨u, hu⟩ := hwu.mul a.isUnit
    rw [spectrum.mem_iff, spectrum.mem_iff, ← hfac, ← hu, Units.isUnit_units_mul,
      ← IsUnit.neg_iff, neg_sub]
  ext w
  constructor
  · intro hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact spectrum.not_isUnit_of_zero_mem (R := ℂ) hw (a⁻¹ : 𝒜ˣ).isUnit
    exact ⟨w⁻¹, (key w hw0).mp hw, inv_inv w⟩
  · rintro ⟨v, hv, rfl⟩
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact spectrum.not_isUnit_of_zero_mem (R := ℂ) hv a.isUnit
    exact (key v⁻¹ (inv_ne_zero hv0)).mpr (by rwa [inv_inv])

/-- **11XXIII** (`spectral-permanence`, cstar.tex:1695, Theorem (Spectral
Permanence)): for a closed ∗-subalgebra `𝒮` of a C*-algebra `ℬ` and
`a ∈ 𝒮`, the spectrum of `a` computed in `𝒮` equals the one computed in
`ℬ`.

This is, as in the thesis, an immediate consequence of **11XVIII**: if
`z - a` is invertible in `ℬ` then its inverse already lies in `𝒮`, so it is
invertible in `𝒮`; the other inclusion is the inclusion `𝒮 ⊆ ℬ`.
(Mathlib proves the same theorem as `StarSubalgebra.spectrum_eq`, by a
different route — through connectedness of the complement of the spectrum
of a self-adjoint element.) -/
theorem spectral_permanence (𝒮 : StarSubalgebra ℂ ℬ)
    (h𝒮 : IsClosed (𝒮 : Set ℬ)) (a : 𝒮) :
    spectrum ℂ (a : ℬ) = spectrum ℂ a :=
  by
    have hcoe : ∀ z : ℂ, ((algebraMap ℂ 𝒮 z - a : 𝒮) : ℬ) = algebraMap ℂ ℬ z - (a : ℬ) :=
      fun z => by push_cast; rfl
    have key : ∀ z : ℂ,
        IsUnit (algebraMap ℂ ℬ z - (a : ℬ)) ↔ IsUnit (algebraMap ℂ 𝒮 z - a) := by
      intro z
      constructor
      · intro hu
        -- **11XVIII**: the inverse of `z - a`, taken in `ℬ`, lies in `𝒮`
        have hmem : Ring.inverse (algebraMap ℂ ℬ z - (a : ℬ)) ∈ 𝒮 :=
          improved_inverse_permanence 𝒮 h𝒮 _ (by rw [← hcoe z]; exact SetLike.coe_mem _) hu
        refine ⟨⟨algebraMap ℂ 𝒮 z - a, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
        · apply Subtype.ext
          rw [MulMemClass.coe_mul, OneMemClass.coe_one, hcoe z]
          exact Ring.mul_inverse_cancel _ hu
        · apply Subtype.ext
          rw [MulMemClass.coe_mul, OneMemClass.coe_one, hcoe z]
          exact Ring.inverse_mul_cancel _ hu
      · intro hu
        have h : IsUnit ((algebraMap ℂ 𝒮 z - a : 𝒮) : ℬ) := hu.map 𝒮.subtype
        rwa [hcoe z] at h
    ext z
    simp only [spectrum.mem_iff]
    exact not_congr (key z)

end Invertibles

end Theses.A.CStar
