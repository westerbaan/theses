/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 5953–6742.

  §Towards von Neumann Algebras
    Directed Suprema    (parsec 350: uniform boundedness, Hellinger–Toeplitz;
                         parsec 360: self-dual Hilbert 𝒜-modules, bounded forms;
                         parsec 370: the weak operator topology, suprema of
                         bounded directed sets of self-adjoint operators)
    Normal Functionals  (parsec 380: normal functionals on B(H);
                         parsec 390: orthonormal bases, and the theorem that
                         every normal positive functional on B(H) is a sum of
                         vector functionals)
    parsec 400: closing remarks (nothing to formalize).

All statements of parsecs 350–400 are proved.  See CONVENTIONS.md for the
numbering (**35II** = parsec 350, point 20) and naming conventions.
-/
import Theses.Common
import Theses.A.CStar.Representation

open scoped ComplexOrder ComplexInnerProductSpace lp
open Filter Topology

namespace Theses.A.CStar

/-! ## Parsec 350: Directed suprema — uniform boundedness and Hellinger–Toeplitz

**35I** (cstar.tex:5987): introduction — B(H) has suprema of norm-bounded
directed sets of self-adjoint operators, the vector functionals preserve them,
and every functional preserving them is a sum of vector functionals (39IX
below).  Nothing to formalize. -/

section UniformBoundedness

variable {𝒳 𝒴 : Type*} [NormedAddCommGroup 𝒳] [NormedSpace ℂ 𝒳]
  [NormedAddCommGroup 𝒴] [NormedSpace ℂ 𝒴]

/-- **35II** (`pub`, cstar.tex:6015, Theorem (Uniform Boundedness)): a family
`F` of bounded linear maps from a complete normed vector space `𝒳` to a normed
vector space `𝒴` is bounded, `sup_T ‖T‖ < ∞`, provided that `sup_T ‖T x‖ < ∞`
for every `x ∈ 𝒳`.  Mathlib: `banach_steinhaus`. -/
theorem pub [CompleteSpace 𝒳] {ι : Type*} (F : ι → 𝒳 →L[ℂ] 𝒴)
    (h : ∀ x : 𝒳, BddAbove (Set.range fun i => ‖F i x‖)) :
    BddAbove (Set.range fun i => ‖F i‖) := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := F) (fun x => by
    obtain ⟨C, hC⟩ := h x
    exact ⟨C, fun i => hC (Set.mem_range_self i)⟩)
  exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩

end UniformBoundedness

section HilbertModules

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {X Y : Type*}
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒜 X] [CStarModule 𝒜 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒜 Y] [CStarModule 𝒜 Y]

/-- Additivity of the 𝒜-valued inner product in its first argument.
(Auxiliary for **35VI** and **36V**.) -/
private theorem inner_add_left' (a b c : X) :
    inner 𝒜 (a + b) c = inner 𝒜 a c + inner 𝒜 b c := by
  rw [← CStarModule.star_inner (A := 𝒜), CStarModule.inner_add_right, star_add,
    CStarModule.star_inner, CStarModule.star_inner]

/-- Conjugate-homogeneity of the 𝒜-valued inner product in its first argument.
(Auxiliary for **35VI** and **36V**.) -/
private theorem inner_smul_left' (z : ℂ) (a c : X) :
    inner 𝒜 (z • a) c = (starRingEnd ℂ) z • inner 𝒜 a c := by
  rw [← CStarModule.star_inner (A := 𝒜), CStarModule.inner_smul_right_complex, star_smul,
    CStarModule.star_inner]
  rfl

/-- Definiteness: the 𝒜-valued inner product separates the points of a
pre-Hilbert 𝒜-module.  (Auxiliary for **35VI** and **36V**.) -/
private theorem ext_inner_left' {a b : X} (h : ∀ c : X, inner 𝒜 a c = inner 𝒜 b c) :
    a = b := by
  have hsub : ∀ c : X, inner 𝒜 (a - b) c = 0 := by
    intro c
    have h1 : a - b = a + ((-1 : ℂ) • b) := by
      rw [neg_one_smul]; exact (sub_eq_add_neg a b)
    rw [h1, inner_add_left' (𝒜 := 𝒜), inner_smul_left' (𝒜 := 𝒜), h c]
    simp
  exact sub_eq_zero.mp (CStarModule.inner_self.mp (hsub (a - b)))

/-- Auxiliary for **35VI**: an adjointable map between pre-Hilbert
𝒜-modules is automatically ℂ-linear.  This is the clause **32I** flags when it
says that an adjointable map "must be linear, and a module map": the inner
product is definite, so `T (x + x')` and `T x + T x'` — which have the same
inner product with every `y ∈ Y`, by adjointness and additivity of the inner
product on `X` — are equal.  (Compare `adjointCLM` in `A/CStar/Basic`, which
does the same for `𝒜 = ℂ` in the proof of **4XVI**.) -/
private theorem linear_of_isAdjointTo {T : X → Y} {S : Y → X}
    (adj : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) :
    ∃ T' : X →ₗ[ℂ] Y, ⇑T' = T := by
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, rfl⟩
  · intro x x'
    refine ext_inner_left' (𝒜 := 𝒜) fun y => ?_
    rw [adj, inner_add_left' (𝒜 := 𝒜), ← adj, ← adj, inner_add_left' (𝒜 := 𝒜)]
  · intro c x
    refine ext_inner_left' (𝒜 := 𝒜) fun y => ?_
    rw [RingHom.id_apply, adj, inner_smul_left' (𝒜 := 𝒜), ← adj,
      inner_smul_left' (𝒜 := 𝒜)]

/-- Auxiliary for **35VI**: the adjointness relation is symmetric in `(T, X)`
and `(S, Y)` — take the star of both sides (**32I**). -/
private theorem isAdjointTo_swap' {T : X → Y} {S : Y → X}
    (adj : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) :
    ∀ (y : Y) (x : X), inner 𝒜 (S y) x = inner 𝒜 y (T x) := by
  intro y x
  rw [← CStarModule.star_inner (A := 𝒜) x (S y), ← adj, CStarModule.star_inner]

/-- Auxiliary for **35VI**: the case in which the *domain* `X` is complete.
The public statement below takes either completeness hypothesis and reduces
the second to this one by `isAdjointTo_swap'`. -/
private theorem hellinger_toeplitz_aux [CompleteSpace X] (T : X → Y) (S : Y → X)
    (adj : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) :
    Continuous T ∧ Continuous S := by
  -- Mathlib deliberately does not register `NormedSpace ℂ X` for a `CStarModule`
  -- (it wants to be able to replace the topology); the norm axiom is available
  -- as `CStarModule.normedSpaceCore`, and for the *given* norm on `X` it gives
  -- exactly the missing instance.
  letI : NormSMulClass ℂ X :=
    ⟨fun c x => (CStarModule.normedSpaceCore 𝒜 (E := X)).norm_smul c x⟩
  letI : NormSMulClass ℂ Y :=
    ⟨fun c y => (CStarModule.normedSpaceCore 𝒜 (E := Y)).norm_smul c y⟩
  letI : NormedSpace ℂ X := { norm_smul_le := fun c x => le_of_eq (norm_smul c x) }
  letI : NormedSpace ℂ Y := { norm_smul_le := fun c y => le_of_eq (norm_smul c y) }
  -- for each `y`, the map `⟨T* y, ·⟩ = ⟨y, T ·⟩ : X → 𝒜` is bounded, by 32VI
  set φ : Y → (X →L[ℂ] 𝒜) := fun y =>
    LinearMap.mkContinuous
      { toFun := fun x => inner 𝒜 (S y) x
        map_add' := fun _ _ => CStarModule.inner_add_right
        map_smul' := fun _ _ => CStarModule.inner_smul_right_complex }
      ‖S y‖ (fun _ => CStarModule.norm_inner_le X) with hφdef
  have hφ : ∀ (y : Y) (x : X), φ y x = inner 𝒜 (S y) x := fun _ _ => rfl
  have hswap : ∀ (y : Y) (x : X), ‖(φ y x : 𝒜)‖ = ‖inner 𝒜 (T x) y‖ := by
    intro y x
    rw [hφ, ← CStarModule.star_inner (A := 𝒜) x (S y), ← adj x y, norm_star]
  -- uniform boundedness over the unit ball of `Y` (35II)
  have hbdd : ∀ x : X, BddAbove (Set.range fun y : {y : Y // ‖y‖ ≤ 1} => ‖φ y.1 x‖) := by
    intro x
    refine ⟨‖T x‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    show ‖φ (y : Y) x‖ ≤ ‖T x‖
    rw [hswap]
    calc ‖inner 𝒜 (T x) (y : Y)‖ ≤ ‖T x‖ * ‖(y : Y)‖ := CStarModule.norm_inner_le Y
      _ ≤ ‖T x‖ * 1 := by gcongr; exact y.2
      _ = ‖T x‖ := mul_one _
  obtain ⟨B, hB⟩ := pub (fun y : {y : Y // ‖y‖ ≤ 1} => φ y.1) hbdd
  have hB' : ∀ y : {y : Y // ‖y‖ ≤ 1}, ‖φ y.1‖ ≤ B := fun y => hB (Set.mem_range_self y)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB' ⟨0, by simp⟩)
  -- hence `‖⟨y, T x⟩‖ ≤ B ‖y‖ ‖x‖` for all `x`, `y`
  have hform : ∀ (x : X) (y : Y), ‖inner 𝒜 (T x) y‖ ≤ B * ‖y‖ * ‖x‖ := by
    intro x y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [mul_nonneg, hB0]
    · have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
      set y' : Y := (((‖y‖⁻¹ : ℝ) : ℂ)) • y with hy'
      have hn : ‖y'‖ ≤ 1 := by
        rw [hy', norm_smul]
        simp [abs_of_nonneg hy0.le, inv_mul_cancel₀ hy0.ne']
      have hyy : ((‖y‖ : ℂ)) • y' = y := by
        rw [hy', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hy0.ne',
          Complex.ofReal_one, one_smul]
      have h1 : ‖inner 𝒜 (T x) y'‖ ≤ B * ‖x‖ := by
        rw [← hswap]
        exact le_trans ((φ y').le_opNorm x)
          (mul_le_mul_of_nonneg_right (hB' ⟨y', hn⟩) (norm_nonneg x))
      calc ‖inner 𝒜 (T x) y‖ = ‖((‖y‖ : ℂ)) • inner 𝒜 (T x) y'‖ := by
            rw [← CStarModule.inner_smul_right_complex, hyy]
        _ = ‖y‖ * ‖inner 𝒜 (T x) y'‖ := by
            rw [norm_smul]; simp
        _ ≤ ‖y‖ * (B * ‖x‖) := by gcongr
        _ = B * ‖y‖ * ‖x‖ := by ring
  -- and `‖T x‖² = ‖⟨T x, T x⟩‖ ≤ B ‖T x‖ ‖x‖` gives `‖T x‖ ≤ B ‖x‖` (32X)
  have hTb : ∀ x : X, ‖T x‖ ≤ B * ‖x‖ := by
    intro x
    have h1 := hform x (T x)
    rw [← CStarModule.norm_sq_eq (A := 𝒜) (x := T x)] at h1
    rcases eq_or_lt_of_le (norm_nonneg (T x)) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith [norm_nonneg x]
  have hSb : ∀ y : Y, ‖S y‖ ≤ B * ‖y‖ := by
    intro y
    have h1 : ‖inner 𝒜 (S y) (S y)‖ ≤ B * ‖y‖ * ‖S y‖ := by
      rw [← adj (S y) y]
      exact hform (S y) y
    rw [← CStarModule.norm_sq_eq (A := 𝒜) (x := S y)] at h1
    rcases eq_or_lt_of_le (norm_nonneg (S y)) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith [norm_nonneg y]
  -- both maps are linear (`linear_of_isAdjointTo`), so the two bounds bundle
  obtain ⟨T', hT'⟩ := linear_of_isAdjointTo (𝒜 := 𝒜) adj
  obtain ⟨S', hS'⟩ := linear_of_isAdjointTo (𝒜 := 𝒜) (isAdjointTo_swap' (𝒜 := 𝒜) adj)
  refine ⟨?_, ?_⟩
  · rw [← hT']
    exact (T'.mkContinuous B fun x => by rw [hT']; exact hTb x).continuous
  · rw [← hS']
    exact (S'.mkContinuous B fun y => by rw [hS']; exact hSb y).continuous

/-- **35VI** (`hellinger-toeplitz`, cstar.tex:6070, Theorem): an adjointable
map `T : X → Y` between pre-Hilbert 𝒜-modules (here: `CStarModule`s over a
C*-algebra `𝒜`) is bounded — together with its adjoint — as soon as **either**
`X` or `Y` is complete.  The special case `𝒜 = ℂ`, `X = Y` a Hilbert space is
the classical Hellinger–Toeplitz theorem (**35VIII**); Mathlib:
`LinearMap.IsSymmetric.continuous`.

Neither `T` nor `S` is assumed linear.  The source's `T` is an *adjointable
map*, and **32I** notes that such a map "must be linear, and a module map" —
so ℂ-linearity is part of the **conclusion** here, derived from definiteness
of the inner product by `linear_of_isAdjointTo`.  (The 𝒜-module-map half is
not claimed by 35VI itself; it is `IsBoundedModuleMap`, delivered by **36V**.)
This is the shape `A/CStar/Basic`'s **4XVI** takes for `𝒜 = ℂ`, where the
adjoint is likewise a bare map `H → H`.

The "either" is genuine: the statement is symmetric in `(T, X)` and `(S, Y)`
— take the star of the adjointness relation — so the hypothesis is the
*disjunction* of the two completeness assumptions, and the second disjunct is
discharged by instantiating the first with the roles swapped. -/
theorem hellinger_toeplitz (hc : CompleteSpace X ∨ CompleteSpace Y)
    (T : X → Y) (S : Y → X)
    (adj : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) :
    ∃ (T' : X →ₗ[ℂ] Y) (S' : Y →ₗ[ℂ] X),
      ⇑T' = T ∧ ⇑S' = S ∧ Continuous T ∧ Continuous S := by
  obtain ⟨T', hT'⟩ := linear_of_isAdjointTo (𝒜 := 𝒜) adj
  obtain ⟨S', hS'⟩ := linear_of_isAdjointTo (𝒜 := 𝒜) (isAdjointTo_swap' (𝒜 := 𝒜) adj)
  refine ⟨T', S', hT', hS', ?_⟩
  rcases hc with h | h
  · haveI := h
    exact hellinger_toeplitz_aux (𝒜 := 𝒜) T S adj
  · haveI := h
    exact (hellinger_toeplitz_aux (𝒜 := 𝒜) S T (isAdjointTo_swap' (𝒜 := 𝒜) adj)).symm

/-! **35VIII** (cstar.tex:6101, Remark): the Hellinger–Toeplitz theorem —
every symmetric operator on a Hilbert space is bounded — is the special case
of **35VI** noted in its doc comment; not converted separately. -/

section C00

/-! ### 35IX: completeness may not be dropped

**35IX** (`hellinger-toeplitz-needs-complete`, cstar.tex:6109, Example): the
condition that either `X` or `Y` be complete may not be dropped from **35VI**:
the linear map `T : c₀₀ → c₀₀`, `T α = (n αₙ)ₙ`, on the finitely supported
sequences is self-adjoint but not bounded.

The carrier is the one **5III** (`A/CStar/Basic`, `projection_on_c00`) already
works with: `c₀₀` sits inside `ℓ² = lp (fun _ : ℕ => ℂ) 2` as a `Submodule`,
which supplies the pre-Hilbert structure (`Submodule.innerProductSpace`) for
free — no new instance on `Finsupp` is needed.  Here it is carved out by
finite support rather than as the span of the coordinate vectors, which is
what the definition of `T` needs; `c00_eq_span` checks the two descriptions
agree.

The Example's point comes out as three declarations: `c00T_isAdjointTo`
(self-adjointness, in the file's own sense from **4VIII**),
`c00T_not_continuous` (unboundedness), and — the reason this is no
counterexample to **35VI** — `c00_not_complete`. -/

/-- A finitely supported sequence is square-summable. -/
private theorem memLp_two_of_finite_support {f : ℕ → ℂ}
    (hf : (Function.support f).Finite) : Memℓp f 2 := by
  refine memℓp_gen (summable_of_ne_finset_zero (s := hf.toFinset) ?_)
  intro b hb
  have hb0 : f b = 0 := by
    by_contra h
    exact hb (hf.mem_toFinset.2 h)
  simp [hb0]

/-- **35IX** (`hellinger-toeplitz-needs-complete`, cstar.tex:6109, Example):
`c₀₀`, the finitely supported sequences, as a linear subspace of `ℓ²`.  Its
pre-Hilbert structure is the one Mathlib puts on a submodule of an inner
product space; it is *not* complete (`c00_not_complete`). -/
def c00 : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) where
  carrier := {f | (Function.support (f : ℕ → ℂ)).Finite}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, lp.coeFn_add] at hf hg ⊢
    exact (hf.union hg).subset (Function.support_add _ _)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, lp.coeFn_zero, Function.support_zero]
    exact Set.finite_empty
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq, lp.coeFn_smul] at hf ⊢
    refine hf.subset fun n hn => ?_
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

theorem mem_c00_iff {f : lp (fun _ : ℕ => ℂ) 2} :
    f ∈ c00 ↔ (Function.support (f : ℕ → ℂ)).Finite := Iff.rfl

/-- The coordinate vectors of **5III** lie in `c₀₀`. -/
theorem single_mem_c00 (n : ℕ) (z : ℂ) : lp.single 2 n z ∈ c00 := by
  rw [mem_c00_iff]
  refine (Set.finite_singleton n).subset fun m hm => ?_
  simp only [Function.mem_support, lp.coeFn_single] at hm
  by_contra hne
  exact hm (Pi.single_eq_of_ne hne _)

/-- The carrier used here is the one **5III** (`projection_on_c00`) works
with: carving `c₀₀` out by finite support gives the same subspace as spanning
it by the coordinate vectors `lp.single 2 n z`. -/
theorem c00_eq_span :
    c00 = Submodule.span ℂ {f : lp (fun _ : ℕ => ℂ) 2 | ∃ n z, f = lp.single 2 n z} := by
  apply le_antisymm
  · intro f hf
    have hsupp : (Function.support (f : ℕ → ℂ)).Finite := mem_c00_iff.1 hf
    have hrepr : f = ∑ k ∈ hsupp.toFinset, lp.single 2 k ((f : ℕ → ℂ) k) := by
      apply lp.ext
      funext n
      rw [lp.coeFn_sum]
      simp only [Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
      by_cases h : n ∈ hsupp.toFinset
      · simp [h]
      · simp only [h, ite_false]
        by_contra hne
        exact h (hsupp.mem_toFinset.2 hne)
    rw [hrepr]
    exact sum_mem fun k _ => Submodule.subset_span ⟨k, _, rfl⟩
  · rw [Submodule.span_le]
    rintro f ⟨n, z, rfl⟩
    exact single_mem_c00 n z

/-- The support of `n ↦ n · αₙ` is contained in that of `α`. -/
private theorem support_mulNat_subset (x : lp (fun _ : ℕ => ℂ) 2) :
    (Function.support fun n : ℕ => (n : ℂ) * x n) ⊆ Function.support (x : ℕ → ℂ) := by
  intro n hn
  simp only [Function.mem_support] at hn ⊢
  intro h
  exact hn (by rw [h, mul_zero])

/-- The underlying `ℓ²` sequence of `T α = (n αₙ)ₙ`. -/
private noncomputable def mulNat (x : c00) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n => (n : ℂ) * (x : lp (fun _ : ℕ => ℂ) 2) n,
    memLp_two_of_finite_support (((mem_c00_iff.1 x.2)).subset (support_mulNat_subset _))⟩

private theorem mulNat_apply (x : c00) (n : ℕ) :
    (mulNat x : ℕ → ℂ) n = (n : ℂ) * (x : lp (fun _ : ℕ => ℂ) 2) n := rfl

private theorem mulNat_mem (x : c00) : mulNat x ∈ c00 :=
  (mem_c00_iff.1 x.2).subset (support_mulNat_subset _)

/-- **35IX** (`hellinger-toeplitz-needs-complete`, cstar.tex:6109, Example):
the linear map `T : c₀₀ → c₀₀` given by `T α = (n αₙ)ₙ`.  It stays inside
`c₀₀` because multiplying coordinatewise does not enlarge the support. -/
noncomputable def c00T : c00 →ₗ[ℂ] c00 where
  toFun x := ⟨mulNat x, mulNat_mem x⟩
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext n
    simp only [mulNat_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c x := by
    apply Subtype.ext
    apply lp.ext
    funext n
    simp only [mulNat_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] theorem c00T_apply (x : c00) (n : ℕ) :
    ((c00T x : lp (fun _ : ℕ => ℂ) 2) : ℕ → ℂ) n = (n : ℂ) * (x : lp (fun _ : ℕ => ℂ) 2) n := rfl

/-- **35IX**, first half: `T` is self-adjoint, in the sense of **4VIII**
(`IsAdjointTo`) that **35VI** takes as its hypothesis.  Termwise in the `ℓ²`
inner product, `conj (n αₙ) βₙ = conj αₙ (n βₙ)` because `n` is real. -/
theorem c00T_isAdjointTo : IsAdjointTo (⇑c00T) (⇑c00T) := by
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [c00T_apply, RCLike.inner_apply, map_mul, Complex.conj_natCast]
  ring

/-- **35IX**: `c00T_isAdjointTo` in Mathlib's vocabulary — `T` is a symmetric
operator, the hypothesis of `LinearMap.IsSymmetric.continuous` (**35VIII**). -/
theorem c00T_isSymmetric : LinearMap.IsSymmetric c00T := c00T_isAdjointTo

/-- **35IX**: the thesis's own witnesses `x_N = (1, 1/2, …, 1/N, 0, …)`. -/
noncomputable def xN (N : ℕ) : c00 :=
  ⟨∑ k ∈ Finset.Icc 1 N, lp.single 2 k ((k : ℂ)⁻¹),
    sum_mem fun k _ => single_mem_c00 k _⟩

/-- **35IX**: `T` maps `x_N = (1, 1/2, …, 1/N, 0, …)` to `(1, …, 1, 0, …)`. -/
theorem c00T_xN (N : ℕ) :
    (c00T (xN N) : lp (fun _ : ℕ => ℂ) 2)
      = ∑ k ∈ Finset.Icc 1 N, lp.single 2 k (1 : ℂ) := by
  apply lp.ext
  funext n
  simp only [c00T_apply, xN, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]
  by_cases h : n ∈ Finset.Icc 1 N
  · have hn : 1 ≤ n := (Finset.mem_Icc.1 h).1
    have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp [h, mul_inv_cancel₀ hne]
  · simp [h]

/-- **35IX**: `‖T x_N‖ = √N`, the thesis's computation. -/
theorem norm_c00T_xN (N : ℕ) : ‖c00T (xN N)‖ = Real.sqrt N := by
  have h2 : ‖c00T (xN N)‖ ^ 2 = (N : ℝ) := by
    have h := lp.norm_sum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num)
      (fun _ : ℕ => (1 : ℂ)) (Finset.Icc 1 N)
    simp only [ENNReal.toReal_ofNat] at h
    rw [Submodule.coe_norm, c00T_xN]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num] at h
    rw [Real.rpow_natCast] at h
    simp only [Real.rpow_natCast, norm_one, one_pow, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul, mul_one] at h
    rw [h]
    simp
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- **35IX**: the `x_N` are norm-bounded — `‖x_N‖² = ∑_{k=1}^N 1/k²` is at most
`∑' k, 1/k²`.  The next lemma evaluates that bound as the thesis's `π/√6`. -/
theorem norm_xN_le (N : ℕ) :
    ‖xN N‖ ≤ Real.sqrt (∑' k : ℕ, 1 / (k : ℝ) ^ 2) := by
  have hsummable : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have h2 : ‖xN N‖ ^ 2 = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ 2 := by
    have h := lp.norm_sum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num)
      (fun k : ℕ => ((k : ℂ))⁻¹) (Finset.Icc 1 N)
    simp only [ENNReal.toReal_ofNat] at h
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    simp only [Real.rpow_natCast] at h
    rw [Submodule.coe_norm]
    show ‖∑ k ∈ Finset.Icc 1 N, lp.single 2 k ((k : ℂ))⁻¹‖ ^ 2 = _
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_inv, Complex.norm_natCast]
    field_simp
  have hle : ‖xN N‖ ^ 2 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := by
    rw [h2]
    exact hsummable.sum_le_tsum _ (fun i _ => by positivity)
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _)] at h

/-- **35IX**: the thesis's bound, `‖x_N‖ ≤ π/√6`.  The Basel sum
`∑_{k≥1} 1/k² = π²/6` is Mathlib's `hasSum_zeta_two`. -/
theorem norm_xN_le_pi_div_sqrt_six (N : ℕ) :
    ‖xN N‖ ≤ Real.pi / Real.sqrt 6 := by
  have hz : (∑' k : ℕ, 1 / (k : ℝ) ^ 2) = Real.pi ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  have hval : Real.sqrt (∑' k : ℕ, 1 / (k : ℝ) ^ 2) = Real.pi / Real.sqrt 6 := by
    rw [hz, show Real.pi ^ 2 / 6 = (Real.pi / Real.sqrt 6) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]]
    exact Real.sqrt_sq (by positivity)
  exact hval ▸ norm_xN_le N

/-- **35IX**, second half: `T` is not bounded.  This is the thesis's argument:
`T` maps `x_N = (1, 1/2, …, 1/N, 0, …)`, of 2-norm below `π/√6`, to
`(1, …, 1, 0, …)`, of 2-norm `√N`. -/
theorem c00T_not_bounded : ¬ ∃ C : ℝ, ∀ x : c00, ‖c00T x‖ ≤ C * ‖x‖ := by
  rintro ⟨C, hC⟩
  set B := Real.pi / Real.sqrt 6 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hC0 : 0 ≤ C := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 := hC (xN 1)
    rw [norm_c00T_xN, Nat.cast_one, Real.sqrt_one] at h1
    nlinarith [norm_nonneg (xN 1)]
  have key : ∀ N : ℕ, Real.sqrt N ≤ C * B := fun N =>
    (norm_c00T_xN N ▸ hC (xN N)).trans
      (mul_le_mul_of_nonneg_left (norm_xN_le_pi_div_sqrt_six N) hC0)
  obtain ⟨N, hN⟩ := exists_nat_gt ((C * B) ^ 2)
  have h3 : C * B < Real.sqrt N := (Real.lt_sqrt (mul_nonneg hC0 hB0)).2 hN
  linarith [key N]

/-- **35IX**, second half, in the form **35VI** denies: `T` is not
continuous. -/
theorem c00T_not_continuous : ¬ Continuous (⇑c00T) := by
  intro h
  set F : c00 →L[ℂ] c00 := ⟨c00T, h⟩ with hF
  exact c00T_not_bounded ⟨‖F‖, fun x => F.le_opNorm x⟩

/-- **35IX**, and the missing clause of **4IX** (`hilb-basic-examples`): `c₀₀`
is an inner product space that is *not* complete.  This is what keeps 35IX
from contradicting **35VI**, and the argument is 35VI itself: were `c₀₀`
complete, its symmetric operator `T` would be bounded.

That is `hellinger_toeplitz` (:222), *this file's* rendering of the Theorem,
applied at `𝒜 = ℂ` with `T` as its own adjoint.  Mathlib's
`LinearMap.IsSymmetric.continuous` would close the goal too, but through
Mathlib rather than through the tree's 35VI; going through 35VI is what makes
`c00T_isAdjointTo`, with its **4VIII** hypothesis, the form consumed here. -/
theorem c00_not_complete : ¬ CompleteSpace c00 := by
  intro h
  obtain ⟨_, _, _, _, hcont, _⟩ :=
    hellinger_toeplitz (𝒜 := ℂ) (Or.inl h) (⇑c00T) (⇑c00T) c00T_isAdjointTo
  exact c00T_not_continuous hcont

/-- **35IX** (`hellinger-toeplitz-needs-complete`, cstar.tex:6109, Example):
completeness may not be dropped from **35VI** — on `c₀₀` there is a
self-adjoint linear map that is not continuous. -/
theorem hellinger_toeplitz_needs_complete :
    ∃ T : c00 →ₗ[ℂ] c00, IsAdjointTo (⇑T) (⇑T) ∧ ¬ Continuous (⇑T) :=
  ⟨c00T, c00T_isAdjointTo, c00T_not_continuous⟩

end C00

/-! ## Parsec 360: Self-dual Hilbert modules and bounded forms -/

variable (𝒜) in
/-- Auxiliary notion for **36I**/**36IV**/**36V** (the thesis introduces
(bounded) module maps between Hilbert 𝒜-modules in its section on Hilbert
C*-modules): a ℂ-linear map `T : X → Y` between pre-Hilbert 𝒜-modules is a
*bounded module map* when it is 𝒜-linear (`T (a • x) = a • T x`) and bounded
(equivalently, continuous). -/
def IsBoundedModuleMap (T : X →ₗ[ℂ] Y) : Prop :=
  (∀ (a : 𝒜) (x : X), T (a • x) = a • T x) ∧ Continuous (⇑T)

variable (𝒜 X) in
/-- **36I** (`self-dual`, cstar.tex:6123, Definition): a Hilbert 𝒜-module `X`
is *self-dual* when every bounded module map `r : X → 𝒜` is of the form
`⟪y, ·⟫` for some `y ∈ X`.  (**36II**, the Example that every Hilbert space is
self-dual by Riesz, is `selfDual_hilbert` below.) -/
def SelfDual : Prop :=
  ∀ r : X →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r → ∃ y : X, ∀ x : X, r x = inner 𝒜 y x

/-- **36II** (cstar.tex:6130, Example): by Riesz' representation theorem
(**5XI**, Mathlib's `InnerProductSpace.toDual`) every Hilbert space is
self-dual — that is, `SelfDual ℂ H` for the pre-Hilbert ℂ-module `H`, whose
𝒜-valued inner product (`𝒜 = ℂ`) is the ordinary one.

This is the instance of **36I** at `𝒜 = ℂ`, and it is what makes **36V**
applicable to a Hilbert space: `exists_rho` (**39IX**) and
`bh_bounded_uw_complete` (**76III**, `A/VN/Completeness`) both represent a
bounded form on `H` by instantiating 36V here, which is the thesis's own
route in both places.  Note that a bounded module map over `𝒜 = ℂ` is just a
continuous ℂ-linear functional: the module-map clause
`r (c • x) = c • r x` is ℂ-linearity again. -/
theorem selfDual_hilbert (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : SelfDual ℂ H := by
  intro r hr
  refine ⟨(InnerProductSpace.toDual ℂ H).symm ⟨r, hr.2⟩, fun x => ?_⟩
  exact (InnerProductSpace.toDual_symm_apply (x := x)
    (y := (⟨r, hr.2⟩ : H →L[ℂ] ℂ))).symm

/-- **36III** (cstar.tex:6134, Exercise): for a C*-algebra `𝒜` the Hilbert
𝒜-module `𝒜^N` of `N`-tuples (Mathlib: the type synonym
`WithCStarModule 𝒜 (Fin N → 𝒜)`, notation `C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)`) is
self-dual. -/
theorem selfDual_pi (𝒜 : Type*) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (N : ℕ) :
    SelfDual 𝒜 (WithCStarModule 𝒜 (Fin N → 𝒜)) :=
  by
    intro r hr
    -- the standard "basis" `e i = (0, …, 1, …, 0)` of `𝒜^N`
    set e : Fin N → WithCStarModule 𝒜 (Fin N → 𝒜) :=
      fun i => (WithCStarModule.equiv 𝒜 _).symm (Pi.single i 1) with he
    refine ⟨(WithCStarModule.equiv 𝒜 _).symm fun i => star (r (e i)), fun x => ?_⟩
    have hdecomp : ∑ i, (x i) • e i = x := by
      ext j
      have hsum : (∑ i, (x i) • e i) j = ∑ i, ((x i) • e i) j := by
        have h := map_sum (WithCStarModule.linearEquiv ℂ 𝒜 (Fin N → 𝒜))
          (fun i => (x i) • e i) Finset.univ
        calc (∑ i, (x i) • e i) j
            = (WithCStarModule.linearEquiv ℂ 𝒜 (Fin N → 𝒜) (∑ i, (x i) • e i)) j := rfl
          _ = (∑ i, WithCStarModule.linearEquiv ℂ 𝒜 (Fin N → 𝒜) ((x i) • e i)) j := by
              rw [h]
          _ = ∑ i, ((x i) • e i) j := Finset.sum_apply _ _ _
      rw [hsum]
      simp only [he, WithCStarModule.smul_apply, WithCStarModule.equiv_symm_pi_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
    calc r x = r (∑ i, (x i) • e i) := by rw [hdecomp]
      _ = ∑ i, (x i) * r (e i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => hr.1 _ _
      _ = inner 𝒜 ((WithCStarModule.equiv 𝒜 _).symm fun i => star (r (e i))) x := by
          rw [WithCStarModule.pi_inner]
          exact Finset.sum_congr rfl fun i _ => by
            simp [WithCStarModule.inner_def]

variable (𝒜) in
/-- **36IV** (`chilb-form`, cstar.tex:6139, Definition): a *(bounded) form* on
Hilbert 𝒜-modules `X` and `Y` is a map `[·,·] : X × Y → 𝒜` such that
`[x, ·] : Y → 𝒜` and `[·, y]* : X → 𝒜` are (bounded) module maps for all
`x ∈ X` and `y ∈ Y`.  (Since `B` is a bare function, the module-map conditions
are phrased as the existence of linear maps agreeing with it.) -/
structure IsBoundedForm (B : X → Y → 𝒜) : Prop where
  bddModuleMap_right : ∀ x : X,
    ∃ r : Y →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧ ∀ y : Y, r y = B x y
  bddModuleMap_left_star : ∀ y : Y,
    ∃ r : X →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧ ∀ x : X, r x = star (B x y)

/-- **36V** (`chilb-form-representation`, cstar.tex:6150, Proposition): for
every bounded form `[·,·] : X × Y → 𝒜` on self-dual Hilbert 𝒜-modules `X` and
`Y` there is a unique adjointable bounded module map `T : X → Y` with
`[x, y] = ⟪T x, y⟫` for all `x ∈ X`, `y ∈ Y`.

**Completeness, half restored and half dropped.**  The source says *Hilbert*
𝒜-modules, and a Hilbert 𝒜-module is by definition (cstar.tex 32I) a
pre-Hilbert module that is *complete*; our `CStarModule` hypotheses only give
the pre-Hilbert structure.  The thesis's proof genuinely needs completeness —
it obtains boundedness of `T` and `S` from **35VI**, which is false without it
(**35IX**) — so `[CompleteSpace X]` is added back.

But only *one* of the two is added: the source assumes **both** `X` and `Y`
complete, and `[CompleteSpace Y]` is **dropped** here, because 35VI needs only
one of the two (that is the "either" of its statement, now carried by its
hypothesis `hc`).  So relative to the point this statement is a genuine — and
true — generalisation in `Y`, and a faithful transcription in `X`. -/
theorem chilb_form_representation [CompleteSpace X]
    (hX : SelfDual 𝒜 X) (hY : SelfDual 𝒜 Y)
    {B : X → Y → 𝒜} (hB : IsBoundedForm 𝒜 B) :
    ∃! T : X →ₗ[ℂ] Y, IsBoundedModuleMap 𝒜 T ∧
      (∃ S : Y →ₗ[ℂ] X, ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y)) ∧
      ∀ (x : X) (y : Y), B x y = inner 𝒜 (T x) y := by
  classical
  -- `[x, ·]` is a bounded module map `Y → 𝒜`, so self-duality of `Y` represents it
  have hTex : ∀ x : X, ∃ t : Y, ∀ y : Y, B x y = inner 𝒜 t y := by
    intro x
    obtain ⟨r, hr, hrB⟩ := hB.bddModuleMap_right x
    obtain ⟨t, ht⟩ := hY r hr
    exact ⟨t, fun y => by rw [← hrB, ht]⟩
  have hSex : ∀ y : Y, ∃ s : X, ∀ x : X, star (B x y) = inner 𝒜 s x := by
    intro y
    obtain ⟨r, hr, hrB⟩ := hB.bddModuleMap_left_star y
    obtain ⟨s, hs⟩ := hX r hr
    exact ⟨s, fun x => by rw [← hrB, hs]⟩
  choose T₀ hT₀ using hTex
  choose S₀ hS₀ using hSex
  -- the form is additive/conjugate-homogeneous/𝒜-linear in its first argument …
  have hBleft : ∀ y : Y, ∃ r : X →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧
      ∀ x : X, r x = star (B x y) := hB.bddModuleMap_left_star
  -- … which transfers to `T₀` through the definiteness of the inner product
  have hTadd : ∀ x x' : X, T₀ (x + x') = T₀ x + T₀ x' := by
    intro x x'
    refine ext_inner_left' (𝒜 := 𝒜) fun y => ?_
    obtain ⟨r, -, hrB⟩ := hBleft y
    have hB' : B (x + x') y = B x y + B x' y := by
      have h := congrArg star (map_add r x x')
      rw [hrB, hrB, hrB, star_add, star_star, star_star, star_star] at h
      exact h
    rw [inner_add_left' (𝒜 := 𝒜), ← hT₀, ← hT₀, ← hT₀]
    exact hB'
  have hTsmul : ∀ (c : ℂ) (x : X), T₀ (c • x) = c • T₀ x := by
    intro c x
    refine ext_inner_left' (𝒜 := 𝒜) fun y => ?_
    obtain ⟨r, -, hrB⟩ := hBleft y
    have h := congrArg star (map_smul r c x)
    rw [hrB, hrB, star_star] at h
    rw [inner_smul_left' (𝒜 := 𝒜), ← hT₀, ← hT₀, h, star_smul, star_star]
    rfl
  set T : X →ₗ[ℂ] Y := { toFun := T₀, map_add' := hTadd, map_smul' := hTsmul } with hTdef
  have hTapp : ∀ x : X, T x = T₀ x := fun _ => rfl
  -- the same for `S₀`, using that `[x, ·]` is linear
  have hBright : ∀ x : X, ∃ r : Y →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧
      ∀ y : Y, r y = B x y := hB.bddModuleMap_right
  have hSadd : ∀ y y' : Y, S₀ (y + y') = S₀ y + S₀ y' := by
    intro y y'
    refine ext_inner_left' (𝒜 := 𝒜) fun x => ?_
    obtain ⟨r, -, hrB⟩ := hBright x
    have hB' : B x (y + y') = B x y + B x y' := by
      rw [← hrB, ← hrB, ← hrB, map_add]
    rw [inner_add_left' (𝒜 := 𝒜), ← hS₀ y x, ← hS₀ y' x, ← hS₀ (y + y') x, hB', star_add]
  have hSsmul : ∀ (c : ℂ) (y : Y), S₀ (c • y) = c • S₀ y := by
    intro c y
    refine ext_inner_left' (𝒜 := 𝒜) fun x => ?_
    obtain ⟨r, -, hrB⟩ := hBright x
    have hB' : B x (c • y) = c • B x y := by rw [← hrB, ← hrB, map_smul]
    rw [inner_smul_left' (𝒜 := 𝒜), ← hS₀ y x, ← hS₀ (c • y) x, hB', star_smul]
    rfl
  set S : Y →ₗ[ℂ] X := { toFun := S₀, map_add' := hSadd, map_smul' := hSsmul } with hSdef
  have hSapp : ∀ y : Y, S y = S₀ y := fun _ => rfl
  -- `T` and `S` are adjoint …
  have hadj : ∀ (x : X) (y : Y), inner 𝒜 (T x) y = inner 𝒜 x (S y) := by
    intro x y
    rw [hTapp, hSapp, ← hT₀, ← CStarModule.star_inner (A := 𝒜) (S₀ y) x, ← hS₀, star_star]
  -- … hence bounded, by **35VI**
  obtain ⟨-, -, -, -, hcontT, -⟩ :=
    hellinger_toeplitz (𝒜 := 𝒜) (Or.inl ‹CompleteSpace X›) (⇑T) (⇑S) hadj
  have hTmod : ∀ (a : 𝒜) (x : X), T (a • x) = a • T x := by
    intro a x
    refine ext_inner_left' (𝒜 := 𝒜) fun y => ?_
    obtain ⟨r, hr, hrB⟩ := hBleft y
    have h := congrArg star (hr.1 a x)
    rw [hrB, hrB, star_star] at h
    have hB' : B (a • x) y = B x y * star a := by
      rw [h, smul_eq_mul, star_mul, star_star]
    have hsm : inner 𝒜 (a • T₀ x) y = inner 𝒜 (T₀ x) y * star a := by
      rw [← CStarModule.star_inner (A := 𝒜) y (a • T₀ x),
        CStarModule.inner_op_smul_right, star_mul,
        CStarModule.star_inner (A := 𝒜) y (T₀ x)]
    rw [hTapp, hTapp, ← hT₀, hsm, ← hT₀]
    exact hB'
  refine ⟨T, ⟨⟨hTmod, hcontT⟩, ⟨S, hadj⟩, fun x y => by rw [hTapp]; exact hT₀ x y⟩, ?_⟩
  rintro T' ⟨-, -, hT'⟩
  refine LinearMap.ext fun x => ?_
  refine ext_inner_left' (𝒜 := 𝒜) fun y => ?_
  rw [← hT' x y, hTapp]
  exact hT₀ x y

end HilbertModules

/-! ## Parsec 370: The weak operator topology and directed suprema in B(H)

**37I** (cstar.tex:6178): "another consequence of 35II is this" — nothing to
formalize. -/

section BH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **37II** (`hilb-weakly-bounded-complete`, cstar.tex:6182, Proposition):
given a net `(y_α)_α` in a Hilbert space `H` for which `⟪y_α, x⟫` is Cauchy
*and bounded* for every `x ∈ H`, there is a unique `y ∈ H` with
`⟪y, x⟫ = lim_α ⟪y_α, x⟫` for all `x ∈ H`.  (**37IV**, Remark, not converted:
boundedness may not be omitted.) -/
theorem hilb_weakly_bounded_complete {ι : Type*} {l : Filter ι} [l.NeBot]
    (y : ι → H)
    (hcauchy : ∀ x : H, Cauchy (l.map fun α => ⟪y α, x⟫))
    (hbdd : ∀ x : H, BddAbove (Set.range fun α => ‖⟪y α, x⟫‖)) :
    ∃! z : H, ∀ x : H, Tendsto (fun α => ⟪y α, x⟫) l (𝓝 ⟪z, x⟫) := by
  classical
  have hlim : ∀ x : H, ∃ c : ℂ, Tendsto (fun α => ⟪y α, x⟫) l (𝓝 c) := fun x =>
    CompleteSpace.complete (hcauchy x)
  choose φ hφ using hlim
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun α => ‖innerSL ℂ (y α)‖) :=
    pub _ fun x => by simpa using hbdd x
  have hCle : ∀ α, ‖y α‖ ≤ C := fun α => by
    simpa using hC (Set.mem_range_self α)
  have hbound : ∀ x : H, ‖φ x‖ ≤ C * ‖x‖ := by
    intro x
    refine le_of_tendsto (hφ x).norm (Eventually.of_forall fun α => ?_)
    calc ‖⟪y α, x⟫‖ ≤ ‖y α‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖x‖ := by gcongr; exact hCle α
  have hadd : ∀ x x' : H, φ (x + x') = φ x + φ x' := by
    intro x x'
    refine tendsto_nhds_unique (hφ (x + x')) ?_
    simpa [inner_add_right] using (hφ x).add (hφ x')
  have hsmul : ∀ (c : ℂ) (x : H), φ (c • x) = c • φ x := by
    intro c x
    refine tendsto_nhds_unique (hφ (c • x)) ?_
    simpa [inner_smul_right] using (hφ x).const_smul c
  let φL : H →ₗ[ℂ] ℂ := { toFun := φ, map_add' := hadd, map_smul' := hsmul }
  let φC : H →L[ℂ] ℂ := φL.mkContinuous C hbound
  refine ⟨(InnerProductSpace.toDual ℂ H).symm φC, fun x => ?_, ?_⟩
  · have : ⟪(InnerProductSpace.toDual ℂ H).symm φC, x⟫ = φ x :=
      InnerProductSpace.toDual_symm_apply
    rw [this]
    exact hφ x
  · intro z hz
    refine ext_inner_right ℂ fun x => ?_
    rw [InnerProductSpace.toDual_symm_apply]
    exact tendsto_nhds_unique (hz x) (hφ x)

/-! **37V** (`swot`, cstar.tex:6252, Definition):

1. the *weak operator topology (WOT)* on B(H) is the least topology making
   `T ↦ ⟪x, T x⟫ : B(H) → ℂ` continuous for every `x ∈ H`.  In Mathlib the
   type copy `H →WOT[ℂ] H` (`ContinuousLinearMapWOT`) carries the weak
   operator topology (defined there via all maps `T ↦ y (T x)` with `y` in the
   dual — equivalent to the thesis's diagonal definition by polarization); the
   inclusion is `ContinuousLinearMapWOT.ofCLM`, and net convergence is
   characterized by
   `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`.

2. the *strong operator topology (SOT)* on B(H) is the topology **induced by
   the seminorms** `T ↦ ‖T x‖ = ⟪x, T* T x⟫^{1/2}`, `x ∈ H` — the wording of
   erratum `parsec-370.50`, incorporated in cstar.tex.  "Induced by the
   seminorms" is not the same as "the least topology making them continuous";
   see `sot_withSeminorms`.  Net convergence is `‖T_α x - T x‖ → 0` for
   every `x`, which is `sot_tendsto_iff` below, stated on Mathlib's type copy
   `H →Lₚₜ[ℂ] H` (`PointwiseConvergenceCLM`, the topology of pointwise
   convergence — Mathlib's own docstring records that this is what is
   elsewhere called the strong operator topology).  The thesis mentions the
   SOT only for comparison (**37VI**, Remark) and never uses it. -/

/-- The polarization identity in the form used to pass between the thesis's
diagonal description of the weak operator topology and Mathlib's:
`⟪y, S x⟫` is a fixed linear combination of the four diagonal values
`⟪z, S z⟫`, `z ∈ {x ± y, x ± i y}`.  (Auxiliary.) -/
private theorem inner_polarization (S : H →L[ℂ] H) (x y : H) : ⟪y, S x⟫ =
    (⟪x + y, S (x + y)⟫ - ⟪x - y, S (x - y)⟫ +
      Complex.I * ⟪x + Complex.I • y, S (x + Complex.I • y)⟫ -
      Complex.I * ⟪x - Complex.I • y, S (x - Complex.I • y)⟫) / 4 := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **37V** (`swot`, cstar.tex:6252, Definition), part 1, embedded claim: a
net `(T_α)_α` converges to `T` in B(H) with respect to the weak operator
topology (Mathlib: `H →WOT[ℂ] H`) if and only if `⟪x, T_α x⟫ → ⟪x, T x⟫` for
every `x ∈ H` (the thesis's diagonal condition; equivalent to Mathlib's
`ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto` by
polarization). -/
theorem swot_tendsto_iff {ι : Type*} {l : Filter ι} (T : ι → H →L[ℂ] H)
    (T₀ : H →L[ℂ] H) :
    Tendsto (fun α => ContinuousLinearMapWOT.ofCLM (T α)) l
        (𝓝 (ContinuousLinearMapWOT.ofCLM T₀)) ↔
      ∀ x : H, Tendsto (fun α => ⟪x, T α x⟫) l (𝓝 ⟪x, T₀ x⟫) := by
  have key := fun (S : H →L[ℂ] H) (x y : H) => inner_polarization S x y
  constructor
  · intro h x
    simpa using ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp h x x
  · intro h
    rw [ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
    intro x y
    simp only [ContinuousLinearMapWOT.ofCLM_apply]
    rw [key T₀ x y]
    refine Filter.Tendsto.congr (fun α => (key (T α) x y).symm) ?_
    exact ((((h (x + y)).sub (h (x - y))).add
      ((h (x + Complex.I • y)).const_mul Complex.I)).sub
      ((h (x - Complex.I • y)).const_mul Complex.I)).div_const 4

/-- **37V** (`swot`, cstar.tex:6252, Definition), part 1, the definition
itself: Mathlib's weak operator topology on `H →WOT[ℂ] H` **is** the thesis's
— *the least topology making `T ↦ ⟪x, T x⟫` continuous for every `x ∈ H`*,
i.e. the infimum of the topologies induced by those maps.

Mathlib takes the least topology making all of `T ↦ y (T x)`, `y` in the
dual, continuous; the two agree by Riesz and polarization, which is what
`inner_polarization` supplies and what the two inclusions below use.  (With
this in hand `swot_tendsto_iff` is the *consequence* the point draws, not the
definition itself.) -/
theorem swot_topology_eq :
    (inferInstance : TopologicalSpace (H →WOT[ℂ] H)) =
      ⨅ x : H, TopologicalSpace.induced (fun T : H →WOT[ℂ] H => (⟪x, T x⟫ : ℂ))
        inferInstance := by
  refine le_antisymm (le_iInf fun x => continuous_iff_le_induced.mp ?_) ?_
  · -- `⟪x, (·) x⟫` is WOT-continuous: it is `y (T x)` for `y = ⟪x, ·⟫` (Riesz)
    simpa [InnerProductSpace.toDual_apply_apply] using
      ContinuousLinearMapWOT.continuous_dual_apply (σ := RingHom.id ℂ) x
        (InnerProductSpace.toDual ℂ H x)
  · -- conversely, `T ↦ y (T x)` is a combination of diagonal values, so the
    -- topology on the left makes Mathlib's inducing map continuous
    letI tI : TopologicalSpace (H →WOT[ℂ] H) :=
      ⨅ x : H, TopologicalSpace.induced (fun T : H →WOT[ℂ] H => (⟪x, T x⟫ : ℂ))
        inferInstance
    have hdiag : ∀ z : H, Continuous (fun T : H →WOT[ℂ] H => (⟪z, T z⟫ : ℂ)) := fun z =>
      continuous_iInf_dom (i := z) continuous_induced_dom
    have hcont : Continuous (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) := by
      refine continuous_pi fun p => ?_
      obtain ⟨x, y⟩ := p
      obtain ⟨z, rfl⟩ : ∃ z, y = InnerProductSpace.toDual ℂ H z :=
        ⟨(InnerProductSpace.toDual ℂ H).symm y, by simp⟩
      have heq : ∀ T : H →WOT[ℂ] H,
          ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H T
              (x, InnerProductSpace.toDual ℂ H z) =
          ((⟪x + z, T (x + z)⟫ : ℂ) - ⟪x - z, T (x - z)⟫ +
            Complex.I * ⟪x + Complex.I • z, T (x + Complex.I • z)⟫ -
            Complex.I * ⟪x - Complex.I • z, T (x - Complex.I • z)⟫) / 4 := by
        intro T
        rw [ContinuousLinearMapWOT.inducingFn_apply, InnerProductSpace.toDual_apply_apply]
        exact inner_polarization (ContinuousLinearMapWOT.toCLM T) x z
      simp only [heq]
      exact ((((hdiag _).sub (hdiag _)).add ((hdiag _).const_mul _)).sub
        ((hdiag _).const_mul _)).div_const 4
    exact continuous_iff_le_induced.mp hcont

/-- **37V** (`swot`, cstar.tex:6252, Definition), part 2, embedded claim: a
net `(T_α)_α` converges to `T` in B(H) with respect to the *strong* operator
topology — Mathlib's topology of pointwise convergence on `H →Lₚₜ[ℂ] H`,
which is the topology induced by the seminorms `T ↦ ‖T x‖` of the definition's
corrected text — if and only if `‖T_α x - T x‖ → 0` for every `x ∈ H`.

This is the item-2 counterpart of `swot_tendsto_iff`; the thesis states it as
the "so a net converges iff …" sentence of item 2 and never uses it. -/
theorem sot_tendsto_iff {ι : Type*} {l : Filter ι} (T : ι → H →L[ℂ] H)
    (T₀ : H →L[ℂ] H) :
    Tendsto (fun α =>
        UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | Finite s} (T α)) l
        (𝓝 (UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | Finite s} T₀)) ↔
      ∀ x : H, Tendsto (fun α => ‖T α x - T₀ x‖) l (𝓝 0) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  refine forall_congr' fun x => ?_
  rw [← tendsto_sub_nhds_zero_iff, ← tendsto_zero_iff_norm_tendsto_zero]
  rfl

omit [CompleteSpace H] in
/-- **37V** (`swot`, cstar.tex:6268, Definition), part 2, the definition
*itself*: the strong operator topology on `B(H)` **is** the topology induced
by the seminorms `T ↦ ‖T x‖`, `x ∈ H`.

This is the item-2 counterpart of `swot_topology_eq`, and it is what makes
`sot_tendsto_iff` above a *consequence* of the definition rather than a
substitute for it.  The carrier is Mathlib's `H →Lₚₜ[ℂ] H`
(`PointwiseConvergenceCLM (RingHom.id ℂ) H H`, which is by definition the
`UniformConvergenceCLM … {s : Set H | Finite s}` that `sot_tendsto_iff` is
stated over), and `WithSeminorms` is Mathlib's "the topology is induced by
this family of seminorms" — *not* "the least topology making them
continuous", which is the form erratum `parsec-370.50` corrects and warns is
not always the same thing.

*Class 5 — closed by Mathlib.*  `PointwiseConvergenceCLM.withSeminorms` says
exactly this; the Definition has no proof to match. -/
theorem sot_withSeminorms :
    WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H) :=
  PointwiseConvergenceCLM.withSeminorms

omit [CompleteSpace H] in
/-- The seminorms of `sot_withSeminorms` are the thesis's: the one indexed by
`x ∈ H` sends `T` to `‖T x‖` — the definition's own formula, whose second
description `⟪x, T* T x⟫^{1/2}` is `‖T x‖` again. -/
theorem sot_seminorm_apply (x : H) (T : H →Lₚₜ[ℂ] H) :
    PointwiseConvergenceCLM.seminorm x T = ‖T x‖ := rfl

/-- **37VII** (`bh-wot-bounded-complete`, cstar.tex:6292, Lemma): if
`(T_α)_α` is a net of bounded operators on a Hilbert space `H` such that
`⟪x, T_α x⟫` is Cauchy and bounded for every `x ∈ H`, then `(T_α)_α`
WOT-converges to some bounded operator `T ∈ B(H)`.

*Class 1 — faithful.*  The Lemma's own proof (cstar.tex:6266): polarisation
turns the hypothesis on the diagonal into boundedness and Cauchyness of every
matrix coefficient `⟪y, T_α x⟫`, so **37II** `hilb_weakly_bounded_complete`
produces `T x` for each `x`, and `T` is linear.  For boundedness the thesis
runs the same argument on the net of *adjoints* `(T_α*)_α` — whose diagonal
values are the conjugates of `(T_α)`'s — to get a map `S` adjoint to `T`, and
concludes with **35VI** `hellinger_toeplitz`. -/
theorem bh_wot_bounded_complete {ι : Type*} {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] H)
    (hcauchy : ∀ x : H, Cauchy (l.map fun α => ⟪x, T α x⟫))
    (hbdd : ∀ x : H, BddAbove (Set.range fun α => ‖⟪x, T α x⟫‖)) :
    ∃ T₀ : H →L[ℂ] H,
      Tendsto (fun α => ContinuousLinearMapWOT.ofCLM (T α)) l
        (𝓝 (ContinuousLinearMapWOT.ofCLM T₀)) := by
  classical
  -- the diagonal values converge
  have hd : ∀ x : H, ∃ c : ℂ, Tendsto (fun α => ⟪x, T α x⟫) l (𝓝 c) :=
    fun x => CompleteSpace.complete (hcauchy x)
  choose d hdlim using hd
  -- hence, by polarization, so do all matrix coefficients
  have hfull : ∀ x y : H, Tendsto (fun α => ⟪y, T α x⟫) l
      (𝓝 ((d (x + y) - d (x - y) + Complex.I * d (x + Complex.I • y) -
        Complex.I * d (x - Complex.I • y)) / 4)) := by
    intro x y
    refine Filter.Tendsto.congr (fun α => (inner_polarization (T α) x y).symm) ?_
    exact ((((hdlim (x + y)).sub (hdlim (x - y))).add
      ((hdlim (x + Complex.I • y)).const_mul Complex.I)).sub
      ((hdlim (x - Complex.I • y)).const_mul Complex.I)).div_const 4
  -- and all matrix coefficients are bounded
  have habs : ∀ A B C D : ℂ,
      ‖(A - B + Complex.I * C - Complex.I * D) / 4‖ ≤ (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) / 4 := by
    intro A B C D
    have e1 : ‖A - B + Complex.I * C - Complex.I * D‖ ≤
        ‖A - B + Complex.I * C‖ + ‖Complex.I * D‖ := norm_sub_le _ _
    have e2 : ‖A - B + Complex.I * C‖ ≤ ‖A - B‖ + ‖Complex.I * C‖ := norm_add_le _ _
    have e3 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    have e4 : ‖Complex.I * C‖ = ‖C‖ := by simp
    have e5 : ‖Complex.I * D‖ = ‖D‖ := by simp
    have e6 : ‖(A - B + Complex.I * C - Complex.I * D) / 4‖
        = ‖A - B + Complex.I * C - Complex.I * D‖ / 4 := by
      rw [norm_div]; norm_num
    rw [e6]
    linarith
  have hbdd2 : ∀ x y : H, BddAbove (Set.range fun α => ‖⟪y, T α x⟫‖) := by
    intro x y
    obtain ⟨b1, hb1⟩ := hbdd (x + y)
    obtain ⟨b2, hb2⟩ := hbdd (x - y)
    obtain ⟨b3, hb3⟩ := hbdd (x + Complex.I • y)
    obtain ⟨b4, hb4⟩ := hbdd (x - Complex.I • y)
    refine ⟨(b1 + b2 + b3 + b4) / 4, ?_⟩
    rintro _ ⟨α, rfl⟩
    dsimp only
    rw [inner_polarization (T α) x y]
    refine (habs _ _ _ _).trans ?_
    have h1 := hb1 (Set.mem_range_self α)
    have h2 := hb2 (Set.mem_range_self α)
    have h3 := hb3 (Set.mem_range_self α)
    have h4 := hb4 (Set.mem_range_self α)
    linarith
  have hconj : ∀ (x y : H) (α : ι), ‖⟪T α x, y⟫‖ = ‖⟪y, T α x⟫‖ := by
    intro x y α
    rw [← inner_conj_symm (T α x) y, RCLike.norm_conj]
  -- the net `(T α x)` converges weakly, for every `x`
  have hxlim : ∀ x : H, ∃! z : H, ∀ y : H, Tendsto (fun α => ⟪T α x, y⟫) l (𝓝 ⟪z, y⟫) := by
    intro x
    refine hilb_weakly_bounded_complete (fun α => T α x) (fun y => ?_) (fun y => ?_)
    · have h0 : Tendsto (fun α => ⟪T α x, y⟫) l
          (𝓝 (star ((d (x + y) - d (x - y) + Complex.I * d (x + Complex.I • y) -
            Complex.I * d (x - Complex.I • y)) / 4))) :=
        Filter.Tendsto.congr (fun α => inner_conj_symm (T α x) y) (hfull x y).star
      exact h0.cauchy_map
    · obtain ⟨b, hb⟩ := hbdd2 x y
      refine ⟨b, ?_⟩
      rintro _ ⟨α, rfl⟩
      dsimp only
      rw [hconj x y α]
      exact hb (Set.mem_range_self α)
  choose S hS _huniq using hxlim
  have hSadd : ∀ x x' : H, S (x + x') = S x + S x' := by
    intro x x'
    refine ext_inner_right ℂ fun y => ?_
    rw [inner_add_left]
    refine tendsto_nhds_unique (hS (x + x') y) ?_
    simpa [inner_add_left] using (hS x y).add (hS x' y)
  have hSsmul : ∀ (c : ℂ) (x : H), S (c • x) = c • S x := by
    intro c x
    refine ext_inner_right ℂ fun y => ?_
    rw [inner_smul_left]
    refine tendsto_nhds_unique (hS (c • x) y) ?_
    simpa [inner_smul_left, mul_comm] using (hS x y).const_mul (starRingEnd ℂ c)
  -- the net of adjoints converges weakly too, giving `S` an adjoint …
  have hylim : ∀ x : H, ∃! z : H, ∀ y : H,
      Tendsto (fun α => ⟪ContinuousLinearMap.adjoint (T α) x, y⟫) l (𝓝 ⟪z, y⟫) := by
    intro x
    refine hilb_weakly_bounded_complete (fun α => ContinuousLinearMap.adjoint (T α) x)
      (fun y => ?_) (fun y => ?_)
    · have h0 : Tendsto (fun α => ⟪ContinuousLinearMap.adjoint (T α) x, y⟫) l
          (𝓝 ((d (y + x) - d (y - x) + Complex.I * d (y + Complex.I • x) -
            Complex.I * d (y - Complex.I • x)) / 4)) :=
        Filter.Tendsto.congr
          (fun α => (ContinuousLinearMap.adjoint_inner_left (T α) y x).symm) (hfull y x)
      exact h0.cauchy_map
    · obtain ⟨b, hb⟩ := hbdd2 y x
      refine ⟨b, ?_⟩
      rintro _ ⟨α, rfl⟩
      dsimp only
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact hb (Set.mem_range_self α)
  choose R hR _huniqR using hylim
  have hadj : ∀ (x y : H), (inner ℂ (S x) y : ℂ) = inner ℂ x (R y) := by
    intro x y
    have h2 : Tendsto (fun α => ⟪ContinuousLinearMap.adjoint (T α) y, x⟫) l
        (𝓝 (star ⟪S x, y⟫)) := by
      refine Filter.Tendsto.congr (fun α => ?_) (hS x y).star
      rw [ContinuousLinearMap.adjoint_inner_left, RCLike.star_def, inner_conj_symm]
    have h3 := tendsto_nhds_unique (hR y x) h2
    rw [← inner_conj_symm x (R y), h3]
    simp
  -- … and **35VI** (Hellinger–Toeplitz) makes it bounded
  obtain ⟨-, -, -, -, hScont, -⟩ :=
    hellinger_toeplitz (𝒜 := ℂ) (Or.inl (inferInstance : CompleteSpace H)) S R hadj
  let SL : H →ₗ[ℂ] H := { toFun := S, map_add' := hSadd, map_smul' := hSsmul }
  refine ⟨⟨SL, hScont⟩, ?_⟩
  rw [ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
  intro x y
  simp only [ContinuousLinearMapWOT.ofCLM_apply]
  have h2 : ⟪y, (⟨SL, hScont⟩ : H →L[ℂ] H) x⟫ = ⟪y, S x⟫ := rfl
  rw [h2, ← inner_conj_symm y (S x)]
  exact Filter.Tendsto.congr (fun α => inner_conj_symm y (T α x)) ((hS x y).star)

/-- Symmetry of the real part of the inner product.  (Auxiliary.) -/
private theorem re_inner_comm (x y : H) : (⟪x, y⟫ : ℂ).re = (⟪y, x⟫ : ℂ).re := by
  have h : (⟪x, y⟫ : ℂ) = starRingEnd ℂ ⟪y, x⟫ := (inner_conj_symm x y).symm
  rw [h, Complex.conj_re]

/-- For a self-adjoint operator the diagonal values `⟪x, T x⟫` are real.
(Auxiliary for **37IX**.) -/
private theorem inner_self_ofReal_re {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (x : H) :
    (((⟪x, T x⟫).re : ℝ) : ℂ) = ⟪x, T x⟫ := by
  refine Complex.conj_eq_iff_re.mp ?_
  rw [inner_conj_symm]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT x x
  simpa using hsym

/-- Monotonicity of the diagonal values. (Auxiliary for **37IX**.) -/
private theorem re_inner_mono {S T : H →L[ℂ] H} (h : S ≤ T) (x : H) :
    (⟪x, S x⟫).re ≤ (⟪x, T x⟫).re := by
  have h0 : (0 : H →L[ℂ] H) ≤ T - S := sub_nonneg.mpr h
  have hp := (ContinuousLinearMap.isPositive_iff_complex (T - S)).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h0) x
  have h2 : (0 : ℝ) ≤ (⟪(T - S) x, x⟫).re := by simpa using hp.2
  rw [ContinuousLinearMap.sub_apply, inner_sub_left] at h2
  simp only [Complex.sub_re] at h2
  rw [re_inner_comm x (S x), re_inner_comm x (T x)]
  linarith

/-- Conversely, a self-adjoint operator dominating another one on the diagonal
dominates it.  (Auxiliary for **37IX**.) -/
private theorem le_of_re_inner {S T : H →L[ℂ] H} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (h : ∀ x, (⟪x, S x⟫).re ≤ (⟪x, T x⟫).re) : S ≤ T := by
  have hTS : IsSelfAdjoint (T - S) := hT.sub hS
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hre : (((⟪x, (T - S) x⟫).re : ℝ) : ℂ) = ⟪x, (T - S) x⟫ := inner_self_ofReal_re hTS x
  have hcomm : (⟪(T - S) x, x⟫ : ℂ) = ⟪x, (T - S) x⟫ := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTS x x
    simpa using hsym
  have hnn : (0 : ℝ) ≤ (⟪x, (T - S) x⟫).re := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right]
    simp only [Complex.sub_re]
    linarith [h x]
  rw [hcomm]
  exact ⟨by simpa using hre, by simpa using hnn⟩

/-- The diagonal values `⟪x, T x⟫` of a self-adjoint operator are real.
(Auxiliary for **37IX**.) -/
private theorem inner_self_im_eq_zero (S : selfAdjoint (H →L[ℂ] H)) (x : H) :
    (⟪x, (S : H →L[ℂ] H) x⟫).im = 0 := by
  rw [← inner_self_ofReal_re S.2 x]
  simp

/-- For a WOT-convergent net of self-adjoint operators the (real) diagonal
values converge to those of the limit.  (Auxiliary for **37IX**.) -/
private theorem re_diag_tendsto_of_wot {D : Set (selfAdjoint (H →L[ℂ] H))}
    {T' : selfAdjoint (H →L[ℂ] H)}
    (hT' : Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H)))) (x : H) :
    Tendsto (fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re) atTop
      (𝓝 (⟪x, (T' : H →L[ℂ] H) x⟫).re) :=
  (Complex.continuous_re.tendsto _).comp ((swot_tendsto_iff _ _).mp hT' x)

/-- **37IX** (`hilb-suprema`, cstar.tex:6335, Proposition), part 1: an upwards
directed set `D` of self-adjoint operators on a Hilbert space `H` with
`sup_{T ∈ D} ⟪x, T x⟫ < ∞` for all `x ∈ H` — viewed as the net `(T)_{T ∈ D}`
indexed by itself — converges in the weak operator topology to some
self-adjoint `T' ∈ B(H)`. -/
theorem hilb_suprema_1 (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D)) :
    ∃ T' : selfAdjoint (H →L[ℂ] H),
      Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
        atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H))) := by
  classical
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  have hreal : ∀ (x : H) (S : selfAdjoint (H →L[ℂ] H)),
      (((⟪x, (S : H →L[ℂ] H) x⟫).re : ℝ) : ℂ) = ⟪x, (S : H →L[ℂ] H) x⟫ :=
    fun x S => inner_self_ofReal_re S.2 x
  have hmono : ∀ x : H, Monotone fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re :=
    fun x _ _ hST => re_inner_mono hST x
  have hbddR : ∀ x : H, BddAbove (Set.range fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re) := by
    intro x
    obtain ⟨c, hc⟩ := hbdd x
    refine ⟨c.re, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact (RCLike.le_iff_re_im.mp (hc ⟨T.1, T.2, rfl⟩)).1
  have htendR : ∀ x : H, Tendsto (fun T : D => (⟪x, (T.1 : H →L[ℂ] H) x⟫).re) atTop
      (𝓝 (⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re)) :=
    fun x => tendsto_atTop_ciSup (hmono x) (hbddR x)
  have htendC : ∀ x : H, Tendsto (fun T : D => ⟪x, (T.1 : H →L[ℂ] H) x⟫) atTop
      (𝓝 (((⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re : ℝ) : ℂ))) := fun x =>
    Filter.Tendsto.congr (fun T => hreal x T.1)
      ((Complex.continuous_ofReal.tendsto _).comp (htendR x))
  -- the *cofinal tail* above `d₀`, on which the net is norm-bounded
  obtain ⟨F, hFdef⟩ : ∃ F : D → selfAdjoint (H →L[ℂ] H),
      ∀ T, F T = if (⟨d₀, hd₀⟩ : D) ≤ T then T.1 else d₀ := ⟨_, fun _ => rfl⟩
  have hFpos : ∀ T : D, (⟨d₀, hd₀⟩ : D) ≤ T → F T = T.1 := fun T h => by
    rw [hFdef T]; simp [h]
  have hFneg : ∀ T : D, ¬ ((⟨d₀, hd₀⟩ : D) ≤ T) → F T = d₀ := fun T h => by
    rw [hFdef T]; simp [h]
  have hFev : ∀ᶠ T in (atTop : Filter D), F T = T.1 := by
    filter_upwards [eventually_ge_atTop (⟨d₀, hd₀⟩ : D)] with T hT using hFpos T hT
  have hFtendC : ∀ x : H, Tendsto (fun T : D => ⟪x, (F T : H →L[ℂ] H) x⟫) atTop
      (𝓝 (((⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re : ℝ) : ℂ))) := by
    intro x
    refine (htendC x).congr' ?_
    filter_upwards [hFev] with T hT
    rw [hT]
  have hFcauchy : ∀ x : H, Cauchy (atTop.map fun T : D => ⟪x, (F T : H →L[ℂ] H) x⟫) :=
    fun x => (hFtendC x).cauchy_map
  have hFnbdd : ∀ x : H, BddAbove (Set.range fun T : D => ‖⟪x, (F T : H →L[ℂ] H) x⟫‖) := by
    intro x
    obtain ⟨c, hc⟩ := hbddR x
    refine ⟨|(⟪x, (d₀ : H →L[ℂ] H) x⟫).re| + |c|, ?_⟩
    rintro _ ⟨T, rfl⟩
    have hnorm : ‖⟪x, (F T : H →L[ℂ] H) x⟫‖ = |(⟪x, (F T : H →L[ℂ] H) x⟫).re| := by
      conv_lhs => rw [← hreal x (F T)]
      exact RCLike.norm_ofReal _
    have hlow : (⟪x, (d₀ : H →L[ℂ] H) x⟫).re ≤ (⟪x, (F T : H →L[ℂ] H) x⟫).re := by
      by_cases h : (⟨d₀, hd₀⟩ : D) ≤ T
      · rw [hFpos T h]; exact re_inner_mono h x
      · rw [hFneg T h]
    have hup : (⟪x, (F T : H →L[ℂ] H) x⟫).re ≤ c := by
      by_cases h : (⟨d₀, hd₀⟩ : D) ≤ T
      · rw [hFpos T h]; exact hc (Set.mem_range_self T)
      · rw [hFneg T h]; exact hc (Set.mem_range_self (⟨d₀, hd₀⟩ : D))
    simp only [hnorm, abs_le]
    have h1 := neg_abs_le (⟪x, (d₀ : H →L[ℂ] H) x⟫).re
    have h2 := le_abs_self c
    have h3 := abs_nonneg c
    have h4 := abs_nonneg (⟪x, (d₀ : H →L[ℂ] H) x⟫).re
    constructor <;> linarith
  obtain ⟨T₀, hT₀⟩ := bh_wot_bounded_complete (fun T : D => (F T : H →L[ℂ] H))
    hFcauchy hFnbdd
  have hdiag : ∀ x : H, Tendsto (fun T : D => ⟪x, (F T : H →L[ℂ] H) x⟫) atTop (𝓝 ⟪x, T₀ x⟫) :=
    (swot_tendsto_iff (fun T : D => (F T : H →L[ℂ] H)) T₀).mp hT₀
  have hT₀val : ∀ x : H,
      (⟪x, T₀ x⟫ : ℂ) = ((⨆ T : D, (⟪x, (T.1 : H →L[ℂ] H) x⟫).re : ℝ) : ℂ) :=
    fun x => tendsto_nhds_unique (hdiag x) (hFtendC x)
  have hsa : IsSelfAdjoint T₀ := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
      LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have h2 : (⟪T₀ v, v⟫ : ℂ) = ((⨆ T : D, (⟪v, (T.1 : H →L[ℂ] H) v⟫).re : ℝ) : ℂ) := by
      rw [← inner_conj_symm (T₀ v) v, hT₀val v, Complex.conj_ofReal]
    simp only [ContinuousLinearMap.coe_coe]
    rw [h2, Complex.conj_ofReal]
  refine ⟨⟨T₀, hsa⟩, ?_⟩
  refine hT₀.congr' ?_
  filter_upwards [hFev] with T hT
  rw [hT]

/-- **37IX** (`hilb-suprema`, cstar.tex:6335, Proposition), part 2: the WOT
limit `T'` of such a directed set `D` (cf. `hilb_suprema_1`) is the supremum
of `D` among the self-adjoint operators. -/
theorem hilb_suprema_2 (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D))
    (T' : selfAdjoint (H →L[ℂ] H))
    (hT' : Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H)))) :
    IsLUB D T' := by
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  constructor
  · intro S hS
    rw [← Subtype.coe_le_coe]
    refine le_of_re_inner S.2 T'.2 fun x => ?_
    refine ge_of_tendsto (re_diag_tendsto_of_wot hT' x) ?_
    filter_upwards [eventually_ge_atTop (⟨S, hS⟩ : D)] with T hT
    exact re_inner_mono hT x
  · intro S hS
    rw [← Subtype.coe_le_coe]
    refine le_of_re_inner T'.2 S.2 fun x => ?_
    refine le_of_tendsto (re_diag_tendsto_of_wot hT' x) (Eventually.of_forall fun T => ?_)
    exact re_inner_mono (hS T.2) x

/-- **37IX** (`hilb-suprema`, cstar.tex:6335, Proposition), part 3: for the
WOT limit `T'` of such a directed set `D` one has
`⟪x, T' x⟫ = sup_{T ∈ D} ⟪x, T x⟫` for all `x ∈ H` (stated as an `IsLUB` in ℂ
with the order from `ComplexOrder`). -/
theorem hilb_suprema_3 (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D))
    (T' : selfAdjoint (H →L[ℂ] H))
    (hT' : Tendsto (fun T : D => ContinuousLinearMapWOT.ofCLM ((T.1 : H →L[ℂ] H)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (T' : H →L[ℂ] H))))
    (x : H) :
    IsLUB ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D)
      ⟪x, (T' : H →L[ℂ] H) x⟫ := by
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  constructor
  · rintro _ ⟨S, hS, rfl⟩
    rw [Complex.le_def]
    refine ⟨?_, by rw [inner_self_im_eq_zero S, inner_self_im_eq_zero T']⟩
    refine ge_of_tendsto (re_diag_tendsto_of_wot hT' x) ?_
    filter_upwards [eventually_ge_atTop (⟨S, hS⟩ : D)] with T hT
    exact re_inner_mono hT x
  · intro c hc
    have hcim : c.im = 0 := by
      have h := Complex.le_def.mp (hc ⟨d₀, hd₀, rfl⟩)
      rw [← h.2, inner_self_im_eq_zero d₀]
    rw [Complex.le_def]
    refine ⟨?_, by rw [inner_self_im_eq_zero T', hcim]⟩
    refine le_of_tendsto (re_diag_tendsto_of_wot hT' x) (Eventually.of_forall fun T => ?_)
    exact (Complex.le_def.mp (hc ⟨T.1, T.2, rfl⟩)).1

/-- **37XI** (cstar.tex:6408, Definition), well-definedness claim: every
nonempty norm-bounded directed subset `D` of the self-adjoint part of B(H)
has a supremum there (this repackages **37IX**: norm-boundedness gives the
pointwise bounds `sup_{T ∈ D} ⟪x, T x⟫ < ∞`). -/
theorem exists_isLUB_of_normBounded_directed (D : Set (selfAdjoint (H →L[ℂ] H)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    ∃ s : selfAdjoint (H →L[ℂ] H), IsLUB D s := by
  obtain ⟨C, hC⟩ := hbdd
  have hb : ∀ x : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D) := by
    intro x
    refine ⟨((C * ‖x‖ ^ 2 : ℝ) : ℂ), ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    rw [Complex.le_def]
    refine ⟨?_, by rw [inner_self_im_eq_zero T, Complex.ofReal_im]⟩
    rw [Complex.ofReal_re]
    calc (⟪x, (T : H →L[ℂ] H) x⟫).re ≤ ‖⟪x, (T : H →L[ℂ] H) x⟫‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖(T : H →L[ℂ] H) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (C * ‖x‖) := by
          gcongr
          exact ((T : H →L[ℂ] H).le_opNorm x).trans (by gcongr; exact hC T hT)
      _ = C * ‖x‖ ^ 2 := by ring
  obtain ⟨T', hT'⟩ := hilb_suprema_1 D hne hdir hb
  exact ⟨T', hilb_suprema_2 D hne hdir hb T' hT'⟩

/-- **37XI** (cstar.tex:6408, Definition): the supremum `⋁ D` of a nonempty
norm-bounded directed subset `D` of the self-adjoint part of B(H), which
exists by **37IX** (`exists_isLUB_of_normBounded_directed`). -/
noncomputable def bhSup (D : Set (selfAdjoint (H →L[ℂ] H)))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧
      ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    selfAdjoint (H →L[ℂ] H) :=
  (exists_isLUB_of_normBounded_directed D h.1 h.2.1 h.2.2).choose

/-- **37XI** (cstar.tex:6408, Definition): `⋁ D` is the least upper bound of
`D`. -/
theorem isLUB_bhSup (D : Set (selfAdjoint (H →L[ℂ] H)))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧
      ∃ C : ℝ, ∀ T ∈ D, ‖(T : H →L[ℂ] H)‖ ≤ C) :
    IsLUB D (bhSup D h) :=
  (exists_isLUB_of_normBounded_directed D h.1 h.2.1 h.2.2).choose_spec

/-! ## Parsec 380: Normal functionals on B(H) -/

/-- **38I** (`bh-normal`, cstar.tex:6419, Definition): a positive functional
`ω : B(H) → ℂ` is *normal* when `ω (⋁ D) = ⋁_{T ∈ D} ω T` for every bounded
directed subset `D` of the self-adjoint part of B(H).  This is precisely
`Theses.PreservesDirSups` from `Theses.Common` (specialized to `A = B(H)`,
where every nonempty bounded directed set of self-adjoint elements actually
has a supremum, by **37IX**); the *normal positive functionals* on B(H) are
`Theses.NPFunctional (H →L[ℂ] H)`.

**38Ia** (`bh-normal-abbreviation`, cstar.tex:6427, Notation): "n" abbreviates
"normal": np-map, npu-map, … — cf. `Theses.NPFunctional`; not converted
separately. -/
abbrev BHNormal (ω : (H →L[ℂ] H) → ℂ) : Prop :=
  PreservesDirSups ω

/-- **38II** (cstar.tex:6434, Example): all vector functionals `⟪x, (·) x⟫` on
B(H) are normal, by **37IX**. -/
theorem vector_functional_normal (x : H) :
    BHNormal (fun T : H →L[ℂ] H => ⟪x, T x⟫) := by
  intro D s hne hdir hlub
  have hb : ∀ y : H,
      BddAbove ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪y, (T : H →L[ℂ] H) y⟫) '' D) := by
    intro y
    refine ⟨⟪y, (s : H →L[ℂ] H) y⟫, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    rw [Complex.le_def]
    exact ⟨re_inner_mono (Subtype.coe_le_coe.mpr (hlub.1 hT)) y,
      by rw [inner_self_im_eq_zero T, inner_self_im_eq_zero s]⟩
  obtain ⟨T', hT'⟩ := hilb_suprema_1 D hne hdir hb
  have h3 := hilb_suprema_3 D hne hdir hb T' hT' x
  rwa [(hilb_suprema_2 D hne hdir hb T' hT').unique hlub] at h3

/-- An operator whose diagonal values are all real is self-adjoint.
(Auxiliary for **38III**.) -/
private theorem isSelfAdjoint_of_re_diag {T : H →L[ℂ] H}
    (h : ∀ x : H, (((⟪x, T x⟫).re : ℝ) : ℂ) = ⟪x, T x⟫) : IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h2 : (⟪T v, v⟫ : ℂ) = (((⟪v, T v⟫).re : ℝ) : ℂ) := by
    rw [← inner_conj_symm (T v) v, ← h v, Complex.conj_ofReal, Complex.ofReal_re]
  simp only [ContinuousLinearMap.coe_coe]
  rw [h2, Complex.conj_ofReal]

/-- Multiplication by a nonnegative real is monotone for the order on `ℂ`.
(Auxiliary for **38III**.) -/
private theorem ofReal_mul_le_ofReal_mul {r : ℝ} (hr : 0 ≤ r) {z w : ℂ} (h : z ≤ w) :
    (r : ℂ) * z ≤ (r : ℂ) * w := by
  rw [Complex.le_def] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left h.1 hr
  · rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, h.2]

/-- Bound on the diagonal values of a bounded operator.  (Auxiliary for
**38III**.) -/
private theorem re_inner_le_norm_mul (T : H →L[ℂ] H) (x : H) :
    (⟪x, T x⟫).re ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc (⟪x, T x⟫).re ≤ ‖⟪x, T x⟫‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm _
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- **38III** (`bh-normal-effects`, cstar.tex:6439, Exercise): a positive
functional `ω : B(H) → ℂ` is normal provided it preserves suprema of directed
sets of *effects* (self-adjoint `T` with `0 ≤ T ≤ 1`). -/
theorem bh_normal_effects (ω : (H →L[ℂ] H) →ₚ[ℂ] ℂ)
    (h : ∀ (D : Set (selfAdjoint (H →L[ℂ] H))) (s : selfAdjoint (H →L[ℂ] H)),
      D.Nonempty → DirectedOn (· ≤ ·) D →
      (∀ T ∈ D, 0 ≤ (T : H →L[ℂ] H) ∧ (T : H →L[ℂ] H) ≤ 1) →
      IsLUB D s →
      IsLUB ((fun d : selfAdjoint (H →L[ℂ] H) => ω (d : H →L[ℂ] H)) '' D)
        (ω (s : H →L[ℂ] H))) :
    BHNormal (⇑ω) := by
  intro D s hne hdir hlub
  obtain ⟨d₀, hd₀⟩ := hne
  set M : ℝ := ‖(s : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)‖ + 1 with hMdef
  have hM : 0 < M := by positivity
  -- the affine rescaling `a ↦ M⁻¹ (a - d₀)` and its diagonal values
  have hdiag : ∀ (r : ℝ) (a b : H →L[ℂ] H) (x : H),
      ⟪x, (((r : ℝ) : ℂ) • (a - b)) x⟫ = ((r : ℝ) : ℂ) * (⟪x, a x⟫ - ⟪x, b x⟫) := by
    intro r a b x
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, inner_smul_right,
      inner_sub_right]
  have hdiagre : ∀ (r : ℝ) (a b : H →L[ℂ] H) (x : H),
      (⟪x, (((r : ℝ) : ℂ) • (a - b)) x⟫).re = r * ((⟪x, a x⟫).re - (⟪x, b x⟫).re) := by
    intro r a b x
    rw [hdiag, Complex.re_ofReal_mul, Complex.sub_re]
  have hsaSub : ∀ (r : ℝ) (a b : selfAdjoint (H →L[ℂ] H)),
      IsSelfAdjoint (((r : ℝ) : ℂ) • ((a : H →L[ℂ] H) - (b : H →L[ℂ] H))) := by
    intro r a b
    refine isSelfAdjoint_of_re_diag fun x => ?_
    obtain ⟨u, hu⟩ : ∃ u : ℝ, (⟪x, (a : H →L[ℂ] H) x⟫ : ℂ) = (u : ℂ) :=
      ⟨_, (inner_self_ofReal_re a.2 x).symm⟩
    obtain ⟨v, hv⟩ : ∃ v : ℝ, (⟪x, (b : H →L[ℂ] H) x⟫ : ℂ) = (v : ℂ) :=
      ⟨_, (inner_self_ofReal_re b.2 x).symm⟩
    rw [hdiag, hu, hv]
    norm_num
  have hsaAdd : ∀ (r : ℝ) (a b : selfAdjoint (H →L[ℂ] H)),
      IsSelfAdjoint (((r : ℝ) : ℂ) • (a : H →L[ℂ] H) + (b : H →L[ℂ] H)) := by
    intro r a b
    refine isSelfAdjoint_of_re_diag fun x => ?_
    obtain ⟨u, hu⟩ : ∃ u : ℝ, (⟪x, (a : H →L[ℂ] H) x⟫ : ℂ) = (u : ℂ) :=
      ⟨_, (inner_self_ofReal_re a.2 x).symm⟩
    obtain ⟨v, hv⟩ : ∃ v : ℝ, (⟪x, (b : H →L[ℂ] H) x⟫ : ℂ) = (v : ℂ) :=
      ⟨_, (inner_self_ofReal_re b.2 x).symm⟩
    rw [ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.smul_apply,
      inner_smul_right, hu, hv]
    norm_num
  set g : selfAdjoint (H →L[ℂ] H) → selfAdjoint (H →L[ℂ] H) := fun a =>
    ⟨((M⁻¹ : ℝ) : ℂ) • ((a : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)), hsaSub M⁻¹ a d₀⟩ with hgdef
  have hMinv : (0 : ℝ) < M⁻¹ := by positivity
  -- `g` is an order isomorphism of the self-adjoint part
  have hgmono : ∀ a b : selfAdjoint (H →L[ℂ] H), a ≤ b ↔ g a ≤ g b := by
    intro a b
    constructor
    · intro hab
      rw [← Subtype.coe_le_coe]
      refine le_of_re_inner (hsaSub M⁻¹ a d₀) (hsaSub M⁻¹ b d₀) fun x => ?_
      rw [hdiagre, hdiagre]
      have h1 := re_inner_mono (Subtype.coe_le_coe.mpr hab) x
      nlinarith
    · intro hab
      rw [← Subtype.coe_le_coe]
      refine le_of_re_inner a.2 b.2 fun x => ?_
      have h1 := re_inner_mono (Subtype.coe_le_coe.mpr hab) x
      rw [hdiagre, hdiagre] at h1
      nlinarith
  have hgsurj : ∀ t : selfAdjoint (H →L[ℂ] H), ∃ u, g u = t := by
    intro t
    refine ⟨⟨((M : ℝ) : ℂ) • (t : H →L[ℂ] H) + (d₀ : H →L[ℂ] H), hsaAdd M t d₀⟩, ?_⟩
    apply Subtype.ext
    change ((M⁻¹ : ℝ) : ℂ) • ((((M : ℝ) : ℂ) • (t : H →L[ℂ] H) + (d₀ : H →L[ℂ] H))
      - (d₀ : H →L[ℂ] H)) = (t : H →L[ℂ] H)
    rw [add_sub_cancel_right, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hM.ne',
      Complex.ofReal_one, one_smul]
  -- the cofinal tail above `d₀` has the same supremum
  have hD₀dir : DirectedOn (· ≤ ·) {d ∈ D | d₀ ≤ d} := by
    rintro a ⟨haD, ha0⟩ b ⟨hbD, _⟩
    obtain ⟨c, hcD, hac, hbc⟩ := hdir a haD b hbD
    exact ⟨c, ⟨hcD, ha0.trans hac⟩, hac, hbc⟩
  have hD₀lub : IsLUB {d ∈ D | d₀ ≤ d} s := by
    constructor
    · rintro a ⟨haD, _⟩
      exact hlub.1 haD
    · intro t ht
      refine hlub.2 fun a haD => ?_
      obtain ⟨c, hcD, hac, h0c⟩ := hdir a haD d₀ hd₀
      exact hac.trans (ht ⟨hcD, h0c⟩)
  -- the rescaled tail is a directed set of effects with supremum `g s`
  have hEne : (g '' {d ∈ D | d₀ ≤ d}).Nonempty :=
    ⟨g d₀, Set.mem_image_of_mem g ⟨hd₀, le_refl _⟩⟩
  have hEdir : DirectedOn (· ≤ ·) (g '' {d ∈ D | d₀ ≤ d}) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hD₀dir a ha b hb
    exact ⟨g c, Set.mem_image_of_mem g hc, (hgmono a c).mp hac, (hgmono b c).mp hbc⟩
  have hEeff : ∀ T ∈ g '' {d ∈ D | d₀ ≤ d},
      0 ≤ (T : H →L[ℂ] H) ∧ (T : H →L[ℂ] H) ≤ 1 := by
    rintro _ ⟨a, ⟨haD, ha0⟩, rfl⟩
    have h1 := re_inner_mono (Subtype.coe_le_coe.mpr ha0)
    have h2 := re_inner_mono (Subtype.coe_le_coe.mpr (hlub.1 haD))
    constructor
    · refine le_of_re_inner (star_zero _) (hsaSub M⁻¹ a d₀) fun x => ?_
      rw [hdiagre]
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re]
      nlinarith [h1 x]
    · refine le_of_re_inner (hsaSub M⁻¹ a d₀) (star_one _) fun x => ?_
      rw [hdiagre]
      have h3 : (⟪x, ((s : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)) x⟫).re ≤ (M - 1) * ‖x‖ ^ 2 := by
        simpa [hMdef] using re_inner_le_norm_mul ((s : H →L[ℂ] H) - (d₀ : H →L[ℂ] H)) x
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at h3
      have h4 : (⟪x, (1 : H →L[ℂ] H) x⟫).re = ‖x‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
      have h5 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
      have h6 : M⁻¹ * M = 1 := inv_mul_cancel₀ hM.ne'
      rw [h4]
      nlinarith [h2 x]
  have hElub : IsLUB (g '' {d ∈ D | d₀ ≤ d}) (g s) := by
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      exact (hgmono a s).mp (hD₀lub.1 ha)
    · intro t ht
      obtain ⟨u, rfl⟩ := hgsurj t
      exact (hgmono s u).mp
        (hD₀lub.2 fun a ha => (hgmono a u).mpr (ht (Set.mem_image_of_mem g ha)))
  have hkey := h (g '' {d ∈ D | d₀ ≤ d}) (g s) hEne hEdir hEeff hElub
  -- transport back along `ω (g a) = M⁻¹ (ω a - ω d₀)`
  have hωg : ∀ a : selfAdjoint (H →L[ℂ] H),
      ω ((g a : H →L[ℂ] H)) =
        ((M⁻¹ : ℝ) : ℂ) * (ω (a : H →L[ℂ] H) - ω (d₀ : H →L[ℂ] H)) := by
    intro a
    change ω (((M⁻¹ : ℝ) : ℂ) • ((a : H →L[ℂ] H) - (d₀ : H →L[ℂ] H))) = _
    rw [map_smul, map_sub, smul_eq_mul]
  constructor
  · rintro _ ⟨a, haD, rfl⟩
    exact OrderHomClass.mono ω (Subtype.coe_le_coe.mpr (hlub.1 haD))
  · intro c hc
    have hub : ((M⁻¹ : ℝ) : ℂ) * (c - ω (d₀ : H →L[ℂ] H)) ∈
        upperBounds ((fun d : selfAdjoint (H →L[ℂ] H) => ω (d : H →L[ℂ] H)) ''
          (g '' {d ∈ D | d₀ ≤ d})) := by
      rintro _ ⟨_, ⟨a, ⟨haD, _⟩, rfl⟩, rfl⟩
      change ω ((g a : H →L[ℂ] H)) ≤ _
      rw [hωg a]
      exact ofReal_mul_le_ofReal_mul hMinv.le
        (sub_le_sub_right (hc (Set.mem_image_of_mem _ haD)) _)
    have h7 := hkey.2 hub
    rw [hωg s] at h7
    have h8 := ofReal_mul_le_ofReal_mul (le_of_lt hM) h7
    have h9 : ∀ z : ℂ, ((M : ℝ) : ℂ) * (((M⁻¹ : ℝ) : ℂ) * z) = z := by
      intro z
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hM.ne', Complex.ofReal_one,
        one_mul]
    rw [h9, h9] at h8
    exact (sub_le_sub_iff_right _).mp h8

/-- Monotonicity of the diagonal values, as an inequality in `ℂ` (the
`ComplexOrder`).  Note that `S ≤ T` does not force `S` and `T` themselves to be
self-adjoint — only their difference — so this is not a corollary of
`re_inner_mono`.  (Auxiliary for **38IV**.) -/
private theorem inner_le_inner_of_le {S T : H →L[ℂ] H} (h : S ≤ T) (y : H) :
    (⟪y, S y⟫ : ℂ) ≤ ⟪y, T y⟫ := by
  have h0 : (0 : H →L[ℂ] H) ≤ T - S := sub_nonneg.mpr h
  have hp := (ContinuousLinearMap.isPositive_iff_complex (T - S)).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h0) y
  have hswap : (⟪y, (T - S) y⟫ : ℂ) = ⟪(T - S) y, y⟫ := by
    rw [← inner_conj_symm y ((T - S) y), ← hp.1, Complex.conj_ofReal, hp.1]
  have hnn : (0 : ℂ) ≤ ⟪y, (T - S) y⟫ := by
    rw [hswap, ← hp.1, ← Complex.ofReal_zero, Complex.real_le_real]
    exact hp.2
  rw [ContinuousLinearMap.sub_apply, inner_sub_right] at hnn
  exact sub_nonneg.mp hnn

/-- **38IV** (`bh-functional-lemma`, cstar.tex:6448, Lemma), part 1
(convergence): for a sequence `x₁, x₂, …` in a Hilbert space `H` with
`∑ₙ ‖xₙ‖² < ∞` and any `T ∈ B(H)`, the sum `∑ₙ ⟪xₙ, T xₙ⟫` converges. -/
theorem bh_functional_lemma_1 (x : ℕ → H) (hx : Summable fun n => ‖x n‖ ^ 2)
    (T : H →L[ℂ] H) :
    Summable fun n => ⟪x n, T (x n)⟫ := by
  refine Summable.of_norm_bounded (hx.mul_left ‖T‖) fun n => ?_
  calc ‖⟪x n, T (x n)⟫‖ ≤ ‖x n‖ * ‖T (x n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x n‖ * (‖T‖ * ‖x n‖) := by gcongr; exact T.le_opNorm _
    _ = ‖T‖ * ‖x n‖ ^ 2 := by ring

/-- **38IV** (`bh-functional-lemma`, cstar.tex:6448, Lemma), part 2: every
sequence `x₁, x₂, …` in a Hilbert space `H` with `∑ₙ ‖xₙ‖² < ∞` gives an
np-map (normal positive functional) `ω : B(H) → ℂ` defined by
`ω T = ∑ₙ ⟪xₙ, T xₙ⟫`. -/
theorem bh_functional_lemma_2 (x : ℕ → H) (hx : Summable fun n => ‖x n‖ ^ 2) :
    ∃ ω : NPFunctional (H →L[ℂ] H),
      ∀ T : H →L[ℂ] H, ω T = ∑' n, ⟪x n, T (x n)⟫ := by
  classical
  have hsum : ∀ T : H →L[ℂ] H, Summable fun n => ⟪x n, T (x n)⟫ :=
    fun T => bh_functional_lemma_1 x hx T
  refine ⟨⟨{ toFun := fun T => ∑' n, ⟪x n, T (x n)⟫
             map_add' := fun S T => by
               rw [← (hsum S).tsum_add (hsum T)]
               exact tsum_congr fun n => by simp [inner_add_right]
             map_smul' := fun c T => by
               rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
               exact tsum_congr fun n => by simp [inner_smul_right]
             monotone' := fun S T hST =>
               (hsum S).tsum_le_tsum (fun n => inner_le_inner_of_le hST (x n)) (hsum T) },
      ?_⟩, fun T => rfl⟩
  -- Normality.  Following the thesis, we reduce to directed sets of *effects*
  -- (**38III**), which makes every diagonal value `⟪xₙ, T xₙ⟫` nonnegative, and
  -- then interchange the two suprema.
  refine bh_normal_effects _ ?_
  intro D s hne hdir heff hlub
  haveI : Nonempty D := hne.to_subtype
  haveI : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  set r : ℕ → selfAdjoint (H →L[ℂ] H) → ℝ :=
    fun n T => (⟪x n, (T : H →L[ℂ] H) (x n)⟫).re with hr
  have hreal : ∀ (n : ℕ) (T : selfAdjoint (H →L[ℂ] H)),
      ((r n T : ℝ) : ℂ) = ⟪x n, (T : H →L[ℂ] H) (x n)⟫ :=
    fun n T => inner_self_ofReal_re T.2 (x n)
  have hsumr : ∀ T : selfAdjoint (H →L[ℂ] H), Summable fun n => r n T := fun T =>
    (hsum (T : H →L[ℂ] H)).map Complex.reCLM Complex.reCLM.continuous
  have htsum : ∀ T : selfAdjoint (H →L[ℂ] H),
      ((∑' n, r n T : ℝ) : ℂ) = ∑' n, ⟪x n, (T : H →L[ℂ] H) (x n)⟫ := fun T => by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => hreal n T
  -- the elements of `D`, and hence their supremum, are positive
  have hnnD : ∀ T ∈ D, ∀ n, 0 ≤ r n T := by
    intro T hT n
    simpa using re_inner_mono (heff T hT).1 (x n)
  have hnns : ∀ n, 0 ≤ r n s := by
    obtain ⟨d₀, hd₀⟩ := hne
    intro n
    exact (hnnD d₀ hd₀ n).trans (re_inner_mono (Subtype.coe_le_coe.mpr (hlub.1 hd₀)) (x n))
  -- each vector functional is normal (**38II**); transported to `ℝ`
  have hLR : ∀ n : ℕ, IsLUB (Set.range fun T : D => r n T.1) (r n s) := by
    intro n
    have h := vector_functional_normal (x n) D s hne hdir hlub
    constructor
    · rintro _ ⟨T, rfl⟩
      exact (Complex.le_def.mp (h.1 ⟨T.1, T.2, rfl⟩)).1
    · intro cr hcr
      have hub : ((cr : ℝ) : ℂ) ∈ upperBounds
          ((fun d : selfAdjoint (H →L[ℂ] H) => ⟪x n, (d : H →L[ℂ] H) (x n)⟫) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        show (⟪x n, (d : H →L[ℂ] H) (x n)⟫ : ℂ) ≤ ((cr : ℝ) : ℂ)
        rw [← hreal n d, Complex.real_le_real]
        exact hcr ⟨⟨d, hd⟩, rfl⟩
      have h2 : (⟪x n, (s : H →L[ℂ] H) (x n)⟫ : ℂ) ≤ ((cr : ℝ) : ℂ) := h.2 hub
      rw [← hreal n s, Complex.real_le_real] at h2
      exact h2
  have hmonoR : ∀ n : ℕ, Monotone fun T : D => r n T.1 := fun n _ _ hST =>
    re_inner_mono (Subtype.coe_le_coe.mpr (Subtype.coe_le_coe.mpr hST)) (x n)
  have htend : ∀ n : ℕ, Tendsto (fun T : D => r n T.1) atTop (𝓝 (r n s)) := fun n =>
    tendsto_atTop_isLUB (hmonoR n) (hLR n)
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact (hsum _).tsum_le_tsum
      (fun n => inner_le_inner_of_le (Subtype.coe_le_coe.mpr (hlub.1 hd)) (x n)) (hsum _)
  · intro c hc
    -- `c` dominates the (real) values `ω d` for `d ∈ D`, hence is itself real
    obtain ⟨d₀, hd₀⟩ := hne
    have hcre : ∀ d ∈ D, (∑' n, r n d) ≤ c.re := by
      intro d hd
      have h := hc ⟨d, hd, rfl⟩
      change (∑' n, ⟪x n, (d : H →L[ℂ] H) (x n)⟫) ≤ c at h
      rw [← htsum d] at h
      exact (Complex.le_def.mp h).1
    have hcim : c.im = 0 := by
      have h := hc ⟨d₀, hd₀, rfl⟩
      change (∑' n, ⟪x n, (d₀ : H →L[ℂ] H) (x n)⟫) ≤ c at h
      rw [← htsum d₀] at h
      simpa using (Complex.le_def.mp h).2.symm
    show (∑' n, ⟪x n, (s : H →L[ℂ] H) (x n)⟫) ≤ c
    rw [← htsum s, ← Complex.re_add_im c, hcim]
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.real_le_real]
    -- the interchange of suprema: each finite partial sum of the `r n s` is a
    -- limit of the corresponding partial sums along `D`, and those are bounded
    -- by `c.re`
    refine (hsumr s).tsum_le_of_sum_le fun F => ?_
    refine le_of_tendsto (tendsto_finsetSum F fun n _ => htend n) (Eventually.of_forall ?_)
    intro T
    refine le_trans ?_ (hcre T.1 T.2)
    exact (hsumr T.1).sum_le_tsum F (fun n _ => hnnD T.1 T.2 n)

/-- The vector functional `⟪x, (·) x⟫ : B(H) → ℂ` bundled as a continuous
linear functional (auxiliary for **38VI**). -/
noncomputable def vectorFunctionalCLM (x : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)

omit [CompleteSpace H] in
@[simp]
theorem vectorFunctionalCLM_apply (x : H) (T : H →L[ℂ] H) :
    vectorFunctionalCLM x T = ⟪x, T x⟫ :=
  rfl

/-- **38VI** (`vector-functional-convergence`, cstar.tex:6493, Exercise),
part 1: for a family `(x_α)_α` in a Hilbert space `H`, `∑_α ‖x_α‖² < ∞` if and
only if `∑_α ⟪x_α, (·) x_α⟫` converges with respect to the operator norm to
some bounded functional on B(H). -/
theorem vector_functional_convergence_1 {ι : Type*} (x : ι → H) :
    (Summable fun α => ‖x α‖ ^ 2) ↔
      ∃ φ : (H →L[ℂ] H) →L[ℂ] ℂ, HasSum (fun α => vectorFunctionalCLM (x α)) φ := by
  classical
  have hnorm : ∀ α, ‖vectorFunctionalCLM (x α)‖ ≤ ‖x α‖ ^ 2 := by
    intro α
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T => ?_
    calc ‖vectorFunctionalCLM (x α) T‖ = ‖⟪x α, T (x α)⟫‖ := rfl
      _ ≤ ‖x α‖ * ‖T (x α)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x α‖ * (‖T‖ * ‖x α‖) := by gcongr; exact T.le_opNorm _
      _ = ‖x α‖ ^ 2 * ‖T‖ := by ring
  have hone : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    simpa [ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1)
  have hsum1 : ∀ G : Finset ι,
      ((∑ α ∈ G, vectorFunctionalCLM (x α)) 1 : ℂ) = ((∑ α ∈ G, ‖x α‖ ^ 2 : ℝ) : ℂ) := by
    intro G
    rw [ContinuousLinearMap.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [vectorFunctionalCLM_apply, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
    simp
  have hle : ∀ G : Finset ι,
      (∑ α ∈ G, ‖x α‖ ^ 2 : ℝ) ≤ ‖∑ α ∈ G, vectorFunctionalCLM (x α)‖ := by
    intro G
    have h1 : ‖((∑ α ∈ G, vectorFunctionalCLM (x α)) 1 : ℂ)‖ ≤
        ‖∑ α ∈ G, vectorFunctionalCLM (x α)‖ * ‖(1 : H →L[ℂ] H)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [hsum1 G, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : (0 : ℝ) ≤ ∑ α ∈ G, ‖x α‖ ^ 2 := Finset.sum_nonneg fun α _ => by positivity
    have h3 : (0 : ℝ) ≤ ‖∑ α ∈ G, vectorFunctionalCLM (x α)‖ := norm_nonneg _
    rw [abs_of_nonneg h2] at h1
    nlinarith
  constructor
  · intro hs
    exact ⟨_, (Summable.of_norm_bounded hs hnorm).hasSum⟩
  · rintro ⟨φ, hφ⟩
    obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp
      (hφ.eventually (Metric.ball_mem_nhds φ one_pos))
    refine summable_of_sum_le (c := ‖φ‖ + 1) (fun α => by positivity) fun F => ?_
    calc (∑ α ∈ F, ‖x α‖ ^ 2) ≤ ∑ α ∈ F ∪ F₀, ‖x α‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            fun α _ _ => by positivity
      _ ≤ ‖∑ α ∈ F ∪ F₀, vectorFunctionalCLM (x α)‖ := hle _
      _ ≤ ‖φ‖ + 1 := by
          have hb := hF₀ (F ∪ F₀) Finset.subset_union_right
          have hd : ‖(∑ α ∈ F ∪ F₀, vectorFunctionalCLM (x α)) - φ‖ < 1 := by
            simpa [dist_eq_norm] using hb
          have := norm_sub_norm_le (∑ α ∈ F ∪ F₀, vectorFunctionalCLM (x α)) φ
          linarith

/-- **38VI** (`vector-functional-convergence`, cstar.tex:6493, Exercise),
part 2: for a net `(x_α)_α` in a Hilbert space `H` and `x ∈ H`, if `x_α → x`
then `⟪x_α, (·) x_α⟫` operator-norm converges to `⟪x, (·) x⟫`.

(The converse is false — the constant net `x_α = i • x` with `x ≠ 0` induces
the same vector functional as `x` — and erratum `parsec-380.60` drops it from
the Exercise, together with its hint; the direction below is the only one used
later on.) -/
theorem vector_functional_convergence_2 {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : ι → H) (x₀ : H) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun α => vectorFunctionalCLM (x α)) l (𝓝 (vectorFunctionalCLM x₀)) := by
  -- The thesis publishes no solution for parsec 380, so this argument is ours.
  -- The estimate is the polarisation-free one: split the difference of the two
  -- vector functionals as `⟪y-x, T y⟫ + ⟪x, T (y-x)⟫`, so that it is bounded by
  -- `‖y - x‖ (‖y‖ + ‖x‖)` uniformly in `‖T‖ ≤ 1`.
  have key : ∀ y : H, ‖vectorFunctionalCLM y - vectorFunctionalCLM x₀‖
      ≤ ‖y - x₀‖ * (‖y‖ + ‖x₀‖) := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T => ?_
    have hsplit : (vectorFunctionalCLM y - vectorFunctionalCLM x₀) T
        = ⟪y - x₀, T y⟫ + ⟪x₀, T (y - x₀)⟫ := by
      simp only [ContinuousLinearMap.sub_apply, vectorFunctionalCLM_apply,
        inner_sub_left, map_sub, inner_sub_right]
      ring
    rw [hsplit]
    have b1 : ‖⟪y - x₀, T y⟫‖ ≤ ‖y - x₀‖ * (‖T‖ * ‖y‖) :=
      (norm_inner_le_norm _ _).trans <|
        mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    have b2 : ‖⟪x₀, T (y - x₀)⟫‖ ≤ ‖x₀‖ * (‖T‖ * ‖y - x₀‖) :=
      (norm_inner_le_norm _ _).trans <|
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    calc ‖⟪y - x₀, T y⟫ + ⟪x₀, T (y - x₀)⟫‖
        ≤ ‖⟪y - x₀, T y⟫‖ + ‖⟪x₀, T (y - x₀)⟫‖ := norm_add_le _ _
      _ ≤ ‖y - x₀‖ * (‖T‖ * ‖y‖) + ‖x₀‖ * (‖T‖ * ‖y - x₀‖) := add_le_add b1 b2
      _ = ‖y - x₀‖ * (‖y‖ + ‖x₀‖) * ‖T‖ := by ring
  -- `‖x_α - x₀‖ → 0` while `‖x_α‖ + ‖x₀‖ → 2‖x₀‖`, so the bound tends to `0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun α => norm_nonneg _) (fun α => key (x α)) ?_
  have h1 : Tendsto (fun α => ‖x α - x₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h2 : Tendsto (fun α => ‖x α‖ + ‖x₀‖) l (𝓝 (‖x₀‖ + ‖x₀‖)) :=
    (hx.norm).add tendsto_const_nhds
  simpa using h1.mul h2

/-! ## Parsec 390: Orthonormal bases and the normality theorem for B(H)

**39I** (cstar.tex:6514): introduction to the final project — every normal
positive functional on B(H) is `∑ₙ ⟪xₙ, (·) xₙ⟫`; nothing to formalize. -/

/-- **39II** (cstar.tex:6525, Definition): a subset `E` of a Hilbert space is
*orthonormal* if `⟪e, e'⟫ = 0` for distinct `e, e' ∈ E` and `⟪e, e⟫ = 1` for
`e ∈ E` (Mathlib: `Orthonormal ℂ ((↑) : E → H)`); a *maximal* orthonormal
subset is called an *orthonormal basis* (cf. Mathlib's `HilbertBasis`, and
`exists_hilbertBasis`; **39III**, Remark: every Hilbert space has one, by
Zorn's lemma — not converted separately). -/
def IsOrthonormalBasis (E : Set H) : Prop :=
  Orthonormal ℂ ((↑) : E → H) ∧
    ∀ E' : Set H, E ⊆ E' → Orthonormal ℂ ((↑) : E' → H) → E' = E

/-- **39IV** (`orthonormal`, cstar.tex:6549, Proposition), part 1 (Bessel's
inequality): for an orthonormal subset `E` of a Hilbert space `H` and `x ∈ H`,
`∑_{e ∈ E} |⟪e, x⟫|² ≤ ‖x‖²` (the sum in particular converges).  Mathlib:
`Orthonormal.tsum_inner_products_le`. -/
theorem orthonormal_1 (E : Set H) (hE : Orthonormal ℂ ((↑) : E → H)) (x : H) :
    (Summable fun e : E => ‖⟪(e : H), x⟫‖ ^ 2) ∧
      ∑' e : E, ‖⟪(e : H), x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  ⟨hE.inner_products_summable x, hE.tsum_inner_products_le x⟩

/-- **39IV** (`orthonormal`, cstar.tex:6549, Proposition), part 2: for an
orthonormal subset `E` and `x ∈ H`, the sum `∑_{e ∈ E} ⟪e, x⟫ e` converges in
`H`. -/
theorem orthonormal_2 (E : Set H) (hE : Orthonormal ℂ ((↑) : E → H)) (x : H) :
    ∃ y : H, HasSum (fun e : E => ⟪(e : H), x⟫ • (e : H)) y := by
  have hmem : Memℓp (fun e : E => (⟪(e : H), x⟫ : ℂ)) 2 :=
    memℓp_gen (by simpa using hE.inner_products_summable x)
  have hs := hE.orthogonalFamily.summable_of_lp ⟨_, hmem⟩
  simp only [LinearIsometry.toSpanSingleton_apply] at hs
  exact ⟨_, hs.hasSum⟩

/-- **39IV** (`orthonormal`, cstar.tex:6549, Proposition), part 3: if `E` is a
maximal orthonormal subset (an orthonormal basis), then
`∑_{e ∈ E} ⟪e, x⟫ e = x` for every `x ∈ H`. -/
theorem orthonormal_3 (E : Set H) (hE : IsOrthonormalBasis E) (x : H) :
    HasSum (fun e : E => ⟪(e : H), x⟫ • (e : H)) x := by
  have hsp : (Submodule.span ℂ (Set.range ((↑) : E → H)))ᗮ = ⊥ := by
    have h := (maximal_orthonormal_iff_orthogonalComplement_eq_bot hE.1).mp
      (fun u hu hu' => hE.2 u hu hu')
    simpa [Subtype.range_coe] using h
  have hb := (HilbertBasis.mkOfOrthogonalEqBot hE.1 hsp).hasSum_repr x
  simpa [HilbertBasis.repr_apply_apply, HilbertBasis.coe_mkOfOrthogonalEqBot] using hb

/-- **39IV** (`orthonormal`, cstar.tex:6549, Proposition), part 4 (Parseval's
identity): if `E` is an orthonormal basis, then
`∑_{e ∈ E} |⟪e, x⟫|² = ‖x‖²` for every `x ∈ H`. -/
theorem orthonormal_4 (E : Set H) (hE : IsOrthonormalBasis E) (x : H) :
    HasSum (fun e : E => ‖⟪(e : H), x⟫‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (orthonormal_3 E hE x).mapL (innerSL ℂ x)
  simp only [innerSL_apply_apply] at h
  have key : ∀ e : E, ⟪x, ⟪(e : H), x⟫ • (e : H)⟫ = ((‖⟪(e : H), x⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro e
    rw [inner_smul_right, ← inner_conj_symm x (e : H), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hx : ⟪x, x⟫ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hx] at h
  simp only [key] at h
  exact_mod_cast h

/-! The rank-one operator `|x⟩⟨y| : z ↦ ⟪y, z⟫ • x` is **4XIX** (`ketbra`,
cstar.tex:671), defined in `Theses.A.CStar.Basic` and imported here. -/

/-- **39VI** (`sum-ketbras`, cstar.tex:6622, Exercise), part 1: for an
orthonormal basis `E` of a Hilbert space `H`, `∑_{e ∈ E} |e⟩⟨e|` converges to
`1` in the weak operator topology. -/
theorem sum_ketbras_1 (E : Set H) (hE : IsOrthonormalBasis E) :
    HasSum (fun e : E => ContinuousLinearMapWOT.ofCLM (ketbra (e : H) (e : H)))
      (ContinuousLinearMapWOT.ofCLM (1 : H →L[ℂ] H)) := by
  have key : ∀ (s : Finset E) (z : H),
      (∑ e ∈ s, ContinuousLinearMapWOT.ofCLM (ketbra (e : H) (e : H))) z
        = ∑ e ∈ s, ⟪(e : H), z⟫ • (e : H) := by
    classical
    intro s z
    induction s using Finset.induction with
    | empty => simp
    | insert e s he ih =>
        rw [Finset.sum_insert he, Finset.sum_insert he, ContinuousLinearMapWOT.add_apply, ih]
        simp [ketbra]
  rw [HasSum, ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
  intro x y
  have h := (orthonormal_3 E hE x).mapL (innerSL ℂ y)
  simpa [key, inner_sum, ContinuousLinearMapWOT.ofCLM_apply, HasSum] using h

/-- **39VI** (`sum-ketbras`, cstar.tex:6622, Exercise), part 2:
`∑_{e ∈ E} |e⟩⟨e| = 1` also in the sense that the directed set of partial sums
`∑_{e ∈ F} |e⟩⟨e|` over finite `F ⊆ E` has `1` as its supremum in B(H). -/
theorem sum_ketbras_2 (E : Set H) (hE : IsOrthonormalBasis E) :
    IsLUB {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)}
      1 := by
  classical
  have hket : ∀ (F : Finset E) (x : H),
      (∑ e ∈ F, ketbra (e : H) (e : H)) x = ∑ e ∈ F, ⟪(e : H), x⟫ • (e : H) := by
    intro F x
    induction F using Finset.induction with
    | empty => simp
    | insert e s he ih =>
        rw [Finset.sum_insert he, Finset.sum_insert he, ContinuousLinearMap.add_apply, ih]
        simp [ketbra]
  have hinner : ∀ (F : Finset E) (x : H),
      ⟪x, (∑ e ∈ F, ketbra (e : H) (e : H)) x⟫
        = ((∑ e ∈ F, ‖⟪(e : H), x⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro F x
    rw [hket F x, inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [inner_smul_right, ← inner_conj_symm x (e : H), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    norm_cast
  have hsa : ∀ F : Finset E, IsSelfAdjoint (∑ e ∈ F, ketbra (e : H) (e : H)) := by
    intro F
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp only [ContinuousLinearMap.coe_coe, hket]
    rw [sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [inner_smul_left, inner_smul_right, ← inner_conj_symm x (e : H)]
    ring
  have hone : ∀ x : H, (⟪x, (1 : H →L[ℂ] H) x⟫).re = ‖x‖ ^ 2 := by
    intro x
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
  constructor
  · rintro S ⟨F, rfl⟩
    refine le_of_re_inner (hsa F) (star_one _) fun x => ?_
    rw [hinner F x, hone x, Complex.ofReal_re]
    exact hE.1.sum_inner_products_le x
  · intro T hT
    have h0 : (0 : H →L[ℂ] H) ≤ T := by
      have h := hT (⟨(∅ : Finset E), by simp⟩ :
        (0 : H →L[ℂ] H) ∈ {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)})
      exact h
    have hTsa : IsSelfAdjoint T :=
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp h0).isSelfAdjoint
    refine le_of_re_inner (star_one _) hTsa fun x => ?_
    rw [hone x]
    refine hasSum_le_of_sum_le (orthonormal_4 E hE x) fun F => ?_
    have hle := re_inner_mono (hT (⟨F, rfl⟩ :
      (∑ e ∈ F, ketbra (e : H) (e : H)) ∈
        {S : H →L[ℂ] H | ∃ F : Finset E, S = ∑ e ∈ F, ketbra (e : H) (e : H)})) x
    rw [hinner F x, Complex.ofReal_re] at hle
    exact hle

/-- The action of a finite sum of `|e⟩⟨e|`.  (Auxiliary for **39VI**.) -/
private theorem ketbra_sum_apply {E : Set H} (F : Finset E) (x : H) :
    (∑ e ∈ F, ketbra (e : H) (e : H)) x = ∑ e ∈ F, ⟪(e : H), x⟫ • (e : H) := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | insert e s he ih =>
      rw [Finset.sum_insert he, Finset.sum_insert he, ContinuousLinearMap.add_apply, ih]
      simp [ketbra]

/-- The diagonal values of a finite sum of `|e⟩⟨e|`.  (Auxiliary for **39VI**.) -/
private theorem ketbra_sum_inner {E : Set H} (F : Finset E) (x : H) :
    ⟪x, (∑ e ∈ F, ketbra (e : H) (e : H)) x⟫ = ((∑ e ∈ F, ‖⟪(e : H), x⟫‖ ^ 2 : ℝ) : ℂ) := by
  rw [ketbra_sum_apply F x, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [inner_smul_right, ← inner_conj_symm x (e : H), Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

/-- A finite sum of `|e⟩⟨e|` is self-adjoint.  (Auxiliary for **39VI**.) -/
private theorem ketbra_sum_isSelfAdjoint {E : Set H} (F : Finset E) :
    IsSelfAdjoint (∑ e ∈ F, ketbra (e : H) (e : H)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ketbra_sum_apply]
  rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [inner_smul_left, inner_smul_right, ← inner_conj_symm x (e : H)]
  ring

/-- The finite sums of `|e⟩⟨e|` increase with the index set.  (Auxiliary for
**39VI**.) -/
private theorem ketbra_sum_mono {E : Set H} {F G : Finset E} (h : F ⊆ G) :
    (∑ e ∈ F, ketbra (e : H) (e : H)) ≤ ∑ e ∈ G, ketbra (e : H) (e : H) :=
  le_of_re_inner (ketbra_sum_isSelfAdjoint F) (ketbra_sum_isSelfAdjoint G) fun x => by
    rw [ketbra_sum_inner, ketbra_sum_inner, Complex.ofReal_re, Complex.ofReal_re]
    exact Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- The finite sums of `|e⟩⟨e|` are positive.  (Auxiliary for **39VII**.) -/
private theorem ketbra_sum_nonneg {E : Set H} (F : Finset E) :
    (0 : H →L[ℂ] H) ≤ ∑ e ∈ F, ketbra (e : H) (e : H) := by
  simpa using ketbra_sum_mono (F := (∅ : Finset E)) (G := F) (by simp)

/-- The finite sums of `|e⟩⟨e|` over an orthonormal set are below `1` (Bessel).
(Auxiliary for **39VII**.) -/
private theorem ketbra_sum_le_one {E : Set H} (hE : Orthonormal ℂ ((↑) : E → H))
    (F : Finset E) : (∑ e ∈ F, ketbra (e : H) (e : H)) ≤ 1 :=
  le_of_re_inner (ketbra_sum_isSelfAdjoint F) (star_one _) fun x => by
    rw [ketbra_sum_inner F x, Complex.ofReal_re]
    have h : (⟪x, (1 : H →L[ℂ] H) x⟫).re = ‖x‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [h]
    exact hE.sum_inner_products_le x

/-- Consequently `‖∑_{e ∈ F} |e⟩⟨e|‖ ≤ 1`.  (Auxiliary for **39VII**.) -/
private theorem ketbra_sum_norm_le_one {E : Set H} (hE : Orthonormal ℂ ((↑) : E → H))
    (F : Finset E) : ‖∑ e ∈ F, ketbra (e : H) (e : H)‖ ≤ 1 := by
  refine le_trans (CStarAlgebra.norm_le_norm_of_nonneg_of_le (ketbra_sum_nonneg F)
    (ketbra_sum_le_one hE F)) ?_
  simpa [ContinuousLinearMap.one_def] using
    (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1)

/-- The sandwich `P A P` of an operator between the projections
`P = ∑_{e ∈ F} |e⟩⟨e|` expands as `∑_{e, e' ∈ F} ⟪e, A e'⟫ |e⟩⟨e'|`.  This is
the identity opening the thesis's proof of **39VII**. -/
private theorem ketbra_sum_sandwich {E : Set H} (F : Finset E) (A : H →L[ℂ] H) :
    (∑ e ∈ F, ketbra (e : H) (e : H)) * A * (∑ e ∈ F, ketbra (e : H) (e : H))
      = ∑ e ∈ F, ∑ e' ∈ F, (⟪(e : H), A (e' : H)⟫ : ℂ) • ketbra (e : H) (e' : H) := by
  ext z
  have hL : ((∑ e ∈ F, ketbra (e : H) (e : H)) * A * (∑ e ∈ F, ketbra (e : H) (e : H))) z
      = ∑ e ∈ F, ∑ e' ∈ F, ((⟪(e' : H), z⟫ * ⟪(e : H), A (e' : H)⟫ : ℂ)) • (e : H) := by
    change (∑ e ∈ F, ketbra (e : H) (e : H)) (A ((∑ e ∈ F, ketbra (e : H) (e : H)) z)) = _
    rw [ketbra_sum_apply, ketbra_sum_apply, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [inner_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [map_smul, inner_smul_right]
  have hR : (∑ e ∈ F, ∑ e' ∈ F, (⟪(e : H), A (e' : H)⟫ : ℂ) • ketbra (e : H) (e' : H)) z
      = ∑ e ∈ F, ∑ e' ∈ F, ((⟪(e : H), A (e' : H)⟫ * ⟪(e' : H), z⟫ : ℂ)) • (e : H) := by
    rw [sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [sum_apply]
    refine Finset.sum_congr rfl fun e' _ => ?_
    simp [ketbra, smul_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => by rw [mul_comm]

/-- `P = ∑_{e ∈ F} |e⟩⟨e|` is idempotent when `E` is orthonormal — it is the
orthogonal projection onto the span of `F`.  (Auxiliary for **39VII**.) -/
private theorem ketbra_sum_idem {E : Set H} (hE : Orthonormal ℂ ((↑) : E → H))
    (F : Finset E) :
    (∑ e ∈ F, ketbra (e : H) (e : H)) * (∑ e ∈ F, ketbra (e : H) (e : H))
      = ∑ e ∈ F, ketbra (e : H) (e : H) := by
  classical
  have h := ketbra_sum_sandwich F (1 : H →L[ℂ] H)
  rw [mul_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun e he => ?_
  have hite : ∀ e' : E, (⟪(e : H), (1 : H →L[ℂ] H) (e' : H)⟫ : ℂ) • ketbra (e : H) (e' : H)
      = if e' = e then ketbra (e : H) (e : H) else 0 := by
    intro e'
    rw [IsOneApplyEqSelf.one_apply_eq_self, orthonormal_iff_ite.mp hE e e']
    by_cases hee : e' = e
    · subst hee; simp
    · simp [Ne.symm hee, hee]
  simp only [hite]
  exact Finset.sum_ite_eq' F e (fun _ => ketbra (e : H) (e : H)) ▸ by simp [he]

/-- Kadison's inequality (**30IV**.1, `omega_norm_basic_1`) for a normal
positive functional on B(H), stated with real parts.  (Auxiliary for
**39VII**.) -/
private theorem npf_kadison (ω : NPFunctional (H →L[ℂ] H)) (a b : H →L[ℂ] H) :
    ‖ω (star a * b)‖ ^ 2 ≤ (ω (star a * a)).re * (ω (star b * b)).re := by
  have hpos : IsPositiveMap (ω.toPositiveLinearMap.toLinearMap) :=
    fun t ht => ω.toPositiveLinearMap.map_nonneg ht
  have hcoe : ∀ t : H →L[ℂ] H, ω.toPositiveLinearMap.toLinearMap t = ω t := fun _ => rfl
  have h := omega_norm_basic_1 _ hpos a b
  simp only [hcoe] at h
  have hA : (0 : ℂ) ≤ ω (star a * a) := ω.toPositiveLinearMap.map_nonneg (star_mul_self_nonneg a)
  have hB : (0 : ℂ) ≤ ω (star b * b) := ω.toPositiveLinearMap.map_nonneg (star_mul_self_nonneg b)
  have hAim : (ω (star a * a)).im = 0 := by simpa using (Complex.le_def.mp hA).2.symm
  have hBim : (ω (star b * b)).im = 0 := by simpa using (Complex.le_def.mp hB).2.symm
  have hre := (Complex.le_def.mp h).1
  rwa [Complex.mul_re, hAim, hBim, mul_zero, sub_zero, ← Complex.ofReal_pow,
    Complex.ofReal_re] at hre

/-- **39VI** (`sum-ketbras`, cstar.tex:6622, Exercise), part 3: consequently
`ω 1 = ∑_{e ∈ E} ω (|e⟩⟨e|)` for every np-map `ω : B(H) → ℂ`. -/
theorem sum_ketbras_3 (E : Set H) (hE : IsOrthonormalBasis E)
    (ω : NPFunctional (H →L[ℂ] H)) :
    HasSum (fun e : E => ω (ketbra (e : H) (e : H))) (ω 1) := by
  classical
  have hmapsum : ∀ F : Finset E,
      ω (∑ e ∈ F, ketbra (e : H) (e : H)) = ∑ e ∈ F, ω (ketbra (e : H) (e : H)) :=
    fun F => map_sum ω.toPositiveLinearMap _ F
  have hωnn : ∀ T : H →L[ℂ] H, 0 ≤ T → 0 ≤ ω T :=
    fun _ hT => ω.toPositiveLinearMap.map_nonneg hT
  have hone : IsSelfAdjoint (1 : H →L[ℂ] H) := star_one _
  have hketnn : ∀ e : E, (0 : H →L[ℂ] H) ≤ ketbra (e : H) (e : H) := by
    intro e
    simpa using ketbra_sum_mono (F := (∅ : Finset E)) (G := {e}) (by simp)
  -- the directed set of finite partial sums, in the self-adjoint part of B(H)
  set f : Finset E → selfAdjoint (H →L[ℂ] H) := fun F =>
    ⟨∑ e ∈ F, ketbra (e : H) (e : H), ketbra_sum_isSelfAdjoint F⟩ with hf
  have hne : (Set.range f).Nonempty := ⟨f ∅, Set.mem_range_self _⟩
  have hdir : DirectedOn (· ≤ ·) (Set.range f) := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨f (F ∪ G), Set.mem_range_self _,
      Subtype.coe_le_coe.mp (ketbra_sum_mono Finset.subset_union_left),
      Subtype.coe_le_coe.mp (ketbra_sum_mono Finset.subset_union_right)⟩
  have hlub : IsLUB (Set.range f) (⟨1, hone⟩ : selfAdjoint (H →L[ℂ] H)) := by
    constructor
    · rintro _ ⟨F, rfl⟩
      exact Subtype.coe_le_coe.mp ((sum_ketbras_2 E hE).1 ⟨F, rfl⟩)
    · intro t ht
      refine Subtype.coe_le_coe.mp ((sum_ketbras_2 E hE).2 ?_)
      rintro S ⟨F, rfl⟩
      exact Subtype.coe_le_coe.mpr (ht (Set.mem_range_self F))
  have hnormal := ω.preservesDirSups' (Set.range f) ⟨1, hone⟩ hne hdir hlub
  -- the summands are nonnegative reals
  have hre : ∀ e : E, ((((ω (ketbra (e : H) (e : H))).re : ℝ)) : ℂ)
      = ω (ketbra (e : H) (e : H)) := by
    intro e
    have h := Complex.le_def.mp (hωnn _ (hketnn e))
    exact Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr h.2.symm)
  have hnn : ∀ e : E, 0 ≤ (ω (ketbra (e : H) (e : H))).re :=
    fun e => (Complex.le_def.mp (hωnn _ (hketnn e))).1
  have hre1 : ((((ω (1 : H →L[ℂ] H)).re : ℝ)) : ℂ) = ω 1 := by
    have h := Complex.le_def.mp (hωnn 1 zero_le_one)
    exact Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr h.2.symm)
  -- the partial sums of the real parts have `(ω 1).re` as least upper bound
  have hsumre : ∀ F : Finset E,
      ((∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re : ℝ) : ℂ)
        = ω (∑ e ∈ F, ketbra (e : H) (e : H)) := by
    intro F
    rw [hmapsum F]
    push_cast
    exact Finset.sum_congr rfl fun e _ => hre e
  have hlubR : IsLUB (Set.range fun F : Finset E => ∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re)
      ((ω (1 : H →L[ℂ] H)).re) := by
    constructor
    · rintro _ ⟨F, rfl⟩
      rw [← Complex.real_le_real, hsumre F, hre1]
      exact hnormal.1 ⟨f F, Set.mem_range_self F, rfl⟩
    · intro c hc
      rw [← Complex.real_le_real, hre1]
      refine hnormal.2 ?_
      rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      change ω (∑ e ∈ F, ketbra (e : H) (e : H)) ≤ (c : ℂ)
      rw [← hsumre F, Complex.real_le_real]
      exact hc (Set.mem_range_self F)
  have hR := hasSum_of_isLUB_of_nonneg _ hnn hlubR
  have h2 : HasSum (fun e : E => (((ω (ketbra (e : H) (e : H))).re : ℝ) : ℂ))
      ((((ω (1 : H →L[ℂ] H)).re : ℝ)) : ℂ) := Complex.hasSum_ofReal.mpr hR
  simpa only [hre, hre1] using h2

/-- **39VII** (`bh-np-lemma`, cstar.tex:6643, Lemma), verbatim: for a Hilbert
space `H` with orthonormal basis `E`, a normal positive functional
`ω : B(H) → ℂ`, and `A ∈ B(H)`,

`ω A = lim_{F ⊆ E finite} ∑_{e, e' ∈ F} ⟪e, A e'⟫ ω (|e⟩⟨e'|)`,

which is the statement below.

⚠ The limit over the square partial sums may **not** be replaced by the bare
double sum `∑_{e, e' ∈ E}`, which is false: under the thesis's own convention
for `∑_{i ∈ I}` (6II) it is the *unordered* sum over `E × E`, and already for
a vector functional `ω = ⟪x, (·) x⟫` on `ℓ²` the family
`(⟪e, A e'⟫ ω(|e⟩⟨e'|))_{e,e'}` need not be absolutely — hence, in `ℂ`, not unconditionally — summable: take
`A` block diagonal with `N×N` discrete-Fourier blocks (unitary, all entries of
modulus `N^{-1/2}`) of sizes `N_k = k⁸` and `x` constant `c_k` on the `k`-th
block with `N_k c_k² = k⁻²`, so that `∑ ‖x‖² < ∞` while
`∑ |A_{ee'}| |x_e| |x_{e'}| = ∑_k N_k^{3/2} c_k² = ∑_k k² = ∞`.  The trap is
that the squares `F × F` are *cofinal* among the finite subsets of `E × E`,
and convergence along a cofinal subfamily is not convergence of the net.

That is erratum `parsec-390.70`, incorporated in cstar.tex: the source prints
the limit over the square partial sums, which is what the Lemma's own proof
establishes and the form **39IX** consumes. -/
theorem bh_np_lemma (E : Set H) (hE : IsOrthonormalBasis E)
    (ω : NPFunctional (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    Tendsto (fun F : Finset E =>
        ∑ e ∈ F, ∑ e' ∈ F, ⟪(e : H), A (e' : H)⟫ * ω (ketbra (e : H) (e' : H)))
      atTop (𝓝 (ω A)) := by
  classical
  -- linearity and positivity of `ω`, phrased for its `NPFunctional` coercion
  have hω_add : ∀ S T : H →L[ℂ] H, ω (S + T) = ω S + ω T :=
    fun S T => map_add ω.toPositiveLinearMap S T
  have hω_sub : ∀ S T : H →L[ℂ] H, ω (S - T) = ω S - ω T :=
    fun S T => map_sub ω.toPositiveLinearMap S T
  have hω_sum : ∀ (F : Finset E) (f : E → H →L[ℂ] H), ω (∑ i ∈ F, f i) = ∑ i ∈ F, ω (f i) :=
    fun F f => map_sum ω.toPositiveLinearMap f F
  have hω_smul : ∀ (c : ℂ) (T : H →L[ℂ] H), ω (c • T) = c * ω T := fun c T => by
    rw [← smul_eq_mul]; exact map_smul ω.toPositiveLinearMap c T
  have hnn : ∀ T : H →L[ℂ] H, 0 ≤ T → (0 : ℂ) ≤ ω T :=
    fun _ hT => ω.toPositiveLinearMap.map_nonneg hT
  have hω1 : (0 : ℝ) ≤ (ω 1).re := (Complex.le_def.mp (hnn 1 zero_le_one)).1
  set P : Finset E → (H →L[ℂ] H) := fun F => ∑ e ∈ F, ketbra (e : H) (e : H) with hPdef
  have hPapp : ∀ F : Finset E, P F = ∑ e ∈ F, ketbra (e : H) (e : H) := fun _ => rfl
  set Q : Finset E → (H →L[ℂ] H) := fun F => 1 - P F with hQdef
  have hQapp : ∀ F : Finset E, Q F = 1 - P F := fun _ => rfl
  -- `ω (P A P)` is the square partial sum
  have hdouble : ∀ F : Finset E, ω (P F * A * P F)
      = ∑ e ∈ F, ∑ e' ∈ F, ⟪(e : H), A (e' : H)⟫ * ω (ketbra (e : H) (e' : H)) := by
    intro F
    rw [hPapp F, ketbra_sum_sandwich F A, hω_sum]
    exact Finset.sum_congr rfl fun e _ => by
      rw [hω_sum]; exact Finset.sum_congr rfl fun e' _ => hω_smul _ _
  -- `P F` is a self-adjoint idempotent of norm at most one, hence so is `Q F`
  have hPsa : ∀ F : Finset E, star (P F) = P F := fun F => ketbra_sum_isSelfAdjoint F
  have hPP : ∀ F : Finset E, P F * P F = P F := fun F => by
    rw [hPapp F]; exact ketbra_sum_idem hE.1 F
  have hPnorm : ∀ F : Finset E, ‖P F‖ ≤ 1 := fun F => ketbra_sum_norm_le_one hE.1 F
  have hQsa : ∀ F : Finset E, star (Q F) = Q F := fun F => by
    rw [hQapp F, star_sub, star_one, hPsa F]
  have hQQ : ∀ F : Finset E, star (Q F) * Q F = Q F := fun F => by
    rw [hQsa F, hQapp F]
    have h : (1 - P F) * (1 - P F) = 1 - P F - P F + P F * P F := by noncomm_ring
    rw [h, hPP F]
    abel
  -- `ω a ≤ ‖a‖ ω 1` for self-adjoint `a`
  have hbound : ∀ a : H →L[ℂ] H, IsSelfAdjoint a → (ω a).re ≤ ‖a‖ * (ω 1).re := by
    intro a ha
    have h1 : a ≤ algebraMap ℝ (H →L[ℂ] H) ‖a‖ := ha.le_algebraMap_norm_self
    have h2 : (0 : ℂ) ≤ ω (algebraMap ℝ (H →L[ℂ] H) ‖a‖ - a) := hnn _ (sub_nonneg.mpr h1)
    have h3 : ω (algebraMap ℝ (H →L[ℂ] H) ‖a‖) = ((‖a‖ : ℝ) : ℂ) * ω 1 := by
      rw [algebraMap_real_eq, Algebra.algebraMap_eq_smul_one, hω_smul]
    rw [hω_sub, h3] at h2
    have h4 := (Complex.le_def.mp h2).1
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re] at h4
    linarith
  -- the two ingredients of the thesis's Kadison estimate
  have hAA : ((ω (star A * A)).re) ≤ ‖A‖ ^ 2 * (ω 1).re := by
    have h := hbound _ (IsSelfAdjoint.star_mul_self A)
    rw [CStarRing.norm_star_mul_self] at h
    calc (ω (star A * A)).re ≤ ‖A‖ * ‖A‖ * (ω 1).re := h
      _ = ‖A‖ ^ 2 * (ω 1).re := by ring
  have hPAAP : ∀ F : Finset E,
      (ω (star (star A * P F) * (star A * P F))).re ≤ ‖A‖ ^ 2 * (ω 1).re := by
    intro F
    have h := hbound _ (IsSelfAdjoint.star_mul_self (star A * P F))
    rw [CStarRing.norm_star_mul_self] at h
    have hn : ‖star A * P F‖ ≤ ‖A‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [norm_star]
      calc ‖A‖ * ‖P F‖ ≤ ‖A‖ * 1 := by gcongr; exact hPnorm F
        _ = ‖A‖ := mul_one _
    have hsq : ‖star A * P F‖ * ‖star A * P F‖ ≤ ‖A‖ ^ 2 :=
      (mul_le_mul hn hn (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq (sq ‖A‖).symm)
    exact le_trans h (mul_le_mul_of_nonneg_right hsq hω1)
  -- the tail `ω (Q F)` tends to `0`, by **39VI**.3
  have hQre : ∀ F : Finset E,
      (ω (Q F)).re = (ω 1).re - ∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re := by
    intro F
    rw [hQapp F, hω_sub, hPapp F, hω_sum, Complex.sub_re, Complex.re_sum]
  have hQnn : ∀ F : Finset E, 0 ≤ (ω (Q F)).re := by
    intro F
    refine (Complex.le_def.mp (hnn _ ?_)).1
    rw [hQapp F, sub_nonneg, hPapp F]
    exact ketbra_sum_le_one hE.1 F
  have hQtend : Tendsto (fun F : Finset E => (ω (Q F)).re) atTop (𝓝 0) := by
    have h2 : Tendsto (fun F : Finset E => ∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re) atTop
        (𝓝 ((ω 1).re)) := (sum_ketbras_3 E hE ω).map Complex.reCLM Complex.reCLM.continuous
    have h3 : Tendsto (fun F : Finset E =>
        (ω 1).re - ∑ e ∈ F, (ω (ketbra (e : H) (e : H))).re) atTop (𝓝 ((ω 1).re - (ω 1).re)) :=
      tendsto_const_nhds.sub h2
    rw [sub_self] at h3
    exact h3.congr fun F => (hQre F).symm
  -- assemble the estimate `|ω A − ω (P A P)| ≤ 2 √(‖A‖² ω 1) √(ω (Q F))`
  have hsplit : ∀ F : Finset E,
      A - P F * A * P F = star (Q F) * A + star (star A * P F) * Q F := by
    intro F
    rw [hQsa F, hQapp F]
    have hst : star (star A * P F) = P F * A := by rw [star_mul, star_star, hPsa F]
    rw [hst]
    noncomm_ring
  have hsqrt : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ t → t ^ 2 ≤ u * v →
      t ≤ Real.sqrt u * Real.sqrt v := by
    intro u v t hu ht h
    rw [← Real.sqrt_mul hu]
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht).symm
      _ ≤ Real.sqrt (u * v) := Real.sqrt_le_sqrt h
  have hkey : ∀ F : Finset E,
      ‖(∑ e ∈ F, ∑ e' ∈ F, ⟪(e : H), A (e' : H)⟫ * ω (ketbra (e : H) (e' : H))) - ω A‖
        ≤ 2 * (Real.sqrt (‖A‖ ^ 2 * (ω 1).re) * Real.sqrt ((ω (Q F)).re)) := by
    intro F
    rw [← hdouble F]
    have hdiff : ω (P F * A * P F) - ω A
        = -(ω (star (Q F) * A) + ω (star (star A * P F) * Q F)) := by
      rw [← hω_add, ← hsplit F, hω_sub]
      ring
    rw [hdiff, norm_neg]
    -- `|ω (Q* A)| ≤ √(ω Q) √(‖A‖² ω 1)`
    have e1 : ‖ω (star (Q F) * A)‖
        ≤ Real.sqrt ((ω (Q F)).re) * Real.sqrt (‖A‖ ^ 2 * (ω 1).re) := by
      refine hsqrt _ _ _ (hQnn F) (norm_nonneg _) ?_
      have hk := npf_kadison ω (Q F) A
      rw [hQQ F] at hk
      exact hk.trans (mul_le_mul_of_nonneg_left hAA (hQnn F))
    -- `|ω ((A* P)* Q)| ≤ √(‖A‖² ω 1) √(ω Q)`
    have e2 : ‖ω (star (star A * P F) * Q F)‖
        ≤ Real.sqrt (‖A‖ ^ 2 * (ω 1).re) * Real.sqrt ((ω (Q F)).re) := by
      refine hsqrt _ _ _ (by positivity) (norm_nonneg _) ?_
      have hk := npf_kadison ω (star A * P F) (Q F)
      rw [hQQ F] at hk
      exact hk.trans (mul_le_mul_of_nonneg_right (hPAAP F) (hQnn F))
    calc ‖ω (star (Q F) * A) + ω (star (star A * P F) * Q F)‖
        ≤ ‖ω (star (Q F) * A)‖ + ‖ω (star (star A * P F) * Q F)‖ := norm_add_le _ _
      _ ≤ Real.sqrt ((ω (Q F)).re) * Real.sqrt (‖A‖ ^ 2 * (ω 1).re)
            + Real.sqrt (‖A‖ ^ 2 * (ω 1).re) * Real.sqrt ((ω (Q F)).re) := add_le_add e1 e2
      _ = 2 * (Real.sqrt (‖A‖ ^ 2 * (ω 1).re) * Real.sqrt ((ω (Q F)).re)) := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun F => norm_nonneg _) hkey ?_
  have hs0 : Tendsto (fun F : Finset E => Real.sqrt ((ω (Q F)).re)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hQtend
  rw [Real.sqrt_zero] at hs0
  have hs1 := (hs0.const_mul (Real.sqrt (‖A‖ ^ 2 * (ω 1).re))).const_mul (2 : ℝ)
  rw [mul_zero, mul_zero] at hs1
  exact hs1

/-- The action of `|x⟩⟨y|`.  (Auxiliary for **39IX**.) -/
private theorem ketbra_apply' (a b u : H) : ketbra a b u = ⟪b, u⟫ • a := rfl

/-- `|x⟩⟨y|* = |y⟩⟨x|` (**4XIX**.2).  (Auxiliary for **39IX**.) -/
private theorem ketbra_star (x y : H) : star (ketbra x y) = ketbra y x := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff (ketbra y x) (ketbra x y)).mpr ?_).symm
  intro u v
  simp only [ketbra_apply', inner_smul_left, inner_smul_right]
  rw [← inner_conj_symm u x]
  ring

/-- `|x⟩⟨z|` is additive in `x`.  (Auxiliary for **39IX**.) -/
private theorem ketbra_add_left (x y z : H) : ketbra (x + y) z = ketbra x z + ketbra y z := by
  ext w; simp only [ketbra_apply', ContinuousLinearMap.add_apply, smul_add]

/-- `|x⟩⟨z|` is homogeneous in `x`.  (Auxiliary for **39IX**.) -/
private theorem ketbra_smul_left (c : ℂ) (x z : H) : ketbra (c • x) z = c • ketbra x z := by
  ext w
  simp only [ketbra_apply', ContinuousLinearMap.smul_apply]
  exact smul_comm _ _ _

/-- `|x⟩⟨x| ≥ 0`.  (Auxiliary for **39IX**.) -/
private theorem ketbra_self_nonneg (x : H) : (0 : H →L[ℂ] H) ≤ ketbra x x := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have h : (⟪(ketbra x x) z, z⟫ : ℂ) = ((Complex.normSq ⟪x, z⟫ : ℝ) : ℂ) := by
    simp only [ketbra_apply', inner_smul_left]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [h]
  exact ⟨by simp, by simp [Complex.normSq_nonneg]⟩

/-- **39IX**, first step: for a positive functional `ω` on `B(H)` there is a
positive `ϱ ∈ B(H)` with `ω |y⟩⟨x| = ⟪x, ϱ y⟫`.

This is the thesis's own route (cstar.tex:6666).  The map
`(x, y) ↦ ω |y⟩⟨x|` is a bounded form in the sense of **36IV** on the Hilbert
ℂ-module `H`, which is self-dual by **36II** (`selfDual_hilbert`), so **36V**
(`chilb_form_representation`) represents it.  36V delivers a `T` with
`ω |y⟩⟨x| = ⟪T x, y⟫` *together with its adjoint* `S`, and it is `ϱ := S` that
the thesis's display `⟪x, ϱ y⟫` names; `S` is bounded by **35VI**, exactly as
inside the proof of 36V.  (For `𝒜 = ℂ` the self-duality step *is* the Riesz
representation theorem, which is what 36II says; going through 36V rather than
through Mathlib's `InnerProductSpace.toDual` directly is what keeps 36V — and
with it 35VI — on the path the thesis lays out.)  Positivity of `ϱ` is the
thesis's own argument (`hilb-positive-operators`): `⟪x, ϱ x⟫ = ω |x⟩⟨x| ≥ 0`. -/
private theorem exists_rho (ω : NPFunctional (H →L[ℂ] H)) :
    ∃ ϱ : H →L[ℂ] H, 0 ≤ ϱ ∧ ∀ x y : H, ω (ketbra y x) = ⟪x, ϱ y⟫ := by
  obtain ⟨C, hC⟩ := ω.toPositiveLinearMap.exists_norm_apply_le
  have hstar : ∀ T : H →L[ℂ] H, ω (star T) = star (ω T) :=
    cstar_p_implies_i ω.toPositiveLinearMap.toLinearMap
      (fun a ha => ω.toPositiveLinearMap.map_nonneg ha)
  -- `z ↦ ω |z⟩⟨y|` is a bounded module map `H → ℂ`, for every `y`
  have hlin : ∀ y : H, ∃ r : H →ₗ[ℂ] ℂ, IsBoundedModuleMap ℂ r ∧
      ∀ x : H, r x = ω (ketbra x y) := by
    intro y
    have hb : ∀ x : H, ‖ω (ketbra x y)‖ ≤ ((C : ℝ) * ‖y‖) * ‖x‖ := by
      intro x
      refine le_trans (hC _) ?_
      rw [ketbra_norm]
      nlinarith [norm_nonneg x, norm_nonneg y, C.2]
    let f : H →ₗ[ℂ] ℂ :=
      { toFun := fun x => ω (ketbra x y)
        map_add' := fun a b => by
          rw [ketbra_add_left]; exact map_add ω.toPositiveLinearMap _ _
        map_smul' := fun c a => by
          rw [ketbra_smul_left]; exact map_smul ω.toPositiveLinearMap _ _ }
    exact ⟨f, ⟨fun c x => map_smul f c x, (f.mkContinuous _ hb).continuous⟩, fun _ => rfl⟩
  -- hence `(x, y) ↦ ω |y⟩⟨x|` is a bounded form (**36IV**)
  have hBform : IsBoundedForm ℂ (fun x y : H => ω (ketbra y x)) :=
    { bddModuleMap_right := fun x => hlin x
      bddModuleMap_left_star := fun y => by
        obtain ⟨r, hr, hrB⟩ := hlin y
        refine ⟨r, hr, fun x => ?_⟩
        rw [hrB, ← ketbra_star y x, hstar] }
  -- **36V**, at `𝒜 = ℂ`, with self-duality of `H` supplied by **36II**
  obtain ⟨T, ⟨-, ⟨S, hadj⟩, hTB⟩, -⟩ :=
    chilb_form_representation (𝒜 := ℂ) (selfDual_hilbert H) (selfDual_hilbert H) hBform
  -- `S` — the thesis's `ϱ` — is bounded by **35VI**
  obtain ⟨-, -, -, -, -, hScont⟩ :=
    hellinger_toeplitz (𝒜 := ℂ) (Or.inl (inferInstance : CompleteSpace H)) (⇑T) (⇑S) hadj
  refine ⟨⟨S, hScont⟩, ?_, ?_⟩
  · -- positivity, by **25V** (`hilb-positive-operators`)
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro z
    have hval : (0 : ℂ) ≤ ω (ketbra z z) :=
      ω.toPositiveLinearMap.map_nonneg (ketbra_self_nonneg z)
    have him : (ω (ketbra z z)).im = 0 := by simpa using (Complex.le_def.mp hval).2.symm
    have hdiag : (⟪z, S z⟫ : ℂ) = ω (ketbra z z) := ((hTB z z).trans (hadj z z)).symm
    have h : (⟪(⟨S, hScont⟩ : H →L[ℂ] H) z, z⟫ : ℂ) = ω (ketbra z z) := by
      rw [show ((⟨S, hScont⟩ : H →L[ℂ] H) z) = S z from rfl, ← inner_conj_symm (S z) z, hdiag]
      exact Complex.conj_eq_iff_im.mpr him
    rw [h]
    exact ⟨(Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr him)),
      (Complex.le_def.mp hval).1⟩
  · intro x y
    exact (hTB x y).trans (hadj x y)

/-- **39IX** (`bh-np`, cstar.tex:6690, Theorem): every normal positive
functional `ω : B(H) → ℂ` on a Hilbert space `H` is of the form
`ω = ∑ₙ ⟪xₙ, (·) xₙ⟫` for some sequence `x₁, x₂, … ∈ H` with
`∑ₙ ‖xₙ‖² = ‖ω‖` (for a positive functional `‖ω‖ = ω 1`, which is how the
norm condition is stated here). -/
theorem bh_np (ω : NPFunctional (H →L[ℂ] H)) :
    ∃ x : ℕ → H,
      (∀ T : H →L[ℂ] H, HasSum (fun n => ⟪x n, T (x n)⟫) (ω T)) ∧
      HasSum (fun n => ((‖x n‖ ^ 2 : ℝ) : ℂ)) (ω 1) := by
  classical
  obtain ⟨ϱ, hϱnn, hϱ⟩ := exists_rho ω
  -- an orthonormal basis of `H` (**39III**)
  obtain ⟨E, hEon, hEmax⟩ : ∃ E : Set H, Orthonormal ℂ ((↑) : E → H) ∧
      ∀ E' : Set H, E ⊆ E' → Orthonormal ℂ ((↑) : E' → H) → E' = E := by
    obtain ⟨w, -, hw, hmax⟩ := exists_maximal_orthonormal (𝕜 := ℂ) (E := H)
      (s := (∅ : Set H)) (by simp)
    exact ⟨w, hw, fun E' h h' => hmax E' h h'⟩
  have hE : IsOrthonormalBasis E := ⟨hEon, hEmax⟩
  have hω1real : ((((ω 1).re : ℝ)) : ℂ) = ω 1 := by
    have h : (0 : ℂ) ≤ ω 1 := ω.toPositiveLinearMap.map_nonneg zero_le_one
    exact Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr (by
      simpa using (Complex.le_def.mp h).2.symm))
  -- `R = √ϱ`, and the family `y e = √ϱ e` indexed by the basis
  set R : H →L[ℂ] H := CFC.sqrt ϱ with hRdef
  have hRsa : IsSelfAdjoint R := .of_nonneg (CFC.sqrt_nonneg ϱ)
  have hRR : R * R = ϱ := CFC.sqrt_mul_sqrt_self ϱ hϱnn
  have hRsym : ∀ u v : H, (⟪R u, v⟫ : ℂ) = ⟪u, R v⟫ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hRsa
  have hRRapp : ∀ u : H, R (R u) = ϱ u := fun u => by
    have := congrArg (fun T : H →L[ℂ] H => T u) hRR
    simpa using this
  set y : E → H := fun e => R (e : H) with hydef
  -- Parseval: `∑_{e ∈ E} ⟪a, e⟫ ⟪e, b⟫ = ⟪a, b⟫` (**39IV**.3)
  have hparseval : ∀ a b : H,
      HasSum (fun e : E => (⟪(e : H), b⟫ : ℂ) * ⟪a, (e : H)⟫) ⟪a, b⟫ := by
    intro a b
    have h := (orthonormal_3 E hE b).mapL (innerSL ℂ a)
    simpa [inner_smul_right] using h
  -- the thesis's computation `ω |u⟩⟨v| = ⟪√ϱ v, √ϱ u⟫ = ∑_e ⟪y e, |u⟩⟨v| (y e)⟫`
  have hkey : ∀ u v : H,
      HasSum (fun e : E => (⟪y e, ketbra u v (y e)⟫ : ℂ)) (ω (ketbra u v)) := by
    intro u v
    have hval : (ω (ketbra u v) : ℂ) = ⟪R v, R u⟫ := by
      rw [hϱ v u, ← hRRapp u, hRsym]
    rw [hval]
    refine (hparseval (R v) (R u)).congr_fun fun e => ?_
    rw [ketbra_apply', inner_smul_right, hydef]
    simp only
    rw [← hRsym (e : H) u, hRsym v (e : H)]
    ring
  -- `∑_{e ∈ E} ‖y e‖² = ω 1`, by **39VI**.3
  have hnormval : ∀ e : E, (((‖y e‖ ^ 2 : ℝ) : ℂ)) = ω (ketbra (e : H) (e : H)) := by
    intro e
    have h := hϱ (e : H) (e : H)
    rw [h, ← hRRapp (e : H), ← hRsym, hydef]
    simp only
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hnormE : HasSum (fun e : E => (((‖y e‖ ^ 2 : ℝ) : ℂ))) (ω 1) :=
    (sum_ketbras_3 E hE ω).congr_fun fun e => hnormval e
  -- pass from the basis `E` to a sequence, by countability of the support
  have hsummableE : Summable fun e : E => ‖y e‖ ^ 2 :=
    (Complex.hasSum_ofReal.mp (by rw [hω1real]; exact hnormE)).summable
  have hsupp : (Function.support y).Countable := by
    have h : (Function.support fun e : E => ‖y e‖ ^ 2).Countable :=
      hsummableE.countable_support
    refine h.mono ?_
    intro e he
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, norm_eq_zero] at he ⊢
    simp [he]
  obtain ⟨j, hj⟩ := Set.countable_iff_exists_injective.mp hsupp
  set x : ℕ → H := Function.extend j (fun e : Function.support y => y (e : E)) 0 with hxdef
  have hxout : ∀ n : ℕ, n ∉ Set.range j → x n = 0 := by
    intro n hn
    rw [hxdef, Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hn)]
    rfl
  have hxj : ∀ e : Function.support y, x (j e) = y (e : E) := fun e =>
    hj.extend_apply _ _ e
  have htrans : ∀ (g : H → ℂ), g 0 = 0 → ∀ c : ℂ,
      HasSum (fun e : E => g (y e)) c → HasSum (fun n : ℕ => g (x n)) c := by
    intro g hg0 c hc
    have hsub : Function.support (fun e : E => g (y e)) ⊆ Function.support y := by
      intro e he
      simp only [Function.mem_support] at he ⊢
      intro h
      exact he (by rw [h, hg0])
    have h1 : HasSum ((fun e : E => g (y e)) ∘ (Subtype.val : Function.support y → E)) c :=
      (hasSum_subtype_iff_of_support_subset hsub).mpr hc
    refine (hj.hasSum_iff (f := fun n : ℕ => g (x n)) ?_).mp ?_
    · intro n hn
      rw [hxout n hn]; exact hg0
    · refine h1.congr_fun fun e => ?_
      simp only [Function.comp_apply]
      rw [hxj e]
  -- the sequence and the functional it induces (**38IV**.2)
  have hnormN : HasSum (fun n : ℕ => (((‖x n‖ ^ 2 : ℝ) : ℂ))) (ω 1) :=
    htrans (fun v => (((‖v‖ ^ 2 : ℝ) : ℂ))) (by simp) _ hnormE
  have hsummableN : Summable fun n : ℕ => ‖x n‖ ^ 2 :=
    (Complex.hasSum_ofReal.mp (by rw [hω1real]; exact hnormN)).summable
  obtain ⟨ω', hω'⟩ := bh_functional_lemma_2 x hsummableN
  have hω'sum : ∀ T : H →L[ℂ] H, HasSum (fun n => ⟪x n, T (x n)⟫) (ω' T) := by
    intro T
    rw [hω' T]
    exact (bh_functional_lemma_1 x hsummableN T).hasSum
  -- `ω'` and `ω` agree on the rank-one operators …
  have hketeq : ∀ u v : H, ω' (ketbra u v) = ω (ketbra u v) := by
    intro u v
    exact (hω'sum (ketbra u v)).unique
      (htrans (fun w => ⟪w, ketbra u v w⟫) (by simp) _ (hkey u v))
  -- … hence everywhere, by **39VII**
  have heq : ∀ A : H →L[ℂ] H, ω' A = ω A := by
    intro A
    refine tendsto_nhds_unique (f := fun F : Finset E =>
      ∑ e ∈ F, ∑ e' ∈ F, ⟪(e : H), A (e' : H)⟫ * ω' (ketbra (e : H) (e' : H)))
      (bh_np_lemma E hE ω' A) ?_
    refine (bh_np_lemma E hE ω A).congr fun F => ?_
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => by rw [hketeq]
  refine ⟨x, fun T => ?_, hnormN⟩
  rw [← heq T]
  exact hω'sum T

end BH

/-! **40I** (cstar.tex:6748): closing remarks of the chapter — nothing to
formalize. -/

end Theses.A.CStar
