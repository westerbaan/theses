/-
# vn.tex parsec 490: `𝓑^a(X)` for a self-dual Hilbert 𝒜-module

**49II** (`bah-vn`, vn.tex:1176, Theorem): for a von Neumann algebra `𝒜` and a
*self-dual* (**36I**) Hilbert `𝒜`-module `X`, the C*-algebra `𝓑^a(X)`
(**32XIII** `bax_cstar`) of bounded adjointable module maps on `X` is a von
Neumann algebra, and `⟨x, (·) x⟩ : 𝓑^a(X) → 𝒜` is normal for every `x ∈ X`.

## What is here, and what is not

The thesis's statement quantifies over the *type* `𝓑^a(X)`.  That type exists
in the tree — `Bax 𝒜 X` at `Theses/A/CStar/Matrices.lean:849`, carrying the
whole `CStarAlgebra` structure together with its spectral order — but it is
`private` to that file, so no statement outside `A/CStar/Matrices` can name
it.  Until it is exported, `VonNeumannAlgebra (Bax 𝒜 X)` cannot be *written*
here.

What can be written, and is written below, is the entire mathematical content
of 49II with the type replaced by its intrinsic description.  By **32XV**
(`chilb_vector_states_2`, `Theses/A/CStar/Matrices.lean`) the order of
`𝓑^a(X)` is the vector-functional order

    T ≼ S   ⟺   ⟨x, T x⟩ ≤ ⟨x, S x⟩ for all x ∈ X,

which is `VecLE` below, and self-adjointness of `T` in `𝓑^a(X)` is
`ModuleAdjointTo 𝒜 T T`.  In those terms 49II says exactly two things, and
both are proved here with no `sorry`:

* **suprema** — `bah_vn_sup`: a nonempty, `≼`-directed, `≼`-bounded set of
  self-adjoint adjointable operators has a least upper bound `S` for `≼`, and
  `⟨x, S x⟩ = ⋁_{T ∈ 𝒟} ⟨x, T x⟩` for every `x` — which is the *normality* of
  `⟨x, (·) x⟩` that 49II's second clause asserts;
* **enough np-functionals** — `bah_vn_np_faithful`: if `ξ(⟨x, T x⟩) = 0` for
  every np-functional `ξ` on `𝒜` and every `x`, then `T = 0`.

Together these are the two clauses of **42I** (`vna`) for `𝓑^a(X)`.  Once
`Bax` is exported, `VonNeumannAlgebra (Bax 𝒜 X)` follows from the two by
transporting `≼` along 32XV; that step is the only thing missing, and it is
blocked on a file this pass may not edit.

## The proof is the thesis's

`exists_isLUB_vecForm` follows vn.tex:1189–1240 step for step:

1. for each `x`, `{⟨x, T x⟩ : T ∈ 𝒟}` is a bounded directed set of
   self-adjoint elements of `𝒜`, so it has a supremum (**42I**), and the net
   converges ultraweakly to it (**44VI** `vna_supremum_uwlimit`);
2. polarisation (`inner_apply_polarization`, the module-form shape of
   **44II**) turns those four limits into a limit of `⟨y, T z⟩`, giving a form
   `[y, z]`;
3. the form is bounded — the thesis reads its bound off **32X**
   `chilb_form_bounded`; ours reads it off the order instead, from
   `T₀ ≼ ⋁𝒟 ≼ S₀`, which avoids needing the unit ball to be *ultraweakly*
   closed (the thesis has that only at **73VIII**, later than this point);
4. `X` is self-dual, so **36V** `chilb_form_representation` represents the
   form as `[y, z] = ⟨y, S z⟩`;
5. `S` is the supremum, because the vector functionals are order separating
   (**32XV**), and `⟨x, S x⟩ = ⋁_T ⟨x, T x⟩` by construction.

`bah_vn_np_faithful` is vn.tex:1241–1250: `ξ ∘ ⟨x, (·) x⟩` is an
np-functional, so `⟨x, T x⟩ = 0` for every `x` by faithfulness in `𝒜`, and
then `T = 0` by polarisation.

## Why a separate module

Parsec 490 otherwise lives in `A/VN/Basic`, whose variable context is a single
von Neumann algebra; this section needs a Hilbert `𝒜`-module `X` with
`[NormedSpace ℂ X]` and `[CompleteSpace X]` alongside it.  The import is
`A/VN/Completeness` rather than `A/VN/Basic` only to reuse `uwTendsto_unique`,
`UWTendsto.add` and `UWTendsto.smul`, which live there; the *mathematical*
dependencies of everything below are **42I**, **42III**, **44II**, **44VI**,
**44XI** and cstar's **32X**, **32XV**, **36I**, **36V** — nothing later than
the point itself.  49IV (`M_N(𝒜)` is a von Neumann algebra) does not use this
file: it is proved directly in `A/VN/Basic`, deliberately routing around 49II.
-/
import Theses.A.VN.Completeness

namespace Theses.A.VN

open Theses Theses.A.CStar Filter Topology
open scoped ComplexOrder

section UWAux

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Ultraweak convergence commutes with the involution: `ω(a*) = ω(a)*` for an
np-functional (**42II**, `npFunctional_star`).  The additive and scalar
companions of this are `UWTendsto.add` and `UWTendsto.smul` in
`A/VN/Completeness`; this one has no counterpart there. -/
theorem uwTendsto_star {ι : Type*} {l : Filter ι} {f : ι → A} {a : A}
    (h : UWTendsto f l a) : UWTendsto (fun i => star (f i)) l (star a) := by
  rw [uwTendsto_iff] at h ⊢
  intro ω
  simp only [npFunctional_star]
  exact (continuous_star.tendsto _).comp (h ω)

end UWAux

section BaX

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul 𝒜 X]
  [CStarModule 𝒜 X]

variable (𝒜) in
/-- The vector-functional order on the operators of `X`: `T ≼ S` when
`⟨x, T x⟩ ≤ ⟨x, S x⟩` for every `x ∈ X`.  By **32XV**
(`chilb_vector_states_2`) this is the order of `𝓑^a(X)` restricted to the
adjointable operators, which is how 49II's "bounded directed subset of
`Re 𝓑^a(X)`" and "supremum in `Re 𝓑^a(X)`" are rendered below. -/
def VecLE (T S : X →L[ℂ] X) : Prop := ∀ x : X, inner 𝒜 x (T x) ≤ inner 𝒜 x (S x)

omit [StarOrderedRing 𝒜] in
/-- The vector functional of a self-adjoint adjointable operator is a
self-adjoint element of `𝒜`: `⟨x, T x⟩* = ⟨T x, x⟩ = ⟨x, T x⟩`. -/
theorem isSelfAdjoint_vecForm {T : X →L[ℂ] X} (hT : ModuleAdjointTo 𝒜 ⇑T ⇑T) (x : X) :
    IsSelfAdjoint (inner 𝒜 x (T x)) := by
  show star (inner 𝒜 x (T x)) = inner 𝒜 x (T x)
  rw [CStarModule.star_inner]
  exact hT x x

omit [StarOrderedRing 𝒜] in
/-- Polarisation (**44II** for the `𝒜`-valued form of a module map): the
sesquilinear form `(y, z) ↦ ⟨y, T z⟩` of a ℂ-linear `T` is recovered from its
quadratic part,
`⟨z, T y⟩ = ¼ ∑_{k<4} iᵏ ⟨y + iᵏ z, T (y + iᵏ z)⟩`.
No adjointability or self-adjointness is needed.  This is the module analogue
of `matForm_polarization` (`A/VN/Basic`), and vn.tex:1206 is where 49II's
proof uses it. -/
theorem inner_apply_polarization (T : X →L[ℂ] X) (y z : X) :
    inner 𝒜 z (T y) = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4, Complex.I ^ k •
      inner 𝒜 (y + (Complex.I ^ k : ℂ) • z) (T (y + (Complex.I ^ k : ℂ) • z)) := by
  have hexp : ∀ c : ℂ, inner 𝒜 (y + c • z) (T (y + c • z))
      = inner 𝒜 y (T y) + c • inner 𝒜 y (T z)
        + (starRingEnd ℂ) c • inner 𝒜 z (T y)
        + ((starRingEnd ℂ) c * c) • inner 𝒜 z (T z) := by
    intro c
    simp only [map_add, map_smul, CStarModule.inner_add_left,
      CStarModule.inner_add_right, CStarModule.inner_smul_left_complex,
      CStarModule.inner_smul_right_complex, starRingEnd_apply]
    module
  simp only [hexp, Finset.sum_range_succ, Finset.sum_range_zero, smul_add,
    smul_smul, zero_add]
  match_scalars <;>
    norm_num [pow_succ, Complex.I_mul_I, map_pow, Complex.conj_I]

section Main

variable [VonNeumannAlgebra 𝒜]

/-- **49II** (`bah-vn`, vn.tex:1176, Theorem), the substance of the first
clause: for a self-dual Hilbert `𝒜`-module `X` over a von Neumann algebra
`𝒜`, a nonempty set `𝒟` of self-adjoint adjointable operators that is
directed and bounded above in the vector-functional order has an adjointable
self-adjoint `S` with `⟨x, S x⟩ = ⋁_{T ∈ 𝒟} ⟨x, T x⟩` for every `x ∈ X`.

The supremum clause *is* the normality of `⟨x, (·) x⟩` asserted by 49II's
second half, and `bah_vn_sup` reads off it that `S` is the least upper bound
of `𝒟` for `≼`.  The proof is vn.tex:1189–1240; the module header says where
it deviates (the bound on the form comes from the order rather than from
ultraweak closedness of the ball). -/
theorem exists_isLUB_vecForm [CompleteSpace X] (hX : SelfDual 𝒜 X)
    {𝒟 : Set (X →L[ℂ] X)} {S₀ : X →L[ℂ] X}
    (hne : 𝒟.Nonempty)
    (hsa : ∀ T ∈ 𝒟, ModuleAdjointTo 𝒜 ⇑T ⇑T)
    (hdir : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, ∃ R ∈ 𝒟, VecLE 𝒜 T R ∧ VecLE 𝒜 S R)
    (hub : ∀ T ∈ 𝒟, VecLE 𝒜 T S₀) :
    ∃ S : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑S ⇑S ∧
      (∀ x : X, IsLUB {a : 𝒜 | ∃ T ∈ 𝒟, a = inner 𝒜 x (T x)} (inner 𝒜 x (S x))) := by
  classical
  obtain ⟨T₀, hT₀⟩ := hne
  let _ : Preorder 𝒟 :=
    { le := fun T S => VecLE 𝒜 T.1 S.1
      le_refl := fun _ _ => le_refl _
      le_trans := fun _ _ _ h h' x => (h x).trans (h' x) }
  have : Nonempty 𝒟 := ⟨⟨T₀, hT₀⟩⟩
  have : IsDirected 𝒟 (· ≤ ·) := ⟨fun T S => by
    obtain ⟨R, hR, h1, h2⟩ := hdir T.1 T.2 S.1 S.2
    exact ⟨⟨R, hR⟩, h1, h2⟩⟩
  -- the vector functionals of `𝒟`, as self-adjoint elements
  set F : X → 𝒟 → selfAdjoint 𝒜 := fun x T =>
    ⟨inner 𝒜 x (T.1 x), isSelfAdjoint_vecForm (hsa T.1 T.2) x⟩ with hF
  have hFmono : ∀ (x : X) {T S : 𝒟}, T ≤ S → F x T ≤ F x S :=
    fun x _ _ h => Subtype.coe_le_coe.mp (h x)
  have hS₀sa : ∀ x : X, IsSelfAdjoint (inner 𝒜 x (S₀ x)) := by
    intro x
    have h1 : (F x ⟨T₀, hT₀⟩ : 𝒜) ≤ inner 𝒜 x (S₀ x) := hub T₀ hT₀ x
    have h3 := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h1)
    have h4 := (F x ⟨T₀, hT₀⟩).2
    simpa using h3.add h4
  have hUB : ∀ x : X, (⟨inner 𝒜 x (S₀ x), hS₀sa x⟩ : selfAdjoint 𝒜)
      ∈ upperBounds (Set.range (F x)) := by
    rintro x _ ⟨T, rfl⟩
    exact Subtype.coe_le_coe.mp (hub T.1 T.2 x)
  have hQgood : ∀ x : X, (Set.range (F x)).Nonempty ∧
      DirectedOn (· ≤ ·) (Set.range (F x)) ∧ BddAbove (Set.range (F x)) := by
    intro x
    refine ⟨⟨F x ⟨T₀, hT₀⟩, ⟨T₀, hT₀⟩, rfl⟩, ?_, ⟨_, hUB x⟩⟩
    rintro _ ⟨T, rfl⟩ _ ⟨S, rfl⟩
    obtain ⟨R, hR, h1, h2⟩ := hdir T.1 T.2 S.1 S.2
    exact ⟨F x ⟨R, hR⟩, ⟨⟨R, hR⟩, rfl⟩,
      Subtype.coe_le_coe.mp (h1 x), Subtype.coe_le_coe.mp (h2 x)⟩
  set q : X → selfAdjoint 𝒜 := fun x => dirSup (Set.range (F x)) (hQgood x) with hq
  have hlub : ∀ x : X, IsLUB (Set.range (F x)) (q x) :=
    fun x => isLUB_dirSup _ (hQgood x)
  -- **44VI**: the net of vector functionals converges ultraweakly to its supremum
  have hconv : ∀ w : X, UWTendsto (fun T : 𝒟 => inner 𝒜 w (T.1 w)) atTop ((q w : 𝒜)) := by
    intro w
    have hg : Tendsto (fun T : 𝒟 => (⟨F w T, ⟨T, rfl⟩⟩ : Set.range (F w))) atTop atTop := by
      rw [tendsto_atTop]
      rintro ⟨-, T', rfl⟩
      filter_upwards [eventually_ge_atTop T'] with T hT
      exact Subtype.coe_le_coe.mpr (hFmono w hT)
    exact (vna_supremum_uwlimit (Set.range (F w)) (hQgood w)).comp hg
  -- the form `[y,z]`, obtained from the suprema by polarisation
  set B : X → X → 𝒜 := fun y z => (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4,
      Complex.I ^ k • ((q (z + (Complex.I ^ k : ℂ) • y) : selfAdjoint 𝒜) : 𝒜) with hBdef
  have hBconv : ∀ y z : X, UWTendsto (fun T : 𝒟 => inner 𝒜 y (T.1 z)) atTop (B y z) := by
    intro y z
    have hrw : ∀ T : 𝒟, inner 𝒜 y (T.1 z) = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4,
        Complex.I ^ k • inner 𝒜 (z + (Complex.I ^ k : ℂ) • y)
          (T.1 (z + (Complex.I ^ k : ℂ) • y)) :=
      fun T => inner_apply_polarization T.1 z y
    simp only [hrw, hBdef]
    exact UWTendsto.smul _ (uwTendsto_finsetSum fun k _ => UWTendsto.smul _ (hconv _))
  have hBself : ∀ x : X, B x x = ((q x : selfAdjoint 𝒜) : 𝒜) := fun x =>
    uwTendsto_unique (hBconv x x) (hconv x)
  have hBstar : ∀ y z : X, star (B y z) = B z y := by
    intro y z
    have h2 : UWTendsto (fun T : 𝒟 => inner 𝒜 z (T.1 y)) atTop (star (B y z)) := by
      refine Filter.Tendsto.congr (fun T => ?_) (uwTendsto_star (hBconv y z))
      rw [CStarModule.star_inner]
      exact hsa T.1 T.2 z y
    exact uwTendsto_unique h2 (hBconv z y)
  have hBadd : ∀ y z z' : X, B y (z + z') = B y z + B y z' := by
    intro y z z'
    refine uwTendsto_unique (hBconv y (z + z')) (Filter.Tendsto.congr (fun T => ?_)
      (UWTendsto.add (hBconv y z) (hBconv y z')))
    rw [map_add, CStarModule.inner_add_right]
  have hBsmul : ∀ (y : X) (c : ℂ) (z : X), B y (c • z) = c • B y z := by
    intro y c z
    refine uwTendsto_unique (hBconv y (c • z)) (Filter.Tendsto.congr (fun T => ?_)
      (UWTendsto.smul c (hBconv y z)))
    rw [map_smul, CStarModule.inner_smul_right_complex]
  have hBmodule : ∀ (y : X) (a : 𝒜) (z : X), B y (a • z) = a * B y z := by
    intro y a z
    have h := uwTendsto_mul_left_right a 1 (hBconv y z)
    rw [mul_one] at h
    refine uwTendsto_unique (hBconv y (a • z)) (Filter.Tendsto.congr (fun T => ?_) h)
    rw [mul_one, (moduleAdjointable_linear _ ⟨_, hsa T.1 T.2⟩).2.2 a z,
      CStarModule.inner_op_smul_right]
  -- a uniform bound: `T₀ ≼ ⋁𝒟 ≼ S₀` bounds the suprema in norm
  set M : ℝ := ‖S₀‖ + 2 * ‖T₀‖ with hM
  have hinner_norm : ∀ (T : X →L[ℂ] X) (w : X), ‖inner 𝒜 w (T w)‖ ≤ ‖T‖ * ‖w‖ ^ 2 := by
    intro T w
    calc ‖inner 𝒜 w (T w)‖ ≤ ‖w‖ * ‖T w‖ := CStarModule.norm_inner_le X
      _ ≤ ‖w‖ * (‖T‖ * ‖w‖) := by gcongr; exact T.le_opNorm w
      _ = ‖T‖ * ‖w‖ ^ 2 := by ring
  have hqnorm : ∀ w : X, ‖((q w : selfAdjoint 𝒜) : 𝒜)‖ ≤ M * ‖w‖ ^ 2 := by
    intro w
    have hab : inner 𝒜 w (T₀ w) ≤ ((q w : selfAdjoint 𝒜) : 𝒜) :=
      Subtype.coe_le_coe.mpr ((hlub w).1 ⟨⟨T₀, hT₀⟩, rfl⟩)
    have hbc : ((q w : selfAdjoint 𝒜) : 𝒜) ≤ inner 𝒜 w (S₀ w) :=
      Subtype.coe_le_coe.mpr ((hlub w).2 (hUB w))
    have h2 := CStarAlgebra.norm_le_norm_of_nonneg_of_le (sub_nonneg.mpr hab)
      (sub_le_sub_right hbc (inner 𝒜 w (T₀ w)))
    have h3 : ‖((q w : selfAdjoint 𝒜) : 𝒜)‖
        ≤ ‖((q w : selfAdjoint 𝒜) : 𝒜) - inner 𝒜 w (T₀ w)‖ + ‖inner 𝒜 w (T₀ w)‖ := by
      simpa using norm_add_le (((q w : selfAdjoint 𝒜) : 𝒜) - inner 𝒜 w (T₀ w))
        (inner 𝒜 w (T₀ w))
    calc ‖((q w : selfAdjoint 𝒜) : 𝒜)‖
        ≤ ‖((q w : selfAdjoint 𝒜) : 𝒜) - inner 𝒜 w (T₀ w)‖ + ‖inner 𝒜 w (T₀ w)‖ := h3
      _ ≤ ‖inner 𝒜 w (S₀ w) - inner 𝒜 w (T₀ w)‖ + ‖inner 𝒜 w (T₀ w)‖ := by gcongr
      _ ≤ (‖inner 𝒜 w (S₀ w)‖ + ‖inner 𝒜 w (T₀ w)‖) + ‖inner 𝒜 w (T₀ w)‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ (‖S₀‖ * ‖w‖ ^ 2 + ‖T₀‖ * ‖w‖ ^ 2) + ‖T₀‖ * ‖w‖ ^ 2 := by
          gcongr <;> exact hinner_norm _ _
      _ = M * ‖w‖ ^ 2 := by rw [hM]; ring
  have hBnorm : ∀ y z : X, ‖B y z‖ ≤ M * (‖y‖ + ‖z‖) ^ 2 := by
    intro y z
    have hIk : ∀ k : ℕ, ‖(Complex.I ^ k : ℂ)‖ = 1 := by
      intro k; rw [norm_pow, Complex.norm_I, one_pow]
    have hterm : ∀ k ∈ Finset.range 4,
        ‖Complex.I ^ k • ((q (z + (Complex.I ^ k : ℂ) • y) : selfAdjoint 𝒜) : 𝒜)‖
          ≤ M * (‖y‖ + ‖z‖) ^ 2 := by
      intro k _
      rw [norm_smul, hIk k, one_mul]
      refine (hqnorm _).trans ?_
      have hz : ‖z + (Complex.I ^ k : ℂ) • y‖ ≤ ‖y‖ + ‖z‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, hIk k, one_mul]
        linarith
      have hMnn : (0 : ℝ) ≤ M := by
        have := norm_nonneg S₀; have := norm_nonneg T₀; rw [hM]; linarith
      gcongr
    have h1 : ‖∑ k ∈ Finset.range 4,
        Complex.I ^ k • ((q (z + (Complex.I ^ k : ℂ) • y) : selfAdjoint 𝒜) : 𝒜)‖
        ≤ 4 * (M * (‖y‖ + ‖z‖) ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Finset.range 4,
              ‖Complex.I ^ k • ((q (z + (Complex.I ^ k : ℂ) • y) : selfAdjoint 𝒜) : 𝒜)‖
          ≤ ∑ _k ∈ Finset.range 4, M * (‖y‖ + ‖z‖) ^ 2 := Finset.sum_le_sum hterm
        _ = 4 * (M * (‖y‖ + ‖z‖) ^ 2) := by simp [Finset.sum_const]
    calc ‖B y z‖ = (4 : ℝ)⁻¹ * ‖∑ k ∈ Finset.range 4,
            Complex.I ^ k • ((q (z + (Complex.I ^ k : ℂ) • y) : selfAdjoint 𝒜) : 𝒜)‖ := by
          rw [hBdef, norm_smul]; norm_num
      _ ≤ (4 : ℝ)⁻¹ * (4 * (M * (‖y‖ + ‖z‖) ^ 2)) := by gcongr
      _ = M * (‖y‖ + ‖z‖) ^ 2 := by ring
  have hBzero : ∀ y : X, B y 0 = 0 := by
    intro y
    simpa using hBsmul y 0 0
  -- **36IV**: for each `y`, `[y,·]` is a bounded module map
  have hlin : ∀ y : X, ∃ r : X →ₗ[ℂ] 𝒜, IsBoundedModuleMap 𝒜 r ∧ ∀ z : X, r z = B y z := by
    intro y
    refine ⟨{ toFun := fun z => B y z
              map_add' := hBadd y
              map_smul' := fun c z => hBsmul y c z }, ⟨fun a z => ?_, ?_⟩, fun _ => rfl⟩
    · show B y (a • z) = a • B y z
      rw [hBmodule, smul_eq_mul]
    · refine AddMonoidHomClass.continuous_of_bound _ (M * (‖y‖ + 1) ^ 2) fun z => ?_
      show ‖B y z‖ ≤ M * (‖y‖ + 1) ^ 2 * ‖z‖
      rcases eq_or_ne z 0 with rfl | hz
      · simp [hBzero]
      · have hzp : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
        have hzc : ((‖z‖ : ℂ)) ≠ 0 := by simpa using ne_of_gt hzp
        have hzu : ((‖z‖ : ℂ)) • (((‖z‖ : ℂ))⁻¹ • z) = z := by
          rw [smul_smul, mul_inv_cancel₀ hzc, one_smul]
        have hun : ‖((‖z‖ : ℂ))⁻¹ • z‖ = 1 := by
          rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
          exact inv_mul_cancel₀ (ne_of_gt hzp)
        calc ‖B y z‖ = ‖((‖z‖ : ℂ)) • B y (((‖z‖ : ℂ))⁻¹ • z)‖ := by
              rw [← hBsmul, hzu]
          _ = ‖z‖ * ‖B y (((‖z‖ : ℂ))⁻¹ • z)‖ := by
              rw [norm_smul, Complex.norm_real, norm_norm]
          _ ≤ ‖z‖ * (M * (‖y‖ + 1) ^ 2) := by
              gcongr
              simpa [hun] using hBnorm y (((‖z‖ : ℂ))⁻¹ • z)
          _ = M * (‖y‖ + 1) ^ 2 * ‖z‖ := by ring
  -- **36V**: the bounded form is represented by an adjointable operator
  have hform : IsBoundedForm 𝒜 B := by
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨r, hr, hrB⟩ := hlin x
      exact ⟨r, hr, hrB⟩
    · obtain ⟨r, hr, hrB⟩ := hlin y
      exact ⟨r, hr, fun x => by rw [hrB]; exact (hBstar x y).symm⟩
  obtain ⟨Slin, ⟨hSbm, -, hSrep⟩, -⟩ := chilb_form_representation hX hX hform
  have hswap : ∀ u v : X, inner 𝒜 u (Slin v) = star (inner 𝒜 (Slin v) u) := by
    intro u v
    rw [CStarModule.star_inner]
  refine ⟨({ toLinearMap := Slin, cont := hSbm.2 } : X →L[ℂ] X), fun x y => ?_,
    fun x => ?_⟩
  · show inner 𝒜 (Slin x) y = inner 𝒜 x (Slin y)
    rw [← hSrep x y, hswap x y, ← hSrep y x, hBstar]
  · have hxx : inner 𝒜 x (Slin x) = ((q x : selfAdjoint 𝒜) : 𝒜) := by
      rw [hswap x x, ← hSrep x x, hBself]
      exact (q x).2.star_eq
    have hcoe := isLUB_coe_of_isLUB (hQgood x).1 (hlub x)
    have hset : Subtype.val '' Set.range (F x)
        = {a : 𝒜 | ∃ T ∈ 𝒟, a = inner 𝒜 x (T x)} := by
      ext a
      constructor
      · rintro ⟨_, ⟨T, rfl⟩, rfl⟩
        exact ⟨T.1, T.2, rfl⟩
      · rintro ⟨T, hT, rfl⟩
        exact ⟨F x ⟨T, hT⟩, ⟨⟨T, hT⟩, rfl⟩, rfl⟩
    rw [hset] at hcoe
    show IsLUB {a : 𝒜 | ∃ T ∈ 𝒟, a = inner 𝒜 x (T x)} (inner 𝒜 x (Slin x))
    rw [hxx]
    exact hcoe

/-- **49II** (`bah-vn`, vn.tex:1176, Theorem), first clause, in the shape 42I
asks for: a nonempty `≼`-directed `≼`-bounded set of self-adjoint adjointable
operators on a self-dual `X` has a *least upper bound* for `≼`, and each
`⟨x, (·) x⟩` carries it to the supremum of the images.  With `Bax` exported
this is `VonNeumannAlgebra.isLUB_of_bddAbove_directed` for `𝓑^a(X)`, by
**32XV**. -/
theorem bah_vn_sup [CompleteSpace X] (hX : SelfDual 𝒜 X)
    {𝒟 : Set (X →L[ℂ] X)} {S₀ : X →L[ℂ] X}
    (hne : 𝒟.Nonempty)
    (hsa : ∀ T ∈ 𝒟, ModuleAdjointTo 𝒜 ⇑T ⇑T)
    (hdir : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, ∃ R ∈ 𝒟, VecLE 𝒜 T R ∧ VecLE 𝒜 S R)
    (hub : ∀ T ∈ 𝒟, VecLE 𝒜 T S₀) :
    ∃ S : X →L[ℂ] X, ModuleAdjointTo 𝒜 ⇑S ⇑S ∧
      (∀ T ∈ 𝒟, VecLE 𝒜 T S) ∧
      (∀ S' : X →L[ℂ] X, (∀ T ∈ 𝒟, VecLE 𝒜 T S') → VecLE 𝒜 S S') ∧
      (∀ x : X, IsLUB {a : 𝒜 | ∃ T ∈ 𝒟, a = inner 𝒜 x (T x)} (inner 𝒜 x (S x))) := by
  obtain ⟨S, hSsa, hSlub⟩ := exists_isLUB_vecForm hX hne hsa hdir hub
  refine ⟨S, hSsa, fun T hT x => ?_, fun S' hS' x => ?_, hSlub⟩
  · exact (hSlub x).1 ⟨T, hT, rfl⟩
  · exact (hSlub x).2 (by rintro _ ⟨T, hT, rfl⟩; exact hS' T hT x)

omit [VonNeumannAlgebra 𝒜] in
/-- The vector functionals separate the operators: if `⟨x, Tx⟩ = 0` for every
`x`, then `T = 0`.  (Polarisation, **32XV**.) -/
theorem eq_zero_of_vecForm_eq_zero {T : X →L[ℂ] X}
    (h : ∀ x : X, inner 𝒜 x (T x) = 0) : T = 0 := by
  ext y
  refine eq_of_inner_right_eq (𝒜 := 𝒜) fun z => ?_
  rw [inner_apply_polarization T y z]
  simp only [h, smul_zero, Finset.sum_const_zero]
  simp

/-- The second half of **49II**: `𝓑^a(X)` has enough np-functionals.  If
`ξ(⟨x, T x⟩) = 0` for every np-functional `ξ` on `𝒜` and every `x ∈ X`, and
`T` is positive in the vector-functional sense, then `T = 0`. -/
theorem bah_vn_np_faithful {T : X →L[ℂ] X}
    (hpos : ∀ x : X, 0 ≤ inner 𝒜 x (T x))
    (h : ∀ (ξ : NPFunctional 𝒜) (x : X), ξ (inner 𝒜 x (T x)) = 0) : T = 0 :=
  eq_zero_of_vecForm_eq_zero fun x =>
    VonNeumannAlgebra.np_faithful _ (hpos x) fun ξ => h ξ x

end Main

end BaX
