/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — a companion.

**This file has no thesis counterpart**: it formalizes the note
`wittrock-dil.tex` (repository root), not a thesis point, and carries no
DISP code and no audit row.  Thesis points it uses are cited by number, as
elsewhere in the tree.  The formalization of the note is spread over three
files: this one, `WittrockSplit.lean` (Lemma 3, and Definition 4 to
Corollary 13) and `WittrockBK.lean` (Proposition 8 and Corollary 14).
`WittrockSum.lean` adds a result that is not in the note: Wittrock dilations
are closed under direct sums of the domain (`isWittrockDilationOf_wsum`,
`exists_wittrockDilation_of_sum`).

# Wittrock dilations

A *Wittrock dilation* of an ncp-map `φ : 𝒳 → 𝒜` is a von Neumann algebra `ℰ`
with an ncp-map `h : 𝒳 ⊗ ℰ → 𝒜`, `h(x ⊗ 1) = φ(x)`, through which every
other such `h' : 𝒳 ⊗ ℰ' → 𝒜` factors as `h' = h ∘ (id ⊗ τ)` for a unique
ncp-map `τ : ℰ' → ℰ` with `(id ⊗ τ)(x ⊗ 1) = x ⊗ 1`.  The note's main
result (Theorem 10) is that `φ` has one iff `ϱ(𝒳)` splits off its commutant
in the algebra `𝒫` of a Paschke dilation `(𝒫, ϱ, h)` (**140II**).

## The note, item by item

* **Definition 1**: `IsWittrockDilationOf`, with the mediating clause
  `IsWittrockMediator` (the note's clause verbatim by
  `isWittrockMediator_iff_tmap`).  Here.
* **Remark 2** (mediators are unital): not stated on its own; it is
  `one_vtmul_injective` where used, the case `𝒳 = {0}` being dispatched
  separately.
* **Lemma 3** (the Wittrock correspondence): `wittrock_correspondence`
  (`WittrockSplit`), with `[0,φ]_ncp` the `ncpInterval` of **157II**.
* **Definition 4**: `SplitsOffCommutant` (`WittrockSplit`), with the
  commutant in `𝒫`, `relComm` (here), and `SubVN`, `CommVN`.
* **Remark 5**: not formalized (a comparison with the literature).
* **Lemma 6**: `exists_typeI_factor_iso`, `splitsOffCommutant_of_typeI_factor`
  (`WittrockSplit`), transported from `exists_bh_split` (here).
* **Proposition 7**: `splitsOffCommutant_iff_centre_corners`
  (`WittrockSplit`).  `⇒`: `centre_linf_of_splitsOffCommutant` (via
  `duplicable_centre_of_splitsOffCommutant`, **128XI**, **127III**) and
  `splitsOffCommutant_corner`; `⇐`: `splitsOffCommutant_of_centre_corners`;
  "in particular": `splitsOffCommutant_of_atomicTypeI`.
* **Proposition 8**: `splitsOffCommutant_bh_iff` (`WittrockBK`); `⇒` is
  `atomicTypeI_of_splitsOffCommutant_bh`, whose factor case is
  `exists_bh_of_factor_splits`.
* **Lemma 9**: `splitsOffCommutant_range_iff` (`WittrockSplit`).
* **Theorem 10**: `wittrock_iff_splitsOffCommutant` (`WittrockSplit`); `⇒` is
  `splitsOffCommutant_of_wittrock`; `⇐` with the last sentence is
  `isWittrockDilationOf_of_splitsOffCommutant`, whose universal-property
  half is `isWittrockDilationOf_paschke_of_mul` (here).  The form
  `σ(x ⊗ e) = ϱ(x) τ(e)` of the mediator of **140II**, which both
  directions use, is `exists_paschke_mediator` (here).
* **Corollary 11**: `isWittrockDilationOf_bh_paschke`, and with **154III**
  `exists_wittrockDilation_of_bh`; the ℂ case is
  `isWittrockDilationOf_stdFilter` (`stdFilter_wittrock` after
  `ℂ ⊗ ℰ ≅ ℰ`).  Here.
* **Corollary 12**: `exists_wittrockDilation_of_atomicTypeI`
  (`WittrockSplit`).
* **Corollary 13**: `centre_linf_of_wittrock`; the "in particular" is
  `not_wittrock_of_centre_no_minProj`
  (`not_wittrock_of_centre_no_minProj_paschke` for a given Paschke
  dilation), and its example `𝒳 = L^∞[0,1]` is `not_wittrock_of_linfty`
  (`not_wittrock_of_linfty_paschke`).  `WittrockSplit`.
* **Corollary 14**: `wittrock_iff_atomicTypeI_stinespring`
  (`exists_wittrock_of_atomicTypeI_stinespring` is its `⇐` alone) and the
  "in particular" `not_wittrock_of_factor_not_typeI`.  `WittrockBK`.

## Choices and deviations from the note

* **Universes.** `IsPaschkeDilationOf` quantifies over triples whose
  algebra lives in the universe of its own `𝒫`; likewise the universal
  property here quantifies over `ℰ'` in the universe of `ℰ`.  Theorem 10 and
  everything built on it therefore put `𝒳`, `𝒫`, `𝒜` and the sought `ℰ` in
  one universe.  Lemma 3 puts `𝒳`, `ℰ` and `𝒜` in one universe, as its
  proof tests against `𝒳 ⊗ ℂ²` with the tree's `tmap`.
* **`id ⊗ τ`.** The tree's `tmap` (**115II**) needs its four algebras in
  one universe, but in the ℂ case `𝒳 = ℂ : Type 0` while `ℰ` lives
  in the universe of `𝒜`.  So the definition asks for *some* ncp-map
  `σ : 𝒳 ⊗ ℰ' → 𝒳 ⊗ ℰ` with `σ(x ⊗ e) = x ⊗ τ(e)`.  Such a `σ` is unique
  (`ncp_ext_vnt`), and when all algebras share a universe it is
  `tmap (ncpId 𝒳) τ` (`isWittrockMediator_iff_tmap`), the note's clause
  verbatim.
* **"Type I factor", "direct sum of type I factors", "factor".** A type I
  factor is an algebra `≅ 𝓑(ℋ)`; a direct sum of type I factors is thesis
  A's `AtomicTypeI` (`≅ ⊕ⱼ 𝓑(𝒦ⱼ)` with `𝒦ⱼ ≠ 0`); a factor is `IsFactor`
  (centre `ℂ1`, **162II**).
* **Corollary 11, ℂ case.** The identification `ℂ ⊗ ℰ ≅ ℰ` is the left
  unitor `λ` of **119IVb**, so the dilating map is `c_p ∘ λ`; the proof is
  direct (**96V**, **98II**) rather than through **140X**, **169XI** and
  Theorem 10.
* **Lemma 3.** `ℂ²` is `ℓ^∞({0,1})`, and `𝒳 ⊗ ℂ² ≅ 𝒳 ⊕ 𝒳` is replaced by
  the two coordinate slices `𝒳 ⊗ ℂ² → 𝒳`.  For injectivity the test map is
  written as `h ∘ (id ⊗ κ)` for `κ(v) = v(0)e₁ + v(1)(1 − e₁)`, which is the
  note's test map for `ψ = h(· ⊗ e₁)`.  `φ` is a bare function; it is ncp
  anyway, being `h(· ⊗ 1)`.
* **Lemma 6.** The note shows with matrix units that `𝒫` is generated by
  `𝓑(ℋ) ⊗ 1` and `1 ⊗ 𝒩`, where `ℛ^□ = 1 ⊗ 𝒩`.  Here that step is
  `eq_concreteTensor_of_one_opTensor_mem`, proved from the amplification
  theorem of `A/Proc/Tensor.lean` instead, in the orientation `𝒦 ⊗ ℋ`; its
  `N` is the note's `𝒫` and its `E₀` the note's `𝒩`.
* **Theorem 10, `⇒`.** That `τ` maps projections to projections is shown
  directly (`τ(p) − τ(p)²` is `τ(g)` for an effect `g` below `p` and
  `1 − p`) rather than through extreme points of the effect sets; **99II**
  (`gardner`) then makes it multiplicative, as in the note.
* **Proposition 7, "in particular", and Corollary 12** are proved by the
  note's block argument run on the domain `⊕ⱼ 𝓑(𝒦ⱼ)`
  (`splitsOffCommutant_range_of_blocks`), which makes the passage through
  `ϱ(𝒳) ≅ c𝒳` unnecessary.  Proposition 7, `⇒`, second half, holds for every
  central projection, not only the minimal ones.
* **Corollary 13, "in particular".** "The centre of `𝒳` has no minimal
  projections" is `∀ c, ¬ IsMinCentralProj ⊤ c`: `𝒳` has no minimal
  central projection (a minimal central projection of `𝒳` being the same
  as a minimal projection of its centre).  The example `L^∞[0,1]` is taken
  as `L^∞(Ω)` for any measure space `Ω` without atoms: thesis A's
  presentation `IsLinftyOf` (`Duplicators.lean`), with "without atoms"
  `ContinuousSpace` (**129II**) and no σ-finiteness assumed.
* **Proposition 8, `⇒`**, cites two facts from Takesaki; both are proved,
  in `WittrockBK.lean`.  "A tensor product of factors is a factor" is
  `isFactor_vnt`, from the tree's commutation theorem and **121II**; "a
  tensor factor of a type I factor is of type I" is `exists_bh_of_vnt_bh`,
  with slice maps: if `𝒜 ⊗ ℬ ≅ 𝓑(𝒦)`, then `ℬ` has a minimal projection
  `q`, and `𝒜 ≅ 𝒜 ⊗ q` is a corner of `𝓑(𝒦)`.
-/
import Theses.A.Proc.CommutationAmplify
import Theses.B.Dils.Paschke

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN Theses.A.Proc

noncomputable section

namespace Theses.B.Dils

universe u v w

/-! ## The definition -/

section Definition

variable {X : Type u} {A : Type w}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The mediating clause of the note's universal property: `τ : ℰ' → ℰ`
makes the diagram commute.  `id_𝒳 ⊗ τ` is rendered as an ncp-map `σ` with
`σ(x ⊗ e) = x ⊗ τ(e)`; see the file header for why, and
`isWittrockMediator_iff_tmap` for the reading with **115II**'s `tmap`. -/
def IsWittrockMediator {E E' : Type v}
    [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    [CStarAlgebra E'] [PartialOrder E'] [StarOrderedRing E'] [VonNeumannAlgebra E']
    (h : NCPMap (VNT X E) A) (h' : NCPMap (VNT X E') A) (τ : NCPMap E' E) : Prop :=
  ∃ σ : NCPMap (VNT X E') (VNT X E),
    (∀ (x : X) (e : E'), σ (x ⊗ᵥ e) = x ⊗ᵥ τ e) ∧
    (∀ x : X, σ (x ⊗ᵥ (1 : E')) = x ⊗ᵥ (1 : E)) ∧
    ∀ z, h (σ z) = h' z

/-- A **Wittrock dilation** of `φ : 𝒳 → 𝒜` (`wittrock-dil.tex`,
Definition 1): a von Neumann algebra `ℰ` with an ncp-map `h : 𝒳 ⊗ ℰ → 𝒜`,
`h(x ⊗ 1) = φ(x)`, such that for every von Neumann algebra `ℰ'` (in the
universe of `ℰ`) and ncp-map `h' : 𝒳 ⊗ ℰ' → 𝒜` with `h'(x ⊗ 1) = φ(x)` there
is a unique ncp-map `τ : ℰ' → ℰ` with `(id ⊗ τ)(x ⊗ 1) = x ⊗ 1` and
`h ∘ (id ⊗ τ) = h'`. -/
def IsWittrockDilationOf (φ : X → A) (E : Type v)
    [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    (h : NCPMap (VNT X E) A) : Prop :=
  (∀ x : X, h (x ⊗ᵥ (1 : E)) = φ x) ∧
  ∀ (E' : Type v) [CStarAlgebra E'] [PartialOrder E'] [StarOrderedRing E']
    [VonNeumannAlgebra E'] (h' : NCPMap (VNT X E') A),
    (∀ x : X, h' (x ⊗ᵥ (1 : E')) = φ x) →
      ∃! τ : NCPMap E' E, IsWittrockMediator h h' τ

end Definition

section NCPLinear

variable {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem wncp_smul (f : NCPMap B C) (c : ℂ) (x : B) : f (c • x) = c • f x :=
  map_smul f.toCompletelyPositiveMap c x

theorem wncp_add (f : NCPMap B C) (x y : B) : f (x + y) = f x + f y :=
  map_add f.toCompletelyPositiveMap x y

theorem wncp_zero (f : NCPMap B C) : f (0 : B) = 0 :=
  map_zero f.toCompletelyPositiveMap

end NCPLinear

/-- ncp-maps out of `𝒳 ⊗ ℰ` agreeing on elementary tensors are equal: they
are ultraweakly continuous (**44XV**) and the elementary tensors span an
ultraweakly dense subspace (**108II**). -/
theorem ncp_ext_vnt {X : Type u} {E : Type v} {B : Type w}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [VonNeumannAlgebra B]
    (f g : NCPMap (VNT X E) B) (h : ∀ (x : X) (e : E), f (x ⊗ᵥ e) = g (x ⊗ᵥ e)) :
    f = g := by
  let _ : TopologicalSpace B := ultraweak B
  have : T2Space B := vn_positive_basic_1.1
  have hf : @Continuous (VNT X E) B (ultraweak _) (ultraweak B) ⇑f :=
    ((p_uwcont (ncpPositive f)).out 2 0).mp f.preservesDirSups'
  have hg : @Continuous (VNT X E) B (ultraweak _) (ultraweak B) ⇑g :=
    ((p_uwcont (ncpPositive g)).out 2 0).mp g.preservesDirSups'
  have hkey := tensor_linear_ext (vnTensor X E).isTensorProduct
    f.toCompletelyPositiveMap.toLinearMap g.toCompletelyPositiveMap.toLinearMap hf hg h
  exact DFunLike.coe_injective (congrArg (fun k : VNT X E →ₗ[ℂ] B => ⇑k) hkey)

/-- In one universe the mediating clause reads literally as in the note,
with `id ⊗ τ` the map `tmap (ncpId 𝒳) τ` of **115II**. -/
theorem isWittrockMediator_iff_tmap {X E E' A : Type u}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    [CStarAlgebra E'] [PartialOrder E'] [StarOrderedRing E'] [VonNeumannAlgebra E']
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (h : NCPMap (VNT X E) A) (h' : NCPMap (VNT X E') A) (τ : NCPMap E' E) :
    IsWittrockMediator h h' τ ↔
      (∀ x : X, tmap (ncpId X) τ (x ⊗ᵥ (1 : E')) = x ⊗ᵥ (1 : E)) ∧
        ∀ z, h (tmap (ncpId X) τ z) = h' z := by
  constructor
  · rintro ⟨σ, hσe, hσ1, hσh⟩
    have hσ : σ = tmap (ncpId X) τ :=
      (exists_tmap (ncpId X) τ).unique (fun x e => by rw [hσe, ncpId_apply])
        (tmap_apply (ncpId X) τ)
    subst hσ
    exact ⟨hσ1, hσh⟩
  · rintro ⟨h1, hh⟩
    exact ⟨tmap (ncpId X) τ, fun x e => by rw [tmap_apply, ncpId_apply], h1, hh⟩

/-! ## The scalar case: standard filters -/

section Scalar

variable {A : Type w} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A]

/-- The ℂ case of the note's Corollary 11 in the form it takes after
`ℂ ⊗ ℰ ≅ ℰ`: `c_p(1) = p`, and every ncp-map `h' : ℰ' → 𝒜` with
`h'(1) = p` is `c_p ∘ τ` for a unique ncp-map `τ` that is unital.  This is
**96V** (`c_p` is a filter) with **98II** (`c_p` is injective) — a direct
argument, where the note goes through **140X**, **169XI** and Theorem 10. -/
theorem stdFilter_wittrock (p : A) (hp : 0 ≤ p) :
    (stdFilter p 1 : A) = p ∧
      ∀ (E' : Type w) [CStarAlgebra E'] [PartialOrder E'] [StarOrderedRing E']
        [VonNeumannAlgebra E'] (h' : NCPMap E' A), h' 1 = p →
        ∃! τ : NCPMap E' (Corner A (ceil p)),
          τ 1 = 1 ∧ ∀ e, stdFilter p (τ e) = h' e := by
  refine ⟨stdFilter_one hp, fun E' _ _ _ _ h' h1 => ?_⟩
  obtain ⟨τ, hτ, hτu⟩ := (isFilter_stdFilter p hp).universal E' h'
    (by rw [h1, stdFilter_one hp])
  refine ⟨τ, ⟨stdFilter_injective hp (by rw [← hτ 1, h1, stdFilter_one hp]),
    fun e => (hτ e).symm⟩, fun τ' hτ' => hτu τ' fun e => (hτ'.2 e).symm⟩

/-- The left unitor `λ : ℂ ⊗ ℰ → ℰ` of **119IVb** is bijective. -/
theorem leftUnitor_bijective (E : Type w) [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] [VonNeumannAlgebra E] : Function.Bijective (leftUnitor E) :=
  (exists_unitors (A := E)).2.2.1.choose_spec.2.1

/-- The note's **Corollary 11**, last claim (the ℂ case): for positive `p`,
the standard filter
`c_p : ⌈p⌉𝒜⌈p⌉ → 𝒜` of **98I**, read on `ℂ ⊗ ⌈p⌉𝒜⌈p⌉` through the left
unitor of **119IVb**, is a Wittrock dilation of `λ ↦ λp`. -/
theorem isWittrockDilationOf_stdFilter (p : A) (hp : 0 ≤ p) :
    IsWittrockDilationOf (fun z : ℂ => z • p) (Corner A (ceil p))
      (ncpComp (stdFilter p) (nmiuNCP (leftUnitor (Corner A (ceil p))))) := by
  set E := Corner A (ceil p)
  have hbE := leftUnitor_bijective E
  refine ⟨fun z => ?_, fun E' _ _ _ _ h' hh' => ?_⟩
  · rw [ncpComp_apply, nmiuNCP_apply, leftUnitor_apply, wncp_smul, stdFilter_one hp]
  simp only at hh'
  have hbE' := leftUnitor_bijective E'
  have hinv : ∀ {F : Type w} [CStarAlgebra F] [PartialOrder F] [StarOrderedRing F]
      [VonNeumannAlgebra F] (hb : Function.Bijective (leftUnitor F)) (z : ℂ) (b : F),
      nmiuSymm (leftUnitor F) hb (z • b) = z ⊗ᵥ b := by
    intro F _ _ _ _ hb z b
    rw [← leftUnitor_apply z b, nmiuSymm_apply_apply]
  -- `g = h' ∘ λ⁻¹ : ℰ' → 𝒜` has `g(1) = p`; its factorisation `g = c_p ∘ τ`
  -- gives the mediator, with `id ⊗ τ = λ⁻¹ ∘ τ ∘ λ`
  set g : NCPMap E' A := ncpComp h' (nmiuNCP (nmiuSymm (leftUnitor E') hbE'))
  have hg : ∀ b, g b = h' ((1 : ℂ) ⊗ᵥ b) := fun b => by
    rw [ncpComp_apply, nmiuNCP_apply, ← hinv hbE' 1 b, one_smul]
  obtain ⟨τ, ⟨hτ1, hτ⟩, hτu⟩ := (stdFilter_wittrock p hp).2 E' g
    (by rw [hg, hh', one_smul])
  refine ⟨τ, ⟨ncpComp (nmiuNCP (nmiuSymm (leftUnitor E) hbE))
      (ncpComp τ (nmiuNCP (leftUnitor E'))), fun z e => ?_, fun z => ?_, fun w => ?_⟩,
    fun τ' ⟨σ', hσ'e, hσ'1, hσ'h⟩ => hτu τ' ⟨?_, fun b => ?_⟩⟩
  · rw [ncpComp_apply, ncpComp_apply, nmiuNCP_apply, nmiuNCP_apply, leftUnitor_apply,
      wncp_smul]
    exact hinv hbE z (τ e)
  · rw [ncpComp_apply, ncpComp_apply, nmiuNCP_apply, nmiuNCP_apply, leftUnitor_apply,
      wncp_smul, hτ1]
    exact hinv hbE z 1
  · rw [ncpComp_apply, ncpComp_apply, nmiuNCP_apply, nmiuNCP_apply, ncpComp_apply,
      nmiuNCP_apply, nmiuSymm_apply_apply', hτ, ncpComp_apply, nmiuNCP_apply,
      nmiuSymm_apply_apply]
  · have h1 := congrArg (leftUnitor E) ((hσ'e 1 1).symm.trans (hσ'1 1))
    rwa [leftUnitor_apply, leftUnitor_apply, one_smul, one_smul] at h1
  · rw [hg, ← hσ'h, hσ'e, ncpComp_apply, nmiuNCP_apply, leftUnitor_apply, one_smul]

end Scalar

/-! ## Tools

Positive decompositions, monotone nets, ncp-maps as cp and ultraweakly
continuous maps, `1 ⊗ (·)`, and direct sums `⊕ᵢ 𝒜ᵢ`: Mathlib's `lp 𝒜ᵢ ∞`,
with coprojections `κᵢ = lpKappa i` and projections `πᵢ = lpProjNMIU i`. -/

/-- Every element of a C*-algebra is a `ℂ`-combination of positive ones. -/
theorem wit_nonneg_induction {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (P : B → Prop) (hpos : ∀ a, 0 ≤ a → P a)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hsmul : ∀ (c : ℂ) a, P a → P (c • a))
    (b : B) : P b := by
  have hsa : ∀ y : B, IsSelfAdjoint y → P y := by
    intro y hy
    have h1 : 0 ≤ y + algebraMap ℝ B ‖y‖ := by
      have := hy.neg_algebraMap_norm_le_self
      rwa [neg_le_iff_add_nonneg] at this
    have h2 : (0 : B) ≤ algebraMap ℝ B ‖y‖ := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact smul_nonneg (norm_nonneg y) zero_le_one
    have := hadd _ _ (hpos _ h1) (hsmul (-1) _ (hpos _ h2))
    simpa using this
  rw [← realPart_add_I_smul_imaginaryPart b]
  exact hadd _ _ (hsa _ (realPart b).2) (hsmul _ _ (hsa _ (imaginaryPart b).2))

/-- A monotone net of self-adjoint elements that is bounded above converges
ultraweakly to its supremum (**44VI**, `vna_supremum_uwlimit`, reindexed). -/
theorem wit_uwTendsto_of_monotone {B : Type w} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (f : ι → B) (hmono : Monotone f)
    (hsa : ∀ i, IsSelfAdjoint (f i)) {c : B} (hc : ∀ i, f i ≤ c) :
    ∃ s : B, IsLUB (Set.range f) s ∧ UWTendsto f atTop s := by
  set D : Set (selfAdjoint B) := Set.range fun i => (⟨f i, hsa i⟩ : selfAdjoint B)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hcsa : IsSelfAdjoint c := by
    have h := (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr (hc i₀))).add (hsa i₀)
    simpa using h
  have hD : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := by
    refine ⟨⟨_, i₀, rfl⟩, ?_, ⟨⟨c, hcsa⟩, ?_⟩⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      exact ⟨_, ⟨k, rfl⟩, hmono hik, hmono hjk⟩
    · rintro _ ⟨i, rfl⟩
      exact hc i
  have hval := isLUB_val_of_isLUB hD.1 (isLUB_dirSup D hD)
  have hrange : Subtype.val '' D = Set.range f := by
    rw [← Set.range_comp]; rfl
  rw [hrange] at hval
  refine ⟨_, hval, ?_⟩
  have hlim := vna_supremum_uwlimit D hD
  have ht : Tendsto (fun i => (⟨⟨f i, hsa i⟩, i, rfl⟩ : D)) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun d => ?_
    obtain ⟨_, j, rfl⟩ := d
    exact ⟨j, fun i hi => hmono hi⟩
  exact hlim.comp ht

section LpMaps

variable {I : Type*} {𝒜 : I → Type u} [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
  [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]

/-- The coordinate projection `πᵢ : ⊕ⱼ 𝒜ⱼ → 𝒜ᵢ` as an nmiu-map (normal by
**47IV**.2). -/
def lpProjNMIU (i : I) : NMIUMap (lp 𝒜 ∞) (𝒜 i) where
  toStarAlgHom :=
    { toFun := fun a => (a : ∀ j, 𝒜 j) i
      map_one' := by rw [lp.infty_coeFn_one]; rfl
      map_mul' := fun a b => by rw [lp.infty_coeFn_mul]; rfl
      map_zero' := rfl
      map_add' := fun a b => rfl
      commutes' := fun r => by
        simp only [Algebra.algebraMap_eq_smul_one]
        rw [lp.coeFn_smul, lp.infty_coeFn_one]; rfl
      map_star' := fun a => by rw [lp.coeFn_star]; rfl }
  preservesDirSups' := vn_products_proj_normal 𝒜 i

@[simp] theorem lpProjNMIU_apply (i : I) (a : lp 𝒜 ∞) :
    lpProjNMIU i a = (a : ∀ j, 𝒜 j) i := rfl

/-- `κᵢ` as a linear map. -/
def lpKappaₗ (i : I) : 𝒜 i →ₗ[ℂ] lp 𝒜 ∞ where
  toFun := lpKappa i
  map_add' := lpKappa_add i
  map_smul' := lpKappa_smul i

omit [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
  [∀ i, VonNeumannAlgebra (𝒜 i)] in
theorem lpKappaₗ_cp (i : I) :
    Theses.A.CStar.IsCompletelyPositiveMap (lpKappaₗ (𝒜 := 𝒜) i) := by
  intro n a c
  have he : ∑ p, ∑ q, star (c p) * lpKappaₗ i (star (a p) * a q) * c q
      = star (∑ p, lpKappa i (a p) * c p) * ∑ q, lpKappa i (a q) * c q := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    change star (c p) * lpKappa i (star (a p) * a q) * c q
      = star (lpKappa i (a p) * c p) * (lpKappa i (a q) * c q)
    rw [← lpKappa_mul, ← lpKappa_star, star_mul]
    noncomm_ring
  rw [he]
  exact star_mul_self_nonneg _

omit [∀ i, VonNeumannAlgebra (𝒜 i)] in
/-- `κᵢ` is normal: suprema in `⊕ⱼ 𝒜ⱼ` are computed coordinatewise. -/
theorem lpKappa_normal (i : I) : PreservesDirSups (fun a : 𝒜 i => lpKappa i a) := by
  intro D s hne hdir hlub
  obtain ⟨d₀, hd₀⟩ := hne
  have hval := isLUB_val_of_isLUB ⟨d₀, hd₀⟩ hlub
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact lpKappa_le i (hval.1 ⟨d, hd, rfl⟩)
  · rw [lp_infty_le_iff]
    intro j
    by_cases hj : j = i
    · subst hj
      rw [lpKappa_apply_self]
      refine hval.2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have := (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) j
      rwa [lpKappa_apply_self] at this
    · rw [lpKappa_apply_ne _ _ hj]
      have := (lp_infty_le_iff _ _).mp (hu ⟨d₀, hd₀, rfl⟩) j
      rwa [lpKappa_apply_ne _ _ hj] at this

/-- The coprojection `κᵢ : 𝒜ᵢ → ⊕ⱼ 𝒜ⱼ` as an ncp-map. -/
def lpKappaNCP (i : I) : NCPMap (𝒜 i) (lp 𝒜 ∞) where
  toCompletelyPositiveMap :=
    { toLinearMap := lpKappaₗ i
      map_cstarMatrix_nonneg' := by
        have h : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) (𝒜 i)), 0 ≤ M →
            0 ≤ M.map ⇑(lpKappaₗ (𝒜 := 𝒜) i) :=
          (Theses.A.CStar.cp_iff _).out 0 1 |>.mp (lpKappaₗ_cp i)
        exact h }
  preservesDirSups' := lpKappa_normal i

omit [∀ i, VonNeumannAlgebra (𝒜 i)] in
@[simp] theorem lpKappaNCP_apply (i : I) (a : 𝒜 i) : lpKappaNCP i a = lpKappa i a := rfl

/-- The finite restrictions `∑_{i∈F} κᵢ(xᵢ)` of `x ∈ ⊕ᵢ 𝒜ᵢ` converge
ultraweakly to `x`. -/
theorem uwTendsto_lpRestrict (x : lp 𝒜 ∞) :
    UWTendsto (fun F : Finset I => ∑ i ∈ F, lpKappa i ((x : ∀ j, 𝒜 j) i)) atTop x := by
  classical
  let _ : TopologicalSpace (lp 𝒜 ∞) := ultraweak _
  have : IsTopologicalAddGroup (lp 𝒜 ∞) := ultraweak_isTopologicalAddGroup
  have : ContinuousSMul ℂ (lp 𝒜 ∞) := ultraweak_continuousSMul_complex
  refine wit_nonneg_induction (fun x : lp 𝒜 ∞ => UWTendsto
    (fun F : Finset I => ∑ i ∈ F, lpKappa i ((x : ∀ j, 𝒜 j) i)) atTop x)
    ?_ ?_ ?_ x
  · intro x hx
    have hxi : ∀ i, 0 ≤ (x : ∀ j, 𝒜 j) i := (lp_infty_nonneg_iff x).mp hx
    have hκ : ∀ i, 0 ≤ lpKappa i ((x : ∀ j, 𝒜 j) i) := fun i => by
      have := lpKappa_le i (hxi i)
      rwa [lpKappa_zero] at this
    have hnn : ∀ F : Finset I, 0 ≤ ∑ i ∈ F, lpKappa i ((x : ∀ j, 𝒜 j) i) :=
      fun F => Finset.sum_nonneg fun i _ => hκ i
    have hmono : Monotone fun F : Finset I => ∑ i ∈ F, lpKappa i ((x : ∀ j, 𝒜 j) i) := by
      intro F G hFG
      change ∑ i ∈ F, lpKappa i ((x : ∀ j, 𝒜 j) i) ≤ ∑ i ∈ G, lpKappa i ((x : ∀ j, 𝒜 j) i)
      rw [← Finset.sum_sdiff hFG]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => hκ i)
    have hle : ∀ F : Finset I, ∑ i ∈ F, lpKappa i ((x : ∀ j, 𝒜 j) i) ≤ x := by
      intro F
      rw [lp_infty_le_iff]
      intro k
      rw [lpKappa_sum_apply]
      split_ifs
      · exact le_rfl
      · exact hxi k
    obtain ⟨s, hs, hlim⟩ := wit_uwTendsto_of_monotone _ hmono
      (fun F => IsSelfAdjoint.of_nonneg (hnn F)) hle
    have hsx : s = x := by
      refine le_antisymm (hs.2 fun _ ⟨F, hF⟩ => hF ▸ hle F) ?_
      rw [lp_infty_le_iff]
      intro k
      have h := (lp_infty_le_iff _ _).mp (hs.1 ⟨{k}, rfl⟩) k
      rw [lpKappa_sum_apply] at h
      simpa using h
    rwa [hsx] at hlim
  · intro a b ha hb
    refine (ha.add hb).congr fun F => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lp.coeFn_add, Pi.add_apply, lpKappa_add]
  · intro c a ha
    refine (ha.const_smul c).congr fun F => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, lpKappa_smul]

end LpMaps

theorem wit_norm_le_of_le {z w : ℂ} (hz : 0 ≤ z) (hzw : z ≤ w) : ‖z‖ ≤ ‖w‖ := by
  have hw : 0 ≤ w := hz.trans hzw
  obtain ⟨hzr, hzi⟩ := Complex.nonneg_iff.mp hz
  obtain ⟨hwr, hwi⟩ := Complex.nonneg_iff.mp hw
  have hle := (Complex.le_def.mp hzw).1
  rw [← Complex.re_add_im z, ← Complex.re_add_im w, ← hzi, ← hwi]
  simp [abs_of_nonneg hzr, abs_of_nonneg hwr, hle]

theorem wit_ncp_cp {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] (f : NCPMap B C) :
    Theses.A.CStar.IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
  (Theses.A.CStar.cp_iff _).out 1 0 |>.mp fun N M hM =>
    f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM

theorem wit_ncp_continuous {B C : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] [VonNeumannAlgebra C] (f : NCPMap B C) :
    @Continuous B C (ultraweak B) (ultraweak C) ⇑f :=
  ((p_uwcont (ncpPositive f)).out 2 0).mp f.preservesDirSups'

/-- `1 ⊗ (·)` is injective when `𝒳` is non-zero (by **116III**.2). -/
theorem one_vtmul_injective {X E : Type u}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [VonNeumannAlgebra E]
    [Nontrivial X] : Function.Injective fun e : E => (1 : X) ⊗ᵥ e := by
  intro a b hab
  have h : (1 : X) ⊗ᵥ (a - b) = 0 := by
    change (vnTensor X E).map 1 (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hab
  have hn := norm_vtmul (1 : X) (a - b)
  rw [h, norm_zero, CStarRing.norm_one, one_mul] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)

/-! ## Commutants within `𝒫`, and Theorem 10, `⇐`

`relComm` is the commutant `ℛ^□` within `𝒫` of the note's Definition 4, and
`RangeComm ϱ` is `ϱ(𝒳)^□` for an nmiu-map `ϱ : 𝒳 → 𝒫`, bundled as a von
Neumann algebra.  For a Paschke dilation `(𝒫, ϱ, h)` of `φ`,
`isWittrockDilationOf_paschke_of_mul` is the first paragraph of the proof of
the note's Theorem 10, for any domain `𝒳`. -/

section Corestrict

variable {B C : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] [VonNeumannAlgebra C]

/-- An ncp-map whose range lies in a von Neumann subalgebra `S` corestricts
to an ncp-map into `Theses.A.Proc.VNSub C S`. -/
def ncpCorestrict (f : NCPMap B C) (S : StarSubalgebra ℂ C) (hS : IsVNSubalgebra C S)
    (hmem : ∀ b, f b ∈ S) : NCPMap B (Theses.A.Proc.VNSub C S hS) where
  toCompletelyPositiveMap :=
    { toLinearMap :=
        { toFun := fun b => ⟨f b, hmem b⟩
          map_add' := fun b b' => Theses.A.Proc.VNSub.val_injective (wncp_add f b b')
          map_smul' := fun c b => Theses.A.Proc.VNSub.val_injective (wncp_smul f c b) }
      map_cstarMatrix_nonneg' := by
        refine (Theses.A.CStar.cp_iff _).out 0 1 |>.mp ?_
        intro n a c
        have hcp := wit_ncp_cp f n a (fun i => (c i).val)
        change (0 : C) ≤ Theses.A.Proc.VNSub.valAddHom (∑ i, ∑ j, star (c i) *
          (⟨f (star (a i) * a j), hmem _⟩ : Theses.A.Proc.VNSub C S hS) * c j)
        simp only [map_sum]
        exact hcp }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hfn := f.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact hfn.1 ⟨d, hd, rfl⟩
    · intro u hu
      exact hfn.2 (by rintro _ ⟨d, hd, rfl⟩; exact hu ⟨d, hd, rfl⟩)

omit [VonNeumannAlgebra C] in
@[simp] theorem ncpCorestrict_val (f : NCPMap B C) (S : StarSubalgebra ℂ C)
    (hS : IsVNSubalgebra C S) (hmem : ∀ b, f b ∈ S) (b : B) :
    (ncpCorestrict f S hS hmem b).val = f b := rfl

end Corestrict

section PaschkeWittrock

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]
  {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P] [VonNeumannAlgebra P]

/-- The commutant `ℛ^□ = {e ∈ 𝒫 : a e = e a for all a ∈ ℛ}` of a
∗-subalgebra `ℛ` taken *within* `𝒫`, a von Neumann subalgebra of `𝒫`
(**65III**).  This is the `^□` of the note's Definition 4. -/
def relComm (R : StarSubalgebra ℂ P) : StarSubalgebra ℂ P :=
  (commutant_basic_3' (R : Set P) fun _ h => star_mem h).1.choose

theorem isVNSubalgebra_relComm (R : StarSubalgebra ℂ P) :
    IsVNSubalgebra P (relComm R) :=
  (commutant_basic_3' (R : Set P) fun _ h => star_mem h).1.choose_spec.1

theorem mem_relComm {R : StarSubalgebra ℂ P} {e : P} :
    e ∈ relComm R ↔ ∀ a ∈ R, a * e = e * a := by
  rw [← SetLike.mem_coe, relComm,
    (commutant_basic_3' (R : Set P) fun _ h => star_mem h).1.choose_spec.2]
  exact Iff.rfl

/-- The commutant `ϱ(𝒳)^□ = {e ∈ 𝒫 : e ϱ(x) = ϱ(x) e for all x}` of the
range of an nmiu-map `ϱ` within `𝒫`, a von Neumann subalgebra of `𝒫`
(**65III**): `relComm` of the range of `ϱ`. -/
abbrev rangeComm (ρ : NMIUMap X P) : StarSubalgebra ℂ P :=
  relComm ρ.toStarAlgHom.range

omit [VonNeumannAlgebra X] in
theorem isVNSubalgebra_rangeComm (ρ : NMIUMap X P) :
    IsVNSubalgebra P (rangeComm ρ) :=
  isVNSubalgebra_relComm _

omit [VonNeumannAlgebra X] in
theorem mem_rangeComm {ρ : NMIUMap X P} {e : P} :
    e ∈ rangeComm ρ ↔ ∀ x, ρ x * e = e * ρ x := by
  rw [rangeComm, mem_relComm]
  constructor
  · intro he x
    exact he (ρ x) ⟨x, rfl⟩
  · rintro he _ ⟨x, rfl⟩
    exact he x

/-- `ϱ(𝒳)^□`, the commutant of the range of `ϱ` within `𝒫`, bundled as a von
Neumann algebra: the `ℰ` of the note's Theorem 10. -/
abbrev RangeComm (ρ : NMIUMap X P) : Type u :=
  Theses.A.Proc.VNSub P (rangeComm ρ) (isVNSubalgebra_rangeComm ρ)

variable (X) in
/-- `x ↦ x ⊗ 1 : 𝒳 → 𝒳 ⊗ ℰ` as an nmiu-map (the mirror of **116III**.5). -/
def vtmulOneNMIU (E : Type u) [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    [VonNeumannAlgebra E] : NMIUMap X (VNT X E) where
  toStarAlgHom :=
    { toFun := fun x => x ⊗ᵥ (1 : E)
      map_one' := (vnTensor X E).isTensorProduct.miu.1
      map_mul' := fun x y => by
        have h := (vnTensor X E).isTensorProduct.miu.2.1 x y (1 : E) 1
        rwa [one_mul] at h
      map_zero' := map_zero ((vnTensor X E).map.flip 1)
      map_add' := fun x y => map_add ((vnTensor X E).map.flip 1) x y
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        change (vnTensor X E).map (r • 1) 1 = r • 1
        rw [map_smul, LinearMap.smul_apply, (vnTensor X E).isTensorProduct.miu.1]
      map_star' := fun x => by
        have h := (vnTensor X E).isTensorProduct.miu.2.2 x (1 : E)
        rw [star_one] at h
        exact h.symm }
  preservesDirSups' := by
    let p : X →ₚ[ℂ] VNT X E :=
      { toFun := fun x => x ⊗ᵥ (1 : E)
        map_add' := fun x y => map_add ((vnTensor X E).map.flip 1) x y
        map_smul' := fun c x => map_smul ((vnTensor X E).map.flip 1) c x
        monotone' := fun x y hxy => by
          have h := vtmul_nonneg (y - x) (1 : E) (sub_nonneg.mpr hxy) zero_le_one
          rw [show (y - x) ⊗ᵥ (1 : E) = y ⊗ᵥ (1 : E) - x ⊗ᵥ (1 : E) from
            map_sub ((vnTensor X E).map.flip 1) y x] at h
          exact sub_nonneg.mp h }
    exact ((p_uwcont p).out 0 2).mp (continuous_ultraweak_vtmul_left (1 : E))

@[simp] theorem vtmulOneNMIU_apply (E : Type u) [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] [VonNeumannAlgebra E] (x : X) :
    vtmulOneNMIU X E x = x ⊗ᵥ (1 : E) := rfl

/-- The first paragraph of the note's proof of Theorem 10, up to the
universal property: for a Paschke dilation `(𝒫, ϱ, h)` of `φ` and an
ncp-map `h' : 𝒳 ⊗ ℰ' → 𝒜` with `h'(x ⊗ 1) = φ(x)`, the mediating map
`σ : 𝒳 ⊗ ℰ' → 𝒫` of **140II** has the form `σ(x ⊗ e) = ϱ(x) τ(e)` for an
ncpu-map `τ : ℰ' → ϱ(𝒳)^□`, by the bimodularity **139III**. -/
theorem exists_paschke_mediator {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (φ : NCPMap X A) (ρ : NMIUMap X P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    {E' : Type u} [CStarAlgebra E'] [PartialOrder E'] [StarOrderedRing E'] [VonNeumannAlgebra E']
    (h' : NCPMap (VNT X E') A) (hh' : ∀ x, h' (x ⊗ᵥ (1 : E')) = φ x) :
    ∃ (σ : NCPMap (VNT X E') P) (τ : NCPMap E' (RangeComm ρ)),
      (∀ x, σ (x ⊗ᵥ (1 : E')) = ρ x) ∧ (∀ z, hP (σ z) = h' z) ∧
      (∀ x e, σ (x ⊗ᵥ e) = ρ x * (τ e).val) ∧ τ 1 = 1 := by
  obtain ⟨-, hUP⟩ := hD
  have hρ1 : ρ 1 = 1 := map_one ρ.toStarAlgHom
  set ι₁ := vtmulOneNMIU X E'
  have hι₁1 : ι₁ 1 = 1 := map_one ι₁.toStarAlgHom
  obtain ⟨σ, ⟨hσρ, hσh⟩, -⟩ :=
    hUP (⟨VNT X E', inferInstance, ι₁, h'⟩ : PaschkeTriple X A) fun a => hh' a
  have hσρ' : ∀ a, σ (a ⊗ᵥ (1 : E')) = ρ a := fun a => hσρ a
  have hbim : ∀ (a₁ a₂ : X) (c : VNT X E'), σ (ι₁ a₁ * c * ι₁ a₂) = ρ a₁ * σ c * ρ a₂ :=
    fun a₁ a₂ c => dils_univlemma ρ ι₁ σ hσρ a₁ a₂ c
  obtain ⟨ι₂, hι₂⟩ := (tensor_simple_facts_5 (A := X) (B := E') 1 zero_le_one).2
  have hmul : ∀ (x x' : X) (e e' : E'), (x ⊗ᵥ e) * (x' ⊗ᵥ e') = (x * x') ⊗ᵥ (e * e') :=
    fun x x' e e' => ((vnTensor X E').isTensorProduct.miu.2.1 x x' e e').symm
  have hleft : ∀ (x : X) (e : E'), σ (x ⊗ᵥ e) = ρ x * σ ((1 : X) ⊗ᵥ e) := by
    intro x e
    have h := hbim x 1 (ι₂ e)
    rwa [hι₁1, mul_one, hρ1, mul_one, hι₂, vtmulOneNMIU_apply, hmul, mul_one, one_mul]
      at h
  have hright : ∀ (x : X) (e : E'), σ (x ⊗ᵥ e) = σ ((1 : X) ⊗ᵥ e) * ρ x := by
    intro x e
    have h := hbim 1 x (ι₂ e)
    rwa [hι₁1, one_mul, hρ1, one_mul, hι₂, vtmulOneNMIU_apply, hmul, mul_one, one_mul]
      at h
  have hmem : ∀ e, ncpComp σ (nmiuNCP ι₂) e ∈ rangeComm ρ := by
    intro e
    rw [mem_rangeComm]
    intro x
    rw [ncpComp_apply, nmiuNCP_apply, hι₂, ← hleft, hright]
  set τ : NCPMap E' (RangeComm ρ) :=
    ncpCorestrict (ncpComp σ (nmiuNCP ι₂)) (rangeComm ρ) (isVNSubalgebra_rangeComm ρ)
      hmem
  have hτ : ∀ e, (τ e).val = σ ((1 : X) ⊗ᵥ e) := fun e => by
    rw [ncpCorestrict_val, ncpComp_apply, nmiuNCP_apply, hι₂]
  refine ⟨σ, τ, hσρ', fun c => hσh c, fun x e => by rw [hτ]; exact hleft x e, ?_⟩
  refine Theses.A.Proc.VNSub.val_injective ?_
  rw [hτ, hσρ']
  exact hρ1

/-- The note's **Theorem 10**, first paragraph of the proof (the `⇐`
direction, in the form of Lemma 9): for an arbitrary domain `𝒳`, if
`x ⊗ e ↦ ϱ(x) e` extends to an nmiu-map
`Ψ : 𝒳 ⊗ ϱ(𝒳)^□ → 𝒫`, then `h ∘ Ψ` is a Wittrock dilation of `φ`.  The
mediator for `h'` is the `τ` of `exists_paschke_mediator`; it is unique
because the mediator `σ` of **140II** is.  Neither injectivity nor
surjectivity of `Ψ` is used. -/
theorem isWittrockDilationOf_paschke_of_mul {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
    (φ : NCPMap X A) (ρ : NMIUMap X P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple X A) ⇑φ)
    (Ψ : NMIUMap (VNT X (RangeComm ρ)) P) (hΨ : ∀ x e, Ψ (x ⊗ᵥ e) = ρ x * e.val) :
    IsWittrockDilationOf ⇑φ (RangeComm ρ) (ncpComp hP (nmiuNCP Ψ)) := by
  have hρ1 : ρ 1 = 1 := map_one ρ.toStarAlgHom
  refine ⟨fun x => ?_, fun E' _ _ _ _ h' hh' => ?_⟩
  · rw [ncpComp_apply, nmiuNCP_apply, hΨ]
    change hP (ρ x * 1) = φ x
    rw [mul_one]
    exact hD.1 x
  obtain ⟨σ, τ, hσρ, hσh, hστ, hτ1⟩ := exists_paschke_mediator φ ρ hP hD h' hh'
  -- `Ψ ∘ (id ⊗ τ) = σ`
  have hkey : ncpComp (nmiuNCP Ψ) (tmap (ncpId X) τ) = σ := by
    refine ncp_ext_vnt _ _ fun x e => ?_
    rw [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, hΨ, hστ]
  refine ⟨τ, (isWittrockMediator_iff_tmap _ _ _).mpr ⟨fun x => ?_, fun z => ?_⟩, ?_⟩
  · rw [tmap_apply, ncpId_apply, hτ1]
  · rw [ncpComp_apply, ← ncpComp_apply (nmiuNCP Ψ), hkey]
    exact hσh z
  · rintro τ' ⟨σ'', he, h1, hh⟩
    have hσ₂ : ncpComp (nmiuNCP Ψ) σ'' = σ := by
      refine (hD.2 (⟨VNT X E', inferInstance, vtmulOneNMIU X E', h'⟩ : PaschkeTriple X A)
        fun a => hh' a).unique ⟨fun a => ?_, fun c => ?_⟩ ⟨hσρ, hσh⟩
      · change ncpComp (nmiuNCP Ψ) σ'' (a ⊗ᵥ (1 : E')) = ρ a
        rw [ncpComp_apply, nmiuNCP_apply, h1, hΨ]
        change ρ a * 1 = ρ a
        rw [mul_one]
      · change hP (ncpComp (nmiuNCP Ψ) σ'' c) = h' c
        rw [← hh c, ncpComp_apply, nmiuNCP_apply, ncpComp_apply, nmiuNCP_apply]
    refine DFunLike.ext _ _ fun e => Theses.A.Proc.VNSub.val_injective ?_
    have h1e := hστ 1 e
    rw [← hσ₂, ncpComp_apply, nmiuNCP_apply, he, hΨ, hρ1, one_mul, one_mul] at h1e
    exact h1e

end PaschkeWittrock

/-! ## Lemma 6 for `𝓑(ℋ)`, and Corollary 11

For every nmiu-map `ϱ : 𝓑(ℋ) → 𝒫`, `x ⊗ e ↦ ϱ(x) e` extends to an
nmiu-isomorphism `𝓑(ℋ) ⊗ ϱ(𝓑(ℋ))^□ ≅ 𝒫` (`exists_bh_split`); with Theorem
10, `⇐`, this gives Corollary 11. -/

section Splitting

section Bridge

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `(x, y) ↦ x ⊗ y` into the Hilbert tensor product `hilbTensor` of
`Stinespring.lean` (the one **138II** is stated with). -/
def hilbTensorMkBilin : H →ₗ[ℂ] K →ₗ[ℂ] Theses.B.Dils.hilbTensor H K :=
  LinearMap.mk₂ ℂ hilbTensorMk hilbTensorMk_add_left hilbTensorMk_smul_left
    hilbTensorMk_add_right hilbTensorMk_smul_right

/-- Stinespring's `hilbTensor` is a tensor product of Hilbert spaces in the
sense of **109II**. -/
theorem isHilbertTensorProduct_hilbTensorMk :
    IsHilbertTensorProduct (hilbTensorMkBilin (H := H) (K := K)) := by
  refine ⟨?_, fun x x' y y' => hilbTensor_inner_mk x x' y y'⟩
  set M := Submodule.span ℂ {t : Theses.B.Dils.hilbTensor H K |
    ∃ x y, t = hilbTensorMkBilin x y}
  have hsub : Set.range (fun z : TensorProduct ℂ H K =>
      ((z : Theses.B.Dils.hilbTensor H K))) ⊆ (M : Set _) := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero =>
        dsimp only
        rw [UniformSpace.Completion.coe_zero]
        exact M.zero_mem
    | tmul x y => exact Submodule.subset_span ⟨x, y, rfl⟩
    | add z z' hz hz' =>
        dsimp only at hz hz' ⊢
        rw [UniformSpace.Completion.coe_add]
        exact M.add_mem hz hz'
  exact hilbTensor_denseRange_coe.mono hsub

/-- The unitary `hilbTensor H K ≅ ℋ ⊗ 𝒦` between the two Hilbert tensor
products of the tree (**110V**). -/
theorem exists_hilbTensor_bridge :
    ∃ W : Theses.B.Dils.hilbTensor H K ≃ₗᵢ[ℂ] HT H K,
      ∀ x y, W (hilbTensorMk x y) = x ⊗ₕ y :=
  (hilb_tensor_unique _ _ isHilbertTensorProduct_hilbTensorMk
    (Theses.A.Proc.hilbTensor H K).isTensor).exists

end Bridge

section Helpers

/-- A bijective ∗-homomorphism between von Neumann algebras is an
nmiu-map: it is an order isomorphism, so it preserves suprema. -/
def nmiuOfBijective {B C : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : B →⋆ₐ[ℂ] C) (hf : Function.Bijective f) : NMIUMap B C where
  toStarAlgHom := f
  preservesDirSups' := starAlgEquiv_preservesDirSups' (StarAlgEquiv.ofBijective f hf)

@[simp] theorem nmiuOfBijective_apply {B C : Type u} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : B →⋆ₐ[ℂ] C) (hf : Function.Bijective f) (b : B) : nmiuOfBijective f hf b = f b :=
  rfl

/-- A ∗-homomorphism into a von Neumann subalgebra, corestricted. -/
def saCorestrict {B C : Type u} [CStarAlgebra B] [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (f : B →⋆ₐ[ℂ] C) (S : StarSubalgebra ℂ C)
    (hS : IsVNSubalgebra C S) (hmem : ∀ b, f b ∈ S) :
    B →⋆ₐ[ℂ] Theses.A.Proc.VNSub C S hS where
  toFun b := ⟨f b, hmem b⟩
  map_one' := Theses.A.Proc.VNSub.val_injective (map_one f)
  map_mul' b b' := Theses.A.Proc.VNSub.val_injective (map_mul f b b')
  map_zero' := Theses.A.Proc.VNSub.val_injective (map_zero f)
  map_add' b b' := Theses.A.Proc.VNSub.val_injective (map_add f b b')
  commutes' r := Theses.A.Proc.VNSub.val_injective (by
    change f (algebraMap ℂ B r) = (algebraMap ℂ (Theses.A.Proc.VNSub C S hS) r).val
    have halg : (algebraMap ℂ (Theses.A.Proc.VNSub C S hS) r).val = algebraMap ℂ C r := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [halg]
    exact f.commutes r)
  map_star' b := Theses.A.Proc.VNSub.val_injective (map_star f b)

@[simp] theorem saCorestrict_val {B C : Type u} [CStarAlgebra B] [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] (f : B →⋆ₐ[ℂ] C) (S : StarSubalgebra ℂ C)
    (hS : IsVNSubalgebra C S) (hmem : ∀ b, f b ∈ S) (b : B) :
    (saCorestrict f S hS hmem b).val = f b := rfl

variable {K K₂ : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- Conjugation `y ↦ V y V^*` by a unitary `V`, as a ∗-homomorphism. -/
def conjHom {V : K →L[ℂ] K₂} (hV : IsUnitaryCLM V) :
    (K →L[ℂ] K) →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂) where
  toFun := cext V
  map_one' := ucext_one hV
  map_mul' := cext_mul hV
  map_zero' := cext_zero V
  map_add' := cext_add V
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cext_smul,
      ucext_one hV]
  map_star' := cext_star V

theorem conjHom_bijective {V : K →L[ℂ] K₂} (hV : IsUnitaryCLM V) :
    Function.Bijective (conjHom hV) :=
  ⟨cext_injective hV, fun y => ⟨cmpr V y, ucext_cmpr hV y⟩⟩

variable (K K₂) in
/-- `a ↦ a ⊗ 1 : 𝓑(𝒦) → 𝓑(𝒦 ⊗ 𝒦₂)`, as a ∗-homomorphism. -/
def opTensorOneHom : (K →L[ℂ] K) →⋆ₐ[ℂ] (HT K K₂ →L[ℂ] HT K K₂) where
  toFun a := opTensor a 1
  map_one' := opTensor_one
  map_mul' a a' := by rw [← opTensor_mul, one_mul]
  map_zero' := by
    have h := opTensor_smul_left (0 : ℂ) (0 : K →L[ℂ] K) (1 : K₂ →L[ℂ] K₂)
    rwa [zero_smul, zero_smul] at h
  map_add' a a' := opTensor_add_left a a' 1
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, opTensor_smul_left,
      opTensor_one]
  map_star' a := by rw [opTensor_star, star_one]

@[simp] theorem opTensorOneHom_apply (a : K →L[ℂ] K) :
    opTensorOneHom K K₂ a = opTensor a 1 := rfl

/-- The claim in the proof of the note's Lemma 6 that `𝒫` is generated by
`𝓑(ℋ) ⊗ 1` and `1 ⊗ 𝒩`, where `ℛ^□ = 1 ⊗ 𝒩`, in the orientation `𝒦 ⊗ ℋ`:
a von Neumann algebra `N ⊆ 𝓑(𝒦 ⊗ ℋ)` containing `1 ⊗ 𝓑(ℋ)` is
`E₀ ⊗̄ 𝓑(ℋ)` for the von Neumann algebra `E₀ = {a : a ⊗ 1 ∈ N}`.  In the
note's letters, `N` is `𝒫` and `E₀` is `𝒩`.  Proved from the amplification
theorem instead of the note's matrix units: `N^□ ⊆ (1 ⊗ 𝓑(ℋ))^□ = 𝓑(𝒦) ⊗ 1`,
so `N^□ = C ⊗ 1` for a von Neumann algebra `C`, and
`N = (C ⊗ 1)^□ = C^□ ⊗̄ 𝓑(ℋ)` with `C^□ ⊆ E₀`. -/
theorem eq_concreteTensor_of_one_opTensor_mem {K H : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : StarSubalgebra ℂ (HT K H →L[ℂ] HT K H)) (hN : IsVNSubalgebra _ N)
    (h1N : ∀ b : H →L[ℂ] H, opTensor (1 : K →L[ℂ] K) b ∈ N) :
    IsVNSubalgebra _ (N.comap (opTensorOneHom K H)) ∧
      N = concreteTensor K H (N.comap (opTensorOneHom K H)) ⊤ := by
  -- `E₀ = {a : a ⊗ 1 ∈ N}` and `C = {c : c ⊗ 1 ∈ N^□}` are von Neumann algebras
  have hvn : ∀ M : StarSubalgebra ℂ (HT K H →L[ℂ] HT K H), IsVNSubalgebra _ M →
      IsVNSubalgebra _ (M.comap (opTensorOneHom K H)) := by
    intro M hM
    have hle : wstar (K →L[ℂ] K) ((M.comap (opTensorOneHom K H)) : Set (K →L[ℂ] K))
        ≤ M.comap (opTensorOneHom K H) := fun a ha =>
      opTensor_one_mem_of_mem_wstar hM (fun b hb => hb) ha
    have heq := le_antisymm hle fun a ha => (isVNSubalgebra_wstar (A := K →L[ℂ] K) _).2 ha
    rw [← heq]
    exact (isVNSubalgebra_wstar _).1
  set E₀ := N.comap (opTensorOneHom K H)
  have hE₀ : IsVNSubalgebra _ E₀ := hvn N hN
  set C := (vnComm N).comap (opTensorOneHom K H)
  have hC : IsVNSubalgebra _ C := hvn _ (isVNSubalgebra_vnComm N)
  have hQ : ∀ q ∈ vnComm N, ∃ c ∈ C, q = opTensor c 1 := by
    intro q hq
    obtain ⟨c, rfl⟩ := eq_opTensor_one_of_comm q fun b => (mem_vnComm.mp hq _ (h1N b)).symm
    exact ⟨c, hq, rfl⟩
  refine ⟨hE₀, ?_⟩
  refine le_antisymm (fun z hz => ?_) (concreteTensor_le hN fun a ha b _ => ?_)
  · have hC' : commutant _ (C : Set (K →L[ℂ] K)) ⊆ (E₀ : Set (K →L[ℂ] K)) := by
      intro c' hc'
      change opTensor c' 1 ∈ N
      rw [← vnComm_vnComm N hN]
      refine mem_vnComm.mpr fun q hq => ?_
      obtain ⟨c, hc, rfl⟩ := hQ q hq
      rw [← opTensor_mul, ← opTensor_mul, hc' c hc]
    have hz' : z ∈ commutant _ {w | ∃ a ∈ (C : Set (K →L[ℂ] K)),
        w = opTensor a (1 : H →L[ℂ] H)} := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_vnComm.mp ha z hz).symm
    rw [← amplification C hC] at hz'
    have hsub : {w : HT K H →L[ℂ] HT K H | ∃ a ∈ commutant _ (C : Set (K →L[ℂ] K)),
        ∃ b : H →L[ℂ] H, w = opTensor a b} ⊆ {x | ∃ a ∈ E₀,
        ∃ b ∈ (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)), x = opTensor a b} := by
      rintro w ⟨a, ha, b, rfl⟩
      exact ⟨a, hC' ha, b, StarSubalgebra.mem_top, rfl⟩
    exact wstar_mono hsub hz'
  · rw [show opTensor a b = opTensor a 1 * opTensor 1 b by
      rw [← opTensor_mul, mul_one, one_mul]]
    exact mul_mem ha (h1N b)

end Helpers

section Split

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : Type u} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P] [VonNeumannAlgebra P]

/-- Lemma 6 for the type I factor `ϱ(𝓑(ℋ))`: for an nmiu-map
`ϱ : 𝓑(ℋ) → 𝒫`, `x ⊗ e ↦ ϱ(x) e` extends to an nmiu-isomorphism
`𝓑(ℋ) ⊗ ϱ(𝓑(ℋ))^□ ≅ 𝒫`.  This is the first claim of the note's
Corollary 11, whose `ϱ` belongs to a Paschke dilation; only `ϱ` is used.
`exists_typeI_factor_iso` (in `WittrockSplit.lean`) transports it to Lemma 6
as stated, for any type I factor subalgebra.

The route is the note's: represent `𝒫` on some `𝒦` (**48VIII**), write
`ϱ(x) = U^*(x ⊗ 1)U` (**138II**), conjugate so that `ϱ(x) = 1 ⊗ x`, read
`𝒫 = 𝒩 ⊗̄ 𝓑(ℋ)` off `eq_concreteTensor_of_one_opTensor_mem` (whose `E₀` is
the note's `𝒩`), and finish
with **111VII** and **114II**.  Two detours are bookkeeping: **138II** is
stated with the Hilbert tensor product of `Stinespring.lean`, which
`exists_hilbTensor_bridge` identifies with that of `A/Proc/Tensor.lean`;
and the flip unitary puts `𝓑(ℋ)` second, the factor the amplification
theorem leaves whole. -/
theorem exists_bh_split (ρ : NMIUMap (H →L[ℂ] H) P) :
    ∃ Ψ : NMIUMap (VNT (H →L[ℂ] H) (RangeComm ρ)) P,
      Function.Bijective Ψ ∧ ∀ x e, Ψ (x ⊗ᵥ e) = ρ x * e.val := by
  classical
  have hρ1 : ρ 1 = 1 := map_one ρ.toStarAlgHom
  by_cases hPn : Nontrivial P
  swap
  · -- `𝒫 = {0}`: everything in sight is zero
    rw [not_nontrivial_iff_subsingleton] at hPn
    have hE : Subsingleton (RangeComm ρ) :=
      ⟨fun a b => Theses.A.Proc.VNSub.val_injective (Subsingleton.elim _ _)⟩
    have hT : Subsingleton (VNT (H →L[ℂ] H) (RangeComm ρ)) := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← (vnTensor (H →L[ℂ] H) (RangeComm ρ)).isTensorProduct.miu.1,
        Subsingleton.elim (1 : RangeComm ρ) 0, map_zero]
    let z : VNT (H →L[ℂ] H) (RangeComm ρ) →⋆ₐ[ℂ] P :=
      { toFun := fun _ => 0, map_one' := Subsingleton.elim _ _,
        map_mul' := fun _ _ => Subsingleton.elim _ _, map_zero' := rfl,
        map_add' := fun _ _ => Subsingleton.elim _ _,
        commutes' := fun _ => Subsingleton.elim _ _,
        map_star' := fun _ => Subsingleton.elim _ _ }
    refine ⟨⟨z, fun _ _ _ _ _ => ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
        fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩⟩,
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩,
      fun _ _ => Subsingleton.elim _ _⟩
  -- `ℋ ≠ 0`, since `𝒫 ≠ 0` and `ϱ` is unital
  obtain ⟨y₀, hy₀⟩ : ∃ y : H, y ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    have h1 : (1 : H →L[ℂ] H) = 0 := ContinuousLinearMap.ext fun z => by simp [hcon z]
    have h2 : (1 : P) = 0 := by
      rw [← hρ1, h1]
      exact map_zero ρ.toStarAlgHom
    exact one_ne_zero h2
  -- **48VIII**: `𝒫` acts on some `𝒦`
  obtain ⟨ι, f, hfinj, -⟩ := ngns P
  let ρ₁ := nmiuComp f ρ
  have hρ₁ : ∃ a, ρ₁ a ≠ 0 := by
    refine ⟨1, fun h => ?_⟩
    have h' : f 1 = f 0 := by
      have e0 : f 0 = 0 := map_zero f.toStarAlgHom
      rw [e0, ← hρ1]
      exact h
    exact one_ne_zero (hfinj h')
  -- **138II**: `ϱ₁(a) = U^* (a ⊗ 1) U`
  obtain ⟨K', _, _, _, U, hU1, hU2, hρU⟩ := nmiu_between_type_I ρ₁ hρ₁
  obtain ⟨W, hW⟩ := exists_hilbTensor_bridge (H := H) (K := K')
  have hUu : IsUnitaryCLM U := ⟨hU1, hU2⟩
  have hWu : IsUnitaryCLM (W : Theses.B.Dils.hilbTensor H K' →L[ℂ] HT H K') :=
    isUnitaryCLM_of_linearIsometryEquiv W
  let V := htFlip H K' ∘L ((W : Theses.B.Dils.hilbTensor H K' →L[ℂ] HT H K') ∘L U)
  have hVu : IsUnitaryCLM V :=
    isUnitaryCLM_comp (isUnitaryCLM_comp hUu hWu) (isUnitaryCLM_htFlip H K')
  have hWconj : ∀ a : H →L[ℂ] H,
      cext (W : Theses.B.Dils.hilbTensor H K' →L[ℂ] HT H K') (tensorCLM a 1)
        = opTensor a 1 := by
    intro a
    refine ext_htmul fun x y => ?_
    rw [cext_apply, W.adjoint_eq_symm, opTensor_apply, ← hW x y]
    change W (tensorCLM a 1 (W.symm (W (hilbTensorMk x y)))) = _
    rw [LinearIsometryEquiv.symm_apply_apply, tensorCLM_mk, hW]
  have hjρ₀ : ∀ a, cext V (ρ₁ a) = opTensor 1 a := by
    intro a
    rw [hρU a]
    change cext V (cmpr U (tensorCLM a 1)) = _
    rw [cext_comp, cext_comp, ucext_cmpr hUu, hWconj, cext_htFlip_opTensor]
  -- `j : 𝒫 → 𝓑(𝒦' ⊗ ℋ)`, `p ↦ V f(p) V^*`, with `j(ϱ(a)) = 1 ⊗ a`
  let j : NMIUMap P (HT K' H →L[ℂ] HT K' H) :=
    nmiuComp (nmiuOfBijective (conjHom hVu) (conjHom_bijective hVu)) f
  have hjinj : Function.Injective j := (conjHom_bijective hVu).1.comp hfinj
  have hjmul : ∀ p q, j (p * q) = j p * j q := map_mul j.toStarAlgHom
  have hjρ : ∀ a, j (ρ a) = opTensor 1 a := hjρ₀
  let N := j.toStarAlgHom.range
  have hN : IsVNSubalgebra _ N :=
    isVNSubalgebra_range j.toStarAlgHom hjinj j.preservesDirSups'
  have hjN : ∀ p, j p ∈ N := fun p => ⟨p, rfl⟩
  have h1N : ∀ b : H →L[ℂ] H, opTensor (1 : K' →L[ℂ] K') b ∈ N :=
    fun b => hjρ b ▸ hjN (ρ b)
  -- `N = E₀ ⊗̄ 𝓑(ℋ)` with `E₀ = {a : a ⊗ 1 ∈ N}`, the note's `𝒩`
  let E₀ := N.comap (opTensorOneHom K' H)
  obtain ⟨hE₀, hNT⟩ := eq_concreteTensor_of_one_opTensor_mem N hN h1N
  -- **111VII**: `(a, b) ↦ a ⊗ b` is a tensor product of `E₀` and `𝓑(ℋ)`
  obtain ⟨γ₀, hγ₀v, hγ₀⟩ := special_tensor E₀ (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) hE₀
    isVNSubalgebra_top
  -- the three nmiu-isomorphisms that move it onto `𝓑(ℋ)`, `ϱ(𝓑(ℋ))^□` and `𝒫`
  let jc := nmiuCorestrict j N hN hjN
  have hjc : Function.Bijective jc :=
    nmiuCorestrict_bijective j N hN hjN hjinj fun s ⟨p, hp⟩ => ⟨p, hp⟩
  let jinv := nmiuSymm jc hjc
  have hjinv : ∀ s, j (jinv s) = s.val := fun s =>
    congrArg Theses.A.Proc.VNSub.val (nmiuSymm_apply_apply' jc hjc s)
  have hWN : ∀ y : Theses.A.Proc.VNSub (HT K' H →L[ℂ] HT K' H)
      (wstar (HT K' H →L[ℂ] HT K' H) {x | ∃ a ∈ E₀,
        ∃ b ∈ (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)), x = opTensor a b})
      (isVNSubalgebra_wstar _).1, y.val ∈ N := by
    intro y
    rw [hNT]
    exact y.property
  let inc := nmiuCorestrict Theses.A.Proc.VNSub.valNMIU N hN hWN
  have hinc : Function.Bijective inc := by
    refine nmiuCorestrict_bijective _ N hN hWN Theses.A.Proc.VNSub.valNMIU_injective
      fun s hs => ?_
    rw [hNT] at hs
    exact ⟨⟨s, hs⟩, rfl⟩
  let Θ := nmiuComp jinv inc
  have hΘ : Function.Bijective Θ := (nmiuSymm_bijective jc hjc).comp hinc
  have hΘj : ∀ y, j (Θ y) = y.val := fun y => hjinv (inc y)
  let β := nmiuCorestrict (nmiuId (H →L[ℂ] H)) ⊤ isVNSubalgebra_top
    fun _ => StarSubalgebra.mem_top
  have hβ : Function.Bijective β :=
    nmiuCorestrict_bijective _ ⊤ _ _ nmiuId_bijective.1 fun s _ => ⟨s, rfl⟩
  -- `ψ : E₀ → ϱ(𝓑(ℋ))^□`, `a ↦ j⁻¹(a ⊗ 1)`
  have hmemψ : ∀ a : Theses.A.Proc.VNSub (K' →L[ℂ] K') E₀ hE₀,
      jinv ⟨opTensor a.val 1, a.property⟩ ∈ rangeComm ρ := by
    intro a
    rw [mem_rangeComm]
    intro x
    apply hjinj
    rw [hjmul, hjmul, hjρ, hjinv, ← opTensor_mul, ← opTensor_mul, one_mul, mul_one, one_mul,
      mul_one]
  let ψhom := saCorestrict (jinv.toStarAlgHom.comp (saCorestrict
      ((opTensorOneHom K' H).comp Theses.A.Proc.VNSub.valStarAlgHom) N hN
      fun a => a.property)) (rangeComm ρ) (isVNSubalgebra_rangeComm ρ) hmemψ
  have hψj : ∀ a, j (ψhom a).val = opTensor a.val 1 := fun a => hjinv _
  have hψ : Function.Bijective ψhom := by
    constructor
    · intro a b hab
      have h := congrArg (fun e : RangeComm ρ => j e.val) hab
      simp only [hψj] at h
      exact Theses.A.Proc.VNSub.val_injective (opTensor_one_right_inj hy₀ h)
    · intro e
      have hcomm : ∀ b : H →L[ℂ] H,
          j e.val * opTensor (1 : K' →L[ℂ] K') b = opTensor 1 b * j e.val := by
        intro b
        rw [← hjρ, ← hjmul, ← hjmul, (mem_rangeComm.mp e.property b).symm]
      obtain ⟨a, ha⟩ := eq_opTensor_one_of_comm (j e.val) hcomm
      have haE : a ∈ E₀ := by
        change opTensor a 1 ∈ N
        rw [← ha]
        exact hjN _
      refine ⟨⟨a, haE⟩, Theses.A.Proc.VNSub.val_injective (hjinj ?_)⟩
      rw [hψj, ha]
  let ψ := nmiuOfBijective ψhom hψ
  let φE := nmiuSymm ψ hψ
  have hjE : ∀ e : RangeComm ρ, j e.val = opTensor (φE e).val 1 := by
    intro e
    have h := nmiuSymm_apply_apply' ψ hψ e
    conv_lhs => rw [← h]
    exact hψj _
  -- transport, flip, and **114II**
  have hγ₁ := isTensorProduct_comp φE (nmiuSymm_bijective ψ hψ) β hβ hγ₀
  have hγ₂ := isTensorProduct_comp_target hγ₁ Θ hΘ
  have hγ₃ := isTensorProduct_flip hγ₂
  obtain ⟨Ψ, hΨe, hΨb, -⟩ := tensor_uniqueness (vnTensor (H →L[ℂ] H) (RangeComm ρ)).map _
    (vnTensor (H →L[ℂ] H) (RangeComm ρ)).isTensorProduct hγ₃
  refine ⟨Ψ, hΨb, fun x e => ?_⟩
  rw [show Ψ (x ⊗ᵥ e) = _ from hΨe x e]
  apply hjinj
  change j (Θ (γ₀ (φE e) (β x))) = j (ρ x * e.val)
  rw [hΘj, hγ₀v, hjmul, hjρ, hjE e, ← opTensor_mul, one_mul, mul_one]
  rfl

/-- The note's **Corollary 11**: for a Paschke dilation `(𝒫, ϱ, h)` of an
ncp-map `φ : 𝓑(ℋ) → 𝒜` (**140II**), `x ⊗ e ↦ ϱ(x) e` extends to an
nmiu-isomorphism `Ψ : 𝓑(ℋ) ⊗ ϱ(𝓑(ℋ))^□ ≅ 𝒫` (`exists_bh_split`), and
`h ∘ Ψ` is a Wittrock dilation of `φ` (`isWittrockDilationOf_paschke_of_mul`). -/
theorem isWittrockDilationOf_bh_paschke {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A]
    (φ : NCPMap (H →L[ℂ] H) A) (ρ : NMIUMap (H →L[ℂ] H) P) (hP : NCPMap P A)
    (hD : IsPaschkeDilationOf
      (⟨P, inferInstance, ρ, hP⟩ : PaschkeTriple (H →L[ℂ] H) A) ⇑φ) :
    ∃ Ψ : NMIUMap (VNT (H →L[ℂ] H) (RangeComm ρ)) P,
      Function.Bijective Ψ ∧ (∀ x e, Ψ (x ⊗ᵥ e) = ρ x * e.val) ∧
      IsWittrockDilationOf ⇑φ (RangeComm ρ) (ncpComp hP (nmiuNCP Ψ)) := by
  obtain ⟨Ψ, hΨb, hΨ⟩ := exists_bh_split ρ
  exact ⟨Ψ, hΨb, hΨ, isWittrockDilationOf_paschke_of_mul φ ρ hP hD Ψ hΨ⟩

end Split

/-- Corollary 11 with **154III**: every ncp-map `φ : 𝓑(ℋ) → 𝒜` has a
Wittrock dilation: combine
`isWittrockDilationOf_bh_paschke` with the Paschke dilation of **154III**. -/
theorem exists_wittrockDilation_of_bh {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
    (φ : NCPMap (H →L[ℂ] H) A) :
    ∃ (E : Type u) (_ : CStarAlgebra E) (_ : PartialOrder E) (_ : StarOrderedRing E)
      (_ : VonNeumannAlgebra E) (h : NCPMap (VNT (H →L[ℂ] H) E) A),
      IsWittrockDilationOf ⇑φ E h := by
  obtain ⟨M⟩ := existence_paschke φ
  let _ : VonNeumannAlgebra (Ba A M.X)ᵐᵒᵖ :=
    @vonNeumannAlgebra_mulOpposite (Ba A M.X) _ _ _ (ba_vonNeumannAlgebra M.selfDual)
  obtain ⟨Ψ, -, -, hW⟩ := isWittrockDilationOf_bh_paschke φ M.ρ M.h (existence_paschke_5 φ M)
  exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, _, hW⟩

end Splitting

end Theses.B.Dils
