/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex), §Measurement
(parsecs 930–1060): assert maps `a ↦ √p a √p`, corners `⌞p⌟𝒜⌞p⌟` and
filters with their universal properties, isomorphism theorems, purity,
contraposition (`f^⋄`/`f_⋄`), rigidity, ⋄-self-adjointness and
⋄-positivity, and the axiomatization of the sequential product
`p ∗ q = √p q √p`.

## Encoding

* The **corner** `e𝒜e` of `e ∈ A` appears in two guises: as the subset
  `cornerSet A e = {a | e·a·e = a}` of `A` (for element-level statements),
  and as a bundled type `Corner A e` (a one-field structure wrapper around
  that subset).  The C*/von Neumann algebra structure on `Corner A e`
  (with unit `e`, 94II parts 5–8) is **proved**; the coherence with the
  operations of `A` is pinned down by `corner_vna_basic`.  Those instances hold only when `e` is a
  **projection** (94I forms corners of projections only), which is carried
  through instance resolution as `[Fact (IsStarProjection e)]`; for the
  indices `⌈p⌉`, `⌊p⌋`, `⌈d⌉ᵣ` and `⌈f⌉` that occur in this chapter the
  `Fact` is discharged once and for all just above `cornerSet`.
* Maps into/out of corners (the standard corner `π_p`, the standard filter
  `c_p`, `Ad_a`-style maps, `[f]`, `⟨f⟩`) are obtained by *choice* from
  sorry-ed existence lemmas (`exists_...`), following the pattern of
  `Theses/B/Eff/WStarCat.lean`; their defining formulas are the
  corresponding `..._apply`/`..._spec` theorems.
* The universal properties are Prop-valued structures `IsCornerOf` (95I)
  and `IsFilter` (96I) quantifying over all von Neumann algebras in the
  same universe `u`.  A **corner** map simpliciter (`IsCornerMap`) is a
  *unital* corner of some effect, per the convention of 95I.
* **Purity** (100I) is the inductive closure of filters and corner maps
  under composition (`ncpComp`, composition of ncp-maps by choice).
-/
import Theses.A.VN.NormalFunctionals

open scoped ComplexOrder CStarAlgebra
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

variable {A B C : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-! ## Infrastructure: identity and composition of ncp-maps, carriers -/

section NormalityAux

/-! ### Auxiliary: normality of the identity and of composites

These are the routine facts behind `exists_ncpId`, `exists_ncpComp`,
`nmiuId` and `nmiuComp`.  `isLUB_val_of_isLUB` / `isLUB_of_isLUB_val` are
*generalisations* of `Theses.A.VN.isLUB_coe_of_isLUB` /
`Theses.A.VN.isLUB_sa_of_isLUB`: those are stated inside a
`variable [VonNeumannAlgebra A]` section of `Theses/A/VN/Projections.lean`
(Lean's `unusedSectionVars` linter flags the hypothesis as unused there),
whereas `exists_ncpId` and `exists_ncpComp` need them for plain
C*-algebras.  Once `omit [VonNeumannAlgebra A] in` is added upstream these
can be deleted in favour of the originals. -/

variable {A' B' C' : Type*}
  [NonUnitalRing A'] [StarRing A'] [PartialOrder A'] [StarOrderedRing A']
  [NonUnitalRing B'] [StarRing B'] [PartialOrder B'] [StarOrderedRing B']
  [NonUnitalRing C'] [StarRing C'] [PartialOrder C'] [StarOrderedRing C']

/-- The supremum of a nonempty set of self-adjoint elements computed in
`sa(A)` is its supremum in `A`. -/
theorem isLUB_val_of_isLUB {D : Set (selfAdjoint A')} {s : selfAdjoint A'}
    (hne : D.Nonempty) (h : IsLUB D s) :
    IsLUB (Subtype.val '' D) ((s : selfAdjoint A') : A') := by
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · have hu0 : ((d₀ : selfAdjoint A') : A') ≤ u := hu ⟨d₀, hd₀, rfl⟩
    have husa : IsSelfAdjoint u := by
      have hd : IsSelfAdjoint (u - ((d₀ : selfAdjoint A') : A')) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu0)
      simpa using hd.add d₀.2
    have hub : (⟨u, husa⟩ : selfAdjoint A') ∈ upperBounds D :=
      fun e he => hu ⟨e, he, rfl⟩
    exact h.2 hub

/-- Converse of `isLUB_val_of_isLUB`. -/
theorem isLUB_of_isLUB_val {D : Set (selfAdjoint A')} {s : selfAdjoint A'}
    (h : IsLUB (Subtype.val '' D) ((s : selfAdjoint A') : A')) : IsLUB D s := by
  refine ⟨fun d hd => Subtype.coe_le_coe.mp (h.1 ⟨d, hd, rfl⟩), fun v hv => ?_⟩
  refine Subtype.coe_le_coe.mp (h.2 ?_)
  rintro _ ⟨d, hd, rfl⟩
  exact Subtype.coe_le_coe.mpr (hv hd)

/-- The identity is normal. -/
theorem preservesDirSups_id : PreservesDirSups (fun a : A' => a) := by
  intro D s hne _ hlub
  exact isLUB_val_of_isLUB hne hlub

/-- A composite of normal maps is normal, provided the inner one preserves
self-adjointness and is monotone (as every positive map is). -/
theorem preservesDirSups_comp {f : A' → B'} {g : B' → C'}
    (hsa : ∀ x : A', IsSelfAdjoint x → IsSelfAdjoint (f x))
    (hmono : ∀ x y : A', x ≤ y → f x ≤ f y)
    (hf : PreservesDirSups f) (hg : PreservesDirSups g) :
    PreservesDirSups (fun a => g (f a)) := by
  intro D s hne hdir hlub
  set G : Set (selfAdjoint B') :=
    (fun d : selfAdjoint A' => (⟨f (d : A'), hsa _ d.2⟩ : selfAdjoint B')) '' D
    with hG
  have hval : Subtype.val '' G = (fun d : selfAdjoint A' => f (d : A')) '' D := by
    rw [hG, ← Set.image_comp]; rfl
  have hlubG : IsLUB G (⟨f (s : A'), hsa _ s.2⟩ : selfAdjoint B') := by
    refine isLUB_of_isLUB_val ?_
    rw [hval]
    exact hf D s hne hdir hlub
  have hGne : G.Nonempty := hne.image _
  have hGdir : DirectedOn (· ≤ ·) G := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩,
      Subtype.coe_le_coe.mp (hmono _ _ (Subtype.coe_le_coe.mpr hxz)),
      Subtype.coe_le_coe.mp (hmono _ _ (Subtype.coe_le_coe.mpr hyz))⟩
  have hkey := hg G _ hGne hGdir hlubG
  rw [hG, ← Set.image_comp] at hkey
  exact hkey

end NormalityAux

/-- A positive linear map between C*-algebras preserves self-adjointness
(via `a = a⁺ - a⁻`).  Generalises `Theses.A.VN.isSelfAdjoint_map_of_positive`,
which is stated inside a `variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]`
section (both hypotheses unused, as Lean's linter reports) and so cannot be
applied in `exists_ncpComp`, where `A`, `B`, `C` are plain C*-algebras. -/
theorem isSelfAdjoint_map_of_pos {A' B' : Type*}
    [CStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    (f : A' →ₚ[ℂ] B') {x : A'} (hx : IsSelfAdjoint x) : IsSelfAdjoint (f x) := by
  have hsplit : posPart x - negPart x = x := CFC.posPart_sub_negPart x hx
  have hz : (f (0 : A') : B') = 0 := map_zero f
  have h1 : (0 : B') ≤ f (posPart x) := by
    have h : (f (0 : A') : B') ≤ f (posPart x) := f.monotone (CFC.posPart_nonneg x)
    rwa [hz] at h
  have h2 : (0 : B') ≤ f (negPart x) := by
    have h : (f (0 : A') : B') ≤ f (negPart x) := f.monotone (CFC.negPart_nonneg x)
    rwa [hz] at h
  have := (IsSelfAdjoint.of_nonneg h1).sub (IsSelfAdjoint.of_nonneg h2)
  rwa [← map_sub, hsplit] at this

/-- Infrastructure: the identity map is an ncp-map (cf. 100II part 2);
stated as an existence lemma from which `ncpId` is obtained by choice. -/
theorem exists_ncpId (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : ∃ f : NCPMap A A, ∀ a : A, f a = a := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := LinearMap.id
                map_cstarMatrix_nonneg' := fun k M hM => by simpa using hM }
            preservesDirSups' := preservesDirSups_id }, fun a => rfl⟩

/-- The identity ncp-map. -/
noncomputable def ncpId (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : NCPMap A A := (exists_ncpId A).choose

theorem ncpId_apply (a : A) : ncpId A a = a := (exists_ncpId A).choose_spec a

/-- Infrastructure: ncp-maps are closed under composition; stated as an
existence lemma from which `ncpComp` is obtained by choice. -/
theorem exists_ncpComp (g : NCPMap B C) (f : NCPMap A B) :
    ∃ h : NCPMap A C, ∀ a : A, h a = g (f a) := by
  have hmono : ∀ x y : A, x ≤ y → f x ≤ f y := fun x y h =>
    OrderHomClass.mono f.toCompletelyPositiveMap h
  have hsa : ∀ x : A, IsSelfAdjoint x → IsSelfAdjoint (f x) := fun x hx =>
    isSelfAdjoint_map_of_pos (PositiveLinearMap.ofClass f.toCompletelyPositiveMap) hx
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap :=
                  (g.toCompletelyPositiveMap.toLinearMap).comp
                    f.toCompletelyPositiveMap.toLinearMap
                map_cstarMatrix_nonneg' := fun k M hM => by
                  have h1 : (0 : CStarMatrix (Fin k) (Fin k) B) ≤
                      M.map f.toCompletelyPositiveMap.toLinearMap :=
                    f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
                  have h2 := g.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k _ h1
                  exact h2 }
            preservesDirSups' := by
              exact preservesDirSups_comp (f := ⇑f) (g := ⇑g) hsa hmono
                f.preservesDirSups' g.preservesDirSups' }, fun a => rfl⟩

/-- Composition `g ∘ f` of ncp-maps. -/
noncomputable def ncpComp (g : NCPMap B C) (f : NCPMap A B) : NCPMap A C :=
  (exists_ncpComp g f).choose

theorem ncpComp_apply (g : NCPMap B C) (f : NCPMap A B) (a : A) :
    ncpComp g f a = g (f a) := (exists_ncpComp g f).choose_spec a

/-- Infrastructure (vn.tex 63I applied to an ncp-map, needed throughout
this chapter): an ncp-map `f` between von Neumann algebras has a least
projection `p` with `f(p^⊥) = 0` — its **carrier** `⌈f⌉`. -/
theorem exists_ncpCarrier [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    ∃! p : A, IsStarProjection p ∧ f (1 - p) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → p ≤ q :=
  exists_carrier (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
    f.preservesDirSups'

/-- The carrier `⌈f⌉` of an ncp-map between von Neumann algebras (least
projection `p` with `f(p^⊥) = 0`), by choice from `exists_ncpCarrier`. -/
noncomputable def ncpCarrier [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) : A := (exists_ncpCarrier f).choose

/-! ### Infrastructure: projection-hood of `⌈·⌉`, `⌊·⌋`, `⌈·⌉ᵣ` and `⌈f⌉`

The corner `e𝒜e` is only a von Neumann algebra when `e` is a *projection*
(94I/94II), so the instances on `Corner A e` below are stated under
`[Fact (IsStarProjection e)]`.  The indices that actually occur in this
chapter — `⌈p⌉`, `⌊p⌋`, `⌈d⌉ᵣ` and `⌈f⌉` — are projections
*unconditionally* (`ceil`/`floor` have junk value `0` off their domain, and
`0` is a projection), so the corresponding `Fact` instances are supplied
here once and for all. -/

/-- `⌈b⌉` is a projection for **every** `b : A`: for positive `b` this is
`ceil_spec`, and off the positive cone `⌈b⌉` is the junk value `0`. -/
theorem isStarProjection_ceil [VonNeumannAlgebra A] (b : A) :
    IsStarProjection (ceil b) := by
  by_cases hb : 0 ≤ b
  · exact (ceil_spec hb).1
  · simp only [ceil, dif_neg hb]
    exact IsStarProjection.zero A

/-- `⌊b⌋` is a projection for **every** `b : A` (junk value `0` off the
effects). -/
theorem isStarProjection_floor [VonNeumannAlgebra A] (b : A) :
    IsStarProjection (floor b) := by
  by_cases hb : b ∈ effects A
  · exact (floor_spec hb).1
  · simp only [floor, dif_neg hb]
    exact IsStarProjection.zero A

/-- The support projection `⌈b⌉ᵣ = ⌈b*b⌉` is a projection. -/
theorem isStarProjection_suppProj [VonNeumannAlgebra A] (b : A) :
    IsStarProjection (suppProj b) := isStarProjection_ceil _

/-- The carrier `⌈f⌉` of an ncp-map is a projection. -/
theorem isStarProjection_ncpCarrier [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NCPMap A B) : IsStarProjection (ncpCarrier f) :=
  (exists_ncpCarrier f).choose_spec.1.1

instance factIsStarProjectionCeil [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (ceil b)) := ⟨isStarProjection_ceil b⟩

instance factIsStarProjectionFloor [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (floor b)) := ⟨isStarProjection_floor b⟩

instance factIsStarProjectionSuppProj [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (suppProj b)) := ⟨isStarProjection_suppProj b⟩

instance factIsStarProjectionNcpCarrier [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NCPMap A B) :
    Fact (IsStarProjection (ncpCarrier f)) := ⟨isStarProjection_ncpCarrier f⟩

/-! ## Parsec 940: the corner `e𝒜e` -/

variable (A) in
/-- **94I** (proc.tex:176, Definition): the **corner** of a projection `e`
of a von Neumann algebra `A`, as a subset of `A`: the set `e𝒜e` of
elements of the form `e·a·e`, here rendered as `{a | e·a·e = a}`
(equivalent by 94II part 1). -/
def cornerSet (e : A) : Set A := {a : A | e * a * e = a}

variable (A) in
/-- **94I** (proc.tex:176, Definition), bundled form: the corner `e𝒜e` as
a type of its own.  By **94II** (parts 5–8) it is a von Neumann algebra
with unit `e`; those instances are proved below, guarded by
`[Fact (IsStarProjection e)]` (94I forms corners of projections only). -/
structure Corner (e : A) : Type u where
  /-- The underlying element of `A`. -/
  val : A
  /-- Membership in the corner: `e·val·e = val`. -/
  property : e * val * e = val

/-! ### The algebraic structure of the corner

Everything here is carried by `Corner.val` from `A`, except the unit, which
is `e`.  The elementary instances below are the ingredients out of which the
four instances demanded by 94II parts 5–8 are assembled; they are stated so
that `Corner.val` is a (non-unital) ∗-algebra isometry onto the closed set
`cornerSet A e`. -/

namespace Corner

variable {e : A}

theorem val_injective : Function.Injective (Corner.val : Corner A e → A) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  cases h; rfl

section Proj

variable [hFe : Fact (IsStarProjection e)]

/-- The projection hypothesis carried by the `Fact` instance. -/
theorem proj (e : A) [hFe : Fact (IsStarProjection e)] : IsStarProjection e :=
  hFe.out

theorem mul_left (a : Corner A e) : e * a.val = a.val := by
  have hee : e * e = e := (proj e).isIdempotentElem.eq
  calc e * a.val = e * (e * a.val * e) := by rw [a.property]
    _ = (e * e) * a.val * e := by noncomm_ring
    _ = e * a.val * e := by rw [hee]
    _ = a.val := a.property

theorem mul_right (a : Corner A e) : a.val * e = a.val := by
  have hee : e * e = e := (proj e).isIdempotentElem.eq
  calc a.val * e = (e * a.val * e) * e := by rw [a.property]
    _ = e * a.val * (e * e) := by noncomm_ring
    _ = e * a.val * e := by rw [hee]
    _ = a.val := a.property

instance : Zero (Corner A e) := ⟨⟨0, by simp⟩⟩
instance : Add (Corner A e) :=
  ⟨fun a b => ⟨a.val + b.val, by rw [mul_add, add_mul, a.property, b.property]⟩⟩
instance : Neg (Corner A e) := ⟨fun a => ⟨-a.val, by rw [mul_neg, neg_mul, a.property]⟩⟩
instance : Sub (Corner A e) :=
  ⟨fun a b => ⟨a.val - b.val, by rw [mul_sub, sub_mul, a.property, b.property]⟩⟩
instance : SMul ℕ (Corner A e) :=
  ⟨fun n a => ⟨n • a.val, by rw [mul_smul_comm, smul_mul_assoc, a.property]⟩⟩
instance : SMul ℤ (Corner A e) :=
  ⟨fun n a => ⟨n • a.val, by rw [mul_smul_comm, smul_mul_assoc, a.property]⟩⟩
instance : SMul ℂ (Corner A e) :=
  ⟨fun n a => ⟨n • a.val, by rw [mul_smul_comm, smul_mul_assoc, a.property]⟩⟩
instance : One (Corner A e) :=
  ⟨⟨e, by rw [(proj e).isIdempotentElem.eq, (proj e).isIdempotentElem.eq]⟩⟩
instance : Mul (Corner A e) :=
  ⟨fun a b => ⟨a.val * b.val, by
    have h1 := mul_left a
    have h2 := mul_right b
    calc e * (a.val * b.val) * e = (e * a.val) * (b.val * e) := by noncomm_ring
      _ = a.val * b.val := by rw [h1, h2]⟩⟩
instance : Star (Corner A e) :=
  ⟨fun a => ⟨star a.val, by
    have hs : star e = e := (proj e).isSelfAdjoint.star_eq
    conv_rhs => rw [← a.property]
    rw [star_mul, star_mul, hs, mul_assoc]⟩⟩

@[simp] theorem val_zero : (0 : Corner A e).val = 0 := rfl
@[simp] theorem val_add (a b : Corner A e) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_neg (a : Corner A e) : (-a).val = -a.val := rfl
@[simp] theorem val_sub (a b : Corner A e) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_one : (1 : Corner A e).val = e := rfl
@[simp] theorem val_mul (a b : Corner A e) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_star (a : Corner A e) : (star a).val = star a.val := rfl
@[simp] theorem val_smul (z : ℂ) (a : Corner A e) : (z • a).val = z • a.val := rfl
@[simp] theorem val_nsmul (n : ℕ) (a : Corner A e) : (n • a).val = n • a.val := rfl
@[simp] theorem val_zsmul (n : ℤ) (a : Corner A e) : (n • a).val = n • a.val := rfl

instance instAddCommGroup : AddCommGroup (Corner A e) :=
  Function.Injective.addCommGroup Corner.val val_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance instRing : Ring (Corner A e) where
  __ := instAddCommGroup
  mul_assoc a b c := val_injective (mul_assoc _ _ _)
  one_mul a := val_injective (mul_left a)
  mul_one a := val_injective (mul_right a)
  left_distrib a b c := val_injective (mul_add _ _ _)
  right_distrib a b c := val_injective (add_mul _ _ _)
  zero_mul a := val_injective (zero_mul _)
  mul_zero a := val_injective (mul_zero _)

/-- `Corner.val` as an additive monoid homomorphism. -/
def valAddHom : Corner A e →+ A where
  toFun := Corner.val
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℂ (Corner A e) :=
  Function.Injective.module ℂ valAddHom val_injective (fun _ _ => rfl)

instance instAlgebra : Algebra ℂ (Corner A e) :=
  Algebra.ofModule (fun r x y => val_injective (smul_mul_assoc r x.val y.val))
    (fun r x y => val_injective (mul_smul_comm r x.val y.val))

instance instStarRing : StarRing (Corner A e) where
  star_involutive a := val_injective (star_star a.val)
  star_mul a b := val_injective (star_mul a.val b.val)
  star_add a b := val_injective (star_add a.val b.val)

instance instStarModule : StarModule ℂ (Corner A e) where
  star_smul r a := val_injective (star_smul r a.val)

/-- `Corner.val` as a non-unital ring homomorphism.  It is *not* unital:
`(1 : Corner A e).val = e`. -/
def valNonUnitalRingHom : Corner A e →ₙ+* A where
  toFun := Corner.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance instNormedRing : NormedRing (Corner A e) :=
  NormedRing.induced (Corner A e) A valNonUnitalRingHom val_injective

@[simp] theorem norm_def (a : Corner A e) : ‖a‖ = ‖a.val‖ := rfl

instance instNormedAlgebra : NormedAlgebra ℂ (Corner A e) where
  norm_smul_le r a := by simpa [norm_def] using (norm_smul_le r a.val)

theorem isometry_val : Isometry (Corner.val : Corner A e → A) :=
  AddMonoidHomClass.isometry_of_norm valAddHom (fun _ => rfl)

theorem range_val : Set.range (Corner.val : Corner A e → A) = cornerSet A e := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩; exact b.property
  · intro ha; exact ⟨⟨a, ha⟩, rfl⟩

/-- The corner is norm-closed: it is the preimage of `{0}` under the
continuous map `a ↦ e·a·e − a`. -/
theorem isClosed_cornerSet : IsClosed (cornerSet A e) := by
  have hcont : Continuous (fun a : A => e * a * e - a) := by fun_prop
  have h : cornerSet A e = (fun a : A => e * a * e - a) ⁻¹' {0} := by
    ext a; simp [cornerSet, sub_eq_zero]
  rw [h]
  exact isClosed_singleton.preimage hcont

instance instCompleteSpace : CompleteSpace (Corner A e) := by
  refine (isometry_val (e := e)).isUniformInducing.completeSpace ?_
  rw [range_val]
  exact isClosed_cornerSet.isComplete

instance instCStarRing : CStarRing (Corner A e) where
  norm_mul_self_le a := CStarRing.norm_star_mul_self (x := a.val) |>.symm.le

end Proj

end Corner

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 5: the
corner `e𝒜e` of a **projection** `e` is a C*-algebra (with the operations
of `A` and unit `e`). -/
noncomputable instance (e : A) [Fact (IsStarProjection e)] :
    CStarAlgebra (Corner A e) where

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), parts 5–6: the
canonical (Loewner) partial order on the corner `e𝒜e`. -/
noncomputable instance (e : A) [Fact (IsStarProjection e)] :
    PartialOrder (Corner A e) :=
  PartialOrder.lift Corner.val Corner.val_injective

namespace Corner

variable {e : A} [Fact (IsStarProjection e)]

theorem le_def (a b : Corner A e) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

/-- The square root of a positive element of the corner again lies in the
corner: if `e·a·e = a` then `(1−e)·a·(1−e) = 0`, so for `s = √a` one has
`‖s(1−e)‖² = ‖(1−e)·a·(1−e)‖ = 0`, i.e. `s = s·e = e·s`. -/
theorem sqrt_mem (a : A) (ha : 0 ≤ a) (hmem : e * a * e = a) :
    e * CFC.sqrt a * e = CFC.sqrt a := by
  set s := CFC.sqrt a with hs
  have hsa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha
  have hee : e * e = e := (proj e).isIdempotentElem.eq
  have hse : star e = e := (proj e).isSelfAdjoint.star_eq
  have hkey : (1 - e) * a * (1 - e) = 0 := by
    conv_lhs => rw [← hmem]
    have h1 : (1 - e) * e = 0 := by noncomm_ring [hee]
    have h2 : e * (1 - e) = 0 := by noncomm_ring [hee]
    calc (1 - e) * (e * a * e) * (1 - e)
        = ((1 - e) * e) * a * (e * (1 - e)) := by noncomm_ring
      _ = 0 := by rw [h1, h2]; simp
  have hnorm : ‖s * (1 - e)‖ = 0 := by
    have hstar : star (s * (1 - e)) * (s * (1 - e)) = (1 - e) * a * (1 - e) := by
      rw [star_mul, hsa.star_eq, star_sub, star_one, hse]
      calc (1 - e) * s * (s * (1 - e)) = (1 - e) * (s * s) * (1 - e) := by
            noncomm_ring
        _ = (1 - e) * a * (1 - e) := by rw [hss]
    have h2 : ‖s * (1 - e)‖ * ‖s * (1 - e)‖ = ‖(1 - e) * a * (1 - e)‖ := by
      rw [← hstar, CStarRing.norm_star_mul_self]
    rw [hkey, norm_zero] at h2
    nlinarith [norm_nonneg (s * (1 - e))]
  have hzero : s * (1 - e) = 0 := by rwa [norm_eq_zero] at hnorm
  have hse' : s * e = s := by
    have h := hzero
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  have hes : e * s = s := by
    have h := congrArg star hse'
    rwa [star_mul, hse, hsa.star_eq] at h
  rw [hes, hse']

end Corner

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), parts 5–6: the
order on the corner `e𝒜e` is the star-order. -/
instance (e : A) [Fact (IsStarProjection e)] :
    StarOrderedRing (Corner A e) := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · show z.val + x.val ≤ z.val + y.val
    exact add_le_add le_rfl (show x.val ≤ y.val from hxy)
  · constructor
    · intro hx
      have hx' : (0 : A) ≤ x.val := hx
      refine ⟨⟨CFC.sqrt x.val, Corner.sqrt_mem x.val hx' x.property⟩, ?_⟩
      refine Corner.val_injective ?_
      have hsa : IsSelfAdjoint (CFC.sqrt x.val) :=
        IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x.val)
      show x.val = star (CFC.sqrt x.val) * CFC.sqrt x.val
      rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self x.val hx']
    · rintro ⟨s, rfl⟩
      show (0 : A) ≤ star s.val * s.val
      exact star_mul_self_nonneg s.val

/-- Generalisation of **94II** part 6 needed already for the von Neumann
instance below: the supremum in `A` of a nonempty directed set of
self-adjoint elements of the corner again lies in the corner. -/
theorem isLUB_mem_cornerSet [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) (D : Set (selfAdjoint A)) (s : selfAdjoint A)
    (hD : ∀ d ∈ D, (d : A) ∈ cornerSet A e) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    (s : A) ∈ cornerSet A e := by
  have h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D :=
    ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hstar : star e = e := he.isSelfAdjoint.star_eq
  have hnat := ad_normal e D h
  rw [hstar] at hnat
  have himg : (fun d : selfAdjoint A => e * (d : A) * e) '' D = Subtype.val '' D :=
    Set.image_congr fun d hd => hD d hd
  rw [himg] at hnat
  have huniq := hnat.unique (isLUB_coe_of_isLUB h.1 (isLUB_dirSup D h))
  have hsd : s = dirSup D h := hlub.unique (isLUB_dirSup D h)
  show e * (s : A) * e = (s : A)
  rw [hsd]
  exact huniq

namespace Corner

variable {e : A} [Fact (IsStarProjection e)] [VonNeumannAlgebra A]

/-- A self-adjoint element of the corner, viewed in `A`. -/
def saMap (d : selfAdjoint (Corner A e)) : selfAdjoint A :=
  ⟨d.1.val, congrArg Corner.val (show star d.1 = d.1 from d.2)⟩

@[simp] theorem saMap_coe (d : selfAdjoint (Corner A e)) :
    ((saMap d : selfAdjoint A) : A) = d.1.val := rfl

/-- Suprema of nonempty directed sets of self-adjoint elements are computed
in the corner exactly as they are in `A` (94II part 6). -/
theorem isLUB_saMap_image {D : Set (selfAdjoint (Corner A e))}
    {s : selfAdjoint (Corner A e)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (saMap '' D) (saMap s) := by
  set D' : Set (selfAdjoint A) := saMap '' D with hD'
  have hne' : D'.Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) D' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
    exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩
  have hbdd' : BddAbove D' := by
    refine ⟨saMap s, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hlub.1 hx
  obtain ⟨s₀, hs₀⟩ :=
    VonNeumannAlgebra.isLUB_of_bddAbove_directed D' hne' hdir' hbdd'
  have hmem : (s₀ : A) ∈ cornerSet A e := by
    refine isLUB_mem_cornerSet e (proj e) D' s₀ ?_ hne' hdir' hs₀
    rintro _ ⟨x, hx, rfl⟩
    exact x.1.property
  set t : Corner A e := ⟨(s₀ : A), hmem⟩ with ht
  have htsa : IsSelfAdjoint t := val_injective s₀.2
  have hlubt : IsLUB D ⟨t, htsa⟩ := by
    constructor
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro u hu
      have hub : saMap u ∈ upperBounds D' := by
        rintro _ ⟨x, hx, rfl⟩
        exact hu hx
      exact hs₀.2 hub
  have hst : s = ⟨t, htsa⟩ := hlub.unique hlubt
  have hsm : saMap (⟨t, htsa⟩ : selfAdjoint (Corner A e)) = s₀ := Subtype.ext rfl
  rw [hst, hsm]
  exact hs₀

/-- Restriction of an np-functional on `A` to the corner (94II part 8). -/
def restrictNP (e : A) [Fact (IsStarProjection e)] (ω : NPFunctional A) :
    NPFunctional (Corner A e) where
  toPositiveLinearMap :=
    { toFun := fun a => ω a.val
      map_add' := fun x y => map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c x => map_smul ω.toPositiveLinearMap _ _
      monotone' := fun x y hxy => ω.toPositiveLinearMap.monotone hxy }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hkey := ω.preservesDirSups' (saMap '' D) (saMap s) (hne.image _)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
        obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
        exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩)
      (isLUB_saMap_image hne hdir hlub)
    rw [← Set.image_comp] at hkey
    exact hkey

@[simp] theorem restrictNP_apply (e : A) [Fact (IsStarProjection e)]
    (ω : NPFunctional A) (a : Corner A e) : restrictNP e ω a = ω a.val := rfl

end Corner

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 8
(conclusion): the corner `e𝒜e` of a von Neumann algebra is a von Neumann
algebra. -/
instance (e : A) [Fact (IsStarProjection e)] [VonNeumannAlgebra A] :
    VonNeumannAlgebra (Corner A e) where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    obtain ⟨u, hu⟩ := hbdd
    have hne' : (Corner.saMap '' D).Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) (Corner.saMap '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨v, hv, hxv, hzv⟩ := hdir x hx z hz
      exact ⟨Corner.saMap v, ⟨v, hv, rfl⟩, hxv, hzv⟩
    have hbdd' : BddAbove (Corner.saMap '' D) := by
      refine ⟨Corner.saMap u, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    obtain ⟨s₀, hs₀⟩ :=
      VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
    have hmem : (s₀ : A) ∈ cornerSet A e := by
      refine isLUB_mem_cornerSet e (Corner.proj e) _ s₀ ?_ hne' hdir' hs₀
      rintro _ ⟨x, hx, rfl⟩
      exact x.1.property
    refine ⟨⟨⟨(s₀ : A), hmem⟩, Corner.val_injective s₀.2⟩, ?_, ?_⟩
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro v hv
      have hub : Corner.saMap v ∈ upperBounds (Corner.saMap '' D) := by
        rintro _ ⟨x, hx, rfl⟩
        exact hv hx
      exact hs₀.2 hub
  np_faithful := by
    intro a ha hω
    refine Corner.val_injective ?_
    exact VonNeumannAlgebra.np_faithful a.val ha
      (fun ω => hω (Corner.restrictNP e ω))

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 1: for a
projection `e`, an `a ∈ A` is of the form `e·b·e` iff `e·a·e = a` iff both
the support and range projections `⌈a⌉ᵣ, ⌈a⌉ₗ` lie below `e`. -/
theorem corner_vna_basic_1 [VonNeumannAlgebra A] (e a : A)
    (he : IsStarProjection e) :
    ((∃ b : A, a = e * b * e) ↔ a ∈ cornerSet A e) ∧
      (a ∈ cornerSet A e ↔ suppProj a ≤ e ∧ rangeProj a ≤ e) := by
  have hee : e * e = e := he.isIdempotentElem.eq
  have hmem : ∀ x : A, e * x * e = x → e * x = x ∧ x * e = x := by
    intro x hx
    refine ⟨?_, ?_⟩
    · calc e * x = e * (e * x * e) := by rw [hx]
        _ = e * e * x * e := by noncomm_ring
        _ = x := by rw [hee, hx]
    · calc x * e = e * x * e * e := by rw [hx]
        _ = e * x * (e * e) := by noncomm_ring
        _ = x := by rw [hee, hx]
  constructor
  · constructor
    · rintro ⟨b, rfl⟩
      show e * (e * b * e) * e = e * b * e
      calc e * (e * b * e) * e = (e * e) * b * (e * e) := by noncomm_ring
        _ = e * b * e := by rw [hee]
    · intro ha; exact ⟨a, ha.symm⟩
  · constructor
    · intro ha
      obtain ⟨h1, h2⟩ := hmem a ha
      exact ⟨(ceill_basic_1 a).2 ⟨he, h2⟩, (ceill_basic_2 a).2 ⟨he, h1⟩⟩
    · rintro ⟨hs, hr⟩
      have hsp : IsStarProjection (suppProj a) := (ceill_basic_1 a).1.1
      have hrp : IsStarProjection (rangeProj a) := (ceill_basic_2 a).1.1
      have hse : suppProj a * e = suppProj a :=
        ((projection_below_effect e (suppProj a) ⟨he.nonneg, he.le_one⟩ hsp).out 0 7).mp hs
      have hre : e * rangeProj a = rangeProj a :=
        ((projection_below_effect e (rangeProj a) ⟨he.nonneg, he.le_one⟩ hrp).out 0 6).mp hr
      have hae : a * e = a := by
        calc a * e = a * suppProj a * e := by rw [(ceill_basic_1 a).1.2]
          _ = a * (suppProj a * e) := by noncomm_ring
          _ = a * suppProj a := by rw [hse]
          _ = a := (ceill_basic_1 a).1.2
      have hea : e * a = a := by
        calc e * a = e * (rangeProj a * a) := by rw [(ceill_basic_2 a).1.2]
          _ = (e * rangeProj a) * a := by noncomm_ring
          _ = rangeProj a * a := by rw [hre]
          _ = a := (ceill_basic_2 a).1.2
      show e * a * e = a
      rw [hea, hae]

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 2: the
corner `e𝒜e` is closed under addition, scalar multiplication,
multiplication and involution. -/
theorem corner_vna_basic_2 (e : A) (he : IsStarProjection e) (a b : A)
    (ha : a ∈ cornerSet A e) (hb : b ∈ cornerSet A e) (z : ℂ) :
    a + b ∈ cornerSet A e ∧ z • a ∈ cornerSet A e ∧
      a * b ∈ cornerSet A e ∧ star a ∈ cornerSet A e := by
  have hee : e * e = e := he.isIdempotentElem.eq
  have ha' : e * a * e = a := ha
  have hb' : e * b * e = b := hb
  have hea : e * a = a := by
    calc e * a = e * (e * a * e) := by rw [ha']
      _ = e * e * a * e := by noncomm_ring
      _ = a := by rw [hee, ha']
  have hbe : b * e = b := by
    calc b * e = e * b * e * e := by rw [hb']
      _ = e * b * (e * e) := by noncomm_ring
      _ = b := by rw [hee, hb']
  refine ⟨?_, ?_, ?_, ?_⟩
  · show e * (a + b) * e = a + b
    rw [mul_add, add_mul, ha', hb']
  · show e * (z • a) * e = z • a
    rw [mul_smul_comm, smul_mul_assoc, ha']
  · show e * (a * b) * e = a * b
    calc e * (a * b) * e = (e * a) * (b * e) := by noncomm_ring
      _ = a * b := by rw [hea, hbe]
  · show e * star a * e = star a
    have := congrArg star ha'
    rw [star_mul, star_mul, he.isSelfAdjoint.star_eq] at this
    calc e * star a * e = e * (star a * e) := by noncomm_ring
      _ = star a := this

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 3: `e` is
a unit for the corner `e𝒜e`. -/
theorem corner_vna_basic_3 (e : A) (he : IsStarProjection e) (a : A)
    (ha : a ∈ cornerSet A e) : e * a = a ∧ a * e = a := by
  have hee : e * e = e := he.isIdempotentElem.eq
  have ha' : e * a * e = a := ha
  refine ⟨?_, ?_⟩
  · calc e * a = e * (e * a * e) := by rw [ha']
      _ = e * e * a * e := by noncomm_ring
      _ = a := by rw [hee, ha']
  · calc a * e = e * a * e * e := by rw [ha']
      _ = e * a * (e * e) := by noncomm_ring
      _ = a := by rw [hee, ha']

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 4: the
corner `e𝒜e` is norm closed and ultraweakly closed. -/
theorem corner_vna_basic_4 [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) :
    IsClosed (cornerSet A e) ∧ IsClosed[ultraweak A] (cornerSet A e) := by
  have hstar : star e = e := he.isSelfAdjoint.star_eq
  refine ⟨isClosed_eq (by fun_prop) continuous_id, ?_⟩
  -- `e𝒜e` is cut out by the np-functionals: `eae = a` iff `ω(eae) = ω(a)`
  -- for every np-functional `ω` (the np-functionals are separating, 44XI),
  -- and `a ↦ ω(eae)` is again an np-functional (`conjNP`), hence
  -- ultraweakly continuous.
  have hset : cornerSet A e =
      ⋂ ω : NPFunctional A, (fun a : A => (conjNP e ω) a - ω a) ⁻¹' {0} := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      conjNP_apply, hstar]
    constructor
    · intro ha ω
      rw [show e * a * e = a from ha, sub_self]
    · intro h
      have h0 : e * a * e - a = 0 :=
        np_separating _ fun ω => by rw [npFunctional_sub]; exact h ω
      exact sub_eq_zero.mp h0
  rw [hset]
  letI : TopologicalSpace A := ultraweak A
  refine isClosed_iInter fun ω => ?_
  exact isClosed_singleton.preimage
    ((continuous_ultraweak_npFunctional (conjNP e ω)).sub
      (continuous_ultraweak_npFunctional ω))

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 5,
coherence: the (asserted) C*-algebra structure of `Corner A e` is given by
the operations and norm of `A`, with `e` as unit. -/
theorem corner_vna_basic_5 (e : A) [Fact (IsStarProjection e)]
    (a b : Corner A e) (z : ℂ) :
    (a + b).val = a.val + b.val ∧ (a * b).val = a.val * b.val ∧
      (z • a).val = z • a.val ∧ (star a).val = star a.val ∧
      (1 : Corner A e).val = e ∧ (0 : Corner A e).val = 0 ∧
      ‖a‖ = ‖a.val‖ ∧ (a ≤ b ↔ a.val ≤ b.val) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 6: the
supremum in `A` of a bounded directed set of self-adjoint elements of the
corner `e𝒜e` lies again in `e𝒜e` (and is the supremum there). -/
theorem corner_vna_basic_6 [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) (D : Set (selfAdjoint A))
    (hD : ∀ d ∈ D, (d : A) ∈ cornerSet A e)
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    (dirSup D h : A) ∈ cornerSet A e :=
  -- `e(·)e` is normal (44VIII), so it sends `⋁D` to `⋁ e D e = ⋁ D`
  isLUB_mem_cornerSet e he D (dirSup D h) hD h.1 h.2.1 (isLUB_dirSup D h)

namespace Corner

variable {e : A} [Fact (IsStarProjection e)]

/-- `Corner.val` as a non-unital ∗-algebra homomorphism. -/
def valStarHom : Corner A e →⋆ₙₐ[ℂ] A where
  toFun := Corner.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem valStarHom_apply (a : Corner A e) : valStarHom a = a.val := rfl

theorem map_eq_mapₙₐ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (Corner A e)) :
    M.map (Corner.val) = CStarMatrix.mapₙₐ (valStarHom (e := e)) M := by
  ext i j; rfl

theorem map_val_injective (k : ℕ) :
    Function.Injective
      (fun M : CStarMatrix (Fin k) (Fin k) (Corner A e) => M.map (Corner.val)) :=
  CStarMatrix.map_injective val_injective

/-- The diagonal matrix `diag(e, …, e)`, a projection of `M_k(A)`. -/
def diagProj (e : A) (k : ℕ) : CStarMatrix (Fin k) (Fin k) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun _ => e)

theorem diagProj_apply (e : A) (k : ℕ) (i j : Fin k) :
    diagProj e k i j = if i = j then e else 0 := rfl

theorem isStarProjection_diagProj (k : ℕ) :
    IsStarProjection (diagProj e k) := by
  have hsa : star e = e := (proj e).isSelfAdjoint.star_eq
  have hee : e * e = e := (proj e).isIdempotentElem.eq
  constructor
  · show diagProj e k * diagProj e k = diagProj e k
    ext i j
    rw [CStarMatrix.mul_apply, diagProj_apply]
    rw [Finset.sum_eq_single i]
    · rw [diagProj_apply, diagProj_apply, if_pos rfl]
      by_cases h : i = j
      · subst h; simp [hee]
      · rw [if_neg h, mul_zero]
    · intro b _ hb
      rw [diagProj_apply, if_neg (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · show star (diagProj e k) = diagProj e k
    ext i j
    rw [CStarMatrix.star_apply, diagProj_apply, diagProj_apply]
    by_cases h : i = j
    · subst h; simp [hsa]
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem diagProj_conj (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (Corner A e)) :
    diagProj e k * (M.map Corner.val) * diagProj e k = M.map Corner.val := by
  ext i j
  rw [CStarMatrix.mul_apply, CStarMatrix.map_apply]
  have h₁ : ∀ l, (diagProj e k * M.map Corner.val) i l = e * (M i l).val := by
    intro l
    rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
    · rw [diagProj_apply, if_pos rfl, CStarMatrix.map_apply]
    · intro b _ hb
      rw [diagProj_apply, if_neg (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp only [h₁]
  rw [Finset.sum_eq_single j]
  · rw [diagProj_apply, if_pos rfl]
    exact (M i j).property
  · intro b _ hb
    rw [diagProj_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Positivity in `M_k(e𝒜e)` is positivity in `M_k(𝒜)`. -/
theorem nonneg_map_val_iff (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (Corner A e)) :
    0 ≤ M.map Corner.val ↔ 0 ≤ M := by
  letI : NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin k) (Fin k) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  letI : NonnegSpectrumClass ℝ (CStarMatrix (Fin k) (Fin k) A) :=
    CStarAlgebra.instNonnegSpectrumClass
  letI : NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin k) (Fin k) (Corner A e)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  letI : NonnegSpectrumClass ℝ (CStarMatrix (Fin k) (Fin k) (Corner A e)) :=
    CStarAlgebra.instNonnegSpectrumClass
  constructor
  · intro h
    -- `√(M.map val)` again has entries in the corner
    set Q := CFC.sqrt (M.map Corner.val) with hQ
    have hQmem : diagProj e k * Q * diagProj e k = Q := by
      haveI : Fact (IsStarProjection (diagProj e k)) :=
        ⟨isStarProjection_diagProj k⟩
      exact Corner.sqrt_mem (M.map Corner.val) h (diagProj_conj k M)
    have hentry : ∀ i j, e * Q i j * e = Q i j := by
      intro i j
      have := congrFun (congrFun hQmem i) j
      rw [CStarMatrix.mul_apply] at this
      have h₁ : ∀ l, (diagProj e k * Q) i l = e * Q i l := by
        intro l
        rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
        · rw [diagProj_apply, if_pos rfl]
        · intro b _ hb
          rw [diagProj_apply, if_neg (Ne.symm hb), zero_mul]
        · intro hc; exact absurd (Finset.mem_univ i) hc
      simp only [h₁] at this
      rw [Finset.sum_eq_single j] at this
      · rwa [diagProj_apply, if_pos rfl] at this
      · intro b _ hb
        rw [diagProj_apply, if_neg hb, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ j) hc
    set N : CStarMatrix (Fin k) (Fin k) (Corner A e) :=
      CStarMatrix.ofMatrix (Matrix.of fun i j => (⟨Q i j, hentry i j⟩ : Corner A e))
      with hN
    have hNmap : N.map Corner.val = Q := by ext i j; rfl
    have hMN : M = star N * N := by
      refine map_val_injective k ?_
      show M.map Corner.val = (star N * N).map Corner.val
      rw [map_eq_mapₙₐ (M := star N * N), map_mul, map_star, ← map_eq_mapₙₐ, hNmap]
      rw [hQ]
      have hsa : IsSelfAdjoint (CFC.sqrt (M.map Corner.val)) :=
        IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
      rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self _ h]
    rw [hMN]
    exact star_mul_self_nonneg N
  · intro h
    set N := CFC.sqrt M with hN
    have hsa : IsSelfAdjoint N := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
    have hMN : M = star N * N := by
      rw [hsa.star_eq, hN, CFC.sqrt_mul_sqrt_self M h]
    rw [hMN, map_eq_mapₙₐ, map_mul, map_star, ← map_eq_mapₙₐ]
    exact star_mul_self_nonneg _

/-- `e ≤ 1` for a projection `e`. -/
theorem le_one : e ≤ 1 := by
  have hee : e * e = e := (proj e).isIdempotentElem.eq
  have hse : star e = e := (proj e).isSelfAdjoint.star_eq
  have h : star (1 - e) * (1 - e) = 1 - e := by
    rw [star_sub, star_one, hse]
    noncomm_ring [hee]
  have := star_mul_self_nonneg (1 - e)
  rw [h] at this
  exact sub_nonneg.mp this

/-- If the image under `val` of `T ⊆ e𝒜e` has least upper bound `x.val` in
`𝒜`, then `x` is a least upper bound of `T` in `e𝒜e`. -/
theorem isLUB_of_isLUB_image_val {T : Set (Corner A e)} {x : Corner A e}
    (h : IsLUB (Corner.val '' T) x.val) : IsLUB T x := by
  constructor
  · intro t ht
    exact h.1 ⟨t, ht, rfl⟩
  · intro u hu
    refine h.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hu ht

end Corner

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 7: the
inclusion `e𝒜e → 𝒜` is an ncpsu-map (existence lemma; `cornerIncl` is
obtained from it by choice). -/
theorem exists_cornerIncl [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] :
    ∃ f : NCPSUMap (Corner A e) A, ∀ a : Corner A e, f.toNCPMap a = a.val := by

  refine ⟨{ toNCPMap :=
              { toCompletelyPositiveMap :=
                  { toFun := fun a => a.val
                    map_add' := fun _ _ => rfl
                    map_smul' := fun _ _ => rfl
                    map_cstarMatrix_nonneg' := fun k M hM => ?_ }
                preservesDirSups' := ?_ }
            subunital' := ?_ }, fun _ => rfl⟩
  · exact (Corner.nonneg_map_val_iff k M).mpr hM
  · intro D s hne hdir hlub
    have h1 := Corner.isLUB_saMap_image hne hdir hlub
    have h2 := isLUB_coe_of_isLUB (hne.image _) h1
    rw [← Set.image_comp] at h2
    exact h2
  · show (1 : Corner A e).val ≤ (1 : A)
    exact Corner.le_one


/-- The inclusion `e𝒜e → 𝒜` as an ncpsu-map (94II part 7). -/
noncomputable def cornerIncl [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] :
    NCPSUMap (Corner A e) A := (exists_cornerIncl e).choose

theorem cornerIncl_apply [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (a : Corner A e) :
    (cornerIncl e).toNCPMap a = a.val := (exists_cornerIncl e).choose_spec a

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 8: the
restriction of an np-functional on `𝒜` to the corner `e𝒜e` is an
np-functional. -/
theorem corner_vna_basic_8 [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (ω : NPFunctional A) :
    ∃ ω' : NPFunctional (Corner A e), ∀ a : Corner A e, ω' a = ω a.val :=
  ⟨Corner.restrictNP e ω, fun _ => rfl⟩

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 9: the
projection `a ↦ e·a·e : 𝒜 → e𝒜e` onto a corner is an ncpu-map
(existence lemma; `cornerProjMap` is obtained from it by choice). -/
theorem exists_cornerProjMap [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] :
    ∃ π : NCPUMap A (Corner A e), ∀ a : A, (π.toNCPMap a).val = e * a * e := by

  have hee : e * e = e := (Corner.proj e).isIdempotentElem.eq
  have hse : star e = e := (Corner.proj e).isSelfAdjoint.star_eq
  have hmem : ∀ a : A, e * (e * a * e) * e = e * a * e := by
    intro a
    calc e * (e * a * e) * e = (e * e) * a * (e * e) := by noncomm_ring
      _ = e * a * e := by rw [hee]
  refine ⟨{ toNCPMap :=
              { toCompletelyPositiveMap :=
                  { toFun := fun a => ⟨e * a * e, hmem a⟩
                    map_add' := fun x y => Corner.val_injective (by
                      show e * (x + y) * e = e * x * e + e * y * e
                      noncomm_ring)
                    map_smul' := fun c x => Corner.val_injective (by
                      simp [mul_smul_comm, smul_mul_assoc])
                    map_cstarMatrix_nonneg' := fun k M hM => ?_ }
                preservesDirSups' := ?_ }
            unital' := ?_ }, fun _ => rfl⟩
  · refine (Corner.nonneg_map_val_iff k _).mp ?_
    have hmap : (CStarMatrix.map M fun a => (⟨e * a * e, hmem a⟩ : Corner A e)).map
        Corner.val = star (Corner.diagProj e k) * M * Corner.diagProj e k := by
      ext i j
      rw [CStarMatrix.map_apply, CStarMatrix.map_apply, CStarMatrix.mul_apply]
      have h₁ : ∀ l, (star (Corner.diagProj e k) * M) i l = e * M i l := by
        intro l
        rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
        · rw [CStarMatrix.star_apply, Corner.diagProj_apply, if_pos rfl, hse]
        · intro b _ hb
          rw [CStarMatrix.star_apply, Corner.diagProj_apply, if_neg hb, star_zero,
            zero_mul]
        · intro hc; exact absurd (Finset.mem_univ i) hc
      simp only [h₁]
      rw [Finset.sum_eq_single j]
      · rw [Corner.diagProj_apply, if_pos rfl]
      · intro b _ hb
        rw [Corner.diagProj_apply, if_neg hb, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ j) hc
    have key : (0 : CStarMatrix (Fin k) (Fin k) A) ≤
        star (Corner.diagProj e k) * M * Corner.diagProj e k :=
      star_left_conjugate_nonneg hM (Corner.diagProj e k)
    rw [← hmap] at key
    exact key
  · intro D s hne hdir hlub
    refine Corner.isLUB_of_isLUB_image_val ?_
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
    have hs : s = dirSup D h := hlub.unique (isLUB_dirSup D h)
    have hnat := ad_normal e D h
    rw [hse, ← hs] at hnat
    rw [← Set.image_comp]
    exact hnat
  · refine Corner.val_injective ?_
    show e * 1 * e = e
    rw [mul_one, hee]


/-- The projection `a ↦ e·a·e : 𝒜 → e𝒜e` onto a corner as an ncpu-map
(94II part 9). -/
noncomputable def cornerProjMap [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] :
    NCPUMap A (Corner A e) := (exists_cornerProjMap e).choose

theorem cornerProjMap_apply [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (a : A) :
    ((cornerProjMap e).toNCPMap a).val = e * a * e :=
  (exists_cornerProjMap e).choose_spec a

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 10: every
np-functional `ω'` on `e𝒜e` is the restriction of the np-functional
`ω'(e(·)e)` on `𝒜`. -/
theorem corner_vna_basic_10 [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (ω' : NPFunctional (Corner A e)) :
    ∃ ω : NPFunctional A,
      (∀ a : A, ω a = ω' ((cornerProjMap e).toNCPMap a)) ∧
      (∀ a : Corner A e, ω' a = ω a.val) := by
  set π := (cornerProjMap (A := A) e).toNCPMap with hπ
  refine ⟨compNP (PositiveLinearMap.ofClass π.toCompletelyPositiveMap)
      π.preservesDirSups' ω', fun _ => rfl, ?_⟩
  intro a
  show ω' a = ω' (π a.val)
  congr 1
  refine Corner.val_injective ?_
  rw [hπ, cornerProjMap_apply]
  exact a.property.symm

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 10
(continued): the ultraweak and ultrastrong topologies of the corner
`e𝒜e` coincide with those induced from `𝒜`. -/
theorem corner_vna_basic_10' [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] :
    ultraweak (Corner A e) =
        TopologicalSpace.induced (Corner.val) (ultraweak A) ∧
      ultrastrong (Corner A e) =
        TopologicalSpace.induced (Corner.val) (ultrastrong A) := sorry

/-- **94III** (`ad-ncp`, proc.tex:247, Exercise), part 1: if
`a* p a ≤ q` for projections `p, q`, then `a* b a ∈ q𝒜q` for every
`b ∈ p𝒜p`. -/
theorem ad_ncp_1 [VonNeumannAlgebra A] (a p q : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : star a * p * a ≤ q) (b : A) (hb : b ∈ cornerSet A p) :
    star a * b * a ∈ cornerSet A q := by
  have hb' : p * b * p = b := hb
  have hrp : IsStarProjection (1 - q) := hq.one_sub
  -- step 1: `p a q^⊥ = 0`
  have hconj := star_left_conjugate_le_conjugate h (1 - q)
  rw [hrp.isSelfAdjoint.star_eq,
    show (1 - q) * q * (1 - q) = 0 by
      rw [sub_mul, one_mul, hq.isIdempotentElem.eq, sub_self, zero_mul]] at hconj
  have hnn : (0 : A) ≤ (1 - q) * (star a * p * a) * (1 - q) := by
    have h0 := star_left_conjugate_nonneg hp.nonneg (a * (1 - q))
    rw [star_mul, hrp.isSelfAdjoint.star_eq] at h0
    calc (0 : A) ≤ (1 - q) * star a * p * (a * (1 - q)) := h0
      _ = (1 - q) * (star a * p * a) * (1 - q) := by noncomm_ring
  have hzero : (1 - q) * (star a * p * a) * (1 - q) = 0 := le_antisymm hconj hnn
  have hpar : p * a * (1 - q) = 0 := by
    refine CStarRing.star_mul_self_eq_zero_iff _ |>.mp ?_
    calc star (p * a * (1 - q)) * (p * a * (1 - q))
        = (1 - q) * star a * (p * p) * (a * (1 - q)) := by
          rw [star_mul, star_mul, hrp.isSelfAdjoint.star_eq,
            hp.isSelfAdjoint.star_eq]; noncomm_ring
      _ = (1 - q) * (star a * p * a) * (1 - q) := by
          rw [hp.isIdempotentElem.eq]; noncomm_ring
      _ = 0 := hzero
  -- step 2: `pa = paq` and `a*p = q a*p`, whence `a* b a` sits in `q𝒜q`
  have hpa : p * a = p * a * q := by
    rw [mul_sub, mul_one, sub_eq_zero] at hpar
    exact hpar
  have hap : star a * p = q * (star a * p) := by
    have hs := congrArg star hpa
    calc star a * p = star (p * a) := by
          rw [star_mul, hp.isSelfAdjoint.star_eq]
      _ = star (p * a * q) := hs
      _ = q * (star a * p) := by
          rw [star_mul, star_mul, hq.isSelfAdjoint.star_eq,
            hp.isSelfAdjoint.star_eq]
  show q * (star a * b * a) * q = star a * b * a
  symm
  calc star a * b * a = star a * (p * b * p) * a := by rw [hb']
    _ = (star a * p) * b * (p * a) := by noncomm_ring
    _ = (q * (star a * p)) * b * (p * a * q) := by rw [← hap, ← hpa]
    _ = q * (star a * (p * b * p) * a) * q := by noncomm_ring
    _ = q * (star a * b * a) * q := by rw [hb']

/-- **94III** (`ad-ncp`, proc.tex:247, Exercise), part 2: if
`a* p a ≤ q`, then `a*(·)a` gives an ncp-map `p𝒜p → q𝒜q` (existence
lemma; `adNCP` is obtained from it by choice). -/
theorem exists_adNCP [VonNeumannAlgebra A] (a p q : A)
    [Fact (IsStarProjection p)] [Fact (IsStarProjection q)]
    (h : star a * p * a ≤ q) :
    ∃ f : NCPMap (Corner A p) (Corner A q),
      ∀ b : Corner A p, (f b).val = star a * b.val * a := by
  have hmem : ∀ b : Corner A p, q * (star a * b.val * a) * q = star a * b.val * a :=
    fun b => ad_ncp_1 a p q (Corner.proj p) (Corner.proj q) h b.val b.property
  refine ⟨{ toCompletelyPositiveMap :=
              { toFun := fun b => ⟨star a * b.val * a, hmem b⟩
                map_add' := fun x y => Corner.val_injective (by
                  show star a * (x.val + y.val) * a
                      = star a * x.val * a + star a * y.val * a
                  noncomm_ring)
                map_smul' := fun c x => Corner.val_injective (by
                  show star a * (c • x.val) * a = c • (star a * x.val * a)
                  simp [mul_smul_comm, smul_mul_assoc])
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · refine (Corner.nonneg_map_val_iff k _).mp ?_
    set D : CStarMatrix (Fin k) (Fin k) A :=
      CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a) with hD
    have hDapp : ∀ i j, D i j = if i = j then a else 0 := fun i j => rfl
    have hkey : (CStarMatrix.map M fun b : Corner A p =>
        (⟨star a * b.val * a, hmem b⟩ : Corner A q)).map Corner.val
        = star D * (M.map Corner.val) * D := by
      ext i j
      rw [CStarMatrix.map_apply, CStarMatrix.map_apply, CStarMatrix.mul_apply]
      have h₁ : ∀ l, (star D * M.map Corner.val) i l = star a * (M i l).val := by
        intro l
        rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
        · rw [CStarMatrix.star_apply, hDapp, if_pos rfl, CStarMatrix.map_apply]
        · intro b _ hb
          rw [CStarMatrix.star_apply, hDapp, if_neg hb, star_zero, zero_mul]
        · intro hc; exact absurd (Finset.mem_univ i) hc
      simp only [h₁]
      rw [Finset.sum_eq_single j]
      · rw [hDapp, if_pos rfl]
      · intro b _ hb
        rw [hDapp, if_neg hb, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ j) hc
    have hMval : (0 : CStarMatrix (Fin k) (Fin k) A) ≤ M.map Corner.val :=
      (Corner.nonneg_map_val_iff k M).mpr hM
    have key : (0 : CStarMatrix (Fin k) (Fin k) A)
        ≤ star D * (M.map Corner.val) * D := star_left_conjugate_nonneg hMval D
    rw [← hkey] at key
    exact key
  · intro D s hne hdir hlub
    refine Corner.isLUB_of_isLUB_image_val ?_
    have h1 := Corner.isLUB_saMap_image hne hdir hlub
    have hbdd : BddAbove (Corner.saMap '' D) := ⟨Corner.saMap s, h1.1⟩
    have hh : (Corner.saMap '' D).Nonempty ∧
        DirectedOn (· ≤ ·) (Corner.saMap '' D) ∧ BddAbove (Corner.saMap '' D) := by
      refine ⟨hne.image _, ?_, hbdd⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
      exact ⟨Corner.saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩
    have hs : Corner.saMap s = dirSup _ hh := h1.unique (isLUB_dirSup _ hh)
    have hnat := ad_normal a (Corner.saMap '' D) hh
    rw [← hs] at hnat
    rw [← Set.image_comp] at hnat
    rw [← Set.image_comp]
    exact hnat

/-- The ncp-map `a*(·)a : p𝒜p → q𝒜q` of 94III part 2. -/
noncomputable def adNCP [VonNeumannAlgebra A] (a p q : A)
    [Fact (IsStarProjection p)] [Fact (IsStarProjection q)]
    (h : star a * p * a ≤ q) : NCPMap (Corner A p) (Corner A q) :=
  (exists_adNCP a p q h).choose

/-- Infrastructure (used for 95II and 103II): for `a·q = a` the map
`a*(·)a : 𝒜 → q𝒜q` is an ncp-map; by choice `adToCorner`. -/
theorem exists_adToCorner [VonNeumannAlgebra A] (a q : A)
    [Fact (IsStarProjection q)] (h : a * q = a) :
    ∃ f : NCPMap A (Corner A q), ∀ b : A, (f b).val = star a * b * a := by
  have hsq : star q = q := (Corner.proj q).isSelfAdjoint.star_eq
  have hqa : q * star a = star a := by
    have := congrArg star h
    rwa [star_mul, hsq] at this
  have hmem : ∀ b : A, q * (star a * b * a) * q = star a * b * a := by
    intro b
    calc q * (star a * b * a) * q = (q * star a) * b * (a * q) := by noncomm_ring
      _ = star a * b * a := by rw [hqa, h]
  refine ⟨{ toCompletelyPositiveMap :=
              { toFun := fun b => ⟨star a * b * a, hmem b⟩
                map_add' := fun x y => Corner.val_injective (by
                  show star a * (x + y) * a = star a * x * a + star a * y * a
                  noncomm_ring)
                map_smul' := fun c x => Corner.val_injective (by
                  show star a * (c • x) * a = c • (star a * x * a)
                  simp [mul_smul_comm, smul_mul_assoc])
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · refine (Corner.nonneg_map_val_iff k _).mp ?_
    set D : CStarMatrix (Fin k) (Fin k) A :=
      CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a) with hD
    have hDapp : ∀ i j, D i j = if i = j then a else 0 := fun i j => rfl
    have hkey : (CStarMatrix.map M fun b => (⟨star a * b * a, hmem b⟩ : Corner A q)).map
        Corner.val = star D * M * D := by
      ext i j
      rw [CStarMatrix.map_apply, CStarMatrix.map_apply, CStarMatrix.mul_apply]
      have h₁ : ∀ l, (star D * M) i l = star a * M i l := by
        intro l
        rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
        · rw [CStarMatrix.star_apply, hDapp, if_pos rfl]
        · intro b _ hb
          rw [CStarMatrix.star_apply, hDapp, if_neg hb, star_zero, zero_mul]
        · intro hc; exact absurd (Finset.mem_univ i) hc
      simp only [h₁]
      rw [Finset.sum_eq_single j]
      · rw [hDapp, if_pos rfl]
      · intro b _ hb
        rw [hDapp, if_neg hb, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ j) hc
    have key : (0 : CStarMatrix (Fin k) (Fin k) A) ≤ star D * M * D :=
      star_left_conjugate_nonneg hM D
    rw [← hkey] at key
    exact key
  · intro D s hne hdir hlub
    refine Corner.isLUB_of_isLUB_image_val ?_
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have hh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
    have hs : s = dirSup D hh := hlub.unique (isLUB_dirSup D hh)
    have hnat := ad_normal a D hh
    rw [← hs] at hnat
    rw [← Set.image_comp]
    exact hnat

/-- The ncp-map `a*(·)a : 𝒜 → q𝒜q` (for `a·q = a`). -/
noncomputable def adToCorner [VonNeumannAlgebra A] (a q : A)
    [Fact (IsStarProjection q)] (h : a * q = a) :
    NCPMap A (Corner A q) := (exists_adToCorner a q h).choose

/-- Infrastructure (used for 101VII and 103II): `a*(·)a : 𝒜 → 𝒜` is an
ncp-map; by choice `adSelf`. -/
theorem exists_adSelf [VonNeumannAlgebra A] (a : A) :
    ∃ f : NCPMap A A, ∀ b : A, f b = star a * b * a := by
  classical
  refine ⟨{ toCompletelyPositiveMap :=
              { toFun := fun b => star a * b * a
                map_add' := fun x y => by noncomm_ring
                map_smul' := fun c x => by
                  simp [mul_smul_comm, smul_mul_assoc]
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · -- `M ↦ (a* Mᵢⱼ a)ᵢⱼ` is conjugation by the diagonal matrix `diag(a)`
    set D : CStarMatrix (Fin k) (Fin k) A :=
      CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a) with hD
    have hDapp : ∀ i j, D i j = if i = j then a else 0 := fun i j => rfl
    have hkey : M.map (fun b => star a * b * a) = star D * M * D := by
      ext i j
      rw [CStarMatrix.map_apply, CStarMatrix.mul_apply]
      have h₁ : ∀ l, (star D * M) i l = star a * M i l := by
        intro l
        rw [CStarMatrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · rw [CStarMatrix.star_apply, hDapp, if_pos rfl]
        · intro b _ hb
          rw [CStarMatrix.star_apply, hDapp, if_neg hb, star_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
      simp only [h₁]
      rw [Finset.sum_eq_single j]
      · rw [hDapp, if_pos rfl]
      · intro b _ hb
        rw [hDapp, if_neg hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hgoal : (0 : CStarMatrix (Fin k) (Fin k) A) ≤ star D * M * D :=
      star_left_conjugate_nonneg hM D
    rw [← hkey] at hgoal
    exact hgoal
  · -- normality is 44VIII (`ad_normal`)
    intro D s hne hdir hlub
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
    have hs : s = dirSup D h := hlub.unique (isLUB_dirSup D h)
    have := ad_normal a D h
    rw [← hs] at this
    exact this

/-- The ncp-map `a*(·)a : 𝒜 → 𝒜`. -/
noncomputable def adSelf [VonNeumannAlgebra A] (a : A) : NCPMap A A :=
  (exists_adSelf a).choose

theorem adSelf_apply [VonNeumannAlgebra A] (a b : A) :
    adSelf a b = star a * b * a := (exists_adSelf a).choose_spec b

/-! ## Parsec 950: corners (universal property) -/

/-- **95I** (`corner`, proc.tex:263, Definition): a **corner** of an effect
`p` of a von Neumann algebra `A` is an ncp-map `π : A → C` with
`π(p^⊥) = 0` which is initial among such maps: every ncp-map `f : A → B`
with `f(p^⊥) = 0` factors as `f = g ∘ π` for a unique ncp-map `g`.
(Convention of 95I: a *corner* simpliciter is a *unital* corner; see
`IsCornerMap`.) -/
structure IsCornerOf (p : A) (π : NCPMap A C) : Prop where
  map_perp : π (1 - p) = 0
  universal : ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : NCPMap A B),
    f (1 - p) = 0 → ∃! g : NCPMap C B, ∀ a : A, f a = g (π a)

/-- **95I** (`corner`, proc.tex:263, Definition), convention: a **corner**
(map) is a *unital* ncp-map which is a corner of some effect. -/
def IsCornerMap (π : NCPMap A C) : Prop :=
  π 1 = 1 ∧ ∃ p ∈ effects A, IsCornerOf p π

/-- **95II** (`prop-corner`, proc.tex:288, Proposition): given an effect
`p` and a partial isometry `u` with `⌊p⌋ = u u*`, the map
`π(a) = u* a u : 𝒜 → u*u 𝒜 u*u` is a corner of `p`. -/
theorem prop_corner [VonNeumannAlgebra A] (p u : A) (hp : p ∈ effects A)
    (hu : IsPartialIsometry A u) [Fact (IsStarProjection (star u * u))]
    (h : floor p = u * star u)
    (h' : u * (star u * u) = u) :
    IsCornerOf p (adToCorner u (star u * u) h') := by
  -- The author's proof (proc.tex:290), with one substitution: the last step
  -- ("`f(a) = f(uu* a uu*)` by `cp-comprehension`") is run through
  -- `carrier_fundamental` (63VI) instead of `cp_comprehension` (63IV), which
  -- is still `sorry` in `A/VN`; the two say the same thing here, since
  -- `f((uu*)^⊥) = 0` makes `⌈f⌉ ≤ uu*`.
  have hpi : ∀ b : A, ((adToCorner u (star u * u) h') b).val = star u * b * u :=
    (exists_adToCorner u (star u * u) h').choose_spec
  have hq5 : star u * u * star u = star u :=
    ((partial_isometry_equivalents u).out 0 4).mp hu
  have hqproj : IsStarProjection (u * star u) :=
    ((partial_isometry_equivalents u).out 0 3).mp hu
  have h1p : (0 : A) ≤ 1 - p := sub_nonneg.mpr hp.2
  have hceil1p : ceil (1 - p) = 1 - u * star u := by
    rw [← (ceil_floor_basic_1 p hp).2, h]
  -- `u*(uu*)^⊥u = 0`, so `⌈u* p^⊥ u⌉ = ⌈u*⌈p^⊥⌉u⌉ = 0` and `u* p^⊥ u = 0`
  have key0 : star u * (1 - u * star u) * u = 0 := by
    have e : star u * (1 - u * star u) * u = star u * u - (star u * u * star u) * u := by
      noncomm_ring
    rw [e, hq5, sub_self]
  have hval : star u * (1 - p) * u = 0 := by
    refine (ceil_basic_3 _ (star_left_conjugate_nonneg h1p u)).mpr ?_
    rw [ceil_fundamental_1 u (1 - p) h1p, hceil1p, key0, ceil_zero]
  refine ⟨Corner.val_injective (by rw [hpi]; exact hval), ?_⟩
  intro B _ _ _ _ f hf0
  set F : A →ₚ[ℂ] B := PositiveLinearMap.ofClass f.toCompletelyPositiveMap with hF
  have hFapp : ∀ a : A, F a = f a := fun _ => rfl
  have hFn : PreservesDirSups ⇑F := f.preservesDirSups'
  have hFnn : ∀ a : A, 0 ≤ a → (0 : B) ≤ F a := by
    intro a ha
    have hz : (F (0 : A) : B) = 0 := map_zero F
    have h0 : (F (0 : A) : B) ≤ F a := F.monotone ha
    rwa [hz] at h0
  -- `⌈f((uu*)^⊥)⌉ = ⌈f(⌈p^⊥⌉)⌉ = ⌈f(p^⊥)⌉ = 0`, so `f` kills `(uu*)^⊥`
  have hfq : F (1 - u * star u) = 0 := by
    have h1 : ceil (F (1 - p)) = ceil (F (ceil (1 - p))) := ncp_ceil F hFn (1 - p) h1p
    rw [hFapp (1 - p), hf0, ceil_zero, hceil1p] at h1
    exact (ceil_basic_3 _ (hFnn _ hqproj.one_sub.nonneg)).mpr h1.symm
  -- hence `⌈f⌉ ≤ uu*`, and therefore `f(a) = f(uu* a uu*)`
  have hcle : carrier F hFn ≤ u * star u := (carrier_spec F hFn).2.2 _ hqproj hfq
  have hcproj : IsStarProjection (carrier F hFn) := (carrier_spec F hFn).1
  have hcq : carrier F hFn * (u * star u) = carrier F hFn :=
    ((projection_below_effect (u * star u) (carrier F hFn)
      ⟨hqproj.nonneg, hqproj.le_one⟩ hcproj).out 0 7).mp hcle
  have hqc : (u * star u) * carrier F hFn = carrier F hFn := by
    have hs := congrArg star hcq
    rwa [star_mul, hqproj.isSelfAdjoint.star_eq, hcproj.isSelfAdjoint.star_eq] at hs
  have hconj : ∀ a : A, F a = F (u * star u * a * (u * star u)) := by
    intro a
    have e1 := (carrier_fundamental F hFn a).2.2
    have e2 := (carrier_fundamental F hFn (u * star u * a * (u * star u))).2.2
    rw [e2, show carrier F hFn * (u * star u * a * (u * star u)) * carrier F hFn
        = (carrier F hFn * (u * star u)) * a * ((u * star u) * carrier F hFn) by
      noncomm_ring, hcq, hqc, ← e1]
  -- existence: `g = f ∘ ζ` with `ζ(a) = u a u*`; uniqueness: `π` is surjective
  set zeta : NCPMap (Corner A (star u * u)) A :=
    ncpComp (adSelf (star u)) (cornerIncl (star u * u)).toNCPMap with hzetadef
  have hzeta : ∀ b : Corner A (star u * u),
      zeta b = star (star u) * b.val * star u := by
    intro b
    rw [hzetadef, ncpComp_apply, cornerIncl_apply, adSelf_apply]
  have hfac : ∀ a : A, f a = ncpComp f zeta ((adToCorner u (star u * u) h') a) := by
    intro a
    rw [ncpComp_apply, hzeta, hpi, star_star,
      show u * (star u * a * u) * star u = u * star u * a * (u * star u) by noncomm_ring]
    exact hconj a
  refine ⟨ncpComp f zeta, hfac, fun g hg => ?_⟩
  refine DFunLike.ext _ _ fun b => ?_
  have hsurj : (adToCorner u (star u * u) h') (u * b.val * star u) = b := by
    refine Corner.val_injective ?_
    rw [hpi]
    calc star u * (u * b.val * star u) * u
        = (star u * u) * b.val * (star u * u) := by noncomm_ring
      _ = b.val := b.property
  calc g b = g ((adToCorner u (star u * u) h') (u * b.val * star u)) := by rw [hsurj]
    _ = f (u * b.val * star u) := (hg _).symm
    _ = ncpComp f zeta ((adToCorner u (star u * u) h') (u * b.val * star u)) := hfac _
    _ = ncpComp f zeta b := by rw [hsurj]

/-! ## Parsec 960: filters -/

/-- **96I** (`filter`, proc.tex:336, Definition): a **filter** is an
ncp-map `c : C → A` between von Neumann algebras such that every ncp-map
`f : B → A` with `f(1) ≤ c(1)` factors as `f = c ∘ g` for a unique
ncp-map `g : B → C`.  We say `c` is a filter *for* `c(1)`. -/
structure IsFilter (c : NCPMap C A) : Prop where
  universal : ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : NCPMap B A),
    f 1 ≤ c 1 → ∃! g : NCPMap B C, ∀ b : B, f b = c (g b)

/-- **96III** (`ncp-uwlim`, proc.tex:363, Lemma), main claim: the pointwise
ultraweak limit `g` of a net of positive linear maps `f_α : A → B` between
von Neumann algebras is positive. -/
theorem ncp_uwlim [VonNeumannAlgebra A] [VonNeumannAlgebra B] {ι : Type*}
    (l : Filter ι) [l.NeBot] (f : ι → (A →ₚ[ℂ] B)) (g : A →ₗ[ℂ] B)
    (hlim : ∀ a : A, UWTendsto (fun i => f i a) l (g a)) :
    ∀ a : A, 0 ≤ a → 0 ≤ g a := sorry

/-- **96III** (`ncp-uwlim`, proc.tex:363, Lemma), part 1: the limit is
completely positive provided the `f_α` are. -/
theorem ncp_uwlim_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B] {ι : Type*}
    (l : Filter ι) [l.NeBot] (f : ι → (A →ₚ[ℂ] B)) (g : A →ₗ[ℂ] B)
    (hlim : ∀ a : A, UWTendsto (fun i => f i a) l (g a))
    (hcp : ∀ i, Theses.A.CStar.IsCompletelyPositiveMap (f i).toLinearMap) :
    Theses.A.CStar.IsCompletelyPositiveMap g := sorry

/-- **96III** (`ncp-uwlim`, proc.tex:363, Lemma), part 2: the limit is
normal provided the `f_α` are normal and converge uniformly on `[0,1]_A`
(uniformly with respect to each np-functional of `B`). -/
theorem ncp_uwlim_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B] {ι : Type*}
    (l : Filter ι) [l.NeBot] (f : ι → (A →ₚ[ℂ] B)) (g : A →ₗ[ℂ] B)
    (hlim : ∀ a : A, UWTendsto (fun i => f i a) l (g a))
    (hn : ∀ i, PreservesDirSups ⇑(f i))
    (hunif : ∀ ω : NPFunctional B, ∀ ε > (0 : ℝ),
      ∀ᶠ i in l, ∀ p ∈ effects A, ‖ω (f i p) - ω (g p)‖ ≤ ε) :
    PreservesDirSups ⇑g := sorry

/-- Infrastructure for the filters of parsec 980: for a projection `e` and
any `a : A`, the map `b ↦ a* b a : e𝒜e → 𝒜` is an ncp-map. -/
theorem exists_adFromCorner [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (a : A) :
    ∃ f : NCPMap (Corner A e) A, ∀ b : Corner A e, f b = star a * b.val * a := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toFun := fun b => star a * b.val * a
                map_add' := fun x y => by
                  show star a * (x.val + y.val) * a
                      = star a * x.val * a + star a * y.val * a
                  noncomm_ring
                map_smul' := fun c x => by
                  show star a * (c • x.val) * a = c • (star a * x.val * a)
                  simp [mul_smul_comm, smul_mul_assoc]
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · -- `b ↦ a* b a` on the corner is `M ↦ star D (M.map val) D` for `D = diag a`
    set D : CStarMatrix (Fin k) (Fin k) A :=
      CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a) with hD
    have hDapp : ∀ i j, D i j = if i = j then a else 0 := fun i j => rfl
    have hkey : M.map (fun b : Corner A e => star a * b.val * a)
        = star D * (M.map Corner.val) * D := by
      ext i j
      rw [CStarMatrix.map_apply, CStarMatrix.mul_apply]
      have h₁ : ∀ l, (star D * M.map Corner.val) i l = star a * (M i l).val := by
        intro l
        rw [CStarMatrix.mul_apply, Finset.sum_eq_single i]
        · rw [CStarMatrix.star_apply, hDapp, if_pos rfl, CStarMatrix.map_apply]
        · intro b _ hb
          rw [CStarMatrix.star_apply, hDapp, if_neg hb, star_zero, zero_mul]
        · intro hc; exact absurd (Finset.mem_univ i) hc
      simp only [h₁]
      rw [Finset.sum_eq_single j]
      · rw [hDapp, if_pos rfl]
      · intro b _ hb
        rw [hDapp, if_neg hb, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ j) hc
    have hMval : (0 : CStarMatrix (Fin k) (Fin k) A) ≤ M.map Corner.val :=
      (Corner.nonneg_map_val_iff k M).mpr hM
    have key : (0 : CStarMatrix (Fin k) (Fin k) A)
        ≤ star D * (M.map Corner.val) * D := star_left_conjugate_nonneg hMval D
    rw [← hkey] at key
    exact key
  · -- normality: `val` is normal and `ad_a` is normal (44VIII)
    intro D s hne hdir hlub
    have h1 := Corner.isLUB_saMap_image hne hdir hlub
    have h2 : IsLUB (Subtype.val '' (Corner.saMap '' D))
        ((Corner.saMap s : selfAdjoint A) : A) :=
      isLUB_coe_of_isLUB (hne.image _) h1
    have hbdd : BddAbove (Corner.saMap '' D) := ⟨Corner.saMap s, h1.1⟩
    have h : (Corner.saMap '' D).Nonempty ∧ DirectedOn (· ≤ ·) (Corner.saMap '' D)
        ∧ BddAbove (Corner.saMap '' D) := by
      refine ⟨hne.image _, ?_, hbdd⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
      exact ⟨Corner.saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩
    have hs : Corner.saMap s = dirSup _ h := h1.unique (isLUB_dirSup _ h)
    have hnat := ad_normal a (Corner.saMap '' D) h
    rw [← hs] at hnat
    rw [← Set.image_comp] at hnat
    exact hnat

/-- **96V** (`canonical-filter`, proc.tex:414, Proposition),
well-definedness: for `d ∈ 𝒜` the assignment `a ↦ d* a d` gives an
ncp-map `⌈d⌉ᵣ𝒜⌈d⌉ᵣ → 𝒜`; by choice `canonicalFilter`. -/
theorem exists_canonicalFilter [VonNeumannAlgebra A] (d : A) :
    ∃ c : NCPMap (Corner A (suppProj d)) A,
      ∀ a : Corner A (suppProj d), c a = star d * a.val * d :=
  exists_adFromCorner (suppProj d) d

/-- The map `d*(·)d : ⌈d⌉ᵣ𝒜⌈d⌉ᵣ → 𝒜` of 96V. -/
noncomputable def canonicalFilter [VonNeumannAlgebra A] (d : A) :
    NCPMap (Corner A (suppProj d)) A := (exists_canonicalFilter d).choose

theorem canonicalFilter_apply [VonNeumannAlgebra A] (d : A)
    (a : Corner A (suppProj d)) : canonicalFilter d a = star d * a.val * d :=
  (exists_canonicalFilter d).choose_spec a

/-- **96V** (`canonical-filter`, proc.tex:414, Proposition): the map
`c(a) = d* a d : ⌈d⌉ᵣ𝒜⌈d⌉ᵣ → 𝒜` is a filter. -/
theorem canonical_filter [VonNeumannAlgebra A] (d : A) :
    IsFilter (canonicalFilter d) := sorry

/-! ## Parsec 980: standard corner and filter -/

/-- **98I** (`dfn-standard-corner-and-filter`, proc.tex:551, Definition),
part 1, well-definedness: for positive `p` the assignment
`a ↦ √p a √p` gives an ncp-map `⌈p⌉𝒜⌈p⌉ → 𝒜`; by choice `stdFilter`. -/
theorem exists_stdFilter [VonNeumannAlgebra A] (p : A) :
    ∃ c : NCPMap (Corner A (ceil p)) A,
      ∀ a : Corner A (ceil p), c a = CFC.sqrt p * a.val * CFC.sqrt p := by
  obtain ⟨c, hc⟩ := exists_adFromCorner (ceil p) (CFC.sqrt p)
  refine ⟨c, fun a => ?_⟩
  rw [hc a, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq]

/-- **98I** (`dfn-standard-corner-and-filter`, proc.tex:551, Definition),
part 1: the **standard filter** `c_p : ⌈p⌉𝒜⌈p⌉ → 𝒜` for a positive
element `p`, given by `c_p(a) = √p a √p`. -/
noncomputable def stdFilter [VonNeumannAlgebra A] (p : A) :
    NCPMap (Corner A (ceil p)) A := (exists_stdFilter p).choose

theorem stdFilter_apply [VonNeumannAlgebra A] (p : A)
    (a : Corner A (ceil p)) : stdFilter p a = CFC.sqrt p * a.val * CFC.sqrt p :=
  (exists_stdFilter p).choose_spec a

/-- **98I** (`dfn-standard-corner-and-filter`, proc.tex:551, Definition),
part 2: the **standard corner** `π_p : 𝒜 → ⌊p⌋𝒜⌊p⌋` of an effect `p`,
given by `π_p(a) = ⌊p⌋a⌊p⌋` — the corner projection onto `⌊p⌋`. -/
noncomputable def stdCorner [VonNeumannAlgebra A] (p : A) :
    NCPUMap A (Corner A (floor p)) := cornerProjMap (floor p)

theorem stdCorner_apply [VonNeumannAlgebra A] (p : A) (a : A) :
    ((stdCorner p).toNCPMap a).val = floor p * a * floor p :=
  cornerProjMap_apply (floor p) a

/-- Infrastructure for 98IV/98V (the two sides of `corners-floor`): an
ncp-map kills `p^⊥` iff it kills `⌊p⌋^⊥`.  Left to right is 60V
(`⌈f(p^⊥)⌉ = ⌈f(⌈p^⊥⌉)⌉` and `⌈p^⊥⌉ = ⌊p⌋^⊥`), right to left is
`p^⊥ ≤ ⌊p⌋^⊥` and positivity. -/
theorem map_perp_iff_floor [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (p : A) (hp : p ∈ effects A) (f : NCPMap A B) :
    f (1 - p) = 0 ↔ f (1 - floor p) = 0 := by
  have hfl : IsStarProjection (floor p) := isStarProjection_floor p
  have h1p : (0 : A) ≤ 1 - p := sub_nonneg.mpr hp.2
  set F : A →ₚ[ℂ] B := PositiveLinearMap.ofClass f.toCompletelyPositiveMap with hF
  have hFapp : ∀ a : A, F a = f a := fun _ => rfl
  have hFn : PreservesDirSups ⇑F := f.preservesDirSups'
  have hFnn : ∀ a : A, 0 ≤ a → (0 : B) ≤ F a := by
    intro a ha
    have hz : (F (0 : A) : B) = 0 := map_zero F
    have h0 : (F (0 : A) : B) ≤ F a := F.monotone ha
    rwa [hz] at h0
  constructor
  · intro h0
    have h1 : ceil (F (1 - p)) = ceil (F (ceil (1 - p))) := ncp_ceil F hFn (1 - p) h1p
    rw [hFapp (1 - p), h0, ceil_zero, ((ceil_floor_basic_1 p hp).2).symm] at h1
    exact (ceil_basic_3 _ (hFnn _ hfl.one_sub.nonneg)).mpr h1.symm
  · intro h0
    refine le_antisymm ?_ (hFnn _ h1p)
    have h2 : (F (1 - p) : B) ≤ (F (1 - floor p) : B) :=
      F.monotone (sub_le_sub_left (floor_le hp) 1)
    rwa [show (F (1 - floor p) : B) = f (1 - floor p) from rfl, h0] at h2

/-- Infrastructure for 98IV (`corner-basic`): the standard corner
`π_p(a) = ⌊p⌋a⌊p⌋` *is* a corner of `p` — 95II with `u = ⌊p⌋`, rendered
directly on `⌊p⌋𝒜⌊p⌋` (so as to avoid transporting along
`⌊p⌋*⌊p⌋ = ⌊p⌋`).  The proof is the one of 95II. -/
theorem isCornerOf_stdCorner [VonNeumannAlgebra A] (p : A)
    (hp : p ∈ effects A) : IsCornerOf p (stdCorner p).toNCPMap := by
  have hfl : IsStarProjection (floor p) := isStarProjection_floor p
  have hflp : floor p * p = floor p := (floor_spec hp).2.1
  have hpi : ∀ a : A, ((stdCorner p).toNCPMap a).val = floor p * a * floor p :=
    stdCorner_apply p
  refine ⟨Corner.val_injective ?_, ?_⟩
  · rw [hpi]
    change floor p * (1 - p) * floor p = (0 : A)
    rw [mul_sub, mul_one, hflp, sub_self, zero_mul]
  intro B _ _ _ _ f hf0
  set F : A →ₚ[ℂ] B := PositiveLinearMap.ofClass f.toCompletelyPositiveMap with hF
  have hFn : PreservesDirSups ⇑F := f.preservesDirSups'
  have hfq : F (1 - floor p) = 0 := (map_perp_iff_floor p hp f).mp hf0
  -- `⌈f⌉ ≤ ⌊p⌋`, so `f(a) = f(⌊p⌋a⌊p⌋)` by 63VI
  have hcle : carrier F hFn ≤ floor p := (carrier_spec F hFn).2.2 _ hfl hfq
  have hcproj : IsStarProjection (carrier F hFn) := (carrier_spec F hFn).1
  have hcq : carrier F hFn * floor p = carrier F hFn :=
    ((projection_below_effect (floor p) (carrier F hFn)
      ⟨hfl.nonneg, hfl.le_one⟩ hcproj).out 0 7).mp hcle
  have hqc : floor p * carrier F hFn = carrier F hFn := by
    have hs := congrArg star hcq
    rwa [star_mul, hfl.isSelfAdjoint.star_eq, hcproj.isSelfAdjoint.star_eq] at hs
  have hconj : ∀ a : A, F a = F (floor p * a * floor p) := by
    intro a
    have e1 := (carrier_fundamental F hFn a).2.2
    have e2 := (carrier_fundamental F hFn (floor p * a * floor p)).2.2
    rw [e2, show carrier F hFn * (floor p * a * floor p) * carrier F hFn
        = (carrier F hFn * floor p) * a * (floor p * carrier F hFn) by
      noncomm_ring, hcq, hqc, ← e1]
  have hfac : ∀ a : A, f a = ncpComp f (cornerIncl (floor p)).toNCPMap
      ((stdCorner p).toNCPMap a) := by
    intro a
    rw [ncpComp_apply, cornerIncl_apply, hpi]
    exact hconj a
  refine ⟨ncpComp f (cornerIncl (floor p)).toNCPMap, hfac, fun g hg => ?_⟩
  refine DFunLike.ext _ _ fun b => ?_
  have hsurj : (stdCorner p).toNCPMap b.val = b :=
    Corner.val_injective (by rw [hpi]; exact b.property)
  calc g b = g ((stdCorner p).toNCPMap b.val) := by rw [hsurj]
    _ = f b.val := (hg _).symm
    _ = ncpComp f (cornerIncl (floor p)).toNCPMap
          ((stdCorner p).toNCPMap b.val) := hfac _
    _ = ncpComp f (cornerIncl (floor p)).toNCPMap b := by rw [hsurj]

/-- **98II** (`filter-basic`, proc.tex:577, Exercise), part 1: for a filter
`c : C → 𝒜` with `p := c(1)` there is a unique ncp-map
`α : C → ⌈p⌉𝒜⌈p⌉` with `c = c_p ∘ α`, and this `α` is a unital
ncp-isomorphism. -/
theorem filter_basic_1 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (c : NCPMap C A) (hc : IsFilter c) :
    ∃ α : NCPMap C (Corner A (ceil (c 1))),
      (∀ x : C, c x = stdFilter (c 1) (α x)) ∧ α 1 = 1 ∧
      (∃ α' : NCPMap (Corner A (ceil (c 1))) C,
        (∀ x, α' (α x) = x) ∧ ∀ y, α (α' y) = y) ∧
      (∀ β : NCPMap C (Corner A (ceil (c 1))),
        (∀ x : C, c x = stdFilter (c 1) (β x)) → β = α) := sorry

/-- **98II** (`filter-basic`, proc.tex:577, Exercise), part 2: a filter is
injective, faithful (`⌈c⌉ = 1`), and mono in `W*_cp`. -/
theorem filter_basic_2 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (c : NCPMap C A) (hc : IsFilter c) :
    Function.Injective ⇑c ∧ ncpCarrier c = 1 ∧
      ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
        [VonNeumannAlgebra B] (g h : NCPMap B C),
        (∀ b, c (g b) = c (h b)) → g = h := sorry

/-- **98II** (`filter-basic`, proc.tex:577, Exercise), part 3: a filter is
bipositive. -/
theorem filter_basic_3 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (c : NCPMap C A) (hc : IsFilter c) (x : C) : 0 ≤ c x ↔ 0 ≤ x := sorry

/-- **98III** (`filters-composition`, proc.tex:601, Exercise): the
composition of filters is a filter. -/
theorem filters_composition [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (c : NCPMap C B) (d : NCPMap B A)
    (hc : IsFilter c) (hd : IsFilter d) : IsFilter (ncpComp d c) := sorry

/-- **98IV** (`corner-basic`, proc.tex:608, Exercise), part 1: for a
(unital) corner `π : 𝒜 → C` of an effect `p` there is a unique ncp-map
`β : ⌊p⌋𝒜⌊p⌋ → C` with `π = β ∘ π_p`; and this `β` is unital and an
ncp-isomorphism. -/
theorem corner_basic_1 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (p : A) (hp : p ∈ effects A) (π : NCPMap A C) (hπ : IsCornerOf p π)
    (hu : π 1 = 1) :
    ∃ β : NCPMap (Corner A (floor p)) C,
      (∀ a : A, π a = β ((stdCorner p).toNCPMap a)) ∧ β 1 = 1 ∧
      (∃ β' : NCPMap C (Corner A (floor p)),
        (∀ x, β' (β x) = x) ∧ ∀ y, β (β' y) = y) ∧
      (∀ β₂ : NCPMap (Corner A (floor p)) C,
        (∀ a : A, π a = β₂ ((stdCorner p).toNCPMap a)) → β₂ = β) := by
  -- Two corners of the same effect are initial among the same maps, hence
  -- canonically isomorphic; `π_p` is a corner of `p` by `isCornerOf_stdCorner`.
  have hρ : IsCornerOf p (stdCorner p).toNCPMap := isCornerOf_stdCorner p hp
  obtain ⟨β, hβ, hβu⟩ := hρ.universal C π hπ.map_perp
  obtain ⟨α, hα, -⟩ := hπ.universal (Corner A (floor p))
    (stdCorner p).toNCPMap hρ.map_perp
  have hβα : ncpComp β α = ncpId C := by
    obtain ⟨_, _, hun⟩ := hπ.universal C π hπ.map_perp
    rw [hun (ncpComp β α) (fun a => by rw [ncpComp_apply, ← hα, ← hβ]),
      hun (ncpId C) (fun a => by rw [ncpId_apply])]
  have hαβ : ncpComp α β = ncpId (Corner A (floor p)) := by
    obtain ⟨_, _, hun⟩ := hρ.universal (Corner A (floor p))
      (stdCorner p).toNCPMap hρ.map_perp
    rw [hun (ncpComp α β) (fun a => by rw [ncpComp_apply, ← hβ, ← hα]),
      hun (ncpId _) (fun a => by rw [ncpId_apply])]
  refine ⟨β, hβ, ?_, ⟨α, fun x => ?_, fun y => ?_⟩, hβu⟩
  · rw [← (stdCorner p).unital', ← hβ, hu]
  · have hx := congrArg
      (fun (k : NCPMap (Corner A (floor p)) (Corner A (floor p))) => k x) hαβ
    simpa [ncpComp_apply, ncpId_apply] using hx
  · have hy := congrArg (fun (k : NCPMap C C) => k y) hβα
    simpa [ncpComp_apply, ncpId_apply] using hy

/-- **98IV** (`corner-basic`, proc.tex:608, Exercise), part 2: a corner is
surjective, and epi in `W*_cp`. -/
theorem corner_basic_2 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (p : A) (hp : p ∈ effects A) (π : NCPMap A C) (hπ : IsCornerOf p π)
    (hu : π 1 = 1) :
    Function.Surjective ⇑π ∧
      ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
        [VonNeumannAlgebra B] (g h : NCPMap C B),
        (∀ a, g (π a) = h (π a)) → g = h := by
  -- surjectivity: `π = β ∘ π_p` with `β` invertible and `π_p` surjective;
  -- epi: `g ∘ π` factors through `π` uniquely, and both `g` and `h` do it
  obtain ⟨β, hβ, -, ⟨β', -, hββ'⟩, -⟩ := corner_basic_1 p hp π hπ hu
  refine ⟨fun c => ⟨(β' c).val, ?_⟩, ?_⟩
  · have hsurj : (stdCorner p).toNCPMap (β' c).val = β' c :=
      Corner.val_injective (by rw [stdCorner_apply]; exact (β' c).property)
    rw [hβ, hsurj, hββ']
  · intro B _ _ _ _ g h hgh
    obtain ⟨k, -, hun⟩ := hπ.universal B (ncpComp g π) (by
      rw [ncpComp_apply, hπ.map_perp]
      exact map_zero g.toCompletelyPositiveMap)
    rw [hun g (fun a => by rw [ncpComp_apply]),
      hun h (fun a => by rw [ncpComp_apply, hgh])]

/-- **98V** (`corners-floor`, proc.tex:622, Exercise): an ncpu-map `π` is a
corner for an effect `p` iff it is a corner for `⌊p⌋`; in which case
`⌈π⌉ = ⌊p⌋`.  (Thus a corner `π` is a corner for `⌈π⌉`.) -/
theorem corners_floor [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (p : A) (hp : p ∈ effects A) (π : NCPMap A B) (hu : π 1 = 1) :
    (IsCornerOf p π ↔ IsCornerOf (floor p) π) ∧
      (IsCornerOf p π → ncpCarrier π = floor p) := by
  -- the two universal properties quantify over the *same* maps, by
  -- `map_perp_iff_floor`; and `⌈π⌉ = ⌊p⌋` because `π = β ∘ π_p` with `β`
  -- injective, so `π(e^⊥) = 0` iff `⌊p⌋e^⊥⌊p⌋ = 0` iff `⌊p⌋ ≤ e`
  have hfl : IsStarProjection (floor p) := isStarProjection_floor p
  have hcspec : IsStarProjection (ncpCarrier π) ∧ π (1 - ncpCarrier π) = 0 ∧
      ∀ q : A, IsStarProjection q → π (1 - q) = 0 → ncpCarrier π ≤ q :=
    (exists_ncpCarrier π).choose_spec.1
  refine ⟨⟨fun h => ⟨(map_perp_iff_floor p hp π).mp h.map_perp,
      fun D _ _ _ _ f hf => h.universal D f ((map_perp_iff_floor p hp f).mpr hf)⟩,
    fun h => ⟨(map_perp_iff_floor p hp π).mpr h.map_perp,
      fun D _ _ _ _ f hf => h.universal D f ((map_perp_iff_floor p hp f).mp hf)⟩⟩,
    fun h => ?_⟩
  obtain ⟨β, hβ, -, ⟨β', hβ'β, -⟩, -⟩ := corner_basic_1 p hp π h hu
  refine le_antisymm (hcspec.2.2 _ hfl ((map_perp_iff_floor p hp π).mp h.map_perp)) ?_
  have he : IsStarProjection (ncpCarrier π) := hcspec.1
  have hinj : Function.Injective ⇑β := fun x y hxy => by rw [← hβ'β x, ← hβ'β y, hxy]
  have hstd : (stdCorner p).toNCPMap (1 - ncpCarrier π) = 0 := by
    refine hinj ?_
    rw [← hβ, hcspec.2.1]
    exact (map_zero β.toCompletelyPositiveMap).symm
  have hval : floor p * (1 - ncpCarrier π) * floor p = 0 := by
    have hc := congrArg Corner.val hstd
    rwa [stdCorner_apply] at hc
  have hz : (1 - ncpCarrier π) * floor p = 0 := by
    refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
    rw [star_mul, hfl.isSelfAdjoint.star_eq, he.one_sub.isSelfAdjoint.star_eq]
    calc floor p * (1 - ncpCarrier π) * ((1 - ncpCarrier π) * floor p)
        = floor p * ((1 - ncpCarrier π) * (1 - ncpCarrier π)) * floor p := by
          noncomm_ring
      _ = floor p * (1 - ncpCarrier π) * floor p := by
          rw [he.one_sub.isIdempotentElem.eq]
      _ = 0 := hval
  refine ((projection_below_effect (ncpCarrier π) (floor p)
    ⟨he.nonneg, he.le_one⟩ hfl).out 0 6).mpr ?_
  rw [sub_mul, one_mul, sub_eq_zero] at hz
  exact hz.symm

/-- **98VI** (`corners-composition`, proc.tex:631, Exercise): the
composition of corners is again a corner. -/
theorem corners_composition [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (π : NCPMap A B) (τ : NCPMap B C)
    (hπ : IsCornerMap π) (hτ : IsCornerMap τ) : IsCornerMap (ncpComp τ π) :=
  sorry

/-- **98VII** (`filter-corner`, proc.tex:642, Theorem): given an ncp-map
`f : 𝒜 → ℬ`, a projection `e` with `⌈f⌉ ≤ e`, and a positive `p` with
`f(1) ≤ p`, there is a unique ncp-map `g : e𝒜e → ⌈p⌉ℬ⌈p⌉` with
`c_p ∘ g ∘ π_e = f`; it is given by `g(a) = √p \ f(a) / √p`. -/
theorem filter_corner [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : A) [Fact (IsStarProjection e)]
    (hce : ncpCarrier f ≤ e) (p : B) (hp : 0 ≤ p) (hfp : f 1 ≤ p) :
    ∃! g : NCPMap (Corner A e) (Corner B (ceil p)),
      ∀ a : A, f a = stdFilter p (g ((cornerProjMap e).toNCPMap a)) := sorry

/-- **98VII** (`filter-corner`, proc.tex:642, Theorem), formula: the unique
`g` above is given by `g(a) = √p \ f(a) / √p`. -/
theorem filter_corner_formula [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : A) [Fact (IsStarProjection e)]
    (hce : ncpCarrier f ≤ e) (p : B) (hp : 0 ≤ p) (hfp : f 1 ≤ p)
    (g : NCPMap (Corner A e) (Corner B (ceil p)))
    (hg : ∀ a : A, f a = stdFilter p (g ((cornerProjMap e).toNCPMap a))) :
    ∀ x : Corner A e,
      (g x).val = ldiv (CFC.sqrt p) (div (f x.val) (CFC.sqrt p)) := sorry

/-- **98IX** (`square-f`, proc.tex:698, Corollary), well-definedness: for
an ncp-map `f : 𝒜 → ℬ` the formula `a ↦ √f(1) \ f(a) / √f(1)` gives an
ncp-map `⌈f⌉𝒜⌈f⌉ → ⌈f(1)⌉ℬ⌈f(1)⌉`; by choice `sqBracket`, the map
`[f]`. -/
theorem exists_sqBracket [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    ∃ g : NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))),
      ∀ a : Corner A (ncpCarrier f),
        (g a).val = ldiv (CFC.sqrt (f 1)) (div (f a.val) (CFC.sqrt (f 1))) :=
  sorry

/-- **98IX** (`square-f`, proc.tex:698, Corollary): the ncp-map
`[f] : ⌈f⌉𝒜⌈f⌉ → ⌈f(1)⌉ℬ⌈f(1)⌉` with `c_{f(1)} ∘ [f] ∘ π_{⌈f⌉} = f`. -/
noncomputable def sqBracket [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))) :=
  (exists_sqBracket f).choose

/-- **98IX** (`square-f`, proc.tex:698, Corollary): `[f]` is the unique
ncp-map making the square `c_{f(1)} ∘ [f] ∘ π_{⌈f⌉} = f` commute;
moreover `[f]` is unital and faithful. -/
theorem square_f [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    (∀ a : A,
      f a = stdFilter (f 1)
        (sqBracket f ((cornerProjMap (ncpCarrier f)).toNCPMap a))) ∧
    (∀ g : NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))),
      (∀ a : A, f a = stdFilter (f 1)
        (g ((cornerProjMap (ncpCarrier f)).toNCPMap a))) → g = sqBracket f) ∧
    sqBracket f 1 = 1 ∧ ncpCarrier (sqBracket f) = 1 := sorry

/-! ## Parsec 990: isomorphism -/

/-- **99II** (`gardner`, proc.tex:795, Proposition): for an ncpu-map
`f : 𝒜 → ℬ` between von Neumann algebras the following are equivalent:
(1) `f` is multiplicative; (2) `f(a)f(b) = 0` whenever `ab = 0`;
(3) `⌈f(p)⌉⌈f(q)⌉ = 0` for projections with `pq = 0`; (4) `f` maps
projections to projections; (5) `⌈f(a)⌉ = f(⌈a⌉)` for `a ≥ 0`. -/
theorem gardner [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hu : f 1 = 1) :
    [ ∀ a b : A, f (a * b) = f a * f b,
      ∀ a b : A, a * b = 0 → f a * f b = 0,
      ∀ p q : A, IsStarProjection p → IsStarProjection q → p * q = 0 →
        ceil (f p) * ceil (f q) = 0,
      ∀ p : A, IsStarProjection p → IsStarProjection (f p),
      ∀ a : A, 0 ≤ a → ceil (f a) = f (ceil a) ].TFAE := sorry

/-- **99IX** (`iso`, proc.tex:878, Theorem): an ncpsu-isomorphism between
von Neumann algebras is an nmiu-isomorphism (unital, multiplicative, and
involution preserving). -/
theorem iso [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPSUMap A B) (g : NCPSUMap B A)
    (hgf : ∀ a, g.toNCPMap (f.toNCPMap a) = a)
    (hfg : ∀ b, f.toNCPMap (g.toNCPMap b) = b) :
    f.toNCPMap 1 = 1 ∧
      (∀ a b : A, f.toNCPMap (a * b) = f.toNCPMap a * f.toNCPMap b) ∧
      (∀ a : A, f.toNCPMap (star a) = star (f.toNCPMap a)) := sorry

/-- **99XI** (proc.tex:897, Exercise): any filter of a projection is
multiplicative. -/
theorem filter_of_projection_multiplicative [VonNeumannAlgebra A]
    [VonNeumannAlgebra C] (c : NCPMap C A) (hc : IsFilter c)
    (hp : IsStarProjection (c 1)) : ∀ x y : C, c (x * y) = c x * c y := sorry

/-- **99XII** (`sharp-multiplicative`, proc.tex:905, Exercise): for an
ncp-map `f` between von Neumann algebras: multiplicative ⟺ sends
projections to projections ⟺ `⌈f(a)⌉ = f(⌈a⌉)` for `a ≥ 0`. -/
theorem sharp_multiplicative [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    [ ∀ a b : A, f (a * b) = f a * f b,
      ∀ p : A, IsStarProjection p → IsStarProjection (f p),
      ∀ a : A, 0 ≤ a → ceil (f a) = f (ceil a) ].TFAE := sorry

/-! ## Parsec 1000: purity -/

/-- **100I** (`pure`, proc.tex:926, Definition): filters, corners, and
their compositions are called **pure**. -/
inductive IsPure :
    ∀ {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
      NCPMap A B → Prop
  | filter {A B : Type u} [CStarAlgebra A] [PartialOrder A]
      [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
      [StarOrderedRing B] {c : NCPMap A B} : IsFilter c → IsPure c
  | corner {A B : Type u} [CStarAlgebra A] [PartialOrder A]
      [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
      [StarOrderedRing B] {π : NCPMap A B} : IsCornerMap π → IsPure π
  | comp {A B C : Type u} [CStarAlgebra A] [PartialOrder A]
      [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
      [StarOrderedRing B] [CStarAlgebra C] [PartialOrder C]
      [StarOrderedRing C] {f : NCPMap A B} {g : NCPMap B C} :
      IsPure g → IsPure f → IsPure (ncpComp g f)

/-- **100II** (proc.tex:931, Exercise), part 1: an ncp-isomorphism between
von Neumann algebras is pure. -/
theorem isPure_of_iso [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) : IsPure f := by
  -- An ncp-isomorphism is a *filter*: for `h : X → B` the (unique) `k` with
  -- `h = f ∘ k` is `g ∘ h`; the hypothesis `h 1 ≤ f 1` is not needed.
  refine IsPure.filter ⟨?_⟩
  intro X _ _ _ _ h _
  refine ⟨ncpComp g h, fun x => ?_, fun k hk => ?_⟩
  · rw [ncpComp_apply, hfg]
  · refine DFunLike.ext _ _ fun x => ?_
    rw [ncpComp_apply, hk x, hgf]

/-- **100II** (proc.tex:931, Exercise), part 2: the identity map on a von
Neumann algebra is pure. -/
theorem isPure_id [VonNeumannAlgebra A] : IsPure (ncpId A) :=
  isPure_of_iso (ncpId A) (ncpId A) (fun a => by rw [ncpId_apply, ncpId_apply])
    (fun a => by rw [ncpId_apply, ncpId_apply])

/-- **100II** (proc.tex:931, Exercise), part 3: the map `a*(·)a : 𝒜 → 𝒜`
is pure, for any element `a` of a von Neumann algebra `𝒜`. -/
theorem isPure_adSelf [VonNeumannAlgebra A] (a : A) : IsPure (adSelf a) :=
  sorry

/-- **100III** (`pure-fundamental`, proc.tex:945, Proposition): for an
ncp-map `f : 𝒜 → ℬ` between von Neumann algebras are equivalent:
(1) `f` is pure; (2) `f = c ∘ π` for a filter `c` and a corner `π`;
(3) `[f]` is an ncpu-isomorphism. -/
theorem pure_fundamental [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    [ IsPure f,
      ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
        (_ : StarOrderedRing C) (_ : VonNeumannAlgebra C)
        (π : NCPMap A C) (c : NCPMap C B),
        IsCornerMap π ∧ IsFilter c ∧ f = ncpComp c π,
      sqBracket f 1 = 1 ∧
        ∃ h : NCPMap (Corner B (ceil (f 1))) (Corner A (ncpCarrier f)),
          (∀ x, h (sqBracket f x) = x) ∧ ∀ y, sqBracket f (h y) = y ].TFAE :=
  sorry

/-- **100VII** (`special-pure-maps`, proc.tex:1016, Exercise), part 1: a
faithful pure map is a filter. -/
theorem special_pure_maps_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) (hfaith : ncpCarrier f = 1) :
    IsFilter f := sorry

/-- **100VII** (`special-pure-maps`, proc.tex:1016, Exercise), part 2: a
unital pure map is a corner. -/
theorem special_pure_maps_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) (hu : f 1 = 1) : IsCornerMap f := sorry

/-- **100VII** (`special-pure-maps`, proc.tex:1016, Exercise), part 3: a
unital and faithful pure map is an ncpu-isomorphism. -/
theorem special_pure_maps_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) (hu : f 1 = 1)
    (hfaith : ncpCarrier f = 1) :
    ∃ g : NCPMap B A, (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b) ∧ g 1 = 1 :=
  sorry

/-! ## Parsec 1010: contraposition -/

/-- **101I** (proc.tex:1031, Definition): for an ncp-map `f : 𝒜 → ℬ` the
map `f^⋄ : Proj(𝒜) → Proj(ℬ)`, `f^⋄(e) = ⌈f(e)⌉` (here defined on all of
`A`; only its values on projections matter). -/
noncomputable def diamondUp [VonNeumannAlgebra B] (f : NCPMap A B)
    (e : A) : B := ceil (f e)

/-- **101II** (proc.tex:1048, Proposition), well-definedness: for an
ncp-map `f : 𝒜 → ℬ` and a projection `e` of `ℬ` there is a least
projection `p` of `𝒜` with `⌈f(p^⊥)⌉ ≤ e^⊥`. -/
theorem exists_diamondDown [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : B) (he : IsStarProjection e) :
    ∃! p : A, IsStarProjection p ∧ ceil (f (1 - p)) ≤ 1 - e ∧
      ∀ q : A, IsStarProjection q → ceil (f (1 - q)) ≤ 1 - e → p ≤ q := sorry

open scoped Classical in
/-- **101II** (proc.tex:1048, Proposition): the map
`f_⋄ : Proj(ℬ) → Proj(𝒜)`: `f_⋄(e)` is the least projection `p` with
`⌈f(p^⊥)⌉ ≤ e^⊥` (junk value `0` off the projections). -/
noncomputable def diamondDown [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : B) : A :=
  if he : IsStarProjection e then (exists_diamondDown f e he).choose else 0

/-- **101II** (proc.tex:1048, Proposition), formula: `f_⋄(e)` is the
carrier of the ncp-map `e f(·) e`, i.e. the least projection `p` with
`e·f(p^⊥)·e = 0`. -/
theorem diamondDown_carrier [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : B) (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ e * f (1 - p) * e = 0}
      (diamondDown f e) := sorry

/-- **101IV** (`diamond-suprema`, proc.tex:1071, Exercise), part 1: the
Galois-type correspondence `f^⋄(s) ≤ t^⊥ ⟺ f_⋄(t) ≤ s^⊥`. -/
theorem diamond_suprema_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (s : A) (t : B) (hs : IsStarProjection s)
    (ht : IsStarProjection t) :
    diamondUp f s ≤ 1 - t ↔ diamondDown f t ≤ 1 - s := sorry

/-- **101IV** (`diamond-suprema`, proc.tex:1071, Exercise), part 2:
`f^⋄(⋃E) = ⋃_{e∈E} f^⋄(e)` for every set of projections `E`. -/
theorem diamond_suprema_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (E : Set A) (hE : ∀ e ∈ E, IsStarProjection e) :
    diamondUp f (projSup E) = projSup (diamondUp f '' E) := sorry

/-- **101V** (proc.tex:1085, Exercise), definition part: ncp-maps `f, g`
are **equivalent** when `f^⋄ = g^⋄`. -/
def NCPEquiv [VonNeumannAlgebra B] (f g : NCPMap A B) : Prop :=
  ∀ e : A, IsStarProjection e → diamondUp f e = diamondUp g e

/-- **101V** (proc.tex:1085, Exercise): `f^⋄ = g^⋄` iff `f_⋄ = g_⋄`. -/
theorem ncpEquiv_iff [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f g : NCPMap A B) :
    NCPEquiv f g ↔
      ∀ e : B, IsStarProjection e → diamondDown f e = diamondDown g e := sorry

/-- **101VI** (`contraposed`, proc.tex:1091): ncp-maps `f : 𝒜 → ℬ` and
`g : ℬ → 𝒜` are **contraposed** when
`⌈f(s)⌉ ≤ t^⊥ ⟺ ⌈g(t)⌉ ≤ s^⊥` for all projections `s`, `t`. -/
def Contraposed [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) : Prop :=
  ∀ s t, IsStarProjection s → IsStarProjection t →
    (diamondUp f s ≤ 1 - t ↔ diamondUp g t ≤ 1 - s)

/-- **101VI** (`contraposed`, proc.tex:1091): `f^⋄ = g_⋄` iff `f_⋄ = g^⋄`
iff `f` and `g` are contraposed. -/
theorem contraposed_iff [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) :
    ((∀ s, IsStarProjection s → diamondUp f s = diamondDown g s) ↔
        (∀ t, IsStarProjection t → diamondUp g t = diamondDown f t)) ∧
      ((∀ s, IsStarProjection s → diamondUp f s = diamondDown g s) ↔
        Contraposed f g) := sorry

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 1:
the maps `a*(·)a` and `a(·)a*` on a von Neumann algebra are contraposed. -/
theorem equivalent_examples_1 [VonNeumannAlgebra A] (a : A) :
    Contraposed (adSelf a) (adSelf (star a)) := sorry

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 1
(continued): the standard corner `π_s` and the standard filter `c_s` of a
projection `s` are contraposed (the filter of a projection being the
inclusion). -/
theorem equivalent_examples_1' [VonNeumannAlgebra A] (s : A)
    [Fact (IsStarProjection s)] :
    Contraposed (cornerProjMap s).toNCPMap (cornerIncl s).toNCPMap := sorry

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 2: an
ncp-isomorphism is contraposed to its inverse. -/
theorem equivalent_examples_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) : Contraposed f g := sorry

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 3:
`(zf)^⋄ = f^⋄` for every positive central `z` with `⌈z⌉ = 1`. -/
theorem equivalent_examples_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f h : NCPMap A B) (z : B) (hz : z ∈ centre B) (hz0 : 0 ≤ z)
    (hz1 : ceil z = 1) (hh : ∀ x, h x = z * f x) : NCPEquiv h f := sorry

/-- **101VIII** (`diamond-composition`, proc.tex:1134, Exercise), part 1:
`(g ∘ f)^⋄ = g^⋄ ∘ f^⋄` and `(g ∘ f)_⋄ = f_⋄ ∘ g_⋄`. -/
theorem diamond_composition_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (f : NCPMap A B) (g : NCPMap B C) :
    (∀ e : A, IsStarProjection e →
        diamondUp (ncpComp g f) e = diamondUp g (diamondUp f e)) ∧
      ∀ e : C, IsStarProjection e →
        diamondDown (ncpComp g f) e = diamondDown f (diamondDown g e) := sorry

/-- **101VIII** (`diamond-composition`, proc.tex:1134, Exercise), part 2:
equivalence of ncp-maps is preserved under composition. -/
theorem diamond_composition_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (f f' : NCPMap A B) (g g' : NCPMap B C)
    (hf : NCPEquiv f f') (hg : NCPEquiv g g') :
    NCPEquiv (ncpComp g f) (ncpComp g' f') := sorry

/-- **101VIII** (`diamond-composition`, proc.tex:1134, Exercise), part 3:
contraposition is preserved under composition (with reversal). -/
theorem diamond_composition_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (f : NCPMap A B) (f' : NCPMap B A)
    (g : NCPMap B C) (g' : NCPMap C B) (hf : Contraposed f f')
    (hg : Contraposed g g') :
    Contraposed (ncpComp g f) (ncpComp f' g') := sorry

/-- **101IX** (`diamond-sum`, proc.tex:1162, Proposition):
`(f+g)^⋄(s) = f^⋄(s) ∪ g^⋄(s)` and `(f+g)_⋄(t) = f_⋄(t) ∪ g_⋄(t)`
(the sum `f + g` rendered as any ncp-map `h` with `h = f + g`
pointwise). -/
theorem diamond_sum [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f g h : NCPMap A B) (hh : ∀ a, h a = f a + g a) :
    (∀ s : A, IsStarProjection s →
        diamondUp h s = projSup {diamondUp f s, diamondUp g s}) ∧
      ∀ t : B, IsStarProjection t →
        diamondDown h t = projSup {diamondDown f t, diamondDown g t} := sorry

/-- **101XI** (`carrier-f-dagger-f`, proc.tex:1187, Lemma): for contraposed
`f : 𝒜 → ℬ` and `g : ℬ → 𝒜` we have `⌈f⌉ = ⌈g ∘ f⌉`. -/
theorem carrier_f_dagger_f [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (h : Contraposed f g) :
    ncpCarrier f = ncpCarrier (ncpComp g f) := sorry

/-! ## Parsec 1020: rigidity -/

/-- **102II** (`rigid`, proc.tex:1206, Definition): an ncp-map
`f : 𝒜 → ℬ` is **rigid** when the only ncp-map `g` with `g(1) = f(1)` and
`⌈f(p)⌉ = ⌈g(p)⌉` for all projections `p` is `f` itself. -/
def IsRigid [VonNeumannAlgebra B] (f : NCPMap A B) : Prop :=
  ∀ g : NCPMap A B, g 1 = f 1 →
    (∀ p : A, IsStarProjection p → ceil (f p) = ceil (g p)) → g = f

/-- **102III** (`rigid-ncp-extreme`, proc.tex:1214, Proposition): a rigid
map `f` is extreme among the ncp-maps `g` with `g(1) = f(1)`. -/
theorem rigid_ncp_extreme [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsRigid f) (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (g₁ g₂ : NCPMap A B) (h₁ : g₁ 1 = f 1) (h₂ : g₂ 1 = f 1)
    (hconv : ∀ a, f a = (l : ℂ) • g₁ a + ((1 - l : ℝ) : ℂ) • g₂ a) :
    g₁ = f ∧ g₂ = f := sorry

/-- **102V** (`nmiu-rigid`, proc.tex:1241, Proposition): an nmiu-map
between von Neumann algebras is rigid (stated for an ncp-map `f` that
coincides with an nmiu-map `ρ`). -/
theorem nmiu_rigid [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ρ : NMIUMap A B) (f : NCPMap A B) (h : ∀ a, f a = ρ a) : IsRigid f :=
  sorry

/-- **102VII** (`canonical-quotient-rigid`, proc.tex:1268, Lemma): for an
element `b` of a von Neumann algebra the ncp-map
`a ↦ b* a b : ⌈b⌉ᵣ𝒜⌈b⌉ᵣ → 𝒜` is rigid. -/
theorem canonical_quotient_rigid [VonNeumannAlgebra A] (b : A) :
    IsRigid (canonicalFilter b) := sorry

/-- **102IX** (`pure-is-rigid`, proc.tex:1341, Theorem): every pure map
between von Neumann algebras is rigid. -/
theorem pure_is_rigid [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) : IsRigid f := sorry

/-! ## Parsec 1030: ⋄-positivity -/

/-- **103I** (proc.tex:1389, Definition), part 1: an ncp-map
`f : 𝒜 → 𝒜` is **⋄-self-adjoint** if it is pure and contraposed to
itself. -/
def IsDiamondSelfAdjoint [VonNeumannAlgebra A] (f : NCPMap A A) : Prop :=
  IsPure f ∧ Contraposed f f

/-- **103I** (proc.tex:1389, Definition), part 2: an ncp-map `f : 𝒜 → 𝒜`
is **⋄-positive** if `f = g ∘ g` for some ⋄-self-adjoint `g`. -/
def IsDiamondPositive [VonNeumannAlgebra A] (f : NCPMap A A) : Prop :=
  ∃ g : NCPMap A A, IsDiamondSelfAdjoint g ∧ f = ncpComp g g

/-- **103II** (`purely-positive-examples`, proc.tex:1412, Examples),
part 1: for self-adjoint `a` the map `a(·)a` is ⋄-self-adjoint. -/
theorem purely_positive_examples_1 [VonNeumannAlgebra A] (a : A)
    (ha : IsSelfAdjoint a) : IsDiamondSelfAdjoint (adSelf a) := sorry

/-- **103II** (`purely-positive-examples`, proc.tex:1412, Examples),
part 2: for positive `a` the map `a(·)a` is ⋄-positive. -/
theorem purely_positive_examples_2 [VonNeumannAlgebra A] (a : A)
    (ha : 0 ≤ a) : IsDiamondPositive (adSelf a) := sorry

/-- **103III** (`purely-positive-basic`, proc.tex:1425, Exercise), part 1:
`⌈f⌉ = ⌈f(1)⌉` for a ⋄-self-adjoint `f`. -/
theorem purely_positive_basic_1 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) : ncpCarrier f = ceil (f 1) := sorry

/-- **103III** (`purely-positive-basic`, proc.tex:1425, Exercise), part 2:
if `f` is ⋄-self-adjoint then so is `f ∘ f`, and `⌈f∘f⌉ = ⌈f⌉`. -/
theorem purely_positive_basic_2 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) :
    IsDiamondSelfAdjoint (ncpComp f f) ∧
      ncpCarrier (ncpComp f f) = ncpCarrier f := sorry

/-- **103III** (`purely-positive-basic`, proc.tex:1425, Exercise), part 3:
a ⋄-positive map is ⋄-self-adjoint. -/
theorem purely_positive_basic_3 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondPositive f) : IsDiamondSelfAdjoint f := sorry

/-! ## Parsec 1040: central similarity -/

/-- **104II** (proc.tex:1458, Definition): positive elements `p, q` of a
von Neumann algebra are **centrally similar** if `c·p = d·q` for some
positive central `c, d` with `⌈p⌉ ≤ ⌈c⌉` and `⌈q⌉ ≤ ⌈d⌉`. -/
def CentrallySimilar [VonNeumannAlgebra A] (p q : A) : Prop :=
  ∃ c d : A, c ∈ centre A ∧ d ∈ centre A ∧ 0 ≤ c ∧ 0 ≤ d ∧
    c * p = d * q ∧ ceil p ≤ ceil c ∧ ceil q ≤ ceil d

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 1: if `p` and `q` are centrally similar then everything commuting
with `p` commutes with `q`; in particular `pq = qp`. -/
theorem centrally_similar_basic_1 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : CentrallySimilar p q) :
    (∀ a : A, a * p = p * a → a * q = q * a) ∧ p * q = q * p := sorry

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 2: centrally similar `p, q` have `⌈p⌉ = ⌈q⌉`. -/
theorem centrally_similar_basic_2 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : CentrallySimilar p q) :
    ceil p = ceil q := sorry

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 2a: assuming `p ≤ B·q`, `p` and `q` are centrally similar iff `p/q`
is central; `p` is centrally similar to `1` iff `p` is central; and `p` is
centrally similar to `p²` iff `p` is central. -/
theorem centrally_similar_basic_2a [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (bound : ℝ) (hb : p ≤ (bound : ℂ) • q) :
    (CentrallySimilar p q ↔ div p q ∈ centre A) ∧
      (CentrallySimilar p 1 ↔ p ∈ centre A) ∧
      (CentrallySimilar p (p ^ 2) ↔ p ∈ centre A) := sorry

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 3: if `p` and `q` commute, `m` is their infimum, and both `m/p` and
`m/q` are central, then `p` and `q` are centrally similar. -/
theorem centrally_similar_basic_3 [VonNeumannAlgebra A] (p q m : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcomm : p * q = q * p)
    (hm : IsGLB {p, q} m) (h1 : div m p ∈ centre A)
    (h2 : div m q ∈ centre A) : CentrallySimilar p q := sorry

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 4: for pseudoinvertible `p, q`: centrally similar iff `p·q^∼¹`
central iff `q·p^∼¹` central iff both `m·p^∼¹` and `m·q^∼¹` central
(`m` the infimum of `p` and `q`). -/
theorem centrally_similar_basic_4 [VonNeumannAlgebra A] (p q m : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpi : Pseudoinvertible A p)
    (hqi : Pseudoinvertible A q) (hm : IsGLB {p, q} m) :
    (CentrallySimilar p q ↔ p * pinv q ∈ centre A) ∧
      (p * pinv q ∈ centre A ↔ q * pinv p ∈ centre A) ∧
      (q * pinv p ∈ centre A ↔
        m * pinv p ∈ centre A ∧ m * pinv q ∈ centre A) := sorry

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 5: if `p, q` commute and `e₁ ≤ e₂ ≤ ⋯` are projections commuting
with `p` and `q`, with `⋃ₙ eₙ = ⌈p⌉`, such that the `eₙp` and `eₙq` are
pseudoinvertible and centrally similar, then `p` and `q` are centrally
similar. -/
theorem centrally_similar_basic_5 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcomm : p * q = q * p) (e : ℕ → A)
    (he : ∀ n, IsStarProjection (e n)) (hmono : Monotone e)
    (hcp : ∀ n, e n * p = p * e n) (hcq : ∀ n, e n * q = q * e n)
    (hsup : projSup (Set.range e) = ceil p)
    (hpin : ∀ n, Pseudoinvertible A (e n * p))
    (hqin : ∀ n, Pseudoinvertible A (e n * q))
    (hcs : ∀ n, CentrallySimilar (e n * p) (e n * q)) :
    CentrallySimilar p q := sorry

/-- **104IV** (`centrally-similar-fundamental`, proc.tex:1519, Lemma):
if `⌈q ϑ(e) q⌉ ≤ e` and `⌈q ϑ(e^⊥) q⌉ ≤ e^⊥` for a projection `e`,
positive `q`, and an miu-map `ϑ : 𝒜 → 𝒜`, then `eq = qe` and
`ϑ(e) = e`. -/
theorem centrally_similar_fundamental [VonNeumannAlgebra A] (e q : A)
    (he : IsStarProjection e) (hq : 0 ≤ q) (ϑ : MIUMap A A)
    (h1 : ceil (q * ϑ e * q) ≤ e)
    (h2 : ceil (q * ϑ (1 - e) * q) ≤ 1 - e) :
    e * q = q * e ∧ ϑ e = e := sorry

/-- **104VI** (`centrally-similar-corollary`, proc.tex:1546, Corollary): a
positive `q` with `⌈q⌉ = 1` is central provided there is an miu-map `ϑ`
with `⌈q ϑ(e) q⌉ ≤ e` for every projection `e`; and then `ϑ = id`. -/
theorem centrally_similar_corollary [VonNeumannAlgebra A] (q : A)
    (hq : 0 ≤ q) (hcq : ceil q = 1) (ϑ : MIUMap A A)
    (h : ∀ e : A, IsStarProjection e → ceil (q * ϑ e * q) ≤ e) :
    q ∈ centre A ∧ ∀ a, ϑ a = a := sorry

/-- **104VII** (`positive-quotients-centrally-similar`, proc.tex:1556,
Proposition): positive `p, q` with `⌈p⌉ = ⌈q⌉ = 1` are centrally similar
when there is an miu-isomorphism `ϑ` with `⌈p e p⌉ = ⌈q ϑ(e) q⌉` for all
projections `e`; and in that case `ϑ = id`. -/
theorem positive_quotients_centrally_similar [VonNeumannAlgebra A]
    (p q : A) (hp : 0 ≤ p) (hq : 0 ≤ q) (hcp : ceil p = 1)
    (hcq : ceil q = 1) (ϑ : MIUMap A A) (hbij : Function.Bijective ⇑ϑ)
    (h : ∀ e : A, IsStarProjection e →
      ceil (p * e * p) = ceil (q * ϑ e * q)) :
    CentrallySimilar p q ∧ ∀ a, ϑ a = a := sorry

/-- **104IX** (`faithful-positive-map-uniqueness`, proc.tex:1628,
Proposition): a faithful ⋄-positive map `f : 𝒜 → 𝒜` is of the form
`f = √p(·)√p` where `p := f(1)`. -/
theorem faithful_positive_map_uniqueness [VonNeumannAlgebra A]
    (f : NCPMap A A) (hf : IsDiamondPositive f)
    (hfaith : ncpCarrier f = 1) :
    ∀ a : A, f a = CFC.sqrt (f 1) * a * CFC.sqrt (f 1) := sorry

/-! ## Parsec 1050: the map `⟨f⟩` -/

/-- **105II** (`chevron-f`, proc.tex:1690, Definition), well-definedness:
for an ncp-map `f : 𝒜 → ℬ` the formula `a ↦ ⌈f(1)⌉ f(a) ⌈f(1)⌉` (the
composite `π_{⌈f(1)⌉} ∘ f ∘ c_{⌈f⌉}`, cf. 105III part 1) gives an ncp-map
`⌈f⌉𝒜⌈f⌉ → ⌈f(1)⌉ℬ⌈f(1)⌉`; by choice `chevron`. -/
theorem exists_chevron [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    ∃ g : NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))),
      ∀ a : Corner A (ncpCarrier f),
        (g a).val = ceil (f 1) * f a.val * ceil (f 1) := by
  -- `⟨f⟩ = π_{⌈f(1)⌉} ∘ f ∘ c_{⌈f⌉}` (105III part 1): a composite of ncp-maps,
  -- the filter of the projection `⌈f⌉` being the inclusion `cornerIncl`.
  refine ⟨ncpComp (cornerProjMap (ceil (f 1))).toNCPMap
    (ncpComp f (cornerIncl (ncpCarrier f)).toNCPMap), fun a => ?_⟩
  rw [ncpComp_apply, ncpComp_apply, cornerIncl_apply, cornerProjMap_apply]

/-- **105II** (`chevron-f`, proc.tex:1690, Definition): the ncp-map
`⟨f⟩ : ⌈f⌉𝒜⌈f⌉ → ⌈f(1)⌉ℬ⌈f(1)⌉` with
`c_{⌈f(1)⌉} ∘ ⟨f⟩ ∘ π_{⌈f⌉} = f`. -/
noncomputable def chevron [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))) :=
  (exists_chevron f).choose

/-- **105II** (`chevron-f`, proc.tex:1690, Definition), defining property:
`⟨f⟩` is the unique ncp-map with `c_{⌈f(1)⌉} ∘ ⟨f⟩ ∘ π_{⌈f⌉} = f` (the
filter of the projection `⌈f(1)⌉` being the inclusion of the corner). -/
theorem chevron_unique [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    (∀ a : A,
      f a = (chevron f ((cornerProjMap (ncpCarrier f)).toNCPMap a)).val) ∧
    ∀ g : NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))),
      (∀ a : A,
        f a = (g ((cornerProjMap (ncpCarrier f)).toNCPMap a)).val) →
      g = chevron f := sorry

/-- **105III** (`chevron-f-basic`, proc.tex:1717, Exercise), parts 1–2:
`⟨f⟩ = π_{⌈f(1)⌉} ∘ f ∘ c_{⌈f⌉}` (the defining formula of `chevron`) and
`⟨f⟩ = π_{⌈f(1)⌉} ∘ c_{f(1)} ∘ [f]`, i.e.
`⟨f⟩(a) = √f(1) [f](a) √f(1)`. -/
theorem chevron_f_basic_12 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (a : Corner A (ncpCarrier f)) :
    (chevron f a).val = ceil (f 1) * f a.val * ceil (f 1) ∧
      (chevron f a).val =
        CFC.sqrt (f 1) * (sqBracket f a).val * CFC.sqrt (f 1) := sorry

/-- **105III** (`chevron-f-basic`, proc.tex:1717, Exercise), part 3:
`⟨f⟩` is faithful and `⟨f⟩(1) = f(1)`. -/
theorem chevron_f_basic_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    ncpCarrier (chevron f) = 1 ∧ (chevron f 1).val = f 1 := sorry

/-- **105III** (`chevron-f-basic`, proc.tex:1717, Exercise), part 4: if
`f` is pure then `⟨f⟩` is pure, and hence a filter. -/
theorem chevron_f_basic_4 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) :
    IsPure (chevron f) ∧ IsFilter (chevron f) := sorry

/-- **105IV** (`chevron-f-purely-positive`, proc.tex:1742, Exercise),
part 1: for ⋄-self-adjoint `f : 𝒜 → 𝒜` (so `⌈f⌉ = ⌈f(1)⌉` and `⟨f⟩` can
be regarded as a map `⌈f⌉𝒜⌈f⌉ → ⌈f⌉𝒜⌈f⌉`), `⟨f⟩` is ⋄-self-adjoint.
(Rendered on the corner `⌈f(1)⌉𝒜⌈f(1)⌉` via the chevron formula.) -/
theorem chevron_f_purely_positive_1 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) :
    ∃ g : NCPMap (Corner A (ceil (f 1))) (Corner A (ceil (f 1))),
      (∀ a : Corner A (ceil (f 1)),
        (g a).val = ceil (f 1) * f a.val * ceil (f 1)) ∧
      IsDiamondSelfAdjoint g := sorry

/-- **105IV** (`chevron-f-purely-positive`, proc.tex:1742, Exercise),
part 2: for ⋄-self-adjoint `f`, `⟨f²⟩ = ⟨f⟩²` — rendered elementwise: for
`a` in the corner `⌈f(1)⌉𝒜⌈f(1)⌉`,
`⌈f(1)⌉ f(f(a)) ⌈f(1)⌉ = ⌈f(1)⌉ f(⌈f(1)⌉ f(a) ⌈f(1)⌉) ⌈f(1)⌉`. -/
theorem chevron_f_purely_positive_2 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) (a : A)
    (ha : a ∈ cornerSet A (ceil (f 1))) :
    ceil (f 1) * f (f a) * ceil (f 1) =
      ceil (f 1) * f (ceil (f 1) * f a * ceil (f 1)) * ceil (f 1) := sorry

/-- **105IV** (`chevron-f-purely-positive`, proc.tex:1742, Exercise),
part 3: if `f` is ⋄-positive then `⟨f⟩` is ⋄-positive (rendered on the
corner `⌈f(1)⌉𝒜⌈f(1)⌉` as in part 1). -/
theorem chevron_f_purely_positive_3 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondPositive f) :
    ∃ g : NCPMap (Corner A (ceil (f 1))) (Corner A (ceil (f 1))),
      (∀ a : Corner A (ceil (f 1)),
        (g a).val = ceil (f 1) * f a.val * ceil (f 1)) ∧
      IsDiamondPositive g := sorry

/-- **105V** (`positive-map-uniqueness`, proc.tex:1766, Theorem),
existence: `√p(·)√p` is a ⋄-positive map with value `p` at `1`. -/
theorem positive_map_uniqueness_exists [VonNeumannAlgebra A] (p : A)
    (hp : 0 ≤ p) :
    ∃ f : NCPMap A A, IsDiamondPositive f ∧ f 1 = p ∧
      ∀ a, f a = CFC.sqrt p * a * CFC.sqrt p := sorry

/-- **105V** (`positive-map-uniqueness`, proc.tex:1766, Theorem),
uniqueness: any ⋄-positive `f : 𝒜 → 𝒜` with `f(1) = p` is
`√p(·)√p`. -/
theorem positive_map_uniqueness [VonNeumannAlgebra A] (p : A) (hp : 0 ≤ p)
    (f : NCPMap A A) (hf : IsDiamondPositive f) (h1 : f 1 = p) :
    ∀ a, f a = CFC.sqrt p * a * CFC.sqrt p := sorry

/-- **105VII** (`sqrt-axiom`, proc.tex:1792, Corollary, "Square Root
Axiom"): given positive `p` there is a unique ⋄-positive `g : 𝒜 → 𝒜`
with `g(g(1)) = p`, namely `g = ⁴√p(·)⁴√p`. -/
theorem sqrt_axiom [VonNeumannAlgebra A] (p : A) (hp : 0 ≤ p) :
    (∃ g : NCPMap A A, IsDiamondPositive g ∧ g (g 1) = p ∧
      ∀ a, g a = CFC.sqrt (CFC.sqrt p) * a * CFC.sqrt (CFC.sqrt p)) ∧
    ∀ g : NCPMap A A, IsDiamondPositive g → g (g 1) = p →
      ∀ a, g a = CFC.sqrt (CFC.sqrt p) * a * CFC.sqrt (CFC.sqrt p) := sorry

/-! ## Parsec 1060: the sequential product -/

/-- **106I** (`uniqueness-sequential-product`, proc.tex:1811, Theorem), the
axioms: a binary operation `∗` on (the effects of) a von Neumann algebra
`𝒜` is a **sequential product** when for all effects `p`:
(A) `p ∗ 1 = p`; (B) `p ∗ (·)` is given on effects by a pure map;
(C) `p ∗ (p ∗ q) = (p ∗ p) ∗ q`; (D) `p = q ∗ q` for some effect `q`;
(E) `p ∗ e₁ ≤ e₂^⊥ ⟺ p ∗ e₂ ≤ e₁^⊥` for projections `e₁, e₂`. -/
structure IsSequentialProduct [VonNeumannAlgebra A] (op : A → A → A) :
    Prop where
  ax1 : ∀ p ∈ effects A, op p 1 = p
  ax2 : ∀ p ∈ effects A, ∃ f : NCPMap A A, IsPure f ∧
    ∀ q ∈ effects A, op p q = f q
  ax3 : ∀ p ∈ effects A, ∀ q ∈ effects A, op p (op p q) = op (op p p) q
  ax4 : ∀ p ∈ effects A, ∃ q ∈ effects A, p = op q q
  ax5 : ∀ p ∈ effects A, ∀ e₁ e₂ : A, IsStarProjection e₁ →
    IsStarProjection e₂ → (op p e₁ ≤ 1 - e₂ ↔ op p e₂ ≤ 1 - e₁)

/-- **106I** (`uniqueness-sequential-product`, proc.tex:1811, Theorem),
existence: `p ∗ q = √p q √p` is a sequential product on the effects of
any von Neumann algebra. -/
theorem uniqueness_sequential_product_exists [VonNeumannAlgebra A] :
    IsSequentialProduct (fun p q : A => CFC.sqrt p * q * CFC.sqrt p) := sorry

/-- **106I** (`uniqueness-sequential-product`, proc.tex:1811, Theorem),
uniqueness: any sequential product on the effects of a von Neumann algebra
is given by `p ∗ q = √p q √p`. -/
theorem uniqueness_sequential_product [VonNeumannAlgebra A] (op : A → A → A)
    (h : IsSequentialProduct op) :
    ∀ p ∈ effects A, ∀ q ∈ effects A,
      op p q = CFC.sqrt p * q * CFC.sqrt p := sorry

/-- **106III** (proc.tex:1858, Exercise), part 1: `p ∗ q := ⌈p⌉q⌈p⌉`
satisfies all axioms of 106I except (A) (which fails when `A` is
nontrivial). -/
theorem sequential_product_counterexample_1 [VonNeumannAlgebra A]
    [Nontrivial A] :
    (∀ p ∈ effects A, ∃ f : NCPMap A A, IsPure f ∧
        ∀ q ∈ effects A, ceil p * q * ceil p = f q) ∧
    (∀ p ∈ effects A, ∀ q ∈ effects A,
        ceil p * (ceil q * q * ceil q) * ceil p =
          ceil (ceil p * p * ceil p) * q * ceil (ceil p * p * ceil p)) ∧
    (∀ p ∈ effects A, ∃ q ∈ effects A, p = ceil q * q * ceil q) ∧
    (∀ p ∈ effects A, ∀ e₁ e₂ : A, IsStarProjection e₁ →
        IsStarProjection e₂ →
        (ceil p * e₁ * ceil p ≤ 1 - e₂ ↔ ceil p * e₂ * ceil p ≤ 1 - e₁)) ∧
    ¬ IsSequentialProduct (fun p q : A => ceil p * q * ceil p) := sorry

/-- **106III** (proc.tex:1858, Exercise), part 2:
`p ∗ q := ⌊p⌋q⌊p⌋ + √(p−⌊p⌋) q √(p−⌊p⌋)` satisfies axioms (A), (C),
(D), (E) of 106I.  (That (B) may fail is not formalized.) -/
theorem sequential_product_counterexample_2 [VonNeumannAlgebra A] :
    ∀ op : A → A → A,
      (∀ p q, op p q = floor p * q * floor p +
        CFC.sqrt (p - floor p) * q * CFC.sqrt (p - floor p)) →
      (∀ p ∈ effects A, op p 1 = p) ∧
      (∀ p ∈ effects A, ∀ q ∈ effects A, op p (op p q) = op (op p p) q) ∧
      (∀ p ∈ effects A, ∃ q ∈ effects A, p = op q q) ∧
      (∀ p ∈ effects A, ∀ e₁ e₂ : A, IsStarProjection e₁ →
        IsStarProjection e₂ → (op p e₁ ≤ 1 - e₂ ↔ op p e₂ ≤ 1 - e₁)) := sorry

/-- **106III** (proc.tex:1858, Exercise), part 3: for a family `u` of
unitaries `u_p` of the corners `⌈p⌉𝒜⌈p⌉`, the operation
`p ∗ q := √p u_p* q u_p √p` satisfies (A) and (B); it moreover satisfies
(C) when `u_p² = u_{p²}`, (D) when `p u_p = u_p p`, and (E) when
`u_p* = u_p`. -/
theorem sequential_product_counterexample_3 [VonNeumannAlgebra A]
    (u : A → A)
    (hu : ∀ p ∈ effects A, u p ∈ cornerSet A (ceil p) ∧
      star (u p) * u p = ceil p ∧ u p * star (u p) = ceil p)
    (op : A → A → A)
    (hop : ∀ p q, op p q =
      CFC.sqrt p * star (u p) * q * u p * CFC.sqrt p) :
    ((∀ p ∈ effects A, op p 1 = p) ∧
      (∀ p ∈ effects A, ∃ f : NCPMap A A, IsPure f ∧
        ∀ q ∈ effects A, op p q = f q)) ∧
    ((∀ p ∈ effects A, u p * u p = u (p * p)) →
      ∀ p ∈ effects A, ∀ q ∈ effects A, op p (op p q) = op (op p p) q) ∧
    ((∀ p ∈ effects A, p * u p = u p * p) →
      ∀ p ∈ effects A, ∃ q ∈ effects A, p = op q q) ∧
    ((∀ p ∈ effects A, star (u p) = u p) →
      ∀ p ∈ effects A, ∀ e₁ e₂ : A, IsStarProjection e₁ →
        IsStarProjection e₂ →
        (op p e₁ ≤ 1 - e₂ ↔ op p e₂ ≤ 1 - e₁)) := sorry

/-- **106III** (proc.tex:1858, Exercise), part 4, first claim: there is a
Borel function `g : [0,1] → S¹` with `g(½) ≠ 1` and `g(λ²) = g(λ)²`.
FIXME(borel-calculus): the second claim — that
`p ∗ q := √p g(p)* q g(p) √p` satisfies all axioms of 106I except (E) —
requires the Borel functional calculus `p ↦ g(p)`, which Mathlib's `cfc`
(continuous only) does not provide; it is not formalized. -/
theorem sequential_product_counterexample_4 :
    ∃ g : ℝ → ℂ, Measurable g ∧ (∀ l : ℝ, l ∈ Set.Icc (0:ℝ) 1 → ‖g l‖ = 1) ∧
      g (1/2) ≠ 1 ∧ ∀ l : ℝ, l ∈ Set.Icc (0:ℝ) 1 → g (l ^ 2) = g l ^ 2 := by
  -- `g(λ) = λ^{iπ/log 2} = exp(i·(π/log 2)·log λ)`: the functional equation
  -- `g(λ²) = g(λ)²` is `log(λ²) = 2 log λ` (which Mathlib's `Real.log_pow`
  -- gives for *every* real `λ`, junk value `log 0 = 0` included), and
  -- `g(½) = exp(-iπ) = -1 ≠ 1`.
  refine ⟨fun l => Complex.exp ((((Real.pi / Real.log 2) * Real.log l : ℝ) : ℂ)
      * Complex.I), ?_, fun l _ => Complex.norm_exp_ofReal_mul_I _, ?_, ?_⟩
  · fun_prop
  · have h2 : Real.log 2 ≠ 0 := by positivity
    have hlog : Real.pi / Real.log 2 * Real.log (1 / 2) = -Real.pi := by
      rw [one_div, Real.log_inv]; field_simp
    change Complex.exp _ ≠ 1
    rw [hlog]
    push_cast
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  · intro l _
    change Complex.exp _ = Complex.exp _ ^ 2
    rw [show ((Real.pi / Real.log 2 * Real.log (l ^ 2) : ℝ) : ℂ)
        = ((2 : ℕ) : ℂ) * ((Real.pi / Real.log 2 * Real.log l : ℝ) : ℂ) by
      rw [Real.log_pow]; push_cast; ring]
    rw [mul_assoc, Complex.exp_nat_mul]

/- **106IV** (`fourth-axiom`, proc.tex:1901, Problem): open problem (is
axiom (D) redundant?) — not formalizable as a theorem; skipped.
**106V** (proc.tex:1908, Remark): historical remark on the axioms of
[westerbaan2016universal]; skipped. -/

end Theses.A.Proc
