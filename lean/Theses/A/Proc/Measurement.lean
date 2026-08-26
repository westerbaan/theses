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
  existence lemmas (`exists_...`), following the pattern of
  `Theses/B/Eff/WStarCat.lean`; their defining formulas are the
  corresponding `..._apply`/`..._spec` theorems.  **All** of those existence
  lemmas are proved — `exists_sqBracket` (98IX) and `exists_diamondDown`
  (101II) included, so no statement about the maps they define is vacuous.
  (This note used to say that those two were still `sorry`; that was
  obsolete, and three proof routes elsewhere in the file were justified by
  similarly stale claims.  The file has exactly two `sorry`s:
  `centrally_similar_basic_5` (104III.5, waiting on a form of 104III.4
  relative to a projection unit) and `sequential_product_counterexample_3`
  (106III.3, whose transcribed (E) clause is false as printed — `ERRATA.md`).)
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

omit [StarOrderedRing A'] in
/-- A pointwise sum of normal monotone maps is normal.  (Needed for
`exists_ncpAdd`, hence for 102III.)  The upper-bound half is immediate;
for the least-upper-bound half, given an upper bound `u` of
`{f d + g d | d ∈ D}` and `d₁, d₂ ∈ D`, pick `d₃ ≥ d₁, d₂`: then
`f d₁ + g d₂ ≤ f d₃ + g d₃ ≤ u`, so `u - g d₂` bounds `f''D`, giving
`f s ≤ u - g d₂`; hence `u - f s` bounds `g''D`, giving `g s ≤ u - f s`. -/
theorem preservesDirSups_add {f g : A' → B'}
    (hfm : ∀ x y : A', x ≤ y → f x ≤ f y) (hgm : ∀ x y : A', x ≤ y → g x ≤ g y)
    (hf : PreservesDirSups f) (hg : PreservesDirSups g) :
    PreservesDirSups (fun a => f a + g a) := by
  intro D s hne hdir hlub
  have hF := hf D s hne hdir hlub
  have hG := hg D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact add_le_add (hF.1 ⟨d, hd, rfl⟩) (hG.1 ⟨d, hd, rfl⟩)
  · intro u hu
    have hkey : ∀ d₂ ∈ D,
        f ((s : selfAdjoint A') : A') + g ((d₂ : selfAdjoint A') : A') ≤ u := by
      intro d₂ hd₂
      have hb : (u - g ((d₂ : selfAdjoint A') : A')) ∈
          upperBounds ((fun d : selfAdjoint A' => f (d : A')) '' D) := by
        rintro _ ⟨d₁, hd₁, rfl⟩
        obtain ⟨d₃, hd₃, h13, h23⟩ := hdir d₁ hd₁ d₂ hd₂
        have h1 : f ((d₁ : selfAdjoint A') : A') ≤ f ((d₃ : selfAdjoint A') : A') :=
          hfm _ _ (Subtype.coe_le_coe.mpr h13)
        have h2 : g ((d₂ : selfAdjoint A') : A') ≤ g ((d₃ : selfAdjoint A') : A') :=
          hgm _ _ (Subtype.coe_le_coe.mpr h23)
        have h3 : f ((d₃ : selfAdjoint A') : A') + g ((d₃ : selfAdjoint A') : A') ≤ u :=
          hu ⟨d₃, hd₃, rfl⟩
        rw [le_sub_iff_add_le]
        exact le_trans (add_le_add h1 h2) h3
      have h := hF.2 hb
      rwa [le_sub_iff_add_le] at h
    have hb2 : (u - f ((s : selfAdjoint A') : A')) ∈
        upperBounds ((fun d : selfAdjoint A' => g (d : A')) '' D) := by
      rintro _ ⟨d₂, hd₂, rfl⟩
      rw [le_sub_iff_add_le, add_comm]
      exact hkey d₂ hd₂
    have h := hG.2 hb2
    rwa [le_sub_iff_add_le, add_comm] at h

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

/-- Infrastructure (needed for 102III): ncp-maps are closed under pointwise
addition.  `NCPMap` carries no algebraic instances, so — as for `ncpComp` —
this is stated as an existence lemma. -/
theorem exists_ncpAdd (f g : NCPMap A B) :
    ∃ h : NCPMap A B, ∀ a : A, h a = f a + g a := by
  have hfm : ∀ x y : A, x ≤ y → (f x : B) ≤ f y := fun x y h =>
    OrderHomClass.mono f.toCompletelyPositiveMap h
  have hgm : ∀ x y : A, x ≤ y → (g x : B) ≤ g y := fun x y h =>
    OrderHomClass.mono g.toCompletelyPositiveMap h
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := f.toCompletelyPositiveMap.toLinearMap
                  + g.toCompletelyPositiveMap.toLinearMap
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · have hsplit : M.map ⇑(f.toCompletelyPositiveMap.toLinearMap
        + g.toCompletelyPositiveMap.toLinearMap)
        = M.map ⇑f.toCompletelyPositiveMap.toLinearMap
          + M.map ⇑g.toCompletelyPositiveMap.toLinearMap := by
      ext i j
      rfl
    rw [hsplit]
    exact add_nonneg (f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM)
      (g.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM)
  · exact preservesDirSups_add hfm hgm f.preservesDirSups' g.preservesDirSups'

/-- Infrastructure: an ncp-map is positive. -/
theorem ncpMap_nonneg (f : NCPMap A B) {a : A} (ha : 0 ≤ a) : (0 : B) ≤ f a := by
  have h := OrderHomClass.mono f.toCompletelyPositiveMap ha
  rwa [map_zero f.toCompletelyPositiveMap] at h

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

/-- Infrastructure (used for 101VII part 3 and 104III part 2): for positive
`x` and positive *central* `y` with `⌈x⌉ ≤ ⌈y⌉` we have `⌈yx⌉ = ⌈x⌉`.
(`yx = √x y √x`, so 60VII gives `⌈yx⌉ = ⌈√x ⌈y⌉ √x⌉ = ⌈⌈y⌉x⌉ = ⌈x⌉`.) -/
theorem ceil_central_mul [VonNeumannAlgebra A] (x y : A) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hyc : y ∈ centre A) (hle : ceil x ≤ ceil y) :
    ceil (y * x) = ceil x := by
  have hsx : star (CFC.sqrt x) = CFC.sqrt x :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq
  have hcomm : CFC.sqrt x * y = y * CFC.sqrt x := hyc (CFC.sqrt x) (Set.mem_univ _)
  have hcc : CFC.sqrt x * ceil y = ceil y * CFC.sqrt x :=
    ceil_basic_2 y (CFC.sqrt x) hy hcomm
  have hcx : ceil x * x = x := by
    have h1 : x * ceil x = x := (ceil_spec hx).2.1
    have h2 := congrArg star h1
    rwa [star_mul, (ceil_spec hx).1.isSelfAdjoint.star_eq,
      (IsSelfAdjoint.of_nonneg hx).star_eq] at h2
  have hyx : ceil y * x = x := by
    have hcc2 : ceil y * ceil x = ceil x :=
      ((projection_below_effect (ceil y) (ceil x)
        ⟨(ceil_spec hy).1.nonneg, (ceil_spec hy).1.le_one⟩
        (ceil_spec hx).1).out 0 6).mp hle
    calc ceil y * x = ceil y * (ceil x * x) := by rw [hcx]
      _ = (ceil y * ceil x) * x := by noncomm_ring
      _ = x := by rw [hcc2, hcx]
  have e1 : y * x = star (CFC.sqrt x) * y * CFC.sqrt x := by
    rw [hsx, hcomm]
    calc y * x = y * (CFC.sqrt x * CFC.sqrt x) := by rw [CFC.sqrt_mul_sqrt_self x hx]
      _ = y * CFC.sqrt x * CFC.sqrt x := by noncomm_ring
  rw [e1, ceil_fundamental_1 (CFC.sqrt x) y hy, hsx, hcc]
  congr 1
  calc ceil y * CFC.sqrt x * CFC.sqrt x = ceil y * (CFC.sqrt x * CFC.sqrt x) := by
        noncomm_ring
    _ = ceil y * x := by rw [CFC.sqrt_mul_sqrt_self x hx]
    _ = x := hyx

/-- Infrastructure (used for 105II): `⌈f(x)⌉ ≤ ⌈f(1)⌉` for positive `x`,
because `‖x‖⁻¹x` is an effect and so `‖x‖⁻¹f(x) ≤ f(1)`. -/
theorem ceil_le_ceil_one [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (x : A) (hx : 0 ≤ x) : ceil (f x) ≤ ceil (f 1) := by
  have hz : (f (0 : A) : B) = 0 := map_zero f.toCompletelyPositiveMap
  rcases eq_or_ne x 0 with rfl | hne
  · rw [hz, ceil_zero]
    exact (isStarProjection_ceil (f 1)).nonneg
  · have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hne
    set l : ℝ := ‖x‖⁻¹ with hldef
    have hl : 0 < l := inv_pos.mpr hn
    have hb0 : (0 : A) ≤ ((l : ℝ) : ℂ) • x := by
      rw [Complex.coe_smul]; exact smul_nonneg hl.le hx
    have hb1 : ((l : ℝ) : ℂ) • x ≤ 1 := by
      refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp ?_
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, hldef,
        inv_mul_cancel₀ (ne_of_gt hn)]
    have hfle : f (((l : ℝ) : ℂ) • x) ≤ f 1 :=
      OrderHomClass.mono f.toCompletelyPositiveMap hb1
    have hfsm : (f (((l : ℝ) : ℂ) • x) : B) = ((l : ℝ) : ℂ) • f x :=
      map_smul f.toCompletelyPositiveMap.toLinearMap _ _
    rw [hfsm] at hfle
    have hnn : (0 : B) ≤ ((l : ℝ) : ℂ) • f x := by
      rw [Complex.coe_smul]; exact smul_nonneg hl.le (ncpMap_nonneg f hx)
    have hmono := ceil_mono hnn hfle
    rwa [Complex.coe_smul, ceil_smul (ncpMap_nonneg f hx) hl] at hmono

/-- Infrastructure (used for 105II): `⌈f(1)⌉f(a)⌈f(1)⌉ = f(a)` for **every**
`a` — for positive `a` by `ceil_le_ceil_one` and 59III, and in general
because both sides are `ℂ`-linear and the positive elements span. -/
theorem ceilOne_conj [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (a : A) : ceil (f 1) * f a * ceil (f 1) = f a := by
  have he : IsStarProjection (ceil (f 1)) := isStarProjection_ceil _
  have hz : (f (0 : A) : B) = 0 := map_zero f.toCompletelyPositiveMap
  have hadd : ∀ y z : A, (f (y + z) : B) = f y + f z := fun y z =>
    map_add f.toCompletelyPositiveMap.toLinearMap y z
  have hsm : ∀ (c : ℂ) (y : A), (f (c • y) : B) = c • f y := fun c y =>
    map_smul f.toCompletelyPositiveMap.toLinearMap c y
  have hpos : ∀ x : A, 0 ≤ x → ceil (f 1) * f x * ceil (f 1) = f x := by
    intro x hx
    have h := ceil_le_ceil_one f x hx
    have h1 : ceil (f 1) * f x = f x :=
      ((ceil_basic_1 (f x) (ceil (f 1)) (ncpMap_nonneg f hx) he).out 2 0).mp h
    have h2 : f x * ceil (f 1) = f x :=
      ((ceil_basic_1 (f x) (ceil (f 1)) (ncpMap_nonneg f hx) he).out 2 1).mp h
    rw [h1, h2]
  have hmem : a ∈ Submodule.span ℂ {y : A | 0 ≤ y} := by
    rw [CStarAlgebra.span_nonneg]; trivial
  induction hmem using Submodule.span_induction with
  | mem y hy => exact hpos y hy
  | zero => rw [hz, mul_zero, zero_mul]
  | add y z _ _ ihy ihz => rw [hadd, mul_add, add_mul, ihy, ihz]
  | smul c y _ ih => rw [hsm, mul_smul_comm, smul_mul_assoc, ih]

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

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 6, **both**
clauses: the supremum in `A` of a bounded directed set `D` of self-adjoint
elements of the corner `e𝒜e` lies again in `e𝒜e`, **and is, in fact, the
supremum of `D` in `e𝒜e`** — i.e. whenever `D` is the image of a set `D'`
of self-adjoint elements of `Corner A e`, that same element, read in the
corner, *is* the least upper bound of `D'` there.

(The second clause used to be left to the `VonNeumannAlgebra (Corner A e)`
instance at `Corner.isLUB_saMap_image` above, which does produce the
ambient supremum as the supremum in the corner; the DISP-tagged statement
did not say it.  It was then stated only in the conditional form "*any*
least upper bound of `D'` in the corner equals the ambient supremum", which
is weaker than the point: the point asserts that the ambient supremum *is*
the supremum in `e𝒜e`, and the conditional form is silent when `D'` has no
least upper bound in the corner at all.  The conditional form follows from
this one by `IsLUB.unique`.) -/
theorem corner_vna_basic_6 [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (he : IsStarProjection e) (D : Set (selfAdjoint A))
    (hD : ∀ d ∈ D, (d : A) ∈ cornerSet A e)
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    (dirSup D h : A) ∈ cornerSet A e ∧
      ∀ D' : Set (selfAdjoint (Corner A e)), Corner.saMap '' D' = D →
        ∃ s' : selfAdjoint (Corner A e),
          (s' : Corner A e).val = (dirSup D h : A) ∧ IsLUB D' s' := by
  -- first clause: `e(·)e` is normal (44VIII), so it sends `⋁D` to `⋁ eDe = ⋁D`
  have hmem : (dirSup D h : A) ∈ cornerSet A e :=
    isLUB_mem_cornerSet e he D (dirSup D h) hD h.1 h.2.1 (isLUB_dirSup D h)
  refine ⟨hmem, ?_⟩
  -- second clause: the order of `e𝒜e` is that of `𝒜` (part 5), so the
  -- ambient supremum — which the first clause puts in the corner — is an
  -- upper bound of `D'` there, and any upper bound of `D'` in the corner is
  -- one of `D` in `𝒜`, so the ambient supremum is below it
  rintro D' rfl
  set t : selfAdjoint A := dirSup (Corner.saMap '' D') h with ht
  have hlubA : IsLUB (Corner.saMap '' D') t := isLUB_dirSup _ h
  have htsa : IsSelfAdjoint (⟨(t : A), hmem⟩ : Corner A e) := Corner.val_injective t.2
  refine ⟨⟨⟨(t : A), hmem⟩, htsa⟩, rfl, ?_, ?_⟩
  · exact fun x hx => hlubA.1 ⟨x, hx, rfl⟩
  · intro u hu
    have hub : Corner.saMap u ∈ upperBounds (Corner.saMap '' D') := by
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    exact hlubA.2 hub

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
        TopologicalSpace.induced (Corner.val) (ultrastrong A) := by
  -- `‖x‖_{ω ∘ val} = ‖x.val‖_ω`, since `val` is a ∗-homomorphism
  have hsemi : ∀ (ω : NPFunctional A) (x : Corner A e),
      omegaNorm (Corner A e) (Corner.restrictNP e ω) x = omegaNorm A ω x.val := by
    intro ω x
    show Real.sqrt (Corner.restrictNP e ω (star x * x)).re
      = Real.sqrt (ω (star x.val * x.val)).re
    rw [Corner.restrictNP_apply, Corner.val_mul, Corner.val_star]
  have hsemi' : ∀ (ω' : NPFunctional (Corner A e)) (ω : NPFunctional A),
      (∀ y : Corner A e, ω' y = ω y.val) →
      ∀ x : Corner A e, omegaNorm (Corner A e) ω' x = omegaNorm A ω x.val := by
    intro ω' ω hω x
    show Real.sqrt (ω' (star x * x)).re = Real.sqrt (ω (star x.val * x.val)).re
    rw [hω]
    rfl
  constructor
  · refine le_antisymm ?_ ?_
    · rw [← continuous_iff_le_induced]
      refine (continuous_iInf_rng).mpr fun ω => ?_
      rw [continuous_induced_rng]
      exact continuous_ultraweak_npFunctional (Corner.restrictNP e ω)
    · show TopologicalSpace.induced (Corner.val) (ultraweak A) ≤
        ⨅ ω' : NPFunctional (Corner A e),
          TopologicalSpace.induced (fun x => ω' x) inferInstance
      refine le_iInf fun ω' => ?_
      obtain ⟨ω, -, hω⟩ := corner_vna_basic_10 e ω'
      have hfun : (fun x : Corner A e => (ω' x : ℂ))
          = (fun a : A => (ω a : ℂ)) ∘ Corner.val := funext hω
      rw [hfun, ← induced_compose]
      exact induced_mono (iInf_le _ ω)
  · refine le_antisymm ?_ ?_
    · show ultrastrong (Corner A e) ≤ TopologicalSpace.induced Corner.val
        (TopologicalSpace.generateFrom
          {U : Set A | ∃ (ω : NPFunctional A) (b : A) (ε : ℝ), 0 < ε ∧
            U = {a : A | omegaNorm A ω (a - b) < ε}})
      rw [induced_generateFrom_eq]
      refine le_generateFrom ?_
      rintro _ ⟨U, ⟨ω, b, ε, hε, rfl⟩, rfl⟩
      refine (@isOpen_iff_forall_mem_open (Corner A e)
        (ultrastrong (Corner A e)) _).mpr ?_
      intro x₀ hx₀
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx₀
      refine ⟨{x : Corner A e |
          omegaNorm (Corner A e) (Corner.restrictNP e ω) (x - x₀) <
            ε - omegaNorm A ω (x₀.val - b)}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Set.mem_ofPred_eq] at hx
        rw [hsemi] at hx
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        have htri := omegaNorm_sub_le ω x.val x₀.val b
        have hv : (x - x₀).val = x.val - x₀.val := rfl
        rw [hv] at hx
        linarith
      · exact TopologicalSpace.isOpen_generateFrom_of_mem
          ⟨Corner.restrictNP e ω, x₀, ε - omegaNorm A ω (x₀.val - b), by linarith, rfl⟩
      · simp only [Set.mem_ofPred_eq, sub_self, omegaNorm_zero]
        linarith
    · show TopologicalSpace.induced Corner.val (ultrastrong A) ≤
        TopologicalSpace.generateFrom
          {U : Set (Corner A e) | ∃ (ω' : NPFunctional (Corner A e))
            (b : Corner A e) (ε : ℝ), 0 < ε ∧
            U = {a : Corner A e | omegaNorm (Corner A e) ω' (a - b) < ε}}
      refine le_generateFrom ?_
      rintro _ ⟨ω', b, ε, hε, rfl⟩
      obtain ⟨ω, -, hω⟩ := corner_vna_basic_10 e ω'
      have hset : {a : Corner A e | omegaNorm (Corner A e) ω' (a - b) < ε}
          = Corner.val ⁻¹' {a : A | omegaNorm A ω (a - b.val) < ε} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage]
        rw [hsemi' ω' ω hω (x - b)]
        rfl
      rw [hset]
      exact ⟨_, TopologicalSpace.isOpen_generateFrom_of_mem ⟨ω, b.val, ε, hε, rfl⟩, rfl⟩

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

/-- Infrastructure (needed for 102III): a nonnegative real multiple of an
ncp-map is an ncp-map.  Rather than checking complete positivity and
normality of `l·f` directly, `l·f` is *realised* as `Ad_{√l} ∘ f`, i.e. as
`ncpComp (adSelf (√l·1)) f`, so that both obligations come for free from
`exists_adSelf` and `exists_ncpComp`.  (Cf. the independent, direct
construction in `Theses/B/Dils/Stinespring.lean`, which is `private`
there; the two should eventually be consolidated.) -/
theorem exists_ncpSmul [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) {l : ℝ} (hl : 0 ≤ l) :
    ∃ h : NCPMap A B, ∀ a : A, h a = ((l : ℝ) : ℂ) • f a := by
  refine ⟨ncpComp (adSelf (algebraMap ℂ B ((Real.sqrt l : ℝ) : ℂ))) f, fun a => ?_⟩
  rw [ncpComp_apply, adSelf_apply, ← algebraMap_star_comm]
  simp only [Complex.star_def, Complex.conj_ofReal, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt hl]

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
  -- The author's proof (proc.tex:290) verbatim; in particular the last step
  -- ("`f(a) = f(uu* a uu*)` by `cp-comprehension`") *is* `cp_comprehension`
  -- (63IV).  (Until session 94 it went through `carrier_fundamental` (63VI)
  -- instead, on the ground that 63IV was "still `sorry` in `A/VN`" — which
  -- has not been true for a long time.)
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
  -- `f` kills `(uu*)^⊥`, so `f(a) = f(uu* a uu*)` by `cp-comprehension` (63IV)
  have hconj : ∀ a : A, F a = F (u * star u * a * (u * star u)) := fun a =>
    (cp_comprehension F (u * star u) ⟨hqproj.nonneg, hqproj.le_one⟩ hfq a).2.2
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
    ∀ a : A, 0 ≤ a → 0 ≤ g a := by
  -- the author's argument (proc.tex:381): `g(a)` is the ultraweak limit of
  -- the positive elements `f_α(a)`, and the positive cone is ultraweakly
  -- closed by **44XI** (`vn-positive-basic`, part 2)
  intro a ha
  have hclosed : @IsClosed B (ultraweak B) {b : B | 0 ≤ b} := vn_positive_basic_2.1
  have hev : ∀ᶠ i in l, (f i a : B) ∈ {b : B | 0 ≤ b} := by
    filter_upwards with i
    have h : ((f i) (0 : A) : B) ≤ (f i) a := (f i).monotone ha
    rwa [map_zero (f i)] at h
  exact @IsClosed.mem_of_tendsto B (ultraweak B) ι _ _ _ l _ hclosed (hlim a) hev

/-- **96III** (`ncp-uwlim`, proc.tex:363, Lemma), part 1: the limit is
completely positive provided the `f_α` are. -/
theorem ncp_uwlim_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B] {ι : Type*}
    (l : Filter ι) [l.NeBot] (f : ι → (A →ₚ[ℂ] B)) (g : A →ₗ[ℂ] B)
    (hlim : ∀ a : A, UWTendsto (fun i => f i a) l (g a))
    (hcp : ∀ i, Theses.A.CStar.IsCompletelyPositiveMap (f i).toLinearMap) :
    Theses.A.CStar.IsCompletelyPositiveMap g := by
  -- the author's argument (proc.tex:390): `∑_{ij} b_i* g(a_i* a_j) b_j` is
  -- the ultraweak limit of the positive `∑_{ij} b_i* f_α(a_i* a_j) b_j`,
  -- because `x ↦ b_i* x b_j` is ultraweakly continuous (**45IV**
  -- `mult-uws-cont`, here in the sharper form `continuous_ultraweak_conj`),
  -- and the positive cone is ultraweakly closed (**44XI**).
  intro n a b
  have hclosed : @IsClosed B (ultraweak B) {x : B | 0 ≤ x} := vn_positive_basic_2.1
  have hlim2 : UWTendsto
      (fun i => ∑ p, ∑ q, star (b p) * (f i) (star (a p) * a q) * b q) l
      (∑ p, ∑ q, star (b p) * g (star (a p) * a q) * b q) := by
    rw [uwTendsto_iff]
    intro ω
    have hterm : ∀ p q : Fin n,
        Tendsto (fun i => (ω (star (b p) * (f i) (star (a p) * a q) * b q) : ℂ)) l
          (𝓝 (ω (star (b p) * g (star (a p) * a q) * b q))) := by
      intro p q
      have hc := @Continuous.tendsto B ℂ (ultraweak B) _
        (fun x : B => (ω (star (b p) * x * b q) : ℂ))
        (continuous_ultraweak_conj ω (star (b p)) (b q)) (g (star (a p) * a q))
      exact hc.comp (hlim (star (a p) * a q))
    have hsum := tendsto_finsetSum Finset.univ
      (fun p _ => tendsto_finsetSum Finset.univ (fun q _ => hterm p q))
    have hms : ∀ F : Fin n → B, (ω (∑ p, F p) : ℂ) = ∑ p, ω (F p) :=
      fun F => map_sum ω.toPositiveLinearMap F Finset.univ
    simp only [hms]
    exact hsum
  refine @IsClosed.mem_of_tendsto B (ultraweak B) ι _ _ _ l _ hclosed hlim2 ?_
  filter_upwards with i using hcp i n a b

/-- Infrastructure for 96III.2: the `ContinuousOn` counterpart of
`Theses.A.VN.continuous_ultraweak_of_forall` — a map into a von Neumann
algebra is ultraweakly continuous on a set as soon as `ω ∘ F` is, for every
np-functional `ω`.  (Immediate from **42III** `uwTendsto_iff`, which is
stated for an arbitrary filter and so applies to `𝓝[s] x`.) -/
private theorem continuousOn_ultraweak_of_forall (F : A → B) (s : Set A)
    (h : ∀ ω : NPFunctional B,
      @ContinuousOn A ℂ (ultraweak A) _ (fun x => (ω (F x) : ℂ)) s) :
    @ContinuousOn A B (ultraweak A) (ultraweak B) F s := by
  intro x hx
  have hx2 : UWTendsto (fun y : A => F y)
      (@nhdsWithin A (ultraweak A) x s) (F x) := by
    rw [uwTendsto_iff]
    intro ω
    exact h ω x hx
  exact hx2

/-- **96III** (`ncp-uwlim`, proc.tex:363, Lemma), part 2: the limit is
normal provided the `f_α` are normal and converge uniformly on `[0,1]_A`
(uniformly with respect to each np-functional of `B`). -/
theorem ncp_uwlim_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B] {ι : Type*}
    (l : Filter ι) [l.NeBot] (f : ι → (A →ₚ[ℂ] B)) (g : A →ₗ[ℂ] B)
    (hlim : ∀ a : A, UWTendsto (fun i => f i a) l (g a))
    (hn : ∀ i, PreservesDirSups ⇑(f i))
    (hunif : ∀ ω : NPFunctional B, ∀ ε > (0 : ℝ),
      ∀ᶠ i in l, ∀ p ∈ effects A, ‖ω (f i p) - ω (g p)‖ ≤ ε) :
    PreservesDirSups ⇑g := by
  -- the author's argument (proc.tex:405): `g` is ultraweakly continuous on
  -- `[0,1]_A`, being there a uniform limit of the ultraweakly continuous
  -- `f_α`, and hence normal by **44XV** `p-uwcont`.  ("Uniform" is read
  -- through the np-functionals, as the statement's `hunif` says: it is
  -- uniform convergence of `ω ∘ f_α` to `ω ∘ g` for each `ω`.)
  have hpos : ∀ a : A, 0 ≤ a → 0 ≤ g a := ncp_uwlim l f g hlim
  let gp : A →ₚ[ℂ] B :=
    { toFun := fun a => g a
      map_add' := map_add g
      map_smul' := map_smul g
      monotone' := fun x y hxy => by
        have h := hpos (y - x) (sub_nonneg.mpr hxy)
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  refine ((p_uwcont gp).out 1 2).mp ?_
  refine continuousOn_ultraweak_of_forall _ _ fun ω => ?_
  let _ : TopologicalSpace A := ultraweak A
  have hcont : ∀ i, ContinuousOn (fun y : A => (ω (f i y) : ℂ)) (effects A) := by
    intro i
    have h := continuous_ultraweak_npFunctional (compNP (f i) (hn i) ω)
    simpa using h.continuousOn
  have huc : TendstoUniformlyOn (fun i (y : A) => (ω (f i y) : ℂ))
      (fun y : A => (ω (g y) : ℂ)) l (effects A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hunif ω (ε / 2) (by linarith)] with i hi y hy
    have h1 := hi y hy
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  exact huc.continuousOn ((Eventually.of_forall hcont).frequently)

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

/-- The range projection `⌊b⌉ = ⌈b b*⌉` is a projection, for **every**
`b : A`.  The corner of **96V** is formed with it (see the note on the
statement of `exists_canonicalFilter`). -/
theorem isStarProjection_rangeProj [VonNeumannAlgebra A] (b : A) :
    IsStarProjection (rangeProj b) := isStarProjection_ceil _

instance factIsStarProjectionRangeProj [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (rangeProj b)) := ⟨isStarProjection_rangeProj b⟩

/-- Auxiliary for **96V**: `t` is an approximate pseudoinverse of `a` iff
`t*` is one of `a*`.  Each of the six clauses of `IsApproxPseudoinverse` is
the star-image of another; the two partial-sum sets even coincide *on the
nose*, because `t_n a` and `a t_n` are projections, hence self-adjoint. -/
private theorem isApproxPseudoinverse_star [VonNeumannAlgebra A] {a : A}
    {t : ℕ → A} (h : IsApproxPseudoinverse A a t) :
    IsApproxPseudoinverse A (star a) (fun n => star (t n)) := by
  have hL : ∀ n, star (t n) * star a = a * t n := by
    intro n; rw [← star_mul, (h.proj_right n).isSelfAdjoint.star_eq]
  have hR : ∀ n, star a * star (t n) = t n * a := by
    intro n; rw [← star_mul, (h.proj_left n).isSelfAdjoint.star_eq]
  refine { proj_left := ?_, proj_right := ?_, sum_left := ?_, sum_range := ?_,
           sum_right := ?_, sum_supp := ?_ }
  · intro n; rw [hL n]; exact h.proj_right n
  · intro n; rw [hR n]; exact h.proj_left n
  · have he : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, star (t n) * star a}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, a * t n} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [hL]⟩
    rw [he, suppProj_star]
    exact h.sum_right
  · have he : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (star (t n))}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (t n)} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [rangeProj_star]⟩
    rw [he, suppProj_star]
    exact h.sum_supp
  · have he : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, star a * star (t n)}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, t n * a} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [hR]⟩
    rw [he, rangeProj_star]
    exact h.sum_left
  · have he : {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (star (t n))}
        = {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (t n)} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [suppProj_star]⟩
    rw [he, rangeProj_star]
    exact h.sum_range

/-- **96V** (`canonical-filter`, proc.tex:414, Proposition),
well-definedness: for `d ∈ 𝒜` the assignment `a ↦ d* a d` gives an
ncp-map `(d⌉𝒜(d⌉ → 𝒜`; by choice `canonicalFilter`.

**Note on the index.**  The thesis writes the corner as `\ceilr{d}𝒜\ceilr{d}`,
and `\ceilr{·}` is the **range** projection `⌊d⌉ = ⌈dd*⌉` (vn.tex 59I), not
the support projection `⌈d⌋ = ⌈d*d⌉`.  An earlier transcription used
`suppProj d` here, which makes `canonical_filter` **false**: for
`d = |0⟩⟨1|` one has `⌈d⌋ = |1⟩⟨1|` and `d* a d = 0` for every `a` in
`⌈d⌋𝒜⌈d⌋`, so `c` is the zero map and the factorisation is not unique.
With the range projection the map is the filter for `d*d`, as it must be to
match the standard filter `c_p` of 98I at `d = √p` (where
`⌊√p⌉ = ⌈p⌉`). -/
theorem exists_canonicalFilter [VonNeumannAlgebra A] (d : A) :
    ∃ c : NCPMap (Corner A (rangeProj d)) A,
      ∀ a : Corner A (rangeProj d), c a = star d * a.val * d :=
  exists_adFromCorner (rangeProj d) d

/-- The map `d*(·)d : ⌊d⌉𝒜⌊d⌉ → 𝒜` of 96V. -/
noncomputable def canonicalFilter [VonNeumannAlgebra A] (d : A) :
    NCPMap (Corner A (rangeProj d)) A := (exists_canonicalFilter d).choose

theorem canonicalFilter_apply [VonNeumannAlgebra A] (d : A)
    (a : Corner A (rangeProj d)) : canonicalFilter d a = star d * a.val * d :=
  (exists_canonicalFilter d).choose_spec a

/-- Infrastructure for **96V** and parsec 980: for `x` in the corner
`⌊d⌉𝒜⌊d⌉` one has `d*∖(d*xd)/d = x`.  Both steps are the explicit
characterisations of **81II**: `(d*xd)/d = d*x` because `x⌊d⌉ = x`, and
`d*∖(d*x) = x` because `⌈d*⌋ = ⌊d⌉` (**59VI**.3) and `⌊d⌉x = x`. -/
theorem ldiv_div_ad [VonNeumannAlgebra A] (d x : A)
    (hx : rangeProj d * x * rangeProj d = x) :
    ldiv (star d) (div (star d * x * d) d) = x := by
  have hqq : rangeProj d * rangeProj d = rangeProj d :=
    (isStarProjection_rangeProj d).isIdempotentElem.eq
  have hxq : x * rangeProj d = x := by
    calc x * rangeProj d
        = (rangeProj d * x * rangeProj d) * rangeProj d := by rw [hx]
      _ = rangeProj d * x * (rangeProj d * rangeProj d) := by noncomm_ring
      _ = rangeProj d * x * rangeProj d := by rw [hqq]
      _ = x := hx
  have hqx : rangeProj d * x = x := by
    calc rangeProj d * x
        = rangeProj d * (rangeProj d * x * rangeProj d) := by rw [hx]
      _ = (rangeProj d * rangeProj d) * x * rangeProj d := by noncomm_ring
      _ = rangeProj d * x * rangeProj d := by rw [hqq]
      _ = x := hx
  have h1 : div (star d * x * d) d = star d * x :=
    div_eq rfl (by rw [mul_assoc, hxq])
  rw [h1]
  exact ldiv_eq rfl (by rw [suppProj_star, hqx])

/-- The heart of **96V** (proc.tex:426): an ncp-map `f : ℬ → 𝒜` with
`f(1) ≤ d*d` factors as `f = d*g(·)d` through an ncp-map
`g : ℬ → ⌊d⌉𝒜⌊d⌉`, namely `g(b) = d*∖f(b)/d`.

The author's argument.  *Existence* of the value is
`sequential-douglas` (**81VI**.1) applied to `0 ≤ f(b) ≤ ‖b‖f(1) ≤ ‖b‖d*d`,
extended off the positive cone by linearity; *positivity* is **81VI**.2;
*complete positivity* is `ncp-uwlim` (**96III**.1) applied to the
completely positive approximants `(∑_{n<N}t_n)* f(·) (∑_{n<N}t_n)`, which
converge pointwise to `g` by `div-approx` (**81VII**).

*Normality* is `div-usc` (**81IX**), as the thesis says.  The printed 81IX
claimed ultra*strong* continuity of `a ↦ d*∖a/d` on `d*(𝒜)₁d`, which is
false (see the section note above `div_uwc` in `Theses.A.VN.Division`); on
the author's ruling of 2026-08-17 both 81IX and this proof in vn.tex run
*ultraweakly* instead, and that is `div_uwc`.  So: `f` carries the effects
of `ℬ` into `d*(𝒜)₁d` (by (3) below, whose bound is `‖b‖ ≤ 1` there), on
which `a ↦ d*∖a/d` is ultraweakly continuous, hence `g` is ultraweakly
continuous on the effects and normal by **44XV** (2) ⇒ (3); the suprema
transfer to the corner by `Corner.isLUB_of_isLUB_image_val`.  (Until this
session the normality step instead used bipositivity of `c = d*(·)d` on the
corner — sound, but it left the corrected 81IX with no consumer at all, and
`div_uwc`'s own doc names this proof as the one it is for.) -/
private theorem canonicalFilter_factor [VonNeumannAlgebra A]
    {B' : Type u} [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [VonNeumannAlgebra B'] (d : A) (f : NCPMap B' A)
    (hf1 : (f 1 : A) ≤ star d * d) :
    ∃ g : NCPMap B' (Corner A (rangeProj d)),
      ∀ b : B', star d * (g b).val * d = (f b : A) := by
  classical
  set q : A := rangeProj d with hqdef
  have hq : IsStarProjection q := isStarProjection_rangeProj d
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hqd : q * d = d := (ceill_basic_2 d).1.2
  have hdq : star d * q = star d := by
    have h := congrArg star hqd
    rwa [star_mul, hq.isSelfAdjoint.star_eq] at h
  -- linearity helpers for `f`
  have hfadd : ∀ x y : B', (f (x + y) : A) = f x + f y :=
    fun x y => map_add f.toCompletelyPositiveMap x y
  have hfsmul : ∀ (z : ℂ) (x : B'), (f (z • x) : A) = z • f x :=
    fun z x => map_smul f.toCompletelyPositiveMap z x
  have hfsub : ∀ x y : B', (f (x - y) : A) = f x - f y :=
    fun x y => map_sub f.toCompletelyPositiveMap x y
  have hfmono : ∀ {x y : B'}, x ≤ y → (f x : A) ≤ f y := by
    intro x y h
    have h0 : (0 : A) ≤ f (y - x) := ncpMap_nonneg f (sub_nonneg.mpr h)
    rw [hfsub, sub_nonneg] at h0
    exact h0
  -- (1) the inversion formula `d*∖(d* x d)/d = x` for `x` in the corner
  have hinv : ∀ x : A, q * x * q = x →
      ldiv (star d) (div (star d * x * d) d) = x := fun x hx => ldiv_div_ad d x hx
  -- (2) injectivity of `c = d*(·)d` on the corner
  have hinj : ∀ x y : A, q * x * q = x → q * y * q = y →
      star d * x * d = star d * y * d → x = y := by
    intro x y hx hy h
    rw [← hinv x hx, ← hinv y hy, h]
  -- (3) every value of `f` lies in `d*𝒜d` (81VI.1 plus linearity)
  have hsmulmono : ∀ (r : ℝ), 0 ≤ r → ∀ x z : A, x ≤ z →
      ((r : ℂ)) • x ≤ ((r : ℂ)) • z := by
    intro r hr x z h
    have h2 := Theses.A.CStar.ofReal_smul_nonneg (sub_nonneg.mpr h) hr
    rwa [smul_sub, sub_nonneg] at h2
  have hposmem : ∀ y : B', 0 ≤ y →
      ∃ e : A, ‖e‖ ≤ ‖y‖ ∧ (f y : A) = star d * e * d := by
    intro y hy
    have hyle : y ≤ algebraMap ℂ B' ((‖y‖ : ℝ) : ℂ) := by
      rw [← Theses.A.CStar.algebraMap_real_eq]
      exact (IsSelfAdjoint.of_nonneg hy).le_algebraMap_norm_self
    have h1 : (f y : A) ≤ ((‖y‖ : ℝ) : ℂ) • (f 1 : A) := by
      have h := hfmono hyle
      rwa [Algebra.algebraMap_eq_smul_one, hfsmul] at h
    have h2 : (f y : A) ≤ ((‖y‖ : ℝ) : ℂ) • (star d * d) :=
      h1.trans (hsmulmono ‖y‖ (norm_nonneg y) _ _ hf1)
    exact (sequential_douglas_1 (f y) d (ncpMap_nonneg f hy) ‖y‖
      (norm_nonneg y)).1.2 h2
  have hmem : ∀ b : B', ∃ e : A, (f b : A) = star d * e * d := by
    intro b
    obtain ⟨e1, -, h1⟩ := hposmem _ (CFC.posPart_nonneg ((realPart b : B')))
    obtain ⟨e2, -, h2⟩ := hposmem _ (CFC.negPart_nonneg ((realPart b : B')))
    obtain ⟨e3, -, h3⟩ := hposmem _ (CFC.posPart_nonneg ((imaginaryPart b : B')))
    obtain ⟨e4, -, h4⟩ := hposmem _ (CFC.negPart_nonneg ((imaginaryPart b : B')))
    refine ⟨e1 - e2 + Complex.I • (e3 - e4), ?_⟩
    have hb : (realPart b : B') + Complex.I • (imaginaryPart b : B') = b :=
      realPart_add_I_smul_imaginaryPart b
    have hr : posPart ((realPart b : B')) - negPart ((realPart b : B'))
        = (realPart b : B') := CFC.posPart_sub_negPart _ (realPart b).2
    have hi : posPart ((imaginaryPart b : B')) - negPart ((imaginaryPart b : B'))
        = (imaginaryPart b : B') := CFC.posPart_sub_negPart _ (imaginaryPart b).2
    rw [← hb, ← hr, ← hi, hfadd, hfsmul, hfsub, hfsub, h1, h2, h3, h4]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  -- (4) the factorisation, elementwise
  set F : B' → A := fun b => ldiv (star d) (div ((f b : A)) d) with hFdef
  have hFapp : ∀ b : B', F b = ldiv (star d) (div ((f b : A)) d) :=
    fun b => by rw [hFdef]
  have hF : ∀ b : B', q * F b * q = F b ∧ star d * F b * d = (f b : A) := by
    intro b
    obtain ⟨e, he⟩ := hmem b
    have hcorner : q * (q * e * q) * q = q * e * q := by
      calc q * (q * e * q) * q = (q * q) * e * (q * q) := by noncomm_ring
        _ = q * e * q := by rw [hqq]
    have hfe : (f b : A) = star d * (q * e * q) * d := by
      rw [he]
      calc star d * e * d = (star d * q) * e * (q * d) := by rw [hdq, hqd]
        _ = star d * (q * e * q) * d := by noncomm_ring
    have hFb : F b = q * e * q := by
      rw [hFapp b, hfe]
      exact hinv _ hcorner
    exact ⟨by rw [hFb]; exact hcorner, by rw [hFb, ← hfe]⟩
  -- (5) linearity and positivity of `F`
  have hFadd : ∀ x y : B', F (x + y) = F x + F y := by
    intro x y
    refine hinj _ _ (hF (x + y)).1 ?_ ?_
    · rw [mul_add, add_mul, (hF x).1, (hF y).1]
    · rw [(hF (x + y)).2, hfadd, mul_add, add_mul, (hF x).2, (hF y).2]
  have hFsmul : ∀ (z : ℂ) (x : B'), F (z • x) = z • F x := by
    intro z x
    refine hinj _ _ (hF (z • x)).1 ?_ ?_
    · rw [mul_smul_comm, smul_mul_assoc, (hF x).1]
    · rw [(hF (z • x)).2, hfsmul, mul_smul_comm, smul_mul_assoc, (hF x).2]
  set Flin : B' →ₗ[ℂ] A :=
    { toFun := F, map_add' := hFadd, map_smul' := hFsmul } with hFlin
  have hFlinapp : ∀ b : B', Flin b = F b := fun _ => rfl
  have hFpos : ∀ y : B', 0 ≤ y → 0 ≤ F y := by
    intro y hy
    obtain ⟨e, he⟩ := hmem y
    rw [hFapp y]
    exact sequential_douglas_2 ((f y : A)) d (ncpMap_nonneg f hy) ⟨e, he⟩
  have hFmono : ∀ {x y : B'}, x ≤ y → F x ≤ F y := by
    intro x y h
    have h0 := hFpos (y - x) (sub_nonneg.mpr h)
    rw [show F (y - x) = F y - F x from map_sub Flin y x, sub_nonneg] at h0
    exact h0
  -- (6) complete positivity: the thesis's `div-approx` + `ncp-uwlim` argument
  have hFcp : Theses.A.CStar.IsCompletelyPositiveMap Flin := by
    obtain ⟨t, ht⟩ := approximate_pseudoinverse d
    have hst : IsApproxPseudoinverse A (star d) (fun n => star (t n)) :=
      isApproxPseudoinverse_star ht
    set T : ℕ → A := fun N => ∑ n ∈ Finset.range N, t n with hTdef
    have hTstar : ∀ N : ℕ, (∑ n ∈ Finset.range N, star (t n)) = star (T N) := by
      intro N; rw [hTdef, star_sum]
    set hN : ℕ → (B' →ₚ[ℂ] A) := fun N =>
      PositiveLinearMap.ofClass
        (ncpComp (adSelf (T N)) f).toCompletelyPositiveMap with hNdef
    have hNapp : ∀ (N : ℕ) (b : B'), (hN N b : A) = star (T N) * (f b : A) * T N := by
      intro N b
      show ((ncpComp (adSelf (T N)) f) b : A) = _
      rw [ncpComp_apply, adSelf_apply]
    -- the pointwise ultrastrong convergence, first for `0 ≤ y` with `‖y‖ ≤ 1`
    have hbase : ∀ y : B', 0 ≤ y → ‖y‖ ≤ 1 →
        USTendsto (fun N => star (T N) * (f y : A) * T N) atTop (F y) := by
      intro y hy hy1
      obtain ⟨e, hen, he⟩ := hposmem y hy
      have hconv := div_approx ((f y : A)) d (star d) t (fun n => star (t n)) ht
        hst ⟨e, hen.trans hy1, he⟩
      rw [hFapp y]
      simpa only [hTstar] using hconv
    -- closure under sums and scalars
    have hadd : ∀ x y : B',
        USTendsto (fun N => star (T N) * (f x : A) * T N) atTop (F x) →
        USTendsto (fun N => star (T N) * (f y : A) * T N) atTop (F y) →
        USTendsto (fun N => star (T N) * (f (x + y) : A) * T N) atTop (F (x + y)) := by
      intro x y hx hy
      have h := usTendsto_add hx hy
      rw [hFadd]
      refine h.congr fun N => ?_
      rw [hfadd, mul_add, add_mul]
    have hsmul : ∀ (z : ℂ) (x : B'),
        USTendsto (fun N => star (T N) * (f x : A) * T N) atTop (F x) →
        USTendsto (fun N => star (T N) * (f (z • x) : A) * T N) atTop (F (z • x)) := by
      intro z x hx
      have h := usTendsto_smul z hx
      rw [hFsmul]
      refine h.congr fun N => ?_
      rw [hfsmul, mul_smul_comm, smul_mul_assoc]
    have hpos : ∀ y : B', 0 ≤ y →
        USTendsto (fun N => star (T N) * (f y : A) * T N) atTop (F y) := by
      intro y hy
      rcases eq_or_lt_of_le (norm_nonneg y) with hn | hn
      · have hy0 : y = 0 := norm_eq_zero.mp hn.symm
        subst hy0
        have hf0 : (f (0 : B') : A) = 0 := map_zero f.toCompletelyPositiveMap
        have hF0 : F (0 : B') = 0 := by
          refine hinj _ _ (hF 0).1 (by simp) ?_
          rw [(hF 0).2, hf0]; simp
        rw [hF0]
        simp only [hf0, mul_zero, zero_mul]
        exact usTendsto_const 0
      · have hu0 : (0 : B') ≤ ((‖y‖⁻¹ : ℝ) : ℂ) • y :=
          Theses.A.CStar.ofReal_smul_nonneg hy (by positivity)
        have hu1 : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ ≤ 1 := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hn)]
          rw [inv_mul_cancel₀ (ne_of_gt hn)]
        have hy' : ((‖y‖ : ℝ) : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y) = y := by
          rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hn)]
          simp
        have h := hsmul ((‖y‖ : ℝ) : ℂ) _ (hbase _ hu0 hu1)
        rwa [hy'] at h
    have hsa : ∀ y : B', IsSelfAdjoint y →
        USTendsto (fun N => star (T N) * (f y : A) * T N) atTop (F y) := by
      intro y hy
      have hd0 : posPart y + (-1 : ℂ) • negPart y = y := by
        rw [neg_one_smul, ← sub_eq_add_neg]
        exact CFC.posPart_sub_negPart y hy
      have h := hadd _ _ (hpos _ (CFC.posPart_nonneg y))
        (hsmul (-1 : ℂ) _ (hpos _ (CFC.negPart_nonneg y)))
      rwa [hd0] at h
    have hall : ∀ b : B',
        USTendsto (fun N => star (T N) * (f b : A) * T N) atTop (F b) := by
      intro b
      have hb : (realPart b : B') + Complex.I • (imaginaryPart b : B') = b :=
        realPart_add_I_smul_imaginaryPart b
      have h := hadd _ _ (hsa _ (realPart b).2)
        (hsmul Complex.I _ (hsa _ (imaginaryPart b).2))
      rwa [hb] at h
    refine Theses.A.Proc.ncp_uwlim_1 atTop hN Flin ?_ ?_
    · intro b
      have h := uwweaker_2 _ atTop _ (hall b)
      rw [hFlinapp b]
      exact h.congr fun N => (hNapp N b).symm
    · intro N
      refine ((Theses.A.CStar.cp_iff _).out 1 0).mp fun k M hM => ?_
      exact (ncpComp (adSelf (T N)) f).toCompletelyPositiveMap.map_cstarMatrix_nonneg'
        k M hM
  -- (7) assemble
  refine ⟨{ toCompletelyPositiveMap :=
              { toFun := fun b => ⟨F b, (hF b).1⟩
                map_add' := fun x y => Corner.val_injective (hFadd x y)
                map_smul' := fun z x => Corner.val_injective (hFsmul z x)
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun b => (hF b).2⟩
  · refine (Corner.nonneg_map_val_iff k _).mp ?_
    have hcp2 : ∀ (N : ℕ) (X : CStarMatrix (Fin N) (Fin N) B'), 0 ≤ X →
        0 ≤ X.map ⇑Flin := ((Theses.A.CStar.cp_iff Flin).out 0 1).mp hFcp
    refine (hcp2 k M hM).trans_eq ?_
    ext i j
    rw [CStarMatrix.map_apply, CStarMatrix.map_apply, CStarMatrix.map_apply]
    rfl
  · -- (7) normality: the thesis's own route, through **81IX**.  `f` carries
    -- the effects of `ℬ` into `d*(𝒜)₁d`, on which `a ↦ d*∖a/d` is
    -- ultraweakly continuous (`div_uwc`), so `F` is ultraweakly continuous
    -- on the effects and hence normal by **44XV** (2) ⇒ (3).
    have hFdiv : ∀ b : B', F b = ldiv (star d) (div ((f b : A)) d) := by
      intro b
      rw [← (hF b).2]
      exact (hinv _ (hF b).1).symm
    have hmaps : Set.MapsTo (fun b : B' => (f b : A)) (effects B')
        {a : A | ∃ e : A, ‖e‖ ≤ 1 ∧ a = star d * e * d} := by
      intro b hb
      obtain ⟨e, hen, he⟩ := hposmem b hb.1
      exact ⟨e, hen.trans (norm_le_one_of_mem_effects hb), he⟩
    have hfcont : @Continuous B' A (ultraweak B') (ultraweak A)
        (fun b : B' => (f b : A)) :=
      ((p_uwcont (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)).out 2 0).mp
        f.preservesDirSups'
    have hFcont : @ContinuousOn B' A (ultraweak B') (ultraweak A)
        (fun b : B' => F b) (effects B') := by
      letI : TopologicalSpace B' := ultraweak B'
      letI : TopologicalSpace A := ultraweak A
      exact (ContinuousOn.comp (div_uwc d (star d)).2 hfcont.continuousOn
        hmaps).congr fun b _ => (hFdiv b).symm
    have hFn : PreservesDirSups (fun b : B' => F b) :=
      preservesDirSups_of_continuousOn_effects
        ({ toLinearMap := Flin, monotone' := fun _ _ h => hFmono h } : B' →ₚ[ℂ] A)
        hFcont
    intro D s hne hdir hlub
    refine Corner.isLUB_of_isLUB_image_val ?_
    rw [Set.image_image]
    exact hFn D s hne hdir hlub

/-- **96V** (`canonical-filter`, proc.tex:414, Proposition), in the general
form in which parsec 980 uses it: *any* ncp-map `c : e𝒜e → 𝒜` of the shape
`a ↦ d*ad`, with `e` the range projection `⌊d⌉`, is a filter.
`canonical_filter` is the case `e = ⌊d⌉` on the nose, and
`isFilter_stdFilter` (the standard filter `c_p` of 98I) is `d = √p`; the
detour through an arbitrary `e` avoids having to transport along
`⌊√p⌉ = ⌈p⌉` inside the dependent type `Corner A e`. -/
theorem isFilter_ad [VonNeumannAlgebra A] (d e : A) [Fact (IsStarProjection e)]
    (he : e = rangeProj d) (c : NCPMap (Corner A e) A)
    (hc : ∀ a : Corner A e, (c a : A) = star d * a.val * d) : IsFilter c := by
  subst he
  have hqd : rangeProj d * d = d := (ceill_basic_2 d).1.2
  have hdq : star d * rangeProj d = star d := by
    have h := congrArg star hqd
    rwa [star_mul, (isStarProjection_rangeProj d).isSelfAdjoint.star_eq] at h
  have hc1 : (c 1 : A) = star d * d := by
    rw [hc 1, Corner.val_one, hdq]
  refine ⟨fun B' _ _ _ _ f hf1 => ?_⟩
  rw [hc1] at hf1
  obtain ⟨g, hg⟩ := canonicalFilter_factor d f hf1
  refine ⟨g, fun b => ?_, fun g' hg' => ?_⟩
  · rw [hc (g b), hg b]
  · refine DFunLike.ext _ _ fun b => Corner.val_injective ?_
    have h1 := hg' b
    rw [hc] at h1
    have h2 : star d * (g' b).val * d = star d * (g b).val * d := by
      rw [← h1, hg b]
    exact mult_cancellation_3 d _ _ (g' b).property (g b).property h2

/-- **96V** (`canonical-filter`, proc.tex:414, Proposition): the map
`c(a) = d* a d : ⌊d⌉𝒜⌊d⌉ → 𝒜` is a filter. -/
theorem canonical_filter [VonNeumannAlgebra A] (d : A) :
    IsFilter (canonicalFilter d) :=
  isFilter_ad d (rangeProj d) rfl (canonicalFilter d) (canonicalFilter_apply d)

/-- Infrastructure for **98II**.2 (proc.tex:588, "by proving first that
`c_p` is injective using `mult-cancellation`"): `a ↦ d*ad` is injective on
`⌊d⌉𝒜⌊d⌉`.  This is **60VIII**.3 verbatim. -/
theorem ad_injective [VonNeumannAlgebra A] (d e : A) (he : e = rangeProj d)
    {x y : A} (hx : e * x * e = x) (hy : e * y * e = y)
    (h : star d * x * d = star d * y * d) : x = y := by
  subst he
  exact mult_cancellation_3 d _ _ hx hy h

/-- Infrastructure for **98II**.3 (proc.tex:594, "by proving first that
`c_p` is bipositive using `sequential-douglas`"): `a ↦ d*ad` is bipositive
on `⌊d⌉𝒜⌊d⌉`.  Positivity of `d*∖(d*ad)/d = a` is **81VI**.2. -/
theorem ad_bipositive [VonNeumannAlgebra A] (d e : A) (he : e = rangeProj d)
    {x : A} (hx : e * x * e = x) (h : 0 ≤ star d * x * d) : 0 ≤ x := by
  subst he
  have h2 := sequential_douglas_2 (star d * x * d) d h ⟨x, rfl⟩
  rwa [ldiv_div_ad d x hx] at h2

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

/-- Auxiliary: `⌈p⌉ = ⌊√p⌉` for positive `p` (both are `⌈√p √p⌉`). -/
theorem ceil_eq_rangeProj_sqrt [VonNeumannAlgebra A] {p : A} (hp : 0 ≤ p) :
    ceil p = rangeProj (CFC.sqrt p) := by
  rw [rangeProj, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq,
    CFC.sqrt_mul_sqrt_self p hp]

/-- **96V** for the standard filter: `c_p` **is** a filter, for every
positive `p`.  This is `isFilter_ad` at `d = √p`, using `⌈p⌉ = ⌊√p⌉`; the
whole of parsec 980 rests on it. -/
theorem isFilter_stdFilter [VonNeumannAlgebra A] (p : A) (hp : 0 ≤ p) :
    IsFilter (stdFilter p) := by
  refine isFilter_ad (CFC.sqrt p) (ceil p) (ceil_eq_rangeProj_sqrt hp)
    (stdFilter p) fun a => ?_
  rw [stdFilter_apply, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq]

/-- `c_p(1) = p`: the standard filter is a filter **for** `p`. -/
theorem stdFilter_one [VonNeumannAlgebra A] {p : A} (hp : 0 ≤ p) :
    (stdFilter p 1 : A) = p := by
  have h : ceil p * CFC.sqrt p = CFC.sqrt p := by
    rw [ceil_eq_rangeProj_sqrt hp]
    exact (ceill_basic_2 (CFC.sqrt p)).1.2
  rw [stdFilter_apply, Corner.val_one]
  rw [show CFC.sqrt p * ceil p = CFC.sqrt p from by
    have h2 := congrArg star h
    rwa [star_mul, (isStarProjection_ceil p).isSelfAdjoint.star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq] at h2]
  exact CFC.sqrt_mul_sqrt_self p hp

/-- **98II**.2, first half, for the standard filter (the exercise's own
hint): `c_p` is injective, by **60VIII** `mult-cancellation`. -/
theorem stdFilter_injective [VonNeumannAlgebra A] {p : A} (hp : 0 ≤ p) :
    Function.Injective ⇑(stdFilter p) := by
  intro x y h
  rw [stdFilter_apply, stdFilter_apply] at h
  refine Corner.val_injective
    (ad_injective (CFC.sqrt p) (ceil p) (ceil_eq_rangeProj_sqrt hp)
      x.property y.property ?_)
  rwa [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq]

/-- **98II**.3 for the standard filter (the exercise's own hint): `c_p` is
bipositive, by **81VI**.2 `sequential-douglas`. -/
theorem stdFilter_bipositive [VonNeumannAlgebra A] {p : A} (hp : 0 ≤ p)
    (x : Corner A (ceil p)) : 0 ≤ (stdFilter p x : A) ↔ 0 ≤ x := by
  have hsa : star (CFC.sqrt p) = CFC.sqrt p :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  rw [stdFilter_apply]
  constructor
  · intro h
    have h2 : 0 ≤ star (CFC.sqrt p) * x.val * CFC.sqrt p := by rwa [hsa]
    exact ad_bipositive (CFC.sqrt p) (ceil p) (ceil_eq_rangeProj_sqrt hp)
      x.property h2
  · intro h
    have h1 : (0 : A) ≤ x.val := h
    have h2 := star_left_conjugate_nonneg h1 (CFC.sqrt p)
    rwa [hsa] at h2

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
        (∀ x : C, c x = stdFilter (c 1) (β x)) → β = α) := by
  -- Both universal properties are now available: `c_p` is a filter for
  -- `p = c(1)` (96V via `isFilter_stdFilter`) and `c` is one by hypothesis,
  -- and `c(1) = p = c_p(1)`, so each factors through the other; the two
  -- uniqueness clauses make the factorisations mutually inverse.
  have hp : (0 : A) ≤ c 1 := ncpMap_nonneg c zero_le_one
  have hone : (stdFilter (c 1) 1 : A) = c 1 := stdFilter_one hp
  obtain ⟨α, hα, huniqα⟩ :=
    (isFilter_stdFilter (c 1) hp).universal C c (by rw [hone])
  obtain ⟨β, hβ, -⟩ :=
    hc.universal (Corner A (ceil (c 1))) (stdFilter (c 1)) (by rw [hone])
  obtain ⟨c₀, -, huniqC⟩ := hc.universal C c le_rfl
  have hαβ : ∀ y : Corner A (ceil (c 1)), α (β y) = y := by
    intro y
    refine stdFilter_injective hp ?_
    rw [← hα (β y), ← hβ y]
  have hβα : ncpComp β α = ncpId C :=
    (huniqC (ncpComp β α) fun x => by
        rw [ncpComp_apply, ← hβ (α x), ← hα x]).trans
      (huniqC (ncpId C) fun x => by rw [ncpId_apply]).symm
  have hβα' : ∀ x : C, β (α x) = x := fun x => by
    have h := congrArg (fun k : NCPMap C C => k x) hβα
    simpa [ncpComp_apply, ncpId_apply] using h
  have hα1 : α 1 = 1 := by
    refine stdFilter_injective hp ?_
    rw [← hα 1, hone]
  exact ⟨α, hα, hα1, ⟨β, hβα', hαβ⟩, fun γ hγ => huniqα γ hγ⟩

/-- **98II** (`filter-basic`, proc.tex:577, Exercise), part 2: a filter is
injective, faithful (`⌈c⌉ = 1`), and mono in `W*_cp`. -/
theorem filter_basic_2 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (c : NCPMap C A) (hc : IsFilter c) :
    Function.Injective ⇑c ∧ ncpCarrier c = 1 ∧
      ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
        [VonNeumannAlgebra B] (g h : NCPMap B C),
        (∀ b, c (g b) = c (h b)) → g = h := by
  -- The exercise's own route: `c = c_p ∘ α` with `α` an isomorphism (part 1)
  -- and `c_p` injective by `mult-cancellation`; faithfulness and mono are
  -- then formal consequences of injectivity.
  obtain ⟨α, hα, -, ⟨α', hα'1, -⟩, -⟩ := filter_basic_1 c hc
  have hp : (0 : A) ≤ c 1 := ncpMap_nonneg c zero_le_one
  have hinj : Function.Injective ⇑c := by
    intro x y h
    have h1 : (stdFilter (c 1) (α x) : A) = stdFilter (c 1) (α y) := by
      rw [← hα x, ← hα y, h]
    have h2 := stdFilter_injective hp h1
    have h3 := congrArg (fun z => α' z) h2
    rwa [hα'1, hα'1] at h3
  refine ⟨hinj, ?_, fun B _ _ _ _ g h hgh => ?_⟩
  · have hspec := (exists_ncpCarrier c).choose_spec.1
    have h0 : (c (1 - ncpCarrier c) : A) = 0 := hspec.2.1
    have hz : (c (0 : C) : A) = 0 := map_zero c.toCompletelyPositiveMap
    have h1 : (1 : C) - ncpCarrier c = 0 := hinj (h0.trans hz.symm)
    exact (sub_eq_zero.mp h1).symm
  · exact DFunLike.ext _ _ fun b => hinj (hgh b)

/-- **98II** (`filter-basic`, proc.tex:577, Exercise), part 3: a filter is
bipositive. -/
theorem filter_basic_3 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (c : NCPMap C A) (hc : IsFilter c) (x : C) : 0 ≤ c x ↔ 0 ≤ x := by
  -- again `c = c_p ∘ α` with `α` an isomorphism (part 1); `c_p` is
  -- bipositive by `sequential-douglas`, and `α`, `α'` are positive.
  obtain ⟨α, hα, -, ⟨α', hα'1, -⟩, -⟩ := filter_basic_1 c hc
  have hp : (0 : A) ≤ c 1 := ncpMap_nonneg c zero_le_one
  constructor
  · intro h
    rw [hα x] at h
    have h2 := (stdFilter_bipositive hp (α x)).mp h
    have h3 := ncpMap_nonneg α' h2
    rwa [hα'1] at h3
  · intro h
    rw [hα x]
    exact (stdFilter_bipositive hp (α x)).mpr (ncpMap_nonneg α h)

/-- **98III** (`filters-composition`, proc.tex:601, Exercise): the
composition of filters is a filter. -/
theorem filters_composition [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (c : NCPMap C B) (d : NCPMap B A)
    (hc : IsFilter c) (hd : IsFilter d) : IsFilter (ncpComp d c) := by
  -- The obstruction the naive argument runs into is that `f(1) ≤ d(c(1))`
  -- does *not* give `f(1) ≤ d(1)`, because `c(1)` need not be an effect.
  -- It is removed by **rescaling**: `c(1) ≤ l·1` for `l = ‖c(1)‖+1`, so
  -- `f(1) ≤ l·d(1)`, and `l⁻¹f` factors through `d` as `l⁻¹f = d ∘ h`.
  -- Then `h' := l·h` has `d(h'(1)) = f(1) ≤ d(c(1))`, so `h'(1) ≤ c(1)` by
  -- bipositivity of `d` (98II.3), and `h'` factors through `c`.
  refine ⟨fun E _ _ _ _ f hf1 => ?_⟩
  rw [ncpComp_apply] at hf1
  set l : ℝ := ‖(c 1 : B)‖ + 1 with hldef
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hlpos : (0 : ℝ) < l := by
    have : (0 : ℝ) ≤ ‖(c 1 : B)‖ := norm_nonneg _
    simp only [hldef]; linarith
  have hlinv : (0 : ℝ) ≤ l⁻¹ := inv_nonneg.mpr hl0
  -- `c(1) ≤ l·1`
  have hc1l : (c 1 : B) ≤ algebraMap ℂ B ((l : ℝ) : ℂ) := by
    have h1 : (c 1 : B) ≤ algebraMap ℝ B ‖(c 1 : B)‖ :=
      (IsSelfAdjoint.of_nonneg (ncpMap_nonneg c zero_le_one)).le_algebraMap_norm_self
    rw [Theses.A.CStar.algebraMap_real_eq] at h1
    exact h1.trans (Theses.A.CStar.algebraMap_ofReal_mono (by simp [hldef]))
  -- hence `f(1) ≤ d(c(1)) ≤ l·d(1)`
  have hdsmul : ∀ (t : ℝ) (x : B), (d (((t : ℝ) : ℂ) • x) : A) = ((t : ℝ) : ℂ) • d x :=
    fun t x => map_smul d.toCompletelyPositiveMap.toLinearMap _ _
  have hfl : (f 1 : A) ≤ ((l : ℝ) : ℂ) • d 1 := by
    refine hf1.trans ?_
    have hc1l' : (c 1 : B) ≤ ((l : ℝ) : ℂ) • (1 : B) := by
      rwa [← Algebra.algebraMap_eq_smul_one]
    have h : (d (c 1) : A) ≤ d (((l : ℝ) : ℂ) • (1 : B)) :=
      OrderHomClass.mono d.toCompletelyPositiveMap hc1l'
    rwa [hdsmul] at h
  -- `l⁻¹f` factors through `d`
  obtain ⟨f', hf'⟩ := exists_ncpSmul f hlinv
  have hf'1 : (f' 1 : A) ≤ d 1 := by
    have h0 : (0 : A) ≤ ((l⁻¹ : ℝ) : ℂ) • (((l : ℝ) : ℂ) • (d 1 : A) - f 1) :=
      Theses.A.CStar.ofReal_smul_nonneg (sub_nonneg.mpr hfl) hlinv
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hlpos),
      Complex.ofReal_one, one_smul, sub_nonneg] at h0
    rwa [hf' 1]
  obtain ⟨h, hh, -⟩ := hd.universal E f' hf'1
  -- rescale back: `h' = l·h` satisfies `d ∘ h' = f`
  obtain ⟨h', hh'⟩ := exists_ncpSmul h hl0
  have hdh' : ∀ b : E, (d (h' b) : A) = f b := by
    intro b
    rw [hh' b, hdsmul, ← hh b, hf' b, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt hlpos), Complex.ofReal_one, one_smul]
  -- `h'(1) ≤ c(1)`, by bipositivity of `d`
  have hh'1 : (h' 1 : B) ≤ c 1 := by
    have hsub : (d ((c 1 : B) - h' 1) : A) = d (c 1) - d (h' 1) :=
      map_sub d.toCompletelyPositiveMap.toLinearMap _ _
    have h0 : (0 : A) ≤ d ((c 1 : B) - h' 1) := by
      rw [hsub, hdh' 1, sub_nonneg]
      exact hf1
    have := (filter_basic_3 d hd ((c 1 : B) - h' 1)).mp h0
    rwa [sub_nonneg] at this
  obtain ⟨g, hg, -⟩ := hc.universal E h' hh'1
  refine ⟨g, fun b => ?_, fun g' hg' => ?_⟩
  · rw [ncpComp_apply, ← hg b, hdh' b]
  · refine DFunLike.ext _ _ fun b => ?_
    have hinjd : Function.Injective ⇑d := (filter_basic_2 d hd).1
    have hinjc : Function.Injective ⇑c := (filter_basic_2 c hc).1
    refine hinjc (hinjd ?_)
    have h1 := hg' b
    rw [ncpComp_apply] at h1
    rw [← h1, ← hg b, hdh' b]

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
    (hπ : IsCornerMap π) (hτ : IsCornerMap τ) : IsCornerMap (ncpComp τ π) := by
  -- The effect to take is `s := β'(r)`, the transport of `τ`'s effect `r`
  -- along the isomorphism `β : ⌊p⌋𝒜⌊p⌋ ≅ ℬ` of 98IV.1: then `s ≤ ⌊p⌋` and
  -- `π(s) = r`, so `π(1−s) = 1−r` and the maps killing `1−s` are exactly
  -- those that factor through `π` and then through `τ`.  (The exercise's
  -- hint — `⌈τ⌉ ≤ ⌈π(⌈τ∘π⌉^⊥)⌉^⊥` — is the direction one does not need;
  -- see the 98VI row of ERRATA.md.)
  obtain ⟨hπu, p, hp, hπc⟩ := hπ
  obtain ⟨hτu, r, hr, hτc⟩ := hτ
  obtain ⟨β, hβ, hβ1, ⟨β', hβ'β, hββ'⟩, -⟩ := corner_basic_1 p hp π hπc hπu
  have hβinj : Function.Injective ⇑β := fun x y hxy => by rw [← hβ'β x, ← hβ'β y, hxy]
  have hβ'1 : β' 1 = 1 := hβinj (by rw [hββ', hβ1])
  set s : A := (β' r).val with hsdef
  have hsfl : s ≤ floor p := by
    have h : β' r ≤ 1 := by rw [← hβ'1]; exact OrderHomClass.mono β'.toCompletelyPositiveMap hr.2
    have h2 := (Corner.le_def (β' r) 1).mp h
    rwa [Corner.val_one] at h2
  have hs0 : (0 : A) ≤ s := by
    have h : (0 : Corner A (floor p)) ≤ β' r := ncpMap_nonneg β' hr.1
    have h2 := (Corner.le_def 0 (β' r)).mp h
    rwa [show ((0 : Corner A (floor p)) : Corner A (floor p)).val = 0 from rfl] at h2
  have hsp : s ≤ p := hsfl.trans (floor_le hp)
  have hseff : s ∈ effects A := ⟨hs0, hsp.trans hp.2⟩
  have hπs : (π s : B) = r := by
    have hstd : (stdCorner p).toNCPMap s = β' r :=
      Corner.val_injective (by rw [stdCorner_apply]; exact (β' r).property)
    rw [hβ s, hstd, hββ']
  have hπ1s : (π (1 - s) : B) = 1 - r := by
    have hsub : (π (1 - s) : B) = π 1 - π s :=
      map_sub π.toCompletelyPositiveMap.toLinearMap _ _
    rw [hsub, hπu, hπs]
  refine ⟨by rw [ncpComp_apply, hπu, hτu], s, hseff, ?_, ?_⟩
  · rw [ncpComp_apply, hπ1s]
    exact hτc.map_perp
  · intro E _ _ _ _ f hf
    -- `f` kills `1−p` because `s ≤ p`
    have hfp : (f (1 - p) : E) = 0 := by
      refine le_antisymm ?_ (ncpMap_nonneg f (sub_nonneg.mpr hp.2))
      have h : (f (1 - p) : E) ≤ f (1 - s) :=
        OrderHomClass.mono f.toCompletelyPositiveMap (sub_le_sub_left hsp 1)
      rwa [hf] at h
    obtain ⟨f₁, hf₁, -⟩ := hπc.universal E f hfp
    have hf₁r : (f₁ (1 - r) : E) = 0 := by rw [← hπ1s, ← hf₁, hf]
    obtain ⟨g, hg, -⟩ := hτc.universal E f₁ hf₁r
    refine ⟨g, fun a => ?_, fun g' hg' => ?_⟩
    · rw [ncpComp_apply, ← hg, ← hf₁]
    · -- uniqueness: `τ ∘ π` is surjective (98IV.2)
      have hsπ : Function.Surjective ⇑π := (corner_basic_2 p hp π hπc hπu).1
      have hsτ : Function.Surjective ⇑τ := (corner_basic_2 r hr τ hτc hτu).1
      refine DFunLike.ext _ _ fun y => ?_
      obtain ⟨b, rfl⟩ := hsτ y
      obtain ⟨a, rfl⟩ := hsπ b
      have h1 := hg' a
      rw [ncpComp_apply] at h1
      rw [← h1, ← hg, ← hf₁]

/-- Auxiliary: `⌊e⌋ = e` for a projection `e`. -/
theorem floor_of_isStarProjection [VonNeumannAlgebra A] {e : A}
    (he : IsStarProjection e) : floor e = e :=
  le_antisymm (floor_le ⟨he.nonneg, he.le_one⟩)
    ((floor_spec ⟨he.nonneg, he.le_one⟩).2.2 e he he.isIdempotentElem.eq)

/-- The corner projection onto a *projection* `e` is a corner of `e`: this is
`isCornerOf_stdCorner` at `p = e`, transported along `⌊e⌋ = e` (the extra
argument `u` carries the transport, since `Corner A u` is a dependent
type). -/
theorem isCornerOf_cornerProjMap [VonNeumannAlgebra A] (e u : A)
    [Fact (IsStarProjection u)] (he : IsStarProjection e) (h : floor e = u) :
    IsCornerOf e (cornerProjMap u).toNCPMap := by
  subst h
  exact isCornerOf_stdCorner e ⟨he.nonneg, he.le_one⟩

/-- **98VII** (`filter-corner`, proc.tex:642, Theorem): given an ncp-map
`f : 𝒜 → ℬ`, a projection `e` with `⌈f⌉ ≤ e`, and a positive `p` with
`f(1) ≤ p`, there is a unique ncp-map `g : e𝒜e → ⌈p⌉ℬ⌈p⌉` with
`c_p ∘ g ∘ π_e = f`; it is given by `g(a) = √p \ f(a) / √p`. -/
theorem filter_corner [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : A) [Fact (IsStarProjection e)]
    (hce : ncpCarrier f ≤ e) (p : B) (hp : 0 ≤ p) (hfp : f 1 ≤ p) :
    ∃! g : NCPMap (Corner A e) (Corner B (ceil p)),
      ∀ a : A, f a = stdFilter p (g ((cornerProjMap e).toNCPMap a)) := by
  -- The thesis's proof (proc.tex:678) verbatim: `π_e` is a corner of `e` and
  -- `f(e^⊥) = 0`, so `f = h ∘ π_e` for a unique `h`; `h(1) = f(1) ≤ p = c_p(1)`
  -- and `c_p` is a filter (96V), so `h = c_p ∘ g` for a unique `g`.
  -- Uniqueness is `π_e` epi (98IV.2, here directly: `π_e` is surjective) and
  -- `c_p` mono (98II.2, here directly: `c_p` is injective).
  have he : IsStarProjection e := Corner.proj e
  have hcspec : IsStarProjection (ncpCarrier f) ∧ (f (1 - ncpCarrier f) : B) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → ncpCarrier f ≤ q :=
    (exists_ncpCarrier f).choose_spec.1
  have hsub : ∀ x y : A, (f (x - y) : B) = f x - f y :=
    fun x y => map_sub f.toCompletelyPositiveMap x y
  have hfe : (f (1 - e) : B) = 0 := by
    refine le_antisymm ?_ (ncpMap_nonneg f (sub_nonneg.mpr he.le_one))
    have h1 : (0 : B) ≤ f (1 - ncpCarrier f - (1 - e)) :=
      ncpMap_nonneg f (by
        have h2 : (1 : A) - ncpCarrier f - (1 - e) = e - ncpCarrier f := by abel
        rw [h2]
        exact sub_nonneg.mpr hce)
    rw [hsub, sub_nonneg, hcspec.2.1] at h1
    exact h1
  obtain ⟨h, hh, -⟩ :=
    (isCornerOf_cornerProjMap e e he (floor_of_isStarProjection he)).universal B f hfe
  have hh1 : (h 1 : B) ≤ p := by
    have h1 : ((cornerProjMap e).toNCPMap 1 : Corner A e) = 1 := (cornerProjMap e).unital'
    have h2 := hh 1
    rw [h1] at h2
    rw [← h2]
    exact hfp
  obtain ⟨g, hg, -⟩ := (isFilter_stdFilter p hp).universal (Corner A e) h
    (by rw [stdFilter_one hp]; exact hh1)
  refine ⟨g, fun a => ?_, fun g' hg' => ?_⟩
  · rw [hh a, hg]
  · refine DFunLike.ext _ _ fun x => ?_
    have hsurj : (cornerProjMap e).toNCPMap x.val = x :=
      Corner.val_injective (by rw [cornerProjMap_apply]; exact x.property)
    refine stdFilter_injective hp ?_
    calc (stdFilter p (g' x) : B)
        = stdFilter p (g' ((cornerProjMap e).toNCPMap x.val)) := by rw [hsurj]
      _ = f x.val := (hg' x.val).symm
      _ = h ((cornerProjMap e).toNCPMap x.val) := hh x.val
      _ = stdFilter p (g ((cornerProjMap e).toNCPMap x.val)) := hg _
      _ = stdFilter p (g x) := by rw [hsurj]

/-- **98VII** (`filter-corner`, proc.tex:642, Theorem), formula: the unique
`g` above is given by `g(a) = √p \ f(a) / √p`. -/
theorem filter_corner_formula [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : A) [Fact (IsStarProjection e)]
    (hce : ncpCarrier f ≤ e) (p : B) (hp : 0 ≤ p) (hfp : f 1 ≤ p)
    (g : NCPMap (Corner A e) (Corner B (ceil p)))
    (hg : ∀ a : A, f a = stdFilter p (g ((cornerProjMap e).toNCPMap a))) :
    ∀ x : Corner A e,
      (g x).val = ldiv (CFC.sqrt p) (div (f x.val) (CFC.sqrt p)) := by
  intro x
  have hsa : star (CFC.sqrt p) = CFC.sqrt p :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  have hsurj : (cornerProjMap e).toNCPMap x.val = x :=
    Corner.val_injective (by rw [cornerProjMap_apply]; exact x.property)
  have hval : (f x.val : B) = CFC.sqrt p * (g x).val * CFC.sqrt p := by
    rw [hg x.val, hsurj, stdFilter_apply]
  have hcorner : rangeProj (CFC.sqrt p) * (g x).val * rangeProj (CFC.sqrt p)
      = (g x).val := by
    rw [← ceil_eq_rangeProj_sqrt hp]
    exact (g x).property
  have hkey := ldiv_div_ad (CFC.sqrt p) (g x).val hcorner
  rw [hsa] at hkey
  rw [hval]
  exact hkey.symm

/-- **98IX** (`square-f`, proc.tex:698, Corollary), well-definedness: for
an ncp-map `f : 𝒜 → ℬ` the formula `a ↦ √f(1) \ f(a) / √f(1)` gives an
ncp-map `⌈f⌉𝒜⌈f⌉ → ⌈f(1)⌉ℬ⌈f(1)⌉`; by choice `sqBracket`, the map
`[f]`. -/
theorem exists_sqBracket [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    ∃ g : NCPMap (Corner A (ncpCarrier f)) (Corner B (ceil (f 1))),
      ∀ a : Corner A (ncpCarrier f),
        (g a).val = ldiv (CFC.sqrt (f 1)) (div (f a.val) (CFC.sqrt (f 1))) := by
  -- **98IX** is **98VII** at `e = ⌈f⌉` and `p = f(1)`.
  have hp : (0 : B) ≤ f 1 := ncpMap_nonneg f zero_le_one
  obtain ⟨g, hg, -⟩ := filter_corner f (ncpCarrier f) le_rfl (f 1) hp le_rfl
  exact ⟨g, filter_corner_formula f (ncpCarrier f) le_rfl (f 1) hp le_rfl g hg⟩

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
    sqBracket f 1 = 1 ∧ ncpCarrier (sqBracket f) = 1 := by
  -- `[f]` is the `g` of **98VII** at `e = ⌈f⌉`, `p = f(1)`; it is pinned down
  -- by the *formula*, which determines its values, so it coincides with that
  -- `g` and inherits the square and its uniqueness.  Unitality is
  -- `c_p([f](1)) = f(1) = p = c_p(1)` plus injectivity of `c_p`.
  -- Faithfulness: if `[f](x) = 0` for `0 ≤ x ∈ ⌈f⌉𝒜⌈f⌉` then `f(x) = 0`,
  -- so `f(⌈x⌉) = 0` by 60V, so `⌈f⌉ ≤ ⌈x⌉^⊥` by minimality of the carrier,
  -- while `⌈x⌉ ≤ ⌈f⌉`; hence `⌈x⌉ = 0` and `x = 0`.
  have hp : (0 : B) ≤ f 1 := ncpMap_nonneg f zero_le_one
  have hcspec : IsStarProjection (ncpCarrier f) ∧ (f (1 - ncpCarrier f) : B) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → ncpCarrier f ≤ q :=
    (exists_ncpCarrier f).choose_spec.1
  obtain ⟨g, hg, hgu⟩ := filter_corner f (ncpCarrier f) le_rfl (f 1) hp le_rfl
  have hform := filter_corner_formula f (ncpCarrier f) le_rfl (f 1) hp le_rfl g hg
  have hsq : ∀ x : Corner A (ncpCarrier f),
      (sqBracket f x).val
        = ldiv (CFC.sqrt (f 1)) (div (f x.val) (CFC.sqrt (f 1))) :=
    (exists_sqBracket f).choose_spec
  have heq : sqBracket f = g := by
    refine DFunLike.ext _ _ fun x => Corner.val_injective ?_
    rw [hsq x, hform x]
  refine ⟨by rw [heq]; exact hg, fun g₂ hg₂ => by rw [heq]; exact hgu g₂ hg₂, ?_, ?_⟩
  · rw [heq]
    refine stdFilter_injective hp ?_
    have h1 : ((cornerProjMap (ncpCarrier f)).toNCPMap 1 :
        Corner A (ncpCarrier f)) = 1 := (cornerProjMap (ncpCarrier f)).unital'
    have h2 := hg 1
    rw [h1] at h2
    rw [← h2, stdFilter_one hp]
  · -- faithfulness
    have hspec : IsStarProjection (ncpCarrier (sqBracket f)) ∧
        (sqBracket f (1 - ncpCarrier (sqBracket f)) :
          Corner B (ceil (f 1))) = 0 ∧
        ∀ q : Corner A (ncpCarrier f), IsStarProjection q →
          sqBracket f (1 - q) = 0 → ncpCarrier (sqBracket f) ≤ q :=
      (exists_ncpCarrier (sqBracket f)).choose_spec.1
    set x : Corner A (ncpCarrier f) := 1 - ncpCarrier (sqBracket f) with hxdef
    have hsurj : (cornerProjMap (ncpCarrier f)).toNCPMap x.val = x :=
      Corner.val_injective (by rw [cornerProjMap_apply]; exact x.property)
    have hfx : (f x.val : B) = 0 := by
      have h3 := hg x.val
      rw [hsurj, ← heq, hspec.2.1] at h3
      rw [h3]
      exact map_zero (stdFilter (f 1)).toCompletelyPositiveMap
    have hxnn : (0 : Corner A (ncpCarrier f)) ≤ x :=
      sub_nonneg.mpr hspec.1.le_one
    have hxpos : (0 : A) ≤ x.val := hxnn
    have hxq : x.val * ncpCarrier f = x.val := by
      have hpp : ncpCarrier f * ncpCarrier f = ncpCarrier f :=
        (Corner.proj (ncpCarrier f)).isIdempotentElem.eq
      calc x.val * ncpCarrier f
          = ncpCarrier f * x.val * (ncpCarrier f * ncpCarrier f) := by
            conv_lhs => rw [← x.property]
            noncomm_ring
        _ = ncpCarrier f * x.val * ncpCarrier f := by rw [hpp]
        _ = x.val := x.property
    have hsle : ceil x.val ≤ ncpCarrier f :=
      ((ceil_basic_1 x.val (ncpCarrier f) hxpos hcspec.1).out 1 2).mp hxq
    have hFF : ∀ a : A,
        (PositiveLinearMap.ofClass f.toCompletelyPositiveMap a : B) = f a :=
      fun _ => rfl
    have hceil := ncp_ceil (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' x.val hxpos
    simp only [hFF] at hceil
    rw [hfx, ceil_zero] at hceil
    have hfs : (f (ceil x.val) : B) = 0 :=
      (ceil_basic_3 _ (ncpMap_nonneg f (isStarProjection_ceil x.val).nonneg)).mpr
        hceil.symm
    have hle : ncpCarrier f ≤ 1 - ceil x.val := by
      refine hcspec.2.2 (1 - ceil x.val) (isStarProjection_ceil x.val).one_sub ?_
      have h4 : (1 : A) - (1 - ceil x.val) = ceil x.val := by abel
      rw [h4]
      exact hfs
    have hsp := isStarProjection_ceil x.val
    have hc0 : ceil x.val = 0 := by
      -- `s ≤ s^⊥` conjugated by `s` gives `s = s³ ≤ s s^⊥ s = 0`
      have hconj := star_left_conjugate_le_conjugate (hsle.trans hle) (ceil x.val)
      rw [hsp.isSelfAdjoint.star_eq] at hconj
      have hL : ceil x.val * ceil x.val * ceil x.val = ceil x.val := by
        rw [hsp.isIdempotentElem.eq, hsp.isIdempotentElem.eq]
      have hR : ceil x.val * (1 - ceil x.val) * ceil x.val = 0 := by
        have h5 : ceil x.val * (1 - ceil x.val) * ceil x.val
            = ceil x.val * ceil x.val
              - ceil x.val * ceil x.val * ceil x.val := by noncomm_ring
        rw [h5, hL, hsp.isIdempotentElem.eq, sub_self]
      rw [hL, hR] at hconj
      exact le_antisymm hconj hsp.nonneg
    have hx0 : x = 0 :=
      Corner.val_injective ((ceil_basic_3 x.val hxpos).mpr hc0)
    rw [hxdef] at hx0
    exact (sub_eq_zero.mp hx0).symm

/-- An ncp-map commutes with subtraction (it is linear; `NCPMap` carries no
`AddMonoidHomClass` instance, so this goes through its
`CompletelyPositiveMap`). -/
private theorem ncpMap_sub (f : NCPMap A B) (x y : A) : f (x - y) = f x - f y :=
  map_sub f.toCompletelyPositiveMap x y

/-- An ncp-map is monotone. -/
private theorem ncpMap_mono (f : NCPMap A B) {x y : A} (h : x ≤ y) :
    f x ≤ f y := by
  have h0 : (0 : B) ≤ f (y - x) := ncpMap_nonneg f (sub_nonneg.mpr h)
  rw [ncpMap_sub, sub_nonneg] at h0
  exact h0

/-- For positive `b` and a projection `e`: `⌈b⌉ ≤ e^⊥` iff `e b e = 0`
(proc.tex:1063).  Left to right is 59III (`ceil-basic`); right to left
factors `ebe = (√b e)*(√b e)`. -/
theorem ceil_le_perp_iff [VonNeumannAlgebra B] {b e : B} (hb : 0 ≤ b)
    (he : IsStarProjection e) : ceil b ≤ 1 - e ↔ e * b * e = 0 := by
  constructor
  · intro h
    have h1 : b * (1 - e) = b := ((ceil_basic_1 b (1 - e) hb he.one_sub).out 2 1).mp h
    rw [mul_sub, mul_one, sub_eq_self] at h1
    rw [mul_assoc, h1, mul_zero]
  · intro h
    have hs : star (CFC.sqrt b) = CFC.sqrt b :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq
    have hz : CFC.sqrt b * e = 0 := by
      refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
      rw [star_mul, hs, he.isSelfAdjoint.star_eq]
      calc e * CFC.sqrt b * (CFC.sqrt b * e)
          = e * (CFC.sqrt b * CFC.sqrt b) * e := by noncomm_ring
        _ = e * b * e := by rw [CFC.sqrt_mul_sqrt_self b hb]
        _ = 0 := h
    have hbe : b * e = 0 := by
      rw [← CFC.sqrt_mul_sqrt_self b hb, mul_assoc, hz, mul_zero]
    refine ((ceil_basic_1 b (1 - e) hb he.one_sub).out 1 2).mp ?_
    rw [mul_sub, mul_one, hbe, sub_zero]

/-- A positive element below both a projection `p` and its complement is
`0`: conjugating by `p^⊥` and by `p` gives `⌈x⌉ ≤ p` and `⌈x⌉ ≤ p^⊥`
(59III), i.e. `px = x` and `(1-p)x = x`. -/
private theorem eq_zero_of_le_proj_le_perp [VonNeumannAlgebra A] {x p : A}
    (hx : 0 ≤ x) (hp : IsStarProjection p) (h1 : x ≤ p) (h2 : x ≤ 1 - p) :
    x = 0 := by
  have hc1 : (1 - p) * x * (1 - p) = 0 := by
    have hle : (1 - p) * x * (1 - p) ≤ (1 - p) * p * (1 - p) := by
      have := star_left_conjugate_le_conjugate h1 (1 - p)
      rwa [star_sub, star_one, hp.isSelfAdjoint.star_eq] at this
    have hzero : (1 - p) * p * (1 - p) = 0 := by
      have hpp : p * p = p := hp.isIdempotentElem
      noncomm_ring [hpp]
    rw [hzero] at hle
    have hge : (0 : A) ≤ (1 - p) * x * (1 - p) := by
      have := star_left_conjugate_nonneg hx (1 - p)
      rwa [star_sub, star_one, hp.isSelfAdjoint.star_eq] at this
    exact le_antisymm hle hge
  have hc2 : p * x * p = 0 := by
    have hle : p * x * p ≤ p * (1 - p) * p := by
      have := star_left_conjugate_le_conjugate h2 p
      rwa [hp.isSelfAdjoint.star_eq] at this
    have hzero : p * (1 - p) * p = 0 := by
      have hpp : p * p = p := hp.isIdempotentElem
      noncomm_ring [hpp]
    rw [hzero] at hle
    have hge : (0 : A) ≤ p * x * p := by
      have := star_left_conjugate_nonneg hx p
      rwa [hp.isSelfAdjoint.star_eq] at this
    exact le_antisymm hle hge
  have hce1 : ceil x ≤ p := by
    have := (ceil_le_perp_iff hx hp.one_sub).mpr hc1
    rwa [sub_sub_cancel] at this
  have hce2 : ceil x ≤ 1 - p := (ceil_le_perp_iff hx hp).mpr hc2
  have e1 : p * x = x := ((ceil_basic_1 x p hx hp).out 2 0).mp hce1
  have e2 : (1 - p) * x = x :=
    ((ceil_basic_1 x (1 - p) hx hp.one_sub).out 2 0).mp hce2
  have h3 : (1 - p) * x = x - p * x := by noncomm_ring
  rw [h3, e1, sub_self] at e2
  exact e2.symm

/-- A *unital* ncp-isomorphism maps projections to projections: `e := f(p)`
is an effect, so `d := e - e²` is positive and below both `e` and `e^⊥`;
`g(d)` is then below both `p` and `p^⊥`, hence `0`, and `g` is injective,
so `e² = e`. -/
private theorem isStarProjection_map [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NCPMap A B) (g : NCPMap B A)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) (hfu : f 1 = 1)
    (hgu : g 1 = 1) {p : A} (hp : IsStarProjection p) :
    IsStarProjection (f p) := by
  set e : B := f p with he
  have he0 : (0 : B) ≤ e := ncpMap_nonneg f hp.nonneg
  have he1 : e ≤ 1 := by
    have := ncpMap_mono f hp.le_one
    rwa [hfu] at this
  have hd0 : (0 : B) ≤ e - e * e := sub_nonneg.mpr (mul_self_le_self ⟨he0, he1⟩)
  have hsq : (0 : B) ≤ e * e := by
    have := star_mul_self_nonneg e
    rwa [(IsSelfAdjoint.of_nonneg he0).star_eq] at this
  have hd1 : e - e * e ≤ e := by
    have : e - e * e ≤ e - 0 := sub_le_sub_left hsq e
    simpa using this
  have hd2 : e - e * e ≤ 1 - e := by
    have hns : (0 : B) ≤ (1 - e) * (1 - e) := by
      have := star_mul_self_nonneg (1 - e)
      rwa [star_sub, star_one, (IsSelfAdjoint.of_nonneg he0).star_eq] at this
    have hexp : (1 - e) * (1 - e) = (1 - e) - (e - e * e) := by noncomm_ring
    rw [hexp, sub_nonneg] at hns
    exact hns
  have hginj : Function.Injective ⇑g := fun x y hxy => by
    rw [← hfg x, ← hfg y, hxy]
  have hgd : g (e - e * e) = 0 := by
    refine eq_zero_of_le_proj_le_perp (ncpMap_nonneg g hd0) hp ?_ ?_
    · have := ncpMap_mono g hd1
      rwa [he, hgf] at this
    · have hrhs : g (1 - e) = 1 - p := by rw [ncpMap_sub, hgu, he, hgf]
      have := ncpMap_mono g hd2
      rwa [hrhs] at this
  have hd : e - e * e = 0 :=
    hginj (by rw [hgd]; exact (map_zero g.toCompletelyPositiveMap).symm)
  exact ⟨by show e * e = e; rw [sub_eq_zero] at hd; exact hd.symm,
    IsSelfAdjoint.of_nonneg he0⟩

/-! ### Infrastructure for parsecs 990–1040

Linearity, monotonicity and norm-continuity of an ncp-map; norm-density of
the linear span of the projections (**65IV**, `projections-norm-dense`); and
the individual implications of **99II** (`gardner`), which are stated
separately because **99XII** (`sharp-multiplicative`), **99IX** (`iso`) and
**102V** (`nmiu-rigid`) each need some of them for a map that is *not*
assumed unital. -/

/-- An ncp-map is additive. -/
private theorem ncpMap_add (f : NCPMap A B) (x y : A) : f (x + y) = f x + f y :=
  map_add f.toCompletelyPositiveMap x y

/-- An ncp-map sends `0` to `0`. -/
private theorem ncpMap_zero (f : NCPMap A B) : (f 0 : B) = 0 :=
  map_zero f.toCompletelyPositiveMap

/-- An ncp-map is `ℂ`-homogeneous. -/
private theorem ncpMap_smul (f : NCPMap A B) (c : ℂ) (x : A) :
    f (c • x) = c • f x :=
  map_smul f.toCompletelyPositiveMap c x

/-- An ncp-map is norm-continuous: `‖f(a)‖ ≤ ‖f(1)‖ ‖a‖` by **34XVI**
(`cp-russo-dye`). -/
private theorem ncpMap_continuous (f : NCPMap A B) : Continuous ⇑f := by
  have hcp : Theses.A.CStar.IsCompletelyPositiveMap
      (f.toCompletelyPositiveMap.toLinearMap) :=
    ((Theses.A.CStar.cp_iff _).out 1 0).mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  exact AddMonoidHomClass.continuous_of_bound
    (f.toCompletelyPositiveMap.toLinearMap) ‖(f 1 : B)‖
    (fun x => Theses.A.CStar.cp_russo_dye _ hcp x)

/-- **65IV** (`projections-norm-dense`) for arbitrary, not necessarily
self-adjoint, elements: the linear span of the projections of a von Neumann
algebra is norm-dense (split `x = ℜx + i ℑx`). -/
private theorem mem_closure_span_projections [VonNeumannAlgebra A] (x : A) :
    x ∈ closure (Submodule.span ℂ {p : A | IsStarProjection p} : Set A) := by
  have hsa : ∀ y : A, IsSelfAdjoint y →
      y ∈ closure (Submodule.span ℂ {p : A | IsStarProjection p} : Set A) :=
    fun y hy => closure_mono (SetLike.coe_subset_coe.mpr
      (Submodule.span_mono fun p hp => hp.1)) (projections_norm_dense y hy)
  have hx : (realPart x : A) + Complex.I • (imaginaryPart x : A) = x :=
    realPart_add_I_smul_imaginaryPart x
  have hmem : x ∈ Submodule.topologicalClosure
      (Submodule.span ℂ {p : A | IsStarProjection p}) := by
    rw [← hx]
    exact Submodule.add_mem _ (hsa _ (realPart x).2)
      (Submodule.smul_mem _ _ (hsa _ (imaginaryPart x).2))
  exact hmem

/-- A norm-closed `ℂ`-subspace of a von Neumann algebra containing every
projection is the whole algebra (**65IV**). -/
private theorem mem_of_isClosed_of_projections [VonNeumannAlgebra A]
    (S : Submodule ℂ A) (hS : IsClosed (S : Set A))
    (hp : ∀ p : A, IsStarProjection p → p ∈ S) (x : A) : x ∈ S := by
  have hspan : Submodule.span ℂ {p : A | IsStarProjection p} ≤ S :=
    Submodule.span_le.mpr fun p hpp => hp p hpp
  have hmem : x ∈ closure (S : Set A) :=
    closure_mono (SetLike.coe_subset_coe.mpr hspan)
      (mem_closure_span_projections (A := A) x)
  rwa [hS.closure_eq] at hmem

/-- Every value of an ncp-map sits under `⌈f(1)⌉`: `f(x)⌈f(1)⌉ = f(x)`.
By **61II** (`ncp-ceill`), `⌈f(x)⌋ ≤ ⌈f(⌈x⌋)⌉ ≤ ⌈f(1)⌉`. -/
private theorem ncpMap_mul_ceilOne [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (x : A) : (f x : B) * ceil (f 1) = f x := by
  have hs : IsStarProjection (suppProj x) := (ceill_basic_1 x).1.1
  have hle : suppProj (f x : B) ≤ ceil ((f 1 : B)) :=
    (ncp_ceill f x).1.trans
      (ceil_mono (ncpMap_nonneg f hs.nonneg) (ncpMap_mono f hs.le_one))
  have hq : IsStarProjection (ceil ((f 1 : B))) :=
    (ceil_spec (ncpMap_nonneg f zero_le_one)).1
  have hsf : IsStarProjection (suppProj (f x : B)) := (ceill_basic_1 (f x : B)).1.1
  have e : suppProj (f x : B) * ceil ((f 1 : B)) = suppProj (f x : B) :=
    (hsf.le_iff_mul_eq_left hq).mp hle
  calc (f x : B) * ceil ((f 1 : B))
      = (f x * suppProj (f x : B)) * ceil ((f 1 : B)) := by
        rw [(ceill_basic_1 (f x : B)).1.2]
    _ = f x * (suppProj (f x : B) * ceil ((f 1 : B))) := by noncomm_ring
    _ = f x * suppProj (f x : B) := by rw [e]
    _ = f x := (ceill_basic_1 (f x : B)).1.2

/-- **99II** (`gardner`), (1) ⇒ (4): a multiplicative ncp-map maps
projections to projections. -/
private theorem isStarProjection_map_of_mul (f : NCPMap A B)
    (h : ∀ a b : A, f (a * b) = f a * f b) :
    ∀ p : A, IsStarProjection p → IsStarProjection (f p) := fun p hp =>
  ⟨by change (f p : B) * f p = f p; rw [← h p p, hp.isIdempotentElem.eq],
    by change star (f p : B) = f p; rw [← ncp_star f p, hp.isSelfAdjoint.star_eq]⟩

/-- **99II** (`gardner`), (4) ⇒ (5): `⌈f(a)⌉ = ⌈f(⌈a⌉)⌉ = f(⌈a⌉)` by
**60V** (`ncp-ceil`), since `f(⌈a⌉)` is a projection. -/
private theorem ceil_map_of_isStarProjection_map [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NCPMap A B)
    (h : ∀ p : A, IsStarProjection p → IsStarProjection (f p)) :
    ∀ a : A, 0 ≤ a → ceil (f a) = f (ceil a) := by
  intro a ha
  have h3 : ceil ((ncpPositive f) a : B) = ceil ((ncpPositive f) (ceil a) : B) :=
    ncp_ceil (ncpPositive f) f.preservesDirSups' a ha
  simp only [ncpPositive_apply] at h3
  rw [h3, ceil_of_isStarProjection (h (ceil a) (ceil_spec ha).1)]

/-- **99II** (`gardner`), (5) ⇒ (4): `f(p) = f(⌈p⌉) = ⌈f(p)⌉` is a
projection. -/
private theorem isStarProjection_map_of_ceil [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NCPMap A B)
    (h : ∀ a : A, 0 ≤ a → ceil (f a) = f (ceil a)) :
    ∀ p : A, IsStarProjection p → IsStarProjection (f p) := by
  intro p hp
  have hh := h p hp.nonneg
  rw [ceil_of_isStarProjection hp] at hh
  rw [← hh]
  exact (ceil_spec (ncpMap_nonneg f hp.nonneg)).1

/-- **99II** (`gardner`), (4) ⇒ (3), the author's argument: `pq = 0` gives
`p ≤ q^⊥`, so `f(p) ≤ f(1) - f(q) ≤ 1 - f(q)`, and of two projections one
of which is below the other's complement the product is `0`.  Unitality is
not needed — `f(1)` is a projection because `1` is. -/
private theorem gardner_43 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B)
    (h : ∀ p : A, IsStarProjection p → IsStarProjection (f p)) :
    ∀ p q : A, IsStarProjection p → IsStarProjection q → p * q = 0 →
      ceil (f p) * ceil (f q) = 0 := by
  intro p q hp hq hpq
  have hfp := h p hp
  have hfq := h q hq
  have hf1 := h 1 (IsStarProjection.one (R := A))
  rw [ceil_of_isStarProjection hfp, ceil_of_isStarProjection hfq]
  have hple : p ≤ 1 - q :=
    (hp.le_iff_mul_eq_left hq.one_sub).mpr (by rw [mul_sub, mul_one, hpq, sub_zero])
  have h1 : (f p : B) ≤ 1 - f q := by
    have hm := ncpMap_mono f hple
    rw [ncpMap_sub] at hm
    exact hm.trans (sub_le_sub_right hf1.le_one _)
  have h2 := (hfp.le_iff_mul_eq_left hfq.one_sub).mp h1
  rw [mul_sub, mul_one] at h2
  exact sub_eq_self.mp h2

/-- **99II** (`gardner`), (3) ⇒ (2), the author's argument:
`f(a)f(b) = f(a)⌈f(a)⌋⌊f(b)⌉f(b)`, and `⌈f(a)⌋⌊f(b)⌉ = 0` because
`⌈f(a)⌋ ≤ ⌈f(⌈a⌋)⌉`, `⌊f(b)⌉ ≤ ⌈f(⌊b⌉)⌉` (**61II**) and `⌈a⌋⌊b⌉ = 0`
(**60VIII**).  No unitality is needed. -/
private theorem gardner_32 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B)
    (h : ∀ p q : A, IsStarProjection p → IsStarProjection q → p * q = 0 →
      ceil (f p) * ceil (f q) = 0) :
    ∀ a b : A, a * b = 0 → (f a : B) * f b = 0 := by
  intro a b hab
  have hsa : IsStarProjection (suppProj a) := (ceill_basic_1 a).1.1
  have hrb : IsStarProjection (rangeProj b) := (ceill_basic_2 b).1.1
  have h0 : suppProj a * rangeProj b = 0 :=
    ((mult_cancellation_1 b a).out 0 1).mp hab
  have hz := h _ _ hsa hrb h0
  have hc1 : IsStarProjection (ceil ((f (suppProj a) : B))) :=
    (ceil_spec (ncpMap_nonneg f hsa.nonneg)).1
  have hc2 : IsStarProjection (ceil ((f (rangeProj b) : B))) :=
    (ceil_spec (ncpMap_nonneg f hrb.nonneg)).1
  have hsfa : IsStarProjection (suppProj (f a : B)) := (ceill_basic_1 (f a : B)).1.1
  have hrfb : IsStarProjection (rangeProj (f b : B)) := (ceill_basic_2 (f b : B)).1.1
  have e1 : suppProj (f a : B) * ceil ((f (suppProj a) : B)) = suppProj (f a : B) :=
    (hsfa.le_iff_mul_eq_left hc1).mp (ncp_ceill f a).1
  have e2 : ceil ((f (rangeProj b) : B)) * rangeProj (f b : B)
      = rangeProj (f b : B) := by
    have h' := (hrfb.le_iff_mul_eq_left hc2).mp (ncp_ceill f b).2
    have h'' := congrArg star h'
    rwa [star_mul, hc2.isSelfAdjoint.star_eq, hrfb.isSelfAdjoint.star_eq] at h''
  have hzero : suppProj (f a : B) * rangeProj (f b : B) = 0 := by
    calc suppProj (f a : B) * rangeProj (f b : B)
        = (suppProj (f a : B) * ceil ((f (suppProj a) : B)))
          * (ceil ((f (rangeProj b) : B)) * rangeProj (f b : B)) := by rw [e1, e2]
      _ = suppProj (f a : B)
          * (ceil ((f (suppProj a) : B)) * ceil ((f (rangeProj b) : B)))
          * rangeProj (f b : B) := by noncomm_ring
      _ = 0 := by rw [hz, mul_zero, zero_mul]
  exact ((mult_cancellation_1 (f b : B) (f a : B)).out 1 0).mp hzero

/-- **99II** (`gardner`), (2) ⇒ (1), the author's argument.  From
`a e^⊥ e = 0` and `a e e^⊥ = 0` one gets `f(a)f(e) = f(ae)f(e)` and
`f(ae) = f(ae)f(e)` for every projection `e`, hence `f(ae) = f(a)f(e)`;
since the linear span of the projections is norm-dense (**65IV**) and `f`
is norm-continuous, this extends to all of `𝒜`.  Instead of unitality only
`f(1)` being a *projection* is needed (this is what **99XII** uses). -/
private theorem gardner_21 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hq : IsStarProjection (f 1 : B))
    (h2 : ∀ a b : A, a * b = 0 → (f a : B) * f b = 0) :
    ∀ a b : A, (f (a * b) : B) = f a * f b := by
  have key : ∀ (a e : A), IsStarProjection e → (f (a * e) : B) = f a * f e := by
    intro a e he
    have hA : (f (a * (1 - e)) : B) * f e = 0 := by
      refine h2 _ _ ?_
      calc a * (1 - e) * e = a * ((1 - e) * e) := by noncomm_ring
        _ = 0 := by
            rw [sub_mul, one_mul, he.isIdempotentElem.eq, sub_self, mul_zero]
    have hB : (f (a * e) : B) * f (1 - e) = 0 := by
      refine h2 _ _ ?_
      calc a * e * (1 - e) = a * (e * (1 - e)) := by noncomm_ring
        _ = 0 := by
            rw [mul_sub, mul_one, he.isIdempotentElem.eq, sub_self, mul_zero]
    have hone : (f (a * e) : B) * f 1 = f (a * e) := by
      have hc := ncpMap_mul_ceilOne f (a * e)
      rwa [ceil_of_isStarProjection hq] at hc
    have hsplit : a * (1 - e) = a - a * e := by noncomm_ring
    rw [hsplit, ncpMap_sub, sub_mul, sub_eq_zero] at hA
    rw [ncpMap_sub, mul_sub, hone, sub_eq_zero] at hB
    rw [hA, ← hB]
  intro a
  let S : Submodule ℂ A :=
    { carrier := {x : A | (f (a * x) : B) = (f a : B) * f x}
      add_mem' := by
        intro x y hx hy
        replace hx : (f (a * x) : B) = (f a : B) * f x := hx
        replace hy : (f (a * y) : B) = (f a : B) * f y := hy
        change (f (a * (x + y)) : B) = (f a : B) * f (x + y)
        rw [mul_add, ncpMap_add, ncpMap_add, hx, hy, mul_add]
      zero_mem' := by
        change (f (a * 0) : B) = (f a : B) * f 0
        rw [mul_zero, ncpMap_zero, mul_zero]
      smul_mem' := by
        intro c x hx
        replace hx : (f (a * x) : B) = (f a : B) * f x := hx
        change (f (a * (c • x)) : B) = (f a : B) * f (c • x)
        rw [mul_smul_comm, ncpMap_smul, ncpMap_smul, hx, mul_smul_comm] }
  have hclosed : IsClosed (S : Set A) :=
    isClosed_eq ((ncpMap_continuous f).comp (continuous_const.mul continuous_id))
      (continuous_const.mul (ncpMap_continuous f))
  exact fun b => mem_of_isClosed_of_projections S hclosed (fun p hp => key a p hp) b

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
      ∀ a : A, 0 ≤ a → ceil (f a) = f (ceil a) ].TFAE := by
  -- the author's cycle (1) ⇒ (4) ⇒ (3) ⇒ (2) ⇒ (1) with (4) ⇔ (5) on the
  -- side; each implication is one of the private lemmas above.
  have hq : IsStarProjection (f 1 : B) := by
    rw [hu]; exact IsStarProjection.one (R := B)
  tfae_have 1 → 4 := isStarProjection_map_of_mul f
  tfae_have 4 → 5 := ceil_map_of_isStarProjection_map f
  tfae_have 5 → 4 := isStarProjection_map_of_ceil f
  tfae_have 4 → 3 := gardner_43 f
  tfae_have 3 → 2 := gardner_32 f
  tfae_have 2 → 1 := gardner_21 f hq
  tfae_finish

/-- **99IX** (`iso`, proc.tex:878, Theorem): an ncpsu-isomorphism between
von Neumann algebras is an nmiu-isomorphism (unital, multiplicative, and
involution preserving). -/
theorem iso [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPSUMap A B) (g : NCPSUMap B A)
    (hgf : ∀ a, g.toNCPMap (f.toNCPMap a) = a)
    (hfg : ∀ b, f.toNCPMap (g.toNCPMap b) = b) :
    f.toNCPMap 1 = 1 ∧
      (∀ a b : A, f.toNCPMap (a * b) = f.toNCPMap a * f.toNCPMap b) ∧
      (∀ a : A, f.toNCPMap (star a) = star (f.toNCPMap a)) := by
  -- the author's proof: `1 = f(g 1) ≤ f 1 ≤ 1` makes both maps unital;
  -- a unital ncp-isomorphism maps projections to projections
  -- (`isStarProjection_map`), hence is multiplicative by **99II**;
  -- involutivity is `cstar-p-implies-i` (**10IV**).
  have hfu : (f.toNCPMap 1 : B) = 1 := by
    refine le_antisymm f.subunital' ?_
    have h := ncpMap_mono f.toNCPMap g.subunital'
    rwa [hfg 1] at h
  have hgu : (g.toNCPMap 1 : A) = 1 := by
    refine le_antisymm g.subunital' ?_
    have h := ncpMap_mono g.toNCPMap f.subunital'
    rwa [hgf 1] at h
  refine ⟨hfu, gardner_21 f.toNCPMap (by rw [hfu]; exact IsStarProjection.one (R := B))
    (gardner_32 f.toNCPMap (gardner_43 f.toNCPMap fun p hp =>
      isStarProjection_map f.toNCPMap g.toNCPMap hgf hfg hfu hgu hp)),
    fun a => ncp_star f.toNCPMap a⟩

/-! ### Infrastructure for 99XI: the corner inclusion of a *projection* is a
filter

For a *projection* `p` the standard filter `c_p(a) = √p a √p` is just the
inclusion `p𝒜p → 𝒜`, and that is the shape 99XI needs.  It is an instance
of **96V** (`isFilter_ad` at `d = p`, using `⌊p⌉ = p`), which is proved
1200 lines above; `isFilter_cornerIncl` below simply reads it off.

(Until session 94 this section instead proved the universal property from
scratch — an ncp-map `f` with `f(1) ≤ p` already takes its values in the
corner, so it corestricts, uniquely because the inclusion is injective — on
the ground that 96V was "out of reach here, its proof needing
`sequential-douglas`, `div-approx` and `div-usc` (vn.tex 81VI, 81VII,
81IX), all still `sorry` in `A/VN/Division.lean`".  `A/VN/Division.lean` has
no `sorry`.  The elementary route is kept below as
`conj_ncp_eq_of_le_proj`/`exists_ncpCorestrict`, which the corestriction
arguments of 100III and 102VII use in their own right.) -/

/-- If an ncp-map `f : ℬ → 𝒜` satisfies `f(1) ≤ p` for a projection `p`,
then all of its values lie in the corner `p𝒜p`.  For positive `b` this is
`⌈f(b)⌉ ≤ ⌈f(1)⌉ ≤ ⌈p⌉ = p` (using `f(b) ≤ ‖b‖·f(1)`); the general case
follows by linearity (`b = ℜb + i·ℑb`, `y = y⁺ − y⁻`). -/
private theorem conj_ncp_eq_of_le_proj [VonNeumannAlgebra A]
    {B' : Type u} [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [VonNeumannAlgebra B'] {p : A} (hp : IsStarProjection p) (f : NCPMap B' A)
    (hf1 : (f 1 : A) ≤ p) (b : B') : p * f b * p = f b := by
  have hpos : ∀ y : B', 0 ≤ y → p * f y * p = f y := by
    intro y hy
    have hfy : (0 : A) ≤ f y := ncpMap_nonneg f hy
    have hle : ceil (f y) ≤ p := by
      rcases eq_or_lt_of_le (norm_nonneg y) with hn | hn
      · have hy0 : y = 0 := by
          have : ‖y‖ = 0 := hn.symm
          exact norm_eq_zero.mp this
        rw [hy0, ncpMap_zero, ceil_zero]
        exact hp.nonneg
      · have hyle : y ≤ algebraMap ℂ B' ((‖y‖ : ℝ) : ℂ) := by
          rw [← Theses.A.CStar.algebraMap_real_eq]
          exact (IsSelfAdjoint.of_nonneg hy).le_algebraMap_norm_self
        have h1 : (f y : A) ≤ f (algebraMap ℂ B' ((‖y‖ : ℝ) : ℂ)) :=
          ncpMap_mono f hyle
        have h2 : (f (algebraMap ℂ B' ((‖y‖ : ℝ) : ℂ)) : A)
            = ((‖y‖ : ℝ) : ℂ) • f 1 := by
          rw [Algebra.algebraMap_eq_smul_one, ncpMap_smul]
        rw [h2] at h1
        have h3 : ceil (f y) ≤ ceil (((‖y‖ : ℝ) : ℂ) • (f 1 : A)) :=
          ceil_mono hfy h1
        rw [(ceil_basic_4 (f 1) (f 1) (ncpMap_nonneg f zero_le_one)
          (ncpMap_nonneg f zero_le_one) ‖y‖ hn).1] at h3
        refine h3.trans ?_
        have := ceil_mono (ncpMap_nonneg f zero_le_one) hf1
        rwa [ceil_of_isStarProjection hp] at this
    have hr : (f y : A) * p = f y := (ceil_le_iff hfy hp).mp hle
    have hl : p * (f y : A) = f y :=
      ((ceil_basic_1 (f y) p hfy hp).out 2 0).mp hle
    rw [hl, hr]
  have hsa : ∀ y : B', IsSelfAdjoint y → p * f y * p = f y := by
    intro y hy
    have hd : posPart y - negPart y = y := CFC.posPart_sub_negPart y hy
    rw [← hd, ncpMap_sub, mul_sub, sub_mul,
      hpos _ (CFC.posPart_nonneg y), hpos _ (CFC.negPart_nonneg y)]
  have hb : (realPart b : B') + Complex.I • (imaginaryPart b : B') = b :=
    realPart_add_I_smul_imaginaryPart b
  rw [← hb, ncpMap_add, ncpMap_smul, mul_add, add_mul, mul_smul_comm,
    smul_mul_assoc, hsa _ (realPart b).2, hsa _ (imaginaryPart b).2]

/-- Corestriction of an ncp-map along a corner: if every value of
`f : ℬ → 𝒜` lies in `p𝒜p`, then `f` is `val ∘ g` for an ncp-map
`g : ℬ → p𝒜p`. -/
private theorem exists_ncpCorestrict [VonNeumannAlgebra A]
    {B' : Type u} [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [VonNeumannAlgebra B'] (p : A) [Fact (IsStarProjection p)]
    (f : NCPMap B' A) (hf : ∀ b : B', p * f b * p = f b) :
    ∃ g : NCPMap B' (Corner A p), ∀ b : B', (g b).val = f b := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toFun := fun b => ⟨f b, hf b⟩
                map_add' := fun x y => Corner.val_injective (by
                  show (f (x + y) : A) = f x + f y
                  exact ncpMap_add f x y)
                map_smul' := fun z x => Corner.val_injective (by
                  show (f (z • x) : A) = z • f x
                  exact ncpMap_smul f z x)
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · refine (Corner.nonneg_map_val_iff k _).mp ?_
    change (0 : CStarMatrix (Fin k) (Fin k) A) ≤
      (CStarMatrix.map M fun b => (⟨f b, hf b⟩ : Corner A p)).map Corner.val
    have hkey : (CStarMatrix.map M fun b => (⟨f b, hf b⟩ : Corner A p)).map
        Corner.val = M.map ⇑f.toCompletelyPositiveMap.toLinearMap := by
      ext i j
      rw [CStarMatrix.map_apply, CStarMatrix.map_apply, CStarMatrix.map_apply]
      rfl
    rw [hkey]
    exact f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
  · intro D s hne hdir hlub
    refine Corner.isLUB_of_isLUB_image_val ?_
    have h := f.preservesDirSups' D s hne hdir hlub
    rw [← Set.image_comp]
    exact h

/-- The inclusion `p𝒜p → 𝒜` of the corner of a **projection** `p` is a
filter: **96V** (`isFilter_ad`) at `d = p`, since `p*ap = a` for `a ∈ p𝒜p`
and `⌊p⌉ = p`. -/
theorem isFilter_cornerIncl [VonNeumannAlgebra A] (p : A)
    [Fact (IsStarProjection p)] : IsFilter (cornerIncl p).toNCPMap := by
  have hp : IsStarProjection p := Fact.out
  refine isFilter_ad p p (rangeProj_of_isStarProjection hp).symm _ fun a => ?_
  rw [cornerIncl_apply, hp.isSelfAdjoint.star_eq]
  exact a.property.symm

/-- **99XI** (proc.tex:897, Exercise): any filter of a projection is
multiplicative. -/
theorem filter_of_projection_multiplicative [VonNeumannAlgebra A]
    [VonNeumannAlgebra C] (c : NCPMap C A) (hc : IsFilter c)
    (hp : IsStarProjection (c 1)) : ∀ x y : C, c (x * y) = c x * c y := by
  -- The exercise's own hint: `c` is the standard filter of `p := c(1)` up to
  -- an ncpu-isomorphism (98II), which is an nmiu-isomorphism by 99IX `iso`.
  -- Since `p` is a projection the standard filter is the corner inclusion
  -- (`isFilter_cornerIncl`, an instance of 96V), and the two universal
  -- properties give the isomorphism directly — which is 98II.1's own
  -- argument, run at this `c` rather than quoted from it.
  have : Fact (IsStarProjection (c 1)) := ⟨hp⟩
  have hone : ((cornerIncl (c 1)).toNCPMap 1 : A) = c 1 := by
    rw [cornerIncl_apply]; exact Corner.val_one
  obtain ⟨α, hα, -⟩ := (isFilter_cornerIncl (c 1)).universal C c (by rw [hone])
  obtain ⟨β, hβ, -⟩ :=
    hc.universal (Corner A (c 1)) (cornerIncl (c 1)).toNCPMap (by rw [hone])
  obtain ⟨c₀, -, huniqC⟩ := hc.universal C c le_rfl
  -- `α` and `β` are mutually inverse
  have hαβ : ∀ y : Corner A (c 1), α (β y) = y := by
    intro y
    refine Corner.val_injective ?_
    have h1 := hα (β y)
    rw [cornerIncl_apply] at h1
    have h2 := hβ y
    rw [cornerIncl_apply] at h2
    rw [← h1, ← h2]
  have hβα : ncpComp β α = ncpId C := by
    rw [huniqC (ncpComp β α) (fun x => by
        rw [ncpComp_apply, ← hβ (α x), ← hα x]),
      huniqC (ncpId C) (fun x => by rw [ncpId_apply])]
  have hβα' : ∀ x : C, β (α x) = x := fun x => by
    have := congrArg (fun k : NCPMap C C => k x) hβα
    simpa [ncpComp_apply, ncpId_apply] using this
  -- both are unital
  have hα1 : α 1 = 1 := by
    refine Corner.val_injective ?_
    have h1 := hα 1
    rw [cornerIncl_apply] at h1
    rw [← h1, Corner.val_one]
  have hβ1 : β 1 = 1 := by
    have := hβα' 1
    rwa [hα1] at this
  -- `iso` (99IX): a unital ncp-isomorphism is multiplicative
  have hmul := (iso (A := C) (B := Corner A (c 1))
    ⟨α, by change (α 1 : Corner A (c 1)) ≤ 1; rw [hα1]⟩
    ⟨β, by change (β 1 : C) ≤ 1; rw [hβ1]⟩ hβα' hαβ).2.1
  intro x y
  have h1 := hα (x * y)
  rw [cornerIncl_apply] at h1
  have h2 := hα x
  rw [cornerIncl_apply] at h2
  have h3 := hα y
  rw [cornerIncl_apply] at h3
  rw [h1, hmul x y, Corner.val_mul, ← h2, ← h3]

/-- **99XII** (`sharp-multiplicative`, proc.tex:905, Exercise): for an
ncp-map `f` between von Neumann algebras: multiplicative ⟺ sends
projections to projections ⟺ `⌈f(a)⌉ = f(⌈a⌉)` for `a ≥ 0`. -/
theorem sharp_multiplicative [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    [ ∀ a b : A, f (a * b) = f a * f b,
      ∀ p : A, IsStarProjection p → IsStarProjection (f p),
      ∀ a : A, 0 ≤ a → ceil (f a) = f (ceil a) ].TFAE := by
  -- The exercise's own hint, transcribed: factor `f = ζ ∘ h` where `ζ` is a
  -- filter for `f(1)` and `h` is an ncp-map.  Take `ζ = c_{f(1)}` (96V/98I)
  -- and let `h` be the map its universal property provides.  Under (2) the
  -- element `ζ(1) = f(1)` is a projection, so `ζ` is multiplicative by
  -- **99XI**; and `ζ` is injective (**98II**.2), which makes `h` unital and
  -- carries (2) across to `h`.  So `h` is multiplicative by **99II**
  -- `gardner` — in its *unital* form, which is the point of the hint — and
  -- hence so is `f = ζ ∘ h`.
  -- (Until session 94 this went straight to the implications of 99II at the
  -- non-unital `f`, on the ground that **98II** `filter-basic` was "still
  -- `sorry`"; `filter_basic_1`/`_2`/`_3` are proved 1000 lines above.)
  tfae_have 1 → 2 := isStarProjection_map_of_mul f
  tfae_have 2 → 3 := ceil_map_of_isStarProjection_map f
  tfae_have 3 → 2 := isStarProjection_map_of_ceil f
  tfae_have 2 → 1 := by
    intro h
    have hf0 : (0 : B) ≤ f 1 := ncpMap_nonneg f zero_le_one
    have hζ : IsFilter (stdFilter (f 1)) := isFilter_stdFilter (f 1) hf0
    have hζ1 : (stdFilter (f 1) 1 : B) = f 1 := stdFilter_one hf0
    -- `f(1) ≤ ζ(1)`, so `f` factors through `ζ`
    obtain ⟨k, hk, -⟩ := hζ.universal A f (le_of_eq hζ1.symm)
    have hinj : Function.Injective ⇑(stdFilter (f 1)) := (filter_basic_2 _ hζ).1
    -- `ζ` is a filter of a projection, hence multiplicative (99XI)
    have hmulζ : ∀ x y, (stdFilter (f 1) (x * y) : B)
        = stdFilter (f 1) x * stdFilter (f 1) y :=
      filter_of_projection_multiplicative _ hζ
        (by rw [hζ1]; exact h 1 (IsStarProjection.one (R := A)))
    have hk1 : k 1 = 1 := hinj (by rw [← hk 1, hζ1])
    have hkproj : ∀ p : A, IsStarProjection p → IsStarProjection (k p) := by
      intro p hp
      refine ⟨hinj ?_, ?_⟩
      · show (stdFilter (f 1) (k p * k p) : B) = stdFilter (f 1) (k p)
        rw [hmulζ, ← hk p]
        exact (h p hp).isIdempotentElem.eq
      · show star (k p) = k p
        rw [← ncp_star k p, hp.isSelfAdjoint.star_eq]
    have hkmul := ((gardner k hk1).out 3 0).mp hkproj
    intro a b
    rw [hk (a * b), hkmul a b, hmulζ, ← hk a, ← hk b]
  tfae_finish

/-! ## Parsec 1000: purity -/

/-- **100I** (`pure`, proc.tex:926, Definition): filters, corners, and
their compositions are called **pure**.

The whole chapter lives in `W*_cp`, so the algebra *through* which a
composition passes is a von Neumann algebra like the others; the `comp`
constructor therefore carries `[VonNeumannAlgebra B]`.  Without it the
definition is not the thesis's, and **100III** (1)⟹(2) is not provable:
its induction must factor the two halves of a composite through
`filter-basic` / `corner-basic`, which need the intermediate algebra to be
a von Neumann algebra.  (Transcription fix, session 49; the filter and
corner constructors need no such hypothesis because the base cases of that
induction do not.) -/
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
      [StarOrderedRing C] [VonNeumannAlgebra B] {f : NCPMap A B}
      {g : NCPMap B C} :
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
theorem isPure_adSelf [VonNeumannAlgebra A] (a : A) : IsPure (adSelf a) := by
  -- `a*(·)a = c ∘ π_{⌊a⌉}` with `c` the canonical filter of `a` (**96V**)
  -- and `π_{⌊a⌉}` the corner projection onto the projection `⌊a⌉`.
  have hq : IsStarProjection (rangeProj a) := isStarProjection_rangeProj a
  have hqa : rangeProj a * a = a := (ceill_basic_2 a).1.2
  have haq : star a * rangeProj a = star a := by
    have h := congrArg star hqa
    rwa [star_mul, hq.isSelfAdjoint.star_eq] at h
  have hfac : adSelf a
      = ncpComp (canonicalFilter a) (cornerProjMap (rangeProj a)).toNCPMap := by
    refine DFunLike.ext _ _ fun b => ?_
    rw [adSelf_apply, ncpComp_apply, canonicalFilter_apply, cornerProjMap_apply]
    calc star a * b * a = (star a * rangeProj a) * b * (rangeProj a * a) := by
          rw [haq, hqa]
      _ = star a * (rangeProj a * b * rangeProj a) * a := by noncomm_ring
  rw [hfac]
  refine IsPure.comp (IsPure.filter (canonical_filter a)) (IsPure.corner ?_)
  exact ⟨(cornerProjMap (rangeProj a)).unital', rangeProj a,
    ⟨hq.nonneg, hq.le_one⟩,
    isCornerOf_cornerProjMap (rangeProj a) (rangeProj a) hq
      (floor_of_isStarProjection hq)⟩

/-! ### Infrastructure for **100III** `pure-fundamental` -/

/-- An ncp-isomorphism is a **filter**: the factorisation of `h` through
`f` is `f⁻¹ ∘ h`, and the hypothesis `h(1) ≤ f(1)` is not needed.  (This is
the argument inside `isPure_of_iso`, isolated for reuse.) -/
theorem isFilter_of_iso [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) : IsFilter f := by
  refine ⟨?_⟩
  intro X _ _ _ _ h _
  refine ⟨ncpComp g h, fun x => ?_, fun k hk => ?_⟩
  · rw [ncpComp_apply, hfg]
  · refine DFunLike.ext _ _ fun x => ?_
    rw [ncpComp_apply, hk x, hgf]

/-- The identity map is a filter. -/
theorem isFilter_ncpId [VonNeumannAlgebra A] : IsFilter (ncpId A) :=
  isFilter_of_iso (ncpId A) (ncpId A) (fun a => by rw [ncpId_apply, ncpId_apply])
    (fun b => by rw [ncpId_apply, ncpId_apply])

/-- An ncp-isomorphism is a corner of `1`. -/
theorem isCornerOf_one_of_iso [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) : IsCornerOf (1 : A) f := by
  constructor
  · rw [sub_self]
    exact map_zero f.toCompletelyPositiveMap
  · intro X _ _ _ _ h _
    refine ⟨ncpComp h g, fun a => ?_, fun k hk => ?_⟩
    · rw [ncpComp_apply, hgf]
    · refine DFunLike.ext _ _ fun b => ?_
      calc k b = k (f (g b)) := by rw [hfg]
        _ = h (g b) := (hk (g b)).symm
        _ = ncpComp h g b := (ncpComp_apply h g b).symm

/-- A *unital* ncp-isomorphism is a **corner map** — a corner of `1`. -/
theorem isCornerMap_of_iso [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) (hu : f 1 = 1) : IsCornerMap f :=
  ⟨hu, 1, ⟨zero_le_one, le_rfl⟩, isCornerOf_one_of_iso f g hgf hfg⟩

/-- The identity map is a corner of `1`. -/
theorem isCornerOf_one_ncpId [VonNeumannAlgebra A] :
    IsCornerOf (1 : A) (ncpId A) :=
  isCornerOf_one_of_iso (ncpId A) (ncpId A)
    (fun a => by rw [ncpId_apply, ncpId_apply])
    (fun b => by rw [ncpId_apply, ncpId_apply])

/-- The identity map is a corner map. -/
theorem isCornerMap_ncpId [VonNeumannAlgebra A] : IsCornerMap (ncpId A) :=
  isCornerMap_of_iso (ncpId A) (ncpId A)
    (fun a => by rw [ncpId_apply, ncpId_apply])
    (fun b => by rw [ncpId_apply, ncpId_apply]) (ncpId_apply 1)

/-- **98IV**.1 in the form 100III needs it: *any* two corners of the same
effect are canonically isomorphic (`corner_basic_1` is the case where one
of them is the standard corner `π_p`). -/
theorem corner_unique [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (p : A) (π : NCPMap A B) (hπ : IsCornerOf p π)
    (ρ : NCPMap A C) (hρ : IsCornerOf p ρ) :
    ∃ β : NCPMap C B, (∀ a : A, π a = β (ρ a)) ∧
      ∃ β' : NCPMap B C, (∀ x, β' (β x) = x) ∧ ∀ y, β (β' y) = y := by
  obtain ⟨β, hβ, -⟩ := hρ.universal B π hπ.map_perp
  obtain ⟨γ, hγ, -⟩ := hπ.universal C ρ hρ.map_perp
  have hβγ : ncpComp β γ = ncpId B := by
    obtain ⟨k₀, hk₀, hun⟩ := hπ.universal B π hπ.map_perp
    rw [hun (ncpComp β γ) (fun a => by rw [ncpComp_apply, ← hγ, ← hβ]),
      hun (ncpId B) (fun a => by rw [ncpId_apply])]
  have hγβ : ncpComp γ β = ncpId C := by
    obtain ⟨k₀, hk₀, hun⟩ := hρ.universal C ρ hρ.map_perp
    rw [hun (ncpComp γ β) (fun a => by rw [ncpComp_apply, ← hβ, ← hγ]),
      hun (ncpId C) (fun a => by rw [ncpId_apply])]
  refine ⟨β, hβ, γ, fun x => ?_, fun y => ?_⟩
  · have h := congrArg (fun k : NCPMap C C => k x) hγβ
    simpa [ncpComp_apply, ncpId_apply] using h
  · have h := congrArg (fun k : NCPMap B B => k y) hβγ
    simpa [ncpComp_apply, ncpId_apply] using h

/-- **98II**.1 in the form 100III needs it: two filters with the same value
at `1` are canonically isomorphic (`filter_basic_1` is the case where one
of them is the standard filter `c_p`). -/
theorem filter_unique [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (c : NCPMap B A) (hc : IsFilter c) (d : NCPMap C A)
    (hd : IsFilter d) (h : (c 1 : A) = d 1) :
    ∃ α : NCPMap B C, (∀ x : B, (c x : A) = d (α x)) ∧ α 1 = 1 ∧
      ∃ α' : NCPMap C B, (∀ x, α' (α x) = x) ∧ ∀ y, α (α' y) = y := by
  obtain ⟨α, hα, -⟩ := hd.universal B c (le_of_eq h)
  obtain ⟨γ, hγ, -⟩ := hc.universal C d (le_of_eq h.symm)
  have hγα : ncpComp γ α = ncpId B := by
    obtain ⟨k₀, hk₀, hun⟩ := hc.universal B c le_rfl
    rw [hun (ncpComp γ α) (fun x => by rw [ncpComp_apply, ← hγ, ← hα]),
      hun (ncpId B) (fun x => by rw [ncpId_apply])]
  have hαγ : ncpComp α γ = ncpId C := by
    obtain ⟨k₀, hk₀, hun⟩ := hd.universal C d le_rfl
    rw [hun (ncpComp α γ) (fun x => by rw [ncpComp_apply, ← hα, ← hγ]),
      hun (ncpId C) (fun x => by rw [ncpId_apply])]
  have hγα' : ∀ x : B, γ (α x) = x := fun x => by
    have h1 := congrArg (fun k : NCPMap B B => k x) hγα
    simpa [ncpComp_apply, ncpId_apply] using h1
  have hαγ' : ∀ y : C, α (γ y) = y := fun y => by
    have h1 := congrArg (fun k : NCPMap C C => k y) hαγ
    simpa [ncpComp_apply, ncpId_apply] using h1
  refine ⟨α, hα, ?_, γ, hγα', hαγ'⟩
  refine (filter_basic_2 d hd).1 ?_
  rw [← hα 1, h]

/-- A **unital filter is an ncpu-isomorphism**: `id` factors through it by
its own universal property (`filter_unique` against `id`, which is a filter
by `isFilter_ncpId`).  This is what turns 100III into **100VII**. -/
theorem exists_inverse_of_isFilter_unital [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (c : NCPMap A B) (hc : IsFilter c)
    (hu : (c 1 : B) = 1) :
    ∃ g : NCPMap B A, (∀ a, g (c a) = a) ∧ (∀ b, c (g b) = b) ∧ g 1 = 1 := by
  obtain ⟨α, hα, hα1, α', hα'α, hαα'⟩ :=
    filter_unique c hc (ncpId B) isFilter_ncpId (by rw [ncpId_apply, hu])
  have hcx : ∀ x : A, (c x : B) = α x := fun x => by rw [hα x, ncpId_apply]
  refine ⟨α', fun a => ?_, fun b => ?_, ?_⟩
  · rw [hcx a, hα'α]
  · rw [hcx (α' b), hαα']
  · have h := hα'α 1
    rwa [hα1] at h

/-- A **corner of `1` is an ncp-isomorphism**, hence in particular a
filter — the corner half of the same reduction. -/
theorem isFilter_of_isCornerOf_one [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (π : NCPMap A B) (hπ : IsCornerOf (1 : A) π) : IsFilter π := by
  obtain ⟨β, hβ, β', hβ'β, hββ'⟩ :=
    corner_unique (1 : A) π hπ (ncpId A) isCornerOf_one_ncpId
  have hβx : ∀ a : A, (π a : B) = β a := fun a => by rw [hβ a, ncpId_apply]
  refine isFilter_of_iso π β' (fun a => ?_) (fun b => ?_)
  · rw [hβx a, hβ'β]
  · rw [hβx (β' b), hββ']

/-- Auxiliary for **100III**: an ncp-map killing `q^⊥`, for a projection
`q`, is invariant under conjugation by `q`.  (The carrier step inside
`isCornerOf_stdCorner`, isolated so that it can also be used when the
ambient algebra is itself a corner.) -/
private theorem map_conj_eq_of_map_perp [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {q : A} (hq : IsStarProjection q) (f : NCPMap A B)
    (hf : (f (1 - q) : B) = 0) (a : A) : (f a : B) = f (q * a * q) := by
  set F : A →ₚ[ℂ] B := PositiveLinearMap.ofClass f.toCompletelyPositiveMap with hF
  have hFn : PreservesDirSups ⇑F := f.preservesDirSups'
  have hf' : F (1 - q) = 0 := hf
  have hcle : carrier F hFn ≤ q := (carrier_spec F hFn).2.2 _ hq hf'
  have hcproj : IsStarProjection (carrier F hFn) := (carrier_spec F hFn).1
  have hcq : carrier F hFn * q = carrier F hFn :=
    ((projection_below_effect q (carrier F hFn) ⟨hq.nonneg, hq.le_one⟩
      hcproj).out 0 7).mp hcle
  have hqc : q * carrier F hFn = carrier F hFn := by
    have hs := congrArg star hcq
    rwa [star_mul, hq.isSelfAdjoint.star_eq, hcproj.isSelfAdjoint.star_eq] at hs
  have key : (F a : B) = F (q * a * q) := by
    have e1 := (carrier_fundamental F hFn a).2.2
    have e2 := (carrier_fundamental F hFn (q * a * q)).2.2
    rw [e2, show carrier F hFn * (q * a * q) * carrier F hFn
        = (carrier F hFn * q) * a * (q * carrier F hFn) by noncomm_ring, hcq,
      hqc, ← e1]
  exact key

/-- Auxiliary for **100III**: for projections `q ≤ e` the map
`x ↦ q x q : e𝒜e → q𝒜q` is a **corner** (of the effect `q` of `e𝒜e`).
This is `isCornerOf_stdCorner` run inside the von Neumann algebra `e𝒜e`,
but with the sub-corner presented as `q𝒜q` rather than as a corner of a
corner — which is what keeps 100III clear of iterated corners. -/
private theorem exists_subCornerProj [VonNeumannAlgebra A] {e q : A}
    [Fact (IsStarProjection e)] [Fact (IsStarProjection q)] (hqe : q * e = q) :
    ∃ κ : NCPMap (Corner A e) (Corner A q),
      (∀ x : Corner A e, (κ x).val = q * x.val * q) ∧ IsCornerMap κ := by
  have he : IsStarProjection e := Corner.proj e
  have hq : IsStarProjection q := Corner.proj q
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have heq : e * q = q := by
    have h := congrArg star hqe
    rwa [star_mul, he.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] at h
  have hqmem : e * q * e = q := by rw [heq, hqe]
  -- the map `x ↦ q x q : e𝒜e → 𝒜`, corestricted to `q𝒜q`
  have hbaseapp : ∀ x : Corner A e,
      (ncpComp (adSelf q) (cornerIncl e).toNCPMap x : A) = q * x.val * q := by
    intro x
    rw [ncpComp_apply, cornerIncl_apply, adSelf_apply, hq.isSelfAdjoint.star_eq]
  obtain ⟨κ, hκ0⟩ := exists_ncpCorestrict q
    (ncpComp (adSelf q) (cornerIncl e).toNCPMap) (by
      intro x
      rw [hbaseapp]
      calc q * (q * x.val * q) * q = (q * q) * x.val * (q * q) := by noncomm_ring
        _ = q * x.val * q := by rw [hqq])
  have hκ : ∀ x : Corner A e, (κ x).val = q * x.val * q := by
    intro x; rw [hκ0 x, hbaseapp]
  -- the inclusion `q𝒜q → e𝒜e`
  obtain ⟨ι, hι0⟩ := exists_ncpCorestrict e (cornerIncl q).toNCPMap (by
    intro y
    rw [cornerIncl_apply]
    calc e * y.val * e = e * (q * y.val * q) * e := by rw [y.property]
      _ = (e * q) * y.val * (q * e) := by noncomm_ring
      _ = q * y.val * q := by rw [heq, hqe]
      _ = y.val := y.property)
  have hι : ∀ y : Corner A q, (ι y).val = y.val := by
    intro y; rw [hι0 y, cornerIncl_apply]
  have hq'idem : (⟨q, hqmem⟩ : Corner A e) * ⟨q, hqmem⟩ = ⟨q, hqmem⟩ :=
    Corner.val_injective (by show q * q = q; exact hqq)
  have hq'sa : star (⟨q, hqmem⟩ : Corner A e) = ⟨q, hqmem⟩ :=
    Corner.val_injective (by show star q = q; exact hq.isSelfAdjoint.star_eq)
  have hq' : IsStarProjection (⟨q, hqmem⟩ : Corner A e) := ⟨hq'idem, hq'sa⟩
  refine ⟨κ, hκ, ?_, ⟨q, hqmem⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine Corner.val_injective ?_
    rw [hκ]
    simp only [Corner.val_one]
    rw [hqe, hqq]
  · exact (Corner.le_def _ _).mpr (show (0 : A) ≤ q from hq.nonneg)
  · refine (Corner.le_def _ _).mpr ?_
    show q ≤ (1 : Corner A e).val
    simp only [Corner.val_one]
    exact ((projection_below_effect e q ⟨he.nonneg, he.le_one⟩ hq).out 7 0).mp hqe
  · refine Corner.val_injective ?_
    rw [hκ]
    simp only [Corner.val_sub, Corner.val_one, Corner.val_zero]
    have h1 : q * (e - q) * q = q * e * q - q * q * q := by noncomm_ring
    rw [h1, hqe, hqq, hqq, sub_self]
  · intro X _ _ _ _ f' hf'
    have hconj := map_conj_eq_of_map_perp hq' f' hf'
    refine ⟨ncpComp f' ι, fun x => ?_, fun g hg => ?_⟩
    · rw [ncpComp_apply]
      have hval : ι (κ x) = (⟨q, hqmem⟩ : Corner A e) * x * ⟨q, hqmem⟩ :=
        Corner.val_injective (by rw [hι, hκ]; simp only [Corner.val_mul])
      rw [hval]
      exact hconj x
    · refine DFunLike.ext _ _ fun y => ?_
      have hsurj : κ (ι y) = y :=
        Corner.val_injective (by rw [hκ, hι]; exact y.property)
      calc g y = g (κ (ι y)) := by rw [hsurj]
        _ = f' (ι y) := (hg _).symm
        _ = ncpComp f' ι y := (ncpComp_apply f' ι y).symm

/-- Auxiliary for **100III**: a filter all of whose values lie in a corner
`q𝒜q` is still a filter when corestricted to `q𝒜q`. -/
private theorem isFilter_corestrict [VonNeumannAlgebra A]
    [VonNeumannAlgebra C] {q : A} [Fact (IsStarProjection q)] (c : NCPMap C A)
    (hc : IsFilter c) (c' : NCPMap C (Corner A q))
    (hcc : ∀ x : C, (c' x).val = c x) : IsFilter c' := by
  refine ⟨?_⟩
  intro X _ _ _ _ h hh1
  have hh0 : ∀ x : X, (ncpComp (cornerIncl q).toNCPMap h x : A) = (h x).val := by
    intro x; rw [ncpComp_apply, cornerIncl_apply]
  have hle : (ncpComp (cornerIncl q).toNCPMap h 1 : A) ≤ c 1 := by
    rw [hh0, ← hcc 1]
    exact (Corner.le_def _ _).mp hh1
  obtain ⟨g, hg, hgu⟩ := hc.universal X (ncpComp (cornerIncl q).toNCPMap h) hle
  refine ⟨g, fun x => ?_, fun g' hg' => ?_⟩
  · refine Corner.val_injective ?_
    rw [hcc, ← hh0 x]
    exact hg x
  · refine hgu g' ?_
    intro x
    rw [hh0, ← hcc (g' x), hg' x]

/-- Auxiliary for **100III** and **100VII**: a filter is faithful
(`⌈c⌉ = 1`, 98II.2 — here only its injectivity is used), so
`⌈c ∘ π⌉ = ⌈π⌉`. -/
private theorem ncpCarrier_comp_filter [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] [VonNeumannAlgebra C] (π : NCPMap A C)
    (c : NCPMap C B) (hc : IsFilter c) :
    ncpCarrier (ncpComp c π) = ncpCarrier π := by
  have hcinj : Function.Injective ⇑c := (filter_basic_2 c hc).1
  have hcz : (c (0 : C) : B) = 0 := map_zero c.toCompletelyPositiveMap
  have hzero : ∀ x : A, (ncpComp c π x : B) = 0 ↔ (π x : C) = 0 := by
    intro x
    rw [ncpComp_apply]
    exact ⟨fun h => hcinj (by rw [h, hcz]), fun h => by rw [h, hcz]⟩
  have hspecf := (exists_ncpCarrier (ncpComp c π)).choose_spec.1
  have hspecπ := (exists_ncpCarrier π).choose_spec.1
  exact le_antisymm (hspecf.2.2 _ hspecπ.1 ((hzero _).mpr hspecπ.2.1))
    (hspecπ.2.2 _ hspecf.1 ((hzero _).mp hspecf.2.1))

/-- The heart of **100III** (1)⟹(2): the composition `π ∘ c` of a filter
`c` followed by a corner `π` is again *properly* pure, i.e. of the form
(filter) ∘ (corner).

The thesis (proc.tex:975) reduces this — by `filter-basic` and
`corner-basic` — to `π_s ∘ c_p` and then appeals to the Example `ad-pure`
(98XI) for `[π_s ∘ c_p]` being an ncpu-isomorphism.  We give the
factorisation of `π_s ∘ c_p` outright, which avoids `ad-pure` (and with it
the polar decomposition and the iterated corners `[f]` would live in):
with `a := √p·s` one has `s√p x √p s = a*(⌊a⌉x⌊a⌉)a`, where
`x ↦ ⌊a⌉x⌊a⌉ : ⌈p⌉𝒜⌈p⌉ → ⌊a⌉𝒜⌊a⌉` is a corner (`exists_subCornerProj`)
and `a*(·)a : ⌊a⌉𝒜⌊a⌉ → s𝒜s` is a filter (**96V** `canonical_filter`,
corestricted). -/
private theorem properlyPure_corner_comp_filter [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] [VonNeumannAlgebra C] (c : NCPMap C A)
    (hc : IsFilter c) (π : NCPMap A B) (hπ : IsCornerMap π) :
    ∃ (Z : Type u) (_ : CStarAlgebra Z) (_ : PartialOrder Z)
      (_ : StarOrderedRing Z) (_ : VonNeumannAlgebra Z) (π' : NCPMap C Z)
      (c' : NCPMap Z B), IsCornerMap π' ∧ IsFilter c' ∧
      ncpComp π c = ncpComp c' π' := by
  obtain ⟨hπu, r, hr, hπc⟩ := hπ
  have hs : IsStarProjection (floor r) := isStarProjection_floor r
  have hπs : IsCornerOf (floor r) π := ((corners_floor r hr π hπu).1).mp hπc
  obtain ⟨β, hβ, β', hβ'β, hββ'⟩ :=
    corner_unique (floor r) π hπs (cornerProjMap (floor r)).toNCPMap
      (isCornerOf_cornerProjMap (floor r) (floor r) hs
        (floor_of_isStarProjection hs))
  have hp0 : (0 : A) ≤ c 1 := ncpMap_nonneg c zero_le_one
  obtain ⟨α, hα, hα1, α', hα'α, hαα'⟩ :=
    filter_unique c hc (stdFilter (c 1)) (isFilter_stdFilter (c 1) hp0)
      (by rw [stdFilter_one hp0])
  set a : A := CFC.sqrt (c 1) * floor r with hadef
  have hsqsa : star (CFC.sqrt (c 1)) = CFC.sqrt (c 1) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (c 1))).star_eq
  have hstara : star a = floor r * CFC.sqrt (c 1) := by
    rw [hadef, star_mul, hs.isSelfAdjoint.star_eq, hsqsa]
  have has : a * floor r = a := by
    rw [hadef, mul_assoc, hs.isIdempotentElem.eq]
  have hsl : floor r * star a = star a := by
    rw [hstara, ← mul_assoc, hs.isIdempotentElem.eq]
  have hqa : rangeProj a * a = a := (ceill_basic_2 a).1.2
  have haq : star a * rangeProj a = star a := by
    have h := congrArg star hqa
    rwa [star_mul, (isStarProjection_rangeProj a).isSelfAdjoint.star_eq] at h
  -- the corner `⌈p⌉𝒜⌈p⌉ → ⌊a⌉𝒜⌊a⌉`
  have hqle : rangeProj a ≤ ceil (c 1) := by
    rw [ceil_eq_rangeProj_sqrt hp0, hadef]
    exact rangeProj_mul_le _ _
  have hqe : rangeProj a * ceil (c 1) = rangeProj a :=
    ((projection_below_effect (ceil (c 1)) (rangeProj a)
      ⟨(isStarProjection_ceil (c 1)).nonneg, (isStarProjection_ceil (c 1)).le_one⟩
      (isStarProjection_rangeProj a)).out 0 7).mp hqle
  obtain ⟨κ, hκ, hκcorner⟩ := exists_subCornerProj (A := A) (e := ceil (c 1))
    (q := rangeProj a) hqe
  -- the filter `a*(·)a : ⌊a⌉𝒜⌊a⌉ → s𝒜s`
  have hsval : ∀ z : Corner A (rangeProj a),
      floor r * (canonicalFilter a z : A) * floor r = canonicalFilter a z := by
    intro z
    rw [canonicalFilter_apply]
    calc floor r * (star a * z.val * a) * floor r
        = (floor r * star a) * z.val * (a * floor r) := by noncomm_ring
      _ = star a * z.val * a := by rw [hsl, has]
  obtain ⟨c₀, hc₀⟩ := exists_ncpCorestrict (floor r) (canonicalFilter a) hsval
  have hc₀filter : IsFilter c₀ :=
    isFilter_corestrict (canonicalFilter a) (canonical_filter a) c₀ hc₀
  refine ⟨Corner A (rangeProj a), inferInstance, inferInstance, inferInstance,
    inferInstance, ncpComp κ α, ncpComp β c₀,
    corners_composition α κ (isCornerMap_of_iso α α' hα'α hαα' hα1) hκcorner,
    filters_composition c₀ β hc₀filter (isFilter_of_iso β β' hβ'β hββ'), ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  rw [ncpComp_apply, ncpComp_apply, ncpComp_apply, ncpComp_apply, hα x,
    hβ (stdFilter (c 1) (α x))]
  congr 1
  refine Corner.val_injective ?_
  rw [cornerProjMap_apply, hc₀, canonicalFilter_apply, hκ, stdFilter_apply]
  calc floor r * (CFC.sqrt (c 1) * (α x).val * CFC.sqrt (c 1)) * floor r
      = (floor r * CFC.sqrt (c 1)) * (α x).val * (CFC.sqrt (c 1) * floor r) := by
        noncomm_ring
    _ = star a * (α x).val * a := by rw [← hstara, ← hadef]
    _ = (star a * rangeProj a) * (α x).val * (rangeProj a * a) := by
        rw [haq, hqa]
    _ = star a * (rangeProj a * (α x).val * rangeProj a) * a := by noncomm_ring

/-- **100III** (1)⟹(2): every pure map is *properly* pure.  The induction
of the thesis (proc.tex:955): filters and corners compose among themselves
(98III, 98VI), so everything reduces to `π ∘ c` — which is
`properlyPure_corner_comp_filter`. -/
private theorem properlyPure_of_isPure {X Y : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [CStarAlgebra Y] [PartialOrder Y]
    [StarOrderedRing Y] {f : NCPMap X Y} (hf : IsPure f) :
    ∀ [VonNeumannAlgebra X] [VonNeumannAlgebra Y],
      ∃ (Z : Type u) (_ : CStarAlgebra Z) (_ : PartialOrder Z)
        (_ : StarOrderedRing Z) (_ : VonNeumannAlgebra Z) (π : NCPMap X Z)
        (c : NCPMap Z Y), IsCornerMap π ∧ IsFilter c ∧ f = ncpComp c π := by
  induction hf with
  | filter hc =>
      intro _ _
      exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
        ncpId _, _, isCornerMap_ncpId, hc,
        DFunLike.ext _ _ fun x => by rw [ncpComp_apply, ncpId_apply]⟩
  | corner hπ =>
      intro _ _
      exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
        _, ncpId _, hπ, isFilter_ncpId,
        DFunLike.ext _ _ fun x => by rw [ncpComp_apply, ncpId_apply]⟩
  | comp hg hf' ihg ihf =>
      intro _ _
      obtain ⟨E₁, _, _, _, _, π₁, c₁, hπ₁, hc₁, hfac₁⟩ := ihf
      obtain ⟨E₂, _, _, _, _, π₂, c₂, hπ₂, hc₂, hfac₂⟩ := ihg
      obtain ⟨E₃, _, _, _, _, π₃, c₃, hπ₃, hc₃, hcrux⟩ :=
        properlyPure_corner_comp_filter c₁ hc₁ π₂ hπ₂
      refine ⟨E₃, inferInstance, inferInstance, inferInstance, inferInstance,
        ncpComp π₃ π₁, ncpComp c₂ c₃, corners_composition π₁ π₃ hπ₁ hπ₃,
        filters_composition c₃ c₂ hc₃ hc₂, ?_⟩
      rw [hfac₁, hfac₂]
      refine DFunLike.ext _ _ fun x => ?_
      have hcx := congrArg (fun k : NCPMap E₁ E₂ => k (π₁ x)) hcrux
      simp only [ncpComp_apply] at hcx
      simp only [ncpComp_apply]
      rw [hcx]

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
          (∀ x, h (sqBracket f x) = x) ∧ ∀ y, sqBracket f (h y) = y ].TFAE := by
  -- The thesis's cycle, with (1)⟹(2) the only work (see
  -- `properlyPure_of_isPure`).  (2)⟹(3): `⌈f⌉ = ⌈π⌉` (because `⌈c⌉ = 1`) and
  -- `f(1) = c(1)` (because `π(1) = 1`), so `f = c_{f(1)} ∘ (α ∘ β') ∘ π_{⌈f⌉}`
  -- with `α`, `β'` the isomorphisms of 98II.1 and 98IV.1; by the uniqueness
  -- clause of 98IX that composite *is* `[f]`.  (3)⟹(1): `[f]` is an
  -- isomorphism, hence a filter, so `c_{f(1)} ∘ [f]` is a filter (98III) and
  -- `f = (c_{f(1)} ∘ [f]) ∘ π_{⌈f⌉}` is pure.
  have hp : (0 : B) ≤ f 1 := ncpMap_nonneg f zero_le_one
  have hcf : IsStarProjection (ncpCarrier f) := isStarProjection_ncpCarrier f
  tfae_have 1 → 2 := fun hf => properlyPure_of_isPure hf
  tfae_have 2 → 3 := by
    rintro ⟨C', _, _, _, _, π, c, hπ, hc, hfac⟩
    have hfx : ∀ x : A, (f x : B) = c (π x) := fun x => by
      rw [hfac, ncpComp_apply]
    have hcarr : ncpCarrier f = ncpCarrier π := by
      rw [hfac]; exact ncpCarrier_comp_filter π c hc
    obtain ⟨hπu, p, hp', hπc⟩ := hπ
    have hc1 : (c 1 : B) = f 1 := by rw [hfx 1, hπu]
    have hcarrπ : ncpCarrier π = floor p := (corners_floor p hp' π hπu).2 hπc
    have hπc' : IsCornerOf (ncpCarrier f) π := by
      rw [hcarr, hcarrπ]
      exact ((corners_floor p hp' π hπu).1).mp hπc
    obtain ⟨β, hβ, β', hβ'β, hββ'⟩ :=
      corner_unique (ncpCarrier f) (cornerProjMap (ncpCarrier f)).toNCPMap
        (isCornerOf_cornerProjMap (ncpCarrier f) (ncpCarrier f) hcf
          (floor_of_isStarProjection hcf)) π hπc'
    obtain ⟨α, hα, hα1, α', hα'α, hαα'⟩ :=
      filter_unique c hc (stdFilter (f 1)) (isFilter_stdFilter (f 1) hp)
        (by rw [stdFilter_one hp, hc1])
    -- `γ = α ∘ β'` satisfies the square of 98IX, hence is `[f]`
    have hsquare : ∀ a : A, (f a : B) =
        stdFilter (f 1)
          (ncpComp α β' ((cornerProjMap (ncpCarrier f)).toNCPMap a)) := by
      intro a
      rw [ncpComp_apply, hβ a, hβ'β, ← hα (π a)]
      exact hfx a
    have hγ : ncpComp α β' = sqBracket f := (square_f f).2.1 _ hsquare
    refine ⟨(square_f f).2.2.1, ncpComp β α', fun x => ?_, fun y => ?_⟩
    · rw [← hγ, ncpComp_apply, ncpComp_apply, hα'α, hββ']
    · rw [← hγ, ncpComp_apply, ncpComp_apply, hβ'β, hαα']
  tfae_have 3 → 1 := by
    rintro ⟨-, h, hhf, hfh⟩
    have hfac : f = ncpComp (ncpComp (stdFilter (f 1)) (sqBracket f))
        ((cornerProjMap (ncpCarrier f)).toNCPMap) := by
      refine DFunLike.ext _ _ fun a => ?_
      rw [ncpComp_apply, ncpComp_apply]
      exact (square_f f).1 a
    rw [hfac]
    refine IsPure.comp (IsPure.filter (filters_composition (sqBracket f)
      (stdFilter (f 1)) (isFilter_of_iso (sqBracket f) h hhf hfh)
      (isFilter_stdFilter (f 1) hp))) (IsPure.corner ?_)
    exact ⟨(cornerProjMap (ncpCarrier f)).unital', ncpCarrier f,
      ⟨hcf.nonneg, hcf.le_one⟩,
      isCornerOf_cornerProjMap (ncpCarrier f) (ncpCarrier f) hcf
        (floor_of_isStarProjection hcf)⟩
  tfae_finish

/-- **100VII** (`special-pure-maps`, proc.tex:1016, Exercise), part 1: a
faithful pure map is a filter. -/
theorem special_pure_maps_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) (hfaith : ncpCarrier f = 1) :
    IsFilter f := by
  -- `f = c ∘ π` by 100III; `⌈π⌉ = ⌈f⌉ = 1`, so `π` is a corner of `1`,
  -- hence an isomorphism, hence a filter — and filters compose (98III).
  obtain ⟨Z, _, _, _, _, π, c, hπ, hc, hfac⟩ := ((pure_fundamental f).out 0 1).mp hf
  obtain ⟨hπu, p, hp, hπc⟩ := hπ
  have hfl : floor p = 1 := by
    rw [← (corners_floor p hp π hπu).2 hπc, ← ncpCarrier_comp_filter π c hc,
      ← hfac, hfaith]
  have hπ1 : IsCornerOf (1 : A) π := by
    rw [← hfl]
    exact ((corners_floor p hp π hπu).1).mp hπc
  rw [hfac]
  exact filters_composition π c (isFilter_of_isCornerOf_one π hπ1) hc

/-- **100VII** (`special-pure-maps`, proc.tex:1016, Exercise), part 2: a
unital pure map is a corner. -/
theorem special_pure_maps_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) (hu : f 1 = 1) : IsCornerMap f := by
  -- `f = c ∘ π` by 100III; `c(1) = f(1) = 1`, so the filter `c` is an
  -- isomorphism, hence a corner map — and corners compose (98VI).
  obtain ⟨Z, _, _, _, _, π, c, hπ, hc, hfac⟩ := ((pure_fundamental f).out 0 1).mp hf
  have hc1 : (c 1 : B) = 1 := by
    have h1 : (f 1 : B) = c (π 1) := by rw [hfac, ncpComp_apply]
    rw [hπ.1] at h1
    rw [← h1, hu]
  obtain ⟨g, hgc, hcg, -⟩ := exists_inverse_of_isFilter_unital c hc hc1
  rw [hfac]
  exact corners_composition π c hπ (isCornerMap_of_iso c g hgc hcg hc1)

/-- **100VII** (`special-pure-maps`, proc.tex:1016, Exercise), part 3: a
unital and faithful pure map is an ncpu-isomorphism. -/
theorem special_pure_maps_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) (hu : f 1 = 1)
    (hfaith : ncpCarrier f = 1) :
    ∃ g : NCPMap B A, (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b) ∧ g 1 = 1 :=
  -- part 1 makes `f` a filter, and a unital filter is an isomorphism
  exists_inverse_of_isFilter_unital f (special_pure_maps_1 f hf hfaith) hu

/-! ## Parsec 1010: contraposition -/

/-- **101I** (proc.tex:1031, Definition): for an ncp-map `f : 𝒜 → ℬ` the
map `f^⋄ : Proj(𝒜) → Proj(ℬ)`, `f^⋄(e) = ⌈f(e)⌉` (here defined on all of
`A`; only its values on projections matter). -/
noncomputable def diamondUp [VonNeumannAlgebra B] (f : NCPMap A B)
    (e : A) : B := ceil (f e)

/-! ### Infrastructure for parsec 1010

Three elementary facts about the orthocomplement, and the one computational
ingredient of 101II: for positive `b` and a projection `e` the conditions
`⌈b⌉ ≤ e^⊥` and `e b e = 0` agree (the author's "`ef(s^⊥)e=0` iff
`⌈f(s^⊥)⌉ ≤ e^⊥`", proc.tex:1063). -/

/-- Orthogonality of two elements of `[0,1]` is symmetric. -/
theorem perp_symm {a b : A} : a ≤ 1 - b ↔ b ≤ 1 - a := by
  constructor <;> intro h <;> rw [← sub_nonneg] at h ⊢ <;>
    · convert h using 1
      abel

/-- Two projections that are below the same orthocomplements are equal. -/
theorem starProj_eq_of_perp_iff {a b : A}
    (h : ∀ t : A, IsStarProjection t → (a ≤ 1 - t ↔ b ≤ 1 - t))
    (ha : IsStarProjection a) (hb : IsStarProjection b) : a = b := by
  have h1 : b ≤ a := by
    have hx := (h (1 - a) ha.one_sub).mp (sub_sub_cancel 1 a).ge
    rwa [sub_sub_cancel] at hx
  have h2 : a ≤ b := by
    have hx := (h (1 - b) hb.one_sub).mpr (sub_sub_cancel 1 b).ge
    rwa [sub_sub_cancel] at hx
  exact le_antisymm h2 h1

/-- The supremum of two projections is below a projection `q` iff both are. -/
theorem projSup_pair_le_iff [VonNeumannAlgebra A] {a b q : A}
    (ha : IsStarProjection a) (hb : IsStarProjection b) (hq : IsStarProjection q) :
    projSup ({a, b} : Set A) ≤ q ↔ a ≤ q ∧ b ≤ q := by
  have hP : ∀ p ∈ ({a, b} : Set A), IsStarProjection p := by
    rintro p (rfl | rfl) <;> assumption
  obtain ⟨-, hub, hleast⟩ := projSup_spec hP
  refine ⟨fun h => ⟨le_trans (hub a (by left; rfl)) h,
      le_trans (hub b (by right; rfl)) h⟩, fun h => hleast q hq ?_⟩
  rintro p (rfl | rfl)
  · exact h.1
  · exact h.2

/-- Infrastructure for 101VII part 1: for projections `s`, `t` and any `x`,
`t (x* s x) t = 0` iff `s x t = 0`, because `t x* s x t = (sxt)*(sxt)`. -/
theorem conj_perp_eq_zero_iff {s t x : A} (hs : IsStarProjection s)
    (ht : IsStarProjection t) :
    t * (star x * s * x) * t = 0 ↔ s * x * t = 0 := by
  have h : star (s * x * t) * (s * x * t) = t * (star x * s * x) * t := by
    rw [star_mul, star_mul, ht.isSelfAdjoint.star_eq, hs.isSelfAdjoint.star_eq]
    calc t * (star x * s) * (s * x * t) = t * star x * (s * s) * x * t := by
          noncomm_ring
      _ = t * (star x * s * x) * t := by
          rw [hs.isIdempotentElem.eq]; noncomm_ring
  rw [← h]
  exact CStarRing.star_mul_self_eq_zero_iff _

/-- Infrastructure for 101VII part 1: `s x t = 0` iff `t x* s = 0`, for
projections `s`, `t`. -/
theorem mul_triple_eq_zero_iff_star {s t x : A} (hs : IsStarProjection s)
    (ht : IsStarProjection t) : s * x * t = 0 ↔ t * star x * s = 0 := by
  constructor <;> intro h <;>
    · have h' := congrArg star h
      simpa [star_mul, mul_assoc, hs.isSelfAdjoint.star_eq,
        ht.isSelfAdjoint.star_eq] using h'

/-- **101II** (proc.tex:1048, Proposition), well-definedness: for an
ncp-map `f : 𝒜 → ℬ` and a projection `e` of `ℬ` there is a least
projection `p` of `𝒜` with `⌈f(p^⊥)⌉ ≤ e^⊥`. -/
theorem exists_diamondDown [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : B) (he : IsStarProjection e) :
    ∃! p : A, IsStarProjection p ∧ ceil (f (1 - p)) ≤ 1 - e ∧
      ∀ q : A, IsStarProjection q → ceil (f (1 - q)) ≤ 1 - e → p ≤ q := by
  -- The author's proof (proc.tex:1060): `f_⋄(e)` is the carrier of the
  -- ncp-map `e f(·) e`, using `ef(s^⊥)e = 0  ⟺  ⌈f(s^⊥)⌉ ≤ e^⊥`.
  have happ : ∀ a : A, ncpComp (adSelf e) f a = e * f a * e := by
    intro a
    rw [ncpComp_apply, adSelf_apply, he.isSelfAdjoint.star_eq]
  have hiff : ∀ q : A, IsStarProjection q →
      (ncpComp (adSelf e) f (1 - q) = 0 ↔ ceil (f (1 - q)) ≤ 1 - e) := by
    intro q hq
    rw [happ]
    exact (ceil_le_perp_iff (ncpMap_nonneg f (sub_nonneg.mpr hq.le_one)) he).symm
  obtain ⟨p, ⟨hp, hp0, hpl⟩, -⟩ := exists_ncpCarrier (ncpComp (adSelf e) f)
  refine ⟨p, ⟨hp, (hiff p hp).mp hp0,
    fun q hq hq' => hpl q hq ((hiff q hq).mpr hq')⟩, ?_⟩
  rintro r ⟨hr, hr1, hrl⟩
  exact le_antisymm (hrl p hp ((hiff p hp).mp hp0)) (hpl r hr ((hiff r hr).mpr hr1))

open scoped Classical in
/-- **101II** (proc.tex:1048, Proposition): the map
`f_⋄ : Proj(ℬ) → Proj(𝒜)`: `f_⋄(e)` is the least projection `p` with
`⌈f(p^⊥)⌉ ≤ e^⊥` (junk value `0` off the projections). -/
noncomputable def diamondDown [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : B) : A :=
  if he : IsStarProjection e then (exists_diamondDown f e he).choose else 0

/-- The defining property of `f_⋄(e)`, for a projection `e`. -/
theorem diamondDown_spec [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) {e : B} (he : IsStarProjection e) :
    IsStarProjection (diamondDown f e) ∧
      ceil (f (1 - diamondDown f e)) ≤ 1 - e ∧
      ∀ q : A, IsStarProjection q → ceil (f (1 - q)) ≤ 1 - e →
        diamondDown f e ≤ q := by
  rw [diamondDown, dif_pos he]
  exact (exists_diamondDown f e he).choose_spec.1

/-- `f^⋄(e)` is a projection. -/
theorem isStarProjection_diamondUp [VonNeumannAlgebra B] (f : NCPMap A B)
    (e : A) : IsStarProjection (diamondUp f e) := isStarProjection_ceil _

/-- `f_⋄(1) = ⌈f⌉`: for `e = 1` the condition `⌈f(p^⊥)⌉ ≤ 1^⊥` reads
`f(p^⊥) = 0`, so 101II specialises to the carrier of 63I. -/
theorem diamondDown_one [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) : diamondDown f 1 = ncpCarrier f := by
  have hiff : ∀ q : A, IsStarProjection q →
      (ceil (f (1 - q)) ≤ 1 - 1 ↔ f (1 - q) = 0) := by
    intro q hq
    have hnn := ncpMap_nonneg f (sub_nonneg.mpr hq.le_one)
    rw [sub_self]
    exact ⟨fun hle => (ceil_basic_3 _ hnn).mpr
        (le_antisymm hle (isStarProjection_ceil _).nonneg),
      fun h0 => by rw [h0, ceil_zero]⟩
  obtain ⟨hp, hple, hpl⟩ := diamondDown_spec f (IsStarProjection.one (R := B))
  have hspec : IsStarProjection (ncpCarrier f) ∧ f (1 - ncpCarrier f) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → ncpCarrier f ≤ q :=
    (exists_ncpCarrier f).choose_spec.1
  exact le_antisymm (hpl _ hspec.1 ((hiff _ hspec.1).mpr hspec.2.1))
    (hspec.2.2 _ hp ((hiff _ hp).mp hple))

/-- **101II** (proc.tex:1048, Proposition), formula: `f_⋄(e)` is the
carrier of the ncp-map `e f(·) e`, i.e. the least projection `p` with
`e·f(p^⊥)·e = 0`. -/
theorem diamondDown_carrier [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : B) (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ e * f (1 - p) * e = 0}
      (diamondDown f e) := by
  obtain ⟨hp, hple, hpl⟩ := diamondDown_spec f he
  have hcv : ∀ q : A, IsStarProjection q →
      (ceil (f (1 - q)) ≤ 1 - e ↔ e * f (1 - q) * e = 0) := fun q hq =>
    ceil_le_perp_iff (ncpMap_nonneg f (sub_nonneg.mpr hq.le_one)) he
  exact ⟨⟨hp, (hcv _ hp).mp hple⟩, fun q hq => hpl q hq.1 ((hcv q hq.1).mpr hq.2)⟩

/-- **101IV** (`diamond-suprema`, proc.tex:1071, Exercise), part 1: the
Galois-type correspondence `f^⋄(s) ≤ t^⊥ ⟺ f_⋄(t) ≤ s^⊥`. -/
theorem diamond_suprema_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (s : A) (t : B) (hs : IsStarProjection s)
    (ht : IsStarProjection t) :
    diamondUp f s ≤ 1 - t ↔ diamondDown f t ≤ 1 - s := by
  obtain ⟨-, hple, hpl⟩ := diamondDown_spec f ht
  constructor
  · intro h
    refine hpl (1 - s) hs.one_sub ?_
    rwa [sub_sub_cancel]
  · intro h
    have hmono : ceil (f (1 - (1 - s))) ≤ ceil (f (1 - diamondDown f t)) :=
      ceil_mono (ncpMap_nonneg f (by rw [sub_sub_cancel]; exact hs.nonneg))
        (OrderHomClass.mono f.toCompletelyPositiveMap (sub_le_sub_left h 1))
    rw [sub_sub_cancel] at hmono
    exact le_trans hmono hple

/-- **101IV** (`diamond-suprema`, proc.tex:1071, Exercise), part 2:
`f^⋄(⋃E) = ⋃_{e∈E} f^⋄(e)` for every set of projections `E`. -/
theorem diamond_suprema_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (E : Set A) (hE : ∀ e ∈ E, IsStarProjection e) :
    diamondUp f (projSup E) = projSup (diamondUp f '' E) :=
  -- literally 60IX part 2 (`ncp_union_2`) for the np-map underlying `f`
  ncp_union_2 (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
    f.preservesDirSups' E hE

/-- **101V** (proc.tex:1085, Exercise), definition part: ncp-maps `f, g`
are **equivalent** when `f^⋄ = g^⋄`. -/
def NCPEquiv [VonNeumannAlgebra B] (f g : NCPMap A B) : Prop :=
  ∀ e : A, IsStarProjection e → diamondUp f e = diamondUp g e

/-- **101V** (proc.tex:1085, Exercise): `f^⋄ = g^⋄` iff `f_⋄ = g_⋄`. -/
theorem ncpEquiv_iff [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f g : NCPMap A B) :
    NCPEquiv f g ↔
      ∀ e : B, IsStarProjection e → diamondDown f e = diamondDown g e := by
  -- both sides say that the two Galois connections of 101IV.1 agree
  constructor
  · intro h e he
    refine starProj_eq_of_perp_iff (fun t ht => ?_) (diamondDown_spec f he).1
      (diamondDown_spec g he).1
    rw [← diamond_suprema_1 f t e ht he, ← diamond_suprema_1 g t e ht he, h t ht]
  · intro h s hs
    refine starProj_eq_of_perp_iff (fun t ht => ?_) (isStarProjection_diamondUp f s)
      (isStarProjection_diamondUp g s)
    rw [diamond_suprema_1 f s t hs ht, diamond_suprema_1 g s t hs ht, h t ht]

/-- **101VI** (`contraposed`, proc.tex:1091): ncp-maps `f : 𝒜 → ℬ` and
`g : ℬ → 𝒜` are **contraposed** when
`⌈f(s)⌉ ≤ t^⊥ ⟺ ⌈g(t)⌉ ≤ s^⊥` for all projections `s`, `t`. -/
def Contraposed [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) : Prop :=
  ∀ s t, IsStarProjection s → IsStarProjection t →
    (diamondUp f s ≤ 1 - t ↔ diamondUp g t ≤ 1 - s)

/-- Contraposition is a symmetric relation (immediately from the
definition). -/
theorem contraposed_symm [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) : Contraposed f g ↔ Contraposed g f :=
  ⟨fun h s t hs ht => (h t s ht hs).symm, fun h s t hs ht => (h t s ht hs).symm⟩

/-- **101VI** (`contraposed`, proc.tex:1091), the workhorse: `f^⋄ = g_⋄`
iff `f` and `g` are contraposed. -/
theorem contraposed_iff_diamond [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) :
    (∀ s, IsStarProjection s → diamondUp f s = diamondDown g s) ↔
      Contraposed f g := by
  constructor
  · intro h s t hs ht
    rw [diamond_suprema_1 g t s ht hs, ← h s hs]
  · intro h s hs
    refine starProj_eq_of_perp_iff (fun t ht => ?_) (isStarProjection_diamondUp f s)
      (diamondDown_spec g hs).1
    rw [← diamond_suprema_1 g t s ht hs]
    exact h s t hs ht

/-- **101VI** (`contraposed`, proc.tex:1091): `f^⋄ = g_⋄` iff `f_⋄ = g^⋄`
iff `f` and `g` are contraposed. -/
theorem contraposed_iff [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) :
    ((∀ s, IsStarProjection s → diamondUp f s = diamondDown g s) ↔
        (∀ t, IsStarProjection t → diamondUp g t = diamondDown f t)) ∧
      ((∀ s, IsStarProjection s → diamondUp f s = diamondDown g s) ↔
        Contraposed f g) :=
  ⟨(contraposed_iff_diamond f g).trans
      ((contraposed_symm f g).trans (contraposed_iff_diamond g f).symm),
    contraposed_iff_diamond f g⟩

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 1:
the maps `a*(·)a` and `a(·)a*` on a von Neumann algebra are contraposed. -/
theorem equivalent_examples_1 [VonNeumannAlgebra A] (a : A) :
    Contraposed (adSelf a) (adSelf (star a)) := by
  -- both `⌈a* s a⌉ ≤ t^⊥` and `⌈a t a*⌉ ≤ s^⊥` say `s a t = 0`
  intro s t hs ht
  have e1 : diamondUp (adSelf a) s = ceil (star a * s * a) := by
    show ceil (adSelf a s) = _
    rw [adSelf_apply]
  have e2 : diamondUp (adSelf (star a)) t = ceil (star (star a) * t * star a) := by
    show ceil (adSelf (star a) t) = _
    rw [adSelf_apply]
  have h1 : diamondUp (adSelf a) s ≤ 1 - t ↔ s * a * t = 0 := by
    rw [e1, ceil_le_perp_iff (star_left_conjugate_nonneg hs.nonneg a) ht]
    exact conj_perp_eq_zero_iff hs ht
  have h2 : diamondUp (adSelf (star a)) t ≤ 1 - s ↔ s * a * t = 0 := by
    rw [e2, ceil_le_perp_iff (star_left_conjugate_nonneg ht.nonneg (star a)) hs,
      conj_perp_eq_zero_iff ht hs, ← mul_triple_eq_zero_iff_star hs ht]
  rw [h1, h2]

/-- Infrastructure for 101VII.1: a projection of the corner `e𝒜e` is a
projection of `𝒜`. -/
private theorem isStarProjection_val_of_corner [VonNeumannAlgebra A] {e : A}
    [Fact (IsStarProjection e)] {x : Corner A e} (hx : IsStarProjection x) :
    IsStarProjection x.val := by
  refine ⟨?_, ?_⟩
  · show x.val * x.val = x.val
    rw [← Corner.val_mul]
    exact congrArg Corner.val hx.isIdempotentElem.eq
  · show star x.val = x.val
    rw [← Corner.val_star]
    exact congrArg Corner.val hx.isSelfAdjoint.star_eq

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 1,
**middle clause**: if `p` and `q` are projections of `𝒜` with `a*pa ≤ q`
(the situation of **94III** `ad-ncp`), the maps `a*(·)a : p𝒜p → q𝒜q` and
`a(·)a* : q𝒜q → p𝒜p` are contraposed.

The two maps are carried as ncp-maps between the corners *given by* their
formulas — which is how 94III.2 supplies the first one (`adNCP`).  Stating
it that way is what makes the clause true as printed: `a*pa ≤ q` is exactly
what puts `a*(·)a` inside `q𝒜q`, but the printed clause offers nothing to
put `a(·)a*` inside `p𝒜p`, and without such a hypothesis the second map
does not exist (`p = 0`, `q = 1`, `a = 1`: then `a*pa = 0 ≤ q`, while
`a(·)a*` is the identity `𝒜 → 0`).  Assuming the maps rather than
constructing them assumes neither `a*pa ≤ q` nor its mirror `aqa* ≤ p`, and
both instances of the clause — `adNCP` and the corner/filter pair of the
"in particular" below — supply them.

Proof: the argument of `equivalent_examples_1` read inside the corners.
Both sides say `x a t = 0` for the projections `x` of `p𝒜p` and `t` of
`q𝒜q`. -/
theorem equivalent_examples_1_corners [VonNeumannAlgebra A] (a p q : A)
    [Fact (IsStarProjection p)] [Fact (IsStarProjection q)]
    (f : NCPMap (Corner A p) (Corner A q)) (g : NCPMap (Corner A q) (Corner A p))
    (hf : ∀ b : Corner A p, (f b).val = star a * b.val * a)
    (hg : ∀ b : Corner A q, (g b).val = a * b.val * star a) :
    Contraposed f g := by
  intro x t hx ht
  have hxv : IsStarProjection x.val := isStarProjection_val_of_corner hx
  have htv : IsStarProjection t.val := isStarProjection_val_of_corner ht
  have hfx : (0 : Corner A q) ≤ f x := ncpMap_nonneg f hx.nonneg
  have hgt : (0 : Corner A p) ≤ g t := ncpMap_nonneg g ht.nonneg
  -- `⌈f(x)⌉ ≤ t^⊥` in `q𝒜q` is `t (a* x a) t = 0` in `𝒜`
  have hL : (diamondUp f x ≤ 1 - t) ↔ t.val * (star a * x.val * a) * t.val = 0 := by
    have hval : (t * f x * t).val = t.val * (star a * x.val * a) * t.val := by
      rw [Corner.val_mul, Corner.val_mul, hf]
    show ceil (f x) ≤ 1 - t ↔ _
    rw [ceil_le_perp_iff hfx ht]
    exact ⟨fun h => by rw [← hval, h, Corner.val_zero],
      fun h => Corner.val_injective (by rw [hval, Corner.val_zero, h])⟩
  -- `⌈g(t)⌉ ≤ x^⊥` in `p𝒜p` is `x (a t a*) x = 0` in `𝒜`
  have hR : (diamondUp g t ≤ 1 - x) ↔ x.val * (a * t.val * star a) * x.val = 0 := by
    have hval : (x * g t * x).val = x.val * (a * t.val * star a) * x.val := by
      rw [Corner.val_mul, Corner.val_mul, hg]
    show ceil (g t) ≤ 1 - x ↔ _
    rw [ceil_le_perp_iff hgt hx]
    exact ⟨fun h => by rw [← hval, h, Corner.val_zero],
      fun h => Corner.val_injective (by rw [hval, Corner.val_zero, h])⟩
  rw [hL, hR, conj_perp_eq_zero_iff (x := a) hxv htv,
    show a * t.val * star a = star (star a) * t.val * star a from by rw [star_star],
    conj_perp_eq_zero_iff (x := star a) htv hxv]
  exact mul_triple_eq_zero_iff_star hxv htv


/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 1,
**third clause** ("in particular"): the standard corner `π_s` and the
standard filter `c_s` of a projection `s` are contraposed (the filter of a
projection being the inclusion).

The thesis reads this off the middle clause
(`equivalent_examples_1_corners`) at `p = 1`, `q = s`, `a = s`.  Here it is
proved directly instead, because `π_s` has domain `𝒜` rather than the
corner `Corner A 1`, and the two are isomorphic but not identical; the
argument is the same one. -/
theorem equivalent_examples_1' [VonNeumannAlgebra A] (s : A)
    [Fact (IsStarProjection s)] :
    Contraposed (cornerProjMap s).toNCPMap (cornerIncl s).toNCPMap := by
  -- the argument of `equivalent_examples_1` carried through the corner:
  -- both sides say `x·t = 0`, once computed in `s𝒜s` and once in `𝒜`
  have hs : IsStarProjection s := Fact.out
  intro x t hx ht
  have htv : IsStarProjection t.val := by
    refine ⟨?_, ?_⟩
    · show t.val * t.val = t.val
      rw [← Corner.val_mul]
      exact congrArg Corner.val ht.isIdempotentElem.eq
    · show star t.val = t.val
      rw [← Corner.val_star]
      exact congrArg Corner.val ht.isSelfAdjoint.star_eq
  have htvs : t.val * s = t.val := Corner.mul_right t
  have hstv : s * t.val = t.val := Corner.mul_left t
  have hπnn : (0 : Corner A s) ≤ (cornerProjMap s).toNCPMap x :=
    ncpMap_nonneg _ hx.nonneg
  -- `⌈π_s(x)⌉ ≤ t^⊥` in the corner is `t·x·t = 0` in `𝒜`
  have hL : (diamondUp ((cornerProjMap s).toNCPMap) x ≤ 1 - t) ↔
      t.val * x * t.val = 0 := by
    show ceil ((cornerProjMap s).toNCPMap x) ≤ 1 - t ↔ _
    rw [ceil_le_perp_iff hπnn ht]
    have hval : (t * (cornerProjMap s).toNCPMap x * t).val
        = t.val * x * t.val := by
      rw [Corner.val_mul, Corner.val_mul, cornerProjMap_apply]
      calc t.val * (s * x * s) * t.val
          = t.val * s * x * (s * t.val) := by noncomm_ring
        _ = t.val * x * t.val := by rw [htvs, hstv]
    constructor
    · intro h
      have := congrArg Corner.val h
      rwa [hval, Corner.val_zero] at this
    · intro h
      refine Corner.val_injective ?_
      rw [hval, Corner.val_zero, h]
  -- `⌈c_s(t)⌉ ≤ x^⊥` in `𝒜` is `x·t·x = 0`
  have hR : (diamondUp ((cornerIncl s).toNCPMap) t ≤ 1 - x) ↔
      x * t.val * x = 0 := by
    show ceil ((cornerIncl s).toNCPMap t) ≤ 1 - x ↔ _
    rw [cornerIncl_apply, ceil_le_perp_iff htv.nonneg hx]
  rw [hL, hR]
  have h1 : t.val * x * t.val = 0 ↔ x * t.val = 0 := by
    simpa using conj_perp_eq_zero_iff hx htv (x := 1)
  have h2 : x * t.val * x = 0 ↔ t.val * x = 0 := by
    simpa using conj_perp_eq_zero_iff htv hx (x := 1)
  have h3 : x * t.val = 0 ↔ t.val * x = 0 := by
    simpa using mul_triple_eq_zero_iff_star hx htv (x := 1)
  rw [h1, h2, h3]

/-! ### Infrastructure for **101VII**.2

The exercise's claim is stated for an *arbitrary* ncp-isomorphism, and in
that generality it is **false** (`equivalent_examples_2_is_false` below,
and `ERRATA.md`): the thesis itself notes at proc.tex:282 that there are
non-unital ncp-isomorphisms, and `a(·)a` for an invertible positive
non-central `a` is one — it is contraposed to `a(·)a` (part 1), not to its
inverse `a⁻¹(·)a⁻¹`.  Unitality of `f` repairs it, and is what an
isomorphism of the category `W*_cpsu` of the theses carries anyway (a
subunital iso with subunital inverse is unital: `1 = g(f 1) ≤ g 1 ≤ 1`).

With `f` unital the proof is short, and does not need Kadison's theorem
that a unital order isomorphism is a Jordan isomorphism: it is enough that
`f` maps projections to projections, which follows from the order
structure alone. -/

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 2: a
**unital** ncp-isomorphism is contraposed to its inverse.

The unitality hypothesis `hfu` is **not** in the thesis and is not
redundant — see `equivalent_examples_2_is_false` below and the **101VII.2**
row of `ERRATA.md` (status OPEN), which records the same counterexample and
proposes adding "unital" to the printed Example.  (It is automatic for an
isomorphism of `W*_cpsu`, where the maps are subunital.)
Given it, `g` is unital too, `f` and `g` map projections to projections,
and `f(s) ≤ 1 - t ⟺ s ≤ 1 - g(t)` by applying `g` and `f`. -/
theorem equivalent_examples_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) (hfu : f 1 = 1) : Contraposed f g := by
  have hgu : g 1 = 1 := by rw [← hfu, hgf]
  intro s t hs ht
  have hfs : IsStarProjection (f s) :=
    isStarProjection_map f g hgf hfg hfu hgu hs
  have hgt : IsStarProjection (g t) :=
    isStarProjection_map g f hfg hgf hgu hfu ht
  show ceil (f s) ≤ 1 - t ↔ ceil (g t) ≤ 1 - s
  rw [ceil_of_isStarProjection hfs, ceil_of_isStarProjection hgt]
  constructor
  · intro h
    have := ncpMap_mono g h
    rw [ncpMap_sub, hgu, hgf] at this
    exact perp_symm.mp this
  · intro h
    have := ncpMap_mono f h
    rw [ncpMap_sub, hfu, hfg] at this
    exact perp_symm.mp this

/-! ### **101VII**.2 without unitality is false

The witness lives in `B(ℂ²)` (the von Neumann algebra of **42V**.2, whose
instance is honest), transported from `M₂(ℂ)` along Mathlib's
`Matrix.toEuclideanCLM`.  With
`a = diag(1,2)`, `s = ½!![1,1;1,1]`, `t = ⅕!![4,-2;-2,1]`,
the maps `f = a(·)a` and `g = a⁻¹(·)a⁻¹` are mutually inverse ncp-maps
(both are `adSelf` of a self-adjoint element), `s` and `t` are
projections, and `t·f(s)·t = 0` while `s·g(t)·s = (9/80)!![1,1;1,1] ≠ 0`.
By `ceil_le_perp_iff` that is exactly `⌈f(s)⌉ ≤ t^⊥` and
`¬ ⌈g(t)⌉ ≤ s^⊥`.

Geometrically: `f` sends the line `ℂ(1,1)` to `ℂ(1,2) = t^⊥`, so the left
side holds; but `g` sends `t = ℂ(2,-1)` to `ℂ(4,-1)`, which is *not*
orthogonal to `s = ℂ(1,1)`.  The map contraposed to `f` is `f` itself
(part 1, `equivalent_examples_1`, since `a* = a`). -/

section Counterexample

/-- `ℂ²` as a Hilbert space. -/
private abbrev H₂ : Type := EuclideanSpace ℂ (Fin 2)

/-- `B(ℂ²)`, the von Neumann algebra the counterexample lives in. -/
private abbrev B₂ : Type := H₂ →L[ℂ] H₂

/-- `M₂(ℂ) ≅ B(ℂ²)` as ∗-algebras (Mathlib). -/
private noncomputable def matEmb : Matrix (Fin 2) (Fin 2) ℂ ≃⋆ₐ[ℂ] B₂ :=
  Matrix.toEuclideanCLM

private def ceA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 2]
private def ceA' : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1/2]
private def ceS : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]
private def ceT : Matrix (Fin 2) (Fin 2) ℂ := !![4/5, -2/5; -2/5, 1/5]

private theorem ce_facts :
    star ceA = ceA ∧ star ceA' = ceA' ∧ ceA * ceA' = 1 ∧ ceA' * ceA = 1 ∧
      ceS * ceS = ceS ∧ star ceS = ceS ∧ ceT * ceT = ceT ∧ star ceT = ceT ∧
      ceT * (ceA * ceS * ceA) * ceT = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ceA, ceA', ceS, ceT, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
          Matrix.one_apply] <;>
        norm_num

/-- **101VII**.2 is false as stated in the thesis: there are mutually
inverse ncp-maps that are not contraposed.  See `ERRATA.md`. -/
theorem equivalent_examples_2_is_false :
    ∃ f g : NCPMap B₂ B₂, (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) ∧
      ¬ Contraposed f g := by
  obtain ⟨hstar0, hstar1, h01, h10, hs0, hs0s, ht0, ht0s, hzero⟩ := ce_facts
  have hnz : ceS * (ceA' * ceT * ceA') * ceS ≠ 0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [ceA', ceS, ceT, Matrix.mul_apply, Fin.sum_univ_two] at h00
    norm_num at h00
  set a : B₂ := matEmb ceA with ha
  set b : B₂ := matEmb ceA' with hb
  set s : B₂ := matEmb ceS with hs
  set t : B₂ := matEmb ceT with ht
  have hsa : star a = a := by rw [ha, ← map_star]; exact congrArg matEmb hstar0
  have hsb : star b = b := by rw [hb, ← map_star]; exact congrArg matEmb hstar1
  have hab : a * b = 1 := by rw [ha, hb, ← map_mul, h01, map_one]
  have hba : b * a = 1 := by rw [ha, hb, ← map_mul, h10, map_one]
  have hsproj : IsStarProjection s :=
    ⟨by show matEmb ceS * matEmb ceS = matEmb ceS; rw [← map_mul, hs0],
      by show star (matEmb ceS) = matEmb ceS
         rw [← map_star]; exact congrArg matEmb hs0s⟩
  have htproj : IsStarProjection t :=
    ⟨by show matEmb ceT * matEmb ceT = matEmb ceT; rw [← map_mul, ht0],
      by show star (matEmb ceT) = matEmb ceT
         rw [← map_star]; exact congrArg matEmb ht0s⟩
  refine ⟨adSelf a, adSelf b, ?_, ?_, ?_⟩
  · intro x
    rw [adSelf_apply, adSelf_apply, hsa, hsb]
    calc b * (a * x * a) * b = b * a * x * (a * b) := by noncomm_ring
      _ = x := by rw [hab, hba, one_mul, mul_one]
  · intro x
    rw [adSelf_apply, adSelf_apply, hsa, hsb]
    calc a * (b * x * b) * a = a * b * x * (b * a) := by noncomm_ring
      _ = x := by rw [hab, hba, one_mul, mul_one]
  · intro hcontra
    have hfs : (0 : B₂) ≤ adSelf a s := by
      rw [adSelf_apply]
      exact star_left_conjugate_nonneg hsproj.nonneg a
    have hgt : (0 : B₂) ≤ adSelf b t := by
      rw [adSelf_apply]
      exact star_left_conjugate_nonneg htproj.nonneg b
    have hL : diamondUp (adSelf a) s ≤ 1 - t := by
      show ceil (adSelf a s) ≤ 1 - t
      rw [ceil_le_perp_iff hfs htproj, adSelf_apply, hsa]
      have hrw : t * (a * s * a) * t = matEmb (ceT * (ceA * ceS * ceA) * ceT) := by
        rw [ha, hs, ht]; simp only [← map_mul]
      rw [hrw, hzero, map_zero]
    have hR := (hcontra s t hsproj htproj).mp hL
    rw [show diamondUp (adSelf b) t = ceil (adSelf b t) from rfl,
      ceil_le_perp_iff hgt hsproj, adSelf_apply, hsb] at hR
    have hR' : matEmb (ceS * (ceA' * ceT * ceA') * ceS) = 0 := by
      rw [← hR, hb, hs, ht]; simp only [map_mul]
    exact hnz (by simpa using congrArg matEmb.symm hR')

end Counterexample

/-- **101VII** (`equivalent-examples`, proc.tex:1102, Examples), part 3:
`(zf)^⋄ = f^⋄` for every positive central `z` with `⌈z⌉ = 1`. -/
theorem equivalent_examples_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f h : NCPMap A B) (z : B) (hz : z ∈ centre B) (hz0 : 0 ≤ z)
    (hz1 : ceil z = 1) (hh : ∀ x, h x = z * f x) : NCPEquiv h f := by
  intro e he
  change ceil (h e) = ceil (f e)
  rw [hh]
  exact ceil_central_mul (f e) z (ncpMap_nonneg f he.nonneg) hz0 hz
    (by rw [hz1]; exact (ceil_spec (ncpMap_nonneg f he.nonneg)).1.le_one)

/-- **101VIII** (`diamond-composition`, proc.tex:1134, Exercise), part 1:
`(g ∘ f)^⋄ = g^⋄ ∘ f^⋄` and `(g ∘ f)_⋄ = f_⋄ ∘ g_⋄`. -/
theorem diamond_composition_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (f : NCPMap A B) (g : NCPMap B C) :
    (∀ e : A, IsStarProjection e →
        diamondUp (ncpComp g f) e = diamondUp g (diamondUp f e)) ∧
      ∀ e : C, IsStarProjection e →
        diamondDown (ncpComp g f) e = diamondDown f (diamondDown g e) := by
  -- part 1 *is* `ncp_ceil` (60V); part 2 follows through the Galois
  -- connection 101IV.1, as the author indicates
  have hup : ∀ e : A, IsStarProjection e →
      diamondUp (ncpComp g f) e = diamondUp g (diamondUp f e) := by
    intro e he
    show ceil (ncpComp g f e) = ceil (g (ceil (f e)))
    rw [ncpComp_apply]
    exact ncp_ceil (PositiveLinearMap.ofClass g.toCompletelyPositiveMap)
      g.preservesDirSups' (f e) (ncpMap_nonneg f he.nonneg)
  refine ⟨hup, fun e he => ?_⟩
  refine starProj_eq_of_perp_iff (fun s hs => ?_) (diamondDown_spec _ he).1
    (diamondDown_spec f (diamondDown_spec g he).1).1
  rw [← diamond_suprema_1 (ncpComp g f) s e hs he, hup s hs,
    diamond_suprema_1 g (diamondUp f s) e (isStarProjection_diamondUp f s) he,
    perp_symm, diamond_suprema_1 f s (diamondDown g e) hs (diamondDown_spec g he).1]

/-- **101VIII** (`diamond-composition`, proc.tex:1134, Exercise), part 2:
equivalence of ncp-maps is preserved under composition. -/
theorem diamond_composition_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (f f' : NCPMap A B) (g g' : NCPMap B C)
    (hf : NCPEquiv f f') (hg : NCPEquiv g g') :
    NCPEquiv (ncpComp g f) (ncpComp g' f') := by
  intro e he
  rw [(diamond_composition_1 f g).1 e he, (diamond_composition_1 f' g').1 e he,
    hf e he, hg _ (isStarProjection_diamondUp f' e)]

/-- **101VIII** (`diamond-composition`, proc.tex:1134, Exercise), part 3:
contraposition is preserved under composition (with reversal). -/
theorem diamond_composition_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (f : NCPMap A B) (f' : NCPMap B A)
    (g : NCPMap B C) (g' : NCPMap C B) (hf : Contraposed f f')
    (hg : Contraposed g g') :
    Contraposed (ncpComp g f) (ncpComp f' g') := by
  refine (contraposed_iff_diamond _ _).mp fun s hs => ?_
  rw [(diamond_composition_1 f g).1 s hs, (diamond_composition_1 g' f').2 s hs,
    (contraposed_iff_diamond f f').mpr hf s hs,
    (contraposed_iff_diamond g g').mpr hg _
      (diamondDown_spec f' hs).1]

/-- **101IX** (`diamond-sum`, proc.tex:1162, Proposition):
`(f+g)^⋄(s) = f^⋄(s) ∪ g^⋄(s)` and `(f+g)_⋄(t) = f_⋄(t) ∪ g_⋄(t)`
(the sum `f + g` rendered as any ncp-map `h` with `h = f + g`
pointwise). -/
theorem diamond_sum [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f g h : NCPMap A B) (hh : ∀ a, h a = f a + g a) :
    (∀ s : A, IsStarProjection s →
        diamondUp h s = projSup {diamondUp f s, diamondUp g s}) ∧
      ∀ t : B, IsStarProjection t →
        diamondDown h t = projSup {diamondDown f t, diamondDown g t} := by
  -- the author's argument (proc.tex:1172): part 1 is `ceil-basic`, part 2
  -- runs the Galois connection 101IV.1 on both sides
  have hup : ∀ s : A, IsStarProjection s →
      diamondUp h s = projSup ({diamondUp f s, diamondUp g s} : Set B) := by
    intro s hs
    show ceil (h s) = _
    rw [hh s]
    exact (ceil_basic_4 (f s) (g s) (ncpMap_nonneg f hs.nonneg)
      (ncpMap_nonneg g hs.nonneg) 1 one_pos).2
  refine ⟨hup, fun t ht => ?_⟩
  have hPf := diamondDown_spec f ht
  have hPg := diamondDown_spec g ht
  refine starProj_eq_of_perp_iff (fun s hs => ?_) (diamondDown_spec h ht).1
    (projSup_spec (P := ({diamondDown f t, diamondDown g t} : Set A))
      (by rintro p (rfl | rfl); exacts [hPf.1, hPg.1])).1
  rw [← diamond_suprema_1 h s t hs ht, hup s hs,
    projSup_pair_le_iff (isStarProjection_diamondUp f s)
      (isStarProjection_diamondUp g s) ht.one_sub,
    projSup_pair_le_iff hPf.1 hPg.1 hs.one_sub,
    diamond_suprema_1 f s t hs ht, diamond_suprema_1 g s t hs ht]

/-- **101XI** (`carrier-f-dagger-f`, proc.tex:1187, Lemma): for contraposed
`f : 𝒜 → ℬ` and `g : ℬ → 𝒜` we have `⌈f⌉ = ⌈g ∘ f⌉`. -/
theorem carrier_f_dagger_f [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (g : NCPMap B A) (h : Contraposed f g) :
    ncpCarrier f = ncpCarrier (ncpComp g f) := by
  -- the author's chain (proc.tex:1192):
  -- `⌈gf⌉ = (gf)_⋄(1) = f_⋄(g_⋄(1)) = g^⋄(⌈g⌉) = g^⋄(1) = f_⋄(1) = ⌈f⌉`
  have hgd : ∀ t : B, IsStarProjection t → diamondUp g t = diamondDown f t :=
    (contraposed_iff_diamond g f).mpr ((contraposed_symm f g).mp h)
  have hspec : IsStarProjection (ncpCarrier g) ∧ g (1 - ncpCarrier g) = 0 ∧
      ∀ q : B, IsStarProjection q → g (1 - q) = 0 → ncpCarrier g ≤ q :=
    (exists_ncpCarrier g).choose_spec.1
  have hg1 : (g 1 : A) = g (ncpCarrier g) := by
    have hadd : ∀ y z : B, (g (y + z) : A) = g y + g z := fun y z =>
      map_add g.toCompletelyPositiveMap.toLinearMap y z
    have hsum := hadd (ncpCarrier g) (1 - (ncpCarrier g : B))
    rw [show (ncpCarrier g : B) + (1 - ncpCarrier g) = 1 by abel, hspec.2.1,
      add_zero] at hsum
    exact hsum
  calc ncpCarrier f = diamondDown f 1 := (diamondDown_one f).symm
    _ = diamondUp g 1 := (hgd 1 (IsStarProjection.one (R := B))).symm
    _ = diamondUp g (ncpCarrier g) := by
        show ceil (g 1) = ceil (g (ncpCarrier g))
        rw [hg1]
    _ = diamondDown f (ncpCarrier g) := hgd _ hspec.1
    _ = diamondDown f (diamondDown g 1) := by rw [diamondDown_one]
    _ = diamondDown (ncpComp g f) 1 :=
        ((diamond_composition_1 f g).2 1 (IsStarProjection.one (R := A))).symm
    _ = ncpCarrier (ncpComp g f) := diamondDown_one _

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
    g₁ = f ∧ g₂ = f := by
  -- the author's proof (proc.tex:1219), transcribed; the only Lean-side
  -- addition is `exists_ncpAdd`/`exists_ncpSmul`, since `NCPMap` has no
  -- `+` or `•`.  Note `h₂` is not used: `g₂ 1 = f 1` already follows from
  -- `hconv` at `1` together with `h₁`.
  have hm0 : (0 : ℝ) < 1 - l := sub_pos.mpr hl1
  have hsm : ∀ (x : B) (r : ℝ), 0 ≤ x → 0 < r → ceil (((r : ℝ) : ℂ) • x) = ceil x :=
    fun x r hx hr => (ceil_basic_4 x x hx hx r hr).1
  have hnn : ∀ (x : B) (r : ℝ), 0 ≤ x → 0 ≤ r → (0 : B) ≤ ((r : ℝ) : ℂ) • x := by
    intro x r hx hr
    rw [Complex.coe_smul]; exact smul_nonneg hr hx
  -- `f^⋄(p) = g₁^⋄(p) ∪ g₂^⋄(p)`, by `diamond-sum` (101IX) and
  -- `equivalent-examples` (here in the form `⌈λa⌉ = ⌈a⌉`, 59III.4)
  have hsum : ∀ p : A, IsStarProjection p →
      ceil (f p) = projSup ({ceil (g₁ p), ceil (g₂ p)} : Set B) := by
    intro p hp
    have k1 : (0 : B) ≤ g₁ p := ncpMap_nonneg g₁ hp.nonneg
    have k2 : (0 : B) ≤ g₂ p := ncpMap_nonneg g₂ hp.nonneg
    rw [hconv p, (ceil_basic_4 _ _ (hnn _ l k1 hl0.le) (hnn _ (1 - l) k2 hm0.le) 1 one_pos).2,
      hsm _ l k1 hl0, hsm _ (1 - l) k2 hm0]
  -- "and in particular `g₁^⋄(s) ≤ f^⋄(s)`"
  have hg₁le : ∀ p : A, IsStarProjection p → ceil (g₁ p) ≤ ceil (f p) := by
    intro p hp
    rw [hsum p hp]
    exact (projSup_spec (P := ({ceil (g₁ p), ceil (g₂ p)} : Set B))
      (by rintro q (rfl | rfl) <;> exact isStarProjection_ceil _)).2.1 _ (by left; rfl)
  -- "Then for `h := λ g₁ + λ^⊥ f` we have `h(1) = f(1)` and `h^⋄ = f^⋄`"
  obtain ⟨k₁, hk₁⟩ := exists_ncpSmul g₁ hl0.le
  obtain ⟨k₂, hk₂⟩ := exists_ncpSmul f hm0.le
  obtain ⟨h, hh⟩ := exists_ncpAdd k₁ k₂
  have hha : ∀ a : A, (h a : B) = (l : ℂ) • g₁ a + ((1 - l : ℝ) : ℂ) • f a := by
    intro a; rw [hh, hk₁, hk₂]
  have hone : (h 1 : B) = f 1 := by
    rw [hha, h₁, ← add_smul,
      show ((l : ℝ) : ℂ) + ((1 - l : ℝ) : ℂ) = 1 by push_cast; ring, one_smul]
  have hceil : ∀ p : A, IsStarProjection p → ceil (f p) = ceil (h p) := by
    intro p hp
    have k1 : (0 : B) ≤ g₁ p := ncpMap_nonneg g₁ hp.nonneg
    have kf : (0 : B) ≤ f p := ncpMap_nonneg f hp.nonneg
    rw [hha, (ceil_basic_4 _ _ (hnn _ l k1 hl0.le) (hnn _ (1 - l) kf hm0.le) 1 one_pos).2,
      hsm _ l k1 hl0, hsm _ (1 - l) kf hm0]
    have hP : ∀ q ∈ ({ceil (g₁ p), ceil (f p)} : Set B), IsStarProjection q := by
      rintro q (rfl | rfl) <;> exact isStarProjection_ceil _
    refine le_antisymm ((projSup_spec hP).2.1 _ (by right; rfl)) ?_
    exact (projSup_pair_le_iff (isStarProjection_ceil _) (isStarProjection_ceil _)
      (isStarProjection_ceil _)).mpr ⟨hg₁le p hp, le_rfl⟩
  -- "so that `λ g₁ + λ^⊥ f ≡ h = f = λ g₁ + λ^⊥ g₂` by rigidity of `f`"
  have hhf : h = f := hf h hone hceil
  have hfeq : ∀ a : A, (f a : B) = (l : ℂ) • g₁ a + ((1 - l : ℝ) : ℂ) • f a := by
    intro a; rw [← hha a, hhf]
  -- "and thus `f = g₂`"; `f = g₁` then follows by cancelling `λ ≠ 0`
  -- (the author instead repeats the argument with the roles swapped)
  have hg₂ : g₂ = f := by
    refine DFunLike.ext _ _ fun a => ?_
    have e : ((1 - l : ℝ) : ℂ) • (g₂ a : B) = ((1 - l : ℝ) : ℂ) • f a :=
      add_left_cancel ((hconv a).symm.trans (hfeq a))
    have hne : ((1 - l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hm0)
    have e' := congrArg (fun x : B => (((1 - l : ℝ) : ℂ))⁻¹ • x) e
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at e'
    exact e'
  have hg₁ : g₁ = f := by
    refine DFunLike.ext _ _ fun a => ?_
    have e0 : ((l : ℝ) : ℂ) • (f a : B) + ((1 - l : ℝ) : ℂ) • f a
        = (l : ℂ) • g₁ a + ((1 - l : ℝ) : ℂ) • f a := by
      rw [← hfeq a, ← add_smul,
        show ((l : ℝ) : ℂ) + ((1 - l : ℝ) : ℂ) = 1 by push_cast; ring, one_smul]
    have e : ((l : ℝ) : ℂ) • (f a : B) = ((l : ℝ) : ℂ) • g₁ a := add_right_cancel e0
    have hne : ((l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hl0)
    have e' := congrArg (fun x : B => (((l : ℝ) : ℂ))⁻¹ • x) e
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at e'
    exact e'.symm
  exact ⟨hg₁, hg₂⟩

/-- **102V** (`nmiu-rigid`, proc.tex:1241, Proposition): an nmiu-map
between von Neumann algebras is rigid (stated for an ncp-map `f` that
coincides with an nmiu-map `ρ`). -/
theorem nmiu_rigid [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ρ : NMIUMap A B) (f : NCPMap A B) (h : ∀ a, f a = ρ a) : IsRigid f := by
  -- the author's proof: for an ncp-map `g` with `g(1) = f(1) = 1` and
  -- `⌈g(p)⌉ = ⌈ϱ(p)⌉`, `⌈g(p)⌉⌈g(q)⌉ = ϱ(p)ϱ(q) = ϱ(pq) = 0` when `pq = 0`,
  -- so `g` is multiplicative by **99II**, hence maps projections to
  -- projections, and `g(p) = ⌈g(p)⌉ = ⌈ϱ(p)⌉ = ϱ(p) = f(p)`.  The two
  -- continuous linear maps `g` and `f` then agree on all of `𝒜`, because
  -- the linear span of the projections is norm-dense (**65IV**).
  intro g hg1 hceil
  have hρproj : ∀ p : A, IsStarProjection p → IsStarProjection ((ρ p : B)) := by
    intro p hp
    refine ⟨?_, ?_⟩
    · change (ρ.toStarAlgHom p) * (ρ.toStarAlgHom p) = ρ.toStarAlgHom p
      rw [← map_mul, hp.isIdempotentElem.eq]
    · change star (ρ.toStarAlgHom p) = ρ.toStarAlgHom p
      rw [← map_star, hp.isSelfAdjoint.star_eq]
  have hf1 : (f 1 : B) = 1 := by
    rw [h 1]
    change (ρ.toStarAlgHom 1 : B) = 1
    exact map_one _
  have hgu : (g 1 : B) = 1 := by rw [hg1, hf1]
  have h3 : ∀ p q : A, IsStarProjection p → IsStarProjection q → p * q = 0 →
      ceil (g p) * ceil (g q) = 0 := by
    intro p q hp hq hpq
    rw [← hceil p hp, ← hceil q hq, h p, h q,
      ceil_of_isStarProjection (hρproj p hp), ceil_of_isStarProjection (hρproj q hq)]
    change (ρ.toStarAlgHom p) * (ρ.toStarAlgHom q) = 0
    rw [← map_mul, hpq, map_zero]
  have hmult := gardner_21 g (by rw [hgu]; exact IsStarProjection.one (R := B))
    (gardner_32 g h3)
  have hgproj := isStarProjection_map_of_mul g hmult
  have hagree : ∀ p : A, IsStarProjection p → (g p : B) = f p := by
    intro p hp
    rw [← ceil_of_isStarProjection (hgproj p hp), ← hceil p hp, h p,
      ceil_of_isStarProjection (hρproj p hp), ← h p]
  refine DFunLike.ext _ _ fun x => ?_
  let S : Submodule ℂ A :=
    { carrier := {y : A | (g y : B) = f y}
      add_mem' := by
        intro y z hy hz
        replace hy : (g y : B) = f y := hy
        replace hz : (g z : B) = f z := hz
        change (g (y + z) : B) = f (y + z)
        rw [ncpMap_add, ncpMap_add, hy, hz]
      zero_mem' := by
        change (g 0 : B) = f 0
        rw [ncpMap_zero, ncpMap_zero]
      smul_mem' := by
        intro c y hy
        replace hy : (g y : B) = f y := hy
        change (g (c • y) : B) = f (c • y)
        rw [ncpMap_smul, ncpMap_smul, hy] }
  have hclosed : IsClosed (S : Set A) :=
    isClosed_eq (ncpMap_continuous g) (ncpMap_continuous f)
  exact mem_of_isClosed_of_projections S hclosed hagree x

/-- Auxiliary for **105IV**: the ceiling computed *in a corner* is the
ambient ceiling.  For `0 ≤ x` in `e𝒜e` one has `⌈x⌉ ≤ e` (59III), so the
ambient `⌈x⌉` lies in the corner, and the two least-ness clauses are the
same condition on the same projections. -/
theorem corner_ceil_val [VonNeumannAlgebra A] {e : A}
    [Fact (IsStarProjection e)] (x : Corner A e) (hx : 0 ≤ x) :
    (ceil x).val = ceil x.val := by
  have he : IsStarProjection e := Corner.proj e
  have hx0 : (0 : A) ≤ x.val := hx
  have hcproj : IsStarProjection (ceil x.val) := isStarProjection_ceil x.val
  have hle : ceil x.val ≤ e := (ceil_le_iff hx0 he).mpr (Corner.mul_right x)
  have hce : ceil x.val * e = ceil x.val :=
    ((projection_below_effect e (ceil x.val) ⟨he.nonneg, he.le_one⟩
      hcproj).out 0 7).mp hle
  have hec : e * ceil x.val = ceil x.val := by
    have h := congrArg star hce
    rwa [star_mul, he.isSelfAdjoint.star_eq, hcproj.isSelfAdjoint.star_eq] at h
  have hmem : e * ceil x.val * e = ceil x.val := by rw [hec, hce]
  have hcorner : IsStarProjection (⟨ceil x.val, hmem⟩ : Corner A e) :=
    ⟨Corner.val_injective (by
        show ceil x.val * ceil x.val = ceil x.val
        exact hcproj.isIdempotentElem.eq),
      Corner.val_injective (by
        show star (ceil x.val) = ceil x.val
        exact hcproj.isSelfAdjoint.star_eq)⟩
  refine congrArg Corner.val (ceil_eq_of_isLeast hx hcorner ?_ ?_)
  · exact Corner.val_injective (by
      show x.val * ceil x.val = x.val
      exact (ceil_spec hx0).2.1)
  · intro q hq hxq
    show ceil x.val ≤ q.val
    refine (ceil_spec hx0).2.2 q.val ?_ ?_
    · exact ⟨congrArg Corner.val hq.isIdempotentElem.eq,
        congrArg Corner.val hq.isSelfAdjoint.star_eq⟩
    · exact congrArg Corner.val hxq

/-- Auxiliary for **102VII**: the identity nmiu-map of a von Neumann
algebra.  (`nmiuId` proper lives in `Tensor.lean`, which imports this
file.) -/
private noncomputable def nmiuIdAux (X : Type u) [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] : NMIUMap X X where
  toStarAlgHom := StarAlgHom.id ℂ X
  preservesDirSups' := preservesDirSups_id

/-- Auxiliary for **102VII**: the identity ncp-map of a von Neumann algebra
is rigid — this is **102V** `nmiu-rigid` at `ϱ = id`, and it is the form in
which the thesis's proof of 102VII uses it ("since the identity on `eₙ𝒜eₙ`
is rigid by `nmiu-rigid` …"). -/
private theorem isRigid_ncpId (X : Type u) [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [VonNeumannAlgebra X] : IsRigid (ncpId X) :=
  nmiu_rigid (nmiuIdAux X) (ncpId X) fun a => by rw [ncpId_apply]; rfl

/-- Auxiliary for **102VII**: `‖q‖ ≤ 1` for a projection `q` (needed as the
norm bound in `mult-jus-cont`). -/
private theorem norm_isStarProjection_le_one [VonNeumannAlgebra A] {q : A}
    (hq : IsStarProjection q) : ‖q‖ ≤ 1 := by
  have h : ‖star q * q‖ = ‖q‖ * ‖q‖ := CStarRing.norm_star_mul_self
  rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq] at h
  nlinarith [norm_nonneg q]

/-- Auxiliary for **102VII**, the heart of the thesis's argument
(proc.tex:1290): let `e ≤ r` be projections and `h` a unital ncp-map on
`r𝒜r` such that `⌈e h(p) e⌉ = ⌈e p e⌉` for every projection `p` of `r𝒜r`.
Then `e h(x) e = x` for every `x` in `e𝒜e`.

The proof is the thesis's: the compression `x ↦ e h(x) e : e𝒜e → e𝒜e` is
an ncp-map which agrees with the identity on `1` and on ceilings of
projections, and the identity is rigid by **102V**. -/
private theorem compress_eq_of_ceil [VonNeumannAlgebra A] {r e : A}
    [Fact (IsStarProjection r)] [Fact (IsStarProjection e)] (hle : e ≤ r)
    (h : NCPMap (Corner A r) (Corner A r)) (hh1 : (h 1).val = r)
    (hceil : ∀ P : Corner A r, IsStarProjection P →
      ceil (e * (h P).val * e) = ceil (e * P.val * e))
    (x : Corner A r) (hx : e * x.val * e = x.val) :
    e * (h x).val * e = x.val := by
  have hr : IsStarProjection r := Corner.proj r
  have he : IsStarProjection e := Corner.proj e
  have hse : star e = e := he.isSelfAdjoint.star_eq
  have hee : e * e = e := he.isIdempotentElem.eq
  have her : e * r = e :=
    ((projection_below_effect r e ⟨hr.nonneg, hr.le_one⟩ he).out 0 7).mp hle
  have hre : r * e = e :=
    ((projection_below_effect r e ⟨hr.nonneg, hr.le_one⟩ he).out 0 6).mp hle
  -- the inclusion `e𝒜e → r𝒜r` and the compression `r𝒜r → e𝒜e`
  obtain ⟨ι, hι⟩ := exists_adNCP (A := A) e e r
    (by rw [hse, hee, hee]; exact hle)
  obtain ⟨κ, hκ⟩ := exists_adNCP (A := A) e r e
    (le_of_eq (by rw [hse, her, hee]))
  have hιval : ∀ y : Corner A e, (ι y).val = y.val := by
    intro y
    rw [hι, hse]
    exact y.property
  have hκval : ∀ z : Corner A r, (κ z).val = e * z.val * e := by
    intro z; rw [hκ, hse]
  set k : NCPMap (Corner A e) (Corner A e) := ncpComp κ (ncpComp h ι) with hkdef
  have hkval : ∀ y : Corner A e, (k y).val = e * (h (ι y)).val * e := by
    intro y
    rw [hkdef, ncpComp_apply, ncpComp_apply, hκval]
  -- `k` is unital: apply the ceiling hypothesis at `P = 1 - ι(1)`
  have hone : (k 1 : Corner A e) = 1 := by
    have hι1 : (ι (1 : Corner A e)).val = e := by rw [hιval]; rfl
    -- `Q = 1 - ι 1` is a projection of `r𝒜r`
    set Q : Corner A r := 1 - ι 1 with hQdef
    have hQval : Q.val = r - e := by rw [hQdef]; simp [hι1]
    have hQproj : IsStarProjection Q := by
      constructor
      · refine Corner.val_injective ?_
        show Q.val * Q.val = Q.val
        rw [hQval]
        calc (r - e) * (r - e) = r * r - r * e - e * r + e * e := by noncomm_ring
          _ = r - e := by rw [hr.isIdempotentElem.eq, hre, her, hee]; abel
      · refine Corner.val_injective ?_
        show star Q.val = Q.val
        rw [hQval, star_sub, hr.isSelfAdjoint.star_eq, hse]
    have hQ0 : ceil (e * (h Q).val * e) = 0 := by
      rw [hceil Q hQproj, hQval]
      have hz : e * (r - e) * e = 0 := by
        have hexp : e * (r - e) * e = (e * r) * e - (e * e) * e := by noncomm_ring
        rw [hexp]
        simp only [her, hee, sub_self]
      rw [hz, ceil_zero]
    have hQnn : (0 : A) ≤ e * (h Q).val * e := by
      have h0 : (0 : Corner A r) ≤ h Q := ncpMap_nonneg h hQproj.nonneg
      have h1 : (0 : A) ≤ (h Q).val := h0
      have := star_left_conjugate_nonneg h1 e
      rwa [hse] at this
    have hQzero : e * (h Q).val * e = 0 := (ceil_basic_3 _ hQnn).mpr hQ0
    have hsub : (h Q).val = r - (h (ι 1)).val := by
      have : (h Q : Corner A r) = h 1 - h (ι 1) := by
        rw [hQdef]; exact ncpMap_sub h 1 (ι 1)
      have hv := congrArg Corner.val this
      rw [Corner.val_sub, hh1] at hv
      exact hv
    refine Corner.val_injective ?_
    rw [hkval, Corner.val_one]
    have hexp : e * (h (ι 1)).val * e = e * r * e - e * (h Q).val * e := by
      rw [hsub]; noncomm_ring
    rw [hexp, hQzero, her, hee, sub_zero]
  -- `k` and the identity have the same ceilings on projections
  have hceilk : ∀ P : Corner A e, IsStarProjection P →
      ceil ((ncpId (Corner A e)) P) = ceil (k P) := by
    intro P hP
    have hPval : IsStarProjection P.val :=
      ⟨congrArg Corner.val hP.isIdempotentElem.eq,
        congrArg Corner.val hP.isSelfAdjoint.star_eq⟩
    have hιP : IsStarProjection (ι P) := by
      constructor
      · exact Corner.val_injective (by
          show (ι P).val * (ι P).val = (ι P).val
          rw [hιval]; exact hPval.isIdempotentElem.eq)
      · exact Corner.val_injective (by
          show star (ι P).val = (ι P).val
          rw [hιval]; exact hPval.isSelfAdjoint.star_eq)
    have hePe : e * P.val * e = P.val := P.property
    refine Corner.val_injective ?_
    have hid0 : (0 : Corner A e) ≤ ncpId (Corner A e) P := by
      rw [ncpId_apply]; exact hP.nonneg
    have hk0 : (0 : Corner A e) ≤ k P := ncpMap_nonneg k hP.nonneg
    rw [corner_ceil_val _ hid0, corner_ceil_val _ hk0,
      ncpId_apply, hkval, hceil (ι P) hιP, hιval, hePe]
  have hkid : k = ncpId (Corner A e) := isRigid_ncpId (Corner A e) k
    (by rw [hone, ncpId_apply]) hceilk
  -- conclude
  have hιx : ι (⟨x.val, hx⟩ : Corner A e) = x :=
    Corner.val_injective (by rw [hιval])
  have hkx := congrArg (fun (m : NCPMap (Corner A e) (Corner A e)) =>
    (m (⟨x.val, hx⟩ : Corner A e)).val) hkid
  simp only [hkval, ncpId_apply, hιx] at hkx
  exact hkx

/-- **102VII** (`canonical-quotient-rigid`, proc.tex:1268, Lemma), in the
index-free form of `isFilter_ad`: any ncp-map `c : e𝒜e → 𝒜` given by the
formula `a ↦ d* a d`, where `e = ⌈d⌉ᵣ`, is rigid.  (`canonical_quotient_rigid`
below is the case `e = ⌈d⌉ᵣ`, `c = c_d`; `stdFilter_rigid` is the case
`d = √p`, which 102IX needs and which would otherwise require a transport
along `⌈p⌉ = ⌈√p⌉ᵣ` inside the dependent type `Corner 𝒜 e`.) -/
theorem ad_rigid [VonNeumannAlgebra A] (b e : A) [Fact (IsStarProjection e)]
    (he : e = rangeProj b) (c : NCPMap (Corner A e) A)
    (hcapp : ∀ a : Corner A e, (c a : A) = star b * a.val * b) : IsRigid c := by
  classical
  subst he
  intro g hg1 hgceil
  set r : A := rangeProj b with hrdef
  have hr : IsStarProjection r := isStarProjection_rangeProj b
  have hrb : r * b = b := (ceill_basic_2 b).1.2
  have hbr : star b * r = star b := by
    have h := congrArg star hrb
    rwa [star_mul, hr.isSelfAdjoint.star_eq] at h
  -- (1) the factorisation `g = c ∘ h` through the filter `c = b*(·)b`
  obtain ⟨h, hh, -⟩ :=
    (isFilter_ad b r rfl c hcapp).universal (Corner A r) g (le_of_eq hg1)
  -- (2) `h` is unital
  have hh1 : (h 1).val = r := by
    refine ad_injective b r rfl ((h 1).property) ?_ ?_
    · show r * r * r = r
      rw [hr.isIdempotentElem.eq, hr.isIdempotentElem.eq]
    · have e1 : star b * (h 1).val * b = (c (h 1) : A) := (hcapp _).symm
      have e2 : (c (h (1 : Corner A r)) : A) = g 1 := (hh 1).symm
      rw [e1, e2, hg1, hcapp, Corner.val_one]
  -- (3) an approximate pseudoinverse of `b`, and the projections `eₙ`
  obtain ⟨t, ht⟩ := approximate_pseudoinverse b
  set p : ℕ → A := fun n => suppProj (t n) with hpdef
  have hpproj : ∀ n, IsStarProjection (p n) := fun n => isStarProjection_suppProj _
  have hlub : IsLUB {x : A | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, p n} r := ht.sum_supp
  obtain ⟨heproj, hemono, hetend⟩ := partialSums_of_isLUB hpproj hlub hr.le_one
  set e : ℕ → A := fun N => ∑ n ∈ Finset.range N, p n with hedef
  have hele : ∀ N, e N ≤ r := fun N => hlub.1 ⟨N, rfl⟩
  have hbs : ∀ N, b * (∑ n ∈ Finset.range N, t n) = e N := by
    intro N
    rw [Finset.mul_sum, hedef]
    exact Finset.sum_congr rfl fun n _ => ht.mul_eq_suppProj n
  -- (4) the ceiling identity `⌈eₙ h(P) eₙ⌉ = ⌈eₙ P eₙ⌉`
  have hceil : ∀ (N : ℕ) (P : Corner A r), IsStarProjection P →
      ceil (e N * (h P).val * e N) = ceil (e N * P.val * e N) := by
    intro N P hP
    set s : A := ∑ n ∈ Finset.range N, t n with hsdef
    have hes : e N = b * s := (hbs N).symm
    have hse : star s * star b = e N := by
      have hst := congrArg star hes
      rw [star_mul, (heproj N).isSelfAdjoint.star_eq] at hst
      exact hst.symm
    have hconj : ∀ y : A, e N * y * e N = star s * (star b * y * b) * s := by
      intro y
      have hexp : star s * (star b * y * b) * s = (star s * star b) * y * (b * s) := by
        noncomm_ring
      rw [hexp, hse, ← hes]
    have hgP : (0 : A) ≤ g P := ncpMap_nonneg g hP.nonneg
    have hcP : (0 : A) ≤ (c P : A) := ncpMap_nonneg c hP.nonneg
    have hstep : star b * (h P).val * b = (g P : A) := by
      rw [← hcapp, ← hh P]
    calc ceil (e N * (h P).val * e N)
        = ceil (star s * (g P : A) * s) := by rw [hconj, hstep]
      _ = ceil (star s * ceil (g P : A) * s) := ceil_fundamental_1 s _ hgP
      _ = ceil (star s * ceil (c P : A) * s) := by rw [hgceil P hP]
      _ = ceil (star s * (c P : A) * s) := (ceil_fundamental_1 s _ hcP).symm
      _ = ceil (e N * P.val * e N) := by rw [hconj, hcapp]
  -- (5) `eₙ h(x) eₙ = x` for `x` in `eₙ𝒜eₙ`, by `compress_eq_of_ceil`
  have hcompress : ∀ (N : ℕ) (x : Corner A r), e N * x.val * e N = x.val →
      e N * (h x).val * e N = x.val := by
    intro N x hx
    have : Fact (IsStarProjection (e N)) := ⟨heproj N⟩
    exact compress_eq_of_ceil (hele N) h hh1 (hceil N) x hx
  -- (6) `eₙ z eₙ → r z r` ultrastrongly, hence ultraweakly (`mult-jus-cont`)
  have hconv : ∀ z : A, UWTendsto (fun N => e N * z * e N) atTop (r * z * r) := by
    intro z
    have hb1 : ∀ N, ‖e N‖ ≤ 1 := fun N => norm_isStarProjection_le_one (heproj N)
    have h1 : USTendsto (fun N => e N * z) atTop (r * z) :=
      mult_jus_cont _ _ _ _ hetend (usTendsto_const z) ⟨1, hb1⟩
    have h2 : USTendsto (fun N => (e N * z) * e N) atTop ((r * z) * r) :=
      mult_jus_cont _ _ _ _ h1 hetend ⟨‖z‖, fun N => by
        calc ‖e N * z‖ ≤ ‖e N‖ * ‖z‖ := norm_mul_le _ _
          _ ≤ 1 * ‖z‖ := by
              exact mul_le_mul_of_nonneg_right (hb1 N) (norm_nonneg z)
          _ = ‖z‖ := one_mul _⟩
    exact uwweaker_2 _ _ _ h2
  -- (7) `h` fixes every `x` supported by some `eₙ`
  have hfix : ∀ (N : ℕ) (x : Corner A r), e N * x.val * e N = x.val →
      (h x).val = x.val := by
    intro N x hx
    have hstab : ∀ M, N ≤ M → e M * x.val * e M = x.val := by
      intro M hNM
      have hle : e N ≤ e M := hemono hNM
      have h1 : e M * e N = e N :=
        ((projection_below_effect (e M) (e N)
          ⟨(heproj M).nonneg, (heproj M).le_one⟩ (heproj N)).out 0 6).mp hle
      have h2 : e N * e M = e N :=
        ((projection_below_effect (e M) (e N)
          ⟨(heproj M).nonneg, (heproj M).le_one⟩ (heproj N)).out 0 7).mp hle
      calc e M * x.val * e M = e M * (e N * x.val * e N) * e M := by rw [hx]
        _ = (e M * e N) * x.val * (e N * e M) := by noncomm_ring
        _ = e N * x.val * e N := by rw [h1, h2]
        _ = x.val := hx
    refine eq_of_forall_npFunctional fun ω => ?_
    have hlim := (uwTendsto_iff _ _ _).mp (hconv ((h x).val)) ω
    have hval : r * (h x).val * r = (h x).val := (h x).property
    rw [hval] at hlim
    have heq : ∀ᶠ M in atTop, (ω (e M * (h x).val * e M) : ℂ) = ω x.val := by
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      rw [hcompress M x (hstab M hM)]
    exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
  -- (8) `h = id`, by ultraweak density of `⋃ₙ eₙ𝒜eₙ`
  have hhid : ∀ x : Corner A r, (h x : Corner A r) = x := by
    intro x
    refine Corner.val_injective (eq_of_forall_npFunctional fun ω => ?_)
    -- the truncations `x_M = e_M x e_M`, all fixed by `h`
    have hmem : ∀ M, e M * (e M * x.val * e M) * e M = e M * x.val * e M := by
      intro M
      calc e M * (e M * x.val * e M) * e M
          = (e M * e M) * x.val * (e M * e M) := by noncomm_ring
        _ = e M * x.val * e M := by rw [(heproj M).isIdempotentElem.eq]
    have hcor : ∀ M, r * (e M * x.val * e M) * r = e M * x.val * e M := by
      intro M
      have h1 : r * e M = e M :=
        ((projection_below_effect r (e M) ⟨hr.nonneg, hr.le_one⟩
          (heproj M)).out 0 6).mp (hele M)
      have h2 : e M * r = e M :=
        ((projection_below_effect r (e M) ⟨hr.nonneg, hr.le_one⟩
          (heproj M)).out 0 7).mp (hele M)
      calc r * (e M * x.val * e M) * r = (r * e M) * x.val * (e M * r) := by
            noncomm_ring
        _ = e M * x.val * e M := by rw [h1, h2]
    set y : ℕ → Corner A r := fun M => ⟨e M * x.val * e M, hcor M⟩ with hydef
    have hyfix : ∀ M, (h (y M)).val = (y M).val := fun M => hfix M (y M) (hmem M)
    -- `ν = ω ∘ h` is an np-functional on the corner, hence of the form
    -- `ω₂(·.val)` by `corner-vna-basic` part 10
    set ν : NPFunctional (Corner A r) :=
      compNP (PositiveLinearMap.ofClass h.toCompletelyPositiveMap)
        h.preservesDirSups' (Corner.restrictNP r ω) with hνdef
    obtain ⟨ω₂, -, hω₂⟩ := corner_vna_basic_10 r ν
    have hxval : r * x.val * r = x.val := x.property
    have hconvx := (uwTendsto_iff _ _ _).mp (hconv x.val) ω
    rw [hxval] at hconvx
    have hconvx₂ := (uwTendsto_iff _ _ _).mp (hconv x.val) ω₂
    rw [hxval] at hconvx₂
    have hL : Filter.Tendsto (fun M => (ω ((h (y M)).val) : ℂ)) atTop
        (𝓝 (ω x.val)) := by
      refine hconvx.congr fun M => ?_
      rw [hyfix M]
    have hR : Filter.Tendsto (fun M => (ω ((h (y M)).val) : ℂ)) atTop
        (𝓝 (ω ((h x).val))) := by
      have hrep : ∀ z : Corner A r, (ω ((h z).val) : ℂ) = ω₂ z.val := fun z =>
        hω₂ z
      simp only [hrep]
      exact hconvx₂.congr fun M => rfl
    exact tendsto_nhds_unique hR hL
  refine DFunLike.ext _ _ fun x => ?_
  rw [hh x, hhid x]

/-- **102VII** (`canonical-quotient-rigid`, proc.tex:1268, Lemma): for an
element `b` of a von Neumann algebra the ncp-map
`a ↦ b* a b : ⌈b⌉ᵣ𝒜⌈b⌉ᵣ → 𝒜` is rigid. -/
theorem canonical_quotient_rigid [VonNeumannAlgebra A] (b : A) :
    IsRigid (canonicalFilter b) :=
  ad_rigid b (rangeProj b) rfl (canonicalFilter b) (canonicalFilter_apply b)

/-- **102VII** for the *standard* filter `c_p = √p(·)√p` of a positive `p`
(the form 102IX uses). -/
theorem stdFilter_rigid [VonNeumannAlgebra A] (p : A) (hp : 0 ≤ p) :
    IsRigid (stdFilter p) := by
  refine ad_rigid (CFC.sqrt p) (ceil p) (ceil_eq_rangeProj_sqrt hp)
    (stdFilter p) fun a => ?_
  rw [stdFilter_apply, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq]

/-- **102IX** (`pure-is-rigid`, proc.tex:1341, Theorem): every pure map
between von Neumann algebras is rigid. -/
theorem pure_is_rigid [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) : IsRigid f := by
  classical
  intro g hg1 hgceil
  have hp : (0 : B) ≤ f 1 := ncpMap_nonneg f zero_le_one
  have hcfp : IsStarProjection (ncpCarrier f) := isStarProjection_ncpCarrier f
  have hspecf : IsStarProjection (ncpCarrier f) ∧ (f (1 - ncpCarrier f) : B) = 0 ∧
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → ncpCarrier f ≤ q :=
    (exists_ncpCarrier f).choose_spec.1
  have hspecg : IsStarProjection (ncpCarrier g) ∧ (g (1 - ncpCarrier g) : B) = 0 ∧
      ∀ q : A, IsStarProjection q → g (1 - q) = 0 → ncpCarrier g ≤ q :=
    (exists_ncpCarrier g).choose_spec.1
  -- (1) `⌈f⌉ = ⌈g⌉`: the two carriers are least in the *same* set of
  -- projections, because `f(q^⊥) = 0 ↔ ⌈f(q^⊥)⌉ = 0 ↔ ⌈g(q^⊥)⌉ = 0 ↔ g(q^⊥) = 0`
  have hzero : ∀ q : A, IsStarProjection q →
      ((f (1 - q) : B) = 0 ↔ (g (1 - q) : B) = 0) := by
    intro q hq
    have hfn : (0 : B) ≤ f (1 - q) := ncpMap_nonneg f (sub_nonneg.mpr hq.le_one)
    have hgn : (0 : B) ≤ g (1 - q) := ncpMap_nonneg g (sub_nonneg.mpr hq.le_one)
    rw [ceil_basic_3 _ hfn, ceil_basic_3 _ hgn, hgceil _ hq.one_sub]
  have hcarrier : ncpCarrier g = ncpCarrier f := by
    refine le_antisymm (hspecg.2.2 _ hcfp ((hzero _ hcfp).mp hspecf.2.1))
      (hspecf.2.2 _ hspecg.1 ((hzero _ hspecg.1).mpr hspecg.2.1))
  -- (2) `g` factors through the corner `π_{⌈f⌉}` of `⌈f⌉ = ⌈g⌉`
  have hπ : IsCornerOf (ncpCarrier f) (cornerProjMap (ncpCarrier f)).toNCPMap :=
    isCornerOf_cornerProjMap _ _ hcfp (floor_of_isStarProjection hcfp)
  have hgperp : (g (1 - ncpCarrier f) : B) = 0 := by
    rw [← hcarrier]; exact hspecg.2.1
  obtain ⟨h, hh, -⟩ := hπ.universal B g hgperp
  have hπ1 : ((cornerProjMap (ncpCarrier f)).toNCPMap 1 : Corner A (ncpCarrier f))
      = 1 := by
    refine Corner.val_injective ?_
    rw [cornerProjMap_apply, Corner.val_one, mul_one, hcfp.isIdempotentElem.eq]
  have hh1 : (h 1 : B) = f 1 := by rw [← hπ1, ← hh 1, hg1]
  -- (3) `[f]` is an isomorphism, by **100III**
  obtain ⟨hfu, finv, hinvl, hinvr⟩ := ((pure_fundamental f).out 0 2).mp hf
  have hfinvu : (finv 1 : Corner A (ncpCarrier f)) = 1 := by
    rw [← hfu, hinvl]
  -- (4) `h ∘ [f]⁻¹ = c_{f(1)}`, by rigidity of `c_{f(1)}` (**102VII**)
  have hsquare := (square_f f).1
  have hcomp : ncpComp h finv = stdFilter (f 1) := by
    refine stdFilter_rigid (f 1) hp (ncpComp h finv) ?_ ?_
    · rw [ncpComp_apply, hfinvu, hh1, stdFilter_one hp]
    · intro Q hQ
      -- `Q = [f](q)` with `q = [f]⁻¹(Q)` a projection, and `π(q) = q`
      have hq : IsStarProjection (finv Q) :=
        isStarProjection_map finv (sqBracket f) hinvr hinvl hfinvu hfu hQ
      have hqval : IsStarProjection ((finv Q).val) :=
        ⟨congrArg Corner.val hq.isIdempotentElem.eq,
          congrArg Corner.val hq.isSelfAdjoint.star_eq⟩
      have hπq : ((cornerProjMap (ncpCarrier f)).toNCPMap ((finv Q).val)
          : Corner A (ncpCarrier f)) = finv Q := by
        refine Corner.val_injective ?_
        rw [cornerProjMap_apply]
        exact (finv Q).property
      have hfq : (f ((finv Q).val) : B) = stdFilter (f 1) Q := by
        rw [hsquare, hπq, hinvr]
      have hhq : (h (finv Q) : B) = g ((finv Q).val) := by
        rw [hh ((finv Q).val), hπq]
      rw [ncpComp_apply, hhq, ← hgceil _ hqval, hfq]
  -- (5) conclude
  refine DFunLike.ext _ _ fun a => ?_
  calc (g a : B) = h ((cornerProjMap (ncpCarrier f)).toNCPMap a) := hh a
    _ = h (finv (sqBracket f ((cornerProjMap (ncpCarrier f)).toNCPMap a))) := by
        rw [hinvl]
    _ = ncpComp h finv (sqBracket f ((cornerProjMap (ncpCarrier f)).toNCPMap a)) :=
        (ncpComp_apply _ _ _).symm
    _ = f a := by rw [hcomp, ← hsquare]

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
    (ha : IsSelfAdjoint a) : IsDiamondSelfAdjoint (adSelf a) := by
  -- purity is 100II.3; contraposition to itself is 101VII.1 at `a* = a`
  refine ⟨isPure_adSelf a, ?_⟩
  have h := equivalent_examples_1 a
  rwa [ha.star_eq] at h

/-- **103II** (`purely-positive-examples`, proc.tex:1412, Examples),
part 2: for positive `a` the map `a(·)a` is ⋄-positive. -/
theorem purely_positive_examples_2 [VonNeumannAlgebra A] (a : A)
    (ha : 0 ≤ a) : IsDiamondPositive (adSelf a) := by
  -- `a(·)a = g ∘ g` for `g = √a(·)√a`, which is ⋄-self-adjoint by part 1
  have hsa : IsSelfAdjoint (CFC.sqrt a) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  refine ⟨adSelf (CFC.sqrt a), purely_positive_examples_1 _ hsa, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  rw [ncpComp_apply, adSelf_apply, adSelf_apply, adSelf_apply, hsa.star_eq,
    (IsSelfAdjoint.of_nonneg ha).star_eq]
  calc a * x * a
      = (CFC.sqrt a * CFC.sqrt a) * x * (CFC.sqrt a * CFC.sqrt a) := by
        rw [CFC.sqrt_mul_sqrt_self a ha]
    _ = CFC.sqrt a * (CFC.sqrt a * x * CFC.sqrt a) * CFC.sqrt a := by noncomm_ring

/-- **103III** (`purely-positive-basic`, proc.tex:1425, Exercise), part 1:
`⌈f⌉ = ⌈f(1)⌉` for a ⋄-self-adjoint `f`. -/
theorem purely_positive_basic_1 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) : ncpCarrier f = ceil (f 1) := by
  -- `⌈f⌉ = f_⋄(1) = f^⋄(1) = ⌈f(1)⌉`; only `f^⋄ = f_⋄` is used
  have hd : diamondUp f 1 = diamondDown f 1 :=
    (contraposed_iff_diamond f f).mpr hf.2 1 (IsStarProjection.one (R := A))
  rw [← diamondDown_one f, ← hd]
  rfl

/-- **103III** (`purely-positive-basic`, proc.tex:1425, Exercise), part 2:
if `f` is ⋄-self-adjoint then so is `f ∘ f`, and `⌈f∘f⌉ = ⌈f⌉`. -/
theorem purely_positive_basic_2 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) :
    IsDiamondSelfAdjoint (ncpComp f f) ∧
      ncpCarrier (ncpComp f f) = ncpCarrier f :=
  ⟨⟨IsPure.comp hf.1 hf.1, diamond_composition_3 f f f f hf.2 hf.2⟩,
    (carrier_f_dagger_f f f hf.2).symm⟩

/-- **103III** (`purely-positive-basic`, proc.tex:1425, Exercise), part 3:
a ⋄-positive map is ⋄-self-adjoint. -/
theorem purely_positive_basic_3 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondPositive f) : IsDiamondSelfAdjoint f := by
  obtain ⟨g, hg, rfl⟩ := hf
  exact (purely_positive_basic_2 g hg).1

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
    (∀ a : A, a * p = p * a → a * q = q * a) ∧ p * q = q * p := by
  -- Exercise, no author argument.  If `a` commutes with `p` then it commutes
  -- with `cp = dq`, and since `d` is central this says `d(aq − qa) = 0`,
  -- hence also `(aq − qa)d = 0`; passing to the carrier gives
  -- `⌈d⌉(aq − qa) = 0 = (aq − qa)⌈d⌉`.  Because `⌈q⌉ ≤ ⌈d⌉` we have
  -- `⌈d⌉q = q = q⌈d⌉`, so those two read `⌈d⌉aq = qa` and `aq = qa⌈d⌉`;
  -- multiplying the second by `⌈d⌉` on the left turns it into `⌈d⌉aq = aq`.
  -- (Note `0 ≤ p` is not needed.)
  obtain ⟨c, d, hc, hd, hc0, hd0, hcd, hpc, hqd⟩ := h
  have hqsa : IsSelfAdjoint q := IsSelfAdjoint.of_nonneg hq
  have hdsa : IsSelfAdjoint d := IsSelfAdjoint.of_nonneg hd0
  have hcdproj : IsStarProjection (ceil d) := (ceil_spec hd0).1
  have h1 : ceil q * ceil d = ceil q :=
    ((ceil_spec hq).1.le_iff_mul_eq_left hcdproj).mp hqd
  have h2 : q * ceil q = q := (ceil_spec hq).2.1
  have hr : q * ceil d = q := by
    conv_lhs => rw [← h2]
    rw [mul_assoc, h1, h2]
  have hl : ceil d * q = q := by
    have hs := congrArg star hr
    rwa [star_mul, hcdproj.isSelfAdjoint.star_eq, hqsa.star_eq] at hs
  have key : ∀ a : A, a * p = p * a → a * q = q * a := by
    intro a hap
    have hacp : a * (c * p) = c * p * a := by
      calc a * (c * p) = (a * c) * p := (mul_assoc _ _ _).symm
        _ = (c * a) * p := by rw [hc a (Set.mem_univ a)]
        _ = c * (a * p) := mul_assoc _ _ _
        _ = c * (p * a) := by rw [hap]
        _ = c * p * a := (mul_assoc _ _ _).symm
    rw [hcd] at hacp
    have hdx : d * (a * q - q * a) = 0 := by
      have e1 : a * (d * q) = d * (a * q) := by
        rw [← mul_assoc, hd a (Set.mem_univ a), mul_assoc]
      rw [e1, mul_assoc] at hacp
      rw [mul_sub, hacp, sub_self]
    have hxd : (a * q - q * a) * d = 0 := by
      rw [hd _ (Set.mem_univ _)]; exact hdx
    have hcx : ceil d * (a * q - q * a) = 0 := ceil_mul_eq_zero hd0 hdx
    have hxc : (a * q - q * a) * ceil d = 0 := by
      have hs := congrArg star hxd
      rw [star_mul, hdsa.star_eq, star_zero] at hs
      have h3 := ceil_mul_eq_zero hd0 hs
      have h4 := congrArg star h3
      rwa [star_mul, star_star, hcdproj.isSelfAdjoint.star_eq, star_zero] at h4
    have e1 : a * q = q * a * ceil d := by
      rw [sub_mul, mul_assoc a q (ceil d), hr] at hxc
      exact sub_eq_zero.mp hxc
    have e2 : ceil d * (a * q) = q * a := by
      rw [mul_sub, ← mul_assoc (ceil d) q a, hl] at hcx
      exact sub_eq_zero.mp hcx
    have e3 : ceil d * (a * q) = a * q := by
      rw [e1, ← mul_assoc, ← mul_assoc, hl]
    exact e3.symm.trans e2
  exact ⟨key, key p rfl⟩

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 2: centrally similar `p, q` have `⌈p⌉ = ⌈q⌉`. -/
theorem centrally_similar_basic_2 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : CentrallySimilar p q) :
    ceil p = ceil q := by
  -- `⌈cp⌉ = ⌈p⌉` and `⌈dq⌉ = ⌈q⌉` by `ceil_central_mul`, and `cp = dq`
  obtain ⟨c, d, hc, hd, hc0, hd0, hcd, hpc, hqd⟩ := h
  rw [← ceil_central_mul p c hp hc0 hc hpc, hcd,
    ceil_central_mul q d hq hd0 hd hqd]

/-- Infrastructure: `⌈1⌉ = 1`. -/
theorem ceil_one [VonNeumannAlgebra A] : ceil (1 : A) = 1 := by
  have h := (ceil_spec (zero_le_one (α := A))).2.1
  rwa [one_mul] at h

/-- **104III**.2a, obstruction: central similarity to `1` forces `⌈p⌉ = 1`.
Immediate from part 2 (`centrally_similar_basic_2`) and `ceil_one`. -/
theorem centrally_similar_one_carrier [VonNeumannAlgebra A] (p : A)
    (hp : 0 ≤ p) (h : CentrallySimilar p 1) : ceil p = 1 := by
  have h2 := centrally_similar_basic_2 p 1 hp zero_le_one h
  rwa [ceil_one] at h2

/-- **104III**.2a, obstruction (projection form): a *central projection* `e`
is centrally similar to `1` only if `e = 1`.  So the printed claim "`p` is
centrally similar to `1` iff `p` is central" would force every central
projection of every von Neumann algebra to be `1`. -/
theorem centrally_similar_one_of_isStarProjection [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) (h : CentrallySimilar e 1) : e = 1 := by
  have hce : ceil e = e := by
    refine le_antisymm ((ceil_spec he.nonneg).2.2 e he he.isIdempotentElem.eq) ?_
    exact (he.le_iff_mul_eq_left (ceil_spec he.nonneg).1).mpr (ceil_spec he.nonneg).2.1
  rw [← hce]
  exact centrally_similar_one_carrier e he.nonneg h

/-- **104III**.2a, obstruction to the *third* claim: every projection is
centrally similar to its own square (`e² = e`, so `c = d = 1` works).  So
"`p` is centrally similar to `p²` iff `p` is central" would force every
projection of every von Neumann algebra to be central — false already in
`M₂(ℂ)` at `e = diag(1,0)`.  Together with
`centrally_similar_basic_2a_counterexample` this refutes all three claims
of 2a; the common repair is the faithfulness hypothesis `⌈p⌉ = ⌈q⌉ = 1`
that 104VII states explicitly. -/
theorem centrally_similar_sq_of_isStarProjection [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) : CentrallySimilar e (e ^ 2) := by
  have hsq : e ^ 2 = e := by rw [sq, he.isIdempotentElem.eq]
  refine ⟨1, 1, fun m _ => by rw [one_mul, mul_one],
    fun m _ => by rw [one_mul, mul_one], zero_le_one, zero_le_one,
    by rw [hsq], ?_, ?_⟩
  · rw [ceil_one]; exact (ceil_spec he.nonneg).1.le_one
  · rw [hsq, ceil_one]; exact (ceil_spec he.nonneg).1.le_one

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise), part 2a
is **FALSE as printed** in its first two claims; this is the counterexample.
Take `𝒜 = ℂ`, `p = 0`, `q = 1`, `B = 1`.  Then `p ≤ B·q`, `p/q = 0` is
central and `p` itself is central, yet `p` and `q` are *not* centrally
similar — by part 2 they would have to satisfy `⌈p⌉ = ⌈q⌉`, i.e. `0 = 1`.
The missing hypothesis is faithfulness.  The author's repair of 2026-08-19
(erratum `parsec-1040.30`) is already in proc.tex: part 2a now assumes
`⌈p⌉ = ⌈q⌉ = 1` and replaces `p ≤ Bq` by `p² ≤ Bq²` — see
`centrally_similar_basic_2a` below.  (There is therefore no 104III row in
`ERRATA.md`; the ruling closed it.  An earlier revision of this note proposed
`⌈p⌉ = ⌈q⌉`, or `q ≤ B'·p` alongside `p ≤ B·q`, which is *not* the repair that
was adopted.)  `p = 0` is only the smallest witness —
`p = (1,0)` and `q = (1,1)` in `ℂ²` fail the same way, and by
`centrally_similar_one_of_isStarProjection` *every* central projection
`≠ 1` is a witness, so this is not a degeneracy at `0`. -/
theorem centrally_similar_basic_2a_counterexample :
    (0 : ℂ) ∈ centre ℂ ∧ (0 : ℂ) ≤ ((1 : ℝ) : ℂ) • (1 : ℂ) ∧
      div (0 : ℂ) 1 ∈ centre ℂ ∧ ¬ CentrallySimilar (0 : ℂ) 1 := by
  have hd : div (0 : ℂ) 1 = 0 := div_eq (by simp) (by simp)
  refine ⟨fun m _ => by ring, by norm_num,
    by rw [hd]; exact fun m _ => by ring, fun h => ?_⟩
  have h0 := centrally_similar_one_carrier (0 : ℂ) le_rfl h
  rw [ceil_zero] at h0
  exact zero_ne_one h0

/-- Cancelling a faithful positive element on the left: `⌈b⌉ = 1` and
`b·y = 0` give `y = 0`. -/
private theorem eq_zero_of_faithful_mul [VonNeumannAlgebra A] {b y : A} (hb : 0 ≤ b)
    (hcb : ceil b = 1) (h : b * y = 0) : y = 0 := by
  have h2 := ceil_mul_eq_zero hb h
  rwa [hcb, one_mul] at h2

/-- …and on the right. -/
private theorem eq_zero_of_mul_faithful [VonNeumannAlgebra A] {b y : A} (hb : 0 ≤ b)
    (hcb : ceil b = 1) (h : y * b = 0) : y = 0 := by
  have hs : b * star y = 0 := by
    have h2 := congrArg star h
    rwa [star_mul, star_zero, (IsSelfAdjoint.of_nonneg hb).star_eq] at h2
  have h3 := eq_zero_of_faithful_mul hb hcb hs
  have h4 := congrArg star h3
  rwa [star_star, star_zero] at h4

/-- A central `z` whose product with a faithful positive `b` is positive is
itself positive: `z` is self-adjoint because `zb = (zb)* = z*b`, and its
negative part `u` satisfies `u(zb) = −u²b`, which is positive on the left and
negative on the right, so `u²b = 0` and `u = 0`. -/
private theorem nonneg_of_central_mul [VonNeumannAlgebra A] {b z : A} (hb : 0 ≤ b)
    (hcb : ceil b = 1) (hz : z ∈ centre A) (hzb : 0 ≤ z * b) : 0 ≤ z := by
  have hbz : b * z = z * b := hz b (Set.mem_univ b)
  -- `z` is self-adjoint: `z b = (z b)* = b z* = z* b`
  have hsz : ∀ a : A, a * star z = star z * a := by
    intro a
    have h := hz (star a) (Set.mem_univ _)
    have h2 := congrArg star h
    simp only [star_mul, star_star] at h2
    exact h2.symm
  have hzsa : IsSelfAdjoint z := by
    have h1 : star z * b = z * b := by
      have h2 := (IsSelfAdjoint.of_nonneg hzb).star_eq
      rw [star_mul, (IsSelfAdjoint.of_nonneg hb).star_eq] at h2
      rw [← hsz b]
      exact h2
    have hkey : (z - star z) * b = 0 := by rw [sub_mul, h1, sub_self]
    exact (sub_eq_zero.mp (eq_zero_of_mul_faithful hb hcb hkey)).symm
  -- the negative part `u` of `z` commutes with `b`
  have hzzpos : (0 : A) ≤ z * z := by
    have h := star_mul_self_nonneg z
    rwa [hzsa.star_eq] at h
  have habs : CFC.abs z = CFC.sqrt (z * z) := Theses.A.CStar.abs_eq_sqrt_mul_self hzsa
  have hzzb : b * (z * z) = z * z * b := by
    calc b * (z * z) = b * z * z := by rw [mul_assoc]
      _ = z * b * z := by rw [hbz]
      _ = z * (b * z) := by rw [mul_assoc]
      _ = z * (z * b) := by rw [hbz]
      _ = z * z * b := by rw [mul_assoc]
  have habsb : b * CFC.abs z = CFC.abs z * b := by
    rw [habs]
    exact (Theses.A.CStar.sqrt_commute _ hzzpos b hzzb).1
  have hu_eq : z⁻ = (2 : ℂ)⁻¹ • (CFC.abs z - z) := by
    rw [CFC.abs_sub_self z hzsa, two_nsmul, ← two_smul ℂ, smul_smul]
    norm_num
  have hu0 : (0 : A) ≤ z⁻ := CFC.negPart_nonneg z
  have hub : b * z⁻ = z⁻ * b := by
    rw [hu_eq, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, habsb, hbz]
  have huz : z * z⁻ = z⁻ * z := by
    have habsz : z * CFC.abs z = CFC.abs z * z := by
      rw [habs]
      exact (Theses.A.CStar.sqrt_commute _ hzzpos z (by
        calc z * (z * z) = z * z * z := by rw [mul_assoc])).1
    rw [hu_eq, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, habsz]
  -- `u·(z b) = −u²·b`, positive and negative at once
  have hz : z⁻ * z = -(z⁻ * z⁻) := by
    have h := CFC.posPart_sub_negPart z hzsa
    calc z⁻ * z = z⁻ * (z⁺ - z⁻) := by rw [h]
      _ = -(z⁻ * z⁻) := by rw [mul_sub, CFC.negPart_mul_posPart, zero_sub]
  have hup : z⁻ * (z * b) = -(z⁻ * z⁻ * b) := by
    calc z⁻ * (z * b) = z⁻ * z * b := by rw [mul_assoc]
      _ = -(z⁻ * z⁻ * b) := by rw [hz, neg_mul]
  have hcomm1 : z⁻ * (z * b) = (z * b) * z⁻ := by
    calc z⁻ * (z * b) = (z⁻ * z) * b := by rw [mul_assoc]
      _ = (z * z⁻) * b := by rw [huz]
      _ = z * (z⁻ * b) := by rw [mul_assoc]
      _ = z * (b * z⁻) := by rw [hub]
      _ = (z * b) * z⁻ := by rw [mul_assoc]
  have hpos1 : (0 : A) ≤ z⁻ * (z * b) :=
    Theses.A.CStar.sqrt_1 _ _ hu0 hzb hcomm1
  have hcomm2 : z⁻ * z⁻ * b = b * (z⁻ * z⁻) := by
    calc z⁻ * z⁻ * b = z⁻ * (z⁻ * b) := by rw [mul_assoc]
      _ = z⁻ * (b * z⁻) := by rw [hub]
      _ = z⁻ * b * z⁻ := by rw [mul_assoc]
      _ = b * z⁻ * z⁻ := by rw [hub]
      _ = b * (z⁻ * z⁻) := by rw [mul_assoc]
  have hpos2 : (0 : A) ≤ z⁻ * z⁻ * b :=
    Theses.A.CStar.sqrt_1 _ _ (Theses.A.CStar.sqrt_1 _ _ hu0 hu0 rfl) hb hcomm2
  have hzero : z⁻ * z⁻ * b = 0 :=
    le_antisymm (by rw [← neg_nonneg, ← hup]; exact hpos1) hpos2
  have husq : z⁻ * z⁻ = 0 := eq_zero_of_mul_faithful hb hcb hzero
  have hu : z⁻ = 0 := by
    rw [← CStarRing.star_mul_self_eq_zero_iff (z⁻), (IsSelfAdjoint.of_nonneg hu0).star_eq]
    exact husq
  have h := CFC.posPart_sub_negPart z hzsa
  rw [hu, sub_zero] at h
  rw [← h]
  exact CFC.posPart_nonneg _

/-- A pseudoinvertible positive element with full carrier is invertible,
`p^∼¹` being a two-sided inverse. -/
private theorem pinv_two_sided [VonNeumannAlgebra A] {x : A} (hx : 0 ≤ x)
    (hxi : Pseudoinvertible A x) (hcx : ceil x = 1) :
    pinv x * x = 1 ∧ x * pinv x = 1 := by
  obtain ⟨h1, -, -, h4⟩ := pinv_spec hxi
  refine ⟨?_, ?_⟩
  · rwa [suppProj_of_nonneg hx, hcx] at h1
  · rwa [rangeProj_eq_suppProj_of_isSelfAdjoint (IsSelfAdjoint.of_nonneg hx),
      suppProj_of_nonneg hx, hcx] at h4

/-- The inverse of a central element is central. -/
private theorem centre_inv [VonNeumannAlgebra A] {x y : A} (hxy : x * y = 1) (hyx : y * x = 1)
    (hxc : x ∈ centre A) : y ∈ centre A := by
  intro a _
  calc a * y = y * x * (a * y) := by rw [hyx, one_mul]
    _ = y * (x * a) * y := by noncomm_ring
    _ = y * (a * x) * y := by rw [hxc a (Set.mem_univ a)]
    _ = y * a * (x * y) := by noncomm_ring
    _ = y * a := by rw [hxy, mul_one]

/-- `⌈p ∧ q⌉ = 1` for commuting faithful positives: with `r := 1 − ⌈p ∧ q⌉`,
the identity `(p∧q)(p+q) = pq + (p∧q)²` gives `(pq)r = 0`, and faithfulness
of `p` and `q` cancels twice. -/
private theorem ceil_meet_eq_one [VonNeumannAlgebra A] {p q : A} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hcp : ceil p = 1) (hcq : ceil q = 1) (hcomm : p * q = q * p) :
    ceil (Theses.A.CStar.meet p q) = 1 := by
  set m := Theses.A.CStar.meet p q with hmdef
  have hm0 : 0 ≤ m := Theses.A.CStar.meet_nonneg hp hq hcomm
  have hpm : p * m = m * p := Theses.A.CStar.commute_meet hp hq rfl hcomm
  have hqm : q * m = m * q := Theses.A.CStar.commute_meet hp hq hcomm.symm rfl
  have hr : m * (1 - ceil m) = 0 := by
    rw [mul_sub, mul_one, (ceil_spec hm0).2.1, sub_self]
  have hcmp : p * ceil m = ceil m * p := ceil_basic_2 m p hm0 hpm
  have hcmq : q * ceil m = ceil m * q := ceil_basic_2 m q hm0 hqm
  have hcomm_r : (p + q) * (1 - ceil m) = (1 - ceil m) * (p + q) := by
    rw [add_mul, mul_add, mul_sub, sub_mul, mul_sub, sub_mul, mul_one, one_mul,
      mul_one, one_mul, hcmp, hcmq]
  have hid := Theses.A.CStar.meet_mul_add hp hq hcomm
  have hpq : p * q = m * (p + q) - m * m := by rw [hid]; abel
  have hkey : p * (q * (1 - ceil m)) = 0 := by
    calc p * (q * (1 - ceil m)) = (p * q) * (1 - ceil m) := by rw [mul_assoc]
      _ = (m * (p + q)) * (1 - ceil m) - (m * m) * (1 - ceil m) := by
          rw [hpq, sub_mul]
      _ = m * ((p + q) * (1 - ceil m)) - m * (m * (1 - ceil m)) := by
          rw [mul_assoc, mul_assoc]
      _ = m * ((1 - ceil m) * (p + q)) - m * 0 := by rw [hcomm_r, hr]
      _ = (m * (1 - ceil m)) * (p + q) - 0 := by rw [mul_assoc, mul_zero]
      _ = 0 := by rw [hr, zero_mul, sub_zero]
  have hqr : q * (1 - ceil m) = 0 := eq_zero_of_faithful_mul hp hcp hkey
  have hr0 : (1 : A) - ceil m = 0 := eq_zero_of_faithful_mul hq hcq hqr
  exact (sub_eq_zero.mp hr0).symm

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 2a, **as repaired by the author on 2026-08-19** (erratum
`parsec-1040.30`): assuming `⌈p⌉ = ⌈q⌉ = 1` and `p² ≤ B·q²`, `p` and `q` are
centrally similar iff `p/q` is central; `p` is centrally similar to `1` iff
`p` is central; and `p` is centrally similar to `p²` iff `p` is central.

Two changes from the printed form.  The faithfulness is new — all three are
false without it, see `centrally_similar_basic_2a_counterexample` just above,
which refutes the printed form at `p = 0`, `q = 1` in `ℂ`.  And the bound is
now on the *squares*: the printed `p ≤ Bq` gives only `√p ∈ 𝒜√q`, whereas
`p/q` is the junk value `0` unless `p ∈ 𝒜q`, which by Douglas' lemma
(**81V**.1) is exactly `p² ≤ B·q²`.  The gap is not vacuous even with both
`p` and `q` faithful: in `B(ℓ²)` with `q = ∑ₙ n⁻¹|n⟩⟨n|` and `xₙ = n^{-3/4}`,
`p := q + |x⟩⟨x|` satisfies `p ≤ (1+B)q` while `ran p ⊄ ran q`.

The proof of the first claim: `⇒` cancels `c` in `(c·(p/q) − d)·q = 0` and
then in `c·(a(p/q) − (p/q)a) = ad − da = 0`; `⇐` takes `c = 1`, `d = p/q`,
whose positivity comes from its negative part `u` satisfying
`u·p = −u²·q` — the left side positive and the right side negative, so
`u²q = 0` and `u = 0` — and whose carrier is `1` because `p⌈p/q⌉ = p`. -/
theorem centrally_similar_basic_2a [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcp : ceil p = 1) (hcq : ceil q = 1)
    (bound : ℝ) (hB : 0 ≤ bound) (hb : p ^ 2 ≤ (bound : ℂ) • q ^ 2) :
    (CentrallySimilar p q ↔ div p q ∈ centre A) ∧
      (CentrallySimilar p 1 ↔ p ∈ centre A) ∧
      (CentrallySimilar p (p ^ 2) ↔ p ∈ centre A) :=
  by
    have hpsa : IsSelfAdjoint p := IsSelfAdjoint.of_nonneg hp
    have hqsa : IsSelfAdjoint q := IsSelfAdjoint.of_nonneg hq
    -- cancellation against a faithful element, on either side
    have hcancelL : ∀ {x y : A}, 0 ≤ x → ceil x = 1 → x * y = 0 → y = 0 := by
      intro x y hx hcx h
      have h2 := ceil_mul_eq_zero hx h
      rwa [hcx, one_mul] at h2
    have hcancelR : ∀ {x y : A}, 0 ≤ x → ceil x = 1 → y * x = 0 → y = 0 := by
      intro x y hx hcx h
      have hs : x * star y = 0 := by
        have h2 := congrArg star h
        rwa [star_mul, star_zero, (IsSelfAdjoint.of_nonneg hx).star_eq] at h2
      have h3 := hcancelL hx hcx hs
      have h4 := congrArg star h3
      rwa [star_star, star_zero] at h4
    -- commuting positives have a positive product
    have hmul_nonneg : ∀ {x y : A}, 0 ≤ x → 0 ≤ y → x * y = y * x → 0 ≤ x * y := by
      intro x y hx hy hxy
      have hsq : CFC.sqrt x * y = y * CFC.sqrt x :=
        ((Theses.A.CStar.sqrt_commute x hx y hxy.symm).1).symm
      have hsa : star (CFC.sqrt x) = CFC.sqrt x :=
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq
      have hconj := star_left_conjugate_nonneg hy (CFC.sqrt x)
      rw [hsa] at hconj
      have he : CFC.sqrt x * y * CFC.sqrt x = x * y := by
        rw [mul_assoc, ← hsq, ← mul_assoc, CFC.sqrt_mul_sqrt_self x hx]
      rwa [he] at hconj
    have hpsq : (0 : A) ≤ p ^ 2 := by rw [sq]; exact hmul_nonneg hp hp rfl
    -- claim 2
    have claim2 : CentrallySimilar p 1 ↔ p ∈ centre A := by
      constructor
      · rintro ⟨c, d, hc, hd, hc0, hd0, hcd, hpc, -⟩
        rw [mul_one] at hcd
        have hcc : ceil c = 1 :=
          le_antisymm (ceil_spec hc0).1.le_one (by rw [← hcp]; exact hpc)
        intro a _
        have key : c * (a * p - p * a) = 0 := by
          have h1 : c * (a * p) = a * d := by
            rw [← mul_assoc, ← hc a (Set.mem_univ a), mul_assoc, hcd]
          have h2 : c * (p * a) = d * a := by rw [← mul_assoc, hcd]
          rw [mul_sub, h1, h2, hd a (Set.mem_univ a), sub_self]
        exact sub_eq_zero.mp (hcancelL hc0 hcc key)
      · intro hpc
        exact ⟨1, p, fun a _ => by rw [one_mul, mul_one], hpc, zero_le_one, hp,
          by rw [one_mul, mul_one],
          by rw [ceil_one]; exact (ceil_spec hp).1.le_one,
          le_of_eq (by rw [ceil_one, hcp])⟩
    -- claim 3
    have claim3 : CentrallySimilar p (p ^ 2) ↔ p ∈ centre A := by
      constructor
      · rintro ⟨c, d, hc, hd, hc0, hd0, hcd, hpc, hp2d⟩
        have hcc : ceil c = 1 :=
          le_antisymm (ceil_spec hc0).1.le_one (by rw [← hcp]; exact hpc)
        have hdd : ceil d = 1 := by
          refine le_antisymm (ceil_spec hd0).1.le_one ?_
          rw [← hcp, ← ceil_basic_5 p hp]
          exact hp2d
        have key : (c - d * p) * p = 0 := by
          rw [sub_mul, hcd, mul_assoc, ← sq, sub_self]
        have hcdp : c = d * p := sub_eq_zero.mp (hcancelR hp hcp key)
        intro a _
        have key2 : d * (a * p - p * a) = 0 := by
          have h1 : d * (a * p) = a * c := by
            rw [← mul_assoc, ← hd a (Set.mem_univ a), mul_assoc, ← hcdp]
          have h2 : d * (p * a) = c * a := by rw [← mul_assoc, ← hcdp]
          rw [mul_sub, h1, h2, hc a (Set.mem_univ a), sub_self]
        exact sub_eq_zero.mp (hcancelL hd0 hdd key2)
      · intro hpc
        exact ⟨p, 1, hpc, fun a _ => by rw [one_mul, mul_one], hp, zero_le_one,
          by rw [one_mul, sq], le_rfl,
          by rw [ceil_one]; exact (ceil_spec hpsq).1.le_one⟩
    -- claim 1; the corrected hypothesis is exactly Douglas' condition
    have hex : ∃ c : A, p = c * q := by
      have hsq : (0 : ℝ) ≤ Real.sqrt bound := Real.sqrt_nonneg _
      have hsq2 : ((Real.sqrt bound : ℂ) ^ 2) = (bound : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt hB]
      have hkey : star p * p ≤ ((Real.sqrt bound : ℂ) ^ 2) • (star q * q) := by
        rw [hpsa.star_eq, hqsa.star_eq, ← sq, ← sq, hsq2]
        exact hb
      obtain ⟨c, -, hc⟩ := ((douglas_1 p q (Real.sqrt bound) hsq).1).mpr hkey
      exact ⟨c, hc⟩
    set z := div p q with hzdef
    have hzq : z * q = p := (div_spec p q hex).1.symm
    have claim1 : CentrallySimilar p q ↔ z ∈ centre A := by
      constructor
      · rintro ⟨c, d, hc, hd, hc0, hd0, hcd, hpc, hqd⟩
        have hcc : ceil c = 1 :=
          le_antisymm (ceil_spec hc0).1.le_one (by rw [← hcp]; exact hpc)
        have hczd : c * z = d := by
          refine sub_eq_zero.mp (hcancelR hq hcq ?_)
          rw [sub_mul, mul_assoc, hzq, hcd, sub_self]
        intro a _
        have key : c * (a * z - z * a) = 0 := by
          have h1 : c * (a * z) = a * d := by
            rw [← mul_assoc, ← hc a (Set.mem_univ a), mul_assoc, hczd]
          have h2 : c * (z * a) = d * a := by rw [← mul_assoc, hczd]
          rw [mul_sub, h1, h2, hd a (Set.mem_univ a), sub_self]
        exact sub_eq_zero.mp (hcancelL hc0 hcc key)
      · intro hzc
        have hqz : q * z = z * q := hzc q (Set.mem_univ q)
        -- `z` is self-adjoint, because `z q = p = p* = q z* = z* q`
        have hsz : ∀ a : A, a * star z = star z * a := by
          intro a
          have h := hzc (star a) (Set.mem_univ _)
          have h2 := congrArg star h
          simp only [star_mul, star_star] at h2
          exact h2.symm
        have hzsa : IsSelfAdjoint z := by
          have h1 : star z * q = p := by
            have h2 := congrArg star hzq
            rw [star_mul, hqsa.star_eq, hpsa.star_eq] at h2
            rw [← hsz q]
            exact h2
          have hkey : (z - star z) * q = 0 := by rw [sub_mul, hzq, h1, sub_self]
          exact (sub_eq_zero.mp (hcancelR hq hcq hkey)).symm
        have hzzpos : (0 : A) ≤ z * z := by
          have h := star_mul_self_nonneg z
          rwa [hzsa.star_eq] at h
        have habs : CFC.abs z = CFC.sqrt (z * z) := by
          show CFC.sqrt (star z * z) = _
          rw [hzsa.star_eq]
        have hzzq : q * (z * z) = z * z * q := by
          calc q * (z * z) = q * z * z := by rw [mul_assoc]
            _ = z * q * z := by rw [hqz]
            _ = z * (q * z) := by rw [mul_assoc]
            _ = z * (z * q) := by rw [hqz]
            _ = z * z * q := by rw [mul_assoc]
        have habsq : q * CFC.abs z = CFC.abs z * q := by
          rw [habs]
          exact (Theses.A.CStar.sqrt_commute _ hzzpos q hzzq).1
        have habsz : z * CFC.abs z = CFC.abs z * z := by
          rw [habs]
          exact (Theses.A.CStar.sqrt_commute _ hzzpos z (by
            calc z * (z * z) = z * z * z := by rw [mul_assoc])).1
        have hu_eq : z⁻ = (2 : ℂ)⁻¹ • (CFC.abs z - z) := by
          rw [CFC.abs_sub_self z hzsa, two_nsmul, ← two_smul ℂ, smul_smul]
          norm_num
        have hu0 : (0 : A) ≤ z⁻ := CFC.negPart_nonneg z
        have huq : q * z⁻ = z⁻ * q := by
          rw [hu_eq, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, habsq, hqz]
        have huz : z * z⁻ = z⁻ * z := by
          rw [hu_eq, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, habsz]
        have hz : z⁻ * z = -(z⁻ * z⁻) := by
          have h := CFC.posPart_sub_negPart z hzsa
          calc z⁻ * z = z⁻ * (z⁺ - z⁻) := by rw [h]
            _ = -(z⁻ * z⁻) := by rw [mul_sub, CFC.negPart_mul_posPart, zero_sub]
        have hup : z⁻ * p = -(z⁻ * z⁻ * q) := by
          calc z⁻ * p = z⁻ * (z * q) := by rw [hzq]
            _ = z⁻ * z * q := by rw [mul_assoc]
            _ = -(z⁻ * z⁻ * q) := by rw [hz, neg_mul]
        have hupq : p * z⁻ = z⁻ * p := by
          calc p * z⁻ = z * q * z⁻ := by rw [hzq]
            _ = z * (q * z⁻) := by rw [mul_assoc]
            _ = z * (z⁻ * q) := by rw [huq]
            _ = z * z⁻ * q := by rw [mul_assoc]
            _ = z⁻ * z * q := by rw [huz]
            _ = z⁻ * (z * q) := by rw [mul_assoc]
            _ = z⁻ * p := by rw [hzq]
        have hpos1 : (0 : A) ≤ z⁻ * p := hmul_nonneg hu0 hp hupq.symm
        have huuq : z⁻ * z⁻ * q = q * (z⁻ * z⁻) := by
          calc z⁻ * z⁻ * q = z⁻ * (z⁻ * q) := by rw [mul_assoc]
            _ = z⁻ * (q * z⁻) := by rw [huq]
            _ = z⁻ * q * z⁻ := by rw [mul_assoc]
            _ = q * z⁻ * z⁻ := by rw [huq]
            _ = q * (z⁻ * z⁻) := by rw [mul_assoc]
        have hpos2 : (0 : A) ≤ z⁻ * z⁻ * q :=
          hmul_nonneg (hmul_nonneg hu0 hu0 rfl) hq huuq
        have hzero : z⁻ * z⁻ * q = 0 :=
          le_antisymm (by rw [← neg_nonneg, ← hup]; exact hpos1) hpos2
        have husq : z⁻ * z⁻ = 0 := hcancelR hq hcq hzero
        have hu : z⁻ = 0 := by
          rw [← CStarRing.star_mul_self_eq_zero_iff (z⁻),
            (IsSelfAdjoint.of_nonneg hu0).star_eq]
          exact husq
        have hz0 : (0 : A) ≤ z := by
          have h := CFC.posPart_sub_negPart z hzsa
          rw [hu, sub_zero] at h
          rw [← h]
          exact CFC.posPart_nonneg _
        have hcz : ceil z = 1 := by
          refine le_antisymm (ceil_spec hz0).1.le_one ?_
          rw [← hcp]
          refine (ceil_le_iff hp (ceil_spec hz0).1).mpr ?_
          have hzc' : z * ceil z = z := (ceil_spec hz0).2.1
          have hqcz : q * ceil z = ceil z * q := ceil_basic_2 z q hz0 hqz
          calc p * ceil z = z * q * ceil z := by rw [hzq]
            _ = z * (q * ceil z) := by rw [mul_assoc]
            _ = z * (ceil z * q) := by rw [hqcz]
            _ = z * ceil z * q := by rw [mul_assoc]
            _ = z * q := by rw [hzc']
            _ = p := hzq
        exact ⟨1, z, fun a _ => by rw [one_mul, mul_one], hzc, zero_le_one, hz0,
          by rw [one_mul, hzq], by rw [ceil_one]; exact (ceil_spec hp).1.le_one,
          le_of_eq (by rw [hcq, hcz])⟩
    exact ⟨claim1, claim2, claim3⟩

/-- **104III**.3/.4/.5, obstruction: the projection `(1,0)` of
`ℓ^∞({0,1})` is not centrally similar to `1` (it is a central projection
`≠ 1`, so `centrally_similar_one_of_isStarProjection` applies).  This is
the witness for the three counterexamples below. -/
private theorem pbFourWitness_not_centrallySimilar_one :
    ¬ CentrallySimilar (pbFourWitness : lp (fun _ : Fin 2 => ℂ) ⊤) 1 := fun h =>
  pbFourWitness_ne_one
    (centrally_similar_one_of_isStarProjection _ pbFourWitness_isStarProjection h)

/-! ### A *factor* witness for 104III: `B(ℂ²)`

The `ℓ^∞({0,1})` witness above refutes 104III.2a/.3/.4/.5 as printed, and the
repair `⌈p⌉ = ⌈q⌉` excludes it — as does the *weaker* proposed repair
`⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` (equal **central** carriers, `cceil`), because in a
commutative von Neumann algebra the central carrier *is* the carrier.  The
witnesses in this section live in the factor `B(ℂ²)` instead, where every
non-zero element has central carrier `1` (`bh_cceil_eq_one`, from **67II**.3
`central_examples_3`), so `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` holds for free; they show that
adding it repairs neither part 4 nor part 5. -/

/-- The projection `diag(1,0)` of `B(ℂ²)`. -/
private def bhTwoProj : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)

/-- The swap unitary of `B(ℂ²)`; it does not commute with `bhTwoProj`. -/
private def bhTwoSwap : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)

private theorem bhTwoProj_isStarProjection : IsStarProjection bhTwoProj := by
  constructor
  · show bhTwoProj * bhTwoProj = bhTwoProj
    rw [bhTwoProj, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · show star bhTwoProj = bhTwoProj
    rw [bhTwoProj, ← map_star]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem bhTwoProj_ne_one : bhTwoProj ≠ 1 := by
  intro h
  rw [bhTwoProj, ← map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))] at h
  have hM := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective h
  have := congrFun (congrFun hM 1) 1
  simp at this

private theorem bhTwoProj_ne_zero : bhTwoProj ≠ 0 := by
  intro h
  rw [bhTwoProj, ← map_zero (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))] at h
  have hM := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective h
  have := congrFun (congrFun hM 0) 0
  simp at this

private theorem bhTwoProj_not_commute_swap : bhTwoSwap * bhTwoProj ≠ bhTwoProj * bhTwoSwap := by
  intro h
  have hM : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, 0]
      = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0] := by
    apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).injective
    rw [map_mul, map_mul]
    exact h
  have := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at this

/-- `B(H)` is a **factor** (**67II**.3/**67III**): every non-zero element has
central carrier `⌈⌈T⌉⌉ = 1`.  Indeed `⌈⌈T⌉⌉` is central, hence a scalar `z·1`
by `central_examples_3`, and `⌈⌈T⌉⌉T = T` forces `z = 1`. -/
theorem bh_cceil_eq_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (T : H →L[ℂ] H) (hT : T ≠ 0) :
    cceil T = 1 := by
  obtain ⟨⟨-, hzc, hzT⟩, -⟩ := cceil_isLeast T
  obtain ⟨z, hz⟩ := (central_examples_3 (cceil T)).mp hzc
  rw [hz, smul_mul_assoc, one_mul] at hzT
  have hz1 : z = 1 := by
    by_contra hne
    refine hT ?_
    have hzero : (z - 1) • T = 0 := by rw [sub_smul, one_smul, hzT, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  rw [hz, hz1, one_smul]

private theorem bhTwoProj_cceil : cceil bhTwoProj = 1 :=
  bh_cceil_eq_one bhTwoProj bhTwoProj_ne_zero

private theorem bhTwoOne_cceil :
    cceil (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) = 1 :=
  bh_cceil_eq_one 1 one_ne_zero

private theorem bhTwoProjCompl_ne_zero :
    (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) - bhTwoProj ≠ 0 :=
  fun h => bhTwoProj_ne_one (sub_eq_zero.mp h).symm

private theorem bhTwoProjCompl_cceil :
    cceil ((1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) - bhTwoProj) = 1 :=
  bh_cceil_eq_one _ bhTwoProjCompl_ne_zero

private theorem bhTwoProj_not_centrallySimilar_one :
    ¬ CentrallySimilar bhTwoProj
      (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := fun h =>
  bhTwoProj_ne_one
    (centrally_similar_one_of_isStarProjection _ bhTwoProj_isStarProjection h)

open scoped ENNReal in
/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 3 is **FALSE as printed**; this is the counterexample.  Take
`𝒜 = ℓ^∞({0,1})`, `p = (1,0)`, `q = 1`.  They commute, `m := p∧q = p`
(as `p ≤ q`), and `m/p = p`, `m/q = p` are central (the algebra is
commutative), yet `p` and `q` are not centrally similar — by part 2 they
would have to satisfy `⌈p⌉ = ⌈q⌉`, i.e. `(1,0) = 1`.
The missing hypothesis is exactly that: `⌈p⌉ = ⌈q⌉` (the same omission as
in part 2a, and as in **79VI**.4).  It is *necessary*, by part 2, and
with it the argument runs: `m = (m/p)·p = (m/q)·q` exhibits the central
similarity as soon as `⌈p⌉ ≤ ⌈m/p⌉` and `⌈q⌉ ≤ ⌈m/q⌉`, which follows
from `⌈m⌉ = ⌈p⌉ = ⌈q⌉` — and that in turn is where `m = p∧q` is used. -/
theorem centrally_similar_basic_3_counterexample :
    ∃ p q m : lp (fun _ : Fin 2 => ℂ) ∞,
      0 ≤ p ∧ 0 ≤ q ∧ p * q = q * p ∧ IsGLB {p, q} m ∧
        div m p ∈ centre _ ∧ div m q ∈ centre _ ∧ ¬ CentrallySimilar p q := by
  refine ⟨pbFourWitness, 1, pbFourWitness, pbFourWitness_isStarProjection.nonneg,
    zero_le_one, by rw [mul_one, one_mul], ⟨?_, ?_⟩, ?_, ?_,
    pbFourWitness_not_centrallySimilar_one⟩
  · rintro x (rfl | rfl)
    · exact le_rfl
    · exact pbFourWitness_isStarProjection.le_one
  · intro x hx
    exact hx (by left; rfl)
  · have hd : div (pbFourWitness : lp (fun _ : Fin 2 => ℂ) ∞) pbFourWitness
        = pbFourWitness := by
      refine div_eq (pbFourWitness_isStarProjection.isIdempotentElem.eq).symm ?_
      rw [rangeProj_of_isStarProjection pbFourWitness_isStarProjection,
        pbFourWitness_isStarProjection.isIdempotentElem.eq]
    rw [hd]
    exact fun a _ => mul_comm a _
  · have hd : div (pbFourWitness : lp (fun _ : Fin 2 => ℂ) ∞) 1 = pbFourWitness := by
      refine div_eq (by rw [mul_one]) ?_
      rw [rangeProj_of_isStarProjection (IsStarProjection.one _), mul_one]
    rw [hd]
    exact fun a _ => mul_comm a _

/-- **104III**.3: the hypothesis `⌈p⌉ = ⌈q⌉ = 1` of the **repaired** point 3
cannot be weakened to equal *central* carriers.

Our transcription reads `p ∧ q` as `Theses.A.CStar.meet` — the meet of a
commuting pair inside the commutative C*-subalgebra it generates — which is
what the repaired proc.tex 104III means, its preamble citing
`commutative-cstar-basic`(5) for when `p ∧ q` is defined at all.  Under that
reading part 3 is **false with `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` in place of
`⌈p⌉ = ⌈q⌉ = 1`**: in the factor `B(ℂ²)` take `p = diag(1,0)` and
`q = 1 − p`.  Then `m := p ∧ q = pq = 0` is a lower bound of both,
`m/p = m/q = 0` are central and `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉ = 1`, yet `p ≁ q`, since
part 2 would force `⌈p⌉ = ⌈q⌉`.

(This comment used to describe a superseded state of the tree, in which our
`p ∧ q` was the infimum of `{p, q}` in the order of `𝒜` (`IsGLB`).  Under
*that* reading the witness below is not one — `p` and `1 − p` have no
infimum in `B(ℂ²)` — and the only route to part 3 ran through Kadison's
anti-lattice theorem, which this tree does not have.
`centrally_similar_basic_3` now uses `meet`, so that route is abandoned and
this theorem is a counterexample to the statement actually transcribed.) -/
theorem centrally_similar_basic_3_meet_cceil_counterexample :
    ∃ p q m : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      0 ≤ p ∧ 0 ≤ q ∧ p * q = q * p ∧ m = p * q ∧
        m = Theses.A.CStar.meet p q ∧ m ≤ p ∧ m ≤ q ∧
        div m p ∈ centre _ ∧ div m q ∈ centre _ ∧
        cceil p = cceil q ∧ ¬ CentrallySimilar p q := by
  have hP := bhTwoProj_isStarProjection
  have hQ := hP.one_sub
  have hpq : bhTwoProj * (1 - bhTwoProj) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  have hqp : (1 - bhTwoProj) * bhTwoProj = 0 := by
    rw [sub_mul, one_mul, hP.isIdempotentElem.eq, sub_self]
  have hdiv : ∀ b : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      div 0 b = 0 := fun b => div_eq (by rw [zero_mul]) (by rw [zero_mul])
  -- `p ∧ (1−p) = 0`: `2p − 1` is a symmetry, so `|p − (1−p)| = 1`
  have hsa : IsSelfAdjoint (bhTwoProj - (1 - bhTwoProj)) :=
    hP.isSelfAdjoint.sub hQ.isSelfAdjoint
  have hsq : (bhTwoProj - (1 - bhTwoProj)) * (bhTwoProj - (1 - bhTwoProj)) = 1 := by
    have hpp : bhTwoProj * bhTwoProj = bhTwoProj := hP.isIdempotentElem.eq
    have hexp : (bhTwoProj - (1 - bhTwoProj)) * (bhTwoProj - (1 - bhTwoProj))
        = 4 * (bhTwoProj * bhTwoProj) - 4 * bhTwoProj + 1 := by noncomm_ring
    rw [hexp, hpp]
    noncomm_ring
  have habs : CFC.abs (bhTwoProj - (1 - bhTwoProj)) = 1 := by
    rw [Theses.A.CStar.abs_eq_sqrt_mul_self hsa, hsq, CFC.sqrt_one]
  have hmeet : Theses.A.CStar.meet bhTwoProj (1 - bhTwoProj) = 0 := by
    rw [Theses.A.CStar.meet, habs,
      show bhTwoProj + (1 - bhTwoProj) - 1 = 0 by abel, smul_zero]
  refine ⟨bhTwoProj, 1 - bhTwoProj, 0, hP.nonneg, hQ.nonneg, by rw [hpq, hqp], hpq.symm,
    hmeet.symm, hP.nonneg, hQ.nonneg, by rw [hdiv]; exact fun a _ => by rw [mul_zero, zero_mul],
    by rw [hdiv]; exact fun a _ => by rw [mul_zero, zero_mul],
    by rw [bhTwoProj_cceil, bhTwoProjCompl_cceil], ?_⟩
  intro h
  have h2 := centrally_similar_basic_2 bhTwoProj (1 - bhTwoProj) hP.nonneg hQ.nonneg h
  rw [ceil_of_isStarProjection hP, ceil_of_isStarProjection hQ] at h2
  refine bhTwoProj_ne_zero ?_
  calc bhTwoProj = bhTwoProj * bhTwoProj := hP.isIdempotentElem.eq.symm
    _ = bhTwoProj * (1 - bhTwoProj) := by rw [← h2]
    _ = 0 := hpq

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 3, **as repaired by the author on 2026-08-19** (erratum
`parsec-1040.30`): if `⌈p⌉ = ⌈q⌉ = 1`, `p` and `q` commute, and both
`(p ∧ q)/p` and `(p ∧ q)/q` are central, then `p` and `q` are centrally
similar.

Two changes from the printed form.  The faithfulness is new — without it
`centrally_similar_basic_3_counterexample` just above refutes it.  And
`p ∧ q` is now `Theses.A.CStar.meet`, the meet in the commutative
C*-subalgebra `p` and `q` generate (**26II**.5), where the earlier
transcription read it as `IsGLB {p, q} m` — the infimum in the order of `𝒜`,
which by Kadison's anti-lattice theorem usually does not exist, so that form
was near-vacuous. -/
theorem centrally_similar_basic_3 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcp : ceil p = 1) (hcq : ceil q = 1)
    (hcomm : p * q = q * p)
    (h1 : div (Theses.A.CStar.meet p q) p ∈ centre A)
    (h2 : div (Theses.A.CStar.meet p q) q ∈ centre A) :
    CentrallySimilar p q :=
  by
    set m := Theses.A.CStar.meet p q with hmdef
    have hm0 : 0 ≤ m := Theses.A.CStar.meet_nonneg hp hq hcomm
    have hsad : IsSelfAdjoint (p - q) :=
      (IsSelfAdjoint.of_nonneg hp).sub (IsSelfAdjoint.of_nonneg hq)
    have hmp : m ≤ p := Theses.A.CStar.meet_le_left p q hsad
    have hpm : p * m = m * p := Theses.A.CStar.commute_meet hp hq rfl hcomm
    have hqm : q * m = m * q := Theses.A.CStar.commute_meet hp hq hcomm.symm rfl
    have hcm : ceil m = 1 := ceil_meet_eq_one hp hq hcp hcq hcomm
    -- `m ∈ Ap` and `m ∈ Aq` by Douglas, since `m ≤ p` gives `m² ≤ p²` here
    have hsq : ∀ x : A, 0 ≤ x → m ≤ x → x * m = m * x → m * m ≤ x * x := by
      intro x hx hmx hxm
      have hd : (0 : A) ≤ x - m := sub_nonneg.mpr hmx
      have e1 : (0 : A) ≤ x * (x - m) :=
        Theses.A.CStar.sqrt_1 _ _ hx hd (by rw [mul_sub, sub_mul, hxm])
      have e2 : (0 : A) ≤ (x - m) * m :=
        Theses.A.CStar.sqrt_1 _ _ hd hm0 (by rw [sub_mul, mul_sub, hxm])
      have hid : x * x - m * m = x * (x - m) + (x - m) * m := by noncomm_ring
      rw [← sub_nonneg, hid]
      exact add_nonneg e1 e2
    have hmem : ∀ x : A, 0 ≤ x → m ≤ x → x * m = m * x → ∃ c : A, m = c * x := by
      intro x hx hmx hxm
      have hkey : star m * m ≤ ((1 : ℂ) ^ 2) • (star x * x) := by
        rw [(IsSelfAdjoint.of_nonneg hm0).star_eq, (IsSelfAdjoint.of_nonneg hx).star_eq,
          one_pow, one_smul]
        exact hsq x hx hmx hxm
      obtain ⟨c, -, hc⟩ := ((douglas_1 m x 1 zero_le_one).1).mpr hkey
      exact ⟨c, hc⟩
    have hmq : m ≤ q := Theses.A.CStar.meet_le_right p q hsad
    have hexp := hmem p hp hmp hpm
    have hexq := hmem q hq hmq hqm
    have hdp : div m p * p = m := (div_spec m p hexp).1.symm
    have hdq : div m q * q = m := (div_spec m q hexq).1.symm
    -- the two quotients are positive, and faithful because `⌈m⌉ = 1`
    have hposc : (0 : A) ≤ div m p := nonneg_of_central_mul hp hcp h1 (by rw [hdp]; exact hm0)
    have hposd : (0 : A) ≤ div m q := nonneg_of_central_mul hq hcq h2 (by rw [hdq]; exact hm0)
    have hfaith : ∀ (x c : A), 0 ≤ x → 0 ≤ c → c ∈ centre A → c * x = m → ceil c = 1 := by
      intro x c hx hc0 hc hcx
      have hcc : c * (1 - ceil c) = 0 := by
        rw [mul_sub, mul_one, (ceil_spec hc0).2.1, sub_self]
      have hcx' : x * ceil c = ceil c * x :=
        ceil_basic_2 c x hc0 (hc x (Set.mem_univ x))
      have hkey : m * (1 - ceil c) = 0 := by
        calc m * (1 - ceil c) = (c * x) * (1 - ceil c) := by rw [hcx]
          _ = c * (x * (1 - ceil c)) := by rw [mul_assoc]
          _ = c * ((1 - ceil c) * x) := by
              rw [mul_sub, sub_mul, mul_one, one_mul, hcx']
          _ = (c * (1 - ceil c)) * x := by rw [mul_assoc]
          _ = 0 := by rw [hcc, zero_mul]
      have h0 := eq_zero_of_faithful_mul hm0 hcm hkey
      exact (sub_eq_zero.mp h0).symm
    refine ⟨div m p, div m q, h1, h2, hposc, hposd, by rw [hdp, hdq], ?_, ?_⟩
    · exact le_of_eq (by rw [hcp, hfaith p (div m p) hp hposc h1 hdp])
    · exact le_of_eq (by rw [hcq, hfaith q (div m q) hq hposd h2 hdq])

open scoped ENNReal in
/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 4 is **FALSE as printed**; this is the counterexample to its first
`iff`.  Same witness as for part 3: in `ℓ^∞({0,1})` take `p = (1,0)` and
`q = 1`; both are projections, hence pseudoinvertible, `p·q^∼¹ = p` is
central, yet `p` and `q` are not centrally similar. -/
theorem centrally_similar_basic_4_counterexample :
    ∃ p q m : lp (fun _ : Fin 2 => ℂ) ∞,
      0 ≤ p ∧ 0 ≤ q ∧ Pseudoinvertible _ p ∧ Pseudoinvertible _ q ∧ IsGLB {p, q} m ∧
        p * pinv q ∈ centre _ ∧ ¬ CentrallySimilar p q := by
  refine ⟨pbFourWitness, 1, pbFourWitness, pbFourWitness_isStarProjection.nonneg,
    zero_le_one, pseudoinvertible_of_isStarProjection pbFourWitness_isStarProjection,
    pseudoinvertible_of_isStarProjection (IsStarProjection.one _), ⟨?_, ?_⟩, ?_,
    pbFourWitness_not_centrallySimilar_one⟩
  · rintro x (rfl | rfl)
    · exact le_rfl
    · exact pbFourWitness_isStarProjection.le_one
  · intro x hx
    exact hx (by left; rfl)
  · rw [pinv_of_isStarProjection (IsStarProjection.one _), mul_one]
    exact fun a _ => mul_comm a _

/-- **104III**.4, second obstruction: unlike parts 2a and 3, part 4 is
**not** repaired by adding `⌈p⌉ = ⌈q⌉`.  Its first `iff` at `p = q = e`
for a projection `e` (where `e` and `e` are trivially centrally similar,
`m = e`, and `e·e^∼¹ = e`) would make *every* projection of *every* von
Neumann algebra central — false already in `M₂(ℂ)` at `e = diag(1,0)`.
What part 4 needs is the *faithfulness* hypothesis `⌈p⌉ = ⌈q⌉ = 1` of
**104VII**, which turns pseudoinvertibility into invertibility; the
`⟹` of the first `iff` is then three lines: `cp = dq` gives
`c·(pq⁻¹) = d`, so `c·(a(pq⁻¹) − (pq⁻¹)a) = 0` for every `a`, and
`⌈c⌉ = 1` cancels `c`. -/
theorem centrally_similar_basic_4_obstruction [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e)
    (h : CentrallySimilar e e ↔ e * pinv e ∈ centre A) : e ∈ centre A := by
  have hcs : CentrallySimilar e e :=
    ⟨1, 1, fun a _ => by rw [one_mul, mul_one], fun a _ => by rw [one_mul, mul_one],
      zero_le_one, zero_le_one, rfl,
      by rw [ceil_one, ceil_of_isStarProjection he]; exact he.le_one,
      by rw [ceil_one, ceil_of_isStarProjection he]; exact he.le_one⟩
  have hc := h.mp hcs
  rwa [pinv_of_isStarProjection he, he.isIdempotentElem.eq] at hc

/-- **104III**.4, third obstruction, in concrete form: the weaker repair
`⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` (equal **central** carriers) does not work either.  In the
factor `B(ℂ²)` take `p = q = m = diag(1,0)`: `p` and `q` are trivially
centrally similar (`c = d = 1`), `m` is their infimum, both are
pseudoinvertible, `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉ = 1` since `B(ℂ²)` is a factor — and yet
`p·q^∼¹ = p` is *not* central.  This is `centrally_similar_basic_4_obstruction`
made unconditional (that one only says "if the first `iff` held at `e` then
`e` would be central"), and it settles the shape of the repair: at `p = q`
*every* hypothesis that is reflexive in the pair holds, so both `⌈p⌉ = ⌈q⌉`
and `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉` leave the first `iff` false.  Only a condition ruling out
non-faithful `p` — the `⌈p⌉ = ⌈q⌉ = 1` of **104VII**, under which
`centrally_similar_basic_4_faithful` proves the first two `iff`s — repairs
part 4. -/
theorem centrally_similar_basic_4_cceil_counterexample :
    ∃ p q m : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      0 ≤ p ∧ 0 ≤ q ∧ Pseudoinvertible _ p ∧ Pseudoinvertible _ q ∧ IsGLB {p, q} m ∧
        cceil p = cceil q ∧ CentrallySimilar p q ∧ p * pinv q ∉ centre _ := by
  have hP := bhTwoProj_isStarProjection
  refine ⟨bhTwoProj, bhTwoProj, bhTwoProj, hP.nonneg, hP.nonneg,
    pseudoinvertible_of_isStarProjection hP, pseudoinvertible_of_isStarProjection hP,
    ⟨?_, ?_⟩, rfl, ?_, ?_⟩
  · rintro x (rfl | rfl) <;> exact le_rfl
  · intro x hx
    exact hx (by left; rfl)
  · exact ⟨1, 1, fun a _ => by rw [one_mul, mul_one], fun a _ => by rw [one_mul, mul_one],
      zero_le_one, zero_le_one, rfl,
      by rw [ceil_one, ceil_of_isStarProjection hP]; exact hP.le_one,
      by rw [ceil_one, ceil_of_isStarProjection hP]; exact hP.le_one⟩
  · intro hc
    rw [pinv_of_isStarProjection hP, hP.isIdempotentElem.eq] at hc
    exact bhTwoProj_not_commute_swap (hc bhTwoSwap (Set.mem_univ _))

/-- **104III**.4, the **repaired** first two `iff`s: with the faithfulness
hypothesis `⌈p⌉ = ⌈q⌉ = 1` of **104VII** in place, `p` and `q` are
centrally similar iff `p·q^∼¹` is central, iff `q·p^∼¹` is central.  (The
third `iff`, the one involving `p ∧ q`, is not proved here.)

`⌈q⌉ = 1` makes `q^∼¹` a two-sided inverse of `q`, so: if `z := pq⁻¹` is
central then `zq = p` exhibits the central similarity — `z = √(q⁻¹) p
√(q⁻¹) ≥ 0`, and `⌈z⌉ ≥ ⌈p⌉ = 1`; conversely `cp = dq` gives `cz = d`,
hence `c(az − za) = ad − da = 0` for every `a`, and `⌈c⌉ ≥ ⌈p⌉ = 1`
cancels `c`.  The second `iff` is that `qp⁻¹` is the inverse of `pq⁻¹` and
that the inverse of a central element is central. -/
theorem centrally_similar_basic_4_faithful [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpi : Pseudoinvertible A p)
    (hqi : Pseudoinvertible A q) (hcp : ceil p = 1) (hcq : ceil q = 1) :
    (CentrallySimilar p q ↔ p * pinv q ∈ centre A) ∧
      (p * pinv q ∈ centre A ↔ q * pinv p ∈ centre A) := by
  -- `q^∼¹` is a two-sided inverse of `q` (and likewise for `p`)
  have hinvs : ∀ x : A, 0 ≤ x → Pseudoinvertible A x → ceil x = 1 →
      pinv x * x = 1 ∧ x * pinv x = 1 := by
    intro x hx hxi hcx
    obtain ⟨h1, -, -, h4⟩ := pinv_spec hxi
    refine ⟨?_, ?_⟩
    · rwa [suppProj_of_nonneg hx, hcx] at h1
    · rwa [rangeProj_eq_suppProj_of_isSelfAdjoint (IsSelfAdjoint.of_nonneg hx),
        suppProj_of_nonneg hx, hcx] at h4
  obtain ⟨hqpq, hqqp⟩ := hinvs q hq hqi hcq
  obtain ⟨hppp, hppq⟩ := hinvs p hp hpi hcp
  -- the inverse of a central element is central
  have hcentre_inv : ∀ x y : A, x * y = 1 → y * x = 1 → x ∈ centre A → y ∈ centre A := by
    intro x y hxy hyx hxc a _
    calc a * y = y * x * (a * y) := by rw [hyx, one_mul]
      _ = y * (x * a) * y := by noncomm_ring
      _ = y * (a * x) * y := by rw [hxc a (Set.mem_univ a)]
      _ = y * a * (x * y) := by noncomm_ring
      _ = y * a := by rw [hxy, mul_one]
  have hzz : (p * pinv q) * (q * pinv p) = 1 := by
    calc (p * pinv q) * (q * pinv p) = p * (pinv q * q) * pinv p := by noncomm_ring
      _ = 1 := by rw [hqpq, mul_one, hppq]
  have hzz' : (q * pinv p) * (p * pinv q) = 1 := by
    calc (q * pinv p) * (p * pinv q) = q * (pinv p * p) * pinv q := by noncomm_ring
      _ = 1 := by rw [hppp, mul_one, hqqp]
  refine ⟨⟨?_, ?_⟩, ⟨fun h => hcentre_inv _ _ hzz hzz' h,
    fun h => hcentre_inv _ _ hzz' hzz h⟩⟩
  · -- centrally similar ⟹ `pq⁻¹` central
    rintro ⟨c, d, hc, hd, hc0, hd0, hcd, hpc, -⟩
    have hcc : ceil c = 1 :=
      le_antisymm (ceil_spec hc0).1.le_one (by rw [← hcp]; exact hpc)
    have hcz : c * (p * pinv q) = d := by
      calc c * (p * pinv q) = c * p * pinv q := by noncomm_ring
        _ = d * q * pinv q := by rw [hcd]
        _ = d := by rw [mul_assoc, hqqp, mul_one]
    intro a _
    have key : c * (a * (p * pinv q) - p * pinv q * a) = 0 := by
      have h1 : c * (a * (p * pinv q)) = a * d := by
        rw [← mul_assoc, ← hc a (Set.mem_univ a), mul_assoc, hcz]
      have h2 : c * (p * pinv q * a) = d * a := by rw [← mul_assoc, hcz]
      rw [mul_sub, h1, h2, hd a (Set.mem_univ a), sub_self]
    have h0 := ceil_mul_eq_zero hc0 key
    rw [hcc, one_mul, sub_eq_zero] at h0
    exact h0
  · -- `pq⁻¹` central ⟹ centrally similar
    intro hzc
    have hzq : p * pinv q * q = p := by rw [mul_assoc, hqpq, mul_one]
    -- `z = √(q⁻¹) p √(q⁻¹)` is positive
    have hpq0 : (0 : A) ≤ pinv q := pinv_nonneg hq hqi
    have ht0 : (0 : A) ≤ CFC.sqrt (pinv q) := CFC.sqrt_nonneg _
    have htsa : star (CFC.sqrt (pinv q)) = CFC.sqrt (pinv q) :=
      (IsSelfAdjoint.of_nonneg ht0).star_eq
    have htt : CFC.sqrt (pinv q) * CFC.sqrt (pinv q) = pinv q :=
      CFC.sqrt_mul_sqrt_self _ hpq0
    have htq : q * CFC.sqrt (pinv q) = CFC.sqrt (pinv q) * q :=
      (Theses.A.CStar.sqrt_commute (pinv q) hpq0 q (by rw [hqqp, hqpq])).1
    have htqt : CFC.sqrt (pinv q) * q * CFC.sqrt (pinv q) = 1 := by
      calc CFC.sqrt (pinv q) * q * CFC.sqrt (pinv q)
          = q * CFC.sqrt (pinv q) * CFC.sqrt (pinv q) := by rw [← htq]
        _ = q * pinv q := by rw [mul_assoc, htt]
        _ = 1 := hqqp
    have hz0 : (0 : A) ≤ p * pinv q := by
      have hconj : CFC.sqrt (pinv q) * p * CFC.sqrt (pinv q) = p * pinv q := by
        calc CFC.sqrt (pinv q) * p * CFC.sqrt (pinv q)
            = CFC.sqrt (pinv q) * (p * pinv q * q) * CFC.sqrt (pinv q) := by rw [hzq]
          _ = CFC.sqrt (pinv q) * (p * pinv q) * (q * CFC.sqrt (pinv q)) := by
              noncomm_ring
          _ = (p * pinv q) * CFC.sqrt (pinv q) * (q * CFC.sqrt (pinv q)) := by
              rw [hzc _ (Set.mem_univ (CFC.sqrt (pinv q)))]
          _ = (p * pinv q) * (CFC.sqrt (pinv q) * q * CFC.sqrt (pinv q)) := by
              noncomm_ring
          _ = p * pinv q := by rw [htqt, mul_one]
      rw [← hconj]
      have h := star_left_conjugate_nonneg hp (CFC.sqrt (pinv q))
      rwa [htsa] at h
    -- `⌈z⌉ ≥ ⌈p⌉ = 1`
    have hcz1 : ceil (p * pinv q) = 1 := by
      refine le_antisymm (ceil_spec hz0).1.le_one ?_
      rw [← hcp]
      refine ((ceil_basic_1 p (ceil (p * pinv q)) hp (ceil_spec hz0).1).out 0 2).mp ?_
      have hzc' : (p * pinv q) * ceil (p * pinv q) = p * pinv q := (ceil_spec hz0).2.1
      have hzl : ceil (p * pinv q) * (p * pinv q) = p * pinv q :=
        ((ceil_basic_1 _ _ hz0 (ceil_spec hz0).1).out 1 0).mp hzc'
      calc ceil (p * pinv q) * p = ceil (p * pinv q) * (p * pinv q * q) := by rw [hzq]
        _ = (ceil (p * pinv q) * (p * pinv q)) * q := by noncomm_ring
        _ = p := by rw [hzl, hzq]
    exact ⟨1, p * pinv q, fun a _ => by rw [one_mul, mul_one],
      hzc, zero_le_one, hz0, by rw [one_mul, hzq], by rw [hcp, ceil_one],
      by rw [hcq, hcz1]⟩

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 4, **as repaired by the author on 2026-08-19** (erratum
`parsec-1040.30`): for commuting pseudoinvertible `p, q` with
`⌈p⌉ = ⌈q⌉ = 1`: centrally similar iff `p·q^∼¹` central iff `q·p^∼¹`
central iff both `(p ∧ q)·p^∼¹` and `(p ∧ q)·q^∼¹` central.

Three changes from the printed form.  The faithfulness is new —
`centrally_similar_basic_4_counterexample` refutes the printed first `iff`,
and `centrally_similar_basic_4_obstruction` shows that `⌈p⌉ = ⌈q⌉` alone
cannot repair it.  Commutation is new too: without it the third `iff` cannot
be stated at all, since `p ∧ q` is only defined for a commuting pair.  And
`p ∧ q` is `Theses.A.CStar.meet`, not the ambient `IsGLB` the earlier
transcription used.  The first two `iff`s are
`centrally_similar_basic_4_faithful` above. -/
theorem centrally_similar_basic_4 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcp : ceil p = 1) (hcq : ceil q = 1)
    (hcomm : p * q = q * p) (hpi : Pseudoinvertible A p)
    (hqi : Pseudoinvertible A q) :
    (CentrallySimilar p q ↔ p * pinv q ∈ centre A) ∧
      (p * pinv q ∈ centre A ↔ q * pinv p ∈ centre A) ∧
      (q * pinv p ∈ centre A ↔
        Theses.A.CStar.meet p q * pinv p ∈ centre A ∧
          Theses.A.CStar.meet p q * pinv q ∈ centre A) :=
  by
    obtain ⟨h1, h2⟩ := centrally_similar_basic_4_faithful p q hp hq hpi hqi hcp hcq
    refine ⟨h1, h2, ?_⟩
    obtain ⟨hPp, hpP⟩ := pinv_two_sided hp hpi hcp
    obtain ⟨hQq, hqQ⟩ := pinv_two_sided hq hqi hcq
    have hP0 : (0 : A) ≤ pinv p := pinv_nonneg hp hpi
    have hQ0 : (0 : A) ≤ pinv q := pinv_nonneg hq hqi
    set m := Theses.A.CStar.meet p q with hmdef
    have hm0 : (0 : A) ≤ m := Theses.A.CStar.meet_nonneg hp hq hcomm
    have hcm : ceil m = 1 := ceil_meet_eq_one hp hq hcp hcq hcomm
    -- `q` commutes with `p⁻¹`, and `p` with `q⁻¹`
    have hqP : q * pinv p = pinv p * q := by
      calc q * pinv p = pinv p * p * (q * pinv p) := by rw [hPp, one_mul]
        _ = pinv p * (p * q) * pinv p := by noncomm_ring
        _ = pinv p * (q * p) * pinv p := by rw [hcomm]
        _ = pinv p * q * (p * pinv p) := by noncomm_ring
        _ = pinv p * q := by rw [hpP, mul_one]
    have hpQ : p * pinv q = pinv q * p := by
      calc p * pinv q = pinv q * q * (p * pinv q) := by rw [hQq, one_mul]
        _ = pinv q * (q * p) * pinv q := by noncomm_ring
        _ = pinv q * (p * q) * pinv q := by rw [hcomm]
        _ = pinv q * p * (q * pinv q) := by noncomm_ring
        _ = pinv q * p := by rw [hqQ, mul_one]
    -- the two localisations of the meet
    have hmP : m * pinv p = Theses.A.CStar.meet 1 (q * pinv p) := by
      rw [hmdef, Theses.A.CStar.meet_mul_right hp hq hP0 (by rw [hpP, hPp]) hqP, hpP]
    have hmQ : m * pinv q = Theses.A.CStar.meet (p * pinv q) 1 := by
      rw [hmdef, Theses.A.CStar.meet_mul_right hp hq hQ0 hpQ (by rw [hqQ, hQq]), hqQ]
    constructor
    · intro hz
      have hz0 : (0 : A) ≤ q * pinv p :=
        nonneg_of_central_mul hp hcp hz (by rw [mul_assoc, hPp, mul_one]; exact hq)
      -- `p q⁻¹` is the inverse of the central `q p⁻¹`, hence central
      have hinv1 : (q * pinv p) * (p * pinv q) = 1 := by
        calc (q * pinv p) * (p * pinv q) = q * (pinv p * p) * pinv q := by noncomm_ring
          _ = 1 := by rw [hPp, mul_one, hqQ]
      have hinv2 : (p * pinv q) * (q * pinv p) = 1 := by
        calc (p * pinv q) * (q * pinv p) = p * (pinv q * q) * pinv p := by noncomm_ring
          _ = 1 := by rw [hQq, mul_one, hpP]
      have hpQc : p * pinv q ∈ centre A := centre_inv hinv1 hinv2 hz
      have hpQ0 : (0 : A) ≤ p * pinv q :=
        nonneg_of_central_mul hq hcq hpQc (by rw [mul_assoc, hQq, mul_one]; exact hp)
      refine ⟨?_, ?_⟩
      · rw [hmP]
        intro x _
        exact Theses.A.CStar.commute_meet zero_le_one hz0 (by rw [mul_one, one_mul])
          (hz x (Set.mem_univ x))
      · rw [hmQ]
        intro x _
        exact Theses.A.CStar.commute_meet hpQ0 zero_le_one (hpQc x (Set.mem_univ x))
          (by rw [mul_one, one_mul])
    · rintro ⟨hc, hd⟩
      -- `c p = m = d q` is a central similarity, and 104III.4's first two `iff`s finish
      have hcp' : (m * pinv p) * p = m := by rw [mul_assoc, hPp, mul_one]
      have hdq' : (m * pinv q) * q = m := by rw [mul_assoc, hQq, mul_one]
      have hc0 : (0 : A) ≤ m * pinv p :=
        nonneg_of_central_mul hp hcp hc (by rw [hcp']; exact hm0)
      have hd0 : (0 : A) ≤ m * pinv q :=
        nonneg_of_central_mul hq hcq hd (by rw [hdq']; exact hm0)
      have hfaith : ∀ x c : A, 0 ≤ c → c ∈ centre A → c * x = m → ceil c = 1 := by
        intro x c hc0' hcc hcx
        have hcc0 : c * (1 - ceil c) = 0 := by
          rw [mul_sub, mul_one, (ceil_spec hc0').2.1, sub_self]
        have hcx' : x * ceil c = ceil c * x :=
          ceil_basic_2 c x hc0' (hcc x (Set.mem_univ x))
        have hkey : m * (1 - ceil c) = 0 := by
          calc m * (1 - ceil c) = (c * x) * (1 - ceil c) := by rw [hcx]
            _ = c * (x * (1 - ceil c)) := by rw [mul_assoc]
            _ = c * ((1 - ceil c) * x) := by
                rw [mul_sub, sub_mul, mul_one, one_mul, hcx']
            _ = (c * (1 - ceil c)) * x := by rw [mul_assoc]
            _ = 0 := by rw [hcc0, zero_mul]
        exact (sub_eq_zero.mp (eq_zero_of_faithful_mul hm0 hcm hkey)).symm
      have hcs : CentrallySimilar p q :=
        ⟨m * pinv p, m * pinv q, hc, hd, hc0, hd0, by rw [hcp', hdq'],
          le_of_eq (by rw [hcp, hfaith p (m * pinv p) hc0 hc hcp']),
          le_of_eq (by rw [hcq, hfaith q (m * pinv q) hd0 hd hdq'])⟩
      obtain ⟨i1, i2⟩ := centrally_similar_basic_4_faithful p q hp hq hpi hqi hcp hcq
      exact i2.mp (i1.mp hcs)

open scoped ENNReal in
/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 5 is **FALSE as printed**; this is the counterexample.  Same witness
again: in `ℓ^∞({0,1})` take `p = (1,0)`, `q = 1` and the constant sequence
`eₙ = (1,0)`.  Then `⋃ₙ eₙ = (1,0) = ⌈p⌉`, every `eₙp = eₙq = (1,0)` is
pseudoinvertible, and `eₙp` and `eₙq` are centrally similar (they are
equal), yet `p` and `q` are not.  The hypothesis `⋃ₙ eₙ = ⌈p⌉` controls
only `p`'s carrier: what is missing is again `⌈p⌉ = ⌈q⌉` (equivalently
`⋃ₙ eₙ = ⌈q⌉` as well). -/
theorem centrally_similar_basic_5_counterexample :
    ∃ (p q : lp (fun _ : Fin 2 => ℂ) ∞) (e : ℕ → lp (fun _ : Fin 2 => ℂ) ∞),
      0 ≤ p ∧ 0 ≤ q ∧ p * q = q * p ∧ (∀ n, IsStarProjection (e n)) ∧ Monotone e ∧
        (∀ n, e n * p = p * e n) ∧ (∀ n, e n * q = q * e n) ∧
        projSup (Set.range e) = ceil p ∧
        (∀ n, Pseudoinvertible _ (e n * p)) ∧ (∀ n, Pseudoinvertible _ (e n * q)) ∧
        (∀ n, CentrallySimilar (e n * p) (e n * q)) ∧ ¬ CentrallySimilar p q := by
  have hw := pbFourWitness_isStarProjection
  have hww : (pbFourWitness : lp (fun _ : Fin 2 => ℂ) ∞) * pbFourWitness = pbFourWitness :=
    hw.isIdempotentElem.eq
  refine ⟨pbFourWitness, 1, fun _ => pbFourWitness, hw.nonneg, zero_le_one,
    by rw [mul_one, one_mul], fun _ => hw, fun m n _ => le_rfl, fun _ => rfl,
    fun n => by rw [mul_one, one_mul], ?_, ?_, ?_, ?_,
    pbFourWitness_not_centrallySimilar_one⟩
  · rw [ceil_of_isStarProjection hw]
    refine projSup_eq ?_ hw ?_ ?_
    · rintro p ⟨n, rfl⟩; exact hw
    · rintro p ⟨n, rfl⟩; exact le_rfl
    · intro q hq hub; exact hub pbFourWitness ⟨0, rfl⟩
  · intro n; rw [hww]; exact pseudoinvertible_of_isStarProjection hw
  · intro n; rw [mul_one]; exact pseudoinvertible_of_isStarProjection hw
  · intro n
    rw [hww, mul_one]
    exact ⟨1, 1, fun a _ => mul_comm a _, fun a _ => mul_comm a _, zero_le_one, zero_le_one,
      rfl, by rw [ceil_one]; exact (ceil_spec hw.nonneg).1.le_one,
      by rw [ceil_one]; exact (ceil_spec hw.nonneg).1.le_one⟩

/-- **104III**.5 is **not repaired by `⌈⌈p⌉⌉ = ⌈⌈q⌉⌉`** either: the printed
statement's witness transplanted from `ℓ^∞({0,1})` to the factor `B(ℂ²)`,
where equal central carriers cost nothing.  Take `p = diag(1,0)`, `q = 1` and
the constant sequence `eₙ = p`.  Then `⋃ₙ eₙ = ⌈p⌉`, each `eₙp = eₙq = p` is
pseudoinvertible, `eₙp` and `eₙq` are centrally similar (they are equal), and
`⌈⌈p⌉⌉ = ⌈⌈q⌉⌉ = 1` — yet `p` and `q` are not centrally similar, since part 2
would force `⌈p⌉ = ⌈q⌉`, i.e. `p = 1`.  Note that no centrality hypothesis
appears in part 5, so nothing here forces faithfulness the way it does inside
a factor for parts 2a and 3.  What part 5 needs is `⌈p⌉ = ⌈q⌉` itself
(equivalently: `⋃ₙ eₙ = ⌈q⌉` as well as `= ⌈p⌉`), which its only consumer
**104VII** supplies in the stronger form `⌈p⌉ = ⌈q⌉ = 1`. -/
theorem centrally_similar_basic_5_cceil_counterexample :
    ∃ (p q : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (e : ℕ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
      0 ≤ p ∧ 0 ≤ q ∧ p * q = q * p ∧ (∀ n, IsStarProjection (e n)) ∧ Monotone e ∧
        (∀ n, e n * p = p * e n) ∧ (∀ n, e n * q = q * e n) ∧
        projSup (Set.range e) = ceil p ∧
        (∀ n, Pseudoinvertible _ (e n * p)) ∧ (∀ n, Pseudoinvertible _ (e n * q)) ∧
        (∀ n, CentrallySimilar (e n * p) (e n * q)) ∧
        cceil p = cceil q ∧ ¬ CentrallySimilar p q := by
  have hw := bhTwoProj_isStarProjection
  have hww : bhTwoProj * bhTwoProj = bhTwoProj := hw.isIdempotentElem.eq
  refine ⟨bhTwoProj, 1, fun _ => bhTwoProj, hw.nonneg, zero_le_one,
    by rw [mul_one, one_mul], fun _ => hw, fun m n _ => le_rfl, fun _ => rfl,
    fun n => by rw [mul_one, one_mul], ?_, ?_, ?_, ?_, ?_,
    bhTwoProj_not_centrallySimilar_one⟩
  · rw [ceil_of_isStarProjection hw]
    refine projSup_eq ?_ hw ?_ ?_
    · rintro p ⟨n, rfl⟩; exact hw
    · rintro p ⟨n, rfl⟩; exact le_rfl
    · intro q hq hub; exact hub bhTwoProj ⟨0, rfl⟩
  · intro n; rw [hww]; exact pseudoinvertible_of_isStarProjection hw
  · intro n; rw [mul_one]; exact pseudoinvertible_of_isStarProjection hw
  · intro n
    rw [hww, mul_one]
    exact ⟨1, 1, fun a _ => by rw [one_mul, mul_one], fun a _ => by rw [one_mul, mul_one],
      zero_le_one, zero_le_one, rfl,
      by rw [ceil_one]; exact (ceil_spec hw.nonneg).1.le_one,
      by rw [ceil_one]; exact (ceil_spec hw.nonneg).1.le_one⟩
  · rw [bhTwoProj_cceil, bhTwoOne_cceil]

/-- **104III** (`centrally-similar-basic`, proc.tex:1465, Exercise),
part 5: if `p, q` commute and `e₁ ≤ e₂ ≤ ⋯` are projections commuting
with `p` and `q`, with `⋃ₙ eₙ = ⌈p⌉`, such that the `eₙp` and `eₙq` are
pseudoinvertible and centrally similar, then `p` and `q` are centrally
similar **on the grounds that both `(p∧q)/p` and `(p∧q)/q` are central**.

That last clause is an assertion in its own right — it is the whole content
of the hint, and it is exactly the hypothesis of part 3 — so it is stated
here as the first two conjuncts, with `CentrallySimilar p q` obtained from
them by `centrally_similar_basic_3`.  Only the grounds clause is `sorry`.

**Repaired by the author on 2026-08-19** (erratum `parsec-1040.30`), first
with `⌈p⌉ = ⌈q⌉` and then, the same day, with the full faithfulness
`⌈p⌉ = ⌈q⌉ = 1` of points 2a–4.  `⌈p⌉ = ⌈q⌉` alone excludes
`centrally_similar_basic_5_counterexample` just above, but leaves the
exercise's *stated route* — "on the grounds that both `(p∧q)/p` and
`(p∧q)/q` are central" — unachievable: in `B(ℂ²)` at `p = diag(1,0)`,
`q = diag(2,0)` and the constant `eₙ = diag(1,0)` every hypothesis holds and
`p ∼ q` (via the scalars `2` and `1`), yet `p ∧ q = p`, so
`(p∧q)/p = ⌈p⌉ = diag(1,0)` is not central.  Under `⌈p⌉ = ⌈q⌉ = 1` that
witness is gone and the grounds clause is exactly the hypothesis of part 3.

Still `sorry`: the route runs `(p∧q)eₙ = (peₙ) ∧ (qeₙ)` (`meet_mul_right`)
and then wants part 4's third `iff` for `eₙp, eₙq`, whose carriers are `eₙ`
rather than `1`; a form of part 4 relative to a projection unit is what is
missing.  Note that the final step does *not* need `Z(e𝒜e) = Z(𝒜)e`: corner
centrality of `γeₙ` kills `eₙ(γa − aγ)eₙ` for every `n`, and `⋃ₙ eₙ = 1`
finishes, as in session 91's proof of 104VII. -/
theorem centrally_similar_basic_5 [VonNeumannAlgebra A] (p q : A)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcp : ceil p = 1) (hcq : ceil q = 1)
    (hcomm : p * q = q * p) (e : ℕ → A)
    (he : ∀ n, IsStarProjection (e n)) (hmono : Monotone e)
    (hecp : ∀ n, e n * p = p * e n) (hecq : ∀ n, e n * q = q * e n)
    (hsup : projSup (Set.range e) = ceil p)
    (hpin : ∀ n, Pseudoinvertible A (e n * p))
    (hqin : ∀ n, Pseudoinvertible A (e n * q))
    (hcs : ∀ n, CentrallySimilar (e n * p) (e n * q)) :
    div (Theses.A.CStar.meet p q) p ∈ centre A ∧
      div (Theses.A.CStar.meet p q) q ∈ centre A ∧ CentrallySimilar p q := by
  -- the exercise's *grounds* clause is the whole content; given it, the
  -- conclusion is part 3 applied to `p`, `q`
  have grounds : div (Theses.A.CStar.meet p q) p ∈ centre A ∧
      div (Theses.A.CStar.meet p q) q ∈ centre A := sorry
  exact ⟨grounds.1, grounds.2,
    centrally_similar_basic_3 p q hp hq hcp hcq hcomm grounds.1 grounds.2⟩

/-- **104IV**, obstruction: the printed statement of 104IV omits the
faithfulness hypothesis `⌈q⌉ = 1` that its own proof invokes ("`ϑ(e)q = qe
= eq` **and `⌈q⌉ = 1`** imply that `ϑ(e) = e` by `mult-cancellation`",
proc.tex:1543).  Without it the hypotheses hold vacuously at `q = 0` — as
this theorem checks — so the printed lemma would force *every* miu-endomorphism
of *every* von Neumann algebra to fix *every* projection, and hence (by
**65IV** `projections-norm-dense`) to be the identity: false already for
`Ad_u` on `B(ℂ²)`, or the flip on `ℂ ⊕ ℂ`.  See `ERRATA.md`.  Only the
second conclusion fails; `eq = qe` needs no faithfulness. -/
theorem centrally_similar_fundamental_needs_faithful [VonNeumannAlgebra A]
    (printed : ∀ (e q : A), IsStarProjection e → 0 ≤ q → ∀ ϑ : MIUMap A A,
      ceil (q * ϑ e * q) ≤ e → ceil (q * ϑ (1 - e) * q) ≤ 1 - e →
      e * q = q * e ∧ ϑ e = e) :
    ∀ e : A, IsStarProjection e → ∀ ϑ : MIUMap A A, ϑ e = e := by
  intro e he ϑ
  have hz : ∀ x : A, (0 : A) * x * 0 = 0 := fun x => by rw [zero_mul, mul_zero]
  refine (printed e 0 he le_rfl ϑ ?_ ?_).2
  · rw [hz, ceil_zero]; exact he.nonneg
  · rw [hz, ceil_zero]; exact he.one_sub.nonneg

/-- **104IV** (`centrally-similar-fundamental`, proc.tex:1519, Lemma):
if `⌈q ϑ(e) q⌉ ≤ e` and `⌈q ϑ(e^⊥) q⌉ ≤ e^⊥` for a projection `e`,
positive `q` **with `⌈q⌉ = 1`**, and an miu-map `ϑ : 𝒜 → 𝒜`, then `eq = qe`
and `ϑ(e) = e`.

The hypothesis `⌈q⌉ = 1` is **not printed** in the thesis but is used in its
proof, and without it the second conclusion is false — see
`centrally_similar_fundamental_needs_faithful` above and the **104IV**
(`centrally-similar-fundamental`) row of `ERRATA.md` (status OPEN), which
asks for `⌈q⌉ = 1` to be added to the hypotheses.  Both consumers of the
lemma (104VI, 104VII) do state it, so nothing downstream changes. -/
theorem centrally_similar_fundamental [VonNeumannAlgebra A] (e q : A)
    (he : IsStarProjection e) (hq : 0 ≤ q) (hcq : ceil q = 1) (ϑ : MIUMap A A)
    (h1 : ceil (q * ϑ e * q) ≤ e)
    (h2 : ceil (q * ϑ (1 - e) * q) ≤ 1 - e) :
    e * q = q * e ∧ ϑ e = e := by
  -- the author's proof (proc.tex:1525), verbatim: `⌈qϑ(e)q⌉ = ⌈ϑ(e)q⌋`, so
  -- `ϑ(e)qe = ϑ(e)q` and `ϑ(e^⊥)qe = 0`; hence `qe = ϑ(e)q`, making
  -- `q²e = qϑ(e)q` self-adjoint, so `q²` and then `q = √(q²)` commute with
  -- `e` (**23VII** `sqrt`); finally `mult-cancellation` (**60VIII**.2).
  have hqsa : IsSelfAdjoint q := IsSelfAdjoint.of_nonneg hq
  have hproj : ∀ p : A, IsStarProjection p → IsStarProjection (ϑ p) := by
    intro p hp
    exact ⟨by show ϑ p * ϑ p = ϑ p; rw [← map_mul, hp.isIdempotentElem.eq],
      by show star (ϑ p) = ϑ p; rw [← map_star, hp.isSelfAdjoint.star_eq]⟩
  -- `⌈q ϑ(p) q⌉ = ⌈ϑ(p)q⌋` for a projection `p` (**59VI** `ceill-basic`)
  have hceil : ∀ p : A, IsStarProjection p →
      ceil (q * ϑ p * q) = suppProj (ϑ p * q) := by
    intro p hp
    have hs : star (ϑ p * q) * (ϑ p * q) = q * ϑ p * q := by
      rw [star_mul, hqsa.star_eq, (hproj p hp).isSelfAdjoint.star_eq]
      calc q * ϑ p * (ϑ p * q) = q * (ϑ p * ϑ p) * q := by noncomm_ring
        _ = q * ϑ p * q := by rw [(hproj p hp).isIdempotentElem.eq]
    rw [suppProj, hs]
  -- `⌈x⌋ ≤ p` gives `xp = x` (**59VI**.1)
  have habs : ∀ x p : A, IsStarProjection p → suppProj x ≤ p → x * p = x := by
    intro x p hp hle
    obtain ⟨⟨hsp, hxs⟩, -⟩ := ceill_basic_1 x
    have hmul : suppProj x * p = suppProj x := (hsp.le_iff_mul_eq_left hp).mp hle
    calc x * p = x * suppProj x * p := by rw [hxs]
      _ = x * (suppProj x * p) := by noncomm_ring
      _ = x * suppProj x := by rw [hmul]
      _ = x := hxs
  have hep : IsStarProjection (1 - e) := he.one_sub
  have ha1 : ϑ e * q * e = ϑ e * q := habs _ _ he (by rw [← hceil e he]; exact h1)
  have ha2 : ϑ (1 - e) * q * (1 - e) = ϑ (1 - e) * q :=
    habs _ _ hep (by rw [← hceil (1 - e) hep]; exact h2)
  have ha3 : ϑ (1 - e) * q * e = 0 := by
    calc ϑ (1 - e) * q * e = ϑ (1 - e) * q * (1 - e) * e := by rw [ha2]
      _ = ϑ (1 - e) * q * ((1 - e) * e) := by noncomm_ring
      _ = 0 := by
          rw [sub_mul, one_mul, he.isIdempotentElem.eq, sub_self, mul_zero]
  have hqe : q * e = ϑ e * q := by
    have hsum : ϑ e + ϑ (1 - e) = 1 := by rw [← map_add, add_sub_cancel, map_one]
    calc q * e = (ϑ e + ϑ (1 - e)) * (q * e) := by rw [hsum, one_mul]
      _ = ϑ e * q * e + ϑ (1 - e) * q * e := by noncomm_ring
      _ = ϑ e * q := by rw [ha3, ha1, add_zero]
  have hcomm2 : e * q ^ 2 = q ^ 2 * e := by
    have hkey : q ^ 2 * e = q * ϑ e * q := by rw [sq, mul_assoc, hqe]; noncomm_ring
    have hsa : IsSelfAdjoint (q ^ 2 * e) := by
      rw [hkey]
      show star (q * ϑ e * q) = q * ϑ e * q
      rw [star_mul, star_mul, hqsa.star_eq, (hproj e he).isSelfAdjoint.star_eq]
      noncomm_ring
    have h := hsa.star_eq
    rwa [star_mul, he.isSelfAdjoint.star_eq, (hqsa.pow 2).star_eq] at h
  have hcomm : e * q = q * e := by
    have hsq : (0 : A) ≤ q ^ 2 := by
      have h := star_mul_self_nonneg q
      rwa [hqsa.star_eq, ← sq] at h
    have hcc := (Theses.A.CStar.sqrt_commute (q ^ 2) hsq e hcomm2).1
    rwa [CFC.sqrt_sq q hq] at hcc
  refine ⟨hcomm, ?_⟩
  -- `⌈q⌉ = 1` forces `⌊q⌉ = 1`, so `mult-cancellation` applies to `ϑ(e)q = eq`
  have hrq : rangeProj q = 1 := by
    obtain ⟨⟨hrp, hrq0⟩, -⟩ := ceill_basic_2 q
    have hqr : q * rangeProj q = q := by
      have h := congrArg star hrq0
      rwa [star_mul, hqsa.star_eq, hrp.isSelfAdjoint.star_eq] at h
    have hz : q * (1 - rangeProj q) = 0 := by rw [mul_sub, mul_one, hqr, sub_self]
    have h := ceil_mul_eq_zero hq hz
    rw [hcq, one_mul, sub_eq_zero] at h
    exact h.symm
  refine mult_cancellation_2 q (ϑ e) e ?_ ?_ ?_
  · rw [hrq]; exact (ceill_basic_1 (ϑ e)).1.1.le_one
  · rw [hrq]; exact (ceill_basic_1 e).1.1.le_one
  · rw [← hqe, hcomm]

/-- **104VI** (`centrally-similar-corollary`, proc.tex:1546, Corollary): a
positive `q` with `⌈q⌉ = 1` is central provided there is an miu-map `ϑ`
with `⌈q ϑ(e) q⌉ ≤ e` for every projection `e`; and then `ϑ = id`. -/
theorem centrally_similar_corollary [VonNeumannAlgebra A] (q : A)
    (hq : 0 ≤ q) (hcq : ceil q = 1) (ϑ : MIUMap A A)
    (h : ∀ e : A, IsStarProjection e → ceil (q * ϑ e * q) ≤ e) :
    q ∈ centre A ∧ ∀ a, ϑ a = a := by
  -- **104IV** applies to every projection `e`, since its second hypothesis
  -- is this one at `e^⊥`; it gives `eq = qe` and `ϑ(e) = e`.  Both
  -- conclusions then extend from the projections to all of `𝒜` because
  -- their linear span is norm-dense (**65IV**) and `x ↦ xq`, `x ↦ qx` and
  -- `ϑ` are continuous and linear.
  have hfund : ∀ e : A, IsStarProjection e → e * q = q * e ∧ ϑ e = e := fun e he =>
    centrally_similar_fundamental e q he hq hcq ϑ (h e he) (h (1 - e) he.one_sub)
  have hcont : Continuous ⇑ϑ :=
    AddMonoidHomClass.continuous_of_bound ϑ 1
      fun x => by simpa using NonUnitalStarAlgHom.norm_apply_le ϑ x
  constructor
  · intro m _
    let S : Submodule ℂ A :=
      { carrier := {y : A | y * q = q * y}
        add_mem' := by
          intro y z hy hz
          replace hy : y * q = q * y := hy
          replace hz : z * q = q * z := hz
          change (y + z) * q = q * (y + z)
          rw [add_mul, mul_add, hy, hz]
        zero_mem' := by change (0 : A) * q = q * 0; rw [zero_mul, mul_zero]
        smul_mem' := by
          intro c y hy
          replace hy : y * q = q * y := hy
          change (c • y) * q = q * (c • y)
          rw [smul_mul_assoc, mul_smul_comm, hy] }
    have hclosed : IsClosed (S : Set A) :=
      isClosed_eq (continuous_id.mul continuous_const)
        (continuous_const.mul continuous_id)
    exact mem_of_isClosed_of_projections S hclosed (fun p hp => (hfund p hp).1) m
  · intro a
    let S : Submodule ℂ A :=
      { carrier := {y : A | ϑ y = y}
        add_mem' := by
          intro y z hy hz
          replace hy : ϑ y = y := hy
          replace hz : ϑ z = z := hz
          change ϑ (y + z) = y + z
          rw [map_add, hy, hz]
        zero_mem' := by change ϑ (0 : A) = 0; rw [map_zero]
        smul_mem' := by
          intro c y hy
          replace hy : ϑ y = y := hy
          change ϑ (c • y) = c • y
          rw [map_smul, hy] }
    have hclosed : IsClosed (S : Set A) := isClosed_eq hcont continuous_id
    exact mem_of_isClosed_of_projections S hclosed (fun p hp => (hfund p hp).2) a


/-! ### Infrastructure for 104VII (`positive-quotients-centrally-similar`)

The authors' proof (proc.tex:1558) has four steps: (1) `⌈pep⌉ = e` for
projections `e` commuting with `p`, so **104IV** gives `eq = qe` and
`ϑ(e) = e`, whence `pq = qp` and `ϑ(p) = p` by **65IV**; (2) a sequence of
projections `e₁ ≤ e₂ ≤ ⋯` commuting with `p` and `q` with `⋃ₙeₙ = ⌈p⌉` and
`eₙp`, `eₙq` pseudoinvertible; (3) the reduction to the invertible case by
passing to the corner `eₙ𝒜eₙ`, where **104VI** applies; (4) descent from the
corners back to `𝒜`.

Steps 1 and 2 are transcribed faithfully — for (2) we take the spectral
projections `Eₙ = 1_{(tₙ,∞)}(p)·1_{(tₙ,∞)}(q)`, `tₙ = 1/(n+1)`, rather than
the thesis's approximate pseudoinverse of `p ∧ q`, which presupposes that
`p ∧ q` exists (ERRATA **104VIII**(b)); the thesis offers its construction
only as an example.

Step (4) is a **different route** (ERRATA **104VIII**(a)).  The printed
proof descends by applying **104III**.5 to the corner-wise central
similarities; but the central elements it obtains from **104VI** are central
in `eₙ𝒜eₙ`, not in `𝒜`, and bridging the two needs `Z(e𝒜e) = Z(𝒜)e`, which
is in neither thesis nor tree.  We avoid the bridge altogether: the *single
global* element `d := p/(p+q)` (which exists by Douglas' lemma **81V**.1,
since `p² ≤ (p+q)²`, and is unique because `⌈p+q⌉ = 1`) restricts on each
corner to `d·Eₙ = (Eₙ + zₙ)^{-1}` with `zₙ = (pEₙ)^{∼1}(qEₙ)` central in
`Eₙ𝒜Eₙ` by **104VI**; so `Eₙ(da − ad)Eₙ = 0` for every `n` and every
`a ∈ 𝒜`, and `d` is central in `𝒜`.  Then `(1−d)p = dq` is the central
similarity outright, and neither **104III**.5 nor `Z(e𝒜e) = Z(𝒜)e` is used.
Likewise `ϑ = id` follows from `ϑ(EₙaEₙ) = EₙaEₙ` with no appeal to the
ultrastrong continuity of `ϑ` (ERRATA **104VIII**(c)): what replaces
"`eₙaeₙ → a` ultrastrongly" is the elementary `eq_zero_of_mul_specPair`,
that only `0` is annihilated by every `Eₙ`. -/

section Aux104VII

variable [VonNeumannAlgebra A]

/-- `c·b = 0` implies `c·⌈b⌉ = 0` for positive `b` (the mirror image of
`ceil_mul_eq_zero`). -/
theorem mul_ceil_eq_zero {b : A} (hb : 0 ≤ b) {c : A} (h : c * b = 0) :
    c * ceil b = 0 := by
  have h' : b * star c = 0 := by
    have h2 := congrArg star h
    rwa [star_mul, star_zero, (IsSelfAdjoint.of_nonneg hb).star_eq] at h2
  have h3 := congrArg star (ceil_mul_eq_zero hb h')
  rwa [star_mul, star_star, star_zero,
    (ceil_spec hb).1.isSelfAdjoint.star_eq] at h3

omit [VonNeumannAlgebra A] in
/-- A projection of the corner `e𝒜e` is the same thing as a projection of
`𝒜` lying in the corner. -/
theorem Corner.isStarProjection_iff {e : A} [Fact (IsStarProjection e)]
    (f : Corner A e) : IsStarProjection f ↔ IsStarProjection f.val :=
  ⟨fun h => ⟨congrArg Corner.val h.isIdempotentElem,
      congrArg Corner.val h.isSelfAdjoint⟩,
    fun h => ⟨Corner.val_injective h.isIdempotentElem,
      Corner.val_injective h.isSelfAdjoint⟩⟩

/-- The ceiling of an element of the corner `e𝒜e` is computed in the corner
exactly as it is in `𝒜` (**94II**: the projections of the corner are the
projections of `𝒜` below `e`, and the order is inherited). -/
theorem Corner.val_ceil {e : A} [Fact (IsStarProjection e)]
    (x : Corner A e) (hx : 0 ≤ x) : (ceil x).val = ceil x.val := by
  have hxv : (0 : A) ≤ x.val := hx
  have hce : ceil x.val ≤ e :=
    (ceil_le_iff hxv (Corner.proj e)).mpr (Corner.mul_right x)
  have hcp : IsStarProjection (ceil x.val) := (ceil_spec hxv).1
  have h1 : ceil x.val * e = ceil x.val :=
    (hcp.le_iff_mul_eq_left (Corner.proj e)).mp hce
  have h2 : e * ceil x.val = ceil x.val := by
    have h3 := congrArg star h1
    rwa [star_mul, hcp.isSelfAdjoint.star_eq,
      (Corner.proj e).isSelfAdjoint.star_eq] at h3
  have hmem : e * ceil x.val * e = ceil x.val := by rw [h2, h1]
  refine congrArg Corner.val
    (ceil_eq_of_isLeast hx (p := ⟨ceil x.val, hmem⟩) ?_ ?_ ?_)
  · exact (Corner.isStarProjection_iff _).mpr hcp
  · exact Corner.val_injective (ceil_spec hxv).2.1
  · intro g hg hxg
    show ceil x.val ≤ g.val
    exact (ceil_spec hxv).2.2 g.val ((Corner.isStarProjection_iff g).mp hg)
      (congrArg Corner.val hxg)

/-- An miu-map `ϑ : 𝒜 → 𝒜` fixing a projection `e` restricts to an miu-map
of the corner `e𝒜e`. -/
def cornerMIU {e : A} [Fact (IsStarProjection e)] (ϑ : MIUMap A A)
    (he : ϑ e = e) : MIUMap (Corner A e) (Corner A e) where
  toFun x := ⟨ϑ x.val, by
    have hx : ϑ (e * x.val * e) = ϑ e * ϑ x.val * ϑ e := by rw [map_mul, map_mul]
    rw [x.property, he] at hx
    exact hx.symm⟩
  map_one' := Corner.val_injective he
  map_mul' x y := Corner.val_injective (map_mul ϑ _ _)
  map_zero' := Corner.val_injective (map_zero ϑ)
  map_add' x y := Corner.val_injective (map_add ϑ _ _)
  map_star' x := Corner.val_injective (map_star ϑ _)
  commutes' r := Corner.val_injective (by
    show ϑ ((algebraMap ℂ (Corner A e) r).val) = (algebraMap ℂ (Corner A e) r).val
    rw [Algebra.algebraMap_eq_smul_one]
    show ϑ (r • e) = r • e
    rw [map_smul, he])

omit [VonNeumannAlgebra A] in
@[simp] theorem cornerMIU_val {e : A} [Fact (IsStarProjection e)]
    (ϑ : MIUMap A A) (he : ϑ e = e) (x : Corner A e) :
    (cornerMIU ϑ he x).val = ϑ x.val := rfl

/-! #### Spectral projections

`1_{(t,∞)}(a) = ⌈(a − t)⁺⌉`, for positive `a` and `t > 0`.  These are the
projections **104VII** needs: they commute with everything that commutes
with `a`, they increase to `⌈a⌉` as `t ↓ 0`, and `a` is *pseudoinvertible*
on each of them, with the explicit pseudoinverse `1/max(a,t)`. -/

/-- The positive part `(a − t)⁺` of `a − t`, as a continuous function of
`a`; the spectral projection `1_{(t,∞)}(a)` is its carrier. -/
noncomputable def specPos (a : A) (t : ℝ) : A := cfc (fun r : ℝ => max (r - t) 0) a

/-- The spectral projection `1_{(t,∞)}(a) = ⌈(a − t)⁺⌉` of a positive
element `a` of a von Neumann algebra. -/
noncomputable def spectralProj (a : A) (t : ℝ) : A := ceil (specPos a t)

omit [VonNeumannAlgebra A] in
theorem specPos_nonneg (a : A) (t : ℝ) : (0 : A) ≤ specPos a t :=
  cfc_nonneg (fun _ _ => le_max_right _ _)

theorem spectralProj_isStarProjection (a : A) (t : ℝ) :
    IsStarProjection (spectralProj a t) := (ceil_spec (specPos_nonneg a t)).1

theorem specPos_mul_spectralProj (a : A) (t : ℝ) :
    specPos a t * spectralProj a t = specPos a t :=
  (ceil_spec (specPos_nonneg a t)).2.1

theorem spectralProj_mul_specPos (a : A) (t : ℝ) :
    spectralProj a t * specPos a t = specPos a t := by
  have h := congrArg star (specPos_mul_spectralProj a t)
  rwa [star_mul, (IsSelfAdjoint.of_nonneg (specPos_nonneg a t)).star_eq,
    (spectralProj_isStarProjection a t).isSelfAdjoint.star_eq] at h

/-- Whatever commutes with `a` commutes with `1_{(t,∞)}(a)`. -/
theorem spectralProj_comm (a : A) (t : ℝ) (x : A) (hx : a * x = x * a) :
    x * spectralProj a t = spectralProj a t * x :=
  ceil_basic_2 _ x (specPos_nonneg a t) (Commute.cfc_real hx _).symm

omit [VonNeumannAlgebra A] in
/-- `‖a − (a − t)⁺‖ ≤ t` for positive `a` and `t ≥ 0`. -/
theorem norm_sub_specPos_le {a : A} (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    ‖a - specPos a t‖ ≤ t := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hrw : a - specPos a t = cfc (fun r : ℝ => r - max (r - t) 0) a := by
    rw [specPos, cfc_sub _ _ a (by fun_prop) (by fun_prop)]
    congr 1
    exact (cfc_id ℝ a).symm
  rw [hrw]
  refine norm_cfc_le ht fun r hr => ?_
  have hr0 : (0 : ℝ) ≤ r := spectrum_nonneg_of_nonneg ha hr
  rw [Real.norm_eq_abs, abs_le]
  rcases le_total r t with h | h
  · rw [max_eq_right (by linarith)]
    constructor <;> linarith
  · rw [max_eq_left (by linarith)]
    constructor <;> linarith

/-- If `x` kills every `1_{(t,∞)}(a)` (`t > 0`) then it kills `a`. -/
theorem mul_eq_zero_of_mul_spectralProj_eq_zero {a x : A} (ha : 0 ≤ a)
    (h : ∀ n : ℕ, x * spectralProj a ((n : ℝ) + 1)⁻¹ = 0) : x * a = 0 := by
  have hkey : ∀ n : ℕ, ‖x * a‖ ≤ ‖x‖ * ((n : ℝ) + 1)⁻¹ := by
    intro n
    set t : ℝ := ((n : ℝ) + 1)⁻¹ with htdef
    have ht : 0 < t := by positivity
    have hxg : x * specPos a t = 0 := by
      rw [← spectralProj_mul_specPos a t, ← mul_assoc, h n, zero_mul]
    have hxa : x * a = x * (a - specPos a t) := by rw [mul_sub, hxg, sub_zero]
    calc ‖x * a‖ = ‖x * (a - specPos a t)‖ := by rw [hxa]
      _ ≤ ‖x‖ * ‖a - specPos a t‖ := norm_mul_le _ _
      _ ≤ ‖x‖ * t := by
          exact mul_le_mul_of_nonneg_left (norm_sub_specPos_le ha ht.le) (norm_nonneg x)
  refine norm_le_zero_iff.mp ?_
  by_contra hc
  rw [not_le] at hc
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / ‖x * a‖)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmul : ‖x * a‖ * ((n : ℝ) + 1) ≤ ‖x‖ := by
    rw [← le_div_iff₀ hpos]
    simpa [div_eq_mul_inv] using hkey n
  rw [div_lt_iff₀ hc] at hn
  nlinarith [norm_nonneg x]

/-- The bounded "inverse" `1/max(a,t)` of a positive `a`, which inverts `a`
on the spectral projection `1_{(t,∞)}(a)`. -/
noncomputable def specInv (a : A) (t : ℝ) : A := cfc (fun r : ℝ => (max r t)⁻¹) a

omit [VonNeumannAlgebra A] in
theorem specInv_nonneg (a : A) {t : ℝ} (ht : 0 < t) : (0 : A) ≤ specInv a t :=
  cfc_nonneg fun r _ => by positivity

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
theorem specInv_comm (a : A) (t : ℝ) (x : A) (hx : a * x = x * a) :
    x * specInv a t = specInv a t * x := (Commute.cfc_real hx _).symm

/-- `1/max(a,t)` is a left (and right) inverse of `a` on `1_{(t,∞)}(a)`:
this is the pseudoinvertibility of `a·1_{(t,∞)}(a)` that **104VII**'s
reduction needs. -/
theorem specInv_mul_mul_spectralProj {a : A} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    specInv a t * a * spectralProj a t = spectralProj a t := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hcont : Continuous (fun r : ℝ => (max r t)⁻¹) :=
    Continuous.inv₀ (by fun_prop) fun r => ne_of_gt (lt_of_lt_of_le ht (le_max_right r t))
  have hcont2 : Continuous (fun r : ℝ => 1 - (max r t)⁻¹ * r) :=
    continuous_const.sub (hcont.mul continuous_id)
  have h1 : specInv a t * a = cfc (fun r : ℝ => (max r t)⁻¹ * r) a := by
    rw [cfc_mul (fun r : ℝ => (max r t)⁻¹) (fun r : ℝ => r) a hcont.continuousOn
      (by fun_prop), specInv, show (fun r : ℝ => r) = (id : ℝ → ℝ) from rfl, cfc_id ℝ a]
  have h2 : (1 : A) - specInv a t * a = cfc (fun r : ℝ => 1 - (max r t)⁻¹ * r) a := by
    rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun r : ℝ => (max r t)⁻¹ * r) a (by fun_prop)
      ((hcont.mul continuous_id).continuousOn), h1]
    congr 1
    exact (cfc_const_one ℝ a).symm
  have h3 : ((1 : A) - specInv a t * a) * specPos a t = 0 := by
    rw [h2, specPos, ← cfc_mul _ _ a hcont2.continuousOn (by fun_prop),
      show (0 : A) = cfc (fun _ : ℝ => (0 : ℝ)) a by simp]
    refine cfc_congr fun r hr => ?_
    have hr0 : (0 : ℝ) ≤ r := spectrum_nonneg_of_nonneg ha hr
    rcases le_total r t with h | h
    · rw [max_eq_right (by linarith : r - t ≤ 0), mul_zero]
    · have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le ht h)
      rw [max_eq_left h, inv_mul_cancel₀ hrne, sub_self, zero_mul]
  have h4 := mul_ceil_eq_zero (specPos_nonneg a t) h3
  rw [← spectralProj, sub_mul, one_mul, sub_eq_zero] at h4
  exact h4.symm

/-- The spectral projections increase as `t` decreases. -/
theorem spectralProj_mono {a : A} (ha : 0 ≤ a) {s t : ℝ} (hst : s ≤ t) :
    spectralProj a t ≤ spectralProj a s := by
  refine ceil_mono (specPos_nonneg a t) ?_
  rw [specPos, specPos]
  exact cfc_mono fun r _ => max_le_max (by linarith) le_rfl

/-! #### Steps 1–2 of the proof of 104VII -/

/-- **104VII**, step 1 (proc.tex:1560): `⌈pep⌉ = e` for a projection `e`
commuting with a faithful positive `p` — because `pep = ep²` and
`⌈p²⌉ = ⌈p⌉ = 1`. -/
theorem ceil_mul_proj_mul_of_comm {p e : A} (hp : 0 ≤ p) (hcp : ceil p = 1)
    (he : IsStarProjection e) (hcomm : e * p = p * e) :
    ceil (p * e * p) = e := by
  have hsq : (0 : A) ≤ p ^ 2 := by
    have h := star_mul_self_nonneg p
    rwa [(IsSelfAdjoint.of_nonneg hp).star_eq, ← sq] at h
  have hcomm2 : e * p ^ 2 = p ^ 2 * e := by
    rw [sq]
    calc e * (p * p) = e * p * p := by rw [mul_assoc]
      _ = p * e * p := by rw [hcomm]
      _ = p * (e * p) := by rw [mul_assoc]
      _ = p * (p * e) := by rw [hcomm]
      _ = p * p * e := by rw [mul_assoc]
  have hrw : p * e * p = e * p ^ 2 := by
    rw [sq]
    calc p * e * p = e * p * p := by rw [hcomm]
      _ = e * (p * p) := by rw [mul_assoc]
  have hnn : (0 : A) ≤ e * p ^ 2 := Theses.A.CStar.sqrt_1 e (p ^ 2) he.nonneg hsq hcomm2
  rw [hrw]
  refine le_antisymm ?_ ?_
  · refine (ceil_le_iff hnn he).mpr ?_
    rw [mul_assoc, ← hcomm2, ← mul_assoc, he.isIdempotentElem.eq]
  · set r : A := ceil (e * p ^ 2) with hrdef
    have hrp : IsStarProjection r := (ceil_spec hnn).1
    have h1 : e * p ^ 2 * r = e * p ^ 2 := (ceil_spec hnn).2.1
    have h2 : r * (e * p ^ 2) = e * p ^ 2 := by
      have h := congrArg star h1
      rwa [star_mul, hrp.isSelfAdjoint.star_eq,
        (IsSelfAdjoint.of_nonneg hnn).star_eq] at h
    have h3 : ((1 : A) - r) * e * p ^ 2 = 0 := by
      have hexp : ((1 : A) - r) * e * p ^ 2 = e * p ^ 2 - r * (e * p ^ 2) := by
        noncomm_ring
      rw [hexp, h2, sub_self]
    have h4 : ((1 : A) - r) * e * ceil (p ^ 2) = 0 := mul_ceil_eq_zero hsq h3
    rw [ceil_basic_5 p hp, hcp, mul_one, sub_mul, one_mul, sub_eq_zero] at h4
    refine (he.le_iff_mul_eq_left hrp).mpr ?_
    have h5 := congrArg star h4
    rwa [star_mul, hrp.isSelfAdjoint.star_eq, he.isSelfAdjoint.star_eq, eq_comm] at h5

/-- **104VII**, steps 1–2 (proc.tex:1560): under the hypotheses of 104VII,
`ϑ` fixes every projection commuting with `p`, and `q` commutes with it; so
`pq = qp` and `ϑ(p) = p`, because `p` is a norm limit of linear
combinations of projections from `{p}^□□` (**65IV**). -/
theorem positive_quotients_step12 {p q : A} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hcp : ceil p = 1) (hcq : ceil q = 1) (ϑ : MIUMap A A)
    (h : ∀ e : A, IsStarProjection e → ceil (p * e * p) = ceil (q * ϑ e * q)) :
    (∀ e : A, IsStarProjection e → e * p = p * e → e * q = q * e ∧ ϑ e = e) ∧
      p * q = q * p ∧ ϑ p = p := by
  have hfix : ∀ e : A, IsStarProjection e → e * p = p * e →
      e * q = q * e ∧ ϑ e = e := by
    intro e he hcomm
    have hperp : (1 - e) * p = p * (1 - e) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
    refine centrally_similar_fundamental e q he hq hcq ϑ ?_ ?_
    · rw [← h e he, ceil_mul_proj_mul_of_comm hp hcp he hcomm]
    · rw [← h (1 - e) he.one_sub, ceil_mul_proj_mul_of_comm hp hcp he.one_sub hperp]
  refine ⟨hfix, ?_⟩
  have hcont : Continuous ⇑ϑ :=
    AddMonoidHomClass.continuous_of_bound ϑ 1
      fun x => by simpa using NonUnitalStarAlgHom.norm_apply_le ϑ x
  let S : Submodule ℂ A :=
    { carrier := {y : A | y * q = q * y ∧ ϑ y = y}
      add_mem' := by
        rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        exact ⟨by rw [add_mul, mul_add, hy1, hz1], by rw [map_add, hy2, hz2]⟩
      zero_mem' := ⟨by rw [zero_mul, mul_zero], map_zero ϑ⟩
      smul_mem' := by
        rintro c y ⟨hy1, hy2⟩
        exact ⟨by rw [smul_mul_assoc, mul_smul_comm, hy1], by rw [map_smul, hy2]⟩ }
  have hclosed : IsClosed (S : Set A) := by
    have : (S : Set A) = {y : A | y * q = q * y} ∩ {y : A | ϑ y = y} := rfl
    rw [this]
    exact (isClosed_eq (continuous_id.mul continuous_const)
      (continuous_const.mul continuous_id)).inter (isClosed_eq hcont continuous_id)
  have hspan : Submodule.span ℂ
      {r : A | IsStarProjection r ∧ r ∈ commutant A (commutant A {p})} ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro r ⟨hrp, hrc⟩
    have hcomm : r * p = p * r := by
      have hpm : p ∈ commutant A {p} := fun m hm => by
        rw [Set.mem_singleton_iff] at hm; rw [hm]
      exact (hrc p hpm).symm
    exact hfix r hrp hcomm
  have hmem : p ∈ closure (S : Set A) :=
    closure_mono (SetLike.coe_subset_coe.mpr hspan)
      (projections_norm_dense p (IsSelfAdjoint.of_nonneg hp))
  rw [hclosed.closure_eq] at hmem
  exact ⟨hmem.1, hmem.2⟩

/-! #### The corner step -/

/-- **104VII**, the reduction to the invertible case (proc.tex:1585), done
*inside* the corner `E𝒜E` and with no appeal to `Z(E𝒜E) = Z(𝒜)E`.

`E` is a projection commuting with `p` and `q`, and `u`, `v` are positive
elements commuting with everything in sight which invert `p` and `q` on the
corner (`upE = E = vqE`) — for the spectral projections
`E = 1_{(t,∞)}(p)·1_{(t,∞)}(q)` one may take `u = 1/max(p,t)`,
`v = 1/max(q,t)`.  Then `z := uqE = (pE)^{∼1}(qE)` is central **in the
corner**, and `ϑ` is the identity **on the corner**. -/
theorem positive_quotients_corner {p q E u v : A} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hu : 0 ≤ u) (hE : IsStarProjection E)
    (cpE : Commute p E) (cqE : Commute q E)
    (cpu : Commute p u) (cqu : Commute q u) (cuE : Commute u E)
    (cpv : Commute p v) (cuv : Commute u v)
    (hupE : u * p * E = E) (hvqE : v * q * E = E)
    (ϑ : MIUMap A A) (hϑE : ϑ E = E)
    (h : ∀ e : A, IsStarProjection e → ceil (p * e * p) = ceil (q * ϑ e * q)) :
    0 ≤ u * q * E ∧ (u * q * E) * (p * E) = q * E ∧ (p * E) * (u * E) = E ∧
      (∀ x : A, E * x * E = x → (u * q * E) * x = x * (u * q * E)) ∧
      (∀ x : A, E * x * E = x → ϑ x = x) := by
  have hEsa : star E = E := hE.isSelfAdjoint.star_eq
  have husa : star u = u := (IsSelfAdjoint.of_nonneg hu).star_eq
  have hqsa : star q = q := (IsSelfAdjoint.of_nonneg hq).star_eq
  set z : A := u * q * E with hzdef
  have hzE : z * E = z := by rw [hzdef, mul_assoc, hE.isIdempotentElem.eq]
  have hEz : E * z = z := by
    rw [hzdef]
    simp only [mul_assoc]
    rw [cuE.symm.left_comm, cqE.symm.left_comm, hE.isIdempotentElem.eq]
  have hzmem : E * z * E = z := by rw [hEz, hzE]
  have hz0 : (0 : A) ≤ z := by
    refine Theses.A.CStar.sqrt_1 (u * q) E ?_ hE.nonneg (Commute.mul_left cuE cqE)
    exact Theses.A.CStar.sqrt_1 u q hu hq cqu.symm.eq
  -- `⌈z⌉ = E`
  have hceilz : ceil z = E := by
    refine le_antisymm ((ceil_le_iff hz0 hE).mpr hzE) ?_
    have hkey : v * p * z = E := by
      rw [hzdef]
      simp only [mul_assoc]
      rw [cpu.left_comm, cuv.symm.left_comm, cpv.symm.left_comm, ← mul_assoc v q E,
        hvqE, ← mul_assoc u p E, hupE]
    have h1 : suppProj E ≤ suppProj z := hkey ▸ suppProj_mul_le (v * p) z
    rwa [suppProj_of_isStarProjection hE, suppProj_of_nonneg hz0] at h1
  -- the corner
  have : Fact (IsStarProjection E) := ⟨hE⟩
  set zc : Corner A E := ⟨z, hzmem⟩ with hzcdef
  have hzc0 : (0 : Corner A E) ≤ zc := hz0
  have hzc1 : ceil zc = 1 :=
    Corner.val_injective (by rw [Corner.val_ceil zc hzc0]; exact hceilz)
  have hWsa : star (u * E) = u * E := by rw [star_mul, hEsa, husa, cuE.eq]
  have hWp : u * E * p = E := by rw [mul_assoc, ← cpE.eq, ← mul_assoc, hupE]
  have hpW : p * (u * E) = E := by rw [← mul_assoc, cpu.eq, hupE]
  have hyp : ∀ f : Corner A E, IsStarProjection f →
      ceil (zc * cornerMIU ϑ hϑE f * zc) ≤ f := by
    intro f hf
    have hfv : IsStarProjection f.val := (Corner.isStarProjection_iff f).mp hf
    have hϑf : IsStarProjection (ϑ f.val) := hfv.map ϑ
    have hw : (0 : A) ≤ q * ϑ f.val * q := by
      have hcj := star_left_conjugate_nonneg hϑf.nonneg q
      rwa [hqsa] at hcj
    have hpfp : (0 : A) ≤ p * f.val * p := by
      have hcj := star_left_conjugate_nonneg hfv.nonneg p
      rwa [(IsSelfAdjoint.of_nonneg hp).star_eq] at hcj
    have hX0 : (0 : Corner A E) ≤ zc * cornerMIU ϑ hϑE f * zc := by
      show (0 : A) ≤ z * ϑ f.val * z
      have hcj := star_left_conjugate_nonneg hϑf.nonneg z
      rwa [(IsSelfAdjoint.of_nonneg hz0).star_eq] at hcj
    show (ceil (zc * cornerMIU ϑ hϑE f * zc)).val ≤ f.val
    rw [Corner.val_ceil _ hX0]
    show ceil (z * ϑ f.val * z) ≤ f.val
    have hconj : z * ϑ f.val * z = star (u * E) * (q * ϑ f.val * q) * (u * E) := by
      rw [hWsa, hzdef]
      simp only [mul_assoc]
      rw [cqE.left_comm, cqu.symm.left_comm]
    rw [hconj, ceil_fundamental_1 (u * E) (q * ϑ f.val * q) hw, ← h f.val hfv,
      ← ceil_fundamental_1 (u * E) (p * f.val * p) hpfp]
    have hfin : star (u * E) * (p * f.val * p) * (u * E) = f.val := by
      rw [hWsa]
      calc u * E * (p * f.val * p) * (u * E)
          = (u * E * p) * f.val * (p * (u * E)) := by simp only [mul_assoc]
        _ = E * f.val * E := by rw [hWp, hpW]
        _ = f.val := f.property
    rw [hfin, ceil_of_isStarProjection hfv]
  obtain ⟨hcentre, hid⟩ :=
    centrally_similar_corollary zc hzc0 hzc1 (cornerMIU ϑ hϑE) hyp
  have hzP : z * (p * E) = q * E := by
    rw [hzdef]
    simp only [mul_assoc]
    rw [cpE.symm.left_comm, hE.isIdempotentElem.eq, cqu.symm.left_comm,
      ← mul_assoc u p E, hupE]
  have hPU : (p * E) * (u * E) = E := by
    simp only [mul_assoc]
    rw [cuE.symm.left_comm, hE.isIdempotentElem.eq, ← mul_assoc p u E, cpu.eq, hupE]
  refine ⟨hz0, hzP, hPU, fun x hx => ?_, fun x hx => ?_⟩
  · exact (congrArg Corner.val (hcentre ⟨x, hx⟩ (Set.mem_univ _))).symm
  · exact congrArg Corner.val (hid ⟨x, hx⟩)

/-! #### The increasing sequence of spectral projections -/

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- The product of two commuting projections is a projection. -/
theorem isStarProjection_mul_of_commute {a b : A} (ha : IsStarProjection a)
    (hb : IsStarProjection b) (hab : Commute a b) : IsStarProjection (a * b) where
  isIdempotentElem := by
    show a * b * (a * b) = a * b
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab.eq]
      _ = a * a * (b * b) := by simp only [mul_assoc]
      _ = a * b := by rw [ha.isIdempotentElem.eq, hb.isIdempotentElem.eq]
  isSelfAdjoint := by
    show star (a * b) = a * b
    rw [star_mul, hb.isSelfAdjoint.star_eq, ha.isSelfAdjoint.star_eq, hab.eq]

/-- The projections `Eₙ = 1_{(tₙ,∞)}(p)·1_{(tₙ,∞)}(q)` with `tₙ = 1/(n+1)`:
an increasing sequence of projections commuting with `p` and `q`, on each of
which both `p` and `q` are invertible, and whose supremum is `⌈p⌉ ∧ ⌈q⌉`. -/
noncomputable def specPair (p q : A) (n : ℕ) : A :=
  spectralProj p ((n : ℝ) + 1)⁻¹ * spectralProj q ((n : ℝ) + 1)⁻¹

theorem commute_spectralProj_spectralProj {p q : A} (hpq : p * q = q * p) (s t : ℝ) :
    Commute (spectralProj p s) (spectralProj q t) :=
  spectralProj_comm q t _ (spectralProj_comm p s q hpq)

theorem specPair_isStarProjection {p q : A} (hpq : p * q = q * p) (n : ℕ) :
    IsStarProjection (specPair p q n) :=
  isStarProjection_mul_of_commute (spectralProj_isStarProjection _ _)
    (spectralProj_isStarProjection _ _) (commute_spectralProj_spectralProj hpq _ _)

theorem commute_specPair_left {p q : A} (hpq : p * q = q * p) (n : ℕ) :
    Commute p (specPair p q n) := by
  simp only [specPair]
  exact Commute.mul_right (spectralProj_comm p ((n : ℝ) + 1)⁻¹ p rfl)
    (spectralProj_comm q ((n : ℝ) + 1)⁻¹ p hpq.symm)

theorem commute_specPair_right {p q : A} (hpq : p * q = q * p) (n : ℕ) :
    Commute q (specPair p q n) := by
  simp only [specPair]
  exact Commute.mul_right (spectralProj_comm p ((n : ℝ) + 1)⁻¹ q hpq)
    (spectralProj_comm q ((n : ℝ) + 1)⁻¹ q rfl)

/-- `t ↦ 1/(t+1)` is antitone on `ℕ`. -/
theorem specSeq_anti {i j : ℕ} (hij : i ≤ j) :
    ((j : ℝ) + 1)⁻¹ ≤ ((i : ℝ) + 1)⁻¹ := by
  have h0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h1 : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  exact inv_anti₀ h0 h1

/-- The `Eₙ` increase. -/
theorem specPair_mul_specPair {p q : A} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p * q = q * p) {m n : ℕ} (hmn : m ≤ n) :
    specPair p q m * specPair p q n = specPair p q m := by
  have hle : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := specSeq_anti hmn
  have ha : spectralProj p ((m : ℝ) + 1)⁻¹ * spectralProj p ((n : ℝ) + 1)⁻¹ =
      spectralProj p ((m : ℝ) + 1)⁻¹ :=
    ((spectralProj_isStarProjection p _).le_iff_mul_eq_left
      (spectralProj_isStarProjection p _)).mp (spectralProj_mono hp hle)
  have hb : spectralProj q ((m : ℝ) + 1)⁻¹ * spectralProj q ((n : ℝ) + 1)⁻¹ =
      spectralProj q ((m : ℝ) + 1)⁻¹ :=
    ((spectralProj_isStarProjection q _).le_iff_mul_eq_left
      (spectralProj_isStarProjection q _)).mp (spectralProj_mono hq hle)
  have hcomm := commute_spectralProj_spectralProj hpq ((n : ℝ) + 1)⁻¹ ((m : ℝ) + 1)⁻¹
  simp only [specPair]
  calc spectralProj p ((m : ℝ) + 1)⁻¹ * spectralProj q ((m : ℝ) + 1)⁻¹ *
        (spectralProj p ((n : ℝ) + 1)⁻¹ * spectralProj q ((n : ℝ) + 1)⁻¹)
      = spectralProj p ((m : ℝ) + 1)⁻¹ * (spectralProj q ((m : ℝ) + 1)⁻¹ *
          spectralProj p ((n : ℝ) + 1)⁻¹) * spectralProj q ((n : ℝ) + 1)⁻¹ := by
        simp only [mul_assoc]
    _ = spectralProj p ((m : ℝ) + 1)⁻¹ * (spectralProj p ((n : ℝ) + 1)⁻¹ *
          spectralProj q ((m : ℝ) + 1)⁻¹) * spectralProj q ((n : ℝ) + 1)⁻¹ := by
        rw [hcomm.eq]
    _ = (spectralProj p ((m : ℝ) + 1)⁻¹ * spectralProj p ((n : ℝ) + 1)⁻¹) *
          (spectralProj q ((m : ℝ) + 1)⁻¹ * spectralProj q ((n : ℝ) + 1)⁻¹) := by
        simp only [mul_assoc]
    _ = spectralProj p ((m : ℝ) + 1)⁻¹ * spectralProj q ((m : ℝ) + 1)⁻¹ := by rw [ha, hb]

/-- `⋁ₙ Eₙ = 1` when `p` and `q` are faithful: nothing but `0` annihilates
every `Eₙ` on the right. -/
theorem eq_zero_of_mul_specPair {p q y : A} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hcp : ceil p = 1) (hcq : ceil q = 1) (hpq : p * q = q * p)
    (hy : ∀ n : ℕ, y * specPair p q n = 0) : y = 0 := by
  have hstep : ∀ m k : ℕ, y * (spectralProj p ((m : ℝ) + 1)⁻¹ *
      spectralProj q ((k : ℝ) + 1)⁻¹) = 0 := by
    intro m k
    set N : ℕ := max m k with hN
    have hmN : m ≤ N := le_max_left _ _
    have hkN : k ≤ N := le_max_right _ _
    have hle1 : ((N : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := specSeq_anti hmN
    have hle2 : ((N : ℝ) + 1)⁻¹ ≤ ((k : ℝ) + 1)⁻¹ := specSeq_anti hkN
    have ha : spectralProj p ((N : ℝ) + 1)⁻¹ * spectralProj p ((m : ℝ) + 1)⁻¹ =
        spectralProj p ((m : ℝ) + 1)⁻¹ := by
      have h1 := ((spectralProj_isStarProjection p ((m : ℝ) + 1)⁻¹).le_iff_mul_eq_left
        (spectralProj_isStarProjection p ((N : ℝ) + 1)⁻¹)).mp (spectralProj_mono hp hle1)
      have h2 := congrArg star h1
      rwa [star_mul, (spectralProj_isStarProjection p _).isSelfAdjoint.star_eq,
        (spectralProj_isStarProjection p _).isSelfAdjoint.star_eq] at h2
    have hb : spectralProj q ((N : ℝ) + 1)⁻¹ * spectralProj q ((k : ℝ) + 1)⁻¹ =
        spectralProj q ((k : ℝ) + 1)⁻¹ := by
      have h1 := ((spectralProj_isStarProjection q ((k : ℝ) + 1)⁻¹).le_iff_mul_eq_left
        (spectralProj_isStarProjection q ((N : ℝ) + 1)⁻¹)).mp (spectralProj_mono hq hle2)
      have h2 := congrArg star h1
      rwa [star_mul, (spectralProj_isStarProjection q _).isSelfAdjoint.star_eq,
        (spectralProj_isStarProjection q _).isSelfAdjoint.star_eq] at h2
    have hcomm := (commute_spectralProj_spectralProj hpq ((m : ℝ) + 1)⁻¹
      ((N : ℝ) + 1)⁻¹).symm
    have hkey : specPair p q N * (spectralProj p ((m : ℝ) + 1)⁻¹ *
        spectralProj q ((k : ℝ) + 1)⁻¹) =
        spectralProj p ((m : ℝ) + 1)⁻¹ * spectralProj q ((k : ℝ) + 1)⁻¹ := by
      simp only [specPair, mul_assoc]
      rw [hcomm.left_comm, hb, ← mul_assoc, ha]
    rw [← hkey, ← mul_assoc, hy N, zero_mul]
  have hcolumn : ∀ m : ℕ, y * spectralProj p ((m : ℝ) + 1)⁻¹ = 0 := by
    intro m
    have h1 : (y * spectralProj p ((m : ℝ) + 1)⁻¹) * q = 0 :=
      mul_eq_zero_of_mul_spectralProj_eq_zero hq fun k => by
        rw [mul_assoc]; exact hstep m k
    have h2 := mul_ceil_eq_zero hq h1
    rwa [hcq, mul_one] at h2
  have h3 : y * p = 0 := mul_eq_zero_of_mul_spectralProj_eq_zero hp hcolumn
  have h4 := mul_ceil_eq_zero hp h3
  rwa [hcp, mul_one] at h4

/-- The corner step, specialised to the canonical sequence `Eₙ`. -/
theorem positive_quotients_specPair {p q : A} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p * q = q * p) (ϑ : MIUMap A A)
    (h : ∀ e : A, IsStarProjection e → ceil (p * e * p) = ceil (q * ϑ e * q))
    (n : ℕ) (hϑE : ϑ (specPair p q n) = specPair p q n) :
    0 ≤ specInv p ((n : ℝ) + 1)⁻¹ * q * specPair p q n ∧
      (specInv p ((n : ℝ) + 1)⁻¹ * q * specPair p q n) * (p * specPair p q n) =
        q * specPair p q n ∧
      (p * specPair p q n) * (specInv p ((n : ℝ) + 1)⁻¹ * specPair p q n) =
        specPair p q n ∧
    (∀ x : A, specPair p q n * x * specPair p q n = x →
        (specInv p ((n : ℝ) + 1)⁻¹ * q * specPair p q n) * x =
          x * (specInv p ((n : ℝ) + 1)⁻¹ * q * specPair p q n)) ∧
      (∀ x : A, specPair p q n * x * specPair p q n = x → ϑ x = x) := by
  set t : ℝ := ((n : ℝ) + 1)⁻¹ with htdef
  have ht : (0 : ℝ) < t := by rw [htdef]; positivity
  have hE : IsStarProjection (specPair p q n) := specPair_isStarProjection hpq n
  have cpE : Commute p (specPair p q n) := commute_specPair_left hpq n
  have cqE : Commute q (specPair p q n) := commute_specPair_right hpq n
  have cpu : Commute p (specInv p t) := specInv_comm p t p rfl
  have cqu : Commute q (specInv p t) := specInv_comm p t q hpq
  have cpv : Commute p (specInv q t) := specInv_comm q t p hpq.symm
  have cqv : Commute q (specInv q t) := specInv_comm q t q rfl
  have cua : Commute (specInv p t) (spectralProj p t) :=
    (specInv_comm p t _ (spectralProj_comm p t p rfl)).symm
  have cub : Commute (specInv p t) (spectralProj q t) :=
    (specInv_comm p t _ (spectralProj_comm q t p hpq.symm)).symm
  have cva : Commute (specInv q t) (spectralProj p t) :=
    (specInv_comm q t _ (spectralProj_comm p t q hpq)).symm
  have cvb : Commute (specInv q t) (spectralProj q t) :=
    (specInv_comm q t _ (spectralProj_comm q t q rfl)).symm
  have cuE : Commute (specInv p t) (specPair p q n) := by
    simp only [specPair, ← htdef]; exact Commute.mul_right cua cub
  have cvE : Commute (specInv q t) (specPair p q n) := by
    simp only [specPair, ← htdef]; exact Commute.mul_right cva cvb
  have cuv : Commute (specInv p t) (specInv q t) :=
    specInv_comm q t _ cqu.eq
  have hupE : specInv p t * p * specPair p q n = specPair p q n := by
    simp only [specPair, ← htdef, ← mul_assoc, specInv_mul_mul_spectralProj hp ht]
  have hvqE : specInv q t * q * specPair p q n = specPair p q n := by
    simp only [specPair, ← htdef, mul_assoc]
    rw [(show Commute q (spectralProj p t) from spectralProj_comm p t q hpq).left_comm,
      cva.left_comm,
      ← mul_assoc (specInv q t) q _, specInv_mul_mul_spectralProj hq ht]
  exact positive_quotients_corner hp hq (specInv_nonneg p ht) hE
    cpE cqE cpu cqu cuE cpv cuv hupE hvqE ϑ hϑE h

/-- A self-adjoint **central** `d` with `d·s ≥ 0` for a faithful positive
`s` is itself positive: `d⁻ d s = −(d⁻)²s` is both `≥ 0` and `≤ 0`, so
`(d⁻)²s = 0` and hence `d⁻ = 0`. -/
theorem nonneg_of_central_of_mul_nonneg {d s : A} (hs : 0 ≤ s) (hcs : ceil s = 1)
    (hdsa : IsSelfAdjoint d) (hcomm : ∀ a : A, d * a = a * d) (hds : 0 ≤ d * s) :
    0 ≤ d := by
  set g : A := cfc (fun r : ℝ => max (-r) 0) d with hgdef
  set f : A := cfc (fun r : ℝ => max r 0) d with hfdef
  have hg0 : (0 : A) ≤ g := cfc_nonneg fun r _ => le_max_right _ _
  have hf0 : (0 : A) ≤ f := cfc_nonneg fun r _ => le_max_right _ _
  have hfg : f - g = d := by
    rw [hfdef, hgdef, ← cfc_sub (fun r : ℝ => max r 0) (fun r : ℝ => max (-r) 0) d
      (by fun_prop) (by fun_prop)]
    nth_rewrite 2 [← cfc_id ℝ d]
    refine cfc_congr fun r _ => ?_
    rcases le_total 0 r with hr | hr
    · rw [max_eq_left hr, max_eq_right (by linarith : -r ≤ 0)]; simp
    · rw [max_eq_right hr, max_eq_left (by linarith : (0 : ℝ) ≤ -r)]; simp
  have hprod : f * g = 0 := by
    rw [hfdef, hgdef, ← cfc_mul (fun r : ℝ => max r 0) (fun r : ℝ => max (-r) 0) d
      (by fun_prop) (by fun_prop),
      show (0 : A) = cfc (fun _ : ℝ => (0 : ℝ)) d by simp]
    refine cfc_congr fun r _ => ?_
    rcases le_total 0 r with hr | hr
    · rw [max_eq_right (by linarith : -r ≤ 0), mul_zero]
    · rw [max_eq_right hr, zero_mul]
  have hgc : ∀ a : A, a * g = g * a := fun a =>
    (Commute.cfc_real (show Commute d a from hcomm a) _).symm
  have hdg : d * g = -(g * g) := by rw [← hfg, sub_mul, hprod, zero_sub]
  have hcgds : g * (d * s) = (d * s) * g := (hgc (d * s)).symm
  have h1 : (0 : A) ≤ g * (d * s) := Theses.A.CStar.sqrt_1 g (d * s) hg0 hds hcgds
  have h2 : g * (d * s) = -(g * g * s) := by
    rw [← mul_assoc, ← hgc d, hdg, neg_mul]
  have hgg0 : (0 : A) ≤ g * g := by
    have hst := star_mul_self_nonneg g
    rwa [(IsSelfAdjoint.of_nonneg hg0).star_eq] at hst
  have cgs : Commute g s := (hgc s).symm
  have hggs : (0 : A) ≤ g * g * s :=
    Theses.A.CStar.sqrt_1 (g * g) s hgg0 hs (cgs.mul_left cgs).eq
  have hz : g * g * s = 0 := by
    refine le_antisymm ?_ hggs
    exact neg_nonneg.mp (h2 ▸ h1)
  have hz2 : g * g = 0 := by
    have h4 := mul_ceil_eq_zero hs hz
    rwa [hcs, mul_one] at h4
  have hgzero : g = 0 := by
    have hstar : star g * g = 0 := by
      rwa [(IsSelfAdjoint.of_nonneg hg0).star_eq]
    exact (CStarRing.star_mul_self_eq_zero_iff g).mp hstar
  rw [← hfg, hgzero, sub_zero]
  exact hf0

/-! #### 104VII itself -/

/-- **104VII** (`positive-quotients-centrally-similar`, proc.tex:1556,
Proposition): positive `p, q` with `⌈p⌉ = ⌈q⌉ = 1` are centrally similar
when there is an miu-isomorphism `ϑ` with `⌈p e p⌉ = ⌈q ϑ(e) q⌉` for all
projections `e`; and in that case `ϑ = id`.

The author's proof (proc.tex:1558), with the descent from the corners done
differently — see the section preamble above and ERRATA **104VIII**.  Note
that `hbij` is **not used**: an miu-*map* with the stated property is
automatically the identity, so bijectivity comes out rather than going in.
The hypothesis is kept because the thesis states it. -/
theorem positive_quotients_centrally_similar (p q : A) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hcp : ceil p = 1) (hcq : ceil q = 1) (ϑ : MIUMap A A)
    (hbij : Function.Bijective ⇑ϑ)
    (h : ∀ e : A, IsStarProjection e →
      ceil (p * e * p) = ceil (q * ϑ e * q)) :
    CentrallySimilar p q ∧ ∀ a, ϑ a = a := by
  obtain ⟨hfix, hpq, hϑp⟩ := positive_quotients_step12 hp hq hcp hcq ϑ h
  have hpsa : IsSelfAdjoint p := IsSelfAdjoint.of_nonneg hp
  have hqsa : IsSelfAdjoint q := IsSelfAdjoint.of_nonneg hq
  set s : A := p + q with hsdef
  have hs : (0 : A) ≤ s := add_nonneg hp hq
  have hssa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg hs
  have hcs : ceil s = 1 := by
    have h1 : ceil p ≤ ceil s := ceil_mono hp (by rw [hsdef]; exact le_add_of_nonneg_right hq)
    rw [hcp] at h1
    exact le_antisymm (ceil_spec hs).1.le_one h1
  -- `d := p/(p+q)` exists by Douglas' lemma (**81V**.1), since `p² ≤ (p+q)²`
  have hsq : p * p ≤ s * s := by
    have h1 : (0 : A) ≤ p * q := Theses.A.CStar.sqrt_1 p q hp hq hpq
    have h2 : (0 : A) ≤ q * q := by
      have hst := star_mul_self_nonneg q
      rwa [hqsa.star_eq] at hst
    have hexp : s * s - p * p = p * q + (q * p + q * q) := by rw [hsdef]; noncomm_ring
    rw [← sub_nonneg, hexp, ← hpq]
    exact add_nonneg h1 (add_nonneg h1 h2)
  obtain ⟨d, -, hd⟩ := ((douglas_1 p s 1 zero_le_one).1).mpr (by
    simpa [hpsa.star_eq, hssa.star_eq] using hsq)
  -- `d` is the *unique* solution of `d·s = p`, hence commutes with `p` and `q`
  have huniq : ∀ c c' : A, c * s = c' * s → c = c' := by
    intro c c' hcc
    have h0 : (c - c') * s = 0 := by rw [sub_mul, hcc, sub_self]
    have h1 := mul_ceil_eq_zero hs h0
    rw [hcs, mul_one, sub_eq_zero] at h1
    exact h1
  have hdcomm : ∀ x : A, x * p = p * x → x * q = q * x → x * d = d * x := by
    intro x hxp hxq
    have hxs : x * s = s * x := by rw [hsdef, mul_add, add_mul, hxp, hxq]
    refine huniq _ _ ?_
    calc x * d * s = x * (d * s) := mul_assoc _ _ _
      _ = x * p := by rw [← hd]
      _ = p * x := hxp
      _ = d * s * x := by rw [← hd]
      _ = d * (s * x) := mul_assoc _ _ _
      _ = d * (x * s) := by rw [hxs]
      _ = d * x * s := (mul_assoc _ _ _).symm
  -- the increasing projections `Eₙ`
  have hEproj : ∀ n : ℕ, IsStarProjection (specPair p q n) := specPair_isStarProjection hpq
  have hEE : ∀ n : ℕ, specPair p q n * specPair p q n = specPair p q n :=
    fun n => (hEproj n).isIdempotentElem.eq
  have hϑE : ∀ n : ℕ, ϑ (specPair p q n) = specPair p q n := fun n =>
    (hfix _ (hEproj n) (commute_specPair_left hpq n).symm.eq).2
  -- nothing but `0` is killed by every `Eₙ` on both sides
  have hvanish : ∀ y : A, (∀ n : ℕ, specPair p q n * y * specPair p q n = 0) → y = 0 := by
    intro y hy
    have hmk : ∀ m k : ℕ, specPair p q m * y * specPair p q k = 0 := by
      intro m k
      have hm : specPair p q m * specPair p q (max m k) = specPair p q m :=
        specPair_mul_specPair hp hq hpq (le_max_left m k)
      have hk0 : specPair p q k * specPair p q (max m k) = specPair p q k :=
        specPair_mul_specPair hp hq hpq (le_max_right m k)
      have hk : specPair p q (max m k) * specPair p q k = specPair p q k := by
        have hst := congrArg star hk0
        rwa [star_mul, (hEproj _).isSelfAdjoint.star_eq,
          (hEproj _).isSelfAdjoint.star_eq] at hst
      have hexp : specPair p q m * (specPair p q (max m k) * y * specPair p q (max m k)) *
          specPair p q k
          = (specPair p q m * specPair p q (max m k)) * y *
            (specPair p q (max m k) * specPair p q k) := by simp only [mul_assoc]
      rw [hm, hk] at hexp
      rw [← hexp, hy (max m k), mul_zero, zero_mul]
    have hleft : ∀ m : ℕ, specPair p q m * y = 0 :=
      fun m => eq_zero_of_mul_specPair hp hq hcp hcq hpq (fun k => hmk m k)
    have hstar : star y = 0 := by
      refine eq_zero_of_mul_specPair hp hq hcp hcq hpq (fun m => ?_)
      have hst := congrArg star (hleft m)
      rwa [star_mul, star_zero, (hEproj m).isSelfAdjoint.star_eq] at hst
    exact star_eq_zero.mp hstar
  -- `d·Eₙ` is central in the corner `Eₙ𝒜Eₙ`
  have hdE : ∀ n : ℕ, ∀ x : A, specPair p q n * x * specPair p q n = x →
      (d * specPair p q n) * x = x * (d * specPair p q n) := by
    intro n x hx
    obtain ⟨hz0, hzP, hPU, hzc, -⟩ := positive_quotients_specPair hp hq hpq ϑ h n (hϑE n)
    set E : A := specPair p q n with hEdef
    set z : A := specInv p ((n : ℝ) + 1)⁻¹ * q * E with hzdef
    set U : A := specInv p ((n : ℝ) + 1)⁻¹ * E with hUdef
    have hEidem : E * E = E := hEE n
    have hEp : E * p = p * E := (commute_specPair_left hpq n).symm.eq
    have hEq : E * q = q * E := (commute_specPair_right hpq n).symm.eq
    have hEs : E * s = s * E := by rw [hsdef, mul_add, add_mul, hEp, hEq]
    have hEd : E * d = d * E := hdcomm E hEp hEq
    have hzE : z * E = z := by rw [hzdef, mul_assoc, hEidem]
    have hEx : E * x = x := by
      conv_lhs => rw [← hx]
      rw [← mul_assoc, ← mul_assoc, hEidem, hx]
    have hxE : x * E = x := by
      conv_lhs => rw [← hx]
      rw [mul_assoc (E * x) E E, hEidem, hx]
    have hsE : (E + z) * (p * E) = s * E := by
      rw [add_mul, hzP, hsdef, add_mul]
      congr 1
      calc E * (p * E) = E * p * E := (mul_assoc _ _ _).symm
        _ = p * E * E := by rw [hEp]
        _ = p * E := by rw [mul_assoc, hEidem]
    have hd1 : (d * E) * (s * E) = p * E := by
      calc (d * E) * (s * E) = d * (E * s) * E := by simp only [mul_assoc]
        _ = d * (s * E) * E := by rw [hEs]
        _ = (d * s) * (E * E) := by simp only [mul_assoc]
        _ = p * E := by rw [← hd, hEidem]
    have hd3 : (d * E * (E + z)) * E = E := by
      calc (d * E * (E + z)) * E = (d * E * (E + z)) * ((p * E) * U) := by rw [hPU]
        _ = (d * E) * ((E + z) * (p * E)) * U := by simp only [mul_assoc]
        _ = (d * E) * (s * E) * U := by rw [hsE]
        _ = (p * E) * U := by rw [hd1]
        _ = E := hPU
    have hd4 : d * E * (E + z) = E := by
      have hfold : (d * E * (E + z)) * E = d * E * (E + z) := by
        rw [mul_assoc, add_mul, hEidem, hzE]
      rw [← hfold, hd3]
    have hxz : x * z = z * x := (hzc x hx).symm
    have hcomm2 : x * (E + z) = (E + z) * x := by
      rw [mul_add, add_mul, hxE, hEx, hxz]
    set y : A := (d * E) * x - x * (d * E) with hydef
    have hy1 : y * (E + z) = 0 := by
      have hA : ((d * E) * x) * (E + z) = x := by
        calc ((d * E) * x) * (E + z) = (d * E) * (x * (E + z)) := by simp only [mul_assoc]
          _ = (d * E) * ((E + z) * x) := by rw [hcomm2]
          _ = (d * E * (E + z)) * x := by simp only [mul_assoc]
          _ = E * x := by rw [hd4]
          _ = x := hEx
      have hB : (x * (d * E)) * (E + z) = x := by
        rw [mul_assoc, hd4, hxE]
      rw [hydef, sub_mul, hA, hB, sub_self]
    have hEz0 : (0 : A) ≤ E + z := add_nonneg (hEproj n).nonneg hz0
    have hceilEz : ceil (E + z) = E := by
      refine le_antisymm ((ceil_le_iff hEz0 (hEproj n)).mpr ?_) ?_
      · rw [add_mul, hEidem, hzE]
      · have h1 : ceil E ≤ ceil (E + z) :=
          ceil_mono (hEproj n).nonneg (le_add_of_nonneg_right hz0)
        rwa [ceil_of_isStarProjection (hEproj n)] at h1
    have hy2 : y * E = 0 := by
      have hcz := mul_ceil_eq_zero hEz0 hy1
      rwa [hceilEz] at hcz
    have hy3 : y * E = y := by
      rw [hydef, sub_mul]
      congr 1
      · rw [mul_assoc (d * E) x E, hxE]
      · rw [mul_assoc x (d * E) E, mul_assoc d E E, hEidem]
    have hy0 : y = 0 := by rw [← hy3]; exact hy2
    exact sub_eq_zero.mp hy0
  -- `d` is central
  have hdc : ∀ a : A, d * a = a * d := by
    intro a
    refine sub_eq_zero.mp (hvanish (d * a - a * d) fun n => ?_)
    set E : A := specPair p q n with hEdef
    have hEidem : E * E = E := hEE n
    have hEd : E * d = d * E :=
      hdcomm E (commute_specPair_left hpq n).symm.eq (commute_specPair_right hpq n).symm.eq
    have hxcorner : E * (E * a * E) * E = E * a * E := by
      calc E * (E * a * E) * E = (E * E) * a * (E * E) := by simp only [mul_assoc]
        _ = E * a * E := by rw [hEidem]
    have hkey := hdE n (E * a * E) hxcorner
    have hleg1 : E * (d * a) * E = (d * E) * (E * a * E) := by
      calc E * (d * a) * E = E * d * a * E := by simp only [mul_assoc]
        _ = d * E * a * E := by rw [hEd]
        _ = d * (E * E) * a * E := by rw [hEidem]
        _ = (d * E) * (E * a * E) := by simp only [mul_assoc]
    have hleg2 : E * (a * d) * E = (E * a * E) * (d * E) := by
      calc E * (a * d) * E = E * a * d * (E * E) := by rw [hEidem]; simp only [mul_assoc]
        _ = E * a * (d * E) * E := by simp only [mul_assoc]
        _ = E * a * (E * d) * E := by rw [hEd]
        _ = (E * a * E) * (d * E) := by simp only [mul_assoc]
    calc E * (d * a - a * d) * E
        = (d * E) * (E * a * E) - (E * a * E) * (d * E) := by
          rw [mul_sub, sub_mul, hleg1, hleg2]
      _ = 0 := sub_eq_zero.mpr hkey
  -- `ϑ = id`
  have hϑid : ∀ a : A, ϑ a = a := by
    intro a
    refine sub_eq_zero.mp (hvanish (ϑ a - a) fun n => ?_)
    obtain ⟨-, -, -, -, hfixc⟩ := positive_quotients_specPair hp hq hpq ϑ h n (hϑE n)
    set E : A := specPair p q n with hEdef
    have hEidem : E * E = E := hEE n
    have hxcorner : E * (E * a * E) * E = E * a * E := by
      calc E * (E * a * E) * E = (E * E) * a * (E * E) := by simp only [mul_assoc]
        _ = E * a * E := by rw [hEidem]
    have h1 : ϑ (E * a * E) = E * a * E := hfixc _ hxcorner
    calc E * (ϑ a - a) * E = ϑ (E * a * E) - E * a * E := by
          rw [mul_sub, sub_mul]
          congr 1
          rw [map_mul, map_mul, hϑE n]
      _ = 0 := sub_eq_zero.mpr h1
  -- `d` is self-adjoint and positive, and so is `1 − d`
  have hdsa : IsSelfAdjoint d := by
    have hstarc : ∀ a : A, star d * a = a * star d := by
      intro a
      have hst := congrArg star (hdc (star a))
      rw [star_mul, star_mul, star_star] at hst
      exact hst.symm
    have h1 : star d * s = p := by
      have hst := congrArg star hd
      rw [hpsa.star_eq, star_mul, hssa.star_eq] at hst
      rw [← hstarc s] at hst
      exact hst.symm
    exact huniq (star d) d (h1.trans hd)
  have hd0 : (0 : A) ≤ d :=
    nonneg_of_central_of_mul_nonneg hs hcs hdsa hdc (by rw [← hd]; exact hp)
  have hqd : (1 - d) * s = q := by rw [sub_mul, one_mul, ← hd, hsdef]; abel
  have hc0 : (0 : A) ≤ 1 - d := by
    refine nonneg_of_central_of_mul_nonneg hs hcs ((IsSelfAdjoint.one A).sub hdsa)
      (fun a => by rw [sub_mul, mul_sub, one_mul, mul_one, hdc a]) ?_
    rw [hqd]; exact hq
  -- the carriers
  have hceil_of : ∀ c x : A, 0 ≤ c → 0 ≤ x → ceil x = 1 → IsSelfAdjoint c → c * s = x →
      ceil c = 1 := by
    intro c x hc0' hx0 hcx hcsa hcx'
    have hcc : ceil c * c = c := by
      have h1 := (ceil_spec hc0').2.1
      have h2 := congrArg star h1
      rwa [star_mul, (ceil_spec hc0').1.isSelfAdjoint.star_eq, hcsa.star_eq] at h2
    have hxc : x * ceil c = x := by
      have h1 : ceil c * x = x := by rw [← hcx', ← mul_assoc, hcc]
      have h2 := congrArg star h1
      rwa [star_mul, (IsSelfAdjoint.of_nonneg hx0).star_eq,
        (ceil_spec hc0').1.isSelfAdjoint.star_eq] at h2
    have hle := (ceil_le_iff hx0 (ceil_spec hc0').1).mpr hxc
    rw [hcx] at hle
    exact le_antisymm (ceil_spec hc0').1.le_one hle
  have hceild : ceil d = 1 := hceil_of d p hd0 hp hcp hdsa hd.symm
  have hceilc : ceil (1 - d) = 1 :=
    hceil_of (1 - d) q hc0 hq hcq ((IsSelfAdjoint.one A).sub hdsa) hqd
  refine ⟨⟨1 - d, d, fun m _ => ?_, fun m _ => (hdc m).symm, hc0, hd0, ?_, ?_, ?_⟩, hϑid⟩
  · rw [sub_mul, mul_sub, one_mul, mul_one, hdc m]
  · have hsum : d * p + d * q = p := by rw [← mul_add, ← hsdef, ← hd]
    rw [sub_mul, one_mul]
    exact (eq_sub_of_add_eq (by rw [add_comm]; exact hsum)).symm
  · rw [hcp, hceilc]
  · rw [hcq, hceild]

end Aux104VII

/-- **104IX** (`faithful-positive-map-uniqueness`, proc.tex:1628,
Proposition): a faithful ⋄-positive map `f : 𝒜 → 𝒜` is of the form
`f = √p(·)√p` where `p := f(1)`.

The author's proof (proc.tex:1631), transcribed.  `f`, being pure (a
composite `ξ∘ξ`) and faithful, is a filter, so `f = √p ϑ(·) √p` for an
ncp-isomorphism `ϑ` (**98II**.1 in the form `filter_unique`, against the
filter `√p(·)√p`); the task is `ϑ = id`.  Writing `f = ξ∘ξ` with `ξ`
⋄-self-adjoint, `⌈ξ⌉ = ⌈f⌉ = 1` (**103III**.2), so `ξ` is a filter too and
`ξ = √w α(·) √w` with `w := ξ(1)`, `⌈w⌉ = 1`.  Then `ξ^⋄ = ξ_⋄` (⋄-self-
adjointness), `ξ^⋄ = (√w(·)√w)^⋄ ∘ α^⋄` and `ξ_⋄ = α_⋄ ∘ (√w(·)√w)_⋄`
(**101VIII**.1), while `(√w(·)√w)_⋄ = (√w(·)√w)^⋄` (**101VII**.1) and
`α_⋄ = α'^⋄` (**101VII**.2, an ncpu-isomorphism is contraposed to its
inverse); so `α^⋄ ∘ D ∘ α^⋄ = D` for `D := (√w(·)√w)^⋄`, whence
`f^⋄ = D∘α^⋄∘D∘α^⋄ = D∘D = (w(·)w)^⋄`, i.e.
`⌈√p ϑ(e) √p⌉ = ⌈w e w⌉` for every projection `e`.  **104VII** at `w`,
`√p` (both faithful) now gives `ϑ = id`.

This proof rests on **104VII**, and on nothing else; since session 91
104VII is proved, so this one is axiom-clean. -/
theorem faithful_positive_map_uniqueness [VonNeumannAlgebra A]
    (f : NCPMap A A) (hf : IsDiamondPositive f)
    (hfaith : ncpCarrier f = 1) :
    ∀ a : A, f a = CFC.sqrt (f 1) * a * CFC.sqrt (f 1) := by
  obtain ⟨ξ, hξ, hfξ⟩ := hf
  have hp : (0 : A) ≤ f 1 := ncpMap_nonneg f zero_le_one
  have hfsa : IsDiamondSelfAdjoint f := purely_positive_basic_3 f ⟨ξ, hξ, hfξ⟩
  have hcp : ceil (f 1) = 1 := by rw [← purely_positive_basic_1 f hfsa]; exact hfaith
  have hcsp : ceil (CFC.sqrt (f 1)) = 1 := by
    have hs : CFC.sqrt (f 1) * ceil (CFC.sqrt (f 1)) = CFC.sqrt (f 1) :=
      (ceil_spec (CFC.sqrt_nonneg (f 1))).2.1
    have hpe : f 1 * ceil (CFC.sqrt (f 1)) = f 1 := by
      calc f 1 * ceil (CFC.sqrt (f 1))
          = CFC.sqrt (f 1) * (CFC.sqrt (f 1) * ceil (CFC.sqrt (f 1))) := by
            rw [← mul_assoc, CFC.sqrt_mul_sqrt_self (f 1) hp]
        _ = f 1 := by rw [hs, CFC.sqrt_mul_sqrt_self (f 1) hp]
    have hle : ceil (f 1) ≤ ceil (CFC.sqrt (f 1)) :=
      (ceil_le_iff hp (isStarProjection_ceil _)).mpr hpe
    rw [hcp] at hle
    exact le_antisymm (isStarProjection_ceil _).le_one hle
  -- the standard filter of `x`, in the form `√x(·)√x : 𝒜 → 𝒜`
  have hadOne : ∀ x : A, 0 ≤ x → (adSelf (CFC.sqrt x) 1 : A) = x := by
    intro x hx
    rw [adSelf_apply, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq,
      mul_one, CFC.sqrt_mul_sqrt_self x hx]
  have hadFilter : ∀ x : A, 0 ≤ x → ceil x = 1 → IsFilter (adSelf (CFC.sqrt x)) := by
    intro x hx hcx
    refine special_pure_maps_1 _ (isPure_adSelf _) ?_
    rw [purely_positive_basic_1 _
      (purely_positive_examples_1 _ (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x))),
      hadOne x hx, hcx]
  -- `f` is pure and faithful, hence a filter, hence `f = √p ϑ(·) √p`
  have hfpure : IsPure f := by rw [hfξ]; exact IsPure.comp hξ.1 hξ.1
  have hffilter : IsFilter f := special_pure_maps_1 f hfpure hfaith
  obtain ⟨ϑ, hϑ, hϑ1, ϑ', hϑ'ϑ, hϑϑ'⟩ :=
    filter_unique f hffilter (adSelf (CFC.sqrt (f 1))) (hadFilter _ hp hcp)
      (hadOne _ hp).symm
  have hfform : ∀ x : A, (f x : A) = CFC.sqrt (f 1) * ϑ x * CFC.sqrt (f 1) :=
    fun x => by
      rw [hϑ x, adSelf_apply,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (f 1))).star_eq]
  -- `ξ` is pure and faithful too, hence a filter, hence `ξ = √w α(·) √w`
  have hcξ : ncpCarrier ξ = 1 := by
    rw [← (purely_positive_basic_2 ξ hξ).2, ← hfξ]; exact hfaith
  have hw : (0 : A) ≤ ξ 1 := ncpMap_nonneg ξ zero_le_one
  have hcw : ceil (ξ 1) = 1 := by rw [← purely_positive_basic_1 ξ hξ]; exact hcξ
  have hξfilter : IsFilter ξ := special_pure_maps_1 ξ hξ.1 hcξ
  obtain ⟨α, hα, hα1, α', hα'α, hαα'⟩ :=
    filter_unique ξ hξfilter (adSelf (CFC.sqrt (ξ 1))) (hadFilter _ hw hcw)
      (hadOne _ hw).symm
  have hξeq : ξ = ncpComp (adSelf (CFC.sqrt (ξ 1))) α :=
    DFunLike.ext _ _ fun x => by rw [ncpComp_apply, ← hα x]
  -- `√w(·)√w` is ⋄-self-adjoint
  have hstdcon : Contraposed (adSelf (CFC.sqrt (ξ 1))) (adSelf (CFC.sqrt (ξ 1))) := by
    have h := equivalent_examples_1 (CFC.sqrt (ξ 1))
    rwa [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (ξ 1))).star_eq] at h
  have hstd : ∀ t : A, IsStarProjection t →
      diamondUp (adSelf (CFC.sqrt (ξ 1))) t
        = diamondDown (adSelf (CFC.sqrt (ξ 1))) t :=
    (contraposed_iff_diamond _ _).mpr hstdcon
  -- `α` is contraposed to its inverse
  have hα'1 : (α' 1 : A) = 1 := by have h := hα'α 1; rwa [hα1] at h
  have hαcon : Contraposed α' α := equivalent_examples_2 α' α hαα' hα'α hα'1
  have hαdown : ∀ t : A, IsStarProjection t →
      diamondUp α' t = diamondDown α t :=
    (contraposed_iff_diamond α' α).mpr hαcon
  -- `α^⋄` and `α'^⋄` are mutually inverse on projections
  have hαid : ncpComp α α' = ncpId A := DFunLike.ext _ _ fun y => by
    rw [ncpComp_apply, hαα', ncpId_apply]
  have hαinv : ∀ e : A, IsStarProjection e → diamondUp α (diamondUp α' e) = e := by
    intro e he
    have h := (diamond_composition_1 α' α).1 e he
    rw [hαid] at h
    rw [← h]
    show ceil (ncpId A e) = e
    rw [ncpId_apply, ceil_of_isStarProjection he]
  -- the key identity `α^⋄ ∘ D ∘ α^⋄ = D`, where `D = (√w(·)√w)^⋄`
  have hξup : ∀ x : A, IsStarProjection x →
      diamondUp ξ x = diamondUp (adSelf (CFC.sqrt (ξ 1))) (diamondUp α x) := by
    intro x hx
    conv_lhs => rw [hξeq]
    exact (diamond_composition_1 α (adSelf (CFC.sqrt (ξ 1)))).1 x hx
  have hkey : ∀ e : A, IsStarProjection e →
      diamondUp (adSelf (CFC.sqrt (ξ 1))) (diamondUp α e)
        = diamondUp α' (diamondUp (adSelf (CFC.sqrt (ξ 1))) e) := by
    intro e he
    have h2 : diamondDown ξ e
        = diamondDown α (diamondDown (adSelf (CFC.sqrt (ξ 1))) e) := by
      conv_lhs => rw [hξeq]
      exact (diamond_composition_1 α (adSelf (CFC.sqrt (ξ 1)))).2 e he
    have h3 : diamondUp ξ e = diamondDown ξ e :=
      (contraposed_iff_diamond ξ ξ).mpr hξ.2 e he
    rw [← hξup e he, h3, h2, ← hstd e he,
      hαdown _ (isStarProjection_diamondUp (adSelf (CFC.sqrt (ξ 1))) e)]
  have hkey2 : ∀ e : A, IsStarProjection e →
      diamondUp α (diamondUp (adSelf (CFC.sqrt (ξ 1))) (diamondUp α e))
        = diamondUp (adSelf (CFC.sqrt (ξ 1))) e := by
    intro e he
    rw [hkey e he, hαinv _ (isStarProjection_diamondUp (adSelf (CFC.sqrt (ξ 1))) e)]
  -- hence `f^⋄(e) = ⌈w e w⌉`
  have hdiam : ∀ e : A, IsStarProjection e →
      ceil (f e) = ceil (ξ 1 * e * ξ 1) := by
    intro e he
    have hff : diamondUp f e = diamondUp ξ (diamondUp ξ e) := by
      conv_lhs => rw [hfξ]
      exact (diamond_composition_1 ξ ξ).1 e he
    have hstep : diamondUp f e
        = diamondUp (adSelf (CFC.sqrt (ξ 1)))
            (diamondUp (adSelf (CFC.sqrt (ξ 1))) e) := by
      rw [hff, hξup _ (isStarProjection_diamondUp ξ e), hξup e he, hkey2 e he]
    have hdd : diamondUp (adSelf (CFC.sqrt (ξ 1)))
        (diamondUp (adSelf (CFC.sqrt (ξ 1))) e) = ceil (ξ 1 * e * ξ 1) := by
      have h := (diamond_composition_1 (adSelf (CFC.sqrt (ξ 1)))
        (adSelf (CFC.sqrt (ξ 1)))).1 e he
      rw [← h]
      show ceil (ncpComp (adSelf (CFC.sqrt (ξ 1))) (adSelf (CFC.sqrt (ξ 1))) e) = _
      rw [ncpComp_apply, adSelf_apply, adSelf_apply,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (ξ 1))).star_eq]
      congr 1
      calc CFC.sqrt (ξ 1) * (CFC.sqrt (ξ 1) * e * CFC.sqrt (ξ 1)) * CFC.sqrt (ξ 1)
          = (CFC.sqrt (ξ 1) * CFC.sqrt (ξ 1)) * e
              * (CFC.sqrt (ξ 1) * CFC.sqrt (ξ 1)) := by noncomm_ring
        _ = ξ 1 * e * ξ 1 := by rw [CFC.sqrt_mul_sqrt_self (ξ 1) hw]
    rw [← hdd, ← hstep]
    rfl
  -- `ϑ` is an miu-isomorphism
  have hϑ'1 : (ϑ' 1 : A) = 1 := by have h := hϑ'ϑ 1; rwa [hϑ1] at h
  have hiso := iso (⟨ϑ, le_of_eq hϑ1⟩ : NCPSUMap A A)
    (⟨ϑ', le_of_eq hϑ'1⟩ : NCPSUMap A A) hϑ'ϑ hϑϑ'
  let Θ : MIUMap A A :=
    { toFun := ⇑ϑ
      map_one' := hϑ1
      map_mul' := hiso.2.1
      map_zero' := map_zero ϑ.toCompletelyPositiveMap.toLinearMap
      map_add' := map_add ϑ.toCompletelyPositiveMap.toLinearMap
      commutes' := fun r => by
        have hsm : (ϑ (r • (1 : A)) : A) = r • ϑ 1 :=
          map_smul ϑ.toCompletelyPositiveMap.toLinearMap r 1
        rw [Algebra.algebraMap_eq_smul_one, hsm, hϑ1]
      map_star' := hiso.2.2 }
  have hΘ : ∀ a : A, (Θ a : A) = ϑ a := fun _ => rfl
  have hbij : Function.Bijective ⇑Θ :=
    Function.bijective_iff_has_inverse.mpr ⟨⇑ϑ', hϑ'ϑ, hϑϑ'⟩
  have hmain := positive_quotients_centrally_similar (ξ 1) (CFC.sqrt (f 1))
    hw (CFC.sqrt_nonneg (f 1)) hcw hcsp Θ hbij (fun e he => by
      rw [hΘ, ← hfform e]; exact (hdiam e he).symm)
  intro a
  have hid : (ϑ a : A) = a := hmain.2 a
  rw [hfform a, hid]


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
      g = chevron f := by
  -- `⟨f⟩(π_{⌈f⌉}a) = ⌈f(1)⌉f(⌈f⌉a⌈f⌉)⌈f(1)⌉ = ⌈f(1)⌉f(a)⌈f(1)⌉ = f(a)`, by
  -- 63VI and `ceilOne_conj`; uniqueness because `π_{⌈f⌉}` is surjective
  have hch : ∀ x : Corner A (ncpCarrier f),
      (chevron f x).val = ceil (f 1) * f x.val * ceil (f 1) :=
    (exists_chevron f).choose_spec
  have hcarr : carrier (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' = ncpCarrier f := rfl
  have hfund : ∀ a : A, (f a : B) = f (ncpCarrier f * a * ncpCarrier f) := by
    intro a
    have h := (carrier_fundamental
      (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' a).2.2
    rwa [hcarr] at h
  have hmain : ∀ a : A,
      f a = (chevron f ((cornerProjMap (ncpCarrier f)).toNCPMap a)).val := by
    intro a
    rw [hch, cornerProjMap_apply, ← hfund, ceilOne_conj]
  refine ⟨hmain, fun g hg => ?_⟩
  refine DFunLike.ext _ _ fun b => ?_
  have hsurj : (cornerProjMap (ncpCarrier f)).toNCPMap b.val = b :=
    Corner.val_injective (by rw [cornerProjMap_apply]; exact b.property)
  refine Corner.val_injective ?_
  calc (g b).val = (g ((cornerProjMap (ncpCarrier f)).toNCPMap b.val)).val := by
        rw [hsurj]
    _ = f b.val := (hg _).symm
    _ = (chevron f ((cornerProjMap (ncpCarrier f)).toNCPMap b.val)).val := hmain _
    _ = (chevron f b).val := by rw [hsurj]

/-- **105III** (`chevron-f-basic`, proc.tex:1717, Exercise), parts 1–2:
`⟨f⟩ = π_{⌈f(1)⌉} ∘ f ∘ c_{⌈f⌉}` (the defining formula of `chevron`) and
`⟨f⟩ = π_{⌈f(1)⌉} ∘ c_{f(1)} ∘ [f]`, i.e.
`⟨f⟩(a) = √f(1) [f](a) √f(1)`. -/
theorem chevron_f_basic_12 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (a : Corner A (ncpCarrier f)) :
    (chevron f a).val = ceil (f 1) * f a.val * ceil (f 1) ∧
      (chevron f a).val =
        CFC.sqrt (f 1) * (sqBracket f a).val * CFC.sqrt (f 1) := by
  -- Part 1 is the defining formula of `chevron`; part 2 is the square of
  -- **98IX** at `a ∈ ⌈f⌉𝒜⌈f⌉` (where `π_{⌈f⌉}a = a`), together with
  -- `⌈f(1)⌉f(x)⌈f(1)⌉ = f(x)`.
  have hch : (chevron f a).val = ceil (f 1) * f a.val * ceil (f 1) :=
    (exists_chevron f).choose_spec a
  refine ⟨hch, ?_⟩
  have hsurj : (cornerProjMap (ncpCarrier f)).toNCPMap a.val = a :=
    Corner.val_injective (by rw [cornerProjMap_apply]; exact a.property)
  have h := (square_f f).1 a.val
  rw [hsurj, stdFilter_apply] at h
  rw [hch, ceilOne_conj, h]

/-- **105III** (`chevron-f-basic`, proc.tex:1717, Exercise), part 3:
`⟨f⟩` is faithful and `⟨f⟩(1) = f(1)`. -/
theorem chevron_f_basic_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    ncpCarrier (chevron f) = 1 ∧ (chevron f 1).val = f 1 := by
  -- faithfulness: if `⟨f⟩(1-q) = 0` then `f(⌈f⌉ - q) = 0` (by `ceilOne_conj`),
  -- so `⌈f⌉ ≤ q + ⌈f⌉^⊥`, and multiplying by `⌈f⌉` gives `⌈f⌉ = q`
  have hch : ∀ x : Corner A (ncpCarrier f),
      (chevron f x).val = ceil (f 1) * f x.val * ceil (f 1) :=
    (exists_chevron f).choose_spec
  have hcarr : carrier (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' = ncpCarrier f := rfl
  have hfund : ∀ a : A, (f a : B) = f (ncpCarrier f * a * ncpCarrier f) := by
    intro a
    have h := (carrier_fundamental
      (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' a).2.2
    rwa [hcarr] at h
  have he : IsStarProjection (ncpCarrier f) := isStarProjection_ncpCarrier f
  have hfspec : IsStarProjection (ncpCarrier f) ∧ f (1 - ncpCarrier f) = 0 ∧
      ∀ r : A, IsStarProjection r → f (1 - r) = 0 → ncpCarrier f ≤ r :=
    (exists_ncpCarrier f).choose_spec.1
  constructor
  · have hqspec : IsStarProjection (ncpCarrier (chevron f)) ∧
        chevron f (1 - ncpCarrier (chevron f)) = 0 ∧
        ∀ r, IsStarProjection r → chevron f (1 - r) = 0 →
          ncpCarrier (chevron f) ≤ r :=
      (exists_ncpCarrier (chevron f)).choose_spec.1
    set q := ncpCarrier (chevron f) with hqdef
    have hqproj : IsStarProjection q := hqspec.1
    have hqv : IsStarProjection q.val :=
      ⟨congrArg Corner.val hqproj.isIdempotentElem.eq,
        congrArg Corner.val hqproj.isSelfAdjoint.star_eq⟩
    have hval : ceil (f 1) * f (ncpCarrier f - q.val) * ceil (f 1) = 0 := by
      have h := congrArg Corner.val hqspec.2.1
      rw [hch] at h
      simpa using h
    have hfz : (f (ncpCarrier f - q.val) : B) = 0 := by
      rw [← ceilOne_conj f (ncpCarrier f - q.val), hval]
    set s : A := q.val + (1 - ncpCarrier f) with hsdef
    have hqe : q.val * ncpCarrier f = q.val := Corner.mul_right q
    have heq : ncpCarrier f * q.val = q.val := Corner.mul_left q
    have hsproj : IsStarProjection s := by
      constructor
      · change s * s = s
        rw [hsdef]
        calc (q.val + (1 - ncpCarrier f)) * (q.val + (1 - ncpCarrier f))
            = q.val * q.val + (q.val - q.val * ncpCarrier f)
              + ((1 - ncpCarrier f) * q.val)
              + (1 - ncpCarrier f) * (1 - ncpCarrier f) := by noncomm_ring
          _ = q.val + (1 - ncpCarrier f) := by
              rw [hqv.isIdempotentElem.eq, hqe, sub_self,
                he.one_sub.isIdempotentElem.eq, sub_mul, one_mul, heq, sub_self]
              abel
      · change star s = s
        rw [hsdef, star_add, hqv.isSelfAdjoint.star_eq,
          he.one_sub.isSelfAdjoint.star_eq]
    have hles : ncpCarrier f ≤ s := by
      refine hfspec.2.2 s hsproj ?_
      rw [show (1 : A) - s = ncpCarrier f - q.val by rw [hsdef]; abel]
      exact hfz
    have hes : ncpCarrier f * s = ncpCarrier f :=
      ((projection_below_effect s (ncpCarrier f)
        ⟨hsproj.nonneg, hsproj.le_one⟩ he).out 0 7).mp hles
    refine (Corner.val_injective ?_).symm
    rw [Corner.val_one]
    rw [hsdef] at hes
    calc ncpCarrier f = ncpCarrier f * (q.val + (1 - ncpCarrier f)) := hes.symm
      _ = ncpCarrier f * q.val + (ncpCarrier f - ncpCarrier f * ncpCarrier f) := by
          noncomm_ring
      _ = q.val := by rw [heq, he.isIdempotentElem.eq, sub_self, add_zero]
  · have h1 : (f (ncpCarrier f) : B) = f 1 := by
      conv_rhs => rw [hfund 1]
      rw [mul_one, he.isIdempotentElem.eq]
    rw [hch, Corner.val_one, h1, ceilOne_conj]

/-- **105III** (`chevron-f-basic`, proc.tex:1717, Exercise), part 4: if
`f` is pure then `⟨f⟩` is pure, and hence a filter. -/
theorem chevron_f_basic_4 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (hf : IsPure f) :
    IsPure (chevron f) ∧ IsFilter (chevron f) := by
  -- The exercise's own route: by part 2, `⟨f⟩ = π_{⌈f(1)⌉} ∘ c_{f(1)} ∘ [f]`;
  -- `[f]` is an ncpu-isomorphism by **100III**, hence a filter, so `⟨f⟩` is
  -- (corner) ∘ (filter) ∘ (filter) and therefore pure.  Purity together with
  -- faithfulness (part 3) makes it a filter by **100VII**.1.
  have hp : (0 : B) ≤ f 1 := ncpMap_nonneg f zero_le_one
  have hce : IsStarProjection (ceil (f 1)) := isStarProjection_ceil (f 1)
  obtain ⟨-, h, hhf, hfh⟩ := ((pure_fundamental f).out 0 2).mp hf
  have hcs : ceil (f 1) * CFC.sqrt (f 1) = CFC.sqrt (f 1) := by
    rw [ceil_eq_rangeProj_sqrt hp]
    exact (ceill_basic_2 (CFC.sqrt (f 1))).1.2
  have hsc : CFC.sqrt (f 1) * ceil (f 1) = CFC.sqrt (f 1) := by
    have h2 := congrArg star hcs
    rwa [star_mul, hce.isSelfAdjoint.star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (f 1))).star_eq] at h2
  have hfac : chevron f = ncpComp (cornerProjMap (ceil (f 1))).toNCPMap
      (ncpComp (stdFilter (f 1)) (sqBracket f)) := by
    refine DFunLike.ext _ _ fun a => Corner.val_injective ?_
    rw [ncpComp_apply, ncpComp_apply, cornerProjMap_apply, stdFilter_apply,
      (chevron_f_basic_12 f a).2]
    calc CFC.sqrt (f 1) * (sqBracket f a).val * CFC.sqrt (f 1)
        = (ceil (f 1) * CFC.sqrt (f 1)) * (sqBracket f a).val
            * (CFC.sqrt (f 1) * ceil (f 1)) := by rw [hcs, hsc]
      _ = ceil (f 1) * (CFC.sqrt (f 1) * (sqBracket f a).val * CFC.sqrt (f 1))
            * ceil (f 1) := by noncomm_ring
  have hpure : IsPure (chevron f) := by
    rw [hfac]
    refine IsPure.comp (IsPure.corner ?_)
      (IsPure.comp (IsPure.filter (isFilter_stdFilter (f 1) hp))
        (IsPure.filter (isFilter_of_iso (sqBracket f) h hhf hfh)))
    exact ⟨(cornerProjMap (ceil (f 1))).unital', ceil (f 1),
      ⟨hce.nonneg, hce.le_one⟩,
      isCornerOf_cornerProjMap (ceil (f 1)) (ceil (f 1)) hce
        (floor_of_isStarProjection hce)⟩
  exact ⟨hpure, special_pure_maps_1 _ hpure (chevron_f_basic_3 f).1⟩

/-- Auxiliary for **105IV**: for projections `p, t ≤ u` the ambient
orthocomplement and the one of the corner `u𝒜u` cut out the same
condition: `p ≤ 1 − t` iff `p ≤ u − t`. -/
theorem le_sub_iff_le_one_sub [VonNeumannAlgebra A] {p t u : A}
    (hp : IsStarProjection p) (ht : IsStarProjection t)
    (hu : IsStarProjection u) (hpu : p ≤ u) (htu : t ≤ u) :
    p ≤ 1 - t ↔ p ≤ u - t := by
  have hut : u * t = t :=
    ((projection_below_effect u t ⟨hu.nonneg, hu.le_one⟩ ht).out 0 6).mp htu
  have htu' : t * u = t :=
    ((projection_below_effect u t ⟨hu.nonneg, hu.le_one⟩ ht).out 0 7).mp htu
  have hpu' : p * u = p :=
    ((projection_below_effect u p ⟨hu.nonneg, hu.le_one⟩ hp).out 0 7).mp hpu
  have hsub : IsStarProjection (u - t) := by
    refine ⟨?_, ?_⟩
    · show (u - t) * (u - t) = u - t
      calc (u - t) * (u - t)
          = u * u - u * t - t * u + t * t := by noncomm_ring
        _ = u - t := by
            rw [hu.isIdempotentElem.eq, ht.isIdempotentElem.eq, hut, htu']
            abel
    · show star (u - t) = u - t
      rw [star_sub, hu.isSelfAdjoint.star_eq, ht.isSelfAdjoint.star_eq]
  constructor
  · intro h
    have hpt : p * (1 - t) = p :=
      ((projection_below_effect (1 - t) p
        ⟨ht.one_sub.nonneg, ht.one_sub.le_one⟩ hp).out 0 7).mp h
    have hpt0 : p * t = 0 := by
      rw [mul_sub, mul_one] at hpt
      exact sub_eq_self.mp hpt
    refine ((projection_below_effect (u - t) p
      ⟨hsub.nonneg, hsub.le_one⟩ hp).out 7 0).mp ?_
    calc p * (u - t) = p * u - p * t := by noncomm_ring
      _ = p := by rw [hpu', hpt0, sub_zero]
  · intro h
    exact h.trans (sub_le_sub_right hu.le_one t)

/-- **105IV**.1 with the index carried as a parameter (so part 3 can use it
at `u = ⌈h(1)⌉` for its square root `h`): for ⋄-self-adjoint `f` and
`u = ⌈f(1)⌉` the map `u f(·) u : u𝒜u → u𝒜u` is ⋄-self-adjoint.

Purity is `π_u ∘ f ∘ (u𝒜u ↪ 𝒜)` — a corner after a pure map after a filter
(`isFilter_cornerIncl`).  Contraposition transports because ceilings in the
corner are ambient ceilings (`corner_ceil_val`), because `⌈f(1)⌉f(x)⌈f(1)⌉
= f(x)`, and because `p ≤ 1 − t` and `p ≤ u − t` agree below `u`. -/
private theorem isDiamondSelfAdjoint_cornerMap [VonNeumannAlgebra A]
    (f : NCPMap A A) (hf : IsDiamondSelfAdjoint f) (u : A)
    [Fact (IsStarProjection u)] (hu : u = ceil (f 1)) :
    ∃ g : NCPMap (Corner A u) (Corner A u),
      (∀ a : Corner A u, (g a).val = u * f a.val * u) ∧
      IsDiamondSelfAdjoint g := by
  have huproj : IsStarProjection u := Corner.proj u
  -- the two consequences of `u = ⌈f(1)⌉` that are used, stated on elements
  -- of `𝒜` (rewriting `u` itself is impossible: it indexes a dependent type)
  have hconj : ∀ x : A, u * f x * u = f x := by
    intro x
    rw [hu]
    exact ceilOne_conj f x
  have hceilu : ∀ x : A, 0 ≤ x → ceil (f x) ≤ u := by
    intro x hx
    rw [hu]
    exact ceil_le_ceil_one f x hx
  refine ⟨ncpComp (cornerProjMap u).toNCPMap
    (ncpComp f (cornerIncl u).toNCPMap), fun a => ?_, ?_, ?_⟩
  · rw [ncpComp_apply, cornerProjMap_apply, ncpComp_apply, cornerIncl_apply]
  · -- purity: a corner after a pure map after a filter
    exact IsPure.comp (IsPure.corner ⟨(cornerProjMap u).unital', u,
        ⟨huproj.nonneg, huproj.le_one⟩,
        isCornerOf_cornerProjMap u u huproj (floor_of_isStarProjection huproj)⟩)
      (IsPure.comp hf.1 (IsPure.filter (isFilter_cornerIncl u)))
  · -- contraposition
    set g : NCPMap (Corner A u) (Corner A u) := ncpComp (cornerProjMap u).toNCPMap
      (ncpComp f (cornerIncl u).toNCPMap) with hgdef
    have hgval : ∀ a : Corner A u, (g a).val = u * f a.val * u := by
      intro a
      rw [hgdef, ncpComp_apply, cornerProjMap_apply, ncpComp_apply,
        cornerIncl_apply]
    have hproj_val : ∀ s : Corner A u, IsStarProjection s →
        IsStarProjection s.val := by
      intro s hs
      exact ⟨congrArg Corner.val hs.isIdempotentElem.eq,
        congrArg Corner.val hs.isSelfAdjoint.star_eq⟩
    have hvalceil : ∀ s : Corner A u, IsStarProjection s →
        (diamondUp g s).val = ceil (f s.val) := by
      intro s hs
      have hgs : (0 : Corner A u) ≤ g s := ncpMap_nonneg g hs.nonneg
      show (ceil (g s)).val = ceil (f s.val)
      rw [corner_ceil_val (g s) hgs, hgval s, hconj s.val]
    have hiff : ∀ s t : Corner A u, IsStarProjection s → IsStarProjection t →
        ((diamondUp g s ≤ 1 - t) ↔ ceil (f s.val) ≤ 1 - t.val) := by
      intro s t hs ht
      have hs0 : (0 : A) ≤ s.val := hs.nonneg
      have hsu : ceil (f s.val) ≤ u := hceilu s.val hs0
      have htu : t.val ≤ u := by
        have h : t ≤ (1 : Corner A u) := ht.le_one
        exact h
      have hmid : (diamondUp g s ≤ 1 - t) ↔ ceil (f s.val) ≤ u - t.val := by
        constructor
        · intro h
          have h2 : (diamondUp g s).val ≤ ((1 : Corner A u) - t).val := h
          rwa [hvalceil s hs, Corner.val_sub, Corner.val_one] at h2
        · intro h
          show (diamondUp g s).val ≤ ((1 : Corner A u) - t).val
          rwa [hvalceil s hs, Corner.val_sub, Corner.val_one]
      exact hmid.trans (le_sub_iff_le_one_sub (isStarProjection_ceil _)
        (hproj_val t ht) huproj hsu htu).symm
    intro s t hs ht
    rw [hiff s t hs ht, hiff t s ht hs]
    exact hf.2 s.val t.val (hproj_val s hs) (hproj_val t ht)

/-- **105IV** (`chevron-f-purely-positive`, proc.tex:1742, Exercise),
part 1: for ⋄-self-adjoint `f : 𝒜 → 𝒜` (so `⌈f⌉ = ⌈f(1)⌉` and `⟨f⟩` can
be regarded as a map `⌈f⌉𝒜⌈f⌉ → ⌈f⌉𝒜⌈f⌉`), `⟨f⟩` is ⋄-self-adjoint.
(Rendered on the corner `⌈f(1)⌉𝒜⌈f(1)⌉` via the chevron formula.) -/
theorem chevron_f_purely_positive_1 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) :
    ∃ g : NCPMap (Corner A (ceil (f 1))) (Corner A (ceil (f 1))),
      (∀ a : Corner A (ceil (f 1)),
        (g a).val = ceil (f 1) * f a.val * ceil (f 1)) ∧
      IsDiamondSelfAdjoint g :=
  isDiamondSelfAdjoint_cornerMap f hf (ceil (f 1)) rfl

/-- **105IV** (`chevron-f-purely-positive`, proc.tex:1742, Exercise),
part 2: for ⋄-self-adjoint `f`, `⟨f²⟩ = ⟨f⟩²` — rendered elementwise: for
`a` in the corner `⌈f(1)⌉𝒜⌈f(1)⌉`,
`⌈f(1)⌉ f(f(a)) ⌈f(1)⌉ = ⌈f(1)⌉ f(⌈f(1)⌉ f(a) ⌈f(1)⌉) ⌈f(1)⌉`.

In this rendering the hypothesis `ha` is **not needed** (the
unused-variable warning is left in place as the evidence), and ⋄-self-
adjointness is used only through **103III**.1 `purely_positive_basic_1`
(`⌈f⌉ = ⌈f(1)⌉`): the identity is then **63VI** `carrier_fundamental`,
`f(x) = f(⌈f⌉·x·⌈f⌉)`, at `x = f(a)`. -/
theorem chevron_f_purely_positive_2 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondSelfAdjoint f) (a : A)
    (ha : a ∈ cornerSet A (ceil (f 1))) :
    ceil (f 1) * f (f a) * ceil (f 1) =
      ceil (f 1) * f (ceil (f 1) * f a * ceil (f 1)) * ceil (f 1) := by
  have hcarr : carrier (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' = ncpCarrier f := rfl
  have hfund : ∀ x : A, (f x : A) = f (ncpCarrier f * x * ncpCarrier f) := by
    intro x
    have h := (carrier_fundamental
      (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' x).2.2
    rwa [hcarr] at h
  have hce : ncpCarrier f = ceil (f 1) := purely_positive_basic_1 f hf
  rw [← hce]
  conv_rhs => rw [← hfund (f a)]

/-- **105IV** (`chevron-f-purely-positive`, proc.tex:1742, Exercise),
part 3: if `f` is ⋄-positive then `⟨f⟩` is ⋄-positive (rendered on the
corner `⌈f(1)⌉𝒜⌈f(1)⌉` as in part 1). -/
theorem chevron_f_purely_positive_3 [VonNeumannAlgebra A] (f : NCPMap A A)
    (hf : IsDiamondPositive f) :
    ∃ g : NCPMap (Corner A (ceil (f 1))) (Corner A (ceil (f 1))),
      (∀ a : Corner A (ceil (f 1)),
        (g a).val = ceil (f 1) * f a.val * ceil (f 1)) ∧
      IsDiamondPositive g := by
  -- `f = h ∘ h` with `h` ⋄-self-adjoint; `⌈f(1)⌉ = ⌈f⌉ = ⌈h∘h⌉ = ⌈h⌉ = ⌈h(1)⌉`
  -- (103III.1/.2/.3), so part 1 applies to `h` *on the corner of `⌈f(1)⌉`*
  -- and gives a ⋄-self-adjoint `k` with `⟨f⟩ = k ∘ k` — the latter being
  -- exactly part 2, `⟨h²⟩ = ⟨h⟩²`.
  obtain ⟨h, hh, hfhh⟩ := hf
  have hfsa : IsDiamondSelfAdjoint f := purely_positive_basic_3 f ⟨h, hh, hfhh⟩
  have hfval : ∀ x : A, (f x : A) = h (h x) := fun x => by
    rw [hfhh, ncpComp_apply]
  have he : ceil (f 1) = ceil (h 1) := by
    rw [← purely_positive_basic_1 f hfsa, ← purely_positive_basic_1 h hh, hfhh]
    exact (purely_positive_basic_2 h hh).2
  have hkey : ∀ x : A, ceil (h 1) * x * ceil (h 1) = x →
      ceil (f 1) * h (ceil (f 1) * h x * ceil (f 1)) * ceil (f 1)
        = ceil (f 1) * h (h x) * ceil (f 1) := by
    intro x hx
    rw [he]
    exact (chevron_f_purely_positive_2 h hh x hx).symm
  obtain ⟨k, hkval, hksa⟩ := isDiamondSelfAdjoint_cornerMap h hh (ceil (f 1)) he
  refine ⟨ncpComp k k, fun a => ?_, k, hksa, rfl⟩
  have hmem : ceil (h 1) * a.val * ceil (h 1) = a.val := by
    rw [← he]; exact a.property
  rw [ncpComp_apply, hkval, hkval, hkey a.val hmem, hfval a.val]

/-- **105V** (`positive-map-uniqueness`, proc.tex:1766, Theorem),
existence: `√p(·)√p` is a ⋄-positive map with value `p` at `1`. -/
theorem positive_map_uniqueness_exists [VonNeumannAlgebra A] (p : A)
    (hp : 0 ≤ p) :
    ∃ f : NCPMap A A, IsDiamondPositive f ∧ f 1 = p ∧
      ∀ a, f a = CFC.sqrt p * a * CFC.sqrt p := by
  -- the map is `√p(·)√p = adSelf √p`, which is ⋄-positive by **103II**.2
  -- (applied to the positive element `√p`); its value at `1` is `√p√p = p`
  have hsa : star (CFC.sqrt p) = CFC.sqrt p :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  refine ⟨adSelf (CFC.sqrt p),
    purely_positive_examples_2 _ (CFC.sqrt_nonneg p), ?_, fun a => ?_⟩
  · rw [adSelf_apply, hsa, mul_one, CFC.sqrt_mul_sqrt_self p hp]
  · rw [adSelf_apply, hsa]

/-- **105V** (`positive-map-uniqueness`, proc.tex:1766, Theorem),
uniqueness: any ⋄-positive `f : 𝒜 → 𝒜` with `f(1) = p` is
`√p(·)√p`.

The author's proof (proc.tex:1772), transcribed: `⟨f⟩` on the corner
`⌈p⌉𝒜⌈p⌉` is ⋄-positive by **105IV**.3 and faithful by **105III**.3 (the
faithfulness argument of `chevron_f_basic_3` is repeated here, since
`⌈f⌉ = ⌈f(1)⌉` only up to the propositional equality
`purely_positive_basic_1` and the two corners are different *types*), so
`⟨f⟩ = √p(·)√p` by **104IX**; and `f = c_{⌈p⌉} ∘ ⟨f⟩ ∘ π_{⌈p⌉}`
together with `√p⌈p⌉ = √p` gives `f = √p(·)√p`.

Depends on **104IX**, hence on **104VII** — both proved. -/
theorem positive_map_uniqueness [VonNeumannAlgebra A] (p : A) (hp : 0 ≤ p)
    (f : NCPMap A A) (hf : IsDiamondPositive f) (h1 : f 1 = p) :
    ∀ a, f a = CFC.sqrt p * a * CFC.sqrt p := by
  have hfsa : IsDiamondSelfAdjoint f := purely_positive_basic_3 f hf
  have hcarr : ncpCarrier f = ceil (f 1) := purely_positive_basic_1 f hfsa
  have hcarr' : carrier (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' = ncpCarrier f := rfl
  have hu : IsStarProjection (ceil (f 1)) := isStarProjection_ceil _
  have hfund : ∀ a : A, (f a : A) = f (ceil (f 1) * a * ceil (f 1)) := by
    intro a
    have h := (carrier_fundamental
      (PositiveLinearMap.ofClass f.toCompletelyPositiveMap)
      f.preservesDirSups' a).2.2
    rwa [hcarr', hcarr] at h
  obtain ⟨g, hgval, hgdp⟩ := chevron_f_purely_positive_3 f hf
  -- `⟨f⟩` is faithful
  have hfspec : IsStarProjection (ncpCarrier f) ∧ f (1 - ncpCarrier f) = 0 ∧
      ∀ r : A, IsStarProjection r → f (1 - r) = 0 → ncpCarrier f ≤ r :=
    (exists_ncpCarrier f).choose_spec.1
  have hgfaith : ncpCarrier g = 1 := by
    have hqspec : IsStarProjection (ncpCarrier g) ∧
        g (1 - ncpCarrier g) = 0 ∧
        ∀ r, IsStarProjection r → g (1 - r) = 0 → ncpCarrier g ≤ r :=
      (exists_ncpCarrier g).choose_spec.1
    set q := ncpCarrier g with hqdef
    have hqproj : IsStarProjection q := hqspec.1
    have hqv : IsStarProjection q.val :=
      ⟨congrArg Corner.val hqproj.isIdempotentElem.eq,
        congrArg Corner.val hqproj.isSelfAdjoint.star_eq⟩
    have hval : ceil (f 1) * f (ceil (f 1) - q.val) * ceil (f 1) = 0 := by
      have h := congrArg Corner.val hqspec.2.1
      rw [hgval] at h
      simpa using h
    have hfz : (f (ceil (f 1) - q.val) : A) = 0 :=
      (ceilOne_conj f (ceil (f 1) - q.val)).symm.trans hval
    set s : A := q.val + (1 - ceil (f 1)) with hsdef
    have hqe : q.val * ceil (f 1) = q.val := Corner.mul_right q
    have heq : ceil (f 1) * q.val = q.val := Corner.mul_left q
    have hsproj : IsStarProjection s := by
      constructor
      · change s * s = s
        rw [hsdef]
        calc (q.val + (1 - ceil (f 1))) * (q.val + (1 - ceil (f 1)))
            = q.val * q.val + (q.val - q.val * ceil (f 1))
              + ((1 - ceil (f 1)) * q.val)
              + (1 - ceil (f 1)) * (1 - ceil (f 1)) := by noncomm_ring
          _ = q.val + (1 - ceil (f 1)) := by
              rw [hqv.isIdempotentElem.eq, hqe, sub_self,
                hu.one_sub.isIdempotentElem.eq, sub_mul, one_mul, heq, sub_self]
              abel
      · change star s = s
        rw [hsdef, star_add, hqv.isSelfAdjoint.star_eq,
          hu.one_sub.isSelfAdjoint.star_eq]
    have hles : ceil (f 1) ≤ s := by
      rw [← hcarr]
      refine hfspec.2.2 s hsproj ?_
      rw [show (1 : A) - s = ceil (f 1) - q.val by rw [hsdef]; abel]
      exact hfz
    have hes : ceil (f 1) * s = ceil (f 1) :=
      ((projection_below_effect s (ceil (f 1))
        ⟨hsproj.nonneg, hsproj.le_one⟩ hu).out 0 7).mp hles
    refine (Corner.val_injective ?_).symm
    rw [Corner.val_one]
    rw [hsdef] at hes
    calc ceil (f 1)
        = ceil (f 1) * (q.val + (1 - ceil (f 1))) := hes.symm
      _ = ceil (f 1) * q.val + (ceil (f 1) - ceil (f 1) * ceil (f 1)) := by
          noncomm_ring
      _ = q.val := by rw [heq, hu.isIdempotentElem.eq, sub_self, add_zero]
  -- `⟨f⟩(1) = f(1) = p`
  have hfu : (f (ceil (f 1)) : A) = f 1 := by
    conv_rhs => rw [hfund 1]
    rw [mul_one, hu.isIdempotentElem.eq]
  have hg1 : ((g 1).val : A) = p := by
    rw [hgval, Corner.val_one, hfu, ceilOne_conj, h1]
  -- `√p` lies in the corner and is the square root of `⟨f⟩(1)` there
  have hsq : ceil (f 1) * CFC.sqrt (f 1) = CFC.sqrt (f 1) := by
    rw [ceil_eq_rangeProj_sqrt (ncpMap_nonneg f zero_le_one)]
    exact (ceill_basic_2 (CFC.sqrt (f 1))).1.2
  have hqs : CFC.sqrt (f 1) * ceil (f 1) = CFC.sqrt (f 1) := by
    have h2 := congrArg star hsq
    rwa [star_mul, hu.isSelfAdjoint.star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (f 1))).star_eq] at h2
  have hmem : ceil (f 1) * CFC.sqrt p * ceil (f 1) = CFC.sqrt p := by
    rw [← h1, hsq, hqs]
  set s : Corner A (ceil (f 1)) := ⟨CFC.sqrt p, hmem⟩ with hsdef
  have hs0 : (0 : Corner A (ceil (f 1))) ≤ s := CFC.sqrt_nonneg p
  have hsqrt : CFC.sqrt (g 1) = s :=
    CFC.sqrt_unique (Corner.val_injective (by
      rw [Corner.val_mul, hsdef, hg1]
      exact CFC.sqrt_mul_sqrt_self p hp)) hs0
  have hkey := faithful_positive_map_uniqueness g hgdp hgfaith
  intro a
  have hmemA : ceil (f 1) * (ceil (f 1) * a * ceil (f 1)) * ceil (f 1)
      = ceil (f 1) * a * ceil (f 1) := by
    have h := hu.isIdempotentElem.eq
    calc ceil (f 1) * (ceil (f 1) * a * ceil (f 1)) * ceil (f 1)
        = (ceil (f 1) * ceil (f 1)) * a * (ceil (f 1) * ceil (f 1)) := by
          noncomm_ring
      _ = ceil (f 1) * a * ceil (f 1) := by rw [h]
  have hv := hgval ⟨ceil (f 1) * a * ceil (f 1), hmemA⟩
  have hthis := congrArg Corner.val (hkey ⟨ceil (f 1) * a * ceil (f 1), hmemA⟩)
  rw [hsqrt] at hthis
  have hval2 : (s * (⟨ceil (f 1) * a * ceil (f 1), hmemA⟩ : Corner A (ceil (f 1)))
      * s).val = CFC.sqrt p * a * CFC.sqrt p := by
    show CFC.sqrt p * (ceil (f 1) * a * ceil (f 1)) * CFC.sqrt p = _
    have e1 : CFC.sqrt p * ceil (f 1) = CFC.sqrt p := by rw [← h1]; exact hqs
    have e2 : ceil (f 1) * CFC.sqrt p = CFC.sqrt p := by rw [← h1]; exact hsq
    calc CFC.sqrt p * (ceil (f 1) * a * ceil (f 1)) * CFC.sqrt p
        = (CFC.sqrt p * ceil (f 1)) * a * (ceil (f 1) * CFC.sqrt p) := by
          noncomm_ring
      _ = CFC.sqrt p * a * CFC.sqrt p := by rw [e1, e2]
  rw [hfund a, ← ceilOne_conj f (ceil (f 1) * a * ceil (f 1)), ← hv, hthis, hval2]


/-- **105VII** (`sqrt-axiom`, proc.tex:1792, Corollary, "Square Root
Axiom"): given positive `p` there is a unique ⋄-positive `g : 𝒜 → 𝒜`
with `g(g(1)) = p`, namely `g = ⁴√p(·)⁴√p`.

The author's proof (proc.tex:1796), transcribed: any such `g` is
`√(g(1))(·)√(g(1))` by **105V**, so `p = g(g(1)) = g(1)²` and hence
`g(1) = √p` by uniqueness of the square root; existence is `adSelf ⁴√p`,
⋄-positive by **103II**.2.

The uniqueness half depends on **105V**, hence on **104VII** — both
proved; the existence half is unconditional. -/
theorem sqrt_axiom [VonNeumannAlgebra A] (p : A) (hp : 0 ≤ p) :
    (∃ g : NCPMap A A, IsDiamondPositive g ∧ g (g 1) = p ∧
      ∀ a, g a = CFC.sqrt (CFC.sqrt p) * a * CFC.sqrt (CFC.sqrt p)) ∧
    ∀ g : NCPMap A A, IsDiamondPositive g → g (g 1) = p →
      ∀ a, g a = CFC.sqrt (CFC.sqrt p) * a * CFC.sqrt (CFC.sqrt p) := by
  have hs0 : (0 : A) ≤ CFC.sqrt p := CFC.sqrt_nonneg p
  have hss : CFC.sqrt p * CFC.sqrt p = p := CFC.sqrt_mul_sqrt_self p hp
  obtain ⟨t, ht0, htt⟩ : ∃ t : A, (0 : A) ≤ t ∧ t * t = CFC.sqrt p :=
    ⟨CFC.sqrt (CFC.sqrt p), CFC.sqrt_nonneg _, CFC.sqrt_mul_sqrt_self _ hs0⟩
  have hts : CFC.sqrt (CFC.sqrt p) = t := CFC.sqrt_unique htt ht0
  have htsa : star t = t := (IsSelfAdjoint.of_nonneg ht0).star_eq
  simp only [hts]
  constructor
  · refine ⟨adSelf t, purely_positive_examples_2 _ ht0, ?_,
      fun a => by rw [adSelf_apply, htsa]⟩
    have h1 : (adSelf t (1 : A) : A) = CFC.sqrt p := by
      rw [adSelf_apply, htsa, mul_one, htt]
    rw [h1, adSelf_apply, htsa, ← htt, ← hss, ← htt]
    noncomm_ring
  · intro g hg hgg a
    have hg0 : (0 : A) ≤ g 1 := ncpMap_nonneg g zero_le_one
    have hform := positive_map_uniqueness (g 1) hg0 g hg rfl
    obtain ⟨r, hr0, hr⟩ : ∃ r : A, (0 : A) ≤ r ∧ r * r = g 1 :=
      ⟨CFC.sqrt (g 1), CFC.sqrt_nonneg _, CFC.sqrt_mul_sqrt_self _ hg0⟩
    have hsq : CFC.sqrt (g 1) = r := CFC.sqrt_unique hr hr0
    rw [hsq] at hform
    have hp2 : p = g 1 * g 1 := by
      have h0 : p = r * g 1 * r := by rw [← hgg, hform (g 1)]
      rw [h0, ← hr]; noncomm_ring
    have hg1 : (g 1 : A) = CFC.sqrt p := by
      rw [hp2, CFC.sqrt_mul_self _ hg0]
    have hrt : r = t := by rw [← hts, ← hsq, hg1]
    rw [hform a, hrt]


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

/-- Infrastructure for 106I, axiom (E): for an **effect** `b` and a
projection `q` one has `b ≤ q` iff `⌈b⌉ ≤ q`.  (The `⟸` direction needs
`b ≤ 1`: it fails for positive `b` of norm `> 1`, e.g. `b = 2q`.)  This is
what turns the order-theoretic axiom (E) into the ceiling-theoretic
contraposition of **101VII**.1. -/
private theorem effect_le_isStarProjection_iff [VonNeumannAlgebra A] {b q : A}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hq : IsStarProjection q) :
    b ≤ q ↔ ceil b ≤ q := by
  constructor
  · intro h
    have hc : star (1 - q) = 1 - q := hq.one_sub.isSelfAdjoint.star_eq
    have h1 : (0 : A) ≤ (1 - q) * (q - b) * (1 - q) := by
      have h0 := star_left_conjugate_nonneg (sub_nonneg.mpr h) (1 - q)
      rwa [hc] at h0
    have h2 : (1 - q) * (q - b) * (1 - q) = -((1 - q) * b * (1 - q)) := by
      have hz : (1 - q) * q = 0 := by
        rw [sub_mul, one_mul, hq.isIdempotentElem.eq, sub_self]
      calc (1 - q) * (q - b) * (1 - q)
          = ((1 - q) * q) * (1 - q) - (1 - q) * b * (1 - q) := by noncomm_ring
        _ = -((1 - q) * b * (1 - q)) := by rw [hz, zero_mul, zero_sub]
    have h3 : (1 - q) * b * (1 - q) = 0 := by
      refine le_antisymm (neg_nonneg.mp (h2 ▸ h1)) ?_
      have h0 := star_left_conjugate_nonneg hb (1 - q)
      rwa [hc] at h0
    have h4 := (ceil_le_perp_iff hb hq.one_sub).mpr h3
    rwa [sub_sub_cancel] at h4
  · intro h
    have hbq : b * q = b := (ceil_le_iff hb hq).mp h
    have hqb : q * b = b := ((ceil_basic_1 b q hb hq).out 2 0).mp h
    have hz : (0 : A) ≤ q * (1 - b) * q := by
      have h0 := star_left_conjugate_nonneg (sub_nonneg.mpr hb1) q
      rwa [hq.isSelfAdjoint.star_eq] at h0
    have he : q * (1 - b) * q = q - b := by
      calc q * (1 - b) * q = q * q - (q * b) * q := by noncomm_ring
        _ = q - b := by rw [hq.isIdempotentElem.eq, hqb, hbq]
    rw [he] at hz
    exact sub_nonneg.mp hz

/-- **106I** (`uniqueness-sequential-product`, proc.tex:1811, Theorem),
existence: `p ∗ q = √p q √p` is a sequential product on the effects of
any von Neumann algebra. -/
theorem uniqueness_sequential_product_exists [VonNeumannAlgebra A] :
    IsSequentialProduct (fun p q : A => CFC.sqrt p * q * CFC.sqrt p) := by
  -- (A) `√p1√p = p`; (B) `√p(·)√p = adSelf √p`, pure by **100II**.3;
  -- (C) both sides are `pqp`, since `√p p √p = pp` and `√(pp) = p`;
  -- (D) `p = √p ∗ √p` with `√p` an effect; (E) is **101VII**.1, the
  -- contraposition of `a*(·)a` with `a(·)a*` at the self-adjoint `a = √p`,
  -- transported from ceilings to the order by `effect_le_isStarProjection_iff`.
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp q hq => ?_, fun p hp => ?_,
    fun p hp e₁ e₂ h₁ h₂ => ?_⟩
  · show CFC.sqrt p * 1 * CFC.sqrt p = p
    rw [mul_one, CFC.sqrt_mul_sqrt_self p hp.1]
  · exact ⟨adSelf (CFC.sqrt p), isPure_adSelf _, fun q _ => by
      rw [adSelf_apply, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq]⟩
  · show CFC.sqrt p * (CFC.sqrt p * q * CFC.sqrt p) * CFC.sqrt p
      = CFC.sqrt (CFC.sqrt p * p * CFC.sqrt p) * q
        * CFC.sqrt (CFC.sqrt p * p * CFC.sqrt p)
    set s := CFC.sqrt p with hsdef
    have hps : s * s = p := CFC.sqrt_mul_sqrt_self p hp.1
    have h1 : s * p * s = p * p := by rw [← hps]; noncomm_ring
    rw [h1, CFC.sqrt_mul_self p hp.1]
    calc s * (s * q * s) * s = (s * s) * q * (s * s) := by noncomm_ring
      _ = p * q * p := by rw [hps]
  · set s := CFC.sqrt p with hsdef
    have hs0 : (0 : A) ≤ s := CFC.sqrt_nonneg p
    have hps : s * s = p := CFC.sqrt_mul_sqrt_self p hp.1
    have hs1 : s ≤ 1 := by
      have h := CFC.sqrt_le_sqrt p 1 hp.2
      rwa [CFC.sqrt_one] at h
    refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
    show p = CFC.sqrt s * s * CFC.sqrt s
    set t := CFC.sqrt s with htdef
    have hts : t * t = s := CFC.sqrt_mul_sqrt_self s hs0
    calc p = s * s := hps.symm
      _ = t * s * t := by rw [← hts]; noncomm_ring
  · show CFC.sqrt p * e₁ * CFC.sqrt p ≤ 1 - e₂ ↔
      CFC.sqrt p * e₂ * CFC.sqrt p ≤ 1 - e₁
    set s := CFC.sqrt p with hsdef
    have hs0 : (0 : A) ≤ s := CFC.sqrt_nonneg p
    have hssa : star s = s := (IsSelfAdjoint.of_nonneg hs0).star_eq
    have hps : s * s = p := CFC.sqrt_mul_sqrt_self p hp.1
    -- `s e s` is an effect, for every effect `e`
    have heff : ∀ e : A, IsStarProjection e →
        (0 : A) ≤ s * e * s ∧ s * e * s ≤ 1 := by
      intro e he
      have h0 : (0 : A) ≤ s * e * s := by
        have h := star_left_conjugate_nonneg he.nonneg s
        rwa [hssa] at h
      refine ⟨h0, ?_⟩
      have h1 : (0 : A) ≤ s * (1 - e) * s := by
        have h := star_left_conjugate_nonneg (sub_nonneg.mpr he.le_one) s
        rwa [hssa] at h
      have h2 : s * (1 - e) * s = p - s * e * s := by
        calc s * (1 - e) * s = s * s - s * e * s := by noncomm_ring
          _ = p - s * e * s := by rw [hps]
      rw [h2, sub_nonneg] at h1
      exact h1.trans hp.2
    have hd : ∀ e : A, diamondUp (adSelf s) e = ceil (s * e * s) := by
      intro e
      show ceil (adSelf s e) = _
      rw [adSelf_apply, hssa]
    have hcon : Contraposed (adSelf s) (adSelf s) := by
      have h := equivalent_examples_1 s
      rwa [hssa] at h
    rw [effect_le_isStarProjection_iff (heff e₁ h₁).1 (heff e₁ h₁).2 h₂.one_sub,
      effect_le_isStarProjection_iff (heff e₂ h₂).1 (heff e₂ h₂).2 h₁.one_sub,
      ← hd e₁, ← hd e₂]
    exact hcon e₁ e₂ h₁ h₂

/-- **106I** (`uniqueness-sequential-product`, proc.tex:1811, Theorem),
uniqueness: any sequential product on the effects of a von Neumann algebra
is given by `p ∗ q = √p q √p`.

The author's proof (proc.tex:1839), transcribed: pick `p'` with
`p = p' ∗ p'` by (D) and a pure `f` with `p' ∗ (·) = f` on effects by (B);
axiom (E) says exactly that `f` is contraposed to itself (turning the
order-theoretic `≤ e^⊥` into the ceiling-theoretic one by
`effect_le_isStarProjection_iff`, as in the existence half), so `f` is
⋄-self-adjoint and `f∘f` is ⋄-positive with `f(f(1)) = p' ∗ p' = p` by
(A); **105V** makes `f∘f = √p(·)√p`, and (C) turns `p ∗ q` into
`f(f(q))`.

Depends on **105V**, hence on **104VII** — both proved. -/
theorem uniqueness_sequential_product [VonNeumannAlgebra A] (op : A → A → A)
    (h : IsSequentialProduct op) :
    ∀ p ∈ effects A, ∀ q ∈ effects A,
      op p q = CFC.sqrt p * q * CFC.sqrt p := by
  intro p hp q hq
  obtain ⟨p', hp', hpp⟩ := h.ax4 p hp
  obtain ⟨f, hfpure, hfval⟩ := h.ax2 p' hp'
  have hone : (1 : A) ∈ effects A := ⟨zero_le_one, le_rfl⟩
  have hf1 : (f 1 : A) = p' := by rw [← hfval 1 hone]; exact h.ax1 p' hp'
  -- `f` maps effects to effects
  have hfeff : ∀ b : A, b ∈ effects A → f b ∈ effects A := by
    intro b hb
    refine ⟨ncpMap_nonneg f hb.1, ?_⟩
    have h1 : (0 : A) ≤ f (1 - b) := ncpMap_nonneg f (sub_nonneg.mpr hb.2)
    have h2 : (f (1 - b) : A) = f 1 - f b :=
      map_sub f.toCompletelyPositiveMap.toLinearMap 1 b
    rw [h2, sub_nonneg] at h1
    exact h1.trans (hf1 ▸ hp'.2)
  -- axiom (E) says exactly that `f` is contraposed to itself
  have hcon : Contraposed f f := by
    intro e₁ e₂ h₁ h₂
    have hb₁ := hfeff e₁ ⟨h₁.nonneg, h₁.le_one⟩
    have hb₂ := hfeff e₂ ⟨h₂.nonneg, h₂.le_one⟩
    have hax := h.ax5 p' hp' e₁ e₂ h₁ h₂
    rw [hfval e₁ ⟨h₁.nonneg, h₁.le_one⟩, hfval e₂ ⟨h₂.nonneg, h₂.le_one⟩] at hax
    show ceil (f e₁) ≤ 1 - e₂ ↔ ceil (f e₂) ≤ 1 - e₁
    rw [← effect_le_isStarProjection_iff hb₁.1 hb₁.2 h₂.one_sub,
      ← effect_le_isStarProjection_iff hb₂.1 hb₂.2 h₁.one_sub]
    exact hax
  have hfsa : IsDiamondSelfAdjoint f := ⟨hfpure, hcon⟩
  have hdp : IsDiamondPositive (ncpComp f f) := ⟨f, hfsa, rfl⟩
  have hff1 : (ncpComp f f) 1 = p := by
    rw [ncpComp_apply, hf1, ← hfval p' hp', ← hpp]
  have hkey := positive_map_uniqueness p hp.1 (ncpComp f f) hdp hff1
  have hopq : op p' q ∈ effects A := by
    rw [hfval q hq]; exact hfeff q hq
  calc op p q = op (op p' p') q := by rw [← hpp]
    _ = op p' (op p' q) := (h.ax3 p' hp' q hq).symm
    _ = f (f q) := by rw [hfval _ hopq, hfval q hq]
    _ = (ncpComp f f) q := (ncpComp_apply f f q).symm
    _ = CFC.sqrt p * q * CFC.sqrt p := hkey q


/-- **106III** (proc.tex:1858, Exercise), part 1: `p ∗ q := ⌈p⌉q⌈p⌉`
satisfies all axioms of 106I except (A) (which fails when `A` is
nontrivial).  The conjuncts are (B), (C), (D), (E), `¬(A)`, each written
out at this `∗`; the (C) conjunct is
`p ∗ (p ∗ q) = (p ∗ p) ∗ q`, whose inner `⌈p⌉` used to be printed here as
`⌈q⌉` — true and equivalent for effects (`⌈q⌉q⌈q⌉ = q`), but not the
axiom. -/
theorem sequential_product_counterexample_1 [VonNeumannAlgebra A]
    [Nontrivial A] :
    (∀ p ∈ effects A, ∃ f : NCPMap A A, IsPure f ∧
        ∀ q ∈ effects A, ceil p * q * ceil p = f q) ∧
    (∀ p ∈ effects A, ∀ q ∈ effects A,
        ceil p * (ceil p * q * ceil p) * ceil p =
          ceil (ceil p * p * ceil p) * q * ceil (ceil p * p * ceil p)) ∧
    (∀ p ∈ effects A, ∃ q ∈ effects A, p = ceil q * q * ceil q) ∧
    (∀ p ∈ effects A, ∀ e₁ e₂ : A, IsStarProjection e₁ →
        IsStarProjection e₂ →
        (ceil p * e₁ * ceil p ≤ 1 - e₂ ↔ ceil p * e₂ * ceil p ≤ 1 - e₁)) ∧
    ¬ IsSequentialProduct (fun p q : A => ceil p * q * ceil p) := by
  -- `⌈b⌉b⌈b⌉ = b` for every effect `b` (both `b⌈b⌉ = b` and `⌈b⌉b = b`)
  have hsandwich : ∀ b : A, 0 ≤ b → ceil b * b * ceil b = b := by
    intro b hb
    have h2 : b * ceil b = b := (ceil_spec hb).2.1
    have h1 : ceil b * b = b :=
      ((ceil_basic_1 b (ceil b) hb (ceil_spec hb).1).out 2 0).mp le_rfl
    rw [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (B): `⌈p⌉(·)⌈p⌉` is pure — the corner projection onto `⌈p⌉𝒜⌈p⌉`
    -- followed by the corner *inclusion*, which is a filter by
    -- `isFilter_cornerIncl` (this is where 96V would otherwise be needed).
    intro p _
    have hcp : IsStarProjection (ceil p) := isStarProjection_ceil p
    have heff : ceil p ∈ effects A := ⟨hcp.nonneg, hcp.le_one⟩
    have hfl : floor (ceil p) = ceil p := by
      refine le_antisymm (floor_le heff) ?_
      exact (floor_spec heff).2.2 _ hcp hcp.isIdempotentElem.eq
    have hfac : adSelf (ceil p)
        = ncpComp (cornerIncl (floor (ceil p))).toNCPMap
          (stdCorner (ceil p)).toNCPMap := by
      refine DFunLike.ext _ _ fun a => ?_
      rw [adSelf_apply, ncpComp_apply, cornerIncl_apply, stdCorner_apply, hfl,
        hcp.isSelfAdjoint.star_eq]
    have hcorner : IsCornerMap (stdCorner (ceil p)).toNCPMap :=
      ⟨(stdCorner (ceil p)).unital', ceil p, heff, isCornerOf_stdCorner (ceil p) heff⟩
    refine ⟨adSelf (ceil p), ?_, fun q _ => ?_⟩
    · rw [hfac]
      exact IsPure.comp (IsPure.filter (isFilter_cornerIncl (floor (ceil p))))
        (IsPure.corner hcorner)
    · rw [adSelf_apply, hcp.isSelfAdjoint.star_eq]
  · -- (C): both sides are `⌈p⌉q⌈p⌉`
    intro p hp q _
    have hcp : IsStarProjection (ceil p) := isStarProjection_ceil p
    rw [hsandwich p hp.1]
    calc ceil p * (ceil p * q * ceil p) * ceil p
        = (ceil p * ceil p) * q * (ceil p * ceil p) := by noncomm_ring
      _ = ceil p * q * ceil p := by rw [hcp.isIdempotentElem.eq]
  · -- (D): `p = ⌈p⌉p⌈p⌉`
    intro p hp
    exact ⟨p, hp, (hsandwich p hp.1).symm⟩
  · -- (E): both sides say `e₁⌈p⌉e₂ = 0`
    intro p _ e₁ e₂ he₁ he₂
    have hcp : IsStarProjection (ceil p) := isStarProjection_ceil p
    have hc : star (ceil p) = ceil p := hcp.isSelfAdjoint.star_eq
    -- for an effect `x` and a projection `e`: `x ≤ e^⊥` iff `e x e = 0`
    have hiff : ∀ x : A, 0 ≤ x → x ≤ 1 → ∀ e : A, IsStarProjection e →
        (x ≤ 1 - e ↔ e * x * e = 0) := by
      intro x hx hx1 e he
      constructor
      · intro h
        have h1 : e * x * e ≤ e * (1 - e) * e := by
          have := star_left_conjugate_le_conjugate h e
          rwa [he.isSelfAdjoint.star_eq] at this
        have h2 : e * (1 - e) * e = 0 := by
          rw [mul_sub, mul_one, he.isIdempotentElem.eq, sub_self, zero_mul]
        have h3 : (0 : A) ≤ e * x * e := by
          have := star_left_conjugate_nonneg hx e
          rwa [he.isSelfAdjoint.star_eq] at this
        exact le_antisymm (h2 ▸ h1) h3
      · intro h
        have hle : ceil x ≤ 1 - e := (ceil_le_perp_iff hx he).mpr h
        have hxe : x * (1 - e) = x := (ceil_le_iff hx he.one_sub).mp hle
        have hex : (1 - e) * x = x :=
          ((ceil_basic_1 x (1 - e) hx he.one_sub).out 2 0).mp hle
        calc x = (1 - e) * x * (1 - e) := by rw [hex, hxe]
          _ ≤ (1 - e) * 1 * (1 - e) := by
              have := star_left_conjugate_le_conjugate hx1 (1 - e)
              rwa [he.one_sub.isSelfAdjoint.star_eq] at this
          _ = 1 - e := by
              rw [mul_one, sub_mul, one_mul, mul_sub, mul_one,
                he.isIdempotentElem.eq]
              abel
    have hnn : ∀ e : A, IsStarProjection e → (0 : A) ≤ ceil p * e * ceil p := by
      intro e he
      have := star_left_conjugate_nonneg he.nonneg (ceil p)
      rwa [hc] at this
    have hle1 : ∀ e : A, IsStarProjection e → ceil p * e * ceil p ≤ 1 := by
      intro e he
      calc ceil p * e * ceil p ≤ ceil p * 1 * ceil p := by
            have := star_left_conjugate_le_conjugate he.le_one (ceil p)
            rwa [hc] at this
        _ = ceil p := by rw [mul_one, hcp.isIdempotentElem.eq]
        _ ≤ 1 := hcp.le_one
    have hkey : ∀ e f : A, IsStarProjection e → IsStarProjection f →
        (f * (ceil p * e * ceil p) * f = 0 ↔ e * ceil p * f = 0) := by
      intro e f he hf
      have hstar : star (e * ceil p * f) = f * ceil p * e := by
        rw [star_mul, star_mul, hf.isSelfAdjoint.star_eq, hc,
          he.isSelfAdjoint.star_eq, mul_assoc]
      constructor
      · intro h
        refine (CStarRing.star_mul_self_eq_zero_iff (e * ceil p * f)).mp ?_
        rw [hstar]
        calc f * ceil p * e * (e * ceil p * f)
            = f * (ceil p * e * ceil p) * f := by
              rw [show f * ceil p * e * (e * ceil p * f)
                = f * ceil p * (e * e) * ceil p * f by noncomm_ring,
                he.isIdempotentElem.eq]
              noncomm_ring
          _ = 0 := h
      · intro h
        have h' : f * ceil p * e = 0 := by rw [← hstar, h, star_zero]
        calc f * (ceil p * e * ceil p) * f
            = (f * ceil p * e) * (e * ceil p * f) := by
              rw [show (f * ceil p * e) * (e * ceil p * f)
                = f * ceil p * (e * e) * ceil p * f by noncomm_ring,
                he.isIdempotentElem.eq]
              noncomm_ring
          _ = 0 := by rw [h', zero_mul]
    have hst : ∀ x y : A, IsStarProjection x → IsStarProjection y →
        star (x * ceil p * y) = y * ceil p * x := by
      intro x y hx hy
      rw [star_mul, star_mul, hy.isSelfAdjoint.star_eq, hc,
        hx.isSelfAdjoint.star_eq, ← mul_assoc]
    rw [hiff _ (hnn e₁ he₁) (hle1 e₁ he₁) e₂ he₂,
      hiff _ (hnn e₂ he₂) (hle1 e₂ he₂) e₁ he₁,
      hkey e₁ e₂ he₁ he₂, hkey e₂ e₁ he₂ he₁]
    constructor
    · intro h
      rw [← hst e₁ e₂ he₁ he₂, h, star_zero]
    · intro h
      rw [← hst e₂ e₁ he₂ he₁, h, star_zero]
  · -- ¬(A): at `p = ½·1` the operation gives `⌈p⌉ = 1 ≠ p`
    intro h
    set p : A := ((1 / 2 : ℝ) : ℂ) • 1 with hpdef
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hp0 : (0 : A) ≤ p := Theses.A.CStar.ofReal_smul_nonneg zero_le_one hhalf.le
    have hp1 : p ≤ (1 : A) := by
      rw [hpdef, ← Algebra.algebraMap_eq_smul_one]
      have := Theses.A.CStar.algebraMap_ofReal_mono (𝒜 := A) (s := (1 / 2 : ℝ))
        (t := (1 : ℝ)) (by norm_num)
      rwa [Complex.ofReal_one, map_one] at this
    have hceil : ceil p = 1 := by
      rw [hpdef, (ceil_basic_4 (1 : A) (1 : A) zero_le_one zero_le_one (1 / 2) hhalf).1,
        ceil_of_isStarProjection (IsStarProjection.one (R := A))]
    have hax1 := h.ax1 p ⟨hp0, hp1⟩
    rw [hceil, one_mul, mul_one] at hax1
    -- `p = 1` forces `A` trivial
    have hone : ((1 / 2 : ℝ) : ℂ) • (1 : A) = (1 : A) := hpdef.symm.trans hax1.symm
    have hzero : (((1 / 2 : ℝ) : ℂ) - 1) • (1 : A) = 0 := by
      rw [sub_smul, hone, one_smul, sub_self]
    have hne : (((1 / 2 : ℝ) : ℂ) - 1) ≠ 0 := by
      simp only [ne_eq, sub_eq_zero]
      intro hcc
      have : ((1 / 2 : ℝ) : ℝ) = 1 := by exact_mod_cast hcc
      norm_num at this
    exact one_ne_zero ((smul_eq_zero.mp hzero).resolve_left hne)

/-- **106III** (proc.tex:1858, Exercise), part 2:
`p ∗ q := ⌊p⌋q⌊p⌋ + √(p−⌊p⌋) q √(p−⌊p⌋)` satisfies axioms (A), (C),
(D), (E) of 106I.  That (B) **fails** — the other half of the part, and the
reason it is stated — is
`sequential_product_counterexample_2_ax2_is_false` below. -/
theorem sequential_product_counterexample_2 [VonNeumannAlgebra A] :
    ∀ op : A → A → A,
      (∀ p q, op p q = floor p * q * floor p +
        CFC.sqrt (p - floor p) * q * CFC.sqrt (p - floor p)) →
      (∀ p ∈ effects A, op p 1 = p) ∧
      (∀ p ∈ effects A, ∀ q ∈ effects A, op p (op p q) = op (op p p) q) ∧
      (∀ p ∈ effects A, ∃ q ∈ effects A, p = op q q) ∧
      (∀ p ∈ effects A, ∀ e₁ e₂ : A, IsStarProjection e₁ →
        IsStarProjection e₂ → (op p e₁ ≤ 1 - e₂ ↔ op p e₂ ≤ 1 - e₁)) := by
  -- Exercise, no author argument.  Write `f := ⌊p⌋` and `s := √(p−⌊p⌋)`; the
  -- whole computation rests on `fp = pf = f`, hence `f(p−f) = 0`, hence
  -- `fs = sf = 0`, and on `ps = sp`.  Then `p ∗ q = fqf + sqs` with the two
  -- summands living in orthogonal corners, which makes (A) `f + (p−f) = p`,
  -- (C) `p ∗ p = p²` together with `⌊p²⌋ = ⌊p⌋` and `√(p²−⌊p⌋) = p−⌊p⌋`,
  -- (D) `q ∗ q = q²` at `q = √p`, and (E) the conjunction of the two
  -- symmetric conditions `e₁fe₂ = 0` and `e₁se₂ = 0`.
  intro op hop
  have basics : ∀ p ∈ effects A,
      IsStarProjection (floor p) ∧ floor p * p = floor p ∧ p * floor p = floor p ∧
        (0 : A) ≤ p - floor p ∧
        CFC.sqrt (p - floor p) * CFC.sqrt (p - floor p) = p - floor p ∧
        star (CFC.sqrt (p - floor p)) = CFC.sqrt (p - floor p) ∧
        floor p * CFC.sqrt (p - floor p) = 0 ∧
        CFC.sqrt (p - floor p) * floor p = 0 ∧
        p * CFC.sqrt (p - floor p) = CFC.sqrt (p - floor p) * p := by
    intro p hp
    have hf : IsStarProjection (floor p) := (floor_spec hp).1
    have hfp : floor p * p = floor p := (floor_spec hp).2.1
    have hfsa : star (floor p) = floor p := hf.isSelfAdjoint.star_eq
    have hpsa : star p = p := (IsSelfAdjoint.of_nonneg hp.1).star_eq
    have hpf : p * floor p = floor p := by
      have h := congrArg star hfp
      rwa [star_mul, hpsa, hfsa] at h
    have hsub : (0 : A) ≤ p - floor p := sub_nonneg.mpr (floor_le hp)
    have hss : CFC.sqrt (p - floor p) * CFC.sqrt (p - floor p) = p - floor p :=
      CFC.sqrt_mul_sqrt_self _ hsub
    have hssa : star (CFC.sqrt (p - floor p)) = CFC.sqrt (p - floor p) :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
    have hfx : floor p * (p - floor p) = 0 := by
      rw [mul_sub, hfp, hf.isIdempotentElem.eq, sub_self]
    have hsf : CFC.sqrt (p - floor p) * floor p = 0 := by
      refine (CStarRing.star_mul_self_eq_zero_iff _).mp ?_
      rw [star_mul, hssa, hfsa]
      calc floor p * CFC.sqrt (p - floor p) * (CFC.sqrt (p - floor p) * floor p)
          = floor p * (CFC.sqrt (p - floor p) * CFC.sqrt (p - floor p)) * floor p := by
            noncomm_ring
        _ = 0 := by rw [hss, hfx, zero_mul]
    have hfs : floor p * CFC.sqrt (p - floor p) = 0 := by
      have h := congrArg star hsf
      rwa [star_mul, hfsa, hssa, star_zero] at h
    have hps : p * CFC.sqrt (p - floor p) = CFC.sqrt (p - floor p) * p := by
      refine (Theses.A.CStar.sqrt_commute (p - floor p) hsub p ?_).1
      rw [mul_sub, sub_mul, hfp, hpf]
    exact ⟨hf, hfp, hpf, hsub, hss, hssa, hfs, hsf, hps⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (A): `f·1·f + s·1·s = f + (p − f) = p`
    intro p hp
    obtain ⟨hf, -, -, -, hss, -, -, -, -⟩ := basics p hp
    rw [hop, mul_one, mul_one, hf.isIdempotentElem.eq, hss]
    abel
  · -- (C): both sides are `fqf + (p−f)q(p−f)`
    intro p hp q _
    obtain ⟨hf, hfp, hpf, hsub, hss, -, hfs, hsf, hps⟩ := basics p hp
    have hff : floor p * floor p = floor p := hf.isIdempotentElem.eq
    have hpsa : star p = p := (IsSelfAdjoint.of_nonneg hp.1).star_eq
    -- `p ∗ p = p²`
    have hopp : op p p = p * p := by
      rw [hop]
      have e1 : floor p * p * floor p = floor p := by rw [hfp, hff]
      have e2 : CFC.sqrt (p - floor p) * p * CFC.sqrt (p - floor p) = p * p - floor p := by
        calc CFC.sqrt (p - floor p) * p * CFC.sqrt (p - floor p)
            = CFC.sqrt (p - floor p) * (p * CFC.sqrt (p - floor p)) := by noncomm_ring
          _ = CFC.sqrt (p - floor p) * CFC.sqrt (p - floor p) * p := by
              rw [hps]; noncomm_ring
          _ = p * p - floor p := by rw [hss, sub_mul, hfp]
      rw [e1, e2]; abel
    -- `⌊p²⌋ = ⌊p⌋` and `√(p² − ⌊p⌋) = p − ⌊p⌋`
    have hpp0 : (0 : A) ≤ p * p := by
      have h := star_mul_self_nonneg p
      rwa [hpsa] at h
    have hppeff : p * p ∈ effects A := ⟨hpp0, (mul_self_le_self hp).trans hp.2⟩
    have hfle : floor p ≤ p * p := by
      have h := ((projection_below_effect p (floor p) hp hf).out 0 5).mp (floor_le hp)
      rwa [sq] at h
    have hfpp : floor (p * p) = floor p := by
      refine le_antisymm ?_ ((floor_isGreatest hppeff).2 ⟨hf, hfle⟩)
      exact (floor_isGreatest hp).2
        ⟨(floor_spec hppeff).1, (floor_le hppeff).trans (mul_self_le_self hp)⟩
    have hsqpp : CFC.sqrt (p * p - floor p) = p - floor p := by
      have hexp : p * p - floor p = (p - floor p) * (p - floor p) := by
        rw [sub_mul, mul_sub, mul_sub, hfp, hpf, hff]; abel
      rw [hexp, CFC.sqrt_mul_self _ hsub]
    -- the two sides
    rw [hopp, hop (p * p) q, hfpp, hsqpp, hop p (op p q), hop p q]
    calc floor p * (floor p * q * floor p +
          CFC.sqrt (p - floor p) * q * CFC.sqrt (p - floor p)) * floor p +
          CFC.sqrt (p - floor p) * (floor p * q * floor p +
            CFC.sqrt (p - floor p) * q * CFC.sqrt (p - floor p)) *
            CFC.sqrt (p - floor p)
        = (floor p * floor p) * q * (floor p * floor p) +
            (floor p * CFC.sqrt (p - floor p)) * q *
              (CFC.sqrt (p - floor p) * floor p) +
            ((CFC.sqrt (p - floor p) * floor p) * q *
                (floor p * CFC.sqrt (p - floor p)) +
              (CFC.sqrt (p - floor p) * CFC.sqrt (p - floor p)) * q *
                (CFC.sqrt (p - floor p) * CFC.sqrt (p - floor p))) := by noncomm_ring
      _ = floor p * q * floor p + (p - floor p) * q * (p - floor p) := by
          rw [hff, hfs, hsf, hss]; simp
  · -- (D): `q ∗ q = q²`, so `p = √p ∗ √p`
    intro p hp
    refine ⟨CFC.sqrt p, sqrt_mem_effects hp, ?_⟩
    obtain ⟨hf, hfq, -, -, hss, -, -, -, hqs⟩ := basics _ (sqrt_mem_effects hp)
    rw [hop]
    have e1 : floor (CFC.sqrt p) * CFC.sqrt p * floor (CFC.sqrt p) = floor (CFC.sqrt p) := by
      rw [hfq, hf.isIdempotentElem.eq]
    have e2 : CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p)) * CFC.sqrt p *
        CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p))
          = CFC.sqrt p * CFC.sqrt p - floor (CFC.sqrt p) := by
      calc CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p)) * CFC.sqrt p *
            CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p))
          = CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p)) *
              (CFC.sqrt p * CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p))) := by noncomm_ring
        _ = CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p)) *
              CFC.sqrt (CFC.sqrt p - floor (CFC.sqrt p)) * CFC.sqrt p := by
            rw [hqs]; noncomm_ring
        _ = CFC.sqrt p * CFC.sqrt p - floor (CFC.sqrt p) := by rw [hss, sub_mul, hfq]
    rw [e1, e2, CFC.sqrt_mul_sqrt_self p hp.1]
    abel
  · -- (E): `p ∗ e₁ ≤ e₂^⊥` iff `e₁fe₂ = 0` and `e₁se₂ = 0`, which is symmetric
    intro p hp e₁ e₂ h₁ h₂
    obtain ⟨hf, hfp, hpf, hsub, hss, hssa, hfs, hsf, hps⟩ := basics p hp
    have hfsa : star (floor p) = floor p := hf.isSelfAdjoint.star_eq
    -- for an effect `x` and a projection `e`: `x ≤ e^⊥` iff `exe = 0`
    have hiff : ∀ x : A, 0 ≤ x → x ≤ 1 → ∀ e : A, IsStarProjection e →
        (x ≤ 1 - e ↔ e * x * e = 0) := by
      intro x hx hx1 e he
      constructor
      · intro h
        have h1 : e * x * e ≤ e * (1 - e) * e := by
          have := star_left_conjugate_le_conjugate h e
          rwa [he.isSelfAdjoint.star_eq] at this
        have h2 : e * (1 - e) * e = 0 := by
          rw [mul_sub, mul_one, he.isIdempotentElem.eq, sub_self, zero_mul]
        have h3 : (0 : A) ≤ e * x * e := by
          have := star_left_conjugate_nonneg hx e
          rwa [he.isSelfAdjoint.star_eq] at this
        exact le_antisymm (h2 ▸ h1) h3
      · intro h
        have hle : ceil x ≤ 1 - e := (ceil_le_perp_iff hx he).mpr h
        have hxe : x * (1 - e) = x := (ceil_le_iff hx he.one_sub).mp hle
        have hex : (1 - e) * x = x :=
          ((ceil_basic_1 x (1 - e) hx he.one_sub).out 2 0).mp hle
        calc x = (1 - e) * x * (1 - e) := by rw [hex, hxe]
          _ ≤ (1 - e) * 1 * (1 - e) := by
              have := star_left_conjugate_le_conjugate hx1 (1 - e)
              rwa [he.one_sub.isSelfAdjoint.star_eq] at this
          _ = 1 - e := by
              rw [mul_one, sub_mul, one_mul, mul_sub, mul_one,
                he.isIdempotentElem.eq]
              abel
    -- `p ∗ e` is an effect, for every projection `e`
    have heff : ∀ e : A, IsStarProjection e → 0 ≤ op p e ∧ op p e ≤ 1 := by
      intro e he
      have hnn1 : (0 : A) ≤ floor p * e * floor p := by
        have := star_left_conjugate_nonneg he.nonneg (floor p)
        rwa [hfsa] at this
      have hnn2 : (0 : A) ≤ CFC.sqrt (p - floor p) * e * CFC.sqrt (p - floor p) := by
        have := star_left_conjugate_nonneg he.nonneg (CFC.sqrt (p - floor p))
        rwa [hssa] at this
      have hle1 : floor p * e * floor p ≤ floor p := by
        have := star_left_conjugate_le_conjugate he.le_one (floor p)
        rw [hfsa, mul_one, hf.isIdempotentElem.eq] at this
        exact this
      have hle2 : CFC.sqrt (p - floor p) * e * CFC.sqrt (p - floor p) ≤ p - floor p := by
        have := star_left_conjugate_le_conjugate he.le_one (CFC.sqrt (p - floor p))
        rw [hssa, mul_one, hss] at this
        exact this
      refine ⟨by rw [hop]; exact add_nonneg hnn1 hnn2, ?_⟩
      rw [hop]
      calc floor p * e * floor p + CFC.sqrt (p - floor p) * e * CFC.sqrt (p - floor p)
          ≤ floor p + (p - floor p) := add_le_add hle1 hle2
        _ = p := by abel
        _ ≤ 1 := hp.2
    -- the characterisation
    have hcancel : ∀ x a b : A, star x = x → IsStarProjection a → IsStarProjection b →
        (b * (x * a * x) * b = 0 ↔ a * x * b = 0) := by
      intro x a b hx ha hb
      have hstar : star (a * x * b) = b * x * a := by
        rw [star_mul, star_mul, hb.isSelfAdjoint.star_eq, hx, ha.isSelfAdjoint.star_eq,
          mul_assoc]
      rw [← CStarRing.star_mul_self_eq_zero_iff (a * x * b), hstar]
      constructor
      · intro h
        calc b * x * a * (a * x * b)
            = b * (x * (a * a) * x) * b := by noncomm_ring
          _ = 0 := by rw [ha.isIdempotentElem.eq]; exact h
      · intro h
        calc b * (x * a * x) * b = b * x * a * (a * x * b) := by
              rw [show b * x * a * (a * x * b) = b * (x * (a * a) * x) * b by noncomm_ring,
                ha.isIdempotentElem.eq]
          _ = 0 := h
    have hchar : ∀ d₁ d₂ : A, IsStarProjection d₁ → IsStarProjection d₂ →
        (op p d₁ ≤ 1 - d₂ ↔ (d₁ * floor p * d₂ = 0 ∧
          d₁ * CFC.sqrt (p - floor p) * d₂ = 0)) := by
      intro d₁ d₂ hd₁ hd₂
      rw [hiff _ (heff d₁ hd₁).1 (heff d₁ hd₁).2 d₂ hd₂, hop]
      have hsplit : d₂ * (floor p * d₁ * floor p +
          CFC.sqrt (p - floor p) * d₁ * CFC.sqrt (p - floor p)) * d₂
          = d₂ * (floor p * d₁ * floor p) * d₂ +
            d₂ * (CFC.sqrt (p - floor p) * d₁ * CFC.sqrt (p - floor p)) * d₂ := by
        noncomm_ring
      have hn1 : (0 : A) ≤ d₂ * (floor p * d₁ * floor p) * d₂ := by
        have h0 : (0 : A) ≤ floor p * d₁ * floor p := by
          have := star_left_conjugate_nonneg hd₁.nonneg (floor p)
          rwa [hfsa] at this
        have := star_left_conjugate_nonneg h0 d₂
        rwa [hd₂.isSelfAdjoint.star_eq] at this
      have hn2 : (0 : A) ≤ d₂ * (CFC.sqrt (p - floor p) * d₁ *
          CFC.sqrt (p - floor p)) * d₂ := by
        have h0 : (0 : A) ≤ CFC.sqrt (p - floor p) * d₁ * CFC.sqrt (p - floor p) := by
          have := star_left_conjugate_nonneg hd₁.nonneg (CFC.sqrt (p - floor p))
          rwa [hssa] at this
        have := star_left_conjugate_nonneg h0 d₂
        rwa [hd₂.isSelfAdjoint.star_eq] at this
      rw [hsplit]
      constructor
      · intro h
        have h1 : d₂ * (floor p * d₁ * floor p) * d₂ = 0 := by
          refine le_antisymm ?_ hn1
          calc d₂ * (floor p * d₁ * floor p) * d₂
              ≤ d₂ * (floor p * d₁ * floor p) * d₂ +
                d₂ * (CFC.sqrt (p - floor p) * d₁ * CFC.sqrt (p - floor p)) * d₂ :=
                le_add_of_nonneg_right hn2
            _ = 0 := h
        have h2 : d₂ * (CFC.sqrt (p - floor p) * d₁ * CFC.sqrt (p - floor p)) * d₂ = 0 := by
          rw [h1, zero_add] at h
          exact h
        exact ⟨(hcancel (floor p) d₁ d₂ hfsa hd₁ hd₂).mp h1,
          (hcancel _ d₁ d₂ hssa hd₁ hd₂).mp h2⟩
      · rintro ⟨h1, h2⟩
        rw [(hcancel (floor p) d₁ d₂ hfsa hd₁ hd₂).mpr h1,
          (hcancel _ d₁ d₂ hssa hd₁ hd₂).mpr h2, add_zero]
    have hsym : ∀ x a b : A, star x = x → IsStarProjection a → IsStarProjection b →
        a * x * b = 0 → b * x * a = 0 := by
      intro x a b hx ha hb h
      have := congrArg star h
      rwa [star_mul, star_mul, hb.isSelfAdjoint.star_eq, hx, ha.isSelfAdjoint.star_eq,
        ← mul_assoc, star_zero] at this
    rw [hchar e₁ e₂ h₁ h₂, hchar e₂ e₁ h₂ h₁]
    exact ⟨fun h => ⟨hsym _ _ _ hfsa h₁ h₂ h.1, hsym _ _ _ hssa h₁ h₂ h.2⟩,
      fun h => ⟨hsym _ _ _ hfsa h₂ h₁ h.1, hsym _ _ _ hssa h₂ h₁ h.2⟩⟩

/-! ### **106III**.2: axiom (B) does fail

Part 2 asks one to show that
`p ∗ q := ⌊p⌋q⌊p⌋ + √(p−⌊p⌋) q √(p−⌊p⌋)` satisfies every axiom of 106I
**except** (B) — so half the content of the part is that (B) *fails*, which
is what makes (B) independent of the rest.  `sequential_product_counterexample_2`
above supplies (A), (C), (D) and (E); this section supplies the failure.

The witness is `B(ℂ²)` at `p = e + ½e^⊥` for a rank-one projection `e`.
There `⌊p⌋ = e` and `p − ⌊p⌋ = ½e^⊥`, so `√(p−⌊p⌋)` lies in `e^⊥𝒜e^⊥` and
`p ∗ q` depends on `q` only through `eqe` and `e^⊥qe^⊥` — hence is **not
injective**, the two rank-one projections onto `ℂ(1,1)` and `ℂ(1,−1)`
having the same image.  It is, however, **faithful**.  And a faithful pure
map is a filter (**100VII**.1), while a filter is injective (**98II**.2). -/

/-- The floor of `e + t·e^⊥` is `e`, for a projection `e` and `0 ≤ t < 1`:
a projection `w` below `e + te^⊥` satisfies `(e + te^⊥)w = w`, which forces
`(1−t)·e^⊥w = 0` and hence `ew = w`. -/
private theorem effects_and_floor_proj_add_smul [VonNeumannAlgebra A] {e : A}
    (he : IsStarProjection e) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    e + (t : ℂ) • (1 - e) ∈ effects A ∧ floor (e + (t : ℂ) • (1 - e)) = e := by
  set p : A := e + (t : ℂ) • (1 - e) with hpdef
  have hpe : p - e = (t : ℂ) • (1 - e) := by rw [hpdef]; abel
  have hp0 : (0 : A) ≤ p :=
    add_nonneg he.nonneg (Theses.A.CStar.ofReal_smul_nonneg he.one_sub.nonneg ht0)
  have hp1 : p ≤ 1 := by
    rw [← sub_nonneg, show (1 : A) - p = ((1 - t : ℝ) : ℂ) • (1 - e) by
      rw [hpdef]; push_cast; module]
    exact Theses.A.CStar.ofReal_smul_nonneg he.one_sub.nonneg (by linarith)
  have hpeff : p ∈ effects A := ⟨hp0, hp1⟩
  have hep : e ≤ p := by
    rw [← sub_nonneg, hpe]
    exact Theses.A.CStar.ofReal_smul_nonneg he.one_sub.nonneg ht0
  refine ⟨hpeff, ((floor_isGreatest hpeff).unique ⟨⟨he, hep⟩, ?_⟩)⟩
  rintro w ⟨hw, hwp⟩
  have hpw : p * w = w := ((projection_below_effect p w hpeff hw).out 0 6).mp hwp
  have hsplit : w = e * w + (1 - e) * w := by
    rw [← add_mul, show e + (1 - e) = (1 : A) by abel, one_mul]
  have hexp : p * w = e * w + (t : ℂ) • ((1 - e) * w) := by
    rw [hpdef, add_mul, smul_mul_assoc]
  have hkey : (t : ℂ) • ((1 - e) * w) = (1 - e) * w := by
    refine add_left_cancel (a := e * w) ?_
    rw [← hexp, hpw]
    exact hsplit
  have hzero : (1 - e) * w = 0 := by
    have hy : ((1 : ℂ) - (t : ℂ)) • ((1 - e) * w) = 0 := by
      rw [sub_smul, one_smul, hkey, sub_self]
    refine (smul_eq_zero.mp hy).resolve_left ?_
    intro hc
    exact absurd (Complex.ofReal_eq_one.mp (sub_eq_zero.mp hc).symm) (by linarith)
  have hew : e * w = w := by
    conv_rhs => rw [hsplit]
    rw [hzero, add_zero]
  exact ((projection_below_effect e w ⟨he.nonneg, he.le_one⟩ hw).out 6 0).mp hew

section SPC2

private abbrev spc2B := EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)

private abbrev spc2T (M : Matrix (Fin 2) (Fin 2) ℂ) : spc2B :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

private theorem spc2_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    spc2T M * spc2T N = spc2T (M * N) := (map_mul _ _ _).symm

private theorem spc2_star (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (spc2T M) = spc2T (star M) := (map_star _ _).symm

private theorem spc2_one : spc2T 1 = 1 := map_one _

private theorem spc2_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    spc2T M - spc2T N = spc2T (M - N) := (map_sub _ _ _).symm

private theorem spc2_inj {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : spc2T M = spc2T N) :
    M = N := Matrix.toEuclideanCLM.injective h

private def spc2E : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private def spc2S : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]
private def spc2S' : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, -1/2; -1/2, 1/2]

private theorem spc2_facts :
    spc2E * spc2E = spc2E ∧ star spc2E = spc2E ∧
      spc2S * spc2S = spc2S ∧ star spc2S = spc2S ∧
      spc2S' * spc2S' = spc2S' ∧ star spc2S' = spc2S' ∧
      spc2E * spc2S * spc2E = spc2E * spc2S' * spc2E ∧
      (1 - spc2E) * spc2S * (1 - spc2E) = (1 - spc2E) * spc2S' * (1 - spc2E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [spc2E, spc2S, spc2S', Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
          Matrix.one_apply, Matrix.sub_apply] <;>
        norm_num

private theorem spc2_S_ne : spc2S ≠ spc2S' := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [spc2S, spc2S'] at h01
  norm_num at h01

/-- **106III** (proc.tex:1858, Exercise), part 2, the **failing** axiom:
there is a von Neumann algebra and an effect `p` of it for which
`q ↦ ⌊p⌋q⌊p⌋ + √(p−⌊p⌋) q √(p−⌊p⌋)` is **not** given by any pure map — so
axiom (B) does not follow from (A), (C), (D), (E), which is the point of
part 2.

Witness: `B(ℂ²)` at `p = e + ½e^⊥`, `e` the projection onto `ℂ(1,0)`.  The
operation is then `q ↦ eqe + ½e^⊥qe^⊥`.  It is faithful (a positive `x`
with `exe = 0 = e^⊥xe^⊥` is `0`), so a pure map computing it would be a
filter by **100VII**.1 and hence injective by **98II**.2; but it sends the
projections onto `ℂ(1,1)` and `ℂ(1,−1)` to the same element. -/
theorem sequential_product_counterexample_2_ax2_is_false :
    ∃ p ∈ effects spc2B,
      ¬ ∃ f : NCPMap spc2B spc2B, IsPure f ∧
        ∀ q ∈ effects spc2B, floor p * q * floor p +
          CFC.sqrt (p - floor p) * q * CFC.sqrt (p - floor p) = f q := by
  obtain ⟨hEE, hEs, hSS, hSs, hS'S', hS's, hES, hE'S⟩ := spc2_facts
  set e : spc2B := spc2T spc2E with hedef
  have he : IsStarProjection e :=
    ⟨show e * e = e by rw [hedef, spc2_mul, hEE],
      show star e = e by rw [hedef, spc2_star, hEs]⟩
  have hesa : star e = e := he.isSelfAdjoint.star_eq
  set p : spc2B := e + (((1 / 2 : ℝ)) : ℂ) • (1 - e) with hpdef
  obtain ⟨hpeff, hfloor⟩ :=
    effects_and_floor_proj_add_smul he (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨p, hpeff, ?_⟩
  rintro ⟨f, hpure, hf⟩
  -- `√(p − ⌊p⌋)` lives in `e^⊥𝒜e^⊥`
  set s : spc2B := CFC.sqrt (p - floor p) with hsdef
  have hpe : p - floor p = (((1 / 2 : ℝ)) : ℂ) • (1 - e) := by
    rw [hfloor, hpdef]; abel
  have hpe0 : (0 : spc2B) ≤ p - floor p := by
    rw [hpe]
    exact Theses.A.CStar.ofReal_smul_nonneg he.one_sub.nonneg (by norm_num)
  have hsa : star s = s := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  have hss : s * s = (((1 / 2 : ℝ)) : ℂ) • (1 - e) := by
    rw [hsdef, CFC.sqrt_mul_sqrt_self _ hpe0, hpe]
  have hse : s * e = 0 := by
    refine (CStarRing.star_mul_self_eq_zero_iff (s * e)).mp ?_
    rw [star_mul, hsa, hesa]
    calc e * s * (s * e) = e * (s * s) * e := by noncomm_ring
      _ = 0 := by
          rw [hss, mul_smul_comm, smul_mul_assoc,
            show e * (1 - e) * e = 0 by
              rw [mul_sub, mul_one, he.isIdempotentElem.eq, sub_self, zero_mul],
            smul_zero]
  have hs1e : s * (1 - e) = s := by rw [mul_sub, mul_one, hse, sub_zero]
  have hes : (1 - e) * s = s := by
    have h := congrArg star hs1e
    rwa [star_mul, hsa, he.one_sub.isSelfAdjoint.star_eq] at h
  -- the operation, written out
  have hop : ∀ q : spc2B, floor p * q * floor p + s * q * s
      = e * q * e + s * q * s := by intro q; rw [hfloor]
  -- it depends on `q` only through `eqe` and `e^⊥qe^⊥`
  have hconj : ∀ q : spc2B, s * q * s = s * ((1 - e) * q * (1 - e)) * s := by
    intro q
    calc s * q * s = (s * (1 - e)) * q * ((1 - e) * s) := by rw [hs1e, hes]
      _ = s * ((1 - e) * q * (1 - e)) * s := by noncomm_ring
  -- faithfulness: `exe = 0 = sxs` forces `x = 0` for positive `x`
  have hkill : ∀ (y x : spc2B), star y = y → 0 ≤ x → y * x * y = 0 → x * y = 0 := by
    intro y x hy hx h
    have hxs : star (CFC.sqrt x * y) * (CFC.sqrt x * y) = y * x * y := by
      rw [star_mul, hy, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq]
      calc y * CFC.sqrt x * (CFC.sqrt x * y)
          = y * (CFC.sqrt x * CFC.sqrt x) * y := by noncomm_ring
        _ = y * x * y := by rw [CFC.sqrt_mul_sqrt_self x hx]
    have h0 : CFC.sqrt x * y = 0 :=
      (CStarRing.star_mul_self_eq_zero_iff _).mp (by rw [hxs]; exact h)
    calc x * y = CFC.sqrt x * (CFC.sqrt x * y) := by
          rw [← mul_assoc, CFC.sqrt_mul_sqrt_self x hx]
      _ = 0 := by rw [h0, mul_zero]
  have hfaith : ncpCarrier f = 1 := by
    have hcspec := (exists_ncpCarrier f).choose_spec.1
    have hcproj : IsStarProjection (ncpCarrier f) := isStarProjection_ncpCarrier f
    set x : spc2B := 1 - ncpCarrier f with hxdef
    have hxproj : IsStarProjection x := hcproj.one_sub
    have hx : (0 : spc2B) ≤ x := hxproj.nonneg
    have hsum : e * x * e + s * x * s = 0 := by
      rw [← hop x, hf x ⟨hxproj.nonneg, hxproj.le_one⟩]
      exact hcspec.2.1
    have hnn1 : (0 : spc2B) ≤ e * x * e := by
      have h := star_left_conjugate_nonneg hx e; rwa [hesa] at h
    have hnn2 : (0 : spc2B) ≤ s * x * s := by
      have h := star_left_conjugate_nonneg hx s; rwa [hsa] at h
    have hz1 : e * x * e = 0 := by
      refine le_antisymm ?_ hnn1
      have h : e * x * e ≤ e * x * e + s * x * s := le_add_of_nonneg_right hnn2
      rwa [hsum] at h
    have hz2 : s * x * s = 0 := by
      refine le_antisymm ?_ hnn2
      have h : s * x * s ≤ e * x * e + s * x * s := le_add_of_nonneg_left hnn1
      rwa [hsum] at h
    have hxe : x * e = 0 := hkill e x hesa hx hz1
    have hxs : x * s = 0 := hkill s x hsa hx hz2
    have hx1e : x * (1 - e) = 0 := by
      have h1 : x * (s * s) = 0 := by rw [← mul_assoc, hxs, zero_mul]
      rw [hss, mul_smul_comm] at h1
      refine (smul_eq_zero.mp h1).resolve_left ?_
      simp
    have hx0 : x = 0 := by
      calc x = x * e + x * (1 - e) := by rw [← mul_add, show e + (1 - e) = (1 : spc2B) by abel, mul_one]
        _ = 0 := by rw [hxe, hx1e, add_zero]
    have := sub_eq_zero.mp hx0
    exact this.symm
  -- a faithful pure map is a filter (100VII.1), and a filter is injective (98II.2)
  have hinj : Function.Injective ⇑f :=
    (filter_basic_2 f (special_pure_maps_1 f hpure hfaith)).1
  -- but the two projections onto `ℂ(1,1)` and `ℂ(1,−1)` collide
  set q₁ : spc2B := spc2T spc2S with hq1def
  set q₂ : spc2B := spc2T spc2S' with hq2def
  have hq1 : IsStarProjection q₁ :=
    ⟨show q₁ * q₁ = q₁ by rw [hq1def, spc2_mul, hSS],
      show star q₁ = q₁ by rw [hq1def, spc2_star, hSs]⟩
  have hq2 : IsStarProjection q₂ :=
    ⟨show q₂ * q₂ = q₂ by rw [hq2def, spc2_mul, hS'S'],
      show star q₂ = q₂ by rw [hq2def, spc2_star, hS's]⟩
  have hone : (1 : spc2B) - e = spc2T (1 - spc2E) := by
    rw [hedef, ← spc2_one, spc2_sub]
  have hcorner : e * q₁ * e = e * q₂ * e := by
    rw [hedef, hq1def, hq2def, spc2_mul, spc2_mul, spc2_mul, spc2_mul, hES]
  have hcorner' : (1 - e) * q₁ * (1 - e) = (1 - e) * q₂ * (1 - e) := by
    rw [hone, hq1def, hq2def, spc2_mul, spc2_mul, spc2_mul, spc2_mul, hE'S]
  have hcollide : (f q₁ : spc2B) = f q₂ := by
    rw [← hf q₁ ⟨hq1.nonneg, hq1.le_one⟩, ← hf q₂ ⟨hq2.nonneg, hq2.le_one⟩,
      hop q₁, hop q₂, hconj q₁, hconj q₂, hcorner, hcorner']
  exact spc2_S_ne (spc2_inj (hinj hcollide))

end SPC2

/-! ### Infrastructure for the 106III.3 counterexample: `B(ℂ²)`

The witnesses live in `B(ℂ²) = M₂(ℂ)`, transported from matrices along the
`*`-isomorphism `Matrix.toEuclideanCLM`.  All the numbers are rational
(`s = diag(1, 3/5)`, `p = s² = diag(1, 9/25)`, `1 − p = diag(0, 4/5)²`), so
the matrix identities are `norm_num` computations; only the positivity of
`s` needs an irrational entry (`s = diag(1,√(3/5))*diag(1,√(3/5))`). -/

section SPC3

private abbrev spc3B := EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)

private abbrev spc3T (M : Matrix (Fin 2) (Fin 2) ℂ) : spc3B :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

private theorem spc3_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    spc3T M * spc3T N = spc3T (M * N) := (map_mul _ _ _).symm

private theorem spc3_star (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (spc3T M) = spc3T (star M) := (map_star _ _).symm

private theorem spc3_one : spc3T 1 = 1 := map_one _

private theorem spc3_zero : spc3T 0 = 0 := map_zero _

private theorem spc3_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    spc3T M - spc3T N = spc3T (M - N) := (map_sub _ _ _).symm

private theorem spc3_inj {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : spc3T M = spc3T N) :
    M = N := Matrix.toEuclideanCLM.injective h

private def spc3S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 3/5]
private def spc3P : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 9/25]
private def spc3V : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
private def spc3W : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 4/5]
private def spc3Pi : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 25/9]
private def spc3E1 : Matrix (Fin 2) (Fin 2) ℂ := !![25/34, -15/34; -15/34, 9/34]
private def spc3E2 : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]

private theorem spc3_SS : spc3S * spc3S = spc3P := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3S, spc3P, Matrix.mul_apply, Fin.sum_univ_two]

private theorem spc3_Sstar : star spc3S = spc3S := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [spc3S, Matrix.star_apply]

private theorem spc3_Vstar : star spc3V = spc3V := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [spc3V, Matrix.star_apply]

private theorem spc3_VV : spc3V * spc3V = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3V, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem spc3_PiP : spc3Pi * spc3P = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3P, spc3Pi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem spc3_WW : star spc3W * spc3W = 1 - spc3P := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3W, spc3P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.star_apply, Matrix.sub_apply, map_div₀, map_ofNat]

private theorem spc3_E1E1 : spc3E1 * spc3E1 = spc3E1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3E1, Matrix.mul_apply, Fin.sum_univ_two]

private theorem spc3_E1star : star spc3E1 = spc3E1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [spc3E1, Matrix.star_apply]

private theorem spc3_E2E2 : spc3E2 * spc3E2 = spc3E2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3E2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem spc3_E2star : star spc3E2 = spc3E2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [spc3E2, Matrix.star_apply]

private theorem spc3_zeroprod : spc3E1 * (spc3V * spc3S) * spc3E2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3E1, spc3E2, spc3V, spc3S, Matrix.mul_apply, Fin.sum_univ_two]

private theorem spc3_nonzeroprod : spc3E2 * (spc3V * spc3S) * spc3E1 ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [spc3E1, spc3E2, spc3V, spc3S, Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem spc3_S0 : ∃ T0 : Matrix (Fin 2) (Fin 2) ℂ, star T0 * T0 = spc3S := by
  obtain ⟨r, -, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) * (r : ℂ) = (3/5 : ℂ) := by
    refine ⟨Real.sqrt (3/5), Real.sqrt_nonneg _, ?_⟩
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  refine ⟨!![1, 0; 0, (r : ℂ)], ?_⟩
  have hrc : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [spc3S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hrc, hr]

open scoped Classical in
/-- **106III** (proc.tex:1858, Exercise), part 3: its claim that `∗` obeys
axiom (E) as soon as `u_p^* = u_p` is **FALSE as printed**; this is the
counterexample.  Work in `𝒜 = B(ℂ²)`, put `p := diag(1, 9/25)` (so
`⌈p⌉ = 1` and `√p = diag(1, 3/5)`), and take the family `u_p := ` the flip
`!![0,1;1,0]` at that one `p` and `u_x := ⌈x⌉` at every other effect `x`:
every `u_x` is a self-adjoint unitary of `⌈x⌉𝒜⌈x⌉`.  With
`a := u_p√p = !![0,3/5;1,0]`, axiom (E) at `p` says
`e₁ a e₂ = 0 ⟺ e₂ a e₁ = 0` for all projections `e₁, e₂`, i.e. that `a`
and `a^*` have the same zero pattern; at the rank-one projections onto
`(5,−3)` and `(1,1)` it fails.

What (E) needs is not `u_p^* = u_p` but `p u_p = u_p p` — the hypothesis
the exercise attaches to (D) — for then `a = u_p√p` is *normal*, which is
what makes the two sides of (E) star-conjugate.  (The same is true of the
claim about axiom (C): `p ∗ (p ∗ q)` is `Ad` at `u_p√p u_p√p` and
`(p ∗ p) ∗ q` is `Ad` at `u_{p∗p}√(p∗p)`, and `u_p² = u_{p²}` identifies
the two only when `u_p` commutes with `p`, since only then is
`p ∗ p = p²`.  Refuting (C) needs a family that also meets `u_x² = u_{x²}`
along the *backward* chain `x, √x, ⁴√x, …` of the modified point, so it is
not formalized here.)  Both slips are harmless for the exercise's own
conclusion, where `u_p = g(p)` is a Borel function of `p`. -/
theorem sequential_product_counterexample_3_ax5_is_false :
    ∃ u : (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) →
        (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
      (∀ p ∈ effects (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
          u p ∈ cornerSet (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
            (ceil p) ∧
          star (u p) * u p = ceil p ∧ u p * star (u p) = ceil p) ∧
      (∀ p ∈ effects (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
          star (u p) = u p) ∧
      ¬ (∀ p ∈ effects (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
          ∀ e₁ e₂ : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
          IsStarProjection e₁ → IsStarProjection e₂ →
          (CFC.sqrt p * star (u p) * e₁ * u p * CFC.sqrt p ≤ 1 - e₂ ↔
            CFC.sqrt p * star (u p) * e₂ * u p * CFC.sqrt p ≤ 1 - e₁)) := by
  classical
  set s : spc3B := spc3T spc3S with hs_def
  set p : spc3B := spc3T spc3P with hp_def
  set v : spc3B := spc3T spc3V with hv_def
  set d1 : spc3B := spc3T spc3E1 with hd1_def
  set d2 : spc3B := spc3T spc3E2 with hd2_def
  have hs0 : (0 : spc3B) ≤ s := by
    obtain ⟨T0, hT0⟩ := spc3_S0
    have h := star_mul_self_nonneg (spc3T T0)
    rwa [spc3_star, spc3_mul, hT0] at h
  have hssa : star s = s := by rw [hs_def, spc3_star, spc3_Sstar]
  have hss : s * s = p := by rw [hs_def, hp_def, spc3_mul, spc3_SS]
  have hp0 : (0 : spc3B) ≤ p := by
    have h := star_mul_self_nonneg s
    rwa [hssa, hss] at h
  have hp1 : p ≤ 1 := by
    refine sub_nonneg.mp ?_
    have h := star_mul_self_nonneg (spc3T spc3W)
    rwa [spc3_star, spc3_mul, spc3_WW, ← spc3_sub, spc3_one, ← hp_def] at h
  have hsqrt : CFC.sqrt p = s := by rw [← hss]; exact CFC.sqrt_mul_self s hs0
  have hceil : ceil p = 1 := by
    have hpi : spc3T spc3Pi * p = 1 := by rw [hp_def, spc3_mul, spc3_PiP, spc3_one]
    have h1 : p * ceil p = p := (ceil_spec hp0).2.1
    calc ceil p = 1 * ceil p := (one_mul _).symm
      _ = spc3T spc3Pi * p * ceil p := by rw [hpi]
      _ = spc3T spc3Pi * (p * ceil p) := by rw [mul_assoc]
      _ = spc3T spc3Pi * p := by rw [h1]
      _ = 1 := hpi
  have hvsa : star v = v := by rw [hv_def, spc3_star, spc3_Vstar]
  have hvv : v * v = 1 := by rw [hv_def, spc3_mul, spc3_VV, spc3_one]
  have he1 : IsStarProjection d1 :=
    ⟨show d1 * d1 = d1 by rw [hd1_def, spc3_mul, spc3_E1E1],
      show star d1 = d1 by rw [hd1_def, spc3_star, spc3_E1star]⟩
  have he2 : IsStarProjection d2 :=
    ⟨show d2 * d2 = d2 by rw [hd2_def, spc3_mul, spc3_E2E2],
      show star d2 = d2 by rw [hd2_def, spc3_star, spc3_E2star]⟩
  have hastar : star (v * s) = s * v := by rw [star_mul, hssa, hvsa]
  have haa : star (v * s) * (v * s) = p := by
    rw [hastar]
    calc s * v * (v * s) = s * (v * v) * s := by noncomm_ring
      _ = p := by rw [hvv, mul_one, hss]
  have hz1 : d1 * (v * s) * d2 = 0 := by
    rw [hd1_def, hv_def, hs_def, hd2_def, spc3_mul, spc3_mul, spc3_mul, spc3_zeroprod,
      spc3_zero]
  have hz2 : d2 * (v * s) * d1 ≠ 0 := by
    rw [hd2_def, hv_def, hs_def, hd1_def, spc3_mul, spc3_mul, spc3_mul]
    intro h
    exact spc3_nonzeroprod (spc3_inj (by rw [h, spc3_zero]))
  have heff : ∀ e : spc3B, IsStarProjection e →
      (0 : spc3B) ≤ star (v * s) * e * (v * s) ∧ star (v * s) * e * (v * s) ≤ 1 := by
    intro e he
    refine ⟨star_left_conjugate_nonneg he.nonneg _, ?_⟩
    calc star (v * s) * e * (v * s) ≤ star (v * s) * 1 * (v * s) :=
          star_left_conjugate_le_conjugate he.le_one _
      _ = p := by rw [mul_one, haa]
      _ ≤ 1 := hp1
  have hiff : ∀ x : spc3B, 0 ≤ x → x ≤ 1 → ∀ e : spc3B, IsStarProjection e →
      (x ≤ 1 - e ↔ e * x * e = 0) := by
    intro x hx hx1 e he
    constructor
    · intro h
      have h1 : e * x * e ≤ e * (1 - e) * e := by
        have := star_left_conjugate_le_conjugate h e
        rwa [he.isSelfAdjoint.star_eq] at this
      have h2 : e * (1 - e) * e = 0 := by
        rw [mul_sub, mul_one, he.isIdempotentElem.eq, sub_self, zero_mul]
      have h3 : (0 : spc3B) ≤ e * x * e := by
        have := star_left_conjugate_nonneg hx e
        rwa [he.isSelfAdjoint.star_eq] at this
      exact le_antisymm (h2 ▸ h1) h3
    · intro h
      have hle : ceil x ≤ 1 - e := (ceil_le_perp_iff hx he).mpr h
      have hxe : x * (1 - e) = x := (ceil_le_iff hx he.one_sub).mp hle
      have hex : (1 - e) * x = x :=
        ((ceil_basic_1 x (1 - e) hx he.one_sub).out 2 0).mp hle
      calc x = (1 - e) * x * (1 - e) := by rw [hex, hxe]
        _ ≤ (1 - e) * 1 * (1 - e) := by
            have := star_left_conjugate_le_conjugate hx1 (1 - e)
            rwa [he.one_sub.isSelfAdjoint.star_eq] at this
        _ = 1 - e := by
            rw [mul_one, sub_mul, one_mul, mul_sub, mul_one, he.isIdempotentElem.eq]
            abel
  have hsand : ∀ x y : spc3B, IsStarProjection x → IsStarProjection y →
      y * (star (v * s) * x * (v * s)) * y
        = star (x * (v * s) * y) * (x * (v * s) * y) := by
    intro x y hx hy
    have hstar' : star (x * (v * s) * y) = y * star (v * s) * x := by
      rw [star_mul, star_mul, hy.isSelfAdjoint.star_eq, hx.isSelfAdjoint.star_eq,
        mul_assoc]
    rw [hstar']
    calc y * (star (v * s) * x * (v * s)) * y
        = y * star (v * s) * (x * x) * (v * s) * y := by
          rw [hx.isIdempotentElem.eq]; noncomm_ring
      _ = y * star (v * s) * x * (x * (v * s) * y) := by noncomm_ring
  set u : spc3B → spc3B := fun x => if x = p then v else ceil x with hu_def
  have hup : u p = v := by simp [hu_def]
  have hux : ∀ x : spc3B, x ≠ p → u x = ceil x := by intro x hx; simp [hu_def, hx]
  refine ⟨u, ?_, ?_, ?_⟩
  · intro x _
    by_cases hxp : x = p
    · rw [hxp, hup, hceil]
      exact ⟨show (1 : spc3B) * v * 1 = v by rw [one_mul, mul_one], by rw [hvsa, hvv],
        by rw [hvsa, hvv]⟩
    · rw [hux x hxp]
      have hc : IsStarProjection (ceil x) := isStarProjection_ceil x
      exact ⟨show ceil x * ceil x * ceil x = ceil x by
          rw [hc.isIdempotentElem.eq, hc.isIdempotentElem.eq],
        by rw [hc.isSelfAdjoint.star_eq, hc.isIdempotentElem.eq],
        by rw [hc.isSelfAdjoint.star_eq, hc.isIdempotentElem.eq]⟩
  · intro x _
    by_cases hxp : x = p
    · rw [hxp, hup]; exact hvsa
    · rw [hux x hxp]; exact (isStarProjection_ceil x).isSelfAdjoint.star_eq
  · intro hE
    have hEp := hE p ⟨hp0, hp1⟩ d1 d2 he1 he2
    rw [hup, hsqrt, hvsa] at hEp
    have hshape : ∀ e : spc3B, s * v * e * v * s = star (v * s) * e * (v * s) := by
      intro e; rw [hastar]; noncomm_ring
    rw [hshape, hshape] at hEp
    have hfwd : star (v * s) * d1 * (v * s) ≤ 1 - d2 := by
      refine (hiff _ (heff d1 he1).1 (heff d1 he1).2 d2 he2).mpr ?_
      rw [hsand d1 d2 he1 he2, hz1]
      simp
    have hbad := (hiff _ (heff d2 he2).1 (heff d2 he2).2 d1 he1).mp (hEp.mp hfwd)
    rw [hsand d2 d1 he2 he1] at hbad
    exact hz2 ((CStarRing.star_mul_self_eq_zero_iff _).mp hbad)

end SPC3

/-- **106III** (proc.tex:1858, Exercise), part 3: for a family `u` of
unitaries `u_p` of the corners `⌈p⌉𝒜⌈p⌉`, the operation
`p ∗ q := √p u_p* q u_p √p` satisfies (A) and (B); it moreover satisfies
(C) when `u_p² = u_{p²}`, (D) when `p u_p = u_p p`, and (E) when
`u_p* = u_p`.

**Parked: the (E) clause is false as printed** — see
`sequential_product_counterexample_3_ax5_is_false` just above, and the
analysis of the (C) clause in its doc comment (also false, and for the
same reason: both need `p u_p = u_p p`).  (A), (B) and (D) are fine:
(A) is `√p u_p* u_p √p = √p ⌈p⌉ √p = p`, (B) is `Ad` at `u_p√p`
(`isPure_adSelf`), and (D) is `q ∗ q = q²` at `q = √p`, using the
commutation hypothesis attached to it.  The statement is left untouched
pending the author's ruling. -/
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


