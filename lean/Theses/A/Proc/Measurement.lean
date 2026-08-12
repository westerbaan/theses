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
  (with unit `e`, 94II parts 5–8) is *asserted* by `sorry`-ed instances;
  the coherence with the operations of `A` is pinned down by the sorry-ed
  parts of `corner_vna_basic`.
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

/-- Infrastructure: the identity map is an ncp-map (cf. 100II part 2);
stated as an existence lemma from which `ncpId` is obtained by choice. -/
theorem exists_ncpId (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : ∃ f : NCPMap A A, ∀ a : A, f a = a := sorry

/-- The identity ncp-map. -/
noncomputable def ncpId (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : NCPMap A A := (exists_ncpId A).choose

theorem ncpId_apply (a : A) : ncpId A a = a := (exists_ncpId A).choose_spec a

/-- Infrastructure: ncp-maps are closed under composition; stated as an
existence lemma from which `ncpComp` is obtained by choice. -/
theorem exists_ncpComp (g : NCPMap B C) (f : NCPMap A B) :
    ∃ h : NCPMap A C, ∀ a : A, h a = g (f a) := sorry

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
      ∀ q : A, IsStarProjection q → f (1 - q) = 0 → p ≤ q := sorry

/-- The carrier `⌈f⌉` of an ncp-map between von Neumann algebras (least
projection `p` with `f(p^⊥) = 0`), by choice from `exists_ncpCarrier`. -/
noncomputable def ncpCarrier [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) : A := (exists_ncpCarrier f).choose

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
with unit `e`; those instances are asserted below with `sorry`. -/
structure Corner (e : A) : Type u where
  /-- The underlying element of `A`. -/
  val : A
  /-- Membership in the corner: `e·val·e = val`. -/
  property : e * val * e = val

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 5: the
corner `e𝒜e` is a C*-algebra (with the operations of `A` and unit `e`). -/
noncomputable instance (e : A) : CStarAlgebra (Corner A e) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), parts 5–6: the
canonical (Loewner) partial order on the corner `e𝒜e`. -/
noncomputable instance (e : A) : PartialOrder (Corner A e) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), parts 5–6: the
order on the corner `e𝒜e` is the star-order. -/
instance (e : A) : StarOrderedRing (Corner A e) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 8
(conclusion): the corner `e𝒜e` of a von Neumann algebra is a von Neumann
algebra. -/
instance (e : A) [VonNeumannAlgebra A] : VonNeumannAlgebra (Corner A e) :=
  sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 1: for a
projection `e`, an `a ∈ A` is of the form `e·b·e` iff `e·a·e = a` iff both
the support and range projections `⌈a⌉ᵣ, ⌈a⌉ₗ` lie below `e`. -/
theorem corner_vna_basic_1 [VonNeumannAlgebra A] (e a : A)
    (he : IsStarProjection e) :
    ((∃ b : A, a = e * b * e) ↔ a ∈ cornerSet A e) ∧
      (a ∈ cornerSet A e ↔ suppProj a ≤ e ∧ rangeProj a ≤ e) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 2: the
corner `e𝒜e` is closed under addition, scalar multiplication,
multiplication and involution. -/
theorem corner_vna_basic_2 (e : A) (he : IsStarProjection e) (a b : A)
    (ha : a ∈ cornerSet A e) (hb : b ∈ cornerSet A e) (z : ℂ) :
    a + b ∈ cornerSet A e ∧ z • a ∈ cornerSet A e ∧
      a * b ∈ cornerSet A e ∧ star a ∈ cornerSet A e := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 3: `e` is
a unit for the corner `e𝒜e`. -/
theorem corner_vna_basic_3 (e : A) (he : IsStarProjection e) (a : A)
    (ha : a ∈ cornerSet A e) : e * a = a ∧ a * e = a := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 4: the
corner `e𝒜e` is norm closed and ultraweakly closed. -/
theorem corner_vna_basic_4 [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) :
    IsClosed (cornerSet A e) ∧ IsClosed[ultraweak A] (cornerSet A e) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 5,
coherence: the (asserted) C*-algebra structure of `Corner A e` is given by
the operations and norm of `A`, with `e` as unit. -/
theorem corner_vna_basic_5 (e : A) (he : IsStarProjection e)
    (a b : Corner A e) (z : ℂ) :
    (a + b).val = a.val + b.val ∧ (a * b).val = a.val * b.val ∧
      (z • a).val = z • a.val ∧ (star a).val = star a.val ∧
      (1 : Corner A e).val = e ∧ (0 : Corner A e).val = 0 ∧
      ‖a‖ = ‖a.val‖ ∧ (a ≤ b ↔ a.val ≤ b.val) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 6: the
supremum in `A` of a bounded directed set of self-adjoint elements of the
corner `e𝒜e` lies again in `e𝒜e` (and is the supremum there). -/
theorem corner_vna_basic_6 [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) (D : Set (selfAdjoint A))
    (hD : ∀ d ∈ D, (d : A) ∈ cornerSet A e)
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    (dirSup D h : A) ∈ cornerSet A e := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 7: the
inclusion `e𝒜e → 𝒜` is an ncpsu-map (existence lemma; `cornerIncl` is
obtained from it by choice). -/
theorem exists_cornerIncl [VonNeumannAlgebra A] (e : A) :
    ∃ f : NCPSUMap (Corner A e) A, ∀ a : Corner A e, f.toNCPMap a = a.val :=
  sorry

/-- The inclusion `e𝒜e → 𝒜` as an ncpsu-map (94II part 7). -/
noncomputable def cornerIncl [VonNeumannAlgebra A] (e : A) :
    NCPSUMap (Corner A e) A := (exists_cornerIncl e).choose

theorem cornerIncl_apply [VonNeumannAlgebra A] (e : A) (a : Corner A e) :
    (cornerIncl e).toNCPMap a = a.val := (exists_cornerIncl e).choose_spec a

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 8: the
restriction of an np-functional on `𝒜` to the corner `e𝒜e` is an
np-functional. -/
theorem corner_vna_basic_8 [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) (ω : NPFunctional A) :
    ∃ ω' : NPFunctional (Corner A e), ∀ a : Corner A e, ω' a = ω a.val :=
  sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 9: the
projection `a ↦ e·a·e : 𝒜 → e𝒜e` onto a corner is an ncpu-map
(existence lemma; `cornerProjMap` is obtained from it by choice). -/
theorem exists_cornerProjMap [VonNeumannAlgebra A] (e : A) :
    ∃ π : NCPUMap A (Corner A e), ∀ a : A, (π.toNCPMap a).val = e * a * e :=
  sorry

/-- The projection `a ↦ e·a·e : 𝒜 → e𝒜e` onto a corner as an ncpu-map
(94II part 9). -/
noncomputable def cornerProjMap [VonNeumannAlgebra A] (e : A) :
    NCPUMap A (Corner A e) := (exists_cornerProjMap e).choose

theorem cornerProjMap_apply [VonNeumannAlgebra A] (e : A) (a : A) :
    ((cornerProjMap e).toNCPMap a).val = e * a * e :=
  (exists_cornerProjMap e).choose_spec a

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 10: every
np-functional `ω'` on `e𝒜e` is the restriction of the np-functional
`ω'(e(·)e)` on `𝒜`. -/
theorem corner_vna_basic_10 [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) (ω' : NPFunctional (Corner A e)) :
    ∃ ω : NPFunctional A,
      (∀ a : A, ω a = ω' ((cornerProjMap e).toNCPMap a)) ∧
      (∀ a : Corner A e, ω' a = ω a.val) := sorry

/-- **94II** (`corner-vna-basic`, proc.tex:194, Exercise), part 10
(continued): the ultraweak and ultrastrong topologies of the corner
`e𝒜e` coincide with those induced from `𝒜`. -/
theorem corner_vna_basic_10' [VonNeumannAlgebra A] (e : A)
    (he : IsStarProjection e) :
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
    star a * b * a ∈ cornerSet A q := sorry

/-- **94III** (`ad-ncp`, proc.tex:247, Exercise), part 2: if
`a* p a ≤ q`, then `a*(·)a` gives an ncp-map `p𝒜p → q𝒜q` (existence
lemma; `adNCP` is obtained from it by choice). -/
theorem exists_adNCP [VonNeumannAlgebra A] (a p q : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : star a * p * a ≤ q) :
    ∃ f : NCPMap (Corner A p) (Corner A q),
      ∀ b : Corner A p, (f b).val = star a * b.val * a := sorry

/-- The ncp-map `a*(·)a : p𝒜p → q𝒜q` of 94III part 2. -/
noncomputable def adNCP [VonNeumannAlgebra A] (a p q : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : star a * p * a ≤ q) : NCPMap (Corner A p) (Corner A q) :=
  (exists_adNCP a p q hp hq h).choose

/-- Infrastructure (used for 95II and 103II): for `a·q = a` the map
`a*(·)a : 𝒜 → q𝒜q` is an ncp-map; by choice `adToCorner`. -/
theorem exists_adToCorner [VonNeumannAlgebra A] (a q : A) (h : a * q = a) :
    ∃ f : NCPMap A (Corner A q), ∀ b : A, (f b).val = star a * b * a := sorry

/-- The ncp-map `a*(·)a : 𝒜 → q𝒜q` (for `a·q = a`). -/
noncomputable def adToCorner [VonNeumannAlgebra A] (a q : A) (h : a * q = a) :
    NCPMap A (Corner A q) := (exists_adToCorner a q h).choose

/-- Infrastructure (used for 101VII and 103II): `a*(·)a : 𝒜 → 𝒜` is an
ncp-map; by choice `adSelf`. -/
theorem exists_adSelf [VonNeumannAlgebra A] (a : A) :
    ∃ f : NCPMap A A, ∀ b : A, f b = star a * b * a := sorry

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
    (hu : IsPartialIsometry A u) (h : floor p = u * star u)
    (h' : u * (star u * u) = u) :
    IsCornerOf p (adToCorner u (star u * u) h') := sorry

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

/-- **96V** (`canonical-filter`, proc.tex:414, Proposition),
well-definedness: for `d ∈ 𝒜` the assignment `a ↦ d* a d` gives an
ncp-map `⌈d⌉ᵣ𝒜⌈d⌉ᵣ → 𝒜`; by choice `canonicalFilter`. -/
theorem exists_canonicalFilter [VonNeumannAlgebra A] (d : A) :
    ∃ c : NCPMap (Corner A (suppProj d)) A,
      ∀ a : Corner A (suppProj d), c a = star d * a.val * d := sorry

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
      ∀ a : Corner A (ceil p), c a = CFC.sqrt p * a.val * CFC.sqrt p := sorry

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
        (∀ a : A, π a = β₂ ((stdCorner p).toNCPMap a)) → β₂ = β) := sorry

/-- **98IV** (`corner-basic`, proc.tex:608, Exercise), part 2: a corner is
surjective, and epi in `W*_cp`. -/
theorem corner_basic_2 [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    (p : A) (hp : p ∈ effects A) (π : NCPMap A C) (hπ : IsCornerOf p π)
    (hu : π 1 = 1) :
    Function.Surjective ⇑π ∧
      ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
        [VonNeumannAlgebra B] (g h : NCPMap C B),
        (∀ a, g (π a) = h (π a)) → g = h := sorry

/-- **98V** (`corners-floor`, proc.tex:622, Exercise): an ncpu-map `π` is a
corner for an effect `p` iff it is a corner for `⌊p⌋`; in which case
`⌈π⌉ = ⌊p⌋`.  (Thus a corner `π` is a corner for `⌈π⌉`.) -/
theorem corners_floor [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (p : A) (hp : p ∈ effects A) (π : NCPMap A B) (hu : π 1 = 1) :
    (IsCornerOf p π ↔ IsCornerOf (floor p) π) ∧
      (IsCornerOf p π → ncpCarrier π = floor p) := sorry

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
    (f : NCPMap A B) (e : A) (he : IsStarProjection e)
    (hce : ncpCarrier f ≤ e) (p : B) (hp : 0 ≤ p) (hfp : f 1 ≤ p) :
    ∃! g : NCPMap (Corner A e) (Corner B (ceil p)),
      ∀ a : A, f a = stdFilter p (g ((cornerProjMap e).toNCPMap a)) := sorry

/-- **98VII** (`filter-corner`, proc.tex:642, Theorem), formula: the unique
`g` above is given by `g(a) = √p \ f(a) / √p`. -/
theorem filter_corner_formula [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) (e : A) (he : IsStarProjection e)
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
    (hfg : ∀ b, f (g b) = b) : IsPure f := sorry

/-- **100II** (proc.tex:931, Exercise), part 2: the identity map on a von
Neumann algebra is pure. -/
theorem isPure_id [VonNeumannAlgebra A] : IsPure (ncpId A) := sorry

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
    (hs : IsStarProjection s) :
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
        (g a).val = ceil (f 1) * f a.val * ceil (f 1) := sorry

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
      g (1/2) ≠ 1 ∧ ∀ l : ℝ, l ∈ Set.Icc (0:ℝ) 1 → g (l ^ 2) = g l ^ 2 :=
  sorry

/- **106IV** (`fourth-axiom`, proc.tex:1901, Problem): open problem (is
axiom (D) redundant?) — not formalizable as a theorem; skipped.
**106V** (proc.tex:1908, Remark): historical remark on the axioms of
[westerbaan2016universal]; skipped. -/

end Theses.A.Proc
