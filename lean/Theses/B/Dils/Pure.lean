/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 5966–6550.

  parsec 1680:  introduction to pure maps
  parsec 1690:  corners and filters
  parsec 1700:  pure maps
  parsec 1710:  the Paschke dilation of a corner; pure ⟺ ϱ surjective
  parsec 1720:  ncp-extreme maps

Statements only; every proof is `sorry`.  All von Neumann algebras live in
one universe `u`.  The corner algebras `pAp` appear as the type
`cornerSet A p` (a subtype), whose C*-structure — a genuine result of the
thesis with unit `p` — is provided as `sorry`-instances.  Corners and
filters (proc.tex parsecs 950–980 of thesis A, not yet formalized) are
defined here from scratch following **169II** and **169VIII**.
-/
import Theses.B.Dils.SelfDual

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u

namespace Theses.B.Dils

/-! **168I**–**168IV** (dils.tex:5968–6054, `dils-pure-discussion`):
introduction and discussion of rejected alternative notions of purity —
nothing to formalize. -/

/-! ## The corner algebra `pAp` -/

section CornerSet

variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **corner algebra** `pAp = {a : p a p = a}` of `A` at `p` (used for
a projection, or with `⌊a⌋` for an effect `a`; cf. proc.tex 94I). -/
def cornerSet (p : A) : Type u :=
  {a : A // p * a * p = a}

/-- `pAp` is a C*-algebra with unit `p` (for a projection `p`; cf.
proc.tex 94II `corner-vna-basic`).  FIXME(sorry-instance): deferred; the
instance is stated unconditionally but is only meaningful for projections
`p`. -/
noncomputable instance cornerSet.instCStarAlgebra (p : A) :
    CStarAlgebra (cornerSet A p) :=
  sorry

/-- The canonical order on `pAp`.  FIXME(sorry-instance): deferred. -/
noncomputable instance cornerSet.instPartialOrder (p : A) :
    PartialOrder (cornerSet A p) :=
  sorry

/-- The canonical order of `pAp` makes it star-ordered.
FIXME(sorry-instance): deferred. -/
noncomputable instance cornerSet.instStarOrderedRing (p : A) :
    StarOrderedRing (cornerSet A p) :=
  sorry

/-- `pAp` is a von Neumann algebra when `A` is (and `p` is a projection;
cf. proc.tex 94II).  Deferred like the instances above. -/
theorem cornerSet_vonNeumannAlgebra [VonNeumannAlgebra A] (p : A) :
    VonNeumannAlgebra (cornerSet A p) :=
  sorry

end CornerSet

/-! ## Parsec 1690: corners and filters

**169I** (dils.tex:6056) and **169VII** (dils.tex:6113): introduction —
nothing to formalize.  **169III**, **169IX** (Remarks) — not converted. -/

section CornersFilters

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **169II** (`dils-corner`, dils.tex:6060, Definition): an ncp-map
`h : A → B` is a **corner** for an effect `a ∈ [0,1]_A` when `h(a) = h(1)`
and every ncp-map `f : A → C` with `f(a) = f(1)` factors uniquely through
`h` (as `f = f' ∘ h`). -/
def IsCornerFor (h : NCPMap A B) (a : A) : Prop :=
  a ∈ effects A ∧ h a = h 1 ∧
  ∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (f : NCPMap A C), f a = f 1 →
    ∃! f' : NCPMap B C, ∀ x, f' (h x) = f x

/-- **169II** (`dils-corner`, dils.tex:6060, Definition): a **corner** is
an ncp-map which is a corner for some effect. -/
def IsCorner (h : NCPMap A B) : Prop :=
  ∃ a : A, IsCornerFor h a

/-- **169IV** (`standard-corner-dils`, dils.tex:6080, Example): the
**standard corner** `h_a : A → ⌊a⌋A⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋`, is a corner for
the effect `a` (see proc.tex 98I, 95II). -/
theorem standard_corner_dils [VonNeumannAlgebra A] (a : A)
    (ha : a ∈ effects A) :
    ∃ h : NCPMap A (cornerSet A (floor a)),
      (∀ b : A, (h b).1 = floor a * b * floor a) ∧ IsCornerFor h a :=
  sorry

/-- **169V** (`h-is-corner-for-unital-map`, dils.tex:6088, Lemma): if
`(𝒫, ϱ, h)` is a Paschke dilation of a *unital* ncp-map, then `h` is a
corner.

**169VI** is the proof — not converted. -/
theorem h_is_corner_for_unital_map (φ : NCPMap A B) (hu : φ 1 = 1)
    (D : PaschkeTriple A B) (hD : IsPaschkeDilationOf D ⇑φ) :
    IsCorner D.h :=
  sorry

/-- **169VIII** (`dils-def-filter`, dils.tex:6116, Definition): an ncp-map
`c : A → B` is a **filter** for `b ∈ B`, `b ≥ 0`, when `c(1) ≤ b` and
every ncp-map `f : C → B` with `f(1) ≤ b` factors uniquely through `c` (as
`f = c ∘ f'`). -/
def IsFilterFor (c : NCPMap A B) (b : B) : Prop :=
  0 ≤ b ∧ c 1 ≤ b ∧
  ∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (f : NCPMap C B), f 1 ≤ b →
    ∃! f' : NCPMap C A, ∀ x, c (f' x) = f x

/-- **169VIII** (`dils-def-filter`, dils.tex:6116, Definition): a
**filter** is an ncp-map which is a filter for some positive element. -/
def IsFilter (c : NCPMap A B) : Prop :=
  ∃ b : B, IsFilterFor c b

/-- **169X** (`dils-stand-filter`, dils.tex:6150, Example): the **standard
filter** `c_b : ⌈b⌉B⌈b⌉ → B`, `a ↦ √b a √b`, is a filter for `b ≥ 0` (see
proc.tex 96V, 98I). -/
theorem dils_stand_filter [VonNeumannAlgebra B] (b : B) (hb : 0 ≤ b) :
    ∃ c : NCPMap (cornerSet B (ceil b)) B,
      (∀ a : cornerSet B (ceil b), c a = CFC.sqrt b * a.1 * CFC.sqrt b) ∧
      IsFilterFor c b :=
  sorry

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 1: if `(𝒫, ϱ, h)` is a Paschke dilation of `φ : A → B` and
`c : B → C` a filter, then `(𝒫, ϱ, c ∘ h)` is a Paschke dilation of
`c ∘ φ`. -/
theorem dils_filter_basics_1 {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) (c : NCPMap B C) (hc : IsFilter c) :
    ∃ h' : NCPMap D.P C, (∀ x, h' x = c (D.h x)) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ fun a => c (φ a) :=
  sorry

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 2, first half: for a filter `c' : C' → B` of `φ(1)` there is a unique
unital ncp-map `φ'` with `φ = c' ∘ φ'`. -/
theorem dils_filter_basics_2a {C' : Type u} [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (φ : NCPMap A B)
    (c' : NCPMap C' B) (hc : IsFilterFor c' (φ 1)) :
    ∃! φ' : NCPMap A C', φ' 1 = 1 ∧ ∀ a, c' (φ' a) = φ a :=
  sorry

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 2, second half: if moreover `(𝒫, ϱ, h)` is a Paschke dilation of
`φ'`, then `(𝒫, ϱ, c' ∘ h)` is a Paschke dilation of `φ`. -/
theorem dils_filter_basics_2b {C' : Type u} [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (φ : NCPMap A B)
    (c' : NCPMap C' B) (hc : IsFilterFor c' (φ 1)) (φ' : NCPMap A C')
    (hφ' : φ' 1 = 1 ∧ ∀ a, c' (φ' a) = φ a) (D : PaschkeTriple A C')
    (hD : IsPaschkeDilationOf D ⇑φ') :
    ∃ h' : NCPMap D.P B, (∀ x, h' x = c' (D.h x)) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ ⇑φ :=
  sorry

/-- **169XII** (`dils-filters-injective`, dils.tex:6180, Exercise): filters
are injective. -/
theorem dils_filters_injective (c : NCPMap A B) (hc : IsFilter c) :
    Function.Injective ⇑c :=
  sorry

end CornersFilters

/-! ## Parsec 1700: pure maps -/

section Pure

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **170I** (`dils-def-pure`, dils.tex:6186, Definition): an ncp-map is
**pure** when it is a composition of filters and corners; equivalently (by
proc.tex 100III `pure-fundamental`, cf. **170Ia**) a filter after a
corner, which is the form used here. -/
def IsPureMap (φ : NCPMap A B) : Prop :=
  ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (h : NCPMap A C) (c : NCPMap C B),
    IsCorner h ∧ IsFilter c ∧ ∀ a, φ a = c (h a)

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **170II** (`dils-examples-pure`, dils.tex:6195, Examples), part 1: the
pure maps `B(ℋ) → B(𝒦)` are precisely the maps `ad_T` for bounded
operators `T : 𝒦 → ℋ`. -/
theorem dils_examples_pure_1 (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    IsPureMap φ ↔ ∃ T : K →L[ℂ] H, ∀ a, φ a = conjOperator T a :=
  sorry

/-- **170II** (`dils-examples-pure`, dils.tex:6195, Examples), part 2: the
right-hand side `h` of any Paschke dilation is pure (it is `c ∘ h'` for a
filter `c` and corner `h'` by **169V** and **169XI**).

**170III** (Remark, the †-structure preview: there is a unique dagger on
the category of von Neumann algebras with pure maps, `(ad_V)† = ad_{V*}`;
see eff.tex 215III `dagger-theorem`) — not converted here. -/
theorem dils_examples_pure_2 (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    IsPureMap D.h :=
  sorry

/-- **170IV** (`surjective-nmiu`, dils.tex:6223, Exercise), first half:
every surjective nmiu-map is a corner of a central projection (hence
pure). -/
theorem surjective_nmiu_1 (ϱ : NMIUMap A B) (hs : Function.Surjective ⇑ϱ)
    (φ : NCPMap A B) (hφ : ∀ a, φ a = ϱ a) :
    ∃ z : A, IsStarProjection z ∧ IsCentral A z ∧ IsCornerFor φ z :=
  sorry

/-- **170IV** (`surjective-nmiu`, dils.tex:6223, Exercise), second half:
conversely, every corner of a central projection is (equal as a map to) a
surjective nmiu-map. -/
theorem surjective_nmiu_2 (φ : NCPMap A B) (z : A)
    (hz : IsStarProjection z) (hcentral : IsCentral A z)
    (hφ : IsCornerFor φ z) :
    ∃ ϱ : NMIUMap A B, (∀ a, ϱ a = φ a) ∧ Function.Surjective ⇑ϱ :=
  sorry

end Pure

/-! ## Parsec 1710: purity via the Paschke dilation

**171I** (dils.tex:6232): introduction; **171III**–**171VI** and
**171VIII** are proofs — not converted. -/

section PaschkePure

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **171II** (`paschke-corner`, dils.tex:6237, Theorem): for a projection
`p` in a von Neumann algebra `A`, a Paschke dilation of the standard
corner `h_p : A → pAp` is `(⌈⌈p⌉⌉A, h_{⌈⌈p⌉⌉}, h'_p)`, where `⌈⌈p⌉⌉` is
the central carrier of `p`, `h_{⌈⌈p⌉⌉}` the standard corner for `⌈⌈p⌉⌉`,
and `h'_p` the restriction of `h_p` to `⌈⌈p⌉⌉A`. -/
theorem paschke_corner [VonNeumannAlgebra A] (p : A)
    (hp : IsStarProjection p) (hp' : NCPMap A (cornerSet A p))
    (hval : ∀ a : A, (hp' a).1 = p * a * p) :
    ∃ (ρ : NMIUMap A (cornerSet A (cceil p)))
      (h : NCPMap (cornerSet A (cceil p)) (cornerSet A p)),
      (∀ a : A, (ρ a).1 = cceil p * a * cceil p) ∧
      (∀ c : cornerSet A (cceil p), (h c).1 = p * c.1 * p) ∧
      IsPaschkeDilationOf
        ⟨cornerSet A (cceil p), cornerSet_vonNeumannAlgebra A (cceil p),
          ρ, h⟩ ⇑hp' :=
  sorry

/-- **171VII** (`paschke-pure`, dils.tex:6365, Theorem): an ncp-map `φ`
with Paschke dilation `(𝒫, ϱ, h)` is pure if and only if `ϱ` is
surjective. -/
theorem paschke_pure [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    IsPureMap φ ↔ Function.Surjective ⇑D.ρ :=
  sorry

end PaschkePure

/-! ## Parsec 1720: ncp-extreme maps

**172I** (dils.tex:6404): introduction; **172IV**–**172VII**, **172IX**,
**172XI** are proofs — not converted. -/

section Extreme

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **172II** (dils.tex:6408, Definition): an ncp-map `φ` is
**ncp-extreme** when it is an extreme point among the ncp-maps with the
same value on `1`: `λφ₁ + (1-λ)φ₂ = φ` with `0 < λ < 1` and
`φ₁(1) = φ₂(1) = φ(1)` forces `φ₁ = φ₂ = φ`. -/
def NCPExtreme (φ : NCPMap A B) : Prop :=
  ∀ l : ℝ, 0 < l → l < 1 → ∀ φ₁ φ₂ : NCPMap A B,
    φ₁ 1 = φ 1 → φ₂ 1 = φ 1 →
    (∀ a, φ a = (l : ℂ) • φ₁ a + ((1 - l : ℝ) : ℂ) • φ₂ a) →
    (∀ a, φ₁ a = φ a) ∧ ∀ a, φ₂ a = φ a

/-- **172III** (`ncp-extreme-paschke`, dils.tex:6426, Theorem): for an
ncp-map `φ` with Paschke dilation `(𝒫, ϱ, h)` the following are
equivalent: (1) `h` is injective on the commutant `ϱ(A)′`; (2) `h` is
injective on `[0,1]_{ϱ(A)′}`; (3) `φ` is ncp-extreme. -/
theorem ncp_extreme_paschke [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    List.TFAE
      [Set.InjOn ⇑D.h (commutant D.P (Set.range ⇑D.ρ)),
       Set.InjOn ⇑D.h
         (commutant D.P (Set.range ⇑D.ρ) ∩ Set.Icc (0 : D.P) 1),
       NCPExtreme φ] :=
  sorry

/-- **172VIII** (`nmiu-ncp-extreme`, dils.tex:6512, Corollary): every
nmiu-map (as an ncp-map) is ncp-extreme. -/
theorem nmiu_ncp_extreme (ϱ : NMIUMap A B) (φ : NCPMap A B)
    (hφ : ∀ a, φ a = ϱ a) :
    NCPExtreme φ :=
  sorry

/-- **172X** (dils.tex:6520, Theorem): every pure ncp-map is
ncp-extreme. -/
theorem pure_ncp_extreme [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (hpure : IsPureMap φ) :
    NCPExtreme φ :=
  sorry

/-- **172XII** (`ncp-extreme-comp`, dils.tex:6544, Corollary): every
ncp-map is the composition of two ncp-extreme maps. -/
theorem ncp_extreme_comp [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) :
    ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C) (ψ₁ : NCPMap A C) (ψ₂ : NCPMap C B),
      NCPExtreme ψ₁ ∧ NCPExtreme ψ₂ ∧ ∀ a, φ a = ψ₂ (ψ₁ a) :=
  sorry

end Extreme

end Theses.B.Dils
