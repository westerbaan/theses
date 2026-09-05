/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 1: C*-algebras — cstar.tex, lines 3887–4958.

  §Representation
    … by Continuous Functions   (parsec 270: Riesz ideals, multiplicative
                                 states, Stone–Weierstraß, Gelfand's
                                 representation theorem; parsec 280: the
                                 continuous functional calculus, monotonicity
                                 of the square root; parsec 290: the duality
                                 with compact Hausdorff spaces)
    … by Bounded Operators      (parsec 300: states, the GNS construction,
                                 the Gelfand–Naimark theorem)

All statements of parsecs 270–300 are proved.  Two of them were brought up to
their printed form on 2026-09-04 under the `docs/DECISIONS.md` §2.1 ruling,
which closes §2.5 and §2.4 with them: **28II**.4 `functional_calculus_4` now
identifies the unique element with `f(a)`, and **30X** `proto_gelfand_naimark_2`
now names `ϱ_Ω` (`dsumRep`) in clause (1), so the equivalence has a converse
and the closing miu-isomorphism claim is `proto_gelfand_naimark_3`.  See
CONVENTIONS.md for the numbering (**27XV** = parsec 270, point 150) and naming
conventions.
-/
import Theses.A.CStar.Positive

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule NNReal ENNReal
open Filter Topology WeakDual

universe u v

namespace Theses.A.CStar

/-! ## Parsec 270: Gelfand's representation theorem

**27I** (cstar.tex:3919): introduction — nothing to formalize.
**27II** (cstar.tex:3928, Setting): `𝒜` is a commutative C*-algebra.

**27III** (`gelfand-representation`, cstar.tex:3931, Definition): the
*spectrum* `spec(𝒜)` of `𝒜` is the set of miu-maps `f : 𝒜 → ℂ` with the
topology of pointwise convergence — in Mathlib `WeakDual.characterSpace ℂ 𝒜`
(its elements are the non-zero continuous algebra homomorphisms, which for a
C*-algebra are exactly the miu-maps, automatically continuous by
`norm_mi_map_contractive`); the *Gelfand representation*
`γ : 𝒜 → C(spec 𝒜)`, `γ(a)(f) = f(a)`, is Mathlib's
`gelfandTransform ℂ 𝒜` (star-preserving version: `gelfandStarTransform`).

**27V** (cstar.tex:3951, Remark): the relation between `spec(𝒜)` and
`spec(a)` appears at **27XVII**; nothing to formalize.
**27VI** (cstar.tex:3961): program — nothing to formalize. -/

section GelfandRepresentation

variable {𝒜 : Type*} [CommCStarAlgebra 𝒜]

/-- **27IV** (`gelfand-representation-basic`, cstar.tex:3945, Exercise),
part 1: the evaluation map `f ↦ f(a)` on `spec(𝒜)` is continuous for every
`a ∈ 𝒜`.

*Class 1 — faithful.*  The solution says continuity is "a direct result of
putting the topology of pointwise convergence on `spec(𝒜)`": here that is
`WeakDual.eval_continuous a` (evaluation is continuous for the weak-∗
topology), composed with the inclusion of the character space carrying the
induced topology. -/
theorem gelfand_representation_basic_1 (a : 𝒜) :
    Continuous fun φ : characterSpace ℂ 𝒜 => φ a :=
  (WeakDual.eval_continuous a).comp continuous_induced_dom

/-- **27IV** (`gelfand-representation-basic`, cstar.tex:3945, Exercise),
part 2: the Gelfand representation is an miu-map; multiplicativity and
unitality are part of the bundled `gelfandTransform`, so involution
preservation remains.

*Class 1 — faithful.*  The solution's reason is that `γ` preserves each
operation "essentially because each `f ∈ spec(𝒜)` preserves" it; the
involution clause is exactly that, evaluated character by character:
`γ(a*)(φ) = φ(a*) = φ(a)* = γ(a)*(φ)` for every `φ`, i.e. `map_star φ a`. -/
theorem gelfand_representation_basic_2 (a : 𝒜) :
    gelfandTransform ℂ 𝒜 (star a) = star (gelfandTransform ℂ 𝒜 a) := by
  ext φ
  simp only [ContinuousMap.star_apply]
  exact map_star φ a

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **27VII** (cstar.tex:3978, Definition): a *Riesz ideal* of `𝒜` is an
order ideal `I` with `|a| ∈ I` for every self-adjoint `a ∈ I`. -/
def IsRieszIdeal (I : Submodule ℂ 𝒜) : Prop :=
  IsOrderIdeal I ∧ ∀ a ∈ I, IsSelfAdjoint a → CFC.abs a ∈ I

/-- **27VII** (cstar.tex:3978, Definition): a *maximal Riesz ideal* is a
proper Riesz ideal maximal among the proper Riesz ideals. -/
def IsMaximalRieszIdeal (I : Submodule ℂ 𝒜) : Prop :=
  (IsRieszIdeal I ∧ (1 : 𝒜) ∉ I) ∧
    ∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → (1 : 𝒜) ∉ J → I ≤ J → J = I

/-! ### Helpers for the parsec 270 Riesz-ideal chain -/

private theorem rsmul_mono {r : ℝ} (hr : 0 ≤ r) {x y : 𝒜} (h : x ≤ y) :
    r • x ≤ r • y := by
  have h1 := ofReal_smul_nonneg (sub_nonneg.mpr h) hr
  rw [Complex.coe_smul, smul_sub] at h1
  exact sub_nonneg.mp h1

private theorem rsmul_mono' {r s : ℝ} (h : r ≤ s) {x : 𝒜} (hx : 0 ≤ x) :
    r • x ≤ s • x := by
  have h1 := ofReal_smul_nonneg hx (sub_nonneg.mpr h)
  rw [Complex.coe_smul, sub_smul] at h1
  exact sub_nonneg.mp h1

private theorem rsmul_mem {I : Submodule ℂ 𝒜} {x : 𝒜} (hx : x ∈ I) (r : ℝ) :
    r • x ∈ I := by
  have h := I.smul_mem ((r : ℂ)) hx
  rwa [Complex.coe_smul] at h

/-- `-|x| ≤ x ≤ |x|`. -/
private theorem neg_abs_le_self (x : 𝒜) (hx : IsSelfAdjoint x) :
    -CFC.abs x ≤ x ∧ x ≤ CFC.abs x :=
  ⟨(cstar_pos_neg_part_1 x hx).1, (cstar_pos_neg_part_1 x hx).2.1⟩

/-- In a commutative C*-algebra, `|x| ≤ y` iff `-y ≤ x ≤ y`. -/
private theorem abs_le_iff (x y : 𝒜) (hx : IsSelfAdjoint x) :
    CFC.abs x ≤ y ↔ (-y ≤ x ∧ x ≤ y) := by
  have hlub := commutative_cstar_basic_1 x hx
  constructor
  · intro h
    exact ⟨neg_le_of_neg_le (le_trans (hlub.1 (Set.mem_insert_of_mem _ rfl)) h),
      le_trans (hlub.1 (Set.mem_insert _ _)) h⟩
  · rintro ⟨h1, h2⟩
    refine hlub.2 ?_
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact h2
    · exact neg_le_of_neg_le h1

/-- The triangle inequality for `|·|` in a commutative C*-algebra. -/
private theorem abs_add_le (x y : 𝒜) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    CFC.abs (x + y) ≤ CFC.abs x + CFC.abs y := by
  obtain ⟨hx1, hx2⟩ := neg_abs_le_self x hx
  obtain ⟨hy1, hy2⟩ := neg_abs_le_self y hy
  refine (abs_le_iff _ _ (hx.add hy)).mpr ⟨?_, add_le_add hx2 hy2⟩
  have := add_le_add hx1 hy1
  rwa [← neg_add] at this

private theorem re_im_mem {I : Submodule ℂ 𝒜} (hI : IsOrderIdeal I)
    {x : 𝒜} (hx : x ∈ I) : (ℜ x : 𝒜) ∈ I ∧ (ℑ x : 𝒜) ∈ I := by
  have hs : star x ∈ I := hI.star_mem x hx
  constructor
  · rw [realPart_apply_coe]
    exact rsmul_mem (I.add_mem hx hs) _
  · rw [imaginaryPart_apply_coe]
    exact I.smul_mem _ (rsmul_mem (I.sub_mem hx hs) _)

private theorem posPart_negPart_mem {I : Submodule ℂ 𝒜} (hI : IsRieszIdeal I)
    {x : 𝒜} (hx : x ∈ I) (hxsa : IsSelfAdjoint x) : x⁺ ∈ I ∧ x⁻ ∈ I := by
  have habs : CFC.abs x ∈ I := hI.2 x hx hxsa
  have hp2 : CFC.abs x + x = x⁺ + x⁺ := by
    rw [CFC.abs_add_self x hxsa, two_nsmul]
  have hn2 : CFC.abs x - x = x⁻ + x⁻ := by
    rw [CFC.abs_sub_self x hxsa, two_nsmul]
  have hp : x⁺ = (2 : ℝ)⁻¹ • (CFC.abs x + x) := by rw [hp2]; module
  have hn : x⁻ = (2 : ℝ)⁻¹ • (CFC.abs x - x) := by rw [hn2]; module
  exact ⟨hp ▸ rsmul_mem (I.add_mem habs hx) _, hn ▸ rsmul_mem (I.sub_mem habs hx) _⟩

/-- **27VIII**, the case `a` self-adjoint and `x` positive: the thesis's own
final step, `−‖a‖x ≤ ax ≤ ‖a‖x` by **23VII**.2. -/
private theorem riesz_mul_mem_of_nonneg {I : Submodule ℂ 𝒜} (hI : IsRieszIdeal I)
    {a x : 𝒜} (ha : IsSelfAdjoint a) (hx : x ∈ I) (hx0 : 0 ≤ x) : a * x ∈ I := by
  obtain ⟨hlo, hhi⟩ := (norm_le_iff_neg_algebraMap_le ha (norm_nonneg a)).mp le_rfl
  set r : 𝒜 := algebraMap ℂ 𝒜 ((‖a‖ : ℝ) : ℂ) with hr
  have hrsa : IsSelfAdjoint r := isSelfAdjoint_algebraMap_ofReal _
  have h1 : x * (-r) ≤ x * a :=
    sqrt_2 x hx0 (-r) a hrsa.neg ha (mul_comm _ _) (mul_comm _ _) hlo
  have h2 : x * a ≤ x * r := sqrt_2 x hx0 a r ha hrsa (mul_comm _ _) (mul_comm _ _) hhi
  have hxr : x * r = ((‖a‖ : ℝ) : ℂ) • x := by
    rw [hr, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hmem : ((‖a‖ : ℝ) : ℂ) • x ∈ I := I.smul_mem _ hx
  have hnn : (0 : 𝒜) ≤ ((‖a‖ : ℝ) : ℂ) • x := ofReal_smul_nonneg hx0 (norm_nonneg a)
  rw [mul_neg, hxr] at h1
  rw [hxr] at h2
  rw [mul_comm]
  exact hI.1.mem_of_mem_interval _ hmem hnn _ h1 h2

private theorem riesz_mul_mem_of_isSelfAdjoint {I : Submodule ℂ 𝒜}
    (hI : IsRieszIdeal I) {a x : 𝒜} (ha : IsSelfAdjoint a) (hx : x ∈ I)
    (hxsa : IsSelfAdjoint x) : a * x ∈ I := by
  obtain ⟨hp, hn⟩ := posPart_negPart_mem hI hx hxsa
  have h1 := riesz_mul_mem_of_nonneg hI ha hp (CFC.posPart_nonneg x)
  have h2 := riesz_mul_mem_of_nonneg hI ha hn (CFC.negPart_nonneg x)
  have he : a * x = a * x⁺ - a * x⁻ := by
    rw [← mul_sub, CFC.posPart_sub_negPart x hxsa]
  rw [he]
  exact I.sub_mem h1 h2

private theorem riesz_mul_mem_of_left_isSelfAdjoint {I : Submodule ℂ 𝒜}
    (hI : IsRieszIdeal I) {a x : 𝒜} (ha : IsSelfAdjoint a) (hx : x ∈ I) :
    a * x ∈ I := by
  obtain ⟨hre, him⟩ := re_im_mem hI.1 hx
  have h1 := riesz_mul_mem_of_isSelfAdjoint hI ha hre (ℜ x).2
  have h2 := riesz_mul_mem_of_isSelfAdjoint hI ha him (ℑ x).2
  have he : a * x = a * (ℜ x : 𝒜) + Complex.I • (a * (ℑ x : 𝒜)) := by
    rw [← mul_smul_comm, ← mul_add, realPart_add_I_smul_imaginaryPart]
  rw [he]
  exact I.add_mem h1 (I.smul_mem _ h2)

/-- **27VIII** (`riesz-ideal-ring-ideal`, cstar.tex:3989, Lemma): a Riesz
ideal `I` of `𝒜` is a ring ideal: `a x ∈ I` for `a ∈ 𝒜`, `x ∈ I`. -/
theorem riesz_ideal_ring_ideal (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (a : 𝒜) (x : 𝒜) (hx : x ∈ I) : a * x ∈ I := by
  have h1 := riesz_mul_mem_of_left_isSelfAdjoint hI (ℜ a).2 hx
  have h2 := riesz_mul_mem_of_left_isSelfAdjoint hI (ℑ a).2 hx
  have he : a * x = (ℜ a : 𝒜) * x + Complex.I • ((ℑ a : 𝒜) * x) := by
    rw [← smul_mul_assoc, ← add_mul, realPart_add_I_smul_imaginaryPart]
  rw [he]
  exact I.add_mem h1 (I.smul_mem _ h2)

/-- **27X** (`riesz-ideal-basic`, cstar.tex:4009, Exercise), part 3: each
proper Riesz ideal is contained in a maximal Riesz ideal. -/
theorem riesz_ideal_basic_3 (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (h1 : (1 : 𝒜) ∉ I) :
    ∃ J : Submodule ℂ 𝒜, IsMaximalRieszIdeal J ∧ I ≤ J := by
  have hzorn : ∀ c ⊆ {J : Submodule ℂ 𝒜 | IsRieszIdeal J ∧ (1 : 𝒜) ∉ J},
      IsChain (· ≤ ·) c → ∀ y ∈ c,
        ∃ ub ∈ {J : Submodule ℂ 𝒜 | IsRieszIdeal J ∧ (1 : 𝒜) ∉ J},
          ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hmem : ∀ x : 𝒜, x ∈ sSup c ↔ ∃ K ∈ c, x ∈ K := fun x =>
      Submodule.mem_sSup_of_directed ⟨y, hy⟩ hchain.directedOn
    refine ⟨sSup c, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, fun z hz => le_sSup hz⟩
    · intro b hb
      obtain ⟨K, hKc, hbK⟩ := (hmem b).mp hb
      exact Submodule.mem_sSup_of_mem hKc ((hc hKc).1.1.star_mem b hbK)
    · intro b hb hb0 d hd1 hd2
      obtain ⟨K, hKc, hbK⟩ := (hmem b).mp hb
      exact Submodule.mem_sSup_of_mem hKc
        ((hc hKc).1.1.mem_of_mem_interval b hbK hb0 d hd1 hd2)
    · intro b hb hbsa
      obtain ⟨K, hKc, hbK⟩ := (hmem b).mp hb
      exact Submodule.mem_sSup_of_mem hKc ((hc hKc).1.2 b hbK hbsa)
    · intro hone
      obtain ⟨K, hKc, h1K⟩ := (hmem 1).mp hone
      exact (hc hKc).2 h1K
  obtain ⟨m, hIm, hm⟩ := zorn_le_nonempty₀ _ hzorn I ⟨hI, h1⟩
  exact ⟨m, ⟨hm.1, fun J hJ hJ1 hmJ => le_antisymm (hm.2 ⟨hJ, hJ1⟩ hmJ) hmJ⟩, hIm⟩

private theorem isSelfAdjoint_of_mem_interval' {b c : 𝒜} (h1 : -b ≤ c) (h2 : c ≤ b) :
    IsSelfAdjoint c := by
  have hs1 : IsSelfAdjoint (b - c) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h2)
  have hs2 : IsSelfAdjoint (c - -b) := IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h1)
  have hsum : IsSelfAdjoint (c - -b - (b - c)) := hs2.sub hs1
  have he : c - -b - (b - c) = c + c := by abel
  rw [he] at hsum
  have h := hsum.star_eq
  rw [star_add] at h
  have h2' : (2 : ℂ)⁻¹ • (star c + star c) = (2 : ℂ)⁻¹ • (c + c) := by rw [h]
  have e1 : (2 : ℂ)⁻¹ • (star c + star c) = star c := by module
  have e2 : (2 : ℂ)⁻¹ • (c + c) = c := by module
  rw [e1, e2] at h2'
  exact h2'

/-- The two halves of `|c| = c⁺ + c⁻` bound `|c|` from below. -/
private theorem posPart_le_abs (c : 𝒜) (hc : IsSelfAdjoint c) :
    c⁺ ≤ CFC.abs c ∧ c⁻ ≤ CFC.abs c := by
  have h := CFC.posPart_add_negPart c hc
  constructor
  · rw [← h]; simpa using add_le_add_left (CFC.negPart_nonneg c) c⁺
  · rw [← h]; simpa using add_le_add_right (CFC.posPart_nonneg c) c⁻

/-- The Riesz-decomposition step of **27X**.2 (`riesz-decomposition-lemma`,
the thesis's own hint): anything positive below `p + q` splits along `I ⊔ J`. -/
private theorem mem_sup_of_le_add {I J : Submodule ℂ 𝒜} (hI : IsRieszIdeal I)
    (hJ : IsRieszIdeal J) {p q d : 𝒜} (hp : p ∈ I) (hp0 : 0 ≤ p) (hq : q ∈ J)
    (hq0 : 0 ≤ q) (hd0 : 0 ≤ d) (hd : d ≤ p + q) : d ∈ I ⊔ J := by
  obtain ⟨u, v, hu0, hup, hv0, hvq, he⟩ :=
    riesz_decomposition_lemma p q d hp0 hq0 hd0 hd
  have h1 : u ∈ I := hI.1.mem_of_mem_interval p hp hp0 u
    (le_trans (neg_nonpos_of_nonneg hp0) hu0) hup
  have h2 : v ∈ J := hJ.1.mem_of_mem_interval q hq hq0 v
    (le_trans (neg_nonpos_of_nonneg hq0) hv0) hvq
  rw [he]
  exact Submodule.add_mem_sup h1 h2

/-- Every self-adjoint element of `I ⊔ J` is dominated in absolute value by a
sum of a positive element of `I` and a positive element of `J`. -/
private theorem abs_le_sup_witness {I J : Submodule ℂ 𝒜} (hI : IsRieszIdeal I)
    (hJ : IsRieszIdeal J) {b : 𝒜} (hb : b ∈ I ⊔ J) (hbsa : IsSelfAdjoint b) :
    ∃ p ∈ I, ∃ q ∈ J, 0 ≤ p ∧ 0 ≤ q ∧ CFC.abs b ≤ p + q := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨hyre, -⟩ := re_im_mem hI.1 hy
  obtain ⟨hzre, -⟩ := re_im_mem hJ.1 hz
  refine ⟨CFC.abs (ℜ y : 𝒜), hI.2 _ hyre (ℜ y).2, CFC.abs (ℜ z : 𝒜),
    hJ.2 _ hzre (ℜ z).2, CFC.abs_nonneg _, CFC.abs_nonneg _, ?_⟩
  have hbre : b = (ℜ y : 𝒜) + (ℜ z : 𝒜) := by
    have : (ℜ b : 𝒜) = (ℜ y : 𝒜) + (ℜ z : 𝒜) := by
      rw [← hyz, map_add, AddSubgroup.coe_add]
    rw [← this, hbsa.coe_realPart]
  rw [hbre]
  exact abs_add_le _ _ (ℜ y).2 (ℜ z).2

/-- **27X** (`riesz-ideal-basic`, cstar.tex:4009, Exercise), part 2, first
clause: the sum `I + J` of two Riesz ideals is a Riesz ideal.  The part's
second clause — that `I + J` may fail to be an order ideal when `I` and `J`
are only *order* ideals — is `riesz_ideal_basic_2_order_counterexample`
below. -/
theorem riesz_ideal_basic_2 (I J : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (hJ : IsRieszIdeal J) : IsRieszIdeal (I ⊔ J) := by
  have habs : ∀ b ∈ I ⊔ J, IsSelfAdjoint b → CFC.abs b ∈ I ⊔ J := by
    intro b hb hbsa
    obtain ⟨p, hp, q, hq, hp0, hq0, hle⟩ := abs_le_sup_witness hI hJ hb hbsa
    exact mem_sup_of_le_add hI hJ hp hp0 hq hq0 (CFC.abs_nonneg b) hle
  refine ⟨⟨?_, ?_⟩, habs⟩
  · intro b hb
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hb
    rw [← hyz, star_add]
    exact Submodule.add_mem_sup (hI.1.star_mem y hy) (hJ.1.star_mem z hz)
  · intro b hb hb0 c hc1 hc2
    have hbsa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg hb0
    have hcsa : IsSelfAdjoint c := isSelfAdjoint_of_mem_interval' hc1 hc2
    obtain ⟨p, hp, q, hq, hp0, hq0, hle⟩ := abs_le_sup_witness hI hJ hb hbsa
    rw [CFC.abs_of_nonneg b hb0] at hle
    have hcb : CFC.abs c ≤ b := (abs_le_iff c b hcsa).mpr ⟨hc1, hc2⟩
    obtain ⟨hcp, hcn⟩ := posPart_le_abs c hcsa
    have h1 : c⁺ ∈ I ⊔ J := mem_sup_of_le_add hI hJ hp hp0 hq hq0
      (CFC.posPart_nonneg c) (le_trans (le_trans hcp hcb) hle)
    have h2 : c⁻ ∈ I ⊔ J := mem_sup_of_le_add hI hJ hp hp0 hq hq0
      (CFC.negPart_nonneg c) (le_trans (le_trans hcn hcb) hle)
    rw [← CFC.posPart_sub_negPart c hcsa]
    exact Submodule.sub_mem _ h1 h2

/-! ### 27X.2's second clause: order ideals are not closed under sums

The Exercise's own contrast: `I + J` *is* a Riesz ideal when `I` and `J` are
(`riesz_ideal_basic_2` above), "but `I + J` might not be an order ideal
when `I` and `J` are order ideals".  The Exercise supplies no witness and
`asols.tex` has no solution at `parsec-270.100`, so the witness below is
ours.  It lives in the commutative C*-algebra `ℂ³` of the Setting **27II**,
and is as small as it can be: in `ℂ²` every order ideal is one of `0`,
`ℂ × 0`, `0 × ℂ`, a line `ℂ·(λ,μ)` with `λμ ∉ [0,∞)`, or the whole algebra,
and those are closed under sums. -/

/-- `u = (1, 1, -1)`, a self-adjoint element of `ℂ³` that is neither positive
nor negative, so that the line `ℂ·u` meets the positive cone only in `0`. -/
private noncomputable def ideal3u : Fin 3 → ℂ := ![1, 1, -1]

/-- `v = (0, 0, 1)`, a positive element of `ℂ³` whose order interval
`[-v, v]` already lies on the line `ℂ·v`. -/
private noncomputable def ideal3v : Fin 3 → ℂ := ![0, 0, 1]

/-- `ℂ·u` is an order ideal: it is a `⋆`-closed subspace, and it contains no
positive element but `0` (if `c·u ≥ 0` then `c ≥ 0` from the first
coordinate and `-c ≥ 0` from the third), so the interval condition is
vacuous. -/
private theorem ideal3u_isOrderIdeal : IsOrderIdeal (ℂ ∙ ideal3u) := by
  constructor
  · intro b hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine Submodule.mem_span_singleton.mpr ⟨starRingEnd ℂ c, ?_⟩
    funext i; fin_cases i <;> simp [ideal3u]
  · intro b hb hb0 a hle hge
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have h0 : (0 : ℂ) ≤ c := by simpa [ideal3u] using hb0 0
    have h2 : (0 : ℂ) ≤ -c := by simpa [ideal3u] using hb0 2
    have hcz : c = 0 := le_antisymm (neg_nonneg.mp h2) h0
    subst hcz
    have ha : a = 0 := le_antisymm (by simpa using hge) (by simpa using hle)
    rw [ha]
    exact Submodule.zero_mem _

/-- `ℂ·v` is an order ideal: `⋆`-closed, and for `b = c·v ≥ 0` an element of
`[-b, b]` has vanishing first two coordinates, hence lies on the line. -/
private theorem ideal3v_isOrderIdeal : IsOrderIdeal (ℂ ∙ ideal3v) := by
  constructor
  · intro b hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine Submodule.mem_span_singleton.mpr ⟨starRingEnd ℂ c, ?_⟩
    funext i; fin_cases i <;> simp [ideal3v]
  · intro b hb hb0 a hle hge
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine Submodule.mem_span_singleton.mpr ⟨a 2, ?_⟩
    have e0 : a 0 = 0 := by
      have h1 : -(c • ideal3v) 0 ≤ a 0 := hle 0
      have h2 : a 0 ≤ (c • ideal3v) 0 := hge 0
      simp [ideal3v] at h1 h2
      exact le_antisymm h2 h1
    have e1 : a 1 = 0 := by
      have h1 : -(c • ideal3v) 1 ≤ a 1 := hle 1
      have h2 : a 1 ≤ (c • ideal3v) 1 := hge 1
      simp [ideal3v] at h1 h2
      exact le_antisymm h2 h1
    funext i; fin_cases i <;> simp [ideal3v, e0, e1]

/-- Every element of `ℂ·u + ℂ·v` has its first two coordinates equal:
`c·u + d·v = (c, c, -c + d)`. -/
private theorem ideal3_mem_sup {x : Fin 3 → ℂ}
    (hx : x ∈ (ℂ ∙ ideal3u) ⊔ (ℂ ∙ ideal3v)) : x 0 = x 1 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [ideal3u, ideal3v]

/-- **27X** (`riesz-ideal-basic`, cstar.tex:4009, Exercise), part 2, second
clause: the sum of two *order* ideals need not be an order ideal.

The witnesses are `I = ℂ·(1,1,-1)` and `J = ℂ·(0,0,1)` in `ℂ³`.  Their sum
is the plane `{(x, x, z)}`, which contains the positive element
`b = (1,1,0) = u + v`; but `a = (1,0,0)` satisfies `-b ≤ a ≤ b` and has
unequal first two coordinates, so it is not in `I + J`. -/
theorem riesz_ideal_basic_2_order_counterexample :
    ∃ I J : Submodule ℂ (Fin 3 → ℂ),
      IsOrderIdeal I ∧ IsOrderIdeal J ∧ ¬ IsOrderIdeal (I ⊔ J) := by
  refine ⟨ℂ ∙ ideal3u, ℂ ∙ ideal3v, ideal3u_isOrderIdeal, ideal3v_isOrderIdeal, ?_⟩
  intro h
  set b : Fin 3 → ℂ := ![1, 1, 0] with hb
  set a : Fin 3 → ℂ := ![1, 0, 0] with ha
  have hbmem : b ∈ (ℂ ∙ ideal3u) ⊔ (ℂ ∙ ideal3v) := by
    refine Submodule.mem_sup.mpr ⟨(1 : ℂ) • ideal3u, Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), (1 : ℂ) • ideal3v,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    funext i; fin_cases i <;> simp [ideal3u, ideal3v, hb]
  have hb0 : (0 : Fin 3 → ℂ) ≤ b := by intro i; fin_cases i <;> simp [hb]
  have h1 : -b ≤ a := by intro i; fin_cases i <;> simp [ha, hb] <;> norm_num
  have h2 : a ≤ b := by intro i; fin_cases i <;> simp [ha, hb]
  have hcoord := ideal3_mem_sup (h.mem_of_mem_interval b hbmem hb0 a h1 h2)
  simp [ha] at hcoord

/-! ### The least Riesz ideal `(a)ₘ` (27X.1) -/

/-- `x` is dominated by a natural multiple of `|a|`. -/
private def AbsDom (a x : 𝒜) : Prop := ∃ n : ℕ, CFC.abs x ≤ (n : ℝ) • CFC.abs a

private theorem absDom_le {a x : 𝒜} {n m : ℕ}
    (h : CFC.abs x ≤ (n : ℝ) • CFC.abs a) (hnm : n ≤ m) :
    CFC.abs x ≤ (m : ℝ) • CFC.abs a :=
  le_trans h (rsmul_mono' (by exact_mod_cast hnm) (CFC.abs_nonneg a))

private theorem sa_coe (x : selfAdjoint 𝒜) : IsSelfAdjoint (x : 𝒜) := x.2

private theorem isSelfAdjoint_rsmul (r : ℝ) {x : 𝒜} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := (IsSelfAdjoint.all r).smul hx

private theorem absDom_zero (a : 𝒜) : AbsDom a 0 :=
  ⟨0, by simp⟩

private theorem absDom_add {a x y : 𝒜} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxd : AbsDom a x) (hyd : AbsDom a y) : AbsDom a (x + y) := by
  obtain ⟨n, hn⟩ := hxd
  obtain ⟨m, hm⟩ := hyd
  refine ⟨n + m, le_trans (abs_add_le x y hx hy) ?_⟩
  have h := add_le_add hn hm
  rwa [← add_smul, ← Nat.cast_add] at h

private theorem absDom_neg {a x : 𝒜} (h : AbsDom a x) : AbsDom a (-x) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rwa [CFC.abs_neg]⟩

private theorem absDom_rsmul {a x : 𝒜} (r : ℝ) (h : AbsDom a x) : AbsDom a (r • x) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨⌈|r| * (n : ℝ)⌉₊, ?_⟩
  have hcoe : r • x = ((r : ℂ)) • x := (Complex.coe_smul r x).symm
  rw [hcoe, CFC.abs_smul]
  have hnr : ‖(r : ℂ)‖ = |r| := by simp
  rw [hnr]
  calc |r| • CFC.abs x ≤ |r| • ((n : ℝ) • CFC.abs a) := rsmul_mono (abs_nonneg r) hn
    _ = (|r| * (n : ℝ)) • CFC.abs a := by rw [smul_smul]
    _ ≤ (⌈|r| * (n : ℝ)⌉₊ : ℝ) • CFC.abs a :=
        rsmul_mono' (Nat.le_ceil _) (CFC.abs_nonneg a)

/-- **27X**.1: the least Riesz ideal containing the self-adjoint `a`. -/
private def rieszIdealGen (a : 𝒜) : Submodule ℂ 𝒜 where
  carrier := {b | AbsDom a (ℜ b : 𝒜) ∧ AbsDom a (ℑ b : 𝒜)}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, ZeroMemClass.coe_zero]
    exact ⟨absDom_zero a, absDom_zero a⟩
  add_mem' := by
    rintro b c ⟨hbr, hbi⟩ ⟨hcr, hci⟩
    refine ⟨?_, ?_⟩
    · rw [map_add, AddSubgroup.coe_add]
      exact absDom_add (ℜ b).2 (ℜ c).2 hbr hcr
    · rw [map_add, AddSubgroup.coe_add]
      exact absDom_add (ℑ b).2 (ℑ c).2 hbi hci
  smul_mem' := by
    rintro z b ⟨hbr, hbi⟩
    refine ⟨?_, ?_⟩
    · rw [realPart_smul]
      have he : ((z.re • ℜ b - z.im • ℑ b : selfAdjoint 𝒜) : 𝒜)
          = z.re • (ℜ b : 𝒜) + -(z.im • (ℑ b : 𝒜)) := by
        rw [AddSubgroup.coe_sub, selfAdjoint.val_smul, selfAdjoint.val_smul,
          sub_eq_add_neg]
      rw [he]
      exact absDom_add (isSelfAdjoint_rsmul _ (sa_coe (ℜ b)))
        (isSelfAdjoint_rsmul _ (sa_coe (ℑ b))).neg
        (absDom_rsmul _ hbr) (absDom_neg (absDom_rsmul _ hbi))
    · rw [imaginaryPart_smul]
      have he : ((z.re • ℑ b + z.im • ℜ b : selfAdjoint 𝒜) : 𝒜)
          = z.re • (ℑ b : 𝒜) + z.im • (ℜ b : 𝒜) := by
        rw [AddSubgroup.coe_add, selfAdjoint.val_smul, selfAdjoint.val_smul]
      rw [he]
      exact absDom_add (isSelfAdjoint_rsmul _ (sa_coe (ℑ b)))
        (isSelfAdjoint_rsmul _ (sa_coe (ℜ b)))
        (absDom_rsmul _ hbi) (absDom_rsmul _ hbr)

private theorem rsmul_nonneg {r : ℝ} (hr : 0 ≤ r) {x : 𝒜} (hx : 0 ≤ x) : 0 ≤ r • x := by
  have h := ofReal_smul_nonneg hx hr
  rwa [Complex.coe_smul] at h

private theorem mem_rieszIdealGen_iff {a b : 𝒜} :
    b ∈ rieszIdealGen a ↔ ∃ n : ℕ,
      CFC.abs (ℜ b : 𝒜) ≤ (n : ℝ) • CFC.abs a ∧
      CFC.abs (ℑ b : 𝒜) ≤ (n : ℝ) • CFC.abs a := by
  constructor
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    exact ⟨max n m, absDom_le hn (le_max_left _ _), absDom_le hm (le_max_right _ _)⟩
  · rintro ⟨n, h1, h2⟩
    exact ⟨⟨n, h1⟩, ⟨n, h2⟩⟩

private theorem self_mem_rieszIdealGen {a : 𝒜} (ha : IsSelfAdjoint a) :
    a ∈ rieszIdealGen a := by
  refine ⟨?_, ?_⟩
  · rw [ha.coe_realPart]
    exact ⟨1, by rw [Nat.cast_one, one_smul]⟩
  · rw [ha.imaginaryPart, ZeroMemClass.coe_zero]
    exact absDom_zero a

private theorem rieszIdealGen_isRieszIdeal {a : 𝒜} : IsRieszIdeal (rieszIdealGen a) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro b ⟨hbr, hbi⟩
    refine ⟨?_, ?_⟩
    · have h : (ℜ (star b) : 𝒜) = (ℜ b : 𝒜) := by
        rw [realPart_apply_coe, realPart_apply_coe, star_star, add_comm]
      rw [h]; exact hbr
    · have h : (ℑ (star b) : 𝒜) = -(ℑ b : 𝒜) := by
        rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star,
          ← smul_neg, ← smul_neg, neg_sub]
      rw [h]; exact absDom_neg hbi
  · rintro b ⟨hbr, -⟩ hb0 c h1 h2
    have hcsa : IsSelfAdjoint c := isSelfAdjoint_of_mem_interval' h1 h2
    have hbsa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg hb0
    rw [hbsa.coe_realPart] at hbr
    obtain ⟨n, hn⟩ := hbr
    rw [CFC.abs_of_nonneg b hb0] at hn
    refine ⟨?_, ?_⟩
    · rw [hcsa.coe_realPart]
      exact ⟨n, le_trans ((abs_le_iff c b hcsa).mpr ⟨h1, h2⟩) hn⟩
    · rw [hcsa.imaginaryPart, ZeroMemClass.coe_zero]
      exact absDom_zero a
  · rintro b ⟨hbr, -⟩ hbsa
    rw [hbsa.coe_realPart] at hbr
    obtain ⟨n, hn⟩ := hbr
    have habs0 : (0 : 𝒜) ≤ CFC.abs b := CFC.abs_nonneg b
    have habssa : IsSelfAdjoint (CFC.abs b) := IsSelfAdjoint.of_nonneg habs0
    refine ⟨?_, ?_⟩
    · rw [habssa.coe_realPart]
      exact ⟨n, by rw [CFC.abs_of_nonneg _ habs0]; exact hn⟩
    · rw [habssa.imaginaryPart, ZeroMemClass.coe_zero]
      exact absDom_zero a

private theorem rieszIdealGen_least {a : 𝒜} (ha : IsSelfAdjoint a)
    (J : Submodule ℂ 𝒜) (hJ : IsRieszIdeal J) (haJ : a ∈ J) :
    rieszIdealGen a ≤ J := by
  have habsJ : CFC.abs a ∈ J := hJ.2 a haJ ha
  have hdom : ∀ x : 𝒜, IsSelfAdjoint x → AbsDom a x → x ∈ J := by
    rintro x hx ⟨n, hn⟩
    have hmem : (n : ℝ) • CFC.abs a ∈ J := rsmul_mem habsJ _
    have hnn : (0 : 𝒜) ≤ (n : ℝ) • CFC.abs a :=
      rsmul_nonneg (Nat.cast_nonneg n) (CFC.abs_nonneg a)
    obtain ⟨h1, h2⟩ := (abs_le_iff x _ hx).mp hn
    exact hJ.1.mem_of_mem_interval _ hmem hnn x h1 h2
  rintro b ⟨hbr, hbi⟩
  have h := J.add_mem (hdom _ (sa_coe (ℜ b)) hbr)
    (J.smul_mem Complex.I (hdom _ (sa_coe (ℑ b)) hbi))
  rwa [realPart_add_I_smul_imaginaryPart] at h

/-- **27X** (`riesz-ideal-basic`, cstar.tex:4009, Exercise), part 1: the
least Riesz ideal containing a self-adjoint `a` is
`(a)ₘ = { b : |Re b|, |Im b| ≤ n|a| for some n ∈ ℕ }`. -/
theorem riesz_ideal_basic_1 (a : 𝒜) (ha : IsSelfAdjoint a) :
    ∃ I : Submodule ℂ 𝒜, IsRieszIdeal I ∧ a ∈ I ∧
      (∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → a ∈ J → I ≤ J) ∧
      ∀ b : 𝒜, b ∈ I ↔ ∃ n : ℕ,
        CFC.abs ((ℜ b : 𝒜)) ≤ (n : ℝ) • CFC.abs a ∧
        CFC.abs ((ℑ b : 𝒜)) ≤ (n : ℝ) • CFC.abs a :=
  ⟨rieszIdealGen a, rieszIdealGen_isRieszIdeal, self_mem_rieszIdealGen ha,
    fun J hJ haJ => rieszIdealGen_least ha J hJ haJ, fun _ => mem_rieszIdealGen_iff⟩

/-! ### 27XI, following the corrected proof of erratum `parsec-270.120` -/

/-- If `1` lies in `I ⊔ (a)ₘ` for positive `a`, then `1 ≤ |x| + n·a` for some
self-adjoint `x ∈ I` and some `n : ℕ`. -/
private theorem one_le_abs_add_nsmul_of_one_mem_sup {I : Submodule ℂ 𝒜}
    (hI : IsRieszIdeal I) {a : 𝒜} (ha : 0 ≤ a)
    (h1 : (1 : 𝒜) ∈ I ⊔ rieszIdealGen a) :
    ∃ x ∈ I, IsSelfAdjoint x ∧ ∃ n : ℕ, (1 : 𝒜) ≤ CFC.abs x + (n : ℝ) • a := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨hyre, -⟩ := re_im_mem hI.1 hy
  obtain ⟨n, hn⟩ := hz.1
  refine ⟨(ℜ y : 𝒜), hyre, sa_coe _, n, ?_⟩
  have hone : ((ℜ (1 : 𝒜) : 𝒜)) = (ℜ y : 𝒜) + (ℜ z : 𝒜) := by
    rw [← hyz, map_add, AddSubgroup.coe_add]
  have h1sa : IsSelfAdjoint (1 : 𝒜) := by simp [isSelfAdjoint_iff]
  rw [h1sa.coe_realPart] at hone
  have habsa : CFC.abs a = a := CFC.abs_of_nonneg a ha
  rw [habsa] at hn
  calc (1 : 𝒜) = CFC.abs (1 : 𝒜) := CFC.abs_one.symm
    _ = CFC.abs ((ℜ y : 𝒜) + (ℜ z : 𝒜)) := by rw [← hone]
    _ ≤ CFC.abs (ℜ y : 𝒜) + CFC.abs (ℜ z : 𝒜) := abs_add_le _ _ (sa_coe _) (sa_coe _)
    _ ≤ CFC.abs (ℜ y : 𝒜) + (n : ℝ) • a := add_le_add le_rfl hn

/-- The first half of erratum `parsec-270.120`: for positive `a, b` with
`ab = 0`, a maximal Riesz ideal contains `a` or `b`. -/
private theorem mem_or_mem_of_mul_eq_zero {I : Submodule ℂ 𝒜}
    (hI : IsMaximalRieszIdeal I) {a b : 𝒜} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b = 0) : a ∈ I ∨ b ∈ I := by
  by_cases hna : a ∈ I
  · exact Or.inl hna
  by_cases hnb : b ∈ I
  · exact Or.inr hnb
  exfalso
  -- maximality forces `1 ∈ I ⊔ (a)ₘ` and `1 ∈ I ⊔ (b)ₘ`
  have key : ∀ c : 𝒜, 0 ≤ c → c ∉ I → (1 : 𝒜) ∈ I ⊔ rieszIdealGen c := by
    intro c hc hnc
    by_contra hone
    have hsup : IsRieszIdeal (I ⊔ rieszIdealGen c) :=
      riesz_ideal_basic_2 I _ hI.1.1 rieszIdealGen_isRieszIdeal
    have heq := hI.2 _ hsup hone le_sup_left
    exact hnc (heq ▸ (le_sup_right : rieszIdealGen c ≤ I ⊔ rieszIdealGen c)
      (self_mem_rieszIdealGen (IsSelfAdjoint.of_nonneg hc)))
  obtain ⟨x, hxI, hxsa, n, hxn⟩ :=
    one_le_abs_add_nsmul_of_one_mem_sup hI.1.1 ha (key a ha hna)
  obtain ⟨y, hyI, hysa, m, hym⟩ :=
    one_le_abs_add_nsmul_of_one_mem_sup hI.1.1 hb (key b hb hnb)
  set u : 𝒜 := CFC.abs x + (n : ℝ) • a with hu
  set v : 𝒜 := CFC.abs y + (m : ℝ) • b with hv
  have hu0 : (0 : 𝒜) ≤ u := le_trans zero_le_one hxn
  -- `1 ≤ uv`, using **23VII**.1 (`sqrt_1`)
  have huv : (1 : 𝒜) ≤ u * v := by
    have h1 : (0 : 𝒜) ≤ u * (v - 1) :=
      sqrt_1 u (v - 1) hu0 (sub_nonneg.mpr hym) (mul_comm _ _)
    have h2 : (0 : 𝒜) ≤ u - 1 := sub_nonneg.mpr hxn
    have he : u * (v - 1) + (u - 1) = u * v - 1 := by noncomm_ring
    rw [← sub_nonneg, ← he]
    exact add_nonneg h1 h2
  -- `uv` lies in `I`, because `ab = 0` kills the only term that is not
  have habsx : CFC.abs x ∈ I := hI.1.1.2 x hxI hxsa
  have habsy : CFC.abs y ∈ I := hI.1.1.2 y hyI hysa
  have hexp : u * v = CFC.abs x * CFC.abs y + (n : ℝ) • (a * CFC.abs y)
      + (m : ℝ) • (b * CFC.abs x) := by
    rw [hu, hv]
    have hz : ((n : ℝ) • a) * ((m : ℝ) • b) = 0 := by
      rw [smul_mul_assoc, mul_smul_comm, hab, smul_zero, smul_zero]
    have hcomm : CFC.abs x * ((m : ℝ) • b) = (m : ℝ) • (b * CFC.abs x) := by
      rw [mul_smul_comm, mul_comm]
    have hcomm2 : ((n : ℝ) • a) * CFC.abs y = (n : ℝ) • (a * CFC.abs y) := by
      rw [smul_mul_assoc]
    rw [add_mul, mul_add, mul_add, hz, hcomm, hcomm2, add_zero]
    abel
  have huvI : u * v ∈ I := by
    rw [hexp]
    exact I.add_mem (I.add_mem (riesz_ideal_ring_ideal I hI.1.1 _ _ habsy)
      (rsmul_mem (riesz_ideal_ring_ideal I hI.1.1 _ _ habsy) _))
      (rsmul_mem (riesz_ideal_ring_ideal I hI.1.1 _ _ habsx) _)
  have huv0 : (0 : 𝒜) ≤ u * v := le_trans zero_le_one huv
  exact hI.1.2 (hI.1.1.1.mem_of_mem_interval _ huvI huv0 1
    (le_trans (neg_nonpos_of_nonneg huv0) zero_le_one) huv)

/-- **27XI** (`maximal-riesz-ideal-maximal-order-ideal`, cstar.tex:4036,
Lemma): a maximal Riesz ideal is a maximal order ideal.

The proof printed at cstar.tex 270.120 is the **corrected** one of erratum
`parsec-270.120` (`asols.tex:124–182`), which repairs an erroneous assumption
that `|a| ∈ J`; what follows transcribes it. -/
theorem maximal_riesz_ideal_maximal_order_ideal (I : Submodule ℂ 𝒜)
    (hI : IsMaximalRieszIdeal I) : IsMaximalOrderIdeal I := by
  refine ⟨⟨hI.1.1.1, hI.1.2⟩, fun J hJ hIJ => ?_⟩
  have hJriesz : IsRieszIdeal J := by
    refine ⟨hJ.1, fun c hc hcsa => ?_⟩
    have hmul : c⁺ * c⁻ = 0 := CFC.posPart_mul_negPart c
    have hc' : c⁺ - c⁻ = c := CFC.posPart_sub_negPart c hcsa
    have h3 : c⁺ = c + c⁻ := sub_eq_iff_eq_add.mp hc'
    have hboth : c⁺ ∈ J ∧ c⁻ ∈ J := by
      rcases mem_or_mem_of_mul_eq_zero hI (CFC.posPart_nonneg c)
        (CFC.negPart_nonneg c) hmul with h | h
      · refine ⟨hIJ h, ?_⟩
        have h2 := J.sub_mem (hIJ h) hc
        have he : c⁺ - c = c⁻ := by rw [h3]; abel
        rwa [he] at h2
      · exact ⟨h3 ▸ J.add_mem hc (hIJ h), hIJ h⟩
    rw [← CFC.posPart_add_negPart c hcsa]
    exact J.add_mem hboth.1 hboth.2
  exact hI.2 J hJriesz hJ.2 hIJ

/-- **27XIII** (`riesz-ideal-miu-map`, cstar.tex:4101, Lemma): for every
maximal Riesz ideal `I` of `𝒜` there is an miu-map `f : 𝒜 → ℂ` with
`ker(f) = I`. -/
theorem riesz_ideal_miu_map (I : Submodule ℂ 𝒜) (hI : IsMaximalRieszIdeal I) :
    ∃ f : 𝒜 →⋆ₐ[ℂ] ℂ, ∀ a : 𝒜, f a = 0 ↔ a ∈ I := by
  obtain ⟨ω, ⟨hpos, hone⟩, hker⟩ :=
    maximal_ideal_state I (maximal_riesz_ideal_maximal_order_ideal I hI)
  have hstar : ∀ a : 𝒜, ω (star a) = star (ω a) := cstar_p_implies_i ω hpos
  -- multiplicativity, by the thesis's own four lines
  have hmul : ∀ a b : 𝒜, ω (a * b) = ω a * ω b := by
    intro a b
    have hbI : b - ω b • (1 : 𝒜) ∈ I := by
      rw [← hker, LinearMap.mem_ker, map_sub, map_smul, hone, smul_eq_mul, mul_one,
        sub_self]
    have hmem : a * (b - ω b • (1 : 𝒜)) ∈ I := riesz_ideal_ring_ideal I hI.1.1 a _ hbI
    have hz : ω (a * (b - ω b • (1 : 𝒜))) = 0 := by
      rw [← LinearMap.mem_ker, hker]; exact hmem
    rw [mul_sub, map_sub, mul_smul_comm, mul_one, map_smul, smul_eq_mul, sub_eq_zero] at hz
    rw [hz, mul_comm]
  let f : 𝒜 →⋆ₐ[ℂ] ℂ :=
    { toFun := ω
      map_one' := hone
      map_mul' := hmul
      map_zero' := map_zero ω
      map_add' := map_add ω
      commutes' := fun r => by simp [Algebra.algebraMap_eq_smul_one, hone]
      map_star' := hstar }
  refine ⟨f, fun a => ?_⟩
  show ω a = 0 ↔ a ∈ I
  rw [← hker, LinearMap.mem_ker]

/-! ### 27X.1b and 27X.1c -/

private theorem least_eq_rieszIdealGen {a : 𝒜} (ha : IsSelfAdjoint a)
    (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I) (haI : a ∈ I)
    (hleast : ∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → a ∈ J → I ≤ J) :
    I = rieszIdealGen a :=
  le_antisymm (hleast _ rieszIdealGen_isRieszIdeal (self_mem_rieszIdealGen ha))
    (rieszIdealGen_least ha I hI haI)

/-- Copy of the file-private `isUnit_of_one_le_smul` of `Positive.lean`. -/
private theorem isUnit_of_one_le_rsmul {a : 𝒜} (hpos : 0 ≤ a) {m : ℝ}
    (hm : (1 : 𝒜) ≤ m • a) : IsUnit a := by
  rcases subsingleton_or_nontrivial 𝒜 with hsub | hnt
  · exact isUnit_of_subsingleton a
  have hmpos : 0 < m := by
    rcases le_or_gt m 0 with hle | hgt
    · exfalso
      have h2 : (0 : 𝒜) ≤ (-m) • a := rsmul_nonneg (by linarith) hpos
      rw [neg_smul] at h2
      have h3 : (1 : 𝒜) ≤ 0 := le_trans hm (neg_nonneg.mp h2)
      exact one_ne_zero (α := 𝒜) (le_antisymm h3 zero_le_one)
    · exact hgt
  have hinv : m⁻¹ • (1 : 𝒜) ≤ a := by
    have h2 := rsmul_mono (le_of_lt (inv_pos.mpr hmpos)) hm
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hmpos), one_smul] at h2
  obtain ⟨n, hn⟩ := exists_nat_gt m
  have hn0 : (0 : ℝ) < n := lt_trans hmpos hn
  refine (positive_basic_2_6 a hpos).mpr ⟨n, by exact_mod_cast hn0, ?_⟩
  have hle2 : ((n : ℝ))⁻¹ ≤ m⁻¹ := inv_anti₀ hmpos (le_of_lt hn)
  have hcast : ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  calc algebraMap ℂ 𝒜 (((n : ℝ)⁻¹ : ℝ) : ℂ)
      ≤ algebraMap ℂ 𝒜 ((m⁻¹ : ℝ) : ℂ) := algebraMap_ofReal_mono hle2
    _ = m⁻¹ • (1 : 𝒜) := by rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    _ ≤ a := hinv

/-- `|a|` and `a` are units together: `|a|² = a²`. -/
private theorem isUnit_abs_iff {a : 𝒜} (ha : IsSelfAdjoint a) :
    IsUnit (CFC.abs a) ↔ IsUnit a := by
  have hsq : CFC.abs a * CFC.abs a = a * a := by
    rw [CFC.abs_mul_abs, ha.star_eq]
  constructor
  · intro h
    have : IsUnit (a * a) := hsq ▸ h.mul h
    exact isUnit_of_mul_isUnit_left this
  · intro h
    have : IsUnit (CFC.abs a * CFC.abs a) := hsq ▸ h.mul h
    exact isUnit_of_mul_isUnit_left this

/-- `(a)ₘ` is proper unless `a` is invertible: this is the half of **27X**.1b
that **27XV** needs. -/
private theorem isUnit_of_one_mem_rieszIdealGen {a : 𝒜} (ha : IsSelfAdjoint a)
    (h1 : (1 : 𝒜) ∈ rieszIdealGen a) : IsUnit a := by
  obtain ⟨n, hn⟩ := h1.1
  have h1sa : IsSelfAdjoint (1 : 𝒜) := by simp [isSelfAdjoint_iff]
  rw [h1sa.coe_realPart, CFC.abs_one] at hn
  exact (isUnit_abs_iff ha).mp (isUnit_of_one_le_rsmul (CFC.abs_nonneg a) hn)

/-- **27X** (`riesz-ideal-basic`, cstar.tex:4009, Exercise), part 1b: the
least Riesz ideal containing a self-adjoint `a` is all of `𝒜` iff `a` is
invertible. -/
theorem riesz_ideal_basic_1b (a : 𝒜) (ha : IsSelfAdjoint a)
    (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I) (haI : a ∈ I)
    (hleast : ∀ J : Submodule ℂ 𝒜, IsRieszIdeal J → a ∈ J → I ≤ J) :
    I = ⊤ ↔ IsUnit a := by
  rw [least_eq_rieszIdealGen ha I hI haI hleast]
  constructor
  · intro htop
    exact isUnit_of_one_mem_rieszIdealGen ha (htop ▸ Submodule.mem_top)
  · intro hu
    obtain ⟨n, hn0, hle⟩ :=
      (positive_basic_2_6 _ (CFC.abs_nonneg a)).mp ((isUnit_abs_iff ha).mpr hu)
    have hcast : ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at hle
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hone : (1 : 𝒜) ≤ (n : ℝ) • CFC.abs a := by
      have h2 := rsmul_mono (le_of_lt hn0') hle
      rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hn0'), one_smul] at h2
    -- every self-adjoint `x` is then dominated: `|x| ≤ ‖x‖·1 ≤ ‖x‖n·|a|`
    have hdom : ∀ x : 𝒜, IsSelfAdjoint x → AbsDom a x := by
      intro x hx
      refine ⟨⌈‖x‖ * (n : ℝ)⌉₊, ?_⟩
      obtain ⟨hlo, hhi⟩ := (norm_le_iff_neg_algebraMap_le hx (norm_nonneg x)).mp le_rfl
      have hax : CFC.abs x ≤ ‖x‖ • (1 : 𝒜) := by
        refine (abs_le_iff x _ hx).mpr ?_
        rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at hlo hhi
        exact ⟨hlo, hhi⟩
      calc CFC.abs x ≤ ‖x‖ • (1 : 𝒜) := hax
        _ ≤ ‖x‖ • ((n : ℝ) • CFC.abs a) := rsmul_mono (norm_nonneg x) hone
        _ = (‖x‖ * (n : ℝ)) • CFC.abs a := by rw [smul_smul]
        _ ≤ (⌈‖x‖ * (n : ℝ)⌉₊ : ℝ) • CFC.abs a :=
            rsmul_mono' (Nat.le_ceil _) (CFC.abs_nonneg a)
    refine eq_top_iff.mpr fun b _ => ⟨hdom _ (sa_coe (ℜ b)), hdom _ (sa_coe (ℑ b))⟩

/-- **27X** (`riesz-ideal-basic`, cstar.tex:4009, Exercise), part 1c: for
positive `a` the least Riesz ideal `(a)ₘ` coincides with the least order
ideal `(a)` (of **22III**).  (For non-positive `a` they may differ; that
claim is not converted.) -/
theorem riesz_ideal_basic_1c (a : 𝒜) (ha : 0 ≤ a) (I J : Submodule ℂ 𝒜)
    (hI : IsRieszIdeal I) (haI : a ∈ I)
    (hIleast : ∀ K : Submodule ℂ 𝒜, IsRieszIdeal K → a ∈ K → I ≤ K)
    (hJ : IsOrderIdeal J) (haJ : a ∈ J)
    (hJleast : ∀ K : Submodule ℂ 𝒜, IsOrderIdeal K → a ∈ K → J ≤ K) :
    I = J := by
  have hasa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  obtain ⟨K, hK, haK, hKleast, hKchar⟩ := order_ideal_basic_3a a hasa
  have hJK : J = K := le_antisymm (hJleast K hK haK) (hKleast J hJ haJ)
  -- `(a)` is a Riesz ideal when `a ≥ 0`
  have hJriesz : IsRieszIdeal J := by
    refine ⟨hJ, fun c hc hcsa => ?_⟩
    rw [hJK] at hc ⊢
    obtain ⟨lam, mu, hlo, hhi⟩ := (hKchar c hcsa).mp hc
    set nu : ℝ := max mu (-lam) with hnu
    have h1 : c ≤ nu • a := le_trans hhi (rsmul_mono' (le_max_left _ _) ha)
    have h2 : -c ≤ nu • a := by
      refine le_trans ?_ (rsmul_mono' (le_max_right _ _) ha)
      rw [neg_smul]
      exact neg_le_neg hlo
    have habs : CFC.abs c ≤ nu • a := (abs_le_iff c _ hcsa).mpr ⟨neg_le_of_neg_le h2, h1⟩
    refine (hKchar _ (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg c))).mpr
      ⟨0, nu, ?_, habs⟩
    rw [zero_smul]
    exact CFC.abs_nonneg c
  exact le_antisymm (hIleast J hJriesz haJ) (hJleast I hI.1 haI)

/-- **27XV** (`inv-mult-state`, cstar.tex:4122, Proposition): a self-adjoint
element `a` of the commutative C*-algebra `𝒜` is not invertible iff
`f(a) = 0` for some `f ∈ spec(𝒜)`. -/
theorem inv_mult_state (a : 𝒜) (ha : IsSelfAdjoint a) :
    ¬IsUnit a ↔ ∃ φ : characterSpace ℂ 𝒜, φ a = 0 := by
  constructor
  · -- This is now the **thesis's own** route (cstar.tex:4060): the least Riesz
    -- ideal `(a)ₘ` containing `a` is proper, extend it to a maximal Riesz ideal
    -- by **27X**.3, and apply **27XIII**.  Until the 270 chain was proved this
    -- direction went through Mathlib's Gelfand theory, which reaches the
    -- character space through maximal *ring* ideals — exactly the route
    -- **16VIII** (cstar.tex:2678) rejects.  That detour is gone.
    intro h
    have hproper : (1 : 𝒜) ∉ rieszIdealGen a := fun h1 =>
      h (isUnit_of_one_mem_rieszIdealGen ha h1)
    obtain ⟨J, hJmax, hJle⟩ :=
      riesz_ideal_basic_3 _ rieszIdealGen_isRieszIdeal hproper
    obtain ⟨f, hf⟩ := riesz_ideal_miu_map J hJmax
    refine ⟨WeakDual.CharacterSpace.equivAlgHom.symm f.toAlgHom, ?_⟩
    have : (WeakDual.CharacterSpace.equivAlgHom.symm f.toAlgHom : 𝒜 → ℂ) = f :=
      WeakDual.CharacterSpace.equivAlgHom_symm_coe f.toAlgHom
    rw [show (WeakDual.CharacterSpace.equivAlgHom.symm f.toAlgHom) a = f a from
      congrFun this a]
    exact (hf a).mpr (hJle (self_mem_rieszIdealGen ha))
  · -- The easy direction is the thesis's own, and elementary: `φ(a) ∈ spec(a)`
    -- because `a - φ(a)` lies in `ker φ`, which contains no unit.
    rintro ⟨φ, hφ⟩
    rw [← spectrum.zero_mem_iff (R := ℂ), ← hφ]
    exact WeakDual.CharacterSpace.apply_mem_spectrum φ a

end Order

/-- **27XVII** (`spectrum-miu`, cstar.tex:4145, Exercise):
`spec(a) = { f(a) : f ∈ spec(𝒜) }` for self-adjoint `a ∈ 𝒜`.

*Class 1 — faithful.*  The exercise's own derivation from **27XV**
`inv_mult_state`: a point `λ` of `spec(a)` is real (`a` being self-adjoint),
so `λ − a` is self-adjoint and non-invertible, and **27XV** produces a
character killing it, i.e. one with `f(a) = λ`; conversely `f(a) ∈ spec(a)`
is **27XV**'s easy direction.

Mathlib's `WeakDual.CharacterSpace.mem_spectrum_iff_exists` is deliberately
not used: its proof reaches the character space through maximal *ring*
ideals, the route **16VIII** (cstar.tex:2678) rejects.  The two order
instances the statement needs are supplied locally by
`CStarAlgebra.spectralOrder`. -/
theorem spectrum_miu (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ a = Set.range fun φ : characterSpace ℂ 𝒜 => φ a := by
  letI : PartialOrder 𝒜 := CStarAlgebra.spectralOrder 𝒜
  haveI : StarOrderedRing 𝒜 := CStarAlgebra.spectralOrderedRing 𝒜
  refine Set.ext fun z => ⟨fun hz => ?_, ?_⟩
  · have hre : z = (z.re : ℂ) := mem_spectrum_eq_re_of_isSelfAdjoint ha hz
    have hsa : IsSelfAdjoint (algebraMap ℂ 𝒜 z - a) := by
      refine IsSelfAdjoint.sub (IsSelfAdjoint.algebraMap 𝒜 ?_) ha
      show star z = z
      rw [hre, Complex.star_def, Complex.conj_ofReal]
    obtain ⟨φ, hφ⟩ := (inv_mult_state _ hsa).mp (spectrum.mem_iff.mp hz)
    refine ⟨φ, ?_⟩
    rw [map_sub, AlgHomClass.commutes] at hφ
    exact (sub_eq_zero.mp hφ).symm
  · rintro ⟨φ, rfl⟩
    exact WeakDual.CharacterSpace.apply_mem_spectrum φ a

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4149,
Exercise), part 1: the Gelfand representation is an isometry,
`‖γ(a)‖ = ‖a‖`.

*Class 1 — faithful.*  The Exercise's own hint (cstar.tex:4086): for
self-adjoint `a` the range of `γ(a)` is `spec(a)` by **27XVII**
`spectrum_miu` — the spectrum of an element of `C(spec 𝒜)` being its range —
so `γ(a)` and `a` have the same spectral radius, and **16II**
`norm_spectrum` turns that into `‖γ(a)‖ = ‖a‖`.  The general case is the
C*-identity: `‖γ(a)‖² = ‖γ(a)*γ(a)‖ = ‖γ(a*a)‖ = ‖a*a‖ = ‖a‖²`.

Mathlib's `gelfandTransform_isometry` is deliberately not used: its proof
runs through `WeakDual.CharacterSpace.mem_spectrum_iff_exists` and so through
maximal *ring* ideals, the route **16VIII** rejects. -/
theorem gelfand_representation_isometry (a : 𝒜) :
    ‖gelfandTransform ℂ 𝒜 a‖ = ‖a‖ := by
  -- the self-adjoint case, by **27XVII** and **16II**
  have hsa : ∀ b : 𝒜, IsSelfAdjoint b → ‖gelfandTransform ℂ 𝒜 b‖ = ‖b‖ := by
    intro b hb
    have hγsa : IsSelfAdjoint (gelfandTransform ℂ 𝒜 b) := by
      rw [IsSelfAdjoint, ← gelfand_representation_basic_2, hb.star_eq]
    have hspec : spectrum ℂ (gelfandTransform ℂ 𝒜 b) = spectrum ℂ b := by
      rw [ContinuousMap.spectrum_eq_range]
      exact (spectrum_miu b hb).symm
    have hr : spectralRadius ℂ (gelfandTransform ℂ 𝒜 b) = spectralRadius ℂ b := by
      unfold spectralRadius
      rw [hspec]
    rw [norm_spectrum _ hγsa, norm_spectrum b hb] at hr
    exact congrArg NNReal.toReal (ENNReal.coe_inj.mp hr)
  -- the general case, by the C*-identity
  have hstar : star (gelfandTransform ℂ 𝒜 a) * gelfandTransform ℂ 𝒜 a
      = gelfandTransform ℂ 𝒜 (star a * a) := by
    rw [map_mul, gelfand_representation_basic_2]
  have h2 : ‖gelfandTransform ℂ 𝒜 a‖ * ‖gelfandTransform ℂ 𝒜 a‖ = ‖a‖ * ‖a‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar, hsa _ (IsSelfAdjoint.star_mul_self a),
      CStarRing.norm_star_mul_self]
  nlinarith [norm_nonneg (gelfandTransform ℂ 𝒜 a), norm_nonneg a]

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4149,
Exercise), part 2, first clause: consequently `γ` is injective.

*Class 1 — faithful.*  The Exercise's own "conclude": `γ(a) = γ(b)` makes
`‖a − b‖ = ‖γ(a − b)‖ = 0` by part 1. -/
theorem gelfand_representation_injective :
    Function.Injective (gelfandTransform ℂ 𝒜) := by
  intro a b hab
  have h : ‖a - b‖ = 0 := by
    rw [← gelfand_representation_isometry (a - b), map_sub, hab, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h)

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4149,
Exercise), part 2, second clause: the range of `γ` is a *C*-subalgebra* of
`C(spec 𝒜)` — a ⋆-subalgebra whose carrier is closed — and `γ` is an
miu-isomorphism of `𝒜` onto it.

*Class 1 — faithful.*  Both clauses come straight from part 1: an isometry of
a complete space is a closed embedding, so its range is closed, and an
injective ⋆-homomorphism corestricts to an isomorphism onto its range. -/
theorem gelfand_representation_range :
    ∃ S : StarSubalgebra ℂ C(characterSpace ℂ 𝒜, ℂ),
      (S : Set C(characterSpace ℂ 𝒜, ℂ)) = Set.range (gelfandTransform ℂ 𝒜) ∧
        IsClosed (S : Set C(characterSpace ℂ 𝒜, ℂ)) ∧
        ∃ e : 𝒜 ≃⋆ₐ[ℂ] S, ∀ a : 𝒜, Subtype.val (e a) = gelfandTransform ℂ 𝒜 a := by
  refine ⟨StarAlgHom.range (gelfandStarTransform 𝒜 : 𝒜 →⋆ₐ[ℂ] _), rfl, ?_,
    StarAlgEquiv.ofInjective _ gelfand_representation_injective, fun _ => rfl⟩
  show IsClosed (Set.range (gelfandTransform ℂ 𝒜))
  exact (AddMonoidHomClass.isometry_of_norm (gelfandTransform ℂ 𝒜)
    gelfand_representation_isometry).isClosedEmbedding.isClosed_range

/-! ### The printed route to **27XX** (Stone–Weierstraß), cstar.tex:4180–4250

The thesis proves **27XX** by the *lattice* argument **27XXI**–**27XXIV**, not
by polynomial approximation of `t ↦ |t|` (which is what Mathlib's
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`
runs on).  It can, because its `𝒮` is a **C*-subalgebra**: the modulus is
`|f| = √(f* f)` and the square root is the one of **23VII** (`sqrt`,
cstar.tex:3653, parsec 230, hence available at parsec 270), which stays inside
a *closed* ⋆-subalgebra because it is the norm limit of the **23II** iteration
`b₀ = 0`, `bₙ₊₁ = ½(a + bₙ²)`, all of whose terms are polynomials in `a`
without constant term.  That is `sqrt_mem_of_isClosed` below.

Nothing here reaches forward to parsec 280: `CFC.sqrt` occurs only as the name
under which the tree already states **23VII**.0, and every step that computes
with it goes through the *uniqueness* of positive square roots
(`sqrt_existsUnique`, **23VII**.0), never through `cfc` or **28II**.4.  In
particular `sqrt_apply` — that the square root in `C(X, ℂ)` is the pointwise
one — is proved by exhibiting the pointwise root and appealing to that
uniqueness.

The printed argument itself is run on the self-adjoint part of `C(X, ℂ)`,
which is `C(X, ℝ)`; that is where the `⊔`, `⊓` and `≤` of the printed proof
live, and `C(X, ℝ)` carries them as instances.  `realSub S` is the subalgebra
of real-valued elements of `S`, i.e. the print's "replacing `f` by `Re f` or
`Im f`" (**27XXII**) made into a definition. -/

section StoneWeierstrassAux

/-- Every term of the **23II** iteration `b₀ = 0`, `bₙ₊₁ = ½(a + bₙ²)` of
cstar.tex:3485, which the tree carries as `sqrtApproxSeq`, is a polynomial in
`a` with zero constant term, hence lies in every ⋆-subalgebra containing
`a`. -/
private theorem sqrtApproxSeq_mem {𝒜 : Type*} [CStarAlgebra 𝒜]
    (S : StarSubalgebra ℂ 𝒜) {a : 𝒜} (ha : a ∈ S) :
    ∀ n : ℕ, sqrtApproxSeq a n ∈ S := by
  intro n
  induction n with
  | zero => exact (show (0 : 𝒜) ∈ S from zero_mem S)
  | succ n ih =>
      exact (show (2 : ℂ)⁻¹ • (a + sqrtApproxSeq a n ^ 2) ∈ S from
        S.smul_mem (S.add_mem ha (S.pow_mem ih 2)) _)

/-- `(r • x)² = r² • x²`. -/
private theorem smul_sq' {𝒜 : Type*} [CStarAlgebra 𝒜] (r : ℂ) (x : 𝒜) :
    (r • x) ^ 2 = (r * r) • x ^ 2 := by
  rw [sq, sq, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A self-adjoint element of norm at most one is below `1` — **17VI**.3a
`positive_basic_2_3a`, restated because `Positive.lean`'s helper of this name
is `private`. -/
private theorem le_one_of_norm_le_one' {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] {x : 𝒜} (hsa : IsSelfAdjoint x) (h : ‖x‖ ≤ 1) : x ≤ 1 := by
  have h2 := (positive_basic_2_3a x hsa 1 zero_le_one).mpr h
  simpa using h2.2

/-- **The missing lemma of the printed proof**: the square root of a positive
element of a *closed* ⋆-subalgebra lies in that subalgebra.  By **23II** the
square root of `a` is `√‖a‖ · (1 - b)` with `b = lim bₙ` the limit of the
iteration applied to `1 - ‖a‖⁻¹a`; every `bₙ` lies in the subalgebra, and the
subalgebra is closed.  That this element *is* `√a` is the uniqueness of
positive square roots, **23VII**.0. -/
private theorem sqrt_mem_of_isClosed {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (S : StarSubalgebra ℂ 𝒜) (hS : IsClosed (S : Set 𝒜))
    {a : 𝒜} (ha : 0 ≤ a) (haS : a ∈ S) : CFC.sqrt a ∈ S := by
  rcases eq_or_lt_of_le (norm_nonneg a) with hs | hs
  · have h0 : a = 0 := norm_eq_zero.mp hs.symm
    subst h0
    have hz : (0 : 𝒜) = CFC.sqrt 0 :=
      (sqrt_existsUnique (0 : 𝒜) le_rfl).unique ⟨le_rfl, by simp, by simp⟩
        (sqrt_spec (0 : 𝒜) le_rfl)
    rw [← hz]
    exact zero_mem S
  · have hr0 : (0 : ℝ) ≤ ‖a‖⁻¹ := by positivity
    set y : 𝒜 := ((‖a‖⁻¹ : ℝ) : ℂ) • a with hy
    have hy0 : 0 ≤ y := ofReal_smul_nonneg ha hr0
    have hyn : ‖y‖ ≤ 1 := by
      rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        inv_mul_cancel₀ (ne_of_gt hs)]
    have hy1 : y ≤ 1 := le_one_of_norm_le_one' (IsSelfAdjoint.of_nonneg hy0) hyn
    have hyS : y ∈ S := S.smul_mem haS _
    have hc0 : (0 : 𝒜) ≤ 1 - y := sub_nonneg.mpr hy1
    have hc1 : (1 : 𝒜) - y ≤ 1 := sub_le_self 1 hy0
    have hcS : (1 : 𝒜) - y ∈ S := S.sub_mem (one_mem S) hyS
    obtain ⟨b, hb, -⟩ := sqrt_lemma_existsUnique (1 - y) hc0 hc1
    have hlim : Tendsto (sqrtApproxSeq (1 - y)) atTop (𝓝 b) :=
      sqrt_lemma_tendsto (1 - y) hc0 hc1 b hb
    have hbS : b ∈ S :=
      hS.mem_of_tendsto hlim (Eventually.of_forall (sqrtApproxSeq_mem S hcS))
    obtain ⟨hb0, hb1, hbc, hbsq⟩ := hb
    have hd0 : (0 : 𝒜) ≤ 1 - b := sub_nonneg.mpr hb1
    have hd2 : (1 - b) ^ 2 = y := by rw [hbsq]; abel
    have hdS : (1 : 𝒜) - b ∈ S := S.sub_mem (one_mem S) hbS
    have hac : a * (1 - y) = (1 - y) * a := by
      rw [hy, mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    have hab : a * b = b * a :=
      (sqrt_lemma_commute (1 - y) hc0 hc1 b ⟨hb0, hb1, hbc, hbsq⟩ a hac).1
    set e : 𝒜 := ((Real.sqrt ‖a‖ : ℝ) : ℂ) • (1 - b) with he
    have he0 : 0 ≤ e := ofReal_smul_nonneg hd0 (Real.sqrt_nonneg _)
    have he2 : e ^ 2 = a := by
      rw [he, smul_sq', hd2, hy, ← Complex.ofReal_mul, Real.mul_self_sqrt hs.le,
        smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hs),
        Complex.ofReal_one, one_smul]
    have hea : a * e = e * a := by
      rw [he, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hab]
    have hcfc : e = CFC.sqrt a :=
      (sqrt_existsUnique a ha).unique ⟨he0, he2, hea⟩ (sqrt_spec a ha)
    rw [← hcfc, he]
    exact S.smul_mem hdS _

section NonCompact

variable {X : Type*} [TopologicalSpace X]

/-- The inclusion `C(X, ℝ) → C(X, ℂ)`. -/
private noncomputable def ofRealCM : C(X, ℝ) →ₐ[ℝ] C(X, ℂ) :=
  (RCLike.ofRealAm (K := ℂ)).compLeftContinuous ℝ RCLike.continuous_ofReal

private theorem ofRealCM_apply (u : C(X, ℝ)) (x : X) : ofRealCM u x = ((u x : ℝ) : ℂ) := rfl

/-- The real-valued part of a ⋆-subalgebra of `C(X, ℂ)`: an `ℝ`-subalgebra of
`C(X, ℝ)`. -/
private noncomputable def realSub (S : StarSubalgebra ℂ C(X, ℂ)) : Subalgebra ℝ C(X, ℝ) :=
  (S.restrictScalars ℝ).comap ofRealCM

private theorem mem_realSub {S : StarSubalgebra ℂ C(X, ℂ)} {u : C(X, ℝ)} :
    u ∈ realSub S ↔ ofRealCM u ∈ S := Iff.rfl

/-- A unital subalgebra of `C(X, ℝ)` contains the constants — the print's
`g(y)` and `ε` as elements of `𝒮`. -/
private theorem const_mem (A : Subalgebra ℝ C(X, ℝ)) (t : ℝ) :
    ContinuousMap.const X t ∈ A := by
  have h := A.algebraMap_mem t
  convert h using 1
  ext x
  simp

/-- **27XXII** (`stone-weierstrass-1`, cstar.tex:4192): for `x ≠ y` and
`t ≥ 0` there is `u ∈ 𝒮` with `0 ≤ u ≤ t`, `u(x) = 0` and `u(y) = t`.  The
print's five successive replacements: `f - f(x)` kills the value at `x`, `Re`
or `Im` makes it self-adjoint (here: we are already in `C(X, ℝ)`), `f₊` or
`f₋` makes it positive, a scalar makes `u(y) = t`, and `u ⊓ t` caps it. -/
private theorem sw_two_point (A : Subalgebra ℝ C(X, ℝ))
    (hinf : ∀ u ∈ A, ∀ v ∈ A, u ⊓ v ∈ A) (hsup : ∀ u ∈ A, ∀ v ∈ A, u ⊔ v ∈ A)
    (hsep : ∀ x y : X, x ≠ y → ∃ u ∈ A, u x ≠ u y)
    {x y : X} (hxy : x ≠ y) {t : ℝ} (ht : 0 ≤ t) :
    ∃ u ∈ A, (∀ z, 0 ≤ u z) ∧ (∀ z, u z ≤ t) ∧ u x = 0 ∧ u y = t := by
  obtain ⟨f, hfA, hfne⟩ := hsep x y hxy
  set f₁ : C(X, ℝ) := f - ContinuousMap.const X (f x) with hf₁
  have hf₁A : f₁ ∈ A := A.sub_mem hfA (const_mem A _)
  have hf₁x : f₁ x = 0 := by simp [hf₁]
  have hf₁y : f₁ y ≠ 0 := by
    simp only [hf₁, ContinuousMap.sub_apply, ContinuousMap.const_apply]
    exact sub_ne_zero.mpr (Ne.symm hfne)
  obtain ⟨v, hvA, hv0, hvx, hvy⟩ :
      ∃ v ∈ A, (∀ z, 0 ≤ v z) ∧ v x = 0 ∧ 0 < v y := by
    rcases lt_or_gt_of_ne hf₁y with hneg | hpos
    · refine ⟨(-f₁) ⊔ 0, hsup _ (A.neg_mem hf₁A) _ (zero_mem A), fun z => ?_, ?_, ?_⟩
      · simp only [ContinuousMap.sup_apply, ContinuousMap.neg_apply, ContinuousMap.zero_apply]
        exact le_max_right _ _
      · simp [hf₁x]
      · rw [ContinuousMap.sup_apply, ContinuousMap.neg_apply, ContinuousMap.zero_apply,
          lt_max_iff]
        exact Or.inl (by linarith)
    · refine ⟨f₁ ⊔ 0, hsup _ hf₁A _ (zero_mem A), fun z => ?_, ?_, ?_⟩
      · simp only [ContinuousMap.sup_apply, ContinuousMap.zero_apply]
        exact le_max_right _ _
      · simp [hf₁x]
      · rw [ContinuousMap.sup_apply, ContinuousMap.zero_apply, lt_max_iff]
        exact Or.inl hpos
  set w : C(X, ℝ) := (t / v y) • v with hw
  have hwA : w ∈ A := A.smul_mem hvA _
  have hwx : w x = 0 := by simp [hw, hvx]
  have hwy : w y = t := by
    simp only [hw, ContinuousMap.smul_apply, smul_eq_mul]
    field_simp
  have hw0 : ∀ z, 0 ≤ w z := by
    intro z
    have h1 : 0 ≤ t / v y := div_nonneg ht hvy.le
    simpa [hw] using mul_nonneg h1 (hv0 z)
  refine ⟨w ⊓ ContinuousMap.const X t, hinf _ hwA _ (const_mem A t), fun z => ?_,
    fun z => ?_, ?_, ?_⟩
  · simp only [ContinuousMap.inf_apply, ContinuousMap.const_apply]
    exact le_min (hw0 z) ht
  · simp only [ContinuousMap.inf_apply, ContinuousMap.const_apply]
    exact min_le_right _ _
  · simp only [ContinuousMap.inf_apply, ContinuousMap.const_apply, hwx]
    exact min_eq_left ht
  · simp only [ContinuousMap.inf_apply, ContinuousMap.const_apply, hwy]
    exact min_self t

end NonCompact

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The square root of a positive `f ∈ C(X, ℂ)` is the pointwise one.  Proved
from the uniqueness of positive square roots (**23VII**.0) alone: the
pointwise root is positive, squares to `f` and commutes with it.  (The cheap
route — restrict the evaluation character and use **28II**.4 — is barred by
the `docs/DECISIONS.md` §2.2 ruling, parsec 280 being later than 270.) -/
private theorem sqrt_apply {f : C(X, ℂ)} (hf : 0 ≤ f) (x : X) :
    CFC.sqrt f x = ((Real.sqrt (f x).re : ℝ) : ℂ) := by
  have hptwise : ∀ z : X, 0 ≤ (f z).re ∧ (f z).im = 0 := by
    intro z
    have h := ContinuousMap.le_def.mp hf z
    rw [Complex.le_def] at h
    exact ⟨by simpa using h.1, by simp [← h.2]⟩
  set s : C(X, ℂ) := ⟨fun z => ((Real.sqrt (f z).re : ℝ) : ℂ), by fun_prop⟩ with hs
  have hs0 : 0 ≤ s := by
    rw [ContinuousMap.le_def]
    intro z
    rw [Complex.le_def]
    exact ⟨by simp [hs], by simp [hs]⟩
  have hs2 : s ^ 2 = f := by
    ext z
    have h := hptwise z
    have hre : ((((f z).re : ℝ)) : ℂ) = f z := by
      apply Complex.ext <;> simp [h.2]
    calc (s ^ 2) z = (s z) * (s z) := by rw [sq]; rfl
      _ = (((Real.sqrt (f z).re * Real.sqrt (f z).re : ℝ)) : ℂ) := by
            simp [hs, Complex.ofReal_mul]
      _ = f z := by rw [Real.mul_self_sqrt h.1, hre]
  have heq : CFC.sqrt f = s :=
    (sqrt_existsUnique f hf).unique (sqrt_spec f hf) ⟨hs0, hs2, mul_comm _ _⟩
  rw [heq]
  rfl

/-- `realSub S` is closed when `S` is: it is the preimage of `S` under the
continuous inclusion `C(X, ℝ) → C(X, ℂ)`. -/
private theorem realSub_isClosed {S : StarSubalgebra ℂ C(X, ℂ)}
    (hS : IsClosed (S : Set C(X, ℂ))) :
    IsClosed ((realSub S : Subalgebra ℝ C(X, ℝ)) : Set C(X, ℝ)) := by
  have hcont : Continuous (fun u : C(X, ℝ) => ofRealCM u) := by
    have hfun : (fun u : C(X, ℝ) => ofRealCM u)
        = fun u => (RCLike.ofRealCLM (K := ℂ)).compLeftContinuous ℝ X u := by
      funext u; ext x; rfl
    rw [hfun]
    exact ((RCLike.ofRealCLM (K := ℂ)).compLeftContinuous ℝ X).continuous
  have hset : ((realSub S : Subalgebra ℝ C(X, ℝ)) : Set C(X, ℝ))
      = (fun u : C(X, ℝ) => ofRealCM u) ⁻¹' (S : Set C(X, ℂ)) := Set.ext fun _ => Iff.rfl
  rw [hset]
  exact hS.preimage hcont

/-- The lattice step of the printed proof: `|u| = √(u* u)` lies in `realSub S`
whenever `u` does.  This is where `sqrt_mem_of_isClosed` and `sqrt_apply`
meet. -/
private theorem realSub_abs_mem {S : StarSubalgebra ℂ C(X, ℂ)}
    (hS : IsClosed (S : Set C(X, ℂ))) {u : C(X, ℝ)} (hu : u ∈ realSub S) :
    |u| ∈ realSub S := by
  rw [mem_realSub] at hu ⊢
  have hpos : (0 : C(X, ℂ)) ≤ star (ofRealCM u) * ofRealCM u := star_mul_self_nonneg _
  have hstar : star (ofRealCM u) ∈ S := star_mem hu
  have hmem : CFC.sqrt (star (ofRealCM u) * ofRealCM u) ∈ S :=
    sqrt_mem_of_isClosed S hS hpos (S.mul_mem hstar hu)
  have heq : ofRealCM |u| = CFC.sqrt (star (ofRealCM u) * ofRealCM u) := by
    ext x
    rw [sqrt_apply hpos]
    simp [ofRealCM_apply, ContinuousMap.abs_apply, Real.sqrt_mul_self_eq_abs]
  rw [heq]
  exact hmem

/-- **27XXIII** (cstar.tex:4207): for `g > 0`, `ε > 0` and `y ∈ X` there is
`u ∈ 𝒮` with `0 ≤ u ≤ g + ε` and `u(y) = g(y)`.  The print covers `X \ V`,
where `V = {z : g(y) < g(z) + ε}`, by the sets `{z : f_x(z) < ε}` and takes
the infimum over a finite subcover; here the constant `g(y)` is thrown in as
the patch indexed by the points of `V`, so that one infimum over a finite
subcover of `X` does both jobs (on `V` the print's bound `f ≤ g(y)` is exactly
that constant).  N.B. the print writes `U_x := {z : f_x(z) ≤ ε}` and calls it
open, and writes `X \ U` for `X \ V`; both are slips. -/
private theorem sw_dominate (A : Subalgebra ℝ C(X, ℝ))
    (hinf : ∀ u ∈ A, ∀ v ∈ A, u ⊓ v ∈ A) (hsup : ∀ u ∈ A, ∀ v ∈ A, u ⊔ v ∈ A)
    (hsep : ∀ x y : X, x ≠ y → ∃ u ∈ A, u x ≠ u y)
    {g : C(X, ℝ)} (hg : ∀ z, 0 < g z) {ε : ℝ} (hε : 0 < ε) (y : X) :
    ∃ u ∈ A, (∀ z, 0 ≤ u z) ∧ (∀ z, u z ≤ g z + ε) ∧ u y = g y := by
  have hne : Nonempty X := ⟨y⟩
  set V : Set X := {z | g y < g z + ε} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const (g.continuous.add continuous_const)
  have hyV : y ∈ V := by show g y < g y + ε; linarith
  have key : ∀ x : X, ∃ w ∈ A, (∀ z, 0 ≤ w z) ∧ w y = g y ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, w z ≤ g z + ε := by
    intro x
    by_cases hxV : x ∈ V
    · exact ⟨ContinuousMap.const X (g y), const_mem A _, fun _ => (hg y).le, rfl,
        V, hVopen, hxV, fun _ hz => le_of_lt hz⟩
    · have hxy : x ≠ y := fun h => hxV (h ▸ hyV)
      obtain ⟨u, huA, hu0, hule, hux, huy⟩ :=
        sw_two_point A hinf hsup hsep hxy (hg y).le
      refine ⟨u, huA, hu0, huy, {z | u z < ε},
        isOpen_lt u.continuous continuous_const, ?_, fun z hz => ?_⟩
      · show u x < ε
        rw [hux]; exact hε
      · have hz' : u z < ε := hz
        have := hg z
        linarith
  choose w hwA hw0 hwy U hUopen hxU hUle using key
  obtain ⟨ts, hts⟩ := CompactSpace.elim_nhds_subcover U (fun x => (hUopen x).mem_nhds (hxU x))
  have htsne : ts.Nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ hne hts
  refine ⟨ts.inf' htsne w, Finset.inf'_mem (A : Set C(X, ℝ)) hinf ts htsne w
    (fun i _ => hwA i), fun z => ?_, fun z => ?_, ?_⟩
  · rw [ContinuousMap.inf'_apply]
    exact Finset.le_inf' htsne (fun i => w i z) (fun i _ => hw0 i z)
  · obtain ⟨x, hx, hzx⟩ := Set.exists_set_mem_of_union_eq_top _ _ hts z
    rw [ContinuousMap.inf'_apply]
    exact le_trans (Finset.inf'_le (fun i => w i z) hx) (hUle x z hzx)
  · rw [ContinuousMap.inf'_apply]
    refine le_antisymm ?_ (Finset.le_inf' htsne (fun i => w i y) (fun i _ => (hwy i).ge))
    obtain ⟨i, hi⟩ := htsne
    exact le_of_le_of_eq (Finset.inf'_le (fun i => w i y) hi) (hwy i)

/-- **27XXIV** (cstar.tex:4235): the supremum over a finite subcover of the
`27XXIII` functions is within `ε` of `g`.  N.B. the print takes `U_y` to be a
neighbourhood of `y` on which `g(y) - ε ≤ f_y`, which gives `f ≥ g(y) - ε` and
not the `f ≥ g(z) - ε` wanted; `U_y := {z : g(z) - ε < f_y(z)}`, open because
`g` and `f_y` are continuous and a neighbourhood of `y` because `f_y(y) =
g(y)`, is what the argument needs. -/
private theorem sw_approx (A : Subalgebra ℝ C(X, ℝ))
    (hinf : ∀ u ∈ A, ∀ v ∈ A, u ⊓ v ∈ A) (hsup : ∀ u ∈ A, ∀ v ∈ A, u ⊔ v ∈ A)
    (hsep : ∀ x y : X, x ≠ y → ∃ u ∈ A, u x ≠ u y) [Nonempty X]
    {g : C(X, ℝ)} (hg : ∀ z, 0 < g z) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ A, ∀ z, |u z - g z| ≤ ε := by
  have key : ∀ y : X, ∃ w ∈ A, (∀ z, w z ≤ g z + ε) ∧
      ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, g z - ε < w z := by
    intro y
    obtain ⟨w, hwA, _, hwle, hwy⟩ := sw_dominate A hinf hsup hsep hg hε y
    refine ⟨w, hwA, hwle, {z | g z - ε < w z},
      isOpen_lt (g.continuous.sub continuous_const) w.continuous, ?_, fun _ hz => hz⟩
    show g y - ε < w y
    rw [hwy]; linarith
  choose w hwA hwle U hUopen hyU hUlt using key
  obtain ⟨ys, hys⟩ := CompactSpace.elim_nhds_subcover U (fun y => (hUopen y).mem_nhds (hyU y))
  have hysne : ys.Nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ ‹Nonempty X› hys
  refine ⟨ys.sup' hysne w, Finset.sup'_mem (A : Set C(X, ℝ)) hsup ys hysne w
    (fun i _ => hwA i), fun z => ?_⟩
  rw [abs_le]
  constructor
  · obtain ⟨y, hy, hzy⟩ := Set.exists_set_mem_of_union_eq_top _ _ hys z
    have h1 : g z - ε < w y z := hUlt y z hzy
    have h2 : w y z ≤ (ys.sup' hysne w) z := by
      rw [ContinuousMap.sup'_apply]; exact Finset.le_sup' (fun i => w i z) hy
    linarith
  · have h3 : (ys.sup' hysne w) z ≤ g z + ε := by
      rw [ContinuousMap.sup'_apply]
      exact Finset.sup'_le hysne (fun i => w i z) (fun i _ => hwle i z)
    linarith

/-- **27XXI** (cstar.tex:4180), the reduction, in `C(X, ℝ)`: a *closed*
subalgebra that is a sublattice and separates points is everything.  It is
enough to get within `ε` of each strictly positive `g`, because the subalgebra
is closed; and every `u` is a difference of two strictly positive functions,
which is the print's "it suffices to show `g ∈ 𝒮` for positive `g`" together
with its "we may assume `g(x) > 0`, replacing `g` by `1 + g`". -/
private theorem sw_real (A : Subalgebra ℝ C(X, ℝ)) (hcl : IsClosed (A : Set C(X, ℝ)))
    (hinf : ∀ u ∈ A, ∀ v ∈ A, u ⊓ v ∈ A) (hsup : ∀ u ∈ A, ∀ v ∈ A, u ⊔ v ∈ A)
    (hsep : ∀ x y : X, x ≠ y → ∃ u ∈ A, u x ≠ u y) : A = ⊤ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine Algebra.eq_top_iff.mpr fun u => ?_
    have hu : u = 0 := by ext x; exact (hX.false x).elim
    rw [hu]; exact zero_mem A
  · have hpos : ∀ g : C(X, ℝ), (∀ z, 0 < g z) → g ∈ A := by
      intro g hg
      rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨u, huA, hu⟩ := sw_approx A hinf hsup hsep hg (half_pos hε)
      refine ⟨u, huA, ?_⟩
      have hd : dist g u ≤ ε / 2 := by
        rw [ContinuousMap.dist_le (by positivity)]
        intro z
        rw [Real.dist_eq, abs_sub_comm]
        exact hu z
      linarith
    refine Algebra.eq_top_iff.mpr fun u => ?_
    have hp : ∀ z, 0 < ((u ⊔ 0) + 1 : C(X, ℝ)) z := by
      intro z
      simp only [ContinuousMap.add_apply, ContinuousMap.sup_apply, ContinuousMap.zero_apply,
        ContinuousMap.one_apply]
      have := le_max_right (u z) 0
      linarith
    have hq : ∀ z, 0 < (((-u) ⊔ 0) + 1 : C(X, ℝ)) z := by
      intro z
      simp only [ContinuousMap.add_apply, ContinuousMap.sup_apply, ContinuousMap.zero_apply,
        ContinuousMap.neg_apply, ContinuousMap.one_apply]
      have := le_max_right (-(u z)) 0
      linarith
    have hdecomp : u = ((u ⊔ 0) + 1) - (((-u) ⊔ 0) + 1) := by
      ext z
      simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.sup_apply,
        ContinuousMap.zero_apply, ContinuousMap.neg_apply, ContinuousMap.one_apply]
      rcases le_total 0 (u z) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -(u z) ≤ (0:ℝ))]; ring
      · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -(u z))]; ring
    rw [hdecomp]
    exact A.sub_mem (hpos _ hp) (hpos _ hq)

end StoneWeierstrassAux

/-- **27XX** (`stone-weierstrass`, cstar.tex:4170, Theorem
(Stone–Weierstraß)): a C*-subalgebra `𝒮` of `C(X)`, `X` compact Hausdorff,
which separates the points of `X` is all of `C(X)`.

*Class 1 — faithful.*  The printed proof **27XXI**–**27XXIV**, transcribed in
the section above: `𝒮` is closed under `|·|` because `|f| = √(f* f)` and the
square root of **23VII** stays inside a closed ⋆-subalgebra
(`sqrt_mem_of_isClosed`), hence under `⊔` and `⊓` on its real-valued part
(`realSub`); then **27XXII**'s two-point interpolation, **27XXIII**'s finite
infimum over a cover of the complement of `V`, and **27XXIV**'s finite
supremum over a cover of `X`.

Mathlib's `starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` is
deliberately not used: its lattice step approximates `t ↦ |t|` by Bernstein
polynomials, where the thesis uses the square root of parsec 230. -/
theorem stone_weierstrass {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (S : StarSubalgebra ℂ C(X, ℂ)) (hS : IsClosed (S : Set C(X, ℂ)))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ S, f x ≠ f y) :
    S = ⊤ := by
  have hmem : ∀ u : C(X, ℝ), u ∈ realSub S ↔ ofRealCM u ∈ S := fun _ => Iff.rfl
  have hAcl : IsClosed ((realSub S : Subalgebra ℝ C(X, ℝ)) : Set C(X, ℝ)) := realSub_isClosed hS
  have hAabs : ∀ u ∈ realSub S, |u| ∈ realSub S := fun _ hu => realSub_abs_mem hS hu
  have hAinf : ∀ u ∈ realSub S, ∀ v ∈ realSub S, u ⊓ v ∈ realSub S := by
    intro u hu v hv
    rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
    exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.add_mem _ hu hv)
      (hAabs _ (Subalgebra.sub_mem _ hv hu))) _
  have hAsup : ∀ u ∈ realSub S, ∀ v ∈ realSub S, u ⊔ v ∈ realSub S := by
    intro u hu v hv
    rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
    exact Subalgebra.smul_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ hu hv)
      (hAabs _ (Subalgebra.sub_mem _ hv hu))) _
  have hre : ∀ f : C(X, ℂ), f ∈ S → (⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
      : C(X, ℝ)) ∈ realSub S := by
    intro f hf
    rw [hmem]
    have heq : ofRealCM (⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩ : C(X, ℝ))
        = (2 : ℂ)⁻¹ • (f + star f) := by
      ext z
      rw [ofRealCM_apply]
      simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.star_apply,
        smul_eq_mul, ContinuousMap.coe_mk]
      rw [Complex.star_def, Complex.add_conj]
      field_simp
      push_cast
      ring
    rw [heq]
    have hstarf : star f ∈ S := star_mem hf
    exact S.smul_mem (S.add_mem hf hstarf) _
  have him : ∀ f : C(X, ℂ), f ∈ S → (⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩
      : C(X, ℝ)) ∈ realSub S := by
    intro f hf
    rw [hmem]
    have heq : ofRealCM (⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩ : C(X, ℝ))
        = ((2 : ℂ) * Complex.I)⁻¹ • (f - star f) := by
      ext z
      rw [ofRealCM_apply]
      simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.star_apply,
        smul_eq_mul, ContinuousMap.coe_mk]
      rw [Complex.star_def, Complex.sub_conj]
      field_simp
      push_cast
      ring
    rw [heq]
    have hstarf : star f ∈ S := star_mem hf
    exact S.smul_mem (S.sub_mem hf hstarf) _
  have hAsep : ∀ x y : X, x ≠ y → ∃ u ∈ realSub S, u x ≠ u y := by
    intro x y hxy
    obtain ⟨f, hfS, hfne⟩ := hsep x y hxy
    by_cases hr : (f x).re = (f y).re
    · exact ⟨⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩, him f hfS,
        fun h => hfne (Complex.ext hr h)⟩
    · exact ⟨⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩, hre f hfS, hr⟩
  have hAtop : realSub S = ⊤ := sw_real _ hAcl hAinf hAsup hAsep
  have hall : ∀ u : C(X, ℝ), ofRealCM u ∈ S := by
    intro u
    have hu : u ∈ realSub S := by rw [hAtop]; exact Algebra.mem_top
    exact (hmem u).mp hu
  refine StarSubalgebra.eq_top_iff.mpr fun f => ?_
  have h1 := hall (⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩ : C(X, ℝ))
  have h2 := hall (⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩ : C(X, ℝ))
  have hf : f = ofRealCM (⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
      : C(X, ℝ)) + Complex.I •
      ofRealCM (⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩ : C(X, ℝ)) := by
    ext z
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [ofRealCM_apply, ofRealCM_apply]
    simp only [ContinuousMap.coe_mk]
    rw [mul_comm]
    exact (Complex.re_add_im (f z)).symm
  rw [hf]
  exact S.add_mem h1 (S.smul_mem h2 _)

/-- **27XXV** (`spectrum-calg-compact-hausdorff`, cstar.tex:4253, Lemma): the
spectrum `spec(𝒜)` of a commutative C*-algebra is a compact Hausdorff space.

*Class 1 — faithful.*  The printed proof **27XXVI** (cstar.tex:4256),
transcribed.  Each `f ∈ spec(𝒜)` satisfies `|f(a)| ≤ ‖a‖` by **20V**
`norm_mi_map_contractive`, so `spec(𝒜)` sits inside the product
`∏_{a ∈ 𝒜} {z : |z| ≤ ‖a‖}`, which is compact by Tychonoff
(`isCompact_univ_pi`) and Hausdorff; the topology of pointwise convergence on
`spec(𝒜)` is exactly the one induced by that inclusion
(`WeakBilin.isEmbedding`), so it remains to see that `spec(𝒜)` is *closed* in
the product — that a pointwise limit of miu-maps is an miu-map.  That is the
printed computation `f(ab) = lim f_i(ab) = lim f_i(a)f_i(b) = f(a)f(b)` and
its analogues: each of additivity, homogeneity, multiplicativity, unitality
and the norm bound is a closed condition, being an equality (or an
inequality) between two continuous functions of the point of the product.
Hausdorffness is the printed "subspace of the Hausdorff product". -/
theorem spectrum_calg_compact_hausdorff :
    CompactSpace (characterSpace ℂ 𝒜) ∧ T2Space (characterSpace ℂ 𝒜) := by
  let _ : PartialOrder 𝒜 := CStarAlgebra.spectralOrder 𝒜
  have _ : StarOrderedRing 𝒜 := CStarAlgebra.spectralOrderedRing 𝒜
  -- the topology of pointwise convergence is induced from the product `𝒜 → ℂ`
  have hemb : Topology.IsEmbedding
      (fun φ : characterSpace ℂ 𝒜 => fun a : 𝒜 => (φ : WeakDual ℂ 𝒜) a) :=
    (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).comp
      (Topology.IsEmbedding.subtypeVal (p := fun x : WeakDual ℂ 𝒜 => x ∈ characterSpace ℂ 𝒜))
  -- `spec(𝒜)` is, inside that product, the set of contractive miu-maps
  have hrange : (Set.range fun φ : characterSpace ℂ 𝒜 => fun a : 𝒜 => (φ : WeakDual ℂ 𝒜) a)
      = {g : 𝒜 → ℂ | ∀ x y : 𝒜, g (x + y) = g x + g y} ∩
        ({g : 𝒜 → ℂ | ∀ (c : ℂ) (x : 𝒜), g (c • x) = c * g x} ∩
          ({g : 𝒜 → ℂ | ∀ x y : 𝒜, g (x * y) = g x * g y} ∩
            ({g : 𝒜 → ℂ | g 1 = 1} ∩ {g : 𝒜 → ℂ | ∀ x : 𝒜, ‖g x‖ ≤ ‖x‖}))) := by
    ext g
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨fun x y => map_add φ x y, fun c x => ?_, fun x y => map_mul φ x y,
        map_one φ, fun x => ?_⟩
      · show (φ : WeakDual ℂ 𝒜) (c • x) = c * (φ : WeakDual ℂ 𝒜) x
        rw [map_smul, smul_eq_mul]
      · exact norm_mi_map_contractive
          ({ WeakDual.CharacterSpace.equivAlgHom φ with map_star' := fun y => map_star φ y } :
            𝒜 →⋆ₐ[ℂ] ℂ) x
    · rintro ⟨hadd, hsmul, hmul, hone, hbnd⟩
      refine ⟨⟨StrongDual.toWeakDual (LinearMap.mkContinuous
        { toFun := g, map_add' := hadd,
          map_smul' := fun c x => by simpa using hsmul c x } 1
        (fun x => by simpa using hbnd x)), ?_, hmul⟩, rfl⟩
      intro h
      have h1 : g 1 = 0 := congrArg (fun ψ : WeakDual ℂ 𝒜 => ψ 1) h
      rw [hone] at h1
      exact one_ne_zero h1
  -- each of those five conditions is closed in the product
  have hclosed : IsClosed
      (Set.range fun φ : characterSpace ℂ 𝒜 => fun a : 𝒜 => (φ : WeakDual ℂ 𝒜) a) := by
    rw [hrange]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
    · simpa only [Set.ofPred_forall] using
        isClosed_iInter fun x : 𝒜 => isClosed_iInter fun y : 𝒜 =>
          isClosed_eq (continuous_apply (x + y))
            (show Continuous fun g : 𝒜 → ℂ => g x + g y from
              (continuous_apply x).add (continuous_apply y))
    · simpa only [Set.ofPred_forall] using
        isClosed_iInter fun c : ℂ => isClosed_iInter fun x : 𝒜 =>
          isClosed_eq (continuous_apply (c • x))
            (show Continuous fun g : 𝒜 → ℂ => c * g x from
              continuous_const.mul (continuous_apply x))
    · simpa only [Set.ofPred_forall] using
        isClosed_iInter fun x : 𝒜 => isClosed_iInter fun y : 𝒜 =>
          isClosed_eq (continuous_apply (x * y))
            (show Continuous fun g : 𝒜 → ℂ => g x * g y from
              (continuous_apply x).mul (continuous_apply y))
    · exact isClosed_eq (continuous_apply 1) continuous_const
    · simpa only [Set.ofPred_forall] using
        isClosed_iInter fun x : 𝒜 =>
          isClosed_le (show Continuous fun g : 𝒜 → ℂ => ‖g x‖ from (continuous_apply x).norm)
            continuous_const
  -- Tychonoff: the product of the closed balls is compact
  have hpi : IsCompact (Set.univ.pi fun a : 𝒜 => Metric.closedBall (0 : ℂ) ‖a‖) :=
    isCompact_univ_pi fun a => isCompact_closedBall 0 ‖a‖
  have hsub : (Set.range fun φ : characterSpace ℂ 𝒜 => fun a : 𝒜 => (φ : WeakDual ℂ 𝒜) a)
      ⊆ Set.univ.pi fun a : 𝒜 => Metric.closedBall (0 : ℂ) ‖a‖ := by
    rw [hrange]
    rintro g ⟨-, -, -, -, hbnd⟩ a -
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbnd a
  refine ⟨?_, hemb.t2Space⟩
  have huniv : IsCompact (Set.univ : Set (characterSpace ℂ 𝒜)) := by
    rw [hemb.isCompact_iff, Set.image_univ]
    exact hpi.of_isClosed_subset hclosed hsub
  exact isCompact_univ_iff.mp huniv

/-- **27XXVII** (`gelfand`, cstar.tex:4288, Gelfand's Representation
Theorem): for a commutative C*-algebra `𝒜` the Gelfand representation
`γ : 𝒜 → C(spec 𝒜)` is an miu-isomorphism — it is bijective (and
star-preserving by `gelfand_representation_basic_2`, so a ⋆-isomorphism:
`gelfandStarTransform`).

*Class 1 — faithful.*  The assembly of **27XXVIII** (cstar.tex:4317):
injectivity is **27XVIII**.2, and for surjectivity the range of `γ` is a
closed ⋆-subalgebra of `C(spec 𝒜)` by **27XVIII**.2's second clause which
separates the points of `spec 𝒜` — two characters agreeing on every `γ(a)`
agree on every `a` — so **27XX** `stone_weierstrass` makes it everything.

Mathlib's `gelfandTransform_bijective` is deliberately not used: it supplies
its own isometry by the maximal-ring-ideal route instead of **27XVIII**. -/
theorem gelfand : Function.Bijective (gelfandTransform ℂ 𝒜) := by
  refine ⟨gelfand_representation_injective, ?_⟩
  obtain ⟨S, hScarrier, hSclosed, -⟩ := gelfand_representation_range (𝒜 := 𝒜)
  have hmem : ∀ a : 𝒜, gelfandTransform ℂ 𝒜 a ∈ S := fun a => by
    rw [← SetLike.mem_coe, hScarrier]; exact ⟨a, rfl⟩
  have hsep : ∀ φ ψ : characterSpace ℂ 𝒜, φ ≠ ψ → ∃ f ∈ S, f φ ≠ f ψ := by
    intro φ ψ hne
    by_contra hcon
    refine hne (Subtype.ext (ContinuousLinearMap.ext fun a => ?_))
    by_contra hne2
    exact hcon ⟨gelfandTransform ℂ 𝒜 a, hmem a, hne2⟩
  have htop : S = ⊤ := stone_weierstrass S hSclosed hsep
  intro g
  have hg : g ∈ (S : Set C(characterSpace ℂ 𝒜, ℂ)) := by
    rw [SetLike.mem_coe, htop]
    exact StarSubalgebra.mem_top
  rwa [hScarrier] at hg

/-- **27XVII** `spectrum_miu` in the form the solution to **28II** uses it
(asols.tex, `parsec-280.20`, points 5 and 6 cite `parsec-270.170` for
elements that need not be self-adjoint): in a *commutative* C*-algebra
`spec(b) = { φ(b) : φ ∈ spec(𝒮) }` for every `b`.  This is the printed
statement of **27XVII** with the self-adjointness dropped, which Gelfand's
representation theorem **27XXVII** — available at parsec 280 — supplies:
`γ` is an isomorphism, so `spec(b) = spec(γ(b))`, and the spectrum of a
continuous function on a compact space is its range. -/
private theorem spectrum_eq_range_char {𝒮 : Type*} [CommCStarAlgebra 𝒮] (b : 𝒮) :
    spectrum ℂ b = Set.range fun φ : characterSpace ℂ 𝒮 => φ b := by
  have h := AlgEquiv.spectrum_eq (AlgEquiv.ofBijective (gelfandTransform ℂ 𝒮) gelfand) b
  rw [← h, ContinuousMap.spectrum_eq_range]
  rfl

end GelfandRepresentation

/-! ## Parsec 280: the continuous functional calculus -/

section FunctionalCalculus

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 1: there
is a least C*-subalgebra `C*(a)` of `𝒜` containing `a` — Mathlib's
`StarAlgebra.elemental ℂ a`. -/
theorem functional_calculus_1 (a : 𝒜) :
    IsLeast {S : StarSubalgebra ℂ 𝒜 | a ∈ S ∧ IsClosed (S : Set 𝒜)}
      (StarAlgebra.elemental ℂ a) :=
  ⟨⟨StarAlgebra.elemental.self_mem ℂ a, StarAlgebra.elemental.isClosed ℂ a⟩,
    fun _ hS => StarAlgebra.elemental.le_of_mem hS.2 hS.1⟩

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 1b:
every `b ∈ C*(a)` commutes with every `c` that commutes with `a` (and with
`a*`). -/
theorem functional_calculus_1b (a b : 𝒜) (hb : b ∈ StarAlgebra.elemental ℂ a)
    (c : 𝒜) (hc : a * c = c * a) (hc' : star a * c = c * star a) :
    b * c = c * b := by
  have hcmem : c ∈ (StarSubalgebra.centralizer ℂ ({a} : Set 𝒜) : Set 𝒜) :=
    (StarSubalgebra.mem_centralizer_iff ℂ).mpr (by rintro g rfl; exact ⟨hc, hc'⟩)
  have hbmem := StarAlgebra.elemental.le_centralizer_centralizer (R := ℂ) a hb
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hbmem) c hcmem).1.symm

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 2: `a`
is *normal* (`C*(a)` commutative, Mathlib: `IsStarNormal a`) iff
`a a* = a* a` iff `Re(a) Im(a) = Im(a) Re(a)`. -/
theorem functional_calculus_2 (a : 𝒜) :
    ((∀ x y : StarAlgebra.elemental ℂ a, x * y = y * x) ↔
      a * star a = star a * a) ∧
    (a * star a = star a * a ↔
      (ℜ a : 𝒜) * (ℑ a : 𝒜) = (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
  have ha : a = (ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜) :=
    (realPart_add_I_smul_imaginaryPart a).symm
  have has : star a = (ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜) := by
    conv_lhs => rw [ha]
    rw [star_add, star_smul, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
    simp [sub_eq_add_neg]
  have h7 := (cstar_involution_basic_7 a).2
  have h7' : a * star a = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 -
      Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
    calc a * star a
        = ((ℜ a : 𝒜) + Complex.I • (ℑ a : 𝒜)) * ((ℜ a : 𝒜) - Complex.I • (ℑ a : 𝒜)) := by
          rw [← has, ← ha]
      _ = (ℜ a : 𝒜) ^ 2 + (ℑ a : 𝒜) ^ 2 -
            Complex.I • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
          rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
            mul_smul_comm, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_sub, sq, sq]
          abel
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · exact congrArg Subtype.val (h ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
      ⟨star a, StarAlgebra.elemental.star_self_mem ℂ a⟩)
  · -- the solution's route, part 1 twice: `a` commutes with itself and with
    -- `a*`, so by **28II**.1b it commutes with every `b ∈ C*(a)`; likewise
    -- `a*`; so every such `b` commutes with every `c ∈ C*(a)`
    have hax : ∀ x : 𝒜, x ∈ StarAlgebra.elemental ℂ a → a * x = x * a := fun x hx =>
      (functional_calculus_1b a x hx a rfl h.symm).symm
    have hsx : ∀ x : 𝒜, x ∈ StarAlgebra.elemental ℂ a → star a * x = x * star a :=
      fun x hx => (functional_calculus_1b a x hx (star a) h rfl).symm
    intro x y
    exact Subtype.ext
      (functional_calculus_1b a (y : 𝒜) y.2 (x : 𝒜) (hax _ x.2) (hsx _ x.2)).symm
  · have hkey : star a * a - a * star a =
        (2 * Complex.I) • ((ℜ a : 𝒜) * (ℑ a : 𝒜) - (ℑ a : 𝒜) * (ℜ a : 𝒜)) := by
      rw [h7, h7']; module
    have hI : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
    constructor
    · intro h
      rw [h, sub_self] at hkey
      exact sub_eq_zero.mp ((smul_eq_zero.mp hkey.symm).resolve_left hI)
    · intro h
      rw [sub_eq_zero.mpr h, smul_zero] at hkey
      exact (sub_eq_zero.mp hkey).symm

/-! **28II**, part 3: for normal `a` the functional calculus
`Φ : C(spec a) → 𝒜`, `f ↦ f(a)`, obtained by composing Gelfand's
representation theorem for `C*(a)` with the restriction along
`j : spec(C*(a)) → spec(a)`, `ρ ↦ ρ(a)` — in Mathlib the continuous
functional calculus `cfc f a` (for `f : ℂ → ℂ` continuous on `spec a`),
and `CFC.rpow a α` for the powers `a^α`, `a ≥ 0`, `α ∈ (0,∞)`.

`Φ` itself is Mathlib's `cfc`, so it is not built here; but the map `j` that
the exercise asks one to produce first *is* stated, as
`functional_calculus_3_j` below. -/

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 3, first
clause: `j : ρ ↦ ρ(a)` maps `spec(C*(a))` into `spec(a)`, and does so
continuously.  (Mathlib: `StarAlgebra.elemental.characterSpaceToSpectrum` and
`StarAlgebra.elemental.continuous_characterSpaceToSpectrum`.)  It is this map
along which `Φ` restricts, and `functional_calculus_4` uses exactly these two
facts. -/
theorem functional_calculus_3_j (a : 𝒜) [IsStarNormal a] :
    (∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a),
        φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ : StarAlgebra.elemental ℂ a)
          ∈ spectrum ℂ a) ∧
      Continuous fun φ : characterSpace ℂ (StarAlgebra.elemental ℂ a) =>
        φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :
          StarAlgebra.elemental ℂ a) :=
  ⟨fun φ => (StarAlgebra.elemental.characterSpaceToSpectrum a φ).2,
    (StarAlgebra.elemental.continuous_characterSpaceToSpectrum a).subtype_val⟩

section Ordered
variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 3
(sample property): `a^α a^β = a^{α+β}` for `a ≥ 0` and `α, β ∈ (0,∞)`.

*Class 3 — mild.*  The solution's own two-line derivation (asols.tex,
`parsec-280.20`, point 3), transcribed: `a^α = Φ((·)^α)` by definition, the
pointwise identity `x^{α+β} = x^α x^β` holds on `[0,∞)` (`NNReal.rpow_add_of_nonneg`,
the exponents being non-negative), and `Φ` is an miu-map, hence multiplicative
(`cfc_mul`) — which is exactly the property the exercise instructs one to use.
The local shortcut: `CFC.rpow` is Mathlib's `ℝ≥0`-valued calculus, whose `Φ`
is identified with the thesis's `ℂ`-valued `Φ` of **28II**.4 only through
Mathlib's spectrum-restriction lemmas, not through **28II**.4 itself. -/
theorem functional_calculus_3 (a : 𝒜) (ha : 0 ≤ a) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    CFC.rpow a α * CFC.rpow a β = CFC.rpow a (α + β) := by
  have hcont : ∀ γ : ℝ, 0 ≤ γ → ∀ S : Set ℝ≥0, ContinuousOn (fun x : ℝ≥0 => x ^ γ) S :=
    fun γ hγ _ _ _ => (NNReal.continuousAt_rpow_const (Or.inr hγ)).continuousWithinAt
  simp only [CFC.rpow_eq_pow, CFC.rpow_def]
  rw [← cfc_mul _ _ a (hcont α hα.le _) (hcont β hβ.le _)]
  exact (cfc_congr fun z _ => NNReal.rpow_add_of_nonneg z hα.le hβ.le).symm

end Ordered

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 4:
`f(a)` is the unique element of `C*(a)` with `φ(f(a)) = f(φ(a))` for all
`φ ∈ spec(C*(a))` — i.e. an element `b` of `C*(a)` satisfies the character
condition exactly when it *is* `f(a) = Φ(f)`, Mathlib's `cfc f a`.  Both of
the exercise's assertions are here: uniqueness (two elements satisfying the
condition are both `f(a)`) and the identification of the element with `f(a)`,
which is the half one computes with.

Proof, following the thesis: part 3's `j : ρ ↦ ρ(a)` maps `spec(C*(a))` into
`spec(a)` continuously, so `f ∘ j ∈ C(spec(C*(a)))`; and `C*(a)` is commutative
(`IsStarNormal a`), so Gelfand's representation theorem **27XXVII** makes
`γ = gelfandStarTransform` a bijection onto `C(spec(C*(a)))`.  The element
sought is exactly `γ⁻¹(f ∘ j)` — and that *is* `f(a)`, because Mathlib builds
`cfc f a` by the very same formula (`cfcHom_eq_of_isStarNormal`, whose
`continuousFunctionalCalculus a` is `γ⁻¹ ∘ (· ∘ j)`).

*Statement change, 2026-09-04, under the `docs/DECISIONS.md` §2.1 ruling,
which thereby closes §2.5 (the former QUESTIONS A10).*  This read
`∃! b : C*(a), ∀ φ, φ b = f (φ a)` — uniqueness together with *bare*
existence.  The name `f(a)` did not occur in it, so it did not characterise
the functional calculus; the exercise's second assertion was missing. -/
theorem functional_calculus_4 (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    ∀ b : StarAlgebra.elemental ℂ a,
      (∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a),
          φ b = f (φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :
            StarAlgebra.elemental ℂ a))) ↔ (b : 𝒜) = cfc f a := by
  -- `j : ρ ↦ ρ(a)` maps `spec(C*(a))` into `spec(a)` and is continuous
  -- (part 3 of the exercise; Mathlib's `characterSpaceToSpectrum`).
  have hmem : ∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a),
      φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ : StarAlgebra.elemental ℂ a) ∈
        spectrum ℂ a :=
    fun φ => (StarAlgebra.elemental.characterSpaceToSpectrum a φ).2
  have hcont : Continuous fun φ : characterSpace ℂ (StarAlgebra.elemental ℂ a) =>
      f (φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :
        StarAlgebra.elemental ℂ a)) :=
    hf.comp_continuous
      (StarAlgebra.elemental.continuous_characterSpaceToSpectrum a).subtype_val hmem
  -- `f ∘ j ∈ C(spec(C*(a)))`; the claim is that its `γ`-preimage is `f(a)`.
  set g : C(characterSpace ℂ (StarAlgebra.elemental ℂ a), ℂ) := ⟨_, hcont⟩ with hg
  have hcfc : ((gelfandStarTransform (StarAlgebra.elemental ℂ a)).symm g : 𝒜)
      = cfc f a := by
    have h1 : continuousFunctionalCalculus a
          ⟨(spectrum ℂ a).domRestrict f, hf.domRestrict⟩
        = (gelfandStarTransform (StarAlgebra.elemental ℂ a)).symm g := by
      show (gelfandStarTransform (StarAlgebra.elemental ℂ a)).symm _ = _
      congr 1
    rw [← h1, cfc_apply f a, cfcHom_eq_of_isStarNormal a]
    rfl
  intro b
  constructor
  · intro h
    have hb : gelfandStarTransform (StarAlgebra.elemental ℂ a) b = g := by
      ext φ; exact h φ
    rw [← hcfc, ← hb, StarAlgEquiv.symm_apply_apply]
  · intro h φ
    have hb : b = (gelfandStarTransform (StarAlgebra.elemental ℂ a)).symm g :=
      Subtype.ext (by rw [h, hcfc])
    rw [hb]
    exact DFunLike.congr_fun
      ((gelfandStarTransform (StarAlgebra.elemental ℂ a)).apply_symm_apply g) φ

/-- Pre-composition of a character with an miu-map, computed pointwise: the
solution to **28II** restricts a character `φ ∈ spec(C*(ϱ(a)))` (point 6) or
`φ ∈ spec(C*(a))` (point 7) along an miu-map and uses that `b ↦ φ(ϱ(b))` is
again a character.  Mathlib bundles that as
`WeakDual.CharacterSpace.compContinuousMap`; this is its defining value. -/
private theorem char_comp_apply {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [StarRing A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    [StarRing B] (ψ : A →⋆ₐ[ℂ] B) (φ : characterSpace ℂ B) (x : A) :
    (WeakDual.CharacterSpace.compContinuousMap ψ φ) x = φ (ψ x) := by
  show ((WeakDual.CharacterSpace.equivAlgHom.symm
      ((WeakDual.CharacterSpace.equivAlgHom φ).comp (ψ : A →ₐ[ℂ] B)) : characterSpace ℂ A) :
      A → ℂ) x = φ (ψ x)
  rw [WeakDual.CharacterSpace.equivAlgHom_symm_coe, AlgHom.comp_apply,
    WeakDual.CharacterSpace.equivAlgHom_coe]
  rfl

/-- `f(a) = Φ(f)` lies in `C*(a)`, as the exercise's `Φ : C(spec a) → C*(a) ⊆ 𝒜`
says it does: `cfc f a` is by construction the image of `f` under
`continuousFunctionalCalculus a : C(spec a, ℂ) ≃⋆ₐ[ℂ] C*(a)`. -/
private theorem cfc_mem_elemental (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) : cfc f a ∈ StarAlgebra.elemental ℂ a := by
  rw [cfc_apply f a, cfcHom_eq_of_isStarNormal a]
  exact SetLike.coe_mem _

/-- **27XVII**, as the solution to **28II** cites it (`parsec-270.170`), for an
element of the commutative C*-algebra `C*(a)`: `spec(b) = { φ(b) : φ ∈
spec(C*(a)) }`, the spectrum taken in `𝒜` — the same set, by spectral
permanence for the closed ⋆-subalgebra `C*(a)`, which the exercise's
identification of `spec(a)` with the spectrum of `a` in `C*(a)` presupposes. -/
private theorem spectrum_eq_range_elemental (a : 𝒜) [IsStarNormal a]
    (b : StarAlgebra.elemental ℂ a) :
    spectrum ℂ (b : 𝒜)
      = Set.range fun φ : characterSpace ℂ (StarAlgebra.elemental ℂ a) => φ b := by
  rw [← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed ℂ a) (a := b)]
  exact spectrum_eq_range_char b

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 5
(Spectral mapping theorem): `spec(f(a)) = f(spec(a))` for normal `a` and
`f ∈ C(spec a)`.

*Class 1 — faithful.*  The solution's own three-line chain (asols.tex,
`parsec-280.20`, point 5), transcribed:
`f(spec a) = { f(φ(a)) : φ ∈ spec(C*(a)) }` by **27XVII**, `= { φ(f(a)) : φ }`
by part 4 (`functional_calculus_4`, which since 2026-09-04 states exactly that
`f(a)` is the element of `C*(a)` with `φ(f(a)) = f(φ(a))`), and `= spec(f(a))`
by **27XVII** again, `f(a)` being an element of `C*(a)`. -/
theorem functional_calculus_5 (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (cfc f a) = f '' spectrum ℂ a := by
  obtain ⟨b, hb⟩ : ∃ b : StarAlgebra.elemental ℂ a, (b : 𝒜) = cfc f a :=
    ⟨⟨cfc f a, cfc_mem_elemental a f hf⟩, rfl⟩
  -- part 4: `φ(f(a)) = f(φ(a))` for every character `φ` of `C*(a)`
  have hchar := (functional_calculus_4 a f hf b).mpr hb
  -- **27XVII** for `a` and for `f(a)`, both elements of `C*(a)`
  have h2 : spectrum ℂ a
      = Set.range fun φ : characterSpace ℂ (StarAlgebra.elemental ℂ a) =>
          φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ : StarAlgebra.elemental ℂ a) :=
    spectrum_eq_range_elemental a ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  rw [← hb, spectrum_eq_range_elemental a b, h2]
  ext z
  simp only [Set.mem_range, Set.mem_image, hchar]
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨_, ⟨φ, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨φ, rfl⟩, rfl⟩
    exact ⟨φ, rfl⟩

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 6:
`spec(ρ(a)) ⊆ spec(a)` and `ρ(f(a)) = f(ρ(a))` for every miu-map
`ρ : 𝒜 → ℬ`.

*Class 1 — faithful.*  Both clauses are the solution's own (asols.tex,
`parsec-280.20`, point 6).  The first is the printed contrapositive: if
`a − λ` were invertible then so would be `ρ(a − λ) = ρ(a) − λ`, which it is
not.  For the second, the solution says it suffices by point 4 to check that
`ρ(f(a))` lies in `C*(ρ(a))` and that `φ(ρ(f(a))) = f(φ(ρ(a)))` for every
`φ ∈ spec(C*(ρ(a)))`.  The first is the printed observation
`ρ(C*(a)) ⊆ C*(ρ(a))` — here: `C*(ρ(a))` pulled back along the (bounded, by
**20V**) map `ρ` is a closed ⋆-subalgebra containing `a`, so it contains
`C*(a)`, which is the printed "`b` is a limit of polynomials in `a, a*`, and
`ρ` is continuous".  The second is the printed "`b ↦ φ(ρ(b))` is an miu-map
`C*(a) → ℂ`", to which point 4 for `a` applies. -/
theorem functional_calculus_6 {ℬ : Type*} [CStarAlgebra ℬ]
    (ρ : 𝒜 →⋆ₐ[ℂ] ℬ) (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (ρ a) ⊆ spectrum ℂ a ∧ ρ (cfc f a) = cfc f (ρ a) := by
  -- first clause: if `λ − a` were invertible, so would be `λ − ρ(a)`
  have hsub : spectrum ℂ (ρ a) ⊆ spectrum ℂ a := by
    intro z hz
    rw [spectrum.mem_iff] at hz ⊢
    intro hu
    refine hz ?_
    have h := hu.map ρ
    rwa [map_sub, AlgHomClass.commutes] at h
  refine ⟨hsub, ?_⟩
  -- `ρ(C*(a)) ⊆ C*(ρ(a))`: the preimage of `C*(ρ(a))` is closed and holds `a`
  have hρcont : Continuous ρ :=
    AddMonoidHomClass.continuous_of_bound ρ 1 fun x => by
      simpa using NonUnitalStarAlgHom.norm_apply_le ρ x
  have hclosed : IsClosed
      (((StarAlgebra.elemental ℂ (ρ a)).comap ρ : StarSubalgebra ℂ 𝒜) : Set 𝒜) := by
    rw [StarSubalgebra.coe_comap]
    exact (StarAlgebra.elemental.isClosed ℂ (ρ a)).preimage hρcont
  have hle : StarAlgebra.elemental ℂ a ≤ (StarAlgebra.elemental ℂ (ρ a)).comap ρ :=
    StarAlgebra.elemental.le_of_mem hclosed (StarAlgebra.elemental.self_mem ℂ (ρ a))
  set ρ' : StarAlgebra.elemental ℂ a →⋆ₐ[ℂ] StarAlgebra.elemental ℂ (ρ a) :=
    StarAlgHom.codRestrict (ρ.comp (StarAlgebra.elemental ℂ a).subtype)
      (StarAlgebra.elemental ℂ (ρ a)) (fun x => hle x.2) with hρ'
  have hρ'coe : ∀ x : StarAlgebra.elemental ℂ a,
      ((ρ' x : StarAlgebra.elemental ℂ (ρ a)) : ℬ) = ρ (x : 𝒜) := fun _ => rfl
  obtain ⟨b, hb⟩ : ∃ b : StarAlgebra.elemental ℂ a, (b : 𝒜) = cfc f a :=
    ⟨⟨cfc f a, cfc_mem_elemental a f hf⟩, rfl⟩
  have hchar := (functional_calculus_4 a f hf b).mpr hb
  have hf' : ContinuousOn f (spectrum ℂ (ρ a)) := hf.mono hsub
  -- point 4 for `ρ(a)`, applied to `ρ(f(a)) ∈ C*(ρ(a))`
  have key := (functional_calculus_4 (ρ a) f hf' (ρ' b)).mp ?_
  · rw [← hb, ← hρ'coe b, key]
  · intro ψ
    have h2 : ρ' (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ : StarAlgebra.elemental ℂ a)
        = (⟨ρ a, StarAlgebra.elemental.self_mem ℂ (ρ a)⟩ :
            StarAlgebra.elemental ℂ (ρ a)) := Subtype.ext rfl
    rw [← char_comp_apply ρ' ψ b, ← h2, ← char_comp_apply ρ' ψ]
    exact hchar _

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 7:
`g(f(a)) = (g ∘ f)(a)` for normal `a`.

*Class 1 — faithful.*  The solution's own argument (asols.tex,
`parsec-280.20`, point 7): by point 4 it suffices that `g(f(a)) ∈ C*(a)` and
`φ(g(f(a))) = g(f(φ(a)))` for every `φ ∈ spec(C*(a))`.  The first is the
printed `C*(f(a)) ⊆ C*(a)`, because `f(a) ∈ C*(a)`.  For the second the
solution restricts `φ` to `C*(f(a)) ⊆ C*(a)` and applies point 4 twice:
`φ(g(f(a))) = g(φ(f(a)))` and `φ(f(a)) = f(φ(a))`. -/
theorem functional_calculus_7 (a : 𝒜) [IsStarNormal a] (f g : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a))
    (hg : ContinuousOn g (f '' spectrum ℂ a)) :
    cfc g (cfc f a) = cfc (g ∘ f) a := by
  have hn : IsStarNormal (cfc f a) := cfc_predicate f a
  have hspec : spectrum ℂ (cfc f a) = f '' spectrum ℂ a := functional_calculus_5 a f hf
  have hg' : ContinuousOn g (spectrum ℂ (cfc f a)) := by rw [hspec]; exact hg
  have hgf : ContinuousOn (g ∘ f) (spectrum ℂ a) := hg.comp hf (Set.mapsTo_image f _)
  have hfa : cfc f a ∈ StarAlgebra.elemental ℂ a := cfc_mem_elemental a f hf
  -- `C*(f(a)) ⊆ C*(a)`, since `f(a) ∈ C*(a)`
  have hle : StarAlgebra.elemental ℂ (cfc f a) ≤ StarAlgebra.elemental ℂ a :=
    StarAlgebra.elemental.le_of_mem (StarAlgebra.elemental.isClosed ℂ a) hfa
  have hga : cfc g (cfc f a) ∈ StarAlgebra.elemental ℂ (cfc f a) :=
    cfc_mem_elemental (cfc f a) g hg'
  have hg4 := (functional_calculus_4 (cfc f a) g hg' ⟨cfc g (cfc f a), hga⟩).mpr rfl
  have hf4 := (functional_calculus_4 a f hf ⟨cfc f a, hfa⟩).mpr rfl
  refine (functional_calculus_4 a (g ∘ f) hgf ⟨cfc g (cfc f a), hle hga⟩).mp fun φ => ?_
  -- `φ` restricted to `C*(f(a))` is a character there
  have hres := hg4 (WeakDual.CharacterSpace.compContinuousMap (StarSubalgebra.inclusion hle) φ)
  rw [char_comp_apply, char_comp_apply] at hres
  have e1 : StarSubalgebra.inclusion hle
      (⟨cfc g (cfc f a), hga⟩ : StarAlgebra.elemental ℂ (cfc f a))
      = (⟨cfc g (cfc f a), hle hga⟩ : StarAlgebra.elemental ℂ a) := Subtype.ext rfl
  have e2 : StarSubalgebra.inclusion hle
      (⟨cfc f a, StarAlgebra.elemental.self_mem ℂ (cfc f a)⟩ :
        StarAlgebra.elemental ℂ (cfc f a))
      = (⟨cfc f a, hfa⟩ : StarAlgebra.elemental ℂ a) := Subtype.ext rfl
  rw [e1, e2] at hres
  rw [hres, hf4 φ]
  rfl

section Ordered2
variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4325, Exercise), part 7b:
`(a^α)^β = a^{αβ}` for `a ≥ 0` and `α, β ∈ (0,∞)`.

*Class 3 — mild.*  The solution calls this "a trivial corollary" of point 7,
"as `x ↦ x^α` gives a continuous map `[0,∞) → [0,∞)`"; that is exactly what is
transcribed here — composition of the calculus (`cfc_comp`, point 7's own
statement) together with the pointwise identity `x^{αβ} = (x^α)^β`.  The local
shortcut is the one of `functional_calculus_3`: `CFC.rpow` is Mathlib's
`ℝ≥0`-valued calculus, so the composition law used is `cfc_comp` there rather
than `functional_calculus_7` above. -/
theorem functional_calculus_7b (a : 𝒜) (ha : 0 ≤ a) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    CFC.rpow (CFC.rpow a α) β = CFC.rpow a (α * β) := by
  have hcont : ∀ γ : ℝ, 0 ≤ γ → ∀ S : Set ℝ≥0, ContinuousOn (fun x : ℝ≥0 => x ^ γ) S :=
    fun γ hγ _ _ _ => (NNReal.continuousAt_rpow_const (Or.inr hγ)).continuousWithinAt
  simp only [CFC.rpow_eq_pow, CFC.rpow_def]
  rw [← cfc_comp _ _ a ha (hcont β hβ.le _) (hcont α hα.le _)]
  exact cfc_congr fun z _ => (NNReal.rpow_mul z α β).symm

/-! ### **28IV** (cstar.tex:4425, Proof): Pedersen's argument for **28III**

Mathlib's `CFC.rpow_le_rpow` is *not* this argument: it reads operator
monotonicity off the integral representation of `a^p` (Carlen, Lemma 2.8).
The printed proof, transcribed here, writes `E` for the set of `α` for which
`(·)^α` is monotone on the positive *invertible* elements: `(a + 1/n)^α →
a^α` in norm (point 41, cstar.tex:4455) reduces the Theorem to invertible
`a`, `b`; `E` is closed (point 50, cstar.tex:4495) because `α ↦ b^α` is norm
continuous; `E` is midpoint-closed (point 60, cstar.tex:4510) by the
spectral-radius computation `‖b^{-γ/2} a^γ b^{-γ/2}‖ =
ρ(b^{-β/2} a^{β/2} · a^{α/2} b^{-α/2}) ≤ 1` for `γ = (α+β)/2`; and `0, 1 ∈ E`,
so midpoints give the dyadic rationals of `[0,1]` and closedness the rest.
Each of the three delicate steps is the printed one: point 41 is the uniform
continuity of `(·)^α` on the compact spectrum read against the sup-norm of the
calculus (`tendsto_rpow_add_inv`), point 50 factors `α ↦ b^α` through
`C(spec b)` (`continuous_rpow_exponent`), and point 60 moves the conjugating
factor across by `ρ(cd) = ρ(dc)`, **19Ia** `prod_spec` (`spectralRadius_mul_comm`
and `norm_le_norm_conjugate`). -/

section Pedersen

variable [Nontrivial 𝒜]

variable (𝒜) in
/-- The set `E` of **28IV** (cstar.tex:4443): the exponents `α` for which
`(·)^α` is monotone on the positive *invertible* elements. -/
private def monoExp : Set ℝ :=
  {α : ℝ | ∀ a b : 𝒜, IsStrictlyPositive a → a ≤ b → a ^ α ≤ b ^ α}

omit [Nontrivial 𝒜] in
/-- **28IV** point 50's ingredient (cstar.tex:4495): `α ↦ b^α` is norm
continuous, "being the composition of the map `α ↦ b^α : [0,1] → C(spec b)`,
which is norm continuous, and the functional calculus `f ↦ f(b) :
C(spec b) → 𝒜`, which being an miu-map is norm continuous as well".  The
second factor is `continuousAt_cfc_fun`, which is that composition (its proof
is `cfcHom_continuous`); the first is the uniform convergence proved here:
`(α, t) ↦ t^α` is continuous on the compact `[α₀-1, α₀+1] × spec b`, every
`t ∈ spec b` being strictly positive, hence uniformly continuous on it. -/
private lemma continuous_rpow_exponent {b : 𝒜} (hb : IsStrictlyPositive b) :
    Continuous fun α : ℝ => b ^ α := by
  have hb0 : (0 : 𝒜) ≤ b := hb.nonneg
  have hcontOn : ∀ α : ℝ, ContinuousOn (fun t : ℝ => t ^ α) (spectrum ℝ b) := fun α =>
    ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (hb.spectrum_pos ht).ne'
  simp only [CFC.rpow_eq_cfc_real hb0]
  refine continuous_iff_continuousAt.2 fun α₀ => ?_
  refine continuousAt_cfc_fun ?_ (.of_forall hcontOn)
  -- `α ↦ (·)^α` is norm continuous into `C(spec b)`: uniform convergence on
  -- `spec b`, from uniform continuity on a compact box around `(α₀, spec b)`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hKc : IsCompact (spectrum ℝ b) :=
    ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) b
  have hS : IsCompact (Set.Icc (α₀ - 1) (α₀ + 1) ×ˢ spectrum ℝ b) := isCompact_Icc.prod hKc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ p.1)
      (Set.Icc (α₀ - 1) (α₀ + 1) ×ˢ spectrum ℝ b) := by
    intro p hp
    have ht : p.2 ≠ 0 := (hb.spectrum_pos hp.2).ne'
    exact (continuousAt_snd.rpow continuousAt_fst (Or.inl ht)).continuousWithinAt
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hcont) ε hε
  filter_upwards [Metric.ball_mem_nhds α₀ (lt_min hδ0 one_pos)] with α hα t ht
  have hα' : |α - α₀| < min δ 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hα; exact hα
  have h1 : ((α₀, t) : ℝ × ℝ) ∈ Set.Icc (α₀ - 1) (α₀ + 1) ×ˢ spectrum ℝ b :=
    ⟨Set.mem_Icc.2 ⟨by linarith, by linarith⟩, ht⟩
  have h2 : ((α, t) : ℝ × ℝ) ∈ Set.Icc (α₀ - 1) (α₀ + 1) ×ˢ spectrum ℝ b := by
    refine ⟨Set.mem_Icc.2 ⟨?_, ?_⟩, ht⟩
    · have := (abs_lt.1 hα').1; have := min_le_right δ (1 : ℝ); linarith
    · have := (abs_lt.1 hα').2; have := min_le_right δ (1 : ℝ); linarith
  have hd : dist ((α₀, t) : ℝ × ℝ) ((α, t) : ℝ × ℝ) < δ := by
    have hpd : dist ((α₀, t) : ℝ × ℝ) ((α, t) : ℝ × ℝ) = dist α₀ α := by
      simp [Prod.dist_eq]
    rw [hpd, Real.dist_eq, abs_sub_comm]
    exact lt_of_lt_of_le hα' (min_le_left _ _)
  exact hδ _ h1 _ h2 hd

omit [Nontrivial 𝒜] in
/-- **28IV** point 50 (cstar.tex:4495): `E` is closed. -/
private lemma isClosed_monoExp : IsClosed (monoExp 𝒜) := by
  have h : monoExp 𝒜 = ⋂ (a : 𝒜) (b : 𝒜) (_ : IsStrictlyPositive a) (_ : a ≤ b),
      {α : ℝ | a ^ α ≤ b ^ α} := by
    ext α; simp [monoExp]
  rw [h]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun ha =>
    isClosed_iInter fun hab => ?_
  exact isClosed_le (continuous_rpow_exponent ha) (continuous_rpow_exponent (ha.of_le hab))

omit [Nontrivial 𝒜] in
/-- `0 ∈ E` (cstar.tex:4449): `a^0 = 1 = b^0` for *invertible* `a`, `b`. -/
private lemma zero_mem_monoExp : (0 : ℝ) ∈ monoExp 𝒜 := by
  intro a b ha hab
  rw [CFC.rpow_zero a ha.nonneg, CFC.rpow_zero b (ha.of_le hab).nonneg]

omit [Nontrivial 𝒜] in
/-- `1 ∈ E`: `a^1 = a ≤ b = b^1`. -/
private lemma one_mem_monoExp : (1 : ℝ) ∈ monoExp 𝒜 := by
  intro a b ha hab
  rwa [CFC.rpow_one a ha.nonneg, CFC.rpow_one b (ha.of_le hab).nonneg]

/-- The reduction of **28IV** point 60 to a norm (cstar.tex:4516): `a^α ≤ b^α`
iff `‖a^{α/2} b^{-α/2}‖ ≤ 1`, the thesis conjugating by `b^{α/2}` (positive
by **25II** `astara-pos-basic-consequences`) and reading `c ≤ 1` as
`‖c‖ ≤ 1`. -/
private lemma rpow_le_rpow_iff_norm_le_one {a b : 𝒜} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) (α : ℝ) :
    a ^ α ≤ b ^ α ↔ ‖a ^ (α / 2) * b ^ (-(α / 2))‖ ≤ 1 := by
  rcases eq_or_ne α 0 with rfl | hα
  · rw [show (0 : ℝ) / 2 = 0 by norm_num, neg_zero, CFC.rpow_zero a ha.nonneg,
      CFC.rpow_zero b hb.nonneg]
    simp
  · rw [le_iff_norm_sqrt_mul_rpow (a ^ α) (b ^ α) CFC.rpow_nonneg
      (IsStrictlyPositive.rpow b α hb), CFC.sqrt_rpow ha.isUnit hα,
      CFC.rpow_rpow b α (-(1 / 2)) hα hb, show α * -(1 / 2 : ℝ) = -(α / 2) by ring]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Nontrivial 𝒜] in
/-- **28IV** point 60's spectral-radius step (cstar.tex:4532): "recall
from `prod-spec` that `spec(cd) \ {0} = spec(dc) \ {0}`, and so
`ρ(cd) = ρ(dc)` for all `c, d`".  The two spectra agree away from `0`, and `0`
contributes nothing to a supremum of norms, so the suprema agree. -/
private lemma spectralRadius_mul_comm (c d : 𝒜) :
    spectralRadius ℂ (c * d) = spectralRadius ℂ (d * c) := by
  have key : ∀ x y : 𝒜, spectralRadius ℂ (x * y) ≤ spectralRadius ℂ (y * x) := by
    intro x y
    refine iSup₂_le fun k hk => ?_
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · have hmem : k ∈ spectrum ℂ (y * x) := by
        have h := prod_spec x y
        have hk' : k ∈ spectrum ℂ (x * y) \ {0} := ⟨hk, by simpa using hk0⟩
        exact (h ▸ hk').1
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (y * x)) => (‖k‖₊ : ℝ≥0∞)) k hmem
  exact le_antisymm (key c d) (key d c)

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Moving a conjugating factor to the other side does not decrease the norm of
a self-adjoint element: `‖c‖ = ρ(c) = ρ(c w v) = ρ(v c w) ≤ ‖v c w‖`, with `ρ`
the spectral radius, `‖c‖ = ρ(c)` for self-adjoint `c` by **19V**
`norm-spectrum`, and `ρ(cd) = ρ(dc)` by **19Ia** `prod_spec`.  This is the
step **28IV** point 60 (cstar.tex:4532) takes with `w v = 1` the pair
`b^{-(α-β)/4} b^{(α-β)/4}`. -/
private lemma norm_le_norm_conjugate {c v w : 𝒜} (hc : IsSelfAdjoint c)
    (hwv : w * v = 1) : ‖c‖ ≤ ‖v * c * w‖ := by
  have h1 : spectralRadius ℂ c = spectralRadius ℂ (v * c * w) := by
    calc spectralRadius ℂ c
        = spectralRadius ℂ ((c * w) * v) := by rw [mul_assoc, hwv, mul_one]
      _ = spectralRadius ℂ (v * (c * w)) := spectralRadius_mul_comm _ _
      _ = spectralRadius ℂ (v * c * w) := by rw [mul_assoc]
  have h2 : (‖c‖₊ : ℝ≥0∞) ≤ (‖v * c * w‖₊ : ℝ≥0∞) := by
    rw [← norm_spectrum c hc, h1]
    exact spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) _
  exact_mod_cast h2

/-- **28IV** point 60 (cstar.tex:4510): `E` is closed under midpoints.  With
`γ = (α+β)/2`, the printed computation `‖a^{γ/2} b^{-γ/2}‖² =
‖b^{-γ/2} a^γ b^{-γ/2}‖ = ρ(b^{-β/2} a^γ b^{-α/2})` — conjugate by
`b^{(α-β)/4}` — and that factors as `≤ 1 · 1`. -/
private lemma monoExp_midpoint {α β : ℝ} (hα : α ∈ monoExp 𝒜) (hβ : β ∈ monoExp 𝒜) :
    (α + β) / 2 ∈ monoExp 𝒜 := by
  intro a b ha hab
  have hb : IsStrictlyPositive b := ha.of_le hab
  have hA : ‖a ^ (α / 2) * b ^ (-(α / 2))‖ ≤ 1 :=
    (rpow_le_rpow_iff_norm_le_one ha hb α).1 (hα a b ha hab)
  have hB : ‖a ^ (β / 2) * b ^ (-(β / 2))‖ ≤ 1 :=
    (rpow_le_rpow_iff_norm_le_one ha hb β).1 (hβ a b ha hab)
  rw [rpow_le_rpow_iff_norm_le_one ha hb]
  have hsq : a ^ ((α + β) / 2 / 2) * a ^ ((α + β) / 2 / 2) = a ^ ((α + β) / 2) := by
    rw [← CFC.rpow_add ha.isUnit]
    congr 1
    ring
  have hkey : star (a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2))) *
      (a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2))) =
      b ^ (-((α + β) / 2 / 2)) * a ^ ((α + β) / 2) * b ^ (-((α + β) / 2 / 2)) := by
    calc star (a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2))) *
          (a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2)))
        = b ^ (-((α + β) / 2 / 2)) * (a ^ ((α + β) / 2 / 2) * a ^ ((α + β) / 2 / 2)) *
            b ^ (-((α + β) / 2 / 2)) := by
          have hsa1 : star (a ^ ((α + β) / 2 / 2)) = a ^ ((α + β) / 2 / 2) :=
            IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
          have hsa2 : star (b ^ (-((α + β) / 2 / 2))) = b ^ (-((α + β) / 2 / 2)) :=
            IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
          simp only [star_mul, hsa1, hsa2, mul_assoc]
      _ = b ^ (-((α + β) / 2 / 2)) * a ^ ((α + β) / 2) * b ^ (-((α + β) / 2 / 2)) := by
          rw [hsq]
  have hcsa : IsSelfAdjoint (b ^ (-((α + β) / 2 / 2)) * a ^ ((α + β) / 2) *
      b ^ (-((α + β) / 2 / 2))) := by
    rw [← hkey]
    exact IsSelfAdjoint.star_mul_self _
  have hwv : b ^ (-((α - β) / 4)) * b ^ ((α - β) / 4) = 1 := CFC.rpow_neg_mul_rpow _ hb
  have e1 : b ^ ((α - β) / 4) * b ^ (-((α + β) / 2 / 2)) = b ^ (-(β / 2)) := by
    rw [← CFC.rpow_add hb.isUnit]; congr 1; ring
  have e2 : b ^ (-((α + β) / 2 / 2)) * b ^ (-((α - β) / 4)) = b ^ (-(α / 2)) := by
    rw [← CFC.rpow_add hb.isUnit]; congr 1; ring
  have e3 : a ^ ((α + β) / 2) = a ^ (β / 2) * a ^ (α / 2) := by
    rw [← CFC.rpow_add ha.isUnit]; congr 1; ring
  have hconj : b ^ ((α - β) / 4) * (b ^ (-((α + β) / 2 / 2)) * a ^ ((α + β) / 2) *
      b ^ (-((α + β) / 2 / 2))) * b ^ (-((α - β) / 4)) =
      (b ^ (-(β / 2)) * a ^ (β / 2)) * (a ^ (α / 2) * b ^ (-(α / 2))) := by
    calc b ^ ((α - β) / 4) * (b ^ (-((α + β) / 2 / 2)) * a ^ ((α + β) / 2) *
          b ^ (-((α + β) / 2 / 2))) * b ^ (-((α - β) / 4))
        = (b ^ ((α - β) / 4) * b ^ (-((α + β) / 2 / 2))) * a ^ ((α + β) / 2) *
            (b ^ (-((α + β) / 2 / 2)) * b ^ (-((α - β) / 4))) := by
          simp only [mul_assoc]
      _ = b ^ (-(β / 2)) * (a ^ (β / 2) * a ^ (α / 2)) * b ^ (-(α / 2)) := by
          rw [e1, e2, e3]
      _ = (b ^ (-(β / 2)) * a ^ (β / 2)) * (a ^ (α / 2) * b ^ (-(α / 2))) := by
          simp only [mul_assoc]
  have hB' : ‖b ^ (-(β / 2)) * a ^ (β / 2)‖ ≤ 1 := by
    have hsa1 : star (a ^ (β / 2)) = a ^ (β / 2) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have hsa2 : star (b ^ (-(β / 2))) = b ^ (-(β / 2)) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    rw [← norm_star, star_mul, hsa1, hsa2]
    exact hB
  have hnorm : ‖a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2))‖ *
      ‖a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2))‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, hkey]
    refine (norm_le_norm_conjugate hcsa hwv).trans ?_
    rw [hconj]
    refine (norm_mul_le _ _).trans ?_
    calc ‖b ^ (-(β / 2)) * a ^ (β / 2)‖ * ‖a ^ (α / 2) * b ^ (-(α / 2))‖
        ≤ 1 * 1 := mul_le_mul hB' hA (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  nlinarith [norm_nonneg (a ^ ((α + β) / 2 / 2) * b ^ (-((α + β) / 2 / 2)))]

/-- Every dyadic rational of `[0,1]` lies in `E`, by induction. -/
private lemma dyadic_mem_monoExp (n : ℕ) : ∀ k : ℕ, k ≤ 2 ^ n →
    ((k : ℝ) / 2 ^ n) ∈ monoExp 𝒜 := by
  induction n with
  | zero =>
      intro k hk
      simp only [pow_zero] at hk
      interval_cases k
      · simpa using zero_mem_monoExp (𝒜 := 𝒜)
      · simpa using one_mem_monoExp (𝒜 := 𝒜)
  | succ n ih =>
      intro k hk
      have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · subst hm
        have e : ((m + m : ℕ) : ℝ) / 2 ^ (n + 1) = (m : ℝ) / 2 ^ n := by
          push_cast [pow_succ]
          ring
        rw [e]
        exact ih m (by omega)
      · subst hm
        have e : ((2 * m + 1 : ℕ) : ℝ) / 2 ^ (n + 1) =
            ((m : ℝ) / 2 ^ n + ((m + 1 : ℕ) : ℝ) / 2 ^ n) / 2 := by
          push_cast [pow_succ]
          ring
        rw [e]
        exact monoExp_midpoint (ih m (by omega)) (ih (m + 1) (by omega))

/-- `E ⊇ [0,1]` (cstar.tex:4447): the dyadics are dense and `E` is closed. -/
private lemma Icc_subset_monoExp : Set.Icc (0 : ℝ) 1 ⊆ monoExp 𝒜 := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hpow : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have hle1 : ∀ n : ℕ, x - ((2 : ℝ) ^ n)⁻¹ ≤ (⌊x * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by
    intro n
    have hinv : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (hpow n).ne'
    have hexp : (x - ((2 : ℝ) ^ n)⁻¹) * 2 ^ n = x * 2 ^ n - 1 := by
      rw [sub_mul, hinv]
    rw [le_div_iff₀ (hpow n), hexp]
    linarith [Nat.lt_floor_add_one (x * (2 : ℝ) ^ n)]
  have hle2 : ∀ n : ℕ, ((⌊x * 2 ^ n⌋₊ : ℝ) / 2 ^ n) ≤ x := by
    intro n
    rw [div_le_iff₀ (hpow n)]
    exact Nat.floor_le (by positivity)
  refine (isClosed_monoExp (𝒜 := 𝒜)).mem_of_tendsto
    (b := atTop) (f := fun n : ℕ => (⌊x * 2 ^ n⌋₊ : ℝ) / 2 ^ n) ?_ ?_
  · have hinv : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simpa [inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hlow : Tendsto (fun n : ℕ => x - ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.sub hinv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hle1 hle2
  · filter_upwards with n
    refine dyadic_mem_monoExp n _ ?_
    have hcast : x * (2 : ℝ) ^ n ≤ ((2 ^ n : ℕ) : ℝ) := by
      push_cast
      nlinarith [hpow n]
    calc ⌊x * (2 : ℝ) ^ n⌋₊ ≤ ⌊((2 ^ n : ℕ) : ℝ)⌋₊ := Nat.floor_mono hcast
      _ = 2 ^ n := Nat.floor_natCast _

/-- **28IV** point 41 (`fc-uniformly-continuous`, cstar.tex:4455):
`(c + 1/n)^α → c^α` in norm, the convergence that reduces **28III** to
invertible elements.  The thesis proves it for an arbitrary uniformly
continuous `f` by taking the norm through the Gelfand representation of a
commutative subalgebra containing both elements: `‖f(x) - f(y)‖ =
sup_φ |f(φ(x)) - f(φ(y))| ≤ ε` once `|φ(x) - φ(y)| ≤ ‖x - y‖ ≤ δ`.  Here
`c + 1/n = (· + 1/n)(c)` is a function of `c` itself, so that supremum is over
`spec c` and the two functions are `t ↦ (t + 1/n)^α` and `t ↦ t^α`, uniformly
close on the compact `[0, ‖c‖ + 1]` because `(·)^α` is uniformly continuous
there; `tendsto_cfc_fun` is the sup-norm estimate that turns that into norm
convergence. -/
private lemma tendsto_rpow_add_inv {c : 𝒜} (hc : 0 ≤ c) {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun n : ℕ => (c + algebraMap ℝ 𝒜 ((n : ℝ) + 1)⁻¹) ^ α) atTop (𝓝 (c ^ α)) := by
  have hsa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc
  have hcont : Continuous fun t : ℝ => t ^ α :=
    continuous_iff_continuousAt.2 fun t => Real.continuousAt_rpow_const t α (Or.inr hα)
  -- `(c + λ)^α` is a function of `c`: the thesis's commutative subalgebra.
  have hstep : ∀ lam : ℝ, 0 ≤ lam →
      (c + algebraMap ℝ 𝒜 lam) ^ α = cfc (fun t : ℝ => (t + lam) ^ α) c := by
    intro lam hlam
    have hnn : (0 : 𝒜) ≤ c + algebraMap ℝ 𝒜 lam := add_nonneg hc (algebraMap_nonneg 𝒜 hlam)
    have hadd : c + algebraMap ℝ 𝒜 lam = cfc (fun t : ℝ => t + lam) c := by
      rw [cfc_add c (fun t : ℝ => t) (fun _ : ℝ => lam) (by fun_prop) (by fun_prop),
        cfc_id' ℝ c, cfc_const lam c]
    calc (c + algebraMap ℝ 𝒜 lam) ^ α
        = cfc (fun t : ℝ => t ^ α) (cfc (fun t : ℝ => t + lam) c) := by
          rw [CFC.rpow_eq_cfc_real hnn, hadd]
      _ = cfc ((fun t : ℝ => t ^ α) ∘ (fun t : ℝ => t + lam)) c :=
          (cfc_comp _ _ c hsa hcont.continuousOn (by fun_prop)).symm
      _ = cfc (fun t : ℝ => (t + lam) ^ α) c := rfl
  have hfun : ∀ n : ℕ, (c + algebraMap ℝ 𝒜 ((n : ℝ) + 1)⁻¹) ^ α =
      cfc (fun t : ℝ => (t + ((n : ℝ) + 1)⁻¹) ^ α) c := fun n => hstep _ (by positivity)
  simp only [hfun, CFC.rpow_eq_cfc_real hc]
  refine tendsto_cfc_fun ?_ (.of_forall fun n => by fun_prop)
  -- Uniform continuity of `(·)^α` on `[0, ‖c‖ + 1]`, which contains `spec c`
  -- and every `t + 1/n` for `t` in it.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := ‖c‖ + 1)).uniformContinuousOn_of_continuous
      hcont.continuousOn) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ0
  filter_upwards [Filter.eventually_ge_atTop N] with n hn t ht
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hc ht
  have htM : t ≤ ‖c‖ := by
    have h := spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self t).trans h
  have hlam0 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hlamδ : ((n : ℝ) + 1)⁻¹ < δ := by
    have hle : ((N : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
      linarith
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hle
    rw [inv_eq_one_div]
    linarith
  have hlam1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : dist t (t + ((n : ℝ) + 1)⁻¹) < δ := by
    rw [Real.dist_eq]
    have hsub : t - (t + ((n : ℝ) + 1)⁻¹) = -((n : ℝ) + 1)⁻¹ := by ring
    rw [hsub, abs_neg, abs_of_pos hlam0]
    exact hlamδ
  exact hδ t ⟨ht0, by linarith⟩ (t + ((n : ℝ) + 1)⁻¹) ⟨by linarith, by linarith⟩ hd

end Pedersen

/-- **28III** (`sqrt-monotone`, cstar.tex:4420, Theorem): `0 ≤ a ≤ b`
implies `a^α ≤ b^α` for `α ∈ (0, 1]`; in particular the square root is
monotone on the positive elements.

*Class 1 — faithful.*  The Theorem's own proof **28IV**, after Pedersen, is
the section above; what is left here is its first movement, the reduction to
invertible elements: `a + 1/n ≤ b + 1/n` are positive and invertible, so
`(a + 1/n)^α ≤ (b + 1/n)^α` by `Icc_subset_monoExp`, and both sides converge
in norm by `tendsto_rpow_add_inv`, point 41 (`fc-uniformly-continuous`,
cstar.tex:4455). -/
theorem sqrt_monotone (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) (α : ℝ)
    (h0 : 0 < α) (h1 : α ≤ 1) :
    CFC.rpow a α ≤ CFC.rpow b α := by
  rcases subsingleton_or_nontrivial 𝒜 with _hs | _hnt
  · exact le_of_eq (Subsingleton.elim _ _)
  have hE : α ∈ monoExp 𝒜 := Icc_subset_monoExp ⟨h0.le, h1⟩
  have hb : 0 ≤ b := ha.trans hab
  have hepos : ∀ n : ℕ, IsStrictlyPositive (algebraMap ℝ 𝒜 ((n : ℝ) + 1)⁻¹) := by
    intro n
    exact ⟨algebraMap_nonneg 𝒜 (by positivity),
      (isUnit_iff_ne_zero.2 (by positivity)).map (algebraMap ℝ 𝒜)⟩
  have hmono : ∀ n : ℕ, (a + algebraMap ℝ 𝒜 ((n : ℝ) + 1)⁻¹) ^ α ≤
      (b + algebraMap ℝ 𝒜 ((n : ℝ) + 1)⁻¹) ^ α := fun n =>
    hE _ _ (IsStrictlyPositive.nonneg_add ha (hepos n)) (add_le_add hab le_rfl)
  exact le_of_tendsto_of_tendsto' (tendsto_rpow_add_inv ha h0.le)
    (tendsto_rpow_add_inv hb h0.le) hmono

end Ordered2

end FunctionalCalculus

/-! ## Parsec 290 (`gelfand-equivalence`): duality with compact Hausdorff spaces

**29I** (cstar.tex:4582): the functors `C : CH → (cCStar_miu)^op` and
`spec : (cCStar_miu)^op → CH`, and the statement that the Gelfand
representations form a natural isomorphism giving an equivalence
`(cCStar_miu)^op ≃ CH`.  The construction of the categories is out of scope
here; the key mathematical content is **29II** and **29VII** below. -/

section Duality

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **29II** (cstar.tex:4610, Lemma): every miu-map `τ : C(X) → ℂ`, `X`
compact Hausdorff, is given by evaluation at some point `x ∈ X`.

*Class 1 — faithful.*  The Lemma's own proof (cstar.tex:4520–4560), in three
movements around the set

  `Z = { x ∈ X : h(x) ≠ 0 for some h ≥ 0 in C(X) with τ(h) = 0 }`.

**29V** (cstar.tex:4647) — if `f ≥ 0` vanishes outside `Z` then `τ(f) = 0`:
each `x` with `f(x) > 0` lies in `Z`, so some `h ≥ 0` with `τ(h) = 0` has
`h(x) > 0`, and `g := (f(x)/h(x) + 1)·h` is a positive element with
`τ(g) = 0` and `g(x) > f(x)`; the sets `{ f < g }` cover the compact
`{ f ≥ ε }`, a finite subcover gives `g₁, …, g_N`, and their supremum
`g₁ ∨ ⋯ ∨ g_N` — which exists by **26II**.3 and which `τ` preserves by
**26II**.4, so `τ(g₁ ∨ ⋯ ∨ g_N) = 0` — dominates `f` up to `ε`.  Hence
`0 ≤ τ(f) ≤ ε` for every `ε > 0`.

**29IV** (cstar.tex:4637) — `X \ Z` has at most one point: for `x ≠ y`
Urysohn gives `p, q ≥ 0` with `pq = 0`, `p(x) = 1`, `q(y) = 1`, and
`0 = τ(pq) = τ(p)τ(q)` puts `x` or `y` into `Z`.  It is non-empty because
`f = 1` in **29V** would otherwise give `1 = τ(1) = 0`.

**29VI** (cstar.tex:4667) — with `x₀` the unique point outside `Z`, the
element `d := f − f(x₀)` has `(d*d)(x) ≠ 0 ⟹ x ≠ x₀ ⟹ x ∈ Z`, so **29V**
gives `0 = τ(d*d) = |τ(f) − f(x₀)|²`.

Mathlib's `CharacterSpace.homeoEval` is deliberately not used: reading `x`
off its surjectivity is reading it off **29VII**, which the thesis derives
*from* this Lemma.  The finite-supremum ingredient **29V** needs is
`commutative_cstar_basic_3_finite` with `commutative_cstar_basic_4_finite`. -/
theorem multiplicative_state_on_cx (τ : C(X, ℂ) →⋆ₐ[ℂ] ℂ) :
    ∃ x : X, ∀ f : C(X, ℂ), τ f = f x := by
  classical
  have hmono : ∀ {a b : C(X, ℂ)}, a ≤ b → τ a ≤ τ b := by
    intro a b hab
    have h := norm_mi_map_positive τ (b - a) (sub_nonneg.mpr hab)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  set Z : Set X := {x : X | ∃ h : C(X, ℂ), 0 ≤ h ∧ τ h = 0 ∧ h x ≠ 0} with hZdef
  -- **29V**
  have key : ∀ f : C(X, ℂ), 0 ≤ f → (∀ x : X, f x ≠ 0 → x ∈ Z) → τ f = 0 := by
    intro f hf hfZ
    have hf0 : (0 : ℂ) ≤ τ f := norm_mi_map_positive τ f hf
    have hbound : ∀ ε : ℝ, 0 < ε → (τ f).re ≤ 0 + ε := by
      intro ε hε
      have hKc : IsClosed {x : X | ε ≤ (f x).re} :=
        isClosed_le continuous_const (Complex.continuous_re.comp f.continuous)
      have hK : IsCompact {x : X | ε ≤ (f x).re} := hKc.isCompact
      set G : Type _ := {g : C(X, ℂ) // 0 ≤ g ∧ τ g = 0} with hGdef
      set U : G → Set X := fun g => {y : X | (f y).re < ((g : C(X, ℂ)) y).re} with hUdef
      have hUo : ∀ g : G, IsOpen (U g) := fun g =>
        isOpen_lt (Complex.continuous_re.comp f.continuous)
          (Complex.continuous_re.comp (g : C(X, ℂ)).continuous)
      have hcov : {x : X | ε ≤ (f x).re} ⊆ ⋃ g : G, U g := by
        intro x hx
        have hx' : ε ≤ (f x).re := hx
        have hfxre : 0 ≤ (f x).re := (Complex.le_def.mp ((ContinuousMap.le_def.mp hf) x)).1
        have hfx : f x ≠ 0 := by
          intro h0
          rw [h0] at hx'
          simp only [Complex.zero_re] at hx'
          exact absurd hx' (not_le.mpr hε)
        obtain ⟨h, hh0, hhτ, hhx⟩ := hfZ x hfx
        have hhxre : 0 < (h x).re := by
          rcases lt_or_eq_of_le ((ContinuousMap.le_def.mp hh0) x) with hlt | heq
          · exact (Complex.lt_def.mp hlt).1
          · exact absurd heq.symm hhx
        refine Set.mem_iUnion.mpr ⟨⟨(((f x).re / (h x).re + 1 : ℝ) : ℂ) • h, ?_, ?_⟩, ?_⟩
        · refine smul_nonneg ?_ hh0
          rw [Complex.zero_le_real]
          exact add_nonneg (div_nonneg hfxre hhxre.le) zero_le_one
        · rw [map_smul, hhτ, smul_zero]
        · show (f x).re < _
          simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hhxre)]
          linarith
      obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcov
      set S : Set C(X, ℂ) := insert 0 (Subtype.val '' (↑t : Set G)) with hSdef
      have hSfin : S.Finite := (t.finite_toSet.image _).insert _
      have hSne : S.Nonempty := Set.insert_nonempty _ _
      have hSnn : ∀ x ∈ S, (0 : C(X, ℂ)) ≤ x := by
        rintro x (rfl | ⟨g, -, rfl⟩)
        · exact le_refl _
        · exact g.2.1
      have hSsa : ∀ x ∈ S, IsSelfAdjoint x := fun x hx => IsSelfAdjoint.of_nonneg (hSnn x hx)
      obtain ⟨s, hs⟩ := commutative_cstar_basic_3_finite hSfin hSne hSsa
      have hτs : τ s = 0 := by
        have h4 := commutative_cstar_basic_4_finite τ hSfin hSne hSsa hs
        have himg : (⇑τ '' S) = {(0 : ℂ)} := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            rcases hx with rfl | ⟨g, -, rfl⟩
            · simp
            · simpa using g.2.2
          · rintro rfl
            exact ⟨0, Set.mem_insert _ _, map_zero τ⟩
        rw [himg] at h4
        exact h4.unique isLUB_singleton
      have hs0 : (0 : C(X, ℂ)) ≤ s := hs.1 (Set.mem_insert _ _)
      have hfle : f ≤ s + ((ε : ℂ) • 1) := by
        refine ContinuousMap.le_def.mpr fun y => ?_
        have him : (f y).im = 0 := ((Complex.le_def.mp ((ContinuousMap.le_def.mp hf) y)).2).symm
        have hsim : (s y).im = 0 := ((Complex.le_def.mp ((ContinuousMap.le_def.mp hs0) y)).2).symm
        have hsre : 0 ≤ (s y).re := (Complex.le_def.mp ((ContinuousMap.le_def.mp hs0) y)).1
        have hre : (f y).re ≤ (s y).re + ε := by
          by_cases hy : ε ≤ (f y).re
          · obtain ⟨g, hgt, hgy⟩ := Set.mem_iUnion₂.mp (ht hy)
            have hgs : (g : C(X, ℂ)) ≤ s :=
              hs.1 (Set.mem_insert_of_mem _ ⟨g, hgt, rfl⟩)
            have h1 : ((g : C(X, ℂ)) y).re ≤ (s y).re :=
              (Complex.le_def.mp ((ContinuousMap.le_def.mp hgs) y)).1
            have h2 : (f y).re < ((g : C(X, ℂ)) y).re := hgy
            linarith
          · have hy' : (f y).re < ε := not_le.mp hy
            linarith
        rw [Complex.le_def]
        refine ⟨?_, ?_⟩
        · simpa [Complex.add_re] using hre
        · simp [Complex.add_im, him, hsim]
      have hτle := hmono hfle
      rw [map_add, map_smul, map_one, hτs, smul_eq_mul, mul_one, zero_add] at hτle
      simpa using (Complex.le_def.mp hτle).1
    have hre : (τ f).re ≤ 0 := le_of_forall_pos_le_add hbound
    have hre0 : 0 ≤ (τ f).re := (Complex.le_def.mp hf0).1
    have him0 : (τ f).im = 0 := ((Complex.le_def.mp hf0).2).symm
    exact Complex.ext (by rw [Complex.zero_re]; linarith) (by rw [Complex.zero_im]; exact him0)
  -- **29IV**: `X \ Z` has at most one point
  have huniq : ∀ x y : X, x ∉ Z → y ∉ Z → x = y := by
    intro x y hx hy
    by_contra hxy
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
    obtain ⟨p, hp0, hp1, hp01⟩ :=
      exists_continuous_zero_one_of_isClosed (isClosed_compl_iff.mpr hU)
        (isClosed_singleton (x := x)) (by
          rw [Set.disjoint_left]
          rintro z hz rfl
          exact hz hxU)
    obtain ⟨q, hq0, hq1, hq01⟩ :=
      exists_continuous_zero_one_of_isClosed (isClosed_compl_iff.mpr hV)
        (isClosed_singleton (x := y)) (by
          rw [Set.disjoint_left]
          rintro z hz rfl
          exact hz hyV)
    set P : C(X, ℂ) := ⟨fun z => ((p z : ℝ) : ℂ), Complex.continuous_ofReal.comp p.continuous⟩
      with hPdef
    set Q : C(X, ℂ) := ⟨fun z => ((q z : ℝ) : ℂ), Complex.continuous_ofReal.comp q.continuous⟩
      with hQdef
    have hP0 : 0 ≤ P := by
      refine ContinuousMap.le_def.mpr fun z => ?_
      show (0 : ℂ) ≤ ((p z : ℝ) : ℂ)
      rw [Complex.zero_le_real]
      exact (hp01 z).1
    have hQ0 : 0 ≤ Q := by
      refine ContinuousMap.le_def.mpr fun z => ?_
      show (0 : ℂ) ≤ ((q z : ℝ) : ℂ)
      rw [Complex.zero_le_real]
      exact (hq01 z).1
    have hPQ : P * Q = 0 := by
      ext z
      show ((p z : ℝ) : ℂ) * ((q z : ℝ) : ℂ) = 0
      by_cases hz : z ∈ U
      · have : q z = 0 := hq0 (fun hzV => Set.disjoint_left.mp hUV hz hzV)
        rw [this]
        simp
      · have : p z = 0 := hp0 hz
        rw [this]
        simp
    have hmul : τ P * τ Q = 0 := by rw [← map_mul, hPQ, map_zero]
    have hPx : P x = 1 := by
      show ((p x : ℝ) : ℂ) = 1
      rw [hp1 rfl]
      simp
    have hQy : Q y = 1 := by
      show ((q y : ℝ) : ℂ) = 1
      rw [hq1 rfl]
      simp
    rcases mul_eq_zero.mp hmul with h | h
    · exact hx ⟨P, hP0, h, by rw [hPx]; exact one_ne_zero⟩
    · exact hy ⟨Q, hQ0, h, by rw [hQy]; exact one_ne_zero⟩
  -- `X \ Z` is nonempty
  have hex : ∃ x : X, x ∉ Z := by
    by_contra hall
    have hall' : ∀ x : X, x ∈ Z := fun x => not_not.mp (not_exists.mp hall x)
    have := key 1 zero_le_one (fun x _ => hall' x)
    rw [map_one] at this
    exact one_ne_zero this
  obtain ⟨x₀, hx₀⟩ := hex
  refine ⟨x₀, fun f => ?_⟩
  -- cstar.tex:4560
  set d : C(X, ℂ) := f - (f x₀) • 1 with hddef
  have hdx₀ : d x₀ = 0 := by simp [hddef]
  have hg : τ (star d * d) = 0 := by
    refine key _ (star_mul_self_nonneg d) ?_
    intro x hx
    by_contra hxZ
    have : x = x₀ := huniq x x₀ hxZ hx₀
    subst this
    exact hx (by simp [hdx₀])
  rw [map_mul, map_star] at hg
  have hd0 : τ d = 0 := by
    rcases mul_eq_zero.mp hg with h | h
    · exact star_eq_zero.mp h
    · exact h
  rw [hddef, map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_eq_zero] at hd0
  exact hd0

/-- **29VII** (cstar.tex:4670, Exercise): the map `x ↦ δₓ` (with
`δₓ(f) = f(x)`, an miu-map) is a homeomorphism from `X` onto `spec(C(X))`.

*Class 1 — faithful.*  The Exercise's own three steps.  That `δₓ` is miu and
that `x ↦ δₓ` is continuous is Mathlib's `continuousMapEval`, a definition.
Injectivity is Urysohn on the compact Hausdorff `X`: a `p` with `p(x) = 0`
and `p(y) = 1` separates `δₓ` from `δ_y`.  Surjectivity is **29II**
`multiplicative_state_on_cx`.  And a continuous bijection from a compact
space to a Hausdorff space is a homeomorphism — the corrected form of
erratum parsec-290.70.

Mathlib's `homeoEval` is deliberately not used: its surjectivity runs through
the maximal *ring* ideals of `C(X)`, the route **16VIII** rejects, and it
inverts the thesis's order, which proves **29II** first and reads this
Exercise off it. -/
theorem eval_homeomorphism :
    ∃ e : X ≃ₜ characterSpace ℂ C(X, ℂ),
      ∀ (x : X) (f : C(X, ℂ)), (e x : WeakDual ℂ C(X, ℂ)) f = f x := by
  have hinj : Function.Injective (WeakDual.CharacterSpace.continuousMapEval X ℂ) := by
    intro x y hxy
    by_contra hne
    obtain ⟨p, hp0, hp1, -⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x)) (isClosed_singleton (x := y))
      (Set.disjoint_singleton.mpr hne)
    have h : ((p x : ℝ) : ℂ) = ((p y : ℝ) : ℂ) :=
      congrArg (fun φ : characterSpace ℂ C(X, ℂ) =>
        (φ : WeakDual ℂ C(X, ℂ))
          (⟨fun z => ((p z : ℝ) : ℂ), Complex.continuous_ofReal.comp p.continuous⟩ :
            C(X, ℂ))) hxy
    rw [hp0 rfl, hp1 rfl] at h
    exact zero_ne_one (by exact_mod_cast h)
  have hsurj : Function.Surjective (WeakDual.CharacterSpace.continuousMapEval X ℂ) := by
    intro φ
    let τ : C(X, ℂ) →⋆ₐ[ℂ] ℂ :=
      { WeakDual.CharacterSpace.equivAlgHom φ with
        map_star' := fun f => map_star φ f }
    obtain ⟨x, hx⟩ := multiplicative_state_on_cx τ
    exact ⟨x, Subtype.ext (ContinuousLinearMap.ext fun f => (hx f).symm)⟩
  exact ⟨@Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
      { Equiv.ofBijective _ ⟨hinj, hsurj⟩ with
        toFun := WeakDual.CharacterSpace.continuousMapEval X ℂ }
      (map_continuous (WeakDual.CharacterSpace.continuousMapEval X ℂ)),
    fun _ _ => rfl⟩

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [CStarAlgebra ℬ]

/-- **29VIII** (`injective-miu-isometry`, cstar.tex:4680, Exercise): every
injective miu-map between C*-algebras is an isometry.

*Class 3 — mathlib.*  `NonUnitalStarAlgHom.norm_map`: pass to the
unitization, reduce by the C*-identity to `star a * a`, then equate the norms
through the real spectrum and the spectral radius.  The Exercise's own route
— mono = injective and epi = surjective in `CH`, so that the restriction
`σ : C*(a) → C*(ρ a)`, being epi and mono, is an isomorphism — is not
transcribed: the categories of **29I** are out of scope here, and Mathlib has
no category of C*-algebras either. -/
theorem injective_miu_isometry (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) (a : 𝒜) : ‖ρ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map ρ hρ a

/-- **29IX** (`injective-miu-iso-on-image`, cstar.tex:4707, Exercise), first
clause: the range of an injective miu-map `ρ : 𝒜 → ℬ` is closed.

*Class 1 — faithful.*  The solution's route: `ρ` is an isometry by **29VIII**
(`injective_miu_isometry`), so a convergent sequence in `ρ(𝒜)` pulls back to a
Cauchy sequence in `𝒜`, which converges by completeness, and its image is the
limit — i.e. an isometric image of a complete space is closed.  Closedness is
grounded here on **29VIII** exactly as printed, rather than on Mathlib's own
`NonUnitalStarAlgHom.isometry`. -/
theorem injective_miu_iso_on_image (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) : IsClosed (Set.range ρ) := by
  have hiso : Isometry ρ :=
    AddMonoidHomClass.isometry_of_norm ρ (injective_miu_isometry ρ hρ)
  exact hiso.isClosedEmbedding.isClosed_range

/-- **29IX** (`injective-miu-iso-on-image`, cstar.tex:4707, Exercise), the
conclusion the Exercise asks one to draw: `ρ(𝒜)` is a *C*-subalgebra* of `ℬ`
— a ⋆-subalgebra with closed carrier — and `ρ` is an miu-isomorphism of `𝒜`
onto it.

This is the clause that **27XVIII**.2 and **30X** defer to.

*Class 1 — faithful.*  Closedness is the first clause, from **29VIII**; the
isomorphism is `ρ` corestricted to its range, injective by hypothesis. -/
theorem injective_miu_iso_on_image_isomorphism (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) :
    ∃ S : StarSubalgebra ℂ ℬ, (S : Set ℬ) = Set.range ρ ∧ IsClosed (S : Set ℬ) ∧
      ∃ e : 𝒜 ≃⋆ₐ[ℂ] S, ∀ a : 𝒜, Subtype.val (e a) = ρ a := by
  refine ⟨StarAlgHom.range ρ, rfl, ?_, StarAlgEquiv.ofInjective ρ hρ, fun _ => rfl⟩
  show IsClosed (Set.range ρ)
  exact injective_miu_iso_on_image ρ hρ

end Duality

/-! ## Parsec 300: representation by bounded operators

**30I** (`completion-inner-product-space`, cstar.tex:4720): the plan for the
Gelfand–Naimark theorem via the GNS construction — nothing to formalize. -/

section GNS

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **30II** (`state-inner-product`, cstar.tex:4769, Lemma): for every p-map
`ω : 𝒜 → ℂ` on a C*-algebra, `[a, b]_ω = ω(a* b)` defines an inner product
on `𝒜` (positive semi-definite, conjugate symmetric; linearity in the second
argument is automatic). -/
theorem state_inner_product (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    0 ≤ ω (star a * a) ∧ star (ω (star a * b)) = ω (star b * a) :=
  ⟨hω _ (star_mul_self_nonneg a), by
    simpa [star_mul] using (cstar_p_implies_i ω hω (star a * b)).symm⟩

/-- The seminorm `‖a‖_ω = ω(a* a)^{1/2}` induced by a positive functional
`ω` (**30IV**, `omega-norm-basic`, cstar.tex:4787). -/
noncomputable def omegaSeminorm (ω : 𝒜 →ₗ[ℂ] ℂ) (a : 𝒜) : ℝ :=
  Real.sqrt (ω (star a * a)).re

/-- A positive linear functional in the sense of `IsPositiveMap`, bundled as
Mathlib's `PositiveLinearMap` so that the GNS machinery applies.  (Auxiliary.) -/
private def toPLM (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω) : 𝒜 →ₚ[ℂ] ℂ where
  __ := ω
  monotone' a b hab := by
    have h := hω (b - a) (sub_nonneg.mpr hab)
    rw [map_sub] at h
    exact sub_nonneg.mp h

@[simp]
private theorem toPLM_apply (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω) (a : 𝒜) :
    toPLM ω hω a = ω a := rfl

/-- The inner product `[a, b]_ω = ω(a* b)` of **30II** as a
`PreInnerProductSpace.Core ℂ 𝒜` — possibly degenerate, which is the setting
of **4XV** (`A/CStar/Basic`).  It is what **30IV**.1 applies Cauchy–Schwarz
to, as the Exercise instructs. -/
@[instance_reducible] private noncomputable def omegaCore (ω : 𝒜 →ₗ[ℂ] ℂ)
    (hω : IsPositiveMap ω) :
    PreInnerProductSpace.Core ℂ 𝒜 where
  inner a b := ω (star a * b)
  conj_inner_symm a b := by
    simpa [Complex.star_def] using (state_inner_product ω hω b a).2
  re_inner_nonneg a := (Complex.le_def.mp (hω _ (star_mul_self_nonneg a))).1
  add_left a b c := by
    show ω (star (a + b) * c) = ω (star a * c) + ω (star b * c)
    rw [star_add, add_mul, map_add]
  smul_left a b r := by
    show ω (star (r • a) * b) = (starRingEnd ℂ) r * ω (star a * b)
    rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul, starRingEnd_apply]

/-- **30IV** (`omega-norm-basic`, cstar.tex:4787, Exercise), part 1
(Kadison's inequality): `|ω(a* b)|² ≤ ω(a* a) ω(b* b)` for a p-map `ω`.

*Class 1 — faithful.*  The Exercise says "use Cauchy–Schwarz
(`inner-product-basic`)", and that is what this does: **4XV**.1
`inner_product_basic_1` for the inner product `[·,·]_ω` of **30II**, packaged
as `omegaCore` above.  `ω(a* a)` and `ω(b* b)` are real because `ω` is
positive, which turns the real inequality into the stated one over `ℂ`. -/
theorem omega_norm_basic_1 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    ((‖ω (star a * b)‖ : ℂ)) ^ 2 ≤ ω (star a * a) * ω (star b * b) := by
  have hcs : ‖ω (star a * b)‖ ^ 2
      ≤ RCLike.re (ω (star a * a)) * RCLike.re (ω (star b * b)) :=
    inner_product_basic_1 (V := 𝒜) (c := omegaCore ω hω) a b
  have hre : ∀ x : 𝒜, ω (star x * x) = ((RCLike.re (ω (star x * x)) : ℝ) : ℂ) := by
    intro x
    have h := hω _ (star_mul_self_nonneg x)
    refine Complex.ext rfl ?_
    rw [Complex.ofReal_im]
    exact ((Complex.le_def.mp h).2).symm
  rw [hre a, hre b]
  exact_mod_cast RCLike.ofReal_le_ofReal (K := ℂ) |>.mpr hcs

/-- **30IV** (`omega-norm-basic`, cstar.tex:4787, Exercise), part 2, the
inequality (in the corrected form of erratum `parsec-300.40`, without the
`‖ω‖` factor): `‖ab‖_ω ≤ ‖a‖ ‖b‖_ω`, using `a* a ≤ ‖a‖²`.  The four
counterexamples the exercise also asks for are
`omega_norm_basic_2_counterexamples` below.

*Class 1 — faithful.*  This is the solution's own estimate: `‖ab‖_ω² =
ω(b*(a*a)b) ≤ ‖a‖² ω(b*b) = ‖a‖² ‖b‖_ω²`, where `a*a ≤ ‖a‖²·1` (self-adjoint
`≤ ‖·‖` by the parsec-90 order and the C*-identity) and `b*(·)b` is order
preserving (**25II**, `star_left_conjugate_le_conjugate`), and `ω` is monotone
because positive; taking square roots gives the claim. -/
theorem omega_norm_basic_2 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    omegaSeminorm ω (a * b) ≤ ‖a‖ * omegaSeminorm ω b := by
  have hmono : ∀ {x y : 𝒜}, x ≤ y → ω x ≤ ω y := by
    intro x y h
    have := hω (y - x) (sub_nonneg.mpr h)
    rw [map_sub] at this
    exact sub_nonneg.mp this
  -- `a*a ≤ ‖a‖·‖a‖ • 1` (self-adjoint `≤ ‖·‖` and the C*-identity)
  have h1 : star a * a ≤ (‖a‖ * ‖a‖) • (1 : 𝒜) := by
    have h := (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a)).le_algebraMap_norm_self
    rwa [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one] at h
  -- conjugate by `b` (25II: `b*(·)b` order preserving)
  have h2 : star b * (star a * a) * b ≤ (‖a‖ * ‖a‖) • (star b * b) := by
    have := star_left_conjugate_le_conjugate h1 b
    rwa [show star b * ((‖a‖ * ‖a‖) • (1 : 𝒜)) * b = (‖a‖ * ‖a‖) • (star b * b) by
      rw [mul_smul_comm, smul_mul_assoc, mul_one]] at this
  have hcomm : star (a * b) * (a * b) = star b * (star a * a) * b := by
    rw [star_mul]; noncomm_ring
  -- push through the positive `ω` and take real parts
  have hle : ω (star (a * b) * (a * b)) ≤ (‖a‖ * ‖a‖) • ω (star b * b) := by
    rw [hcomm]
    refine (hmono h2).trans_eq ?_
    rw [LinearMap.map_smul_of_tower]
  have hre : (ω (star (a * b) * (a * b))).re ≤ (‖a‖ * ‖a‖) * (ω (star b * b)).re := by
    have := (Complex.le_def.mp hle).1
    rwa [Complex.smul_re, smul_eq_mul] at this
  unfold omegaSeminorm
  rw [show ‖a‖ = Real.sqrt (‖a‖ * ‖a‖) by rw [Real.sqrt_mul_self (norm_nonneg a)],
    ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hre

/-! The four counterexamples of **30IV**.2, all in `𝒜 = M₂(ℂ)` with the
p-map `ω : M ↦ M₀₀`, which are the thesis's own witnesses. -/

private theorem exists_star_mul_self_aux {M : Type*} [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] {a : M} (ha : 0 ≤ a) :
    ∃ b, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha

/-- `ω : M₂(ℂ) → ℂ`, `M ↦ M₀₀` — the p-map the exercise's hints use. -/
private noncomputable def omegaM2 : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun M := M 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem omegaM2_pos : IsPositiveMap omegaM2 := by
  intro M hM
  obtain ⟨C, rfl⟩ := exists_star_mul_self_aux hM
  show (0 : ℂ) ≤ (star C * C) 0 0
  rw [CStarMatrix.mul_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [CStarMatrix.star_apply]
  exact star_mul_self_nonneg _

/-- `‖a‖_ω² = |a₀₀|² + |a₁₀|²` for this `ω`. -/
private theorem omegaSeminorm_M2 (a : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    omegaSeminorm omegaM2 a
      = Real.sqrt (Complex.normSq (a 0 0) + Complex.normSq (a 1 0)) := by
  unfold omegaSeminorm
  congr 1
  show ((star a * a) 0 0).re = _
  rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
  simp [CStarMatrix.star_apply, Complex.normSq_apply, Complex.add_re, Complex.mul_re]

/-- `½(¹¹₁₁)`, the thesis's second witness. -/
private noncomputable def pM2 : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![1/2, 1/2; 1/2, 1/2]

/-- `(⁰⁰₀₁)`, the thesis's first witness. -/
private noncomputable def dM2 : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![0, 0; 0, 1]

/-- `(⁰¹₀₀)`, for the last counterexample. -/
private noncomputable def eM2 : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![0, 1; 0, 0]

private theorem pM2_norm : omegaSeminorm omegaM2 pM2 = Real.sqrt (1/2) := by
  rw [omegaSeminorm_M2]
  norm_num [pM2, CStarMatrix.ofMatrix_apply, Complex.normSq_apply]

private theorem pM2_sq : pM2 * pM2 = pM2 := by
  ext i j
  rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [pM2, CStarMatrix.ofMatrix_apply]

private theorem pM2_star : star pM2 = pM2 := by
  ext i j
  rw [CStarMatrix.star_apply]
  fin_cases i <;> fin_cases j <;> norm_num [pM2, CStarMatrix.ofMatrix_apply]

private theorem half_lt_sqrt_half : (1/2 : ℝ) < Real.sqrt (1/2) := by
  rw [show (1/2 : ℝ) = Real.sqrt ((1/2) ^ 2) by rw [Real.sqrt_sq]; norm_num]
  exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

/-- **30IV** (`omega-norm-basic`, cstar.tex:4787, Exercise), part 2, the four
counterexamples: for the p-map `ω : M ↦ M₀₀` on `M₂(ℂ)` none of

* `‖ab‖_ω ≤ ‖a‖_ω ‖b‖`,
* `‖ab‖_ω ≤ ‖a‖_ω ‖b‖_ω`,
* `‖a* a‖_ω = ‖a‖_ω²`,
* `‖a*‖_ω = ‖a‖_ω`

holds in general.

*Class 1 — faithful.*  The witnesses are the exercise's own hints:
`a = (⁰⁰₀₁)`, `b = ½(¹¹₁₁)` for the first; `a = b = ½(¹¹₁₁)` for the second
and third (where `‖a‖_ω = √½` but `‖a‖_ω² = ½ < √½`).  For the fourth, which
the exercise leaves open, we take the matrix unit `a = (⁰¹₀₀)`: `‖a‖_ω = 0`
while `‖a*‖_ω = 1`. -/
theorem omega_norm_basic_2_counterexamples :
    ∃ ω : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ, IsPositiveMap ω ∧
      (∃ a b : CStarMatrix (Fin 2) (Fin 2) ℂ,
        ¬ omegaSeminorm ω (a * b) ≤ omegaSeminorm ω a * ‖b‖) ∧
      (∃ a b : CStarMatrix (Fin 2) (Fin 2) ℂ,
        ¬ omegaSeminorm ω (a * b) ≤ omegaSeminorm ω a * omegaSeminorm ω b) ∧
      (∃ a : CStarMatrix (Fin 2) (Fin 2) ℂ,
        omegaSeminorm ω (star a * a) ≠ omegaSeminorm ω a ^ 2) ∧
      (∃ a : CStarMatrix (Fin 2) (Fin 2) ℂ,
        omegaSeminorm ω (star a) ≠ omegaSeminorm ω a) := by
  refine ⟨omegaM2, omegaM2_pos, ⟨dM2, pM2, ?_⟩, ⟨pM2, pM2, ?_⟩, ⟨pM2, ?_⟩, ⟨eM2, ?_⟩⟩
  · have hL : omegaSeminorm omegaM2 (dM2 * pM2) = 1/2 := by
      rw [omegaSeminorm_M2]
      have h0 : (dM2 * pM2) 0 0 = 0 := by
        rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
        simp [dM2, pM2, CStarMatrix.ofMatrix_apply]
      have h1 : (dM2 * pM2) 1 0 = 1/2 := by
        rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
        simp [dM2, pM2, CStarMatrix.ofMatrix_apply]
      rw [h0, h1]
      norm_num [Complex.normSq_apply]
    have hR : omegaSeminorm omegaM2 dM2 = 0 := by
      rw [omegaSeminorm_M2]
      norm_num [dM2, CStarMatrix.ofMatrix_apply, Complex.normSq_apply]
    rw [hL, hR, zero_mul]
    norm_num
  · rw [pM2_sq, pM2_norm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
    exact not_le.mpr half_lt_sqrt_half
  · rw [pM2_star, pM2_sq, pM2_norm, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
    intro h
    have hl := half_lt_sqrt_half
    rw [h] at hl
    exact lt_irrefl _ hl
  · have h1 : omegaSeminorm omegaM2 eM2 = 0 := by
      rw [omegaSeminorm_M2]
      norm_num [eM2, CStarMatrix.ofMatrix_apply, Complex.normSq_apply]
    have h2 : omegaSeminorm omegaM2 (star eM2) = 1 := by
      rw [omegaSeminorm_M2]
      have e0 : (star eM2) 0 0 = 0 := by
        rw [CStarMatrix.star_apply]; norm_num [eM2, CStarMatrix.ofMatrix_apply]
      have e1 : (star eM2) 1 0 = 1 := by
        rw [CStarMatrix.star_apply]; norm_num [eM2, CStarMatrix.ofMatrix_apply]
      rw [e0, e1]
      norm_num [Complex.normSq_apply]
    rw [h1, h2]
    norm_num

/-! ### 30V: the completion of an inner product space, built by hand -/

namespace InnerCompletion

noncomputable section

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- `‖x‖ = √⟪x,x⟫` in any (semi)normed inner product space. -/
theorem norm_eq_sqrt_re_inner' {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x : E) : ‖x‖ = Real.sqrt (RCLike.re (⟪x, x⟫ : ℂ)) := by
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x, Real.sqrt_sq (norm_nonneg x)]

theorem re_inner_self_nonneg' {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x : E) : 0 ≤ RCLike.re (⟪x, x⟫ : ℂ) := by
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x]
  positivity

omit [InnerProductSpace ℂ V] in
/-- A Cauchy sequence on `V` is bounded. -/
theorem cau_bdd {a : ℕ → V} (ha : CauchySeq a) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C := by
  obtain ⟨R, hR0, hR⟩ := cauchySeq_bdd ha
  refine ⟨‖a 0‖ + R, by positivity, fun n => ?_⟩
  have h := hR n 0
  rw [dist_eq_norm] at h
  have h2 : ‖a n‖ ≤ ‖a n - a 0‖ + ‖a 0‖ := by
    simpa using norm_add_le (a n - a 0) (a 0)
  linarith

/-- The Cauchy sequences on `V`, as a submodule of `ℕ → V`. -/
def cauSeqs (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Submodule ℂ (ℕ → V) where
  carrier := {a | CauchySeq a}
  add_mem' {a b} ha hb := ha.add hb
  zero_mem' := cauchySeq_const 0
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Metric.cauchySeq_iff] at ha ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := ha (ε / (‖c‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm] at h ⊢
    have hsm : (c • a) m - (c • a) n = c • (a m - a n) := by
      simp [Pi.smul_apply, smul_sub]
    rw [hsm, norm_smul]
    have h1 : ‖c‖ * ‖a m - a n‖ ≤ (‖c‖ + 1) * ‖a m - a n‖ := by
      nlinarith [norm_nonneg (a m - a n)]
    have h2 : (‖c‖ + 1) * ‖a m - a n‖ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) :=
      mul_lt_mul_of_pos_left h (by positivity)
    rw [mul_div_cancel₀ _ (by positivity : (‖c‖ + 1) ≠ 0)] at h2
    linarith

/-- The null sequences among the Cauchy sequences: `lim ‖aₙ‖ = 0`.  Two Cauchy
sequences are identified in the completion exactly when their difference is
null, which is the thesis's `lim ‖aₙ − bₙ‖ = 0`. -/
def nullSeqs (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Submodule ℂ ↥(cauSeqs V) where
  carrier := {a | Tendsto (fun n => ‖(a : ℕ → V) n‖) atTop (𝓝 0)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_add_le ((a : ℕ → V) n) ((b : ℕ → V) n)) (by simpa using ha.add hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := ha.const_mul ‖c‖
    rw [mul_zero] at h
    exact h.congr (fun n => by simp [norm_smul])

/-- The completion of `V`: Cauchy sequences on `V` modulo `lim ‖aₙ − bₙ‖ = 0`. -/
def Cpl (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] : Type _ :=
  ↥(cauSeqs V) ⧸ nullSeqs V

instance : AddCommGroup (Cpl V) :=
  inferInstanceAs (AddCommGroup (↥(cauSeqs V) ⧸ nullSeqs V))

instance : Module ℂ (Cpl V) :=
  inferInstanceAs (Module ℂ (↥(cauSeqs V) ⧸ nullSeqs V))

/-- The class of a Cauchy sequence in the completion. -/
def mkC (a : ↥(cauSeqs V)) : Cpl V := Submodule.Quotient.mk a

theorem mkC_surjective : Function.Surjective (mkC (V := V)) :=
  fun x => Submodule.Quotient.mk_surjective _ x

theorem mkC_add (a b : ↥(cauSeqs V)) : mkC (a + b) = mkC a + mkC b := rfl

theorem mkC_sub (a b : ↥(cauSeqs V)) : mkC (a - b) = mkC a - mkC b := rfl

theorem mkC_smul (c : ℂ) (a : ↥(cauSeqs V)) : mkC (c • a) = c • mkC a := rfl

theorem mkC_eq_zero {a : ↥(cauSeqs V)} :
    (mkC a : Cpl V) = 0 ↔ Tendsto (fun n => ‖a.1 n‖) atTop (𝓝 0) :=
  Submodule.Quotient.mk_eq_zero _

theorem mkC_eq_mkC {a b : ↥(cauSeqs V)} :
    (mkC a : Cpl V) = mkC b ↔ Tendsto (fun n => ‖a.1 n - b.1 n‖) atTop (𝓝 0) :=
  Submodule.Quotient.eq _

/-! #### The inner product on the completion -/

/-- Solution parsec-300.50, item 2, for the inner product: if `a` and `b` are
Cauchy then so is `⟪aₙ,bₙ⟫`, by Cauchy–Schwarz and the boundedness of a Cauchy
sequence. -/
theorem inner_cauchySeq {a b : ℕ → V} (ha : CauchySeq a) (hb : CauchySeq b) :
    CauchySeq (fun n => (⟪a n, b n⟫ : ℂ)) := by
  obtain ⟨Ca, hCa0, hCa⟩ := cau_bdd ha
  obtain ⟨Cb, hCb0, hCb⟩ := cau_bdd hb
  rw [Metric.cauchySeq_iff] at ha hb ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / (4 * (Cb + 1))) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hb (ε / (4 * (Ca + 1))) (by positivity)
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  have h1 := hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  have h2 := hN₂ m (le_of_max_le_right hm) n (le_of_max_le_right hn)
  rw [dist_eq_norm] at h1 h2 ⊢
  have hsplit : (⟪a m, b m⟫ : ℂ) - ⟪a n, b n⟫
      = ⟪a m - a n, b m⟫ + ⟪a n, b m - b n⟫ := by
    rw [inner_sub_left, inner_sub_right]; ring
  rw [hsplit]
  have e1 : ‖(⟪a m - a n, b m⟫ : ℂ)‖ ≤ ‖a m - a n‖ * ‖b m‖ := norm_inner_le_norm _ _
  have e2 : ‖(⟪a n, b m - b n⟫ : ℂ)‖ ≤ ‖a n‖ * ‖b m - b n‖ := norm_inner_le_norm _ _
  have t1 : ‖a m - a n‖ * ‖b m‖ ≤ ε / 4 := by
    have hb' : ‖b m‖ ≤ Cb + 1 := (hCb m).trans (by linarith)
    have hmul := mul_le_mul h1.le hb' (norm_nonneg _) (by positivity)
    calc ‖a m - a n‖ * ‖b m‖ ≤ (ε / (4 * (Cb + 1))) * (Cb + 1) := hmul
      _ = ε / 4 := by field_simp
  have t2 : ‖a n‖ * ‖b m - b n‖ ≤ ε / 4 := by
    have ha' : ‖a n‖ ≤ Ca + 1 := (hCa n).trans (by linarith)
    have hmul := mul_le_mul ha' h2.le (norm_nonneg _) (by positivity)
    calc ‖a n‖ * ‖b m - b n‖ ≤ (Ca + 1) * (ε / (4 * (Ca + 1))) := hmul
      _ = ε / 4 := by field_simp
  have htri := norm_add_le (⟪a m - a n, b m⟫ : ℂ) (⟪a n, b m - b n⟫ : ℂ)
  linarith

/-- The inner product of two Cauchy sequences: `lim ⟪aₙ,bₙ⟫`. -/
def ipCau (a b : ↥(cauSeqs V)) : ℂ := limUnder atTop (fun n => (⟪a.1 n, b.1 n⟫ : ℂ))

theorem ipCau_tendsto (a b : ↥(cauSeqs V)) :
    Tendsto (fun n => (⟪a.1 n, b.1 n⟫ : ℂ)) atTop (𝓝 (ipCau a b)) :=
  (inner_cauchySeq a.2 b.2).tendsto_limUnder

/-- Solution parsec-300.50, item 3, for the inner product: `lim ⟪aₙ,bₙ⟫` does
not change when `a` and `b` are replaced by equivalent Cauchy sequences. -/
theorem ipCau_congr {a a' b b' : ↥(cauSeqs V)}
    (ha : Tendsto (fun n => ‖a.1 n - a'.1 n‖) atTop (𝓝 0))
    (hb : Tendsto (fun n => ‖b.1 n - b'.1 n‖) atTop (𝓝 0)) :
    ipCau a b = ipCau a' b' := by
  obtain ⟨Cb, hCb0, hCb⟩ := cau_bdd b.2
  obtain ⟨Ca, hCa0, hCa⟩ := cau_bdd a'.2
  have hdiff : Tendsto (fun n => (⟪a.1 n, b.1 n⟫ : ℂ) - ⟪a'.1 n, b'.1 n⟫) atTop (𝓝 0) := by
    refine squeeze_zero_norm
      (a := fun n => ‖a.1 n - a'.1 n‖ * Cb + Ca * ‖b.1 n - b'.1 n‖) (fun n => ?_) ?_
    · have hsplit : (⟪a.1 n, b.1 n⟫ : ℂ) - ⟪a'.1 n, b'.1 n⟫
          = ⟪a.1 n - a'.1 n, b.1 n⟫ + ⟪a'.1 n, b.1 n - b'.1 n⟫ := by
        rw [inner_sub_left, inner_sub_right]; ring
      rw [hsplit]
      have e1 : ‖(⟪a.1 n - a'.1 n, b.1 n⟫ : ℂ)‖ ≤ ‖a.1 n - a'.1 n‖ * ‖b.1 n‖ :=
        norm_inner_le_norm _ _
      have e2 : ‖(⟪a'.1 n, b.1 n - b'.1 n⟫ : ℂ)‖ ≤ ‖a'.1 n‖ * ‖b.1 n - b'.1 n‖ :=
        norm_inner_le_norm _ _
      have f1 : ‖a.1 n - a'.1 n‖ * ‖b.1 n‖ ≤ ‖a.1 n - a'.1 n‖ * Cb :=
        mul_le_mul_of_nonneg_left (hCb n) (norm_nonneg _)
      have f2 : ‖a'.1 n‖ * ‖b.1 n - b'.1 n‖ ≤ Ca * ‖b.1 n - b'.1 n‖ :=
        mul_le_mul_of_nonneg_right (hCa n) (norm_nonneg _)
      have htri := norm_add_le (⟪a.1 n - a'.1 n, b.1 n⟫ : ℂ) (⟪a'.1 n, b.1 n - b'.1 n⟫ : ℂ)
      linarith
    · have hsum := (ha.mul_const Cb).add (hb.const_mul Ca)
      simpa using hsum
  have hlim : Tendsto (fun n => (⟪a'.1 n, b'.1 n⟫ : ℂ)) atTop (𝓝 (ipCau a b)) := by
    have h := (ipCau_tendsto a b).sub hdiff
    rw [sub_zero] at h
    exact h.congr (fun n => by ring)
  exact tendsto_nhds_unique hlim (ipCau_tendsto a' b')

/-- The inner product on the completion. -/
def ipQuot (x y : Cpl V) : ℂ :=
  Quotient.liftOn₂' x y ipCau (by
    intro a b a' b' ha hb
    exact ipCau_congr ((Submodule.quotientRel_def _).1 ha) ((Submodule.quotientRel_def _).1 hb))

theorem ipQuot_mk (a b : ↥(cauSeqs V)) : ipQuot (mkC a : Cpl V) (mkC b) = ipCau a b := rfl

theorem ipQuot_conj (x y : Cpl V) : (starRingEnd ℂ) (ipQuot y x) = ipQuot x y := by
  obtain ⟨a, rfl⟩ := mkC_surjective x
  obtain ⟨b, rfl⟩ := mkC_surjective y
  rw [ipQuot_mk, ipQuot_mk, starRingEnd_apply]
  refine tendsto_nhds_unique ?_ (ipCau_tendsto a b)
  exact ((ipCau_tendsto b a).star).congr
    (fun n => by rw [← starRingEnd_apply, inner_conj_symm])

theorem ipQuot_nonneg (x : Cpl V) : 0 ≤ RCLike.re (ipQuot x x) := by
  obtain ⟨a, rfl⟩ := mkC_surjective x
  rw [ipQuot_mk]
  exact ge_of_tendsto' (((RCLike.continuous_re (K := ℂ)).tendsto _).comp (ipCau_tendsto a a))
    (fun n => re_inner_self_nonneg' (a.1 n))

theorem ipQuot_add_left (x y z : Cpl V) :
    ipQuot (x + y) z = ipQuot x z + ipQuot y z := by
  obtain ⟨a, rfl⟩ := mkC_surjective x
  obtain ⟨b, rfl⟩ := mkC_surjective y
  obtain ⟨c, rfl⟩ := mkC_surjective z
  rw [← mkC_add, ipQuot_mk, ipQuot_mk, ipQuot_mk]
  refine tendsto_nhds_unique (ipCau_tendsto (a + b) c) ?_
  exact ((ipCau_tendsto a c).add (ipCau_tendsto b c)).congr
    (fun n => (inner_add_left (𝕜 := ℂ) (a.1 n) (b.1 n) (c.1 n)).symm)

theorem ipQuot_smul_left (x y : Cpl V) (r : ℂ) :
    ipQuot (r • x) y = (starRingEnd ℂ) r * ipQuot x y := by
  obtain ⟨a, rfl⟩ := mkC_surjective x
  obtain ⟨b, rfl⟩ := mkC_surjective y
  rw [← mkC_smul, ipQuot_mk, ipQuot_mk]
  refine tendsto_nhds_unique (ipCau_tendsto (r • a) b) ?_
  exact ((ipCau_tendsto a b).const_mul ((starRingEnd ℂ) r)).congr
    (fun n => (inner_smul_left (𝕜 := ℂ) (a.1 n) (b.1 n) r).symm)

theorem ipQuot_definite (x : Cpl V) (hx : ipQuot x x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := mkC_surjective x
  rw [ipQuot_mk] at hx
  rw [mkC_eq_zero]
  have h1 : Tendsto (fun n => RCLike.re (⟪a.1 n, a.1 n⟫ : ℂ)) atTop
      (𝓝 (RCLike.re (ipCau a a))) :=
    ((RCLike.continuous_re (K := ℂ)).tendsto _).comp (ipCau_tendsto a a)
  rw [hx, map_zero] at h1
  have h2 := h1.sqrt
  rw [Real.sqrt_zero] at h2
  exact h2.congr (fun n => (norm_eq_sqrt_re_inner' (a.1 n)).symm)

/-- The inner-product core of the completion.  Positive *definiteness* is the
point of the quotient: `lim ⟪aₙ,aₙ⟫ = 0` says exactly that `a` is null. -/
instance complCore : InnerProductSpace.Core ℂ (Cpl V) where
  inner := ipQuot
  conj_inner_symm := ipQuot_conj
  re_inner_nonneg := ipQuot_nonneg
  add_left := ipQuot_add_left
  smul_left := ipQuot_smul_left
  definite := ipQuot_definite

instance : NormedAddCommGroup (Cpl V) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (Cpl V) := InnerProductSpace.ofCore _

theorem inner_mkC (a b : ↥(cauSeqs V)) :
    (⟪(mkC a : Cpl V), mkC b⟫ : ℂ) = ipCau a b := rfl

/-- The norm on the completion is the thesis's `lim ‖aₙ‖`. -/
theorem norm_mkC_tendsto (a : ↥(cauSeqs V)) :
    Tendsto (fun n => ‖a.1 n‖) atTop (𝓝 ‖(mkC a : Cpl V)‖) := by
  rw [norm_eq_sqrt_re_inner' (mkC a : Cpl V), inner_mkC]
  exact ((((RCLike.continuous_re (K := ℂ)).tendsto _).comp (ipCau_tendsto a a)).sqrt).congr
    (fun n => (norm_eq_sqrt_re_inner' (a.1 n)).symm)

/-- Solution parsec-300.50, item 3: the distance on the completion is the
thesis's `d((aₙ)ₙ, (bₙ)ₙ) = lim ‖aₙ − bₙ‖`. -/
theorem dist_mkC_tendsto (a b : ↥(cauSeqs V)) :
    Tendsto (fun n => ‖a.1 n - b.1 n‖) atTop (𝓝 (dist (mkC a : Cpl V) (mkC b))) := by
  rw [dist_eq_norm, ← mkC_sub]
  exact norm_mkC_tendsto (a - b)

/-! #### The embedding `η` -/

/-- The constant sequence `a, a, a, …`. -/
def constSeq (v : V) : ↥(cauSeqs V) := ⟨fun _ => v, cauchySeq_const v⟩

/-- **30V**'s embedding `η : V → ℋ`, sending `a` to the constant sequence. -/
def etaMap (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V →ₗ[ℂ] Cpl V where
  toFun v := mkC (constSeq v)
  map_add' _v _w := rfl
  map_smul' _c _v := rfl

theorem etaMap_apply (v : V) : etaMap V v = mkC (constSeq v) := rfl

/-- `⟪η a, η b⟫ = [a,b]`. -/
theorem inner_etaMap (a b : V) : (⟪etaMap V a, etaMap V b⟫ : ℂ) = ⟪a, b⟫ := by
  rw [etaMap_apply, etaMap_apply, inner_mkC]
  exact tendsto_nhds_unique (ipCau_tendsto (constSeq a) (constSeq b)) tendsto_const_nhds

/-- Solution parsec-300.50, item 6: `η` is an isometry. -/
theorem norm_etaMap (v : V) : ‖etaMap V v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_re_inner' (etaMap V v), inner_etaMap, ← norm_eq_sqrt_re_inner']

/-- Solution parsec-300.50, item 5: `η(a₁), η(a₂), …` converges to `(aₙ)ₙ`, so
`η(V)` is dense in the completion. -/
theorem denseRange_etaMap : DenseRange (etaMap V) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, rfl⟩ := mkC_surjective x
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 a.2 (ε / 2) (by positivity)
  refine ⟨etaMap V (a.1 N), Set.mem_range_self _, ?_⟩
  have hle : dist (mkC a : Cpl V) (etaMap V (a.1 N)) ≤ ε / 2 := by
    refine le_of_tendsto (dist_mkC_tendsto a (constSeq (a.1 N))) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := hN n hn N le_rfl
    rw [dist_eq_norm] at h
    exact h.le
  linarith

/-! #### Completeness: the printed diagonal-subsequence argument -/

omit [InnerProductSpace ℂ V] in
/-- Solution parsec-300.50, item 4, second WLOG: every Cauchy sequence has an
equivalent subsequence with `‖bₘ − b_M‖ ≤ 2^{-M}` for `m ≥ M`. -/
theorem exists_rapid {a : ℕ → V} (ha : CauchySeq a) :
    ∃ b : ℕ → V, CauchySeq b ∧ (∀ M m, M ≤ m → ‖b m - b M‖ ≤ (1 / 2 : ℝ) ^ M) ∧
      Tendsto (fun n => ‖a n - b n‖) atTop (𝓝 0) := by
  rw [Metric.cauchySeq_iff] at ha
  choose N hN using fun k : ℕ => ha ((1 / 2 : ℝ) ^ k) (by positivity)
  obtain ⟨M, hMs, hMN⟩ : ∃ M : ℕ → ℕ, (∀ j, M j + 1 ≤ M (j + 1)) ∧ (∀ k, N k ≤ M k) := by
    refine ⟨fun k => Nat.rec (motive := fun _ => ℕ) (N 0)
      (fun j ih => max (N (j + 1)) (ih + 1)) k, fun j => le_max_right _ _, fun k => ?_⟩
    cases k with
    | zero => exact le_rfl
    | succ j => exact le_max_left _ _
  have hMmono : Monotone M :=
    monotone_nat_of_le_succ (fun j => le_trans (Nat.le_succ _) (hMs j))
  have hMk : ∀ k, k ≤ M k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ j ih => exact le_trans (Nat.succ_le_succ ih) (hMs j)
  have hrap : ∀ K m, K ≤ m → ‖a (M m) - a (M K)‖ ≤ (1 / 2 : ℝ) ^ K := by
    intro K m hKm
    have h := hN K (M m) (le_trans (hMN K) (hMmono hKm)) (M K) (hMN K)
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨fun k => a (M k), ?_, hrap, ?_⟩
  · rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < ε / 2)
      (by norm_num : (1/2 : ℝ) < 1)
    refine ⟨K, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 := hrap K m hm
    have h2 := hrap K n hn
    have hsub := norm_sub_le (a (M m) - a (M K)) (a (M n) - a (M K))
    have heq : a (M m) - a (M K) - (a (M n) - a (M K)) = a (M m) - a (M n) := by abel
    rw [heq] at hsub
    linarith
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < ε)
      (by norm_num : (1/2 : ℝ) < 1)
    refine ⟨M K, fun n hn => ?_⟩
    have hKn : K ≤ n := le_trans (hMk K) hn
    have h := hN K n (le_trans (hMN K) hn) (M n) (le_trans (hMN K) (hMmono hKn))
    rw [dist_eq_norm] at h
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact lt_trans h hK

/-- Solution parsec-300.50, item 4: the completion is complete, by the printed
diagonal-subsequence argument. -/
instance complete_compl : CompleteSpace (Cpl V) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => by positivity) ?_
  intro u hu
  -- the printed second WLOG: rapidly-Cauchy representatives
  have hrep : ∀ n, ∃ b : ↥(cauSeqs V), mkC b = u n ∧
      ∀ K m, K ≤ m → ‖b.1 m - b.1 K‖ ≤ (1 / 2 : ℝ) ^ K := by
    intro n
    obtain ⟨a, ha⟩ := mkC_surjective (u n)
    obtain ⟨b, hbc, hbr, hab⟩ := exists_rapid a.2
    refine ⟨⟨b, hbc⟩, ?_, hbr⟩
    rw [← ha, mkC_eq_mkC]
    exact hab.congr (fun n => norm_sub_rev _ _)
  choose b hb hbr using hrep
  -- the printed estimate: ‖a_{ns} − a_{mt}‖ ≤ 3·2^{-N} for n,m,s,t ≥ N
  have key : ∀ N n m s t : ℕ, N ≤ n → N ≤ m → N ≤ s → N ≤ t →
      ‖(b n).1 s - (b m).1 t‖ ≤ 3 * (1 / 2 : ℝ) ^ N := by
    intro N n m s t hn hm hs ht
    have hlim := dist_mkC_tendsto (b n) (b m)
    rw [hb n, hb m] at hlim
    have hlt : dist (u n) (u m) < (1 / 2 : ℝ) ^ N := hu N n m hn hm
    have hev : ∀ᶠ k in atTop, ‖(b n).1 k - (b m).1 k‖ < (1 / 2 : ℝ) ^ N :=
      hlim.eventually_lt_const hlt
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ :=
      ((hev.and (eventually_ge_atTop s)).and (eventually_ge_atTop t)).exists
    have e1 : ‖(b n).1 s - (b n).1 k‖ ≤ (1 / 2 : ℝ) ^ N := by
      have h := hbr n s k hk2
      rw [← norm_neg, neg_sub] at h
      exact h.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hs)
    have e2 : ‖(b m).1 k - (b m).1 t‖ ≤ (1 / 2 : ℝ) ^ N := by
      have h := hbr m t k hk3
      exact h.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) ht)
    have htri : ‖(b n).1 s - (b m).1 t‖
        ≤ ‖(b n).1 s - (b n).1 k‖ + ‖(b n).1 k - (b m).1 k‖ + ‖(b m).1 k - (b m).1 t‖ := by
      have hd4 := dist_triangle4 ((b n).1 s) ((b n).1 k) ((b m).1 k) ((b m).1 t)
      simpa only [dist_eq_norm] using hd4
    linarith
  -- the printed diagonal sequence
  have hdiag : CauchySeq (fun n => (b n).1 n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < ε / 3)
      (by norm_num : (1/2 : ℝ) < 1)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hk := key N m n m n hm hn hm hn
    linarith
  refine ⟨mkC ⟨fun n => (b n).1 n, hdiag⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < ε / 3)
    (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨N, fun m hm => ?_⟩
  have hlim := dist_mkC_tendsto (b m) (⟨fun n => (b n).1 n, hdiag⟩ : ↥(cauSeqs V))
  rw [hb m] at hlim
  have hle : dist (u m) (mkC ⟨fun n => (b n).1 n, hdiag⟩) ≤ 3 * (1 / 2 : ℝ) ^ N := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    exact key N m k k k hm hk hk hk
  linarith

end

end InnerCompletion

/-! ### 30V: the extension clause -/

section DenseExtension

/-- Solution parsec-300.50, item 6, the general fact the exercise's extension
clause rests on: a uniformly continuous map `f` on a dense isometric copy of
`D` inside a metric space `W`, with values in a complete space `Y`, extends
uniquely to a uniformly continuous map on `W`.  The extension is the printed
`g(x) = limₙ f(dₙ)` for any `d` with `ι(dₙ) → x`, and its uniform continuity is
the printed three-term estimate. -/
theorem dense_uniform_extension {W : Type*} [PseudoMetricSpace W]
    {D : Type*} [PseudoMetricSpace D] (ι : D → W)
    (hiso : ∀ x y : D, dist (ι x) (ι y) = dist x y) (hdense : DenseRange ι)
    {Y : Type*} [UniformSpace Y] [T0Space Y] [CompleteSpace Y]
    (f : D → Y) (hf : UniformContinuous f) :
    ∃! g : W → Y, UniformContinuous g ∧ ∀ d : D, g (ι d) = f d := by
  -- for each `x` an approximating sequence in `D`
  have hseq : ∀ x : W, ∃ d : ℕ → D, Tendsto (fun n => ι (d n)) atTop (𝓝 x) := by
    intro x
    have hex : ∀ k : ℕ, ∃ y : D, dist x (ι y) < 1 / (k + 1) := by
      intro k
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
        Metric.mem_closure_iff.1 (hdense x) (1 / (k + 1)) (by positivity)
      exact ⟨y, hy⟩
    choose d hd using hex
    refine ⟨d, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨K, fun n hn => ?_⟩
    have h := hd n
    rw [dist_comm] at h
    refine lt_of_lt_of_le h (le_trans ?_ hK.le)
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  choose d hd using hseq
  -- `f(dₙ)` is Cauchy, hence converges in the complete space `Y`
  have hconv : ∀ x : W, ∃ y : Y, Tendsto (fun n => f (d x n)) atTop (𝓝 y) := by
    intro x
    refine cauchySeq_tendsto_of_complete (hf.comp_cauchySeq ?_)
    have h1 : CauchySeq (fun n => ι (d x n)) := (hd x).cauchySeq
    rw [Metric.cauchySeq_iff] at h1 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h1 ε hε
    exact ⟨N, fun m hm n hn => by rw [← hiso]; exact hN m hm n hn⟩
  choose g hg using hconv
  -- `g` extends `f`
  have hgext : ∀ a : D, g (ι a) = f a := by
    intro a
    refine tendsto_nhds_unique (hg (ι a)) ?_
    have hda : Tendsto (fun n => d (ι a) n) atTop (𝓝 a) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hd (ι a)) ε hε
      exact ⟨N, fun n hn => by rw [← hiso]; exact hN n hn⟩
    exact (hf.continuous.tendsto a).comp hda
  -- `g` is uniformly continuous, by the printed three-term estimate
  have hgu : UniformContinuous g := by
    rw [Metric.uniformity_basis_dist.uniformContinuous_iff (uniformity Y).basis_sets]
    intro S hS
    obtain ⟨T, hT, hTsymm, hTsub⟩ := comp_comp_symm_mem_uniformity_sets hS
    obtain ⟨δ, hδ, hδf⟩ :=
      (Metric.uniformity_basis_dist.uniformContinuous_iff (uniformity Y).basis_sets).1 hf T hT
    refine ⟨δ / 3, by positivity, fun x y hxy => ?_⟩
    have e1 : ∀ᶠ n in atTop, (g x, f (d x n)) ∈ T :=
      (hg x).eventually (UniformSpace.ball_mem_nhds _ hT)
    have e2 : ∀ᶠ n in atTop, (g y, f (d y n)) ∈ T :=
      (hg y).eventually (UniformSpace.ball_mem_nhds _ hT)
    have e3 : ∀ᶠ n in atTop, dist (ι (d x n)) x < δ / 3 := by
      have h := (hd x).eventually (Metric.ball_mem_nhds x (by positivity : (0:ℝ) < δ / 3))
      simpa [Metric.mem_ball] using h
    have e4 : ∀ᶠ n in atTop, dist (ι (d y n)) y < δ / 3 := by
      have h := (hd y).eventually (Metric.ball_mem_nhds y (by positivity : (0:ℝ) < δ / 3))
      simpa [Metric.mem_ball] using h
    obtain ⟨k, ⟨hk1, hk2⟩, hk3, hk4⟩ := ((e1.and e2).and (e3.and e4)).exists
    have hmem : dist x y < δ / 3 := hxy
    have hdd : dist (d x k) (d y k) < δ := by
      rw [← hiso]
      have htri := dist_triangle4 (ι (d x k)) x y (ι (d y k))
      have hy' : dist y (ι (d y k)) < δ / 3 := by rw [dist_comm]; exact hk4
      linarith
    have hmid : (f (d x k), f (d y k)) ∈ T := hδf _ _ hdd
    have hlast : (f (d y k), g y) ∈ T := SetRel.symm T hk2
    exact hTsub (SetRel.prodMk_mem_comp (SetRel.prodMk_mem_comp hk1 hmid) hlast)
  refine ⟨g, ⟨hgu, hgext⟩, ?_⟩
  rintro g' ⟨hg'u, hg'ext⟩
  refine hdense.equalizer hg'u.continuous hgu.continuous ?_
  funext a
  simp only [Function.comp_apply, hg'ext, hgext]

/-- Solution parsec-300.50, last item, in the form both the exercise's own
extension clause and **30VI**'s `ϱ_ω` need it: a bounded linear map `f` on a
dense isometric copy `ι(D)` of `D` inside `W`, with values in a Banach space
`K`, extends *uniquely* to a bounded linear map on `W`.

The printed argument: the uniformly continuous extension `g` is the one
`dense_uniform_extension` supplies, and the equations `g(x+y) = g x + g y`,
`g(r·x) = r·g x` and the inequality `‖g x‖ ≤ ‖f‖‖x‖` hold on the dense set
`ι(D)` — because `f` is linear and bounded — with both sides continuous, so
they hold on all of `W`.  Uniqueness is again density.

`D` is only *semi*normed, which is what **30VI** needs: `[·,·]_ω` is in
general degenerate, so `𝒜` under `‖·‖_ω` is a seminormed space. -/
theorem dense_linear_extension {D : Type*} [SeminormedAddCommGroup D] [NormedSpace ℂ D]
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace ℂ W] (ι : D →ₗᵢ[ℂ] W)
    (hdense : DenseRange ι)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (f : D →L[ℂ] K) :
    ∃! g : W →L[ℂ] K, ∀ v : D, g (ι v) = f v := by
  have hiso : ∀ x y : D, dist (ι x) (ι y) = dist x y := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ι.norm_map]
  obtain ⟨g₀, ⟨hg₀u, hg₀e⟩, -⟩ :=
    dense_uniform_extension (fun v : D => ι v) hiso hdense (⇑f) f.lipschitz.uniformContinuous
  have hadd1 : ∀ (v : D) (y : W), g₀ (ι v + y) = g₀ (ι v) + g₀ y := by
    intro v
    refine congrFun (hdense.equalizer
      (g := fun y => g₀ (ι v + y)) (h := fun y => g₀ (ι v) + g₀ y)
      (hg₀u.continuous.comp (continuous_const.add continuous_id))
      (continuous_const.add hg₀u.continuous) ?_)
    funext w
    simp only [Function.comp_apply]
    rw [← map_add ι, hg₀e, hg₀e, hg₀e, map_add]
  have hadd : ∀ x y : W, g₀ (x + y) = g₀ x + g₀ y := by
    intro x y
    refine congrFun (hdense.equalizer
      (g := fun x => g₀ (x + y)) (h := fun x => g₀ x + g₀ y)
      (hg₀u.continuous.comp (continuous_id.add continuous_const))
      (hg₀u.continuous.add continuous_const) ?_) x
    funext v
    simp only [Function.comp_apply]
    exact hadd1 v y
  have hsmul : ∀ (r : ℂ) (x : W), g₀ (r • x) = r • g₀ x := by
    intro r
    refine congrFun (hdense.equalizer
      (g := fun x => g₀ (r • x)) (h := fun x => r • g₀ x)
      (hg₀u.continuous.comp (continuous_const_smul r))
      ((continuous_const_smul r).comp hg₀u.continuous) ?_)
    funext v
    simp only [Function.comp_apply]
    rw [← map_smul ι, hg₀e, hg₀e, map_smul]
  have hbd : ∀ x : W, ‖g₀ x‖ ≤ ‖f‖ * ‖x‖ := by
    have hcl : IsClosed {x : W | ‖g₀ x‖ ≤ ‖f‖ * ‖x‖} :=
      isClosed_le (continuous_norm.comp hg₀u.continuous) (continuous_const.mul continuous_norm)
    have hsub : Set.range (fun v : D => ι v) ⊆ {x : W | ‖g₀ x‖ ≤ ‖f‖ * ‖x‖} := by
      rintro _ ⟨v, rfl⟩
      simp only [Set.mem_ofPred_eq, hg₀e v, ι.norm_map]
      exact f.le_opNorm v
    have h := hcl.closure_subset_iff.2 hsub
    rw [hdense.closure_range] at h
    exact fun x => h (Set.mem_univ x)
  let gL : W →ₗ[ℂ] K :=
    { toFun := g₀, map_add' := hadd, map_smul' := fun r x => hsmul r x }
  refine ⟨gL.mkContinuous ‖f‖ hbd, fun v => hg₀e v, ?_⟩
  intro g' hg'
  have heq : (g' : W → K) = g₀ := by
    refine hdense.equalizer g'.continuous hg₀u.continuous ?_
    funext v
    simp only [Function.comp_apply]
    rw [hg' v, hg₀e v]
  ext x
  exact congrFun heq x

end DenseExtension

section InnerProductCompletionClauses

open InnerCompletion

/-- **30V** (`inner-product-completion`, cstar.tex:4840, Exercise), the
headline: every complex inner product space `V` can be completed to a Hilbert
space `H` in which it embeds densely.

The Hilbert space is the exercise's own, built above from solution
parsec-300.50: `InnerCompletion.Cpl V`, the Cauchy sequences on `V` modulo
`lim ‖aₙ − bₙ‖ = 0`, with `η = InnerCompletion.etaMap` sending `a` to the
constant sequence `a, a, a, …`.  Its distance is the printed
`d((aₙ)ₙ,(bₙ)ₙ) = lim ‖aₙ − bₙ‖`, its completeness is the printed
diagonal-subsequence argument, and `η` is a dense isometry.  Mathlib's
`UniformSpace.Completion` is not used.

The exercise's two *extension* clauses, which are what it is used for, are
`inner_product_completion_extension` and `inner_product_completion_extendL`
below; the second is what **30VI**'s `ϱ_ω` needs.  The exercise states the
headline for a *possibly degenerate* inner product, where `η` need not be
injective; that is `inner_product_completion_degenerate`, immediately
below. -/
theorem inner_product_completion (V : Type v) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] :
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (e : V →ₗᵢ[ℂ] H), DenseRange e :=
  ⟨Cpl V, inferInstance, inferInstance, inferInstance,
    ⟨etaMap V, norm_etaMap⟩, denseRange_etaMap⟩

section DegenerateInner

-- The inner product of a possibly degenerate `PreInnerProductSpace.Core`,
-- written `⟪·,·⟫`, as in **4XV** (`A/CStar/Basic`).
attribute [local instance] InnerProductSpace.Core.toPreInner'

/-- **30V** (`inner-product-completion`, cstar.tex:4840, Exercise), the
headline for a possibly *degenerate* inner product — which is how the
exercise states it: "note, however, that `η` need not be injective: show that
`η(a) = η(b)` iff `‖a−b‖ = 0` for all `a,b ∈ V`".  So `V` carries only a
`PreInnerProductSpace.Core ℂ V`, the setting of **4XV**, where
`‖x‖ = innerNorm x = √⟪x,x⟫` is a *seminorm* and need not be a norm.  The
completion `ℋ` is still a Hilbert space, `η : V → ℋ` is still linear with
`⟪η a, η b⟫ = [a,b]` and dense image — and `η` collapses exactly the
seminorm-zero differences.

Nothing has to be added for the degenerate case: `InnerCompletion.Cpl V` is
built above for a *seminormed* `V`, and the collapse of `η` is the printed
one — `η a = η b` says that the constant sequence `a−b, a−b, …` is null,
i.e. that `‖a−b‖ = 0` (solution parsec-300.50, item 1).

For a definite inner product this is `inner_product_completion` above (where
`η` is then an isometric *embedding*); the two extension clauses are
`inner_product_completion_extension` and `inner_product_completion_extendL`
below. -/
theorem inner_product_completion_degenerate (V : Type v) [AddCommGroup V] [Module ℂ V]
    [c : PreInnerProductSpace.Core ℂ V] :
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (η : V →ₗ[ℂ] H),
      (∀ a b : V, (⟪η a, η b⟫ : ℂ) = ⟪a, b⟫) ∧ DenseRange η ∧
      (∀ a b : V, η a = η b ↔ innerNorm (a - b) = 0) := by
  let _ : SeminormedAddCommGroup V :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := V) (c := c)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c
  refine ⟨Cpl V, inferInstance, inferInstance, inferInstance, etaMap V,
    fun a b => inner_etaMap a b, denseRange_etaMap, fun a b => ?_⟩
  -- `η a = η b` iff the constant sequence `a−b` is null iff `‖a−b‖ = 0`
  have hnorm : ∀ x : V, ‖x‖ = innerNorm x := fun x => rfl
  rw [etaMap_apply, etaMap_apply, ← sub_eq_zero, ← mkC_sub]
  have hsub : constSeq a - constSeq b = constSeq (a - b) := rfl
  rw [hsub, mkC_eq_zero, ← hnorm]
  constructor
  · intro h
    exact (tendsto_nhds_unique h tendsto_const_nhds).symm
  · intro h
    rw [show (fun _ : ℕ => ‖(constSeq (a - b) : ↥(cauSeqs V)).1 _‖) = fun _ : ℕ => ‖a - b‖ from rfl,
      h]
    exact tendsto_const_nhds

end DegenerateInner

/-- **30V** (`inner-product-completion`, cstar.tex:4840, Exercise), the
uniform-extension clause: every uniformly continuous map `f : V → X` into a
complete space extends *uniquely* to a uniformly continuous map on the
completion `H` of `V` (where "`g` extends `f`" means `f = g ∘ η`).

The statement names Mathlib's `UniformSpace.Completion V` as the carrier of
`H`, but nothing of its extension API is used: the extension is the printed
`g(x) = limₙ f(dₙ)` of solution parsec-300.50, item 6, proved for a dense
isometric copy of `V` in any metric space as `dense_uniform_extension`
above. -/
theorem inner_product_completion_extension (V : Type v) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {X : Type*} [UniformSpace X] [T0Space X]
    [CompleteSpace X] (f : V → X) (hf : UniformContinuous f) :
    ∃! g : UniformSpace.Completion V → X,
      UniformContinuous g ∧ ∀ v : V, g (v : UniformSpace.Completion V) = f v :=
  dense_uniform_extension (fun v : V => (v : UniformSpace.Completion V))
    (fun x y => UniformSpace.Completion.dist_eq x y)
    UniformSpace.Completion.denseRange_coe f hf

/-- **30V** (`inner-product-completion`, cstar.tex:4840, Exercise), the final
clause: every bounded linear map `f : V → K` into a Hilbert space `K` extends
*uniquely* to a bounded linear map on the completion `H` of `V`.

This is the clause **30VI** uses to build `ϱ_ω(a)` from `b ↦ ab`.  It is the
printed argument of solution parsec-300.50, last item: the uniformly
continuous extension `g` comes from `dense_uniform_extension`, and it is
linear and bounded because those equations and that inequality hold on the
dense image of `V` and both sides are continuous.  Mathlib's
`ContinuousLinearMap.extend` is not used.  That argument is carried by
`dense_linear_extension` above, which runs it for an arbitrary dense isometric
copy — as **30VI** needs, since `𝒜` under `‖·‖_ω` is only seminormed. -/
theorem inner_product_completion_extendL (V : Type v) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (f : V →L[ℂ] K) :
    ∃! g : UniformSpace.Completion V →L[ℂ] K,
      ∀ v : V, g (v : UniformSpace.Completion V) = f v :=
  dense_linear_extension UniformSpace.Completion.toComplₗᵢ
    UniformSpace.Completion.denseRange_coe f

end InnerProductCompletionClauses

/-! ### **30VI**–**30VIII**: the GNS representation `ϱ_ω`

**30VI** (`gns`, cstar.tex:4886, Definition (Gelfand–Naimark–Segal
construction)): for a p-map `ω : 𝒜 → ℂ`, the Hilbert space `ℋ_ω` is the
completion of `𝒜` under `[·,·]_ω` (**30II**), with embedding
`η_ω : 𝒜 → ℋ_ω`, and `ϱ_ω(a) : ℋ_ω → ℋ_ω` is the *unique* bounded linear map
with `ϱ_ω(a) η_ω(b) = η_ω(ab)`, obtained from the extension clause of **30V**
because `b ↦ ab` is bounded for `‖·‖_ω` by **30IV**.2 (`omega-norm-basic`).

The carrier is Mathlib's (`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`):
for `ω : 𝒜 →ₚ[ℂ] ℂ`, `ω.PreGNS` is `𝒜` with the `[·,·]_ω` inner product —
seminormed, since `[·,·]_ω` is in general degenerate — and `ℋ_ω = ω.GNS` its
completion, with `η_ω(b)` the coercion of `ω.toPreGNS b`.  Everything on top
of that carrier is the thesis's: `gnsRho` is `ϱ_ω`, built by
`dense_linear_extension` (**30V**) exactly as **30VI** builds it, and
`gnsRhoHom` is **30VII** with **30VIII**'s four-part proof transcribed.
`gnsStarAlgHom_eq_gnsRho` then identifies Mathlib's `ω.gnsStarAlgHom` with it,
by the uniqueness half of the same clause of **30V**. -/

section GNSRepresentation

open PositiveLinearMap

omit [StarOrderedRing 𝒜] in
/-- A p-map bundled as Mathlib's `𝒜 →ₚ[ℂ] ℂ` is positive in the sense of
**10II**.5, which is the form **30IV** is stated in. -/
private theorem gnsPos (ω : 𝒜 →ₚ[ℂ] ℂ) : IsPositiveMap ω.toLinearMap :=
  fun _ ha => ω.map_nonneg ha

/-- `ω.PreGNS` carries exactly the seminorm `‖·‖_ω` of **30IV**. -/
private theorem norm_preGNS (ω : 𝒜 →ₚ[ℂ] ℂ) (x : ω.PreGNS) :
    ‖x‖ = omegaSeminorm ω.toLinearMap (ω.ofPreGNS x) := by
  simp [PositiveLinearMap.preGNS_norm_def, omegaSeminorm]

/-- `‖η_ω(x)‖ = ‖x‖_ω`: `η_ω` is the isometry of **30V**. -/
private theorem norm_gnsEta (ω : 𝒜 →ₚ[ℂ] ℂ) (x : 𝒜) :
    ‖((ω.toPreGNS x : ω.PreGNS) : ω.GNS)‖ = omegaSeminorm ω.toLinearMap x := by
  rw [UniformSpace.Completion.norm_coe]
  simp [PositiveLinearMap.preGNS_norm_def, omegaSeminorm]

/-- `{η_ω(b) : b ∈ 𝒜}` is dense in `ℋ_ω` — the fact **30VIII** uses four
times. -/
private theorem denseRange_gnsEta (ω : 𝒜 →ₚ[ℂ] ℂ) :
    DenseRange (fun b : 𝒜 => ((ω.toPreGNS b : ω.PreGNS) : ω.GNS)) := by
  have hsurj : Function.Surjective (fun b : 𝒜 => (ω.toPreGNS b : ω.PreGNS)) :=
    ω.toPreGNS.surjective
  simpa [DenseRange, Set.range_comp'] using
    (UniformSpace.Completion.denseRange_coe (α := ω.PreGNS))

/-- **30VI**'s `b ↦ ab`, `𝒜 → ℋ_ω`, bounded by `‖a‖`: that is **30IV**.2,
`‖ab‖_ω ≤ ‖a‖‖b‖_ω`, which is the reason the Definition gives. -/
private noncomputable def gnsLeftMul (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) : ω.PreGNS →L[ℂ] ω.GNS :=
  LinearMap.mkContinuous
    (((UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := ω.PreGNS)).toLinearMap.comp
        ω.toPreGNS.toLinearMap).comp
      ((LinearMap.mulLeft ℂ a).comp ω.ofPreGNS.toLinearMap))
    ‖a‖ (by
      intro x
      show ‖((ω.toPreGNS (a * ω.ofPreGNS x) : ω.PreGNS) : ω.GNS)‖ ≤ ‖a‖ * ‖x‖
      rw [norm_gnsEta, norm_preGNS]
      exact omega_norm_basic_2 ω.toLinearMap (gnsPos ω) a (ω.ofPreGNS x))

private theorem gnsLeftMul_apply (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) (x : ω.PreGNS) :
    gnsLeftMul ω a x = ((ω.toPreGNS (a * ω.ofPreGNS x) : ω.PreGNS) : ω.GNS) := rfl

/-- The extension clause of **30V** applied to `b ↦ ab`, which is how **30VI**
defines `ϱ_ω(a)`. -/
private theorem gnsExtSpec (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) :
    ∃! g : ω.GNS →L[ℂ] ω.GNS, ∀ v : ω.PreGNS,
      g ((UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := ω.PreGNS)) v) = gnsLeftMul ω a v :=
  dense_linear_extension _ UniformSpace.Completion.denseRange_coe (gnsLeftMul ω a)

/-- **30VI** (`gns`, cstar.tex:4886): `ϱ_ω(a)`, the unique bounded linear map
`ℋ_ω → ℋ_ω` extending `b ↦ ab`.  Built as the Definition builds it: the map
`b ↦ ab` is bounded for `‖·‖_ω` by **30IV**.2, so the extension clause of
**30V** (`dense_linear_extension`) supplies it. -/
noncomputable def gnsRho (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) : ω.GNS →L[ℂ] ω.GNS :=
  (gnsExtSpec ω a).choose

/-- The defining property of **30VI**'s `ϱ_ω(a)`: `ϱ_ω(a) η_ω(b) = η_ω(ab)`. -/
theorem gnsRho_apply_eta (ω : 𝒜 →ₚ[ℂ] ℂ) (a b : 𝒜) :
    gnsRho ω a ((ω.toPreGNS b : ω.PreGNS) : ω.GNS)
      = ((ω.toPreGNS (a * b) : ω.PreGNS) : ω.GNS) := by
  have h := (gnsExtSpec ω a).choose_spec.1 (ω.toPreGNS b)
  simpa [gnsRho, gnsLeftMul_apply] using h

/-- The other half of **30VI**'s "*the unique* bounded linear map with
`ϱ_ω(a) η_ω(b) = η_ω(ab)`". -/
theorem gnsRho_unique (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) (g : ω.GNS →L[ℂ] ω.GNS)
    (hg : ∀ b : 𝒜, g ((ω.toPreGNS b : ω.PreGNS) : ω.GNS)
      = ((ω.toPreGNS (a * b) : ω.PreGNS) : ω.GNS)) :
    g = gnsRho ω a := by
  refine (gnsExtSpec ω a).choose_spec.2 g ?_
  intro v
  have := hg (ω.ofPreGNS v)
  simpa [gnsLeftMul_apply] using this

/-- Two bounded operators on `ℋ_ω` agreeing on every `η_ω(b)` are equal —
"and `{η_ω(b) : b ∈ 𝒜}` is dense in `ℋ_ω`", the step **30VIII** takes after
each of its computations. -/
private theorem gns_ext {ω : 𝒜 →ₚ[ℂ] ℂ} {S T : ω.GNS →L[ℂ] ω.GNS}
    (h : ∀ b : 𝒜, S ((ω.toPreGNS b : ω.PreGNS) : ω.GNS)
      = T ((ω.toPreGNS b : ω.PreGNS) : ω.GNS)) : S = T := by
  have := (denseRange_gnsEta ω).equalizer S.continuous T.continuous (funext h)
  ext x
  exact congrFun this x

private theorem gnsEta_add (ω : 𝒜 →ₚ[ℂ] ℂ) (x y : 𝒜) :
    ((ω.toPreGNS (x + y) : ω.PreGNS) : ω.GNS)
      = ((ω.toPreGNS x : ω.PreGNS) : ω.GNS) + ((ω.toPreGNS y : ω.PreGNS) : ω.GNS) := by
  rw [map_add, UniformSpace.Completion.coe_add]

private theorem gnsEta_smul (ω : 𝒜 →ₚ[ℂ] ℂ) (r : ℂ) (x : 𝒜) :
    ((ω.toPreGNS (r • x) : ω.PreGNS) : ω.GNS)
      = r • ((ω.toPreGNS x : ω.PreGNS) : ω.GNS) := by
  rw [map_smul, UniformSpace.Completion.coe_smul]

/-- **30VIII**, first paragraph: "`ϱ_ω(a₁+a₂) η_ω(b) = η_ω((a₁+a₂)b) =
η_ω(a₁b) + η_ω(a₂b) = (ϱ_ω(a₁)+ϱ_ω(a₂)) η_ω(b)` for all `b ∈ 𝒜`, and
`{η_ω(b) : b ∈ 𝒜}` is dense in `ℋ_ω`". -/
theorem gnsRho_add (ω : 𝒜 →ₚ[ℂ] ℂ) (a₁ a₂ : 𝒜) :
    gnsRho ω (a₁ + a₂) = gnsRho ω a₁ + gnsRho ω a₂ :=
  gns_ext fun b => by
    rw [gnsRho_apply_eta, add_mul, gnsEta_add, _root_.add_apply,
      gnsRho_apply_eta, gnsRho_apply_eta]

/-- **30VIII**, first paragraph, "since similarly `ϱ_ω(λa) = λ ϱ_ω(a)`". -/
theorem gnsRho_smul (ω : 𝒜 →ₚ[ℂ] ℂ) (r : ℂ) (a : 𝒜) :
    gnsRho ω (r • a) = r • gnsRho ω a :=
  gns_ext fun b => by
    rw [gnsRho_apply_eta, smul_mul_assoc, gnsEta_smul, smul_apply, gnsRho_apply_eta]

/-- **30VIII**, second paragraph: "since `ϱ_ω(1) η_ω(b) = η_ω(b)` for all
`b ∈ 𝒜`, we have `ϱ_ω(1) x = x` for all `x ∈ ℋ_ω`". -/
theorem gnsRho_one (ω : 𝒜 →ₚ[ℂ] ℂ) : gnsRho ω 1 = 1 :=
  gns_ext fun b => by rw [gnsRho_apply_eta, one_mul, one_apply_eq_self]

/-- **30VIII**, third paragraph: "`(ϱ_ω(a₁) ϱ_ω(a₂)) η_ω(b) = η_ω(a₁a₂b) =
ϱ_ω(a₁a₂) η_ω(b)` for all `a₁,a₂,b ∈ 𝒜`". -/
theorem gnsRho_mul (ω : 𝒜 →ₚ[ℂ] ℂ) (a₁ a₂ : 𝒜) :
    gnsRho ω (a₁ * a₂) = gnsRho ω a₁ * gnsRho ω a₂ :=
  gns_ext fun b => by
    rw [gnsRho_apply_eta, mul_apply_eq_comp, gnsRho_apply_eta, gnsRho_apply_eta, mul_assoc]

/-- **30VIII**, last paragraph: to see that `ϱ_ω` preserves the involution it
suffices to prove that `ϱ_ω(a*)` is the adjoint of `ϱ_ω(a)`, and
`⟨ϱ_ω(a*) η_ω(b), η_ω(c)⟩ ≡ [a*b,c]_ω = ω(b*ac) = [b,ac]_ω ≡
⟨η_ω(b), ϱ_ω(a) η_ω(c)⟩` for all `b,c ∈ 𝒜`, whence — `{η_ω(b)}` being dense —
`⟨ϱ_ω(a*)x, y⟩ = ⟨x, ϱ_ω(a)y⟩` for all `x,y ∈ ℋ_ω`.  The density step is taken
once in each argument. -/
theorem gnsRho_star (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) :
    gnsRho ω (star a) = star (gnsRho ω a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
  have base : ∀ b c : 𝒜,
      (⟪gnsRho ω (star a) ((ω.toPreGNS b : ω.PreGNS) : ω.GNS),
        ((ω.toPreGNS c : ω.PreGNS) : ω.GNS)⟫ : ℂ)
      = ⟪((ω.toPreGNS b : ω.PreGNS) : ω.GNS),
        gnsRho ω a ((ω.toPreGNS c : ω.PreGNS) : ω.GNS)⟫ := by
    intro b c
    rw [gnsRho_apply_eta, gnsRho_apply_eta, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.preGNS_inner_def, ofPreGNS_toPreGNS, ofPreGNS_toPreGNS,
      ofPreGNS_toPreGNS, ofPreGNS_toPreGNS, star_mul, star_star, mul_assoc]
  have step1 : ∀ (b : 𝒜) (y : ω.GNS),
      (⟪gnsRho ω (star a) ((ω.toPreGNS b : ω.PreGNS) : ω.GNS), y⟫ : ℂ)
      = ⟪((ω.toPreGNS b : ω.PreGNS) : ω.GNS), gnsRho ω a y⟫ := by
    intro b
    refine congrFun ((denseRange_gnsEta ω).equalizer
      (g := fun y => (⟪gnsRho ω (star a) ((ω.toPreGNS b : ω.PreGNS) : ω.GNS), y⟫ : ℂ))
      (h := fun y => (⟪((ω.toPreGNS b : ω.PreGNS) : ω.GNS), gnsRho ω a y⟫ : ℂ))
      (continuous_inner.comp (continuous_const.prodMk continuous_id))
      (continuous_inner.comp (continuous_const.prodMk (gnsRho ω a).continuous)) ?_)
    funext c
    exact base b c
  intro x y
  refine congrFun ((denseRange_gnsEta ω).equalizer
    (g := fun x => (⟪gnsRho ω (star a) x, y⟫ : ℂ))
    (h := fun x => (⟪x, gnsRho ω a y⟫ : ℂ))
    (continuous_inner.comp ((gnsRho ω (star a)).continuous.prodMk continuous_const))
    (continuous_inner.comp (continuous_id.prodMk continuous_const)) ?_) x
  funext b
  exact step1 b y

/-- **30VII** (cstar.tex:4919, Proposition): `ϱ_ω : 𝒜 → B(ℋ_ω)` is an
miu-map.  The four clauses are **30VIII**'s, `gnsRho_add`/`gnsRho_smul`
(linear), `gnsRho_one` (unital), `gnsRho_mul` (multiplicative) and
`gnsRho_star` (involution preserving). -/
noncomputable def gnsRhoHom (ω : 𝒜 →ₚ[ℂ] ℂ) : 𝒜 →⋆ₐ[ℂ] (ω.GNS →L[ℂ] ω.GNS) where
  toFun := gnsRho ω
  map_one' := gnsRho_one ω
  map_mul' := gnsRho_mul ω
  map_zero' := by simpa using gnsRho_smul ω 0 0
  map_add' := gnsRho_add ω
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, gnsRho_smul, gnsRho_one]
  map_star' := gnsRho_star ω

@[simp] theorem gnsRhoHom_apply (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) : gnsRhoHom ω a = gnsRho ω a := rfl

/-- Mathlib's `ω.gnsStarAlgHom` is the thesis's `ϱ_ω`.  Mathlib builds it by
extending the same `b ↦ ab` over the same completion, so this is the
uniqueness half of **30V**'s extension clause (`gnsRho_unique`) applied to it:
the two bounded linear maps agree on `η_ω(𝒜)`. -/
theorem gnsStarAlgHom_eq_gnsRho (ω : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜) :
    ω.gnsStarAlgHom a = gnsRho ω a :=
  gnsRho_unique ω a _ fun b => by simp [PositiveLinearMap.gnsStarAlgHom]

end GNSRepresentation

/-- **30VII** (cstar.tex:4919, Proposition): `ϱ_ω : 𝒜 → B(ℋ_ω)` is an
miu-map.  The Proposition itself is `gnsRhoHom` above, whose **30VIII** proof
is transcribed there; what is recorded here is the defining property
`ϱ_ω(a) η_ω(b) = η_ω(ab)` of **30VI**, for the `ϱ_ω` Mathlib bundles.

*Class 1 — faithful.*  The proof is the thesis's own `ϱ_ω`: `gnsRho ω a` is
the extension of `b ↦ ab` given by **30V**, `gnsRho_apply_eta` is **30VI**'s
defining identity for it, and `gnsStarAlgHom_eq_gnsRho` identifies Mathlib's
`ω.gnsStarAlgHom a` with it by the uniqueness half of the same clause. -/
theorem gns_starAlgHom_apply (ω : 𝒜 →ₚ[ℂ] ℂ) (a b : 𝒜) :
    ω.gnsStarAlgHom a ((ω.toPreGNS b : ω.PreGNS) : ω.GNS) =
      ((ω.toPreGNS (a * b) : ω.PreGNS) : ω.GNS) := by
  rw [gnsStarAlgHom_eq_gnsRho, gnsRho_apply_eta]

/-! **30IX** (`gelfand-naimark-representation`, cstar.tex:4966, Definition):
given a collection `Ω` of p-maps on `𝒜`, the representation
`ϱ_Ω : 𝒜 → B(⊕_{ω∈Ω} ℋ_ω)`, `ϱ_Ω(a) x = (ϱ_ω(a) x(ω))_ω`.  It *is*
constructed below, as `dsumRep`, and both halves of **30X** run through it,
as the Proposition's proof does; **30X**.2 and **30XIV** additionally state
their conclusion existentially. -/

variable (𝒜) in
/-- The map `a ↦ b* a b` as a linear map (used to express condition 3 of
**30X**). -/
noncomputable def conjMap (b : 𝒜) : 𝒜 →ₗ[ℂ] 𝒜 :=
  (LinearMap.mulLeft ℂ (star b)).comp (LinearMap.mulRight ℂ b)

/-- **29IX** (`injective-miu-iso-on-image`) in the form **30X**'s proof uses
it: an injective miu-map *reflects* positivity.  The thesis puts it as "`ϱ_Ω`
restricts to an miu-isomorphism from `𝒜` to `ϱ_Ω(𝒜)`, so in order to prove
that `a ≥ 0` it suffices to show that `ϱ_Ω(a) ≥ 0`" (cstar.tex:5024).

*Class 1 — faithful.*  That is the route taken: `injective_miu_iso_on_image_isomorphism`
(**29IX**) gives the C*-subalgebra `S = ρ(𝒜)` of `ℬ` and the miu-isomorphism
`e : 𝒜 ≅ S` with `↑(e x) = ρ x`, so `spec(x) = spec(e x)` (an algebra
isomorphism preserves the spectrum) `= spec(ρ x)` (spectral permanence for
the *closed* ⋆-subalgebra `S`, which is what the "C*-subalgebra" half of
**29IX** is for), and positivity of a self-adjoint element is a property of
its spectrum, **17V**.3.  (`A/CStar/Positive.lean` has an auxiliary of the
same statement for **20aII**, but private.) -/
private theorem nonneg_of_injective_miu {ℬ : Type*} [CStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) (x : 𝒜) (h : 0 ≤ ρ x) : 0 ≤ x := by
  have hisa : IsSelfAdjoint (ρ x) := IsSelfAdjoint.of_nonneg h
  have hsa : IsSelfAdjoint x := hρ (by rw [map_star, hisa.star_eq])
  obtain ⟨S, -, hSclosed, e, he⟩ := injective_miu_iso_on_image_isomorphism ρ hρ
  have : IsClosed (S : Set ℬ) := hSclosed
  have hspec : spectrum ℂ (ρ x) = spectrum ℂ x := by
    rw [← he x]
    exact (StarSubalgebra.spectrum_eq S (a := e x)).symm.trans
      (AlgEquiv.spectrum_eq e.toAlgEquiv x)
  have h3 := ((cstar_positive_tfae (ρ x) hisa).out 3 2).mp h
  rw [hspec] at h3
  exact ((cstar_positive_tfae x hsa).out 2 3).mp h3

/-- `0 ≤ T` in `B(H)` gives `0 ≤ ⟨y, T y⟩` for *every* `y` — **25III**'s easy
half, without the normalisation `‖y‖ = 1` that `OrderSeparating` carries. -/
private theorem inner_nonneg_of_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hT : 0 ≤ T) (y : H) :
    (0 : ℂ) ≤ ⟪y, T y⟫ := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  rw [hS]
  simp only [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K]
  positivity

open PositiveLinearMap in
/-- The step of **30X**'s proof at cstar.tex:5030–5044: `ϱ_ω(a)` is positive
as soon as `ω(b* a b) ≥ 0` for every `b`.

"Since the vector states on `ℋ_ω` are order separating by **30XIII**, it
suffices to show that `⟨x, ϱ_ω(a)x⟩ ≥ 0` for given `x ∈ ℋ_ω`.  Since
`{η_ω(b) : b ∈ 𝒜}` is dense in `ℋ_ω`, we only need to prove that
`0 ≤ ⟨η_ω(b), ϱ_ω(a) η_ω(b)⟩ ≡ ω(b* a b)` for given `b ∈ 𝒜`, but this is true
by assumption." -/
private theorem gnsStarAlgHom_nonneg (f : 𝒜 →ₚ[ℂ] ℂ) (a : 𝒜)
    (h : ∀ b : 𝒜, (0 : ℂ) ≤ f (star b * a * b)) : 0 ≤ f.gnsStarAlgHom a := by
  set T : f.GNS →L[ℂ] f.GNS := f.gnsStarAlgHom a with hT
  -- `{x : 0 ≤ ⟨x, T x⟩}` is closed …
  have hclosed : IsClosed {x : f.GNS | (0 : ℂ) ≤ ⟪x, T x⟫} := by
    have hcont : Continuous fun x : f.GNS => (⟪x, T x⟫ : ℂ) :=
      continuous_inner.comp (continuous_id.prodMk T.continuous)
    exact isClosed_le continuous_const hcont
  -- … and contains every `η_ω(b)`, where `⟨η_ω(b), T η_ω(b)⟩ = ω(b* a b)`
  have hsub : ∀ b : 𝒜,
      ((f.toPreGNS b : f.PreGNS) : f.GNS) ∈ {x : f.GNS | (0 : ℂ) ≤ ⟪x, T x⟫} := by
    intro b
    show (0 : ℂ) ≤ ⟪((f.toPreGNS b : f.PreGNS) : f.GNS), T _⟫
    rw [hT, gns_starAlgHom_apply, UniformSpace.Completion.inner_coe, f.preGNS_inner_def,
      f.ofPreGNS_toPreGNS, f.ofPreGNS_toPreGNS, ← mul_assoc]
    exact h b
  have hall : ∀ x : f.GNS, (0 : ℂ) ≤ ⟪x, T x⟫ := by
    have hd : DenseRange (fun b : 𝒜 => ((f.toPreGNS b : f.PreGNS) : f.GNS)) := by
      have hsurj : Function.Surjective (fun b : 𝒜 => (f.toPreGNS b : f.PreGNS)) :=
        f.toPreGNS.surjective
      simpa [DenseRange, Set.range_comp'] using
        (UniformSpace.Completion.denseRange_coe (α := f.PreGNS))
    intro x
    exact hclosed.closure_subset_iff.mpr (Set.range_subset_iff.mpr hsub) (hd x)
  -- **30XIII**: the vector states of `B(ℋ_ω)` are order separating
  exact (hilb_vector_states_order_separating (H := f.GNS) T).mpr fun x => hall (x : f.GNS)

/-! ### **30IX** `ϱ_Ω`: the Hilbert direct sum of a family of representations

The thesis's `ϱ_Ω : 𝒜 → B(⊕_{ω∈Ω} ℋ_ω)`, `ϱ_Ω(a)x = (ϱ_ω(a) x(ω))_ω`, built as
the diagonal operator on `lp G 2`.  Mathlib has the single-`ω` GNS
representation and the Hilbert direct sum `lp G 2`, but not the diagonal
operator, so it is constructed here.  (The pattern follows the `ℕ`-fold
amplification `amp` of `A/VN/NormalFunctionals.lean`, generalised to a family
of distinct spaces and to a uniformly bounded family of operators.) -/

section DirectSum

variable {ι : Type v} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
variable (ρ : ∀ i, 𝒜 →⋆ₐ[ℂ] (G i →L[ℂ] G i))

private theorem dsum_memLp (a : 𝒜) (y : lp G 2) :
    Memℓp (fun i => ρ i a ((y : ∀ i, G i) i)) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine memℓp_gen (Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (((lp.memℓp y).summable hp).mul_left (‖a‖ ^ (2 : ℝ≥0∞).toReal)))
  calc ‖ρ i a ((y : ∀ i, G i) i)‖ ^ (2 : ℝ≥0∞).toReal
      ≤ (‖a‖ * ‖(y : ∀ i, G i) i‖) ^ (2 : ℝ≥0∞).toReal := by
        refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
        exact le_trans ((ρ i a).le_opNorm _)
          (mul_le_mul_of_nonneg_right (norm_mi_map_contractive (ρ i) a) (norm_nonneg _))
    _ = ‖a‖ ^ (2 : ℝ≥0∞).toReal * ‖(y : ∀ i, G i) i‖ ^ (2 : ℝ≥0∞).toReal :=
        Real.mul_rpow (norm_nonneg _) (norm_nonneg _)

/-- `ϱ_Ω(a)`, as a linear map on the Hilbert direct sum. -/
private noncomputable def dsumLM (a : 𝒜) : lp G 2 →ₗ[ℂ] lp G 2 where
  toFun y := ⟨fun i => ρ i a ((y : ∀ i, G i) i), dsum_memLp ρ a y⟩
  map_add' y z := by
    ext i; simp only [lp.coeFn_add, Pi.add_apply]; exact map_add (ρ i a) _ _
  map_smul' c y := by
    ext i
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    exact map_smul (ρ i a) _ _

@[simp] private theorem dsumLM_apply (a : 𝒜) (y : lp G 2) (i : ι) :
    ((dsumLM ρ a y : lp G 2) : ∀ i, G i) i = ρ i a ((y : ∀ i, G i) i) := rfl

private theorem dsumLM_norm_le (a : 𝒜) (y : lp G 2) :
    ‖dsumLM ρ a y‖ ≤ ‖a‖ * ‖y‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsy : Summable fun i => ‖(y : ∀ i, G i) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp y).summable hp
  have hsz : Summable fun i =>
      ‖((dsumLM ρ a y : lp G 2) : ∀ i, G i) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp _).summable hp
  have hle : ∀ i, ‖((dsumLM ρ a y : lp G 2) : ∀ i, G i) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ‖a‖ ^ (2 : ℝ≥0∞).toReal * ‖(y : ∀ i, G i) i‖ ^ (2 : ℝ≥0∞).toReal := by
    intro i
    rw [dsumLM_apply]
    calc ‖ρ i a ((y : ∀ i, G i) i)‖ ^ (2 : ℝ≥0∞).toReal
        ≤ (‖a‖ * ‖(y : ∀ i, G i) i‖) ^ (2 : ℝ≥0∞).toReal := by
          refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
          exact le_trans ((ρ i a).le_opNorm _)
            (mul_le_mul_of_nonneg_right (norm_mi_map_contractive (ρ i) a) (norm_nonneg _))
      _ = _ := Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  have h1 : ‖dsumLM ρ a y‖ ^ (2 : ℝ≥0∞).toReal ≤ (‖a‖ * ‖y‖) ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      lp.norm_rpow_eq_tsum hp y, ← tsum_mul_left]
    exact hsz.tsum_le_tsum hle (hsy.mul_left _)
  have hcast : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast, Real.rpow_natCast] at h1
  nlinarith [norm_nonneg (dsumLM ρ a y), mul_nonneg (norm_nonneg a) (norm_nonneg y)]

private noncomputable def dsumCLM (a : 𝒜) : lp G 2 →L[ℂ] lp G 2 :=
  (dsumLM ρ a).mkContinuous ‖a‖ (dsumLM_norm_le ρ a)

@[simp] private theorem dsumCLM_apply (a : 𝒜) (y : lp G 2) (i : ι) :
    ((dsumCLM ρ a y : lp G 2) : ∀ i, G i) i = ρ i a ((y : ∀ i, G i) i) := rfl

private theorem lp_clm_ext' {f g : lp G 2 →L[ℂ] lp G 2}
    (h : ∀ (y : lp G 2) (i : ι),
      ((f y : lp G 2) : ∀ i, G i) i = ((g y : lp G 2) : ∀ i, G i) i) : f = g :=
  ContinuousLinearMap.ext fun y => Subtype.ext (funext (h y))

/-- **30IX** `ϱ_Ω` : the direct sum of a family of representations, as an
miu-map into `B(⊕ᵢ Gᵢ)`. -/
noncomputable def dsumRep : 𝒜 →⋆ₐ[ℂ] (lp G 2 →L[ℂ] lp G 2) where
  toFun := dsumCLM ρ
  map_one' := by
    refine lp_clm_ext' fun y i => ?_
    rw [dsumCLM_apply, map_one]
    rfl
  map_mul' a b := by
    refine lp_clm_ext' fun y i => ?_
    rw [dsumCLM_apply, map_mul]
    rfl
  map_zero' := by
    refine lp_clm_ext' fun y i => ?_
    rw [dsumCLM_apply, map_zero]
    simp
  map_add' a b := by
    refine lp_clm_ext' fun y i => ?_
    rw [dsumCLM_apply, map_add]
    rfl
  commutes' c := by
    refine lp_clm_ext' fun y i => ?_
    rw [dsumCLM_apply, AlgHomClass.commutes]
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun y z => ?_
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    rw [dsumCLM_apply, dsumCLM_apply, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

@[simp] theorem dsumRep_apply (a : 𝒜) (y : lp G 2) (i : ι) :
    ((dsumRep ρ a y : lp G 2) : ∀ i, G i) i = ρ i a ((y : ∀ i, G i) i) := rfl

theorem dsumRep_eq_zero_iff (a : 𝒜) : dsumRep ρ a = 0 ↔ ∀ i, ρ i a = 0 := by
  classical
  constructor
  · intro h i
    ext x
    have h2 := congrArg (fun T : lp G 2 →L[ℂ] lp G 2 => ((T (lp.single 2 i x) :
      lp G 2) : ∀ i, G i) i) h
    simpa using h2
  · intro h
    refine lp_clm_ext' fun y i => ?_
    rw [dsumRep_apply, h i]
    simp

/-- `ϱ_Ω(a)` is positive as soon as every `ϱ_ω(a)` is: by **25III** it is
enough that `⟨x, ϱ_Ω(a)x⟩ = ∑_ω ⟨x(ω), ϱ_ω(a)x(ω)⟩ ≥ 0`, and every summand
is. -/
private theorem dsumRep_nonneg (a : 𝒜) (h : ∀ i, 0 ≤ ρ i a) : 0 ≤ dsumRep ρ a := by
  refine (hilb_vector_states_order_separating (H := lp G 2) _).mpr ?_
  intro x
  show (0 : ℂ) ≤ ⟪(x : lp G 2), dsumRep ρ a (x : lp G 2)⟫
  rw [lp.inner_eq_tsum]
  refine tsum_nonneg fun i => ?_
  rw [dsumRep_apply]
  exact inner_nonneg_of_nonneg (h i) _

end DirectSum

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4977, Proposition),
(2) ⇒ (1) — the argument of cstar.tex:5002 in the form the rest of the
Proposition uses it: if `Ω` is centre separating then `ϱ_Ω` itself is
injective.

"Let `a ∈ 𝒜` with `ϱ_Ω(a) = 0` be given.  We must show that `a = 0`, and for
this it is enough to prove that `a* a = 0`.  Let `b ∈ 𝒜` and `ω ∈ Ω` be given.
Since `Ω` is centre separating, it suffices to show that
`0 = ω(b* a* a b) ≡ ‖ab‖²_ω`.  Since `ϱ_Ω(a) = 0`, we have `ϱ_ω(a) = 0`, thus
`0 = ϱ_ω(a) η_ω(b) = η_ω(ab)`, and so `‖ab‖_ω = 0`." -/
private theorem dsumRep_gns_injective {ι : Type v} (f : ι → (𝒜 →ₚ[ℂ] ℂ))
    (hc : ∀ x : 𝒜, 0 ≤ x → (x = 0 ↔ ∀ (i : ι) (b : 𝒜), f i (star b * x * b) = 0)) :
    Function.Injective (dsumRep (fun i => (f i).gnsStarAlgHom)) := by
  have key : ∀ a : 𝒜, dsumRep (fun i => (f i).gnsStarAlgHom) a = 0 → a = 0 := by
    intro a ha
    have h0 : ∀ i, (f i).gnsStarAlgHom a = 0 := (dsumRep_eq_zero_iff _ a).mp ha
    have hzero : ∀ (i : ι) (b : 𝒜), f i (star b * (star a * a) * b) = 0 := by
      intro i b
      -- `0 = ϱ_ω(a) η_ω(b) = η_ω(ab)`
      have h1 : ((((f i).toPreGNS (a * b) : (f i).PreGNS) : (f i).GNS)) = 0 := by
        rw [← gns_starAlgHom_apply (f i) a b, h0 i]
        rfl
      have h2 : ‖(((f i).toPreGNS (a * b) : (f i).PreGNS))‖ = 0 := by
        rw [← UniformSpace.Completion.norm_coe
          (((f i).toPreGNS (a * b) : (f i).PreGNS)), h1, norm_zero]
      have h3 := (f i).preGNS_norm_sq ((f i).toPreGNS (a * b))
      rw [h2] at h3
      have h4 : star (a * b) * (a * b) = star b * (star a * a) * b := by
        rw [star_mul]; noncomm_ring
      rw [← h4]
      simpa using h3.symm
    -- centre separation, applied to the positive element `a* a`
    have hk : star a * a = 0 := (hc _ (star_mul_self_nonneg a)).mpr hzero
    have hn : ‖a‖ * ‖a‖ = 0 := by rw [← CStarRing.norm_star_mul_self, hk, norm_zero]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg a])
  intro x y hxy
  exact sub_eq_zero.mp (key (x - y) (by rw [map_sub, hxy, sub_self]))

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4977, Proposition),
(1) ⇒ (3): if `ϱ_Ω` is injective then `Ω'` is order separating.  This is the
Proposition's own argument at cstar.tex:5018, which uses nothing about `Ω`
beyond the injectivity of `ϱ_Ω`: by **29IX** it suffices that `ϱ_Ω(a) ≥ 0`
(`nonneg_of_injective_miu`), and each `ϱ_ω(a) ≥ 0` by `gnsStarAlgHom_nonneg`
(**30XIII** and the density of `{η_ω(b)}` in `ℋ_ω`).  In particular the
self-adjointness of `a` is not established by hand: it comes free with the
positivity of `ϱ_Ω(a)`. -/
private theorem orderSeparating_of_dsumRep_injective {ι : Type v}
    (ω : ι → (𝒜 →ₗ[ℂ] ℂ)) (hpos : ∀ i, IsPositiveMap (ω i))
    (hinj : Function.Injective
      (dsumRep (fun i => (toPLM (ω i) (hpos i)).gnsStarAlgHom))) :
    OrderSeparating (fun p : ι × 𝒜 => (ω p.1).comp (conjMap 𝒜 p.2)) := by
  have hconj : ∀ (i : ι) (b x : 𝒜),
      ((ω i).comp (conjMap 𝒜 b)) x = ω i (star b * x * b) := by
    intro i b x
    show ω i (star b * (x * b)) = ω i (star b * x * b)
    rw [mul_assoc]
  intro a
  refine ⟨fun ha p => ?_, fun H => ?_⟩
  · simp only [hconj]
    exact hpos p.1 _ (star_left_conjugate_nonneg ha p.2)
  · have Hb : ∀ (i : ι) (b : 𝒜), (0 : ℂ) ≤ ω i (star b * a * b) := by
      intro i b
      simpa only [hconj] using H (i, b)
    -- every `ϱ_ω(a)` is positive (cstar.tex:5030)
    have hcoord : ∀ i, 0 ≤ (toPLM (ω i) (hpos i)).gnsStarAlgHom a :=
      fun i => gnsStarAlgHom_nonneg _ a fun b => Hb i b
    -- hence so is `ϱ_Ω(a)`; and `ϱ_Ω` is injective, so it reflects positivity
    exact nonneg_of_injective_miu _ hinj a (dsumRep_nonneg _ a hcoord)

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4977, Proposition),
equivalence (2) ↔ (3): a collection `Ω` of p-maps on `𝒜` is centre
separating iff `Ω' = { ω(b* (·) b) : ω ∈ Ω, b ∈ 𝒜 }` is order separating.

*Class 1 — faithful.*  Both directions are the Proposition's own proof.
"It is clear that (3) entails (2)" is the second bullet.  For (2) ⇒ (3) the
thesis goes through (1): `ϱ_Ω` is injective by cstar.tex:5002
(`dsumRep_gns_injective`), and then cstar.tex:5018, which is the preceding
`orderSeparating_of_dsumRep_injective`. -/
theorem proto_gelfand_naimark_1 {ι : Type v} (ω : ι → (𝒜 →ₗ[ℂ] ℂ))
    (hpos : ∀ i, IsPositiveMap (ω i)) :
    CentreSeparating (fun i => ω i) ↔
      OrderSeparating (fun p : ι × 𝒜 => (ω p.1).comp (conjMap 𝒜 p.2)) := by
  have hconj : ∀ (i : ι) (b x : 𝒜),
      ((ω i).comp (conjMap 𝒜 b)) x = ω i (star b * x * b) := by
    intro i b x
    show ω i (star b * (x * b)) = ω i (star b * x * b)
    rw [mul_assoc]
  constructor
  · intro hc
    exact orderSeparating_of_dsumRep_injective ω hpos
      (dsumRep_gns_injective (fun i => toPLM (ω i) (hpos i)) hc)
  · intro ho a ha
    refine ⟨fun h i b => by rw [h]; simp, fun H => ?_⟩
    have h1 : (0 : 𝒜) ≤ -a := by
      refine (ho (-a)).mpr fun p => ?_
      simp only [hconj]
      rw [show star p.2 * (-a) * p.2 = -(star p.2 * a * p.2) by noncomm_ring, map_neg,
        H p.1 p.2, neg_zero]
    exact le_antisymm (neg_nonneg.mp h1) ha

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4977, Proposition),
equivalence (1) ↔ (2): `ϱ_Ω : 𝒜 → B(ℋ_Ω)` — the concrete `dsumRep` of
**30IX**, the diagonal operator on `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω` — is injective iff
`Ω` is centre separating.  Together with `proto_gelfand_naimark_1` this is
the Proposition's three-way equivalence, and `proto_gelfand_naimark_3` is its
closing claim.

*Class 1 — faithful.*  (2) ⇒ (1) is cstar.tex:5002, `dsumRep_gns_injective`;
(1) ⇒ (2) is the thesis's (1) ⇒ (3) (`orderSeparating_of_dsumRep_injective`,
cstar.tex:5018) followed by "(3) entails (2)", which is the second bullet of
the printed proof and the `mpr` of `proto_gelfand_naimark_1`.

*Statement change, 2026-09-04, under the `docs/DECISIONS.md` §2.1 ruling,
which thereby closes §2.4 (the former QUESTIONS A8).*  This read
`CentreSeparating Ω → ∃ H (ρ : 𝒜 →⋆ₐ[ℂ] B H), Function.Injective ρ`, which
names neither `Ω` nor `ϱ_Ω`: in that form clause (1) does not depend on `Ω`,
so the converse (1) ⇒ (2) was unstatable, and (2) ⇒ (1) collapsed into
**30XIV** (every C*-algebra with a centre separating family of p-maps has an
injective representation *is* Gelfand–Naimark).  The existential is where it
belongs, in `gelfand_naimark` below, which is unchanged. -/
theorem proto_gelfand_naimark_2 {ι : Type v} (ω : ι → (𝒜 →ₗ[ℂ] ℂ))
    (hpos : ∀ i, IsPositiveMap (ω i)) :
    Function.Injective (dsumRep (fun i => (toPLM (ω i) (hpos i)).gnsStarAlgHom)) ↔
      CentreSeparating (fun i => ω i) :=
  ⟨fun hinj => (proto_gelfand_naimark_1 ω hpos).mpr
      (orderSeparating_of_dsumRep_injective ω hpos hinj),
    fun hc => dsumRep_gns_injective (fun i => toPLM (ω i) (hpos i)) hc⟩

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4977, Proposition), the
closing claim: in that case `ϱ_Ω(𝒜)` is a C*-subalgebra of `B(ℋ_Ω)` and
`ϱ_Ω` restricts to an miu-isomorphism from `𝒜` onto `ϱ_Ω(𝒜)`.

*Class 1 — faithful.*  This is **29IX** applied to `ϱ_Ω`, which is what the
Proposition's own proof does (cstar.tex:5020): `injective_miu_iso_on_image_isomorphism`
on the injectivity `proto_gelfand_naimark_2` supplies. -/
theorem proto_gelfand_naimark_3 {ι : Type v} (ω : ι → (𝒜 →ₗ[ℂ] ℂ))
    (hpos : ∀ i, IsPositiveMap (ω i))
    (hc : CentreSeparating (fun i => ω i)) :
    ∃ S : StarSubalgebra ℂ
        (lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2 →L[ℂ]
          lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2),
      (S : Set (lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2 →L[ℂ]
          lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2))
          = Set.range (dsumRep fun i => (toPLM (ω i) (hpos i)).gnsStarAlgHom) ∧
        IsClosed (S : Set (lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2 →L[ℂ]
          lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2)) ∧
          ∃ e : 𝒜 ≃⋆ₐ[ℂ] S, ∀ a : 𝒜,
            Subtype.val (e a) = dsumRep (fun i => (toPLM (ω i) (hpos i)).gnsStarAlgHom) a :=
  injective_miu_iso_on_image_isomorphism _ ((proto_gelfand_naimark_2 ω hpos).mpr hc)

end GNS

/-- **30XIV** (`gelfand-naimark`, cstar.tex:5048, Theorem
(Gelfand–Naimark)): every C*-algebra `𝒜` is miu-isomorphic to a C*-algebra
of bounded operators on a Hilbert space. -/
theorem gelfand_naimark (𝒜 : Type u) [CStarAlgebra 𝒜] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (ρ : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ρ := by
  -- the thesis's proof: take `Ω` to be *all* states of `𝒜`; they are order
  -- separating (**22VIII**), hence centre separating (**30X**), so **30X**.2
  -- applies.  `Ω` lives in `Type u`, so `ℋ_Ω` does too.
  letI : PartialOrder 𝒜 := CStarAlgebra.spectralOrder 𝒜
  haveI : StarOrderedRing 𝒜 := CStarAlgebra.spectralOrderedRing 𝒜
  have hpos : ∀ ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω}, IsPositiveMap (ω : 𝒜 →ₗ[ℂ] ℂ) :=
    fun ω => ω.2.1
  have hc : CentreSeparating fun ω : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω} =>
      (ω : 𝒜 →ₗ[ℂ] ℂ) := by
    refine (proto_gelfand_naimark_1 _ hpos).mpr fun a => ⟨fun ha p => ?_, fun H => ?_⟩
    · show (0 : ℂ) ≤ (p.1 : 𝒜 →ₗ[ℂ] ℂ) (star p.2 * (a * p.2))
      rw [← mul_assoc]
      exact hpos p.1 _ (star_left_conjugate_nonneg ha p.2)
    · refine (states_order_separating_2 a).mpr fun ω => ?_
      have h := H (ω, 1)
      have he : (conjMap 𝒜 (1 : 𝒜)) a = a := by
        show star (1 : 𝒜) * (a * 1) = a
        rw [star_one, one_mul, mul_one]
      show (0 : ℂ) ≤ (ω : 𝒜 →ₗ[ℂ] ℂ) a
      simp only [LinearMap.comp_apply, he] at h
      exact h
  -- `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω` and `ϱ_Ω` (**30IX**)
  exact ⟨lp (fun i : {ω : 𝒜 →ₗ[ℂ] ℂ // IsState ω} =>
      (toPLM (i : 𝒜 →ₗ[ℂ] ℂ) (hpos i)).GNS) 2, inferInstance, inferInstance,
    inferInstance, _, (proto_gelfand_naimark_2 _ hpos).mpr hc⟩

end Theses.A.CStar
