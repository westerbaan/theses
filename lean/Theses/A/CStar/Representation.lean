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

All statements of parsecs 270–300 are proved, **28II**.4
`functional_calculus_4` included (session 92); its *statement* is nevertheless
still awaiting an author decision, because our rendering is weaker than the
exercise — see QUESTIONS A10 and the note on the declaration itself.  See
CONVENTIONS.md for the numbering (**27XV** = parsec 270, point 150) and naming
conventions.
-/
import Theses.A.CStar.Positive

open scoped ComplexOrder ComplexInnerProductSpace ComplexStarModule NNReal ENNReal
open Filter Topology WeakDual

universe u v

namespace Theses.A.CStar

/-! ## Parsec 270: Gelfand's representation theorem

**27I** (cstar.tex:3890): introduction — nothing to formalize.
**27II** (cstar.tex:3899, Setting): `𝒜` is a commutative C*-algebra.

**27III** (`gelfand-representation`, cstar.tex:3902, Definition): the
*spectrum* `spec(𝒜)` of `𝒜` is the set of miu-maps `f : 𝒜 → ℂ` with the
topology of pointwise convergence — in Mathlib `WeakDual.characterSpace ℂ 𝒜`
(its elements are the non-zero continuous algebra homomorphisms, which for a
C*-algebra are exactly the miu-maps, automatically continuous by
`norm_mi_map_contractive`); the *Gelfand representation*
`γ : 𝒜 → C(spec 𝒜)`, `γ(a)(f) = f(a)`, is Mathlib's
`gelfandTransform ℂ 𝒜` (star-preserving version: `gelfandStarTransform`).

**27V** (cstar.tex:3922, Remark): the relation between `spec(𝒜)` and
`spec(a)` appears at **27XVII**; nothing to formalize.
**27VI** (cstar.tex:3932): program — nothing to formalize. -/

section GelfandRepresentation

variable {𝒜 : Type*} [CommCStarAlgebra 𝒜]

/-- **27IV** (`gelfand-representation-basic`, cstar.tex:3916, Exercise),
part 1: the evaluation map `f ↦ f(a)` on `spec(𝒜)` is continuous for every
`a ∈ 𝒜`. -/
theorem gelfand_representation_basic_1 (a : 𝒜) :
    Continuous fun φ : characterSpace ℂ 𝒜 => φ a :=
  (gelfandTransform ℂ 𝒜 a).continuous

/-- **27IV** (`gelfand-representation-basic`, cstar.tex:3916, Exercise),
part 2: the Gelfand representation is an miu-map; multiplicativity and
unitality are part of the bundled `gelfandTransform`, so involution
preservation remains. -/
theorem gelfand_representation_basic_2 (a : 𝒜) :
    gelfandTransform ℂ 𝒜 (star a) = star (gelfandTransform ℂ 𝒜 a) :=
  gelfandTransform_map_star a

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **27VII** (cstar.tex:3949, Definition): a *Riesz ideal* of `𝒜` is an
order ideal `I` with `|a| ∈ I` for every self-adjoint `a ∈ I`. -/
def IsRieszIdeal (I : Submodule ℂ 𝒜) : Prop :=
  IsOrderIdeal I ∧ ∀ a ∈ I, IsSelfAdjoint a → CFC.abs a ∈ I

/-- **27VII** (cstar.tex:3949, Definition): a *maximal Riesz ideal* is a
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

/-- **27VIII** (`riesz-ideal-ring-ideal`, cstar.tex:3963, Lemma): a Riesz
ideal `I` of `𝒜` is a ring ideal: `a x ∈ I` for `a ∈ 𝒜`, `x ∈ I`. -/
theorem riesz_ideal_ring_ideal (I : Submodule ℂ 𝒜) (hI : IsRieszIdeal I)
    (a : 𝒜) (x : 𝒜) (hx : x ∈ I) : a * x ∈ I := by
  have h1 := riesz_mul_mem_of_left_isSelfAdjoint hI (ℜ a).2 hx
  have h2 := riesz_mul_mem_of_left_isSelfAdjoint hI (ℑ a).2 hx
  have he : a * x = (ℜ a : 𝒜) * x + Complex.I • ((ℑ a : 𝒜) * x) := by
    rw [← smul_mul_assoc, ← add_mul, realPart_add_I_smul_imaginaryPart]
  rw [he]
  exact I.add_mem h1 (I.smul_mem _ h2)

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3983, Exercise), part 3: each
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

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3983, Exercise), part 2: the sum
`I + J` of two Riesz ideals is a Riesz ideal.  (That `I + J` might not be an
order ideal for order ideals `I`, `J` is not converted.) -/
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

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3983, Exercise), part 1: the
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

/-- **27XI** (`maximal-riesz-ideal-maximal-order-ideal`, cstar.tex:4010,
Lemma): a maximal Riesz ideal is a maximal order ideal.

The proof now printed at cstar.tex 270.120 is the **corrected** one of
erratum `parsec-270.120` (`asols.tex:113–171`), incorporated 2026-08-13; the
first printing erroneously assumed `|a| ∈ J`.  What follows transcribes the
corrected proof, so the erratum is no longer outstanding. -/
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

/-- **27XIII** (`riesz-ideal-miu-map`, cstar.tex:4075, Lemma): for every
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

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3983, Exercise), part 1b: the
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

/-- **27X** (`riesz-ideal-basic`, cstar.tex:3983, Exercise), part 1c: for
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

/-- **27XV** (`inv-mult-state`, cstar.tex:4055, Proposition): a self-adjoint
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
    -- **16VIII** (cstar.tex:2663) rejects.  That detour is gone.
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

/-- **27XVII** (`spectrum-miu`, cstar.tex:4078, Exercise):
`spec(a) = { f(a) : f ∈ spec(𝒜) }` for self-adjoint `a ∈ 𝒜`.

*Class 1 — faithful.*  The exercise's own derivation from **27XV**
`inv_mult_state`: a point `λ` of `spec(a)` is real (`a` being self-adjoint),
so `λ − a` is self-adjoint and non-invertible, and **27XV** produces a
character killing it, i.e. one with `f(a) = λ`; conversely `f(a) ∈ spec(a)`
is **27XV**'s easy direction.

Until this repair the theorem went through Mathlib's
`WeakDual.CharacterSpace.mem_spectrum_iff_exists`, whose proof reaches the
character space through maximal *ring* ideals — the route **16VIII**
(cstar.tex:2663) rejects, and the very detour that `inv_mult_state`'s own
note records as removed.  The two order instances are supplied locally by
`CStarAlgebra.spectralOrder`, so the statement is unchanged. -/
theorem spectrum_miu (a : 𝒜) (ha : IsSelfAdjoint a) :
    spectrum ℂ a = Set.range fun φ : characterSpace ℂ 𝒜 => φ a := by
  letI : PartialOrder 𝒜 := CStarAlgebra.spectralOrder 𝒜
  haveI : StarOrderedRing 𝒜 := CStarAlgebra.spectralOrderedRing 𝒜
  refine Set.ext fun z => ⟨fun hz => ?_, ?_⟩
  · have hre : z = (z.re : ℂ) := ha.mem_spectrum_eq_re hz
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

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4082,
Exercise), part 1: the Gelfand representation is an isometry,
`‖γ(a)‖ = ‖a‖`.

*Class 1 — faithful.*  The Exercise's own hint (cstar.tex:4086): for
self-adjoint `a` the range of `γ(a)` is `spec(a)` by **27XVII**
`spectrum_miu` — the spectrum of an element of `C(spec 𝒜)` being its range —
so `γ(a)` and `a` have the same spectral radius, and **16II**
`norm_spectrum` turns that into `‖γ(a)‖ = ‖a‖`.  The general case is the
C*-identity: `‖γ(a)‖² = ‖γ(a)*γ(a)‖ = ‖γ(a*a)‖ = ‖a*a‖ = ‖a‖²`.

Until this repair the theorem was Mathlib's `gelfandTransform_isometry`,
whose proof runs through `WeakDual.CharacterSpace.mem_spectrum_iff_exists`
and so through maximal *ring* ideals — the route **16VIII** rejects and that
`inv_mult_state` and `spectrum_miu` were taken off. -/
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

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4082,
Exercise), part 2, first clause: consequently `γ` is injective.

*Class 1 — faithful.*  The Exercise's own "conclude": `γ(a) = γ(b)` makes
`‖a − b‖ = ‖γ(a − b)‖ = 0` by part 1. -/
theorem gelfand_representation_injective :
    Function.Injective (gelfandTransform ℂ 𝒜) := by
  intro a b hab
  have h : ‖a - b‖ = 0 := by
    rw [← gelfand_representation_isometry (a - b), map_sub, hab, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h)

/-- **27XVIII** (`gelfand-representation-isometry`, cstar.tex:4082,
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

/-- **27XX** (`stone-weierstrass`, cstar.tex:4103, Theorem
(Stone–Weierstraß)): a C*-subalgebra `𝒮` of `C(X)`, `X` compact Hausdorff,
which separates the points of `X` is all of `C(X)`.  (Mathlib:
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`.) -/
theorem stone_weierstrass {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (S : StarSubalgebra ℂ C(X, ℂ)) (hS : IsClosed (S : Set C(X, ℂ)))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ S, f x ≠ f y) :
    S = ⊤ := by
  have hsep' : S.SeparatesPoints := by
    rintro x y hxy
    obtain ⟨f, hf, hne⟩ := hsep x y hxy
    exact ⟨(f : X → ℂ), ⟨f, hf, rfl⟩, hne⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep'
  refine top_le_iff.mp ?_
  calc (⊤ : StarSubalgebra ℂ C(X, ℂ)) = S.topologicalClosure := h.symm
    _ ≤ S := StarSubalgebra.topologicalClosure_minimal le_rfl hS

/-- **27XXV** (`spectrum-calg-compact-hausdorff`, cstar.tex:4186, Lemma): the
spectrum `spec(𝒜)` of a commutative C*-algebra is a compact Hausdorff space.
(Mathlib instances on `characterSpace ℂ 𝒜`.) -/
theorem spectrum_calg_compact_hausdorff :
    CompactSpace (characterSpace ℂ 𝒜) ∧ T2Space (characterSpace ℂ 𝒜) :=
  ⟨inferInstance, inferInstance⟩

/-- **27XXVII** (`gelfand`, cstar.tex:4221, Gelfand's Representation
Theorem): for a commutative C*-algebra `𝒜` the Gelfand representation
`γ : 𝒜 → C(spec 𝒜)` is an miu-isomorphism — it is bijective (and
star-preserving by `gelfand_representation_basic_2`, so a ⋆-isomorphism:
`gelfandStarTransform`).

*Class 1 — faithful.*  The assembly of **27XXVIII** (cstar.tex:4228):
injectivity is **27XVIII**.2, and for surjectivity the range of `γ` is a
closed ⋆-subalgebra of `C(spec 𝒜)` by **27XVIII**.2's second clause which
separates the points of `spec 𝒜` — two characters agreeing on every `γ(a)`
agree on every `a` — so **27XX** `stone_weierstrass` makes it everything.

Until this repair the theorem was Mathlib's `gelfandTransform_bijective`,
which supplies its own isometry (the maximal-ring-ideal route) instead of
**27XVIII**. -/
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

end GelfandRepresentation

/-! ## Parsec 280: the continuous functional calculus -/

section FunctionalCalculus

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 1: there
is a least C*-subalgebra `C*(a)` of `𝒜` containing `a` — Mathlib's
`StarAlgebra.elemental ℂ a`. -/
theorem functional_calculus_1 (a : 𝒜) :
    IsLeast {S : StarSubalgebra ℂ 𝒜 | a ∈ S ∧ IsClosed (S : Set 𝒜)}
      (StarAlgebra.elemental ℂ a) :=
  ⟨⟨StarAlgebra.elemental.self_mem ℂ a, StarAlgebra.elemental.isClosed ℂ a⟩,
    fun _ hS => StarAlgebra.elemental.le_of_mem hS.2 hS.1⟩

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 1b:
every `b ∈ C*(a)` commutes with every `c` that commutes with `a` (and with
`a*`). -/
theorem functional_calculus_1b (a b : 𝒜) (hb : b ∈ StarAlgebra.elemental ℂ a)
    (c : 𝒜) (hc : a * c = c * a) (hc' : star a * c = c * star a) :
    b * c = c * b := by
  have hcmem : c ∈ (StarSubalgebra.centralizer ℂ ({a} : Set 𝒜) : Set 𝒜) :=
    (StarSubalgebra.mem_centralizer_iff ℂ).mpr (by rintro g rfl; exact ⟨hc, hc'⟩)
  have hbmem := StarAlgebra.elemental.le_centralizer_centralizer (R := ℂ) a hb
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hbmem) c hcmem).1.symm

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 2: `a`
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

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 3, first
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

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 3
(sample property): `a^α a^β = a^{α+β}` for `a ≥ 0` and `α, β ∈ (0,∞)`. -/
theorem functional_calculus_3 (a : 𝒜) (ha : 0 ≤ a) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    CFC.rpow a α * CFC.rpow a β = CFC.rpow a (α + β) := by
  lift α to NNReal using hα.le with α' hα'
  lift β to NNReal using hβ.le with β' hβ'
  have hα0 : (0 : NNReal) < α' := by exact_mod_cast hα
  have hβ0 : (0 : NNReal) < β' := by exact_mod_cast hβ
  have e : ∀ x : NNReal, 0 < x → CFC.rpow a (x : ℝ) = CFC.nnrpow a x :=
    fun x hx => (CFC.nnrpow_eq_rpow hx).symm
  rw [← NNReal.coe_add, e _ hα0, e _ hβ0, e _ (add_pos hα0 hβ0)]
  exact (CFC.nnrpow_add hα0 hβ0).symm

end Ordered

/-- **28II** (`functional-calculus`, cstar.tex:4299, Exercise), part 4:
`f(a)` is the unique element `b` of `C*(a)` with `φ(b) = f(φ(a))` for all
`φ ∈ spec(C*(a))`.

⚠ **This is the weaker form of 28II.4, and is proved as such.**  The exercise
asserts two things: that the character condition determines at most one element
of `C*(a)`, and that the element it determines *is* `f(a)` — i.e. `Φ(f)` of
part 3, Mathlib's `cfc f a`.  The statement below is the first clause together
with bare existence; the name `f(a)` does not occur in it, so it does not
characterise the functional calculus.  Strengthening it is a statement change
and needs a ruling: **QUESTIONS A10**, which carries the (compiled) 14-line
proof of the missing clause `φ (cfc f a) = f (φ a)`.

Proof, following the thesis: part 3's `j : ρ ↦ ρ(a)` maps `spec(C*(a))` into
`spec(a)` continuously, so `f ∘ j ∈ C(spec(C*(a)))`; and `C*(a)` is commutative
(`IsStarNormal a`), so Gelfand's representation theorem **27XXVII** makes
`γ = gelfandStarTransform` a bijection onto `C(spec(C*(a)))`.  The element
sought is exactly `γ⁻¹(f ∘ j)`, and it is unique because `γ` is injective. -/
theorem functional_calculus_4 (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    ∃! b : StarAlgebra.elemental ℂ a,
      ∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a),
        φ b = f (φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :
          StarAlgebra.elemental ℂ a)) := by
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
  -- `f ∘ j ∈ C(spec(C*(a)))`; the claim is that it has a unique `γ`-preimage.
  set g : C(characterSpace ℂ (StarAlgebra.elemental ℂ a), ℂ) := ⟨_, hcont⟩
  have key : ∀ b : StarAlgebra.elemental ℂ a,
      (∀ φ : characterSpace ℂ (StarAlgebra.elemental ℂ a),
          φ b = f (φ (⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :
            StarAlgebra.elemental ℂ a))) ↔
        gelfandStarTransform (StarAlgebra.elemental ℂ a) b = g := by
    intro b
    constructor
    · intro h; ext φ; exact h φ
    · intro h φ; exact DFunLike.congr_fun h φ
  -- Gelfand's representation theorem (27XXVII) for the commutative C*-algebra
  -- `C*(a)`: `γ` is bijective, so `f ∘ j` has exactly one preimage.
  refine ⟨(gelfandStarTransform (StarAlgebra.elemental ℂ a)).symm g, ?_, ?_⟩
  · exact (key _).2 ((gelfandStarTransform (StarAlgebra.elemental ℂ a)).apply_symm_apply g)
  · intro b hb
    rw [← (gelfandStarTransform (StarAlgebra.elemental ℂ a)).symm_apply_apply b,
      (key b).1 hb]

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 5
(Spectral mapping theorem): `spec(f(a)) = f(spec(a))` for normal `a` and
`f ∈ C(spec a)`.  (Mathlib: `cfc_map_spectrum`.) -/
theorem functional_calculus_5 (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (cfc f a) = f '' spectrum ℂ a :=
  cfc_map_spectrum f a

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 6:
`spec(ρ(a)) ⊆ spec(a)` and `ρ(f(a)) = f(ρ(a))` for every miu-map
`ρ : 𝒜 → ℬ`. -/
theorem functional_calculus_6 {ℬ : Type*} [CStarAlgebra ℬ]
    (ρ : 𝒜 →⋆ₐ[ℂ] ℬ) (a : 𝒜) [IsStarNormal a] (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    spectrum ℂ (ρ a) ⊆ spectrum ℂ a ∧ ρ (cfc f a) = cfc f (ρ a) :=
  ⟨AlgHom.spectrum_apply_subset ρ a, ρ.map_cfc f a hf
    (AddMonoidHomClass.continuous_of_bound ρ 1 fun x => by
      simpa using NonUnitalStarAlgHom.norm_apply_le ρ x)⟩

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 7:
`g(f(a)) = (g ∘ f)(a)` for normal `a`.  (Mathlib: `cfc_comp`.) -/
theorem functional_calculus_7 (a : 𝒜) [IsStarNormal a] (f g : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a))
    (hg : ContinuousOn g (f '' spectrum ℂ a)) :
    cfc g (cfc f a) = cfc (g ∘ f) a :=
  (cfc_comp g f a).symm

section Ordered2
variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **28II** (`functional-calculus`, cstar.tex:4258, Exercise), part 7b:
`(a^α)^β = a^{αβ}` for `a ≥ 0` and `α, β ∈ (0,∞)`. -/
theorem functional_calculus_7b (a : 𝒜) (ha : 0 ≤ a) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    CFC.rpow (CFC.rpow a α) β = CFC.rpow a (α * β) :=
  CFC.rpow_rpow_of_exponent_nonneg a α β hα.le hβ.le ha

/-- **28III** (`sqrt-monotone`, cstar.tex:4353, Theorem): `0 ≤ a ≤ b`
implies `a^α ≤ b^α` for `α ∈ (0, 1]`; in particular the square root is
monotone on the positive elements. -/
theorem sqrt_monotone (a b : 𝒜) (ha : 0 ≤ a) (hab : a ≤ b) (α : ℝ)
    (h0 : 0 < α) (h1 : α ≤ 1) :
    CFC.rpow a α ≤ CFC.rpow b α :=
  CFC.rpow_le_rpow ⟨h0.le, h1⟩ hab

end Ordered2

end FunctionalCalculus

/-! ## Parsec 290 (`gelfand-equivalence`): duality with compact Hausdorff spaces

**29I** (cstar.tex:4475): the functors `C : CH → (cCStar_miu)^op` and
`spec : (cCStar_miu)^op → CH`, and the statement that the Gelfand
representations form a natural isomorphism giving an equivalence
`(cCStar_miu)^op ≃ CH`.  The construction of the categories is out of scope
here; the key mathematical content is **29II** and **29VII** below. -/

section Duality

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **29II** (cstar.tex:4503, Lemma): every miu-map `τ : C(X) → ℂ`, `X`
compact Hausdorff, is given by evaluation at some point `x ∈ X`.

*Class 1 — faithful.*  The Lemma's own proof (cstar.tex:4520–4560), in three
movements around the set

  `Z = { x ∈ X : h(x) ≠ 0 for some h ≥ 0 in C(X) with τ(h) = 0 }`.

**29V** (cstar.tex:4540) — if `f ≥ 0` vanishes outside `Z` then `τ(f) = 0`:
each `x` with `f(x) > 0` lies in `Z`, so some `h ≥ 0` with `τ(h) = 0` has
`h(x) > 0`, and `g := (f(x)/h(x) + 1)·h` is a positive element with
`τ(g) = 0` and `g(x) > f(x)`; the sets `{ f < g }` cover the compact
`{ f ≥ ε }`, a finite subcover gives `g₁, …, g_N`, and their supremum
`g₁ ∨ ⋯ ∨ g_N` — which exists by **26II**.3 and which `τ` preserves by
**26II**.4, so `τ(g₁ ∨ ⋯ ∨ g_N) = 0` — dominates `f` up to `ε`.  Hence
`0 ≤ τ(f) ≤ ε` for every `ε > 0`.

**29IV** (cstar.tex:4530) — `X \ Z` has at most one point: for `x ≠ y`
Urysohn gives `p, q ≥ 0` with `pq = 0`, `p(x) = 1`, `q(y) = 1`, and
`0 = τ(pq) = τ(p)τ(q)` puts `x` or `y` into `Z`.  It is non-empty because
`f = 1` in **29V** would otherwise give `1 = τ(1) = 0`.

**29VI** (cstar.tex:4560) — with `x₀` the unique point outside `Z`, the
element `d := f − f(x₀)` has `(d*d)(x) ≠ 0 ⟹ x ≠ x₀ ⟹ x ∈ Z`, so **29V**
gives `0 = τ(d*d) = |τ(f) − f(x₀)|²`.

Until this repair the proof ran backwards: it read `x` off the surjectivity
of Mathlib's `CharacterSpace.homeoEval`, i.e. off **29VII** — which the
thesis derives *from* this Lemma.  The finite-supremum ingredient **29V**
needs (`commutative_cstar_basic_3_finite`, `commutative_cstar_basic_4_finite`)
is what made the honest route available. -/
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

/-- **29VII** (cstar.tex:4563, Exercise): the map `x ↦ δₓ` (with
`δₓ(f) = f(x)`, an miu-map) is a homeomorphism from `X` onto `spec(C(X))`.

*Class 1 — faithful.*  The Exercise's own three steps.  That `δₓ` is miu and
that `x ↦ δₓ` is continuous is Mathlib's `continuousMapEval`, a definition.
Injectivity is Urysohn on the compact Hausdorff `X`: a `p` with `p(x) = 0`
and `p(y) = 1` separates `δₓ` from `δ_y`.  Surjectivity is **29II**
`multiplicative_state_on_cx`.  And a continuous bijection from a compact
space to a Hausdorff space is a homeomorphism — the corrected form of
erratum parsec-290.70.

Until this repair the theorem was Mathlib's `homeoEval`, whose surjectivity
runs through the maximal *ring* ideals of `C(X)` — the route **16VIII**
rejects — and which is therefore the inversion of the thesis's order: the
thesis proves **29II** first and reads this Exercise off it. -/
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

/-- **29VIII** (`injective-miu-isometry`, cstar.tex:4573, Exercise): every
injective miu-map between C*-algebras is an isometry.  (The intermediate
categorical steps — mono = injective and epi = surjective in `CH` — are part
of the proof and not converted separately.) -/
theorem injective_miu_isometry (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) (a : 𝒜) : ‖ρ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map ρ hρ a

/-- **29IX** (`injective-miu-iso-on-image`, cstar.tex:4600, Exercise), first
clause: the range of an injective miu-map `ρ : 𝒜 → ℬ` is closed. -/
theorem injective_miu_iso_on_image (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) : IsClosed (Set.range ρ) :=
  (NonUnitalStarAlgHom.isometry ρ hρ).isClosedEmbedding.isClosed_range

/-- **29IX** (`injective-miu-iso-on-image`, cstar.tex:4600, Exercise), the
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

**30I** (`completion-inner-product-space`, cstar.tex:4613): the plan for the
Gelfand–Naimark theorem via the GNS construction — nothing to formalize. -/

section GNS

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **30II** (`state-inner-product`, cstar.tex:4662, Lemma): for every p-map
`ω : 𝒜 → ℂ` on a C*-algebra, `[a, b]_ω = ω(a* b)` defines an inner product
on `𝒜` (positive semi-definite, conjugate symmetric; linearity in the second
argument is automatic). -/
theorem state_inner_product (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    0 ≤ ω (star a * a) ∧ star (ω (star a * b)) = ω (star b * a) :=
  ⟨hω _ (star_mul_self_nonneg a), by
    simpa [star_mul] using (cstar_p_implies_i ω hω (star a * b)).symm⟩

/-- The seminorm `‖a‖_ω = ω(a* a)^{1/2}` induced by a positive functional
`ω` (**30IV**, `omega-norm-basic`, cstar.tex:4680). -/
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

/-- **30IV** (`omega-norm-basic`, cstar.tex:4680, Exercise), part 1
(Kadison's inequality): `|ω(a* b)|² ≤ ω(a* a) ω(b* b)` for a p-map `ω`. -/
theorem omega_norm_basic_1 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    ((‖ω (star a * b)‖ : ℂ)) ^ 2 ≤ ω (star a * a) * ω (star b * b) := by
  set f := toPLM ω hω with hf
  have hA : ((‖(f.toPreGNS a : f.PreGNS)‖ : ℂ)) ^ 2 = ω (star a * a) :=
    f.preGNS_norm_sq (f.toPreGNS a)
  have hB : ((‖(f.toPreGNS b : f.PreGNS)‖ : ℂ)) ^ 2 = ω (star b * b) :=
    f.preGNS_norm_sq (f.toPreGNS b)
  have hi : ⟪(f.toPreGNS a : f.PreGNS), (f.toPreGNS b : f.PreGNS)⟫ = ω (star a * b) := rfl
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS a : f.PreGNS) (f.toPreGNS b : f.PreGNS)
  rw [hi] at hcs
  have hsq : ‖ω (star a * b)‖ ^ 2 ≤
      (‖(f.toPreGNS a : f.PreGNS)‖ * ‖(f.toPreGNS b : f.PreGNS)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcs 2
  rw [← hA, ← hB, ← mul_pow]
  exact_mod_cast RCLike.ofReal_le_ofReal (K := ℂ) |>.mpr hsq

/-- **30IV** (`omega-norm-basic`, cstar.tex:4680, Exercise), part 2, the
inequality (in the corrected form of erratum `parsec-300.40`, without the
`‖ω‖` factor): `‖ab‖_ω ≤ ‖a‖ ‖b‖_ω`, using `a* a ≤ ‖a‖²`.  The four
counterexamples the exercise also asks for are
`omega_norm_basic_2_counterexamples` below. -/
theorem omega_norm_basic_2 (ω : 𝒜 →ₗ[ℂ] ℂ) (hω : IsPositiveMap ω)
    (a b : 𝒜) :
    omegaSeminorm ω (a * b) ≤ ‖a‖ * omegaSeminorm ω b := by
  set f := toPLM ω hω with hf
  have hn : ∀ x : 𝒜, omegaSeminorm ω x = ‖(f.toPreGNS x : f.PreGNS)‖ := fun _ => rfl
  rw [hn, hn]
  have heq : (f.toPreGNS (a * b) : f.PreGNS) = f.leftMulMapPreGNS a (f.toPreGNS b) := rfl
  rw [heq]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have h2 : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

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

/-- **30IV** (`omega-norm-basic`, cstar.tex:4680, Exercise), part 2, the four
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

/-- **30V** (`inner-product-completion`, cstar.tex:4733, Exercise), the
headline: every complex inner product space `V` can be completed to a Hilbert
space `H` in which it embeds densely (Mathlib: `UniformSpace.Completion` with
its `InnerProductSpace` instance; the intermediate steps — the metric on
Cauchy sequences, its completeness, and the extension of the operations — are
Mathlib's completion API).

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
  ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    UniformSpace.Completion.toComplₗᵢ, UniformSpace.Completion.denseRange_coe⟩

section DegenerateInner

-- The inner product of a possibly degenerate `PreInnerProductSpace.Core`,
-- written `⟪·,·⟫`, as in **4XV** (`A/CStar/Basic`).
attribute [local instance] InnerProductSpace.Core.toPreInner'

/-- **30V** (`inner-product-completion`, cstar.tex:4733, Exercise), the
headline for a possibly *degenerate* inner product — which is how the
exercise states it: "note, however, that `η` need not be injective: show that
`η(a) = η(b)` iff `‖a−b‖ = 0` for all `a,b ∈ V`".  So `V` carries only a
`PreInnerProductSpace.Core ℂ V`, the setting of **4XV**, where
`‖x‖ = innerNorm x = √⟪x,x⟫` is a *seminorm* and need not be a norm.  The
completion `ℋ` is still a Hilbert space, `η : V → ℋ` is still linear with
`⟪η a, η b⟫ = [a,b]` and dense image — and `η` collapses exactly the
seminorm-zero differences.

Divergence (2), a different route to the same object: the thesis builds `ℋ`
by hand as the Cauchy sequences on `V` modulo `lim ‖aₙ−bₙ‖ = 0`, whereas this
is Mathlib's completion of the separation quotient of `V`.  The exercise's
collapse of `η` is carried by that quotient: `η a = η b` iff `a` and `b` are
inseparable (the completion map is injective on a T0 space) iff
`d(a,b) = ‖a−b‖ = 0`, which is the exercise's own criterion.

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
  refine ⟨UniformSpace.Completion (SeparationQuotient V), inferInstance, inferInstance,
    inferInstance,
    ((UniformSpace.Completion.toComplL : SeparationQuotient V →L[ℂ]
        UniformSpace.Completion (SeparationQuotient V)).comp
      (SeparationQuotient.mkCLM ℂ V)).toLinearMap, fun a b => ?_, ?_, fun a b => ?_⟩
  · change (⟪((SeparationQuotient.mk a : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V)),
      ((SeparationQuotient.mk b : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V))⟫ : ℂ) = _
    rw [UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
  · exact UniformSpace.Completion.denseRange_coe.comp
      SeparationQuotient.surjective_mk.denseRange
      (UniformSpace.Completion.continuous_coe _)
  · -- `η a = η b` iff `mk a = mk b` (the completion map is injective on the
    -- T0 separation quotient) iff `d(a,b) = 0` iff `‖a−b‖ = 0`.
    have h1 : (((SeparationQuotient.mk a : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V)) =
      ((SeparationQuotient.mk b : SeparationQuotient V) :
        UniformSpace.Completion (SeparationQuotient V))) ↔
        (SeparationQuotient.mk a : SeparationQuotient V) = SeparationQuotient.mk b :=
      UniformSpace.Completion.coe_inj
    have h2 : (SeparationQuotient.mk a : SeparationQuotient V) = SeparationQuotient.mk b
        ↔ dist a b = 0 := by
      rw [SeparationQuotient.mk_eq_mk, Metric.inseparable_iff]
    have h3 : dist a b = innerNorm (a - b) := by
      rw [dist_eq_norm]
      rfl
    rw [← h3, ← h2, ← h1]
    exact Iff.rfl

end DegenerateInner

/-- **30V** (`inner-product-completion`, cstar.tex:4733, Exercise), the
uniform-extension clause: every uniformly continuous map `f : V → X` into a
complete space extends *uniquely* to a uniformly continuous map on the
completion `H` of `V` (where "`g` extends `f`" means `f = g ∘ η`). -/
theorem inner_product_completion_extension (V : Type v) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {X : Type*} [UniformSpace X] [T0Space X]
    [CompleteSpace X] (f : V → X) (hf : UniformContinuous f) :
    ∃! g : UniformSpace.Completion V → X,
      UniformContinuous g ∧ ∀ v : V, g (v : UniformSpace.Completion V) = f v := by
  refine ⟨UniformSpace.Completion.extension f,
    ⟨UniformSpace.Completion.uniformContinuous_extension,
      fun v => UniformSpace.Completion.extension_coe hf v⟩, ?_⟩
  rintro g ⟨hgc, hg⟩
  exact (UniformSpace.Completion.extension_unique hf hgc fun v => (hg v).symm).symm

/-- **30V** (`inner-product-completion`, cstar.tex:4733, Exercise), the final
clause: every bounded linear map `f : V → K` into a Hilbert space `K` extends
*uniquely* to a bounded linear map on the completion `H` of `V`.

This is the clause **30VI** uses to build `ϱ_ω(a)` from `b ↦ ab`. -/
theorem inner_product_completion_extendL (V : Type v) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (f : V →L[ℂ] K) :
    ∃! g : UniformSpace.Completion V →L[ℂ] K,
      ∀ v : V, g (v : UniformSpace.Completion V) = f v := by
  have hd : DenseRange (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := V)) :=
    UniformSpace.Completion.denseRange_coe
  have hi : IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := V)) :=
    UniformSpace.Completion.isUniformInducing_coe V
  refine ⟨ContinuousLinearMap.extend f UniformSpace.Completion.toComplL,
    fun v => ContinuousLinearMap.extend_eq f hd hi v, ?_⟩
  intro g hg
  refine (ContinuousLinearMap.extend_unique f hd hi g ?_).symm
  ext v
  exact hg v

/-! **30VI** (`gns`, cstar.tex:4779, Definition (Gelfand–Naimark–Segal
construction)): for a p-map `ω : 𝒜 → ℂ`, the Hilbert space `ℋ_ω` is the
completion of `𝒜` under `[·,·]_ω`, with embedding `η_ω : 𝒜 → ℋ_ω`, and
`ϱ_ω(a) : ℋ_ω → ℋ_ω` is the continuous extension of `b ↦ ab`.  In Mathlib
(`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`), for
`ω : 𝒜 →ₚ[ℂ] ℂ`: `ω.PreGNS` (= `𝒜` with the `[·,·]_ω` inner product),
`ω.GNS` (its completion), and `ω.gnsStarAlgHom : 𝒜 →⋆ₐ[ℂ] B(ω.GNS)`. -/

/-- **30VII** (cstar.tex:4812, Proposition): `ϱ_ω : 𝒜 → B(ℋ_ω)` is an
miu-map — Mathlib's `ω.gnsStarAlgHom` is bundled as one; the defining
property `ϱ_ω(a) η_ω(b) = η_ω(ab)` is recorded here. -/
theorem gns_starAlgHom_apply (ω : 𝒜 →ₚ[ℂ] ℂ) (a b : 𝒜) :
    ω.gnsStarAlgHom a ((ω.toPreGNS b : ω.PreGNS) : ω.GNS) =
      ((ω.toPreGNS (a * b) : ω.PreGNS) : ω.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom]

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
that `a ≥ 0` it suffices to show that `ϱ_Ω(a) ≥ 0`" (cstar.tex:5024).  The
argument is **17V**'s norm criterion for positivity: `0 ≤ ρ x` gives
`‖ρ x − t‖ ≤ t` at `t = ‖ρ x‖/2`, and both norms are unchanged by `ρ`
(**29VIII** `injective_miu_isometry`), so `‖x − t‖ ≤ t` at `t = ‖x‖/2`.
(`A/CStar/Positive.lean` has the same auxiliary for **20aII**, but private.) -/
private theorem nonneg_of_injective_miu {ℬ : Type*} [CStarAlgebra ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (ρ : 𝒜 →⋆ₐ[ℂ] ℬ)
    (hρ : Function.Injective ρ) (x : 𝒜) (h : 0 ≤ ρ x) : 0 ≤ x := by
  have hiso : ∀ y : 𝒜, ‖ρ y‖ = ‖y‖ := injective_miu_isometry ρ hρ
  have hisa : IsSelfAdjoint (ρ x) := IsSelfAdjoint.of_nonneg h
  have hsa : IsSelfAdjoint x := hρ (by rw [map_star, hisa.star_eq])
  have ht' : ‖ρ x‖ / 2 ≤ ‖x‖ / 2 := by rw [hiso]
  have hfwd : (0 : ℬ) ≤ ρ x ↔
      ∀ t : ℝ, ‖ρ x‖ / 2 ≤ t → ‖ρ x - algebraMap ℂ ℬ (t : ℂ)‖ ≤ t :=
    (cstar_positive_tfae (ρ x) hisa).out 3 1
  have h2 : ‖ρ x - algebraMap ℂ ℬ ((‖x‖ / 2 : ℝ) : ℂ)‖ ≤ ‖x‖ / 2 :=
    hfwd.mp h (‖x‖ / 2) ht'
  have h3 : ρ (x - algebraMap ℂ 𝒜 ((‖x‖ / 2 : ℝ) : ℂ))
      = ρ x - algebraMap ℂ ℬ ((‖x‖ / 2 : ℝ) : ℂ) := by
    rw [map_sub]
    congr 1
    exact AlgHomClass.commutes ρ _
  rw [← h3, hiso] at h2
  have hbwd : (∃ t : ℝ, ‖x‖ / 2 ≤ t ∧ ‖x - algebraMap ℂ 𝒜 (t : ℂ)‖ ≤ t) ↔ (0 : 𝒜) ≤ x :=
    (cstar_positive_tfae x hsa).out 0 3
  exact hbwd.mp ⟨‖x‖ / 2, le_rfl, h2⟩

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
(2) ⇒ (1) and final claim: if `Ω` is centre separating then `ϱ_Ω` is
injective, so `𝒜` is miu-isomorphic to a C*-algebra of bounded operators on
the Hilbert space `ℋ_Ω` (by **29IX**).  Stated existentially. -/
theorem proto_gelfand_naimark_2 {ι : Type v} (ω : ι → (𝒜 →ₗ[ℂ] ℂ))
    (hpos : ∀ i, IsPositiveMap (ω i))
    (hc : CentreSeparating (fun i => ω i)) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ρ : 𝒜 →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective ρ :=
  -- `ℋ_Ω = ⊕_{ω∈Ω} ℋ_ω` and `ϱ_Ω` (**30IX**), from the block above
  ⟨lp (fun i => (toPLM (ω i) (hpos i)).GNS) 2, inferInstance, inferInstance,
    inferInstance, _, dsumRep_gns_injective (fun i => toPLM (ω i) (hpos i)) hc⟩

/-- **30X** (`proto-gelfand-naimark`, cstar.tex:4977, Proposition),
equivalence (2) ↔ (3): a collection `Ω` of p-maps on `𝒜` is centre
separating iff `Ω' = { ω(b* (·) b) : ω ∈ Ω, b ∈ 𝒜 }` is order separating.

*Class 1 — faithful.*  Both directions are the Proposition's own proof.
"It is clear that (3) entails (2)" is the second bullet.  For (2) ⇒ (3) the
thesis goes through (1): `ϱ_Ω` is injective by cstar.tex:5002
(`dsumRep_gns_injective`), and then cstar.tex:5018 — by **29IX** it suffices
that `ϱ_Ω(a) ≥ 0` (`nonneg_of_injective_miu`), which holds because each
`ϱ_ω(a) ≥ 0` (`gnsStarAlgHom_nonneg`, by **30XIII** and the density of
`{η_ω(b)}` in `ℋ_ω`).  In particular the self-adjointness of `a` is not
established by hand: it comes free with the positivity of `ϱ_Ω(a)`. -/
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
  · intro hc a
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
      exact nonneg_of_injective_miu _
        (dsumRep_gns_injective (fun i => toPLM (ω i) (hpos i)) hc) a
        (dsumRep_nonneg _ a hcoord)
  · intro ho a ha
    refine ⟨fun h i b => by rw [h]; simp, fun H => ?_⟩
    have h1 : (0 : 𝒜) ≤ -a := by
      refine (ho (-a)).mpr fun p => ?_
      simp only [hconj]
      rw [show star p.2 * (-a) * p.2 = -(star p.2 * a * p.2) by noncomm_ring, map_neg,
        H p.1 p.2, neg_zero]
    exact le_antisymm (neg_nonneg.mp h1) ha

end GNS

/-- **30XIV** (`gelfand-naimark`, cstar.tex:4941, Theorem
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
  exact proto_gelfand_naimark_2 _ hpos hc

end Theses.A.CStar
