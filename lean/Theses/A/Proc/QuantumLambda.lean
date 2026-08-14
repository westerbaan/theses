/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex), §Quantum
Lambda Calculus (parsecs 1200–1255): the ingredients for the model of
Selinger and Valiron's quantum lambda calculus — the first adjunction
`ℓ^∞ ⊣ nsp` between `Set` and `(W*_miu)^op` (122II), the second
adjunction `F ⊣ U` between `W*_cpsu` and `W*_miu` (124III), Kornell's
free exponential (`(-) ⊗ 𝒜 : W*_miu → W*_miu` has a left adjoint,
125VIII), and the hereditarily atomic variants with their concrete
descriptions (parsecs 1251–1255).

## Encoding

* `ℓ^∞(X)` is `lp (fun _ : X => ℂ) ∞` (instances from `Theses/A/VN/
  Basic.lean`); `nsp A = NMIUMap A ℂ` is the set of nmiu-functionals.
* The adjunctions are stated through universal arrows, bundled as
  structures (`FreeMIU`, `FreeExp`, `HaFreeMIU`, `HaFreeExp`) whose
  existence (`Nonempty _`) is the sorry-ed content of the theorems —
  a concrete rendering of "the inclusion/`(-) ⊗ 𝒜` has a left adjoint",
  per the conversion policy's allowance for concrete phrasings of
  categorical statements.
* `HereditarilyAtomic` is reused from `Theses/A/VN/Division.lean`.
  Matrix algebras are `MatAlg n = CStarMatrix (Fin n) (Fin n) ℂ`; in the
  concrete descriptions (125cIII, 125eVII) the summands are rendered as
  `MatAlg (N i + 1)` to keep them nontrivial (as in the encoding of
  `HereditarilyAtomic`).
* Composition of nmiu-maps is the honest `nmiuComp` (star-algebra
  composition; normality sorry-ed).
-/
import Theses.A.Proc.Tensor

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal Cardinal
open Filter Topology Theses Theses.A.VN Cardinal

noncomputable section

namespace Theses.A.Proc

universe u v w

variable {A B C D : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-! ## Infrastructure -/

section NmiuComp

variable {A₁ : Type u} {B₁ : Type v} {C₁ : Type w}
  [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [CStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁]
  [CStarAlgebra C₁] [PartialOrder C₁] [StarOrderedRing C₁]

/-- Infrastructure: composition of nmiu-maps (normality sorry-ed). -/
noncomputable def nmiuComp (g : NMIUMap B₁ C₁) (f : NMIUMap A₁ B₁) :
    NMIUMap A₁ C₁ :=
  { toStarAlgHom := g.toStarAlgHom.comp f.toStarAlgHom
    preservesDirSups' := by
      refine preservesDirSups_comp (f := ⇑f) (g := ⇑g) (fun x hx => ?_)
        (fun x y h => OrderHomClass.mono f.toStarAlgHom h)
        f.preservesDirSups' g.preservesDirSups'
      show IsSelfAdjoint (f.toStarAlgHom x)
      rw [IsSelfAdjoint, ← map_star, hx.star_eq] }

end NmiuComp

section DirectSums

variable {I : Type*} {𝒜 : I → Type*} [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)]

/-- Infrastructure: the coordinate projection `πⱼ : ⊕ᵢ 𝒜ᵢ → 𝒜ⱼ` as a
∗-homomorphism.  (This is `Theses.A.VN.vn_products_proj_normal`'s companion;
that file is closed for editing, so the two live here.) -/
def lpEvalSAH (j : I) : lp 𝒜 ∞ →⋆ₐ[ℂ] 𝒜 j where
  toFun a := (a : ∀ i, 𝒜 i) j
  map_one' := by rw [lp.infty_coeFn_one]; rfl
  map_mul' a b := by rw [lp.infty_coeFn_mul]; rfl
  map_zero' := rfl
  map_add' a b := by rw [lp.coeFn_add]; rfl
  commutes' c := by
    have h : ((algebraMap ℂ (lp 𝒜 ∞) c : lp 𝒜 ∞) : ∀ i, 𝒜 i)
        = fun i => algebraMap ℂ (𝒜 i) c := by
      rw [Algebra.algebraMap_eq_smul_one, lp.coeFn_smul, lp.infty_coeFn_one]
      funext i
      simp [Algebra.algebraMap_eq_smul_one]
    exact congrFun h j
  map_star' a := by rw [lp.coeFn_star]; rfl

omit [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] in
@[simp] theorem lpEvalSAH_apply (j : I) (a : lp 𝒜 ∞) :
    lpEvalSAH j a = (a : ∀ i, 𝒜 i) j := rfl

/-! **47IV**.2 and **47IV**.3 used to be proved here, because `A/VN/Basic.lean`
was closed for editing when they were found.  They now live where they belong,
as `Theses.A.VN.vn_products_proj_normal` and `Theses.A.VN.vn_products_nmiu`,
and the use sites below call those directly.

One remark does not survive the move and is recorded here instead: the proof of
`vn_products_nmiu` uses **no** `VonNeumannAlgebra` hypothesis at all — the
∗-algebra part is **20aI** `cstar_product_2_miu` and normality of the mediating
map follows from normality of the `fᵢ` because the order on `lp 𝒜 ∞` is
pointwise (`lp_infty_le_iff`).  The hypotheses are kept in the A/VN statement
because 47IV is stated there for von Neumann algebras. -/

/-! ### The coprojections `κᵢ : 𝒜ᵢ → ⊕ⱼ 𝒜ⱼ`

Infrastructure for **122IV** (`nmiu-functional-product`): the *nmisu*-maps
`κᵢ` of proc.tex:4595, the finite partial sums `∑_{j ∈ F} κⱼ(1)` (whose
supremum is `1`), and the fact that an nmiu-functional is `1` on exactly one
`κᵢ(1)`. -/

open Classical in
def lpKappa (i : I) (a : 𝒜 i) : lp 𝒜 ∞ := lp.single ∞ i a

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_mul_left (i : I) (x : lp 𝒜 ∞) :
    lpKappa i (1 : 𝒜 i) * x = lpKappa i ((x : ∀ j, 𝒜 j) i) := by
  apply lp.ext
  funext j
  rw [lp.infty_coeFn_mul]
  simp only [lpKappa, lp.coeFn_single, Pi.mul_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_mul (i : I) (a b : 𝒜 i) :
    lpKappa i a * lpKappa i b = lpKappa i (a * b) := by
  apply lp.ext
  funext j
  rw [lp.infty_coeFn_mul]
  simp only [lpKappa, lp.coeFn_single, Pi.mul_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_sa (i : I) : IsSelfAdjoint (lpKappa i (1 : 𝒜 i)) := by
  show star _ = _
  apply lp.ext
  funext j
  rw [lp.coeFn_star]
  simp only [lpKappa, lp.coeFn_single, Pi.star_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

open Classical in
noncomputable def lpSumSA (F : Finset I) : selfAdjoint (lp 𝒜 ∞) :=
  ⟨∑ j ∈ F, lpKappa j (1 : 𝒜 j), by
    show star _ = _
    rw [star_sum]
    exact Finset.sum_congr rfl fun j _ => lpKappa_sa j⟩

omit [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpSumSA_apply (F : Finset I) (i : I) :
    (((lpSumSA F : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞) : ∀ k, 𝒜 k) i
      = if i ∈ F then 1 else 0 := by
  have h := map_sum (lpEvalSAH (𝒜 := 𝒜) i) (fun j => lpKappa j (1 : 𝒜 j)) F
  simp only [lpEvalSAH_apply] at h
  show ((∑ j ∈ F, lpKappa j (1 : 𝒜 j) : lp 𝒜 ∞) : ∀ k, 𝒜 k) i = _
  rw [h]
  simp only [lpKappa, lp.coeFn_single]
  exact Finset.sum_pi_single i (fun _ => 1) F

open Classical in
theorem lpSumSA_isLUB :
    IsLUB (Set.range (lpSumSA (𝒜 := 𝒜))) ⟨1, IsSelfAdjoint.one _⟩ := by
  have hone : ∀ i : I, ((1 : lp 𝒜 ∞) : ∀ k, 𝒜 k) i = 1 := by
    intro i; rw [lp.infty_coeFn_one]; rfl
  constructor
  · rintro _ ⟨F, rfl⟩
    rw [← Subtype.coe_le_coe, lp_infty_le_iff]
    intro i
    rw [lpSumSA_apply]
    show _ ≤ ((1 : lp 𝒜 ∞) : ∀ k, 𝒜 k) i
    rw [hone]
    split
    · exact le_rfl
    · exact zero_le_one
  · intro u hu
    rw [← Subtype.coe_le_coe, lp_infty_le_iff]
    intro i
    have h := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr (hu ⟨{i}, rfl⟩)) i
    rw [lpSumSA_apply] at h
    simp only [Finset.mem_singleton] at h
    show ((1 : lp 𝒜 ∞) : ∀ k, 𝒜 k) i ≤ _
    rw [hone]
    exact h

open Classical in
theorem exists_kappa_one (φ : NMIUMap (lp 𝒜 ∞) ℂ) :
    ∃ i, φ (lpKappa i (1 : 𝒜 i)) = 1 := by
  have hψ : ∀ x : lp 𝒜 ∞, φ x = φ.toStarAlgHom x := fun _ => rfl
  by_contra hcon
  simp only [not_exists] at hcon
  have hzero : ∀ j, φ (lpKappa j (1 : 𝒜 j)) = 0 := by
    intro j
    have hid : φ (lpKappa j (1 : 𝒜 j)) * φ (lpKappa j (1 : 𝒜 j))
        = φ (lpKappa j (1 : 𝒜 j)) := by
      rw [hψ, ← map_mul φ.toStarAlgHom, lpKappa_mul, mul_one]
    have h0 : φ (lpKappa j (1 : 𝒜 j)) * (φ (lpKappa j (1 : 𝒜 j)) - 1) = 0 := by
      linear_combination hid
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd (by linear_combination h) (hcon j)
  have hne : (Set.range (lpSumSA (𝒜 := 𝒜))).Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hmono : ∀ {F G : Finset I}, F ⊆ G → lpSumSA (𝒜 := 𝒜) F ≤ lpSumSA G := by
    intro F G hFG
    rw [← Subtype.coe_le_coe, lp_infty_le_iff]
    intro i
    rw [lpSumSA_apply, lpSumSA_apply]
    split <;> split
    · exact le_rfl
    · exact absurd (hFG ‹_›) ‹_›
    · exact zero_le_one
    · exact le_rfl
  have hdir : DirectedOn (· ≤ ·) (Set.range (lpSumSA (𝒜 := 𝒜))) := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨lpSumSA (F ∪ G), ⟨F ∪ G, rfl⟩, hmono Finset.subset_union_left,
      hmono Finset.subset_union_right⟩
  have hlub := φ.preservesDirSups' _ _ hne hdir lpSumSA_isLUB
  have himg : ((fun d : selfAdjoint (lp 𝒜 ∞) => φ.toStarAlgHom (d : lp 𝒜 ∞)) ''
      Set.range (lpSumSA (𝒜 := 𝒜))) = {0} := by
    ext z
    simp only [Set.mem_image, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨F, rfl⟩, rfl⟩
      show φ.toStarAlgHom (∑ j ∈ F, lpKappa j (1 : 𝒜 j)) = 0
      rw [map_sum φ.toStarAlgHom]
      exact Finset.sum_eq_zero fun j _ => (hψ _) ▸ hzero j
    · rintro rfl
      refine ⟨lpSumSA ∅, ⟨∅, rfl⟩, ?_⟩
      show φ.toStarAlgHom (∑ j ∈ (∅ : Finset I), lpKappa j (1 : 𝒜 j)) = 0
      simp
  rw [himg] at hlub
  have h1 : φ.toStarAlgHom ((⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint (lp 𝒜 ∞))
      : lp 𝒜 ∞) = 1 := map_one φ.toStarAlgHom
  rw [h1] at hlub
  have hle : (1 : ℂ) ≤ 0 := hlub.2 (fun z hz => le_of_eq hz)
  exact absurd hle (by simp [Complex.le_def])

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_star (i : I) (a : 𝒜 i) :
    star (lpKappa i a) = lpKappa i (star a) := by
  apply lp.ext
  funext j
  rw [lp.coeFn_star]
  simp only [lpKappa, lp.coeFn_single, Pi.star_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_apply_self (i : I) (a : 𝒜 i) :
    ((lpKappa i a : lp 𝒜 ∞) : ∀ j, 𝒜 j) i = a := lp.single_apply_self _ _ _

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_apply_ne (i : I) (a : 𝒜 i) {j : I} (h : j ≠ i) :
    ((lpKappa i a : lp 𝒜 ∞) : ∀ k, 𝒜 k) j = 0 := lp.single_apply_ne _ _ _ h

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_sa' (i : I) {a : 𝒜 i} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (lpKappa i a) := by
  show star _ = _
  rw [lpKappa_star, ha.star_eq]

open Classical in
theorem lpKappa_le (i : I) {a b : 𝒜 i} (h : a ≤ b) :
    lpKappa i a ≤ lpKappa i b := by
  rw [lp_infty_le_iff]
  intro j
  by_cases hj : j = i
  · subst hj; rw [lpKappa_apply_self, lpKappa_apply_self]; exact h
  · rw [lpKappa_apply_ne _ _ hj, lpKappa_apply_ne _ _ hj]


/-- **122IV** (`nmiu-functional-product`, proc.tex:4585, Lemma), in its
universe-polymorphic form: an nmiu-functional on a direct sum `⊕ᵢ 𝒜ᵢ`
factors as `φ' ∘ πᵢ`.  (The statement `nmiu_functional_product` below is
this one; it is restated there because the section it belongs to fixes
`𝒜 : I → Type u`, which excludes `ℓ^∞(X) = ⊕_{x ∈ X} ℂ`.)

Following proc.tex:4595, except that the thesis's step `φ(eᵢ^⊥) = 0` is
replaced by the observation that `φ(x) = φ(eᵢ)φ(x)` is immediate from
multiplicativity once `φ(eᵢ) = 1`; and the existence of an `i` with
`φ(eᵢ) = 1` — which the thesis leaves implicit — is where normality is
used: `1 = ⋁_F ∑_{j ∈ F} eⱼ` is a directed supremum. -/
theorem lp_nmiu_functional_factors (φ : NMIUMap (lp 𝒜 ∞) ℂ) :
    ∃ (i : I) (φ' : NMIUMap (𝒜 i) ℂ),
      ∀ x : lp 𝒜 ∞, φ x = φ' ((x : ∀ j, 𝒜 j) i) := by
  classical
  classical
  obtain ⟨i, hi⟩ := exists_kappa_one φ
  have hψ : ∀ x : lp 𝒜 ∞, φ x = φ.toStarAlgHom x := fun _ => rfl
  refine ⟨i, ⟨{ toFun := fun a => φ (lpKappa i a)
                map_one' := hi
                map_mul' := fun a b => by
                  rw [← lpKappa_mul, hψ, hψ, hψ, map_mul]
                map_zero' := by
                  rw [hψ]
                  show φ.toStarAlgHom (lp.single ∞ i (0 : 𝒜 i)) = 0
                  rw [lp.single_zero, map_zero]
                map_add' := fun a b => by
                  rw [hψ, hψ, hψ]
                  show φ.toStarAlgHom (lp.single ∞ i (a + b)) = _
                  rw [lp.single_add, map_add]
                  rfl
                commutes' := fun c => by
                  rw [Algebra.algebraMap_eq_smul_one]
                  show φ (lp.single ∞ i (c • (1 : 𝒜 i))) = _
                  rw [lp.single_smul, hψ, map_smul]
                  show c • φ (lpKappa i (1 : 𝒜 i)) = _
                  rw [hi, smul_eq_mul, mul_one]
                  simp
                map_star' := fun a => by
                  rw [hψ, hψ, ← lpKappa_star, map_star] }, ?_⟩, ?_⟩
  · -- normality
    intro D s hne hdir hlub
    set κ : selfAdjoint (𝒜 i) → selfAdjoint (lp 𝒜 ∞) :=
      fun d => ⟨lpKappa i (d : 𝒜 i), lpKappa_sa' i d.2⟩ with hκ
    have hκmono : ∀ {a b : selfAdjoint (𝒜 i)}, a ≤ b → κ a ≤ κ b := by
      intro a b h
      rw [← Subtype.coe_le_coe]
      exact lpKappa_le i (Subtype.coe_le_coe.mpr h)
    have hlub' : IsLUB (κ '' D) (κ s) := by
      constructor
      · rintro _ ⟨d, hd, rfl⟩
        exact hκmono (hlub.1 hd)
      · intro u hu
        obtain ⟨d₀, hd₀⟩ := hne
        rw [← Subtype.coe_le_coe, lp_infty_le_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          rw [hκ]
          simp only
          rw [lpKappa_apply_self]
          have hub : (⟨((u : lp 𝒜 ∞) : ∀ k, 𝒜 k) j,
              lp_infty_isSelfAdjoint u.2 j⟩ : selfAdjoint (𝒜 j)) ∈ upperBounds D := by
            intro d hd
            have := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr (hu ⟨d, hd, rfl⟩)) j
            rw [← Subtype.coe_le_coe]
            simpa [hκ, lpKappa_apply_self] using this
          exact hlub.2 hub
        · rw [hκ]
          simp only
          rw [lpKappa_apply_ne _ _ hj]
          have := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr (hu ⟨d₀, hd₀, rfl⟩)) j
          rwa [show ((κ d₀ : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞) = lpKappa i (d₀ : 𝒜 i) from rfl,
            lpKappa_apply_ne _ _ hj] at this
    have h := φ.preservesDirSups' (κ '' D) (κ s) (hne.image _) ?_ hlub'
    · rwa [Set.image_image] at h
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨κ z, ⟨z, hz, rfl⟩, hκmono hxz, hκmono hyz⟩
  · intro x
    show φ x = φ (lpKappa i ((x : ∀ j, 𝒜 j) i))
    rw [← lpKappa_mul_left, hψ, hψ, map_mul,
      show φ.toStarAlgHom (lpKappa i (1 : 𝒜 i)) = 1 from hi, one_mul]

end DirectSums

variable (X : Type u) in
/-- The commutative von Neumann algebra `ℓ^∞(X)` of bounded functions on a
set `X`, as the `X`-fold direct sum of copies of `ℂ` (vn.tex 50I). -/
abbrev linf : Type u := lp (fun _ : X => ℂ) ∞

/-! ## Parsec 1210: the intersection of concrete tensor products -/

section Concrete

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (H K) in
/-- The "concrete" tensor product of von Neumann subalgebras
`𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)`: the least von Neumann subalgebra of
`B(ℋ ⊗ 𝒦)` containing all `A ⊗ B` with `A ∈ 𝒜`, `B ∈ ℬ` (121II). -/
def concreteTensor (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    StarSubalgebra ℂ (HT H K →L[ℂ] HT H K) :=
  wstar (HT H K →L[ℂ] HT H K)
    {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}

/-- **121II** (`intersection-tensor`, proc.tex:4450, Proposition;
Takesaki IV.5.10): for von Neumann subalgebras `𝒜₁, 𝒜₂ ⊆ B(ℋ)` and
`ℬ₁, ℬ₂ ⊆ B(𝒦)`,
`(𝒜₁ ⊗ ℬ₁) ∩ (𝒜₂ ⊗ ℬ₂) = (𝒜₁ ∩ 𝒜₂) ⊗ (ℬ₁ ∩ ℬ₂)` (concrete tensor
products). -/
theorem intersection_tensor (SA₁ SA₂ : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB₁ SB₂ : StarSubalgebra ℂ (K →L[ℂ] K))
    (hA₁ : IsVNSubalgebra (H →L[ℂ] H) SA₁)
    (hA₂ : IsVNSubalgebra (H →L[ℂ] H) SA₂)
    (hB₁ : IsVNSubalgebra (K →L[ℂ] K) SB₁)
    (hB₂ : IsVNSubalgebra (K →L[ℂ] K) SB₂) :
    concreteTensor H K SA₁ SB₁ ⊓ concreteTensor H K SA₂ SB₂ =
      concreteTensor H K (SA₁ ⊓ SA₂) (SB₁ ⊓ SB₂) := sorry

end Concrete

/-! ## Parsec 1220: the first adjunction -/

variable (A) in
/-- **122I** (proc.tex:4480, Definition): the set `nsp(𝒜)` of
nmiu-functionals on a von Neumann algebra `𝒜` — the object part of the
functor `nsp = W*_miu(·, ℂ) : (W*_miu)^op → Set`. -/
abbrev nsp : Type u := NMIUMap A ℂ

/-- **122I** (proc.tex:4480, Definition), morphism part: an nmiu-map
`f : 𝒜 → ℬ` induces `nsp(f) : nsp(ℬ) → nsp(𝒜)`, `φ ↦ φ ∘ f`. -/
noncomputable def nspMap (f : NMIUMap A B) (φ : nsp B) : nsp A :=
  nmiuComp φ f

/-- **122II** (`first-adjunction`, proc.tex:4493, Proposition),
well-definedness of the unit: for `x ∈ X` evaluation at `x` is an
nmiu-functional on `ℓ^∞(X)`. -/
theorem exists_linfEval (X : Type u) (x : X) :
    ∃ φ : NMIUMap (linf X) ℂ, ∀ f : linf X, φ f = f x :=
  ⟨⟨lpEvalSAH x, vn_products_proj_normal (fun _ : X => ℂ) x⟩, fun _ => rfl⟩

/-- The unit `η : X → nsp(ℓ^∞(X))`, `η(x)(h) = h(x)` (122II). -/
noncomputable def linfEval (X : Type u) (x : X) : nsp (linf X) :=
  (exists_linfEval X x).choose

theorem linfEval_apply (X : Type u) (x : X) (f : linf X) :
    linfEval X x f = (f : ∀ _ : X, ℂ) x :=
  (exists_linfEval X x).choose_spec f

/-- **122II** (`first-adjunction`, proc.tex:4493, Proposition): the map
`η : X → nsp(ℓ^∞(X))` is universal: for every map `f : X → nsp(𝒜)` there
is a unique nmiu-map `g : 𝒜 → ℓ^∞(X)` with `nsp(g) ∘ η = f`.  (Hence
`X ↦ ℓ^∞(X)` extends to a functor `Set → (W*_miu)^op` left adjoint to
`nsp`; its action on maps is `linfMap` below.) -/
theorem first_adjunction [VonNeumannAlgebra A] (X : Type u)
    (f : X → nsp A) :
    ∃! g : NMIUMap A (linf X),
      ∀ (x : X) (a : A), (f x) a = linfEval X x (g a) := by
  obtain ⟨g, hg, huniq⟩ := vn_products_nmiu (fun _ : X => ℂ) f
  refine ⟨g, fun x a => ?_, fun g' hg' => huniq g' fun x a => ?_⟩
  · rw [linfEval_apply, hg x a]
  · rw [← linfEval_apply, ← hg' x a]

/-- **122II** (`first-adjunction`, proc.tex:4493, Proposition), the
functor `ℓ^∞` on maps: `ℓ^∞(f)(h) = h ∘ f` is an nmiu-map
`ℓ^∞(Y) → ℓ^∞(X)`. -/
theorem exists_linfMap {X Y : Type u} (f : X → Y) :
    ∃ h : NMIUMap (linf Y) (linf X),
      ∀ (g : linf Y) (x : X), h g x = g (f x) := by
  obtain ⟨h, hh, -⟩ :=
    vn_products_nmiu (fun _ : X => ℂ) (fun x => linfEval Y (f x))
  exact ⟨h, fun g x => (hh x g).trans (linfEval_apply Y (f x) g)⟩

/-- The nmiu-map `ℓ^∞(f) : ℓ^∞(Y) → ℓ^∞(X)` for `f : X → Y` (122II). -/
noncomputable def linfMap {X Y : Type u} (f : X → Y) :
    NMIUMap (linf Y) (linf X) := (exists_linfMap f).choose

section Sums

variable {I : Type u} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]

/-- **122IV** (`nmiu-functional-product`, proc.tex:4585, Lemma): an
nmiu-functional on a direct sum `⊕ᵢ 𝒜ᵢ` is of the form `φ' ∘ πᵢ` for
some `i` and nmiu-functional `φ'` on `𝒜ᵢ`.

*Hypothesis not used*: the proof never needs the summands to be von Neumann
algebras — normality of `φ` alone does the work (the `unusedSectionVars`
warning is left in place as the evidence).  The universe-polymorphic form is
`lp_nmiu_functional_factors` above; only that form applies to `ℓ^∞(X)`. -/
theorem nmiu_functional_product (φ : NMIUMap (lp 𝒜 ∞) ℂ) :
    ∃ (i : I) (φ' : NMIUMap (𝒜 i) ℂ), ∀ x : lp 𝒜 ∞, φ x = φ' (x i) :=
  lp_nmiu_functional_factors φ


/-- **122VI** (`cor:linf-ff`, proc.tex:4612, Exercise), part 1: the
functor `nsp` preserves coproducts: every nmiu-functional on `⊕ᵢ 𝒜ᵢ`
factors through exactly one summand. -/
theorem cor_linf_ff_1 (φ : NMIUMap (lp 𝒜 ∞) ℂ) :
    ∃! p : Σ i : I, nsp (𝒜 i), ∀ x : lp 𝒜 ∞, φ x = p.2 (x p.1) := by
  classical
  obtain ⟨i, φ', hφ'⟩ := nmiu_functional_product 𝒜 φ
  have hone : φ (lpKappa i (1 : 𝒜 i)) = 1 := by
    rw [hφ' (lpKappa i 1), lpKappa_apply_self]
    exact map_one φ'.toStarAlgHom
  refine ⟨⟨i, φ'⟩, hφ', ?_⟩
  rintro ⟨j, ψ⟩ hψ
  replace hψ : ∀ x : lp 𝒜 ∞, φ x = ψ ((x : ∀ k, 𝒜 k) j) := hψ
  obtain rfl : j = i := by
    by_contra hne
    have h := hψ (lpKappa i (1 : 𝒜 i))
    have hz : ψ (0 : 𝒜 j) = 0 := map_zero ψ.toStarAlgHom
    rw [lpKappa_apply_ne i 1 hne, hz, hone] at h
    exact one_ne_zero h
  have hcoe : ψ = φ' := by
    apply DFunLike.coe_injective
    funext a
    have h1 := hψ (lpKappa j a)
    have h2 := hφ' (lpKappa j a)
    rw [lpKappa_apply_self] at h1 h2
    rw [← h1, ← h2]
  rw [hcoe]

end Sums

/-- **122VI** (`cor:linf-ff`, proc.tex:4612, Exercise), part 2: the unit
`η : X → nsp(ℓ^∞(X))` is a bijection. -/
theorem cor_linf_ff_2 (X : Type u) : Function.Bijective (linfEval X) := by
  classical
  have hid : ∀ (ψ : NMIUMap ℂ ℂ) (c : ℂ), ψ c = c := fun ψ c => by
    have h : ψ.toStarAlgHom c = c := by simpa using ψ.toStarAlgHom.commutes c
    exact h
  constructor
  · intro x y hxy
    by_contra hne
    have h := congrArg (fun φ : nsp (linf X) => φ (lpKappa (𝒜 := fun _ : X => ℂ) x 1)) hxy
    simp only [linfEval_apply] at h
    rw [lpKappa_apply_self, lpKappa_apply_ne x 1 (Ne.symm hne)] at h
    exact one_ne_zero h
  · intro φ
    obtain ⟨i, φ', hφ'⟩ := lp_nmiu_functional_factors (𝒜 := fun _ : X => ℂ) φ
    refine ⟨i, ?_⟩
    apply DFunLike.coe_injective
    funext f
    rw [linfEval_apply, hφ' f, hid φ']

/-- **122VI** (`cor:linf-ff`, proc.tex:4612, Exercise), part 3: the
functor `ℓ^∞ : Set → (W*_miu)^op` is full and faithful; whence `Set` is
(isomorphic to) a coreflective subcategory of `(W*_miu)^op`. -/
theorem cor_linf_ff_3 (X Y : Type u) :
    Function.Injective (linfMap : (X → Y) → NMIUMap (linf Y) (linf X)) ∧
      ∀ h : NMIUMap (linf Y) (linf X), ∃ f : X → Y, h = linfMap f := by
  classical
  have hspec : ∀ (f : X → Y) (g : linf Y) (x : X),
      ((linfMap f g : linf X) : ∀ _ : X, ℂ) x = (g : ∀ _ : Y, ℂ) (f x) :=
    fun f => (exists_linfMap f).choose_spec
  refine ⟨fun f g hfg => ?_, fun h => ?_⟩
  · funext x
    by_contra hne
    have h1 := hspec f (lpKappa (𝒜 := fun _ : Y => ℂ) (f x) 1) x
    have h2 := hspec g (lpKappa (𝒜 := fun _ : Y => ℂ) (f x) 1) x
    rw [hfg, h2, lpKappa_apply_ne _ _ (Ne.symm hne)] at h1
    rw [lpKappa_apply_self] at h1
    exact one_ne_zero h1.symm
  · choose f hf using fun x => (cor_linf_ff_2 Y).2 (nmiuComp (linfEval X x) h)
    refine ⟨f, ?_⟩
    apply DFunLike.coe_injective
    funext g
    apply lp.ext
    funext x
    rw [hspec f g x]
    have hx : linfEval Y (f x) g = nmiuComp (linfEval X x) h g :=
      congrArg (fun ψ : nsp (linf Y) => ψ g) (hf x)
    rw [linfEval_apply,
      show nmiuComp (linfEval X x) h g = linfEval X x (h g) from rfl,
      linfEval_apply] at hx
    exact hx.symm

/-! ## Parsec 1230: `ℓ^∞` and `nsp` are strong monoidal -/

/-- **123I** (proc.tex:4628, Exercise), part 1: the indicator functions
`x̂ = single x 1` generate `ℓ^∞(X)`. -/
theorem linf_generated (X : Type u) [DecidableEq X] :
    wstar (linf X) {f : linf X | ∃ x : X, f = lp.single ∞ x 1} = ⊤ := sorry

/-- **123I** (proc.tex:4628, Exercise), part 2: the coordinate projections
`π_x : ℓ^∞(X) → ℂ` form an order separating collection of
nmiu-functionals on `ℓ^∞(X)`. -/
theorem linf_projections_order_separating (X : Type u) (f g : linf X)
    (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g)
    (h : ∀ x : X, (f x).re ≤ (g x).re) : f ≤ g := by
  rw [lp_infty_le_iff]
  intro x
  rw [Complex.le_def]
  refine ⟨h x, ?_⟩
  rw [Complex.conj_eq_iff_im.mp (lp_infty_isSelfAdjoint hf x),
    Complex.conj_eq_iff_im.mp (lp_infty_isSelfAdjoint hg x)]

/-- **123I** (proc.tex:4628, Exercise), part 3: the map
`⊗ : ℓ^∞(X) × ℓ^∞(Y) → ℓ^∞(X × Y)`, `(f ⊗ g)(x,y) = f(x)g(y)` is a
tensor product; whence `ℓ^∞(X × Y) ≅ ℓ^∞(X) ⊗ ℓ^∞(Y)` (and `ℓ^∞` is
strong monoidal). -/
theorem linf_tensor (X Y : Type u) :
    ∃ γ : linf X →ₗ[ℂ] linf Y →ₗ[ℂ] linf (X × Y),
      (∀ (f : linf X) (g : linf Y) (x : X) (y : Y),
        γ f g (x, y) = f x * g y) ∧ IsTensorProduct γ := sorry

/-- **123II** (proc.tex:4663, Exercise), part 1: an nmiu-functional `φ` on
`𝒜 ⊗ ℬ` restricts to nmiu-functionals `σ = φ((·) ⊗ 1)` and
`τ = φ(1 ⊗ (·))` with `φ(a ⊗ b) = σ(a)τ(b)`. -/
theorem nsp_tensor_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NMIUMap (VNT A B) ℂ) :
    ∃ (σ : NMIUMap A ℂ) (τ : NMIUMap B ℂ),
      (∀ a : A, σ a = φ (a ⊗ᵥ 1)) ∧ (∀ b : B, τ b = φ (1 ⊗ᵥ b)) ∧
        ∀ (a : A) (b : B), φ (a ⊗ᵥ b) = σ a * τ b := sorry

/-- **123II** (proc.tex:4663, Exercise), part 2: `(σ, τ) ↦ σ ⊗ τ` gives a
bijection `nsp(𝒜) × nsp(ℬ) → nsp(𝒜 ⊗ ℬ)` (which makes `nsp` strong
monoidal) — rendered: every pair extends uniquely to a product
nmiu-functional. -/
theorem nsp_tensor_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (σ : NMIUMap A ℂ) (τ : NMIUMap B ℂ) :
    ∃! φ : NMIUMap (VNT A B) ℂ,
      ∀ (a : A) (b : B), φ (a ⊗ᵥ b) = σ a * τ b := sorry

/-! ## Parsec 1240: the second adjunction -/

/-- **124I** (`vn-generation-bound`, proc.tex:4688, Lemma): if a von
Neumann algebra `𝒜` is generated by `S ⊆ 𝒜`, then
`#𝒜 ≤ 2^(2^(#ℂ + #S))`. -/
theorem vn_generation_bound [VonNeumannAlgebra A] (S : Set A)
    (hS : wstar A S = ⊤) :
    #A ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (Cardinal.continuum + #S)) := sorry

variable (A) in
/-- **124III** (`second-adjunction`, proc.tex:4718, Theorem), bundled: a
universal arrow from the von Neumann algebra `𝒜` to the inclusion
`W*_miu → W*_cpsu`: an object `F(𝒜)` with an ncpsu-unit `η : 𝒜 → F(𝒜)`
through which every ncpsu-map into a von Neumann algebra factors by a
unique nmiu-map. -/
structure FreeMIU [VonNeumannAlgebra A] : Type (u + 1) where
  carrier : Type u
  [cstar : CStarAlgebra carrier]
  [po : PartialOrder carrier]
  [sor : StarOrderedRing carrier]
  [vna : VonNeumannAlgebra carrier]
  unit : NCPSUMap A carrier
  universal : ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : NCPSUMap A B),
    ∃! g : NMIUMap carrier B,
      ∀ a : A, f.toNCPMap a = g (unit.toNCPMap a)

attribute [instance] FreeMIU.cstar FreeMIU.po FreeMIU.sor FreeMIU.vna

variable (A) in
/-- **124III** (`second-adjunction`, proc.tex:4718, Theorem): the
inclusion `W*_miu → W*_cpsu` has a left adjoint `F` — rendered: every von
Neumann algebra has a universal arrow to the inclusion. -/
theorem second_adjunction [VonNeumannAlgebra A] : Nonempty (FreeMIU A) :=
  sorry

/-! ## Parsec 1250: the free exponential -/

variable (A) in
/-- **125II** (`vn-gns-bound`, proc.tex:4814, Lemma), bundled: a faithful
representation of a von Neumann algebra on a Hilbert space. -/
structure ConcreteRep [VonNeumannAlgebra A] : Type (u + 1) where
  space : Type u
  [nacg : NormedAddCommGroup space]
  [ips : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]
  rep : NMIUMap A (space →L[ℂ] space)
  injective : Function.Injective ⇑rep

attribute [instance] ConcreteRep.nacg ConcreteRep.ips ConcreteRep.complete

variable (A) in
/-- **125II** (`vn-gns-bound`, proc.tex:4814, Lemma): a von Neumann
algebra `𝒜` can be faithfully represented on a Hilbert space with no more
than `2^#𝒜` vectors. -/
theorem vn_gns_bound [VonNeumannAlgebra A] :
    ∃ r : ConcreteRep A, #r.space ≤ (2 : Cardinal.{u}) ^ #A := sorry

/-- **125IV** (`equaliser-lemma`, proc.tex:4846, Lemma (Kornell)): every
nmiu-map `h : 𝒟 → 𝒜 ⊗ 𝒞` factors as `(ι ⊗ id) ∘ h̃` through
`𝒜̃ ⊗ 𝒞` for a von Neumann subalgebra `𝒜̃ ⊆ 𝒜` generated by at most
`#𝒟 · 2^#𝒞` elements, such that nmiu-maps `f, g : 𝒜 → ℬ` with
`(f ⊗ id) ∘ h = (g ⊗ id) ∘ h` agree on `𝒜̃`. -/
theorem equaliser_lemma [VonNeumannAlgebra A] [VonNeumannAlgebra C]
    [VonNeumannAlgebra D] (h : NMIUMap D (VNT A C)) :
    ∃ (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) (G : Set A),
      S = wstar A G ∧ #G ≤ #D * (2 : Cardinal.{u}) ^ #C ∧
      ∃ (ι : NMIUMap (VNSub A S hS) A)
        (ht : NMIUMap D (VNT (VNSub A S hS) C)),
        (∀ x : VNSub A S hS, ι x = x.val) ∧
        (∀ d : D, h d = tmapM ι (nmiuId C) (ht d)) ∧
        ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B]
          [StarOrderedRing B] [VonNeumannAlgebra B] (f g : NMIUMap A B),
          (∀ d : D, tmapM f (nmiuId C) (h d) =
            tmapM g (nmiuId C) (h d)) →
          ∀ x : VNSub A S hS, f (ι x) = g (ι x) := sorry

/-- **125VI** (`tensor-equalisers`, proc.tex:4972, Proposition),
definition part: `e : ℰ → 𝒜` is an **equaliser** of nmiu-maps
`f, g : 𝒜 → ℬ` when `f ∘ e = g ∘ e` and every nmiu-map `h` with
`f ∘ h = g ∘ h` factors uniquely through `e`. -/
def IsNMIUEqualizer {E : Type u} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (f g : NMIUMap A B) (e : NMIUMap E A) : Prop :=
  (∀ x : E, f (e x) = g (e x)) ∧
    ∀ (D' : Type u) [CStarAlgebra D'] [PartialOrder D']
      [StarOrderedRing D'] [VonNeumannAlgebra D'] (h : NMIUMap D' A),
      (∀ d, f (h d) = g (h d)) → ∃! k : NMIUMap D' E, ∀ d, h d = e (k d)

/-- **125VI** (`tensor-equalisers`, proc.tex:4972, Proposition): if `e` is
an equaliser of nmiu-maps `f, g : 𝒜 → ℬ`, then `e ⊗ id_𝒞` is an
equaliser of `f ⊗ id` and `g ⊗ id`. -/
theorem tensor_equalisers [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] {E : Type u} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] [VonNeumannAlgebra E] (f g : NMIUMap A B)
    (e : NMIUMap E A) (he : IsNMIUEqualizer f g e) :
    IsNMIUEqualizer (tmapM f (nmiuId C)) (tmapM g (nmiuId C))
      (tmapM e (nmiuId C)) := sorry

section TensorSub

variable (𝒜 : Type u) {ℬ : Type v}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [VonNeumannAlgebra ℬ]

/-- Helper for 125VIIb/125e: the von Neumann subalgebra `𝒮 ⊗ 𝒜` of
`ℬ ⊗ 𝒜` generated by the `s ⊗ a` with `s ∈ 𝒮`, `a ∈ 𝒜`. -/
def tensorSub (S : StarSubalgebra ℂ ℬ) : StarSubalgebra ℂ (VNT ℬ 𝒜) :=
  wstar (VNT ℬ 𝒜) {x : VNT ℬ 𝒜 | ∃ s ∈ S, ∃ a : 𝒜, x = s ⊗ᵥ a}

end TensorSub

/-- **125VIIb** (`tensor-preimage`, proc.tex:5025, Exercise): for an
nmiu-map `ρ : ℬ → 𝒞` and a von Neumann subalgebra `𝒮 ⊆ 𝒞`,
`(ρ ⊗ id_𝒜)⁻¹(𝒮 ⊗ 𝒜) = ρ⁻¹(𝒮) ⊗ 𝒜`. -/
theorem tensor_preimage [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (ρ : NMIUMap B C) (S : StarSubalgebra ℂ C)
    (hS : IsVNSubalgebra C S) :
    ⇑(tmapM ρ (nmiuId A)) ⁻¹' (tensorSub A S : Set (VNT C A)) =
      (tensorSub A (S.comap ρ.toStarAlgHom) : Set (VNT B A)) := sorry

/-- **125VIII** (`tensor-closed`, proc.tex:5048, Theorem (Kornell)),
bundled: a universal arrow witnessing the free exponential: an object
`ℬ^{*𝒜}` with an nmiu-unit `η : ℬ → ℬ^{*𝒜} ⊗ 𝒜` through which every
nmiu-map `ℬ → 𝒞 ⊗ 𝒜` factors by a unique nmiu-map. -/
structure FreeExp (ℬ 𝒜 : Type u)
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [VonNeumannAlgebra ℬ]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [VonNeumannAlgebra 𝒜] : Type (u + 1) where
  carrier : Type u
  [cstar : CStarAlgebra carrier]
  [po : PartialOrder carrier]
  [sor : StarOrderedRing carrier]
  [vna : VonNeumannAlgebra carrier]
  unit : NMIUMap ℬ (VNT carrier 𝒜)
  universal : ∀ (C' : Type u) [CStarAlgebra C'] [PartialOrder C']
    [StarOrderedRing C'] [VonNeumannAlgebra C']
    (h : NMIUMap ℬ (VNT C' 𝒜)),
    ∃! g : NMIUMap carrier C', ∀ b : ℬ, h b = tmapM g (nmiuId 𝒜) (unit b)

attribute [instance] FreeExp.cstar FreeExp.po FreeExp.sor FreeExp.vna

/-- **125VIII** (`tensor-closed`, proc.tex:5048, Theorem (Kornell)): the
functor `(·) ⊗ 𝒜 : W*_miu → W*_miu` has a left adjoint `(·)^{*𝒜}` —
rendered: every `ℬ` has a universal arrow `ℬ → ℬ^{*𝒜} ⊗ 𝒜`. -/
theorem tensor_closed [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    Nonempty (FreeExp B A) := sorry

/- **125X** (`cstar-no-model`, proc.tex:5105, Remark): no analogous free
exponential exists for C*-algebras — remark, not converted. -/

/-! ## Parsecs 1251–1252: the hereditarily atomic second adjunction -/

variable (A) in
/-- **125bII** (proc.tex:5240, Proposition), bundled: a universal arrow
from a hereditarily atomic von Neumann algebra `𝒜` to the inclusion
`haW*_miu → haW*_cpsu`. -/
structure HaFreeMIU [VonNeumannAlgebra A] : Type (u + 1) where
  carrier : Type u
  [cstar : CStarAlgebra carrier]
  [po : PartialOrder carrier]
  [sor : StarOrderedRing carrier]
  [vna : VonNeumannAlgebra carrier]
  ha : HereditarilyAtomic carrier
  unit : NCPSUMap A carrier
  universal : ∀ (B : Type u) [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B], HereditarilyAtomic B →
    ∀ f : NCPSUMap A B, ∃! g : NMIUMap carrier B,
      ∀ a : A, f.toNCPMap a = g (unit.toNCPMap a)

attribute [instance] HaFreeMIU.cstar HaFreeMIU.po HaFreeMIU.sor
  HaFreeMIU.vna

variable (A) in
/-- **125bII** (proc.tex:5240, Proposition): the inclusion
`haW*_miu → haW*_cpsu` has a left adjoint `F_ha`. -/
theorem ha_second_adjunction [VonNeumannAlgebra A]
    (hA : HereditarilyAtomic A) : Nonempty (HaFreeMIU A) := sorry

/-! ## Parsec 1253: concrete description of `F_ha` -/

/-- The full matrix algebra `M_n = M_n(ℂ)` (as `CStarMatrix`). -/
abbrev MatAlg (n : ℕ) : Type := CStarMatrix (Fin n) (Fin n) ℂ

noncomputable instance (n : ℕ) : PartialOrder (MatAlg n) :=
  CStarAlgebra.spectralOrder _

instance (n : ℕ) : StarOrderedRing (MatAlg n) :=
  CStarAlgebra.spectralOrderedRing _

/-- `M_n(ℂ)` is a von Neumann algebra.  This is **49IV**.1
(`Theses.A.VN.mn_vna_1`, vn.tex:1272) at `𝒜 = ℂ`, so it is *not* an
independent obligation: the `sorry` that used to sit here has been
repointed at its owner in `A/VN`.  (Note the `PartialOrder` above is the
same spectral order that `mn_vna_1` is stated against, so the two agree
definitionally.) -/
instance (n : ℕ) : VonNeumannAlgebra (MatAlg n) := Theses.A.VN.mn_vna_1 n

/-- **125cII** (proc.tex:5284): two ncpsu-maps
`f₁ : 𝒜 → M_{n₁}`, `f₂ : 𝒜 → M_{n₂}` are **miu-equivalent** when there
is an nmiu-isomorphism `φ : M_{n₁} → M_{n₂}` with `φ ∘ f₁ = f₂`. -/
def MIUEquiv {n₁ n₂ : ℕ} (f₁ : NCPSUMap A (MatAlg n₁))
    (f₂ : NCPSUMap A (MatAlg n₂)) : Prop :=
  ∃ φ : NMIUMap (MatAlg n₁) (MatAlg n₂), Function.Bijective ⇑φ ∧
    ∀ a : A, φ (f₁.toNCPMap a) = f₂.toNCPMap a

/-- **125cII** (proc.tex:5284): the maps considered in the concrete
description of `F_ha`: ncpsu-maps `f : 𝒜 → M_n` with
`W*(f(𝒜)) = M_n`. -/
def GeneratesMat {n : ℕ} (f : NCPSUMap A (MatAlg n)) : Prop :=
  wstar (MatAlg n) (Set.range ⇑f.toNCPMap) = ⊤

/-- **125cIII** (`Fha-concrete`, proc.tex:5300, Theorem): for a
hereditarily atomic `𝒜` with a set of representatives
`r_i : 𝒜 → M_{N_i+1}` (`i ∈ I`) for miu-equivalence of the generating
ncpsu-maps into matrix algebras, the unique nmiu-map
`Φ : F_ha(𝒜) → ⊕ᵢ M_{N_i+1}` with `Φ ∘ η = ⟨r_i⟩ᵢ` is an
nmiu-isomorphism. -/
theorem Fha_concrete [VonNeumannAlgebra A] (hA : HereditarilyAtomic A)
    (F : HaFreeMIU A) (I : Type u) (N : I → ℕ)
    (r : ∀ i : I, NCPSUMap A (MatAlg (N i + 1)))
    (hgen : ∀ i, GeneratesMat (r i))
    (hdistinct : ∀ i j, i ≠ j → ¬ MIUEquiv (r i) (r j))
    (hrep : ∀ (n : ℕ) (f : NCPSUMap A (MatAlg (n + 1))), GeneratesMat f →
      ∃ i, MIUEquiv (r i) f) :
    ∃ Φ : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
      Function.Bijective ⇑Φ ∧
      (∀ (a : A) (i : I),
        Φ (F.unit.toNCPMap a) i = (r i).toNCPMap a) ∧
      ∀ Φ' : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
        (∀ (a : A) (i : I),
          Φ' (F.unit.toNCPMap a) i = (r i).toNCPMap a) → Φ' = Φ := sorry

/-! ## Parsec 1254: the hereditarily atomic free exponential -/

/-- **125dII** (proc.tex:5528, Proposition), bundled: a universal arrow
witnessing the hereditarily atomic free exponential `ℬ^{*_ha 𝒜}`. -/
structure HaFreeExp (ℬ 𝒜 : Type u)
    [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [VonNeumannAlgebra ℬ]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [VonNeumannAlgebra 𝒜] : Type (u + 1) where
  carrier : Type u
  [cstar : CStarAlgebra carrier]
  [po : PartialOrder carrier]
  [sor : StarOrderedRing carrier]
  [vna : VonNeumannAlgebra carrier]
  ha : HereditarilyAtomic carrier
  unit : NMIUMap ℬ (VNT carrier 𝒜)
  universal : ∀ (C' : Type u) [CStarAlgebra C'] [PartialOrder C']
    [StarOrderedRing C'] [VonNeumannAlgebra C'], HereditarilyAtomic C' →
    ∀ h : NMIUMap ℬ (VNT C' 𝒜),
    ∃! g : NMIUMap carrier C', ∀ b : ℬ, h b = tmapM g (nmiuId 𝒜) (unit b)

attribute [instance] HaFreeExp.cstar HaFreeExp.po HaFreeExp.sor
  HaFreeExp.vna

/-- **125dII** (proc.tex:5528, Proposition): for hereditarily atomic `𝒜`
the functor `(·) ⊗ 𝒜 : haW*_miu → haW*_miu` has a left adjoint
`(·)^{*_ha 𝒜}`. -/
theorem ha_tensor_closed [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (hA : HereditarilyAtomic A) (hB : HereditarilyAtomic B) :
    Nonempty (HaFreeExp B A) := sorry

/-! ## Parsec 1255: concrete description of `(·)^{*_ha 𝒜}` -/

section TensorBSurj

variable {𝒜 : Type u} {ℬ : Type v} {𝒞 : Type w}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [VonNeumannAlgebra ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
  [VonNeumannAlgebra 𝒞]

/-- **125eII** (proc.tex:5557, Definition): an nmiu-map
`s : 𝒜 → 𝒞 ⊗ ℬ` is **`(·) ⊗ ℬ`-surjective** when the only von Neumann
subalgebra `𝒮 ⊆ 𝒞` with `s(𝒜) ⊆ 𝒮 ⊗ ℬ` is `𝒮 = 𝒞`. -/
def TensorBSurjective (s : NMIUMap 𝒜 (VNT 𝒞 ℬ)) : Prop :=
  ∀ S : StarSubalgebra ℂ 𝒞, IsVNSubalgebra 𝒞 S →
    Set.range ⇑s ⊆ (tensorSub ℬ S : Set (VNT 𝒞 ℬ)) → S = ⊤

end TensorBSurj

/-- **125eIIa** (`tensor-map-factorisation`, proc.tex:5569): for any
nmiu-map `s : 𝒜 → 𝒞 ⊗ ℬ` there is a von Neumann subalgebra
`𝒞̃ ⊆ 𝒞` with `s(𝒜) ⊆ 𝒞̃ ⊗ ℬ` such that the restriction of `s` to
`𝒜 → 𝒞̃ ⊗ ℬ` is `(·) ⊗ ℬ`-surjective. -/
theorem tensor_map_factorisation [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] [VonNeumannAlgebra C]
    (s : NMIUMap A (VNT C B)) :
    ∃ (S : StarSubalgebra ℂ C) (hS : IsVNSubalgebra C S),
      Set.range ⇑s ⊆ (tensorSub B S : Set (VNT C B)) ∧
      ∃ (ι : NMIUMap (VNSub C S hS) C)
        (st : NMIUMap A (VNT (VNSub C S hS) B)),
        (∀ x, ι x = x.val) ∧
        (∀ a : A, s a = tmapM ι (nmiuId B) (st a)) ∧
        TensorBSurjective st := sorry

/-- **125eIII** (`tensorBsurjectivity`, proc.tex:5580, Lemma): given a
`(·) ⊗ ℬ`-surjective nmiu-map `s : 𝒜 → 𝒞 ⊗ ℬ` and an nmiu-map
`ρ : 𝒞 → 𝒟`, the composite `(ρ ⊗ ℬ) ∘ s` is `(·) ⊗ ℬ`-surjective iff
`ρ` is surjective. -/
theorem tensorBsurjectivity [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] [VonNeumannAlgebra D]
    (s : NMIUMap A (VNT C B)) (hs : TensorBSurjective s)
    (ρ : NMIUMap C D) :
    TensorBSurjective (nmiuComp (tmapM ρ (nmiuId B)) s) ↔
      Function.Surjective ⇑ρ := sorry

/-- **125eVI** (proc.tex:5630, Definition): two nmiu-maps
`f₁ : 𝒜 → M_{n₁} ⊗ ℬ`, `f₂ : 𝒜 → M_{n₂} ⊗ ℬ` are
**`(·) ⊗ ℬ`-equivalent** when there is an nmiu-isomorphism
`φ : M_{n₁} → M_{n₂}` with `(φ ⊗ ℬ) ∘ f₁ = f₂`. -/
def TensorBEquiv [VonNeumannAlgebra B] {n₁ n₂ : ℕ}
    (f₁ : NMIUMap A (VNT (MatAlg n₁) B))
    (f₂ : NMIUMap A (VNT (MatAlg n₂) B)) : Prop :=
  ∃ φ : NMIUMap (MatAlg n₁) (MatAlg n₂), Function.Bijective ⇑φ ∧
    ∀ a : A, tmapM φ (nmiuId B) (f₁ a) = f₂ a

/-- **125eVII** (`AstarhaB-concrete`, proc.tex:5652, Theorem): for
hereditarily atomic `𝒜`, `ℬ` with a set of representatives
`s_i : 𝒜 → M_{N_i+1} ⊗ ℬ` (`i ∈ I`) for `(·) ⊗ ℬ`-equivalence of the
`(·) ⊗ ℬ`-surjective nmiu-maps into matrix algebras tensor `ℬ`, the
unique nmiu-map `Φ : 𝒜^{*_ha ℬ} → ⊕ᵢ M_{N_i+1}` compatible with the
unit is an nmiu-isomorphism.  (The compatibility
`(π_i ⊗ ℬ)((Φ ⊗ ℬ)(η(a))) = s_i(a)` is rendered through the map
`Φᵢ := (π_i ∘ Φ) ⊗ ℬ` applied to the unit.) -/
theorem AstarhaB_concrete [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (hA : HereditarilyAtomic A) (hB : HereditarilyAtomic B)
    (F : HaFreeExp A B) (I : Type u) (N : I → ℕ)
    (s : ∀ i : I, NMIUMap A (VNT (MatAlg (N i + 1)) B))
    (hsurj : ∀ i, TensorBSurjective (s i))
    (hdistinct : ∀ i j, i ≠ j → ¬ TensorBEquiv (s i) (s j))
    (hrep : ∀ (n : ℕ) (f : NMIUMap A (VNT (MatAlg (n + 1)) B)),
      TensorBSurjective f → ∃ i, TensorBEquiv (s i) f) :
    ∃ Φ : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
      Function.Bijective ⇑Φ ∧
      ∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
        (∀ x : F.carrier, πΦ x = Φ x i) →
        ∀ a : A, tmapM πΦ (nmiuId B) (F.unit a) = s i a := sorry

end Theses.A.Proc
