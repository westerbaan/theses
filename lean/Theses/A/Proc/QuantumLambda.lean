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
  existence (`Nonempty _`) is the content of the theorems — a concrete
  rendering of "the inclusion/`(-) ⊗ 𝒜` has a left adjoint", per the
  conversion policy's allowance for concrete phrasings of categorical
  statements.  Three of the four are **proved**: 124III
  `second_adjunction` (`Nonempty (FreeMIU 𝒜)`), 125bII
  `ha_second_adjunction` (`Nonempty (HaFreeMIU 𝒜)`) and 125dII
  `ha_tensor_closed` (`Nonempty (HaFreeExp ℬ 𝒜)`).  Only 125VIII
  `tensor_closed` (`Nonempty (FreeExp ℬ 𝒜)`) is still `sorry`, being
  blocked on 125IV `equaliser_lemma` and hence on 121II
  `intersection_tensor`.
* `HereditarilyAtomic` is reused from `Theses/A/VN/Division.lean`.
  Matrix algebras are `MatAlg n = CStarMatrix (Fin n) (Fin n) ℂ`; in the
  concrete descriptions (125cIII, 125eVII) the summands are rendered as
  `MatAlg (N i + 1)` to keep them nontrivial (as in the encoding of
  `HereditarilyAtomic`).
* Composition of nmiu-maps is the honest `nmiuComp` of
  `Theses/A/Proc/Tensor.lean`: star-algebra composition, with normality
  (`preservesDirSups'`) **proved** there from `preservesDirSups_comp`
  (`Theses/A/Proc/Measurement.lean`).  Nothing about it is `sorry`-ed.
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
`κᵢ` of proc.tex:4595 live in `Tensor.lean` (117II needs them too); here are
the finite partial sums `∑_{j ∈ F} κⱼ(1)` (whose supremum is `1`), and the
fact that an nmiu-functional is `1` on exactly one `κᵢ(1)`. -/

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
`nsp`; its action on maps is `linfMap` below.)

The Proposition's second sentence — the functor and the adjunction — is
`linfNspAdjunction` in the `Categorical` section below, whose hom-set
equivalence is this `∃!`. -/
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
(isomorphic to) a coreflective subcategory of `(W*_miu)^op`.

Full and faithful are the two clauses below (surjectivity and injectivity
of `f ↦ ℓ^∞(f)` on each hom-set); the "whence" is the instance
`linfCoreflective` in the `Categorical` section below, which reads them as
`Coreflective linfFunctor`. -/
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

/-! ## The categorical form of the first adjunction

`CONVENTIONS.md`: "the categories `CStar_miu`, `W*_nmiu`, `W*_ncpsu`, … are
defined with Mathlib's category theory library when a chapter needs them".
This is where the chapter needs `W*_miu`: **122II**'s second sentence — "and
as a result, `X ↦ ℓ^∞(X)` extends to a functor `Set → (W*_miu)^op` that is
left adjoint to `nsp`" — and the "whence" of **122VI**.3, that `Set` is a
coreflective subcategory of `(W*_miu)^op`.  Neither was stated before
2026-08-21; the audit recorded both as `weaker`.

Nothing here is new mathematics.  `first_adjunction` *is* the hom-set
bijection `W*_miu(𝒜, ℓ^∞(X)) ≅ Set(X, nsp(𝒜))` (universality of `η` in the
`∃!` form), and `cor_linf_ff_3` *is* fullness and faithfulness of `ℓ^∞`; what
follows packages them as `Adjunction` and `Coreflective`, which is exactly the
thesis's own "and as a result".  The objects of `W*_miu` are bundled
`Theses.VonNeumannAlgebra`s and its morphisms are `NMIUMap`s, matching
`B/Eff/WStarCat.lean`'s `WStar` (which cannot be imported here: it belongs to
thesis B). -/

section Categorical

open CategoryTheory


/-- A bundled von Neumann algebra: the object type of `W*_miu`. -/
structure WMIU : Type (u + 1) where
  carrier : Type u
  [cstarAlgebra : CStarAlgebra carrier]
  [partialOrder : PartialOrder carrier]
  [starOrderedRing : StarOrderedRing carrier]
  [vonNeumannAlgebra : Theses.VonNeumannAlgebra carrier]

attribute [instance] WMIU.cstarAlgebra WMIU.partialOrder
  WMIU.starOrderedRing WMIU.vonNeumannAlgebra

instance : CoeSort WMIU.{u} (Type u) := ⟨WMIU.carrier⟩

/-- Bundle a von Neumann algebra as an object of `W*_miu`. -/
def WMIU.of (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Theses.VonNeumannAlgebra A] : WMIU := ⟨A⟩

instance : Category WMIU.{u} where
  Hom A B := NMIUMap A B
  id A := nmiuId A
  comp f g := nmiuComp g f
  id_comp f := DFunLike.coe_injective rfl
  comp_id f := DFunLike.coe_injective rfl
  assoc f g h := DFunLike.coe_injective rfl

/-- A morphism of `W*_miu` *is* an nmiu-map. -/
def WMIU.hom {A B : WMIU.{u}} (f : A ⟶ B) : NMIUMap A B := f

/-- An nmiu-map *is* a morphism of `W*_miu`. -/
def WMIU.ofHom {A B : WMIU.{u}} (f : NMIUMap A B) : A ⟶ B := f

@[simp] theorem WMIU.hom_ofHom {A B : WMIU.{u}} (f : NMIUMap A B) :
    WMIU.hom (WMIU.ofHom f) = f := rfl

theorem WMIU.hom_injective {A B : WMIU.{u}} {f g : A ⟶ B}
    (h : WMIU.hom f = WMIU.hom g) : f = g := h

theorem WMIU.hom_ext {A B : WMIU.{u}} {f g : A ⟶ B}
    (h : ∀ x : A, WMIU.hom f x = WMIU.hom g x) : f = g :=
  WMIU.hom_injective (DFunLike.coe_injective (funext h))

@[simp] theorem WMIU.hom_id {A : WMIU.{u}} (a : A) : WMIU.hom (𝟙 A) a = a := rfl

@[simp] theorem WMIU.hom_comp {A B C : WMIU.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    WMIU.hom (f ≫ g) a = WMIU.hom g (WMIU.hom f a) := rfl

theorem linfMap_apply {X Y : Type u} (f : X → Y) (g : linf Y) (x : X) :
    ((linfMap f g : linf X) : ∀ _ : X, ℂ) x = (g : ∀ _ : Y, ℂ) (f x) :=
  (exists_linfMap f).choose_spec g x

/-- Extensionality for nmiu-maps into `ℓ^∞(X)`. -/
theorem linf_nmiu_ext {X : Type u} {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {h k : NMIUMap A (linf X)}
    (hh : ∀ (a : A) (x : X), ((h a : linf X) : ∀ _ : X, ℂ) x
      = ((k a : linf X) : ∀ _ : X, ℂ) x) : h = k :=
  DFunLike.coe_injective (funext fun a => lp.ext (funext fun x => hh a x))

/-- `nsp : (W*_miu)^op ⥤ Set`. -/
def nspFunctor : WMIU.{u}ᵒᵖ ⥤ Type u where
  obj A := nsp A.unop
  map {A B} f := TypeCat.ofHom (fun φ : nsp A.unop => nspMap (WMIU.hom f.unop) φ)
  map_id A := by
    apply TypeCat.Hom.ext
    apply DFunLike.coe_injective
    funext φ
    exact DFunLike.coe_injective rfl
  map_comp f g := by
    apply TypeCat.Hom.ext
    apply DFunLike.coe_injective
    funext φ
    exact DFunLike.coe_injective rfl

/-- `ℓ^∞ : Set ⥤ (W*_miu)^op`. -/
def linfFunctor : Type u ⥤ WMIU.{u}ᵒᵖ where
  obj X := Opposite.op (WMIU.of (linf X))
  map {X Y} f :=
    Quiver.Hom.op (WMIU.ofHom (A := WMIU.of (linf Y)) (B := WMIU.of (linf X))
      (linfMap (fun x : X => f x)))
  map_id X := by
    apply Quiver.Hom.unop_inj
    refine linf_nmiu_ext fun g x => ?_
    exact linfMap_apply _ g x
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    refine linf_nmiu_ext fun h x => ?_
    exact (linfMap_apply (fun x : X => g (f x)) h x).trans
      ((linfMap_apply (fun y : Y => g y) h (f x)).symm.trans
        (linfMap_apply (fun x : X => f x) (linfMap (fun y : Y => g y) h) x).symm)

/-- The hom-set bijection of the first adjunction: **122II** says exactly
that `η : X → nsp(ℓ^∞(X))` is universal, i.e. that
`W*_miu(𝒜, ℓ^∞(X)) ≅ Set(X, nsp(𝒜))`. -/
def linfNspHomEquiv (X : Type u) (A : WMIU.{u}ᵒᵖ) :
    (linfFunctor.obj X ⟶ A) ≃ (X ⟶ nspFunctor.obj A) where
  toFun g := TypeCat.ofHom
    (fun x : X => nmiuComp (linfEval X x) (WMIU.hom g.unop))
  invFun f := Quiver.Hom.op (WMIU.ofHom
    (A := A.unop) (B := WMIU.of (linf X))
    (first_adjunction (A := A.unop) X (fun x : X => f x)).choose)
  left_inv g := by
    apply Quiver.Hom.unop_inj
    exact ((first_adjunction (A := A.unop) X
      (fun x : X => nmiuComp (linfEval X x) (WMIU.hom g.unop))).choose_spec.2
        (WMIU.hom g.unop) (fun _ _ => rfl)).symm
  right_inv f := by
    apply TypeCat.Hom.ext
    apply DFunLike.coe_injective
    funext x
    show (nmiuComp (linfEval X x)
        (first_adjunction (A := A.unop) X (fun x : X => f x)).choose :
          NMIUMap A.unop ℂ) = (f x : NMIUMap A.unop ℂ)
    exact DFunLike.coe_injective (funext fun a =>
      ((first_adjunction (A := A.unop) X (fun x : X => f x)).choose_spec.1 x a).symm)

/-- **122II** (`first-adjunction`, proc.tex:4493, Proposition), second
sentence: `X ↦ ℓ^∞(X)` is a functor `Set → (W*_miu)^op` and it is **left
adjoint** to `nsp`. -/
def linfNspAdjunction : linfFunctor.{u} ⊣ nspFunctor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := linfNspHomEquiv
      homEquiv_naturality_left_symm := by
        intro X' X A f g
        apply Quiver.Hom.unop_inj
        refine (first_adjunction (A := A.unop) X'
          (fun x' : X' => (f ≫ g) x')).unique
            ((first_adjunction (A := A.unop) X'
              (fun x' : X' => (f ≫ g) x')).choose_spec.1) ?_
        intro x' a
        exact ((first_adjunction (A := A.unop) X
              (fun x : X => g x)).choose_spec.1 (f x') a).trans
          ((linfEval_apply X (f x') _).trans
            ((linfMap_apply (fun x : X' => f x) _ x').symm.trans
              (linfEval_apply X' x' _).symm))
      homEquiv_naturality_right := by
        intro X A B f g
        apply TypeCat.Hom.ext
        apply DFunLike.coe_injective
        funext x
        show (nmiuComp (linfEval X x) (WMIU.hom (f ≫ g).unop) : NMIUMap B.unop ℂ)
          = nmiuComp (nmiuComp (linfEval X x) (WMIU.hom f.unop)) (WMIU.hom g.unop)
        exact DFunLike.coe_injective rfl }

/-- **122VI** (`cor:linf-ff`, proc.tex:4612, Exercise), part 3, second
half: `Set` is a **coreflective subcategory** of `(W*_miu)^op` — the
functor `ℓ^∞` is full and faithful (part 3, first half, `cor_linf_ff_3`)
and is a left adjoint (**122II**). -/
instance linfCoreflective : Coreflective (linfFunctor.{u}) where
  map_surjective {X Y} h := by
    obtain ⟨k, hk⟩ := (cor_linf_ff_3 X Y).2 (WMIU.hom h.unop)
    exact ⟨TypeCat.ofHom k, Quiver.Hom.unop_inj hk.symm⟩
  map_injective {X Y f g} h := by
    apply TypeCat.Hom.ext
    apply DFunLike.coe_injective
    have h' : linfMap (fun x : X => f x) = linfMap (fun x : X => g x) :=
      congrArg (fun p => WMIU.hom (Quiver.Hom.unop p)) h
    exact (cor_linf_ff_3 X Y).1 h'
  R := nspFunctor
  adj := linfNspAdjunction

end Categorical

/-! ## Parsec 1230: `ℓ^∞` and `nsp` are strong monoidal -/

/-- **123I** (proc.tex:4628, Exercise), part 1: the indicator functions
`x̂ = single x 1` generate `ℓ^∞(X)`.

No author argument (an exercise past parsec 340, so no published solution
either).  The route taken: norm-closedness alone is *not* enough — the
finitely supported functions are norm-dense in `c₀(X)`, not in `ℓ^∞(X)` — so
the work is done by closure under directed suprema.  For `0 ≤ f` the finite
restrictions `∑_{x ∈ F} f(x)·x̂` (`F ⊆ X` finite) form a directed family whose
supremum is `f`, because the order on `⊕_{x ∈ X} ℂ` is pointwise
(`lp_infty_le_iff`); note the least-upper-bound half needs only the singletons
`F = {y}`.  A self-adjoint `a` is reduced to that case by `a = (a + ‖a‖·1) −
‖a‖·1` (no positive/negative part decomposition is needed), and a general `f`
by `f = ℜf + i·ℑf`. -/
theorem linf_generated (X : Type u) [DecidableEq X] :
    wstar (linf X) {f : linf X | ∃ x : X, f = lp.single ∞ x 1} = ⊤ := by
  obtain ⟨hVN, hgen⟩ :=
    isVNSubalgebra_wstar (A := linf X) {f : linf X | ∃ x : X, f = lp.single ∞ x 1}
  set S : StarSubalgebra ℂ (linf X) :=
    wstar (linf X) {f : linf X | ∃ x : X, f = lp.single ∞ x 1} with hSdef
  -- every `single x z` lies in `S`
  have hsingle : ∀ (x : X) (z : ℂ), (lp.single ∞ x z : linf X) ∈ S := by
    intro x z
    have h : (lp.single ∞ x z : linf X) = z • lp.single ∞ x (1 : ℂ) := by
      rw [← lp.single_smul]; simp
    rw [h]
    exact SMulMemClass.smul_mem _ (hgen ⟨x, rfl⟩)
  have hsum_mem : ∀ (c : X → ℂ) (F : Finset X),
      (∑ x ∈ F, (lp.single ∞ x (c x) : linf X)) ∈ S :=
    fun c F => sum_mem fun x _ => hsingle x (c x)
  -- the value of a finite restriction
  have hev : ∀ (c : X → ℂ) (F : Finset X) (y : X),
      ((∑ x ∈ F, (lp.single ∞ x (c x) : linf X)) : linf X) y
        = if y ∈ F then c y else 0 := by
    intro c F y
    have h := map_sum (lpEvalSAH (𝒜 := fun _ : X => ℂ) y)
      (fun x => (lp.single ∞ x (c x) : linf X)) F
    simp only [lpEvalSAH_apply] at h
    rw [h]
    simp only [lp.coeFn_single]
    exact Finset.sum_pi_single y c F
  -- `single x z` is self-adjoint when `z` is
  have hsingle_sa : ∀ (x : X) (z : ℂ), (starRingEnd ℂ) z = z →
      IsSelfAdjoint (lp.single ∞ x z : linf X) := by
    intro x z hz
    change star _ = _
    apply lp.ext
    rw [lp.coeFn_star]
    funext y
    simp only [Pi.star_apply, lp.coeFn_single, Pi.single_apply]
    split
    · exact hz
    · simp
  -- every positive element lies in `S`
  have key_pos : ∀ f : linf X, 0 ≤ f → f ∈ S := by
    intro f hf
    have hfx : ∀ y : X, (0 : ℂ) ≤ (f : linf X) y := (lp_infty_nonneg_iff f).mp hf
    have him : ∀ y : X, (starRingEnd ℂ) ((f : linf X) y) = (f : linf X) y := fun y =>
      Complex.conj_eq_iff_im.mpr (Complex.le_def.mp (hfx y)).2.symm
    have hfsa : IsSelfAdjoint f := by
      change star f = f
      apply lp.ext
      rw [lp.coeFn_star]
      funext y
      exact him y
    set c : X → ℂ := fun y => (f : linf X) y with hc
    have hsa : ∀ F : Finset X,
        IsSelfAdjoint (∑ x ∈ F, (lp.single ∞ x (c x) : linf X)) := by
      intro F
      change star _ = _
      rw [star_sum]
      exact Finset.sum_congr rfl fun x _ => hsingle_sa x (c x) (him x)
    set g : Finset X → selfAdjoint (linf X) :=
      fun F => ⟨∑ x ∈ F, (lp.single ∞ x (c x) : linf X), hsa F⟩ with hg
    have hev' : ∀ (F : Finset X) (y : X),
        ((g F : selfAdjoint (linf X)) : linf X) y = if y ∈ F then c y else 0 :=
      fun F y => hev c F y
    have hmono : ∀ {F G : Finset X}, F ⊆ G → g F ≤ g G := by
      intro F G hFG
      rw [← Subtype.coe_le_coe, lp_infty_le_iff]
      intro y
      rw [hev', hev']
      split_ifs with h1 h2 h3
      · exact le_rfl
      · exact absurd (hFG h1) h2
      · exact hfx y
      · exact le_rfl
    have hlub : IsLUB (Set.range g) ⟨f, hfsa⟩ := by
      constructor
      · rintro _ ⟨F, rfl⟩
        rw [← Subtype.coe_le_coe, lp_infty_le_iff]
        intro y
        rw [hev']
        change _ ≤ (f : linf X) y
        split
        · exact le_rfl
        · exact hfx y
      · intro u hu
        rw [← Subtype.coe_le_coe, lp_infty_le_iff]
        intro y
        have h := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr (hu ⟨{y}, rfl⟩)) y
        rw [hev'] at h
        simpa using h
    refine hVN.dirSup_mem (Set.range g) ⟨f, hfsa⟩ ?_ ⟨_, ⟨∅, rfl⟩⟩ ?_ hlub
    · rintro _ ⟨F, rfl⟩
      exact hsum_mem c F
    · rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
      exact ⟨g (F ∪ G), ⟨F ∪ G, rfl⟩, hmono Finset.subset_union_left,
        hmono Finset.subset_union_right⟩
  -- every self-adjoint element lies in `S`
  have key_sa : ∀ f : linf X, IsSelfAdjoint f → f ∈ S := by
    intro a ha
    have hb : (0 : linf X) ≤ a + ((‖a‖ : ℂ) • 1) := by
      rw [lp_infty_nonneg_iff]
      intro y
      have h1 : ((a + ((‖a‖ : ℂ) • 1) : linf X) : linf X) y = (a : linf X) y + (‖a‖ : ℂ) := by
        rw [lp.coeFn_add, lp.coeFn_smul, lp.infty_coeFn_one]
        simp
      rw [h1, Complex.le_def]
      have him : ((a : linf X) y).im = 0 :=
        Complex.conj_eq_iff_im.mp (lp_infty_isSelfAdjoint ha y)
      have h2 : ‖(a : linf X) y‖ ≤ ‖a‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero a y
      have h3 : |((a : linf X) y).re| ≤ ‖(a : linf X) y‖ := Complex.abs_re_le_norm _
      constructor
      · simp only [Complex.zero_re, Complex.add_re, Complex.ofReal_re]
        have := abs_le.mp h3
        linarith [this.1]
      · simp [him]
    have hrw : a = (a + ((‖a‖ : ℂ) • 1)) - ((‖a‖ : ℂ) • 1) :=
      (add_sub_cancel_right a ((‖a‖ : ℂ) • 1)).symm
    rw [hrw]
    exact sub_mem (key_pos _ hb) (SMulMemClass.smul_mem _ (one_mem S))
  refine StarSubalgebra.eq_top_iff.mpr fun f => ?_
  rw [← realPart_add_I_smul_imaginaryPart f]
  exact add_mem (key_sa _ (realPart f).2)
    (SMulMemClass.smul_mem _ (key_sa _ (imaginaryPart f).2))

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

/-- `{id}` is a centre separating collection on `ℂ`. -/
theorem centreSeparatingConj_complexId :
    CentreSeparatingConj ℂ {Theses.A.VN.complexIdNP} := by
  rw [centreSeparatingConj_iff]
  intro a ha
  refine ⟨fun h ω _ b => by rw [h]; simp, fun H => ?_⟩
  have h := H Theses.A.VN.complexIdNP rfl 1
  rw [star_one, one_mul, mul_one] at h
  exact h

theorem linfT_memℓp (X Y : Type u) (f : linf X) (g : linf Y) :
    Memℓp (fun p : X × Y => (f : ∀ _ : X, ℂ) p.1 * (g : ∀ _ : Y, ℂ) p.2) ∞ := by
  rw [memℓp_infty_iff]
  refine ⟨‖f‖ * ‖g‖, ?_⟩
  rintro _ ⟨p, rfl⟩
  show ‖(f : ∀ _ : X, ℂ) p.1 * (g : ∀ _ : Y, ℂ) p.2‖ ≤ ‖f‖ * ‖g‖
  rw [norm_mul]
  exact mul_le_mul (lp.norm_apply_le_norm (by simp) f p.1)
    (lp.norm_apply_le_norm (by simp) g p.2) (norm_nonneg _) (norm_nonneg f)

/-- `(f ⊗ g)(x,y) = f(x)·g(y) : ℓ^∞(X) × ℓ^∞(Y) → ℓ^∞(X × Y)` (**123I**.3). -/
def linfT (X Y : Type u) (f : linf X) (g : linf Y) : linf (X × Y) :=
  ⟨fun p => (f : ∀ _ : X, ℂ) p.1 * (g : ∀ _ : Y, ℂ) p.2, linfT_memℓp X Y f g⟩

@[simp] theorem linfT_apply (X Y : Type u) (f : linf X) (g : linf Y) (p : X × Y) :
    ((linfT X Y f g : linf (X × Y)) : ∀ _ : X × Y, ℂ) p
      = (f : ∀ _ : X, ℂ) p.1 * (g : ∀ _ : Y, ℂ) p.2 := rfl

/-- `linfT` as a bilinear map. -/
def linfTmul (X Y : Type u) : linf X →ₗ[ℂ] linf Y →ₗ[ℂ] linf (X × Y) :=
  LinearMap.mk₂ ℂ (linfT X Y)
    (fun f f' g => by
      refine lp.ext (funext fun p => ?_)
      simp only [linfT_apply, lp.coeFn_add, Pi.add_apply]; ring)
    (fun c f g => by
      refine lp.ext (funext fun p => ?_)
      simp only [linfT_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring)
    (fun f g g' => by
      refine lp.ext (funext fun p => ?_)
      simp only [linfT_apply, lp.coeFn_add, Pi.add_apply]; ring)
    (fun c f g => by
      refine lp.ext (funext fun p => ?_)
      simp only [linfT_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem linfTmul_apply (X Y : Type u) (f : linf X) (g : linf Y) (p : X × Y) :
    ((linfTmul X Y f g : linf (X × Y)) : ∀ _ : X × Y, ℂ) p
      = (f : ∀ _ : X, ℂ) p.1 * (g : ∀ _ : Y, ℂ) p.2 := rfl

theorem linfTmul_miu (X Y : Type u) : MIUBilinear (linfTmul X Y) := by
  refine ⟨?_, ?_, ?_⟩
  · refine lp.ext (funext fun p => ?_)
    simp only [linfTmul_apply, lp.infty_coeFn_one, Pi.one_apply, one_mul]
  · intro f f' g g'
    refine lp.ext (funext fun p => ?_)
    simp only [linfTmul_apply, lp.infty_coeFn_mul, Pi.mul_apply]
    ring
  · intro f g
    refine lp.ext (funext fun p => ?_)
    simp only [linfTmul_apply, lp.coeFn_star, Pi.star_apply, star_mul']

/-- **123I** (proc.tex:4628, Exercise), part 3: the map
`⊗ : ℓ^∞(X) × ℓ^∞(Y) → ℓ^∞(X × Y)`, `(f ⊗ g)(x,y) = f(x)g(y)` is a
tensor product; whence `ℓ^∞(X × Y) ≅ ℓ^∞(X) ⊗ ℓ^∞(Y)` (and `ℓ^∞` is
strong monoidal). -/
theorem linf_tensor (X Y : Type u) :
    ∃ γ : linf X →ₗ[ℂ] linf Y →ₗ[ℂ] linf (X × Y),
      (∀ (f : linf X) (g : linf Y) (x : X) (y : Y),
        γ f g (x, y) = f x * g y) ∧ IsTensorProduct γ := by
  classical
  refine ⟨linfTmul X Y, fun f g x y => rfl, ?_⟩
  set γ := linfTmul X Y with hγ
  have hmiu : MIUBilinear γ := linfTmul_miu X Y
  set Sg : Set (NPFunctional (linf X)) :=
    {χ : NPFunctional (linf X) | ∃ x, ∃ ω ∈ ({Theses.A.VN.complexIdNP} :
      Set (NPFunctional ℂ)), ∀ u : linf X, χ u = ω ((u : ∀ _ : X, ℂ) x)} with hSgd
  set Γ : Set (NPFunctional (linf Y)) :=
    {χ : NPFunctional (linf Y) | ∃ y, ∃ ω ∈ ({Theses.A.VN.complexIdNP} :
      Set (NPFunctional ℂ)), ∀ u : linf Y, χ u = ω ((u : ∀ _ : Y, ℂ) y)} with hΓd
  have hSg : CentreSeparatingConj (linf X) Sg :=
    sum_generation_2 (fun _ : X => ℂ) (fun _ => {Theses.A.VN.complexIdNP})
      (fun _ => centreSeparatingConj_complexId)
  have hΓ : CentreSeparatingConj (linf Y) Γ :=
    sum_generation_2 (fun _ : Y => ℂ) (fun _ => {Theses.A.VN.complexIdNP})
      (fun _ => centreSeparatingConj_complexId)
  refine (tensor_characterization Sg Γ hSg hΓ γ hmiu).mpr ⟨?_, ?_, ?_⟩
  · -- (1) the `δ_{(x,y)} = δ_x ⊗ δ_y` generate, by **117II**.1
    have hgen := sum_generation_1 (fun _ : X × Y => ℂ) (fun _ => (∅ : Set ℂ))
      (fun _ => starSubalgebra_complex_eq_top _)
    have hsub : ({x : linf (X × Y) | ∃ i, ∃ a ∈ (∅ : Set ℂ),
          x = lp.single ∞ i a} ∪
        {x : linf (X × Y) | ∃ i, x = lp.single ∞ i 1})
        ⊆ (tensorSpan γ hmiu : Set (linf (X × Y))) := by
      rintro x (⟨i, a, ha, -⟩ | ⟨p, rfl⟩)
      · exact ha.elim
      · refine Submodule.subset_span ⟨lp.single ∞ p.1 1, lp.single ∞ p.2 1, ?_⟩
        refine lp.ext (funext fun q => ?_)
        by_cases hq : q = p
        · subst hq
          rw [lp.single_apply_self]
          show (1 : ℂ) = ((lp.single ∞ q.1 (1 : ℂ) : linf X) : ∀ _ : X, ℂ) q.1
            * ((lp.single ∞ q.2 (1 : ℂ) : linf Y) : ∀ _ : Y, ℂ) q.2
          rw [lp.single_apply_self, lp.single_apply_self, one_mul]
        · rw [lp.single_apply_ne _ _ _ hq]
          show (0 : ℂ) = ((lp.single ∞ p.1 (1 : ℂ) : linf X) : ∀ _ : X, ℂ) q.1
            * ((lp.single ∞ p.2 (1 : ℂ) : linf Y) : ∀ _ : Y, ℂ) q.2
          by_cases h1 : q.1 = p.1
          · have h2 : q.2 ≠ p.2 := fun h2 => hq (Prod.ext h1 h2)
            rw [lp.single_apply_ne _ _ _ h2, mul_zero]
          · rw [lp.single_apply_ne _ _ _ h1, zero_mul]
    have htop : wstar (linf (X × Y))
        (tensorSpan γ hmiu : Set (linf (X × Y))) = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hgen]
      exact wstar_mono hsub
    exact dense_of_wstar_eq_top _ htop
  · -- (2) the product functional of two point evaluations is a point evaluation
    rintro σ ⟨x, ω, hω, hσ⟩ τ ⟨y, ω', hω', hτ⟩
    obtain rfl : ω = Theses.A.VN.complexIdNP := hω
    obtain rfl : ω' = Theses.A.VN.complexIdNP := hω'
    refine ⟨lpNP (x, y) Theses.A.VN.complexIdNP, fun f g => ?_⟩
    rw [lp_infty_np_apply, hσ f, hτ g]
    rfl
  · -- (3) they are centre separating, again by **117II**.2
    have h := sum_generation_2 (fun _ : X × Y => ℂ)
      (fun _ => {Theses.A.VN.complexIdNP})
      (fun _ => centreSeparatingConj_complexId)
    refine centreSeparatingConj_mono h ?_
    rintro χ ⟨p, ω, hω, hχ⟩
    obtain rfl : ω = Theses.A.VN.complexIdNP := hω
    refine ⟨lpNP p.1 Theses.A.VN.complexIdNP,
      ⟨p.1, Theses.A.VN.complexIdNP, rfl, fun u => rfl⟩,
      lpNP p.2 Theses.A.VN.complexIdNP,
      ⟨p.2, Theses.A.VN.complexIdNP, rfl, fun u => rfl⟩, fun f g => ?_⟩
    rw [hχ]
    rfl


/-! ### Auxiliaries for **123II**

The exercise (proc.tex:4663) gives no argument.  Both halves run on the
same two devices: the two "slice" nmiu-maps `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`
(the second is **116III**.5), and `tensor_linear_ext` — the vector-valued
form of `prod_functional_unique` — for everything that has to be checked
beyond the elementary tensors. -/

/-- Auxiliary for **123II**: an nmiu-functional is in particular an
np-functional (an nmiu-map is completely positive, `nmiuNCP`, and normal
by its own field). -/
private noncomputable def nmiuNP [VonNeumannAlgebra A] (σ : NMIUMap A ℂ) :
    NPFunctional A where
  toPositiveLinearMap := ncpPositive (nmiuNCP σ)
  preservesDirSups' := σ.preservesDirSups'

@[simp] private theorem nmiuNP_apply [VonNeumannAlgebra A] (σ : NMIUMap A ℂ)
    (a : A) : (nmiuNP σ a : ℂ) = σ a := rfl

/-- Auxiliary for **123II**.1: the left slice `a ↦ a ⊗ 1` is linear. -/
private theorem vtmulLeft_add [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (a a' : A) : (a + a') ⊗ᵥ (1 : B) = a ⊗ᵥ (1 : B) + a' ⊗ᵥ (1 : B) := by
  show (vnTensor A B).map (a + a') 1 = _
  rw [map_add]
  rfl

private theorem vtmulLeft_smul [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (r : ℂ) (a : A) : (r • a) ⊗ᵥ (1 : B) = r • (a ⊗ᵥ (1 : B)) := by
  show (vnTensor A B).map (r • a) 1 = _
  rw [map_smul]
  rfl

private theorem vtmulLeft_mono [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {x y : A} (h : x ≤ y) : x ⊗ᵥ (1 : B) ≤ y ⊗ᵥ (1 : B) := by
  have h1 := vtmul_nonneg (y - x) (1 : B) (sub_nonneg.mpr h) zero_le_one
  have h2 : ((y - x) ⊗ᵥ (1 : B)) = y ⊗ᵥ (1 : B) - x ⊗ᵥ (1 : B) := by
    show (vnTensor A B).map (y - x) 1 = _
    rw [map_sub]
    rfl
  rw [h2] at h1
  exact sub_nonneg.mp h1

/-- Auxiliary for **123II**.1: the left slice is normal, by **44XV**
`p_uwcont` and the ultraweak continuity of `a ↦ a ⊗ b` (proved for
**116IV**.1). -/
private noncomputable def pmapTmulLeft (A B : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    A →ₚ[ℂ] VNT A B where
  toFun a := a ⊗ᵥ (1 : B)
  map_add' := vtmulLeft_add
  map_smul' := vtmulLeft_smul
  monotone' _ _ h := vtmulLeft_mono h

private theorem preservesDirSups_vtmulLeft [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] :
    PreservesDirSups (fun a : A => a ⊗ᵥ (1 : B)) :=
  ((p_uwcont (pmapTmulLeft A B)).out 0 2).mp
    (continuous_ultraweak_vtmul_left (1 : B))

/-- Auxiliary for **123II**.1: the left slice `a ↦ a ⊗ 1` as an nmiu-map.
(The right slice `b ↦ 1 ⊗ b` is **116III**.5, `tensor_simple_facts_5`.) -/
private noncomputable def nmiuTmulLeft (A B : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    NMIUMap A (VNT A B) where
  toStarAlgHom :=
    { toFun := fun a => a ⊗ᵥ (1 : B)
      map_one' := (vnTensor A B).isTensorProduct.miu.1
      map_mul' := fun x y => by
        have h := (vnTensor A B).isTensorProduct.miu.2.1 x y (1 : B) (1 : B)
        rwa [one_mul] at h
      map_zero' := by
        show (vnTensor A B).map 0 1 = 0
        rw [map_zero]
        rfl
      map_add' := vtmulLeft_add
      commutes' := fun r => by
        have hone : ((1 : A) ⊗ᵥ (1 : B)) = (1 : VNT A B) :=
          (vnTensor A B).isTensorProduct.miu.1
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          vtmulLeft_smul, hone]
      map_star' := fun a => by
        have h := (vnTensor A B).isTensorProduct.miu.2.2 a (1 : B)
        rw [star_one] at h
        exact h.symm }
  preservesDirSups' := preservesDirSups_vtmulLeft

@[simp] private theorem nmiuTmulLeft_apply [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (a : A) :
    nmiuTmulLeft A B a = a ⊗ᵥ (1 : B) := rfl

/-- **123II** (proc.tex:4663, Exercise), part 1: an nmiu-functional `φ` on
`𝒜 ⊗ ℬ` restricts to nmiu-functionals `σ = φ((·) ⊗ 1)` and
`τ = φ(1 ⊗ (·))` with `φ(a ⊗ b) = σ(a)τ(b)`. -/
theorem nsp_tensor_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NMIUMap (VNT A B) ℂ) :
    ∃ (σ : NMIUMap A ℂ) (τ : NMIUMap B ℂ),
      (∀ a : A, σ a = φ (a ⊗ᵥ 1)) ∧ (∀ b : B, τ b = φ (1 ⊗ᵥ b)) ∧
        ∀ (a : A) (b : B), φ (a ⊗ᵥ b) = σ a * τ b := by
  -- `σ = φ ∘ ((·) ⊗ 1)` and `τ = φ ∘ (1 ⊗ (·))`, both nmiu as composites of
  -- nmiu-maps; the product formula is multiplicativity of `φ` against
  -- `(a ⊗ 1)(1 ⊗ b) = a ⊗ b`.
  obtain ⟨ρ, hρ⟩ := (tensor_simple_facts_5 (A := A) (B := B) (1 : A) zero_le_one).2
  refine ⟨nmiuComp φ (nmiuTmulLeft A B), nmiuComp φ ρ, fun a => rfl, fun b => ?_,
    fun a b => ?_⟩
  · show φ (ρ b) = φ ((1 : A) ⊗ᵥ b)
    rw [hρ]
  · have h1 : ((a ⊗ᵥ (1 : B)) * ((1 : A) ⊗ᵥ b)) = a ⊗ᵥ b := by
      have h := (vnTensor A B).isTensorProduct.miu.2.1 a (1 : A) (1 : B) b
      rw [mul_one, one_mul] at h
      exact h.symm
    have hmulφ : ∀ x y : VNT A B, φ (x * y) = φ x * φ y :=
      fun x y => map_mul φ.toStarAlgHom x y
    show (φ (a ⊗ᵥ b) : ℂ) = φ (a ⊗ᵥ (1 : B)) * φ (ρ b)
    rw [hρ, ← h1, hmulφ]

/-- **123II** (proc.tex:4663, Exercise), part 2, well-definedness half:
every pair `(σ, τ)` extends to a *unique* nmiu-functional `σ ⊗ τ` on
`𝒜 ⊗ ℬ` with `(σ ⊗ τ)(a ⊗ b) = σ(a)τ(b)`.  That the resulting map
`nsp(𝒜) × nsp(ℬ) → nsp(𝒜 ⊗ ℬ)` is a **bijection**, which is what the
Exercise asks for, is `nsp_tensor_2_bijection` below. -/
theorem nsp_tensor_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (σ : NMIUMap A ℂ) (τ : NMIUMap B ℂ) :
    ∃! φ : NMIUMap (VNT A B) ℂ,
      ∀ (a : A) (b : B), φ (a ⊗ᵥ b) = σ a * τ b := by
  classical
  -- The candidate is the *product np-functional* `σ ⊗ τ` (108II's clause
  -- `prod_exists`); what has to be added is that it is multiplicative, and
  -- that is `tensor_linear_ext` twice — once in each argument.
  have hone : ((1 : A) ⊗ᵥ (1 : B)) = (1 : VNT A B) :=
    (vnTensor A B).isTensorProduct.miu.1
  have hmulσ : ∀ x y : A, σ (x * y) = σ x * σ y := fun x y => map_mul σ.toStarAlgHom x y
  have hmulτ : ∀ x y : B, τ (x * y) = τ x * τ y := fun x y => map_mul τ.toStarAlgHom x y
  have honeσ : σ (1 : A) = 1 := map_one σ.toStarAlgHom
  have honeτ : τ (1 : B) = 1 := map_one τ.toStarAlgHom
  obtain ⟨χ, hχtmul⟩ : ∃ χ : NPFunctional (VNT A B),
      ∀ (a : A) (b : B), (χ (a ⊗ᵥ b) : ℂ) = σ a * τ b :=
    ⟨prodNP (vnTensor A B).isTensorProduct (nmiuNP σ) (nmiuNP τ),
      fun a b => prodNP_apply (vnTensor A B).isTensorProduct (nmiuNP σ) (nmiuNP τ) a b⟩
  have hcont : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ (fun x => (χ x : ℂ)) :=
    continuous_ultraweak_npFunctional χ
  have haddχ : ∀ x y : VNT A B, (χ (x + y) : ℂ) = χ x + χ y :=
    fun x y => map_add χ.toPositiveLinearMap x y
  have hsmulχ : ∀ (c : ℂ) (x : VNT A B), (χ (c • x) : ℂ) = c * χ x :=
    fun c x => (map_smul χ.toPositiveLinearMap c x).trans (smul_eq_mul _ _)
  -- the two linear maps compared in each step
  have hmk : ∀ z : VNT A B, ∃ F : VNT A B →ₗ[ℂ] ℂ, ∀ t, F t = (χ (z * t) : ℂ) := by
    intro z
    exact ⟨{ toFun := fun t => (χ (z * t) : ℂ)
             map_add' := fun x y => by rw [mul_add, haddχ]
             map_smul' := fun c x => by
               simp only [RingHom.id_apply, smul_eq_mul]
               rw [mul_smul_comm, hsmulχ] }, fun _ => rfl⟩
  have hmk' : ∀ z : VNT A B, ∃ G : VNT A B →ₗ[ℂ] ℂ, ∀ t, G t = (χ (t * z) : ℂ) := by
    intro z
    exact ⟨{ toFun := fun t => (χ (t * z) : ℂ)
             map_add' := fun x y => by rw [add_mul, haddχ]
             map_smul' := fun c x => by
               simp only [RingHom.id_apply, smul_eq_mul]
               rw [smul_mul_assoc, hsmulχ] }, fun _ => rfl⟩
  have hmkc : ∀ c : ℂ, ∃ G : VNT A B →ₗ[ℂ] ℂ, ∀ t, G t = c * (χ t : ℂ) := by
    intro c
    exact ⟨{ toFun := fun t => c * (χ t : ℂ)
             map_add' := fun x y => by rw [haddχ]; ring
             map_smul' := fun r x => by
               simp only [RingHom.id_apply, smul_eq_mul]
               rw [hsmulχ]; ring }, fun _ => rfl⟩
  -- step 1: multiplicativity with an elementary tensor on the left
  have hstep1 : ∀ (a : A) (b : B) (t : VNT A B),
      (χ ((a ⊗ᵥ b) * t) : ℂ) = χ (a ⊗ᵥ b) * χ t := by
    intro a b
    obtain ⟨F, hF⟩ := hmk (a ⊗ᵥ b)
    obtain ⟨G, hG⟩ := hmkc (χ (a ⊗ᵥ b) : ℂ)
    have hFG : F = G := by
      refine tensor_linear_ext (vnTensor A B).isTensorProduct F G ?_ ?_ ?_
      · have hfun : ⇑F = fun t => (χ ((a ⊗ᵥ b) * t) : ℂ) := funext hF
        rw [hfun]
        exact @Continuous.comp (VNT A B) (VNT A B) ℂ (ultraweak (VNT A B))
          (ultraweak (VNT A B)) _ _ _ hcont (mult_uws_cont (a ⊗ᵥ b)).1
      · have hfun : ⇑G = fun t => (χ (a ⊗ᵥ b) : ℂ) * (χ t : ℂ) := funext hG
        rw [hfun]
        exact @Continuous.comp (VNT A B) ℂ ℂ (ultraweak (VNT A B)) _ _ _ _
          (continuous_const.mul continuous_id) hcont
      · intro c d
        have hmul : ((a ⊗ᵥ b) * (c ⊗ᵥ d)) = (a * c) ⊗ᵥ (b * d) :=
          ((vnTensor A B).isTensorProduct.miu.2.1 a c b d).symm
        have h1 : F ((vnTensor A B).map c d) = (χ ((a ⊗ᵥ b) * (c ⊗ᵥ d)) : ℂ) := hF _
        have h2 : G ((vnTensor A B).map c d) = (χ (a ⊗ᵥ b) : ℂ) * (χ (c ⊗ᵥ d) : ℂ) :=
          hG _
        rw [h1, h2, hmul, hχtmul, hχtmul, hχtmul, hmulσ, hmulτ]
        ring
    intro t
    rw [← hF t, ← hG t, hFG]
  -- step 2: multiplicativity in general
  have hmul : ∀ x t : VNT A B, (χ (x * t) : ℂ) = χ x * χ t := by
    intro x t
    obtain ⟨F, hF⟩ := hmk' t
    obtain ⟨G, hG⟩ := hmkc (χ t : ℂ)
    have hFG : F = G := by
      refine tensor_linear_ext (vnTensor A B).isTensorProduct F G ?_ ?_ ?_
      · have hfun : ⇑F = fun x => (χ (x * t) : ℂ) := funext hF
        rw [hfun]
        exact @Continuous.comp (VNT A B) (VNT A B) ℂ (ultraweak (VNT A B))
          (ultraweak (VNT A B)) _ _ _ hcont (mult_uws_cont t).2.1
      · have hfun : ⇑G = fun x => (χ t : ℂ) * (χ x : ℂ) := funext hG
        rw [hfun]
        exact @Continuous.comp (VNT A B) ℂ ℂ (ultraweak (VNT A B)) _ _ _ _
          (continuous_const.mul continuous_id) hcont
      · intro a b
        have h1 : F ((vnTensor A B).map a b) = (χ ((a ⊗ᵥ b) * t) : ℂ) := hF _
        have h2 : G ((vnTensor A B).map a b) = (χ t : ℂ) * (χ (a ⊗ᵥ b) : ℂ) := hG _
        rw [h1, h2, hstep1 a b t]
        ring
    have h : (χ (x * t) : ℂ) = (χ t : ℂ) * (χ x : ℂ) := by
      rw [← hF x, ← hG x, hFG]
    rw [h]
    ring
  have hχone : (χ (1 : VNT A B) : ℂ) = 1 := by
    rw [← hone, hχtmul, honeσ, honeτ, one_mul]
  obtain ⟨φ, hφval⟩ : ∃ φ : NMIUMap (VNT A B) ℂ, ∀ x, φ x = (χ x : ℂ) :=
    ⟨{ toStarAlgHom :=
        { toFun := fun x => (χ x : ℂ)
          map_one' := hχone
          map_mul' := hmul
          map_zero' := map_zero χ.toPositiveLinearMap
          map_add' := haddχ
          commutes' := fun r => by
            rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
              hsmulχ, hχone, mul_one, smul_eq_mul, mul_one]
          map_star' := fun x => npFunctional_star χ x }
       preservesDirSups' := χ.preservesDirSups' }, fun _ => rfl⟩
  refine ⟨φ, fun a b => by rw [hφval, hχtmul], ?_⟩
  -- uniqueness: two nmiu-functionals agreeing on elementary tensors agree
  intro ψ hψ
  have hψcont : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑(nmiuLin ψ) :=
    continuous_ultraweak_npFunctional (nmiuNP ψ)
  have hφcont : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑(nmiuLin φ) :=
    continuous_ultraweak_npFunctional (nmiuNP φ)
  have h := tensor_linear_ext (vnTensor A B).isTensorProduct (nmiuLin ψ)
    (nmiuLin φ) hψcont hφcont (fun a b => by
      show (ψ (a ⊗ᵥ b) : ℂ) = φ (a ⊗ᵥ b)
      rw [hψ a b, hφval, hχtmul])
  refine DFunLike.coe_injective (funext fun x => ?_)
  have h2 := congrArg (fun L : VNT A B →ₗ[ℂ] ℂ => L x) h
  simpa using h2

/-- **123II** (proc.tex:4663, Exercise), part 2, as the Exercise states it:
`(σ, τ) ↦ σ ⊗ τ` is a **bijection** `nsp(𝒜) × nsp(ℬ) → nsp(𝒜 ⊗ ℬ)`.
The map itself is `nsp_tensor_2` (well-definedness, and the formula
`(σ ⊗ τ)(a ⊗ b) = σ(a)τ(b)` that pins it down); **surjectivity is part 1**,
`nsp_tensor_1`, and **injectivity is part 1's formulas** `σ = φ((·) ⊗ 1)`,
`τ = φ(1 ⊗ (·))`, read off by evaluating at `a ⊗ 1` and `1 ⊗ b`.
(The parenthetical "this makes `nsp` strong monoidal" is not formalized:
no monoidal structure is formed in the tree.) -/
theorem nsp_tensor_2_bijection [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    ∃ Θ : NMIUMap A ℂ × NMIUMap B ℂ → NMIUMap (VNT A B) ℂ,
      (∀ (p : NMIUMap A ℂ × NMIUMap B ℂ) (a : A) (b : B),
        Θ p (a ⊗ᵥ b) = p.1 a * p.2 b) ∧ Function.Bijective Θ := by
  classical
  have hex : ∀ p : NMIUMap A ℂ × NMIUMap B ℂ,
      ∃ φ : NMIUMap (VNT A B) ℂ,
        (∀ (a : A) (b : B), φ (a ⊗ᵥ b) = p.1 a * p.2 b) ∧
        ∀ ψ : NMIUMap (VNT A B) ℂ,
          (∀ (a : A) (b : B), ψ (a ⊗ᵥ b) = p.1 a * p.2 b) → ψ = φ :=
    fun p => nsp_tensor_2 p.1 p.2
  choose Θ hΘ huniq using hex
  refine ⟨Θ, hΘ, ?_, ?_⟩
  · -- injectivity: recover `σ` and `τ` by part 1's formulas
    rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ hpair
    have hσ : σ = σ' := by
      refine DFunLike.coe_injective (funext fun a => ?_)
      have e : Θ (σ, τ) (a ⊗ᵥ (1 : B)) = Θ (σ', τ') (a ⊗ᵥ (1 : B)) := by
        rw [hpair]
      rw [hΘ (σ, τ) a 1, hΘ (σ', τ') a 1,
        show τ (1 : B) = 1 from map_one τ.toStarAlgHom,
        show τ' (1 : B) = 1 from map_one τ'.toStarAlgHom, mul_one, mul_one] at e
      exact e
    have hτ : τ = τ' := by
      refine DFunLike.coe_injective (funext fun b => ?_)
      have e : Θ (σ, τ) ((1 : A) ⊗ᵥ b) = Θ (σ', τ') ((1 : A) ⊗ᵥ b) := by
        rw [hpair]
      rw [hΘ (σ, τ) 1 b, hΘ (σ', τ') 1 b,
        show σ (1 : A) = 1 from map_one σ.toStarAlgHom,
        show σ' (1 : A) = 1 from map_one σ'.toStarAlgHom, one_mul, one_mul] at e
      exact e
    rw [hσ, hτ]
  · -- surjectivity: part 1 produces the pair, and `nsp_tensor_2`'s
    -- uniqueness identifies `φ` with its extension
    intro φ
    obtain ⟨σ, τ, -, -, hφ⟩ := nsp_tensor_1 φ
    exact ⟨(σ, τ), (huniq (σ, τ) φ (fun a b => hφ a b)).symm⟩

/-! ## Parsec 1240: the second adjunction -/

section GenerationBound

/-- Infrastructure for **124I**: a von Neumann algebra is no larger than
`2^(2^#D)` for any ultraweakly dense `D ⊆ 𝒜`.  This is the thesis's "every
element of `𝒜` is the ultraweak limit of a filter on `S'`, of which there
are no more than `2^(2^#S')`" (proc.tex:4705): the filter attached to `x` is
the trace `comap ι (𝓝 x)` of its neighbourhood filter, which determines `x`
because the ultraweak topology is Hausdorff (**44XI**.1). -/
private theorem card_le_of_dense {𝒳 : Type u} [CStarAlgebra 𝒳]
    [PartialOrder 𝒳] [StarOrderedRing 𝒳] [VonNeumannAlgebra 𝒳] (D : Set 𝒳)
    (hD : @Dense 𝒳 (ultraweak 𝒳) D) :
    #𝒳 ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ #D) := by
  classical
  let _ : TopologicalSpace 𝒳 := ultraweak 𝒳
  have _ : T2Space 𝒳 := vn_positive_basic_1.1
  have hinj : Function.Injective
      (fun x : 𝒳 => Filter.comap ((↑) : D → 𝒳) (nhds x)) := by
    intro x y hxy
    have hx : x ∈ closure D := by rw [hD.closure_eq]; trivial
    have hnb : (Filter.comap ((↑) : D → 𝒳) (nhds x)).NeBot :=
      mem_closure_iff_comap_neBot.mp hx
    have h1 : Filter.Tendsto ((↑) : D → 𝒳)
        (Filter.comap ((↑) : D → 𝒳) (nhds x)) (nhds x) := Filter.tendsto_comap
    have h2 : Filter.Tendsto ((↑) : D → 𝒳)
        (Filter.comap ((↑) : D → 𝒳) (nhds x)) (nhds y) := by
      simp only at hxy
      rw [hxy]; exact Filter.tendsto_comap
    exact tendsto_nhds_unique h1 h2
  refine le_trans (Cardinal.mk_le_of_injective hinj) ?_
  have hfil : Function.Injective (fun F : Filter D => F.sets) :=
    fun _ _ h => Filter.filter_eq h
  refine le_trans (Cardinal.mk_le_of_injective hfil) ?_
  rw [Cardinal.mk_set, Cardinal.mk_set]

/-- Infrastructure for **124I**: the ∗-subalgebra generated by `S` has at
most `#ℂ + #S` elements — the thesis's "every element of `S'` can be formed
from `S ∪ ℂ` using the finitary operations" (proc.tex:4700), which Mathlib
supplies as `Algebra.lift_cardinalMk_adjoin_le`. -/
private theorem card_starAdjoin_le {𝒳 : Type u} [CStarAlgebra 𝒳] (S : Set 𝒳) :
    #(StarAlgebra.adjoin ℂ S) ≤ Cardinal.continuum + #S := by
  have hbig : ℵ₀ ≤ Cardinal.continuum + #S :=
    le_trans Cardinal.aleph0_le_continuum le_self_add
  have hcoe : #(StarAlgebra.adjoin ℂ S)
      = #(Algebra.adjoin ℂ (S ∪ star S)) := by
    have h := StarAlgebra.adjoin_toSubalgebra ℂ (A := 𝒳) S
    exact Cardinal.mk_congr (Equiv.setCongr (congrArg (fun T : Subalgebra ℂ 𝒳 =>
      (T : Set 𝒳)) h))
  have hstar : #(star S : Set 𝒳) ≤ #S := by
    refine Cardinal.mk_le_of_injective (f := fun x : (star S : Set 𝒳) =>
      (⟨star x.val, x.property⟩ : S)) ?_
    intro x y h
    exact Subtype.ext (star_injective (congrArg Subtype.val h))
  have hunion : #((S ∪ star S : Set 𝒳)) ≤ Cardinal.continuum + #S := by
    refine le_trans (Cardinal.mk_union_le _ _) ?_
    calc #S + #(star S : Set 𝒳)
        ≤ (Cardinal.continuum + #S) + (Cardinal.continuum + #S) :=
          add_le_add le_add_self (le_trans hstar le_add_self)
      _ = Cardinal.continuum + #S := Cardinal.add_eq_self hbig
  rw [hcoe]
  have h := Algebra.lift_cardinalMk_adjoin_le ℂ (A := 𝒳) (S ∪ star S)
  rw [Cardinal.lift_uzero, Cardinal.lift_uzero, Cardinal.mk_complex,
    Cardinal.lift_continuum] at h
  exact le_trans h (max_le (max_le (le_add_right le_rfl) hunion) hbig)

/-- **124I** (`vn-generation-bound`, proc.tex:4688, Lemma): if a von
Neumann algebra `𝒜` is generated by `S ⊆ 𝒜`, then
`#𝒜 ≤ 2^(2^(#ℂ + #S))`.

The proof is the thesis's own.  The ∗-subalgebra `S'` generated by `S` is
ultraweakly dense (this is `dense_of_wstar_eq_top`, i.e. 75VII
`usClosureSubalgebra`, which is what makes `W*(·)` a closure operator), it
has at most `#ℂ + #S` elements, and every element of `𝒜` is the limit of a
(unique-limit) filter on it. -/
theorem vn_generation_bound [VonNeumannAlgebra A] (S : Set A)
    (hS : wstar A S = ⊤) :
    #A ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (Cardinal.continuum + #S)) := by
  have hsub : S ⊆ ((StarAlgebra.adjoin ℂ S : StarSubalgebra ℂ A) : Set A) :=
    StarAlgebra.subset_adjoin ℂ S
  have htop : wstar A ((StarAlgebra.adjoin ℂ S : StarSubalgebra ℂ A) : Set A)
      = ⊤ := top_le_iff.mp (hS ▸ wstar_mono hsub)
  have hdense : @Dense A (ultraweak A)
      ((StarAlgebra.adjoin ℂ S : StarSubalgebra ℂ A) : Set A) :=
    dense_of_wstar_eq_top _ htop
  refine le_trans (card_le_of_dense _ hdense) ?_
  have h2 : (2 : Cardinal.{u}) ≠ 0 := by norm_num
  exact Cardinal.power_le_power_left h2
    (Cardinal.power_le_power_left h2 (card_starAdjoin_le S))

end GenerationBound

/-! ### **125II** `vn-gns-bound`, stated ahead of its parsec

The bounded faithful representation of parsec **1250** is used by the proof
of **124III** just below — not by the thesis's proof, which relabels the
algebra rather than its representing Hilbert space, but by the divergence
described in the next block.  It is therefore stated here; the rest of parsec
1250 follows 124III as printed. -/

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

section GnsBound

/-! ### Cardinality infrastructure for 125II

The thesis's count (proc.tex:4820) is `#ℋ = Σ_ω #ℋ_ω`, which is **not**
the cardinality of a Hilbert direct sum over an uncountable index set: an
`ℓ²`-family has *countable support*, so `⊕_ω ℋ_ω` is a set of countable
partial functions and its cardinality is bounded by `(Σ_ω #ℋ_ω)^ℵ₀`, not by
`Σ_ω #ℋ_ω`.  Both bounds happen to come out at `2^#𝒜`, so the lemma stands;
the two private lemmas below supply the two estimates the printed proof
uses implicitly — "every vector of `ℋ_ω` is a limit of a sequence from `𝒜`"
and the countable-support bound. -/

/-- Infrastructure for **125II**: a Hausdorff Fréchet–Urysohn space carrying
a map with dense range from `X` has at most `#X ^ ℵ₀` points — every point is
the limit of a sequence from the dense range, and limits are unique.  (This
is the thesis's "every element of `ℋ_ω` is the limit of a sequence of
elements from `𝒜`".) -/
private theorem card_le_of_denseRange {X Y : Type u} [TopologicalSpace Y]
    [T2Space Y] [FrechetUrysohnSpace Y] {f : X → Y} (hf : DenseRange f) :
    #Y ≤ (#X) ^ ℵ₀ := by
  classical
  have key : ∀ y : Y, ∃ g : ℕ → X,
      Filter.Tendsto (fun n => f (g n)) Filter.atTop (nhds y) := by
    intro y
    have hy : y ∈ closure (Set.range f) := hf y
    rw [mem_closure_iff_seq_limit] at hy
    obtain ⟨x, hx, hlim⟩ := hy
    choose g hg using hx
    refine ⟨g, ?_⟩
    have hgx : (fun n => f (g n)) = x := funext hg
    rw [hgx]; exact hlim
  have hinj : Function.Injective (fun y : Y => (key y).choose) := by
    intro y z h
    have hy := (key y).choose_spec
    have hz := (key z).choose_spec
    rw [show (key y).choose = (key z).choose from h] at hy
    exact tendsto_nhds_unique hy hz
  refine (Cardinal.mk_le_of_injective hinj).trans_eq ?_
  simp

/-- Infrastructure for **125II**: a member of `ℓ²(E)` is determined by its
*graph* `{⟨i, y i⟩ : y i ≠ 0}`, which is countable because `Σᵢ‖yᵢ‖²`
converges; hence `#ℓ²(E) ≤ (#Σᵢ Eᵢ)^ℵ₀ + 1` (the `+ 1` is the zero vector,
whose graph is empty).  This is the step the thesis's `#ℋ = Σ_ω #ℋ_ω`
elides. -/
private theorem card_lp_two_le {ι : Type u} {E : ι → Type u}
    [∀ i, NormedAddCommGroup (E i)] :
    #(lp E 2) ≤ (#(Σ i, E i)) ^ ℵ₀ + 1 := by
  classical
  set S : lp E 2 → Set (Σ i, E i) :=
    fun y => {p | ((y : ∀ i, E i) p.1 = p.2) ∧ p.2 ≠ 0} with hS
  have hcount : ∀ y : lp E 2, (S y).Countable := by
    intro y
    have hmem : Memℓp (y : ∀ i, E i) 2 := y.2
    have hsum : Summable fun i => ‖(y : ∀ i, E i) i‖ ^ (2 : ℝ≥0∞).toReal :=
      (memℓp_gen_iff (by norm_num)).mp hmem
    have hsupp : (Function.support
        fun i => ‖(y : ∀ i, E i) i‖ ^ (2 : ℝ≥0∞).toReal).Countable :=
      hsum.countable_support
    have hsub : S y ⊆ (fun i => (⟨i, (y : ∀ i, E i) i⟩ : Σ i, E i)) ''
        (Function.support fun i => ‖(y : ∀ i, E i) i‖ ^ (2 : ℝ≥0∞).toReal) := by
      rintro ⟨i, x⟩ ⟨h1, h2⟩
      refine ⟨i, ?_, ?_⟩
      · show ‖(y : ∀ i, E i) i‖ ^ (2 : ℝ≥0∞).toReal ≠ 0
        have hx : (y : ∀ i, E i) i ≠ 0 := by rw [h1]; exact h2
        have hn : ‖(y : ∀ i, E i) i‖ ≠ 0 := norm_ne_zero_iff.mpr hx
        exact fun hc => hn (by
          have h0 : (0:ℝ) ≤ ‖(y : ∀ i, E i) i‖ := norm_nonneg _
          exact (Real.rpow_eq_zero_iff_of_nonneg h0).mp hc |>.1)
      · simp only [h1]
    exact (hsupp.image _).mono hsub
  have hinj : ∀ y z : lp E 2, S y = S z → y = z := by
    intro y z h
    refine Subtype.ext (funext fun i => ?_)
    by_cases hy : (y : ∀ i, E i) i = 0
    · by_cases hz : (z : ∀ i, E i) i = 0
      · rw [hy, hz]
      · have hmem : (⟨i, (z : ∀ i, E i) i⟩ : Σ i, E i) ∈ S z := ⟨rfl, hz⟩
        rw [← h] at hmem
        exact hmem.1
    · have hmem : (⟨i, (y : ∀ i, E i) i⟩ : Σ i, E i) ∈ S y := ⟨rfl, hy⟩
      rw [h] at hmem
      exact hmem.1.symm
  have hne : ∀ y : lp E 2, (S y).Nonempty →
      ∃ g : ℕ → (Σ i, E i), S y = Set.range g :=
    fun y hy => (hcount y).exists_eq_range hy
  set Φ : lp E 2 → Option (ℕ → (Σ i, E i)) :=
    fun y => if h : (S y).Nonempty then some (hne y h).choose else none with hΦ
  have hΦinj : Function.Injective Φ := by
    intro y z hyz
    refine hinj y z ?_
    by_cases hy : (S y).Nonempty <;> by_cases hz : (S z).Nonempty
    · rw [hΦ] at hyz
      simp only [dif_pos hy, dif_pos hz, Option.some.injEq] at hyz
      rw [(hne y hy).choose_spec, (hne z hz).choose_spec, hyz]
    · rw [hΦ] at hyz; simp only [dif_pos hy, dif_neg hz, reduceCtorEq] at hyz
    · rw [hΦ] at hyz; simp only [dif_neg hy, dif_pos hz, reduceCtorEq] at hyz
    · rw [Set.not_nonempty_iff_eq_empty] at hy hz; rw [hy, hz]
  refine (Cardinal.mk_le_of_injective hΦinj).trans_eq ?_
  rw [Cardinal.mk_option]
  congr 1
  simp

/-- Infrastructure for **125II**: there are at most `2^#𝒳` np-functionals on
an infinite `𝒳`, because each is a map `𝒳 → ℂ` (proc.tex:4826). -/
private theorem card_npFunctional_le {𝒳 : Type u} [CStarAlgebra 𝒳]
    [PartialOrder 𝒳] (h𝒳 : ℵ₀ ≤ #𝒳) :
    #(NPFunctional 𝒳) ≤ (2 : Cardinal.{u}) ^ #𝒳 := by
  have hinj : Function.Injective (fun ω : NPFunctional 𝒳 => (⇑ω : 𝒳 → ℂ)) :=
    fun _ _ h => DFunLike.coe_injective h
  refine le_trans (Cardinal.mk_le_of_injective hinj) ?_
  rw [Cardinal.mk_arrow, Cardinal.mk_complex, Cardinal.lift_continuum,
    Cardinal.lift_uzero, ← Cardinal.two_power_aleph0, ← Cardinal.power_mul,
    Cardinal.aleph0_mul_eq h𝒳]

/-- Infrastructure for **125II**: the direct-sum GNS space of a *nontrivial*
von Neumann algebra has at most `2^#𝒳` vectors (proc.tex:4820). -/
private theorem card_gnsHilb_le {𝒳 : Type u} [CStarAlgebra 𝒳]
    [PartialOrder 𝒳] [StarOrderedRing 𝒳] [Nontrivial 𝒳] :
    #(gnsHilb 𝒳) ≤ (2 : Cardinal.{u}) ^ #𝒳 := by
  have hinfX : Infinite 𝒳 := Infinite.of_injective (algebraMap ℂ 𝒳)
    (RingHom.injective (algebraMap ℂ 𝒳))
  have h𝒳 : ℵ₀ ≤ #𝒳 := Cardinal.infinite_iff.mp hinfX
  have hXle : #𝒳 ≤ (2 : Cardinal.{u}) ^ #𝒳 := (Cardinal.cantor _).le
  have hkey : ((2 : Cardinal.{u}) ^ #𝒳) ^ ℵ₀ = (2 : Cardinal.{u}) ^ #𝒳 := by
    rw [← Cardinal.power_mul, Cardinal.mul_aleph0_eq h𝒳]
  have hpowX : (#𝒳) ^ ℵ₀ ≤ (2 : Cardinal.{u}) ^ #𝒳 :=
    le_trans (Cardinal.power_le_power_right hXle) hkey.le
  have hinf2 : ℵ₀ ≤ (2 : Cardinal.{u}) ^ #𝒳 := le_trans h𝒳 hXle
  have hGNS : ∀ ω : NPFunctional 𝒳,
      #(ω.toPositiveLinearMap.GNS) ≤ (2 : Cardinal.{u}) ^ #𝒳 := fun ω =>
    le_trans (card_le_of_denseRange (gnsVec_denseRange ω)) hpowX
  have hsigma : #(Σ ω : NPFunctional 𝒳, ω.toPositiveLinearMap.GNS)
      ≤ (2 : Cardinal.{u}) ^ #𝒳 := by
    rw [Cardinal.mk_sigma]
    calc (Cardinal.sum fun ω : NPFunctional 𝒳 => #(ω.toPositiveLinearMap.GNS))
        ≤ Cardinal.sum fun _ : NPFunctional 𝒳 => (2 : Cardinal.{u}) ^ #𝒳 :=
          Cardinal.sum_le_sum _ _ hGNS
      _ = #(NPFunctional 𝒳) * (2 : Cardinal.{u}) ^ #𝒳 := Cardinal.sum_const' _ _
      _ ≤ ((2 : Cardinal.{u}) ^ #𝒳) * ((2 : Cardinal.{u}) ^ #𝒳) := by
          gcongr; exact card_npFunctional_le h𝒳
      _ = (2 : Cardinal.{u}) ^ #𝒳 := Cardinal.mul_eq_self hinf2
  calc #(gnsHilb 𝒳)
      ≤ (#(Σ ω : NPFunctional 𝒳, ω.toPositiveLinearMap.GNS)) ^ ℵ₀ + 1 :=
        card_lp_two_le
    _ ≤ ((2 : Cardinal.{u}) ^ #𝒳) ^ ℵ₀ + 1 :=
        add_le_add (Cardinal.power_le_power_right hsigma) le_rfl
    _ = (2 : Cardinal.{u}) ^ #𝒳 + 1 := by rw [hkey]
    _ = (2 : Cardinal.{u}) ^ #𝒳 := Cardinal.add_one_eq hinf2

variable (A) in
/-- **125II** (`vn-gns-bound`, proc.tex:4814, Lemma): a von Neumann
algebra `𝒜` can be faithfully represented on a Hilbert space with no more
than `2^#𝒜` vectors.

The representation is the thesis's: the direct-sum GNS representation
`ϱ_Ω : 𝒜 → B(⊕_ω ℋ_ω)` over *all* np-functionals (48V/48VIII, `gnsRep`),
which is faithful and normal.  The count follows the thesis for `#Ω` and
`#ℋ_ω`, but not for `#ℋ`: see `card_lp_two_le` above. -/
theorem vn_gns_bound [VonNeumannAlgebra A] :
    ∃ r : ConcreteRep A, #r.space ≤ (2 : Cardinal.{u}) ^ #A := by
  refine ⟨{ space := gnsHilb A
            rep := ⟨gnsRep, gnsRep_normal⟩
            injective := gnsRep_injective }, ?_⟩
  show #(gnsHilb A) ≤ (2 : Cardinal.{u}) ^ #A
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · -- the thesis's `𝒜 = {0}` case: every `ℋ_ω` is a point, and so is `ℋ`
    have huniq : Unique A := uniqueOfSubsingleton (0 : A)
    have hA1 : #A = 1 := Cardinal.mk_eq_one A
    have hsubGNS : ∀ ω : NPFunctional A,
        Subsingleton ω.toPositiveLinearMap.GNS := by
      intro ω
      refine Cardinal.le_one_iff_subsingleton.mp ?_
      refine le_trans (card_le_of_denseRange (gnsVec_denseRange ω)) ?_
      rw [hA1, Cardinal.one_power]
    have hss : Subsingleton (gnsHilb A) :=
      ⟨fun a b => Subtype.ext (funext fun ω => (hsubGNS ω).elim _ _)⟩
    refine le_trans (Cardinal.le_one_iff_subsingleton.mpr hss) ?_
    rw [hA1, Cardinal.power_one]
    exact one_le_two
  · exact card_gnsHilb_le

end GnsBound

/-! ### Infrastructure for **124III**

proc.tex:4718 proves 124III from **Freyd's adjoint functor theorem**: `W*_miu`
has products (**47IV**) and equalisers (**47V**), hence all limits, the
inclusion `U : W*_miu → W*_cpsu` preserves them, and the *solution set
condition* is checked by hand.

Two divergences from the printed proof, both forced.

* **Freyd's theorem itself is not invoked.**  Mathlib's general adjoint
  functor theorem (`CategoryTheory.isRightAdjoint_of_preservesLimits_of_`
  `solutionSetCondition`) is stated for `Category` instances, and neither
  `W*_miu` nor `W*_cpsu` is bundled as one in this development (**47II** is
  deliberately unbundled — its products and equalisers are stated through
  their universal properties).  Bundling both categories, their limits and
  the functor, only to unbundle the resulting adjunction into the universal
  arrow `FreeMIU A` asks for, is more work than Freyd's construction, which
  here collapses to two lines: `F(𝒜)` is the von Neumann subalgebra of the
  product `∏ᵢ 𝒞ᵢ` over the solution set **generated by the range of the
  mediating map** `η`.  Existence of the factorisation is weak initiality of
  the product; uniqueness is **47V** — two nmiu-maps out of `F(𝒜)` agreeing
  on `η(𝒜)` agree on the von Neumann subalgebra it generates, which is all
  of `F(𝒜)`.  Freyd's equaliser-of-all-endomorphisms step is not needed.
* **The solution set is indexed differently.**  proc.tex takes "von Neumann
  algebras carried on a subset of `κ`", which would need the whole
  C*-algebra structure transported along a relabelling bijection.  Here the
  index is a *von Neumann subalgebra of `B(ℓ²(T))` for a subset `T ⊆ K`* of a
  fixed `K` with `#K = 2^{2^{2^{𝔠+#𝒜}}}`, so that the only transport needed
  is of the **Hilbert space**: `lpReindex` moves `ℓ²(ι)` to `ℓ²(T)` along a
  bijection `ι ≃ T`, and `LinearIsometryEquiv.conjStarAlgEquiv` carries the
  algebra with it.  The cardinal bookkeeping is **124I** (for `#𝒜` after
  generation) followed by **125II** (for the dimension of the representing
  Hilbert space), so both of this file's earlier lemmas are used. -/

section SecondAdjunction

/-! #### Von Neumann subalgebras, relatively

`VNSub` bundles a von Neumann subalgebra as an algebra; what 124III needs in
addition is that the bundling is *transparent* for the three notions the
proof manipulates: matrix positivity, suprema, and von Neumann
subalgebras. -/

private theorem vnsub_val_sum {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}
    {n : ℕ} (F : Fin n → VNSub A S hS) :
    (∑ i, F i).val = ∑ i, (F i).val :=
  map_sum (VNSub.valAddHom (A := A) (S := S) (hS := hS)) F Finset.univ

/-- Positivity of a matrix over a von Neumann subalgebra is positivity of its
image in the ambient algebra.  The quadratic-form criterion **33II**
transports, because the order on `VNSub` is the restricted one
(`VNSub.le_def` is `Iff.rfl`). -/
private theorem vnsub_nonneg_of_map_val {S : StarSubalgebra ℂ A}
    {hS : IsVNSubalgebra A S} (k : ℕ)
    (M : CStarMatrix (Fin k) (Fin k) (VNSub A S hS))
    (h : 0 ≤ M.map VNSub.val) : 0 ≤ M := by
  rw [Theses.A.CStar.cstar_matrix_positive_iff]
  intro a
  have h2 := (Theses.A.CStar.cstar_matrix_positive_iff _).mp h (fun i => (a i).val)
  refine (VNSub.le_def 0 _).mpr ?_
  rw [VNSub.val_zero]
  have key : (∑ i, ∑ j, star (a i) * M i j * a j).val
      = ∑ i, ∑ j, star ((a i).val) * (M.map VNSub.val) i j * ((a j).val) := by
    rw [vnsub_val_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vnsub_val_sum]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [key]
  exact h2

/-- A supremum in a von Neumann subalgebra is one in the ambient algebra
(the converse of `VNSub.isLUB_saMap_image`, for plain elements). -/
private theorem vnsub_isLUB_of_val {S : StarSubalgebra ℂ A}
    {hS : IsVNSubalgebra A S} {T : Set (VNSub A S hS)} {x : VNSub A S hS}
    (h : IsLUB (VNSub.val '' T) x.val) : IsLUB T x := by
  constructor
  · intro t ht
    exact h.1 ⟨t, ht, rfl⟩
  · intro u hu
    refine h.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hu ht

/-- Corestriction of an ncpsu-map to a von Neumann subalgebra containing its
range — the companion of `nmiuCorestrict`, and of `exists_ncpCorestrict`
(`Measurement.lean`) for corners. -/
private theorem exists_ncpsuCorestrict [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (S : StarSubalgebra ℂ B) (hS : IsVNSubalgebra B S) (f : NCPSUMap A B)
    (hf : ∀ a : A, f.toNCPMap a ∈ S) :
    ∃ g : NCPSUMap A (VNSub B S hS), ∀ a : A, (g.toNCPMap a).val = f.toNCPMap a := by
  refine ⟨{ toNCPMap :=
              { toCompletelyPositiveMap :=
                  { toFun := fun a => ⟨f.toNCPMap a, hf a⟩
                    map_add' := fun x y => VNSub.val_injective (by
                      show (f.toNCPMap (x + y) : B) = f.toNCPMap x + f.toNCPMap y
                      exact map_add f.toNCPMap.toCompletelyPositiveMap.toLinearMap x y)
                    map_smul' := fun z x => VNSub.val_injective (by
                      show (f.toNCPMap (z • x) : B) = z • f.toNCPMap x
                      exact map_smul f.toNCPMap.toCompletelyPositiveMap.toLinearMap z x)
                    map_cstarMatrix_nonneg' := fun k M hM => ?_ }
                preservesDirSups' := ?_ }
            subunital' := ?_ }, fun _ => rfl⟩
  · refine vnsub_nonneg_of_map_val k _ ?_
    have hkey : ∀ N : CStarMatrix (Fin k) (Fin k) (VNSub B S hS),
        (∀ i j, (N i j).val
          = M.map ⇑f.toNCPMap.toCompletelyPositiveMap.toLinearMap i j) →
        0 ≤ N.map VNSub.val := by
      intro N hN
      have hNe : N.map VNSub.val
          = M.map ⇑f.toNCPMap.toCompletelyPositiveMap.toLinearMap := by
        ext i j
        rw [CStarMatrix.map_apply]
        exact hN i j
      rw [hNe]
      exact f.toNCPMap.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
    exact hkey _ fun _ _ => rfl
  · intro D s hne hdir hlub
    refine vnsub_isLUB_of_val ?_
    have h := f.toNCPMap.preservesDirSups' D s hne hdir hlub
    rw [← Set.image_comp]
    exact h
  · show (⟨f.toNCPMap 1, hf 1⟩ : VNSub B S hS) ≤ 1
    exact f.subunital'

/-- A von Neumann subalgebra of a von Neumann subalgebra is one of the
ambient algebra.  Closedness is the isometric closed embedding `val`;
directed suprema transfer because `val` reflects them
(`vnsub_isLUB_of_val`). -/
private theorem vnsub_isVNSubalgebra_map [VonNeumannAlgebra A]
    {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}
    (T : StarSubalgebra ℂ (VNSub A S hS)) (hT : IsVNSubalgebra (VNSub A S hS) T) :
    IsVNSubalgebra A (T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))) := by
  have hce := (AddMonoidHomClass.isometry_of_norm
    (VNSub.valAddHom (A := A) (S := S) (hS := hS)) (fun _ => rfl)).isClosedEmbedding
  have hmem : ∀ x : A, x ∈ T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS)) ↔
      ∃ t : VNSub A S hS, t ∈ T ∧ t.val = x := by
    intro x
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  constructor
  · have hcoe : ((T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))) : Set A)
        = VNSub.val '' (T : Set (VNSub A S hS)) := by
      ext x
      simp only [Set.mem_image, SetLike.mem_coe, hmem]
    rw [hcoe]
    exact hce.isClosedMap _ hT.isClosed
  · intro D s hDS hne hdir hlub
    have hlift : ∀ d ∈ D, ∃ t : selfAdjoint (VNSub A S hS),
        t.1 ∈ T ∧ VNSub.saMap t = d := by
      intro d hd
      obtain ⟨t, ht, hte⟩ := (hmem _).mp (hDS d hd)
      refine ⟨⟨t, ?_⟩, ht, Subtype.ext hte⟩
      exact VNSub.val_injective (by rw [VNSub.val_star, hte]; exact d.2)
    have hsS : (s : A) ∈ S := by
      refine hS.dirSup_mem D s (fun d hd => ?_) hne hdir hlub
      obtain ⟨t, ht, hte⟩ := hlift d hd
      exact hte ▸ t.1.property
    set s' : selfAdjoint (VNSub A S hS) :=
      ⟨⟨(s : A), hsS⟩, VNSub.val_injective s.2⟩ with hs'
    set D' : Set (selfAdjoint (VNSub A S hS)) :=
      {t | t.1 ∈ T ∧ VNSub.saMap t ∈ D} with hD'
    have hD'ne : D'.Nonempty := by
      obtain ⟨d, hd⟩ := hne
      obtain ⟨t, ht, hte⟩ := hlift d hd
      exact ⟨t, ht, hte ▸ hd⟩
    have hD'dir : DirectedOn (· ≤ ·) D' := by
      rintro t ⟨htT, htD⟩ u ⟨huT, huD⟩
      obtain ⟨v, hv, htv, huv⟩ := hdir _ htD _ huD
      obtain ⟨w, hw, hwe⟩ := hlift v hv
      exact ⟨w, ⟨hw, hwe ▸ hv⟩, by rw [← hwe] at htv; exact htv,
        by rw [← hwe] at huv; exact huv⟩
    have hD'lub : IsLUB D' s' := by
      constructor
      · rintro t ⟨-, htD⟩
        exact hlub.1 htD
      · intro u hu
        have h2 : s ≤ VNSub.saMap u := by
          refine hlub.2 ?_
          intro d hd
          obtain ⟨t, ht, hte⟩ := hlift d hd
          exact hte ▸ hu ⟨ht, hte ▸ hd⟩
        exact h2
    have := hT.dirSup_mem D' s' (fun t ht => ht.1) hD'ne hD'dir hD'lub
    exact (hmem _).mpr ⟨s'.1, this, rfl⟩

/-- **The minimality of `W*(G)` is inherited by the bundled subalgebra**: a
von Neumann subalgebra of `W*(G)` containing (the copies of) the elements of
`G` is everything.  This single lemma does two jobs below — it is what makes
`W*(G)`, as an algebra in its own right, *generated* by `G` (so that **124I**
applies to it), and it is the uniqueness half of 124III. -/
private theorem vnsub_wstar_eq_top [VonNeumannAlgebra A] {G : Set A}
    {hSw : IsVNSubalgebra A (wstar A G)}
    (T : StarSubalgebra ℂ (VNSub A (wstar A G) hSw))
    (hT : IsVNSubalgebra (VNSub A (wstar A G) hSw) T)
    (hGT : ∀ x : VNSub A (wstar A G) hSw, x.val ∈ G → x ∈ T) : T = ⊤ := by
  have hmap := vnsub_isVNSubalgebra_map T hT
  have hsub : G ⊆ ((T.map (VNSub.valStarAlgHom
      (A := A) (S := wstar A G) (hS := hSw))) : Set A) := by
    intro g hg
    exact ⟨⟨g, (isVNSubalgebra_wstar G).2 hg⟩, hGT _ hg, rfl⟩
  have hle : wstar A G ≤ T.map (VNSub.valStarAlgHom
      (A := A) (S := wstar A G) (hS := hSw)) :=
    sInf_le (show _ ∈ {T : StarSubalgebra ℂ A | IsVNSubalgebra A T ∧ G ⊆ T} from
      ⟨hmap, hsub⟩)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨t, ht, hte⟩ := hle x.property
  exact (VNSub.val_injective hte : t = x) ▸ ht

/-! #### Relabelling: `ℓ²` along a bijection of index sets

This is the ingredient that replaces proc.tex's "von Neumann algebra on a
subset of `κ`".  A bijection of index sets induces a unitary of the
`ℓ²`-spaces, hence (`conjStarAlgEquiv`) an nmiu-isomorphism of the algebras
of operators, along which von Neumann subalgebras transport
(`isVNSubalgebra_map`). -/

private theorem two_toReal_pos : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num

private def lpReindexFun {ι ι' : Type u} (e : ι ≃ ι')
    (f : lp (fun _ : ι => ℂ) 2) : lp (fun _ : ι' => ℂ) 2 :=
  ⟨fun j => (f : ∀ _ : ι, ℂ) (e.symm j), by
    show Memℓp (fun j => (f : ∀ _ : ι, ℂ) (e.symm j)) 2
    rw [memℓp_gen_iff two_toReal_pos]
    exact (Equiv.summable_iff e.symm).mpr
      ((memℓp_gen_iff (E := fun _ : ι => ℂ) (p := 2) two_toReal_pos).mp f.2)⟩

/-- Reindexing `ℓ²` along a bijection of index sets is a unitary. -/
private def lpReindex {ι ι' : Type u} (e : ι ≃ ι') :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι' => ℂ) 2 where
  toFun := lpReindexFun e
  invFun := lpReindexFun e.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    refine lp.ext (funext fun i => ?_)
    show (f : ∀ _ : ι, ℂ) (e.symm (e i)) = _
    rw [e.symm_apply_apply]
  right_inv f := by
    refine lp.ext (funext fun j => ?_)
    show (f : ∀ _ : ι', ℂ) (e (e.symm j)) = _
    rw [e.apply_symm_apply]
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
    congr 1
    exact Equiv.tsum_eq e.symm (fun i => ‖(f : ∀ _ : ι, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal)

/-- `ℓ²(T)` for a subset `T` of the index type `K`. -/
@[reducible] private def ell2 {K : Type u} (T : Set K) := lp (fun _ : T => ℂ) 2

/-- `B(ℓ²(T))`: the algebras out of which the solution set is built. -/
@[reducible] private def opAlg {K : Type u} (T : Set K) := ell2 T →L[ℂ] ell2 T

/-- **The relabelling step of 124III**: a von Neumann algebra small enough
that `2^{#𝒳} ≤ #K` is nmiu-isomorphic to a von Neumann subalgebra of
`B(ℓ²(T))` for some `T ⊆ K`.  By **125II** it acts faithfully and normally on
a Hilbert space of cardinality at most `2^{#𝒳}`, whose orthonormal basis
therefore injects into `K`; `lpReindex` and `conjStarAlgEquiv` move the
representation onto `ℓ²(T)`. -/
private theorem exists_smallRealization {K : Type u} (𝒳 : Type u) [CStarAlgebra 𝒳]
    [PartialOrder 𝒳] [StarOrderedRing 𝒳] [VonNeumannAlgebra 𝒳]
    (hK : (2 : Cardinal.{u}) ^ (#𝒳) ≤ #K) :
    ∃ (T : Set K) (S : StarSubalgebra ℂ (opAlg T))
      (hS : IsVNSubalgebra (opAlg T) S)
      (ε : NMIUMap 𝒳 (VNSub (opAlg T) S hS)), Function.Bijective ⇑ε := by
  obtain ⟨r, hcard⟩ := vn_gns_bound 𝒳
  obtain ⟨w, bas, -⟩ := exists_hilbertBasis ℂ r.space
  have hw : #(w : Set r.space) ≤ #K :=
    le_trans (Cardinal.mk_set_le w) (le_trans hcard hK)
  obtain ⟨j⟩ := (Cardinal.le_def _ _).mp hw
  set T : Set K := Set.range j with hT
  set e : (w : Set r.space) ≃ (T : Set K) := Equiv.ofInjective j j.injective with he
  set U : r.space ≃ₗᵢ[ℂ] ell2 T := bas.repr.trans (lpReindex e) with hU
  set Φ : (r.space →L[ℂ] r.space) ≃⋆ₐ[ℂ] opAlg T := U.conjStarAlgEquiv with hΦ
  set g : 𝒳 →⋆ₐ[ℂ] opAlg T := Φ.toStarAlgHom.comp r.rep.toStarAlgHom with hg
  have hginj : Function.Injective ⇑g := fun x y hxy => r.injective (Φ.injective hxy)
  have hgn : PreservesDirSups ⇑g :=
    preservesDirSups_pmap_comp (starAlgHomP r.rep.toStarAlgHom) r.rep.preservesDirSups'
      (starAlgHomP Φ.toStarAlgHom) (starAlgEquiv_preservesDirSups Φ)
  refine ⟨T, g.range, isVNSubalgebra_range g hginj hgn,
    nmiuCorestrict ⟨g, hgn⟩ _ (isVNSubalgebra_range g hginj hgn) (fun a => ⟨a, rfl⟩),
    nmiuCorestrict_bijective _ _ _ _ hginj ?_⟩
  rintro _ ⟨a, rfl⟩
  exact ⟨a, rfl⟩

/-! #### The solution set -/

/-- Composition of an ncpsu-map with an nmiu-map. -/
private def ncpsuCompNmiu (g : NMIUMap B C) (f : NCPSUMap A B) : NCPSUMap A C :=
  ⟨ncpComp (nmiuNCP g) f.toNCPMap, by
    show (ncpComp (nmiuNCP g) f.toNCPMap) 1 ≤ 1
    rw [ncpComp_apply]
    refine le_trans (OrderHomClass.mono
      (nmiuNCP g).toCompletelyPositiveMap f.subunital') ?_
    show (g 1 : C) ≤ 1
    exact le_of_eq (map_one g.toStarAlgHom)⟩

private theorem ncpsuCompNmiu_apply (g : NMIUMap B C) (f : NCPSUMap A B) (x : A) :
    (ncpsuCompNmiu g f).toNCPMap x = g (f.toNCPMap x) :=
  ncpComp_apply (nmiuNCP g) f.toNCPMap x

/-- The index of the solution set of **124III**: a von Neumann subalgebra of
`B(ℓ²(T))` for a subset `T` of the fixed index type `K`, together with an
ncpsu-map into it from `𝒜`.  Because `VonNeumannAlgebra` is a `Prop` class
and `StarSubalgebra ℂ (opAlg T)` is a *set* of operators, this lives in
`Type u` — which is the whole point of the solution set condition. -/
private structure SolIdx (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (K : Type u) : Type u where
  T : Set K
  S : StarSubalgebra ℂ (opAlg T)
  hS : IsVNSubalgebra (opAlg T) S
  hnt : Nontrivial (VNSub (opAlg T) S hS)
  γ : NCPSUMap A (VNSub (opAlg T) S hS)

/-- **The solution set condition** (proc.tex:4718): every ncpsu-map from `𝒜`
into a *nontrivial* von Neumann algebra factors as an nmiu-map after one of
the `γᵢ`.  The algebra `ℬ' = W*(f(𝒜))` has at most `2^{2^{𝔠+#𝒜}}` elements by
**124I** — applicable because `vnsub_wstar_eq_top` says `ℬ'`, as an algebra,
is generated by `f(𝒜)` — and `exists_smallRealization` then puts it on
`ℓ²(T)`.  (The trivial target is handled separately, in 124III itself: the
product of **47IV** needs every factor nontrivial.) -/
private theorem solution_set (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] {K : Type u}
    (hK : #K = 2 ^ ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      (Cardinal.continuum + #A)))
    {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [VonNeumannAlgebra B] [Nontrivial B] (f : NCPSUMap A B) :
    ∃ (i : SolIdx A K) (h : NMIUMap (VNSub (opAlg i.T) i.S i.hS) B),
      ∀ a : A, h ((i.γ).toNCPMap a) = f.toNCPMap a := by
  classical
  have h2 : (2 : Cardinal.{u}) ≠ 0 := by norm_num
  set G : Set B := Set.range (fun a : A => f.toNCPMap a) with hG
  have hw := isVNSubalgebra_wstar (A := B) G
  obtain ⟨f', hf'⟩ := exists_ncpsuCorestrict (wstar B G) hw.1 f (fun a => hw.2 ⟨a, rfl⟩)
  have hgen : wstar (VNSub B (wstar B G) hw.1)
      (VNSub.val ⁻¹' G) = ⊤ := by
    refine vnsub_wstar_eq_top _ (isVNSubalgebra_wstar _).1 fun x hx => ?_
    exact (isVNSubalgebra_wstar (A := VNSub B (wstar B G) hw.1)
      (VNSub.val ⁻¹' G)).2 hx
  have hcardG : #((VNSub.val ⁻¹' G : Set (VNSub B (wstar B G) hw.1))) ≤ #A := by
    refine le_trans (Cardinal.mk_le_of_injective
      (f := fun x : (VNSub.val ⁻¹' G : Set (VNSub B (wstar B G) hw.1)) =>
        (⟨x.val.val, x.property⟩ : G)) ?_) ?_
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      exact Subtype.ext (VNSub.val_injective (congrArg Subtype.val h))
    · exact Cardinal.mk_range_le
  have hcard : #(VNSub B (wstar B G) hw.1) ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (Cardinal.continuum + #A) := by
    refine le_trans (vn_generation_bound _ hgen) ?_
    exact Cardinal.power_le_power_left h2 (Cardinal.power_le_power_left h2
      (add_le_add le_rfl hcardG))
  obtain ⟨T, S, hS, ε, hεbij⟩ :=
    exists_smallRealization (K := K) (VNSub B (wstar B G) hw.1)
      (by rw [hK]; exact Cardinal.power_le_power_left h2 hcard)
  have hntB' : Nontrivial (VNSub B (wstar B G) hw.1) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg VNSub.val h)⟩⟩
  have hntS : Nontrivial (VNSub (opAlg T) S hS) :=
    ⟨⟨ε 1, ε 0, fun h => one_ne_zero (hεbij.1 h)⟩⟩
  refine ⟨⟨T, S, hS, hntS, ncpsuCompNmiu ε f'⟩,
    nmiuComp VNSub.valNMIU (nmiuSymm ε hεbij), fun a => ?_⟩
  show VNSub.valNMIU (nmiuSymm ε hεbij
    ((ncpsuCompNmiu ε f').toNCPMap a)) = f.toNCPMap a
  rw [ncpsuCompNmiu_apply, nmiuSymm_apply_apply]
  exact hf' a

private instance solNontrivial {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {K : Type u} (i : SolIdx A K) :
    Nontrivial (VNSub (opAlg i.T) i.S i.hS) := i.hnt

/-- The product `∏ᵢ 𝒞ᵢ` over the solution set (**47IV**). -/
@[reducible] private def solProd (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) : Type u :=
  lp (fun i : SolIdx A K => VNSub (opAlg i.T) i.S i.hS) ∞

end SecondAdjunction


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

set_option maxHeartbeats 1000000 in
variable (A) in
/-- **124III** (`second-adjunction`, proc.tex:4718, Theorem): the
inclusion `W*_miu → W*_cpsu` has a left adjoint `F` — rendered: every von
Neumann algebra has a universal arrow to the inclusion. -/
theorem second_adjunction [VonNeumannAlgebra A] : Nonempty (FreeMIU A) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : Type u, #K = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (2 : Cardinal.{u}) ^ (Cardinal.continuum + #A)) := ⟨_, Cardinal.mk_out _⟩
  obtain ⟨η, hη, -⟩ := vn_products_ncpsu
    (fun i : SolIdx A K => VNSub (opAlg i.T) i.S i.hS) (fun i => i.γ)
  have hw := isVNSubalgebra_wstar (A := solProd A K)
    (Set.range (fun a : A => η.toNCPMap a))
  obtain ⟨η', hη'⟩ :=
    exists_ncpsuCorestrict (wstar (solProd A K) (Set.range (fun a : A => η.toNCPMap a)))
      hw.1 η (fun a => hw.2 ⟨a, rfl⟩)
  refine ⟨{ carrier := VNSub (solProd A K)
              (wstar (solProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1
            unit := η'
            universal := fun B _ _ _ _ f => ?_ }⟩
  rcases subsingleton_or_nontrivial B with hsub | hntB
  · -- a trivial target admits exactly one nmiu-map, the zero map
    exact ⟨{ toStarAlgHom :=
               { toFun := fun _ => 0
                 map_one' := Subsingleton.elim _ _
                 map_mul' := fun _ _ => Subsingleton.elim _ _
                 map_zero' := rfl
                 map_add' := fun _ _ => Subsingleton.elim _ _
                 commutes' := fun _ => Subsingleton.elim _ _
                 map_star' := fun _ => Subsingleton.elim _ _ }
             preservesDirSups' := fun D s _ _ _ =>
               ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
                fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩ },
      fun _ => Subsingleton.elim _ _,
      fun _ _ => DFunLike.coe_injective (funext fun _ => Subsingleton.elim _ _)⟩
  · -- weak initiality: factor through the solution set, then project
    obtain ⟨i, h, hh⟩ := solution_set A hK f
    obtain ⟨g, hgeq⟩ : ∃ g : NMIUMap (VNSub (solProd A K)
          (wstar (solProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1) B,
        ∀ x, g x = h (lpEvalSAH i x.val) :=
      ⟨nmiuComp (nmiuComp h ⟨lpEvalSAH i,
        vn_products_proj_normal
          (fun j : SolIdx A K => VNSub (opAlg j.T) j.S j.hS) i⟩)
        VNSub.valNMIU, fun _ => rfl⟩
    have hgval : ∀ a : A, f.toNCPMap a = g (η'.toNCPMap a) := by
      intro a
      rw [hgeq (η'.toNCPMap a), hη' a]
      simp only [lpEvalSAH_apply]
      rw [hη i a]
      exact (hh a).symm
    refine ⟨g, hgval, fun g' hg' => ?_⟩
    -- uniqueness: the equaliser (**47V**) is a von Neumann subalgebra
    -- containing the range of the unit, which generates the whole algebra
    obtain ⟨E, hE, hEset⟩ := vn_equalisers g' g
    have hEtop : E = ⊤ := by
      refine vnsub_wstar_eq_top E hE fun x hx => ?_
      obtain ⟨a, ha⟩ := hx
      have hx' : x = η'.toNCPMap a := VNSub.val_injective (by rw [hη' a]; exact ha.symm)
      have hgg : g' x = g x := by rw [hx', ← hg' a, ← hgval a]
      rw [← SetLike.mem_coe, hEset]
      exact hgg
    refine DFunLike.coe_injective (funext fun x => ?_)
    have hxE : x ∈ (E : Set (VNSub (solProd A K)
        (wstar (solProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1)) := by
      rw [hEtop]; trivial
    rw [hEset] at hxE
    exact hxE

/-! ## Parsec 1250: the free exponential

(**125II** `vn-gns-bound` and its `ConcreteRep` are stated above, ahead of
this parsec, because **124III**'s proof uses them.) -/

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

/-! ### Infrastructure for **125bII**

proc.tex:5250 says the proof is "exactly as in" 124III
(`second_adjunction`), and it is: Freyd again, with the solution set cut
down to the *hereditarily atomic* targets.  Three things change, all of
them simplifications.

* **The solution set is indexed by direct sums of matrix algebras**, not by
  von Neumann algebras carried on a subset of a cardinal.  A hereditarily
  atomic algebra *is* a `⊕ⱼ M_{Nⱼ+1}` — that is **84bII**, the definition
  used here — so the only relabelling needed is of the *index set of the
  summands*, which is `exists_lp_reindex` (written for 125cIII, moved up to
  here), and not of a Hilbert space.  In particular **125II**
  `vn_gns_bound` and `exists_smallRealization` are *not* used, and the
  index type `K` needs only `#K = 2^(2^(𝔠+#𝒜))` — one exponential less than
  124III.
* **The product over the solution set is formed flat.**  proc.tex:5257
  needs "a direct sum of hereditarily atomic algebras is hereditarily
  atomic"; here the product is taken over the `Σ`-type of pairs
  (solution-set entry, one of its summands) from the start, so it is
  *literally* a direct sum of matrix algebras and its hereditary atomicity
  is `StarAlgEquiv.refl`.  What would have been the flattening isomorphism
  becomes a single block projection `⊕_{(i,j)} M → ⊕ⱼ M`, which is just
  **47IV** applied to the coordinate projections.
* **No nontriviality side condition.**  124III's `SolIdx` carries a
  `Nontrivial` field because **47IV** needs nontrivial factors, and its
  proof splits off the trivial target; here the factors are matrix algebras
  `M_{N+1}`, so both disappear.

`ha_second_adjunction` does **not** use `hA`, and cannot: the carrier is a
von Neumann subalgebra of a direct sum of matrix algebras whatever `𝒜` is,
so `F_ha` exists for *every* von Neumann algebra.  The hypothesis is kept
because the thesis states the adjunction with `haW*_cpsu` as its domain. -/

section HaSecondAdjunction

universe u₁ u₂ u₃ u₄

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
  [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]

/-! #### Helpers shared with 125cIII

The next three declarations were written for `Fha_concrete` (125cIII,
"helpers 4 and 5" of the `FhaAux` block below) and are used again here;
they live at this point in the file only because 125bII comes first. -/

/-! ### helper 4: composing an ncpsu-map with an nmiu-map, across universes -/

private theorem exists_ncpsuCompNmiu' (g : NMIUMap Y Z) (f : NCPSUMap X Y) :
    ∃ h : NCPSUMap X Z, ∀ x : X, h.toNCPMap x = g (f.toNCPMap x) := by
  have hmono : ∀ x y : X, x ≤ y → f.toNCPMap x ≤ f.toNCPMap y := fun x y h =>
    OrderHomClass.mono f.toNCPMap.toCompletelyPositiveMap h
  have hsa : ∀ x : X, IsSelfAdjoint x → IsSelfAdjoint (f.toNCPMap x) := fun x hx =>
    isSelfAdjoint_map_of_pos
      (PositiveLinearMap.ofClass f.toNCPMap.toCompletelyPositiveMap) hx
  refine ⟨{ toNCPMap :=
              { toCompletelyPositiveMap :=
                  { toLinearMap :=
                      ((nmiuNCP g).toCompletelyPositiveMap.toLinearMap).comp
                        f.toNCPMap.toCompletelyPositiveMap.toLinearMap
                    map_cstarMatrix_nonneg' := fun k M hM => by
                      have h1 : (0 : CStarMatrix (Fin k) (Fin k) Y) ≤
                          M.map f.toNCPMap.toCompletelyPositiveMap.toLinearMap :=
                        f.toNCPMap.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
                      exact (nmiuNCP g).toCompletelyPositiveMap.map_cstarMatrix_nonneg'
                        k _ h1 }
                preservesDirSups' := by
                  exact preservesDirSups_comp (f := ⇑f.toNCPMap) (g := ⇑(nmiuNCP g))
                    hsa hmono f.toNCPMap.preservesDirSups' (nmiuNCP g).preservesDirSups' }
            subunital' := ?_ }, fun _ => rfl⟩
  show g (f.toNCPMap 1) ≤ 1
  refine le_trans (starAlgHom_mono' g.toStarAlgHom f.subunital') ?_
  exact le_of_eq (map_one g.toStarAlgHom)




/-- The coordinate projection as an nmiu-map. -/
private def lpEvalNMIU {I : Type u₁} (𝒜 : I → Type u₄) [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] (j : I) : NMIUMap (lp 𝒜 ∞) (𝒜 j) :=
  ⟨lpEvalSAH j, vn_products_proj_normal 𝒜 j⟩

/-! ### helper 5: reindexing a direct sum along a bijection of index sets -/

private theorem exists_lp_reindex {I₁ : Type u₁} {I₂ : Type u₂} {𝒜 : I₂ → Type u₄}
    {ℬ : I₁ → Type u₄}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
    [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]
    [∀ i, CStarAlgebra (ℬ i)] [∀ i, Nontrivial (ℬ i)] [∀ i, PartialOrder (ℬ i)]
    [∀ i, StarOrderedRing (ℬ i)] [∀ i, VonNeumannAlgebra (ℬ i)]
    (e : I₁ ≃ I₂) (u : ∀ i : I₁, NMIUMap (𝒜 (e i)) (ℬ i))
    (hu : ∀ i, Function.Bijective ⇑(u i)) :
    ∃ Φ : NMIUMap (lp 𝒜 ∞) (lp ℬ ∞), Function.Bijective ⇑Φ ∧
      ∀ (x : lp 𝒜 ∞) (i : I₁),
        ((Φ x : lp ℬ ∞) : ∀ j, ℬ j) i = u i ((x : ∀ j, 𝒜 j) (e i)) := by
  classical
  obtain ⟨Φ, hΦ, -⟩ := vn_products_nmiu (B := lp 𝒜 ∞) ℬ
    (fun i => nmiuComp (u i) (lpEvalNMIU 𝒜 (e i)))
  have hΦapp : ∀ (x : lp 𝒜 ∞) (i : I₁),
      ((Φ x : lp ℬ ∞) : ∀ j, ℬ j) i = u i ((x : ∀ j, 𝒜 j) (e i)) := fun x i => hΦ i x
  -- the inverse maps
  set v : ∀ i : I₁, NMIUMap (ℬ i) (𝒜 (e i)) := fun i => nmiuSymm (u i) (hu i) with hv
  have hvu : ∀ (i : I₁) (b : ℬ i), u i (v i b) = b := fun i b =>
    nmiuSymm_apply_apply' (u i) (hu i) b
  have hvnorm : ∀ (i : I₁) (b : ℬ i), ‖v i b‖ = ‖b‖ := by
    intro i b
    have h := NonUnitalStarAlgHom.norm_map (u i).toStarAlgHom (hu i).1 (v i b)
    rw [show ((u i).toStarAlgHom (v i b) : ℬ i) = b from hvu i b] at h
    exact h.symm
  refine ⟨Φ, ⟨?_, ?_⟩, hΦapp⟩
  · intro x y hxy
    refine lp.ext (funext fun j => ?_)
    obtain ⟨i, rfl⟩ := e.surjective j
    refine (hu i).1 ?_
    rw [← hΦapp x i, ← hΦapp y i, hxy]
  · intro z
    have hmem : Memℓp ((Equiv.piCongrLeft 𝒜 e)
        (fun i : I₁ => v i ((z : ∀ j, ℬ j) i))) ∞ := by
      refine memℓp_infty_iff.mpr ⟨‖z‖, ?_⟩
      rintro _ ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective j
      show ‖(Equiv.piCongrLeft 𝒜 e)
        (fun i : I₁ => v i ((z : ∀ j, ℬ j) i)) (e i)‖ ≤ ‖z‖
      rw [Equiv.piCongrLeft_apply_apply, hvnorm]
      exact lp.norm_apply_le_norm (by simp) z i
    refine ⟨⟨_, hmem⟩, ?_⟩
    refine lp.ext (funext fun i => ?_)
    rw [hΦapp]
    show u i ((Equiv.piCongrLeft 𝒜 e)
      (fun i' : I₁ => v i' ((z : ∀ j, ℬ j) i')) (e i)) = _
    rw [Equiv.piCongrLeft_apply_apply, hvu]

/-! #### The solution set of 125bII -/

/-- A matrix algebra `M_{n+1}`, spelled exactly as in `HereditarilyAtomic`
(**84bII**) so that the two match on the nose. -/
private abbrev HaMat (n : ℕ) : Type :=
  CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ

/-- The index of the solution set of **125bII**: a hereditarily atomic von
Neumann algebra *presented* as `⊕_{j ∈ J} M_{N j+1}` with `J` a subset of a
fixed index type `K`, together with an ncpsu-map into it from `𝒜`.  (124III
instead carries a von Neumann subalgebra of `B(ℓ²(T))`; the presentation is
what makes the flat product below manifestly hereditarily atomic.) -/
private structure HaSolIdx (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (K : Type u) : Type u where
  J : Set K
  N : J → ℕ
  γ : NCPSUMap A (lp (fun j : J => HaMat (N j)) ∞)

/-- The algebra of a solution-set entry. -/
@[reducible] private def HaSolAlg {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {K : Type u} (i : HaSolIdx A K) :
    Type u :=
  lp (fun j : i.J => HaMat (i.N j)) ∞

/-- The *flat* index of the product over the solution set: a pair of a
solution-set entry and one of its summands. -/
@[reducible] private def HaSolFlat (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) : Type u :=
  Σ i : HaSolIdx A K, i.J

/-- The product `∏ᵢ 𝒞ᵢ` over the solution set, formed flat — a single direct
sum of matrix algebras. -/
@[reducible] private def haSolProd (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) : Type u :=
  lp (fun p : HaSolFlat A K => HaMat (p.1.N p.2)) ∞

/-- Whence proc.tex:5257's "a direct sum of hereditarily atomic algebras is
hereditarily atomic" is not needed: the product is hereditarily atomic *by
definition*. -/
private theorem hereditarilyAtomic_haSolProd (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) :
    HereditarilyAtomic (haSolProd A K) :=
  ⟨HaSolFlat A K, fun p => p.1.N p.2,
    ⟨StarAlgEquiv.refl (R := ℂ) (A := haSolProd A K)⟩⟩

/-- The **block projection** `⊕_{(i,j)} M_{N i j+1} → ⊕ⱼ M_{N i j+1}` onto
the summands belonging to a single solution-set entry: **47IV** applied to
the family of coordinate projections. -/
private theorem exists_haBlockProj (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] {K : Type u}
    (i : HaSolIdx A K) :
    ∃ pr : NMIUMap (haSolProd A K) (HaSolAlg i),
      ∀ (x : haSolProd A K) (j : i.J),
        ((pr x : HaSolAlg i) : ∀ j' : i.J, HaMat (i.N j')) j
          = (x : ∀ q : HaSolFlat A K, HaMat (q.1.N q.2)) ⟨i, j⟩ := by
  obtain ⟨g, hg, -⟩ := vn_products_nmiu (B := haSolProd A K)
    (fun j : i.J => HaMat (i.N j))
    (fun j => lpEvalNMIU (fun q : HaSolFlat A K => HaMat (q.1.N q.2)) ⟨i, j⟩)
  exact ⟨g, fun x j => hg j x⟩

/-- A hereditarily atomic von Neumann algebra no larger than `K` is
`⊕_{j ∈ J} M_{N j+1}` for a *subset* `J ⊆ K`.  This is the relabelling step
of 124III, one exponential cheaper: the summand index type `I₀` injects into
the algebra by `i ↦ κᵢ(1)`, so it injects into `K`, and `exists_lp_reindex`
moves the direct sum along that injection. -/
private theorem exists_haPresentation {K : Type u} (W : Type u)
    [CStarAlgebra W] [PartialOrder W] [StarOrderedRing W]
    [VonNeumannAlgebra W] (hW : HereditarilyAtomic W) (hK : #W ≤ #K) :
    ∃ (J : Set K) (N : J → ℕ)
      (Θ : NMIUMap W (lp (fun j : J => HaMat (N j)) ∞)),
      Function.Bijective ⇑Θ := by
  classical
  obtain ⟨I₀, N₀, ⟨Ψ⟩⟩ := hW
  have hinj : Function.Injective
      (fun i : I₀ => Ψ.symm (lpKappa i (1 : HaMat (N₀ i)))) := by
    intro i i' hii'
    by_contra hne
    have h1 : lpKappa i (1 : HaMat (N₀ i)) = lpKappa i' (1 : HaMat (N₀ i')) :=
      Ψ.symm.injective hii'
    have h2 := congrArg
      (fun x : lp (fun k : I₀ => HaMat (N₀ k)) ∞ =>
        (x : ∀ k : I₀, HaMat (N₀ k)) i) h1
    rw [lpKappa_apply_self, lpKappa_apply_ne _ _ hne] at h2
    exact one_ne_zero h2
  have hcardI : #I₀ ≤ #K :=
    le_trans (Cardinal.mk_le_of_injective hinj) hK
  obtain ⟨jm⟩ := (Cardinal.le_def _ _).mp hcardI
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : NMIUMap W (lp (fun i : I₀ => HaMat (N₀ i)) ∞),
      ∀ x : W, Ψ' x = Ψ x :=
    ⟨⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩, fun _ => rfl⟩
  obtain ⟨Φ, hΦbij, -⟩ := exists_lp_reindex
    (𝒜 := fun i : I₀ => HaMat (N₀ i))
    (ℬ := fun j : (Set.range ⇑jm : Set K) =>
      HaMat (N₀ ((Equiv.ofInjective ⇑jm jm.injective).symm j)))
    (Equiv.ofInjective ⇑jm jm.injective).symm
    (fun _ => nmiuId _) (fun _ => nmiuId_bijective)
  refine ⟨Set.range ⇑jm,
    fun j => N₀ ((Equiv.ofInjective ⇑jm jm.injective).symm j),
    nmiuComp Φ Ψ', ⟨fun x y hxy => ?_, fun z => ?_⟩⟩
  · have hx : Φ (Ψ' x) = Φ (Ψ' y) := hxy
    have := hΦbij.1 hx
    rw [hΨ' x, hΨ' y] at this
    exact Ψ.injective this
  · obtain ⟨w, hw⟩ := hΦbij.2 z
    refine ⟨Ψ.symm w, ?_⟩
    show Φ (Ψ' (Ψ.symm w)) = z
    rw [hΨ' (Ψ.symm w), Ψ.apply_symm_apply]
    exact hw

/-- **The solution set condition for 125bII** (proc.tex:5262): every
ncpsu-map from `𝒜` into a *hereditarily atomic* von Neumann algebra factors
as an nmiu-map after one of the `γᵢ`.  The algebra `ℬ' = W*(f(𝒜))` is
hereditarily atomic by **84bIII** and has at most `2^(2^(𝔠+#𝒜))` elements by
**124I**; `exists_haPresentation` then puts it on a subset of `K`. -/
private theorem ha_solution_set (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] {K : Type u}
    (hK : #K = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (Cardinal.continuum + #A)))
    {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [VonNeumannAlgebra B] (hB : HereditarilyAtomic B) (f : NCPSUMap A B) :
    ∃ (i : HaSolIdx A K) (h : NMIUMap (HaSolAlg i) B),
      ∀ a : A, h ((i.γ).toNCPMap a) = f.toNCPMap a := by
  classical
  have h2 : (2 : Cardinal.{u}) ≠ 0 := by norm_num
  set G : Set B := Set.range (fun a : A => f.toNCPMap a) with hG
  have hw := isVNSubalgebra_wstar (A := B) G
  obtain ⟨f', hf'⟩ := exists_ncpsuCorestrict (wstar B G) hw.1 f (fun a => hw.2 ⟨a, rfl⟩)
  have hgen : wstar (VNSub B (wstar B G) hw.1)
      (VNSub.val ⁻¹' G) = ⊤ := by
    refine vnsub_wstar_eq_top _ (isVNSubalgebra_wstar _).1 fun x hx => ?_
    exact (isVNSubalgebra_wstar (A := VNSub B (wstar B G) hw.1)
      (VNSub.val ⁻¹' G)).2 hx
  have hcardG : #((VNSub.val ⁻¹' G : Set (VNSub B (wstar B G) hw.1))) ≤ #A := by
    refine le_trans (Cardinal.mk_le_of_injective
      (f := fun x : (VNSub.val ⁻¹' G : Set (VNSub B (wstar B G) hw.1)) =>
        (⟨x.val.val, x.property⟩ : G)) ?_) ?_
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      exact Subtype.ext (VNSub.val_injective (congrArg Subtype.val h))
    · exact Cardinal.mk_range_le
  have hcard : #(VNSub B (wstar B G) hw.1) ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (Cardinal.continuum + #A) := by
    refine le_trans (vn_generation_bound _ hgen) ?_
    exact Cardinal.power_le_power_left h2 (Cardinal.power_le_power_left h2
      (add_le_add le_rfl hcardG))
  have hB' : HereditarilyAtomic (VNSub B (wstar B G) hw.1) :=
    hereditarilyAtomic_subalgebra hB VNSub.valNMIU VNSub.valNMIU_injective
  obtain ⟨J, N, Θ, hΘbij⟩ := exists_haPresentation (K := K)
    (VNSub B (wstar B G) hw.1) hB' (by rw [hK]; exact hcard)
  obtain ⟨γ, hγ⟩ : ∃ γ : NCPSUMap A (lp (fun j : J => HaMat (N j)) ∞),
      ∀ a : A, γ.toNCPMap a = Θ (f'.toNCPMap a) :=
    ⟨ncpsuCompNmiu Θ f', fun a => ncpsuCompNmiu_apply Θ f' a⟩
  refine ⟨⟨J, N, γ⟩, nmiuComp VNSub.valNMIU (nmiuSymm Θ hΘbij), fun a => ?_⟩
  show VNSub.valNMIU (nmiuSymm Θ hΘbij (γ.toNCPMap a)) = f.toNCPMap a
  rw [hγ a, nmiuSymm_apply_apply]
  exact hf' a

end HaSecondAdjunction


set_option maxHeartbeats 1000000 in
variable (A) in
/-- **125bII** (proc.tex:5240, Proposition): the inclusion
`haW*_miu → haW*_cpsu` has a left adjoint `F_ha`.

Freyd, exactly as in 124III `second_adjunction`: `F_ha(𝒜)` is the von
Neumann subalgebra of the product over the solution set generated by the
range of the mediating map `η`.  Existence of the factorisation is weak
initiality of the product (`ha_solution_set` followed by the block
projection); uniqueness is **47V** `vn_equalisers` together with
`vnsub_wstar_eq_top`.  Hereditary atomicity of the carrier is **84bIII**
applied to `hereditarilyAtomic_haSolProd`.

`hA` is not used; see the note above `section HaSecondAdjunction`. -/
theorem ha_second_adjunction [VonNeumannAlgebra A]
    (hA : HereditarilyAtomic A) : Nonempty (HaFreeMIU A) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : Type u, #K = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (Cardinal.continuum + #A)) := ⟨_, Cardinal.mk_out _⟩
  choose γ' hγ' using fun p : HaSolFlat A K =>
    exists_ncpsuCompNmiu' (lpEvalNMIU (fun j : p.1.J => HaMat (p.1.N j)) p.2) p.1.γ
  obtain ⟨η, hη, -⟩ := vn_products_ncpsu
    (fun p : HaSolFlat A K => HaMat (p.1.N p.2)) γ'
  have hw := isVNSubalgebra_wstar (A := haSolProd A K)
    (Set.range (fun a : A => η.toNCPMap a))
  obtain ⟨η', hη'⟩ :=
    exists_ncpsuCorestrict
      (wstar (haSolProd A K) (Set.range (fun a : A => η.toNCPMap a)))
      hw.1 η (fun a => hw.2 ⟨a, rfl⟩)
  refine ⟨{ carrier := VNSub (haSolProd A K)
              (wstar (haSolProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1
            ha := hereditarilyAtomic_subalgebra (hereditarilyAtomic_haSolProd A K)
              VNSub.valNMIU VNSub.valNMIU_injective
            unit := η'
            universal := fun B _ _ _ _ hB f => ?_ }⟩
  -- weak initiality: factor through the solution set, then block-project
  obtain ⟨i, h, hh⟩ := ha_solution_set A hK hB f
  obtain ⟨pr, hpr⟩ := exists_haBlockProj A i
  obtain ⟨g, hgeq⟩ : ∃ g : NMIUMap (VNSub (haSolProd A K)
        (wstar (haSolProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1) B,
      ∀ x, g x = h (pr x.val) :=
    ⟨nmiuComp h (nmiuComp pr VNSub.valNMIU), fun _ => rfl⟩
  have hprη : ∀ a : A, pr (η.toNCPMap a) = (i.γ).toNCPMap a := by
    intro a
    refine lp.ext (funext fun j => ?_)
    rw [hpr, hη ⟨i, j⟩ a, hγ' ⟨i, j⟩ a]
    rfl
  have hgval : ∀ a : A, f.toNCPMap a = g (η'.toNCPMap a) := by
    intro a
    rw [hgeq (η'.toNCPMap a), hη' a, hprη a]
    exact (hh a).symm
  refine ⟨g, hgval, fun g' hg' => ?_⟩
  -- uniqueness: the equaliser (**47V**) is a von Neumann subalgebra
  -- containing the range of the unit, which generates the whole algebra
  obtain ⟨E, hE, hEset⟩ := vn_equalisers g' g
  have hEtop : E = ⊤ := by
    refine vnsub_wstar_eq_top E hE fun x hx => ?_
    obtain ⟨a, ha⟩ := hx
    have hx' : x = η'.toNCPMap a := VNSub.val_injective (by rw [hη' a]; exact ha.symm)
    have hgg : g' x = g x := by rw [hx', ← hg' a, ← hgval a]
    rw [← SetLike.mem_coe, hEset]
    exact hgg
  refine DFunLike.coe_injective (funext fun x => ?_)
  have hxE : x ∈ (E : Set (VNSub (haSolProd A K)
      (wstar (haSolProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1)) := by
    rw [hEtop]; trivial
  rw [hEset] at hxE
  exact hxE

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

/-! ### Machinery for 125cIII

The proof of `Fha_concrete` below needs five things that are not in the tree,
all of them stated across two universes (`F.carrier : Type u`, but
`MatAlg n : Type 0`, and the A/VN development of `wstar` and of ncp-map
composition fixes a single universe):

* `nmiu_ext_of_wstar_top` — two nmiu-maps agreeing on a generating set are
  equal.  This is **47V** `vn_equalisers` (whose proof is copied verbatim,
  the statement there being single-universe) plus minimality of `W*(G)`; it
  replaces every appeal in proc.tex:5300ff to the *uniqueness* half of the
  universal property of `η`, which cannot be used directly because the
  universal property quantifies over `Type u` and the matrix algebras are
  `Type 0`.
* `isVNSubalgebra_comap` — the preimage of a von Neumann subalgebra along a
  normal ∗-homomorphism is one.
* `exists_ncpsuCompNmiu'` — the universe-polymorphic form of
  `ncpsuCompNmiu` (the underlying `ncpComp` of `Measurement.lean` fixes one
  universe).
* `exists_lp_reindex` — a bijection of index sets together with
  nmiu-isomorphisms of the summands induces an nmiu-isomorphism of the
  direct sums.  The dependent-type bookkeeping is done by Mathlib's
  `Equiv.piCongrLeft`.
* `exists_lp_factor` — proc.tex:5300's Existence step: an nmiu-map onto a
  *factor* out of a direct sum factors through a single summand.  The thesis
  gets the summand from `∑ᵢ ϱ(cᵢ) = 1` and normality; here it comes for free
  from **69IV** `carrier_miu` (already universe-polymorphic), whose carrier
  is a central projection of `⊕ᵢ𝒜ᵢ`, hence has a coordinate equal to `1`.
  Injectivity of the resulting `ρ'` is Mathlib's `IsSimpleRing` for matrix
  rings rather than the thesis's `nmiu-factors`. -/

section FhaAux

universe u₁ u₂ u₃ u₄

/-! ### helper 1: central idempotents of a matrix algebra -/

private theorem matAlg_central_idem {n : ℕ} {x : MatAlg n}
    (hx : x * x = x) (hcen : ∀ y, x * y = y * x) : x = 0 ∨ x = 1 := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with he | hne
  · left
    have : Subsingleton (MatAlg n) := by
      constructor
      intro a b
      funext i
      exact he.elim i
    exact Subsingleton.elim _ _
  · set X : Matrix (Fin n) (Fin n) ℂ := CStarMatrix.ofMatrixStarAlgEquiv.symm x with hX
    have hXcen : ∀ y : Matrix (Fin n) (Fin n) ℂ, X * y = y * X := by
      intro y
      have h := hcen (CStarMatrix.ofMatrixStarAlgEquiv y)
      have h1 := congrArg CStarMatrix.ofMatrixStarAlgEquiv.symm h
      rw [map_mul, map_mul] at h1
      simpa [hX] using h1
    have hXX : X * X = X := by
      have h1 := congrArg CStarMatrix.ofMatrixStarAlgEquiv.symm hx
      rw [map_mul] at h1
      simpa [hX] using h1
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
      (M := X) (fun i j _ => (hXcen (Matrix.single i j 1)).symm)
    have hcc : (Matrix.scalar (Fin n)) (c * c) = (Matrix.scalar (Fin n)) c := by
      rw [map_mul, hc, hXX]
    have hc2 : c * c = c := by
      obtain ⟨i⟩ := hne
      have h4 := congrFun (congrFun hcc i) i
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h4
    have : c = 0 ∨ c = 1 := by
      rcases eq_or_ne c 0 with h | h
      · exact Or.inl h
      · right
        field_simp at hc2
        exact hc2
    rcases this with h | h
    · left
      have : X = 0 := by rw [← hc, h, map_zero]
      rw [hX] at this
      have := congrArg CStarMatrix.ofMatrixStarAlgEquiv this
      simpa using this
    · right
      have : X = 1 := by rw [← hc, h, map_one]
      rw [hX] at this
      have := congrArg CStarMatrix.ofMatrixStarAlgEquiv this
      simpa using this

/-! ### helper 2: a unital ∗-hom out of a matrix algebra is injective -/

private theorem matAlg_starAlgHom_injective {n : ℕ} {M : Type u₂} [CStarAlgebra M]
    [Nontrivial M] (φ : MatAlg (n + 1) →⋆ₐ[ℂ] M) : Function.Injective ⇑φ := by
  set e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ≃⋆ₐ[ℂ] MatAlg (n + 1) :=
    CStarMatrix.ofMatrixStarAlgEquiv with he
  have hsimple : Function.Injective
      ⇑(((φ : MatAlg (n + 1) →⋆ₐ[ℂ] M).comp (e : _ →⋆ₐ[ℂ] _)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →⋆ₐ[ℂ] M) := by
    exact RingHom.injective
      (((φ.comp (e : _ →⋆ₐ[ℂ] _)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →⋆ₐ[ℂ] M) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →+* M)
  intro x y hxy
  have h : φ (e (e.symm x)) = φ (e (e.symm y)) := by
    rw [e.apply_symm_apply, e.apply_symm_apply]; exact hxy
  have := hsimple h
  rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, this]




variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
  [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]

/-! ### helper 3: two nmiu-maps agreeing on a generating set are equal -/

private theorem nmiu_ext_of_wstar_top [VonNeumannAlgebra X] [VonNeumannAlgebra Y]
    (f g : NMIUMap X Y) (G : Set X) (hG : wstar X G = ⊤)
    (hfg : ∀ x ∈ G, f x = g x) (x : X) : f x = g x := by
  classical
  have hE : IsVNSubalgebra X (StarAlgHom.equalizer f.toStarAlgHom g.toStarAlgHom) := by
    constructor
    · have hfc : Continuous ⇑f.toStarAlgHom :=
        AddMonoidHomClass.continuous_of_bound f.toStarAlgHom 1 fun a => by
          simpa using Theses.A.CStar.norm_mi_map_contractive f.toStarAlgHom a
      have hgc : Continuous ⇑g.toStarAlgHom :=
        AddMonoidHomClass.continuous_of_bound g.toStarAlgHom 1 fun a => by
          simpa using Theses.A.CStar.norm_mi_map_contractive g.toStarAlgHom a
      exact isClosed_eq hfc hgc
    · intro D s hDsub hne hdir hlub
      have hf := f.preservesDirSups' D s hne hdir hlub
      have hg := g.preservesDirSups' D s hne hdir hlub
      have himg : (fun d : selfAdjoint X => (f.toStarAlgHom (d : X) : Y)) '' D
          = (fun d : selfAdjoint X => (g.toStarAlgHom (d : X) : Y)) '' D := by
        ext y
        constructor
        · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, (hDsub d hd).symm⟩
        · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, hDsub d hd⟩
      rw [himg] at hf
      exact hf.unique hg
  have hle : wstar X G ≤ StarAlgHom.equalizer f.toStarAlgHom g.toStarAlgHom :=
    sInf_le ⟨hE, fun y hy => hfg y hy⟩
  rw [hG, top_le_iff] at hle
  have : x ∈ StarAlgHom.equalizer f.toStarAlgHom g.toStarAlgHom := by
    rw [hle]; trivial
  exact this

/-! ### helper 6: the preimage of a von Neumann subalgebra -/

private theorem isVNSubalgebra_comap [VonNeumannAlgebra X] [VonNeumannAlgebra Y]
    (θ : X →⋆ₐ[ℂ] Y) (hθ : PreservesDirSups ⇑θ) (S : StarSubalgebra ℂ Y)
    (hS : IsVNSubalgebra Y S) : IsVNSubalgebra X (S.comap θ) := by
  have hsa : ∀ d : selfAdjoint X, IsSelfAdjoint (θ (d : X)) := by
    intro d
    show star (θ (d : X)) = θ (d : X)
    rw [← map_star, d.2.star_eq]
  constructor
  · have hc : Continuous ⇑θ :=
      AddMonoidHomClass.continuous_of_bound θ 1 fun a => by
        simpa using Theses.A.CStar.norm_mi_map_contractive θ a
    exact hS.isClosed.preimage hc
  · intro D s hDS hne hdir hlub
    set G : Set (selfAdjoint Y) :=
      (fun d : selfAdjoint X => (⟨θ (d : X), hsa d⟩ : selfAdjoint Y)) '' D with hG
    have hval : Subtype.val '' G = (fun d : selfAdjoint X => θ (d : X)) '' D := by
      rw [hG, ← Set.image_comp]; rfl
    have hlubG : IsLUB G (⟨θ (s : X), hsa s⟩ : selfAdjoint Y) := by
      refine isLUB_sa_of_isLUB ?_
      rw [hval]
      exact hθ D s hne hdir hlub
    have hGne : G.Nonempty := hne.image _
    have hGdir : DirectedOn (· ≤ ·) G := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
      exact ⟨_, ⟨c, hc, rfl⟩,
        Subtype.coe_le_coe.mp (starAlgHom_mono' θ (Subtype.coe_le_coe.mpr hac)),
        Subtype.coe_le_coe.mp (starAlgHom_mono' θ (Subtype.coe_le_coe.mpr hbc))⟩
    exact hS.dirSup_mem G _ (fun d hd => by
      obtain ⟨e, he, rfl⟩ := hd
      exact hDS e he) hGne hGdir hlubG

/-! ### helpers 4 and 5 have moved

`exists_ncpsuCompNmiu'` (composing an ncpsu-map with an nmiu-map across
universes), `lpEvalNMIU` and `exists_lp_reindex` (reindexing a direct sum
along a bijection of index sets) are stated above, before 125bII, whose
proof needs them too. -/



open Classical in
private theorem lpKappa_one_comm {I : Type u₁} {𝒜 : I → Type u₄} [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    (i : I) (x : lp 𝒜 ∞) :
    lpKappa i (1 : 𝒜 i) * x = x * lpKappa i (1 : 𝒜 i) := by
  apply lp.ext
  funext j
  rw [lp.infty_coeFn_mul, lp.infty_coeFn_mul]
  simp only [Pi.mul_apply, lpKappa, lp.coeFn_single]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

open Classical in
private theorem mul_lpKappa {I : Type u₁} {𝒜 : I → Type u₄} [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    (i : I) (z : lp 𝒜 ∞) (a : 𝒜 i) :
    z * lpKappa i a = lpKappa i ((z : ∀ j, 𝒜 j) i * a) := by
  apply lp.ext
  funext j
  rw [lp.infty_coeFn_mul]
  simp only [Pi.mul_apply, lpKappa, lp.coeFn_single]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-! ### helper 2': an nmiu-map onto a factor out of a direct sum of matrix
algebras factors through one summand -/

open Classical in
private theorem exists_lp_factor {I : Type u₁} {𝒜 : I → Type u₄} [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] {M : Type u₂}
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [VonNeumannAlgebra M]
    [Nontrivial M]
    (hfacM : ∀ x : M, x * x = x → (∀ y, x * y = y * x) → x = 0 ∨ x = 1)
    (hfacA : ∀ (i : I) (x : 𝒜 i), x * x = x → (∀ y, x * y = y * x) → x = 0 ∨ x = 1)
    (hinjA : ∀ (i : I) (φ : 𝒜 i →⋆ₐ[ℂ] M), Function.Injective ⇑φ)
    (ρ : NMIUMap (lp 𝒜 ∞) M) (hsurj : Function.Surjective ⇑ρ) :
    ∃ (i : I) (ρ' : NMIUMap (𝒜 i) M), Function.Bijective ⇑ρ' ∧
      ∀ x : lp 𝒜 ∞, ρ x = ρ' ((x : ∀ j, 𝒜 j) i) := by
  classical
  -- the carrier of `ρ`
  obtain ⟨hzcen, hzker⟩ :=
    carrier_miu ρ (nmiuP ρ) ρ.preservesDirSups' (fun _ => rfl)
  have hzproj : IsStarProjection (carrier (nmiuP ρ) ρ.preservesDirSups') :=
    (carrier_spec (nmiuP ρ) ρ.preservesDirSups').1
  set z : lp 𝒜 ∞ := carrier (nmiuP ρ) ρ.preservesDirSups'
  have hone : (ρ 1 : M) = 1 := map_one ρ.toStarAlgHom
  have hmulρ : ∀ a b : lp 𝒜 ∞, (ρ (a * b) : M) = ρ a * ρ b := fun a b =>
    map_mul ρ.toStarAlgHom a b
  have hsmulρ : ∀ (c : ℂ) (x : lp 𝒜 ∞), (ρ (c • x) : M) = c • ρ x := fun c x =>
    map_smul ρ.toStarAlgHom c x
  have hsmulρ : ∀ (c : ℂ) (x : lp 𝒜 ∞), (ρ (c • x) : M) = c • ρ x := fun c x =>
    map_smul ρ.toStarAlgHom c x
  -- `z ≠ 0`
  have hzne : z ≠ 0 := by
    intro h
    have h1 : (ρ 1 : M) = 0 := (hzker 1).mpr (by rw [h, zero_mul])
    rw [hone] at h1
    exact one_ne_zero h1
  -- some coordinate of `z` is nonzero
  obtain ⟨i, hzi⟩ : ∃ i : I, (z : ∀ j, 𝒜 j) i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hzne (lp.ext (funext fun j => by rw [hcon j]; rfl))
  -- that coordinate is a central idempotent, hence `1`
  have hzz : z * z = z := hzproj.isIdempotentElem.eq
  have hzii : (z : ∀ j, 𝒜 j) i * (z : ∀ j, 𝒜 j) i = (z : ∀ j, 𝒜 j) i := by
    have h := congrArg (fun w : lp 𝒜 ∞ => (w : ∀ j, 𝒜 j) i) hzz
    simpa [lp.infty_coeFn_mul] using h
  have hzicen : ∀ y : 𝒜 i, (z : ∀ j, 𝒜 j) i * y = y * (z : ∀ j, 𝒜 j) i := by
    intro y
    have h := hzcen (lpKappa i y)
    have h1 := congrArg (fun w : lp 𝒜 ∞ => (w : ∀ j, 𝒜 j) i) h
    simpa [lp.infty_coeFn_mul, lpKappa_apply_self] using h1
  have hzi1 : (z : ∀ j, 𝒜 j) i = 1 :=
    (hfacA i _ hzii hzicen).resolve_left hzi
  -- `ρ` is `1` on the unit of the `i`-th summand
  have hkne : (ρ (lpKappa i (1 : 𝒜 i)) : M) ≠ 0 := by
    intro h
    have h1 := (hzker _).mp h
    rw [mul_lpKappa, hzi1, mul_one] at h1
    have h2 := congrArg (fun w : lp 𝒜 ∞ => (w : ∀ j, 𝒜 j) i) h1
    rw [lpKappa_apply_self] at h2
    exact one_ne_zero (h2.trans rfl)
  have hkidem : (ρ (lpKappa i (1 : 𝒜 i)) : M) * ρ (lpKappa i (1 : 𝒜 i))
      = ρ (lpKappa i (1 : 𝒜 i)) := by
    rw [← hmulρ, lpKappa_mul, mul_one]
  have hkcen : ∀ y : M, (ρ (lpKappa i (1 : 𝒜 i)) : M) * y
      = y * ρ (lpKappa i (1 : 𝒜 i)) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [← hmulρ, ← hmulρ, lpKappa_one_comm]
  have hi : (ρ (lpKappa i (1 : 𝒜 i)) : M) = 1 :=
    (hfacM _ hkidem hkcen).resolve_left hkne
  -- the factoring ∗-homomorphism
  set ρ'₀ : 𝒜 i →⋆ₐ[ℂ] M :=
    { toFun := fun a => ρ (lpKappa i a)
      map_one' := hi
      map_mul' := fun a b => by
        rw [← lpKappa_mul]; exact hmulρ _ _
      map_zero' := by
        show (ρ (lp.single ∞ i (0 : 𝒜 i)) : M) = 0
        rw [lp.single_zero]; exact map_zero ρ.toStarAlgHom
      map_add' := fun a b => by
        show (ρ (lp.single ∞ i (a + b)) : M) = _
        rw [lp.single_add]; exact map_add ρ.toStarAlgHom _ _
      commutes' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        show (ρ (lp.single ∞ i (c • (1 : 𝒜 i))) : M) = _
        rw [lp.single_smul]
        show (ρ (c • lpKappa i (1 : 𝒜 i)) : M) = _
        rw [hsmulρ, hi]
        exact (Algebra.algebraMap_eq_smul_one c).symm
      map_star' := fun a => by
        rw [← lpKappa_star]; exact map_star ρ.toStarAlgHom _ }
  have hfac : ∀ x : lp 𝒜 ∞, (ρ x : M) = ρ'₀ ((x : ∀ j, 𝒜 j) i) := by
    intro x
    show (ρ x : M) = ρ (lpKappa i ((x : ∀ j, 𝒜 j) i))
    rw [← lpKappa_mul_left, hmulρ, hi, one_mul]
  have hsurj' : Function.Surjective ⇑ρ'₀ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨(x : ∀ j, 𝒜 j) i, (hfac x).symm⟩
  have hinj' : Function.Injective ⇑ρ'₀ := hinjA i ρ'₀
  exact ⟨i, ⟨ρ'₀, starAlgEquiv_preservesDirSups'
    (StarAlgEquiv.ofBijective ρ'₀ ⟨hinj', hsurj'⟩)⟩, ⟨hinj', hsurj'⟩, hfac⟩



/-! ### step B: the unit generates `F_ha(𝒜)` -/

private theorem wstar_unit_eq_top [VonNeumannAlgebra A] (F : HaFreeMIU A) :
    wstar F.carrier (Set.range ⇑F.unit.toNCPMap) = ⊤ := by
  classical
  have hSvn : IsVNSubalgebra F.carrier
      (wstar F.carrier (Set.range ⇑F.unit.toNCPMap)) :=
    (isVNSubalgebra_wstar (Set.range ⇑F.unit.toNCPMap)).1
  have hGS : Set.range ⇑F.unit.toNCPMap ⊆ wstar F.carrier (Set.range ⇑F.unit.toNCPMap) :=
    (isVNSubalgebra_wstar (Set.range ⇑F.unit.toNCPMap)).2
  have hha : HereditarilyAtomic
      (VNSub F.carrier (wstar F.carrier (Set.range ⇑F.unit.toNCPMap)) hSvn) :=
    hereditarilyAtomic_subalgebra F.ha VNSub.valNMIU VNSub.valNMIU_injective
  obtain ⟨g, hg⟩ : ∃ g : NCPSUMap A
      (VNSub F.carrier (wstar F.carrier (Set.range ⇑F.unit.toNCPMap)) hSvn),
      ∀ a : A, (g.toNCPMap a).val = F.unit.toNCPMap a :=
    exists_ncpsuCorestrict _ hSvn F.unit (fun a => hGS ⟨a, rfl⟩)
  obtain ⟨ϱ, hϱ, -⟩ := F.universal _ hha g
  obtain ⟨τ, -, huniq⟩ := F.universal F.carrier F.ha F.unit
  have h1 : nmiuComp VNSub.valNMIU ϱ = nmiuId F.carrier := by
    rw [huniq (nmiuComp VNSub.valNMIU ϱ) ?_, huniq (nmiuId F.carrier) (fun a => rfl)]
    intro a
    show F.unit.toNCPMap a = (ϱ (F.unit.toNCPMap a)).val
    rw [← hϱ a, hg a]
  refine eq_top_iff.mpr fun x _ => ?_
  have h2 : (ϱ x).val = x :=
    congrFun (congrArg (fun f : NMIUMap F.carrier F.carrier => ⇑f) h1) x
  exact h2 ▸ (ϱ x).property


end FhaAux

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
          Φ' (F.unit.toNCPMap a) i = (r i).toNCPMap a) → Φ' = Φ := by
  classical
  have htop : wstar F.carrier (Set.range ⇑F.unit.toNCPMap) = ⊤ := wstar_unit_eq_top F
  -- the mediating map `Φ` from the universal property
  obtain ⟨R, hR, -⟩ := vn_products_ncpsu (fun i : I => MatAlg (N i + 1)) r
  have hhaB : HereditarilyAtomic (lp (fun i : I => MatAlg (N i + 1)) ∞) :=
    ⟨I, N, ⟨StarAlgEquiv.refl (R := ℂ)
      (A := lp (fun i : I => MatAlg (N i + 1)) ∞)⟩⟩
  obtain ⟨Φ, hΦ, -⟩ := F.universal _ hhaB R
  have hΦr : ∀ (a : A) (i : I),
      ((Φ (F.unit.toNCPMap a) : lp (fun i : I => MatAlg (N i + 1)) ∞) :
        ∀ j : I, MatAlg (N j + 1)) i = (r i).toNCPMap a := by
    intro a i
    rw [← hΦ a]
    exact hR i a
  -- uniqueness, from `htop`
  have huniq : ∀ Φ' : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
      (∀ (a : A) (i : I), Φ' (F.unit.toNCPMap a) i = (r i).toNCPMap a) → Φ' = Φ := by
    intro Φ' hΦ'
    refine DFunLike.coe_injective (funext fun x => ?_)
    refine nmiu_ext_of_wstar_top Φ' Φ _ htop ?_ x
    rintro _ ⟨a, rfl⟩
    exact lp.ext (funext fun i => by rw [hΦ' a i, hΦr a i])
  refine ⟨Φ, ?_, hΦr, huniq⟩
  -- ## bijectivity
  obtain ⟨I', N', ⟨ψ₀⟩⟩ := F.ha
  set ψ : NMIUMap F.carrier (lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :=
    ⟨ψ₀.toStarAlgHom, starAlgEquiv_preservesDirSups' ψ₀⟩ with hψdef
  have hψbij : Function.Bijective ⇑ψ := ψ₀.bijective
  -- the maps `sᵢ' = πᵢ' ∘ ψ ∘ η`
  have hsex : ∀ i' : I', ∃ sm : NCPSUMap A (MatAlg (N' i' + 1)), ∀ a : A,
      sm.toNCPMap a =
        ((ψ (F.unit.toNCPMap a) : lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :
          ∀ j : I', MatAlg (N' j + 1)) i' := fun i' =>
    exists_ncpsuCompNmiu'
      (nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i') ψ) F.unit
  choose s hs using hsex
  -- each `sᵢ'` generates its matrix algebra
  have hsgen : ∀ i' : I', GeneratesMat (s i') := by
    intro i'
    set θ : F.carrier →⋆ₐ[ℂ] MatAlg (N' i' + 1) :=
      (nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i') ψ).toStarAlgHom
      with hθ
    have hθn : PreservesDirSups ⇑θ :=
      (nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i') ψ).preservesDirSups'
    have hcomap := isVNSubalgebra_comap θ hθn
      (wstar (MatAlg (N' i' + 1)) (Set.range ⇑(s i').toNCPMap))
      (isVNSubalgebra_wstar _).1
    have hle : wstar F.carrier (Set.range ⇑F.unit.toNCPMap) ≤
        (wstar (MatAlg (N' i' + 1)) (Set.range ⇑(s i').toNCPMap)).comap θ := by
      refine sInf_le ⟨hcomap, ?_⟩
      rintro _ ⟨a, rfl⟩
      show θ (F.unit.toNCPMap a) ∈ wstar (MatAlg (N' i' + 1)) (Set.range ⇑(s i').toNCPMap)
      have : θ (F.unit.toNCPMap a) = (s i').toNCPMap a := (hs i' a).symm
      rw [this]
      exact (isVNSubalgebra_wstar _).2 ⟨a, rfl⟩
    rw [htop, top_le_iff] at hle
    -- `θ` is surjective
    have hθsurj : Function.Surjective ⇑θ := by
      intro y
      obtain ⟨x, hx⟩ := hψbij.2 (lpKappa i' y)
      refine ⟨x, ?_⟩
      show ((ψ x : lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :
        ∀ j : I', MatAlg (N' j + 1)) i' = y
      rw [hx, lpKappa_apply_self]
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨x, rfl⟩ := hθsurj y
    have hx : x ∈ (wstar (MatAlg (N' i' + 1)) (Set.range ⇑(s i').toNCPMap)).comap θ := by
      rw [hle]; trivial
    exact hx
  -- `c : I' → I`
  have hcex : ∀ i' : I', ∃ i : I, MIUEquiv (r i) (s i') := fun i' =>
    hrep (N' i') (s i') (hsgen i')
  choose c hc using hcex
  -- `d : I → I'`, by the factoring lemma
  have hdex : ∀ i : I, ∃ i' : I', MIUEquiv (s i') (r i) := by
    intro i
    set ρ : NMIUMap F.carrier (MatAlg (N i + 1)) :=
      nmiuComp (lpEvalNMIU (fun j : I => MatAlg (N j + 1)) i) Φ with hρdef
    have hρη : ∀ a : A, ρ (F.unit.toNCPMap a) = (r i).toNCPMap a := fun a => hΦr a i
    have hρsurj : Function.Surjective ⇑ρ := by
      have hrange : wstar (MatAlg (N i + 1)) (Set.range ⇑(r i).toNCPMap) ≤
          ρ.toStarAlgHom.range :=
        sInf_le ⟨nmiu_image ρ, by
          rintro _ ⟨a, rfl⟩
          exact ⟨F.unit.toNCPMap a, hρη a⟩⟩
      rw [hgen i, top_le_iff] at hrange
      intro y
      have : y ∈ ρ.toStarAlgHom.range := by rw [hrange]; trivial
      exact this
    set rhoT : NMIUMap (lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) (MatAlg (N i + 1)) :=
      nmiuComp ρ (nmiuSymm ψ hψbij) with hrhoT
    have hrhoTsurj : Function.Surjective ⇑rhoT := fun y => by
      obtain ⟨x, hx⟩ := hρsurj y
      exact ⟨ψ x, by rw [show rhoT (ψ x) = ρ (nmiuSymm ψ hψbij (ψ x)) from rfl,
        nmiuSymm_apply_apply, hx]⟩
    obtain ⟨i', ρ', hρ'bij, hρ'fac⟩ :=
      exists_lp_factor (fun x hx hcen => matAlg_central_idem hx hcen)
        (fun _ x hx hcen => matAlg_central_idem hx hcen)
        (fun _ φ => matAlg_starAlgHom_injective φ) rhoT hrhoTsurj
    refine ⟨i', ρ', hρ'bij, fun a => ?_⟩
    rw [hs i' a, ← hρ'fac (ψ (F.unit.toNCPMap a))]
    show ρ (nmiuSymm ψ hψbij (ψ (F.unit.toNCPMap a))) = _
    rw [nmiuSymm_apply_apply, hρη a]
  choose d hd using hdex
  -- `c` and `d` are mutually inverse
  have htrans : ∀ {n₁ n₂ n₃ : ℕ} {f₁ : NCPSUMap A (MatAlg n₁)}
      {f₂ : NCPSUMap A (MatAlg n₂)} {f₃ : NCPSUMap A (MatAlg n₃)},
      MIUEquiv f₁ f₂ → MIUEquiv f₂ f₃ → MIUEquiv f₁ f₃ := by
    rintro n₁ n₂ n₃ f₁ f₂ f₃ ⟨φ₁, hb₁, he₁⟩ ⟨φ₂, hb₂, he₂⟩
    exact ⟨nmiuComp φ₂ φ₁, hb₂.comp hb₁, fun a => by
      show φ₂ (φ₁ (f₁.toNCPMap a)) = _
      rw [he₁ a, he₂ a]⟩
  have hcd : ∀ i : I, c (d i) = i := by
    intro i
    by_contra hne
    exact hdistinct _ _ hne (htrans (hc (d i)) (hd i))
  -- uniqueness of the `s`-representatives
  have hsuniq : ∀ i₁ i₂ : I', MIUEquiv (s i₁) (s i₂) → i₁ = i₂ := by
    rintro i₁ i₂ ⟨φ, hφbij, hφ⟩
    by_contra hne
    have hagree : ∀ x : F.carrier,
        nmiuComp φ (nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i₁) ψ) x
          = nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i₂) ψ x := by
      refine nmiu_ext_of_wstar_top _ _ _ htop ?_
      rintro _ ⟨a, rfl⟩
      show φ (((ψ (F.unit.toNCPMap a) : lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :
        ∀ j : I', MatAlg (N' j + 1)) i₁) = _
      rw [← hs i₁ a, hφ a, hs i₂ a]
      rfl
    obtain ⟨x, hx⟩ := hψbij.2 (lpKappa i₁ (1 : MatAlg (N' i₁ + 1)))
    have h := hagree x
    show False
    rw [show nmiuComp φ (nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i₁) ψ) x
      = φ (((ψ x : lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :
        ∀ j : I', MatAlg (N' j + 1)) i₁) from rfl,
      show nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i₂) ψ x
      = ((ψ x : lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :
        ∀ j : I', MatAlg (N' j + 1)) i₂ from rfl, hx,
      lpKappa_apply_self, lpKappa_apply_ne _ _ (Ne.symm hne),
      show (φ 1 : MatAlg (N' i₂ + 1)) = 1 from map_one φ.toStarAlgHom] at h
    exact one_ne_zero h
  have hdc : ∀ i' : I', d (c i') = i' := fun i' =>
    hsuniq _ _ (htrans (hd (c i')) (hc i'))
  -- the reindexing isomorphism
  set e : I ≃ I' := ⟨d, c, hcd, hdc⟩ with he
  obtain ⟨Θ, hΘbij, hΘ⟩ :=
    exists_lp_reindex (𝒜 := fun i' : I' => MatAlg (N' i' + 1))
      (ℬ := fun i : I => MatAlg (N i + 1)) e
      (fun i => (hd i).choose) (fun i => (hd i).choose_spec.1)
  have hΦeq : Φ = nmiuComp Θ ψ := by
    refine (huniq (nmiuComp Θ ψ) ?_).symm
    intro a i
    show ((Θ (ψ (F.unit.toNCPMap a)) : lp (fun i : I => MatAlg (N i + 1)) ∞) :
      ∀ j : I, MatAlg (N j + 1)) i = _
    rw [hΘ]
    show (hd i).choose (((ψ (F.unit.toNCPMap a) :
      lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) : ∀ j : I', MatAlg (N' j + 1)) (d i)) = _
    rw [← hs (d i) a]
    exact (hd i).choose_spec.2 a
  rw [hΦeq]
  exact hΘbij.comp hψbij


/-! ## The hereditarily atomic slice device

Session 84's core.  For **hereditarily atomic** `𝒜 ≅ ⊕_{j∈J} M_{n_j+1}`
(**84bII**) and *any* von Neumann algebra `𝒞`, every `x ∈ 𝒞 ⊗ 𝒜` has, in
each block `j`, a **finite** matrix of entries `c^j_{kl} ∈ 𝒞`:

> `(1 ⊗ z_j)·x  =  ∑_{k,l} (c^j_{kl} ⊗ 1)·(1 ⊗ u^j_{kl})`.

This is the elementary substitute, available only in the hereditarily
atomic case, for Tomiyama's slice-map property — which in general is
equivalent to the commutation theorem `(M ⊗̄ N)' = M' ⊗̄ N'` and hence out
of reach here (PROVING-LOG, session 83).

The entry extraction stays inside `Type u`: it never slices into `ℂ`.
`haE j k l x := (id ⊗ κ_j)((1⊗u^j_{0k})·x·(1⊗u^j_{l0}))`, where `κ_j` is
the ncp-map `a ↦ ω_j(a)·1` of the np-functional `ω_j(a) = (a_j)_{00}`, and
`haE j k l` lands in the range of the nmiu-map `c ↦ c ⊗ 1` (`nmiuTmulLeft`),
which is a von Neumann subalgebra by **69IVb** `nmiu_image` and hence
ultraweakly closed by **75VIII** `vnsac`.  Agreement on elementary tensors
plus `tensor_linear_ext` (108II(1)) does the rest.

`npScalarP`/`npScalar` fill the one API gap the survey predicted: the tree
had no `NPFunctional → NCPMap`.  Complete positivity is **34IX**
`cp_commutative_cod`/`cp_commutative_dom` through `ℂ`, normality is
**44XV** `p_uwcont`. -/

section HaSlice

set_option synthInstance.maxHeartbeats 400000

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C]

/-- `x ↦ u * x * v` is ultraweakly continuous. -/
private theorem continuous_uw_mulmul {X : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [VonNeumannAlgebra X] (u v : X) :
    @Continuous X X (ultraweak X) (ultraweak X) (fun x => u * x * v) :=
  continuous_ultraweak_of_forall _ fun ω => continuous_ultraweak_conj ω u v

/-- `z ↦ z·1` is monotone on the complex order. -/
private theorem algebraMap_complex_mono {z w : ℂ} (h : z ≤ w) :
    algebraMap ℂ A z ≤ algebraMap ℂ A w := by
  have h0 : (0:ℂ) ≤ w - z := sub_nonneg.mpr h
  obtain ⟨hre, him⟩ := Complex.le_def.mp h0
  have hd : w - z = (((w - z).re : ℝ) : ℂ) := by
    refine Complex.ext (by simp) ?_
    simp only [Complex.ofReal_im]
    simpa using him.symm
  rw [← sub_nonneg, ← map_sub, hd]
  exact Theses.A.CStar.algebraMap_ofReal_nonneg (by simpa using hre)

/-- The scalar map `a ↦ ω(a)·1` as a positive linear map. -/
private def npScalarP (ω : NPFunctional A) : A →ₚ[ℂ] A where
  toFun a := algebraMap ℂ A (ω a)
  map_add' x y := by
    show algebraMap ℂ A (ω (x + y)) = _
    rw [npFunctional_add, map_add]
  map_smul' r x := by
    show algebraMap ℂ A (ω (r • x)) = _
    rw [show (ω (r • x) : ℂ) = r * ω x from ω.toPositiveLinearMap.map_smul r x,
      map_mul, ← Algebra.smul_def]
    rfl
  monotone' x y h :=
    algebraMap_complex_mono (ω.toPositiveLinearMap.monotone h)

@[simp] private theorem npScalarP_apply (ω : NPFunctional A) (a : A) :
    npScalarP ω a = algebraMap ℂ A (ω a) := rfl

private theorem npScalarP_cp (ω : NPFunctional A) :
    Theses.A.CStar.IsCompletelyPositiveMap
      ((npScalarP ω : A →ₚ[ℂ] A) : A →ₗ[ℂ] A) := by
  have h1 : Theses.A.CStar.IsCompletelyPositiveMap (npLin ω) :=
    Theses.A.CStar.cp_commutative_cod (npLin ω)
      (fun a ha => npFunctional_nonneg ω ha)
  have h2 : Theses.A.CStar.IsCompletelyPositiveMap (Algebra.linearMap ℂ A) :=
    Theses.A.CStar.cp_of_mi (Algebra.linearMap ℂ A)
      (fun x y => by
        show algebraMap ℂ A (x * y) = algebraMap ℂ A x * algebraMap ℂ A y
        rw [map_mul])
      (fun x => by
        show algebraMap ℂ A (star x) = star (algebraMap ℂ A x)
        rw [algebraMap_star_comm])
  have h3 := Theses.A.CStar.cp_comp (npLin ω) (Algebra.linearMap ℂ A) h1 h2
  exact h3

private theorem npScalarP_normal (ω : NPFunctional A) :
    PreservesDirSups ⇑(npScalarP (A := A) ω) := by
  letI : TopologicalSpace A := ultraweak A
  refine ((p_uwcont (npScalarP ω)).out 0 2).mp ?_
  refine continuous_ultraweak_of_forall _ fun ν => ?_
  have heq : (fun a : A => (ν (npScalarP ω a) : ℂ))
      = fun a : A => (ν 1 : ℂ) * (ω a : ℂ) := by
    funext a
    show (ν (algebraMap ℂ A (ω a)) : ℂ) = _
    rw [Algebra.algebraMap_eq_smul_one,
      show (ν ((ω a : ℂ) • (1:A)) : ℂ) = (ω a : ℂ) * ν 1 from
        ν.toPositiveLinearMap.map_smul _ _]
    ring
  rw [heq]
  exact continuous_const.mul (continuous_ultraweak_npFunctional ω)

/-- The scalar map as an ncp-map. -/
private def npScalar (ω : NPFunctional A) : NCPMap A A where
  toCompletelyPositiveMap :=
    { toLinearMap := (npScalarP ω : A →ₗ[ℂ] A)
      map_cstarMatrix_nonneg' :=
        (Theses.A.CStar.cp_iff ((npScalarP ω : A →ₚ[ℂ] A) : A →ₗ[ℂ] A)).out 0 1
          |>.mp (npScalarP_cp ω) }
  preservesDirSups' := npScalarP_normal ω

@[simp] private theorem npScalar_apply (ω : NPFunctional A) (a : A) :
    npScalar ω a = algebraMap ℂ A (ω a) := rfl


/-! ## Matrix units -/


variable {m : ℕ}

/-- `M_m(ℂ)` as `CStarMatrix`, transported from `Matrix`. -/
private def matE : Matrix (Fin m) (Fin m) ℂ ≃⋆ₐ[ℂ] MatAlg m :=
  CStarMatrix.ofMatrixStarAlgEquiv

private theorem matE_apply (M : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) :
    (matE M) p q = M p q := rfl

private theorem matE_symm_apply (M : MatAlg m) (p q : Fin m) :
    (matE.symm M : Matrix (Fin m) (Fin m) ℂ) p q = M p q := rfl

/-- The matrix unit `e_{kl}` of `M_m`. -/
private def matU (k l : Fin m) : MatAlg m := matE (Matrix.single k l 1)

private theorem matU_mul_mul (o k l : Fin m) (M : MatAlg m) :
    matU o k * M * matU l o = (M k l) • matU o o := by
  have h : matU o k * M * matU l o
      = matE (Matrix.single o k (1:ℂ) * matE.symm M * Matrix.single l o 1) := by
    rw [map_mul, map_mul]
    show matU o k * (matE (matE.symm M)) * matU l o = _
    rw [matE.apply_symm_apply]
    rfl
  rw [h, Matrix.single_mul_mul_single, one_mul, mul_one,
    show (matE.symm M : Matrix (Fin m) (Fin m) ℂ) k l = M k l from rfl,
    matU, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem sum_matU_diag : ∑ p : Fin m, matU p p = (1 : MatAlg m) := by
  rw [show ∑ p : Fin m, matU p p
      = matE (∑ p : Fin m, Matrix.single p p (1:ℂ)) from (map_sum matE _ _).symm,
    show ∑ p : Fin m, Matrix.single p p (1:ℂ) = 1 from ?_, map_one]
  conv_rhs => rw [Matrix.matrix_eq_sum_single (1 : Matrix (Fin m) (Fin m) ℂ)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq]
  · intro q _ hq
    rw [Matrix.one_apply_ne (Ne.symm hq), Matrix.single_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

private theorem matrix_eq_sum_matU (M : MatAlg m) :
    M = ∑ k : Fin m, ∑ l : Fin m, (M k l) • matU k l := by
  have h : ∀ k l : Fin m, (M k l) • matU k l = matE (Matrix.single k l (M k l)) := by
    intro k l
    rw [matU, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [h, ← map_sum]
  conv_lhs => rw [show M = matE (matE.symm M) from (matE.apply_symm_apply M).symm]
  exact congrArg matE (Matrix.matrix_eq_sum_single _)



/-! ## The hereditarily atomic decomposition -/


/-- The coprojection as an additive homomorphism (for `map_sum`). -/
private def lpKappaHom {I : Type u₁} (𝒜 : I → Type u₄) [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] (j : I) :
    𝒜 j →+ lp 𝒜 ∞ where
  toFun := lpKappa j
  map_zero' := lpKappa_zero j
  map_add' := lpKappa_add j

private theorem lpKappa_sum {I : Type u₁} {𝒜 : I → Type u₄} [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] (j : I) {ι : Type*}
    (F : Finset ι) (f : ι → 𝒜 j) :
    lpKappa j (∑ p ∈ F, f p) = ∑ p ∈ F, lpKappa j (f p) :=
  map_sum (lpKappaHom 𝒜 j) f F

private theorem lpKappa_mul_right' {I : Type u₁} {𝒜 : I → Type u₄} [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    (j : I) (m : 𝒜 j) (y : lp 𝒜 ∞) :
    lpKappa j m * y = lpKappa j (m * (y : ∀ i, 𝒜 i) j) := by
  calc lpKappa j m * y = lpKappa j (m * 1) * y := by rw [mul_one]
    _ = (lpKappa j m * lpKappa j 1) * y := by rw [lpKappa_mul]
    _ = lpKappa j m * (lpKappa j 1 * y) := mul_assoc _ _ _
    _ = lpKappa j m * lpKappa j ((y : ∀ i, 𝒜 i) j) := by rw [lpKappa_mul_left]
    _ = lpKappa j (m * (y : ∀ i, 𝒜 i) j) := lpKappa_mul _ _ _


variable {J : Type u} {nn : J → ℕ}
  (Φ : A ≃⋆ₐ[ℂ] lp (fun j : J => MatAlg (nn j + 1)) ∞)

/-- `Φ` as an nmiu-map. -/
private def haPhi : NMIUMap A (lp (fun j : J => MatAlg (nn j + 1)) ∞) :=
  ⟨Φ.toStarAlgHom, starAlgEquiv_preservesDirSups Φ⟩

/-- The `j`-th block of `a`. -/
private def haPi (j : J) : NMIUMap A (MatAlg (nn j + 1)) :=
  nmiuComp (lpEvalNMIU _ j) (haPhi Φ)

private theorem haPi_apply (j : J) (a : A) :
    haPi Φ j a = (Φ a : ∀ j : J, MatAlg (nn j + 1)) j := rfl

/-- The `(k,l)` entry of the `j`-th block. -/
private def haEnt (j : J) (a : A) (k l : Fin (nn j + 1)) : ℂ :=
  (haPi Φ j a : MatAlg (nn j + 1)) k l

/-- The matrix units of `𝒜`. -/
private def haU (j : J) (k l : Fin (nn j + 1)) : A := Φ.symm (lpKappa j (matU k l))

/-- The central projections of `𝒜`. -/
private def haZ (j : J) : A := Φ.symm (lpKappa j 1)

private theorem haU_mul_mul (j : J) (o k l : Fin (nn j + 1)) (a : A) :
    haU Φ j o k * a * haU Φ j l o = (haEnt Φ j a k l) • haU Φ j o o := by
  have ha : a = Φ.symm (Φ a) := (Φ.symm_apply_apply a).symm
  rw [haU, haU, haU]
  conv_lhs => rw [ha]
  rw [← map_mul, ← map_mul, lpKappa_mul_right', lpKappa_mul, matU_mul_mul,
    lpKappa_smul]
  exact map_smul Φ.symm.toStarAlgHom _ _

private theorem sum_haU_diag (j : J) : ∑ p : Fin (nn j + 1), haU Φ j p p = haZ Φ j := by
  rw [haZ, ← sum_matU_diag (m := nn j + 1), lpKappa_sum, map_sum]
  rfl

private theorem haZ_mul (j : J) (a : A) :
    haZ Φ j * a = ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
      (haEnt Φ j a k l) • haU Φ j k l := by
  have ha : a = Φ.symm (Φ a) := (Φ.symm_apply_apply a).symm
  rw [haZ]
  conv_lhs => rw [ha]
  rw [← map_mul, lpKappa_mul_left]
  conv_lhs => rw [show ((Φ a : ∀ j : J, MatAlg (nn j + 1)) j)
    = ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
      (haEnt Φ j a k l) • matU k l from matrix_eq_sum_matU _]
  rw [show lpKappa (𝒜 := fun j : J => MatAlg (nn j + 1)) j
      (∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
        (haEnt Φ j a k l) • matU (m := nn j + 1) k l)
      = ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
        lpKappa j ((haEnt Φ j a k l) • matU (m := nn j + 1) k l) from ?_, map_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [lpKappa_smul]
      exact map_smul Φ.symm.toStarAlgHom _ _
  · rw [lpKappa_sum]
    exact Finset.sum_congr rfl fun k _ => lpKappa_sum _ _ _



/-! ## The slice operators -/


/-- The identity np-functional on `ℂ`. -/
private def oneNP : NPFunctional ℂ where
  toPositiveLinearMap :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      monotone' := fun _ _ h => h }
  preservesDirSups' := by
    intro D s hne _ hlub
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mpr (hlub.1 hd)
    · intro u hu
      obtain ⟨d₀, hd₀⟩ := hne
      have h0 : (d₀ : ℂ) ≤ u := hu ⟨d₀, hd₀, rfl⟩
      have him : (d₀ : ℂ).im = 0 := Complex.conj_eq_iff_im.mp d₀.2
      have hui : u.im = 0 := by
        have := (Complex.le_def.mp h0).2
        rw [him] at this
        exact this.symm
      have husa : IsSelfAdjoint u := Complex.conj_eq_iff_im.mpr hui
      exact Subtype.coe_le_coe.mpr (hlub.2 (fun d hd => Subtype.coe_le_coe.mp
        (hu ⟨d, hd, rfl⟩) : ∀ d ∈ D, d ≤ (⟨u, husa⟩ : selfAdjoint ℂ)))

/-- The np-functional `a ↦ (a_j)_{00}`. -/
private def haOm (j : J) : NPFunctional A :=
  compNP (nmiuP (haPi Φ j)) (haPi Φ j).preservesDirSups'
    (matFormNP oneNP (matUnit (0 : Fin (nn j + 1))))

private theorem haOm_apply (j : J) (a : A) : (haOm Φ j a : ℂ) = haEnt Φ j a 0 0 := by
  show (matFormNP oneNP (matUnit (0 : Fin (nn j + 1))) (haPi Φ j a) : ℂ) = _
  rw [matFormNP_apply, matForm_matUnit]
  rfl

/-- The ncp-map `a ↦ (a_j)_{00}·1`. -/
private def haKappa (j : J) : NCPMap A A := npScalar (haOm Φ j)

private theorem haKappa_apply (j : J) (a : A) :
    haKappa Φ j a = algebraMap ℂ A (haEnt Φ j a 0 0) := by
  show algebraMap ℂ A (haOm Φ j a) = _
  rw [haOm_apply]

private theorem haKappa_haU (j : J) : haKappa Φ j (haU Φ j 0 0) = 1 := by
  rw [haKappa_apply]
  have hpi : haPi Φ j (haU Φ j (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)))
      = matU (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)) := by
    show ((Φ (Φ.symm (lpKappa j
        (matU (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)))))) :
      ∀ q : J, MatAlg (nn q + 1)) j = _
    rw [Φ.apply_symm_apply, lpKappa_apply_self]
  have h : haEnt Φ j (haU Φ j (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)))
      (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)) = 1 := by
    show (haPi Φ j (haU Φ j (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1))) :
      MatAlg (nn j + 1)) (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)) = 1
    rw [hpi]
    show (Matrix.single (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)) (1 : ℂ))
      (0 : Fin (nn j + 1)) (0 : Fin (nn j + 1)) = 1
    simp
  rw [h, map_one]




variable (C)

/-- The slice operator `x ↦ (id ⊗ κ_j)((1⊗u_{0k}) x (1⊗u_{l0}))`. -/
private def haE (j : J) (k l : Fin (nn j + 1)) (x : VNT C A) : VNT C A :=
  tmap (ncpId C) (haKappa Φ j)
    (((1 : C) ⊗ᵥ haU Φ j 0 k) * x * ((1 : C) ⊗ᵥ haU Φ j l 0))

variable {C}

private theorem vtmul_mul_vtmul (c c' : C) (a a' : A) :
    (c ⊗ᵥ a) * (c' ⊗ᵥ a') = (c * c') ⊗ᵥ (a * a') :=
  ((vnTensor C A).isTensorProduct.miu.2.1 c c' a a').symm

private theorem vtmul_smul_right (c : C) (r : ℂ) (a : A) :
    c ⊗ᵥ (r • a) = r • (c ⊗ᵥ a) :=
  map_smul ((vnTensor C A).map c) r a

private theorem haE_tmul (j : J) (k l : Fin (nn j + 1)) (c : C) (a : A) :
    haE C Φ j k l (c ⊗ᵥ a) = (haEnt Φ j a k l) • (c ⊗ᵥ (1 : A)) := by
  rw [haE, vtmul_mul_vtmul, vtmul_mul_vtmul, one_mul, mul_one,
    haU_mul_mul, vtmul_smul_right,
    show (tmap (ncpId C) (haKappa Φ j)) ((haEnt Φ j a k l) • (c ⊗ᵥ haU Φ j 0 0))
        = (haEnt Φ j a k l) • (tmap (ncpId C) (haKappa Φ j) (c ⊗ᵥ haU Φ j 0 0)) from
      map_smul (tmap (ncpId C) (haKappa Φ j)).toCompletelyPositiveMap.toLinearMap _ _,
    tmap_apply, ncpId_apply, haKappa_haU]

/-- `haE` as a linear map. -/
private def haEL (j : J) (k l : Fin (nn j + 1)) : VNT C A →ₗ[ℂ] VNT C A :=
  ((tmap (ncpId C) (haKappa Φ j)).toCompletelyPositiveMap.toLinearMap).comp
    (((LinearMap.mulRight ℂ ((1 : C) ⊗ᵥ haU Φ j l 0)).comp
      (LinearMap.mulLeft ℂ ((1 : C) ⊗ᵥ haU Φ j 0 k))))

private theorem haEL_apply (j : J) (k l : Fin (nn j + 1)) (x : VNT C A) :
    haEL Φ j k l x = haE C Φ j k l x := rfl

private theorem haEL_continuous (j : J) (k l : Fin (nn j + 1)) :
    @Continuous (VNT C A) (VNT C A) (ultraweak _) (ultraweak _) ⇑(haEL Φ j k l) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  have h1 : Continuous
      (fun x : VNT C A => ((1 : C) ⊗ᵥ haU Φ j 0 k) * x * ((1 : C) ⊗ᵥ haU Φ j l 0)) :=
    continuous_uw_mulmul _ _
  have h2 : Continuous ⇑(tmap (ncpId C) (haKappa Φ j)) :=
    ((p_uwcont (ncpPositive (tmap (ncpId C) (haKappa Φ j)))).out 2 0).mp
      (tmap (ncpId C) (haKappa Φ j)).preservesDirSups'
  exact h2.comp h1






private theorem haE_mem (j : J) (k l : Fin (nn j + 1)) (x : VNT C A) :
    ∃ c : C, haE C Φ j k l x = c ⊗ᵥ (1 : A) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  haveI : T2Space (VNT C A) := vn_positive_basic_1.1
  obtain ⟨hRvn⟩ : Nonempty (IsVNSubalgebra (VNT C A)
      (nmiuTmulLeft C A).toStarAlgHom.range) :=
    ⟨nmiu_image _⟩
  have hRcl : IsClosed
      ((nmiuTmulLeft C A).toStarAlgHom.range : Set (VNT C A)) :=
    (vnsac _ hRvn).2
  set W : Submodule ℂ (VNT C A) :=
    Submodule.comap (haEL Φ j k l)
      (Subalgebra.toSubmodule
        (nmiuTmulLeft C A).toStarAlgHom.range.toSubalgebra) with hW
  have hWcl : IsClosed (W : Set (VNT C A)) :=
    hRcl.preimage (haEL_continuous Φ j k l)
  have hspan : (Submodule.span ℂ
      {t : VNT C A | ∃ a b, t = (vnTensor C A).map a b} : Set (VNT C A))
      ⊆ (W : Set (VNT C A)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, a, rfl⟩
    have hmem : haE C Φ j k l (c ⊗ᵥ a) ∈
        (nmiuTmulLeft C A).toStarAlgHom.range := by
      rw [haE_tmul, ← vtmulLeft_smul]
      exact ⟨(haEnt Φ j a k l) • c, rfl⟩
    exact hmem
  have hx : x ∈ W := by
    have hd := (vnTensor C A).isTensorProduct.dense
    have hcl : x ∈ closure ((Submodule.span ℂ
        {t : VNT C A | ∃ a b, t = (vnTensor C A).map a b} : Set (VNT C A))) := by
      rw [hd.closure_eq]; trivial
    exact hWcl.closure_subset_iff.mpr hspan hcl
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

private theorem haSliceEq (j : J) (x : VNT C A) :
    ((1 : C) ⊗ᵥ haZ Φ j) * x
      = ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
          haE C Φ j k l x * ((1 : C) ⊗ᵥ haU Φ j k l) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  haveI : T2Space (VNT C A) := vn_positive_basic_1.1
  set f : VNT C A →ₗ[ℂ] VNT C A :=
    LinearMap.mulLeft ℂ ((1 : C) ⊗ᵥ haZ Φ j) with hf
  set g : VNT C A →ₗ[ℂ] VNT C A :=
    ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
      (LinearMap.mulRight ℂ ((1 : C) ⊗ᵥ haU Φ j k l)).comp (haEL Φ j k l) with hg
  have hgapp : ∀ y : VNT C A, g y
      = ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
          haE C Φ j k l y * ((1 : C) ⊗ᵥ haU Φ j k l) := by
    intro y
    rw [hg]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => LinearMap.sum_apply _ _ _
  have hcf : Continuous ⇑f := (mult_uws_cont ((1 : C) ⊗ᵥ haZ Φ j)).1
  have hcg : Continuous ⇑g := by
    have h : ⇑g = fun y : VNT C A => ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
        haE C Φ j k l y * ((1 : C) ⊗ᵥ haU Φ j k l) := funext hgapp
    rw [h]
    refine continuous_ultraweak_of_forall _ fun ν => ?_
    have hnu : (fun y : VNT C A => (ν (∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
          haE C Φ j k l y * ((1 : C) ⊗ᵥ haU Φ j k l)) : ℂ))
        = fun y : VNT C A => ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
            (ν (haE C Φ j k l y * ((1 : C) ⊗ᵥ haU Φ j k l)) : ℂ) := by
      funext y
      exact (map_sum ν.toPositiveLinearMap _ _).trans
        (Finset.sum_congr rfl fun k _ => map_sum ν.toPositiveLinearMap _ _)
    rw [hnu]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    have hc1 : Continuous (fun y : VNT C A =>
        (ν (1 * y * ((1 : C) ⊗ᵥ haU Φ j k l)) : ℂ)) :=
      continuous_ultraweak_conj ν 1 ((1 : C) ⊗ᵥ haU Φ j k l)
    simp only [one_mul] at hc1
    exact hc1.comp (haEL_continuous Φ j k l)
  have hfg : f = g := by
    refine tensor_linear_ext (vnTensor C A).isTensorProduct f g hcf hcg ?_
    intro c a
    show ((1 : C) ⊗ᵥ haZ Φ j) * (c ⊗ᵥ a) = g (c ⊗ᵥ a)
    rw [hgapp, vtmul_mul_vtmul, one_mul, haZ_mul]
    have hsum : c ⊗ᵥ (∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
          (haEnt Φ j a k l) • haU Φ j k l)
        = ∑ k : Fin (nn j + 1), ∑ l : Fin (nn j + 1),
            (haEnt Φ j a k l) • (c ⊗ᵥ haU Φ j k l) := by
      show (vnTensor C A).map c _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [map_sum]
        exact Finset.sum_congr rfl fun l _ => map_smul ((vnTensor C A).map c) _ _
    rw [hsum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [haE_tmul, smul_mul_assoc, vtmul_mul_vtmul, mul_one, one_mul]
  have := congrFun (congrArg (fun F : VNT C A →ₗ[ℂ] VNT C A => ⇑F) hfg) x
  rw [hgapp] at this
  exact this



/-! ## Parsec 1254 preliminaries: the approximation step and the ha
slice-map property

Session 85's continuation of the slice device.  `haApprox` is the
ultraweak approximation step (`∑_{j∈F} z_j ↑ 1`, **44VI**
`vna_supremum_uwlimit`, with `vnsac` supplying *ultraweak* closedness of a
von Neumann subalgebra — `IsVNSubalgebra` only carries norm closedness).
`haMem` and `haE_of_mem` are the two halves of the hereditarily atomic
slice-map property, and `haTensorPreimage`/`haTensorBSurj` are the private
ha forms of **125VIIb** `tensor_preimage` and **125eIII**
`tensorBsurjectivity`.  They do *not* close those two statements, which are
stated for arbitrary second factors and remain blocked on the commutation
theorem (PROVING-LOG, session 83). -/

/-- Monotonicity of the finite partial sums `∑_{j∈F} κⱼ(1)`. -/
private theorem lpSumSA_mono {I : Type*} {𝒜 : I → Type*} [∀ i, CStarAlgebra (𝒜 i)]
    [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    {F G : Finset I} (hFG : F ⊆ G) : lpSumSA (𝒜 := 𝒜) F ≤ lpSumSA G := by
  classical
  rw [← Subtype.coe_le_coe, lp_infty_le_iff]
  intro i
  rw [lpSumSA_apply, lpSumSA_apply]
  split <;> split
  · exact le_rfl
  · exact absurd (hFG ‹_›) ‹_›
  · exact zero_le_one
  · exact le_rfl

/-- A supremum of a nonempty set of self-adjoint elements taken in the
self-adjoint part is a supremum in the algebra. -/
private theorem isLUB_coe_of_isLUB' {X : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] {D : Set (selfAdjoint X)} {s : selfAdjoint X}
    (hne : D.Nonempty) (h : IsLUB D s) :
    IsLUB ((fun d : selfAdjoint X => (d : X)) '' D) (s : X) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · intro c hc
    obtain ⟨d, hd⟩ := hne
    have hdc : (d : X) ≤ c := hc ⟨d, hd, rfl⟩
    have hsa : IsSelfAdjoint c := by
      have h0 : (0 : X) ≤ c - d := sub_nonneg.mpr hdc
      simpa using h0.isSelfAdjoint.add d.2
    have hub : (⟨c, hsa⟩ : selfAdjoint X) ∈ upperBounds D := by
      intro e he
      exact Subtype.coe_le_coe.mp (hc ⟨e, he, rfl⟩)
    exact Subtype.coe_le_coe.mpr (h.2 hub)

/-- The finite partial sums `∑_{j∈F} z_j` of the central projections. -/
private def haZS (F : Finset J) : A := ∑ j ∈ F, haZ Φ j

private theorem haZS_eq (F : Finset J) :
    haZS Φ F = Φ.symm ((lpSumSA (𝒜 := fun j : J => MatAlg (nn j + 1)) F :
      selfAdjoint (lp (fun j : J => MatAlg (nn j + 1)) ∞)) :
      lp (fun j : J => MatAlg (nn j + 1)) ∞) := by
  classical
  show ∑ j ∈ F, Φ.symm (lpKappa j 1) = _
  rw [show ((lpSumSA (𝒜 := fun j : J => MatAlg (nn j + 1)) F :
      selfAdjoint (lp (fun j : J => MatAlg (nn j + 1)) ∞)) :
      lp (fun j : J => MatAlg (nn j + 1)) ∞)
      = ∑ j ∈ F, lpKappa j (1 : MatAlg (nn j + 1)) from rfl]
  exact (map_sum Φ.symm.toStarAlgHom _ _).symm

private theorem haZS_sa (F : Finset J) : IsSelfAdjoint (haZS Φ F) := by
  show star _ = _
  rw [haZS_eq]
  exact (map_star Φ.symm.toStarAlgHom _).symm.trans
    (congrArg ⇑Φ.symm.toStarAlgHom (lpSumSA F).2.star_eq)

private def haZSsa (F : Finset J) : selfAdjoint A := ⟨haZS Φ F, haZS_sa Φ F⟩

private theorem haZS_mono {F G : Finset J} (hFG : F ⊆ G) : haZS Φ F ≤ haZS Φ G := by
  rw [haZS_eq, haZS_eq]
  exact starAlgHom_mono' Φ.symm.toStarAlgHom
    (Subtype.coe_le_coe.mpr (lpSumSA_mono hFG))

private theorem haZS_isLUB : IsLUB (Set.range (fun F : Finset J => haZS Φ F)) (1 : A) := by
  have h1 : IsLUB ((fun d : selfAdjoint (lp (fun j : J => MatAlg (nn j + 1)) ∞) =>
      (d : lp (fun j : J => MatAlg (nn j + 1)) ∞)) ''
        Set.range (lpSumSA (𝒜 := fun j : J => MatAlg (nn j + 1))))
      ((⟨1, IsSelfAdjoint.one _⟩ :
        selfAdjoint (lp (fun j : J => MatAlg (nn j + 1)) ∞)) :
        lp (fun j : J => MatAlg (nn j + 1)) ∞) :=
    isLUB_coe_of_isLUB' ⟨_, ⟨∅, rfl⟩⟩ lpSumSA_isLUB
  have h2 := isLUB_image_of_orderIso ⇑Φ.symm (starAlgEquiv_le_iff Φ.symm)
    Φ.symm.surjective h1
  have himg : ⇑Φ.symm '' ((fun d : selfAdjoint (lp (fun j : J => MatAlg (nn j + 1)) ∞) =>
      (d : lp (fun j : J => MatAlg (nn j + 1)) ∞)) ''
        Set.range (lpSumSA (𝒜 := fun j : J => MatAlg (nn j + 1))))
      = Set.range (fun F : Finset J => haZS Φ F) := by
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨F, rfl⟩, rfl⟩, rfl⟩
      exact ⟨F, haZS_eq Φ F⟩
    · rintro ⟨F, rfl⟩
      exact ⟨_, ⟨_, ⟨F, rfl⟩, rfl⟩, (haZS_eq Φ F).symm⟩
  rw [himg] at h2
  rwa [show Φ.symm ((⟨1, IsSelfAdjoint.one _⟩ :
      selfAdjoint (lp (fun j : J => MatAlg (nn j + 1)) ∞)) :
      lp (fun j : J => MatAlg (nn j + 1)) ∞) = 1 from map_one Φ.symm.toStarAlgHom] at h2

/-- **The ultraweak approximation step**: `∑_{j∈F} z_j ↑ 1`, so `x` is the
ultraweak limit of `(1 ⊗ ∑_{j∈F} z_j)·x`; hence `x` lies in every
ultraweakly closed set containing all of those. -/
private theorem haApprox (x : VNT C A) (T : Set (VNT C A))
    (hT : @IsClosed (VNT C A) (ultraweak (VNT C A)) T)
    (hmem : ∀ F : Finset J, ((1 : C) ⊗ᵥ haZS Φ F) * x ∈ T) : x ∈ T := by
  classical
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  letI : TopologicalSpace A := ultraweak A
  set D : Set (selfAdjoint A) := Set.range (haZSsa Φ) with hD
  have hcoe : (fun d : selfAdjoint A => (d : A)) '' D
      = Set.range (fun F : Finset J => haZS Φ F) := by
    ext y
    constructor
    · rintro ⟨_, ⟨F, rfl⟩, rfl⟩; exact ⟨F, rfl⟩
    · rintro ⟨F, rfl⟩; exact ⟨haZSsa Φ F, ⟨F, rfl⟩, rfl⟩
  have hlubA : IsLUB ((fun d : selfAdjoint A => (d : A)) '' D) (1 : A) := by
    rw [hcoe]; exact haZS_isLUB Φ
  have hlub : IsLUB D (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint A) := by
    constructor
    · rintro _ ⟨F, rfl⟩
      exact Subtype.coe_le_coe.mp (hlubA.1 ⟨_, ⟨F, rfl⟩, rfl⟩)
    · intro u hu
      refine Subtype.coe_le_coe.mp (hlubA.2 ?_)
      rintro _ ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mpr (hu hd)
  have hh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := by
    refine ⟨⟨_, ⟨∅, rfl⟩⟩, ?_, ⟨_, hlub.1⟩⟩
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨haZSsa Φ (F ∪ G), ⟨F ∪ G, rfl⟩,
      Subtype.coe_le_coe.mp (haZS_mono Φ Finset.subset_union_left),
      Subtype.coe_le_coe.mp (haZS_mono Φ Finset.subset_union_right)⟩
  have hds : dirSup D hh = (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint A) :=
    (isLUB_dirSup D hh).unique hlub
  have hnet := vna_supremum_uwlimit D hh
  rw [hds] at hnet
  set ψ : Finset J → D := fun F => ⟨haZSsa Φ F, ⟨F, rfl⟩⟩ with hψ
  have hψmono : Monotone ψ := fun F G hFG =>
    Subtype.coe_le_coe.mpr (Subtype.coe_le_coe.mp (haZS_mono Φ hFG))
  have hψtend : Tendsto ψ atTop atTop :=
    tendsto_atTop_atTop_of_monotone hψmono (by
      rintro ⟨_, F, rfl⟩
      exact ⟨F, le_rfl⟩)
  have h1 : Tendsto (fun F : Finset J => haZS Φ F) atTop
      (@nhds A (ultraweak A) (1 : A)) := hnet.comp hψtend
  have hcont : @Continuous A (VNT C A) (ultraweak A) (ultraweak (VNT C A))
      (fun b : A => ((1 : C) ⊗ᵥ b) * x) :=
    ((mult_uws_cont x).2.1).comp (continuous_ultraweak_vtmul_right (1 : C))
  have h2 := (hcont.tendsto (1 : A)).comp h1
  have hone : ((1 : C) ⊗ᵥ (1 : A)) = 1 := (vnTensor C A).isTensorProduct.miu.1
  rw [show ((1 : C) ⊗ᵥ (1 : A)) * x = x by rw [hone, one_mul]] at h2
  exact hT.mem_of_tendsto h2 (Filter.Eventually.of_forall hmem)

/-! ### The two membership corollaries (the ha slice-map property) -/

private theorem vtmul_one_mem (S : StarSubalgebra ℂ C) (a : A) :
    ((1 : C) ⊗ᵥ a) ∈ tensorSub A S :=
  (isVNSubalgebra_wstar _).2 ⟨1, S.one_mem, a, rfl⟩

/-- **The ha slice-map property, containment half**: if every entry
`haE j k l x` of `x` lies in `𝒮 ⊗ 𝒜`, then `x` does. -/
private theorem haMem (S : StarSubalgebra ℂ C) (x : VNT C A)
    (h : ∀ (j : J) (k l : Fin (nn j + 1)), haE C Φ j k l x ∈ tensorSub A S) :
    x ∈ tensorSub A S := by
  classical
  have hcl : @IsClosed (VNT C A) (ultraweak (VNT C A))
      ((tensorSub A S : StarSubalgebra ℂ (VNT C A)) : Set (VNT C A)) :=
    (vnsac _ (isVNSubalgebra_wstar _).1).2
  have hmem := haApprox Φ x
    ((tensorSub A S : StarSubalgebra ℂ (VNT C A)) : Set (VNT C A)) hcl ?_
  · exact hmem
  intro F
  have hsplit : ((1 : C) ⊗ᵥ haZS Φ F) * x = ∑ j ∈ F, ((1 : C) ⊗ᵥ haZ Φ j) * x := by
    have hd : ((1 : C) ⊗ᵥ haZS Φ F) = ∑ j ∈ F, ((1 : C) ⊗ᵥ haZ Φ j) :=
      map_sum ((vnTensor C A).map 1) _ _
    rw [hd, Finset.sum_mul]
  rw [SetLike.mem_coe, hsplit]
  refine sum_mem fun j _ => ?_
  rw [haSliceEq Φ j x]
  exact sum_mem fun k _ => sum_mem fun l _ =>
    mul_mem (h j k l) (vtmul_one_mem S _)

private theorem tmapM_vtmul_one {C' : Type u} [CStarAlgebra C'] [PartialOrder C']
    [StarOrderedRing C'] [VonNeumannAlgebra C'] (ρ : NMIUMap C' C) (a : A) :
    tmapM ρ (nmiuId A) ((1 : C') ⊗ᵥ a) = (1 : C) ⊗ᵥ a := by
  rw [tmapM_apply, nmiuId_apply,
    show (ρ 1 : C) = 1 from map_one ρ.toStarAlgHom]

/-- Naturality of the slice operator in the first factor. -/
private theorem haE_natural {C' : Type u} [CStarAlgebra C'] [PartialOrder C']
    [StarOrderedRing C'] [VonNeumannAlgebra C'] (ρ : NMIUMap C' C)
    (j : J) (k l : Fin (nn j + 1)) (y : VNT C' A) :
    tmapM ρ (nmiuId A) (haE C' Φ j k l y) = haE C Φ j k l (tmapM ρ (nmiuId A) y) := by
  have hcomm : ncpComp (nmiuNCP (tmapM ρ (nmiuId A))) (tmap (ncpId C') (haKappa Φ j))
      = ncpComp (tmap (ncpId C) (haKappa Φ j)) (nmiuNCP (tmapM ρ (nmiuId A))) := by
    refine (exists_tmap (nmiuNCP ρ) (haKappa Φ j)).unique (fun a b => ?_) (fun a b => ?_)
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, tmapM_apply,
        nmiuId_apply]
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, tmapM_apply,
        nmiuId_apply]
  have hkey : ∀ z : VNT C' A, tmapM ρ (nmiuId A) (tmap (ncpId C') (haKappa Φ j) z)
      = tmap (ncpId C) (haKappa Φ j) (tmapM ρ (nmiuId A) z) := fun z => by
    have h := congrArg (fun f : NCPMap (VNT C' A) (VNT C A) => f z) hcomm
    simpa only [ncpComp_apply, nmiuNCP_apply] using h
  have hmul : ∀ z w : VNT C' A, tmapM ρ (nmiuId A) (z * w)
      = tmapM ρ (nmiuId A) z * tmapM ρ (nmiuId A) w :=
    fun z w => map_mul (tmapM ρ (nmiuId A)).toStarAlgHom z w
  show tmapM ρ (nmiuId A) (tmap (ncpId C') (haKappa Φ j) _) = _
  rw [hkey]
  show _ = tmap (ncpId C) (haKappa Φ j) _
  congr 1
  rw [hmul, hmul, tmapM_vtmul_one, tmapM_vtmul_one]

/-- **The ha slice-map property, extraction half** (the ha form of
125VIIb): the entries of an element of `𝒮 ⊗ 𝒜` lie in `𝒮`. -/
private theorem haE_of_mem (S : StarSubalgebra ℂ C) (hS : IsVNSubalgebra C S)
    (x : VNT C A) (hx : x ∈ tensorSub A S) (j : J) (k l : Fin (nn j + 1)) :
    ∃ c ∈ S, haE C Φ j k l x = c ⊗ᵥ (1 : A) := by
  have hrange : tensorSub A S ≤
      (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A)).toStarAlgHom.range := by
    refine sInf_le ⟨nmiu_image _, ?_⟩
    rintro _ ⟨s, hs, a, rfl⟩
    refine ⟨(⟨s, hs⟩ : VNSub C S hS) ⊗ᵥ a, ?_⟩
    show tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A)
      ((⟨s, hs⟩ : VNSub C S hS) ⊗ᵥ a) = s ⊗ᵥ a
    rw [tmapM_apply, nmiuId_apply]
    rfl
  obtain ⟨y, hy⟩ : x ∈
      (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A)).toStarAlgHom.range :=
    hrange hx
  have hy' : tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A) y = x := hy
  obtain ⟨c, hc⟩ := haE_mem (C := VNSub C S hS) Φ j k l y
  refine ⟨c.val, c.property, ?_⟩
  rw [← hy', ← haE_natural Φ (VNSub.valNMIU (A := C) (S := S) (hS := hS)) j k l y, hc,
    tmapM_apply, nmiuId_apply]
  rfl

/-! ### The ha forms of 125VIIb and 125eIII -/

variable [VonNeumannAlgebra D]

/-- `c ↦ c ⊗ 1` is injective when the second factor is nontrivial. -/
private theorem vtmul_one_injective [Nontrivial A] :
    Function.Injective (fun c : C => c ⊗ᵥ (1 : A)) := by
  intro c c' h
  have hsub : (c - c') ⊗ᵥ (1 : A) = c ⊗ᵥ (1 : A) - c' ⊗ᵥ (1 : A) :=
    map_sub ((vnTensor C A).map.flip (1 : A)) c c'
  have hz : (c - c') ⊗ᵥ (1 : A) = 0 := by
    rw [hsub, show (c ⊗ᵥ (1 : A)) = c' ⊗ᵥ (1 : A) from h, sub_self]
  have hn : ‖c - c'‖ * ‖(1 : A)‖ = 0 := by
    rw [← norm_vtmul, hz, norm_zero]
  rw [norm_one, mul_one, norm_eq_zero, sub_eq_zero] at hn
  exact hn

/-- A tensor product with a trivial factor is trivial. -/
private theorem vnt_subsingleton {Cc Aa : Type*} [CStarAlgebra Cc] [PartialOrder Cc]
    [StarOrderedRing Cc] [VonNeumannAlgebra Cc] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] [Subsingleton Aa] :
    Subsingleton (VNT Cc Aa) := by
  have h1 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 1 := (vnTensor Cc Aa).isTensorProduct.miu.1
  have h0 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 0 := by
    rw [show (1 : Aa) = 0 from Subsingleton.elim _ _]
    exact map_zero ((vnTensor Cc Aa).map 1)
  exact subsingleton_of_zero_eq_one (h1.symm.trans h0).symm

/-- **The ha form of 125VIIb** (`tensor-preimage`): for hereditarily atomic
`𝒜`, `(ρ ⊗ 𝒜)⁻¹(𝒮 ⊗ 𝒜) = ρ⁻¹(𝒮) ⊗ 𝒜`. -/
private theorem haTensorPreimage
    (Φ : A ≃⋆ₐ[ℂ] lp (fun j : J => MatAlg (nn j + 1)) ∞) (ρ : NMIUMap C D)
    (S : StarSubalgebra ℂ D) (hS : IsVNSubalgebra D S) (x : VNT C A) :
    tmapM ρ (nmiuId A) x ∈ tensorSub A S ↔
      x ∈ tensorSub A (S.comap ρ.toStarAlgHom) := by
  rcases subsingleton_or_nontrivial A with hss | hnt
  · haveI := hss
    haveI : Subsingleton (VNT C A) := vnt_subsingleton
    haveI : Subsingleton (VNT D A) := vnt_subsingleton
    constructor
    · intro _
      rw [Subsingleton.elim x 0]
      exact zero_mem _
    · intro _
      rw [Subsingleton.elim (tmapM ρ (nmiuId A) x) 0]
      exact zero_mem _
  haveI := hnt
  constructor
  · intro hx
    refine haMem Φ _ _ (fun j k l => ?_)
    obtain ⟨c', hc'⟩ := haE_mem (C := C) Φ j k l x
    obtain ⟨d, hd, hde⟩ := haE_of_mem Φ S hS _ hx j k l
    have hnat := haE_natural Φ ρ j k l x
    rw [hc', hde, tmapM_apply, nmiuId_apply] at hnat
    have hcd : ρ c' = d := vtmul_one_injective hnat
    rw [hc']
    refine (isVNSubalgebra_wstar _).2 ⟨c', ?_, 1, rfl⟩
    show ρ.toStarAlgHom c' ∈ S
    rw [show ρ.toStarAlgHom c' = d from hcd]
    exact hd
  · intro hx
    have hle : tensorSub A (S.comap ρ.toStarAlgHom) ≤
        (tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom := by
      refine sInf_le ⟨isVNSubalgebra_comap (tmapM ρ (nmiuId A)).toStarAlgHom
        (tmapM ρ (nmiuId A)).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
      rintro _ ⟨t, ht, a, rfl⟩
      show tmapM ρ (nmiuId A) (t ⊗ᵥ a) ∈ tensorSub A S
      rw [tmapM_apply, nmiuId_apply]
      exact (isVNSubalgebra_wstar _).2 ⟨ρ t, ht, a, rfl⟩
    exact hle hx

variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]

end HaSlice

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

/-! ### Infrastructure of parsec 1255, moved forward

`tmapM_range_le`, the functoriality of `tmapM` and the singleton direct sum
`punitSum` (the `Type 0`/`Type u` bridge) were all written for parsec 1255;
the proof of 125dII below needs the three of them, so they now live here.
Nothing else about them has changed. -/

section TmapMRange

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C] [VonNeumannAlgebra D]


/-- The range of `ρ ⊗ 𝒜` is contained in `ρ(𝒞) ⊗ 𝒜`. -/
private theorem tmapM_range_le (ρ : NMIUMap C D) (y : VNT C A) :
    tmapM ρ (nmiuId A) y ∈ tensorSub A ρ.toStarAlgHom.range := by
  have htop : wstar (VNT C A)
      {t : VNT C A | ∃ a b, t = (vnTensor C A).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor C A).isTensorProduct.dense
  have hle : wstar (VNT C A) {t : VNT C A | ∃ a b, t = (vnTensor C A).map a b} ≤
      (tensorSub A ρ.toStarAlgHom.range).comap (tmapM ρ (nmiuId A)).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM ρ (nmiuId A)).toStarAlgHom
      (tmapM ρ (nmiuId A)).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨c, a, rfl⟩
    show tmapM ρ (nmiuId A) (c ⊗ᵥ a) ∈ tensorSub A ρ.toStarAlgHom.range
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2 ⟨ρ c, ⟨c, rfl⟩, a, rfl⟩
  rw [htop, top_le_iff] at hle
  have hy : y ∈ (tensorSub A ρ.toStarAlgHom.range).comap
      (tmapM ρ (nmiuId A)).toStarAlgHom := by rw [hle]; trivial
  exact hy
end TmapMRange

section TmapMFunctoriality

universe u₁ u₂ u₃ u₄

variable {X₁ : Type u₁} {X₂ : Type u₂} {X₃ : Type u₃} {Y : Type u₄}
  [CStarAlgebra X₁] [PartialOrder X₁] [StarOrderedRing X₁] [VonNeumannAlgebra X₁]
  [CStarAlgebra X₂] [PartialOrder X₂] [StarOrderedRing X₂] [VonNeumannAlgebra X₂]
  [CStarAlgebra X₃] [PartialOrder X₃] [StarOrderedRing X₃] [VonNeumannAlgebra X₃]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]

/-! ### Functoriality of `tmapM` -/

private theorem tmapM_id (t : VNT X₁ Y) : tmapM (nmiuId X₁) (nmiuId Y) t = t := by
  have h : tmapM (nmiuId X₁) (nmiuId Y) = nmiuId (VNT X₁ Y) :=
    (exists_tmapM (nmiuId X₁) (nmiuId Y)).unique
      (fun a b => tmapM_apply _ _ a b) (fun a b => rfl)
  rw [h]
  rfl

private theorem tmapM_comp_id (ρ₁ : NMIUMap X₁ X₂) (ρ₂ : NMIUMap X₂ X₃) (t : VNT X₁ Y) :
    tmapM ρ₂ (nmiuId Y) (tmapM ρ₁ (nmiuId Y) t)
      = tmapM (nmiuComp ρ₂ ρ₁) (nmiuId Y) t := by
  have h : nmiuComp (tmapM ρ₂ (nmiuId Y)) (tmapM ρ₁ (nmiuId Y))
      = tmapM (nmiuComp ρ₂ ρ₁) (nmiuId Y) :=
    (exists_tmapM (nmiuComp ρ₂ ρ₁) (nmiuId Y)).unique
      (fun a b => by simp only [nmiuComp_apply, tmapM_apply, nmiuId_apply])
      (fun a b => tmapM_apply _ _ a b)
  exact congrArg (fun f : NMIUMap (VNT X₁ Y) (VNT X₃ Y) => f t) h

private theorem tmapM_injective {A₁ A₂ B₁ B₂ : Type u}
    [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁] [VonNeumannAlgebra A₁]
    [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂] [VonNeumannAlgebra A₂]
    [CStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁] [VonNeumannAlgebra B₁]
    [CStarAlgebra B₂] [PartialOrder B₂] [StarOrderedRing B₂] [VonNeumannAlgebra B₂]
    (f : NMIUMap A₁ A₂) (g : NMIUMap B₁ B₂) (hf : Function.Injective ⇑f)
    (hg : Function.Injective ⇑g) : Function.Injective ⇑(tmapM f g) :=
  tensor_injective f g hf hg (nmiuNCP (tmapM f g)) (fun a b => tmapM_apply f g a b)

/-! ### `(·) ⊗ ℬ`-surjectivity: congruence and transport along an isomorphism -/

/-! ### The singleton direct sum `M ≅ ⊕_{PUnit} M`

A device for the universe gap: `HaFreeExp.universal` quantifies over `Type u`
targets while `MatAlg n : Type 0`.  `punitSum n` is `M_n` presented as a
one-summand direct sum, which *is* in `Type u`, hereditarily atomic, and
nmiu-isomorphic to `M_n`. -/

private abbrev punitSum (n : ℕ) : Type u := lp (fun _ : PUnit.{u+1} => MatAlg (n + 1)) ∞

private def punitEval (n : ℕ) : NMIUMap (punitSum.{u} n) (MatAlg (n + 1)) :=
  lpEvalNMIU (fun _ : PUnit.{u+1} => MatAlg (n + 1)) PUnit.unit

private theorem punitEval_bijective (n : ℕ) :
    Function.Bijective ⇑(punitEval.{u} n) := by
  constructor
  · intro x y h
    refine lp.ext (funext fun p => ?_)
    cases p
    exact h
  · intro m
    exact ⟨lpKappa PUnit.unit m, lpKappa_apply_self _ _⟩

private def punitInv (n : ℕ) : NMIUMap (MatAlg (n + 1)) (punitSum.{u} n) :=
  nmiuSymm (punitEval.{u} n) (punitEval_bijective n)

private theorem punitEval_comp_inv (n : ℕ) :
    nmiuComp (punitEval.{u} n) (punitInv.{u} n) = nmiuId (MatAlg (n + 1)) :=
  DFunLike.coe_injective
    (funext fun m => nmiuSymm_apply_apply' (punitEval.{u} n) (punitEval_bijective n) m)

private theorem punitSum_ha (n : ℕ) : HereditarilyAtomic (punitSum.{u} n) :=
  ⟨PUnit.{u+1}, fun _ => n, ⟨StarAlgEquiv.refl ℂ (punitSum.{u} n)⟩⟩
end TmapMFunctoriality

/-! ## Parsec 1254 preliminaries: direct sums pass through `(·) ⊗ 𝒜`

125dII is Freyd once more (proc.tex:5541: "exactly as in
`tensor-closed-proof`, but with a suitably modified solution set"), and the
one ingredient of that proof which 125bII did not need is that `(·) ⊗ 𝒜`
*preserves the products of* `haW*_miu` — that is, that

> `(⊕ₚ 𝒞ₚ) ⊗ 𝒜  ≅  ⊕ₚ (𝒞ₚ ⊗ 𝒜)`,   with `πₚ ⊗ id` for coordinates.

That is **117III** `tensor_distributes_over_sums` (which distributes over
the *second* factor) read through **119IVc** `exists_braiding` and **114II**
`tensor_uniqueness`.  The only work is bookkeeping: 117III confines the
index type *and* the summands to a single universe, while the summands here
are the matrix algebras `M_{N p+1} : Type 0` over an index `P : Type u`.
`punitSum` — the `Type 0`/`Type u` bridge written for 125eVII — does the
moving, and `exists_lp_congr` (the fixed-index, universe-crossing companion
of `exists_lp_reindex`) carries the summandwise isomorphisms. -/

section HaTensorClosed

universe u₁ u₂ u₃ u₄

variable {X₁ : Type u₁} {X₂ : Type u₂} {Y : Type u₃}
  [CStarAlgebra X₁] [PartialOrder X₁] [StarOrderedRing X₁] [VonNeumannAlgebra X₁]
  [CStarAlgebra X₂] [PartialOrder X₂] [StarOrderedRing X₂] [VonNeumannAlgebra X₂]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]

/-- `ρ ⊗ id` is bijective when `ρ` is — the universe-polymorphic form (its
inverse is `ρ⁻¹ ⊗ id`, so `tensor_injective`, a single-universe statement, is
not needed). -/
private theorem tmapM_id_bijective (f : NMIUMap X₁ X₂) (hf : Function.Bijective ⇑f) :
    Function.Bijective ⇑(tmapM f (nmiuId Y)) := by
  have h1 : nmiuComp (nmiuSymm f hf) f = nmiuId X₁ :=
    DFunLike.coe_injective (funext fun x => nmiuSymm_apply_apply f hf x)
  have h2 : nmiuComp f (nmiuSymm f hf) = nmiuId X₂ :=
    DFunLike.coe_injective (funext fun y => nmiuSymm_apply_apply' f hf y)
  refine ⟨fun x y hxy => ?_, fun z =>
    ⟨tmapM (nmiuSymm f hf) (nmiuId Y) z, by rw [tmapM_comp_id, h2, tmapM_id]⟩⟩
  have h := congrArg (fun z : VNT X₂ Y => tmapM (nmiuSymm f hf) (nmiuId Y) z) hxy
  simpa only [tmapM_comp_id, h1, tmapM_id] using h

/-- A composite of bijective nmiu-maps is bijective (stated for `nmiuComp`
itself, so that `Function.Bijective.comp` never has to unify `⇑(g ∘ f)`
with `⇑g ∘ ⇑f` at the large tensor-product types below). -/
private theorem nmiuComp_bijective {Z₁ : Type u₁} {Z₂ : Type u₂} {Z₃ : Type u₃}
    [CStarAlgebra Z₁] [PartialOrder Z₁] [StarOrderedRing Z₁] [VonNeumannAlgebra Z₁]
    [CStarAlgebra Z₂] [PartialOrder Z₂] [StarOrderedRing Z₂] [VonNeumannAlgebra Z₂]
    [CStarAlgebra Z₃] [PartialOrder Z₃] [StarOrderedRing Z₃] [VonNeumannAlgebra Z₃]
    (g : NMIUMap Z₂ Z₃) (f : NMIUMap Z₁ Z₂) (hg : Function.Bijective ⇑g)
    (hf : Function.Bijective ⇑f) : Function.Bijective ⇑(nmiuComp g f) := by
  refine ⟨fun x y h => hf.1 (hg.1 h), fun z => ?_⟩
  obtain ⟨y, rfl⟩ := hg.2 z
  obtain ⟨x, rfl⟩ := hf.2 y
  exact ⟨x, rfl⟩

/-- A tensor product of nontrivial von Neumann algebras is nontrivial:
`‖1 ⊗ 1‖ = ‖1‖·‖1‖ = 1` by **116III**.2 `norm_vtmul`. -/
private theorem vnt_nontrivial {Cc Aa : Type u}
    [CStarAlgebra Cc] [PartialOrder Cc] [StarOrderedRing Cc] [VonNeumannAlgebra Cc]
    [CStarAlgebra Aa] [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa]
    [Nontrivial Cc] [Nontrivial Aa] : Nontrivial (VNT Cc Aa) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h1 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 1 := (vnTensor Cc Aa).isTensorProduct.miu.1
  have h2 : ‖((1 : Cc) ⊗ᵥ (1 : Aa))‖ = 1 := by
    rw [norm_vtmul, norm_one, norm_one, mul_one]
  rw [h1, h, norm_zero] at h2
  exact zero_ne_one h2

/-- `M_{n+1}`, presented as the one-summand direct sum `punitSum n`, is
nontrivial. -/
private theorem punitSum_nontrivial (n : ℕ) : Nontrivial (punitSum.{u} n) :=
  Function.Injective.nontrivial (f := ⇑(punitInv.{u} n))
    (nmiuSymm_bijective (punitEval.{u} n) (punitEval_bijective n)).1

attribute [local instance] punitSum_nontrivial

variable {Aa : Type u} [CStarAlgebra Aa] [PartialOrder Aa] [StarOrderedRing Aa]
  [VonNeumannAlgebra Aa] [Nontrivial Aa]

/-- `M_{n+1} ⊗ 𝒜` is nontrivial — the cross-universe form of
`vnt_nontrivial`, which `norm_vtmul` (a single-universe statement) does not
reach directly: `punitSum n ⊗ 𝒜` is nontrivial and injects into it. -/
private theorem vnt_mat_nontrivial (n : ℕ) :
    Nontrivial (VNT (MatAlg (n + 1)) Aa) := by
  haveI : Nontrivial (VNT (punitSum.{u} n) Aa) := vnt_nontrivial
  exact Function.Injective.nontrivial
    (f := ⇑(tmapM (punitEval.{u} n) (nmiuId Aa)))
    (tmapM_id_bijective (punitEval.{u} n) (punitEval_bijective n)).1

attribute [local instance] vnt_mat_nontrivial

/-- Summandwise nmiu-isomorphisms induce an nmiu-isomorphism of direct sums.
(`exists_lp_reindex` does this along a *bijection of index sets* but confines
the two families to one universe; here the index type is fixed and the
summands may move universe, which is what the `Type 0` matrix algebras
need.) -/
private theorem exists_lp_congr {I₀ : Type u₁} {𝒳 : I₀ → Type u₂} {𝒴 : I₀ → Type u₃}
    [∀ i, CStarAlgebra (𝒳 i)] [∀ i, Nontrivial (𝒳 i)] [∀ i, PartialOrder (𝒳 i)]
    [∀ i, StarOrderedRing (𝒳 i)] [∀ i, VonNeumannAlgebra (𝒳 i)]
    [∀ i, CStarAlgebra (𝒴 i)] [∀ i, Nontrivial (𝒴 i)] [∀ i, PartialOrder (𝒴 i)]
    [∀ i, StarOrderedRing (𝒴 i)] [∀ i, VonNeumannAlgebra (𝒴 i)]
    (w : ∀ i, NMIUMap (𝒳 i) (𝒴 i)) (hw : ∀ i, Function.Bijective ⇑(w i)) :
    ∃ Θ : NMIUMap (lp 𝒳 ∞) (lp 𝒴 ∞), Function.Bijective ⇑Θ ∧
      ∀ (x : lp 𝒳 ∞) (i : I₀),
        ((Θ x : lp 𝒴 ∞) : ∀ j, 𝒴 j) i = w i ((x : ∀ j, 𝒳 j) i) := by
  obtain ⟨Θ, hΘ, -⟩ := vn_products_nmiu (B := lp 𝒳 ∞) 𝒴
    (fun i => nmiuComp (w i) (lpEvalNMIU 𝒳 i))
  obtain ⟨Λ, hΛ, -⟩ := vn_products_nmiu (B := lp 𝒴 ∞) 𝒳
    (fun i => nmiuComp (nmiuSymm (w i) (hw i)) (lpEvalNMIU 𝒴 i))
  have hΘa : ∀ (x : lp 𝒳 ∞) (i : I₀),
      ((Θ x : lp 𝒴 ∞) : ∀ j, 𝒴 j) i = w i ((x : ∀ j, 𝒳 j) i) := fun x i => hΘ i x
  have hΛa : ∀ (z : lp 𝒴 ∞) (i : I₀),
      ((Λ z : lp 𝒳 ∞) : ∀ j, 𝒳 j) i
        = nmiuSymm (w i) (hw i) ((z : ∀ j, 𝒴 j) i) := fun z i => hΛ i z
  refine ⟨Θ, ⟨fun x y hxy => ?_, fun z => ⟨Λ z, ?_⟩⟩, hΘa⟩
  · refine lp.ext (funext fun i => ?_)
    have hx : ((Λ (Θ x) : lp 𝒳 ∞) : ∀ j, 𝒳 j) i = (x : ∀ j, 𝒳 j) i := by
      rw [hΛa, hΘa, nmiuSymm_apply_apply]
    have hy : ((Λ (Θ y) : lp 𝒳 ∞) : ∀ j, 𝒳 j) i = (y : ∀ j, 𝒳 j) i := by
      rw [hΛa, hΘa, nmiuSymm_apply_apply]
    rw [← hx, ← hy, hxy]
  · refine lp.ext (funext fun i => ?_)
    rw [hΘa, hΛa, nmiuSymm_apply_apply']

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **The products of `haW*_miu` pass through `(·) ⊗ 𝒜`**:
`(⊕ₚ M_{N p+1}) ⊗ 𝒜 ≅ ⊕ₚ (M_{N p+1} ⊗ 𝒜)`, with the coordinates of the
isomorphism the maps `πₚ ⊗ id`.  This is **117III**
`tensor_distributes_over_sums` (over the *second* factor), transported by
**119IVc** `exists_braiding` and moved onto the `Type 0` summands by
`punitSum`. -/
private theorem exists_matSumTensorIso {P₀ : Type u} (N : P₀ → ℕ) :
    ∃ θ : NMIUMap (VNT (lp (fun p : P₀ => MatAlg (N p + 1)) ∞) Aa)
        (lp (fun p : P₀ => VNT (MatAlg (N p + 1)) Aa) ∞),
      Function.Bijective ⇑θ ∧
      ∀ (x : VNT (lp (fun p : P₀ => MatAlg (N p + 1)) ∞) Aa) (p : P₀),
        ((θ x : lp (fun q : P₀ => VNT (MatAlg (N q + 1)) Aa) ∞) :
            ∀ q : P₀, VNT (MatAlg (N q + 1)) Aa) p
          = tmapM (lpEvalNMIU (fun q : P₀ => MatAlg (N q + 1)) p) (nmiuId Aa) x := by
  classical
  have hpe : ∀ (n : ℕ) (m : MatAlg (n + 1)),
      punitEval.{u} n (punitInv.{u} n m) = m := fun n m =>
    nmiuSymm_apply_apply' (punitEval.{u} n) (punitEval_bijective n) m
  -- (1) the `Type u` avatar of the summands
  obtain ⟨Θ, hΘbij, hΘa⟩ := exists_lp_congr
    (𝒳 := fun p : P₀ => MatAlg (N p + 1)) (𝒴 := fun p : P₀ => punitSum.{u} (N p))
    (fun p => punitInv.{u} (N p))
    (fun p => nmiuSymm_bijective (punitEval.{u} (N p)) (punitEval_bijective (N p)))
  -- (2) **117III**, and **114II** to move it onto the chosen tensor product
  haveI hntp : ∀ p : P₀, Nontrivial (VNT Aa (punitSum.{u} (N p))) :=
    fun _ => vnt_nontrivial
  haveI hntp' : ∀ p : P₀, Nontrivial (VNT (punitSum.{u} (N p)) Aa) :=
    fun _ => vnt_nontrivial
  haveI hntm : ∀ p : P₀, Nontrivial (VNT (MatAlg (N p + 1)) Aa) :=
    fun p => vnt_mat_nontrivial (N p)
  obtain ⟨γ, hγe, hγ⟩ :=
    tensor_distributes_over_sums (A := Aa) (fun p : P₀ => punitSum.{u} (N p))
  obtain ⟨φ, hφe, hφbij, -⟩ :=
    tensor_uniqueness (vnTensor (lp (fun p : P₀ => punitSum.{u} (N p)) ∞) Aa).map
      γ.flip (vnTensor (lp (fun p : P₀ => punitSum.{u} (N p)) ∞) Aa).isTensorProduct
      (isTensorProduct_flip hγ)
  -- (3) the braidings of the summands
  have hbr : ∀ p : P₀, ∃ s : NMIUMap (VNT Aa (punitSum.{u} (N p)))
      (VNT (punitSum.{u} (N p)) Aa),
      (∀ (a : Aa) (c : punitSum.{u} (N p)), s (a ⊗ᵥ c) = c ⊗ᵥ a) ∧
        Function.Bijective ⇑s := fun p => by
    obtain ⟨s, hs, hsb, -⟩ := exists_braiding Aa (punitSum.{u} (N p))
    exact ⟨s, hs, hsb⟩
  choose s hse hsbij using hbr
  obtain ⟨Ξ, hΞbij, hΞa⟩ := exists_lp_congr
    (𝒳 := fun p : P₀ => VNT Aa (punitSum.{u} (N p)))
    (𝒴 := fun p : P₀ => VNT (punitSum.{u} (N p)) Aa) s hsbij
  -- (4) back to the matrix summands
  obtain ⟨Ω, hΩbij, hΩa⟩ := exists_lp_congr
    (𝒳 := fun p : P₀ => VNT (punitSum.{u} (N p)) Aa)
    (𝒴 := fun p : P₀ => VNT (MatAlg (N p + 1)) Aa)
    (fun p => tmapM (punitEval.{u} (N p)) (nmiuId Aa))
    (fun p => tmapM_id_bijective _ (punitEval_bijective (N p)))
  refine ⟨nmiuComp Ω (nmiuComp Ξ (nmiuComp φ (tmapM Θ (nmiuId Aa)))), ?_, ?_⟩
  · exact nmiuComp_bijective _ _ hΩbij (nmiuComp_bijective _ _ hΞbij
      (nmiuComp_bijective _ _ hφbij (tmapM_id_bijective Θ hΘbij)))
  · intro x p
    -- both sides are nmiu-maps of `x`; they agree on the elementary tensors,
    -- which generate `(⊕ₚ M_{N p+1}) ⊗ 𝒜`
    have hgen : wstar (VNT (lp (fun q : P₀ => MatAlg (N q + 1)) ∞) Aa)
        {t : VNT (lp (fun q : P₀ => MatAlg (N q + 1)) ∞) Aa |
          ∃ a b, t = (vnTensor (lp (fun q : P₀ => MatAlg (N q + 1)) ∞) Aa).map a b}
        = ⊤ :=
      wstar_eq_top_of_dense_span _
        (vnTensor (lp (fun q : P₀ => MatAlg (N q + 1)) ∞) Aa).isTensorProduct.dense
    refine nmiu_ext_of_wstar_top
      (nmiuComp (lpEvalNMIU (fun q : P₀ => VNT (MatAlg (N q + 1)) Aa) p)
        (nmiuComp Ω (nmiuComp Ξ (nmiuComp φ (tmapM Θ (nmiuId Aa))))))
      (tmapM (lpEvalNMIU (fun q : P₀ => MatAlg (N q + 1)) p) (nmiuId Aa)) _ hgen
      ?_ x
    rintro _ ⟨c, a, rfl⟩
    show ((Ω (Ξ (φ (tmapM Θ (nmiuId Aa) (c ⊗ᵥ a)))) :
        lp (fun q : P₀ => VNT (MatAlg (N q + 1)) Aa) ∞) :
        ∀ q : P₀, VNT (MatAlg (N q + 1)) Aa) p
      = tmapM (lpEvalNMIU (fun q : P₀ => MatAlg (N q + 1)) p) (nmiuId Aa) (c ⊗ᵥ a)
    have e1 : tmapM Θ (nmiuId Aa) (c ⊗ᵥ a) = (Θ c) ⊗ᵥ a := by
      rw [tmapM_apply, nmiuId_apply]
    have hφe' : ∀ (y : lp (fun q : P₀ => punitSum.{u} (N q)) ∞) (bb : Aa),
        φ (y ⊗ᵥ bb) = γ.flip y bb := hφe
    have e2 : ((φ ((Θ c) ⊗ᵥ a) :
        lp (fun q : P₀ => VNT Aa (punitSum.{u} (N q))) ∞) :
        ∀ q : P₀, VNT Aa (punitSum.{u} (N q))) p
        = a ⊗ᵥ ((Θ c : lp (fun q : P₀ => punitSum.{u} (N q)) ∞) :
            ∀ q : P₀, punitSum.{u} (N q)) p := by
      rw [hφe' (Θ c) a]
      exact hγe a (Θ c) p
    rw [e1, hΩa, hΞa, e2, hse, hΘa, tmapM_apply, nmiuId_apply, hpe,
      tmapM_apply, nmiuId_apply]
    rfl


/-! ### The solution set of 125dII

proc.tex:5541 asks for "a suitably modified solution set".  It can be taken
to be, simply, *all* nmiu-maps `ℬ → M_{n+1} ⊗ 𝒜` — an honest set, the
matrix algebras being indexed by `ℕ` — because a hereditarily atomic `𝒞`
*is* a direct sum of matrix algebras (**84bII**) and `(·) ⊗ 𝒜` turns that
direct sum into a product (`exists_matSumTensorIso`): the maps
`(πᵢ ⊗ id) ∘ h` are already in the solution set, and `h` is assembled from
them.  So the cardinality machinery of 125bII — **124I**
`vn_generation_bound`, the index type `K`, `exists_haPresentation` — is not
needed here at all. -/

/-- The index of the solution set of **125dII**. -/
private abbrev HaTSolIdx (Bb Aa : Type u) [CStarAlgebra Bb] [PartialOrder Bb]
    [StarOrderedRing Bb] [VonNeumannAlgebra Bb] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] : Type u :=
  Σ n : ℕ, NMIUMap Bb (VNT (MatAlg (n + 1)) Aa)

/-- The product over the solution set — a direct sum of matrix algebras, so
hereditarily atomic by definition. -/
private abbrev haTSolProd (Bb Aa : Type u) [CStarAlgebra Bb] [PartialOrder Bb]
    [StarOrderedRing Bb] [VonNeumannAlgebra Bb] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] : Type u :=
  lp (fun r : HaTSolIdx Bb Aa => MatAlg (r.1 + 1)) ∞

/-- Into a trivial von Neumann algebra there is an nmiu-map from anywhere
(the degenerate case `𝒜` subsingleton of 125dII, where `𝒞 ⊗ 𝒜` is trivial
for every `𝒞`). -/
private def nmiuOfSubsingleton (Z₁ : Type u₁) (Z₂ : Type u₂)
    [CStarAlgebra Z₁] [PartialOrder Z₁] [StarOrderedRing Z₁]
    [CStarAlgebra Z₂] [PartialOrder Z₂] [StarOrderedRing Z₂] [Subsingleton Z₂] :
    NMIUMap Z₁ Z₂ where
  toStarAlgHom :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _
      map_star' := fun _ => Subsingleton.elim _ _ }
  preservesDirSups' := fun _ _ _ _ _ =>
    ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
      fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩

/-- A hereditarily atomic algebra with a nonempty index set is nontrivial —
which is how the *nontrivial* case of 125dII's degenerate split is entered
from a slice index `j ∈ J`. -/
private theorem nontrivial_of_haIndex {Aa : Type u} [CStarAlgebra Aa]
    [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa] {J : Type u}
    {nn : J → ℕ} (Φ : Aa ≃⋆ₐ[ℂ] lp (fun j : J => MatAlg (nn j + 1)) ∞) (j : J) :
    Nontrivial Aa := by
  refine Function.Injective.nontrivial
    (f := fun m : MatAlg (nn j + 1) => Φ.symm (lpKappa j m)) ?_
  intro m m' hm
  have h1 : lpKappa j m = lpKappa j m' := Φ.symm.injective hm
  have h2 := congrArg
    (fun x : lp (fun k : J => MatAlg (nn k + 1)) ∞ =>
      (x : ∀ k : J, MatAlg (nn k + 1)) j) h1
  rwa [lpKappa_apply_self, lpKappa_apply_self] at h2

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **125dII** (proc.tex:5528, Proposition): for hereditarily atomic `𝒜`
the functor `(·) ⊗ 𝒜 : haW*_miu → haW*_miu` has a left adjoint
`(·)^{*_ha 𝒜}`.

`hB` is the hypothesis that the *object* `ℬ` lies in `haW*_miu`; that is
part of 125dII's own setting, so the statement is not weaker than the
Proposition.  But **`hB` is never used**: it occurs only in the binder
(`linter.unusedVariables` reports it, and the proof below mentions it
nowhere).  It cannot be used, either — the carrier is a von Neumann
subalgebra of the direct sum of matrix algebras `haTSolProd ℬ 𝒜`
whatever `ℬ` is, and the unit is corestricted to it — so the tree in fact
proves the **stronger** fact that `(·) ⊗ 𝒜` has a left adjoint on *all* of
`W*_miu`, not only on `haW*_miu`.  (`hA` *is* used: it supplies the
presentation `Φ` of `𝒜` that `haE_mem`/`haE_natural` and
`nontrivial_of_haIndex` need.)  The stronger form is not stated, because
the thesis states the adjunction with `haW*_miu` as its domain. -/
theorem ha_tensor_closed [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (hA : HereditarilyAtomic A) (hB : HereditarilyAtomic B) :
    Nonempty (HaFreeExp B A) := by
  classical
  obtain ⟨J, nn, ⟨Φ⟩⟩ := hA
  have hPha : HereditarilyAtomic (haTSolProd B A) :=
    ⟨HaTSolIdx B A, fun r => r.1, ⟨StarAlgEquiv.refl ℂ (haTSolProd B A)⟩⟩
  -- **weak initiality**: the mediating map `η : ℬ → P ⊗ 𝒜`, whose `r`-th
  -- coordinate is the solution-set entry `r` itself
  obtain ⟨η, hη⟩ : ∃ η : NMIUMap B (VNT (haTSolProd B A) A),
      ∀ (r : HaTSolIdx B A) (b : B),
        tmapM (lpEvalNMIU (fun q : HaTSolIdx B A => MatAlg (q.1 + 1)) r) (nmiuId A)
            (η b) = r.2 b := by
    rcases subsingleton_or_nontrivial A with hss | hnt
    · haveI := hss
      haveI : Subsingleton (VNT (haTSolProd B A) A) := vnt_subsingleton
      haveI : ∀ r : HaTSolIdx B A, Subsingleton (VNT (MatAlg (r.1 + 1)) A) :=
        fun _ => vnt_subsingleton
      exact ⟨nmiuOfSubsingleton B (VNT (haTSolProd B A) A),
        fun r b => Subsingleton.elim _ _⟩
    · haveI := hnt
      haveI hntm : ∀ r : HaTSolIdx B A, Nontrivial (VNT (MatAlg (r.1 + 1)) A) :=
        fun r => vnt_mat_nontrivial r.1
      obtain ⟨θ, hθbij, hθa⟩ :=
        exists_matSumTensorIso (Aa := A) (fun r : HaTSolIdx B A => r.1)
      obtain ⟨pr, hpr, -⟩ := vn_products_nmiu (B := B)
        (fun r : HaTSolIdx B A => VNT (MatAlg (r.1 + 1)) A) (fun r => r.2)
      refine ⟨nmiuComp (nmiuSymm θ hθbij) pr, fun r b => ?_⟩
      have h1 := hθa (nmiuSymm θ hθbij (pr b)) r
      rw [nmiuSymm_apply_apply'] at h1
      show tmapM (lpEvalNMIU (fun q : HaTSolIdx B A => MatAlg (q.1 + 1)) r) (nmiuId A)
          (nmiuSymm θ hθbij (pr b)) = r.2 b
      rw [← h1]
      exact hpr r b
  -- **the carrier**: the von Neumann subalgebra of `P` generated by the
  -- entries of `η`
  choose ent hent using fun
      (q : B × Σ j : J, Fin (nn j + 1) × Fin (nn j + 1)) =>
    haE_mem (C := haTSolProd B A) Φ q.2.1 q.2.2.1 q.2.2.2 (η q.1)
  have hDvn : IsVNSubalgebra (haTSolProd B A)
      (wstar (haTSolProd B A) (Set.range ent)) :=
    (isVNSubalgebra_wstar (Set.range ent)).1
  have hIvn : IsVNSubalgebra (VNT (haTSolProd B A) A)
      (tensorSub A (wstar (haTSolProd B A) (Set.range ent))) :=
    (isVNSubalgebra_wstar _).1
  have hηmem : ∀ b : B,
      η b ∈ tensorSub A (wstar (haTSolProd B A) (Set.range ent)) := by
    intro b
    refine haMem Φ _ _ (fun j k l => ?_)
    rw [hent ⟨b, ⟨j, (k, l)⟩⟩]
    exact (isVNSubalgebra_wstar _).2
      ⟨ent ⟨b, ⟨j, (k, l)⟩⟩,
        (isVNSubalgebra_wstar (Set.range ent)).2 ⟨⟨b, ⟨j, (k, l)⟩⟩, rfl⟩, 1, rfl⟩
  -- `ι ⊗ id` is injective with range exactly `D ⊗ 𝒜`, so `η` corestricts
  have hΞinj : Function.Injective
      ⇑(tmapM (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) (nmiuId A)) :=
    tmapM_injective _ _ VNSub.valNMIU_injective (fun _ _ h => h)
  have hΞmem : ∀ y : VNT (VNSub (haTSolProd B A)
        (wstar (haTSolProd B A) (Set.range ent)) hDvn) A,
      tmapM (VNSub.valNMIU (A := haTSolProd B A)
          (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) (nmiuId A) y
        ∈ tensorSub A (wstar (haTSolProd B A) (Set.range ent)) := by
    intro y
    have h := tmapM_range_le (A := A) (VNSub.valNMIU (A := haTSolProd B A)
      (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) y
    rwa [VNSub.valNMIU_range] at h
  have hΞsurj : ∀ z ∈ tensorSub A (wstar (haTSolProd B A) (Set.range ent)),
      ∃ y, tmapM (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) (nmiuId A) y = z := by
    have hle : tensorSub A (wstar (haTSolProd B A) (Set.range ent)) ≤
        (tmapM (VNSub.valNMIU (A := haTSolProd B A)
          (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn))
          (nmiuId A)).toStarAlgHom.range := by
      refine sInf_le ⟨nmiu_image _, ?_⟩
      rintro _ ⟨s, hs, a, rfl⟩
      refine ⟨(⟨s, hs⟩ : VNSub (haTSolProd B A)
        (wstar (haTSolProd B A) (Set.range ent)) hDvn) ⊗ᵥ a, ?_⟩
      show tmapM (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) (nmiuId A)
          ((⟨s, hs⟩ : VNSub (haTSolProd B A)
            (wstar (haTSolProd B A) (Set.range ent)) hDvn) ⊗ᵥ a) = s ⊗ᵥ a
      rw [tmapM_apply, nmiuId_apply]
      rfl
    intro z hz
    exact hle hz
  obtain ⟨un, hun⟩ : ∃ un : NMIUMap B (VNT (VNSub (haTSolProd B A)
        (wstar (haTSolProd B A) (Set.range ent)) hDvn) A),
      ∀ b : B, tmapM (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) (nmiuId A) (un b)
        = η b := by
    have hΛbij := nmiuCorestrict_bijective
      (tmapM (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)) (nmiuId A))
      (tensorSub A (wstar (haTSolProd B A) (Set.range ent))) hIvn hΞmem hΞinj hΞsurj
    refine ⟨nmiuComp (nmiuSymm _ hΛbij)
      (nmiuCorestrict η (tensorSub A (wstar (haTSolProd B A) (Set.range ent)))
        hIvn hηmem), fun b => ?_⟩
    exact congrArg VNSub.val (nmiuSymm_apply_apply' _ hΛbij
      (nmiuCorestrict η (tensorSub A (wstar (haTSolProd B A) (Set.range ent)))
        hIvn hηmem b))
  refine ⟨{ carrier := VNSub (haTSolProd B A)
              (wstar (haTSolProd B A) (Set.range ent)) hDvn
            ha := hereditarilyAtomic_subalgebra hPha VNSub.valNMIU
              VNSub.valNMIU_injective
            unit := un
            universal := fun C' _ _ _ _ hC' h => ?_ }⟩
  obtain ⟨I', m, ⟨Ψ⟩⟩ := hC'
  -- the decomposition of the target, as a pair of mutually inverse nmiu-maps
  have hΨbij : Function.Bijective
      ⇑(⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩ :
        NMIUMap C' (lp (fun i : I' => MatAlg (m i + 1)) ∞)) := Ψ.bijective
  -- the factoring map `P → 𝒞'`: coordinatewise, the solution-set entry
  -- `(πᵢ ∘ Ψ) ⊗ id ∘ h`
  obtain ⟨g₁, hg₁, -⟩ := vn_products_nmiu (B := haTSolProd B A)
    (fun i : I' => MatAlg (m i + 1))
    (fun i => lpEvalNMIU (fun q : HaTSolIdx B A => MatAlg (q.1 + 1))
      (⟨m i, nmiuComp (tmapM (nmiuComp
        (lpEvalNMIU (fun i' : I' => MatAlg (m i' + 1)) i)
        (⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩ :
          NMIUMap C' (lp (fun i' : I' => MatAlg (m i' + 1)) ∞))) (nmiuId A)) h⟩ :
        HaTSolIdx B A))
  have hfac : ∀ b : B, tmapM (nmiuComp
      (⟨Ψ.symm.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ.symm⟩ :
        NMIUMap (lp (fun i : I' => MatAlg (m i + 1)) ∞) C') g₁) (nmiuId A) (η b)
      = h b := by
    rcases subsingleton_or_nontrivial A with hss | hnt
    · haveI := hss
      haveI : Subsingleton (VNT C' A) := vnt_subsingleton
      exact fun b => Subsingleton.elim _ _
    · haveI := hnt
      haveI hntm : ∀ i : I', Nontrivial (VNT (MatAlg (m i + 1)) A) :=
        fun i => vnt_mat_nontrivial (m i)
      obtain ⟨θ', hθ'bij, hθ'a⟩ := exists_matSumTensorIso (Aa := A) m
      intro b
      refine (tmapM_id_bijective (⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩ :
        NMIUMap C' (lp (fun i : I' => MatAlg (m i + 1)) ∞)) hΨbij).1 ?_
      rw [tmapM_comp_id]
      refine hθ'bij.1 ?_
      refine lp.ext (funext fun i => ?_)
      rw [hθ'a, hθ'a, tmapM_comp_id, tmapM_comp_id]
      have hmapeq : nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (m i' + 1)) i)
          (nmiuComp (⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩ :
              NMIUMap C' (lp (fun i' : I' => MatAlg (m i' + 1)) ∞))
            (nmiuComp (⟨Ψ.symm.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ.symm⟩ :
              NMIUMap (lp (fun i' : I' => MatAlg (m i' + 1)) ∞) C') g₁))
          = lpEvalNMIU (fun q : HaTSolIdx B A => MatAlg (q.1 + 1))
            (⟨m i, nmiuComp (tmapM (nmiuComp
              (lpEvalNMIU (fun i' : I' => MatAlg (m i' + 1)) i)
              (⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩ :
                NMIUMap C' (lp (fun i' : I' => MatAlg (m i' + 1)) ∞))) (nmiuId A)) h⟩ :
              HaTSolIdx B A) := by
        refine DFunLike.coe_injective (funext fun x => ?_)
        show ((Ψ (Ψ.symm (g₁ x)) : lp (fun i' : I' => MatAlg (m i' + 1)) ∞) :
            ∀ i' : I', MatAlg (m i' + 1)) i = _
        rw [Ψ.apply_symm_apply]
        exact hg₁ i x
      rw [hmapeq, hη]
      rfl
  refine ⟨nmiuComp (nmiuComp
      (⟨Ψ.symm.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ.symm⟩ :
        NMIUMap (lp (fun i : I' => MatAlg (m i + 1)) ∞) C') g₁)
      (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)),
    fun b => ?_, fun g' hg' => ?_⟩
  · rw [← tmapM_comp_id, hun b]
    exact (hfac b).symm
  · -- **uniqueness**: the equaliser is a von Neumann subalgebra containing
    -- the entries, which generate the carrier
    obtain ⟨E, hE, hEset⟩ := vn_equalisers g' (nmiuComp (nmiuComp
      (⟨Ψ.symm.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ.symm⟩ :
        NMIUMap (lp (fun i : I' => MatAlg (m i + 1)) ∞) C') g₁)
      (VNSub.valNMIU (A := haTSolProd B A)
        (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)))
    have hEtop : E = ⊤ := by
      refine vnsub_wstar_eq_top E hE fun x hx => ?_
      obtain ⟨q, hq⟩ := hx
      haveI : Nontrivial A := nontrivial_of_haIndex Φ q.2.1
      obtain ⟨d, hd⟩ := haE_mem (C := VNSub (haTSolProd B A)
        (wstar (haTSolProd B A) (Set.range ent)) hDvn) Φ q.2.1 q.2.2.1 q.2.2.2 (un q.1)
      have hdx : d = x := by
        have hnat := haE_natural Φ (VNSub.valNMIU (A := haTSolProd B A)
          (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn))
          q.2.1 q.2.2.1 q.2.2.2 (un q.1)
        rw [hd, hun q.1, hent q, tmapM_apply, nmiuId_apply] at hnat
        exact VNSub.val_injective ((vtmul_one_injective hnat).trans hq)
      have hgg : g' d ⊗ᵥ (1 : A)
          = (nmiuComp (nmiuComp
              (⟨Ψ.symm.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ.symm⟩ :
                NMIUMap (lp (fun i : I' => MatAlg (m i + 1)) ∞) C') g₁)
              (VNSub.valNMIU (A := haTSolProd B A)
                (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn))) d
            ⊗ᵥ (1 : A) := by
        have h1 := haE_natural Φ g' q.2.1 q.2.2.1 q.2.2.2 (un q.1)
        have h2 := haE_natural Φ (nmiuComp (nmiuComp
          (⟨Ψ.symm.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ.symm⟩ :
            NMIUMap (lp (fun i : I' => MatAlg (m i + 1)) ∞) C') g₁)
          (VNSub.valNMIU (A := haTSolProd B A)
            (S := wstar (haTSolProd B A) (Set.range ent)) (hS := hDvn)))
          q.2.1 q.2.2.1 q.2.2.2 (un q.1)
        rw [hd, tmapM_apply, nmiuId_apply] at h1 h2
        rw [h1, h2, ← hg' q.1, ← tmapM_comp_id, hun q.1, hfac q.1]
      rw [← SetLike.mem_coe, hEset]
      show g' x = _
      rw [← hdx]
      exact vtmul_one_injective hgg
    refine DFunLike.coe_injective (funext fun x => ?_)
    have hxE : x ∈ (E : Set (VNSub (haTSolProd B A)
        (wstar (haTSolProd B A) (Set.range ent)) hDvn)) := by
      rw [hEtop]; trivial
    rw [hEset] at hxE
    exact hxE

end HaTensorClosed


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

section HaSliceBSurj

set_option synthInstance.maxHeartbeats 400000

universe u₁ u₂ u₃ u₄

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C] [VonNeumannAlgebra D]
variable {J : Type u} {nn : J → ℕ}
variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]

/-- **The ha form of 125eIII** (`tensorBsurjectivity`), the easy half:
if `(ρ ⊗ 𝒜) ∘ s` is `(·) ⊗ 𝒜`-surjective then `ρ` is surjective. -/
private theorem surj_of_haTensorBSurj (s : NMIUMap X (VNT C A)) (ρ : NMIUMap C D)
    (hcomp : TensorBSurjective (nmiuComp (tmapM ρ (nmiuId A)) s)) :
    Function.Surjective ⇑ρ := by
  have hrange : Set.range ⇑(nmiuComp (tmapM ρ (nmiuId A)) s)
      ⊆ ((tensorSub A ρ.toStarAlgHom.range : StarSubalgebra ℂ (VNT D A)) :
        Set (VNT D A)) := by
    rintro _ ⟨a, rfl⟩
    exact tmapM_range_le ρ (s a)
  have htop := hcomp ρ.toStarAlgHom.range (nmiu_image ρ) hrange
  intro d
  have hd : d ∈ ρ.toStarAlgHom.range := by rw [htop]; trivial
  exact hd

/-- **The ha form of 125eIII** (`tensorBsurjectivity`), the hard half:
`(ρ ⊗ 𝒜) ∘ s` is `(·) ⊗ 𝒜`-surjective when `s` is and `ρ` is surjective. -/
private theorem haTensorBSurj
    (Φ : A ≃⋆ₐ[ℂ] lp (fun j : J => MatAlg (nn j + 1)) ∞) (s : NMIUMap X (VNT C A))
    (hs : TensorBSurjective s) (ρ : NMIUMap C D) (hρ : Function.Surjective ⇑ρ) :
    TensorBSurjective (nmiuComp (tmapM ρ (nmiuId A)) s) := by
  intro S hS hsub
  have h1 : Set.range ⇑s ⊆
      ((tensorSub A (S.comap ρ.toStarAlgHom) : StarSubalgebra ℂ (VNT C A)) :
        Set (VNT C A)) := by
    rintro _ ⟨a, rfl⟩
    exact (haTensorPreimage Φ ρ S hS (s a)).mp (hsub ⟨a, rfl⟩)
  have h2 := hs _ (isVNSubalgebra_comap ρ.toStarAlgHom ρ.preservesDirSups' S hS) h1
  refine eq_top_iff.mpr fun d _ => ?_
  obtain ⟨c, rfl⟩ := hρ d
  have hc : c ∈ S.comap ρ.toStarAlgHom := by rw [h2]; trivial
  exact hc

/-! ### `(·) ⊗ ℬ`-surjectivity: congruence and transport along an isomorphism -/

variable {Xs : Type u₁} {C₁ : Type u₂} {C₂ : Type u₃} {Bb : Type u₄}
  [CStarAlgebra Xs] [PartialOrder Xs] [StarOrderedRing Xs] [VonNeumannAlgebra Xs]
  [CStarAlgebra C₁] [PartialOrder C₁] [StarOrderedRing C₁] [VonNeumannAlgebra C₁]
  [CStarAlgebra C₂] [PartialOrder C₂] [StarOrderedRing C₂] [VonNeumannAlgebra C₂]
  [CStarAlgebra Bb] [PartialOrder Bb] [StarOrderedRing Bb] [VonNeumannAlgebra Bb]

private theorem tensorBSurjective_congr {s₁ s₂ : NMIUMap Xs (VNT C₁ Bb)}
    (h : ∀ a, s₁ a = s₂ a) (hs : TensorBSurjective s₁) : TensorBSurjective s₂ := by
  intro S hS hsub
  refine hs S hS ?_
  rintro _ ⟨a, rfl⟩
  rw [h a]
  exact hsub ⟨a, rfl⟩

private theorem tensorBSurjective_of_iso (θ : NMIUMap C₁ C₂)
    (hθ : Function.Bijective ⇑θ) (s : NMIUMap Xs (VNT C₁ Bb))
    (hs : TensorBSurjective s) :
    TensorBSurjective (nmiuComp (tmapM θ (nmiuId Bb)) s) := by
  intro S hS hsub
  have hθθ : nmiuComp (nmiuSymm θ hθ) θ = nmiuId C₁ :=
    DFunLike.coe_injective (funext fun c => nmiuSymm_apply_apply θ hθ c)
  have hcomap : IsVNSubalgebra C₁ (S.comap θ.toStarAlgHom) :=
    isVNSubalgebra_comap θ.toStarAlgHom θ.preservesDirSups' S hS
  have hpull : ∀ y : VNT C₂ Bb, y ∈ tensorSub Bb S →
      tmapM (nmiuSymm θ hθ) (nmiuId Bb) y ∈ tensorSub Bb (S.comap θ.toStarAlgHom) := by
    intro y hy
    have hle : tensorSub Bb S ≤ (tensorSub Bb (S.comap θ.toStarAlgHom)).comap
        (tmapM (nmiuSymm θ hθ) (nmiuId Bb)).toStarAlgHom := by
      refine sInf_le ⟨isVNSubalgebra_comap _
        (tmapM (nmiuSymm θ hθ) (nmiuId Bb)).preservesDirSups' _
        (isVNSubalgebra_wstar _).1, ?_⟩
      rintro _ ⟨t, ht, b, rfl⟩
      show tmapM (nmiuSymm θ hθ) (nmiuId Bb) (t ⊗ᵥ b)
        ∈ tensorSub Bb (S.comap θ.toStarAlgHom)
      rw [tmapM_apply, nmiuId_apply]
      refine (isVNSubalgebra_wstar _).2 ⟨nmiuSymm θ hθ t, ?_, b, rfl⟩
      show θ.toStarAlgHom (nmiuSymm θ hθ t) ∈ S
      rw [show θ.toStarAlgHom (nmiuSymm θ hθ t) = t from nmiuSymm_apply_apply' θ hθ t]
      exact ht
    exact hle hy
  have hrange : Set.range ⇑s ⊆
      ((tensorSub Bb (S.comap θ.toStarAlgHom) : StarSubalgebra ℂ (VNT C₁ Bb)) :
        Set (VNT C₁ Bb)) := by
    rintro _ ⟨a, rfl⟩
    have h1 : tmapM θ (nmiuId Bb) (s a) ∈ tensorSub Bb S := hsub ⟨a, rfl⟩
    have h2 := hpull _ h1
    rw [tmapM_comp_id, hθθ, tmapM_id] at h2
    exact h2
  have htop := hs _ hcomap hrange
  refine eq_top_iff.mpr fun c₂ _ => ?_
  obtain ⟨c₁, rfl⟩ := hθ.2 c₂
  have hc : c₁ ∈ S.comap θ.toStarAlgHom := by rw [htop]; trivial
  exact hc

/-! ### Cross-universe form of the easy half of 125eIII -/

private theorem tmapM_range_le2 (ρ : NMIUMap C₁ C₂) (y : VNT C₁ Bb) :
    tmapM ρ (nmiuId Bb) y ∈ tensorSub Bb ρ.toStarAlgHom.range := by
  have htop : wstar (VNT C₁ Bb)
      {t : VNT C₁ Bb | ∃ a b, t = (vnTensor C₁ Bb).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor C₁ Bb).isTensorProduct.dense
  have hle : wstar (VNT C₁ Bb) {t : VNT C₁ Bb | ∃ a b, t = (vnTensor C₁ Bb).map a b} ≤
      (tensorSub Bb ρ.toStarAlgHom.range).comap (tmapM ρ (nmiuId Bb)).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM ρ (nmiuId Bb)).toStarAlgHom
      (tmapM ρ (nmiuId Bb)).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨c, b, rfl⟩
    show tmapM ρ (nmiuId Bb) (c ⊗ᵥ b) ∈ tensorSub Bb ρ.toStarAlgHom.range
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2 ⟨ρ c, ⟨c, rfl⟩, b, rfl⟩
  rw [htop, top_le_iff] at hle
  have hy : y ∈ (tensorSub Bb ρ.toStarAlgHom.range).comap
      (tmapM ρ (nmiuId Bb)).toStarAlgHom := by rw [hle]; trivial
  exact hy

private theorem surj_of_haTensorBSurj2 (s : NMIUMap Xs (VNT C₁ Bb)) (ρ : NMIUMap C₁ C₂)
    (hcomp : TensorBSurjective (nmiuComp (tmapM ρ (nmiuId Bb)) s)) :
    Function.Surjective ⇑ρ := by
  have hrange : Set.range ⇑(nmiuComp (tmapM ρ (nmiuId Bb)) s)
      ⊆ ((tensorSub Bb ρ.toStarAlgHom.range : StarSubalgebra ℂ (VNT C₂ Bb)) :
        Set (VNT C₂ Bb)) := by
    rintro _ ⟨a, rfl⟩
    exact tmapM_range_le2 ρ (s a)
  have htop := hcomp ρ.toStarAlgHom.range (nmiu_image ρ) hrange
  intro d
  have hd : d ∈ ρ.toStarAlgHom.range := by rw [htop]; trivial
  exact hd

private theorem nmiuComp_punit (n : ℕ) {Z : Type u₁} [CStarAlgebra Z] [PartialOrder Z]
    [StarOrderedRing Z] [VonNeumannAlgebra Z] (ρ : NMIUMap Z (MatAlg (n + 1))) :
    nmiuComp (punitEval.{u} n) (nmiuComp (punitInv.{u} n) ρ) = ρ :=
  DFunLike.coe_injective (funext fun z =>
    nmiuSymm_apply_apply' (punitEval.{u} n) (punitEval_bijective n) (ρ z))

/-! ### The unit of `(·)^{*_ha ℬ}` is `(·) ⊗ ℬ`-surjective (proc.tex:5690) -/

private theorem haFreeExp_unit_tensorBSurjective {Aa Bb2 : Type u}
    [CStarAlgebra Aa] [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa]
    [CStarAlgebra Bb2] [PartialOrder Bb2] [StarOrderedRing Bb2] [VonNeumannAlgebra Bb2]
    (F : HaFreeExp Aa Bb2) : TensorBSurjective F.unit := by
  intro S hS hsub
  have hSha : HereditarilyAtomic (VNSub F.carrier S hS) :=
    hereditarilyAtomic_subalgebra F.ha VNSub.valNMIU VNSub.valNMIU_injective
  set Θ : NMIUMap (VNT (VNSub F.carrier S hS) Bb2) (VNT F.carrier Bb2) :=
    tmapM (VNSub.valNMIU (A := F.carrier) (S := S) (hS := hS)) (nmiuId Bb2) with hΘ
  have hΘinj : Function.Injective ⇑Θ :=
    tmapM_injective _ _ VNSub.valNMIU_injective (fun _ _ h => h)
  have hTvn : IsVNSubalgebra (VNT F.carrier Bb2) Θ.toStarAlgHom.range := nmiu_image Θ
  have hle : tensorSub Bb2 S ≤ Θ.toStarAlgHom.range := by
    refine sInf_le ⟨hTvn, ?_⟩
    rintro _ ⟨t, ht, b, rfl⟩
    refine ⟨(⟨t, ht⟩ : VNSub F.carrier S hS) ⊗ᵥ b, ?_⟩
    show Θ ((⟨t, ht⟩ : VNSub F.carrier S hS) ⊗ᵥ b) = t ⊗ᵥ b
    rw [hΘ, tmapM_apply, nmiuId_apply]
    rfl
  have hmemΘ : ∀ y, Θ y ∈ Θ.toStarAlgHom.range := fun y => ⟨y, rfl⟩
  set κ := nmiuCorestrict Θ Θ.toStarAlgHom.range hTvn hmemΘ with hκ
  have hκbij : Function.Bijective ⇑κ :=
    nmiuCorestrict_bijective Θ _ hTvn hmemΘ hΘinj (by rintro _ ⟨y, rfl⟩; exact ⟨y, rfl⟩)
  have hmemη : ∀ a : Aa, F.unit a ∈ Θ.toStarAlgHom.range := fun a => hle (hsub ⟨a, rfl⟩)
  set η' := nmiuCorestrict F.unit Θ.toStarAlgHom.range hTvn hmemη with hη'
  set f : NMIUMap Aa (VNT (VNSub F.carrier S hS) Bb2) :=
    nmiuComp (nmiuSymm κ hκbij) η' with hf
  have hfΘ : ∀ a : Aa, Θ (f a) = F.unit a := by
    intro a
    have h1 : κ (f a) = η' a := nmiuSymm_apply_apply' κ hκbij (η' a)
    exact congrArg VNSub.val h1
  obtain ⟨g, hg, -⟩ := F.universal (VNSub F.carrier S hS) hSha f
  set σ : NMIUMap F.carrier F.carrier :=
    nmiuComp (VNSub.valNMIU (A := F.carrier) (S := S) (hS := hS)) g with hσ
  have hσunit : ∀ a : Aa, F.unit a = tmapM σ (nmiuId Bb2) (F.unit a) := by
    intro a
    rw [hσ, ← tmapM_comp_id, ← hg a]
    exact (hfΘ a).symm
  have hidunit : ∀ a : Aa,
      F.unit a = tmapM (nmiuId F.carrier) (nmiuId Bb2) (F.unit a) :=
    fun a => (tmapM_id _).symm
  obtain ⟨g₀, -, huniq⟩ := F.universal F.carrier F.ha F.unit
  have hσid : σ = nmiuId F.carrier :=
    (huniq σ hσunit).trans (huniq (nmiuId F.carrier) hidunit).symm
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (g x).val = x := by
    have := congrArg (fun h : NMIUMap F.carrier F.carrier => h x) hσid
    exact this
  rw [← hx]
  exact (g x).property


end HaSliceBSurj

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

section AstarhaBAux

set_option synthInstance.maxHeartbeats 400000

/-! ### The concrete description of `𝒜^{*_ha ℬ}`

The assembly of 125eVII, following proc.tex:5680–5810 and the shape of
125cIII `Fha_concrete`.  The two genuinely new steps are
`haFreeExp_unit_tensorBSurjective` (proc.tex:5690) and the ha form of
`tensorBsurjectivity`; `hA` is *not* used. -/



/-- Infrastructure for the uniqueness clause of **125eVII**: two elements of
`(⊕ᵢ M_{Nᵢ+1}) ⊗ ℬ` with the same coordinates `(πᵢ ⊗ ℬ)(·)` are equal.
This is the injectivity half of `exists_matSumTensorIso` (**117III** through
**119IVc**), with the degenerate case `ℬ` trivial split off. -/
private theorem tensorB_ext_of_coords {I₀ Bb : Type u}
    [CStarAlgebra Bb] [PartialOrder Bb] [StarOrderedRing Bb]
    [VonNeumannAlgebra Bb] (N : I₀ → ℕ)
    (x y : VNT (lp (fun i : I₀ => MatAlg (N i + 1)) ∞) Bb)
    (h : ∀ i : I₀,
      tmapM (lpEvalNMIU (fun j : I₀ => MatAlg (N j + 1)) i) (nmiuId Bb) x
        = tmapM (lpEvalNMIU (fun j : I₀ => MatAlg (N j + 1)) i) (nmiuId Bb) y) :
    x = y := by
  rcases subsingleton_or_nontrivial Bb with hss | hnt
  · haveI := hss
    haveI : Subsingleton (VNT (lp (fun i : I₀ => MatAlg (N i + 1)) ∞) Bb) :=
      vnt_subsingleton
    exact Subsingleton.elim _ _
  · haveI := hnt
    haveI hntm : ∀ i : I₀, Nontrivial (VNT (MatAlg (N i + 1)) Bb) :=
      fun i => vnt_mat_nontrivial (Aa := Bb) (N i)
    obtain ⟨θ, hθbij, hθa⟩ := exists_matSumTensorIso (Aa := Bb) N
    refine hθbij.1 (lp.ext (funext fun i => ?_))
    rw [hθa, hθa, h i]

set_option maxHeartbeats 2000000 in
private theorem haAstarhaB_concrete_aux {Aa Bb2 : Type u}
    [CStarAlgebra Aa] [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa]
    [CStarAlgebra Bb2] [PartialOrder Bb2] [StarOrderedRing Bb2] [VonNeumannAlgebra Bb2]
    (hB : HereditarilyAtomic Bb2) (F : HaFreeExp Aa Bb2) (I : Type u) (N : I → ℕ)
    (s : ∀ i : I, NMIUMap Aa (VNT (MatAlg (N i + 1)) Bb2))
    (hsurj : ∀ i, TensorBSurjective (s i))
    (hdistinct : ∀ i j, i ≠ j → ¬ TensorBEquiv (s i) (s j))
    (hrep : ∀ (n : ℕ) (f : NMIUMap Aa (VNT (MatAlg (n + 1)) Bb2)),
      TensorBSurjective f → ∃ i, TensorBEquiv (s i) f) :
    ∃ Φ : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
      Function.Bijective ⇑Φ ∧
      (∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
        (∀ x : F.carrier, πΦ x = Φ x i) →
        ∀ a : Aa, tmapM πΦ (nmiuId Bb2) (F.unit a) = s i a) ∧
      ∀ Φ' : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
        (∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
          (∀ x : F.carrier, πΦ x = Φ' x i) →
          ∀ a : Aa, tmapM πΦ (nmiuId Bb2) (F.unit a) = s i a) → Φ' = Φ := by
  classical
  obtain ⟨JB, nnB, ⟨ΦB⟩⟩ := hB
  have hunit : TensorBSurjective F.unit := haFreeExp_unit_tensorBSurjective F
  obtain ⟨I', N', ⟨ψ₀⟩⟩ := F.ha
  obtain ⟨ψ, hψbij, -⟩ :
      ∃ ψ : NMIUMap F.carrier (lp (fun i' : I' => MatAlg (N' i' + 1)) ∞),
        Function.Bijective ⇑ψ ∧ ∀ x, ψ x = ψ₀ x :=
    ⟨⟨ψ₀.toStarAlgHom, starAlgEquiv_preservesDirSups' ψ₀⟩, ψ₀.bijective, fun _ => rfl⟩
  obtain ⟨pp, hppapp⟩ :
      ∃ pp : ∀ i' : I', NMIUMap F.carrier (MatAlg (N' i' + 1)),
        ∀ (i' : I') (x : F.carrier),
          pp i' x = ((ψ x : lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) :
            ∀ j : I', MatAlg (N' j + 1)) i' :=
    ⟨fun i' => nmiuComp (lpEvalNMIU (fun i' : I' => MatAlg (N' i' + 1)) i') ψ,
      fun _ _ => rfl⟩
  obtain ⟨ee, heeapp⟩ :
      ∃ ee : ∀ i' : I', NMIUMap Aa (VNT (MatAlg (N' i' + 1)) Bb2),
        ∀ (i' : I') (a : Aa), ee i' a = tmapM (pp i') (nmiuId Bb2) (F.unit a) :=
    ⟨fun i' => nmiuComp (tmapM (pp i') (nmiuId Bb2)) F.unit, fun _ _ => rfl⟩
  have hppsurj : ∀ i' : I', Function.Surjective ⇑(pp i') := by
    intro i' y
    obtain ⟨x, hx⟩ := hψbij.2 (lpKappa i' y)
    exact ⟨x, by rw [hppapp, hx, lpKappa_apply_self]⟩
  -- (i) each `eᵢ'` is `(·) ⊗ ℬ`-surjective
  have hesurj : ∀ i' : I', TensorBSurjective (ee i') := by
    intro i'
    have hinvbij : Function.Bijective ⇑(punitInv.{u} (N' i')) :=
      nmiuSymm_bijective _ _
    have hsu : Function.Surjective ⇑(nmiuComp (punitInv.{u} (N' i')) (pp i')) := by
      intro y
      obtain ⟨m, hm⟩ := hinvbij.2 y
      obtain ⟨x, hx⟩ := hppsurj i' m
      exact ⟨x, by show punitInv.{u} (N' i') (pp i' x) = y; rw [hx, hm]⟩
    have h1 := haTensorBSurj ΦB F.unit hunit
      (nmiuComp (punitInv.{u} (N' i')) (pp i')) hsu
    have h2 := tensorBSurjective_of_iso (punitEval.{u} (N' i'))
      (punitEval_bijective (N' i')) _ h1
    refine tensorBSurjective_congr (fun a => ?_) h2
    show tmapM (punitEval.{u} (N' i')) (nmiuId Bb2)
        (tmapM (nmiuComp (punitInv.{u} (N' i')) (pp i')) (nmiuId Bb2) (F.unit a))
      = ee i' a
    rw [tmapM_comp_id, nmiuComp_punit, heeapp]
  -- (ii) `c : I' → I`
  have hcex : ∀ i' : I', ∃ i : I, TensorBEquiv (s i) (ee i') :=
    fun i' => hrep (N' i') (ee i') (hesurj i')
  choose c hc using hcex
  -- (iii) the mediating maps `ρᵢ : F.carrier → M_{Nᵢ+1}`
  have hrhoex : ∀ i : I, ∃ ρ : NMIUMap F.carrier (MatAlg (N i + 1)),
      ∀ a : Aa, tmapM ρ (nmiuId Bb2) (F.unit a) = s i a := by
    intro i
    obtain ⟨g, hg, -⟩ := F.universal (punitSum.{u} (N i)) (punitSum_ha (N i))
      (nmiuComp (tmapM (punitInv.{u} (N i)) (nmiuId Bb2)) (s i))
    refine ⟨nmiuComp (punitEval.{u} (N i)) g, fun a => ?_⟩
    have h1 : tmapM (punitInv.{u} (N i)) (nmiuId Bb2) (s i a)
        = tmapM g (nmiuId Bb2) (F.unit a) := hg a
    have h2 : tmapM (punitEval.{u} (N i)) (nmiuId Bb2)
          (tmapM (punitInv.{u} (N i)) (nmiuId Bb2) (s i a))
        = tmapM (punitEval.{u} (N i)) (nmiuId Bb2)
          (tmapM g (nmiuId Bb2) (F.unit a)) := by rw [h1]
    rw [tmapM_comp_id, tmapM_comp_id, punitEval_comp_inv, tmapM_id] at h2
    exact h2.symm
  choose rho hrho using hrhoex
  have hrhosurj : ∀ i : I, Function.Surjective ⇑(rho i) := by
    intro i
    refine surj_of_haTensorBSurj2 F.unit (rho i) ?_
    exact tensorBSurjective_congr (fun a => (hrho i a).symm) (hsurj i)
  -- `d : I → I'` by the factoring lemma
  have hdex : ∀ i : I, ∃ i' : I', TensorBEquiv (ee i') (s i) := by
    intro i
    obtain ⟨rhoT, hrhoTapp⟩ :
        ∃ rhoT : NMIUMap (lp (fun i' : I' => MatAlg (N' i' + 1)) ∞) (MatAlg (N i + 1)),
          ∀ y, rhoT y = rho i (nmiuSymm ψ hψbij y) :=
      ⟨nmiuComp (rho i) (nmiuSymm ψ hψbij), fun _ => rfl⟩
    have hrhoTsurj : Function.Surjective ⇑rhoT := by
      intro y
      obtain ⟨x, hx⟩ := hrhosurj i y
      exact ⟨ψ x, by rw [hrhoTapp, nmiuSymm_apply_apply, hx]⟩
    obtain ⟨i', ρ', hρ'bij, hρ'fac⟩ :=
      exists_lp_factor (fun x hx hcen => matAlg_central_idem hx hcen)
        (fun _ x hx hcen => matAlg_central_idem hx hcen)
        (fun _ φ => matAlg_starAlgHom_injective φ) rhoT hrhoTsurj
    refine ⟨i', ρ', hρ'bij, fun a => ?_⟩
    have hcomp : nmiuComp ρ' (pp i') = rho i := by
      refine DFunLike.coe_injective (funext fun x => ?_)
      show ρ' (pp i' x) = rho i x
      rw [hppapp, ← hρ'fac (ψ x), hrhoTapp, nmiuSymm_apply_apply]
    rw [heeapp, tmapM_comp_id, hcomp, hrho i a]
  choose d hd using hdex
  -- transitivity of `(·) ⊗ ℬ`-equivalence
  have htrans : ∀ {n₁ n₂ n₃ : ℕ} {f₁ : NMIUMap Aa (VNT (MatAlg n₁) Bb2)}
      {f₂ : NMIUMap Aa (VNT (MatAlg n₂) Bb2)} {f₃ : NMIUMap Aa (VNT (MatAlg n₃) Bb2)},
      TensorBEquiv f₁ f₂ → TensorBEquiv f₂ f₃ → TensorBEquiv f₁ f₃ := by
    rintro n₁ n₂ n₃ f₁ f₂ f₃ ⟨φ₁, hb₁, he₁⟩ ⟨φ₂, hb₂, he₂⟩
    refine ⟨nmiuComp φ₂ φ₁, hb₂.comp hb₁, fun a => ?_⟩
    rw [← tmapM_comp_id, he₁ a, he₂ a]
  have hcd : ∀ i : I, c (d i) = i := by
    intro i
    by_contra hne
    exact hdistinct _ _ hne (htrans (hc (d i)) (hd i))
  -- uniqueness of the `e`-representatives
  have hsuniq : ∀ i₁ i₂ : I', TensorBEquiv (ee i₁) (ee i₂) → i₁ = i₂ := by
    rintro i₁ i₂ ⟨φ, hφbij, hφ⟩
    by_contra hne
    obtain ⟨μ₁, hμ₁⟩ : ∃ μ : NMIUMap F.carrier (punitSum.{u} (N' i₂)),
        ∀ x, μ x = punitInv.{u} (N' i₂) (φ (pp i₁ x)) :=
      ⟨nmiuComp (punitInv.{u} (N' i₂)) (nmiuComp φ (pp i₁)), fun _ => rfl⟩
    obtain ⟨μ₂, hμ₂⟩ : ∃ μ : NMIUMap F.carrier (punitSum.{u} (N' i₂)),
        ∀ x, μ x = punitInv.{u} (N' i₂) (pp i₂ x) :=
      ⟨nmiuComp (punitInv.{u} (N' i₂)) (pp i₂), fun _ => rfl⟩
    have hμ₁eq : μ₁ = nmiuComp (punitInv.{u} (N' i₂)) (nmiuComp φ (pp i₁)) :=
      DFunLike.coe_injective (funext hμ₁)
    have hμ₂eq : μ₂ = nmiuComp (punitInv.{u} (N' i₂)) (pp i₂) :=
      DFunLike.coe_injective (funext hμ₂)
    have h1 : ∀ a : Aa, tmapM (nmiuComp φ (pp i₁)) (nmiuId Bb2) (F.unit a)
        = tmapM (pp i₂) (nmiuId Bb2) (F.unit a) := by
      intro a
      rw [← tmapM_comp_id, ← heeapp, hφ a, heeapp]
    have hkey : ∀ a : Aa, tmapM μ₁ (nmiuId Bb2) (F.unit a)
        = tmapM μ₂ (nmiuId Bb2) (F.unit a) := by
      intro a
      calc tmapM μ₁ (nmiuId Bb2) (F.unit a)
          = tmapM (punitInv.{u} (N' i₂)) (nmiuId Bb2)
              (tmapM (nmiuComp φ (pp i₁)) (nmiuId Bb2) (F.unit a)) := by
            rw [hμ₁eq, tmapM_comp_id]
        _ = tmapM (punitInv.{u} (N' i₂)) (nmiuId Bb2)
              (tmapM (pp i₂) (nmiuId Bb2) (F.unit a)) := by rw [h1]
        _ = tmapM μ₂ (nmiuId Bb2) (F.unit a) := by rw [hμ₂eq, tmapM_comp_id]
    obtain ⟨g₀, -, huniq⟩ := F.universal (punitSum.{u} (N' i₂)) (punitSum_ha (N' i₂))
      (nmiuComp (tmapM μ₂ (nmiuId Bb2)) F.unit)
    have hμ : μ₁ = μ₂ :=
      (huniq μ₁ (fun a => (hkey a).symm)).trans (huniq μ₂ (fun _ => rfl)).symm
    have hφpp : ∀ x : F.carrier, φ (pp i₁ x) = pp i₂ x := by
      intro x
      have h : μ₁ x = μ₂ x :=
        congrArg (fun ν : NMIUMap F.carrier (punitSum.{u} (N' i₂)) => ν x) hμ
      rw [hμ₁ x, hμ₂ x] at h
      exact (nmiuSymm_bijective (punitEval.{u} (N' i₂)) (punitEval_bijective (N' i₂))).1 h
    obtain ⟨x, hx⟩ := hψbij.2 (lpKappa i₁ (1 : MatAlg (N' i₁ + 1)))
    have hx₁ : pp i₁ x = 1 := by rw [hppapp, hx, lpKappa_apply_self]
    have hx₂ : pp i₂ x = 0 := by
      rw [hppapp, hx, lpKappa_apply_ne _ _ (Ne.symm hne)]
    have := hφpp x
    rw [hx₁, hx₂, show (φ 1 : MatAlg (N' i₂ + 1)) = 1 from map_one φ.toStarAlgHom] at this
    exact one_ne_zero this
  have hdc : ∀ i' : I', d (c i') = i' := fun i' =>
    hsuniq _ _ (htrans (hd (c i')) (hc i'))
  obtain ⟨Θ, hΘbij, hΘ⟩ :=
    exists_lp_reindex (𝒜 := fun i' : I' => MatAlg (N' i' + 1))
      (ℬ := fun i : I => MatAlg (N i + 1)) (⟨d, c, hcd, hdc⟩ : I ≃ I')
      (fun i => (hd i).choose) (fun i => (hd i).choose_spec.1)
  -- the compatibility clause
  have hcompat : ∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
      (∀ x : F.carrier, πΦ x = nmiuComp Θ ψ x i) →
      ∀ a : Aa, tmapM πΦ (nmiuId Bb2) (F.unit a) = s i a := by
    intro i πΦ hπΦ a
    have hπeq : πΦ = nmiuComp ((hd i).choose) (pp (d i)) := by
      refine DFunLike.coe_injective (funext fun x => ?_)
      show πΦ x = (hd i).choose (pp (d i) x)
      rw [hπΦ x, hppapp]
      exact hΘ (ψ x) i
    rw [hπeq, ← tmapM_comp_id, ← heeapp]
    exact (hd i).choose_spec.2 a
  refine ⟨nmiuComp Θ ψ, hΘbij.comp hψbij, hcompat, ?_⟩
  -- **uniqueness** (proc.tex:5652: "the *unique* nmiu-map `Φ` that makes the
  -- diagram commute"), from `F.universal` — exactly as 125cIII
  -- `Fha_concrete` gets its uniqueness clause, except that here the unit
  -- lands in `F.carrier ⊗ ℬ`, so the two candidates are compared *after*
  -- tensoring with `ℬ`: their coordinates `(πᵢ ⊗ ℬ) ∘ (Φ ⊗ ℬ) ∘ η` are both
  -- `sᵢ`, and `tensorB_ext_of_coords` (117III) says the coordinates
  -- determine an element of `(⊕ᵢ M_{Nᵢ+1}) ⊗ ℬ`.
  intro Φ' hΦ'
  have hhaB : HereditarilyAtomic (lp (fun i : I => MatAlg (N i + 1)) ∞) :=
    ⟨I, N, ⟨StarAlgEquiv.refl (R := ℂ)
      (A := lp (fun i : I => MatAlg (N i + 1)) ∞)⟩⟩
  have key : ∀ Φ₀ : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
      (∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
        (∀ x : F.carrier, πΦ x = Φ₀ x i) →
        ∀ a : Aa, tmapM πΦ (nmiuId Bb2) (F.unit a) = s i a) →
      ∀ a : Aa, tmapM Φ₀ (nmiuId Bb2) (F.unit a)
        = tmapM (nmiuComp Θ ψ) (nmiuId Bb2) (F.unit a) := by
    intro Φ₀ h₀ a
    refine tensorB_ext_of_coords N _ _ (fun i => ?_)
    rw [tmapM_comp_id, tmapM_comp_id,
      h₀ i (nmiuComp (lpEvalNMIU (fun j : I => MatAlg (N j + 1)) i) Φ₀)
        (fun _ => rfl) a,
      hcompat i (nmiuComp (lpEvalNMIU (fun j : I => MatAlg (N j + 1)) i)
        (nmiuComp Θ ψ)) (fun _ => rfl) a]
  obtain ⟨g₀, -, huniq⟩ := F.universal _ hhaB
    (nmiuComp (tmapM (nmiuComp Θ ψ) (nmiuId Bb2)) F.unit)
  have h1 : Φ' = g₀ := huniq Φ' (fun a => (key Φ' hΦ' a).symm)
  have h2 : nmiuComp Θ ψ = g₀ := huniq (nmiuComp Θ ψ) (fun _ => rfl)
  rw [h1, h2]

end AstarhaBAux

/-- **125eVII** (`AstarhaB-concrete`, proc.tex:5652, Theorem): for
hereditarily atomic `𝒜`, `ℬ` with a set of representatives
`s_i : 𝒜 → M_{N_i+1} ⊗ ℬ` (`i ∈ I`) for `(·) ⊗ ℬ`-equivalence of the
`(·) ⊗ ℬ`-surjective nmiu-maps into matrix algebras tensor `ℬ`, the
unique nmiu-map `Φ : 𝒜^{*_ha ℬ} → ⊕ᵢ M_{N_i+1}` compatible with the
unit is an nmiu-isomorphism.  (The compatibility
`(π_i ⊗ ℬ)((Φ ⊗ ℬ)(η(a))) = s_i(a)` is rendered through the map
`Φᵢ := (π_i ∘ Φ) ⊗ ℬ` applied to the unit.)

The third conjunct is the Theorem's word "**the unique**": every nmiu-map
`Φ'` satisfying the same compatibility equals `Φ`.  (It is the clause the
sibling 125cIII `Fha_concrete` carries, and it is proved the same way, out
of `F.universal`; see the tail of `haAstarhaB_concrete_aux`.)

`hA` is stated and never used — the construction needs only the hereditary
atomicity of `ℬ` (through `haTensorBSurj`) and of `F.carrier` (`F.ha`) —
but it is 125eVII's own setting and is kept. -/
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
      (∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
        (∀ x : F.carrier, πΦ x = Φ x i) →
        ∀ a : A, tmapM πΦ (nmiuId B) (F.unit a) = s i a) ∧
      ∀ Φ' : NMIUMap F.carrier (lp (fun i : I => MatAlg (N i + 1)) ∞),
        (∀ (i : I) (πΦ : NMIUMap F.carrier (MatAlg (N i + 1))),
          (∀ x : F.carrier, πΦ x = Φ' x i) →
          ∀ a : A, tmapM πΦ (nmiuId B) (F.unit a) = s i a) → Φ' = Φ :=
  haAstarhaB_concrete_aux hB F I N s hsurj hdistinct hrep

end Theses.A.Proc

