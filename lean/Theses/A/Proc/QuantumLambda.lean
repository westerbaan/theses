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
  statements.  All four are **proved**: 124III `second_adjunction`
  (`Nonempty (FreeMIU 𝒜)`), 125bII `ha_second_adjunction`
  (`Nonempty (HaFreeMIU 𝒜)`), 125dII `ha_tensor_closed`
  (`Nonempty (HaFreeExp ℬ 𝒜)`) and 125VIII `tensor_closed`
  (`Nonempty (FreeExp ℬ 𝒜)`).  125VIII runs on 121II `intersection_tensor`
  (from `A/Proc/CommutationTheorem.lean`'s `intersection_tensor'`) and 125IV
  `equaliser_lemma`, through 125VI `tensor_equalisers` and 125VIIb
  `tensor_preimage`.  Because they consume 125IV,
  **125VI, 125VIIb, 125VIII, 125eIIa and 125eIII are stated after the 125IV
  apparatus** (the `EqL` block and `equaliser_lemma`), rather than at their
  places in parsecs 1250 and 1255.  That apparatus is placed *before* the
  packaged atomic type I statements and the concrete description of
  `(·)^{*_ha ℬ}`, so that the hereditarily atomic and atomic type I forms of
  125VIIb and 125eIII are not needed by anything and the general statements
  are cited where the thesis cites them.
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
import Theses.A.Proc.CommutationTheorem

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
∗-homomorphism.  Companion to `Theses.A.VN.vn_products_proj_normal`. -/
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

/-! **47IV**.2 and **47IV**.3 live in `A/VN/Basic.lean`, as
`Theses.A.VN.vn_products_proj_normal` and `Theses.A.VN.vn_products_nmiu`;
the use sites below call those directly.

One remark on them is recorded here: the proof of
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

/-- **122IV** (`nmiu-functional-product`, proc.tex:4591, Lemma), in its
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

/-- **121II** (`intersection-tensor`, proc.tex:4456, Proposition;
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
      concreteTensor H K (SA₁ ⊓ SA₂) (SB₁ ⊓ SB₂) :=
  intersection_tensor' SA₁ SA₂ SB₁ SB₂ hA₁ hA₂ hB₁ hB₂


end Concrete

/-! ## Parsec 1220: the first adjunction -/

variable (A) in
/-- **122I** (proc.tex:4486, Definition): the set `nsp(𝒜)` of
nmiu-functionals on a von Neumann algebra `𝒜` — the object part of the
functor `nsp = W*_miu(·, ℂ) : (W*_miu)^op → Set`. -/
abbrev nsp : Type u := NMIUMap A ℂ

/-- **122I** (proc.tex:4486, Definition), morphism part: an nmiu-map
`f : 𝒜 → ℬ` induces `nsp(f) : nsp(ℬ) → nsp(𝒜)`, `φ ↦ φ ∘ f`. -/
noncomputable def nspMap (f : NMIUMap A B) (φ : nsp B) : nsp A :=
  nmiuComp φ f

/-- **122II** (`first-adjunction`, proc.tex:4499, Proposition),
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

/-- **122II** (`first-adjunction`, proc.tex:4499, Proposition): the map
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

/-- **122II** (`first-adjunction`, proc.tex:4499, Proposition), the
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

/-- **122IV** (`nmiu-functional-product`, proc.tex:4591, Lemma): an
nmiu-functional on a direct sum `⊕ᵢ 𝒜ᵢ` is of the form `φ' ∘ πᵢ` for
some `i` and nmiu-functional `φ'` on `𝒜ᵢ`.

*Hypothesis not used*: the proof never needs the summands to be von Neumann
algebras — normality of `φ` alone does the work (the `unusedSectionVars`
warning is left in place as the evidence).  The universe-polymorphic form is
`lp_nmiu_functional_factors` above; only that form applies to `ℓ^∞(X)`. -/
theorem nmiu_functional_product (φ : NMIUMap (lp 𝒜 ∞) ℂ) :
    ∃ (i : I) (φ' : NMIUMap (𝒜 i) ℂ), ∀ x : lp 𝒜 ∞, φ x = φ' (x i) :=
  lp_nmiu_functional_factors φ


/-- **122VI** (`cor:linf-ff`, proc.tex:4618, Exercise), part 1: the
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

/-- **122VI** (`cor:linf-ff`, proc.tex:4618, Exercise), part 2: the unit
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

/-- **122VI** (`cor:linf-ff`, proc.tex:4618, Exercise), part 3: the
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
coreflective subcategory of `(W*_miu)^op`.

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

/-- **122II** (`first-adjunction`, proc.tex:4499, Proposition), second
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

/-- **122VI** (`cor:linf-ff`, proc.tex:4618, Exercise), part 3, second
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

/-- **123I** (proc.tex:4634, Exercise), part 1: the indicator functions
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

/-- **123I** (proc.tex:4634, Exercise), part 2: the coordinate projections
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

/-- **123I** (proc.tex:4634, Exercise), part 3: the map
`⊗ : ℓ^∞(X) × ℓ^∞(Y) → ℓ^∞(X × Y)`, `(f ⊗ g)(x,y) = f(x)g(y)` is a
tensor product; whence `ℓ^∞(X × Y) ≅ ℓ^∞(X) ⊗ ℓ^∞(Y)` (and `ℓ^∞` is
strong monoidal).

The exercise's own route is followed: "**using this**, and
`tensor-characterization`" — `this` being parts 1 and 2.  Condition (1) of
**116VII** is part 1 `linf_generated`, applied to `X × Y`: the elementary
tensors `δ_x ⊗ δ_y` are exactly the `δ_{(x,y)}`, and those generate.
Condition (3) is part 2 `linf_projections_order_separating`, again applied
to `X × Y`: the product functionals are the point evaluations `π_{(x,y)}`,
they are order separating, and an order separating collection is centre
separating (take the conjugator `1`, and compare with `0`).  Only the two
*hypotheses* `Σ`, `Γ` of 116VII — that the point evaluations on `ℓ^∞(X)`
and on `ℓ^∞(Y)` are centre separating — are taken from **117II**.2
`sum_generation_2`, which states them in the form 116VII asks for.

The `Conclude that ℓ^∞(X × Y) ≅ ℓ^∞(X) ⊗ ℓ^∞(Y)` tail is not stated here
as an isomorphism; it is obtained where it is used (`Duplicators`'
`linf_nmiu_mul`) by feeding this into **114II** `tensor_uniqueness`.  The
parenthetical "(in fact, it follows that `ℓ^∞` is strong monoidal)" is not
formalized. -/
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
  · -- (1) the `δ_{(x,y)} = δ_x ⊗ δ_y` generate, by **part 1**
    have hsub : {f : linf (X × Y) | ∃ p : X × Y, f = lp.single ∞ p 1}
        ⊆ (tensorSpan γ hmiu : Set (linf (X × Y))) := by
      rintro x ⟨p, rfl⟩
      refine Submodule.subset_span ⟨lp.single ∞ p.1 1, lp.single ∞ p.2 1, ?_⟩
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
      rw [← linf_generated (X × Y)]
      exact wstar_mono hsub
    exact dense_of_wstar_eq_top _ htop
  · -- (2) the product functional of two point evaluations is a point evaluation
    rintro σ ⟨x, ω, hω, hσ⟩ τ ⟨y, ω', hω', hτ⟩
    obtain rfl : ω = Theses.A.VN.complexIdNP := hω
    obtain rfl : ω' = Theses.A.VN.complexIdNP := hω'
    refine ⟨lpNP (x, y) Theses.A.VN.complexIdNP, fun f g => ?_⟩
    rw [lp_infty_np_apply, hσ f, hτ g]
    rfl
  · -- (3) they are centre separating, by **part 2**
    rw [centreSeparatingConj_iff]
    intro a ha
    refine ⟨fun h ω _ b => by rw [h]; simp, fun H => ?_⟩
    have hzero : ∀ p : X × Y, ((a : ∀ _ : X × Y, ℂ) p) = 0 := by
      intro p
      have hmem : lpNP p Theses.A.VN.complexIdNP ∈
          {h : NPFunctional (linf (X × Y)) | ∃ σ ∈ Sg, ∃ τ ∈ Γ,
            ∀ (f : linf X) (g : linf Y), (h (γ f g) : ℂ) = σ f * τ g} := by
        refine ⟨lpNP p.1 Theses.A.VN.complexIdNP,
          ⟨p.1, Theses.A.VN.complexIdNP, rfl, fun u => rfl⟩,
          lpNP p.2 Theses.A.VN.complexIdNP,
          ⟨p.2, Theses.A.VN.complexIdNP, rfl, fun u => rfl⟩, fun f g => ?_⟩
        rfl
      have h1 := H _ hmem 1
      rw [show (star (1 : linf (X × Y)) * a * 1) = a by simp] at h1
      rw [lp_infty_np_apply] at h1
      exact h1
    have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
    have hle : a ≤ 0 :=
      linf_projections_order_separating (X × Y) a 0 hsa (IsSelfAdjoint.zero _)
        (fun p => by rw [hzero p]; simp)
    exact le_antisymm hle ha


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

/-- **123II** (proc.tex:4669, Exercise), part 1: an nmiu-functional `φ` on
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

/-- **123II** (proc.tex:4669, Exercise), part 2, well-definedness half:
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

/-- **123II** (proc.tex:4669, Exercise), part 2, as the Exercise states it:
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

/-- **124I** (`vn-generation-bound`, proc.tex:4694, Lemma): if a von
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

The bounded faithful representation of parsec **1250** is used by 125IV
`equaliser_lemma`, by `tensor_preimage`, by `exists_minimal_tensorSub` and by
`nmiu_ext_of_tensorBSurjective`, all below in this file: each of them
argues on a *concrete* Hilbert space carrying the tensored factor.  It is
stated here rather than in its own parsec because the cardinality
infrastructure its bound needs sits in this block, beside 124I.  Neither
solution set uses it: both relabel the algebra's **elements**
(`exists_vnOnSet` below), as proc.tex:4769 does. -/

variable (A) in
/-- **125II** (`vn-gns-bound`, proc.tex:4820, Lemma), bundled: a faithful
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
C*-algebra has at most `2^#𝒳` vectors (proc.tex:4820).  (125II is about von
Neumann algebras; the binders here are `CStarAlgebra` and `Nontrivial`, which
is all the cardinal count uses.) -/
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
/-- **125II** (`vn-gns-bound`, proc.tex:4820, Lemma): a von Neumann
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

One divergence from the printed proof, and it is forced.

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

The solution set is the printed one: proc.tex's "von Neumann algebras carried
on a subset of `κ`" with `κ = 2^{2^{𝔠+#𝒜}}`, rendered by `SolIdx` on top of
`VNOnSet`, with `exists_vnOnSet` supplying the relabelling.  The cardinal
bookkeeping is **124I** and nothing else; **125II** is not used here. -/

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

/-! #### Relabelling: the elements

This is what proc.tex:4769 does, and it is what *both* solution sets of this
file — 124III's `SolIdx` and 125VIII's `TSolIdx` — are built on: the index
datum is a von Neumann algebra *carried on a subset of `κ`*, so the
relabelling is of the **elements** of the algebra.  Mathlib has no
`Equiv.cstarAlgebra`, so the
C*-structure is carried along the relabelling bijection by hand
(`cstarTransport`, on top of `Equiv.normedRing`, `Equiv.algebra`,
`Equiv.starRing` and `Equiv.starModule`); the order needs no transport at
all, being the spectral order of the transported C*-structure, exactly as
for `lp _ ∞` (`A/VN/Basic.lean:860`); and Kadison's `VonNeumannAlgebra`
predicate transports by `vonNeumannAlgebra_of_starAlgEquiv`. -/

set_option warn.classDefReducibility false in
/-- A `CStarAlgebra` structure carried along an `Equiv`.  The two clauses
Mathlib's transfer instances do not cover are `CompleteSpace` — the
transported metric is `dist x y = dist (e x) (e y)` by definition, so `e` is
an isometry — and the C*-identity, immediate from
`e (star x * x) = star (e x) * e x`.  `NormedAlgebra` has to be given its
`Algebra` field explicitly: synthesising it produces a second, non-defeq
`Algebra ℂ α` and the `StarModule` clause then fails to typecheck. -/
@[reducible] private def cstarTransport {α β : Type u} [CStarAlgebra β]
    (e : α ≃ β) : CStarAlgebra α := by
  letI nr : NormedRing α := e.normedRing
  letI sr : StarRing α := e.starRing
  letI alg : Algebra ℂ α := e.algebra ℂ
  have hmul : ∀ x y : α, e (x * y) = e x * e y := fun _ _ => e.apply_symm_apply _
  have hstar : ∀ x : α, e (star x) = star (e x) := fun _ => e.apply_symm_apply _
  have hnorm : ∀ x : α, ‖x‖ = ‖e x‖ := fun _ => rfl
  have hsmul : ∀ (c : ℂ) (x : α), e (c • x) = c • e x :=
    fun _ _ => e.apply_symm_apply _
  haveI hc : CompleteSpace α :=
    (IsometryEquiv.mk e (Isometry.of_dist_eq fun _ _ => rfl)).completeSpace
  haveI hcs : CStarRing α := ⟨fun x => by
    rw [hnorm x, hnorm (star x * x), hmul, hstar, CStarRing.norm_star_mul_self]⟩
  letI hna : NormedAlgebra ℂ α :=
    { toAlgebra := alg
      norm_smul_le := fun c x => by
        rw [hnorm (c • x), hsmul, hnorm x]; exact norm_smul_le c (e x) }
  letI sm : StarModule ℂ α := e.starModule ℂ
  exact { }

/-- A von Neumann algebra **carried on a subset of `K`**: proc.tex:4752's
index datum.  The C*-structure and the order are data on `↥T`, Kadison's
condition (**42I**) is a field, and the whole thing lives in `Type u` — which
is what makes the solution set a set. -/
private structure VNOnSet (K : Type u) : Type u where
  T : Set K
  [cstar : CStarAlgebra ↥T]
  [po : PartialOrder ↥T]
  [sor : StarOrderedRing ↥T]
  vna : VonNeumannAlgebra ↥T

attribute [instance] VNOnSet.cstar VNOnSet.po VNOnSet.sor VNOnSet.vna

/-- **The relabelling step of 124III** (proc.tex:4769): a von Neumann algebra
with at most `#K` elements is ∗-isomorphic to one carried on a subset of `K`.
Inject `𝒳` into `K`, take the range, and carry the structure across
`Equiv.ofInjective`. -/
private theorem exists_vnOnSet (𝒳 : Type u) [CStarAlgebra 𝒳] [PartialOrder 𝒳]
    [StarOrderedRing 𝒳] [VonNeumannAlgebra 𝒳] {K : Type u} (h : #𝒳 ≤ #K) :
    ∃ V : VNOnSet K, Nonempty (𝒳 ≃⋆ₐ[ℂ] ↥V.T) := by
  obtain ⟨ι⟩ := (Cardinal.le_def 𝒳 K).mp h
  let e : ↥(Set.range ι) ≃ 𝒳 := (Equiv.ofInjective ι ι.injective).symm
  let ca : CStarAlgebra ↥(Set.range ι) := cstarTransport e
  let po : PartialOrder ↥(Set.range ι) := CStarAlgebra.spectralOrder _
  let sor : StarOrderedRing ↥(Set.range ι) := CStarAlgebra.spectralOrderedRing _
  have hadd : ∀ x y : ↥(Set.range ι), e (x + y) = e x + e y :=
    fun _ _ => e.apply_symm_apply _
  have hmul : ∀ x y : ↥(Set.range ι), e (x * y) = e x * e y :=
    fun _ _ => e.apply_symm_apply _
  have hstar : ∀ x : ↥(Set.range ι), e (star x) = star (e x) :=
    fun _ => e.apply_symm_apply _
  have hsmul : ∀ (c : ℂ) (x : ↥(Set.range ι)), e (c • x) = c • e x :=
    fun _ _ => e.apply_symm_apply _
  let Φ : 𝒳 ≃⋆ₐ[ℂ] ↥(Set.range ι) :=
    { toFun := e.symm
      invFun := e
      left_inv := e.apply_symm_apply
      right_inv := e.symm_apply_apply
      map_add' := fun x y => e.injective (by
        rw [hadd, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply])
      map_mul' := fun x y => e.injective (by
        rw [hmul, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply])
      map_smul' := fun c x => e.injective (by
        rw [hsmul, e.apply_symm_apply, e.apply_symm_apply])
      map_star' := fun x => e.injective (by
        rw [hstar, e.apply_symm_apply, e.apply_symm_apply]) }
  have hvna : VonNeumannAlgebra ↥(Set.range ι) := vonNeumannAlgebra_of_starAlgEquiv Φ
  exact ⟨{ T := Set.range ι, vna := hvna }, ⟨Φ⟩⟩

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

/-- The index of the solution set of **124III**, proc.tex:4752 on the nose: a
von Neumann algebra carried on a subset `T` of the fixed index type `K`,
together with an ncpsu-map into it from `𝒜`.  It lives in `Type u` — which is
the whole point of the solution set condition. -/
private structure SolIdx (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (K : Type u) extends VNOnSet K where
  hnt : Nontrivial ↥T
  γ : NCPSUMap A ↥T

/-- **The solution set condition** (proc.tex:4718): every ncpsu-map from `𝒜`
into a *nontrivial* von Neumann algebra factors as an nmiu-map after one of
the `γᵢ`.  The algebra `ℬ' = W*(f(𝒜))` has at most `2^{2^{𝔠+#𝒜}} = #K`
elements by **124I** — applicable because `vnsub_wstar_eq_top` says `ℬ'`, as
an algebra, is generated by `f(𝒜)` — and `exists_vnOnSet` then relabels its
elements by a subset of `K`, which is proc.tex:4769.  (The trivial target is
handled separately, in 124III itself: the product of **47IV** needs every
factor nontrivial.) -/
private theorem solution_set (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] {K : Type u}
    (hK : #K = (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      (Cardinal.continuum + #A))
    {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [VonNeumannAlgebra B] [Nontrivial B] (f : NCPSUMap A B) :
    ∃ (i : SolIdx A K) (h : NMIUMap ↥i.T B),
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
  obtain ⟨V, ⟨Φ⟩⟩ :=
    exists_vnOnSet (K := K) (VNSub B (wstar B G) hw.1) (by rw [hK]; exact hcard)
  have hntB' : Nontrivial (VNSub B (wstar B G) hw.1) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg VNSub.val h)⟩⟩
  -- `ε` is introduced by `obtain`, not by `let`: `nmiuSymm_apply_apply` will
  -- not rewrite through a let-bound nmiu-map whose bijectivity is recorded
  -- against the underlying `≃⋆ₐ` instead of against `ε` itself.
  obtain ⟨ε, hεbij⟩ : ∃ ε : NMIUMap (VNSub B (wstar B G) hw.1) ↥V.T,
      Function.Bijective ⇑ε :=
    ⟨⟨Φ.toStarAlgHom, starAlgEquiv_preservesDirSups' Φ⟩, Φ.bijective⟩
  have hntS : Nontrivial ↥V.T :=
    ⟨⟨ε 1, ε 0, fun h => one_ne_zero (hεbij.1 h)⟩⟩
  refine ⟨⟨V, hntS, ncpsuCompNmiu ε f'⟩,
    nmiuComp VNSub.valNMIU (nmiuSymm ε hεbij), fun a => ?_⟩
  show VNSub.valNMIU (nmiuSymm ε hεbij
    ((ncpsuCompNmiu ε f').toNCPMap a)) = f.toNCPMap a
  rw [ncpsuCompNmiu_apply, nmiuSymm_apply_apply]
  exact hf' a

private instance solNontrivial {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {K : Type u} (i : SolIdx A K) :
    Nontrivial ↥i.T := i.hnt

/-- The product `∏ᵢ 𝒞ᵢ` over the solution set (**47IV**). -/
@[reducible] private def solProd (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) : Type u :=
  lp (fun i : SolIdx A K => ↥i.T) ∞

end SecondAdjunction


variable (A) in
/-- **124III** (`second-adjunction`, proc.tex:4724, Theorem), bundled: a
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
/-- **124III** (`second-adjunction`, proc.tex:4724, Theorem): the
inclusion `W*_miu → W*_cpsu` has a left adjoint `F` — rendered: every von
Neumann algebra has a universal arrow to the inclusion. -/
theorem second_adjunction [VonNeumannAlgebra A] : Nonempty (FreeMIU A) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : Type u, #K = (2 : Cardinal.{u}) ^
      (2 : Cardinal.{u}) ^ (Cardinal.continuum + #A) := ⟨_, Cardinal.mk_out _⟩
  obtain ⟨η, hη, -⟩ := vn_products_ncpsu
    (fun i : SolIdx A K => (↥i.T : Type u)) (fun i => i.γ)
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
          (fun j : SolIdx A K => (↥j.T : Type u)) i⟩)
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
this parsec, beside the cardinality infrastructure their bound needs; their
consumers are 125IV `equaliser_lemma` and the `tensorSub` lemmas below in
this file.) -/

/- **125IV** (`equaliser-lemma`, proc.tex:4852, Lemma (Kornell)) is
`equaliser_lemma`, below in this file: its proof needs the
two-sided abstract form of 121II, and hence `tensorSub₂`, which is only
available there. -/

/-- **125VI** (`tensor-equalisers`, proc.tex:4978, Proposition),
definition part: `e : ℰ → 𝒜` is an **equaliser** of nmiu-maps
`f, g : 𝒜 → ℬ` when `f ∘ e = g ∘ e` and every nmiu-map `h` with
`f ∘ h = g ∘ h` factors uniquely through `e`. -/
def IsNMIUEqualizer {E : Type u} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (f g : NMIUMap A B) (e : NMIUMap E A) : Prop :=
  (∀ x : E, f (e x) = g (e x)) ∧
    ∀ (D' : Type u) [CStarAlgebra D'] [PartialOrder D']
      [StarOrderedRing D'] [VonNeumannAlgebra D'] (h : NMIUMap D' A),
      (∀ d, f (h d) = g (h d)) → ∃! k : NMIUMap D' E, ∀ d, h d = e (k d)

/- **125VI** (`tensor-equalisers`, proc.tex:4978, Proposition) is
`tensor_equalisers`, below in this file: its proof consumes 125IV
`equaliser_lemma`, which is stated there. -/

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

/- **125VIIb** (`tensor-preimage`, proc.tex:5031, Exercise) is
`tensor_preimage`, below in this file: its proof consumes the
slice-map property, i.e. 121II, through `EqL`'s `mem_tensorSub_of_image`. -/

/-- **125VIII** (`tensor-closed`, proc.tex:5054, Theorem (Kornell)),
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

/- **125VIII** (`tensor-closed`, proc.tex:5054, Theorem (Kornell)) is
`tensor_closed`, below in this file: its proof consumes 125IV
`equaliser_lemma`. -/

/- **125X** (`cstar-no-model`, proc.tex:5111, Remark): no analogous free
exponential exists for C*-algebras — remark, not converted. -/

/-! ## Parsecs 1251–1252: the hereditarily atomic second adjunction -/

variable (A) in
/-- **125bII** (proc.tex:5246, Proposition), bundled: a universal arrow
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
down to the *hereditarily atomic* targets, which is proc.tex:5276's
"the ncpsu-maps `γ : 𝒜 → 𝒞` for which `𝒞` is a *hereditarily atomic* von
Neumann algebra **on a subset of the cardinal** `κ = 2^(2^(𝔠+#𝒜))`".

`HaSolIdx` is therefore 124III's `SolIdx` with one extra field, the
hereditary atomicity of the carrier: the same `VNOnSet` relabelling of the
**elements** by `exists_vnOnSet`, which is proc.tex:4769; the same `κ`; and
the same `Nontrivial` side condition, which **47IV** needs of the factors
of a product and which 124III's proof splits the trivial target off for.
Hereditary atomicity survives the relabelling because it is preserved by an
injective nmiu-map (**84bIII** `hereditarilyAtomic_subalgebra`).

The one thing the hereditarily atomic setting has to supply that 124III
does not is proc.tex:5262's *"`haW*_miu` is closed under products"*: the
product `⊕ᵢ 𝒞ᵢ` over the solution set must itself be hereditarily atomic.
That is `hereditarilyAtomic_lp` below — the flattening isomorphism
`⊕ᵢ (⊕_{j ∈ Jᵢ} M_{Nᵢⱼ+1}) ≅ ⊕_{(i,j)} M_{Nᵢⱼ+1}`, built in both directions
out of **47IV**.

`ha_second_adjunction` does **not** use `hA`, and cannot: the carrier is a
von Neumann subalgebra of a product of hereditarily atomic algebras
whatever `𝒜` is, so `F_ha` exists for *every* von Neumann algebra.  The
hypothesis is kept because the thesis states the adjunction with
`haW*_cpsu` as its domain. -/

section HaSecondAdjunction

universe u₁ u₂ u₃ u₄

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
  [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]

/-! #### Helpers shared with 125cIII

The next three declarations were written for `Fha_concrete` (125cIII,
"helpers 4 and 5" of the `FhaAux` block below); `lpEvalNMIU` is used again
here, by `hereditarilyAtomic_lp` and by the product over the solution set.
They live at this point in the file only because 125bII comes first. -/

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

set_option maxHeartbeats 1000000 in
/-- **proc.tex:5262**: `haW*_miu` is closed under products — an `ℓ^∞`-sum
of hereditarily atomic von Neumann algebras is hereditarily atomic.

The flattening isomorphism `⊕ᵢ (⊕_{j ∈ Jᵢ} M_{Nᵢⱼ+1}) ≅ ⊕_{(i,j)} M_{Nᵢⱼ+1}`,
whose index type is the `Σ`-type of pairs (summand of the sum, summand of
that summand).  Both directions are **47IV** `vn_products_nmiu`: `Θ` has
coordinates `x ↦ Ψᵢ(xᵢ)ⱼ` and `Λ` has coordinates `z ↦ Ψᵢ⁻¹(j ↦ z₍ᵢ,ⱼ₎)`,
the inner family of the latter being a second application of 47IV; the two
composites are the identity coordinatewise. -/
private theorem hereditarilyAtomic_lp {I : Type u} (𝒞 : I → Type u)
    [∀ i, CStarAlgebra (𝒞 i)] [∀ i, Nontrivial (𝒞 i)] [∀ i, PartialOrder (𝒞 i)]
    [∀ i, StarOrderedRing (𝒞 i)] [∀ i, VonNeumannAlgebra (𝒞 i)]
    (h : ∀ i, HereditarilyAtomic (𝒞 i)) : HereditarilyAtomic (lp 𝒞 ∞) := by
  classical
  choose J N hΨ using h
  have Ψ : ∀ i, 𝒞 i ≃⋆ₐ[ℂ] lp (fun j : J i => HaMat (N i j)) ∞ :=
    fun i => (hΨ i).some
  have hntl : ∀ i, Nontrivial (lp (fun j : J i => HaMat (N i j)) ∞) :=
    fun i => (Ψ i).injective.nontrivial
  obtain ⟨Ψ', hΨ'bij⟩ :
      ∃ Ψ' : ∀ i, NMIUMap (𝒞 i) (lp (fun j : J i => HaMat (N i j)) ∞),
        ∀ i, Function.Bijective ⇑(Ψ' i) :=
    ⟨fun i => ⟨(Ψ i).toStarAlgHom, starAlgEquiv_preservesDirSups' (Ψ i)⟩,
      fun i => (Ψ i).bijective⟩
  obtain ⟨Θ, hΘ, -⟩ := vn_products_nmiu (B := lp 𝒞 ∞)
    (fun p : Σ i : I, J i => HaMat (N p.1 p.2))
    (fun p => nmiuComp (lpEvalNMIU (fun j : J p.1 => HaMat (N p.1 j)) p.2)
      (nmiuComp (Ψ' p.1) (lpEvalNMIU 𝒞 p.1)))
  have hΘa : ∀ (x : lp 𝒞 ∞) (i : I) (j : J i),
      ((Θ x : lp (fun q : Σ i : I, J i => HaMat (N q.1 q.2)) ∞) :
          ∀ q : Σ i : I, J i, HaMat (N q.1 q.2)) ⟨i, j⟩
        = ((Ψ' i ((x : ∀ i', 𝒞 i') i) : lp (fun j' : J i => HaMat (N i j')) ∞) :
              ∀ j' : J i, HaMat (N i j')) j := fun x i j => hΘ ⟨i, j⟩ x
  have hGi : ∀ i : I, ∃ g : NMIUMap (lp (fun p : Σ i : I, J i =>
        HaMat (N p.1 p.2)) ∞) (lp (fun j : J i => HaMat (N i j)) ∞),
      ∀ (j : J i) (z : lp (fun p : Σ i : I, J i => HaMat (N p.1 p.2)) ∞),
        ((g z : lp (fun j' : J i => HaMat (N i j')) ∞) :
            ∀ j' : J i, HaMat (N i j')) j
          = (z : ∀ p : Σ i : I, J i, HaMat (N p.1 p.2)) ⟨i, j⟩ := by
    intro i
    obtain ⟨g, hg, -⟩ := vn_products_nmiu (fun j : J i => HaMat (N i j))
      (fun j => lpEvalNMIU (fun p : Σ i : I, J i => HaMat (N p.1 p.2)) ⟨i, j⟩)
    exact ⟨g, fun j z => hg j z⟩
  choose Gi hGia using hGi
  obtain ⟨Λ, hΛ, -⟩ := vn_products_nmiu (B := lp (fun p : Σ i : I, J i =>
      HaMat (N p.1 p.2)) ∞) 𝒞
    (fun i => nmiuComp (nmiuSymm (Ψ' i) (hΨ'bij i)) (Gi i))
  have hΛa : ∀ (z : lp (fun p : Σ i : I, J i => HaMat (N p.1 p.2)) ∞) (i : I),
      ((Λ z : lp 𝒞 ∞) : ∀ i', 𝒞 i') i
        = nmiuSymm (Ψ' i) (hΨ'bij i) (Gi i z) := fun z i => hΛ i z
  have hΘΛ : ∀ z, Θ (Λ z) = z := by
    intro z
    refine lp.ext (funext ?_)
    rintro ⟨i, j⟩
    rw [hΘa, hΛa, nmiuSymm_apply_apply', hGia]
  have hΛΘ : ∀ x, Λ (Θ x) = x := by
    intro x
    refine lp.ext (funext fun i => ?_)
    rw [hΛa]
    have hcoord : Gi i (Θ x) = Ψ' i ((x : ∀ i', 𝒞 i') i) := by
      refine lp.ext (funext fun j => ?_)
      rw [hGia, hΘa]
    rw [hcoord, nmiuSymm_apply_apply]
  exact ⟨Σ i : I, J i, fun p => N p.1 p.2,
    ⟨StarAlgEquiv.ofBijective Θ.toStarAlgHom
      ⟨fun x y hxy => by rw [← hΛΘ x, ← hΛΘ y]; exact congrArg _ hxy,
        fun z => ⟨Λ z, hΘΛ z⟩⟩⟩⟩

/-- The index of the solution set of **125bII**, proc.tex:5276 on the nose:
a *hereditarily atomic* von Neumann algebra carried on a subset `T` of the
fixed index type `K`, together with an ncpsu-map into it from `𝒜`.  It is
124III's `SolIdx` with the single extra field `ha`. -/
private structure HaSolIdx (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (K : Type u) extends VNOnSet K where
  hnt : Nontrivial ↥T
  ha : HereditarilyAtomic ↥T
  γ : NCPSUMap A ↥T

private instance haSolNontrivial {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {K : Type u} (i : HaSolIdx A K) :
    Nontrivial ↥i.T := i.hnt

/-- The algebra of a solution-set entry. -/
@[reducible] private def HaSolAlg {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {K : Type u} (i : HaSolIdx A K) :
    Type u :=
  ↥i.T

/-- The product `∏ᵢ 𝒞ᵢ` over the solution set (**47IV**). -/
@[reducible] private def haSolProd (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) : Type u :=
  lp (fun i : HaSolIdx A K => (↥i.T : Type u)) ∞

/-- proc.tex:5262's "a direct sum of hereditarily atomic algebras is
hereditarily atomic", applied to the solution set. -/
private theorem hereditarilyAtomic_haSolProd (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (K : Type u) :
    HereditarilyAtomic (haSolProd A K) :=
  hereditarilyAtomic_lp (fun i : HaSolIdx A K => (↥i.T : Type u))
    (fun i => i.ha)

/-- The projection of the product onto a single solution-set entry:
**47IV** again. -/
private theorem exists_haBlockProj (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] {K : Type u}
    (i : HaSolIdx A K) :
    ∃ pr : NMIUMap (haSolProd A K) (HaSolAlg i),
      ∀ x : haSolProd A K,
        pr x = (x : ∀ j : HaSolIdx A K, (↥j.T : Type u)) i :=
  ⟨lpEvalNMIU (fun j : HaSolIdx A K => (↥j.T : Type u)) i, fun _ => rfl⟩

/-- **The solution set condition for 125bII** (proc.tex:5262): every
ncpsu-map from `𝒜` into a *hereditarily atomic* von Neumann algebra factors
as an nmiu-map after one of the `γᵢ`.  The algebra `ℬ' = W*(f(𝒜))` is
hereditarily atomic by **84bIII** and has at most `2^(2^(𝔠+#𝒜))` elements by
**124I**; `exists_vnOnSet` then relabels its elements by a subset of `K`,
which is proc.tex:4769, and **84bIII** carries hereditary atomicity across
the relabelling.  (The trivial target is handled separately, in 125bII itself:
the product of **47IV** needs every factor nontrivial.) -/
private theorem ha_solution_set (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] {K : Type u}
    (hK : #K = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (Cardinal.continuum + #A)))
    {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [VonNeumannAlgebra B] [Nontrivial B] (hB : HereditarilyAtomic B)
    (f : NCPSUMap A B) :
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
  obtain ⟨V, ⟨Φ⟩⟩ :=
    exists_vnOnSet (K := K) (VNSub B (wstar B G) hw.1) (by rw [hK]; exact hcard)
  have hntB' : Nontrivial (VNSub B (wstar B G) hw.1) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg VNSub.val h)⟩⟩
  obtain ⟨ε, hεbij⟩ : ∃ ε : NMIUMap (VNSub B (wstar B G) hw.1) ↥V.T,
      Function.Bijective ⇑ε :=
    ⟨⟨Φ.toStarAlgHom, starAlgEquiv_preservesDirSups' Φ⟩, Φ.bijective⟩
  have hntS : Nontrivial ↥V.T :=
    ⟨⟨ε 1, ε 0, fun h => one_ne_zero (hεbij.1 h)⟩⟩
  have haT : HereditarilyAtomic ↥V.T :=
    hereditarilyAtomic_subalgebra hB' (nmiuSymm ε hεbij)
      (nmiuSymm_bijective ε hεbij).1
  refine ⟨⟨V, hntS, haT, ncpsuCompNmiu ε f'⟩,
    nmiuComp VNSub.valNMIU (nmiuSymm ε hεbij), fun a => ?_⟩
  show VNSub.valNMIU (nmiuSymm ε hεbij
    ((ncpsuCompNmiu ε f').toNCPMap a)) = f.toNCPMap a
  rw [ncpsuCompNmiu_apply, nmiuSymm_apply_apply]
  exact hf' a

end HaSecondAdjunction


set_option maxHeartbeats 1000000 in
variable (A) in
/-- **125bII** (proc.tex:5246, Proposition): the inclusion
`haW*_miu → haW*_cpsu` has a left adjoint `F_ha`.

Freyd, exactly as in 124III `second_adjunction`: `F_ha(𝒜)` is the von
Neumann subalgebra of the product over the solution set generated by the
range of the mediating map `η`.  Existence of the factorisation is weak
initiality of the product (`ha_solution_set` followed by the block
projection); uniqueness is **47V** `vn_equalisers` together with
`vnsub_wstar_eq_top`.  Hereditary atomicity of the carrier is **84bIII**
applied to `hereditarilyAtomic_haSolProd`, which is proc.tex:5262's
"`haW*_miu` is closed under products".  The trivial target is split off
first, exactly as in 124III: **47IV** needs the factors nontrivial.

`hA` is not used; see the note above `section HaSecondAdjunction`. -/
theorem ha_second_adjunction [VonNeumannAlgebra A]
    (hA : HereditarilyAtomic A) : Nonempty (HaFreeMIU A) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : Type u, #K = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
      (Cardinal.continuum + #A)) := ⟨_, Cardinal.mk_out _⟩
  obtain ⟨η, hη, -⟩ := vn_products_ncpsu
    (fun i : HaSolIdx A K => (↥i.T : Type u)) (fun i => i.γ)
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
  -- weak initiality: factor through the solution set, then block-project
  obtain ⟨i, h, hh⟩ := ha_solution_set A hK hB f
  obtain ⟨pr, hpr⟩ := exists_haBlockProj A i
  obtain ⟨g, hgeq⟩ : ∃ g : NMIUMap (VNSub (haSolProd A K)
        (wstar (haSolProd A K) (Set.range (fun a : A => η.toNCPMap a))) hw.1) B,
      ∀ x, g x = h (pr x.val) :=
    ⟨nmiuComp h (nmiuComp pr VNSub.valNMIU), fun _ => rfl⟩
  have hprη : ∀ a : A, pr (η.toNCPMap a) = (i.γ).toNCPMap a := by
    intro a
    rw [hpr]
    exact hη i a
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
independent obligation.  (Note the `PartialOrder` above is the same
spectral order that `mn_vna_1` is stated against, so the two agree
definitionally.) -/
instance (n : ℕ) : VonNeumannAlgebra (MatAlg n) := Theses.A.VN.mn_vna_1 n

/-- **125cII** (proc.tex:5290): two ncpsu-maps
`f₁ : 𝒜 → M_{n₁}`, `f₂ : 𝒜 → M_{n₂}` are **miu-equivalent** when there
is an nmiu-isomorphism `φ : M_{n₁} → M_{n₂}` with `φ ∘ f₁ = f₂`. -/
def MIUEquiv {n₁ n₂ : ℕ} (f₁ : NCPSUMap A (MatAlg n₁))
    (f₂ : NCPSUMap A (MatAlg n₂)) : Prop :=
  ∃ φ : NMIUMap (MatAlg n₁) (MatAlg n₂), Function.Bijective ⇑φ ∧
    ∀ a : A, φ (f₁.toNCPMap a) = f₂.toNCPMap a

/-- **125cII** (proc.tex:5290): the maps considered in the concrete
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

/-- **125cIII** (`Fha-concrete`, proc.tex:5306, Theorem): for a
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

For **hereditarily atomic** `𝒜 ≅ ⊕_{j∈J} M_{n_j+1}`
(**84bII**) and *any* von Neumann algebra `𝒞`, every `x ∈ 𝒞 ⊗ 𝒜` has, in
each block `j`, a **finite** matrix of entries `c^j_{kl} ∈ 𝒞`:

> `(1 ⊗ z_j)·x  =  ∑_{k,l} (c^j_{kl} ⊗ 1)·(1 ⊗ u^j_{kl})`.

This is the elementary substitute, available only in the hereditarily
atomic case, for Tomiyama's slice-map property — which in general is
equivalent to the commutation theorem `(M ⊗̄ N)' = M' ⊗̄ N'` and hence out
of reach here.

The entry extraction stays inside `Type u`: it never slices into `ℂ`.
`haE j k l x := (id ⊗ κ_j)((1⊗u^j_{0k})·x·(1⊗u^j_{l0}))`, where `κ_j` is
the ncp-map `a ↦ ω_j(a)·1` of the np-functional `ω_j(a) = (a_j)_{00}`, and
`haE j k l` lands in the range of the nmiu-map `c ↦ c ⊗ 1` (`nmiuTmulLeft`),
which is a von Neumann subalgebra by **69IVb** `nmiu_image` and hence
ultraweakly closed by **75VIII** `vnsac`.  Agreement on elementary tensors
plus `tensor_linear_ext` (108II(1)) does the rest.

`npScalarP`/`npScalar` supply the `NPFunctional → NCPMap` the rest of the
tree does not have.  Complete positivity is **34IX**
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

The continuation of the slice device.  `haApprox` is the
ultraweak approximation step (`∑_{j∈F} z_j ↑ 1`, **44VI**
`vna_supremum_uwlimit`, with `vnsac` supplying *ultraweak* closedness of a
von Neumann subalgebra — `IsVNSubalgebra` only carries norm closedness).
`haMem` and `haE_of_mem` are the two halves of the hereditarily atomic
slice-map property, and `haTensorPreimage`/`haTensorBSurj` are the private
ha forms of **125VIIb** `tensor_preimage` and **125eIII**
`tensorBsurjectivity`.  They do *not* close those two statements, which are
stated for arbitrary second factors; the general versions stand below, after
the 125IV apparatus, and go through the commutation theorem.  Since that
apparatus now precedes parsec 1255, `haTensorPreimage` has no consumer left:
`haTensorBSurj` cites the general 125eIII. -/

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

/-- **125dII** (proc.tex:5534, Proposition), bundled: a universal arrow
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
`vn_generation_bound`, the index type `K`, `exists_vnOnSet` — is not
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
/-- **125dII** (proc.tex:5534, Proposition): for hereditarily atomic `𝒜`
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

/-- **125eII** (proc.tex:5563, Definition): an nmiu-map
`s : 𝒜 → 𝒞 ⊗ ℬ` is **`(·) ⊗ ℬ`-surjective** when the only von Neumann
subalgebra `𝒮 ⊆ 𝒞` with `s(𝒜) ⊆ 𝒮 ⊗ ℬ` is `𝒮 = 𝒞`. -/
def TensorBSurjective (s : NMIUMap 𝒜 (VNT 𝒞 ℬ)) : Prop :=
  ∀ S : StarSubalgebra ℂ 𝒞, IsVNSubalgebra 𝒞 S →
    Set.range ⇑s ⊆ (tensorSub ℬ S : Set (VNT 𝒞 ℬ)) → S = ⊤

end TensorBSurj

/-! # Parsec 1254–1255, widened: atomic type I second factors

The `haE` device of the previous sections runs on
`𝒜 ≅ ⊕ⱼ M_{nⱼ+1}` (**84bII** `HereditarilyAtomic`).  Everything below is
the same device with the summands widened from `M_{nⱼ}` to `B(𝒦ⱼ)` for
*arbitrary* nonzero Hilbert spaces `𝒦ⱼ` — the **atomic type I** von
Neumann algebras, `AtomicTypeIRep` / `AtomicTypeI` below.

The one genuinely new ingredient is convergence.  Finite dimensionally
`∑_{p} u_{pp} = 1` on the nose, so the block expansion
`z_j·x = ∑_{k,l} E_{kl}(x)·(1 ⊗ u_{kl})` is a finite identity and the only
limit taken is over `Finset J` (`haApprox`).  For `dim 𝒦ⱼ = ∞` the partial
sums `p_F = ∑_{p ∈ F} u_{pp}` merely *increase to* `1` (Parseval,
`bkP_isLUB`), the expansion becomes the two-sided compression
`(1 ⊗ p_F)·x·(1 ⊗ p_F) = ∑_{k,l ∈ F} E_{kl}(x)·(1 ⊗ u_{kl})`, and one has
to pass to the limit in a *product*.  Ultraweak convergence `p_F → 1` does
not survive multiplication, but for a monotone net of **projections** the
Cauchy–Schwarz inequality **43I**.1 does the job in four lines:
`|ω(z x z − p x p)| ≤ (‖(zx)*‖_ω + ‖x‖·ω(z)^{1/2})·ω(z − p)^{1/2} → 0`
(`uw_compress_tendsto`).  That is the whole of the difference: no other new
mathematics is needed.

Delivered: the widened slice `atE`, both halves of the slice-map property
(`atMem`, `atE_of_mem`), and the widened `haTensorPreimage` /
`haTensorBSurj` — packaged as the public `atomicTypeI_tensor_preimage`
(125VIIb for atomic type I `𝒜`) and `atomicTypeI_tensorBsurjectivity`
(125eIII for atomic type I `ℬ`, **both** directions).  None of this closes
121II or any of its followers: those are general in exactly the slot that
has to be atomic here (see `docs/COMMUTATION-THEOREM.md` §2). -/

/-! ## Atomic type I: the matrix units of `B(𝒦)` -/

section BKUnits

variable {ι : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

private theorem conj_mul_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

private theorem hb_inner_self (e : HilbertBasis ι ℂ K) (o : ι) :
    (⟪e o, e o⟫ : ℂ) = 1 := by
  classical
  have h := (orthonormal_iff_ite.mp e.orthonormal) o o
  simpa using h

private theorem hb_inner_ne (e : HilbertBasis ι ℂ K) {k l : ι} (h : k ≠ l) :
    (⟪e k, e l⟫ : ℂ) = 0 := by
  classical
  have h2 := (orthonormal_iff_ite.mp e.orthonormal) k l
  simpa [h] using h2

/-- The matrix unit `|e_k⟩⟨e_l|` of `B(𝒦)` against a Hilbert basis `e`. -/
def bkU (e : HilbertBasis ι ℂ K) (k l : ι) : K →L[ℂ] K :=
  (innerSL ℂ (e l)).smulRight (e k)

theorem bkU_apply (e : HilbertBasis ι ℂ K) (k l : ι) (x : K) :
    bkU e k l x = (⟪e l, x⟫ : ℂ) • e k := rfl

theorem bkU_star (e : HilbertBasis ι ℂ K) (k l : ι) :
    star (bkU e k l) = bkU e l k := by
  have h : bkU e l k = ContinuousLinearMap.adjoint (bkU e k l) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro u v
    rw [bkU_apply, bkU_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  rw [h]
  rfl

theorem bkU_mul_mul (e : HilbertBasis ι ℂ K) (o k l : ι) (T : K →L[ℂ] K) :
    bkU e o k * T * bkU e l o = (⟪e k, T (e l)⟫ : ℂ) • bkU e o o := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hl : bkU e l o x = (⟪e o, x⟫ : ℂ) • e l := rfl
  show bkU e o k (T (bkU e l o x)) = ((⟪e k, T (e l)⟫ : ℂ) • bkU e o o) x
  rw [hl, map_smul, bkU_apply, inner_smul_right, smul_apply,
    bkU_apply, smul_smul, mul_comm]

theorem bkU_mul_mul' (e : HilbertBasis ι ℂ K) (k l : ι) (T : K →L[ℂ] K) :
    bkU e k k * T * bkU e l l = (⟪e k, T (e l)⟫ : ℂ) • bkU e k l := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hl : bkU e l l x = (⟪e l, x⟫ : ℂ) • e l := rfl
  show bkU e k k (T (bkU e l l x)) = ((⟪e k, T (e l)⟫ : ℂ) • bkU e k l) x
  rw [hl, map_smul, bkU_apply, inner_smul_right, smul_apply,
    bkU_apply, smul_smul, mul_comm]

theorem bkU_diag_inner (e : HilbertBasis ι ℂ K) (o : ι) :
    (⟪e o, (bkU e o o) (e o)⟫ : ℂ) = 1 := by
  rw [bkU_apply, inner_smul_right, hb_inner_self, mul_one]

/-- The finite-rank projection `∑_{k ∈ F} |e_k⟩⟨e_k|`. -/
def bkP (e : HilbertBasis ι ℂ K) (F : Finset ι) : K →L[ℂ] K := ∑ k ∈ F, bkU e k k

@[simp] theorem bkP_empty (e : HilbertBasis ι ℂ K) : bkP e ∅ = 0 := rfl

theorem bkP_star (e : HilbertBasis ι ℂ K) (F : Finset ι) :
    star (bkP e F) = bkP e F := by
  rw [bkP, star_sum]
  exact Finset.sum_congr rfl fun k _ => bkU_star e k k

theorem bkU_diag_mul_self (e : HilbertBasis ι ℂ K) (k : ι) :
    bkU e k k * bkU e k k = bkU e k k := by
  have h := bkU_mul_mul' e k k (1 : K →L[ℂ] K)
  rw [mul_one, show ((1 : K →L[ℂ] K) (e k)) = e k from rfl, hb_inner_self,
    one_smul] at h
  exact h

theorem bkU_diag_mul_ne (e : HilbertBasis ι ℂ K) {k l : ι} (h : k ≠ l) :
    bkU e k k * bkU e l l = 0 := by
  have h2 := bkU_mul_mul' e k l (1 : K →L[ℂ] K)
  rw [mul_one, show ((1 : K →L[ℂ] K) (e l)) = e l from rfl, hb_inner_ne e h,
    zero_smul] at h2
  exact h2

theorem bkP_mul_self (e : HilbertBasis ι ℂ K) (F : Finset ι) :
    bkP e F * bkP e F = bkP e F := by
  classical
  rw [bkP, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · exact bkU_diag_mul_self e k
  · intro l _ hlk
    exact bkU_diag_mul_ne e (Ne.symm hlk)
  · intro h; exact absurd hk h

theorem bkP_nonneg (e : HilbertBasis ι ℂ K) (F : Finset ι) : 0 ≤ bkP e F := by
  have h : bkP e F = star (bkP e F) * bkP e F := by
    rw [bkP_star, bkP_mul_self]
  rw [h]
  exact star_mul_self_nonneg _

theorem bkP_mono (e : HilbertBasis ι ℂ K) {F G : Finset ι} (h : F ⊆ G) :
    bkP e F ≤ bkP e G := by
  classical
  have hsd : bkP e G - bkP e F = bkP e (G \ F) := by
    have hs : (∑ k ∈ G \ F, bkU e k k) + (∑ k ∈ F, bkU e k k)
        = ∑ k ∈ G, bkU e k k := Finset.sum_sdiff h
    show (∑ k ∈ G, bkU e k k) - (∑ k ∈ F, bkU e k k) = ∑ k ∈ G \ F, bkU e k k
    rw [← hs]; abel
  rw [← sub_nonneg, hsd]
  exact bkP_nonneg e _

theorem bkP_le_one (e : HilbertBasis ι ℂ K) (F : Finset ι) :
    bkP e F ≤ 1 := by
  rw [← sub_nonneg]
  have hsa : star ((1 : K →L[ℂ] K) - bkP e F) = 1 - bkP e F := by
    rw [star_sub, star_one, bkP_star]
  have hid : ((1 : K →L[ℂ] K) - bkP e F) * (1 - bkP e F) = 1 - bkP e F := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, bkP_mul_self]
    abel
  have h : (1 : K →L[ℂ] K) - bkP e F = star (1 - bkP e F) * (1 - bkP e F) := by
    rw [hsa, hid]
  rw [h]
  exact star_mul_self_nonneg _

theorem bkP_mul_mul (e : HilbertBasis ι ℂ K) (F : Finset ι) (T : K →L[ℂ] K) :
    bkP e F * T * bkP e F
      = ∑ k ∈ F, ∑ l ∈ F, (⟪e k, T (e l)⟫ : ℂ) • bkU e k l := by
  have h : bkP e F * T * bkP e F
      = ∑ k ∈ F, ∑ l ∈ F, (bkU e k k * T * bkU e l l) := by
    rw [bkP, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
  rw [h]
  exact Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => bkU_mul_mul' e k l T

theorem inner_bkP_apply (e : HilbertBasis ι ℂ K) (F : Finset ι) (x : K) :
    (⟪x, bkP e F x⟫ : ℂ) = ∑ k ∈ F, (⟪x, e k⟫ : ℂ) * ⟪e k, x⟫ := by
  show (⟪x, (∑ k ∈ F, bkU e k k) x⟫ : ℂ) = _
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bkU_apply, inner_smul_right]
  ring

/-- `∑_{k ∈ F} |e_k⟩⟨e_k| ↑ 1`: the finite-rank projections attached to a
Hilbert basis have supremum `1` in `B(𝒦)`.  This is Parseval, and it is
where the infinite-dimensional slice device parts company with the
finite-dimensional one, where `∑_k u_{kk} = 1` holds *on the nose*. -/
theorem bkP_isLUB (e : HilbertBasis ι ℂ K) :
    IsLUB (Set.range (bkP e)) (1 : K →L[ℂ] K) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨F, rfl⟩; exact bkP_le_one e F
  · intro y hy
    have h0 : (0 : K →L[ℂ] K) ≤ y := by
      have h := hy ⟨∅, rfl⟩
      rwa [bkP_empty] at h
    rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
    have hysa : IsSelfAdjoint y := h0.isSelfAdjoint
    have hsub : IsSelfAdjoint (y - 1) := hysa.sub (IsSelfAdjoint.one _)
    have hsym : (↑(y - 1) : K →ₗ[ℂ] K).IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsub
    refine (ContinuousLinearMap.isPositive_iff_complex (y - 1)).mpr fun x => ?_
    have hreal : ((RCLike.re (⟪(y - 1) x, x⟫ : ℂ) : ℝ) : ℂ) = ⟪(y - 1) x, x⟫ := by
      have h := hsym x x
      have hc : (starRingEnd ℂ) (⟪(y - 1) x, x⟫ : ℂ) = ⟪(y - 1) x, x⟫ := by
        rw [inner_conj_symm]; exact h.symm
      have him : (⟪(y - 1) x, x⟫ : ℂ).im = 0 := Complex.conj_eq_iff_im.mp hc
      show ((((⟪(y - 1) x, x⟫ : ℂ).re : ℝ)) : ℂ) = _
      refine Complex.ext (Complex.ofReal_re _) ?_
      rw [Complex.ofReal_im]
      exact him.symm
    refine ⟨hreal, ?_⟩
    have hpar : HasSum (fun k : ι => ‖(⟪e k, x⟫ : ℂ)‖ ^ 2) ((⟪x, x⟫ : ℂ).re) := by
      have h := e.hasSum_inner_mul_inner x x
      have h2 := Complex.reCLM.hasSum h
      simp only [Complex.reCLM_apply] at h2
      refine h2.congr_fun fun k => ?_
      rw [show (⟪x, e k⟫ : ℂ) = (starRingEnd ℂ) (⟪e k, x⟫ : ℂ) from
        (inner_conj_symm x (e k)).symm, conj_mul_re]
    have hle : ∀ F : Finset ι, ∑ k ∈ F, ‖(⟪e k, x⟫ : ℂ)‖ ^ 2 ≤ (⟪x, y x⟫ : ℂ).re := by
      intro F
      have hmono := hy ⟨F, rfl⟩
      have hpos := (ContinuousLinearMap.isPositive_iff_complex (y - bkP e F)).mp
        ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hmono)) x
      have hexp : (⟪x, bkP e F x⟫ : ℂ).re = ∑ k ∈ F, ‖(⟪e k, x⟫ : ℂ)‖ ^ 2 := by
        rw [inner_bkP_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (⟪x, e k⟫ : ℂ) = (starRingEnd ℂ) (⟪e k, x⟫ : ℂ) from
          (inner_conj_symm x (e k)).symm, conj_mul_re]
      have hdiff : (⟪x, (y - bkP e F) x⟫ : ℂ).re
          = (⟪x, y x⟫ : ℂ).re - (⟪x, bkP e F x⟫ : ℂ).re := by
        rw [sub_apply, inner_sub_right, Complex.sub_re]
      have hswap : (⟪(y - bkP e F) x, x⟫ : ℂ).re = (⟪x, (y - bkP e F) x⟫ : ℂ).re := by
        rw [← inner_conj_symm x ((y - bkP e F) x), Complex.conj_re]
      have h3 := hpos.2
      rw [show (RCLike.re (⟪(y - bkP e F) x, x⟫ : ℂ)) = (⟪(y - bkP e F) x, x⟫ : ℂ).re from rfl,
        hswap, hdiff, hexp] at h3
      linarith
    have hxx : (⟪x, x⟫ : ℂ).re ≤ (⟪x, y x⟫ : ℂ).re := hasSum_le_of_sum_le hpar hle
    have hswap2 : (⟪(y - 1) x, x⟫ : ℂ).re = (⟪x, y x⟫ : ℂ).re - (⟪x, x⟫ : ℂ).re := by
      have hs : (⟪(y - 1) x, x⟫ : ℂ).re = (⟪x, (y - 1) x⟫ : ℂ).re := by
        rw [← inner_conj_symm x ((y - 1) x), Complex.conj_re]
      rw [hs, sub_apply, inner_sub_right, Complex.sub_re]
      rfl
    show (0:ℝ) ≤ RCLike.re (⟪(y - 1) x, x⟫ : ℂ)
    rw [show (RCLike.re (⟪(y - 1) x, x⟫ : ℂ)) = (⟪(y - 1) x, x⟫ : ℂ).re from rfl, hswap2]
    linarith

end BKUnits

/-! ## The generic direct-sum layer

`haZS`/`haApprox` above are stated for `⊕ⱼ M_{nⱼ+1}`, but their proofs use
nothing about the summands; the versions here are the same arguments for an
arbitrary family `𝒜`, together with the transported coprojection `gU` that
carries the block algebra `𝒜 j` into `A`. -/

section GenSum

set_option synthInstance.maxHeartbeats 400000

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C]
variable {J : Type u} {𝒜 : J → Type u} [∀ j, CStarAlgebra (𝒜 j)]
  [∀ j, Nontrivial (𝒜 j)] [∀ j, PartialOrder (𝒜 j)] [∀ j, StarOrderedRing (𝒜 j)]
  [∀ j, VonNeumannAlgebra (𝒜 j)]
  (Ψ : A ≃⋆ₐ[ℂ] lp 𝒜 ∞)

private theorem lpKappa_one_mul_right {I : Type*} {ℬ : I → Type*}
    [∀ i, CStarAlgebra (ℬ i)] [∀ i, Nontrivial (ℬ i)] [∀ i, PartialOrder (ℬ i)]
    [∀ i, StarOrderedRing (ℬ i)] (i : I) (x : lp ℬ ∞) :
    x * lpKappa i (1 : ℬ i) = lpKappa i ((x : ∀ j, ℬ j) i) := by
  have h := congrArg star (lpKappa_mul_left (𝒜 := ℬ) i (star x))
  rw [star_mul, star_star, (lpKappa_sa (𝒜 := ℬ) i).star_eq, lpKappa_star] at h
  rw [h]
  congr 1
  rw [show ((star x : lp ℬ ∞) : ∀ j, ℬ j) i = star ((x : ∀ j, ℬ j) i) from by
    rw [lp.coeFn_star]; rfl, star_star]

/-- `Ψ` as an nmiu-map. -/
private def gPhi : NMIUMap A (lp 𝒜 ∞) :=
  ⟨Ψ.toStarAlgHom, starAlgEquiv_preservesDirSups Ψ⟩

/-- The `j`-th block of `a`. -/
private def gPi (j : J) : NMIUMap A (𝒜 j) := nmiuComp (lpEvalNMIU _ j) (gPhi Ψ)

private theorem gPi_apply (j : J) (a : A) : gPi Ψ j a = (Ψ a : ∀ j : J, 𝒜 j) j := rfl

/-- The coprojection `κ_j : 𝒜 j → A`, transported along `Ψ`. -/
private def gU (j : J) (m : 𝒜 j) : A := Ψ.symm (lpKappa j m)

/-- The central projection carried by the `j`-th block. -/
private def gZ (j : J) : A := gU Ψ j 1

private theorem gU_add (j : J) (m m' : 𝒜 j) :
    gU Ψ j (m + m') = gU Ψ j m + gU Ψ j m' := by
  rw [gU, gU, gU, lpKappa_add]
  exact map_add Ψ.symm.toStarAlgHom _ _

private theorem gU_zero (j : J) : gU Ψ j 0 = 0 := by
  rw [gU, lpKappa_zero]
  exact map_zero Ψ.symm.toStarAlgHom

private theorem gU_sub (j : J) (m m' : 𝒜 j) :
    gU Ψ j (m - m') = gU Ψ j m - gU Ψ j m' := by
  rw [gU, gU, gU, lpKappa_sub]
  exact map_sub Ψ.symm.toStarAlgHom _ _

private theorem gU_smul (j : J) (r : ℂ) (m : 𝒜 j) :
    gU Ψ j (r • m) = r • gU Ψ j m := by
  rw [gU, gU, lpKappa_smul]
  exact map_smul Ψ.symm.toStarAlgHom _ _

private theorem gU_star (j : J) (m : 𝒜 j) :
    star (gU Ψ j m) = gU Ψ j (star m) := by
  rw [gU, gU, ← lpKappa_star]
  exact (map_star Ψ.symm.toStarAlgHom _).symm

private theorem gU_mul (j : J) (m m' : 𝒜 j) :
    gU Ψ j m * gU Ψ j m' = gU Ψ j (m * m') := by
  rw [gU, gU, gU, ← lpKappa_mul]
  exact (map_mul Ψ.symm.toStarAlgHom _ _).symm

private theorem gU_sum (j : J) {ι' : Type*} (F : Finset ι') (f : ι' → 𝒜 j) :
    gU Ψ j (∑ p ∈ F, f p) = ∑ p ∈ F, gU Ψ j (f p) := by
  classical
  induction F using Finset.induction with
  | empty => simpa using gU_zero Ψ j
  | insert p F hp ih =>
      rw [Finset.sum_insert hp, Finset.sum_insert hp, gU_add, ih]

private theorem gU_nonneg (j : J) {m : 𝒜 j} (hm : 0 ≤ m) : 0 ≤ gU Ψ j m := by
  have h : (0 : A) = gU Ψ j 0 := (gU_zero Ψ j).symm
  rw [h, gU, gU]
  exact starAlgHom_mono' Ψ.symm.toStarAlgHom (lpKappa_le j hm)

private theorem gU_le (j : J) {m m' : 𝒜 j} (h : m ≤ m') :
    gU Ψ j m ≤ gU Ψ j m' := by
  rw [← sub_nonneg, ← gU_sub]
  exact gU_nonneg Ψ j (sub_nonneg.mpr h)

private theorem gU_mul_mul (j : J) (m m' : 𝒜 j) (a : A) :
    gU Ψ j m * a * gU Ψ j m' = gU Ψ j (m * (Ψ a : ∀ j : J, 𝒜 j) j * m') := by
  have ha : a = Ψ.symm (Ψ a) := (Ψ.symm_apply_apply a).symm
  rw [gU, gU, gU]
  conv_lhs => rw [ha]
  rw [← map_mul, ← map_mul]
  congr 1
  calc lpKappa j m * Ψ a * lpKappa j m'
      = lpKappa j (m * (1 : 𝒜 j)) * Ψ a * lpKappa j m' := by rw [mul_one]
    _ = lpKappa j m * lpKappa j (1 : 𝒜 j) * Ψ a * lpKappa j m' := by rw [lpKappa_mul]
    _ = lpKappa j m * (lpKappa j (1 : 𝒜 j) * Ψ a) * lpKappa j m' := by
        rw [mul_assoc (lpKappa j m) (lpKappa j (1 : 𝒜 j)) (Ψ a)]
    _ = lpKappa j m * lpKappa j ((Ψ a : ∀ j : J, 𝒜 j) j) * lpKappa j m' := by
        rw [lpKappa_mul_left]
    _ = lpKappa j (m * (Ψ a : ∀ j : J, 𝒜 j) j * m') := by
        rw [lpKappa_mul, lpKappa_mul]

private theorem gZ_mul (j : J) (a : A) :
    gZ Ψ j * a = gU Ψ j ((Ψ a : ∀ j : J, 𝒜 j) j) := by
  rw [gZ, gU, gU]
  conv_lhs => rw [show a = Ψ.symm (Ψ a) from (Ψ.symm_apply_apply a).symm]
  rw [← map_mul, lpKappa_mul_left]

private theorem gZ_comm (j : J) (a : A) : gZ Ψ j * a = a * gZ Ψ j := by
  rw [gZ_mul, gZ, gU, gU]
  conv_rhs => rw [show a = Ψ.symm (Ψ a) from (Ψ.symm_apply_apply a).symm]
  rw [← map_mul, lpKappa_one_mul_right]

/-- The block projections of a family of positive elements with supremum `1`
in the block have supremum `z_j` in `A`. -/
private theorem gU_isLUB (j : J) {ι' : Type*} [Nonempty ι'] (p : ι' → 𝒜 j)
    (hp0 : ∀ i, 0 ≤ p i) (hlub : IsLUB (Set.range p) (1 : 𝒜 j)) :
    IsLUB (Set.range fun i => gU Ψ j (p i)) (gZ Ψ j) := by
  have hlp : IsLUB (Set.range fun i => lpKappa j (p i)) (lpKappa j (1 : 𝒜 j)) := by
    constructor
    · rintro _ ⟨i, rfl⟩
      exact lpKappa_le j (hlub.1 ⟨i, rfl⟩)
    · intro y hy
      rw [lp_infty_le_iff]
      intro q
      by_cases hq : q = j
      · subst hq
        rw [lpKappa_apply_self]
        refine hlub.2 ?_
        rintro _ ⟨i, rfl⟩
        have h := hy ⟨i, rfl⟩
        rw [lp_infty_le_iff] at h
        have h2 := h q
        rwa [lpKappa_apply_self] at h2
      · rw [lpKappa_apply_ne _ _ hq]
        obtain ⟨i⟩ := ‹Nonempty ι'›
        have h := hy ⟨i, rfl⟩
        rw [lp_infty_le_iff] at h
        have h2 := h q
        rw [lpKappa_apply_ne _ _ hq] at h2
        exact h2
  have h2 := isLUB_image_of_orderIso ⇑Ψ.symm (starAlgEquiv_le_iff Ψ.symm)
    Ψ.symm.surjective hlp
  have himg : ⇑Ψ.symm '' (Set.range fun i => lpKappa j (p i))
      = Set.range fun i => gU Ψ j (p i) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  rwa [himg] at h2

/-! ### The approximation step `∑_{j ∈ F} z_j ↑ 1`, for an arbitrary family -/

private def gZS (F : Finset J) : A := ∑ j ∈ F, gZ Ψ j

private theorem gZS_eq (F : Finset J) :
    gZS Ψ F = Ψ.symm ((lpSumSA (𝒜 := 𝒜) F : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞) := by
  classical
  show ∑ j ∈ F, Ψ.symm (lpKappa j 1) = _
  rw [show ((lpSumSA (𝒜 := 𝒜) F : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞)
      = ∑ j ∈ F, lpKappa j (1 : 𝒜 j) from rfl]
  exact (map_sum Ψ.symm.toStarAlgHom _ _).symm

private theorem gZS_sa (F : Finset J) : IsSelfAdjoint (gZS Ψ F) := by
  show star _ = _
  rw [gZS_eq]
  exact (map_star Ψ.symm.toStarAlgHom _).symm.trans
    (congrArg ⇑Ψ.symm.toStarAlgHom (lpSumSA F).2.star_eq)

private theorem gZS_mono {F G : Finset J} (hFG : F ⊆ G) : gZS Ψ F ≤ gZS Ψ G := by
  rw [gZS_eq, gZS_eq]
  exact starAlgHom_mono' Ψ.symm.toStarAlgHom
    (Subtype.coe_le_coe.mpr (lpSumSA_mono hFG))

private theorem gZS_isLUB : IsLUB (Set.range (fun F : Finset J => gZS Ψ F)) (1 : A) := by
  have h1 : IsLUB ((fun d : selfAdjoint (lp 𝒜 ∞) => (d : lp 𝒜 ∞)) ''
        Set.range (lpSumSA (𝒜 := 𝒜)))
      ((⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞) :=
    isLUB_coe_of_isLUB' ⟨_, ⟨∅, rfl⟩⟩ lpSumSA_isLUB
  have h2 := isLUB_image_of_orderIso ⇑Ψ.symm (starAlgEquiv_le_iff Ψ.symm)
    Ψ.symm.surjective h1
  have himg : ⇑Ψ.symm '' ((fun d : selfAdjoint (lp 𝒜 ∞) => (d : lp 𝒜 ∞)) ''
        Set.range (lpSumSA (𝒜 := 𝒜)))
      = Set.range (fun F : Finset J => gZS Ψ F) := by
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨F, rfl⟩, rfl⟩, rfl⟩
      exact ⟨F, gZS_eq Ψ F⟩
    · rintro ⟨F, rfl⟩
      exact ⟨_, ⟨_, ⟨F, rfl⟩, rfl⟩, (gZS_eq Ψ F).symm⟩
  rw [himg] at h2
  rwa [show Ψ.symm ((⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞) = 1 from
    map_one Ψ.symm.toStarAlgHom] at h2

/-- **The ultraweak approximation step**, for an arbitrary family: `x` lies
in every ultraweakly closed set containing all `(1 ⊗ ∑_{j∈F} z_j)·x`. -/
private theorem gApprox (x : VNT C A) (T : Set (VNT C A))
    (hT : @IsClosed (VNT C A) (ultraweak (VNT C A)) T)
    (hmem : ∀ F : Finset J, ((1 : C) ⊗ᵥ gZS Ψ F) * x ∈ T) : x ∈ T := by
  classical
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  letI : TopologicalSpace A := ultraweak A
  have h1 : Tendsto (fun F : Finset J => gZS Ψ F) atTop
      (@nhds A (ultraweak A) (1 : A)) :=
    uwTendsto_of_isLUB (X := A) (fun F => gZS Ψ F) 1 (gZS_sa Ψ)
      (fun F G hFG => gZS_mono Ψ hFG) (gZS_isLUB Ψ)
  have hcont : @Continuous A (VNT C A) (ultraweak A) (ultraweak (VNT C A))
      (fun b : A => ((1 : C) ⊗ᵥ b) * x) :=
    ((mult_uws_cont x).2.1).comp (continuous_ultraweak_vtmul_right (1 : C))
  have h2 := (hcont.tendsto (1 : A)).comp h1
  have hone : ((1 : C) ⊗ᵥ (1 : A)) = 1 := (vnTensor C A).isTensorProduct.miu.1
  rw [show ((1 : C) ⊗ᵥ (1 : A)) * x = x by rw [hone, one_mul]] at h2
  exact hT.mem_of_tendsto h2 (Filter.Eventually.of_forall hmem)

end GenSum

/-! ## The atomic type I slice device

The widened form of the `haE` device: `𝒜 ≅ ⊕_j B(𝒦_j)` with the `𝒦_j`
arbitrary Hilbert spaces.  Everything is the same except that the block
expansion is now the *compression* `p_F a p_F = ∑_{k,l ∈ F} a_{kl} u_{kl}`
along a finite set `F` of basis indices, and the passage `F ↑ ⊤` needs
`uw_compress_tendsto`. -/

section AtSlice

set_option synthInstance.maxHeartbeats 400000

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C]
variable {J : Type u} {ιk : J → Type u} {K : J → Type u}
  [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
  [∀ j, CompleteSpace (K j)] [∀ j, Nontrivial (K j)] [∀ j, Nonempty (ιk j)]

variable (e : ∀ j : J, HilbertBasis (ιk j) ℂ (K j))
  (Ψ : A ≃⋆ₐ[ℂ] lp (fun j : J => (K j →L[ℂ] K j)) ∞)

/-- The matrix units of `𝒜`. -/
private def atU (j : J) (k l : ιk j) : A := gU Ψ j (bkU (e j) k l)

/-- The block compressions of `𝒜`. -/
private def atP (j : J) (F : Finset (ιk j)) : A := gU Ψ j (bkP (e j) F)

/-- The `(k,l)` entry of the `j`-th block. -/
private def atEnt (j : J) (a : A) (k l : ιk j) : ℂ :=
  ⟪e j k, ((Ψ a : ∀ q : J, (K q →L[ℂ] K q)) j) (e j l)⟫

private theorem atPsi_gU (j : J) (m : K j →L[ℂ] K j) :
    (Ψ (gU Ψ j m) : ∀ q : J, (K q →L[ℂ] K q)) j = m := by
  rw [gU, Ψ.apply_symm_apply, lpKappa_apply_self]

private theorem atEnt_atU (j : J) (k l k' l' : ιk j) :
    atEnt e Ψ j (atU e Ψ j k l) k' l' = ⟪e j k', (bkU (e j) k l) (e j l')⟫ := by
  rw [atEnt, atU, atPsi_gU]

private theorem atU_mul_mul (j : J) (o k l : ιk j) (a : A) :
    atU e Ψ j o k * a * atU e Ψ j l o = (atEnt e Ψ j a k l) • atU e Ψ j o o := by
  rw [atU, atU, atU, gU_mul_mul, bkU_mul_mul, gU_smul]
  rfl

private theorem atP_mul_mul (j : J) (F : Finset (ιk j)) (a : A) :
    atP e Ψ j F * a * atP e Ψ j F
      = ∑ k ∈ F, ∑ l ∈ F, (atEnt e Ψ j a k l) • atU e Ψ j k l := by
  rw [atP, gU_mul_mul, bkP_mul_mul, gU_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gU_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [gU_smul]; rfl

private theorem atP_sa (j : J) (F : Finset (ιk j)) :
    star (atP e Ψ j F) * atP e Ψ j F = atP e Ψ j F := by
  rw [atP, gU_star, gU_mul, bkP_star, bkP_mul_self]

private theorem atP_le (j : J) (F : Finset (ιk j)) : atP e Ψ j F ≤ gZ Ψ j :=
  gU_le Ψ j (bkP_le_one (e j) F)

private theorem atP_isSelfAdjoint (j : J) (F : Finset (ιk j)) :
    IsSelfAdjoint (atP e Ψ j F) := by
  show star _ = _
  rw [atP, gU_star, bkP_star]

private theorem atP_mono (j : J) {F G : Finset (ιk j)} (h : F ⊆ G) :
    atP e Ψ j F ≤ atP e Ψ j G :=
  gU_le Ψ j (bkP_mono (e j) h)

private theorem atP_isLUB (j : J) :
    IsLUB (Set.range (atP e Ψ j)) (gZ Ψ j) :=
  gU_isLUB Ψ j (bkP (e j)) (bkP_nonneg (e j)) (bkP_isLUB (e j))

private theorem atGZ_sub_atP (j : J) (F : Finset (ιk j)) :
    star (gZ Ψ j - atP e Ψ j F) * (gZ Ψ j - atP e Ψ j F) = gZ Ψ j - atP e Ψ j F := by
  have hsub : gZ Ψ j - atP e Ψ j F = gU Ψ j (1 - bkP (e j) F) := by
    rw [gU_sub, gZ, atP]
  rw [hsub, gU_star, gU_mul, star_sub, star_one, bkP_star]
  congr 1
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, bkP_mul_self]
  abel

/-- The distinguished basis index of the `j`-th block. -/
private def atO (_e : ∀ j : J, HilbertBasis (ιk j) ℂ (K j)) (j : J) : ιk j :=
  Classical.arbitrary (ιk j)

/-- The np-functional `a ↦ ⟪e^j_0, a_j e^j_0⟫`. -/
private def atOm (j : J) : NPFunctional A :=
  compNP (nmiuP (gPi Ψ j)) (gPi Ψ j).preservesDirSups' (vectorNP (e j (atO e j)))

private theorem atOm_apply (j : J) (a : A) :
    (atOm e Ψ j a : ℂ) = atEnt e Ψ j a (atO e j) (atO e j) := rfl

/-- The ncp-map `a ↦ ⟪e^j_0, a_j e^j_0⟫·1`. -/
private def atKappa (j : J) : NCPMap A A := npScalar (atOm e Ψ j)

private theorem atKappa_apply (j : J) (a : A) :
    atKappa e Ψ j a = algebraMap ℂ A (atEnt e Ψ j a (atO e j) (atO e j)) := by
  show algebraMap ℂ A (atOm e Ψ j a) = _
  rw [atOm_apply]

private theorem atKappa_atU (j : J) :
    atKappa e Ψ j (atU e Ψ j (atO e j) (atO e j)) = 1 := by
  rw [atKappa_apply, atEnt_atU, bkU_diag_inner, map_one]

variable (C)

/-- The widened slice operator
`x ↦ (id ⊗ κ_j)((1 ⊗ u^j_{0k}) x (1 ⊗ u^j_{l0}))`. -/
private def atE (j : J) (k l : ιk j) (x : VNT C A) : VNT C A :=
  tmap (ncpId C) (atKappa e Ψ j)
    (((1 : C) ⊗ᵥ atU e Ψ j (atO e j) k) * x * ((1 : C) ⊗ᵥ atU e Ψ j l (atO e j)))

variable {C}

private theorem atE_tmul (j : J) (k l : ιk j) (c : C) (a : A) :
    atE C e Ψ j k l (c ⊗ᵥ a) = (atEnt e Ψ j a k l) • (c ⊗ᵥ (1 : A)) := by
  rw [atE, vtmul_mul_vtmul, vtmul_mul_vtmul, one_mul, mul_one,
    atU_mul_mul, vtmul_smul_right,
    show (tmap (ncpId C) (atKappa e Ψ j))
        ((atEnt e Ψ j a k l) • (c ⊗ᵥ atU e Ψ j (atO e j) (atO e j)))
        = (atEnt e Ψ j a k l) •
            (tmap (ncpId C) (atKappa e Ψ j)) (c ⊗ᵥ atU e Ψ j (atO e j) (atO e j)) from
      map_smul (tmap (ncpId C) (atKappa e Ψ j)).toCompletelyPositiveMap.toLinearMap _ _,
    tmap_apply, ncpId_apply, atKappa_atU]

/-- `atE` as a linear map. -/
private def atEL (j : J) (k l : ιk j) : VNT C A →ₗ[ℂ] VNT C A :=
  ((tmap (ncpId C) (atKappa e Ψ j)).toCompletelyPositiveMap.toLinearMap).comp
    (((LinearMap.mulRight ℂ ((1 : C) ⊗ᵥ atU e Ψ j l (atO e j))).comp
      (LinearMap.mulLeft ℂ ((1 : C) ⊗ᵥ atU e Ψ j (atO e j) k))))

private theorem atEL_apply (j : J) (k l : ιk j) (x : VNT C A) :
    atEL e Ψ j k l x = atE C e Ψ j k l x := rfl

private theorem atEL_continuous (j : J) (k l : ιk j) :
    @Continuous (VNT C A) (VNT C A) (ultraweak _) (ultraweak _) ⇑(atEL e Ψ j k l) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  have h1 : Continuous (fun x : VNT C A =>
      ((1 : C) ⊗ᵥ atU e Ψ j (atO e j) k) * x * ((1 : C) ⊗ᵥ atU e Ψ j l (atO e j))) :=
    continuous_uw_mulmul _ _
  have h2 : Continuous ⇑(tmap (ncpId C) (atKappa e Ψ j)) :=
    ((p_uwcont (ncpPositive (tmap (ncpId C) (atKappa e Ψ j)))).out 2 0).mp
      (tmap (ncpId C) (atKappa e Ψ j)).preservesDirSups'
  exact h2.comp h1

private theorem atE_mem (j : J) (k l : ιk j) (x : VNT C A) :
    ∃ c : C, atE C e Ψ j k l x = c ⊗ᵥ (1 : A) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  haveI : T2Space (VNT C A) := vn_positive_basic_1.1
  obtain ⟨hRvn⟩ : Nonempty (IsVNSubalgebra (VNT C A)
      (nmiuTmulLeft C A).toStarAlgHom.range) :=
    ⟨nmiu_image _⟩
  have hRcl : IsClosed
      ((nmiuTmulLeft C A).toStarAlgHom.range : Set (VNT C A)) :=
    (vnsac _ hRvn).2
  set W : Submodule ℂ (VNT C A) :=
    Submodule.comap (atEL e Ψ j k l)
      (Subalgebra.toSubmodule
        (nmiuTmulLeft C A).toStarAlgHom.range.toSubalgebra) with hW
  have hWcl : IsClosed (W : Set (VNT C A)) :=
    hRcl.preimage (atEL_continuous e Ψ j k l)
  have hspan : (Submodule.span ℂ
      {t : VNT C A | ∃ a b, t = (vnTensor C A).map a b} : Set (VNT C A))
      ⊆ (W : Set (VNT C A)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, a, rfl⟩
    have hmem : atE C e Ψ j k l (c ⊗ᵥ a) ∈
        (nmiuTmulLeft C A).toStarAlgHom.range := by
      rw [atE_tmul, ← vtmulLeft_smul]
      exact ⟨(atEnt e Ψ j a k l) • c, rfl⟩
    exact hmem
  have hx : x ∈ W := by
    have hd := (vnTensor C A).isTensorProduct.dense
    have hcl : x ∈ closure ((Submodule.span ℂ
        {t : VNT C A | ∃ a b, t = (vnTensor C A).map a b} : Set (VNT C A))) := by
      rw [hd.closure_eq]; trivial
    exact hWcl.closure_subset_iff.mpr hspan hcl
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

/-- The widened block expansion: the *compression* of `x` by `1 ⊗ p^j_F` is
the finite sum of its entries in `F`. -/
private theorem atSliceEq (j : J) (F : Finset (ιk j)) (x : VNT C A) :
    ((1 : C) ⊗ᵥ atP e Ψ j F) * x * ((1 : C) ⊗ᵥ atP e Ψ j F)
      = ∑ k ∈ F, ∑ l ∈ F, atE C e Ψ j k l x * ((1 : C) ⊗ᵥ atU e Ψ j k l) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  haveI : T2Space (VNT C A) := vn_positive_basic_1.1
  set f : VNT C A →ₗ[ℂ] VNT C A :=
    (LinearMap.mulRight ℂ ((1 : C) ⊗ᵥ atP e Ψ j F)).comp
      (LinearMap.mulLeft ℂ ((1 : C) ⊗ᵥ atP e Ψ j F)) with hf
  set g : VNT C A →ₗ[ℂ] VNT C A :=
    ∑ k ∈ F, ∑ l ∈ F,
      (LinearMap.mulRight ℂ ((1 : C) ⊗ᵥ atU e Ψ j k l)).comp (atEL e Ψ j k l) with hg
  have hgapp : ∀ y : VNT C A, g y
      = ∑ k ∈ F, ∑ l ∈ F, atE C e Ψ j k l y * ((1 : C) ⊗ᵥ atU e Ψ j k l) := by
    intro y
    rw [hg, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => LinearMap.sum_apply _ _ _
  have hcf : Continuous ⇑f := continuous_uw_mulmul _ _
  have hcg : Continuous ⇑g := by
    have h : ⇑g = fun y : VNT C A => ∑ k ∈ F, ∑ l ∈ F,
        atE C e Ψ j k l y * ((1 : C) ⊗ᵥ atU e Ψ j k l) := funext hgapp
    rw [h]
    refine continuous_ultraweak_of_forall _ fun ν => ?_
    have hnu : (fun y : VNT C A => (ν (∑ k ∈ F, ∑ l ∈ F,
          atE C e Ψ j k l y * ((1 : C) ⊗ᵥ atU e Ψ j k l)) : ℂ))
        = fun y : VNT C A => ∑ k ∈ F, ∑ l ∈ F,
            (ν (atE C e Ψ j k l y * ((1 : C) ⊗ᵥ atU e Ψ j k l)) : ℂ) := by
      funext y
      exact (map_sum ν.toPositiveLinearMap _ _).trans
        (Finset.sum_congr rfl fun k _ => map_sum ν.toPositiveLinearMap _ _)
    rw [hnu]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    have hc1 : Continuous (fun y : VNT C A =>
        (ν (1 * y * ((1 : C) ⊗ᵥ atU e Ψ j k l)) : ℂ)) :=
      continuous_ultraweak_conj ν 1 ((1 : C) ⊗ᵥ atU e Ψ j k l)
    simp only [one_mul] at hc1
    exact hc1.comp (atEL_continuous e Ψ j k l)
  have hfg : f = g := by
    refine tensor_linear_ext (vnTensor C A).isTensorProduct f g hcf hcg ?_
    intro c a
    show ((1 : C) ⊗ᵥ atP e Ψ j F) * (c ⊗ᵥ a) * ((1 : C) ⊗ᵥ atP e Ψ j F) = g (c ⊗ᵥ a)
    rw [hgapp, vtmul_mul_vtmul, vtmul_mul_vtmul, one_mul, mul_one, atP_mul_mul]
    have hsum : c ⊗ᵥ (∑ k ∈ F, ∑ l ∈ F, (atEnt e Ψ j a k l) • atU e Ψ j k l)
        = ∑ k ∈ F, ∑ l ∈ F, (atEnt e Ψ j a k l) • (c ⊗ᵥ atU e Ψ j k l) := by
      show (vnTensor C A).map c _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [map_sum]
        exact Finset.sum_congr rfl fun l _ => map_smul ((vnTensor C A).map c) _ _
    rw [hsum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [atE_tmul, smul_mul_assoc, vtmul_mul_vtmul, mul_one, one_mul]
  have h := congrFun (congrArg (fun L : VNT C A →ₗ[ℂ] VNT C A => ⇑L) hfg) x
  rw [hgapp] at h
  exact h

end AtSlice

/-! ### The two membership corollaries (the atomic type I slice-map property) -/

section AtSliceProperty

set_option synthInstance.maxHeartbeats 400000

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C] [VonNeumannAlgebra D]
variable {J : Type u} {ιk : J → Type u} {K : J → Type u}
  [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
  [∀ j, CompleteSpace (K j)] [∀ j, Nontrivial (K j)] [∀ j, Nonempty (ιk j)]

variable (e : ∀ j : J, HilbertBasis (ιk j) ℂ (K j))
  (Ψ : A ≃⋆ₐ[ℂ] lp (fun j : J => (K j →L[ℂ] K j)) ∞)

private theorem vtmulR_mul (a a' : A) :
    ((1 : C) ⊗ᵥ a) * ((1 : C) ⊗ᵥ a') = (1 : C) ⊗ᵥ (a * a') := by
  rw [vtmul_mul_vtmul, one_mul]

private theorem vtmulR_star (a : A) :
    star ((1 : C) ⊗ᵥ a) = (1 : C) ⊗ᵥ star a := by
  have h := (vnTensor C A).isTensorProduct.miu.2.2 (1 : C) a
  rw [star_one] at h
  exact h

private theorem vtmulR_sub (a a' : A) :
    (1 : C) ⊗ᵥ (a - a') = ((1 : C) ⊗ᵥ a) - ((1 : C) ⊗ᵥ a') :=
  map_sub ((vnTensor C A).map 1) a a'

private theorem vtmulR_mono {a a' : A} (h : a ≤ a') :
    ((1 : C) ⊗ᵥ a) ≤ ((1 : C) ⊗ᵥ a') := by
  have h1 := vtmul_nonneg (1 : C) (a' - a) zero_le_one (sub_nonneg.mpr h)
  rw [vtmulR_sub] at h1
  exact sub_nonneg.mp h1

/-- `1 ⊗ z_j` is central in `𝒞 ⊗ 𝒜`: it commutes with the elementary
tensors, and the two multiplication maps are ultraweakly continuous. -/
private theorem vtmul_gZ_comm (j : J) (x : VNT C A) :
    ((1 : C) ⊗ᵥ gZ Ψ j) * x = x * ((1 : C) ⊗ᵥ gZ Ψ j) := by
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  haveI : T2Space (VNT C A) := vn_positive_basic_1.1
  set f : VNT C A →ₗ[ℂ] VNT C A :=
    LinearMap.mulLeft ℂ ((1 : C) ⊗ᵥ gZ Ψ j) with hf
  set g : VNT C A →ₗ[ℂ] VNT C A :=
    LinearMap.mulRight ℂ ((1 : C) ⊗ᵥ gZ Ψ j) with hg
  have hcf : Continuous ⇑f := (mult_uws_cont ((1 : C) ⊗ᵥ gZ Ψ j)).1
  have hcg : Continuous ⇑g := (mult_uws_cont ((1 : C) ⊗ᵥ gZ Ψ j)).2.1
  have hfg : f = g := by
    refine tensor_linear_ext (vnTensor C A).isTensorProduct f g hcf hcg ?_
    intro c a
    show ((1 : C) ⊗ᵥ gZ Ψ j) * (c ⊗ᵥ a) = (c ⊗ᵥ a) * ((1 : C) ⊗ᵥ gZ Ψ j)
    rw [vtmul_mul_vtmul, vtmul_mul_vtmul, one_mul, mul_one, gZ_comm]
  exact congrFun (congrArg (fun L : VNT C A →ₗ[ℂ] VNT C A => ⇑L) hfg) x

private theorem gZ_mul_self (j : J) : gZ Ψ j * gZ Ψ j = gZ Ψ j := by
  rw [gZ, gU_mul, one_mul]

/-- The compressions `1 ⊗ p^j_F` converge ultraweakly to `1 ⊗ z_j` from
both sides. -/
private theorem atCompress_tendsto (j : J) (x : VNT C A) :
    UWTendsto (fun F : Finset (ιk j) =>
        ((1 : C) ⊗ᵥ atP e Ψ j F) * x * ((1 : C) ⊗ᵥ atP e Ψ j F)) atTop
      (((1 : C) ⊗ᵥ gZ Ψ j) * x * ((1 : C) ⊗ᵥ gZ Ψ j)) := by
  refine uw_compress_tendsto ((1 : C) ⊗ᵥ gZ Ψ j)
    (fun F => (1 : C) ⊗ᵥ atP e Ψ j F) (fun F => ?_) (fun F => ?_) (fun F => ?_) ?_ x
  · rw [vtmulR_star, vtmulR_mul, atP_sa]
  · rw [← vtmulR_sub, vtmulR_star, vtmulR_mul, atGZ_sub_atP]
  · exact vtmulR_mono (atP_le e Ψ j F)
  · letI : TopologicalSpace A := ultraweak A
    letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
    have h : UWTendsto (atP e Ψ j) atTop (gZ Ψ j) :=
      uwTendsto_of_isLUB (X := A) (ι' := Finset (ιk j)) (atP e Ψ j) (gZ Ψ j)
        (atP_isSelfAdjoint e Ψ j)
        (fun F G hFG => atP_mono e Ψ j hFG) (atP_isLUB e Ψ j)
    have hcont : @Continuous A (VNT C A) (ultraweak A) (ultraweak (VNT C A))
        (fun b : A => (1 : C) ⊗ᵥ b) := continuous_ultraweak_vtmul_right (1 : C)
    exact (hcont.tendsto (gZ Ψ j)).comp h

/-- **The atomic type I slice-map property, containment half**: if every
entry `atE j k l x` of `x` lies in `𝒮 ⊗ 𝒜`, then `x` does. -/
private theorem atMem (S : StarSubalgebra ℂ C) (x : VNT C A)
    (h : ∀ (j : J) (k l : ιk j), atE C e Ψ j k l x ∈ tensorSub A S) :
    x ∈ tensorSub A S := by
  classical
  letI : TopologicalSpace (VNT C A) := ultraweak (VNT C A)
  have hcl : @IsClosed (VNT C A) (ultraweak (VNT C A))
      ((tensorSub A S : StarSubalgebra ℂ (VNT C A)) : Set (VNT C A)) :=
    (vnsac _ (isVNSubalgebra_wstar _).1).2
  refine gApprox Ψ x ((tensorSub A S : StarSubalgebra ℂ (VNT C A)) : Set (VNT C A))
    hcl ?_
  intro F
  have hsplit : ((1 : C) ⊗ᵥ gZS Ψ F) * x = ∑ j ∈ F, ((1 : C) ⊗ᵥ gZ Ψ j) * x := by
    have hd : ((1 : C) ⊗ᵥ gZS Ψ F) = ∑ j ∈ F, ((1 : C) ⊗ᵥ gZ Ψ j) :=
      map_sum ((vnTensor C A).map 1) _ _
    rw [hd, Finset.sum_mul]
  rw [SetLike.mem_coe, hsplit]
  refine sum_mem fun j _ => ?_
  have hww : ((1 : C) ⊗ᵥ gZ Ψ j) * ((1 : C) ⊗ᵥ gZ Ψ j) = ((1 : C) ⊗ᵥ gZ Ψ j) := by
    rw [vtmulR_mul, gZ_mul_self]
  have hcomm := vtmul_gZ_comm Ψ j x
  have hzz : ((1 : C) ⊗ᵥ gZ Ψ j) * x * ((1 : C) ⊗ᵥ gZ Ψ j)
      = ((1 : C) ⊗ᵥ gZ Ψ j) * x :=
    calc ((1 : C) ⊗ᵥ gZ Ψ j) * x * ((1 : C) ⊗ᵥ gZ Ψ j)
        = ((1 : C) ⊗ᵥ gZ Ψ j) * (x * ((1 : C) ⊗ᵥ gZ Ψ j)) := mul_assoc _ _ _
      _ = ((1 : C) ⊗ᵥ gZ Ψ j) * (((1 : C) ⊗ᵥ gZ Ψ j) * x) := by rw [hcomm]
      _ = (((1 : C) ⊗ᵥ gZ Ψ j) * ((1 : C) ⊗ᵥ gZ Ψ j)) * x := (mul_assoc _ _ _).symm
      _ = ((1 : C) ⊗ᵥ gZ Ψ j) * x := by rw [hww]
  rw [← hzz]
  refine hcl.mem_of_tendsto (atCompress_tendsto e Ψ j x)
    (Filter.Eventually.of_forall fun F' => ?_)
  rw [atSliceEq]
  exact sum_mem fun k _ => sum_mem fun l _ =>
    mul_mem (h j k l) (vtmul_one_mem S _)

/-- Naturality of the widened slice operator in the first factor. -/
private theorem atE_natural {C' : Type u} [CStarAlgebra C'] [PartialOrder C']
    [StarOrderedRing C'] [VonNeumannAlgebra C'] (ρ : NMIUMap C' C)
    (j : J) (k l : ιk j) (y : VNT C' A) :
    tmapM ρ (nmiuId A) (atE C' e Ψ j k l y)
      = atE C e Ψ j k l (tmapM ρ (nmiuId A) y) := by
  have hcomm : ncpComp (nmiuNCP (tmapM ρ (nmiuId A))) (tmap (ncpId C') (atKappa e Ψ j))
      = ncpComp (tmap (ncpId C) (atKappa e Ψ j)) (nmiuNCP (tmapM ρ (nmiuId A))) := by
    refine (exists_tmap (nmiuNCP ρ) (atKappa e Ψ j)).unique (fun a b => ?_) (fun a b => ?_)
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, tmapM_apply,
        nmiuId_apply]
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply, tmapM_apply,
        nmiuId_apply]
  have hkey : ∀ z : VNT C' A, tmapM ρ (nmiuId A) (tmap (ncpId C') (atKappa e Ψ j) z)
      = tmap (ncpId C) (atKappa e Ψ j) (tmapM ρ (nmiuId A) z) := fun z => by
    have h := congrArg (fun F : NCPMap (VNT C' A) (VNT C A) => F z) hcomm
    simpa only [ncpComp_apply, nmiuNCP_apply] using h
  have hmul : ∀ z w : VNT C' A, tmapM ρ (nmiuId A) (z * w)
      = tmapM ρ (nmiuId A) z * tmapM ρ (nmiuId A) w :=
    fun z w => map_mul (tmapM ρ (nmiuId A)).toStarAlgHom z w
  show tmapM ρ (nmiuId A) (tmap (ncpId C') (atKappa e Ψ j) _) = _
  rw [hkey]
  show _ = tmap (ncpId C) (atKappa e Ψ j) _
  congr 1
  rw [hmul, hmul, tmapM_vtmul_one, tmapM_vtmul_one]

/-- **The atomic type I slice-map property, extraction half**: the entries
of an element of `𝒮 ⊗ 𝒜` lie in `𝒮`. -/
private theorem atE_of_mem (S : StarSubalgebra ℂ C) (hS : IsVNSubalgebra C S)
    (x : VNT C A) (hx : x ∈ tensorSub A S) (j : J) (k l : ιk j) :
    ∃ c ∈ S, atE C e Ψ j k l x = c ⊗ᵥ (1 : A) := by
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
  obtain ⟨c, hc⟩ := atE_mem (C := VNSub C S hS) e Ψ j k l y
  refine ⟨c.val, c.property, ?_⟩
  rw [← hy', ← atE_natural e Ψ (VNSub.valNMIU (A := C) (S := S) (hS := hS)) j k l y, hc,
    tmapM_apply, nmiuId_apply]
  rfl

/-- **The atomic type I form of 125VIIb** (`tensor-preimage`): for
`𝒜 ≅ ⊕_j B(𝒦_j)` with the `𝒦_j` *arbitrary* Hilbert spaces,
`(ρ ⊗ 𝒜)⁻¹(𝒮 ⊗ 𝒜) = ρ⁻¹(𝒮) ⊗ 𝒜`. -/
private theorem atTensorPreimage
    (e : ∀ j : J, HilbertBasis (ιk j) ℂ (K j))
    (Ψ : A ≃⋆ₐ[ℂ] lp (fun j : J => (K j →L[ℂ] K j)) ∞) (ρ : NMIUMap C D)
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
    refine atMem e Ψ _ _ (fun j k l => ?_)
    obtain ⟨c', hc'⟩ := atE_mem (C := C) e Ψ j k l x
    obtain ⟨d, hd, hde⟩ := atE_of_mem e Ψ S hS _ hx j k l
    have hnat := atE_natural e Ψ ρ j k l x
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

end AtSliceProperty

/-! ### The atomic type I form of 125eIII -/

section AtSliceBSurj

set_option synthInstance.maxHeartbeats 400000

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C] [VonNeumannAlgebra D]
variable {J : Type u} {ιk : J → Type u} {K : J → Type u}
  [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
  [∀ j, CompleteSpace (K j)] [∀ j, Nontrivial (K j)] [∀ j, Nonempty (ιk j)]
variable {Xs : Type u} [CStarAlgebra Xs] [PartialOrder Xs] [StarOrderedRing Xs]
  [VonNeumannAlgebra Xs]

/-- **The atomic type I form of 125eIII** (`tensorBsurjectivity`), the hard
half: `(ρ ⊗ 𝒜) ∘ s` is `(·) ⊗ 𝒜`-surjective when `s` is and `ρ` is
surjective, for `𝒜 ≅ ⊕_j B(𝒦_j)`. -/
private theorem atTensorBSurj
    (e : ∀ j : J, HilbertBasis (ιk j) ℂ (K j))
    (Ψ : A ≃⋆ₐ[ℂ] lp (fun j : J => (K j →L[ℂ] K j)) ∞)
    (s : NMIUMap Xs (VNT C A)) (hs : TensorBSurjective s) (ρ : NMIUMap C D)
    (hρ : Function.Surjective ⇑ρ) :
    TensorBSurjective (nmiuComp (tmapM ρ (nmiuId A)) s) := by
  intro S hS hsub
  have h1 : Set.range ⇑s ⊆
      ((tensorSub A (S.comap ρ.toStarAlgHom) : StarSubalgebra ℂ (VNT C A)) :
        Set (VNT C A)) := by
    rintro _ ⟨a, rfl⟩
    exact (atTensorPreimage e Ψ ρ S hS (s a)).mp (hsub ⟨a, rfl⟩)
  have h2 := hs _ (isVNSubalgebra_comap ρ.toStarAlgHom ρ.preservesDirSups' S hS) h1
  refine eq_top_iff.mpr fun d _ => ?_
  obtain ⟨c, rfl⟩ := hρ d
  have hc : c ∈ S.comap ρ.toStarAlgHom := by rw [h2]; trivial
  exact hc

end AtSliceBSurj

/-! ## The concrete-to-abstract bridge

`intersection_tensor` (121II) is stated concretely, about von Neumann
subalgebras of `B(ℋ ⊗ 𝒦)`; its consumers (125IV, 125VI, 125VIIb,
125VIII) are stated abstractly, in terms of the chosen tensor product
`VNT` (115I).  This section builds the bridge:

* `concreteTensorEquiv` — the canonical nmiu-isomorphism
  `W*(𝒜 ⊙ ℬ) ≅ 𝒜 ⊗ ℬ` for von Neumann subalgebras `𝒜 ⊆ B(ℋ)`,
  `ℬ ⊆ B(𝒦)`, obtained by feeding 111VII `special_tensor` and the
  chosen tensor product to 114II `tensor_uniqueness`;
* `mem_wstar_image_iff` / `mem_wstar_vnsub_iff` — `W*(-)` commutes with
  nmiu-isomorphisms and with passage to a bundled von Neumann
  subalgebra;
* `tensorSub₂` — the two-sided companion of `tensorSub`, and
  `concreteTensorEquiv_mem_tensorSub₂`, which says the bridge carries
  `concreteTensor` to `tensorSub₂`;
* `tensorSub₂_inf_of_intersection_tensor` — the transport of a `⊓`-fact
  about `concreteTensor` (i.e. of 121II) to the corresponding `⊓`-fact
  about `tensorSub₂`.  121II is taken as an explicit hypothesis, so that
  it is usable the moment it is proved. -/

section WstarTransport

universe ua ub

variable {X : Type ua} {Y : Type ub}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]

/-- `W*(-)` commutes with an nmiu-isomorphism. -/
theorem mem_wstar_image_iff (φ : NMIUMap X Y) (hφ : Function.Bijective ⇑φ)
    (G : Set X) (x : X) : φ x ∈ wstar Y (⇑φ '' G) ↔ x ∈ wstar X G := by
  constructor
  · intro hx
    have hle : wstar Y (⇑φ '' G) ≤
        (wstar X G).comap (nmiuSymm φ hφ).toStarAlgHom := by
      refine sInf_le ⟨isVNSubalgebra_comap (nmiuSymm φ hφ).toStarAlgHom
        (nmiuSymm φ hφ).preservesDirSups' _ (isVNSubalgebra_wstar G).1, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      show nmiuSymm φ hφ (φ g) ∈ wstar X G
      rw [nmiuSymm_apply_apply]
      exact (isVNSubalgebra_wstar G).2 hg
    have h2 : nmiuSymm φ hφ (φ x) ∈ wstar X G := hle hx
    rwa [nmiuSymm_apply_apply] at h2
  · intro hx
    have hle : wstar X G ≤ (wstar Y (⇑φ '' G)).comap φ.toStarAlgHom := by
      refine sInf_le ⟨isVNSubalgebra_comap φ.toStarAlgHom φ.preservesDirSups' _
        (isVNSubalgebra_wstar _).1, fun g hg => ?_⟩
      exact (isVNSubalgebra_wstar _).2 ⟨g, hg, rfl⟩
    exact hle hx

end WstarTransport

section WstarVNSub

variable [VonNeumannAlgebra A] {S : StarSubalgebra ℂ A}
  {hS : IsVNSubalgebra A S}

/-- `W*(-)` commutes with passage to a bundled von Neumann subalgebra: for
`G ⊆ 𝒮`, `W*(G)` computed inside `𝒮` is the trace of `W*(G)`. -/
theorem mem_wstar_vnsub_iff (G : Set A) (hGS : G ⊆ (S : Set A))
    (x : VNSub A S hS) :
    x ∈ wstar (VNSub A S hS) {y : VNSub A S hS | y.val ∈ G} ↔ x.val ∈ wstar A G := by
  constructor
  · intro hx
    have hle : wstar (VNSub A S hS) {y : VNSub A S hS | y.val ∈ G} ≤
        (wstar A G).comap (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS)) := by
      refine sInf_le ⟨isVNSubalgebra_comap
        (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))
        (VNSub.valNMIU (A := A) (S := S) (hS := hS)).preservesDirSups' _
        (isVNSubalgebra_wstar G).1, fun y hy => (isVNSubalgebra_wstar G).2 hy⟩
    exact hle hx
  · intro hx
    have hle : wstar A G ≤
        (wstar (VNSub A S hS) {y : VNSub A S hS | y.val ∈ G}).map
          (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS)) := by
      refine sInf_le ⟨vnsub_isVNSubalgebra_map _ (isVNSubalgebra_wstar _).1,
        fun g hg => ⟨⟨g, hGS hg⟩, (isVNSubalgebra_wstar _).2 hg, rfl⟩⟩
    obtain ⟨t, ht, hte⟩ := hle hx
    exact (VNSub.val_injective hte : t = x) ▸ ht

variable (hS) in
/-- The trace on a bundled von Neumann subalgebra `𝒮 ⊆ 𝒜` of a
`∗`-subalgebra `𝒮' ⊆ 𝒜`. -/
def VNSub.restrict (S' : StarSubalgebra ℂ A) : StarSubalgebra ℂ (VNSub A S hS) :=
  S'.comap (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))

omit [VonNeumannAlgebra A] in
@[simp] theorem VNSub.mem_restrict (S' : StarSubalgebra ℂ A) (x : VNSub A S hS) :
    x ∈ VNSub.restrict hS S' ↔ x.val ∈ S' := Iff.rfl

omit [VonNeumannAlgebra A] in
theorem VNSub.restrict_self : VNSub.restrict hS S = ⊤ :=
  SetLike.ext fun x => ⟨fun _ => trivial, fun _ => x.property⟩

omit [VonNeumannAlgebra A] in
theorem VNSub.restrict_inf (S₁ S₂ : StarSubalgebra ℂ A) :
    VNSub.restrict hS (S₁ ⊓ S₂) = VNSub.restrict hS S₁ ⊓ VNSub.restrict hS S₂ :=
  rfl

omit [VonNeumannAlgebra A] in
/-- A `∗`-subalgebra of a bundled von Neumann subalgebra `𝒮 ⊆ 𝒜` is the
trace on `𝒮` of its image in `𝒜`. -/
theorem VNSub.restrict_map_val (T : StarSubalgebra ℂ (VNSub A S hS)) :
    VNSub.restrict hS
        (T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS))) = T := by
  refine SetLike.ext fun x => ?_
  constructor
  · rintro ⟨t, ht, hte⟩
    exact (VNSub.val_injective hte : t = x) ▸ ht
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [VonNeumannAlgebra A] in
theorem VNSub.map_val_le (T : StarSubalgebra ℂ (VNSub A S hS)) :
    T.map (VNSub.valStarAlgHom (A := A) (S := S) (hS := hS)) ≤ S := by
  rintro _ ⟨t, -, rfl⟩
  exact t.property

end WstarVNSub

section TensorSub2

variable {𝒜 : Type u} {ℬ : Type v}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [VonNeumannAlgebra ℬ]

/-- The two-sided companion of `tensorSub`: the von Neumann subalgebra
`𝒮 ⊗ 𝒯 ⊆ 𝒜 ⊗ ℬ` generated by the `s ⊗ t` with `s ∈ 𝒮`, `t ∈ 𝒯`.
(`tensorSub` is the special case `𝒯 = ⊤`, see `tensorSub_eq_tensorSub₂`.) -/
def tensorSub₂ (S : StarSubalgebra ℂ 𝒜) (T : StarSubalgebra ℂ ℬ) :
    StarSubalgebra ℂ (VNT 𝒜 ℬ) :=
  wstar (VNT 𝒜 ℬ) {x : VNT 𝒜 ℬ | ∃ a ∈ S, ∃ b ∈ T, x = a ⊗ᵥ b}

/-- `tensorSub` is `tensorSub₂` with a full second factor. -/
theorem tensorSub_eq_tensorSub₂ (S : StarSubalgebra ℂ 𝒜) :
    tensorSub ℬ S = tensorSub₂ S (⊤ : StarSubalgebra ℂ ℬ) := by
  refine congrArg (wstar (VNT 𝒜 ℬ)) ?_
  ext x
  constructor
  · rintro ⟨s, hs, b, rfl⟩
    exact ⟨s, hs, b, StarSubalgebra.mem_top, rfl⟩
  · rintro ⟨s, hs, b, -, rfl⟩
    exact ⟨s, hs, b, rfl⟩

end TensorSub2

section ConcreteBridge

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The concrete tensor product `𝒜 ⊗ ℬ ⊆ B(ℋ ⊗ 𝒦)` bundled as an algebra
in its own right. -/
abbrev ConcreteTensorAlg (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) : Type u :=
  VNSub (HT H K →L[ℂ] HT H K) (concreteTensor H K SA SB)
    (isVNSubalgebra_concreteTensor SA SB)

/-- **The bridge**, existence form: for von Neumann subalgebras
`𝒜 ⊆ B(ℋ)` and `ℬ ⊆ B(𝒦)` there is a unique nmiu-isomorphism from the
*concrete* tensor product `W*(𝒜 ⊙ ℬ) ⊆ B(ℋ ⊗ 𝒦)` to the *chosen*
tensor product `𝒜 ⊗ ℬ` sending `a ⊗ b` to `a ⊗ᵥ b`.

This is 111VII `special_tensor` (the concrete tensor product *is* a
tensor product in the abstract sense) fed to 114II `tensor_uniqueness`
(the abstract tensor product is unique up to a unique nmiu-isomorphism
respecting the elementary tensors). -/
theorem exists_concreteTensorEquiv (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (hSA : IsVNSubalgebra (H →L[ℂ] H) SA) (hSB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    ∃ φ : NMIUMap (ConcreteTensorAlg SA SB)
        (VNT (VNSub (H →L[ℂ] H) SA hSA) (VNSub (K →L[ℂ] K) SB hSB)),
      Function.Bijective ⇑φ ∧
      (∀ (x : ConcreteTensorAlg SA SB) (a : VNSub (H →L[ℂ] H) SA hSA)
          (b : VNSub (K →L[ℂ] K) SB hSB),
        x.val = opTensor a.val b.val → φ x = a ⊗ᵥ b) ∧
      (∀ ψ : NMIUMap (ConcreteTensorAlg SA SB)
          (VNT (VNSub (H →L[ℂ] H) SA hSA) (VNSub (K →L[ℂ] K) SB hSB)),
        (∀ (x : ConcreteTensorAlg SA SB) (a : VNSub (H →L[ℂ] H) SA hSA)
            (b : VNSub (K →L[ℂ] K) SB hSB),
          x.val = opTensor a.val b.val → ψ x = a ⊗ᵥ b) → ψ = φ) := by
  obtain ⟨γ, hγval, hγ⟩ := special_tensor SA SB hSA hSB
  obtain ⟨φ, hφ, hbij, huniq⟩ := tensor_uniqueness γ
    (vnTensor (VNSub (H →L[ℂ] H) SA hSA) (VNSub (K →L[ℂ] K) SB hSB)).map hγ
    (vnTensor (VNSub (H →L[ℂ] H) SA hSA) (VNSub (K →L[ℂ] K) SB hSB)).isTensorProduct
  refine ⟨φ, hbij, ?_, ?_⟩
  · intro x a b hx
    have hxe : x = γ a b := VNSub.val_injective (by rw [hx, hγval])
    rw [hxe]
    exact hφ a b
  · exact fun ψ hψ => huniq ψ fun a b => hψ (γ a b) a b (hγval a b)

/-- **The bridge**: the canonical nmiu-isomorphism
`W*(𝒜 ⊙ ℬ) ≅ 𝒜 ⊗ ℬ`. -/
def concreteTensorEquiv (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (hSA : IsVNSubalgebra (H →L[ℂ] H) SA) (hSB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    NMIUMap (ConcreteTensorAlg SA SB)
      (VNT (VNSub (H →L[ℂ] H) SA hSA) (VNSub (K →L[ℂ] K) SB hSB)) :=
  (exists_concreteTensorEquiv SA SB hSA hSB).choose

theorem concreteTensorEquiv_bijective (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (hSA : IsVNSubalgebra (H →L[ℂ] H) SA) (hSB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    Function.Bijective ⇑(concreteTensorEquiv SA SB hSA hSB) :=
  (exists_concreteTensorEquiv SA SB hSA hSB).choose_spec.1

/-- The bridge sends `a ⊗ b` to `a ⊗ᵥ b`. -/
theorem concreteTensorEquiv_opTensor {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hSA : IsVNSubalgebra (H →L[ℂ] H) SA) (hSB : IsVNSubalgebra (K →L[ℂ] K) SB)
    (x : ConcreteTensorAlg SA SB) (a : VNSub (H →L[ℂ] H) SA hSA)
    (b : VNSub (K →L[ℂ] K) SB hSB) (hx : x.val = opTensor a.val b.val) :
    concreteTensorEquiv SA SB hSA hSB x = a ⊗ᵥ b :=
  (exists_concreteTensorEquiv SA SB hSA hSB).choose_spec.2.1 x a b hx

end ConcreteBridge

section AbstractTransport

variable {𝒜 𝒜' ℬ ℬ' : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
  [CStarAlgebra 𝒜'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [VonNeumannAlgebra 𝒜']
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [VonNeumannAlgebra ℬ]
  [CStarAlgebra ℬ'] [PartialOrder ℬ'] [StarOrderedRing ℬ'] [VonNeumannAlgebra ℬ']

/-- The image of a `∗`-subalgebra under an nmiu-isomorphism is the preimage
under the inverse. -/
theorem starSubalgebra_map_eq_comap (u : NMIUMap 𝒜 𝒜')
    (hu : Function.Bijective ⇑u) (S : StarSubalgebra ℂ 𝒜) :
    S.map u.toStarAlgHom = S.comap (nmiuSymm u hu).toStarAlgHom := by
  refine SetLike.ext fun x => ?_
  constructor
  · rintro ⟨s, hs, rfl⟩
    show nmiuSymm u hu (u s) ∈ S
    rw [nmiuSymm_apply_apply]
    exact hs
  · intro hx
    exact ⟨nmiuSymm u hu x, hx, nmiuSymm_apply_apply' u hu x⟩

/-- A von Neumann subalgebra is carried to one by an nmiu-isomorphism. -/
theorem isVNSubalgebra_nmiu_map (u : NMIUMap 𝒜 𝒜') (hu : Function.Bijective ⇑u)
    (S : StarSubalgebra ℂ 𝒜) (hS : IsVNSubalgebra 𝒜 S) :
    IsVNSubalgebra 𝒜' (S.map u.toStarAlgHom) := by
  rw [starSubalgebra_map_eq_comap u hu]
  exact isVNSubalgebra_comap _ (nmiuSymm u hu).preservesDirSups' _ hS

omit [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra 𝒜'] in
theorem starSubalgebra_map_top (u : NMIUMap 𝒜 𝒜') (hu : Function.Surjective ⇑u) :
    (⊤ : StarSubalgebra ℂ 𝒜).map u.toStarAlgHom = ⊤ := by
  refine SetLike.ext fun x => ⟨fun _ => StarSubalgebra.mem_top, fun _ => ?_⟩
  obtain ⟨a, ha⟩ := hu x
  exact ⟨a, StarSubalgebra.mem_top, ha⟩

theorem starSubalgebra_map_inf (u : NMIUMap 𝒜 𝒜') (hu : Function.Bijective ⇑u)
    (S T : StarSubalgebra ℂ 𝒜) :
    (S ⊓ T).map u.toStarAlgHom = S.map u.toStarAlgHom ⊓ T.map u.toStarAlgHom := by
  rw [starSubalgebra_map_eq_comap u hu, starSubalgebra_map_eq_comap u hu,
    starSubalgebra_map_eq_comap u hu]
  rfl

/-- The chosen tensor product is functorial for nmiu-isomorphisms: nmiu-isos
`u : 𝒜 ≅ 𝒜'` and `v : ℬ ≅ ℬ'` induce an nmiu-iso `𝒜 ⊗ ℬ ≅ 𝒜' ⊗ ℬ'`
sending `a ⊗ᵥ b` to `u a ⊗ᵥ v b`.  (114II again: `(a, b) ↦ u a ⊗ᵥ v b` is
a tensor product of `𝒜` and `ℬ` by `isTensorProduct_comp`.) -/
theorem exists_vntEquiv (u : NMIUMap 𝒜 𝒜') (hu : Function.Bijective ⇑u)
    (v : NMIUMap ℬ ℬ') (hv : Function.Bijective ⇑v) :
    ∃ Θ : NMIUMap (VNT 𝒜 ℬ) (VNT 𝒜' ℬ'),
      Function.Bijective ⇑Θ ∧ ∀ (a : 𝒜) (b : ℬ), Θ (a ⊗ᵥ b) = u a ⊗ᵥ v b := by
  have hγ : IsTensorProduct
      (((vnTensor 𝒜' ℬ').map).compl₁₂ (nmiuLin u) (nmiuLin v)) :=
    isTensorProduct_comp u hu v hv (vnTensor 𝒜' ℬ').isTensorProduct
  obtain ⟨Θ, hΘ, hbij, -⟩ := tensor_uniqueness (vnTensor 𝒜 ℬ).map _
    (vnTensor 𝒜 ℬ).isTensorProduct hγ
  exact ⟨Θ, hbij, fun a b => hΘ a b⟩

/-- Such an nmiu-iso carries `tensorSub₂` to `tensorSub₂`. -/
theorem mem_tensorSub₂_map (u : NMIUMap 𝒜 𝒜') (v : NMIUMap ℬ ℬ')
    (Θ : NMIUMap (VNT 𝒜 ℬ) (VNT 𝒜' ℬ')) (hΘbij : Function.Bijective ⇑Θ)
    (hΘ : ∀ (a : 𝒜) (b : ℬ), Θ (a ⊗ᵥ b) = u a ⊗ᵥ v b)
    (S : StarSubalgebra ℂ 𝒜) (T : StarSubalgebra ℂ ℬ) (x : VNT 𝒜 ℬ) :
    Θ x ∈ tensorSub₂ (S.map u.toStarAlgHom) (T.map v.toStarAlgHom) ↔
      x ∈ tensorSub₂ S T := by
  have himg : ⇑Θ '' {t : VNT 𝒜 ℬ | ∃ a ∈ S, ∃ b ∈ T, t = a ⊗ᵥ b} =
      {t : VNT 𝒜' ℬ' | ∃ a ∈ S.map u.toStarAlgHom, ∃ b ∈ T.map v.toStarAlgHom,
        t = a ⊗ᵥ b} := by
    ext t
    constructor
    · rintro ⟨z, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨u a, ⟨a, ha, rfl⟩, v b, ⟨b, hb, rfl⟩, hΘ a b⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a ⊗ᵥ b, ⟨a, ha, b, hb, rfl⟩, hΘ a b⟩
  rw [tensorSub₂, ← himg, mem_wstar_image_iff Θ hΘbij _ x]
  exact Iff.rfl

end AbstractTransport

section ConcreteTransport

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
  (hSA : IsVNSubalgebra (H →L[ℂ] H) SA) (hSB : IsVNSubalgebra (K →L[ℂ] K) SB)

/-- The bridge carries `concreteTensor` to `tensorSub₂`: for von Neumann
subalgebras `𝒜' ⊆ 𝒜 ⊆ B(ℋ)` and `ℬ' ⊆ ℬ ⊆ B(𝒦)`, an element of
`W*(𝒜 ⊙ ℬ)` lies in `W*(𝒜' ⊙ ℬ')` exactly when its image under the
bridge lies in `𝒜' ⊗ ℬ' ⊆ 𝒜 ⊗ ℬ`.

This is the statement that makes 121II — a fact about `⊓` of
`concreteTensor`s — say something about `⊓` of `tensorSub₂`s. -/
theorem concreteTensorEquiv_mem_tensorSub₂
    (SA' : StarSubalgebra ℂ (H →L[ℂ] H)) (SB' : StarSubalgebra ℂ (K →L[ℂ] K))
    (hA' : SA' ≤ SA) (hB' : SB' ≤ SB) (x : ConcreteTensorAlg SA SB) :
    concreteTensorEquiv SA SB hSA hSB x ∈
        tensorSub₂ (VNSub.restrict hSA SA') (VNSub.restrict hSB SB') ↔
      x.val ∈ concreteTensor H K SA' SB' := by
  set φ := concreteTensorEquiv SA SB hSA hSB with hφdef
  set Gc : Set (HT H K →L[ℂ] HT H K) :=
    {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA', ∃ b ∈ SB', x = opTensor a b} with hGc
  set G' : Set (ConcreteTensorAlg SA SB) := {y | y.val ∈ Gc} with hG'
  have hGsub : Gc ⊆ (concreteTensor H K SA SB : Set (HT H K →L[ℂ] HT H K)) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact opTensor_mem_concreteTensor (hA' ha) (hB' hb)
  have himg : ⇑φ '' G' =
      {t : VNT (VNSub (H →L[ℂ] H) SA hSA) (VNSub (K →L[ℂ] K) SB hSB) |
        ∃ a ∈ VNSub.restrict hSA SA', ∃ b ∈ VNSub.restrict hSB SB', t = a ⊗ᵥ b} := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hz
      exact ⟨⟨a, hA' ha⟩, ha, ⟨b, hB' hb⟩, hb,
        concreteTensorEquiv_opTensor hSA hSB z ⟨a, hA' ha⟩ ⟨b, hB' hb⟩ hab⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨⟨opTensor a.val b.val,
        opTensor_mem_concreteTensor a.property b.property⟩, ?_, ?_⟩
      · exact ⟨a.val, ha, b.val, hb, rfl⟩
      · exact concreteTensorEquiv_opTensor hSA hSB _ a b rfl
  rw [tensorSub₂, ← himg,
    mem_wstar_image_iff φ (concreteTensorEquiv_bijective SA SB hSA hSB) G' x,
    hG', mem_wstar_vnsub_iff Gc hGsub x]
  exact Iff.rfl

/-- **Transport of 121II**, two-sided form: a `⊓`-identity for concrete
tensor products becomes the corresponding `⊓`-identity for `tensorSub₂`
inside the chosen tensor product `𝒜 ⊗ ℬ`.  The hypothesis `h121` is
exactly `intersection_tensor` (121II) for the four subalgebras
concerned. -/
theorem tensorSub₂_inf_of_intersection_tensor
    (SA₁ SA₂ : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB₁ SB₂ : StarSubalgebra ℂ (K →L[ℂ] K))
    (hA₁ : SA₁ ≤ SA) (hA₂ : SA₂ ≤ SA) (hB₁ : SB₁ ≤ SB) (hB₂ : SB₂ ≤ SB)
    (h121 : concreteTensor H K SA₁ SB₁ ⊓ concreteTensor H K SA₂ SB₂ =
      concreteTensor H K (SA₁ ⊓ SA₂) (SB₁ ⊓ SB₂)) :
    tensorSub₂ (VNSub.restrict hSA SA₁) (VNSub.restrict hSB SB₁) ⊓
        tensorSub₂ (VNSub.restrict hSA SA₂) (VNSub.restrict hSB SB₂) =
      tensorSub₂ (VNSub.restrict hSA (SA₁ ⊓ SA₂))
        (VNSub.restrict hSB (SB₁ ⊓ SB₂)) := by
  refine SetLike.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (concreteTensorEquiv_bijective SA SB hSA hSB).2 y
  have e1 := concreteTensorEquiv_mem_tensorSub₂ hSA hSB SA₁ SB₁ hA₁ hB₁ x
  have e2 := concreteTensorEquiv_mem_tensorSub₂ hSA hSB SA₂ SB₂ hA₂ hB₂ x
  have e3 := concreteTensorEquiv_mem_tensorSub₂ hSA hSB (SA₁ ⊓ SA₂) (SB₁ ⊓ SB₂)
    (le_trans inf_le_left hA₁) (le_trans inf_le_left hB₁) x
  have hinf : x.val ∈ concreteTensor H K (SA₁ ⊓ SA₂) (SB₁ ⊓ SB₂) ↔
      (x.val ∈ concreteTensor H K SA₁ SB₁ ∧
        x.val ∈ concreteTensor H K SA₂ SB₂) := by
    rw [← h121]; exact Iff.rfl
  constructor
  · intro h
    exact e3.mpr (hinf.mpr ⟨e1.mp h.1, e2.mp h.2⟩)
  · intro h
    obtain ⟨h1, h2⟩ := hinf.mp (e3.mp h)
    exact ⟨e1.mpr h1, e2.mpr h2⟩

end ConcreteTransport

section AbstractIntersection

variable {𝒜 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]

/-- The statement of **121II** `intersection_tensor`, packaged as a
proposition so that it can be taken as a hypothesis: for von Neumann
subalgebras `𝒜₁, 𝒜₂ ⊆ B(ℋ)` and `ℬ₁, ℬ₂ ⊆ B(𝒦)`,
`(𝒜₁ ⊗ ℬ₁) ∩ (𝒜₂ ⊗ ℬ₂) = (𝒜₁ ∩ 𝒜₂) ⊗ (ℬ₁ ∩ ℬ₂)` for the *concrete*
tensor products.  (`intersection_tensor` is exactly a proof of this.) -/
def IntersectionTensorStatement : Prop :=
  ∀ {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (SA₁ SA₂ : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB₁ SB₂ : StarSubalgebra ℂ (K →L[ℂ] K)),
    IsVNSubalgebra (H →L[ℂ] H) SA₁ → IsVNSubalgebra (H →L[ℂ] H) SA₂ →
    IsVNSubalgebra (K →L[ℂ] K) SB₁ → IsVNSubalgebra (K →L[ℂ] K) SB₂ →
    concreteTensor H K SA₁ SB₁ ⊓ concreteTensor H K SA₂ SB₂ =
      concreteTensor H K (SA₁ ⊓ SA₂) (SB₁ ⊓ SB₂)

set_option maxHeartbeats 1000000 in
/-- **The abstract form of 121II**, one-sided: granted the concrete 121II, for
von Neumann subalgebras
`𝒮₁, 𝒮₂ ⊆ 𝒜` and any von Neumann algebra `𝒞`,
`(𝒮₁ ⊗ 𝒞) ∩ (𝒮₂ ⊗ 𝒞) = (𝒮₁ ∩ 𝒮₂) ⊗ 𝒞` inside the chosen tensor
product `𝒜 ⊗ 𝒞`.

The proof realises `𝒜` and `𝒞` concretely (111X `ngns_ulift`), transports
everything along the resulting nmiu-isomorphisms (`exists_vntEquiv`,
`mem_tensorSub₂_map`) and along the bridge `concreteTensorEquiv`, and
applies the concrete statement there.

⚠ **125IV does not consume this form.**  It needs the *two-sided*
`EqL.tensorSub₂_inf_of_intersectionTensorStatement` below, because the
intersection it takes, `(𝒜̃ ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)`, varies in both factors.
Its only consumer is `tensorSub_inf` just below, which has none. -/
theorem tensorSub_inf_of_intersectionTensorStatement
    (h121 : IntersectionTensorStatement.{u})
    (S₁ S₂ : StarSubalgebra ℂ 𝒜) (hS₁ : IsVNSubalgebra 𝒜 S₁)
    (hS₂ : IsVNSubalgebra 𝒜 S₂) :
    tensorSub 𝒞 S₁ ⊓ tensorSub 𝒞 S₂ = tensorSub 𝒞 (S₁ ⊓ S₂) := by
  obtain ⟨ι, f, SA, hSA, hfmem, hfsurj, hfinj⟩ := ngns_ulift.{u, u} 𝒜
  obtain ⟨κ, g, SB, hSB, hgmem, hgsurj, hginj⟩ := ngns_ulift.{u, u} 𝒞
  set u₀ := nmiuCorestrict f SA hSA hfmem with hu₀
  have hu : Function.Bijective ⇑u₀ :=
    nmiuCorestrict_bijective f SA hSA hfmem hfinj hfsurj
  set v₀ := nmiuCorestrict g SB hSB hgmem with hv₀
  have hv : Function.Bijective ⇑v₀ :=
    nmiuCorestrict_bijective g SB hSB hgmem hginj hgsurj
  obtain ⟨Θ, hΘbij, hΘ⟩ := exists_vntEquiv u₀ hu v₀ hv
  set T₁ := S₁.map u₀.toStarAlgHom with hT₁
  set T₂ := S₂.map u₀.toStarAlgHom with hT₂
  set SA₁ := T₁.map VNSub.valStarAlgHom with hSA₁def
  set SA₂ := T₂.map VNSub.valStarAlgHom with hSA₂def
  have hr₁ : T₁ = VNSub.restrict hSA SA₁ := (VNSub.restrict_map_val T₁).symm
  have hr₂ : T₂ = VNSub.restrict hSA SA₂ := (VNSub.restrict_map_val T₂).symm
  have hVN₁ : IsVNSubalgebra _ SA₁ :=
    vnsub_isVNSubalgebra_map T₁ (isVNSubalgebra_nmiu_map u₀ hu S₁ hS₁)
  have hVN₂ : IsVNSubalgebra _ SA₂ :=
    vnsub_isVNSubalgebra_map T₂ (isVNSubalgebra_nmiu_map u₀ hu S₂ hS₂)
  have hle₁ : SA₁ ≤ SA := VNSub.map_val_le T₁
  have hle₂ : SA₂ ≤ SA := VNSub.map_val_le T₂
  have key : ∀ (S : StarSubalgebra ℂ 𝒜) (x : VNT 𝒜 𝒞),
      x ∈ tensorSub 𝒞 S ↔
        Θ x ∈ tensorSub₂ (S.map u₀.toStarAlgHom) (VNSub.restrict hSB SB) := by
    intro S x
    have h1 : VNSub.restrict hSB SB
        = (⊤ : StarSubalgebra ℂ 𝒞).map v₀.toStarAlgHom := by
      rw [starSubalgebra_map_top v₀ hv.2, VNSub.restrict_self]
    rw [tensorSub_eq_tensorSub₂, h1]
    exact (mem_tensorSub₂_map u₀ v₀ Θ hΘbij hΘ S ⊤ x).symm
  have hmain := tensorSub₂_inf_of_intersection_tensor hSA hSB SA₁ SA₂ SB SB
    hle₁ hle₂ le_rfl le_rfl (h121 SA₁ SA₂ SB SB hVN₁ hVN₂ hSB hSB)
  rw [show SB ⊓ SB = SB from inf_idem _] at hmain
  have hT12 : (S₁ ⊓ S₂).map u₀.toStarAlgHom = VNSub.restrict hSA (SA₁ ⊓ SA₂) := by
    rw [starSubalgebra_map_inf u₀ hu, VNSub.restrict_inf, ← hr₁, ← hr₂]
  refine SetLike.ext fun x => ?_
  have k1 := key S₁ x
  have k2 := key S₂ x
  have k3 := key (S₁ ⊓ S₂) x
  rw [← hT₁, hr₁] at k1
  rw [← hT₂, hr₂] at k2
  rw [hT12] at k3
  constructor
  · rintro ⟨h1, h2⟩
    refine k3.mpr ?_
    rw [← hmain]
    exact ⟨k1.mp h1, k2.mp h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := (hmain ▸ k3.mp h : _ ∈ _ ⊓ _)
    exact ⟨k1.mpr h1, k2.mpr h2⟩

end AbstractIntersection

section AbstractIntersectionUnconditional

/-- 121II, packaged as `IntersectionTensorStatement` — the hypothesis its
six downstream consumers were phrased against. -/
theorem intersectionTensorStatement : IntersectionTensorStatement.{u} :=
  fun SA₁ SA₂ SB₁ SB₂ hA₁ hA₂ hB₁ hB₂ =>
    intersection_tensor SA₁ SA₂ SB₁ SB₂ hA₁ hA₂ hB₁ hB₂

/-- **The abstract form of 121II**, unconditional: for von Neumann subalgebras
`𝒮₁, 𝒮₂ ⊆ 𝒜` and any von Neumann algebra `𝒞`,

  `(𝒮₁ ⊗ 𝒞) ∩ (𝒮₂ ⊗ 𝒞) = (𝒮₁ ∩ 𝒮₂) ⊗ 𝒞`

inside the chosen tensor product `𝒜 ⊗ 𝒞`.  This is
`tensorSub_inf_of_intersectionTensorStatement` with its hypothesis discharged.

⚠ **Nothing consumes this.**  125IV `equaliser_lemma` goes through the
*two-sided* `EqL.tensorSub₂_inf_of_intersectionTensorStatement` below, whose
intersection `(𝒜̃ ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)` varies in both factors; this
one-sided form is kept on the record as the unconditional statement of the
abstract 121II. -/
theorem tensorSub_inf {𝒜 𝒞 : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    (S₁ S₂ : StarSubalgebra ℂ 𝒜) (hS₁ : IsVNSubalgebra 𝒜 S₁)
    (hS₂ : IsVNSubalgebra 𝒜 S₂) :
    tensorSub 𝒞 S₁ ⊓ tensorSub 𝒞 S₂ = tensorSub 𝒞 (S₁ ⊓ S₂) :=
  tensorSub_inf_of_intersectionTensorStatement intersectionTensorStatement S₁ S₂ hS₁ hS₂

end AbstractIntersectionUnconditional

/-! ## Parsec 1250, continued: **125IV** `equaliser-lemma`

The proof of 125IV (proc.tex:4852, Lemma (Kornell)) needs the *two-sided*
abstract form of 121II — `tensorSub₂_inf_of_intersectionTensorStatement`
below — and hence everything in this file down to `tensorSub₂`; that is why
it sits here, at the end, rather than beside the other parsec-1250
statements above.

Everything auxiliary is kept in the namespace `EqL`. -/

section Polarisation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The polarisation identity in the form used by proc.tex:4930
(`eq:polarisation-equaliser`): the off-diagonal matrix entry `⟪ξ, T ζ⟫` is
a combination of the four diagonal entries `⟪i^m ξ + ζ, T (i^m ξ + ζ)⟫`. -/
theorem inner_polarisation (T : H →L[ℂ] H) (ξ ζ : H) :
    ⟪ξ + ζ, T (ξ + ζ)⟫
        + Complex.I * ⟪Complex.I • ξ + ζ, T (Complex.I • ξ + ζ)⟫
        - ⟪(-1 : ℂ) • ξ + ζ, T ((-1 : ℂ) • ξ + ζ)⟫
        - Complex.I * ⟪(-Complex.I) • ξ + ζ, T ((-Complex.I) • ξ + ζ)⟫
      = 4 * ⟪ξ, T ζ⟫ := by
  have hexp : ∀ c : ℂ, ⟪c • ξ + ζ, T (c • ξ + ζ)⟫
      = (starRingEnd ℂ) c * c * ⟪ξ, T ξ⟫ + (starRingEnd ℂ) c * ⟪ξ, T ζ⟫
        + c * ⟪ζ, T ξ⟫ + ⟪ζ, T ζ⟫ := by
    intro c
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    ring
  have h1 : ⟪ξ + ζ, T (ξ + ζ)⟫ = ⟪(1 : ℂ) • ξ + ζ, T ((1 : ℂ) • ξ + ζ)⟫ := by
    rw [one_smul]
  rw [h1, hexp, hexp, hexp, hexp]
  simp only [map_one, Complex.conj_I, map_neg, neg_neg]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (2 * ⟪ζ, T ξ⟫ - 2 * ⟪ξ, T ζ⟫) * hI

end Polarisation


namespace EqL

theorem nmiuTmulLeft_injective [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [Nontrivial B] : Function.Injective ⇑(nmiuTmulLeft A B) := by
  intro x y hxy
  have h0 : (x - y) ⊗ᵥ (1 : B) = 0 := by
    have h2 : ((x - y) ⊗ᵥ (1 : B)) = x ⊗ᵥ (1 : B) - y ⊗ᵥ (1 : B) := by
      show (vnTensor A B).map (x - y) 1 = _
      rw [map_sub]
      rfl
    rw [h2, show (x ⊗ᵥ (1 : B)) = nmiuTmulLeft A B x from rfl,
      show (y ⊗ᵥ (1 : B)) = nmiuTmulLeft A B y from rfl, hxy, sub_self]
  have hn : ‖x - y‖ * ‖(1 : B)‖ = 0 := by
    rw [← norm_vtmul, h0, norm_zero]
  rw [norm_one, mul_one, norm_eq_zero, sub_eq_zero] at hn
  exact hn

set_option maxHeartbeats 1000000 in
/-- **The two-sided abstract form of 121II**: granted the concrete 121II,
for von Neumann subalgebras `𝒮₁, 𝒮₂ ⊆ 𝒜` and `𝒯₁, 𝒯₂ ⊆ 𝒞`,
`(𝒮₁ ⊗ 𝒯₁) ∩ (𝒮₂ ⊗ 𝒯₂) = (𝒮₁ ∩ 𝒮₂) ⊗ (𝒯₁ ∩ 𝒯₂)` inside the chosen
tensor product `𝒜 ⊗ 𝒞`.

This is `tensorSub_inf_of_intersectionTensorStatement` above with both
factors allowed to vary; 125IV needs the
two-sided form, because the intersection it takes is
`(𝒜̃ ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)`. -/
theorem tensorSub₂_inf_of_intersectionTensorStatement
    {𝒜 𝒞 : Type u}
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    (h121 : IntersectionTensorStatement.{u})
    (S₁ S₂ : StarSubalgebra ℂ 𝒜) (hS₁ : IsVNSubalgebra 𝒜 S₁)
    (hS₂ : IsVNSubalgebra 𝒜 S₂)
    (T₁ T₂ : StarSubalgebra ℂ 𝒞) (hT₁ : IsVNSubalgebra 𝒞 T₁)
    (hT₂ : IsVNSubalgebra 𝒞 T₂) :
    tensorSub₂ S₁ T₁ ⊓ tensorSub₂ S₂ T₂ = tensorSub₂ (S₁ ⊓ S₂) (T₁ ⊓ T₂) := by
  obtain ⟨ι, f, SA, hSA, hfmem, hfsurj, hfinj⟩ := ngns_ulift.{u, u} 𝒜
  obtain ⟨κ, g, SB, hSB, hgmem, hgsurj, hginj⟩ := ngns_ulift.{u, u} 𝒞
  set u₀ := nmiuCorestrict f SA hSA hfmem with hu₀
  have hu : Function.Bijective ⇑u₀ :=
    nmiuCorestrict_bijective f SA hSA hfmem hfinj hfsurj
  set v₀ := nmiuCorestrict g SB hSB hgmem with hv₀
  have hv : Function.Bijective ⇑v₀ :=
    nmiuCorestrict_bijective g SB hSB hgmem hginj hgsurj
  obtain ⟨Θ, hΘbij, hΘ⟩ := exists_vntEquiv u₀ hu v₀ hv
  -- the four images, first in the bundled subalgebras and then in `B(ℋ)`
  set SA₁ := (S₁.map u₀.toStarAlgHom).map VNSub.valStarAlgHom with hSA₁def
  set SA₂ := (S₂.map u₀.toStarAlgHom).map VNSub.valStarAlgHom with hSA₂def
  set SB₁ := (T₁.map v₀.toStarAlgHom).map VNSub.valStarAlgHom with hSB₁def
  set SB₂ := (T₂.map v₀.toStarAlgHom).map VNSub.valStarAlgHom with hSB₂def
  have hrA₁ : S₁.map u₀.toStarAlgHom = VNSub.restrict hSA SA₁ :=
    (VNSub.restrict_map_val _).symm
  have hrA₂ : S₂.map u₀.toStarAlgHom = VNSub.restrict hSA SA₂ :=
    (VNSub.restrict_map_val _).symm
  have hrB₁ : T₁.map v₀.toStarAlgHom = VNSub.restrict hSB SB₁ :=
    (VNSub.restrict_map_val _).symm
  have hrB₂ : T₂.map v₀.toStarAlgHom = VNSub.restrict hSB SB₂ :=
    (VNSub.restrict_map_val _).symm
  have hVNA₁ : IsVNSubalgebra _ SA₁ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map u₀ hu S₁ hS₁)
  have hVNA₂ : IsVNSubalgebra _ SA₂ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map u₀ hu S₂ hS₂)
  have hVNB₁ : IsVNSubalgebra _ SB₁ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map v₀ hv T₁ hT₁)
  have hVNB₂ : IsVNSubalgebra _ SB₂ :=
    vnsub_isVNSubalgebra_map _ (isVNSubalgebra_nmiu_map v₀ hv T₂ hT₂)
  have hleA₁ : SA₁ ≤ SA := VNSub.map_val_le _
  have hleA₂ : SA₂ ≤ SA := VNSub.map_val_le _
  have hleB₁ : SB₁ ≤ SB := VNSub.map_val_le _
  have hleB₂ : SB₂ ≤ SB := VNSub.map_val_le _
  have key : ∀ (S : StarSubalgebra ℂ 𝒜) (T : StarSubalgebra ℂ 𝒞) (x : VNT 𝒜 𝒞),
      x ∈ tensorSub₂ S T ↔
        Θ x ∈ tensorSub₂ (S.map u₀.toStarAlgHom) (T.map v₀.toStarAlgHom) :=
    fun S T x => (mem_tensorSub₂_map u₀ v₀ Θ hΘbij hΘ S T x).symm
  have hmain := tensorSub₂_inf_of_intersection_tensor hSA hSB SA₁ SA₂ SB₁ SB₂
    hleA₁ hleA₂ hleB₁ hleB₂ (h121 SA₁ SA₂ SB₁ SB₂ hVNA₁ hVNA₂ hVNB₁ hVNB₂)
  have hA12 : (S₁ ⊓ S₂).map u₀.toStarAlgHom = VNSub.restrict hSA (SA₁ ⊓ SA₂) := by
    rw [starSubalgebra_map_inf u₀ hu, VNSub.restrict_inf, ← hrA₁, ← hrA₂]
  have hB12 : (T₁ ⊓ T₂).map v₀.toStarAlgHom = VNSub.restrict hSB (SB₁ ⊓ SB₂) := by
    rw [starSubalgebra_map_inf v₀ hv, VNSub.restrict_inf, ← hrB₁, ← hrB₂]
  refine SetLike.ext fun x => ?_
  have k1 := key S₁ T₁ x
  have k2 := key S₂ T₂ x
  have k3 := key (S₁ ⊓ S₂) (T₁ ⊓ T₂) x
  rw [hrA₁, hrB₁] at k1
  rw [hrA₂, hrB₂] at k2
  rw [hA12, hB12] at k3
  constructor
  · rintro ⟨h1, h2⟩
    refine k3.mpr ?_
    rw [← hmain]
    exact ⟨k1.mp h1, k2.mp h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := (hmain ▸ k3.mp h : _ ∈ _ ⊓ _)
    exact ⟨k1.mpr h1, k2.mpr h2⟩



/-! ## The slice maps `r_ξ`

For a vector `ξ` of a Hilbert space `ℋ` the thesis's `r_ξ` is the np-map
`𝒜 ⊗ 𝒞 → 𝒜` with `r_ξ(a ⊗ c) = ⟪ξ, cξ⟫ a`.  Here it is rendered as the
ncp-map `𝒜 ⊗ B(ℋ) → 𝒜 ⊗ B(ℋ)` given by `id ⊗ (b ↦ ⟪ξ, bξ⟫·1)`, whose
values all lie in the copy `𝒜 ⊗ 1` of `𝒜`; that avoids having to build
the identification `𝒜 ⊗ ℂ ≅ 𝒜`. -/

section RSlice

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem vtmul_mul_vtmul {C₀ A₀ : Type u} [CStarAlgebra C₀] [PartialOrder C₀]
    [StarOrderedRing C₀] [VonNeumannAlgebra C₀] [CStarAlgebra A₀] [PartialOrder A₀]
    [StarOrderedRing A₀] [VonNeumannAlgebra A₀] (c c' : C₀) (a a' : A₀) :
    (c ⊗ᵥ a) * (c' ⊗ᵥ a') = (c * c') ⊗ᵥ (a * a') :=
  ((vnTensor C₀ A₀).isTensorProduct.miu.2.1 c c' a a').symm

theorem vtmul_smul_right {C₀ A₀ : Type u} [CStarAlgebra C₀] [PartialOrder C₀]
    [StarOrderedRing C₀] [VonNeumannAlgebra C₀] [CStarAlgebra A₀] [PartialOrder A₀]
    [StarOrderedRing A₀] [VonNeumannAlgebra A₀] (c : C₀) (r : ℂ) (a : A₀) :
    c ⊗ᵥ (r • a) = r • (c ⊗ᵥ a) :=
  map_smul ((vnTensor C₀ A₀).map c) r a

variable (𝒜)

/-- The slice `r_ξ`, as an ncp-endomorphism of `𝒜 ⊗ B(ℋ)`. -/
def rSlice (ξ : H) : NCPMap (VNT 𝒜 (H →L[ℂ] H)) (VNT 𝒜 (H →L[ℂ] H)) :=
  tmap (ncpId 𝒜) (npScalar (vectorNP ξ))

theorem rSlice_tmul (ξ : H) (a : 𝒜) (b : H →L[ℂ] H) :
    rSlice 𝒜 ξ (a ⊗ᵥ b) = (⟪ξ, b ξ⟫ : ℂ) • (a ⊗ᵥ (1 : H →L[ℂ] H)) := by
  rw [rSlice, tmap_apply, ncpId_apply, npScalar_apply, vectorNP_apply,
    Algebra.algebraMap_eq_smul_one, vtmul_smul_right]

/-- `r_ξ` as a linear map. -/
def rSliceL (ξ : H) : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
  (rSlice 𝒜 ξ).toCompletelyPositiveMap.toLinearMap

@[simp] theorem rSliceL_apply (ξ : H) (x : VNT 𝒜 (H →L[ℂ] H)) :
    rSliceL 𝒜 ξ x = rSlice 𝒜 ξ x := rfl

theorem rSliceL_continuous (ξ : H) :
    @Continuous (VNT 𝒜 (H →L[ℂ] H)) (VNT 𝒜 (H →L[ℂ] H))
      (ultraweak _) (ultraweak _) ⇑(rSliceL 𝒜 ξ) :=
  ((p_uwcont (ncpPositive (rSlice 𝒜 ξ))).out 2 0).mp (rSlice 𝒜 ξ).preservesDirSups'

/-- Every value of `r_ξ` lies in the copy `𝒜 ⊗ 1` of `𝒜`.  The argument is
self-contained: the set of `x` whose image does is an ultraweakly closed
subspace containing the elementary tensors. -/
theorem rSlice_mem (ξ : H) (x : VNT 𝒜 (H →L[ℂ] H)) :
    ∃ a : 𝒜, rSlice 𝒜 ξ x = a ⊗ᵥ (1 : H →L[ℂ] H) := by
  let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
  have _ : T2Space (VNT 𝒜 (H →L[ℂ] H)) := vn_positive_basic_1.1
  obtain ⟨hRvn⟩ : Nonempty (IsVNSubalgebra (VNT 𝒜 (H →L[ℂ] H))
      (nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range) :=
    ⟨nmiu_image _⟩
  have hRcl : IsClosed
      ((nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range :
        Set (VNT 𝒜 (H →L[ℂ] H))) := (vnsac _ hRvn).2
  set W : Submodule ℂ (VNT 𝒜 (H →L[ℂ] H)) :=
    Submodule.comap (rSliceL 𝒜 ξ)
      (Subalgebra.toSubmodule
        (nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range.toSubalgebra) with hW
  have hWcl : IsClosed (W : Set (VNT 𝒜 (H →L[ℂ] H))) :=
    hRcl.preimage (rSliceL_continuous 𝒜 ξ)
  have hspan : (Submodule.span ℂ
      {t : VNT 𝒜 (H →L[ℂ] H) | ∃ a b, t = (vnTensor 𝒜 (H →L[ℂ] H)).map a b} :
        Set (VNT 𝒜 (H →L[ℂ] H))) ⊆ (W : Set (VNT 𝒜 (H →L[ℂ] H))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, b, rfl⟩
    have hmem : rSlice 𝒜 ξ (a ⊗ᵥ b) ∈
        (nmiuTmulLeft 𝒜 (H →L[ℂ] H)).toStarAlgHom.range := by
      rw [rSlice_tmul, ← vtmulLeft_smul]
      exact ⟨(⟪ξ, b ξ⟫ : ℂ) • a, rfl⟩
    exact hmem
  have hx : x ∈ W := by
    have hd := (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct.dense
    have hcl : x ∈ closure ((Submodule.span ℂ
        {t : VNT 𝒜 (H →L[ℂ] H) | ∃ a b, t = (vnTensor 𝒜 (H →L[ℂ] H)).map a b} :
          Set (VNT 𝒜 (H →L[ℂ] H)))) := by
      rw [hd.closure_eq]; trivial
    exact hWcl.closure_subset_iff.mpr hspan hcl
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

end RSlice



/-! ## The rank-one compressions of `𝒜 ⊗ B(ℋ)`

`eq:polarisation-equaliser` of proc.tex:4930: the compression of `x` by the
matrix units `1 ⊗ |e_k⟩⟨e_k|` and `1 ⊗ |e_l⟩⟨e_l|` is a combination of four
values of `r_ξ`, times `1 ⊗ |e_k⟩⟨e_l|`. -/

section Compression

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ιH : Type u}

/-- The polarisation identity, transported into `𝒜 ⊗ B(ℋ)`. -/
theorem tensor_polarisation (e : HilbertBasis ιH ℂ H) (k l : ιH)
    (x : VNT 𝒜 (H →L[ℂ] H)) :
    ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l)
      = ((4 : ℂ)⁻¹ • (rSlice 𝒜 (e k + e l) x
            + Complex.I • rSlice 𝒜 (Complex.I • e k + e l) x
            - rSlice 𝒜 ((-1 : ℂ) • e k + e l) x
            - Complex.I • rSlice 𝒜 ((-Complex.I) • e k + e l) x))
          * ((1 : 𝒜) ⊗ᵥ bkU e k l) := by
  let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
  have _ : T2Space (VNT 𝒜 (H →L[ℂ] H)) := vn_positive_basic_1.1
  set v0 : H := e k + e l with hv0
  set v1 : H := Complex.I • e k + e l with hv1
  set v2 : H := (-1 : ℂ) • e k + e l with hv2
  set v3 : H := (-Complex.I) • e k + e l with hv3
  set Q : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
    (4 : ℂ)⁻¹ • (rSliceL 𝒜 v0 + Complex.I • rSliceL 𝒜 v1 - rSliceL 𝒜 v2
      - Complex.I • rSliceL 𝒜 v3) with hQ
  have hQapp : ∀ y : VNT 𝒜 (H →L[ℂ] H), Q y
      = (4 : ℂ)⁻¹ • (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
          - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y) := by
    intro y
    rw [hQ]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      rSliceL_apply]
  set f : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
    (LinearMap.mulRight ℂ ((1 : 𝒜) ⊗ᵥ bkU e l l)).comp
      (LinearMap.mulLeft ℂ ((1 : 𝒜) ⊗ᵥ bkU e k k)) with hf
  set g : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) :=
    (LinearMap.mulRight ℂ ((1 : 𝒜) ⊗ᵥ bkU e k l)).comp Q with hg
  have hcf : Continuous ⇑f := continuous_uw_mulmul _ _
  have hQc : Continuous ⇑Q := by
    refine continuous_ultraweak_of_forall _ fun ν => ?_
    have hcomp : ∀ v : H, @Continuous (VNT 𝒜 (H →L[ℂ] H)) ℂ
        (ultraweak _) _ (fun y => (ν (rSlice 𝒜 v y) : ℂ)) := fun v =>
      (continuous_ultraweak_npFunctional ν).comp (rSliceL_continuous 𝒜 v)
    have hrw : (fun y : VNT 𝒜 (H →L[ℂ] H) => (ν (Q y) : ℂ))
        = fun y => (4 : ℂ)⁻¹ * ((ν (rSlice 𝒜 v0 y) : ℂ)
            + Complex.I * (ν (rSlice 𝒜 v1 y) : ℂ)
            - (ν (rSlice 𝒜 v2 y) : ℂ)
            - Complex.I * (ν (rSlice 𝒜 v3 y) : ℂ)) := by
      funext y
      rw [hQapp y,
        show (ν ((4 : ℂ)⁻¹ • (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
              - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y)) : ℂ)
            = (4 : ℂ)⁻¹ * ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
              - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y) from
          ν.toPositiveLinearMap.map_smul _ _]
      congr 1
      rw [show (ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y
              - rSlice 𝒜 v2 y - Complex.I • rSlice 𝒜 v3 y) : ℂ)
            = ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y - rSlice 𝒜 v2 y)
              - ν (Complex.I • rSlice 𝒜 v3 y) from
          map_sub ν.toPositiveLinearMap _ _,
        show (ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y - rSlice 𝒜 v2 y) : ℂ)
            = ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y)
              - ν (rSlice 𝒜 v2 y) from map_sub ν.toPositiveLinearMap _ _,
        show (ν (rSlice 𝒜 v0 y + Complex.I • rSlice 𝒜 v1 y) : ℂ)
            = ν (rSlice 𝒜 v0 y) + ν (Complex.I • rSlice 𝒜 v1 y) from
          map_add ν.toPositiveLinearMap _ _,
        show (ν (Complex.I • rSlice 𝒜 v1 y) : ℂ)
            = Complex.I * ν (rSlice 𝒜 v1 y) from
          ν.toPositiveLinearMap.map_smul _ _,
        show (ν (Complex.I • rSlice 𝒜 v3 y) : ℂ)
            = Complex.I * ν (rSlice 𝒜 v3 y) from
          ν.toPositiveLinearMap.map_smul _ _]
    rw [hrw]
    exact continuous_const.mul ((((hcomp v0).add
      (continuous_const.mul (hcomp v1))).sub (hcomp v2)).sub
        (continuous_const.mul (hcomp v3)))
  have hcg : Continuous ⇑g := by
    have h1 : Continuous (fun y : VNT 𝒜 (H →L[ℂ] H) =>
        1 * y * ((1 : 𝒜) ⊗ᵥ bkU e k l)) := continuous_uw_mulmul _ _
    simp only [one_mul] at h1
    exact h1.comp hQc
  have hQtmul : ∀ (a : 𝒜) (b : H →L[ℂ] H),
      Q (a ⊗ᵥ b) = (⟪e k, b (e l)⟫ : ℂ) • (a ⊗ᵥ (1 : H →L[ℂ] H)) := by
    intro a b
    rw [hQapp, rSlice_tmul, rSlice_tmul, rSlice_tmul, rSlice_tmul,
      smul_smul, smul_smul, ← add_smul, ← sub_smul, ← sub_smul, smul_smul]
    congr 1
    have hp := inner_polarisation b (e k) (e l)
    rw [hv0, hv1, hv2, hv3]
    linear_combination (4 : ℂ)⁻¹ * hp
  have hfg : f = g := by
    refine tensor_linear_ext (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct f g hcf hcg ?_
    intro a b
    show ((1 : 𝒜) ⊗ᵥ bkU e k k) * (a ⊗ᵥ b) * ((1 : 𝒜) ⊗ᵥ bkU e l l)
      = Q (a ⊗ᵥ b) * ((1 : 𝒜) ⊗ᵥ bkU e k l)
    rw [vtmul_mul_vtmul, vtmul_mul_vtmul, one_mul, mul_one, bkU_mul_mul',
      vtmul_smul_right, hQtmul, smul_mul_assoc, vtmul_mul_vtmul, mul_one, one_mul]
  have h : f x = g x :=
    congrFun (congrArg
      (fun L : VNT 𝒜 (H →L[ℂ] H) →ₗ[ℂ] VNT 𝒜 (H →L[ℂ] H) => ⇑L) hfg) x
  have hfx : f x = ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l) := rfl
  have hgx : g x = Q x * ((1 : 𝒜) ⊗ᵥ bkU e k l) := rfl
  rw [← hfx, h, hgx, hQapp]


/-! ### `1 ⊗ b` calculus -/

theorem vtmulR_mul (a a' : H →L[ℂ] H) :
    ((1 : 𝒜) ⊗ᵥ a) * ((1 : 𝒜) ⊗ᵥ a') = (1 : 𝒜) ⊗ᵥ (a * a') := by
  rw [vtmul_mul_vtmul, one_mul]

theorem vtmulR_star (a : H →L[ℂ] H) :
    star ((1 : 𝒜) ⊗ᵥ a) = (1 : 𝒜) ⊗ᵥ star a := by
  have h := (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct.miu.2.2 (1 : 𝒜) a
  rw [star_one] at h
  exact h

theorem vtmulR_sub (a a' : H →L[ℂ] H) :
    (1 : 𝒜) ⊗ᵥ (a - a') = ((1 : 𝒜) ⊗ᵥ a) - ((1 : 𝒜) ⊗ᵥ a') :=
  map_sub ((vnTensor 𝒜 (H →L[ℂ] H)).map 1) a a'

theorem vtmulR_one : ((1 : 𝒜) ⊗ᵥ (1 : H →L[ℂ] H)) = 1 :=
  (vnTensor 𝒜 (H →L[ℂ] H)).isTensorProduct.miu.1

theorem vtmulR_mono {a a' : H →L[ℂ] H} (h : a ≤ a') :
    ((1 : 𝒜) ⊗ᵥ a) ≤ ((1 : 𝒜) ⊗ᵥ a') := by
  have h1 := vtmul_nonneg (1 : 𝒜) (a' - a) zero_le_one (sub_nonneg.mpr h)
  rw [vtmulR_sub] at h1
  exact sub_nonneg.mp h1

/-- The compressions `1 ⊗ p_F` converge ultraweakly to `1` from both
sides. -/
theorem compress_tendsto (e : HilbertBasis ιH ℂ H) (x : VNT 𝒜 (H →L[ℂ] H)) :
    UWTendsto (fun F : Finset ιH =>
        ((1 : 𝒜) ⊗ᵥ bkP e F) * x * ((1 : 𝒜) ⊗ᵥ bkP e F)) atTop x := by
  have hmain : UWTendsto (fun F : Finset ιH =>
      ((1 : 𝒜) ⊗ᵥ bkP e F) * x * ((1 : 𝒜) ⊗ᵥ bkP e F)) atTop
      ((1 : VNT 𝒜 (H →L[ℂ] H)) * x * 1) := by
    refine uw_compress_tendsto 1 (fun F => (1 : 𝒜) ⊗ᵥ bkP e F)
      (fun F => ?_) (fun F => ?_) (fun F => ?_) ?_ x
    · rw [vtmulR_star, vtmulR_mul, bkP_star, bkP_mul_self]
    · rw [← vtmulR_one, ← vtmulR_sub, vtmulR_star, vtmulR_mul, star_sub, star_one,
        bkP_star]
      congr 1
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, bkP_mul_self]
      abel
    · rw [← vtmulR_one]
      exact vtmulR_mono (bkP_le_one e F)
    · let _ : TopologicalSpace (H →L[ℂ] H) := ultraweak (H →L[ℂ] H)
      let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
      have h : UWTendsto (bkP e) atTop (1 : H →L[ℂ] H) :=
        uwTendsto_of_isLUB (X := H →L[ℂ] H) (ι' := Finset ιH) (bkP e) 1
          (fun F => (bkP_star e F : star (bkP e F) = bkP e F))
          (fun F G hFG => bkP_mono e hFG) (bkP_isLUB e)
      have hcont : @Continuous (H →L[ℂ] H) (VNT 𝒜 (H →L[ℂ] H))
          (ultraweak (H →L[ℂ] H)) (ultraweak (VNT 𝒜 (H →L[ℂ] H)))
          (fun b : H →L[ℂ] H => (1 : 𝒜) ⊗ᵥ b) :=
        continuous_ultraweak_vtmul_right (1 : 𝒜)
      have h2 := (hcont.tendsto (1 : H →L[ℂ] H)).comp h
      rw [vtmulR_one] at h2
      exact h2
  rwa [one_mul, mul_one] at hmain

/-- The compression of `x` by `1 ⊗ p_F` is the finite sum of its rank-one
compressions. -/
theorem compress_eq_sum (e : HilbertBasis ιH ℂ H) (F : Finset ιH)
    (x : VNT 𝒜 (H →L[ℂ] H)) :
    ((1 : 𝒜) ⊗ᵥ bkP e F) * x * ((1 : 𝒜) ⊗ᵥ bkP e F)
      = ∑ k ∈ F, ∑ l ∈ F,
          ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l) := by
  have hsum : ((1 : 𝒜) ⊗ᵥ bkP e F) = ∑ k ∈ F, ((1 : 𝒜) ⊗ᵥ bkU e k k) := by
    show (vnTensor 𝒜 (H →L[ℂ] H)).map 1 (∑ k ∈ F, bkU e k k) = _
    exact map_sum ((vnTensor 𝒜 (H →L[ℂ] H)).map 1) _ _
  rw [hsum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

/-- **The containment step of proc.tex:4938**: if every slice `r_ξ(x)` of
`x` lands in `𝒮`, then `x ∈ 𝒮 ⊗ B(ℋ)`. -/
theorem mem_tensorSub_of_rSlice_mem (S : StarSubalgebra ℂ 𝒜)
    (e : HilbertBasis ιH ℂ H) (x : VNT 𝒜 (H →L[ℂ] H))
    (hx : ∀ (ξ : H) (a : 𝒜), rSlice 𝒜 ξ x = a ⊗ᵥ (1 : H →L[ℂ] H) → a ∈ S) :
    x ∈ tensorSub (H →L[ℂ] H) S := by
  let _ : TopologicalSpace (VNT 𝒜 (H →L[ℂ] H)) := ultraweak (VNT 𝒜 (H →L[ℂ] H))
  set T : StarSubalgebra ℂ (VNT 𝒜 (H →L[ℂ] H)) := tensorSub (H →L[ℂ] H) S with hT
  have hcl : @IsClosed (VNT 𝒜 (H →L[ℂ] H)) (ultraweak (VNT 𝒜 (H →L[ℂ] H)))
      ((T : StarSubalgebra ℂ (VNT 𝒜 (H →L[ℂ] H))) : Set (VNT 𝒜 (H →L[ℂ] H))) :=
    (vnsac _ (isVNSubalgebra_wstar _).1).2
  have hterm : ∀ (v : H) (k l : ιH),
      rSlice 𝒜 v x * ((1 : 𝒜) ⊗ᵥ bkU e k l) ∈ T := by
    intro v k l
    obtain ⟨a, ha⟩ := rSlice_mem 𝒜 v x
    rw [ha, vtmul_mul_vtmul, mul_one, one_mul]
    exact (isVNSubalgebra_wstar _).2 ⟨a, hx v a ha, bkU e k l, rfl⟩
  have hrank : ∀ k l : ιH,
      ((1 : 𝒜) ⊗ᵥ bkU e k k) * x * ((1 : 𝒜) ⊗ᵥ bkU e l l) ∈ T := by
    intro k l
    rw [tensor_polarisation e k l x, smul_mul_assoc, sub_mul, sub_mul, add_mul,
      smul_mul_assoc, smul_mul_assoc]
    exact SMulMemClass.smul_mem _
      (sub_mem (sub_mem (add_mem (hterm _ k l)
        (SMulMemClass.smul_mem _ (hterm _ k l))) (hterm _ k l))
        (SMulMemClass.smul_mem _ (hterm _ k l)))
  refine hcl.mem_of_tendsto (compress_tendsto e x)
    (Filter.Eventually.of_forall fun F => ?_)
  rw [SetLike.mem_coe, compress_eq_sum]
  exact sum_mem fun k _ => sum_mem fun l _ => hrank k l


end Compression



/-! ## Naturality of the slices, and the embedding `𝒜 ⊗ 𝒞 ↪ 𝒜 ⊗ B(ℋ)` -/

section Naturality

variable {𝒜 ℬ 𝒞 : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [VonNeumannAlgebra ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] in
theorem isVNSubalgebra_top' :
    IsVNSubalgebra 𝒜 (⊤ : StarSubalgebra ℂ 𝒜) := by
  refine ⟨?_, fun _ _ _ _ _ _ => StarSubalgebra.mem_top⟩
  rw [StarSubalgebra.coe_top]
  exact isClosed_univ

/-- `f ⊗ id` intertwines the slices `r_ξ` — the identity
`f ∘ r_ξ = r'_ξ ∘ (f ⊗ id)` of proc.tex:4900. -/
theorem rSlice_natural (f : NMIUMap 𝒜 ℬ) (ξ : H) (y : VNT 𝒜 (H →L[ℂ] H)) :
    tmapM f (nmiuId (H →L[ℂ] H)) (rSlice 𝒜 ξ y)
      = rSlice ℬ ξ (tmapM f (nmiuId (H →L[ℂ] H)) y) := by
  have hcomm : ncpComp (nmiuNCP (tmapM f (nmiuId (H →L[ℂ] H))))
        (tmap (ncpId 𝒜) (npScalar (vectorNP ξ)))
      = ncpComp (tmap (ncpId ℬ) (npScalar (vectorNP ξ)))
        (nmiuNCP (tmapM f (nmiuId (H →L[ℂ] H)))) := by
    refine (exists_tmap (nmiuNCP f) (npScalar (vectorNP ξ))).unique
      (fun a b => ?_) (fun a b => ?_)
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply,
        tmapM_apply, nmiuId_apply]
    · simp only [ncpComp_apply, tmap_apply, ncpId_apply, nmiuNCP_apply,
        tmapM_apply, nmiuId_apply]
  have h := congrArg
    (fun F : NCPMap (VNT 𝒜 (H →L[ℂ] H)) (VNT ℬ (H →L[ℂ] H)) => F y) hcomm
  simp only [ncpComp_apply, nmiuNCP_apply] at h
  exact h

/-- The two ways of reading `f ⊗ ρ`. -/
theorem tmapM_swap (f : NMIUMap 𝒜 ℬ) (ρ : NMIUMap 𝒞 (H →L[ℂ] H))
    (y : VNT 𝒜 𝒞) :
    tmapM f (nmiuId (H →L[ℂ] H)) (tmapM (nmiuId 𝒜) ρ y)
      = tmapM (nmiuId ℬ) ρ (tmapM f (nmiuId 𝒞) y) := by
  have h : nmiuComp (tmapM f (nmiuId (H →L[ℂ] H))) (tmapM (nmiuId 𝒜) ρ)
      = nmiuComp (tmapM (nmiuId ℬ) ρ) (tmapM f (nmiuId 𝒞)) :=
    (exists_tmapM f ρ).unique
      (fun a b => by
        simp only [nmiuComp_apply, tmapM_apply, nmiuId_apply])
      (fun a b => by
        simp only [nmiuComp_apply, tmapM_apply, nmiuId_apply])
  exact congrArg (fun F : NMIUMap (VNT 𝒜 𝒞) (VNT ℬ (H →L[ℂ] H)) => F y) h

/-- The range of `id ⊗ ρ` lies in `𝒜 ⊗ ρ(𝒞)`. -/
theorem tmapM_right_range_le (ρ : NMIUMap 𝒞 (H →L[ℂ] H)) (y : VNT 𝒜 𝒞) :
    tmapM (nmiuId 𝒜) ρ y ∈
      tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range := by
  have htop : wstar (VNT 𝒜 𝒞)
      {t : VNT 𝒜 𝒞 | ∃ a b, t = (vnTensor 𝒜 𝒞).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor 𝒜 𝒞).isTensorProduct.dense
  have hle : wstar (VNT 𝒜 𝒞) {t : VNT 𝒜 𝒞 | ∃ a b, t = (vnTensor 𝒜 𝒞).map a b} ≤
      (tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range).comap
        (tmapM (nmiuId 𝒜) ρ).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM (nmiuId 𝒜) ρ).toStarAlgHom
      (tmapM (nmiuId 𝒜) ρ).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨a, c, rfl⟩
    show tmapM (nmiuId 𝒜) ρ (a ⊗ᵥ c) ∈
      tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2
      ⟨a, StarSubalgebra.mem_top, ρ c, ⟨c, rfl⟩, rfl⟩
  rw [htop, top_le_iff] at hle
  have hy : y ∈ (tensorSub₂ (⊤ : StarSubalgebra ℂ 𝒜) ρ.toStarAlgHom.range).comap
      (tmapM (nmiuId 𝒜) ρ).toStarAlgHom := by rw [hle]; trivial
  exact hy

/-- `𝒮 ⊗ ρ(𝒞)` is the image of `𝒮 ⊗ 𝒞` under `id ⊗ ρ`. -/
theorem exists_preimage_of_mem_tensorSub₂ (ρ : NMIUMap 𝒞 (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ) (S : StarSubalgebra ℂ 𝒜)
    (z : VNT 𝒜 (H →L[ℂ] H))
    (hz : z ∈ tensorSub₂ S ρ.toStarAlgHom.range) :
    ∃ y ∈ tensorSub 𝒞 S, tmapM (nmiuId 𝒜) ρ y = z := by
  set J := tmapM (nmiuId 𝒜) ρ with hJ
  have hJinj : Function.Injective ⇑J :=
    tmapM_injective (nmiuId 𝒜) ρ (nmiuId_bijective (X := 𝒜)).1 hρ
  set R := J.toStarAlgHom.range with hR
  have hRvn : IsVNSubalgebra (VNT 𝒜 (H →L[ℂ] H)) R := nmiu_image J
  set u := nmiuCorestrict J R hRvn (fun y => ⟨y, rfl⟩) with hu
  have hubij : Function.Bijective ⇑u :=
    nmiuCorestrict_bijective J R hRvn (fun y => ⟨y, rfl⟩) hJinj
      (by rintro _ ⟨y, rfl⟩; exact ⟨y, rfl⟩)
  set W : StarSubalgebra ℂ (VNT 𝒜 (H →L[ℂ] H)) :=
    ((tensorSub 𝒞 S).map u.toStarAlgHom).map VNSub.valStarAlgHom with hW
  have hWvn : IsVNSubalgebra (VNT 𝒜 (H →L[ℂ] H)) W :=
    vnsub_isVNSubalgebra_map _
      (isVNSubalgebra_nmiu_map u hubij _ (isVNSubalgebra_wstar _).1)
  have hmemW : ∀ x : VNT 𝒜 (H →L[ℂ] H),
      x ∈ W ↔ ∃ y ∈ tensorSub 𝒞 S, J y = x := by
    intro x
    constructor
    · rintro ⟨t, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨u y, ⟨y, hy, rfl⟩, rfl⟩
  have hle : tensorSub₂ S ρ.toStarAlgHom.range ≤ W := by
    refine sInf_le ⟨hWvn, ?_⟩
    rintro _ ⟨a, ha, _, ⟨c, rfl⟩, rfl⟩
    refine (hmemW _).mpr ⟨a ⊗ᵥ c, ?_, ?_⟩
    · exact (isVNSubalgebra_wstar _).2 ⟨a, ha, c, rfl⟩
    · rw [hJ, tmapM_apply, nmiuId_apply]
      rfl
  exact (hmemW z).mp (hle hz)

/-- **The intersection step of proc.tex:4938**: granted 121II, an element
of `𝒜 ⊗ 𝒞` whose image in `𝒜 ⊗ B(ℋ)` lies in `𝒮 ⊗ B(ℋ)` already lies in
`𝒮 ⊗ 𝒞`.  This is `𝒮 ⊗ 𝒞 = (𝒮 ⊗ B(ℋ)) ∩ (𝒜 ⊗ 𝒞)`. -/
theorem mem_tensorSub_of_image (h121 : IntersectionTensorStatement.{u})
    (ρ : NMIUMap 𝒞 (H →L[ℂ] H)) (hρ : Function.Injective ⇑ρ)
    (S : StarSubalgebra ℂ 𝒜) (hS : IsVNSubalgebra 𝒜 S) (x : VNT 𝒜 𝒞)
    (hx : tmapM (nmiuId 𝒜) ρ x ∈ tensorSub (H →L[ℂ] H) S) :
    x ∈ tensorSub 𝒞 S := by
  rw [tensorSub_eq_tensorSub₂] at hx
  have hx2 := tmapM_right_range_le (𝒜 := 𝒜) ρ x
  have hinf := tensorSub₂_inf_of_intersectionTensorStatement
    (𝒜 := 𝒜) (𝒞 := H →L[ℂ] H) h121 S ⊤ hS isVNSubalgebra_top'
    (⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) ρ.toStarAlgHom.range
    isVNSubalgebra_top' (nmiu_image ρ)
  have hmem : tmapM (nmiuId 𝒜) ρ x ∈
      tensorSub₂ (S ⊓ ⊤) ((⊤ : StarSubalgebra ℂ (H →L[ℂ] H)) ⊓
        ρ.toStarAlgHom.range) := by
    rw [← hinf]
    exact ⟨hx, hx2⟩
  rw [inf_top_eq, top_inf_eq] at hmem
  obtain ⟨y, hy, hyx⟩ := exists_preimage_of_mem_tensorSub₂ ρ hρ S _ hmem
  have hJinj : Function.Injective ⇑(tmapM (nmiuId 𝒜) ρ) :=
    tmapM_injective (nmiuId 𝒜) ρ (nmiuId_bijective (X := 𝒜)).1 hρ
  exact hJinj hyx ▸ hy

end Naturality



/-- The range of `ρ ⊗ id` is contained in `ρ(𝒞) ⊗ 𝒜` (the left-hand
companion of `tmapM_range_le` above). -/
theorem tmapM_left_range_le {C₀ D₀ A₀ : Type u}
    [CStarAlgebra C₀] [PartialOrder C₀] [StarOrderedRing C₀] [VonNeumannAlgebra C₀]
    [CStarAlgebra D₀] [PartialOrder D₀] [StarOrderedRing D₀] [VonNeumannAlgebra D₀]
    [CStarAlgebra A₀] [PartialOrder A₀] [StarOrderedRing A₀] [VonNeumannAlgebra A₀]
    (ρ : NMIUMap C₀ D₀) (y : VNT C₀ A₀) :
    tmapM ρ (nmiuId A₀) y ∈ tensorSub A₀ ρ.toStarAlgHom.range := by
  have htop : wstar (VNT C₀ A₀)
      {t : VNT C₀ A₀ | ∃ a b, t = (vnTensor C₀ A₀).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor C₀ A₀).isTensorProduct.dense
  have hle : wstar (VNT C₀ A₀) {t : VNT C₀ A₀ | ∃ a b, t = (vnTensor C₀ A₀).map a b} ≤
      (tensorSub A₀ ρ.toStarAlgHom.range).comap (tmapM ρ (nmiuId A₀)).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM ρ (nmiuId A₀)).toStarAlgHom
      (tmapM ρ (nmiuId A₀)).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨c, a, rfl⟩
    show tmapM ρ (nmiuId A₀) (c ⊗ᵥ a) ∈ tensorSub A₀ ρ.toStarAlgHom.range
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2 ⟨ρ c, ⟨c, rfl⟩, a, rfl⟩
  rw [htop, top_le_iff] at hle
  have hy : y ∈ (tensorSub A₀ ρ.toStarAlgHom.range).comap
      (tmapM ρ (nmiuId A₀)).toStarAlgHom := by rw [hle]; trivial
  exact hy

/-- The corestriction of a map landing in `𝒮 ⊗ 𝒞` to `(VNSub 𝒜 𝒮) ⊗ 𝒞`
(the device of `ha_tensor_closed`). -/
theorem exists_corestrict_tensorSub {A₀ C₀ D₀ : Type u}
    [CStarAlgebra A₀] [PartialOrder A₀] [StarOrderedRing A₀] [VonNeumannAlgebra A₀]
    [CStarAlgebra C₀] [PartialOrder C₀] [StarOrderedRing C₀] [VonNeumannAlgebra C₀]
    [CStarAlgebra D₀] [PartialOrder D₀] [StarOrderedRing D₀] [VonNeumannAlgebra D₀]
    (S : StarSubalgebra ℂ A₀) (hS : IsVNSubalgebra A₀ S) (h : NMIUMap D₀ (VNT A₀ C₀))
    (hmem : ∀ d : D₀, h d ∈ tensorSub C₀ S) :
    ∃ ht : NMIUMap D₀ (VNT (VNSub A₀ S hS) C₀),
      ∀ d : D₀, tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀) (ht d)
        = h d := by
  have hIvn : IsVNSubalgebra (VNT A₀ C₀) (tensorSub C₀ S) :=
    (isVNSubalgebra_wstar _).1
  have hΞinj : Function.Injective
      ⇑(tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀)) :=
    tmapM_injective _ _ VNSub.valNMIU_injective (nmiuId_bijective (X := C₀)).1
  have hΞmem : ∀ y : VNT (VNSub A₀ S hS) C₀,
      tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀) y
        ∈ tensorSub C₀ S := by
    intro y
    have hy := tmapM_left_range_le (A₀ := C₀)
      (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) y
    rwa [VNSub.valNMIU_range] at hy
  have hΞsurj : ∀ z ∈ tensorSub C₀ S,
      ∃ y, tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀) y = z := by
    have hle : tensorSub C₀ S ≤
        (tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS))
          (nmiuId C₀)).toStarAlgHom.range := by
      refine sInf_le ⟨nmiu_image _, ?_⟩
      rintro _ ⟨s, hs, c, rfl⟩
      refine ⟨(⟨s, hs⟩ : VNSub A₀ S hS) ⊗ᵥ c, ?_⟩
      show tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀)
          ((⟨s, hs⟩ : VNSub A₀ S hS) ⊗ᵥ c) = s ⊗ᵥ c
      rw [tmapM_apply, nmiuId_apply]
      rfl
    intro z hz
    exact hle hz
  have hΛbij := nmiuCorestrict_bijective
    (tmapM (VNSub.valNMIU (A := A₀) (S := S) (hS := hS)) (nmiuId C₀))
    (tensorSub C₀ S) hIvn hΞmem hΞinj hΞsurj
  refine ⟨nmiuComp (nmiuSymm _ hΛbij)
    (nmiuCorestrict h (tensorSub C₀ S) hIvn hmem), fun d => ?_⟩
  exact congrArg VNSub.val (nmiuSymm_apply_apply' _ hΛbij
    (nmiuCorestrict h (tensorSub C₀ S) hIvn hmem d))



end EqL

/-! ## 125IV `equaliser-lemma`, granted 121II -/

open EqL in
set_option maxHeartbeats 1000000 in
/-- **125IV** (`equaliser-lemma`, proc.tex:4852, Lemma (Kornell)), granted
**121II** `intersection-tensor` (as `IntersectionTensorStatement`): every
nmiu-map `h : 𝒟 → 𝒜 ⊗ 𝒞` factors as `(ι ⊗ id) ∘ h̃` through `𝒜̃ ⊗ 𝒞` for a
von Neumann subalgebra `𝒜̃ ⊆ 𝒜` generated by at most `#𝒟 · 2^#𝒞`
elements, such that nmiu-maps `f, g : 𝒜 → ℬ` with
`(f ⊗ id) ∘ h = (g ⊗ id) ∘ h` agree on `𝒜̃`.

This is `equaliser_lemma` (below) with 121II as an explicit hypothesis;
`equaliser_lemma` itself is
`equaliser_lemma_of_intersectionTensorStatement intersectionTensorStatement h`. -/
theorem equaliser_lemma_of_intersectionTensorStatement
    (h121 : IntersectionTensorStatement.{u})
    {A C D : Type u}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] [VonNeumannAlgebra C]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [VonNeumannAlgebra D]
    (h : NMIUMap D (VNT A C)) :
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
          ∀ x : VNSub A S hS, f (ι x) = g (ι x) := by
  classical
  -- the equaliser clause holds for any `S` of the form `wstar A G` as soon
  -- as `f` and `g` agree on `G`
  have hEq : ∀ (G : Set A) (Bb : Type u) [CStarAlgebra Bb] [PartialOrder Bb]
      [StarOrderedRing Bb] [VonNeumannAlgebra Bb] (f g : NMIUMap A Bb),
      (∀ a ∈ G, f a = g a) → ∀ a ∈ wstar A G, f a = g a := by
    intro G Bb _ _ _ _ f g hfg a ha
    obtain ⟨E, hE, hEset⟩ := vn_equalisers f g
    have hGE : G ⊆ (E : Set A) := by
      intro y hy
      rw [hEset]
      exact hfg y hy
    have hSE : wstar A G ≤ E := sInf_le ⟨hE, hGE⟩
    have hmem : a ∈ (E : Set A) := hSE ha
    rw [hEset] at hmem
    exact hmem
  rcases subsingleton_or_nontrivial C with hCsub | hCnt
  · -- degenerate case: `𝒞` is trivial, so `𝒜 ⊗ 𝒞` is
    have _ := hCsub
    have hVsub : Subsingleton (VNT A C) := vnt_subsingleton
    have hVsub' : ∀ (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S),
        Subsingleton (VNT (VNSub A S hS) C) := fun _ _ => vnt_subsingleton
    refine ⟨wstar A (∅ : Set A), (isVNSubalgebra_wstar _).1, ∅, rfl, ?_,
      VNSub.valNMIU, nmiuOfSubsingleton D _, fun _ => rfl, fun _ =>
        Subsingleton.elim _ _, ?_⟩
    · simp
    · intro Bb _ _ _ _ f g _ x
      exact hEq ∅ Bb f g (fun a ha => absurd ha (Set.notMem_empty a)) x.val x.property
  · -- the main case
    have _ := hCnt
    obtain ⟨rep, hcard⟩ := vn_gns_bound (A := C)
    have hntBH : Nontrivial (rep.space →L[ℂ] rep.space) :=
      ⟨⟨rep.rep 0, rep.rep 1, fun hc => zero_ne_one (rep.injective hc)⟩⟩
    obtain ⟨w, e, -⟩ := exists_hilbertBasis ℂ rep.space
    -- the elements `r_ξ(h(d))`
    have hchoice : ∀ p : D × rep.space, ∃ a : A,
        rSlice A p.2 (tmapM (nmiuId A) rep.rep (h p.1))
          = a ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) :=
      fun p => rSlice_mem A p.2 _
    choose r hr using hchoice
    refine ⟨wstar A (Set.range r), (isVNSubalgebra_wstar _).1, Set.range r, rfl,
      ?_, ?_⟩
    · -- the cardinality bound
      refine le_trans Cardinal.mk_range_le ?_
      have hprod : #(D × rep.space) = #D * #rep.space := by
        simp [Cardinal.mk_prod]
      rw [hprod]
      exact mul_le_mul' le_rfl hcard
    · -- the factorisation and the equaliser clause
      have hgen : ∀ p : D × rep.space, r p ∈ wstar A (Set.range r) :=
        fun p => (isVNSubalgebra_wstar _).2 ⟨p, rfl⟩
      have hmemS : ∀ d : D, h d ∈ tensorSub C (wstar A (Set.range r)) := by
        intro d
        refine mem_tensorSub_of_image h121 rep.rep rep.injective _
          (isVNSubalgebra_wstar _).1 (h d) ?_
        refine mem_tensorSub_of_rSlice_mem _ e _ ?_
        intro ξ a ha
        have h1 : a ⊗ᵥ (1 : rep.space →L[ℂ] rep.space)
            = r (d, ξ) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
          rw [← ha, hr (d, ξ)]
        rw [nmiuTmulLeft_injective h1]
        exact hgen (d, ξ)
      obtain ⟨ht, hht⟩ := exists_corestrict_tensorSub
        (wstar A (Set.range r)) (isVNSubalgebra_wstar _).1 h hmemS
      refine ⟨VNSub.valNMIU, ht, fun _ => rfl, fun d => (hht d).symm, ?_⟩
      intro Bb _ _ _ _ f g hfg x
      refine hEq (Set.range r) Bb f g ?_ x.val x.property
      rintro _ ⟨p, rfl⟩
      obtain ⟨d, ξ⟩ := p
      have hnat : ∀ k : NMIUMap A Bb,
          tmapM k (nmiuId (rep.space →L[ℂ] rep.space))
              (rSlice A ξ (tmapM (nmiuId A) rep.rep (h d)))
            = rSlice Bb ξ (tmapM (nmiuId Bb) rep.rep
                (tmapM k (nmiuId C) (h d))) := by
        intro k
        rw [rSlice_natural, tmapM_swap]
      have hval : ∀ k : NMIUMap A Bb,
          tmapM k (nmiuId (rep.space →L[ℂ] rep.space))
              (rSlice A ξ (tmapM (nmiuId A) rep.rep (h d)))
            = k (r (d, ξ)) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
        intro k
        rw [hr (d, ξ), tmapM_apply, nmiuId_apply]
      have hkey : f (r (d, ξ)) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space)
          = g (r (d, ξ)) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
        rw [← hval f, ← hval g, hnat f, hnat g, hfg d]
      exact nmiuTmulLeft_injective hkey

/-- **125IV** (`equaliser-lemma`, proc.tex:4852, Lemma (Kornell)): every
nmiu-map `h : 𝒟 → 𝒜 ⊗ 𝒞` factors as `(ι ⊗ id) ∘ h̃` through
`𝒜̃ ⊗ 𝒞` for a von Neumann subalgebra `𝒜̃ ⊆ 𝒜` generated by at most
`#𝒟 · 2^#𝒞` elements, such that nmiu-maps `f, g : 𝒜 → ℬ` with
`(f ⊗ id) ∘ h = (g ⊗ id) ∘ h` agree on `𝒜̃`.

The proof is `equaliser_lemma_of_intersectionTensorStatement` with its
hypothesis discharged by 121II `intersection_tensor`. -/
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
          ∀ x : VNSub A S hS, f (ι x) = g (ι x) :=
  equaliser_lemma_of_intersectionTensorStatement intersectionTensorStatement h



/-! # Parsecs 1250 and 1255, concluded

The five statements below are exactly those whose proofs consume 125IV
`equaliser_lemma`, or the slice-map property (121II) that `EqL` packages;
they therefore have to sit *after* those, that is, here, rather than at their
places in parsecs 1250 and 1255.  Nothing between their original positions and
here refers to them.

The one genuinely new ingredient is the **converse** of `EqL`'s
`mem_tensorSub_of_rSlice_mem`: the slices of an element of `𝒮 ⊗ B(ℋ)` lie in
`𝒮`.  Together the two halves are Tomiyama's slice-map property, and with
`mem_tensorSub_of_image` — which is where 121II enters — they give the
general 125VIIb. -/

section ParsecEnd

open EqL

/-! ## The slice-map property -/

/-- `id ⊗ ρ` carries `𝒮 ⊗ 𝒜₁` into `𝒮 ⊗ 𝒜₂`. -/
private theorem tensorSub_map_right {𝒞 𝒜₁ 𝒜₂ : Type u}
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    [CStarAlgebra 𝒜₁] [PartialOrder 𝒜₁] [StarOrderedRing 𝒜₁] [VonNeumannAlgebra 𝒜₁]
    [CStarAlgebra 𝒜₂] [PartialOrder 𝒜₂] [StarOrderedRing 𝒜₂] [VonNeumannAlgebra 𝒜₂]
    (ρ : NMIUMap 𝒜₁ 𝒜₂) (S : StarSubalgebra ℂ 𝒞) {z : VNT 𝒞 𝒜₁}
    (hz : z ∈ tensorSub 𝒜₁ S) : tmapM (nmiuId 𝒞) ρ z ∈ tensorSub 𝒜₂ S := by
  have hle : tensorSub 𝒜₁ S ≤
      (tensorSub 𝒜₂ S).comap (tmapM (nmiuId 𝒞) ρ).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM (nmiuId 𝒞) ρ).toStarAlgHom
      (tmapM (nmiuId 𝒞) ρ).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨s, hs, a, rfl⟩
    show tmapM (nmiuId 𝒞) ρ (s ⊗ᵥ a) ∈ tensorSub 𝒜₂ S
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2 ⟨s, hs, ρ a, rfl⟩
  exact hle hz

/-- **The converse of `mem_tensorSub_of_rSlice_mem`**: every slice `r_ξ(z)` of
an element `z` of `𝒮 ⊗ B(ℋ)` lies in `𝒮`.

The proof needs no commutation theorem: `𝒮 ⊗ B(ℋ)` is, on the nose, the range
of `ι ⊗ id` for the inclusion `ι : 𝒮 ↪ 𝒞` (a von Neumann subalgebra of
`𝒞 ⊗ B(ℋ)` containing the generators `s ⊗ b`, by 69IVb), and `r_ξ` is natural
(`rSlice_natural`), so the slice of `(ι ⊗ id)(w)` is `ι` of the slice of
`w`. -/
private theorem rSlice_mem_of_mem_tensorSub {𝒞 : Type u}
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial (H →L[ℂ] H)]
    (S : StarSubalgebra ℂ 𝒞) (hS : IsVNSubalgebra 𝒞 S) (ξ : H)
    {z : VNT 𝒞 (H →L[ℂ] H)} (hz : z ∈ tensorSub (H →L[ℂ] H) S)
    {c : 𝒞} (hc : rSlice 𝒞 ξ z = c ⊗ᵥ (1 : H →L[ℂ] H)) : c ∈ S := by
  have hle : tensorSub (H →L[ℂ] H) S ≤
      (tmapM (VNSub.valNMIU (A := 𝒞) (S := S) (hS := hS))
        (nmiuId (H →L[ℂ] H))).toStarAlgHom.range := by
    refine sInf_le ⟨nmiu_image _, ?_⟩
    rintro _ ⟨s, hs, b, rfl⟩
    refine ⟨(⟨s, hs⟩ : VNSub 𝒞 S hS) ⊗ᵥ b, ?_⟩
    show tmapM (VNSub.valNMIU (A := 𝒞) (S := S) (hS := hS)) (nmiuId (H →L[ℂ] H))
        ((⟨s, hs⟩ : VNSub 𝒞 S hS) ⊗ᵥ b) = s ⊗ᵥ b
    rw [tmapM_apply, nmiuId_apply]
    rfl
  obtain ⟨w, hw⟩ := hle hz
  have hwz : tmapM (VNSub.valNMIU (A := 𝒞) (S := S) (hS := hS))
      (nmiuId (H →L[ℂ] H)) w = z := hw
  obtain ⟨v, hv⟩ := rSlice_mem (VNSub 𝒞 S hS) ξ w
  have hnat := rSlice_natural
    (VNSub.valNMIU (A := 𝒞) (S := S) (hS := hS)) ξ w
  rw [hv, tmapM_apply, nmiuId_apply, hwz, hc] at hnat
  have hval : (v.val : 𝒞) = c := nmiuTmulLeft_injective hnat
  exact hval ▸ v.property

/-! ## 125VI `tensor-equalisers` -/

/-- **Equaliser maps are injective** — what `proc.tex:4990` calls on (through
`tensor-injective`) for the uniqueness clause of 125VI.  47V `vn_equalisers`
builds *an* equaliser concretely, as a von Neumann subalgebra `Q ⊆ 𝒜` with the
inclusion for its map; an abstract equaliser `e` corestricts to `Q` and the
two universal properties make the corestriction a retract of the comparison
map, so `e` is the composite of an injection with an injection. -/
private theorem nmiuEqualizer_injective [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {E : Type u} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    [VonNeumannAlgebra E] {f g : NMIUMap A B} {e : NMIUMap E A}
    (he : IsNMIUEqualizer f g e) : Function.Injective ⇑e := by
  obtain ⟨Q, hQ, hQset⟩ := vn_equalisers f g
  have hmem : ∀ x : E, e x ∈ Q := by
    intro x
    have hx : e x ∈ {a : A | f a = g a} := he.1 x
    rw [← hQset] at hx
    exact hx
  have hfgQ : ∀ x : VNSub A Q hQ,
      f (VNSub.valNMIU (A := A) (S := Q) (hS := hQ) x)
        = g (VNSub.valNMIU (A := A) (S := Q) (hS := hQ) x) := by
    intro x
    have hx : x.val ∈ (Q : Set A) := x.property
    rw [hQset] at hx
    exact hx
  obtain ⟨k, hk, -⟩ := he.2 (VNSub A Q hQ) VNSub.valNMIU hfgQ
  obtain ⟨k₀, -, huniq⟩ := he.2 E e (fun x => he.1 x)
  have h1 : nmiuComp k (nmiuCorestrict e Q hQ hmem) = nmiuId E := by
    refine (huniq (nmiuComp k (nmiuCorestrict e Q hQ hmem)) ?_).trans
      (huniq (nmiuId E) (fun _ => rfl)).symm
    intro x
    show e x = e (k (nmiuCorestrict e Q hQ hmem x))
    exact hk (nmiuCorestrict e Q hQ hmem x)
  have h1' : ∀ x : E, k (nmiuCorestrict e Q hQ hmem x) = x := by
    intro x
    have h := congrArg (fun F : NMIUMap E E => F x) h1
    rw [nmiuComp_apply, nmiuId_apply] at h
    exact h
  intro x y hxy
  have hk'eq : nmiuCorestrict e Q hQ hmem x = nmiuCorestrict e Q hQ hmem y :=
    VNSub.val_injective (by
      rw [nmiuCorestrict_val, nmiuCorestrict_val, hxy])
  rw [← h1' x, ← h1' y, hk'eq]

/-- **125VI** (`tensor-equalisers`, proc.tex:4978, Proposition): if `e` is
an equaliser of nmiu-maps `f, g : 𝒜 → ℬ`, then `e ⊗ id_𝒞` is an
equaliser of `f ⊗ id` and `g ⊗ id`.

This is proc.tex:4980 verbatim.  Uniqueness of the mediating map is
injectivity of `e ⊗ id`, which is 114I `tensor-injective` applied to the
injective `e` (`nmiuEqualizer_injective`).  Existence is 125IV
`equaliser_lemma`: it factors `h` through `𝒜̃ ⊗ 𝒞` for a von Neumann
subalgebra `𝒜̃ ⊆ 𝒜` on which `f` and `g` agree, and the equaliser property of
`e` then factors the inclusion `𝒜̃ ↪ 𝒜` through `e`. -/
theorem tensor_equalisers [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] {E : Type u} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] [VonNeumannAlgebra E] (f g : NMIUMap A B)
    (e : NMIUMap E A) (he : IsNMIUEqualizer f g e) :
    IsNMIUEqualizer (tmapM f (nmiuId C)) (tmapM g (nmiuId C))
      (tmapM e (nmiuId C)) := by
  have hein : Function.Injective ⇑e := nmiuEqualizer_injective he
  have hinj : Function.Injective ⇑(tmapM e (nmiuId C)) :=
    tmapM_injective e (nmiuId C) hein (nmiuId_bijective (X := C)).1
  refine ⟨fun x => ?_, fun D' _ _ _ _ h hh => ?_⟩
  · have hfe : nmiuComp f e = nmiuComp g e :=
      DFunLike.coe_injective (funext fun y => he.1 y)
    rw [tmapM_comp_id, tmapM_comp_id, hfe]
  · obtain ⟨S, hS, G, -, -, ι, ht, -, hfact, heq⟩ :=
      equaliser_lemma (A := A) (C := C) (D := D') h
    obtain ⟨ιt, hιt, -⟩ := he.2 (VNSub A S hS) ι (heq B f g hh)
    have hcomp : nmiuComp e ιt = ι :=
      DFunLike.coe_injective (funext fun x => (hιt x).symm)
    have hkmain : ∀ d : D',
        h d = tmapM e (nmiuId C) (nmiuComp (tmapM ιt (nmiuId C)) ht d) := by
      intro d
      show h d = tmapM e (nmiuId C) (tmapM ιt (nmiuId C) (ht d))
      rw [tmapM_comp_id, hcomp]
      exact hfact d
    exact ⟨nmiuComp (tmapM ιt (nmiuId C)) ht, hkmain, fun k' hk' =>
      DFunLike.coe_injective (funext fun d => hinj ((hk' d).symm.trans (hkmain d)))⟩

/-- The companion of `vnt_subsingleton` for a trivial **left** factor. -/
private theorem vnt_subsingleton_left {Cc Aa : Type*} [CStarAlgebra Cc]
    [PartialOrder Cc] [StarOrderedRing Cc] [VonNeumannAlgebra Cc]
    [CStarAlgebra Aa] [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa]
    [Subsingleton Cc] : Subsingleton (VNT Cc Aa) := by
  have h1 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 1 := (vnTensor Cc Aa).isTensorProduct.miu.1
  have h0 : ((1 : Cc) ⊗ᵥ (1 : Aa)) = 0 := by
    rw [show (1 : Cc) = 0 from Subsingleton.elim _ _]
    show (vnTensor Cc Aa).map 0 1 = 0
    rw [map_zero, LinearMap.zero_apply]
  exact subsingleton_of_zero_eq_one (h1.symm.trans h0).symm

/-- **The products of `W*_miu` pass through `(·) ⊗ 𝒜`**:
`(⊕ₚ 𝒟ₚ) ⊗ 𝒜 ≅ ⊕ₚ (𝒟ₚ ⊗ 𝒜)`, with the coordinates of the isomorphism the
maps `πₚ ⊗ id`.  This is `exists_matSumTensorIso` with the summands
arbitrary rather than matrix algebras — which makes it *shorter*, the
`punitSum` universe shuffle being what the matrix version needed. -/
private theorem exists_sumTensorIso {Aa : Type u} [CStarAlgebra Aa]
    [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa] [Nontrivial Aa]
    {P₀ : Type u} (𝒟 : P₀ → Type u) [∀ p, CStarAlgebra (𝒟 p)]
    [∀ p, Nontrivial (𝒟 p)] [∀ p, PartialOrder (𝒟 p)]
    [∀ p, StarOrderedRing (𝒟 p)] [∀ p, VonNeumannAlgebra (𝒟 p)]
    [∀ p, Nontrivial (VNT (𝒟 p) Aa)] :
    ∃ θ : NMIUMap (VNT (lp 𝒟 ∞) Aa) (lp (fun p : P₀ => VNT (𝒟 p) Aa) ∞),
      Function.Bijective ⇑θ ∧
      ∀ (x : VNT (lp 𝒟 ∞) Aa) (p : P₀),
        ((θ x : lp (fun q : P₀ => VNT (𝒟 q) Aa) ∞) : ∀ q : P₀, VNT (𝒟 q) Aa) p
          = tmapM (lpEvalNMIU 𝒟 p) (nmiuId Aa) x := by
  classical
  haveI hntp : ∀ p : P₀, Nontrivial (VNT Aa (𝒟 p)) := fun _ => vnt_nontrivial
  obtain ⟨γ, hγe, hγ⟩ := tensor_distributes_over_sums (A := Aa) 𝒟
  obtain ⟨φ, hφe, hφbij, -⟩ :=
    tensor_uniqueness (vnTensor (lp 𝒟 ∞) Aa).map γ.flip
      (vnTensor (lp 𝒟 ∞) Aa).isTensorProduct (isTensorProduct_flip hγ)
  have hbr : ∀ p : P₀, ∃ s : NMIUMap (VNT Aa (𝒟 p)) (VNT (𝒟 p) Aa),
      (∀ (a : Aa) (c : 𝒟 p), s (a ⊗ᵥ c) = c ⊗ᵥ a) ∧ Function.Bijective ⇑s :=
    fun p => by
      obtain ⟨sp, hsp, hspb, -⟩ := exists_braiding Aa (𝒟 p)
      exact ⟨sp, hsp, hspb⟩
  choose sb hse hsbij using hbr
  obtain ⟨Ξ, hΞbij, hΞa⟩ := exists_lp_congr
    (𝒳 := fun p : P₀ => VNT Aa (𝒟 p)) (𝒴 := fun p : P₀ => VNT (𝒟 p) Aa) sb hsbij
  refine ⟨nmiuComp Ξ φ, nmiuComp_bijective _ _ hΞbij hφbij, ?_⟩
  intro x p
  have hgen : wstar (VNT (lp 𝒟 ∞) Aa)
      {t : VNT (lp 𝒟 ∞) Aa | ∃ a b, t = (vnTensor (lp 𝒟 ∞) Aa).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor (lp 𝒟 ∞) Aa).isTensorProduct.dense
  refine nmiu_ext_of_wstar_top
    (nmiuComp (lpEvalNMIU (fun q : P₀ => VNT (𝒟 q) Aa) p) (nmiuComp Ξ φ))
    (tmapM (lpEvalNMIU 𝒟 p) (nmiuId Aa)) _ hgen ?_ x
  rintro _ ⟨c, a, rfl⟩
  show ((Ξ (φ (c ⊗ᵥ a)) : lp (fun q : P₀ => VNT (𝒟 q) Aa) ∞) :
      ∀ q : P₀, VNT (𝒟 q) Aa) p
    = tmapM (lpEvalNMIU 𝒟 p) (nmiuId Aa) (c ⊗ᵥ a)
  have hφe' : ∀ (y : lp 𝒟 ∞) (bb : Aa), φ (y ⊗ᵥ bb) = γ.flip y bb := hφe
  have e2 : ((φ (c ⊗ᵥ a) : lp (fun q : P₀ => VNT Aa (𝒟 q)) ∞) :
      ∀ q : P₀, VNT Aa (𝒟 q)) p = a ⊗ᵥ (c : ∀ q : P₀, 𝒟 q) p := by
    rw [hφe' c a]
    exact hγe a c p
  rw [hΞa, e2, hse, tmapM_apply, nmiuId_apply]
  rfl

/-! ### The binary product of the hint of 125VIIb (proc.tex:5049) -/

section PairProduct

variable {X Y : Type u}

private def pairFam (X Y : Type u) : ULift.{u} Bool → Type u
  | ⟨true⟩ => X
  | ⟨false⟩ => Y

private instance pairFamCStar [CStarAlgebra X] [CStarAlgebra Y] :
    ∀ b, CStarAlgebra (pairFam X Y b)
  | ⟨true⟩ => ‹CStarAlgebra X›
  | ⟨false⟩ => ‹CStarAlgebra Y›

private instance pairFamNontrivial [Nontrivial X] [Nontrivial Y] :
    ∀ b, Nontrivial (pairFam X Y b)
  | ⟨true⟩ => ‹Nontrivial X›
  | ⟨false⟩ => ‹Nontrivial Y›

private instance pairFamPO [PartialOrder X] [PartialOrder Y] :
    ∀ b, PartialOrder (pairFam X Y b)
  | ⟨true⟩ => ‹PartialOrder X›
  | ⟨false⟩ => ‹PartialOrder Y›

private instance pairFamSOR [CStarAlgebra X] [CStarAlgebra Y] [PartialOrder X]
    [PartialOrder Y] [StarOrderedRing X] [StarOrderedRing Y] :
    ∀ b, StarOrderedRing (pairFam X Y b)
  | ⟨true⟩ => ‹StarOrderedRing X›
  | ⟨false⟩ => ‹StarOrderedRing Y›

private instance pairFamVNA [CStarAlgebra X] [CStarAlgebra Y] [PartialOrder X]
    [PartialOrder Y] [StarOrderedRing X] [StarOrderedRing Y]
    [VonNeumannAlgebra X] [VonNeumannAlgebra Y] :
    ∀ b, VonNeumannAlgebra (pairFam X Y b)
  | ⟨true⟩ => ‹VonNeumannAlgebra X›
  | ⟨false⟩ => ‹VonNeumannAlgebra Y›

variable [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]
  [Nontrivial X] [Nontrivial Y]

private def pairFst : NMIUMap (lp (pairFam X Y) ∞) X :=
  lpEvalNMIU (pairFam X Y) ⟨true⟩

private def pairSnd : NMIUMap (lp (pairFam X Y) ∞) Y :=
  lpEvalNMIU (pairFam X Y) ⟨false⟩

private theorem pair_ext (p q : lp (pairFam X Y) ∞)
    (h0 : pairFst p = pairFst q) (h1 : pairSnd p = pairSnd q) : p = q := by
  refine lp.ext (funext fun b => ?_)
  obtain ⟨b⟩ := b
  cases b
  · exact h1
  · exact h0

private def pairNMIU {Z : Type u} [CStarAlgebra Z] [PartialOrder Z]
    [StarOrderedRing Z] [VonNeumannAlgebra Z] (u : NMIUMap Z X) (v : NMIUMap Z Y) :
    ∀ b, NMIUMap Z (pairFam X Y b)
  | ⟨true⟩ => u
  | ⟨false⟩ => v

private theorem exists_pairPair {Z : Type u} [CStarAlgebra Z] [PartialOrder Z]
    [StarOrderedRing Z] [VonNeumannAlgebra Z] (u : NMIUMap Z X) (v : NMIUMap Z Y) :
    ∃ w : NMIUMap Z (lp (pairFam X Y) ∞),
      (∀ z, pairFst (w z) = u z) ∧ (∀ z, pairSnd (w z) = v z) := by
  obtain ⟨w, hw, -⟩ := vn_products_nmiu (pairFam X Y) (pairNMIU u v)
  exact ⟨w, fun z => hw ⟨true⟩ z, fun z => hw ⟨false⟩ z⟩

end PairProduct

/-- the range of the inclusion of a bundled von Neumann subalgebra -/
private theorem vnsub_valNMIU_range [VonNeumannAlgebra B] (S : StarSubalgebra ℂ B)
    (hS : IsVNSubalgebra B S) :
    (VNSub.valNMIU (A := B) (S := S) (hS := hS)).toStarAlgHom.range = S := by
  ext b
  constructor
  · rintro ⟨t, rfl⟩
    exact t.property
  · intro hb
    exact ⟨⟨b, hb⟩, rfl⟩

private theorem tensorSub_top {𝒜 ℬ : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] [CStarAlgebra ℬ] [PartialOrder ℬ]
    [StarOrderedRing ℬ] [VonNeumannAlgebra ℬ] :
    tensorSub 𝒜 (⊤ : StarSubalgebra ℂ ℬ) = ⊤ := by
  have htop : wstar (VNT ℬ 𝒜)
      {t : VNT ℬ 𝒜 | ∃ a b, t = (vnTensor ℬ 𝒜).map a b} = ⊤ :=
    wstar_eq_top_of_dense_span _ (vnTensor ℬ 𝒜).isTensorProduct.dense
  have hle : wstar (VNT ℬ 𝒜) {t : VNT ℬ 𝒜 | ∃ a b, t = (vnTensor ℬ 𝒜).map a b}
      ≤ tensorSub 𝒜 (⊤ : StarSubalgebra ℂ ℬ) := by
    refine sInf_le ⟨(isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨a, b, rfl⟩
    exact (isVNSubalgebra_wstar _).2 ⟨a, trivial, b, rfl⟩
  rw [htop] at hle
  exact top_le_iff.mp hle

/-- **The hint of 125VIIb** (proc.tex:5049). -/
private theorem exists_preimagePullback [VonNeumannAlgebra B] [VonNeumannAlgebra C]
    [Nontrivial B] (ρ : NMIUMap B C) (S : StarSubalgebra ℂ C)
    (hS : IsVNSubalgebra C S) (hntS : Nontrivial (VNSub C S hS))
    (hcomap : IsVNSubalgebra B (S.comap ρ.toStarAlgHom)) :
    ∃ ε : NMIUMap (VNSub B (S.comap ρ.toStarAlgHom) hcomap)
        (lp (pairFam B (VNSub C S hS)) ∞),
      IsNMIUEqualizer (nmiuComp ρ pairFst) (nmiuComp VNSub.valNMIU pairSnd) ε ∧
        ∀ x, pairFst (ε x) = x.val := by
  have := hntS
  have hmem : ∀ x : VNSub B (S.comap ρ.toStarAlgHom) hcomap,
      ρ (VNSub.valNMIU x) ∈ S := fun x => x.property
  set ρ' : NMIUMap (VNSub B (S.comap ρ.toStarAlgHom) hcomap) (VNSub C S hS) :=
    nmiuCorestrict (nmiuComp ρ VNSub.valNMIU) S hS hmem with hρ'
  obtain ⟨ε, hε0, hε1⟩ := exists_pairPair
    (VNSub.valNMIU (A := B) (S := S.comap ρ.toStarAlgHom) (hS := hcomap)) ρ'
  refine ⟨ε, ⟨fun x => ?_, fun D' _ _ _ _ h hh => ?_⟩, hε0⟩
  · show ρ (pairFst (ε x)) = VNSub.valNMIU (pairSnd (ε x))
    rw [hε0, hε1]
    rfl
  · have hhmem : ∀ d : D', pairFst (h d) ∈ S.comap ρ.toStarAlgHom := by
      intro d
      have := hh d
      show ρ.toStarAlgHom (pairFst (h d)) ∈ S
      show ρ (pairFst (h d)) ∈ S
      rw [show ρ (pairFst (h d)) = VNSub.valNMIU (pairSnd (h d)) from this]
      exact (pairSnd (h d)).property
    refine ⟨nmiuCorestrict (nmiuComp pairFst h) (S.comap ρ.toStarAlgHom) hcomap hhmem,
      fun d => ?_, fun k' hk' => ?_⟩
    · refine pair_ext _ _ ?_ ?_
      · rw [hε0]; rfl
      · refine VNSub.val_injective ?_
        rw [hε1]
        exact (hh d).symm
    · refine DFunLike.coe_injective (funext fun d => VNSub.val_injective ?_)
      show (k' d).val = pairFst (h d)
      have := congrArg (fun y => pairFst y) (hk' d)
      show (k' d).val = _
      rw [this]
      exact (hε0 (k' d)).symm

/-! ## 125VIIb `tensor-preimage` -/

/-- **125VIIb** (`tensor-preimage`, proc.tex:5031, Exercise): for an
nmiu-map `ρ : ℬ → 𝒞` and a von Neumann subalgebra `𝒮 ⊆ 𝒞`,
`(ρ ⊗ id_𝒜)⁻¹(𝒮 ⊗ 𝒜) = ρ⁻¹(𝒮) ⊗ 𝒜`.

The `⊇` half is elementary and general: `ρ⁻¹(𝒮) ⊗ 𝒜` is generated by
elements `b ⊗ a` with `ρ(b) ∈ 𝒮`, whose images `ρ(b) ⊗ a` lie in `𝒮 ⊗ 𝒜`,
and the preimage of a von Neumann subalgebra is one (`isVNSubalgebra_comap`).

The `⊆` half is **the Exercise's own hint** (proc.tex:5049): *express*
`ρ⁻¹(𝒮)` *as a pullback in* `W*_miu` *of* `ρ ∘ π₁, e ∘ π₂ : ℬ ⊕ 𝒮 → 𝒞`.
That pullback is `exists_preimagePullback`; `(·) ⊗ 𝒜` preserves it because
it preserves products (**47IV** through `exists_sumTensorIso`, 117III) and
equalisers (**125VI** `tensor_equalisers`, which is where 125IV and hence
121II are spent) — proc.tex:5023's "thus all limits, and in particular, all
pullbacks".  Reading the preserved pullback back off: `𝒲 = (ρ ⊗ 𝒜)⁻¹(𝒮 ⊗ 𝒜)`
comes with `u : 𝒲 → ℬ ⊗ 𝒜` (the inclusion) and `v : 𝒲 → 𝒮 ⊗ 𝒜` (the
corestriction of `ρ ⊗ 𝒜`, through 114I `tensor-injective` for `e ⊗ 𝒜`) with
`(ρ ⊗ 𝒜) ∘ u = (e ⊗ 𝒜) ∘ v`, so the cone `⟨u, v⟩` factors through
`ρ⁻¹(𝒮) ⊗ 𝒜`, and `u` is that factorisation followed by `ι ⊗ 𝒜`.  Whence
every element of `𝒲` lies in the range of `ι ⊗ 𝒜`, which is `ρ⁻¹(𝒮) ⊗ 𝒜`
(`tmapM_left_range_le`).  The three degenerate cases — `𝒜`, `ℬ` or `𝒞`
trivial — are taken separately, the binary product `ℬ ⊕ 𝒮` of **47IV**
needing its factors nontrivial. -/
theorem tensor_preimage [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (ρ : NMIUMap B C) (S : StarSubalgebra ℂ C)
    (hS : IsVNSubalgebra C S) :
    ⇑(tmapM ρ (nmiuId A)) ⁻¹' (tensorSub A S : Set (VNT C A)) =
      (tensorSub A (S.comap ρ.toStarAlgHom) : Set (VNT B A)) := by
  classical
  have hcomap : IsVNSubalgebra B (S.comap ρ.toStarAlgHom) :=
    isVNSubalgebra_comap ρ.toStarAlgHom ρ.preservesDirSups' S hS
  ext x
  constructor
  · intro hx
    have hx' : tmapM ρ (nmiuId A) x ∈ tensorSub A S := hx
    rcases subsingleton_or_nontrivial A with hss | hntA
    · have := hss
      have : Subsingleton (VNT B A) := vnt_subsingleton
      rw [show x = 0 from Subsingleton.elim _ _]
      exact zero_mem _
    rcases subsingleton_or_nontrivial B with hssB | hntB
    · have := hssB
      have : Subsingleton (VNT B A) := vnt_subsingleton_left
      rw [show x = 0 from Subsingleton.elim _ _]
      exact zero_mem _
    rcases subsingleton_or_nontrivial C with hssC | hntC
    · have := hssC
      have htop : S.comap ρ.toStarAlgHom = ⊤ :=
        eq_top_iff.mpr fun b _ => by
          show ρ.toStarAlgHom b ∈ S
          rw [show ρ.toStarAlgHom b = 0 from Subsingleton.elim _ _]
          exact zero_mem _
      rw [htop, tensorSub_top]
      trivial
    have := hntA
    have := hntB
    have := hntC
    have hntS : Nontrivial (VNSub C S hS) :=
      ⟨⟨1, 0, fun h => one_ne_zero (congrArg VNSub.val h)⟩⟩
    obtain ⟨ε, hεeq, hεfst⟩ := exists_preimagePullback ρ S hS hntS hcomap
    have hten := tensor_equalisers (C := A) (nmiuComp ρ pairFst)
      (nmiuComp VNSub.valNMIU pairSnd) ε hεeq
    have hΨinj : Function.Injective
        ⇑(tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A)) :=
      tmapM_injective _ _ VNSub.valNMIU_injective (fun _ _ h => h)
    have hTvn : IsVNSubalgebra (VNT C A)
        (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS))
          (nmiuId A)).toStarAlgHom.range := nmiu_image _
    have hmemΨ : ∀ y, tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A) y
        ∈ (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS))
            (nmiuId A)).toStarAlgHom.range := fun y => ⟨y, rfl⟩
    have hκbij : Function.Bijective ⇑(nmiuCorestrict
        (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A)) _ hTvn hmemΨ) :=
      nmiuCorestrict_bijective _ _ hTvn hmemΨ hΨinj (by rintro _ ⟨y, rfl⟩; exact ⟨y, rfl⟩)
    have hle : tensorSub A S ≤ (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS))
        (nmiuId A)).toStarAlgHom.range := by
      refine sInf_le ⟨hTvn, ?_⟩
      rintro _ ⟨t, ht, a, rfl⟩
      refine ⟨(⟨t, ht⟩ : VNSub C S hS) ⊗ᵥ a, ?_⟩
      show tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A)
        ((⟨t, ht⟩ : VNSub C S hS) ⊗ᵥ a) = t ⊗ᵥ a
      rw [tmapM_apply, nmiuId_apply]
      rfl
    have hWvn : IsVNSubalgebra (VNT B A)
        ((tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom) :=
      isVNSubalgebra_comap (tmapM ρ (nmiuId A)).toStarAlgHom
        (tmapM ρ (nmiuId A)).preservesDirSups' _ (isVNSubalgebra_wstar _).1
    have hvmem : ∀ z : VNSub (VNT B A)
        ((tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom) hWvn,
        tmapM ρ (nmiuId A) (VNSub.valNMIU z)
          ∈ (tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS))
              (nmiuId A)).toStarAlgHom.range := fun z => hle z.property
    obtain ⟨v, hvΨ⟩ : ∃ v : NMIUMap (VNSub (VNT B A)
        ((tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom) hWvn)
        (VNT (VNSub C S hS) A),
        ∀ z, tmapM (VNSub.valNMIU (A := C) (S := S) (hS := hS)) (nmiuId A) (v z)
          = tmapM ρ (nmiuId A) (VNSub.valNMIU z) := by
      refine ⟨nmiuComp (nmiuSymm _ hκbij)
        (nmiuCorestrict (nmiuComp (tmapM ρ (nmiuId A)) VNSub.valNMIU) _ hTvn hvmem),
        fun z => ?_⟩
      exact congrArg VNSub.val (nmiuSymm_apply_apply' _ hκbij
        (nmiuCorestrict (nmiuComp (tmapM ρ (nmiuId A)) VNSub.valNMIU) _ hTvn hvmem z))
    have hntVNT : ∀ b : ULift.{u} Bool, Nontrivial (VNT (pairFam B (VNSub C S hS) b) A) :=
      fun _ => vnt_nontrivial
    obtain ⟨θ, hθbij, hθa⟩ := exists_sumTensorIso (Aa := A) (pairFam B (VNSub C S hS))
    obtain ⟨wp, hw0, hw1⟩ :
        ∃ w : NMIUMap (VNSub (VNT B A)
            ((tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom) hWvn)
            (lp (fun b : ULift.{u} Bool => VNT (pairFam B (VNSub C S hS) b) A) ∞),
          (∀ z, ((w z : lp (fun b : ULift.{u} Bool => VNT (pairFam B (VNSub C S hS) b) A) ∞) :
              ∀ b : ULift.{u} Bool, VNT (pairFam B (VNSub C S hS) b) A) ⟨true⟩ = VNSub.valNMIU z) ∧
          (∀ z, ((w z : lp (fun b : ULift.{u} Bool => VNT (pairFam B (VNSub C S hS) b) A) ∞) :
              ∀ b : ULift.{u} Bool, VNT (pairFam B (VNSub C S hS) b) A) ⟨false⟩ = v z) := by
      obtain ⟨w, hw, -⟩ :=
        vn_products_nmiu (fun b : ULift.{u} Bool => VNT (pairFam B (VNSub C S hS) b) A)
          (fun b => match b with
            | ⟨true⟩ => (VNSub.valNMIU : NMIUMap (VNSub (VNT B A)
                ((tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom) hWvn)
                (VNT B A))
            | ⟨false⟩ => v)
      exact ⟨w, fun z => hw ⟨true⟩ z, fun z => hw ⟨false⟩ z⟩
    obtain ⟨hm, hfst, hsnd⟩ : ∃ hm : NMIUMap (VNSub (VNT B A)
        ((tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom) hWvn)
        (VNT (lp (pairFam B (VNSub C S hS)) ∞) A),
        (∀ z, tmapM pairFst (nmiuId A) (hm z) = VNSub.valNMIU z) ∧
        (∀ z, tmapM pairSnd (nmiuId A) (hm z) = v z) := by
      refine ⟨nmiuComp (nmiuSymm θ hθbij) wp, fun z => ?_, fun z => ?_⟩
      · have h := hθa (nmiuSymm θ hθbij (wp z)) ⟨true⟩
        rw [nmiuSymm_apply_apply' θ hθbij (wp z), hw0] at h
        exact h.symm
      · have h := hθa (nmiuSymm θ hθbij (wp z)) ⟨false⟩
        rw [nmiuSymm_apply_apply' θ hθbij (wp z), hw1] at h
        exact h.symm
    have hcond : ∀ z, tmapM (nmiuComp ρ pairFst) (nmiuId A) (hm z)
        = tmapM (nmiuComp (VNSub.valNMIU (A := C) (S := S) (hS := hS)) pairSnd)
            (nmiuId A) (hm z) := by
      intro z
      rw [← tmapM_comp_id, ← tmapM_comp_id, hfst, hsnd]
      exact (hvΨ z).symm
    obtain ⟨k, hk, -⟩ := hten.2 _ hm hcond
    have heq : nmiuComp (pairFst (X := B) (Y := VNSub C S hS)) ε
        = VNSub.valNMIU (A := B) (S := S.comap ρ.toStarAlgHom) (hS := hcomap) :=
      DFunLike.coe_injective (funext fun t => hεfst t)
    have hx'' : x ∈ (tensorSub A S).comap (tmapM ρ (nmiuId A)).toStarAlgHom := hx'
    have hkey : x = tmapM (VNSub.valNMIU (A := B) (S := S.comap ρ.toStarAlgHom)
        (hS := hcomap)) (nmiuId A) (k ⟨x, hx''⟩) :=
      calc x = tmapM pairFst (nmiuId A) (hm ⟨x, hx''⟩) := (hfst ⟨x, hx''⟩).symm
        _ = tmapM pairFst (nmiuId A) (tmapM ε (nmiuId A) (k ⟨x, hx''⟩)) := by
              rw [hk ⟨x, hx''⟩]
        _ = tmapM (nmiuComp pairFst ε) (nmiuId A) (k ⟨x, hx''⟩) := tmapM_comp_id _ _ _
        _ = tmapM (VNSub.valNMIU (A := B) (S := S.comap ρ.toStarAlgHom)
              (hS := hcomap)) (nmiuId A) (k ⟨x, hx''⟩) := by rw [heq]
    rw [hkey]
    have hrange := tmapM_left_range_le (A₀ := A)
      (VNSub.valNMIU (A := B) (S := S.comap ρ.toStarAlgHom) (hS := hcomap))
      (k ⟨x, hx''⟩)
    rwa [vnsub_valNMIU_range] at hrange
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

/-! ## 125eIII `tensorBsurjectivity` -/

/-- **125eIII** (`tensorBsurjectivity`, proc.tex:5586, Lemma): given a
`(·) ⊗ ℬ`-surjective nmiu-map `s : 𝒜 → 𝒞 ⊗ ℬ` and an nmiu-map
`ρ : 𝒞 → 𝒟`, the composite `(ρ ⊗ ℬ) ∘ s` is `(·) ⊗ ℬ`-surjective iff
`ρ` is surjective.

`mp` (proc.tex:5620) needs neither `hs` nor 125VIIb: `range(ρ ⊗ ℬ)` sits
inside `ρ(𝒞) ⊗ ℬ` by `tmapM_range_le`, and `ρ(𝒞)` is a von Neumann
subalgebra by 69IVb `nmiu_image`, so surjectivity of the composite forces
`ρ(𝒞) = ⊤`.  `mpr` (proc.tex:5600) is 125VIIb `tensor_preimage`: a von
Neumann subalgebra `𝒮 ⊆ 𝒟` with `((ρ ⊗ ℬ) ∘ s)(𝒜) ⊆ 𝒮 ⊗ ℬ` pulls back to
`s(𝒜) ⊆ ρ⁻¹(𝒮) ⊗ ℬ`, whence `ρ⁻¹(𝒮) = ⊤` and, `ρ` being onto, `𝒮 = ⊤`. -/
theorem tensorBsurjectivity [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] [VonNeumannAlgebra D]
    (s : NMIUMap A (VNT C B)) (hs : TensorBSurjective s)
    (ρ : NMIUMap C D) :
    TensorBSurjective (nmiuComp (tmapM ρ (nmiuId B)) s) ↔
      Function.Surjective ⇑ρ := by
  refine ⟨fun hcomp => ?_, fun hρ => ?_⟩
  · -- **proc.tex:5620**, and it uses neither `hs` nor atomicity.
    have hrange : Set.range ⇑(nmiuComp (tmapM ρ (nmiuId B)) s)
        ⊆ ((tensorSub B ρ.toStarAlgHom.range : StarSubalgebra ℂ (VNT D B)) :
          Set (VNT D B)) := by
      rintro _ ⟨a, rfl⟩
      exact tmapM_range_le ρ (s a)
    have htop := hcomp ρ.toStarAlgHom.range (nmiu_image ρ) hrange
    intro d
    have hd : d ∈ ρ.toStarAlgHom.range := by rw [htop]; trivial
    exact hd
  · -- **proc.tex:5600**, through 125VIIb `tensor_preimage`.
    intro S hS hsub
    have h1 : Set.range ⇑s ⊆
        ((tensorSub B (S.comap ρ.toStarAlgHom) : StarSubalgebra ℂ (VNT C B)) :
          Set (VNT C B)) := by
      rintro _ ⟨a, rfl⟩
      have hmem : s a ∈ ⇑(tmapM ρ (nmiuId B)) ⁻¹'
          ((tensorSub B S : StarSubalgebra ℂ (VNT D B)) : Set (VNT D B)) :=
        hsub ⟨a, rfl⟩
      rw [tensor_preimage (A := B) ρ S hS] at hmem
      exact hmem
    have h2 := hs _ (isVNSubalgebra_comap ρ.toStarAlgHom ρ.preservesDirSups' S hS) h1
    refine eq_top_iff.mpr fun d _ => ?_
    obtain ⟨c, rfl⟩ := hρ d
    have hc : c ∈ S.comap ρ.toStarAlgHom := by rw [h2]; trivial
    exact hc

end ParsecEnd


section ParsecEndTwo

open EqL


/-! ## The minimal `𝒮` with `s(𝒳) ⊆ 𝒮 ⊗ 𝒜`, and what it is good for -/

/-- `f ⊗ id` carries `𝒮 ⊗ 𝒜` into `f(𝒮) ⊗ 𝒜`. -/
private theorem tensorSub_map_left {𝒞₁ 𝒞₂ 𝒜 : Type u}
    [CStarAlgebra 𝒞₁] [PartialOrder 𝒞₁] [StarOrderedRing 𝒞₁] [VonNeumannAlgebra 𝒞₁]
    [CStarAlgebra 𝒞₂] [PartialOrder 𝒞₂] [StarOrderedRing 𝒞₂] [VonNeumannAlgebra 𝒞₂]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (f : NMIUMap 𝒞₁ 𝒞₂) (S : StarSubalgebra ℂ 𝒞₁) {z : VNT 𝒞₁ 𝒜}
    (hz : z ∈ tensorSub 𝒜 S) :
    tmapM f (nmiuId 𝒜) z ∈ tensorSub 𝒜 (S.map f.toStarAlgHom) := by
  have hle : tensorSub 𝒜 S ≤
      (tensorSub 𝒜 (S.map f.toStarAlgHom)).comap
        (tmapM f (nmiuId 𝒜)).toStarAlgHom := by
    refine sInf_le ⟨isVNSubalgebra_comap (tmapM f (nmiuId 𝒜)).toStarAlgHom
      (tmapM f (nmiuId 𝒜)).preservesDirSups' _ (isVNSubalgebra_wstar _).1, ?_⟩
    rintro _ ⟨t, ht, a, rfl⟩
    show tmapM f (nmiuId 𝒜) (t ⊗ᵥ a) ∈ tensorSub 𝒜 (S.map f.toStarAlgHom)
    rw [tmapM_apply, nmiuId_apply]
    exact (isVNSubalgebra_wstar _).2 ⟨f t, ⟨t, ht, rfl⟩, a, rfl⟩
  exact hle hz

/-- **The least `𝒮` with `s(𝒳) ⊆ 𝒮 ⊗ 𝒜`**, for any nmiu-map
`s : 𝒳 → 𝒞 ⊗ 𝒜`.

It is `W*({r_ξ(s(x))})`, the von Neumann subalgebra generated by all the
slices of all the values of `s` — the same generating set 125IV
`equaliser_lemma` builds, and the proof that `s(𝒳) ⊆ 𝒮 ⊗ 𝒜` is 125IV's own
(`mem_tensorSub_of_rSlice_mem` up in `𝒞 ⊗ B(ℋ)`, then
`mem_tensorSub_of_image` — that is, 121II — to come back down to `𝒞 ⊗ 𝒜`).
Minimality is the converse slice-map property
`rSlice_mem_of_mem_tensorSub`.  No cardinality bound is claimed here; 125IV
is the version that carries one. -/
private theorem exists_minimal_tensorSub {X 𝒞 𝒜 : Type u}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (s : NMIUMap X (VNT 𝒞 𝒜)) :
    ∃ (S : StarSubalgebra ℂ 𝒞) (hS : IsVNSubalgebra 𝒞 S),
      Set.range ⇑s ⊆ (tensorSub 𝒜 S : Set (VNT 𝒞 𝒜)) ∧
      ∀ S' : StarSubalgebra ℂ 𝒞, IsVNSubalgebra 𝒞 S' →
        Set.range ⇑s ⊆ (tensorSub 𝒜 S' : Set (VNT 𝒞 𝒜)) → S ≤ S' := by
  classical
  rcases subsingleton_or_nontrivial 𝒜 with hss | hnt
  · haveI := hss
    haveI : Subsingleton (VNT 𝒞 𝒜) := vnt_subsingleton
    refine ⟨wstar 𝒞 (∅ : Set 𝒞), (isVNSubalgebra_wstar _).1, ?_,
      fun S' hS' _ => sInf_le ⟨hS', Set.empty_subset _⟩⟩
    rintro _ ⟨x, rfl⟩
    have h0 : s x = 0 := Subsingleton.elim _ _
    rw [h0]
    exact zero_mem _
  · haveI := hnt
    obtain ⟨rep, -⟩ := vn_gns_bound (A := 𝒜)
    haveI hntBH : Nontrivial (rep.space →L[ℂ] rep.space) :=
      ⟨⟨rep.rep 0, rep.rep 1, fun hc => zero_ne_one (rep.injective hc)⟩⟩
    obtain ⟨w, e, -⟩ := exists_hilbertBasis ℂ rep.space
    have hchoice : ∀ p : X × rep.space, ∃ c : 𝒞,
        rSlice 𝒞 p.2 (tmapM (nmiuId 𝒞) rep.rep (s p.1))
          = c ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) :=
      fun p => rSlice_mem 𝒞 p.2 _
    choose r hr using hchoice
    refine ⟨wstar 𝒞 (Set.range r), (isVNSubalgebra_wstar _).1, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      refine mem_tensorSub_of_image intersectionTensorStatement rep.rep
        rep.injective _ (isVNSubalgebra_wstar _).1 (s x) ?_
      refine mem_tensorSub_of_rSlice_mem _ e _ ?_
      intro ξ c hc
      have h1 : c ⊗ᵥ (1 : rep.space →L[ℂ] rep.space)
          = r (x, ξ) ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
        rw [← hc, hr (x, ξ)]
      rw [nmiuTmulLeft_injective h1]
      exact (isVNSubalgebra_wstar _).2 ⟨(x, ξ), rfl⟩
    · intro S' hS' hsub
      refine sInf_le ⟨hS', ?_⟩
      rintro _ ⟨p, rfl⟩
      obtain ⟨x, ξ⟩ := p
      exact rSlice_mem_of_mem_tensorSub S' hS' ξ
        (tensorSub_map_right rep.rep S' (hsub ⟨x, rfl⟩)) (hr (x, ξ))

/-- **The corestriction of `s` to a least `𝒮` is `(·) ⊗ 𝒜`-surjective** —
which is 125eII's definition read backwards, and is what makes `𝒮` unique. -/
private theorem tensorBSurjective_of_minimal {X 𝒞 𝒜 : Type u}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞] [VonNeumannAlgebra 𝒞]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (s : NMIUMap X (VNT 𝒞 𝒜)) (S : StarSubalgebra ℂ 𝒞) (hS : IsVNSubalgebra 𝒞 S)
    (hmin : ∀ S' : StarSubalgebra ℂ 𝒞, IsVNSubalgebra 𝒞 S' →
      Set.range ⇑s ⊆ (tensorSub 𝒜 S' : Set (VNT 𝒞 𝒜)) → S ≤ S')
    (st : NMIUMap X (VNT (VNSub 𝒞 S hS) 𝒜))
    (hst : ∀ x : X, tmapM (VNSub.valNMIU (A := 𝒞) (S := S) (hS := hS))
      (nmiuId 𝒜) (st x) = s x) :
    TensorBSurjective st := by
  intro S' hS' hsub
  have hT := vnsub_isVNSubalgebra_map S' hS'
  have hrange : Set.range ⇑s ⊆
      ((tensorSub 𝒜 (S'.map (VNSub.valStarAlgHom (A := 𝒞) (S := S) (hS := hS))) :
        StarSubalgebra ℂ (VNT 𝒞 𝒜)) : Set (VNT 𝒞 𝒜)) := by
    rintro _ ⟨x, rfl⟩
    rw [← hst x]
    exact tensorSub_map_left (VNSub.valNMIU (A := 𝒞) (S := S) (hS := hS)) S'
      (hsub ⟨x, rfl⟩)
  have hle := hmin _ hT hrange
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨z, hz, hzy⟩ := hle y.property
  exact (VNSub.val_injective hzy : z = y) ▸ hz

/-- **A `(·) ⊗ 𝒜`-surjective `s` is an epimorphism after `(·) ⊗ 𝒜`**: two
nmiu-maps out of `P` that agree after tensoring on the values of `s` are
equal.  This is the uniqueness clause of 125VIII, and it is again the
slice-map property: the equaliser of `g` and `g'` (47V) is a von Neumann
subalgebra `𝒬 ⊆ P`, every slice of every `s(x)` lands in it by naturality of
`r_ξ`, hence `s(𝒳) ⊆ 𝒬 ⊗ 𝒜` and `𝒬 = P`. -/
private theorem nmiu_ext_of_tensorBSurjective {X Pp 𝒜 Y : Type u}
    [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra Pp] [PartialOrder Pp] [StarOrderedRing Pp] [VonNeumannAlgebra Pp]
    [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y]
    (s : NMIUMap X (VNT Pp 𝒜)) (hs : TensorBSurjective s) (g g' : NMIUMap Pp Y)
    (hgg : ∀ x : X, tmapM g (nmiuId 𝒜) (s x) = tmapM g' (nmiuId 𝒜) (s x)) :
    g = g' := by
  classical
  obtain ⟨Q, hQ, hQset⟩ := vn_equalisers g g'
  have hrange : Set.range ⇑s ⊆
      ((tensorSub 𝒜 Q : StarSubalgebra ℂ (VNT Pp 𝒜)) : Set (VNT Pp 𝒜)) := by
    rintro _ ⟨x, rfl⟩
    rcases subsingleton_or_nontrivial 𝒜 with hss | hnt
    · haveI := hss
      haveI : Subsingleton (VNT Pp 𝒜) := vnt_subsingleton
      have h0 : s x = 0 := Subsingleton.elim _ _
      rw [h0]
      exact zero_mem _
    · haveI := hnt
      obtain ⟨rep, -⟩ := vn_gns_bound (A := 𝒜)
      haveI hntBH : Nontrivial (rep.space →L[ℂ] rep.space) :=
        ⟨⟨rep.rep 0, rep.rep 1, fun hc => zero_ne_one (rep.injective hc)⟩⟩
      obtain ⟨w, e, -⟩ := exists_hilbertBasis ℂ rep.space
      refine mem_tensorSub_of_image intersectionTensorStatement rep.rep
        rep.injective _ hQ (s x) ?_
      refine mem_tensorSub_of_rSlice_mem _ e _ ?_
      intro ξ c hc
      have hg := rSlice_natural g ξ (tmapM (nmiuId Pp) rep.rep (s x))
      have hg' := rSlice_natural g' ξ (tmapM (nmiuId Pp) rep.rep (s x))
      rw [hc, tmapM_apply, nmiuId_apply, tmapM_swap] at hg
      rw [hc, tmapM_apply, nmiuId_apply, tmapM_swap] at hg'
      have hcc : g c ⊗ᵥ (1 : rep.space →L[ℂ] rep.space)
          = g' c ⊗ᵥ (1 : rep.space →L[ℂ] rep.space) := by
        rw [hg, hg', hgg x]
      have hmem : c ∈ {p : Pp | g p = g' p} := nmiuTmulLeft_injective hcc
      rw [← hQset] at hmem
      exact hmem
  have htop := hs Q hQ hrange
  refine DFunLike.coe_injective (funext fun p => ?_)
  have hp : p ∈ (Q : Set Pp) := by rw [htop]; trivial
  rw [hQset] at hp
  exact hp

/-! ## 125eIIa `tensor-map-factorisation` -/

/-- **125eIIa** (`tensor-map-factorisation`, proc.tex:5575): for any
nmiu-map `s : 𝒜 → 𝒞 ⊗ ℬ` there is a von Neumann subalgebra
`𝒞̃ ⊆ 𝒞` with `s(𝒜) ⊆ 𝒞̃ ⊗ ℬ` such that the restriction of `s` to
`𝒜 → 𝒞̃ ⊗ ℬ` is `(·) ⊗ ℬ`-surjective.

proc.tex:5575 says "by inspecting the proof of `equaliser-lemma`", and that
is what `exists_minimal_tensorSub` does: 125IV's generating set
`{r_ξ(s(a))}` generates not merely *a* `𝒞̃` that works but the *least* one,
and least is exactly `(·) ⊗ ℬ`-surjective. -/
theorem tensor_map_factorisation [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] [VonNeumannAlgebra C]
    (s : NMIUMap A (VNT C B)) :
    ∃ (S : StarSubalgebra ℂ C) (hS : IsVNSubalgebra C S),
      Set.range ⇑s ⊆ (tensorSub B S : Set (VNT C B)) ∧
      ∃ (ι : NMIUMap (VNSub C S hS) C)
        (st : NMIUMap A (VNT (VNSub C S hS) B)),
        (∀ x, ι x = x.val) ∧
        (∀ a : A, s a = tmapM ι (nmiuId B) (st a)) ∧
        TensorBSurjective st := by
  obtain ⟨S, hS, hrange, hmin⟩ := exists_minimal_tensorSub s
  obtain ⟨st, hst⟩ := exists_corestrict_tensorSub S hS s (fun a => hrange ⟨a, rfl⟩)
  exact ⟨S, hS, hrange, VNSub.valNMIU, st, fun _ => rfl, fun a => (hst a).symm,
    tensorBSurjective_of_minimal s S hS hmin st hst⟩

/-! ## 125VIII `tensor-closed`

Freyd's General Adjoint Functor Theorem, exactly as proc.tex:5061 runs it,
with the same three ingredients as 124III `second_adjunction`: a solution
set, the product over it, and a von Neumann subalgebra of that product cut
out so that the unit generates.

* The **solution set** is `TSolIdx`, the one `tensor-closed-proof` (proc.tex:5081) prints, on the nose and built
  exactly like 124III's `SolIdx`: a von Neumann algebra *carried on a subset
  `T` of `κ`* (`VNOnSet K` with `#K = κ`), together with an nmiu-map
  `ℬ → 𝒟 ⊗ 𝒜` into its tensor.  The solution set *condition* is 125IV
  `equaliser_lemma`: it factors `h : ℬ → 𝒞 ⊗ 𝒜` through `𝒞̃ ⊗ 𝒜` with `𝒞̃`
  generated by at most `#ℬ · 2^{#𝒜}` elements, whence
  `#𝒞̃ ≤ 2^{2^{𝔠 + #ℬ·2^{#𝒜}}} = #K` by 124I `vn_generation_bound`, and
  `exists_vnOnSet` then relabels its elements by a subset of `K`.
  (proc.tex:5085 writes `κ = 2^{2^{𝔠·#ℬ·2^{#𝒜}}}`, the same cardinal: the
  exponent is a sum of infinite cardinals here and a product there.)
* `(·) ⊗ 𝒜` turns the **product** `P = ⊕ᵢ 𝒟ᵢ` into the product of the
  `𝒟ᵢ ⊗ 𝒜` — 117III `tensor_distributes_over_sums` through 119IVc
  `exists_braiding`, packaged as `exists_sumTensorIso` — so the solution-set
  maps assemble into a single `η : ℬ → P ⊗ 𝒜`.
* The **carrier** is `VNSub P 𝒮₁` for the *least* `𝒮₁ ⊆ P` with
  `η(ℬ) ⊆ 𝒮₁ ⊗ 𝒜`.  Least makes the unit `(·) ⊗ 𝒜`-surjective, and that is
  precisely the uniqueness clause of the universal property
  (`nmiu_ext_of_tensorBSurjective`). -/


/-- The index of the solution set of **125VIII**, proc.tex:5070 on the nose:
a von Neumann algebra carried on a subset `T` of the fixed index type `K`,
together with an nmiu-map from `ℬ` into its tensor with `𝒜`.  Exactly
124III's `SolIdx` over the same `VNOnSet`, with an nmiu-map into the tensor
where 124III has an ncpsu-map; it lives in `Type u`, which is the whole
point of the solution set condition. -/
private structure TSolIdx (Bb Aa : Type u) [CStarAlgebra Bb] [PartialOrder Bb]
    [StarOrderedRing Bb] [VonNeumannAlgebra Bb] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] (K : Type u) extends VNOnSet K where
  hnt : Nontrivial ↥T
  γ : NMIUMap Bb (VNT ↥T Aa)

private instance tsolNontrivial {Bb Aa : Type u} [CStarAlgebra Bb] [PartialOrder Bb]
    [StarOrderedRing Bb] [VonNeumannAlgebra Bb] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] {K : Type u} (i : TSolIdx Bb Aa K) :
    Nontrivial ↥i.T := i.hnt

/-- The product `∏ᵢ 𝒟ᵢ` over the solution set (**47IV**). -/
@[reducible] private def tsolProd (Bb Aa : Type u) [CStarAlgebra Bb] [PartialOrder Bb]
    [StarOrderedRing Bb] [VonNeumannAlgebra Bb] [CStarAlgebra Aa] [PartialOrder Aa]
    [StarOrderedRing Aa] [VonNeumannAlgebra Aa] (K : Type u) : Type u :=
  lp (fun i : TSolIdx Bb Aa K => ↥i.T) ∞

set_option maxHeartbeats 1000000 in
/-- **The solution set condition** for 125VIII (proc.tex:5070): every
nmiu-map `ℬ → 𝒞 ⊗ 𝒜` into a *nontrivial* `𝒞` factors as `(t ⊗ 𝒜) ∘ γᵢ` for
one of the solution-set entries `γᵢ`.  This is 125IV `equaliser_lemma`
followed by 124I `vn_generation_bound` and `exists_vnOnSet`, in the
shape of 124III's `solution_set`. -/
private theorem tensor_solution_set (Bb Aa : Type u) [CStarAlgebra Bb]
    [PartialOrder Bb] [StarOrderedRing Bb] [VonNeumannAlgebra Bb]
    [CStarAlgebra Aa] [PartialOrder Aa] [StarOrderedRing Aa] [VonNeumannAlgebra Aa]
    {K : Type u}
    (hK : #K = (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      (Cardinal.continuum + #Bb * (2 : Cardinal.{u}) ^ #Aa))
    {C' : Type u} [CStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
    [VonNeumannAlgebra C'] [Nontrivial C'] (h : NMIUMap Bb (VNT C' Aa)) :
    ∃ (i : TSolIdx Bb Aa K) (t : NMIUMap ↥i.T C'),
      ∀ b : Bb, h b = tmapM t (nmiuId Aa) (i.γ b) := by
  classical
  have h2 : (2 : Cardinal.{u}) ≠ 0 := by norm_num
  obtain ⟨S₀, hS₀, G, hSG, hcardG, ι, ht, -, hfact, -⟩ :=
    equaliser_lemma (A := C') (C := Aa) (D := Bb) h
  subst hSG
  have hgen : wstar (VNSub C' (wstar C' G) hS₀) (VNSub.val ⁻¹' G) = ⊤ := by
    refine vnsub_wstar_eq_top _ (isVNSubalgebra_wstar _).1 fun x hx => ?_
    exact (isVNSubalgebra_wstar (A := VNSub C' (wstar C' G) hS₀)
      (VNSub.val ⁻¹' G)).2 hx
  have hcardG' : #((VNSub.val ⁻¹' G : Set (VNSub C' (wstar C' G) hS₀)))
      ≤ #Bb * (2 : Cardinal.{u}) ^ #Aa := by
    refine le_trans (Cardinal.mk_le_of_injective
      (f := fun x : (VNSub.val ⁻¹' G : Set (VNSub C' (wstar C' G) hS₀)) =>
        (⟨x.val.val, x.property⟩ : G)) ?_) hcardG
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    exact Subtype.ext (VNSub.val_injective (congrArg Subtype.val hxy))
  have hcard : #(VNSub C' (wstar C' G) hS₀) ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        (Cardinal.continuum + #Bb * (2 : Cardinal.{u}) ^ #Aa) := by
    refine le_trans (vn_generation_bound _ hgen) ?_
    exact Cardinal.power_le_power_left h2 (Cardinal.power_le_power_left h2
      (add_le_add le_rfl hcardG'))
  obtain ⟨V, ⟨Φ⟩⟩ :=
    exists_vnOnSet (K := K) (VNSub C' (wstar C' G) hS₀) (by rw [hK]; exact hcard)
  have hntC : Nontrivial (VNSub C' (wstar C' G) hS₀) :=
    ⟨⟨1, 0, fun hq => one_ne_zero (congrArg VNSub.val hq)⟩⟩
  -- as in `solution_set`: `ε` is introduced by `obtain`, not by `let`, or
  -- `nmiuSymm_apply_apply` will not rewrite through the let-bound value.
  obtain ⟨ε, hεbij⟩ : ∃ ε : NMIUMap (VNSub C' (wstar C' G) hS₀) ↥V.T,
      Function.Bijective ⇑ε :=
    ⟨⟨Φ.toStarAlgHom, starAlgEquiv_preservesDirSups' Φ⟩, Φ.bijective⟩
  have hntS : Nontrivial ↥V.T :=
    ⟨⟨ε 1, ε 0, fun hq => one_ne_zero (hεbij.1 hq)⟩⟩
  refine ⟨⟨V, hntS, nmiuComp (tmapM ε (nmiuId Aa)) ht⟩,
    nmiuComp ι (nmiuSymm ε hεbij), fun b => ?_⟩
  show h b = tmapM (nmiuComp ι (nmiuSymm ε hεbij)) (nmiuId Aa)
    (tmapM ε (nmiuId Aa) (ht b))
  rw [tmapM_comp_id]
  have hmap : nmiuComp (nmiuComp ι (nmiuSymm ε hεbij)) ε = ι :=
    DFunLike.coe_injective (funext fun y => by
      show ι (nmiuSymm ε hεbij (ε y)) = ι y
      rw [nmiuSymm_apply_apply])
  rw [hmap]
  exact hfact b

set_option maxHeartbeats 1000000 in
/-- **125VIII** (`tensor-closed`, proc.tex:5054, Theorem (Kornell)): the
functor `(·) ⊗ 𝒜 : W*_miu → W*_miu` has a left adjoint `(·)^{*𝒜}` —
rendered: every `ℬ` has a universal arrow `ℬ → ℬ^{*𝒜} ⊗ 𝒜`. -/
theorem tensor_closed [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    Nonempty (FreeExp B A) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : Type u, #K = (2 : Cardinal.{u}) ^
      (2 : Cardinal.{u}) ^ (Cardinal.continuum + #B * (2 : Cardinal.{u}) ^ #A) :=
    ⟨_, Cardinal.mk_out _⟩
  -- **weak initiality**: the mediating map `η : ℬ → P ⊗ 𝒜`, whose `i`-th
  -- coordinate is the solution-set entry `i` itself
  obtain ⟨η, hη⟩ : ∃ η : NMIUMap B (VNT (tsolProd B A K) A),
      ∀ (i : TSolIdx B A K) (b : B),
        tmapM (lpEvalNMIU
          (fun q : TSolIdx B A K => (↥q.T : Type u)) i) (nmiuId A) (η b)
          = i.γ b := by
    rcases subsingleton_or_nontrivial A with hss | hnt
    · haveI := hss
      haveI : Subsingleton (VNT (tsolProd B A K) A) := vnt_subsingleton
      haveI : ∀ i : TSolIdx B A K,
          Subsingleton (VNT ↥i.T A) :=
        fun _ => vnt_subsingleton
      exact ⟨nmiuOfSubsingleton B (VNT (tsolProd B A K) A),
        fun i b => Subsingleton.elim _ _⟩
    · haveI := hnt
      haveI hntv : ∀ i : TSolIdx B A K,
          Nontrivial (VNT ↥i.T A) :=
        fun _ => vnt_nontrivial
      obtain ⟨θ, hθbij, hθa⟩ := exists_sumTensorIso (Aa := A)
        (fun i : TSolIdx B A K => (↥i.T : Type u))
      obtain ⟨pr, hpr, -⟩ := vn_products_nmiu (B := B)
        (fun i : TSolIdx B A K => VNT ↥i.T A) (fun i => i.γ)
      refine ⟨nmiuComp (nmiuSymm θ hθbij) pr, fun i b => ?_⟩
      have h1 := hθa (nmiuSymm θ hθbij (pr b)) i
      rw [nmiuSymm_apply_apply'] at h1
      show tmapM (lpEvalNMIU
        (fun q : TSolIdx B A K => (↥q.T : Type u)) i) (nmiuId A)
          (nmiuSymm θ hθbij (pr b)) = i.γ b
      rw [← h1]
      exact hpr i b
  -- **the carrier**: the least von Neumann subalgebra `𝒮₁ ⊆ P` with
  -- `η(ℬ) ⊆ 𝒮₁ ⊗ 𝒜`
  obtain ⟨S₁, hS₁, hrange, hmin⟩ := exists_minimal_tensorSub η
  obtain ⟨un, hun⟩ :=
    exists_corestrict_tensorSub S₁ hS₁ η (fun b => hrange ⟨b, rfl⟩)
  have hsurj : TensorBSurjective un :=
    tensorBSurjective_of_minimal η S₁ hS₁ hmin un hun
  refine ⟨{ carrier := VNSub (tsolProd B A K) S₁ hS₁
            unit := un
            universal := fun C' _ _ _ _ h => ?_ }⟩
  rcases subsingleton_or_nontrivial C' with hsub | hntC
  · haveI := hsub
    haveI : Subsingleton (VNT C' A) := vnt_subsingleton_left
    exact ⟨nmiuOfSubsingleton (VNSub (tsolProd B A K) S₁ hS₁) C',
      fun _ => Subsingleton.elim _ _,
      fun _ _ => DFunLike.coe_injective (funext fun _ => Subsingleton.elim _ _)⟩
  · haveI := hntC
    obtain ⟨i, t, hti⟩ := tensor_solution_set B A hK h
    have hmain : ∀ b : B, h b = tmapM
        (nmiuComp (nmiuComp t (lpEvalNMIU
            (fun q : TSolIdx B A K => (↥q.T : Type u)) i))
          (VNSub.valNMIU (A := tsolProd B A K) (S := S₁) (hS := hS₁)))
        (nmiuId A) (un b) := by
      intro b
      rw [← tmapM_comp_id, ← tmapM_comp_id, hun b, hη i b]
      exact hti b
    exact ⟨_, hmain, fun g' hg' =>
      nmiu_ext_of_tensorBSurjective un hsurj g' _
        (fun b => (hg' b).symm.trans (hmain b))⟩

end ParsecEndTwo

/-! ## Atomic type I algebras: the packaged statements

`HereditarilyAtomic` (**84bII**, `A/VN/Division.lean`) asks for
`⊕ⱼ M_{nⱼ}`.  `AtomicTypeIRep` is its sibling with the summands widened to
`B(𝒦ⱼ)` for arbitrary nonzero Hilbert spaces `𝒦ⱼ` — the *atomic type I*
von Neumann algebras.  A hereditarily atomic algebra is atomic type I with
all the `𝒦ⱼ` finite dimensional (`𝒦ⱼ = ℂ^{nⱼ}`); the implication
`HereditarilyAtomic 𝒜 → AtomicTypeI 𝒜` is **not** proved here, because it
needs `M_n ≅ B(ℂⁿ)` (Mathlib's `Matrix.toEuclideanCLM`) *plus* a universe
lift — `EuclideanSpace ℂ (Fin n) : Type 0` while `AtomicTypeIRep.K :
J → Type u`, and neither Mathlib nor the tree puts an `InnerProductSpace`
on `ULift`.  Nothing below needs it. -/

section AtomicTypeI

set_option synthInstance.maxHeartbeats 400000

/-- The data of an **atomic type I** presentation `𝒜 ≅ ⊕ⱼ B(𝒦ⱼ)`.  The
`𝒦ⱼ` are arbitrary *nonzero* Hilbert spaces; requiring them nonzero keeps
the summands nontrivial and loses no generality, exactly as the `Nᵢ + 1` of
**84bII** does. -/
structure AtomicTypeIRep (𝒜 : Type u) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] : Type (u + 1) where
  /-- The index set of the blocks. -/
  J : Type u
  /-- The Hilbert space of the `j`-th block. -/
  K : J → Type u
  [nag : ∀ j, NormedAddCommGroup (K j)]
  [ips : ∀ j, InnerProductSpace ℂ (K j)]
  [cs : ∀ j, CompleteSpace (K j)]
  [nt : ∀ j, Nontrivial (K j)]
  /-- The identification `𝒜 ≅ ⊕ⱼ B(𝒦ⱼ)`. -/
  iso : 𝒜 ≃⋆ₐ[ℂ] lp (fun j : J => (K j →L[ℂ] K j)) ∞

attribute [instance] AtomicTypeIRep.nag AtomicTypeIRep.ips AtomicTypeIRep.cs
  AtomicTypeIRep.nt

variable (A) in
/-- A von Neumann algebra is **atomic type I** when it is nmiu-isomorphic to
a direct sum `⊕ⱼ B(𝒦ⱼ)` of type I factors. -/
def AtomicTypeI [VonNeumannAlgebra A] : Prop := Nonempty (AtomicTypeIRep A)

/-- A Hilbert basis of a nonzero Hilbert space has a nonempty index set. -/
private theorem hilbertBasis_index_nonempty {ι : Type*} {Kk : Type*}
    [NormedAddCommGroup Kk] [InnerProductSpace ℂ Kk] [Nontrivial Kk]
    (e : HilbertBasis ι ℂ Kk) : Nonempty ι := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Kk
  have hz : ∀ z : Kk, z = 0 := fun z =>
    (e.hasSum_repr z).unique (hasSum_empty (f := fun i : ι => (e.repr z) i • e i))
  exact hxy ((hz x).trans (hz y).symm)

set_option linter.unusedVariables false in
/-- **125VIIb** (`tensor-preimage`, proc.tex:5031) for an **atomic type I**
tensored factor: for an nmiu-map `ρ : ℬ → 𝒞`, a von Neumann subalgebra
`𝒮 ⊆ 𝒞` and `𝒜 ≅ ⊕ⱼ B(𝒦ⱼ)`, `(ρ ⊗ id_𝒜)⁻¹(𝒮 ⊗ 𝒜) = ρ⁻¹(𝒮) ⊗ 𝒜`.

This is the Exercise's own statement with a redundant hypothesis: 125VIIb
`tensor_preimage`, proved above for *every* `𝒜`, gives it outright, and
`R` is not used.  It was proved separately, from the widened slice device
`atTensorPreimage`, only while 125VIIb still stood after it in the file. -/
theorem atomicTypeI_tensor_preimage [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (R : AtomicTypeIRep A) (ρ : NMIUMap B C)
    (S : StarSubalgebra ℂ C) (hS : IsVNSubalgebra C S) :
    ⇑(tmapM ρ (nmiuId A)) ⁻¹' (tensorSub A S : Set (VNT C A)) =
      (tensorSub A (S.comap ρ.toStarAlgHom) : Set (VNT B A)) :=
  tensor_preimage (A := A) ρ S hS

set_option linter.unusedVariables false in
/-- **125eIII** (`tensorBsurjectivity`, proc.tex:5600) for an **atomic type
I** tensored factor `ℬ ≅ ⊕ⱼ B(𝒦ⱼ)`: `(ρ ⊗ ℬ) ∘ s` is `(·) ⊗ ℬ`-surjective
iff `ρ` is surjective.

This is the Lemma's own statement with a redundant hypothesis: 125eIII
`tensorBsurjectivity`, proved above for *every* `ℬ`, gives it outright, and
`R` is not used.  It was proved separately, from the widened slice device
`atTensorBSurj`, only while 125eIII still stood after it in the file. -/
theorem atomicTypeI_tensorBsurjectivity [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] [VonNeumannAlgebra D] (R : AtomicTypeIRep B)
    (s : NMIUMap A (VNT C B)) (hs : TensorBSurjective s) (ρ : NMIUMap C D) :
    TensorBSurjective (nmiuComp (tmapM ρ (nmiuId B)) s) ↔
      Function.Surjective ⇑ρ :=
  tensorBsurjectivity s hs ρ

end AtomicTypeI


section HaSliceBSurj

set_option synthInstance.maxHeartbeats 400000

universe u₁ u₂ u₃ u₄

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C] [VonNeumannAlgebra D]
variable {J : Type u} {nn : J → ℕ}
variable {X : Type u} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [VonNeumannAlgebra X]

/-- **The ha form of 125eIII** (`tensorBsurjectivity`), the easy half:
if `(ρ ⊗ 𝒜) ∘ s` is `(·) ⊗ 𝒜`-surjective then `ρ` is surjective.

It has **no consumer**: the 125eVII assembly needs the four algebras in
four universes and so uses the twin `surj_of_haTensorBSurj2` below instead,
which supersedes it.  The proof uses **nothing** about hereditary
atomicity — neither here nor in the twin does `Φ` appear — which is why the
`→` half of the general `tensorBsurjectivity` above needs
no atomicity either. -/
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

set_option linter.unusedVariables false in
/-- **The ha form of 125eIII** (`tensorBsurjectivity`), the hard half:
`(ρ ⊗ 𝒜) ∘ s` is `(·) ⊗ 𝒜`-surjective when `s` is and `ρ` is surjective.

It is **the thesis's own argument, and no longer a special case of it**:
the general 125eIII `tensorBsurjectivity` now stands above this point in
the file and delivers the statement with `Φ` unused.  The hereditarily
atomic substitute `haTensorPreimage` for 125VIIb, which the by-hand proof
used, is thereby no longer needed here. -/
private theorem haTensorBSurj
    (Φ : A ≃⋆ₐ[ℂ] lp (fun j : J => MatAlg (nn j + 1)) ∞) (s : NMIUMap X (VNT C A))
    (hs : TensorBSurjective s) (ρ : NMIUMap C D) (hρ : Function.Surjective ⇑ρ) :
    TensorBSurjective (nmiuComp (tmapM ρ (nmiuId A)) s) :=
  (tensorBsurjectivity s hs ρ).mpr hρ

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

/- **125eIIa** (`tensor-map-factorisation`, proc.tex:5575) is
`tensor_map_factorisation`, above in this file, and **125eIII**
(`tensorBsurjectivity`, proc.tex:5586) is `tensorBsurjectivity` there: both
consume the slice-map property, i.e. 121II. -/


/-- **125eVI** (proc.tex:5636, Definition): two nmiu-maps
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

/-- **125eVII** (`AstarhaB-concrete`, proc.tex:5658, Theorem): for
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

