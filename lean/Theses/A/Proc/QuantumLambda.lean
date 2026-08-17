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

/-- **123II** (proc.tex:4663, Exercise), part 2: `(σ, τ) ↦ σ ⊗ τ` gives a
bijection `nsp(𝒜) × nsp(ℬ) → nsp(𝒜 ⊗ ℬ)` (which makes `nsp` strong
monoidal) — rendered: every pair extends uniquely to a product
nmiu-functional. -/
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
