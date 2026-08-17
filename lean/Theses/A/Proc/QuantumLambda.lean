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

