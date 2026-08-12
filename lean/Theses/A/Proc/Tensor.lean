/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex), §Tensor
product (parsecs 1070–1190): the tensor product of von Neumann algebras
defined abstractly via product functionals (108II), its existence via the
Hilbert space tensor product and the concrete (spatial) tensor product
(parsecs 1090–1110), its universal property (112XI), functoriality
(115II), miscellaneous properties, and the symmetric monoidal structure
on `W*_miu`, `W*_cp`, `W*_cpu`, and `W*_cpsu` (119V).

## Encoding

* Bilinear maps `β : 𝒜 × ℬ → 𝒞` are curried linear maps
  `β : A →ₗ[ℂ] B →ₗ[ℂ] C`; `β_⊙` is `TensorProduct.lift β` on the
  *algebraic* tensor product `A ⊗[ℂ] B` (Mathlib's `TensorProduct ℂ`).
* A tensor product of von Neumann algebras is the Prop-valued structure
  `IsTensorProduct γ` (108II).  A *chosen* tensor product is the bundle
  `VNTensorProduct A B : Type (u+1)` (carrier + instances + map); its
  existence (111XII) is a sorry-ed `Nonempty`, and `vnTensor A B` picks
  one by choice (115I).  `VNT A B` is its carrier and `a ⊗ᵥ b` the tensor
  of elements.
* Similarly for Hilbert spaces: `IsHilbertTensorProduct` (109II),
  the bundle `HilbertTensor H K`, choice `hilbTensor`, carrier `HT H K`,
  elementwise `x ⊗ₕ y`, and `opTensor A B` for operators (111V).
* Corners of the spatial construction (111VII) live on the wrapper type
  `VNSub S` of a von Neumann subalgebra `S`, with sorry-ed algebra
  instances (as for `Corner` in `Measurement.lean`).
* Maps out of the tensor (`tmap f g` for ncp-maps, `tmapM ρ σ` for
  nmiu-maps, product functionals on the predual, associators, unitors,
  braidings) are obtained by choice from sorry-ed unique-existence
  lemmas; their defining equations on pure tensors are `_apply` lemmas.
* The monoidal structure (119V) is stated concretely (naturality,
  pentagon, triangle, hexagon, symmetry — as equations between the chosen
  structure maps), not through Mathlib's `MonoidalCategory`, per the
  conversion policy's allowance for concrete phrasings.
-/
import Theses.A.Proc.Measurement

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u v w

/-! ## Parsec 1080: bilinear maps and the definition of the tensor
product

(These core notions are universe-polymorphic in the two factors so that
the tensor unit `ℂ : Type 0` can be paired with an algebra in `Type u`,
as needed for the unitors of 119IVb.) -/

section Bilinear

variable {A₁ : Type u} {B₁ : Type v} {C₁ : Type w}
  [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [CStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁]
  [CStarAlgebra C₁] [PartialOrder C₁] [StarOrderedRing C₁]

/-- **108I** (`bilinear-basic`, proc.tex:2006, Definition), part 1: a
bilinear map between von Neumann algebras is **unital** when
`β(1,1) = 1`. -/
def BilinUnital (β : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) : Prop := β 1 1 = 1

/-- **108I** (`bilinear-basic`, proc.tex:2006, Definition), part 2: a
bilinear map is **multiplicative** if `β(ab, cd) = β(a,c)·β(b,d)`. -/
def BilinMult (β : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) : Prop :=
  ∀ a b : A₁, ∀ c d : B₁, β (a * b) (c * d) = β a c * β b d

/-- **108I** (`bilinear-basic`, proc.tex:2006, Definition), part 3: a
bilinear map is **involution preserving** if `β(a,b)* = β(a*, b*)`. -/
def BilinStar (β : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) : Prop :=
  ∀ (a : A₁) (b : B₁), star (β a b) = β (star a) (star b)

/-- **108I** (`bilinear-basic`, proc.tex:2006, Definition): a bilinear map
is **miu-bilinear** when it is multiplicative, involution preserving and
unital. -/
def MIUBilinear (β : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) : Prop :=
  BilinUnital β ∧ BilinMult β ∧ BilinStar β

/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 4c: a
bilinear map is **completely positive** when
`∑_{i,j} cᵢ* β(aᵢ*aⱼ, bᵢ*bⱼ) cⱼ ≥ 0`. -/
def BilinCP (β : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A₁) (b : Fin n → B₁) (c : Fin n → C₁),
    0 ≤ ∑ i, ∑ j,
      star (c i) * β (star (a i) * a j) (star (b i) * b j) * c j

/-- **108II** (`tensor`, proc.tex:2034, Definition): an miu-bilinear map
`γ : 𝒜 × ℬ → 𝒯` between von Neumann algebras is a **tensor product** of
`𝒜` and `ℬ` when (1) the linear span of its range is ultraweakly dense in
`𝒯`; (2) for all np-functionals `σ`, `τ` the product functional
`γ(σ,τ)` (with `γ(σ,τ)(γ(a,b)) = σ(a)τ(b)`) exists and is positive
(i.e. is an np-functional); and (3) these product functionals form a
faithful collection. -/
structure IsTensorProduct [VonNeumannAlgebra A₁] [VonNeumannAlgebra B₁]
    [VonNeumannAlgebra C₁] (γ : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) : Prop where
  miu : MIUBilinear γ
  dense : @Dense C₁ (ultraweak C₁)
    (Submodule.span ℂ {t : C₁ | ∃ a b, t = γ a b} : Set C₁)
  prod_exists : ∀ (σ : NPFunctional A₁) (τ : NPFunctional B₁),
    ∃ h : NPFunctional C₁, ∀ (a : A₁) (b : B₁), h (γ a b) = σ a * τ b
  faithful : ∀ t : C₁, 0 ≤ t →
    (∀ (σ : NPFunctional A₁) (τ : NPFunctional B₁) (h : NPFunctional C₁),
      (∀ (a : A₁) (b : B₁), h (γ a b) = σ a * τ b) → h t = 0) → t = 0

/-- **108II** (`tensor`, proc.tex:2034, Definition), embedded claim: by
condition (1) there is *at most one* normal (here: ultraweakly continuous
linear) functional `h` on `𝒯` with `h(γ(a,b)) = f(a)g(b)` — the
**product functional** `γ(f,g)`. -/
theorem prod_functional_unique [VonNeumannAlgebra A₁]
    [VonNeumannAlgebra B₁] [VonNeumannAlgebra C₁]
    (γ : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁) (hγ : IsTensorProduct γ)
    (f : A₁ →ₗ[ℂ] ℂ) (g : B₁ →ₗ[ℂ] ℂ) (h₁ h₂ : C₁ →ₗ[ℂ] ℂ)
    (hc₁ : @Continuous C₁ ℂ (ultraweak C₁) _ ⇑h₁)
    (hc₂ : @Continuous C₁ ℂ (ultraweak C₁) _ ⇑h₂)
    (he₁ : ∀ (a : A₁) (b : B₁), h₁ (γ a b) = f a * g b)
    (he₂ : ∀ (a : A₁) (b : B₁), h₂ (γ a b) = f a * g b) : h₁ = h₂ := sorry

/-- The chosen product np-functional `γ(σ,τ)` of a tensor product (from
field `prod_exists` of `IsTensorProduct`, by choice). -/
noncomputable def prodNP [VonNeumannAlgebra A₁] [VonNeumannAlgebra B₁]
    [VonNeumannAlgebra C₁] {γ : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁}
    (hγ : IsTensorProduct γ) (σ : NPFunctional A₁) (τ : NPFunctional B₁) :
    NPFunctional C₁ := (hγ.prod_exists σ τ).choose

theorem prodNP_apply [VonNeumannAlgebra A₁] [VonNeumannAlgebra B₁]
    [VonNeumannAlgebra C₁] {γ : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁}
    (hγ : IsTensorProduct γ) (σ : NPFunctional A₁) (τ : NPFunctional B₁)
    (a : A₁) (b : B₁) : prodNP hγ σ τ (γ a b) = σ a * τ b :=
  (hγ.prod_exists σ τ).choose_spec a b

end Bilinear

variable {A B C D : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-! ## Parsec 1090: the tensor product of Hilbert spaces -/

section Hilbert

variable {H K L H' K' : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- **109II** (proc.tex:2101, Definition): a bilinear map
`γ : ℋ × 𝒦 → 𝒯` between Hilbert spaces is a **tensor product** when the
linear span of its range is dense in `𝒯` and
`⟨γ(x,y), γ(x',y')⟩ = ⟨x,x'⟩⟨y,y'⟩`. -/
structure IsHilbertTensorProduct {T : Type u} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T]
    (γ : H →ₗ[ℂ] K →ₗ[ℂ] T) : Prop where
  dense : Dense (Submodule.span ℂ {t : T | ∃ x y, t = γ x y} : Set T)
  inner_mul : ∀ (x x' : H) (y y' : K),
    ⟪γ x y, γ x' y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫

/-- **109III** (proc.tex:2117, Exercise), part 1: the map
`γ(f,g) = (f(x)g(y))_{x,y} : ℓ²(X) × ℓ²(Y) → ℓ²(X×Y)` is a tensor
product of Hilbert spaces. -/
theorem l2_tensor (X Y : Type u) :
    ∃ γ : lp (fun _ : X => ℂ) 2 →ₗ[ℂ] lp (fun _ : Y => ℂ) 2 →ₗ[ℂ]
        lp (fun _ : X × Y => ℂ) 2,
      (∀ f g x y, γ f g (x, y) = f x * g y) ∧ IsHilbertTensorProduct γ :=
  sorry

/-- **109III** (proc.tex:2117, Exercise), part 2: a subset `E` of a
Hilbert space `ℋ` is an orthonormal basis iff `x ↦ ∑_{e∈E} x_e e` is an
isometric isomorphism `ℓ²(E) → ℋ`. -/
theorem orthonormal_basis_iff_l2_iso (E : Set H) :
    (Orthonormal ℂ (fun e : E => (e : H)) ∧
        Dense (Submodule.span ℂ E : Set H)) ↔
      ∃ T : lp (fun _ : E => ℂ) 2 ≃ₗᵢ[ℂ] H,
        ∀ x : lp (fun _ : E => ℂ) 2, T x = ∑' e : E, x e • (e : H) := sorry

variable (H K) in
/-- **110VI** (proc.tex:2349, Notation): a bundled (chosen) tensor product
of the Hilbert spaces `H` and `K`. -/
structure HilbertTensor : Type (u + 1) where
  space : Type u
  [nacg : NormedAddCommGroup space]
  [ips : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]
  map : H →ₗ[ℂ] K →ₗ[ℂ] space
  isTensor : IsHilbertTensorProduct map

attribute [instance] HilbertTensor.nacg HilbertTensor.ips
  HilbertTensor.complete

variable (H K) in
/-- **109III** (proc.tex:2117, Exercise), part 3: any pair of Hilbert
spaces has a tensor product (via orthonormal bases and part 1). -/
theorem hilbertTensor_nonempty : Nonempty (HilbertTensor H K) := sorry

variable (H K) in
/-- **110VI** (proc.tex:2349, Notation): a chosen tensor product
`⊗ : ℋ × 𝒦 → ℋ ⊗ 𝒦` of Hilbert spaces. -/
noncomputable def hilbTensor : HilbertTensor H K :=
  (hilbertTensor_nonempty H K).some

variable (H K) in
/-- The carrier `ℋ ⊗ 𝒦` of the chosen Hilbert space tensor product. -/
abbrev HT : Type u := (hilbTensor H K).space

/-- The elementary tensor `x ⊗ y ∈ ℋ ⊗ 𝒦`. -/
noncomputable def htmul (x : H) (y : K) : HT H K := (hilbTensor H K).map x y

@[inherit_doc] scoped infixr:70 " ⊗ₕ " => htmul

/-- **109IV** (`hilb-tensor-basic`, proc.tex:2145, Proposition), part 1:
`‖γ(x,y)‖ = ‖x‖·‖y‖` for a tensor product of Hilbert spaces. -/
theorem hilb_tensor_basic_1 {T : Type u} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] (γ : H →ₗ[ℂ] K →ₗ[ℂ] T)
    (hγ : IsHilbertTensorProduct γ) (x : H) (y : K) :
    ‖γ x y‖ = ‖x‖ * ‖y‖ := sorry

/-- **109IV** (`hilb-tensor-basic`, proc.tex:2145, Proposition), part 2:
for orthonormal bases `ℰ` of `ℋ` and `ℱ` of `𝒦` the set
`{γ(e,f) : e ∈ ℰ, f ∈ ℱ}` is an orthonormal basis of `𝒯`. -/
theorem hilb_tensor_basic_2 {T : Type u} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] (γ : H →ₗ[ℂ] K →ₗ[ℂ] T)
    (hγ : IsHilbertTensorProduct γ) (E : Set H) (F : Set K)
    (hE : Orthonormal ℂ (fun e : E => (e : H)) ∧
      Dense (Submodule.span ℂ E : Set H))
    (hF : Orthonormal ℂ (fun f : F => (f : K)) ∧
      Dense (Submodule.span ℂ F : Set K)) :
    Orthonormal ℂ
        (fun t : {t : T | ∃ e ∈ E, ∃ f ∈ F, t = γ e f} => (t : T)) ∧
      Dense (Submodule.span ℂ {t : T | ∃ e ∈ E, ∃ f ∈ F, t = γ e f} :
        Set T) := sorry

/-- **110I** (proc.tex:2201, Definition): a bilinear map
`β : ℋ × 𝒦 → ℒ` between Hilbert spaces is **ℓ²-bounded** by
`B ∈ [0,∞)` when
`‖∑ᵢ β(xᵢ,yᵢ)‖² ≤ B² ∑_{i,j} ⟨xᵢ,xⱼ⟩⟨yᵢ,yⱼ⟩`. -/
def L2Bounded (β : H →ₗ[ℂ] K →ₗ[ℂ] L) (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ (n : ℕ) (x : Fin n → H) (y : Fin n → K),
    ‖∑ i, β (x i) (y i)‖ ^ 2 ≤
      bound ^ 2 * (∑ i, ∑ j, ⟪x i, x j⟫ * ⟪y i, y j⟫).re

/-- **110III** (`hilb-tensor-universal-property`, proc.tex:2232, Theorem):
a tensor product `γ : ℋ × 𝒦 → 𝒯` of Hilbert spaces is ℓ²-bounded (by 1)
and initial as such: for any bilinear `β : ℋ × 𝒦 → ℒ` that is ℓ²-bounded
by `B` there is a unique bounded linear map `β_γ : 𝒯 → ℒ` with
`β_γ(γ(x,y)) = β(x,y)`; moreover `‖β_γ‖ ≤ B`. -/
theorem hilb_tensor_universal_property {T : Type u} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] (γ : H →ₗ[ℂ] K →ₗ[ℂ] T)
    (hγ : IsHilbertTensorProduct γ) :
    L2Bounded γ 1 ∧
      ∀ (β : H →ₗ[ℂ] K →ₗ[ℂ] L) (bound : ℝ), L2Bounded β bound →
        ∃! f : T →L[ℂ] L, (∀ x y, f (γ x y) = β x y) ∧ ‖f‖ ≤ bound := sorry

/-- **110V** (proc.tex:2338, Exercise): the tensor product of Hilbert
spaces is unique up to a unique isometric isomorphism. -/
theorem hilb_tensor_unique {T T' : Type u} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] [NormedAddCommGroup T']
    [InnerProductSpace ℂ T'] [CompleteSpace T']
    (γ : H →ₗ[ℂ] K →ₗ[ℂ] T) (γ' : H →ₗ[ℂ] K →ₗ[ℂ] T')
    (hγ : IsHilbertTensorProduct γ) (hγ' : IsHilbertTensorProduct γ') :
    ∃! φ : T ≃ₗᵢ[ℂ] T', ∀ x y, φ (γ x y) = γ' x y := sorry

/-! ## Parsec 1110: Schur's product theorem; the spatial tensor product -/

/-- **111II** (`schur`, proc.tex:2372, Lemma; part of Schur's product
theorem): the entrywise (Hadamard) product of positive `N×N`-matrices
over `ℂ` is positive. -/
theorem schur (N : ℕ) (a b : Matrix (Fin N) (Fin N) ℂ)
    (ha : a.PosSemidef) (hb : b.PosSemidef) :
    (Matrix.hadamard a b).PosSemidef := sorry

/-- **111IV** (`mult-completely-monotone`, proc.tex:2428, Exercise): for
positive matrices `a ≤ ã` and `b ≤ b̃` over `ℂ` (of the same dimensions)
the Hadamard products satisfy `a ⊙ b ≤ ã ⊙ b̃`. -/
theorem mult_completely_monotone (N : ℕ)
    (a a' b b' : Matrix (Fin N) (Fin N) ℂ) (ha : a.PosSemidef)
    (hb : b.PosSemidef) (hab : (a' - a).PosSemidef)
    (hbb : (b' - b).PosSemidef) :
    (Matrix.hadamard a' b' - Matrix.hadamard a b).PosSemidef := sorry

/-- **111V** (`hilb-tensor-functor`, proc.tex:2436, Proposition): for
bounded linear maps `A : ℋ → ℋ'` and `B : 𝒦 → 𝒦'` there is a unique
bounded linear map `A ⊗ B : ℋ ⊗ 𝒦 → ℋ' ⊗ 𝒦'` with
`(A ⊗ B)(x ⊗ y) = Ax ⊗ By`. -/
theorem exists_opTensor (f : H →L[ℂ] H') (g : K →L[ℂ] K') :
    ∃! T : HT H K →L[ℂ] HT H' K',
      ∀ (x : H) (y : K), T (x ⊗ₕ y) = f x ⊗ₕ g y := sorry

/-- The operator `A ⊗ B : ℋ ⊗ 𝒦 → ℋ' ⊗ 𝒦'` of 111V. -/
noncomputable def opTensor (f : H →L[ℂ] H') (g : K →L[ℂ] K') :
    HT H K →L[ℂ] HT H' K' := (exists_opTensor f g).choose

theorem opTensor_apply (f : H →L[ℂ] H') (g : K →L[ℂ] K') (x : H) (y : K) :
    opTensor f g (x ⊗ₕ y) = f x ⊗ₕ g y :=
  (exists_opTensor f g).choose_spec.1 x y

end Hilbert

/-! ## Von Neumann subalgebras as bundled algebras (for the spatial
tensor product) -/

variable (A) in
/-- Wrapper: a von Neumann subalgebra `S ⊆ A` bundled as an algebra in its
own right, with sorry-ed instances (cf. `Corner` in `Measurement.lean`). -/
structure VNSub (S : StarSubalgebra ℂ A) : Type u where
  val : A
  property : val ∈ S

noncomputable instance (S : StarSubalgebra ℂ A) : CStarAlgebra (VNSub A S) :=
  sorry

noncomputable instance (S : StarSubalgebra ℂ A) : PartialOrder (VNSub A S) :=
  sorry

instance (S : StarSubalgebra ℂ A) : StarOrderedRing (VNSub A S) := sorry

instance (S : StarSubalgebra ℂ A) [VonNeumannAlgebra A] :
    VonNeumannAlgebra (VNSub A S) := sorry

section Spatial

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **111VII** (`special-tensor`, proc.tex:2491, Theorem): for von Neumann
algebras `𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)` of operators, the map
`(A, B) ↦ A ⊗ B : 𝒜 × ℬ → B(ℋ ⊗ 𝒦)` is miu-bilinear, and its restriction
to the von Neumann subalgebra `𝒯 ⊆ B(ℋ ⊗ 𝒦)` generated by its range is a
tensor product of `𝒜` and `ℬ`. -/
theorem special_tensor (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (hSA : IsVNSubalgebra (H →L[ℂ] H) SA)
    (hSB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    ∃ γ : VNSub (H →L[ℂ] H) SA →ₗ[ℂ] VNSub (K →L[ℂ] K) SB →ₗ[ℂ]
        VNSub (HT H K →L[ℂ] HT H K)
          (wstar (HT H K →L[ℂ] HT H K)
            {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}),
      (∀ a b, (γ a b).val = opTensor a.val b.val) ∧ IsTensorProduct γ :=
  sorry

end Spatial

/-- **111XII** (proc.tex:2583, Exercise): every pair of (abstract) von
Neumann algebras has a tensor product (via the normal Gelfand–Naimark
representation, vn.tex 48VIII, and 111VII). -/
theorem vnTensorProduct_exists [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    ∃ (T : Type u) (_ : CStarAlgebra T) (_ : PartialOrder T)
      (_ : StarOrderedRing T) (_ : VonNeumannAlgebra T)
      (γ : A →ₗ[ℂ] B →ₗ[ℂ] T), IsTensorProduct γ := sorry

/-! ## Parsec 1120: the algebraic tensor product `𝒜 ⊙ ℬ` and the
universal property -/

/-- Helper: the linear functional `f ⊙ g` on the algebraic tensor product
with `(f ⊙ g)(a ⊗ b) = f(a)·g(b)` (parsec 1120 intro, proc.tex:2594). -/
noncomputable def odotF (f : A →ₗ[ℂ] ℂ) (g : B →ₗ[ℂ] ℂ) :
    A ⊗[ℂ] B →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f g)

/-- Helper: the underlying linear functional of an np-functional. -/
def npLin (σ : NPFunctional A) : A →ₗ[ℂ] ℂ :=
  σ.toPositiveLinearMap.toLinearMap

/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 1: a
**basic functional** on `𝒜 ⊙ ℬ` is one of the form
`(σ ⊙ τ)(t* (·) t)` for np-functionals `σ`, `τ` and `t ∈ 𝒜 ⊙ ℬ`. -/
def IsBasicFunctional [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) : Prop :=
  ∃ (σ : NPFunctional A) (τ : NPFunctional B) (t : A ⊗[ℂ] B),
    ∀ s : A ⊗[ℂ] B, ω s = odotF (npLin σ) (npLin τ) (star t * s * t)

/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 1: a
**simple functional** on `𝒜 ⊙ ℬ` is a finite sum of basic functionals. -/
def IsSimpleFunctional [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) : Prop :=
  ∃ (n : ℕ) (ωs : Fin n → (A ⊗[ℂ] B →ₗ[ℂ] ℂ)),
    (∀ i, IsBasicFunctional (ωs i)) ∧ ω = ∑ i, ωs i

variable (A B) in
/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 2: the
**tensor product norm** on `𝒜 ⊙ ℬ`:
`‖t‖ = sup_ω ‖t‖_ω = sup_ω ω(t*t)^½` over the basic functionals `ω` with
`ω(1) ≤ 1`. -/
noncomputable def tensorNorm [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (t : A ⊗[ℂ] B) : ℝ :=
  sSup {r : ℝ | ∃ ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ, IsBasicFunctional ω ∧
    (ω 1).re ≤ 1 ∧ r = Real.sqrt (ω (star t * t)).re}

variable (A B) in
/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 3: a
functional on `𝒜 ⊙ ℬ` is an **operator norm limit of simple
functionals** when it can be approximated by simple functionals uniformly
with respect to the tensor product norm. -/
def NormLimitOfSimple [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : A ⊗[ℂ] B →ₗ[ℂ] ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ g : A ⊗[ℂ] B →ₗ[ℂ] ℂ, IsSimpleFunctional g ∧
    ∀ t : A ⊗[ℂ] B, ‖f t - g t‖ ≤ ε * tensorNorm A B t

set_option warn.classDefReducibility false in
variable (A B) in
/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 3: the
**ultraweak tensor product topology** on `𝒜 ⊙ ℬ` — the least topology
making all operator norm limits of simple functionals continuous. -/
noncomputable def uwTensorTopology [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] : TopologicalSpace (A ⊗[ℂ] B) :=
  ⨅ f : {f : A ⊗[ℂ] B →ₗ[ℂ] ℂ // NormLimitOfSimple A B f},
    TopologicalSpace.induced (fun t => f.1 t) inferInstance

/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 4a: a
bilinear map `β : 𝒜 × ℬ → 𝒞` between von Neumann algebras is **bounded**
when its extension `β_⊙ : 𝒜 ⊙ ℬ → 𝒞` is bounded with respect to the
tensor product norm. -/
def BilinBounded [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (β : A →ₗ[ℂ] B →ₗ[ℂ] C) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t : A ⊗[ℂ] B,
    ‖TensorProduct.lift β t‖ ≤ M * tensorNorm A B t

/-- **112II** (`tensor-extra`, proc.tex:2681, Definitions), part 4b: a
bilinear map is **normal** when `β_⊙` is continuous from the ultraweak
tensor product topology to the ultraweak topology on `𝒞`. -/
def BilinNormal [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    [VonNeumannAlgebra C] (β : A →ₗ[ℂ] B →ₗ[ℂ] C) : Prop :=
  @Continuous _ _ (uwTensorTopology A B) (ultraweak C)
    ⇑(TensorProduct.lift β)

/-- **112III** (`product-state-positive`, proc.tex:2781, Lemma): for
C*-algebras and positive functionals `σ`, `τ`,
`(σ ⊙ τ)(t* t) ≥ 0` for all `t ∈ 𝒜 ⊙ ℬ`. -/
theorem product_state_positive (σ : A →ₚ[ℂ] ℂ) (τ : B →ₚ[ℂ] ℂ)
    (t : A ⊗[ℂ] B) :
    0 ≤ odotF σ.toLinearMap τ.toLinearMap (star t * t) := sorry

/-- **112V** (`basic-state-inner-product`, proc.tex:2808, Exercise): for a
basic functional `ω`, `[s,t]_ω = ω(s* t)` is an inner product (a
positive-semidefinite sesquilinear form): it is conjugate-symmetric and
positive. -/
theorem basic_state_inner_product [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ)
    (hω : IsBasicFunctional ω) :
    (∀ s t : A ⊗[ℂ] B, ω (star t * s) = starRingEnd ℂ (ω (star s * t))) ∧
      ∀ t : A ⊗[ℂ] B, 0 ≤ ω (star t * t) := sorry

/-- **112VI** (proc.tex:2815, Lemma): product functionals formed from
separating collections `Ω`, `Ξ` of linear functionals on C*-algebras are
separating: if `(σ ⊙ τ)(t) = 0` for all `σ ∈ Ω`, `τ ∈ Ξ`, then
`t = 0`. -/
theorem product_functionals_separating (Ω : Set (A →ₗ[ℂ] ℂ))
    (Ξ : Set (B →ₗ[ℂ] ℂ))
    (hΩ : ∀ a : A, (∀ σ ∈ Ω, σ a = 0) → a = 0)
    (hΞ : ∀ b : B, (∀ τ ∈ Ξ, τ b = 0) → b = 0) (t : A ⊗[ℂ] B)
    (h : ∀ σ ∈ Ω, ∀ τ ∈ Ξ, odotF σ τ t = 0) : t = 0 := sorry

/-- **112VIII** (`tensor-product-norm`, proc.tex:2849, Exercise): the
tensor product norm is a norm on `𝒜 ⊙ ℬ`. -/
theorem tensor_product_norm [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    (∀ t : A ⊗[ℂ] B, 0 ≤ tensorNorm A B t) ∧
      (∀ t : A ⊗[ℂ] B, tensorNorm A B t = 0 ↔ t = 0) ∧
      (∀ (z : ℂ) (t : A ⊗[ℂ] B),
        tensorNorm A B (z • t) = ‖z‖ * tensorNorm A B t) ∧
      ∀ s t : A ⊗[ℂ] B,
        tensorNorm A B (s + t) ≤ tensorNorm A B s + tensorNorm A B t :=
  sorry

/-- **112IX** (`product-functional`, proc.tex:2854, Exercise): for bounded
ultraweakly continuous functionals `f ∈ 𝒜_*` and `g ∈ ℬ_*` the
functional `f ⊙ g` is bounded (w.r.t. the tensor norm) and continuous
w.r.t. the ultraweak tensor product topology. -/
theorem product_functional [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : A →ₗ[ℂ] ℂ) (g : B →ₗ[ℂ] ℂ)
    (hfb : ∃ M : ℝ, ∀ a, ‖f a‖ ≤ M * ‖a‖)
    (hgb : ∃ M : ℝ, ∀ b, ‖g b‖ ≤ M * ‖b‖)
    (hfc : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hgc : @Continuous B ℂ (ultraweak B) _ ⇑g) :
    (∃ M : ℝ, ∀ t : A ⊗[ℂ] B, ‖odotF f g t‖ ≤ M * tensorNorm A B t) ∧
      @Continuous _ ℂ (uwTensorTopology A B) _ ⇑(odotF f g) := sorry

section TensorBasic

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [VonNeumannAlgebra T]

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 1 (headline
claims): for a tensor product `γ` the np-functionals of the form
`γ(σ,τ)(γ_⊙(s)* (·) γ_⊙(s))` are order separating, and every
np-functional on `𝒯` is an operator-norm limit of finite sums of such;
their restrictions along `γ_⊙` are exactly the basic functionals. -/
theorem tensor_basic_1 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ) :
    (∀ x y : T, IsSelfAdjoint x → IsSelfAdjoint y →
      (∀ (σ : NPFunctional A) (τ : NPFunctional B) (s : A ⊗[ℂ] B),
        (prodNP hγ σ τ (star (TensorProduct.lift γ s) * x *
            TensorProduct.lift γ s)).re ≤
          (prodNP hγ σ τ (star (TensorProduct.lift γ s) * y *
            TensorProduct.lift γ s)).re) → x ≤ y) ∧
    ∀ (h : NPFunctional T), ∀ ε > (0 : ℝ),
      ∃ (n : ℕ) (σ : Fin n → NPFunctional A) (τ : Fin n → NPFunctional B)
        (s : Fin n → A ⊗[ℂ] B),
        ∀ t : T,
          ‖h t - ∑ i, prodNP hγ (σ i) (τ i)
            (star (TensorProduct.lift γ (s i)) * t *
              TensorProduct.lift γ (s i))‖ ≤ ε * ‖t‖ := sorry

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 2 (headline
claim): `γ_⊙ : 𝒜 ⊙ ℬ → 𝒯` is an isometry for the tensor product
norm. -/
theorem tensor_basic_2 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ)
    (s : A ⊗[ℂ] B) : ‖TensorProduct.lift γ s‖ = tensorNorm A B s := sorry

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 3 (headline
claim): `γ_⊙` is continuous from the ultraweak tensor product topology to
the ultraweak topology on `𝒯` (and the restriction of an np-functional
along `γ_⊙` is an operator norm limit of simple functionals). -/
theorem tensor_basic_3 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ) :
    (@Continuous _ _ (uwTensorTopology A B) (ultraweak T)
        ⇑(TensorProduct.lift γ)) ∧
      ∀ h : NPFunctional T,
        NormLimitOfSimple A B
          ((npLin h).comp (TensorProduct.lift γ)) := sorry

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 4:
`‖f ∘ γ_⊙‖ = ‖f‖` for every `f ∈ 𝒯_*` — rendered in bound form: `f` and
`f ∘ γ_⊙` have the same bounds. -/
theorem tensor_basic_4 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ)
    (f : T →L[ℂ] ℂ) (hf : @Continuous T ℂ (ultraweak T) _ ⇑f) (M : ℝ)
    (hM : 0 ≤ M) :
    (∀ t : A ⊗[ℂ] B,
        ‖f (TensorProduct.lift γ t)‖ ≤ M * tensorNorm A B t) ↔
      ∀ x : T, ‖f x‖ ≤ M * ‖x‖ := sorry

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 5: every
operator norm limit of simple functionals extends uniquely along `γ_⊙` to
an np-functional on `𝒯`; consequently `γ_⊙` is an ultraweak topological
embedding. -/
theorem tensor_basic_5 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ) :
    (∀ ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ, NormLimitOfSimple A B ω' →
      ∃! ω : NPFunctional T,
        ∀ s : A ⊗[ℂ] B, ω (TensorProduct.lift γ s) = ω' s) ∧
    uwTensorTopology A B =
      TopologicalSpace.induced ⇑(TensorProduct.lift γ) (ultraweak T) :=
  sorry

/-- **112XI** (`tensor-universal-property`, proc.tex:2980, Theorem): a
tensor product `γ : 𝒜 × ℬ → 𝒯` has the universal property that every
normal bounded bilinear map `β : 𝒜 × ℬ → 𝒞` extends uniquely to an
ultraweakly continuous linear map `β_γ : 𝒯 → 𝒞` with `β_γ ∘ γ = β`;
moreover `β_γ` and `β_⊙` have the same bounds. -/
theorem tensor_universal_property (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hγ : IsTensorProduct γ) (β : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (hn : BilinNormal β) (hb : BilinBounded β) :
    (∃! g : T →ₗ[ℂ] C,
      @Continuous T C (ultraweak T) (ultraweak C) ⇑g ∧
        ∀ (a : A) (b : B), g (γ a b) = β a b) ∧
    ∀ g : T →ₗ[ℂ] C,
      @Continuous T C (ultraweak T) (ultraweak C) ⇑g →
      (∀ (a : A) (b : B), g (γ a b) = β a b) →
      ∀ M : ℝ, 0 ≤ M →
        ((∀ t, ‖TensorProduct.lift β t‖ ≤ M * tensorNorm A B t) ↔
          ∀ x : T, ‖g x‖ ≤ M * ‖x‖) := sorry

end TensorBasic

/-! ## Parsec 1130: completely positive bilinear maps -/

/-- **113II** (proc.tex:3012, Exercise): an mi-bilinear map between von
Neumann algebras is completely positive. -/
theorem mi_bilinear_cp (β : A →ₗ[ℂ] B →ₗ[ℂ] C) (hm : BilinMult β)
    (hi : BilinStar β) : BilinCP β := sorry

/-- **113III** (proc.tex:3018, Notation): the entrywise bilinear map
`M_N β : M_N(𝒜) × M_N(ℬ) → M_N(𝒞)`,
`(M_N β)(A, B)ᵢⱼ = β(Aᵢⱼ, Bᵢⱼ)` (as a plain function). -/
def matBilin (β : A →ₗ[ℂ] B →ₗ[ℂ] C) (N : ℕ)
    (M : CStarMatrix (Fin N) (Fin N) A)
    (M' : CStarMatrix (Fin N) (Fin N) B) :
    CStarMatrix (Fin N) (Fin N) C :=
  CStarMatrix.ofMatrix (Matrix.of fun i j => β (M i j) (M' i j))

/-- **113IV** (`cp-bilinear`, proc.tex:3029, Exercise), parts 1 and 3: a
bilinear map `β` is completely positive iff `(M_N β)(A,B) ≥ 0` for all
positive `A ∈ M_N(𝒜)`, `B ∈ M_N(ℬ)` and all `N` (positivity of matrices
rendered by the criterion of cstar.tex 33II).  (Part 2, complete
positivity of `M_N β` itself, is subsumed by applying the statement to
`M_N β`.) -/
theorem cp_bilinear (β : A →ₗ[ℂ] B →ₗ[ℂ] C) :
    BilinCP β ↔
      ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) A)
        (M' : CStarMatrix (Fin N) (Fin N) B),
        (∀ a : Fin N → A, 0 ≤ ∑ i, ∑ j, star (a i) * M i j * a j) →
        (∀ b : Fin N → B, 0 ≤ ∑ i, ∑ j, star (b i) * M' i j * b j) →
        ∀ c : Fin N → C,
          0 ≤ ∑ i, ∑ j, star (c i) * matBilin β N M M' i j * c j := sorry

/-- **113IV** (`cp-bilinear`, proc.tex:3029, Exercise), corollary:
`h ∘ β ∘ (f × g)` is completely positive when `f`, `g`, `h` are cp-maps
between von Neumann algebras. -/
theorem cp_bilinear_comp {A' B' C' : Type u} [CStarAlgebra A']
    [PartialOrder A'] [StarOrderedRing A'] [CStarAlgebra B']
    [PartialOrder B'] [StarOrderedRing B'] [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (β : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (hβ : BilinCP β) (f : A' →ₗ[ℂ] A) (g : B' →ₗ[ℂ] B) (h : C →ₗ[ℂ] C')
    (hf : Theses.A.CStar.IsCompletelyPositiveMap f)
    (hg : Theses.A.CStar.IsCompletelyPositiveMap g)
    (hh : Theses.A.CStar.IsCompletelyPositiveMap h)
    (β' : A' →ₗ[ℂ] B' →ₗ[ℂ] C')
    (hβ' : ∀ a b, β' a b = h (β (f a) (g b))) : BilinCP β' := sorry

/-! ## Parsec 1140: extra universal properties and uniqueness -/

section Extra

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [VonNeumannAlgebra T]

/-- **114I** (`tensor-universal-property-extra`, proc.tex:3053, Exercise):
for a tensor product `γ` and a normal bounded bilinear `β` with extension
`β_γ` (any uw-continuous `g` with `g ∘ γ = β`): (1) `β_γ` is
multiplicative iff `β` is; (2) involution preserving iff `β` is;
(3) unital iff `β` is; (4) positive iff `∑ᵢⱼ β(aᵢ*aⱼ, bᵢ*bⱼ) ≥ 0`;
(5) completely positive iff `β` is. -/
theorem tensor_universal_property_extra (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hγ : IsTensorProduct γ) (β : A →ₗ[ℂ] B →ₗ[ℂ] C) (hn : BilinNormal β)
    (hb : BilinBounded β) (g : T →ₗ[ℂ] C)
    (hgc : @Continuous T C (ultraweak T) (ultraweak C) ⇑g)
    (hg : ∀ (a : A) (b : B), g (γ a b) = β a b) :
    (Theses.A.CStar.IsMultiplicativeMap g ↔ BilinMult β) ∧
      (Theses.A.CStar.IsInvolutionPreserving g ↔ BilinStar β) ∧
      (g 1 = 1 ↔ BilinUnital β) ∧
      (Theses.A.CStar.IsPositiveMap g ↔
        ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B),
          0 ≤ ∑ i, ∑ j, β (star (a i) * a j) (star (b i) * b j)) ∧
      (Theses.A.CStar.IsCompletelyPositiveMap g ↔ BilinCP β) := sorry

/-- **114II** (`tensor-uniqueness`, proc.tex:3087, Exercise): the tensor
product of von Neumann algebras is unique: for tensor products
`γ : 𝒜 × ℬ → 𝒯` and `γ' : 𝒜 × ℬ → 𝒯'` there is a unique
nmiu-isomorphism `φ : 𝒯 → 𝒯'` with `φ(γ(a,b)) = γ'(a,b)`. -/
theorem tensor_uniqueness {T' : Type u} [CStarAlgebra T'] [PartialOrder T']
    [StarOrderedRing T'] [VonNeumannAlgebra T'] (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (γ' : A →ₗ[ℂ] B →ₗ[ℂ] T') (hγ : IsTensorProduct γ)
    (hγ' : IsTensorProduct γ') :
    ∃ φ : NMIUMap T T', (∀ a b, φ (γ a b) = γ' a b) ∧
      Function.Bijective ⇑φ ∧
      ∀ ψ : NMIUMap T T', (∀ a b, ψ (γ a b) = γ' a b) → ψ = φ := sorry

end Extra

/-! ## Parsec 1150: the chosen tensor product and functoriality -/

section ChosenCore

variable (𝒜 : Type u) (ℬ : Type v)
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [VonNeumannAlgebra ℬ]

/-- **115I** (proc.tex:3103, Notation), bundled: a chosen tensor product of
the von Neumann algebras `𝒜` and `ℬ`. -/
structure VNTensorProduct : Type (max u v + 1) where
  carrier : Type (max u v)
  [cstar : CStarAlgebra carrier]
  [po : PartialOrder carrier]
  [sor : StarOrderedRing carrier]
  [vna : VonNeumannAlgebra carrier]
  map : 𝒜 →ₗ[ℂ] ℬ →ₗ[ℂ] carrier
  isTensorProduct : IsTensorProduct map

attribute [instance] VNTensorProduct.cstar VNTensorProduct.po
  VNTensorProduct.sor VNTensorProduct.vna

/-- **111XII** (proc.tex:2583, Exercise), bundled form: a tensor product
of `𝒜` and `ℬ` exists. -/
theorem vnTensorProduct_nonempty : Nonempty (VNTensorProduct 𝒜 ℬ) := sorry

/-- **115I** (proc.tex:3103, Notation): we pick one tensor product
`⊗ : 𝒜 × ℬ → 𝒜 ⊗ ℬ` of von Neumann algebras. -/
noncomputable def vnTensor : VNTensorProduct 𝒜 ℬ :=
  (vnTensorProduct_nonempty 𝒜 ℬ).some

/-- **115I** (proc.tex:3103, Notation): the carrier `𝒜 ⊗ ℬ` of the chosen
tensor product. -/
abbrev VNT : Type (max u v) := (vnTensor 𝒜 ℬ).carrier

variable {𝒜 ℬ}

/-- The elementary tensor `a ⊗ b ∈ 𝒜 ⊗ ℬ` (115I). -/
noncomputable def vtmul (a : 𝒜) (b : ℬ) : VNT 𝒜 ℬ := (vnTensor 𝒜 ℬ).map a b

@[inherit_doc] scoped infixr:70 " ⊗ᵥ " => vtmul

end ChosenCore

section Chosen

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
  [VonNeumannAlgebra D]

/-- **115II** (`tensor-functorial`, proc.tex:3114, Proposition),
well-definedness: for ncp-maps `f : 𝒜 → 𝒞` and `g : ℬ → 𝒟` there is a
unique ncp-map `f ⊗ g : 𝒜 ⊗ ℬ → 𝒞 ⊗ 𝒟` with
`(f ⊗ g)(a ⊗ b) = f(a) ⊗ g(b)`. -/
theorem exists_tmap (f : NCPMap A C) (g : NCPMap B D) :
    ∃! h : NCPMap (VNT A B) (VNT C D),
      ∀ (a : A) (b : B), h (a ⊗ᵥ b) = f a ⊗ᵥ g b := sorry

/-- The ncp-map `f ⊗ g : 𝒜 ⊗ ℬ → 𝒞 ⊗ 𝒟` of 115II. -/
noncomputable def tmap (f : NCPMap A C) (g : NCPMap B D) :
    NCPMap (VNT A B) (VNT C D) := (exists_tmap f g).choose

theorem tmap_apply (f : NCPMap A C) (g : NCPMap B D) (a : A) (b : B) :
    tmap f g (a ⊗ᵥ b) = f a ⊗ᵥ g b := (exists_tmap f g).choose_spec.1 a b

/-- **115II** (`tensor-functorial`, proc.tex:3114, Proposition), parts
1–3: `f ⊗ g` is multiplicative when `f` and `g` are, involution
preserving when `f` and `g` are, and (sub)unital when `f` and `g` are. -/
theorem tensor_functorial (f : NCPMap A C) (g : NCPMap B D) :
    ((∀ a a', f (a * a') = f a * f a') →
      (∀ b b', g (b * b') = g b * g b') →
      ∀ x y, tmap f g (x * y) = tmap f g x * tmap f g y) ∧
    ((∀ a, f (star a) = star (f a)) → (∀ b, g (star b) = star (g b)) →
      ∀ x, tmap f g (star x) = star (tmap f g x)) ∧
    (f 1 = 1 → g 1 = 1 → tmap f g 1 = 1) ∧
    (f 1 ≤ 1 → g 1 ≤ 1 → tmap f g 1 ≤ 1) := sorry

/-- **115IV** (`tensor-functor`, proc.tex:3275, Exercise), identity law:
the assignments `(𝒜,ℬ) ↦ 𝒜 ⊗ ℬ`, `(f,g) ↦ f ⊗ g` give a bifunctor on
`W*_miu`, `W*_cp`, `W*_cpu` and `W*_cpsu` — rendered concretely:
`id ⊗ id = id`. -/
theorem tensor_functor_id : tmap (ncpId A) (ncpId B) = ncpId (VNT A B) :=
  sorry

/-- **115IV** (`tensor-functor`, proc.tex:3275, Exercise), composition
law: `(f' ∘ f) ⊗ (g' ∘ g) = (f' ⊗ g') ∘ (f ⊗ g)`. -/
theorem tensor_functor_comp {A' B' : Type u} [CStarAlgebra A']
    [PartialOrder A'] [StarOrderedRing A'] [VonNeumannAlgebra A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [VonNeumannAlgebra B'] (f : NCPMap A C) (f' : NCPMap C A')
    (g : NCPMap B D) (g' : NCPMap D B') :
    tmap (ncpComp f' f) (ncpComp g' g) =
      ncpComp (tmap f' g') (tmap f g) := sorry

/-- **115V** (`tensor-injective`, proc.tex:3288, Proposition): given
injective nmiu-maps `f : 𝒜 → 𝒞`, `g : ℬ → 𝒟`, the map
`f ⊗ g : 𝒜 ⊗ ℬ → 𝒞 ⊗ 𝒟` is injective (rendered for any ncp-map
agreeing with `f ⊗ g` on pure tensors). -/
theorem tensor_injective (f : NMIUMap A C) (g : NMIUMap B D)
    (hf : Function.Injective ⇑f) (hg : Function.Injective ⇑g)
    (h : NCPMap (VNT A B) (VNT C D))
    (hh : ∀ (a : A) (b : B), h (a ⊗ᵥ b) = f a ⊗ᵥ g b) :
    Function.Injective ⇑h := sorry

/-! ## Parsec 1160: miscellaneous properties -/

/-- **116I** (`product-functional-norm`, proc.tex:3403, Lemma),
well-definedness (from 112IX and 112XI): bounded ultraweakly continuous
functionals `f ∈ 𝒜_*`, `g ∈ ℬ_*` induce a unique normal functional
`f ⊗ g` on `𝒜 ⊗ ℬ`. -/
theorem exists_predualTensor (f : A →L[ℂ] ℂ) (g : B →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hg : @Continuous B ℂ (ultraweak B) _ ⇑g) :
    ∃! h : VNT A B →L[ℂ] ℂ,
      @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑h ∧
        ∀ (a : A) (b : B), h (a ⊗ᵥ b) = f a * g b := sorry

/-- The product functional `f ⊗ g ∈ (𝒜 ⊗ ℬ)_*` (116I). -/
noncomputable def predualTensor (f : A →L[ℂ] ℂ) (g : B →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hg : @Continuous B ℂ (ultraweak B) _ ⇑g) : VNT A B →L[ℂ] ℂ :=
  (exists_predualTensor f g hf hg).choose

/-- **116I** (`product-functional-norm`, proc.tex:3403, Lemma):
`‖f ⊗ g‖ = ‖f‖·‖g‖` for `f ∈ 𝒜_*`, `g ∈ ℬ_*`. -/
theorem product_functional_norm (f : A →L[ℂ] ℂ) (g : B →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hg : @Continuous B ℂ (ultraweak B) _ ⇑g) :
    ‖predualTensor f g hf hg‖ = ‖f‖ * ‖g‖ := sorry

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 1:
`a ⊗ b ≥ 0` for positive `a`, `b`; hence `a₁ ⊗ b₁ ≤ a₂ ⊗ b₂` for
`0 ≤ a₁ ≤ a₂` and `0 ≤ b₁ ≤ b₂`. -/
theorem tensor_simple_facts_1 (a : A) (b : B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a ⊗ᵥ b ∧
      ∀ (a₂ : A) (b₂ : B), a ≤ a₂ → b ≤ b₂ → a ⊗ᵥ b ≤ a₂ ⊗ᵥ b₂ := sorry

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 2:
`‖a ⊗ b‖ = ‖a‖·‖b‖`, and `⊗ : 𝒜 × ℬ → 𝒜 ⊗ ℬ` is norm continuous. -/
theorem tensor_simple_facts_2 :
    (∀ (a : A) (b : B), ‖a ⊗ᵥ b‖ = ‖a‖ * ‖b‖) ∧
      Continuous fun p : A × B => p.1 ⊗ᵥ p.2 := sorry

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 3:
`⊗ : 𝒜_* × ℬ_* → (𝒜 ⊗ ℬ)_*` is norm continuous — rendered by the
estimate `‖f ⊗ g − f' ⊗ g'‖ ≤ ‖f − f'‖·‖g‖ + ‖f'‖·‖g − g'‖`. -/
theorem tensor_simple_facts_3 (f f' : A →L[ℂ] ℂ) (g g' : B →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hf' : @Continuous A ℂ (ultraweak A) _ ⇑f')
    (hg : @Continuous B ℂ (ultraweak B) _ ⇑g)
    (hg' : @Continuous B ℂ (ultraweak B) _ ⇑g') :
    ‖predualTensor f g hf hg - predualTensor f' g' hf' hg'‖ ≤
      ‖f - f'‖ * ‖g‖ + ‖f'‖ * ‖g - g'‖ := sorry

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 4:
`⊗ : 𝒜 × ℬ → 𝒜 ⊗ ℬ` is (jointly) ultraweakly continuous. -/
theorem tensor_simple_facts_4 :
    @Continuous (A × B) (VNT A B)
      (@instTopologicalSpaceProd A B (ultraweak A) (ultraweak B))
      (ultraweak (VNT A B)) (fun p => p.1 ⊗ᵥ p.2) := sorry

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 5:
`a ⊗ (·) : ℬ → 𝒜 ⊗ ℬ` is an ncp-map for positive `a`, and `1 ⊗ (·)` is
an nmiu-map. -/
theorem tensor_simple_facts_5 (a : A) (ha : 0 ≤ a) :
    (∃ f : NCPMap B (VNT A B), ∀ b, f b = a ⊗ᵥ b) ∧
      ∃ ρ : NMIUMap B (VNT A B), ∀ b, ρ b = (1 : A) ⊗ᵥ b := sorry

/-- **116IV** (`tensor-generation`, proc.tex:3489, Proposition), part 1:
if the linear spans of `S ⊆ 𝒜` and `T ⊆ ℬ` are ultraweakly dense, then
the linear span of `{s ⊗ t}` is ultraweakly dense in `𝒜 ⊗ ℬ`. -/
theorem tensor_generation_1 (S : Set A) (T : Set B)
    (hS : @Dense A (ultraweak A) (Submodule.span ℂ S : Set A))
    (hT : @Dense B (ultraweak B) (Submodule.span ℂ T : Set B)) :
    @Dense (VNT A B) (ultraweak (VNT A B))
      (Submodule.span ℂ {x : VNT A B | ∃ s ∈ S, ∃ t ∈ T, x = s ⊗ᵥ t} :
        Set (VNT A B)) := sorry

/-- **116IV** (`tensor-generation`, proc.tex:3489, Proposition), part 2:
centre separating collections `Ω`, `Θ` of np-functionals on `𝒜`, `ℬ`
yield a centre separating collection `{ω ⊗ θ}` on `𝒜 ⊗ ℬ`. -/
theorem tensor_generation_2 (Ω : Set (NPFunctional A))
    (Θ : Set (NPFunctional B)) (hΩ : CentreSeparating A Ω)
    (hΘ : CentreSeparating B Θ) :
    CentreSeparating (VNT A B)
      {χ : NPFunctional (VNT A B) | ∃ ω ∈ Ω, ∃ θ ∈ Θ,
        ∀ (a : A) (b : B), χ (a ⊗ᵥ b) = ω a * θ b} := sorry

end Chosen

/-- **116VII** (`tensor-characterization`, proc.tex:3578, Theorem): given
centre separating collections `Σ`, `Γ` of np-functionals on `𝒜`, `ℬ`, an
miu-bilinear map `γ : 𝒜 × ℬ → 𝒯` is a tensor product iff (1) the span of
its range is ultraweakly dense, (2) for `σ ∈ Σ`, `τ ∈ Γ` the product
functional exists and is positive, and (3) those product functionals are
centre separating. -/
theorem tensor_characterization [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
    [VonNeumannAlgebra T] (Sg : Set (NPFunctional A))
    (Γ : Set (NPFunctional B)) (hSg : CentreSeparating A Sg)
    (hΓ : CentreSeparating B Γ) (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hmiu : MIUBilinear γ) :
    IsTensorProduct γ ↔
      (@Dense T (ultraweak T)
          (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T)) ∧
        (∀ σ ∈ Sg, ∀ τ ∈ Γ, ∃ h : NPFunctional T,
          ∀ (a : A) (b : B), h (γ a b) = σ a * τ b) ∧
        CentreSeparating T
          {h : NPFunctional T | ∃ σ ∈ Sg, ∃ τ ∈ Γ,
            ∀ (a : A) (b : B), h (γ a b) = σ a * τ b} := sorry

/-! ## Parsec 1170: distribution over direct sums -/

section Sums

variable {I : Type u} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]

/-- **117II** (`sum-generation`, proc.tex:3733, Exercise), part 1: if
`Aᵢ ⊆ 𝒜ᵢ` generates `𝒜ᵢ` for each `i`, then `⋃ᵢ κᵢ(Aᵢ)` generates the
direct sum `⊕ᵢ 𝒜ᵢ`. -/
theorem sum_generation_1 [DecidableEq I] (S : ∀ i, Set (𝒜 i))
    (hS : ∀ i, wstar (𝒜 i) (S i) = ⊤) :
    wstar (lp 𝒜 ∞)
      {x : lp 𝒜 ∞ | ∃ i, ∃ a ∈ S i, x = lp.single ∞ i a} = ⊤ := sorry

/-- **117II** (`sum-generation`, proc.tex:3733, Exercise), part 2: centre
separating collections `Ωᵢ` on the `𝒜ᵢ` give the centre separating
collection `{ω ∘ πᵢ}` on `⊕ᵢ 𝒜ᵢ`. -/
theorem sum_generation_2 (Ω : ∀ i, Set (NPFunctional (𝒜 i)))
    (hΩ : ∀ i, CentreSeparating (𝒜 i) (Ω i)) :
    CentreSeparating (lp 𝒜 ∞)
      {χ : NPFunctional (lp 𝒜 ∞) | ∃ i, ∃ ω ∈ Ω i,
        ∀ x : lp 𝒜 ∞, χ x = ω (x i)} := sorry

variable [VonNeumannAlgebra A] [∀ i, Nontrivial (VNT A (𝒜 i))]

/-- **117III** (`tensor-distributes-over-sums`, proc.tex:3758,
Proposition): the bilinear map
`γ : 𝒜 × ⊕ᵢ ℬᵢ → ⊕ᵢ (𝒜 ⊗ ℬᵢ)`, `(a, b) ↦ (a ⊗ bᵢ)ᵢ` is a tensor
product; whence `𝒜 ⊗ ⊕ᵢ ℬᵢ ≅ ⊕ᵢ (𝒜 ⊗ ℬᵢ)`. -/
theorem tensor_distributes_over_sums :
    ∃ γ : A →ₗ[ℂ] lp 𝒜 ∞ →ₗ[ℂ] lp (fun i => VNT A (𝒜 i)) ∞,
      (∀ (a : A) (b : lp 𝒜 ∞) (i : I), (γ a b) i = a ⊗ᵥ b i) ∧
        IsTensorProduct γ := sorry

end Sums

/-! ## Parsec 1180: tensors of projections and carriers -/

section Carriers

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
  [VonNeumannAlgebra D]

/-- **118II** (proc.tex:3802, Lemma), part 1:
`⌈a ⊗ b⌉ = ⌈a⌉ ⊗ ⌈b⌉` for positive `a`, `b`. -/
theorem ceil_tensor (a : A) (b : B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ceil (a ⊗ᵥ b) = ceil a ⊗ᵥ ceil b := sorry

/-- **118II** (proc.tex:3802, Lemma), part 2:
`⌈⌈a ⊗ b⌉⌉ = ⌈⌈a⌉⌉ ⊗ ⌈⌈b⌉⌉` (central supports/carriers). -/
theorem cceil_tensor (a : A) (b : B) :
    cceil (a ⊗ᵥ b) = cceil a ⊗ᵥ cceil b := sorry

/-- **118IV** (`carrier-tensor`, proc.tex:3880, Exercise), part 1:
`⌈f ⊗ g⌉ ≤ ⌈f⌉ ⊗ ⌈g⌉` for np-maps `f`, `g`. -/
theorem carrier_tensor_1 (f : NCPMap A C) (g : NCPMap B D) :
    ncpCarrier (tmap f g) ≤ ncpCarrier f ⊗ᵥ ncpCarrier g := sorry

/-- **118IV** (`carrier-tensor`, proc.tex:3880, Exercise), part 4 (the
case of functionals): `⌈σ ⊗ τ⌉ = ⌈σ⌉ ⊗ ⌈τ⌉` for np-functionals `σ`,
`τ` — for any np-functional `χ` on `𝒜 ⊗ ℬ` restricting to the product.
(Parts 2–3, the Hilbert-space steps toward it, are proof-steps of the
guided exercise and are not converted separately.) -/
theorem carrier_tensor_4 (σ : NPFunctional A) (τ : NPFunctional B)
    (χ : NPFunctional (VNT A B))
    (hχ : ∀ (a : A) (b : B), χ (a ⊗ᵥ b) = σ a * τ b) :
    npCarrier χ = npCarrier σ ⊗ᵥ npCarrier τ := sorry

/-- **118IV** (`carrier-tensor`, proc.tex:3880, Exercise), part 5:
`⌈f ⊗ g⌉ = ⌈f⌉ ⊗ ⌈g⌉` for np-maps `f`, `g`. -/
theorem carrier_tensor_5 (f : NCPMap A C) (g : NCPMap B D) :
    ncpCarrier (tmap f g) = ncpCarrier f ⊗ᵥ ncpCarrier g := sorry

/-- **118IV** (`carrier-tensor`, proc.tex:3880, Exercise), part 6:
`(f ⊗ g)_⋄(s ⊗ t) = f_⋄(s) ⊗ g_⋄(t)` for projections `s ∈ 𝒞`,
`t ∈ 𝒟`. -/
theorem carrier_tensor_6 (f : NCPMap A C) (g : NCPMap B D) (s : C) (t : D)
    (hs : IsStarProjection s) (ht : IsStarProjection t) :
    diamondDown (tmap f g) (s ⊗ᵥ t) =
      diamondDown f s ⊗ᵥ diamondDown g t := sorry

end Carriers

/-! ## Parsec 1190: monoidal structure -/

section Monoidal

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
  [VonNeumannAlgebra D]

/-- **119II** (proc.tex:3994, Proposition), trilinear tensor products
(cf. 119I): a trilinear map `γ : 𝒜 × ℬ × 𝒞 → 𝒯` is a **tensor product**
when it is miu-trilinear, the span of its range is ultraweakly dense, the
product functionals of np-functionals exist and are positive, and they
form a faithful collection. -/
structure IsTensorProduct₃ {T : Type u} [CStarAlgebra T] [PartialOrder T]
    [StarOrderedRing T] [VonNeumannAlgebra T]
    (γ : A →ₗ[ℂ] B →ₗ[ℂ] C →ₗ[ℂ] T) : Prop where
  unital : γ 1 1 1 = 1
  mult : ∀ a a' b b' c c',
    γ (a * a') (b * b') (c * c') = γ a b c * γ a' b' c'
  star_map : ∀ a b c, star (γ a b c) = γ (star a) (star b) (star c)
  dense : @Dense T (ultraweak T)
    (Submodule.span ℂ {t : T | ∃ a b c, t = γ a b c} : Set T)
  prod_exists : ∀ (σ : NPFunctional A) (τ : NPFunctional B)
    (υ : NPFunctional C), ∃ h : NPFunctional T,
      ∀ a b c, h (γ a b c) = σ a * τ b * υ c
  faithful : ∀ t : T, 0 ≤ t →
    (∀ (σ : NPFunctional A) (τ : NPFunctional B) (υ : NPFunctional C)
      (h : NPFunctional T),
      (∀ a b c, h (γ a b c) = σ a * τ b * υ c) → h t = 0) → t = 0

/-- **119II** (proc.tex:3994, Proposition): the trilinear map
`(a,b,c) ↦ (a ⊗ b) ⊗ c : 𝒜 × ℬ × 𝒞 → (𝒜 ⊗ ℬ) ⊗ 𝒞` is a tensor
product. -/
theorem triple_tensor :
    ∃ γ : A →ₗ[ℂ] B →ₗ[ℂ] C →ₗ[ℂ] VNT (VNT A B) C,
      (∀ a b c, γ a b c = (a ⊗ᵥ b) ⊗ᵥ c) ∧ IsTensorProduct₃ γ := sorry

section AssocBraid

variable (𝒜 : Type u) (ℬ : Type v) (𝒞 : Type w)
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [VonNeumannAlgebra 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [VonNeumannAlgebra ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
  [VonNeumannAlgebra 𝒞]

/-- **119IV** (`associator`, proc.tex:4031, Corollary): there is a unique
nmiu-isomorphism `α : 𝒜 ⊗ (ℬ ⊗ 𝒞) → (𝒜 ⊗ ℬ) ⊗ 𝒞` with
`α(a ⊗ (b ⊗ c)) = (a ⊗ b) ⊗ c`. -/
theorem exists_associator :
    ∃ α : NMIUMap (VNT 𝒜 (VNT ℬ 𝒞)) (VNT (VNT 𝒜 ℬ) 𝒞),
      (∀ a b c, α (a ⊗ᵥ (b ⊗ᵥ c)) = (a ⊗ᵥ b) ⊗ᵥ c) ∧
      Function.Bijective ⇑α ∧
      ∀ α' : NMIUMap (VNT 𝒜 (VNT ℬ 𝒞)) (VNT (VNT 𝒜 ℬ) 𝒞),
        (∀ a b c, α' (a ⊗ᵥ (b ⊗ᵥ c)) = (a ⊗ᵥ b) ⊗ᵥ c) → α' = α := sorry

/-- The associator `α_{𝒜,ℬ,𝒞}` (119IV), by choice. -/
noncomputable def associator :
    NMIUMap (VNT 𝒜 (VNT ℬ 𝒞)) (VNT (VNT 𝒜 ℬ) 𝒞) :=
  (exists_associator 𝒜 ℬ 𝒞).choose

/-- **119IVc** (proc.tex:4072, Exercise): the bilinear map
`(a, b) ↦ b ⊗ a : 𝒜 × ℬ → ℬ ⊗ 𝒜` is a tensor product; hence there is a
unique nmiu-isomorphism (braiding) `γ_{𝒜,ℬ} : 𝒜 ⊗ ℬ → ℬ ⊗ 𝒜` with
`γ(a ⊗ b) = b ⊗ a`. -/
theorem exists_braiding :
    ∃ s : NMIUMap (VNT 𝒜 ℬ) (VNT ℬ 𝒜),
      (∀ (a : 𝒜) (b : ℬ), s (a ⊗ᵥ b) = b ⊗ᵥ a) ∧
      Function.Bijective ⇑s ∧
      ∀ s' : NMIUMap (VNT 𝒜 ℬ) (VNT ℬ 𝒜),
        (∀ (a : 𝒜) (b : ℬ), s' (a ⊗ᵥ b) = b ⊗ᵥ a) → s' = s := sorry

/-- The braiding `γ_{𝒜,ℬ} : 𝒜 ⊗ ℬ → ℬ ⊗ 𝒜` (119IVc), by choice. -/
noncomputable def braiding : NMIUMap (VNT 𝒜 ℬ) (VNT ℬ 𝒜) :=
  (exists_braiding 𝒜 ℬ).choose

end AssocBraid

/-- **119IVb** (proc.tex:4053, Exercise): the bilinear maps
`(z, a) ↦ z·a : ℂ × 𝒜 → 𝒜` and `(a, z) ↦ z·a : 𝒜 × ℂ → 𝒜` are tensor
products; hence there are unique nmiu-isomorphisms (unitors)
`λ_𝒜 : ℂ ⊗ 𝒜 → 𝒜` and `ρ_𝒜 : 𝒜 ⊗ ℂ → 𝒜` with `λ(z ⊗ a) = z·a = ρ(a ⊗ z)`. -/
theorem exists_unitors :
    IsTensorProduct (LinearMap.lsmul ℂ A) ∧
      IsTensorProduct (LinearMap.lsmul ℂ A).flip ∧
      (∃ l : NMIUMap (VNT ℂ A) A,
        (∀ (z : ℂ) (a : A), l (z ⊗ᵥ a) = z • a) ∧ Function.Bijective ⇑l ∧
        ∀ l' : NMIUMap (VNT ℂ A) A,
          (∀ (z : ℂ) (a : A), l' (z ⊗ᵥ a) = z • a) → l' = l) ∧
      ∃ r : NMIUMap (VNT A ℂ) A,
        (∀ (a : A) (z : ℂ), r (a ⊗ᵥ z) = z • a) ∧ Function.Bijective ⇑r ∧
        ∀ r' : NMIUMap (VNT A ℂ) A,
          (∀ (a : A) (z : ℂ), r' (a ⊗ᵥ z) = z • a) → r' = r := sorry

variable (A) in
/-- The left unitor `λ_𝒜 : ℂ ⊗ 𝒜 → 𝒜` (119IVb), by choice. -/
noncomputable def leftUnitor : NMIUMap (VNT ℂ A) A :=
  (exists_unitors (A := A)).2.2.1.choose

variable (A) in
/-- The right unitor `ρ_𝒜 : 𝒜 ⊗ ℂ → 𝒜` (119IVb), by choice. -/
noncomputable def rightUnitor : NMIUMap (VNT A ℂ) A :=
  (exists_unitors (A := A)).2.2.2.choose

section TmapM

universe u₁ u₂ u₃ u₄

variable {A₂ : Type u₁} {B₂ : Type u₂} {C₂ : Type u₃} {D₂ : Type u₄}
  [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [VonNeumannAlgebra A₂]
  [CStarAlgebra B₂] [PartialOrder B₂] [StarOrderedRing B₂]
  [VonNeumannAlgebra B₂]
  [CStarAlgebra C₂] [PartialOrder C₂] [StarOrderedRing C₂]
  [VonNeumannAlgebra C₂]
  [CStarAlgebra D₂] [PartialOrder D₂] [StarOrderedRing D₂]
  [VonNeumannAlgebra D₂]

/-- Infrastructure for 119V: for nmiu-maps `ρ : 𝒜 → 𝒞`, `σ : ℬ → 𝒟`
there is a unique nmiu-map `ρ ⊗ σ` acting on pure tensors as expected. -/
theorem exists_tmapM (ρ : NMIUMap A₂ C₂) (σ : NMIUMap B₂ D₂) :
    ∃! h : NMIUMap (VNT A₂ B₂) (VNT C₂ D₂),
      ∀ (a : A₂) (b : B₂), h (a ⊗ᵥ b) = ρ a ⊗ᵥ σ b := sorry

/-- The nmiu-map `ρ ⊗ σ` (infrastructure for 119V). -/
noncomputable def tmapM (ρ : NMIUMap A₂ C₂) (σ : NMIUMap B₂ D₂) :
    NMIUMap (VNT A₂ B₂) (VNT C₂ D₂) := (exists_tmapM ρ σ).choose

end TmapM

variable (A) in
/-- The identity nmiu-map (infrastructure for 119V). -/
noncomputable def nmiuId : NMIUMap A A :=
  { toStarAlgHom := StarAlgHom.id ℂ A
    preservesDirSups' := sorry }

/-- **119V** (`vn-smc`, proc.tex:4087, Theorem), naturality: the
associators form a natural transformation, i.e.
`α ∘ (f ⊗ (g ⊗ h)) = ((f ⊗ g) ⊗ h) ∘ α` for all ncp-maps `f`, `g`, `h`.
(The monoidal structure is stated concretely rather than through
`CategoryTheory.MonoidalCategory`; cf. the file docstring.) -/
theorem vn_smc_associator_natural {A' B' C' : Type u} [CStarAlgebra A']
    [PartialOrder A'] [StarOrderedRing A'] [VonNeumannAlgebra A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [VonNeumannAlgebra B'] [CStarAlgebra C'] [PartialOrder C']
    [StarOrderedRing C'] [VonNeumannAlgebra C'] (f : NCPMap A A')
    (g : NCPMap B B') (h : NCPMap C C') (t : VNT A (VNT B C)) :
    associator A' B' C' (tmap f (tmap g h) t) =
      tmap (tmap f g) h (associator A B C t) := sorry

/-- **119V** (`vn-smc`, proc.tex:4087, Theorem), pentagon: the pentagon
coherence diagram for the associators commutes. -/
theorem vn_smc_pentagon (t : VNT A (VNT B (VNT C D))) :
    associator (VNT A B) C D (associator A B (VNT C D) t) =
      tmapM (associator A B C) (nmiuId D)
        (associator A (VNT B C) D (tmapM (nmiuId A) (associator B C D) t)) :=
  sorry

/-- **119V** (`vn-smc`, proc.tex:4087, Theorem), triangle: the unitor
coherence diagram commutes: `(ρ_𝒜 ⊗ id) ∘ α = id ⊗ λ_𝒞`. -/
theorem vn_smc_triangle (t : VNT A (VNT ℂ C)) :
    tmapM (rightUnitor A) (nmiuId C) (associator A ℂ C t) =
      tmapM (nmiuId A) (leftUnitor C) t := sorry

/-- **119V** (`vn-smc`, proc.tex:4087, Theorem), hexagon: the braiding
satisfies the hexagon identity. -/
theorem vn_smc_hexagon (t : VNT A (VNT B C)) :
    associator C A B (braiding (VNT A B) C (associator A B C t)) =
      tmapM (braiding A C) (nmiuId B)
        (associator A C B (tmapM (nmiuId A) (braiding B C) t)) := sorry

/-- **119V** (`vn-smc`, proc.tex:4087, Theorem), symmetry:
`γ_{ℬ,𝒜} ∘ γ_{𝒜,ℬ} = id` and `λ_ℬ ∘ γ_{ℬ,ℂ} = ρ_ℬ`. -/
theorem vn_smc_symmetry :
    (∀ t : VNT A B, braiding B A (braiding A B t) = t) ∧
      ∀ t : VNT B ℂ, leftUnitor B (braiding B ℂ t) = rightUnitor B t :=
  sorry

end Monoidal

end Theses.A.Proc
