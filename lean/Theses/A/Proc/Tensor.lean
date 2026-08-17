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
  `VNSub S` of a von Neumann subalgebra `S`, whose algebra instances are
  proved (as for `Corner` in `Measurement.lean`).
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
    (he₂ : ∀ (a : A₁) (b : B₁), h₂ (γ a b) = f a * g b) : h₁ = h₂ := by
  letI : TopologicalSpace C₁ := ultraweak C₁
  -- `h₁` and `h₂` agree on the range of `γ`, hence (being linear) on its
  -- span, which is ultraweakly dense by condition (1) of 108II.
  have hspan : Set.EqOn ⇑h₁ ⇑h₂
      (Submodule.span ℂ {t : C₁ | ∃ a b, t = γ a b} : Set C₁) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨a, b, rfl⟩ := hu
        exact (he₁ a b).trans (he₂ a b).symm
    | zero => simp
    | add u v _ _ hu hv => simp [map_add, hu, hv]
    | smul c u _ hu => simp [map_smul, hu]
  exact DFunLike.coe_injective (Continuous.ext_on hγ.dense hc₁ hc₂ hspan)

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

/-- A tensor product is symmetric in its two factors: if `γ : 𝒜 × ℬ → 𝒯`
is a tensor product then so is `γ.flip : ℬ × 𝒜 → 𝒯`, `(b,a) ↦ γ(a,b)`.
Every clause of 108II is invariant under the swap — the product functional
of `(σ,τ)` for `γ.flip` is the one of `(τ,σ)` for `γ`, since `ℂ` is
commutative.  This is the content of the exercise **119IVc**. -/
theorem isTensorProduct_flip [VonNeumannAlgebra A₁] [VonNeumannAlgebra B₁]
    [VonNeumannAlgebra C₁] {γ : A₁ →ₗ[ℂ] B₁ →ₗ[ℂ] C₁} (hγ : IsTensorProduct γ) :
    IsTensorProduct γ.flip := by
  have happ : ∀ (b : B₁) (a : A₁), γ.flip b a = γ a b := fun _ _ => rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show γ.flip 1 1 = 1
    rw [happ]; exact hγ.miu.1
  · intro b b' a a'
    rw [happ, happ, happ]
    exact hγ.miu.2.1 _ _ _ _
  · intro b a
    rw [happ, happ]
    exact hγ.miu.2.2 _ _
  · have hset : {t : C₁ | ∃ (b : B₁) (a : A₁), t = γ.flip b a}
        = {t : C₁ | ∃ a b, t = γ a b} := by
      ext t
      exact ⟨fun ⟨b, a, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨b, a, h⟩⟩
    rw [hset]
    exact hγ.dense
  · intro σ τ
    obtain ⟨h, hh⟩ := hγ.prod_exists τ σ
    exact ⟨h, fun b a => by rw [happ, hh a b, mul_comm]⟩
  · intro t ht hfaith
    refine hγ.faithful t ht fun σ τ h hcompat => ?_
    exact hfaith τ σ h fun b a => by rw [happ, hcompat a b, mul_comm]

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

/-! ### Auxiliaries for **109III**.1

The map `γ(f,g) = (f(x)g(y))_{x,y}` of the exercise, and the three facts
it needs: that `(x,y) ↦ f(x)g(y)` is square summable (Tonelli for the
double series of nonnegative terms), that the inner product factorises
(the same computation, now for the absolutely summable double series
`⟨f,f'⟩⟨g,g'⟩`), and that the image contains the point masses
`δ_(x,y) = γ(δ_x, δ_y)`, whose span is dense. -/

section L2Aux

variable {X Y : Type u}

/-- `(x,y) ↦ f(x)g(y)` is square summable when `f` and `g` are: the sum of
the squares is the product of the two sums. -/
private theorem l2Mem (f : lp (fun _ : X => ℂ) 2) (g : lp (fun _ : Y => ℂ) 2) :
    Memℓp (fun p : X × Y => f p.1 * g p.2) 2 := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hf : Summable fun x : X => ‖f x‖ ^ (2 : ℝ) := by
    have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (f := (f : ∀ _ : X, ℂ))
      (by rw [h2]; norm_num)).mp (lp.memℓp f)
    rwa [h2] at this
  have hg : Summable fun y : Y => ‖g y‖ ^ (2 : ℝ) := by
    have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (f := (g : ∀ _ : Y, ℂ))
      (by rw [h2]; norm_num)).mp (lp.memℓp g)
    rwa [h2] at this
  refine memℓp_gen ?_
  rw [h2]
  refine (hf.mul_of_nonneg hg (fun x => by positivity)
    (fun y => by positivity)).congr fun p => ?_
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- The bilinear map `γ` of **109III**.1. -/
private def l2Gamma : lp (fun _ : X => ℂ) 2 →ₗ[ℂ] lp (fun _ : Y => ℂ) 2 →ₗ[ℂ]
    lp (fun _ : X × Y => ℂ) 2 :=
  LinearMap.mk₂ ℂ (fun f g => ⟨fun p : X × Y => f p.1 * g p.2, l2Mem f g⟩)
    (fun _ _ _ => by
      ext p; show _ * _ = ((_ : ∀ _ : X × Y, ℂ) + _) p; simp [add_mul])
    (fun _ _ _ => by ext p; simp [mul_assoc])
    (fun _ _ _ => by
      ext p; show _ * _ = ((_ : ∀ _ : X × Y, ℂ) + _) p; simp [mul_add])
    (fun _ _ _ => by ext p; simp [mul_left_comm])

/-- The `X`-series `x ↦ ⟨f(x), f'(x)⟩` is absolutely summable
(Cauchy–Schwarz, i.e. Hölder for the conjugate pair `(2,2)`). -/
private theorem l2SummableInner (f f' : lp (fun _ : X => ℂ) 2) :
    Summable fun x : X => ‖(inner ℂ (f x) (f' x) : ℂ)‖ := by
  have h := lp.summable_mul (E := fun _ : X => ℂ) (p := 2) (q := 2) (by
    rw [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num]
    exact Real.HolderConjugate.two_two) f f'
  refine h.congr fun x => ?_
  rw [RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]

/-- `⟨γ(f,g), γ(f',g')⟩ = ⟨f,f'⟩⟨g,g'⟩`. -/
private theorem l2Gamma_inner (f f' : lp (fun _ : X => ℂ) 2)
    (g g' : lp (fun _ : Y => ℂ) 2) :
    (inner ℂ (l2Gamma f g) (l2Gamma f' g') : ℂ)
      = inner ℂ f f' * inner ℂ g g' := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum,
    tsum_mul_tsum_of_summable_norm (l2SummableInner f f')
      (l2SummableInner g g')]
  refine tsum_congr fun p => ?_
  show (inner ℂ (l2Gamma f g p) (l2Gamma f' g' p) : ℂ) = _
  rw [show (l2Gamma f g p : ℂ) = f p.1 * g p.2 from rfl,
    show (l2Gamma f' g' p : ℂ) = f' p.1 * g' p.2 from rfl,
    RCLike.inner_apply, RCLike.inner_apply, RCLike.inner_apply]
  simp only [map_mul]
  ring

open scoped Classical in
/-- `γ(c·δ_x, δ_y) = c·δ_(x,y)`: the point masses are in the range. -/
private theorem l2Gamma_single (i : X × Y) (c : ℂ) :
    lp.single (E := fun _ : X × Y => ℂ) 2 i c
      = l2Gamma (lp.single (E := fun _ : X => ℂ) 2 i.1 c)
          (lp.single (E := fun _ : Y => ℂ) 2 i.2 1) := by
  ext p
  have hR : (l2Gamma (lp.single (E := fun _ : X => ℂ) 2 i.1 c)
      (lp.single (E := fun _ : Y => ℂ) 2 i.2 1) :
        lp (fun _ : X × Y => ℂ) 2) p
      = (lp.single (E := fun _ : X => ℂ) 2 i.1 c) p.1 *
        (lp.single (E := fun _ : Y => ℂ) 2 i.2 1) p.2 := rfl
  rw [hR, lp.single_apply, lp.single_apply, lp.single_apply]
  by_cases h1 : p.1 = i.1 <;> by_cases h2 : p.2 = i.2 <;>
    simp [Pi.single_apply, h1, h2, Prod.ext_iff]

open scoped Classical in
/-- The span of the range of `γ` is dense: it contains every finite sum of
point masses, and those converge to an arbitrary element of `ℓ²(X×Y)`. -/
private theorem l2Gamma_dense :
    Dense (Submodule.span ℂ
      {t : lp (fun _ : X × Y => ℂ) 2 | ∃ f g, t = l2Gamma f g} :
        Set (lp (fun _ : X × Y => ℂ) 2)) := by
  intro t
  have hsum := lp.hasSum_single (E := fun _ : X × Y => ℂ) (p := 2)
    (by norm_num) t
  refine mem_closure_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  exact ⟨_, _, l2Gamma_single i (t i)⟩

end L2Aux

/-- **109III** (proc.tex:2117, Exercise), part 1: the map
`γ(f,g) = (f(x)g(y))_{x,y} : ℓ²(X) × ℓ²(Y) → ℓ²(X×Y)` is a tensor
product of Hilbert spaces. -/
theorem l2_tensor (X Y : Type u) :
    ∃ γ : lp (fun _ : X => ℂ) 2 →ₗ[ℂ] lp (fun _ : Y => ℂ) 2 →ₗ[ℂ]
        lp (fun _ : X × Y => ℂ) 2,
      (∀ f g x y, γ f g (x, y) = f x * g y) ∧ IsHilbertTensorProduct γ :=
  ⟨l2Gamma, fun _ _ _ _ => rfl, l2Gamma_dense, fun f f' g g' =>
    l2Gamma_inner f f' g g'⟩

/-- **109III** (proc.tex:2117, Exercise), part 2: a subset `E` of a
Hilbert space `ℋ` is an orthonormal basis iff `x ↦ ∑_{e∈E} x_e e` is an
isometric isomorphism `ℓ²(E) → ℋ`. -/
theorem orthonormal_basis_iff_l2_iso (E : Set H) :
    (Orthonormal ℂ (fun e : E => (e : H)) ∧
        Dense (Submodule.span ℂ E : Set H)) ↔
      ∃ T : lp (fun _ : E => ℂ) 2 ≃ₗᵢ[ℂ] H,
        ∀ x : lp (fun _ : E => ℂ) 2, T x = ∑' e : E, x e • (e : H) := by
  classical
  have hrange : Set.range (fun e : E => (e : H)) = E := Subtype.range_coe
  constructor
  · -- `⇒`: this is exactly Mathlib's `HilbertBasis.mk`.
    rintro ⟨hon, hdense⟩
    have hsp : ⊤ ≤
        (Submodule.span ℂ (Set.range fun e : E => (e : H))).topologicalClosure := by
      rw [hrange, Submodule.dense_iff_topologicalClosure_eq_top.mp hdense]
    set b := HilbertBasis.mk hon hsp with hb
    refine ⟨b.repr.symm, fun x => ?_⟩
    have hsum := b.hasSum_repr_symm x
    rw [HilbertBasis.coe_mk] at hsum
    exact hsum.tsum_eq.symm
  · -- `⇐`: `e = T(δ_e)`, so orthonormality is the isometry of `T`, and
    -- `E^⊥ = 0` because `⟨e, y⟩` is the `e`-th coordinate of `T⁻¹y`.
    rintro ⟨T, hT⟩
    have hsingle : ∀ e : E, T (lp.single 2 e (1 : ℂ)) = (e : H) := by
      intro e
      rw [hT]
      refine (tsum_eq_single e ?_).trans ?_
      · intro f hf
        simp [lp.single_apply, hf]
      · simp [lp.single_apply]
    have hinner : ∀ e f : E, ⟪(e : H), (f : H)⟫ =
        ⟪(lp.single 2 e (1 : ℂ) : lp (fun _ : E => ℂ) 2),
          (lp.single 2 f (1 : ℂ) : lp (fun _ : E => ℂ) 2)⟫ := by
      intro e f
      rw [← hsingle e, ← hsingle f, T.inner_map_map]
    refine ⟨⟨fun e => ?_, fun {e f} hef => ?_⟩, ?_⟩
    · change ‖(e : H)‖ = 1
      rw [← hsingle e, T.norm_map, lp.norm_single (by norm_num)]
      simp
    · change ⟪(e : H), (f : H)⟫ = 0
      rw [hinner e f, lp.inner_single_left]
      simp [lp.single_apply, hef]
    · refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
      rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
      intro y hy
      have hcoord : ∀ e : E, (T.symm y) e = 0 := by
        intro e
        have h1 : ⟪lp.single 2 e (1 : ℂ), T.symm y⟫ = (T.symm y) e := by
          rw [lp.inner_single_left]; simp
        have h2 : ⟪lp.single 2 e (1 : ℂ), T.symm y⟫ = ⟪(e : H), y⟫ := by
          rw [← T.inner_map_map, hsingle e, T.apply_symm_apply]
        rw [← h1, h2]
        exact hy _ (Submodule.subset_span e.2)
      have hzero : T.symm y = 0 := by
        ext e
        simpa using hcoord e
      calc y = T (T.symm y) := (T.apply_symm_apply y).symm
        _ = T 0 := by rw [hzero]
        _ = 0 := map_zero _

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
theorem hilbertTensor_nonempty : Nonempty (HilbertTensor H K) := by
  classical
  -- The completion of the algebraic tensor product `H ⊗[ℂ] K`, which
  -- Mathlib equips with the inner product `⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x,x'⟫⟪y,y'⟫`.
  set T := UniformSpace.Completion (H ⊗[ℂ] K)
  set γ : H →ₗ[ℂ] K →ₗ[ℂ] T :=
    LinearMap.compr₂ (TensorProduct.mk ℂ H K)
      (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap with hγ
  have hγ_apply : ∀ (x : H) (y : K), γ x y = ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : T) := by
    intro x y; rfl
  refine ⟨{ space := T, map := γ, isTensor := ⟨?_, ?_⟩ }⟩
  · -- the span of the pure tensors contains the (dense) image of `H ⊗ K`
    have hsub : Set.range ((↑) : (H ⊗[ℂ] K) → T) ⊆
        (Submodule.span ℂ {t : T | ∃ x y, t = γ x y} : Set T) := by
      rintro _ ⟨z, rfl⟩
      induction z with
      | zero =>
          have hz : ((0 : H ⊗[ℂ] K) : T) = 0 := UniformSpace.Completion.coe_zero
          rw [hz]
          exact Submodule.zero_mem _
      | tmul x y =>
          exact Submodule.subset_span ⟨x, y, (hγ_apply x y).symm⟩
      | add z w hz hw =>
          have hadd : ((z + w : H ⊗[ℂ] K) : T) = (z : T) + (w : T) :=
            UniformSpace.Completion.coe_add z w
          rw [hadd]
          exact Submodule.add_mem _ hz hw
    exact UniformSpace.Completion.denseRange_coe.mono hsub
  · intro x x' y y'
    rw [hγ_apply, hγ_apply, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul]

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
    ‖γ x y‖ = ‖x‖ * ‖y‖ := by
  -- `‖γ(x,y)‖² = ⟪γ(x,y),γ(x,y)⟫ = ⟪x,x⟫⟪y,y⟫ = ‖x‖²‖y‖²`
  have h := hγ.inner_mul x x y y
  have hsq : ‖γ x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    have hc : ((‖γ x y‖ ^ 2 : ℝ) : ℂ) = (((‖x‖ * ‖y‖) ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa [inner_self_eq_norm_sq_to_K, mul_pow] using h
    exact_mod_cast hc
  calc ‖γ x y‖ = Real.sqrt (‖γ x y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((‖x‖ * ‖y‖) ^ 2) := by rw [hsq]
    _ = ‖x‖ * ‖y‖ := Real.sqrt_sq (by positivity)

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
        Set T) := by
  classical
  obtain ⟨honE, hdE⟩ := hE
  obtain ⟨honF, hdF⟩ := hF
  set G : Set T := {t : T | ∃ e ∈ E, ∃ f ∈ F, t = γ e f} with hGdef
  constructor
  · -- Orthonormality is immediate from `⟨γ(e,f),γ(e',f')⟩ = ⟨e,e'⟩⟨f,f'⟩`.
    constructor
    · rintro ⟨t, e, he, f, hf, rfl⟩
      change ‖γ e f‖ = 1
      rw [hilb_tensor_basic_1 γ hγ, honE.1 ⟨e, he⟩, honF.1 ⟨f, hf⟩, one_mul]
    · rintro ⟨t, e, he, f, hf, rfl⟩ ⟨t', e', he', f', hf', rfl⟩ hne
      change ⟪γ e f, γ e' f'⟫ = 0
      rw [hγ.inner_mul]
      rcases eq_or_ne e e' with rfl | hee
      · have hff : (⟨f, hf⟩ : F) ≠ ⟨f', hf'⟩ := by
          intro h
          have hfeq : f = f' := congrArg Subtype.val h
          subst hfeq
          exact hne rfl
        rw [honF.2 hff, mul_zero]
      · have hee' : (⟨e, he⟩ : E) ≠ ⟨e', he'⟩ := fun h => hee (congrArg Subtype.val h)
        rw [honE.2 hee', zero_mul]
  · -- Density: expand `x` and `y` in the bases and use continuity of `γ`.
    have hspE : ⊤ ≤
        (Submodule.span ℂ (Set.range fun e : E => (e : H))).topologicalClosure := by
      rw [Subtype.range_coe, Submodule.dense_iff_topologicalClosure_eq_top.mp hdE]
    have hspF : ⊤ ≤
        (Submodule.span ℂ (Set.range fun f : F => (f : K))).topologicalClosure := by
      rw [Subtype.range_coe, Submodule.dense_iff_topologicalClosure_eq_top.mp hdF]
    set bE := HilbertBasis.mk honE hspE with hbE
    set bF := HilbertBasis.mk honF hspF with hbF
    have hbEc : ⇑bE = fun e : E => (e : H) := by
      rw [hbE]; exact HilbertBasis.coe_mk honE hspE
    have hbFc : ⇑bF = fun f : F => (f : K) := by
      rw [hbF]; exact HilbertBasis.coe_mk honF hspF
    set M := (Submodule.span ℂ G).topologicalClosure with hMdef
    have hMclosed : IsClosed (M : Set T) := Submodule.isClosed_topologicalClosure _
    have hGM : ∀ t ∈ G, t ∈ M :=
      fun t ht => Submodule.le_topologicalClosure _ (Submodule.subset_span ht)
    -- `γ(·,f)` and `γ(x,·)` as bounded operators (109IV.1).
    let Lf : K → (H →L[ℂ] T) := fun f =>
      (γ.flip f).mkContinuous ‖f‖ (fun x => by
        rw [LinearMap.flip_apply, hilb_tensor_basic_1 γ hγ, mul_comm])
    let Lx : H → (K →L[ℂ] T) := fun x =>
      (γ x).mkContinuous ‖x‖ (fun y => le_of_eq (hilb_tensor_basic_1 γ hγ x y))
    have hLf : ∀ (f : K) (x : H), Lf f x = γ x f := fun f x => rfl
    have hLx : ∀ (x : H) (y : K), Lx x y = γ x y := fun x y => rfl
    -- Step A: `γ(x,f) = ∑_{e∈ℰ} ⟨e,x⟩ γ(e,f) ∈ M` for `f ∈ ℱ`.
    have hstepA : ∀ (f : K), f ∈ F → ∀ x : H, γ x f ∈ M := by
      intro f hf x
      have h1 : HasSum (fun e : E => bE.repr x e • (e : H)) x := by
        have h := bE.hasSum_repr x
        rwa [hbEc] at h
      have h2 := (Lf f).hasSum h1
      rw [hLf] at h2
      refine hMclosed.mem_of_tendsto h2 (Filter.Eventually.of_forall fun s => ?_)
      refine Submodule.sum_mem _ fun e _ => ?_
      rw [map_smul, hLf]
      exact Submodule.smul_mem _ _ (hGM _ ⟨(e : H), e.2, f, hf, rfl⟩)
    -- Step B: `γ(x,y) = ∑_{f∈ℱ} ⟨f,y⟩ γ(x,f) ∈ M`.
    have hstepB : ∀ (x : H) (y : K), γ x y ∈ M := by
      intro x y
      have h1 : HasSum (fun f : F => bF.repr y f • (f : K)) y := by
        have h := bF.hasSum_repr y
        rwa [hbFc] at h
      have h2 := (Lx x).hasSum h1
      rw [hLx] at h2
      refine hMclosed.mem_of_tendsto h2 (Filter.Eventually.of_forall fun s => ?_)
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [map_smul, hLx]
      exact Submodule.smul_mem _ _ (hstepA (f : K) f.2 x)
    -- Hence `M` contains the (dense) span of the range of `γ`.
    have hsub : (Submodule.span ℂ {t : T | ∃ x y, t = γ x y} : Set T) ⊆ (M : Set T) := by
      refine SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr ?_)
      rintro _ ⟨x, y, rfl⟩
      exact hstepB x y
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr (eq_top_iff.mpr ?_)
    intro t _
    have huniv : (Set.univ : Set T) ⊆ (M : Set T) := by
      rw [← hγ.dense.closure_eq]
      exact hMclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ t)

/-- **110I** (proc.tex:2201, Definition): a bilinear map
`β : ℋ × 𝒦 → ℒ` between Hilbert spaces is **ℓ²-bounded** by
`B ∈ [0,∞)` when
`‖∑ᵢ β(xᵢ,yᵢ)‖² ≤ B² ∑_{i,j} ⟨xᵢ,xⱼ⟩⟨yᵢ,yⱼ⟩`. -/
def L2Bounded (β : H →ₗ[ℂ] K →ₗ[ℂ] L) (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ (n : ℕ) (x : Fin n → H) (y : Fin n → K),
    ‖∑ i, β (x i) (y i)‖ ^ 2 ≤
      bound ^ 2 * (∑ i, ∑ j, ⟪x i, x j⟫ * ⟪y i, y j⟫).re

/-- Auxiliary for **110III**: for a tensor product `γ` of Hilbert spaces
the Gram-type sum `∑_{i,j} ⟨xᵢ,xⱼ⟩⟨yᵢ,yⱼ⟩` occurring in the definition of
ℓ²-boundedness is exactly `‖∑ᵢ γ(xᵢ,yᵢ)‖²`.  (This is the computation
with which proc.tex:2250 opens the proof of 110III.) -/
theorem IsHilbertTensorProduct.gram_sum_re {T : Type u}
    [NormedAddCommGroup T] [InnerProductSpace ℂ T] [CompleteSpace T]
    {γ : H →ₗ[ℂ] K →ₗ[ℂ] T} (hγ : IsHilbertTensorProduct γ) (n : ℕ)
    (x : Fin n → H) (y : Fin n → K) :
    (∑ i, ∑ j, ⟪x i, x j⟫ * ⟪y i, y j⟫).re = ‖∑ i, γ (x i) (y i)‖ ^ 2 := by
  have key : ∑ i, ∑ j, ⟪x i, x j⟫ * ⟪y i, y j⟫
      = ⟪∑ i, γ (x i) (y i), ∑ i, γ (x i) (y i)⟫ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    exact Finset.sum_congr rfl fun j _ =>
      (hγ.inner_mul (x i) (x j) (y i) (y j)).symm
  rw [key, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

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
        ∃ f : T →L[ℂ] L, (∀ x y, f (γ x y) = β x y) ∧ ‖f‖ ≤ bound ∧
          ∀ g : T →L[ℂ] L, (∀ x y, g (γ x y) = β x y) → g = f := by
  classical
  -- `γ` is ℓ²-bounded by `1`: the defining Gram sum *is* `‖∑ γ(xᵢ,yᵢ)‖²`.
  refine ⟨⟨zero_le_one, fun n x y => ?_⟩, ?_⟩
  · rw [hγ.gram_sum_re n x y, one_pow, one_mul]
  intro β bound hβ
  -- The span of the range of `γ` is the range of `β_⊙ = TensorProduct.lift γ`
  -- on the algebraic tensor product, hence the latter is dense.
  have hsub : Submodule.span ℂ {t : T | ∃ x y, t = γ x y} ≤
      LinearMap.range (TensorProduct.lift γ) := by
    rw [Submodule.span_le]
    rintro t ⟨x, y, rfl⟩
    exact ⟨x ⊗ₜ[ℂ] y, by simp⟩
  have hdense : DenseRange ⇑(TensorProduct.lift γ) := by
    refine Dense.mono ?_ hγ.dense
    simpa only [LinearMap.coe_range] using (SetLike.coe_subset_coe.2 hsub)
  -- ℓ²-boundedness of `β` by `bound` says exactly that
  -- `‖β_⊙ z‖ ≤ bound · ‖γ_⊙ z‖` on the algebraic tensor product.
  have hnorm : ∀ z : H ⊗[ℂ] K,
      ‖TensorProduct.lift β z‖ ≤ bound * ‖TensorProduct.lift γ z‖ := by
    intro z
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
    set n := S.card with hn
    set ee := S.equivFin with hee
    have hsum : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
        (g : H × K → M), ∑ i ∈ S, g i = ∑ k : Fin n, g (ee.symm k) :=
      fun {M} _ _ g => by
        rw [← Finset.sum_coe_sort S g]
        exact (Equiv.sum_comp ee.symm fun i : S => g (i : H × K)).symm
    set x : Fin n → H := fun k => ((ee.symm k : H × K)).1 with hx
    set y : Fin n → K := fun k => ((ee.symm k : H × K)).2 with hy
    have hβS : TensorProduct.lift β (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2)
        = ∑ k : Fin n, β (x k) (y k) := by
      rw [map_sum, hsum (M := L) fun i => TensorProduct.lift β (i.1 ⊗ₜ[ℂ] i.2)]
      simp [hx, hy]
    have hγS : TensorProduct.lift γ (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2)
        = ∑ k : Fin n, γ (x k) (y k) := by
      rw [map_sum, hsum (M := T) fun i => TensorProduct.lift γ (i.1 ⊗ₜ[ℂ] i.2)]
      simp [hx, hy]
    rw [hβS, hγS]
    refine le_of_pow_le_pow_left₀ two_ne_zero
      (mul_nonneg hβ.1 (norm_nonneg _)) ?_
    calc ‖∑ k : Fin n, β (x k) (y k)‖ ^ 2
        ≤ bound ^ 2 * (∑ i, ∑ j, ⟪x i, x j⟫ * ⟪y i, y j⟫).re := hβ.2 n x y
      _ = (bound * ‖∑ k : Fin n, γ (x k) (y k)‖) ^ 2 := by
          rw [hγ.gram_sum_re n x y, mul_pow]
  refine ⟨(TensorProduct.lift β).extendOfNorm (TensorProduct.lift γ),
    fun x y => ?_, ?_, ?_⟩
  · have h := LinearMap.extendOfNorm_eq (f := TensorProduct.lift β)
      (e := TensorProduct.lift γ) hdense ⟨bound, hnorm⟩ (x ⊗ₜ[ℂ] y)
    simpa using h
  · exact LinearMap.opNorm_extendOfNorm_le hdense hβ.1 hnorm
  · intro g hg
    refine (LinearMap.extendOfNorm_unique hdense bound hnorm g ?_).symm
    refine TensorProduct.ext' fun x y => ?_
    simpa using hg x y

/-- **110V** (proc.tex:2338, Exercise): the tensor product of Hilbert
spaces is unique up to a unique isometric isomorphism. -/
theorem hilb_tensor_unique {T T' : Type u} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] [NormedAddCommGroup T']
    [InnerProductSpace ℂ T'] [CompleteSpace T']
    (γ : H →ₗ[ℂ] K →ₗ[ℂ] T) (γ' : H →ₗ[ℂ] K →ₗ[ℂ] T')
    (hγ : IsHilbertTensorProduct γ) (hγ' : IsHilbertTensorProduct γ') :
    ∃! φ : T ≃ₗᵢ[ℂ] T', ∀ x y, φ (γ x y) = γ' x y := by
  -- Both `γ` and `γ'` are `ℓ²`-bounded by `1` (110III), so each factors
  -- through the other; the two factorisations are mutually inverse.
  obtain ⟨hb, huniv⟩ := hilb_tensor_universal_property (L := T') γ hγ
  obtain ⟨hb', huniv'⟩ := hilb_tensor_universal_property (L := T) γ' hγ'
  obtain ⟨F, hF, hFn, -⟩ := huniv γ' 1 hb'
  obtain ⟨G, hG, hGn, -⟩ := huniv' γ 1 hb
  have hGF : G.comp F = ContinuousLinearMap.id ℂ T := by
    refine ContinuousLinearMap.ext_on hγ.dense ?_
    rintro _ ⟨x, y, rfl⟩
    simp [hF x y, hG x y]
  have hFG : F.comp G = ContinuousLinearMap.id ℂ T' := by
    refine ContinuousLinearMap.ext_on hγ'.dense ?_
    rintro _ ⟨x, y, rfl⟩
    simp [hF x y, hG x y]
  have hGFa : ∀ t : T, G (F t) = t := fun t =>
    congrArg (fun L : T →L[ℂ] T => L t) hGF
  have hFGa : ∀ t : T', F (G t) = t := fun t =>
    congrArg (fun L : T' →L[ℂ] T' => L t) hFG
  -- `‖F‖ ≤ 1` and `‖G‖ ≤ 1` together with `G ∘ F = id` force `F` isometric.
  have hnorm : ∀ t : T, ‖F t‖ = ‖t‖ := by
    intro t
    refine le_antisymm ?_ ?_
    · simpa using F.le_opNorm t |>.trans (by
        simpa using mul_le_mul_of_nonneg_right hFn (norm_nonneg t))
    · calc ‖t‖ = ‖G (F t)‖ := by rw [hGFa t]
        _ ≤ ‖G‖ * ‖F t‖ := G.le_opNorm _
        _ ≤ 1 * ‖F t‖ := by gcongr
        _ = ‖F t‖ := one_mul _
  set e : T ≃ₗ[ℂ] T' :=
    { toFun := F, map_add' := F.map_add, map_smul' := F.map_smul,
      invFun := G, left_inv := hGFa, right_inv := hFGa } with he
  refine ⟨⟨e, hnorm⟩, fun x y => hF x y, fun φ hφ => ?_⟩
  refine LinearIsometryEquiv.ext fun t => ?_
  have : (φ.toLinearIsometry.toContinuousLinearMap : T →L[ℂ] T') = F := by
    refine ContinuousLinearMap.ext_on hγ.dense ?_
    rintro _ ⟨x, y, rfl⟩
    simpa using (hφ x y).trans (hF x y).symm
  exact congrArg (fun L : T →L[ℂ] T' => L t) this

/-! ## Parsec 1110: Schur's product theorem; the spatial tensor product -/

/-- **111II** (`schur`, proc.tex:2372, Lemma; part of Schur's product
theorem): the entrywise (Hadamard) product of positive `N×N`-matrices
over `ℂ` is positive. -/
theorem schur (N : ℕ) (a b : Matrix (Fin N) (Fin N) ℂ)
    (ha : a.PosSemidef) (hb : b.PosSemidef) :
    (Matrix.hadamard a b).PosSemidef := ha.hadamard hb

/-- **111IV** (`mult-completely-monotone`, proc.tex:2428, Exercise): for
positive matrices `a ≤ ã` and `b ≤ b̃` over `ℂ` (of the same dimensions)
the Hadamard products satisfy `a ⊙ b ≤ ã ⊙ b̃`. -/
theorem mult_completely_monotone (N : ℕ)
    (a a' b b' : Matrix (Fin N) (Fin N) ℂ) (ha : a.PosSemidef)
    (hb : b.PosSemidef) (hab : (a' - a).PosSemidef)
    (hbb : (b' - b).PosSemidef) :
    (Matrix.hadamard a' b' - Matrix.hadamard a b).PosSemidef := by
  -- `a'⊙b' - a⊙b = a⊙(b'-b) + (a'-a)⊙b + (a'-a)⊙(b'-b)`, and each
  -- summand is positive by Schur (111II).
  have hsplit : Matrix.hadamard a' b' - Matrix.hadamard a b =
      Matrix.hadamard a (b' - b) + Matrix.hadamard (a' - a) b +
        Matrix.hadamard (a' - a) (b' - b) := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hsplit]
  exact ((ha.hadamard hbb).add (hab.hadamard hb)).add (hab.hadamard hbb)

/-- Auxiliary: `⟨u,u⟩ = ‖u‖²` as a *real* complex number. -/
theorem inner_self_eq_ofReal_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : E) : ⟪u, u⟫ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · simpa [RCLike.re_to_complex] using (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  · simpa [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) u

/-- Auxiliary: the quadratic form `zᴴMz` of a finite matrix written out. -/
theorem quadForm_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    dotProduct (star z) (M.mulVec z) = ∑ i, ∑ j, star (z i) * M i j * z j := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    mul_assoc]

/-- Auxiliary for **111V**: the quadratic form of the Gram matrix
`(⟨vᵢ,vⱼ⟩)ᵢⱼ` at `z` is `⟨∑ᵢ zᵢvᵢ, ∑ⱼ zⱼvⱼ⟩`. -/
theorem gram_quad_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {n : ℕ} (v : Fin n → E) (z : Fin n → ℂ) :
    ∑ i, ∑ j, star (z i) * ⟪v i, v j⟫ * z j
      = ⟪∑ i, z i • v i, ∑ i, z i • v i⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [inner_smul_right]; simp only [Complex.star_def]; ring

/-- Auxiliary for **111V**: a Gram matrix is positive. -/
theorem gram_posSemidef {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {n : ℕ} (v : Fin n → E) :
    (Matrix.of fun i j : Fin n => ⟪v i, v j⟫).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun z => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, inner_conj_symm]
  · rw [quadForm_eq]
    simp only [Matrix.of_apply]
    rw [gram_quad_eq, inner_self_eq_ofReal_norm_sq]
    exact Complex.zero_le_real.2 (by positivity)

/-- Auxiliary for **111V** (proc.tex:2500): for a bounded operator `A` we
have `(⟨Avᵢ,Avⱼ⟩)ᵢⱼ ≤ ‖A‖² (⟨vᵢ,vⱼ⟩)ᵢⱼ` as matrices. -/
theorem gram_op_le_posSemidef {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {n : ℕ} (A : E →L[ℂ] F) (v : Fin n → E) :
    ((Matrix.of fun i j : Fin n => ((‖A‖ : ℂ) ^ 2) * ⟪v i, v j⟫) -
        Matrix.of fun i j : Fin n => ⟪A (v i), A (v j)⟫).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun z => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, inner_conj_symm, Complex.star_def,
      ← Complex.ofReal_pow]
  · rw [quadForm_eq]
    have hmap : ∑ i, z i • A (v i) = A (∑ i, z i • v i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (A.map_smul _ _).symm
    have hsplit : ∑ i, ∑ j, star (z i) *
          ((Matrix.of fun i j : Fin n => ((‖A‖ : ℂ) ^ 2) * ⟪v i, v j⟫) -
            Matrix.of fun i j : Fin n => ⟪A (v i), A (v j)⟫) i j * z j
        = ((‖A‖ : ℂ) ^ 2) *
            (∑ i, ∑ j, star (z i) * ⟪v i, v j⟫ * z j) -
          ∑ i, ∑ j, star (z i) * ⟪A (v i), A (v j)⟫ * z j := by
      simp only [Matrix.sub_apply, Matrix.of_apply, mul_sub, sub_mul,
        Finset.sum_sub_distrib, Finset.mul_sum]
      refine congrArg₂ _ ?_ rfl
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, gram_quad_eq, gram_quad_eq (fun k => A (v k)) z, hmap]
    have h3 : ((‖A‖ : ℂ)) ^ 2 = ((‖A‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [inner_self_eq_ofReal_norm_sq, inner_self_eq_ofReal_norm_sq, h3,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    refine Complex.zero_le_real.2 ?_
    have hop := A.le_opNorm (∑ i, z i • v i)
    have h0 : (0 : ℝ) ≤ ‖A (∑ i, z i • v i)‖ := norm_nonneg _
    nlinarith

/-- Auxiliary for **111V**: the sum of all entries of a positive matrix is
`≥ 0` (take the all-ones vector in the quadratic form). -/
theorem sum_entries_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) : (0 : ℂ) ≤ ∑ i, ∑ j, M i j := by
  have h := hM.dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  rw [quadForm_eq] at h
  simpa using h

/-- **111V** (`hilb-tensor-functor`, proc.tex:2436, Proposition): for
bounded linear maps `A : ℋ → ℋ'` and `B : 𝒦 → 𝒦'` there is a unique
bounded linear map `A ⊗ B : ℋ ⊗ 𝒦 → ℋ' ⊗ 𝒦'` with
`(A ⊗ B)(x ⊗ y) = Ax ⊗ By`. -/
theorem exists_opTensor (f : H →L[ℂ] H') (g : K →L[ℂ] K') :
    ∃! T : HT H K →L[ℂ] HT H' K',
      ∀ (x : H) (y : K), T (x ⊗ₕ y) = f x ⊗ₕ g y := by
  -- The bilinear map `(x,y) ↦ f x ⊗ g y : ℋ × 𝒦 → ℋ' ⊗ 𝒦'`.
  set β : H →ₗ[ℂ] K →ₗ[ℂ] HT H' K' :=
    ((hilbTensor H' K').map.compl₂ (g : K →ₗ[ℂ] K')).comp (f : H →ₗ[ℂ] H')
    with hβdef
  have hβ_apply : ∀ x y, β x y = f x ⊗ₕ g y := fun _ _ => rfl
  -- It is `ℓ²`-bounded by `‖f‖·‖g‖`, by 111IV applied to the Gram matrices.
  have hbdd : L2Bounded β (‖f‖ * ‖g‖) := by
    refine ⟨by positivity, fun n x y => ?_⟩
    have hlhs : ‖∑ i, β (x i) (y i)‖ ^ 2 =
        (∑ i, ∑ j, ⟪f (x i), f (x j)⟫ * ⟪g (y i), g (y j)⟫).re := by
      have hb : ∀ i, β (x i) (y i)
          = (hilbTensor H' K').map (f (x i)) (g (y i)) := fun _ => rfl
      simp only [hb]
      rw [← (hilbTensor H' K').isTensor.gram_sum_re n (fun i => f (x i))
        (fun i => g (y i))]
    rw [hlhs]
    -- `(⟨f xᵢ, f xⱼ⟩) ⊙ (⟨g yᵢ, g yⱼ⟩) ≤ ‖f‖²‖g‖² (⟨xᵢ,xⱼ⟩) ⊙ (⟨yᵢ,yⱼ⟩)`
    have hpsd := mult_completely_monotone n
      (Matrix.of fun i j : Fin n => ⟪f (x i), f (x j)⟫)
      (Matrix.of fun i j : Fin n => ((‖f‖ : ℂ) ^ 2) * ⟪x i, x j⟫)
      (Matrix.of fun i j : Fin n => ⟪g (y i), g (y j)⟫)
      (Matrix.of fun i j : Fin n => ((‖g‖ : ℂ) ^ 2) * ⟪y i, y j⟫)
      (gram_posSemidef _) (gram_posSemidef _)
      (gram_op_le_posSemidef f x) (gram_op_le_posSemidef g y)
    have hsum := sum_entries_nonneg hpsd
    rw [← sub_nonneg]
    have hre := (Complex.le_def.mp hsum).1
    simp only [Complex.zero_re, Matrix.sub_apply, Matrix.hadamard_apply,
      Matrix.of_apply, Complex.re_sum, Complex.sub_re, Finset.sum_sub_distrib]
      at hre
    have hcast : ∀ i j : Fin n,
        (((‖f‖ : ℂ) ^ 2 * ⟪x i, x j⟫) * ((‖g‖ : ℂ) ^ 2 * ⟪y i, y j⟫)).re =
          (‖f‖ * ‖g‖) ^ 2 * (⟪x i, x j⟫ * ⟪y i, y j⟫).re := by
      intro i j
      have : ((‖f‖ : ℂ) ^ 2 * ⟪x i, x j⟫) * ((‖g‖ : ℂ) ^ 2 * ⟪y i, y j⟫) =
          (((‖f‖ * ‖g‖) ^ 2 : ℝ) : ℂ) * (⟪x i, x j⟫ * ⟪y i, y j⟫) := by
        push_cast; ring
      rw [this, Complex.re_ofReal_mul]
    simp only [hcast] at hre
    rw [Complex.re_sum]
    simp only [Complex.re_sum, ← Finset.mul_sum]
    simp only [← Finset.mul_sum] at hre
    linarith
  obtain ⟨hb1, huniv⟩ := hilb_tensor_universal_property (L := HT H' K')
    (hilbTensor H K).map (hilbTensor H K).isTensor
  obtain ⟨T, hT, -, -⟩ := huniv β (‖f‖ * ‖g‖) hbdd
  refine ⟨T, fun x y => (hT x y).trans (hβ_apply x y), fun T' hT' => ?_⟩
  refine ContinuousLinearMap.ext_on (hilbTensor H K).isTensor.dense ?_
  rintro t ⟨x, y, rfl⟩
  exact (hT' x y).trans ((hT x y).trans (hβ_apply x y)).symm

/-- The operator `A ⊗ B : ℋ ⊗ 𝒦 → ℋ' ⊗ 𝒦'` of 111V. -/
noncomputable def opTensor (f : H →L[ℂ] H') (g : K →L[ℂ] K') :
    HT H K →L[ℂ] HT H' K' := (exists_opTensor f g).choose

theorem opTensor_apply (f : H →L[ℂ] H') (g : K →L[ℂ] K') (x : H) (y : K) :
    opTensor f g (x ⊗ₕ y) = f x ⊗ₕ g y :=
  (exists_opTensor f g).choose_spec.1 x y

/-- Two continuous linear maps out of `ℋ ⊗ 𝒦` agreeing on elementary
tensors are equal. -/
theorem ext_htmul {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {f g : HT H K →L[ℂ] Z} (h : ∀ (x : H) (y : K), f (x ⊗ₕ y) = g (x ⊗ₕ y)) :
    f = g := by
  refine ContinuousLinearMap.ext_on (hilbTensor H K).isTensor.dense ?_
  rintro _ ⟨x, y, rfl⟩
  exact h x y

/-- The defining inner product of `ℋ ⊗ 𝒦`. -/
theorem htmul_inner (x x' : H) (y y' : K) :
    ⟪x ⊗ₕ y, x' ⊗ₕ y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫ :=
  (hilbTensor H K).isTensor.inner_mul x x' y y'

theorem norm_htmul (x : H) (y : K) : ‖x ⊗ₕ y‖ = ‖x‖ * ‖y‖ :=
  hilb_tensor_basic_1 _ (hilbTensor H K).isTensor x y

theorem htmul_add_left (x x' : H) (y : K) :
    (x + x') ⊗ₕ y = x ⊗ₕ y + x' ⊗ₕ y := by
  show (hilbTensor H K).map (x + x') y = _
  rw [map_add]; rfl

theorem htmul_smul_left (c : ℂ) (x : H) (y : K) :
    (c • x) ⊗ₕ y = c • (x ⊗ₕ y) := by
  show (hilbTensor H K).map (c • x) y = _
  rw [map_smul]; rfl

theorem opTensor_one : opTensor (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 :=
  ext_htmul fun x y => by rw [opTensor_apply]; rfl

theorem opTensor_mul (a a' : H →L[ℂ] H) (b b' : K →L[ℂ] K) :
    opTensor (a * a') (b * b') = opTensor a b * opTensor a' b' :=
  ext_htmul fun x y => by
    simp only [ContinuousLinearMap.mul_apply, opTensor_apply]

theorem opTensor_add_left (a a' : H →L[ℂ] H') (b : K →L[ℂ] K') :
    opTensor (a + a') b = opTensor a b + opTensor a' b :=
  ext_htmul fun x y => by
    rw [opTensor_apply]
    show (a + a') x ⊗ₕ b y = opTensor a b (x ⊗ₕ y) + opTensor a' b (x ⊗ₕ y)
    rw [opTensor_apply, opTensor_apply]
    show (a x + a' x) ⊗ₕ b y = _
    rw [htmul_add_left]

theorem opTensor_add_right (a : H →L[ℂ] H') (b b' : K →L[ℂ] K') :
    opTensor a (b + b') = opTensor a b + opTensor a b' :=
  ext_htmul fun x y => by
    rw [opTensor_apply]
    show a x ⊗ₕ (b + b') y = opTensor a b (x ⊗ₕ y) + opTensor a b' (x ⊗ₕ y)
    rw [opTensor_apply, opTensor_apply]
    show a x ⊗ₕ (b y + b' y) = _
    show (hilbTensor H' K').map (a x) (b y + b' y) = _
    rw [map_add]; rfl

theorem opTensor_smul_left (c : ℂ) (a : H →L[ℂ] H') (b : K →L[ℂ] K') :
    opTensor (c • a) b = c • opTensor a b :=
  ext_htmul fun x y => by
    rw [opTensor_apply]
    show (c • a) x ⊗ₕ b y = c • opTensor a b (x ⊗ₕ y)
    rw [opTensor_apply]
    show (c • a x) ⊗ₕ b y = _
    rw [htmul_smul_left]

theorem opTensor_smul_right (c : ℂ) (a : H →L[ℂ] H') (b : K →L[ℂ] K') :
    opTensor a (c • b) = c • opTensor a b :=
  ext_htmul fun x y => by
    rw [opTensor_apply]
    show a x ⊗ₕ (c • b) y = c • opTensor a b (x ⊗ₕ y)
    rw [opTensor_apply]
    show (hilbTensor H' K').map (a x) (c • b y) = _
    rw [map_smul]; rfl

/-- A vector of `ℋ ⊗ 𝒦` is determined by its inner products with the
elementary tensors. -/
theorem eq_of_inner_htmul {u v : HT H K}
    (h : ∀ (x : H) (y : K), ⟪x ⊗ₕ y, u⟫ = ⟪x ⊗ₕ y, v⟫) : u = v := by
  have hcl : (innerSL ℂ u : HT H K →L[ℂ] ℂ) = innerSL ℂ v := by
    refine ext_htmul fun x y => ?_
    have h1 := congrArg (starRingEnd ℂ) (h x y)
    rw [inner_conj_symm, inner_conj_symm] at h1
    simpa using h1
  refine ext_inner_right ℂ fun z => ?_
  exact congrArg (fun L : HT H K →L[ℂ] ℂ => L z) hcl

/-- The adjoint of `A ⊗ B` is `A* ⊗ B*`. -/
theorem opTensor_adjoint (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    ContinuousLinearMap.adjoint (opTensor a b)
      = opTensor (ContinuousLinearMap.adjoint a) (ContinuousLinearMap.adjoint b) := by
  refine ext_htmul fun x y => ?_
  refine eq_of_inner_htmul fun x' y' => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, opTensor_apply, opTensor_apply,
    htmul_inner, htmul_inner, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]

theorem opTensor_star (a : H →L[ℂ] H) (b : K →L[ℂ] K) :
    star (opTensor a b) = opTensor (star a) (star b) :=
  opTensor_adjoint a b

end Hilbert

/-! ## Von Neumann subalgebras as bundled algebras (for the spatial
tensor product) -/

variable (A) in
/-- Wrapper: a von Neumann subalgebra `S ⊆ A` bundled as an algebra in its
own right, with proved instances (cf. `Corner` in `Measurement.lean`).
The witness `hS : IsVNSubalgebra A S` (42V, `A/VN/Basic.lean`) is carried
as an index: a bare `StarSubalgebra ℂ A` need not be norm-closed, hence
need not be complete, hence need not be a C*-algebra at all. -/
structure VNSub (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    Type u where
  val : A
  property : val ∈ S

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}

theorem val_injective :
    Function.Injective (VNSub.val (A := A) (S := S) (hS := hS)) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  cases h; rfl

instance : Zero (VNSub A S hS) := ⟨⟨0, zero_mem S⟩⟩
instance : Add (VNSub A S hS) :=
  ⟨fun a b => ⟨a.val + b.val, add_mem a.property b.property⟩⟩
instance : Neg (VNSub A S hS) := ⟨fun a => ⟨-a.val, neg_mem a.property⟩⟩
instance : Sub (VNSub A S hS) :=
  ⟨fun a b => ⟨a.val - b.val, sub_mem a.property b.property⟩⟩
instance : SMul ℕ (VNSub A S hS) := ⟨fun n a => ⟨n • a.val, nsmul_mem a.property n⟩⟩
instance : SMul ℤ (VNSub A S hS) := ⟨fun n a => ⟨n • a.val, zsmul_mem a.property n⟩⟩
instance : SMul ℂ (VNSub A S hS) :=
  ⟨fun z a => ⟨z • a.val, SMulMemClass.smul_mem z a.property⟩⟩
instance : One (VNSub A S hS) := ⟨⟨1, one_mem S⟩⟩
instance : Mul (VNSub A S hS) :=
  ⟨fun a b => ⟨a.val * b.val, mul_mem a.property b.property⟩⟩
instance : Star (VNSub A S hS) := ⟨fun a => ⟨star a.val, star_mem a.property⟩⟩

@[simp] theorem val_zero : (0 : VNSub A S hS).val = 0 := rfl
@[simp] theorem val_add (a b : VNSub A S hS) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_neg (a : VNSub A S hS) : (-a).val = -a.val := rfl
@[simp] theorem val_sub (a b : VNSub A S hS) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_one : (1 : VNSub A S hS).val = 1 := rfl
@[simp] theorem val_mul (a b : VNSub A S hS) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_star (a : VNSub A S hS) : (star a).val = star a.val := rfl
@[simp] theorem val_smul (z : ℂ) (a : VNSub A S hS) : (z • a).val = z • a.val := rfl

instance instAddCommGroup : AddCommGroup (VNSub A S hS) :=
  Function.Injective.addCommGroup VNSub.val val_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance instRing : Ring (VNSub A S hS) where
  __ := instAddCommGroup
  mul_assoc a b c := val_injective (mul_assoc _ _ _)
  one_mul a := val_injective (one_mul _)
  mul_one a := val_injective (mul_one _)
  left_distrib a b c := val_injective (mul_add _ _ _)
  right_distrib a b c := val_injective (add_mul _ _ _)
  zero_mul a := val_injective (zero_mul _)
  mul_zero a := val_injective (mul_zero _)

/-- `VNSub.val` as an additive monoid homomorphism. -/
def valAddHom : VNSub A S hS →+ A where
  toFun := VNSub.val
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℂ (VNSub A S hS) :=
  Function.Injective.module ℂ valAddHom val_injective (fun _ _ => rfl)

instance instAlgebra : Algebra ℂ (VNSub A S hS) :=
  Algebra.ofModule (fun r x y => val_injective (smul_mul_assoc r x.val y.val))
    (fun r x y => val_injective (mul_smul_comm r x.val y.val))

instance instStarRing : StarRing (VNSub A S hS) where
  star_involutive a := val_injective (star_star a.val)
  star_mul a b := val_injective (star_mul a.val b.val)
  star_add a b := val_injective (star_add a.val b.val)

instance instStarModule : StarModule ℂ (VNSub A S hS) where
  star_smul r a := val_injective (star_smul r a.val)

/-- `VNSub.val` as a non-unital ring homomorphism. -/
def valNonUnitalRingHom : VNSub A S hS →ₙ+* A where
  toFun := VNSub.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance instNormedRing : NormedRing (VNSub A S hS) :=
  NormedRing.induced (VNSub A S hS) A valNonUnitalRingHom val_injective

@[simp] theorem norm_def (a : VNSub A S hS) : ‖a‖ = ‖a.val‖ := rfl

instance instNormedAlgebra : NormedAlgebra ℂ (VNSub A S hS) where
  norm_smul_le r a := by simpa [norm_def] using (norm_smul_le r a.val)

theorem isometry_val : Isometry (VNSub.val (A := A) (S := S) (hS := hS)) :=
  AddMonoidHomClass.isometry_of_norm valAddHom (fun _ => rfl)

theorem range_val :
    Set.range (VNSub.val (A := A) (S := S) (hS := hS)) = (S : Set A) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩; exact b.property
  · intro ha; exact ⟨⟨a, ha⟩, rfl⟩

instance instCompleteSpace : CompleteSpace (VNSub A S hS) := by
  refine (isometry_val (S := S) (hS := hS)).isUniformInducing.completeSpace ?_
  rw [range_val]
  exact hS.isClosed.isComplete

instance instCStarRing : CStarRing (VNSub A S hS) where
  norm_mul_self_le a := CStarRing.norm_star_mul_self (x := a.val) |>.symm.le

end VNSub

noncomputable instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    CStarAlgebra (VNSub A S hS) where

noncomputable instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    PartialOrder (VNSub A S hS) :=
  PartialOrder.lift VNSub.val VNSub.val_injective

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S}

theorem le_def (a b : VNSub A S hS) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

/-- The square root of a positive element of a *closed* star subalgebra
again lies in it: `√a = cfcₙ √ a`, and the non-unital continuous functional
calculus of an element stays inside every closed star subalgebra
containing it (Mathlib's `cfcₙ_mem`). -/
theorem sqrt_mem (hcl : IsClosed (S : Set A)) (a : A) (ha : 0 ≤ a)
    (hmem : a ∈ S) : CFC.sqrt a ∈ S := by
  have : IsClosed (S : Set A) := hcl
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) Real.sqrt hmem

end VNSub

instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    StarOrderedRing (VNSub A S hS) := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · show z.val + x.val ≤ z.val + y.val
    exact add_le_add le_rfl (show x.val ≤ y.val from hxy)
  · constructor
    · intro hx
      have hx' : (0 : A) ≤ x.val := hx
      refine ⟨⟨CFC.sqrt x.val, VNSub.sqrt_mem hS.isClosed x.val hx' x.property⟩, ?_⟩
      refine VNSub.val_injective ?_
      have hsa : IsSelfAdjoint (CFC.sqrt x.val) :=
        IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x.val)
      show x.val = star (CFC.sqrt x.val) * CFC.sqrt x.val
      rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self x.val hx']
    · rintro ⟨s, rfl⟩
      show (0 : A) ≤ star s.val * s.val
      exact star_mul_self_nonneg s.val

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S} [VonNeumannAlgebra A]

/-- A self-adjoint element of `S`, viewed in `A`. -/
def saMap (d : selfAdjoint (VNSub A S hS)) : selfAdjoint A :=
  ⟨d.1.val, congrArg VNSub.val (show star d.1 = d.1 from d.2)⟩

@[simp] theorem saMap_coe (d : selfAdjoint (VNSub A S hS)) :
    ((saMap d : selfAdjoint A) : A) = d.1.val := rfl

/-- Suprema of nonempty directed sets of self-adjoint elements are computed
in a von Neumann subalgebra exactly as they are in `A` (42V part 4). -/
theorem isLUB_saMap_image {D : Set (selfAdjoint (VNSub A S hS))}
    {s : selfAdjoint (VNSub A S hS)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (saMap '' D) (saMap s) := by
  set D' : Set (selfAdjoint A) := saMap '' D with hD'
  have hne' : D'.Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) D' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
    exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩
  have hbdd' : BddAbove D' := by
    refine ⟨saMap s, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hlub.1 hx
  obtain ⟨s₀, hs₀⟩ :=
    VonNeumannAlgebra.isLUB_of_bddAbove_directed D' hne' hdir' hbdd'
  have hmem : (s₀ : A) ∈ S :=
    hS.dirSup_mem D' s₀ (by rintro _ ⟨x, hx, rfl⟩; exact x.1.property) hne' hdir' hs₀
  set t : VNSub A S hS := ⟨(s₀ : A), hmem⟩ with ht
  have htsa : IsSelfAdjoint t := val_injective s₀.2
  have hlubt : IsLUB D ⟨t, htsa⟩ := by
    constructor
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro u hu
      have hub : saMap u ∈ upperBounds D' := by
        rintro _ ⟨x, hx, rfl⟩
        exact hu hx
      exact hs₀.2 hub
  have hst : s = ⟨t, htsa⟩ := hlub.unique hlubt
  have hsm : saMap (⟨t, htsa⟩ : selfAdjoint (VNSub A S hS)) = s₀ := Subtype.ext rfl
  rw [hst, hsm]
  exact hs₀

/-- Restriction of an np-functional on `A` to a von Neumann subalgebra. -/
def restrictNP (ω : NPFunctional A) : NPFunctional (VNSub A S hS) where
  toPositiveLinearMap :=
    { toFun := fun a => ω a.val
      map_add' := fun x y => map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c x => map_smul ω.toPositiveLinearMap _ _
      monotone' := fun x y hxy => ω.toPositiveLinearMap.monotone hxy }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hkey := ω.preservesDirSups' (saMap '' D) (saMap s) (hne.image _)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
        obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
        exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩)
      (isLUB_saMap_image hne hdir hlub)
    rw [← Set.image_comp] at hkey
    exact hkey

@[simp] theorem restrictNP_apply (ω : NPFunctional A) (a : VNSub A S hS) :
    (restrictNP ω : NPFunctional (VNSub A S hS)) a = ω a.val := rfl

end VNSub

instance (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S)
    [VonNeumannAlgebra A] : VonNeumannAlgebra (VNSub A S hS) where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    obtain ⟨u, hu⟩ := hbdd
    have hne' : (VNSub.saMap '' D).Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) (VNSub.saMap (S := S) (hS := hS) '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨v, hv, hxv, hzv⟩ := hdir x hx z hz
      exact ⟨VNSub.saMap v, ⟨v, hv, rfl⟩, hxv, hzv⟩
    have hbdd' : BddAbove (VNSub.saMap (S := S) (hS := hS) '' D) := by
      refine ⟨VNSub.saMap u, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    obtain ⟨s₀, hs₀⟩ :=
      VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
    have hmem : (s₀ : A) ∈ S :=
      hS.dirSup_mem _ s₀ (by rintro _ ⟨x, hx, rfl⟩; exact x.1.property) hne' hdir' hs₀
    refine ⟨⟨⟨(s₀ : A), hmem⟩, VNSub.val_injective s₀.2⟩, ?_, ?_⟩
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro v hv
      have hub : VNSub.saMap v ∈ upperBounds (VNSub.saMap (S := S) (hS := hS) '' D) := by
        rintro _ ⟨x, hx, rfl⟩
        exact hv hx
      exact hs₀.2 hub
  np_faithful := by
    intro a ha hω
    refine VNSub.val_injective ?_
    exact VonNeumannAlgebra.np_faithful a.val ha (fun ω => hω (VNSub.restrictNP ω))

/-! ### The inclusion of a von Neumann subalgebra as an nmiu-map -/

namespace VNSub

variable {S : StarSubalgebra ℂ A} {hS : IsVNSubalgebra A S} [VonNeumannAlgebra A]

/-- `VNSub.val` as a `ℂ`-linear map. -/
def valLinearMap : VNSub A S hS →ₗ[ℂ] A where
  toFun := VNSub.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion `S ↪ A` of a von Neumann subalgebra as a ∗-homomorphism. -/
def valStarAlgHom : VNSub A S hS →⋆ₐ[ℂ] A where
  toFun := VNSub.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    show (algebraMap ℂ (VNSub A S hS) r).val = algebraMap ℂ A r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' _ := rfl

@[simp] theorem valStarAlgHom_apply (a : VNSub A S hS) :
    valStarAlgHom a = a.val := rfl

/-- The inclusion `S ↪ A` of a von Neumann subalgebra is an nmiu-map: it is
a ∗-homomorphism, and normal because suprema in `S` are computed in `A`. -/
def valNMIU : NMIUMap (VNSub A S hS) A where
  toStarAlgHom := valStarAlgHom
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := isLUB_coe_of_isLUB (hne.image saMap) (isLUB_saMap_image hne hdir hlub)
    rw [← Set.image_comp] at h
    exact h

@[simp] theorem valNMIU_apply (a : VNSub A S hS) :
    valNMIU (S := S) (hS := hS) a = a.val := rfl

theorem valNMIU_injective :
    Function.Injective ⇑(valNMIU (A := A) (S := S) (hS := hS)) :=
  val_injective

theorem valNMIU_range :
    (valNMIU (A := A) (S := S) (hS := hS)).toStarAlgHom.range = S := by
  refine SetLike.ext fun a => ?_
  constructor
  · rintro ⟨b, rfl⟩; exact b.property
  · intro ha; exact ⟨⟨a, ha⟩, rfl⟩

theorem isVNSubalgebra_valNMIU_range :
    IsVNSubalgebra A (valNMIU (A := A) (S := S) (hS := hS)).toStarAlgHom.range := by
  rw [valNMIU_range]; exact hS

/-- The ultraweak topology of a von Neumann subalgebra is the one induced
from the ambient algebra (**89XI**.2). -/
theorem ultraweak_eq_induced :
    ultraweak (VNSub A S hS) =
      TopologicalSpace.induced (VNSub.val (A := A) (S := S) (hS := hS))
        (ultraweak A) :=
  functional_permanence_2 valNMIU valNMIU_injective isVNSubalgebra_valNMIU_range

end VNSub

section Spatial

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open scoped Pointwise in
/-- The linear span of `{A ⊗ B : A ∈ 𝒜, B ∈ ℬ}` is a ∗-subalgebra of
`B(ℋ ⊗ 𝒦)`: it contains `1 = 1 ⊗ 1`, and is closed under multiplication and
the involution because `(A⊗B)(A'⊗B') = AA' ⊗ BB'` and `(A⊗B)* = A*⊗B*`. -/
def spatialSpan (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    StarSubalgebra ℂ (HT H K →L[ℂ] HT H K) where
  carrier := ↑(Submodule.span ℂ
    {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
  mul_mem' := by
    intro a b ha hb
    have hle : Submodule.span ℂ
        ({x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} *
          {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}) ≤
        Submodule.span ℂ
          {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨a1, ha1, b1, hb1, rfl⟩, _, ⟨a2, ha2, b2, hb2, rfl⟩, rfl⟩
      exact Submodule.subset_span
        ⟨a1 * a2, mul_mem ha1 ha2, b1 * b2, mul_mem hb1 hb2,
          (opTensor_mul a1 a2 b1 b2).symm⟩
    have h : a * b ∈
        (Submodule.span ℂ
            {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}) *
          (Submodule.span ℂ
            {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}) :=
      Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    exact hle h
  one_mem' := Submodule.subset_span ⟨1, one_mem SA, 1, one_mem SB, opTensor_one.symm⟩
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := by
    intro r
    have h1 : (algebraMap ℂ (HT H K →L[ℂ] HT H K)) r = r • (1 : HT H K →L[ℂ] HT H K) :=
      Algebra.algebraMap_eq_smul_one r
    rw [h1]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, one_mem SA, 1, one_mem SB, opTensor_one.symm⟩)
  star_mem' := by
    intro a ha
    refine Submodule.span_induction (p := fun x _ => star x ∈ Submodule.span ℂ
      {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨a1, ha1, b1, hb1, rfl⟩
      exact Submodule.subset_span
        ⟨star a1, star_mem ha1, star b1, star_mem hb1, opTensor_star a1 b1⟩
    · simp
    · intro x y _ _ hx hy
      rw [star_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [star_smul]
      exact Submodule.smul_mem _ _ hx

theorem coe_spatialSpan (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K)) =
      ↑(Submodule.span ℂ
        {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}) := rfl

theorem wstar_spatialSpan (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K)) :
    wstar (HT H K →L[ℂ] HT H K) (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K)) =
      wstar (HT H K →L[ℂ] HT H K)
        {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} := by
  have hGsub : {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} ⊆
      (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K)) := Submodule.subset_span
  have hspan : (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K)) ⊆
      (wstar (HT H K →L[ℂ] HT H K)
        {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} :
          Set (HT H K →L[ℂ] HT H K)) := by
    rw [coe_spatialSpan]
    refine (Submodule.span_le (p := (wstar (HT H K →L[ℂ] HT H K)
      {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}).toSubmodule)).mpr ?_
    exact (isVNSubalgebra_wstar
      {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}).2
  have h2 : {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} ⊆
      (wstar (HT H K →L[ℂ] HT H K)
        (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K)) :
          Set (HT H K →L[ℂ] HT H K)) :=
    hGsub.trans (isVNSubalgebra_wstar
      (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K))).2
  exact le_antisymm
    (sInf_le ⟨(isVNSubalgebra_wstar
      {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}).1, hspan⟩)
    (sInf_le ⟨(isVNSubalgebra_wstar
      (spatialSpan SA SB : Set (HT H K →L[ℂ] HT H K))).1, h2⟩)

/-- The vector functionals `⟨x⊗y,(·)x⊗y⟩` are faithful on `B(ℋ ⊗ 𝒦)`:
a positive operator killed by all of them is zero (the last step of the
proof of **111VII**, condition `tensor-3`). -/
theorem eq_zero_of_inner_htmul_eq_zero {t : HT H K →L[ℂ] HT H K} (ht : 0 ≤ t)
    (h : ∀ (x : H) (y : K), ⟪x ⊗ₕ y, t (x ⊗ₕ y)⟫ = 0) : t = 0 := by
  have hRR : CFC.sqrt t * CFC.sqrt t = t := CFC.sqrt_mul_sqrt_self t ht
  have hRsa : IsSelfAdjoint (CFC.sqrt t) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg t)
  have hRadj : ContinuousLinearMap.adjoint (CFC.sqrt t) = CFC.sqrt t := hRsa.star_eq
  have hkill : ∀ (x : H) (y : K), CFC.sqrt t (x ⊗ₕ y) = 0 := by
    intro x y
    have h0 := h x y
    rw [← hRR] at h0
    have hstep : ⟪CFC.sqrt t (x ⊗ₕ y), CFC.sqrt t (x ⊗ₕ y)⟫ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hRadj]
      simpa using h0
    exact inner_self_eq_zero.mp hstep
  have hR0 : CFC.sqrt t = 0 := by
    refine ext_htmul fun x y => ?_
    rw [hkill x y]
    rfl
  rw [← hRR, hR0, mul_zero]

/-- The heart of condition `tensor-2` of **111VII**: given np-functionals
`σ` on `𝒜 ⊆ B(ℋ)` and `τ` on `ℬ ⊆ B(𝒦)`, write them (by **89IX**
`normal-functional`) as `σ = ∑ₙ⟨xₙ,(·)xₙ⟩` and `τ = ∑ₘ⟨yₘ,(·)yₘ⟩`; then
`∑_{n,m}‖xₙ ⊗ yₘ‖² < ∞`, so `(xₙ ⊗ yₘ)_{n,m}` defines an np-functional `ω`
on `B(ℋ ⊗ 𝒦)` (**38IV**.2 through `exists_sumVectorNP`), and
`ω(A ⊗ B) = σ(A)τ(B)`. -/
theorem exists_np_of_spatial_product {SA : StarSubalgebra ℂ (H →L[ℂ] H)}
    {SB : StarSubalgebra ℂ (K →L[ℂ] K)} {hSA : IsVNSubalgebra (H →L[ℂ] H) SA}
    {hSB : IsVNSubalgebra (K →L[ℂ] K) SB}
    (σ : NPFunctional (VNSub (H →L[ℂ] H) SA hSA))
    (τ : NPFunctional (VNSub (K →L[ℂ] K) SB hSB)) :
    ∃ ω : NPFunctional (HT H K →L[ℂ] HT H K),
      ∀ (a : VNSub (H →L[ℂ] H) SA hSA) (b : VNSub (K →L[ℂ] K) SB hSB),
        ω (opTensor a.val b.val) = σ a * τ b := by
  obtain ⟨x, hxsum, hx⟩ := normal_functional VNSub.valNMIU
    VNSub.valNMIU_injective VNSub.isVNSubalgebra_valNMIU_range σ
  obtain ⟨y, hysum, hy⟩ := normal_functional VNSub.valNMIU
    VNSub.valNMIU_injective VNSub.isVNSubalgebra_valNMIU_range τ
  -- `∑_{n,m} ‖xₙ ⊗ yₘ‖² = (∑ₙ‖xₙ‖²)(∑ₘ‖yₘ‖²) < ∞`
  have hz : Summable fun p : ℕ × ℕ => ‖x p.1 ⊗ₕ y p.2‖ ^ 2 := by
    refine ((hxsum.mul_of_nonneg hysum (fun n => by positivity)
      (fun m => by positivity)).congr fun p => ?_)
    rw [norm_htmul, mul_pow]
  obtain ⟨ω, hω⟩ :=
    exists_sumVectorNP (H := HT H K) (ι := ℕ × ℕ) (fun p => x p.1 ⊗ₕ y p.2) hz
  refine ⟨ω, fun a b => ?_⟩
  -- both `ω(A⊗B)` and `σ(A)τ(B)` are the sum of the same double family
  have hfn : Summable fun n : ℕ => ‖⟪x n, a.val (x n)⟫‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (hxsum.mul_left ‖a.val‖)
    calc ‖⟪x n, a.val (x n)⟫‖ ≤ ‖x n‖ * ‖a.val (x n)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x n‖ * (‖a.val‖ * ‖x n‖) := by
          gcongr
          exact a.val.le_opNorm _
      _ = ‖a.val‖ * ‖x n‖ ^ 2 := by ring
  have hgn : Summable fun m : ℕ => ‖⟪y m, b.val (y m)⟫‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) (hysum.mul_left ‖b.val‖)
    calc ‖⟪y m, b.val (y m)⟫‖ ≤ ‖y m‖ * ‖b.val (y m)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y m‖ * (‖b.val‖ * ‖y m‖) := by
          gcongr
          exact b.val.le_opNorm _
      _ = ‖b.val‖ * ‖y m‖ ^ 2 := by ring
  have hsummable : Summable fun p : ℕ × ℕ =>
      ⟪x p.1, a.val (x p.1)⟫ * ⟪y p.2, b.val (y p.2)⟫ := by
    refine Summable.of_norm ?_
    refine (hfn.mul_of_nonneg hgn (fun n => norm_nonneg _) (fun m => norm_nonneg _)).congr
      fun p => ?_
    rw [norm_mul]
  have h1 := hω (opTensor a.val b.val)
  have h2 := (hx a).mul (hy b) hsummable
  have hterm : ∀ p : ℕ × ℕ,
      ⟪x p.1 ⊗ₕ y p.2, opTensor a.val b.val (x p.1 ⊗ₕ y p.2)⟫
        = ⟪x p.1, a.val (x p.1)⟫ * ⟪y p.2, b.val (y p.2)⟫ := by
    intro p
    rw [opTensor_apply, htmul_inner]
  rw [funext hterm] at h1
  exact h1.unique h2

/-- Condition `tensor-1` of **111VII**: the linear span of the elementary
tensors is ultraweakly dense in the von Neumann algebra `𝒯` they generate.
This is the Double Commutant Theorem (**88VI**: `W*(S)` is the ultraweak
closure of a unital ∗-subalgebra `S`) together with the fact that the
ultraweak topology of a von Neumann subalgebra is induced from the ambient
algebra (**89XI**.2). -/
theorem spatial_dense (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (U : Set (VNSub (HT H K →L[ℂ] HT H K)
      (wstar (HT H K →L[ℂ] HT H K)
        {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
      (isVNSubalgebra_wstar _).1))
    (hU : VNSub.val '' U =
      {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b}) :
    @Dense (VNSub (HT H K →L[ℂ] HT H K)
      (wstar (HT H K →L[ℂ] HT H K)
        {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
      (isVNSubalgebra_wstar _).1) (ultraweak _)
      (Submodule.span ℂ U : Set (VNSub (HT H K →L[ℂ] HT H K)
        (wstar (HT H K →L[ℂ] HT H K)
          {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
        (isVNSubalgebra_wstar _).1)) := by
  letI : TopologicalSpace (HT H K →L[ℂ] HT H K) := ultraweak (HT H K →L[ℂ] HT H K)
  letI : TopologicalSpace (VNSub (HT H K →L[ℂ] HT H K)
      (wstar (HT H K →L[ℂ] HT H K)
        {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
      (isVNSubalgebra_wstar _).1) :=
    ultraweak (VNSub (HT H K →L[ℂ] HT H K)
      (wstar (HT H K →L[ℂ] HT H K)
        {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
      (isVNSubalgebra_wstar _).1)
  have hind : Topology.IsInducing
      (VNSub.val (A := HT H K →L[ℂ] HT H K)
        (S := wstar (HT H K →L[ℂ] HT H K)
          {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
        (hS := (isVNSubalgebra_wstar _).1)) :=
    ⟨VNSub.ultraweak_eq_induced⟩
  refine hind.dense_iff.mpr fun t => ?_
  have himg : VNSub.val '' (Submodule.span ℂ U : Set (VNSub (HT H K →L[ℂ] HT H K)
        (wstar (HT H K →L[ℂ] HT H K)
          {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
        (isVNSubalgebra_wstar _).1)) =
      (Submodule.span ℂ (VNSub.val '' U) : Set (HT H K →L[ℂ] HT H K)) := by
    show ⇑VNSub.valLinearMap '' (Submodule.span ℂ U : Set (VNSub (HT H K →L[ℂ] HT H K)
        (wstar (HT H K →L[ℂ] HT H K)
          {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
        (isVNSubalgebra_wstar _).1)) =
      (Submodule.span ℂ (⇑VNSub.valLinearMap '' U) : Set (HT H K →L[ℂ] HT H K))
    rw [← Submodule.map_span, Submodule.map_coe]
  rw [himg, hU]
  have hclosure : closure
      (↑(Submodule.span ℂ
        {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})) =
      (wstar (HT H K →L[ℂ] HT H K)
        {x : HT H K →L[ℂ] HT H K | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} :
          Set (HT H K →L[ℂ] HT H K)) := by
    rw [← coe_spatialSpan SA SB, ← (double_commutant (spatialSpan SA SB)).2.1,
      (double_commutant (spatialSpan SA SB)).2.2, wstar_spatialSpan]
  rw [hclosure]
  exact t.property

/-- **111VII** (`special-tensor`, proc.tex:2491, Theorem): for von Neumann
algebras `𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)` of operators, the map
`(A, B) ↦ A ⊗ B : 𝒜 × ℬ → B(ℋ ⊗ 𝒦)` is miu-bilinear, and its restriction
to the von Neumann subalgebra `𝒯 ⊆ B(ℋ ⊗ 𝒦)` generated by its range is a
tensor product of `𝒜` and `ℬ`. -/
theorem special_tensor (SA : StarSubalgebra ℂ (H →L[ℂ] H))
    (SB : StarSubalgebra ℂ (K →L[ℂ] K))
    (hSA : IsVNSubalgebra (H →L[ℂ] H) SA)
    (hSB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    ∃ γ : VNSub (H →L[ℂ] H) SA hSA →ₗ[ℂ] VNSub (K →L[ℂ] K) SB hSB →ₗ[ℂ]
        VNSub (HT H K →L[ℂ] HT H K)
          (wstar (HT H K →L[ℂ] HT H K)
            {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
          (isVNSubalgebra_wstar _).1,
      (∀ a b, (γ a b).val = opTensor a.val b.val) ∧ IsTensorProduct γ := by
  have hmem : ∀ (a : VNSub (H →L[ℂ] H) SA hSA) (b : VNSub (K →L[ℂ] K) SB hSB),
      opTensor a.val b.val ∈
        wstar (HT H K →L[ℂ] HT H K) {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b} :=
    fun a b => (isVNSubalgebra_wstar _).2 ⟨a.val, a.property, b.val, b.property, rfl⟩
  refine ⟨LinearMap.mk₂ ℂ (fun a b => ⟨opTensor a.val b.val, hmem a b⟩)
      (fun a a' b => VNSub.val_injective (opTensor_add_left _ _ _))
      (fun c a b => VNSub.val_injective (opTensor_smul_left c _ _))
      (fun a b b' => VNSub.val_injective (opTensor_add_right _ _ _))
      (fun c a b => VNSub.val_injective (opTensor_smul_right c _ _)),
    fun a b => rfl, ?_, ?_, ?_, ?_⟩
  · -- miu-bilinearity
    refine ⟨VNSub.val_injective opTensor_one, fun a b c d => ?_, fun a b => ?_⟩
    · exact VNSub.val_injective (opTensor_mul _ _ _ _)
    · exact VNSub.val_injective (opTensor_star _ _)
  · -- **tensor-1**
    refine spatial_dense SA SB _ ?_
    ext u
    constructor
    · rintro ⟨t, ⟨a, b, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, b.val, b.property, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨opTensor a b, hmem ⟨a, ha⟩ ⟨b, hb⟩⟩, ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩, rfl⟩
  · -- **tensor-2**
    intro σ τ
    obtain ⟨ω, hω⟩ := exists_np_of_spatial_product σ τ
    exact ⟨VNSub.restrictNP ω, fun a b => hω a b⟩
  · -- **tensor-3**
    intro t ht hfaith
    refine VNSub.val_injective ?_
    show t.val = (0 : HT H K →L[ℂ] HT H K)
    refine eq_zero_of_inner_htmul_eq_zero ht fun x y => ?_
    refine hfaith (VNSub.restrictNP (vectorNP x)) (VNSub.restrictNP (vectorNP y))
      (VNSub.restrictNP (vectorNP (x ⊗ₕ y))) fun a b => ?_
    show ⟪x ⊗ₕ y, opTensor a.val b.val (x ⊗ₕ y)⟫ = ⟪x, a.val x⟫ * ⟪y, b.val y⟫
    rw [opTensor_apply, htmul_inner]

end Spatial

/-! ### Transport of a tensor product along nmiu-isomorphisms (for 111XII) -/

section Transport

/-- Transfer of a least upper bound along an order isomorphism. -/
theorem isLUB_image_of_orderIso {X Y : Type*} [Preorder X] [Preorder Y]
    (ψ : X → Y) (hmono : ∀ x y, ψ x ≤ ψ y ↔ x ≤ y)
    (hsurj : Function.Surjective ψ) {E : Set X} {e : X} (h : IsLUB E e) :
    IsLUB (ψ '' E) (ψ e) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact (hmono x e).mpr (h.1 hx)
  · intro u hu
    obtain ⟨v, rfl⟩ := hsurj u
    exact (hmono e v).mpr (h.2 fun x hx => (hmono x v).mp (hu ⟨x, hx, rfl⟩))

variable {A₂ : Type u₁} {B₂ : Type u₂}
  [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [CStarAlgebra B₂] [PartialOrder B₂] [StarOrderedRing B₂]

/-- A ∗-homomorphism between C*-algebras is positive: `a = (√a)*√a`.
(The universe-polymorphic form of `starAlgHom_nonneg`, which `A/VN` states
for two algebras in the *same* universe.) -/
theorem starAlgHom_nonneg' (φ : A₂ →⋆ₐ[ℂ] B₂) {a : A₂} (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hsa : IsSelfAdjoint (CFC.sqrt a) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have h : a = star (CFC.sqrt a) * CFC.sqrt a := by
    rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self a ha]
  rw [h, map_mul, map_star]
  exact star_mul_self_nonneg _

/-- The universe-polymorphic form of `starAlgHom_mono`. -/
theorem starAlgHom_mono' (φ : A₂ →⋆ₐ[ℂ] B₂) {x y : A₂} (h : x ≤ y) : φ x ≤ φ y := by
  have h0 := starAlgHom_nonneg' φ (sub_nonneg.mpr h)
  rw [map_sub] at h0
  exact sub_nonneg.mp h0

/-- A ∗-isomorphism is an order isomorphism. -/
theorem starAlgEquiv_le_iff (Φ : A₂ ≃⋆ₐ[ℂ] B₂) (x y : A₂) : Φ x ≤ Φ y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => starAlgHom_mono' Φ.toStarAlgHom h⟩
  have h' : Φ.symm (Φ x) ≤ Φ.symm (Φ y) := starAlgHom_mono' Φ.symm.toStarAlgHom h
  rwa [Φ.symm_apply_apply, Φ.symm_apply_apply] at h'

/-- The universe-polymorphic form of `starAlgEquiv_preservesDirSups`. -/
theorem starAlgEquiv_preservesDirSups' (Φ : A₂ ≃⋆ₐ[ℂ] B₂) : PreservesDirSups ⇑Φ := by
  intro D s hne hdir hlub
  have h := isLUB_image_of_orderIso ⇑Φ (starAlgEquiv_le_iff Φ) Φ.surjective
    (isLUB_coe_of_isLUB hne hlub)
  rw [← Set.image_comp] at h
  exact h

/-- A von Neumann subalgebra is carried to one by a ∗-isomorphism. -/
theorem isVNSubalgebra_map [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    (Φ : A₂ ≃⋆ₐ[ℂ] B₂) (S : StarSubalgebra ℂ A₂) (hS : IsVNSubalgebra A₂ S) :
    IsVNSubalgebra B₂ (S.map Φ.toStarAlgHom) := by
  have hmem : ∀ y : B₂, y ∈ S.map Φ.toStarAlgHom ↔ Φ.symm y ∈ S := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Φ.symm (Φ x) ∈ S
      rwa [Φ.symm_apply_apply]
    · intro hy
      refine ⟨Φ.symm y, hy, ?_⟩
      show Φ (Φ.symm y) = y
      rw [Φ.apply_symm_apply]
  have hsa : ∀ d : selfAdjoint B₂, IsSelfAdjoint (Φ.symm (d : B₂)) := by
    intro d
    show star (Φ.symm (d : B₂)) = Φ.symm (d : B₂)
    rw [← map_star Φ.symm]
    exact congrArg (fun z : B₂ => Φ.symm z) d.2.star_eq
  refine ⟨?_, ?_⟩
  · have hset : (S.map Φ.toStarAlgHom : Set B₂) = ⇑Φ.symm ⁻¹' (S : Set A₂) := by
      ext y
      exact hmem y
    rw [hset]
    exact hS.isClosed.preimage
      (NonUnitalStarAlgHom.isometry Φ.symm.toStarAlgHom Φ.symm.injective).continuous
  · intro D s hDsub hne hdir hlub
    rw [hmem]
    refine hS.dirSup_mem ((fun d : selfAdjoint B₂ => (⟨Φ.symm (d : B₂), hsa d⟩ :
      selfAdjoint A₂)) '' D) ⟨Φ.symm (s : B₂), hsa s⟩ ?_ (hne.image _) ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact (hmem (d : B₂)).mp (hDsub d hd)
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
      obtain ⟨f, hf, hdf, hef⟩ := hdir d hd e he
      exact ⟨⟨Φ.symm (f : B₂), hsa f⟩, ⟨f, hf, rfl⟩,
        (starAlgEquiv_le_iff Φ.symm _ _).mpr hdf,
        (starAlgEquiv_le_iff Φ.symm _ _).mpr hef⟩
    · refine isLUB_sa_of_isLUB ?_
      have h := isLUB_image_of_orderIso ⇑Φ.symm (starAlgEquiv_le_iff Φ.symm)
        Φ.symm.surjective (isLUB_coe_of_isLUB hne hlub)
      rw [← Set.image_comp] at h
      rw [← Set.image_comp]
      exact h

/-- The inverse of a bijective nmiu-map is again an nmiu-map: it is a
∗-isomorphism, hence an order isomorphism (**48VI**.2), and an order
isomorphism transports suprema. -/
noncomputable def nmiuSymm [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    (φ : NMIUMap A₂ B₂) (hφ : Function.Bijective ⇑φ) : NMIUMap B₂ A₂ where
  toStarAlgHom := (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).symm.toStarAlgHom
  preservesDirSups' :=
    starAlgEquiv_preservesDirSups' (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).symm

@[simp] theorem nmiuSymm_apply_apply [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    (φ : NMIUMap A₂ B₂) (hφ : Function.Bijective ⇑φ) (a : A₂) :
    nmiuSymm φ hφ (φ a) = a :=
  (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).symm_apply_apply a

/-- An nmiu-map as a plain `ℂ`-linear map. -/
def nmiuLin (f : NMIUMap A₂ B₂) : A₂ →ₗ[ℂ] B₂ where
  toFun := f
  map_add' := map_add f.toStarAlgHom
  map_smul' := map_smul f.toStarAlgHom

@[simp] theorem nmiuLin_apply (f : NMIUMap A₂ B₂) (a : A₂) : nmiuLin f a = f a := rfl

variable {A₃ : Type u₃} {B₃ : Type u₄} {T₂ : Type u₅}
  [CStarAlgebra A₃] [PartialOrder A₃] [StarOrderedRing A₃]
  [CStarAlgebra B₃] [PartialOrder B₃] [StarOrderedRing B₃]
  [CStarAlgebra T₂] [PartialOrder T₂] [StarOrderedRing T₂]

/-- A tensor product transports along nmiu-isomorphisms of the two factors:
if `γ : 𝒜' × ℬ' → 𝒯` is a tensor product and `φ : 𝒜 ≅ 𝒜'`, `ψ : ℬ ≅ ℬ'` are
nmiu-isomorphisms, then `(a,b) ↦ γ(φa, ψb)` is a tensor product of `𝒜` and
`ℬ`.  (This is what turns the *spatial* tensor product 111VII into the
abstract existence statement **111XII**.) -/
theorem isTensorProduct_comp [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    [VonNeumannAlgebra A₃] [VonNeumannAlgebra B₃] [VonNeumannAlgebra T₂]
    (φ : NMIUMap A₂ A₃) (hφ : Function.Bijective ⇑φ)
    (ψ : NMIUMap B₂ B₃) (hψ : Function.Bijective ⇑ψ)
    {γ : A₃ →ₗ[ℂ] B₃ →ₗ[ℂ] T₂} (hγ : IsTensorProduct γ) :
    IsTensorProduct (γ.compl₁₂ (nmiuLin φ) (nmiuLin ψ)) := by
  have hφP : PreservesDirSups ⇑(nmiuP φ) := φ.preservesDirSups'
  have hψP : PreservesDirSups ⇑(nmiuP ψ) := ψ.preservesDirSups'
  have happ : ∀ (a : A₂) (b : B₂),
      (γ.compl₁₂ (nmiuLin φ) (nmiuLin ψ)) a b = γ (φ a) (ψ b) := fun _ _ => rfl
  have hφ1 : φ (1 : A₂) = 1 := map_one φ.toStarAlgHom
  have hψ1 : ψ (1 : B₂) = 1 := map_one ψ.toStarAlgHom
  have hφmul : ∀ a a' : A₂, φ (a * a') = φ a * φ a' := map_mul φ.toStarAlgHom
  have hψmul : ∀ b b' : B₂, ψ (b * b') = ψ b * ψ b' := map_mul ψ.toStarAlgHom
  have hφstar : ∀ a : A₂, φ (star a) = star (φ a) := map_star φ.toStarAlgHom
  have hψstar : ∀ b : B₂, ψ (star b) = star (ψ b) := map_star ψ.toStarAlgHom
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show (γ.compl₁₂ (nmiuLin φ) (nmiuLin ψ)) 1 1 = 1
    rw [happ, hφ1, hψ1]
    exact hγ.miu.1
  · intro a b c d
    rw [happ, happ, happ, hφmul, hψmul]
    exact hγ.miu.2.1 _ _ _ _
  · intro a b
    rw [happ, happ, hφstar, hψstar]
    exact hγ.miu.2.2 _ _
  · have hset : {t : T₂ | ∃ (a : A₂) (b : B₂),
        t = (γ.compl₁₂ (nmiuLin φ) (nmiuLin ψ)) a b} = {t : T₂ | ∃ a b, t = γ a b} := by
      ext t
      constructor
      · rintro ⟨a, b, rfl⟩
        exact ⟨φ a, ψ b, rfl⟩
      · rintro ⟨a', b', rfl⟩
        obtain ⟨a, rfl⟩ := hφ.2 a'
        obtain ⟨b, rfl⟩ := hψ.2 b'
        exact ⟨a, b, rfl⟩
    rw [hset]
    exact hγ.dense
  · intro σ τ
    obtain ⟨h, hh⟩ := hγ.prod_exists
      (compNP (nmiuP (nmiuSymm φ hφ)) (nmiuSymm φ hφ).preservesDirSups' σ)
      (compNP (nmiuP (nmiuSymm ψ hψ)) (nmiuSymm ψ hψ).preservesDirSups' τ)
    refine ⟨h, fun a b => ?_⟩
    rw [happ, hh (φ a) (ψ b)]
    show σ (nmiuSymm φ hφ (φ a)) * τ (nmiuSymm ψ hψ (ψ b)) = σ a * τ b
    rw [nmiuSymm_apply_apply φ hφ a, nmiuSymm_apply_apply ψ hψ b]
  · intro t ht hfaith
    refine hγ.faithful t ht fun σ₃ τ₃ h hcompat => ?_
    refine hfaith (compNP (nmiuP φ) hφP σ₃) (compNP (nmiuP ψ) hψP τ₃) h fun a b => ?_
    rw [happ, hcompat (φ a) (ψ b)]
    rfl

/-- An nmiu-map `f : 𝒜 → ℬ` whose image is a von Neumann subalgebra `S`
corestricts to an nmiu-map into the bundled algebra `VNSub ℬ S`. -/
noncomputable def nmiuCorestrict [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    (f : NMIUMap A₂ B₂) (S : StarSubalgebra ℂ B₂) (hS : IsVNSubalgebra B₂ S)
    (hmem : ∀ a, f a ∈ S) : NMIUMap A₂ (VNSub B₂ S hS) where
  toStarAlgHom :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := VNSub.val_injective (map_one f.toStarAlgHom)
      map_mul' := fun a a' => VNSub.val_injective (map_mul f.toStarAlgHom a a')
      map_zero' := VNSub.val_injective (map_zero f.toStarAlgHom)
      map_add' := fun a a' => VNSub.val_injective (map_add f.toStarAlgHom a a')
      commutes' := fun r => VNSub.val_injective (by
        show f (algebraMap ℂ A₂ r) = (algebraMap ℂ (VNSub B₂ S hS) r).val
        have halg : (algebraMap ℂ (VNSub B₂ S hS) r).val = algebraMap ℂ B₂ r := by
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
          rfl
        rw [halg]
        exact f.toStarAlgHom.commutes r)
      map_star' := fun a => VNSub.val_injective (map_star f.toStarAlgHom a) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hfn := f.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact hfn.1 ⟨d, hd, rfl⟩
    · intro u hu
      exact hfn.2 (by rintro _ ⟨d, hd, rfl⟩; exact hu ⟨d, hd, rfl⟩)

@[simp] theorem nmiuCorestrict_val [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    (f : NMIUMap A₂ B₂) (S : StarSubalgebra ℂ B₂) (hS : IsVNSubalgebra B₂ S)
    (hmem : ∀ a, f a ∈ S) (a : A₂) : (nmiuCorestrict f S hS hmem a).val = f a := rfl

theorem nmiuCorestrict_bijective [VonNeumannAlgebra A₂] [VonNeumannAlgebra B₂]
    (f : NMIUMap A₂ B₂) (S : StarSubalgebra ℂ B₂) (hS : IsVNSubalgebra B₂ S)
    (hmem : ∀ a, f a ∈ S) (hinj : Function.Injective ⇑f)
    (hsurj : ∀ s ∈ S, ∃ a, f a = s) :
    Function.Bijective ⇑(nmiuCorestrict f S hS hmem) := by
  constructor
  · intro a a' h
    exact hinj (congrArg VNSub.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := hsurj x hx
    exact ⟨a, VNSub.val_injective ha⟩

end Transport

/-! ### Universe-polymorphic infrastructure for nmiu-maps

These are the pieces the *universe-polymorphic* `tmap` of 119V needs
(`exists_tmapM`), where the four algebras `𝒜, ℬ, 𝒞, 𝒟` live in four
independent universes and so `𝒜 ⊗ ℬ` and `𝒞 ⊗ 𝒟` do too.  None of the
parsec-1120/1130/1140 machinery is re-universed: instead the four algebras
and the two tensor products are *lifted* into one common universe
(`exists_vnLift`, from `ngns_ulift`), where the single-universe development
applies verbatim, and the result is transported back.  The only genuinely
cross-universe ingredients are here — and the two A/VN lemmas they need,
**44XV** `p_uwcont` and `compNP`, are already universe-polymorphic in
`A/VN/Basic.lean` (they sit in a `variable {A B : Type*}` section), so no
A/VN twin is required. -/

section NmiuAux

variable {X : Type p} {Y : Type q} {Z : Type r}
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
  [CStarAlgebra Z] [PartialOrder Z] [StarOrderedRing Z]

/-- Composition of nmiu-maps. -/
def nmiuComp (g : NMIUMap Y Z) (f : NMIUMap X Y) : NMIUMap X Z where
  toStarAlgHom := g.toStarAlgHom.comp f.toStarAlgHom
  preservesDirSups' := by
    refine preservesDirSups_comp (f := ⇑f) (g := ⇑g) (fun x hx => ?_)
      (fun _ _ h => starAlgHom_mono' f.toStarAlgHom h)
      f.preservesDirSups' g.preservesDirSups'
    show IsSelfAdjoint (f.toStarAlgHom x)
    rw [IsSelfAdjoint, ← map_star, hx.star_eq]

@[simp] theorem nmiuComp_apply (g : NMIUMap Y Z) (f : NMIUMap X Y) (x : X) :
    nmiuComp g f x = g (f x) := rfl

/-- The companion of `nmiuSymm_apply_apply` on the other side. -/
theorem nmiuSymm_apply_apply' [VonNeumannAlgebra X] [VonNeumannAlgebra Y]
    (φ : NMIUMap X Y) (hφ : Function.Bijective ⇑φ) (b : Y) :
    φ (nmiuSymm φ hφ b) = b :=
  (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).apply_symm_apply b

variable (X) in
/-- The identity nmiu-map (infrastructure for 119IVb/119IVc/119V).  Moved
here from the 119V block so that the universe-lifting device of
`exists_vnt_transfer` can use it as the identity transport. -/
noncomputable def nmiuId [VonNeumannAlgebra X] : NMIUMap X X :=
  { toStarAlgHom := StarAlgHom.id ℂ X
    preservesDirSups' := preservesDirSups_id }

@[simp] theorem nmiuId_apply [VonNeumannAlgebra X] (x : X) : nmiuId X x = x := rfl

theorem nmiuId_bijective [VonNeumannAlgebra X] :
    Function.Bijective ⇑(nmiuId X) :=
  ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩

theorem nmiuSymm_bijective [VonNeumannAlgebra X] [VonNeumannAlgebra Y]
    (φ : NMIUMap X Y) (hφ : Function.Bijective ⇑φ) :
    Function.Bijective ⇑(nmiuSymm φ hφ) :=
  ⟨fun x y h => by
      have := congrArg (fun z => φ z) h
      simpa [nmiuSymm_apply_apply'] using this,
    fun x => ⟨φ x, nmiuSymm_apply_apply φ hφ x⟩⟩

/-- An nmiu-map is completely positive in the sense of cstar.tex **10II**:
it takes `star (a i) * a j` to `star (f (a i)) * f (a j)`, so the defining
sum is `star z * z`. -/
theorem nmiuLin_cp (f : NMIUMap X Y) :
    Theses.A.CStar.IsCompletelyPositiveMap (nmiuLin f) := by
  have hm : ∀ x y : X, f (x * y) = f x * f y := map_mul f.toStarAlgHom
  have hs : ∀ x : X, f (star x) = star (f x) := map_star f.toStarAlgHom
  intro n a c
  have he : ∑ i, ∑ j, star (c i) * (nmiuLin f) (star (a i) * a j) * c j
      = star (∑ i, f (a i) * c i) * ∑ j, f (a j) * c j := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (c i) * (f (star (a i) * a j)) * c j
      = star (f (a i) * c i) * (f (a j) * c j)
    rw [hm, hs, star_mul]
    noncomm_ring
  rw [he]
  exact star_mul_self_nonneg _

/-- An nmiu-map as an ncp-map. -/
def nmiuNCP (f : NMIUMap X Y) : NCPMap X Y where
  toCompletelyPositiveMap :=
    { toLinearMap := nmiuLin f
      map_cstarMatrix_nonneg' := by
        have h : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) X), 0 ≤ M →
            0 ≤ M.map ⇑(nmiuLin f) :=
          (Theses.A.CStar.cp_iff (nmiuLin f)).out 0 1 |>.mp (nmiuLin_cp f)
        exact h }
  preservesDirSups' := f.preservesDirSups'

@[simp] theorem nmiuNCP_apply (f : NMIUMap X Y) (x : X) : nmiuNCP f x = f x := rfl

end NmiuAux

section TensorTransfer

variable {Xa : Type p} {Xb : Type q} {Xt : Type r} {Xt' : Type s}
  [CStarAlgebra Xa] [PartialOrder Xa] [StarOrderedRing Xa] [VonNeumannAlgebra Xa]
  [CStarAlgebra Xb] [PartialOrder Xb] [StarOrderedRing Xb] [VonNeumannAlgebra Xb]
  [CStarAlgebra Xt] [PartialOrder Xt] [StarOrderedRing Xt] [VonNeumannAlgebra Xt]
  [CStarAlgebra Xt'] [PartialOrder Xt'] [StarOrderedRing Xt']
  [VonNeumannAlgebra Xt']

/-- An nmiu-map is ultraweakly continuous (**44XV** `p_uwcont`, which is
already universe-polymorphic in `A/VN/Basic.lean`). -/
theorem nmiu_uwContinuous (f : NMIUMap Xt Xt') :
    @Continuous Xt Xt' (ultraweak Xt) (ultraweak Xt') ⇑f :=
  ((p_uwcont (nmiuP f)).out 2 0).mp f.preservesDirSups'

set_option linter.unusedSectionVars false in
/-- A tensor product transports along an nmiu-isomorphism of the *target*:
if `γ : 𝒜 × ℬ → 𝒯` is a tensor product and `ℓ : 𝒯 ≅ 𝒯'` is an
nmiu-isomorphism, then `ℓ ∘ γ` is a tensor product of `𝒜` and `ℬ`.  (The
companion of `isTensorProduct_comp`, which transports along isomorphisms of
the two *factors*; unlike that one this moves the tensor product itself to
another universe, which is what makes `exists_tmapM` possible.) -/
theorem isTensorProduct_comp_target {γ : Xa →ₗ[ℂ] Xb →ₗ[ℂ] Xt}
    (hγ : IsTensorProduct γ) (ℓ : NMIUMap Xt Xt')
    (hℓ : Function.Bijective ⇑ℓ) :
    IsTensorProduct (γ.compr₂ (nmiuLin ℓ)) := by
  have happ : ∀ (a : Xa) (b : Xb), (γ.compr₂ (nmiuLin ℓ)) a b = ℓ (γ a b) :=
    fun _ _ => rfl
  have hℓ1 : ℓ (1 : Xt) = 1 := map_one ℓ.toStarAlgHom
  have hℓmul : ∀ x y : Xt, ℓ (x * y) = ℓ x * ℓ y := map_mul ℓ.toStarAlgHom
  have hℓstar : ∀ x : Xt, ℓ (star x) = star (ℓ x) := map_star ℓ.toStarAlgHom
  set g := nmiuSymm ℓ hℓ with hg
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show (γ.compr₂ (nmiuLin ℓ)) 1 1 = 1
    rw [happ, hγ.miu.1, hℓ1]
  · intro a b c d
    rw [happ, happ, happ, hγ.miu.2.1, hℓmul]
  · intro a b
    rw [happ, happ, ← hγ.miu.2.2, hℓstar]
  · -- density: `ℓ` is an ultraweak homeomorphism
    let _ : TopologicalSpace Xt := ultraweak Xt
    let _ : TopologicalSpace Xt' := ultraweak Xt'
    have hset : {t : Xt' | ∃ a b, t = (γ.compr₂ (nmiuLin ℓ)) a b}
        = ⇑(nmiuLin ℓ) '' {t : Xt | ∃ a b, t = γ a b} := by
      ext t
      constructor
      · rintro ⟨a, b, rfl⟩; exact ⟨γ a b, ⟨a, b, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, b, rfl⟩, rfl⟩; exact ⟨a, b, rfl⟩
    have hspan : (Submodule.span ℂ
          {t : Xt' | ∃ a b, t = (γ.compr₂ (nmiuLin ℓ)) a b} : Set Xt')
        = ⇑(nmiuLin ℓ) ''
          (Submodule.span ℂ {t : Xt | ∃ a b, t = γ a b} : Set Xt) := by
      rw [hset, ← Submodule.map_span, Submodule.map_coe]
    rw [hspan]
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    rw [← Set.image_univ_of_surjective (f := ⇑(nmiuLin ℓ)) hℓ.2,
      ← dense_iff_closure_eq.mp hγ.dense]
    exact image_closure_subset_closure_image (nmiu_uwContinuous ℓ)
  · intro σ τ
    obtain ⟨h, hh⟩ := hγ.prod_exists σ τ
    refine ⟨compNP (nmiuP g) g.preservesDirSups' h, fun a b => ?_⟩
    show h (g (ℓ (γ a b))) = σ a * τ b
    rw [hg, nmiuSymm_apply_apply ℓ hℓ]
    exact hh a b
  · intro t ht hfaith
    have ht0 : (0 : Xt) ≤ g t := starAlgHom_nonneg' g.toStarAlgHom ht
    have hgt : g t = 0 := by
      refine hγ.faithful (g t) ht0 fun σ τ h hcompat => ?_
      exact hfaith σ τ (compNP (nmiuP g) g.preservesDirSups' h)
        (fun a b => by
          show h (g (ℓ (γ a b))) = σ a * τ b
          rw [hg, nmiuSymm_apply_apply ℓ hℓ]
          exact hcompat a b)
    have hlt := nmiuSymm_apply_apply' ℓ hℓ t
    rw [← hlt, ← hg, hgt]
    exact map_zero ℓ.toStarAlgHom

end TensorTransfer

/-! ### Universe-lifting a Hilbert space

The bundled form of 111XII has its two algebras in *different* universes `u`
and `v`, while the spatial construction needs both Hilbert spaces in one
universe; `ULift` supplies the common refinement `max u v`. -/

section ULiftHilbert

variable {H₀ : Type u₁} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]

instance : InnerProductSpace ℂ (ULift.{u₂} H₀) :=
  { ULift.normedSpace with
    inner := fun x y => ⟪x.down, y.down⟫
    norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner (𝕜 := ℂ) x.down
    conj_inner_symm := fun x y => inner_conj_symm (𝕜 := ℂ) x.down y.down
    add_left := fun x y z => inner_add_left (𝕜 := ℂ) x.down y.down z.down
    smul_left := fun x y r => inner_smul_left (𝕜 := ℂ) x.down y.down (r := r) }

/-- The canonical isometric isomorphism `ULift ℋ ≃ ℋ`. -/
def uliftIsometry : ULift.{u₂} H₀ ≃ₗᵢ[ℂ] H₀ where
  toLinearEquiv := ULift.moduleEquiv
  norm_map' _ := rfl

end ULiftHilbert

/-- **48VIII** `ngns` with the representing Hilbert space lifted into
`Type (max u₁ u₂)`: every von Neumann algebra `𝒜 : Type u₁` is
nmiu-isomorphic to a von Neumann subalgebra of `B(ULift ℓ²(ι))`. -/
theorem ngns_ulift (A₄ : Type u₁) [CStarAlgebra A₄] [PartialOrder A₄]
    [StarOrderedRing A₄] [VonNeumannAlgebra A₄] :
    ∃ (ι : Type u₁)
      (f : NMIUMap A₄ (ULift.{u₂} (lp (fun _ : ι => ℂ) 2) →L[ℂ]
        ULift.{u₂} (lp (fun _ : ι => ℂ) 2)))
      (S : StarSubalgebra ℂ (ULift.{u₂} (lp (fun _ : ι => ℂ) 2) →L[ℂ]
        ULift.{u₂} (lp (fun _ : ι => ℂ) 2)))
      (hS : IsVNSubalgebra _ S),
      (∀ a, f a ∈ S) ∧ (∀ s ∈ S, ∃ a, f a = s) ∧ Function.Injective ⇑f := by
  obtain ⟨ι, f₀, hinj, hR⟩ := ngns A₄
  set Φ : ((lp (fun _ : ι => ℂ) 2) →L[ℂ] (lp (fun _ : ι => ℂ) 2)) ≃⋆ₐ[ℂ]
      (ULift.{u₂} (lp (fun _ : ι => ℂ) 2) →L[ℂ] ULift.{u₂} (lp (fun _ : ι => ℂ) 2)) :=
    (uliftIsometry (H₀ := lp (fun _ : ι => ℂ) 2)).symm.conjStarAlgEquiv with hΦ
  refine ⟨ι, ⟨Φ.toStarAlgHom.comp f₀.toStarAlgHom, ?_⟩,
    (f₀.toStarAlgHom.range).map Φ.toStarAlgHom, isVNSubalgebra_map Φ _ hR,
    fun a => ⟨f₀ a, ⟨a, rfl⟩, rfl⟩, ?_, ?_⟩
  · intro D s hne hdir hlub
    have h1 := f₀.preservesDirSups' D s hne hdir hlub
    have h2 := isLUB_image_of_orderIso ⇑Φ (starAlgEquiv_le_iff Φ) Φ.surjective h1
    rw [← Set.image_comp] at h2
    exact h2
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · intro a a' h
    exact hinj (Φ.injective h)

/-- Universe lift: every von Neumann algebra `𝒳 : Type p` is
nmiu-isomorphic to one living in `Type (max p q)` — by **48VIII** `ngns`
with the representing Hilbert space lifted (`ngns_ulift`) and the image
bundled as a `VNSub`.  This is what lets the four-universe `tmap`
(`exists_tmapM`) be reduced to the single-universe one. -/
theorem exists_vnLift (𝒳 : Type p) [CStarAlgebra 𝒳] [PartialOrder 𝒳]
    [StarOrderedRing 𝒳] [VonNeumannAlgebra 𝒳] :
    ∃ (X' : Type (max p q)) (_ : CStarAlgebra X') (_ : PartialOrder X')
      (_ : StarOrderedRing X') (_ : VonNeumannAlgebra X') (ε : NMIUMap 𝒳 X'),
      Function.Bijective ⇑ε := by
  obtain ⟨ι, f, S, hS, hmem, hsurj, hinj⟩ := ngns_ulift.{p, q} 𝒳
  exact ⟨VNSub _ S hS, inferInstance, inferInstance, inferInstance, inferInstance,
    nmiuCorestrict f S hS hmem,
    nmiuCorestrict_bijective f S hS hmem hinj hsurj⟩

/-- **111XII** (proc.tex:2583, Exercise): every pair of (abstract) von
Neumann algebras has a tensor product (via the normal Gelfand–Naimark
representation, vn.tex 48VIII, and 111VII). -/
theorem vnTensorProduct_exists [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    ∃ (T : Type u) (_ : CStarAlgebra T) (_ : PartialOrder T)
      (_ : StarOrderedRing T) (_ : VonNeumannAlgebra T)
      (γ : A →ₗ[ℂ] B →ₗ[ℂ] T), IsTensorProduct γ := by
  obtain ⟨ι, f, hfinj, hfR⟩ := ngns A
  obtain ⟨κ, g, hginj, hgR⟩ := ngns B
  obtain ⟨γ₀, -, hγ₀⟩ := special_tensor f.toStarAlgHom.range g.toStarAlgHom.range hfR hgR
  have hfmem : ∀ a, f a ∈ f.toStarAlgHom.range := fun a => ⟨a, rfl⟩
  have hgmem : ∀ b, g b ∈ g.toStarAlgHom.range := fun b => ⟨b, rfl⟩
  exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
    γ₀.compl₁₂ (nmiuLin (nmiuCorestrict f _ hfR hfmem))
      (nmiuLin (nmiuCorestrict g _ hgR hgmem)),
    isTensorProduct_comp _
      (nmiuCorestrict_bijective f _ hfR hfmem hfinj (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)) _
      (nmiuCorestrict_bijective g _ hgR hgmem hginj (by rintro _ ⟨b, rfl⟩; exact ⟨b, rfl⟩))
      hγ₀⟩

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

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B]
  [StarOrderedRing B] in
/-- Auxiliary for **112III**: every element of `𝒜 ⊙ ℬ` is a finite sum
`∑ᵢ aᵢ ⊙ bᵢ` indexed by a `Fin N` (the form the author's proof writes it
in).  Mathlib's `TensorProduct.exists_finset` gives a `Finset`; this
reindexes it. -/
private theorem exists_fin_repr (t : A ⊗[ℂ] B) :
    ∃ (N : ℕ) (a : Fin N → A) (b : Fin N → B), t = ∑ i, a i ⊗ₜ[ℂ] b i := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  refine ⟨S.card, fun i => ((S.equivFin.symm i : A × B)).1,
          fun i => ((S.equivFin.symm i : A × B)).2, ?_⟩
  rw [hS, ← Finset.sum_coe_sort S (fun p => p.1 ⊗ₜ[ℂ] p.2)]
  exact (Fintype.sum_equiv S.equivFin.symm _ _ (fun i => rfl)).symm

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B]
  [StarOrderedRing B] in
/-- Auxiliary for **112VI**: the author's "by replacing them if necessary
we may assume that `a₁, …, a_N` are linearly independent".  Made precise
by expanding the `aᵢ` in a basis `E` of their (finite-dimensional) span
and collecting the coefficients on the `ℬ`-side. -/
private theorem exists_indep_repr (t : A ⊗[ℂ] B) :
    ∃ (N : ℕ) (a : Fin N → A) (b : Fin N → B),
      LinearIndependent ℂ a ∧ t = ∑ i, a i ⊗ₜ[ℂ] b i := by
  obtain ⟨M, a₀, b₀, rfl⟩ := exists_fin_repr t
  set V : Submodule ℂ A := Submodule.span ℂ (Set.range a₀) with hV
  have : Module.Finite ℂ V := Module.Finite.span_of_finite ℂ (Set.finite_range a₀)
  set e : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V with he
  set E : Fin (Module.finrank ℂ V) → A := fun j => (e j : A) with hE
  have hEind : LinearIndependent ℂ E :=
    e.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hmem : ∀ i, a₀ i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  set c : Fin M → Fin (Module.finrank ℂ V) → ℂ :=
    fun i j => e.repr ⟨a₀ i, hmem i⟩ j with hc
  have hrep : ∀ i, a₀ i = ∑ j, c i j • E j := by
    intro i
    have h := congrArg (Submodule.subtype V) (e.sum_repr ⟨a₀ i, hmem i⟩)
    simp only [map_sum, map_smul, Submodule.coe_subtype] at h
    exact h.symm
  refine ⟨_, E, fun j => ∑ i, c i j • b₀ i, hEind, ?_⟩
  calc ∑ i, a₀ i ⊗ₜ[ℂ] b₀ i
      = ∑ i, ∑ j, E j ⊗ₜ[ℂ] (c i j • b₀ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hrep i, TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
    _ = ∑ j, ∑ i, E j ⊗ₜ[ℂ] (c i j • b₀ i) := Finset.sum_comm
    _ = ∑ j, E j ⊗ₜ[ℂ] (∑ i, c i j • b₀ i) :=
        Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_sum _ _ _).symm

/-- Auxiliary for **112III**: for a positive functional `σ` on a
C*-algebra the matrix `(σ(aᵢ* aⱼ))ᵢⱼ` is positive.  This is the step the
author justifies by `cp-commutative` (**34IX**): `σ` is completely
positive because `ℂ` is commutative, and complete positivity in the form
`Theses.A.CStar.IsCompletelyPositiveMap` *is* the statement that the
quadratic form of that matrix is nonnegative. -/
private theorem posMap_gram_posSemidef (σ : A →ₚ[ℂ] ℂ) {N : ℕ}
    (a : Fin N → A) :
    (Matrix.of fun i j : Fin N => σ (star (a i) * a j)).PosSemidef := by
  have hpos : Theses.A.CStar.IsPositiveMap σ.toLinearMap :=
    fun x hx => σ.map_nonneg hx
  have hcp : Theses.A.CStar.IsCompletelyPositiveMap σ.toLinearMap :=
    Theses.A.CStar.cp_commutative_cod _ hpos
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun z => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    have h : σ.toLinearMap (star (star (a j) * a i))
        = star (σ.toLinearMap (star (a j) * a i)) :=
      Theses.A.CStar.cstar_p_implies_i σ.toLinearMap hpos _
    rw [star_mul, star_star] at h
    exact h.symm
  · rw [quadForm_eq]
    simpa using hcp N a z

/-- Auxiliary for **112V**: `σ ⊙ τ` is involution preserving when `σ` and
`τ` are (**10IV**, `cstar-p-implies-i`). -/
private theorem odotF_star (σ : A →ₚ[ℂ] ℂ) (τ : B →ₚ[ℂ] ℂ)
    (y : A ⊗[ℂ] B) :
    odotF σ.toLinearMap τ.toLinearMap (star y)
      = starRingEnd ℂ (odotF σ.toLinearMap τ.toLinearMap y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
      have hσ := Theses.A.CStar.cstar_p_implies_i σ.toLinearMap
        (fun u hu => σ.map_nonneg hu) x
      have hτ := Theses.A.CStar.cstar_p_implies_i τ.toLinearMap
        (fun u hu => τ.map_nonneg hu) z
      simp [odotF, TensorProduct.star_tmul, hσ, hτ]
  | add y z hy hz => simp [star_add, hy, hz]

/-- **112III** (`product-state-positive`, proc.tex:2781, Lemma): for
C*-algebras and positive functionals `σ`, `τ`,
`(σ ⊙ τ)(t* t) ≥ 0` for all `t ∈ 𝒜 ⊙ ℬ`. -/
theorem product_state_positive (σ : A →ₚ[ℂ] ℂ) (τ : B →ₚ[ℂ] ℂ)
    (t : A ⊗[ℂ] B) :
    0 ≤ odotF σ.toLinearMap τ.toLinearMap (star t * t) := by
  -- proc.tex:2789, verbatim: write `t = ∑ₙ aₙ ⊙ bₙ`, so that
  -- `(σ ⊙ τ)(t*t) = ∑_{n,m} σ(aₙ* a_m) τ(bₙ* b_m)`; both matrices are
  -- positive by `cp-commutative`, hence so is their entrywise product by
  -- `schur` (111II), and the sum of the entries of a positive matrix is
  -- nonnegative.
  obtain ⟨N, a, b, rfl⟩ := exists_fin_repr t
  have hexp : star (∑ i, a i ⊗ₜ[ℂ] b i) * (∑ i, a i ⊗ₜ[ℂ] b i)
      = ∑ i, ∑ j, (star (a i) * a j) ⊗ₜ[ℂ] (star (b i) * b j) := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hexp]
  have hsum := sum_entries_nonneg
    (schur N _ _ (posMap_gram_posSemidef σ a) (posMap_gram_posSemidef τ b))
  simp only [Matrix.hadamard_apply, Matrix.of_apply] at hsum
  simpa [odotF] using hsum

/-- **112V** (`basic-state-inner-product`, proc.tex:2808, Exercise): for a
basic functional `ω`, `[s,t]_ω = ω(s* t)` is an inner product (a
positive-semidefinite sesquilinear form): it is conjugate-symmetric and
positive. -/
theorem basic_state_inner_product [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ)
    (hω : IsBasicFunctional ω) :
    (∀ s t : A ⊗[ℂ] B, ω (star t * s) = starRingEnd ℂ (ω (star s * t))) ∧
      ∀ t : A ⊗[ℂ] B, 0 ≤ ω (star t * t) := by
  -- The exercise says "use `product-state-positive`", and that is exactly
  -- what the second half is: `ω(t* t) = (σ ⊙ τ)((t t₀)* (t t₀))`.
  -- Conjugate-symmetry does not need positivity at all — it is
  -- involution-preservation of `σ ⊙ τ` (`odotF_star`) transported along
  -- the ∗-compatible map `x ↦ t₀* x t₀`.
  obtain ⟨σ, τ, t₀, hrep⟩ := hω
  refine ⟨fun s t => ?_, fun t => ?_⟩
  · have hstar : star t * s = star (star s * t) := by rw [star_mul, star_star]
    rw [hstar, hrep, hrep]
    have h : star t₀ * star (star s * t) * t₀
        = star (star t₀ * (star s * t) * t₀) := by simp [star_mul, mul_assoc]
    rw [h]
    exact odotF_star σ.toPositiveLinearMap τ.toPositiveLinearMap _
  · rw [hrep]
    have h := product_state_positive σ.toPositiveLinearMap
      τ.toPositiveLinearMap (t * t₀)
    have heq : star (t * t₀) * (t * t₀) = star t₀ * (star t * t) * t₀ := by
      simp [star_mul, mul_assoc]
    rwa [heq] at h

/-- **112VI** (proc.tex:2815, Lemma): product functionals formed from
separating collections `Ω`, `Ξ` of linear functionals on C*-algebras are
separating: if `(σ ⊙ τ)(t) = 0` for all `σ ∈ Ω`, `τ ∈ Ξ`, then
`t = 0`. -/
theorem product_functionals_separating (Ω : Set (A →ₗ[ℂ] ℂ))
    (Ξ : Set (B →ₗ[ℂ] ℂ))
    (hΩ : ∀ a : A, (∀ σ ∈ Ω, σ a = 0) → a = 0)
    (hΞ : ∀ b : B, (∀ τ ∈ Ξ, τ b = 0) → b = 0) (t : A ⊗[ℂ] B)
    (h : ∀ σ ∈ Ω, ∀ τ ∈ Ξ, odotF σ τ t = 0) : t = 0 := by
  -- proc.tex:2833, verbatim: write `t = ∑ₙ aₙ ⊙ bₙ` with the `aₙ` linearly
  -- independent; for `τ ∈ Ξ` the element `∑ₙ aₙ τ(bₙ)` is killed by every
  -- `σ ∈ Ω`, hence is `0`, hence every `τ(bₙ)` is `0`; and then every
  -- `bₙ` is `0`, so `t = 0`.
  obtain ⟨N, a, b, hind, rfl⟩ := exists_indep_repr t
  have hb : ∀ j, b j = 0 := by
    intro j
    refine hΞ _ fun τ hτ => ?_
    have key : ∀ σ ∈ Ω, σ (∑ k, τ (b k) • a k) = 0 := by
      intro σ hσ
      have h1 := h σ hσ τ hτ
      simp only [odotF, map_sum, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
        LinearMap.mul_apply'] at h1
      simp only [map_sum, map_smul, smul_eq_mul]
      rw [← h1]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    exact (Fintype.linearIndependent_iff.mp hind) (fun k => τ (b k)) (hΩ _ key) j
  simp [hb]

/-! ### The tensor product seminorms `‖·‖_ω` (auxiliary for **112VIII**)

The tensor product norm of 112II is a supremum of the seminorms
`‖t‖_ω = ω(t* t)^½` over the basic functionals `ω` with `ω(1) ≤ 1`.  By
**112V** each `[s,t]_ω = ω(s* t)` is a positive semidefinite Hermitian
form, so `‖·‖_ω` is exactly the seminorm of Mathlib's
`PreInnerProductSpace.Core` — which is where Cauchy–Schwarz, the
triangle inequality and homogeneity come from. -/

/-- `‖t‖_ω = ω(t* t)^½`, the seminorm attached to a functional on
`𝒜 ⊙ ℬ` (the quantity the tensor product norm of 112II takes the
supremum of). -/
private noncomputable def tsn [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] B) : ℝ :=
  Real.sqrt (ω (star t * t)).re

set_option warn.classDefReducibility false in
/-- The semi-inner-product structure `[s,t]_ω = ω(s* t)` of a basic
functional: this *is* **112V** `basic_state_inner_product`, packaged so
that Mathlib's Cauchy–Schwarz applies. -/
private noncomputable def basicCore [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ}
    (hω : IsBasicFunctional ω) : PreInnerProductSpace.Core ℂ (A ⊗[ℂ] B) where
  inner s t := ω (star s * t)
  conj_inner_symm x y := by
    show (starRingEnd ℂ) (ω (star y * x)) = ω (star x * y)
    rw [(basic_state_inner_product ω hω).1 x y, Complex.conj_conj]
  re_inner_nonneg x := by
    have h := (basic_state_inner_product ω hω).2 x
    simpa using (Complex.le_def.mp h).1
  add_left x y z := by simp [star_add, add_mul]
  smul_left x y r := by simp [star_smul, RCLike.star_def]

omit [StarOrderedRing A] [StarOrderedRing B] in
private theorem tsn_nonneg [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] B) : 0 ≤ tsn ω t :=
  Real.sqrt_nonneg _

/-- Cauchy–Schwarz: `|ω(s* t)| ≤ ‖s‖_ω ‖t‖_ω` for a basic functional. -/
private theorem basic_cauchy_schwarz [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω)
    (s t : A ⊗[ℂ] B) : ‖ω (star s * t)‖ ≤ tsn ω s * tsn ω t := by
  let _c := basicCore hω
  let _ := InnerProductSpace.Core.toPreInner' (𝕜 := ℂ) (F := A ⊗[ℂ] B)
  let _ := InnerProductSpace.Core.toNorm (𝕜 := ℂ) (F := A ⊗[ℂ] B)
  exact InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) s t

private theorem tsn_add_le [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) (s t : A ⊗[ℂ] B) :
    tsn ω (s + t) ≤ tsn ω s + tsn ω t := by
  let _c := basicCore hω
  let _ := InnerProductSpace.Core.toPreInner' (𝕜 := ℂ) (F := A ⊗[ℂ] B)
  let _ := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
    (F := A ⊗[ℂ] B)
  exact norm_add_le s t

private theorem tsn_smul [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) (z : ℂ)
    (t : A ⊗[ℂ] B) : tsn ω (z • t) = ‖z‖ * tsn ω t := by
  let _c := basicCore hω
  let _ := InnerProductSpace.Core.toPreInner' (𝕜 := ℂ) (F := A ⊗[ℂ] B)
  let _ := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
    (F := A ⊗[ℂ] B)
  let _ := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := A ⊗[ℂ] B)
  exact norm_smul z t

private theorem tsn_sum_le [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) {N : ℕ}
    (f : Fin N → A ⊗[ℂ] B) : tsn ω (∑ i, f i) ≤ ∑ i, tsn ω (f i) := by
  let _c := basicCore hω
  let _ := InnerProductSpace.Core.toPreInner' (𝕜 := ℂ) (F := A ⊗[ℂ] B)
  let _ := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
    (F := A ⊗[ℂ] B)
  exact norm_sum_le (E := A ⊗[ℂ] B) Finset.univ f

/-- A basic functional is nonnegative on `x ⊙ y` for positive `x`, `y`:
write `x = u* u`, `y = v* v`, so that `x ⊙ y = (u ⊙ v)* (u ⊙ v)` and
apply **112V**. -/
private theorem basic_nonneg_tmul [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω)
    {x : A} (hx : 0 ≤ x) {y : B} (hy : 0 ≤ y) : 0 ≤ ω (x ⊗ₜ[ℂ] y) := by
  obtain ⟨u, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  obtain ⟨v, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy
  have h : (star u * u) ⊗ₜ[ℂ] (star v * v)
      = star (u ⊗ₜ[ℂ] v) * (u ⊗ₜ[ℂ] v) := by
    rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h]
  exact (basic_state_inner_product ω hω).2 _

private theorem basic_mono_tmul_left [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω)
    {x x' : A} (h : x ≤ x') {y : B} (hy : 0 ≤ y) :
    ω (x ⊗ₜ[ℂ] y) ≤ ω (x' ⊗ₜ[ℂ] y) := by
  have hd := basic_nonneg_tmul hω (sub_nonneg.mpr h) hy
  rw [TensorProduct.sub_tmul, map_sub, sub_nonneg] at hd
  exact hd

private theorem basic_mono_tmul_right [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω)
    {x : A} (hx : 0 ≤ x) {y y' : B} (h : y ≤ y') :
    ω (x ⊗ₜ[ℂ] y) ≤ ω (x ⊗ₜ[ℂ] y') := by
  have hd := basic_nonneg_tmul hω hx (sub_nonneg.mpr h)
  rw [TensorProduct.tmul_sub, map_sub, sub_nonneg] at hd
  exact hd

private theorem basic_one_nonneg [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) : 0 ≤ ω 1 := by
  have := (basic_state_inner_product ω hω).2 1
  simpa using this

/-- `ω(x ⊙ y) ≤ ‖x‖‖y‖ ω(1)` for positive `x`, `y`: apply `x ≤ ‖x‖·1`
and `y ≤ ‖y‖·1` one slot at a time. -/
private theorem basic_tmul_le [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) {x : A} (hx : 0 ≤ x)
    {y : B} (hy : 0 ≤ y) :
    (ω (x ⊗ₜ[ℂ] y)).re ≤ ‖x‖ * ‖y‖ * (ω 1).re := by
  have hx1 : x ≤ ((‖x‖ : ℝ) : ℂ) • (1 : A) := by
    rw [Complex.coe_smul]; exact le_norm_smul_one hx
  have hy1 : y ≤ ((‖y‖ : ℝ) : ℂ) • (1 : B) := by
    rw [Complex.coe_smul]; exact le_norm_smul_one hy
  have h1 := basic_mono_tmul_left hω hx1 hy
  have h2 := basic_mono_tmul_right hω
    (le_trans hx hx1 : (0 : A) ≤ ((‖x‖ : ℝ) : ℂ) • (1 : A)) hy1
  have hstep : ω (x ⊗ₜ[ℂ] y) ≤ (((‖x‖ * ‖y‖ : ℝ)) : ℂ) * ω 1 := by
    refine le_trans h1 (le_trans h2 (le_of_eq ?_))
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul,
      smul_eq_mul, ← Algebra.TensorProduct.one_def]
    push_cast
    ring
  have := (Complex.le_def.mp hstep).1
  simpa using this

/-- `‖a ⊙ b‖_ω ≤ ‖a‖‖b‖` when `ω(1) ≤ 1`. -/
private theorem tsn_tmul_le [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) (h1 : (ω 1).re ≤ 1)
    (a : A) (b : B) : tsn ω (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ := by
  have hstar : star (a ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] b)
      = (star a * a) ⊗ₜ[ℂ] (star b * b) := by
    rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  have hb := basic_tmul_le hω (star_mul_self_nonneg a) (star_mul_self_nonneg b)
  have hna : ‖star a * a‖ = ‖a‖ * ‖a‖ := CStarRing.norm_star_mul_self
  have hnb : ‖star b * b‖ = ‖b‖ * ‖b‖ := CStarRing.norm_star_mul_self
  have h0 : (0 : ℝ) ≤ (ω 1).re := by
    simpa using (Complex.le_def.mp (basic_one_nonneg hω)).1
  have hkey : (ω (star (a ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] b))).re ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [hstar]
    refine hb.trans ?_
    rw [hna, hnb]
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hle : tsn ω (a ⊗ₜ[ℂ] b) ≤ Real.sqrt ((‖a‖ * ‖b‖) ^ 2) :=
    Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (by positivity)] at hle

/-- The set of which the tensor product norm (112II) is the supremum. -/
private def tnSet [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (t : A ⊗[ℂ] B) : Set ℝ :=
  {r : ℝ | ∃ ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ, IsBasicFunctional ω ∧
    (ω 1).re ≤ 1 ∧ r = Real.sqrt (ω (star t * t)).re}

omit [StarOrderedRing A] [StarOrderedRing B] in
private theorem tensorNorm_eq_sSup [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (t : A ⊗[ℂ] B) :
    tensorNorm A B t = sSup (tnSet t) := rfl

omit [StarOrderedRing A] [StarOrderedRing B] in
private theorem tnSet_nonneg [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {t : A ⊗[ℂ] B} {r : ℝ} (hr : r ∈ tnSet t) : 0 ≤ r := by
  obtain ⟨ω, _, _, rfl⟩ := hr
  exact Real.sqrt_nonneg _

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- `0` is always in the set: the zero functional is basic (`t₀ = 0`). -/
private theorem zero_mem_tnSet [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (t : A ⊗[ℂ] B) : (0 : ℝ) ∈ tnSet t :=
  ⟨0, ⟨zeroNP, zeroNP, 0, fun s => by simp⟩, by simp, by simp⟩

/-- The set is bounded above by `∑ᵢ ‖aᵢ‖‖bᵢ‖` for any representation
`t = ∑ᵢ aᵢ ⊙ bᵢ` — this is what makes the supremum meaningful. -/
private theorem tnSet_bddAbove [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (t : A ⊗[ℂ] B) : BddAbove (tnSet t) := by
  obtain ⟨N, a, b, rfl⟩ := exists_fin_repr t
  refine ⟨∑ i, ‖a i‖ * ‖b i‖, ?_⟩
  rintro r ⟨ω, hω, h1, rfl⟩
  calc Real.sqrt (ω (star (∑ i, a i ⊗ₜ[ℂ] b i) * ∑ i, a i ⊗ₜ[ℂ] b i)).re
      = tsn ω (∑ i, a i ⊗ₜ[ℂ] b i) := rfl
    _ ≤ ∑ i, tsn ω (a i ⊗ₜ[ℂ] b i) := tsn_sum_le hω _
    _ ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
        Finset.sum_le_sum fun i _ => tsn_tmul_le hω h1 (a i) (b i)

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- **112VIII**, part 1. -/
theorem tensorNorm_nonneg [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (t : A ⊗[ℂ] B) : 0 ≤ tensorNorm A B t :=
  Real.sSup_nonneg fun _ hx => tnSet_nonneg hx

@[simp] theorem tensorNorm_zero [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    tensorNorm A B (0 : A ⊗[ℂ] B) = 0 := by
  refine le_antisymm (csSup_le ⟨0, zero_mem_tnSet 0⟩ ?_) ?_
  · rintro r ⟨ω, _, _, rfl⟩
    simp
  · exact le_csSup (tnSet_bddAbove 0) (zero_mem_tnSet 0)

private theorem tensorNorm_smul_le [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (z : ℂ) (t : A ⊗[ℂ] B) :
    tensorNorm A B (z • t) ≤ ‖z‖ * tensorNorm A B t := by
  refine csSup_le ⟨0, zero_mem_tnSet _⟩ ?_
  rintro r ⟨ω, hω, h1, rfl⟩
  have h : Real.sqrt (ω (star (z • t) * (z • t))).re = ‖z‖ * tsn ω t :=
    tsn_smul hω z t
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (le_csSup (tnSet_bddAbove t) ⟨ω, hω, h1, rfl⟩) (norm_nonneg z)

/-- **112VIII**, part 3. -/
theorem tensorNorm_smul [VonNeumannAlgebra A] [VonNeumannAlgebra B] (z : ℂ)
    (t : A ⊗[ℂ] B) : tensorNorm A B (z • t) = ‖z‖ * tensorNorm A B t := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  refine le_antisymm (tensorNorm_smul_le z t) ?_
  have h := tensorNorm_smul_le z⁻¹ (z • t)
  rw [smul_smul, inv_mul_cancel₀ hz, one_smul, norm_inv] at h
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc ‖z‖ * tensorNorm A B t
      ≤ ‖z‖ * (‖z‖⁻¹ * tensorNorm A B (z • t)) :=
        mul_le_mul_of_nonneg_left h hzpos.le
    _ = tensorNorm A B (z • t) := by field_simp

/-- **112VIII**, part 4: the triangle inequality, from Cauchy–Schwarz for
each basic functional separately. -/
theorem tensorNorm_add_le [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (s t : A ⊗[ℂ] B) :
    tensorNorm A B (s + t) ≤ tensorNorm A B s + tensorNorm A B t := by
  refine csSup_le ⟨0, zero_mem_tnSet _⟩ ?_
  rintro r ⟨ω, hω, h1, rfl⟩
  calc Real.sqrt (ω (star (s + t) * (s + t))).re = tsn ω (s + t) := rfl
    _ ≤ tsn ω s + tsn ω t := tsn_add_le hω s t
    _ ≤ tensorNorm A B s + tensorNorm A B t :=
        add_le_add (le_csSup (tnSet_bddAbove s) ⟨ω, hω, h1, rfl⟩)
          (le_csSup (tnSet_bddAbove t) ⟨ω, hω, h1, rfl⟩)

/-- **112VIII**, part 2 (definiteness).  For `t ≠ 0` the product
functionals separate (**112VI**, applied to the np-functionals, which are
separating by vn.tex 44XI), giving `σ`, `τ` with `(σ ⊙ τ)(t) ≠ 0`;
Cauchy–Schwarz then forces both `(σ ⊙ τ)(1) > 0` and
`(σ ⊙ τ)(t* t) > 0`, and rescaling by `t₀ = ((σ⊙τ)(1))^{-½}·1` turns
`σ ⊙ τ` into a basic functional with `ω(1) = 1`. -/
theorem tensorNorm_eq_zero_iff [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (t : A ⊗[ℂ] B) : tensorNorm A B t = 0 ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, tensorNorm_zero]⟩
  by_contra ht
  obtain ⟨σ, τ, hστ⟩ : ∃ (σ : NPFunctional A) (τ : NPFunctional B),
      odotF (npLin σ) (npLin τ) t ≠ 0 := by
    by_contra hex
    have hall : ∀ (σ : NPFunctional A) (τ : NPFunctional B),
        odotF (npLin σ) (npLin τ) t = 0 := fun σ τ => by
      by_contra h0
      exact hex ⟨σ, τ, h0⟩
    refine ht (product_functionals_separating
      (Set.range fun σ : NPFunctional A => npLin σ)
      (Set.range fun τ : NPFunctional B => npLin τ)
      (fun a ha => np_separating a fun ω => ha (npLin ω) ⟨ω, rfl⟩)
      (fun b hb => np_separating b fun ω => hb (npLin ω) ⟨ω, rfl⟩)
      t ?_)
    rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    exact hall σ τ
  set ω₀ := odotF (npLin σ) (npLin τ) with hω₀def
  have hb₀ : IsBasicFunctional ω₀ := ⟨σ, τ, 1, fun s => by simp [hω₀def]⟩
  have hcs := basic_cauchy_schwarz hb₀ 1 t
  rw [star_one, one_mul] at hcs
  have hpos : 0 < ‖ω₀ t‖ := norm_pos_iff.mpr hστ
  have hs1 : 0 < tsn ω₀ 1 := by
    rcases (tsn_nonneg ω₀ 1).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, zero_mul] at hcs; linarith
  have hst : 0 < tsn ω₀ t := by
    rcases (tsn_nonneg ω₀ t).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, mul_zero] at hcs; linarith
  have hc : 0 < (ω₀ 1).re := by
    have hone : tsn ω₀ 1 = Real.sqrt (ω₀ 1).re := by simp [tsn]
    rw [hone] at hs1
    exact Real.sqrt_pos.mp hs1
  have hcstar : 0 < (ω₀ (star t * t)).re := Real.sqrt_pos.mp hst
  set c : ℝ := (ω₀ 1).re with hcdef
  set r : ℝ := Real.sqrt (1 / c) with hrdef
  have hr2 : r ^ 2 = 1 / c := Real.sq_sqrt (by positivity)
  set ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ := ((r ^ 2 : ℝ) : ℂ) • ω₀ with hωdef
  have hωapp : ∀ s, ω s = ((r ^ 2 : ℝ) : ℂ) * ω₀ s := fun s => rfl
  have hbω : IsBasicFunctional ω := by
    refine ⟨σ, τ, ((r : ℂ)) • 1, fun s => ?_⟩
    have hstar : star (((r : ℂ)) • (1 : A ⊗[ℂ] B)) * s * (((r : ℂ)) • 1)
        = (((r ^ 2 : ℝ)) : ℂ) • s := by
      rw [star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
        smul_smul]
      norm_num
      rw [← Complex.ofReal_pow]
      norm_num [pow_two]
    rw [hstar, hωapp, map_smul, smul_eq_mul]
  have h1 : (ω 1).re ≤ 1 := by
    rw [hωapp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    rw [hr2, ← hcdef, one_div, inv_mul_cancel₀ (ne_of_gt hc)]
  have hposval : 0 < Real.sqrt (ω (star t * t)).re := by
    rw [Real.sqrt_pos, hωapp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    have hr2pos : 0 < r ^ 2 := by rw [hr2]; positivity
    exact mul_pos hr2pos hcstar
  have hmem := le_csSup (tnSet_bddAbove t)
    (⟨ω, hbω, h1, rfl⟩ : Real.sqrt (ω (star t * t)).re ∈ tnSet t)
  rw [← tensorNorm_eq_sSup, h] at hmem
  linarith

/-- **112VIII** (`tensor-product-norm`, proc.tex:2849, Exercise): the
tensor product norm is a norm on `𝒜 ⊙ ℬ`. -/
theorem tensor_product_norm [VonNeumannAlgebra A] [VonNeumannAlgebra B] :
    (∀ t : A ⊗[ℂ] B, 0 ≤ tensorNorm A B t) ∧
      (∀ t : A ⊗[ℂ] B, tensorNorm A B t = 0 ↔ t = 0) ∧
      (∀ (z : ℂ) (t : A ⊗[ℂ] B),
        tensorNorm A B (z • t) = ‖z‖ * tensorNorm A B t) ∧
      ∀ s t : A ⊗[ℂ] B,
        tensorNorm A B (s + t) ≤ tensorNorm A B s + tensorNorm A B t :=
  ⟨tensorNorm_nonneg, tensorNorm_eq_zero_iff, tensorNorm_smul,
    tensorNorm_add_le⟩

/-! ### Auxiliary for **112IX**

The np-functional case is the one the exercise calls "almost by
definition": `σ ⊙ τ` *is* a basic functional (take `t₀ = 1`), hence
simple, hence trivially an operator-norm limit of simple functionals —
which is continuity for `uwTensorTopology` — and Cauchy–Schwarz against
`1` bounds it by `(σ⊙τ)(1)` times the tensor product norm.  The general
case is then **72XI** `luws` (2) ⇒ (3): `f = f₀ + i f₁ − f₂ − i f₃` with
`f_k` np-functionals. -/

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
private theorem odotF_tmul (f : A →ₗ[ℂ] ℂ) (g : B →ₗ[ℂ] ℂ) (a : A) (b : B) :
    odotF f g (a ⊗ₜ[ℂ] b) = f a * g b := by
  simp [odotF]

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- For np-functionals `σ`, `τ` the product functional `σ ⊙ τ` is basic
(witness `t₀ = 1`). -/
private theorem isBasicFunctional_odotF [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (σ : NPFunctional A) (τ : NPFunctional B) :
    IsBasicFunctional (odotF (npLin σ) (npLin τ)) :=
  ⟨σ, τ, 1, fun s => by simp⟩

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
private theorem smul_apply_re (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) (r : ℝ) (s : A ⊗[ℂ] B) :
    ((((r : ℝ) : ℂ) • ω) s).re = r * (ω s).re := by
  rw [LinearMap.smul_apply, smul_eq_mul]
  simp [Complex.mul_re]

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- A basic functional stays basic after multiplication by a nonnegative
real: conjugate its witness `t₀` by `√r`. -/
private theorem isBasicFunctional_smul [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω)
    {r : ℝ} (hr : 0 ≤ r) : IsBasicFunctional (((r : ℝ) : ℂ) • ω) := by
  obtain ⟨σ, τ, t₀, hωt⟩ := hω
  refine ⟨σ, τ, ((Real.sqrt r : ℝ) : ℂ) • t₀, fun s => ?_⟩
  have hsq : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  have hsr : star ((Real.sqrt r : ℝ) : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by simp
  have hstar : star (((Real.sqrt r : ℝ) : ℂ) • t₀) * s * (((Real.sqrt r : ℝ) : ℂ) • t₀)
      = ((r : ℝ) : ℂ) • (star t₀ * s * t₀) := by
    rw [star_smul, hsr, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
      hsq]
  rw [LinearMap.smul_apply, smul_eq_mul, hωt s, hstar, map_smul, smul_eq_mul]

omit [StarOrderedRing A] [StarOrderedRing B] in
private theorem tsn_smul_functional [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) {r : ℝ} (hr : 0 ≤ r) (t : A ⊗[ℂ] B) :
    tsn (((r : ℝ) : ℂ) • ω) t = Real.sqrt r * tsn ω t := by
  unfold tsn
  rw [smul_apply_re, Real.sqrt_mul hr]

/-- Every basic functional is bounded by `ω(1)` times the tensor product
norm.  (Cauchy–Schwarz against `1`, after rescaling `ω` so that
`ω(1) ≤ 1` — which is what makes it one of the functionals the supremum
defining `‖·‖` runs over.) -/
private theorem basic_norm_le_tensorNorm [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω)
    (t : A ⊗[ℂ] B) : ‖ω t‖ ≤ (ω 1).re * tensorNorm A B t := by
  have h0 : (0 : ℝ) ≤ (ω 1).re := by
    simpa using (Complex.le_def.mp (basic_one_nonneg hω)).1
  have hcs := basic_cauchy_schwarz hω 1 t
  rw [star_one, one_mul] at hcs
  have hone : tsn ω 1 = Real.sqrt (ω 1).re := by simp [tsn]
  rcases h0.eq_or_lt with hc | hc
  · rw [hone, ← hc, Real.sqrt_zero, zero_mul] at hcs
    rw [← hc, zero_mul]
    exact hcs
  · set c : ℝ := (ω 1).re with hcdef
    set ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ := (((c⁻¹ : ℝ)) : ℂ) • ω with hω'def
    have hbω' : IsBasicFunctional ω' :=
      isBasicFunctional_smul hω (inv_pos.mpr hc).le
    have h1 : (ω' 1).re ≤ 1 := by
      rw [hω'def, smul_apply_re, ← hcdef, inv_mul_cancel₀ (ne_of_gt hc)]
    have hmem : tsn ω' t ≤ tensorNorm A B t := by
      rw [tensorNorm_eq_sSup]
      exact le_csSup (tnSet_bddAbove t) ⟨ω', hbω', h1, rfl⟩
    have hts : tsn ω' t = Real.sqrt c⁻¹ * tsn ω t :=
      tsn_smul_functional ω (inv_pos.mpr hc).le t
    have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hsne : Real.sqrt c ≠ 0 := ne_of_gt hs
    have hself : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
    have hcc : c * Real.sqrt c⁻¹ = Real.sqrt c := by
      rw [Real.sqrt_inv]
      field_simp
      linarith
    calc ‖ω t‖ ≤ tsn ω 1 * tsn ω t := hcs
      _ = Real.sqrt c * tsn ω t := by rw [hone]
      _ = c * (Real.sqrt c⁻¹ * tsn ω t) := by rw [← mul_assoc, hcc]
      _ = c * tsn ω' t := by rw [hts]
      _ ≤ c * tensorNorm A B t := mul_le_mul_of_nonneg_left hmem hc.le

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- Every basic functional is continuous for the ultraweak tensor product
topology: it is simple, hence (trivially) an operator-norm limit of
simple functionals, and `uwTensorTopology` is the initial topology for
exactly those. -/
private theorem continuous_uwTensor_of_basic [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) :
    @Continuous _ ℂ (uwTensorTopology A B) _ ⇑ω := by
  have hsimple : IsSimpleFunctional ω := ⟨1, fun _ => ω, fun _ => hω, by simp⟩
  have hnl : NormLimitOfSimple A B ω := by
    intro ε hε
    refine ⟨ω, hsimple, fun t => ?_⟩
    simpa using mul_nonneg hε.le (tensorNorm_nonneg t)
  rw [continuous_iff_le_induced]
  show uwTensorTopology A B ≤ _
  exact iInf_le _ (⟨ω, hnl⟩ :
    {h : A ⊗[ℂ] B →ₗ[ℂ] ℂ // NormLimitOfSimple A B h})

/-- **112IX** (`product-functional`, proc.tex:2854, Exercise): for bounded
ultraweakly continuous functionals `f ∈ 𝒜_*` and `g ∈ ℬ_*` the
functional `f ⊙ g` is bounded (w.r.t. the tensor norm) and continuous
w.r.t. the ultraweak tensor product topology.

Note that the boundedness hypotheses `hfb`, `hgb` are **not used** (the
unused-variable warnings on them are left in place as the evidence):
ultraweak continuity alone gives, by **72XI** `luws` (2) ⇒ (3), a
decomposition of `f` into np-functionals, and boundedness of `f` is a
consequence rather than a hypothesis. -/
theorem product_functional [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : A →ₗ[ℂ] ℂ) (g : B →ₗ[ℂ] ℂ)
    (hfb : ∃ M : ℝ, ∀ a, ‖f a‖ ≤ M * ‖a‖)
    (hgb : ∃ M : ℝ, ∀ b, ‖g b‖ ≤ M * ‖b‖)
    (hfc : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hgc : @Continuous B ℂ (ultraweak B) _ ⇑g) :
    (∃ M : ℝ, ∀ t : A ⊗[ℂ] B, ‖odotF f g t‖ ≤ M * tensorNorm A B t) ∧
      @Continuous _ ℂ (uwTensorTopology A B) _ ⇑(odotF f g) := by
  classical
  -- **72XI** `luws` (2) ⇒ (3): decompose `f` and `g` into np-functionals.
  obtain ⟨F, hF⟩ := ((luws f).out 1 2).mp hfc
  obtain ⟨G, hG⟩ := ((luws g).out 1 2).mp hgc
  set co : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I] with hcodef
  have hconorm : ∀ k, ‖co k‖ = 1 := by
    intro k; fin_cases k <;> simp [hcodef]
  have hnpA : ∀ (σ : NPFunctional A) (a : A), npLin σ a = σ a := fun _ _ => rfl
  have hnpB : ∀ (τ : NPFunctional B) (b : B), npLin τ b = τ b := fun _ _ => rfl
  have hfsum : ∀ a : A, f a = ∑ k, co k * npLin (F k) a := by
    intro a
    rw [Fin.sum_univ_four, hF a]
    simp only [hnpA, hcodef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, one_mul]
    ring
  have hgsum : ∀ b : B, g b = ∑ l, co l * npLin (G l) b := by
    intro b
    rw [Fin.sum_univ_four, hG b]
    simp only [hnpB, hcodef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, one_mul]
    ring
  have hsplit : odotF f g = ∑ k : Fin 4, ∑ l : Fin 4,
      (co k * co l) • odotF (npLin (F k)) (npLin (G l)) := by
    refine TensorProduct.ext' fun a b => ?_
    rw [odotF_tmul, hfsum a, hgsum b, Finset.sum_mul_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, odotF_tmul]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have happ : ∀ t : A ⊗[ℂ] B, odotF f g t = ∑ k : Fin 4, ∑ l : Fin 4,
      (co k * co l) * odotF (npLin (F k)) (npLin (G l)) t := by
    intro t
    rw [hsplit]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine ⟨⟨∑ k : Fin 4, ∑ l : Fin 4,
      (odotF (npLin (F k)) (npLin (G l)) 1).re, fun t => ?_⟩, ?_⟩
  · rw [happ t, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, norm_mul, hconorm, hconorm, one_mul, one_mul]
    exact basic_norm_le_tensorNorm (isBasicFunctional_odotF (F k) (G l)) t
  · let _ : TopologicalSpace (A ⊗[ℂ] B) := uwTensorTopology A B
    have hfun : ⇑(odotF f g) = fun t => ∑ k : Fin 4, ∑ l : Fin 4,
        (co k * co l) * odotF (npLin (F k)) (npLin (G l)) t := funext happ
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
      continuous_const.mul
        (continuous_uwTensor_of_basic (isBasicFunctional_odotF (F k) (G l)))

/-- The defining property of the tensor product norm, read for a basic
functional that is *not* assumed subunital: `ω(s* s) ≤ ‖s‖² ω(1)`.  (Rescale
`ω` by `ω(1)⁻¹`, which keeps it basic by `isBasicFunctional_smul`; the
degenerate case `ω(1) = 0` forces `ω = 0` by Cauchy–Schwarz.)  This is the
estimate **112X**.2 needs. -/
private theorem basic_star_self_le [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ} (hω : IsBasicFunctional ω) (s : A ⊗[ℂ] B) :
    (ω (star s * s)).re ≤ tensorNorm A B s ^ 2 * (ω 1).re := by
  have h0 : (0 : ℝ) ≤ (ω 1).re := by
    simpa using (Complex.le_def.mp (basic_one_nonneg hω)).1
  rcases h0.eq_or_lt with hc | hc
  · have hb := basic_norm_le_tensorNorm hω (star s * s)
    rw [← hc, zero_mul] at hb
    have hz : ω (star s * s) = 0 := norm_le_zero_iff.mp hb
    rw [hz, ← hc]
    simp
  · set c : ℝ := (ω 1).re with hcdef
    set ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ := (((c⁻¹ : ℝ)) : ℂ) • ω with hω'def
    have hbω' : IsBasicFunctional ω' :=
      isBasicFunctional_smul hω (inv_pos.mpr hc).le
    have h1 : (ω' 1).re ≤ 1 := by
      rw [hω'def, smul_apply_re, ← hcdef, inv_mul_cancel₀ (ne_of_gt hc)]
    have hmem : tsn ω' s ≤ tensorNorm A B s := by
      rw [tensorNorm_eq_sSup]
      exact le_csSup (tnSet_bddAbove s) ⟨ω', hbω', h1, rfl⟩
    have hXnn : (0 : ℝ) ≤ (ω (star s * s)).re := by
      simpa using (Complex.le_def.mp ((basic_state_inner_product ω hω).2 s)).1
    have hval : tsn ω' s = Real.sqrt (c⁻¹ * (ω (star s * s)).re) := by
      unfold tsn
      rw [hω'def, smul_apply_re]
    rw [hval] at hmem
    have hnn : (0 : ℝ) ≤ c⁻¹ * (ω (star s * s)).re :=
      mul_nonneg (inv_nonneg.mpr hc.le) hXnn
    have hsq : c⁻¹ * (ω (star s * s)).re ≤ tensorNorm A B s ^ 2 := by
      nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (c⁻¹ * (ω (star s * s)).re)]
    calc (ω (star s * s)).re = c * (c⁻¹ * (ω (star s * s)).re) := by
          field_simp
      _ ≤ c * tensorNorm A B s ^ 2 := mul_le_mul_of_nonneg_left hsq hc.le
      _ = tensorNorm A B s ^ 2 * c := mul_comm _ _

section TensorBasic

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [VonNeumannAlgebra T]

/-! ### Infrastructure for **112X**: the ∗-subalgebra `γ_⊙(𝒜 ⊙ ℬ)` and the
product functionals as a centre separating collection -/

open scoped Pointwise in
/-- The linear span of the range of an miu-bilinear map `γ`, as a
∗-subalgebra of the codomain — this is `γ_⊙(𝒜 ⊙ ℬ)`, the copy of the
algebraic tensor product `𝒜 ⊙ ℬ` inside `𝒯` (see `range_lift_eq_span`).  It
is a ∗-subalgebra because `γ` is multiplicative and involution preserving
and `γ(1,1) = 1`. -/
def tensorSpan (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hmiu : MIUBilinear γ) :
    StarSubalgebra ℂ T where
  toSubalgebra := (Submodule.span ℂ {t : T | ∃ a b, t = γ a b}).toSubalgebra
    (Submodule.subset_span ⟨1, 1, hmiu.1.symm⟩)
    (by
      intro x y hx hy
      have hsub : ({t : T | ∃ a b, t = γ a b} * {t : T | ∃ a b, t = γ a b})
          ⊆ {t : T | ∃ a b, t = γ a b} := by
        rintro _ ⟨p, ⟨a, b, rfl⟩, q, ⟨a', b', rfl⟩, rfl⟩
        exact ⟨a * a', b * b', (hmiu.2.1 a a' b b').symm⟩
      have h1 : x * y ∈ Submodule.span ℂ {t : T | ∃ a b, t = γ a b}
          * Submodule.span ℂ {t : T | ∃ a b, t = γ a b} :=
        Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h1
      exact Submodule.span_le.mpr (hsub.trans Submodule.subset_span) h1)
  star_mem' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨a, b, rfl⟩ := hu
        exact Submodule.subset_span ⟨star a, star b, hmiu.2.2 a b⟩
    | zero => simp
    | add u v _ _ hu hv => rw [star_add]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu => rw [star_smul]; exact Submodule.smul_mem _ _ hu

@[simp] theorem coe_tensorSpan (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hmiu : MIUBilinear γ) :
    (tensorSpan γ hmiu : Set T)
      = (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T) :=
  rfl

/-- The range of `γ_⊙ : 𝒜 ⊙ ℬ → 𝒯` is the linear span of the range of
`γ`, since `𝒜 ⊙ ℬ` is spanned by the pure tensors. -/
theorem range_lift_eq_span (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) :
    Set.range ⇑(TensorProduct.lift γ)
      = (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T) := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => exact Submodule.subset_span ⟨a, b, by simp⟩
    | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  · intro ht
    induction ht using Submodule.span_induction with
    | mem u hu => obtain ⟨a, b, rfl⟩ := hu; exact ⟨a ⊗ₜ[ℂ] b, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
        obtain ⟨s, rfl⟩ := hu; obtain ⟨s', rfl⟩ := hv; exact ⟨s + s', by simp⟩
    | smul c u _ hu => obtain ⟨s, rfl⟩ := hu; exact ⟨c • s, by simp⟩

/-- The collection of *product functionals* `γ(σ,τ)` of a tensor product. -/
def prodFunctionals {γ : A →ₗ[ℂ] B →ₗ[ℂ] T} (hγ : IsTensorProduct γ) :
    Set (NPFunctional T) :=
  {χ : NPFunctional T | ∃ (σ : NPFunctional A) (τ : NPFunctional B),
    χ = prodNP hγ σ τ}

/-- Any np-functional implementing the product of `σ` and `τ` *is* the
chosen product functional `γ(σ,τ)` — `prod_functional_unique` read for
np-functionals. -/
theorem eq_prodNP {γ : A →ₗ[ℂ] B →ₗ[ℂ] T} (hγ : IsTensorProduct γ)
    (σ : NPFunctional A) (τ : NPFunctional B) (h : NPFunctional T)
    (hh : ∀ (a : A) (b : B), h (γ a b) = σ a * τ b) (t : T) :
    h t = prodNP hγ σ τ t := by
  have hu := prod_functional_unique γ hγ (npLin σ) (npLin τ) (npLin h)
    (npLin (prodNP hγ σ τ)) (continuous_ultraweak_npFunctional h)
    (continuous_ultraweak_npFunctional _) hh (prodNP_apply hγ σ τ)
  exact congrArg (fun f : T →ₗ[ℂ] ℂ => f t) hu

/-- The product functionals of a tensor product are **centre separating**
in the sense of cstar.tex **21II**.4: this is faithfulness (condition (3)
of 108II) with the conjugating element taken to be `1`. -/
theorem centreSeparatingConj_prodFunctionals {γ : A →ₗ[ℂ] B →ₗ[ℂ] T}
    (hγ : IsTensorProduct γ) : CentreSeparatingConj T (prodFunctionals hγ) := by
  rw [centreSeparatingConj_iff]
  intro a ha
  refine ⟨fun h ω hω b => by simp [h], fun H => ?_⟩
  refine hγ.faithful a ha fun σ τ h hh => ?_
  have h1 := H (prodNP hγ σ τ) ⟨σ, τ, rfl⟩ 1
  rw [star_one, one_mul, mul_one] at h1
  rw [eq_prodNP hγ σ τ h hh a]
  exact h1

/-- `γ_⊙(𝒜 ⊙ ℬ)` is *ultrastrongly* dense in `𝒯`: it is ultraweakly dense
by condition (1) of 108II, and **74VI** `dense_subalgebra` upgrades that to
ultrastrong convergence of a bounded net. -/
theorem dense_ultrastrong_tensorSpan {γ : A →ₗ[ℂ] B →ₗ[ℂ] T}
    (hγ : IsTensorProduct γ) :
    @Dense T (ultrastrong T)
      ((tensorSpan γ hγ.miu : StarSubalgebra ℂ T) : Set T) := by
  intro x
  refine (mem_usClosure_iff _ x).mpr ?_
  intro ω ε hε
  obtain ⟨ι, l, hl, s, hs, hlim⟩ :=
    dense_subalgebra (tensorSpan γ hγ.miu) hγ.dense 1 one_pos x
  have _ : l.NeBot := hl
  have ht := (usTendsto_iff s l x).mp hlim ω
  obtain ⟨i, hi⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨s i, (hs i).1, hi⟩

/-! ### `γ_⊙` is a ∗-homomorphism, and `Ω ↔ basic functionals`

The second half of **112X**.1's exercise text ("show that `ω ∘ γ_⊙` is a basic
functional for every `ω ∈ Ω`, and that every basic functional is of this form")
— infrastructure for 112X.2/.3, which our rendering of part 1 does not
state. -/

theorem lift_one (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hu : BilinUnital γ) :
    TensorProduct.lift γ (1 : A ⊗[ℂ] B) = 1 := by
  show TensorProduct.lift γ ((1 : A) ⊗ₜ[ℂ] (1 : B)) = 1
  rw [TensorProduct.lift.tmul]
  exact hu

theorem lift_mul (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hm : BilinMult γ) (s t : A ⊗[ℂ] B) :
    TensorProduct.lift γ (s * t)
      = TensorProduct.lift γ s * TensorProduct.lift γ t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a' b' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp [hm a a' b b']
      | add u v hu hv => rw [mul_add, map_add, map_add, hu, hv, mul_add]
  | add u v hu hv => rw [add_mul, map_add, map_add, hu, hv, add_mul]

theorem lift_star (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hs : BilinStar γ) (s : A ⊗[ℂ] B) :
    TensorProduct.lift γ (star s) = star (TensorProduct.lift γ s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [hs a b]
  | add u v hu hv => rw [star_add, map_add, map_add, hu, hv, star_add]

/-- `γ(σ,τ) ∘ γ_⊙ = σ ⊙ τ`. -/
theorem prodNP_lift {γ : A →ₗ[ℂ] B →ₗ[ℂ] T} (hγ : IsTensorProduct γ)
    (σ : NPFunctional A) (τ : NPFunctional B) (s : A ⊗[ℂ] B) :
    prodNP hγ σ τ (TensorProduct.lift γ s) = odotF (npLin σ) (npLin τ) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [prodNP_apply hγ σ τ a b, odotF, npLin, TensorProduct.lift.tmul,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply']
      rfl
  | add u v hu hv => rw [map_add, npFunctional_add, hu, hv, map_add]

/-- The np-functionals of the collection `Ω` of **112X**.1:
`γ(σ,τ)(γ_⊙(s)*(·)γ_⊙(s))`. -/
def conjProdNP {γ : A →ₗ[ℂ] B →ₗ[ℂ] T} (hγ : IsTensorProduct γ)
    (σ : NPFunctional A) (τ : NPFunctional B) (s : A ⊗[ℂ] B) : NPFunctional T :=
  conjNP (TensorProduct.lift γ s) (prodNP hγ σ τ)

@[simp] theorem conjProdNP_apply {γ : A →ₗ[ℂ] B →ₗ[ℂ] T} (hγ : IsTensorProduct γ)
    (σ : NPFunctional A) (τ : NPFunctional B) (s : A ⊗[ℂ] B) (t : T) :
    conjProdNP hγ σ τ s t
      = prodNP hγ σ τ
          (star (TensorProduct.lift γ s) * t * TensorProduct.lift γ s) :=
  conjNP_apply _ _ _

/-- The restriction of a member of `Ω` along `γ_⊙` is the basic functional
`(σ ⊙ τ)(s*(·)s)`. -/
theorem conjProdNP_lift {γ : A →ₗ[ℂ] B →ₗ[ℂ] T} (hγ : IsTensorProduct γ)
    (σ : NPFunctional A) (τ : NPFunctional B) (s t : A ⊗[ℂ] B) :
    conjProdNP hγ σ τ s (TensorProduct.lift γ t)
      = odotF (npLin σ) (npLin τ) (star s * t * s) := by
  rw [conjProdNP_apply, ← lift_star γ hγ.miu.2.2, ← lift_mul γ hγ.miu.2.1,
    ← lift_mul γ hγ.miu.2.1, prodNP_lift hγ]

theorem isBasicFunctional_comp_lift {γ : A →ₗ[ℂ] B →ₗ[ℂ] T}
    (hγ : IsTensorProduct γ) (σ : NPFunctional A) (τ : NPFunctional B)
    (s : A ⊗[ℂ] B) :
    IsBasicFunctional ((npLin (conjProdNP hγ σ τ s)).comp (TensorProduct.lift γ)) :=
  ⟨σ, τ, s, fun t => conjProdNP_lift hγ σ τ s t⟩

/-- Conversely, every basic functional on `𝒜 ⊙ ℬ` is the restriction along
`γ_⊙` of a (unique, by `prod_functional_unique`) member of `Ω`. -/
theorem exists_conjProdNP_of_isBasicFunctional {γ : A →ₗ[ℂ] B →ₗ[ℂ] T}
    (hγ : IsTensorProduct γ) (ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ) (hω : IsBasicFunctional ω) :
    ∃ (σ : NPFunctional A) (τ : NPFunctional B) (s : A ⊗[ℂ] B),
      ∀ t : A ⊗[ℂ] B, ω t = conjProdNP hγ σ τ s (TensorProduct.lift γ t) := by
  obtain ⟨σ, τ, s, hs⟩ := hω
  exact ⟨σ, τ, s, fun t => by rw [hs t, conjProdNP_lift hγ]⟩

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
              TensorProduct.lift γ (s i))‖ ≤ ε * ‖t‖ := by
  constructor
  · -- **Order separating.**  Put `a := y - x`.  By `nonneg_of_conjNP_of_centreSeparating`
    -- (30X fed with `centreSeparatingConj_prodFunctionals`) it suffices that
    -- `γ(σ,τ)(c* a c) ≥ 0` for *every* `c ∈ 𝒯`, while the hypothesis gives this
    -- only for `c ∈ γ_⊙(𝒜 ⊙ ℬ)`.  **74VI** `dense_subalgebra` supplies a
    -- norm-bounded net `s_α → c` ultrastrongly from that subalgebra, and
    -- **72III**.1c `bstaromega_lipschitz` transfers the limit.
    intro x y hx hy H
    rw [← sub_nonneg]
    set a : T := y - x with hadef
    have hasa : IsSelfAdjoint a := hy.sub hx
    have hconj : ∀ d : T, IsSelfAdjoint (star d * a * d) := fun d => by
      show star (star d * a * d) = star d * a * d
      rw [star_mul, star_mul, star_star, hasa.star_eq, mul_assoc]
    refine nonneg_of_conjNP_of_centreSeparating (prodFunctionals hγ)
      (centreSeparatingConj_prodFunctionals hγ) ?_
    rintro χ ⟨σ, τ, rfl⟩ c
    set ω : NPFunctional T := prodNP hγ σ τ with hωdef
    have hsplit : ∀ d : T,
        ω (star d * a * d) = ω (star d * y * d) - ω (star d * x * d) := by
      intro d
      have e : star d * a * d = star d * y * d - star d * x * d := by
        rw [hadef]; noncomm_ring
      rw [e, npFunctional_sub]
    obtain ⟨ι, l, hl, s, hs, hlim⟩ :=
      dense_subalgebra (tensorSpan γ hγ.miu) hγ.dense 1 one_pos c
    have _ : l.NeBot := hl
    have hnn : ∀ i, 0 ≤ (ω (star (s i) * a * s i)).re := by
      intro i
      have hmem : s i ∈ Set.range ⇑(TensorProduct.lift γ) := by
        rw [range_lift_eq_span]; exact (hs i).1
      obtain ⟨v, hv⟩ := hmem
      have hH := H σ τ v
      rw [hv] at hH
      rw [hsplit, Complex.sub_re]
      linarith
    set K : ℝ := ‖c‖ * (1 + 1) * omegaNorm T ω 1 + omegaNorm T ω c with hKdef
    have hbnd : ∀ i, ‖ω (star (s i) * a * s i) - ω (star c * a * c)‖
        ≤ omegaNorm T ω (s i - c) * (K * ‖a‖) := by
      intro i
      have hlip := bstaromega_lipschitz ω (s i) c a
      have hsi : omegaNorm T ω (s i) ≤ ‖c‖ * (1 + 1) * omegaNorm T ω 1 := by
        have h1 : omegaNorm T ω (s i * 1) ≤ ‖s i‖ * omegaNorm T ω 1 :=
          omegaNorm_mul_le ω (s i) 1
        rw [mul_one] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (hs i).2 (omegaNorm_nonneg ω 1))
      have h0 := omegaNorm_nonneg ω (s i - c)
      have h1 : omegaNorm T ω (s i) + omegaNorm T ω c ≤ K := by rw [hKdef]; linarith
      refine hlip.trans ?_
      calc omegaNorm T ω (s i - c) * (omegaNorm T ω (s i) + omegaNorm T ω c) * ‖a‖
          = omegaNorm T ω (s i - c)
              * ((omegaNorm T ω (s i) + omegaNorm T ω c) * ‖a‖) := by ring
        _ ≤ omegaNorm T ω (s i - c) * (K * ‖a‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h1 (norm_nonneg a)) h0
    have hzero : Tendsto (fun i => omegaNorm T ω (s i - c) * (K * ‖a‖)) l (𝓝 0) := by
      have hus := (usTendsto_iff s l c).mp hlim ω
      simpa using hus.mul_const (K * ‖a‖)
    have hconv : Tendsto (fun i => ω (star (s i) * a * s i)) l
        (𝓝 (ω (star c * a * c))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun i => norm_nonneg _) hbnd hzero
    have hre : Tendsto (fun i => (ω (star (s i) * a * s i)).re) l
        (𝓝 (ω (star c * a * c)).re) := (Complex.continuous_re.tendsto _).comp hconv
    have hfin : (0 : ℝ) ≤ (ω (star c * a * c)).re :=
      ge_of_tendsto hre (Filter.Eventually.of_forall hnn)
    rw [Complex.le_def]
    exact ⟨by simpa using hfin, by
      rw [Complex.zero_im, npFunctional_im_eq_zero ω (hconj c)]⟩
  · -- **Every np-functional is a norm limit of finite sums from `Ω`** — this is
    -- **90II**.2 `vn_center_separating_fundamental_2` applied to the centre
    -- separating collection of product functionals and the ultrastrongly dense
    -- ∗-subalgebra `γ_⊙(𝒜 ⊙ ℬ)`.
    intro h ε hε
    have hdense : @Dense T (ultrastrong T) (Set.range ⇑(TensorProduct.lift γ)) := by
      rw [range_lift_eq_span]; exact dense_ultrastrong_tensorSpan hγ
    obtain ⟨n, ω, s, hmem, hbound⟩ :=
      vn_center_separating_fundamental_2 (prodFunctionals hγ)
        (centreSeparatingConj_prodFunctionals hγ)
        (Set.range ⇑(TensorProduct.lift γ)) hdense h ε hε
    choose σ τ hστ using fun k => (hmem k).1
    choose u hu using fun k => (hmem k).2
    refine ⟨n, σ, τ, u, fun t => ?_⟩
    simp only [hu]
    simpa only [hστ] using hbound t

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 2 (headline
claim): `γ_⊙ : 𝒜 ⊙ ℬ → 𝒯` is an isometry for the tensor product
norm. -/
theorem tensor_basic_2 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ)
    (s : A ⊗[ℂ] B) : ‖TensorProduct.lift γ s‖ = tensorNorm A B s := by
  -- Both halves are read off the identity `γ_⊙(s)*γ_⊙(s) = γ_⊙(s* s)` and the
  -- bijection `Ω ↔ basic functionals` of 112X.1.
  have hsmul : ∀ (χ : NPFunctional T) (r : ℝ) (x : T),
      χ (((r : ℝ) : ℂ) • x) = ((r : ℝ) : ℂ) * χ x := by
    intro χ r x
    show npLin χ (((r : ℝ) : ℂ) • x) = _
    rw [map_smul]
    rfl
  set y : T := TensorProduct.lift γ s with hydef
  have hstarmul : star y * y = TensorProduct.lift γ (star s * s) := by
    rw [hydef, lift_mul γ hγ.miu.2.1, lift_star γ hγ.miu.2.2]
  have hxnn : (0 : T) ≤ star y * y := star_mul_self_nonneg y
  have hnx : ‖star y * y‖ = ‖y‖ ^ 2 := by
    rw [CStarRing.norm_star_mul_self]; ring
  have hone : TensorProduct.lift γ (1 : A ⊗[ℂ] B) = 1 := lift_one γ hγ.miu.1
  refine le_antisymm ?_ ?_
  · -- `‖γ_⊙ s‖ ≤ ‖s‖`.  The thesis obtains this from `order-separating-norm`
    -- (**21VII**) applied to the *unital* members `Ω₁`; we apply the order
    -- separating property of 112X.1 directly at `γ_⊙(s)*γ_⊙(s) ≤ ‖s‖²·1`,
    -- which is 21VII's own argument without the renormalisation of `Ω` to
    -- `Ω₁` (see the log).
    have hN : (0 : ℝ) ≤ tensorNorm A B s := tensorNorm_nonneg s
    have hsa1 : IsSelfAdjoint (((tensorNorm A B s ^ 2 : ℝ) : ℂ) • (1 : T)) := by
      show star _ = _
      simp
    have hle : star y * y ≤ ((tensorNorm A B s ^ 2 : ℝ) : ℂ) • (1 : T) := by
      refine (tensor_basic_1 γ hγ).1 _ _ (IsSelfAdjoint.star_mul_self y) hsa1 ?_
      intro σ τ v
      have hbasic := isBasicFunctional_comp_lift hγ σ τ v
      set ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ :=
        (npLin (conjProdNP hγ σ τ v)).comp (TensorProduct.lift γ) with hω'def
      have hL : prodNP hγ σ τ (star (TensorProduct.lift γ v) * (star y * y) *
          TensorProduct.lift γ v) = ω' (star s * s) := by
        rw [hstarmul]
        rfl
      have hR : prodNP hγ σ τ (star (TensorProduct.lift γ v) *
            (((tensorNorm A B s ^ 2 : ℝ) : ℂ) • (1 : T)) *
            TensorProduct.lift γ v)
          = ((tensorNorm A B s ^ 2 : ℝ) : ℂ) * ω' 1 := by
        have he : star (TensorProduct.lift γ v) *
              (((tensorNorm A B s ^ 2 : ℝ) : ℂ) • (1 : T)) *
              TensorProduct.lift γ v
            = ((tensorNorm A B s ^ 2 : ℝ) : ℂ) •
              (star (TensorProduct.lift γ v) * 1 * TensorProduct.lift γ v) := by
          rw [mul_smul_comm, smul_mul_assoc]
        rw [he, hsmul]
        congr 1
        show _ = conjProdNP hγ σ τ v (TensorProduct.lift γ 1)
        rw [conjProdNP_apply, hone]
      rw [hL, hR, Complex.re_ofReal_mul]
      exact basic_star_self_le hbasic s
    have hnorm : ‖star y * y‖ ≤ tensorNorm A B s ^ 2 := by
      refine (Theses.A.CStar.norm_le_iff_neg_algebraMap_le
        (IsSelfAdjoint.star_mul_self y) (by positivity)).mpr ⟨?_, ?_⟩
      · refine le_trans (neg_nonpos.mpr ?_) hxnn
        exact Theses.A.CStar.algebraMap_ofReal_nonneg (by positivity)
      · rwa [Algebra.algebraMap_eq_smul_one]
    rw [hnx] at hnorm
    nlinarith [norm_nonneg y, hN]
  · -- `‖s‖ ≤ ‖γ_⊙ s‖`: every basic functional is `χ ∘ γ_⊙` for a member `χ`
    -- of `Ω`, and `χ(γ_⊙(s)*γ_⊙(s)) ≤ ‖γ_⊙ s‖² χ(1)` by positivity of `χ`.
    refine Real.sSup_le (fun r hr => ?_) (norm_nonneg y)
    obtain ⟨ω, hω, h1, rfl⟩ := hr
    obtain ⟨σ, τ, u, hrep⟩ := exists_conjProdNP_of_isBasicFunctional hγ ω hω
    have hval : ω (star s * s) = conjProdNP hγ σ τ u (star y * y) := by
      rw [hrep, hstarmul]
    have hone' : ω 1 = conjProdNP hγ σ τ u 1 := by rw [hrep, hone]
    have hb : star y * y ≤ ((‖star y * y‖ : ℝ) : ℂ) • (1 : T) := by
      rw [Complex.coe_smul]
      exact le_norm_smul_one hxnn
    have hmono := npFunctional_mono (conjProdNP hγ σ τ u) hb
    rw [hsmul] at hmono
    have hre : (ω (star s * s)).re ≤ ‖y‖ ^ 2 * (ω 1).re := by
      rw [hval, hone']
      have := (Complex.le_def.mp hmono).1
      rwa [Complex.re_ofReal_mul, hnx] at this
    have h1nn : (0 : ℝ) ≤ (ω 1).re := by
      simpa using (Complex.le_def.mp (basic_one_nonneg hω)).1
    have hfin : (ω (star s * s)).re ≤ ‖y‖ ^ 2 := by
      refine hre.trans ?_
      nlinarith [sq_nonneg ‖y‖]
    calc Real.sqrt (ω (star s * s)).re ≤ Real.sqrt (‖y‖ ^ 2) :=
          Real.sqrt_le_sqrt hfin
      _ = ‖y‖ := Real.sqrt_sq (norm_nonneg y)

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 3 (headline
claim): `γ_⊙` is continuous from the ultraweak tensor product topology to
the ultraweak topology on `𝒯` (and the restriction of an np-functional
along `γ_⊙` is an operator norm limit of simple functionals). -/
theorem tensor_basic_3 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ) :
    (@Continuous _ _ (uwTensorTopology A B) (ultraweak T)
        ⇑(TensorProduct.lift γ)) ∧
      ∀ h : NPFunctional T,
        NormLimitOfSimple A B
          ((npLin h).comp (TensorProduct.lift γ)) := by
  -- The second half first.  **112X**.1's second conjunct approximates an
  -- np-functional `h` on `𝒯`, in *operator* norm, by a finite sum of members
  -- of `Ω`; restricting along `γ_⊙` turns that sum into a simple functional
  -- (`isBasicFunctional_comp_lift`), and **112X**.2 converts `ε‖γ_⊙ t‖` into
  -- `ε‖t‖` — which is the thesis's `‖f ∘ γ_⊙‖ ≤ ‖f‖`, here in the only form
  -- it is used.  The first half then follows because `uwTensorTopology` is
  -- by definition the initial topology of exactly these functionals.
  have hnl : ∀ h : NPFunctional T,
      NormLimitOfSimple A B ((npLin h).comp (TensorProduct.lift γ)) := by
    intro h ε hε
    obtain ⟨n, σ, τ, s, hb⟩ := (tensor_basic_1 γ hγ).2 h ε hε
    refine ⟨∑ i, (npLin (conjProdNP hγ (σ i) (τ i) (s i))).comp
      (TensorProduct.lift γ), ⟨n, fun i =>
        (npLin (conjProdNP hγ (σ i) (τ i) (s i))).comp (TensorProduct.lift γ),
        fun i => isBasicFunctional_comp_lift hγ (σ i) (τ i) (s i), rfl⟩,
      fun t => ?_⟩
    have hbt := hb (TensorProduct.lift γ t)
    rw [tensor_basic_2 γ hγ t] at hbt
    refine le_trans (le_of_eq ?_) hbt
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply]
    rfl
  refine ⟨?_, hnl⟩
  rw [continuous_iff_le_induced]
  show uwTensorTopology A B ≤ TopologicalSpace.induced ⇑(TensorProduct.lift γ)
    (⨅ ω : NPFunctional T,
      TopologicalSpace.induced (fun x : T => (ω x : ℂ)) inferInstance)
  rw [induced_iInf]
  refine le_iInf fun ω => ?_
  rw [induced_compose]
  exact iInf_le _ (⟨(npLin ω).comp (TensorProduct.lift γ), hnl ω⟩ :
    {f : A ⊗[ℂ] B →ₗ[ℂ] ℂ // NormLimitOfSimple A B f})

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 4:
`‖f ∘ γ_⊙‖ = ‖f‖` for every `f ∈ 𝒯_*` — rendered in bound form: `f` and
`f ∘ γ_⊙` have the same bounds. -/
theorem tensor_basic_4 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ)
    (f : T →L[ℂ] ℂ) (hf : @Continuous T ℂ (ultraweak T) _ ⇑f) (M : ℝ)
    (hM : 0 ≤ M) :
    (∀ t : A ⊗[ℂ] B,
        ‖f (TensorProduct.lift γ t)‖ ≤ M * tensorNorm A B t) ↔
      ∀ x : T, ‖f x‖ ≤ M * ‖x‖ := by
  constructor
  · -- The thesis's argument verbatim: **86IX** supplies a partial isometry `u`
    -- with `f(u) = ‖f‖` (**86XI** `functional_norm`); **74VI** approximates `u`
    -- ultrastrongly from `γ_⊙(𝒜 ⊙ ℬ)` with `‖s_α‖ ≤ ‖u‖(1+ε)`; and **112X**.2
    -- turns the tensor-norm bound on `f ∘ γ_⊙` into a `𝒯`-norm bound along the
    -- net.  Hence `‖f‖ ≤ M(1+ε)` for every `ε > 0`.
    intro h
    obtain ⟨u, hu, heq, -, hpos, -⟩ :=
      polar_decomposition_of_functional (A := T) f.toLinearMap
        (by simpa using
          (@Continuous.continuousOn T ℂ (ultraweak T) _ ⇑f _ hf))
    have hfu : f u = ((‖f‖ : ℝ) : ℂ) := functional_norm f hf u hu hpos heq
    have hpr : IsStarProjection (star u * u) := by
      rw [hu.1, suppProj]
      exact (ceil_spec (star_mul_self_nonneg u)).1
    have hu1 : ‖u‖ ≤ 1 := by
      have h1 : ‖u‖ * ‖u‖ ≤ 1 := by
        rw [← CStarRing.norm_star_mul_self]
        exact IsStarProjection.norm_le _ hpr
      nlinarith [norm_nonneg u]
    have hkey : ∀ ε : ℝ, 0 < ε → ‖f‖ ≤ M * (1 + ε) := by
      intro ε hε
      obtain ⟨ι, l, hl, s, hs, hlim⟩ :=
        dense_subalgebra (tensorSpan γ hγ.miu) hγ.dense ε hε u
      have _ : l.NeBot := hl
      have huw : UWTendsto s l u := uwweaker_2 s l u hlim
      have hconv : Tendsto (fun i => ‖f (s i)‖) l (𝓝 ‖f u‖) :=
        ((@Continuous.tendsto T ℂ (ultraweak T) _ ⇑f hf u).comp huw).norm
      have hbd : ∀ i, ‖f (s i)‖ ≤ M * (1 + ε) := by
        intro i
        have hmem : s i ∈ Set.range ⇑(TensorProduct.lift γ) := by
          rw [range_lift_eq_span]; exact (hs i).1
        obtain ⟨v, hv⟩ := hmem
        have h1 := h v
        rw [← tensor_basic_2 γ hγ v, hv] at h1
        refine h1.trans ?_
        have h2 := (hs i).2
        have h3 : ‖s i‖ ≤ 1 * (1 + ε) := by
          refine h2.trans ?_
          gcongr
        calc M * ‖s i‖ ≤ M * (1 * (1 + ε)) := by gcongr
          _ = M * (1 + ε) := by ring
      have hlim' := le_of_tendsto hconv (Filter.Eventually.of_forall hbd)
      rw [hfu] at hlim'
      simpa using hlim'
    have hfM : ‖f‖ ≤ M := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hpos1 : (0 : ℝ) < M + 1 := by linarith
      have hε : (0 : ℝ) < δ / (M + 1) := by positivity
      have he : (M + 1) * (δ / (M + 1)) = δ := by field_simp
      have h2 : M * (δ / (M + 1)) ≤ (M + 1) * (δ / (M + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h3 : M * (1 + δ / (M + 1)) = M + M * (δ / (M + 1)) := by ring
      linarith [hkey _ hε]
    intro x
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ M * ‖x‖ := by gcongr
  · -- The easy half: **112X**.2 again.
    intro h t
    rw [← tensor_basic_2 γ hγ t]
    exact h _

/-- An np-functional is bounded, with `‖ω‖ ≤ ω(1)`: Kadison's inequality
`‖ω a‖ ≤ ‖a‖_ω √(ω 1)` together with `‖a‖_ω = ‖a·1‖_ω ≤ ‖a‖‖1‖_ω`. -/
private theorem npFunctional_norm_le (ω : NPFunctional T) (a : T) :
    ‖ω a‖ ≤ (ω 1).re * ‖a‖ := by
  have h0 : (0 : ℝ) ≤ (ω 1).re := by
    simpa using (Complex.le_def.mp (npFunctional_nonneg ω zero_le_one)).1
  have h1 := norm_apply_le_omegaNorm ω a
  have h2 : omegaNorm T ω a ≤ ‖a‖ * Real.sqrt (ω 1).re := by
    have h := omegaNorm_mul_le ω a 1
    rwa [mul_one, omegaNorm_one] at h
  have h3 : Real.sqrt (ω 1).re * Real.sqrt (ω 1).re = (ω 1).re :=
    Real.mul_self_sqrt h0
  nlinarith [Real.sqrt_nonneg (ω 1).re, norm_nonneg a, omegaNorm_nonneg ω a]

/-- An np-functional as a continuous linear functional. -/
private noncomputable def npCLM (ω : NPFunctional T) : T →L[ℂ] ℂ :=
  LinearMap.mkContinuous (npLin ω) ((ω 1).re) (npFunctional_norm_le ω)

@[simp] private theorem npCLM_apply (ω : NPFunctional T) (a : T) :
    npCLM ω a = ω a := rfl

/-- **112X** (`tensor-basic`, proc.tex:2868, Exercise), part 5: every
operator norm limit of simple functionals extends uniquely along `γ_⊙` to
an np-functional on `𝒯`; consequently `γ_⊙` is an ultraweak topological
embedding. -/
theorem tensor_basic_5 (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hγ : IsTensorProduct γ) :
    (∀ ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ, NormLimitOfSimple A B ω' →
      ∃! ω : NPFunctional T,
        ∀ s : A ⊗[ℂ] B, ω (TensorProduct.lift γ s) = ω' s) ∧
    uwTensorTopology A B =
      TopologicalSpace.induced ⇑(TensorProduct.lift γ) (ultraweak T) := by
  -- Uniqueness is ultraweak density of `γ_⊙(𝒜 ⊙ ℬ)` (108II(1)); existence is
  -- the thesis's route through **87III** `predual_complete`, with **112X**.4
  -- supplying `‖f ∘ γ_⊙‖ = ‖f‖`, which is what makes the approximating
  -- sequence Cauchy in `𝒯_*`.  The topology equality then follows: `≤` is
  -- 112X.3's first conjunct, and `≥` is the factorisation just obtained.
  have huniq : ∀ ω₁ ω₂ : NPFunctional T,
      (∀ s : A ⊗[ℂ] B,
        ω₁ (TensorProduct.lift γ s) = ω₂ (TensorProduct.lift γ s)) → ω₁ = ω₂ := by
    intro ω₁ ω₂ h
    letI : TopologicalSpace T := ultraweak T
    refine DFunLike.coe_injective (Continuous.ext_on hγ.dense
      (continuous_ultraweak_npFunctional ω₁)
      (continuous_ultraweak_npFunctional ω₂) ?_)
    intro t ht
    rw [← range_lift_eq_span] at ht
    obtain ⟨s, rfl⟩ := ht
    exact h s
  have hexists : ∀ ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ, NormLimitOfSimple A B ω' →
      ∃ ω : NPFunctional T, ∀ s, ω (TensorProduct.lift γ s) = ω' s := by
    intro ω' hω'
    choose G hGs hGb using fun n : ℕ => hω' (1 / (n + 1)) (by positivity)
    -- each simple functional lifts to a positive normal functional on `𝒯`
    have hrep : ∀ n : ℕ, ∃ H : T →L[ℂ] ℂ,
        (@Continuous T ℂ (ultraweak T) _ ⇑H) ∧ (∀ x : T, 0 ≤ x → 0 ≤ H x) ∧
        ∀ t : A ⊗[ℂ] B, H (TensorProduct.lift γ t) = G n t := by
      intro n
      obtain ⟨k, ωs, hbasic, hsum⟩ := hGs n
      choose σ τ u hu using fun i =>
        exists_conjProdNP_of_isBasicFunctional hγ (ωs i) (hbasic i)
      refine ⟨∑ i, npCLM (conjProdNP hγ (σ i) (τ i) (u i)), ?_, ?_, ?_⟩
      · letI : TopologicalSpace T := ultraweak T
        have hfun : ⇑(∑ i, npCLM (conjProdNP hγ (σ i) (τ i) (u i)))
            = fun x : T => ∑ i, (conjProdNP hγ (σ i) (τ i) (u i) x : ℂ) := by
          funext x
          simp [ContinuousLinearMap.sum_apply]
        rw [hfun]
        exact continuous_finsetSum _ fun i _ =>
          continuous_ultraweak_npFunctional _
      · intro x hx
        rw [ContinuousLinearMap.sum_apply]
        exact Finset.sum_nonneg fun i _ => by
          simpa using npFunctional_nonneg (conjProdNP hγ (σ i) (τ i) (u i)) hx
      · intro t
        rw [ContinuousLinearMap.sum_apply, hsum]
        simp only [LinearMap.sum_apply, npCLM_apply]
        exact Finset.sum_congr rfl fun i _ => (hu i t).symm
    choose H hHc hHpos hHval using hrep
    -- the sequence is Cauchy in the predual, by **112X**.4
    have hdiff : ∀ n m : ℕ,
        ‖H n - H m‖ ≤ 1 / (n + 1) + 1 / (m + 1) := by
      intro n m
      have hM : (0 : ℝ) ≤ 1 / (n + 1) + 1 / (m + 1) := by positivity
      have hc : @Continuous T ℂ (ultraweak T) _ ⇑(H n - H m) := by
        letI : TopologicalSpace T := ultraweak T
        have : ⇑(H n - H m) = fun x : T => H n x - H m x := by
          funext x; simp
        rw [this]
        exact (hHc n).sub (hHc m)
      have hpt : ∀ x : T, ‖(H n - H m) x‖ ≤ (1 / (n + 1) + 1 / (m + 1)) * ‖x‖ := by
        refine (tensor_basic_4 γ hγ (H n - H m) hc _ hM).mp ?_
        intro t
        rw [ContinuousLinearMap.sub_apply, hHval n t, hHval m t]
        have e : G n t - G m t = -(ω' t - G n t) + (ω' t - G m t) := by ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        have := hGb n t
        have := hGb m t
        rw [add_mul]
        push_cast at *
        linarith
      exact ContinuousLinearMap.opNorm_le_bound _ hM hpt
    have hCauchy : CauchySeq H := by
      refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 / (N + 1)) ?_ ?_
      · intro n m N hn hm
        rw [dist_eq_norm]
        refine (hdiff n m).trans ?_
        have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast by omega]
        have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast by omega]
        have : (2 : ℝ) / (N + 1) = 1 / (N + 1) + 1 / (N + 1) := by ring
        linarith
      · have h : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop
            (𝓝 ((2 : ℝ) * 0)) :=
          Filter.Tendsto.const_mul (2 : ℝ) tendsto_one_div_add_atTop_nhds_zero_nat
        rw [mul_zero] at h
        exact h.congr fun n => by ring
    obtain ⟨F, hFmem, hFtend⟩ :=
      cauchySeq_tendsto_of_isComplete predual_complete (fun n => hHc n) hCauchy
    have hFc : @Continuous T ℂ (ultraweak T) _ ⇑F := hFmem
    have hev : ∀ x : T, Tendsto (fun n => H n x) atTop (𝓝 (F x)) := by
      intro x
      have hb : ∀ n, ‖H n x - F x‖ ≤ ‖H n - F‖ * ‖x‖ := by
        intro n
        simpa using (H n - F).le_opNorm x
      have h1 : Tendsto (fun n => ‖H n - F‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp hFtend
      have h0 : Tendsto (fun n => ‖H n - F‖ * ‖x‖) atTop (𝓝 0) := by
        simpa using h1.mul_const ‖x‖
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) hb h0
    have hFpos : ∀ x : T, 0 ≤ x → 0 ≤ F x := by
      intro x hx
      have h := hev x
      have hre : Tendsto (fun n => (H n x).re) atTop (𝓝 (F x).re) :=
        (Complex.continuous_re.tendsto _).comp h
      have him : Tendsto (fun n => (H n x).im) atTop (𝓝 (F x).im) :=
        (Complex.continuous_im.tendsto _).comp h
      rw [Complex.le_def]
      refine ⟨?_, ?_⟩
      · simpa using ge_of_tendsto hre (Filter.Eventually.of_forall
          fun n => (Complex.le_def.mp (hHpos n x hx)).1)
      · have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
          tendsto_const_nhds
        have heq : (fun n : ℕ => (H n x).im) = fun _ : ℕ => (0 : ℝ) := by
          funext n
          exact ((Complex.le_def.mp (hHpos n x hx)).2).symm
        rw [heq] at him
        simpa using (tendsto_nhds_unique him hz).symm
    have hFval : ∀ t : A ⊗[ℂ] B, F (TensorProduct.lift γ t) = ω' t := by
      intro t
      have h1 : Tendsto (fun n => G n t) atTop (𝓝 (F (TensorProduct.lift γ t))) := by
        have := hev (TensorProduct.lift γ t)
        simpa only [hHval] using this
      have h2 : Tendsto (fun n : ℕ => G n t) atTop (𝓝 (ω' t)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hb : ∀ n : ℕ, ‖G n t - ω' t‖ ≤ 1 / (n + 1) * tensorNorm A B t := by
          intro n
          rw [norm_sub_rev]
          exact_mod_cast hGb n t
        have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * tensorNorm A B t)
            atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
            (tensorNorm A B t)
        exact squeeze_zero (fun n => norm_nonneg _) hb h0
      exact tendsto_nhds_unique h1 h2
    -- package `F` as an np-functional
    let g : T →ₚ[ℂ] ℂ :=
      { toFun := fun x => F x
        map_add' := fun x y => by simp
        map_smul' := fun c x => by simp
        monotone' := fun x y hxy => by
          have h := hFpos (y - x) (sub_nonneg.mpr hxy)
          rw [map_sub] at h
          exact sub_nonneg.mp h }
    refine ⟨⟨g, preservesDirSups_of_continuousOn_effects_functional g
      (@Continuous.continuousOn T ℂ (ultraweak T) _ ⇑g (effects T) hFc)⟩, hFval⟩
  refine ⟨fun ω' hω' => ?_, ?_⟩
  · obtain ⟨ω, hω⟩ := hexists ω' hω'
    exact ⟨ω, hω, fun ω₂ hω₂ => huniq ω₂ ω fun s => (hω₂ s).trans (hω s).symm⟩
  refine le_antisymm (continuous_iff_le_induced.mp (tensor_basic_3 γ hγ).1) ?_
  show TopologicalSpace.induced ⇑(TensorProduct.lift γ) (ultraweak T) ≤
    ⨅ f : {f : A ⊗[ℂ] B →ₗ[ℂ] ℂ // NormLimitOfSimple A B f},
      TopologicalSpace.induced (fun t => f.1 t) inferInstance
  refine le_iInf fun f => ?_
  obtain ⟨ω, hω⟩ := hexists f.1 f.2
  have h1 : ultraweak T ≤
      TopologicalSpace.induced (fun x : T => (ω x : ℂ)) inferInstance :=
    continuous_iff_le_induced.mp (continuous_ultraweak_npFunctional ω)
  calc TopologicalSpace.induced ⇑(TensorProduct.lift γ) (ultraweak T)
      ≤ TopologicalSpace.induced ⇑(TensorProduct.lift γ)
          (TopologicalSpace.induced (fun x : T => (ω x : ℂ)) inferInstance) :=
        induced_mono h1
    _ = TopologicalSpace.induced (fun t => f.1 t) inferInstance := by
        rw [induced_compose]
        congr 1
        funext t
        exact hω t

/-- An ultraweak limit of a norm-bounded net is norm-bounded: every closed
ball is ultraweakly closed (`isClosed_ultraweak_closedBall`).  The
ultrastrong analogue is `norm_le_of_usTendsto`. -/
private theorem norm_le_of_uwTendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {x : ι → C} {y : C} {K : ℝ} (hK : 0 ≤ K) (hconv : UWTendsto x l y)
    (hbdd : ∀ i, ‖x i‖ ≤ K) : ‖y‖ ≤ K := by
  letI : TopologicalSpace C := ultraweak C
  have h := (isClosed_ultraweak_closedBall hK).mem_of_tendsto hconv
    (Filter.Eventually.of_forall fun i => by
      simpa using hbdd i)
  simpa using h

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
          ∀ x : T, ‖g x‖ ≤ M * ‖x‖) := by
  -- proc.tex:2998 verbatim: `β_⊙` is ultraweakly continuous and bounded, and
  -- by **112X** `𝒜 ⊙ ℬ` *is* an ultraweakly dense ∗-subalgebra of `𝒯` via
  -- `γ_⊙` — 112X.2 makes `γ_⊙` injective and isometric, 112X.5 identifies the
  -- ultraweak tensor topology with the one induced from `𝒯` — so **77V**
  -- `vn_extension` applies.  The "trivial details" the thesis skips are the
  -- inverse `γ_⊙⁻¹` on the subalgebra and the `‖β_γ‖ = ‖β_⊙‖` half, which
  -- needs the same 74VI approximation as 112X.4.
  classical
  have hinj : Function.Injective ⇑(TensorProduct.lift γ) := by
    intro t t' h
    have h0 : tensorNorm A B (t - t') = 0 := by
      rw [← tensor_basic_2 γ hγ, map_sub, h, sub_self, norm_zero]
    exact sub_eq_zero.mp ((tensorNorm_eq_zero_iff _).mp h0)
  have hcomp : ∀ g : T →ₗ[ℂ] C, (∀ (a : A) (b : B), g (γ a b) = β a b) →
      ∀ t : A ⊗[ℂ] B, g (TensorProduct.lift γ t) = TensorProduct.lift β t := by
    intro g hg t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simpa using hg a b
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  set S : StarSubalgebra ℂ T := tensorSpan γ hγ.miu with hSdef
  have hmemS : ∀ y : T, y ∈ S ↔ y ∈ Set.range ⇑(TensorProduct.lift γ) := by
    intro y
    rw [range_lift_eq_span, hSdef, ← SetLike.mem_coe, coe_tensorSpan]
  have hSdense : @Dense T (ultraweak T) (S : Set T) := by
    rw [hSdef, coe_tensorSpan]; exact hγ.dense
  have hsurj : ∀ s : S, ∃ t : A ⊗[ℂ] B, TensorProduct.lift γ t = (s : T) :=
    fun s => (hmemS _).mp s.2
  choose pre hpre using hsurj
  -- the linear map `f = β_⊙ ∘ γ_⊙⁻¹` on `S`
  have hprelin : ∀ s s' : S, pre (s + s') = pre s + pre s' := by
    intro s s'
    refine hinj ?_
    rw [hpre, map_add, hpre, hpre]
    rfl
  have hpresmul : ∀ (c : ℂ) (s : S), pre (c • s) = c • pre s := by
    intro c s
    refine hinj ?_
    rw [hpre, map_smul, hpre]
    rfl
  obtain ⟨M₀, hM₀0, hM₀⟩ := hb
  set f : S →ₗ[ℂ] C :=
    { toFun := fun s => TensorProduct.lift β (pre s)
      map_add' := fun s s' => by rw [hprelin, map_add]
      map_smul' := fun c s => by rw [hpresmul, map_smul]; rfl } with hfdef
  have hfcont : @Continuous S C
      (TopologicalSpace.induced Subtype.val (ultraweak T)) (ultraweak C) ⇑f := by
    have hprecont : @Continuous S (A ⊗[ℂ] B)
        (TopologicalSpace.induced Subtype.val (ultraweak T))
        (uwTensorTopology A B) pre := by
      rw [(tensor_basic_5 γ hγ).2]
      refine continuous_induced_rng.mpr ?_
      have he : ⇑(TensorProduct.lift γ) ∘ pre = (Subtype.val : S → T) := funext hpre
      rw [he]
      exact continuous_induced_dom (f := (Subtype.val : S → T)) (t := ultraweak T)
    exact @Continuous.comp S (A ⊗[ℂ] B) C
      (TopologicalSpace.induced Subtype.val (ultraweak T))
      (uwTensorTopology A B) (ultraweak C) _ _ hn hprecont
  have hfbd : ∀ s : S, ‖f s‖ ≤ M₀ * ‖(s : T)‖ := by
    intro s
    have h1 := hM₀ (pre s)
    rwa [← tensor_basic_2 γ hγ (pre s), hpre s] at h1
  obtain ⟨g0, ⟨hg0c, hg0e⟩, -⟩ := vn_extension S hSdense f hfcont M₀ hfbd
  have hg0γ : ∀ (a : A) (b : B), g0 (γ a b) = β a b := by
    intro a b
    have hmem : γ a b ∈ S := (hmemS _).mpr ⟨a ⊗ₜ[ℂ] b, by simp⟩
    have h := hg0e ⟨γ a b, hmem⟩
    have hp : pre ⟨γ a b, hmem⟩ = a ⊗ₜ[ℂ] b := by
      refine hinj ?_
      rw [hpre]
      simp
    rw [hfdef] at h
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hp] at h
    simpa using h
  have huniqg : ∀ g g' : T →ₗ[ℂ] C,
      @Continuous T C (ultraweak T) (ultraweak C) ⇑g →
      @Continuous T C (ultraweak T) (ultraweak C) ⇑g' →
      (∀ (a : A) (b : B), g (γ a b) = β a b) →
      (∀ (a : A) (b : B), g' (γ a b) = β a b) → g = g' := by
    intro g g' hgc hg'c hg hg'
    letI : TopologicalSpace T := ultraweak T
    letI : TopologicalSpace C := ultraweak C
    have _t2 : T2Space C := vn_positive_basic_1.1
    refine DFunLike.coe_injective (Continuous.ext_on hγ.dense hgc hg'c ?_)
    intro t ht
    rw [← range_lift_eq_span] at ht
    obtain ⟨u, rfl⟩ := ht
    rw [hcomp g hg u, hcomp g' hg' u]
  refine ⟨⟨g0, ⟨hg0c, hg0γ⟩, fun g' hg' => huniqg g' g0 hg'.1 hg0c hg'.2 hg0γ⟩,
    fun g hgc hg M hM => ⟨fun h x => ?_, fun h t => ?_⟩⟩
  · -- `‖β_γ‖ ≤ ‖β_⊙‖`: approximate `x` from `S` by **74VI** as in 112X.4
    have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hpos1 : (0 : ℝ) < M * ‖x‖ + 1 := by nlinarith
    have hkey : ∀ ε : ℝ, 0 < ε → ‖g x‖ ≤ M * ‖x‖ * (1 + ε) := by
      intro ε hε
      obtain ⟨ι, l, hl, s, hs, hlim⟩ := dense_subalgebra S hSdense ε hε x
      have _ : l.NeBot := hl
      have huw : UWTendsto s l x := uwweaker_2 s l x hlim
      have hgconv : UWTendsto (fun i => g (s i)) l (g x) :=
        (@Continuous.tendsto T C (ultraweak T) (ultraweak C) ⇑g hgc x).comp huw
      refine norm_le_of_uwTendsto
        (mul_nonneg (mul_nonneg hM hx0) (by linarith)) hgconv fun i => ?_
      obtain ⟨v, hv⟩ := (hmemS (s i)).mp (hs i).1
      have h1 : g (s i) = TensorProduct.lift β v := by rw [← hv, hcomp g hg v]
      rw [h1]
      refine (h v).trans ?_
      rw [← tensor_basic_2 γ hγ v, hv]
      calc M * ‖s i‖ ≤ M * (‖x‖ * (1 + ε)) :=
            mul_le_mul_of_nonneg_left (hs i).2 hM
        _ = M * ‖x‖ * (1 + ε) := by ring
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hd : (0 : ℝ) < δ / (M * ‖x‖ + 1) := div_pos hδ hpos1
    have hk := hkey _ hd
    have he : (M * ‖x‖ + 1) * (δ / (M * ‖x‖ + 1)) = δ := by field_simp
    have h2 : M * ‖x‖ * (δ / (M * ‖x‖ + 1))
        ≤ (M * ‖x‖ + 1) * (δ / (M * ‖x‖ + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hd.le
    have hexp : M * ‖x‖ * (1 + δ / (M * ‖x‖ + 1))
        = M * ‖x‖ + M * ‖x‖ * (δ / (M * ‖x‖ + 1)) := by ring
    linarith
  · -- `‖β_⊙‖ ≤ ‖β_γ‖`: immediate from 112X.2
    rw [← hcomp g hg t, ← tensor_basic_2 γ hγ t]
    exact h _

/-! ### The normal-limit lemma

**An operator-norm limit of normal functionals is normal.**  This is
**87III** `predual_complete` used as a closure property, and it is needed in
two shapes.

* `continuous_ultraweak_of_normLimit` — on a single von Neumann algebra:
  the predual is a *closed* subset of the dual, because it is complete and
  the dual is Hausdorff.  (**116III**.5 wants this shape.)
* `exists_uwExtension_of_normLimit` — on `𝒜 ⊙ ℬ`: a functional that is,
  uniformly in the tensor product norm, a limit of `uwTensorTopology`
  continuous bounded functionals is itself of the form `E ∘ γ_⊙` for a
  normal functional `E` on a tensor product `𝒯`, hence itself
  `uwTensorTopology` continuous and bounded.  This is exactly the argument
  of **112X**.5 with "sum of members of `Ω`" abstracted to "continuous and
  bounded", and it is what makes `BilinNormal` available for
  `β(a,b) = f(a) ⊗ g(b)` in **115II**: continuity into `ultraweak (𝒞 ⊗ 𝒟)`
  is tested against *every* np-functional `χ`, and only the basic ones come
  with the `∑ₖₗ odotF` decomposition that **112IX** consumes; the general
  `χ` is only an *operator-norm* limit of those (**112X**.1.2), and the
  transported limit is uniform only relative to the tensor product norm. -/

/-- **87III** `predual_complete` as a closure property: an operator-norm
limit of ultraweakly continuous functionals is ultraweakly continuous. -/
theorem continuous_ultraweak_of_normLimit (F : T →L[ℂ] ℂ)
    (h : ∀ ε > (0 : ℝ), ∃ G : T →L[ℂ] ℂ,
      (@Continuous T ℂ (ultraweak T) _ ⇑G) ∧ ‖F - G‖ ≤ ε) :
    @Continuous T ℂ (ultraweak T) _ ⇑F := by
  have hcl : IsClosed (predual T) := predual_complete.isClosed
  have hmem : F ∈ closure (predual T) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨G, hG, hFG⟩ := h (ε / 2) (by positivity)
    refine ⟨G, hG, ?_⟩
    rw [dist_eq_norm]
    linarith
  rw [hcl.closure_eq] at hmem
  exact hmem

/-- The factorisation **112IX** really produces: for bounded ultraweakly
continuous functionals `f ∈ 𝒜_*`, `g ∈ ℬ_*`, the functional `f ⊙ g` on
`𝒜 ⊙ ℬ` is the restriction along `γ_⊙` of an ultraweakly continuous
functional on `𝒯`.  (**72XI** `luws` decomposes `f` and `g` into four
np-functionals each, and `prodNP_lift` factors each of the sixteen product
functionals.  Note that **112XI** cannot be used for this: `BilinNormal`
lives in a single universe `u`, and `ℂ` is not in it.) -/
theorem exists_uwExtension_odotF (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hγ : IsTensorProduct γ) (f : A →ₗ[ℂ] ℂ) (g : B →ₗ[ℂ] ℂ)
    (hfc : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hgc : @Continuous B ℂ (ultraweak B) _ ⇑g) :
    ∃ E : T →L[ℂ] ℂ, (@Continuous T ℂ (ultraweak T) _ ⇑E) ∧
      ∀ t : A ⊗[ℂ] B, E (TensorProduct.lift γ t) = odotF f g t := by
  classical
  obtain ⟨F, hF⟩ := ((luws f).out 1 2).mp hfc
  obtain ⟨G, hG⟩ := ((luws g).out 1 2).mp hgc
  set co : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I] with hcodef
  have hnpA : ∀ (σ : NPFunctional A) (a : A), npLin σ a = σ a := fun _ _ => rfl
  have hnpB : ∀ (τ : NPFunctional B) (b : B), npLin τ b = τ b := fun _ _ => rfl
  have hfsum : ∀ a : A, f a = ∑ k, co k * npLin (F k) a := by
    intro a
    rw [Fin.sum_univ_four, hF a]
    simp only [hnpA, hcodef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, one_mul]
    ring
  have hgsum : ∀ b : B, g b = ∑ l, co l * npLin (G l) b := by
    intro b
    rw [Fin.sum_univ_four, hG b]
    simp only [hnpB, hcodef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, one_mul]
    ring
  have happ : ∀ t : A ⊗[ℂ] B, odotF f g t = ∑ k : Fin 4, ∑ l : Fin 4,
      (co k * co l) * odotF (npLin (F k)) (npLin (G l)) t := by
    have hsplit : odotF f g = ∑ k : Fin 4, ∑ l : Fin 4,
        (co k * co l) • odotF (npLin (F k)) (npLin (G l)) := by
      refine TensorProduct.ext' fun a b => ?_
      rw [odotF_tmul, hfsum a, hgsum b, Finset.sum_mul_sum]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, odotF_tmul]
      exact Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => by ring
    intro t
    rw [hsplit]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine ⟨∑ k : Fin 4, ∑ l : Fin 4,
    (co k * co l) • npCLM (prodNP hγ (F k) (G l)), ?_, fun t => ?_⟩
  · letI : TopologicalSpace T := ultraweak T
    have hfun : ⇑(∑ k : Fin 4, ∑ l : Fin 4,
        (co k * co l) • npCLM (prodNP hγ (F k) (G l)))
        = fun x : T => ∑ k : Fin 4, ∑ l : Fin 4,
          (co k * co l) * (prodNP hγ (F k) (G l) x : ℂ) := by
      funext x
      simp [ContinuousLinearMap.sum_apply]
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
      continuous_const.mul (continuous_ultraweak_npFunctional _)
  · rw [happ t]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      npCLM_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [prodNP_lift hγ]

/-- **The normal-limit lemma** (**112X**.5's own route, ending in **87III**
`predual_complete`): if a functional `ν` on `𝒜 ⊙ ℬ` is, uniformly in the
tensor product norm, a limit of restrictions along `γ_⊙` of normal
functionals on `𝒯`, then `ν` is itself such a restriction.

The point is that the operator-norm distance of two normal functionals on
`𝒯` is *computed* by their restrictions along `γ_⊙` (**112X**.4), so the
approximants form a Cauchy sequence in the predual `𝒯_*`, which is complete
(**87III**). -/
theorem exists_uwExtension_of_normLimit (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hγ : IsTensorProduct γ) (ν : A ⊗[ℂ] B →ₗ[ℂ] ℂ)
    (h : ∀ ε > (0 : ℝ), ∃ E : T →L[ℂ] ℂ, (@Continuous T ℂ (ultraweak T) _ ⇑E) ∧
      ∀ t, ‖ν t - E (TensorProduct.lift γ t)‖ ≤ ε * tensorNorm A B t) :
    ∃ E : T →L[ℂ] ℂ, (@Continuous T ℂ (ultraweak T) _ ⇑E) ∧
      ∀ t, E (TensorProduct.lift γ t) = ν t := by
  choose H hHc happ using fun n : ℕ => h (1 / (n + 1)) (by positivity)
  -- the sequence is Cauchy in the predual, by **112X**.4
  have hdiff : ∀ n m : ℕ, ‖H n - H m‖ ≤ 1 / (n + 1) + 1 / (m + 1) := by
    intro n m
    have hMnm : (0 : ℝ) ≤ 1 / (n + 1) + 1 / (m + 1) := by positivity
    have hc : @Continuous T ℂ (ultraweak T) _ ⇑(H n - H m) := by
      letI : TopologicalSpace T := ultraweak T
      have he : ⇑(H n - H m) = fun x : T => H n x - H m x := by funext x; simp
      rw [he]
      exact (hHc n).sub (hHc m)
    refine ContinuousLinearMap.opNorm_le_bound _ hMnm ?_
    refine (tensor_basic_4 γ hγ (H n - H m) hc _ hMnm).mp ?_
    intro t
    rw [ContinuousLinearMap.sub_apply]
    have e : H n (TensorProduct.lift γ t) - H m (TensorProduct.lift γ t)
        = -(ν t - H n (TensorProduct.lift γ t)) + (ν t - H m (TensorProduct.lift γ t)) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    have h1 := happ n t
    have h2 := happ m t
    rw [add_mul]
    push_cast at *
    linarith
  have hCauchy : CauchySeq H := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 / (N + 1)) ?_ ?_
    · intro n m N hn hm
      rw [dist_eq_norm]
      refine (hdiff n m).trans ?_
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / (N + 1) := by
        apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast by omega]
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / (N + 1) := by
        apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast by omega]
      have h3 : (2 : ℝ) / (N + 1) = 1 / (N + 1) + 1 / (N + 1) := by ring
      linarith
    · have hz : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop
          (𝓝 ((2 : ℝ) * 0)) :=
        Filter.Tendsto.const_mul (2 : ℝ) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [mul_zero] at hz
      exact hz.congr fun n => by ring
  obtain ⟨F, hFmem, hFtend⟩ :=
    cauchySeq_tendsto_of_isComplete predual_complete (fun n => hHc n) hCauchy
  refine ⟨F, hFmem, fun t => ?_⟩
  have hev : Tendsto (fun n => H n (TensorProduct.lift γ t)) atTop
      (𝓝 (F (TensorProduct.lift γ t))) := by
    have hb : ∀ n, ‖H n (TensorProduct.lift γ t) - F (TensorProduct.lift γ t)‖
        ≤ ‖H n - F‖ * ‖TensorProduct.lift γ t‖ := by
      intro n
      simpa using (H n - F).le_opNorm (TensorProduct.lift γ t)
    have h1 : Tendsto (fun n => ‖H n - F‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hFtend
    have h0 : Tendsto (fun n => ‖H n - F‖ * ‖TensorProduct.lift γ t‖) atTop (𝓝 0) := by
      simpa using h1.mul_const ‖TensorProduct.lift γ t‖
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hb h0
  have h2 : Tendsto (fun n : ℕ => H n (TensorProduct.lift γ t)) atTop (𝓝 (ν t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ n : ℕ, ‖H n (TensorProduct.lift γ t) - ν t‖
        ≤ 1 / (n + 1) * tensorNorm A B t := by
      intro n
      rw [norm_sub_rev]
      exact_mod_cast happ n t
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * tensorNorm A B t)
        atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
        (tensorNorm A B t)
    exact squeeze_zero (fun n => norm_nonneg _) hb h0
  exact tendsto_nhds_unique hev h2

/-- A functional of the form `E ∘ γ_⊙` for a normal `E` on `𝒯` is continuous
for the ultraweak tensor product topology (**112X**.3.1) and bounded by
`‖E‖` (**112X**.2). -/
theorem uwTensor_continuous_of_uwExtension (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hγ : IsTensorProduct γ) (ν : A ⊗[ℂ] B →ₗ[ℂ] ℂ) (E : T →L[ℂ] ℂ)
    (hEc : @Continuous T ℂ (ultraweak T) _ ⇑E)
    (hEval : ∀ t, E (TensorProduct.lift γ t) = ν t) :
    (@Continuous _ ℂ (uwTensorTopology A B) _ ⇑ν) ∧
      ∀ t, ‖ν t‖ ≤ ‖E‖ * tensorNorm A B t := by
  refine ⟨?_, fun t => ?_⟩
  · letI : TopologicalSpace (A ⊗[ℂ] B) := uwTensorTopology A B
    letI : TopologicalSpace T := ultraweak T
    have hfun : ⇑ν = ⇑E ∘ ⇑(TensorProduct.lift γ) := funext fun t => (hEval t).symm
    rw [hfun]
    exact hEc.comp (tensor_basic_3 γ hγ).1
  · rw [← hEval t, ← tensor_basic_2 γ hγ t]
    exact E.le_opNorm _

end TensorBasic

/-! ## Parsec 1130: completely positive bilinear maps -/

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B]
  [StarOrderedRing B] in
/-- **113II** (proc.tex:3012, Exercise): an mi-bilinear map between von
Neumann algebras is completely positive. -/
theorem mi_bilinear_cp (β : A →ₗ[ℂ] B →ₗ[ℂ] C) (hm : BilinMult β)
    (hi : BilinStar β) : BilinCP β := by
  -- The exercise's index entry points at Schur's product theorem, but no
  -- Schur is needed: multiplicativity and involution-preservation turn
  -- `β(aᵢ*aⱼ, bᵢ*bⱼ)` into `β(aᵢ,bᵢ)* β(aⱼ,bⱼ)`, so the whole double sum
  -- collapses to `x* x` with `x = ∑ᵢ β(aᵢ,bᵢ)cᵢ`.
  intro n a b c
  have key : ∀ i j : Fin n,
      star (c i) * β (star (a i) * a j) (star (b i) * b j) * c j
        = star (β (a i) (b i) * c i) * (β (a j) (b j) * c j) := by
    intro i j
    rw [hm (star (a i)) (a j) (star (b i)) (b j), ← hi (a i) (b i),
      star_mul, mul_assoc, mul_assoc, mul_assoc]
  calc (0 : C) ≤ star (∑ i, β (a i) (b i) * c i) * (∑ i, β (a i) (b i) * c i) :=
        star_mul_self_nonneg _
    _ = ∑ i, ∑ j, star (c i) * β (star (a i) * a j) (star (b i) * b j) * c j := by
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (key i j).symm

/-- **113III** (proc.tex:3018, Notation): the entrywise bilinear map
`M_N β : M_N(𝒜) × M_N(ℬ) → M_N(𝒞)`,
`(M_N β)(A, B)ᵢⱼ = β(Aᵢⱼ, Bᵢⱼ)` (as a plain function). -/
def matBilin (β : A →ₗ[ℂ] B →ₗ[ℂ] C) (N : ℕ)
    (M : CStarMatrix (Fin N) (Fin N) A)
    (M' : CStarMatrix (Fin N) (Fin N) B) :
    CStarMatrix (Fin N) (Fin N) C :=
  CStarMatrix.ofMatrix (Matrix.of fun i j => β (M i j) (M' i j))

/-! ### Auxiliaries for **113IV**

The exercise's "positivity of `M_N β`" is stated through the criterion of
cstar.tex **33II** (`cstar_matrix_positive_iff`, proved), and the passage
between the two is always the same: a positive matrix is `X* X`, so its
entries are `Mᵢⱼ = ∑ₖ Xₖᵢ* Xₖⱼ`, and bilinearity turns a double sum into a
sum of instances of the definition of complete positivity. -/

private theorem sum_comm₃ {N : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → Fin N → M) :
    ∑ i, ∑ j, ∑ k, h i j k = ∑ k, ∑ i, ∑ j, h i j k := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]

private theorem sum_comm₄ {N : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → Fin N → Fin N → M) :
    ∑ i, ∑ j, ∑ k, ∑ l, h i j k l = ∑ k, ∑ l, ∑ i, ∑ j, h i j k l := by
  rw [sum_comm₃ (fun i j k => ∑ l, h i j k l)]
  exact Finset.sum_congr rfl fun k _ => sum_comm₃ (fun i j l => h i j k l)

/-- `0 ≤ a` gives `a = b* b`; stated for an abstract C*-algebra because
typeclass search cannot find the functional calculus instances for
`CStarMatrix` directly (the same dodge as in `A/CStar/Matrices.lean`). -/
private theorem exists_star_mul_self {M : Type*} [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] {a : M} (ha : 0 ≤ a) :
    ∃ b, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha

/-- A positive matrix over a C*-algebra is `X* X`, entrywise
`Mᵢⱼ = ∑ₖ Xₖᵢ* Xₖⱼ`. -/
private theorem exists_star_repr_of_nonneg {N : ℕ}
    (M : CStarMatrix (Fin N) (Fin N) A) (hM : 0 ≤ M) :
    ∃ X : Fin N → Fin N → A, ∀ i j, M i j = ∑ k, star (X k i) * X k j := by
  obtain ⟨Y, hY⟩ := exists_star_mul_self hM
  refine ⟨fun k i => Y k i, fun i j => ?_⟩
  rw [hY, CStarMatrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [CStarMatrix.star_apply]

/-- A cp-map applied entrywise to a positive matrix keeps it positive (in
the quadratic-form form of **33II**). -/
private theorem cp_matrix_nonneg {D E : Type u} [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (h : D →ₗ[ℂ] E)
    (hh : Theses.A.CStar.IsCompletelyPositiveMap h) {N : ℕ}
    (P : CStarMatrix (Fin N) (Fin N) D) (hP : 0 ≤ P) (c : Fin N → E) :
    0 ≤ ∑ i, ∑ j, star (c i) * h (P i j) * c j := by
  obtain ⟨Z, hZ⟩ := exists_star_repr_of_nonneg P hP
  have hrw : ∑ i, ∑ j, star (c i) * h (P i j) * c j
      = ∑ k, ∑ i, ∑ j, star (c i) * h (star (Z k i) * Z k j) * c j := by
    rw [← sum_comm₃ (fun i j k => star (c i) * h (star (Z k i) * Z k j) * c j)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hZ i j, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [hrw]
  exact Finset.sum_nonneg fun k _ => hh N (fun i => Z k i) c

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
          0 ≤ ∑ i, ∑ j, star (c i) * matBilin β N M M' i j * c j := by
  constructor
  · -- (1) ⇒ (3): decompose both positive matrices as `X* X`, `Y* Y` and
    -- expand by bilinearity; each of the resulting `N²` double sums is an
    -- instance of complete positivity of `β`.
    intro hβ N M M' hM hM' c
    obtain ⟨X, hX⟩ := exists_star_repr_of_nonneg M
      ((Theses.A.CStar.cstar_matrix_positive_iff M).mpr hM)
    obtain ⟨Y, hY⟩ := exists_star_repr_of_nonneg M'
      ((Theses.A.CStar.cstar_matrix_positive_iff M').mpr hM')
    have hrw : ∑ i, ∑ j, star (c i) * matBilin β N M M' i j * c j
        = ∑ k, ∑ l, ∑ i, ∑ j, star (c i) *
            β (star (X k i) * X k j) (star (Y l i) * Y l j) * c j := by
      rw [← sum_comm₄ (fun i j k l => star (c i) *
        β (star (X k i) * X k j) (star (Y l i) * Y l j) * c j)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hb : β (M i j) (M' i j)
          = ∑ k, ∑ l, β (star (X k i) * X k j) (star (Y l i) * Y l j) := by
        have hfst : β (∑ k, star (X k i) * X k j)
            = ∑ k, β (star (X k i) * X k j) := map_sum β _ _
        rw [hX i j, hY i j, hfst, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun k _ => map_sum _ _ _
      show star (c i) * β (M i j) (M' i j) * c j = _
      rw [hb, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hrw]
    exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      hβ N (fun i => X k i) (fun i => Y l i) c
  · -- (3) ⇒ (1): apply it to the Gram matrices `(aᵢ* aⱼ)`, `(bᵢ* bⱼ)`,
    -- positive by **33II**.3.
    intro h n a b c
    have hM : ∀ x : Fin n → A, 0 ≤ ∑ i, ∑ j,
        star (x i) * (CStarMatrix.ofMatrix
          (Matrix.of fun i j => star (a i) * a j) :
            CStarMatrix (Fin n) (Fin n) A) i j * x j :=
      fun x => (Theses.A.CStar.cstar_matrix_positive_iff _).mp
        (Theses.A.CStar.cstar_matrix_star_mul_nonneg a) x
    have hM' : ∀ y : Fin n → B, 0 ≤ ∑ i, ∑ j,
        star (y i) * (CStarMatrix.ofMatrix
          (Matrix.of fun i j => star (b i) * b j) :
            CStarMatrix (Fin n) (Fin n) B) i j * y j :=
      fun y => (Theses.A.CStar.cstar_matrix_positive_iff _).mp
        (Theses.A.CStar.cstar_matrix_star_mul_nonneg b) y
    exact h n _ _ hM hM' c

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
    (hβ' : ∀ a b, β' a b = h (β (f a) (g b))) : BilinCP β' := by
  -- `M_N f` and `M_N g` send the Gram matrices to positive matrices (that
  -- is complete positivity of `f`, `g`, verbatim), `cp_bilinear` sends
  -- those to a positive matrix, and `M_N h` keeps it positive.
  intro n a b c
  set M : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (a i) * a j)) with hMdef
  set M' : CStarMatrix (Fin n) (Fin n) B :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => g (star (b i) * b j)) with hM'def
  have hMq : ∀ x : Fin n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j :=
    fun x => hf n a x
  have hM'q : ∀ y : Fin n → B, 0 ≤ ∑ i, ∑ j, star (y i) * M' i j * y j :=
    fun y => hg n b y
  have hP : 0 ≤ matBilin β n M M' :=
    (Theses.A.CStar.cstar_matrix_positive_iff _).mpr
      ((cp_bilinear β).mp hβ n M M' hMq hM'q)
  have hfin := cp_matrix_nonneg h hh (matBilin β n M M') hP c
  refine le_of_le_of_eq hfin ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hβ' (star (a i) * a j) (star (b i) * b j)]
  rfl


/-! **113II** together with **113IV**, in the unbundled form in which
thesis B's `IsVNTensor` (dils.tex 165II) supplies its data (`M_N t` sends a
pair of positive matrices to a positive one), is stated and proved as
`Theses.A.CStar.matBilin_nonneg_of_mi` in `A/CStar/Matrices.lean`: its
content is about matrices over C*-algebras, and `B/Dils` needs it but does
not import `A/Proc`.  See `QUESTIONS.md` D3. -/

/-! ## Parsec 1140: extra universal properties and uniqueness -/

/-! ### Auxiliaries for **114I** and **114II**

Both exercises extend an identity from the ultraweakly dense ∗-subalgebra
`γ_⊙(𝒜 ⊙ ℬ)` to all of `𝒯`.  For the *linear* identities (multiplicativity,
involution, unitality) separate ultraweak continuity (**45IV**
`mult_uws_cont` and `continuous_ultraweak_star` below) suffices; for the
*quadratic* ones (positivity, complete positivity) it does not, and one needs
`uwTendsto_starMul`: along a norm-bounded ultrastrongly convergent net,
`s_α* t_α → s* t` **ultraweakly**.  That is Cauchy–Schwarz for `‖·‖_ω`
(**72III**.1b, `norm_apply_star_mul_le`) applied to the splitting
`s_α* t_α − s* t = s_α*(t_α − t) + (s_α − s)* t`. -/

section DensityAux

variable {A₄ : Type*} [CStarAlgebra A₄] [PartialOrder A₄] [StarOrderedRing A₄]

/-- The involution is ultraweakly continuous: `ω(a*) = ω(a)*` for every
np-functional `ω` (cstar.tex 10IV), so `continuous_ultraweak_of_forall`
applies. -/
theorem continuous_ultraweak_star :
    @Continuous A₄ A₄ (ultraweak A₄) (ultraweak A₄) (fun a => star a) := by
  letI : TopologicalSpace A₄ := ultraweak A₄
  refine continuous_ultraweak_of_forall _ fun ω => ?_
  have h : (fun x : A₄ => (ω (star x) : ℂ)) = fun x : A₄ => star (ω x) :=
    funext fun x => npFunctional_star ω x
  rw [h]
  exact (continuous_ultraweak_npFunctional ω).star

/-- If `u_α → u` and `v_α → v` ultrastrongly and the `u_α` are norm bounded,
then `u_α* v_α → u* v` **ultraweakly** — the quantitative content of
**45VI** `mult-jus-cont` that the extension arguments of 114I need.  (Only
the `u`-net has to be bounded.) -/
theorem uwTendsto_starMul {ι : Type*} {l : Filter ι} {u v : ι → A₄} {x y : A₄}
    {K : ℝ} (hK : ∀ i, ‖u i‖ ≤ K) (hu : USTendsto u l x) (hv : USTendsto v l y) :
    UWTendsto (fun i => star (u i) * v i) l (star x * y) := by
  rw [uwTendsto_iff]
  intro ω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ i, ‖ω (star (u i) * v i) - ω (star x * y)‖
      ≤ K * omegaNorm A₄ ω 1 * omegaNorm A₄ ω (v i - y)
        + omegaNorm A₄ ω (u i - x) * omegaNorm A₄ ω y := by
    intro i
    have e : star (u i) * v i - star x * y
        = star (u i) * (v i - y) + star (u i - x) * y := by
      rw [star_sub]; noncomm_ring
    have h1 : ω (star (u i) * v i) - ω (star x * y)
        = ω (star (u i) * (v i - y)) + ω (star (u i - x) * y) := by
      rw [← npFunctional_sub, e, npFunctional_add]
    rw [h1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_apply_star_mul_le ω (u i) (v i - y)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (omegaNorm_nonneg ω _)
      have h2 := omegaNorm_mul_le ω (u i) 1
      rw [mul_one] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right (hK i) (omegaNorm_nonneg ω 1))
    · exact norm_apply_star_mul_le ω (u i - x) y
  have hz : Tendsto (fun i => K * omegaNorm A₄ ω 1 * omegaNorm A₄ ω (v i - y)
      + omegaNorm A₄ ω (u i - x) * omegaNorm A₄ ω y) l (𝓝 0) := by
    have h1 := (usTendsto_iff v l y).mp hv ω
    have h2 := (usTendsto_iff u l x).mp hu ω
    simpa using (h1.const_mul (K * omegaNorm A₄ ω 1)).add
      (h2.mul_const (omegaNorm A₄ ω y))
  exact squeeze_zero (fun i => norm_nonneg _) hbd hz

/-! ### The ultraweak topology as a topological **ℂ**-vector space, and the
norm as a supremum over *subunital* np-functionals

Two facts about a single von Neumann algebra that `A/VN` does not record and
that **116III**.2 and **116IV**.1 need.  `A/VN` has `ultraweak_continuousSMul`
only for `ℝ` (that is what Krein–Milman in **86IX** needs) and **21VII**
`order_separating_norm` only for *unital* maps, while the collection of
np-functionals with `ω(1) ≤ 1` — the one the tensor product norm runs over —
is subunital. -/

/-- The ultraweak topology makes `A` a topological **ℂ**-vector space: it is
an infimum of topologies induced by `ℂ`-linear maps, so the `ℝ`-argument of
`ultraweak_continuousSMul` works verbatim over `ℂ`. -/
theorem ultraweak_continuousSMul_complex :
    @ContinuousSMul ℂ A₄ _ _ (ultraweak A₄) := by
  rw [ultraweak]
  refine continuousSMul_iInf fun ω => ?_
  exact continuousSMul_induced ω.toPositiveLinearMap.toLinearMap

/-- `‖p‖ = sup {ω(p) : ω np-functional with ω(1) ≤ 1}` for positive `p`, in
the `ε`-form.  **21VII** `order_separating_norm` gives the same supremum only
over *unital* maps, and the rescaling `ω ↦ ω(1)⁻¹ω` is unavailable when
`ω(1) = 0`; so this is proved instead from **87VI** `norm_predual` and **86IX**
`polar_decomposition_of_functional`: the polar decomposition turns a normal
`f` in the unit ball into the np-functional `|f| = f(u(·))` with
`|f|(1) = f(u) = ‖f‖ ≤ 1` (**86XIV** `functional_norm`), and Cauchy–Schwarz
for `‖·‖_{|f|}` at `(√p·u)* √p = u* p` gives `|f(p)|² ≤ ‖p‖·|f|(p)`. -/
theorem exists_npFunctional_polar [VonNeumannAlgebra A₄] (f : A₄ →L[ℂ] ℂ)
    (hfc : @Continuous A₄ ℂ (ultraweak A₄) _ ⇑f) :
    ∃ (u : A₄) (σ : NPFunctional A₄), IsPartialIsometry A₄ u ∧
      (∀ a : A₄, (σ a : ℂ) = f (u * a)) ∧
      (∀ a : A₄, (f a : ℂ) = f (u * star u * a)) ∧
      (σ 1 : ℂ) = ((‖f‖ : ℝ) : ℂ) := by
  obtain ⟨u, hpi, h1, -, hpos, -⟩ :=
    polar_decomposition_of_functional (f : A₄ →L[ℂ] ℂ).toLinearMap
      (by
        letI : TopologicalSpace A₄ := ultraweak A₄
        exact hfc.continuousOn)
  let g : A₄ →ₚ[ℂ] ℂ :=
    { toFun := fun a => f (u * a)
      map_add' := fun x y => by simp only [mul_add, map_add]
      map_smul' := fun s x => by
        simp only [RingHom.id_apply, mul_smul_comm, map_smul, smul_eq_mul]
      monotone' := fun a b hab => by
        have h0 : (0 : ℂ) ≤ f (u * (b - a)) := hpos _ (sub_nonneg.mpr hab)
        rw [mul_sub, map_sub, sub_nonneg] at h0
        exact h0 }
  have hcont : @ContinuousOn A₄ ℂ (ultraweak A₄) _ ⇑g (effects A₄) := by
    letI : TopologicalSpace A₄ := ultraweak A₄
    have hmul : Continuous (fun a : A₄ => u * a) := (mult_uws_cont u).1
    exact (hfc.continuousOn).comp hmul.continuousOn (fun a _ => Set.mem_univ _)
  refine ⟨u, ⟨g, preservesDirSups_of_continuousOn_effects_functional g hcont⟩,
    hpi, fun _ => rfl, fun a => h1 a, ?_⟩
  show f (u * 1) = ((‖f‖ : ℝ) : ℂ)
  rw [mul_one]
  exact functional_norm f hfc u hpi hpos h1

/-- A partial isometry has `u* u ≤ 1`: `1 − u* u` is a projection. -/
theorem starMulSelf_le_one_of_isPartialIsometry [VonNeumannAlgebra A₄] {u : A₄}
    (hpi : IsPartialIsometry A₄ u) : star u * u ≤ (1 : A₄) := by
  have hproj : IsStarProjection (star u * u) :=
    ((partial_isometry_equivalents u).out 0 1).mp hpi
  have hi : (star u * u) * (star u * u) = star u * u := hproj.isIdempotentElem.eq
  have hsa : star (star u * u) = star u * u := hproj.isSelfAdjoint.star_eq
  have he : (1 : A₄) - star u * u
      = star ((1 : A₄) - star u * u) * ((1 : A₄) - star u * u) := by
    rw [star_sub, star_one, hsa]
    have hexp : ((1 : A₄) - star u * u) * ((1 : A₄) - star u * u)
        = 1 - star u * u - star u * u + (star u * u) * (star u * u) := by
      noncomm_ring
    rw [hexp, hi]
    abel
  have h0 : (0 : A₄) ≤ 1 - star u * u := by rw [he]; exact star_mul_self_nonneg _
  exact sub_nonneg.mp h0

theorem exists_npFunctional_ge_norm_sub [VonNeumannAlgebra A₄] {p : A₄}
    (hp : 0 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : NPFunctional A₄, (σ 1).re ≤ 1 ∧ ‖p‖ - ε ≤ (σ p).re := by
  rcases le_or_gt ‖p‖ ε with hsmall | hbig
  · refine ⟨zeroNP, ?_, ?_⟩
    · show ((0 : ℂ)).re ≤ 1; simp
    · show ‖p‖ - ε ≤ ((0 : ℂ)).re
      simp only [Complex.zero_re]
      linarith
  have hp0 : (0 : ℝ) < ‖p‖ := lt_of_le_of_lt hε.le hbig
  -- **87VI**: a normal `f` in the unit ball with `‖f p‖` close to `‖p‖`
  have hnub : (‖p‖ - ε / 2) ∉
      upperBounds {r : ℝ | ∃ f ∈ predual A₄, ‖f‖ ≤ 1 ∧ r = ‖f p‖} := by
    intro hub
    have := (norm_predual p).2 hub
    linarith
  rw [mem_upperBounds] at hnub
  push_neg at hnub
  obtain ⟨r, ⟨f, hfmem, hf1, rfl⟩, hfp⟩ := hnub
  have hfc : @Continuous A₄ ℂ (ultraweak A₄) _ ⇑f := hfmem
  -- **86IX** + **86XIV**: the np-functional `|f| = f(u ·)` with `|f|(1) = ‖f‖`
  obtain ⟨u, σ, hpi, hσapp, h1', hσone⟩ := exists_npFunctional_polar f hfc
  have hule : star u * u ≤ (1 : A₄) := starMulSelf_le_one_of_isPartialIsometry hpi
  have hσ1 : (σ (1 : A₄)).re ≤ 1 := by rw [hσone, Complex.ofReal_re]; exact hf1
  refine ⟨σ, hσ1, ?_⟩
  -- Cauchy–Schwarz for `‖·‖_σ`: `‖f p‖ ≤ √‖p‖ · √(σ p)`
  have hsq : CFC.sqrt p * CFC.sqrt p = p := CFC.sqrt_mul_sqrt_self p hp
  have hsqsa : star (CFC.sqrt p) = CFC.sqrt p :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  have hkey : (σ (star u * p) : ℂ) = f p := by
    rw [hσapp, ← mul_assoc, ← h1' p]
  have hrew : star (CFC.sqrt p * u) * CFC.sqrt p = star u * p := by
    rw [star_mul, hsqsa, mul_assoc, hsq]
  have hcs := norm_apply_star_mul_le σ (CFC.sqrt p * u) (CFC.sqrt p)
  rw [hrew, hkey] at hcs
  have hom_p : omegaNorm A₄ σ (CFC.sqrt p) = Real.sqrt (σ p).re := by
    rw [omegaNorm, hsqsa, hsq]
  have hom_u : omegaNorm A₄ σ u ≤ 1 := by
    have hmono : (σ (star u * u)).re ≤ (σ (1 : A₄)).re := by
      have h := npFunctional_mono σ hule
      simpa using (Complex.le_def.mp h).1
    rw [omegaNorm]
    calc Real.sqrt (σ (star u * u)).re ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt (hmono.trans hσ1)
      _ = 1 := Real.sqrt_one
  have hnsq : ‖CFC.sqrt p‖ = Real.sqrt ‖p‖ := by
    have h : ‖CFC.sqrt p‖ * ‖CFC.sqrt p‖ = ‖p‖ := by
      rw [← CStarRing.norm_star_mul_self, hsqsa, hsq]
    rw [← h, Real.sqrt_mul_self (norm_nonneg _)]
  have hom_pu : omegaNorm A₄ σ (CFC.sqrt p * u) ≤ Real.sqrt ‖p‖ := by
    refine (omegaNorm_mul_le σ (CFC.sqrt p) u).trans ?_
    rw [hnsq]
    calc Real.sqrt ‖p‖ * omegaNorm A₄ σ u ≤ Real.sqrt ‖p‖ * 1 :=
          mul_le_mul_of_nonneg_left hom_u (Real.sqrt_nonneg _)
      _ = Real.sqrt ‖p‖ := mul_one _
  have hfinal : ‖f p‖ ≤ Real.sqrt (‖p‖ * (σ p).re) := by
    refine hcs.trans ?_
    rw [hom_p, Real.sqrt_mul (norm_nonneg p)]
    exact mul_le_mul_of_nonneg_right hom_pu (Real.sqrt_nonneg _)
  have hlt : ‖p‖ - ε / 2 < Real.sqrt (‖p‖ * (σ p).re) := lt_of_lt_of_le hfp hfinal
  have hpos2 : (0 : ℝ) < ‖p‖ - ε / 2 := by linarith
  have hsqlt : (‖p‖ - ε / 2) ^ 2 < ‖p‖ * (σ p).re := by
    have h := (Real.lt_sqrt (by positivity)).mp hlt
    linarith
  nlinarith [sq_nonneg ε, hp0]

/-- The `‖·‖_σ` form of the previous lemma: `‖a‖ ≤ sup_σ σ(a* a)^½` over
np-functionals with `σ(1) ≤ 1`.  (Apply the previous lemma at `p = a* a` with
`ε' = 2‖a‖ε − ε²`.) -/
theorem exists_npFunctional_ge_omegaNorm_sub [VonNeumannAlgebra A₄] (a : A₄)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : NPFunctional A₄, (σ 1).re ≤ 1 ∧
      ‖a‖ - ε ≤ Real.sqrt (σ (star a * a)).re := by
  rcases le_or_gt ‖a‖ ε with h | h
  · refine ⟨zeroNP, by show ((0 : ℂ)).re ≤ 1; simp, ?_⟩
    have hz : (zeroNP (star a * a) : ℂ) = 0 := rfl
    rw [hz]
    simp only [Complex.zero_re, Real.sqrt_zero]
    linarith
  · have hna : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    obtain ⟨σ, hσ1, hσa⟩ :=
      exists_npFunctional_ge_norm_sub (p := star a * a) (star_mul_self_nonneg a)
        (ε := 2 * ‖a‖ * ε - ε ^ 2) (by nlinarith)
    refine ⟨σ, hσ1, ?_⟩
    have hnorm : ‖star a * a‖ = ‖a‖ * ‖a‖ := CStarRing.norm_star_mul_self
    rw [hnorm] at hσa
    have hge : (‖a‖ - ε) ^ 2 ≤ (σ (star a * a)).re := by nlinarith
    calc ‖a‖ - ε = Real.sqrt ((‖a‖ - ε) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt (σ (star a * a)).re := Real.sqrt_le_sqrt hge

end DensityAux

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
      (Theses.A.CStar.IsCompletelyPositiveMap g ↔ BilinCP β) := by
  -- Each of the five is an identity on the ultraweakly dense ∗-subalgebra
  -- `γ_⊙(𝒜 ⊙ ℬ)` extended to `𝒯`; `hn` and `hb` are not needed, since the
  -- extension `g` is *given*.  The linear clauses (1)–(3) use separate
  -- ultraweak continuity of multiplication and of the involution; the
  -- quadratic clauses (4)–(5) use `uwTendsto_starMul` along the bounded
  -- ultrastrong net of **74VI** `dense_subalgebra`, plus ultraweak closedness
  -- of the positive cone (**44XI**.2).
  classical
  letI : TopologicalSpace T := ultraweak T
  letI : TopologicalSpace C := ultraweak C
  haveI _t2C : T2Space C := vn_positive_basic_1.1
  have hcomp : ∀ t : A ⊗[ℂ] B,
      g (TensorProduct.lift γ t) = TensorProduct.lift β t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simpa using hg a b
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  have hdense : Dense (Set.range ⇑(TensorProduct.lift γ)) := by
    rw [range_lift_eq_span]; exact hγ.dense
  have hext : ∀ p q : T → C, Continuous p → Continuous q →
      (∀ t : A ⊗[ℂ] B, p (TensorProduct.lift γ t) = q (TensorProduct.lift γ t)) →
      ∀ x, p x = q x := by
    intro p q hp hq h x
    exact congrFun (Continuous.ext_on hdense hp hq
      (by rintro _ ⟨t, rfl⟩; exact h t)) x
  -- `β_⊙(s* t)` expanded on representations of `s`, `t` by pure tensors
  have hliftq : ∀ {N M : ℕ} (a : Fin N → A) (b : Fin N → B)
      (a' : Fin M → A) (b' : Fin M → B),
      TensorProduct.lift β (star (∑ k, a k ⊗ₜ[ℂ] b k) * ∑ l, a' l ⊗ₜ[ℂ] b' l)
        = ∑ k, ∑ l, β (star (a k) * a' l) (star (b k) * b' l) := by
    intro N M a b a' b'
    rw [star_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have he : star (a k ⊗ₜ[ℂ] b k) * (a' l ⊗ₜ[ℂ] b' l)
        = (star (a k) * a' l) ⊗ₜ[ℂ] (star (b k) * b' l) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [he, TensorProduct.lift.tmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `β_γ` is multiplicative iff `β` is
    constructor
    · intro hm a a' b b'
      rw [← hg (a * a') (b * b'), ← hg a b, ← hg a' b', hγ.miu.2.1 a a' b b', hm]
    · intro hmβ
      have step1 : ∀ s t : A ⊗[ℂ] B,
          g (TensorProduct.lift γ s * TensorProduct.lift γ t)
            = g (TensorProduct.lift γ s) * g (TensorProduct.lift γ t) := by
        intro s t
        rw [← lift_mul γ hγ.miu.2.1, hcomp, hcomp, hcomp, lift_mul β hmβ]
      have step2 : ∀ (t : A ⊗[ℂ] B) (x : T),
          g (x * TensorProduct.lift γ t) = g x * g (TensorProduct.lift γ t) := by
        intro t
        refine hext (fun z => g (z * TensorProduct.lift γ t))
          (fun z => g z * g (TensorProduct.lift γ t)) ?_ ?_ (fun s => step1 s t)
        · exact hgc.comp (mult_uws_cont _).2.1
        · exact (mult_uws_cont (g (TensorProduct.lift γ t))).2.1.comp hgc
      intro x y
      refine hext (fun z => g (x * z)) (fun z => g x * g z) ?_ ?_
        (fun t => step2 t x) y
      · exact hgc.comp (mult_uws_cont x).1
      · exact (mult_uws_cont (g x)).1.comp hgc
  · -- (2) `β_γ` is involution preserving iff `β` is
    constructor
    · intro hi a b
      rw [← hg a b, ← hi, hγ.miu.2.2 a b]
      exact hg _ _
    · intro hsβ x
      refine hext (fun z => g (star z)) (fun z => star (g z)) ?_ ?_ (fun t => ?_) x
      · exact hgc.comp continuous_ultraweak_star
      · exact continuous_ultraweak_star.comp hgc
      · rw [← lift_star γ hγ.miu.2.2, hcomp, hcomp, lift_star β hsβ]
  · -- (3) `β_γ` is unital iff `β` is — immediate from `γ(1,1) = 1`
    have h1 : g (1 : T) = β 1 1 := by
      have h := hg 1 1
      rwa [hγ.miu.1] at h
    rw [h1]
    exact Iff.rfl
  · -- (4) `β_γ` is positive iff `∑ᵢⱼ β(aᵢ*aⱼ, bᵢ*bⱼ) ≥ 0`
    constructor
    · intro hp n a b
      have hz : (0 : T) ≤ star (∑ i, γ (a i) (b i)) * ∑ i, γ (a i) (b i) :=
        star_mul_self_nonneg _
      have hexp : star (∑ i, γ (a i) (b i)) * (∑ i, γ (a i) (b i))
          = ∑ i, ∑ j, γ (star (a i) * a j) (star (b i) * b j) := by
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hγ.miu.2.2 (a i) (b i), ← hγ.miu.2.1]
      have hgs : g (∑ i, ∑ j, γ (star (a i) * a j) (star (b i) * b j))
          = ∑ i, ∑ j, β (star (a i) * a j) (star (b i) * b j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => hg _ _
      rw [← hgs, ← hexp]
      exact hp _ hz
    · intro H x hx
      obtain ⟨y, rfl⟩ := exists_star_mul_self hx
      obtain ⟨ι, l, hl, s, hs, hlim⟩ :=
        dense_subalgebra (tensorSpan γ hγ.miu) hγ.dense 1 one_pos y
      have _ : l.NeBot := hl
      have hconv : UWTendsto (fun i => star (s i) * s i) l (star y * y) :=
        uwTendsto_starMul (K := ‖y‖ * (1 + 1)) (fun i => (hs i).2) hlim hlim
      have hgconv : Tendsto (fun i => g (star (s i) * s i)) l (𝓝 (g (star y * y))) :=
        (hgc.tendsto _).comp hconv
      refine (vn_positive_basic_2.1).mem_of_tendsto hgconv
        (Filter.Eventually.of_forall fun i => ?_)
      obtain ⟨t, ht⟩ : s i ∈ Set.range ⇑(TensorProduct.lift γ) := by
        rw [range_lift_eq_span]; exact (hs i).1
      show (0 : C) ≤ g (star (s i) * s i)
      rw [← ht, ← lift_star γ hγ.miu.2.2, ← lift_mul γ hγ.miu.2.1, hcomp]
      obtain ⟨N, a, b, rfl⟩ := exists_fin_repr t
      rw [hliftq a b a b]
      exact H N a b
  · -- (5) `β_γ` is completely positive iff `β` is
    constructor
    · intro hcpg n a b c
      refine le_of_le_of_eq (hcpg n (fun i => γ (a i) (b i)) c) ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      congr 2
      rw [hγ.miu.2.2 (a i) (b i), ← hγ.miu.2.1, hg]
    · intro hcpβ n u c
      -- first for families from `γ_⊙(𝒜 ⊙ ℬ)`: expanding each `tᵢ` into pure
      -- tensors turns the quadratic form into an instance of `BilinCP β`
      -- indexed by `Σ i, Fin (Nᵢ) ≃ Fin (∑ᵢ Nᵢ)`
      have hbase : ∀ (m : ℕ) (t : Fin m → A ⊗[ℂ] B) (d : Fin m → C),
          0 ≤ ∑ i, ∑ j, star (d i) *
            g (star (TensorProduct.lift γ (t i)) *
              TensorProduct.lift γ (t j)) * d j := by
        intro m t d
        choose N a b hab using fun i => exists_fin_repr (t i)
        set F : ((i : Fin m) × Fin (N i)) → ((i : Fin m) × Fin (N i)) → C :=
          fun p q => star (d p.1) *
            β (star (a p.1 p.2) * a q.1 q.2) (star (b p.1 p.2) * b q.1 q.2) * d q.1
          with hF
        set e := (finSigmaFinEquiv (n := N)) with he
        have key := hcpβ (∑ i, N i) (fun p => a (e.symm p).1 (e.symm p).2)
          (fun p => b (e.symm p).1 (e.symm p).2) (fun p => d (e.symm p).1)
        have hsig : ∑ p, ∑ q, F p q
            = ∑ p' : Fin (∑ i, N i), ∑ q' : Fin (∑ i, N i),
                F (e.symm p') (e.symm q') := by
          refine (Fintype.sum_equiv e.symm _ _ ?_).symm
          intro p'
          exact Fintype.sum_equiv e.symm (fun q' => F (e.symm p') (e.symm q'))
            (fun q => F (e.symm p') q) (fun _ => rfl)
        have h1 : (0 : C) ≤ ∑ p, ∑ q, F p q := by
          rw [hsig]; simpa only [hF] using key
        have hval : ∀ i j : Fin m,
            ∑ k, ∑ l, F ⟨i, k⟩ ⟨j, l⟩
              = star (d i) * g (star (TensorProduct.lift γ (t i)) *
                  TensorProduct.lift γ (t j)) * d j := by
          intro i j
          have hgt : g (star (TensorProduct.lift γ (t i)) *
              TensorProduct.lift γ (t j))
              = ∑ k, ∑ l, β (star (a i k) * a j l) (star (b i k) * b j l) := by
            rw [← lift_star γ hγ.miu.2.2, ← lift_mul γ hγ.miu.2.1, hcomp,
              hab i, hab j, hliftq (a i) (b i) (a j) (b j)]
          rw [hgt, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
        have hfull : ∑ p, ∑ q, F p q
            = ∑ i, ∑ j, star (d i) * g (star (TensorProduct.lift γ (t i)) *
                TensorProduct.lift γ (t j)) * d j := by
          rw [Fintype.sum_sigma (fun p => ∑ q, F p q)]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hinner : ∀ k : Fin (N i),
              (∑ q, F ⟨i, k⟩ q) = ∑ j, ∑ l, F ⟨i, k⟩ ⟨j, l⟩ :=
            fun k => Fintype.sum_sigma (fun q => F ⟨i, k⟩ q)
          rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hinner k),
            Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => hval i j
        rwa [hfull] at h1
      -- and then for arbitrary `uᵢ ∈ 𝒯`, approximating all `n` of them
      -- simultaneously along the product of the `n` nets of **74VI**
      have happrox : ∀ x : T, ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧
          ∃ s : ι → T,
            (∀ i, s i ∈ tensorSpan γ hγ.miu ∧ ‖s i‖ ≤ ‖x‖ * (1 + 1)) ∧
              USTendsto s l x :=
        fun x => dense_subalgebra (tensorSpan γ hγ.miu) hγ.dense 1 one_pos x
      choose ι l hl s hs hlim using happrox
      haveI hlb : ∀ i : Fin n, (l (u i)).NeBot := fun i => hl (u i)
      set L : Filter (∀ i : Fin n, ι (u i)) := Filter.pi (fun i => l (u i)) with hL
      haveI hLne : L.NeBot := by rw [hL]; infer_instance
      set S : Fin n → (∀ i : Fin n, ι (u i)) → T := fun i x => s (u i) (x i) with hS
      have hSlim : ∀ i, USTendsto (S i) L (u i) := fun i =>
        (hlim (u i)).comp (tendsto_eval_pi (fun i => l (u i)) i)
      have hconv : ∀ i j : Fin n,
          UWTendsto (fun x => star (S i x) * S j x) L (star (u i) * u j) :=
        fun i j => uwTendsto_starMul (K := ‖u i‖ * (1 + 1))
          (fun x => (hs (u i) (x i)).2) (hSlim i) (hSlim j)
      have hsum : Tendsto
          (fun x => ∑ i, ∑ j, star (c i) * g (star (S i x) * S j x) * c j) L
          (𝓝 (∑ i, ∑ j, star (c i) * g (star (u i) * u j) * c j)) := by
        rw [show (𝓝 (∑ i, ∑ j, star (c i) * g (star (u i) * u j) * c j))
            = @nhds C (ultraweak C) _ from rfl]
        rw [← UWTendsto, uwTendsto_iff]
        intro χ
        have hterm : ∀ i j : Fin n,
            Tendsto (fun x => (χ (star (c i) * g (star (S i x) * S j x) * c j) : ℂ))
              L (𝓝 (χ (star (c i) * g (star (u i) * u j) * c j))) := by
          intro i j
          exact ((continuous_ultraweak_conj χ (star (c i)) (c j)).tendsto _).comp
            ((hgc.tendsto _).comp (hconv i j))
        have hexpand : ∀ (z : Fin n → Fin n → C),
            (χ (∑ i, ∑ j, star (c i) * z i j * c j) : ℂ)
              = ∑ i, ∑ j, (χ (star (c i) * z i j * c j) : ℂ) := by
          intro z
          show npLin χ _ = _
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => map_sum (npLin χ) _ _
        simp only [hexpand]
        exact tendsto_finsetSum _ fun i _ =>
          tendsto_finsetSum _ fun j _ => hterm i j
      refine (vn_positive_basic_2.1).mem_of_tendsto hsum
        (Filter.Eventually.of_forall fun x => ?_)
      have hmem : ∀ i : Fin n, ∃ t : A ⊗[ℂ] B, TensorProduct.lift γ t = S i x := by
        intro i
        have hmm := (hs (u i) (x i)).1
        rw [← SetLike.mem_coe, coe_tensorSpan, ← range_lift_eq_span] at hmm
        exact hmm
      choose t ht using hmem
      have hb' := hbase n t c
      show (0 : C) ≤ ∑ i, ∑ j, star (c i) * g (star (S i x) * S j x) * c j
      simpa only [ht] using hb'

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
      ∀ ψ : NMIUMap T T', (∀ a b, ψ (γ a b) = γ' a b) → ψ = φ := by
  -- Each of `γ`, `γ'` is a normal bounded bilinear map — normality is
  -- **112X**.3.1 and boundedness is the isometry **112X**.2 — so **112XI**
  -- extends each along the other, and the two composites are the identity by
  -- 112XI's own uniqueness clause.  Multiplicativity, involution preservation
  -- and unitality of the extension are **114I**.1/.2/.3 read off `γ'`'s
  -- miu-bilinearity, and normality of the resulting ∗-isomorphism is free
  -- (`starAlgEquiv_preservesDirSups'`).  Uniqueness among *nmiu*-maps is
  -- 112XI's uniqueness again, since a normal positive map is ultraweakly
  -- continuous (**44XV** `p_uwcont`).
  classical
  letI : TopologicalSpace T := ultraweak T
  letI : TopologicalSpace T' := ultraweak T'
  have hnb : ∀ {T₀ : Type u} [CStarAlgebra T₀] [PartialOrder T₀]
      [StarOrderedRing T₀] [VonNeumannAlgebra T₀] (δ : A →ₗ[ℂ] B →ₗ[ℂ] T₀),
      IsTensorProduct δ → BilinNormal δ ∧ BilinBounded δ := by
    intro T₀ _ _ _ _ δ hδ
    exact ⟨(tensor_basic_3 δ hδ).1, ⟨1, zero_le_one, fun t => by
      rw [tensor_basic_2 δ hδ t, one_mul]⟩⟩
  obtain ⟨hn', hb'⟩ := hnb γ' hγ'
  obtain ⟨hn, hb⟩ := hnb γ hγ
  obtain ⟨⟨φ₀, ⟨hφc, hφe⟩, hφu⟩, -⟩ := tensor_universal_property γ hγ γ' hn' hb'
  obtain ⟨⟨ψ₀, ⟨hψc, hψe⟩, -⟩, -⟩ := tensor_universal_property γ' hγ' γ hn hb
  obtain ⟨⟨gT, -, huniqT⟩, -⟩ := tensor_universal_property γ hγ γ hn hb
  obtain ⟨⟨gT', -, huniqT'⟩, -⟩ := tensor_universal_property γ' hγ' γ' hn' hb'
  have hid1 : ∀ x : T, ψ₀ (φ₀ x) = x := by
    have h1 := huniqT (ψ₀.comp φ₀) ⟨hψc.comp hφc, fun a b => by
      rw [LinearMap.comp_apply, hφe, hψe]⟩
    have h2 := huniqT (LinearMap.id) ⟨continuous_id, fun _ _ => rfl⟩
    intro x
    exact congrArg (fun f : T →ₗ[ℂ] T => f x) (h1.trans h2.symm)
  have hid2 : ∀ y : T', φ₀ (ψ₀ y) = y := by
    have h1 := huniqT' (φ₀.comp ψ₀) ⟨hφc.comp hψc, fun a b => by
      rw [LinearMap.comp_apply, hψe, hφe]⟩
    have h2 := huniqT' (LinearMap.id) ⟨continuous_id, fun _ _ => rfl⟩
    intro y
    exact congrArg (fun f : T' →ₗ[ℂ] T' => f y) (h1.trans h2.symm)
  have hbij : Function.Bijective ⇑φ₀ :=
    ⟨Function.LeftInverse.injective hid1, Function.RightInverse.surjective hid2⟩
  obtain ⟨hm, hs, hu, -, -⟩ :=
    tensor_universal_property_extra γ hγ γ' hn' hb' φ₀ hφc hφe
  have hmult := hm.mpr hγ'.miu.2.1
  have hstar := hs.mpr hγ'.miu.2.2
  have hunit := hu.mpr hγ'.miu.1
  set Φ : T →⋆ₐ[ℂ] T' :=
    { toFun := ⇑φ₀
      map_one' := hunit
      map_mul' := hmult
      map_zero' := map_zero φ₀
      map_add' := map_add φ₀
      commutes' := fun r => by
        show φ₀ (algebraMap ℂ T r) = algebraMap ℂ T' r
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          map_smul, hunit]
      map_star' := hstar } with hΦ
  refine ⟨{ toStarAlgHom := Φ
            preservesDirSups' :=
              starAlgEquiv_preservesDirSups' (StarAlgEquiv.ofBijective Φ hbij) },
          fun a b => hφe a b, hbij, ?_⟩
  intro ψ hψ
  have hψcont : @Continuous T T' (ultraweak T) (ultraweak T') ⇑(nmiuLin ψ) :=
    ((p_uwcont (nmiuP ψ)).out 2 0).mp ψ.preservesDirSups'
  have heq : nmiuLin ψ = φ₀ := hφu (nmiuLin ψ) ⟨hψcont, hψ⟩
  refine DFunLike.ext _ _ fun x => ?_
  exact congrArg (fun f : T →ₗ[ℂ] T' => f x) heq

/-- The functional case of **114I**.4, proved separately because 114I cannot
be applied to a `ℂ`-valued bilinear map: `BilinNormal` confines its three
algebras to a single universe `u`, and `ℂ` is not in it.  An ultraweakly
continuous functional on `𝒯` which is nonnegative on `γ_⊙(v* v)` is
positive — by **74VI** `dense_subalgebra` plus `uwTendsto_starMul`, exactly
as in 114I. -/
theorem nonneg_of_nonneg_on_tensorSpan (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hγ : IsTensorProduct γ) (E : T →L[ℂ] ℂ)
    (hEc : @Continuous T ℂ (ultraweak T) _ ⇑E)
    (hE : ∀ v : A ⊗[ℂ] B, 0 ≤ E (TensorProduct.lift γ (star v * v)))
    {x : T} (hx : 0 ≤ x) : 0 ≤ E x := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  obtain ⟨ι, l, hl, s, hs, hlim⟩ :=
    dense_subalgebra (tensorSpan γ hγ.miu) hγ.dense 1 one_pos y
  have _ : l.NeBot := hl
  have huw : UWTendsto (fun i => star (s i) * s i) l (star y * y) :=
    uwTendsto_starMul (fun i => (hs i).2) hlim hlim
  have hconv : Tendsto (fun i => E (star (s i) * s i)) l (𝓝 (E (star y * y))) :=
    (@Continuous.tendsto T ℂ (ultraweak T) _ ⇑E hEc _).comp huw
  have hnn : ∀ i, 0 ≤ E (star (s i) * s i) := by
    intro i
    have hmem : s i ∈ Set.range ⇑(TensorProduct.lift γ) := by
      rw [range_lift_eq_span]; exact (hs i).1
    obtain ⟨v, hv⟩ := hmem
    have he : star (s i) * s i = TensorProduct.lift γ (star v * v) := by
      rw [← hv, ← lift_star γ hγ.miu.2.2, ← lift_mul γ hγ.miu.2.1]
    rw [he]
    exact hE v
  have hre : Tendsto (fun i => (E (star (s i) * s i)).re) l (𝓝 (E (star y * y)).re) :=
    (Complex.continuous_re.tendsto _).comp hconv
  have him : Tendsto (fun i => (E (star (s i) * s i)).im) l (𝓝 (E (star y * y)).im) :=
    (Complex.continuous_im.tendsto _).comp hconv
  rw [Complex.le_def]
  refine ⟨?_, ?_⟩
  · simpa using ge_of_tendsto hre (Filter.Eventually.of_forall
      fun i => (Complex.le_def.mp (hnn i)).1)
  · have hz : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 (0 : ℝ)) := tendsto_const_nhds
    have heq : (fun i : ι => (E (star (s i) * s i)).im) = fun _ : ι => (0 : ℝ) :=
      funext fun i => ((Complex.le_def.mp (hnn i)).2).symm
    rw [heq] at him
    simpa using (tendsto_nhds_unique him hz).symm

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
theorem vnTensorProduct_nonempty : Nonempty (VNTensorProduct 𝒜 ℬ) := by
  obtain ⟨ι, f, SA, hSA, hfmem, hfsurj, hfinj⟩ := ngns_ulift.{u, v} 𝒜
  obtain ⟨κ, g, SB, hSB, hgmem, hgsurj, hginj⟩ := ngns_ulift.{v, u} ℬ
  obtain ⟨γ₀, -, hγ₀⟩ := special_tensor SA SB hSA hSB
  exact ⟨{ carrier := _
           map := γ₀.compl₁₂ (nmiuLin (nmiuCorestrict f SA hSA hfmem))
             (nmiuLin (nmiuCorestrict g SB hSB hgmem))
           isTensorProduct := isTensorProduct_comp _
             (nmiuCorestrict_bijective f SA hSA hfmem hfinj hfsurj) _
             (nmiuCorestrict_bijective g SB hSB hgmem hginj hgsurj) hγ₀ }⟩

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

/-! ### Infrastructure for **115II**: the cp-Cauchy–Schwarz step

proc.tex:3210 bounds `β_⊙` for `β(a,b) = f(a) ⊗ g(b)` through the inequality
`β_⊙(s)* β_⊙(s) ≤ ‖f‖‖g‖ β_⊙(s* s)`, which it derives from **34XIV**
`cp-cs` applied to the amplification `M_n f` and the row matrix
`A = (a₁ … a_n; 0)`.  We take the same inequality but avoid amplifying `f`:
`cp_cs_sum` is `cp-cs` for a *vector* of arguments (proved by applying
`cstar_positive_2x2matrix` to the 2×2 compression of the positive matrix
`(f(vᵢ* vⱼ))` along `v = (a₁,…,a_n,1)`), and `tmap_cs` then splits
`‖f(1)‖‖g(1)‖ Q ⊗ Q' − P ⊗ P'` into `P⊗R' + R⊗P' + R⊗R'` with
`R = ‖f(1)‖Q − P ≥ 0`, each summand positive by
`Theses.A.CStar.matBilin_nonneg_of_mi` (**113II**+**113IV** for the
miu-bilinear `⊗`).  This replaces the thesis's `M_n ⊗` bookkeeping. -/

open Theses.A.CStar in
theorem cp_cs_sum {A₅ B₅ : Type u} [CStarAlgebra A₅] [PartialOrder A₅]
    [StarOrderedRing A₅] [CStarAlgebra B₅] [PartialOrder B₅]
    [StarOrderedRing B₅] (f : A₅ →ₗ[ℂ] B₅)
    (hf : Theses.A.CStar.IsCompletelyPositiveMap f)
    {n : ℕ} (a : Fin n → A₅) (c : Fin n → B₅) :
    star (∑ i, f (a i) * c i) * (∑ i, f (a i) * c i)
      ≤ ((‖f 1‖ : ℝ) : ℂ) • ∑ i, ∑ j, star (c i) * f (star (a i) * a j) * c j := by
  classical
  set z : B₅ := ∑ i, f (a i) * c i with hz
  set Q : B₅ := ∑ i, ∑ j, star (c i) * f (star (a i) * a j) * c j with hQ
  set v : Fin (n + 1) → A₅ := Fin.snoc a 1 with hv
  have hfstar : ∀ x : A₅, f (star x) = star (f x) :=
    cstar_p_implies_i f (astara_pos_basic_2_cp f hf)
  have hcp2 : ∀ (N : ℕ) (x : Fin N → A₅),
      (0 : CStarMatrix (Fin N) (Fin N) B₅) ≤
        CStarMatrix.ofMatrix (Matrix.of fun i j => f (star (x i) * x j)) :=
    ((cp_iff f).out 0 2).mp hf
  have hG := hcp2 (n+1) v
  have hq : ∀ w : Fin (n+1) → B₅,
      0 ≤ ∑ i, ∑ j, star (w i) * f (star (v i) * v j) * w j := by
    intro w
    have h := (cstar_matrix_positive_iff _).mp hG w
    simpa using h
  have hstarz : star z = ∑ i, star (c i) * f (star (a i)) := by
    rw [hz, star_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul, hfstar]
  have hexp : ∀ x y : B₅,
      ∑ i, ∑ j, star ((Fin.snoc (fun i => c i * x) y : Fin (n+1) → B₅) i) *
          f (star (v i) * v j) * ((Fin.snoc (fun i => c i * x) y : Fin (n+1) → B₅) j)
        = star x * Q * x + star x * star z * y
          + (star y * z * x + star y * f 1 * y) := by
    intro x y
    set w : Fin (n+1) → B₅ := Fin.snoc (fun i => c i * x) y with hw
    have hwc : ∀ i : Fin n, w i.castSucc = c i * x := fun i => by
      rw [hw]; exact Fin.snoc_castSucc _ _ _
    have hwl : w (Fin.last n) = y := by rw [hw]; exact Fin.snoc_last _ _
    have hvc : ∀ i : Fin n, v i.castSucc = a i := fun i => by
      rw [hv]; exact Fin.snoc_castSucc _ _ _
    have hvl : v (Fin.last n) = 1 := by rw [hv]; exact Fin.snoc_last _ _
    have hinner : ∀ i : Fin (n+1),
        ∑ j, star (w i) * f (star (v i) * v j) * w j
          = (∑ j : Fin n, star (w i) * f (star (v i) * a j) * (c j * x))
            + star (w i) * f (star (v i)) * y := by
      intro i
      rw [Fin.sum_univ_castSucc]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by rw [hvc, hwc]
      · rw [hwl, hvl, mul_one]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
      Finset.sum_add_distrib, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have e1 : ∑ i : Fin n, ∑ j : Fin n,
        star (w i.castSucc) * f (star (v i.castSucc) * a j) * (c j * x)
          = star x * Q * x := by
      rw [hQ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hwc, hvc, star_mul]
      noncomm_ring
    have e2 : ∑ j : Fin n, star (w (Fin.last n)) * f (star (v (Fin.last n)) * a j)
        * (c j * x) = star y * z * x := by
      rw [hz, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hwl, hvl, star_one, one_mul]
      noncomm_ring
    have e3 : ∑ i : Fin n, star (w i.castSucc) * f (star (v i.castSucc)) * y
        = star x * star z * y := by
      rw [hstarz, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwc, hvc, star_mul]
      noncomm_ring
    have e4 : star (w (Fin.last n)) * f (star (v (Fin.last n))) * y
        = star y * f 1 * y := by
      rw [hwl, hvl, star_one]
    rw [e1, e2, e3, e4]
    abel
  set M : CStarMatrix (Fin 2) (Fin 2) B₅ :=
    CStarMatrix.ofMatrix (Matrix.of ![![Q, star z], ![z, f 1]]) with hM
  have hM00 : M 0 0 = Q := rfl
  have hM01 : M 0 1 = star z := rfl
  have hM11 : M 1 1 = f 1 := rfl
  have hMpos : (0 : CStarMatrix (Fin 2) (Fin 2) B₅) ≤ M := by
    rw [cstar_matrix_positive_iff]
    intro e
    have h := hq ((Fin.snoc (fun i => c i * (e 0)) (e 1) : Fin (n+1) → B₅))
    rw [hexp (e 0) (e 1)] at h
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    show 0 ≤ star (e 0) * M 0 0 * e 0 + star (e 0) * M 0 1 * e 1
      + (star (e 1) * M 1 0 * e 0 + star (e 1) * M 1 1 * e 1)
    rw [hM00, hM01, hM11, show M 1 0 = z from rfl]
    exact h
  obtain ⟨-, h2⟩ := cstar_positive_2x2matrix M hMpos
  rw [hM00, hM01, hM11, star_star] at h2
  rwa [show (((‖f 1‖ : ℝ) : ℂ)) • Q = (‖f 1‖ : ℝ) • Q from by
    rw [← IsScalarTower.algebraMap_smul ℂ (‖f 1‖ : ℝ) Q, Complex.coe_algebraMap]]

open Theses.A.CStar in
/-- The cp-Cauchy–Schwarz step of **115II**. -/
theorem tmap_cs (F : A →ₗ[ℂ] C) (G : B →ₗ[ℂ] D)
    (hF : Theses.A.CStar.IsCompletelyPositiveMap F)
    (hG : Theses.A.CStar.IsCompletelyPositiveMap G)
    {n : ℕ} (a : Fin n → A) (b : Fin n → B) :
    star (∑ i, (F (a i)) ⊗ᵥ (G (b i))) * (∑ i, (F (a i)) ⊗ᵥ (G (b i)))
      ≤ ((‖F 1‖ * ‖G 1‖ : ℝ) : ℂ) •
        ∑ i, ∑ j, (F (star (a i) * a j)) ⊗ᵥ (G (star (b i) * b j)) := by
  classical
  set vt : C → D → VNT C D := fun x y => x ⊗ᵥ y with hvt
  have hmiu := (vnTensor C D).isTensorProduct.miu
  have hl : ∀ (x x' : C) (y : D), vt (x + x') y = vt x y + vt x' y := by
    intro x x' y
    show (vnTensor C D).map (x + x') y = _
    rw [map_add]; rfl
  have hr : ∀ (x : C) (y y' : D), vt x (y + y') = vt x y + vt x y' := by
    intro x y y'
    show (vnTensor C D).map x (y + y') = _
    rw [map_add]; rfl
  have hmul : ∀ (x x' : C) (y y' : D), vt x y * vt x' y' = vt (x * x') (y * y') :=
    fun x x' y y' => (hmiu.2.1 x x' y y').symm
  have hstar : ∀ (x : C) (y : D), star (vt x y) = vt (star x) (star y) :=
    fun x y => hmiu.2.2 x y
  have hvtsmul : ∀ (r s : ℂ) (x : C) (y : D),
      vt (r • x) (s • y) = (r * s) • vt x y := by
    intro r s x y
    show ((vnTensor C D).map (r • x)) (s • y) = _
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [mul_comm s r]
    rfl
  set K₁ : ℂ := ((‖F 1‖ : ℝ) : ℂ) with hK₁
  set K₂ : ℂ := ((‖G 1‖ : ℝ) : ℂ) with hK₂
  set p : Fin n → Fin n → C := fun i j => star (F (a i)) * F (a j) with hp
  set q : Fin n → Fin n → C := fun i j => K₁ • F (star (a i) * a j) with hq
  set p' : Fin n → Fin n → D := fun i j => star (G (b i)) * G (b j) with hp'
  set q' : Fin n → Fin n → D := fun i j => K₂ • G (star (b i) * b j) with hq'
  set r : Fin n → Fin n → C := fun i j => q i j - p i j with hrr
  set r' : Fin n → Fin n → D := fun i j => q' i j - p' i j with hrr'
  have hPpos : (0 : CStarMatrix (Fin n) (Fin n) C) ≤
      CStarMatrix.ofMatrix (Matrix.of p) := cstar_matrix_star_mul_nonneg _
  have hP'pos : (0 : CStarMatrix (Fin n) (Fin n) D) ≤
      CStarMatrix.ofMatrix (Matrix.of p') := cstar_matrix_star_mul_nonneg _
  have hRpos : (0 : CStarMatrix (Fin n) (Fin n) C) ≤
      CStarMatrix.ofMatrix (Matrix.of r) := by
    rw [cstar_matrix_positive_iff]
    intro c
    have hcs := cp_cs_sum F hF a c
    have hlhs : star (∑ i, F (a i) * c i) * (∑ i, F (a i) * c i)
        = ∑ i, ∑ j, star (c i) * p i j * c j := by
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]
      show _ = star (c i) * (star (F (a i)) * F (a j)) * c j
      noncomm_ring
    have hrhs : K₁ • (∑ i, ∑ j, star (c i) * F (star (a i) * a j) * c j)
        = ∑ i, ∑ j, star (c i) * q i j * c j := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show K₁ • (star (c i) * F (star (a i) * a j) * c j)
        = star (c i) * (K₁ • F (star (a i) * a j)) * c j
      rw [mul_smul_comm, smul_mul_assoc]
    rw [hlhs, hrhs] at hcs
    have hsub : ∑ i, ∑ j, star (c i) *
        (CStarMatrix.ofMatrix (Matrix.of r) : CStarMatrix (Fin n) (Fin n) C) i j * c j
        = (∑ i, ∑ j, star (c i) * q i j * c j)
          - ∑ i, ∑ j, star (c i) * p i j * c j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      show star (c i) * (q i j - p i j) * c j = _
      noncomm_ring
    rw [hsub, sub_nonneg]
    exact hcs
  have hR'pos : (0 : CStarMatrix (Fin n) (Fin n) D) ≤
      CStarMatrix.ofMatrix (Matrix.of r') := by
    rw [cstar_matrix_positive_iff]
    intro c
    have hcs := cp_cs_sum G hG b c
    have hlhs : star (∑ i, G (b i) * c i) * (∑ i, G (b i) * c i)
        = ∑ i, ∑ j, star (c i) * p' i j * c j := by
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]
      show _ = star (c i) * (star (G (b i)) * G (b j)) * c j
      noncomm_ring
    have hrhs : K₂ • (∑ i, ∑ j, star (c i) * G (star (b i) * b j) * c j)
        = ∑ i, ∑ j, star (c i) * q' i j * c j := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show K₂ • (star (c i) * G (star (b i) * b j) * c j)
        = star (c i) * (K₂ • G (star (b i) * b j)) * c j
      rw [mul_smul_comm, smul_mul_assoc]
    rw [hlhs, hrhs] at hcs
    have hsub : ∑ i, ∑ j, star (c i) *
        (CStarMatrix.ofMatrix (Matrix.of r') : CStarMatrix (Fin n) (Fin n) D) i j * c j
        = (∑ i, ∑ j, star (c i) * q' i j * c j)
          - ∑ i, ∑ j, star (c i) * p' i j * c j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      show star (c i) * (q' i j - p' i j) * c j = _
      noncomm_ring
    rw [hsub, sub_nonneg]
    exact hcs
  have hcross : ∀ (M : Fin n → Fin n → C) (M' : Fin n → Fin n → D),
      (0 : CStarMatrix (Fin n) (Fin n) C) ≤ CStarMatrix.ofMatrix (Matrix.of M) →
      (0 : CStarMatrix (Fin n) (Fin n) D) ≤ CStarMatrix.ofMatrix (Matrix.of M') →
      0 ≤ ∑ i, ∑ j, vt (M i j) (M' i j) := by
    intro M M' hM hM'
    have h := matBilin_nonneg_of_mi vt hl hr hmul hstar
      (CStarMatrix.ofMatrix (Matrix.of M)) (CStarMatrix.ofMatrix (Matrix.of M'))
      hM hM' (fun _ => 1)
    simpa using h
  -- expand
  have hLHS : star (∑ i, (F (a i)) ⊗ᵥ (G (b i))) * (∑ i, (F (a i)) ⊗ᵥ (G (b i)))
      = ∑ i, ∑ j, vt (p i j) (p' i j) := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (vt (F (a i)) (G (b i))) * vt (F (a j)) (G (b j)) = _
    rw [hstar, hmul]
  have hRHS : ((‖F 1‖ * ‖G 1‖ : ℝ) : ℂ) •
      ∑ i, ∑ j, (F (star (a i) * a j)) ⊗ᵥ (G (star (b i) * b j))
      = ∑ i, ∑ j, vt (q i j) (q' i j) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hq, hq']
    show _ = vt (K₁ • F (star (a i) * a j)) (K₂ • G (star (b i) * b j))
    rw [hvtsmul, hK₁, hK₂, ← Complex.ofReal_mul]
  have hqp : ∀ i j, q i j = p i j + r i j := by
    intro i j; simp only [hrr]; abel
  have hqp' : ∀ i j, q' i j = p' i j + r' i j := by
    intro i j; simp only [hrr']; abel
  have hterm : ∀ i j : Fin n, vt (q i j) (q' i j)
      = vt (p i j) (p' i j) + vt (p i j) (r' i j) + vt (r i j) (p' i j)
        + vt (r i j) (r' i j) := by
    intro i j
    rw [hqp i j, hqp' i j, hl, hr, hr]
    abel
  have hsum : ∑ i, ∑ j, vt (q i j) (q' i j)
      = (∑ i, ∑ j, vt (p i j) (p' i j)) + (∑ i, ∑ j, vt (p i j) (r' i j))
        + (∑ i, ∑ j, vt (r i j) (p' i j)) + (∑ i, ∑ j, vt (r i j) (r' i j)) := by
    simp only [hterm, Finset.sum_add_distrib]
  rw [hLHS, hRHS, hsum]
  have h0 : (0 : VNT C D) ≤ (∑ i, ∑ j, vt (p i j) (r' i j))
      + (∑ i, ∑ j, vt (r i j) (p' i j)) + ∑ i, ∑ j, vt (r i j) (r' i j) :=
    add_nonneg (add_nonneg (hcross p r' hPpos hR'pos) (hcross r p' hRpos hP'pos))
      (hcross r r' hRpos hR'pos)
  rw [show ((∑ i, ∑ j, vt (p i j) (p' i j)) + (∑ i, ∑ j, vt (p i j) (r' i j))
        + (∑ i, ∑ j, vt (r i j) (p' i j)) + (∑ i, ∑ j, vt (r i j) (r' i j)))
      = (∑ i, ∑ j, vt (p i j) (p' i j)) + ((∑ i, ∑ j, vt (p i j) (r' i j))
        + (∑ i, ∑ j, vt (r i j) (p' i j)) + ∑ i, ∑ j, vt (r i j) (r' i j)) from
    by abel]
  exact le_add_of_nonneg_right h0

/-! ### 116III.1, moved forward because **115II** uses it

Positivity and monotonicity of `⊗` are needed for the bound
`f(1) ⊗ g(1) ≤ ‖f(1)‖‖g(1)‖·1` in the proof of `BilinBounded` below. -/

/-- The first half of **116III**.1: `a ⊗ b ≥ 0` for positive `a` and `b`. -/
theorem vtmul_nonneg (a : A) (b : B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a ⊗ᵥ b := by
  -- `a ⊗ b = (√a)*(√a) ⊗ (√b)*(√b) = (√a ⊗ √b)* (√a ⊗ √b)`, by
  -- multiplicativity and involution-preservation of `⊗` (108I).
  have hsa : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have hsb : star (CFC.sqrt b) = CFC.sqrt b :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq
  have ha' : a = star (CFC.sqrt a) * CFC.sqrt a := by
    rw [hsa, CFC.sqrt_mul_sqrt_self a ha]
  have hb' : b = star (CFC.sqrt b) * CFC.sqrt b := by
    rw [hsb, CFC.sqrt_mul_sqrt_self b hb]
  have hmul := (vnTensor A B).isTensorProduct.miu.2.1
    (star (CFC.sqrt a)) (CFC.sqrt a) (star (CFC.sqrt b)) (CFC.sqrt b)
  have hstar := (vnTensor A B).isTensorProduct.miu.2.2 (CFC.sqrt a) (CFC.sqrt b)
  show (0 : VNT A B) ≤ (vnTensor A B).map a b
  rw [ha', hb', hmul, ← hstar]
  exact star_mul_self_nonneg _

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 1:
`a ⊗ b ≥ 0` for positive `a`, `b`; hence `a₁ ⊗ b₁ ≤ a₂ ⊗ b₂` for
`0 ≤ a₁ ≤ a₂` and `0 ≤ b₁ ≤ b₂`. -/
theorem tensor_simple_facts_1 (a : A) (b : B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a ⊗ᵥ b ∧
      ∀ (a₂ : A) (b₂ : B), a ≤ a₂ → b ≤ b₂ → a ⊗ᵥ b ≤ a₂ ⊗ᵥ b₂ := by
  refine ⟨vtmul_nonneg a b ha hb, fun a₂ b₂ ha₂ hb₂ => ?_⟩
  -- `a₂ ⊗ b₂ - a ⊗ b = (a₂ - a) ⊗ b₂ + a ⊗ (b₂ - b)`, both terms positive
  have h1 : (0 : VNT A B) ≤ (a₂ - a) ⊗ᵥ b₂ :=
    vtmul_nonneg _ _ (sub_nonneg.mpr ha₂) (hb.trans hb₂)
  have h2 : (0 : VNT A B) ≤ a ⊗ᵥ (b₂ - b) :=
    vtmul_nonneg _ _ ha (sub_nonneg.mpr hb₂)
  have hsplit : a₂ ⊗ᵥ b₂ - a ⊗ᵥ b = (a₂ - a) ⊗ᵥ b₂ + a ⊗ᵥ (b₂ - b) := by
    show (vnTensor A B).map a₂ b₂ - (vnTensor A B).map a b =
      (vnTensor A B).map (a₂ - a) b₂ + (vnTensor A B).map a (b₂ - b)
    rw [map_sub, map_sub]
    simp only [LinearMap.sub_apply]
    abel
  have hsum := add_nonneg h1 h2
  rw [← hsplit] at hsum
  exact sub_nonneg.mp hsum

/-! ### **115II**: the bilinear map `β(a,b) = f(a) ⊗ g(b)`

proc.tex:3138.  Everything hangs on `β` being *bounded* and *normal*; 112XI,
114I(5) and 44XV then deliver `f ⊗ g` with all its properties.  Both
hypotheses go through the same object: for an np-functional `χ` on `𝒞 ⊗ 𝒟`,
the functional `χ ∘ β_⊙` on `𝒜 ⊙ ℬ` is the restriction along `⊗_⊙` of a
normal functional on `𝒜 ⊗ ℬ`.  For `χ` in the collection `Ω` of 112X.1 this
is the thesis's computation
`χ ∘ β_⊙ = ∑ₖₗ σ(cₖ*f(·)c_l) ⊙ τ(dₖ*g(·)d_l)` fed to **112IX**; for a
general `χ` it is that plus the normal-limit lemma, because 112X.1.2 only
makes `χ` an *operator-norm* limit of members of `Ω`. -/

/-- The bilinear map `β(a,b) = f(a) ⊗ g(b)` of **115II**. -/
noncomputable def tmapBilin (f : NCPMap A C) (g : NCPMap B D) :
    A →ₗ[ℂ] B →ₗ[ℂ] VNT C D :=
  ((vnTensor C D).map).compl₁₂ f.toCompletelyPositiveMap.toLinearMap
    g.toCompletelyPositiveMap.toLinearMap

@[simp] theorem tmapBilin_apply (f : NCPMap A C) (g : NCPMap B D) (a : A) (b : B) :
    tmapBilin f g a b = f a ⊗ᵥ g b := rfl

/-- An ncp-map is completely positive in the sense of cstar.tex **10II**. -/
private theorem ncp_cp (f : NCPMap A C) :
    Theses.A.CStar.IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
  ((Theses.A.CStar.cp_iff _).out 1 0).mp fun N M hM =>
    f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM

private theorem isCompletelyPositiveMap_id {X : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] :
    Theses.A.CStar.IsCompletelyPositiveMap (LinearMap.id : X →ₗ[ℂ] X) := by
  intro n a c
  have he : ∑ i, ∑ j, star (c i) * ((LinearMap.id : X →ₗ[ℂ] X) (star (a i) * a j)) * c j
      = star (∑ i, a i * c i) * ∑ j, a j * c j := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (c i) * (star (a i) * a j) * c j = star (a i * c i) * (a j * c j)
    rw [star_mul]
    noncomm_ring
  rw [he]
  exact star_mul_self_nonneg _

/-- `β` is completely positive: **113IV**'s corollary `cp_bilinear_comp`
applied to the miu-bilinear `⊗ : 𝒞 × 𝒟 → 𝒞 ⊗ 𝒟` (completely positive by
**113II**). -/
theorem tmapBilin_cp (f : NCPMap A C) (g : NCPMap B D) :
    BilinCP (tmapBilin f g) :=
  cp_bilinear_comp ((vnTensor C D).map)
    (mi_bilinear_cp _ (vnTensor C D).isTensorProduct.miu.2.1
      (vnTensor C D).isTensorProduct.miu.2.2)
    f.toCompletelyPositiveMap.toLinearMap g.toCompletelyPositiveMap.toLinearMap
    LinearMap.id (ncp_cp f) (ncp_cp g) isCompletelyPositiveMap_id
    (tmapBilin f g) (fun a b => rfl)

/-- `t₀* (x ⊙ y) t₀` expanded on a representation `t₀ = ∑ₖ cₖ ⊙ dₖ`. -/
private theorem star_tmul_conj_expand {N : ℕ} (c : Fin N → C) (d : Fin N → D)
    (x : C) (y : D) :
    star (∑ k, c k ⊗ₜ[ℂ] d k) * (x ⊗ₜ[ℂ] y) * (∑ l, c l ⊗ₜ[ℂ] d l)
      = ∑ k, ∑ l, (star (c k) * x * c l) ⊗ₜ[ℂ] (star (d k) * y * d l) := by
  rw [star_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- An ncp-map is ultraweakly continuous (**44XV** `p_uwcont`). -/
private theorem ncp_uwcont (f : NCPMap A C) :
    @Continuous A C (ultraweak A) (ultraweak C) (fun a => (f a : C)) :=
  ((p_uwcont (ncpPositive f)).out 2 0).mp f.preservesDirSups'

/-- The heart of **115II** (proc.tex:3175): for a member `χ` of the
collection `Ω` of **112X**.1 on `𝒞 ⊗ 𝒟`, the functional `χ ∘ β_⊙` is the
finite sum `∑ₖₗ σ(cₖ* f(·)c_l) ⊙ τ(dₖ* g(·)d_l)` of `odotF`s of bounded
ultraweakly continuous functionals, hence — by **112IX** in the factorised
form `exists_uwExtension_odotF` — the restriction along `⊗_⊙` of a normal
functional on `𝒜 ⊗ ℬ`. -/
theorem exists_extension_conjProdNP (f : NCPMap A C) (g : NCPMap B D)
    (σ : NPFunctional C) (τ : NPFunctional D) (t₀ : C ⊗[ℂ] D) :
    ∃ E : VNT A B →L[ℂ] ℂ,
      (@Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑E) ∧
      ∀ t : A ⊗[ℂ] B,
        E (TensorProduct.lift (vnTensor A B).map t)
          = conjProdNP (vnTensor C D).isTensorProduct σ τ t₀
              (TensorProduct.lift (tmapBilin f g) t) := by
  classical
  obtain ⟨N, c, d, ht₀⟩ := exists_fin_repr t₀
  set φ : Fin N → Fin N → (A →ₗ[ℂ] ℂ) := fun k l =>
    (npLin σ).comp (((LinearMap.mulRight ℂ (c l)).comp
      (LinearMap.mulLeft ℂ (star (c k)))).comp
        f.toCompletelyPositiveMap.toLinearMap) with hφ
  set ψ : Fin N → Fin N → (B →ₗ[ℂ] ℂ) := fun k l =>
    (npLin τ).comp (((LinearMap.mulRight ℂ (d l)).comp
      (LinearMap.mulLeft ℂ (star (d k)))).comp
        g.toCompletelyPositiveMap.toLinearMap) with hψ
  have hφval : ∀ (k l : Fin N) (a : A), φ k l a = σ (star (c k) * f a * c l) :=
    fun _ _ _ => rfl
  have hψval : ∀ (k l : Fin N) (b : B), ψ k l b = τ (star (d k) * g b * d l) :=
    fun _ _ _ => rfl
  have hφc : ∀ k l, @Continuous A ℂ (ultraweak A) _ ⇑(φ k l) := by
    intro k l
    letI : TopologicalSpace A := ultraweak A
    letI : TopologicalSpace C := ultraweak C
    have h1 : Continuous (fun z : C => star (c k) * z) :=
      (mult_uws_cont (star (c k))).1
    have h2 : Continuous (fun z : C => z * c l) := (mult_uws_cont (c l)).2.1
    have h3 : Continuous (fun a : A => (f a : C)) := ncp_uwcont f
    exact (continuous_ultraweak_npFunctional σ).comp (h2.comp (h1.comp h3))
  have hψc : ∀ k l, @Continuous B ℂ (ultraweak B) _ ⇑(ψ k l) := by
    intro k l
    letI : TopologicalSpace B := ultraweak B
    letI : TopologicalSpace D := ultraweak D
    have h1 : Continuous (fun z : D => star (d k) * z) :=
      (mult_uws_cont (star (d k))).1
    have h2 : Continuous (fun z : D => z * d l) := (mult_uws_cont (d l)).2.1
    have h3 : Continuous (fun b : B => (g b : D)) := ncp_uwcont g
    exact (continuous_ultraweak_npFunctional τ).comp (h2.comp (h1.comp h3))
  choose E hEc hEval using fun p : Fin N × Fin N =>
    exists_uwExtension_odotF (vnTensor A B).map (vnTensor A B).isTensorProduct
      (φ p.1 p.2) (ψ p.1 p.2) (hφc p.1 p.2) (hψc p.1 p.2)
  -- the thesis's identity `χ ∘ β_⊙ = ∑ₖₗ σ(cₖ*f(·)c_l) ⊙ τ(dₖ*g(·)d_l)`
  have hkey : (∑ p : Fin N × Fin N, odotF (φ p.1 p.2) (ψ p.1 p.2))
      = (npLin (conjProdNP (vnTensor C D).isTensorProduct σ τ t₀)).comp
          (TensorProduct.lift (tmapBilin f g)) := by
    refine TensorProduct.ext' fun a b => ?_
    have hlhs : (∑ p : Fin N × Fin N, odotF (φ p.1 p.2) (ψ p.1 p.2)) (a ⊗ₜ[ℂ] b)
        = ∑ k, ∑ l, σ (star (c k) * f a * c l) * τ (star (d k) * g b * d l) := by
      rw [LinearMap.sum_apply, ← Finset.sum_product']
      exact Finset.sum_congr rfl fun p _ => by
        rw [odotF_tmul, hφval, hψval]
    have hrhs : (npLin (conjProdNP (vnTensor C D).isTensorProduct σ τ t₀)).comp
        (TensorProduct.lift (tmapBilin f g)) (a ⊗ₜ[ℂ] b)
        = ∑ k, ∑ l, σ (star (c k) * f a * c l) * τ (star (d k) * g b * d l) := by
      show conjProdNP (vnTensor C D).isTensorProduct σ τ t₀
          (TensorProduct.lift (tmapBilin f g) (a ⊗ₜ[ℂ] b)) = _
      have h1 : TensorProduct.lift (tmapBilin f g) (a ⊗ₜ[ℂ] b)
          = TensorProduct.lift (vnTensor C D).map ((f a : C) ⊗ₜ[ℂ] (g b : D)) := by
        simp
        rfl
      rw [h1, conjProdNP_lift (vnTensor C D).isTensorProduct, ht₀,
        star_tmul_conj_expand c d (f a) (g b)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [odotF_tmul]; rfl
    rw [hlhs, hrhs]
  refine ⟨∑ p : Fin N × Fin N, E p, ?_, fun t => ?_⟩
  · letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
    have hfun : ⇑(∑ p : Fin N × Fin N, E p)
        = fun x : VNT A B => ∑ p : Fin N × Fin N, E p x := by
      funext x; simp [ContinuousLinearMap.sum_apply]
    rw [hfun]
    exact continuous_finsetSum _ fun p _ => hEc p
  · rw [ContinuousLinearMap.sum_apply]
    have h1 : ∑ p : Fin N × Fin N, E p (TensorProduct.lift (vnTensor A B).map t)
        = ∑ p : Fin N × Fin N, odotF (φ p.1 p.2) (ψ p.1 p.2) t :=
      Finset.sum_congr rfl fun p _ => hEval p t
    rw [h1, ← LinearMap.sum_apply, hkey]
    rfl

/-- `β_⊙(v* v) = ∑ᵢⱼ β(aᵢ* aⱼ, bᵢ* bⱼ)` for `v = ∑ᵢ aᵢ ⊙ bᵢ`. -/
private theorem lift_star_mul_self {N : ℕ} (β : A →ₗ[ℂ] B →ₗ[ℂ] VNT C D)
    (a : Fin N → A) (b : Fin N → B) :
    TensorProduct.lift β (star (∑ i, a i ⊗ₜ[ℂ] b i) * ∑ i, a i ⊗ₜ[ℂ] b i)
      = ∑ i, ∑ j, β (star (a i) * a j) (star (b i) * b j) := by
  rw [star_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.lift.tmul]

/-- `β_⊙` maps `v* v` to a positive element: that is `BilinCP β` with
`c ≡ 1`. -/
private theorem lift_tmapBilin_star_mul_self_nonneg (f : NCPMap A C)
    (g : NCPMap B D) (v : A ⊗[ℂ] B) :
    0 ≤ TensorProduct.lift (tmapBilin f g) (star v * v) := by
  obtain ⟨N, a, b, rfl⟩ := exists_fin_repr v
  rw [lift_star_mul_self]
  simpa using tmapBilin_cp f g N a b (fun _ => 1)

/-- The np-functional `E_χ` extending `χ ∘ β_⊙` along `⊗_⊙`, for `χ` in the
collection `Ω` of **112X**.1.  Positivity of `E_χ` is `BilinCP β` on
`γ_⊙(𝒜 ⊙ ℬ)` plus `nonneg_of_nonneg_on_tensorSpan`; normality is then
`preservesDirSups_of_continuousOn_effects_functional`. -/
theorem exists_npExtension_conjProdNP (f : NCPMap A C) (g : NCPMap B D)
    (σ : NPFunctional C) (τ : NPFunctional D) (t₀ : C ⊗[ℂ] D) :
    ∃ E : NPFunctional (VNT A B),
      ∀ t : A ⊗[ℂ] B,
        E (TensorProduct.lift (vnTensor A B).map t)
          = conjProdNP (vnTensor C D).isTensorProduct σ τ t₀
              (TensorProduct.lift (tmapBilin f g) t) := by
  obtain ⟨E, hEc, hEval⟩ := exists_extension_conjProdNP f g σ τ t₀
  have hpos : ∀ x : VNT A B, 0 ≤ x → 0 ≤ E x := by
    intro x hx
    refine nonneg_of_nonneg_on_tensorSpan (vnTensor A B).map
      (vnTensor A B).isTensorProduct E hEc (fun v => ?_) hx
    rw [hEval]
    exact npFunctional_nonneg _ (lift_tmapBilin_star_mul_self_nonneg f g v)
  let E₀ : VNT A B →ₚ[ℂ] ℂ :=
    { toFun := fun x => E x
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp
      monotone' := fun x y hxy => by
        have h := hpos (y - x) (sub_nonneg.mpr hxy)
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  exact ⟨⟨E₀, preservesDirSups_of_continuousOn_effects_functional E₀
    (@Continuous.continuousOn (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑E₀
      (effects (VNT A B)) hEc)⟩, hEval⟩

/-- The **first promise** of proc.tex:3175, `‖ω ∘ β_⊙‖ ≤ ‖f‖‖g‖` for a basic
`ω` with `ω(1) ≤ 1`, here without the normalisation: for `χ ∈ Ω`,
`‖χ(β_⊙ t)‖ ≤ ‖f(1)‖‖g(1)‖ χ(1) ‖t‖`.  (The thesis's route: the extension
`ω'` of `ω ∘ β_⊙` is completely positive, so `cp-russo-dye` gives
`‖ω'‖ = ω'(1) = ω(f(1) ⊗ g(1)) ≤ ‖f‖‖g‖ω(1)`.  Here `ω'` is the
np-functional `E_χ`, and `npFunctional_norm_le` is the Russo–Dye step.) -/
theorem conjProdNP_tmapBilin_norm_le (f : NCPMap A C) (g : NCPMap B D)
    (σ : NPFunctional C) (τ : NPFunctional D) (t₀ : C ⊗[ℂ] D) (t : A ⊗[ℂ] B) :
    ‖(conjProdNP (vnTensor C D).isTensorProduct σ τ t₀)
        (TensorProduct.lift (tmapBilin f g) t)‖
      ≤ ‖(f 1 : C)‖ * ‖(g 1 : D)‖ *
        ((conjProdNP (vnTensor C D).isTensorProduct σ τ t₀) 1).re *
          tensorNorm A B t := by
  set χ := conjProdNP (vnTensor C D).isTensorProduct σ τ t₀ with hχ
  obtain ⟨E, hE⟩ := exists_npExtension_conjProdNP f g σ τ t₀
  have hf1 : (0 : C) ≤ f 1 := (ncpPositive f).map_nonneg zero_le_one
  have hg1 : (0 : D) ≤ g 1 := (ncpPositive g).map_nonneg zero_le_one
  -- `E(1) = χ(f(1) ⊗ g(1)) ≤ ‖f(1)‖‖g(1)‖ χ(1)`
  have hone : TensorProduct.lift (vnTensor A B).map (1 : A ⊗[ℂ] B) = 1 :=
    lift_one _ (vnTensor A B).isTensorProduct.miu.1
  have hβone : TensorProduct.lift (tmapBilin f g) (1 : A ⊗[ℂ] B)
      = (f 1 : C) ⊗ᵥ (g 1 : D) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.lift.tmul]
    rfl
  have hE1 : (E 1 : ℂ) = χ ((f 1 : C) ⊗ᵥ (g 1 : D)) := by
    rw [← hone, hE, hβone]
  have hle : (f 1 : C) ⊗ᵥ (g 1 : D)
      ≤ ((‖(f 1 : C)‖ * ‖(g 1 : D)‖ : ℝ) : ℂ) • (1 : VNT C D) := by
    have h1 : (f 1 : C) ≤ ((‖(f 1 : C)‖ : ℝ) : ℂ) • (1 : C) := by
      rw [Complex.coe_smul]; exact le_norm_smul_one hf1
    have h2 : (g 1 : D) ≤ ((‖(g 1 : D)‖ : ℝ) : ℂ) • (1 : D) := by
      rw [Complex.coe_smul]; exact le_norm_smul_one hg1
    have h3 := (tensor_simple_facts_1 (f 1 : C) (g 1 : D) hf1 hg1).2 _ _ h1 h2
    refine h3.trans (le_of_eq ?_)
    show ((vnTensor C D).map (((‖(f 1 : C)‖ : ℝ) : ℂ) • (1 : C)))
        (((‖(g 1 : D)‖ : ℝ) : ℂ) • (1 : D)) = _
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul,
      (vnTensor C D).isTensorProduct.miu.1]
    congr 1
    push_cast
    ring
  have hE1le : (E 1).re ≤ ‖(f 1 : C)‖ * ‖(g 1 : D)‖ * (χ 1).re := by
    have hmono := npFunctional_mono χ hle
    have hsmul : χ (((‖(f 1 : C)‖ * ‖(g 1 : D)‖ : ℝ) : ℂ) • (1 : VNT C D))
        = ((‖(f 1 : C)‖ * ‖(g 1 : D)‖ : ℝ) : ℂ) * χ 1 := by
      show npLin χ _ = _
      rw [map_smul]
      rfl
    rw [hsmul] at hmono
    have h := (Complex.le_def.mp hmono).1
    rw [Complex.re_ofReal_mul] at h
    rw [hE1]
    exact h
  -- `‖χ(β_⊙ t)‖ = ‖E(⊗_⊙ t)‖ ≤ E(1)‖⊗_⊙ t‖ = E(1)‖t‖`
  have hmain : ‖χ (TensorProduct.lift (tmapBilin f g) t)‖
      ≤ (E 1).re * tensorNorm A B t := by
    rw [← hE t, ← tensor_basic_2 (vnTensor A B).map (vnTensor A B).isTensorProduct t]
    exact npFunctional_norm_le E _
  refine hmain.trans ?_
  have hnn : (0 : ℝ) ≤ tensorNorm A B t := tensorNorm_nonneg t
  exact mul_le_mul_of_nonneg_right hE1le hnn

/-- **115II**, boundedness of `β` (proc.tex:3162): with the first promise
`‖χ ∘ β_⊙‖ ≤ ‖f‖‖g‖χ(1)` and the cp-Cauchy–Schwarz step `tmap_cs`,
`χ(β_⊙(s)* β_⊙(s)) ≤ ‖f‖²‖g‖²‖s‖²χ(1)` for every `χ ∈ Ω`, which is exactly
what the order-separating half of **112X**.1 turns into
`β_⊙(s)* β_⊙(s) ≤ ‖f‖²‖g‖²‖s‖²·1`. -/
theorem tmapBilin_bounded (f : NCPMap A C) (g : NCPMap B D) :
    BilinBounded (tmapBilin f g) := by
  classical
  set K : ℝ := ‖(f 1 : C)‖ * ‖(g 1 : D)‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun t => ?_⟩
  set z : VNT C D := TensorProduct.lift (tmapBilin f g) t with hz
  set r : ℝ := (K * tensorNorm A B t) ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have htn : (0 : ℝ) ≤ tensorNorm A B t := tensorNorm_nonneg t
  -- the tensor-norm identity `‖s* s‖ = ‖s‖²`
  have hsq : tensorNorm A B (star t * t) = tensorNorm A B t ^ 2 := by
    rw [← tensor_basic_2 (vnTensor A B).map (vnTensor A B).isTensorProduct,
      ← tensor_basic_2 (vnTensor A B).map (vnTensor A B).isTensorProduct,
      lift_mul _ (vnTensor A B).isTensorProduct.miu.2.1,
      lift_star _ (vnTensor A B).isTensorProduct.miu.2.2,
      CStarRing.norm_star_mul_self]
    ring
  -- the cp-Cauchy–Schwarz step
  have hcs : star z * z ≤ ((K : ℝ) : ℂ) •
      TensorProduct.lift (tmapBilin f g) (star t * t) := by
    obtain ⟨N, a, b, ht⟩ := exists_fin_repr t
    have h1 : z = ∑ i, (f (a i) : C) ⊗ᵥ (g (b i) : D) := by
      rw [hz, ht, map_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    have h2 : TensorProduct.lift (tmapBilin f g) (star t * t)
        = ∑ i, ∑ j, (f (star (a i) * a j) : C) ⊗ᵥ (g (star (b i) * b j) : D) := by
      rw [ht, lift_star_mul_self]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl
    rw [h1, h2]
    exact tmap_cs f.toCompletelyPositiveMap.toLinearMap
      g.toCompletelyPositiveMap.toLinearMap (ncp_cp f) (ncp_cp g) a b
  -- `χ(z* z) ≤ r χ(1)` for every member `χ` of `Ω`
  have hkey : star z * z ≤ ((r : ℝ) : ℂ) • (1 : VNT C D) := by
    have hsa1 : IsSelfAdjoint (((r : ℝ) : ℂ) • (1 : VNT C D)) := by
      show star _ = _
      simp
    refine (tensor_basic_1 (vnTensor C D).map (vnTensor C D).isTensorProduct).1
      _ _ (IsSelfAdjoint.star_mul_self z) hsa1 (fun σ τ v => ?_)
    set χ := conjProdNP (vnTensor C D).isTensorProduct σ τ v with hχ
    have hχ1 : (0 : ℝ) ≤ (χ 1).re := by
      simpa using (Complex.le_def.mp (npFunctional_nonneg χ zero_le_one)).1
    have hL : prodNP (vnTensor C D).isTensorProduct σ τ
        (star (TensorProduct.lift (vnTensor C D).map v) * (star z * z) *
          TensorProduct.lift (vnTensor C D).map v) = χ (star z * z) := rfl
    have hR : prodNP (vnTensor C D).isTensorProduct σ τ
        (star (TensorProduct.lift (vnTensor C D).map v) * (((r : ℝ) : ℂ) •
            (1 : VNT C D)) * TensorProduct.lift (vnTensor C D).map v)
        = ((r : ℝ) : ℂ) * χ 1 := by
      have he : star (TensorProduct.lift (vnTensor C D).map v) *
            (((r : ℝ) : ℂ) • (1 : VNT C D)) *
            TensorProduct.lift (vnTensor C D).map v
          = ((r : ℝ) : ℂ) • (star (TensorProduct.lift (vnTensor C D).map v) *
            (1 : VNT C D) * TensorProduct.lift (vnTensor C D).map v) := by
        rw [mul_smul_comm, smul_mul_assoc]
      rw [he]
      show npLin (prodNP (vnTensor C D).isTensorProduct σ τ) _ = _
      rw [map_smul]
      rfl
    rw [hL, hR, Complex.re_ofReal_mul]
    -- the two promises
    have h1 : (χ (star z * z)).re
        ≤ K * (χ (TensorProduct.lift (tmapBilin f g) (star t * t))).re := by
      have hmono := npFunctional_mono χ hcs
      have hsmul : χ (((K : ℝ) : ℂ) •
          TensorProduct.lift (tmapBilin f g) (star t * t))
          = ((K : ℝ) : ℂ) * χ (TensorProduct.lift (tmapBilin f g) (star t * t)) := by
        show npLin χ _ = _
        rw [map_smul]
        rfl
      rw [hsmul] at hmono
      have h := (Complex.le_def.mp hmono).1
      rwa [Complex.re_ofReal_mul] at h
    have h2 : (χ (TensorProduct.lift (tmapBilin f g) (star t * t))).re
        ≤ K * (χ 1).re * tensorNorm A B t ^ 2 := by
      refine le_trans (Complex.re_le_norm _) ?_
      have h := conjProdNP_tmapBilin_norm_le f g σ τ v (star t * t)
      rw [hsq] at h
      exact h
    calc (χ (star z * z)).re
        ≤ K * (χ (TensorProduct.lift (tmapBilin f g) (star t * t))).re := h1
      _ ≤ K * (K * (χ 1).re * tensorNorm A B t ^ 2) := by
          exact mul_le_mul_of_nonneg_left h2 hK0
      _ = r * (χ 1).re := by rw [hr]; ring
  -- from `z* z ≤ r·1` to `‖z‖ ≤ K‖t‖`
  have hnorm : ‖star z * z‖ ≤ r := by
    refine (Theses.A.CStar.norm_le_iff_neg_algebraMap_le
      (IsSelfAdjoint.star_mul_self z) hr0).mpr ⟨?_, ?_⟩
    · refine le_trans (neg_nonpos.mpr ?_) (star_mul_self_nonneg z)
      exact Theses.A.CStar.algebraMap_ofReal_nonneg hr0
    · rwa [Algebra.algebraMap_eq_smul_one]
  rw [CStarRing.norm_star_mul_self] at hnorm
  nlinarith [norm_nonneg z, mul_nonneg hK0 htn]

/-- Continuity into an ultraweak topology is tested by the np-functionals
(`continuous_ultraweak_of_forall`, with the domain topology arbitrary). -/
private theorem continuous_ultraweak_of_forall' {X : Type*}
    (tX : TopologicalSpace X) {Y : Type u} [CStarAlgebra Y] [PartialOrder Y]
    [StarOrderedRing Y] [VonNeumannAlgebra Y] (p : X → Y)
    (h : ∀ ω : NPFunctional Y, @Continuous X ℂ tX _ (fun x => (ω (p x) : ℂ))) :
    @Continuous X Y tX (ultraweak Y) p := by
  letI := tX
  letI : TopologicalSpace Y := ultraweak Y
  rw [continuous_iff_le_induced]
  show tX ≤ TopologicalSpace.induced p
    (⨅ ω : NPFunctional Y,
      TopologicalSpace.induced (fun y : Y => (ω y : ℂ)) inferInstance)
  rw [induced_iInf]
  refine le_iInf fun ω => ?_
  rw [induced_compose]
  exact continuous_iff_le_induced.mp (h ω)

/-- **115II**, normality of `β`.  The thesis reads this off from the *basic*
functionals ("incidentally, since each `ω ∘ β_⊙` is ultraweakly continuous,
so is `β_⊙`"), but continuity into `ultraweak (𝒞 ⊗ 𝒟)` has to be tested
against *every* np-functional `χ` on `𝒞 ⊗ 𝒟`, and **112X**.1.2 only makes
such a `χ` an *operator-norm* limit of members of `Ω`.  The normal-limit
lemma `exists_uwExtension_of_normLimit` is what closes that gap — using
boundedness of `β`, already proved, to transport the operator norm. -/
theorem tmapBilin_normal (f : NCPMap A C) (g : NCPMap B D) :
    BilinNormal (tmapBilin f g) := by
  classical
  obtain ⟨M, hM0, hMb⟩ := tmapBilin_bounded f g
  refine continuous_ultraweak_of_forall' (uwTensorTopology A B) _ (fun χ => ?_)
  -- `χ ∘ β_⊙` factors through `⊗_⊙` as a normal functional on `𝒜 ⊗ ℬ`
  have happrox : ∀ ε > (0 : ℝ), ∃ E : VNT A B →L[ℂ] ℂ,
      (@Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑E) ∧
      ∀ t : A ⊗[ℂ] B,
        ‖((npLin χ).comp (TensorProduct.lift (tmapBilin f g))) t
          - E (TensorProduct.lift (vnTensor A B).map t)‖
          ≤ ε * tensorNorm A B t := by
    intro ε hε
    obtain ⟨n, σ, τ, s, hb⟩ :=
      (tensor_basic_1 (vnTensor C D).map (vnTensor C D).isTensorProduct).2 χ
        (ε / (M + 1)) (by positivity)
    choose Ei hEic hEival using fun i : Fin n =>
      exists_extension_conjProdNP f g (σ i) (τ i) (s i)
    refine ⟨∑ i, Ei i, ?_, fun t => ?_⟩
    · letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
      have hfun : ⇑(∑ i, Ei i) = fun x : VNT A B => ∑ i, Ei i x := by
        funext x; simp [ContinuousLinearMap.sum_apply]
      rw [hfun]
      exact continuous_finsetSum _ fun i _ => hEic i
    · have hval : (∑ i, Ei i) (TensorProduct.lift (vnTensor A B).map t)
          = ∑ i, prodNP (vnTensor C D).isTensorProduct (σ i) (τ i)
              (star (TensorProduct.lift (vnTensor C D).map (s i)) *
                TensorProduct.lift (tmapBilin f g) t *
                TensorProduct.lift (vnTensor C D).map (s i)) := by
        rw [ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => hEival i t
      rw [hval]
      have h1 := hb (TensorProduct.lift (tmapBilin f g) t)
      have h2 : ‖TensorProduct.lift (tmapBilin f g) t‖ ≤ M * tensorNorm A B t :=
        hMb t
      have h3 : (0 : ℝ) ≤ ε / (M + 1) := by positivity
      have h4 : ε / (M + 1) * ‖TensorProduct.lift (tmapBilin f g) t‖
          ≤ ε / (M + 1) * (M * tensorNorm A B t) :=
        mul_le_mul_of_nonneg_left h2 h3
      have h5 : ε / (M + 1) * (M * tensorNorm A B t) ≤ ε * tensorNorm A B t := by
        have hnn : (0 : ℝ) ≤ tensorNorm A B t := tensorNorm_nonneg t
        have hMle : M / (M + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        have : ε / (M + 1) * M = ε * (M / (M + 1)) := by
          field_simp
        calc ε / (M + 1) * (M * tensorNorm A B t)
            = (ε * (M / (M + 1))) * tensorNorm A B t := by rw [← this]; ring
          _ ≤ (ε * 1) * tensorNorm A B t := by
              refine mul_le_mul_of_nonneg_right ?_ hnn
              exact mul_le_mul_of_nonneg_left hMle hε.le
          _ = ε * tensorNorm A B t := by ring
      exact le_trans (le_trans h1 h4) h5
  obtain ⟨E, hEc, hEval⟩ := exists_uwExtension_of_normLimit (vnTensor A B).map
    (vnTensor A B).isTensorProduct
    ((npLin χ).comp (TensorProduct.lift (tmapBilin f g))) happrox
  exact (uwTensor_continuous_of_uwExtension (vnTensor A B).map
    (vnTensor A B).isTensorProduct _ E hEc hEval).1

/-! ### **115II** itself -/

/-- **115II** (`tensor-functorial`, proc.tex:3114, Proposition),
well-definedness: for ncp-maps `f : 𝒜 → 𝒞` and `g : ℬ → 𝒟` there is a
unique ncp-map `f ⊗ g : 𝒜 ⊗ ℬ → 𝒞 ⊗ 𝒟` with
`(f ⊗ g)(a ⊗ b) = f(a) ⊗ g(b)`. -/
theorem exists_tmap (f : NCPMap A C) (g : NCPMap B D) :
    ∃! h : NCPMap (VNT A B) (VNT C D),
      ∀ (a : A) (b : B), h (a ⊗ᵥ b) = f a ⊗ᵥ g b := by
  -- proc.tex:3140: `β` is completely positive by **113IV**, and bounded and
  -- normal by the two halves above, so **112XI** extends it and **114I**(5)
  -- makes the extension completely positive; normality of the extension is
  -- **44XV**, and uniqueness is ultraweak density of `⊗_⊙(𝒜 ⊙ ℬ)`.
  obtain ⟨⟨hl, ⟨hlc, hle⟩, -⟩, -⟩ :=
    tensor_universal_property (vnTensor A B).map (vnTensor A B).isTensorProduct
      (tmapBilin f g) (tmapBilin_normal f g) (tmapBilin_bounded f g)
  have hcp : Theses.A.CStar.IsCompletelyPositiveMap hl :=
    ((tensor_universal_property_extra (vnTensor A B).map
      (vnTensor A B).isTensorProduct (tmapBilin f g) (tmapBilin_normal f g)
      (tmapBilin_bounded f g) hl hlc hle).2.2.2.2).mpr (tmapBilin_cp f g)
  have hpos : Theses.A.CStar.IsPositiveMap hl :=
    Theses.A.CStar.astara_pos_basic_2_cp hl hcp
  set hP : VNT A B →ₚ[ℂ] VNT C D :=
    { toFun := fun x => hl x
      map_add' := fun x y => map_add hl x y
      map_smul' := fun c x => map_smul hl c x
      monotone' := fun x y hxy => by
        have h := hpos _ (sub_nonneg.mpr hxy)
        rw [map_sub] at h
        exact sub_nonneg.mp h } with hPdef
  have hdirsup : PreservesDirSups ⇑hP := ((p_uwcont hP).out 0 2).mp hlc
  have hcpm : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) (VNT A B)),
      0 ≤ M → 0 ≤ M.map ⇑hl := ((Theses.A.CStar.cp_iff hl).out 0 1).mp hcp
  refine ⟨⟨{ toLinearMap := hl
             map_cstarMatrix_nonneg' := fun k M hM => hcpm k M hM },
      hdirsup⟩, fun a b => hle a b, ?_⟩
  -- uniqueness
  intro h' hh'
  letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
  letI : TopologicalSpace (VNT C D) := ultraweak (VNT C D)
  haveI : T2Space (VNT C D) := vn_positive_basic_1.1
  have hdense : Dense (Set.range ⇑(TensorProduct.lift (vnTensor A B).map)) := by
    rw [range_lift_eq_span]
    exact (vnTensor A B).isTensorProduct.dense
  have hc' : Continuous ⇑h' :=
    ((p_uwcont (ncpPositive h')).out 2 0).mp h'.preservesDirSups'
  have hkey : ∀ t : A ⊗[ℂ] B,
      h'.toCompletelyPositiveMap.toLinearMap
          (TensorProduct.lift (vnTensor A B).map t)
        = hl (TensorProduct.lift (vnTensor A B).map t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a b =>
        rw [TensorProduct.lift.tmul, hle a b]
        exact hh' a b
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  refine DFunLike.coe_injective (Continuous.ext_on hdense hc' hlc ?_)
  rintro _ ⟨t, rfl⟩
  exact hkey t

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
    (f 1 ≤ 1 → g 1 ≤ 1 → tmap f g 1 ≤ 1) := by
  -- "all the properties claimed for `f ⊗ g` follow with the very least of
  -- effort from `tensor-universal-property-extra`" (proc.tex:3155)
  set hl := (tmap f g).toCompletelyPositiveMap.toLinearMap with hhl
  have hlc : @Continuous (VNT A B) (VNT C D) (ultraweak (VNT A B))
      (ultraweak (VNT C D)) ⇑hl :=
    ((p_uwcont (ncpPositive (tmap f g))).out 2 0).mp (tmap f g).preservesDirSups'
  have hle : ∀ (a : A) (b : B), hl ((vnTensor A B).map a b) = tmapBilin f g a b :=
    fun a b => tmap_apply f g a b
  obtain ⟨e1, e2, e3, -, -⟩ := tensor_universal_property_extra (vnTensor A B).map
    (vnTensor A B).isTensorProduct (tmapBilin f g) (tmapBilin_normal f g)
    (tmapBilin_bounded f g) hl hlc hle
  have hone : hl 1 = (f 1 : C) ⊗ᵥ (g 1 : D) := by
    rw [← (vnTensor A B).isTensorProduct.miu.1, hle]
    rfl
  refine ⟨fun hfm hgm x y => e1.mpr (fun a a' b b' => ?_) x y,
    fun hfs hgs x => e2.mpr (fun a b => ?_) x,
    fun hf1 hg1 => e3.mpr ?_, fun hf1 hg1 => ?_⟩
  · show (f (a * a') : C) ⊗ᵥ (g (b * b') : D)
      = ((f a : C) ⊗ᵥ (g b : D)) * ((f a' : C) ⊗ᵥ (g b' : D))
    rw [hfm, hgm]
    exact (vnTensor C D).isTensorProduct.miu.2.1 (f a) (f a') (g b) (g b')
  · show star ((f a : C) ⊗ᵥ (g b : D))
      = (f (star a) : C) ⊗ᵥ (g (star b) : D)
    rw [hfs, hgs]
    exact (vnTensor C D).isTensorProduct.miu.2.2 (f a) (g b)
  · show (f 1 : C) ⊗ᵥ (g 1 : D) = 1
    rw [hf1, hg1]
    exact (vnTensor C D).isTensorProduct.miu.1
  · show hl 1 ≤ 1
    rw [hone]
    have hf0 : (0 : C) ≤ f 1 := (ncpPositive f).map_nonneg zero_le_one
    have hg0 : (0 : D) ≤ g 1 := (ncpPositive g).map_nonneg zero_le_one
    have h := (tensor_simple_facts_1 (f 1 : C) (g 1 : D) hf0 hg0).2 1 1 hf1 hg1
    refine h.trans (le_of_eq ?_)
    exact (vnTensor C D).isTensorProduct.miu.1

/-- **115IV** (`tensor-functor`, proc.tex:3275, Exercise), identity law:
the assignments `(𝒜,ℬ) ↦ 𝒜 ⊗ ℬ`, `(f,g) ↦ f ⊗ g` give a bifunctor on
`W*_miu`, `W*_cp`, `W*_cpu` and `W*_cpsu` — rendered concretely:
`id ⊗ id = id`. -/
theorem tensor_functor_id : tmap (ncpId A) (ncpId B) = ncpId (VNT A B) :=
  (exists_tmap (ncpId A) (ncpId B)).unique (tmap_apply (ncpId A) (ncpId B))
    (fun a b => by rw [ncpId_apply, ncpId_apply, ncpId_apply])

/-- **115IV** (`tensor-functor`, proc.tex:3275, Exercise), composition
law: `(f' ∘ f) ⊗ (g' ∘ g) = (f' ⊗ g') ∘ (f ⊗ g)`. -/
theorem tensor_functor_comp {A' B' : Type u} [CStarAlgebra A']
    [PartialOrder A'] [StarOrderedRing A'] [VonNeumannAlgebra A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B']
    [VonNeumannAlgebra B'] (f : NCPMap A C) (f' : NCPMap C A')
    (g : NCPMap B D) (g' : NCPMap D B') :
    tmap (ncpComp f' f) (ncpComp g' g) =
      ncpComp (tmap f' g') (tmap f g) :=
  (exists_tmap (ncpComp f' f) (ncpComp g' g)).unique
    (tmap_apply (ncpComp f' f) (ncpComp g' g))
    (fun a b => by
      rw [ncpComp_apply, tmap_apply, tmap_apply, ncpComp_apply, ncpComp_apply])

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

/-- Two normal functionals on `𝒜 ⊗ ℬ` agreeing on pure tensors are equal
(ultraweak density of the span of the pure tensors, 108II(1)). -/
private theorem clm_ext_of_tmul {h₁ h₂ : VNT A B →L[ℂ] ℂ}
    (hc₁ : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑h₁)
    (hc₂ : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑h₂)
    (h : ∀ (a : A) (b : B), h₁ (a ⊗ᵥ b) = h₂ (a ⊗ᵥ b)) : h₁ = h₂ := by
  letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
  have hdense : Dense (Set.range ⇑(TensorProduct.lift (vnTensor A B).map)) := by
    rw [range_lift_eq_span]
    exact (vnTensor A B).isTensorProduct.dense
  have hkey : ∀ t : A ⊗[ℂ] B,
      h₁ (TensorProduct.lift (vnTensor A B).map t)
        = h₂ (TensorProduct.lift (vnTensor A B).map t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a b => rw [TensorProduct.lift.tmul]; exact h a b
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  refine DFunLike.coe_injective (Continuous.ext_on hdense hc₁ hc₂ ?_)
  rintro _ ⟨t, rfl⟩
  exact hkey t

/-- **116I** (`product-functional-norm`, proc.tex:3403, Lemma),
well-definedness (from 112IX and 112XI): bounded ultraweakly continuous
functionals `f ∈ 𝒜_*`, `g ∈ ℬ_*` induce a unique normal functional
`f ⊗ g` on `𝒜 ⊗ ℬ`. -/
theorem exists_predualTensor (f : A →L[ℂ] ℂ) (g : B →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hg : @Continuous B ℂ (ultraweak B) _ ⇑g) :
    ∃! h : VNT A B →L[ℂ] ℂ,
      @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑h ∧
        ∀ (a : A) (b : B), h (a ⊗ᵥ b) = f a * g b := by
  -- **112IX** in the factorised form `exists_uwExtension_odotF`; uniqueness
  -- is ultraweak density of the span of the pure tensors.
  obtain ⟨E, hEc, hEval⟩ := exists_uwExtension_odotF (vnTensor A B).map
    (vnTensor A B).isTensorProduct f.toLinearMap g.toLinearMap hf hg
  have hval : ∀ (a : A) (b : B), E (a ⊗ᵥ b) = f a * g b := by
    intro a b
    have h := hEval (a ⊗ₜ[ℂ] b)
    rw [TensorProduct.lift.tmul, odotF_tmul] at h
    exact h
  exact ⟨E, ⟨hEc, hval⟩, fun h' hh' =>
    clm_ext_of_tmul hh'.1 hEc (fun a b => by rw [hh'.2 a b, hval a b])⟩

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
    ‖predualTensor f g hf hg‖ = ‖f‖ * ‖g‖ := by
  -- The thesis's proof (proc.tex:3405) verbatim: polar-decompose `f` and `g`
  -- (**86IX**), note that `u ⊗ v` is a partial isometry doing the same job for
  -- `f ⊗ g`, and read the norm off **86XIV** `functional_norm`.
  set F : VNT A B →L[ℂ] ℂ := predualTensor f g hf hg with hFdef
  have hspec := (exists_predualTensor f g hf hg).choose_spec.1
  have hFc : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑F := hspec.1
  have hFval : ∀ (a : A) (b : B), F (a ⊗ᵥ b) = f a * g b := hspec.2
  have hcw : ∀ z : VNT A B,
      @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ (fun x => (F (z * x) : ℂ)) := by
    intro z
    letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
    exact hFc.comp (mult_uws_cont z).1
  obtain ⟨u, σ, hpiu, hσapp, h1u, hσone⟩ := exists_npFunctional_polar f hf
  obtain ⟨v, τ, hpiv, hτapp, h1v, hτone⟩ := exists_npFunctional_polar g hg
  have hmiu := (vnTensor A B).isTensorProduct.miu
  have hmul : ∀ (x x' : A) (y y' : B),
      (x ⊗ᵥ y) * (x' ⊗ᵥ y') = (x * x') ⊗ᵥ (y * y') :=
    fun x x' y y' => (hmiu.2.1 x x' y y').symm
  have hstar : ∀ (x : A) (y : B), star (x ⊗ᵥ y) = star x ⊗ᵥ star y :=
    fun x y => hmiu.2.2 x y
  set w : VNT A B := u ⊗ᵥ v with hwdef
  have hstarw : star w = star u ⊗ᵥ star v := hstar u v
  have hu2 : u * star u * u = u := ((partial_isometry_equivalents u).out 0 2).mp hpiu
  have hv2 : v * star v * v = v := ((partial_isometry_equivalents v).out 0 2).mp hpiv
  have hpiw : IsPartialIsometry (VNT A B) w := by
    refine ((partial_isometry_equivalents w).out 2 0).mp ?_
    rw [hwdef, hstarw, hmul, hmul, hu2, hv2]
  -- `F(w ·)` is the product np-functional `σ ⊗ τ`, hence positive
  set χ : NPFunctional (VNT A B) :=
    prodNP (vnTensor A B).isTensorProduct σ τ with hχdef
  have hχval : ∀ (a : A) (b : B), χ (a ⊗ᵥ b) = (σ a : ℂ) * τ b :=
    fun a b => prodNP_apply (vnTensor A B).isTensorProduct σ τ a b
  have hposw : ∀ x : VNT A B, 0 ≤ x → 0 ≤ F (w * x) := by
    have heqχ : F.comp (ContinuousLinearMap.mul ℂ (VNT A B) w) = npCLM χ := by
      refine clm_ext_of_tmul (hcw w) (continuous_ultraweak_npFunctional χ)
        (fun a b => ?_)
      show F (w * (a ⊗ᵥ b)) = (χ (a ⊗ᵥ b) : ℂ)
      rw [hwdef, hmul, hFval, hχval, hσapp, hτapp]
    intro x hx
    have hxv : F (w * x) = (χ x : ℂ) :=
      congrArg (fun h : VNT A B →L[ℂ] ℂ => h x) heqχ
    rw [hxv]
    exact npFunctional_nonneg χ hx
  -- `F = F(w w* ·)`
  have heqw : ∀ x : VNT A B, F x = F (w * star w * x) := by
    have hcomp : F = F.comp (ContinuousLinearMap.mul ℂ (VNT A B) (w * star w)) := by
      refine clm_ext_of_tmul hFc (hcw (w * star w)) (fun a b => ?_)
      show F (a ⊗ᵥ b) = F (w * star w * (a ⊗ᵥ b))
      have hw : w * star w * (a ⊗ᵥ b) = (u * star u * a) ⊗ᵥ (v * star v * b) := by
        rw [hwdef, hstarw, hmul, hmul]
      rw [hw, hFval, hFval, ← h1u a, ← h1v b]
    intro x
    exact congrArg (fun h : VNT A B →L[ℂ] ℂ => h x) hcomp
  have hFw : F w = ((‖F‖ : ℝ) : ℂ) := functional_norm F hFc w hpiw hposw heqw
  -- the two one-sided norms
  have hfu : f u = ((‖f‖ : ℝ) : ℂ) := by
    rw [← hσone, hσapp 1, mul_one]
  have hgv : g v = ((‖g‖ : ℝ) : ℂ) := by
    rw [← hτone, hτapp 1, mul_one]
  have hval : F w = ((‖f‖ * ‖g‖ : ℝ) : ℂ) := by
    rw [hwdef, hFval, hfu, hgv, Complex.ofReal_mul]
  have := hFw.symm.trans hval
  exact_mod_cast this

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 3:
`⊗ : 𝒜_* × ℬ_* → (𝒜 ⊗ ℬ)_*` is norm continuous — rendered by the
estimate `‖f ⊗ g − f' ⊗ g'‖ ≤ ‖f − f'‖·‖g‖ + ‖f'‖·‖g − g'‖`. -/
theorem tensor_simple_facts_3 (f f' : A →L[ℂ] ℂ) (g g' : B →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f)
    (hf' : @Continuous A ℂ (ultraweak A) _ ⇑f')
    (hg : @Continuous B ℂ (ultraweak B) _ ⇑g)
    (hg' : @Continuous B ℂ (ultraweak B) _ ⇑g') :
    ‖predualTensor f g hf hg - predualTensor f' g' hf' hg'‖ ≤
      ‖f - f'‖ * ‖g‖ + ‖f'‖ * ‖g - g'‖ := by
  -- the thesis's argument: `f⊗g − f'⊗g' = (f−f')⊗g + f'⊗(g−g')`, then **116I**
  have hfs : @Continuous A ℂ (ultraweak A) _ ⇑(f - f') := by
    letI : TopologicalSpace A := ultraweak A
    have he : ⇑(f - f') = fun a : A => (f a : ℂ) - f' a := by funext a; simp
    rw [he]; exact hf.sub hf'
  have hgs : @Continuous B ℂ (ultraweak B) _ ⇑(g - g') := by
    letI : TopologicalSpace B := ultraweak B
    have he : ⇑(g - g') = fun b : B => (g b : ℂ) - g' b := by funext b; simp
    rw [he]; exact hg.sub hg'
  have hspec : ∀ (p : A →L[ℂ] ℂ) (q : B →L[ℂ] ℂ)
      (hp : @Continuous A ℂ (ultraweak A) _ ⇑p)
      (hq : @Continuous B ℂ (ultraweak B) _ ⇑q),
      (@Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑(predualTensor p q hp hq)) ∧
        ∀ (a : A) (b : B), predualTensor p q hp hq (a ⊗ᵥ b) = p a * q b :=
    fun p q hp hq => (exists_predualTensor p q hp hq).choose_spec.1
  have hkey : predualTensor f g hf hg - predualTensor f' g' hf' hg'
      = predualTensor (f - f') g hfs hg + predualTensor f' (g - g') hf' hgs := by
    refine clm_ext_of_tmul ?_ ?_ (fun a b => ?_)
    · letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
      have he : ⇑(predualTensor f g hf hg - predualTensor f' g' hf' hg')
          = fun x : VNT A B =>
            (predualTensor f g hf hg x : ℂ) - predualTensor f' g' hf' hg' x := by
        funext x; simp
      rw [he]
      exact (hspec f g hf hg).1.sub (hspec f' g' hf' hg').1
    · letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
      have he : ⇑(predualTensor (f - f') g hfs hg + predualTensor f' (g - g') hf' hgs)
          = fun x : VNT A B => (predualTensor (f - f') g hfs hg x : ℂ)
              + predualTensor f' (g - g') hf' hgs x := by
        funext x; simp
      rw [he]
      exact (hspec (f - f') g hfs hg).1.add (hspec f' (g - g') hf' hgs).1
    · show (predualTensor f g hf hg (a ⊗ᵥ b) : ℂ) - predualTensor f' g' hf' hg' (a ⊗ᵥ b)
        = predualTensor (f - f') g hfs hg (a ⊗ᵥ b)
            + predualTensor f' (g - g') hf' hgs (a ⊗ᵥ b)
      rw [(hspec f g hf hg).2, (hspec f' g' hf' hg').2,
        (hspec (f - f') g hfs hg).2, (hspec f' (g - g') hf' hgs).2]
      show (f a : ℂ) * g b - f' a * g' b
        = ((f a : ℂ) - f' a) * g b + (f' a : ℂ) * ((g b : ℂ) - g' b)
      ring
  calc ‖predualTensor f g hf hg - predualTensor f' g' hf' hg'‖
      = ‖predualTensor (f - f') g hfs hg + predualTensor f' (g - g') hf' hgs‖ := by
        rw [hkey]
    _ ≤ ‖predualTensor (f - f') g hfs hg‖ + ‖predualTensor f' (g - g') hf' hgs‖ :=
        norm_add_le _ _
    _ = ‖f - f'‖ * ‖g‖ + ‖f'‖ * ‖g - g'‖ := by
        rw [product_functional_norm, product_functional_norm]

/-- **116III**.3 in the form **116IV**.2 uses it: two normal functionals on
`𝒜 ⊗ ℬ` that factor on pure tensors are compared by the cross-norm estimate.
(Both are the corresponding `predualTensor`, by the uniqueness clause of
**116I**.) -/
private theorem norm_sub_le_of_tmul_factor (F G : VNT A B →L[ℂ] ℂ)
    (hFc : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑F)
    (hGc : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑G)
    (p p' : A →L[ℂ] ℂ) (q q' : B →L[ℂ] ℂ)
    (hp : @Continuous A ℂ (ultraweak A) _ ⇑p)
    (hp' : @Continuous A ℂ (ultraweak A) _ ⇑p')
    (hq : @Continuous B ℂ (ultraweak B) _ ⇑q)
    (hq' : @Continuous B ℂ (ultraweak B) _ ⇑q')
    (hF : ∀ (a : A) (b : B), F (a ⊗ᵥ b) = p a * q b)
    (hG : ∀ (a : A) (b : B), G (a ⊗ᵥ b) = p' a * q' b) :
    ‖F - G‖ ≤ ‖p - p'‖ * ‖q‖ + ‖p'‖ * ‖q - q'‖ := by
  have hFeq : F = predualTensor p q hp hq :=
    (exists_predualTensor p q hp hq).unique ⟨hFc, hF⟩
      (exists_predualTensor p q hp hq).choose_spec.1
  have hGeq : G = predualTensor p' q' hp' hq' :=
    (exists_predualTensor p' q' hp' hq').unique ⟨hGc, hG⟩
      (exists_predualTensor p' q' hp' hq').choose_spec.1
  rw [hFeq, hGeq]
  exact tensor_simple_facts_3 p p' q q' hp hp' hq hq'

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 4:
`⊗ : 𝒜 × ℬ → 𝒜 ⊗ ℬ` is (jointly) ultraweakly continuous. -/
theorem tensor_simple_facts_4 :
    @Continuous (A × B) (VNT A B)
      (@instTopologicalSpaceProd A B (ultraweak A) (ultraweak B))
      (ultraweak (VNT A B)) (fun p => p.1 ⊗ᵥ p.2) := sorry

/-! ### 116III.5, and the ultraweak continuity of `a ⊗ (·)`

The np-functionals `χ` on `𝒜 ⊗ ℬ` are only *operator-norm* limits of members
of `Ω` (**112X**.1.2), and only the latter come with the `∑ₖₗ` expansion that
exhibits `b ↦ χ(a ⊗ b)` as ultraweakly continuous.  Since
`‖a ⊗ b‖ ≤ ‖a‖‖b‖`, the transported limit is uniform on the unit ball of
`ℬ`, i.e. a limit in the operator norm of `ℬ_*` — so the normal-limit lemma
`continuous_ultraweak_of_normLimit` (**87III**) applies. -/

/-- The `≤` half of **116III**.2, in tensor-norm form. -/
private theorem tensorNorm_tmul_le (a : A) (b : B) :
    tensorNorm A B (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ := by
  refine Real.sSup_le (fun r hr => ?_) (by positivity)
  obtain ⟨ω, hω, h1, rfl⟩ := hr
  exact tsn_tmul_le hω h1 a b

/-- The `≤` half of **116III**.2: `‖a ⊗ b‖ ≤ ‖a‖‖b‖`. -/
theorem norm_vtmul_le (a : A) (b : B) : ‖a ⊗ᵥ b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : (a ⊗ᵥ b) = TensorProduct.lift (vnTensor A B).map (a ⊗ₜ[ℂ] b) := by
    rw [TensorProduct.lift.tmul]; rfl
  rw [h, tensor_basic_2 (vnTensor A B).map (vnTensor A B).isTensorProduct]
  exact tensorNorm_tmul_le a b

/-- The `≥` half of **116III**.2, in tensor-norm form.  The basic functional
`σ ⊙ τ` (witness `t₀ = 1`) sends `(a ⊙ b)*(a ⊙ b) = (a* a) ⊙ (b* b)` to
`σ(a* a)·τ(b* b)`, so `‖a ⊙ b‖ ≥ σ(a* a)^½ τ(b* b)^½`; both factors are pushed
to `‖a‖`, `‖b‖` by `exists_npFunctional_ge_omegaNorm_sub`, which is exactly
the *subunital* form of **21VII** `order_separating_norm` that the supremum
defining `tensorNorm` runs over. -/
private theorem le_tensorNorm_tmul (a : A) (b : B) :
    ‖a‖ * ‖b‖ ≤ tensorNorm A B (a ⊗ₜ[ℂ] b) := by
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  set ε : ℝ := δ / (‖a‖ + ‖b‖ + 1) with hεdef
  have hna : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hnb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεsum : ε * (‖a‖ + ‖b‖) ≤ δ := by
    have hd : ε * (‖a‖ + ‖b‖ + 1) = δ := by
      rw [hεdef]; field_simp
    nlinarith
  obtain ⟨σ, hσ1, hσa⟩ := exists_npFunctional_ge_omegaNorm_sub a hε
  obtain ⟨τ, hτ1, hτb⟩ := exists_npFunctional_ge_omegaNorm_sub b hε
  set ω : A ⊗[ℂ] B →ₗ[ℂ] ℂ := odotF (npLin σ) (npLin τ) with hωdef
  have hωb : IsBasicFunctional ω := isBasicFunctional_odotF σ τ
  -- the two values are nonnegative reals
  have hσ0 := Complex.le_def.mp (npFunctional_nonneg σ (star_mul_self_nonneg a))
  have hτ0 := Complex.le_def.mp (npFunctional_nonneg τ (star_mul_self_nonneg b))
  have hσ01 := Complex.le_def.mp (npFunctional_nonneg σ (zero_le_one (α := A)))
  have hτ01 := Complex.le_def.mp (npFunctional_nonneg τ (zero_le_one (α := B)))
  have him1 : ((σ (1 : A) : ℂ)).im = 0 := by simpa using hσ01.2.symm
  have him2 : ((τ (1 : B) : ℂ)).im = 0 := by simpa using hτ01.2.symm
  have hre2 : (0 : ℝ) ≤ (τ (1 : B)).re := by simpa using hτ01.1
  have hω1 : (ω 1).re ≤ 1 := by
    have hval : ω (1 : A ⊗[ℂ] B) = (σ 1 : ℂ) * (τ 1 : ℂ) := by
      rw [hωdef, Algebra.TensorProduct.one_def, odotF_tmul]; rfl
    rw [hval, Complex.mul_re, him1, him2, mul_zero, sub_zero]
    calc (σ (1 : A)).re * (τ (1 : B)).re ≤ 1 * 1 :=
          mul_le_mul hσ1 hτ1 hre2 zero_le_one
      _ = 1 := one_mul 1
  have hstar : star (a ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] b)
      = (star a * a) ⊗ₜ[ℂ] (star b * b) := by
    rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  have hval : (ω (star (a ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] b))).re
      = (σ (star a * a)).re * (τ (star b * b)).re := by
    have he : ω (star (a ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] b))
        = (σ (star a * a) : ℂ) * (τ (star b * b) : ℂ) := by
      rw [hstar, hωdef, odotF_tmul]; rfl
    have hia : ((σ (star a * a) : ℂ)).im = 0 := by simpa using hσ0.2.symm
    have hib : ((τ (star b * b) : ℂ)).im = 0 := by simpa using hτ0.2.symm
    rw [he, Complex.mul_re, hia, hib, mul_zero, sub_zero]
  have hmem := le_csSup (tnSet_bddAbove (a ⊗ₜ[ℂ] b))
    (⟨ω, hωb, hω1, rfl⟩ :
      Real.sqrt (ω (star (a ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] b))).re ∈ tnSet (a ⊗ₜ[ℂ] b))
  rw [← tensorNorm_eq_sSup, hval,
    Real.sqrt_mul (by simpa using hσ0.1)] at hmem
  -- combine the two approximations
  set X : ℝ := Real.sqrt (σ (star a * a)).re with hXdef
  set Y : ℝ := Real.sqrt (τ (star b * b)).re with hYdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hprod : ‖a‖ * ‖b‖ ≤ X * Y + δ := by
    rcases le_or_gt ε ‖a‖ with hA | hA
    · rcases le_or_gt ε ‖b‖ with hB | hB
      · nlinarith
      · nlinarith
    · nlinarith
  linarith

/-- **116III**.2: `‖a ⊗ b‖ = ‖a‖·‖b‖`. -/
theorem norm_vtmul (a : A) (b : B) : ‖a ⊗ᵥ b‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (norm_vtmul_le a b) ?_
  have h : (a ⊗ᵥ b) = TensorProduct.lift (vnTensor A B).map (a ⊗ₜ[ℂ] b) := by
    rw [TensorProduct.lift.tmul]; rfl
  rw [h, tensor_basic_2 (vnTensor A B).map (vnTensor A B).isTensorProduct]
  exact le_tensorNorm_tmul a b

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 2:
`‖a ⊗ b‖ = ‖a‖·‖b‖`, and `⊗ : 𝒜 × ℬ → 𝒜 ⊗ ℬ` is norm continuous. -/
theorem tensor_simple_facts_2 :
    (∀ (a : A) (b : B), ‖a ⊗ᵥ b‖ = ‖a‖ * ‖b‖) ∧
      Continuous fun p : A × B => p.1 ⊗ᵥ p.2 := by
  refine ⟨norm_vtmul, ?_⟩
  -- the thesis's warning that this "is not entirely trivial" is the
  -- bilinearity step: `⊗` is a bounded bilinear map with constant `1`.
  have hbd : ∀ (a : A) (b : B), ‖(vnTensor A B).map a b‖ ≤ 1 * ‖a‖ * ‖b‖ := by
    intro a b
    rw [one_mul]
    exact le_of_eq (norm_vtmul a b)
  exact (LinearMap.mkContinuous₂ (vnTensor A B).map 1 hbd).continuous₂

/-- `b ↦ χ(a ⊗ b)` as a continuous linear functional on `ℬ`. -/
private noncomputable def npTmulRight (χ : NPFunctional (VNT A B)) (a : A) :
    B →L[ℂ] ℂ :=
  LinearMap.mkContinuous ((npLin χ).comp ((vnTensor A B).map a))
    ((χ 1).re * ‖a‖) (fun b => by
      have h1 : ‖(χ (a ⊗ᵥ b) : ℂ)‖ ≤ (χ 1).re * ‖a ⊗ᵥ b‖ :=
        npFunctional_norm_le χ _
      have h0 : (0 : ℝ) ≤ (χ 1).re := by
        simpa using (Complex.le_def.mp (npFunctional_nonneg χ zero_le_one)).1
      calc ‖((npLin χ).comp ((vnTensor A B).map a)) b‖
          = ‖(χ (a ⊗ᵥ b) : ℂ)‖ := rfl
        _ ≤ (χ 1).re * ‖a ⊗ᵥ b‖ := h1
        _ ≤ (χ 1).re * (‖a‖ * ‖b‖) :=
            mul_le_mul_of_nonneg_left (norm_vtmul_le a b) h0
        _ = (χ 1).re * ‖a‖ * ‖b‖ := by ring)

@[simp] private theorem npTmulRight_apply (χ : NPFunctional (VNT A B)) (a : A)
    (b : B) : npTmulRight χ a b = χ (a ⊗ᵥ b) := rfl

/-- For a member `χ` of `Ω` the functional `b ↦ χ(a ⊗ b)` is ultraweakly
continuous: it is the finite sum `∑ₖₗ σ(cₖ* a c_l) τ(dₖ*(·)d_l)`. -/
private theorem continuous_npTmulRight_conjProdNP (a : A) (σ : NPFunctional A)
    (τ : NPFunctional B) (s : A ⊗[ℂ] B) :
    @Continuous B ℂ (ultraweak B) _
      ⇑(npTmulRight (conjProdNP (vnTensor A B).isTensorProduct σ τ s) a) := by
  classical
  obtain ⟨N, c, d, hs⟩ := exists_fin_repr s
  letI : TopologicalSpace B := ultraweak B
  have hval : ⇑(npTmulRight (conjProdNP (vnTensor A B).isTensorProduct σ τ s) a)
      = fun b : B => ∑ k, ∑ l, σ (star (c k) * a * c l) * τ (star (d k) * b * d l) := by
    funext b
    show (conjProdNP (vnTensor A B).isTensorProduct σ τ s) (a ⊗ᵥ b) = _
    have h1 : (a ⊗ᵥ b) = TensorProduct.lift (vnTensor A B).map (a ⊗ₜ[ℂ] b) := by
      rw [TensorProduct.lift.tmul]; rfl
    rw [h1, conjProdNP_lift (vnTensor A B).isTensorProduct, hs,
      star_tmul_conj_expand c d a b, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [odotF_tmul]; rfl
  rw [hval]
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  refine continuous_const.mul ?_
  have h1 : Continuous (fun z : B => star (d k) * z) := (mult_uws_cont (star (d k))).1
  have h2 : Continuous (fun z : B => z * d l) := (mult_uws_cont (d l)).2.1
  exact (continuous_ultraweak_npFunctional τ).comp (h2.comp h1)

/-- **116III**.5, the normality half: `a ⊗ (·)` is ultraweakly continuous. -/
theorem continuous_ultraweak_vtmul_right (a : A) :
    @Continuous B (VNT A B) (ultraweak B) (ultraweak (VNT A B))
      (fun b => a ⊗ᵥ b) := by
  classical
  refine continuous_ultraweak_of_forall' (ultraweak B) _ (fun χ => ?_)
  have hF : @Continuous B ℂ (ultraweak B) _ ⇑(npTmulRight χ a) := by
    refine continuous_ultraweak_of_normLimit (npTmulRight χ a) (fun ε hε => ?_)
    obtain ⟨n, σ, τ, s, hb⟩ :=
      (tensor_basic_1 (vnTensor A B).map (vnTensor A B).isTensorProduct).2 χ
        (ε / (‖a‖ + 1)) (by positivity)
    refine ⟨∑ i, npTmulRight
      (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) a, ?_, ?_⟩
    · letI : TopologicalSpace B := ultraweak B
      have hfun : ⇑(∑ i, npTmulRight
          (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) a)
          = fun b : B => ∑ i, npTmulRight
            (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) a b := by
        funext b; simp
      rw [hfun]
      exact continuous_finsetSum _ fun i _ =>
        continuous_npTmulRight_conjProdNP a (σ i) (τ i) (s i)
    · refine ContinuousLinearMap.opNorm_le_bound _ hε.le (fun b => ?_)
      have hb' := hb (a ⊗ᵥ b)
      have hnorm : ‖a ⊗ᵥ b‖ ≤ ‖a‖ * ‖b‖ := norm_vtmul_le a b
      have hpt : ‖(npTmulRight χ a - ∑ i, npTmulRight
          (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) a) b‖
          ≤ ε / (‖a‖ + 1) * ‖a ⊗ᵥ b‖ := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
        exact hb'
      refine hpt.trans ?_
      have h0 : (0 : ℝ) ≤ ε / (‖a‖ + 1) := by positivity
      have hle : ‖a‖ / (‖a‖ + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [norm_nonneg a]
      have he : ε / (‖a‖ + 1) * (‖a‖ * ‖b‖) = ε * (‖a‖ / (‖a‖ + 1)) * ‖b‖ := by
        field_simp
      calc ε / (‖a‖ + 1) * ‖a ⊗ᵥ b‖
          ≤ ε / (‖a‖ + 1) * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_left hnorm h0
        _ = ε * (‖a‖ / (‖a‖ + 1)) * ‖b‖ := he
        _ ≤ ε * 1 * ‖b‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg b)
            exact mul_le_mul_of_nonneg_left hle hε.le
        _ = ε * ‖b‖ := by ring
  exact hF

/-! ### The mirror: `(·) ⊗ b` is ultraweakly continuous

**116IV**.1 needs ultraweak continuity of `⊗` in *each* variable separately
(**116III**.4, joint continuity, is not available — see the note above), so the
argument of `continuous_ultraweak_vtmul_right` is repeated with the roles of
the two factors exchanged.  The expansion is the same one, `star_tmul_conj_expand`;
only which of its two factors carries the variable changes. -/

/-- `a ↦ χ(a ⊗ b)` as a continuous linear functional on `𝒜`. -/
private noncomputable def npTmulLeft (χ : NPFunctional (VNT A B)) (b : B) :
    A →L[ℂ] ℂ :=
  LinearMap.mkContinuous ((npLin χ).comp ((vnTensor A B).map.flip b))
    ((χ 1).re * ‖b‖) (fun a => by
      have h1 : ‖(χ (a ⊗ᵥ b) : ℂ)‖ ≤ (χ 1).re * ‖a ⊗ᵥ b‖ :=
        npFunctional_norm_le χ _
      have h0 : (0 : ℝ) ≤ (χ 1).re := by
        simpa using (Complex.le_def.mp (npFunctional_nonneg χ zero_le_one)).1
      calc ‖((npLin χ).comp ((vnTensor A B).map.flip b)) a‖
          = ‖(χ (a ⊗ᵥ b) : ℂ)‖ := rfl
        _ ≤ (χ 1).re * ‖a ⊗ᵥ b‖ := h1
        _ ≤ (χ 1).re * (‖a‖ * ‖b‖) :=
            mul_le_mul_of_nonneg_left (norm_vtmul_le a b) h0
        _ = (χ 1).re * ‖b‖ * ‖a‖ := by ring)

@[simp] private theorem npTmulLeft_apply (χ : NPFunctional (VNT A B)) (b : B)
    (a : A) : npTmulLeft χ b a = χ (a ⊗ᵥ b) := rfl

/-- For a member `χ` of `Ω` the functional `a ↦ χ(a ⊗ b)` is ultraweakly
continuous: it is the finite sum `∑ₖₗ σ(cₖ*(·)c_l) τ(dₖ* b d_l)`. -/
private theorem continuous_npTmulLeft_conjProdNP (b : B) (σ : NPFunctional A)
    (τ : NPFunctional B) (s : A ⊗[ℂ] B) :
    @Continuous A ℂ (ultraweak A) _
      ⇑(npTmulLeft (conjProdNP (vnTensor A B).isTensorProduct σ τ s) b) := by
  classical
  obtain ⟨N, c, d, hs⟩ := exists_fin_repr s
  letI : TopologicalSpace A := ultraweak A
  have hval : ⇑(npTmulLeft (conjProdNP (vnTensor A B).isTensorProduct σ τ s) b)
      = fun a : A => ∑ k, ∑ l, σ (star (c k) * a * c l) * τ (star (d k) * b * d l) := by
    funext a
    show (conjProdNP (vnTensor A B).isTensorProduct σ τ s) (a ⊗ᵥ b) = _
    have h1 : (a ⊗ᵥ b) = TensorProduct.lift (vnTensor A B).map (a ⊗ₜ[ℂ] b) := by
      rw [TensorProduct.lift.tmul]; rfl
    rw [h1, conjProdNP_lift (vnTensor A B).isTensorProduct, hs,
      star_tmul_conj_expand c d a b, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [odotF_tmul]; rfl
  rw [hval]
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  refine Continuous.mul ?_ continuous_const
  have h1 : Continuous (fun z : A => star (c k) * z) := (mult_uws_cont (star (c k))).1
  have h2 : Continuous (fun z : A => z * c l) := (mult_uws_cont (c l)).2.1
  exact (continuous_ultraweak_npFunctional σ).comp (h2.comp h1)

/-- The mirror of **116III**.5's normality half: `(·) ⊗ b` is ultraweakly
continuous. -/
theorem continuous_ultraweak_vtmul_left (b : B) :
    @Continuous A (VNT A B) (ultraweak A) (ultraweak (VNT A B))
      (fun a => a ⊗ᵥ b) := by
  classical
  refine continuous_ultraweak_of_forall' (ultraweak A) _ (fun χ => ?_)
  have hF : @Continuous A ℂ (ultraweak A) _ ⇑(npTmulLeft χ b) := by
    refine continuous_ultraweak_of_normLimit (npTmulLeft χ b) (fun ε hε => ?_)
    obtain ⟨n, σ, τ, s, hb⟩ :=
      (tensor_basic_1 (vnTensor A B).map (vnTensor A B).isTensorProduct).2 χ
        (ε / (‖b‖ + 1)) (by positivity)
    refine ⟨∑ i, npTmulLeft
      (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) b, ?_, ?_⟩
    · letI : TopologicalSpace A := ultraweak A
      have hfun : ⇑(∑ i, npTmulLeft
          (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) b)
          = fun a : A => ∑ i, npTmulLeft
            (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) b a := by
        funext a; simp
      rw [hfun]
      exact continuous_finsetSum _ fun i _ =>
        continuous_npTmulLeft_conjProdNP b (σ i) (τ i) (s i)
    · refine ContinuousLinearMap.opNorm_le_bound _ hε.le (fun a => ?_)
      have hb' := hb (a ⊗ᵥ b)
      have hnorm : ‖a ⊗ᵥ b‖ ≤ ‖a‖ * ‖b‖ := norm_vtmul_le a b
      have hpt : ‖(npTmulLeft χ b - ∑ i, npTmulLeft
          (conjProdNP (vnTensor A B).isTensorProduct (σ i) (τ i) (s i)) b) a‖
          ≤ ε / (‖b‖ + 1) * ‖a ⊗ᵥ b‖ := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
        exact hb'
      refine hpt.trans ?_
      have h0 : (0 : ℝ) ≤ ε / (‖b‖ + 1) := by positivity
      have hle : ‖b‖ / (‖b‖ + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [norm_nonneg b]
      have he : ε / (‖b‖ + 1) * (‖a‖ * ‖b‖) = ε * (‖b‖ / (‖b‖ + 1)) * ‖a‖ := by
        field_simp
      calc ε / (‖b‖ + 1) * ‖a ⊗ᵥ b‖
          ≤ ε / (‖b‖ + 1) * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_left hnorm h0
        _ = ε * (‖b‖ / (‖b‖ + 1)) * ‖a‖ := he
        _ ≤ ε * 1 * ‖a‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg a)
            exact mul_le_mul_of_nonneg_left hle hε.le
        _ = ε * ‖a‖ := by ring
  exact hF

/-- **116III** (`tensor-simple-facts`, proc.tex:3427, Exercise), part 5:
`a ⊗ (·) : ℬ → 𝒜 ⊗ ℬ` is an ncp-map for positive `a`, and `1 ⊗ (·)` is
an nmiu-map. -/
theorem tensor_simple_facts_5 (a : A) (ha : 0 ≤ a) :
    (∃ f : NCPMap B (VNT A B), ∀ b, f b = a ⊗ᵥ b) ∧
      ∃ ρ : NMIUMap B (VNT A B), ∀ b, ρ b = (1 : A) ⊗ᵥ b := by
  have hmiu := (vnTensor A B).isTensorProduct.miu
  have hstar : ∀ (x : A) (y : B), star (x ⊗ᵥ y) = star x ⊗ᵥ star y :=
    fun x y => hmiu.2.2 x y
  have hmul : ∀ (x x' : A) (y y' : B),
      (x ⊗ᵥ y) * (x' ⊗ᵥ y') = (x * x') ⊗ᵥ (y * y') :=
    fun x x' y y' => (hmiu.2.1 x x' y y').symm
  -- the positive linear map `x ⊗ (·)`, and its normality
  have hpos : ∀ x : A, 0 ≤ x → ∀ b b' : B, b ≤ b' → x ⊗ᵥ b ≤ x ⊗ᵥ b' := by
    intro x hx b b' hb
    have h := vtmul_nonneg x (b' - b) hx (sub_nonneg.mpr hb)
    rw [show (x ⊗ᵥ (b' - b)) = x ⊗ᵥ b' - x ⊗ᵥ b from
      map_sub ((vnTensor A B).map x) b' b] at h
    exact sub_nonneg.mp h
  have hdir : ∀ x : A, 0 ≤ x → ∀ p : B →ₚ[ℂ] VNT A B,
      (∀ b, p b = x ⊗ᵥ b) → PreservesDirSups ⇑p := by
    intro x hx p hp
    refine ((p_uwcont p).out 0 2).mp ?_
    have hfun : ⇑p = fun b => x ⊗ᵥ b := funext hp
    rw [hfun]
    exact continuous_ultraweak_vtmul_right x
  -- complete positivity: `a = x* x` makes the double sum a square
  have hcp : Theses.A.CStar.IsCompletelyPositiveMap ((vnTensor A B).map a) := by
    obtain ⟨x, hx⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    intro n b c
    have hterm : ∀ i j : Fin n, star (c i) * (a ⊗ᵥ (star (b i) * b j)) * c j
        = star ((x ⊗ᵥ b i) * c i) * ((x ⊗ᵥ b j) * c j) := by
      intro i j
      have h1 : star (x ⊗ᵥ b i) * (x ⊗ᵥ b j) = a ⊗ᵥ (star (b i) * b j) := by
        rw [hstar, hmul, ← hx]
      rw [star_mul, ← h1]
      noncomm_ring
    have he : ∑ i, ∑ j, star (c i) * (a ⊗ᵥ (star (b i) * b j)) * c j
        = star (∑ i, (x ⊗ᵥ b i) * c i) * ∑ j, (x ⊗ᵥ b j) * c j := by
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hterm i j
    show (0 : VNT A B) ≤ ∑ i, ∑ j, star (c i) * (a ⊗ᵥ (star (b i) * b j)) * c j
    rw [he]
    exact star_mul_self_nonneg _
  have hcpm : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) B),
      0 ≤ M → 0 ≤ M.map ⇑((vnTensor A B).map a) :=
    ((Theses.A.CStar.cp_iff _).out 0 1).mp hcp
  refine ⟨⟨⟨{ toLinearMap := (vnTensor A B).map a
              map_cstarMatrix_nonneg' := fun k M hM => hcpm k M hM },
      hdir a ha { toFun := fun b => a ⊗ᵥ b
                  map_add' := fun x y => map_add ((vnTensor A B).map a) x y
                  map_smul' := fun r x => map_smul ((vnTensor A B).map a) r x
                  monotone' := fun x y hxy => hpos a ha x y hxy }
        (fun _ => rfl)⟩, fun _ => rfl⟩, ?_⟩
  -- the nmiu-map `1 ⊗ (·)`
  refine ⟨{ toStarAlgHom :=
              { toFun := fun b => (1 : A) ⊗ᵥ b
                map_one' := hmiu.1
                map_mul' := fun x y => by
                  have h := hmiu.2.1 (1 : A) (1 : A) x y
                  rwa [one_mul] at h
                map_zero' := map_zero ((vnTensor A B).map 1)
                map_add' := fun x y => map_add ((vnTensor A B).map 1) x y
                commutes' := fun r => by
                  rw [Algebra.algebraMap_eq_smul_one,
                    Algebra.algebraMap_eq_smul_one]
                  show (vnTensor A B).map 1 (r • (1 : B)) = r • (1 : VNT A B)
                  rw [map_smul, hmiu.1]
                map_star' := fun b => by
                  have h := hmiu.2.2 (1 : A) b
                  rw [star_one] at h
                  exact h.symm }
            preservesDirSups' :=
              hdir 1 zero_le_one
                { toFun := fun b => (1 : A) ⊗ᵥ b
                  map_add' := fun x y => map_add ((vnTensor A B).map 1) x y
                  map_smul' := fun r x => map_smul ((vnTensor A B).map 1) r x
                  monotone' := fun x y hxy => hpos 1 zero_le_one x y hxy }
                (fun _ => rfl) }, fun _ => rfl⟩

/-- **116IV** (`tensor-generation`, proc.tex:3489, Proposition), part 1:
if the linear spans of `S ⊆ 𝒜` and `T ⊆ ℬ` are ultraweakly dense, then
the linear span of `{s ⊗ t}` is ultraweakly dense in `𝒜 ⊗ ℬ`. -/
theorem tensor_generation_1 (S : Set A) (T : Set B)
    (hS : @Dense A (ultraweak A) (Submodule.span ℂ S : Set A))
    (hT : @Dense B (ultraweak B) (Submodule.span ℂ T : Set B)) :
    @Dense (VNT A B) (ultraweak (VNT A B))
      (Submodule.span ℂ {x : VNT A B | ∃ s ∈ S, ∃ t ∈ T, x = s ⊗ᵥ t} :
        Set (VNT A B)) := by
  -- The thesis (proc.tex:3510) runs this through **116III**.4, joint ultraweak
  -- continuity of `⊗`; that is not available (see the note at 116III.4), and
  -- the *separate* continuity of the two slices is enough, since the closure
  -- of a submodule is a submodule.
  letI : TopologicalSpace A := ultraweak A
  letI : TopologicalSpace B := ultraweak B
  letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
  haveI : IsTopologicalAddGroup (VNT A B) := ultraweak_isTopologicalAddGroup
  haveI : ContinuousSMul ℂ (VNT A B) := ultraweak_continuousSMul_complex
  set P : Submodule ℂ (VNT A B) :=
    Submodule.span ℂ {x : VNT A B | ∃ s ∈ S, ∃ t ∈ T, x = s ⊗ᵥ t} with hPdef
  set M : Submodule ℂ (VNT A B) := P.topologicalClosure with hMdef
  have hMclosed : IsClosed (M : Set (VNT A B)) := P.isClosed_topologicalClosure
  have hPM : (P : Set (VNT A B)) ⊆ (M : Set (VNT A B)) := P.le_topologicalClosure
  -- Step 1: `s ⊗ y ∈ P` for `s ∈ S` and `y` in the span of `T`
  have hstep1 : ∀ s ∈ S, ∀ y ∈ (Submodule.span ℂ T : Set B), s ⊗ᵥ y ∈ P := by
    intro s hs y hy
    induction hy using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span ⟨s, hs, u, hu, rfl⟩
    | zero => rw [show s ⊗ᵥ (0 : B) = 0 from map_zero ((vnTensor A B).map s)]
              exact P.zero_mem
    | add u v _ _ hu hv =>
        rw [show s ⊗ᵥ (u + v) = s ⊗ᵥ u + s ⊗ᵥ v from map_add ((vnTensor A B).map s) u v]
        exact P.add_mem hu hv
    | smul c u _ hu =>
        rw [show s ⊗ᵥ (c • u) = c • (s ⊗ᵥ u) from map_smul ((vnTensor A B).map s) c u]
        exact P.smul_mem c hu
  -- Step 2: `s ⊗ b ∈ M` for `s ∈ S` and every `b`, by right-continuity
  have hstep2 : ∀ s ∈ S, ∀ b : B, s ⊗ᵥ b ∈ M := by
    intro s hs b
    have hcont : Continuous (fun y : B => s ⊗ᵥ y) := continuous_ultraweak_vtmul_right s
    have himg : (fun y : B => s ⊗ᵥ y) '' (Submodule.span ℂ T : Set B)
        ⊆ (M : Set (VNT A B)) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hPM (hstep1 s hs y hy)
    have hb : b ∈ closure ((Submodule.span ℂ T : Set B)) := by
      rw [hT.closure_eq]; trivial
    have h := image_closure_subset_closure_image hcont
      (s := (Submodule.span ℂ T : Set B)) ⟨b, hb, rfl⟩
    exact hMclosed.closure_subset_iff.mpr himg h
  -- Step 3: `x ⊗ b ∈ M` for `x` in the span of `S`
  have hstep3 : ∀ b : B, ∀ x ∈ (Submodule.span ℂ S : Set A), x ⊗ᵥ b ∈ M := by
    intro b x hx
    induction hx using Submodule.span_induction with
    | mem u hu => exact hstep2 u hu b
    | zero =>
        rw [show (0 : A) ⊗ᵥ b = 0 from by
          rw [show ((0 : A) ⊗ᵥ b) = (vnTensor A B).map 0 b from rfl, map_zero]; rfl]
        exact M.zero_mem
    | add u v _ _ hu hv =>
        rw [show (u + v) ⊗ᵥ b = u ⊗ᵥ b + v ⊗ᵥ b from by
          rw [show ((u + v) ⊗ᵥ b) = (vnTensor A B).map (u + v) b from rfl, map_add]; rfl]
        exact M.add_mem hu hv
    | smul c u _ hu =>
        rw [show (c • u) ⊗ᵥ b = c • (u ⊗ᵥ b) from by
          rw [show ((c • u) ⊗ᵥ b) = (vnTensor A B).map (c • u) b from rfl, map_smul]; rfl]
        exact M.smul_mem c hu
  -- Step 4: every pure tensor is in `M`, by left-continuity
  have hstep4 : ∀ (a : A) (b : B), a ⊗ᵥ b ∈ M := by
    intro a b
    have hcont : Continuous (fun x : A => x ⊗ᵥ b) := continuous_ultraweak_vtmul_left b
    have himg : (fun x : A => x ⊗ᵥ b) '' (Submodule.span ℂ S : Set A)
        ⊆ (M : Set (VNT A B)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hstep3 b x hx
    have ha : a ∈ closure ((Submodule.span ℂ S : Set A)) := by
      rw [hS.closure_eq]; trivial
    have h := image_closure_subset_closure_image hcont
      (s := (Submodule.span ℂ S : Set A)) ⟨a, ha, rfl⟩
    exact hMclosed.closure_subset_iff.mpr himg h
  -- Step 5: conclude by 108II(1)
  have hspan : Submodule.span ℂ {t : VNT A B | ∃ a b, t = (vnTensor A B).map a b} ≤ M := by
    rw [Submodule.span_le]
    rintro x ⟨a, b, rfl⟩
    exact hstep4 a b
  have hdM : Dense (M : Set (VNT A B)) :=
    Dense.mono hspan (vnTensor A B).isTensorProduct.dense
  have hMuniv : (M : Set (VNT A B)) = Set.univ := by
    rw [← hMclosed.closure_eq, hdM.closure_eq]
  have hMtop : M = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    rw [← SetLike.mem_coe, hMuniv]
    trivial
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hMtop

/-- **116IV** (`tensor-generation`, proc.tex:3489, Proposition), part 2:
centre separating collections `Ω`, `Θ` of np-functionals on `𝒜`, `ℬ`
yield a centre separating collection `{ω ⊗ θ}` on `𝒜 ⊗ ℬ`. -/
theorem tensor_generation_2 (Ω : Set (NPFunctional A))
    (Θ : Set (NPFunctional B)) (hΩ : CentreSeparatingConj A Ω)
    (hΘ : CentreSeparatingConj B Θ) :
    CentreSeparatingConj (VNT A B)
      {χ : NPFunctional (VNT A B) | ∃ ω ∈ Ω, ∃ θ ∈ Θ,
        ∀ (a : A) (b : B), χ (a ⊗ᵥ b) = ω a * θ b} := by
  classical
  -- The thesis's proof (proc.tex:3538): it is enough that *every* product
  -- functional `σ ⊗ τ` kills `t` (108II(3)), and **90II**.2 makes `σ` an
  -- operator-norm limit of sums `∑ₖ ωₖ(sₖ*(·)sₖ)` with `ωₖ ∈ Ω`, likewise `τ`;
  -- **116III**.3 transports the two limits to `𝒜 ⊗ ℬ`.
  rw [centreSeparatingConj_iff]
  intro t ht
  refine ⟨fun h χ _ v => by rw [h]; simp, fun hkill => ?_⟩
  refine (vnTensor A B).isTensorProduct.faithful t ht (fun σ τ h hval => ?_)
  have hvalv : ∀ (a : A) (b : B), (h (a ⊗ᵥ b) : ℂ) = (σ a : ℂ) * τ b := hval
  have hhc : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑(npCLM h) :=
    continuous_ultraweak_npFunctional h
  have hdA : @Dense A (ultrastrong A) (Set.univ : Set A) := by
    letI : TopologicalSpace A := ultrastrong A; exact dense_univ
  have hdB : @Dense B (ultrastrong B) (Set.univ : Set B) := by
    letI : TopologicalSpace B := ultrastrong B; exact dense_univ
  -- the ε-estimate
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(h t : ℂ)‖ ≤ ε * (‖npCLM σ‖ + ‖npCLM τ‖ + 1) * ‖t‖ := by
    intro ε hε hε1
    obtain ⟨n, ω, s, hωs, hσap⟩ :=
      vn_center_separating_fundamental_2 Ω hΩ Set.univ hdA σ ε hε
    obtain ⟨m, θ, r, hθr, hτap⟩ :=
      vn_center_separating_fundamental_2 Θ hΘ Set.univ hdB τ ε hε
    -- the approximating functionals `σ'`, `τ'`
    set σlin : A →ₗ[ℂ] ℂ := ∑ k, (npLin (ω k)).comp
      ((LinearMap.mulRight ℂ (s k)).comp (LinearMap.mulLeft ℂ (star (s k))))
      with hσlindef
    have hσlinapp : ∀ a : A, σlin a = ∑ k, ((ω k) (star (s k) * a * s k) : ℂ) := by
      intro a
      rw [hσlindef]
      simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
      rfl
    set τlin : B →ₗ[ℂ] ℂ := ∑ l, (npLin (θ l)).comp
      ((LinearMap.mulRight ℂ (r l)).comp (LinearMap.mulLeft ℂ (star (r l))))
      with hτlindef
    have hτlinapp : ∀ b : B, τlin b = ∑ l, ((θ l) (star (r l) * b * r l) : ℂ) := by
      intro b
      rw [hτlindef]
      simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
      rfl
    have hσdiff : ∀ a : A, ‖(σ a : ℂ) - σlin a‖ ≤ ε * ‖a‖ := by
      intro a; rw [hσlinapp a]; exact hσap a
    have hτdiff : ∀ b : B, ‖(τ b : ℂ) - τlin b‖ ≤ ε * ‖b‖ := by
      intro b; rw [hτlinapp b]; exact hτap b
    have hσbd : ∀ a : A, ‖σlin a‖ ≤ (‖npCLM σ‖ + ε) * ‖a‖ := by
      intro a
      have h1 : ‖(σ a : ℂ)‖ ≤ ‖npCLM σ‖ * ‖a‖ := (npCLM σ).le_opNorm a
      have h2 := hσdiff a
      have h3 : ‖σlin a‖ ≤ ‖(σ a : ℂ)‖ + ‖(σ a : ℂ) - σlin a‖ := by
        have := norm_sub_le (σ a : ℂ) ((σ a : ℂ) - σlin a)
        simpa using this
      nlinarith [norm_nonneg a]
    have hτbd : ∀ b : B, ‖τlin b‖ ≤ (‖npCLM τ‖ + ε) * ‖b‖ := by
      intro b
      have h1 : ‖(τ b : ℂ)‖ ≤ ‖npCLM τ‖ * ‖b‖ := (npCLM τ).le_opNorm b
      have h2 := hτdiff b
      have h3 : ‖τlin b‖ ≤ ‖(τ b : ℂ)‖ + ‖(τ b : ℂ) - τlin b‖ := by
        have := norm_sub_le (τ b : ℂ) ((τ b : ℂ) - τlin b)
        simpa using this
      nlinarith [norm_nonneg b]
    set σ' : A →L[ℂ] ℂ := σlin.mkContinuous (‖npCLM σ‖ + ε) hσbd with hσ'def
    set τ' : B →L[ℂ] ℂ := τlin.mkContinuous (‖npCLM τ‖ + ε) hτbd with hτ'def
    have hσ'app : ∀ a : A, (σ' a : ℂ) = σlin a := fun _ => rfl
    have hτ'app : ∀ b : B, (τ' b : ℂ) = τlin b := fun _ => rfl
    have hσ'c : @Continuous A ℂ (ultraweak A) _ ⇑σ' := by
      letI : TopologicalSpace A := ultraweak A
      have he : ⇑σ' = fun a : A => ∑ k, ((ω k) (star (s k) * a * s k) : ℂ) :=
        funext (fun a => (hσ'app a).trans (hσlinapp a))
      rw [he]
      exact continuous_finsetSum _ fun k _ =>
        (continuous_ultraweak_npFunctional (ω k)).comp
          (((mult_uws_cont (s k)).2.1).comp (mult_uws_cont (star (s k))).1)
    have hτ'c : @Continuous B ℂ (ultraweak B) _ ⇑τ' := by
      letI : TopologicalSpace B := ultraweak B
      have he : ⇑τ' = fun b : B => ∑ l, ((θ l) (star (r l) * b * r l) : ℂ) :=
        funext (fun b => (hτ'app b).trans (hτlinapp b))
      rw [he]
      exact continuous_finsetSum _ fun l _ =>
        (continuous_ultraweak_npFunctional (θ l)).comp
          (((mult_uws_cont (r l)).2.1).comp (mult_uws_cont (star (r l))).1)
    -- the corresponding functional on `𝒜 ⊗ ℬ`
    set χ : Fin n → Fin m → NPFunctional (VNT A B) :=
      fun k l => prodNP (vnTensor A B).isTensorProduct (ω k) (θ l) with hχdef
    set v : Fin n → Fin m → VNT A B := fun k l => (s k) ⊗ᵥ (r l) with hvdef
    set G : VNT A B →L[ℂ] ℂ :=
      ∑ p : Fin n × Fin m, npCLM (conjNP (v p.1 p.2) (χ p.1 p.2)) with hGdef
    have hGapp : ∀ x : VNT A B, (G x : ℂ)
        = ∑ p : Fin n × Fin m, (χ p.1 p.2) (star (v p.1 p.2) * x * v p.1 p.2) := by
      intro x
      rw [hGdef]
      simp [ContinuousLinearMap.sum_apply]
    have hGc : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _ ⇑G := by
      letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
      have he : ⇑G = fun x : VNT A B =>
          ∑ p : Fin n × Fin m, ((χ p.1 p.2) (star (v p.1 p.2) * x * v p.1 p.2) : ℂ) :=
        funext hGapp
      rw [he]
      exact continuous_finsetSum _ fun p _ =>
        (continuous_ultraweak_npFunctional (χ p.1 p.2)).comp
          (((mult_uws_cont (v p.1 p.2)).2.1).comp
            (mult_uws_cont (star (v p.1 p.2))).1)
    have hmiu := (vnTensor A B).isTensorProduct.miu
    have hmulv : ∀ (x x' : A) (y y' : B),
        (x ⊗ᵥ y) * (x' ⊗ᵥ y') = (x * x') ⊗ᵥ (y * y') :=
      fun x x' y y' => (hmiu.2.1 x x' y y').symm
    have hstarv : ∀ (x : A) (y : B), star (x ⊗ᵥ y) = star x ⊗ᵥ star y :=
      fun x y => hmiu.2.2 x y
    have hGval : ∀ (a : A) (b : B), (G (a ⊗ᵥ b) : ℂ) = (σ' a : ℂ) * τ' b := by
      intro a b
      rw [hGapp, hσ'app, hτ'app, hσlinapp, hτlinapp, Finset.sum_mul_sum,
        ← Finset.sum_product']
      refine Finset.sum_congr rfl fun p _ => ?_
      have hconj : star (v p.1 p.2) * (a ⊗ᵥ b) * v p.1 p.2
          = (star (s p.1) * a * s p.1) ⊗ᵥ (star (r p.2) * b * r p.2) := by
        rw [hvdef, hstarv, hmulv, hmulv]
      rw [hconj, hχdef]
      exact prodNP_apply (vnTensor A B).isTensorProduct (ω p.1) (θ p.2) _ _
    have hGt : (G t : ℂ) = 0 := by
      rw [hGapp]
      refine Finset.sum_eq_zero fun p _ => ?_
      refine hkill (χ p.1 p.2) ⟨ω p.1, (hωs p.1).1, θ p.2, (hθr p.2).1, fun a b => ?_⟩
        (v p.1 p.2)
      exact prodNP_apply (vnTensor A B).isTensorProduct (ω p.1) (θ p.2) a b
    -- the cross-norm estimate
    have hnσ : ‖npCLM σ - σ'‖ ≤ ε :=
      ContinuousLinearMap.opNorm_le_bound _ hε.le (fun a => by
        simpa [hσ'app] using hσdiff a)
    have hnτ : ‖npCLM τ - τ'‖ ≤ ε :=
      ContinuousLinearMap.opNorm_le_bound _ hε.le (fun b => by
        simpa [hτ'app] using hτdiff b)
    have hnσ' : ‖σ'‖ ≤ ‖npCLM σ‖ + ε :=
      LinearMap.mkContinuous_norm_le _ (by positivity) _
    have hmain := norm_sub_le_of_tmul_factor (npCLM h) G hhc hGc (npCLM σ) σ'
      (npCLM τ) τ' (continuous_ultraweak_npFunctional σ) hσ'c
      (continuous_ultraweak_npFunctional τ) hτ'c (fun a b => hvalv a b) hGval
    have hht : ‖(h t : ℂ)‖ ≤ ‖npCLM h - G‖ * ‖t‖ := by
      have h0 : ((npCLM h - G) t : ℂ) = (h t : ℂ) := by
        rw [ContinuousLinearMap.sub_apply, hGt, sub_zero]; rfl
      have := (npCLM h - G).le_opNorm t
      rwa [h0] at this
    have hfin : ‖npCLM h - G‖ ≤ ε * (‖npCLM σ‖ + ‖npCLM τ‖ + 1) := by
      refine hmain.trans ?_
      have h1 : ‖npCLM σ - σ'‖ * ‖npCLM τ‖ ≤ ε * ‖npCLM τ‖ :=
        mul_le_mul_of_nonneg_right hnσ (norm_nonneg _)
      have h2 : ‖σ'‖ * ‖npCLM τ - τ'‖ ≤ (‖npCLM σ‖ + ε) * ε := by
        refine mul_le_mul hnσ' hnτ (norm_nonneg _) (by positivity)
      nlinarith [norm_nonneg (npCLM σ), norm_nonneg (npCLM τ), hε.le]
    calc ‖(h t : ℂ)‖ ≤ ‖npCLM h - G‖ * ‖t‖ := hht
      _ ≤ ε * (‖npCLM σ‖ + ‖npCLM τ‖ + 1) * ‖t‖ :=
          mul_le_mul_of_nonneg_right hfin (norm_nonneg t)
  -- let `ε → 0`
  have hzero : ∀ δ : ℝ, 0 < δ → ‖(h t : ℂ)‖ ≤ δ := by
    intro δ hδ
    set C : ℝ := ‖npCLM σ‖ + ‖npCLM τ‖ + 1 with hCdef
    have hC : (0 : ℝ) < C := by
      rw [hCdef]; positivity
    have hden : (0 : ℝ) < C * (‖t‖ + 1) := by positivity
    set ε : ℝ := min 1 (δ / (C * (‖t‖ + 1))) with hεdef
    have hε : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hε2 : ε ≤ δ / (C * (‖t‖ + 1)) := min_le_right _ _
    have h1 := hbound ε hε hε1
    have h2 : ε * C * ‖t‖ ≤ δ := by
      have h3 : ε * (C * (‖t‖ + 1)) ≤ δ := by
        rw [le_div_iff₀ hden] at hε2; linarith
      nlinarith [norm_nonneg t, hε.le, hC.le]
    linarith
  have hnorm0 : ‖(h t : ℂ)‖ = 0 :=
    le_antisymm (le_of_forall_pos_le_add (fun δ hδ => by
      simpa using hzero δ hδ)) (norm_nonneg _)
  exact norm_eq_zero.mp hnorm0

end Chosen

/-! ### Infrastructure for **116VII** `tensor_characterization`

The hard half of 116VII (proc.tex:3600) has to work with a `γ` that is *not
yet known* to be a tensor product, so `prodNP_lift`, `conjProdNP_lift`,
`isBasicFunctional_comp_lift` and `dense_ultrastrong_tensorSpan` — all of
which take an `IsTensorProduct` — are unavailable.  The four lemmas below are
their `IsTensorProduct`-free twins, stated for an miu-bilinear `γ` together
with an np-functional `h` implementing a product `σ ⊙ τ`. -/

section Characterization

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]
variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [VonNeumannAlgebra T]

/-- `h ∘ γ_⊙ = σ ⊙ τ` for *any* np-functional `h` implementing the product of
`σ` and `τ` (`prodNP_lift` without `IsTensorProduct`). -/
private theorem prodLike_lift (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) {σ : NPFunctional A}
    {τ : NPFunctional B} {h : NPFunctional T}
    (hh : ∀ (a : A) (b : B), (h (γ a b) : ℂ) = σ a * τ b) (s : A ⊗[ℂ] B) :
    (h (TensorProduct.lift γ s) : ℂ) = odotF (npLin σ) (npLin τ) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [TensorProduct.lift.tmul, hh a b, odotF, npLin,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply']
      rfl
  | add u v hu hv => rw [map_add, npFunctional_add, hu, hv, map_add]

/-- `h(γ_⊙(v)*(·)γ_⊙(v))` restricted along `γ_⊙` is `(σ ⊙ τ)(v*(·)v)`
(`conjProdNP_lift` without `IsTensorProduct`). -/
private theorem conjLike_lift (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hmiu : MIUBilinear γ)
    {σ : NPFunctional A} {τ : NPFunctional B} {h : NPFunctional T}
    (hh : ∀ (a : A) (b : B), (h (γ a b) : ℂ) = σ a * τ b) (v s : A ⊗[ℂ] B) :
    (conjNP (TensorProduct.lift γ v) h (TensorProduct.lift γ s) : ℂ)
      = odotF (npLin σ) (npLin τ) (star v * s * v) := by
  rw [conjNP_apply, ← lift_star γ hmiu.2.2, ← lift_mul γ hmiu.2.1,
    ← lift_mul γ hmiu.2.1, prodLike_lift γ hh]

/-- Hence that restriction is a *basic* functional
(`isBasicFunctional_comp_lift` without `IsTensorProduct`). -/
private theorem conjLike_basic (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hmiu : MIUBilinear γ)
    {σ : NPFunctional A} {τ : NPFunctional B} {h : NPFunctional T}
    (hh : ∀ (a : A) (b : B), (h (γ a b) : ℂ) = σ a * τ b) (v : A ⊗[ℂ] B) :
    IsBasicFunctional
      ((npLin (conjNP (TensorProduct.lift γ v) h)).comp
        (TensorProduct.lift γ)) :=
  ⟨σ, τ, v, fun s => conjLike_lift γ hmiu hh v s⟩

/-- `γ_⊙(𝒜 ⊙ ℬ)` is *ultrastrongly* dense as soon as it is ultraweakly dense
(`dense_ultrastrong_tensorSpan` without `IsTensorProduct`). -/
private theorem usDense_range_lift (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hmiu : MIUBilinear γ)
    (hdense : @Dense T (ultraweak T)
      (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T)) :
    @Dense T (ultrastrong T) (Set.range ⇑(TensorProduct.lift γ)) := by
  have hd : @Dense T (ultraweak T)
      ((tensorSpan γ hmiu : StarSubalgebra ℂ T) : Set T) := by
    rw [coe_tensorSpan]; exact hdense
  rw [range_lift_eq_span]
  intro x
  refine (mem_usClosure_iff _ x).mpr ?_
  intro ω ε hε
  obtain ⟨ι, l, hl, s, hs, hlim⟩ :=
    dense_subalgebra (tensorSpan γ hmiu) hd 1 one_pos x
  have _ : l.NeBot := hl
  have ht := (usTendsto_iff s l x).mp hlim ω
  obtain ⟨i, hi⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨s i, (hs i).1, hi⟩

/-- **116VII**, first step (proc.tex:3608): under the hypotheses of the
characterisation `γ_⊙` is bounded for the tensor product norm, with constant
`1`.  The thesis renormalises the order separating collection to its unital
members and quotes **21VII**; we run the estimate directly, exactly as
`tensor_basic_2` does, with **90II**.1 supplying order separation. -/
private theorem char_bounded (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hmiu : MIUBilinear γ)
    (Ω : Set (NPFunctional T)) (hΩ : CentreSeparatingConj T Ω)
    (hΩval : ∀ h ∈ Ω, ∃ (σ : NPFunctional A) (τ : NPFunctional B),
      ∀ (a : A) (b : B), (h (γ a b) : ℂ) = σ a * τ b)
    (hdense : @Dense T (ultraweak T)
      (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T))
    (t : A ⊗[ℂ] B) : ‖TensorProduct.lift γ t‖ ≤ tensorNorm A B t := by
  classical
  have hsmulω : ∀ (χ : NPFunctional T) (r : ℝ) (x : T),
      (χ (((r : ℝ) : ℂ) • x) : ℂ) = ((r : ℝ) : ℂ) * χ x := by
    intro χ r x
    show npLin χ (((r : ℝ) : ℂ) • x) = _
    rw [map_smul]; rfl
  set y : T := TensorProduct.lift γ t with hydef
  have hstarmul : star y * y = TensorProduct.lift γ (star t * t) := by
    rw [hydef, lift_mul γ hmiu.2.1, lift_star γ hmiu.2.2]
  have hxnn : (0 : T) ≤ star y * y := star_mul_self_nonneg y
  have hnx : ‖star y * y‖ = ‖y‖ ^ 2 := by
    rw [CStarRing.norm_star_mul_self]; ring
  have hone : TensorProduct.lift γ (1 : A ⊗[ℂ] B) = 1 := lift_one γ hmiu.1
  set N : ℝ := tensorNorm A B t ^ 2 with hNdef
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; positivity
  have hsa1 : IsSelfAdjoint (((N : ℝ) : ℂ) • (1 : T)) := by
    show star _ = _
    simp
  have hle : star y * y ≤ ((N : ℝ) : ℂ) • (1 : T) := by
    refine vn_center_separating_fundamental_1 Ω hΩ
      (Set.range ⇑(TensorProduct.lift γ)) (usDense_range_lift γ hmiu hdense)
      _ _ (IsSelfAdjoint.star_mul_self y) hsa1 ?_
    rintro ω hω _ ⟨v, rfl⟩
    obtain ⟨σ, τ, hστ⟩ := hΩval ω hω
    set ω' : A ⊗[ℂ] B →ₗ[ℂ] ℂ :=
      (npLin (conjNP (TensorProduct.lift γ v) ω)).comp (TensorProduct.lift γ)
      with hω'def
    have hbasic : IsBasicFunctional ω' := conjLike_basic γ hmiu hστ v
    have hL : (ω (star (TensorProduct.lift γ v) * (star y * y) *
        TensorProduct.lift γ v) : ℂ) = ω' (star t * t) := by
      rw [hstarmul]; rfl
    have hR : (ω (star (TensorProduct.lift γ v) * (((N : ℝ) : ℂ) • (1 : T)) *
        TensorProduct.lift γ v) : ℂ) = ((N : ℝ) : ℂ) * ω' 1 := by
      have he : star (TensorProduct.lift γ v) * (((N : ℝ) : ℂ) • (1 : T)) *
            TensorProduct.lift γ v
          = ((N : ℝ) : ℂ) • (star (TensorProduct.lift γ v) *
              TensorProduct.lift γ (1 : A ⊗[ℂ] B) * TensorProduct.lift γ v) := by
        rw [hone, mul_smul_comm, smul_mul_assoc]
      rw [he, hsmulω]
      rfl
    rw [hL, hR]
    have hbs := basic_star_self_le hbasic t
    have hpos1 : (0 : ℂ) ≤ ω' 1 := basic_one_nonneg hbasic
    have hposX : (0 : ℂ) ≤ ω' (star t * t) :=
      (basic_state_inner_product ω' hbasic).2 t
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [Complex.re_ofReal_mul]; exact hbs
    · have h1 : (ω' (star t * t)).im = 0 := by
        simpa using ((Complex.le_def.mp hposX).2).symm
      have h2 : (ω' 1).im = 0 := by
        simpa using ((Complex.le_def.mp hpos1).2).symm
      simp [Complex.mul_im, h1, h2]
  have hnorm : ‖star y * y‖ ≤ N := by
    refine (Theses.A.CStar.norm_le_iff_neg_algebraMap_le
      (IsSelfAdjoint.star_mul_self y) hN0).mpr ⟨?_, ?_⟩
    · refine le_trans (neg_nonpos.mpr ?_) hxnn
      exact Theses.A.CStar.algebraMap_ofReal_nonneg hN0
    · rwa [Algebra.algebraMap_eq_smul_one]
  rw [hnx, hNdef] at hnorm
  nlinarith [norm_nonneg y, tensorNorm_nonneg (A := A) (B := B) t]

/-- **116VII**, second step (proc.tex:3630): `γ_⊙` is continuous from the
ultraweak tensor product topology to the ultraweak topology on `𝒯`.  Every
np-functional on `𝒯` is, by **90II**.2, an operator-norm limit of finite sums
of `h(γ_⊙(v)*(·)γ_⊙(v))` with `h ∈ Ω`; restricted along `γ_⊙` those are the
basic functionals, and `char_bounded` converts `ε‖γ_⊙ u‖` into `ε‖u‖`. -/
private theorem char_normal (γ : A →ₗ[ℂ] B →ₗ[ℂ] T) (hmiu : MIUBilinear γ)
    (Ω : Set (NPFunctional T)) (hΩ : CentreSeparatingConj T Ω)
    (hΩval : ∀ h ∈ Ω, ∃ (σ : NPFunctional A) (τ : NPFunctional B),
      ∀ (a : A) (b : B), (h (γ a b) : ℂ) = σ a * τ b)
    (hdense : @Dense T (ultraweak T)
      (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T)) :
    BilinNormal γ := by
  classical
  have hbdd := char_bounded γ hmiu Ω hΩ hΩval hdense
  have hnl : ∀ h : NPFunctional T,
      NormLimitOfSimple A B ((npLin h).comp (TensorProduct.lift γ)) := by
    intro h ε hε
    obtain ⟨n, ω, s, hmem, hb⟩ :=
      vn_center_separating_fundamental_2 Ω hΩ
        (Set.range ⇑(TensorProduct.lift γ))
        (usDense_range_lift γ hmiu hdense) h ε hε
    choose v hv using fun k => (hmem k).2
    refine ⟨∑ k, (npLin (conjNP (s k) (ω k))).comp (TensorProduct.lift γ),
      ⟨n, fun k => (npLin (conjNP (s k) (ω k))).comp (TensorProduct.lift γ),
        fun k => ?_, rfl⟩, fun u => ?_⟩
    · obtain ⟨σ, τ, hστ⟩ := hΩval (ω k) (hmem k).1
      show IsBasicFunctional
        ((npLin (conjNP (s k) (ω k))).comp (TensorProduct.lift γ))
      rw [← hv k]
      exact conjLike_basic γ hmiu hστ (v k)
    · have hbt := hb (TensorProduct.lift γ u)
      have hstep : ε * ‖TensorProduct.lift γ u‖ ≤ ε * tensorNorm A B u :=
        mul_le_mul_of_nonneg_left (hbdd u) hε.le
      refine le_trans (le_trans (le_of_eq ?_) hbt) hstep
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply]
      rfl
  show @Continuous _ _ (uwTensorTopology A B) (ultraweak T)
    ⇑(TensorProduct.lift γ)
  rw [continuous_iff_le_induced]
  show uwTensorTopology A B ≤ TopologicalSpace.induced ⇑(TensorProduct.lift γ)
    (⨅ ω : NPFunctional T,
      TopologicalSpace.induced (fun x : T => (ω x : ℂ)) inferInstance)
  rw [induced_iInf]
  refine le_iInf fun ω => ?_
  rw [induced_compose]
  exact iInf_le _ (⟨(npLin ω).comp (TensorProduct.lift γ), hnl ω⟩ :
    {f : A ⊗[ℂ] B →ₗ[ℂ] ℂ // NormLimitOfSimple A B f})

/-- The inverse of a bijective nmiu-map, as an nmiu-map. -/
private noncomputable def nmiuInv {X Y : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
    [VonNeumannAlgebra Y] (φ : NMIUMap X Y) (hφ : Function.Bijective ⇑φ) :
    NMIUMap Y X where
  toStarAlgHom := (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).symm
  preservesDirSups' :=
    starAlgEquiv_preservesDirSups' (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).symm

private theorem nmiuInv_apply' {X Y : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
    [VonNeumannAlgebra Y] (φ : NMIUMap X Y) (hφ : Function.Bijective ⇑φ)
    (y : Y) : (φ (nmiuInv φ hφ y) : Y) = y :=
  (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).apply_symm_apply y

private theorem nmiuInv_apply {X Y : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [VonNeumannAlgebra X]
    [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]
    [VonNeumannAlgebra Y] (φ : NMIUMap X Y) (hφ : Function.Bijective ⇑φ)
    (x : X) : nmiuInv φ hφ (φ x) = x :=
  (StarAlgEquiv.ofBijective φ.toStarAlgHom hφ).symm_apply_apply x

end Characterization

/-- **116VII** (`tensor-characterization`, proc.tex:3578, Theorem): given
centre separating collections `Σ`, `Γ` of np-functionals on `𝒜`, `ℬ`, an
miu-bilinear map `γ : 𝒜 × ℬ → 𝒯` is a tensor product iff (1) the span of
its range is ultraweakly dense, (2) for `σ ∈ Σ`, `τ ∈ Γ` the product
functional exists and is positive, and (3) those product functionals are
centre separating. -/
theorem tensor_characterization [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
    [VonNeumannAlgebra T] (Sg : Set (NPFunctional A))
    (Γ : Set (NPFunctional B)) (hSg : CentreSeparatingConj A Sg)
    (hΓ : CentreSeparatingConj B Γ) (γ : A →ₗ[ℂ] B →ₗ[ℂ] T)
    (hmiu : MIUBilinear γ) :
    IsTensorProduct γ ↔
      (@Dense T (ultraweak T)
          (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T)) ∧
        (∀ σ ∈ Sg, ∀ τ ∈ Γ, ∃ h : NPFunctional T,
          ∀ (a : A) (b : B), h (γ a b) = σ a * τ b) ∧
        CentreSeparatingConj T
          {h : NPFunctional T | ∃ σ ∈ Sg, ∃ τ ∈ Γ,
            ∀ (a : A) (b : B), h (γ a b) = σ a * τ b} := by
  -- proc.tex:3600.  The "only if" half is 108II plus **116IV**.2 transported
  -- along the nmiu-isomorphism of **114II**; the "if" half is the theorem's
  -- content: `char_bounded` and `char_normal` make `γ_⊙` bounded and normal,
  -- **112XI** + **114I** turn that into an nmiu-map `γ_⊗ : 𝒜 ⊗ ℬ → 𝒯` out of
  -- the *chosen* tensor product, and `γ_⊗` is then shown bijective.
  -- *Divergence.*  For injectivity the thesis computes the carrier `⌈γ_⊗⌉`
  -- and uses **69IV** `carrier_miu`; we use the centre separating collection
  -- of 116IV.2 directly on `γ_⊗(x)* γ_⊗(x) = γ_⊗(x* x)`, which is the same
  -- argument with the carrier bookkeeping removed.
  classical
  set γv : A →ₗ[ℂ] B →ₗ[ℂ] VNT A B := (vnTensor A B).map with hγvdef
  have hγv : IsTensorProduct γv := (vnTensor A B).isTensorProduct
  constructor
  · -- **only if**: conditions (1) and (2) are 108II verbatim; (3) is 116IV.2
    -- transported along `φ : 𝒜 ⊗ ℬ ≅ 𝒯`.
    intro hγ
    refine ⟨hγ.dense, fun σ _ τ _ => hγ.prod_exists σ τ, ?_⟩
    obtain ⟨φ, hφe, hφbij, -⟩ := tensor_uniqueness γv γ hγv hγ
    have hψφ : ∀ x : VNT A B, nmiuInv φ hφbij (φ x) = x :=
      fun x => nmiuInv_apply φ hφbij x
    have hφ0 : (φ (0 : VNT A B) : T) = 0 := map_zero φ.toStarAlgHom
    rw [centreSeparatingConj_iff]
    intro a ha
    refine ⟨fun hz χ _ b => by rw [hz]; simp, fun hkill => ?_⟩
    obtain ⟨x, rfl⟩ := hφbij.2 a
    have hx : (0 : VNT A B) ≤ x := by
      have hle := injective_nmiu_iso_on_image_2 φ hφbij.1 0 x
      rw [hφ0] at hle
      exact hle.mp ha
    have hzero : x = 0 := by
      refine ((centreSeparatingConj_iff _).mp
        (tensor_generation_2 Sg Γ hSg hΓ) x hx).mpr ?_
      rintro χ ⟨ω, hω, θ, hθ, hval⟩ c
      have hk := hkill
        (compNP (nmiuP (nmiuInv φ hφbij)) (nmiuInv φ hφbij).preservesDirSups' χ)
        ⟨ω, hω, θ, hθ, fun a b => by
          show (χ (nmiuInv φ hφbij (γ a b)) : ℂ) = _
          rw [← hφe a b, hψφ]
          exact hval a b⟩ (φ c)
      have hmulφ : ∀ p q : VNT A B, (φ (p * q) : T) = φ p * φ q :=
        fun p q => map_mul φ.toStarAlgHom p q
      have hstarφ : ∀ p : VNT A B, (φ (star p) : T) = star (φ p) :=
        fun p => map_star φ.toStarAlgHom p
      have he : nmiuInv φ hφbij (star (φ c) * φ x * φ c) = star c * x * c := by
        rw [← hstarφ, ← hmulφ, ← hmulφ, hψφ]
      have hk' : (χ (nmiuInv φ hφbij (star (φ c) * φ x * φ c)) : ℂ) = 0 := hk
      rwa [he] at hk'
    rw [hzero, hφ0]
  · -- **if**: the theorem's content.
    rintro ⟨hdense, hprod, hcs⟩
    have hΩval : ∀ h ∈ {h : NPFunctional T | ∃ σ ∈ Sg, ∃ τ ∈ Γ,
        ∀ (a : A) (b : B), h (γ a b) = σ a * τ b},
        ∃ (σ : NPFunctional A) (τ : NPFunctional B),
          ∀ (a : A) (b : B), (h (γ a b) : ℂ) = σ a * τ b := by
      rintro h ⟨σ, -, τ, -, hval⟩
      exact ⟨σ, τ, hval⟩
    have hbn : BilinNormal γ := char_normal γ hmiu _ hcs hΩval hdense
    have hbb : BilinBounded γ := ⟨1, zero_le_one, fun t => by
      rw [one_mul]; exact char_bounded γ hmiu _ hcs hΩval hdense t⟩
    obtain ⟨⟨g, ⟨hgc, hge⟩, -⟩, -⟩ := tensor_universal_property γv hγv γ hbn hbb
    obtain ⟨hm, hs, hu, -, -⟩ :=
      tensor_universal_property_extra γv hγv γ hbn hbb g hgc hge
    have hmult := hm.mpr hmiu.2.1
    have hstar := hs.mpr hmiu.2.2
    have hunit := hu.mpr hmiu.1
    set Φ : VNT A B →⋆ₐ[ℂ] T :=
      { toFun := ⇑g
        map_one' := hunit
        map_mul' := hmult
        map_zero' := map_zero g
        map_add' := map_add g
        commutes' := fun r => by
          show g (algebraMap ℂ (VNT A B) r) = algebraMap ℂ T r
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
            map_smul, hunit]
        map_star' := hstar } with hΦdef
    have hΦapp : ∀ z : VNT A B, (Φ z : T) = g z := fun _ => rfl
    have hΦc : @Continuous (VNT A B) T (ultraweak (VNT A B)) (ultraweak T)
        ⇑(starAlgHomP Φ) := hgc
    have hΦnormal : PreservesDirSups ⇑(starAlgHomP Φ) :=
      ((p_uwcont (starAlgHomP Φ)).out 0 2).mp hΦc
    set Φn : NMIUMap (VNT A B) T :=
      { toStarAlgHom := Φ, preservesDirSups' := hΦnormal } with hΦndef
    -- **injectivity**: `γ_⊗(x)* γ_⊗(x) = γ_⊗(x* x)` is killed by the centre
    -- separating collection of 116IV.2.
    have hinj : Function.Injective ⇑Φ := by
      have hker : ∀ x : VNT A B, (Φ x : T) = 0 → x = 0 := by
        intro x hx
        have hpos : (0 : VNT A B) ≤ star x * x := star_mul_self_nonneg x
        have hzero : star x * x = 0 := by
          refine ((centreSeparatingConj_iff _).mp
            (tensor_generation_2 Sg Γ hSg hΓ) _ hpos).mpr ?_
          rintro χ ⟨ω, hω, θ, hθ, hval⟩ c
          obtain ⟨h, hh⟩ := hprod ω hω θ hθ
          have hcont : @Continuous (VNT A B) ℂ (ultraweak (VNT A B)) _
              ⇑((npLin h).comp g) := by
            letI : TopologicalSpace (VNT A B) := ultraweak (VNT A B)
            letI : TopologicalSpace T := ultraweak T
            exact (continuous_ultraweak_npFunctional h).comp hgc
          have huniq := prod_functional_unique γv hγv (npLin ω) (npLin θ)
            (npLin (prodNP hγv ω θ)) ((npLin h).comp g)
            (continuous_ultraweak_npFunctional _) hcont
            (prodNP_apply hγv ω θ) (fun a b => by
              show (h (g (γv a b)) : ℂ) = _
              rw [hge a b]; exact hh a b)
          have hgz : (Φ (star c * (star x * x) * c) : T) = 0 := by
            simp [map_mul, map_star, hx]
          have hval' : (χ (star c * (star x * x) * c) : ℂ)
              = prodNP hγv ω θ (star c * (star x * x) * c) :=
            eq_prodNP hγv ω θ χ hval _
          rw [hval']
          have := congrArg (fun f : (VNT A B) →ₗ[ℂ] ℂ =>
            f (star c * (star x * x) * c)) huniq
          simp only [LinearMap.comp_apply] at this
          rw [show (npLin (prodNP hγv ω θ)) (star c * (star x * x) * c)
              = (prodNP hγv ω θ (star c * (star x * x) * c) : ℂ) from rfl] at this
          rw [this, ← hΦapp, hgz]
          simp
        have hnn : ‖x‖ * ‖x‖ = 0 := by
          rw [← CStarRing.norm_star_mul_self, hzero, norm_zero]
        have hx0 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
        exact norm_eq_zero.mp hx0
      intro x y hxy
      have hd : (Φ (x - y) : T) = 0 := by rw [map_sub, hxy, sub_self]
      exact sub_eq_zero.mp (hker _ hd)
    -- **surjectivity**: the range is a von Neumann subalgebra (**48VI**.1),
    -- hence ultraweakly closed (**73IX** `vnsac`), and it contains the
    -- ultraweakly dense span of the range of `γ`.
    have hsurj : Function.Surjective ⇑Φ := by
      have hR : IsVNSubalgebra T Φn.toStarAlgHom.range :=
        injective_nmiu_iso_on_image_1 Φn hinj
      have hclosed : @IsClosed T (ultraweak T)
          ((Φn.toStarAlgHom.range : StarSubalgebra ℂ T) : Set T) :=
        (vnsac _ hR).2
      letI : TopologicalSpace T := ultraweak T
      intro x
      have hsub : (Submodule.span ℂ {t : T | ∃ a b, t = γ a b} : Set T)
          ⊆ ((Φn.toStarAlgHom.range : StarSubalgebra ℂ T) : Set T) := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem u hu =>
            obtain ⟨a, b, rfl⟩ := hu
            exact ⟨a ⊗ᵥ b, hge a b⟩
        | zero => exact zero_mem _
        | add u v _ _ hu hv => exact add_mem hu hv
        | smul c u _ hu => exact SMulMemClass.smul_mem c hu
      exact hclosed.closure_subset_iff.mpr hsub (hdense x)
    have hbij : Function.Bijective ⇑Φn := ⟨hinj, hsurj⟩
    have hψΦ : ∀ z : VNT A B, nmiuInv Φn hbij (Φn z) = z :=
      fun z => nmiuInv_apply Φn hbij z
    have hΦψ : ∀ y : T, (Φn (nmiuInv Φn hbij y) : T) = y :=
      nmiuInv_apply' Φn hbij
    have hψγ : ∀ (a : A) (b : B), nmiuInv Φn hbij (γ a b) = γv a b := by
      intro a b
      have hv : (Φn (γv a b) : T) = γ a b := hge a b
      rw [← hv, hψΦ]
    have hprodfun : ∀ (σ : NPFunctional A) (τ : NPFunctional B) (a : A) (b : B),
        (compNP (nmiuP (nmiuInv Φn hbij)) (nmiuInv Φn hbij).preservesDirSups'
          (prodNP hγv σ τ) (γ a b) : ℂ) = σ a * τ b := by
      intro σ τ a b
      show (prodNP hγv σ τ (nmiuInv Φn hbij (γ a b)) : ℂ) = _
      rw [hψγ a b]
      exact prodNP_apply hγv σ τ a b
    refine ⟨hmiu, hdense, fun σ τ => ⟨_, hprodfun σ τ⟩, fun t ht hkill => ?_⟩
    have hx : (0 : VNT A B) ≤ nmiuInv Φn hbij t :=
      starAlgHom_nonneg' (nmiuInv Φn hbij).toStarAlgHom ht
    have hz : nmiuInv Φn hbij t = 0 := by
      refine hγv.faithful _ hx (fun σ τ h hh => ?_)
      have hk := hkill σ τ _ (hprodfun σ τ)
      rw [eq_prodNP hγv σ τ h hh]
      exact hk
    have := hΦψ t
    rw [hz] at this
    rw [← this]
    exact map_zero Φn.toStarAlgHom

/-! ## The coprojections `κᵢ : 𝒜ᵢ → ⊕ⱼ 𝒜ⱼ`

Infrastructure for **117II** below and for **122IV**
(`nmiu-functional-product`) in `QuantumLambda.lean`, where these lemmas were
first proved; 117II.1 needs them, so they were lifted here (that file imports
this one). -/

section Coprojections

variable {I : Type*} {𝒜 : I → Type*} [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)]

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

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_add (i : I) (a b : 𝒜 i) :
    lpKappa i (a + b) = lpKappa i a + lpKappa i b :=
  lp.single_add _ _ _ _

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_zero (i : I) : lpKappa i (0 : 𝒜 i) = 0 :=
  lp.single_zero _ _

omit [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_smul (i : I) (c : ℂ) (a : 𝒜 i) :
    lpKappa i (c • a) = c • lpKappa i a :=
  lp.single_smul _ _ _ _

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
theorem lpKappa_sub (i : I) (a b : 𝒜 i) :
    lpKappa i (a - b) = lpKappa i a - lpKappa i b :=
  lp.single_sub _ _ _ _

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
/-- `κᵢ` is `lp.single` for *any* decidability instance on `I` (the definition
above uses the classical one). -/
theorem lpKappa_eq_single [DecidableEq I] (i : I) (a : 𝒜 i) :
    lpKappa i a = lp.single ∞ i a := by
  apply lp.ext
  funext j
  simp only [lpKappa, lp.coeFn_single]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
/-- `κᵢ` is isometric, hence continuous. -/
theorem lpKappa_continuous (i : I) : Continuous (fun a : 𝒜 i => lpKappa i a) := by
  refine (Isometry.of_dist_eq (fun a b => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, ← lpKappa_sub]
  simp only [lpKappa]
  exact lp.norm_single (by simp) i (a - b)

omit [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
/-- The finite restriction `∑_{j ∈ F} κⱼ(xⱼ)` of `x` has coordinates `xₖ` for
`k ∈ F` and `0` outside `F`. -/
theorem lpKappa_sum_apply (x : lp 𝒜 ∞) (F : Finset I) (k : I) :
    ((∑ j ∈ F, lpKappa j ((x : ∀ k, 𝒜 k) j) : lp 𝒜 ∞) : ∀ k, 𝒜 k) k
      = if k ∈ F then (x : ∀ k, 𝒜 k) k else 0 := by
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lpKappa, lp.coeFn_single]
  exact Finset.sum_pi_single _ _ _

end Coprojections

/-! ### Infrastructure for 117II.1

`W*(⋃ᵢ κᵢ(Aᵢ) ∪ {eᵢ})` is reached in three steps: the preimage
`{a | κᵢ(a) ∈ W}` is a von Neumann subalgebra of `𝒜ᵢ` (`kappaPreimage`), so it
is everything; the finite restrictions of a *positive* `x` then form a directed
family with supremum `x`; and a general `x` is a linear combination of positive
elements. -/

section SumGeneration

variable {I : Type*} {𝒜 : I → Type*} [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)]
  {W : StarSubalgebra ℂ (lp 𝒜 ∞)}

open Classical in
/-- The preimage `{a ∈ 𝒜ᵢ | κᵢ(a) ∈ W}` of a ∗-subalgebra `W ∋ eᵢ` of `⊕ⱼ 𝒜ⱼ`.
It is a ∗-subalgebra because `κᵢ` is multiplicative and ∗-preserving, and
*unital* precisely because `eᵢ = κᵢ(1) ∈ W` — the hypothesis the printed form
of 117II.1 lacks. -/
private def kappaPreimage (i : I) (W : StarSubalgebra ℂ (lp 𝒜 ∞))
    (hone : lpKappa i (1 : 𝒜 i) ∈ W) : StarSubalgebra ℂ (𝒜 i) where
  carrier := {a : 𝒜 i | lpKappa i a ∈ W}
  mul_mem' {a b} ha hb := by
    show lpKappa i (a * b) ∈ W
    rw [← lpKappa_mul]; exact mul_mem ha hb
  one_mem' := hone
  add_mem' {a b} ha hb := by
    show lpKappa i (a + b) ∈ W
    rw [lpKappa_add]; exact add_mem ha hb
  zero_mem' := by
    show lpKappa i (0 : 𝒜 i) ∈ W
    rw [lpKappa_zero]; exact zero_mem W
  algebraMap_mem' c := by
    show lpKappa i (algebraMap ℂ (𝒜 i) c) ∈ W
    rw [Algebra.algebraMap_eq_smul_one, lpKappa_smul, Algebra.smul_def]
    exact mul_mem (W.algebraMap_mem c) hone
  star_mem' {a} ha := by
    show lpKappa i (star a) ∈ W
    rw [← lpKappa_star]; exact star_mem ha

open Classical in
/-- `κᵢ` on self-adjoint parts. -/
private def kappaSA (i : I) (d : selfAdjoint (𝒜 i)) : selfAdjoint (lp 𝒜 ∞) :=
  ⟨lpKappa i (d : 𝒜 i), lpKappa_sa' i d.2⟩

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] in
open Classical in
private theorem kappaSA_coe (i : I) (d : selfAdjoint (𝒜 i)) :
    ((kappaSA i d : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞) = lpKappa i (d : 𝒜 i) := rfl

open Classical in
private theorem kappaSA_mono (i : I) {d e : selfAdjoint (𝒜 i)} (h : d ≤ e) :
    kappaSA i d ≤ kappaSA i e :=
  Subtype.coe_le_coe.mp (lpKappa_le i (Subtype.coe_le_coe.mpr h))

open Classical in
/-- `{a | κᵢ(a) ∈ W}` is a von Neumann subalgebra of `𝒜ᵢ` when `W` is one of
`⊕ⱼ 𝒜ⱼ`: it is closed because `κᵢ` is isometric, and closed under directed
suprema because `κᵢ` carries the supremum of `D` to the supremum of `κᵢ(D)`
(the order on `⊕ⱼ 𝒜ⱼ` being pointwise, and `κᵢ(d)ⱼ = 0` for `j ≠ i`). -/
private theorem isVNSubalgebra_kappaPreimage (i : I) (hone : lpKappa i (1 : 𝒜 i) ∈ W)
    (hW : IsVNSubalgebra (lp 𝒜 ∞) W) : IsVNSubalgebra (𝒜 i) (kappaPreimage i W hone) := by
  constructor
  · exact IsClosed.preimage (lpKappa_continuous i) hW.isClosed
  · intro D s hDT hne hdir hlub
    show lpKappa i (s : 𝒜 i) ∈ W
    refine hW.dirSup_mem (kappaSA i '' D) (kappaSA i s) ?_ (hne.image _) ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩; exact hDT d hd
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
      obtain ⟨z, hz, hdz, hez⟩ := hdir d hd e he
      exact ⟨kappaSA i z, ⟨z, hz, rfl⟩, kappaSA_mono i hdz, kappaSA_mono i hez⟩
    · constructor
      · rintro _ ⟨d, hd, rfl⟩
        exact kappaSA_mono i (hlub.1 hd)
      · intro u hu
        rw [← Subtype.coe_le_coe, kappaSA_coe, lp_infty_le_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          rw [lpKappa_apply_self]
          have hub : (⟨(u : lp 𝒜 ∞) j, lp_infty_isSelfAdjoint u.2 j⟩ : selfAdjoint (𝒜 j))
              ∈ upperBounds D := by
            intro d hd
            have h1 : kappaSA j d ≤ u := hu ⟨d, hd, rfl⟩
            have h2 := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr h1) j
            rw [kappaSA_coe, lpKappa_apply_self] at h2
            exact Subtype.coe_le_coe.mp h2
          exact Subtype.coe_le_coe.mpr (hlub.2 hub)
        · rw [lpKappa_apply_ne _ _ hj]
          obtain ⟨d₀, hd₀⟩ := hne
          have h1 : kappaSA i d₀ ≤ u := hu ⟨d₀, hd₀, rfl⟩
          have h2 := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr h1) j
          rw [kappaSA_coe, lpKappa_apply_ne _ _ hj] at h2
          exact h2

open Classical in
private theorem lpRestrict_nonneg (x : lp 𝒜 ∞) (hx : 0 ≤ x) (F : Finset I) :
    0 ≤ ∑ j ∈ F, lpKappa j ((x : ∀ k, 𝒜 k) j) := by
  rw [lp_infty_nonneg_iff]
  intro k
  rw [lpKappa_sum_apply]
  by_cases h : k ∈ F
  · simpa [h] using (lp_infty_nonneg_iff x).mp hx k
  · simp [h]

open Classical in
private theorem lpRestrict_mono (x : lp 𝒜 ∞) (hx : 0 ≤ x) {F G : Finset I} (h : F ⊆ G) :
    (∑ j ∈ F, lpKappa j ((x : ∀ k, 𝒜 k) j)) ≤ ∑ j ∈ G, lpKappa j ((x : ∀ k, 𝒜 k) j) := by
  rw [lp_infty_le_iff]
  intro k
  rw [lpKappa_sum_apply, lpKappa_sum_apply]
  by_cases hF : k ∈ F
  · simp [hF, h hF]
  · by_cases hG : k ∈ G <;> simp [hF, hG, (lp_infty_nonneg_iff x).mp hx k]

open Classical in
private theorem lpRestrict_le (x : lp 𝒜 ∞) (hx : 0 ≤ x) (F : Finset I) :
    (∑ j ∈ F, lpKappa j ((x : ∀ k, 𝒜 k) j)) ≤ x := by
  rw [lp_infty_le_iff]
  intro k
  rw [lpKappa_sum_apply]
  by_cases h : k ∈ F
  · simp [h]
  · simpa [h] using (lp_infty_nonneg_iff x).mp hx k

open Classical in
private def lpRestrictSA (x : lp 𝒜 ∞) (hx : 0 ≤ x) (F : Finset I) : selfAdjoint (lp 𝒜 ∞) :=
  ⟨∑ j ∈ F, lpKappa j ((x : ∀ k, 𝒜 k) j), IsSelfAdjoint.of_nonneg (lpRestrict_nonneg x hx F)⟩

open Classical in
private theorem lpRestrictSA_coe (x : lp 𝒜 ∞) (hx : 0 ≤ x) (F : Finset I) :
    ((lpRestrictSA x hx F : selfAdjoint (lp 𝒜 ∞)) : lp 𝒜 ∞)
      = ∑ j ∈ F, lpKappa j ((x : ∀ k, 𝒜 k) j) := rfl

open Classical in
/-- A *positive* `x` is the directed supremum of its finite restrictions
`∑_{j ∈ F} κⱼ(xⱼ)`, so a von Neumann subalgebra containing every `κᵢ(a)`
contains it. -/
private theorem wstar_mem_of_nonneg (hW : IsVNSubalgebra (lp 𝒜 ∞) W)
    (hkey : ∀ (i : I) (a : 𝒜 i), lpKappa i a ∈ W) (x : lp 𝒜 ∞) (hx : 0 ≤ x) : x ∈ W := by
  refine hW.dirSup_mem (Set.range (lpRestrictSA x hx))
    ⟨x, IsSelfAdjoint.of_nonneg hx⟩ ?_ ⟨_, ⟨∅, rfl⟩⟩ ?_ ?_
  · rintro _ ⟨F, rfl⟩
    rw [lpRestrictSA_coe]
    exact sum_mem fun j _ => hkey j _
  · rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    refine ⟨lpRestrictSA x hx (F ∪ G), ⟨F ∪ G, rfl⟩, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp (lpRestrict_mono x hx Finset.subset_union_left)
    · exact Subtype.coe_le_coe.mp (lpRestrict_mono x hx Finset.subset_union_right)
  · constructor
    · rintro _ ⟨F, rfl⟩
      exact Subtype.coe_le_coe.mp (lpRestrict_le x hx F)
    · intro u hu
      rw [← Subtype.coe_le_coe, lp_infty_le_iff]
      intro k
      have h1 : lpRestrictSA x hx {k} ≤ u := hu ⟨{k}, rfl⟩
      have h2 := (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr h1) k
      rw [lpRestrictSA_coe, lpKappa_sum_apply] at h2
      simpa using h2

open Classical in
/-- `y + ‖y‖·1 ≥ 0` for self-adjoint `y`, so self-adjoint elements follow. -/
private theorem wstar_mem_of_isSelfAdjoint (hW : IsVNSubalgebra (lp 𝒜 ∞) W)
    (hkey : ∀ (i : I) (a : 𝒜 i), lpKappa i a ∈ W) (y : lp 𝒜 ∞) (hy : IsSelfAdjoint y) :
    y ∈ W := by
  have h0 : (0 : lp 𝒜 ∞) ≤ y + algebraMap ℝ (lp 𝒜 ∞) ‖y‖ := by
    have h := sub_nonneg.mpr hy.neg_algebraMap_norm_le_self
    rwa [sub_neg_eq_add] at h
  have hmem : algebraMap ℝ (lp 𝒜 ∞) ‖y‖ ∈ W := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (lp 𝒜 ∞)]
    exact W.algebraMap_mem _
  have hy' : y = (y + algebraMap ℝ (lp 𝒜 ∞) ‖y‖) - algebraMap ℝ (lp 𝒜 ∞) ‖y‖ := by abel
  rw [hy']
  exact sub_mem (wstar_mem_of_nonneg hW hkey _ h0) hmem

open Classical in
/-- `x = ℜx + i·ℑx` reduces the general case to the self-adjoint one. -/
private theorem wstar_mem_all (hW : IsVNSubalgebra (lp 𝒜 ∞) W)
    (hkey : ∀ (i : I) (a : 𝒜 i), lpKappa i a ∈ W) (x : lp 𝒜 ∞) : x ∈ W := by
  rw [← realPart_add_I_smul_imaginaryPart x]
  refine add_mem (wstar_mem_of_isSelfAdjoint hW hkey _ (realPart x).2) ?_
  rw [Algebra.smul_def]
  exact mul_mem (W.algebraMap_mem _)
    (wstar_mem_of_isSelfAdjoint hW hkey _ (imaginaryPart x).2)

end SumGeneration

/-! ## Parsec 1170: distribution over direct sums -/

/-! ### Bridging `W*(S) = 𝒯` and ultraweak density

**117III** uses **117II**.1 `sum_generation_1`, which is phrased with `W*(·)`,
to prove condition (1) of **116VII**, which is phrased with ultraweak density
of a linear span.  These two lemmas connect them; both directions are needed
(the first to feed `sum_generation_1`, the second to read its conclusion). -/

section WstarDense

variable {T : Type u} [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [VonNeumannAlgebra T]

/-- If the linear span of `S` is ultraweakly dense then `W*(S) = 𝒯`: `W*(S)`
is a von Neumann subalgebra, hence ultraweakly closed (**75VIII** `vnsac`),
and it contains the span. -/
theorem wstar_eq_top_of_dense_span (S : Set T)
    (h : @Dense T (ultraweak T) (Submodule.span ℂ S : Set T)) :
    wstar T S = ⊤ := by
  let _ : TopologicalSpace T := ultraweak T
  obtain ⟨hvn, hsub⟩ := isVNSubalgebra_wstar (A := T) S
  have hclosed : @IsClosed T (ultraweak T) ((wstar T S : Set T)) := (vnsac _ hvn).2
  have hspanle : (Submodule.span ℂ S : Set T) ⊆ (wstar T S : Set T) := by
    have hle : Submodule.span ℂ S ≤ Subalgebra.toSubmodule (wstar T S).toSubalgebra :=
      Submodule.span_le.mpr hsub
    exact fun x hx => hle hx
  refine StarSubalgebra.eq_top_iff.mpr fun x => ?_
  have hx : x ∈ @closure T (ultraweak T) (Submodule.span ℂ S : Set T) := by
    rw [h.closure_eq]; trivial
  exact hclosed.closure_subset_iff.mpr hspanle hx

/-- Conversely, if `W*(S) = 𝒯` for a ∗-subalgebra `S` then `S` is ultraweakly
dense: its *ultrastrong* closure is already a von Neumann subalgebra
(**75VII** `usClosureSubalgebra`), hence contains `W*(S)`. -/
theorem dense_of_wstar_eq_top (S : StarSubalgebra ℂ T)
    (h : wstar T (S : Set T) = ⊤) :
    @Dense T (ultraweak T) (S : Set T) := by
  have hle : wstar T (S : Set T) ≤ usClosureSubalgebra S :=
    sInf_le ⟨isVNSubalgebra_usClosureSubalgebra S,
      @subset_closure T (ultrastrong T) (S : Set T)⟩
  rw [h] at hle
  intro x
  have hx : x ∈ usClosureSubalgebra S := hle (by trivial)
  exact usClosure_subset_uwClosure (S : Set T) hx

/-- `W*(·)` is monotone. -/
theorem wstar_mono {S S' : Set T} (h : S ⊆ S') : wstar T S ≤ wstar T S' :=
  sInf_le_sInf fun _ hW => ⟨hW.1, h.trans hW.2⟩

/-- *All* np-functionals form a centre separating collection (they are
faithful, 42I). -/
theorem centreSeparatingConj_univ :
    CentreSeparatingConj T (Set.univ : Set (NPFunctional T)) := by
  rw [centreSeparatingConj_iff]
  intro a ha
  refine ⟨fun h ω _ b => by rw [h]; simp, fun H => ?_⟩
  refine VonNeumannAlgebra.np_faithful a ha fun ω => ?_
  have h := H ω (Set.mem_univ _) 1
  simpa using h

/-- A centre separating collection stays centre separating when enlarged. -/
theorem centreSeparatingConj_mono {Ω Ω' : Set (NPFunctional T)}
    (h : CentreSeparatingConj T Ω) (hsub : Ω ⊆ Ω') :
    CentreSeparatingConj T Ω' := by
  rw [centreSeparatingConj_iff] at h ⊢
  intro a ha
  refine ⟨fun hz ω _ b => by rw [hz]; simp, fun H => ?_⟩
  exact (h a ha).mpr fun ω hω b => H ω (hsub hω) b

end WstarDense

section Sums

variable {I : Type*} (𝒜 : I → Type*) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]

/-- **117II** (`sum-generation`, proc.tex:3733, Exercise), part 1: if
`Aᵢ ⊆ 𝒜ᵢ` generates `𝒜ᵢ` for each `i`, then `⋃ᵢ κᵢ(Aᵢ)` generates the
direct sum `⊕ᵢ 𝒜ᵢ`.

**The thesis's statement is false and has been repaired here**: the
coprojections `eᵢ = κᵢ(1)` must be added to the generating set.  The printed
statement is refuted by `sum_generation_1_is_false` below; briefly, `κᵢ` is
not unital, so nothing forces `eᵢ` into `W*(⋃ᵢ κᵢ(Aᵢ))`, and for
`𝒜₀ = 𝒜₁ = ℂ` with `A₀ = A₁ = ∅` (or `{0}`, or `{(1,0)} ⊆ ℂ²` for a
counterexample with nontrivial summands and non-empty generating sets) the
right-hand side is the diagonal `ℂ·1`, not `ℂ ⊕ ℂ`.  With the `eᵢ` present
the exercise goes through: `{a : κᵢ(a) ∈ W}` is then a *unital* ∗-subalgebra
of `𝒜ᵢ`, norm-closed and closed under directed suprema (the order on
`⊕ᵢ 𝒜ᵢ` is pointwise), hence all of `𝒜ᵢ`; and a general `x` is the directed
supremum of its finite restrictions. -/
theorem sum_generation_1 [DecidableEq I] (S : ∀ i, Set (𝒜 i))
    (hS : ∀ i, wstar (𝒜 i) (S i) = ⊤) :
    wstar (lp 𝒜 ∞)
      ({x : lp 𝒜 ∞ | ∃ i, ∃ a ∈ S i, x = lp.single ∞ i a} ∪
        {x : lp 𝒜 ∞ | ∃ i, x = lp.single ∞ i 1}) = ⊤ := by
  set G : Set (lp 𝒜 ∞) := {x : lp 𝒜 ∞ | ∃ i, ∃ a ∈ S i, x = lp.single ∞ i a} ∪
      {x : lp 𝒜 ∞ | ∃ i, x = lp.single ∞ i 1} with hG
  obtain ⟨hWvn, hWsub⟩ := isVNSubalgebra_wstar (A := lp 𝒜 ∞) G
  have hone : ∀ i : I, lpKappa i (1 : 𝒜 i) ∈ wstar (lp 𝒜 ∞) G := fun i =>
    hWsub (by rw [hG]; exact Or.inr ⟨i, lpKappa_eq_single i 1⟩)
  have hgen : ∀ (i : I) (a : 𝒜 i), a ∈ S i → lpKappa i a ∈ wstar (lp 𝒜 ∞) G := fun i a ha =>
    hWsub (by rw [hG]; exact Or.inl ⟨i, a, ha, lpKappa_eq_single i a⟩)
  -- `{a | κᵢ(a) ∈ W}` is a von Neumann subalgebra containing `Sᵢ`, hence `𝒜ᵢ`
  have key : ∀ (i : I) (a : 𝒜 i), lpKappa i a ∈ wstar (lp 𝒜 ∞) G := by
    intro i a
    have hle : wstar (𝒜 i) (S i) ≤ kappaPreimage i (wstar (lp 𝒜 ∞) G) (hone i) := by
      apply sInf_le
      exact ⟨isVNSubalgebra_kappaPreimage i (hone i) hWvn, fun b hb => hgen i b hb⟩
    rw [hS i] at hle
    exact hle (by trivial)
  exact StarSubalgebra.eq_top_iff.mpr fun x => wstar_mem_all hWvn key x

/-- Every `ℂ`-∗-subalgebra of `ℂ` is the whole of `ℂ`; so *every* subset of
`ℂ` is a generating subset, `∅` included. -/
theorem starSubalgebra_complex_eq_top (T : StarSubalgebra ℂ ℂ) : T = ⊤ :=
  StarSubalgebra.eq_top_iff.mpr fun x => by
    simpa using T.algebraMap_mem x

/-- The diagonal `{(z, z) : z ∈ ℂ}` of `ℂ ⊕ ℂ = ℓ^∞(Bool)`. -/
def diagBool : StarSubalgebra ℂ (lp (fun _ : Bool => ℂ) ∞) where
  carrier := {x | x true = x false}
  mul_mem' {a b} ha hb := by
    change ((a * b : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = _
    rw [lp.infty_coeFn_mul]
    simp only [Pi.mul_apply]
    rw [show ((a : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = a false from ha,
      show ((b : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = b false from hb]
  one_mem' := by
    change ((1 : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = _
    rw [lp.infty_coeFn_one]
    rfl
  add_mem' {a b} ha hb := by
    change ((a + b : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = _
    rw [lp.coeFn_add]
    simp only [Pi.add_apply]
    rw [show ((a : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = a false from ha,
      show ((b : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = b false from hb]
  zero_mem' := by
    change ((0 : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = _
    rw [lp.coeFn_zero]
    rfl
  algebraMap_mem' c := by
    change ((algebraMap ℂ (lp (fun _ : Bool => ℂ) ∞) c) : ∀ _ : Bool, ℂ) true = _
    rw [Algebra.algebraMap_eq_smul_one, lp.coeFn_smul, lp.infty_coeFn_one]
    rfl
  star_mem' {a} ha := by
    change ((star a : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = _
    rw [lp.coeFn_star]
    simp only [Pi.star_apply]
    rw [show ((a : lp (fun _ : Bool => ℂ) ∞) : ∀ _ : Bool, ℂ) true = a false from ha]

theorem mem_diagBool {x : lp (fun _ : Bool => ℂ) ∞} :
    x ∈ diagBool ↔ x true = x false := Iff.rfl

/-- The diagonal is a von Neumann subalgebra of `ℂ ⊕ ℂ`: it is closed
(evaluation is 1-Lipschitz) and closed under directed suprema, because those
are computed coordinatewise (`lp_infty_exists_isLUB`). -/
theorem isVNSubalgebra_diagBool :
    IsVNSubalgebra (lp (fun _ : Bool => ℂ) ∞) diagBool := by
  constructor
  · exact isClosed_eq ((lp.lipschitzWith_one_eval ∞ true).continuous)
      ((lp.lipschitzWith_one_eval ∞ false).continuous)
  · intro D s hDS hne hdir hlub
    obtain ⟨s', hs', hev⟩ := lp_infty_exists_isLUB D hne hdir ⟨s, hlub.1⟩
    obtain rfl := hlub.unique hs'
    have himg : lpEvalSA (𝒜 := fun _ : Bool => ℂ) true '' D
        = lpEvalSA (𝒜 := fun _ : Bool => ℂ) false '' D :=
      Set.image_congr fun d hd => Subtype.ext (hDS d hd)
    exact congrArg Subtype.val ((hev true).unique (himg ▸ hev false))

/-- **117II**.1 (`sum-generation`, proc.tex:3733, Exercise) is **false as
printed** — see the doc comment of `sum_generation_1` above.  Witness:
`I = Bool`, `𝒜ᵢ = ℂ`, `Aᵢ = ∅` (which does generate `ℂ`, by
`starSubalgebra_complex_eq_top`), while `W*(∅) ⊆ ℂ·1 ⊊ ℂ ⊕ ℂ` because the
diagonal is a von Neumann subalgebra. -/
theorem sum_generation_1_is_false :
    ¬ ∀ (S : Bool → Set ℂ), (∀ i, wstar ℂ (S i) = ⊤) →
      wstar (lp (fun _ : Bool => ℂ) ∞)
        {x : lp (fun _ : Bool => ℂ) ∞ | ∃ i, ∃ a ∈ S i, x = lp.single ∞ i a} = ⊤ := by
  intro h
  have htop := h (fun _ => ∅) (fun _ => starSubalgebra_complex_eq_top _)
  have hle : wstar (lp (fun _ : Bool => ℂ) ∞)
      {x : lp (fun _ : Bool => ℂ) ∞ | ∃ i, ∃ a ∈ (∅ : Set ℂ), x = lp.single ∞ i a}
        ≤ diagBool := by
    apply sInf_le
    exact ⟨isVNSubalgebra_diagBool, by rintro x ⟨i, a, ha, -⟩; exact ha.elim⟩
  rw [htop] at hle
  have hmem : (lp.single ∞ true (1 : ℂ) : lp (fun _ : Bool => ℂ) ∞) ∈ diagBool :=
    hle (by trivial)
  rw [mem_diagBool] at hmem
  rw [lp.single_apply_self, lp.single_apply_ne _ _ _ (by simp)] at hmem
  exact one_ne_zero hmem

/-- **117II** (`sum-generation`, proc.tex:3733, Exercise), part 2: centre
separating collections `Ωᵢ` on the `𝒜ᵢ` give the centre separating
collection `{ω ∘ πᵢ}` on `⊕ᵢ 𝒜ᵢ`. -/
theorem sum_generation_2 (Ω : ∀ i, Set (NPFunctional (𝒜 i)))
    (hΩ : ∀ i, CentreSeparatingConj (𝒜 i) (Ω i)) :
    CentreSeparatingConj (lp 𝒜 ∞)
      {χ : NPFunctional (lp 𝒜 ∞) | ∃ i, ∃ ω ∈ Ω i,
        ∀ x : lp 𝒜 ∞, χ x = ω (x i)} := by
  classical
  rw [centreSeparatingConj_iff]
  intro a ha
  refine ⟨fun h ω hω b => by simp [h], fun H => ?_⟩
  apply lp.ext
  funext i
  have hpi : (0 : 𝒜 i) ≤ (a : ∀ j, 𝒜 j) i := (lp_infty_nonneg_iff a).mp ha i
  have key : (a : ∀ j, 𝒜 j) i = 0 := by
    refine ((centreSeparatingConj_iff (Ω i)).mp (hΩ i) _ hpi).mpr ?_
    intro ω hω b
    -- test `a` against `ω ∘ πᵢ` conjugated by the coprojection `κᵢ(b)`
    have h := H (lpNP i ω) ⟨i, ω, hω, fun x => rfl⟩ (lp.single ∞ i b)
    rw [lp_infty_np_apply] at h
    rw [← h]
    congr 1
    rw [lp.infty_coeFn_mul, lp.infty_coeFn_mul, lp.coeFn_star]
    simp only [Pi.mul_apply, Pi.star_apply, lp.single_apply_self]
  simpa using key

end Sums

/-! ### **117III**

`sum_generation_1`/`sum_generation_2` above are polymorphic in the universes
of `I` and of the summands (`ℓ^∞(X) = ⊕_{x∈X} ℂ` needs that, see
**123I**.3 `linf_tensor`); 117III itself needs `𝒜`, `⊕ᵢ 𝒜ᵢ` and
`⊕ᵢ 𝒜 ⊗ 𝒜ᵢ` in *one* universe, because **116VII** does. -/

section SumsTensor

variable {I : Type u} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]

variable [VonNeumannAlgebra A] [∀ i, Nontrivial (VNT A (𝒜 i))]

set_option linter.unusedSectionVars false in
theorem sumTmul_memℓp (a : A) (b : lp 𝒜 ∞) :
    Memℓp (fun i => a ⊗ᵥ (b : ∀ i, 𝒜 i) i) ∞ := by
  rw [memℓp_infty_iff]
  refine ⟨‖a‖ * ‖b‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  show ‖a ⊗ᵥ (b : ∀ i, 𝒜 i) i‖ ≤ ‖a‖ * ‖b‖
  rw [norm_vtmul]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) b i) (norm_nonneg a)

/-- The map `(a, b) ↦ (a ⊗ bᵢ)ᵢ : 𝒜 × ⊕ᵢ ℬᵢ → ⊕ᵢ (𝒜 ⊗ ℬᵢ)` of **117III**. -/
noncomputable def sumTmul (a : A) (b : lp 𝒜 ∞) : lp (fun i => VNT A (𝒜 i)) ∞ :=
  ⟨fun i => a ⊗ᵥ (b : ∀ i, 𝒜 i) i, sumTmul_memℓp 𝒜 a b⟩

@[simp] theorem sumTmul_apply (a : A) (b : lp 𝒜 ∞) (i : I) :
    (sumTmul 𝒜 a b : ∀ i, VNT A (𝒜 i)) i = a ⊗ᵥ (b : ∀ i, 𝒜 i) i := rfl

/-- `sumTmul` as a bilinear map. -/
noncomputable def sumTmulBilin :
    A →ₗ[ℂ] lp 𝒜 ∞ →ₗ[ℂ] lp (fun i => VNT A (𝒜 i)) ∞ :=
  LinearMap.mk₂ ℂ (sumTmul 𝒜)
    (fun a a' b => by
      refine lp.ext (funext fun i => ?_)
      simp only [sumTmul_apply, lp.coeFn_add, Pi.add_apply]
      exact map_add (((vnTensor A (𝒜 i)).map).flip ((b : ∀ i, 𝒜 i) i)) a a')
    (fun c a b => by
      refine lp.ext (funext fun i => ?_)
      simp only [sumTmul_apply, lp.coeFn_smul, Pi.smul_apply]
      exact map_smul (((vnTensor A (𝒜 i)).map).flip ((b : ∀ i, 𝒜 i) i)) c a)
    (fun a b b' => by
      refine lp.ext (funext fun i => ?_)
      simp only [sumTmul_apply, lp.coeFn_add, Pi.add_apply]
      exact map_add ((vnTensor A (𝒜 i)).map a) _ _)
    (fun c a b => by
      refine lp.ext (funext fun i => ?_)
      simp only [sumTmul_apply, lp.coeFn_smul, Pi.smul_apply]
      exact map_smul ((vnTensor A (𝒜 i)).map a) c _)

@[simp] theorem sumTmulBilin_apply (a : A) (b : lp 𝒜 ∞) (i : I) :
    ((sumTmulBilin 𝒜 a b : lp (fun i => VNT A (𝒜 i)) ∞) : ∀ i, VNT A (𝒜 i)) i
      = a ⊗ᵥ (b : ∀ i, 𝒜 i) i := rfl

/-- `γ` is miu-bilinear, pointwise from the miu-bilinearity of each `⊗`. -/
theorem sumTmulBilin_miu : MIUBilinear (sumTmulBilin 𝒜 (A := A)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine lp.ext (funext fun i => ?_)
    simp only [sumTmulBilin_apply, lp.infty_coeFn_one, Pi.one_apply]
    exact (vnTensor A (𝒜 i)).isTensorProduct.miu.1
  · intro a a' b b'
    refine lp.ext (funext fun i => ?_)
    simp only [sumTmulBilin_apply, lp.infty_coeFn_mul, Pi.mul_apply]
    exact (vnTensor A (𝒜 i)).isTensorProduct.miu.2.1 a a'
      ((b : ∀ i, 𝒜 i) i) ((b' : ∀ i, 𝒜 i) i)
  · intro a b
    refine lp.ext (funext fun i => ?_)
    simp only [sumTmulBilin_apply, lp.coeFn_star, Pi.star_apply]
    exact (vnTensor A (𝒜 i)).isTensorProduct.miu.2.2 a ((b : ∀ i, 𝒜 i) i)

/-- **117III** (`tensor-distributes-over-sums`, proc.tex:3758,
Proposition): the bilinear map
`γ : 𝒜 × ⊕ᵢ ℬᵢ → ⊕ᵢ (𝒜 ⊗ ℬᵢ)`, `(a, b) ↦ (a ⊗ bᵢ)ᵢ` is a tensor
product; whence `𝒜 ⊗ ⊕ᵢ ℬᵢ ≅ ⊕ᵢ (𝒜 ⊗ ℬᵢ)`. -/
theorem tensor_distributes_over_sums :
    ∃ γ : A →ₗ[ℂ] lp 𝒜 ∞ →ₗ[ℂ] lp (fun i => VNT A (𝒜 i)) ∞,
      (∀ (a : A) (b : lp 𝒜 ∞) (i : I), (γ a b) i = a ⊗ᵥ b i) ∧
        IsTensorProduct γ := by
  -- proc.tex:3772 runs this through **116VII** `tensor_characterization`:
  -- `γ` is miu-bilinear, its range generates `⊕ᵢ 𝒜 ⊗ ℬᵢ` by **117II**.1,
  -- the product functional `γ(σ, τ ∘ πᵢ)` is `(σ ⊗ τ) ∘ πᵢ`, and those are
  -- centre separating by **116IV**.2 and **117II**.2.
  classical
  refine ⟨sumTmulBilin 𝒜, fun a b i => rfl, ?_⟩
  set γ := sumTmulBilin 𝒜 (A := A) with hγ
  have hmiu : MIUBilinear γ := sumTmulBilin_miu 𝒜
  set Γ : Set (NPFunctional (lp 𝒜 ∞)) :=
    {χ : NPFunctional (lp 𝒜 ∞) | ∃ i, ∃ ω ∈ (Set.univ : Set (NPFunctional (𝒜 i))),
      ∀ x : lp 𝒜 ∞, χ x = ω ((x : ∀ i, 𝒜 i) i)} with hΓdef
  have hΓ : CentreSeparatingConj (lp 𝒜 ∞) Γ :=
    sum_generation_2 𝒜 (fun _ => Set.univ) (fun _ => centreSeparatingConj_univ)
  refine (tensor_characterization Set.univ Γ centreSeparatingConj_univ hΓ γ
    hmiu).mpr ⟨?_, ?_, ?_⟩
  · -- (1) density, via **117II**.1 `sum_generation_1`
    set S : ∀ i, Set (VNT A (𝒜 i)) :=
      fun i => {t : VNT A (𝒜 i) | ∃ a b, t = (vnTensor A (𝒜 i)).map a b} with hS
    have hStop : ∀ i, wstar (VNT A (𝒜 i)) (S i) = ⊤ := fun i =>
      wstar_eq_top_of_dense_span (S i) (vnTensor A (𝒜 i)).isTensorProduct.dense
    have hgen := sum_generation_1 (fun i => VNT A (𝒜 i)) S hStop
    have hsub : ({x : lp (fun i => VNT A (𝒜 i)) ∞ | ∃ i, ∃ a ∈ S i,
          x = lp.single ∞ i a} ∪
        {x : lp (fun i => VNT A (𝒜 i)) ∞ | ∃ i, x = lp.single ∞ i 1})
        ⊆ (tensorSpan γ hmiu : Set (lp (fun i => VNT A (𝒜 i)) ∞)) := by
      rintro x (⟨i, c, ⟨a, b, rfl⟩, rfl⟩ | ⟨i, rfl⟩)
      · refine Submodule.subset_span ⟨a, lp.single ∞ i b, ?_⟩
        refine lp.ext (funext fun j => ?_)
        by_cases hj : j = i
        · subst hj
          rw [lp.single_apply_self]
          show ((vnTensor A (𝒜 j)).map a) b
            = a ⊗ᵥ ((lp.single ∞ j b : lp 𝒜 ∞) : ∀ i, 𝒜 i) j
          rw [lp.single_apply_self]
          rfl
        · rw [lp.single_apply_ne _ _ _ hj]
          show (0 : VNT A (𝒜 j)) = a ⊗ᵥ ((lp.single ∞ i b : lp 𝒜 ∞) : ∀ i, 𝒜 i) j
          rw [lp.single_apply_ne _ _ _ hj]
          exact (map_zero ((vnTensor A (𝒜 j)).map a)).symm
      · refine Submodule.subset_span ⟨1, lp.single ∞ i 1, ?_⟩
        refine lp.ext (funext fun j => ?_)
        by_cases hj : j = i
        · subst hj
          rw [lp.single_apply_self]
          show (1 : VNT A (𝒜 j))
            = 1 ⊗ᵥ ((lp.single ∞ j (1 : 𝒜 j) : lp 𝒜 ∞) : ∀ i, 𝒜 i) j
          rw [lp.single_apply_self]
          exact (vnTensor A (𝒜 j)).isTensorProduct.miu.1.symm
        · rw [lp.single_apply_ne _ _ _ hj]
          show (0 : VNT A (𝒜 j))
            = 1 ⊗ᵥ ((lp.single ∞ i (1 : 𝒜 i) : lp 𝒜 ∞) : ∀ i, 𝒜 i) j
          rw [lp.single_apply_ne _ _ _ hj]
          exact (map_zero ((vnTensor A (𝒜 j)).map 1)).symm
    have htop : wstar (lp (fun i => VNT A (𝒜 i)) ∞)
        (tensorSpan γ hmiu : Set (lp (fun i => VNT A (𝒜 i)) ∞)) = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hgen]
      exact wstar_mono hsub
    exact dense_of_wstar_eq_top _ htop
  · -- (2) the product functionals exist: `γ(σ, τ ∘ πᵢ) = (σ ⊗ τ) ∘ πᵢ`
    rintro σ - χ ⟨i, ω, -, hχ⟩
    refine ⟨lpNP i (prodNP (vnTensor A (𝒜 i)).isTensorProduct σ ω), fun a b => ?_⟩
    rw [lp_infty_np_apply, hχ b]
    show prodNP (vnTensor A (𝒜 i)).isTensorProduct σ ω
        ((vnTensor A (𝒜 i)).map a ((b : ∀ i, 𝒜 i) i)) = _
    exact prodNP_apply _ σ ω a _
  · -- (3) they are centre separating: **116IV**.2 plus **117II**.2
    have h := sum_generation_2 (fun i => VNT A (𝒜 i))
      (fun i => {χ : NPFunctional (VNT A (𝒜 i)) |
        ∃ ω ∈ (Set.univ : Set (NPFunctional A)),
        ∃ θ ∈ (Set.univ : Set (NPFunctional (𝒜 i))),
        ∀ (a : A) (b : 𝒜 i), χ (a ⊗ᵥ b) = ω a * θ b})
      (fun i => tensor_generation_2 Set.univ Set.univ centreSeparatingConj_univ
        centreSeparatingConj_univ)
    refine centreSeparatingConj_mono h ?_
    rintro χ ⟨i, ω, ⟨σ, -, τ, -, hω⟩, hχ⟩
    refine ⟨σ, Set.mem_univ _, lpNP i τ, ⟨i, τ, Set.mem_univ _, fun x => rfl⟩,
      fun a b => ?_⟩
    rw [hχ, lp_infty_np_apply]
    exact hω a ((b : ∀ i, 𝒜 i) i)

end SumsTensor

/-! ## Parsec 1180: tensors of projections and carriers -/

section Carriers

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B] [VonNeumannAlgebra C]
  [VonNeumannAlgebra D]

/-- **118II** (proc.tex:3802, Lemma), part 1:
`⌈a ⊗ b⌉ = ⌈a⌉ ⊗ ⌈b⌉` for positive `a`, `b`. -/
theorem ceil_tensor (a : A) (b : B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ceil (a ⊗ᵥ b) = ceil a ⊗ᵥ ceil b := by
  -- The thesis's proof (proc.tex:3813): `⌈a ⊗ b⌉ = ⌈⌈a⌉ ⊗ b⌉ = ⌈⌈a⌉ ⊗ ⌈b⌉⌉`
  -- by **60VI** `ncp_ceil` applied to the two np-maps `(·) ⊗ b` and
  -- `⌈a⌉ ⊗ (·)`, and `⌈a⌉ ⊗ ⌈b⌉` is already a projection.
  have hmiu := (vnTensor A B).isTensorProduct.miu
  have hmul : ∀ (x x' : A) (y y' : B),
      (x ⊗ᵥ y) * (x' ⊗ᵥ y') = (x * x') ⊗ᵥ (y * y') :=
    fun x x' y y' => (hmiu.2.1 x x' y y').symm
  have hstar : ∀ (x : A) (y : B), star (x ⊗ᵥ y) = star x ⊗ᵥ star y :=
    fun x y => hmiu.2.2 x y
  have hca : IsStarProjection (ceil a) := (ceil_spec ha).1
  have hcb : IsStarProjection (ceil b) := (ceil_spec hb).1
  have hca0 : (0 : A) ≤ ceil a := by
    have he : ceil a = star (ceil a) * ceil a := by
      rw [hca.isSelfAdjoint.star_eq, hca.isIdempotentElem.eq]
    rw [he]; exact star_mul_self_nonneg _
  -- monotonicity of the two slices
  have hposL : ∀ (y : B), 0 ≤ y → ∀ x x' : A, x ≤ x' → x ⊗ᵥ y ≤ x' ⊗ᵥ y := by
    intro y hy x x' hx
    have h := vtmul_nonneg (x' - x) y (sub_nonneg.mpr hx) hy
    have he : ((x' - x) ⊗ᵥ y) = x' ⊗ᵥ y - x ⊗ᵥ y := by
      show (vnTensor A B).map (x' - x) y = _
      rw [map_sub, LinearMap.sub_apply]
      rfl
    rw [he] at h
    exact sub_nonneg.mp h
  have hposR : ∀ (x : A), 0 ≤ x → ∀ y y' : B, y ≤ y' → x ⊗ᵥ y ≤ x ⊗ᵥ y' := by
    intro x hx y y' hy
    have h := vtmul_nonneg x (y' - y) hx (sub_nonneg.mpr hy)
    have he : (x ⊗ᵥ (y' - y)) = x ⊗ᵥ y' - x ⊗ᵥ y :=
      map_sub ((vnTensor A B).map x) y' y
    rw [he] at h
    exact sub_nonneg.mp h
  -- the np-map `(·) ⊗ b`
  set FL : A →ₚ[ℂ] VNT A B :=
    { toFun := fun x => x ⊗ᵥ b
      map_add' := fun x y => by
        show (vnTensor A B).map (x + y) b = _
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := fun c x => by
        show (vnTensor A B).map (c • x) b = _
        rw [map_smul, LinearMap.smul_apply]
        rfl
      monotone' := fun x x' h => hposL b hb x x' h } with hFLdef
  have hFLn : PreservesDirSups ⇑FL :=
    ((p_uwcont FL).out 0 2).mp (continuous_ultraweak_vtmul_left b)
  -- the np-map `⌈a⌉ ⊗ (·)`
  set FR : B →ₚ[ℂ] VNT A B :=
    { toFun := fun y => ceil a ⊗ᵥ y
      map_add' := fun x y => map_add ((vnTensor A B).map (ceil a)) x y
      map_smul' := fun c x => map_smul ((vnTensor A B).map (ceil a)) c x
      monotone' := fun y y' h => hposR (ceil a) hca0 y y' h } with hFRdef
  have hFRn : PreservesDirSups ⇑FR :=
    ((p_uwcont FR).out 0 2).mp (continuous_ultraweak_vtmul_right (ceil a))
  have h1 : ceil (a ⊗ᵥ b) = ceil (ceil a ⊗ᵥ b) := ncp_ceil FL hFLn a ha
  have h2 : ceil (ceil a ⊗ᵥ b) = ceil (ceil a ⊗ᵥ ceil b) := ncp_ceil FR hFRn b hb
  have hproj : IsStarProjection (ceil a ⊗ᵥ ceil b) := by
    constructor
    · show (ceil a ⊗ᵥ ceil b) * (ceil a ⊗ᵥ ceil b) = ceil a ⊗ᵥ ceil b
      rw [hmul, hca.isIdempotentElem.eq, hcb.isIdempotentElem.eq]
    · show star (ceil a ⊗ᵥ ceil b) = ceil a ⊗ᵥ ceil b
      rw [hstar, hca.isSelfAdjoint.star_eq, hcb.isSelfAdjoint.star_eq]
  rw [h1, h2, ceil_of_isStarProjection hproj]

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

set_option linter.unusedSectionVars false in
/-- Transfer of the chosen tensor product along a universe lift: given
nmiu-isomorphisms `εA : 𝒳 ≅ 𝒜'`, `εB : 𝒴 ≅ ℬ'` and `ℓ : 𝒳 ⊗ 𝒴 ≅ 𝒯'`,
with `𝒜'`, `ℬ'`, `𝒯'` in one universe, there is an nmiu-isomorphism
`Φ : 𝒜' ⊗ ℬ' → 𝒯'` with `Φ(εA a ⊗ εB b) = ℓ(a ⊗ b)`.  (`isTensorProduct_comp`
moves the factors, `isTensorProduct_comp_target` moves the target, and
**114II** `tensor_uniqueness` — a single-universe statement, here applied at
the common universe — compares the result with `𝒜' ⊗ ℬ'`.) -/
theorem exists_vnt_transfer {Xa : Type p} {Xb : Type q} {A' B' T' : Type r}
    [CStarAlgebra Xa] [PartialOrder Xa] [StarOrderedRing Xa]
    [VonNeumannAlgebra Xa]
    [CStarAlgebra Xb] [PartialOrder Xb] [StarOrderedRing Xb]
    [VonNeumannAlgebra Xb]
    [CStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A'] [VonNeumannAlgebra A']
    [CStarAlgebra B'] [PartialOrder B'] [StarOrderedRing B'] [VonNeumannAlgebra B']
    [CStarAlgebra T'] [PartialOrder T'] [StarOrderedRing T'] [VonNeumannAlgebra T']
    (εA : NMIUMap Xa A') (hA : Function.Bijective ⇑εA)
    (εB : NMIUMap Xb B') (hB : Function.Bijective ⇑εB)
    (ℓ : NMIUMap (VNT Xa Xb) T') (hℓ : Function.Bijective ⇑ℓ) :
    ∃ Φ : NMIUMap (VNT A' B') T', Function.Bijective ⇑Φ ∧
      ∀ (a : Xa) (b : Xb), Φ (εA a ⊗ᵥ εB b) = ℓ (a ⊗ᵥ b) := by
  have h1 : IsTensorProduct (((vnTensor Xa Xb).map).compr₂ (nmiuLin ℓ)) :=
    isTensorProduct_comp_target (vnTensor Xa Xb).isTensorProduct ℓ hℓ
  have h2 := isTensorProduct_comp (nmiuSymm εA hA) (nmiuSymm_bijective εA hA)
    (nmiuSymm εB hB) (nmiuSymm_bijective εB hB) h1
  obtain ⟨Φ, hΦe, hΦb, -⟩ :=
    tensor_uniqueness (vnTensor A' B').map _ (vnTensor A' B').isTensorProduct h2
  refine ⟨Φ, hΦb, fun a b => ?_⟩
  have hab := hΦe (εA a) (εB b)
  show Φ ((vnTensor A' B').map (εA a) (εB b)) = ℓ ((vnTensor Xa Xb).map a b)
  rw [hab]
  show ℓ ((vnTensor Xa Xb).map (nmiuSymm εA hA (εA a)) (nmiuSymm εB hB (εB b)))
    = ℓ ((vnTensor Xa Xb).map a b)
  rw [nmiuSymm_apply_apply εA hA, nmiuSymm_apply_apply εB hB]


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
        (∀ (a : 𝒜) (b : ℬ), s' (a ⊗ᵥ b) = b ⊗ᵥ a) → s' = s := by
  -- The exercise itself is `isTensorProduct_flip`: `(a,b) ↦ b ⊗ a` is a
  -- tensor product because every clause of 108II is swap-invariant.  The
  -- deduction then wants **114II** `tensor_uniqueness`, which confines its
  -- two factors and both targets to *one* universe, while `𝒜 : Type u` and
  -- `ℬ : Type v`.  So we lift `𝒜`, `ℬ` into `Type (max u v)` (`exists_vnLift`)
  -- and transport the two chosen tensor products there and back with
  -- `exists_vnt_transfer` — the device of `exists_tmapM`.  Both *targets*
  -- `𝒜 ⊗ ℬ` and `ℬ ⊗ 𝒜` already live in `Type (max u v)`, so the transport
  -- of the target is the identity.
  obtain ⟨A', _, _, _, _, εA, hεA⟩ := exists_vnLift.{u, v} 𝒜
  obtain ⟨B', _, _, _, _, εB, hεB⟩ := exists_vnLift.{v, u} ℬ
  obtain ⟨Φ, hΦb, hΦe⟩ := exists_vnt_transfer εA hεA εB hεB
    (nmiuId (VNT 𝒜 ℬ)) nmiuId_bijective
  obtain ⟨Ψ, hΨb, hΨe⟩ := exists_vnt_transfer εB hεB εA hεA
    (nmiuId (VNT ℬ 𝒜)) nmiuId_bijective
  -- `Φ : 𝒜' ⊗ ℬ' ≅ 𝒜 ⊗ ℬ` with `Φ(εA a ⊗ εB b) = a ⊗ b`, and
  -- `Ψ : ℬ' ⊗ 𝒜' ≅ ℬ ⊗ 𝒜` with `Ψ(εB b ⊗ εA a) = b ⊗ a`.
  have hΦe' : ∀ (a : 𝒜) (b : ℬ), Φ (εA a ⊗ᵥ εB b) = a ⊗ᵥ b := hΦe
  have hΨe' : ∀ (b : ℬ) (a : 𝒜), Ψ (εB b ⊗ᵥ εA a) = b ⊗ᵥ a := hΨe
  -- 114II at the single universe `max u v`.
  obtain ⟨s₀, hs₀e, hs₀b, hs₀u⟩ :=
    tensor_uniqueness (vnTensor A' B').map ((vnTensor B' A').map.flip)
      (vnTensor A' B').isTensorProduct
      (isTensorProduct_flip (vnTensor B' A').isTensorProduct)
  have hs₀e' : ∀ (a : A') (b : B'), s₀ (a ⊗ᵥ b) = b ⊗ᵥ a := hs₀e
  refine ⟨nmiuComp Ψ (nmiuComp s₀ (nmiuSymm Φ hΦb)), ?_, ?_, ?_⟩
  · intro a b
    show Ψ (s₀ (nmiuSymm Φ hΦb (a ⊗ᵥ b))) = b ⊗ᵥ a
    rw [← hΦe' a b, nmiuSymm_apply_apply Φ hΦb, hs₀e', hΨe']
  · exact hΨb.comp (hs₀b.comp (nmiuSymm_bijective Φ hΦb))
  · intro s' hs'
    set k' : NMIUMap (VNT A' B') (VNT B' A') :=
      nmiuComp (nmiuSymm Ψ hΨb) (nmiuComp s' Φ) with hk'
    have hk'a : ∀ (a : A') (b : B'), k' ((vnTensor A' B').map a b)
        = (vnTensor B' A').map.flip a b := by
      intro x y
      obtain ⟨a, rfl⟩ := hεA.2 x
      obtain ⟨b, rfl⟩ := hεB.2 y
      show nmiuSymm Ψ hΨb (s' (Φ (εA a ⊗ᵥ εB b))) = εB b ⊗ᵥ εA a
      rw [hΦe' a b, hs' a b, ← hΨe' b a, nmiuSymm_apply_apply Ψ hΨb]
    have hkk : k' = s₀ := hs₀u k' hk'a
    refine DFunLike.ext _ _ fun x => ?_
    have h1 : nmiuSymm Ψ hΨb (s' (Φ (nmiuSymm Φ hΦb x))) = s₀ (nmiuSymm Φ hΦb x) :=
      congrArg (fun f : NMIUMap (VNT A' B') (VNT B' A') => f (nmiuSymm Φ hΦb x)) hkk
    rw [nmiuSymm_apply_apply' Φ hΦb] at h1
    show s' x = Ψ (s₀ (nmiuSymm Φ hΦb x))
    rw [← h1, nmiuSymm_apply_apply' Ψ hΨb]

/-- The braiding `γ_{𝒜,ℬ} : 𝒜 ⊗ ℬ → ℬ ⊗ 𝒜` (119IVc), by choice. -/
noncomputable def braiding : NMIUMap (VNT 𝒜 ℬ) (VNT ℬ 𝒜) :=
  (exists_braiding 𝒜 ℬ).choose

@[simp] theorem braiding_apply (a : 𝒜) (b : ℬ) : braiding 𝒜 ℬ (a ⊗ᵥ b) = b ⊗ᵥ a :=
  (exists_braiding 𝒜 ℬ).choose_spec.1 a b

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
          (∀ (a : A) (z : ℂ), r' (a ⊗ᵥ z) = z • a) → r' = r := by
  -- The exercise proper: `(z,a) ↦ z·a` satisfies 108II.  Density is trivial
  -- (the range is already all of `𝒜`), the product functional of `(σ,τ)` is
  -- `σ(1)·τ` (an np-functional by `smulNP`, since `σ(1) ≥ 0`), and
  -- faithfulness is 42I's `np_faithful` at `σ = complexIdNP`.  The right-hand
  -- version is then `isTensorProduct_flip`.  The *deduction* again wants
  -- **114II**, which is single-universe while `ℂ : Type 0` and `𝒜 : Type u`,
  -- so `ℂ` is lifted into `Type u` with `exists_vnLift` and the chosen
  -- tensor products are moved across with `exists_vnt_transfer`.
  have hsm : ∀ (z : ℂ) (a : A), LinearMap.lsmul ℂ A z a = z • a := fun _ _ => rfl
  have hnpsmul : ∀ (ω : NPFunctional A) (z : ℂ) (a : A), ω (z • a) = z * ω a := by
    intro ω z a
    show npLin ω (z • a) = _
    rw [map_smul]; rfl
  have hlsmul : IsTensorProduct (LinearMap.lsmul ℂ A) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show (1 : ℂ) • (1 : A) = 1
      rw [one_smul]
    · intro z z' a a'
      show (z * z') • (a * a') = (z • a) * (z' • a')
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    · intro z a
      show star (z • a) = (star z) • (star a)
      rw [star_smul]
    · have htop : (Submodule.span ℂ {t : A | ∃ (z : ℂ) (a : A),
          t = LinearMap.lsmul ℂ A z a}) = ⊤ := by
        refine eq_top_iff.mpr fun a _ => Submodule.subset_span ?_
        exact ⟨1, a, (one_smul ℂ a).symm⟩
      have hcoe : ((⊤ : Submodule ℂ A) : Set A) = Set.univ := Submodule.top_coe
      rw [htop, hcoe]
      exact @dense_univ A (ultraweak A)
    · intro σ τ
      have hσ1 : (0 : ℂ) ≤ σ 1 := npFunctional_nonneg σ zero_le_one
      have him : (σ 1).im = 0 := ((Complex.le_def.mp hσ1).2).symm
      have hre : (0 : ℝ) ≤ (σ 1).re := by simpa using (Complex.le_def.mp hσ1).1
      have hcoe : (((σ 1).re : ℝ) : ℂ) = σ 1 := by
        apply Complex.ext <;> simp [him]
      have hσz : ∀ z : ℂ, σ z = z * σ 1 := by
        intro z
        have h : npLin σ (z • (1 : ℂ)) = z • npLin σ (1 : ℂ) := map_smul _ _ _
        show npLin σ z = z * npLin σ 1
        simpa [smul_eq_mul] using h
      refine ⟨smulNP hre τ, fun z a => ?_⟩
      rw [hsm, smulNP_apply, hcoe, hnpsmul τ z a, hσz z]
      ring
    · intro t ht hfaith
      refine VonNeumannAlgebra.np_faithful t ht fun τ => ?_
      refine hfaith Theses.A.VN.complexIdNP τ τ fun z a => ?_
      rw [hsm, hnpsmul τ z a]
      rfl
  refine ⟨hlsmul, isTensorProduct_flip hlsmul, ?_, ?_⟩
  · -- the left unitor
    obtain ⟨C₀, _, _, _, _, εC, hεC⟩ := exists_vnLift.{0, u} ℂ
    obtain ⟨Φ, hΦb, hΦe⟩ := exists_vnt_transfer εC hεC (nmiuId A) nmiuId_bijective
      (nmiuId (VNT ℂ A)) nmiuId_bijective
    have hΦe' : ∀ (z : ℂ) (a : A), Φ (εC z ⊗ᵥ a) = z ⊗ᵥ a := hΦe
    obtain ⟨l₀, hl₀e, hl₀b, hl₀u⟩ :=
      tensor_uniqueness (vnTensor C₀ A).map
        ((LinearMap.lsmul ℂ A).compl₁₂ (nmiuLin (nmiuSymm εC hεC)) (nmiuLin (nmiuId A)))
        (vnTensor C₀ A).isTensorProduct
        (isTensorProduct_comp (nmiuSymm εC hεC) (nmiuSymm_bijective εC hεC)
          (nmiuId A) nmiuId_bijective hlsmul)
    have hl₀e' : ∀ (z : C₀) (a : A), l₀ (z ⊗ᵥ a) = (nmiuSymm εC hεC z) • a := hl₀e
    refine ⟨nmiuComp l₀ (nmiuSymm Φ hΦb), ?_, ?_, ?_⟩
    · intro z a
      show l₀ (nmiuSymm Φ hΦb (z ⊗ᵥ a)) = z • a
      rw [← hΦe' z a, nmiuSymm_apply_apply Φ hΦb, hl₀e', nmiuSymm_apply_apply εC hεC]
    · exact hl₀b.comp (nmiuSymm_bijective Φ hΦb)
    · intro l' hl'
      have hk' : ∀ (z : C₀) (a : A), (nmiuComp l' Φ) ((vnTensor C₀ A).map z a)
          = ((LinearMap.lsmul ℂ A).compl₁₂ (nmiuLin (nmiuSymm εC hεC))
              (nmiuLin (nmiuId A))) z a := by
        intro w a
        obtain ⟨z, rfl⟩ := hεC.2 w
        show l' (Φ (εC z ⊗ᵥ a)) = (nmiuSymm εC hεC (εC z)) • a
        rw [hΦe' z a, hl' z a, nmiuSymm_apply_apply εC hεC]
      have hkk := hl₀u (nmiuComp l' Φ) hk'
      refine DFunLike.ext _ _ fun x => ?_
      have h1 : l' (Φ (nmiuSymm Φ hΦb x)) = l₀ (nmiuSymm Φ hΦb x) :=
        congrArg (fun f : NMIUMap (VNT C₀ A) A => f (nmiuSymm Φ hΦb x)) hkk
      rw [nmiuSymm_apply_apply' Φ hΦb] at h1
      exact h1
  · -- the right unitor
    obtain ⟨C₀, _, _, _, _, εC, hεC⟩ := exists_vnLift.{0, u} ℂ
    obtain ⟨Φ, hΦb, hΦe⟩ := exists_vnt_transfer (nmiuId A) nmiuId_bijective εC hεC
      (nmiuId (VNT A ℂ)) nmiuId_bijective
    have hΦe' : ∀ (a : A) (z : ℂ), Φ (a ⊗ᵥ εC z) = a ⊗ᵥ z := hΦe
    obtain ⟨r₀, hr₀e, hr₀b, hr₀u⟩ :=
      tensor_uniqueness (vnTensor A C₀).map
        ((LinearMap.lsmul ℂ A).flip.compl₁₂ (nmiuLin (nmiuId A))
          (nmiuLin (nmiuSymm εC hεC)))
        (vnTensor A C₀).isTensorProduct
        (isTensorProduct_comp (nmiuId A) nmiuId_bijective
          (nmiuSymm εC hεC) (nmiuSymm_bijective εC hεC) (isTensorProduct_flip hlsmul))
    have hr₀e' : ∀ (a : A) (z : C₀), r₀ (a ⊗ᵥ z) = (nmiuSymm εC hεC z) • a := hr₀e
    refine ⟨nmiuComp r₀ (nmiuSymm Φ hΦb), ?_, ?_, ?_⟩
    · intro a z
      show r₀ (nmiuSymm Φ hΦb (a ⊗ᵥ z)) = z • a
      rw [← hΦe' a z, nmiuSymm_apply_apply Φ hΦb, hr₀e', nmiuSymm_apply_apply εC hεC]
    · exact hr₀b.comp (nmiuSymm_bijective Φ hΦb)
    · intro r' hr'
      have hk' : ∀ (a : A) (z : C₀), (nmiuComp r' Φ) ((vnTensor A C₀).map a z)
          = ((LinearMap.lsmul ℂ A).flip.compl₁₂ (nmiuLin (nmiuId A))
              (nmiuLin (nmiuSymm εC hεC))) a z := by
        intro a w
        obtain ⟨z, rfl⟩ := hεC.2 w
        show r' (Φ (a ⊗ᵥ εC z)) = (nmiuSymm εC hεC (εC z)) • a
        rw [hΦe' a z, hr' a z, nmiuSymm_apply_apply εC hεC]
      have hkk := hr₀u (nmiuComp r' Φ) hk'
      refine DFunLike.ext _ _ fun x => ?_
      have h1 : r' (Φ (nmiuSymm Φ hΦb x)) = r₀ (nmiuSymm Φ hΦb x) :=
        congrArg (fun f : NMIUMap (VNT A C₀) A => f (nmiuSymm Φ hΦb x)) hkk
      rw [nmiuSymm_apply_apply' Φ hΦb] at h1
      exact h1

variable (A) in
/-- The left unitor `λ_𝒜 : ℂ ⊗ 𝒜 → 𝒜` (119IVb), by choice. -/
noncomputable def leftUnitor : NMIUMap (VNT ℂ A) A :=
  (exists_unitors (A := A)).2.2.1.choose

@[simp] theorem leftUnitor_apply (z : ℂ) (a : A) : leftUnitor A (z ⊗ᵥ a) = z • a :=
  (exists_unitors (A := A)).2.2.1.choose_spec.1 z a

variable (A) in
/-- The right unitor `ρ_𝒜 : 𝒜 ⊗ ℂ → 𝒜` (119IVb), by choice. -/
noncomputable def rightUnitor : NMIUMap (VNT A ℂ) A :=
  (exists_unitors (A := A)).2.2.2.choose

@[simp] theorem rightUnitor_apply (a : A) (z : ℂ) : rightUnitor A (a ⊗ᵥ z) = z • a :=
  (exists_unitors (A := A)).2.2.2.choose_spec.1 a z

/-- Uniqueness clause of the right unitor (119IVb). -/
theorem rightUnitor_unique (r' : NMIUMap (VNT A ℂ) A)
    (hr' : ∀ (a : A) (z : ℂ), r' (a ⊗ᵥ z) = z • a) : r' = rightUnitor A :=
  (exists_unitors (A := A)).2.2.2.choose_spec.2.2 r' hr'

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
there is a unique nmiu-map `ρ ⊗ σ` acting on pure tensors as expected.

The four algebras sit in four independent universes, so 112XI/114I — which
`exists_tmap` uses directly — cannot be applied: they confine their algebras
to one universe.  Rather than re-universing parsecs 1120–1140, we *lift* the
four algebras and the two tensor products into the common universe
`max u₁ u₂ u₃ u₄` (`exists_vnLift`), apply `exists_tmap` there, and transport
back along `exists_vnt_transfer`. -/
theorem exists_tmapM (ρ : NMIUMap A₂ C₂) (σ : NMIUMap B₂ D₂) :
    ∃! h : NMIUMap (VNT A₂ B₂) (VNT C₂ D₂),
      ∀ (a : A₂) (b : B₂), h (a ⊗ᵥ b) = ρ a ⊗ᵥ σ b := by
  obtain ⟨A', _, _, _, _, εA, hεA⟩ := exists_vnLift.{u₁, max u₁ u₂ u₃ u₄} A₂
  obtain ⟨B', _, _, _, _, εB, hεB⟩ := exists_vnLift.{u₂, max u₁ u₂ u₃ u₄} B₂
  obtain ⟨C', _, _, _, _, εC, hεC⟩ := exists_vnLift.{u₃, max u₁ u₂ u₃ u₄} C₂
  obtain ⟨D', _, _, _, _, εD, hεD⟩ := exists_vnLift.{u₄, max u₁ u₂ u₃ u₄} D₂
  obtain ⟨T', _, _, _, _, l, hl⟩ :=
    exists_vnLift.{max u₁ u₂, max u₁ u₂ u₃ u₄} (VNT A₂ B₂)
  obtain ⟨S', _, _, _, _, m, hm⟩ :=
    exists_vnLift.{max u₃ u₄, max u₁ u₂ u₃ u₄} (VNT C₂ D₂)
  obtain ⟨Φ, hΦb, hΦe⟩ := exists_vnt_transfer εA hεA εB hεB l hl
  obtain ⟨Ψ, hΨb, hΨe⟩ := exists_vnt_transfer εC hεC εD hεD m hm
  set ρ' : NMIUMap A' C' := nmiuComp εC (nmiuComp ρ (nmiuSymm εA hεA)) with hρ'
  set σ' : NMIUMap B' D' := nmiuComp εD (nmiuComp σ (nmiuSymm εB hεB)) with hσ'
  have hρ'a : ∀ a : A₂, ρ' (εA a) = εC (ρ a) := by
    intro a; show εC (ρ (nmiuSymm εA hεA (εA a))) = εC (ρ a)
    rw [nmiuSymm_apply_apply]
  have hσ'a : ∀ b : B₂, σ' (εB b) = εD (σ b) := by
    intro b; show εD (σ (nmiuSymm εB hεB (εB b))) = εD (σ b)
    rw [nmiuSymm_apply_apply]
  -- 115II at the common universe, upgraded to an nmiu-map by 115II.1–.3
  set kl := (tmap (nmiuNCP ρ') (nmiuNCP σ')).toCompletelyPositiveMap.toLinearMap
    with hkl
  have hfun := tensor_functorial (nmiuNCP ρ') (nmiuNCP σ')
  have hmul := hfun.1 (fun a a' => map_mul ρ'.toStarAlgHom a a')
    (fun b b' => map_mul σ'.toStarAlgHom b b')
  have hstar := hfun.2.1 (fun a => map_star ρ'.toStarAlgHom a)
    (fun b => map_star σ'.toStarAlgHom b)
  have hunit := hfun.2.2.1 (map_one ρ'.toStarAlgHom) (map_one σ'.toStarAlgHom)
  set k : NMIUMap (VNT A' B') (VNT C' D') :=
    { toStarAlgHom :=
        { toFun := ⇑kl
          map_one' := hunit
          map_mul' := hmul
          map_zero' := map_zero kl
          map_add' := map_add kl
          commutes' := fun r => by
            show kl (algebraMap ℂ (VNT A' B') r) = algebraMap ℂ (VNT C' D') r
            rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
              map_smul]
            exact congrArg (fun z => r • z) hunit
          map_star' := hstar }
      preservesDirSups' := (tmap (nmiuNCP ρ') (nmiuNCP σ')).preservesDirSups' }
    with hk
  have hka : ∀ (a : A') (b : B'), k (a ⊗ᵥ b) = ρ' a ⊗ᵥ σ' b := by
    intro a b
    show kl (a ⊗ᵥ b) = ρ' a ⊗ᵥ σ' b
    exact tmap_apply (nmiuNCP ρ') (nmiuNCP σ') a b
  refine ⟨nmiuComp (nmiuSymm m hm) (nmiuComp Ψ
      (nmiuComp k (nmiuComp (nmiuSymm Φ hΦb) l))), ?_, ?_⟩
  · intro a b
    show nmiuSymm m hm (Ψ (k (nmiuSymm Φ hΦb (l (a ⊗ᵥ b))))) = ρ a ⊗ᵥ σ b
    rw [← hΦe a b, nmiuSymm_apply_apply Φ hΦb, hka, hρ'a, hσ'a, hΨe,
      nmiuSymm_apply_apply m hm]
  · intro h' hh'
    set k' : NMIUMap (VNT A' B') (VNT C' D') :=
      nmiuComp (nmiuSymm Ψ hΨb) (nmiuComp m
        (nmiuComp h' (nmiuComp (nmiuSymm l hl) Φ))) with hk'
    have hk'a : ∀ (a : A') (b : B'), k' (a ⊗ᵥ b) = ρ' a ⊗ᵥ σ' b := by
      intro x y
      obtain ⟨a, rfl⟩ := hεA.2 x
      obtain ⟨b, rfl⟩ := hεB.2 y
      show nmiuSymm Ψ hΨb (m (h' (nmiuSymm l hl (Φ (εA a ⊗ᵥ εB b))))) = _
      rw [hΦe a b, nmiuSymm_apply_apply l hl, hh' a b, ← hΨe (ρ a) (σ b),
        nmiuSymm_apply_apply Ψ hΨb, hρ'a, hσ'a]
    have hkk : (tmap (nmiuNCP ρ') (nmiuNCP σ')) = nmiuNCP k' :=
      (exists_tmap (nmiuNCP ρ') (nmiuNCP σ')).unique
        (tmap_apply (nmiuNCP ρ') (nmiuNCP σ'))
        (fun a b => by
          show k' (a ⊗ᵥ b) = ρ' a ⊗ᵥ σ' b
          exact hk'a a b)
    have hkeq : ∀ x : VNT A' B', k x = k' x := by
      intro x
      show kl x = k' x
      exact congrArg (fun f : NCPMap (VNT A' B') (VNT C' D') => f x) hkk
    refine DFunLike.coe_injective (funext fun t => ?_)
    show h' t = nmiuSymm m hm (Ψ (k (nmiuSymm Φ hΦb (l t))))
    have h1 : k' (nmiuSymm Φ hΦb (l t)) = nmiuSymm Ψ hΨb (m (h' t)) := by
      show nmiuSymm Ψ hΨb (m (h' (nmiuSymm l hl (Φ (nmiuSymm Φ hΦb (l t)))))) = _
      rw [nmiuSymm_apply_apply' Φ hΦb, nmiuSymm_apply_apply l hl]
    rw [hkeq, h1, nmiuSymm_apply_apply' Ψ hΨb, nmiuSymm_apply_apply m hm]


/-- The nmiu-map `ρ ⊗ σ` (infrastructure for 119V). -/
noncomputable def tmapM (ρ : NMIUMap A₂ C₂) (σ : NMIUMap B₂ D₂) :
    NMIUMap (VNT A₂ B₂) (VNT C₂ D₂) := (exists_tmapM ρ σ).choose

@[simp] theorem tmapM_apply (ρ : NMIUMap A₂ C₂) (σ : NMIUMap B₂ D₂)
    (a : A₂) (b : B₂) : tmapM ρ σ (a ⊗ᵥ b) = ρ a ⊗ᵥ σ b :=
  (exists_tmapM ρ σ).choose_spec.1 a b

end TmapM

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
      ∀ t : VNT B ℂ, leftUnitor B (braiding B ℂ t) = rightUnitor B t := by
  -- Both halves are uniqueness arguments: two nmiu-maps agreeing on pure
  -- tensors agree.  For the first, the relevant uniqueness is that of
  -- `id ⊗ id` (`exists_tmapM`); for the second it is the right unitor's own.
  constructor
  · have h1 : nmiuComp (braiding B A) (braiding A B) = nmiuId (VNT A B) :=
      (exists_tmapM (nmiuId A) (nmiuId B)).unique
        (fun a b => by
          show braiding B A (braiding A B (a ⊗ᵥ b)) = nmiuId A a ⊗ᵥ nmiuId B b
          rw [braiding_apply, braiding_apply, nmiuId_apply, nmiuId_apply])
        (fun a b => by
          show nmiuId (VNT A B) (a ⊗ᵥ b) = nmiuId A a ⊗ᵥ nmiuId B b
          rfl)
    intro t
    exact congrArg (fun f : NMIUMap (VNT A B) (VNT A B) => f t) h1
  · have h2 : nmiuComp (leftUnitor B) (braiding B ℂ) = rightUnitor B :=
      rightUnitor_unique _ fun b z => by
        show leftUnitor B (braiding B ℂ (b ⊗ᵥ z)) = z • b
        rw [braiding_apply, leftUnitor_apply]
    intro t
    exact congrArg (fun f : NMIUMap (VNT B ℂ) B => f t) h2

end Monoidal

end Theses.A.Proc


