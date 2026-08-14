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
    ∃ γ : VNSub (H →L[ℂ] H) SA hSA →ₗ[ℂ] VNSub (K →L[ℂ] K) SB hSB →ₗ[ℂ]
        VNSub (HT H K →L[ℂ] HT H K)
          (wstar (HT H K →L[ℂ] HT H K)
            {x | ∃ a ∈ SA, ∃ b ∈ SB, x = opTensor a b})
          (isVNSubalgebra_wstar _).1,
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
        {x : lp 𝒜 ∞ | ∃ i, x = lp.single ∞ i 1}) = ⊤ := sorry

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
    (hΩ : ∀ i, CentreSeparating (𝒜 i) (Ω i)) :
    CentreSeparating (lp 𝒜 ∞)
      {χ : NPFunctional (lp 𝒜 ∞) | ∃ i, ∃ ω ∈ Ω i,
        ∀ x : lp 𝒜 ∞, χ x = ω (x i)} := by
  classical
  intro a hcen hpos hkill
  apply lp.ext
  funext i
  -- centrality passes to each coordinate (test against `κᵢ(b)`)
  have hci : IsCentral (𝒜 i) ((a : lp 𝒜 ∞) i) := by
    intro b
    have h := hcen (lp.single ∞ i b)
    have h1 := congrFun (congrArg (fun x : lp 𝒜 ∞ => (x : ∀ j, 𝒜 j)) h) i
    rw [lp.infty_coeFn_mul, lp.infty_coeFn_mul] at h1
    simpa [lp.single_apply_self] using h1
  have hpi : (0 : 𝒜 i) ≤ (a : lp 𝒜 ∞) i := (lp_infty_nonneg_iff a).mp hpos i
  -- `ω ∘ πᵢ` is `lpNP i ω`, hence belongs to the collection
  have hki : ∀ ω ∈ Ω i, ω ((a : lp 𝒜 ∞) i) = 0 := by
    intro ω hω
    have := hkill (lpNP i ω) ⟨i, ω, hω, fun x => rfl⟩
    rwa [lp_infty_np_apply] at this
  simpa using hΩ i _ hci hpi hki

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
    preservesDirSups' := preservesDirSups_id }

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
