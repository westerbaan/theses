/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 2622–3526.

  parsec 1500:  the self-dual completion of a module with 𝒷-valued inner
                product
  parsec 1510:  its universal property
  parsec 1520:  𝒷-sesquilinear forms on self-dual modules; 𝒷ᵃ(X) is a von
                Neumann algebra
  parsec 1530:  ad_T is (n)cp

Statements only; every proof is `sorry`.  See `HilbertModules.lean` for the
conventions (Mathlib's left-action mirror of the thesis's right modules;
the ultranorm uniformity encoded through `UnTendsto`/`UnCauchy`/`UnDense`).

The type `Ba 𝒷 X` of adjointable bounded operators on a Hilbert 𝒷-module,
together with its C*-algebra structure (**143IV**) and canonical order, now
lives in `HilbertModules.lean` (right after 143IV), where the positive and
negative parts that 144I needs are available.  Those instances are **proved**,
not asserted: they are built from `baSubalgebra` (32III), `moduleAdjointTo_unique`,
`module_maps_cstar_identity` (32XII) and `bax_cstar` (32XIII).
-/
import Theses.B.Dils.HilbertModules

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra WithCStarModule
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u v w

namespace Theses.B.Dils

/-! ## Parsec 1500: the self-dual completion

**150I** (dils.tex:2624): introduction — nothing to formalize.
**150III**–**150XV** (fast nets, the uniform space `N`, the uniformity on
`V̄`, the module structure, extending the seminorms, the transfinite
induction on compatible extensions, self-duality) are the proof of
**150II** — not converted. -/

section Completion

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

/-- **150II** (`dils-completion`, dils.tex:2632, Theorem), the data: a
**self-dual completion** of a 𝒷-module `V` with 𝒷-valued inner product
`B`: a self-dual Hilbert 𝒷-module `X` together with a 𝒷-linear
inner-product-preserving `η : V → X` whose image is ultranorm dense. -/
structure SelfDualCompletion (B : BInner 𝒷 V) : Type (max u (v + 1) (w + 1))
    where
  /-- The carrier of the completion. -/
  X : Type w
  [nacg : NormedAddCommGroup X]
  [mod : NormedSpace ℂ X]
  [smul : SMul 𝒷 X]
  [cstarMod : CStarModule 𝒷 X]
  [complete : CompleteSpace X]
  /-- `X` is self dual. -/
  selfDual : SelfDual 𝒷 X
  /-- The embedding `η : V → X`. -/
  η : V → X
  η_add : ∀ v w : V, η (v + w) = η v + η w
  η_smul_complex : ∀ (c : ℂ) (v : V), η (c • v) = c • η v
  η_smul : ∀ (b : 𝒷) (v : V), η (b • v) = b • η v
  /-- `η` preserves the inner product: `[v,w] = ⟨η v, η w⟩`. -/
  η_inner : ∀ v w : V, inner 𝒷 (η v) (η w) = B.inner v w
  /-- The image of `η` is ultranorm dense in `X`. -/
  dense : UnDense (inner 𝒷) (Set.range η)

attribute [instance] SelfDualCompletion.nacg SelfDualCompletion.mod
  SelfDualCompletion.smul SelfDualCompletion.cstarMod
  SelfDualCompletion.complete

/-- **150II** (`dils-completion`, dils.tex:2632, Theorem): for a von
Neumann algebra `𝒷`, every 𝒷-module `V` with (possibly indefinite)
𝒷-valued inner product has a self-dual completion. -/
theorem dils_completion [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V) :
    Nonempty (SelfDualCompletion.{u, v, max u v} B) :=
  sorry

/-! ## Parsec 1510: the universal property of the completion

**151I** (dils.tex:3249): introduction — nothing to formalize.
**151II** is the proof of **151Ia**, transcribed below. -/

/-! ### Elementary properties of the ultranorm seminorms

`HilbertModules.lean` keeps most of these `private`; they are restated here
for `CStarModule`s (so that they are phrased with `inner 𝒷` rather than
`(cstarBInner 𝒷 W).inner` and can be used by `rw`). -/

section UnivHelpers

variable {W : Type*} {V' : Type*}
  [NormedAddCommGroup W] [Module ℂ W] [SMul 𝒷 W] [CStarModule 𝒷 W]
  [AddCommGroup V'] [Module ℂ V'] [SMul 𝒷 V']

omit [StarOrderedRing 𝒷] in
private theorem npf_smul (ω : NPFunctional 𝒷) (c : ℂ) (a : 𝒷) : ω (c • a) = c * ω a :=
  map_smul ω.toPositiveLinearMap c a

omit [StarOrderedRing 𝒷] in
private theorem npf_nonneg (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    (0 : ℂ) ≤ ω a := by
  have h : ω.toPositiveLinearMap 0 ≤ ω.toPositiveLinearMap a :=
    ω.toPositiveLinearMap.monotone ha
  rwa [map_zero] at h

omit [StarOrderedRing 𝒷] in
private theorem npf_im_zero (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    (ω a).im = 0 := by
  simpa using ((Complex.le_def.mp (npf_nonneg ω ha)).2).symm

private theorem le_of_forall_eps {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) :
    a ≤ b := by
  by_contra hc
  have hlt : b < a := lt_of_not_ge hc
  have := h ((a - b) / 2) (by linarith)
  linarith

private theorem un_zero (ω : NPFunctional 𝒷) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (0 : W) = 0 := by
  have h : (inner 𝒷 (0 : W) (0 : W) : 𝒷) = 0 :=
    (cstarBInner 𝒷 W).inner_zero_left 0
  rw [unSeminorm, h]
  simp

omit [StarOrderedRing 𝒷] in
private theorem un_neg (ω : NPFunctional 𝒷) (z : W) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (-z)
      = unSeminorm ω (inner 𝒷 : W → W → 𝒷) z := by
  rw [unSeminorm, unSeminorm, CStarModule.inner_neg_left,
    CStarModule.inner_neg_right, neg_neg]

private theorem op_smul_sub' (b : 𝒷) (z z' : W) : b • (z - z') = b • z - b • z' := by
  have h := op_smul_add b (z - z') z'
  rw [sub_add_cancel] at h
  rw [h]; abel

private theorem un_add_le (ω : NPFunctional 𝒷) (z z' : W) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (z + z')
      ≤ unSeminorm ω (inner 𝒷 : W → W → 𝒷) z
        + unSeminorm ω (inner 𝒷 : W → W → 𝒷) z' :=
  unSeminorm_add_le ω (cstarBInner 𝒷 W) z z'

private theorem un_sub_le (ω : NPFunctional 𝒷) (a b c : W) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (a - c)
      ≤ unSeminorm ω (inner 𝒷 : W → W → 𝒷) (a - b)
        + unSeminorm ω (inner 𝒷 : W → W → 𝒷) (b - c) := by
  have h := un_add_le ω (a - b) (b - c)
  rwa [show a - b + (b - c) = a - c by abel] at h

omit [StarOrderedRing 𝒷] in
private theorem un_sub_comm (ω : NPFunctional 𝒷) (a b : W) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (a - b)
      = unSeminorm ω (inner 𝒷 : W → W → 𝒷) (b - a) := by
  rw [show b - a = -(a - b) by abel, un_neg]

omit [StarOrderedRing 𝒷] in
private theorem un_smul_complex (ω : NPFunctional 𝒷) (c : ℂ) (z : W) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (c • z)
      = ‖c‖ * unSeminorm ω (inner 𝒷 : W → W → 𝒷) z := by
  have h : (inner 𝒷 (c • z) (c • z) : 𝒷)
      = ((Complex.normSq c : ℝ) : ℂ) • inner 𝒷 z z := by
    rw [CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
      smul_smul]
    congr 1
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  rw [unSeminorm, unSeminorm, h, npf_smul, Complex.re_ofReal_mul,
    Real.sqrt_mul (Complex.normSq_nonneg c), Complex.norm_def]

private theorem un_op_smul [VonNeumannAlgebra 𝒷] (ω : NPFunctional 𝒷) (b : 𝒷)
    (z : W) :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (b • z)
      = unSeminorm (conjNP (star b) ω) (inner 𝒷 : W → W → 𝒷) z := by
  have h : (inner 𝒷 (b • z) (b • z) : 𝒷) = b * inner 𝒷 z z * star b :=
    (cstarBInner 𝒷 W).inner_op_smul_self b z
  rw [unSeminorm, unSeminorm, h, conjNP_apply, star_star]

/-- The ultranorm seminorms are separating: an element which is `ε`-small for
every np-functional and every `ε > 0` is `0`. -/
private theorem eq_zero_of_un_small [VonNeumannAlgebra 𝒷] (z : W)
    (h : ∀ (ω : NPFunctional 𝒷) (ε : ℝ), 0 < ε →
      unSeminorm ω (inner 𝒷 : W → W → 𝒷) z ≤ ε) : z = 0 := by
  have hinner : (inner 𝒷 z z : 𝒷) = 0 := by
    refine np_separating _ fun ω => ?_
    have hz : unSeminorm ω (inner 𝒷 : W → W → 𝒷) z = 0 :=
      le_antisymm (le_of_forall_eps fun ε hε => by simpa using h ω ε hε)
        (unSeminorm_nonneg _ _ _)
    have hsq : unSeminorm ω (inner 𝒷 : W → W → 𝒷) z ^ 2
        = (ω (inner 𝒷 z z : 𝒷)).re := unSeminorm_sq ω (cstarBInner 𝒷 W) z
    rw [hz] at hsq
    have hre : (ω (inner 𝒷 z z : 𝒷)).re = 0 := by rw [← hsq]; norm_num
    have hnn : (0 : 𝒷) ≤ inner 𝒷 z z := CStarModule.inner_self_nonneg
    have him : (ω (inner 𝒷 z z : 𝒷)).im = 0 := npf_im_zero ω hnn
    exact Complex.ext (by simpa using hre) (by simpa using him)
  have hn : ‖z‖ = 0 := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷), hinner]
    simp
  exact norm_eq_zero.mp hn

/-- **144V** in seminorm form, phrased with `inner 𝒷` on the target. -/
private theorem un_bmm_le (B₁ : BInner 𝒷 V') (Cc : ℝ) (hCc : 0 ≤ Cc) (S : V' → W)
    (hS : IsBoundedModuleMap B₁ (cstarBInner 𝒷 W) Cc S) (ω : NPFunctional 𝒷)
    (x : V') :
    unSeminorm ω (inner 𝒷 : W → W → 𝒷) (S x) ≤ Cc * unSeminorm ω B₁.inner x :=
  unSeminorm_boundedModuleMap_le B₁ (cstarBInner 𝒷 W) Cc hCc S hS ω x

end UnivHelpers

/-- **151Ia** (`selfdual-completion-univ`, dils.tex:3254, Lemma): let
`η : V → X` be an inner-product-preserving 𝒷-linear map into a self-dual
Hilbert 𝒷-module with ultranorm dense image (e.g. a self-dual completion,
**150II**).  Then for every bounded 𝒷-linear `T : V → Y` into a self-dual
Hilbert 𝒷-module `Y` there is a unique bounded 𝒷-linear `T̂ : X → Y` with
`T̂ ∘ η = T` (moreover `‖T̂‖ = ‖T‖`). -/
theorem selfdual_completion_univ [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) {Y : Type w}
    [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]
    [CompleteSpace Y] (hY : SelfDual 𝒷 Y) (C : ℝ) (T : V → Y)
    (hT : IsBoundedModuleMap B (cstarBInner 𝒷 Y) C T) :
    ∃! T' : E.X → Y,
      (∃ C' : ℝ, IsBoundedModuleMap (cstarBInner 𝒷 E.X) (cstarBInner 𝒷 Y)
        C' T') ∧ ∀ v : V, T' (E.η v) = T v := by
  classical
  -- replace `C` by a nonnegative bound
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : (0 : ℝ) ≤ C' := le_max_right _ _
  have hTC' : IsBoundedModuleMap B (cstarBInner 𝒷 Y) C' T :=
    { hT with
      bound := fun v => (hT.bound v).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) }
  -- elementary consequences of the axioms of `η` and `T`
  have hη0 : E.η 0 = 0 := by
    simpa using E.η_smul_complex 0 0
  have hηsub : ∀ v v' : V, E.η (v - v') = E.η v - E.η v' := by
    intro v v'
    have h := E.η_add (v - v') v'
    rw [sub_add_cancel] at h
    rw [h]; abel
  have hηsem : ∀ (ω : NPFunctional 𝒷) (v : V),
      unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (E.η v) = unSeminorm ω B.inner v := by
    intro ω v
    rw [unSeminorm, unSeminorm, E.η_inner]
  have hT0 : T 0 = 0 := by
    simpa using hT.smul_complex 0 0
  have hTsub : ∀ v v' : V, T (v - v') = T v - T v' := by
    intro v v'
    have h := hT.add (v - v') v'
    rw [sub_add_cancel] at h
    rw [h]; abel
  -- ultranorm density of the image of `η`, in the form needed below
  have hdense' : ∀ (x : E.X) (s : Finset (NPFunctional 𝒷)) (ε : ℝ), 0 < ε →
      ∃ v : V, ∀ ω ∈ s,
        unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η v) ≤ ε := by
    intro x s ε hε
    obtain ⟨d, ⟨v, rfl⟩, hd⟩ := E.dense x (Fintype.card s)
      (fun i => (((Fintype.equivFin s).symm i : {y // y ∈ s}) : NPFunctional 𝒷)) ε hε
    exact ⟨v, fun ω hω => by simpa using hd ((Fintype.equivFin s) ⟨ω, hω⟩)⟩
  -- **149V**: a self-dual module is ultranorm complete
  have hYun : UnComplete (inner 𝒷 : Y → Y → 𝒷) :=
    ((dils_selfdual (𝒷 := 𝒷) (X := Y)).out 0 1).mp hY
  -- the heart of the matter: the ultranorm limit `T̂ x = unlim T x_α`, together
  -- with the estimate `‖T̂ x - T v‖_ω ≤ C ‖x - η v‖_ω` that characterizes it
  have hexists : ∀ x : E.X, ∃ y : Y, ∀ (ω : NPFunctional 𝒷) (v : V),
      unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (y - T v)
        ≤ C' * unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η v) := by
    intro x
    -- the approximating net, indexed by finite sets of (functional, precision)
    choose vnet hvnet using fun s : Finset (NPFunctional 𝒷 × ℕ) =>
      hdense' x (s.image Prod.fst)
        (1 / (((s.sup (fun p => p.2) : ℕ) : ℝ) + 1)) (by positivity)
    have hvnet' : ∀ (s : Finset (NPFunctional 𝒷 × ℕ)) (p : NPFunctional 𝒷 × ℕ),
        p ∈ s → unSeminorm p.1 (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s))
          ≤ 1 / ((p.2 : ℝ) + 1) := by
      intro s p hp
      refine (hvnet s p.1 (Finset.mem_image_of_mem _ hp)).trans ?_
      have hle : (p.2 : ℝ) ≤ ((s.sup (fun q => q.2) : ℕ) : ℝ) := by
        exact_mod_cast Finset.le_sup (f := fun q : NPFunctional 𝒷 × ℕ => q.2) hp
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    -- the ultranorm-Cauchy estimate along the net
    have hcau : ∀ (ω : NPFunctional 𝒷) (s s' : Finset (NPFunctional 𝒷 × ℕ))
        (δ : ℝ), unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s)) ≤ δ →
        unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s')) ≤ δ →
        unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s) - T (vnet s'))
          ≤ C' * (δ + δ) := by
      intro ω s s' δ h1 h2
      calc unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s) - T (vnet s'))
          = unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s - vnet s')) := by
            rw [hTsub]
        _ ≤ C' * unSeminorm ω B.inner (vnet s - vnet s') :=
            un_bmm_le B C' hC'0 T hTC' ω _
        _ = C' * unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷)
              (E.η (vnet s) - E.η (vnet s')) := by rw [← hηsem, hηsub]
        _ ≤ C' * (unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (E.η (vnet s) - x)
              + unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s'))) :=
            mul_le_mul_of_nonneg_left (un_sub_le ω _ x _) hC'0
        _ ≤ C' * (δ + δ) := by
            rw [un_sub_comm ω (E.η (vnet s)) x]
            exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC'0
    have hFcauchy : UnCauchy (inner 𝒷 : Y → Y → 𝒷)
        (Filter.map (fun s => T (vnet s)) atTop) := by
      intro ω ε hε
      obtain ⟨n, hn⟩ :=
        exists_nat_one_div_lt (show (0 : ℝ) < ε / (2 * (C' + 1)) by positivity)
      refine ⟨(fun s => T (vnet s)) '' (Set.Ici {(ω, n)}),
        Filter.image_mem_map (Filter.Ici_mem_atTop _), ?_⟩
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
      have hsub : ({(ω, n)} : Finset (NPFunctional 𝒷 × ℕ)) ⊆ s := hs
      have hsub' : ({(ω, n)} : Finset (NPFunctional 𝒷 × ℕ)) ⊆ s' := hs'
      have h1 : unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s))
          ≤ ε / (2 * (C' + 1)) :=
        (hvnet' s (ω, n) (hsub (Finset.mem_singleton_self _))).trans hn.le
      have h2 : unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s'))
          ≤ ε / (2 * (C' + 1)) :=
        (hvnet' s' (ω, n) (hsub' (Finset.mem_singleton_self _))).trans hn.le
      refine (hcau ω s s' _ h1 h2).trans ?_
      have hden : (0 : ℝ) < 2 * (C' + 1) := by positivity
      have hδ : ε / (2 * (C' + 1)) * (2 * (C' + 1)) = ε := by field_simp
      have hδ0 : (0 : ℝ) ≤ ε / (2 * (C' + 1)) := by positivity
      nlinarith [hδ, hδ0]
    obtain ⟨y₀, hy₀⟩ := hYun _ Filter.map_neBot hFcauchy
    refine ⟨y₀, fun ω v => ?_⟩
    refine le_of_forall_eps fun ε hε => ?_
    -- pick a stage of the net which is both close to `y₀` and close to `x`
    have hev : ∀ᶠ s in (atTop : Filter (Finset (NPFunctional 𝒷 × ℕ))),
        unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s) - y₀)
          < ε / (2 * (C' + 1)) :=
      (Filter.tendsto_map'_iff.mpr (hy₀ ω))
        (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / (2 * (C' + 1))))
    obtain ⟨s₁, hs₁⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨n, hn⟩ :=
      exists_nat_one_div_lt (show (0 : ℝ) < ε / (2 * (C' + 1)) by positivity)
    set s : Finset (NPFunctional 𝒷 × ℕ) := s₁ ∪ {(ω, n)} with hsdef
    have ha : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s) - y₀)
        ≤ ε / (2 * (C' + 1)) := (hs₁ s Finset.subset_union_left).le
    have hb : unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η (vnet s))
        ≤ ε / (2 * (C' + 1)) :=
      (hvnet' s (ω, n)
        (Finset.mem_union_right _ (Finset.mem_singleton_self _))).trans hn.le
    calc unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (y₀ - T v)
        ≤ unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (y₀ - T (vnet s))
            + unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s) - T v) :=
          un_sub_le ω _ (T (vnet s)) _
      _ ≤ ε / (2 * (C' + 1))
            + C' * (unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (E.η (vnet s) - x)
              + unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η v)) := by
          refine add_le_add ((un_sub_comm ω y₀ (T (vnet s))) ▸ ha) ?_
          calc unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s) - T v)
              = unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T (vnet s - v)) := by rw [hTsub]
            _ ≤ C' * unSeminorm ω B.inner (vnet s - v) :=
                un_bmm_le B C' hC'0 T hTC' ω _
            _ = C' * unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷)
                  (E.η (vnet s) - E.η v) := by rw [← hηsem, hηsub]
            _ ≤ _ := mul_le_mul_of_nonneg_left (un_sub_le ω _ x _) hC'0
      _ ≤ C' * unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η v) + ε := by
          rw [un_sub_comm ω (E.η (vnet s)) x]
          have hkey : C' * (ε / (2 * (C' + 1))) ≤ ε / 2 := by
            rw [mul_div_assoc'] at *
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [hε.le, hC'0]
          have hε2 : ε / (2 * (C' + 1)) ≤ ε / 2 := by
            apply div_le_div_of_nonneg_left hε.le (by norm_num)
            nlinarith [hC'0]
          nlinarith [mul_le_mul_of_nonneg_left hb hC'0,
            unSeminorm_nonneg ω (inner 𝒷 : E.X → E.X → 𝒷) (x - E.η v)]
  choose T' hkey using hexists
  -- `T̂` extends `T`
  have hηT : ∀ v : V, T' (E.η v) = T v := by
    intro v
    refine sub_eq_zero.mp (eq_zero_of_un_small (𝒷 := 𝒷) (W := Y) _ fun ω ε hε => ?_)
    have h := hkey (E.η v) ω v
    rw [sub_self, un_zero (W := E.X) ω, mul_zero] at h
    exact h.trans hε.le
  -- the fundamental estimate turns every algebraic identity into a
  -- density argument, one np-functional at a time
  have hbound : ∀ (ω : NPFunctional 𝒷) (x : E.X),
      unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' x)
        ≤ C' * unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) x := by
    intro ω x
    have h := hkey x ω 0
    rwa [hT0, sub_zero, hη0, sub_zero] at h
  have hadd : ∀ x x' : E.X, T' (x + x') = T' x + T' x' := by
    intro x x'
    refine sub_eq_zero.mp (eq_zero_of_un_small (𝒷 := 𝒷) (W := Y) _ fun ω ε hε => ?_)
    obtain ⟨v, hv⟩ := hdense' x {ω} (ε / (4 * (C' + 1))) (by positivity)
    obtain ⟨v', hv'⟩ := hdense' x' {ω} (ε / (4 * (C' + 1))) (by positivity)
    have hv1 := hv ω (Finset.mem_singleton_self _)
    have hv2 := hv' ω (Finset.mem_singleton_self _)
    have hsplit : T' (x + x') - (T' x + T' x')
        = (T' (x + x') - T (v + v')) + ((T v - T' x) + (T v' - T' x')) := by
      rw [hT.add]; abel
    have hA : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' (x + x') - T (v + v'))
        ≤ C' * (ε / (4 * (C' + 1)) + ε / (4 * (C' + 1))) := by
      refine (hkey (x + x') ω (v + v')).trans ?_
      rw [E.η_add]
      refine mul_le_mul_of_nonneg_left ?_ hC'0
      calc unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (x + x' - (E.η v + E.η v'))
          = unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷)
              ((x - E.η v) + (x' - E.η v')) := by rw [show x + x' - (E.η v + E.η v')
                = (x - E.η v) + (x' - E.η v') by abel]
        _ ≤ _ := un_add_le ω _ _
        _ ≤ _ := add_le_add hv1 hv2
    have hB1 : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T v - T' x)
        ≤ C' * (ε / (4 * (C' + 1))) := by
      rw [un_sub_comm]
      exact (hkey x ω v).trans (mul_le_mul_of_nonneg_left hv1 hC'0)
    have hB2 : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T v' - T' x')
        ≤ C' * (ε / (4 * (C' + 1))) := by
      rw [un_sub_comm]
      exact (hkey x' ω v').trans (mul_le_mul_of_nonneg_left hv2 hC'0)
    have hfin : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷)
        (T' (x + x') - (T' x + T' x'))
          ≤ C' * (ε / (4 * (C' + 1)) + ε / (4 * (C' + 1)))
            + (C' * (ε / (4 * (C' + 1))) + C' * (ε / (4 * (C' + 1)))) := by
      rw [hsplit]
      exact (un_add_le ω _ _).trans
        (add_le_add hA ((un_add_le ω _ _).trans (add_le_add hB1 hB2)))
    refine hfin.trans ?_
    have hle : C' * (ε / (4 * (C' + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hε.le, hC'0]
    linarith
  have hsmulC : ∀ (c : ℂ) (x : E.X), T' (c • x) = c • T' x := by
    intro c x
    refine sub_eq_zero.mp (eq_zero_of_un_small (𝒷 := 𝒷) (W := Y) _ fun ω ε hε => ?_)
    obtain ⟨v, hv⟩ := hdense' x {ω}
      (ε / (2 * (C' + 1) * (‖c‖ + 1))) (by positivity)
    have hv1 := hv ω (Finset.mem_singleton_self _)
    have hsplit : T' (c • x) - c • T' x
        = (T' (c • x) - T (c • v)) + c • (T v - T' x) := by
      rw [hT.smul_complex, smul_sub]; abel
    have hA : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' (c • x) - T (c • v))
        ≤ C' * (‖c‖ * (ε / (2 * (C' + 1) * (‖c‖ + 1)))) := by
      refine (hkey (c • x) ω (c • v)).trans ?_
      rw [E.η_smul_complex, ← smul_sub, un_smul_complex]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv1 (norm_nonneg c)) hC'0
    have hB : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (c • (T v - T' x))
        ≤ ‖c‖ * (C' * (ε / (2 * (C' + 1) * (‖c‖ + 1)))) := by
      rw [un_smul_complex, un_sub_comm]
      exact mul_le_mul_of_nonneg_left
        ((hkey x ω v).trans (mul_le_mul_of_nonneg_left hv1 hC'0)) (norm_nonneg c)
    have hfin : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' (c • x) - c • T' x)
        ≤ C' * (‖c‖ * (ε / (2 * (C' + 1) * (‖c‖ + 1))))
          + ‖c‖ * (C' * (ε / (2 * (C' + 1) * (‖c‖ + 1)))) := by
      rw [hsplit]
      exact (un_add_le ω _ _).trans (add_le_add hA hB)
    refine hfin.trans ?_
    have hle : C' * (‖c‖ * (ε / (2 * (C' + 1) * (‖c‖ + 1)))) ≤ ε / 2 := by
      rw [mul_div_assoc', mul_div_assoc',
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hε.le, hC'0, norm_nonneg c]
    linarith
  have hsmulB : ∀ (b : 𝒷) (x : E.X), T' (b • x) = b • T' x := by
    intro b x
    refine sub_eq_zero.mp (eq_zero_of_un_small (𝒷 := 𝒷) (W := Y) _ fun ω ε hε => ?_)
    obtain ⟨v, hv⟩ := hdense' x {ω, conjNP (star b) ω}
      (ε / (2 * (C' + 1))) (by positivity)
    have hv2 := hv (conjNP (star b) ω) (by simp)
    have hsplit : T' (b • x) - b • T' x
        = (T' (b • x) - T (b • v)) + b • (T v - T' x) := by
      rw [hT.smul, op_smul_sub' (W := Y)]
      abel
    have hA : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' (b • x) - T (b • v))
        ≤ C' * (ε / (2 * (C' + 1))) := by
      refine (hkey (b • x) ω (b • v)).trans ?_
      rw [E.η_smul, ← op_smul_sub' (W := E.X), un_op_smul]
      exact mul_le_mul_of_nonneg_left hv2 hC'0
    have hB : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (b • (T v - T' x))
        ≤ C' * (ε / (2 * (C' + 1))) := by
      rw [un_op_smul, un_sub_comm]
      exact (hkey x (conjNP (star b) ω) v).trans
        (mul_le_mul_of_nonneg_left hv2 hC'0)
    have hfin : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' (b • x) - b • T' x)
        ≤ C' * (ε / (2 * (C' + 1))) + C' * (ε / (2 * (C' + 1))) := by
      rw [hsplit]
      exact (un_add_le ω _ _).trans (add_le_add hA hB)
    refine hfin.trans ?_
    have hle : C' * (ε / (2 * (C' + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hε.le, hC'0]
    linarith
  -- boundedness: `⟨T̂x, T̂x⟩ ≤ ‖T‖² ⟨x,x⟩` by order separation of the
  -- np-functionals (**44XI**), which is the thesis's `innerprod-ultraweak` step
  have hnorm : ∀ x : E.X, ‖T' x‖ ≤ C' * ‖x‖ := by
    intro x
    have hle : (inner 𝒷 (T' x) (T' x) : 𝒷) ≤ (C' ^ 2) • (inner 𝒷 x x : 𝒷) := by
      refine np_orderSeparating _ _
        (IsSelfAdjoint.of_nonneg CStarModule.inner_self_nonneg)
        (IsSelfAdjoint.of_nonneg (smul_nonneg (by positivity)
          CStarModule.inner_self_nonneg)) fun ω => ?_
      have hs1 : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T' x) ^ 2
          = (ω (inner 𝒷 (T' x) (T' x) : 𝒷)).re := unSeminorm_sq ω (cstarBInner 𝒷 Y) _
      have hs2 : unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) x ^ 2
          = (ω (inner 𝒷 x x : 𝒷)).re := unSeminorm_sq ω (cstarBInner 𝒷 E.X) _
      have hre : (ω (inner 𝒷 (T' x) (T' x) : 𝒷)).re
          ≤ (ω ((C' ^ 2) • (inner 𝒷 x x : 𝒷))).re := by
        have hsm : (ω ((C' ^ 2) • (inner 𝒷 x x : 𝒷))).re
            = C' ^ 2 * (ω (inner 𝒷 x x : 𝒷)).re := by
          rw [show ((C' ^ 2 : ℝ) • (inner 𝒷 x x : 𝒷))
              = ((C' ^ 2 : ℝ) : ℂ) • (inner 𝒷 x x : 𝒷) from
            (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _),
            npf_smul, Complex.re_ofReal_mul]
        rw [hsm, ← hs1, ← hs2]
        have h := hbound ω x
        have h0 := unSeminorm_nonneg ω (inner 𝒷 : Y → Y → 𝒷) (T' x)
        have h1 := unSeminorm_nonneg ω (inner 𝒷 : E.X → E.X → 𝒷) x
        nlinarith
      have him1 : (ω (inner 𝒷 (T' x) (T' x) : 𝒷)).im = 0 :=
        npf_im_zero ω (CStarModule.inner_self_nonneg (E := Y) (x := T' x))
      have him2 : (ω ((C' ^ 2) • (inner 𝒷 x x : 𝒷))).im = 0 :=
        npf_im_zero ω (smul_nonneg (by positivity : (0:ℝ) ≤ C' ^ 2)
          (CStarModule.inner_self_nonneg (E := E.X) (x := x)))
      exact Complex.le_def.mpr ⟨hre, by rw [him1, him2]⟩
    have hnn : (0 : 𝒷) ≤ inner 𝒷 (T' x) (T' x) := CStarModule.inner_self_nonneg
    have hnle := CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ C' ^ 2)]
      at hnle
    have e1 : ‖T' x‖ ^ 2 = ‖(inner 𝒷 (T' x) (T' x) : 𝒷)‖ :=
      CStarModule.norm_sq_eq (A := 𝒷)
    have e2 : ‖x‖ ^ 2 = ‖(inner 𝒷 x x : 𝒷)‖ := CStarModule.norm_sq_eq (A := 𝒷)
    have h1 : (0 : ℝ) ≤ C' * ‖x‖ := mul_nonneg hC'0 (norm_nonneg x)
    have hsq : ‖T' x‖ ^ 2 ≤ (C' * ‖x‖) ^ 2 := by
      rw [e1, mul_pow, e2]
      exact hnle
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq h1] at hs
  refine ⟨T', ⟨⟨C', ?_⟩, hηT⟩, ?_⟩
  · refine ⟨hadd, hsmulC, hsmulB, fun x => ?_⟩
    rw [cstarBInner_norm, cstarBInner_norm]
    exact hnorm x
  · rintro S ⟨⟨C₂, hS⟩, hSη⟩
    set C₂' : ℝ := max C₂ 0 with hC₂'def
    have hC₂'0 : (0 : ℝ) ≤ C₂' := le_max_right _ _
    have hSC₂' : IsBoundedModuleMap (cstarBInner 𝒷 E.X) (cstarBInner 𝒷 Y) C₂' S :=
      { hS with
        bound := fun x => (hS.bound x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) }
    funext x
    refine sub_eq_zero.mp (eq_zero_of_un_small (𝒷 := 𝒷) (W := Y) _ fun ω ε hε => ?_)
    obtain ⟨v, hv⟩ := hdense' x {ω} (ε / (2 * (C' + C₂' + 1))) (by positivity)
    have hv1 := hv ω (Finset.mem_singleton_self _)
    have hSsub : S x - S (E.η v) = S (x - E.η v) := by
      have h := hS.add (x - E.η v) (E.η v)
      rw [sub_add_cancel] at h
      rw [h]; abel
    have hA : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (S x - T v)
        ≤ C₂' * (ε / (2 * (C' + C₂' + 1))) := by
      rw [← hSη v, hSsub]
      exact (un_bmm_le (cstarBInner 𝒷 E.X) C₂' hC₂'0 S hSC₂' ω _).trans
        (mul_le_mul_of_nonneg_left hv1 hC₂'0)
    have hB : unSeminorm ω (inner 𝒷 : Y → Y → 𝒷) (T v - T' x)
        ≤ C' * (ε / (2 * (C' + C₂' + 1))) := by
      rw [un_sub_comm]
      exact (hkey x ω v).trans (mul_le_mul_of_nonneg_left hv1 hC'0)
    refine (un_sub_le ω (S x) (T v) (T' x)).trans ?_
    have hle1 : C₂' * (ε / (2 * (C' + C₂' + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hε.le, hC'0, hC₂'0]
    have hle2 : C' * (ε / (2 * (C' + C₂' + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hε.le, hC'0, hC₂'0]
    linarith [hA, hB]

end Completion

/-! ## Parsec 1520: sesquilinear forms and 𝒷ᵃ(X) for self-dual X

**152I** (dils.tex:3320): introduction; **152III**/**152IV** (Example) —
nothing to formalize.  **152VI** is the proof of **152V**;
**152XI**–**152XIII** the proof of **152X** — not converted. -/

section SelfDualBa

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

/-- **152II** (dils.tex:3325, Definition): a sesquilinear form `B` on a
normed 𝒷-module is **bounded** (by `r`) when `‖B(x,y)‖ ≤ r ‖x‖ ‖y‖`. -/
def IsBoundedBSesq (r : ℝ) (B : X → X → 𝒷) : Prop :=
  IsBSesquilinear B ∧ ∀ x y : X, ‖B x y‖ ≤ r * ‖x‖ * ‖y‖

/-- **152V** (`hilbmod-sesquilinear-forms`, dils.tex:3343, Proposition):
on a self-dual Hilbert 𝒷-module every bounded 𝒷-sesquilinear form is
`⟨·, T ·⟩` for a unique adjointable bounded operator `T`. -/
theorem hilbmod_sesquilinear_forms [CompleteSpace X] (hX : SelfDual 𝒷 X)
    (r : ℝ) (B : X → X → 𝒷) (hB : IsBoundedBSesq r B) :
    ∃! T : X →L[ℂ] X, ModuleAdjointable 𝒷 ⇑T ∧
      ∀ x y : X, B x y = inner 𝒷 x (T y) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  obtain ⟨hsesq, hbd⟩ := hB
  -- only `SMul 𝒷 X` is assumed, so `1 • y = y` has to be derived
  have hone : ∀ y : X, (1 : 𝒷) • y = y := fun y =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      rw [CStarModule.inner_op_smul_right, one_mul]
  have hleft : ∀ (β : 𝒷) (x y : X), B (β • x) y = B x y * star β := fun β x y => by
    have h := hsesq.smul_op β 1 x y
    rwa [hone, one_mul] at h
  have hright : ∀ (b : 𝒷) (x y : X), B x (b • y) = b * B x y := fun b x y => by
    have h := hsesq.smul_op 1 b x y
    rwa [hone, star_one, mul_one] at h
  -- self-duality, packaged as a representation theorem for bounded 𝒷-linear
  -- functionals given by their components
  have hrep : ∀ (C : ℝ) (F : X → 𝒷), (∀ x x' : X, F (x + x') = F x + F x') →
      (∀ (c : ℂ) (x : X), F (c • x) = c • F x) →
      (∀ (b : 𝒷) (x : X), F (b • x) = b * F x) →
      (∀ x : X, ‖F x‖ ≤ C * ‖x‖) → ∃ t : X, ∀ x : X, F x = inner 𝒷 t x := by
    intro C F hadd hsmul hmod hbound
    exact hX { toFun := F, map_add' := hadd, map_smul' := hsmul } hmod ⟨C, hbound⟩
  -- (a) `x ↦ B(x,y)*` is bounded and 𝒷-linear, so `B(x,y) = ⟨x, t_y⟩`
  have hA : ∀ y : X, ∃ t : X, ∀ x : X, B x y = inner 𝒷 x t := by
    intro y
    obtain ⟨t, ht⟩ := hrep (r * ‖y‖) (fun x => star (B x y))
      (fun x x' => by rw [hsesq.add_left, star_add])
      (fun c x => by rw [hsesq.smul_left_complex, star_smul]; simp)
      (fun b x => by rw [hleft, star_mul, star_star])
      (fun x => by
        rw [norm_star]
        calc ‖B x y‖ ≤ r * ‖x‖ * ‖y‖ := hbd x y
          _ = r * ‖y‖ * ‖x‖ := by ring)
    exact ⟨t, fun x => by
      rw [← CStarModule.star_inner (A := 𝒷) t x, ← ht x, star_star]⟩
  -- (b) `x ↦ B(y,x)` is bounded and 𝒷-linear, so `B(y,x) = ⟨s_y, x⟩`
  have hBrep : ∀ y : X, ∃ s : X, ∀ x : X, B y x = inner 𝒷 s x := fun y =>
    hrep (r * ‖y‖) (fun x => B y x) (fun x x' => hsesq.add_right y x x')
      (fun c x => hsesq.smul_right_complex c y x) (fun b x => hright b y x)
      (fun x => by
        calc ‖B y x‖ ≤ r * ‖y‖ * ‖x‖ := hbd y x
          _ = r * ‖y‖ * ‖x‖ := rfl)
  choose T0 hT0 using hA
  choose S hS using hBrep
  -- `T0` is ℂ-linear, by definiteness of the inner product
  have hTadd : ∀ y y' : X, T0 (y + y') = T0 y + T0 y' := fun y y' =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      rw [← hT0, CStarModule.inner_add_right, ← hT0, ← hT0, hsesq.add_right]
  have hTsmul : ∀ (c : ℂ) (y : X), T0 (c • y) = c • T0 y := fun c y =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      rw [← hT0, CStarModule.inner_smul_right_complex, ← hT0,
        hsesq.smul_right_complex]
  -- `‖T0 x‖² = ‖⟨T0 x, T0 x⟩‖ = ‖B (T0 x, x)‖ ≤ r ‖T0 x‖ ‖x‖`
  set r' : ℝ := max r 0 with hr'
  have hr'0 : (0 : ℝ) ≤ r' := le_max_right _ _
  have hTbound : ∀ x : X, ‖T0 x‖ ≤ r' * ‖x‖ := by
    intro x
    have hsq : ‖T0 x‖ ^ 2 = ‖(inner 𝒷 (T0 x) (T0 x) : 𝒷)‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷) (x := T0 x),
        Real.sq_sqrt (norm_nonneg _)]
    have hle : ‖T0 x‖ ^ 2 ≤ r' * (‖T0 x‖ * ‖x‖) := by
      rw [hsq, ← hT0 x (T0 x)]
      calc ‖B (T0 x) x‖ ≤ r * ‖T0 x‖ * ‖x‖ := hbd _ _
        _ ≤ r' * (‖T0 x‖ * ‖x‖) := by
            have : r * (‖T0 x‖ * ‖x‖) ≤ r' * (‖T0 x‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            linarith [this, mul_assoc r ‖T0 x‖ ‖x‖]
    rcases eq_or_lt_of_le (norm_nonneg (T0 x)) with h0 | h0
    · rw [← h0]; positivity
    · nlinarith [norm_nonneg x]
  set Tl : X →ₗ[ℂ] X :=
    { toFun := T0, map_add' := hTadd, map_smul' := fun c y => hTsmul c y } with hTl
  refine ⟨Tl.mkContinuous r' hTbound, ⟨⟨S, fun x y => ?_⟩, fun x y => hT0 y x⟩,
    fun T' hT' => ?_⟩
  · change inner 𝒷 (T0 x) y = inner 𝒷 x (S y)
    rw [← CStarModule.star_inner (A := 𝒷) y (T0 x), ← hT0 x y, hS y x,
      CStarModule.star_inner]
  · ext y
    exact eq_of_inner_right_eq (𝒜 := 𝒷) fun x =>
      (hT'.2 x y).symm.trans (hT0 y x)

/-- **152VIII** (`hilbmod-adjoint-exists`, dils.tex:3388, Exercise): a
bounded 𝒷-linear map `T : X → Y` between Hilbert 𝒷-modules with `X` self
dual is adjointable. -/
theorem hilbmod_adjoint_exists [CompleteSpace X] [CompleteSpace Y]
    (hX : SelfDual 𝒷 X) (T : X →L[ℂ] Y)
    (hmod : ∀ (b : 𝒷) (x : X), T (b • x) = b • T x) :
    ∃ S : Y →L[ℂ] X, ModuleAdjointTo 𝒷 ⇑T ⇑S := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  let _ : NormedSpace ℂ Y := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  -- for each `y` the functional `τ_y = ⟨y, T ·⟩` is bounded and 𝒷-linear,
  -- so self-duality of `X` represents it as `⟨t, ·⟩`
  have hτ : ∀ y : Y, ∃ t : X, ∀ x : X, inner 𝒷 y (T x) = inner 𝒷 t x := by
    intro y
    refine hX { toFun := fun x => inner 𝒷 y (T x), map_add' := ?_, map_smul' := ?_ }
      (fun b x => ?_) ⟨‖y‖ * ‖T‖, fun x => ?_⟩
    · intro x x'
      simp [CStarModule.inner_add_right]
    · intro c x
      simp [CStarModule.inner_smul_right_complex]
    · show inner 𝒷 y (T (b • x)) = b * inner 𝒷 y (T x)
      rw [hmod, CStarModule.inner_op_smul_right]
    · show ‖inner 𝒷 y (T x)‖ ≤ ‖y‖ * ‖T‖ * ‖x‖
      calc ‖inner 𝒷 y (T x)‖ ≤ ‖y‖ * ‖T x‖ := CStarModule.norm_inner_le Y
        _ ≤ ‖y‖ * (‖T‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg y)
        _ = ‖y‖ * ‖T‖ * ‖x‖ := by ring
  choose S hS using hτ
  -- `S` is the adjoint of `T`
  have hadj : ∀ (x : X) (y : Y), inner 𝒷 (T x) y = inner 𝒷 x (S y) := by
    intro x y
    rw [← CStarModule.star_inner (A := 𝒷) y (T x), hS y x,
      CStarModule.star_inner]
  -- hence linear and bounded
  have hadd : ∀ y y' : Y, S (y + y') = S y + S y' := fun y y' =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      simp only [← hadj, CStarModule.inner_add_right]
  have hsmul : ∀ (c : ℂ) (y : Y), S (c • y) = c • S y := fun c y =>
    eq_of_inner_right_eq (𝒜 := 𝒷) fun x => by
      simp only [← hadj, CStarModule.inner_smul_right_complex]
  set Sl : Y →ₗ[ℂ] X :=
    { toFun := S, map_add' := hadd, map_smul' := fun c y => hsmul c y } with hSl
  have hpos : (0 : ℝ) < ‖T‖ + 1 := by positivity
  have hbound : ∀ y : Y, ‖Sl y‖ ≤ (‖T‖ + 1) * ‖y‖ := by
    refine (Theses.A.CStar.chilb_form_bounded (𝒜 := 𝒷) Sl (‖T‖ + 1) hpos).mpr ?_
    intro y x
    show ‖inner 𝒷 x (S y)‖ ≤ _
    rw [← hadj x y]
    calc ‖inner 𝒷 (T x) y‖ ≤ ‖T x‖ * ‖y‖ := CStarModule.norm_inner_le Y
      _ ≤ (‖T‖ + 1) * ‖x‖ * ‖y‖ := by
          have h1 : ‖T x‖ ≤ (‖T‖ + 1) * ‖x‖ := by
            have h2 := T.le_opNorm x
            have h3 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
            nlinarith
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
  exact ⟨Sl.mkContinuous (‖T‖ + 1) hbound, hadj⟩

end SelfDualBa

section FixedOnV

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

/-- **152IX** (`hilmod-fixed-on-V`, dils.tex:3394, Exercise), part 1: for a
self-dual completion `η : V → X`, the vector states `⟨η v, (·) η v⟩` are
order separating on `𝒷ᵃ(X)`: an adjointable `T` is positive iff
`⟨η v, T (η v)⟩ ≥ 0` for all `v ∈ V`. -/
theorem hilmod_fixed_on_V [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) (T : E.X →L[ℂ] E.X)
    (hT : ModuleAdjointable 𝒷 ⇑T) :
    IsPositiveOp 𝒷 T ↔ ∀ v : V, 0 ≤ inner 𝒷 (E.η v) (T (E.η v)) := by
  -- **144I** on both sides; the image of `η` is ultranorm dense, so the
  -- vector states it supplies already determine positivity
  refine ⟨fun h v => (hilbmod_ordersep T hT).mp h _, fun hv => ?_⟩
  refine (hilbmod_ordersep T hT).mpr
    (unDense_inner_nonneg (Set.range E.η) E.dense T
      (moduleAdjointable_linear (𝒜 := 𝒷) ⇑T hT).2.2 ?_)
  rintro _ ⟨v, rfl⟩
  exact hv v

/-- **152IX** (`hilmod-fixed-on-V`, dils.tex:3394, Exercise), part 2:
consequently adjointable operators agreeing on the vector states of the
dense image are equal: `S = T` iff `⟨η v, T (η v)⟩ = ⟨η v, S (η v)⟩` for
all `v ∈ V`. -/
theorem hilmod_fixed_on_V_eq [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) (T S : E.X →L[ℂ] E.X)
    (hT : ModuleAdjointable 𝒷 ⇑T) (hS : ModuleAdjointable 𝒷 ⇑S)
    (h : ∀ v : V, inner 𝒷 (E.η v) (T (E.η v)) =
      inner 𝒷 (E.η v) (S (E.η v))) :
    T = S := by
  set U : E.X →L[ℂ] E.X := T - S with hU
  obtain ⟨T', hT'⟩ := hT
  obtain ⟨S', hS'⟩ := hS
  -- `U = T - S` is adjointable, hence 𝒷-linear
  have hUadj : ModuleAdjointable 𝒷 ⇑U := by
    refine ⟨fun y => T' y - S' y, fun x y => ?_⟩
    change inner 𝒷 (T x - S x) y = inner 𝒷 x (T' y - S' y)
    rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right, hT' x y, hS' x y]
  obtain ⟨-, -, hUmod⟩ := moduleAdjointable_linear (𝒜 := 𝒷) ⇑U hUadj
  -- `U` is bounded as a module map, hence `‖U z‖_ω ≤ C ‖z‖_ω`
  set C : ℝ := ‖U‖ + 1 with hC
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hbdd : IsBoundedModuleMap (cstarBInner 𝒷 E.X) (cstarBInner 𝒷 E.X) C ⇑U :=
    { add := fun x y => map_add U x y
      smul_complex := fun c x => map_smul U c x
      smul := hUmod
      bound := fun x => by
        change Real.sqrt ‖(inner 𝒷 (U x) (U x) : 𝒷)‖
          ≤ C * Real.sqrt ‖(inner 𝒷 x x : 𝒷)‖
        rw [← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷),
          ← CStarModule.norm_eq_sqrt_norm_inner_self (A := 𝒷)]
        have := U.le_opNorm x
        have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
        nlinarith }
  have hUsem : ∀ (ω : NPFunctional 𝒷) (z : E.X),
      unSeminorm ω (inner 𝒷) (U z) ≤ C * unSeminorm ω (inner 𝒷) z := fun ω z =>
    unSeminorm_boundedModuleMap_le _ _ C hC0 _ hbdd ω z
  -- on the dense image `U` has vanishing diagonal
  have hdense : ∀ v : V, (inner 𝒷 (E.η v) (U (E.η v)) : 𝒷) = 0 := fun v => by
    change inner 𝒷 (E.η v) (T (E.η v) - S (E.η v)) = 0
    rw [CStarModule.inner_sub_right, h v, sub_self]
  -- hence everywhere, by ultranorm density and Cauchy-Schwarz for `‖·‖_ω`
  have hdiag : ∀ x : E.X, (inner 𝒷 x (U x) : 𝒷) = 0 := by
    intro x
    refine np_separating _ fun ω => ?_
    set M : ℝ := unSeminorm ω (inner 𝒷) x with hM
    set N : ℝ := unSeminorm ω (inner 𝒷) (U x) with hN
    have hM0 : (0 : ℝ) ≤ M := unSeminorm_nonneg _ _ _
    have hN0 : (0 : ℝ) ≤ N := unSeminorm_nonneg _ _ _
    have key : ∀ ε : ℝ, 0 < ε → ‖ω (inner 𝒷 x (U x))‖ ≤ ε * (N + (M + 1) * C) := by
      intro ε hε
      set ε' : ℝ := min ε 1 with hε'
      have hε'0 : 0 < ε' := lt_min hε one_pos
      obtain ⟨d, ⟨v, rfl⟩, hd⟩ :=
        E.dense x 1 (fun _ => ω) ε' hε'0
      have ht : unSeminorm ω (inner 𝒷) (x - E.η v) ≤ ε' := hd 0
      have ht0 : (0 : ℝ) ≤ unSeminorm ω (inner 𝒷) (x - E.η v) :=
        unSeminorm_nonneg _ _ _
      -- `⟨x,Ux⟩ = ⟨x-d, Ux⟩ + ⟨d, U(x-d)⟩ + ⟨d, Ud⟩`, and the last term is `0`
      have hsplit : (inner 𝒷 x (U x) : 𝒷)
          = inner 𝒷 (x - E.η v) (U x) + inner 𝒷 (E.η v) (U (x - E.η v))
            + inner 𝒷 (E.η v) (U (E.η v)) := by
        rw [map_sub U, CStarModule.inner_sub_right, CStarModule.inner_sub_left]
        abel
      have hadd : ω (inner 𝒷 (x - E.η v) (U x) + inner 𝒷 (E.η v) (U (x - E.η v)))
          = ω (inner 𝒷 (x - E.η v) (U x))
            + ω (inner 𝒷 (E.η v) (U (x - E.η v))) :=
        map_add ω.toPositiveLinearMap _ _
      rw [hsplit, hdense v, add_zero, hadd]
      -- the two Cauchy-Schwarz estimates
      have hcs1 : ‖ω (inner 𝒷 (x - E.η v) (U x))‖
          ≤ unSeminorm ω (inner 𝒷) (x - E.η v) * N :=
        unSeminorm_inner_le ω (cstarBInner 𝒷 E.X) _ _
      have hdM : unSeminorm ω (inner 𝒷) (E.η v) ≤ M + ε' := by
        have htri := unSeminorm_add_le ω (cstarBInner 𝒷 E.X) x (E.η v - x)
        simp only [show (cstarBInner 𝒷 E.X).inner = (inner 𝒷 : E.X → E.X → 𝒷)
          from rfl, add_sub_cancel] at htri
        have hneg : E.η v - x = -(x - E.η v) := by abel
        have hsymm : unSeminorm ω (inner 𝒷 : E.X → E.X → 𝒷) (E.η v - x)
            = unSeminorm ω (inner 𝒷) (x - E.η v) := by
          rw [unSeminorm, unSeminorm, hneg, CStarModule.inner_neg_left,
            CStarModule.inner_neg_right, neg_neg]
        rw [hsymm] at htri
        linarith [ht]
      have hcs2 : ‖ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖
          ≤ unSeminorm ω (inner 𝒷) (E.η v) * (C * unSeminorm ω (inner 𝒷) (x - E.η v)) := by
        refine (unSeminorm_inner_le ω (cstarBInner 𝒷 E.X) _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (hUsem ω _) (unSeminorm_nonneg _ _ _)
      have hεle : ε' ≤ ε := min_le_left _ _
      have hε1 : ε' ≤ 1 := min_le_right _ _
      have hdM0 : (0 : ℝ) ≤ unSeminorm ω (inner 𝒷) (E.η v) := unSeminorm_nonneg _ _ _
      have htε : unSeminorm ω (inner 𝒷) (x - E.η v) ≤ ε := ht.trans hεle
      have h1 : ‖ω (inner 𝒷 (x - E.η v) (U x))‖ ≤ ε * N :=
        hcs1.trans (mul_le_mul_of_nonneg_right htε hN0)
      have h2 : ‖ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖ ≤ ε * ((M + 1) * C) := by
        refine hcs2.trans ?_
        have hD : unSeminorm ω (inner 𝒷) (E.η v) ≤ M + 1 := by linarith
        have hCt : C * unSeminorm ω (inner 𝒷) (x - E.η v) ≤ C * ε :=
          mul_le_mul_of_nonneg_left htε hC0
        calc unSeminorm ω (inner 𝒷) (E.η v) * (C * unSeminorm ω (inner 𝒷) (x - E.η v))
            ≤ (M + 1) * (C * unSeminorm ω (inner 𝒷) (x - E.η v)) :=
              mul_le_mul_of_nonneg_right hD (by positivity)
          _ ≤ (M + 1) * (C * ε) := mul_le_mul_of_nonneg_left hCt (by linarith)
          _ = ε * ((M + 1) * C) := by ring
      calc ‖ω (inner 𝒷 (x - E.η v) (U x)) + ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖
          ≤ ‖ω (inner 𝒷 (x - E.η v) (U x))‖
              + ‖ω (inner 𝒷 (E.η v) (U (x - E.η v)))‖ := norm_add_le _ _
        _ ≤ ε * (N + (M + 1) * C) := by linarith
    -- letting `ε ↓ 0`
    by_contra hne
    have hpos : 0 < ‖ω (inner 𝒷 x (U x))‖ := norm_pos_iff.mpr hne
    have hK : (0 : ℝ) < N + (M + 1) * C + 1 := by nlinarith
    have := key (‖ω (inner 𝒷 x (U x))‖ / (2 * (N + (M + 1) * C + 1)))
      (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  -- polarization: a sesquilinear form with vanishing diagonal vanishes
  have hsesq : IsBSesquilinear (fun x y : E.X => (inner 𝒷 x (U y) : 𝒷)) :=
    { add_left := fun x y z => by
        simp only [CStarModule.inner_add_left]
      add_right := fun x y z => by
        simp only [map_add U, CStarModule.inner_add_right]
      smul_op := fun β b x y => by
        simp only [hUmod, CStarModule.inner_op_smul_left,
          CStarModule.inner_op_smul_right, mul_assoc]
      smul_left_complex := fun c x y => by
        simp only [CStarModule.inner_smul_left_complex]
        rfl
      smul_right_complex := fun c x y => by
        simp only [map_smul U, CStarModule.inner_smul_right_complex] }
  have hzero : ∀ x y : E.X, (inner 𝒷 x (U y) : 𝒷) = 0 := by
    intro x y
    rw [hilbmod_polarization _ hsesq x y]
    simp only [hdiag, smul_zero, Finset.sum_const_zero]
  have hUz : U = 0 := by
    ext y
    refine eq_of_inner_right_eq (𝒜 := 𝒷) fun x => ?_
    rw [hzero x y]
    simp
  rwa [hU, sub_eq_zero] at hUz

end FixedOnV

section BaVN

variable {𝒷 : Type u} {X Y : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [NormedAddCommGroup X] [Module ℂ X] [SMul 𝒷 X] [CStarModule 𝒷 X]
  [NormedAddCommGroup Y] [Module ℂ Y] [SMul 𝒷 Y] [CStarModule 𝒷 Y]

/-- Positivity in `𝒷ᵃ(X)` from the vector states: if `⟨x, Zx⟩ ≥ 0` for all
`x`, then `0 ≤ Z` in the C*-order of `𝒷ᵃ(X)`.  This is **144I**
`hilbmod_ordersep` transported from `IsPositiveOp` to the type `Ba 𝒷 X`
(adjoints being unique, `R* = R'` and so `Z = R* R ≥ 0`). -/
private theorem ba_nonneg_of_vector [CompleteSpace X] (Z : Ba 𝒷 X)
    (h : ∀ x : X, 0 ≤ inner 𝒷 x (Z.1 x)) : 0 ≤ Z := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  obtain ⟨R, R', hRR', hZ⟩ := (hilbmod_ordersep Z.1 Z.2).mpr h
  let r : Ba 𝒷 X := ⟨R, ⟨R', hRR'⟩⟩
  have hstar : ((star r : Ba 𝒷 X)).1 = R' := by
    have h1 : ModuleAdjointTo 𝒷 (⇑R : X → X) ⇑((star r : Ba 𝒷 X)).1 :=
      baSubalgebra_star_spec r
    exact DFunLike.coe_injective
      (moduleAdjointTo_unique (𝒜 := 𝒷) (⇑R) _ _ h1 hRR')
  have hzz : Z = (star r * r : Ba 𝒷 X) := by
    refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
    change Z.1 x = ((star r : Ba 𝒷 X)).1 ((r : Ba 𝒷 X).1 x)
    rw [hZ, hstar]
    rfl
  rw [hzz]
  exact star_mul_self_nonneg r


/-! ### The proof of **152X**

The thesis's argument (**152XI**–**152XIII**, dils.tex:3413–3505) verbatim:
for a bounded directed net `(T_α)` of self-adjoint elements of `𝒷ᵃ(X)` the
vector forms `⟨x, T_α x⟩` form a bounded directed net in `𝒷`, which
converges ultrastrongly to its supremum by **44XIV** `vna_supremum_uslimit`;
polarization (**142IX**) turns this into an ultrastrong limit
`B(x,y) = uslim_α ⟨x, T_α y⟩` for all `x, y`, which is 𝒷-sesquilinear
because addition and multiplication by a fixed element are ultrastrongly
continuous (**45IV** `mult_uws_cont`) and bounded; **152V**
`hilbmod_sesquilinear_forms` then represents it as `⟨x, Ty⟩` for a unique
`T ∈ 𝒷ᵃ(X)`, and `T` is the supremum.  The vector states are separating by
**144I** and normal by the same computation, which is **152XIII**.

Two deviations from the text, both in the *bound* on `B`.  The thesis picks
`r` with `‖T_α‖ ≤ r` for all `α`; a bounded directed set need not be
norm-bounded (its elements are only bounded *above*), so we bound `B(x,x)`
by order instead — `⟨x, d₀x⟩ ≤ B(x,x) ≤ ⟨x, ub x⟩` — which needs no such
`r`.  And where the thesis derives `‖B(x,y)‖ ≤ r‖x‖‖y‖ ` from
`usconv` and the module Cauchy–Schwarz inequality, we get
`‖B(x,y)‖ ≤ r₀(‖x‖+‖y‖)²` from polarization and then rescale
`x ↦ tx`, `y ↦ t⁻¹y` (which leaves `B(x,y)` fixed) with
`t = (‖y‖/‖x‖)^{1/2}`.  This avoids `usconv`, whose Lean form would need
the ultraweak closedness of norm balls (**44XI**.3 `vn_positive_basic_3`,
still `sorry` in `Theses.A.VN`). -/

/-- `0 ≤ Z` in `𝒷ᵃ(X)` iff every vector form `⟨x, Zx⟩` is positive: the
two halves of **144I** `hilbmod_ordersep`, transported to `Ba 𝒷 X`. -/
theorem ba_nonneg_iff [CompleteSpace X] (Z : Ba 𝒷 X) :
    0 ≤ Z ↔ ∀ x : X, 0 ≤ (inner 𝒷 x (Z.1 x) : 𝒷) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  refine ⟨fun h x => ?_, ba_nonneg_of_vector Z⟩
  have hsq : (0 : Ba 𝒷 X) ≤ (CFC.sqrt Z : Ba 𝒷 X) := CFC.sqrt_nonneg Z
  have hsa : star (CFC.sqrt Z : Ba 𝒷 X) = (CFC.sqrt Z : Ba 𝒷 X) :=
    IsSelfAdjoint.of_nonneg hsq
  have hzz : Z = star (CFC.sqrt Z : Ba 𝒷 X) * (CFC.sqrt Z : Ba 𝒷 X) := by
    rw [hsa, CFC.sqrt_mul_sqrt_self Z h]
  have hkey :=
    baSubalgebra_inner_star_mul_self (𝒷 := 𝒷) (X := X) (CFC.sqrt Z : Ba 𝒷 X) x
  rw [hzz]
  exact hkey ▸ CStarModule.inner_self_nonneg

/-- The vector form of a self-adjoint element of `𝒷ᵃ(X)` is self-adjoint. -/
theorem ba_inner_isSelfAdjoint [CompleteSpace X] (x : X) (Z : Ba 𝒷 X)
    (hZ : IsSelfAdjoint Z) : IsSelfAdjoint (inner 𝒷 x (Z.1 x) : 𝒷) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  have h : ModuleAdjointTo 𝒷 (⇑(Z.1)) (⇑((star Z : Ba 𝒷 X).1)) :=
    baSubalgebra_star_spec (𝒷 := 𝒷) (X := X) Z
  have hz : (star Z : Ba 𝒷 X).1 = Z.1 := congrArg Subtype.val hZ.star_eq
  change star (inner 𝒷 x (Z.1 x) : 𝒷) = _
  rw [CStarModule.star_inner, h x x, hz]

/-- The vector forms are monotone (**144I** again). -/
theorem ba_inner_mono [CompleteSpace X] (x : X) {Z W : Ba 𝒷 X} (h : Z ≤ W) :
    (inner 𝒷 x (Z.1 x) : 𝒷) ≤ inner 𝒷 x (W.1 x) := by
  have hv := (ba_nonneg_iff _).mp (sub_nonneg.mpr h) x
  have he : (W - Z).1 x = W.1 x - Z.1 x := rfl
  rw [he, CStarModule.inner_sub_right, sub_nonneg] at hv
  exact hv

/-- The vector form `⟨x, Z x⟩` of a self-adjoint element of `𝒷ᵃ(X)`, as an
element of the self-adjoint part of `𝒷`. -/
def baVec [CompleteSpace X] (x : X) (Z : selfAdjoint (Ba 𝒷 X)) : selfAdjoint 𝒷 :=
  ⟨inner 𝒷 x ((Z : Ba 𝒷 X).1 x), ba_inner_isSelfAdjoint x _ Z.2⟩

@[simp] theorem baVec_coe [CompleteSpace X] (x : X) (Z : selfAdjoint (Ba 𝒷 X)) :
    (baVec x Z : 𝒷) = inner 𝒷 x ((Z : Ba 𝒷 X).1 x) := rfl

theorem baVec_mono [CompleteSpace X] (x : X) {Z W : selfAdjoint (Ba 𝒷 X)}
    (h : Z ≤ W) : baVec x Z ≤ baVec x W :=
  ba_inner_mono x (Subtype.coe_le_coe.mpr h)

theorem baVec_image_directed [CompleteSpace X] (x : X)
    {D : Set (selfAdjoint (Ba 𝒷 X))} (hdir : DirectedOn (· ≤ ·) D) :
    DirectedOn (· ≤ ·) (baVec x '' D) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
  exact ⟨baVec x c, ⟨c, hc, rfl⟩, baVec_mono x hac, baVec_mono x hbc⟩

/-- **142VIII** (dils.tex:1487, Example): `⟨·, Z·⟩` is a 𝒷-sesquilinear
form for every `Z ∈ 𝒷ᵃ(X)`. -/
theorem ba_isBSesquilinear [CompleteSpace X] (Z : Ba 𝒷 X) :
    IsBSesquilinear (fun x y : X => (inner 𝒷 x (Z.1 y) : 𝒷)) := by
  have hmod := (moduleAdjointable_linear (𝒜 := 𝒷) ⇑(Z.1) Z.2).2.2
  exact
    { add_left := fun x y z => by simp only [CStarModule.inner_add_left]
      add_right := fun x y z => by
        simp only [map_add Z.1, CStarModule.inner_add_right]
      smul_op := fun β b x y => by
        simp only [hmod, CStarModule.inner_op_smul_left,
          CStarModule.inner_op_smul_right, mul_assoc]
      smul_left_complex := fun c x y => by
        simp only [CStarModule.inner_smul_left_complex]
        rfl
      smul_right_complex := fun c x y => by
        simp only [map_smul Z.1, CStarModule.inner_smul_right_complex] }

/-! Elementary stability properties of ultrastrong limits in `𝒷`.  These
belong in `Theses.A.VN.Basic` next to `usTendsto_iff` and **45IV**; they are
here because that file is currently frozen. -/

private theorem usTendsto_add' {ι : Type*} {l : Filter ι} {f g : ι → 𝒷} {a b : 𝒷}
    (hf : USTendsto f l a) (hg : USTendsto g l b) :
    USTendsto (fun i => f i + g i) l (a + b) := by
  rw [usTendsto_iff] at hf hg ⊢
  intro ω
  have h := (hf ω).add (hg ω)
  rw [add_zero] at h
  refine squeeze_zero (fun i => omegaNorm_nonneg _ _) (fun i => ?_) h
  have he : f i + g i - (a + b) = (f i - a) + (g i - b) := by abel
  rw [he]
  exact omegaNorm_add_le ω _ _

private theorem usTendsto_mul_left' [VonNeumannAlgebra 𝒷] {ι : Type*}
    {l : Filter ι} {f : ι → 𝒷} {a : 𝒷} (b : 𝒷) (hf : USTendsto f l a) :
    USTendsto (fun i => b * f i) l (b * a) :=
  Filter.Tendsto.comp
    (@Continuous.tendsto 𝒷 𝒷 (ultrastrong 𝒷) (ultrastrong 𝒷) _
      (mult_uws_cont b).2.2.1 a) hf

private theorem usTendsto_mul_right' [VonNeumannAlgebra 𝒷] {ι : Type*}
    {l : Filter ι} {f : ι → 𝒷} {a : 𝒷} (b : 𝒷) (hf : USTendsto f l a) :
    USTendsto (fun i => f i * b) l (a * b) :=
  Filter.Tendsto.comp
    (@Continuous.tendsto 𝒷 𝒷 (ultrastrong 𝒷) (ultrastrong 𝒷) _
      (mult_uws_cont b).2.2.2 a) hf

private theorem usTendsto_smul' [VonNeumannAlgebra 𝒷] {ι : Type*} {l : Filter ι}
    {f : ι → 𝒷} {a : 𝒷} (c : ℂ) (hf : USTendsto f l a) :
    USTendsto (fun i => c • f i) l (c • a) := by
  have h := usTendsto_mul_left' (algebraMap ℂ 𝒷 c) hf
  simpa only [← Algebra.smul_def] using h

set_option linter.unusedSectionVars false in
private theorem usTendsto_const' {ι : Type*} {l : Filter ι} (a : 𝒷) :
    USTendsto (fun _ : ι => a) l a :=
  @tendsto_const_nhds 𝒷 (ultrastrong 𝒷) ι a l

private theorem usTendsto_sum' {ι : Type*} {l : Filter ι} {κ : Type*}
    (s : Finset κ) (f : κ → ι → 𝒷) (a : κ → 𝒷)
    (hf : ∀ k ∈ s, USTendsto (f k) l (a k)) :
    USTendsto (fun i => ∑ k ∈ s, f k i) l (∑ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using usTendsto_const' (ι := ι) (l := l) (0 : 𝒷)
  | insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      exact usTendsto_add' (hf k (Finset.mem_insert_self _ _))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Ultrastrong limits are unique: the ultrastrong topology is Hausdorff by
**44XI**.1 `vn_positive_basic_1`. -/
private theorem usTendsto_unique' [VonNeumannAlgebra 𝒷] {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → 𝒷} {a b : 𝒷}
    (ha : USTendsto f l a) (hb : USTendsto f l b) : a = b :=
  @tendsto_nhds_unique 𝒷 ι (ultrastrong 𝒷) (vn_positive_basic_1 (A := 𝒷)).2
    f l a b _ ha hb

set_option maxHeartbeats 1000000 in
-- the six stages of the proof in one declaration; see the note above
/-- **152XII** (dils.tex:3417, "bounded order completeness"): a nonempty
bounded directed set of self-adjoint elements of `𝒷ᵃ(X)` has a supremum, and
— the extra clause **152XIII** needs — its vector forms compute it:
`⟨x, (⋁D) x⟩ = ⋁_{d ∈ D} ⟨x, d x⟩`. -/
theorem ba_isLUB [VonNeumannAlgebra 𝒷] [CompleteSpace X] (hX : SelfDual 𝒷 X)
    (D : Set (selfAdjoint (Ba 𝒷 X))) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) :
    ∃ s : selfAdjoint (Ba 𝒷 X), IsLUB D s ∧
      ∀ x : X, IsLUB (baVec x '' D) (baVec x s) := by
  classical
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  obtain ⟨d₀, hd₀⟩ := hne
  obtain ⟨ub, hub⟩ := hbdd
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  -- (1) the vector sets and their suprema
  have hDvh : ∀ x : X, (baVec x '' D).Nonempty ∧ DirectedOn (· ≤ ·) (baVec x '' D) ∧
      BddAbove (baVec x '' D) := by
    intro x
    refine ⟨⟨baVec x d₀, ⟨d₀, hd₀, rfl⟩⟩, baVec_image_directed x hdir, ⟨baVec x ub, ?_⟩⟩
    rintro _ ⟨a, ha, rfl⟩
    exact baVec_mono x (hub ha)
  set q : X → selfAdjoint 𝒷 := fun x => dirSup (baVec x '' D) (hDvh x) with hqdef
  have hqlub : ∀ x : X, IsLUB (baVec x '' D) (q x) := fun x => isLUB_dirSup _ _
  -- (2) **44XIV**: the vector nets converge ultrastrongly to their suprema
  have hnet : ∀ x : X, USTendsto (fun d : D => (baVec x d.1 : 𝒷)) atTop (q x : 𝒷) := by
    intro x
    have hmap : Tendsto
        (fun d : D => (⟨baVec x d.1, ⟨d.1, d.2, rfl⟩⟩ : ↥(baVec x '' D))) atTop atTop := by
      refine Filter.tendsto_atTop.mpr fun b => ?_
      obtain ⟨e, he, hbe⟩ := b.2
      filter_upwards [Filter.mem_atTop (⟨e, he⟩ : D)] with d hd
      change (b : selfAdjoint 𝒷) ≤ baVec x d.1
      exact hbe ▸ baVec_mono x hd
    exact (vna_supremum_uslimit (baVec x '' D) (hDvh x)).comp hmap
  -- (3) the form `B(x,y) = uslim_α ⟨x, T_α y⟩`, defined by polarization
  set Bf : X → X → 𝒷 := fun x y =>
    (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4,
      Complex.I ^ k • (q (Complex.I ^ k • x + y) : 𝒷) with hBfdef
  have hBlim : ∀ x y : X,
      USTendsto (fun d : D => (inner 𝒷 x ((d.1 : Ba 𝒷 X).1 y) : 𝒷)) atTop (Bf x y) := by
    intro x y
    have hpol : ∀ d : D, (inner 𝒷 x ((d.1 : Ba 𝒷 X).1 y) : 𝒷)
        = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4,
            Complex.I ^ k • (baVec (Complex.I ^ k • x + y) d.1 : 𝒷) :=
      fun d => hilbmod_polarization _ (ba_isBSesquilinear (d.1 : Ba 𝒷 X)) x y
    simp only [hpol]
    exact usTendsto_smul' _
      (usTendsto_sum' _ _ _ fun k _ => usTendsto_smul' _ (hnet _))
  have hdiag : ∀ x : X, Bf x x = (q x : 𝒷) :=
    fun x => usTendsto_unique' (hBlim x x) (hnet x)
  -- (4) `Bf` is 𝒷-sesquilinear, by **45IV** and uniqueness of ultrastrong limits
  have hsesq : IsBSesquilinear Bf := by
    constructor
    · intro x y z
      have hrw : ∀ d : D, (inner 𝒷 (x + y) ((d.1 : Ba 𝒷 X).1 z) : 𝒷)
          = inner 𝒷 x ((d.1 : Ba 𝒷 X).1 z) + inner 𝒷 y ((d.1 : Ba 𝒷 X).1 z) :=
        fun d => (ba_isBSesquilinear _).add_left x y z
      have h := hBlim (x + y) z
      simp only [hrw] at h
      exact usTendsto_unique' h (usTendsto_add' (hBlim x z) (hBlim y z))
    · intro x y z
      have hrw : ∀ d : D, (inner 𝒷 x ((d.1 : Ba 𝒷 X).1 (y + z)) : 𝒷)
          = inner 𝒷 x ((d.1 : Ba 𝒷 X).1 y) + inner 𝒷 x ((d.1 : Ba 𝒷 X).1 z) :=
        fun d => (ba_isBSesquilinear _).add_right x y z
      have h := hBlim x (y + z)
      simp only [hrw] at h
      exact usTendsto_unique' h (usTendsto_add' (hBlim x y) (hBlim x z))
    · intro β b x y
      have hrw : ∀ d : D, (inner 𝒷 (β • x) ((d.1 : Ba 𝒷 X).1 (b • y)) : 𝒷)
          = b * inner 𝒷 x ((d.1 : Ba 𝒷 X).1 y) * star β :=
        fun d => (ba_isBSesquilinear _).smul_op β b x y
      have h := hBlim (β • x) (b • y)
      simp only [hrw] at h
      exact usTendsto_unique' h
        (usTendsto_mul_right' (star β) (usTendsto_mul_left' b (hBlim x y)))
    · intro c x y
      have hrw : ∀ d : D, (inner 𝒷 (c • x) ((d.1 : Ba 𝒷 X).1 y) : 𝒷)
          = starRingEnd ℂ c • inner 𝒷 x ((d.1 : Ba 𝒷 X).1 y) :=
        fun d => (ba_isBSesquilinear _).smul_left_complex c x y
      have h := hBlim (c • x) y
      simp only [hrw] at h
      exact usTendsto_unique' h (usTendsto_smul' _ (hBlim x y))
    · intro c x y
      have hrw : ∀ d : D, (inner 𝒷 x ((d.1 : Ba 𝒷 X).1 (c • y)) : 𝒷)
          = c • inner 𝒷 x ((d.1 : Ba 𝒷 X).1 y) :=
        fun d => (ba_isBSesquilinear _).smul_right_complex c x y
      have h := hBlim x (c • y)
      simp only [hrw] at h
      exact usTendsto_unique' h (usTendsto_smul' _ (hBlim x y))
  -- (5) `Bf` is bounded
  have hCS : ∀ (x : X) (Z : Ba 𝒷 X),
      ‖(inner 𝒷 x (Z.1 x) : 𝒷)‖ ≤ ‖Z.1‖ * ‖x‖ * ‖x‖ := by
    intro x Z
    calc ‖(inner 𝒷 x (Z.1 x) : 𝒷)‖ ≤ ‖x‖ * ‖Z.1 x‖ := CStarModule.norm_inner_le X
      _ ≤ ‖x‖ * (‖Z.1‖ * ‖x‖) := by
          gcongr
          exact Z.1.le_opNorm x
      _ = ‖Z.1‖ * ‖x‖ * ‖x‖ := by ring
  set r₀ : ℝ := ‖((ub : Ba 𝒷 X) - (d₀ : Ba 𝒷 X)).1‖ + ‖(d₀ : Ba 𝒷 X).1‖ with hr₀def
  have hr₀0 : (0 : ℝ) ≤ r₀ := by positivity
  have hqbound : ∀ x : X, ‖(q x : 𝒷)‖ ≤ r₀ * (‖x‖ * ‖x‖) := by
    intro x
    have h1 : (inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x) : 𝒷) ≤ (q x : 𝒷) :=
      Subtype.coe_le_coe.mpr ((hqlub x).1 ⟨d₀, hd₀, rfl⟩)
    have h2 : (q x : 𝒷) ≤ inner 𝒷 x ((ub : Ba 𝒷 X).1 x) :=
      Subtype.coe_le_coe.mpr
        ((hqlub x).2 (by rintro _ ⟨a, ha, rfl⟩; exact baVec_mono x (hub ha)))
    have hdiff : (inner 𝒷 x ((ub : Ba 𝒷 X).1 x) : 𝒷) - inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x)
        = inner 𝒷 x (((ub : Ba 𝒷 X) - (d₀ : Ba 𝒷 X)).1 x) := by
      change _ = inner 𝒷 x ((ub : Ba 𝒷 X).1 x - (d₀ : Ba 𝒷 X).1 x)
      rw [CStarModule.inner_sub_right]
    have hn : (0 : 𝒷) ≤ (q x : 𝒷) - inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x) := sub_nonneg.mpr h1
    have hle : (q x : 𝒷) - inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x)
        ≤ inner 𝒷 x (((ub : Ba 𝒷 X) - (d₀ : Ba 𝒷 X)).1 x) := by
      rw [← hdiff]
      exact sub_le_sub_right h2 _
    have hnorm1 := CStarAlgebra.norm_le_norm_of_nonneg_of_le hn hle
    have hnorm2 := hCS x ((ub : Ba 𝒷 X) - (d₀ : Ba 𝒷 X))
    have hnorm3 := hCS x (d₀ : Ba 𝒷 X)
    have htri : ‖(q x : 𝒷)‖
        ≤ ‖(q x : 𝒷) - inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x)‖
            + ‖(inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x) : 𝒷)‖ := by
      simpa using norm_add_le ((q x : 𝒷) - inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x))
        (inner 𝒷 x ((d₀ : Ba 𝒷 X).1 x))
    rw [hr₀def]
    nlinarith [htri, hnorm1, hnorm2, hnorm3]
  have hBbound0 : ∀ x y : X, ‖Bf x y‖ ≤ r₀ * ((‖x‖ + ‖y‖) * (‖x‖ + ‖y‖)) := by
    intro x y
    have hnorm : ∀ k : ℕ,
        ‖Complex.I ^ k • (q (Complex.I ^ k • x + y) : 𝒷)‖
          ≤ r₀ * ((‖x‖ + ‖y‖) * (‖x‖ + ‖y‖)) := by
      intro k
      rw [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      refine (hqbound _).trans ?_
      have hle : ‖Complex.I ^ k • x + y‖ ≤ ‖x‖ + ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have h0 : (0 : ℝ) ≤ ‖Complex.I ^ k • x + y‖ := norm_nonneg _
      have hmul := mul_le_mul hle hle h0 (by positivity : (0 : ℝ) ≤ ‖x‖ + ‖y‖)
      exact mul_le_mul_of_nonneg_left hmul hr₀0
    have hsum : ‖∑ k ∈ Finset.range 4, Complex.I ^ k • (q (Complex.I ^ k • x + y) : 𝒷)‖
        ≤ 4 * (r₀ * ((‖x‖ + ‖y‖) * (‖x‖ + ‖y‖))) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Finset.range 4, ‖Complex.I ^ k • (q (Complex.I ^ k • x + y) : 𝒷)‖
          ≤ ∑ _k ∈ Finset.range 4, r₀ * ((‖x‖ + ‖y‖) * (‖x‖ + ‖y‖)) :=
            Finset.sum_le_sum fun k _ => hnorm k
        _ = 4 * (r₀ * ((‖x‖ + ‖y‖) * (‖x‖ + ‖y‖))) := by
            simp [Finset.sum_const]
    have hBeq : Bf x y = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4,
        Complex.I ^ k • (q (Complex.I ^ k • x + y) : 𝒷) := rfl
    rw [hBeq, norm_smul]
    have h4 : ‖(4 : ℂ)⁻¹‖ = 1 / 4 := by norm_num
    rw [h4]
    nlinarith [hsum]
  have hzero_left : ∀ y : X, Bf 0 y = 0 := by
    intro y
    have h := hsesq.add_left 0 0 y
    rw [add_zero] at h
    have h2 := congrArg (fun z : 𝒷 => z - Bf 0 y) h
    simpa using h2.symm
  have hzero_right : ∀ x : X, Bf x 0 = 0 := by
    intro x
    have h := hsesq.add_right x 0 0
    rw [add_zero] at h
    have h2 := congrArg (fun z : 𝒷 => z - Bf x 0) h
    simpa using h2.symm
  have hBbound : ∀ x y : X, ‖Bf x y‖ ≤ (4 * r₀) * ‖x‖ * ‖y‖ := by
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simp [hzero_left]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hzero_right]
    have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
    set sx : ℝ := Real.sqrt ‖x‖ with hsx
    set sy : ℝ := Real.sqrt ‖y‖ with hsy
    have hsx0 : 0 < sx := Real.sqrt_pos.mpr hx0
    have hsy0 : 0 < sy := Real.sqrt_pos.mpr hy0
    have hsx2 : sx * sx = ‖x‖ := Real.mul_self_sqrt hx0.le
    have hsy2 : sy * sy = ‖y‖ := Real.mul_self_sqrt hy0.le
    set t : ℝ := sy / sx with ht
    have ht0 : 0 < t := div_pos hsy0 hsx0
    have hhom : Bf ((t : ℂ) • x) (((t : ℂ))⁻¹ • y) = Bf x y := by
      rw [hsesq.smul_left_complex, hsesq.smul_right_complex, smul_smul,
        Complex.conj_ofReal]
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      rw [mul_inv_cancel₀ htne, one_smul]
    have hnx : ‖(t : ℂ) • x‖ = t * ‖x‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hny : ‖((t : ℂ))⁻¹ • y‖ = t⁻¹ * ‖y‖ := by
      rw [norm_smul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr ht0)]
    have hkey := hBbound0 ((t : ℂ) • x) (((t : ℂ))⁻¹ • y)
    rw [hhom, hnx, hny] at hkey
    have hcalc : t * ‖x‖ + t⁻¹ * ‖y‖ = 2 * (sx * sy) := by
      rw [ht, ← hsx2, ← hsy2]
      field_simp
      ring
    rw [hcalc] at hkey
    refine hkey.trans (le_of_eq ?_)
    rw [← hsx2, ← hsy2]
    ring
  -- (6) **152V**: the representing operator, and it is the supremum
  obtain ⟨T, ⟨hTadj, hTrep⟩, -⟩ :=
    hilbmod_sesquilinear_forms hX (4 * r₀) Bf ⟨hsesq, hBbound⟩
  set s : Ba 𝒷 X := ⟨T, hTadj⟩ with hsdef
  have hsvec : ∀ x : X, (inner 𝒷 x (s.1 x) : 𝒷) = (q x : 𝒷) := by
    intro x
    rw [hsdef]
    change (inner 𝒷 x (T x) : 𝒷) = _
    rw [← hTrep x x, hdiag x]
  have hub' : ∀ d ∈ D, (d : Ba 𝒷 X) ≤ s := by
    intro d hd
    rw [← sub_nonneg]
    refine (ba_nonneg_iff _).mpr fun x => ?_
    have he : (s - (d : Ba 𝒷 X)).1 x = s.1 x - (d : Ba 𝒷 X).1 x := rfl
    rw [he, CStarModule.inner_sub_right, sub_nonneg, hsvec x]
    exact Subtype.coe_le_coe.mpr ((hqlub x).1 ⟨d, hd, rfl⟩)
  have hsa : IsSelfAdjoint s := by
    have h0 : (0 : Ba 𝒷 X) ≤ s - (d₀ : Ba 𝒷 X) := sub_nonneg.mpr (hub' d₀ hd₀)
    have h1 : IsSelfAdjoint (s - (d₀ : Ba 𝒷 X)) := IsSelfAdjoint.of_nonneg h0
    have h2 : s = (s - (d₀ : Ba 𝒷 X)) + (d₀ : Ba 𝒷 X) := by abel
    rw [h2]
    exact h1.add d₀.2
  refine ⟨⟨s, hsa⟩, ⟨fun d hd => ?_, fun c hc => ?_⟩, fun x => ?_⟩
  · exact Subtype.coe_le_coe.mp (hub' d hd)
  · refine Subtype.coe_le_coe.mp ?_
    rw [← sub_nonneg]
    refine (ba_nonneg_iff _).mpr fun x => ?_
    have he : ((c : Ba 𝒷 X) - s).1 x = (c : Ba 𝒷 X).1 x - s.1 x := rfl
    rw [he, CStarModule.inner_sub_right, sub_nonneg, hsvec x]
    exact Subtype.coe_le_coe.mpr ((hqlub x).2 (by
      rintro _ ⟨a, ha, rfl⟩
      exact baVec_mono x (hc ha)))
  · have hb : baVec x ⟨s, hsa⟩ = q x := Subtype.ext (hsvec x)
    rw [hb]
    exact hqlub x

/-- **152XII**, restated: the supremum of a bounded directed set in
`𝒷ᵃ(X)` is computed by the vector forms. -/
theorem ba_isLUB_vec [VonNeumannAlgebra 𝒷] [CompleteSpace X] (hX : SelfDual 𝒷 X)
    {D : Set (selfAdjoint (Ba 𝒷 X))} {s : selfAdjoint (Ba 𝒷 X)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) (x : X) :
    IsLUB (baVec x '' D) (baVec x s) := by
  obtain ⟨s', hs'lub, hs'vec⟩ := ba_isLUB hX D hne hdir ⟨s, hlub.1⟩
  exact (hlub.unique hs'lub) ▸ hs'vec x

set_option maxHeartbeats 1000000 in
-- as for `ba_isLUB`: instance search through `Ba 𝒷 X` is slow
/-- **152XIII** (`hilbmod-vecstates-normal`, dils.tex:3480): the vector
states are normal, i.e. `Z ↦ ω⟨x, Zx⟩` is an np-functional of `𝒷ᵃ(X)` for
every `x ∈ X` and every np-functional `ω` of `𝒷`. -/
noncomputable def baVecNP [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    (hX : SelfDual 𝒷 X) (x : X) (ω : NPFunctional 𝒷) : NPFunctional (Ba 𝒷 X) where
  toPositiveLinearMap :=
    { toFun := fun Z => ω (inner 𝒷 x (Z.1 x))
      map_add' := fun Z W => by
        change ω (inner 𝒷 x ((Z + W).1 x)) = _
        rw [show ((Z + W).1 x) = Z.1 x + W.1 x from rfl, CStarModule.inner_add_right]
        exact map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c Z => by
        change ω (inner 𝒷 x ((c • Z).1 x)) = _
        rw [show ((c • Z).1 x) = c • Z.1 x from rfl,
          CStarModule.inner_smul_right_complex]
        exact map_smul ω.toPositiveLinearMap _ _
      monotone' := fun Z W h => ω.toPositiveLinearMap.monotone (ba_inner_mono x h) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h := ω.preservesDirSups' (baVec x '' D) (baVec x s) (hne.image _)
      (baVec_image_directed x hdir) (ba_isLUB_vec hX hne hdir hlub x)
    rw [← Set.image_comp] at h
    exact h

@[simp] theorem baVecNP_apply [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    (hX : SelfDual 𝒷 X) (x : X) (ω : NPFunctional 𝒷) (Z : Ba 𝒷 X) :
    baVecNP hX x ω Z = ω (inner 𝒷 x (Z.1 x)) := rfl

set_option maxHeartbeats 1000000 in
-- elaborating the two `VonNeumannAlgebra` fields against the subtype `Ba 𝒷 X`
-- (whose C*-structure is that of `baSubalgebra`) is heartbeat-hungry
/-- **152X** (dils.tex:3409, Theorem): for a self-dual Hilbert 𝒷-module
`X` over a von Neumann algebra `𝒷`, the algebra `𝒷ᵃ(X)` is a von Neumann
algebra (bounded directed suprema exist and the vector states are
separating normal states). -/
theorem ba_vonNeumannAlgebra [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    (hX : SelfDual 𝒷 X) : VonNeumannAlgebra (Ba 𝒷 X) where
  isLUB_of_bddAbove_directed D hne hdir hbdd :=
    let ⟨s, hs, _⟩ := ba_isLUB hX D hne hdir hbdd
    ⟨s, hs⟩
  np_faithful a ha hzero := by
    -- **144I**: the vector states are separating, and **152XIII** they are normal
    have hvec : ∀ x : X, (inner 𝒷 x (a.1 x) : 𝒷) = 0 := fun x =>
      VonNeumannAlgebra.np_faithful _ ((ba_nonneg_iff a).mp ha x) fun ω =>
        hzero (baVecNP hX x ω)
    have hle : a ≤ 0 := by
      rw [← neg_nonneg]
      refine (ba_nonneg_iff _).mpr fun x => ?_
      have he : (-a).1 x = -(a.1 x) := rfl
      rw [he, CStarModule.inner_neg_right, hvec x, neg_zero]
    exact le_antisymm hle ha

/-! ## Parsec 1530: `ad_T` -/

/-- **153I** (`hilbmod-ad-ncp`, dils.tex:3487, Proposition), part 1: for an
adjointable bounded module map `T : X → Y` (with adjoint `T'`) between
Hilbert 𝒷-modules, the map `ad_T : 𝒷ᵃ(Y) → 𝒷ᵃ(X)`, `ad_T(S) = T* S T`,
is completely positive.

**153II** is the author's proof, transcribed here for part 1. -/
theorem hilbmod_ad_cp [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X) (hT : ModuleAdjointTo 𝒷 ⇑T ⇑T') :
    ∃ ad : Ba 𝒷 Y →ₗ[ℂ] Ba 𝒷 X,
      (∀ S : Ba 𝒷 Y, (ad S).1 = T'.comp (S.1.comp T)) ∧
      IsCompletelyPositiveMap ad := by
  -- dils.tex:3495 (**153II**), transcribed: `∑ᵢⱼ Bⱼ* T* Aⱼ* Aᵢ T Bᵢ =
  -- (∑ᵢ Aᵢ T Bᵢ)* (∑ⱼ Aⱼ T Bⱼ) ≥ 0`, checked on vector states (**144I**).
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  let _ : NormedSpace ℂ Y := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  have hTsymm : ModuleAdjointTo 𝒷 (⇑T' : Y → X) ⇑T :=
    moduleAdjointTo_unique (𝒜 := 𝒷) _ _ _ (moduleAdjointTo_symm (𝒜 := 𝒷) _ _ hT)
      (moduleAdjointTo_symm (𝒜 := 𝒷) _ _ hT) ▸
      moduleAdjointTo_symm (𝒜 := 𝒷) _ _ hT
  -- `T' ∘ S ∘ T` is adjointable, with adjoint `T' ∘ S* ∘ T`
  have hmem : ∀ S : Ba 𝒷 Y, ModuleAdjointable 𝒷 ⇑(T'.comp (S.1.comp T)) := by
    intro S
    obtain ⟨S', hS'⟩ := S.2
    refine ⟨fun x => T' (S' (T x)), fun x x' => ?_⟩
    change inner 𝒷 (T' (S.1 (T x))) x' = inner 𝒷 x (T' (S' (T x')))
    rw [hTsymm (S.1 (T x)) x', hS' (T x) (T x'), ← hT x (S' (T x'))]
  set ad : Ba 𝒷 Y →ₗ[ℂ] Ba 𝒷 X :=
    { toFun := fun S => ⟨T'.comp (S.1.comp T), hmem S⟩
      map_add' := fun S S' => Subtype.ext (by
        refine ContinuousLinearMap.ext fun x => ?_
        change T' ((S + S').1 (T x)) = T' (S.1 (T x)) + T' (S'.1 (T x))
        change T' (S.1 (T x) + S'.1 (T x)) = _
        rw [map_add])
      map_smul' := fun c S => Subtype.ext (by
        refine ContinuousLinearMap.ext fun x => ?_
        change T' ((c • S).1 (T x)) = c • T' (S.1 (T x))
        change T' (c • S.1 (T x)) = _
        rw [map_smul]) } with had
  refine ⟨ad, fun S => rfl, ?_⟩
  intro n A B
  -- the vector-state computation of dils.tex:3495
  refine ba_nonneg_of_vector _ fun x => ?_
  set C : Fin n → Y := fun i => (A i).1 (T ((B i).1 x)) with hC
  -- the coercion `𝒷ᵃ(X) → B(X)` is additive, so it commutes with the sums
  let val : Ba 𝒷 X →+ (X →L[ℂ] X) :=
    { toFun := fun S => S.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hvalSum : ∀ f : Fin n → Fin n → Ba 𝒷 X,
      ((∑ i, ∑ j, f i j : Ba 𝒷 X)).1 x = ∑ i, ∑ j, ((f i j).1 x) := by
    intro f
    have h : ((∑ i, ∑ j, f i j : Ba 𝒷 X)).1 = ∑ i, ∑ j, (f i j).1 := by
      change val _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_sum val _ _
    rw [h]
    simp
  -- `⟨x, Bᵢ* T* Aᵢ* Aⱼ T Bⱼ x⟩ = ⟨AᵢTBᵢx, AⱼTBⱼx⟩`
  have hterm : ∀ i j : Fin n,
      (inner 𝒷 x
        (((star (B i) * ad (star (A i) * A j) * B j : Ba 𝒷 X)).1 x) : 𝒷)
        = inner 𝒷 (C i) (C j) := by
    intro i j
    have hBi : ModuleAdjointTo 𝒷 (⇑((B i).1) : X → X)
        ⇑((star (B i) : Ba 𝒷 X)).1 := baSubalgebra_star_spec (B i)
    have hAi : ModuleAdjointTo 𝒷 (⇑((A i).1) : Y → Y)
        ⇑((star (A i) : Ba 𝒷 Y)).1 := baSubalgebra_star_spec (A i)
    change (inner 𝒷 x
      (((star (B i) : Ba 𝒷 X)).1
        (T' (((star (A i) : Ba 𝒷 Y)).1 ((A j).1 (T ((B j).1 x)))))) : 𝒷) = _
    rw [← hBi x _, ← hT ((B i).1 x) _, ← hAi (T ((B i).1 x)) _]
  rw [hvalSum]
  simp only [CStarModule.inner_sum_right, hterm]
  -- `∑ᵢⱼ ⟨Cᵢ,Cⱼ⟩ = ⟨∑ᵢ Cᵢ, ∑ⱼ Cⱼ⟩ ≥ 0`
  have hgram : ∑ i, ∑ j, (inner 𝒷 (C i) (C j) : 𝒷)
      = inner 𝒷 (∑ i, C i) (∑ j, C j) := by
    rw [CStarModule.inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => (CStarModule.inner_sum_right).symm
  rw [hgram]
  exact CStarModule.inner_self_nonneg

set_option maxHeartbeats 1000000 in
-- as for `ba_isLUB`: instance search through `Ba 𝒷 X` is slow
set_option linter.unusedVariables false in
-- `hX` is the thesis's hypothesis and is deliberately kept; see the note below
/-- **153I** (`hilbmod-ad-ncp`, dils.tex:3487, Proposition), part 2: if `X`
and `Y` are moreover self-dual, then `ad_T` is normal, i.e. an ncp-map.

**153III** (the author's proof) is not available to us; the proof here is
**152XII** `ba_isLUB` twice: the vector forms of `ad_T S` on `X` are the
vector forms of `S` on `Y` (`⟨x, T*STx⟩ = ⟨Tx, S(Tx)⟩`), and both suprema
are computed by their vector forms.  Only `hY` is used: normality of `ad_T`
does not need `X` to be self-dual, since the supremum it has to preserve is
one that already exists in `𝒷ᵃ(X)` by hypothesis. -/
theorem hilbmod_ad_ncp [VonNeumannAlgebra 𝒷] [CompleteSpace X]
    [CompleteSpace Y] (hX : SelfDual 𝒷 X) (hY : SelfDual 𝒷 Y)
    (T : X →L[ℂ] Y) (T' : Y →L[ℂ] X) (hT : ModuleAdjointTo 𝒷 ⇑T ⇑T') :
    ∃ ad : NCPMap (Ba 𝒷 Y) (Ba 𝒷 X),
      ∀ S : Ba 𝒷 Y, (ad S).1 = T'.comp (S.1.comp T) := by
  obtain ⟨ad, hadeq, hadcp⟩ := hilbmod_ad_cp T T' hT
  -- the vector forms of `ad_T S` on `X` are the vector forms of `S` on `Y`
  have hvec : ∀ (S : Ba 𝒷 Y) (x : X),
      (inner 𝒷 x ((ad S).1 x) : 𝒷) = inner 𝒷 (T x) (S.1 (T x)) := by
    intro S x
    rw [hadeq S]
    exact (hT x (S.1 (T x))).symm
  have hmono : ∀ Z W : Ba 𝒷 Y, Z ≤ W → ad Z ≤ ad W := by
    intro Z W h
    rw [← sub_nonneg, ← map_sub]
    refine (ba_nonneg_iff _).mpr fun x => ?_
    rw [hvec (W - Z) x]
    have he : (W - Z).1 (T x) = W.1 (T x) - Z.1 (T x) := rfl
    rw [he, CStarModule.inner_sub_right, sub_nonneg]
    exact ba_inner_mono (T x) h
  have hcp2 : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) (Ba 𝒷 Y)),
      0 ≤ M → 0 ≤ M.map ⇑ad := ((cp_iff ad).out 0 1).mp hadcp
  -- normality: **152XII** computes both suprema by vector forms
  have hnorm : PreservesDirSups ⇑ad := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact hmono _ _ (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · intro c hc
      rw [← sub_nonneg]
      refine (ba_nonneg_iff _).mpr fun x => ?_
      rw [show (c - ad (s : Ba 𝒷 Y)).1 x = c.1 x - (ad (s : Ba 𝒷 Y)).1 x from rfl,
        CStarModule.inner_sub_right, sub_nonneg, hvec]
      -- `⟨x, c x⟩` is self-adjoint because it dominates `⟨Tx, d₀ (Tx)⟩`
      obtain ⟨d₀, hd₀⟩ := hne
      have h1 : (inner 𝒷 x ((ad (d₀ : Ba 𝒷 Y)).1 x) : 𝒷) ≤ inner 𝒷 x (c.1 x) :=
        ba_inner_mono x (hc ⟨d₀, hd₀, rfl⟩)
      have h2 : IsSelfAdjoint (inner 𝒷 x ((ad (d₀ : Ba 𝒷 Y)).1 x) : 𝒷) := by
        rw [hvec]
        exact ba_inner_isSelfAdjoint _ _ d₀.2
      have h3 : IsSelfAdjoint ((inner 𝒷 x (c.1 x) : 𝒷)
          - inner 𝒷 x ((ad (d₀ : Ba 𝒷 Y)).1 x)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr h1)
      have hcsa : IsSelfAdjoint (inner 𝒷 x (c.1 x) : 𝒷) := by
        have h4 : (inner 𝒷 x (c.1 x) : 𝒷)
            = ((inner 𝒷 x (c.1 x) : 𝒷) - inner 𝒷 x ((ad (d₀ : Ba 𝒷 Y)).1 x))
              + inner 𝒷 x ((ad (d₀ : Ba 𝒷 Y)).1 x) := by abel
        rw [h4]
        exact h3.add h2
      -- and it dominates every `⟨Tx, d (Tx)⟩`, so it dominates their supremum
      have hlv := ba_isLUB_vec hY ⟨d₀, hd₀⟩ hdir hlub (T x)
      exact Subtype.coe_le_coe.mpr
        (hlv.2 (by
          rintro _ ⟨d, hd, rfl⟩
          refine Subtype.coe_le_coe.mp ?_
          change (inner 𝒷 (T x) ((d : Ba 𝒷 Y).1 (T x)) : 𝒷) ≤ _
          rw [← hvec]
          exact ba_inner_mono x (hc ⟨d, hd, rfl⟩)) :
          baVec (T x) s ≤ (⟨inner 𝒷 x (c.1 x), hcsa⟩ : selfAdjoint 𝒷))
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := ad
               map_cstarMatrix_nonneg' := fun k M hM => hcp2 k M hM }
           preservesDirSups' := hnorm }, hadeq⟩

end BaVN

section AdjVector

variable {𝒜 : Type u} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {n : ℕ}

set_option linter.unusedSectionVars false

/-- The functional `P ↦ ∑ᵢⱼ cᵢ* Pᵢⱼ cⱼ` whose positivity for all `c`
characterises positivity of a matrix (**33II**.1
`cstar_matrix_positive_iff`); packaged as an additive map so that it can be
pushed through finite sums of matrices. -/
private def conjFun (c : Fin n → 𝒜) : CStarMatrix (Fin n) (Fin n) 𝒜 →+ 𝒜 where
  toFun P := ∑ i, ∑ j, star (c i) * P i j * c j
  map_zero' := by simp
  map_add' P Q := by
    simp only [CStarMatrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem conjFun_apply (c : Fin n → 𝒜) (P : CStarMatrix (Fin n) (Fin n) 𝒜) :
    conjFun c P = ∑ i, ∑ j, star (c i) * P i j * c j := rfl

/-- `∑ᵢⱼ Gᵢ* d Hⱼ = (∑ᵢ Gᵢ)* d (∑ⱼ Hⱼ)`. -/
private theorem sum_star_mul_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → 𝒜) (H : κ → 𝒜) (d : 𝒜) :
    ∑ i, ∑ j, star (G i) * d * H j = star (∑ i, G i) * d * ∑ j, H j := by
  rw [star_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- `∑ₖₗ zₖ* zₗ = (∑ₖ zₖ)* (∑ₗ zₗ)`, hence positive. -/
private theorem sum_star_mul_sum' {ι : Type*} [Fintype ι] (z : ι → 𝒜) :
    ∑ k, ∑ l, star (z k) * z l = star (∑ k, z k) * ∑ l, z l := by
  rw [star_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

/-- **153IV** (`hilbmod-adj-vector-ncp`, dils.tex:3517, Exercise): for a
C*-algebra `𝒜` (here: von Neumann algebra, so that normality makes sense)
and `a₁, …, aₙ ∈ 𝒜`, the map `φ : 𝒜 → Mₙ𝒜`, `φ(d) = (aᵢ* d aⱼ)ᵢⱼ`, is an
ncp-map.

The author's solution routes through **153I** `hilbmod_ad_ncp` (`φ = ad_T`
for the row vector `T : 𝒜ⁿ → 𝒜`, `(bᵢ)ᵢ ↦ ∑ᵢ bᵢaᵢ`), which is still open
here — it waits on **152X**.  So this is a direct argument instead: by
**33II**.1 both claims reduce to the scalar identity
`∑ᵢⱼ cᵢ* φ(d)ᵢⱼ cⱼ = v* d v` with `v = ∑ᵢ aᵢcᵢ`, after which complete
positivity is the observation that the corresponding double sum is a square
`w* w`, and normality is **44VIII** `ad_normal` for `v`. -/
theorem hilbmod_adj_vector_ncp {𝒜 : Type u} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜] {n : ℕ}
    [PartialOrder (CStarMatrix (Fin n) (Fin n) 𝒜)]
    [StarOrderedRing (CStarMatrix (Fin n) (Fin n) 𝒜)]
    (a : Fin n → 𝒜) :
    ∃ φ : 𝒜 →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) 𝒜,
      (∀ (d : 𝒜) (i j : Fin n), φ d i j = star (a i) * d * a j) ∧
      IsCompletelyPositiveMap φ ∧ PreservesDirSups ⇑φ := by
  classical
  set φ : 𝒜 →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) 𝒜 :=
    { toFun := fun d => CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * d * a j)
      map_add' := by
        intro x y; ext i j
        show star (a i) * (x + y) * a j = star (a i) * x * a j + star (a i) * y * a j
        noncomm_ring
      map_smul' := by
        intro r x; ext i j
        show star (a i) * (r • x) * a j = r • (star (a i) * x * a j)
        rw [mul_smul_comm, smul_mul_assoc] } with hφdef
  have hentry : ∀ (d : 𝒜) (i j : Fin n), φ d i j = star (a i) * d * a j := fun _ _ _ => rfl
  -- `φ(d)` conjugated by two matrices collapses to a single `ad`-expression
  have hgen : ∀ (M N : CStarMatrix (Fin n) (Fin n) 𝒜) (c : Fin n → 𝒜) (d : 𝒜),
      conjFun c (star M * φ d * N)
        = star (∑ i, ∑ s, a s * (M s i * c i)) * d * ∑ j, ∑ t, a t * (N t j * c j) := by
    intro M N c d
    have hij : ∀ i j : Fin n, star (c i) * (star M * φ d * N) i j * c j
        = star (∑ s, a s * (M s i * c i)) * d * ∑ t, a t * (N t j * c j) := by
      intro i j
      have hA : star (c i) * (star M * φ d * N) i j * c j
          = ∑ s, ∑ t, star (a s * (M s i * c i)) * d * (a t * (N t j * c j)) := by
        rw [mul_assoc (star M) (φ d) N, CStarMatrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [CStarMatrix.star_apply, CStarMatrix.mul_apply, Finset.mul_sum, Finset.mul_sum,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hentry]
        simp only [star_mul]
        noncomm_ring
      rw [hA]
      exact sum_star_mul_mul_sum _ _ d
    rw [conjFun_apply]
    simp only [hij]
    exact sum_star_mul_mul_sum _ _ d
  -- the special case `M = N = 1`: `∑ᵢⱼ cᵢ* φ(d)ᵢⱼ cⱼ = v* d v` with `v = ∑ᵢ aᵢcᵢ`
  have hcollapse : ∀ (c : Fin n → 𝒜) (d : 𝒜),
      conjFun c (φ d) = star (∑ i, a i * c i) * d * ∑ j, a j * c j := by
    intro c d
    have hij : ∀ i j : Fin n, star (c i) * φ d i j * c j
        = star (a i * c i) * d * (a j * c j) := by
      intro i j; rw [hentry]; simp only [star_mul]; noncomm_ring
    rw [conjFun_apply]
    simp only [hij]
    exact sum_star_mul_mul_sum _ _ d
  refine ⟨φ, hentry, ?_, ?_⟩
  · -- complete positivity
    intro m x B
    refine (cstar_matrix_positive_iff _).mpr fun c => ?_
    set V : Fin m → 𝒜 := fun k => ∑ i, ∑ s, a s * ((B k) s i * c i) with hV
    have hpush : ∑ i, ∑ j,
        star (c i) * (∑ k, ∑ l, star (B k) * φ (star (x k) * x l) * B l) i j * c j
        = ∑ k, ∑ l, star (x k * V k) * (x l * V l) := by
      rw [← conjFun_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hgen (B k) (B l) c (star (x k) * x l)]
      simp only [star_mul]
      noncomm_ring
    rw [hpush, sum_star_mul_sum']
    exact star_mul_self_nonneg _
  · -- normality
    intro D s hne hdir hlub
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have hDh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
    have hs : s = dirSup D hDh := hlub.unique (isLUB_dirSup D hDh)
    -- `φ` is positive, hence monotone
    have hpos : ∀ e : 𝒜, 0 ≤ e → 0 ≤ φ e := by
      intro e he
      refine (cstar_matrix_positive_iff _).mpr fun c => ?_
      rw [← conjFun_apply, hcollapse]
      exact star_left_conjugate_nonneg he _
    have hmono : ∀ e e' : 𝒜, e ≤ e' → φ e ≤ φ e' := by
      intro e e' h
      rw [← sub_nonneg] at h ⊢
      rw [← map_sub]
      exact hpos _ h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact hmono _ _ (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · intro Mub hMub
      rw [← sub_nonneg]
      refine (cstar_matrix_positive_iff _).mpr fun c => ?_
      set v : 𝒜 := ∑ i, a i * c i with hv
      have hub : star v * ↑(dirSup D hDh) * v ≤ conjFun c Mub := by
        refine (ad_normal v D hDh).2 ?_
        rintro _ ⟨d, hd, rfl⟩
        have h0 : (0 : CStarMatrix (Fin n) (Fin n) 𝒜) ≤ Mub - φ ↑d :=
          sub_nonneg.mpr (hMub ⟨d, hd, rfl⟩)
        have h1 := (cstar_matrix_positive_iff _).mp h0 c
        rw [← conjFun_apply, map_sub, hcollapse] at h1
        exact sub_nonneg.mp h1
      rw [← conjFun_apply, map_sub, hcollapse, ← hv, ← hs] at *
      exact sub_nonneg.mpr hub

end AdjVector

end Theses.B.Dils
