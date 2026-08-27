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

See `HilbertModules.lean` for the
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
open scoped Uniformity
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

/-! **150II** `dils_completion` — the existence theorem itself — is **proved
below**, at the end of parsec 1500, after the construction it needs (the
ultranorm uniformity, `V̄`, the σ-closure and the maximal compatible
extension).  Only the *proof* moved; the statement is unchanged. -/

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

/-! ## Parsec 1500 continued: the ultranorm uniformity and `V̄`

The construction behind **150II** `dils_completion`, which is proved at the
end of this parsec.  The thesis builds the ultranorm uniformity and its
completion by hand (**150IV**–**150X**); we diverge and use Mathlib's
`UniformSpace.Completion` — see the note on `UnUnif` below and PROVING-LOG
session 59.  The σ-closure of `V₀ = η(V)` inside `V̄` and the 𝒷-valued inner
product on it (**150XI**–**150XV**) follow, and then the carrier itself.
-/

section UnUniformity

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

theorem unSeminorm_zero (ω : NPFunctional 𝒷) (B : BInner 𝒷 V) :
    unSeminorm ω B.inner (0 : V) = 0 := by
  rw [unSeminorm, B.inner_zero_left]
  simp

theorem unSeminorm_neg (ω : NPFunctional 𝒷) (B : BInner 𝒷 V) (x : V) :
    unSeminorm ω B.inner (-x) = unSeminorm ω B.inner x := by
  rw [unSeminorm, unSeminorm, show (-x) = ((-1 : ℂ)) • x by simp,
    B.inner_smul_left_complex, B.inner_smul_right_complex]
  simp

theorem unSeminorm_smul_complex (ω : NPFunctional 𝒷) (B : BInner 𝒷 V) (c : ℂ) (x : V) :
    unSeminorm ω B.inner (c • x) = ‖c‖ * unSeminorm ω B.inner x := by
  have h : B.inner (c • x) (c • x) = ((Complex.normSq c : ℝ) : ℂ) • B.inner x x := by
    rw [B.inner_smul_left_complex, B.inner_smul_right_complex, smul_smul]
    congr 1
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  have hs : ω (((Complex.normSq c : ℝ) : ℂ) • B.inner x x)
      = ((Complex.normSq c : ℝ) : ℂ) * ω (B.inner x x) :=
    map_smul ω.toPositiveLinearMap _ _
  rw [unSeminorm, unSeminorm, h, hs, Complex.re_ofReal_mul,
    Real.sqrt_mul (Complex.normSq_nonneg c), Complex.norm_def]

/-- The ultranorm seminorm `‖x‖_ω = ω[x,x]^½` bundled as a `Seminorm ℂ V`. -/
noncomputable def unSem (B : BInner 𝒷 V) (ω : NPFunctional 𝒷) : Seminorm ℂ V where
  toFun := unSeminorm ω B.inner
  map_zero' := unSeminorm_zero ω B
  add_le' := unSeminorm_add_le ω B
  neg' := unSeminorm_neg ω B
  smul' := unSeminorm_smul_complex ω B

@[simp] theorem unSem_apply (B : BInner 𝒷 V) (ω : NPFunctional 𝒷) (x : V) :
    unSem B ω x = unSeminorm ω B.inner x := rfl

/-! ### The ultranorm uniformity as a Mathlib `UniformSpace`

**150IV**–**150IX** of the thesis construct the ultranorm uniformity on `V`
by hand, together with the completion `V̄` as fast Cauchy nets modulo
equivalence.  We diverge: the ultranorm uniformity *is* the uniformity of
the seminorm family `(‖·‖_ω)_ω` above, so Mathlib's
`UniformSpace.Completion` supplies `V̄` together with its additive group,
its ℂ-module and its 𝒷-action, and the possible *indefiniteness* of `B` is
handled for free because the completion of a non-separated uniform space is
the separated completion.  (Precedent in the tree: **136II**.)

The thesis licenses this itself.  **150V** opens: "As we need some details
in its construction, we will explicitly define `V̄` … There are other ways
to construct a completion of a uniform space, see for instance
[willard, thm. 39.12]" (dils.tex:2735–2740).  The details it wants are the
entourage relations `ε̂` and `ε̃`; here their place is taken by
`exists_semC_entourage_subset` below, which is **150X**'s own "the extended
seminorms induce the same uniformity".

`UnUnif B` is `V` carrying that uniformity; it is a type synonym so that the
uniformity — which depends on the *term* `B` — can be an instance. -/

/-- `V` carrying the ultranorm uniformity of the 𝒷-valued inner product `B`. -/
def UnUnif (B : BInner 𝒷 V) : Type v := V

namespace UnUnif

variable (B : BInner 𝒷 V)

instance : AddCommGroup (UnUnif B) := inferInstanceAs (AddCommGroup V)
instance : Module ℂ (UnUnif B) := inferInstanceAs (Module ℂ V)
instance : SMul 𝒷 (UnUnif B) := inferInstanceAs (SMul 𝒷 V)

/-- The identity `V → UnUnif B`. -/
def mk : V → UnUnif B := id

@[simp] theorem mk_add (x y : V) : mk B (x + y) = mk B x + mk B y := rfl
@[simp] theorem mk_sub (x y : V) : mk B (x - y) = mk B x - mk B y := rfl
@[simp] theorem mk_zero : mk B (0 : V) = 0 := rfl
@[simp] theorem mk_smul (c : ℂ) (x : V) : mk B (c • x) = c • mk B x := rfl
@[simp] theorem mk_op_smul (b : 𝒷) (x : V) : mk B (b • x) = b • mk B x := rfl
theorem mk_surjective : Function.Surjective (mk B) := fun x => ⟨x, rfl⟩

/-- The 𝒷-valued inner product `B`, transported to `UnUnif B`. -/
def binner : BInner 𝒷 (UnUnif B) := B

@[simp] theorem binner_inner (x y : V) :
    (binner B).inner (mk B x) (mk B y) = B.inner x y := rfl

/-- The ultranorm seminorm on `UnUnif B`. -/
noncomputable def sem (ω : NPFunctional 𝒷) : Seminorm ℂ (UnUnif B) := unSem (binner B) ω

theorem sem_apply (ω : NPFunctional 𝒷) (x : UnUnif B) :
    sem B ω x = unSeminorm ω (binner B).inner x := rfl

@[simp] theorem sem_mk (ω : NPFunctional 𝒷) (x : V) :
    sem B ω (mk B x) = unSeminorm ω B.inner x := rfl

noncomputable instance instUniformSpace : UniformSpace (UnUnif B) :=
  ⨅ ω : NPFunctional 𝒷, (sem B ω).toSeminormedAddCommGroup.toUniformSpace

instance : IsUniformAddGroup (UnUnif B) :=
  isUniformAddGroup_iInf fun ω => (sem B ω).toSeminormedAddCommGroup.to_isUniformAddGroup

/-- The topology of `UnUnif B` is the one of the seminorm family `(‖·‖_ω)_ω`. -/
theorem withSeminorms : WithSeminorms (sem B) :=
  (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf _).mpr rfl

/-! ### Bridge: the tree's `Un*` predicates are the uniform-space notions -/

private theorem tendsto_zero_iff_of_nonneg {ι : Type*} {g : ι → ℝ} {l : Filter ι}
    (hg : ∀ i, 0 ≤ g i) :
    Tendsto g l (𝓝 0) ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, g i < ε := by
  constructor
  · intro h ε hε
    filter_upwards [Metric.tendsto_nhds.mp h ε hε] with i hi
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hg i)] at hi
  · intro h
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [h ε hε] with i hi
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hg i)]

/-- **147I**.1: convergence in the ultranorm uniformity is `UnTendsto`. -/
theorem tendsto_iff {ι : Type*} {f : ι → UnUnif B} {l : Filter ι} {x₀ : UnUnif B} :
    Tendsto f l (𝓝 x₀) ↔ UnTendsto (binner B).inner f l x₀ := by
  rw [(withSeminorms B).tendsto_nhds]
  refine forall_congr' fun ω => ?_
  rw [tendsto_zero_iff_of_nonneg fun i => unSeminorm_nonneg ω (binner B).inner _]
  rfl

/-- The uniformity of `UnUnif B` has the thesis's entourages as a basis:
finitely many np-functionals and an `ε > 0`.  (The entourages of a seminorm
uniformity are **146V**.3, `dils.tex:1728`, through the subbase of **146IIIa**;
**146VII** specializes them to the ultranorm seminorms `‖·‖_ω`.) -/
theorem hasBasis_uniformity :
    (uniformity (UnUnif B)).HasBasis (fun sr : Finset (NPFunctional 𝒷) × ℝ => 0 < sr.2)
      (fun sr => {q : UnUnif B × UnUnif B | (sr.1.sup (sem B)) (q.2 - q.1) < sr.2}) := by
  rw [uniformity_eq_comap_nhds_zero]
  simpa [Seminorm.ball, Set.preimage] using
    ((withSeminorms B).hasBasis_zero_ball).comap (fun q : UnUnif B × UnUnif B => q.2 - q.1)

/-- **147I**.2: Cauchyness in the ultranorm uniformity is `UnCauchy`. -/
theorem cauchy_iff {F : Filter (UnUnif B)} :
    Cauchy F ↔ F.NeBot ∧ UnCauchy (binner B).inner F := by
  classical
  rw [(hasBasis_uniformity B).cauchy_iff]
  refine and_congr Iff.rfl ⟨fun h ω ε hε => ?_, fun h sr hsr => ?_⟩
  · obtain ⟨t, htF, ht⟩ := h ({ω}, ε / 2) (by positivity)
    refine ⟨t, htF, fun x hx y hy => ?_⟩
    have hxy : (sem B ω) (y - x) < ε / 2 := by simpa using ht x hx y hy
    have h2 : unSeminorm ω (binner B).inner (x - y) < ε / 2 := by
      rw [← unSeminorm_neg ω (binner B), neg_sub]; exact hxy
    linarith
  · obtain ⟨s, r⟩ := sr
    simp only at hsr ⊢
    choose t htF ht using fun ω : NPFunctional 𝒷 => h ω (r / 2) (by positivity)
    refine ⟨⋂ ω ∈ s, t ω, (Filter.biInter_finset_mem s).mpr fun ω _ => htF ω, ?_⟩
    intro x hx y hy
    rw [Set.mem_iInter₂] at hx hy
    refine Seminorm.finset_sup_apply_lt hsr fun ω hω => ?_
    have hxy := ht ω x (hx ω hω) y (hy ω hω)
    have h2 : unSeminorm ω (binner B).inner (y - x) ≤ r / 2 := by
      rw [← unSeminorm_neg ω (binner B), neg_sub]; exact hxy
    calc sem B ω (y - x) = unSeminorm ω (binner B).inner (y - x) := rfl
      _ ≤ r / 2 := h2
      _ < r := by linarith

/-- **147I**.5: density in the ultranorm uniformity is `UnDense`. -/
theorem dense_iff {D : Set (UnUnif B)} :
    Dense D ↔ UnDense (binner B).inner D := by
  classical
  constructor
  · intro hD x n ωs ε hε
    obtain ⟨d, hdD, hd⟩ :=
      (mem_closure_iff_nhds_basis ((withSeminorms B).hasBasis_ball)).mp
        (hD x) (Finset.image ωs Finset.univ, ε) hε
    refine ⟨d, hdD, fun i => ?_⟩
    have hd' : ((Finset.image ωs Finset.univ).sup (sem B)) (d - x) < ε := hd
    have hlt : sem B (ωs i) (d - x) < ε :=
      lt_of_le_of_lt (Seminorm.le_finset_sup_apply
        (Finset.mem_image_of_mem ωs (Finset.mem_univ i))) hd'
    rw [show x - d = -(d - x) by abel, unSeminorm_neg (ωs i) (binner B)]
    exact le_of_lt hlt
  · intro hD x
    refine (mem_closure_iff_nhds_basis ((withSeminorms B).hasBasis_ball)).mpr ?_
    rintro ⟨s, r⟩ hr
    simp only at hr
    obtain ⟨d, hdD, hd⟩ := hD x (Fintype.card s)
      (fun i => (((Fintype.equivFin s).symm i : {y // y ∈ s}) : NPFunctional 𝒷)) (r / 2)
      (by positivity)
    refine ⟨d, hdD, show (s.sup (sem B)) (d - x) < r from ?_⟩
    refine Seminorm.finset_sup_apply_lt hr fun ω hω => ?_
    have hi := hd (Fintype.equivFin s ⟨ω, hω⟩)
    simp only [Equiv.symm_apply_apply] at hi
    have h2 : unSeminorm ω (binner B).inner (d - x) ≤ r / 2 := by
      rw [show d - x = -(x - d) by abel, unSeminorm_neg ω (binner B)]; exact hi
    calc sem B ω (d - x) = unSeminorm ω (binner B).inner (d - x) := rfl
      _ ≤ r / 2 := h2
      _ < r := by linarith

/-- A map with a per-np-functional Lipschitz bound for the ultranorm
seminorms is uniformly continuous. -/
theorem uniformContinuous_of_bound {V' : Type w} [AddCommGroup V'] [Module ℂ V'] [SMul 𝒷 V']
    (B' : BInner 𝒷 V') (f : UnUnif B → UnUnif B') (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ω : NPFunctional 𝒷, ∃ ω' : NPFunctional 𝒷, ∀ x y : UnUnif B,
      sem B' ω (f x - f y) ≤ C * sem B ω' (x - y)) :
    UniformContinuous f := by
  classical
  choose ω' hω' using h
  rw [(hasBasis_uniformity B).uniformContinuous_iff (hasBasis_uniformity B')]
  rintro ⟨s, r⟩ hr
  simp only at hr
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨(s.image ω', r / (C + 1)), by positivity, fun x y hxy => ?_⟩
  have hxy' : ((s.image ω').sup (sem B)) (y - x) < r / (C + 1) := hxy
  refine Seminorm.finset_sup_apply_lt hr fun ω hω => ?_
  have hb := hω' ω y x
  have hle : sem B (ω' ω) (y - x) < r / (C + 1) :=
    lt_of_le_of_lt (Seminorm.le_finset_sup_apply (Finset.mem_image_of_mem ω' hω)) hxy'
  have hnn : (0 : ℝ) ≤ sem B (ω' ω) (y - x) := apply_nonneg _ _
  calc sem B' ω (f y - f x) ≤ C * sem B (ω' ω) (y - x) := hb
    _ ≤ (C + 1) * sem B (ω' ω) (y - x) := by nlinarith
    _ < (C + 1) * (r / (C + 1)) := mul_lt_mul_of_pos_left hle hC1
    _ = r := by field_simp

instance : UniformContinuousConstSMul ℂ (UnUnif B) where
  uniformContinuous_const_smul c := by
    refine uniformContinuous_of_bound B B _ ‖c‖ (norm_nonneg c) fun ω => ⟨ω, fun x y => ?_⟩
    rw [show c • x - c • y = c • (x - y) by rw [smul_sub]]
    exact le_of_eq (map_smul_eq_mul (sem B ω) c (x - y))

end UnUnif

theorem BInner.inner_op_smul_op_smul (B : BInner 𝒷 V) (b b' : 𝒷) (x y : V) :
    B.inner (b • x) (b' • y) = b' * B.inner x y * star b := by
  rw [B.inner_op_smul_right, B.inner_op_smul_left, mul_assoc]

theorem BInner.inner_op_smul_smul (B : BInner 𝒷 V) (b : 𝒷) (x y : V) :
    B.inner (b • x) (b • y) = b * B.inner x y * star b :=
  B.inner_op_smul_op_smul b b x y

theorem unSeminorm_eq_zero_of_inner (ω : NPFunctional 𝒷) (B : BInner 𝒷 V) {d : V}
    (h : B.inner d d = 0) : unSeminorm ω B.inner d = 0 := by
  rw [unSeminorm, h]
  simp

theorem unSeminorm_op_smul [VonNeumannAlgebra 𝒷] (ω : NPFunctional 𝒷)
    (B : BInner 𝒷 V) (b : 𝒷) (x : V) :
    unSeminorm ω B.inner (b • x) = unSeminorm (conjNP (star b) ω) B.inner x := by
  rw [unSeminorm, unSeminorm, B.inner_op_smul_self, conjNP_apply, star_star]

/-- **150IX**: `x ↦ b·x` transforms the ultranorm seminorms by `ω ↦ b*ω`
(**72III**.1a), so it is uniformly continuous *even though* the 𝒷-action on
`V` is not assumed additive. -/
theorem unSeminorm_op_smul_sub [VonNeumannAlgebra 𝒷] (ω : NPFunctional 𝒷)
    (B : BInner 𝒷 V) (b : 𝒷) (x y : V) :
    unSeminorm ω B.inner (b • x - b • y)
      = unSeminorm (conjNP (star b) ω) B.inner (x - y) := by
  have key : B.inner (b • x - b • y) (b • x - b • y)
      = b * B.inner (x - y) (x - y) * star b := by
    rw [B.inner_sub_left, B.inner_sub_right, B.inner_sub_right,
      B.inner_op_smul_smul, B.inner_op_smul_smul, B.inner_op_smul_smul,
      B.inner_op_smul_smul, B.inner_sub_left, B.inner_sub_right, B.inner_sub_right]
    noncomm_ring
  rw [unSeminorm, unSeminorm, key, conjNP_apply, star_star]

instance [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V) :
    UniformContinuousConstSMul 𝒷 (UnUnif B) where
  uniformContinuous_const_smul b := by
    refine UnUnif.uniformContinuous_of_bound B B _ 1 zero_le_one
      fun ω => ⟨conjNP (star b) ω, fun x y => ?_⟩
    rw [one_mul]
    exact le_of_eq (unSeminorm_op_smul_sub ω (UnUnif.binner B) b x y)

end UnUniformity

/-! ### `V̄`: the ultranorm completion

**150V**–**150IX** of the thesis (fast nets, the uniform space `N`, the
uniformity on `V̄` and its module structure) are replaced by
`UniformSpace.Completion`; see the note above. -/

section UnCompletion

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷] [VonNeumannAlgebra 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

/-- **150VIII**: `V̄`, the (separated) completion of `V` in the ultranorm
uniformity.  It is an `AddCommGroup`, a `Module ℂ` and carries a 𝒷-action,
all supplied by Mathlib. -/
abbrev UnCompl (B : BInner 𝒷 V) : Type v := UniformSpace.Completion (UnUnif B)

variable (B : BInner 𝒷 V)

/-- **150VIII**: `η : V → V̄`. -/
noncomputable def unEta (v : V) : UnCompl B := ((UnUnif.mk B v : UnUnif B) : UnCompl B)

theorem unEta_def (v : V) : unEta B v = ((UnUnif.mk B v : UnUnif B) : UnCompl B) := rfl

@[simp] theorem unEta_add (x y : V) : unEta B (x + y) = unEta B x + unEta B y :=
  by rw [unEta_def, unEta_def, unEta_def, UnUnif.mk_add]
     exact (UniformSpace.Completion.coe_add (UnUnif.mk B x) (UnUnif.mk B y))

@[simp] theorem unEta_sub (x y : V) : unEta B (x - y) = unEta B x - unEta B y :=
  by rw [unEta_def, unEta_def, unEta_def, UnUnif.mk_sub]
     exact (UniformSpace.Completion.coe_sub (UnUnif.mk B x) (UnUnif.mk B y))

@[simp] theorem unEta_zero : unEta B (0 : V) = 0 :=
  (UniformSpace.Completion.coe_zero).symm

@[simp] theorem unEta_smul_complex (c : ℂ) (x : V) :
    unEta B (c • x) = c • unEta B x :=
  by rw [unEta_def, unEta_def, UnUnif.mk_smul]
     exact (UniformSpace.Completion.coe_smul c (UnUnif.mk B x))

@[simp] theorem unEta_op_smul (b : 𝒷) (x : V) : unEta B (b • x) = b • unEta B x :=
  by rw [unEta_def, unEta_def, UnUnif.mk_op_smul]
     exact (UniformSpace.Completion.coe_smul b (UnUnif.mk B x))

/-- **150II**.2: the image of `η` is dense in `V̄`. -/
theorem denseRange_unEta : DenseRange (unEta B) := by
  have h : Set.range (unEta B) = Set.range ((↑) : UnUnif B → UnCompl B) := by
    ext z
    exact ⟨fun ⟨v, hv⟩ => ⟨UnUnif.mk B v, hv⟩,
      fun ⟨x, hx⟩ => ⟨x, hx⟩⟩
  rw [DenseRange, h]
  exact UniformSpace.Completion.denseRange_coe

theorem uniformContinuous_sem (ω : NPFunctional 𝒷) :
    UniformContinuous (UnUnif.sem B ω) :=
  Seminorm.uniformContinuous_of_continuousAt_zero
    ((UnUnif.withSeminorms B).continuous_seminorm ω).continuousAt

/-- **150X**: the ultranorm seminorms extend to `V̄`. -/
noncomputable def semC (ω : NPFunctional 𝒷) : UnCompl B → ℝ :=
  UniformSpace.Completion.extension (UnUnif.sem B ω)

theorem continuous_semC (ω : NPFunctional 𝒷) : Continuous (semC B ω) :=
  UniformSpace.Completion.continuous_extension

@[simp] theorem semC_coe (ω : NPFunctional 𝒷) (x : UnUnif B) :
    semC B ω (x : UnCompl B) = UnUnif.sem B ω x :=
  UniformSpace.Completion.extension_coe (uniformContinuous_sem B ω) x

@[simp] theorem semC_unEta (ω : NPFunctional 𝒷) (v : V) :
    semC B ω (unEta B v) = unSeminorm ω B.inner v :=
  semC_coe B ω (UnUnif.mk B v)

theorem semC_nonneg (ω : NPFunctional 𝒷) (x : UnCompl B) : 0 ≤ semC B ω x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_const (continuous_semC B ω)) fun a => ?_
  rw [semC_coe]
  exact apply_nonneg _ _

theorem semC_zero (ω : NPFunctional 𝒷) : semC B ω 0 = 0 := by
  rw [show (0 : UnCompl B) = ((0 : UnUnif B) : UnCompl B) from
    (UniformSpace.Completion.coe_zero).symm, semC_coe]
  exact map_zero _

theorem semC_add_le (ω : NPFunctional 𝒷) (x y : UnCompl B) :
    semC B ω (x + y) ≤ semC B ω x + semC B ω y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_le ((continuous_semC B ω).comp continuous_add)
      (((continuous_semC B ω).comp continuous_fst).add
        ((continuous_semC B ω).comp continuous_snd))) fun a b => ?_
  rw [← UniformSpace.Completion.coe_add, semC_coe, semC_coe, semC_coe]
  exact map_add_le_add _ _ _

theorem semC_smul_complex (ω : NPFunctional 𝒷) (c : ℂ) (x : UnCompl B) :
    semC B ω (c • x) = ‖c‖ * semC B ω x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((continuous_semC B ω).comp (continuous_const_smul c))
      ((continuous_semC B ω).const_smul ‖c‖)) fun a => ?_
  rw [← UniformSpace.Completion.coe_smul, semC_coe, semC_coe]
  exact map_smul_eq_mul _ _ _

/-- **150IX**/**150X**: the 𝒷-action transforms the extended seminorms by
`ω ↦ b*ω`. -/
theorem semC_op_smul (ω : NPFunctional 𝒷) (b : 𝒷) (x : UnCompl B) :
    semC B ω (b • x) = semC B (conjNP (star b) ω) x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((continuous_semC B ω).comp (continuous_const_smul b))
      (continuous_semC B (conjNP (star b) ω))) fun a => ?_
  rw [← UniformSpace.Completion.coe_smul, semC_coe, semC_coe]
  exact unSeminorm_op_smul ω (UnUnif.binner B) b a

/-! ### The module axioms on `V̄`

The 𝒷-action on `V` carries **no** axioms — `BInner` constrains only the
inner product — so `b·(x+y) - b·x - b·y` need not vanish in `V`.  It does
vanish in *every* ultranorm seminorm, though, because
`[b·u, b'·v] = b'[u,v]b*` is bilinear in `(b,b')` and in `(u,v)`; since `V̄`
is the *separated* completion, the axioms therefore hold on `V̄` on the nose.
This is where the thesis's remark (**150IX**) that `V̄` "is straightforward to
check" to be a right 𝒷-module is discharged. -/

/-- Elements of `V` that agree in every ultranorm seminorm have the same
image in `V̄`. -/
theorem coe_eq_coe_of_inner_zero {x y : UnUnif B}
    (h : (UnUnif.binner B).inner (x - y) (x - y) = 0) :
    (x : UnCompl B) = (y : UnCompl B) := by
  have hins : Inseparable x y := by
    refine (UnUnif.hasBasis_uniformity B).inseparable_iff_uniformity.mpr ?_
    rintro ⟨s, r⟩ hr
    simp only at hr
    refine Seminorm.finset_sup_apply_lt hr fun ω _ => ?_
    have h0 : UnUnif.sem B ω (y - x) = 0 := by
      rw [UnUnif.sem_apply, show y - x = -(x - y) by abel,
        unSeminorm_neg ω (UnUnif.binner B)]
      exact unSeminorm_eq_zero_of_inner ω (UnUnif.binner B) h
    rw [h0]; exact hr
  exact (hins.map (UniformSpace.Completion.continuous_coe _)).eq

theorem add_op_smul' (b b' : 𝒷) (x : UnCompl B) :
    (b + b') • x = b • x + b' • x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_const_smul (b + b'))
      ((continuous_const_smul b).add (continuous_const_smul b'))) fun a => ?_
  rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_smul,
    ← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_add]
  refine coe_eq_coe_of_inner_zero B ?_
  set A := UnUnif.binner B
  simp only [show ((b + b') • a - (b • a + b' • a) : UnUnif B)
    = (b + b') • a - b • a - b' • a by abel]
  simp only [A.inner_sub_left, A.inner_sub_right, A.inner_op_smul_left,
    A.inner_op_smul_right, star_add]
  noncomm_ring

theorem one_op_smul' (x : UnCompl B) : (1 : 𝒷) • x = x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_const_smul (1 : 𝒷)) continuous_id) fun a => ?_
  rw [← UniformSpace.Completion.coe_smul]
  refine coe_eq_coe_of_inner_zero B ?_
  set A := UnUnif.binner B
  simp only [A.inner_sub_left, A.inner_sub_right, A.inner_op_smul_left,
    A.inner_op_smul_right, star_one]
  noncomm_ring

end UnCompletion

/-! ### The σ-closure and its inner product (**150XI**–**150XV**)

This is the heart of **150II**, and the only part of the construction that
Mathlib does not supply.  The thesis extends the inner product from
`V₀ = η(V)` to a maximal *compatible extension* `W ⊆ V̄` by Zorn's lemma over
pairs (a subset together with an inner product on it), taking `σ(W)` — the
limits of norm-bounded Cauchy nets over `W` — at each step.

**Divergence (case 2).**  We keep the thesis's Zorn argument but drop the
data: the *polarization form* `ipf ω x y` of the extended seminorm `‖·‖_ω`
is defined on all of `V̄`, is jointly continuous, and agrees with `ω[x,y]`
on `V₀`; since the np-functionals separate `𝒷` (**44XI**), the inner product
of a compatible extension is *determined* by its underlying set.  So the
poset the thesis orders by "`W₁ ⊆ W₂` and the inner products agree" is here
a poset of plain subsets under `⊆`, and the thesis's limit step (**150XIV**)
becomes a union of sets. -/

section SigmaClosure

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷] [VonNeumannAlgebra 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

variable (B : BInner 𝒷 V)

/-- The extended seminorms separate the points of `V̄`. -/
theorem eq_zero_of_semC_eq_zero {x : UnCompl B}
    (h : ∀ ω : NPFunctional 𝒷, semC B ω x = 0) : x = 0 := by
  set F : Filter (UnUnif B) := Filter.comap ((↑) : UnUnif B → UnCompl B) (𝓝 x) with hF
  have hne : F.NeBot := UniformSpace.Completion.isDenseInducing_coe.comap_nhds_neBot x
  have hto : Tendsto ((↑) : UnUnif B → UnCompl B) F (𝓝 x) := Filter.map_comap_le
  have hsem : ∀ ω : NPFunctional 𝒷,
      Tendsto (fun a : UnUnif B => UnUnif.sem B ω a) F (𝓝 0) := by
    intro ω
    have h1 : Tendsto (fun a : UnUnif B => semC B ω (a : UnCompl B)) F (𝓝 (semC B ω x)) :=
      ((continuous_semC B ω).continuousAt).tendsto.comp hto
    rw [h ω] at h1
    exact h1.congr fun a => semC_coe B ω a
  have h0 : Tendsto (id : UnUnif B → UnUnif B) F (𝓝 0) := by
    rw [UnUnif.tendsto_iff]
    intro ω
    have := hsem ω
    simpa [UnUnif.sem_apply] using this
  have h1 : Tendsto (fun a : UnUnif B => (a : UnCompl B)) F (𝓝 ((0 : UnUnif B) : UnCompl B)) :=
    ((UniformSpace.Completion.continuous_coe (UnUnif B)).continuousAt).tendsto.comp h0
  rw [UniformSpace.Completion.coe_zero] at h1
  exact tendsto_nhds_unique hto h1

/-- `(ω a).re` as a complex number is `ω a`, for `0 ≤ a`. -/
private theorem npf_re_coe (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    (((ω a).re : ℝ) : ℂ) = ω a := by
  have h := npFunctional_nonneg ω ha
  rw [Complex.le_def] at h
  exact Complex.ext (by simp) (by simp [← h.2])

private theorem npf_smul_complex (ω : NPFunctional 𝒷) (c : ℂ) (a : 𝒷) :
    ω (c • a) = c * ω a :=
  (map_smul ω.toPositiveLinearMap c a).trans (smul_eq_mul _ _)

private theorem npf_re_nonneg' (ω : NPFunctional 𝒷) {a : 𝒷} (ha : 0 ≤ a) :
    (0 : ℝ) ≤ (ω a).re := by
  have h := npFunctional_nonneg ω ha
  rw [Complex.le_def] at h
  simpa using h.1

/-- The quadratic form `q_ω(x) = ‖x‖_ω²` on `V̄`, as a complex number. -/
private noncomputable def unQ (ω : NPFunctional 𝒷) (x : UnCompl B) : ℂ :=
  ((semC B ω x ^ 2 : ℝ) : ℂ)

private theorem continuous_unQ (ω : NPFunctional 𝒷) : Continuous (unQ B ω) :=
  Complex.continuous_ofReal.comp ((continuous_semC B ω).pow 2)

private theorem unQ_coe (ω : NPFunctional 𝒷) (a : UnUnif B) :
    unQ B ω (a : UnCompl B) = ω ((UnUnif.binner B).inner a a) := by
  rw [unQ, semC_coe, UnUnif.sem_apply, unSeminorm,
    Real.sq_sqrt (npf_re_nonneg' ω ((UnUnif.binner B).inner_self_nonneg a))]
  exact npf_re_coe ω ((UnUnif.binner B).inner_self_nonneg a)

private theorem unQ_smul (ω : NPFunctional 𝒷) (c : ℂ) (x : UnCompl B) :
    unQ B ω (c • x) = ((‖c‖ ^ 2 : ℝ) : ℂ) * unQ B ω x := by
  rw [unQ, unQ, semC_smul_complex, mul_pow, Complex.ofReal_mul]

private theorem unQ_zero (ω : NPFunctional 𝒷) : unQ B ω 0 = 0 := by
  rw [unQ, semC_zero]; norm_num

/-- **150XI**, the key device: the polarization form of the extended
seminorm `‖·‖_ω`.  On the image of `V` it is `ω[v,w]`, it is *jointly
continuous* (which the inner product itself is not), and — because the
np-functionals separate the points of `𝒷` — it determines the inner product
of any compatible extension. -/
noncomputable def ipf (ω : NPFunctional 𝒷) (x y : UnCompl B) : ℂ :=
  (4 : ℂ)⁻¹ * (unQ B ω (y + x) - unQ B ω (y - x)
    + Complex.I * unQ B ω (y + Complex.I • x)
    - Complex.I * unQ B ω (y - Complex.I • x))

/-- `ipf` is *jointly* continuous — the point of the polarization form. -/
theorem continuous_ipf₂ {α : Type*} [TopologicalSpace α] (ω : NPFunctional 𝒷)
    {f g : α → UnCompl B} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => ipf B ω (f t) (g t) :=
  continuous_const.mul
    (((((continuous_unQ B ω).comp (hg.add hf)).sub
      ((continuous_unQ B ω).comp (hg.sub hf))).add
        (continuous_const.mul ((continuous_unQ B ω).comp
          (hg.add (hf.const_smul Complex.I))))).sub
      (continuous_const.mul ((continuous_unQ B ω).comp
        (hg.sub (hf.const_smul Complex.I)))))

theorem continuous_ipf (ω : NPFunctional 𝒷) :
    Continuous fun p : UnCompl B × UnCompl B => ipf B ω p.1 p.2 :=
  continuous_ipf₂ B ω continuous_fst continuous_snd

@[simp] theorem ipf_coe (ω : NPFunctional 𝒷) (a b : UnUnif B) :
    ipf B ω (a : UnCompl B) (b : UnCompl B) = ω ((UnUnif.binner B).inner a b) := by
  set A := UnUnif.binner B with hA
  have e1 : A.inner (b + a) (b + a)
      = A.inner b b + A.inner b a + A.inner a b + A.inner a a := by
    simp only [A.inner_add_left, A.inner_add_right]; abel
  have e2 : A.inner (b - a) (b - a)
      = A.inner b b - A.inner b a - A.inner a b + A.inner a a := by
    simp only [A.inner_sub_left, A.inner_sub_right]; abel
  have e3 : A.inner (b + Complex.I • a) (b + Complex.I • a)
      = A.inner b b + Complex.I • A.inner b a - Complex.I • A.inner a b
        + A.inner a a := by
    simp only [A.inner_add_left, A.inner_add_right, A.inner_smul_left_complex,
      A.inner_smul_right_complex, Complex.conj_I, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have e4 : A.inner (b - Complex.I • a) (b - Complex.I • a)
      = A.inner b b - Complex.I • A.inner b a + Complex.I • A.inner a b
        + A.inner a a := by
    simp only [A.inner_sub_left, A.inner_sub_right, A.inner_smul_left_complex,
      A.inner_smul_right_complex, Complex.conj_I, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  rw [ipf, ← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_add,
    ← UniformSpace.Completion.coe_sub, ← UniformSpace.Completion.coe_add,
    ← UniformSpace.Completion.coe_sub, unQ_coe, unQ_coe, unQ_coe, unQ_coe,
    e1, e2, e3, e4]
  simp only [npFunctional_add, npFunctional_sub, npf_smul_complex]
  linear_combination ((ω (A.inner b a) - ω (A.inner a b)) / 2) * Complex.I_mul_I

theorem ipf_unEta (ω : NPFunctional 𝒷) (v w : V) :
    ipf B ω (unEta B v) (unEta B w) = ω (B.inner v w) :=
  ipf_coe B ω (UnUnif.mk B v) (UnUnif.mk B w)

private theorem norm_sq_complex (z : ℂ) : (‖z‖ ^ 2 : ℝ) = Complex.normSq z := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]

/-- `ipf ω x x = ‖x‖_ω²` — the polarization form recovers the seminorm. -/
theorem ipf_self (ω : NPFunctional 𝒷) (x : UnCompl B) :
    ipf B ω x x = ((semC B ω x ^ 2 : ℝ) : ℂ) := by
  have h2 : x + x = (2 : ℂ) • x := by rw [two_smul]
  have h0 : x - x = 0 := sub_self x
  have hp : x + Complex.I • x = ((1 + Complex.I : ℂ)) • x := by
    rw [add_smul, one_smul]
  have hm : x - Complex.I • x = ((1 - Complex.I : ℂ)) • x := by
    rw [sub_smul, one_smul]
  have n2 : ((‖(2 : ℂ)‖ ^ 2 : ℝ) : ℂ) = 4 := by
    rw [norm_sq_complex]; norm_num
  have np : ((‖(1 + Complex.I : ℂ)‖ ^ 2 : ℝ) : ℂ) = 2 := by
    rw [norm_sq_complex]; simp [Complex.normSq_apply]; norm_num
  have nm : ((‖(1 - Complex.I : ℂ)‖ ^ 2 : ℝ) : ℂ) = 2 := by
    rw [norm_sq_complex]; simp [Complex.normSq_apply]; norm_num
  rw [ipf, h2, h0, hp, hm, unQ_smul, unQ_smul, unQ_smul, unQ_zero, n2, np, nm]
  rw [unQ]
  ring

theorem ipf_add_right (ω : NPFunctional 𝒷) (x y z : UnCompl B) :
    ipf B ω x (y + z) = ipf B ω x y + ipf B ω x z := by
  refine UniformSpace.Completion.induction_on₃ x y z
    (isClosed_eq (continuous_ipf₂ B ω continuous_fst
        (continuous_snd.fst.add continuous_snd.snd))
      ((continuous_ipf₂ B ω continuous_fst continuous_snd.fst).add
        (continuous_ipf₂ B ω continuous_fst continuous_snd.snd)))
    fun a b c => ?_
  rw [← UniformSpace.Completion.coe_add, ipf_coe, ipf_coe, ipf_coe,
    (UnUnif.binner B).inner_add_right, npFunctional_add]

theorem ipf_smul_right (ω : NPFunctional 𝒷) (c : ℂ) (x y : UnCompl B) :
    ipf B ω x (c • y) = c * ipf B ω x y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (continuous_ipf₂ B ω continuous_fst (continuous_snd.const_smul c))
      ((continuous_ipf₂ B ω continuous_fst continuous_snd).const_mul c))
    fun a b => ?_
  rw [← UniformSpace.Completion.coe_smul, ipf_coe, ipf_coe,
    (UnUnif.binner B).inner_smul_right_complex, npf_smul_complex]

theorem ipf_conj (ω : NPFunctional 𝒷) (x y : UnCompl B) :
    ipf B ω y x = (starRingEnd ℂ) (ipf B ω x y) := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (continuous_ipf₂ B ω continuous_snd continuous_fst)
      (Complex.continuous_conj.comp
        (continuous_ipf₂ B ω continuous_fst continuous_snd)))
    fun a b => ?_
  rw [ipf_coe, ipf_coe, starRingEnd_apply, ← npFunctional_star,
    (UnUnif.binner B).star_inner]

/-- The 𝒷-action transforms `ipf` by `ω ↦ b*ω` — the form of **150IX** that
survives to the completion, and the only handle we have on the module
action there. -/
theorem ipf_op_smul (ω : NPFunctional 𝒷) (b : 𝒷) (x y : UnCompl B) :
    ipf B ω (b • x) (b • y) = ipf B (conjNP (star b) ω) x y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (continuous_ipf₂ B ω (continuous_fst.const_smul b)
        (continuous_snd.const_smul b))
      (continuous_ipf₂ B (conjNP (star b) ω) continuous_fst continuous_snd))
    fun a c => ?_
  rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_smul,
    ipf_coe, ipf_coe, BInner.inner_op_smul_smul, conjNP_apply, star_star]

theorem ipf_zero_right (ω : NPFunctional 𝒷) (x : UnCompl B) : ipf B ω x 0 = 0 := by
  have := ipf_smul_right B ω 0 x 0
  simpa using this

theorem ipf_sub_right (ω : NPFunctional 𝒷) (x y z : UnCompl B) :
    ipf B ω x (y - z) = ipf B ω x y - ipf B ω x z := by
  rw [sub_eq_add_neg, ipf_add_right, show -z = (-1 : ℂ) • z by simp,
    ipf_smul_right]
  ring

/-! ### The inner product determined by `ipf`

Because the np-functionals separate the points of `𝒷` (**44XI**), an element
`b` with `ω b = ipf ω x y` for every `ω` is unique if it exists.  So — and
this is what replaces the thesis's poset of *pairs* (a subset together with
an inner product) by a poset of plain subsets — the inner product of a
compatible extension is determined by the extension's underlying set. -/

/-- `x` and `y` **have an inner product**: some `b ∈ 𝒷` has `ω b = ipf ω x y`
for every np-functional `ω`. -/
def HasIP (x y : UnCompl B) : Prop :=
  ∃ b : 𝒷, ∀ ω : NPFunctional 𝒷, ω b = ipf B ω x y

/-- The inner product of `x` and `y` (junk value `0` when `HasIP` fails). -/
noncomputable def ipVal (x y : UnCompl B) : 𝒷 :=
  Classical.epsilon fun b : 𝒷 => ∀ ω : NPFunctional 𝒷, ω b = ipf B ω x y

theorem ipVal_spec {x y : UnCompl B} (h : HasIP B x y) (ω : NPFunctional 𝒷) :
    ω (ipVal B x y) = ipf B ω x y :=
  Classical.epsilon_spec h ω

theorem ipVal_eq {x y : UnCompl B} {b : 𝒷}
    (hb : ∀ ω : NPFunctional 𝒷, ω b = ipf B ω x y) : ipVal B x y = b :=
  eq_of_forall_npFunctional fun ω => by rw [ipVal_spec B ⟨b, hb⟩ ω, ← hb ω]

theorem hasIP_unEta (v w : V) : HasIP B (unEta B v) (unEta B w) :=
  ⟨B.inner v w, fun ω => (ipf_unEta B ω v w).symm⟩

@[simp] theorem ipVal_unEta (v w : V) :
    ipVal B (unEta B v) (unEta B w) = B.inner v w :=
  ipVal_eq B fun ω => (ipf_unEta B ω v w).symm

variable {B}

theorem HasIP.add_right {x y z : UnCompl B} (h₁ : HasIP B x y) (h₂ : HasIP B x z) :
    HasIP B x (y + z) :=
  ⟨ipVal B x y + ipVal B x z, fun ω => by
    rw [npFunctional_add, ipVal_spec B h₁, ipVal_spec B h₂, ipf_add_right]⟩

theorem ipVal_add_right {x y z : UnCompl B} (h₁ : HasIP B x y) (h₂ : HasIP B x z) :
    ipVal B x (y + z) = ipVal B x y + ipVal B x z :=
  ipVal_eq B fun ω => by
    rw [npFunctional_add, ipVal_spec B h₁, ipVal_spec B h₂, ipf_add_right]

theorem HasIP.smul_right (c : ℂ) {x y : UnCompl B} (h : HasIP B x y) :
    HasIP B x (c • y) :=
  ⟨c • ipVal B x y, fun ω => by
    rw [npf_smul_complex, ipVal_spec B h, ipf_smul_right]⟩

theorem ipVal_smul_right (c : ℂ) {x y : UnCompl B} (h : HasIP B x y) :
    ipVal B x (c • y) = c • ipVal B x y :=
  ipVal_eq B fun ω => by rw [npf_smul_complex, ipVal_spec B h, ipf_smul_right]

theorem HasIP.symm {x y : UnCompl B} (h : HasIP B x y) : HasIP B y x :=
  ⟨star (ipVal B x y), fun ω => by
    rw [npFunctional_star, ipVal_spec B h, ← starRingEnd_apply, ← ipf_conj]⟩

theorem ipVal_symm {x y : UnCompl B} (h : HasIP B x y) :
    ipVal B y x = star (ipVal B x y) :=
  ipVal_eq B fun ω => by
    rw [npFunctional_star, ipVal_spec B h, ← starRingEnd_apply, ← ipf_conj]

theorem HasIP.add_left {x y z : UnCompl B} (h₁ : HasIP B x z) (h₂ : HasIP B y z) :
    HasIP B (x + y) z := ((h₁.symm.add_right h₂.symm).symm)

theorem ipVal_add_left {x y z : UnCompl B} (h₁ : HasIP B x z) (h₂ : HasIP B y z) :
    ipVal B (x + y) z = ipVal B x z + ipVal B y z := by
  rw [ipVal_symm (h₁.symm.add_right h₂.symm), ipVal_add_right h₁.symm h₂.symm,
    star_add, ipVal_symm h₁, ipVal_symm h₂, star_star, star_star]

theorem HasIP.smul_left (c : ℂ) {x y : UnCompl B} (h : HasIP B x y) :
    HasIP B (c • x) y := (h.symm.smul_right c).symm

theorem ipVal_smul_left (c : ℂ) {x y : UnCompl B} (h : HasIP B x y) :
    ipVal B (c • x) y = (starRingEnd ℂ) c • ipVal B x y := by
  rw [ipVal_symm (h.symm.smul_right c), ipVal_smul_right c h.symm, star_smul,
    ipVal_symm h, star_star]
  rfl

theorem HasIP.op_smul (b : 𝒷) {x y : UnCompl B} (h : HasIP B x y) :
    HasIP B (b • x) (b • y) :=
  ⟨b * ipVal B x y * star b, fun ω => by
    have hc : ω (b * ipVal B x y * star b) = conjNP (star b) ω (ipVal B x y) := by
      rw [conjNP_apply, star_star]
    rw [hc, ipVal_spec B h, ipf_op_smul]⟩

theorem ipVal_op_smul (b : 𝒷) {x y : UnCompl B} (h : HasIP B x y) :
    ipVal B (b • x) (b • y) = b * ipVal B x y * star b :=
  ipVal_eq B fun ω => by
    have hc : ω (b * ipVal B x y * star b) = conjNP (star b) ω (ipVal B x y) := by
      rw [conjNP_apply, star_star]
    rw [hc, ipVal_spec B h, ipf_op_smul]

variable (B)

@[simp] theorem ipVal_zero_right (x : UnCompl B) : ipVal B x 0 = 0 :=
  ipVal_eq B fun ω => by rw [npFunctional_zero, ipf_zero_right]

/-- `[x,x] = 0` forces `x = 0`: the inner product of a compatible extension
is *definite*, because the extended seminorms separate `V̄`. -/
theorem eq_zero_of_ipVal_self_eq_zero {x : UnCompl B} (h : HasIP B x x)
    (h0 : ipVal B x x = 0) : x = 0 := by
  refine eq_zero_of_semC_eq_zero B fun ω => ?_
  have h1 : ((semC B ω x ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← ipf_self B ω x, ← ipVal_spec B h ω, h0, npFunctional_zero]
  have h2 : semC B ω x ^ 2 = 0 := by exact_mod_cast h1
  nlinarith [semC_nonneg B ω x]

/-- Positivity: `ω [x,x] = ‖x‖_ω² ≥ 0` for every np-functional, and the
np-functionals are *order* separating (**44XI**). -/
theorem ipVal_self_nonneg {x : UnCompl B} (h : HasIP B x x) :
    (0 : 𝒷) ≤ ipVal B x x := by
  have hsa : IsSelfAdjoint (ipVal B x x) := (ipVal_symm h).symm
  refine np_orderSeparating 0 _ (IsSelfAdjoint.zero 𝒷) hsa fun ω => ?_
  rw [npFunctional_zero, ipVal_spec B h ω, ipf_self, Complex.le_def]
  refine ⟨?_, by simp only [Complex.zero_im, Complex.ofReal_im]⟩
  simp only [Complex.zero_re, Complex.ofReal_re]
  positivity

/-- The sixth module law on `V̄`: the ℂ-action on `𝒷` and the 𝒷-action on
`V̄` are compatible.  Like the other five it holds only after separation. -/
theorem smul_op_smul' (c : ℂ) (b : 𝒷) (x : UnCompl B) :
    ((c • b) • x : UnCompl B) = c • (b • x) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_const_smul (c • b))
      ((continuous_const_smul c).comp (continuous_const_smul b))) fun a => ?_
  rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_smul,
    ← UniformSpace.Completion.coe_smul]
  refine coe_eq_coe_of_inner_zero B ?_
  set A := UnUnif.binner B
  simp only [A.inner_sub_left, A.inner_sub_right, A.inner_op_smul_left,
    A.inner_op_smul_right, A.inner_smul_left_complex, A.inner_smul_right_complex,
    star_smul, Complex.star_def, smul_smul, smul_mul_assoc, mul_smul_comm,
    mul_assoc]
  rw [mul_comm ((starRingEnd ℂ) c) c]
  abel

private theorem smul_cancel {c : ℂ} (hc : c ≠ 0) {u v : 𝒷} (h : c • u = c • v) :
    u = v := by
  have h2 := congrArg (fun z : 𝒷 => c⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using h2

/-- **150XI** (`dils-completion-setup`, dils.tex:3035, Definition), rephrased:
a **compatible extension** is a subset of `V̄` containing `V₀ = η(V)`, closed
under the operations, and on which the inner product exists.

The thesis carries the inner product as *data* (a pair of a subset and an
inner product on it) and orders such pairs; here `HasIP` makes it a property
of the set alone, because `ipf` determines the inner product.  The thesis's
fourth condition — that the extension's own ultranorm seminorms agree with
those of `V̄` — is likewise automatic, being `ω [x,x] = ipf ω x x = ‖x‖_ω²`. -/
structure IsCompatExt (W : Submodule ℂ (UnCompl B)) : Prop where
  unEta_mem : ∀ v : V, unEta B v ∈ W
  op_smul_mem : ∀ (b : 𝒷) ⦃x : UnCompl B⦄, x ∈ W → b • x ∈ W
  hasIP : ∀ ⦃x y : UnCompl B⦄, x ∈ W → y ∈ W → HasIP B x y

variable {B}

/-- The polarization identity in the *algebra* variable: applying
`[b·x, b·y] = b[x,y]b*` at `1 + b` and at `1 + ib` and combining. -/
private theorem compat_key {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W)
    {x y : UnCompl B} (hx : x ∈ W) (hy : y ∈ W) (b : 𝒷) :
    ipVal B x (b • y) + ipVal B (b • x) y
      = ipVal B x y * star b + b * ipVal B x y := by
  have hbx := hW.op_smul_mem b hx
  have hby := hW.op_smul_mem b hy
  have hxy := hW.hasIP hx hy
  have hsum := ipVal_op_smul (1 + b) hxy
  have hex : ((1 + b) • x : UnCompl B) = x + b • x := by
    rw [add_op_smul', one_op_smul']
  have hey : ((1 + b) • y : UnCompl B) = y + b • y := by
    rw [add_op_smul', one_op_smul']
  rw [hex, hey, ipVal_add_left (hW.hasIP hx (W.add_mem hy hby))
      (hW.hasIP hbx (W.add_mem hy hby)),
    ipVal_add_right (hW.hasIP hx hy) (hW.hasIP hx hby),
    ipVal_add_right (hW.hasIP hbx hy) (hW.hasIP hbx hby),
    ipVal_op_smul b hxy] at hsum
  have hrhs : (1 + b) * ipVal B x y * star (1 + b)
      = ipVal B x y + ipVal B x y * star b + b * ipVal B x y
        + b * ipVal B x y * star b := by
    rw [star_add, star_one]; noncomm_ring
  rw [hrhs] at hsum
  have h3 : ipVal B x (b • y) + ipVal B (b • x) y
      = (ipVal B x y + ipVal B x y * star b + b * ipVal B x y
          + b * ipVal B x y * star b) - ipVal B x y - b * ipVal B x y * star b := by
    rw [← hsum]; abel
  rw [h3]; abel

/-- 𝒷-homogeneity of the inner product of a compatible extension. -/
theorem IsCompatExt.ipVal_op_smul_right {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W)
    (b : 𝒷) {x y : UnCompl B} (hx : x ∈ W) (hy : y ∈ W) :
    ipVal B x (b • y) = b * ipVal B x y := by
  have hbx := hW.op_smul_mem b hx
  have hby := hW.op_smul_mem b hy
  have k1 := compat_key hW hx hy b
  have k2 := compat_key hW hx hy ((Complex.I : ℂ) • b)
  rw [smul_op_smul', smul_op_smul',
    ipVal_smul_right Complex.I (hW.hasIP hx hby),
    ipVal_smul_left Complex.I (hW.hasIP hbx hy), Complex.conj_I,
    star_smul, Complex.star_def, Complex.conj_I, mul_smul_comm,
    smul_mul_assoc, neg_smul, neg_smul] at k2
  have e2 : ipVal B x (b • y) - ipVal B (b • x) y
      = -(ipVal B x y * star b) + b * ipVal B x y := by
    refine smul_cancel Complex.I_ne_zero ?_
    rw [smul_sub, smul_add, smul_neg, sub_eq_add_neg]
    exact k2
  have e3 : (2 : ℂ) • ipVal B x (b • y) = (2 : ℂ) • (b * ipVal B x y) := by
    rw [two_smul, two_smul]
    calc ipVal B x (b • y) + ipVal B x (b • y)
        = (ipVal B x (b • y) + ipVal B (b • x) y)
          + (ipVal B x (b • y) - ipVal B (b • x) y) := by abel
      _ = (ipVal B x y * star b + b * ipVal B x y)
          + (-(ipVal B x y * star b) + b * ipVal B x y) := by rw [k1, e2]
      _ = b * ipVal B x y + b * ipVal B x y := by abel
  exact smul_cancel two_ne_zero e3

/-- The 𝒷-action on a compatible extension.  It is not an instance: it
depends on the proof `hW`. -/
@[instance_reducible] noncomputable def IsCompatExt.smulInst
    {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W) : SMul 𝒷 W where
  smul b x := ⟨b • (x : UnCompl B), hW.op_smul_mem b x.2⟩

/-- A compatible extension is a 𝒷-module with a 𝒷-valued inner product —
the thesis's clause 3 of **150XI**, and all five `BInner` axioms come from
the `ipf` identities. -/
noncomputable def IsCompatExt.binner {W : Submodule ℂ (UnCompl B)}
    (hW : IsCompatExt B W) : letI := hW.smulInst; BInner 𝒷 W :=
  letI := hW.smulInst
  { inner := fun x y => ipVal B (x : UnCompl B) (y : UnCompl B)
    inner_add_right := fun x y z =>
      ipVal_add_right (hW.hasIP x.2 y.2) (hW.hasIP x.2 z.2)
    inner_op_smul_right := fun b x y => hW.ipVal_op_smul_right b x.2 y.2
    inner_smul_right_complex := fun c x y => ipVal_smul_right c (hW.hasIP x.2 y.2)
    star_inner := fun x y => (ipVal_symm (hW.hasIP x.2 y.2)).symm
    inner_self_nonneg := fun x => ipVal_self_nonneg B (hW.hasIP x.2 x.2) }

/-- Cauchy–Schwarz (**142V**.1) on a compatible extension. -/
theorem IsCompatExt.norm_ipVal_le {W : Submodule ℂ (UnCompl B)}
    (hW : IsCompatExt B W) {x y : UnCompl B} (hx : x ∈ W) (hy : y ∈ W) :
    ‖ipVal B x y‖ ≤ Real.sqrt ‖ipVal B x x‖ * Real.sqrt ‖ipVal B y y‖ := by
  letI := hW.smulInst
  exact module_seminorm_1 hW.binner ⟨x, hx⟩ ⟨y, hy⟩

/-! ### Norm-boundedness in the extended seminorms

The thesis's `σ(W)` collects the limits of **norm-bounded** Cauchy nets over
`W`, and the norm is the one of `W`'s own inner product.  We phrase the
bound in the extended seminorms instead: `‖x‖ ≤ M` is `[x,x] ≤ M²·1`, which
by order separation of the np-functionals (**44XI**) is
`ω[x,x] ≤ M²ω(1)`, i.e. `‖x‖_ω ≤ M(ω 1)^½`.  This makes sense on all of `V̄`,
and needs neither an inner product nor a supremum. -/

variable (B)

private theorem np_re_le_norm (ω : NPFunctional 𝒷) {a : 𝒷} (ha : IsSelfAdjoint a) :
    (ω a).re ≤ ‖a‖ * (ω 1).re := by
  have h2 := npFunctional_mono ω ha.le_algebraMap_norm_self
  rw [algebraMap_real_eq, Algebra.algebraMap_eq_smul_one, npf_smul_complex] at h2
  simpa [Complex.mul_re] using (Complex.le_def.mp h2).1

private theorem np_one_re_nonneg (ω : NPFunctional 𝒷) : (0 : ℝ) ≤ (ω 1).re :=
  npf_re_nonneg' ω zero_le_one

/-- `‖x‖ ≤ M`, phrased in the extended seminorms only. -/
def SemBddBy (M : ℝ) (x : UnCompl B) : Prop :=
  ∀ ω : NPFunctional 𝒷, semC B ω x ≤ M * Real.sqrt ((ω 1).re)

variable {B}

theorem SemBddBy.add {M N : ℝ} {x y : UnCompl B} (hx : SemBddBy B M x)
    (hy : SemBddBy B N y) : SemBddBy B (M + N) (x + y) := fun ω => by
  have h := semC_add_le B ω x y
  have h1 := hx ω
  have h2 := hy ω
  rw [add_mul]
  linarith

theorem SemBddBy.smul {M : ℝ} {x : UnCompl B} (c : ℂ) (hx : SemBddBy B M x) :
    SemBddBy B (‖c‖ * M) (c • x) := fun ω => by
  rw [semC_smul_complex, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hx ω) (norm_nonneg c)

theorem SemBddBy.op_smul {M : ℝ} {x : UnCompl B} (b : 𝒷) (hM : 0 ≤ M)
    (hx : SemBddBy B M x) : SemBddBy B (M * ‖b‖) (b • x) := fun ω => by
  rw [semC_op_smul]
  have h2 : ((conjNP (star b) ω) 1).re ≤ ‖b‖ ^ 2 * (ω 1).re := by
    rw [conjNP_apply, star_star, mul_one]
    have hsa : IsSelfAdjoint (b * star b) := by
      simp [IsSelfAdjoint, star_mul, star_star]
    have h3 := np_re_le_norm ω hsa
    have hn : ‖b * star b‖ = ‖b‖ ^ 2 := by
      rw [CStarRing.norm_self_mul_star]; ring
    rwa [hn] at h3
  calc semC B (conjNP (star b) ω) x
      ≤ M * Real.sqrt (((conjNP (star b) ω) 1).re) := hx _
    _ ≤ M * Real.sqrt (‖b‖ ^ 2 * (ω 1).re) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) hM
    _ = M * ‖b‖ * Real.sqrt ((ω 1).re) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg b), mul_assoc]

theorem SemBddBy.mono {M N : ℝ} {x : UnCompl B} (hMN : M ≤ N)
    (hx : SemBddBy B M x) : SemBddBy B N x := fun ω =>
  (hx ω).trans (mul_le_mul_of_nonneg_right hMN (Real.sqrt_nonneg _))

/-- On a compatible extension, `SemBddBy` *is* the norm bound: every element
is bounded by its own norm … -/
theorem IsCompatExt.semBddBy_of_mem {W : Submodule ℂ (UnCompl B)}
    (hW : IsCompatExt B W) {x : UnCompl B} (hx : x ∈ W) :
    SemBddBy B (Real.sqrt ‖ipVal B x x‖) x := fun ω => by
  have h := hW.hasIP hx hx
  have hsa : IsSelfAdjoint (ipVal B x x) := (ipVal_symm h).symm
  have h1 : ((semC B ω x ^ 2 : ℝ) : ℂ) = ω (ipVal B x x) := by
    rw [ipVal_spec B h ω, ipf_self]
  have h1' : semC B ω x ^ 2 = (ω (ipVal B x x)).re := by
    rw [← h1]; exact (Complex.ofReal_re _).symm
  have h2 : (ω (ipVal B x x)).re ≤ ‖ipVal B x x‖ * (ω 1).re := np_re_le_norm ω hsa
  have h3 : semC B ω x ^ 2
      ≤ (Real.sqrt ‖ipVal B x x‖ * Real.sqrt ((ω 1).re)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), Real.sq_sqrt (np_one_re_nonneg ω)]
    rw [h1']; exact h2
  nlinarith [semC_nonneg B ω x,
    mul_nonneg (Real.sqrt_nonneg ‖ipVal B x x‖) (Real.sqrt_nonneg ((ω 1).re))]

/-- … and conversely a `SemBddBy M` element of a compatible extension has
`‖[x,x]‖ ≤ M²‖1‖`. -/
theorem IsCompatExt.norm_ipVal_self_le {W : Submodule ℂ (UnCompl B)}
    (hW : IsCompatExt B W) {x : UnCompl B} (hx : x ∈ W) {M : ℝ}
    (hb : SemBddBy B M x) : ‖ipVal B x x‖ ≤ M ^ 2 * ‖(1 : 𝒷)‖ := by
  have h := hW.hasIP hx hx
  have hsa : IsSelfAdjoint (ipVal B x x) := (ipVal_symm h).symm
  have hsa2 : IsSelfAdjoint (((M ^ 2 : ℝ) : ℂ) • (1 : 𝒷)) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← algebraMap_real_eq]
    exact isSelfAdjoint_algebraMap_ofReal _
  have hle : ipVal B x x ≤ ((M ^ 2 : ℝ) : ℂ) • (1 : 𝒷) := by
    refine np_orderSeparating _ _ hsa hsa2 fun ω => ?_
    rw [ipVal_spec B h ω, ipf_self, npf_smul_complex, Complex.le_def]
    have hsq : semC B ω x ^ 2 ≤ M ^ 2 * (ω 1).re := by
      have h1 := hb ω
      have h2 : (0 : ℝ) ≤ semC B ω x := semC_nonneg B ω x
      have h3 : Real.sqrt ((ω 1).re) ^ 2 = (ω 1).re :=
        Real.sq_sqrt (np_one_re_nonneg ω)
      nlinarith [Real.sqrt_nonneg ((ω 1).re)]
    have him : (ω (1 : 𝒷)).im = 0 := by
      have := (Complex.le_def.mp (npFunctional_nonneg ω (zero_le_one (α := 𝒷)))).2
      simpa using this.symm
    refine ⟨?_, ?_⟩
    · rw [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact hsq
    · rw [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, him, mul_zero]
  calc ‖ipVal B x x‖ ≤ ‖((M ^ 2 : ℝ) : ℂ) • (1 : 𝒷)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le (ipVal_self_nonneg B h) hle
    _ = M ^ 2 * ‖(1 : 𝒷)‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ M ^ 2)]

/-! ### The σ-closure (**150XIII**) -/

variable (B)

/-- **150XIII**: `σ(W)`, the set of limits in `V̄` of norm-bounded nets over
`W`.  Nets are replaced by closures of norm-bounded slices, which is the
same thing and avoids the thesis's fast-net reduction (**150V**). -/
def SigmaCl (W : Submodule ℂ (UnCompl B)) : Set (UnCompl B) :=
  {x | ∃ M : ℝ, 0 ≤ M ∧ x ∈ closure ((W : Set (UnCompl B)) ∩ {z | SemBddBy B M z})}

variable {B}

theorem subset_sigmaCl {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W) :
    (W : Set (UnCompl B)) ⊆ SigmaCl B W := fun x hx =>
  ⟨Real.sqrt ‖ipVal B x x‖, Real.sqrt_nonneg _,
    subset_closure ⟨hx, hW.semBddBy_of_mem hx⟩⟩

/-- `σ(W)` is again a ℂ-submodule of `V̄`: the operations are (uniformly)
continuous and multiply the bounds. -/
noncomputable def sigmaSubmodule {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W) :
    Submodule ℂ (UnCompl B) where
  carrier := SigmaCl B W
  zero_mem' := subset_sigmaCl hW W.zero_mem
  add_mem' := by
    rintro x y ⟨M, hM, hx⟩ ⟨N, hN, hy⟩
    exact ⟨M + N, by linarith, map_mem_closure₂ continuous_add hx hy
      fun a ha b hb => ⟨W.add_mem ha.1 hb.1, ha.2.add hb.2⟩⟩
  smul_mem' := by
    rintro c x ⟨M, hM, hx⟩
    exact ⟨‖c‖ * M, by positivity, map_mem_closure (continuous_const_smul c) hx
      fun a ha => ⟨W.smul_mem c ha.1, ha.2.smul c⟩⟩

@[simp] theorem mem_sigmaSubmodule {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W)
    {x : UnCompl B} : x ∈ sigmaSubmodule hW ↔ x ∈ SigmaCl B W := Iff.rfl

set_option maxHeartbeats 1000000 in
/-- The inner product extends to `σ(W)`.  This is the analytic heart of
**150XIII**: the net `[x_α, y_α]` is norm-bounded by Cauchy–Schwarz and
*converges* under every np-functional, because `ipf` is jointly continuous;
so it has an ultraweak limit by **77I**.2 `vn_complete_2`. -/
theorem sigmaCl_hasIP {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W)
    {x y : UnCompl B} (hx : x ∈ SigmaCl B W) (hy : y ∈ SigmaCl B W) :
    HasIP B x y := by
  classical
  obtain ⟨M, hM, hx⟩ := hx
  obtain ⟨N, hN, hy⟩ := hy
  set S₁ := (W : Set (UnCompl B)) ∩ {z | SemBddBy B M z} with hS₁
  set S₂ := (W : Set (UnCompl B)) ∩ {z | SemBddBy B N z} with hS₂
  set F : Filter (UnCompl B × UnCompl B) := 𝓝 (x, y) ⊓ 𝓟 (S₁ ×ˢ S₂) with hFdef
  have hmem : (S₁ ×ˢ S₂) ∈ F := mem_inf_of_right (mem_principal_self _)
  haveI hne : F.NeBot := by
    have hcl : (x, y) ∈ closure (S₁ ×ˢ S₂) := by
      rw [closure_prod_eq]; exact ⟨hx, hy⟩
    exact mem_closure_iff_clusterPt.mp hcl
  set g : UnCompl B × UnCompl B → 𝒷 :=
    fun p => if p ∈ S₁ ×ˢ S₂ then ipVal B p.1 p.2 else 0 with hg
  set C : ℝ := Real.sqrt (M ^ 2 * ‖(1 : 𝒷)‖) * Real.sqrt (N ^ 2 * ‖(1 : 𝒷)‖) with hC
  have hCnn : (0 : ℝ) ≤ C := by positivity
  have hbdd : ∀ p, ‖g p‖ ≤ C := by
    intro p
    by_cases hp : p ∈ S₁ ×ˢ S₂
    · rw [hg]
      simp only [if_pos hp]
      refine (hW.norm_ipVal_le hp.1.1 hp.2.1).trans ?_
      exact mul_le_mul
        (Real.sqrt_le_sqrt (hW.norm_ipVal_self_le hp.1.1 hp.1.2))
        (Real.sqrt_le_sqrt (hW.norm_ipVal_self_le hp.2.1 hp.2.2))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · rw [hg]; simp only [if_neg hp, norm_zero]; exact hCnn
  have htend : ∀ ω : NPFunctional 𝒷,
      Tendsto (fun p => ω (g p)) F (𝓝 (ipf B ω x y)) := by
    intro ω
    have h0 : Tendsto (fun p : UnCompl B × UnCompl B => ipf B ω p.1 p.2) (𝓝 (x, y))
        (𝓝 (ipf B ω x y)) := (continuous_ipf B ω).tendsto (x, y)
    have h1 : Tendsto (fun p : UnCompl B × UnCompl B => ipf B ω p.1 p.2) F
        (𝓝 (ipf B ω x y)) := h0.mono_left inf_le_left
    refine h1.congr' ?_
    filter_upwards [hmem] with p hp
    rw [hg]
    simp only [if_pos hp]
    exact (ipVal_spec B (hW.hasIP hp.1.1 hp.2.1) ω).symm
  obtain ⟨a, ha⟩ := vn_complete_2 F g ⟨C, hbdd⟩ fun ω => (htend ω).cauchy_map
  exact ⟨a, fun ω => tendsto_nhds_unique ((uwTendsto_iff g F a).mp ha ω) (htend ω)⟩

/-- **150XIII**: `σ(W)` is again a compatible extension. -/
theorem IsCompatExt.sigma {W : Submodule ℂ (UnCompl B)} (hW : IsCompatExt B W) :
    IsCompatExt B (sigmaSubmodule hW) where
  unEta_mem v := subset_sigmaCl hW (hW.unEta_mem v)
  op_smul_mem b x hx := by
    obtain ⟨M, hM, hx⟩ := hx
    exact ⟨M * ‖b‖, by positivity, map_mem_closure (continuous_const_smul b) hx
      fun a ha => ⟨hW.op_smul_mem b ha.1, ha.2.op_smul b hM⟩⟩
  hasIP _ _ hx hy := sigmaCl_hasIP hW hx hy

/-! ### The base case, the limit step, and Zorn (**150XII**, **150XIV**, **150XV**) -/

variable (B)

/-- `η : V → V̄` as a ℂ-linear map. -/
noncomputable def unEtaL : V →ₗ[ℂ] UnCompl B where
  toFun := unEta B
  map_add' := unEta_add B
  map_smul' c v := unEta_smul_complex B c v

/-- **150XII** (induction base case): `V₀ = η(V)` is a compatible extension.
It needs no quotient: `V̄` is the *separated* completion, so `η` already
identifies the vectors the thesis has to quotient out. -/
theorem isCompatExt_range : IsCompatExt B (LinearMap.range (unEtaL B)) where
  unEta_mem v := ⟨v, rfl⟩
  op_smul_mem b x hx := by
    obtain ⟨v, rfl⟩ := hx
    exact ⟨b • v, unEta_op_smul B b v⟩
  hasIP x y hx hy := by
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact hasIP_unEta B v w

/-- **150XIV** (limit step) and **150XV**: Zorn's lemma gives a maximal
compatible extension, and by maximality it is σ-closed.  The thesis's limit
step — carrying the inner product along the union of a chain — is here the
observation that a union of a chain of submodules is a submodule, since the
inner product is determined by the set. -/
theorem exists_maximal_compatExt :
    ∃ W : Submodule ℂ (UnCompl B),
      IsCompatExt B W ∧ SigmaCl B W ⊆ (W : Set (UnCompl B)) := by
  have hbound : ∀ c ⊆ {W : Submodule ℂ (UnCompl B) | IsCompatExt B W},
      IsChain (· ≤ ·) c →
      ∃ ub ∈ {W : Submodule ℂ (UnCompl B) | IsCompatExt B W}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨LinearMap.range (unEtaL B), isCompatExt_range B, by simp⟩
    obtain ⟨W₀, hW₀⟩ := hne
    have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
    have hmem : ∀ x : UnCompl B, x ∈ sSup c ↔ ∃ W' ∈ c, x ∈ W' := fun x =>
      Submodule.mem_sSup_of_directed ⟨W₀, hW₀⟩ hdir
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    exact
      { unEta_mem := fun v => (hmem _).mpr ⟨W₀, hW₀, (hc hW₀).unEta_mem v⟩
        op_smul_mem := fun b x hx => by
          obtain ⟨W', hW', hxW'⟩ := (hmem x).mp hx
          exact (hmem _).mpr ⟨W', hW', (hc hW').op_smul_mem b hxW'⟩
        hasIP := fun x y hx hy => by
          obtain ⟨W₁, h₁, hx₁⟩ := (hmem x).mp hx
          obtain ⟨W₂, h₂, hy₂⟩ := (hmem y).mp hy
          obtain ⟨W₃, h₃, hle₁, hle₂⟩ := hdir W₁ h₁ W₂ h₂
          exact (hc h₃).hasIP (hle₁ hx₁) (hle₂ hy₂) }
  obtain ⟨W, hW⟩ := zorn_le₀ {W : Submodule ℂ (UnCompl B) | IsCompatExt B W} hbound
  refine ⟨W, hW.1, fun x hx => ?_⟩
  exact hW.2 hW.1.sigma (subset_sigmaCl hW.1) hx

end SigmaClosure

/-! ## Parsec 1500 concluded: the carrier of the completion, and **150II**

A maximal compatible extension `W ⊆ V̄` (`exists_maximal_compatExt`) is
turned into a self-dual *Hilbert* 𝒷-module.  What has to be produced is a
`NormedAddCommGroup`, a `NormedSpace ℂ`, a `CStarModule 𝒷` (**141II**),
completeness of the *norm* (which **149V** does not supply), self-duality
(**149V**.3 ⇒ .1, through `BddUnComplete`), and the embedding `η` with
ultranorm dense image.

Two devices carry all of it.  `exists_semC_entourage_subset` says the
extended seminorms **generate** the uniformity of `V̄` — the transfer
between the two Cauchy notions that everything below needs.  And a
compatible extension is *bundled* into `CompatExt`, so that the structures
on its carrier can be genuine instances rather than `letI`s depending on a
proof. -/

section CompletionCarrier

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷] [VonNeumannAlgebra 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]
variable (B : BInner 𝒷 V)

/-- The extended seminorms **generate** the uniformity of `V̄`: every
entourage contains one of the thesis's entourages (**146V**.3 / **146VII**),
now phrased with the extended seminorms `semC`.  This is the claim of
**150X**, in the direction the construction needs. -/
theorem exists_semC_entourage_subset {S : Set (UnCompl B × UnCompl B)}
    (hS : S ∈ 𝓤 (UnCompl B)) :
    ∃ (s : Finset (NPFunctional 𝒷)) (r : ℝ), 0 < r ∧
      {p : UnCompl B × UnCompl B | ∀ ω ∈ s, semC B ω (p.2 - p.1) < r} ⊆ S := by
  classical
  obtain ⟨T, ⟨hT, hTcl⟩, hTS⟩ := uniformity_hasBasis_closed.mem_iff.mp hS
  have hpre : (fun q : UnUnif B × UnUnif B => ((q.1 : UnCompl B), (q.2 : UnCompl B))) ⁻¹' T
      ∈ 𝓤 (UnUnif B) := by
    rw [← (UniformSpace.Completion.isUniformInducing_coe (UnUnif B)).comap_uniformity]
    exact preimage_mem_comap hT
  obtain ⟨⟨s, r⟩, hr, hsub⟩ := (UnUnif.hasBasis_uniformity B).mem_iff.mp hpre
  simp only at hr hsub
  refine ⟨s, r, hr, ?_⟩
  set U : Set (UnCompl B × UnCompl B) :=
    {p : UnCompl B × UnCompl B | ∀ ω ∈ s, semC B ω (p.2 - p.1) < r} with hU
  have hUopen : IsOpen U := by
    rw [hU]
    simpa only [Set.ofPred_forall] using
      isOpen_biInter_finset (s := s) (f := fun ω =>
        {p : UnCompl B × UnCompl B | semC B ω (p.2 - p.1) < r})
        fun ω _ => isOpen_lt ((continuous_semC B ω).comp (continuous_snd.sub continuous_fst))
          continuous_const
  set R : Set (UnCompl B × UnCompl B) :=
    Set.range (fun q : UnUnif B × UnUnif B => ((q.1 : UnCompl B), (q.2 : UnCompl B))) with hR
  have hRdense : Dense R :=
    ((UniformSpace.Completion.denseRange_coe (α := UnUnif B)).prodMap
      (UniformSpace.Completion.denseRange_coe (α := UnUnif B)))
  have hUR : U ∩ R ⊆ T := by
    rintro ⟨x, y⟩ ⟨hxy, ⟨⟨a, b⟩, hab⟩⟩
    obtain ⟨rfl, rfl⟩ : x = (a : UnCompl B) ∧ y = (b : UnCompl B) := by
      exact ⟨(congrArg Prod.fst hab).symm, (congrArg Prod.snd hab).symm⟩
    have hlt : (s.sup (UnUnif.sem B)) (b - a) < r := by
      refine Seminorm.finset_sup_apply_lt hr fun ω hω => ?_
      have := hxy ω hω
      rwa [← UniformSpace.Completion.coe_sub, semC_coe] at this
    exact hsub (show ((a, b) : UnUnif B × UnUnif B) ∈ _ from hlt)
  calc U ⊆ closure (U ∩ R) := hRdense.open_subset_closure_inter hUopen
    _ ⊆ closure T := closure_mono hUR
    _ = T := hTcl.closure_eq
    _ ⊆ S := hTS

/-- A filter on `V̄` which is Cauchy for the extended seminorms is Cauchy. -/
theorem cauchy_of_semC {F : Filter (UnCompl B)} (hne : F.NeBot)
    (h : ∀ (ω : NPFunctional 𝒷) (ε : ℝ), 0 < ε →
      ∃ t ∈ F, ∀ x ∈ t, ∀ y ∈ t, semC B ω (x - y) ≤ ε) :
    Cauchy F := by
  classical
  refine ⟨hne, fun S hS => ?_⟩
  obtain ⟨s, r, hr, hsub⟩ := exists_semC_entourage_subset B hS
  choose t htF ht using fun ω : NPFunctional 𝒷 => h ω (r / 2) (by positivity)
  refine Filter.mem_prod_iff.mpr ⟨⋂ ω ∈ s, t ω, (Filter.biInter_finset_mem s).mpr
    fun ω _ => htF ω, ⋂ ω ∈ s, t ω, (Filter.biInter_finset_mem s).mpr fun ω _ => htF ω, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  rw [Set.mem_iInter₂] at hx hy
  refine hsub fun ω hω => ?_
  have := ht ω y (hy ω hω) x (hx ω hω)
  linarith

variable {B}


/-- A compatible extension, **bundled**. -/
structure CompatExt (B : BInner 𝒷 V) : Type v where
  /-- The underlying submodule of `V̄`. -/
  carrier : Submodule ℂ (UnCompl B)
  /-- It is a compatible extension. -/
  isCompat : IsCompatExt B carrier

namespace CompatExt

/-- The carrier of a compatible extension, as a **type synonym** of `↥W`. -/
def Car (E : CompatExt B) : Type v := E.carrier

variable {E : CompatExt B}

/-- The underlying element of `V̄`. -/
def val (x : E.Car) : UnCompl B := Subtype.val x

omit [VonNeumannAlgebra 𝒷] in
theorem val_mem (x : E.Car) : val x ∈ E.carrier := Subtype.property x

omit [VonNeumannAlgebra 𝒷] in
theorem val_injective : Function.Injective (val (E := E)) := Subtype.val_injective

/-- An element of `W`, as an element of the carrier. -/
def ofMem (x : UnCompl B) (hx : x ∈ E.carrier) : E.Car := ⟨x, hx⟩

theorem hasIP (x y : E.Car) : HasIP B (val x) (val y) :=
  E.isCompat.hasIP (val_mem x) (val_mem y)

/-- The norm `‖x‖ = ‖[x,x]‖^½` of the carrier. -/
noncomputable def nrm (x : E.Car) : ℝ := Real.sqrt ‖ipVal B (val x) (val x)‖

private theorem ipVal_neg_neg {v : UnCompl B} (h : HasIP B v v) :
    ipVal B (-v) (-v) = ipVal B v v := by
  rw [show -v = (-1 : ℂ) • v by simp, ipVal_smul_left _ (h.smul_right (-1)),
    ipVal_smul_right _ h]
  simp

noncomputable instance : NormedAddCommGroup E.Car :=
  letI : AddCommGroup E.Car := inferInstanceAs (AddCommGroup E.carrier)
  letI : Module ℂ E.Car := inferInstanceAs (Module ℂ E.carrier)
  letI := E.isCompat.smulInst
  have key := @module_seminorm_2 𝒷 ↥E.carrier _ _ _ _ _ E.isCompat.smulInst
    E.isCompat.binner
  AddGroupNorm.toNormedAddCommGroup
    { toFun := nrm
      map_zero' := by
        show Real.sqrt ‖ipVal B (val (0 : E.Car)) (val (0 : E.Car))‖ = 0
        rw [show val (0 : E.Car) = 0 from rfl, ipVal_zero_right]
        simp
      add_le' := fun x y => (key x y 1 1).1
      neg' := fun x => by
        show Real.sqrt ‖ipVal B (val (-x)) (val (-x))‖
          = Real.sqrt ‖ipVal B (val x) (val x)‖
        rw [show val (-x) = -val x from rfl, ipVal_neg_neg (hasIP x x)]
      eq_zero_of_map_eq_zero' := fun x hx => by
        have hx' : Real.sqrt ‖ipVal B (val x) (val x)‖ = 0 := hx
        have h0 : ‖ipVal B (val x) (val x)‖ = 0 := by
          nlinarith [Real.sq_sqrt (norm_nonneg (ipVal B (val x) (val x))),
            norm_nonneg (ipVal B (val x) (val x))]
        exact val_injective (by
          rw [show val (0 : E.Car) = 0 from rfl]
          exact eq_zero_of_ipVal_self_eq_zero B (hasIP x x) (norm_eq_zero.mp h0)) }

noncomputable instance : Module ℂ E.Car := inferInstanceAs (Module ℂ E.carrier)

noncomputable instance : SMul 𝒷 E.Car where
  smul b x := ofMem (b • val x) (E.isCompat.op_smul_mem b (val_mem x))

omit [VonNeumannAlgebra 𝒷] in
@[simp] theorem val_ofMem (x : UnCompl B) (hx : x ∈ E.carrier) : val (ofMem x hx) = x := rfl
@[simp] theorem val_add (x y : E.Car) : val (x + y) = val x + val y := rfl
@[simp] theorem val_sub (x y : E.Car) : val (x - y) = val x - val y := rfl
@[simp] theorem val_neg (x : E.Car) : val (-x) = -val x := rfl
@[simp] theorem val_zero : val (0 : E.Car) = 0 := rfl
@[simp] theorem val_smul (c : ℂ) (x : E.Car) : val (c • x) = c • val x := rfl
@[simp] theorem val_op_smul (b : 𝒷) (x : E.Car) : val (b • x) = b • val x := rfl

theorem norm_def (x : E.Car) : ‖x‖ = Real.sqrt ‖ipVal B (val x) (val x)‖ := rfl

noncomputable instance : NormedSpace ℂ E.Car where
  norm_smul_le c x :=
    le_of_eq (@module_seminorm_2 𝒷 ↥E.carrier _ _ _ _ _ E.isCompat.smulInst
      E.isCompat.binner x x c 1).2.1

noncomputable instance : CStarModule 𝒷 E.Car where
  inner x y := ipVal B (val x) (val y)
  inner_add_right := ipVal_add_right (hasIP _ _) (hasIP _ _)
  inner_self_nonneg := ipVal_self_nonneg B (hasIP _ _)
  inner_self := by
    intro x
    constructor
    · intro h
      exact val_injective (by
        rw [show val (0 : E.Car) = 0 from rfl]
        exact eq_zero_of_ipVal_self_eq_zero B (hasIP x x) h)
    · rintro rfl
      rw [show val (0 : E.Car) = 0 from rfl, ipVal_zero_right]
  inner_op_smul_right := E.isCompat.ipVal_op_smul_right _ (val_mem _) (val_mem _)
  inner_smul_right_complex := ipVal_smul_right _ (hasIP _ _)
  star_inner x y := (ipVal_symm (hasIP x y)).symm
  norm_eq_sqrt_norm_inner_self x := rfl

@[simp] theorem inner_eq (x y : E.Car) : (inner 𝒷 x y : 𝒷) = ipVal B (val x) (val y) := rfl


/-! ### The carrier is ultranorm complete and norm complete -/

/-- Clause 4 of **150XI**: on a compatible extension the module's own
ultranorm seminorms *are* the extended seminorms of `V̄`. -/
theorem unSeminorm_eq_semC (ω : NPFunctional 𝒷) (x : E.Car) :
    unSeminorm ω (inner 𝒷 : E.Car → E.Car → 𝒷) x = semC B ω (val x) := by
  have h : (ω (inner 𝒷 x x : 𝒷)) = ((semC B ω (val x) ^ 2 : ℝ) : ℂ) := by
    rw [inner_eq, ipVal_spec B (hasIP x x) ω, ipf_self]
  rw [unSeminorm, h, Complex.ofReal_re, Real.sqrt_sq (semC_nonneg B ω (val x))]

theorem semBddBy_val (x : E.Car) : SemBddBy B ‖x‖ (val x) :=
  E.isCompat.semBddBy_of_mem (val_mem x)

/-- **146IX** in the present setting: `‖x‖_ω ≤ ‖x‖ · ω(1)^½` — the
quantitative half of the Beware, as in `unSeminorm_le_norm_mul`.  (Earlier
revisions of this file labelled it 148V, which is `innerprod_ultraweak`.) -/
theorem unSeminorm_le (ω : NPFunctional 𝒷) (x : E.Car) :
    unSeminorm ω (inner 𝒷 : E.Car → E.Car → 𝒷) x ≤ ‖x‖ * Real.sqrt ((ω 1).re) := by
  rw [unSeminorm_eq_semC]; exact semBddBy_val x ω

/-- Conversely a bound in the extended seminorms is a norm bound (up to the
harmless factor `‖1‖`, which is `1` unless `𝒷 = {0}`). -/
theorem norm_le_of_semBddBy {x : E.Car} {M : ℝ} (hM : 0 ≤ M)
    (h : SemBddBy B M (val x)) : ‖x‖ ≤ M * Real.sqrt ‖(1 : 𝒷)‖ := by
  have h1 := E.isCompat.norm_ipVal_self_le (val_mem x) h
  rw [norm_def]
  calc Real.sqrt ‖ipVal B (val x) (val x)‖ ≤ Real.sqrt (M ^ 2 * ‖(1 : 𝒷)‖) :=
        Real.sqrt_le_sqrt h1
    _ = M * Real.sqrt ‖(1 : 𝒷)‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM]

/-- **149V**.3 for the carrier: every norm-bounded ultranorm-Cauchy filter
converges.  This is where σ-closedness of the extension is used: the limit
in `V̄` of a norm-bounded net over `W` lies in `σ(W) = W`. -/
theorem bddUnComplete (hσ : SigmaCl B E.carrier ⊆ (E.carrier : Set (UnCompl B))) :
    BddUnComplete 𝒷 E.Car := by
  classical
  rintro F hne hcau ⟨M, s, hsF, hs⟩
  have := hne
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hne.nonempty_of_mem hsF
    exact le_trans (norm_nonneg x) (hs x hx)
  have hGcau : Cauchy (Filter.map (val (E := E)) F) := by
    refine cauchy_of_semC B (hne.map _) fun ω ε hε => ?_
    obtain ⟨t, htF, ht⟩ := hcau ω ε hε
    refine ⟨val '' t, Filter.image_mem_map htF, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := ht x hx y hy
    rwa [unSeminorm_eq_semC, val_sub] at h
  obtain ⟨x₀, hx₀⟩ := CompleteSpace.complete hGcau
  have htend : Tendsto (val (E := E)) F (𝓝 x₀) := hx₀
  have hmem : x₀ ∈ E.carrier := by
    refine hσ ⟨M, hM, mem_closure_of_tendsto htend ?_⟩
    filter_upwards [hsF] with x hx
    exact ⟨val_mem x, (semBddBy_val x).mono (hs x hx)⟩
  refine ⟨ofMem x₀ hmem, fun ω => ?_⟩
  have hcont : Continuous fun z : UnCompl B => semC B ω (z - x₀) :=
    (continuous_semC B ω).comp (continuous_id.sub continuous_const)
  have h1 : Tendsto (fun x : E.Car => semC B ω (val x - x₀)) F
      (𝓝 (semC B ω (x₀ - x₀))) := (hcont.tendsto x₀).comp htend
  rw [sub_self, semC_zero] at h1
  refine h1.congr fun x => ?_
  rw [unSeminorm_eq_semC, val_sub, val_ofMem]
  rfl

/-- The carrier is **norm** complete — the last field of a Hilbert
𝒷-module, and one that **149V** does not supply.

**A step missing from the printed proof of 150XV** (recorded here, not
repaired: nothing in the tree is wrong).  150XV concludes `W = V̄` from
"completeness", and the completeness it has in hand is *ultranorm*
completeness — which is all that `dils-selfdual` (**149V**) delivers.  But
"Hilbert 𝒷-module" also demands completeness for the **norm**
`‖x‖ = ‖⟨x,x⟩‖^½`, and no clause of 149V supplies that; so it is proved
separately here.

Route: a norm-Cauchy filter is ultranorm-Cauchy and norm-bounded
(**146IX**, `unSeminorm_le`), so it has an ultranorm limit `x₀`; and the
estimate `‖x − x₀‖_ω ≤ ε·ω(1)^½` obtained by inserting a net element gives
`‖x − x₀‖ ≤ ε‖1‖^½` by order separation. -/
theorem completeSpace (hσ : SigmaCl B E.carrier ⊆ (E.carrier : Set (UnCompl B))) :
    CompleteSpace E.Car := by
  classical
  set c : ℝ := Real.sqrt ‖(1 : 𝒷)‖ with hc
  have hc0 : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  refine ⟨?_⟩
  intro F hF
  have := hF.1
  have hmet := Metric.cauchy_iff.mp hF
  have huc : UnCauchy (inner 𝒷 : E.Car → E.Car → 𝒷) F := by
    intro ω ε hε
    have hd0 : (0 : ℝ) ≤ Real.sqrt ((ω 1).re) := Real.sqrt_nonneg _
    obtain ⟨t, htF, ht⟩ := hmet.2 (ε / (Real.sqrt ((ω 1).re) + 1)) (by positivity)
    refine ⟨t, htF, fun x hx y hy => ?_⟩
    have h1 : ‖x - y‖ < ε / (Real.sqrt ((ω 1).re) + 1) := by
      rw [← dist_eq_norm]; exact ht x hx y hy
    have h2 := unSeminorm_le ω (x - y)
    have h3 : ‖x - y‖ * Real.sqrt ((ω 1).re) ≤ ε := by
      have h4 : ‖x - y‖ * (Real.sqrt ((ω 1).re) + 1) ≤ ε :=
        ((lt_div_iff₀ (by positivity)).mp h1).le
      nlinarith [norm_nonneg (x - y)]
    linarith
  have hbdd : ∃ M : ℝ, ∃ s ∈ F, ∀ x ∈ s, ‖x‖ ≤ M := by
    obtain ⟨t, htF, ht⟩ := hmet.2 1 one_pos
    obtain ⟨x₁, hx₁⟩ := hF.1.nonempty_of_mem htF
    refine ⟨‖x₁‖ + 1, t, htF, fun x hx => ?_⟩
    have h1 : ‖x - x₁‖ < 1 := by rw [← dist_eq_norm]; exact ht x hx x₁ hx₁
    calc ‖x‖ = ‖x₁ + (x - x₁)‖ := by rw [show x₁ + (x - x₁) = x by abel]
      _ ≤ ‖x₁‖ + ‖x - x₁‖ := norm_add_le _ _
      _ ≤ ‖x₁‖ + 1 := by linarith
  obtain ⟨x₀, hx₀⟩ := bddUnComplete hσ F hF.1 huc hbdd
  refine ⟨x₀, (Metric.nhds_basis_ball (x := x₀)).ge_iff.mpr fun ε hε => ?_⟩
  have hε'0 : (0 : ℝ) < ε / (2 * (c + 1)) := by positivity
  obtain ⟨t, htF, ht⟩ := hmet.2 (ε / (2 * (c + 1))) hε'0
  filter_upwards [htF] with x hx
  have hsb : SemBddBy B (ε / (2 * (c + 1))) (val (x - x₀)) := by
    intro ω
    have hd0 : (0 : ℝ) ≤ Real.sqrt ((ω 1).re) := Real.sqrt_nonneg _
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨y, hy, hyt⟩ :=
      (((tendsto_order.mp (hx₀ ω)).2 η hη).and (Filter.eventually_mem_set.mpr htF)).exists
    have h1 : semC B ω (val (x - x₀))
        ≤ semC B ω (val x - val y) + semC B ω (val y - val x₀) := by
      have := semC_add_le B ω (val x - val y) (val y - val x₀)
      rw [show val x - val y + (val y - val x₀) = val (x - x₀) by
        rw [val_sub]; abel] at this
      exact this
    have h2 : semC B ω (val x - val y) ≤ (ε / (2 * (c + 1))) * Real.sqrt ((ω 1).re) := by
      have h3 := unSeminorm_le ω (x - y)
      rw [unSeminorm_eq_semC, val_sub] at h3
      have h4 : ‖x - y‖ < ε / (2 * (c + 1)) := by
        rw [← dist_eq_norm]; exact ht x hx y hyt
      nlinarith
    have h5 : semC B ω (val y - val x₀) < η := by
      have h6 := hy
      rwa [unSeminorm_eq_semC, val_sub] at h6
    linarith
  have hnorm := norm_le_of_semBddBy hε'0.le hsb
  rw [Metric.mem_ball, dist_eq_norm]
  have : ‖x - x₀‖ ≤ ε / (2 * (c + 1)) * c := by
    have hval : val (x - x₀) = val (x - x₀) := rfl
    exact hnorm
  have hlt : ε / (2 * (c + 1)) * c < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith


/-! ### `η` and the universal property -/

variable (E)

/-- `η : V → X`, the embedding of `V` into the carrier. -/
noncomputable def eta (v : V) : E.Car := ofMem (unEta B v) (E.isCompat.unEta_mem v)

variable {E}

omit [VonNeumannAlgebra 𝒷] in
@[simp] theorem val_eta (v : V) : val (eta E v) = unEta B v := rfl

theorem eta_add (v w : V) : eta E (v + w) = eta E v + eta E w :=
  val_injective (by rw [val_eta, val_add, val_eta, val_eta, unEta_add])

theorem eta_smul_complex (c : ℂ) (v : V) : eta E (c • v) = c • eta E v :=
  val_injective (by rw [val_eta, val_smul, val_eta, unEta_smul_complex])

theorem eta_op_smul (b : 𝒷) (v : V) : eta E (b • v) = b • eta E v :=
  val_injective (by rw [val_eta, val_op_smul, val_eta, unEta_op_smul])

@[simp] theorem inner_eta (v w : V) :
    (inner 𝒷 (eta E v) (eta E w) : 𝒷) = B.inner v w := by
  rw [inner_eq, val_eta, val_eta, ipVal_unEta]

/-- **150II**.2: the image of `η` is ultranorm dense in the carrier. -/
theorem unDense_range_eta : UnDense (inner 𝒷 : E.Car → E.Car → 𝒷) (Set.range (eta E)) := by
  intro x n ωs ε hε
  set U : Set (UnCompl B) := {z | ∀ i : Fin n, semC B (ωs i) (val x - z) < ε} with hU
  have hUopen : IsOpen U := by
    rw [hU, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt ((continuous_semC B (ωs i)).comp (continuous_const.sub continuous_id))
        continuous_const
  have hxU : val x ∈ U := fun i => by rw [sub_self, semC_zero]; exact hε
  obtain ⟨v, hv⟩ := (denseRange_unEta B).exists_mem_open hUopen ⟨val x, hxU⟩
  refine ⟨eta E v, ⟨v, rfl⟩, fun i => ?_⟩
  rw [unSeminorm_eq_semC, val_sub, val_eta]
  exact (hv i).le

/-- **149V**.1: the carrier is self dual. -/
theorem selfDual (hσ : SigmaCl B E.carrier ⊆ (E.carrier : Set (UnCompl B))) :
    SelfDual 𝒷 E.Car :=
  ((dils_selfdual (𝒷 := 𝒷) (X := E.Car)).out 2 0).mp (bddUnComplete hσ)

end CompatExt

/-- A 𝒷-valued inner product transported to `ULift V` — needed because
**150II** asks for a completion in `Type (max u v)` while `V̄` lives in
`Type v`. -/
def BInner.ulift (B : BInner 𝒷 V) : BInner 𝒷 (ULift.{w} V) where
  inner x y := B.inner x.down y.down
  inner_add_right _ _ _ := B.inner_add_right _ _ _
  inner_op_smul_right _ _ _ := B.inner_op_smul_right _ _ _
  inner_smul_right_complex _ _ _ := B.inner_smul_right_complex _ _ _
  star_inner _ _ := B.star_inner _ _
  inner_self_nonneg _ := B.inner_self_nonneg _

omit [StarOrderedRing 𝒷] in
@[simp] theorem BInner.ulift_inner (B : BInner 𝒷 V) (x y : ULift.{w} V) :
    (B.ulift).inner x y = B.inner x.down y.down := rfl


/-- **150II** (`dils-completion`, dils.tex:2632, Theorem): for a von
Neumann algebra `𝒷`, every 𝒷-module `V` with (possibly indefinite)
𝒷-valued inner product has a self-dual completion.

The proof is the thesis's own: complete `V` in the ultranorm uniformity
(**150IV**–**150X**, here Mathlib's `UniformSpace.Completion`), extend the
inner product from `η(V)` to a maximal compatible extension `W ⊆ V̄` by
Zorn's lemma over the σ-closure (**150XI**–**150XV**), and take `X = W`.
The construction is run on `ULift V` for universe reasons only. -/
theorem dils_completion (B : BInner 𝒷 V) :
    Nonempty (SelfDualCompletion.{u, v, max u v} B) := by
  obtain ⟨W, hW, hσ⟩ := exists_maximal_compatExt (B.ulift : BInner 𝒷 (ULift.{u} V))
  let E : CompatExt (B.ulift : BInner 𝒷 (ULift.{u} V)) := ⟨W, hW⟩
  have hrange : Set.range (fun v : V => CompatExt.eta E (ULift.up v))
      = Set.range (CompatExt.eta E) := by
    ext z
    exact ⟨fun ⟨v, hv⟩ => ⟨ULift.up v, hv⟩, fun ⟨u, hu⟩ => ⟨u.down, hu⟩⟩
  exact ⟨{ X := E.Car
           complete := E.completeSpace hσ
           selfDual := E.selfDual hσ
           η := fun v => CompatExt.eta E (ULift.up v)
           η_add := fun v w => CompatExt.eta_add _ _
           η_smul_complex := fun c v => CompatExt.eta_smul_complex _ _
           η_smul := fun b v => CompatExt.eta_op_smul _ _
           η_inner := fun v w => CompatExt.inner_eta _ _
           dense := hrange ▸ CompatExt.unDense_range_eta }⟩

end CompletionCarrier


/-! ## Parsec 1520: sesquilinear forms and 𝒷ᵃ(X) for self-dual X

**152I** (dils.tex:3320): introduction; **152III** (Example) is
`ba_isBoundedBSesq` below (its sesquilinearity half is `ba_isBSesquilinear`,
142VIII); **152IV**, the Example's closing remark, is **152V** itself.
**152VI** is the proof of **152V**;
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
**order separating** on `𝒷ᵃ(X)`: an adjointable `T` is positive iff
`⟨η v, T (η v)⟩ ≥ 0` for all `v ∈ V`.

The exercise asks for an order separating set of **ncp-maps**; that each
`⟨η v, (·) η v⟩` *is* an ncp-map is `hilmod_fixed_on_V_ncp`, placed after
**152XII** because its normality half needs `ba_isLUB_vec`. -/
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
`t = (‖y‖/‖x‖)^{1/2}`.  This avoids `usconv`.

*(Stale-prose correction.  An earlier revision justified that second
deviation by "**44XI**.3 `vn_positive_basic_3` is still `sorry`"; it is
not — it has been proved in `A/VN/Basic` for some time, and 73VIII
`ultraclosed` supplies the ultraweak form.  The deviation stands on the
first one, and on cost rather than on availability: under the
ERRATA-corrected hypothesis there is no norm bound `r` in the *statement*,
though the erratum's own repair does recover one (replace `D` by its cofinal
tail above some `d₀`, which is norm-bounded because `0 ≤ d − d₀ ≤ u − d₀`),
after which `usconv` — `A/VN/Basic`, proved and imported — would give
`‖B(x,y)‖ ≤ r‖x‖‖y‖` as printed.  That route costs the cofinal-tail
reduction plus the Cauchy–Schwarz estimate, some forty lines, for a bound the
rescaling argument gets in six; it is left, deliberately, as class 2.)* -/

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

/-- **152III** (dils.tex:3335, Example): for `T ∈ 𝒷ᵃ(X)` the map
`⟨(·), T(·)⟩` is a **bounded** 𝒷-sesquilinear form in the sense of
**152II** `IsBoundedBSesq`.  Sesquilinearity is `ba_isBSesquilinear`
(142VIII); the bound is Cauchy–Schwarz for Hilbert C*-modules
(`CStarModule.norm_inner_le`) followed by `‖Ty‖ ≤ ‖T‖‖y‖`, so `r = ‖T‖`
works.  (The thesis states the Example for a pre-Hilbert module; ours
carries `[CompleteSpace X]`, which is what `Ba 𝒷 X` is set up with here.) -/
theorem ba_isBoundedBSesq [CompleteSpace X] (Z : Ba 𝒷 X) :
    ∃ r : ℝ, 0 ≤ r ∧
      IsBoundedBSesq r (fun x y : X => (inner 𝒷 x (Z.1 y) : 𝒷)) := by
  let _ : NormedSpace ℂ X := NormedSpace.ofCore (CStarModule.normedSpaceCore 𝒷)
  refine ⟨‖Z.1‖, norm_nonneg _, ba_isBSesquilinear Z, fun x y => ?_⟩
  calc ‖(inner 𝒷 x (Z.1 y) : 𝒷)‖
      ≤ ‖x‖ * ‖Z.1 y‖ := CStarModule.norm_inner_le X
    _ ≤ ‖x‖ * (‖Z.1‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (Z.1.le_opNorm y) (norm_nonneg x)
    _ = ‖Z.1‖ * ‖x‖ * ‖y‖ := by ring

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
/-- **153I** (`hilbmod-ad-ncp`, dils.tex:3487, Proposition), part 2: if `X`
and `Y` are moreover self-dual, then `ad_T` is normal, i.e. an ncp-map.

The proof is **153III**, the author's own: by **48II** `normal_faithful`
against the vector states of `𝒷ᵃ(X)` — faithful by **144I**
(`ba_nonneg_iff`, whence `ba_vonNeumannAlgebra`'s own `np_faithful`) and
normal by **152XIII** (`baVecNP`) — it is enough that
`S ↦ ω⟨x, ad_T(S) x⟩` is normal for every `x ∈ X` and every np-functional
`ω` of `𝒷`; and `⟨x, ad_T(S) x⟩ = ⟨Tx, S(Tx)⟩`, so that map *is* the vector
state of `𝒷ᵃ(Y)` at `Tx`.  Both self-duality hypotheses are used, `hX` to
make `𝒷ᵃ(X)` a von Neumann algebra and `hY` for `𝒷ᵃ(Y)`.

*(Until session 94 this ran instead through **152XII** `ba_isLUB` twice,
computing both suprema by vector forms and using only `hY`, on the stated
ground that "**153III** (the author's proof) is not available to us".  That
was stale: 48II is in `A/VN/Basic` and 152XIII `baVecNP` sits a page and a
half above in this file.)* -/
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
  -- normality: **153III**, the author's own proof.  By **48II**
  -- `normal_faithful` it is enough that `S ↦ ω⟨x, ad_T(S) x⟩` is normal for
  -- the vector states of `𝒷ᵃ(X)`, which are faithful by **144I**
  -- (`ba_nonneg_iff`) and normal by **152XIII** (`baVecNP`); and
  -- `ω⟨x, ad_T(S) x⟩ = ω⟨Tx, S(Tx)⟩` is the vector state of `𝒷ᵃ(Y)` at `Tx`.
  haveI : VonNeumannAlgebra (Ba 𝒷 X) := ba_vonNeumannAlgebra hX
  haveI : VonNeumannAlgebra (Ba 𝒷 Y) := ba_vonNeumannAlgebra hY
  have hnorm : PreservesDirSups ⇑ad := by
    have hfaith : FaithfulCollection
        {ν : NPFunctional (Ba 𝒷 X) | ∃ (x : X) (ω : NPFunctional 𝒷),
          ν = baVecNP hX x ω} := by
      intro Z hZ hzero
      have hvz : ∀ x : X, (inner 𝒷 x (Z.1 x) : 𝒷) = 0 := fun x =>
        VonNeumannAlgebra.np_faithful _ ((ba_nonneg_iff Z).mp hZ x) fun ω =>
          hzero _ ⟨x, ω, rfl⟩
      have hle : Z ≤ 0 := by
        rw [← neg_nonneg]
        refine (ba_nonneg_iff _).mpr fun x => ?_
        have he : (-Z).1 x = -(Z.1 x) := rfl
        rw [he, CStarModule.inner_neg_right, hvz x, neg_zero]
      exact le_antisymm hle hZ
    refine (normal_faithful _ hfaith
      ({ __ := ad, monotone' := fun Z W h => hmono Z W h } :
        Ba 𝒷 Y →ₚ[ℂ] Ba 𝒷 X)).mpr ?_
    rintro ν ⟨x, ω, rfl⟩
    have heq : (fun S : Ba 𝒷 Y => (baVecNP hX x ω (ad S) : ℂ))
        = fun S : Ba 𝒷 Y => (baVecNP hY (T x) ω S : ℂ) := by
      funext S
      show (ω (inner 𝒷 x ((ad S).1 x)) : ℂ) = _
      rw [hvec S x]
      rfl
    exact heq ▸ (baVecNP hY (T x) ω).preservesDirSups'
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := ad
               map_cstarMatrix_nonneg' := fun k M hM => hcp2 k M hM }
           preservesDirSups' := hnorm }, hadeq⟩

end BaVN

section FixedOnVNCP

variable {𝒷 : Type u} {V : Type v}
  [CStarAlgebra 𝒷] [PartialOrder 𝒷] [StarOrderedRing 𝒷]
  [AddCommGroup V] [Module ℂ V] [SMul 𝒷 V]

/-- **152IX** (`hilmod-fixed-on-V`, dils.tex:3394, Exercise), the clause the
order separation of `hilmod_fixed_on_V` is asserted *of*: the vector states
`⟨η v, (·) η v⟩ : 𝒷ᵃ(X) → 𝒷` of a self-dual completion are **ncp-maps**.

* *completely positive* — **145I** `hilbmod_vectstates_cp` at `x = η v`, in
  its own (unfolded, cstar.tex 10II.6) form `∑ᵢⱼ bᵢ* ⟨x, Tᵢ*Tⱼ x⟩ bⱼ ≥ 0`
  for adjoint pairs `(Tᵢ, Sᵢ)`.  As there, the mirror interchanges the
  inner product's arguments; see the note on 145I for why the unswapped
  form is false.
* *normal* — **152XII** `ba_isLUB_vec`: the vector forms compute bounded
  directed suprema of `𝒷ᵃ(X)`.  (For self-adjoint `Z` the two mirrorings
  `⟨η v, Z η v⟩` and `⟨Z η v, η v⟩` coincide, so the two clauses are about
  the same map; `PreservesDirSups` only ever sees self-adjoint elements.)

Together with `hilmod_fixed_on_V` this is the exercise's "order separating
set of ncp-maps" in full. -/
theorem hilmod_fixed_on_V_ncp [VonNeumannAlgebra 𝒷] (B : BInner 𝒷 V)
    (E : SelfDualCompletion.{u, v, w} B) (v : V) :
    (∀ (n : ℕ) (T S : Fin n → (E.X →L[ℂ] E.X)),
        (∀ i, ModuleAdjointTo 𝒷 ⇑(T i) ⇑(S i)) → ∀ b : Fin n → 𝒷,
          0 ≤ ∑ i, ∑ j, star (b i) *
            inner 𝒷 (((S i).comp (T j)) (E.η v)) (E.η v) * b j) ∧
      PreservesDirSups (fun Z : Ba 𝒷 E.X => (inner 𝒷 (E.η v) (Z.1 (E.η v)) : 𝒷)) := by
  refine ⟨fun n T S hTS b => hilbmod_vectstates_cp (E.η v) n T S hTS b, ?_⟩
  intro D s hne hdir hlub
  have h := ba_isLUB_vec E.selfDual hne hdir hlub (E.η v)
  have h2 := Theses.A.VN.isLUB_coe_of_isLUB (hne.image (baVec (E.η v))) h
  rw [← Set.image_comp] at h2
  exact h2

end FixedOnVNCP

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
for the row vector `T : 𝒜ⁿ → 𝒜`, `(bᵢ)ᵢ ↦ ∑ᵢ aᵢbᵢ` — the solution prints
`∑ᵢ bᵢaᵢ`, which is not `𝒜`-linear and whose stated adjoint is not its
adjoint; its own next display uses the order given here.  `ERRATA.md`,
**153IV**, second row).  An earlier revision
said 153I "is still open here — it waits on **152X**"; that is stale, both
are proved above in this file.  What is missing for the author's route is
the two identifications `𝒷ᵃ(𝒜ⁿ) ≅ Mₙ𝒜` and `𝒷ᵃ(𝒜) ≅ 𝒜ᵒᵖ`: the first is
nowhere in the tree, and the second exists only *downstream*, as
`rightMulEquiv` in `Paschke.lean`, which imports this file.  (The third
ingredient, that `𝒜ⁿ` is a **self-dual** Hilbert `𝒜`-module, *is* available
— cstar **36III** `Theses.A.CStar.selfDual_pi`, on the import path — modulo
a short transfer between `A/CStar`'s `SelfDual`, whose boundedness clause is
`Continuous`, and **141IIa**'s, whose clause is `∃ C, ‖τ x‖ ≤ C‖x‖`.)  Two
missing theorems against the self-contained computation below, so this is a
direct argument instead: by
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
