import Papers.EJA.Pure

/-!
# EJA 34 and 39 without the hidden hypothesis: ⋄-self-adjoint roots of pure maps are pure

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex`.

Def 32 calls `g` ⋄-positive when `g = f ∘ f` for a ⋄-self-adjoint `f`, without
asking `f` to be pure; the printed proofs of **EJA 34** and **EJA 39** use that
`f` is pure (ERRATA; PLAN §2 "B15 recurs").  Here: if `g = f ∘ f` is pure and
`f` is ⋄-self-adjoint, then `f` is pure (`diaSA_root_isPure`), so both results
hold for ⋄-positivity as defined (`eja34'`, `eja39'`).

The von Neumann analogue (the tree's B15, `docs/B15-S.md`) needs 2-positivity
and Gardner's theorem for its determinism half; here finite dimension replaces
it: on the corner `E₁(⌈f(1)⌉)` the pure square reflects order and is
injective, so the root is a positive bijection with positive inverse (injective
⟹ surjective).  Argument: `docs/research/eja-b15.md`.
-/

universe u

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra CategoryTheory

section Aux

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]
variable {W : Type u} [AddCommGroup W] [Module ℝ W] [Mul W] [One W]
  [PartialOrder W] [EuclideanJordanAlgebra W]

/-- A positive map killing an effect kills its ceiling (EJA 23 at `1 − z`). -/
theorem kill_ceil {f : V →ₗ[ℝ] W} (hf : IsPositiveMap f) {z : V} (h0 : 0 ≤ z) (h1 : z ≤ 1)
    (hz : f z = 0) : f (ejaCeil z) = 0 := by
  have ha0 : (0 : V) ≤ 1 - z := eja_sub_nonneg.mpr h1
  have ha1 : 1 - z ≤ 1 := by rw [← eja_sub_nonneg, sub_sub_cancel]; exact h0
  have h := floor_one f hf ha0 ha1 (by rw [map_sub, hz, sub_zero])
  rw [← floor_perp_perp z, map_sub, h, sub_self]

/-- **(S)** ⋄-self-adjointness at `1`: `⌈f(1)⌉ = im f`, so `f(⌈f(1)⌉) = f(1)`. -/
theorem diaSA_supp {f : V →ₗ[ℝ] V} (hf : IsPositiveMap f) (hsa : IsDiaSA f) :
    f (ejaCeil (f 1)) = f 1 := by
  have h := hsa 1 (eja_mul_one 1)
  rw [diaUp, diaDown, ejaU_one, LinearMap.id_comp] at h
  rw [h]; exact (ejaIm_spec hf).2.2.1

/-- **(K)** If `f` is ⋄-self-adjoint and `f(f(p)) = 0` for an idempotent `p`, then
`p ⟂ f(1)`: with `z = f(p)`, `f(⌈z⌉) = 0`, and the zero-pattern criterion at
`p` and `1 − ⌈z⌉` gives `p * f(1 − ⌈z⌉) = p * f(1) = 0`. -/
theorem diaSA_kill {f : V →ₗ[ℝ] V} (hf : IsPositiveMap f) (hf1 : f 1 ≤ 1) (hsa : IsDiaSA f)
    {p : V} (hp : p * p = p) (hg : f (f p) = 0) : p * f 1 = 0 := by
  have hz0 : 0 ≤ f p := hf p (eja_idem_nonneg hp)
  have hz1 : f p ≤ 1 := le_trans (hf.mono (eja_idem_le_one hp)) hf1
  have hc := kill_ceil hf hz0 hz1 hg
  have hcc := ejaCeil_idem (f p)
  have htz : (1 - ejaCeil (f p)) * f p = 0 := by
    rw [eja_sub_mul, eja_one_mul, ejaCeil_mul hz0 hz1, sub_self]
  have h := ((diaSA_iff hf hf1).mp hsa p hp (1 - ejaCeil (f p)) (eja_one_sub_idem hcc)).mp htz
  rwa [map_sub, hc, sub_zero] at h

end Aux

section Root

/-- A filter precomposed with an isomorphism is a filter for the same effect. -/
theorem isFilter_iso_comp {E C D : EJAPsu.{u}} {q : E.carrier} {σ : D ⟶ E}
    (hσ : IsFilter q σ) {θ : C ⟶ D} {θ' : D ⟶ C} (h1 : θ ≫ θ' = 𝟙 C) (h2 : θ' ≫ θ = 𝟙 D) :
    IsFilter q (θ ≫ σ) := by
  refine ⟨?_, fun F h hh => ?_⟩
  · rw [ejapsu_comp_apply]; exact le_trans (σ.mono θ.map_subunital') hσ.1
  obtain ⟨hb, hhb, hu⟩ := hσ.2 F h hh
  refine ⟨hb ≫ θ', ?_, fun k hk => ?_⟩
  · dsimp only
    rw [Category.assoc, ← Category.assoc θ', h2, Category.id_comp, hhb]
  · have : k ≫ θ = hb := hu _ (by dsimp only; rw [Category.assoc]; exact hk)
    rw [← this, Category.assoc, h1, Category.comp_id]

/-- **Step 1**: a pure map reflects order and is injective on the Peirce
`1`-space of an idempotent `e` with `g(e) = g(1)` (`e = ⌊b⌋` for its corner's
effect `b`): the corner is a compression, the rest is an isomorphism followed
by the standard filter, which has the left inverse `Q_{b'}` on its corner. -/
theorem pure_reflect {E F : EJAPsu.{u}} (g : E ⟶ F) (hpure : IsPure g) :
    ∃ e : E.carrier, e * e = e ∧ g.toLinearMap e = g.toLinearMap 1 ∧
      ∀ x, e * x = x → (0 ≤ g.toLinearMap x → 0 ≤ x) ∧ (g.toLinearMap x = 0 → x = 0) := by
  obtain ⟨C, b, q', π, ξ, ⟨hb0, hb1⟩, ⟨hq'0, hq'1⟩, hπ, hξ, hf⟩ := hpure
  obtain ⟨_, hσ⟩ := stdFilter_isFilter F hq'0 hq'1
  obtain ⟨θ, θ', hθσ, hθθ', _⟩ := filter_iso hξ hσ
  obtain ⟨ι, ι', hρι, hιι', _⟩ := corner_iso hπ (stdCorner_isCorner E hb0 hb1)
  obtain ⟨b', _, hU'U, _, _⟩ := filter_data hq'0 hq'1
  have hfac : g = stdCorner E b ≫ ι ≫ θ ≫ stdFilter F hq'0 hq'1 := by
    rw [hf, ← hρι, ← hθσ]; simp only [Category.assoc]
  have hfl := ejaFloor_idem b
  have hga : ∀ x, g.toLinearMap x = ejaU (ejaSqrt q') (EJACorner.val
      (θ.toLinearMap (ι.toLinearMap ((stdCorner E b).toLinearMap x)))) := fun x => by
    rw [hfac]; rfl
  refine ⟨ejaFloor b, hfl, ?_, fun x hx => ?_⟩
  · have : (stdCorner E b).toLinearMap (ejaFloor b) = (stdCorner E b).toLinearMap 1 :=
      EJACorner.val_injective (by
        rw [stdCorner_val, stdCorner_val, eja_pone_one _ hfl,
          (eja_pone_eq_self_iff _ hfl _).mpr hfl])
    rw [hga, hga, this]
  set y := (stdCorner E b).toLinearMap x
  have hyx : EJACorner.val y = x := by
    rw [stdCorner_val]; exact (eja_pone_eq_self_iff _ hfl _).mpr hx
  set w := θ.toLinearMap (ι.toLinearMap y)
  have hback : ejaU b' (g.toLinearMap x) = EJACorner.val w := by
    rw [hga, hU'U]
    exact (eja_pone_eq_self_iff _ (ejaCeil_idem q') _).mpr (EJACorner.val_prop w)
  have hwy : ι'.toLinearMap (θ'.toLinearMap w) = y := by
    simp only [w]; rw [ejapsu_inv_apply hθθ', ejapsu_inv_apply hιι']
  constructor
  · intro h
    have h1 : 0 ≤ w := (eja_corner_nonneg_iff _ _).mpr (by rw [← hback]; exact eja_U_nonneg' _ h)
    have h2 := ι'.map_nonneg' _ (θ'.map_nonneg' _ h1)
    rw [hwy] at h2
    rw [← hyx]; exact eja_corner_val_nonneg h2
  · intro h
    have h1 : w = 0 := EJACorner.val_injective (by rw [← hback, h, map_zero]; rfl)
    rw [h1, map_zero, map_zero] at hwy
    rw [← hyx, ← hwy]; rfl

/-- **B15 for EJAs** (`docs/research/eja-b15.md`): if `f` is ⋄-self-adjoint and
`f ∘ f` is pure, then `f` is pure.  This is the hypothesis the printed proofs
of **EJA 34** and **EJA 39** use without Def 32 providing it.  With
`s = ⌈f(1)⌉`: `f(s) = f(1)` (⋄-self-adjointness at `1`); the pure square
reflects order on `E₁(e)` with `e = s` (both inclusions: the zero-pattern
criterion at `1 − e`, and Step 1 applied to `Q_e(1 − s)`); so `f = ξ_{f(1)} ∘ T
∘ π_s` with `T : E₁(s) → E₁(s)` positive, unital and injective, hence (finite
dimension) bijective, with positive inverse — an isomorphism, and `ξ_{f(1)} ∘ T`
is a filter. -/
theorem diaSA_root_isPure {E : EJAPsu.{u}} (f g : E ⟶ E) (hg : IsPure g) (hfg : g = f ≫ f)
    (hsa : IsDiaSA f.toLinearMap) : IsPure f := by
  have hFpos : IsPositiveMap f.toLinearMap := f.map_nonneg'
  have hF1 : f.toLinearMap 1 ≤ 1 := f.map_subunital'
  have hq0 : 0 ≤ f.toLinearMap 1 := hFpos 1 (eja_idem_nonneg (eja_mul_one 1))
  have hss := ejaCeil_idem (f.toLinearMap 1)
  have hs0 := eja_idem_nonneg hss
  have hs1 := eja_idem_le_one hss
  have hFs : f.toLinearMap (ejaCeil (f.toLinearMap 1)) = f.toLinearMap 1 := diaSA_supp hFpos hsa
  have hG : ∀ x, g.toLinearMap x = f.toLinearMap (f.toLinearMap x) := fun x => by
    rw [hfg, ejapsu_comp_apply]
  obtain ⟨e, he, hge, hrefl⟩ := pure_reflect g hg
  -- Step 2: `e = ⌈f(1)⌉`
  have hse : ejaCeil (f.toLinearMap 1) ≤ e := by
    have hk := diaSA_kill hFpos hF1 hsa (eja_one_sub_idem he)
      (by rw [← hG, map_sub, hge, sub_self])
    exact (EJAceilfloor hq0 hF1).2.2.1.2.2 e he
      ((le_idem_iff_mul_one_sub hq0 hF1 he).mpr hk)
  have hes : e ≤ ejaCeil (f.toLinearMap 1) := by
    have h1s0 : (0 : E.carrier) ≤ 1 - ejaCeil (f.toLinearMap 1) := eja_sub_nonneg.mpr hs1
    have hG1s : g.toLinearMap (1 - ejaCeil (f.toLinearMap 1)) = 0 := by
      rw [hG, map_sub, hFs, sub_self, map_zero]
    have hfi := factorimage g.toLinearMap g.map_nonneg' he hge (1 - ejaCeil (f.toLinearMap 1))
    have hmem : e * ejaU e (1 - ejaCeil (f.toLinearMap 1)) = ejaU e (1 - ejaCeil (f.toLinearMap 1)) := by
      have := EJACorner.val_prop (ejaPoneCorner ⟨e, he⟩ (1 - ejaCeil (f.toLinearMap 1)))
      rw [ejaPoneCorner_val] at this
      rw [ejaU_idem he]; exact this
    have hz := (hrefl _ hmem).2 (by rw [hfi, hG1s])
    have := (eja_U_eq_zero_iff (eja_idem_nonneg he) h1s0).mp hz
    exact (idem_le_effect_iff he hs0 hs1).mpr this
  have hes' : e = ejaCeil (f.toLinearMap 1) := le_antisymm hes hse
  subst hes'
  -- Step 3: the corner and the filter
  set s := ejaCeil (f.toLinearMap 1) with hsdef
  have hfs : ejaFloor s = s := ejaFloor_idem_eq hss
  have hπ := stdCorner_isCorner E hs0 hs1
  obtain ⟨fb, hfb, _⟩ := hπ.2 E f hFs.symm
  obtain ⟨hσ1, hσ⟩ := stdFilter_isFilter E hq0 hF1
  set σ := stdFilter E hq0 hF1
  have hmemc : ∀ c : EJACorner (floorIdem s), s * EJACorner.val c = EJACorner.val c := by
    intro c; have := EJACorner.val_prop c; rwa [show (floorIdem s).elt = s from hfs] at this
  have hπc : ∀ c : EJACorner (floorIdem s), (stdCorner E s).toLinearMap (EJACorner.val c) = c :=
    fun c => EJACorner.val_injective (by
      rw [stdCorner_val]
      exact (eja_pone_eq_self_iff _ (ejaFloor_idem s) _).mpr (EJACorner.val_prop c))
  have hfbv : ∀ c, fb.toLinearMap c = f.toLinearMap (EJACorner.val c) := by
    intro c
    have := congrArg (fun m : E ⟶ E => m.toLinearMap (EJACorner.val c)) hfb
    simpa only [ejapsu_comp_apply, hπc] using this
  have hfb1 : fb.toLinearMap 1 = f.toLinearMap 1 := by
    rw [hfbv, EJACorner.val_one]; show f.toLinearMap (ejaFloor s) = _; rw [hfs]; exact hFs
  obtain ⟨T, hT, _⟩ := hσ.2 _ fb (le_of_eq hfb1)
  have hTv : ∀ c, σ.toLinearMap (T.toLinearMap c) = f.toLinearMap (EJACorner.val c) := by
    intro c; rw [← hfbv, ← hT, ejapsu_comp_apply]
  -- the standard filter is injective
  have hσinj : Function.Injective σ.toLinearMap := by
    obtain ⟨b', _, hU'U, _, _⟩ := filter_data hq0 hF1
    intro y y' h
    apply EJACorner.val_injective
    have h1 := congrArg (ejaU b') h
    rw [stdFilter_apply, stdFilter_apply, hU'U, hU'U,
      (eja_pone_eq_self_iff _ hss _).mpr (EJACorner.val_prop y),
      (eja_pone_eq_self_iff _ hss _).mpr (EJACorner.val_prop y')] at h1
    exact h1
  have hT1 : T.toLinearMap 1 = 1 := hσinj (by
    rw [hTv, hσ1, EJACorner.val_one]; show f.toLinearMap (ejaFloor s) = _; rw [hfs]; exact hFs)
  -- `T` is injective
  have hTinj : Function.Injective T.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : f.toLinearMap (EJACorner.val c) = 0 := by rw [← hTv, hc, map_zero]
    have h2 := (hrefl _ (hmemc c)).2 (by rw [hG, h1, map_zero])
    exact EJACorner.val_injective (by rw [h2]; rfl)
  -- hence bijective (finite dimension, via the cast to an endomorphism)
  have hsc : (ceilIdem (f.toLinearMap 1)).elt = (floorIdem s).elt := hfs.symm
  have hTsurj : Function.Surjective T.toLinearMap := by
    let Tc := T ≫ cornerCast E (ceilIdem (f.toLinearMap 1)) (floorIdem s) hsc
    have hinj : Function.Injective Tc.toLinearMap := by
      intro c c' h
      apply hTinj
      apply EJACorner.val_injective
      have h' := congrArg EJACorner.val h
      exact h'
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    intro d
    obtain ⟨c, hc⟩ := hsurj ((cornerCast E (ceilIdem (f.toLinearMap 1)) (floorIdem s) hsc).toLinearMap d)
    refine ⟨c, EJACorner.val_injective ?_⟩
    have h' := congrArg EJACorner.val hc
    exact h'
  let Te := LinearEquiv.ofBijective T.toLinearMap ⟨hTinj, hTsurj⟩
  have hTe : ∀ d, T.toLinearMap (Te.symm d) = d := fun d => Te.apply_symm_apply d
  -- the inverse is positive and unital
  let T' : filterObj E (f.toLinearMap 1) ⟶ cornerObj E s :=
    { toLinearMap := Te.symm.toLinearMap
      map_nonneg' := fun d hd => by
        have hc := hTe d
        set c := Te.symm d
        have h1 : f.toLinearMap (EJACorner.val c) = σ.toLinearMap d := by rw [← hTv, hc]
        have h2 := (hrefl _ (hmemc c)).1 (by rw [hG, h1]; exact hFpos _ (σ.map_nonneg' _ hd))
        exact (eja_corner_nonneg_iff _ _).mpr h2
      map_subunital' := by
        show Te.symm 1 ≤ 1
        rw [show Te.symm 1 = 1 from Te.symm_apply_eq.mpr hT1.symm] }
  have hTT' : T ≫ T' = 𝟙 _ := ejapsu_hom_ext fun c => Te.symm_apply_apply c
  have hT'T : T' ≫ T = 𝟙 _ := ejapsu_hom_ext fun d => hTe d
  refine ⟨cornerObj E s, s, f.toLinearMap 1, stdCorner E s, fb, ⟨hs0, hs1⟩, ⟨hq0, hF1⟩, hπ,
    ?_, hfb.symm⟩
  rw [← hT]
  exact isFilter_iso_comp hσ hTT' hT'T

end Root

section Corollaries

/-- A ⋄-positive map in the sense of Def 32 (a linear root) as a composite in
`EJA_psu`. -/
theorem diaPos_root {E : EJAPsu.{u}} (g : E ⟶ E) (hpos : IsDiaPos g.toLinearMap) :
    ∃ f : E ⟶ E, IsDiaSA f.toLinearMap ∧ g = f ≫ f := by
  obtain ⟨φ, hφ, hφ1, hφsa, hgφ⟩ := hpos
  refine ⟨⟨φ, hφ, hφ1⟩, hφsa, ejapsu_hom_ext fun x => ?_⟩
  rw [ejapsu_comp_apply, hgφ]; rfl

/-- **EJA 34** (`super-duper-theorem`, main.tex:775, Theorem), as printed: a
pure ⋄-positive `g` (Def 32: `g = f ∘ f` for some ⋄-self-adjoint `f`, not
assumed pure) is `Q_{√g(1)}`.  The root is pure by `diaSA_root_isPure`; then
`super_duper_theorem`. -/
theorem eja34' {E : EJAPsu.{u}} (g : E ⟶ E) (hgpure : IsPure g)
    (hpos : IsDiaPos g.toLinearMap) :
    ∀ x, g.toLinearMap x = ejaU (ejaSqrt (g.toLinearMap 1)) x := by
  obtain ⟨f, hsa, hfg⟩ := diaPos_root g hpos
  exact super_duper_theorem g hgpure ⟨f, diaSA_root_isPure f g hgpure hfg hsa, hsa, hfg⟩

/-- **EJA 39** (main.tex:891, Proposition), as printed: a faithful pure
⋄-positive `g` is `Q_{√g(1)}` (root not assumed pure; `diaSA_root_isPure`, then
`eja39`). -/
theorem eja39' {E : EJAPsu.{u}} (g : E ⟶ E) (hgpure : IsPure g)
    (hg : ∀ a : E.carrier, 0 ≤ a → g.toLinearMap a = 0 → a = 0)
    (hpos : IsDiaPos g.toLinearMap) :
    ∀ x, g.toLinearMap x = ejaU (ejaSqrt (g.toLinearMap 1)) x := by
  obtain ⟨f, hsa, hfg⟩ := diaPos_root g hpos
  exact eja39 g hgpure hg ⟨f, diaSA_root_isPure f g hgpure hfg hsa, hsa, hfg⟩

end Corollaries

end Papers.EJA
