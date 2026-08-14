/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines
3781–4999.

  §Completeness
    Closure of a Convex Subset  (parsecs 720–730: ultrastrongly continuous
                                 functionals, radially open sets,
                                 Hahn–Banach, ultraweak = ultrastrong
                                 closure of convex sets)
    Kaplansky's Density Theorem (parsec 740)
    Closedness of Subalgebras   (parsec 750)
    Completeness                (parsecs 760–770: B(H) and every von Neumann
                                 algebra are ultrastrongly complete and
                                 bounded ultraweakly complete; the unit ball
                                 is ultraweakly compact)

Statements only; every proof is `sorry`.  See `Theses/A/VN/Basic.lean` for
the encoding of the ultraweak/ultrastrong topologies; "ultrastrongly Cauchy"
for a net `(x_i)_{l}` is rendered as `‖x_i - x_j‖_ω → 0` along `l ×ˢ l` for
every np-functional `ω`, and "ultraweakly Cauchy" as `Cauchy (l.map (ω ∘ x))`
for every `ω`.
-/
import Theses.A.VN.Projections

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra Pointwise
open Filter Topology Theses Theses.A.CStar

-- `radialTopology` is intentionally a plain def, not an instance:
set_option warn.classDefReducibility false

universe u

namespace Theses.A.VN

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ### The np-functional cone and the `‖·‖_ω` estimates

`omegaNorm_mul_le`, `zeroNP`, `addNP`, `omegaNorm_le_addNP(')` and
`abs_omegaNorm_sub_omegaNorm_le` used to be file-private here; they are now
public in `Theses/A/VN/Basic.lean`, since **72V**, **72XI**, **73VIII** and
**87VIII** all need them. -/

/-- A net whose pairwise distances vanish along `l ×ˢ l` has a Cauchy image
filter.  (Used to turn the thesis's "`‖(T_α − T_β)x‖` vanishes for large
`α, β`" into Mathlib's `Cauchy`.) -/
private theorem cauchy_map_of_tendsto_dist {X ι : Type*} [PseudoMetricSpace X]
    {l : Filter ι} [l.NeBot] {f : ι → X}
    (h : Tendsto (fun p : ι × ι => dist (f p.1) (f p.2)) (l ×ˢ l) (𝓝 0)) :
    Cauchy (l.map f) := by
  rw [cauchy_map_iff', Metric.uniformity_basis_dist.tendsto_right_iff]
  intro ε hε
  simpa using h.eventually (gt_mem_nhds hε)

/-! ## Parsec 720: ultrastrongly continuous functionals

**71I** (vn.tex:3783) and **72I** (vn.tex:3823): overview — nothing to
formalize. -/

section Functionals

variable [VonNeumannAlgebra A]

variable (A) in
/-- **72II** (`bstaromega`, vn.tex:3841, Definition): the functional
`b*ω : a ↦ ω(b* a b)` for an np-functional `ω` and `b ∈ A`. -/
noncomputable def bStarOmega (b : A) (ω : NPFunctional A) : A → ℂ :=
  fun a => ω (star b * a * b)

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 1a: `b*ω` is
an np-functional. -/
theorem bstaromega_np (b : A) (ω : NPFunctional A) :
    ∃ ω' : NPFunctional A, ⇑ω' = bStarOmega A b ω :=
  -- positivity is `star_left_conjugate_le_conjugate`, normality is **44VIII**
  ⟨conjNP b ω, funext fun a => conjNP_apply b ω a⟩

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 1b:
`|ω(a* b c)| ≤ ‖a‖_ω ‖b‖ ‖c‖_ω`.

**Erratum (author).**  vn.tex:3850 writes this bound with a leading `‖ω‖`
(= `ω(1)`).  That factor must not be there: `‖a‖_ω = ω(a*a)^½` is unnormalised,
so replacing `ω` by `tω` scales the left side by `t` and the right by `t²`.
Counterexample `𝒜 = ℂ`, `ω = t·id` with `0 < t < 1`, `a = b = c = 1`: the left
side is `t`, the right `t²`.  Cauchy–Schwarz gives the factor-free bound
directly (cf. `norm_apply_star_mul_le`).  Same defect as **30IV**.2. -/
theorem bstaromega_bound (ω : NPFunctional A) (a b c : A) :
    ‖ω (star a * b * c)‖ ≤
      omegaNorm A ω a * ‖b‖ * omegaNorm A ω c := by
  calc ‖ω (star a * b * c)‖ = ‖ω (star a * (b * c))‖ := by rw [mul_assoc]
    _ ≤ omegaNorm A ω a * omegaNorm A ω (b * c) := norm_apply_star_mul_le ω a (b * c)
    _ ≤ omegaNorm A ω a * (‖b‖ * omegaNorm A ω c) :=
        mul_le_mul_of_nonneg_left (omegaNorm_mul_le ω b c) (omegaNorm_nonneg ω a)
    _ = omegaNorm A ω a * ‖b‖ * omegaNorm A ω c := by ring

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 1c:
`‖b*ω - b'*ω‖ ≤ ‖b-b'‖_ω (‖b‖_ω + ‖b'‖_ω)` — rendered pointwise.

**Erratum (author).**  As in part 1b, vn.tex:3850's leading `‖ω‖` must not be
there — it breaks homogeneity in `ω` for the same reason. -/
theorem bstaromega_lipschitz (ω : NPFunctional A) (b b' : A) (a : A) :
    ‖bStarOmega A b ω a - bStarOmega A b' ω a‖ ≤
      omegaNorm A ω (b - b') *
        (omegaNorm A ω b + omegaNorm A ω b') * ‖a‖ := by
  show ‖ω (star b * a * b) - ω (star b' * a * b')‖ ≤ _
  have e : star b * a * b - star b' * a * b'
      = star b * a * (b - b') + star (b - b') * a * b' := by
    rw [star_sub]; noncomm_ring
  have hsplit : ω (star b * a * b) - ω (star b' * a * b')
      = ω (star b * a * (b - b')) + ω (star (b - b') * a * b') := by
    rw [← npFunctional_sub, e, npFunctional_add]
  calc ‖ω (star b * a * b) - ω (star b' * a * b')‖
      = ‖ω (star b * a * (b - b')) + ω (star (b - b') * a * b')‖ := by rw [hsplit]
    _ ≤ ‖ω (star b * a * (b - b'))‖ + ‖ω (star (b - b') * a * b')‖ := norm_add_le _ _
    _ ≤ omegaNorm A ω b * ‖a‖ * omegaNorm A ω (b - b') +
          omegaNorm A ω (b - b') * ‖a‖ * omegaNorm A ω b' :=
        add_le_add (bstaromega_bound ω b a (b - b'))
          (bstaromega_bound ω (b - b') a b')
    _ = omegaNorm A ω (b - b') * (omegaNorm A ω b + omegaNorm A ω b') * ‖a‖ := by
        ring

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 2: if
`(b_n)_n` is `‖·‖_ω`-Cauchy, then `(b_n * ω)_n` is Cauchy in the operator
norm and converges to an np-functional. -/
theorem bstaromega_cauchy (ω : NPFunctional A) (b : ℕ → A)
    (hb : Tendsto (fun p : ℕ × ℕ => omegaNorm A ω (b p.1 - b p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ f : NPFunctional A, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ∀ a : A,
      ‖bStarOmega A (b n) ω a - f a‖ ≤ ε * ‖a‖ := by
  classical
  have hbs : ∀ (n : ℕ) (a : A), bStarOmega A (b n) ω a = conjNP (b n) ω a :=
    fun _ _ => rfl
  -- the Cauchy hypothesis in `∃ N, ∀ m n ≥ N` form
  have hcauchy2 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      omegaNorm A ω (b m - b n) < ε := by
    intro ε hε
    obtain ⟨pa, hpa, pb, hpb, h⟩ := Filter.eventually_prod_iff.mp
      (hb.eventually (gt_mem_nhds hε))
    obtain ⟨Na, hNa⟩ := Filter.eventually_atTop.mp hpa
    obtain ⟨Nb, hNb⟩ := Filter.eventually_atTop.mp hpb
    exact ⟨max Na Nb, fun m hm n hn =>
      h (hNa m ((le_max_left _ _).trans hm)) (hNb n ((le_max_right _ _).trans hn))⟩
  -- (0) `‖b n‖_ω` is eventually bounded, by `K`
  obtain ⟨N₀, hN₀⟩ := hcauchy2 1 one_pos
  set K : ℝ := omegaNorm A ω (b N₀) + 1 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have := omegaNorm_nonneg ω (b N₀); rw [hKdef]; linarith
  have hK : ∀ n ≥ N₀, omegaNorm A ω (b n) ≤ K := by
    intro n hn
    have h1 := omegaNorm_sub_le ω (b n) (b N₀) 0
    rw [sub_zero, sub_zero] at h1
    have h2 := (hN₀ n hn N₀ le_rfl).le
    rw [hKdef]; linarith
  -- (1) the thesis's Lipschitz estimate, uniformly for `m, n ≥ N₀`
  have hlip : ∀ m ≥ N₀, ∀ n ≥ N₀, ∀ a : A,
      ‖bStarOmega A (b m) ω a - bStarOmega A (b n) ω a‖
        ≤ omegaNorm A ω (b m - b n) * (2 * K) * ‖a‖ := by
    intro m hm n hn a
    refine (bstaromega_lipschitz ω (b m) (b n) a).trans ?_
    have h5 : omegaNorm A ω (b m) + omegaNorm A ω (b n) ≤ 2 * K := by
      have h1 := hK m hm
      have h2 := hK n hn
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h5 (omegaNorm_nonneg ω (b m - b n))) (norm_nonneg a)
  -- (2) `(b_n * ω)(a)` is Cauchy for each `a`; call its limit `F a`
  have hptc : ∀ a : A, ∃ z : ℂ,
      Tendsto (fun n => bStarOmega A (b n) ω a) atTop (𝓝 z) := by
    intro a
    refine cauchy_map_iff_exists_tendsto.mp (cauchy_map_of_tendsto_dist ?_)
    refine squeeze_zero'
      (g := fun p : ℕ × ℕ => omegaNorm A ω (b p.1 - b p.2) * (2 * K) * ‖a‖)
      (Eventually.of_forall fun _ => dist_nonneg) ?_ ?_
    · refine Filter.eventually_prod_iff.mpr
        ⟨fun m => N₀ ≤ m, eventually_atTop.mpr ⟨N₀, fun _ h => h⟩,
         fun n => N₀ ≤ n, eventually_atTop.mpr ⟨N₀, fun _ h => h⟩, ?_⟩
      intro m hm n hn
      rw [dist_eq_norm]
      exact hlip m hm n hn a
    · simpa using (hb.mul_const (2 * K)).mul_const ‖a‖
  choose F hF using hptc
  -- (3) the convergence is uniform in `‖a‖`
  have huniform : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ∀ a : A,
      ‖bStarOmega A (b n) ω a - F a‖ ≤ ε * ‖a‖ := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hcauchy2 (ε / (2 * K + 1)) (by positivity)
    refine ⟨max N₀ N₁, fun n hn a => ?_⟩
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
    refine le_of_tendsto ((tendsto_const_nhds.sub (hF a)).norm) ?_
    filter_upwards [eventually_ge_atTop (max N₀ N₁)] with m hm
    have hm₀ : N₀ ≤ m := (le_max_left _ _).trans hm
    have hm₁ : N₁ ≤ m := (le_max_right _ _).trans hm
    refine (hlip n hn₀ m hm₀ a).trans ?_
    have h5 := (hN₁ n hn₁ m hm₁).le
    have h6 := norm_nonneg a
    have h7 : omegaNorm A ω (b n - b m) * (2 * K) ≤ ε := by
      have h8 : ε / (2 * K + 1) * (2 * K) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    nlinarith
  -- (4) `F` is a positive linear functional
  have hFadd : ∀ a c : A, F (a + c) = F a + F c := by
    intro a c
    refine tendsto_nhds_unique (hF (a + c)) ?_
    have he : ∀ n : ℕ, bStarOmega A (b n) ω a + bStarOmega A (b n) ω c
        = bStarOmega A (b n) ω (a + c) := by
      intro n
      simp only [hbs]
      exact (npFunctional_add (conjNP (b n) ω) a c).symm
    simpa only [he] using (hF a).add (hF c)
  have hFsmul : ∀ (c : ℂ) (a : A), F (c • a) = c • F a := by
    intro c a
    refine tendsto_nhds_unique (hF (c • a)) ?_
    have he : ∀ n : ℕ, c * bStarOmega A (b n) ω a = bStarOmega A (b n) ω (c • a) := by
      intro n
      simp only [hbs]
      have h := map_smul (conjNP (b n) ω).toPositiveLinearMap c a
      simp only [smul_eq_mul] at h
      exact h.symm
    simpa only [smul_eq_mul, he] using (hF a).const_mul c
  have hFmono : ∀ {a c : A}, a ≤ c → F a ≤ F c := by
    intro a c h
    refine le_of_tendsto_of_tendsto' (hF a) (hF c) fun n => ?_
    simpa only [hbs] using npFunctional_mono (conjNP (b n) ω) h
  have hFim : ∀ x : A, IsSelfAdjoint x → (F x).im = 0 := by
    intro x hx
    have h1 : Tendsto (fun n => (bStarOmega A (b n) ω x).im) atTop (𝓝 (F x).im) :=
      (Complex.continuous_im.tendsto _).comp (hF x)
    have h2 : ∀ n : ℕ, (bStarOmega A (b n) ω x).im = 0 := fun n => by
      simpa only [hbs] using npFunctional_im_eq_zero (conjNP (b n) ω) hx
    simp only [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- (5) `F` is normal: the convergence is *uniform* on the norm-bounded
  -- cofinal part `D' = {d ∈ D | d₀ ≤ d}` of any bounded directed set `D`,
  -- and normality of each `b_n * ω` transfers across a uniform limit.
  have hFnormal : PreservesDirSups (fun a : A => F a) := by
    intro D s hne hdir hlub
    obtain ⟨d₀, hd₀⟩ := hne
    set D' : Set (selfAdjoint A) := {d | d ∈ D ∧ d₀ ≤ d} with hD'def
    have hD'ne : D'.Nonempty := ⟨d₀, hd₀, le_rfl⟩
    have hD'dir : DirectedOn (· ≤ ·) D' := by
      rintro d ⟨hdD, hd0⟩ e ⟨heD, -⟩
      obtain ⟨g, hgD, hdg, heg⟩ := hdir d hdD e heD
      exact ⟨g, ⟨hgD, hd0.trans hdg⟩, hdg, heg⟩
    have hD'lub : IsLUB D' s := by
      refine ⟨fun d hd => hlub.1 hd.1, fun u hu => hlub.2 fun d hd => ?_⟩
      obtain ⟨g, hgD, hdg, hd0g⟩ := hdir d hd d₀ hd₀
      exact hdg.trans (hu ⟨hgD, hd0g⟩)
    set C : ℝ := ‖(d₀ : A)‖ + ‖(s : A) - (d₀ : A)‖ with hCdef
    have hC0 : (0 : ℝ) ≤ C := by positivity
    have hCb : ∀ d ∈ D', ‖((d : selfAdjoint A) : A)‖ ≤ C := by
      rintro d ⟨hdD, hd0⟩
      have h1 : (0 : A) ≤ (d : A) - (d₀ : A) :=
        sub_nonneg.mpr (Subtype.coe_le_coe.mpr hd0)
      have h2 : (d : A) - (d₀ : A) ≤ (s : A) - (d₀ : A) :=
        sub_le_sub_right (Subtype.coe_le_coe.mpr (hlub.1 hdD)) _
      have h3 := CStarAlgebra.norm_le_norm_of_nonneg_of_le h1 h2
      have h4 : ‖(d : A)‖ ≤ ‖(d : A) - (d₀ : A)‖ + ‖(d₀ : A)‖ := by
        simpa using norm_add_le ((d : A) - (d₀ : A)) ((d₀ : A))
      rw [hCdef]; linarith
    refine ⟨?_, fun z hz => ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact hFmono (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · have hzre : ∀ d ∈ D, (F ((d : selfAdjoint A) : A)).re ≤ z.re := fun d hd =>
        (Complex.le_def.mp (hz ⟨d, hd, rfl⟩)).1
      have hzim : z.im = 0 := by
        have h := (Complex.le_def.mp (hz ⟨d₀, hd₀, rfl⟩)).2
        rw [hFim _ d₀.2] at h
        exact h.symm
      refine Complex.le_def.mpr ⟨?_, by rw [hFim _ s.2, hzim]⟩
      refine le_of_forall_pos_le_add fun ε hε => ?_
      set ε' : ℝ := ε / (C + ‖(s : A)‖ + 1) with hε'def
      have hε'0 : 0 < ε' := by rw [hε'def]; positivity
      obtain ⟨N, hN⟩ := huniform ε' hε'0
      have hlubn := (conjNP (b N) ω).preservesDirSups' D' s hD'ne hD'dir hD'lub
      have hub : ∀ y ∈ (fun d : selfAdjoint A => conjNP (b N) ω ((d : selfAdjoint A) : A)) '' D',
          y ≤ (((z.re + ε' * C : ℝ)) : ℂ) := by
        rintro _ ⟨d, hd, rfl⟩
        refine Complex.le_def.mpr ⟨?_, ?_⟩
        · have h1 : ‖bStarOmega A (b N) ω ((d : selfAdjoint A) : A)
              - F ((d : selfAdjoint A) : A)‖ ≤ ε' * ‖((d : selfAdjoint A) : A)‖ :=
            hN N le_rfl _
          have h2 : (conjNP (b N) ω ((d : selfAdjoint A) : A)).re
              - (F ((d : selfAdjoint A) : A)).re ≤ ε' * ‖((d : selfAdjoint A) : A)‖ := by
            refine le_trans ?_ h1
            simpa only [hbs, Complex.sub_re] using
              Complex.re_le_norm (bStarOmega A (b N) ω ((d : selfAdjoint A) : A)
                - F ((d : selfAdjoint A) : A))
          have h3 := hzre d hd.1
          have h4 := hCb d hd
          have h5 : ε' * ‖((d : selfAdjoint A) : A)‖ ≤ ε' * C := by
            exact mul_le_mul_of_nonneg_left h4 hε'0.le
          simp only [Complex.ofReal_re]
          linarith
        · simp only [Complex.ofReal_im]
          exact npFunctional_im_eq_zero (conjNP (b N) ω) d.2
      have hsle : ((conjNP (b N) ω) ((s : selfAdjoint A) : A)).re ≤ z.re + ε' * C := by
        have h2 := (Complex.le_def.mp (hlubn.2 hub)).1
        rw [Complex.ofReal_re] at h2
        exact h2
      have h6 : ‖bStarOmega A (b N) ω ((s : selfAdjoint A) : A)
          - F ((s : selfAdjoint A) : A)‖ ≤ ε' * ‖((s : selfAdjoint A) : A)‖ :=
        hN N le_rfl _
      have h7 : (F ((s : selfAdjoint A) : A)).re
          - (conjNP (b N) ω ((s : selfAdjoint A) : A)).re
            ≤ ε' * ‖((s : selfAdjoint A) : A)‖ := by
        refine le_trans ?_ h6
        have := Complex.re_le_norm (F ((s : selfAdjoint A) : A)
          - bStarOmega A (b N) ω ((s : selfAdjoint A) : A))
        rw [← norm_neg] at h6
        simpa only [hbs, Complex.sub_re, neg_sub] using this.trans
          (le_of_eq (by rw [← norm_neg]; congr 1; abel))
      have h8 : ε' * C + ε' * ‖((s : selfAdjoint A) : A)‖ ≤ ε := by
        rw [hε'def, ← mul_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg ((s : selfAdjoint A) : A)]
      linarith
  -- (6) assemble
  refine ⟨⟨{ toFun := F
             map_add' := hFadd
             map_smul' := fun c a => hFsmul c a
             monotone' := fun _ _ h => hFmono h }, hFnormal⟩, huniform⟩

/-- **72IV** (vn.tex:3876, Exercise): an ultrastrongly continuous linear
functional `f` on a von Neumann algebra is bounded by `1` on some
`‖·‖_ω`-ball. -/
theorem us_continuous_bounded_on_ball (f : A →ₗ[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultrastrong A) _ ⇑f) :
    ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
      ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ 1 := by
  classical
  -- the generating family of the ultrastrong topology and the sets of it
  -- containing `0`
  set G : Set (Set A) :=
    {U : Set A | ∃ (ω : NPFunctional A) (b : A) (ε : ℝ), 0 < ε ∧
      U = {a : A | omegaNorm A ω (a - b) < ε}} with hG
  set T : Set (Set A) := {s : Set A | (0 : A) ∈ s ∧ s ∈ G} with hT
  -- a finite family of basic neighbourhoods of `0` is dominated by a single
  -- `‖·‖_ω`-ball, because np-functionals can be added
  have key : ∀ I : Finset T, ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
      ∀ a : A, omegaNorm A ω a ≤ δ → ∀ i ∈ I, a ∈ (i : Set A) := by
    intro I
    induction I using Finset.induction_on with
    | empty => exact ⟨zeroNP, 1, one_pos, fun a _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | @insert i I _ ih =>
      obtain ⟨ω', δ', hδ', hsub'⟩ := ih
      obtain ⟨h0i, ω₀, b, ε, hε, hUeq⟩ := i.2
      have hb : omegaNorm A ω₀ b < ε := by
        rw [hUeq] at h0i
        simpa using h0i
      refine ⟨addNP ω' ω₀, min δ' ((ε - omegaNorm A ω₀ b) / 2), lt_min hδ' (by linarith),
        fun a ha j hj => ?_⟩
      have ha' : omegaNorm A ω' a ≤ δ' :=
        le_trans (omegaNorm_le_addNP ω' ω₀ a) (le_trans ha (min_le_left _ _))
      have ha₀ : omegaNorm A ω₀ a ≤ (ε - omegaNorm A ω₀ b) / 2 :=
        le_trans (omegaNorm_le_addNP' ω' ω₀ a) (le_trans ha (min_le_right _ _))
      rcases Finset.mem_insert.mp hj with rfl | hjI
      · rw [hUeq]
        have hchain : omegaNorm A ω₀ (a - b)
            ≤ omegaNorm A ω₀ (a - 0) + omegaNorm A ω₀ (0 - b) := omegaNorm_sub_le ω₀ a 0 b
        rw [sub_zero, zero_sub, omegaNorm_neg] at hchain
        exact lt_of_le_of_lt hchain (by linarith)
      · exact hsub' a ha' j hjI
  -- `f` is bounded by `1` on the ultrastrongly open preimage of the unit ball
  have hU : @IsOpen A (ultrastrong A) (⇑f ⁻¹' Metric.ball (0 : ℂ) 1) :=
    (@continuous_def A ℂ (ultrastrong A) _ _).mp hf _ Metric.isOpen_ball
  have h0U : (0 : A) ∈ ⇑f ⁻¹' Metric.ball (0 : ℂ) 1 := by simp
  have hmem : (⇑f ⁻¹' Metric.ball (0 : ℂ) 1) ∈ @nhds A (ultrastrong A) 0 :=
    @IsOpen.mem_nhds A (ultrastrong A) _ _ hU h0U
  rw [show (ultrastrong A) = TopologicalSpace.generateFrom G from rfl,
    TopologicalSpace.nhds_generateFrom, ← hT, iInf_subtype'] at hmem
  obtain ⟨I, hI, V, hV, hUeq⟩ := Filter.mem_iInf.mp hmem
  obtain ⟨ω, δ, hδ, hsub⟩ := key hI.toFinset
  refine ⟨ω, δ, hδ, fun a ha => ?_⟩
  have haU : a ∈ ⇑f ⁻¹' Metric.ball (0 : ℂ) 1 := by
    rw [hUeq]
    refine Set.mem_iInter.mpr fun i => ?_
    exact hV i (hsub a ha i.1 (hI.mem_toFinset.mpr i.2))
  exact le_of_lt (by simpa [Complex.dist_eq] using haU)

/-! ### Auxiliary material for **72V**

`‖·‖_ω` is literally the norm of the GNS pre-Hilbert space
`PositiveLinearMap.PreGNS ω`, so it is homogeneous; and `gnsVec ω` is the
(linear, isometric, dense-range) canonical map of `A` into the GNS Hilbert
space `ℋ_ω = PositiveLinearMap.GNS ω`, which is the thesis's `ℋ_ω`. -/

omit [VonNeumannAlgebra A] in
/-- `‖c • a‖_ω = |c| ‖a‖_ω`. -/
theorem omegaNorm_smul (ω : NPFunctional A) (c : ℂ) (a : A) :
    omegaNorm A ω (c • a) = ‖c‖ * omegaNorm A ω a := by
  simp only [omegaNorm_eq_norm, map_smul, norm_smul]

/-- `gnsVec ω` bundled as a linear map `A →ₗ[ℂ] ℋ_ω`. -/
noncomputable def gnsVecₗ (ω : NPFunctional A) :
    A →ₗ[ℂ] ω.toPositiveLinearMap.GNS where
  toFun := gnsVec ω
  map_add' a b := by
    simp only [gnsVec, map_add]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c a := by
    simp only [gnsVec, map_smul, RingHom.id_apply]
    exact UniformSpace.Completion.coe_smul _ _

omit [VonNeumannAlgebra A] in
@[simp] theorem gnsVecₗ_apply (ω : NPFunctional A) (a : A) :
    gnsVecₗ ω a = gnsVec ω a := rfl

omit [VonNeumannAlgebra A] in
/-- `gnsVec ω : A → ℋ_ω` is isometric for `‖·‖_ω`. -/
theorem gnsVec_norm (ω : NPFunctional A) (a : A) :
    ‖gnsVec ω a‖ = omegaNorm A ω a := by
  rw [gnsVec, UniformSpace.Completion.norm_coe, omegaNorm_eq_norm]

omit [VonNeumannAlgebra A] in
/-- **72V** (`normal-functionals-lemma`, vn.tex:3887, Lemma): for an
np-functional `ω` and a linear `f : A → ℂ` the following are equivalent:
(1) `|f(a)| ≤ B` on some `‖·‖_ω`-ball of radius `δ > 0`;
(2) `|f(a)| ≤ B ‖a‖_ω` for some `B > 0`;
(3) `f = [b, ·]_ω` for some `b` in the Hilbert space completion `H_ω` of
`A` for the inner product `[a, c]_ω = ω(a* c)` (rendered by an existential
completion `φ : A → H`).

**Erratum (ours).**  vn.tex:3887 lists a fourth equivalent condition,

> (4) `f = f₀ + i f₁ - f₂ - i f₃` where the `f_k` are np-maps for which
> there is `B > 0` with `f_k(a) ≤ B ω(a)` for all `a ∈ A⁺` and all `k`,

and it is **not** equivalent to (1)–(3): it is strictly stronger.  It is the
domination clause that is wrong, and the defect is in the last paragraph of
the proof at vn.tex:3981, which asserts `(c*ω)(a) ≡ ω(c* a c) ≤ ‖c‖_ω ω(a)`
for `a ∈ A⁺`.  That inequality is not even homogeneous in `ω` (replacing `ω`
by `tω` scales the left side by `t` and the right by `t^{3/2}` — the same
defect as the two errata on **72III** above), and no rescaling repairs it:
`ω(c* a c) ≤ C ω(a)` is false for `C = ‖c‖²` and false for every constant.

Counterexample (`normal_functionals_lemma_four_counterexample` below).  Take
`A = B(H)` with `H` of dimension `≥ 2`, `ξ ⊥ η` unit vectors,
`ω = ⟪ξ, (·) ξ⟫` and `f = ⟪η, (·) ξ⟫`.  Then `‖a‖_ω = ‖aξ‖`, so
`|f(a)| ≤ ‖a‖_ω` and (2) holds with `B = 1` (hence (1) and (3) too).  But
let `y = |ξ⟩⟨η|` and `p = y* y = |η⟩⟨η|`.  Then `ω(p) = ‖yξ‖² = 0`, so any
np-map `g ≤ B ω` on `A⁺` has `g(p) = 0`, whence `‖y‖_g ≡ g(y* y)^½ = 0` and,
by Cauchy–Schwarz (Kadison), `g(y* z) = 0` for **every** `z`; in particular
`g(p x) = 0` for every `x`.  A decomposition as in (4) would therefore force
`f(p x) = 0` for all `x`, while for `x = |η⟩⟨ξ|` one has `x ξ = η` and so
`f(p x) = ⟪η, p η⟫ = ⟪y η, y η⟫ = ‖ξ‖² = 1`.

So the ω-bounded functionals are *not* spanned by the ω-dominated np-maps:
in the example the latter are exactly `ℝ≥0 · ω`, a one-dimensional cone,
while the former form a two-dimensional space.  This is not repairable by a
different pointwise condition on the `f_k` either — the same argument kills
`|f_k(a)| ≤ B‖a‖_ω` and `f_k(a* a) ≤ B ω(a* a)`.

What survives, and what the thesis actually uses in **72XI**, are the two
one-way implications, proved separately below:
`normal_functionals_lemma_of_dominated` ((4) ⇒ (1), the thesis's argument at
vn.tex:3914, unchanged) and `normal_functionals_decomposition` ((3) ⇒ (4)
*minus* the domination clause, the thesis's argument at vn.tex:3955, whose
polarisation and Cauchy-limit steps are correct).  In **72XI** the
domination is recovered against the *new* np-map `ω' = Σ_k f_k`, not against
the given `ω`, which is all that corollary needs. -/
theorem normal_functionals_lemma (ω : NPFunctional A) (f : A →ₗ[ℂ] ℂ) :
    List.TFAE
      [∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
        ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ B,
       ∃ B : ℝ, 0 < B ∧ ∀ a : A, ‖f a‖ ≤ B * omegaNorm A ω a,
       ∃ (ι : Type u) (φ : A →ₗ[ℂ] lp (fun _ : ι => ℂ) 2),
        DenseRange ⇑φ ∧
        (∀ a c : A, ⟪φ a, φ c⟫ = ω (star a * c)) ∧
        ∃ b : lp (fun _ : ι => ℂ) 2, ∀ a : A, f a = ⟪b, φ a⟫] := by
  -- (1) ⇒ (2) is the thesis's rescaling `ã = δ(ε + ‖a‖_ω)⁻¹ a` (vn.tex:3930).
  tfae_have 1 → 2 := by
    rintro ⟨δ, B, hδ, hB, h⟩
    refine ⟨B / δ, by positivity, fun a => le_of_forall_sub_le fun ε hε => ?_⟩
    set s : ℝ := omegaNorm A ω a with hs
    have hs0 : 0 ≤ s := omegaNorm_nonneg ω a
    set η : ℝ := ε * δ / B with hη
    have hη0 : 0 < η := by rw [hη]; positivity
    set t : ℝ := δ / (η + s) with ht
    have ht0 : 0 < t := by rw [ht]; positivity
    have hball : omegaNorm A ω ((t : ℂ) • a) ≤ δ := by
      rw [omegaNorm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le, ht, ← hs,
        div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hfa : t * ‖f a‖ ≤ B := by
      have hx := h _ hball
      rwa [map_smul, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ht0.le] at hx
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hfa
    have hBη : B * η = ε * δ := by rw [hη]; field_simp
    have key : δ * (‖f a‖ - ε) ≤ δ * (B / δ * s) := by
      have hrw : δ * (B / δ * s) = B * s := by field_simp
      rw [hrw]
      nlinarith
    exact le_of_mul_le_mul_left key hδ
  -- (2) ⇒ (3): `f` extends to a bounded functional on the GNS completion
  -- `ℋ_ω`, Riesz gives the vector, and a Hilbert basis transports `ℋ_ω` to
  -- `ℓ²(w)` (vn.tex:3943; the transport is ours, the thesis leaves `ℋ_ω`
  -- abstract).
  tfae_have 2 → 3 := by
    rintro ⟨B, hB, hf⟩
    have hbound : ∀ a : A, ‖f a‖ ≤ B * ‖gnsVecₗ ω a‖ := by
      intro a; rw [gnsVecₗ_apply, gnsVec_norm]; exact hf a
    have hdense : DenseRange ⇑(gnsVecₗ ω) := gnsVec_denseRange ω
    obtain ⟨w, bas, -⟩ := exists_hilbertBasis ℂ ω.toPositiveLinearMap.GNS
    refine ⟨w, bas.repr.toLinearEquiv.toLinearMap ∘ₗ gnsVecₗ ω, ?_, ?_, ?_⟩
    · exact bas.repr.surjective.denseRange.comp hdense bas.repr.continuous
    · intro a c
      change (⟪bas.repr (gnsVec ω a), bas.repr (gnsVec ω c)⟫ : ℂ) = _
      rw [LinearIsometryEquiv.inner_map_map]
      exact gnsVec_inner ω a c
    · set F : ω.toPositiveLinearMap.GNS →L[ℂ] ℂ :=
        f.extendOfNorm (gnsVecₗ ω) with hFdef
      have hFe : ∀ a : A, F (gnsVecₗ ω a) = f a := fun a =>
        LinearMap.extendOfNorm_eq hdense ⟨B, hbound⟩ a
      refine ⟨bas.repr ((InnerProductSpace.toDual ℂ _).symm F), fun a => ?_⟩
      change _ = (⟪bas.repr ((InnerProductSpace.toDual ℂ _).symm F),
        bas.repr (gnsVec ω a)⟫ : ℂ)
      rw [LinearIsometryEquiv.inner_map_map, InnerProductSpace.toDual_symm_apply]
      exact (hFe a).symm
  -- (3) ⇒ (1) is Cauchy–Schwarz in `ℓ²(ι)`: `‖φ a‖ = ‖a‖_ω`.
  tfae_have 3 → 1 := by
    rintro ⟨ι, φ, -, hinner, b, hb⟩
    have hnorm : ∀ a : A, ‖φ a‖ = omegaNorm A ω a := by
      intro a
      have h2 : (ω (star a * a)).re = ‖φ a‖ ^ 2 := by
        rw [← hinner a a]
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (φ a)
      rw [omegaNorm, h2, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨1, ‖b‖ + 1, one_pos, by positivity, fun a ha => ?_⟩
    calc ‖f a‖ = ‖(⟪b, φ a⟫ : ℂ)‖ := by rw [hb]
      _ ≤ ‖b‖ * ‖φ a‖ := norm_inner_le_norm _ _
      _ ≤ ‖b‖ * 1 := by
          rw [hnorm]; exact mul_le_mul_of_nonneg_left ha (norm_nonneg b)
      _ ≤ ‖b‖ + 1 := by nlinarith [norm_nonneg b]
  tfae_finish

omit [VonNeumannAlgebra A] in
/-- **72V**, the implication (4) ⇒ (1) of vn.tex:3887 (proof at vn.tex:3914):
a linear functional that decomposes into np-maps *dominated by* `B·ω` is
bounded on the unit `‖·‖_ω`-ball.  This half of the thesis's fourth clause is
correct; the converse is not — see the erratum on
`normal_functionals_lemma`. -/
theorem normal_functionals_lemma_of_dominated (ω : NPFunctional A)
    (f : A →ₗ[ℂ] ℂ) (g : Fin 4 → NPFunctional A) (B : ℝ) (hB : 0 < B)
    (hf : ∀ a : A, f a = g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a)
    (hdom : ∀ (k : Fin 4) (a : A), 0 ≤ a → (g k a).re ≤ B * (ω a).re) :
    ∃ δ B' : ℝ, 0 < δ ∧ 0 < B' ∧
      ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ B' := by
  -- `‖a‖_{f_k} ≤ √B ‖a‖_ω`, since `f_k(a* a) ≤ B ω(a* a)`
  have hk : ∀ (k : Fin 4) (a : A),
      omegaNorm A (g k) a ≤ Real.sqrt B * omegaNorm A ω a := by
    intro k a
    rw [omegaNorm, omegaNorm, ← Real.sqrt_mul hB.le]
    exact Real.sqrt_le_sqrt (hdom k _ (star_mul_self_nonneg a))
  -- Kadison: `|f_k(a)| ≤ ‖a‖_{f_k} f_k(1)^½ ≤ √B f_k(1)^½ ‖a‖_ω`
  have hgk : ∀ (k : Fin 4) (a : A),
      ‖g k a‖ ≤ Real.sqrt B * Real.sqrt ((g k 1).re) * omegaNorm A ω a := by
    intro k a
    calc ‖g k a‖ ≤ omegaNorm A (g k) a * Real.sqrt ((g k 1).re) :=
          norm_apply_le_omegaNorm (g k) a
      _ ≤ Real.sqrt B * omegaNorm A ω a * Real.sqrt ((g k 1).re) :=
          mul_le_mul_of_nonneg_right (hk k a) (Real.sqrt_nonneg _)
      _ = _ := by ring
  set C : ℝ := Real.sqrt B * Real.sqrt ((g 0 1).re) +
    Real.sqrt B * Real.sqrt ((g 1 1).re) + Real.sqrt B * Real.sqrt ((g 2 1).re) +
    Real.sqrt B * Real.sqrt ((g 3 1).re) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨1, C + 1, one_pos, by linarith, fun a ha => ?_⟩
  have hb : ∀ k : Fin 4, ‖g k a‖ ≤ Real.sqrt B * Real.sqrt ((g k 1).re) := by
    intro k
    refine (hgk k a).trans ?_
    have h1 : (0 : ℝ) ≤ Real.sqrt B * Real.sqrt ((g k 1).re) := by positivity
    nlinarith [omegaNorm_nonneg ω a]
  have e1 := norm_sub_le (g 0 a + Complex.I * g 1 a - g 2 a) (Complex.I * g 3 a)
  have e2 := norm_sub_le (g 0 a + Complex.I * g 1 a) (g 2 a)
  have e3 := norm_add_le (g 0 a) (Complex.I * g 1 a)
  have hI1 : ‖Complex.I * g 1 a‖ = ‖g 1 a‖ := by simp
  have hI3 : ‖Complex.I * g 3 a‖ = ‖g 3 a‖ := by simp
  rw [hf a]
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  have b3 := hb 3
  rw [hCdef]
  linarith

/-- The vectors `½(iᵏ b + 1)` of the polarisation identity. -/
private noncomputable def polVec (b : A) (k : Fin 4) : A :=
  (2 : ℂ)⁻¹ • (Complex.I ^ (k : ℕ) • b + 1)

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- **Polarisation** (**44II**, `mult-polarization`, vn.tex:643, cited in
72V's proof at vn.tex:3970):
`b* a = Σₖ iᵏ (½(iᵏb+1))* a (½(iᵏb+1))`.  (The thesis writes it as
`¼ Σₖ iᵏ (iᵏb+1)* a (iᵏb+1)`; halving `b+1` absorbs the `¼`, which is what
lets the summands stay np-*functionals* — there is no positive scalar
multiple on the np-cone in `Theses/A/VN/Basic.lean`.) -/
private theorem polarisation_four (b a : A) :
    ∑ k : Fin 4, Complex.I ^ (k : ℕ) • (star (polVec b k) * a * polVec b k)
      = star b * a := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  have hv3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [polVec, Fin.sum_univ_four, Fin.isValue, Fin.val_zero, Fin.val_one,
    Fin.val_two, hv3, pow_zero, pow_one, hI2, hI3, star_smul, star_add, star_one,
    smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num [Complex.ext_iff]
  match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring)

/-- **72V**, the implication (3) ⇒ (4) of vn.tex:3887 (proof at vn.tex:3955),
*minus its domination clause*: an `ω`-bounded linear functional is a
combination `f₀ + i f₁ − f₂ − i f₃` of np-functionals.

The thesis's argument, unchanged apart from the two adjustments forced on us:
a `‖·‖_ω`-Cauchy sequence `b₁, b₂, …` in `A` approximating the Riesz vector
`b ∈ ℋ_ω`, polarisation, and `bstaromega_cauchy` (**72III**.2) for the
limits.  The *domination* `f_k ≤ B ω` claimed in vn.tex:3981 is **omitted**
because it is false — see the erratum on `normal_functionals_lemma`. -/
theorem normal_functionals_decomposition (ω : NPFunctional A) (f : A →ₗ[ℂ] ℂ)
    (hbdd : ∃ B : ℝ, 0 < B ∧ ∀ a : A, ‖f a‖ ≤ B * omegaNorm A ω a) :
    ∃ g : Fin 4 → NPFunctional A, ∀ a : A,
      f a = g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a := by
  classical
  obtain ⟨B, hB, hf⟩ := hbdd
  -- `f` extends to `ℋ_ω` and Riesz gives the vector `b₀`
  have hbound : ∀ a : A, ‖f a‖ ≤ B * ‖gnsVecₗ ω a‖ := by
    intro a; rw [gnsVecₗ_apply, gnsVec_norm]; exact hf a
  have hdense : DenseRange ⇑(gnsVecₗ ω) := gnsVec_denseRange ω
  set F : ω.toPositiveLinearMap.GNS →L[ℂ] ℂ :=
    f.extendOfNorm (gnsVecₗ ω) with hFdef
  have hFe : ∀ a : A, F (gnsVec ω a) = f a := fun a =>
    LinearMap.extendOfNorm_eq hdense ⟨B, hbound⟩ a
  set b₀ : ω.toPositiveLinearMap.GNS :=
    (InnerProductSpace.toDual ℂ _).symm F with hb₀def
  have hb₀ : ∀ a : A, f a = ⟪b₀, gnsVec ω a⟫ := by
    intro a
    rw [hb₀def, InnerProductSpace.toDual_symm_apply, hFe]
  -- a sequence in `A` converging to `b₀` in `ℋ_ω`
  have hex : ∀ n : ℕ, ∃ c : A, ‖gnsVec ω c - b₀‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := hdense.exists_dist_lt b₀ (ε := 1 / (n + 1)) (by positivity)
    exact ⟨c, by rwa [← dist_eq_norm, dist_comm]⟩
  choose c hc using hex
  have hctend : Tendsto (fun n => gnsVec ω (c n)) atTop (𝓝 b₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_eq_norm]
    exact (hc n).le
  -- `(c n)` is `‖·‖_ω`-Cauchy
  have hcauchy0 : Tendsto (fun p : ℕ × ℕ => omegaNorm A ω (c p.1 - c p.2))
      (atTop ×ˢ atTop) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun p => omegaNorm_nonneg ω _)
      (Eventually.of_forall fun p => ?_)
      (g := fun p : ℕ × ℕ => 1 / ((p.1 : ℝ) + 1) + 1 / ((p.2 : ℝ) + 1)) ?_
    · have hlin : gnsVec ω (c p.1 - c p.2) = gnsVec ω (c p.1) - gnsVec ω (c p.2) := by
        simpa using (gnsVecₗ ω).map_sub (c p.1) (c p.2)
      rw [← gnsVec_norm, hlin]
      calc ‖gnsVec ω (c p.1) - gnsVec ω (c p.2)‖
          ≤ ‖gnsVec ω (c p.1) - b₀‖ + ‖b₀ - gnsVec ω (c p.2)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 / ((p.1 : ℝ) + 1) + 1 / ((p.2 : ℝ) + 1) := by
            have h2 : ‖b₀ - gnsVec ω (c p.2)‖ = ‖gnsVec ω (c p.2) - b₀‖ :=
              norm_sub_rev _ _
            rw [h2]
            exact add_le_add (hc p.1).le (hc p.2).le
    · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (h1.comp tendsto_fst).add
        (h1.comp (tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ))))
  -- hence so is each `½(iᵏ c n + 1)`, and `72III`.2 provides the limits
  have hall : ∀ k : Fin 4, ∃ G : NPFunctional A, ∀ ε : ℝ, 0 < ε → ∃ N,
      ∀ n ≥ N, ∀ a : A,
        ‖bStarOmega A (polVec (c n) k) ω a - G a‖ ≤ ε * ‖a‖ := by
    intro k
    refine bstaromega_cauchy ω (fun n => polVec (c n) k) ?_
    have hsub : ∀ p : ℕ × ℕ, polVec (c p.1) k - polVec (c p.2) k
        = ((2 : ℂ)⁻¹ * Complex.I ^ (k : ℕ)) • (c p.1 - c p.2) := by
      intro p
      simp only [polVec, smul_sub, smul_add, smul_smul]
      abel
    have heq : ∀ p : ℕ × ℕ,
        omegaNorm A ω (polVec (c p.1) k - polVec (c p.2) k)
          = ‖((2 : ℂ)⁻¹ * Complex.I ^ (k : ℕ))‖ * omegaNorm A ω (c p.1 - c p.2) := by
      intro p; rw [hsub p, omegaNorm_smul]
    simp only [heq]
    simpa using hcauchy0.const_mul ‖((2 : ℂ)⁻¹ * Complex.I ^ (k : ℕ))‖
  choose G hG using hall
  -- the convergence `(iᵏcₙ+1)*ω → f_k` is pointwise
  have hconv : ∀ (k : Fin 4) (a : A),
      Tendsto (fun n => bStarOmega A (polVec (c n) k) ω a) atTop (𝓝 (G k a)) := by
    intro k a
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hG k (ε / (‖a‖ + 1)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hN n hn a) ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg a, norm_nonneg (a : A)]
  refine ⟨G, fun a => ?_⟩
  -- `f a = lim ω(cₙ* a) = lim Σₖ iᵏ (½(iᵏcₙ+1))*ω (a) = Σₖ iᵏ f_k(a)`
  have hlim1 : Tendsto (fun n => (ω (star (c n) * a) : ℂ)) atTop (𝓝 (f a)) := by
    have hconst : Tendsto (fun _ : ℕ => gnsVec ω a) atTop (𝓝 (gnsVec ω a)) :=
      tendsto_const_nhds
    have h := Filter.Tendsto.inner (𝕜 := ℂ) hctend hconst
    rw [← hb₀ a] at h
    simpa only [gnsVec_inner] using h
  have hpol : ∀ n : ℕ, (ω (star (c n) * a) : ℂ)
      = bStarOmega A (polVec (c n) 0) ω a
        + Complex.I * bStarOmega A (polVec (c n) 1) ω a
        - bStarOmega A (polVec (c n) 2) ω a
        - Complex.I * bStarOmega A (polVec (c n) 3) ω a := by
    intro n
    simp only [bStarOmega]
    have hsmul : ∀ (z : ℂ) (x : A), (ω (z • x) : ℂ) = z * ω x := fun z x => by
      have hz := map_smul ω.toPositiveLinearMap z x
      simp only [smul_eq_mul] at hz
      exact hz
    have hv3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have h := congrArg (fun x : A => (ω x : ℂ)) (polarisation_four (c n) a)
    simp only [Fin.sum_univ_four, Fin.isValue, Fin.val_zero, Fin.val_one,
      Fin.val_two, hv3, pow_zero, pow_one] at h
    rw [← h, npFunctional_add, npFunctional_add, npFunctional_add,
      hsmul, hsmul, hsmul, hsmul]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    rw [hI2, hI3]
    ring
  have hlim2 : Tendsto (fun n => (ω (star (c n) * a) : ℂ)) atTop
      (𝓝 (G 0 a + Complex.I * G 1 a - G 2 a - Complex.I * G 3 a)) := by
    simp only [hpol]
    exact (((hconv 0 a).add (((hconv 1 a)).const_mul Complex.I)).sub
      (hconv 2 a)).sub ((hconv 3 a).const_mul Complex.I)
  exact tendsto_nhds_unique hlim1 hlim2

/-! ### The counterexample to **72V**.(4)

See the erratum on `normal_functionals_lemma`.  On `B(H)` with `dim H ≥ 2`,
the vector functional `ω = ⟪ξ, (·) ξ⟫` and the functional
`f = ⟪η, (·) ξ⟫` (for orthonormal `ξ, η`) satisfy `|f(a)| ≤ ‖a‖_ω` — so all
three conditions of `normal_functionals_lemma` hold — while `f` admits no
decomposition into np-maps dominated by any multiple of `ω`. -/

section Counterexample

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- `f = ⟪η, (·) ξ⟫` as a linear functional on `B(H)`. -/
noncomputable def vectorPairFunctional (ξ η : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun a := ⟪η, a ξ⟫
  map_add' a b := by simp
  map_smul' c a := by simp

omit [CompleteSpace H] in
@[simp] theorem vectorPairFunctional_apply (ξ η : H) (a : H →L[ℂ] H) :
    vectorPairFunctional ξ η a = ⟪η, a ξ⟫ := rfl

/-- `‖a‖_ω = ‖a ξ‖` for the vector functional `ω = ⟪ξ, (·) ξ⟫` on `B(H)`. -/
theorem omegaNorm_vectorNP (ξ : H) (a : H →L[ℂ] H) :
    omegaNorm (H →L[ℂ] H) (vectorNP ξ) a = ‖a ξ‖ := by
  have h : ((vectorNP ξ) (star a * a)).re = ‖a ξ‖ ^ 2 := by
    have h1 : ((vectorNP ξ) (star a * a) : ℂ) = ⟪a ξ, a ξ⟫ := by
      change (⟪ξ, (star a * a) ξ⟫ : ℂ) = _
      rw [ContinuousLinearMap.star_eq_adjoint]
      change (⟪ξ, ContinuousLinearMap.adjoint a (a ξ)⟫ : ℂ) = _
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [h1]
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (a ξ)
  rw [omegaNorm, h, Real.sqrt_sq (norm_nonneg _)]

/-- **Counterexample to 72V.(4)** (ours).  For orthonormal `ξ, η` in a
Hilbert space `H`, the functional `f = ⟪η, (·) ξ⟫` on `B(H)` satisfies
condition (2) of `normal_functionals_lemma` with respect to the np-functional
`ω = ⟪ξ, (·) ξ⟫` (hence conditions (1) and (3) as well), but it is **not** a
combination `f₀ + i f₁ - f₂ - i f₃` of np-maps dominated by any `B·ω` on the
positive cone.  So vn.tex:3887's fourth clause is strictly stronger than the
other three. -/
theorem normal_functionals_lemma_four_counterexample
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (horth : (⟪ξ, η⟫ : ℂ) = 0) :
    (∀ a : H →L[ℂ] H,
        ‖vectorPairFunctional ξ η a‖ ≤ 1 *
          omegaNorm (H →L[ℂ] H) (vectorNP ξ) a) ∧
      ¬ ∃ (g : Fin 4 → NPFunctional (H →L[ℂ] H)) (B : ℝ), 0 < B ∧
        (∀ a : H →L[ℂ] H, vectorPairFunctional ξ η a =
          g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a) ∧
        ∀ (k : Fin 4) (a : H →L[ℂ] H), 0 ≤ a →
          (g k a).re ≤ B * ((vectorNP ξ) a).re := by
  classical
  set y : H →L[ℂ] H := ketbra ξ η with hy
  have hyapp : ∀ u : H, y u = (⟪η, u⟫ : ℂ) • ξ := fun u => rfl
  set x : H →L[ℂ] H := ketbra η ξ with hx
  have hxapp : ∀ u : H, x u = (⟪ξ, u⟫ : ℂ) • η := fun u => rfl
  set p : H →L[ℂ] H := star y * y with hp
  -- `⟪u, p v⟫ = ⟪y u, y v⟫`
  have hpinner : ∀ u v : H, (⟪u, p v⟫ : ℂ) = ⟪y u, y v⟫ := by
    intro u v
    rw [hp, ContinuousLinearMap.star_eq_adjoint]
    change (⟪u, ContinuousLinearMap.adjoint y (y v)⟫ : ℂ) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
  refine ⟨fun a => ?_, ?_⟩
  · rw [one_mul, omegaNorm_vectorNP, vectorPairFunctional_apply]
    calc ‖(⟪η, a ξ⟫ : ℂ)‖ ≤ ‖η‖ * ‖a ξ‖ := norm_inner_le_norm _ _
      _ = ‖a ξ‖ := by rw [hη, one_mul]
  rintro ⟨g, B, hB, hdec, hdom⟩
  -- `ω(p) = ‖y ξ‖² = 0`, because `y ξ = ⟪η, ξ⟫ • ξ = 0`
  have hyξ : y ξ = 0 := by
    rw [hyapp, ← inner_conj_symm, horth]
    simp
  have hωp : ((vectorNP ξ) p).re = 0 := by
    change (⟪ξ, p ξ⟫ : ℂ).re = 0
    rw [hpinner, hyξ]
    simp
  have hp0 : (0 : H →L[ℂ] H) ≤ p := star_mul_self_nonneg y
  -- hence every `f_k` kills `p`, and so, by Cauchy–Schwarz, kills `y* z`
  have hgp : ∀ k : Fin 4, omegaNorm (H →L[ℂ] H) (g k) y = 0 := by
    intro k
    have hle : (g k p).re ≤ 0 := by
      have := hdom k p hp0
      rw [hωp, mul_zero] at this
      exact this
    have hge : (0 : ℝ) ≤ (g k p).re :=
      (Complex.le_def.mp (npFunctional_nonneg (g k) hp0)).1
    have : (g k (star y * y)).re = 0 := by rw [← hp]; linarith
    rw [omegaNorm, this, Real.sqrt_zero]
  have hkill : ∀ (k : Fin 4) (z : H →L[ℂ] H), g k (star y * z) = 0 := by
    intro k z
    have h := norm_apply_star_mul_le (g k) y z
    rw [hgp k, zero_mul] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  -- so `f (p * x) = 0`, while `f (p * x) = ‖y η‖² = ‖ξ‖² = 1`
  have hfzero : vectorPairFunctional ξ η (star y * (y * x)) = 0 := by
    rw [hdec, hkill 0, hkill 1, hkill 2, hkill 3]
    ring
  have hyη : y η = ξ := by
    rw [hyapp, inner_self_eq_norm_sq_to_K, hη]
    simp
  have hxξ : x ξ = η := by
    rw [hxapp, inner_self_eq_norm_sq_to_K, hξ]
    simp
  have hfone : vectorPairFunctional ξ η (star y * (y * x)) = 1 := by
    rw [vectorPairFunctional_apply]
    have hassoc : star y * (y * x) = p * x := by rw [hp, mul_assoc]
    rw [hassoc]
    change (⟪η, p (x ξ)⟫ : ℂ) = 1
    rw [hxξ, hpinner, hyη, inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  rw [hfzero] at hfone
  exact zero_ne_one hfone

/-- The counterexample is inhabited (`H = ℂ²`, `ξ, η` the standard basis),
so the four conditions of vn.tex:3887 are genuinely *not* equivalent:
condition (2) holds here and condition (4) fails. -/
theorem normal_functionals_lemma_four_not_equivalent :
    ∃ (ω : NPFunctional
        (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      (f : (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) →ₗ[ℂ] ℂ),
      (∀ a : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
          ‖f a‖ ≤ 1 * omegaNorm _ ω a) ∧
      ¬ ∃ (g : Fin 4 → NPFunctional
            (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
          (B : ℝ), 0 < B ∧
          (∀ a : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
            f a = g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a) ∧
          ∀ (k : Fin 4) (a : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
            0 ≤ a → (g k a).re ≤ B * (ω a).re := by
  classical
  set ξ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1 with hξdef
  set η : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1 with hηdef
  have hξ : ‖ξ‖ = 1 := by rw [hξdef]; simp
  have hη : ‖η‖ = 1 := by rw [hηdef]; simp
  have horth : (⟪ξ, η⟫ : ℂ) = 0 := by
    rw [hξdef, hηdef, EuclideanSpace.inner_single_left]
    simp
  exact ⟨vectorNP ξ, vectorPairFunctional ξ η,
    normal_functionals_lemma_four_counterexample ξ η hξ hη horth⟩

end Counterexample

/-- **72XI** (`luws`, vn.tex:3989, Corollary): for a linear functional
`f : A → ℂ` on a von Neumann algebra the following are equivalent:
(1) `f` is ultrastrongly continuous; (2) `f` is ultraweakly continuous;
(3) `f = f₀ + i f₁ - f₂ - i f₃` for np-functionals `f_k`; (4) `f` is
bounded on some `‖·‖_ω`-ball; (5) `|f(a)| ≤ ‖a‖_ω` for some
np-functional `ω`. -/
theorem luws (f : A →ₗ[ℂ] ℂ) :
    List.TFAE
      [@Continuous A ℂ (ultrastrong A) _ ⇑f,
       @Continuous A ℂ (ultraweak A) _ ⇑f,
       ∃ g : Fin 4 → NPFunctional A, ∀ a : A,
        f a = g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a,
       ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
        BddAbove {r : ℝ | ∃ a : A, omegaNorm A ω a ≤ δ ∧ r = ‖f a‖},
       ∃ ω : NPFunctional A, ∀ a : A, ‖f a‖ ≤ omegaNorm A ω a] := by
  tfae_have 1 → 4 := by
    intro hcont
    have hopen : @IsOpen A (ultrastrong A) (⇑f ⁻¹' Metric.ball (0 : ℂ) 1) :=
      (@continuous_def A ℂ (ultrastrong A) _ _).mp hcont _ Metric.isOpen_ball
    have hmem : (0 : A) ∈ ⇑f ⁻¹' Metric.ball (0 : ℂ) 1 := by
      simp [Set.mem_preimage, map_zero]
    obtain ⟨ω, δ, hδ, hsub⟩ := exists_ultrastrong_ball_of_isOpen hopen 0 hmem
    refine ⟨ω, δ / 2, by positivity, 1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have hball : a ∈ {x : A | omegaNorm A ω (x - 0) < δ} := by
      simp only [sub_zero, Set.mem_ofPred_eq]
      linarith
    have := hsub hball
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at this
    exact this.le
  tfae_have 4 → 3 := by
    rintro ⟨ω, δ, hδ, B₀, hB₀⟩
    have h1 : ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
        ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ B := by
      refine ⟨δ, |B₀| + 1, hδ, by positivity, fun a ha => ?_⟩
      have := hB₀ ⟨a, ha, rfl⟩
      have hle : B₀ ≤ |B₀| := le_abs_self B₀
      linarith
    exact normal_functionals_decomposition ω f
      ((normal_functionals_lemma ω f).out 0 1 |>.mp h1)
  tfae_have 3 → 2 := by
    rintro ⟨g, hg⟩
    let _ : TopologicalSpace A := ultraweak A
    have heq : ⇑f = fun a : A =>
        (g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a : ℂ) := funext hg
    rw [heq]
    exact (((continuous_ultraweak_npFunctional (g 0)).add
        (continuous_const.mul (continuous_ultraweak_npFunctional (g 1)))).sub
        (continuous_ultraweak_npFunctional (g 2))).sub
      (continuous_const.mul (continuous_ultraweak_npFunctional (g 3)))
  tfae_have 2 → 1 := fun h => continuous_le_dom ultrastrong_le_ultraweak h
  tfae_have 3 → 5 := by
    rintro ⟨g, hg⟩
    -- `ω' = Σₖ fₖ` dominates every `‖·‖_{fₖ}`
    set ω' : NPFunctional A := addNP (addNP (g 0) (g 1)) (addNP (g 2) (g 3)) with hω'
    have hdom : ∀ k : Fin 4, ∀ a : A, omegaNorm A (g k) a ≤ omegaNorm A ω' a := by
      intro k a
      fin_cases k
      · exact le_trans (omegaNorm_le_addNP (g 0) (g 1) a)
          (omegaNorm_le_addNP _ _ a)
      · exact le_trans (omegaNorm_le_addNP' (g 0) (g 1) a)
          (omegaNorm_le_addNP _ _ a)
      · exact le_trans (omegaNorm_le_addNP (g 2) (g 3) a)
          (omegaNorm_le_addNP' _ _ a)
      · exact le_trans (omegaNorm_le_addNP' (g 2) (g 3) a)
          (omegaNorm_le_addNP' _ _ a)
    set C : ℝ := Real.sqrt ((g 0 1).re) + Real.sqrt ((g 1 1).re) +
      Real.sqrt ((g 2 1).re) + Real.sqrt ((g 3 1).re) with hC
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    have hk : ∀ (k : Fin 4) (a : A),
        ‖(g k a : ℂ)‖ ≤ Real.sqrt ((g k 1).re) * omegaNorm A ω' a := by
      intro k a
      calc ‖(g k a : ℂ)‖ ≤ omegaNorm A (g k) a * Real.sqrt ((g k 1).re) :=
            norm_apply_le_omegaNorm (g k) a
        _ ≤ omegaNorm A ω' a * Real.sqrt ((g k 1).re) :=
            mul_le_mul_of_nonneg_right (hdom k a) (Real.sqrt_nonneg _)
        _ = _ := by ring
    have hbound : ∀ a : A, ‖f a‖ ≤ C * omegaNorm A ω' a := by
      intro a
      have e1 := norm_sub_le (g 0 a + Complex.I * g 1 a - g 2 a) (Complex.I * g 3 a)
      have e2 := norm_sub_le (g 0 a + Complex.I * g 1 a) (g 2 a)
      have e3 := norm_add_le (g 0 a) (Complex.I * g 1 a)
      have hI1 : ‖Complex.I * g 1 a‖ = ‖(g 1 a : ℂ)‖ := by simp
      have hI3 : ‖Complex.I * g 3 a‖ = ‖(g 3 a : ℂ)‖ := by simp
      have b0 := hk 0 a
      have b1 := hk 1 a
      have b2 := hk 2 a
      have b3 := hk 3 a
      rw [hg a, hC]
      ring_nf
      ring_nf at e1 e2 e3 b0 b1 b2 b3 hI1 hI3
      linarith
    refine ⟨smulNP (by positivity : (0:ℝ) ≤ C ^ 2) ω', fun a => ?_⟩
    rw [omegaNorm_smulNP, Real.sqrt_sq hC0]
    exact hbound a
  tfae_have 5 → 4 := by
    rintro ⟨ω, hω⟩
    refine ⟨ω, 1, one_pos, 1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact le_trans (hω a) ha
  tfae_finish

end Functionals

/-! ## Parsec 730: radially open sets and Hahn–Banach

**73I** (vn.tex:4019): introduction — nothing to formalize. -/

section Radial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (V) in
/-- **73II** (vn.tex:4025, Definition): a subset `s` of a real vector space
is **radially open** if from each of its points every ray initially stays
in `s`. -/
def RadiallyOpen (s : Set V) : Prop :=
  ∀ a ∈ s, ∀ v : V, ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 ≤ r → r < t → a + r • v ∈ s

variable (V) in
/-- **73III** (vn.tex:4033, Exercise), part 1: the radially open subsets of
a real vector space form a topology. -/
def radialTopology : TopologicalSpace V where
  IsOpen := RadiallyOpen V
  isOpen_univ := fun _ _ _ => ⟨1, one_pos, fun _ _ _ => Set.mem_univ _⟩
  isOpen_inter := by
    rintro s t hs ht a ⟨has, hat⟩ v
    obtain ⟨t₁, ht₁, h₁⟩ := hs a has v
    obtain ⟨t₂, ht₂, h₂⟩ := ht a hat v
    exact ⟨min t₁ t₂, lt_min ht₁ ht₂, fun r hr0 hr =>
      ⟨h₁ r hr0 (lt_of_lt_of_le hr (min_le_left _ _)),
        h₂ r hr0 (lt_of_lt_of_le hr (min_le_right _ _))⟩⟩
  isOpen_sUnion := by
    rintro S hS a ⟨u, huS, hau⟩ v
    obtain ⟨d, hd, h⟩ := hS u huS a hau v
    exact ⟨d, hd, fun r hr0 hr => ⟨u, huS, h r hr0 hr⟩⟩

/-- **73III** (vn.tex:4033, Exercise), part 2: with respect to the radial
topology, translations and scalar multiplication are continuous.
(Parts 3–4 — a radially open non-open subset of `ℝ²`, and the failure of
joint continuity of addition — are pictorial counterexamples, not
converted.) -/
theorem radialTopology_continuous (a : V) (c : ℝ) :
    @Continuous V V (radialTopology V) (radialTopology V) (fun x => x + a) ∧
      @Continuous V V (radialTopology V) (radialTopology V)
        (fun x => c • x) := by
  constructor
  · refine (@continuous_def V V (radialTopology V) (radialTopology V) _).mpr ?_
    intro s hs
    change RadiallyOpen V _
    intro x hx v
    obtain ⟨d, hd, h⟩ := hs (x + a) hx v
    refine ⟨d, hd, fun r hr0 hr => ?_⟩
    change x + r • v + a ∈ s
    have e : x + r • v + a = x + a + r • v := by abel
    rw [e]
    exact h r hr0 hr
  · refine (@continuous_def V V (radialTopology V) (radialTopology V) _).mpr ?_
    intro s hs
    change RadiallyOpen V _
    intro x hx v
    obtain ⟨d, hd, h⟩ := hs (c • x) hx (c • v)
    refine ⟨d, hd, fun r hr0 hr => ?_⟩
    change c • (x + r • v) ∈ s
    have e : c • (x + r • v) = c • x + r • (c • v) := by
      rw [smul_add, smul_comm]
    rw [e]
    exact h r hr0 hr

/-- **73III** (vn.tex:4033, Exercise), part 5: for radially open
`s ⊆ V` and `x, y ∈ V` the set `{t ∈ ℝ | t•x + (1-t)•y ∈ s}` is open. -/
theorem radialTopology_segment (s : Set V) (hs : RadiallyOpen V s)
    (x y : V) : IsOpen {t : ℝ | t • x + (1 - t) • y ∈ s} := by
  rw [Metric.isOpen_iff]
  intro t₀ ht₀
  obtain ⟨d₁, hd₁, h₁⟩ := hs _ ht₀ (x - y)
  obtain ⟨d₂, hd₂, h₂⟩ := hs _ ht₀ (y - x)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, fun t ht => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at ht
  rcases le_or_gt t₀ t with hle | hlt
  · have hr : t - t₀ < d₁ := by
      have := lt_of_lt_of_le ht (min_le_left d₁ d₂)
      rw [abs_of_nonneg (by linarith)] at this
      linarith
    have := h₁ (t - t₀) (by linarith) hr
    have e : t₀ • x + (1 - t₀) • y + (t - t₀) • (x - y)
        = t • x + (1 - t) • y := by module
    rwa [e] at this
  · have hr : t₀ - t < d₂ := by
      have := lt_of_lt_of_le ht (min_le_right d₁ d₂)
      rw [abs_of_neg (by linarith)] at this
      linarith
    have := h₂ (t₀ - t) (by linarith) hr
    have e : t₀ • x + (1 - t₀) • y + (t₀ - t) • (y - x)
        = t • x + (1 - t) • y := by module
    rwa [e] at this

-- only `hs` is needed for the first half; `ht` is part of the exercise's
-- statement and is left unused:
set_option linter.unusedVariables false in
/-- **73III** (vn.tex:4033, Exercise), part 6: sums and positive dilates of
radially open sets are radially open. -/
theorem radialTopology_add (s t : Set V) (hs : RadiallyOpen V s)
    (ht : RadiallyOpen V t) :
    RadiallyOpen V (s + t) ∧
      RadiallyOpen V {x : V | ∃ l : ℝ, 0 < l ∧ ∃ a ∈ s, x = l • a} := by
  constructor
  · rintro a ⟨p, hp, q, hq, rfl⟩ v
    obtain ⟨d, hd, h⟩ := hs p hp v
    refine ⟨d, hd, fun r hr0 hr => ?_⟩
    have e : p + q + r • v = p + r • v + q := by abel
    rw [e]
    exact Set.add_mem_add (h r hr0 hr) hq
  · rintro z ⟨l, hl, a, ha, rfl⟩ v
    obtain ⟨d, hd, h⟩ := hs a ha v
    refine ⟨l * d, by positivity, fun r hr0 hr => ?_⟩
    refine ⟨l, hl, a + (r / l) • v, h (r / l) (by positivity) ?_, ?_⟩
    · rw [div_lt_iff₀ hl]
      linarith [mul_comm l d]
    · rw [smul_add, smul_smul, mul_div_cancel₀ r (ne_of_gt hl)]

/-- **73IV** (`hahn-banach`, vn.tex:4072, Theorem): for every radially open
convex subset `K` of a real vector space with `0 ∉ K` there is a linear
`f : V → ℝ` with `f(x) > 0` for all `x ∈ K`. -/
theorem hahn_banach (K : Set V) (hK : RadiallyOpen V K)
    (hconv : Convex ℝ K) (h0 : (0 : V) ∉ K) :
    ∃ f : V →ₗ[ℝ] ℝ, ∀ x ∈ K, 0 < f x := by
  -- Divergence from vn.tex:4079: the thesis takes `K` maximal by Zorn's Lemma and
  -- shows `V/H` is one-dimensional for `H = {x | -x, x ∉ K}`.  We instead run the
  -- Minkowski-functional proof: `gauge C` for the translate `C = K - x₀` is
  -- sublinear, `C = {gauge C < 1}` because `C` is radially open, and Mathlib's
  -- algebraic Hahn–Banach (`exists_extension_of_le_sublinear`) extends the
  -- functional `c·x₀ ↦ -c` from the line `ℝ x₀`.  No topology on `V` is used —
  -- essential here, since 73III.3/4 show the radial topology is not a TVS.
  rcases Set.eq_empty_or_nonempty K with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have hx₀ne : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  -- translate `K` so that the translate `C` contains `0`
  set C : Set V := (fun v => x₀ + v) ⁻¹' K with hCdef
  have hCmem : ∀ v : V, v ∈ C ↔ x₀ + v ∈ K := fun _ => Iff.rfl
  have hC0 : (0 : V) ∈ C := by rw [hCmem]; simpa using hx₀
  have hCconv : Convex ℝ C := hconv.translate_preimage_right x₀
  have hCrad : RadiallyOpen V C := by
    intro a ha v
    obtain ⟨t, ht, h⟩ := hK (x₀ + a) ha v
    refine ⟨t, ht, fun r hr0 hr => ?_⟩
    rw [hCmem, show x₀ + (a + r • v) = x₀ + a + r • v by abel]
    exact h r hr0 hr
  -- radial openness at `0` in the directions `x` and `-x` makes `C` absorbent
  have habs : Absorbent ℝ C := by
    intro x
    obtain ⟨t₁, ht₁, H₁⟩ := hCrad 0 hC0 x
    obtain ⟨t₂, ht₂, H₂⟩ := hCrad 0 hC0 (-x)
    have htm : 0 < min t₁ t₂ := lt_min ht₁ ht₂
    rw [absorbs_iff_norm]
    refine ⟨2 / min t₁ t₂, fun c hc => ?_⟩
    have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (by positivity) hc
    have hcne : c ≠ 0 := by simpa using norm_pos_iff.mp hcpos
    have habsc : |c⁻¹| < min t₁ t₂ := by
      rw [abs_inv]
      have h1 : 2 / min t₁ t₂ ≤ |c| := by simpa [Real.norm_eq_abs] using hc
      have h2 : 0 < |c| := by simpa [Real.norm_eq_abs] using hcpos
      rw [inv_lt_iff_one_lt_mul₀ h2]
      rw [div_le_iff₀ htm] at h1
      nlinarith
    have hmemC : c⁻¹ • x ∈ C := by
      rcases lt_or_gt_of_ne hcne with hneg | hpos
      · have hinvneg : c⁻¹ < 0 := inv_neg''.mpr hneg
        have h := H₂ (-c⁻¹) (by linarith) (by
          rw [abs_of_neg hinvneg] at habsc
          exact lt_of_lt_of_le habsc (min_le_right _ _))
        rw [zero_add, smul_neg, neg_smul, neg_neg] at h
        exact h
      · have hinvpos : 0 < c⁻¹ := inv_pos.mpr hpos
        have h := H₁ c⁻¹ hinvpos.le (by
          rw [abs_of_pos hinvpos] at habsc
          exact lt_of_lt_of_le habsc (min_le_left _ _))
        rwa [zero_add] at h
    refine Set.singleton_subset_iff.mpr ⟨c⁻¹ • x, hmemC, ?_⟩
    change c • (c⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hcne, one_smul]
  -- radial openness at `v ∈ C` in the direction `v` gives `gauge C v < 1`
  have hgauge_lt : ∀ v ∈ C, gauge C v < 1 := by
    intro v hv
    obtain ⟨t, ht, H⟩ := hCrad v hv v
    set r : ℝ := min (t / 2) 1 with hrdef
    have hr0 : 0 < r := lt_min (by linarith) one_pos
    have hrt : r < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hmem : (1 + r) • v ∈ C := by
      have h := H r hr0.le hrt
      rwa [show v + r • v = (1 + r) • v by module] at h
    have hmem' : v ∈ (1 + r)⁻¹ • C :=
      ⟨(1 + r) • v, hmem, by
        change (1 + r)⁻¹ • (1 + r) • v = v
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt h1r), one_smul]⟩
    calc gauge C v ≤ (1 + r)⁻¹ := gauge_le_of_mem (by positivity) hmem'
      _ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  -- `-x₀ ∉ C` because `0 ∉ K`
  have hgauge_ge : (1 : ℝ) ≤ gauge C (-x₀) := by
    by_contra hlt
    have hmem : -x₀ ∈ C :=
      setOfPred_gauge_lt_one_subset_self hCconv hC0 habs (lt_of_not_ge hlt)
    rw [hCmem] at hmem
    exact h0 (by simpa using hmem)
  -- the functional `c·x₀ ↦ -c` on `ℝ x₀` is dominated by the gauge
  set f₀ : V →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x₀ (-1 : ℝ) hx₀ne with hf₀
  have hdom : ∀ z : f₀.domain, f₀ z ≤ gauge C (z : V) := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ (ℝ ∙ x₀) := hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz'
    have h : f₀ ⟨c • x₀, hz⟩ = c • (-1 : ℝ) :=
      LinearPMap.mkSpanSingleton'_apply x₀ (-1 : ℝ) _ c hz
    rw [h]
    change c • (-1 : ℝ) ≤ gauge C (c • x₀)
    rcases le_or_gt 0 c with hc | hc
    · refine le_trans ?_ (gauge_nonneg _)
      simp only [smul_eq_mul, mul_neg, mul_one, neg_nonpos]
      exact hc
    · rw [show c • x₀ = (-c) • (-x₀) by module,
        gauge_smul_of_nonneg (by linarith : (0 : ℝ) ≤ -c)]
      simp only [smul_eq_mul, mul_neg, mul_one]
      nlinarith [hgauge_ge]
  obtain ⟨g, hg₁, hg₂⟩ := exists_extension_of_le_sublinear f₀ (gauge C)
    (fun c hc x => by rw [gauge_smul_of_nonneg hc.le]; simp)
    (fun x y => gauge_add_le hCconv habs x y) hdom
  have hx₀dom : x₀ ∈ f₀.domain := Submodule.mem_span_singleton_self x₀
  have hgx₀ : g x₀ = -1 := by
    have h := hg₁ ⟨x₀, hx₀dom⟩
    rw [show ((⟨x₀, hx₀dom⟩ : f₀.domain) : V) = x₀ from rfl] at h
    rw [h]
    exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hx₀ne (-1 : ℝ)
  refine ⟨-g, fun x hx => ?_⟩
  have hmemC : x - x₀ ∈ C := by rw [hCmem]; simpa using hx
  have h1 : g (x - x₀) ≤ gauge C (x - x₀) := hg₂ _
  have h2 : gauge C (x - x₀) < 1 := hgauge_lt _ hmemC
  have h3 : g x - g x₀ = g (x - x₀) := by rw [map_sub]
  simp only [LinearMap.neg_apply]
  linarith

end Radial

/-! ### Auxiliaries for **73VIII** -/

omit [PartialOrder A] [StarOrderedRing A] in
private theorem rsmul_eq (r : ℝ) (x : A) : r • x = ((r : ℝ) : ℂ) • x := by
  rw [← IsScalarTower.algebraMap_smul ℂ r x, Complex.coe_algebraMap]

private theorem omegaNorm_rsmul (ω : NPFunctional A) (r : ℝ) (x : A) :
    omegaNorm A ω (r • x) = |r| * omegaNorm A ω x := by
  rw [rsmul_eq, omegaNorm_smul, Complex.norm_real, Real.norm_eq_abs]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem radiallyOpen_add_left {s t : Set A} (hs : RadiallyOpen A s) :
    RadiallyOpen A (s + t) := by
  rintro a ⟨p, hp, q, hq, rfl⟩ v
  obtain ⟨d, hd, h⟩ := hs p hp v
  refine ⟨d, hd, fun r hr0 hr => ?_⟩
  have e : p + q + r • v = p + r • v + q := by abel
  rw [e]
  exact Set.add_mem_add (h r hr0 hr) hq

/-- **73VIII** (`ultraclosed`, vn.tex:4160, Exercise): an ultrastrongly
closed *convex* subset of a von Neumann algebra is ultraweakly closed
(hence the ultrastrong and ultraweak closures of convex sets coincide).
The exercise's enumerated items are steps of the proof and are not
converted separately.

The thesis's five steps, transcribed: (1) `Kᶜ` is ultrastrongly open, so it
contains a `‖·‖_ω`-ball around the point `a₀ ∉ K` to be separated
(`exists_ultrastrong_ball_of_isOpen`); (2) that ball `B` (recentred at `0`)
is convex and radially open, and misses the translate `K' = K - a₀`, so
`0 ∉ B + K'`; (3) **73IV** `hahn_banach` gives an `ℝ`-linear `f` positive on
`B + K'`, extended to a `ℂ`-linear `g` by `g(a) = f(a) - i f(ia)`
(Mathlib's `Module.Dual.extendRCLike`); (4) `|f(b)| < f(k)` for `b ∈ B`,
`k ∈ K'` — because `-b ∈ B` — whence `‖g(b)‖ ≤ 2f(k₀)` on the ball and `g`
is ultraweakly continuous by **72XI** `luws`, clause (4); (5) `B` is
absorbing, so a small multiple `b₀` of a fixed `k₀ ∈ K'` lies in `B` with
`f(b₀) > 0`, and `f ≥ f(b₀) =: δ > 0` on `K'`.  Then
`{a | (g a).re < δ + (g a₀).re}` is an ultraweak neighbourhood of `a₀`
missing `K`. -/
theorem ultraclosed [VonNeumannAlgebra A] (K : Set A) (hconv : Convex ℝ K)
    (hK : @IsClosed A (ultrastrong A) K) : @IsClosed A (ultraweak A) K := by
  rcases Set.eq_empty_or_nonempty K with rfl | ⟨k₀, hk₀⟩
  · exact @isClosed_empty A (ultraweak A)
  letI : TopologicalSpace A := ultraweak A
  refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr ?_)
  intro a₀ ha₀
  -- (1) `K` is ultrastrongly closed, so its complement contains a `‖·‖_ω`-ball at `a₀`
  obtain ⟨ω, ε, hε, hball⟩ :=
    exists_ultrastrong_ball_of_isOpen hK.isOpen_compl a₀ ha₀
  -- (2) the ball `B` at the origin, and the translate `K'` of `K`
  set B : Set A := {b : A | omegaNorm A ω b < ε} with hB
  set K' : Set A := (fun v => a₀ + v) ⁻¹' K with hK'
  have hBmem : ∀ b : A, b ∈ B ↔ omegaNorm A ω b < ε := fun _ => Iff.rfl
  have hK'mem : ∀ v : A, v ∈ K' ↔ a₀ + v ∈ K := fun _ => Iff.rfl
  have hB0 : (0 : A) ∈ B := by rw [hBmem]; simpa using hε
  have hBneg : ∀ b ∈ B, -b ∈ B := by
    intro b hb; rw [hBmem, omegaNorm_neg]; exact hb
  have hBconv : Convex ℝ B := by
    intro x hx y hy s t hs ht hst
    rw [hBmem] at hx hy ⊢
    have h1 : omegaNorm A ω (s • x + t • y) ≤ s * omegaNorm A ω x + t * omegaNorm A ω y := by
      refine le_trans (omegaNorm_add_le ω _ _) ?_
      rw [omegaNorm_rsmul, omegaNorm_rsmul, abs_of_nonneg hs, abs_of_nonneg ht]
    have h2 : s * omegaNorm A ω x + t * omegaNorm A ω y < ε := by
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · rw [← hs0]; simp only [zero_mul, zero_add]
        rw [← hs0, zero_add] at hst
        rw [hst, one_mul]; exact hy
      · rcases eq_or_lt_of_le ht with ht0 | ht0
        · rw [← ht0]; simp only [zero_mul, add_zero]
          rw [← ht0, add_zero] at hst
          rw [hst, one_mul]; exact hx
        · nlinarith [omegaNorm_nonneg ω x, omegaNorm_nonneg ω y]
    linarith
  have hBrad : RadiallyOpen A B := by
    intro b hb v
    rw [hBmem] at hb
    refine ⟨(ε - omegaNorm A ω b) / (omegaNorm A ω v + 1),
      by have := omegaNorm_nonneg ω v; positivity, fun r hr0 hr => ?_⟩
    rw [hBmem]
    have h1 : omegaNorm A ω (b + r • v) ≤ omegaNorm A ω b + r * omegaNorm A ω v := by
      refine le_trans (omegaNorm_add_le ω _ _) ?_
      rw [omegaNorm_rsmul, abs_of_nonneg hr0]
    rw [lt_div_iff₀ (by have := omegaNorm_nonneg ω v; positivity)] at hr
    nlinarith [omegaNorm_nonneg ω v]
  have hK'conv : Convex ℝ K' := hconv.translate_preimage_right a₀
  have hK'ne : k₀ - a₀ ∈ K' := by rw [hK'mem]; simpa using hk₀
  have hdisj : ∀ x ∈ B, x ∉ K' := by
    intro x hx hxK'
    have : a₀ + x ∈ Kᶜ := by
      refine hball ?_
      rw [Set.mem_ofPred_eq]
      simpa using (hBmem x).mp hx
    exact this ((hK'mem x).mp hxK')
  -- (3) Hahn–Banach on `C = B + K'`
  set C : Set A := B + K' with hC
  have hCconv : Convex ℝ C := hBconv.add hK'conv
  have hCrad : RadiallyOpen A C := radiallyOpen_add_left hBrad
  have hC0 : (0 : A) ∉ C := by
    rintro ⟨b, hb, k, hk, hbk⟩
    have hbk' : b + k = 0 := hbk
    have hkb : k = -b := eq_neg_of_add_eq_zero_right hbk'
    exact hdisj (-b) (hBneg b hb) (hkb ▸ hk)
  obtain ⟨f, hf⟩ := hahn_banach C hCrad hCconv hC0
  have hfpos : ∀ b ∈ B, ∀ k ∈ K', 0 < f b + f k := by
    intro b hb k hk
    have := hf (b + k) (Set.add_mem_add hb hk)
    rwa [map_add] at this
  -- (4) `|f(b)| < f(k)` and `‖g(b)‖ ≤ 2 f(k)`
  have habs : ∀ b ∈ B, ∀ k ∈ K', |f b| < f k := by
    intro b hb k hk
    have h1 := hfpos b hb k hk
    have h2 := hfpos (-b) (hBneg b hb) k hk
    rw [map_neg] at h2
    rw [abs_lt]
    constructor <;> linarith
  set g : Module.Dual ℂ A := Module.Dual.extendRCLike (𝕜 := ℂ) f with hg
  have hgapp : ∀ x : A,
      g x = ((f x : ℝ) : ℂ) - Complex.I * ((f (Complex.I • x) : ℝ) : ℂ) := fun x =>
    Module.Dual.extendRCLike_apply (𝕜 := ℂ) f x
  have hgre : ∀ x : A, (g x).re = f x := fun x => by rw [hgapp x]; simp
  have hgnorm : ∀ b ∈ B, ∀ k ∈ K', ‖g b‖ ≤ 2 * f k := by
    intro b hb k hk
    have hIb : Complex.I • b ∈ B := by
      rw [hBmem, omegaNorm_smul]
      simpa using (hBmem b).mp hb
    have e := hgapp b
    have h1 : ‖g b‖ ≤ ‖((f b : ℝ) : ℂ)‖ + ‖Complex.I * ((f (Complex.I • b) : ℝ) : ℂ)‖ := by
      rw [e]; exact norm_sub_le _ _
    have h2 : ‖((f b : ℝ) : ℂ)‖ = |f b| := by simp
    have h3 : ‖Complex.I * ((f (Complex.I • b) : ℝ) : ℂ)‖ = |f (Complex.I • b)| := by simp
    have hb1 := habs b hb k hk
    have hb2 := habs _ hIb k hk
    rw [h2, h3] at h1
    linarith
  -- `g` is ultraweakly continuous by **72XI**
  have hbdd : ∃ (ω' : NPFunctional A) (δ : ℝ), 0 < δ ∧
      BddAbove {r : ℝ | ∃ a : A, omegaNorm A ω' a ≤ δ ∧ r = ‖g a‖} := by
    refine ⟨ω, ε / 2, by positivity, 2 * f (k₀ - a₀), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hgnorm a (by rw [hBmem]; linarith) _ hK'ne
  have hgcont : @Continuous A ℂ (ultraweak A) _ ⇑g := ((luws g).out 3 1).mp hbdd
  -- (5) a strictly positive lower bound `δ` for `f` on `K'`
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k ∈ K', δ ≤ f k := by
    set v : A := k₀ - a₀ with hv
    have hfv : 0 < f v := by
      have := hfpos 0 hB0 v hK'ne
      rwa [map_zero, zero_add] at this
    set r : ℝ := ε / (2 * (omegaNorm A ω v + 1)) with hr
    have hr0 : 0 < r := by
      rw [hr]; have := omegaNorm_nonneg ω v; positivity
    have hrB : r • v ∈ B := by
      rw [hBmem, omegaNorm_rsmul, abs_of_pos hr0, hr]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by have := omegaNorm_nonneg ω v; positivity)]
      nlinarith [omegaNorm_nonneg ω v]
    refine ⟨r * f v, by positivity, fun k hk => ?_⟩
    have h := habs (r • v) hrB k hk
    have he : f (r • v) = r * f v := by rw [map_smul]; simp
    rw [he, abs_of_pos (by positivity)] at h
    linarith
  -- the ultraweakly open separating set
  refine ⟨{a : A | (g a).re < δ + (g a₀).re}, ?_, ?_, by simpa using hδ⟩
  · intro a ha
    simp only [Set.mem_ofPred_eq] at ha
    intro hkK
    have hk' : a - a₀ ∈ K' := by rw [hK'mem]; simpa using hkK
    have := hδle _ hk'
    rw [← hgre] at this
    have e : (g (a - a₀)).re = (g a).re - (g a₀).re := by rw [map_sub]; simp
    rw [e] at this
    linarith
  · have hcont : @Continuous A ℝ (ultraweak A) _ (fun a => (g a).re) :=
      Complex.continuous_re.comp' hgcont
    exact continuous_def.mp hcont _ isOpen_Iio

/-! ## Parsec 740: Kaplansky's density theorem -/

section Kaplansky

variable [VonNeumannAlgebra A]

/-! ### Auxiliaries for **74I** `proto_kaplansky`

The thesis's proof (vn.tex:4232, "an adaptation of Conway Lemma 44.2") works
with the set `S` of continuous `g : ℝ → ℝ` for which `a ↦ g(a)` is
ultrastrongly continuous on `sa(𝒜)`.  `USCont A g` below is that membership,
spelled out as an ε–δ statement in the seminorms `‖·‖_ω` — which is what
`continuousOn_of_usCont` turns into the `ContinuousOn` of the statement.

The plan is the thesis's, in this order: `S` contains the identity and the
constants and is closed under `+`, real scalars, precomposition with an
affine map, multiplication by a *bounded* member, and uniform limits;
`e(t) = t/(1+t²)` lies in `S` by the thesis's identity
`e(b) − e(a) = s(b)(b−a)s(a) − e(b)(b−a)e(a)`, and hence so does
`s(t) = 1/(1+t²) = 1 − t·e(t)`; the translates `s(t−c)` separate the points
of `ℝ ∪ {∞}`, so Stone–Weierstraß puts every continuous `f` vanishing at
infinity in `S`; and `f = f·s + (f·s·t)·t` reduces the general `f = O(t)` to
that case.
-/

variable (A) in
/-- The set `S` of the thesis's proof of **74I**. -/
private def USCont (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ ∀ a : A, IsSelfAdjoint a → ∀ (ω : NPFunctional A) (ε : ℝ), 0 < ε →
    ∃ (ω' : NPFunctional A) (δ : ℝ), 0 < δ ∧
      ∀ b : A, IsSelfAdjoint b → omegaNorm A ω' (b - a) < δ →
        omegaNorm A ω (cfc g b - cfc g a) < ε

omit [VonNeumannAlgebra A] in
private theorem continuousOn_of_usCont {g : ℝ → ℝ} (h : USCont A g) :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => cfc g a)
      {a : A | IsSelfAdjoint a} := by
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha
  intro V hV
  obtain ⟨U, hUV, hUopen, hUmem⟩ := (@mem_nhds_iff A (ultrastrong A) _ _).mp hV
  obtain ⟨ω, ε, hε, hball⟩ := exists_ultrastrong_ball_of_isOpen hUopen _ hUmem
  obtain ⟨ω', δ, hδ, hmain⟩ := h.2 a ha ω ε hε
  refine (@mem_nhdsWithin A (ultrastrong A) _ _ _).mpr
    ⟨{x : A | omegaNorm A ω' (x - a) < δ},
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨ω', a, δ, hδ, rfl⟩, by simpa using hδ, ?_⟩
  rintro b ⟨hb1, hb2⟩
  simp only [Set.mem_ofPred_eq] at hb1 hb2
  exact hUV (hball (hmain b hb2 hb1))

omit [VonNeumannAlgebra A] in
private theorem usCont_const (c : ℝ) : USCont A (fun _ => c) := by
  refine ⟨continuous_const, fun a ha ω ε hε => ⟨zeroNP, 1, one_pos, fun b hb _ => ?_⟩⟩
  rw [cfc_const c b hb, cfc_const c a ha, sub_self, omegaNorm_zero]
  exact hε

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem usCont_id : USCont A (fun t : ℝ => t) := by
  refine ⟨continuous_id, fun a ha ω ε hε => ⟨ω, ε, hε, fun b hb hlt => ?_⟩⟩
  rwa [cfc_id' ℝ b, cfc_id' ℝ a]

omit [VonNeumannAlgebra A] in
private theorem usCont_add {g h : ℝ → ℝ} (hg : USCont A g) (hh : USCont A h) :
    USCont A (fun t => g t + h t) := by
  refine ⟨hg.1.add hh.1, fun a ha ω ε hε => ?_⟩
  obtain ⟨ω₁, δ₁, hδ₁, h₁⟩ := hg.2 a ha ω (ε / 2) (by positivity)
  obtain ⟨ω₂, δ₂, hδ₂, h₂⟩ := hh.2 a ha ω (ε / 2) (by positivity)
  refine ⟨addNP ω₁ ω₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun b hb hlt => ?_⟩
  have hb₁ : omegaNorm A ω₁ (b - a) < δ₁ :=
    lt_of_le_of_lt (omegaNorm_le_addNP ω₁ ω₂ _) (lt_of_lt_of_le hlt (min_le_left _ _))
  have hb₂ : omegaNorm A ω₂ (b - a) < δ₂ :=
    lt_of_le_of_lt (omegaNorm_le_addNP' ω₁ ω₂ _) (lt_of_lt_of_le hlt (min_le_right _ _))
  have he : cfc (fun t => g t + h t) b - cfc (fun t => g t + h t) a
      = (cfc g b - cfc g a) + (cfc h b - cfc h a) := by
    rw [cfc_add b g h hg.1.continuousOn hh.1.continuousOn,
      cfc_add a g h hg.1.continuousOn hh.1.continuousOn]
    abel
  rw [he]
  exact lt_of_le_of_lt (omegaNorm_add_le ω _ _) (by linarith [h₁ b hb hb₁, h₂ b hb hb₂])

omit [VonNeumannAlgebra A] in
private theorem usCont_smul {g : ℝ → ℝ} (hg : USCont A g) (r : ℝ) :
    USCont A (fun t => r * g t) := by
  refine ⟨continuous_const.mul hg.1, fun a ha ω ε hε => ?_⟩
  obtain ⟨ω₁, δ₁, hδ₁, h₁⟩ := hg.2 a ha ω (ε / (|r| + 1)) (by positivity)
  refine ⟨ω₁, δ₁, hδ₁, fun b hb hlt => ?_⟩
  have he : cfc (fun t => r * g t) b - cfc (fun t => r * g t) a
      = r • (cfc g b - cfc g a) := by
    rw [cfc_const_mul r g b hg.1.continuousOn, cfc_const_mul r g a hg.1.continuousOn, smul_sub]
  rw [he, omegaNorm_rsmul]
  
  have h := h₁ b hb hlt
  have hnn : 0 ≤ omegaNorm A ω (cfc g b - cfc g a) := omegaNorm_nonneg _ _
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < |r| + 1)] at h
  nlinarith [abs_nonneg r]

omit [VonNeumannAlgebra A] in
private theorem omegaNorm_le_norm_mul (ω : NPFunctional A) (x : A) :
    omegaNorm A ω x ≤ ‖x‖ * omegaNorm A ω 1 := by
  have := omegaNorm_mul_le ω x 1
  rwa [mul_one] at this

private theorem usCont_mul {g h : ℝ → ℝ} (hg : USCont A g) (hh : USCont A h)
    {C : ℝ} (hC : ∀ t, |g t| ≤ C) : USCont A (fun t => g t * h t) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  refine ⟨hg.1.mul hh.1, fun a ha ω ε hε => ?_⟩
  obtain ⟨ω₁, δ₁, hδ₁, h₁⟩ := hh.2 a ha ω (ε / (2 * (C + 1))) (by positivity)
  obtain ⟨ω₂, δ₂, hδ₂, h₂⟩ := hg.2 a ha (conjNP (cfc h a) ω) (ε / 2) (by positivity)
  refine ⟨addNP ω₁ ω₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun b hb hlt => ?_⟩
  have hb₁ : omegaNorm A ω₁ (b - a) < δ₁ :=
    lt_of_le_of_lt (omegaNorm_le_addNP ω₁ ω₂ _) (lt_of_lt_of_le hlt (min_le_left _ _))
  have hb₂ : omegaNorm A ω₂ (b - a) < δ₂ :=
    lt_of_le_of_lt (omegaNorm_le_addNP' ω₁ ω₂ _) (lt_of_lt_of_le hlt (min_le_right _ _))
  have hgb : ‖cfc g b‖ ≤ C :=
    norm_cfc_le hC0 fun x _ => by rw [Real.norm_eq_abs]; exact hC x
  have he : cfc (fun t => g t * h t) b - cfc (fun t => g t * h t) a
      = cfc g b * (cfc h b - cfc h a) + (cfc g b - cfc g a) * cfc h a := by
    rw [cfc_mul g h b hg.1.continuousOn hh.1.continuousOn,
      cfc_mul g h a hg.1.continuousOn hh.1.continuousOn]
    noncomm_ring
  rw [he]
  refine lt_of_le_of_lt (omegaNorm_add_le ω _ _) ?_
  have e1 : omegaNorm A ω (cfc g b * (cfc h b - cfc h a))
      ≤ C * omegaNorm A ω (cfc h b - cfc h a) := by
    refine (omegaNorm_mul_le ω _ _).trans ?_
    exact mul_le_mul_of_nonneg_right hgb (omegaNorm_nonneg _ _)
  have e2 : omegaNorm A ω ((cfc g b - cfc g a) * cfc h a)
      = omegaNorm A (conjNP (cfc h a) ω) (cfc g b - cfc g a) := omegaNorm_mul_right ω _ _
  have f1 := h₁ b hb hb₁
  have f2 := h₂ b hb hb₂
  rw [e2]
  have hnn : 0 ≤ omegaNorm A ω (cfc h b - cfc h a) := omegaNorm_nonneg _ _
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (C + 1))] at f1
  nlinarith

omit [VonNeumannAlgebra A] in
private theorem usCont_comp_affine {g : ℝ → ℝ} (hg : USCont A g) (r c : ℝ) :
    USCont A (fun t => g (r * t + c)) := by
  have haffcfc : ∀ x : A, IsSelfAdjoint x →
      cfc (fun t => g (r * t + c)) x = cfc g (r • x + algebraMap ℝ A c) := by
    intro x hx
    have haff : cfc (fun t : ℝ => r * t + c) x = r • x + algebraMap ℝ A c := by
      rw [cfc_add x (fun t : ℝ => r * t) (fun _ : ℝ => c) (by fun_prop) (by fun_prop),
        cfc_const_mul r (fun t : ℝ => t) x (by fun_prop), cfc_id' ℝ x, cfc_const c x hx]
    rw [← haff, ← cfc_comp g (fun t : ℝ => r * t + c) x hx hg.1.continuousOn (by fun_prop)]
    rfl
  refine ⟨hg.1.comp (by fun_prop), fun a ha ω ε hε => ?_⟩
  have hc' : IsSelfAdjoint (algebraMap ℝ A c) := IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all c)
  have ha' : IsSelfAdjoint (r • a + algebraMap ℝ A c) :=
    (IsSelfAdjoint.smul (IsSelfAdjoint.all r) ha).add hc'
  obtain ⟨ω', δ, hδ, hmain⟩ := hg.2 _ ha' ω ε hε
  refine ⟨ω', δ / (|r| + 1), by positivity, fun b hb hlt => ?_⟩
  have hb' : IsSelfAdjoint (r • b + algebraMap ℝ A c) :=
    (IsSelfAdjoint.smul (IsSelfAdjoint.all r) hb).add hc'
  have hsub : (r • b + algebraMap ℝ A c) - (r • a + algebraMap ℝ A c) = r • (b - a) := by
    rw [smul_sub]; abel
  have hlt' : omegaNorm A ω' ((r • b + algebraMap ℝ A c) - (r • a + algebraMap ℝ A c)) < δ := by
    rw [hsub, omegaNorm_rsmul]
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < |r| + 1)] at hlt
    nlinarith [omegaNorm_nonneg ω' (b - a), abs_nonneg r]
  have := hmain _ hb' hlt'
  rwa [← haffcfc b hb, ← haffcfc a ha] at this

omit [VonNeumannAlgebra A] in
private theorem usCont_of_approx {g : ℝ → ℝ} (hgc : Continuous g)
    (happ : ∀ η : ℝ, 0 < η → ∃ h : ℝ → ℝ, USCont A h ∧ ∀ t, |g t - h t| ≤ η) :
    USCont A g := by
  refine ⟨hgc, fun a ha ω ε hε => ?_⟩
  set M : ℝ := omegaNorm A ω 1 with hM
  have hM0 : 0 ≤ M := omegaNorm_nonneg _ _
  obtain ⟨h, hh, hgh⟩ := happ (ε / (3 * (M + 1))) (by positivity)
  have hnorm : ∀ x : A, IsSelfAdjoint x → omegaNorm A ω (cfc g x - cfc h x) ≤ ε / 3 := by
    intro x hx
    have hd : cfc g x - cfc h x = cfc (fun t => g t - h t) x :=
      (cfc_sub g h x hgc.continuousOn hh.1.continuousOn).symm
    have hn : ‖cfc g x - cfc h x‖ ≤ ε / (3 * (M + 1)) := by
      rw [hd]
      exact norm_cfc_le (by positivity) fun y _ => by rw [Real.norm_eq_abs]; exact hgh y
    refine (omegaNorm_le_norm_mul ω _).trans ?_
    have hmul := mul_le_mul_of_nonneg_right hn hM0
    refine hmul.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨ω', δ, hδ, hmain⟩ := hh.2 a ha ω (ε / 3) (by positivity)
  refine ⟨ω', δ, hδ, fun b hb hlt => ?_⟩
  have t1 := hnorm b hb
  have t2 := hmain b hb hlt
  have t3 := hnorm a ha
  have step : omegaNorm A ω (cfc g b - cfc g a)
      ≤ omegaNorm A ω (cfc g b - cfc h b) + omegaNorm A ω (cfc h b - cfc g a) :=
    omegaNorm_sub_le ω _ _ _
  have step2 : omegaNorm A ω (cfc h b - cfc g a)
      ≤ omegaNorm A ω (cfc h b - cfc h a) + omegaNorm A ω (cfc h a - cfc g a) :=
    omegaNorm_sub_le ω _ _ _
  have t3' : omegaNorm A ω (cfc h a - cfc g a) ≤ ε / 3 := by
    rw [← omegaNorm_neg, neg_sub]; exact t3
  linarith

/-! ### The generator `e(t) = t/(1+t²)` -/

private noncomputable def sfun : ℝ → ℝ := fun t => 1 / (1 + t ^ 2)
private noncomputable def efun : ℝ → ℝ := fun t => t / (1 + t ^ 2)

private theorem denom_pos (t : ℝ) : (0 : ℝ) < 1 + t ^ 2 := by positivity

private theorem sfun_continuous : Continuous sfun :=
  continuous_const.div (by fun_prop) fun t => (denom_pos t).ne'

private theorem efun_continuous : Continuous efun :=
  continuous_id.div (by fun_prop) fun t => (denom_pos t).ne'

private theorem abs_sfun_le (t : ℝ) : |sfun t| ≤ 1 := by
  rw [sfun, abs_of_pos (by positivity)]
  rw [div_le_one (denom_pos t)]
  nlinarith [sq_nonneg t]

private theorem abs_efun_le (t : ℝ) : |efun t| ≤ 1 := by
  rw [efun, abs_div, abs_of_pos (denom_pos t), div_le_one (denom_pos t)]
  nlinarith [sq_nonneg (|t| - 1), abs_nonneg t, sq_abs t]

private theorem efun_eq_mul (t : ℝ) : efun t = t * sfun t := by
  rw [efun, sfun]; ring

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem cfc_efun_eq {x : A} (hx : IsSelfAdjoint x) :
    cfc efun x = x * cfc sfun x := by
  rw [show efun = fun t : ℝ => t * sfun t from funext efun_eq_mul,
    cfc_mul (fun t : ℝ => t) sfun x (by fun_prop) sfun_continuous.continuousOn, cfc_id' ℝ x]

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem cfc_efun_eq' {x : A} (hx : IsSelfAdjoint x) :
    cfc efun x = cfc sfun x * x := by
  rw [show efun = fun t : ℝ => sfun t * t from funext fun t => by rw [efun_eq_mul]; ring,
    cfc_mul sfun (fun t : ℝ => t) x sfun_continuous.continuousOn (by fun_prop), cfc_id' ℝ x]

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem cfc_one_add_sq {x : A} (hx : IsSelfAdjoint x) :
    cfc (fun t : ℝ => 1 + t ^ 2) x = 1 + x ^ 2 := by
  rw [cfc_add x (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t ^ 2) (by fun_prop) (by fun_prop),
    cfc_const (1 : ℝ) x hx, map_one, cfc_pow_id x 2 hx]

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem cfc_sfun_left {x : A} (hx : IsSelfAdjoint x) :
    (1 + x ^ 2) * cfc sfun x = 1 := by
  have h := cfc_mul (fun t : ℝ => 1 + t ^ 2) sfun x (by fun_prop) sfun_continuous.continuousOn
  rw [cfc_one_add_sq hx] at h
  rw [← h, show (fun t : ℝ => (1 + t ^ 2) * sfun t) = fun _ : ℝ => (1 : ℝ) from
    funext fun t => by rw [sfun]; field_simp, cfc_const (1 : ℝ) x hx, map_one]

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem cfc_sfun_right {x : A} (hx : IsSelfAdjoint x) :
    cfc sfun x * (1 + x ^ 2) = 1 := by
  have h := cfc_mul sfun (fun t : ℝ => 1 + t ^ 2) x sfun_continuous.continuousOn (by fun_prop)
  rw [cfc_one_add_sq hx] at h
  rw [← h, show (fun t : ℝ => sfun t * (1 + t ^ 2)) = fun _ : ℝ => (1 : ℝ) from
    funext fun t => by rw [sfun]; field_simp, cfc_const (1 : ℝ) x hx, map_one]

private theorem usCont_efun : USCont A efun := by
  refine ⟨efun_continuous, fun a ha ω ε hε => ?_⟩
  set Sa : A := cfc sfun a with hSa
  set Ea : A := cfc efun a with hEa
  refine ⟨addNP (conjNP Sa ω) (conjNP Ea ω), ε / 2, by positivity, fun b hb hlt => ?_⟩
  set Sb : A := cfc sfun b with hSb
  set Eb : A := cfc efun b with hEb
  have hnSb : ‖Sb‖ ≤ 1 :=
    norm_cfc_le zero_le_one fun t _ => by rw [Real.norm_eq_abs]; exact abs_sfun_le t
  have hnEb : ‖Eb‖ ≤ 1 :=
    norm_cfc_le zero_le_one fun t _ => by rw [Real.norm_eq_abs]; exact abs_efun_le t
  -- the thesis's identity
  have hEbl : Eb = Sb * b := by rw [hEb, hSb]; exact cfc_efun_eq' hb
  have hEar : Ea = a * Sa := by rw [hEa, hSa]; exact cfc_efun_eq ha
  have ha1 : (1 + a ^ 2) * Sa = 1 := by rw [hSa]; exact cfc_sfun_left ha
  have hb1 : Sb * (1 + b ^ 2) = 1 := by rw [hSb]; exact cfc_sfun_right hb
  have key : Eb - Ea = Sb * ((b - a) * Sa) - Eb * ((b - a) * Ea) := by
    conv_rhs => rw [hEbl, hEar]
    have expand : Sb * ((b - a) * Sa) - Sb * b * ((b - a) * (a * Sa))
        = Sb * b * ((1 + a ^ 2) * Sa) - Sb * (1 + b ^ 2) * (a * Sa) := by
      noncomm_ring
    rw [expand, ha1, hb1, mul_one, one_mul, hEbl, hEar]
  -- and the estimate
  have e1 : omegaNorm A ω (Sb * ((b - a) * Sa)) ≤ omegaNorm A (conjNP Sa ω) (b - a) := by
    refine (omegaNorm_mul_le ω Sb _).trans ?_
    rw [omegaNorm_mul_right ω (b - a) Sa]
    nlinarith [omegaNorm_nonneg (conjNP Sa ω) (b - a), hnSb]
  have e2 : omegaNorm A ω (Eb * ((b - a) * Ea)) ≤ omegaNorm A (conjNP Ea ω) (b - a) := by
    refine (omegaNorm_mul_le ω Eb _).trans ?_
    rw [omegaNorm_mul_right ω (b - a) Ea]
    nlinarith [omegaNorm_nonneg (conjNP Ea ω) (b - a), hnEb]
  have f1 : omegaNorm A (conjNP Sa ω) (b - a) < ε / 2 :=
    lt_of_le_of_lt (omegaNorm_le_addNP _ _ _) hlt
  have f2 : omegaNorm A (conjNP Ea ω) (b - a) < ε / 2 :=
    lt_of_le_of_lt (omegaNorm_le_addNP' _ _ _) hlt
  rw [key, sub_eq_add_neg]
  refine lt_of_le_of_lt (omegaNorm_add_le ω _ _) ?_
  rw [omegaNorm_neg]
  linarith

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem usCont_congr {g h : ℝ → ℝ} (hg : USCont A g) (e : ∀ t, g t = h t) :
    USCont A h := (funext e : g = h) ▸ hg

/-- `s(t) = 1/(1+t²) = 1 − t·e(t)` is in `S`. -/
private theorem usCont_sfun : USCont A sfun := by
  refine usCont_congr (usCont_add (usCont_const (A := A) 1)
    (usCont_smul (usCont_mul usCont_efun usCont_id (C := 1) abs_efun_le) (-1))) fun t => ?_
  rw [sfun, efun]
  field_simp
  ring

/-- The generating family `u_c(t) = 1/(1+(t−c)²)` is in `S`. -/
private theorem usCont_sfun_sub (c : ℝ) : USCont A (fun t : ℝ => sfun (t - c)) := by
  refine usCont_congr (usCont_comp_affine (usCont_sfun (A := A)) 1 (-c)) fun t => ?_
  ring_nf

/-! ### Stone–Weierstraß on `ℝ ∪ {∞}` -/

private theorem tendsto_sfun_sub (c : ℝ) :
    Tendsto (fun t : ℝ => sfun (t - c)) (cocompact ℝ) (𝓝 0) := by
  have hmaj : Tendsto (fun t : ℝ => ‖t‖ + -|c|) (cocompact ℝ) atTop :=
    tendsto_norm_cocompact_atTop.atTop_add (tendsto_const_nhds (x := -|c|))
  have h0 : Tendsto (fun t : ℝ => 1 + (t - c) ^ 2) (cocompact ℝ) atTop := by
    refine tendsto_atTop_mono (fun t => ?_) hmaj
    have h1 : |t| - |c| ≤ |t - c| := abs_sub_abs_le_abs_sub t c
    have h2 : |t - c| ≤ 1 + (t - c) ^ 2 := by
      nlinarith [sq_nonneg (|t - c| - 1), abs_nonneg (t - c), sq_abs (t - c)]
    rw [Real.norm_eq_abs]
    linarith
  simpa [sfun, Pi.inv_def, one_div] using h0.inv_tendsto_atTop

/-- The generator `u_c`, extended to the one-point compactification. -/
private noncomputable def kapGen (c : ℝ) : C(OnePoint ℝ, ℝ) :=
  OnePoint.continuousMapMk ⟨fun t : ℝ => sfun (t - c), sfun_continuous.comp (by fun_prop)⟩ 0
    (by rw [coclosedCompact_eq_cocompact]; exact tendsto_sfun_sub c)

private theorem kapGen_coe (c t : ℝ) : kapGen c (t : OnePoint ℝ) = sfun (t - c) := rfl

private theorem kapGen_infty (c : ℝ) : kapGen c (OnePoint.infty : OnePoint ℝ) = 0 := rfl

private theorem usCont_of_mem_adjoin {F : C(OnePoint ℝ, ℝ)}
    (hF : F ∈ Algebra.adjoin ℝ (Set.range (kapGen))) :
    USCont A (fun t : ℝ => F (t : OnePoint ℝ)) := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact usCont_congr (usCont_sfun_sub (A := A) c) fun t => (kapGen_coe c t).symm
  | algebraMap r => exact usCont_congr (usCont_const (A := A) r) fun t => rfl
  | add x y _ _ ihx ihy => exact usCont_congr (usCont_add ihx ihy) fun t => rfl
  | mul x y _ _ ihx ihy =>
      exact usCont_congr (usCont_mul ihx ihy (C := ‖x‖)
        fun t => by simpa using ContinuousMap.norm_coe_le_norm x (t : OnePoint ℝ)) fun t => rfl

private theorem kapAlg_separatesPoints :
    (Algebra.adjoin ℝ (Set.range (kapGen))).SeparatesPoints := by
  have hmem : ∀ c : ℝ, kapGen c ∈ Algebra.adjoin ℝ (Set.range (kapGen)) := fun c =>
    Algebra.subset_adjoin ⟨c, rfl⟩
  have hne : ∀ u v : ℝ, u ^ 2 ≠ v ^ 2 → sfun u ≠ sfun v := by
    intro u v h he
    apply h
    rw [sfun, sfun] at he
    have hu : (0:ℝ) < 1 + u ^ 2 := by positivity
    have hv : (0:ℝ) < 1 + v ^ 2 := by positivity
    field_simp at he
    linarith
  rintro (_ | x) (_ | y) hxy
  · exact absurd rfl hxy
  · refine ⟨_, ⟨kapGen y, hmem y, rfl⟩, ?_⟩
    change kapGen y (OnePoint.infty : OnePoint ℝ) ≠ kapGen y ((y : ℝ) : OnePoint ℝ)
    rw [kapGen_infty, kapGen_coe, sub_self]
    simp [sfun]
  · refine ⟨_, ⟨kapGen x, hmem x, rfl⟩, ?_⟩
    change kapGen x ((x : ℝ) : OnePoint ℝ) ≠ kapGen x (OnePoint.infty : OnePoint ℝ)
    rw [kapGen_infty, kapGen_coe, sub_self]
    simp [sfun]
  · have hxy' : x ≠ y := by
      intro h; exact hxy (by rw [h])
    refine ⟨_, ⟨kapGen ((x + y) / 2 + 1), hmem _, rfl⟩, ?_⟩
    change kapGen ((x + y) / 2 + 1) ((x : ℝ) : OnePoint ℝ)
      ≠ kapGen ((x + y) / 2 + 1) ((y : ℝ) : OnePoint ℝ)
    rw [kapGen_coe, kapGen_coe]
    refine hne _ _ ?_
    intro h
    apply hxy'
    have : (x - ((x + y) / 2 + 1)) ^ 2 - (y - ((x + y) / 2 + 1)) ^ 2 = 0 := by rw [h]; ring
    have h2 : (x - y) * 2 = 0 := by nlinarith [this]
    linarith

/-- Every continuous `g : ℝ → ℝ` vanishing at infinity is in `S`. -/
private theorem usCont_of_tendsto_zero {g : ℝ → ℝ} (hgc : Continuous g)
    (hg0 : Tendsto g (cocompact ℝ) (𝓝 0)) : USCont A g := by
  set G : C(OnePoint ℝ, ℝ) := OnePoint.continuousMapMk ⟨g, hgc⟩ 0
    (by rw [coclosedCompact_eq_cocompact]; exact hg0) with hG
  have hGcoe : ∀ t : ℝ, G (t : OnePoint ℝ) = g t := fun _ => rfl
  have htop : (Algebra.adjoin ℝ (Set.range (kapGen))).topologicalClosure = ⊤ :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ kapAlg_separatesPoints
  have hGmem : G ∈ closure ((Algebra.adjoin ℝ (Set.range (kapGen))) : Set C(OnePoint ℝ, ℝ)) := by
    have : G ∈ (Algebra.adjoin ℝ (Set.range (kapGen))).topologicalClosure := by
      rw [htop]; trivial
    exact this
  refine usCont_of_approx hgc fun η hη => ?_
  obtain ⟨F, hFmem, hFd⟩ := Metric.mem_closure_iff.mp hGmem η hη
  refine ⟨fun t : ℝ => F (t : OnePoint ℝ), usCont_of_mem_adjoin hFmem, fun t => ?_⟩
  have := ContinuousMap.dist_apply_le_dist (f := G) (g := F) (t : OnePoint ℝ)
  rw [Real.dist_eq, hGcoe] at this
  linarith

/-! ### Reduction of a general `f = O(t)` to a function vanishing at infinity -/

private theorem bounded_of_bigO {g : ℝ → ℝ} (hgc : Continuous g) {n : ℕ} {C : ℝ}
    (h : ∀ t : ℝ, (n : ℝ) ≤ |t| → |g t| ≤ C) : ∃ C' : ℝ, ∀ t, |g t| ≤ C' := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := -(n : ℝ)) (b := (n : ℝ))).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨max C C₀, fun t => ?_⟩
  rcases le_or_gt (n : ℝ) |t| with ht | ht
  · exact le_trans (h t ht) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right C C₀)
    have := hC₀ t ⟨by cases abs_le.mp ht.le with | intro h1 h2 => linarith,
      by cases abs_le.mp ht.le with | intro h1 h2 => linarith⟩
    rwa [Real.norm_eq_abs] at this

private theorem tendsto_mul_sfun {f : ℝ → ℝ} {n : ℕ} {b : ℝ}
    (hb : ∀ t : ℝ, (n : ℝ) ≤ |t| → |f t| ≤ b * |t|) (hb0 : 0 ≤ b) :
    Tendsto (fun t : ℝ => f t * sfun t) (cocompact ℝ) (𝓝 0) := by
  have hnorm : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop :=
    tendsto_norm_cocompact_atTop
  have hmaj : Tendsto (fun t : ℝ => b * (1 / |t|)) (cocompact ℝ) (𝓝 0) := by
    simpa [one_div] using hnorm.inv_tendsto_atTop.const_mul b
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hnorm.eventually_ge_atTop (max (n : ℝ) 1)] with t ht
  have ht1 : (1 : ℝ) ≤ |t| := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < |t| := by linarith
  have htn : (n : ℝ) ≤ |t| := le_trans (le_max_left _ _) ht
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  have hf := hb t htn
  have hval : ‖f t * sfun t‖ = |f t| * (1 / (1 + t ^ 2)) := by
    have h0 : |sfun t| = 1 / (1 + t ^ 2) := by
      simp only [sfun]
      exact abs_of_pos (by positivity)
    rw [Real.norm_eq_abs, abs_mul, h0]
  rw [hval]
  refine (mul_le_mul_of_nonneg_right hf (by positivity)).trans ?_
  have e1 : b * |t| * (1 / (1 + t ^ 2)) = b * |t| / (1 + t ^ 2) := by ring
  have e2 : b * (1 / |t|) = b / |t| := by ring
  rw [e1, e2, div_le_div_iff₀ hden htpos]
  nlinarith [hb0, habs]

/-- **74I** (`proto-kaplansky`, vn.tex:4224, Proposition): for a continuous
`f : ℝ → ℝ` with `f(t) = O(t)`, the map `a ↦ f(a)` (continuous functional
calculus) is ultrastrongly continuous on the self-adjoint part of a von
Neumann algebra.

*Class 1 — faithful*, apart from one simplification.  See the block above
for the plan, which is the thesis's.  The one departure: where the thesis
adjoins all the `e_{a,b}(t) = e(at+b)` and appeals to Stone–Weierstraß for
the algebra they generate, we adjoin only the translates `s(t−c)` of
`s(t) = 1/(1+t²)`.  These already separate the points of `ℝ ∪ {∞}`
(`s(x−c) = s(y−c)` forces `c = (x+y)/2`, and `s(·−c) > 0` on `ℝ` while it
vanishes at `∞`), and being positive they make the "take real parts if
necessary" step of the thesis unnecessary: `C(ℝ ∪ {∞}, ℝ)` is a real
Banach algebra and Mathlib's real Stone–Weierstraß applies directly. -/
theorem proto_kaplansky (f : ℝ → ℝ) (hf : Continuous f)
    (hO : ∃ (n : ℕ) (b : ℝ), ∀ t : ℝ, (n : ℝ) ≤ |t| → |f t| ≤ b * |t|) :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => cfc f a)
      {a : A | IsSelfAdjoint a} := by
  refine continuousOn_of_usCont ?_
  obtain ⟨n, b, hb⟩ := hO
  have habs1 : |((n : ℝ) + 1)| = (n : ℝ) + 1 := abs_of_pos (by positivity)
  have hb0 : 0 ≤ b := by
    have h := hb ((n : ℝ) + 1) (by rw [habs1]; linarith)
    rw [habs1] at h
    nlinarith [abs_nonneg (f ((n : ℝ) + 1))]
  have habsS : ∀ t : ℝ, |sfun t| = 1 / (1 + t ^ 2) := fun t => by
    simp only [sfun]; exact abs_of_pos (by positivity)
  have hg1c : Continuous (fun t => f t * sfun t) := hf.mul sfun_continuous
  have hg1 : USCont A (fun t => f t * sfun t) :=
    usCont_of_tendsto_zero hg1c (tendsto_mul_sfun hb hb0)
  obtain ⟨C₁, hC₁⟩ : ∃ C' : ℝ, ∀ t, |f t * sfun t| ≤ C' := by
    refine bounded_of_bigO hg1c (n := n) (C := b) fun t ht => ?_
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [abs_mul, habsS t]
    refine (mul_le_mul_of_nonneg_right (hb t ht) (by positivity)).trans ?_
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1)]
  have hg2 : USCont A (fun t => f t * sfun t * t) := usCont_mul hg1 usCont_id hC₁
  obtain ⟨C₂, hC₂⟩ : ∃ C' : ℝ, ∀ t, |f t * sfun t * t| ≤ C' := by
    refine bounded_of_bigO (hg1c.mul continuous_id) (n := n) (C := b) fun t ht => ?_
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [abs_mul, abs_mul, habsS t]
    have h1 : |f t| * (1 / (1 + t ^ 2)) * |t| ≤ b * |t| * (1 / (1 + t ^ 2)) * |t| := by
      have hnn : (0 : ℝ) ≤ 1 / (1 + t ^ 2) * |t| := by positivity
      nlinarith [hb t ht]
    refine h1.trans ?_
    rw [mul_comm (b * |t|) (1 / (1 + t ^ 2)), mul_assoc, ← mul_assoc, one_div,
      inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [sq_abs t]
  refine usCont_congr (usCont_add hg1 (usCont_mul hg2 usCont_id hC₂)) fun t => ?_
  simp only [sfun]
  field_simp

/-- **74III** (`abs-us-cont`, vn.tex:4331, Corollary): `a ↦ |a|` is
ultrastrongly continuous on the self-adjoint part of a von Neumann
algebra.

*Class 1 — faithful*: `|t| = O(t)` on the nose (`b = 1`, `n = 0`), so this
is one application of **74I**. -/
theorem abs_us_cont :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A)
      (fun a => cfc (fun t : ℝ => |t|) a) {a : A | IsSelfAdjoint a} :=
  proto_kaplansky (fun t : ℝ => |t|) continuous_abs ⟨0, 1, fun t _ => by rw [one_mul, abs_abs]⟩

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem): if `b`
in a von Neumann algebra `B` is the ultrastrong limit of a net from a
C*-subalgebra `S`, then `b` is the ultrastrong limit of a net `(a_α)_α` in
`S` with `‖a_α‖ ≤ ‖b‖`. -/
theorem kaplansky (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖) ∧ USTendsto a l b :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 1: if moreover `b` is self-adjoint, the `a_α` can be chosen
self-adjoint. -/
theorem kaplansky_sa (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) (hsa : IsSelfAdjoint b) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ IsSelfAdjoint (a i)) ∧
        USTendsto a l b :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 2: if moreover `b` is positive, the `a_α` can be chosen positive. -/
theorem kaplansky_pos (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) (hpos : 0 ≤ b) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ 0 ≤ a i) ∧ USTendsto a l b :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 3: if moreover `b` is an effect, the `a_α` can be chosen to be
effects (retaining `‖a_α‖ ≤ ‖b‖` from the main claim, which the "moreover"
clauses only add to — note this is strictly stronger than `‖a_α‖ ≤ 1`, which
is all that being an effect gives). -/
theorem kaplansky_effects (S : StarSubalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (b : A)
    (hb : b ∈ @closure A (ultrastrong A) S) (heff : b ∈ effects A) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ a i ∈ effects A) ∧ USTendsto a l b :=
  sorry

/-- **74VI** (`dense-subalgebra`, vn.tex:4421, Corollary): given `ε > 0`
and an ultraweakly dense ∗-subalgebra `S` of a von Neumann algebra, every
element `a` is the ultrastrong limit of a net `(s_α)_α` from `S` with
`‖s_α‖ ≤ ‖a‖(1 + ε)`. -/
theorem dense_subalgebra (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (ε : ℝ) (hε : 0 < ε) (a : A) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ s : ι → A,
      (∀ i, s i ∈ S ∧ ‖s i‖ ≤ ‖a‖ * (1 + ε)) ∧ USTendsto s l a :=
  sorry

/-! ## Parsec 750: closedness of subalgebras

**75I** (vn.tex:4460): introduction — nothing to formalize. -/

/-- **75II** (`sequence-separation-lemma`, vn.tex:4469, Lemma): let `S` be
a von Neumann subalgebra of `A`, and let `ω₀`, `ω₁` be npu-functionals on
`A` separated by a net `(b_α)_α` of effects of `S` (i.e.
`ω₀(b_α) → 0` and `ω₁(b_α^⊥) → 0`).  Then `ω₀` and `ω₁` are separated by a
projection `q ∈ S`: `ω₀(q) = 0 = ω₁(q^⊥)`. -/
theorem sequence_separation_lemma (S : StarSubalgebra ℂ A)
    (hS : IsVNSubalgebra A S) (ω₀ ω₁ : NPFunctional A) (hω₀ : ω₀ 1 = 1)
    (hω₁ : ω₁ 1 = 1) {ι : Type*} {l : Filter ι} [l.NeBot] (b : ι → A)
    (hb : ∀ i, b i ∈ S ∧ b i ∈ effects A)
    (h₀ : Tendsto (fun i => ω₀ (b i)) l (𝓝 0))
    (h₁ : Tendsto (fun i => ω₁ (1 - b i)) l (𝓝 0)) :
    ∃ q : A, q ∈ S ∧ IsStarProjection q ∧ ω₀ q = 0 ∧ ω₁ (1 - q) = 0 :=
  sorry

/-- **75VI** (`kadisons-lemma`, vn.tex:4560, Lemma): let `S` be a von
Neumann subalgebra of `A` and `p` a projection of `A` in the ultrastrong
closure of `S`.  For all npu-functionals `ω₀`, `ω₁` with
`ω₀(p) = 0 = ω₁(p^⊥)` there is a projection `q ∈ S` with
`ω₀(q) = 0 = ω₁(q^⊥)`. -/
theorem kadisons_lemma (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S)
    (p : A) (hp : IsStarProjection p)
    (hcl : p ∈ @closure A (ultrastrong A) S) (ω₀ ω₁ : NPFunctional A)
    (hω₀ : ω₀ 1 = 1) (hω₁ : ω₁ 1 = 1) (h₀ : ω₀ p = 0)
    (h₁ : ω₁ (1 - p) = 0) :
    ∃ q : A, q ∈ S ∧ IsStarProjection q ∧ ω₀ q = 0 ∧ ω₁ (1 - q) = 0 :=
  sorry

/-- **75VIII** (`vnsac`, vn.tex:4587, Theorem): a von Neumann subalgebra of
a von Neumann algebra is ultrastrongly and ultraweakly closed. -/
theorem vnsac (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    @IsClosed A (ultrastrong A) (S : Set A) ∧
      @IsClosed A (ultraweak A) (S : Set A) :=
  sorry

end Kaplansky

/-! ## Parsec 760: completeness of B(H) -/

section BH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The vector functional `⟪x, (·) x⟫` on `B(H)` as an np-functional
(**38II**, cstar.tex 6402), obtained from **38IV**.2 at the one-term sequence
`(x, 0, 0, …)`. -/
private theorem exists_npFunctional_vector (x : H) :
    ∃ ω : NPFunctional (H →L[ℂ] H), ∀ T : H →L[ℂ] H, ω T = ⟪x, T x⟫ := by
  classical
  obtain ⟨ω, hω⟩ := bh_functional_lemma_2 (fun n : ℕ => if n = 0 then x else 0)
    (summable_of_ne_finset_zero (s := {0}) (fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [hn]))
  refine ⟨ω, fun T => ?_⟩
  rw [hω, tsum_eq_single 0 (fun b hb => by simp [hb])]
  simp

/-- `‖S‖_ω = ‖S x‖` for the vector functional `ω = ⟪x, (·) x⟫`. -/
private theorem omegaNorm_vector {ω : NPFunctional (H →L[ℂ] H)} {x : H}
    (hω : ∀ T : H →L[ℂ] H, ω T = ⟪x, T x⟫) (S : H →L[ℂ] H) :
    omegaNorm (H →L[ℂ] H) ω S = ‖S x‖ := by
  rw [omegaNorm, hω, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, Real.sqrt_sq (norm_nonneg _)]

/-- If `ω = ∑ₙ ⟪xₙ, (·) xₙ⟫` on `B(H)` then `‖S‖_ω² = ∑ₙ ‖S xₙ‖²`.  This is
the identity that makes the whole of parsec 760 work, and it is exactly what
**39IX** (`bh_np`) supplies for an arbitrary np-functional. -/
private theorem hasSum_normSq_of_np {x : ℕ → H} {ω : NPFunctional (H →L[ℂ] H)}
    (hω : ∀ S : H →L[ℂ] H, HasSum (fun n => ⟪x n, S (x n)⟫) (ω S))
    (S : H →L[ℂ] H) :
    HasSum (fun n => ‖S (x n)‖ ^ 2) (omegaNorm (H →L[ℂ] H) ω S ^ 2) := by
  have hterm : ∀ n, (⟪x n, (star S * S) (x n)⟫ : ℂ)
      = ((‖S (x n)‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h := hω (star S * S)
  simp only [hterm] at h
  have hnn : (0 : ℝ) ≤ (ω (star S * S)).re :=
    (Complex.le_def.mp
      (ω.toPositiveLinearMap.map_nonneg (star_mul_self_nonneg S))).1
  have hsq : omegaNorm (H →L[ℂ] H) ω S ^ 2 = (ω (star S * S)).re := by
    rw [omegaNorm, Real.sq_sqrt hnn]
  rw [hsq]
  simpa only [Complex.ofReal_re] using ((Complex.hasSum_iff _ _).mp h).1

/-- **76I** (`bh-us-complete`, vn.tex:4641, Proposition): `B(H)` is
ultrastrongly complete: every ultrastrongly Cauchy net converges
ultrastrongly. -/
theorem bh_us_complete {ι : Type*} (l : Filter ι) [l.NeBot]
    (T : ι → H →L[ℂ] H)
    (hcauchy : ∀ ω : NPFunctional (H →L[ℂ] H),
      Tendsto (fun p : ι × ι => omegaNorm _ ω (T p.1 - T p.2)) (l ×ˢ l)
        (𝓝 0)) :
    ∃ T₀ : H →L[ℂ] H, USTendsto T l T₀ := by
  classical
  -- (1) `(T_α x)_α` is norm Cauchy for every `x`, because
  -- `‖(T_α − T_β)x‖ = ‖T_α − T_β‖_{⟪x,(·)x⟫}`; let `F x` be its limit.
  have hptc : ∀ x : H, ∃ y : H, Tendsto (fun i => T i x) l (𝓝 y) := by
    intro x
    obtain ⟨ω, hω⟩ := exists_npFunctional_vector x
    refine cauchy_map_iff_exists_tendsto.mp (cauchy_map_of_tendsto_dist ?_)
    refine (hcauchy ω).congr fun p => ?_
    rw [omegaNorm_vector hω, ContinuousLinearMap.sub_apply, dist_eq_norm]
  choose F hF using hptc
  -- (2) `F` is linear.
  have hFadd : ∀ a b : H, F (a + b) = F a + F b := by
    intro a b
    refine tendsto_nhds_unique (hF (a + b)) ?_
    simpa only [map_add] using (hF a).add (hF b)
  have hFsmul : ∀ (c : ℂ) (a : H), F (c • a) = c • F a := by
    intro c a
    refine tendsto_nhds_unique (hF (c • a)) ?_
    simpa only [ContinuousLinearMap.map_smul] using (hF a).const_smul c
  -- (3) `F` is bounded — the thesis's argument by contradiction.
  have hFbdd : ∃ C : ℝ, ∀ x : H, ‖F x‖ ≤ C * ‖x‖ := by
    by_contra hcon
    push_neg at hcon
    -- pick `zₙ` with `‖zₙ‖ ≤ 2⁻ⁿ` and `‖F zₙ‖ ≥ 1`
    have hsel : ∀ n : ℕ, ∃ z : H, ‖z‖ ≤ (2 : ℝ)⁻¹ ^ n ∧ 1 ≤ ‖F z‖ := by
      intro n
      obtain ⟨y, hy⟩ := hcon ((2 : ℝ) ^ n)
      have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ n * ‖y‖ := by positivity
      have hFy : 0 < ‖F y‖ := lt_of_le_of_lt hy0 hy
      refine ⟨(((‖F y‖ : ℝ) : ℂ))⁻¹ • y, ?_, ?_⟩
      · rw [norm_smul]
        simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        rw [inv_mul_le_iff₀ hFy]
        have h2 : ((2 : ℝ)⁻¹) ^ n * (2 : ℝ) ^ n = 1 := by
          rw [← mul_pow]; norm_num
        have h3 := mul_lt_mul_of_pos_left hy
          (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n)
        rw [← mul_assoc, h2, one_mul] at h3
        nlinarith [h3]
      · rw [hFsmul, norm_smul]
        simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        rw [inv_mul_cancel₀ (ne_of_gt hFy)]
    choose z hz1 hz2 using hsel
    have hzsum : Summable fun n => ‖z n‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (summable_geometric_of_lt_one (by norm_num)
          (by norm_num : ((4 : ℝ)⁻¹) < 1))
      have h1 : ‖z n‖ ^ 2 ≤ (((2 : ℝ)⁻¹) ^ n) ^ 2 := by
        have := hz1 n
        nlinarith [norm_nonneg (z n), pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n]
      refine h1.trans_eq ?_
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    obtain ⟨ω, hωdef⟩ := bh_functional_lemma_2 z hzsum
    have hω : ∀ S : H →L[ℂ] H, HasSum (fun n => ⟪z n, S (z n)⟫) (ω S) := by
      intro S; rw [hωdef]; exact (bh_functional_lemma_1 z hzsum S).hasSum
    -- `‖T_α‖_ω` is a Cauchy net of reals, hence converges to some `R`
    have hrc : Cauchy (l.map fun i => omegaNorm (H →L[ℂ] H) ω (T i)) := by
      refine cauchy_map_of_tendsto_dist
        (squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) (hcauchy ω))
      rw [Real.dist_eq]
      exact abs_omegaNorm_sub_omegaNorm_le ω _ _
    obtain ⟨R, hR⟩ := cauchy_map_iff_exists_tendsto.mp hrc
    -- every finite partial sum of `∑ₙ ‖F zₙ‖² ≥ ∑ₙ 1` is bounded by `R²`
    have hkey : ∀ N : ℕ, (N : ℝ) ≤ R ^ 2 := by
      intro N
      have h1 : ∀ i, ∑ n ∈ Finset.range N, ‖T i (z n)‖ ^ 2
          ≤ omegaNorm (H →L[ℂ] H) ω (T i) ^ 2 :=
        fun i => sum_le_hasSum _ (fun n _ => by positivity)
          (hasSum_normSq_of_np hω (T i))
      have h2 : Tendsto (fun i => ∑ n ∈ Finset.range N, ‖T i (z n)‖ ^ 2) l
          (𝓝 (∑ n ∈ Finset.range N, ‖F (z n)‖ ^ 2)) :=
        tendsto_finset_sum _ fun n _ => ((hF (z n)).norm).pow 2
      have h4 : (∑ n ∈ Finset.range N, ‖F (z n)‖ ^ 2) ≤ R ^ 2 :=
        le_of_tendsto_of_tendsto' h2 (hR.pow 2) h1
      refine le_trans ?_ h4
      calc (N : ℝ) = ∑ _n ∈ Finset.range N, (1 : ℝ) := by simp
        _ ≤ ∑ n ∈ Finset.range N, ‖F (z n)‖ ^ 2 :=
            Finset.sum_le_sum fun n _ => by nlinarith [hz2 n]
    obtain ⟨N, hN⟩ := exists_nat_gt (R ^ 2)
    exact absurd (hkey N) (not_le.mpr hN)
  obtain ⟨C, hC⟩ := hFbdd
  refine ⟨LinearMap.mkContinuous
    { toFun := F, map_add' := hFadd, map_smul' := hFsmul } C hC, ?_⟩
  set T₀ : H →L[ℂ] H := LinearMap.mkContinuous
    { toFun := F, map_add' := hFadd, map_smul' := hFsmul } C hC with hT₀def
  have hT₀ : ∀ x : H, T₀ x = F x := fun _ => rfl
  -- (4) `(T_α)_α` converges ultrastrongly to `T₀`.  Every np-functional on
  -- `B(H)` is `∑ₙ ⟪xₙ,(·)xₙ⟫` by **39IX**; for a finite set `G` of indices
  -- the partial sum `∑_{n∈G} ‖(T_α − T₀)xₙ‖²` is the limit over `β` of
  -- `∑_{n∈G} ‖(T_α − T_β)xₙ‖² ≤ ‖T_α − T_β‖_ω²`, hence `≤ (ε/2)²`.
  rw [usTendsto_iff]
  intro ω
  obtain ⟨x, hx, -⟩ := bh_np ω
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.mp
    ((hcauchy ω).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2)))
  filter_upwards [hpa] with i hi
  have hle : omegaNorm (H →L[ℂ] H) ω (T i - T₀) ^ 2 ≤ (ε / 2) ^ 2 := by
    refine hasSum_le_of_sum_le (hasSum_normSq_of_np hx (T i - T₀)) fun G => ?_
    have h2 : Tendsto (fun j => ∑ n ∈ G, ‖(T i - T j) (x n)‖ ^ 2) l
        (𝓝 (∑ n ∈ G, ‖(T i - T₀) (x n)‖ ^ 2)) := by
      refine tendsto_finset_sum _ fun n _ => ?_
      have h := (((tendsto_const_nhds : Tendsto (fun _ : ι => T i (x n)) l _).sub
        (hF (x n))).norm).pow 2
      simpa only [ContinuousLinearMap.sub_apply, hT₀] using h
    refine le_of_tendsto h2 ?_
    filter_upwards [hpb] with j hj
    have hb := hab hi hj
    have hnn := omegaNorm_nonneg ω (T i - T j)
    calc ∑ n ∈ G, ‖(T i - T j) (x n)‖ ^ 2
        ≤ omegaNorm (H →L[ℂ] H) ω (T i - T j) ^ 2 :=
          sum_le_hasSum _ (fun n _ => by positivity)
            (hasSum_normSq_of_np hx (T i - T j))
      _ ≤ (ε / 2) ^ 2 := by nlinarith
  have hnn := omegaNorm_nonneg ω (T i - T₀)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  nlinarith

/-- **76III** (`bh-bounded-uw-complete`, vn.tex:4744, Proposition): `B(H)`
is bounded ultraweakly complete: every norm-bounded ultraweakly Cauchy net
converges ultraweakly. -/
theorem bh_bounded_uw_complete {ι : Type*} (l : Filter ι) [l.NeBot]
    (T : ι → H →L[ℂ] H) (hbdd : ∃ C : ℝ, ∀ i, ‖T i‖ ≤ C)
    (hcauchy : ∀ ω : NPFunctional (H →L[ℂ] H),
      Cauchy (l.map fun i => ω (T i))) :
    ∃ T₀ : H →L[ℂ] H, UWTendsto T l T₀ := by
  classical
  haveI : Nonempty ι := nonempty_of_neBot l
  obtain ⟨C, hCb⟩ := hbdd
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hCb (Classical.arbitrary ι))
  -- (1) `⟪T_α u, u⟫` converges, because `⟪u, (·) u⟫` is an np-functional
  have hdiag : ∀ u : H, ∃ c : ℂ, Tendsto (fun i => (⟪(T i) u, u⟫ : ℂ)) l (𝓝 c) := by
    intro u
    obtain ⟨ω, hω⟩ := exists_npFunctional_vector u
    obtain ⟨c, hc⟩ := cauchy_map_iff_exists_tendsto.mp (hcauchy ω)
    simp only [hω] at hc
    exact ⟨star c, by
      simpa only [← starRingEnd_apply, inner_conj_symm] using hc.star⟩
  -- and hence, by polarisation, so does `⟪T_α y, x⟫` for all `x, y`
  have hform : ∀ y x : H, ∃ c : ℂ,
      Tendsto (fun i => (⟪(T i) y, x⟫ : ℂ)) l (𝓝 c) := by
    intro y x
    obtain ⟨c₁, h₁⟩ := hdiag (y + x)
    obtain ⟨c₂, h₂⟩ := hdiag (y - x)
    obtain ⟨c₃, h₃⟩ := hdiag (y + Complex.I • x)
    obtain ⟨c₄, h₄⟩ := hdiag (y - Complex.I • x)
    refine ⟨(c₁ - c₂ - Complex.I * c₃ + Complex.I * c₄) / 4, ?_⟩
    have hpol : ∀ i, (⟪(T i) y, x⟫ : ℂ) =
        ((⟪(T i) (y + x), y + x⟫ : ℂ) - ⟪(T i) (y - x), y - x⟫ -
          Complex.I * ⟪(T i) (y + Complex.I • x), y + Complex.I • x⟫ +
          Complex.I * ⟪(T i) (y - Complex.I • x), y - Complex.I • x⟫) / 4 := by
      intro i
      simpa only [ContinuousLinearMap.coe_coe] using
        inner_map_polarization' ((T i : H →L[ℂ] H) : H →ₗ[ℂ] H) y x
    simp only [hpol]
    exact (((h₁.sub h₂).sub (tendsto_const_nhds.mul h₃)).add
      (tendsto_const_nhds.mul h₄)).div_const 4
  choose G hG using hform
  -- (2) `G y` is a bounded linear functional; Riesz turns it into `T₀ y`
  have hGadd : ∀ y a b : H, G y (a + b) = G y a + G y b := fun y a b =>
    tendsto_nhds_unique (hG y (a + b))
      (by simpa only [inner_add_right] using (hG y a).add (hG y b))
  have hGsmul : ∀ (y : H) (c : ℂ) (a : H), G y (c • a) = c • G y a := fun y c a =>
    tendsto_nhds_unique (hG y (c • a))
      (by simpa only [inner_smul_right, smul_eq_mul] using (hG y a).const_mul c)
  have hGbound : ∀ y x : H, ‖G y x‖ ≤ C * ‖y‖ * ‖x‖ := by
    intro y x
    refine le_of_tendsto (hG y x).norm (Eventually.of_forall fun i => ?_)
    calc ‖(⟪(T i) y, x⟫ : ℂ)‖ ≤ ‖(T i) y‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖y‖ * ‖x‖ := by
          gcongr
          exact ((T i).le_opNorm y).trans (by gcongr; exact hCb i)
  set S : H → H := fun y => (InnerProductSpace.toDual ℂ H).symm
    (LinearMap.mkContinuous
      { toFun := G y, map_add' := hGadd y, map_smul' := hGsmul y }
      (C * ‖y‖) (hGbound y)) with hSdef
  have hSinner : ∀ y x : H, (⟪S y, x⟫ : ℂ) = G y x := fun y x =>
    InnerProductSpace.toDual_symm_apply
  have hSadd : ∀ a b : H, S (a + b) = S a + S b := by
    intro a b
    refine ext_inner_right ℂ fun v => ?_
    rw [hSinner, inner_add_left, hSinner, hSinner]
    exact tendsto_nhds_unique (hG (a + b) v)
      (by simpa only [map_add, inner_add_left] using (hG a v).add (hG b v))
  have hSsmul : ∀ (c : ℂ) (a : H), S (c • a) = c • S a := by
    intro c a
    refine ext_inner_right ℂ fun v => ?_
    rw [hSinner, inner_smul_left, hSinner]
    exact tendsto_nhds_unique (hG (c • a) v)
      (by simpa only [map_smul, inner_smul_left, smul_eq_mul] using
        (hG a v).const_mul ((starRingEnd ℂ) c))
  have hSbound : ∀ y : H, ‖S y‖ ≤ C * ‖y‖ := by
    intro y
    rw [hSdef]
    refine le_of_eq_of_le ((InnerProductSpace.toDual ℂ H).symm.norm_map _) ?_
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  set T₀ : H →L[ℂ] H := LinearMap.mkContinuous
    { toFun := S, map_add' := hSadd, map_smul' := hSsmul } C hSbound with hT₀def
  have hT₀ : ∀ y x : H, (⟪T₀ y, x⟫ : ℂ) = G y x := hSinner
  refine ⟨T₀, ?_⟩
  -- (3) `ω(T_α) → ω(T₀)` for every np-functional `ω`, by the ε-tail split
  rw [uwTendsto_iff]
  intro ω
  obtain ⟨x, hx, hx1⟩ := bh_np ω
  have hxs : Summable fun n => ‖x n‖ ^ 2 := by
    have h : HasSum (fun n => ‖x n‖ ^ 2) (ω 1).re := by
      simpa only [Complex.ofReal_re] using ((Complex.hasSum_iff _ _).mp hx1).1
    exact h.summable
  have hpt : ∀ n, Tendsto (fun i => (⟪x n, (T i) (x n)⟫ : ℂ)) l
      (𝓝 (⟪x n, T₀ (x n)⟫ : ℂ)) := by
    intro n
    have h := (hG (x n) (x n)).star
    rw [← hT₀ (x n) (x n)] at h
    simpa only [← starRingEnd_apply, inner_conj_symm] using h
  set M : ℝ := C + ‖T₀‖ with hMdef
  have hM0 : (0 : ℝ) ≤ M := by positivity
  set d : ι → ℕ → ℂ :=
    fun i n => (⟪x n, (T i) (x n)⟫ : ℂ) - ⟪x n, T₀ (x n)⟫ with hddef
  have hd : ∀ (i : ι) (n : ℕ), ‖d i n‖ ≤ M * ‖x n‖ ^ 2 := by
    intro i n
    have h1 : d i n = ⟪x n, (T i - T₀) (x n)⟫ := by
      rw [hddef, ContinuousLinearMap.sub_apply, inner_sub_right]
    have h2 : ‖T i - T₀‖ ≤ M :=
      (norm_sub_le _ _).trans (by rw [hMdef]; gcongr; exact hCb i)
    rw [h1]
    calc ‖(⟪x n, (T i - T₀) (x n)⟫ : ℂ)‖ ≤ ‖x n‖ * ‖(T i - T₀) (x n)‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖x n‖ * (M * ‖x n‖) := by
          gcongr; exact ((T i - T₀).le_opNorm _).trans (by gcongr)
      _ = M * ‖x n‖ ^ 2 := by ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : 0 < ε / (2 * (M + 1)) := by positivity
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ,
      ∑' n : ↥((s : Set ℕ)ᶜ), ‖x (n : ℕ)‖ ^ 2 < ε / (2 * (M + 1)) :=
    ((tendsto_tsum_compl_atTop_zero (fun n => ‖x n‖ ^ 2)).eventually
      (gt_mem_nhds hpos)).exists
  have hhead : Tendsto (fun i => ∑ n ∈ s, d i n) l (𝓝 0) := by
    have h : Tendsto (fun i => ∑ n ∈ s, d i n) l
        (𝓝 (∑ n ∈ s, ((⟪x n, T₀ (x n)⟫ : ℂ) - ⟪x n, T₀ (x n)⟫))) :=
      tendsto_finsetSum s fun n _ => (hpt n).sub tendsto_const_nhds
    simpa using h
  filter_upwards [Metric.tendsto_nhds.mp hhead (ε / 2) (by linarith)] with i hi
  have hsum : HasSum (d i) (ω (T i) - ω T₀) := (hx (T i)).sub (hx T₀)
  have hnormsble : Summable fun n => ‖d i n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hd i n)
      (hxs.mul_left M)
  have htail : ‖∑' n : ↥((s : Set ℕ)ᶜ), d i (n : ℕ)‖ ≤ ε / 2 := by
    refine (norm_tsum_le_tsum_norm (hnormsble.subtype _)).trans ?_
    refine (Summable.tsum_le_tsum (f := fun n : ↥((s : Set ℕ)ᶜ) => ‖d i (n : ℕ)‖)
      (g := fun n : ↥((s : Set ℕ)ᶜ) => M * ‖x (n : ℕ)‖ ^ 2)
      (fun n => hd i (n : ℕ)) (hnormsble.subtype _)
      ((hxs.subtype _).mul_left M)).trans ?_
    rw [tsum_mul_left]
    have h3 : (0 : ℝ) ≤ ∑' n : ↥((s : Set ℕ)ᶜ), ‖x (n : ℕ)‖ ^ 2 :=
      tsum_nonneg fun n => by positivity
    have h4 : M * (ε / (2 * (M + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hsplit := hsum.summable.sum_add_tsum_compl (s := s)
  rw [hsum.tsum_eq] at hsplit
  rw [dist_zero_right] at hi
  rw [dist_eq_norm, ← hsplit]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  linarith

end BH

/-! ## Parsec 770: completeness of a von Neumann algebra -/

section Complete

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **77I** (`vn-complete`, vn.tex:4808, Theorem), part 1: a von Neumann
algebra is ultrastrongly complete. -/
theorem vn_complete_1 {ι : Type*} (l : Filter ι) [l.NeBot] (x : ι → A)
    (hcauchy : ∀ ω : NPFunctional A,
      Tendsto (fun p : ι × ι => omegaNorm A ω (x p.1 - x p.2)) (l ×ˢ l)
        (𝓝 0)) :
    ∃ a : A, USTendsto x l a :=
  sorry

/-- **77I** (`vn-complete`, vn.tex:4808, Theorem), part 2: a von Neumann
algebra is bounded ultraweakly complete. -/
theorem vn_complete_2 {ι : Type*} (l : Filter ι) [l.NeBot] (x : ι → A)
    (hbdd : ∃ C : ℝ, ∀ i, ‖x i‖ ≤ C)
    (hcauchy : ∀ ω : NPFunctional A, Cauchy (l.map fun i => ω (x i))) :
    ∃ a : A, UWTendsto x l a :=
  sorry

/-- **77III** (`vn-ball-compact`, vn.tex:4847, Theorem): the unit ball of a
von Neumann algebra is ultraweakly compact. -/
theorem vn_ball_compact :
    @IsCompact A (ultraweak A) (Metric.closedBall (0 : A) 1) :=
  sorry

/-- **77V** (`vn-extension`, vn.tex:4879, Proposition): an ultraweakly
continuous bounded linear map `f` on an ultraweakly dense ∗-subalgebra `S`
of a von Neumann algebra `A` extends uniquely to an ultraweakly continuous
(linear) map `g : A → B`. -/
theorem vn_extension (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (f : S →ₗ[ℂ] B)
    (hf : @Continuous S B (TopologicalSpace.induced Subtype.val (ultraweak A))
      (ultraweak B) ⇑f)
    (C : ℝ) (hC : ∀ s : S, ‖f s‖ ≤ C * ‖(s : A)‖) :
    ∃! g : A →ₗ[ℂ] B,
      @Continuous A B (ultraweak A) (ultraweak B) ⇑g ∧ ∀ s : S, g s = f s :=
  sorry

/-- **77V** (`vn-extension`, vn.tex:4879, Proposition), norm part: the
extension `g` is bounded with `‖g‖ = ‖f‖` — rendered: `g` satisfies every
bound `C` that `f` does. -/
theorem vn_extension_norm (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (f : S →ₗ[ℂ] B)
    (hf : @Continuous S B (TopologicalSpace.induced Subtype.val (ultraweak A))
      (ultraweak B) ⇑f)
    (C : ℝ) (hC : ∀ s : S, ‖f s‖ ≤ C * ‖(s : A)‖) (g : A →ₗ[ℂ] B)
    (hg : @Continuous A B (ultraweak A) (ultraweak B) ⇑g)
    (hext : ∀ s : S, g s = f s) (a : A) :
    ‖g a‖ ≤ C * ‖a‖ :=
  sorry

end Complete

end Theses.A.VN
