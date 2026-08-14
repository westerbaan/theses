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

/-! ### Auxiliaries for **74IV** `kaplansky`

The thesis's proof (vn.tex:4344) of the self-adjoint case runs: the real
parts `Re(a_α)` of an approximating net converge *ultraweakly* to
`Re(b) = b`, so `b` lies in the ultraweak closure of the convex set
`sa(S)`; by **73VIII** `ultraclosed` the ultraweak and ultrastrong closures
of a convex set coincide, so `b` is already the ultrastrong limit of a net
from `sa(S)`; and clamping with the continuous function
`-‖b‖ ∨ (·) ∧ ‖b‖`, which is ultrastrongly continuous by **74I**, brings the
norms down to `‖b‖` without disturbing the limit.  The positive case clamps
with `0 ∨ (·) ∧ ‖b‖` instead, and the effect case is the positive case
together with `‖b‖ ≤ 1`.

The general (non-self-adjoint) case needs the `2×2`-matrix trick and hence
**49IV**.1 `mn_vna_1` and **49IV**.2' `mn_vna_2'` (`Basic.lean`); both are
now proved, and the trick is carried out in the `MatrixTrick` block below,
after the self-adjoint case it consumes. -/

omit [VonNeumannAlgebra A] in
/-- Membership of the ultrastrong closure, in terms of the seminorms. -/
private theorem mem_usClosure_iff (K : Set A) (x : A) :
    x ∈ @closure A (ultrastrong A) K ↔
      ∀ (ω : NPFunctional A) (ε : ℝ), 0 < ε → ∃ z ∈ K, omegaNorm A ω (z - x) < ε := by
  let _ : TopologicalSpace A := ultrastrong A
  constructor
  · intro hx ω ε hε
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.mp hx _ (ultrastrong_ball_mem_nhds ω x hε)
    exact ⟨z, hz2, hz1⟩
  · intro h
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨ω, δ, hδ, hsub⟩ := exists_ultrastrong_ball_of_isOpen ho x hxo
    obtain ⟨z, hz, hlt⟩ := h ω δ hδ
    exact ⟨z, hsub hlt, hz⟩

omit [VonNeumannAlgebra A] in
/-- The ultrastrong closure of a convex set is convex — the `‖·‖_ω` are
seminorms, so the ultrastrong topology is that of a locally convex space. -/
private theorem convex_usClosure {K : Set A} (hK : Convex ℝ K) :
    Convex ℝ (@closure A (ultrastrong A) K) := by
  intro x hx y hy s t hs ht hst
  rw [mem_usClosure_iff] at hx hy ⊢
  intro ω ε hε
  obtain ⟨z, hzK, hz⟩ := hx ω (ε / 2) (by positivity)
  obtain ⟨w, hwK, hw⟩ := hy ω (ε / 2) (by positivity)
  refine ⟨s • z + t • w, hK hzK hwK hs ht hst, ?_⟩
  have hEq : s • z + t • w - (s • x + t • y) = s • (z - x) + t • (w - y) := by
    simp only [smul_sub]; abel
  rw [hEq]
  refine lt_of_le_of_lt (omegaNorm_add_le ω _ _) ?_
  rw [omegaNorm_rsmul, omegaNorm_rsmul, abs_of_nonneg hs, abs_of_nonneg ht]
  have h1 : s * omegaNorm A ω (z - x) ≤ s * (ε / 2) :=
    mul_le_mul_of_nonneg_left hz.le hs
  have h2 : t * omegaNorm A ω (w - y) ≤ t * (ε / 2) :=
    mul_le_mul_of_nonneg_left hw.le ht
  have h3 : s * (ε / 2) + t * (ε / 2) = ε / 2 := by
    rw [← add_mul, hst, one_mul]
  linarith

/-- Comparison of closures under a comparison of topologies. -/
private theorem closure_subset_closure_of_continuous_id {X : Type*}
    (t₁ t₂ : TopologicalSpace X) (h : @Continuous X X t₁ t₂ id) (K : Set X) :
    @closure X t₁ K ⊆ @closure X t₂ K :=
  @closure_minimal X t₁ K (@closure X t₂ K) (@subset_closure X t₂ K)
    (@IsClosed.preimage X X t₁ t₂ id h _ (@isClosed_closure X t₂ K))

omit [VonNeumannAlgebra A] in
/-- The ultrastrong topology is finer than the ultraweak one (**43I**
`uwweaker`), so ultrastrong closures are contained in ultraweak ones. -/
private theorem usClosure_subset_uwClosure (K : Set A) :
    @closure A (ultrastrong A) K ⊆ @closure A (ultraweak A) K :=
  closure_subset_closure_of_continuous_id _ _
    (continuous_le_dom ultrastrong_le_ultraweak (@continuous_id A (ultraweak A))) K

omit [VonNeumannAlgebra A] in
/-- Taking real parts is ultraweakly continuous: `ω(Re a) = Re(ω a)`. -/
private theorem continuous_ultraweak_realPart :
    @Continuous A A (ultraweak A) (ultraweak A)
      (fun x : A => ((2 : ℝ)⁻¹ : ℝ) • (x + star x)) := by
  let _ : TopologicalSpace A := ultraweak A
  rw [ultraweak, continuous_iInf_rng]
  intro ω
  rw [continuous_induced_rng]
  have hform : ∀ x : A, ω (((2 : ℝ)⁻¹ : ℝ) • (x + star x))
      = ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) * (ω x + star (ω x)) := by
    intro x
    rw [rsmul_eq]
    have h2 : ω (((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • (x + star x))
        = ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) * ω (x + star x) :=
      map_smul ω.toPositiveLinearMap ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) (x + star x)
    rw [h2, npFunctional_add, npFunctional_star]
  change Continuous fun x : A => (ω (((2 : ℝ)⁻¹ : ℝ) • (x + star x)) : ℂ)
  simp only [hform]
  exact continuous_const.mul ((continuous_ultraweak_npFunctional ω).add
    (continuous_star.comp (continuous_ultraweak_npFunctional ω)))

omit [VonNeumannAlgebra A] in
/-- The ultraweak half of `mem_usClosure_selfAdjointPart`, isolated so the
ultraweak topology can be installed as the ambient instance. -/
private theorem realPart_mem_of_mem_uwClosure {C S : Set A}
    (hCuw : @IsClosed A (ultraweak A) C)
    (hSsub : ∀ x ∈ S, ((2 : ℝ)⁻¹ : ℝ) • (x + star x) ∈ C)
    {b : A} (hb : b ∈ @closure A (ultraweak A) S) :
    ((2 : ℝ)⁻¹ : ℝ) • (b + star b) ∈ C :=
  @closure_minimal A (ultraweak A) S _ hSsub
    (@IsClosed.preimage A A (ultraweak A) (ultraweak A) _
      continuous_ultraweak_realPart C hCuw) b hb

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- A point of the ultrastrong closure of `K` is the limit of the tautological
net indexed by `K` itself. -/
private theorem exists_net_of_mem_usClosure (K : Set A) (b : A)
    (hb : b ∈ @closure A (ultrastrong A) K) :
    ∃ l : Filter K, l.NeBot ∧ USTendsto (fun i : K => (i : A)) l b := by
  let _ : TopologicalSpace A := ultrastrong A
  exact ⟨Filter.comap (fun i : K => (i : A)) (𝓝 b),
    mem_closure_iff_comap_neBot.mp hb, tendsto_comap⟩

/-- The self-adjoint part of a C\*-subalgebra `S` has the same ultrastrong
closure as `S` at every self-adjoint point — the thesis's first step in
**74IV**, and the only place the ultraweak topology enters. -/
private theorem mem_usClosure_selfAdjointPart (S : StarSubalgebra ℂ A)
    (b : A) (hb : b ∈ @closure A (ultrastrong A) (S : Set A))
    (hsa : IsSelfAdjoint b) :
    b ∈ @closure A (ultrastrong A) {x : A | x ∈ S ∧ IsSelfAdjoint x} := by
  set K : Set A := {x : A | x ∈ S ∧ IsSelfAdjoint x} with hKdef
  have hKconv : Convex ℝ K := by
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ s t hs ht _
    refine ⟨add_mem ?_ ?_, ?_⟩
    · rw [rsmul_eq]; exact SMulMemClass.smul_mem _ hx1
    · rw [rsmul_eq]; exact SMulMemClass.smul_mem _ hy1
    · rw [rsmul_eq, rsmul_eq]
      exact ((IsSelfAdjoint.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]) hx2).add
        (IsSelfAdjoint.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]) hy2))
  set C : Set A := @closure A (ultrastrong A) K with hCdef
  have hCuw : @IsClosed A (ultraweak A) C :=
    ultraclosed C (convex_usClosure hKconv) (@isClosed_closure A (ultrastrong A) K)
  have hSsub : ∀ x ∈ (S : Set A), ((2 : ℝ)⁻¹ : ℝ) • (x + star x) ∈ C := by
    intro s hs
    refine @subset_closure A (ultrastrong A) K _ ⟨?_, ?_⟩
    · rw [rsmul_eq]
      exact SMulMemClass.smul_mem _ (add_mem hs (star_mem hs))
    · rw [rsmul_eq]
      refine IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) ?_
      rw [IsSelfAdjoint, star_add, star_star, add_comm]
  have hmem := realPart_mem_of_mem_uwClosure hCuw hSsub (usClosure_subset_uwClosure _ hb)
  have hReb : ((2 : ℝ)⁻¹ : ℝ) • (b + star b) = b := by
    rw [hsa.star_eq, ← two_smul ℝ b, smul_smul]
    norm_num
  rwa [hReb] at hmem

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
/-- Transport of an ultrastrong limit through an ultrastrongly continuous
functional calculus (**74I**). -/
private theorem usTendsto_cfc {f : ℝ → ℝ}
    (hcont : @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => cfc f a)
      {a : A | IsSelfAdjoint a})
    {ι : Type*} {l : Filter ι} {a : ι → A} {b : A}
    (ha : ∀ i, IsSelfAdjoint (a i)) (hb : IsSelfAdjoint b)
    (h : USTendsto a l b) :
    USTendsto (fun i => cfc f (a i)) l (cfc f b) := by
  let _ : TopologicalSpace A := ultrastrong A
  exact Filter.Tendsto.comp (hcont b hb)
    (tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall ha⟩)

omit [VonNeumannAlgebra A] in
private theorem abs_clamp_le_abs {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    |max (-M) (min t M)| ≤ |t| := by
  refine abs_le.mpr ⟨le_trans ?_ (le_max_right (-M) (min t M)),
    max_le (by linarith [abs_nonneg t]) ((min_le_left _ _).trans (le_abs_self t))⟩
  exact le_min (neg_abs_le t) (by linarith [abs_nonneg t])

omit [VonNeumannAlgebra A] in
private theorem abs_clamp_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    |max (-M) (min t M)| ≤ M :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

omit [VonNeumannAlgebra A] in
private theorem abs_posClamp_le_abs {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    |max 0 (min t M)| ≤ |t| := by
  rcases le_total t 0 with h | h
  · rw [min_eq_left (h.trans hM), max_eq_left h, abs_zero]
    exact abs_nonneg t
  · rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (abs_nonneg t) ((min_le_left _ _).trans (le_abs_self t))

omit [VonNeumannAlgebra A] in
private theorem abs_posClamp_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    |max 0 (min t M)| ≤ M :=
  abs_le.mpr ⟨by linarith [le_max_left (0 : ℝ) (min t M)],
    max_le hM (min_le_right _ _)⟩

/-! #### The `2×2`-matrix trick for the general case of **74IV**

`M₂(S)` is a ∗-subalgebra of the von Neumann algebra `M₂(𝒜)` (**49IV**.1
`mn_vna_1`), closed because the entry maps are `1`-Lipschitz; `B = [[0,b],
[b*,0]]` is self-adjoint with `‖B‖ ≤ ‖b‖`; and `B` lies in the *ultraweak*
closure of `M₂(S)` — the adjoint is ultraweakly, though not ultrastrongly,
continuous — hence by **73VIII** in its ultrastrong closure.  The
self-adjoint case then applies, and **49IV**.2' `mn_vna_2'` reads off the
upper-right entries. -/

section MatrixTrick

variable {N : ℕ}

/-- `M_N(S)`, the ∗-subalgebra of `M_N(𝒜)` of matrices with entries in a
∗-subalgebra `S` of `𝒜`. -/
private def matStarSubalgebra (S : StarSubalgebra ℂ A) (N : ℕ) :
    StarSubalgebra ℂ (CStarMatrix (Fin N) (Fin N) A) where
  carrier := {M | ∀ i j, M i j ∈ S}
  mul_mem' := by
    intro M M' hM hM' i j
    rw [CStarMatrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hM i k) (hM' k j)
  add_mem' := by
    intro M M' hM hM' i j
    rw [CStarMatrix.add_apply]
    exact add_mem (hM i j) (hM' i j)
  zero_mem' := by intro i j; exact zero_mem S
  algebraMap_mem' := by
    intro r i j
    rw [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply, CStarMatrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h]
      exact SMulMemClass.smul_mem r (one_mem S)
    · rw [if_neg h, smul_zero]
      exact zero_mem S
  star_mem' := by
    intro M hM i j
    rw [CStarMatrix.star_apply]
    exact star_mem (hM j i)

omit [VonNeumannAlgebra A] in
private theorem mem_matStarSubalgebra {S : StarSubalgebra ℂ A} {N : ℕ}
    {M : CStarMatrix (Fin N) (Fin N) A} :
    M ∈ matStarSubalgebra S N ↔ ∀ i j, M i j ∈ S := Iff.rfl

omit [VonNeumannAlgebra A] in
private theorem isClosed_matStarSubalgebra {S : StarSubalgebra ℂ A} (hS : IsClosed (S : Set A))
    (N : ℕ) :
    IsClosed (matStarSubalgebra S N : Set (CStarMatrix (Fin N) (Fin N) A)) := by
  have hset : (matStarSubalgebra S N : Set (CStarMatrix (Fin N) (Fin N) A))
      = ⋂ p : Fin N × Fin N, (fun M : CStarMatrix (Fin N) (Fin N) A => M p.1 p.2) ⁻¹' S := by
    ext M
    simp [mem_matStarSubalgebra, Set.mem_iInter, Prod.forall]
  rw [hset]
  refine isClosed_iInter fun p => IsClosed.preimage ?_ hS
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun M M' => ?_).continuous
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← CStarMatrix.sub_apply]
  exact CStarMatrix.norm_entry_le_norm

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem matEmb_mul_of_ne {i j k l : Fin N} (h : j ≠ k) (x y : A) :
    matEmb i j x * matEmb k l y = 0 := by
  ext p q
  rw [CStarMatrix.mul_apply]
  simp only [matEmb_apply]
  rw [Finset.sum_eq_zero]
  · rfl
  · intro r _
    rcases eq_or_ne r j with rfl | hr
    · simp [h]
    · simp [hr]

omit [VonNeumannAlgebra A] in
private theorem convex_starSubalgebra (T : StarSubalgebra ℂ (CStarMatrix (Fin N) (Fin N) A)) :
    Convex ℝ (T : Set (CStarMatrix (Fin N) (Fin N) A)) := by
  intro x hx y hy s t hs ht _
  have hr : ∀ (r : ℝ) (z : CStarMatrix (Fin N) (Fin N) A), r • z = ((r : ℝ) : ℂ) • z :=
    fun r z => by rw [← IsScalarTower.algebraMap_smul ℂ r z, Complex.coe_algebraMap]
  rw [hr, hr]
  exact add_mem (SMulMemClass.smul_mem _ hx) (SMulMemClass.smul_mem _ hy)

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem uwTendsto_add' {ι : Type*} {l : Filter ι} {f g : ι → A} {a b : A}
    (hf : UWTendsto f l a) (hg : UWTendsto g l b) :
    UWTendsto (fun i => f i + g i) l (a + b) := by
  rw [uwTendsto_iff] at hf hg ⊢
  intro ω
  have he : ∀ i, (ω (f i + g i) : ℂ) = ω (f i) + ω (g i) := fun i =>
    map_add ω.toPositiveLinearMap _ _
  have he₀ : (ω (a + b) : ℂ) = ω a + ω b := map_add ω.toPositiveLinearMap _ _
  simp only [he, he₀]
  exact (hf ω).add (hg ω)

omit [VonNeumannAlgebra A] in
private theorem uwTendsto_star' {ι : Type*} {l : Filter ι} {f : ι → A} {a : A}
    (h : UWTendsto f l a) : UWTendsto (fun i => star (f i)) l (star a) := by
  rw [uwTendsto_iff] at h ⊢
  intro ω
  simp only [npFunctional_star]
  exact (Complex.continuous_conj.tendsto _).comp (h ω)

/-- `[[0,b],[b*,0]] ∈ M₂(𝒜)`, the matrix of the 74IV trick. -/
private def antiDiag (b : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  matEmb 0 1 b + matEmb 1 0 (star b)

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem antiDiag_apply_01 (b : A) : antiDiag b 0 1 = b := by
  simp [antiDiag, matEmb_apply]

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem isSelfAdjoint_antiDiag (b : A) : IsSelfAdjoint (antiDiag b) := by
  change star (antiDiag b) = antiDiag b
  rw [antiDiag, star_add, matEmb_star, matEmb_star, star_star]
  abel

omit [VonNeumannAlgebra A] in
private theorem norm_antiDiag_le (b : A) : ‖antiDiag b‖ ≤ ‖b‖ := by
  have hrs : ∀ (r : ℝ) (x : A), r • x = ((r : ℝ) : ℂ) • x := fun r x => by
    rw [← IsScalarTower.algebraMap_smul ℂ r x, Complex.coe_algebraMap]
  have hrsM : ∀ (r : ℝ) (x : CStarMatrix (Fin 2) (Fin 2) A),
      r • x = ((r : ℝ) : ℂ) • x := fun r x => by
    rw [← IsScalarTower.algebraMap_smul ℂ r x, Complex.coe_algebraMap]
  have hsq : star (antiDiag b) * antiDiag b
      = matEmb 0 0 (b * star b) + matEmb 1 1 (star b * b) := by
    rw [(isSelfAdjoint_antiDiag b).star_eq, antiDiag, add_mul, mul_add, mul_add,
      matEmb_mul_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      matEmb_mul 0 1 0 b (star b),
      matEmb_mul 1 0 1 (star b) b,
      matEmb_mul_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    abel
  have hb2 : (0 : ℝ) ≤ ‖b‖ ^ 2 := by positivity
  have hbound : ∀ x : A, x ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • (1 : A) →
      ∀ w : A, star w * x * w ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • (star w * w) := by
    intro x hx w
    have h := star_left_conjugate_le_conjugate hx w
    rwa [mul_smul_comm, smul_mul_assoc, mul_one] at h
  have h1 : b * star b ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • (1 : A) := by
    have h := le_norm_smul_one (mul_star_self_nonneg b)
    rw [CStarRing.norm_self_mul_star, hrs] at h
    refine h.trans (le_of_eq ?_)
    norm_num [sq]
  have h2 : star b * b ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • (1 : A) := by
    have h := le_norm_smul_one (star_mul_self_nonneg b)
    rw [CStarRing.norm_star_mul_self, hrs] at h
    refine h.trans (le_of_eq ?_)
    norm_num [sq]
  have hle : star (antiDiag b) * antiDiag b
      ≤ algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) A) (‖b‖ ^ 2) := by
    rw [hsq, Algebra.algebraMap_eq_smul_one, hrsM]
    refine le_iff_matForm.mpr fun z => ?_
    rw [matForm_add_matrix, matForm_matEmb, matForm_matEmb, matForm_smul_matrix]
    have hone : matForm z z (1 : CStarMatrix (Fin 2) (Fin 2) A)
        = star (z 0) * z 0 + star (z 1) * z 1 := by
      simp [matForm, Fin.sum_univ_two, CStarMatrix.one_apply]
    rw [hone, smul_add]
    exact add_le_add (hbound _ h1 (z 0)) (hbound _ h2 (z 1))
  have hnorm : ‖antiDiag b‖ * ‖antiDiag b‖ ≤ ‖b‖ * ‖b‖ := by
    rw [← CStarRing.norm_star_mul_self]
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap
      (star (antiDiag b) * antiDiag b) hb2 (star_mul_self_nonneg _)).mpr hle
    calc ‖star (antiDiag b) * antiDiag b‖ ≤ ‖b‖ ^ 2 := h
      _ = ‖b‖ * ‖b‖ := by ring
  nlinarith [norm_nonneg (antiDiag b), norm_nonneg b]

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem mem_uwClosure_of_uwTendsto {K : Set A} {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → A} {a : A} (hf : UWTendsto f l a) (hmem : ∀ i, f i ∈ K) :
    a ∈ @closure A (ultraweak A) K := by
  let _ : TopologicalSpace A := ultraweak A
  exact mem_closure_of_tendsto hf (Filter.Eventually.of_forall hmem)

/-- **73VIII** in the direction needed by the `2×2` trick: for a convex set the
ultraweak closure is contained in the ultrastrong one. -/
private theorem mem_usClosure_of_mem_uwClosure {K : Set A} (hK : Convex ℝ K) {a : A}
    (h : a ∈ @closure A (ultraweak A) K) : a ∈ @closure A (ultrastrong A) K :=
  @closure_minimal A (ultraweak A) K _ (@subset_closure A (ultrastrong A) K)
    (ultraclosed _ (convex_usClosure hK) (@isClosed_closure A (ultrastrong A) K)) a h

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem convex_starSubalgebraA (T : StarSubalgebra ℂ A) :
    Convex ℝ (T : Set A) := by
  intro x hx y hy s t hs ht _
  rw [rsmul_eq, rsmul_eq]
  exact add_mem (SMulMemClass.smul_mem _ hx) (SMulMemClass.smul_mem _ hy)

end MatrixTrick

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 1: if moreover `b` is self-adjoint, the `a_α` can be chosen
self-adjoint.

*Class 1 — faithful*, see the block above. -/
theorem kaplansky_sa (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) (hsa : IsSelfAdjoint b) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ IsSelfAdjoint (a i)) ∧
        USTendsto a l b := by
  have hM0 : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  set f : ℝ → ℝ := fun t => max (-‖b‖) (min t ‖b‖) with hfdef
  have hfc : Continuous f := by
    simp only [hfdef]; fun_prop
  have hcfc := proto_kaplansky (A := A) f hfc
    ⟨0, 1, fun t _ => by rw [one_mul]; exact abs_clamp_le_abs hM0 t⟩
  obtain ⟨l, hl, hlim⟩ :=
    exists_net_of_mem_usClosure _ b (mem_usClosure_selfAdjointPart S b hb hsa)
  have hcfcb : cfc f b = b := by
    nth_rewrite 2 [← cfc_id ℝ b]
    refine cfc_congr fun t ht => ?_
    have h := abs_le.mp (spectrum_abs_le hsa ht)
    simp only [hfdef, id]
    rw [min_eq_left h.2, max_eq_right h.1]
  have hSc : IsClosed ((S : StarSubalgebra ℂ A) : Set A) := hS
  refine ⟨_, l, hl, fun i => cfc f (i : A), fun i => ⟨cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) f i.2.1,
    norm_cfc_le hM0 fun t _ => by rw [Real.norm_eq_abs]; exact abs_clamp_le hM0 t,
    cfc_predicate f _⟩, ?_⟩
  have := usTendsto_cfc hcfc (fun i : {x : A | x ∈ S ∧ IsSelfAdjoint x} => i.2.2) hsa hlim
  rwa [hcfcb] at this

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 2: if moreover `b` is positive, the `a_α` can be chosen positive.

*Class 3 — mild divergence*: the thesis first clamps to `[-‖b‖,‖b‖]` and then
takes positive parts; we clamp once, with `0 ∨ (·) ∧ ‖b‖`, which is the
composite of the two. -/
theorem kaplansky_pos (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) (hpos : 0 ≤ b) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ 0 ≤ a i) ∧ USTendsto a l b := by
  have hsa : IsSelfAdjoint b := hpos.isSelfAdjoint
  have hM0 : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  set f : ℝ → ℝ := fun t => max 0 (min t ‖b‖) with hfdef
  have hfc : Continuous f := by
    simp only [hfdef]; fun_prop
  have hcfc := proto_kaplansky (A := A) f hfc
    ⟨0, 1, fun t _ => by rw [one_mul]; exact abs_posClamp_le_abs hM0 t⟩
  obtain ⟨l, hl, hlim⟩ :=
    exists_net_of_mem_usClosure _ b (mem_usClosure_selfAdjointPart S b hb hsa)
  have hcfcb : cfc f b = b := by
    nth_rewrite 2 [← cfc_id ℝ b]
    refine cfc_congr fun t ht => ?_
    have h2 := (abs_le.mp (spectrum_abs_le hsa ht)).2
    have h1 : 0 ≤ t := spectrum_nonneg_of_nonneg hpos ht
    simp only [hfdef, id]
    rw [min_eq_left h2, max_eq_right h1]
  have hSc : IsClosed ((S : StarSubalgebra ℂ A) : Set A) := hS
  refine ⟨_, l, hl, fun i => cfc f (i : A), fun i => ⟨cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) f i.2.1,
    norm_cfc_le hM0 fun t _ => by rw [Real.norm_eq_abs]; exact abs_posClamp_le hM0 t,
    cfc_nonneg fun t _ => le_max_left _ _⟩, ?_⟩
  have := usTendsto_cfc hcfc (fun i : {x : A | x ∈ S ∧ IsSelfAdjoint x} => i.2.2) hsa hlim
  rwa [hcfcb] at this

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 3: if moreover `b` is an effect, the `a_α` can be chosen to be
effects (retaining `‖a_α‖ ≤ ‖b‖` from the main claim, which the "moreover"
clauses only add to — note this is strictly stronger than `‖a_α‖ ≤ 1`, which
is all that being an effect gives).

*Class 1 — faithful*: the thesis's observation that the positive case
already delivers effects, since `‖a_α‖ ≤ ‖b‖ ≤ 1`. -/
theorem kaplansky_effects (S : StarSubalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (b : A)
    (hb : b ∈ @closure A (ultrastrong A) S) (heff : b ∈ effects A) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ a i ∈ effects A) ∧ USTendsto a l b := by
  obtain ⟨ι, l, hl, a, ha, hlim⟩ := kaplansky_pos S hS b hb heff.1
  refine ⟨ι, l, hl, a, fun i => ⟨(ha i).1, (ha i).2.1, (ha i).2.2, ?_⟩, hlim⟩
  refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ (ha i).2.2).mp ?_
  exact (ha i).2.1.trans (norm_le_one_of_mem_effects heff)

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem): if `b`
in a von Neumann algebra `B` is the ultrastrong limit of a net from a
C*-subalgebra `S`, then `b` is the ultrastrong limit of a net `(a_α)_α` in
`S` with `‖a_α‖ ≤ ‖b‖`.

*Class 1 — faithful*, with one repair: the thesis says `B` is the
ultrastrong limit of `[[0,aα],[aα*,0]]`, which is false as stated — the
adjoint is not ultrastrongly continuous (**43II**.4), so `aα* → b*` need not
hold ultrastrongly.  Passing to the *ultraweak* limit, where the adjoint is
continuous, and then back by **73VIII** `ultraclosed` (which the thesis has
already used for the self-adjoint case) repairs it.  Stated after the three
"moreover" clauses because its proof runs part 1 in `M₂(𝒜)`. -/
theorem kaplansky (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖) ∧ USTendsto a l b := by
  classical
  set T : StarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) A) := matStarSubalgebra S 2 with hT
  -- `B = [[0,b],[b*,0]]` lies in the ultraweak, hence (73VIII) ultrastrong,
  -- closure of `M₂(S)`
  have hBmem : antiDiag b ∈
      @closure _ (ultrastrong _) (T : Set (CStarMatrix (Fin 2) (Fin 2) A)) := by
    obtain ⟨l, hl, hlim⟩ := exists_net_of_mem_usClosure (S : Set A) b hb
    have h1 : UWTendsto (fun i : (S : Set A) => (i : A)) l b := uwweaker_2 _ _ _ hlim
    have huw : UWTendsto (fun i : (S : Set A) => antiDiag (i : A)) l (antiDiag b) :=
      uwTendsto_add' (uwTendsto_matEmb 0 1 h1) (uwTendsto_matEmb 1 0 (uwTendsto_star' h1))
    have hmem : ∀ i : (S : Set A), antiDiag (i : A) ∈ T := by
      intro i p q
      fin_cases p <;> fin_cases q <;>
        simp only [antiDiag, CStarMatrix.add_apply, matEmb_apply] <;> norm_num <;>
        first
          | exact zero_mem S
          | exact i.2
          | exact star_mem i.2
    have _ : l.NeBot := hl
    exact mem_usClosure_of_mem_uwClosure (convex_starSubalgebra T)
      (mem_uwClosure_of_uwTendsto huw hmem)
  obtain ⟨ι, l, hl, Am, hAm, hlimA⟩ :=
    kaplansky_sa T (isClosed_matStarSubalgebra hS 2) (antiDiag b) hBmem
      (isSelfAdjoint_antiDiag b)
  refine ⟨ι, l, hl, fun i => (Am i) 0 1, fun i => ⟨(hAm i).1 0 1, ?_⟩, ?_⟩
  · calc ‖(Am i) 0 1‖ ≤ ‖Am i‖ := CStarMatrix.norm_entry_le_norm
      _ ≤ ‖antiDiag b‖ := (hAm i).2.1
      _ ≤ ‖b‖ := norm_antiDiag_le b
  · have h := (mn_vna_2' 2 l Am (antiDiag b)).2.mp hlimA 0 1
    simp only [CStarMatrix.ofMatrix_symm_apply, antiDiag_apply_01] at h
    exact h

/-- **74VI** (`dense-subalgebra`, vn.tex:4421, Corollary): given `ε > 0`
and an ultraweakly dense ∗-subalgebra `S` of a von Neumann algebra, every
element `a` is the ultrastrong limit of a net `(s_α)_α` from `S` with
`‖s_α‖ ≤ ‖a‖(1 + ε)`. -/
theorem dense_subalgebra (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (ε : ℝ) (hε : 0 < ε) (a : A) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ s : ι → A,
      (∀ i, s i ∈ S ∧ ‖s i‖ ≤ ‖a‖ * (1 + ε)) ∧ USTendsto s l a := by
  classical
  set K : Set A := {s : A | s ∈ S ∧ ‖s‖ ≤ ‖a‖ * (1 + ε)} with hK
  -- it suffices that `a` lies in the ultrastrong closure of `K`
  suffices h : a ∈ @closure A (ultrastrong A) K by
    obtain ⟨l, hl, hlim⟩ := exists_net_of_mem_usClosure K a h
    exact ⟨K, l, hl, fun i => (i : A), fun i => i.2, hlim⟩
  rcases eq_or_lt_of_le (norm_nonneg a) with ha0 | ha0
  · -- `a = 0`: the constant net `0` will do
    have haz : a = 0 := norm_eq_zero.mp ha0.symm
    refine @subset_closure A (ultrastrong A) K a ⟨?_, ?_⟩
    · rw [haz]; exact zero_mem S
    · rw [← ha0]; positivity
  -- the norm closure `C` of `S` is a C*-subalgebra containing `a`
  -- in its ultrastrong closure
  set C : StarSubalgebra ℂ A := S.topologicalClosure with hC
  have hCcl : IsClosed (C : Set A) := isClosed_closure
  have haC : a ∈ @closure A (ultrastrong A) (C : Set A) := by
    refine mem_usClosure_of_mem_uwClosure (convex_starSubalgebraA C) ?_
    have hsub : (S : Set A) ⊆ (C : Set A) := subset_closure
    have hmono := @closure_mono A (ultraweak A) (S : Set A) (C : Set A) hsub
    exact hmono (hS a)
  obtain ⟨ι, l, hl, c, hc, hlimc⟩ := kaplansky C hCcl a haC
  rw [mem_usClosure_iff]
  intro ω δ hδ
  -- pick `c α` ultrastrongly close to `a`, then `s ∈ S` in norm close to `c α`
  have _ : l.NeBot := hl
  have hev := (usTendsto_iff c l a).mp hlimc ω
  have hhalf : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨i, hi⟩ := (hev.eventually (gt_mem_nhds hhalf)).exists
  set M : ℝ := omegaNorm A ω 1 with hM
  have hM0 : 0 ≤ M := omegaNorm_nonneg _ _
  set η : ℝ := min (ε * ‖a‖) (δ / (2 * (M + 1))) with hη
  have hMp : (0 : ℝ) < 2 * (M + 1) := by linarith
  have hη0 : 0 < η := lt_min (mul_pos hε ha0) (div_pos hδ hMp)
  obtain ⟨s, hsS, hsc⟩ : ∃ s ∈ (S : Set A), ‖s - c i‖ < η := by
    obtain ⟨s, hsS, hsc⟩ := Metric.mem_closure_iff.mp ((hc i).1) η hη0
    exact ⟨s, hsS, by rw [← dist_eq_norm, dist_comm]; exact hsc⟩
  refine ⟨s, ⟨hsS, ?_⟩, ?_⟩
  · have h1 : ‖s‖ ≤ ‖s - c i‖ + ‖c i‖ := by
      have := norm_add_le (s - c i) (c i)
      simpa using this
    have h2 : ‖s - c i‖ ≤ ε * ‖a‖ := hsc.le.trans (min_le_left _ _)
    have h3 : ‖c i‖ ≤ ‖a‖ := (hc i).2
    nlinarith [h1, h2, h3]
  · have hsplit : omegaNorm A ω (s - a)
        ≤ omegaNorm A ω (s - c i) + omegaNorm A ω (c i - a) :=
      omegaNorm_sub_le ω s (c i) a
    have hnorm : omegaNorm A ω (s - c i) ≤ ‖s - c i‖ * M := by
      have := omegaNorm_mul_le ω (s - c i) 1
      rwa [mul_one] at this
    have hlt : ‖s - c i‖ * M < δ / 2 := by
      have h' : ‖s - c i‖ < δ / (2 * (M + 1)) := lt_of_lt_of_le hsc (min_le_right _ _)
      have h'' : ‖s - c i‖ * (2 * (M + 1)) < δ := (lt_div_iff₀ hMp).mp h'
      nlinarith [norm_nonneg (s - c i), hM0]
    have hci : omegaNorm A ω (c i - a) < δ / 2 := hi
    linarith [hsplit, hnorm, hlt, hci]

/-! ## Parsec 750: closedness of subalgebras

**75I** (vn.tex:4460): introduction — nothing to formalize. -/

/-! ### Auxiliaries for **75II** `sequence_separation_lemma`

The thesis's proof (vn.tex:4482) builds, from a subsequence `(b_n)_n` with
`ω₀(b_n) ≤ n⁻¹2⁻ⁿ` and `ω₁(b_n^⊥) ≤ n⁻¹`, the effects
`a_{nm} = (1+d)⁻¹d` with `d = ∑_{k=n}^m k b_k`, and takes
`a = ⋀_n ⋁_{m≥n} a_{nm}`; the ceiling `⌈a⌉` is then the projection wanted.
The two ingredients below are the ones the thesis names: the map
`d ↦ (1+d)⁻¹d` is order preserving on the positives (**25II**.4
`astara_pos_basic_4`), and for an effect `b` and `m ≥ 0` one has
`(1+mb)⁻¹ ≤ (1+m)⁻¹(1+mb^⊥)` — which the thesis obtains from Gelfand's
theorem and which here is one application of `cfc_le_iff`, since both sides
are continuous functions of the single element `mb`.

`(1+d)⁻¹d` is presented as `cfc frac d` for the globally continuous
`frac t = (t ∨ 0)/(1 + (t ∨ 0))`, which makes membership in a
C\*-subalgebra and the two bounds `0 ≤ cfc frac d ≤ 1`, `cfc frac d ≤ d`
immediate; `cfc_frac_eq` identifies it with `Ring.inverse (1+d) * d` where
**25II**.4 is needed.

*Indexing note*: the thesis's `∑_{k=n}^{m}` is rendered as a sum over
`Finset.range m` of the terms `(n+j+1)·c(n+j)`, which is the same family
reindexed by `j = k − n`; this keeps every sum in `Finset.range` form. -/

/-! ### the function `t ↦ t/(1+t)` -/

private noncomputable def frac : ℝ → ℝ := fun t => max t 0 / (1 + max t 0)

private theorem frac_continuous : Continuous frac := by
  refine Continuous.div (continuous_id.max continuous_const)
    (continuous_const.add (continuous_id.max continuous_const)) fun t => ?_
  have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  exact ne_of_gt (by linarith)

private theorem frac_nonneg (t : ℝ) : 0 ≤ frac t := by
  have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  exact div_nonneg h (by linarith)

private theorem frac_le_one (t : ℝ) : frac t ≤ 1 := by
  have h : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  rw [frac, div_le_one (by linarith)]
  linarith

private theorem frac_eq {t : ℝ} (ht : 0 ≤ t) : frac t = t / (1 + t) := by
  rw [frac, max_eq_left ht]

private theorem frac_le_self {t : ℝ} (ht : 0 ≤ t) : frac t ≤ t := by
  rw [frac_eq ht, div_le_iff₀ (by linarith)]
  nlinarith

private theorem one_add_mul_frac {t : ℝ} (ht : 0 ≤ t) : (1 + t) * frac t = t := by
  rw [frac_eq ht]
  field_simp

/-! ### the operator `(1+d)⁻¹ d` -/

omit [VonNeumannAlgebra A] in
private theorem cfc_frac_mul {d : A} (hd : 0 ≤ d) : (1 + d) * cfc frac d = d := by
  have hsa : IsSelfAdjoint d := hd.isSelfAdjoint
  have h1 : cfc (fun t : ℝ => 1 + t) d = 1 + d := by
    have h := cfc_add (a := d) (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t)
      (by fun_prop) (by fun_prop)
    rwa [cfc_const_one ℝ d, cfc_id' ℝ d] at h
  have h2 : cfc (fun t : ℝ => (1 + t) * frac t) d = cfc (id : ℝ → ℝ) d :=
    cfc_congr fun t ht => one_add_mul_frac (spectrum_nonneg_of_nonneg hd ht)
  rw [← h1, ← cfc_mul _ _ d (by fun_prop) frac_continuous.continuousOn, h2, cfc_id ℝ d]

omit [VonNeumannAlgebra A] in
private theorem cfc_frac_eq {d : A} (hd : 0 ≤ d) :
    cfc frac d = Ring.inverse (1 + d) * d := by
  have hsp1 : IsStrictlyPositive (1 : A) := ⟨zero_le_one, isUnit_one⟩
  have hsp : IsStrictlyPositive ((1 : A) + d) := hsp1.add_nonneg hd
  calc cfc frac d = Ring.inverse (1 + d) * ((1 + d) * cfc frac d) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hsp.isUnit, one_mul]
    _ = Ring.inverse (1 + d) * d := by rw [cfc_frac_mul hd]

omit [VonNeumannAlgebra A] in
private theorem cfc_frac_mono {d e : A} (hd : 0 ≤ d) (hde : d ≤ e) :
    cfc frac d ≤ cfc frac e := by
  rw [cfc_frac_eq hd, cfc_frac_eq (hd.trans hde)]
  exact astara_pos_basic_4 d e hd hde

omit [VonNeumannAlgebra A] in
private theorem cfc_frac_nonneg {d : A} (_hd : 0 ≤ d) : 0 ≤ cfc frac d :=
  cfc_nonneg fun t _ => frac_nonneg t

omit [VonNeumannAlgebra A] in
private theorem cfc_frac_le_one {d : A} (hd : 0 ≤ d) : cfc frac d ≤ 1 := by
  have hsa : IsSelfAdjoint d := hd.isSelfAdjoint
  rw [← cfc_const_one ℝ d]
  exact (cfc_le_iff _ _ d frac_continuous.continuousOn (by fun_prop) hsa).mpr
    fun t _ => frac_le_one t

omit [VonNeumannAlgebra A] in
private theorem cfc_frac_le_self {d : A} (hd : 0 ≤ d) : cfc frac d ≤ d := by
  have hsa : IsSelfAdjoint d := hd.isSelfAdjoint
  nth_rewrite 2 [← cfc_id ℝ d]
  exact (cfc_le_iff _ _ d frac_continuous.continuousOn (by fun_prop) hsa).mpr
    fun t ht => frac_le_self (spectrum_nonneg_of_nonneg hd ht)

/-! ### the effect inequality of vn.tex:4547 -/

private theorem effect_key_ineq {c : A} (hc : c ∈ effects A) {M : ℝ} (hM : 0 ≤ M) :
    1 - cfc frac (M • c) ≤ ((1 + M)⁻¹ : ℝ) • (1 + M • (1 - c)) := by
  set d : A := M • c with hddef
  have hd : 0 ≤ d := smul_nonneg hM hc.1
  have hsa : IsSelfAdjoint d := hd.isSelfAdjoint
  have hnd : ‖d‖ ≤ M := by
    rw [hddef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hM]
    calc M * ‖c‖ ≤ M * 1 := mul_le_mul_of_nonneg_left (norm_le_one_of_mem_effects hc) hM
      _ = M := mul_one M
  have hspec : ∀ t ∈ spectrum ℝ d, 0 ≤ t ∧ t ≤ M := fun t ht =>
    ⟨spectrum_nonneg_of_nonneg hd ht,
      (le_abs_self t).trans ((spectrum_abs_le hsa ht).trans hnd)⟩
  have hL : 1 - cfc frac d = cfc (fun t : ℝ => 1 - frac t) d := by
    have h := cfc_sub (fun _ : ℝ => (1 : ℝ)) frac d (by fun_prop)
      frac_continuous.continuousOn
    rw [cfc_const_one ℝ d] at h
    exact h.symm
  have hA : cfc (fun _ : ℝ => (1 : ℝ) + M) d = 1 + M • (1 : A) := by
    have h := cfc_add (a := d) (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => M)
      (by fun_prop) (by fun_prop)
    rw [cfc_const_one ℝ d, cfc_const M d, Algebra.algebraMap_eq_smul_one] at h
    exact h
  have h1 : cfc (fun t : ℝ => 1 + M - t) d = 1 + M • (1 : A) - d := by
    have h := cfc_sub (fun _ : ℝ => (1 : ℝ) + M) (fun t : ℝ => t) d
      (by fun_prop) (by fun_prop)
    rwa [hA, cfc_id' ℝ d] at h
  have h2 : cfc (fun t : ℝ => (1 + M)⁻¹ * (1 + M - t)) d
      = ((1 + M)⁻¹ : ℝ) • cfc (fun t : ℝ => 1 + M - t) d := by
    rw [← cfc_smul ((1 + M)⁻¹ : ℝ) (fun t : ℝ => 1 + M - t) d (by fun_prop)]
    simp [smul_eq_mul]
  have hR : ((1 + M)⁻¹ : ℝ) • (1 + M • (1 - c))
      = cfc (fun t : ℝ => (1 + M)⁻¹ * (1 + M - t)) d := by
    rw [h2, h1, hddef, smul_sub]
    congr 2
    abel
  rw [hL, hR]
  refine (cfc_le_iff (fun t : ℝ => 1 - frac t) (fun t : ℝ => (1 + M)⁻¹ * (1 + M - t)) d
    (Continuous.continuousOn (continuous_const.sub frac_continuous)) (by fun_prop)
      hsa).mpr fun t ht => ?_
  obtain ⟨ht0, htM⟩ := hspec t ht
  have hp1 : (0 : ℝ) < 1 + t := by linarith
  have hp2 : (0 : ℝ) < 1 + M := by linarith
  rw [frac_eq ht0, ← sub_nonneg]
  have hkey : (1 + M)⁻¹ * (1 + M - t) - (1 - t / (1 + t))
      = t * (M - t) / ((1 + t) * (1 + M)) := by
    field_simp
    ring
  rw [hkey]
  exact div_nonneg (mul_nonneg ht0 (by linarith)) (by positivity)

/-! ### real parts of np-functionals -/

omit [VonNeumannAlgebra A] in
private theorem npRe_mono (ω : NPFunctional A) {x y : A} (h : x ≤ y) : (ω x).re ≤ (ω y).re :=
  (Complex.le_def.mp (npFunctional_mono ω h)).1

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem npFunctional_rsmul (ω : NPFunctional A) (r : ℝ) (x : A) :
    ω (r • x) = (r : ℂ) * ω x := by
  have h : (r • x : A) = ((r : ℂ)) • x := by
    rw [← algebraMap_smul ℂ r x]; simp
  rw [h]
  exact (map_smul ω.toPositiveLinearMap _ _).trans (smul_eq_mul _ _)

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem npRe_rsmul (ω : NPFunctional A) (r : ℝ) (x : A) :
    (ω (r • x)).re = r * (ω x).re := by
  rw [npFunctional_rsmul]
  simp [Complex.mul_re]

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem npRe_sum {J : Type*} (ω : NPFunctional A) (s : Finset J) (g : J → A) :
    (ω (∑ k ∈ s, g k)).re = ∑ k ∈ s, (ω (g k)).re := by
  rw [show ω (∑ k ∈ s, g k) = ∑ k ∈ s, ω (g k) from map_sum ω.toPositiveLinearMap g s,
    Complex.re_sum]

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem npRe_add (ω : NPFunctional A) (x y : A) :
    (ω (x + y)).re = (ω x).re + (ω y).re := by
  rw [npFunctional_add]; simp

omit [VonNeumannAlgebra A] in
private theorem npFunctional_le_ofReal (ω : NPFunctional A) {x : A} (hx : 0 ≤ x) {r : ℝ}
    (h : (ω x).re ≤ r) : (ω x : ℂ) ≤ (r : ℂ) := by
  have h0 : (0 : ℂ) ≤ ω x := npFunctional_nonneg ω hx
  obtain ⟨_, h2⟩ := Complex.le_def.mp h0
  exact Complex.le_def.mpr ⟨by simpa using h, by simp [← h2]⟩

omit [VonNeumannAlgebra A] in
private theorem npFunctional_eq_zero_of_re_le_zero (ω : NPFunctional A) {x : A} (hx : 0 ≤ x)
    (h : (ω x).re ≤ 0) : ω x = 0 := by
  have h0 : (0 : ℂ) ≤ ω x := npFunctional_nonneg ω hx
  obtain ⟨h1, h2⟩ := Complex.le_def.mp h0
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  exact Complex.ext (by simp; linarith) (by simp [← h2])

/-! ### chain suprema -/

omit [StarOrderedRing A] in
private theorem exists_chain_lub {u : ℕ → selfAdjoint A} (hmono : Monotone u)
    {B : selfAdjoint A} (hub : ∀ n, u n ≤ B) :
    ∃ s : selfAdjoint A, IsLUB (Set.range u) s :=
  VonNeumannAlgebra.isLUB_of_bddAbove_directed (Set.range u) ⟨u 0, 0, rfl⟩
    (directedOn_range.mpr hmono.directed_le) ⟨B, by rintro _ ⟨n, rfl⟩; exact hub n⟩

private theorem le_ceil_of_mem_effects {a : A} (ha : a ∈ effects A) : a ≤ ceil a := by
  obtain ⟨hp, hac, _⟩ := ceil_spec ha.1
  have hca : ceil a * a = a := by
    have h := congrArg star hac
    rwa [star_mul, hp.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg ha.1).star_eq] at h
  calc a = ceil a * a * ceil a := by rw [hca, hac]
    _ ≤ ceil a * 1 * ceil a := IsSelfAdjoint.conjugate_le_conjugate ha.2 hp.isSelfAdjoint
    _ = ceil a := by rw [mul_one, hp.isIdempotentElem.eq]

private theorem geom_half_le (m : ℕ) : ∑ j ∈ Finset.range m, (2 : ℝ)⁻¹ ^ j ≤ 2 := by
  rw [geom_sum_eq (by norm_num)]
  have h1 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  rw [div_le_iff_of_neg (by norm_num : ((2 : ℝ)⁻¹ - 1) < 0)]
  nlinarith

/-- **75II** (`sequence-separation-lemma`, vn.tex:4469, Lemma): let `S` be
a von Neumann subalgebra of `A`, and let `ω₀`, `ω₁` be npu-functionals on
`A` separated by a net `(b_α)_α` of effects of `S` (i.e.
`ω₀(b_α) → 0` and `ω₁(b_α^⊥) → 0`).  Then `ω₀` and `ω₁` are separated by a
projection `q ∈ S`: `ω₀(q) = 0 = ω₁(q^⊥)`.

*Class 1 — faithful*, apart from the indexing note above.  Note that
**`ω₀(1) = 1` is never used** — the `ω₀`-half of the argument only needs
`ω₀` positive and normal; only `ω₁`'s normalisation enters, and there only
through `ω₁(1) ≤ 1`.  The binder is therefore spelled `_hω₀`. -/
theorem sequence_separation_lemma (S : StarSubalgebra ℂ A)
    (hS : IsVNSubalgebra A S) (ω₀ ω₁ : NPFunctional A) (_hω₀ : ω₀ 1 = 1)
    (hω₁ : ω₁ 1 = 1) {ι : Type*} {l : Filter ι} [l.NeBot] (b : ι → A)
    (hb : ∀ i, b i ∈ S ∧ b i ∈ effects A)
    (h₀ : Tendsto (fun i => ω₀ (b i)) l (𝓝 0))
    (h₁ : Tendsto (fun i => ω₁ (1 - b i)) l (𝓝 0)) :
    ∃ q : A, q ∈ S ∧ IsStarProjection q ∧ ω₀ q = 0 ∧ ω₁ (1 - q) = 0 := by
  classical
  -- 1. a subsequence with quantitative bounds (vn.tex:4497)
  have hchoice : ∀ n : ℕ, ∃ i : ι,
      (ω₀ (b i)).re ≤ ((n : ℝ) + 1)⁻¹ * (2 : ℝ)⁻¹ ^ (n + 1) ∧
      (ω₁ (1 - b i)).re ≤ ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hp0 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ * (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
    have hp1 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨i, hi0, hi1⟩ :=
      (((Metric.tendsto_nhds.mp h₀) _ hp0).and ((Metric.tendsto_nhds.mp h₁) _ hp1)).exists
    rw [dist_zero_right] at hi0 hi1
    exact ⟨i, (Complex.re_le_norm _).trans hi0.le, (Complex.re_le_norm _).trans hi1.le⟩
  choose idx hidx0 hidx1 using hchoice
  set c : ℕ → A := fun n => b (idx n) with hcdef
  have hcS : ∀ n, c n ∈ S := fun n => (hb (idx n)).1
  have hceff : ∀ n, c n ∈ effects A := fun n => (hb (idx n)).2
  -- 2. the partial sums `D n m = ∑_{j<m} (n+j+1)·c (n+j)`
  set D : ℕ → ℕ → A := fun n m => ∑ j ∈ Finset.range m, ((n : ℝ) + j + 1) • c (n + j)
    with hDdef
  have hDnn : ∀ n m, 0 ≤ D n m := fun n m =>
    Finset.sum_nonneg fun j _ => smul_nonneg (by positivity) (hceff _).1
  have hDS : ∀ n m, D n m ∈ S := fun n m => by
    refine sum_mem fun j _ => ?_
    rw [show (((n : ℝ) + j + 1) • c (n + j) : A)
        = ((((n : ℝ) + j + 1 : ℝ) : ℂ)) • c (n + j) from by
      rw [← algebraMap_smul ℂ ((n : ℝ) + j + 1) (c (n + j))]; simp]
    exact SMulMemClass.smul_mem _ (hcS _)
  have hDmono : ∀ (n : ℕ) {m m' : ℕ}, m ≤ m' → D n m ≤ D n m' := by
    intro n m m' h
    have hsub : Finset.range m ⊆ Finset.range m' := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun j _ _ => smul_nonneg (by positivity) (hceff _).1
  have hDstep : ∀ n m : ℕ, D (n + 1) m ≤ D n (m + 1) := by
    intro n m
    have hsplit : D n (m + 1) = D (n + 1) m + ((n : ℝ) + (0 : ℕ) + 1) • c (n + 0) := by
      simp only [hDdef]
      rw [Finset.sum_range_succ' (fun j : ℕ => ((n : ℝ) + j + 1) • c (n + j)) m]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : (n : ℝ) + ((j + 1 : ℕ) : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) + (j : ℝ) + 1 := by
        push_cast; ring
      have h2 : n + (j + 1) = n + 1 + j := by omega
      rw [h1, h2]
    rw [hsplit]
    exact le_add_of_nonneg_right (smul_nonneg (by positivity) (hceff _).1)
  have hDsingle : ∀ n m' : ℕ, ((n : ℝ) + m' + 1) • c (n + m') ≤ D n (m' + 1) := by
    intro n m'
    exact Finset.single_le_sum (f := fun j : ℕ => ((n : ℝ) + j + 1) • c (n + j))
      (fun j _ => smul_nonneg (by positivity) (hceff _).1) (Finset.self_mem_range_succ m')
  -- 3. the effects `a n m = (1 + D n m)⁻¹ (D n m)`
  set aa : ℕ → ℕ → A := fun n m => cfc frac (D n m) with haadef
  have haaS : ∀ n m, aa n m ∈ S := fun n m => by
    have hcl : IsClosed ((S : StarSubalgebra ℂ A) : Set A) := hS.isClosed
    exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) frac (hDS n m)
  have haann : ∀ n m, 0 ≤ aa n m := fun n m => cfc_frac_nonneg (hDnn n m)
  have haa1 : ∀ n m, aa n m ≤ 1 := fun n m => cfc_frac_le_one (hDnn n m)
  have haasa : ∀ n m, IsSelfAdjoint (aa n m) := fun n m => (haann n m).isSelfAdjoint
  have haamono : ∀ (n : ℕ) {m m' : ℕ}, m ≤ m' → aa n m ≤ aa n m' := fun n _ _ h =>
    cfc_frac_mono (hDnn _ _) (hDmono n h)
  have haastep : ∀ n m : ℕ, aa (n + 1) m ≤ aa n (m + 1) := fun n m =>
    cfc_frac_mono (hDnn _ _) (hDstep n m)
  -- 4. the `ω₀`-estimate
  have hω₀aa : ∀ n m, (ω₀ (aa n m)).re ≤ (2 : ℝ)⁻¹ ^ n := by
    intro n m
    have h1 : (ω₀ (aa n m)).re ≤ (ω₀ (D n m)).re :=
      npRe_mono ω₀ (cfc_frac_le_self (hDnn n m))
    have h2 : (ω₀ (D n m)).re
        = ∑ j ∈ Finset.range m, ((n : ℝ) + j + 1) * (ω₀ (c (n + j))).re := by
      simp only [hDdef]
      rw [npRe_sum]
      exact Finset.sum_congr rfl fun j _ => npRe_rsmul ω₀ _ _
    have h3 : ∀ j : ℕ, ((n : ℝ) + j + 1) * (ω₀ (c (n + j))).re ≤ (2 : ℝ)⁻¹ ^ (n + j + 1) := by
      intro j
      have hk := hidx0 (n + j)
      have hcast : ((n + j : ℕ) : ℝ) + 1 = (n : ℝ) + j + 1 := by push_cast; ring
      rw [hcast] at hk
      have hpos : (0 : ℝ) < (n : ℝ) + j + 1 := by positivity
      calc ((n : ℝ) + j + 1) * (ω₀ (c (n + j))).re
          ≤ ((n : ℝ) + j + 1) * (((n : ℝ) + j + 1)⁻¹ * (2 : ℝ)⁻¹ ^ (n + j + 1)) :=
            mul_le_mul_of_nonneg_left hk hpos.le
        _ = (2 : ℝ)⁻¹ ^ (n + j + 1) := by field_simp
    have h4 : ∑ j ∈ Finset.range m, ((n : ℝ) + j + 1) * (ω₀ (c (n + j))).re
        ≤ ∑ j ∈ Finset.range m, (2 : ℝ)⁻¹ ^ (n + j + 1) :=
      Finset.sum_le_sum fun j _ => h3 j
    have h5 : ∑ j ∈ Finset.range m, (2 : ℝ)⁻¹ ^ (n + j + 1)
        = (2 : ℝ)⁻¹ ^ (n + 1) * ∑ j ∈ Finset.range m, (2 : ℝ)⁻¹ ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_add]
      ring_nf
    have h6 : (2 : ℝ)⁻¹ ^ (n + 1) * ∑ j ∈ Finset.range m, (2 : ℝ)⁻¹ ^ j ≤ (2 : ℝ)⁻¹ ^ n := by
      have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
      calc (2 : ℝ)⁻¹ ^ (n + 1) * ∑ j ∈ Finset.range m, (2 : ℝ)⁻¹ ^ j
          ≤ (2 : ℝ)⁻¹ ^ (n + 1) * 2 := mul_le_mul_of_nonneg_left (geom_half_le m) hp.le
        _ = (2 : ℝ)⁻¹ ^ n := by rw [pow_succ]; field_simp
    rw [h2] at h1
    linarith [h4, h5 ▸ h6]
  -- 5. the `ω₁`-estimate
  have hω₁aa : ∀ n m' : ℕ,
      (ω₁ (1 - aa n (m' + 1))).re ≤ 2 / (1 + ((n : ℝ) + m' + 1)) := by
    intro n m'
    set M : ℝ := (n : ℝ) + m' + 1 with hMdef
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMpos : (0 : ℝ) < M := by positivity
    have hle : 1 - aa n (m' + 1) ≤ ((1 + M)⁻¹ : ℝ) • (1 + M • (1 - c (n + m'))) := by
      refine le_trans (sub_le_sub_left ?_ 1) (effect_key_ineq (hceff (n + m')) hM0)
      exact cfc_frac_mono (smul_nonneg hM0 (hceff (n + m')).1) (hDsingle n m')
    refine (npRe_mono ω₁ hle).trans ?_
    rw [npRe_rsmul, npRe_add, npRe_rsmul]
    have hone : (ω₁ (1 : A)).re = 1 := by rw [hω₁]; simp
    have hcb : (ω₁ (1 - c (n + m'))).re ≤ M⁻¹ := by
      have hk := hidx1 (n + m')
      have hcast : ((n + m' : ℕ) : ℝ) + 1 = M := by rw [hMdef]; push_cast; ring
      rwa [hcast] at hk
    rw [hone]
    have hMi : (0 : ℝ) < 1 + M := by linarith
    rw [div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : M * (ω₁ (1 - c (n + m'))).re ≤ M * M⁻¹ :=
      mul_le_mul_of_nonneg_left hcb hM0
    rw [mul_inv_cancel₀ (ne_of_gt hMpos)] at this
    linarith
  -- 6. `a n = ⋁_m a n m`
  have hlubex : ∀ n : ℕ, ∃ s : selfAdjoint A,
      IsLUB (Set.range fun m : ℕ => (⟨aa n m, haasa n m⟩ : selfAdjoint A)) s := by
    intro n
    exact exists_chain_lub (B := ⟨1, IsSelfAdjoint.one A⟩)
      (fun m m' h => Subtype.coe_le_coe.mp (haamono n h))
      (fun m => Subtype.coe_le_coe.mp (haa1 n m))
  choose an han using hlubex
  have hdir : ∀ n : ℕ, DirectedOn (· ≤ ·)
      (Set.range fun m : ℕ => (⟨aa n m, haasa n m⟩ : selfAdjoint A)) := fun n =>
    directedOn_range.mpr
      (Monotone.directed_le fun m m' h => Subtype.coe_le_coe.mp (haamono n h))
  have hanS : ∀ n, ((an n : selfAdjoint A) : A) ∈ S := fun n =>
    hS.dirSup_mem _ (an n) (by rintro _ ⟨m, rfl⟩; exact haaS n m)
      (Set.range_nonempty _) (hdir n) (han n)
  have haale : ∀ n m, aa n m ≤ ((an n : selfAdjoint A) : A) := fun n m =>
    Subtype.coe_le_coe.mpr ((han n).1 ⟨m, rfl⟩)
  have hanle1 : ∀ n, ((an n : selfAdjoint A) : A) ≤ 1 := fun n => by
    have h : an n ≤ (⟨1, IsSelfAdjoint.one A⟩ : selfAdjoint A) :=
      (han n).2 (by rintro _ ⟨m, rfl⟩; exact Subtype.coe_le_coe.mp (haa1 n m))
    exact Subtype.coe_le_coe.mpr h
  have hannn : ∀ n, (0 : A) ≤ ((an n : selfAdjoint A) : A) := fun n =>
    (haann n 0).trans (haale n 0)
  have hananti : ∀ n, ((an (n + 1) : selfAdjoint A) : A) ≤ ((an n : selfAdjoint A) : A) :=
    fun n => Subtype.coe_le_coe.mpr ((han (n + 1)).2 (by
      rintro _ ⟨m, rfl⟩
      exact Subtype.coe_le_coe.mp ((haastep n m).trans (haale n (m + 1)))))
  -- `ω₀ (a n) ≤ 2⁻ⁿ` by normality
  have hω₀an : ∀ n, (ω₀ ((an n : selfAdjoint A) : A)).re ≤ (2 : ℝ)⁻¹ ^ n := by
    intro n
    have hnorm := ω₀.preservesDirSups' _ (an n) (Set.range_nonempty _) (hdir n) (han n)
    have hub : (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) ∈
        upperBounds ((fun d : selfAdjoint A => (ω₀ (d : A) : ℂ)) ''
          (Set.range fun m : ℕ => (⟨aa n m, haasa n m⟩ : selfAdjoint A))) := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact npFunctional_le_ofReal ω₀ (haann n m) (hω₀aa n m)
    exact_mod_cast (Complex.le_def.mp (hnorm.2 hub)).1
  -- `ω₁ (1 - a n) = 0`
  have hω₁an : ∀ n, ω₁ (1 - ((an n : selfAdjoint A) : A)) = 0 := by
    intro n
    refine npFunctional_eq_zero_of_re_le_zero ω₁ (by
      simpa using sub_nonneg.mpr (hanle1 n)) ?_
    have htend : Tendsto (fun m' : ℕ => 2 / (1 + ((n : ℝ) + m' + 1))) atTop (𝓝 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      refine tendsto_atTop_mono (fun m' : ℕ => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    refine ge_of_tendsto' htend fun m' => ?_
    exact (npRe_mono ω₁ (sub_le_sub_left (haale n (m' + 1)) 1)).trans (hω₁aa n m')
  -- 7. `E = ⋁_n (1 - a n)` and `a = 1 - E`
  have hesa : ∀ n : ℕ, IsSelfAdjoint (1 - ((an n : selfAdjoint A) : A)) :=
    fun n => (sub_nonneg.mpr (hanle1 n)).isSelfAdjoint
  obtain ⟨E, hE⟩ := exists_chain_lub
    (u := fun n : ℕ => (⟨1 - ((an n : selfAdjoint A) : A), hesa n⟩ : selfAdjoint A))
    (B := (⟨1, IsSelfAdjoint.one A⟩ : selfAdjoint A))
    (by
      intro n n' h
      refine Subtype.coe_le_coe.mp (sub_le_sub_left ?_ 1)
      induction h with
      | refl => exact le_rfl
      | step _ ih => exact (hananti _).trans ih)
    (fun n => Subtype.coe_le_coe.mp (by simpa using sub_le_self (1 : A) (hannn n)))
  set a : A := 1 - ((E : selfAdjoint A) : A) with hadef
  have hEdir : DirectedOn (· ≤ ·)
      (Set.range fun n : ℕ => (⟨1 - ((an n : selfAdjoint A) : A), hesa n⟩ : selfAdjoint A)) := by
    refine directedOn_range.mpr (Monotone.directed_le ?_)
    intro n n' h
    refine Subtype.coe_le_coe.mp (sub_le_sub_left ?_ 1)
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact (hananti _).trans ih
  have hES : ((E : selfAdjoint A) : A) ∈ S :=
    hS.dirSup_mem _ E (by
      rintro _ ⟨n, rfl⟩
      exact sub_mem (one_mem _) (hanS n)) (Set.range_nonempty _) hEdir hE
  have hEle : ∀ n, 1 - ((an n : selfAdjoint A) : A) ≤ ((E : selfAdjoint A) : A) := fun n =>
    Subtype.coe_le_coe.mpr (hE.1 ⟨n, rfl⟩)
  have hEle1 : ((E : selfAdjoint A) : A) ≤ 1 := by
    have h : E ≤ (⟨1, IsSelfAdjoint.one A⟩ : selfAdjoint A) :=
      hE.2 (by
        rintro _ ⟨n, rfl⟩
        exact Subtype.coe_le_coe.mp (by simpa using sub_le_self (1 : A) (hannn n)))
    exact Subtype.coe_le_coe.mpr h
  have hann : (0 : A) ≤ a := by rw [hadef]; exact sub_nonneg.mpr hEle1
  have hale1 : a ≤ 1 := by
    rw [hadef]
    have : (0 : A) ≤ ((E : selfAdjoint A) : A) :=
      (sub_nonneg.mpr (hanle1 0)).trans (hEle 0)
    simpa using sub_le_self (1 : A) this
  have haS : a ∈ S := sub_mem (one_mem _) hES
  have halean : ∀ n, a ≤ ((an n : selfAdjoint A) : A) := by
    intro n
    rw [hadef]
    exact sub_le_comm.mp (hEle n)
  -- `ω₀ a = 0`
  have hω₀a : ω₀ a = 0 := by
    refine npFunctional_eq_zero_of_re_le_zero ω₀ hann ?_
    refine ge_of_tendsto'
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
      fun n => ?_
    exact (npRe_mono ω₀ (halean n)).trans (hω₀an n)
  -- `ω₁ (1 - a) = ω₁ E = 0`
  have hω₁a : ω₁ (1 - a) = 0 := by
    have hEeq : (1 : A) - a = ((E : selfAdjoint A) : A) := by rw [hadef]; abel
    rw [hEeq]
    have hnorm := ω₁.preservesDirSups' _ E (Set.range_nonempty _) hEdir hE
    have hub : (0 : ℂ) ∈ upperBounds ((fun d : selfAdjoint A => (ω₁ (d : A) : ℂ)) ''
        (Set.range fun n : ℕ => (⟨1 - ((an n : selfAdjoint A) : A), hesa n⟩ : selfAdjoint A))) := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact le_of_eq (hω₁an n)
    have hle : (ω₁ ((E : selfAdjoint A) : A) : ℂ) ≤ 0 := hnorm.2 hub
    refine npFunctional_eq_zero_of_re_le_zero ω₁ ((sub_nonneg.mpr (hanle1 0)).trans (hEle 0)) ?_
    simpa using (Complex.le_def.mp hle).1
  -- 8. pass to the ceiling
  refine ⟨ceil a, ceil_mem hS hann haS, (ceil_spec hann).1,
    (ceil_functionals_lemma a hann ω₀).mp hω₀a, ?_⟩
  have hq1 : ceil a ≤ 1 := (ceil_spec hann).1.le_one
  refine npFunctional_eq_zero_of_re_le_zero ω₁ (by simpa using sub_nonneg.mpr hq1) ?_
  have := npRe_mono ω₁ (sub_le_sub_left (le_ceil_of_mem_effects ⟨hann, hale1⟩) (1 : A))
  rw [hω₁a] at this
  simpa using this


/-- **75VI** (`kadisons-lemma`, vn.tex:4560, Lemma): let `S` be a von
Neumann subalgebra of `A` and `p` a projection of `A` in the ultrastrong
closure of `S`.  For all npu-functionals `ω₀`, `ω₁` with
`ω₀(p) = 0 = ω₁(p^⊥)` there is a projection `q ∈ S` with
`ω₀(q) = 0 = ω₁(q^⊥)`.

*Class 1 — faithful*: Kaplansky's density theorem in the effect form
(**74IV**.3 `kaplansky_effects`) replaces the approximating net by one of
effects, and **75II** finishes.  Only the *effect* case of 74IV is used, so
this does not depend on the general 74IV (which is proved too, but only
later in the file, since its proof runs the effect case in `M₂(𝒜)`). -/
theorem kadisons_lemma (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S)
    (p : A) (hp : IsStarProjection p)
    (hcl : p ∈ @closure A (ultrastrong A) S) (ω₀ ω₁ : NPFunctional A)
    (hω₀ : ω₀ 1 = 1) (hω₁ : ω₁ 1 = 1) (h₀ : ω₀ p = 0)
    (h₁ : ω₁ (1 - p) = 0) :
    ∃ q : A, q ∈ S ∧ IsStarProjection q ∧ ω₀ q = 0 ∧ ω₁ (1 - q) = 0 := by
  obtain ⟨ι, l, hl, a, ha, hlim⟩ :=
    kaplansky_effects S hS.isClosed p hcl ⟨hp.nonneg, hp.le_one⟩
  have huw := (uwTendsto_iff a l p).mp (uwweaker_2 a l p hlim)
  have : l.NeBot := hl
  refine sequence_separation_lemma S hS ω₀ ω₁ hω₀ hω₁ (l := l) a
    (fun i => ⟨(ha i).1, (ha i).2.2⟩) ?_ ?_
  · have h := huw ω₀
    rwa [h₀] at h
  · have h := (tendsto_const_nhds (x := (ω₁ 1 : ℂ)) (f := l)).sub (huw ω₁)
    have heq : ∀ i, (ω₁ 1 : ℂ) - ω₁ (a i) = ω₁ (1 - a i) := fun i => by
      rw [npFunctional_sub]
    simp only [heq] at h
    rw [← npFunctional_sub, h₁] at h
    exact h

section VNSubalgebraClosure

variable {S : StarSubalgebra ℂ A}

/-- Auxiliary for **75VIII**: the supremum (in the poset of projections of
`A`) of a set of projections of a von Neumann subalgebra `S` again lies in
`S`, and any np-functional annihilating the set annihilates the supremum.

The two statements are proved together because they use the same directed
set: the projections of `S` that are annihilated by `ω` and lie below every
projection upper bound of `P`.  It is directed by `⌈x + y⌉`
(`isLeast_ceil_add`), which stays in `S` by `ceil_mem` and is annihilated by
`ω` by **60I** (`ceil_functionals_lemma`). -/
theorem projSup_mem_of_np (hS : IsVNSubalgebra A S)
    (P : Set A) (hP : ∀ p ∈ P, IsStarProjection p) (hPS : ∀ p ∈ P, p ∈ S)
    (ω : NPFunctional A) (hω : ∀ p ∈ P, ω p = 0) :
    projSup P ∈ S ∧ ω (projSup P) = 0 := by
  classical
  obtain ⟨hsproj, hsub, hsleast⟩ := projSup_spec hP
  set J : Set A := {d : A | IsStarProjection d ∧ d ∈ S ∧ ω d = 0 ∧
    ∀ r : A, IsStarProjection r → (∀ p ∈ P, p ≤ r) → d ≤ r} with hJdef
  have hPJ : P ⊆ J := fun p hp =>
    ⟨hP p hp, hPS p hp, hω p hp, fun r _ hr => hr p hp⟩
  have hne : J.Nonempty :=
    ⟨0, IsStarProjection.zero A, zero_mem _, npFunctional_zero ω,
      fun r hr _ => hr.nonneg⟩
  have hdir : DirectedOn (· ≤ ·) J := by
    rintro x ⟨hx, hxS, hxω, hxle⟩ y ⟨hy, hyS, hyω, hyle⟩
    obtain ⟨⟨hj, hxj, hyj⟩, hjleast⟩ := isLeast_ceil_add hx hy
    have hsum : (0 : A) ≤ x + y := add_nonneg hx.nonneg hy.nonneg
    have hωsum : ω (x + y) = 0 := by
      rw [npFunctional_add, hxω, hyω, add_zero]
    refine ⟨ceil (x + y), ⟨hj, ceil_mem hS hsum (add_mem hxS hyS),
      (ceil_functionals_lemma (x + y) hsum ω).mp hωsum, fun r hr hrP =>
        hjleast ⟨hr, hxle r hr hrP, hyle r hr hrP⟩⟩, hxj, hyj⟩
  have hbdd : BddAbove J := ⟨1, fun d hd => hd.1.le_one⟩
  set J' : Set (selfAdjoint A) := {d : selfAdjoint A | (d : A) ∈ J} with hJ'def
  have hval : Subtype.val '' J' = J := by
    ext x
    exact ⟨by rintro ⟨d, hd, rfl⟩; exact hd,
      fun hx => ⟨⟨x, hx.1.isSelfAdjoint⟩, hx, rfl⟩⟩
  obtain ⟨d₀, hd₀⟩ := id hne
  have hne' : J'.Nonempty := ⟨⟨d₀, hd₀.1.isSelfAdjoint⟩, hd₀⟩
  have hdir' : DirectedOn (· ≤ ·) J' := by
    intro x hx y hy
    obtain ⟨c, hc, hxc, hyc⟩ := hdir _ hx _ hy
    exact ⟨⟨c, hc.1.isSelfAdjoint⟩, hc, hxc, hyc⟩
  have hbdd' : BddAbove J' := ⟨⟨1, IsSelfAdjoint.one A⟩, fun d hd => hd.1.le_one⟩
  have h3 : J'.Nonempty ∧ DirectedOn (· ≤ ·) J' ∧ BddAbove J' := ⟨hne', hdir', hbdd'⟩
  have hlubSA : IsLUB J' (dirSup J' h3) := isLUB_dirSup J' h3
  have hlub : IsLUB J ((dirSup J' h3 : selfAdjoint A) : A) := by
    rw [← hval]
    exact isLUB_coe_of_isLUB hne' hlubSA
  set s : A := ((dirSup J' h3 : selfAdjoint A) : A) with hsdef
  have hsprojJ : IsStarProjection s :=
    vna_directed_supremum_projections J s (fun d hd => hd.1) hne hdir hlub
  -- `s = projSup P`
  have hle₁ : projSup P ≤ s := hsleast s hsprojJ fun p hp => hlub.1 (hPJ hp)
  have hle₂ : s ≤ projSup P := hlub.2 fun d hd => hd.2.2.2 _ hsproj hsub
  have hseq : s = projSup P := le_antisymm hle₂ hle₁
  refine ⟨hseq ▸ hS.dirSup_mem J' (dirSup J' h3) (fun d hd => hd.2.1) hne' hdir' hlubSA, ?_⟩
  -- `ω` annihilates the supremum, by normality
  have hω' := ω.preservesDirSups' J' (dirSup J' h3) hne' hdir' hlubSA
  have himg : (fun d : selfAdjoint A => ω.toPositiveLinearMap (d : A)) '' J' = {(0 : ℂ)} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨d₀, hd₀.1.isSelfAdjoint⟩, hd₀, hd₀.2.2.1⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hd.2.2.1
  rw [himg] at hω'
  rw [← hseq]
  change ω.toPositiveLinearMap s = 0
  exact IsLUB.unique hω' isLUB_singleton


/-- Auxiliary: a projection annihilated by `ω` lies below `⌈ω⌉^⊥`. -/
theorem proj_le_npCarrier_compl (ω : NPFunctional A) {q : A}
    (hq : IsStarProjection q) (h : ω q = 0) : q ≤ 1 - npCarrier ω := by
  have hle := (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.2 (1 - q)
    hq.one_sub (by rw [sub_sub_cancel]; exact h)
  exact le_sub_comm.mp hle

variable (S) in
/-- The **relative co-carrier** `⌈ω⌉_𝒮^⊥`: the largest projection of the von
Neumann subalgebra `𝒮` annihilated by `ω`.  (The thesis's `⌈ω⌉_𝒮` is
`1 - relCoceil 𝒮 ω`; the complement is the convenient form, since it is a
`projSup` rather than a `projInf`.) -/
noncomputable def relCoceil (ω : NPFunctional A) : A :=
  projSup {q : A | IsStarProjection q ∧ q ∈ S ∧ ω q = 0}

omit [StarOrderedRing A] [VonNeumannAlgebra A] in
private theorem relCoceil_set_proj (ω : NPFunctional A) :
    ∀ q ∈ {q : A | IsStarProjection q ∧ q ∈ S ∧ ω q = 0}, IsStarProjection q :=
  fun _ hq => hq.1

theorem relCoceil_isStarProjection (ω : NPFunctional A) :
    IsStarProjection (relCoceil S ω) :=
  (projSup_spec (relCoceil_set_proj ω)).1

theorem le_relCoceil (ω : NPFunctional A) {q : A} (hq : IsStarProjection q)
    (hqS : q ∈ S) (h : ω q = 0) : q ≤ relCoceil S ω :=
  (projSup_spec (relCoceil_set_proj ω)).2.1 q ⟨hq, hqS, h⟩

theorem relCoceil_mem (hS : IsVNSubalgebra A S) (ω : NPFunctional A) :
    relCoceil S ω ∈ S :=
  (projSup_mem_of_np hS _ (relCoceil_set_proj ω) (fun _ hq => hq.2.1) ω
    (fun _ hq => hq.2.2)).1

theorem relCoceil_apply (hS : IsVNSubalgebra A S) (ω : NPFunctional A) :
    ω (relCoceil S ω) = 0 :=
  (projSup_mem_of_np hS _ (relCoceil_set_proj ω) (fun _ hq => hq.2.1) ω
    (fun _ hq => hq.2.2)).2

/-- `⌈ω⌉ ≤ ⌈ω⌉_𝒮`, in complemented form. -/
theorem relCoceil_le_npCarrier_compl (hS : IsVNSubalgebra A S) (ω : NPFunctional A) :
    relCoceil S ω ≤ 1 - npCarrier ω :=
  proj_le_npCarrier_compl ω (relCoceil_isStarProjection ω) (relCoceil_apply hS ω)

theorem relCoceil_eq_one_of_apply_one (ω : NPFunctional A) (h : ω 1 = 0) :
    relCoceil S ω = 1 :=
  le_antisymm (relCoceil_isStarProjection ω).le_one
    (le_relCoceil ω (IsStarProjection.one A) (one_mem S) h)


omit [VonNeumannAlgebra A] in
/-- Auxiliary for the normalisation step: an np-functional with `ω 1 ≠ 0`
becomes an npu-functional after scaling by `(ω 1)⁻¹`, without changing which
elements it annihilates. -/
theorem exists_unital_scaling (ω : NPFunctional A) (h : ω 1 ≠ 0) :
    ∃ (ω' : NPFunctional A) (c : ℂ), c ≠ 0 ∧ ω' 1 = 1 ∧ ∀ a, ω' a = c * ω a := by
  have him : (ω 1).im = 0 := npFunctional_im_eq_zero ω (IsSelfAdjoint.one A)
  have hnn : (0 : ℂ) ≤ ω 1 := npFunctional_nonneg ω zero_le_one
  have hre : (0 : ℝ) ≤ (ω 1).re := (Complex.le_def.mp hnn).1
  set r : ℝ := (ω 1).re with hrdef
  have hone : ω 1 = (r : ℂ) := by
    apply Complex.ext <;> simp [hrdef, him]
  have hrne : r ≠ 0 := fun h0 => h (by rw [hone, h0]; simp)
  have hrinv : (0 : ℝ) ≤ r⁻¹ := inv_nonneg.mpr hre
  refine ⟨smulNP hrinv ω, ((r⁻¹ : ℝ) : ℂ), ?_, ?_, fun a => smulNP_apply hrinv ω a⟩
  · simpa using inv_ne_zero hrne
  · rw [smulNP_apply, hone, ← Complex.ofReal_mul, inv_mul_cancel₀ hrne, Complex.ofReal_one]

/-- The heart of **75VIII**: for `ω₀` with `ω₀(p) = 0` and `ω₁` with
`ω₁(p^⊥) = 0`, Kadison's lemma (**75VI**) produces a projection `q ∈ 𝒮`
between `⌈ω₁⌉_𝒮` and `⌈ω₀⌉_𝒮^⊥`. -/
theorem relCoceil_compl_le (hS : IsVNSubalgebra A S) {p : A}
    (hp : IsStarProjection p) (hcl : p ∈ @closure A (ultrastrong A) S)
    (ω₀ ω₁ : NPFunctional A) (h₀ : ω₀ p = 0) (h₁ : ω₁ (1 - p) = 0) :
    1 - relCoceil S ω₁ ≤ relCoceil S ω₀ := by
  by_cases hu₀ : ω₀ 1 = 0
  · rw [relCoceil_eq_one_of_apply_one ω₀ hu₀]
    simpa using (relCoceil_isStarProjection (S := S) ω₁).nonneg
  by_cases hu₁ : ω₁ 1 = 0
  · rw [relCoceil_eq_one_of_apply_one ω₁ hu₁, sub_self]
    exact (relCoceil_isStarProjection (S := S) ω₀).nonneg
  obtain ⟨ω₀', c₀, hc₀, hu₀', he₀⟩ := exists_unital_scaling ω₀ hu₀
  obtain ⟨ω₁', c₁, hc₁, hu₁', he₁⟩ := exists_unital_scaling ω₁ hu₁
  obtain ⟨q, hqS, hq, hq₀, hq₁⟩ :=
    kadisons_lemma S hS p hp hcl ω₀' ω₁' hu₀' hu₁' (by rw [he₀, h₀, mul_zero])
      (by rw [he₁, h₁, mul_zero])
  have hω₀q : ω₀ q = 0 := by
    have := hq₀; rw [he₀] at this
    exact (mul_eq_zero.mp this).resolve_left hc₀
  have hω₁q : ω₁ (1 - q) = 0 := by
    have := hq₁; rw [he₁] at this
    exact (mul_eq_zero.mp this).resolve_left hc₁
  have h1 : q ≤ relCoceil S ω₀ := le_relCoceil ω₀ hq hqS hω₀q
  have h2 : 1 - q ≤ relCoceil S ω₁ :=
    le_relCoceil ω₁ hq.one_sub (sub_mem (one_mem S) hqS) hω₁q
  exact le_trans (sub_le_comm.mp h2) h1

/-- **75VIII**, main step: a projection of `A` lying in the ultrastrong
closure of a von Neumann subalgebra `𝒮` already lies in `𝒮`. -/
theorem projection_mem_of_mem_usClosure (hS : IsVNSubalgebra A S) {p : A}
    (hp : IsStarProjection p) (hcl : p ∈ @closure A (ultrastrong A) S) : p ∈ S := by
  classical
  have hcarrier : ∀ ω : NPFunctional A, IsStarProjection (npCarrier ω) :=
    fun ω => (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  set Q : Set A := {q : A | ∃ ω : NPFunctional A, ω (1 - p) = 0 ∧
    q = 1 - relCoceil S ω} with hQdef
  have hQproj : ∀ q ∈ Q, IsStarProjection q := by
    rintro _ ⟨ω, -, rfl⟩
    exact (relCoceil_isStarProjection ω).one_sub
  have hQS : ∀ q ∈ Q, q ∈ S := by
    rintro _ ⟨ω, -, rfl⟩
    exact sub_mem (one_mem S) (relCoceil_mem hS ω)
  obtain ⟨hUproj, hUub, hUleast⟩ := projSup_spec hQproj
  set U : A := projSup Q with hUdef
  -- `p ≤ ⋁_{ω₁} ⌈ω₁⌉_𝒮 = U`, by **66IV**.3
  have hpU : p ≤ U := by
    rw [ultracyclic_basic_3 p hp]
    refine (projSup_spec (fun q hq => by obtain ⟨ω, -, rfl⟩ := hq; exact hcarrier ω)).2.2
      U hUproj ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact le_trans (le_sub_comm.mp (relCoceil_le_npCarrier_compl hS ω))
      (hUub _ ⟨ω, hω, rfl⟩)
  -- `U ≤ ⋀_{ω₀} ⌈ω₀⌉_𝒮^⊥ ≤ ⋀_{ω₀} ⌈ω₀⌉^⊥ = p`, by **66IV**.3 at `p^⊥`
  have hUp : U ≤ p := by
    have hstep : (1 : A) - p ≤ 1 - U := by
      rw [ultracyclic_basic_3 (1 - p) hp.one_sub]
      refine (projSup_spec (fun q hq => by obtain ⟨ω, -, rfl⟩ := hq; exact hcarrier ω)).2.2
        (1 - U) hUproj.one_sub ?_
      rintro _ ⟨ω₀, hω₀, rfl⟩
      rw [sub_sub_cancel] at hω₀
      refine le_sub_comm.mp (hUleast _ (hcarrier ω₀).one_sub ?_)
      rintro _ ⟨ω₁, hω₁, rfl⟩
      exact le_trans (relCoceil_compl_le hS hp hcl ω₀ ω₁ hω₀ hω₁)
        (relCoceil_le_npCarrier_compl hS ω₀)
    exact (sub_le_sub_iff_left (1 : A)).mp hstep
  rw [le_antisymm hpU hUp, hUdef]
  exact (projSup_mem_of_np hS Q hQproj hQS zeroNP (fun q _ => rfl)).1


end VNSubalgebraClosure

section UsClosureSubalgebra

variable (S : StarSubalgebra ℂ A)

omit [VonNeumannAlgebra A] in
/-- The norm topology is finer than the ultrastrong topology. -/
theorem norm_le_ultrastrong : (inferInstance : TopologicalSpace A) ≤ ultrastrong A := by
  rw [ultrastrong]
  refine _root_.le_generateFrom ?_
  rintro U ⟨ω, b, ε, hε, rfl⟩
  have hlip : LipschitzWith (Real.toNNReal (omegaNorm A ω 1))
      (fun a : A => omegaNorm A ω (a - b)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 : |omegaNorm A ω (x - b) - omegaNorm A ω (y - b)|
        ≤ omegaNorm A ω ((x - b) - (y - b)) :=
      abs_omegaNorm_sub_omegaNorm_le ω (x - b) (y - b)
    have h2 : ((x - b) - (y - b)) = x - y := by abel
    rw [h2] at h1
    have h3 : omegaNorm A ω (x - y) ≤ ‖x - y‖ * omegaNorm A ω 1 :=
      omegaNorm_le_norm_mul ω (x - y)
    have h4 : (Real.toNNReal (omegaNorm A ω 1) : ℝ) = omegaNorm A ω 1 :=
      Real.coe_toNNReal _ (omegaNorm_nonneg ω 1)
    rw [Real.dist_eq, h4, dist_eq_norm, mul_comm]
    exact h1.trans h3
  exact isOpen_lt hlip.continuous continuous_const

omit [VonNeumannAlgebra A] in
theorem isClosed_of_isClosed_ultrastrong {C : Set A}
    (h : @IsClosed A (ultrastrong A) C) : IsClosed C :=
  h.mono norm_le_ultrastrong



omit [VonNeumannAlgebra A] in
private theorem us_add {x y : A} (hx : x ∈ @closure A (ultrastrong A) (S : Set A))
    (hy : y ∈ @closure A (ultrastrong A) (S : Set A)) :
    x + y ∈ @closure A (ultrastrong A) (S : Set A) := by
  rw [mem_usClosure_iff] at hx hy ⊢
  intro ω ε hε
  obtain ⟨z, hz, hz'⟩ := hx ω (ε / 2) (by positivity)
  obtain ⟨w, hw, hw'⟩ := hy ω (ε / 2) (by positivity)
  refine ⟨z + w, add_mem hz hw, ?_⟩
  have heq : z + w - (x + y) = (z - x) + (w - y) := by abel
  rw [heq]
  exact lt_of_le_of_lt (omegaNorm_add_le ω _ _) (by linarith)

omit [VonNeumannAlgebra A] in
private theorem us_smul (c : ℂ) {x : A} (hx : x ∈ @closure A (ultrastrong A) (S : Set A)) :
    c • x ∈ @closure A (ultrastrong A) (S : Set A) := by
  rw [mem_usClosure_iff] at hx ⊢
  intro ω ε hε
  obtain ⟨z, hz, hz'⟩ := hx ω (ε / (‖c‖ + 1)) (by positivity)
  refine ⟨c • z, SMulMemClass.smul_mem _ hz, ?_⟩
  have heq : c • z - c • x = c • (z - x) := by rw [smul_sub]
  rw [heq, omegaNorm_smul]
  have h0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : omegaNorm A ω (z - x) < ε / (‖c‖ + 1) := hz'
  have h2 : ‖c‖ * omegaNorm A ω (z - x) ≤ (‖c‖ + 1) * omegaNorm A ω (z - x) :=
    mul_le_mul_of_nonneg_right (by linarith) (omegaNorm_nonneg ω _)
  have h3 : (‖c‖ + 1) * omegaNorm A ω (z - x) < (‖c‖ + 1) * (ε / (‖c‖ + 1)) :=
    mul_lt_mul_of_pos_left h1 (by linarith)
  rw [mul_div_cancel₀ _ (by positivity : (‖c‖ : ℝ) + 1 ≠ 0)] at h3
  linarith

private theorem us_mul {x y : A} (hx : x ∈ @closure A (ultrastrong A) (S : Set A))
    (hy : y ∈ @closure A (ultrastrong A) (S : Set A)) :
    x * y ∈ @closure A (ultrastrong A) (S : Set A) := by
  rw [mem_usClosure_iff] at hx hy ⊢
  intro ω ε hε
  -- first approximate `y` (left multiplication by the *fixed* `x` is `‖x‖`-Lipschitz)
  obtain ⟨w, hw, hw'⟩ := hy ω (ε / (2 * (‖x‖ + 1))) (by positivity)
  -- then approximate `x` in the seminorm `‖·‖_{w*ω}`
  obtain ⟨z, hz, hz'⟩ := hx (conjNP w ω) (ε / 2) (by positivity)
  refine ⟨z * w, mul_mem hz hw, ?_⟩
  have heq : z * w - x * y = (z - x) * w + x * (w - y) := by noncomm_ring
  rw [heq]
  refine lt_of_le_of_lt (omegaNorm_add_le ω _ _) ?_
  have hA : omegaNorm A ω ((z - x) * w) = omegaNorm A (conjNP w ω) (z - x) :=
    omegaNorm_mul_right ω (z - x) w
  have hB : omegaNorm A ω (x * (w - y)) ≤ ‖x‖ * omegaNorm A ω (w - y) :=
    omegaNorm_mul_le ω x (w - y)
  have hC : ‖x‖ * omegaNorm A ω (w - y) ≤ (‖x‖ + 1) * omegaNorm A ω (w - y) :=
    mul_le_mul_of_nonneg_right (by linarith) (omegaNorm_nonneg ω _)
  have hD : (‖x‖ + 1) * omegaNorm A ω (w - y) < (‖x‖ + 1) * (ε / (2 * (‖x‖ + 1))) :=
    mul_lt_mul_of_pos_left hw' (by positivity)
  have hE : (‖x‖ + 1) * (ε / (2 * (‖x‖ + 1))) = ε / 2 := by
    field_simp
  rw [hE] at hD
  rw [hA]
  linarith

private theorem us_star {x : A} (hx : x ∈ @closure A (ultrastrong A) (S : Set A)) :
    star x ∈ @closure A (ultrastrong A) (S : Set A) := by
  -- the adjoint is *ultraweakly* continuous, and the ultrastrong closure of the
  -- convex set `S` is ultraweakly closed by **73VIII** (`ultraclosed`)
  refine mem_usClosure_of_mem_uwClosure (convex_starSubalgebraA S) ?_
  have hcont : @Continuous A A (ultraweak A) (ultraweak A) (fun a : A => star a) := by
    let _ : TopologicalSpace A := ultraweak A
    rw [ultraweak, continuous_iInf_rng]
    intro ω
    rw [continuous_induced_rng]
    have hform : ∀ a : A, (ω (star a) : ℂ) = star (ω a) := fun a => npFunctional_star ω a
    change Continuous fun a : A => (ω (star a) : ℂ)
    simp only [hform]
    exact continuous_star.comp (continuous_ultraweak_npFunctional ω)
  have hsub : ∀ a ∈ (S : Set A), star a ∈ @closure A (ultraweak A) (S : Set A) :=
    fun a ha => @subset_closure A (ultraweak A) (S : Set A) _ (star_mem ha)
  exact @closure_minimal A (ultraweak A) (S : Set A) _ hsub
    (@IsClosed.preimage A A (ultraweak A) (ultraweak A) _ hcont _
      (@isClosed_closure A (ultraweak A) (S : Set A))) x (usClosure_subset_uwClosure _ hx)

/-- The **ultrastrong closure of a C\*-subalgebra** of a von Neumann algebra
is again a star subalgebra.  (Asserted without proof in the thesis's proof of
**75VIII**, vn.tex:4597; multiplication is only *separately* ultrastrongly
continuous, which is enough, and the adjoint — which is *not* ultrastrongly
continuous, cf. **43II**.4 — is handled through the ultraweak topology and
**73VIII** `ultraclosed`.) -/
noncomputable def usClosureSubalgebra : StarSubalgebra ℂ A where
  carrier := @closure A (ultrastrong A) (S : Set A)
  mul_mem' := us_mul S
  add_mem' := us_add S
  one_mem' := @subset_closure A (ultrastrong A) (S : Set A) _ (one_mem S)
  zero_mem' := @subset_closure A (ultrastrong A) (S : Set A) _ (zero_mem S)
  algebraMap_mem' := fun r =>
    @subset_closure A (ultrastrong A) (S : Set A) _ (algebraMap_mem S r)
  star_mem' := us_star S

@[simp] theorem mem_usClosureSubalgebra {x : A} :
    x ∈ usClosureSubalgebra S ↔ x ∈ @closure A (ultrastrong A) (S : Set A) := Iff.rfl


/-- The ultrastrong closure of a C*-subalgebra is a von Neumann subalgebra:
it is norm-closed (the ultrastrong topology is coarser than the norm
topology) and closed under bounded directed suprema, because by **44XIV**
`vna_supremum_uslimit` such a supremum is the ultrastrong limit of its own
net. -/
theorem isVNSubalgebra_usClosureSubalgebra :
    IsVNSubalgebra A (usClosureSubalgebra S) where
  isClosed := isClosed_of_isClosed_ultrastrong (@isClosed_closure A (ultrastrong A) _)
  dirSup_mem := by
    intro D s hD hne hdir hlub
    have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨s, hlub.1⟩⟩
    have hlim := vna_supremum_uslimit D h3
    have heq : ((dirSup D h3 : selfAdjoint A) : A) = (s : A) := by
      rw [(isLUB_dirSup D h3).unique hlub]
    rw [heq] at hlim
    have : Nonempty ↥D := hne.to_subtype
    have : IsDirected ↥D (· ≤ ·) := ⟨fun x y => by
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x x.2 y y.2
      exact ⟨⟨z, hz⟩, hxz, hyz⟩⟩
    change (s : A) ∈ @closure A (ultrastrong A) (S : Set A)
    rw [mem_usClosure_iff]
    intro ω ε hε
    have hmem := hlim (ultrastrong_ball_mem_nhds ω ((s : selfAdjoint A) : A)
        (show (0 : ℝ) < ε / 2 by positivity))
    have hev : ∀ᶠ i : ↥D in atTop,
        omegaNorm A ω (((i : selfAdjoint A) : A) - ((s : selfAdjoint A) : A)) < ε / 2 := hmem
    obtain ⟨d, hd⟩ := hev.exists
    obtain ⟨z, hz, hz'⟩ :=
      (mem_usClosure_iff (S : Set A) _).mp (hD (d : selfAdjoint A) d.2) ω (ε / 2) (by positivity)
    refine ⟨z, hz, ?_⟩
    have := omegaNorm_sub_le ω z (((d : selfAdjoint A) : A)) ((s : selfAdjoint A) : A)
    have hd' : omegaNorm A ω (((d : selfAdjoint A) : A) - ((s : selfAdjoint A) : A)) < ε / 2 := hd
    linarith

end UsClosureSubalgebra

/-- **75VIII** (`vnsac`, vn.tex:4587, Theorem): a von Neumann subalgebra of
a von Neumann algebra is ultrastrongly and ultraweakly closed.

*Class 2 — different route in two places, and shorter than the thesis's.*
The thesis's argument runs `p = ⋁_{ω₁} ⌈ω₁⌉_𝒮 = ⋀_{ω₀} ⌈ω₀⌉_𝒮^⊥` and uses
(i) the *unstated* dual of **66IV**.3, `p = ⋀_ω ⌈ω⌉^⊥`, and (ii) the
relativised carriers `⌈ω⌉_𝒮`, which presuppose the von Neumann structure of
`𝒮`.  Neither is needed: complementing the second half of the display turns
it into **66IV**.3 applied to `p^⊥`, so only `⋁` and only `ultracyclic_basic_3`
occur; and `⌈ω⌉_𝒮^⊥` may be *defined* outright as the `projSup` of the
projections of `𝒮` annihilated by `ω` (`relCoceil`), whose two defining
properties come from `projSup_mem_of_np` — no von Neumann structure on `𝒮`
is transported.  The remaining unstated ingredient, "the ultrastrong closure
of `𝒮` is a von Neumann subalgebra", is `usClosureSubalgebra` /
`isVNSubalgebra_usClosureSubalgebra` above. -/
theorem vnsac (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    @IsClosed A (ultrastrong A) (S : Set A) ∧
      @IsClosed A (ultraweak A) (S : Set A) := by
  have hsub : @closure A (ultrastrong A) (S : Set A) ⊆ (S : Set A) := by
    intro a ha
    exact mem_of_isClosed_of_projections_subalgebra
      (isVNSubalgebra_usClosureSubalgebra S) (Subalgebra.toSubmodule S.toSubalgebra)
      hS.isClosed (fun p hp hpS => projection_mem_of_mem_usClosure hS hp hpS) ha
  have hus : @IsClosed A (ultrastrong A) (S : Set A) :=
    (@closure_subset_iff_isClosed A (ultrastrong A) (S : Set A)).mp hsub
  exact ⟨hus, ultraclosed _ (convex_starSubalgebraA S) hus⟩

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

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- Auxiliary for **77I**: `‖·‖_ω` transports along a ∗-homomorphism —
`‖a‖_{ω∘ρ} = ‖ρ(a)‖_ω`.  Stated for an arbitrary functional given
pointwise, since both directions are used. -/
theorem omegaNorm_comp_starAlgHom (ρ : A →⋆ₐ[ℂ] B) (ω : NPFunctional A)
    (ν : NPFunctional B) (hων : ∀ a : A, ω a = ν (ρ a)) (a : A) :
    omegaNorm A ω a = omegaNorm B ν (ρ a) := by
  rw [omegaNorm, omegaNorm, hων, map_mul, map_star]

section Complete

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **77I** (`vn-complete`, vn.tex:4808, Theorem), part 1: a von Neumann
algebra is ultrastrongly complete. -/
theorem vn_complete_1 {ι : Type*} (l : Filter ι) [l.NeBot] (x : ι → A)
    (hcauchy : ∀ ω : NPFunctional A,
      Tendsto (fun p : ι × ι => omegaNorm A ω (x p.1 - x p.2)) (l ×ˢ l)
        (𝓝 0)) :
    ∃ a : A, USTendsto x l a := by
  -- the thesis's argument: transport along `ρ_Ω`, complete inside `B(H_Ω)`
  -- by **76I**, land back in `ρ_Ω(A)` because it is ultrastrongly closed
  -- (**75VIII**), and come back because every np-functional of `A` is a
  -- vector functional in this representation (**48V**).
  obtain ⟨H, _, _, _, ρ, hinj, hn, hvec⟩ := exists_faithful_normal_rep_vectors A
  have hcau : ∀ ν : NPFunctional (H →L[ℂ] H),
      Tendsto (fun p : ι × ι => omegaNorm _ ν (ρ (x p.1) - ρ (x p.2))) (l ×ˢ l)
        (𝓝 0) := by
    intro ν
    refine (hcauchy (compNP (starAlgHomP ρ) hn ν)).congr fun p => ?_
    rw [omegaNorm_comp_starAlgHom ρ _ ν (fun a => rfl), map_sub]
  obtain ⟨T₀, hT₀⟩ := bh_us_complete l (fun i => ρ (x i)) hcau
  -- `T₀` lies in the (ultrastrongly closed) range of `ρ`
  have hmem : T₀ ∈ (ρ.range : Set (H →L[ℂ] H)) := by
    let _ : TopologicalSpace (H →L[ℂ] H) := ultrastrong (H →L[ℂ] H)
    exact IsClosed.mem_of_tendsto
      (vnsac ρ.range (isVNSubalgebra_range ρ hinj hn)).1 hT₀
      (Eventually.of_forall fun i => ⟨x i, rfl⟩)
  obtain ⟨a, ha⟩ : ∃ a : A, ρ a = T₀ := hmem
  refine ⟨a, (usTendsto_iff x l a).mpr fun ω => ?_⟩
  obtain ⟨ξ, hξ⟩ := hvec ω
  have key : ∀ b : A, omegaNorm A ω b = omegaNorm (H →L[ℂ] H) (vectorNP ξ) (ρ b) :=
    omegaNorm_comp_starAlgHom ρ ω (vectorNP ξ) fun b => by
      rw [hξ, vectorNP_apply]
  refine ((usTendsto_iff (fun i => ρ (x i)) l T₀).mp hT₀ (vectorNP ξ)).congr
    fun i => ?_
  rw [key, map_sub, ha]

/-- **77I** (`vn-complete`, vn.tex:4808, Theorem), part 2: a von Neumann
algebra is bounded ultraweakly complete. -/
theorem vn_complete_2 {ι : Type*} (l : Filter ι) [l.NeBot] (x : ι → A)
    (hbdd : ∃ C : ℝ, ∀ i, ‖x i‖ ≤ C)
    (hcauchy : ∀ ω : NPFunctional A, Cauchy (l.map fun i => ω (x i))) :
    ∃ a : A, UWTendsto x l a := by
  -- same transport as in `vn_complete_1`, now through **76III** and the
  -- *ultraweak* half of **75VIII**
  obtain ⟨H, _, _, _, ρ, hinj, hn, hvec⟩ := exists_faithful_normal_rep_vectors A
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨T₀, hT₀⟩ := bh_bounded_uw_complete l (fun i => ρ (x i))
    ⟨C, fun i => by rw [NonUnitalStarAlgHom.norm_map ρ hinj]; exact hC i⟩
    fun ν => hcauchy (compNP (starAlgHomP ρ) hn ν)
  have hmem : T₀ ∈ (ρ.range : Set (H →L[ℂ] H)) := by
    let _ : TopologicalSpace (H →L[ℂ] H) := ultraweak (H →L[ℂ] H)
    exact IsClosed.mem_of_tendsto
      (vnsac ρ.range (isVNSubalgebra_range ρ hinj hn)).2 hT₀
      (Eventually.of_forall fun i => ⟨x i, rfl⟩)
  obtain ⟨a, ha⟩ : ∃ a : A, ρ a = T₀ := hmem
  refine ⟨a, (uwTendsto_iff x l a).mpr fun ω => ?_⟩
  obtain ⟨ξ, hξ⟩ := hvec ω
  have h := (uwTendsto_iff (fun i => ρ (x i)) l T₀).mp hT₀ (vectorNP ξ)
  rw [← ha] at h
  simpa only [hξ, vectorNP_apply] using h

/-- **77III** (`vn-ball-compact`, vn.tex:4847, Theorem): the unit ball of a
von Neumann algebra is ultraweakly compact. -/
theorem vn_ball_compact :
    @IsCompact A (ultraweak A) (Metric.closedBall (0 : A) 1) := by
  -- The thesis embeds `(A)₁` into `ℂ^Ω` and combines Tychonoff with
  -- **77I**.2.  We run the same argument in its ultrafilter form: an
  -- ultrafilter on `(A)₁` pushes to a *convergent* ultrafilter along each
  -- np-functional (Heine–Borel in `ℂ` replaces Tychonoff), so **77I**.2
  -- supplies its ultraweak limit, which lies in `(A)₁` because the ball is
  -- ultraweakly closed (**44XI**.3 plus **73VIII** `ultraclosed`).
  let _ : TopologicalSpace A := ultraweak A
  have hballclosed : IsClosed (Metric.closedBall (0 : A) 1) :=
    ultraclosed _ (convex_closedBall (0 : A) 1) vn_positive_basic_3
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro F hF
  have hrange : Set.range (Subtype.val : ↥(Metric.closedBall (0 : A) 1) → A) ∈
      (F : Filter A) := by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq]
    exact le_principal_iff.mp hF
  set U : Ultrafilter ↥(Metric.closedBall (0 : A) 1) :=
    Ultrafilter.comap (m := Subtype.val) F Subtype.val_injective hrange with hU
  have hmap : Filter.map Subtype.val (U : Filter ↥(Metric.closedBall (0 : A) 1))
      = (F : Filter A) := by
    rw [hU, Ultrafilter.coe_comap]
    exact Filter.map_comap_of_mem hrange
  have hcau : ∀ ω : NPFunctional A,
      Cauchy ((U : Filter ↥(Metric.closedBall (0 : A) 1)).map
        fun i : ↥(Metric.closedBall (0 : A) 1) => ω (i : A)) := by
    intro ω
    obtain ⟨C, hC⟩ := PositiveLinearMap.exists_norm_apply_le ω.toPositiveLinearMap
    refine cauchy_map_iff_exists_tendsto.mpr ?_
    have hin : (Metric.closedBall (0 : ℂ) C) ∈
        (U.map (fun i : ↥(Metric.closedBall (0 : A) 1) => ω (i : A)) :
          Filter ℂ) := by
      rw [Ultrafilter.coe_map, Filter.mem_map]
      refine Filter.Eventually.of_forall
        fun i : ↥(Metric.closedBall (0 : A) 1) => mem_closedBall_zero_iff.mpr ?_
      refine (hC _).trans ?_
      simpa using mul_le_of_le_one_right (by positivity)
        (mem_closedBall_zero_iff.mp i.2)
    obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
      (U.map fun i : ↥(Metric.closedBall (0 : A) 1) => ω (i : A))
      (le_principal_iff.mpr hin)
    exact ⟨z, hz⟩
  obtain ⟨a, ha⟩ := vn_complete_2 (U : Filter ↥(Metric.closedBall (0 : A) 1))
    (fun i => (i : A)) ⟨1, fun i => mem_closedBall_zero_iff.mp i.2⟩ hcau
  have hmem : a ∈ Metric.closedBall (0 : A) 1 :=
    hballclosed.mem_of_tendsto ha (Filter.Eventually.of_forall fun i => i.2)
  exact ⟨a, hmem, hmap ▸ ha⟩

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
