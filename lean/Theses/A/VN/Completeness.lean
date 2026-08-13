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

/-- `‖bc‖_ω ≤ ‖b‖ ‖c‖_ω`: conjugate `b* b ≤ ‖b‖²·1` by `c` and apply `ω`.
(The submultiplicativity behind **72III**.1b; cf. cstar.tex 30IV.) -/
private theorem omegaNorm_mul_le (ω : NPFunctional A) (b c : A) :
    omegaNorm A ω (b * c) ≤ ‖b‖ * omegaNorm A ω c := by
  have hsmul : ∀ (r : ℝ) (x : A), (r : ℝ) • x = ((r : ℂ)) • x := fun r x => by
    rw [← IsScalarTower.algebraMap_smul ℂ r x, Complex.coe_algebraMap]
  have hn : ‖star b * b‖ = ‖b‖ * ‖b‖ := CStarRing.norm_star_mul_self
  have h1 : star b * b ≤ (‖b‖ * ‖b‖ : ℝ) • (1 : A) := by
    have h := le_norm_smul_one (star_mul_self_nonneg b)
    rwa [hn] at h
  have h2 : star (b * c) * (b * c) ≤ (‖b‖ * ‖b‖ : ℝ) • (star c * c) := by
    have h := star_left_conjugate_le_conjugate h1 c
    have e1 : star c * (star b * b) * c = star (b * c) * (b * c) := by
      rw [star_mul]; noncomm_ring
    have e2 : star c * ((‖b‖ * ‖b‖ : ℝ) • (1 : A)) * c
        = (‖b‖ * ‖b‖ : ℝ) • (star c * c) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one]
    rwa [e1, e2] at h
  have hmap : ∀ (r : ℝ) (x : A), ω ((r : ℝ) • x) = (r : ℂ) * ω x := fun r x => by
    rw [hsmul r x]
    exact map_smul ω.toPositiveLinearMap (r : ℂ) x
  have h3 : (ω (star (b * c) * (b * c))).re
      ≤ (‖b‖ * ‖b‖) * (ω (star c * c)).re := by
    have h := npFunctional_mono ω h2
    rw [hmap] at h
    have h4 := (Complex.le_def.mp h).1
    simpa using h4
  rw [omegaNorm, omegaNorm]
  calc Real.sqrt (ω (star (b * c) * (b * c))).re
      ≤ Real.sqrt ((‖b‖ * ‖b‖) * (ω (star c * c)).re) := Real.sqrt_le_sqrt h3
    _ = ‖b‖ * Real.sqrt (ω (star c * c)).re := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg b)]

/-! ### Auxiliary: the np-functionals form a cone

`Theses.NPFunctional` carries no algebraic structure, but the proofs of
**72IV** and **72V** need to replace a *finite family* of np-functionals by a
single one dominating all of them.  Positivity and linearity are inherited
from `A →ₚ[ℂ] ℂ`; only normality has to be checked, and for a sum it is the
standard "`sup` of a sum over a directed set is the sum of the `sup`s". -/

/-- The zero np-functional. -/
private noncomputable def zeroNP : NPFunctional A where
  toPositiveLinearMap := 0
  preservesDirSups' := by
    intro D s hne hdir _
    have h : (fun d : selfAdjoint A => (0 : A →ₚ[ℂ] ℂ) (d : A)) '' D = {(0 : ℂ)} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hne.choose, hne.choose_spec, rfl⟩, ?_⟩
      rintro _ ⟨d, _, rfl⟩
      rfl
    rw [h]
    exact isLUB_singleton

/-- The sum of two np-functionals. -/
private noncomputable def addNP (ω₁ ω₂ : NPFunctional A) : NPFunctional A where
  toPositiveLinearMap := ω₁.toPositiveLinearMap + ω₂.toPositiveLinearMap
  preservesDirSups' := by
    intro D s hne hdir hlub
    have h₁ := ω₁.preservesDirSups' D s hne hdir hlub
    have h₂ := ω₂.preservesDirSups' D s hne hdir hlub
    -- both functionals are real on self-adjoint elements
    have him₁ : ∀ d : selfAdjoint A, (ω₁ (d : A)).im = 0 := fun d =>
      npFunctional_im_eq_zero ω₁ d.2
    have him₂ : ∀ d : selfAdjoint A, (ω₂ (d : A)).im = 0 := fun d =>
      npFunctional_im_eq_zero ω₂ d.2
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact add_le_add (h₁.1 ⟨d, hd, rfl⟩) (h₂.1 ⟨d, hd, rfl⟩)
    · intro z hz
      obtain ⟨d₀, hd₀⟩ := hne
      have hz₀ : ω₁ (d₀ : A) + ω₂ (d₀ : A) ≤ z := hz ⟨d₀, hd₀, rfl⟩
      have hzim : z.im = 0 := by
        have := (Complex.le_def.mp hz₀).2
        simp only [Complex.add_im, him₁, him₂, add_zero] at this
        exact this.symm
      -- `ε`-approximation of each supremum separately, then directedness
      have ex : ∀ (ω : NPFunctional A), IsLUB ((fun d : selfAdjoint A => ω (d : A)) '' D)
          (ω (s : A)) → ∀ ε : ℝ, 0 < ε → ∃ d ∈ D, (ω (s : A)).re - ε < (ω (d : A)).re := by
        intro ω hω ε hε
        by_contra hcon
        push_neg at hcon
        have hub : (ω (s : A)) ≤ (((ω (s : A)).re - ε : ℝ) : ℂ) := by
          refine hω.2 ?_
          rintro _ ⟨d, hd, rfl⟩
          exact Complex.le_def.mpr ⟨by simpa using hcon d hd,
            by simp [npFunctional_im_eq_zero ω d.2]⟩
        have := (Complex.le_def.mp hub).1
        simp at this
        linarith
      have hre : (ω₁ (s : A)).re + (ω₂ (s : A)).re ≤ z.re := by
        by_contra hcon
        push_neg at hcon
        set ε : ℝ := ((ω₁ (s : A)).re + (ω₂ (s : A)).re - z.re) / 2 with hεdef
        have hε : 0 < ε := by rw [hεdef]; linarith
        obtain ⟨d₁, hd₁, hlt₁⟩ := ex ω₁ h₁ ε hε
        obtain ⟨d₂, hd₂, hlt₂⟩ := ex ω₂ h₂ ε hε
        obtain ⟨d, hd, hle₁, hle₂⟩ := hdir d₁ hd₁ d₂ hd₂
        have m₁ : (ω₁ (d₁ : A)).re ≤ (ω₁ (d : A)).re :=
          (Complex.le_def.mp (npFunctional_mono ω₁ (Subtype.coe_le_coe.mpr hle₁))).1
        have m₂ : (ω₂ (d₂ : A)).re ≤ (ω₂ (d : A)).re :=
          (Complex.le_def.mp (npFunctional_mono ω₂ (Subtype.coe_le_coe.mpr hle₂))).1
        have hub : ω₁ (d : A) + ω₂ (d : A) ≤ z := hz ⟨d, hd, rfl⟩
        have hub' := (Complex.le_def.mp hub).1
        simp only [Complex.add_re] at hub'
        rw [hεdef] at hlt₁ hlt₂
        linarith
      show ω₁ (s : A) + ω₂ (s : A) ≤ z
      refine Complex.le_def.mpr ⟨?_, ?_⟩
      · simpa using hre
      · simp [him₁ s, him₂ s, hzim]

@[simp] private theorem zeroNP_apply (a : A) : zeroNP a = 0 := rfl

@[simp] private theorem addNP_apply (ω₁ ω₂ : NPFunctional A) (a : A) :
    addNP ω₁ ω₂ a = ω₁ a + ω₂ a := rfl

/-- `‖·‖_ω₁ ≤ ‖·‖_{ω₁+ω₂}`. -/
private theorem omegaNorm_le_addNP (ω₁ ω₂ : NPFunctional A) (a : A) :
    omegaNorm A ω₁ a ≤ omegaNorm A (addNP ω₁ ω₂) a := by
  rw [omegaNorm, omegaNorm]
  refine Real.sqrt_le_sqrt ?_
  have h : (0 : ℂ) ≤ ω₂ (star a * a) := npFunctional_nonneg ω₂ (star_mul_self_nonneg a)
  have := (Complex.le_def.mp h).1
  simp only [addNP_apply, Complex.add_re]
  simpa using this

/-- `‖·‖_ω₂ ≤ ‖·‖_{ω₁+ω₂}`. -/
private theorem omegaNorm_le_addNP' (ω₁ ω₂ : NPFunctional A) (a : A) :
    omegaNorm A ω₂ a ≤ omegaNorm A (addNP ω₁ ω₂) a := by
  rw [omegaNorm, omegaNorm]
  refine Real.sqrt_le_sqrt ?_
  have h : (0 : ℂ) ≤ ω₁ (star a * a) := npFunctional_nonneg ω₁ (star_mul_self_nonneg a)
  have := (Complex.le_def.mp h).1
  simp only [addNP_apply, Complex.add_re]
  simpa using this

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
      ‖bStarOmega A (b n) ω a - f a‖ ≤ ε * ‖a‖ :=
  sorry

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

/-- **72V** (`normal-functionals-lemma`, vn.tex:3887, Lemma): for an
np-functional `ω` and a linear `f : A → ℂ` the following are equivalent:
(1) `|f(a)| ≤ B` on some `‖·‖_ω`-ball of radius `δ > 0`;
(2) `|f(a)| ≤ B ‖a‖_ω` for some `B > 0`;
(3) `f = [b, ·]_ω` for some `b` in the Hilbert space completion `H_ω` of
`A` for the inner product `[a, c]_ω = ω(a* c)` (rendered by an existential
completion `φ : A → H`);
(4) `f = f₀ + i f₁ - f₂ - i f₃` for np-functionals `f_k` dominated by
`B·ω` on the positive cone. -/
theorem normal_functionals_lemma (ω : NPFunctional A) (f : A →ₗ[ℂ] ℂ) :
    List.TFAE
      [∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
        ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ B,
       ∃ B : ℝ, 0 < B ∧ ∀ a : A, ‖f a‖ ≤ B * omegaNorm A ω a,
       ∃ (ι : Type u) (φ : A →ₗ[ℂ] lp (fun _ : ι => ℂ) 2),
        DenseRange ⇑φ ∧
        (∀ a c : A, ⟪φ a, φ c⟫ = ω (star a * c)) ∧
        ∃ b : lp (fun _ : ι => ℂ) 2, ∀ a : A, f a = ⟪b, φ a⟫,
       ∃ (g : Fin 4 → NPFunctional A) (B : ℝ), 0 < B ∧
        (∀ a : A, f a = g 0 a + Complex.I * g 1 a - g 2 a -
          Complex.I * g 3 a) ∧
        ∀ (k : Fin 4) (a : A), 0 ≤ a → (g k a).re ≤ B * (ω a).re] :=
  sorry

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
       ∃ ω : NPFunctional A, ∀ a : A, ‖f a‖ ≤ omegaNorm A ω a] :=
  sorry

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

/-- **73VIII** (`ultraclosed`, vn.tex:4160, Exercise): an ultrastrongly
closed *convex* subset of a von Neumann algebra is ultraweakly closed
(hence the ultrastrong and ultraweak closures of convex sets coincide).
The exercise's enumerated items are steps of the proof and are not
converted separately. -/
theorem ultraclosed [VonNeumannAlgebra A] (K : Set A) (hconv : Convex ℝ K)
    (hK : @IsClosed A (ultrastrong A) K) : @IsClosed A (ultraweak A) K :=
  sorry

/-! ## Parsec 740: Kaplansky's density theorem -/

section Kaplansky

variable [VonNeumannAlgebra A]

/-- **74I** (`proto-kaplansky`, vn.tex:4224, Proposition): for a continuous
`f : ℝ → ℝ` with `f(t) = O(t)`, the map `a ↦ f(a)` (continuous functional
calculus) is ultrastrongly continuous on the self-adjoint part of a von
Neumann algebra. -/
theorem proto_kaplansky (f : ℝ → ℝ) (hf : Continuous f)
    (hO : ∃ (n : ℕ) (b : ℝ), ∀ t : ℝ, (n : ℝ) ≤ |t| → |f t| ≤ b * |t|) :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => cfc f a)
      {a : A | IsSelfAdjoint a} :=
  sorry

/-- **74III** (`abs-us-cont`, vn.tex:4331, Corollary): `a ↦ |a|` is
ultrastrongly continuous on the self-adjoint part of a von Neumann
algebra. -/
theorem abs_us_cont :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A)
      (fun a => cfc (fun t : ℝ => |t|) a) {a : A | IsSelfAdjoint a} :=
  sorry

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

/-- **76I** (`bh-us-complete`, vn.tex:4641, Proposition): `B(H)` is
ultrastrongly complete: every ultrastrongly Cauchy net converges
ultrastrongly. -/
theorem bh_us_complete {ι : Type*} (l : Filter ι) [l.NeBot]
    (T : ι → H →L[ℂ] H)
    (hcauchy : ∀ ω : NPFunctional (H →L[ℂ] H),
      Tendsto (fun p : ι × ι => omegaNorm _ ω (T p.1 - T p.2)) (l ×ˢ l)
        (𝓝 0)) :
    ∃ T₀ : H →L[ℂ] H, USTendsto T l T₀ :=
  sorry

/-- **76III** (`bh-bounded-uw-complete`, vn.tex:4744, Proposition): `B(H)`
is bounded ultraweakly complete: every norm-bounded ultraweakly Cauchy net
converges ultraweakly. -/
theorem bh_bounded_uw_complete {ι : Type*} (l : Filter ι) [l.NeBot]
    (T : ι → H →L[ℂ] H) (hbdd : ∃ C : ℝ, ∀ i, ‖T i‖ ≤ C)
    (hcauchy : ∀ ω : NPFunctional (H →L[ℂ] H),
      Cauchy (l.map fun i => ω (T i))) :
    ∃ T₀ : H →L[ℂ] H, UWTendsto T l T₀ :=
  sorry

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
