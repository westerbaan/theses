/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines 1–2182.

  §The Basics
    Definition and Counterexamples  (parsec 420: Kadison's definition — in
                                     `Theses.Common` — and the ultraweak and
                                     ultrastrong topologies; parsec 430:
                                     counterexamples in B(ℓ²))
    Elementary Theory               (parsecs 440–460: suprema vs.
                                     multiplication, normality of positive
                                     maps, ultraweak/ultrastrong continuity)
    parsec 470: the categories W*_miu and W*_cpsu, products, equalisers
    parsec 480: the normal Gelfand–Naimark theorem
  §Examples
    parsec 490: matrices over a von Neumann algebra
    parsecs 500–540: commutative von Neumann algebras, L^∞(X), meagre sets,
                     extremal disconnectedness, the classification of
                     commutative von Neumann algebras with a faithful
                     np-functional

See CONVENTIONS.md for the
numbering (**42I** = parsec 420, point 10) and naming conventions.

Encoding of the ultraweak/ultrastrong topologies: they are *defs* (not
instances), so they never clash with the norm topology; statements mention
them explicitly, via `@`-application (e.g. `@IsClosed A (ultraweak A) C`) or
via the convergence predicates `UWTendsto`/`USTendsto`.
-/
import Theses.Common
import Theses.A.CStar.Basic
import Theses.A.CStar.TowardsVN
import Theses.A.CStar.Representation
import Theses.A.CStar.Matrices

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra ENNReal symmDiff
open Filter Topology MeasureTheory Theses Theses.A.CStar

-- The topologies `ultraweak`/`ultrastrong` (and the σ-algebra
-- `almostClopenMS`) are *intentionally* plain defs, not instances:
set_option warn.classDefReducibility false

universe u

namespace Theses.A.VN

/-! ## Parsec 420 (`vna`): Kadison's definition; the two topologies

**42I** (`vna`, vn.tex:166, Definition (Kadison)): the definition of a von
Neumann algebra is formalized in `Theses.Common` as the class
`Theses.VonNeumannAlgebra`.

**42II** (`def-np-functional`, vn.tex:196): normal positive functionals are
`Theses.NPFunctional` (with `Theses.PreservesDirSups` for normality).

**42IIa** (vn.tex:203): "n" abbreviates "normal" — nothing to formalize.

**42IV** (vn.tex:246, Remark): on the interplay of the two topologies —
nothing to formalize. -/

section Topologies

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (A) in
/-- **42III** (vn.tex:208): the seminorm `‖a‖_ω = ω(a*a)^½` associated to an
np-functional `ω` (cf. `omega-norm-basic`, cstar.tex 30IV). -/
noncomputable def omegaNorm (ω : NPFunctional A) (a : A) : ℝ :=
  Real.sqrt (ω (star a * a)).re

/-! ### Auxiliary: `‖·‖_ω` is the GNS seminorm

The seminorm `‖a‖_ω = ω(a*a)^½` of `42III` is literally the norm of the GNS
pre-Hilbert space `PositiveLinearMap.PreGNS ω` that Mathlib builds from a
positive functional (cf. cstar.tex 30II–30IV, `state-inner-product` and
`omega-norm-basic`, where the thesis constructs the same inner product).  All
the seminorm properties used below are read off from that identification. -/

/-- `‖a‖_ω` is the GNS-norm of `a` (`Theses.A.CStar.omega_norm_basic`, i.e.
cstar.tex 30IV, is the same observation). -/
theorem omegaNorm_eq_norm (ω : NPFunctional A) (a : A) :
    omegaNorm A ω a =
      ‖(ω.toPositiveLinearMap.toPreGNS a : ω.toPositiveLinearMap.PreGNS)‖ :=
  rfl

theorem omegaNorm_nonneg (ω : NPFunctional A) (a : A) : 0 ≤ omegaNorm A ω a := by
  rw [omegaNorm_eq_norm]; exact norm_nonneg _

@[simp] theorem omegaNorm_zero (ω : NPFunctional A) : omegaNorm A ω 0 = 0 := by
  rw [omegaNorm_eq_norm, map_zero, norm_zero]

theorem omegaNorm_add_le (ω : NPFunctional A) (a b : A) :
    omegaNorm A ω (a + b) ≤ omegaNorm A ω a + omegaNorm A ω b := by
  simp only [omegaNorm_eq_norm, map_add]
  exact norm_add_le _ _

@[simp] theorem omegaNorm_neg (ω : NPFunctional A) (a : A) :
    omegaNorm A ω (-a) = omegaNorm A ω a := by
  simp only [omegaNorm_eq_norm, map_neg]
  exact norm_neg _

/-- `‖c • a‖_ω = |c| ‖a‖_ω`: `‖·‖_ω` is literally the norm of the GNS
pre-Hilbert space, which is a `ℂ`-vector space. -/
theorem omegaNorm_smul (ω : NPFunctional A) (c : ℂ) (a : A) :
    omegaNorm A ω (c • a) = ‖c‖ * omegaNorm A ω a := by
  simp only [omegaNorm_eq_norm, map_smul, norm_smul]

theorem omegaNorm_sub_le (ω : NPFunctional A) (a b c : A) :
    omegaNorm A ω (a - c) ≤ omegaNorm A ω (a - b) + omegaNorm A ω (b - c) := by
  simp only [omegaNorm_eq_norm, map_sub]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

omit [StarOrderedRing A] in
@[simp] theorem omegaNorm_one (ω : NPFunctional A) :
    omegaNorm A ω 1 = Real.sqrt (ω 1).re := by
  rw [omegaNorm, star_one, one_mul]

/-- Kadison's inequality (cstar.tex 30IV, `omega-norm-basic`, part 1) in the
form `|ω(u* v)| ≤ ‖u‖_ω ‖v‖_ω`: it is Cauchy–Schwarz in the GNS space. -/
theorem norm_apply_star_mul_le (ω : NPFunctional A) (u v : A) :
    ‖ω (star u * v)‖ ≤ omegaNorm A ω u * omegaNorm A ω v := by
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (ω.toPositiveLinearMap.toPreGNS u) (ω.toPositiveLinearMap.toPreGNS v)
  have hi : (⟪ω.toPositiveLinearMap.toPreGNS u,
      ω.toPositiveLinearMap.toPreGNS v⟫ : ℂ) = ω (star u * v) := rfl
  rw [hi, ← omegaNorm_eq_norm, ← omegaNorm_eq_norm] at h
  exact h

omit [StarOrderedRing A] in
/-- `‖·‖_ω` is monotone in `u* u`. -/
theorem omegaNorm_le_omegaNorm (ω : NPFunctional A) {u v : A}
    (h : star u * u ≤ star v * v) : omegaNorm A ω u ≤ omegaNorm A ω v := by
  rw [omegaNorm, omegaNorm]
  exact Real.sqrt_le_sqrt
    (Complex.le_def.mp (ω.toPositiveLinearMap.monotone h)).1

/-- `a ≤ ‖a‖·1` for positive `a` (cstar.tex 24-ish; stated here because it is
needed for **44XIV**). -/
theorem le_norm_smul_one {a : A} (ha : 0 ≤ a) : a ≤ (‖a‖ : ℝ) • (1 : A) := by
  rcases eq_or_lt_of_le (norm_nonneg a) with hn | hn
  · simp [norm_eq_zero.mp hn.symm]
  · have h1 : ‖(‖a‖ : ℝ)⁻¹ • a‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hn)]
    have h2 : (‖a‖ : ℝ)⁻¹ • a ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _
        (smul_nonneg (by positivity) ha)).mp h1
    have h3 := smul_le_smul_of_nonneg_left h2 hn.le
    simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hn)] using h3

/-- `a² ≤ ‖a‖·a` for positive `a` (conjugate `a ≤ ‖a‖·1` by `√a`). -/
theorem mul_self_le_norm_smul {a : A} (ha : 0 ≤ a) :
    a * a ≤ (‖a‖ : ℝ) • a := by
  have hsq : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha
  have hst : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have h := star_left_conjugate_le_conjugate (le_norm_smul_one ha) (CFC.sqrt a)
  rw [hst] at h
  have e1 : CFC.sqrt a * a * CFC.sqrt a = a * a := by
    have step : CFC.sqrt a * (CFC.sqrt a * CFC.sqrt a) * CFC.sqrt a
        = CFC.sqrt a * CFC.sqrt a * (CFC.sqrt a * CFC.sqrt a) := by noncomm_ring
    rw [hsq] at step
    exact step
  have e2 : CFC.sqrt a * ((‖a‖ : ℝ) • (1 : A)) * CFC.sqrt a = (‖a‖ : ℝ) • a := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hsq]
  rwa [e1, e2] at h

/-- The estimate behind **44III** and **44VII**: for `0 ≤ x`,
`|ω(xa)| = |ω(√x · √x a)| ≤ ‖√x‖_ω ‖√x a‖_ω = ω(x)^½ ω(a* x a)^½`. -/
theorem norm_apply_mul_le_of_nonneg (ω : NPFunctional A) {x : A} (hx : 0 ≤ x)
    (a : A) :
    ‖ω (x * a)‖ ≤
      Real.sqrt (ω x).re * Real.sqrt (ω (star a * x * a)).re := by
  have hu0 : (0 : A) ≤ CFC.sqrt x := CFC.sqrt_nonneg x
  have husa : star (CFC.sqrt x) = CFC.sqrt x :=
    (IsSelfAdjoint.of_nonneg hu0).star_eq
  have huu : CFC.sqrt x * CFC.sqrt x = x := CFC.sqrt_mul_sqrt_self x hx
  have h1 : star (CFC.sqrt x) * (CFC.sqrt x * a) = x * a := by
    rw [husa, ← mul_assoc, huu]
  have h2 : omegaNorm A ω (CFC.sqrt x) = Real.sqrt (ω x).re := by
    rw [omegaNorm, husa, huu]
  have h3 : omegaNorm A ω (CFC.sqrt x * a)
      = Real.sqrt (ω (star a * x * a)).re := by
    rw [omegaNorm, star_mul, husa]
    congr 3
    rw [mul_assoc, ← mul_assoc (CFC.sqrt x), huu, ← mul_assoc]
  calc ‖ω (x * a)‖ = ‖ω (star (CFC.sqrt x) * (CFC.sqrt x * a))‖ := by rw [h1]
    _ ≤ omegaNorm A ω (CFC.sqrt x) * omegaNorm A ω (CFC.sqrt x * a) :=
        norm_apply_star_mul_le ω _ _
    _ = _ := by rw [h2, h3]

/-- An np-functional is real on self-adjoint elements (it is involution
preserving by cstar.tex 10IV, `cstar-p-implies-i`). -/
theorem npFunctional_im_eq_zero (ω : NPFunctional A) {a : A}
    (ha : IsSelfAdjoint a) : (ω a).im = 0 := by
  have h := map_star ω.toPositiveLinearMap a
  rw [ha.star_eq] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- Transfer of a supremum of (a nonempty set of) real complex numbers from
`ℂ` with the `ComplexOrder` to `ℝ` — the bridge between normality of an
np-functional and convergence of the corresponding net of reals. -/
theorem isLUB_re_of_isLUB {S : Set ℂ} {z : ℂ}
    (hreal : ∀ w ∈ S, w.im = 0) (h : IsLUB S z) :
    IsLUB (Complex.re '' S) z.re := by
  constructor
  · rintro r ⟨w, hw, rfl⟩
    exact (Complex.le_def.mp (h.1 hw)).1
  · intro r hr
    have hz : z ≤ (r : ℂ) := h.2 fun w hw => Complex.le_def.mpr
      ⟨hr ⟨w, hw, rfl⟩, by rw [hreal w hw, Complex.ofReal_im]⟩
    simpa using (Complex.le_def.mp hz).1

/-- Cauchy–Schwarz for `‖·‖_ω`, i.e. **43I**.1 without the (unused) von
Neumann hypothesis: `|ω(a)| = |[1,a]_ω| ≤ ‖1‖_ω ‖a‖_ω = ‖a‖_ω ω(1)^½`. -/
theorem norm_apply_le_omegaNorm (ω : NPFunctional A) (a : A) :
    ‖ω a‖ ≤ omegaNorm A ω a * Real.sqrt (ω 1).re := by
  have h := norm_apply_star_mul_le ω 1 a
  rw [star_one, one_mul, omegaNorm_one, mul_comm] at h
  exact h

variable (A) in
/-- **42III** (vn.tex:208): the **ultraweak topology** on a von Neumann
algebra `A`: the least topology making every np-functional `ω : A → ℂ`
continuous.  Deliberately a `def`, not an instance. -/
noncomputable def ultraweak : TopologicalSpace A :=
  ⨅ ω : NPFunctional A, TopologicalSpace.induced (fun a => ω a) inferInstance

variable (A) in
/-- **42III** (vn.tex:208): the **ultrastrong topology** on a von Neumann
algebra `A`: the topology generated by the "balls"
`{a | ‖a - b‖_ω < ε}` of the seminorms `‖·‖_ω` associated to the
np-functionals.  Deliberately a `def`, not an instance. -/
noncomputable def ultrastrong : TopologicalSpace A :=
  TopologicalSpace.generateFrom
    {U : Set A | ∃ (ω : NPFunctional A) (b : A) (ε : ℝ), 0 < ε ∧
      U = {a : A | omegaNorm A ω (a - b) < ε}}

/-- Convergence with respect to the ultraweak topology (encoding used
throughout these files). -/
def UWTendsto {ι : Type*} (x : ι → A) (l : Filter ι) (a : A) : Prop :=
  Tendsto x l (@nhds A (ultraweak A) a)

/-- Convergence with respect to the ultrastrong topology (encoding used
throughout these files). -/
def USTendsto {ι : Type*} (x : ι → A) (l : Filter ι) (a : A) : Prop :=
  Tendsto x l (@nhds A (ultrastrong A) a)

omit [StarOrderedRing A] in
/-- **42III** (vn.tex:208), embedded claim ("one can verify"): a net
`(b_α)_α` converges ultraweakly to `b` iff `ω(b_α) → ω(b)` for every
np-functional `ω`. -/
theorem uwTendsto_iff {ι : Type*} (x : ι → A) (l : Filter ι) (b : A) :
    UWTendsto x l b ↔
      ∀ ω : NPFunctional A, Tendsto (fun i => ω (x i)) l (𝓝 (ω b)) := by
  rw [UWTendsto, ultraweak, nhds_iInf]
  simp only [nhds_induced, tendsto_iInf, tendsto_comap_iff, Function.comp_def]

/-- **42III** (vn.tex:208), embedded claim ("one can prove"): a net `(b_α)_α`
converges ultrastrongly to `b` iff `‖b_α - b‖_ω → 0` for every np-functional
`ω`. -/
theorem usTendsto_iff {ι : Type*} (x : ι → A) (l : Filter ι) (b : A) :
    USTendsto x l b ↔
      ∀ ω : NPFunctional A,
        Tendsto (fun i => omegaNorm A ω (x i - b)) l (𝓝 0) := by
  constructor
  · -- each "ball" around `b` is an ultrastrong neighbourhood of `b`
    intro h ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hmem : b ∈ {a : A | omegaNorm A ω (a - b) < ε} := by
      simp [hε]
    have hopen : @IsOpen A (ultrastrong A) {a : A | omegaNorm A ω (a - b) < ε} :=
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨ω, b, ε, hε, rfl⟩
    have := h (@IsOpen.mem_nhds A (ultrastrong A) _ _ hopen hmem)
    filter_upwards [this] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg ω _)]
    exact hi
  · -- conversely, use the triangle inequality for `‖·‖_ω`
    intro h
    rw [USTendsto, ultrastrong, TopologicalSpace.nhds_generateFrom]
    simp only [tendsto_iInf, tendsto_principal, Set.mem_ofPred_eq]
    rintro s ⟨hbs, ω, c, ε, hε, rfl⟩
    simp only [Set.mem_ofPred_eq] at hbs ⊢
    have hδ : 0 < ε - omegaNorm A ω (b - c) := sub_pos.mpr hbs
    have := (Metric.tendsto_nhds.mp (h ω)) _ hδ
    filter_upwards [this] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaNorm_nonneg ω _)] at hi
    calc omegaNorm A ω (x i - c)
        ≤ omegaNorm A ω (x i - b) + omegaNorm A ω (b - c) :=
          omegaNorm_sub_le ω _ _ _
      _ < ε := by linarith

omit [StarOrderedRing A] in
@[simp] theorem npFunctional_sub (ω : NPFunctional A) (a b : A) :
    ω (a - b) = ω a - ω b :=
  map_sub ω.toPositiveLinearMap a b

omit [StarOrderedRing A] in
@[simp] theorem npFunctional_neg (ω : NPFunctional A) (a : A) : ω (-a) = -ω a :=
  map_neg ω.toPositiveLinearMap a

omit [StarOrderedRing A] in
@[simp] theorem npFunctional_add (ω : NPFunctional A) (a b : A) :
    ω (a + b) = ω a + ω b :=
  map_add ω.toPositiveLinearMap a b

omit [StarOrderedRing A] in
@[simp] theorem npFunctional_zero (ω : NPFunctional A) : ω (0 : A) = 0 :=
  map_zero ω.toPositiveLinearMap

theorem npFunctional_mono (ω : NPFunctional A) {a b : A} (h : a ≤ b) :
    (ω a : ℂ) ≤ ω b :=
  ω.toPositiveLinearMap.monotone h

theorem npFunctional_nonneg (ω : NPFunctional A) {a : A} (ha : 0 ≤ a) :
    (0 : ℂ) ≤ ω a := by
  have h1 := npFunctional_mono ω ha
  rwa [npFunctional_zero] at h1

/-- An np-functional is involution preserving (cstar.tex 10IV). -/
theorem npFunctional_star (ω : NPFunctional A) (a : A) :
    ω (star a) = star (ω a) :=
  map_star ω.toPositiveLinearMap a

/-- `|‖a‖_ω − ‖b‖_ω| ≤ ‖a − b‖_ω`: the reverse triangle inequality for the
GNS seminorm. -/
theorem abs_omegaNorm_sub_omegaNorm_le (ω : NPFunctional A) (a b : A) :
    |omegaNorm A ω a - omegaNorm A ω b| ≤ omegaNorm A ω (a - b) := by
  simp only [omegaNorm_eq_norm, map_sub]
  exact abs_norm_sub_norm_le _ _

/-- `‖bc‖_ω ≤ ‖b‖ ‖c‖_ω`: conjugate `b* b ≤ ‖b‖²·1` by `c` and apply `ω`.
(The submultiplicativity behind **72III**.1b; cf. cstar.tex 30IV.) -/
theorem omegaNorm_mul_le (ω : NPFunctional A) (b c : A) :
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

/-! ### The np-functionals form a cone

`Theses.NPFunctional` (root `Common.lean`) carries no algebraic structure,
but several proofs — **72IV**, **72V**, **72XI**, **73VIII**, **87VIII** —
need to replace a *finite family* of np-functionals by a single one
dominating all of them.  Positivity and linearity are inherited from
`A →ₚ[ℂ] ℂ`; only normality has to be checked, and for a sum it is the
standard "`sup` of a sum over a directed set is the sum of the `sup`s". -/

/-- The zero np-functional. -/
noncomputable def zeroNP : NPFunctional A where
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
noncomputable def addNP (ω₁ ω₂ : NPFunctional A) : NPFunctional A where
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

@[simp] theorem zeroNP_apply (a : A) : (zeroNP : NPFunctional A) a = 0 := rfl

@[simp] theorem addNP_apply (ω₁ ω₂ : NPFunctional A) (a : A) :
    addNP ω₁ ω₂ a = ω₁ a + ω₂ a := rfl

/-- `‖·‖_ω₁ ≤ ‖·‖_{ω₁+ω₂}`. -/
theorem omegaNorm_le_addNP (ω₁ ω₂ : NPFunctional A) (a : A) :
    omegaNorm A ω₁ a ≤ omegaNorm A (addNP ω₁ ω₂) a := by
  rw [omegaNorm, omegaNorm]
  refine Real.sqrt_le_sqrt ?_
  have h : (0 : ℂ) ≤ ω₂ (star a * a) := npFunctional_nonneg ω₂ (star_mul_self_nonneg a)
  have := (Complex.le_def.mp h).1
  simp only [addNP_apply, Complex.add_re]
  simpa using this

/-- `‖·‖_ω₂ ≤ ‖·‖_{ω₁+ω₂}`. -/
theorem omegaNorm_le_addNP' (ω₁ ω₂ : NPFunctional A) (a : A) :
    omegaNorm A ω₂ a ≤ omegaNorm A (addNP ω₁ ω₂) a := by
  rw [omegaNorm, omegaNorm]
  refine Real.sqrt_le_sqrt ?_
  have h : (0 : ℂ) ≤ ω₁ (star a * a) := npFunctional_nonneg ω₁ (star_mul_self_nonneg a)
  have := (Complex.le_def.mp h).1
  simp only [addNP_apply, Complex.add_re]
  simpa using this

private theorem cmul_le_cmul {r : ℝ} (hr : 0 ≤ r) {z w : ℂ} (h : z ≤ w) :
    (r : ℂ) * z ≤ (r : ℂ) * w := by
  obtain ⟨h1, h2⟩ := Complex.le_def.mp h
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · simpa using mul_le_mul_of_nonneg_left h1 hr
  · simp [h2]

/-- **72XI**/**73VIII**: the nonnegative real multiple `r·ω` of an np-functional. -/
noncomputable def smulNP {r : ℝ} (hr : 0 ≤ r) (ω : NPFunctional A) : NPFunctional A where
  toPositiveLinearMap :=
    PositiveLinearMap.mk₀ ((r : ℂ) • (ω.toPositiveLinearMap : A →ₗ[ℂ] ℂ))
      (fun x hx => by
        have h : (0 : ℂ) ≤ ω x := npFunctional_nonneg ω hx
        have h2 : (0 : ℂ) ≤ (r : ℂ) * ω x := by simpa using cmul_le_cmul hr h
        exact h2)
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hω := ω.preservesDirSups' D s hne hdir hlub
    have hub : ∀ d ∈ D, (ω (d : A) : ℂ) ≤ ω (s : A) := fun d hd => hω.1 ⟨d, hd, rfl⟩
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      change (r : ℂ) * ω (d : A) ≤ (r : ℂ) * ω (s : A)
      exact cmul_le_cmul hr (hub d hd)
    · intro z hz
      have hz' : ∀ d ∈ D, (r : ℂ) * ω (d : A) ≤ z := fun d hd => hz ⟨d, hd, rfl⟩
      change (r : ℂ) * ω (s : A) ≤ z
      rcases eq_or_lt_of_le hr with hr0 | hr0
      · obtain ⟨d₀, hd₀⟩ := hne
        have h0 := hz' d₀ hd₀
        rw [← hr0] at h0 ⊢
        simpa using h0
      · have hle : (ω (s : A) : ℂ) ≤ ((r⁻¹ : ℝ) : ℂ) * z := by
          refine hω.2 ?_
          rintro _ ⟨d, hd, rfl⟩
          have h := cmul_le_cmul (le_of_lt (inv_pos.mpr hr0)) (hz' d hd)
          rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hr0),
            Complex.ofReal_one, one_mul] at h
        have h := cmul_le_cmul hr hle
        rwa [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hr0),
          Complex.ofReal_one, one_mul] at h

@[simp] theorem smulNP_apply {r : ℝ} (hr : 0 ≤ r) (ω : NPFunctional A) (a : A) :
    smulNP hr ω a = (r : ℂ) * ω a := rfl

theorem omegaNorm_smulNP {r : ℝ} (hr : 0 ≤ r) (ω : NPFunctional A) (a : A) :
    omegaNorm A (smulNP hr ω) a = Real.sqrt r * omegaNorm A ω a := by
  rw [omegaNorm, omegaNorm, smulNP_apply, ← Real.sqrt_mul hr]
  congr 1
  simp

/-- The "balls" `{a | ‖a - b‖_ω < ε}` of **42III** are ultrastrong
neighbourhoods of `b` (they are among the generators of the topology). -/
theorem ultrastrong_ball_mem_nhds (ω : NPFunctional A) (b : A) {ε : ℝ}
    (hε : 0 < ε) : {a : A | omegaNorm A ω (a - b) < ε} ∈ @nhds A (ultrastrong A) b :=
  @IsOpen.mem_nhds A (ultrastrong A) _ _
    (TopologicalSpace.isOpen_generateFrom_of_mem ⟨ω, b, ε, hε, rfl⟩) (by simp [hε])

/-- Every ultrastrongly open set contains a `‖·‖_ω`-ball around each of its
points. -/
theorem exists_ultrastrong_ball_of_isOpen {S : Set A}
    (hS : @IsOpen A (ultrastrong A) S) :
    ∀ b ∈ S, ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
      {a : A | omegaNorm A ω (a - b) < δ} ⊆ S := by
  rw [ultrastrong] at hS
  replace hS : TopologicalSpace.GenerateOpen
      {U : Set A | ∃ (ω : NPFunctional A) (b : A) (ε : ℝ), 0 < ε ∧
        U = {a : A | omegaNorm A ω (a - b) < ε}} S := hS
  induction hS with
  | basic U hU =>
      obtain ⟨ω, c, ε, hε, rfl⟩ := hU
      intro b hb
      simp only [Set.mem_ofPred_eq] at hb
      refine ⟨ω, ε - omegaNorm A ω (b - c), by linarith, fun a ha => ?_⟩
      simp only [Set.mem_ofPred_eq] at ha ⊢
      have := omegaNorm_sub_le ω a b c
      linarith
  | univ => exact fun b _ => ⟨zeroNP, 1, one_pos, fun _ _ => Set.mem_univ _⟩
  | inter U V _ _ ihU ihV =>
      intro b hb
      obtain ⟨ω₁, δ₁, hδ₁, h₁⟩ := ihU b hb.1
      obtain ⟨ω₂, δ₂, hδ₂, h₂⟩ := ihV b hb.2
      refine ⟨addNP ω₁ ω₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun a ha => ?_⟩
      simp only [Set.mem_ofPred_eq] at ha
      refine ⟨h₁ ?_, h₂ ?_⟩
      · exact lt_of_le_of_lt (omegaNorm_le_addNP ω₁ ω₂ _) (lt_of_lt_of_le ha (min_le_left _ _))
      · exact lt_of_le_of_lt (omegaNorm_le_addNP' ω₁ ω₂ _) (lt_of_lt_of_le ha (min_le_right _ _))
  | sUnion T _ ih =>
      rintro b ⟨U, hU, hbU⟩
      obtain ⟨ω, δ, hδ, h⟩ := ih U hU b hbU
      exact ⟨ω, δ, hδ, fun a ha => ⟨U, hU, h ha⟩⟩

/-- Every np-functional is ultrastrongly continuous — this is the content of
**43I**.1, and gives **43I**.2 and **43I**.3 below. -/
theorem continuous_ultrastrong_npFunctional (ω : NPFunctional A) :
    @Continuous A ℂ (ultrastrong A) _ (fun a => ω a) := by
  refine (@continuous_def A ℂ (ultrastrong A) _ _).mpr fun U hU => ?_
  refine (@isOpen_iff_mem_nhds A (ultrastrong A) _).mpr fun b hb => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (ω b) hb
  set c := Real.sqrt (ω 1).re with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hδ : 0 < ε / (c + 1) := by positivity
  filter_upwards [ultrastrong_ball_mem_nhds ω b hδ] with a ha
  refine hball ?_
  have h1 : ‖ω a - ω b‖ ≤ omegaNorm A ω (a - b) * c := by
    simpa using norm_apply_le_omegaNorm ω (a - b)
  have h2 : omegaNorm A ω (a - b) * c ≤ ε / (c + 1) * c :=
    mul_le_mul_of_nonneg_right ha.le hc0
  have h3 : ε / (c + 1) * c < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

/-- Every np-functional is ultraweakly continuous: the ultraweak topology is
by definition the initial topology of the np-functionals. -/
theorem continuous_ultraweak_npFunctional (ω : NPFunctional A) :
    @Continuous A ℂ (ultraweak A) _ (fun a => ω a) :=
  continuous_iff_le_induced.mpr (iInf_le _ ω)

/-- Auxiliary: an intersection of ultraweakly closed sets is ultraweakly
closed (`isClosed_iInter` with the topology spelled out). -/
private theorem isClosed_ultraweak_iInter {ι : Sort*} (s : ι → Set A)
    (h : ∀ i, @IsClosed A (ultraweak A) (s i)) :
    @IsClosed A (ultraweak A) (⋂ i, s i) := by
  letI : TopologicalSpace A := ultraweak A
  exact isClosed_iInter h

/-- Auxiliary: the intersection of two ultraweakly closed sets. -/
private theorem isClosed_ultraweak_inter (s t : Set A)
    (hs : @IsClosed A (ultraweak A) s) (ht : @IsClosed A (ultraweak A) t) :
    @IsClosed A (ultraweak A) (s ∩ t) := by
  letI : TopologicalSpace A := ultraweak A
  exact hs.inter ht

/-- Auxiliary: the preimage of a closed subset of `ℂ` under an np-functional
is ultraweakly closed. -/
private theorem isClosed_ultraweak_preimage (ω : NPFunctional A) {S : Set ℂ}
    (hS : IsClosed S) :
    @IsClosed A (ultraweak A) ((fun a : A => (ω a : ℂ)) ⁻¹' S) :=
  (@continuous_iff_isClosed A ℂ (ultraweak A) _ _).mp
    (continuous_ultraweak_npFunctional ω) S hS

/-- **43I** (`uwweaker`): the ultrastrong topology is finer than the
ultraweak topology.  (Mathlib orders topologies by fineness: `t ≤ s` means
`t` has more open sets.) -/
theorem ultrastrong_le_ultraweak : ultrastrong A ≤ ultraweak A := by
  rw [ultraweak]
  exact le_iInf fun ω =>
    continuous_iff_le_induced.mp (continuous_ultrastrong_npFunctional ω)

/-! ## 42V: Examples of von Neumann algebras -/

/-- The identity is an np-functional on `ℂ`; it is the witness for both
clauses of Kadison's definition in the example `ℂ` (**42V**.1). -/
noncomputable def complexIdNP : NPFunctional ℂ where
  toPositiveLinearMap :=
    { toLinearMap := LinearMap.id, monotone' := fun _ _ h => h }
  preservesDirSups' := by
    intro D s hne _ hlub
    obtain ⟨d₀, hd₀⟩ := hne
    refine ⟨?_, fun w hw => ?_⟩
    · rintro w ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mpr (hlub.1 hd)
    · have hwim : w.im = 0 := by
        have h := hw ⟨d₀, hd₀, rfl⟩
        rw [Complex.le_def] at h
        rw [← h.2, Complex.im_eq_zero_iff_isSelfAdjoint]
        exact d₀.2
      have hub : (⟨w, (Complex.im_eq_zero_iff_isSelfAdjoint w).mp hwim⟩ :
          selfAdjoint ℂ) ∈ upperBounds D :=
        fun d hd => Subtype.coe_le_coe.mp (hw ⟨d, hd, rfl⟩)
      exact Subtype.coe_le_coe.mpr (hlub.2 hub)

/-- The ultraweak topology of the von Neumann algebra `ℂ` is its usual one:
`complexIdNP` is the identity, so it induces the norm topology, and every
np-functional on `ℂ` is `z ↦ z·ω(1)`, hence continuous.  (Needed to specialise
maps into a general von Neumann algebra `B` to functionals.) -/
theorem ultraweak_complex : ultraweak ℂ = (inferInstance : TopologicalSpace ℂ) := by
  refine le_antisymm ?_ (le_iInf fun ω => ?_)
  · refine le_trans (iInf_le _ complexIdNP) (le_of_eq ?_)
    exact induced_id
  · refine continuous_iff_le_induced.mp ?_
    have hval : ∀ z : ℂ, (ω z : ℂ) = z * ω 1 := by
      intro z
      have h : (ω.toPositiveLinearMap (z • (1 : ℂ)) : ℂ)
          = z • (ω.toPositiveLinearMap (1 : ℂ) : ℂ) :=
        map_smul ω.toPositiveLinearMap z (1 : ℂ)
      rw [smul_eq_mul, mul_one, smul_eq_mul] at h
      exact h
    have hcont : Continuous fun z : ℂ => z * (ω 1 : ℂ) :=
      continuous_id.mul continuous_const
    exact hcont.congr fun z => (hval z).symm

/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 1: `ℂ` is a
von Neumann algebra.  (`{0}` — any subsingleton C*-algebra — is one too,
trivially.) -/
noncomputable instance : VonNeumannAlgebra ℂ where
  isLUB_of_bddAbove_directed := by
    -- `sa(ℂ) ≅ ℝ`, and `ℝ` is conditionally complete
    intro D hne _ hbdd
    obtain ⟨b, hb⟩ := hbdd
    obtain ⟨d₀, hd₀⟩ := hne
    set S : Set ℝ := (fun d : selfAdjoint ℂ => (d : ℂ).re) '' D with hS
    have hSne : S.Nonempty := ⟨_, ⟨d₀, hd₀, rfl⟩⟩
    have hSbdd : BddAbove S := by
      refine ⟨(b : ℂ).re, ?_⟩
      rintro r ⟨d, hd, rfl⟩
      exact (Complex.le_def.mp (Subtype.coe_le_coe.mpr (hb hd))).1
    have hsup := Real.isLUB_sSup hSne hSbdd
    have hsa : IsSelfAdjoint ((sSup S : ℝ) : ℂ) :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (Complex.ofReal_im _)
    refine ⟨⟨((sSup S : ℝ) : ℂ), hsa⟩, ?_, fun c hc => ?_⟩
    · intro d hd
      refine Subtype.coe_le_coe.mp (Complex.le_def.mpr ⟨hsup.1 ⟨d, hd, rfl⟩, ?_⟩)
      rw [Complex.ofReal_im, Complex.im_eq_zero_iff_isSelfAdjoint]
      exact d.2
    · refine Subtype.coe_le_coe.mp (Complex.le_def.mpr ⟨?_, ?_⟩)
      · refine hsup.2 ?_
        rintro r ⟨d, hd, rfl⟩
        exact (Complex.le_def.mp (Subtype.coe_le_coe.mpr (hc hd))).1
      · rw [Complex.ofReal_im, eq_comm, Complex.im_eq_zero_iff_isSelfAdjoint]
        exact c.2
  np_faithful := fun a _ h => h complexIdNP

section BH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A vector functional `⟪x, (·) x⟫` on `B(H)` is monotone for the C*-order.
(Auxiliary for **42V**.2.) -/
private theorem inner_diag_mono (x : H) :
    Monotone fun T : H →L[ℂ] H => (⟪x, T x⟫ : ℂ) := by
  intro S T h
  have h0 : (0 : H →L[ℂ] H) ≤ T - S := sub_nonneg.mpr h
  have hp := (ContinuousLinearMap.isPositive_iff_complex (T - S)).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h0) x
  have key : (0 : ℂ) ≤ ⟪x, (T - S) x⟫ := by
    rw [← inner_conj_symm, ← hp.1, Complex.conj_ofReal, Complex.le_def]
    refine ⟨by simpa using hp.2, by simp⟩
  have hsub : (⟪x, T x⟫ : ℂ) - ⟪x, S x⟫ = ⟪x, (T - S) x⟫ := by
    rw [sub_apply, inner_sub_right]
  change (⟪x, S x⟫ : ℂ) ≤ ⟪x, T x⟫
  rw [← sub_nonneg, hsub]
  exact key

/-- The vector functional `⟪x, (·) x⟫` bundled as an np-functional on `B(H)`
(positivity is `inner_diag_mono`, normality is cstar.tex **38II**,
`Theses.A.CStar.vector_functional_normal`).  It is the witness for the
faithfulness clause of **42V**.2. -/
noncomputable def vectorNP (x : H) : NPFunctional (H →L[ℂ] H) where
  toPositiveLinearMap :=
    { toLinearMap := (vectorFunctionalCLM x : (H →L[ℂ] H) →L[ℂ] ℂ).toLinearMap
      monotone' := inner_diag_mono x }
  preservesDirSups' := vector_functional_normal x

@[simp] theorem vectorNP_apply (x : H) (T : H →L[ℂ] H) :
    vectorNP x T = ⟪x, T x⟫ :=
  rfl

/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 2: the
C*-algebra `B(H)` of bounded operators on a Hilbert space `H` is a von
Neumann algebra: it has bounded directed suprema of self-adjoint elements by
cstar.tex 37IX, and the vector states are order separating by cstar.tex
25III. -/
instance : VonNeumannAlgebra (H →L[ℂ] H) where
  isLUB_of_bddAbove_directed := by
    -- cstar.tex **37IX** (`hilb_suprema_1/2`) as the thesis states it: it asks
    -- only for the *pointwise* bounds `sup_{T ∈ D} ⟪x, T x⟫ < ∞`, which an
    -- order bound `S` supplies.  (Its 37XI repackaging `bhSup` asks for norm
    -- boundedness instead, which an order-bounded directed set need not have.)
    intro D hne hdir hbdd
    obtain ⟨S, hS⟩ := hbdd
    have hb : ∀ x : H, BddAbove
        ((fun T : selfAdjoint (H →L[ℂ] H) => ⟪x, (T : H →L[ℂ] H) x⟫) '' D) := by
      intro x
      refine ⟨⟪x, (S : H →L[ℂ] H) x⟫, ?_⟩
      rintro _ ⟨T, hT, rfl⟩
      exact inner_diag_mono x (Subtype.coe_le_coe.mpr (hS hT))
    obtain ⟨T', hT'⟩ := hilb_suprema_1 D hne hdir hb
    exact ⟨T', hilb_suprema_2 D hne hdir hb T' hT'⟩
  np_faithful := by
    intro T _ h
    have hz : ∀ x : H, (⟪(T : H →ₗ[ℂ] H) x, x⟫ : ℂ) = 0 := by
      intro x
      have hx : (⟪x, T x⟫ : ℂ) = 0 := h (vectorNP x)
      rw [← inner_conj_symm] at hx
      simpa using congrArg (starRingEnd ℂ) hx
    refine ContinuousLinearMap.coe_injective ?_
    rw [ContinuousLinearMap.toLinearMap_zero]
    exact (inner_map_self_eq_zero _).mp hz

/-- `‖a‖_ω = ‖a x‖` for the vector functional `ω = ⟪x, (·) x⟫` on `B(H)`. -/
theorem omegaNorm_vectorNP (x : H) (a : H →L[ℂ] H) :
    omegaNorm (H →L[ℂ] H) (vectorNP x) a = ‖a x‖ := by
  have h : ((vectorNP x) (star a * a)).re = ‖a x‖ ^ 2 := by
    have h1 : ((vectorNP x) (star a * a) : ℂ) = ⟪a x, a x⟫ := by
      change (⟪x, (star a * a) x⟫ : ℂ) = _
      rw [ContinuousLinearMap.star_eq_adjoint]
      change (⟪x, ContinuousLinearMap.adjoint a (a x)⟫ : ℂ) = _
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [h1]
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (a x)
  rw [omegaNorm, h, Real.sqrt_sq (norm_nonneg _)]

/-- The ultrastrong topology on `B(H)` is finer than the *strong* topology:
each evaluation `a ↦ a x` is ultrastrongly continuous.  Indeed the
ultrastrong "ball" of the vector functional `⟪x, (·) x⟫` around `a₀` is
literally `{a | ‖(a - a₀) x‖ < ε}` (`omegaNorm_vectorNP`). -/
theorem ultrastrong_continuous_apply (x : H) :
    @Continuous (H →L[ℂ] H) H (ultrastrong (H →L[ℂ] H)) _ (fun a => a x) := by
  rw [@continuous_iff_continuousAt (H →L[ℂ] H) H (ultrastrong _)]
  intro a₀
  show Filter.Tendsto (fun a : H →L[ℂ] H => a x)
    (@nhds (H →L[ℂ] H) (ultrastrong (H →L[ℂ] H)) a₀) (nhds (a₀ x))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hopen : @IsOpen (H →L[ℂ] H) (ultrastrong (H →L[ℂ] H))
      {a : H →L[ℂ] H | omegaNorm (H →L[ℂ] H) (vectorNP x) (a - a₀) < ε} :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨vectorNP x, a₀, ε, hε, rfl⟩
  have hmem : a₀ ∈ {a : H →L[ℂ] H |
      omegaNorm (H →L[ℂ] H) (vectorNP x) (a - a₀) < ε} := by
    simp [hε]
  have hnbhd : {a : H →L[ℂ] H | omegaNorm (H →L[ℂ] H) (vectorNP x) (a - a₀) < ε}
      ∈ @nhds (H →L[ℂ] H) (ultrastrong (H →L[ℂ] H)) a₀ :=
    @IsOpen.mem_nhds (H →L[ℂ] H) (ultrastrong (H →L[ℂ] H)) _ _ hopen hmem
  filter_upwards [hnbhd] with a ha
  have hsub : a x - a₀ x = (a - a₀) x := rfl
  rw [dist_eq_norm, hsub, ← omegaNorm_vectorNP x (a - a₀)]
  exact ha

/-- Since **39IX** `bh_np` writes every np-functional `ω` on `B(H)` as
`∑ₙ ⟪xₙ, (·) xₙ⟫`, the GNS seminorm of `42III` is
`‖T‖²_ω = ω(T*T) = ∑ₙ ‖T xₙ‖²`.  This is what makes the estimates of **43II**
dominated-convergence arguments. -/
theorem hasSum_omegaNorm_sq {ω : NPFunctional (H →L[ℂ] H)} {x : ℕ → H}
    (hx : ∀ T : H →L[ℂ] H, HasSum (fun n => (⟪x n, T (x n)⟫ : ℂ)) (ω T))
    (T : H →L[ℂ] H) :
    HasSum (fun n => ‖T (x n)‖ ^ 2) (omegaNorm (H →L[ℂ] H) ω T ^ 2) := by
  have hnn : (0 : ℝ) ≤ (ω (star T * T)).re := by
    have h : (0 : ℂ) ≤ ω (star T * T) :=
      npFunctional_nonneg ω (star_mul_self_nonneg T)
    simpa using (Complex.le_def.mp h).1
  have hterm : ∀ n : ℕ,
      (⟪x n, (star T * T) (x n)⟫ : ℂ) = ((‖T (x n)‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    have hap : ((star T * T) (x n)) = ContinuousLinearMap.adjoint T (T (x n)) := by
      rw [ContinuousLinearMap.star_eq_adjoint]; rfl
    rw [hap, ContinuousLinearMap.adjoint_inner_right]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (T (x n))]
    exact (inner_self_ofReal_re (T (x n))).symm
  have h : HasSum (fun n : ℕ => ((‖T (x n)‖ ^ 2 : ℝ) : ℂ)) (ω (star T * T)) := by
    simpa only [hterm] using hx (star T * T)
  have hre := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  have hsq : omegaNorm (H →L[ℂ] H) ω T ^ 2 = (ω (star T * T)).re := by
    rw [omegaNorm, Real.sq_sqrt hnn]
  rw [hsq]
  exact hre

end BH

section DirectSum

/- The `[∀ i, Nontrivial (𝒜 i)]` binder below is **not** the thesis's: 42V.1
explicitly allows the zero algebra as a summand.  It is forced by Mathlib,
whose unital normed-ring instance on `lp A ∞` carries it —

    instance [∀ i, Nontrivial (A i)] [∀ i, CStarAlgebra (A i)] :
        NormedRing (lp A ∞)

with the comment "it's slightly weird that we need the `Nontrivial` instance
here; it's because we have no way to say that `‖(1 : A i)‖` is uniformly
bounded as a type class" (`Mathlib/Analysis/CStarAlgebra/lpSpace.lean`).  The
bound is `‖1‖ ≤ 1` in *every* C*-algebra, so nothing mathematical is assumed;
dropping the binder means re-founding the ring structure of `lp 𝒜 ∞` against
Mathlib's instance, which is not a repair of our transcription.  Recorded
here, and left. -/

variable {I : Type*} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)]

-- The unital `CStarAlgebra (lp 𝒜 ∞)` instance is NOT declared here.  It was,
-- anonymously, until 2026-08-29, and it shadowed `lpInftyCStarAlgebra`
-- (`A/CStar/Positive.lean:3768`), which this file already imports through
-- `A/CStar/Representation`.  The two were definitionally equal and the shadow
-- won synthesis downstream, so it was redundant rather than dangerous -- but it
-- was also strictly less general (`Type u` with `𝒜` explicit, against `Type*`
-- with `𝒜` implicit).  Both doc comments were right that *Mathlib* registers
-- only the non-unital and commutative cases; neither mentioned that we had
-- already supplied this one.

/-- The canonical (spectral) order on the direct sum `lp 𝒜 ∞`, mirroring
`CStarMatrix.instPartialOrder`. -/
noncomputable instance : PartialOrder (lp 𝒜 ∞) := CStarAlgebra.spectralOrder _

instance : StarOrderedRing (lp 𝒜 ∞) := CStarAlgebra.spectralOrderedRing _

variable [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]

variable {𝒜}

/-- Positivity in the direct sum `⊕ᵢ 𝒜ᵢ = lp 𝒜 ∞` is *pointwise* positivity. -/
theorem lp_infty_nonneg_iff (a : lp 𝒜 ∞) : 0 ≤ a ↔ ∀ i, 0 ≤ a i := by
  constructor
  · intro ha i
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        rw [lp.infty_coeFn_mul, lp.coeFn_star]
        exact star_mul_self_nonneg (s i)
    | zero => simp
    | add x y _ _ hx hy => simpa using add_nonneg hx hy
  · intro ha
    set b : ∀ i, 𝒜 i := fun i => CFC.sqrt (a i) with hb
    have hbsa : ∀ i, IsSelfAdjoint (b i) := fun i => .of_nonneg (CFC.sqrt_nonneg _)
    have hnorm : ∀ i, ‖b i‖ * ‖b i‖ = ‖(a : ∀ i, 𝒜 i) i‖ := by
      intro i
      have h := CStarRing.norm_star_mul_self (x := b i)
      rw [(hbsa i).star_eq] at h
      rw [← h, hb, CFC.sqrt_mul_sqrt_self _ (ha i)]
    have hmem : Memℓp b ∞ := by
      apply memℓp_infty
      refine ⟨‖a‖ + 1, ?_⟩
      rintro _ ⟨i, rfl⟩
      have h1 : ‖(a : ∀ i, 𝒜 i) i‖ ≤ ‖a‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero a i
      have h2 := hnorm i
      have h3 : (0:ℝ) ≤ ‖b i‖ := norm_nonneg _
      nlinarith [norm_nonneg ((a : ∀ i, 𝒜 i) i)]
    have hEq : a = star (⟨b, hmem⟩ : lp 𝒜 ∞) * ⟨b, hmem⟩ := by
      apply lp.ext
      funext i
      rw [lp.infty_coeFn_mul, lp.coeFn_star]
      change (a : ∀ i, 𝒜 i) i = star (b i) * b i
      rw [(hbsa i).star_eq, hb, CFC.sqrt_mul_sqrt_self _ (ha i)]
    rw [hEq]
    exact star_mul_self_nonneg _

/-- The order on the direct sum `⊕ᵢ 𝒜ᵢ = lp 𝒜 ∞` is the pointwise order. -/
theorem lp_infty_le_iff (a b : lp 𝒜 ∞) : a ≤ b ↔ ∀ i, a i ≤ b i := by
  rw [← sub_nonneg, lp_infty_nonneg_iff]
  simp only [lp.coeFn_sub, Pi.sub_apply, sub_nonneg]

omit [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] in
theorem lp_infty_isSelfAdjoint {a : lp 𝒜 ∞} (ha : IsSelfAdjoint a) (i : I) :
    IsSelfAdjoint ((a : ∀ i, 𝒜 i) i) := by
  have h : (⇑(star a) : ∀ i, 𝒜 i) = ⇑a := congrArg _ ha
  rw [lp.coeFn_star] at h
  exact congrFun h i

variable (𝒜) in
/-- Evaluation `⊕ᵢ 𝒜ᵢ → 𝒜ⱼ` as a linear map. -/
def lpEvalₗ (i : I) : lp 𝒜 ∞ →ₗ[ℂ] 𝒜 i where
  toFun a := a i
  map_add' a b := by rw [lp.coeFn_add]; rfl
  map_smul' c a := by rw [lp.coeFn_smul]; rfl

/-- Evaluation on self-adjoint parts. -/
def lpEvalSA (i : I) (a : selfAdjoint (lp 𝒜 ∞)) : selfAdjoint (𝒜 i) :=
  ⟨(a : lp 𝒜 ∞) i, lp_infty_isSelfAdjoint a.2 i⟩

theorem lpEvalSA_mono (i : I) {a b : selfAdjoint (lp 𝒜 ∞)} (h : a ≤ b) :
    lpEvalSA i a ≤ lpEvalSA i b :=
  (lp_infty_le_iff _ _).mp (Subtype.coe_le_coe.mpr h) i

theorem lp_infty_exists_isLUB [∀ i, VonNeumannAlgebra (𝒜 i)]
    (D : Set (selfAdjoint (lp 𝒜 ∞))) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) :
    ∃ s : selfAdjoint (lp 𝒜 ∞), IsLUB D s ∧
      ∀ i, IsLUB (lpEvalSA i '' D) (lpEvalSA i s) := by
  obtain ⟨S, hS⟩ := hbdd
  obtain ⟨d₀, hd₀⟩ := hne
  have hex : ∀ i, ∃ t : selfAdjoint (𝒜 i), IsLUB (lpEvalSA i '' D) t := by
    intro i
    refine VonNeumannAlgebra.isLUB_of_bddAbove_directed _ ⟨lpEvalSA i d₀, ⟨d₀, hd₀, rfl⟩⟩ ?_
      ⟨lpEvalSA i S, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨lpEvalSA i z, ⟨z, hz, rfl⟩, lpEvalSA_mono i hxz, lpEvalSA_mono i hyz⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact lpEvalSA_mono i (hS hx)
  choose t ht using hex
  have hub : ∀ i, lpEvalSA i S ∈ upperBounds (lpEvalSA i '' D) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact lpEvalSA_mono i (hS hx)
  have hbound : ∀ i, ‖(t i : 𝒜 i)‖ ≤ ‖S‖ + 2 * ‖d₀‖ := by
    intro i
    have h1 : (0 : 𝒜 i) ≤ (t i : 𝒜 i) - ((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i :=
      sub_nonneg.mpr (Subtype.coe_le_coe.mpr ((ht i).1 ⟨d₀, hd₀, rfl⟩))
    have h2 : (t i : 𝒜 i) - ((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i
        ≤ ((S : lp 𝒜 ∞) : ∀ i, 𝒜 i) i - ((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i :=
      sub_le_sub_right (Subtype.coe_le_coe.mpr ((ht i).2 (hub i))) _
    have h3 := CStarAlgebra.norm_le_norm_of_nonneg_of_le h1 h2
    have h4 : ‖((S : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖ ≤ ‖S‖ := by
      simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero (S : lp 𝒜 ∞) i
    have h5 : ‖((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖ ≤ ‖d₀‖ := by
      simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero (d₀ : lp 𝒜 ∞) i
    have h6 : ‖(t i : 𝒜 i)‖ ≤ ‖(t i : 𝒜 i) - ((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖
        + ‖((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖ := by
      simpa using norm_add_le ((t i : 𝒜 i) - ((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i)
        (((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i)
    have h7 : ‖((S : lp 𝒜 ∞) : ∀ i, 𝒜 i) i - ((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖
        ≤ ‖((S : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖ + ‖((d₀ : lp 𝒜 ∞) : ∀ i, 𝒜 i) i‖ := norm_sub_le _ _
    linarith
  have hmem : Memℓp (fun i => (t i : 𝒜 i)) ∞ :=
    memℓp_infty ⟨‖S‖ + 2 * ‖d₀‖, by rintro _ ⟨i, rfl⟩; exact hbound i⟩
  set s : lp 𝒜 ∞ := ⟨fun i => (t i : 𝒜 i), hmem⟩ with hs
  have hssa : IsSelfAdjoint s := by
    apply lp.ext
    rw [lp.coeFn_star]
    funext i
    exact (t i).2
  refine ⟨⟨s, hssa⟩, ⟨?_, ?_⟩, fun i => ?_⟩
  · intro d hd
    rw [← Subtype.coe_le_coe, lp_infty_le_iff]
    intro i
    exact Subtype.coe_le_coe.mpr ((ht i).1 ⟨d, hd, rfl⟩)
  · intro u hu
    rw [← Subtype.coe_le_coe, lp_infty_le_iff]
    intro i
    have hui : lpEvalSA i u ∈ upperBounds (lpEvalSA i '' D) := by
      rintro _ ⟨x, hx, rfl⟩
      exact lpEvalSA_mono i (hu hx)
    exact Subtype.coe_le_coe.mpr ((ht i).2 hui)
  · exact (show lpEvalSA i (⟨s, hssa⟩ : selfAdjoint (lp 𝒜 ∞)) = t i from Subtype.ext rfl) ▸ ht i

/-- Composing an np-functional `ω` on `𝒜ᵢ` with the evaluation `⊕ⱼ 𝒜ⱼ → 𝒜ᵢ`
gives an np-functional on the direct sum. -/
noncomputable def lpNP [∀ i, VonNeumannAlgebra (𝒜 i)] (i : I)
    (ω : NPFunctional (𝒜 i)) : NPFunctional (lp 𝒜 ∞) where
  toPositiveLinearMap :=
    { toLinearMap := ω.toPositiveLinearMap.toLinearMap.comp (lpEvalₗ 𝒜 i)
      monotone' := fun a b hab =>
        ω.toPositiveLinearMap.monotone' ((lp_infty_le_iff a b).mp hab i) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    obtain ⟨s', hs', hev⟩ := lp_infty_exists_isLUB D hne hdir ⟨s, hlub.1⟩
    obtain rfl := hlub.unique hs'
    have hdir' : DirectedOn (· ≤ ·) (lpEvalSA i '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨lpEvalSA i z, ⟨z, hz, rfl⟩, lpEvalSA_mono i hxz, lpEvalSA_mono i hyz⟩
    have h := ω.preservesDirSups' (lpEvalSA i '' D) (lpEvalSA i s) (hne.image _) hdir' (hev i)
    rwa [Set.image_image] at h

theorem lp_infty_np_apply [∀ i, VonNeumannAlgebra (𝒜 i)] (i : I)
    (ω : NPFunctional (𝒜 i)) (a : lp 𝒜 ∞) :
    lpNP i ω a = ω ((a : ∀ i, 𝒜 i) i) := rfl

/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 3 (also
**47IV**, `vn-products`, part 1): the direct sum `⊕ᵢ 𝒜ᵢ` (Mathlib:
`lp 𝒜 ∞`) of a family of von Neumann algebras is a von Neumann algebra.

(Carries the section's `[∀ i, Nontrivial (𝒜 i)]`, which the thesis does not
assume — see the note at the head of this section: it comes from Mathlib's
unital instance on `lp 𝒜 ∞`, not from the mathematics.) -/
instance vonNeumannAlgebra_lp_infty [∀ i, VonNeumannAlgebra (𝒜 i)] :
    VonNeumannAlgebra (lp 𝒜 ∞) where
  isLUB_of_bddAbove_directed D hne hdir hbdd :=
    let ⟨s, hs, _⟩ := lp_infty_exists_isLUB D hne hdir hbdd
    ⟨s, hs⟩
  np_faithful a ha h := by
    apply lp.ext
    funext i
    have : (a : ∀ i, 𝒜 i) i = 0 :=
      VonNeumannAlgebra.np_faithful _ ((lp_infty_nonneg_iff a).mp ha i)
        fun ω => (lp_infty_np_apply i ω a).symm.trans (h (lpNP i ω))
    simpa using this

end DirectSum

/-! ### 42V.3 over the nontrivial summands only

The binder `[∀ i, Nontrivial (𝒜 i)]` of `section DirectSum` is Mathlib's, not
42V's (see the note at the head of that section).  Restated over
`J = {i // Nontrivial (𝒜 i)}` it is *discharged* rather than assumed
(`fun j => j.2`), and `⊕_{j : J} 𝒜ⱼ` is the printed `⊕ᵢ𝒜ᵢ` up to the
isometric star-isomorphism `lpInftyNontrivialEquiv` (`A/CStar/Positive.lean`).

The discharge is a `local instance` rather than a `haveI` in each proof: the
*statements* below already mention structures on `lp` that Mathlib gates on the
binder, so the instance has to be available while the type is elaborated. -/

private theorem nontrivial_of_nontrivialIndex {ι : Type*} {𝒜 : ι → Type*}
    (j : {i // Nontrivial (𝒜 i)}) : Nontrivial (𝒜 j) := j.2

section DirectSumNontrivial

attribute [local instance] nontrivial_of_nontrivialIndex

/-- **42V**.3 without the Mathlib binder: over the nontrivial indices, which is
the whole sum up to `lpInftyNontrivialEquiv` (`A/CStar/Positive.lean`). -/
theorem vonNeumannAlgebra_lp_infty' {I : Type*} {𝒜 : I → Type u}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] :
    VonNeumannAlgebra (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞) :=
  vonNeumannAlgebra_lp_infty (𝒜 := fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j)

end DirectSumNontrivial

variable (A) in
/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 4: a
C*-subalgebra `S` of a von Neumann algebra `A` is a **von Neumann
subalgebra** when the supremum (taken in `A`) of every nonempty bounded
directed set of self-adjoint elements of `S` again belongs to `S`.  (Such an
`S` is itself a von Neumann algebra.) -/
structure IsVNSubalgebra (S : StarSubalgebra ℂ A) : Prop where
  isClosed : IsClosed (S : Set A)
  dirSup_mem : ∀ (D : Set (selfAdjoint A)) (s : selfAdjoint A),
    (∀ d ∈ D, (d : A) ∈ S) → D.Nonempty → DirectedOn (· ≤ ·) D →
      IsLUB D s → (s : A) ∈ S

variable (A) in
/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 4a: the
least von Neumann subalgebra `W*(S)` of `A` containing a subset `S` — the
intersection of all von Neumann subalgebras containing `S`. -/
def wstar (S : Set A) : StarSubalgebra ℂ A :=
  sInf {T : StarSubalgebra ℂ A | IsVNSubalgebra A T ∧ S ⊆ T}

omit [StarOrderedRing A] in
/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 4a,
well-definedness: `W*(S)` is indeed a von Neumann subalgebra containing `S`
(the intersection of von Neumann subalgebras is one). -/
theorem isVNSubalgebra_wstar [VonNeumannAlgebra A] (S : Set A) :
    IsVNSubalgebra A (wstar A S) ∧ S ⊆ wstar A S := by
  -- the intersection of a family of von Neumann subalgebras is one
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [wstar, StarSubalgebra.coe_sInf]
    exact isClosed_biInter fun T hT => hT.1.isClosed
  · intro D s hDS hne hdir hlub
    rw [wstar, StarSubalgebra.mem_sInf]
    intro T hT
    exact hT.1.dirSup_mem D s (fun d hd => by
      have := hDS d hd
      rw [wstar, StarSubalgebra.mem_sInf] at this
      exact this T hT) hne hdir hlub
  · intro x hx
    rw [SetLike.mem_coe, wstar, StarSubalgebra.mem_sInf]
    exact fun T hT => hT.2 hx

/-! **42V**, parts 5–7 (commutants, matrices, `L^∞(X)`) are stated at their
proper places: 65III (`Theses/A/VN/Projections.lean`), 49IV (`mn_vna` below)
and 51IX (`Linfty_vn` below). -/

/-! ## Parsec 430: counterexamples -/

/-- **43I** (`uwweaker`, vn.tex:341, Exercise), part 1:
`|ω(a)| ≤ ‖a‖_ω · ‖ω‖^½` for every np-functional `ω` and `a ∈ A` (for a
positive functional `‖ω‖ = ω(1)`, which is how the norm is rendered
here). -/
theorem uwweaker_1 [VonNeumannAlgebra A] (ω : NPFunctional A) (a : A) :
    ‖ω a‖ ≤ omegaNorm A ω a * Real.sqrt (ω 1).re :=
  norm_apply_le_omegaNorm ω a

/-- **43I** (`uwweaker`, vn.tex:341, Exercise), part 2: ultrastrong
convergence implies ultraweak convergence. -/
theorem uwweaker_2 [VonNeumannAlgebra A] {ι : Type*} (x : ι → A)
    (l : Filter ι) (a : A) (h : USTendsto x l a) : UWTendsto x l a :=
  h.mono_right (nhds_mono ultrastrong_le_ultraweak)

/-- **43I** (`uwweaker`, vn.tex:341, Exercise), part 3: an ultraweakly closed
subset of `A` is ultrastrongly closed. -/
theorem uwweaker_3 [VonNeumannAlgebra A] (C : Set A)
    (h : @IsClosed A (ultraweak A) C) : @IsClosed A (ultrastrong A) C :=
  h.mono ultrastrong_le_ultraweak

/-- **43Ia** (`infima-in-vna`, vn.tex:359, Exercise): every nonempty bounded
filtered (downwards directed) set `F` of self-adjoint elements of a von
Neumann algebra has an infimum, namely `⋀ F = -⋁{-d : d ∈ F}`. -/
theorem infima_in_vna [VonNeumannAlgebra A] (F : Set (selfAdjoint A))
    (hne : F.Nonempty) (hdir : DirectedOn (· ≥ ·) F) (hbdd : BddBelow F) :
    ∃ i : selfAdjoint A, IsGLB F i := by
  -- `a ↦ -a` is an order-reversing isomorphism, so apply 42I.1 to `-F`
  have hne' : (-F).Nonempty := hne.neg
  have hdir' : DirectedOn (· ≤ ·) (-F) := by
    rintro x hx y hy
    rw [Set.mem_neg] at hx hy
    obtain ⟨c, hc, hcx, hcy⟩ := hdir _ hx _ hy
    exact ⟨-c, by simpa using hc, le_neg.mpr hcx, le_neg.mpr hcy⟩
  obtain ⟨s, hs⟩ :=
    VonNeumannAlgebra.isLUB_of_bddAbove_directed (-F) hne' hdir' hbdd.neg
  exact ⟨-s, by simpa using hs.neg⟩

section Counterexamples

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- The operator `|n⟩⟨m|` on `ℓ²` (**43II**, vn.tex:374, part 1). -/
noncomputable def ketbraNat (n m : ℕ) : ℓ² →L[ℂ] ℓ² :=
  ketbra (lp.single 2 n 1) (lp.single 2 m 1)

/-- The action of `|n⟩⟨m|` on a vector: `|n⟩⟨m| z = ⟨e_m, z⟩ e_n`.
(Auxiliary — the computation rules of **43II**.1 are
`vn_counterexamples_1` below.) -/
private theorem ketbraNat_apply (n m : ℕ) (z : ℓ²) :
    ketbraNat n m z = (⟪lp.single 2 m (1 : ℂ), z⟫ : ℂ) • lp.single 2 n (1 : ℂ) :=
  rfl

private theorem inner_single_nat (m l : ℕ) :
    (⟪(lp.single 2 m (1 : ℂ) : ℓ²), (lp.single 2 l (1 : ℂ) : ℓ²)⟫ : ℂ) =
      if m = l then 1 else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  simp [Pi.single_apply]

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 1:
computation rules `(|n⟩⟨m|)* = |m⟩⟨n|` and
`|n⟩⟨m| |l⟩⟨k| = δ_{m,l} |n⟩⟨k|`. -/
theorem vn_counterexamples_1 (k l m n : ℕ) :
    star (ketbraNat n m) = ketbraNat m n ∧
      ketbraNat n m * ketbraNat l k =
        (if m = l then ketbraNat n k else 0) := by
  constructor
  · rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro u v
    rw [ketbraNat_apply, ketbraNat_apply, inner_smul_left, inner_smul_right,
      inner_conj_symm]
    ring
  · refine ContinuousLinearMap.ext fun z => ?_
    have hL : (ketbraNat n m * ketbraNat l k) z
        = ((⟪(lp.single 2 m (1 : ℂ) : ℓ²), (lp.single 2 l (1 : ℂ) : ℓ²)⟫ : ℂ) *
            ⟪lp.single 2 k (1 : ℂ), z⟫) • lp.single 2 n (1 : ℂ) := by
      change ketbraNat n m (ketbraNat l k z) = _
      rw [ketbraNat_apply, ketbraNat_apply, inner_smul_right, mul_comm]
    rw [hL, inner_single_nat]
    by_cases h : m = l
    · simp only [h, ite_true, one_mul, ketbraNat_apply]
    · simp only [h, ite_false, zero_mul, zero_smul, zero_apply]

/-! ### Auxiliary machinery for parts 2–6

Since **39IX** `bh_np` is proved, every np-functional `ω` on `B(ℓ²)` is
`∑ₘ ⟪xₘ, (·) xₘ⟫` with `∑ₘ ‖xₘ‖² = ω(1) < ∞`, and `hasSum_omegaNorm_sq`
turns the seminorm of `42III` into `‖T‖²_ω = ∑ₘ ‖T xₘ‖²`.  For both
`T = |n⟩⟨n|` and `T = |0⟩⟨n|` one has `‖T y‖ = |y(n)|`, so parts 2 and 4 are
one and the same dominated-convergence argument over `m` (Tannery's theorem),
with the summable dominating family `(‖xₘ‖²)ₘ`. -/

private theorem star_ketbraNat (n m : ℕ) :
    star (ketbraNat n m) = ketbraNat m n :=
  (vn_counterexamples_1 0 0 m n).1

private theorem inner_single_coord (n : ℕ) (y : ℓ²) :
    (⟪(lp.single 2 n (1 : ℂ) : ℓ²), y⟫ : ℂ) = y n := by
  rw [lp.inner_single_left]
  simp [RCLike.inner_apply']

private theorem inner_single_coord' (n : ℕ) (y : ℓ²) :
    (⟪y, (lp.single 2 n (1 : ℂ) : ℓ²)⟫ : ℂ) = star (y n) := by
  rw [← inner_conj_symm, inner_single_coord]
  rfl

private theorem norm_single_nat (n : ℕ) : ‖(lp.single 2 n (1 : ℂ) : ℓ²)‖ = 1 := by
  rw [lp.norm_single (by norm_num)]
  simp

private theorem hasSum_coord_sq (y : ℓ²) :
    HasSum (fun n : ℕ => ‖y n‖ ^ 2) (‖y‖ ^ 2) := by
  have hterm : ∀ n : ℕ, (⟪y n, y n⟫ : ℂ) = ((‖y n‖ ^ 2 : ℝ) : ℂ) := fun n => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (y n)]
    exact (inner_self_ofReal_re _).symm
  have hy : (⟪y, y⟫ : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) y]
    exact (inner_self_ofReal_re _).symm
  have h : HasSum (fun n : ℕ => ((‖y n‖ ^ 2 : ℝ) : ℂ)) (((‖y‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [hterm, hy] using lp.hasSum_inner (𝕜 := ℂ) y y
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum h

private theorem tendsto_coord_zero (y : ℓ²) :
    Tendsto (fun n : ℕ => y n) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ‖y n‖ ^ 2) atTop (𝓝 0) :=
    (hasSum_coord_sq y).summable.tendsto_atTop_zero
  have h1 : Tendsto (fun n : ℕ => ‖y n‖) atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h0
    simp only [Function.comp_def, Real.sqrt_zero] at h2
    exact h2.congr fun n => Real.sqrt_sq (norm_nonneg _)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h1

private theorem norm_ketbraNat_apply (n m : ℕ) (y : ℓ²) :
    ‖ketbraNat n m y‖ = ‖y m‖ := by
  rw [ketbraNat_apply, norm_smul, inner_single_coord, norm_single_nat, mul_one]

private theorem norm_ketbraNat_le_one (n m : ℕ) : ‖ketbraNat n m‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [norm_ketbraNat_apply, one_mul]
  exact lp.norm_apply_le_norm (by norm_num) y m

/-- The heart of parts 2 and 4: a sequence `(Tₙ)` on `ℓ²` with
`‖Tₙ y‖ = |y(n)|` for every `y` converges *ultrastrongly* to `0`.  Writing
`ω = ∑ₘ⟪xₘ,(·)xₘ⟫` (**39IX**), `‖Tₙ‖²_ω = ∑ₘ |xₘ(n)|²`, which tends to `0` by
Tannery's theorem: each `|xₘ(n)|² → 0` in `n` because `xₘ ∈ ℓ²`, and
`|xₘ(n)|² ≤ ‖xₘ‖²` is summable in `m`. -/
private theorem usTendsto_zero_of_norm_apply_coord (T : ℕ → (ℓ² →L[ℂ] ℓ²))
    (hT : ∀ (n : ℕ) (y : ℓ²), ‖T n y‖ = ‖y n‖) : USTendsto T atTop 0 := by
  rw [usTendsto_iff]
  intro ω
  obtain ⟨x, hx, hone⟩ := bh_np ω
  have hbound : Summable fun m : ℕ => ‖x m‖ ^ 2 := by
    have hre := Complex.reCLM.hasSum hone
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
    exact hre.summable
  have hsq : ∀ n : ℕ, omegaNorm (ℓ² →L[ℂ] ℓ²) ω (T n - 0) ^ 2
      = ∑' m : ℕ, ‖(x m) n‖ ^ 2 := by
    intro n
    rw [sub_zero]
    refine (HasSum.tsum_eq ?_).symm
    simpa only [hT n] using hasSum_omegaNorm_sq hx (T n)
  have htan : Tendsto (fun n : ℕ => ∑' m : ℕ, ‖(x m) n‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
      (f := fun n m : ℕ => ‖(x m) n‖ ^ 2) (g := fun _ : ℕ => (0 : ℝ))
      (bound := fun m : ℕ => ‖x m‖ ^ 2) hbound
      (fun m => (hasSum_coord_sq (x m)).summable.tendsto_atTop_zero)
      (Filter.Eventually.of_forall fun n m => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr
        exact lp.norm_apply_le_norm (by norm_num) (x m) n)
    simpa using h
  have h2 : Tendsto (fun n : ℕ => omegaNorm (ℓ² →L[ℂ] ℓ²) ω (T n - 0) ^ 2)
      atTop (𝓝 0) := by
    simpa only [hsq] using htan
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_zero] at h3
  exact h3.congr fun n => Real.sqrt_sq (omegaNorm_nonneg _ _)

/-- Auxiliary for parts 4 and 5: no subsequence of the standard basis of `ℓ²`
converges — `‖1 − v(φ n)‖ ≤ ‖e_{φ n} − v‖` while the left side tends to `1`. -/
private theorem not_tendsto_single_sub (v : ℓ²) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    ¬Tendsto (fun n : ℕ => ‖(lp.single 2 (φ n) (1 : ℂ) : ℓ²) - v‖) atTop (𝓝 0) := by
  intro h
  have hle : ∀ n : ℕ,
      ‖(1 : ℂ) - v (φ n)‖ ≤ ‖(lp.single 2 (φ n) (1 : ℂ) : ℓ²) - v‖ := by
    intro n
    have h1 := lp.norm_apply_le_norm (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num)
      ((lp.single 2 (φ n) (1 : ℂ) : ℓ²) - v) (φ n)
    rwa [lp.coeFn_sub, Pi.sub_apply, lp.single_apply_self] at h1
  have hv : Tendsto (fun n : ℕ => v (φ n)) atTop (𝓝 0) :=
    (tendsto_coord_zero v).comp hφ
  have hlim : Tendsto (fun n : ℕ => ‖(1 : ℂ) - v (φ n)‖) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℂ) - v (φ n)) atTop (𝓝 ((1 : ℂ) - 0)) :=
      tendsto_const_nhds.sub hv
    simpa [Function.comp_def] using (continuous_norm.tendsto ((1 : ℂ) - 0)).comp h1
  have hcon : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto hlim h (Filter.Eventually.of_forall hle)
  linarith

/-- Auxiliary: the diagonal values `⟪z, A z⟫` are conjugate-symmetric. -/
private theorem re_inner_swap (A : ℓ² →L[ℂ] ℓ²) (z : ℓ²) :
    (⟪z, A z⟫ : ℂ).re = (⟪A z, z⟫ : ℂ).re := by
  have h : (starRingEnd ℂ) (⟪A z, z⟫ : ℂ) = ⟪z, A z⟫ := inner_conj_symm z (A z)
  rw [← h, Complex.conj_re]

/-- Auxiliary: the diagonal values of a self-adjoint operator are real. -/
private theorem inner_self_real {A : ℓ² →L[ℂ] ℓ²} (hA : IsSelfAdjoint A) (z : ℓ²) :
    ((((⟪z, A z⟫ : ℂ).re : ℝ)) : ℂ) = ⟪z, A z⟫ := by
  have hsym : (⟪A z, z⟫ : ℂ) = ⟪z, A z⟫ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA z z
  refine Complex.conj_eq_iff_re.mp ?_
  rw [inner_conj_symm]
  exact hsym

/-- Auxiliary (a private copy of `Theses.A.CStar`'s): monotonicity of the
diagonal values of operators. -/
private theorem re_inner_mono {S T : ℓ² →L[ℂ] ℓ²} (h : S ≤ T) (z : ℓ²) :
    (⟪z, S z⟫ : ℂ).re ≤ (⟪z, T z⟫ : ℂ).re := by
  have h0 : (0 : ℓ² →L[ℂ] ℓ²) ≤ T - S := sub_nonneg.mpr h
  have hp := (ContinuousLinearMap.isPositive_iff_complex (T - S)).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h0) z
  have h2 : (0 : ℝ) ≤ (⟪(T - S) z, z⟫ : ℂ).re := hp.2
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re] at h2
  rw [re_inner_swap S z, re_inner_swap T z]
  linarith

/-- Auxiliary (a private copy of `Theses.A.CStar`'s): a self-adjoint operator
dominating another on the diagonal dominates it. -/
private theorem le_of_re_inner {S T : ℓ² →L[ℂ] ℓ²} (hS : IsSelfAdjoint S)
    (hT : IsSelfAdjoint T) (h : ∀ z, (⟪z, S z⟫ : ℂ).re ≤ (⟪z, T z⟫ : ℂ).re) :
    S ≤ T := by
  have hTS : IsSelfAdjoint (T - S) := hT.sub hS
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hre : ((((⟪z, (T - S) z⟫ : ℂ).re : ℝ)) : ℂ) = ⟪z, (T - S) z⟫ :=
    inner_self_real hTS z
  have hcomm : (⟪(T - S) z, z⟫ : ℂ) = ⟪z, (T - S) z⟫ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTS z z
  have hnn : (0 : ℝ) ≤ (⟪z, (T - S) z⟫ : ℂ).re := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    linarith [h z]
  rw [hcomm]
  exact ⟨hre, hnn⟩

private theorem ketbraNat_sum_apply (N : ℕ) (z : ℓ²) :
    (∑ n ∈ Finset.range N, ketbraNat n n) z
      = ∑ n ∈ Finset.range N, (z n) • (lp.single 2 n (1 : ℂ) : ℓ²) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        ContinuousLinearMap.add_apply, ih, ketbraNat_apply, inner_single_coord]

private theorem ketbraNat_sum_inner (N : ℕ) (z : ℓ²) :
    (⟪z, (∑ n ∈ Finset.range N, ketbraNat n n) z⟫ : ℂ)
      = ((∑ n ∈ Finset.range N, ‖z n‖ ^ 2 : ℝ) : ℂ) := by
  rw [ketbraNat_sum_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_smul_right, inner_single_coord']
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem ketbraNat_sum_isSelfAdjoint (N : ℕ) :
    IsSelfAdjoint (∑ n ∈ Finset.range N, ketbraNat n n) := by
  rw [IsSelfAdjoint, star_sum]
  exact Finset.sum_congr rfl fun n _ => star_ketbraNat n n

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 2 (first
half): `⋁_N ∑_{n≤N} |n⟩⟨n| = 1` in `B(ℓ²)`. -/
theorem vn_counterexamples_2_sup :
    IsLUB {T : ℓ² →L[ℂ] ℓ² |
        ∃ N : ℕ, T = ∑ n ∈ Finset.range N, ketbraNat n n}
      1 := by
  have hone : ∀ z : ℓ², (⟪z, (1 : ℓ² →L[ℂ] ℓ²) z⟫ : ℂ).re = ‖z‖ ^ 2 := fun z => by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) z
  constructor
  · rintro T ⟨N, rfl⟩
    refine le_of_re_inner (ketbraNat_sum_isSelfAdjoint N) (star_one _) fun z => ?_
    rw [ketbraNat_sum_inner, hone z, Complex.ofReal_re]
    exact sum_le_hasSum (Finset.range N) (fun i _ => by positivity) (hasSum_coord_sq z)
  · intro T hT
    have h0 : (0 : ℓ² →L[ℂ] ℓ²) ≤ T := by
      have h := hT (⟨0, by simp⟩ : (0 : ℓ² →L[ℂ] ℓ²) ∈ {T : ℓ² →L[ℂ] ℓ² |
        ∃ N : ℕ, T = ∑ n ∈ Finset.range N, ketbraNat n n})
      exact h
    have hTsa : IsSelfAdjoint T :=
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp h0).isSelfAdjoint
    refine le_of_re_inner (star_one _) hTsa fun z => ?_
    rw [hone z]
    refine hasSum_le_of_sum_le (hasSum_coord_sq z) fun F => ?_
    obtain ⟨N, hN⟩ := F.exists_nat_subset_range
    have hstep : ∑ n ∈ F, ‖z n‖ ^ 2 ≤ ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hN fun _ _ _ => by positivity
    have hle := re_inner_mono (hT (⟨N, rfl⟩ :
      (∑ n ∈ Finset.range N, ketbraNat n n) ∈ {T : ℓ² →L[ℂ] ℓ² |
        ∃ N : ℕ, T = ∑ n ∈ Finset.range N, ketbraNat n n})) z
    rw [ketbraNat_sum_inner, Complex.ofReal_re] at hle
    linarith

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 2 (second
half): `(|n⟩⟨n|)_n` converges ultrastrongly (hence ultraweakly) to `0`; so
ultrastrong convergence does not imply norm convergence, and `‖·‖` is not
ultraweakly continuous. -/
theorem vn_counterexamples_2_tendsto :
    USTendsto (fun n : ℕ => ketbraNat n n) atTop 0 :=
  usTendsto_zero_of_norm_apply_coord _ fun n y => norm_ketbraNat_apply n n y

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 3: already in
`ℂ`, the sequence `(e^{in})_n` does not converge ultraweakly, although the
products `e^{-in}·e^{in} = 1` are norm-bounded and converge; so ultraweak
convergence of `(b_α* b_α)_α` and norm-boundedness do not imply ultrastrong
convergence of `(b_α)_α`. -/
theorem vn_counterexamples_3 :
    ¬∃ z : ℂ, UWTendsto (fun n : ℕ => Complex.exp (Complex.I * n)) atTop z := by
  rintro ⟨z, hz⟩
  rw [uwTendsto_iff] at hz
  -- the identity is an np-functional on `ℂ`, so ultraweak convergence in `ℂ`
  -- is ordinary convergence
  have h : Tendsto (fun n : ℕ => Complex.exp (Complex.I * n)) atTop (𝓝 z) :=
    hz complexIdNP
  -- `|e^{in}| = 1`, so `z ≠ 0`
  have hz1 : ‖z‖ = 1 := by
    have hn : Tendsto (fun n : ℕ => ‖Complex.exp (Complex.I * n)‖) atTop (𝓝 ‖z‖) :=
      (continuous_norm.tendsto z).comp h
    refine tendsto_nhds_unique hn ?_
    have : ∀ n : ℕ, ‖Complex.exp (Complex.I * n)‖ = 1 := by
      intro n
      rw [Complex.norm_exp]
      simp
    simp only [this]
    exact tendsto_const_nhds
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz1
    exact zero_ne_one hz1
  -- shifting the index multiplies the limit by `e^{i}`
  have hshift : Tendsto (fun n : ℕ => Complex.exp (Complex.I * ((n : ℂ) + 1)))
      atTop (𝓝 z) := by
    have := h.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
  have hmul : Tendsto (fun n : ℕ => Complex.exp (Complex.I * ((n : ℂ) + 1)))
      atTop (𝓝 (Complex.exp Complex.I * z)) := by
    have hc : Tendsto (fun n : ℕ =>
        Complex.exp Complex.I * Complex.exp (Complex.I * n)) atTop
        (𝓝 (Complex.exp Complex.I * z)) := h.const_mul _
    refine hc.congr fun n => ?_
    rw [← Complex.exp_add]
    ring_nf
  have hfix : z = Complex.exp Complex.I * z := tendsto_nhds_unique hshift hmul
  have hone : Complex.exp Complex.I = 1 := by
    have : (Complex.exp Complex.I - 1) * z = 0 := by
      rw [sub_mul, one_mul, ← hfix, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hz0
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
  -- `I = k · 2π I` forces `1 = 2πk`, impossible for an integer `k`
  have hk' : (1 : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    calc (1 : ℂ) * Complex.I = Complex.I := one_mul _
      _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
      _ = ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by ring
  have hk'' : (1 : ℝ) = (k : ℝ) * (2 * Real.pi) := by
    exact_mod_cast hk'
  have hpi : (3 : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  rcases lt_trichotomy (k : ℝ) 1 with hlt | heq | hgt
  · have hk0 : (k : ℝ) ≤ 0 := by
      have : k < 1 := by exact_mod_cast hlt
      have : k ≤ 0 := by omega
      exact_mod_cast this
    nlinarith [Real.pi_pos]
  · rw [heq, one_mul] at hk''
    nlinarith
  · nlinarith [Real.pi_pos]

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 4 (first
half): `(|0⟩⟨n|)_n` converges ultrastrongly to `0`. -/
theorem vn_counterexamples_4_ket :
    USTendsto (fun n : ℕ => ketbraNat 0 n) atTop 0 :=
  usTendsto_zero_of_norm_apply_coord _ fun n y => norm_ketbraNat_apply 0 n y

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 4 (second
half): `(|n⟩⟨0|)_n` converges ultraweakly to `0` but does not converge
ultrastrongly at all. -/
theorem vn_counterexamples_4_bra :
    UWTendsto (fun n : ℕ => ketbraNat n 0) atTop 0 ∧
      ¬∃ T : ℓ² →L[ℂ] ℓ², USTendsto (fun n : ℕ => ketbraNat n 0) atTop T := by
  constructor
  · -- `ω(|n⟩⟨0|) = conj ω(|0⟩⟨n|)`, and `|0⟩⟨n| → 0` ultrastrongly, hence
    -- ultraweakly (**43I**.2)
    have huw : UWTendsto (fun n : ℕ => ketbraNat 0 n) atTop 0 :=
      uwweaker_2 _ _ _ vn_counterexamples_4_ket
    rw [uwTendsto_iff] at huw ⊢
    intro ω
    have h := (continuous_star.tendsto ((ω (0 : ℓ² →L[ℂ] ℓ²)) : ℂ)).comp (huw ω)
    simp only [Function.comp_def] at h
    have hstar : ∀ n : ℕ, star (ω (ketbraNat 0 n) : ℂ) = ω (ketbraNat n 0) := by
      intro n
      rw [← npFunctional_star, star_ketbraNat]
    simp only [hstar] at h
    simpa using h
  · rintro ⟨T, hT⟩
    rw [usTendsto_iff] at hT
    have h := hT (vectorNP (lp.single 2 0 (1 : ℂ) : ℓ²))
    simp only [omegaNorm_vectorNP] at h
    have happ : ∀ n : ℕ, (ketbraNat n 0 - T) (lp.single 2 0 (1 : ℂ) : ℓ²)
        = (lp.single 2 n (1 : ℂ) : ℓ²) - T (lp.single 2 0 (1 : ℂ) : ℓ²) := by
      intro n
      rw [ContinuousLinearMap.sub_apply, ketbraNat_apply, inner_single_nat]
      simp
    simp only [happ] at h
    exact not_tendsto_single_sub _ (tendsto_id (x := (atTop : Filter ℕ))) h

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 4
(conclusion): `a ↦ a*` is not ultrastrongly continuous on `B(ℓ²)`. -/
theorem vn_counterexamples_4_star :
    ¬@Continuous (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²)
        (ultrastrong _) (ultrastrong _) star := by
  intro hcont
  refine vn_counterexamples_4_bra.2 ⟨0, ?_⟩
  have h0 : Filter.Tendsto (star : (ℓ² →L[ℂ] ℓ²) → (ℓ² →L[ℂ] ℓ²))
      (@nhds (ℓ² →L[ℂ] ℓ²) (ultrastrong _) 0)
      (@nhds (ℓ² →L[ℂ] ℓ²) (ultrastrong _) (star (0 : ℓ² →L[ℂ] ℓ²))) :=
    @Continuous.tendsto (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²) (ultrastrong _) (ultrastrong _)
      star hcont 0
  have h : USTendsto (fun n : ℕ => star (ketbraNat 0 n)) atTop
      (star (0 : ℓ² →L[ℂ] ℓ²)) := h0.comp vn_counterexamples_4_ket
  simpa only [star_zero, star_ketbraNat] using h

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 5: the unit
ball of `B(ℓ²)` is not ultrastrongly compact (the sequence `(|0⟩⟨n|)_n` has
no ultrastrongly convergent subnet). -/
theorem vn_counterexamples_5 :
    ¬@IsCompact (ℓ² →L[ℂ] ℓ²) (ultrastrong _)
        (Metric.closedBall (0 : ℓ² →L[ℂ] ℓ²) 1) := by
  intro hcpt
  -- `a ↦ a e₀` is ultrastrongly continuous, so the image of the ball is a
  -- compact — hence sequentially compact — subset of `ℓ²`
  have hcont : @Continuous (ℓ² →L[ℂ] ℓ²) ℓ² (ultrastrong _) _
      (fun a => a (lp.single 2 0 (1 : ℂ) : ℓ²)) := ultrastrong_continuous_apply _
  have himg : IsCompact ((fun a : ℓ² →L[ℂ] ℓ² => a (lp.single 2 0 (1 : ℂ) : ℓ²)) ''
      Metric.closedBall (0 : ℓ² →L[ℂ] ℓ²) 1) :=
    @IsCompact.image _ _ (ultrastrong (ℓ² →L[ℂ] ℓ²)) _ _ _ hcpt hcont
  have hmem : ∀ n : ℕ, (lp.single 2 n (1 : ℂ) : ℓ²) ∈
      (fun a : ℓ² →L[ℂ] ℓ² => a (lp.single 2 0 (1 : ℂ) : ℓ²)) ''
        Metric.closedBall (0 : ℓ² →L[ℂ] ℓ²) 1 := by
    intro n
    refine ⟨ketbraNat n 0, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using norm_ketbraNat_le_one n 0
    · show ketbraNat n 0 (lp.single 2 0 (1 : ℂ) : ℓ²) = (lp.single 2 n (1 : ℂ) : ℓ²)
      rw [ketbraNat_apply, inner_single_nat]
      simp
  obtain ⟨v, -, φ, hφ, hlim⟩ := himg.tendsto_subseq hmem
  refine not_tendsto_single_sub v hφ.tendsto_atTop ?_
  have := tendsto_iff_norm_sub_tendsto_zero.mp hlim
  simpa [Function.comp_def] using this

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6:
`|n⟩⟨0| + |0⟩⟨n| → 0` ultraweakly while its squares converge ultraweakly to
`|0⟩⟨0| ≠ 0`. -/
theorem vn_counterexamples_6 :
    UWTendsto (fun n : ℕ => ketbraNat n 0 + ketbraNat 0 n) atTop 0 ∧
      UWTendsto (fun n : ℕ => (ketbraNat n 0 + ketbraNat 0 n) ^ 2) atTop
        (ketbraNat 0 0) := by
  have h1 : UWTendsto (fun n : ℕ => ketbraNat n 0) atTop 0 :=
    vn_counterexamples_4_bra.1
  have h2 : UWTendsto (fun n : ℕ => ketbraNat 0 n) atTop 0 :=
    uwweaker_2 _ _ _ vn_counterexamples_4_ket
  have h3 : UWTendsto (fun n : ℕ => ketbraNat n n) atTop 0 :=
    uwweaker_2 _ _ _ vn_counterexamples_2_tendsto
  rw [uwTendsto_iff] at h1 h2 h3
  -- the computation rules of part 1: for `n ≠ 0` the two "diagonal" products
  -- vanish and `(|n⟩⟨0| + |0⟩⟨n|)² = |n⟩⟨n| + |0⟩⟨0|`
  have hsq : ∀ n : ℕ, n ≠ 0 →
      (ketbraNat n 0 + ketbraNat 0 n) ^ 2 = ketbraNat n n + ketbraNat 0 0 := by
    intro n hn
    rw [sq, add_mul, mul_add, mul_add, (vn_counterexamples_1 0 n 0 n).2,
      (vn_counterexamples_1 n 0 0 n).2, (vn_counterexamples_1 0 n n 0).2,
      (vn_counterexamples_1 n 0 n 0).2, if_neg (Ne.symm hn), if_pos rfl,
      if_pos rfl, if_neg hn]
    abel
  refine ⟨?_, ?_⟩
  · rw [uwTendsto_iff]
    intro ω
    have h := (h1 ω).add (h2 ω)
    simpa using h
  · rw [uwTendsto_iff]
    intro ω
    have hc : Tendsto (fun _ : ℕ => (ω (ketbraNat 0 0) : ℂ)) atTop
        (𝓝 (ω (ketbraNat 0 0) : ℂ)) := tendsto_const_nhds
    have h := (h3 ω).add hc
    rw [npFunctional_zero, zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← npFunctional_add, ← hsq n hn.ne']

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6
(conclusion): squaring — hence also multiplication jointly, `|·|`, and
`√·` (part 8) — is not ultraweakly continuous on `B(ℓ²)`. -/
theorem vn_counterexamples_6_sq :
    ¬@Continuous (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²) (ultraweak _) (ultraweak _)
        (fun a => a * a) := by
  intro hcont
  obtain ⟨h1, h2⟩ := vn_counterexamples_6
  have h0 : Filter.Tendsto (fun a : ℓ² →L[ℂ] ℓ² => a * a)
      (@nhds (ℓ² →L[ℂ] ℓ²) (ultraweak _) 0)
      (@nhds (ℓ² →L[ℂ] ℓ²) (ultraweak _) ((0 : ℓ² →L[ℂ] ℓ²) * 0)) :=
    @Continuous.tendsto (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²) (ultraweak _) (ultraweak _)
      _ hcont 0
  have hsq : UWTendsto (fun n : ℕ => (ketbraNat n 0 + ketbraNat 0 n) *
      (ketbraNat n 0 + ketbraNat 0 n)) atTop ((0 : ℓ² →L[ℂ] ℓ²) * 0) := h0.comp h1
  rw [mul_zero] at hsq
  have h2' : UWTendsto (fun n : ℕ => (ketbraNat n 0 + ketbraNat 0 n) *
      (ketbraNat n 0 + ketbraNat 0 n)) atTop (ketbraNat 0 0) := by
    simpa only [sq] using h2
  -- two ultraweak limits, tested against the vector functional at `e₀`
  rw [uwTendsto_iff] at hsq h2'
  set ω : NPFunctional (ℓ² →L[ℂ] ℓ²) := vectorNP (lp.single 2 0 (1 : ℂ) : ℓ²)
  have huniq : (ω (ketbraNat 0 0) : ℂ) = ω (0 : ℓ² →L[ℂ] ℓ²) :=
    tendsto_nhds_unique (h2' ω) (hsq ω)
  rw [npFunctional_zero] at huniq
  have hval : (ω (ketbraNat 0 0) : ℂ) = 1 := by
    show (⟪(lp.single 2 0 (1 : ℂ) : ℓ²),
      ketbraNat 0 0 (lp.single 2 0 (1 : ℂ) : ℓ²)⟫ : ℂ) = 1
    rw [ketbraNat_apply, inner_single_nat]
    simp
  rw [hval] at huniq
  exact one_ne_zero huniq

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6 (second
conclusion): multiplication is not *jointly* ultraweakly continuous on
`B(ℓ²)` — squaring is its composite with the (always continuous) diagonal,
and squaring is not ultraweakly continuous by `vn_counterexamples_6_sq`. -/
theorem vn_counterexamples_6_mul :
    ¬@Continuous ((ℓ² →L[ℂ] ℓ²) × (ℓ² →L[ℂ] ℓ²)) (ℓ² →L[ℂ] ℓ²)
        (@instTopologicalSpaceProd _ _ (ultraweak _) (ultraweak _))
        (ultraweak _) (fun p => p.1 * p.2) := by
  intro hcont
  let _ : TopologicalSpace (ℓ² →L[ℂ] ℓ²) := ultraweak _
  exact vn_counterexamples_6_sq (hcont.comp (continuous_id.prodMk continuous_id))

-- Instance synthesis does not find the (existing) real functional calculus
-- on the *concrete* algebra `B(ℓ²)` — it does for an abstract `H →L[ℂ] H` —
-- so the two instances `|·|` needs are named here by hand.  They are the
-- canonical Mathlib ones, so nothing is bent by naming them.
noncomputable local instance :
    ContinuousFunctionalCalculus ℝ (ℓ² →L[ℂ] ℓ²) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℝ (ℓ² →L[ℂ] ℓ²) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6 (third
conclusion): `| |n⟩⟨0| + |0⟩⟨n| | = |0⟩⟨0| + |n⟩⟨n|`.  (Both sides square to
the same positive element, and the positive square root is unique; the
computation rules are those of part 1.  The identity holds for `n = 0` too,
where both sides are `2|0⟩⟨0|`.) -/
theorem vn_counterexamples_6_abs (n : ℕ) :
    CFC.abs (ketbraNat n 0 + ketbraNat 0 n) = ketbraNat 0 0 + ketbraNat n n := by
  have hmul : ∀ p q r t : ℕ,
      ketbraNat p q * ketbraNat r t = if q = r then ketbraNat p t else 0 :=
    fun p q r t => (vn_counterexamples_1 t r q p).2
  have hproj : ∀ m : ℕ, (0 : ℓ² →L[ℂ] ℓ²) ≤ ketbraNat m m := by
    intro m
    have h := star_mul_self_nonneg (ketbraNat m m)
    rwa [star_ketbraNat, hmul m m m m, if_pos rfl] at h
  have hsa : IsSelfAdjoint (ketbraNat n 0 + ketbraNat 0 n) := by
    show star _ = _
    rw [star_add, star_ketbraNat, star_ketbraNat, add_comm]
  have hp : (0 : ℓ² →L[ℂ] ℓ²) ≤ ketbraNat 0 0 + ketbraNat n n :=
    add_nonneg (hproj 0) (hproj n)
  have hsq : (ketbraNat 0 0 + ketbraNat n n) * (ketbraNat 0 0 + ketbraNat n n)
      = (ketbraNat n 0 + ketbraNat 0 n) * (ketbraNat n 0 + ketbraNat 0 n) := by
    by_cases hn : n = 0
    · subst hn; rfl
    · simp only [mul_add, add_mul, hmul, if_neg hn, if_neg (Ne.symm hn),
        add_zero, zero_add]
  -- `|a|` is the unique positive element squaring to `a*a = a·a`
  refine (CFC.mul_self_eq_mul_self_iff _ _ (CFC.abs_nonneg _) hp).mp ?_
  rw [CFC.abs_mul_abs, hsa.star_eq]
  exact hsq.symm

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6 (fourth
conclusion): `a ↦ |a|` is not ultraweakly continuous on `sa(B(ℓ²))`.  The
self-adjoint elements `|n⟩⟨0| + |0⟩⟨n|` converge ultraweakly to `0`, while
their absolute values `|0⟩⟨0| + |n⟩⟨n|` converge ultraweakly to
`|0⟩⟨0| ≠ 0 = |0|`.  (Continuity is negated *on the self-adjoint part*, as
the exercise asks: `A/VN/Completeness`'s **74I** `proto_kaplansky` shows
`a ↦ |a|` *is* ultrastrongly continuous there.) -/
theorem vn_counterexamples_6_abs_cont :
    ¬@ContinuousOn (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²) (ultraweak _) (ultraweak _)
        (fun a => CFC.abs a) {a : ℓ² →L[ℂ] ℓ² | IsSelfAdjoint a} := by
  intro hcont
  -- `|·|` and the values it takes on the net are named *before* the
  -- ultraweak topology is made the ambient instance below: the functional
  -- calculus that defines `|·|` is the one of the *norm* topology.
  set f : (ℓ² →L[ℂ] ℓ²) → (ℓ² →L[ℂ] ℓ²) := fun a => CFC.abs a with hf
  set S : Set (ℓ² →L[ℂ] ℓ²) := {a : ℓ² →L[ℂ] ℓ² | IsSelfAdjoint a} with hS
  have habs : ∀ n : ℕ,
      f (ketbraNat n 0 + ketbraNat 0 n) = ketbraNat 0 0 + ketbraNat n n :=
    fun n => vn_counterexamples_6_abs n
  have hf0 : f (0 : ℓ² →L[ℂ] ℓ²) = 0 := CFC.abs_zero
  have hsa : ∀ n : ℕ, (ketbraNat n 0 + ketbraNat 0 n) ∈ S := by
    intro n
    show star _ = _
    rw [star_add, star_ketbraNat, star_ketbraNat, add_comm]
  have hzero : (0 : ℓ² →L[ℂ] ℓ²) ∈ S := IsSelfAdjoint.zero _
  let _ : TopologicalSpace (ℓ² →L[ℂ] ℓ²) := ultraweak _
  -- the net is self-adjoint and converges ultraweakly to `0`
  have h1 : UWTendsto (fun n : ℕ => ketbraNat n 0 + ketbraNat 0 n) atTop 0 :=
    vn_counterexamples_6.1
  have hwithin : Tendsto (fun n : ℕ => ketbraNat n 0 + ketbraNat 0 n) atTop
      (nhdsWithin (0 : ℓ² →L[ℂ] ℓ²) S) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1
      (Eventually.of_forall hsa)
  -- continuity would force `|aₙ| → |0| = 0` ultraweakly
  have hlim0 : UWTendsto (fun n : ℕ => f (ketbraNat n 0 + ketbraNat 0 n))
      atTop 0 := by
    have hcw : Tendsto f (nhdsWithin (0 : ℓ² →L[ℂ] ℓ²) S) (𝓝 (f 0)) :=
      hcont 0 hzero
    have h := hcw.comp hwithin
    rwa [hf0] at h
  -- but `|aₙ| = |0⟩⟨0| + |n⟩⟨n| → |0⟩⟨0|`
  have h3 : UWTendsto (fun n : ℕ => ketbraNat n n) atTop 0 :=
    uwweaker_2 _ _ _ vn_counterexamples_2_tendsto
  have hlim1 : UWTendsto (fun n : ℕ => f (ketbraNat n 0 + ketbraNat 0 n))
      atTop (ketbraNat 0 0) := by
    rw [uwTendsto_iff] at h3 ⊢
    intro ω
    have hc : Tendsto (fun _ : ℕ => (ω (ketbraNat 0 0) : ℂ)) atTop
        (𝓝 (ω (ketbraNat 0 0) : ℂ)) := tendsto_const_nhds
    have h := hc.add (h3 ω)
    rw [npFunctional_zero, add_zero] at h
    refine h.congr fun n => ?_
    rw [habs n, npFunctional_add]
  -- two ultraweak limits, tested against the vector functional at `e₀`
  rw [uwTendsto_iff] at hlim0 hlim1
  set ω : NPFunctional (ℓ² →L[ℂ] ℓ²) := vectorNP (lp.single 2 0 (1 : ℂ) : ℓ²)
  have huniq : (ω (ketbraNat 0 0) : ℂ) = ω (0 : ℓ² →L[ℂ] ℓ²) :=
    tendsto_nhds_unique (hlim1 ω) (hlim0 ω)
  rw [npFunctional_zero] at huniq
  have hval : (ω (ketbraNat 0 0) : ℂ) = 1 := by
    show (⟪(lp.single 2 0 (1 : ℂ) : ℓ²),
      ketbraNat 0 0 (lp.single 2 0 (1 : ℂ) : ℓ²)⟫ : ℂ) = 1
    rw [ketbraNat_apply, inner_single_nat]
    simp
  rw [hval] at huniq
  exact one_ne_zero huniq

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 11: `B(ℓ²)`
is not ultraweakly complete: there is an ultraweakly Cauchy net (built from
an unbounded functional on `ℓ²` via Riesz representation on finite
dimensional subspaces) with no ultraweak limit. -/
theorem vn_counterexamples_11 :
    ∃ (ι : Type) (l : Filter ι), l.NeBot ∧ ∃ x : ι → (ℓ² →L[ℂ] ℓ²),
      (∀ ω : NPFunctional (ℓ² →L[ℂ] ℓ²), Cauchy (l.map fun i => ω (x i))) ∧
      ¬∃ T, UWTendsto x l T := by
  classical
  set e : ℕ → ℓ² := fun n => lp.single 2 n (1 : ℂ) with he
  -- (a) an unbounded linear functional `f` on `ℓ²`, with `f eₙ = n`
  obtain ⟨f, hf⟩ : ∃ f : ℓ² →ₗ[ℂ] ℂ, ∀ n : ℕ, f (e n) = (n : ℂ) := by
    have hon : Orthonormal ℂ e := by
      rw [orthonormal_iff_ite]
      intro i j
      exact inner_single_nat i j
    have hli : LinearIndependent ℂ e := hon.linearIndependent
    obtain ⟨g, hg⟩ := ((Module.Basis.span hli).constr ℂ (fun n : ℕ => (n : ℂ))).exists_extend
    refine ⟨g, fun n => ?_⟩
    have h1 : ((Module.Basis.span hli n : ↥(Submodule.span ℂ (Set.range e))) : ℓ²) = e n :=
      Module.Basis.coe_span_apply hli n
    have h2 := LinearMap.congr_fun hg (Module.Basis.span hli n)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h1] at h2
    rw [h2, Module.Basis.constr_basis]
  -- (b) Riesz representation on the (finite-dimensional) span of a finite set
  have hriesz : ∀ F : Finset ℓ², ∃ x : ℓ²,
      ∀ y ∈ Submodule.span ℂ (F : Set ℓ²), f y = ⟪x, y⟫ := by
    intro F
    have hcs : CompleteSpace ↥(Submodule.span ℂ (F : Set ℓ²)) :=
      FiniteDimensional.complete ℂ _
    set S : Submodule ℂ ℓ² := Submodule.span ℂ (F : Set ℓ²) with hS
    set g : ↥S →ₗ[ℂ] ℂ := f.comp S.subtype with hgdef
    refine ⟨(((InnerProductSpace.toDual ℂ ↥S).symm g.toContinuousLinearMap : ↥S) : ℓ²),
      fun y hy => ?_⟩
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := ↥S)
      (y := g.toContinuousLinearMap) (x := (⟨y, hy⟩ : ↥S))
    rw [Submodule.coe_inner] at h
    have h2 : (⟪(((InnerProductSpace.toDual ℂ ↥S).symm g.toContinuousLinearMap : ↥S) : ℓ²),
        y⟫ : ℂ) = g ⟨y, hy⟩ := h
    rw [h2]
    rfl
  choose xv hxv using hriesz
  refine ⟨Finset ℓ², atTop, inferInstance,
    fun F => ketbra (e 0) (xv F), ?_, ?_⟩
  · -- (c) the net is ultraweakly Cauchy: `ω(|e⟩⟨x_F|)` is eventually constant
    intro ω
    obtain ⟨y, hy, hy1⟩ := bh_np ω
    have hsum2 : Summable (fun n : ℕ => ‖y n‖ ^ 2) := by
      exact Complex.summable_ofReal.mp hy1.summable
    have hsumz : Summable (fun n : ℕ => (⟪y n, e 0⟫ : ℂ) • y n) := by
      refine Summable.of_norm ((hsum2.mul_right ‖e 0‖).of_nonneg_of_le
        (fun n => norm_nonneg _) fun n => ?_)
      rw [norm_smul]
      calc ‖(⟪y n, e 0⟫ : ℂ)‖ * ‖y n‖ ≤ (‖y n‖ * ‖e 0‖) * ‖y n‖ :=
            mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
        _ = ‖y n‖ ^ 2 * ‖e 0‖ := by ring
    have hz : ∀ v : ℓ², (ω (ketbra (e 0) v) : ℂ) = ⟪v, ∑' n, (⟪y n, e 0⟫ : ℂ) • y n⟫ := by
      intro v
      refine HasSum.unique (hy (ketbra (e 0) v)) ?_
      have h := (hsumz.hasSum).mapL (innerSL ℂ v)
      refine h.congr_fun fun n => ?_
      show (⟪y n, ketbra (e 0) v (y n)⟫ : ℂ) = ⟪v, (⟪y n, e 0⟫ : ℂ) • y n⟫
      show (⟪y n, (⟪v, y n⟫ : ℂ) • e 0⟫ : ℂ) = ⟪v, (⟪y n, e 0⟫ : ℂ) • y n⟫
      rw [inner_smul_right, inner_smul_right]
      ring
    refine Filter.Tendsto.cauchy_map (a := f (∑' n, (⟪y n, e 0⟫ : ℂ) • y n)) ?_
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, Filter.eventually_atTop]
    refine ⟨{∑' n, (⟪y n, e 0⟫ : ℂ) • y n}, fun F hF => ?_⟩
    have hmem : (∑' n, (⟪y n, e 0⟫ : ℂ) • y n) ∈ Submodule.span ℂ (F : Set ℓ²) :=
      Submodule.subset_span (hF (Finset.mem_singleton_self _))
    rw [hz (xv F), ← hxv F _ hmem]
  · -- (d) but it has no ultraweak limit
    rintro ⟨T, hT⟩
    rw [uwTendsto_iff] at hT
    have key : ∀ n : ℕ, 1 ≤ n → (n : ℂ) = ⟪e n + e 0, T (e n + e 0)⟫ := by
      intro n hn
      have hne : ¬ (n = 0) := by omega
      have hw : (⟪e n + e 0, e 0⟫ : ℂ) = 1 := by
        rw [inner_add_left, he]
        simp only []
        rw [inner_single_nat n 0, inner_single_nat 0 0]
        simp [hne]
      have happ : ∀ v : ℓ²,
          (vectorNP (e n + e 0) (ketbra (e 0) v) : ℂ) = ⟪v, e n + e 0⟫ := by
        intro v
        rw [vectorNP_apply]
        show (⟪e n + e 0, (⟪v, e n + e 0⟫ : ℂ) • e 0⟫ : ℂ) = ⟪v, e n + e 0⟫
        rw [inner_smul_right, hw, mul_one]
      have h1 := hT (vectorNP (e n + e 0))
      have h2 : Tendsto (fun F : Finset ℓ² =>
          (vectorNP (e n + e 0) (ketbra (e 0) (xv F)) : ℂ)) atTop (𝓝 (f (e n + e 0))) := by
        refine tendsto_const_nhds.congr' ?_
        rw [EventuallyEq, Filter.eventually_atTop]
        refine ⟨{e n + e 0}, fun F hF => ?_⟩
        have hmem : (e n + e 0) ∈ Submodule.span ℂ (F : Set ℓ²) :=
          Submodule.subset_span (hF (Finset.mem_singleton_self _))
        rw [happ, ← hxv F _ hmem]
      have h3 := tendsto_nhds_unique h2 h1
      rw [vectorNP_apply] at h3
      rw [← h3, map_add, hf n, hf 0]
      simp
    -- but `|⟪w, Tw⟫| ≤ ‖T‖‖w‖² ≤ 4‖T‖`
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (4 * ‖T‖))
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) ≤ n := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
      exact_mod_cast this
    have hnorm : ‖e n + e 0‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [he]
      simp only []
      rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num)]
      norm_num
    have hbd : (n : ℝ) ≤ 4 * ‖T‖ := by
      have h1 : ‖(⟪e n + e 0, T (e n + e 0)⟫ : ℂ)‖ ≤ ‖e n + e 0‖ * ‖T (e n + e 0)‖ :=
        norm_inner_le_norm _ _
      have h2 : ‖T (e n + e 0)‖ ≤ ‖T‖ * ‖e n + e 0‖ := T.le_opNorm _
      have h3 : ((n : ℝ)) = ‖(⟪e n + e 0, T (e n + e 0)⟫ : ℂ)‖ := by
        rw [← key n hn1]; simp
      rw [h3]
      nlinarith [norm_nonneg (e n + e 0), norm_nonneg (T (e n + e 0)),
        norm_nonneg T, hnorm, h1, h2]
    have := lt_of_le_of_lt (le_max_right (1 : ℝ) (4 * ‖T‖)) hn
    linarith

/-! **43II**, parts 7–10 (the maps `|·|_s`, `|·|_r` and squaring are not
ultrastrongly continuous, and multiplication is not jointly ultrastrongly
continuous even with the second argument bounded — via the "growing moving
bump" net) are skipped: they require ad-hoc directed index sets whose
formalization adds bulk without adding a reusable statement; their positive
counterparts are 74I (`proto_kaplansky`) and 45VI (`mult_jus_cont`). -/

end Counterexamples

/-! ## Parsec 440: elementary theory

**44I** (vn.tex:624): introduction — nothing to formalize. -/

omit [PartialOrder A] [StarOrderedRing A] in
/-- **44II** (`mult-polarization`, vn.tex:643, Exercise): the polarisation
identity `a* c b = ¼ ∑_{k<4} iᵏ (iᵏa + b)* c (iᵏa + b)` in a C*-algebra. -/
theorem mult_polarization (a b c : A) :
    star a * c * b =
      (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4, Complex.I ^ k •
        (star ((Complex.I ^ k : ℂ) • a + b) * c *
          ((Complex.I ^ k : ℂ) • a + b)) := by
  simp [Finset.sum_range_succ, star_add, star_smul, add_mul, mul_add,
    smul_smul]
  match_scalars <;> norm_num [pow_succ, Complex.I_mul_I]

/-- **44III** (`vanishing-effects`, vn.tex:654, Lemma): if a net `(x_α)_α` of
effects converges ultraweakly to `0` and `(b_α)_α` is a net with
`‖b_α‖ ≤ 1`, then `(x_α b_α)_α` converges ultraweakly to `0`. -/
theorem vanishing_effects [VonNeumannAlgebra A] {ι : Type*} {l : Filter ι}
    (x b : ι → A) (hx : ∀ i, x i ∈ effects A) (hb : ∀ i, ‖b i‖ ≤ 1)
    (h : UWTendsto x l 0) : UWTendsto (fun i => x i * b i) l 0 := by
  -- The thesis's estimate, for an np-map `ω`:
  --   |ω(xₐbₐ)|² = |ω(√xₐ · √xₐbₐ)|² ≤ ω(xₐ) ω(bₐ* xₐ bₐ)
  --                                  ≤ ω(xₐ) ω(bₐ* bₐ) ≤ ω(xₐ) ω(1).
  rw [uwTendsto_iff] at h ⊢
  intro ω
  have hω0 : (ω 0 : ℂ) = 0 := map_zero ω.toPositiveLinearMap
  have key : ∀ i, ‖ω (x i * b i)‖ ≤
      Real.sqrt (ω (x i)).re * Real.sqrt (ω 1).re := by
    intro i
    have hxi1 : x i ≤ 1 := (hx i).2
    have hu0 : (0 : A) ≤ CFC.sqrt (x i) := CFC.sqrt_nonneg (x i)
    have husa : star (CFC.sqrt (x i)) = CFC.sqrt (x i) :=
      (IsSelfAdjoint.of_nonneg hu0).star_eq
    have huu : CFC.sqrt (x i) * CFC.sqrt (x i) = x i :=
      CFC.sqrt_mul_sqrt_self (x i) (hx i).1
    have h1 : star (CFC.sqrt (x i)) * (CFC.sqrt (x i) * b i) = x i * b i := by
      rw [husa, ← mul_assoc, huu]
    have h2 : omegaNorm A ω (CFC.sqrt (x i)) = Real.sqrt (ω (x i)).re := by
      rw [omegaNorm, husa, huu]
    have hbb : star (b i) * b i ≤ 1 := by
      refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp ?_
      rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg (b i), hb i]
    have h3 : omegaNorm A ω (CFC.sqrt (x i) * b i) ≤ Real.sqrt (ω 1).re := by
      refine (omegaNorm_le_omegaNorm ω (v := 1) ?_).trans_eq (omegaNorm_one ω)
      rw [star_one, one_mul, star_mul, husa]
      calc star (b i) * CFC.sqrt (x i) * (CFC.sqrt (x i) * b i)
          = star (b i) * x i * b i := by
            rw [mul_assoc, ← mul_assoc (CFC.sqrt (x i)), huu, ← mul_assoc]
        _ ≤ star (b i) * 1 * b i := star_left_conjugate_le_conjugate hxi1 (b i)
        _ ≤ 1 := by rw [mul_one]; exact hbb
    calc ‖ω (x i * b i)‖
        = ‖ω (star (CFC.sqrt (x i)) * (CFC.sqrt (x i) * b i))‖ := by rw [h1]
      _ ≤ omegaNorm A ω (CFC.sqrt (x i)) *
            omegaNorm A ω (CFC.sqrt (x i) * b i) := norm_apply_star_mul_le ω _ _
      _ ≤ Real.sqrt (ω (x i)).re * Real.sqrt (ω 1).re := by
            rw [h2]
            exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  have hx0 : Tendsto (fun i => ω (x i)) l (𝓝 0) := by
    have := h ω
    rwa [hω0] at this
  have hsq : Tendsto (fun i => Real.sqrt (ω (x i)).re) l (𝓝 0) := by
    have h1 : Tendsto (fun i => (ω (x i)).re) l (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_re.tendsto (0 : ℂ)).comp hx0
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
  rw [hω0]
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero (fun i => norm_nonneg _) key ?_
  simpa using hsq.mul_const (Real.sqrt (ω 1).re)

/-- **44VI** (`vna-supremum-uwlimit`, vn.tex:692): for a bounded directed set
`D` of self-adjoint elements, the net `(d)_{d∈D}` converges ultraweakly to
`⋁D`. -/
theorem vna_supremum_uwlimit [VonNeumannAlgebra A] (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    UWTendsto (fun d : D => (d : A)) atTop ((dirSup D h : selfAdjoint A) : A) := by
  -- for an np-map `ω`, `(ω d)_{d∈D}` is a monotone net of reals with
  -- supremum `ω(⋁D)` by normality of `ω`, hence converges to it
  rw [uwTendsto_iff]
  intro ω
  have hlub : IsLUB D (dirSup D h) := isLUB_dirSup D h
  have hω : IsLUB ((fun d : selfAdjoint A => ω (d : A)) '' D)
      (ω ((dirSup D h : selfAdjoint A) : A)) :=
    ω.preservesDirSups' D (dirSup D h) h.1 h.2.1 hlub
  have himg : ∀ w ∈ (fun d : selfAdjoint A => ω (d : A)) '' D, w.im = 0 := by
    rintro w ⟨d, -, rfl⟩
    exact npFunctional_im_eq_zero ω d.2
  have hre := isLUB_re_of_isLUB himg hω
  have hrange : Complex.re '' ((fun d : selfAdjoint A => ω (d : A)) '' D) =
      Set.range fun d : D => (ω ((d : selfAdjoint A) : A)).re := by
    rw [← Set.image_comp]
    exact (Set.image_eq_range _ _).trans rfl
  rw [hrange] at hre
  have hmono : Monotone fun d : D => (ω ((d : selfAdjoint A) : A)).re := by
    intro d₁ d₂ hd
    exact (Complex.le_def.mp (ω.toPositiveLinearMap.monotone
      (Subtype.coe_le_coe.mpr hd))).1
  have hlim := tendsto_atTop_isLUB hmono hre
  have hcast : ∀ z : ℂ, z.im = 0 → ((z.re : ℂ)) = z := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have := (Complex.continuous_ofReal.tendsto _).comp hlim
  simp only [Function.comp_def] at this
  rw [hcast _ (npFunctional_im_eq_zero ω (dirSup D h).2)] at this
  refine this.congr fun d => ?_
  exact hcast _ (npFunctional_im_eq_zero ω (d : selfAdjoint A).2)

/-- **44VII** (`vna-supremum-mult`, vn.tex:695): for a bounded directed `D`
and `a ∈ A`, `(d·a)_d` converges ultraweakly to `(⋁D)·a` and `(a*·d)_d` to
`a*·(⋁D)`. -/
theorem vna_supremum_mult [VonNeumannAlgebra A] (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) (a : A) :
    UWTendsto (fun d : D => (d : A) * a) atTop
        (((dirSup D h : selfAdjoint A) : A) * a) ∧
      UWTendsto (fun d : D => star a * (d : A)) atTop
        (star a * ((dirSup D h : selfAdjoint A) : A)) := by
  -- The thesis's hint is to use `vanishing_effects`; concretely we use the
  -- estimate behind it, `|ω((⋁D-d)a)| ≤ ω(⋁D-d)^½ ω(a*(⋁D-d)a)^½`, whose
  -- second factor is *eventually* bounded because `a*(⋁D-d)a` decreases.
  obtain ⟨d₀, hd₀⟩ := h.1
  set s : A := ((dirSup D h : selfAdjoint A) : A) with hs
  have hle : ∀ d ∈ D, ((d : selfAdjoint A) : A) ≤ s := fun d hd =>
    Subtype.coe_le_coe.mpr ((isLUB_dirSup D h).1 hd)
  -- the key limit: `ω((⋁D - d)a) → 0` for every np-functional `ω`
  have main : ∀ ω : NPFunctional A,
      Tendsto (fun d : D => ω ((s - ((d : selfAdjoint A) : A)) * a)) atTop
        (𝓝 0) := by
    intro ω
    set K : ℝ := (ω (star a * (s - ((d₀ : selfAdjoint A) : A)) * a)).re with hK
    have hbound : ∀ᶠ d : D in atTop,
        ‖ω ((s - ((d : selfAdjoint A) : A)) * a)‖ ≤
          Real.sqrt (ω (s - ((d : selfAdjoint A) : A))).re * Real.sqrt K := by
      filter_upwards [eventually_ge_atTop (⟨d₀, hd₀⟩ : D)] with d hdd
      refine (norm_apply_mul_le_of_nonneg ω
        (sub_nonneg.mpr (hle d d.2)) a).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine Real.sqrt_le_sqrt ?_
      refine (Complex.le_def.mp (ω.toPositiveLinearMap.monotone ?_)).1
      refine star_left_conjugate_le_conjugate ?_ a
      exact sub_le_sub_left (Subtype.coe_le_coe.mpr (Subtype.coe_le_coe.mpr hdd)) s
    have hω := (uwTendsto_iff _ _ _).mp (vna_supremum_uwlimit D h) ω
    have hsub : Tendsto (fun d : D => ω (s - ((d : selfAdjoint A) : A))) atTop
        (𝓝 0) := by
      have := (tendsto_const_nhds (x := ω s) (f := (atTop : Filter D))).sub hω
      simpa [← hs] using this
    have hsq : Tendsto
        (fun d : D => Real.sqrt (ω (s - ((d : selfAdjoint A) : A))).re) atTop
        (𝓝 0) := by
      have h1 : Tendsto
          (fun d : D => (ω (s - ((d : selfAdjoint A) : A))).re) atTop (𝓝 0) := by
        simpa [Function.comp_def] using
          (Complex.continuous_re.tendsto (0 : ℂ)).comp hsub
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _) hbound ?_
    simpa using hsq.mul_const (Real.sqrt K)
  constructor
  · rw [uwTendsto_iff]
    intro ω
    have h1 := main ω
    have h2 : ∀ d : D, ω ((s - ((d : selfAdjoint A) : A)) * a)
        = ω (s * a) - ω (((d : selfAdjoint A) : A) * a) := by
      intro d
      rw [sub_mul, npFunctional_sub]
    simp only [h2] at h1
    have := (tendsto_const_nhds (x := ω (s * a)) (f := (atTop : Filter D))).sub h1
    simpa using this
  · rw [uwTendsto_iff]
    intro ω
    -- take adjoints: `ω(a*(⋁D-d)) = conj ω((⋁D-d)a)` as `⋁D-d` is self-adjoint
    have h1 := main ω
    have hstar : ∀ d : D, star a * (s - ((d : selfAdjoint A) : A))
        = star ((s - ((d : selfAdjoint A) : A)) * a) := by
      intro d
      rw [star_mul, star_sub, hs, selfAdjoint.star_val_eq,
        selfAdjoint.star_val_eq]
    have h2 : ∀ d : D, ω (star a * (s - ((d : selfAdjoint A) : A)))
        = star (ω ((s - ((d : selfAdjoint A) : A)) * a)) := by
      intro d
      rw [hstar d]
      exact map_star ω.toPositiveLinearMap _
    have h3 : Tendsto
        (fun d : D => ω (star a * (s - ((d : selfAdjoint A) : A)))) atTop
        (𝓝 0) := by
      simp only [h2]
      simpa [Function.comp_def] using
        (Complex.continuous_conj.tendsto (0 : ℂ)).comp h1
    have h4 : ∀ d : D, ω (star a * (s - ((d : selfAdjoint A) : A)))
        = ω (star a * s) - ω (star a * ((d : selfAdjoint A) : A)) := by
      intro d
      rw [mul_sub, npFunctional_sub]
    simp only [h4] at h3
    have := (tendsto_const_nhds (x := ω (star a * s))
      (f := (atTop : Filter D))).sub h3
    simpa using this

section AdNormal

/-- Conjugation `d ↦ a* d a` as a map on the self-adjoint part. -/
private def conjSA (a : A) (d : selfAdjoint A) : selfAdjoint A :=
  ⟨star a * (d : A) * a, by
    change star (star a * (d : A) * a) = star a * (d : A) * a
    simp [star_mul, d.2.star_eq, mul_assoc]⟩

omit [PartialOrder A] [StarOrderedRing A] in
private theorem conjSA_coe (a : A) (d : selfAdjoint A) :
    ((conjSA a d : selfAdjoint A) : A) = star a * (d : A) * a := rfl

private theorem conjSA_mono (a : A) : Monotone (conjSA a) := fun _ _ hd =>
  Subtype.coe_le_coe.mp
    (star_left_conjugate_le_conjugate (Subtype.coe_le_coe.mpr hd) a)

/-- **44VIII** (`ad-normal-1`, vn.tex:713): for invertible `a` the map
`b ↦ a* b a` is an order isomorphism (with inverse `b ↦ (a⁻¹)* b a⁻¹`) and
therefore preserves all suprema. -/
private theorem conjSA_isLUB_of_isUnit {a : A} (ha : IsUnit a)
    {D : Set (selfAdjoint A)} {s : selfAdjoint A} (hlub : IsLUB D s) :
    IsLUB (conjSA a '' D) (conjSA a s) := by
  obtain ⟨w, rfl⟩ := ha
  have hinv : ∀ (x : A) (d : selfAdjoint A),
      x * ((w : A)) = 1 → ((w : A)) * x = 1 →
        conjSA x (conjSA ((w : A)) d) = d := by
    intro x d hxw hwx
    refine Subtype.ext ?_
    change star x * (star (w : A) * (d : A) * (w : A)) * x = (d : A)
    calc star x * (star (w : A) * (d : A) * (w : A)) * x
        = star ((w : A) * x) * (d : A) * ((w : A) * x) := by
          rw [star_mul]; noncomm_ring
      _ = (d : A) := by rw [hwx, star_one, one_mul, mul_one]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact conjSA_mono _ (hlub.1 hd)
  · intro v hv
    have hb1 : ((w⁻¹ : Aˣ) : A) * ((w : A)) = 1 := w.inv_mul
    have hb2 : ((w : A)) * ((w⁻¹ : Aˣ) : A) = 1 := w.mul_inv
    have hup : ∀ d ∈ D, d ≤ conjSA ((w⁻¹ : Aˣ) : A) v := by
      intro d hd
      have h1 : conjSA ((w : A)) d ≤ v := hv ⟨d, hd, rfl⟩
      have h2 := conjSA_mono ((w⁻¹ : Aˣ) : A) h1
      rwa [hinv _ d hb1 hb2] at h2
    have h3 := conjSA_mono ((w : A)) (hlub.2 hup)
    have h4 : conjSA ((w : A)) (conjSA ((w⁻¹ : Aˣ) : A) v) = v := by
      refine Subtype.ext ?_
      change star ((w : A)) * (star ((w⁻¹ : Aˣ) : A) * (v : A) * ((w⁻¹ : Aˣ) : A))
          * ((w : A)) = (v : A)
      calc star ((w : A)) * (star ((w⁻¹ : Aˣ) : A) * (v : A) * ((w⁻¹ : Aˣ) : A))
              * ((w : A))
          = star (((w⁻¹ : Aˣ) : A) * ((w : A))) * (v : A)
              * (((w⁻¹ : Aˣ) : A) * ((w : A))) := by
            rw [star_mul]; noncomm_ring
        _ = (v : A) := by rw [hb1, star_one, one_mul, mul_one]
    rwa [h4] at h3

/-- Generalisation of the argument of **44VI**: for a monotone
`g : sa(A) → sa(A)` sending a nonempty directed `D` to a set with supremum
`y`, the net `(ω(g d))_{d ∈ D}` converges to `ω(y)`. -/
private theorem tendsto_npFunctional_of_isLUB {D : Set (selfAdjoint A)}
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (g : selfAdjoint A → selfAdjoint A) (hmono : Monotone g)
    {y : selfAdjoint A} (hlub : IsLUB (g '' D) y) (ω : NPFunctional A) :
    Tendsto (fun d : D => ω ((g (d : selfAdjoint A) : selfAdjoint A) : A)) atTop
      (𝓝 (ω (y : A))) := by
  have hne' : (g '' D).Nonempty := hne.image g
  have hdir' : DirectedOn (· ≤ ·) (g '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
    exact ⟨g u, ⟨u, hu, rfl⟩, hmono hxu, hmono hzu⟩
  have hω : IsLUB ((fun e : selfAdjoint A => ω (e : A)) '' (g '' D))
      (ω (y : A)) :=
    ω.preservesDirSups' (g '' D) y hne' hdir' hlub
  have himg : ∀ w ∈ (fun e : selfAdjoint A => ω (e : A)) '' (g '' D),
      w.im = 0 := by
    rintro w ⟨e, -, rfl⟩
    exact npFunctional_im_eq_zero ω e.2
  have hre := isLUB_re_of_isLUB himg hω
  have hrange :
      Complex.re '' ((fun e : selfAdjoint A => ω (e : A)) '' (g '' D)) =
        Set.range fun d : D =>
          (ω ((g (d : selfAdjoint A) : selfAdjoint A) : A)).re := by
    rw [← Set.image_comp, ← Set.image_comp]
    exact (Set.image_eq_range _ _).trans rfl
  rw [hrange] at hre
  have hmono' : Monotone fun d : D =>
      (ω ((g (d : selfAdjoint A) : selfAdjoint A) : A)).re := by
    intro d₁ d₂ hd
    exact (Complex.le_def.mp (ω.toPositiveLinearMap.monotone
      (Subtype.coe_le_coe.mpr (hmono hd)))).1
  have hlim := tendsto_atTop_isLUB hmono' hre
  have hcast : ∀ z : ℂ, z.im = 0 → ((z.re : ℂ)) = z := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have h2 := (Complex.continuous_ofReal.tendsto _).comp hlim
  simp only [Function.comp_def] at h2
  rw [hcast _ (npFunctional_im_eq_zero ω y.2)] at h2
  refine h2.congr fun d => ?_
  exact hcast _ (npFunctional_im_eq_zero ω (g (d : selfAdjoint A)).2)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Every element of a unital C*-algebra becomes invertible after adding a
large enough positive scalar (cstar.tex `spectrum-bounded`). -/
private theorem exists_isUnit_smul_one_add (a : A) :
    ∃ l : ℝ, 0 < l ∧ IsUnit (((l : ℂ)) • (1 : A) + a) := by
  refine ⟨‖a‖ + 1, by positivity, ?_⟩
  set l : ℝ := ‖a‖ + 1 with hl
  have hl0 : (0 : ℝ) < l := by positivity
  have hlne : ((l : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hl0
  have hnorm : ‖-(((l : ℂ))⁻¹ • a)‖ < 1 := by
    rw [norm_neg, norm_smul, norm_inv]
    have hln : ‖((l : ℂ))‖ = l := by
      simp [Complex.norm_real, abs_of_pos hl0]
    rw [hln, inv_mul_lt_one₀ hl0]
    simp [hl]
  have hunit : IsUnit ((1 : A) - -(((l : ℂ))⁻¹ • a)) :=
    (Units.oneSub _ hnorm).isUnit
  have hscal : IsUnit (((l : ℂ)) • (1 : A)) := by
    have : ((l : ℂ)) • (1 : A) = algebraMap ℂ A ((l : ℂ)) := by
      rw [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact (Ne.isUnit hlne).map (algebraMap ℂ A)
  have heq : ((l : ℂ)) • (1 : A) + a
      = (((l : ℂ)) • (1 : A)) * ((1 : A) - -(((l : ℂ))⁻¹ • a)) := by
    rw [sub_neg_eq_add, mul_add, mul_one, smul_mul_assoc, one_mul, smul_smul,
      mul_inv_cancel₀ hlne, one_smul]
  rw [heq]
  exact hscal.mul hunit

/-- **44VIII** (`ad-normal`, vn.tex:704, Proposition):
`⋁_{d∈D} a* d a = a* (⋁D) a` for every bounded directed set `D` of
self-adjoint elements and every `a ∈ A` (stated as an `IsLUB` in `A`; upper
bounds of sets of self-adjoint elements are automatically self-adjoint). -/
theorem ad_normal [VonNeumannAlgebra A] (a : A) (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    IsLUB ((fun d : selfAdjoint A => star a * (d : A) * a) '' D)
      (star a * ((dirSup D h : selfAdjoint A) : A) * a) := by
  obtain ⟨d₀, hd₀⟩ := h.1
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp h.2.1
  set s : selfAdjoint A := dirSup D h with hs
  have hlubD : IsLUB D s := isLUB_dirSup D h
  -- the conjugated set, its supremum `t`, and `t ≤ a* (⋁D) a`
  have hEne : (conjSA a '' D).Nonempty := ⟨conjSA a d₀, d₀, hd₀, rfl⟩
  have hEdir : DirectedOn (· ≤ ·) (conjSA a '' D) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hxu, hzu⟩ := h.2.1 x hx z hz
    exact ⟨conjSA a u, ⟨u, hu, rfl⟩, conjSA_mono a hxu, conjSA_mono a hzu⟩
  have hEub : conjSA a s ∈ upperBounds (conjSA a '' D) := by
    rintro _ ⟨d, hd, rfl⟩
    exact conjSA_mono a (hlubD.1 hd)
  have hEbdd : BddAbove (conjSA a '' D) := ⟨_, hEub⟩
  set t : selfAdjoint A := dirSup (conjSA a '' D) ⟨hEne, hEdir, hEbdd⟩ with ht
  have hlubE : IsLUB (conjSA a '' D) t := isLUB_dirSup _ _
  have hts : t ≤ conjSA a s := hlubE.2 hEub
  -- `a* (⋁D) a = t`, because their difference is positive and killed by every
  -- np-functional
  have hkey : conjSA a s = t := by
    refine Subtype.ext (sub_eq_zero.mp ?_)
    refine VonNeumannAlgebra.np_faithful _
      (sub_nonneg.mpr (Subtype.coe_le_coe.mpr hts)) (fun ω => ?_)
    obtain ⟨l, hl, hu⟩ := exists_isUnit_smul_one_add a
    set c : A := ((l : ℂ)) • (1 : A) + a with hc
    have hsc : star c = ((l : ℂ)) • (1 : A) + star a := by
      rw [hc, star_add, star_smul, star_one, Complex.star_def,
        Complex.conj_ofReal]
    -- the thesis's decomposition
    have hdecomp : ∀ d : selfAdjoint A,
        ω (star a * (d : A) * a)
          = ω ((conjSA c d : selfAdjoint A) : A)
            - (((l : ℂ)) * ((l : ℂ))) * ω (d : A)
            - ((l : ℂ)) * ω ((d : A) * a)
            - ((l : ℂ)) * ω (star a * (d : A)) := by
      intro d
      have hid : ((conjSA c d : selfAdjoint A) : A)
          = (((l : ℂ)) * ((l : ℂ))) • (d : A) + ((l : ℂ)) • ((d : A) * a)
            + ((l : ℂ)) • (star a * (d : A)) + star a * (d : A) * a := by
        rw [conjSA_coe, hsc, hc]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one, mul_assoc]
        module
      have hadd : ∀ x y : A, ω (x + y) = ω x + ω y := fun x y =>
        map_add ω.toPositiveLinearMap x y
      have hsmul : ∀ (r : ℂ) (x : A), ω (r • x) = r * ω x := by
        intro r x
        rw [show ω (r • x) = r • ω x from map_smul ω.toPositiveLinearMap r x,
          smul_eq_mul]
      rw [hid]
      simp only [hadd, hsmul]
      ring
    -- the four limits
    have h1 : Tendsto (fun d : D =>
        ω ((conjSA c (d : selfAdjoint A) : selfAdjoint A) : A)) atTop
        (𝓝 (ω ((conjSA c s : selfAdjoint A) : A))) :=
      tendsto_npFunctional_of_isLUB ⟨d₀, hd₀⟩ h.2.1 (conjSA c) (conjSA_mono c)
        (conjSA_isLUB_of_isUnit hu hlubD) ω
    have h2 : Tendsto (fun d : D => ω ((d : selfAdjoint A) : A)) atTop
        (𝓝 (ω (s : A))) := by
      have hx := vna_supremum_uwlimit D h
      rw [uwTendsto_iff] at hx
      exact hx ω
    have h3 : Tendsto (fun d : D => ω (((d : selfAdjoint A) : A) * a)) atTop
        (𝓝 (ω ((s : A) * a))) := by
      have hx := (vna_supremum_mult D h a).1
      rw [uwTendsto_iff] at hx
      exact hx ω
    have h4 : Tendsto (fun d : D => ω (star a * ((d : selfAdjoint A) : A)))
        atTop (𝓝 (ω (star a * (s : A)))) := by
      have hx := (vna_supremum_mult D h a).2
      rw [uwTendsto_iff] at hx
      exact hx ω
    have hlim : Tendsto
        (fun d : D => ω (star a * ((d : selfAdjoint A) : A) * a)) atTop
        (𝓝 (ω (star a * (s : A) * a))) := by
      have hcomb :=
        Filter.Tendsto.sub
          (Filter.Tendsto.sub
            (Filter.Tendsto.sub h1
              (Filter.Tendsto.const_mul (((l : ℂ)) * ((l : ℂ))) h2))
            (Filter.Tendsto.const_mul ((l : ℂ)) h3))
          (Filter.Tendsto.const_mul ((l : ℂ)) h4)
      rw [← hdecomp s] at hcomb
      exact hcomb.congr fun d => (hdecomp _).symm
    -- `ω(a* d a) ≤ ω(t)` for every `d`, hence in the limit
    have hbnd : ∀ d : D, (ω (star a * ((d : selfAdjoint A) : A) * a)).re
        ≤ (ω (t : A)).re := by
      intro d
      exact (Complex.le_def.mp (ω.toPositiveLinearMap.monotone
        (Subtype.coe_le_coe.mpr (hlubE.1 ⟨(d : selfAdjoint A), d.2, rfl⟩)))).1
    have hre_le : (ω (star a * (s : A) * a)).re ≤ (ω (t : A)).re :=
      le_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
        (Eventually.of_forall hbnd)
    have hre_ge : (ω (t : A)).re ≤ (ω (star a * (s : A) * a)).re :=
      (Complex.le_def.mp (ω.toPositiveLinearMap.monotone
        (Subtype.coe_le_coe.mpr hts))).1
    rw [npFunctional_sub]
    refine Complex.ext ?_ ?_
    · simp only [Complex.sub_re, Complex.zero_re, sub_eq_zero]
      exact le_antisymm hre_le hre_ge
    · simp only [Complex.sub_im, Complex.zero_im, sub_eq_zero]
      rw [npFunctional_im_eq_zero ω (conjSA a s).2,
        npFunctional_im_eq_zero ω t.2]
  -- transfer the `IsLUB` from `sa(A)` to `A`
  have himg : (fun d : selfAdjoint A => star a * (d : A) * a) '' D
      = Subtype.val '' (conjSA a '' D) := by
    rw [← Set.image_comp]
    rfl
  rw [himg]
  have hgoal : star a * (s : A) * a = ((t : selfAdjoint A) : A) := by
    rw [← conjSA_coe, hkey]
  rw [hgoal]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact Subtype.coe_le_coe.mpr (hlubE.1 he)
  · intro u hu
    have hu0 : ((conjSA a d₀ : selfAdjoint A) : A) ≤ u :=
      hu ⟨conjSA a d₀, ⟨d₀, hd₀, rfl⟩, rfl⟩
    have husa : IsSelfAdjoint u := by
      have hd : IsSelfAdjoint (u - ((conjSA a d₀ : selfAdjoint A) : A)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu0)
      simpa using hd.add (conjSA a d₀).2
    have hub : (⟨u, husa⟩ : selfAdjoint A) ∈ upperBounds (conjSA a '' D) :=
      fun e he => hu ⟨e, he, rfl⟩
    exact hlubE.2 hub

/-- **44VIII** in the form needed below: conjugation by `a` preserves the
suprema of bounded directed sets, stated on `sa(A)`. -/
private theorem conjSA_isLUB [VonNeumannAlgebra A] (a : A)
    {D : Set (selfAdjoint A)} {s : selfAdjoint A} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (conjSA a '' D) (conjSA a s) := by
  have h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D :=
    ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hs : dirSup D h = s := (isLUB_dirSup D h).unique hlub
  have hA := ad_normal a D h
  rw [hs] at hA
  have himg : (fun d : selfAdjoint A => star a * (d : A) * a) '' D
      = Subtype.val '' (conjSA a '' D) := by
    rw [← Set.image_comp]; rfl
  rw [himg, ← conjSA_coe a s] at hA
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mp (hA.1 ⟨conjSA a d, ⟨d, hd, rfl⟩, rfl⟩)
  · intro v hv
    refine Subtype.coe_le_coe.mp (hA.2 ?_)
    rintro _ ⟨e, he, rfl⟩
    exact Subtype.coe_le_coe.mpr (hv he)

/-- Auxiliary: an `IsLUB` in `sa(A)` is an `IsLUB` in `A` (upper bounds of a
nonempty set of self-adjoint elements are automatically self-adjoint). -/
theorem isLUB_coe_of_isLUB {D : Set (selfAdjoint A)} {s : selfAdjoint A}
    (hne : D.Nonempty) (h : IsLUB D s) :
    IsLUB (Subtype.val '' D) ((s : selfAdjoint A) : A) := by
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · have hu0 : ((d₀ : selfAdjoint A) : A) ≤ u := hu ⟨d₀, hd₀, rfl⟩
    have husa : IsSelfAdjoint u := by
      have hd : IsSelfAdjoint (u - ((d₀ : selfAdjoint A) : A)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu0)
      simpa using hd.add d₀.2
    have hub : (⟨u, husa⟩ : selfAdjoint A) ∈ upperBounds D :=
      fun e he => hu ⟨e, he, rfl⟩
    exact h.2 hub

/-- An `IsLUB` in `A` of a set of self-adjoint elements is an `IsLUB` in
`sa(A)` (converse of `isLUB_coe_of_isLUB`). -/
theorem isLUB_sa_of_isLUB {D : Set (selfAdjoint A)} {s : selfAdjoint A}
    (h : IsLUB (Subtype.val '' D) ((s : selfAdjoint A) : A)) : IsLUB D s := by
  refine ⟨fun d hd => Subtype.coe_le_coe.mp (h.1 ⟨d, hd, rfl⟩), fun v hv => ?_⟩
  refine Subtype.coe_le_coe.mp (h.2 ?_)
  rintro _ ⟨d, hd, rfl⟩
  exact Subtype.coe_le_coe.mpr (hv hd)

/-- Transfer of an infimum from `sa(A)` to `A`: a lower bound in `A` of a
nonempty set of self-adjoint elements is automatically self-adjoint. -/
theorem isGLB_coe_of_isGLB {F : Set (selfAdjoint A)} {i : selfAdjoint A}
    (hne : F.Nonempty) (h : IsGLB F i) :
    IsGLB (Subtype.val '' F) ((i : selfAdjoint A) : A) := by
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mpr (h.1 hd)
  · have hu0 : u ≤ ((d₀ : selfAdjoint A) : A) := hu ⟨d₀, hd₀, rfl⟩
    have husa : IsSelfAdjoint u := by
      have hd : IsSelfAdjoint (((d₀ : selfAdjoint A) : A) - u) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu0)
      simpa using d₀.2.sub hd
    have hlb : (⟨u, husa⟩ : selfAdjoint A) ∈ lowerBounds F :=
      fun e he => hu ⟨e, he, rfl⟩
    exact h.2 hlb

private theorem conjSA_neg (a : A) (d : selfAdjoint A) :
    conjSA a (-d) = -conjSA a d := by
  refine Subtype.ext ?_
  show star a * ((-d : selfAdjoint A) : A) * a = -((conjSA a d : selfAdjoint A) : A)
  simp [conjSA_coe]

/-- **44VIII** (`ad-normal`, vn.tex:704) in the "variation" used in the proof
of **56VI**: conjugation `d ↦ a* d a` also preserves the *infima* of
nonempty filtered (downwards directed) sets of self-adjoint elements.
Obtained from `ad_normal` by the substitution `x ↦ -x`, exactly as
`infima_in_vna` obtains infima from suprema. -/
theorem ad_normal_inf [VonNeumannAlgebra A] (a : A) {F : Set (selfAdjoint A)}
    {i : selfAdjoint A} (hne : F.Nonempty) (hdir : DirectedOn (· ≥ ·) F)
    (hglb : IsGLB F i) :
    IsGLB ((fun x : A => star a * x * a) '' (Subtype.val '' F))
      (star a * ((i : selfAdjoint A) : A) * a) := by
  -- `-F` is nonempty, directed upwards, and has `-i` as supremum
  have hne' : (-F).Nonempty := hne.neg
  have hdir' : DirectedOn (· ≤ ·) (-F) := by
    rintro x hx y hy
    rw [Set.mem_neg] at hx hy
    obtain ⟨c, hc, hcx, hcy⟩ := hdir _ hx _ hy
    exact ⟨-c, by simpa using hc, le_neg.mpr hcx, le_neg.mpr hcy⟩
  have hlub' : IsLUB (-F) (-i) := hglb.neg
  have hA := conjSA_isLUB a hne' hdir' hlub'
  -- rewrite `conjSA a '' (-F) = -(conjSA a '' F)` and `conjSA a (-i) = -conjSA a i`
  have himg : conjSA a '' (-F) = -(conjSA a '' F) := by
    ext x
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨d, hd, hx⟩
      exact ⟨-d, hd, by rw [conjSA_neg, hx]⟩
    · rintro ⟨d, hd, hx⟩
      refine ⟨-d, by simpa using hd, ?_⟩
      rw [conjSA_neg, hx, neg_neg]
  rw [himg, conjSA_neg] at hA
  have hglbSA : IsGLB (conjSA a '' F) (conjSA a i) := by
    simpa using hA.neg
  have hcoe := isGLB_coe_of_isGLB (hne.image _) hglbSA
  rw [conjSA_coe] at hcoe
  have hset : Subtype.val '' (conjSA a '' F)
      = (fun x : A => star a * x * a) '' (Subtype.val '' F) := by
    rw [← Set.image_comp, ← Set.image_comp]; rfl
  rwa [hset] at hcoe

end AdNormal

/-- **72III**.1a (`bstaromega-basic`, vn.tex:3850) as far as it is needed
here: for an np-functional `ω` and `b ∈ A` the functional `b*ω : a ↦ ω(b* a b)`
is again an np-functional.  Positivity is
`star_left_conjugate_le_conjugate`; normality is exactly **44VIII**
(`ad_normal`).  This is what turns the (trivial) faithfulness of the
np-functionals into *order* separation in **44XI**. -/
noncomputable def conjNP [VonNeumannAlgebra A] (b : A) (ω : NPFunctional A) :
    NPFunctional A where
  toPositiveLinearMap :=
    { toFun := fun x => ω (star b * x * b)
      map_add' := fun x y => by
        rw [mul_add, add_mul]; exact map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c x => by
        rw [mul_smul_comm, smul_mul_assoc]
        exact map_smul ω.toPositiveLinearMap _ _
      monotone' := fun x y hxy =>
        ω.toPositiveLinearMap.monotone (star_left_conjugate_le_conjugate hxy b) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hEdir : DirectedOn (· ≤ ·) (conjSA b '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
      exact ⟨conjSA b u, ⟨u, hu, rfl⟩, conjSA_mono b hxu, conjSA_mono b hzu⟩
    have hkey := ω.preservesDirSups' (conjSA b '' D) (conjSA b s)
      (hne.image _) hEdir (conjSA_isLUB b hne hdir hlub)
    rw [← Set.image_comp] at hkey
    exact hkey

@[simp] theorem conjNP_apply [VonNeumannAlgebra A] (b : A) (ω : NPFunctional A)
    (a : A) : conjNP b ω a = ω (star b * a * b) :=
  rfl

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), the preliminary
claim in the form **30X** delivers it: `a` is positive as soon as
`ω(c* a c) ≥ 0` for every np-functional `ω` and every `c ∈ A`.

The np-functionals are *centre separating* for the trivial reason that they
are faithful (take `c = 1`); cstar.tex **30X** turns that into order
separation of the family `{a ↦ ω(c* a c)}`, whose members are np-functionals
again by `conjNP` (i.e. by **44VIII**). -/
theorem nonneg_of_conjNP [VonNeumannAlgebra A] {a : A}
    (h : ∀ (ω : NPFunctional A) (c : A), (0 : ℂ) ≤ ω (star c * a * c)) :
    0 ≤ a := by
  -- the np-functionals, as a family of positive linear maps
  set Ω : NPFunctional A → (A →ₗ[ℂ] ℂ) :=
    fun ω => ω.toPositiveLinearMap.toLinearMap with hΩ
  have hpos : ∀ ω, IsPositiveMap (Ω ω) := fun ω x hx => by
    have h0 : (ω 0 : ℂ) = 0 := map_zero ω.toPositiveLinearMap
    have h1 : (ω 0 : ℂ) ≤ ω x := ω.toPositiveLinearMap.monotone hx
    rw [h0] at h1
    exact h1
  -- the family is centre separating: this is bare faithfulness (take `c = 1`)
  have hcentre : CentreSeparating Ω := by
    intro x hx
    refine ⟨fun hx0 ω c => by rw [hx0]; simp, fun H => ?_⟩
    refine VonNeumannAlgebra.np_faithful x hx fun ω => ?_
    have h1 := H ω 1
    rw [star_one, one_mul, mul_one] at h1
    exact h1
  -- **30X** upgrades that to order separation of `{a ↦ ω(c* a c)}`
  refine ((proto_gelfand_naimark_1 Ω hpos).mp hcentre a).mpr fun p => ?_
  show (0 : ℂ) ≤ Ω p.1 (star p.2 * (a * p.2))
  rw [← mul_assoc]
  exact h p.1 p.2

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), preliminary claim:
the np-functionals on a von Neumann algebra are not only faithful but order
separating. -/
theorem np_orderSeparating [VonNeumannAlgebra A] (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : ∀ ω : NPFunctional A, ω a ≤ ω b) : a ≤ b := by
  rw [← sub_nonneg]
  refine nonneg_of_conjNP fun ω c => ?_
  have hle := h (conjNP c ω)
  rw [conjNP_apply, conjNP_apply] at hle
  rw [show star c * (b - a) * c = star c * b * c - star c * a * c by noncomm_ring,
    npFunctional_sub, sub_nonneg]
  exact hle

/-- **44XI**, preliminary claim, separating form: an element killed by every
np-functional is zero.  (Faithfulness gives this only for *positive*
elements; order separation removes that restriction.) -/
theorem np_separating [VonNeumannAlgebra A] (a : A)
    (h : ∀ ω : NPFunctional A, ω a = 0) : a = 0 := by
  have h1 : (0 : A) ≤ a := nonneg_of_conjNP fun ω c => by
    have := h (conjNP c ω); rw [conjNP_apply] at this; rw [this]
  have h2 : (0 : A) ≤ -a := nonneg_of_conjNP fun ω c => by
    have := h (conjNP c ω)
    rw [conjNP_apply] at this
    rw [show star c * (-a) * c = -(star c * a * c) by noncomm_ring,
      npFunctional_neg, this, neg_zero]
  exact le_antisymm (neg_nonneg.mp h2) h1

/-- **44XI**, preliminary claim: the np-functionals separate the points of a
von Neumann algebra. -/
theorem eq_of_forall_npFunctional [VonNeumannAlgebra A] {a b : A}
    (h : ∀ ω : NPFunctional A, ω a = ω b) : a = b :=
  sub_eq_zero.mp (np_separating (a - b) fun ω => by
    rw [npFunctional_sub, h ω, sub_self])

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), part 1: the
ultraweak and ultrastrong topologies are Hausdorff. -/
theorem vn_positive_basic_1 [VonNeumannAlgebra A] :
    @T2Space A (ultraweak A) ∧ @T2Space A (ultrastrong A) := by
  have huw : @T2Space A (ultraweak A) := by
    refine @T2Space.mk A (ultraweak A) fun x y hxy => ?_
    obtain ⟨ω, hω⟩ : ∃ ω : NPFunctional A, (ω x : ℂ) ≠ ω y := by
      by_contra hc
      push_neg at hc
      exact hxy (eq_of_forall_npFunctional hc)
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hω
    exact ⟨(fun a : A => (ω a : ℂ)) ⁻¹' u, (fun a : A => (ω a : ℂ)) ⁻¹' v,
      @Continuous.isOpen_preimage A ℂ (ultraweak A) _ _
        (continuous_ultraweak_npFunctional ω) u hu,
      @Continuous.isOpen_preimage A ℂ (ultraweak A) _ _
        (continuous_ultraweak_npFunctional ω) v hv, hxu, hyv,
      huv.preimage _⟩
  -- the ultrastrong topology is finer (**43I**), and `T2Space` is antitone
  exact ⟨huw, t2Space_antitone ultrastrong_le_ultraweak huw⟩

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), part 2: the
positive cone, the self-adjoint part, and the set of effects are ultraweakly
(hence, by **43I**, ultrastrongly) closed. -/
theorem vn_positive_basic_2 [VonNeumannAlgebra A] :
    @IsClosed A (ultraweak A) {a : A | 0 ≤ a} ∧
      @IsClosed A (ultraweak A) {a : A | IsSelfAdjoint a} ∧
      @IsClosed A (ultraweak A) (effects A) := by
  -- Order separation writes each of the three sets as an intersection of
  -- preimages of closed subsets of `ℂ` under np-functionals.
  have hle : ∀ x : A, @IsClosed A (ultraweak A) {a : A | a ≤ x} := by
    intro x
    have hset : {a : A | a ≤ x}
        = ⋂ p : NPFunctional A × A,
            (fun a : A => (conjNP p.2 p.1 a : ℂ)) ⁻¹' Set.Iic (conjNP p.2 p.1 x) := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
      constructor
      · exact fun hax p => npFunctional_mono (conjNP p.2 p.1) hax
      · intro H
        rw [← sub_nonneg]
        refine nonneg_of_conjNP fun ω c => ?_
        have hc := H (ω, c)
        rw [show star c * (x - a) * c = star c * x * c - star c * a * c by
          noncomm_ring, npFunctional_sub, sub_nonneg]
        exact hc
    rw [hset]
    exact isClosed_ultraweak_iInter _ fun p =>
      isClosed_ultraweak_preimage (conjNP p.2 p.1) isClosed_Iic
  have hge : ∀ x : A, @IsClosed A (ultraweak A) {a : A | x ≤ a} := by
    intro x
    have hset : {a : A | x ≤ a}
        = ⋂ p : NPFunctional A × A,
            (fun a : A => (conjNP p.2 p.1 a : ℂ)) ⁻¹' Set.Ici (conjNP p.2 p.1 x) := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
      constructor
      · exact fun hax p => npFunctional_mono (conjNP p.2 p.1) hax
      · intro H
        rw [← sub_nonneg]
        refine nonneg_of_conjNP fun ω c => ?_
        have hc := H (ω, c)
        rw [show star c * (a - x) * c = star c * a * c - star c * x * c by
          noncomm_ring, npFunctional_sub, sub_nonneg]
        exact hc
    rw [hset]
    exact isClosed_ultraweak_iInter _ fun p =>
      isClosed_ultraweak_preimage (conjNP p.2 p.1) isClosed_Ici
  refine ⟨hge 0, ?_, ?_⟩
  · -- `a` is self-adjoint iff `ω(a)` is real for every np-functional
    have hset : {a : A | IsSelfAdjoint a}
        = ⋂ ω : NPFunctional A, (fun a : A => (ω a : ℂ)) ⁻¹' {z : ℂ | z.im = 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      refine ⟨fun ha ω => npFunctional_im_eq_zero ω ha, fun H => ?_⟩
      have h0 : star a - a = 0 := by
        refine np_separating _ fun ω => ?_
        rw [npFunctional_sub, npFunctional_star, Complex.star_def,
          Complex.conj_eq_iff_im.mpr (H ω), sub_self]
      exact sub_eq_zero.mp h0
    rw [hset]
    exact isClosed_ultraweak_iInter _ fun ω =>
      isClosed_ultraweak_preimage ω
        (isClosed_eq Complex.continuous_im continuous_const)
  · exact (Set.ext fun _ => Iff.rfl : effects A = {a : A | 0 ≤ a} ∩ {a : A | a ≤ 1}) ▸
      isClosed_ultraweak_inter _ _ (hge 0) (hle 1)

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), part 3: the unit
ball is ultrastrongly closed.  (It is ultraweakly closed too, but that is
seen only in 73VIII, `ultraclosed`.) -/
theorem vn_positive_basic_3 [VonNeumannAlgebra A] :
    @IsClosed A (ultrastrong A) (Metric.closedBall (0 : A) 1) := by
  -- `‖a‖ ≤ 1` iff `a*a ≤ 1` iff `‖a‖_ω ≤ ‖1‖_ω` for every np-functional `ω`
  -- (the second `iff` is the order-separation of the np-functionals), and
  -- each `{a | ‖a‖_ω ≤ ‖1‖_ω}` is ultrastrongly closed because `‖·‖_ω` is
  -- `1`-Lipschitz for `‖·‖_ω`.
  have hchar : ∀ a : A, ‖a‖ ≤ 1 ↔
      ∀ ω : NPFunctional A, omegaNorm A ω a ≤ omegaNorm A ω 1 := by
    intro a
    have hnn : ∀ ω : NPFunctional A, 0 ≤ (ω (star a * a)).re :=
      fun ω => (Complex.le_def.mp (npFunctional_nonneg ω (star_mul_self_nonneg a))).1
    have hnn1 : ∀ ω : NPFunctional A, 0 ≤ (ω 1).re :=
      fun ω => (Complex.le_def.mp (npFunctional_nonneg ω zero_le_one)).1
    have hnorms : ∀ ω : NPFunctional A,
        omegaNorm A ω a = Real.sqrt (ω (star a * a)).re ∧
          omegaNorm A ω 1 = Real.sqrt (ω 1).re := by
      intro ω
      exact ⟨rfl, by rw [omegaNorm, star_one, one_mul]⟩
    have hsq : ‖a‖ ≤ 1 ↔ star a * a ≤ 1 := by
      rw [← CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a),
        CStarRing.norm_star_mul_self]
      constructor
      · intro h; nlinarith [norm_nonneg a]
      · intro h; nlinarith [norm_nonneg a]
    rw [hsq]
    constructor
    · intro h ω
      obtain ⟨h1, h2⟩ := hnorms ω
      rw [h1, h2]
      exact Real.sqrt_le_sqrt (Complex.le_def.mp (npFunctional_mono ω h)).1
    · intro h
      refine np_orderSeparating _ _ (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a))
        (IsSelfAdjoint.one A) fun ω => ?_
      obtain ⟨h1, h2⟩ := hnorms ω
      have hle := h ω
      rw [h1, h2] at hle
      have hre : (ω (star a * a)).re ≤ (ω 1).re := by
        nlinarith [Real.sq_sqrt (hnn ω), Real.sq_sqrt (hnn1 ω),
          Real.sqrt_nonneg (ω (star a * a)).re, Real.sqrt_nonneg (ω 1).re]
      refine Complex.le_def.mpr ⟨hre, ?_⟩
      have i1 := (Complex.le_def.mp (npFunctional_nonneg ω (star_mul_self_nonneg a))).2
      have i2 := (Complex.le_def.mp (npFunctional_nonneg ω (zero_le_one (α := A)))).2
      rw [← i1, ← i2]
  let _ : TopologicalSpace A := ultrastrong A
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun a ha => ?_
  rw [Set.mem_compl_iff, mem_closedBall_zero_iff, hchar] at ha
  simp only [not_forall, not_le] at ha
  obtain ⟨ω, hω⟩ := ha
  filter_upwards [ultrastrong_ball_mem_nhds ω a (sub_pos.mpr hω)] with b hb
  rw [Set.mem_compl_iff, mem_closedBall_zero_iff, hchar]
  simp only [not_forall, not_le]
  refine ⟨ω, ?_⟩
  have := abs_omegaNorm_sub_omegaNorm_le ω b a
  have h2 : omegaNorm A ω a - omegaNorm A ω b ≤ omegaNorm A ω (b - a) := by
    rw [abs_le] at this; linarith [this.1]
  linarith

/-- **44XIII** (`vna-supremum-commutes`, vn.tex:787): if `a` commutes with
every member of a bounded directed set `D` of self-adjoint elements, then
`a` commutes with `⋁D`. -/
theorem vna_supremum_commutes [VonNeumannAlgebra A]
    (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) (a : A)
    (hc : ∀ d ∈ D, a * (d : A) = (d : A) * a) :
    a * ((dirSup D h : selfAdjoint A) : A) =
      ((dirSup D h : selfAdjoint A) : A) * a := by
  -- `(da)_d → (⋁D)a` and `(ad)_d → a(⋁D)` ultraweakly by **44VII** (the
  -- second by instantiating it at `a*`); the two nets are equal, so — now
  -- that the np-functionals separate points (**44XI**) — so are the limits.
  obtain ⟨d₀, hd₀⟩ := h.1
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp h.2.1
  refine sub_eq_zero.mp (np_separating _ fun ω => ?_)
  rw [npFunctional_sub, sub_eq_zero]
  have h1 := (uwTendsto_iff _ _ _).mp (vna_supremum_mult D h a).1 ω
  have h2 := (uwTendsto_iff _ _ _).mp (vna_supremum_mult D h (star a)).2 ω
  rw [star_star] at h2
  have heq : (fun d : D => (ω (a * ((d : selfAdjoint A) : A)) : ℂ))
      = fun d : D => (ω (((d : selfAdjoint A) : A) * a) : ℂ) := by
    funext d
    rw [hc _ d.2]
  rw [heq] at h2
  exact tendsto_nhds_unique h2 h1

/-- **44XIII** (`vna-supremum-commutes`, vn.tex:787) in the "variation" used
in the proof of **56VI**.80: if `a` commutes with every member of a nonempty
filtered (downwards directed) set `F` of self-adjoint elements which is
bounded below, then `a` commutes with `⋀F`.  Obtained from
`vna_supremum_commutes` by `x ↦ -x`. -/
theorem vna_infimum_commutes [VonNeumannAlgebra A] {F : Set (selfAdjoint A)}
    {i : selfAdjoint A} (hne : F.Nonempty) (hdir : DirectedOn (· ≥ ·) F)
    (hglb : IsGLB F i) (a : A) (hc : ∀ d ∈ F, a * (d : A) = (d : A) * a) :
    a * ((i : selfAdjoint A) : A) = ((i : selfAdjoint A) : A) * a := by
  have hne' : (-F).Nonempty := hne.neg
  have hdir' : DirectedOn (· ≤ ·) (-F) := by
    rintro x hx y hy
    rw [Set.mem_neg] at hx hy
    obtain ⟨c, hc', hcx, hcy⟩ := hdir _ hx _ hy
    exact ⟨-c, by simpa using hc', le_neg.mpr hcx, le_neg.mpr hcy⟩
  have hlub' : IsLUB (-F) (-i) := hglb.neg
  have h3 : (-F).Nonempty ∧ DirectedOn (· ≤ ·) (-F) ∧ BddAbove (-F) :=
    ⟨hne', hdir', ⟨-i, hlub'.1⟩⟩
  have hsup : dirSup (-F) h3 = -i := (isLUB_dirSup (-F) h3).unique hlub'
  have hkey := vna_supremum_commutes (-F) h3 a (by
    rintro d hd
    rw [Set.mem_neg] at hd
    have := hc _ hd
    have hd' : ((d : selfAdjoint A) : A) = -((-d : selfAdjoint A) : A) := by
      simp
    rw [hd']
    rw [mul_neg, neg_mul, this])
  rw [hsup] at hkey
  have hneg : ((-i : selfAdjoint A) : A) = -((i : selfAdjoint A) : A) := by
    simp
  rw [hneg, mul_neg, neg_mul, neg_inj] at hkey
  exact hkey

/-- **44XIV** (`vna-supremum-uslimit`, vn.tex:791): for a bounded directed
set `D` of self-adjoint elements, `(⋁D − d)² → 0` ultraweakly, i.e. the net
`(d)_{d∈D}` converges *ultrastrongly* to `⋁D`. -/
theorem vna_supremum_uslimit [VonNeumannAlgebra A] (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    USTendsto (fun d : D => (d : A)) atTop
      ((dirSup D h : selfAdjoint A) : A) := by
  -- `‖d - ⋁D‖_ω² = ω((⋁D-d)²) ≤ ‖⋁D-d‖ · ω(⋁D-d) ≤ M · ω(⋁D-d) → 0`,
  -- the norms being eventually bounded because `0 ≤ ⋁D-d ≤ ⋁D-d₀`.
  obtain ⟨d₀, hd₀⟩ := h.1
  set s : A := ((dirSup D h : selfAdjoint A) : A) with hs
  have hle : ∀ d ∈ D, ((d : selfAdjoint A) : A) ≤ s := fun d hd =>
    Subtype.coe_le_coe.mpr ((isLUB_dirSup D h).1 hd)
  rw [usTendsto_iff]
  intro ω
  set M : ℝ := ‖s - ((d₀ : selfAdjoint A) : A)‖ with hM
  -- rewrite `‖d - ⋁D‖_ω` as `ω((⋁D-d)²)^½`
  have hnorm : ∀ d : D, omegaNorm A ω (((d : selfAdjoint A) : A) - s) =
      Real.sqrt (ω ((s - ((d : selfAdjoint A) : A)) *
        (s - ((d : selfAdjoint A) : A)))).re := by
    intro d
    rw [omegaNorm]
    congr 3
    rw [star_sub, hs, selfAdjoint.star_val_eq, selfAdjoint.star_val_eq]
    noncomm_ring
  have hbound : ∀ᶠ d : D in atTop,
      omegaNorm A ω (((d : selfAdjoint A) : A) - s) ≤
        Real.sqrt (M * (ω (s - ((d : selfAdjoint A) : A))).re) := by
    filter_upwards [eventually_ge_atTop (⟨d₀, hd₀⟩ : D)] with d hdd
    rw [hnorm d]
    refine Real.sqrt_le_sqrt ?_
    have hx : (0 : A) ≤ s - ((d : selfAdjoint A) : A) := sub_nonneg.mpr (hle d d.2)
    have hxM : ‖s - ((d : selfAdjoint A) : A)‖ ≤ M :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hx
        (sub_le_sub_left (Subtype.coe_le_coe.mpr
          (Subtype.coe_le_coe.mpr hdd)) s)
    have h1 : (s - ((d : selfAdjoint A) : A)) * (s - ((d : selfAdjoint A) : A))
        ≤ M • (s - ((d : selfAdjoint A) : A)) :=
      (mul_self_le_norm_smul hx).trans
        (smul_le_smul_of_nonneg_right hxM hx)
    have h2 : (ω ((s - ((d : selfAdjoint A) : A)) *
          (s - ((d : selfAdjoint A) : A)))).re
        ≤ (ω (M • (s - ((d : selfAdjoint A) : A)))).re :=
      (Complex.le_def.mp (ω.toPositiveLinearMap.monotone h1)).1
    have h3 : ω (M • (s - ((d : selfAdjoint A) : A)))
        = (M : ℂ) * ω (s - ((d : selfAdjoint A) : A)) := by
      have hsm : M • (s - ((d : selfAdjoint A) : A))
          = ((M : ℂ)) • (s - ((d : selfAdjoint A) : A)) :=
        (algebraMap_smul ℂ M (s - ((d : selfAdjoint A) : A))).symm
      rw [hsm]
      exact (map_smul ω.toPositiveLinearMap _ _).trans (smul_eq_mul _ _)
    rw [h3] at h2
    rwa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at h2
  refine squeeze_zero' (Eventually.of_forall fun d => omegaNorm_nonneg ω _)
    hbound ?_
  -- and `ω(⋁D - d) → 0` by 44VI
  have hω := (uwTendsto_iff _ _ _).mp (vna_supremum_uwlimit D h) ω
  have hsub : Tendsto (fun d : D => ω (s - ((d : selfAdjoint A) : A))) atTop
      (𝓝 0) := by
    have := (tendsto_const_nhds (x := ω s) (f := (atTop : Filter D))).sub hω
    simpa [← hs] using this
  have h1 : Tendsto
      (fun d : D => (ω (s - ((d : selfAdjoint A) : A))).re) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.tendsto (0 : ℂ)).comp hsub
  have h2 : Tendsto
      (fun d : D => M * (ω (s - ((d : selfAdjoint A) : A))).re) atTop (𝓝 0) := by
    simpa using h1.const_mul M
  simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h2

/-! ### Positive maps and self-adjoint elements (auxiliary)

These are stated for arbitrary universes because both this file (**48II**,
**48VIII**) and the later chapters need them for plain C*-algebras. -/

section PositiveMaps

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A positive linear map sends self-adjoint elements to self-adjoint
elements (cstar.tex 10IV, `cstar-p-implies-i`, in the form used here). -/
theorem isSelfAdjoint_map_of_positive (f : A →ₚ[ℂ] B) {x : A}
    (hx : IsSelfAdjoint x) : IsSelfAdjoint (f x) := by
  have hsplit : posPart x - negPart x = x := CFC.posPart_sub_negPart x hx
  have hz : (f (0 : A) : B) = 0 := map_zero f
  have h1 : (0 : B) ≤ f (posPart x) := by
    have h : (f (0 : A) : B) ≤ f (posPart x) := f.monotone (CFC.posPart_nonneg x)
    rwa [hz] at h
  have h2 : (0 : B) ≤ f (negPart x) := by
    have h : (f (0 : A) : B) ≤ f (negPart x) := f.monotone (CFC.negPart_nonneg x)
    rwa [hz] at h
  have := (IsSelfAdjoint.of_nonneg h1).sub (IsSelfAdjoint.of_nonneg h2)
  rwa [← map_sub, hsplit] at this

/-- The image in `sa(B)` of a set `D ⊆ sa(A)` under a positive linear map
`f`. -/
private def imageSA (f : A →ₚ[ℂ] B) (D : Set (selfAdjoint A)) :
    Set (selfAdjoint B) :=
  (fun d : selfAdjoint A =>
    (⟨f (d : A), isSelfAdjoint_map_of_positive f d.2⟩ : selfAdjoint B)) '' D

private theorem coe_imageSA (f : A →ₚ[ℂ] B) (D : Set (selfAdjoint A)) :
    Subtype.val '' imageSA f D = (fun d : selfAdjoint A => f (d : A)) '' D := by
  rw [imageSA, ← Set.image_comp]; rfl

private theorem imageSA_nonempty (f : A →ₚ[ℂ] B) {D : Set (selfAdjoint A)}
    (hne : D.Nonempty) : (imageSA f D).Nonempty :=
  hne.image _

private theorem imageSA_directedOn (f : A →ₚ[ℂ] B) {D : Set (selfAdjoint A)}
    (hdir : DirectedOn (· ≤ ·) D) : DirectedOn (· ≤ ·) (imageSA f D) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
  exact ⟨_, ⟨z, hz, rfl⟩,
    Subtype.coe_le_coe.mp (f.monotone (Subtype.coe_le_coe.mpr hxz)),
    Subtype.coe_le_coe.mp (f.monotone (Subtype.coe_le_coe.mpr hyz))⟩

/-- The composite of an np-map `f : A → B` with an np-functional on `B` is
an np-functional on `A`.  (This is the easy half of **48II**.) -/
noncomputable def compNP (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (ω : NPFunctional B) : NPFunctional A where
  toPositiveLinearMap :=
    { toFun := fun x => ω (f x)
      map_add' := fun x y => by
        rw [map_add]; exact map_add ω.toPositiveLinearMap _ _
      map_smul' := fun c x => by
        rw [map_smul]; exact map_smul ω.toPositiveLinearMap _ _
      monotone' := fun x y hxy => npFunctional_mono ω (f.monotone hxy) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hlubG : IsLUB (imageSA f D)
        (⟨f (s : A), isSelfAdjoint_map_of_positive f s.2⟩ : selfAdjoint B) := by
      refine isLUB_sa_of_isLUB ?_
      rw [coe_imageSA]
      exact hf D s hne hdir hlub
    have hkey := ω.preservesDirSups' _ _ (imageSA_nonempty f hne)
      (imageSA_directedOn f hdir) hlubG
    rw [imageSA, ← Set.image_comp] at hkey
    exact hkey

@[simp] theorem compNP_apply (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (ω : NPFunctional B) (x : A) : compNP f hf ω x = ω (f x) := rfl

/-! #### Auxiliary machinery for **44XV**, **45II** and **45IV**

The three parsec-440/450 continuity results all reduce to two mechanisms:
polarisation (`mult_polarization`), which turns `a ↦ ω(u a v)` into a
`ℂ`-combination of the np-functionals `conjNP c ω` of **44VIII**, and a
`‖·‖_ω`-Lipschitz estimate, which gives ultrastrong continuity directly from
the definition of the ultrastrong topology as generated by the `‖·‖_ω`-balls.
-/

omit [PartialOrder A] [StarOrderedRing A] in
/-- Real scalars act through `ℂ`. -/
private theorem real_smul_eq_complex_smul (r : ℝ) (a : A) :
    (r • a : A) = ((r : ℂ)) • a := by
  rw [← algebraMap_smul ℂ r a]; simp

omit [StarOrderedRing A] in
private theorem npFunctional_real_smul (ω : NPFunctional A) (r : ℝ) (a : A) :
    ω (r • a) = (r : ℂ) * ω a := by
  rw [real_smul_eq_complex_smul]
  exact (map_smul ω.toPositiveLinearMap _ _).trans (smul_eq_mul _ _)

omit [StarOrderedRing A] in
private theorem npFunctional_csmul (ω : NPFunctional A) (c : ℂ) (a : A) :
    ω (c • a) = c * ω a :=
  (map_smul ω.toPositiveLinearMap c a).trans (smul_eq_mul _ _)

omit [StarOrderedRing A] in
private theorem npFunctional_finsetSum {ι : Type*} (ω : NPFunctional A)
    (s : Finset ι) (g : ι → A) : ω (∑ i ∈ s, g i) = ∑ i ∈ s, ω (g i) :=
  map_sum ω.toPositiveLinearMap g s

private theorem positiveLinearMap_real_smul (f : A →ₚ[ℂ] B) (r : ℝ) (a : A) :
    f (r • a) = r • f a := by
  rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, map_smul]

omit [StarOrderedRing A] [StarOrderedRing B] in
/-- A map into the codomain is ultraweakly continuous as soon as every
np-functional composed with it is: the ultraweak topology *is* the initial
topology of the np-functionals (**42III**).

Stated over `CStarAlgebra`, not `VonNeumannAlgebra` — `ultraweak` and
`NPFunctional` are defined in that setting and the argument uses nothing more.
The sibling `continuous_ultraweak_conj` below does carry the von Neumann
binder, and the difference is deliberate. -/
theorem continuous_ultraweak_of_forall (f : A → B)
    (h : ∀ ω : NPFunctional B,
      @Continuous A ℂ (ultraweak A) _ (fun x => (ω (f x) : ℂ))) :
    @Continuous A B (ultraweak A) (ultraweak B) f := by
  rw [continuous_iff_le_induced]
  show ultraweak A ≤ TopologicalSpace.induced f
    (⨅ ω : NPFunctional B,
      TopologicalSpace.induced (fun x : B => (ω x : ℂ)) inferInstance)
  rw [induced_iInf]
  refine le_iInf fun ω => ?_
  rw [induced_compose]
  exact continuous_iff_le_induced.mp (h ω)

/-- Polarisation (**44II** `mult_polarization`): for fixed `u, v` in a von
Neumann algebra and an np-functional `ω`, the map `a ↦ ω(u a v)` is a
`ℂ`-combination of the four np-functionals `conjNP (iᵏ u* + v) ω` of
**44VIII**, hence ultraweakly continuous. -/
theorem continuous_ultraweak_conj [VonNeumannAlgebra A] (ω : NPFunctional A)
    (u v : A) :
    @Continuous A ℂ (ultraweak A) _ (fun a : A => (ω (u * a * v) : ℂ)) := by
  let _ : TopologicalSpace A := ultraweak A
  have heq : (fun a : A => (ω (u * a * v) : ℂ))
      = fun a : A => (4 : ℂ)⁻¹ * ∑ k ∈ Finset.range 4, (Complex.I ^ k) *
          (conjNP ((Complex.I ^ k : ℂ) • star u + v) ω) a := by
    funext a
    have h := mult_polarization (star u) v a
    rw [star_star] at h
    rw [h, npFunctional_csmul, npFunctional_finsetSum]
    simp only [npFunctional_csmul, conjNP_apply]
  rw [heq]
  exact continuous_const.mul (continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_ultraweak_npFunctional _))

/-- A set is ultrastrongly open as soon as every point of it has a
`‖·‖_ω`-ball around it inside the set. -/
private theorem isOpen_ultrastrong_of_ball {S : Set A}
    (h : ∀ a ∈ S, ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
      {x : A | omegaNorm A ω (x - a) < δ} ⊆ S) :
    @IsOpen A (ultrastrong A) S := by
  rw [@isOpen_iff_forall_mem_open A (ultrastrong A)]
  intro a ha
  obtain ⟨ω, δ, hδ, hsub⟩ := h a ha
  refine ⟨{x : A | omegaNorm A ω (x - a) < δ}, hsub,
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨ω, a, δ, hδ, rfl⟩, ?_⟩
  simpa using hδ

/-- An additive map which is `‖·‖_ω`-bounded — for every np-functional `ω`
on the codomain there are an np-functional `ω'` on the domain and a constant
`C` with `‖f a‖_ω ≤ C‖a‖_{ω'}` — is ultrastrongly continuous. -/
private theorem continuous_ultrastrong_of_omegaNorm_bound {f : A → B}
    (hsub : ∀ x y : A, f x - f y = f (x - y))
    (hb : ∀ ω : NPFunctional B, ∃ (ω' : NPFunctional A) (C : ℝ), 0 ≤ C ∧
      ∀ x : A, omegaNorm B ω (f x) ≤ C * omegaNorm A ω' x) :
    @Continuous A B (ultrastrong A) (ultrastrong B) f := by
  refine (@continuous_generateFrom_iff A B f (ultrastrong A) _).mpr ?_
  rintro _ ⟨ω, b₀, ε, hε, rfl⟩
  obtain ⟨ω', C, hC, hbound⟩ := hb ω
  refine isOpen_ultrastrong_of_ball ?_
  intro a₀ ha₀
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at ha₀
  set r : ℝ := omegaNorm B ω (f a₀ - b₀) with hr
  refine ⟨ω', (ε - r) / (C + 1), div_pos (sub_pos.mpr ha₀) (by linarith), ?_⟩
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hnn : 0 ≤ omegaNorm A ω' (x - a₀) := omegaNorm_nonneg _ _
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < C + 1)] at hx
  have hkey : C * omegaNorm A ω' (x - a₀) < ε - r := by nlinarith [hx, hnn]
  calc omegaNorm B ω (f x - b₀)
      ≤ omegaNorm B ω (f x - f a₀) + omegaNorm B ω (f a₀ - b₀) :=
        omegaNorm_sub_le ω _ _ _
    _ = omegaNorm B ω (f (x - a₀)) + r := by rw [hsub, hr]
    _ ≤ C * omegaNorm A ω' (x - a₀) + r := by
        have := hbound (x - a₀); linarith
    _ < ε := by linarith

/-- `‖yb‖_ω = ‖y‖_{b*ω}`, where `b*ω = conjNP b ω` is the np-functional
`a ↦ ω(b* a b)` of **44VIII**.  (Public since **74I** `proto_kaplansky`
needs it too — it is the step `‖(b−a)s(a)‖_ω ≡ ‖b−a‖_{s(a)*ω}` of the
thesis's proof.) -/
theorem omegaNorm_mul_right [VonNeumannAlgebra A] (ω : NPFunctional A)
    (y b : A) : omegaNorm A ω (y * b) = omegaNorm A (conjNP b ω) y := by
  rw [omegaNorm, omegaNorm, conjNP_apply, star_mul]
  congr 3
  noncomm_ring

/-- The common core of **44XV** (2) ⇒ (3) and **45I**.1: a positive linear
map which is *ultrastrongly*-to-*ultraweakly* continuous on the effects is
normal.  Replace the bounded directed `D` by its cofinal upper tail
`{d ∈ D | d₀ ≤ d}`, which is norm-bounded, and rescale it into `[0,1]_A` by
the affine map `a ↦ (a − d₀)/‖⋁D − d₀‖`; **44XIV** `vna_supremum_uslimit`
pushes the (ultrastrongly convergent) net into the effects, the hypothesis
pushes it through `f`, and **44XI** (order separation) identifies the limit
as the least upper bound.

Stated with the *finest* source topology and the *coarsest* target topology
of the two applications, so that both **44XV** (ultraweak ⇒ ultraweak) and
**45I**.1 (ultrastrong ⇒ ultrastrong) are one-line corollaries. -/
private theorem preservesDirSups_of_continuousOn_effects_core
    [VonNeumannAlgebra A] [VonNeumannAlgebra B] (f : A →ₚ[ℂ] B)
    (h : @ContinuousOn A B (ultrastrong A) (ultraweak B) f (effects A)) :
    PreservesDirSups ⇑f := by
  let _ : TopologicalSpace A := ultrastrong A
  let _ : TopologicalSpace B := ultraweak B
  intro D s hne hdir hlub
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact f.monotone (Subtype.coe_le_coe.mpr (hlub.1 hd))
  intro z hz
  obtain ⟨d₀, hd₀⟩ := hne
  set D' : Set (selfAdjoint A) := {d ∈ D | d₀ ≤ d} with hD'
  have hne' : D'.Nonempty := ⟨d₀, hd₀, le_refl _⟩
  have hdir' : DirectedOn (· ≤ ·) D' := by
    rintro x ⟨hxD, hx0⟩ y ⟨hyD, hy0⟩
    obtain ⟨e, heD, hxe, hye⟩ := hdir x hxD y hyD
    exact ⟨e, ⟨heD, hx0.trans hxe⟩, hxe, hye⟩
  have hlub' : IsLUB D' s := by
    refine ⟨fun d hd => hlub.1 hd.1, fun u hu => hlub.2 fun d hd => ?_⟩
    obtain ⟨e, heD, hde, h0e⟩ := hdir d hd d₀ hd₀
    exact hde.trans (hu ⟨heD, h0e⟩)
  have hd₀s : ((d₀ : selfAdjoint A) : A) ≤ (s : A) :=
    Subtype.coe_le_coe.mpr (hlub.1 hd₀)
  set c : ℝ := ‖(s : A) - ((d₀ : selfAdjoint A) : A)‖ with hc
  by_cases hc0 : c = 0
  · have hsd : (s : A) = ((d₀ : selfAdjoint A) : A) :=
      sub_eq_zero.mp (norm_eq_zero.mp hc0)
    rw [hsd]
    exact hz ⟨d₀, hd₀, rfl⟩
  have hcpos : 0 < c := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc0)
  set e : A → A := fun a => c⁻¹ • (a - ((d₀ : selfAdjoint A) : A)) with he
  have heff : ∀ a : A, ((d₀ : selfAdjoint A) : A) ≤ a → a ≤ (s : A) →
      e a ∈ effects A := by
    intro a h1 h2
    have hnn : (0 : A) ≤ a - ((d₀ : selfAdjoint A) : A) := sub_nonneg.mpr h1
    refine ⟨smul_nonneg (inv_nonneg.mpr hcpos.le) hnn, ?_⟩
    have hle : a - ((d₀ : selfAdjoint A) : A) ≤ c • (1 : A) := by
      refine (sub_le_sub_right h2 _).trans ?_
      simpa [hc] using le_norm_smul_one (sub_nonneg.mpr hd₀s)
    have := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr hcpos.le)
    rwa [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul] at this
  have hes : e (s : A) ∈ effects A := heff _ hd₀s le_rfl
  have hnonempty : Nonempty D' := ⟨⟨d₀, hd₀, le_refl _⟩⟩
  have hdo : IsDirectedOrder D' := directedOn_iff_isDirectedOrder.mp hdir'
  have hh' : D'.Nonempty ∧ DirectedOn (· ≤ ·) D' ∧ BddAbove D' :=
    ⟨hne', hdir', ⟨s, hlub'.1⟩⟩
  have hsup : dirSup D' hh' = s := (isLUB_dirSup D' hh').unique hlub'
  have hbase : USTendsto (fun d : D' => ((d : selfAdjoint A) : A)) atTop (s : A) := by
    have := vna_supremum_uslimit D' hh'
    rwa [hsup] at this
  have hnet : USTendsto (fun d : D' => e ((d : selfAdjoint A) : A)) atTop
      (e (s : A)) := by
    rw [usTendsto_iff] at hbase ⊢
    intro ω
    have h1 := (hbase ω).const_mul ‖((c⁻¹ : ℝ) : ℂ)‖
    have hrw : ∀ a : A, omegaNorm A ω (e a - e (s : A))
        = ‖((c⁻¹ : ℝ) : ℂ)‖ * omegaNorm A ω (a - (s : A)) := by
      intro a
      have hsm : e a - e (s : A) = ((c⁻¹ : ℝ) : ℂ) • (a - (s : A)) := by
        rw [he]
        simp only
        rw [← real_smul_eq_complex_smul, ← smul_sub]
        congr 1
        abel
      rw [hsm, omegaNorm_smul]
    simp only [hrw]
    simpa using h1
  have hin : ∀ᶠ d : D' in atTop, e ((d : selfAdjoint A) : A) ∈ effects A :=
    Eventually.of_forall fun d =>
      heff _ (Subtype.coe_le_coe.mpr d.2.2) (Subtype.coe_le_coe.mpr (hlub'.1 d.2))
  have htw : Tendsto (fun d : D' => e ((d : selfAdjoint A) : A)) atTop
      (𝓝[effects A] (e (s : A))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hnet hin
  have hfnet : Tendsto (fun d : D' => (f (e ((d : selfAdjoint A) : A)) : B)) atTop
      (𝓝 (f (e (s : A)))) := Filter.Tendsto.comp (h _ hes) htw
  have hback : ∀ a : A, (f a : B) = c • f (e a) + f ((d₀ : selfAdjoint A) : A) := by
    intro a
    rw [he]
    simp only
    rw [positiveLinearMap_real_smul, map_sub, smul_smul,
      mul_inv_cancel₀ hcpos.ne', one_smul]
    abel
  have hfd : UWTendsto (fun d : D' => (f ((d : selfAdjoint A) : A) : B)) atTop
      (f (s : A)) := by
    rw [uwTendsto_iff]
    intro ω
    have h1 := ((uwTendsto_iff _ _ _).mp hfnet ω).const_mul ((c : ℝ) : ℂ)
    have h2 := h1.add_const (ω (f ((d₀ : selfAdjoint A) : A)) : ℂ)
    have hrw : ∀ a : A, (ω (f a) : ℂ)
        = ((c : ℝ) : ℂ) * ω (f (e a)) + ω (f ((d₀ : selfAdjoint A) : A)) := by
      intro a
      rw [hback a]
      simp only [npFunctional_add, npFunctional_real_smul]
    have hfun : (fun d : D' => (ω (f ((d : selfAdjoint A) : A)) : ℂ))
        = fun d : D' => ((c : ℝ) : ℂ) * ω (f (e ((d : selfAdjoint A) : A)))
            + ω (f ((d₀ : selfAdjoint A) : A)) := funext fun d => hrw _
    rw [hfun, hrw ((s : selfAdjoint A) : A)]
    exact h2
  have hzsa : IsSelfAdjoint z := by
    have h1 : (f ((d₀ : selfAdjoint A) : A) : B) ≤ z := hz ⟨d₀, hd₀, rfl⟩
    have h0 : (0 : B) ≤ z - f ((d₀ : selfAdjoint A) : A) := sub_nonneg.mpr h1
    have := (IsSelfAdjoint.of_nonneg h0).add
      (isSelfAdjoint_map_of_positive f d₀.2)
    simpa using this
  refine np_orderSeparating _ _ (isSelfAdjoint_map_of_positive f s.2) hzsa fun ω => ?_
  refine le_of_tendsto ((uwTendsto_iff _ _ _).mp hfd ω) ?_
  exact Eventually.of_forall fun d =>
    npFunctional_mono ω (hz ⟨(d : selfAdjoint A), d.2.1, rfl⟩)

/-- Coarsening the source topology of a `ContinuousOn` statement: the
ultrastrong topology is finer than the ultraweak one (**43I**
`ultrastrong_le_ultraweak`), so ultraweak continuity on a set implies
ultrastrong continuity on it. -/
private theorem continuousWithinAt_ultrastrong_of_ultraweak {f : A → B}
    {S : Set A} {a : A} {t : TopologicalSpace B}
    (h : @ContinuousWithinAt A B (ultraweak A) t f S a) :
    @ContinuousWithinAt A B (ultrastrong A) t f S a :=
  h.mono_left (by
    show @nhdsWithin A (ultrastrong A) a S ≤ @nhdsWithin A (ultraweak A) a S
    exact inf_le_inf_right _ (_root_.nhds_mono ultrastrong_le_ultraweak))

/-- The core of **44XV**, (2) ⇒ (3): a positive linear map which is
ultraweakly continuous on the effects is normal.  This is the special case
of `preservesDirSups_of_continuousOn_effects_core` in which the source
topology is coarsened from ultrastrong to ultraweak. -/
theorem preservesDirSups_of_continuousOn_effects
    [VonNeumannAlgebra A] [VonNeumannAlgebra B] (f : A →ₚ[ℂ] B)
    (h : @ContinuousOn A B (ultraweak A) (ultraweak B) f (effects A)) :
    PreservesDirSups ⇑f :=
  preservesDirSups_of_continuousOn_effects_core f fun a ha =>
    continuousWithinAt_ultrastrong_of_ultraweak (h a ha)

/-- `b ↦ a* b a` as a positive linear map (**34V** `ad-cp`). -/
private noncomputable def adPositive (a : A) : A →ₚ[ℂ] A where
  toFun := fun b => star a * b * a
  map_add' := fun x y => by noncomm_ring
  map_smul' := fun r x => by
    simp only [RingHom.id_apply]
    rw [mul_smul_comm, smul_mul_assoc]
  monotone' := fun _ _ h => star_left_conjugate_le_conjugate h a

/-- The positive linear map underlying an ncp-map. -/
noncomputable def ncpPositive (f : NCPMap A B) : A →ₚ[ℂ] B where
  toFun := fun a => f a
  map_add' := fun x y => map_add f.toCompletelyPositiveMap x y
  map_smul' := fun c x => map_smul f.toCompletelyPositiveMap c x
  monotone' := fun _ _ h => OrderHomClass.mono f.toCompletelyPositiveMap h

@[simp] theorem ncpPositive_apply (f : NCPMap A B) (a : A) :
    (ncpPositive f a : B) = f a := rfl

private theorem ncp_isPositiveMap (f : NCPMap A B) :
    Theses.A.CStar.IsPositiveMap (f.toCompletelyPositiveMap.toLinearMap) := by
  intro a ha
  have h0 : (f.toCompletelyPositiveMap 0 : B) = 0 := map_zero _
  have hm := OrderHomClass.mono f.toCompletelyPositiveMap ha
  rw [h0] at hm
  exact hm

private theorem ncp_isCompletelyPositiveMap (f : NCPMap A B) :
    Theses.A.CStar.IsCompletelyPositiveMap
      (f.toCompletelyPositiveMap.toLinearMap) :=
  (Theses.A.CStar.cp_iff _).out 1 0 |>.mp fun N M hM =>
    f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM

/-- An ncp-map is involution preserving (cstar.tex 10IV,
`cstar-p-implies-i`). -/
theorem ncp_star (f : NCPMap A B) (a : A) : (f (star a) : B) = star (f a) :=
  Theses.A.CStar.cstar_p_implies_i _ (ncp_isPositiveMap f) a

/-- **34XIV** (`cp-cs`, cstar.tex:5741, Kadison's inequality) for an
ncp-map, in the form in which **45II** and **61II** use it:
`f(a)* f(a) ≤ ‖f(1)‖ · f(a* a)`.  (The thesis writes `‖f(1)‖²`; the sharper
`‖f(1)‖` is what `cp_cs` delivers, and either constant serves.) -/
theorem ncp_cp_cs (f : NCPMap A B) (a : A) :
    star (f a : B) * f a ≤ (‖(f 1 : B)‖ : ℝ) • f (star a * a) := by
  have h := Theses.A.CStar.cp_cs (f.toCompletelyPositiveMap.toLinearMap)
    (ncp_isPositiveMap f) (fun x c => ncp_isCompletelyPositiveMap f 2 x c) a 1
  rw [star_one, mul_one, one_mul, one_mul,
    Theses.A.CStar.cstar_p_implies_i _ (ncp_isPositiveMap f) a] at h
  exact h

end PositiveMaps

/-- **44XV** (`p-uwcont`, vn.tex:799, Exercise): for a positive linear map
`f : A → B` between von Neumann algebras the following are equivalent:
(1) `f` is ultraweakly continuous; (2) `f` is ultraweakly continuous on
`[0,1]_A`; (3) `f` preserves suprema of bounded directed sets of
self-adjoint elements; (4) `ω ∘ f` is normal for every np-functional `ω` on
`B`.  In that case `f` is called **normal** (extending 42II). -/
theorem p_uwcont [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : A →ₚ[ℂ] B) :
    List.TFAE
      [@Continuous A B (ultraweak A) (ultraweak B) f,
       @ContinuousOn A B (ultraweak A) (ultraweak B) f (effects A),
       PreservesDirSups ⇑f,
       ∀ ω : NPFunctional B, PreservesDirSups fun a => ω (f a)] := by
  -- (1) ⇒ (2) is trivial; (2) ⇒ (3) is the substance (see
  -- `preservesDirSups_of_continuousOn_effects`); (3) ⇔ (4) is `compNP` plus
  -- order separation; (3) ⇒ (1) is the definition of the ultraweak topology.
  tfae_have 1 → 2 := fun hcont =>
    @Continuous.continuousOn A B (ultraweak A) (ultraweak B) _ _ hcont
  tfae_have 2 → 3 := preservesDirSups_of_continuousOn_effects f
  tfae_have 3 → 4 := fun hf ω => (compNP f hf ω).preservesDirSups'
  tfae_have 4 → 3 := by
    intro hf D s hne hdir hlub
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact f.monotone (Subtype.coe_le_coe.mpr (hlub.1 hd))
    intro z hz
    obtain ⟨d₀, hd₀⟩ := hne
    have hzsa : IsSelfAdjoint z := by
      have h1 : (f ((d₀ : selfAdjoint A) : A) : B) ≤ z := hz ⟨d₀, hd₀, rfl⟩
      have h0 : (0 : B) ≤ z - f ((d₀ : selfAdjoint A) : A) := sub_nonneg.mpr h1
      have := (IsSelfAdjoint.of_nonneg h0).add
        (isSelfAdjoint_map_of_positive f d₀.2)
      simpa using this
    refine np_orderSeparating _ _ (isSelfAdjoint_map_of_positive f s.2) hzsa
      fun ω => ?_
    refine (hf ω D s ⟨d₀, hd₀⟩ hdir hlub).2 ?_
    rintro _ ⟨d, hd, rfl⟩
    exact npFunctional_mono ω (hz ⟨d, hd, rfl⟩)
  tfae_have 3 → 1 := fun hf =>
    continuous_ultraweak_of_forall _ fun ω =>
      continuous_ultraweak_npFunctional (compNP f hf ω)
  tfae_finish

/-- `b ↦ a* b a` is normal, i.e. preserves bounded directed suprema: this is
**44VIII** (`ad_normal`) restated for `adPositive`. -/
private theorem adPositive_normal [VonNeumannAlgebra A] (a : A) :
    PreservesDirSups ⇑(adPositive a) := by
  intro D s hne hdir hlub
  have hh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D :=
    ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hsup : dirSup D hh = s := (isLUB_dirSup D hh).unique hlub
  have := ad_normal a D hh
  rwa [hsup] at this

/-- **44XV** (`p-uwcont`, vn.tex:799, Exercise), conclusion: `b ↦ a* b a` is
ultraweakly continuous for every `a` in a von Neumann algebra (it is normal
by **44VIII**). -/
theorem p_uwcont_ad [VonNeumannAlgebra A] (a : A) :
    @Continuous A A (ultraweak A) (ultraweak A) fun b => star a * b * a :=
  ((p_uwcont (adPositive a)).out 2 0).mp (adPositive_normal a)

/-! ## Parsec 450 -/

/-- **45I** (vn.tex:829, Exercise), part 1: a positive linear map between
von Neumann algebras which is ultrastrongly continuous on `[0,1]_A` is
normal.  This is `preservesDirSups_of_continuousOn_effects_core` — the proof
of **44XV** (2) ⇒ (3) — with the target topology coarsened from ultrastrong
to ultraweak by **43I** `ultrastrong_le_ultraweak`; the net `d → ⋁D` already
converges *ultrastrongly* by **44XIV** `vna_supremum_uslimit`. -/
theorem us_cont_normal [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : A →ₚ[ℂ] B)
    (h : @ContinuousOn A B (ultrastrong A) (ultrastrong B) f (effects A)) :
    PreservesDirSups ⇑f :=
  preservesDirSups_of_continuousOn_effects_core f fun a ha =>
    (h a ha).mono_right (_root_.nhds_mono ultrastrong_le_ultraweak)

section Transpose

/-! ### The transpose on `B(ℓ²)` (**45I**.2)

Mathlib has no transpose on `B(ℓ²)`, so it is built here as `T ↦ J T* J`
with `J` the coordinatewise conjugation `star` of `lp` — a conjugate-linear
isometric involution of `ℓ²`.  The three facts that carry the argument are:
`J` is antiunitary (`star_inner_l2`), the transpose is its own inverse
(`transL2_involutive`, whence normality: an order isomorphism preserves every
supremum it meets), and `|0⟩⟨n| ↦ |n⟩⟨0|`, which is the counterexample net of
**43II**.4 again. -/

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- The conjugation `J` on `ℓ²` is antiunitary: `⟪Jx, Jy⟫ = conj ⟪x,y⟫`. -/
private theorem star_inner_l2 (x y : ℓ²) :
    (⟪star x, star y⟫ : ℂ) = star (⟪x, y⟫ : ℂ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine Eq.trans (tsum_congr fun i => ?_) tsum_star.symm
  rw [lp.star_apply, lp.star_apply]
  simp [RCLike.inner_apply, mul_comm]

private theorem star_single (n : ℕ) :
    star (lp.single 2 n (1 : ℂ) : ℓ²) = lp.single 2 n (1 : ℂ) := by
  ext i
  rcases eq_or_ne n i with h | h <;> simp [h]

/-- The transpose `T ↦ J T* J` on `B(ℓ²)`, as a continuous linear map. -/
private noncomputable def transL2 (T : ℓ² →L[ℂ] ℓ²) : ℓ² →L[ℂ] ℓ² :=
  LinearMap.mkContinuous
    { toFun := fun x => star (star T (star x))
      map_add' := by
        intro x y
        rw [star_add, map_add, star_add]
      map_smul' := by
        intro c x
        rw [RingHom.id_apply, star_smul, map_smul, star_smul, star_star] }
    ‖T‖ (by
      intro x
      show ‖star (star T (star x))‖ ≤ ‖T‖ * ‖x‖
      calc ‖star (star T (star x))‖ = ‖star T (star x)‖ := by rw [norm_star]
        _ ≤ ‖star T‖ * ‖star x‖ := (star T).le_opNorm _
        _ = ‖T‖ * ‖x‖ := by rw [norm_star, norm_star])

private theorem transL2_apply (T : ℓ² →L[ℂ] ℓ²) (x : ℓ²) :
    transL2 T x = star (star T (star x)) := rfl

private theorem star_transL2 (T : ℓ² →L[ℂ] ℓ²) :
    star (transL2 T) = transL2 (star T) := by
  refine ContinuousLinearMap.ext fun u => ?_
  refine ext_inner_left ℂ fun v => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    transL2_apply, transL2_apply, star_star]
  calc (⟪star (star T (star v)), u⟫ : ℂ)
      = ⟪star (star T (star v)), star (star u)⟫ := by rw [star_star]
    _ = star (⟪star T (star v), star u⟫ : ℂ) := star_inner_l2 _ _
    _ = star (⟪star v, T (star u)⟫ : ℂ) := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪star (star v), star (T (star u))⟫ := (star_inner_l2 _ _).symm
    _ = ⟪v, star (T (star u))⟫ := by rw [star_star]

private theorem transL2_involutive (T : ℓ² →L[ℂ] ℓ²) : transL2 (transL2 T) = T := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [transL2_apply, star_transL2, transL2_apply, star_star, star_star, star_star]

private theorem transL2_nonneg {T : ℓ² →L[ℂ] ℓ²} (hT : 0 ≤ T) : 0 ≤ transL2 T := by
  have hsa : star T = T := (IsSelfAdjoint.of_nonneg hT).star_eq
  refine (hilb_positive_operators_2 _).mpr fun x hx => ?_
  rw [transL2_apply, hsa]
  have h1 : (⟪x, star (T (star x))⟫ : ℂ) = star (⟪star x, T (star x)⟫ : ℂ) := by
    calc (⟪x, star (T (star x))⟫ : ℂ)
        = ⟪star (star x), star (T (star x))⟫ := by rw [star_star]
      _ = star (⟪star x, T (star x)⟫ : ℂ) := star_inner_l2 _ _
  rw [h1]
  have h2 : (0 : ℂ) ≤ ⟪star x, T (star x)⟫ :=
    (hilb_positive_operators_2 T).mp hT (star x) (by rw [norm_star]; exact hx)
  have h3 : star (⟪star x, T (star x)⟫ : ℂ) = ⟪star x, T (star x)⟫ := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]
    simpa using (Complex.le_def.mp h2).2.symm
  rw [h3]
  exact h2

private theorem transL2_map_add (S T : ℓ² →L[ℂ] ℓ²) :
    transL2 (S + T) = transL2 S + transL2 T := by
  refine ContinuousLinearMap.ext fun x => ?_
  show star (star (S + T) (star x)) = transL2 S x + transL2 T x
  rw [transL2_apply, transL2_apply, star_add]
  show star (star S (star x) + star T (star x)) = _
  rw [star_add]

private theorem transL2_mono : Monotone transL2 := by
  intro S T hST
  have h : (0 : ℓ² →L[ℂ] ℓ²) ≤ transL2 (T - S) := transL2_nonneg (sub_nonneg.mpr hST)
  have he : transL2 (T - S) = transL2 T - transL2 S := by
    have := transL2_map_add (T - S) S
    rw [sub_add_cancel] at this
    rw [this]
    abel
  rw [he, sub_nonneg] at h
  exact h

/-- The transpose, bundled as a positive linear map. -/
private noncomputable def transPLM :
    (ℓ² →L[ℂ] ℓ²) →ₚ[ℂ] (ℓ² →L[ℂ] ℓ²) where
  toFun := transL2
  map_add' := transL2_map_add
  map_smul' := by
    intro c T
    refine ContinuousLinearMap.ext fun x => ?_
    show star (star (c • T) (star x)) = c • transL2 T x
    rw [transL2_apply, star_smul]
    show star (star c • star T (star x)) = c • star (star T (star x))
    rw [star_smul, star_star]
  monotone' := transL2_mono

/-- **45I** (vn.tex:829, Exercise), part 2: the converse fails — there is a
normal positive map (e.g. the transpose on `B(ℓ²)`) that is not
ultrastrongly continuous. -/
theorem normal_not_us_cont :
    ∃ f : (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) →ₚ[ℂ]
        (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      PreservesDirSups ⇑f ∧
        ¬@Continuous _ _ (ultrastrong _) (ultrastrong _) ⇑f := by
  have hcoe : ⇑transPLM = transL2 := rfl
  refine ⟨transPLM, ?_, ?_⟩
  · -- normality: the transpose is an order isomorphism, hence preserves suprema
    rw [hcoe]
    intro D s hne hdir hlub
    refine ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact transL2_mono (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · intro u hu
      obtain ⟨d₀, hd₀⟩ := hne
      have hle : transL2 (d₀ : ℓ² →L[ℂ] ℓ²) ≤ u := hu ⟨d₀, hd₀, rfl⟩
      have husa : IsSelfAdjoint u := by
        have h1 : IsSelfAdjoint (u - transL2 (d₀ : ℓ² →L[ℂ] ℓ²)) :=
          IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hle)
        have h2 : IsSelfAdjoint (transL2 (d₀ : ℓ² →L[ℂ] ℓ²)) := by
          show star (transL2 (d₀ : ℓ² →L[ℂ] ℓ²)) = _
          rw [star_transL2]
          congr 1
          exact d₀.2
        simpa using h1.add h2
      have hfusa : IsSelfAdjoint (transL2 u) := by
        show star (transL2 u) = _
        rw [star_transL2, husa.star_eq]
      have hub : (⟨transL2 u, hfusa⟩ : selfAdjoint (ℓ² →L[ℂ] ℓ²)) ∈ upperBounds D := by
        intro d hd
        refine Subtype.coe_le_coe.mp ?_
        have h := transL2_mono (hu ⟨d, hd, rfl⟩)
        rwa [transL2_involutive] at h
      have := Subtype.coe_le_coe.mpr (hlub.2 hub)
      have h2 := transL2_mono this
      rwa [transL2_involutive] at h2
  · -- but it is not ultrastrongly continuous: `|0⟩⟨n| ↦ |n⟩⟨0|`
    rw [hcoe]
    intro hcont
    refine vn_counterexamples_4_bra.2 ⟨0, ?_⟩
    have hzero : transL2 (0 : ℓ² →L[ℂ] ℓ²) = 0 := by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [transL2_apply, star_zero]
      simp
    have h0 : Filter.Tendsto transL2
        (@nhds (ℓ² →L[ℂ] ℓ²) (ultrastrong _) 0)
        (@nhds (ℓ² →L[ℂ] ℓ²) (ultrastrong _) (transL2 0)) :=
      @Continuous.tendsto (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²) (ultrastrong _) (ultrastrong _)
        transL2 hcont 0
    have h : USTendsto (fun n : ℕ => transL2 (ketbraNat 0 n)) atTop (transL2 0) :=
      h0.comp vn_counterexamples_4_ket
    have hkb : ∀ n : ℕ, transL2 (ketbraNat 0 n) = ketbraNat n 0 := by
      intro n
      refine ContinuousLinearMap.ext fun x => ?_
      rw [transL2_apply, star_ketbraNat, ketbraNat_apply, star_smul, star_single]
      congr 1
      calc star (⟪(lp.single 2 0 (1 : ℂ) : ℓ²), star x⟫ : ℂ)
          = star (⟪star (lp.single 2 0 (1 : ℂ) : ℓ²), star x⟫ : ℂ) := by rw [star_single]
        _ = star (star (⟪(lp.single 2 0 (1 : ℂ) : ℓ²), x⟫ : ℂ)) := by rw [star_inner_l2]
        _ = ⟪(lp.single 2 0 (1 : ℂ) : ℓ²), x⟫ := star_star _
    simp only [hkb, hzero] at h
    exact h

end Transpose

/-- **45II** (`cp-uscont`, vn.tex:841, Proposition): an ncp-map between von
Neumann algebras is ultrastrongly continuous. -/
theorem cp_uscont [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : NCPMap A B) :
    @Continuous A B (ultrastrong A) (ultrastrong B) ⇑f := by
  -- The thesis's estimate `f(b)* f(b) ≤ ‖f(1)‖ f(b* b)` (**34XIV** `cp-cs`)
  -- says exactly that `f` is `‖·‖_ω`-bounded from `‖·‖_{ω∘f}`, and `ω ∘ f`
  -- is an np-functional because `f` is normal.  (The thesis argues with
  -- nets through the ultraweak continuity of `f`; the ultrastrong topology
  -- is not first countable, so the estimate is applied to the generating
  -- balls directly instead.)
  refine continuous_ultrastrong_of_omegaNorm_bound
    (fun x y => (map_sub f.toCompletelyPositiveMap x y).symm) ?_
  intro ω
  refine ⟨compNP (ncpPositive f) f.preservesDirSups' ω, Real.sqrt ‖(f 1 : B)‖,
    Real.sqrt_nonneg _, fun x => ?_⟩
  have hmono : (ω (star (f x : B) * f x) : ℂ)
      ≤ ω ((‖(f 1 : B)‖ : ℝ) • f (star x * x)) := npFunctional_mono ω (ncp_cp_cs f x)
  rw [npFunctional_real_smul] at hmono
  have hre : (ω (star (f x : B) * f x)).re
      ≤ ‖(f 1 : B)‖ * (ω (f (star x * x))).re := by
    have h1 := (Complex.le_def.mp hmono).1
    simpa using h1
  have hnorm : omegaNorm A (compNP (ncpPositive f) f.preservesDirSups' ω) x
      = Real.sqrt (ω (f (star x * x))).re := rfl
  rw [omegaNorm, hnorm, ← Real.sqrt_mul (norm_nonneg _)]
  exact Real.sqrt_le_sqrt hre

/-- `ad_cp_1` is stated for `mulLeft (b*) ∘ mulRight b`, which is
`adPositive b` up to associativity. -/
private theorem adLinearMap_eq (b : A) :
    ((LinearMap.mulLeft ℂ (star b)).comp (LinearMap.mulRight ℂ b))
      = (adPositive b).toLinearMap :=
  LinearMap.ext fun a => (mul_assoc (star b) a b).symm

/-- `a ↦ b* a b` as an ncp-map: completely positive by **34V**.1
(`ad-cp`.1, cstar.tex:5575), normal by **44VIII** (`ad_normal`).  This is the
object **45IV** asks `cp_uscont` to be applied to. -/
private noncomputable def adNCP [VonNeumannAlgebra A] (b : A) : NCPMap A A where
  toCompletelyPositiveMap :=
    { toLinearMap := (adPositive b).toLinearMap
      map_cstarMatrix_nonneg' :=
        (Theses.A.CStar.cp_iff (adPositive b).toLinearMap).out 0 1 |>.mp
          (adLinearMap_eq b ▸ Theses.A.CStar.ad_cp_1 b) }
  preservesDirSups' := adPositive_normal b

/-- **45IV** (`mult-uws-cont`, vn.tex:868, Exercise), part 1: `a ↦ b* a b`
is ultrastrongly continuous for every `b` in a von Neumann algebra.

This is the exercise's own route, verbatim: "Conclude (using `cp-uscont`
and `ad-cp`) that the map `a ↦ b* a b` is ultrastrongly continuous".  The
map is an ncp-map (`adNCP`: complete positivity is **34V**.1 `ad_cp_1`,
normality is **44VIII** `ad_normal`), so **45II** `cp_uscont` applies. -/
theorem mult_uws_cont_ad [VonNeumannAlgebra A] (b : A) :
    @Continuous A A (ultrastrong A) (ultrastrong A) fun a => star b * a * b :=
  cp_uscont (adNCP b)

/-- **45IV** (`mult-uws-cont`, vn.tex:868, Exercise), part 2: multiplication
by a fixed element, `b ↦ ab` and `b ↦ ba`, is ultraweakly and ultrastrongly
continuous. -/
theorem mult_uws_cont [VonNeumannAlgebra A] (a : A) :
    (@Continuous A A (ultraweak A) (ultraweak A) fun b => a * b) ∧
      (@Continuous A A (ultraweak A) (ultraweak A) fun b => b * a) ∧
      (@Continuous A A (ultrastrong A) (ultrastrong A) fun b => a * b) ∧
      (@Continuous A A (ultrastrong A) (ultrastrong A) fun b => b * a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ultraweakly: polarisation (**44II**) writes `ω(ax)` as a
    -- `ℂ`-combination of np-functionals
    refine continuous_ultraweak_of_forall _ fun ω => ?_
    simpa using continuous_ultraweak_conj ω a 1
  · refine continuous_ultraweak_of_forall _ fun ω => ?_
    simpa using continuous_ultraweak_conj ω 1 a
  · -- ultrastrongly: `‖ax‖_ω ≤ ‖a‖ ‖x‖_ω` and `‖xa‖_ω = ‖x‖_{a*ω}`
    refine continuous_ultrastrong_of_omegaNorm_bound (fun x y => by noncomm_ring) ?_
    exact fun ω => ⟨ω, ‖a‖, norm_nonneg a, fun x => omegaNorm_mul_le ω a x⟩
  · refine continuous_ultrastrong_of_omegaNorm_bound (fun x y => by noncomm_ring) ?_
    exact fun ω => ⟨conjNP a ω, 1, zero_le_one, fun x => by
      rw [omegaNorm_mul_right, one_mul]⟩

/-- **45VI** (`mult-jus-cont`, vn.tex:892, Proposition): if nets `(a_α)_α`,
`(b_α)_α` converge ultrastrongly to `a`, `b` respectively and `(a_α)_α` is
norm-bounded, then `(a_α b_α)_α` converges ultrastrongly to `ab`. -/
theorem mult_jus_cont [VonNeumannAlgebra A] {ι : Type*} {l : Filter ι}
    (x y : ι → A) (a b : A) (hx : USTendsto x l a) (hy : USTendsto y l b)
    (hbdd : ∃ C : ℝ, ∀ i, ‖x i‖ ≤ C) :
    USTendsto (fun i => x i * y i) l (a * b) := by
  -- vn.tex:906 verbatim: `‖ab − a_α b_α‖_ω ≤ ‖(a−a_α)b‖_ω + ‖a_α(b−b_α)‖_ω`
  -- `≤ ‖a−a_α‖_{ω(b*(·)b)} + ‖a_α‖ ‖b−b_α‖_ω`.
  obtain ⟨C, hC⟩ := hbdd
  refine (usTendsto_iff _ l _).mpr fun ω => ?_
  have h1 := (usTendsto_iff x l a).mp hx (conjNP b ω)
  have h2 := (usTendsto_iff y l b).mp hy ω
  have hle : ∀ i : ι, omegaNorm A ω (x i * y i - a * b) ≤
      omegaNorm A (conjNP b ω) (x i - a) + C * omegaNorm A ω (y i - b) := by
    intro i
    calc omegaNorm A ω (x i * y i - a * b)
        ≤ omegaNorm A ω (x i * y i - x i * b)
          + omegaNorm A ω (x i * b - a * b) := omegaNorm_sub_le ω _ _ _
      _ = omegaNorm A ω (x i * (y i - b))
          + omegaNorm A (conjNP b ω) (x i - a) := by
          rw [← mul_sub, ← sub_mul, omegaNorm_mul_right ω (x i - a) b]
      _ ≤ ‖x i‖ * omegaNorm A ω (y i - b)
          + omegaNorm A (conjNP b ω) (x i - a) := by
          linarith [omegaNorm_mul_le ω (x i) (y i - b)]
      _ ≤ omegaNorm A (conjNP b ω) (x i - a)
          + C * omegaNorm A ω (y i - b) := by
          have := mul_le_mul_of_nonneg_right (hC i) (omegaNorm_nonneg ω (y i - b))
          linarith
  refine squeeze_zero' (Eventually.of_forall fun i => omegaNorm_nonneg ω _)
    (Eventually.of_forall hle) ?_
  simpa using h1.add (h2.const_mul C)

/-! ## Parsec 460 -/

/-- **46II** (`usconv`, vn.tex:930, Exercise): a net `(b_α)_α` converges
ultrastrongly to `b` iff both `b_α* b_α → b* b` and `b_α → b`
ultraweakly. -/
theorem usconv [VonNeumannAlgebra A] {ι : Type*} (x : ι → A) (l : Filter ι)
    (b : A) :
    USTendsto x l b ↔
      UWTendsto (fun i => star (x i) * x i) l (star b * b) ∧
        UWTendsto x l b := by
  -- `ω(y*y) = ‖y‖_ω²`, so the two ultraweak conditions are exactly
  -- `‖x_α‖_ω → ‖b‖_ω` and `ω(b*x_α) → ω(b*b)`, and
  -- `‖x_α − b‖_ω² = ω(x_α*x_α) − 2 Re ω(b*x_α) + ω(b*b)`.
  have hcoe : ∀ (ω : NPFunctional A) (y : A),
      (ω (star y * y) : ℂ) = ((omegaNorm A ω y ^ 2 : ℝ) : ℂ) := by
    intro ω y
    obtain ⟨hre, him⟩ :=
      Complex.le_def.mp (npFunctional_nonneg ω (star_mul_self_nonneg y))
    rw [omegaNorm, Real.sq_sqrt (by simpa using hre)]
    exact Complex.ext rfl (by simpa using him.symm)
  constructor
  · intro h
    refine ⟨(uwTendsto_iff _ l _).mpr fun ω => ?_, uwweaker_2 x l b h⟩
    have hω := (usTendsto_iff x l b).mp h ω
    have hn : Tendsto (fun i => omegaNorm A ω (x i)) l (𝓝 (omegaNorm A ω b)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun i => dist_nonneg) (fun i => ?_) hω
      rw [Real.dist_eq]
      exact abs_omegaNorm_sub_omegaNorm_le ω (x i) b
    simp only [hcoe]
    exact (Complex.continuous_ofReal.tendsto _).comp (hn.pow 2)
  · rintro ⟨h1, h2⟩
    refine (usTendsto_iff x l b).mpr fun ω => ?_
    have e1 := (uwTendsto_iff _ l _).mp h1 ω
    have e2 : Tendsto (fun i => (ω (star b * x i) : ℂ)) l (𝓝 (ω (star b * b))) := by
      have hc := @Continuous.tendsto A ℂ (ultraweak A) _ _
        (continuous_ultraweak_conj ω (star b) 1) b
      have := hc.comp h2
      simpa [Function.comp_def] using this
    have e3 : Tendsto (fun i => (ω (star (x i) * b) : ℂ)) l (𝓝 (ω (star b * b))) := by
      have hconj := (Complex.continuous_conj.tendsto (ω (star b * b))).comp e2
      have hsb : ∀ i, (ω (star (x i) * b) : ℂ) = (starRingEnd ℂ) (ω (star b * x i)) := by
        intro i
        rw [starRingEnd_apply, ← npFunctional_star ω, star_mul, star_star]
      have hbb : (starRingEnd ℂ) (ω (star b * b)) = ω (star b * b) := by
        rw [starRingEnd_apply, ← npFunctional_star ω, star_mul, star_star]
      simp only [Function.comp_def, hbb] at hconj
      exact hconj.congr fun i => (hsb i).symm
    have key : ∀ i, ((omegaNorm A ω (x i - b) ^ 2 : ℝ) : ℂ)
        = ω (star (x i) * x i) - ω (star (x i) * b) - ω (star b * x i)
          + ω (star b * b) := by
      intro i
      rw [← hcoe ω (x i - b)]
      have hexp : star (x i - b) * (x i - b)
          = star (x i) * x i - star (x i) * b - star b * x i + star b * b := by
        rw [star_sub]; noncomm_ring
      rw [hexp]
      have hadd : ∀ u v : A, (ω (u + v) : ℂ) = ω u + ω v := fun u v =>
        map_add ω.toPositiveLinearMap u v
      rw [hadd, npFunctional_sub, npFunctional_sub]
    have hlim : Tendsto (fun i => ((omegaNorm A ω (x i - b) ^ 2 : ℝ) : ℂ)) l (𝓝 0) := by
      have hz : (ω (star b * b) : ℂ) - ω (star b * b) - ω (star b * b)
          + ω (star b * b) = 0 := by ring
      refine Tendsto.congr (fun i => (key i).symm) ?_
      rw [← hz]
      exact ((e1.sub e3).sub e2).add tendsto_const_nhds
    have hsq : Tendsto (fun i => omegaNorm A ω (x i - b) ^ 2) l (𝓝 0) := by
      have := (Complex.continuous_re.tendsto (0 : ℂ)).comp hlim
      simp only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] at this
      exact this
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (omegaNorm_nonneg ω _)] using this

/-- **46III**, (3) ⇒ (1): an ultrastrongly continuous positive functional is
normal.  (This is **45I**.1 for `B = ℂ`, without the restriction to the
effects: the net `(d)_{d∈D}` converges ultrastrongly to `⋁D` by **44XIV**
`vna_supremum_uslimit`, so `ω(d) → ω(⋁D)`, and `ω(d) ≤ z` for every upper
bound `z` of the image.) -/
theorem preservesDirSups_of_continuous_ultrastrong [VonNeumannAlgebra A]
    (ω : A →ₚ[ℂ] ℂ) (h : @Continuous A ℂ (ultrastrong A) _ ⇑ω) :
    PreservesDirSups ⇑ω := by
  intro D s hne hdir hlub
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact ω.monotone (Subtype.coe_le_coe.mpr (hlub.1 hd))
  intro z hz
  have hbdd : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hsup : dirSup D hbdd = s := (isLUB_dirSup D hbdd).unique hlub
  have hnonempty : Nonempty D := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hdo : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  -- the net converges ultrastrongly to `⋁D`
  have hnet : USTendsto (fun d : D => ((d : selfAdjoint A) : A)) atTop (s : A) := by
    have := vna_supremum_uslimit D hbdd
    rwa [hsup] at this
  have htend : Tendsto (fun d : D => (ω ((d : selfAdjoint A) : A) : ℂ)) atTop (𝓝 (ω (s : A))) :=
    ((@Continuous.tendsto A ℂ (ultrastrong A) _ ⇑ω h ((s : selfAdjoint A) : A)).comp hnet)
  have hle : ∀ d : D, (ω ((d : selfAdjoint A) : A) : ℂ) ≤ z := fun d =>
    hz ⟨(d : selfAdjoint A), d.2, rfl⟩
  -- compare real and imaginary parts separately
  have hre : (ω (s : A)).re ≤ z.re := by
    refine le_of_tendsto ((Complex.continuous_re.tendsto _).comp htend) ?_
    exact Eventually.of_forall fun d => (Complex.le_def.mp (hle d)).1
  have him : (ω (s : A)).im = z.im := by
    have h1 : Tendsto (fun d : D => (ω ((d : selfAdjoint A) : A) : ℂ).im) atTop
        (𝓝 (ω (s : A)).im) := (Complex.continuous_im.tendsto _).comp htend
    have h2 : Tendsto (fun d : D => (ω ((d : selfAdjoint A) : A) : ℂ).im) atTop (𝓝 z.im) := by
      refine Tendsto.congr' (Eventually.of_forall fun d => ?_) tendsto_const_nhds
      exact ((Complex.le_def.mp (hle d)).2).symm
    exact tendsto_nhds_unique h1 h2
  exact Complex.le_def.mpr ⟨hre, him⟩

/-- **46III** (`npuws`, vn.tex:940, Exercise): for a positive functional `ω`
on a von Neumann algebra, the following are equivalent: (1) `ω` is normal;
(2) `ω` is ultraweakly continuous; (3) `ω` is ultrastrongly continuous. -/
theorem npuws [VonNeumannAlgebra A] (ω : A →ₚ[ℂ] ℂ) :
    List.TFAE
      [PreservesDirSups ⇑ω,
       @Continuous A ℂ (ultraweak A) _ ⇑ω,
       @Continuous A ℂ (ultrastrong A) _ ⇑ω] := by
  tfae_have 1 → 2 := fun h => continuous_ultraweak_npFunctional ⟨ω, h⟩
  tfae_have 2 → 3 := fun h => continuous_le_dom ultrastrong_le_ultraweak h
  tfae_have 3 → 1 := preservesDirSups_of_continuous_ultrastrong ω
  tfae_finish

/-! ## Parsec 470: the categor(ies) of von Neumann algebras

**47II** (vn.tex:960, Definition): the categories `W*_cpsu` (von Neumann
algebras with normal cpsu-maps) and `W*_miu` (with nmiu-maps).  The
morphisms are formalized as `Theses.NCPSUMap` and `Theses.NMIUMap`; the
categorical structure itself is not bundled *here* — the product (47IV) and
equaliser (47V) below are stated through their universal properties, which
is what the thesis uses.  It **is** bundled downstream, and this sentence
should not be read as "nowhere": `W*_miu` is `WMIU` with its `Category`
instance in `A/Proc/QuantumLambda.lean`, and `W*_cpsu` is `WStarCPSU` with
its `Category` instance in `B/Eff/WStarCat.lean` (whose `WStarNCPU` is the
thesis's `vN`).  What really is unbundled is `CStar_pu` (needed for 84aI)
and the full subcategories `haW*_miu`, `haW*_cpsu`.

**47VI** (`vn-effectus`, vn.tex:1017): the sketch that `(W*_cpsu)^op` is an
effectus refers forward to the precise treatment in thesis B (eff.tex);
nothing is formalized here. -/

section Products

/- As in `section DirectSum` above, the `[∀ i, Nontrivial (𝒜 i)]` binder is
Mathlib's, not 47IV's: it is what the unital C*-structure on `lp 𝒜 ∞`
demands.  See the note there. -/

variable {I : Type*} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)] [∀ i, PartialOrder (𝒜 i)]
  [∀ i, StarOrderedRing (𝒜 i)] [∀ i, VonNeumannAlgebra (𝒜 i)]

/-- **47IV** (`vn-products`, vn.tex:988, Exercise), part 2: the coordinate
projections `π_j : ⊕ᵢ𝒜ᵢ → 𝒜ⱼ` are normal (they are miu-maps by cstar.tex
20aI). -/
theorem vn_products_proj_normal (j : I) :
    PreservesDirSups fun a : lp 𝒜 ∞ => (a : ∀ i, 𝒜 i) j := by
  intro D s hne hdir hlub
  obtain ⟨s', hs', hev⟩ := lp_infty_exists_isLUB D hne hdir ⟨s, hlub.1⟩
  obtain rfl := hlub.unique hs'
  have h := isLUB_coe_of_isLUB (hne.image (lpEvalSA j)) (hev j)
  rwa [Set.image_image] at h

/-- **47IV** (`vn-products`, vn.tex:988, Exercise), part 3 (`W*_miu`):
`⊕ᵢ𝒜ᵢ` with the projections `π_j` is the product of the `𝒜ᵢ` in `W*_miu`:
every family of nmiu-maps `f_i : B → 𝒜ᵢ` factors through a unique nmiu-map
`g : B → ⊕ᵢ𝒜ᵢ`.

*The von Neumann hypotheses are not used* (hence the deliberate
`unusedSectionVars` warning, left in place as evidence, as for **112IX** and
**105IV**.2): the ∗-algebra half is **20aI** `cstar_product_2_miu` and
normality of the mediating map follows from normality of the `fᵢ` because the
order on `⊕ᵢ𝒜ᵢ` is pointwise (`lp_infty_le_iff`).  Kept as the thesis states
it, since 47IV is a statement about von Neumann algebras. -/
theorem vn_products_nmiu {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : ∀ i, NMIUMap B (𝒜 i)) :
    ∃! g : NMIUMap B (lp 𝒜 ∞), ∀ (j : I) (b : B),
      ((g b : lp 𝒜 ∞) : ∀ i, 𝒜 i) j = f j b := by
  obtain ⟨g₀, hg₀, -⟩ := cstar_product_2_miu (fun i => (f i).toStarAlgHom)
  have hnorm : PreservesDirSups ⇑g₀ := by
    intro D s hne hdir hlub
    have key : ∀ (j : I) (d : selfAdjoint B),
        ((g₀ (d : B) : lp 𝒜 ∞) : ∀ i, 𝒜 i) j = f j (d : B) := fun j d => hg₀ j _
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      rw [lp_infty_le_iff]
      intro j
      rw [key j d, key j s]
      exact ((f j).preservesDirSups' D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro u hu
      rw [lp_infty_le_iff]
      intro j
      rw [key j s]
      refine ((f j).preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have hd' := (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) j
      rwa [key j d] at hd'
  refine ⟨⟨g₀, hnorm⟩, hg₀, ?_⟩
  intro g' hg'
  apply DFunLike.coe_injective
  funext b
  apply lp.ext
  funext j
  rw [hg' j b]
  exact (hg₀ j b).symm

/-- **47IV** (`vn-products`, vn.tex:988, Exercise), part 3 (`W*_cpsu`):
`⊕ᵢ𝒜ᵢ` is also the product in `W*_cpsu`: every family of ncpsu-maps
`f_i : B → 𝒜ᵢ` factors through a unique ncpsu-map `g : B → ⊕ᵢ𝒜ᵢ`.

*As for `vn_products_nmiu`, the von Neumann hypotheses on the `𝒜ᵢ` are not
used* (hence the deliberate `unusedSectionVars` warning): the C*-half is
**34VI**.4 `cstar_product_4`, which already delivers complete positivity and
subunitality of the mediating map, and normality is pointwise because the
order on `⊕ᵢ𝒜ᵢ` is (`lp_infty_le_iff`). -/
theorem vn_products_ncpsu {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : ∀ i, NCPSUMap B (𝒜 i)) :
    ∃! g : NCPSUMap B (lp 𝒜 ∞), ∀ (j : I) (b : B),
      ((g.toNCPMap b : lp 𝒜 ∞) : ∀ i, 𝒜 i) j = (f j).toNCPMap b := by
  have hcp : ∀ i, IsCompletelyPositiveMap
      ((f i).toNCPMap.toCompletelyPositiveMap.toLinearMap) := fun i =>
    (cp_iff _).out 1 0 |>.mp fun N M hM =>
      (f i).toNCPMap.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hsu : ∀ i, Subunital ⇑((f i).toNCPMap.toCompletelyPositiveMap.toLinearMap) :=
    fun i => (f i).subunital'
  obtain ⟨g, ⟨hgcp, hgsu, hgval⟩, -⟩ :=
    cstar_product_4 (𝒜f := 𝒜)
      (fun i => (f i).toNCPMap.toCompletelyPositiveMap.toLinearMap) hcp hsu
  have hgcp' : IsCompletelyPositiveMap g := hgcp
  have hnorm : PreservesDirSups ⇑g := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      rw [lp_infty_le_iff]
      intro j
      rw [hgval j, hgval j]
      exact ((f j).toNCPMap.preservesDirSups' D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro u hu
      rw [lp_infty_le_iff]
      intro j
      rw [hgval j]
      refine ((f j).toNCPMap.preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have hd' := (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) j
      rwa [hgval j] at hd'
  refine ⟨{ toNCPMap :=
              { toCompletelyPositiveMap :=
                  { toLinearMap := g,
                    map_cstarMatrix_nonneg' := (cp_iff g).out 0 1 |>.mp hgcp' },
                preservesDirSups' := hnorm },
            subunital' := hgsu }, hgval, ?_⟩
  rintro ⟨nc, su⟩ hg'
  congr 1
  apply DFunLike.coe_injective
  funext b
  apply lp.ext
  funext j
  rw [hg' j b]
  exact (hgval j b).symm

end Products

/-! ### 47IV over the nontrivial summands only

As for 42V.3 above: the `[∀ i, Nontrivial (𝒜 i)]` of `section Products` is
Mathlib's, and over `J = {i // Nontrivial (𝒜 i)}` it is discharged by
`fun j => j.2`, so the primed corollaries below are 47IV as printed — the
identification of `⊕_{j : J} 𝒜ⱼ` with `⊕ᵢ𝒜ᵢ` being `lpInftyNontrivialEquiv`
(`A/CStar/Positive.lean`).  The binders are written out on each statement
rather than taken from a `variable` block, so that no `Nontrivial` binder can
be picked up automatically. -/

section ProductsNontrivial

attribute [local instance] nontrivial_of_nontrivialIndex

/-- **47IV**.2 without the Mathlib binder: over the nontrivial indices, which is
the whole sum up to `lpInftyNontrivialEquiv` (`A/CStar/Positive.lean`). -/
theorem vn_products_proj_normal' {I : Type*} {𝒜 : I → Type u}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] (j : {i // Nontrivial (𝒜 i)}) :
    PreservesDirSups fun a : lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞ =>
      (a : ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j :=
  vn_products_proj_normal (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) j

/-- **47IV**.3 (`W*_miu`) without the Mathlib binder: over the nontrivial
indices, which is the whole sum up to `lpInftyNontrivialEquiv`
(`A/CStar/Positive.lean`). -/
theorem vn_products_nmiu' {I : Type*} {𝒜 : I → Type u}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B]
    (f : ∀ j : {i // Nontrivial (𝒜 i)}, NMIUMap B (𝒜 j)) :
    ∃! g : NMIUMap B (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞),
      ∀ (j : {i // Nontrivial (𝒜 i)}) (b : B),
        ((g b : lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞) :
            ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j = f j b :=
  vn_products_nmiu (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) f

/-- **47IV**.3 (`W*_cpsu`) without the Mathlib binder: over the nontrivial
indices, which is the whole sum up to `lpInftyNontrivialEquiv`
(`A/CStar/Positive.lean`). -/
theorem vn_products_ncpsu' {I : Type*} {𝒜 : I → Type u}
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B]
    (f : ∀ j : {i // Nontrivial (𝒜 i)}, NCPSUMap B (𝒜 j)) :
    ∃! g : NCPSUMap B (lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞),
      ∀ (j : {i // Nontrivial (𝒜 i)}) (b : B),
        ((g.toNCPMap b : lp (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) ∞) :
            ∀ j : {i // Nontrivial (𝒜 i)}, 𝒜 j) j = (f j).toNCPMap b :=
  vn_products_ncpsu (fun j : {i // Nontrivial (𝒜 i)} => 𝒜 j) f

end ProductsNontrivial

section Elementary

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **47V** (`vn-equalisers`, vn.tex:1006, Exercise): for nmiu-maps
`f, g : A → B` between von Neumann algebras, the set
`E = {a ∈ A | f(a) = g(a)}` is (the carrier of) a von Neumann subalgebra of
`A`; its inclusion is then the equaliser of `f` and `g` in `W*_miu` and
`W*_cpsu`, which is `vn_equalisers_miu` / `vn_equalisers_cpsu` below (stated
there for an arbitrary realisation of `E` as a von Neumann algebra, since
this file has no von Neumann structure on a subalgebra as a type). -/
theorem vn_equalisers [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f g : NMIUMap A B) :
    ∃ S : StarSubalgebra ℂ A, IsVNSubalgebra A S ∧
      (S : Set A) = {a : A | f a = g a} := by
  classical
  -- `E` is a ∗-subalgebra as the equalizer of two ∗-homomorphisms
  -- (`StarAlgHom.equalizer`); it is norm-closed because miu-maps are
  -- contractive, hence continuous; and it is closed under directed suprema
  -- because `f` and `g` are normal, so `f(⋁D)` and `g(⋁D)` are both suprema
  -- of the *same* set `f''D = g''D`.
  refine ⟨StarAlgHom.equalizer f.toStarAlgHom g.toStarAlgHom, ⟨?_, ?_⟩, rfl⟩
  · have hfc : Continuous ⇑f.toStarAlgHom :=
      AddMonoidHomClass.continuous_of_bound f.toStarAlgHom 1 fun a => by
        simpa using norm_mi_map_contractive f.toStarAlgHom a
    have hgc : Continuous ⇑g.toStarAlgHom :=
      AddMonoidHomClass.continuous_of_bound g.toStarAlgHom 1 fun a => by
        simpa using norm_mi_map_contractive g.toStarAlgHom a
    exact isClosed_eq hfc hgc
  · intro D s hDsub hne hdir hlub
    have hf := f.preservesDirSups' D s hne hdir hlub
    have hg := g.preservesDirSups' D s hne hdir hlub
    have himg : (fun d : selfAdjoint A => (f.toStarAlgHom (d : A) : B)) '' D
        = (fun d : selfAdjoint A => (g.toStarAlgHom (d : A) : B)) '' D := by
      ext y
      constructor
      · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, (hDsub d hd).symm⟩
      · rintro ⟨d, hd, rfl⟩; exact ⟨d, hd, hDsub d hd⟩
    rw [himg] at hf
    show f.toStarAlgHom (s : A) = g.toStarAlgHom (s : A)
    exact hf.unique hg

/-! ## Parsec 480: the normal Gelfand–Naimark theorem -/

/-- A collection `Ω` of np-functionals is **faithful** (`separating`,
cstar.tex 21II): `a = 0` whenever `a ≥ 0` and `ω(a) = 0` for all
`ω ∈ Ω`. -/
def FaithfulCollection (Ω : Set (NPFunctional A)) : Prop :=
  ∀ a : A, 0 ≤ a → (∀ ω ∈ Ω, ω a = 0) → a = 0

/-- **48II** (`normal-faithful`, vn.tex:1082, Exercise): if `Ω` is a
faithful collection of np-functionals on `B`, then a positive linear map
`f : A → B` between von Neumann algebras is normal iff `ω ∘ f` is normal for
all `ω ∈ Ω`. -/
theorem normal_faithful [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (Ω : Set (NPFunctional B)) (hΩ : FaithfulCollection Ω) (f : A →ₚ[ℂ] B) :
    PreservesDirSups ⇑f ↔
      ∀ ω ∈ Ω, PreservesDirSups fun a => ω (f a) := by
  refine ⟨fun hf ω _ => (compNP f hf ω).preservesDirSups', fun h => ?_⟩
  intro D s hne hdir hlub
  -- the image `G ⊆ sa(B)` of `D` is nonempty, directed and bounded by `f s`
  set G : Set (selfAdjoint B) := imageSA f D with hG
  have hfs : IsSelfAdjoint (f (s : A)) := isSelfAdjoint_map_of_positive f s.2
  have hub : (⟨f (s : A), hfs⟩ : selfAdjoint B) ∈ upperBounds G := by
    rintro _ ⟨d, hd, rfl⟩
    exact Subtype.coe_le_coe.mp (f.monotone (Subtype.coe_le_coe.mpr (hlub.1 hd)))
  have hGne : G.Nonempty := imageSA_nonempty f hne
  have hGdir : DirectedOn (· ≤ ·) G := imageSA_directedOn f hdir
  have hGdata : G.Nonempty ∧ DirectedOn (· ≤ ·) G ∧ BddAbove G :=
    ⟨hGne, hGdir, ⟨_, hub⟩⟩
  set u : selfAdjoint B := dirSup G hGdata with hu
  have hlubG : IsLUB G u := isLUB_dirSup G hGdata
  -- every `ω ∈ Ω` cannot tell `⋁ G` from `f (⋁ D)`
  have hsets : (fun d : selfAdjoint B => ((d : B))) '' G
      = (fun d : selfAdjoint A => f (d : A)) '' D := coe_imageSA f D
  have hzero : (f (s : A)) - (u : B) = 0 := by
    refine hΩ _ (sub_nonneg.mpr (Subtype.coe_le_coe.mpr (hlubG.2 hub))) ?_
    intro ω hωΩ
    have h1 : IsLUB ((fun d : selfAdjoint B => (ω (d : B) : ℂ)) '' G) (ω (u : B)) :=
      ω.preservesDirSups' G u hGne hGdir hlubG
    have h2 : IsLUB ((fun d : selfAdjoint A => (ω (f (d : A)) : ℂ)) '' D)
        (ω (f (s : A))) := h ω hωΩ D s hne hdir hlub
    have h3 : (fun d : selfAdjoint B => (ω (d : B) : ℂ)) '' G
        = (fun d : selfAdjoint A => (ω (f (d : A)) : ℂ)) '' D := by
      rw [hG, imageSA, ← Set.image_comp]; rfl
    rw [h3] at h1
    rw [npFunctional_sub, h1.unique h2, sub_self]
  have hfsu : f (s : A) = (u : B) := sub_eq_zero.mp hzero
  refine ⟨?_, fun t ht => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact f.monotone (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · rw [hfsu]
    have htG : ∀ g ∈ G, ((g : B)) ≤ t := by
      rintro _ ⟨d, hd, rfl⟩
      exact ht ⟨d, hd, rfl⟩
    obtain ⟨g₀, hg₀⟩ := hGne
    have htsa : IsSelfAdjoint t := by
      have hd : IsSelfAdjoint (t - ((g₀ : selfAdjoint B) : B)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr (htG g₀ hg₀))
      simpa using hd.add g₀.2
    exact Subtype.coe_le_coe.mpr
      (hlubG.2 (fun g hg => Subtype.coe_le_coe.mp (htG g hg)) :
        u ≤ (⟨t, htsa⟩ : selfAdjoint B))

section NGNSConstruction

variable {C : Type u} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

section StarAlgHomAux

variable {X : Type*} [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
variable {Y : Type*} [CStarAlgebra Y] [PartialOrder Y] [StarOrderedRing Y]

/-- A ∗-homomorphism between C*-algebras is positive.  General form: domain
and codomain need not lie in a *common* universe.  (`starAlgHom_nonneg` just
below is this statement with both in `Type u`, and is what the audit records.) -/
theorem starAlgHom_nonneg_general (φ : X →⋆ₐ[ℂ] Y) {x : X} (hx : 0 ≤ x) : 0 ≤ φ x := by
  have hs : CFC.sqrt x * CFC.sqrt x = x := CFC.sqrt_mul_sqrt_self x hx
  have hsa : IsSelfAdjoint (CFC.sqrt x) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)
  have h : φ x = star (φ (CFC.sqrt x)) * φ (CFC.sqrt x) := by
    rw [← map_star, hsa.star_eq, ← map_mul, hs]
  rw [h]
  exact star_mul_self_nonneg _

/-- A ∗-homomorphism between C*-algebras is monotone.  General form; see
`starAlgHom_nonneg_general`. -/
theorem starAlgHom_mono_general (φ : X →⋆ₐ[ℂ] Y) {x y : X} (hxy : x ≤ y) : φ x ≤ φ y := by
  have h := starAlgHom_nonneg_general φ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A ∗-homomorphism between C*-algebras is positive. -/
theorem starAlgHom_nonneg (φ : A →⋆ₐ[ℂ] C) {x : A} (hx : 0 ≤ x) : 0 ≤ φ x :=
  starAlgHom_nonneg_general φ hx

/-- A ∗-homomorphism between C*-algebras is monotone. -/
theorem starAlgHom_mono (φ : A →⋆ₐ[ℂ] C) {x y : A} (hxy : x ≤ y) : φ x ≤ φ y :=
  starAlgHom_mono_general φ hxy

/-- A ∗-homomorphism between C*-algebras, viewed as a positive linear map. -/
noncomputable def starAlgHomP (φ : A →⋆ₐ[ℂ] C) : A →ₚ[ℂ] C where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ
  monotone' := fun _ _ h => starAlgHom_mono φ h

@[simp] theorem starAlgHomP_apply (φ : A →⋆ₐ[ℂ] C) (x : A) : starAlgHomP φ x = φ x := rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- Auxiliary: a self-adjoint element with vanishing cube is zero.
(cstar.tex 30X uses this; the Mathlib-side proof there is `private`.) -/
theorem eq_zero_of_pow_three_eq_zero {y : A} (hy : IsSelfAdjoint y) (h : y ^ 3 = 0) :
    y = 0 := by
  have h4 : y ^ 2 * y ^ 2 = 0 := by
    have he : y ^ 2 * y ^ 2 = y * y ^ 3 := by noncomm_ring
    rw [he, h, mul_zero]
  have h2 : y ^ 2 = 0 := by
    have hn : ‖y ^ 2‖ * ‖y ^ 2‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, (hy.pow 2).star_eq, h4, norm_zero]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (y ^ 2)])
  have hn : ‖y‖ * ‖y‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, hy.star_eq, ← sq, h2, norm_zero]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])

/-- **48VI**.2 in its general C*-form, without the common-universe constraint:
an *injective* ∗-homomorphism between C*-algebras reflects the order.
(`starAlgHom_le_iff` just below is this statement with both algebras in
`Type u`, and is what the audit records.) -/
theorem starAlgHom_le_iff_general (φ : X →⋆ₐ[ℂ] Y) (hφ : Function.Injective φ)
    {x y : X} : φ x ≤ φ y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => starAlgHom_mono_general φ h⟩
  set z : X := y - x with hz
  have hφz : (0 : Y) ≤ φ z := by rw [hz, map_sub]; exact sub_nonneg.mpr h
  have hzsa : IsSelfAdjoint z := by
    have h1 : φ (star z) = φ z := by rw [map_star, (IsSelfAdjoint.of_nonneg hφz).star_eq]
    exact hφ h1
  have hn0 : negPart z = 0 := by
    have hnn : (0 : X) ≤ negPart z := CFC.negPart_nonneg z
    have hcube : (0 : X) ≤ negPart z ^ 3 := CStarAlgebra.pow_nonneg hnn 3
    have hnsa : IsSelfAdjoint (negPart z) := IsSelfAdjoint.of_nonneg hnn
    have hconj : negPart z * z * negPart z = -(negPart z ^ 3) := by
      have hd : posPart z - negPart z = z := CFC.posPart_sub_negPart z hzsa
      have hnp : negPart z * posPart z = 0 := CFC.negPart_mul_posPart z
      calc negPart z * z * negPart z
          = negPart z * (posPart z - negPart z) * negPart z := by rw [hd]
        _ = negPart z * posPart z * negPart z - negPart z ^ 3 := by noncomm_ring
        _ = -(negPart z ^ 3) := by rw [hnp, zero_mul, zero_sub]
    have hle : φ (negPart z ^ 3) ≤ 0 := by
      have hpos : (0 : Y) ≤ star (φ (negPart z)) * φ z * φ (negPart z) :=
        star_left_conjugate_nonneg hφz _
      rw [← map_star, hnsa.star_eq] at hpos
      have hrw : φ (negPart z) * φ z * φ (negPart z) = -φ (negPart z ^ 3) := by
        rw [← map_mul, ← map_mul, hconj, map_neg]
      rw [hrw] at hpos
      exact neg_nonneg.mp hpos
    have hzero : φ (negPart z ^ 3) = 0 :=
      le_antisymm hle (starAlgHom_nonneg_general φ hcube)
    have h3 : negPart z ^ 3 = 0 := by
      have := hφ (by rw [hzero, map_zero] : φ (negPart z ^ 3) = φ 0)
      exact this
    exact eq_zero_of_pow_three_eq_zero hnsa h3
  have hzpos : (0 : X) ≤ z := by
    have hd : posPart z - negPart z = z := CFC.posPart_sub_negPart z hzsa
    rw [hn0, sub_zero] at hd
    rw [← hd]
    exact CFC.posPart_nonneg z
  rw [hz] at hzpos
  exact sub_nonneg.mp hzpos


/-- **48VI**.2 in its general C*-form: an *injective* ∗-homomorphism between
C*-algebras reflects the order (hence is an order embedding). -/
theorem starAlgHom_le_iff (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) {x y : A} :
    φ x ≤ φ y ↔ x ≤ y :=
  starAlgHom_le_iff_general φ hφ

/-- Composition of normal positive maps is normal. -/
theorem preservesDirSups_pmap_comp (f : A →ₚ[ℂ] B) (hf : PreservesDirSups ⇑f)
    (g : B →ₚ[ℂ] C) (hg : PreservesDirSups ⇑g) :
    PreservesDirSups (fun a => g (f a)) := by
  intro D s hne hdir hlub
  set G : Set (selfAdjoint B) :=
    (fun d : selfAdjoint A =>
      (⟨f (d : A), isSelfAdjoint_map_of_positive f d.2⟩ : selfAdjoint B)) '' D with hG
  have hval : Subtype.val '' G = (fun d : selfAdjoint A => f (d : A)) '' D := by
    rw [hG, ← Set.image_comp]; rfl
  have hlubG : IsLUB G
      (⟨f (s : A), isSelfAdjoint_map_of_positive f s.2⟩ : selfAdjoint B) := by
    refine isLUB_sa_of_isLUB ?_
    rw [hval]
    exact hf D s hne hdir hlub
  have hGne : G.Nonempty := hne.image _
  have hGdir : DirectedOn (· ≤ ·) G := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨_, ⟨z, hz, rfl⟩,
      Subtype.coe_le_coe.mp (f.monotone (Subtype.coe_le_coe.mpr hxz)),
      Subtype.coe_le_coe.mp (f.monotone (Subtype.coe_le_coe.mpr hyz))⟩
  have hkey := hg G _ hGne hGdir hlubG
  rw [hG, ← Set.image_comp] at hkey
  exact hkey

/-- A ∗-isomorphism between C*-algebras is normal: it is an order
isomorphism, so it carries suprema to suprema. -/
theorem starAlgEquiv_preservesDirSups (Φ : A ≃⋆ₐ[ℂ] C) : PreservesDirSups ⇑Φ := by
  intro D s hne hdir hlub
  refine ⟨?_, fun t ht => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact starAlgHom_mono Φ.toStarAlgHom (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · have hcoe := isLUB_coe_of_isLUB hne hlub
    have hsym : ((s : selfAdjoint A) : A) ≤ Φ.symm t := by
      refine hcoe.2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have h := starAlgHom_mono Φ.symm.toStarAlgHom (ht ⟨d, hd, rfl⟩)
      simpa using h
    have h := starAlgHom_mono Φ.toStarAlgHom hsym
    simpa using h

/-- Kadison's definition (**42I**) transports along a ∗-isomorphism: both of
its clauses are order-theoretic, and a ∗-isomorphism is an order isomorphism
(`starAlgEquiv_preservesDirSups`).  Directed suprema are pulled back along
`Φ⁻¹` and pushed forward again; faithfulness of the np-functionals transfers
because `ψ ∘ Φ⁻¹` is an np-functional on `Y` for every np-functional `ψ` on
`X` (`compNP`).  (Both algebras must live in one universe, as everything in
this section does.) -/
theorem vonNeumannAlgebra_of_starAlgEquiv {X Y : Type u} [CStarAlgebra X]
    [PartialOrder X] [StarOrderedRing X] [CStarAlgebra Y] [PartialOrder Y]
    [StarOrderedRing Y] [VonNeumannAlgebra X] (Φ : X ≃⋆ₐ[ℂ] Y) :
    VonNeumannAlgebra Y where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    have hsa : ∀ d : selfAdjoint Y, IsSelfAdjoint (Φ.symm (d : Y)) := fun d =>
      (d.2 : IsSelfAdjoint (d : Y)).map Φ.symm
    have hmono : ∀ a b : Y, a ≤ b → (Φ.symm a : X) ≤ (Φ.symm b : X) := by
      intro a b h
      simpa using starAlgHom_mono Φ.symm.toStarAlgHom h
    set E : Set (selfAdjoint X) :=
      (fun d : selfAdjoint Y => (⟨Φ.symm (d : Y), hsa d⟩ : selfAdjoint X)) '' D with hE
    have hEne : E.Nonempty := hne.image _
    have hEdir : DirectedOn (· ≤ ·) E := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨_, ⟨z, hz, rfl⟩,
        Subtype.coe_le_coe.mp (hmono _ _ (Subtype.coe_le_coe.mpr hxz)),
        Subtype.coe_le_coe.mp (hmono _ _ (Subtype.coe_le_coe.mpr hyz))⟩
    have hEbdd : BddAbove E := by
      obtain ⟨u, hu⟩ := hbdd
      refine ⟨⟨Φ.symm (u : Y), hsa u⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact Subtype.coe_le_coe.mp (hmono _ _ (Subtype.coe_le_coe.mpr (hu hx)))
    obtain ⟨s, hs⟩ := VonNeumannAlgebra.isLUB_of_bddAbove_directed E hEne hEdir hEbdd
    refine ⟨⟨Φ (s : X), (s.2 : IsSelfAdjoint (s : X)).map Φ⟩, isLUB_sa_of_isLUB ?_⟩
    have h := starAlgEquiv_preservesDirSups Φ E s hEne hEdir hs
    have himg : (fun d : selfAdjoint X => (Φ (d : X) : Y)) '' E = Subtype.val '' D := by
      rw [hE, ← Set.image_comp]
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by simp⟩
      · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by simp⟩
    rwa [himg] at h
  np_faithful := by
    intro y hy hall
    have hnorm : PreservesDirSups ⇑(starAlgHomP Φ.symm.toStarAlgHom) :=
      fun D s hne hdir hlub =>
        starAlgEquiv_preservesDirSups Φ.symm D s hne hdir hlub
    have hxnn : (0 : X) ≤ Φ.symm y := by
      have := starAlgHom_mono Φ.symm.toStarAlgHom hy
      rwa [map_zero] at this
    have hx0 : Φ.symm y = 0 := by
      refine VonNeumannAlgebra.np_faithful _ hxnn fun ψ => ?_
      have := hall (compNP (starAlgHomP Φ.symm.toStarAlgHom) hnorm ψ)
      simpa using this
    have := congrArg Φ hx0
    rwa [Φ.apply_symm_apply, map_zero] at this

end StarAlgHomAux

section HilbertRep

/-- A ∗-representation of a C*-algebra on a Hilbert space is a contraction:
`‖ϱ(a)x‖ ≤ ‖a‖‖x‖`.  (From `a*a ≤ ‖a‖²·1` and positivity of `ϱ`.) -/
theorem starAlgHom_apply_norm_le (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) (z : H) :
    ‖φ a z‖ ≤ ‖a‖ * ‖z‖ := by
  have h1 : star a * a ≤ algebraMap ℝ A (‖a‖ ^ 2) :=
    CStarAlgebra.star_mul_le_algebraMap_norm_sq
  have h2 : φ (algebraMap ℝ A (‖a‖ ^ 2)) = algebraMap ℝ (H →L[ℂ] H) (‖a‖ ^ 2) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ A, AlgHomClass.commutes,
      ← IsScalarTower.algebraMap_apply ℝ ℂ (H →L[ℂ] H)]
  have h3 : φ (star a * a) ≤ algebraMap ℝ (H →L[ℂ] H) (‖a‖ ^ 2) := by
    rw [← h2]; exact starAlgHom_mono φ h1
  have h4 : (⟪z, φ (star a * a) z⟫) ≤ ⟪z, (algebraMap ℝ (H →L[ℂ] H) (‖a‖ ^ 2)) z⟫ := by
    simpa using npFunctional_mono (vectorNP z) h3
  have hl : (⟪z, φ (star a * a) z⟫) = ((‖φ a z‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_mul, map_star]
    show ⟪z, (ContinuousLinearMap.adjoint (φ a)) (φ a z)⟫ = _
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hr : (⟪z, (algebraMap ℝ (H →L[ℂ] H) (‖a‖ ^ 2)) z⟫)
      = (((‖a‖ ^ 2 * ‖z‖ ^ 2 : ℝ)) : ℂ) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (H →L[ℂ] H), Algebra.algebraMap_eq_smul_one]
    rw [smul_apply, ContinuousLinearMap.one_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hl, hr, Complex.real_le_real] at h4
  have hsq : ‖φ a z‖ ^ 2 ≤ (‖a‖ * ‖z‖) ^ 2 := by rw [mul_pow]; exact h4
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq

/-- If a set `S` of vectors of `H` is "separating for operators" — only the
zero operator kills all of `S` — then the vector functionals it induces form
a faithful collection of np-functionals on `B(H)`.  (For `T ≥ 0`,
`⟪y,Ty⟫ = ‖√T y‖²`.) -/
theorem faithfulCollection_vectorNP (S : Set H)
    (hzero : ∀ R : H →L[ℂ] H, (∀ y ∈ S, R y = 0) → R = 0) :
    FaithfulCollection (A := H →L[ℂ] H) {ν | ∃ y ∈ S, ν = vectorNP y} := by
  intro T hT h
  have hR : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  have hRsa : IsSelfAdjoint (CFC.sqrt T) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hRadj : ContinuousLinearMap.adjoint (CFC.sqrt T) = CFC.sqrt T := hRsa.star_eq
  have hkill : ∀ y ∈ S, CFC.sqrt T y = 0 := by
    intro y hy
    have h0 : (vectorNP y : NPFunctional (H →L[ℂ] H)) T = 0 := h _ ⟨y, hy, rfl⟩
    rw [vectorNP_apply, ← hR, ContinuousLinearMap.mul_apply] at h0
    have hstep : ContinuousLinearMap.adjoint (CFC.sqrt T) (CFC.sqrt T y)
        = CFC.sqrt T (CFC.sqrt T y) := by rw [hRadj]
    have h1 : (⟪CFC.sqrt T y, CFC.sqrt T y⟫) = 0 := by
      rw [← h0, ← hstep, ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_zero.mp h1
  rw [← hR, hzero _ hkill, mul_zero]

variable [VonNeumannAlgebra A]

/-- **48II**-driven normality criterion for a ∗-representation
`ϱ : A → B(H)` of a von Neumann algebra: if a set `S` of vectors separates
the operators on `H`, and every `y ∈ S` makes `a ↦ ⟪y, ϱ(a)y⟫` an
np-functional on `A`, then `ϱ` is normal. -/
theorem starAlgHom_preservesDirSups_of_vectors (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : Set H)
    (hzero : ∀ R : H →L[ℂ] H, (∀ y ∈ S, R y = 0) → R = 0)
    (hnp : ∀ y ∈ S, ∃ ω : NPFunctional A, ∀ a : A, (⟪y, ρ a y⟫) = ω a) :
    PreservesDirSups ⇑ρ := by
  refine (normal_faithful _ (faithfulCollection_vectorNP S hzero) (starAlgHomP ρ)).mpr ?_
  rintro ν ⟨y, hy, rfl⟩
  obtain ⟨ω, hω⟩ := hnp y hy
  have heq : (fun a : A => (vectorNP y (starAlgHomP ρ a) : ℂ)) = fun a : A => (ω a : ℂ) := by
    funext a
    rw [starAlgHomP_apply, vectorNP_apply]
    exact hω a
  rw [heq]
  exact ω.preservesDirSups'

end HilbertRep

section GNSSum

/-! ### The direct-sum GNS representation over a family of np-functionals

`ϱ_Ω : A → B(⊕_i ℋ_{F i})` for an arbitrary family `F : ι → NPFunctional A`
(**48V**).  Two instances are used: `F = id`, over *all* np-functionals, which
is the `gnsHilb`/`gnsRep` of the normal Gelfand–Naimark theorem **48VIII**
below; and `F = Subtype.val` over a set `Ω` of np-functionals, which
`A/VN/NormalFunctionals.lean` needs for **90II**.2. -/

variable {ι : Type u} (F : ι → NPFunctional A)

/-- `ℋ_Ω = ⊕_i ℋ_{F i}`: the `ℓ²`-direct sum of the GNS spaces of a family of
np-functionals. -/
abbrev gnsHilbFam : Type u := lp (fun i : ι => (F i).toPositiveLinearMap.GNS) 2

private theorem rpow_two_toReal (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
  rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The pointwise (diagonal) action of `a` on `⊕_i ℋ_{F i}`. -/
private noncomputable def gnsDiagFun (a : A) (y : gnsHilbFam F) :
    ∀ i : ι, (F i).toPositiveLinearMap.GNS :=
  fun i => (F i).toPositiveLinearMap.gnsStarAlgHom a ((y : ∀ i : ι, _) i)

private theorem gnsDiag_memlp (a : A) (y : gnsHilbFam F) :
    Memℓp (gnsDiagFun F a y) 2 := by
  refine memℓp_gen ?_
  have hy : Summable (fun i : ι =>
      ‖(y : ∀ i : ι, _) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.hasSum_norm (by norm_num) y).summable
  refine Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun i => ?_) (hy.mul_left (‖a‖ ^ 2))
  rw [rpow_two_toReal, rpow_two_toReal]
  simp only [gnsDiagFun]
  have h := starAlgHom_apply_norm_le ((F i).toPositiveLinearMap.gnsStarAlgHom) a
    ((y : ∀ i : ι, _) i)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [mul_pow] at h3

/-- The diagonal action of `a` on `⊕_i ℋ_{F i}` as a linear map. -/
private noncomputable def gnsDiagLin (a : A) : gnsHilbFam F →ₗ[ℂ] gnsHilbFam F where
  toFun y := ⟨gnsDiagFun F a y, gnsDiag_memlp F a y⟩
  map_add' y z := by
    refine Subtype.ext (funext fun i => ?_)
    show gnsDiagFun F a (y + z) i = gnsDiagFun F a y i + gnsDiagFun F a z i
    simp [gnsDiagFun]
  map_smul' c y := by
    refine Subtype.ext (funext fun i => ?_)
    show gnsDiagFun F a (c • y) i = c • gnsDiagFun F a y i
    simp [gnsDiagFun]

private theorem gnsDiagLin_apply_coe (a : A) (y : gnsHilbFam F) (i : ι) :
    ((gnsDiagLin F a y : gnsHilbFam F) : ∀ i : ι, _) i
      = (F i).toPositiveLinearMap.gnsStarAlgHom a ((y : ∀ i : ι, _) i) := rfl

private theorem gnsDiagLin_norm_le (a : A) (y : gnsHilbFam F) :
    ‖gnsDiagLin F a y‖ ≤ ‖a‖ * ‖y‖ := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsum1 := lp.hasSum_norm hp (gnsDiagLin F a y)
  have hsum2 := lp.hasSum_norm hp y
  have hle : ∀ i : ι,
      ‖((gnsDiagLin F a y : gnsHilbFam F) : ∀ i : ι, _) i‖ ^ (2 : ℝ≥0∞).toReal
        ≤ ‖a‖ ^ 2 * ‖(y : ∀ i : ι, _) i‖ ^ (2 : ℝ≥0∞).toReal := by
    intro i
    rw [rpow_two_toReal, rpow_two_toReal, gnsDiagLin_apply_coe]
    have h := starAlgHom_apply_norm_le ((F i).toPositiveLinearMap.gnsStarAlgHom) a
      ((y : ∀ i : ι, _) i)
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rwa [mul_pow] at h3
  have hkey : ‖gnsDiagLin F a y‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ‖a‖ ^ 2 * ‖y‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [← hsum1.tsum_eq, ← hsum2.tsum_eq, ← tsum_mul_left]
    exact hsum1.summable.tsum_le_tsum hle (hsum2.summable.mul_left _)
  rw [rpow_two_toReal, rpow_two_toReal] at hkey
  have hsq : ‖gnsDiagLin F a y‖ ^ 2 ≤ (‖a‖ * ‖y‖) ^ 2 := by rw [mul_pow]; exact hkey
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq

/-- The diagonal action of `a` on `⊕_i ℋ_{F i}` as a bounded operator. -/
private noncomputable def gnsDiag (a : A) : gnsHilbFam F →L[ℂ] gnsHilbFam F :=
  LinearMap.mkContinuous (gnsDiagLin F a) ‖a‖ (gnsDiagLin_norm_le F a)

@[simp] private theorem gnsDiag_apply_coe (a : A) (y : gnsHilbFam F) (i : ι) :
    ((gnsDiag F a y : gnsHilbFam F) : ∀ i : ι, _) i
      = (F i).toPositiveLinearMap.gnsStarAlgHom a ((y : ∀ i : ι, _) i) := rfl

private theorem gnsHilbFam_ext {F : ι → NPFunctional A} {y z : gnsHilbFam F}
    (h : ∀ i : ι, (y : ∀ i : ι, _) i = (z : ∀ i : ι, _) i) : y = z :=
  Subtype.ext (funext h)

/-- **48V** (`varrho-Omega-normal`, vn.tex:1113): the direct-sum GNS
representation `ϱ_Ω : A → B(⊕_i ℋ_{F i})` of a family of np-functionals. -/
noncomputable def gnsRepFam : A →⋆ₐ[ℂ] (gnsHilbFam F →L[ℂ] gnsHilbFam F) where
  toFun := gnsDiag F
  map_one' := by
    refine ContinuousLinearMap.ext fun y => gnsHilbFam_ext fun i => ?_
    simp
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun y => gnsHilbFam_ext fun i => ?_
    simp
  map_zero' := by
    refine ContinuousLinearMap.ext fun y => gnsHilbFam_ext fun i => ?_
    simp
  map_add' a b := by
    refine ContinuousLinearMap.ext fun y => gnsHilbFam_ext fun i => ?_
    simp
  commutes' r := by
    refine ContinuousLinearMap.ext fun y => gnsHilbFam_ext fun i => ?_
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    show (⟪(F i).toPositiveLinearMap.gnsStarAlgHom (star a) _, _⟫) = _
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] theorem gnsRepFam_apply_coe (a : A) (y : gnsHilbFam F) (i : ι) :
    ((gnsRepFam F a y : gnsHilbFam F) : ∀ i : ι, _) i
      = (F i).toPositiveLinearMap.gnsStarAlgHom a ((y : ∀ i : ι, _) i) := rfl

/-- The canonical vector `η_ω(b) ∈ ℋ_ω`. -/
noncomputable def gnsVec (ω : NPFunctional A) (b : A) : ω.toPositiveLinearMap.GNS :=
  ((ω.toPositiveLinearMap.toPreGNS b : ω.toPositiveLinearMap.PreGNS) :
    ω.toPositiveLinearMap.GNS)

theorem gnsVec_norm_sq (ω : NPFunctional A) (b : A) :
    ((‖gnsVec ω b‖ ^ 2 : ℝ) : ℂ) = ω (star b * b) := by
  rw [gnsVec, UniformSpace.Completion.norm_coe]
  exact_mod_cast PositiveLinearMap.preGNS_norm_sq ω.toPositiveLinearMap _

theorem gnsRep_gnsVec (a b : A) (ω : NPFunctional A) :
    ω.toPositiveLinearMap.gnsStarAlgHom a (gnsVec ω b) = gnsVec ω (a * b) :=
  Theses.A.CStar.gns_starAlgHom_apply ω.toPositiveLinearMap a b

theorem gnsVec_inner (ω : NPFunctional A) (b c : A) :
    (⟪gnsVec ω b, gnsVec ω c⟫) = ω (star b * c) :=
  UniformSpace.Completion.inner_coe _ _

theorem gnsVec_denseRange (ω : NPFunctional A) : DenseRange (gnsVec ω) := by
  have h : Set.range (gnsVec ω)
      = Set.range ((↑) : ω.toPositiveLinearMap.PreGNS → ω.toPositiveLinearMap.GNS) := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩; exact ⟨ω.toPositiveLinearMap.toPreGNS b, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨ω.toPositiveLinearMap.ofPreGNS z, rfl⟩
  show Dense (Set.range (gnsVec ω))
  rw [h]
  exact UniformSpace.Completion.denseRange_coe

open scoped Classical in
/-- The "elementary" vectors `η_{F i}(b)` of `⊕_i ℋ_{F i}`, sitting in a
single summand.  They separate the operators on `⊕_i ℋ_{F i}`, and their
vector functionals pull back along `ϱ_Ω` to the np-functionals `b*ω`. -/
def gnsElemVecsFam : Set (gnsHilbFam F) :=
  {y | ∃ (i : ι) (b : A), y = lp.single 2 i (gnsVec (F i) b)}

theorem gnsElemVecsFam_separating (R : gnsHilbFam F →L[ℂ] gnsHilbFam F)
    (h : ∀ y ∈ gnsElemVecsFam F, R y = 0) : R = 0 := by
  classical
  have hsingle : ∀ (i : ι) (z : (F i).toPositiveLinearMap.GNS),
      R (lp.single 2 i z) = 0 := by
    intro i
    have hcont : Continuous
        fun z : (F i).toPositiveLinearMap.GNS => R (lp.single 2 i z) :=
      R.continuous.comp
        (lp.singleContinuousLinearMap ℂ
          (fun i : ι => (F i).toPositiveLinearMap.GNS) 2 i).continuous
    have hdense : Dense (Set.range (gnsVec (F i))) := gnsVec_denseRange (F i)
    have hfun := Continuous.ext_on hdense hcont continuous_const
      (fun x hx => by obtain ⟨b, rfl⟩ := hx; exact h _ ⟨i, b, rfl⟩)
    exact fun z => congrFun hfun z
  refine ContinuousLinearMap.ext fun y => ?_
  have hs : HasSum (fun i : ι =>
      lp.single 2 i ((y : ∀ i : ι, _) i)) y :=
    lp.hasSum_single (by norm_num) y
  have hmap := hs.mapL R
  have h0 : HasSum (fun _ : ι => (0 : gnsHilbFam F)) (R y) := by
    refine hmap.congr_fun fun i => ?_
    exact (hsingle i ((y : ∀ i : ι, _) i)).symm
  simpa using (hasSum_zero.unique h0).symm

variable [VonNeumannAlgebra A]

-- the `lp`-based Hilbert space `⊕_i ℋ_{F i}` makes the (routine) instance
-- defeq checks against `B(H)`'s C*-algebra structure expensive
set_option maxHeartbeats 2000000 in
/-- **48V** (`varrho-Omega-normal`, vn.tex:1113, Exercise): for *every*
family `Ω` of np-functionals on a von Neumann algebra, the direct-sum GNS
representation `ϱ_Ω : A → B(⊕_i ℋ_{F i})` is normal.  (Exercise, no thesis
proof; ours is **48II** `normal_faithful` against the separating family of
elementary vectors `η_{F i}(b)`, for which `⟪η(b), ϱ_Ω(a)η(b)⟫ = (b*Ω)(a)`
is an np-functional by **44VIII** `ad_normal` — the argument **48IV** gives
for a single `ω`.)  The `ℓ²(ι)`-packaged corollary is
`varrho_Omega_normal`. -/
theorem gnsRepFam_normal : PreservesDirSups ⇑(gnsRepFam F) := by
  classical
  refine starAlgHom_preservesDirSups_of_vectors (gnsRepFam F) (gnsElemVecsFam F)
    (gnsElemVecsFam_separating F) ?_
  rintro _ ⟨i, b, rfl⟩
  refine ⟨conjNP b (F i), fun a => ?_⟩
  rw [lp.inner_single_left]
  show (⟪gnsVec (F i) b,
    ((gnsRepFam F a (lp.single 2 i (gnsVec (F i) b)) : gnsHilbFam F) :
      ∀ _ : ι, _) i⟫) = _
  rw [gnsRepFam_apply_coe, lp.single_apply_self, gnsRep_gnsVec, gnsVec_inner,
    conjNP_apply, mul_assoc]

/-! ### The instance over *all* np-functionals (**48VIII**) -/

section All

variable (A)

/-- The Hilbert space `ℋ_Ω = ⊕_ω ℋ_ω` of the normal Gelfand–Naimark
construction (**48VIII**): the `ℓ²`-direct sum of the GNS spaces of *all*
np-functionals on `A`. -/
abbrev gnsHilb : Type u := gnsHilbFam (fun ω : NPFunctional A => ω)

variable {A}

/-- **48V** (`varrho-Omega-normal`, vn.tex:1113): the direct-sum GNS
representation `ϱ_Ω : A → B(⊕_ω ℋ_ω)` over *all* np-functionals of `A`. -/
noncomputable def gnsRep : A →⋆ₐ[ℂ] (gnsHilb A →L[ℂ] gnsHilb A) :=
  gnsRepFam (fun ω : NPFunctional A => ω)

@[simp] theorem gnsRep_apply_coe (a : A) (y : gnsHilb A) (ω : NPFunctional A) :
    ((gnsRep a y : gnsHilb A) : ∀ ω : NPFunctional A, _) ω
      = ω.toPositiveLinearMap.gnsStarAlgHom a ((y : ∀ ω : NPFunctional A, _) ω) := rfl

open scoped Classical in
/-- The "elementary" vectors `η_ω(b)` of `⊕_ω ℋ_ω`. -/
def gnsElemVecs : Set (gnsHilb A) :=
  gnsElemVecsFam (fun ω : NPFunctional A => ω)

theorem gnsRep_injective : Function.Injective (gnsRep (A := A)) := by
  classical
  have hker : ∀ a : A, gnsRep a = 0 → a = 0 := by
    intro a ha
    have h1 : ∀ ω : NPFunctional A, gnsVec ω a = 0 := by
      intro ω
      have h := congrArg
        (fun T : gnsHilb A →L[ℂ] gnsHilb A =>
          ((T (lp.single 2 ω (gnsVec ω 1)) : gnsHilb A) : ∀ _ : NPFunctional A, _) ω) ha
      simp only [gnsRep_apply_coe, lp.single_apply_self] at h
      rw [gnsRep_gnsVec, mul_one] at h
      simpa using h
    refine (CStarRing.star_mul_self_eq_zero_iff a).mp ?_
    refine VonNeumannAlgebra.np_faithful _ (star_mul_self_nonneg a) fun ω => ?_
    rw [← gnsVec_norm_sq ω a, h1 ω]
    simp
  intro a b hab
  have h : gnsRep (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (hker _ h)

theorem gnsRep_normal : PreservesDirSups ⇑(gnsRep (A := A)) :=
  gnsRepFam_normal _

end All

end GNSSum

section VNRange

variable [VonNeumannAlgebra A] [VonNeumannAlgebra C]

/-- **48VI**.1 in its general form, without the common-universe constraint:
the image of an injective normal ∗-homomorphism between von Neumann algebras
is a von Neumann subalgebra.  (`isVNSubalgebra_range` just below is this
statement with both algebras in `Type u`, and is what the audit records.) -/
theorem isVNSubalgebra_range_general {X : Type*} [CStarAlgebra X] [PartialOrder X]
    [StarOrderedRing X] [VonNeumannAlgebra X] {Y : Type*} [CStarAlgebra Y]
    [PartialOrder Y] [StarOrderedRing Y] [VonNeumannAlgebra Y] (φ : X →⋆ₐ[ℂ] Y)
    (hφ : Function.Injective φ) (hn : PreservesDirSups ⇑φ) :
    IsVNSubalgebra Y φ.range := by
  classical
  have hnorm : ∀ x : X, ‖φ x‖ = ‖x‖ := NonUnitalStarAlgHom.norm_map φ hφ
  have hiso : Isometry (φ : X → Y) := NonUnitalStarAlgHom.isometry φ hφ
  have hrange : ((φ.range : StarSubalgebra ℂ Y) : Set Y) = Set.range (φ : X → Y) := by
    ext x
    exact ⟨fun hx => hx, fun hx => hx⟩
  have hsaMap : ∀ x : selfAdjoint X, IsSelfAdjoint (φ (x : X)) := fun x => by
    show star (φ (x : X)) = φ (x : X)
    rw [← map_star, x.2.star_eq]
  set saMap : selfAdjoint X → selfAdjoint Y := fun x => ⟨φ (x : X), hsaMap x⟩ with hsaMapDef
  refine ⟨?_, ?_⟩
  · rw [hrange]
    exact (hiso.isUniformInducing.isComplete_range).isClosed
  intro D s hDsub hne hdir hlub
  -- every member of `D` comes from a self-adjoint element of `X`
  have hpull : ∀ d ∈ D, ∃ x : selfAdjoint X, saMap x = d := by
    intro d hd
    have hmem : (d : Y) ∈ (φ.range : Set Y) := hDsub d hd
    rw [hrange] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcsa : IsSelfAdjoint c := by
      refine hφ ?_
      rw [map_star, hc, d.2.star_eq]
    exact ⟨⟨c, hcsa⟩, Subtype.ext hc⟩
  -- pass to the cofinal tail above a fixed `d₀ ∈ D`
  obtain ⟨d₀, hd₀⟩ := hne
  set Dt : Set (selfAdjoint Y) := {d | d ∈ D ∧ d₀ ≤ d} with hDtDef
  have hDtne : Dt.Nonempty := ⟨d₀, hd₀, le_refl _⟩
  have hDtdir : DirectedOn (· ≤ ·) Dt := by
    rintro x ⟨hxD, hx0⟩ y ⟨hyD, _⟩
    obtain ⟨z, hzD, hxz, hyz⟩ := hdir x hxD y hyD
    exact ⟨z, ⟨hzD, le_trans hx0 hxz⟩, hxz, hyz⟩
  have hDtlub : IsLUB Dt s := by
    refine ⟨fun d hd => hlub.1 hd.1, fun u hu => hlub.2 fun d hd => ?_⟩
    obtain ⟨z, hzD, hdz, h0z⟩ := hdir d hd d₀ hd₀
    exact le_trans hdz (hu ⟨hzD, h0z⟩)
  -- the pullback of the tail
  set D' : Set (selfAdjoint X) := saMap ⁻¹' Dt with hD'Def
  have himg : saMap '' D' = Dt := by
    refine Set.Subset.antisymm (Set.image_preimage_subset _ _) fun d hd => ?_
    obtain ⟨x, hx⟩ := hpull d hd.1
    exact ⟨x, by rw [hD'Def]; simpa [hx] using hd, hx⟩
  have hd₀t : d₀ ∈ Dt := ⟨hd₀, le_refl _⟩
  have hD'ne : D'.Nonempty := by
    obtain ⟨x, hx⟩ := hpull d₀ hd₀
    exact ⟨x, by rw [hD'Def]; simpa [hx] using hd₀t⟩
  have hD'dir : DirectedOn (· ≤ ·) D' := by
    intro x hx y hy
    obtain ⟨d, hdD, hxd, hyd⟩ := hDtdir (saMap x) hx (saMap y) hy
    obtain ⟨z, hz⟩ := hpull d hdD.1
    refine ⟨z, by rw [hD'Def]; simpa [hz] using hdD, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp
        ((starAlgHom_le_iff_general φ hφ).mp (Subtype.coe_le_coe.mpr (hz ▸ hxd)))
    · exact Subtype.coe_le_coe.mp
        ((starAlgHom_le_iff_general φ hφ).mp (Subtype.coe_le_coe.mpr (hz ▸ hyd)))
  -- the pullback is norm bounded, hence order bounded
  set M : ℝ := ‖(s : Y) - (d₀ : Y)‖ + ‖(d₀ : Y)‖ with hMDef
  have hM0 : 0 ≤ M := by positivity
  have hD'bdd : BddAbove D' := by
    have hsa : IsSelfAdjoint (algebraMap ℂ X ((M : ℝ) : ℂ)) :=
      IsSelfAdjoint.of_nonneg (Theses.A.CStar.algebraMap_ofReal_nonneg hM0)
    refine ⟨⟨algebraMap ℂ X ((M : ℝ) : ℂ), hsa⟩, fun x hx => ?_⟩
    have hd : saMap x ∈ Dt := hx
    have h1 : (0 : Y) ≤ (saMap x : Y) - (d₀ : Y) :=
      sub_nonneg.mpr (Subtype.coe_le_coe.mpr hd.2)
    have h2 : (saMap x : Y) - (d₀ : Y) ≤ (s : Y) - (d₀ : Y) :=
      sub_le_sub_right (Subtype.coe_le_coe.mpr (hDtlub.1 hd)) _
    have h3 : ‖(saMap x : Y) - (d₀ : Y)‖ ≤ ‖(s : Y) - (d₀ : Y)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le h1 h2
    have h4 : ‖(saMap x : Y)‖ ≤ M := by
      have := norm_add_le ((saMap x : Y) - (d₀ : Y)) ((d₀ : Y))
      simp only [sub_add_cancel] at this
      exact le_trans this (by rw [hMDef]; gcongr)
    have h5 : ‖(x : X)‖ ≤ M := by rw [← hnorm]; exact h4
    refine Subtype.coe_le_coe.mp ?_
    refine le_trans ?_ (Theses.A.CStar.algebraMap_ofReal_mono h5)
    have := IsSelfAdjoint.le_algebraMap_norm_self x.2
    rwa [Theses.A.CStar.algebraMap_real_eq] at this
  -- the supremum of the pullback maps onto `s`
  set t : selfAdjoint X := dirSup D' ⟨hD'ne, hD'dir, hD'bdd⟩ with htDef
  have htlub : IsLUB D' t := isLUB_dirSup D' ⟨hD'ne, hD'dir, hD'bdd⟩
  have hkey := hn D' t hD'ne hD'dir htlub
  have hsets : (fun x : selfAdjoint X => φ (x : X)) '' D' = Subtype.val '' Dt := by
    rw [← himg, ← Set.image_comp]
    rfl
  rw [hsets] at hkey
  have hslub : IsLUB (Subtype.val '' Dt) ((s : selfAdjoint Y) : Y) :=
    isLUB_coe_of_isLUB hDtne hDtlub
  have hst : φ (t : X) = (s : Y) := hkey.unique hslub
  show (s : Y) ∈ (φ.range : Set Y)
  rw [hrange, ← hst]
  exact ⟨(t : X), rfl⟩

/-- **48VI**.1 in its general form: the image of an injective normal
∗-homomorphism between von Neumann algebras is a von Neumann subalgebra. -/
theorem isVNSubalgebra_range (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
    (hn : PreservesDirSups ⇑φ) : IsVNSubalgebra C φ.range :=
  isVNSubalgebra_range_general φ hφ hn

end VNRange




section NGNS

/-- The concrete output of the direct-sum GNS construction: every von
Neumann algebra has a faithful *normal* representation on a Hilbert space.
(Stated with the Hilbert space existentially quantified so that the transport
to `ℓ²(ι)` below never has to unfold `⊕_ω ℋ_ω`.) -/
theorem exists_faithful_normal_rep (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ⇑ρ ∧ PreservesDirSups ⇑ρ :=
  ⟨gnsHilb A, inferInstance, inferInstance, inferInstance, gnsRep,
    gnsRep_injective, gnsRep_normal⟩

/-- Refinement of `exists_faithful_normal_rep` recording the extra fact that
in the direct-sum GNS representation *every* np-functional is a vector
functional, witnessed by `ξ_ω = lp.single 2 ω (gnsVec ω 1)`.  This is what
**48V** needs. -/
theorem exists_faithful_normal_rep_vectors (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective ⇑ρ ∧ PreservesDirSups ⇑ρ ∧
        ∀ ω : NPFunctional A, ∃ ξ : H, ∀ a : A, ω a = ⟪ξ, ρ a ξ⟫ := by
  classical
  refine ⟨gnsHilb A, inferInstance, inferInstance, inferInstance, gnsRep,
    gnsRep_injective, gnsRep_normal, fun ω =>
      ⟨lp.single 2 ω (gnsVec ω 1), fun a => ?_⟩⟩
  rw [lp.inner_single_left]
  show _ = (⟪gnsVec ω 1,
    ((gnsRep a (lp.single 2 ω (gnsVec ω 1)) : gnsHilb A) :
      ∀ _ : NPFunctional A, _) ω⟫)
  rw [gnsRep_apply_coe, lp.single_apply_self, gnsRep_gnsVec, gnsVec_inner,
    star_one, one_mul, mul_one]

end NGNS

end NGNSConstruction

set_option maxHeartbeats 1000000 in
/-- **48III** (vn.tex:1091, Proposition): the GNS representation
`ρ_ω : A → B(H_ω)` of an np-functional `ω` on a von Neumann algebra is
normal.  (Rendered as: `ω` admits a *normal* cyclic representation, on
`ℓ²(ι)`, as `ngns` does it; the underlying GNS construction is Mathlib's
`PositiveLinearMap.gnsStarAlgHom`.) -/
theorem gns_normal [VonNeumannAlgebra A] (ω : NPFunctional A) :
    ∃ (ι : Type u) (ρ : MIUMap A
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
      (ξ : lp (fun _ : ι => ℂ) 2),
      (∀ a : A, ω a = ⟪ξ, ρ a ξ⟫) ∧
        Dense (Set.range fun a : A => ρ a ξ) ∧
        PreservesDirSups ⇑ρ := by
  classical
  -- the GNS representation of the single functional `ω`, with cyclic vector
  -- `η_ω(1)`
  set H : Type u := ω.toPositiveLinearMap.GNS with hH
  set ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H) := ω.toPositiveLinearMap.gnsStarAlgHom with hρ
  set ξ : H := gnsVec ω 1 with hξ
  have hdense : Dense (Set.range (gnsVec ω)) := gnsVec_denseRange ω
  have hρξ : ∀ a : A, ρ a ξ = gnsVec ω a := by
    intro a
    rw [hρ, hξ, gnsRep_gnsVec, mul_one]
  -- `ω` is the vector functional of `ξ`
  have hvec : ∀ a : A, ω a = (⟪ξ, ρ a ξ⟫ : ℂ) := by
    intro a
    rw [hρξ, hξ, gnsVec_inner, star_one, one_mul]
  -- the cyclic vector is cyclic
  have hcyc : Dense (Set.range fun a : A => ρ a ξ) := by
    have hset : (Set.range fun a : A => ρ a ξ) = Set.range (gnsVec ω) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, (hρξ a).symm⟩
      · rintro ⟨a, rfl⟩; exact ⟨a, hρξ a⟩
    rw [hset]; exact hdense
  -- normality of `ρ`, by **48II** applied to the (separating) elementary
  -- vectors `η_ω(b)`
  have hnormal : PreservesDirSups ⇑ρ := by
    refine starAlgHom_preservesDirSups_of_vectors ρ (Set.range (gnsVec ω)) ?_ ?_
    · intro R hR
      refine ContinuousLinearMap.ext ?_
      exact fun y => congrFun (Continuous.ext_on hdense R.continuous continuous_const
        (fun x hx => hR x hx)) y
    · rintro _ ⟨b, rfl⟩
      refine ⟨conjNP b ω, fun a => ?_⟩
      rw [hρ, gnsRep_gnsVec, gnsVec_inner, conjNP_apply, mul_assoc]
  -- transport to `ℓ²(w)` along a Hilbert basis, as in `ngns`
  obtain ⟨w, bas, -⟩ := exists_hilbertBasis ℂ H
  set Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (lp (fun _ : w => ℂ) 2 →L[ℂ] lp (fun _ : w => ℂ) 2) :=
    bas.repr.conjStarAlgEquiv with hΦ
  set g : A →⋆ₐ[ℂ] (lp (fun _ : w => ℂ) 2 →L[ℂ] lp (fun _ : w => ℂ) 2) :=
    Φ.toStarAlgHom.comp ρ with hg
  have hΦP : PreservesDirSups ⇑(starAlgHomP Φ.toStarAlgHom) :=
    starAlgEquiv_preservesDirSups Φ
  have hgn : PreservesDirSups ⇑g :=
    preservesDirSups_pmap_comp (starAlgHomP ρ) hnormal
      (starAlgHomP Φ.toStarAlgHom) hΦP
  have happ : ∀ a : A, g a (bas.repr ξ) = bas.repr (ρ a ξ) := by
    intro a; rw [hg, hΦ]; simp
  refine ⟨w, g, bas.repr ξ, fun a => ?_, ?_, hgn⟩
  · rw [happ, LinearIsometryEquiv.inner_map_map, hvec]
  · have heq : (fun a : A => g a (bas.repr ξ))
        = (bas.repr : H → lp (fun _ : w => ℂ) 2) ∘ fun a : A => ρ a ξ := by
      funext a; exact happ a
    rw [heq]
    exact DenseRange.comp bas.repr.surjective.denseRange hcyc
      bas.repr.continuous

-- as for `gnsRep_normal`, the `lp`-based `⊕_ω ℋ_ω` makes the instance defeq
-- checks against `B(H)`'s C*-algebra structure expensive
set_option maxHeartbeats 2000000 in
/-- Corollary of **48V**, packaged as **48III** packages **48IV**: for any
collection `Ω` of np-functionals on a von Neumann algebra there is a *normal*
representation on some `ℓ²(ι)` in which every `ω ∈ Ω` is a vector functional.

This is **weaker** than 48V, which is `gnsRepFam_normal` above: nothing here
pins the representation down to `ϱ_Ω`, and the witness taken by the proof is
the representation over *all* np-functionals, which serves any `Ω` a
fortiori.  Recorded for the `ℓ²(ι)` packaging alone. -/
theorem varrho_Omega_normal [VonNeumannAlgebra A]
    (Ω : Set (NPFunctional A)) :
    ∃ (ι : Type u) (ρ : MIUMap A
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)),
      PreservesDirSups ⇑ρ ∧
        ∀ ω ∈ Ω, ∃ ξ : lp (fun _ : ι => ℂ) 2,
          ∀ a : A, ω a = ⟪ξ, ρ a ξ⟫ := by
  classical
  -- The direct-sum GNS representation `ρ_Ω` is already available for the
  -- *full* set of np-functionals, and it is normal, with every `ω` a vector
  -- functional; a fortiori it serves any `Ω`.  Transport it to `ℓ²(w)` along
  -- a Hilbert basis `w`, exactly as in `ngns`.
  obtain ⟨H, _, _, _, ρ, -, hn, hvec⟩ := exists_faithful_normal_rep_vectors A
  obtain ⟨w, bas, -⟩ := exists_hilbertBasis ℂ H
  set Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (lp (fun _ : w => ℂ) 2 →L[ℂ] lp (fun _ : w => ℂ) 2) :=
    bas.repr.conjStarAlgEquiv with hΦ
  set g : A →⋆ₐ[ℂ] (lp (fun _ : w => ℂ) 2 →L[ℂ] lp (fun _ : w => ℂ) 2) :=
    Φ.toStarAlgHom.comp ρ with hg
  have hρP : PreservesDirSups ⇑(starAlgHomP ρ) := hn
  have hΦP : PreservesDirSups ⇑(starAlgHomP Φ.toStarAlgHom) :=
    starAlgEquiv_preservesDirSups Φ
  have hgn : PreservesDirSups ⇑g :=
    preservesDirSups_pmap_comp (starAlgHomP ρ) hρP
      (starAlgHomP Φ.toStarAlgHom) hΦP
  refine ⟨w, g, hgn, fun ω _ => ?_⟩
  obtain ⟨ξ, hξ⟩ := hvec ω
  refine ⟨bas.repr ξ, fun a => ?_⟩
  have happ : g a (bas.repr ξ) = bas.repr (ρ a ξ) := by
    rw [hg, hΦ]; simp
  rw [happ, LinearIsometryEquiv.inner_map_map, hξ]

/-- **48VI** (`injective-nmiu-iso-on-image`, vn.tex:1120, Lemma), part 1:
the image of an injective nmiu-map `f : A → B` between von Neumann algebras
is a von Neumann subalgebra of `B`. -/
theorem injective_nmiu_iso_on_image_1 [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NMIUMap A B) (hf : Function.Injective f) :
    IsVNSubalgebra B f.toStarAlgHom.range :=
  isVNSubalgebra_range f.toStarAlgHom hf f.preservesDirSups'

/-- **48VI** (`injective-nmiu-iso-on-image`, vn.tex:1120, Lemma), part 2, the
order-embedding half: an injective nmiu-map `f` reflects the order,
`f a ≤ f b ↔ a ≤ b`.  (The full statement — that `f` restricts to an
nmiu-*isomorphism* onto its image — is `injective_nmiu_iso_on_image_2'`
below, which this is the working form of.) -/
theorem injective_nmiu_iso_on_image_2 [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NMIUMap A B) (hf : Function.Injective f)
    (a b : A) : f a ≤ f b ↔ a ≤ b :=
  starAlgHom_le_iff f.toStarAlgHom hf

/-- **48VI** (`injective-nmiu-iso-on-image`, vn.tex:1120, Lemma), part 2: an
injective nmiu-map `f : A → B` between von Neumann algebras restricts to an
nmiu-*isomorphism* onto its image — a ∗-isomorphism `e : A ≅ f(A)` with
`e a = f a`, normal in both directions.  (Together with part 1, `f(A)` is a
von Neumann subalgebra of `B`, so `f(A)` really is a von Neumann algebra and
`e` an isomorphism of such; the *type* `↥f.range` carries the induced order
here, and its von Neumann structure is built in `A/VN/Division`.)

Proof: `StarAlgEquiv.ofInjective` gives the ∗-isomorphism; normality of `e`
is that of `f`, since suprema in `↥f.range` are computed in `B`, and
normality of `e⁻¹` is the order reflection of part 2's working form (an
upper bound `t` of a nonempty set of self-adjoint elements is itself
self-adjoint, so `f t` may be compared inside the image). -/
theorem injective_nmiu_iso_on_image_2' [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NMIUMap A B) (hf : Function.Injective f) :
    ∃ e : A ≃⋆ₐ[ℂ] f.toStarAlgHom.range,
      (∀ a : A, ((e a : B) = f a)) ∧ PreservesDirSups ⇑e ∧
        PreservesDirSups ⇑e.symm := by
  classical
  have hle : ∀ a b : A, f a ≤ f b ↔ a ≤ b := injective_nmiu_iso_on_image_2 f hf
  set e : A ≃⋆ₐ[ℂ] f.toStarAlgHom.range :=
    StarAlgEquiv.ofInjective f.toStarAlgHom hf with he
  have hcoe : ∀ a : A, ((e a : B) = f a) := fun a => rfl
  have hsymm : ∀ x : f.toStarAlgHom.range, f (e.symm x) = (x : B) := by
    intro x
    rw [← hcoe (e.symm x), e.apply_symm_apply]
  refine ⟨e, hcoe, ?_, ?_⟩
  · -- `e` is normal: suprema in the image are the suprema of `B`
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      refine Subtype.coe_le_coe.mp ?_
      rw [hcoe, hcoe]
      exact (hle _ _).mpr (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · intro u hu
      refine Subtype.coe_le_coe.mp ?_
      rw [hcoe]
      refine (f.preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have h := hu ⟨d, hd, rfl⟩
      have h' : ((e (d : A) : B)) ≤ (u : B) := Subtype.coe_le_coe.mpr h
      rwa [hcoe] at h'
  · -- `e⁻¹` is normal, by order reflection
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      refine (hle _ _).mp ?_
      rw [hsymm, hsymm]
      exact Subtype.coe_le_coe.mpr (Subtype.coe_le_coe.mpr (hlub.1 hd))
    · intro t ht
      obtain ⟨d₀, hd₀⟩ := hne
      have hsa₀ : IsSelfAdjoint (e.symm ((d₀ : f.toStarAlgHom.range))) := by
        have hd₀sa : star ((d₀ : f.toStarAlgHom.range))
            = (d₀ : f.toStarAlgHom.range) := d₀.2
        show star (e.symm _) = _
        rw [← map_star, hd₀sa]
      have htsa : IsSelfAdjoint t := by
        have hd : IsSelfAdjoint (t - e.symm ((d₀ : f.toStarAlgHom.range))) :=
          IsSelfAdjoint.of_nonneg (sub_nonneg.mpr (ht ⟨d₀, hd₀, rfl⟩))
        simpa using hd.add hsa₀
      have hetsa : IsSelfAdjoint (e t) := by
        show star (e t) = _
        rw [← map_star, htsa.star_eq]
      have hub : s ≤ (⟨e t, hetsa⟩ : selfAdjoint f.toStarAlgHom.range) := by
        refine hlub.2 fun d hd => ?_
        refine Subtype.coe_le_coe.mp ?_
        refine Subtype.coe_le_coe.mp ?_
        rw [hcoe, ← hsymm (d : f.toStarAlgHom.range)]
        exact (hle _ _).mpr (ht ⟨d, hd, rfl⟩)
      refine (hle _ _).mp ?_
      rw [hsymm]
      have h := Subtype.coe_le_coe.mpr (Subtype.coe_le_coe.mpr hub)
      rwa [hcoe] at h

/-- **47V** (`vn-equalisers`, vn.tex:1006, Exercise), second half, in
`W*_miu`: the inclusion of `E = {a | f a = g a}` *is* the equaliser of `f`
and `g`.

`A/VN/Basic` has no von Neumann structure on a subalgebra *as a type* — that
is `VNSub`, built in `A/VN/Division` — so the inclusion is taken as a
parameter: for any von Neumann algebra `E` and injective nmiu-map
`ι : E → A` whose range is the equaliser set (`VNSub` with its inclusion is
one, by `vn_equalisers`), every nmiu-map `h : C → A` with `f ∘ h = g ∘ h`
factors through `ι` by a unique nmiu-map.

The mediating map is `ι⁻¹ ∘ h`, and every clause of it — multiplicativity,
unitality, ∗-preservation, normality — is read off from the corresponding
clause for `h` by injectivity of `ι` and its order reflection (**48VI**.2
`injective_nmiu_iso_on_image_2`, which is why this sits here rather than
beside `vn_equalisers`). -/
theorem vn_equalisers_miu [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {E C : Type u} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    [VonNeumannAlgebra E] [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [VonNeumannAlgebra C] (f g : NMIUMap A B) (ι : NMIUMap E A)
    (hι : Function.Injective ι)
    (hrange : Set.range (ι : E → A) = {a : A | f a = g a})
    (h : NMIUMap C A) (hfg : ∀ c : C, f (h c) = g (h c)) :
    ∃! m : NMIUMap C E, ∀ c : C, ι (m c) = h c := by
  classical
  have hle : ∀ x y : E, ι x ≤ ι y ↔ x ≤ y :=
    fun x y => injective_nmiu_iso_on_image_2 ι hι x y
  have hmem : ∀ c : C, ∃ x : E, ι x = h c := by
    intro c
    have hc : h c ∈ Set.range (ι : E → A) := by rw [hrange]; exact hfg c
    exact hc
  choose m hm using hmem
  -- the structural laws, each by injectivity of `ι`
  have hι1 : ι (1 : E) = 1 := map_one ι.toStarAlgHom
  have hι0 : ι (0 : E) = 0 := map_zero ι.toStarAlgHom
  have hιmul : ∀ x y : E, ι (x * y) = ι x * ι y := fun x y => map_mul ι.toStarAlgHom x y
  have hιadd : ∀ x y : E, ι (x + y) = ι x + ι y := fun x y => map_add ι.toStarAlgHom x y
  have hιstar : ∀ x : E, ι (star x) = star (ι x) := fun x => map_star ι.toStarAlgHom x
  have hιalg : ∀ r : ℂ, ι (algebraMap ℂ E r) = algebraMap ℂ A r :=
    fun r => ι.toStarAlgHom.commutes r
  have hh1 : h (1 : C) = 1 := map_one h.toStarAlgHom
  have hh0 : h (0 : C) = 0 := map_zero h.toStarAlgHom
  have hhmul : ∀ x y : C, h (x * y) = h x * h y := fun x y => map_mul h.toStarAlgHom x y
  have hhadd : ∀ x y : C, h (x + y) = h x + h y := fun x y => map_add h.toStarAlgHom x y
  have hhstar : ∀ x : C, h (star x) = star (h x) := fun x => map_star h.toStarAlgHom x
  have hhalg : ∀ r : ℂ, h (algebraMap ℂ C r) = algebraMap ℂ A r :=
    fun r => h.toStarAlgHom.commutes r
  have hone : m 1 = 1 := hι (by rw [hm, hι1, hh1])
  have hzero : m 0 = 0 := hι (by rw [hm, hι0, hh0])
  have hmul : ∀ x y : C, m (x * y) = m x * m y := by
    intro x y
    refine hι ?_
    rw [hm, hιmul, hm, hm, hhmul]
  have hadd : ∀ x y : C, m (x + y) = m x + m y := by
    intro x y
    refine hι ?_
    rw [hm, hιadd, hm, hm, hhadd]
  have hcomm : ∀ r : ℂ, m (algebraMap ℂ C r) = algebraMap ℂ E r := by
    intro r
    refine hι ?_
    rw [hm, hιalg, hhalg]
  have hstar : ∀ x : C, m (star x) = star (m x) := by
    intro x
    refine hι ?_
    rw [hm, hιstar, hm, hhstar]
  have hnormal : PreservesDirSups m := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      refine (hle _ _).mp ?_
      rw [hm, hm]
      exact (h.preservesDirSups' D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro t ht
      refine (hle _ _).mp ?_
      rw [hm]
      refine (h.preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      show h ((d : selfAdjoint C) : C) ≤ ι t
      rw [← hm]
      exact (hle _ _).mpr (ht ⟨d, hd, rfl⟩)
  refine ⟨⟨{ toFun := m
             map_one' := hone
             map_mul' := hmul
             map_zero' := hzero
             map_add' := hadd
             commutes' := hcomm
             map_star' := hstar }, hnormal⟩, hm, ?_⟩
  intro m' hm'
  apply DFunLike.coe_injective
  funext c
  exact hι ((hm' c).trans (hm c).symm)

/-- **47V** (`vn-equalisers`, vn.tex:1006, Exercise), second half, in
`W*_cpsu`: the same inclusion is the equaliser of `f` and `g` for *ncpsu*
maps.  Presented exactly as `vn_equalisers_miu`, and proved the same way;
complete positivity of the mediating map `ι⁻¹ ∘ h` is that of `h` pushed
back along `ι`, since `ι(∑ᵢⱼ bᵢ* (ι⁻¹h)(aᵢ*aⱼ) bⱼ) = ∑ᵢⱼ ι(bᵢ)* h(aᵢ*aⱼ)
ι(bⱼ) ≥ 0` and `ι` reflects the order. -/
theorem vn_equalisers_cpsu [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {E C : Type u} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    [VonNeumannAlgebra E] [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [VonNeumannAlgebra C] (f g : NMIUMap A B) (ι : NMIUMap E A)
    (hι : Function.Injective ι)
    (hrange : Set.range (ι : E → A) = {a : A | f a = g a})
    (h : NCPSUMap C A) (hfg : ∀ c : C, f (h.toNCPMap c) = g (h.toNCPMap c)) :
    ∃! m : NCPSUMap C E, ∀ c : C, ι (m.toNCPMap c) = h.toNCPMap c := by
  classical
  have hle : ∀ x y : E, ι x ≤ ι y ↔ x ≤ y :=
    fun x y => injective_nmiu_iso_on_image_2 ι hι x y
  have hmem : ∀ c : C, ∃ x : E, ι x = h.toNCPMap c := by
    intro c
    have hc : h.toNCPMap c ∈ Set.range (ι : E → A) := by rw [hrange]; exact hfg c
    exact hc
  choose m hm using hmem
  have hι0 : ι (0 : E) = 0 := map_zero ι.toStarAlgHom
  have hι1 : ι (1 : E) = 1 := map_one ι.toStarAlgHom
  have hιmul : ∀ x y : E, ι (x * y) = ι x * ι y := fun x y => map_mul ι.toStarAlgHom x y
  have hιadd : ∀ x y : E, ι (x + y) = ι x + ι y := fun x y => map_add ι.toStarAlgHom x y
  have hιsmul : ∀ (r : ℂ) (x : E), ι (r • x) = r • ι x :=
    fun r x => map_smul ι.toStarAlgHom r x
  have hιstar : ∀ x : E, ι (star x) = star (ι x) := fun x => map_star ι.toStarAlgHom x
  have hιsum : ∀ {n : ℕ} (F : Fin n → E), ι (∑ i, F i) = ∑ i, ι (F i) :=
    fun F => map_sum ι.toStarAlgHom F Finset.univ
  -- `m` is linear
  have hadd : ∀ x y : C, m (x + y) = m x + m y := by
    intro x y
    refine hι ?_
    rw [hm, hιadd, hm, hm]
    exact map_add h.toNCPMap.toCompletelyPositiveMap.toLinearMap x y
  have hsmul : ∀ (r : ℂ) (x : C), m (r • x) = r • m x := by
    intro r x
    refine hι ?_
    rw [hm, hιsmul, hm]
    exact map_smul h.toNCPMap.toCompletelyPositiveMap.toLinearMap r x
  set mL : C →ₗ[ℂ] E :=
    { toFun := m
      map_add' := hadd
      map_smul' := hsmul } with hmL
  have hmLapp : ∀ c : C, mL c = m c := fun _ => rfl
  -- complete positivity, pushed forward along `ι`
  have hhcp : IsCompletelyPositiveMap h.toNCPMap.toCompletelyPositiveMap.toLinearMap :=
    (cp_iff _).out 1 0 |>.mp fun N M hM =>
      h.toNCPMap.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hcp : IsCompletelyPositiveMap mL := by
    intro n α b
    refine (hle 0 _).mp ?_
    rw [hι0, hιsum]
    have hterm : ∀ i : Fin n,
        ι (∑ j, star (b i) * mL (star (α i) * α j) * b j)
          = ∑ j, star (ι (b i)) *
              h.toNCPMap.toCompletelyPositiveMap.toLinearMap (star (α i) * α j) * ι (b j) := by
      intro i
      rw [hιsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hιmul, hιmul, hιstar, hmLapp, hm]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact hhcp n α fun i => ι (b i)
  have hsu : Subunital m := by
    refine (hle _ _).mp ?_
    rw [hm, hι1]
    exact h.subunital'
  have hnormal : PreservesDirSups m := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      refine (hle _ _).mp ?_
      rw [hm, hm]
      exact (h.toNCPMap.preservesDirSups' D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro t ht
      refine (hle _ _).mp ?_
      rw [hm]
      refine (h.toNCPMap.preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      show h.toNCPMap ((d : selfAdjoint C) : C) ≤ ι t
      rw [← hm]
      exact (hle _ _).mpr (ht ⟨d, hd, rfl⟩)
  refine ⟨{ toNCPMap :=
              { toCompletelyPositiveMap :=
                  { toLinearMap := mL
                    map_cstarMatrix_nonneg' := (cp_iff mL).out 0 1 |>.mp hcp }
                preservesDirSups' := hnormal }
            subunital' := hsu }, hm, ?_⟩
  rintro ⟨⟨m', hnc⟩, hsu'⟩ hm'
  congr 1
  apply DFunLike.coe_injective
  funext c
  exact hι ((hm' c).trans (hm c).symm)

/-- **48VIII** (`ngns`, vn.tex:1144, Theorem (normal Gelfand–Naimark)):
every von Neumann algebra is nmiu-isomorphic to a von Neumann algebra of
operators on a Hilbert space: there is an injective nmiu-map into some
`B(ℓ²(ι))` whose range is a von Neumann subalgebra. -/
theorem ngns (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] :
    ∃ (ι : Type u) (f : NMIUMap A
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)),
      Function.Injective f ∧ IsVNSubalgebra _ f.toStarAlgHom.range := by
  obtain ⟨H, _, _, _, ρ, hinj, hn⟩ := exists_faithful_normal_rep A
  obtain ⟨w, bas, -⟩ := exists_hilbertBasis ℂ H
  set Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (lp (fun _ : w => ℂ) 2 →L[ℂ] lp (fun _ : w => ℂ) 2) :=
    bas.repr.conjStarAlgEquiv with hΦ
  set g : A →⋆ₐ[ℂ] (lp (fun _ : w => ℂ) 2 →L[ℂ] lp (fun _ : w => ℂ) 2) :=
    Φ.toStarAlgHom.comp ρ with hg
  have hρP : PreservesDirSups ⇑(starAlgHomP ρ) := hn
  have hΦP : PreservesDirSups ⇑(starAlgHomP Φ.toStarAlgHom) :=
    starAlgEquiv_preservesDirSups Φ
  have hginj : Function.Injective ⇑g := fun x y hxy => hinj (Φ.injective hxy)
  have hgn : PreservesDirSups ⇑g :=
    preservesDirSups_pmap_comp (starAlgHomP ρ) hρP (starAlgHomP Φ.toStarAlgHom) hΦP
  exact ⟨w, ⟨g, hgn⟩, hginj, isVNSubalgebra_range g hginj hgn⟩


/-! ## Parsec 490: matrices over a von Neumann algebra

**49II** (`bah-vn`, vn.tex:1177, Theorem): for a von Neumann algebra `𝒜`,
the C*-algebra `B^a(X)` of bounded adjointable module maps on a self-dual
Hilbert `𝒜`-module `X` is a von Neumann algebra, and `⟨x,(·)x⟩` is normal
for every `x ∈ X`.

**Proved, in `Theses/A/VN/BaX.lean`** (2026-08-27) — but not under that
name, and the reason is worth keeping.  cstar **32XIII** `bax_cstar` is
proved in `Theses/A/CStar/Matrices.lean`, and the `Bax` section there
carries the whole `CStarAlgebra` structure (involution the adjoint,
C*-identity from **32XII**, completeness from `bax_cstar`) together with its
spectral order, on `Bax 𝒜 X`.  `Bax` was `private` to that file until
2026-08-27, so `VonNeumannAlgebra (Bax 𝒜 X)` could not be *written* outside
it at all — which is why `A/VN/BaX` first stated both clauses of **42I**
through the vector-functional order, which by **32XV**
`chilb_vector_states_2` *is* the order of `B^a(X)`: `bah_vn_sup` and
`bah_vn_np_faithful`.

`Bax` and the eight instances its elaboration needs are now exported, and
49II is stated as the thesis states it, `bah_vn : VonNeumannAlgebra
(Bax 𝒜 X)`, with its second clause `vecFunctional_normal` as a statement of
its own.  It is the same shape as the tree's B-side twin
`ba_vonNeumannAlgebra` (**152X**), so the theorem both theses prove now has
one rendering.

The other half of the thesis's route to `M_N(𝒜)` is `matrixBaxEquiv` — but
**not** as printed: the thesis's `𝒜^N` is a *right* module, Mathlib's
`C⋆ᵐᵒᵈ(𝒜, Fin N → 𝒜)` is a *left* one, and its adjointables are the right
multiplications, which compose backwards (`cstar_matrices_3` already says
so).  So what holds is `M_N(𝒜)ᵐᵒᵖ ≅ B^a(𝒜^N)`.  This is the same left/right
gap `docs/DECISIONS.md` §3.3 records for 34V.3, and nothing is lost by it:
`ᵐᵒᵖ` preserves star, positivity, order and suprema.  49IV neither needs nor
*could cite* any of it — this file is upstream of `A/VN/BaX` — and is proved
directly below; see the note there. -/

/-! ### Auxiliary machinery for **49IV**: the `𝒜`-valued quadratic form of a
matrix

The thesis prints no proof of 49IV at all: vn.tex 490.40 `mn-vna` is an
Exercise, and `asols.tex` has no solution for it — that file's solutions stop
at parsec 340.  What it does print is 490.10's announcement that 49II
(`bah-vn`) is proved "to this end", i.e. that `M_N(𝒜)` is to be realised as
`B^a(𝒜^N)`.  Both halves of that realisation now exist — `bah_vn` and
`matrixBaxEquiv`, the latter with `M_N(𝒜)ᵐᵒᵖ` for the reason given in the
note above — but **neither may be cited here**.  `bah_vn` lives in
`Theses/A/VN/BaX.lean`, which imports `A.VN.Completeness`, which imports
`A.VN.Projections`, which imports this file: 49II is proved three modules
*downstream* of the module 49IV is stated in, so naming it here is an import
cycle.  Nor can 49IV move down to meet it, `CStarMatrix` being used in
`Projections`, in `Completeness` (the Kaplansky `M₂` argument) and in
`Division`, all upstream of `BaX`, where instance search wants `mn_vna_1`.
So the supremum is constructed here directly, out of the same
ingredient that makes 49II work: the `𝒜`-valued
sesquilinear form `⟨x, M y⟩ = ∑ᵢⱼ xᵢ* Mᵢⱼ yⱼ` of the Hilbert `𝒜`-module
`𝒜^N`.  Its two properties are **33II** (`cstar_matrix_positive_iff`: the
form detects positivity) and **44VIII**+**44XIV** (each `M ↦ ⟨x, M x⟩`
carries a bounded directed set to one whose supremum is an ultrastrong
limit).  Polarisation recovers the entries of the supremum from the
suprema of the forms, and the entries then reassemble into a matrix which
the ultrastrong limits identify as the least upper bound. -/

section MatrixForm

variable {N : ℕ}

omit [PartialOrder A] [StarOrderedRing A]

/-- The `𝒜`-valued sesquilinear form `⟨x, M y⟩ = ∑ᵢⱼ xᵢ* Mᵢⱼ yⱼ` of the
Hilbert `𝒜`-module `𝒜^N`, paired with a matrix `M ∈ M_N(𝒜)`. -/
def matForm (x y : Fin N → A) (M : CStarMatrix (Fin N) (Fin N) A) : A :=
  ∑ i, ∑ j, star (x i) * M i j * y j

theorem matForm_add_right (x y z : Fin N → A) (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm x (y + z) M = matForm x y M + matForm x z M := by
  simp only [matForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem matForm_add_left (x y z : Fin N → A) (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm (x + y) z M = matForm x z M + matForm y z M := by
  simp only [matForm, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem matForm_smul_right (c : ℂ) (x y : Fin N → A)
    (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm x (c • y) M = c • matForm x y M := by
  simp only [matForm, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]

theorem matForm_smul_left (c : ℂ) (x y : Fin N → A)
    (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm (c • x) y M = (starRingEnd ℂ) c • matForm x y M := by
  simp only [matForm, Pi.smul_apply, star_smul, smul_mul_assoc, Finset.smul_sum]
  rfl

theorem matForm_add_matrix (x y : Fin N → A) (M M' : CStarMatrix (Fin N) (Fin N) A) :
    matForm x y (M + M') = matForm x y M + matForm x y M' := by
  simp only [matForm, CStarMatrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem matForm_smul_matrix (c : ℂ) (x y : Fin N → A)
    (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm x y (c • M) = c • matForm x y M := by
  simp only [matForm, CStarMatrix.smul_apply, mul_smul_comm, smul_mul_assoc,
    Finset.smul_sum]

@[simp] theorem matForm_zero_matrix (x y : Fin N → A) :
    matForm x y (0 : CStarMatrix (Fin N) (Fin N) A) = 0 := by
  simp [matForm]

theorem matForm_sub_matrix (x y : Fin N → A) (M M' : CStarMatrix (Fin N) (Fin N) A) :
    matForm x y (M - M') = matForm x y M - matForm x y M' := by
  simp only [matForm, CStarMatrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem matForm_star_matrix (x y : Fin N → A) (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm x y (star M) = star (matForm y x M) := by
  simp only [matForm, CStarMatrix.star_apply, star_sum, star_mul, star_star, mul_assoc]
  exact Finset.sum_comm

/-- The `i`-th standard basis vector of the Hilbert `𝒜`-module `𝒜^N`. -/
def matUnit (i : Fin N) : Fin N → A := fun p => if p = i then 1 else 0

theorem matForm_matUnit (i j : Fin N) (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm (matUnit i) (matUnit j) M = M i j := by
  simp [matForm, matUnit, apply_ite star, ite_mul, mul_ite]

/-- The vector `eᵢ + c eⱼ ∈ 𝒜^N` used for polarisation. -/
def matPolVec (i j : Fin N) (c : ℂ) : Fin N → A := matUnit i + c • matUnit j

theorem matForm_matPolVec (i j : Fin N) (c : ℂ) (M : CStarMatrix (Fin N) (Fin N) A) :
    matForm (matPolVec i j c) (matPolVec i j c) M
      = M i i + c • M i j + (starRingEnd ℂ) c • M j i
        + ((starRingEnd ℂ) c * c) • M j j := by
  simp only [matPolVec, matForm_add_left, matForm_add_right, matForm_smul_left,
    matForm_smul_right, matForm_matUnit, smul_add, smul_smul]
  module

/-- Polarisation (**44II** for the `𝒜`-valued form): every entry of a matrix
is recovered from the values of the quadratic form `x ↦ ⟨x, M x⟩`. -/
theorem matForm_polarization (i j : Fin N) (M : CStarMatrix (Fin N) (Fin N) A) :
    M i j = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4, Complex.I ^ k •
      matForm (matPolVec j i (Complex.I ^ k)) (matPolVec j i (Complex.I ^ k)) M := by
  simp only [matForm_matPolVec, Finset.sum_range_succ, Finset.sum_range_zero,
    smul_add, smul_smul, zero_add]
  match_scalars <;> norm_num [pow_succ, Complex.I_mul_I]

/-- The `𝒜`-valued quadratic form determines the matrix. -/
theorem matrix_ext_of_matForm {M M' : CStarMatrix (Fin N) (Fin N) A}
    (h : ∀ x : Fin N → A, matForm x x M = matForm x x M') : M = M' := by
  ext i j
  rw [matForm_polarization i j M, matForm_polarization i j M']
  exact congrArg _ (Finset.sum_congr rfl fun k _ => congrArg _ (h _))

theorem isSelfAdjoint_matForm {M : CStarMatrix (Fin N) (Fin N) A}
    (hM : IsSelfAdjoint M) (x : Fin N → A) : IsSelfAdjoint (matForm x x M) := by
  have h := matForm_star_matrix x x M
  rw [hM.star_eq] at h
  exact h.symm

end MatrixForm

section MatrixFormOrder

variable {N : ℕ}

/-- **33II** (`cstar_matrix_positive_iff`) restated: `0 ≤ M` iff its
`𝒜`-valued quadratic form is positive. -/
theorem nonneg_iff_matForm {M : CStarMatrix (Fin N) (Fin N) A} :
    0 ≤ M ↔ ∀ x : Fin N → A, 0 ≤ matForm x x M :=
  cstar_matrix_positive_iff M

theorem matForm_mono {M M' : CStarMatrix (Fin N) (Fin N) A} (h : M ≤ M')
    (x : Fin N → A) : matForm x x M ≤ matForm x x M' := by
  rw [← sub_nonneg, ← matForm_sub_matrix]
  exact nonneg_iff_matForm.mp (sub_nonneg.mpr h) x

theorem le_iff_matForm {M M' : CStarMatrix (Fin N) (Fin N) A} :
    M ≤ M' ↔ ∀ x : Fin N → A, matForm x x M ≤ matForm x x M' := by
  refine ⟨fun h x => matForm_mono h x, fun h => ?_⟩
  rw [← sub_nonneg, nonneg_iff_matForm]
  exact fun x => by rw [matForm_sub_matrix]; exact sub_nonneg.mpr (h x)

end MatrixFormOrder

/-! ### Auxiliary machinery: ultrastrong limits are linear

`USTendsto` is closed under scalar multiples, finite sums and multiplication
by fixed elements on either side (the last by **45IV**, in the `‖·‖_ω`-form
in which it was proved).  These are stated here because 49IV needs them
entrywise; cf. the private copies in `Theses/B/Dils/SelfDualCompletion.lean`. -/

section USLinear

theorem usTendsto_smul {ι : Type*} {l : Filter ι} {f : ι → A} {a : A} (c : ℂ)
    (h : USTendsto f l a) : USTendsto (fun i => c • f i) l (c • a) := by
  rw [usTendsto_iff] at h ⊢
  intro ω
  have he : ∀ i, omegaNorm A ω (c • f i - c • a) = ‖c‖ * omegaNorm A ω (f i - a) := by
    intro i; rw [← smul_sub, omegaNorm_smul]
  simp only [he]
  simpa using (h ω).const_mul ‖c‖

theorem usTendsto_add {ι : Type*} {l : Filter ι} {f g : ι → A} {a b : A}
    (hf : USTendsto f l a) (hg : USTendsto g l b) :
    USTendsto (fun i => f i + g i) l (a + b) := by
  rw [usTendsto_iff] at hf hg ⊢
  intro ω
  refine squeeze_zero (fun i => omegaNorm_nonneg _ _) (fun i => ?_)
    (by simpa using (hf ω).add (hg ω))
  have he : f i + g i - (a + b) = (f i - a) + (g i - b) := by abel
  rw [he]
  exact omegaNorm_add_le ω _ _

theorem usTendsto_const {ι : Type*} {l : Filter ι} (a : A) :
    USTendsto (fun _ : ι => a) l a := by
  rw [usTendsto_iff]; intro ω; simpa using tendsto_const_nhds

theorem usTendsto_finsetSum {ι κ : Type*} {l : Filter ι} {s : Finset κ}
    {f : κ → ι → A} {a : κ → A} (h : ∀ k ∈ s, USTendsto (f k) l (a k)) :
    USTendsto (fun i => ∑ k ∈ s, f k i) l (∑ k ∈ s, a k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using usTendsto_const (ι := ι) (l := l) (0 : A)
  | insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      exact usTendsto_add (h k (Finset.mem_insert_self k s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [StarOrderedRing A] in
theorem uwTendsto_finsetSum {ι κ : Type*} {l : Filter ι} {s : Finset κ}
    {f : κ → ι → A} {a : κ → A} (h : ∀ k ∈ s, UWTendsto (f k) l (a k)) :
    UWTendsto (fun i => ∑ k ∈ s, f k i) l (∑ k ∈ s, a k) := by
  rw [uwTendsto_iff]
  intro ω
  simp only [npFunctional_finsetSum]
  exact tendsto_finset_sum _ fun k hk => (uwTendsto_iff _ _ _).mp (h k hk) ω

theorem usTendsto_mul_left_right [VonNeumannAlgebra A] {ι : Type*} {l : Filter ι}
    {f : ι → A} {a : A} (u v : A) (h : USTendsto f l a) :
    USTendsto (fun i => u * f i * v) l (u * a * v) := by
  rw [usTendsto_iff] at h ⊢
  intro ω
  refine squeeze_zero (fun i => omegaNorm_nonneg _ _) (fun i => ?_)
    (by simpa using (h (conjNP v ω)).const_mul ‖u‖)
  have he : u * f i * v - u * a * v = u * (f i - a) * v := by noncomm_ring
  rw [he, omegaNorm_mul_right]
  exact omegaNorm_mul_le _ _ _

/-- The ultraweak companion of `usTendsto_mul_left_right`: two-sided
multiplication by fixed elements preserves ultraweak convergence.  Immediate
from polarisation (**44II**, `continuous_ultraweak_conj`). -/
theorem uwTendsto_mul_left_right [VonNeumannAlgebra A] {ι : Type*} {l : Filter ι}
    {f : ι → A} {a : A} (u v : A) (h : UWTendsto f l a) :
    UWTendsto (fun i => u * f i * v) l (u * a * v) := by
  refine (uwTendsto_iff _ _ _).mpr fun ω => ?_
  exact (@Continuous.tendsto A ℂ (ultraweak A) _ _
    (continuous_ultraweak_conj ω u v) a).comp h

end USLinear

section MatrixVN

variable [VonNeumannAlgebra A] {N : ℕ}

/-- `matForm x x` as a map on self-adjoint parts. -/
def matFormSA (x : Fin N → A) (d : selfAdjoint (CStarMatrix (Fin N) (Fin N) A)) :
    selfAdjoint A :=
  ⟨matForm x x (d : CStarMatrix (Fin N) (Fin N) A), isSelfAdjoint_matForm d.2 x⟩

omit [PartialOrder A] [StarOrderedRing A] [VonNeumannAlgebra A] in
@[simp] theorem matFormSA_coe (x : Fin N → A)
    (d : selfAdjoint (CStarMatrix (Fin N) (Fin N) A)) :
    ((matFormSA x d : selfAdjoint A) : A)
      = matForm x x (d : CStarMatrix (Fin N) (Fin N) A) := rfl

omit [VonNeumannAlgebra A] in
theorem matFormSA_mono (x : Fin N → A) : Monotone (matFormSA (A := A) (N := N) x) :=
  fun _ _ h => Subtype.coe_le_coe.mp (matForm_mono (Subtype.coe_le_coe.mpr h) x)

/-- **49IV**.1, the substance: a nonempty bounded directed set of self-adjoint
matrices over a von Neumann algebra has a supremum, and every `𝒜`-valued
quadratic form `M ↦ ∑ᵢⱼ xᵢ* Mᵢⱼ xⱼ` preserves it. -/
theorem exists_isLUB_matForm
    (D : Set (selfAdjoint (CStarMatrix (Fin N) (Fin N) A)))
    (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) :
    ∃ S : selfAdjoint (CStarMatrix (Fin N) (Fin N) A), IsLUB D S ∧
      ∀ x : Fin N → A, IsLUB (matFormSA x '' D) (matFormSA x S) := by
  classical
  obtain ⟨b, hb⟩ := hbdd
  obtain ⟨d₀, hd₀⟩ := hne
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  have : IsDirectedOrder D := directedOn_iff_isDirectedOrder.mp hdir
  -- the auxiliary suprema `⋁_{d∈D} ∑ᵢⱼ xᵢ* dᵢⱼ xⱼ`
  have hDx : ∀ x : Fin N → A, (matFormSA x '' D).Nonempty ∧
      DirectedOn (· ≤ ·) (matFormSA x '' D) ∧ BddAbove (matFormSA x '' D) := by
    intro x
    refine ⟨⟨matFormSA x d₀, d₀, hd₀, rfl⟩, ?_, ⟨matFormSA x b, ?_⟩⟩
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨r, hr, hpr, hqr⟩ := hdir p hp q hq
      exact ⟨matFormSA x r, ⟨r, hr, rfl⟩, matFormSA_mono x hpr, matFormSA_mono x hqr⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact matFormSA_mono x (hb hp)
  set sx : (Fin N → A) → selfAdjoint A := fun x => dirSup _ (hDx x) with hsx
  have hlubx : ∀ x, IsLUB (matFormSA x '' D) (sx x) := fun x => isLUB_dirSup _ (hDx x)
  -- each such family converges ultrastrongly to its supremum (**44XIV**)
  have hconv : ∀ x : Fin N → A,
      USTendsto (fun d : D => matForm x x (d.1 : CStarMatrix (Fin N) (Fin N) A))
        atTop ((sx x : selfAdjoint A) : A) := by
    intro x
    have hg : Tendsto (fun d : D => (⟨matFormSA x d.1,
        ⟨d.1, d.2, rfl⟩⟩ : (matFormSA x '' D))) atTop atTop := by
      rw [tendsto_atTop]
      rintro ⟨-, p, hp, rfl⟩
      filter_upwards [eventually_ge_atTop (⟨p, hp⟩ : D)] with d hd
      exact Subtype.coe_le_coe.mpr (matFormSA_mono x hd)
    exact (vna_supremum_uslimit (matFormSA x '' D) (hDx x)).comp hg
  -- the candidate supremum, entry by entry, by polarisation
  set Sm : CStarMatrix (Fin N) (Fin N) A := CStarMatrix.ofMatrix (Matrix.of fun i j =>
    (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4, Complex.I ^ k •
      ((sx (matPolVec j i (Complex.I ^ k)) : selfAdjoint A) : A)) with hSm
  have hentry : ∀ i j, USTendsto
      (fun d : D => (d.1 : CStarMatrix (Fin N) (Fin N) A) i j) atTop (Sm i j) := by
    intro i j
    have hrw : ∀ d : D, (d.1 : CStarMatrix (Fin N) (Fin N) A) i j
        = (4 : ℂ)⁻¹ • ∑ k ∈ Finset.range 4, Complex.I ^ k •
            matForm (matPolVec j i (Complex.I ^ k)) (matPolVec j i (Complex.I ^ k))
              (d.1 : CStarMatrix (Fin N) (Fin N) A) :=
      fun d => matForm_polarization i j _
    simp only [hrw]
    exact usTendsto_smul _ (usTendsto_finsetSum fun k _ => usTendsto_smul _ (hconv _))
  have hform : ∀ x : Fin N → A,
      USTendsto (fun d : D => matForm x x (d.1 : CStarMatrix (Fin N) (Fin N) A))
        atTop (matForm x x Sm) := by
    intro x
    simp only [matForm]
    exact usTendsto_finsetSum fun i _ => usTendsto_finsetSum fun j _ =>
      usTendsto_mul_left_right _ _ (hentry i j)
  -- the two ultrastrong limits agree
  have huniq : ∀ x : Fin N → A, matForm x x Sm = ((sx x : selfAdjoint A) : A) := by
    intro x
    let _ : TopologicalSpace A := ultrastrong A
    have _ : T2Space A := (vn_positive_basic_1 (A := A)).2
    exact tendsto_nhds_unique (hform x) (hconv x)
  have hSsa : IsSelfAdjoint Sm := by
    refine matrix_ext_of_matForm fun x => ?_
    rw [matForm_star_matrix, huniq]
    exact (sx x).2.star_eq
  refine ⟨⟨Sm, hSsa⟩, ⟨fun d hd => ?_, fun t ht => ?_⟩, fun x => ?_⟩
  · refine Subtype.coe_le_coe.mp (le_iff_matForm.mpr fun x => ?_)
    rw [huniq]
    exact Subtype.coe_le_coe.mpr ((hlubx x).1 ⟨d, hd, rfl⟩)
  · refine Subtype.coe_le_coe.mp (le_iff_matForm.mpr fun x => ?_)
    rw [huniq]
    have hub : matFormSA x t ∈ upperBounds (matFormSA x '' D) := by
      rintro _ ⟨p, hp, rfl⟩
      exact matFormSA_mono x (ht hp)
    exact Subtype.coe_le_coe.mpr ((hlubx x).2 hub)
  · have hSx : matFormSA x ⟨Sm, hSsa⟩ = sx x := Subtype.ext (huniq x)
    rw [hSx]
    exact hlubx x

/-- For an np-functional `φ` on `𝒜` and `x ∈ 𝒜^N`, the functional
`M ↦ φ(∑ᵢⱼ xᵢ* Mᵢⱼ xⱼ)` is an np-functional on `M_N(𝒜)`.  (These are the
np-functionals 49IV.2 is about, for `a = b = x`.) -/
noncomputable def matFormNP (φ : NPFunctional A) (x : Fin N → A) :
    NPFunctional (CStarMatrix (Fin N) (Fin N) A) where
  toPositiveLinearMap :=
    { toFun := fun M => φ (matForm x x M)
      map_add' := fun M M' => by
        rw [matForm_add_matrix]; exact map_add φ.toPositiveLinearMap _ _
      map_smul' := fun c M => by
        rw [matForm_smul_matrix]; exact map_smul φ.toPositiveLinearMap _ _
      monotone' := fun M M' h => npFunctional_mono φ (matForm_mono h x) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    obtain ⟨S, hS, hSx⟩ := exists_isLUB_matForm D hne hdir ⟨s, hlub.1⟩
    have hsS : s = S := hlub.unique hS
    subst hsS
    have hkey := φ.preservesDirSups' (matFormSA x '' D) (matFormSA x s)
      (hne.image _) ?_ (hSx x)
    · rw [← Set.image_comp] at hkey
      exact hkey
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨r, hr, hpr, hqr⟩ := hdir p hp q hq
      exact ⟨matFormSA x r, ⟨r, hr, rfl⟩, matFormSA_mono x hpr, matFormSA_mono x hqr⟩

@[simp] theorem matFormNP_apply (φ : NPFunctional A) (x : Fin N → A)
    (M : CStarMatrix (Fin N) (Fin N) A) :
    matFormNP φ x M = φ (matForm x x M) := rfl

end MatrixVN

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 1: the C*-algebra
`M_N(𝒜)` of `N×N`-matrices over a von Neumann algebra `𝒜` (Mathlib:
`CStarMatrix (Fin N) (Fin N) 𝒜`) is a von Neumann algebra. -/
instance mn_vna_1 [VonNeumannAlgebra A] (N : ℕ) :
    VonNeumannAlgebra (CStarMatrix (Fin N) (Fin N) A) where
  isLUB_of_bddAbove_directed D hne hdir hbdd := by
    obtain ⟨S, hS, -⟩ := exists_isLUB_matForm D hne hdir hbdd
    exact ⟨S, hS⟩
  np_faithful M hM h := by
    refine matrix_ext_of_matForm (M' := 0) fun x => ?_
    rw [matForm_zero_matrix]
    refine VonNeumannAlgebra.np_faithful _ (nonneg_iff_matForm.mp hM x) fun φ => ?_
    exact h (matFormNP φ x)

/-! ### Auxiliary machinery for **49IV**.2: the corner embeddings `𝒜 → M_N(𝒜)`

The matrix units `x ↦ x·eᵢⱼ` decompose every matrix as `M = ∑ᵢⱼ Mᵢⱼ·eᵢⱼ`;
the diagonal ones `x ↦ x·eⱼⱼ` are normal positive maps, so they pull
np-functionals of `M_N(𝒜)` back to np-functionals of `𝒜`, and polarisation
(**44II**) does the same for the off-diagonal ones.  That gives one direction
of 49IV.2; the other is the polarisation of the `𝒜`-valued form above
together with the estimate `‖Xᵢⱼ‖_φ ≤ ‖X‖_{φ⟨eⱼ,·eⱼ⟩}`. -/

section MatEmb

variable {N : ℕ}

omit [PartialOrder A] [StarOrderedRing A]

/-- The matrix with `x` in position `(i,j)` and zeroes elsewhere. -/
def matEmb (i j : Fin N) (x : A) : CStarMatrix (Fin N) (Fin N) A :=
  CStarMatrix.ofMatrix (Matrix.of fun p q => if p = i then (if q = j then x else 0) else 0)

theorem matEmb_apply (i j : Fin N) (x : A) (p q : Fin N) :
    matEmb i j x p q = if p = i then (if q = j then x else 0) else 0 := rfl

theorem matForm_matEmb (i j : Fin N) (x : A) (y z : Fin N → A) :
    matForm y z (matEmb i j x) = star (y i) * x * z j := by
  simp [matForm, matEmb_apply, ite_mul, mul_ite]

theorem matEmb_add (i j : Fin N) (x y : A) :
    matEmb i j (x + y) = matEmb i j x + matEmb i j y := by
  ext p q; simp [matEmb_apply, apply_ite₂ (· + ·)]

theorem matEmb_smul (i j : Fin N) (c : ℂ) (x : A) :
    matEmb i j (c • x) = c • matEmb i j x := by
  ext p q; simp [matEmb_apply, smul_ite]

theorem matEmb_star (i j : Fin N) (x : A) :
    star (matEmb i j x) = matEmb j i (star x) := by
  ext p q
  simp only [CStarMatrix.star_apply, matEmb_apply, apply_ite star, star_zero]
  split_ifs <;> rfl

theorem matEmb_star_mul (i j : Fin N) (x : A) :
    star (matEmb i j x) * matEmb i j x = matEmb j j (star x * x) := by
  ext p q
  rw [matEmb_star, CStarMatrix.mul_apply]
  simp only [matEmb_apply, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  split_ifs <;> rfl

end MatEmb

section MatEmbOrder

variable {N : ℕ}

theorem matEmb_mono (i : Fin N) {x y : A} (h : x ≤ y) :
    matEmb i i x ≤ matEmb i i y := by
  refine le_iff_matForm.mpr fun z => ?_
  rw [matForm_matEmb, matForm_matEmb]
  exact star_left_conjugate_le_conjugate h (z i)

omit [PartialOrder A] [StarOrderedRing A] in
theorem matForm_finsetSum_matrix {κ : Type*} (s : Finset κ) (y z : Fin N → A)
    (F : κ → CStarMatrix (Fin N) (Fin N) A) :
    matForm y z (∑ k ∈ s, F k) = ∑ k ∈ s, matForm y z (F k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [matForm]
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, matForm_add_matrix, ih, Finset.sum_insert hk]

omit [PartialOrder A] [StarOrderedRing A] in
theorem sum_matEmb (M : CStarMatrix (Fin N) (Fin N) A) :
    M = ∑ i, ∑ j, matEmb i j (M i j) := by
  refine matrix_ext_of_matForm fun x => ?_
  simp only [matForm_finsetSum_matrix, matForm_matEmb]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem matEmb_mul (i j k : Fin N) (x y : A) :
    matEmb i j x * matEmb j k y = matEmb i k (x * y) := by
  ext p q
  rw [CStarMatrix.mul_apply]
  simp only [matEmb_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> rfl

/-- `x ↦ matEmb i i x`, the `i`-th diagonal corner embedding, as a positive
linear map `𝒜 → M_N(𝒜)`. -/
def matEmbP (i : Fin N) : A →ₚ[ℂ] CStarMatrix (Fin N) (Fin N) A where
  toFun := matEmb i i
  map_add' := matEmb_add i i
  map_smul' := matEmb_smul i i
  monotone' := fun _ _ h => matEmb_mono i h

@[simp] theorem matEmbP_apply (i : Fin N) (x : A) : matEmbP i x = matEmb i i x := rfl

/-- The corner embeddings are normal. -/
theorem matEmb_normal [VonNeumannAlgebra A] (i : Fin N) :
    PreservesDirSups (matEmb (A := A) (N := N) i i) := by
  intro D s hne hdir hlub
  have hbdd : BddAbove D := ⟨s, hlub.1⟩
  have hh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, hbdd⟩
  have hs : dirSup D hh = s := (isLUB_dirSup D hh).unique hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact matEmb_mono i (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · intro T hT
    refine le_iff_matForm.mpr fun x => ?_
    rw [matForm_matEmb]
    have hadn := ad_normal (x i) D hh
    rw [hs] at hadn
    refine hadn.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    have hle := hT ⟨d, hd, rfl⟩
    change star (x i) * ((d : selfAdjoint A) : A) * x i ≤ matForm x x T
    rw [← matForm_matEmb i i ((d : selfAdjoint A) : A) x x]
    exact matForm_mono hle x

/-- The np-functional `x ↦ ω(matEmb i i x)` on `𝒜` attached to an
np-functional `ω` on `M_N(𝒜)`. -/
noncomputable def matEmbNP [VonNeumannAlgebra A] (i : Fin N)
    (ω : NPFunctional (CStarMatrix (Fin N) (Fin N) A)) : NPFunctional A :=
  compNP (matEmbP i) (matEmb_normal i) ω

@[simp] theorem matEmbNP_apply [VonNeumannAlgebra A] (i : Fin N)
    (ω : NPFunctional (CStarMatrix (Fin N) (Fin N) A)) (x : A) :
    matEmbNP i ω x = ω (matEmb i i x) := rfl

theorem omegaNorm_matEmb [VonNeumannAlgebra A] (i j : Fin N)
    (ω : NPFunctional (CStarMatrix (Fin N) (Fin N) A)) (x : A) :
    omegaNorm _ ω (matEmb i j x) = omegaNorm A (matEmbNP j ω) x := by
  rw [omegaNorm, omegaNorm, matEmb_star_mul]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem matEmb_sub (i j : Fin N) (x y : A) :
    matEmb i j (x - y) = matEmb i j x - matEmb i j y := by
  ext p q; simp [matEmb_apply, apply_ite₂ (· - ·)]

section Conv

variable [VonNeumannAlgebra A]


/-- `x ↦ ω(matEmb i j x)` is a `ℂ`-combination of np-functionals on `𝒜`
(polarisation **44II** applied to `matEmb i j x = (matEmb i j 1)·(matEmb j j x)`). -/
theorem npFunctional_matEmb_repr (i j : Fin N)
    (ω : NPFunctional (CStarMatrix (Fin N) (Fin N) A)) :
    ∃ ψ : ℕ → NPFunctional A, ∀ x : A,
      (ω (matEmb i j x) : ℂ)
        = (4 : ℂ)⁻¹ * ∑ k ∈ Finset.range 4, Complex.I ^ k * ψ k x := by
  set u : CStarMatrix (Fin N) (Fin N) A := matEmb i j 1 with hu
  refine ⟨fun k => matEmbNP j (conjNP ((Complex.I ^ k : ℂ) • star u + 1) ω), fun x => ?_⟩
  have hx : matEmb i j x = u * matEmb j j x := by rw [hu, matEmb_mul, one_mul]
  have h := mult_polarization (star u) 1 (matEmb j j x)
  rw [star_star, mul_one] at h
  rw [hx, h, npFunctional_csmul, npFunctional_finsetSum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [npFunctional_csmul]
  rfl

theorem uwTendsto_matEmb {ι : Type*} {l : Filter ι} (i j : Fin N)
    {f : ι → A} {a : A} (h : UWTendsto f l a) :
    UWTendsto (fun α => matEmb i j (f α)) l (matEmb i j a) := by
  rw [uwTendsto_iff] at h ⊢
  intro ω
  obtain ⟨ψ, hψ⟩ := npFunctional_matEmb_repr i j ω
  simp only [hψ]
  exact Filter.Tendsto.const_mul _
    (tendsto_finset_sum _ fun k _ => ((h (ψ k)).const_mul _))

theorem usTendsto_matEmb {ι : Type*} {l : Filter ι} (i j : Fin N)
    {f : ι → A} {a : A} (h : USTendsto f l a) :
    USTendsto (fun α => matEmb i j (f α)) l (matEmb i j a) := by
  rw [usTendsto_iff] at h ⊢
  intro ω
  have he : ∀ α, omegaNorm _ ω (matEmb i j (f α) - matEmb i j a)
      = omegaNorm A (matEmbNP j ω) (f α - a) := by
    intro α; rw [← matEmb_sub, omegaNorm_matEmb]
  simp only [he]
  exact h _

/-- The `‖·‖_ω`-estimate behind "ultrastrong convergence in `M_N(𝒜)` implies
entrywise ultrastrong convergence": `‖Xᵢⱼ‖_φ ≤ ‖X‖_{φ(⟨eⱼ,·eⱼ⟩)}`. -/
theorem omegaNorm_entry_le (φ : NPFunctional A) (i j : Fin N)
    (X : CStarMatrix (Fin N) (Fin N) A) :
    omegaNorm A φ (X i j) ≤ omegaNorm _ (matFormNP φ (matUnit j)) X := by
  rw [omegaNorm, omegaNorm]
  refine Real.sqrt_le_sqrt ?_
  have h1 : (matFormNP φ (matUnit j) (star X * X) : ℂ) = φ ((star X * X) j j) := by
    rw [matFormNP_apply, matForm_matUnit]
  have h2 : (star X * X) j j = ∑ k, star (X k j) * X k j := by
    rw [CStarMatrix.mul_apply]
    simp [CStarMatrix.star_apply]
  have h3 : star (X i j) * X i j ≤ ∑ k, star (X k j) * X k j :=
    Finset.single_le_sum (f := fun k => star (X k j) * X k j)
      (fun k _ => star_mul_self_nonneg _) (Finset.mem_univ i)
  have h4 := npFunctional_mono φ h3
  rw [← h2, ← h1] at h4
  exact (Complex.le_def.mp h4).1

/-- Entrywise recovery of an np-functional value by polarisation. -/
theorem npFunctional_entry_repr (φ : NPFunctional A) (i j : Fin N)
    (X : CStarMatrix (Fin N) (Fin N) A) :
    (φ (X i j) : ℂ) = (4 : ℂ)⁻¹ * ∑ k ∈ Finset.range 4, Complex.I ^ k *
      matFormNP φ (matPolVec j i (Complex.I ^ k)) X := by
  conv_lhs => rw [matForm_polarization i j X]
  rw [npFunctional_csmul, npFunctional_finsetSum]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => npFunctional_csmul _ _ _)

end Conv

end MatEmbOrder

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 2 (second half): a net
in `M_N(𝒜)` converges ultraweakly (resp. ultrastrongly) iff it does so
entrywise. -/
theorem mn_vna_2' [VonNeumannAlgebra A] (N : ℕ) {ι : Type*} (l : Filter ι)
    (M : ι → CStarMatrix (Fin N) (Fin N) A)
    (M₀ : CStarMatrix (Fin N) (Fin N) A) :
    (UWTendsto M l M₀ ↔ ∀ i j,
        UWTendsto (fun α => CStarMatrix.ofMatrix.symm (M α) i j) l
          (CStarMatrix.ofMatrix.symm M₀ i j)) ∧
      (USTendsto M l M₀ ↔ ∀ i j,
        USTendsto (fun α => CStarMatrix.ofMatrix.symm (M α) i j) l
          (CStarMatrix.ofMatrix.symm M₀ i j)) := by
  have hMsum : M = fun α => ∑ i, ∑ j, matEmb i j (M α i j) :=
    funext fun α => sum_matEmb (M α)
  have hM₀sum : M₀ = ∑ i, ∑ j, matEmb i j (M₀ i j) := sum_matEmb M₀
  constructor
  · constructor
    · intro h i j
      rw [uwTendsto_iff] at h ⊢
      intro φ
      change Tendsto (fun α => (φ (M α i j) : ℂ)) l (𝓝 (φ (M₀ i j)))
      simp only [npFunctional_entry_repr φ i j]
      exact Filter.Tendsto.const_mul _
        (tendsto_finset_sum _ fun k _ => (h _).const_mul _)
    · intro h
      rw [hMsum, hM₀sum]
      exact uwTendsto_finsetSum fun i _ => uwTendsto_finsetSum fun j _ =>
        uwTendsto_matEmb i j (h i j)
  · constructor
    · intro h i j
      rw [usTendsto_iff] at h ⊢
      intro φ
      refine squeeze_zero (fun α => omegaNorm_nonneg _ _) (fun α => ?_)
        (h (matFormNP φ (matUnit j)))
      have he : (M α i j) - (M₀ i j) = (M α - M₀) i j := by
        rw [CStarMatrix.sub_apply]
      change omegaNorm A φ (M α i j - M₀ i j) ≤ _
      rw [he]
      exact omegaNorm_entry_le φ i j (M α - M₀)
    · intro h
      rw [hMsum, hM₀sum]
      exact usTendsto_finsetSum fun i _ => usTendsto_finsetSum fun j _ =>
        usTendsto_matEmb i j (h i j)


/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 2 (first half): for
`a₁,…,a_N, b₁,…,b_N ∈ 𝒜`, the map `M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ bⱼ : M_N(𝒜) → 𝒜` is
ultraweakly and ultrastrongly continuous; for `a = b` it is moreover normal.
(Placed after the second half, which its proof uses.)  Complete positivity
for `a = b` is the sibling `mn_vna_2_cp`, and the exercise's "in particular"
clause is `mn_vna_2_entry`; the shape of this conjunction is fixed by its
uses elsewhere in the tree, so the two are separate statements. -/
theorem mn_vna_2 [VonNeumannAlgebra A] (N : ℕ) (a b : Fin N → A) :
    @Continuous _ _ (ultraweak (CStarMatrix (Fin N) (Fin N) A)) (ultraweak A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          ∑ i, ∑ j, star (a i) * CStarMatrix.ofMatrix.symm M i j * b j) ∧
      @Continuous _ _ (ultrastrong (CStarMatrix (Fin N) (Fin N) A))
        (ultrastrong A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          ∑ i, ∑ j, star (a i) * CStarMatrix.ofMatrix.symm M i j * b j) ∧
      PreservesDirSups (fun M : CStarMatrix (Fin N) (Fin N) A =>
        ∑ i, ∑ j, star (a i) * CStarMatrix.ofMatrix.symm M i j * a j) := by
  -- The map is `matForm a b`, and convergence in `M_N(𝒜)` is entrywise
  -- (**49IV**.2', below — stated for an arbitrary filter, so it applies to
  -- the identity net on `𝓝 M₀` and yields continuity, not just sequential
  -- continuity).  Normality for `a = b` is then **44XV** (1) ⇒ (3), the map
  -- being positive by **33II** (`matForm_mono`).
  have huw : ∀ x y : Fin N → A,
      @Continuous _ _ (ultraweak (CStarMatrix (Fin N) (Fin N) A)) (ultraweak A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          ∑ i, ∑ j, star (x i) * CStarMatrix.ofMatrix.symm M i j * y j) := by
    intro x y
    let _ : TopologicalSpace (CStarMatrix (Fin N) (Fin N) A) :=
      ultraweak (CStarMatrix (Fin N) (Fin N) A)
    let _ : TopologicalSpace A := ultraweak A
    rw [continuous_iff_continuousAt]
    intro M₀
    have hentry :=
      (mn_vna_2' N (𝓝 M₀) (fun X : CStarMatrix (Fin N) (Fin N) A => X) M₀).1.mp
        tendsto_id
    exact uwTendsto_finsetSum fun i _ => uwTendsto_finsetSum fun j _ =>
      uwTendsto_mul_left_right _ _ (hentry i j)
  refine ⟨huw a b, ?_, ?_⟩
  · let _ : TopologicalSpace (CStarMatrix (Fin N) (Fin N) A) :=
      ultrastrong (CStarMatrix (Fin N) (Fin N) A)
    let _ : TopologicalSpace A := ultrastrong A
    rw [continuous_iff_continuousAt]
    intro M₀
    have hentry :=
      (mn_vna_2' N (𝓝 M₀) (fun X : CStarMatrix (Fin N) (Fin N) A => X) M₀).2.mp
        tendsto_id
    exact usTendsto_finsetSum fun i _ => usTendsto_finsetSum fun j _ =>
      usTendsto_mul_left_right _ _ (hentry i j)
  · let F : CStarMatrix (Fin N) (Fin N) A →ₚ[ℂ] A :=
      { toFun := fun M : CStarMatrix (Fin N) (Fin N) A => matForm a a M
        map_add' := fun X Y => matForm_add_matrix a a X Y
        map_smul' := fun c X => matForm_smul_matrix c a a X
        monotone' := fun X Y h => matForm_mono h a }
    exact ((p_uwcont F).out 0 2).mp (huw a a)

/-- `M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ aⱼ`, the map of **49IV**.2, bundled as a `ℂ`-linear map
`M_N(𝒜) → 𝒜` — the form complete positivity is stated for. -/
def matFormL (N : ℕ) (a : Fin N → A) :
    CStarMatrix (Fin N) (Fin N) A →ₗ[ℂ] A where
  toFun M := matForm a a M
  map_add' := matForm_add_matrix a a
  map_smul' c M := matForm_smul_matrix c a a M

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem matFormL_apply (N : ℕ) (a : Fin N → A)
    (M : CStarMatrix (Fin N) (Fin N) A) :
    matFormL N a M = ∑ i, ∑ j, star (a i) * M i j * a j := rfl

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 2 (first half, the
complete-positivity clause): `M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ aⱼ : M_N(𝒜) → 𝒜` is
*completely positive*.

Exercise, no thesis proof.  Ours is the definition (cstar.tex **10II**.6)
unwound: with `g_{p,r} = ∑ᵢ (X_p)_{r i} aᵢ b_p`, the sum
`∑_{p,q} b_p* (∑_{i,j} aᵢ* (X_p* X_q)_{ij} aⱼ) b_q` collapses to
`∑_r (∑_p g_{p,r})* (∑_q g_{q,r}) ≥ 0`.  No von Neumann hypothesis is
needed, and none is assumed. -/
theorem mn_vna_2_cp (N : ℕ) (a : Fin N → A) :
    IsCompletelyPositiveMap (matFormL N a) := by
  classical
  intro n X b
  set g : Fin n → Fin N → A :=
    fun p r => ∑ i : Fin N, X p r i * (a i * b p) with hg
  have hexp : ∀ (p q : Fin n) (i j : Fin N),
      ((star (X p) * X q) i j : A) = ∑ r : Fin N, star (X p r i) * X q r j := by
    intro p q i j
    rw [CStarMatrix.mul_apply]
    simp [CStarMatrix.star_apply]
  have hterm : ∀ p q : Fin n,
      star (b p) * matFormL N a (star (X p) * X q) * b q
        = ∑ r : Fin N, star (g p r) * g q r := by
    intro p q
    have hL : star (b p) * matFormL N a (star (X p) * X q) * b q
        = ∑ i : Fin N, ∑ j : Fin N, ∑ r : Fin N,
            star (b p) * (star (a i) * (star (X p r i) * X q r j) * a j) * b q := by
      rw [matFormL_apply]
      simp only [hexp, Finset.mul_sum, Finset.sum_mul]
    have hR : ∀ r : Fin N, star (g p r) * g q r
        = ∑ i : Fin N, ∑ j : Fin N,
            star (b p) * (star (a i) * (star (X p r i) * X q r j) * a j) * b q := by
      intro r
      simp only [hg, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [mul_assoc]
    rw [hL]
    calc ∑ i : Fin N, ∑ j : Fin N, ∑ r : Fin N,
            star (b p) * (star (a i) * (star (X p r i) * X q r j) * a j) * b q
        = ∑ i : Fin N, ∑ r : Fin N, ∑ j : Fin N,
            star (b p) * (star (a i) * (star (X p r i) * X q r j) * a j) * b q :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r : Fin N, ∑ i : Fin N, ∑ j : Fin N,
            star (b p) * (star (a i) * (star (X p r i) * X q r j) * a j) * b q :=
          Finset.sum_comm
      _ = ∑ r : Fin N, star (g p r) * g q r :=
          Finset.sum_congr rfl fun r _ => (hR r).symm
  have key : ∑ p : Fin n, ∑ q : Fin n,
        star (b p) * matFormL N a (star (X p) * X q) * b q
      = ∑ r : Fin N, star (∑ p : Fin n, g p r) * ∑ q : Fin n, g q r := by
    calc ∑ p : Fin n, ∑ q : Fin n,
            star (b p) * matFormL N a (star (X p) * X q) * b q
        = ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin N, star (g p r) * g q r :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hterm p q
      _ = ∑ p : Fin n, ∑ r : Fin N, ∑ q : Fin n, star (g p r) * g q r :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ r : Fin N, ∑ p : Fin n, ∑ q : Fin n, star (g p r) * g q r :=
          Finset.sum_comm
      _ = ∑ r : Fin N, star (∑ p : Fin n, g p r) * ∑ q : Fin n, g q r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [star_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
  rw [key]
  exact Finset.sum_nonneg fun r _ => star_mul_self_nonneg _

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 2 ("in particular"):
each entry map `M ↦ Mᵢⱼ : M_N(𝒜) → 𝒜` is ultraweakly and ultrastrongly
continuous.  Read off from **49IV**.2' `mn_vna_2'` applied to the identity
net on `𝓝 M₀`, as in `mn_vna_2`. -/
theorem mn_vna_2_entry [VonNeumannAlgebra A] (N : ℕ) (i j : Fin N) :
    @Continuous _ _ (ultraweak (CStarMatrix (Fin N) (Fin N) A)) (ultraweak A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          CStarMatrix.ofMatrix.symm M i j) ∧
      @Continuous _ _ (ultrastrong (CStarMatrix (Fin N) (Fin N) A))
        (ultrastrong A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          CStarMatrix.ofMatrix.symm M i j) := by
  constructor
  · let _ : TopologicalSpace (CStarMatrix (Fin N) (Fin N) A) :=
      ultraweak (CStarMatrix (Fin N) (Fin N) A)
    let _ : TopologicalSpace A := ultraweak A
    rw [continuous_iff_continuousAt]
    intro M₀
    exact (mn_vna_2' N (𝓝 M₀) (fun X : CStarMatrix (Fin N) (Fin N) A => X) M₀).1.mp
      tendsto_id i j
  · let _ : TopologicalSpace (CStarMatrix (Fin N) (Fin N) A) :=
      ultrastrong (CStarMatrix (Fin N) (Fin N) A)
    let _ : TopologicalSpace A := ultrastrong A
    rw [continuous_iff_continuousAt]
    intro M₀
    exact (mn_vna_2' N (𝓝 M₀) (fun X : CStarMatrix (Fin N) (Fin N) A => X) M₀).2.mp
      tendsto_id i j

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 3: for an ncp-map
`f : 𝒜 → ℬ` between von Neumann algebras, the entrywise map
`M_N f : M_N(𝒜) → M_N(ℬ)` (cstar.tex 33III, `mnf`) is normal. -/
theorem mn_vna_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B] (N : ℕ)
    (f : NCPMap A B) :
    PreservesDirSups fun M : CStarMatrix (Fin N) (Fin N) A =>
      CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm M).map f) := by
  -- Normality is *not* proved directly (unwinding `PreservesDirSups` for
  -- `M_N f` reduces to itself, because `M ↦ M i j` is not monotone).  Go
  -- through **44XV** `p_uwcont` instead: `M_N f` is a positive linear map,
  -- so it is normal as soon as it is ultraweakly *continuous*, and
  -- continuity is entrywise by **49IV**.2' `mn_vna_2'` — which is stated for
  -- an arbitrary filter, so it applies to the identity net on `𝓝 M₀`.
  have hfc : @Continuous A B (ultraweak A) (ultraweak B) ⇑f :=
    ((p_uwcont (ncpPositive f)).out 2 0).mp f.preservesDirSups'
  let F : CStarMatrix (Fin N) (Fin N) A →ₚ[ℂ] CStarMatrix (Fin N) (Fin N) B :=
    { toFun := fun M : CStarMatrix (Fin N) (Fin N) A =>
        CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm M).map ⇑f)
      map_add' := by
        intro X Y
        ext i j
        show (f ((X + Y) i j) : B) = f (X i j) + f (Y i j)
        rw [show ((X + Y) i j : A) = X i j + Y i j from rfl]
        exact map_add f.toCompletelyPositiveMap _ _
      map_smul' := by
        intro r X
        ext i j
        show (f ((r • X) i j) : B) = (r • (CStarMatrix.ofMatrix
          ((CStarMatrix.ofMatrix.symm X).map ⇑f))) i j
        rw [show ((r • X) i j : A) = r • X i j from rfl,
          show ((r • (CStarMatrix.ofMatrix
            ((CStarMatrix.ofMatrix.symm X).map ⇑f))) i j : B)
            = r • (f (X i j)) from rfl]
        exact map_smul f.toCompletelyPositiveMap r (X i j)
      monotone' := by
        intro X Y hXY
        have h0 : (0 : CStarMatrix (Fin N) (Fin N) A) ≤ Y - X := sub_nonneg.mpr hXY
        have := f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N (Y - X) h0
        rw [← sub_nonneg]
        refine le_of_le_of_eq this ?_
        ext i j
        show (f ((Y - X) i j) : B) = f (Y i j) - f (X i j)
        rw [show ((Y - X) i j : A) = Y i j - X i j from rfl]
        exact map_sub f.toCompletelyPositiveMap _ _ }
  have hcont : @Continuous (CStarMatrix (Fin N) (Fin N) A)
      (CStarMatrix (Fin N) (Fin N) B)
      (ultraweak (CStarMatrix (Fin N) (Fin N) A))
      (ultraweak (CStarMatrix (Fin N) (Fin N) B)) ⇑F := by
    let _ : TopologicalSpace (CStarMatrix (Fin N) (Fin N) A) :=
      ultraweak (CStarMatrix (Fin N) (Fin N) A)
    let _ : TopologicalSpace (CStarMatrix (Fin N) (Fin N) B) :=
      ultraweak (CStarMatrix (Fin N) (Fin N) B)
    rw [continuous_iff_continuousAt]
    intro M₀
    have hid : UWTendsto (fun X : CStarMatrix (Fin N) (Fin N) A => X) (𝓝 M₀) M₀ :=
      tendsto_id
    have hentry :=
      (mn_vna_2' N (𝓝 M₀) (fun X : CStarMatrix (Fin N) (Fin N) A => X) M₀).1.mp hid
    refine (mn_vna_2' N (𝓝 M₀) (fun X => F X) (F M₀)).1.mpr ?_
    intro i j
    exact Filter.Tendsto.comp
      (@Continuous.tendsto A B (ultraweak A) (ultraweak B) _ hfc (M₀ i j))
      (hentry i j)
  exact ((p_uwcont F).out 0 2).mp hcont

end Elementary

/-! ## Parsecs 500–510: `L^∞(X)` of a finite complete measure space

**50I** (`linfty-example`, vn.tex:1313) and **51I–51VI**
(`measure-theory-recap`, vn.tex:1369): recapitulation of measure theory and
the construction of `𝓛^∞(X)` and `L^∞(X)`, including the counterexample
that `𝓛^∞([0,1])` is *not* a von Neumann algebra (51III) — narrative;
nothing converted separately.  The quotient C*-algebra `L^∞(X)` has no
Mathlib counterpart (Mathlib's `Lp E ∞ μ` carries no multiplicative
structure), so 51IX below is stated existentially. -/

section Measure

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Auxiliary: a positive functional is real on self-adjoint elements (the
same argument as `npFunctional_im_eq_zero`, but for a bare positive linear
map, which is what **51VII** is given). -/
private theorem positiveLinearMap_im_eq_zero (τ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) : (τ a).im = 0 := by
  have h := map_star τ a
  rw [ha.star_eq] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The construction of **51VIII** (vn.tex:1596, Proof), which yields both
parts of **51VII** at once: a bounded directed set `D` of self-adjoint
elements has a supremum, and `τ` preserves it.

The thesis's argument verbatim.  Write `M = ⋁_{d ∈ D} τ(d)` (a supremum in
`ℝ`, since `τ` is real and monotone on `sa(A)` and `D` is bounded).  Pick an
ascending `a₁ ≤ a₂ ≤ ⋯` in `D` with `⋁ₙ τ(aₙ) = M`, and let `s = ⋁ₙ aₙ` be
the supremum supplied by the hypothesis.  Any upper bound of `D` bounds the
`aₙ`, so `s` is below it; the work is that `s` is an upper bound of `D` at
all.  Given `b ∈ D`, directedness produces an ascending `e₀ ≤ e₁ ≤ ⋯` in `D`
with `b ≤ e₀` and `aₙ ≤ eₙ`; then `s ≤ t := ⋁ₙ eₙ` while
`M = ⋁ₙ τ(aₙ) = τ(s) ≤ τ(t) = ⋁ₙ τ(eₙ) ≤ M`, so `τ(t − s) = 0` and
faithfulness gives `t = s`, whence `b ≤ e₀ ≤ t = s`.  Normality falls out of
the same chain: `τ(s) = M = ⋁_{d ∈ D} τ(d)`. -/
private theorem countably_normal_key (τ : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, 0 ≤ a → τ a = 0 → a = 0)
    (hsup : ∀ a : ℕ → selfAdjoint A, Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint A, IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => τ (a n : A)) (τ (s : A)))
    (D : Set (selfAdjoint A)) (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D)
    (hbdd : BddAbove D) :
    ∃ s : selfAdjoint A, IsLUB D s ∧
      IsLUB ((fun d : selfAdjoint A => τ (d : A)) '' D) (τ (s : A)) := by
  classical
  -- `f` is `τ` read as a real-valued monotone function on `sa(A)`
  set f : selfAdjoint A → ℝ := fun d => (τ (d : A)).re
  have hτre : ∀ d : selfAdjoint A, (τ (d : A) : ℂ) = ((f d : ℝ) : ℂ) := by
    intro d
    exact (Complex.conj_eq_iff_re.mp (by
      rw [Complex.conj_eq_iff_im]; exact positiveLinearMap_im_eq_zero τ d.2)).symm
  have hfmono : ∀ d e : selfAdjoint A, d ≤ e → f d ≤ f e := by
    intro d e h
    exact (Complex.le_def.mp (OrderHomClass.mono τ (Subtype.coe_le_coe.mpr h))).1
  -- `M = ⋁_{d ∈ D} τ(d)` in `ℝ`
  obtain ⟨u, hu⟩ := hbdd
  obtain ⟨d₀, hd₀⟩ := hne
  have hSne : (f '' D).Nonempty := ⟨f d₀, ⟨d₀, hd₀, rfl⟩⟩
  have hSbdd : BddAbove (f '' D) := by
    refine ⟨f u, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hfmono d u (hu hd)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, IsLUB (f '' D) M := ⟨_, Real.isLUB_sSup hSne hSbdd⟩
  have hfle : ∀ d ∈ D, f d ≤ M := fun d hd => hM.1 ⟨d, hd, rfl⟩
  -- a sequence in `D` whose `τ`-values approach `M` has a supremum of value `M`
  have hval : ∀ e : ℕ → selfAdjoint A, (∀ n, e n ∈ D) →
      (∀ n : ℕ, M - 1 / (n + 1) < f (e n)) → ∀ s : selfAdjoint A,
      IsLUB (Set.range fun n => τ (e n : A)) (τ (s : A)) → f s = M := by
    intro e heD hegt s hs
    have himg : ∀ w ∈ Set.range fun n => τ (e n : A), w.im = 0 := by
      rintro _ ⟨n, rfl⟩
      exact positiveLinearMap_im_eq_zero τ (e n).2
    have hre := isLUB_re_of_isLUB himg hs
    have himage : Complex.re '' (Set.range fun n => τ (e n : A))
        = Set.range fun n => f (e n) := by
      ext r
      constructor
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨τ (e n : A), ⟨n, rfl⟩, rfl⟩
    rw [himage] at hre
    refine le_antisymm (hre.2 ?_) ?_
    · rintro _ ⟨n, rfl⟩
      exact hfle _ (heD n)
    · by_contra hlt
      push_neg at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have h1 : M - 1 / (n + 1) < f (e n) := hegt n
      have h2 : f (e n) ≤ f s := hre.1 ⟨n, rfl⟩
      have h3 : (1 : ℝ) / (n + 1) < M - f s := hn
      linarith
  -- directedness, as a choice function
  obtain ⟨g, hg⟩ : ∃ g : selfAdjoint A → selfAdjoint A → selfAdjoint A,
      ∀ x z : selfAdjoint A, x ∈ D → z ∈ D →
        g x z ∈ D ∧ x ≤ g x z ∧ z ≤ g x z := by
    have hpair : ∀ x z : selfAdjoint A, ∃ y : selfAdjoint A,
        x ∈ D → z ∈ D → y ∈ D ∧ x ≤ y ∧ z ≤ y := by
      intro x z
      by_cases hx : x ∈ D
      · by_cases hz : z ∈ D
        · obtain ⟨w, hwD, h1, h2⟩ := hdir x hx z hz
          exact ⟨w, fun _ _ => ⟨hwD, h1, h2⟩⟩
        · exact ⟨x, fun _ h => absurd h hz⟩
      · exact ⟨x, fun h _ => absurd h hx⟩
    choose g hg using hpair
    exact ⟨g, fun x z hx hz => hg x z hx hz⟩
  -- choose `cₙ ∈ D` with `τ(cₙ) > M − 1/(n+1)`
  obtain ⟨c, hcD, hcgt⟩ : ∃ c : ℕ → selfAdjoint A,
      (∀ n, c n ∈ D) ∧ ∀ n : ℕ, M - 1 / (n + 1) < f (c n) := by
    have hex : ∀ n : ℕ, ∃ d : selfAdjoint A, d ∈ D ∧ M - 1 / (n + 1) < f d := by
      intro n
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      obtain ⟨r, hrS, hr⟩ := (lt_isLUB_iff hM).mp (by linarith : M - 1 / (n + 1) < M)
      obtain ⟨d, hd, rfl⟩ := hrS
      exact ⟨d, hd, hr⟩
    choose c hcD hcgt using hex
    exact ⟨c, hcD, hcgt⟩
  -- the ascending sequence `a` in `D` with `⋁ₙ τ(aₙ) = M`
  obtain ⟨a, ha0, hasucc⟩ : ∃ a : ℕ → selfAdjoint A,
      a 0 = c 0 ∧ ∀ n, a (n + 1) = g (a n) (c (n + 1)) :=
    ⟨fun n => Nat.rec (c 0) (fun k prev => g prev (c (k + 1))) n, rfl, fun _ => rfl⟩
  have haD : ∀ n, a n ∈ D := by
    intro n
    induction n with
    | zero => rw [ha0]; exact hcD 0
    | succ n ih => rw [hasucc n]; exact (hg _ _ ih (hcD (n + 1))).1
  have hastep : ∀ n, a n ≤ a (n + 1) := by
    intro n
    rw [hasucc n]
    exact (hg _ _ (haD n) (hcD (n + 1))).2.1
  have hamono : Monotone a := monotone_nat_of_le_succ hastep
  have hca : ∀ n, c n ≤ a n := by
    intro n
    cases n with
    | zero => rw [ha0]
    | succ n => rw [hasucc n]; exact (hg _ _ (haD n) (hcD (n + 1))).2.2
  have hagt : ∀ n : ℕ, M - 1 / (n + 1) < f (a n) := fun n =>
    lt_of_lt_of_le (hcgt n) (hfmono _ _ (hca n))
  have habdd : BddAbove (Set.range a) := by
    refine ⟨u, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hu (haD n)
  obtain ⟨s, hslub, hsτ⟩ := hsup a hamono habdd
  have hfs : f s = M := hval a haD hagt s hsτ
  -- the crux: `s` is an upper bound of `D`
  have hub : ∀ b ∈ D, b ≤ s := by
    intro b hb
    obtain ⟨e, he0, hesucc⟩ : ∃ e : ℕ → selfAdjoint A,
        e 0 = g b (a 0) ∧ ∀ n, e (n + 1) = g (e n) (a (n + 1)) :=
      ⟨fun n => Nat.rec (g b (a 0)) (fun k prev => g prev (a (k + 1))) n, rfl,
        fun _ => rfl⟩
    have heD : ∀ n, e n ∈ D := by
      intro n
      induction n with
      | zero => rw [he0]; exact (hg _ _ hb (haD 0)).1
      | succ n ih => rw [hesucc n]; exact (hg _ _ ih (haD (n + 1))).1
    have hestep : ∀ n, e n ≤ e (n + 1) := by
      intro n
      rw [hesucc n]
      exact (hg _ _ (heD n) (haD (n + 1))).2.1
    have hemono : Monotone e := monotone_nat_of_le_succ hestep
    have hae : ∀ n, a n ≤ e n := by
      intro n
      cases n with
      | zero => rw [he0]; exact (hg _ _ hb (haD 0)).2.2
      | succ n => rw [hesucc n]; exact (hg _ _ (heD n) (haD (n + 1))).2.2
    have hegt : ∀ n : ℕ, M - 1 / (n + 1) < f (e n) := fun n =>
      lt_of_lt_of_le (hagt n) (hfmono _ _ (hae n))
    have hebdd : BddAbove (Set.range e) := by
      refine ⟨u, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hu (heD n)
    obtain ⟨t, htlub, htτ⟩ := hsup e hemono hebdd
    have hft : f t = M := hval e heD hegt t htτ
    -- `s ≤ t` and `τ(t − s) = 0`, so `t = s` by faithfulness
    have hst : s ≤ t := hslub.2 (by
      rintro _ ⟨n, rfl⟩
      exact le_trans (hae n) (htlub.1 ⟨n, rfl⟩))
    have hzero : (t : A) - (s : A) = 0 := by
      refine hfaith _ (sub_nonneg.mpr (Subtype.coe_le_coe.mpr hst)) ?_
      rw [map_sub, hτre t, hτre s, hft, hfs, sub_self]
    have hts : t = s := by
      refine Subtype.ext ?_
      exact sub_eq_zero.mp hzero
    calc b ≤ e 0 := by rw [he0]; exact (hg _ _ hb (haD 0)).2.1
      _ ≤ t := htlub.1 ⟨0, rfl⟩
      _ = s := hts
  refine ⟨s, ⟨hub, ?_⟩, ?_, ?_⟩
  · intro v hv
    exact hslub.2 (by rintro _ ⟨n, rfl⟩; exact hv (haD n))
  · rintro _ ⟨d, hd, rfl⟩
    show (τ (d : A) : ℂ) ≤ τ (s : A)
    rw [hτre d, hτre s, hfs]
    exact RCLike.ofReal_le_ofReal.mpr (hfle d hd)
  · intro z hz
    have hz₀ : τ (d₀ : A) ≤ z := hz ⟨d₀, hd₀, rfl⟩
    have hzim : z.im = 0 := by
      have h := Complex.le_def.mp hz₀
      rw [← h.2]
      exact positiveLinearMap_im_eq_zero τ d₀.2
    rw [hτre s, hfs, Complex.le_def]
    refine ⟨?_, by rw [Complex.ofReal_im, hzim]⟩
    refine hM.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    have hcd := Complex.le_def.mp (hz ⟨d, hd, rfl⟩)
    simp only [hτre d, Complex.ofReal_re] at hcd
    exact hcd.1

/-- **51VII**.2 as a private lemma, so that **51VII**.1 below can use it (the
faithfulness clause of Kadison's definition needs `τ` to be *normal* before
it is an np-functional). -/
private theorem countably_normal_normal (τ : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, 0 ≤ a → τ a = 0 → a = 0)
    (hsup : ∀ a : ℕ → selfAdjoint A, Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint A, IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => τ (a n : A)) (τ (s : A))) :
    PreservesDirSups ⇑τ := by
  intro D s hne hdir hlub
  obtain ⟨s', hs', hτ⟩ := countably_normal_key τ hfaith hsup D hne hdir ⟨s, hlub.1⟩
  rwa [hs'.unique hlub] at hτ

/-- **51VII** (vn.tex:1581, Proposition), part 1: a C*-algebra `A` with a
faithful positive functional `τ` such that every bounded ascending sequence
of self-adjoint elements has a supremum preserved by `τ` is a von Neumann
algebra. -/
theorem vna_of_faithful_countably_normal_1 (τ : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, 0 ≤ a → τ a = 0 → a = 0)
    (hsup : ∀ a : ℕ → selfAdjoint A, Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint A, IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => τ (a n : A)) (τ (s : A))) :
    VonNeumannAlgebra A where
  isLUB_of_bddAbove_directed D hne hdir hbdd :=
    let ⟨s, hs, _⟩ := countably_normal_key τ hfaith hsup D hne hdir hbdd
    ⟨s, hs⟩
  np_faithful a ha h :=
    hfaith a ha (h ⟨τ, countably_normal_normal τ hfaith hsup⟩)

/-- **51VII** (vn.tex:1581, Proposition), part 2: such a `τ` is moreover
normal. -/
theorem vna_of_faithful_countably_normal_2 (τ : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, 0 ≤ a → τ a = 0 → a = 0)
    (hsup : ∀ a : ℕ → selfAdjoint A, Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint A, IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => τ (a n : A)) (τ (s : A))) :
    PreservesDirSups ⇑τ :=
  countably_normal_normal τ hfaith hsup

variable (X : Type u) [MeasurableSpace X] in
/-- A function `X → ℂ` on a measure(able) space that is measurable and
bounded — a member of the thesis's `𝓛^∞(X)` (vn.tex 51II). -/
def IsBoundedMeasurable (f : X → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

/-! ### The construction of `L^∞(X)` for **51IX**

Mathlib has no C*-algebra of bounded measurable functions modulo equality
almost everywhere: `MeasureTheory.Lp E ∞ μ` is only a Banach space, and
`X →ₘ[μ] ℂ` (`MeasureTheory.AEEqFun`) carries `Mul`, `Star` and `Module ℂ`
but *no ring structure at all* (distributivity is missing).  This block
builds one, as the star subalgebra `LinftySub μ` of essentially bounded
elements of `X →ₘ[μ] ℂ`, and then proves 51IX by feeding integration to
**51VII** `vna_of_faithful_countably_normal_1/2` — which is exactly the
thesis's own proof (vn.tex:1638 is a corollary of vn.tex:1581).

Everything here is `private`, and the algebraic instances on `X →ₘ[μ] ℂ`
are `local`, so no instance on Mathlib's `AEEqFun` leaks out of this section.
What *is* exported, at the end of the section and by name, is the result:
`Linfty μ` — the type `L^∞(X, μ)` itself, with its von Neumann algebra
structure, the quotient map `Linfty.mk` and integration — so that **54XI**'s
`f ↦ f°` has an object to land in (`cvn_faithful_6`). -/

section LinftyConstruction

namespace LinftyConstruction

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-! ### The commutative ring structure on `X →ₘ[μ] ℂ` -/

attribute [local simp] AEEqFun.mk_mul_mk AEEqFun.mk_add_mk AEEqFun.mk_eq_mk
  AEEqFun.comp_mk AEEqFun.smul_mk

@[instance_reducible] private noncomputable def aeCommRing (μ : Measure X) :
    CommRing (X →ₘ[μ] ℂ) where
  __ := (inferInstance : AddCommGroup (X →ₘ[μ] ℂ))
  __ := (inferInstance : CommMonoid (X →ₘ[μ] ℂ))
  left_distrib a b c := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    induction b using AEEqFun.induction_on with | _ g hg =>
    induction c using AEEqFun.induction_on with | _ h hh =>
    simp [mul_add]
  right_distrib a b c := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    induction b using AEEqFun.induction_on with | _ g hg =>
    induction c using AEEqFun.induction_on with | _ h hh =>
    simp [add_mul]
  zero_mul a := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    change (0 : X →ₘ[μ] ℂ) * _ = _
    rw [show (0 : X →ₘ[μ] ℂ) = AEEqFun.mk 0 aestronglyMeasurable_const from rfl]
    simp
  mul_zero a := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    change _ * (0 : X →ₘ[μ] ℂ) = _
    rw [show (0 : X →ₘ[μ] ℂ) = AEEqFun.mk 0 aestronglyMeasurable_const from rfl]
    simp

attribute [local instance] aeCommRing

@[instance_reducible] private noncomputable def aeAlgebra (μ : Measure X) :
    Algebra ℂ (X →ₘ[μ] ℂ) :=
  Algebra.ofModule
    (fun r x y => by
      induction x using AEEqFun.induction_on with | _ f hf =>
      induction y using AEEqFun.induction_on with | _ g hg =>
      simp)
    (fun r x y => by
      induction x using AEEqFun.induction_on with | _ f hf =>
      induction y using AEEqFun.induction_on with | _ g hg =>
      simp)

attribute [local instance] aeAlgebra

@[instance_reducible] private noncomputable def aeStarRing (μ : Measure X) :
    StarRing (X →ₘ[μ] ℂ) where
  star_involutive := star_star
  star_mul a b := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    induction b using AEEqFun.induction_on with | _ g hg =>
    change AEEqFun.comp _ continuous_star _
      = AEEqFun.comp _ continuous_star _ * AEEqFun.comp _ continuous_star _
    simp only [AEEqFun.comp_mk, AEEqFun.mk_mul_mk, AEEqFun.mk_eq_mk, Function.comp_def,
      RCLike.star_def]
    exact Filter.EventuallyEq.of_eq (funext fun x => by simp [map_mul, mul_comm])
  star_add a b := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    induction b using AEEqFun.induction_on with | _ g hg =>
    change AEEqFun.comp _ continuous_star _
      = AEEqFun.comp _ continuous_star _ + AEEqFun.comp _ continuous_star _
    simp only [AEEqFun.comp_mk, AEEqFun.mk_add_mk, AEEqFun.mk_eq_mk, Function.comp_def,
      RCLike.star_def]
    exact Filter.EventuallyEq.of_eq (funext fun x => by simp [map_add])

attribute [local instance] aeStarRing

private theorem aeStarModule (μ : Measure X) :
    StarModule ℂ (X →ₘ[μ] ℂ) where
  star_smul r a := by
    induction a using AEEqFun.induction_on with | _ f hf =>
    change AEEqFun.comp _ continuous_star _ = _ • AEEqFun.comp _ continuous_star _
    simp only [AEEqFun.comp_mk, AEEqFun.smul_mk, AEEqFun.mk_eq_mk, Function.comp_def,
      RCLike.star_def]
    exact Filter.EventuallyEq.of_eq (funext fun x => by simp [map_mul])

attribute [local instance] aeStarModule

noncomputable example : Module ℂ (X →ₘ[μ] ℂ) := inferInstance
noncomputable example : StarRing (X →ₘ[μ] ℂ) := inferInstance
noncomputable example : StarModule ℂ (X →ₘ[μ] ℂ) := inferInstance
noncomputable example : Algebra ℂ (X →ₘ[μ] ℂ) := inferInstance

/-! ### essential-supremum estimates -/

private theorem essSup_mul_le (f g : X → ℂ) :
    eLpNormEssSup (f * g) μ ≤ eLpNormEssSup f μ * eLpNormEssSup g μ := by
  rw [eLpNormEssSup_eq_essSup_enorm]
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [ENNReal.ae_le_essSup (fun x => ‖f x‖ₑ) (μ := μ),
    ENNReal.ae_le_essSup (fun x => ‖g x‖ₑ) (μ := μ)] with x h1 h2
  simp only [Pi.mul_apply, enorm_mul]
  exact mul_le_mul' h1 h2

private theorem enn_half_mul (u : ℝ≥0∞) : u ^ (1/2 : ℝ) * u ^ (1/2 : ℝ) = u := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

private theorem enn_sq (u : ℝ≥0∞) : u * u = u ^ (2 : ℝ) := by
  rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]

private theorem enn_le_half {u v : ℝ≥0∞} (h : u * u ≤ v) : u ≤ v ^ (1/2 : ℝ) := by
  have := ENNReal.rpow_le_rpow h (z := (1/2 : ℝ)) (by norm_num)
  calc u = (u * u) ^ (1/2 : ℝ) := by
        rw [enn_sq, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ v ^ (1/2 : ℝ) := this

private theorem essSup_mul_self_ge (f : X → ℂ) :
    eLpNormEssSup f μ * eLpNormEssSup f μ ≤ eLpNormEssSup (fun x => star (f x) * f x) μ := by
  set c := eLpNormEssSup (fun x => star (f x) * f x) μ with hc
  have key : eLpNormEssSup f μ ≤ c ^ (1/2 : ℝ) := by
    rw [eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ENNReal.ae_le_essSup (fun x => ‖star (f x) * f x‖ₑ) (μ := μ)] with x hx
    refine enn_le_half ?_
    rw [hc, eLpNormEssSup_eq_essSup_enorm]
    have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by simp
    simpa only [enorm_mul, hs] using hx
  calc eLpNormEssSup f μ * eLpNormEssSup f μ ≤ c ^ (1/2 : ℝ) * c ^ (1/2 : ℝ) :=
        mul_le_mul' key key
    _ = c := enn_half_mul c

/-! ### `L^∞(X)` as a star subalgebra of `X →ₘ[μ] ℂ` -/

variable (μ) in
private def LinftySub : StarSubalgebra ℂ (X →ₘ[μ] ℂ) where
  carrier := {f | eLpNormEssSup (f : X → ℂ) μ < ∞}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at *
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hf hg)
    refine le_trans (le_of_eq (eLpNormEssSup_congr_ae (AEEqFun.coeFn_mul f g))) ?_
    exact essSup_mul_le _ _
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at *
    refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.2 ⟨hf, hg⟩)
    refine le_trans (le_of_eq (eLpNormEssSup_congr_ae (AEEqFun.coeFn_add f g))) ?_
    rw [eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ENNReal.ae_le_essSup (fun x => ‖f x‖ₑ) (μ := μ),
      ENNReal.ae_le_essSup (fun x => ‖g x‖ₑ) (μ := μ)] with x h1 h2
    exact le_trans (enorm_add_le _ _) (add_le_add h1 h2)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [eLpNormEssSup_congr_ae (AEEqFun.coeFn_zero (β := ℂ) (μ := μ))]
    simp
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    refine lt_of_le_of_lt (le_of_eq (eLpNormEssSup_congr_ae (AEEqFun.coeFn_one (β := ℂ) (μ := μ)))) ?_
    exact lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound (C := ‖(1:ℂ)‖ₑ)
      (by filter_upwards with x; simp)) (by simp)
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq]
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound (C := ‖r‖ₑ) ?_) (by simp)
    have : (algebraMap ℂ (X →ₘ[μ] ℂ) r) = r • (1 : X →ₘ[μ] ℂ) := by
      rw [Algebra.algebraMap_eq_smul_one]
    rw [this]
    filter_upwards [AEEqFun.coeFn_smul r (1 : X →ₘ[μ] ℂ), AEEqFun.coeFn_one (β := ℂ) (μ := μ)] with x h1 h2
    simp [h1, h2]
  star_mem' {f} hf := by
    simp only [Set.mem_ofPred_eq] at *
    refine lt_of_le_of_lt (le_of_eq (eLpNormEssSup_congr_ae (AEEqFun.coeFn_star f))) ?_
    rw [show eLpNormEssSup (star (f : X → ℂ)) μ = eLpNormEssSup (f : X → ℂ) μ from ?_]
    · exact hf
    · rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
      congr 1
      funext x
      simp

/-! ### `L^∞(X)` as a commutative C*-algebra -/

private theorem linfty_mem {f : X →ₘ[μ] ℂ} (hf : f ∈ LinftySub μ) :
    eLpNormEssSup (f : X → ℂ) μ < ∞ := hf

variable (μ) in
private def toLpHom : ↥(LinftySub μ) →+ Lp ℂ ∞ μ where
  toFun a := ⟨(a : X →ₘ[μ] ℂ), by
    rw [Lp.mem_Lp_iff_eLpNorm_lt_top, eLpNorm_exponent_top]
    exact linfty_mem a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem toLpHom_injective : Function.Injective (toLpHom μ) :=
  fun _ _ h => Subtype.ext (congrArg Subtype.val h)

private theorem toLpHom_surjective : Function.Surjective (toLpHom μ) := by
  rintro ⟨f, hf⟩
  refine ⟨⟨f, ?_⟩, rfl⟩
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top, eLpNorm_exponent_top] at hf
  exact hf

private noncomputable instance : NormedAddCommGroup ↥(LinftySub μ) :=
  NormedAddCommGroup.induced _ _ (toLpHom μ) toLpHom_injective

private theorem norm_linfty (a : ↥(LinftySub μ)) :
    ‖a‖ = (eLpNormEssSup ((a : X →ₘ[μ] ℂ) : X → ℂ) μ).toReal := by
  change ‖toLpHom μ a‖ = _
  rw [Lp.norm_def, eLpNorm_exponent_top]
  rfl

private noncomputable instance : NormedCommRing ↥(LinftySub μ) where
  __ := (inferInstance : NormedAddCommGroup ↥(LinftySub μ))
  __ := (inferInstance : CommRing ↥(LinftySub μ))
  norm_mul_le a b := by
    rw [norm_linfty, norm_linfty, norm_linfty, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (by exact ENNReal.mul_ne_top (linfty_mem a.2).ne (linfty_mem b.2).ne) ?_
    refine le_trans (le_of_eq (eLpNormEssSup_congr_ae ?_)) (essSup_mul_le _ _)
    exact AEEqFun.coeFn_mul (a : X →ₘ[μ] ℂ) (b : X →ₘ[μ] ℂ)

private theorem fact_one_le_top : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩

attribute [local instance] fact_one_le_top

private theorem isometry_toLpHom : Isometry (toLpHom (X := X) μ) :=
  AddMonoidHomClass.isometry_of_norm (toLpHom μ) (fun _ => rfl)

private instance : CompleteSpace ↥(LinftySub μ) := by
  refine (isometry_toLpHom (X := X) (μ := μ)).isUniformInducing.completeSpace ?_
  rw [(toLpHom_surjective (X := X) (μ := μ)).range_eq]
  exact isComplete_univ

private instance : CStarRing ↥(LinftySub μ) where
  norm_mul_self_le a := by
    rw [norm_linfty, norm_linfty, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (linfty_mem (star a * a).2).ne ?_
    refine le_trans (essSup_mul_self_ge _) (le_of_eq (eLpNormEssSup_congr_ae ?_))
    filter_upwards [AEEqFun.coeFn_mul (star a : X →ₘ[μ] ℂ) (a : X →ₘ[μ] ℂ),
      AEEqFun.coeFn_star (a : X →ₘ[μ] ℂ)] with x h1 h2
    rw [show ((star a * a : ↥(LinftySub μ)) : X →ₘ[μ] ℂ)
        = star (a : X →ₘ[μ] ℂ) * (a : X →ₘ[μ] ℂ) from rfl, h1]
    simp [h2]

private noncomputable instance : NormedAlgebra ℂ ↥(LinftySub μ) where
  __ := (inferInstance : Algebra ℂ ↥(LinftySub μ))
  norm_smul_le r a := by
    have h1 : eLpNormEssSup (((r • a : ↥(LinftySub μ)) : X →ₘ[μ] ℂ) : X → ℂ) μ
        ≤ ‖r‖ₑ * eLpNormEssSup ((a : X →ₘ[μ] ℂ) : X → ℂ) μ := by
      rw [show ((r • a : ↥(LinftySub μ)) : X →ₘ[μ] ℂ) = r • (a : X →ₘ[μ] ℂ) from rfl,
        eLpNormEssSup_congr_ae (AEEqFun.coeFn_smul r (a : X →ₘ[μ] ℂ))]
      exact eLpNormEssSup_const_smul_le
    rw [norm_linfty, norm_linfty]
    refine le_trans (ENNReal.toReal_mono ?_ h1) ?_
    · exact ENNReal.mul_ne_top (by simp) (linfty_mem a.2).ne
    · rw [ENNReal.toReal_mul]
      simp

private noncomputable instance : CommCStarAlgebra ↥(LinftySub μ) where

/-! ### The a.e.-pointwise order -/

/-- Notation-free access to a representative of an element of `L^∞(X)`. -/
private noncomputable def rep (a : ↥(LinftySub μ)) : X → ℂ := ((a : X →ₘ[μ] ℂ) : X → ℂ)

private theorem rep_add (a b : ↥(LinftySub μ)) : rep (a + b) =ᵐ[μ] rep a + rep b :=
  AEEqFun.coeFn_add (a : X →ₘ[μ] ℂ) (b : X →ₘ[μ] ℂ)

private theorem rep_mul (a b : ↥(LinftySub μ)) : rep (a * b) =ᵐ[μ] rep a * rep b :=
  AEEqFun.coeFn_mul (a : X →ₘ[μ] ℂ) (b : X →ₘ[μ] ℂ)

private theorem rep_star (a : ↥(LinftySub μ)) : rep (star a) =ᵐ[μ] star (rep a) :=
  AEEqFun.coeFn_star (a : X →ₘ[μ] ℂ)

private theorem rep_zero : rep (0 : ↥(LinftySub μ)) =ᵐ[μ] 0 :=
  AEEqFun.coeFn_zero (β := ℂ) (μ := μ)

private theorem rep_one : rep (1 : ↥(LinftySub μ)) =ᵐ[μ] 1 :=
  AEEqFun.coeFn_one (β := ℂ) (μ := μ)

private theorem rep_smul (r : ℂ) (a : ↥(LinftySub μ)) : rep (r • a) =ᵐ[μ] r • rep a :=
  AEEqFun.coeFn_smul r (a : X →ₘ[μ] ℂ)

private theorem rep_injective {a b : ↥(LinftySub μ)} (h : rep a =ᵐ[μ] rep b) : a = b :=
  Subtype.ext (AEEqFun.ext h)

private theorem rep_essSup_lt_top (a : ↥(LinftySub μ)) : eLpNormEssSup (rep a) μ < ∞ :=
  linfty_mem a.2

noncomputable example : PartialOrder ↥(LinftySub μ) := inferInstance

private theorem linfty_le_iff {a b : ↥(LinftySub μ)} :
    a ≤ b ↔ ∀ᵐ x ∂μ, rep a x ≤ rep b x := by
  rw [← Subtype.coe_le_coe, ← AEEqFun.coeFn_le]
  rfl

private theorem continuous_csqrt : Continuous (fun z : ℂ => ((Real.sqrt z.re : ℝ) : ℂ)) := by
  fun_prop

/-- The pointwise square root of a nonnegative element of `L^∞(X)`. -/
private noncomputable def sqrtLinfty (a : ↥(LinftySub μ)) : ↥(LinftySub μ) := by
  refine ⟨AEEqFun.comp (fun z : ℂ => ((Real.sqrt z.re : ℝ) : ℂ)) continuous_csqrt
    (a : X →ₘ[μ] ℂ), ?_⟩
  change eLpNormEssSup _ μ < ∞
  rw [eLpNormEssSup_congr_ae (AEEqFun.coeFn_comp _ _ _)]
  refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_enorm_bound
    (C := (eLpNormEssSup (rep a) μ) ^ (1/2 : ℝ)) ?_) ?_
  · filter_upwards [ENNReal.ae_le_essSup (fun x => ‖rep a x‖ₑ) (μ := μ)] with x hx
    refine enn_le_half ?_
    have h1 : ‖((Real.sqrt (rep a x).re : ℝ) : ℂ)‖ₑ * ‖((Real.sqrt (rep a x).re : ℝ) : ℂ)‖ₑ
        ≤ ‖rep a x‖ₑ := by
      have h2 : ‖((Real.sqrt (rep a x).re : ℝ) : ℂ)‖ = Real.sqrt (rep a x).re := by
        simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h3 : Real.sqrt (rep a x).re * Real.sqrt (rep a x).re ≤ ‖rep a x‖ := by
        rcases le_or_gt (rep a x).re 0 with h | h
        · simp [Real.sqrt_eq_zero_of_nonpos h]
        · rw [Real.mul_self_sqrt h.le]
          exact (Complex.abs_re_le_norm _).trans' (le_abs_self _)
      calc ‖((Real.sqrt (rep a x).re : ℝ) : ℂ)‖ₑ * ‖((Real.sqrt (rep a x).re : ℝ) : ℂ)‖ₑ
          = ENNReal.ofReal (Real.sqrt (rep a x).re * Real.sqrt (rep a x).re) := by
            rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ofReal_norm, h2]
        _ ≤ ‖rep a x‖ₑ := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal h3
    exact h1.trans hx
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (rep_essSup_lt_top a).ne

private theorem rep_sub (a b : ↥(LinftySub μ)) : rep (a - b) =ᵐ[μ] rep a - rep b :=
  AEEqFun.coeFn_sub (a : X →ₘ[μ] ℂ) (b : X →ₘ[μ] ℂ)

private theorem rep_sqrt (a : ↥(LinftySub μ)) :
    rep (sqrtLinfty a) =ᵐ[μ] fun x => ((Real.sqrt (rep a x).re : ℝ) : ℂ) :=
  AEEqFun.coeFn_comp _ continuous_csqrt _

private theorem star_sqrt_mul_sqrt {a : ↥(LinftySub μ)} (ha : ∀ᵐ x ∂μ, 0 ≤ rep a x) :
    star (sqrtLinfty a) * sqrtLinfty a = a := by
  refine rep_injective ?_
  filter_upwards [rep_mul (star (sqrtLinfty a)) (sqrtLinfty a), rep_star (sqrtLinfty a),
    rep_sqrt a, ha] with x h1 h2 h3 h4
  rw [h1]
  simp only [Pi.mul_apply, h2, Pi.star_apply, h3]
  rw [Complex.le_def] at h4
  simp only [Complex.zero_re, Complex.zero_im] at h4
  rw [show star ((Real.sqrt (rep a x).re : ℝ) : ℂ) = ((Real.sqrt (rep a x).re : ℝ) : ℂ) by simp,
    ← Complex.ofReal_mul, Real.mul_self_sqrt h4.1]
  simp [Complex.ext_iff, ← h4.2]

private theorem star_mul_self_nonneg_rep (s : ↥(LinftySub μ)) :
    ∀ᵐ x ∂μ, 0 ≤ rep (star s * s) x := by
  filter_upwards [rep_mul (star s) s, rep_star s] with x h1 h2
  rw [h1]
  simp only [Pi.mul_apply, h2, Pi.star_apply, RCLike.star_def]
  rw [mul_comm, Complex.mul_conj]
  simp [Complex.le_def, Complex.normSq_nonneg]

private noncomputable instance : StarOrderedRing ↥(LinftySub μ) :=
  StarOrderedRing.of_le_iff <| by
    intro x y
    constructor
    · intro h
      refine ⟨sqrtLinfty (y - x), ?_⟩
      have hnn : ∀ᵐ t ∂μ, 0 ≤ rep (y - x) t := by
        filter_upwards [linfty_le_iff.mp h, rep_sub y x] with t h1 h2
        rw [h2]
        simpa using sub_nonneg.mpr h1
      rw [star_sqrt_mul_sqrt hnn]
      ring
    · rintro ⟨s, rfl⟩
      rw [linfty_le_iff]
      filter_upwards [rep_add x (star s * s), star_mul_self_nonneg_rep s] with t h1 h2
      rw [h1]
      simpa using h2

/-! ### The quotient map `q` -/

private theorem memLp_of_isBoundedMeasurable {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    MemLp f ∞ μ := by
  obtain ⟨hm, C, hC⟩ := hf
  exact memLp_top_of_bound hm.aestronglyMeasurable C (.of_forall hC)

open Classical in
variable (μ) in
/-- The quotient map from bounded measurable functions to `L^∞(X)`. -/
private noncomputable def qmap (f : X → ℂ) : ↥(LinftySub μ) :=
  if h : MemLp f ∞ μ then ⟨AEEqFun.mk f h.1, by
    change eLpNormEssSup _ μ < ∞
    rw [eLpNormEssSup_congr_ae (AEEqFun.coeFn_mk f h.1), ← eLpNorm_exponent_top]
    exact h.2⟩
  else 0

private theorem rep_qmap {f : X → ℂ} (hf : MemLp f ∞ μ) : rep (qmap μ f) =ᵐ[μ] f := by
  rw [qmap]
  simp only [hf, ↓reduceDIte]
  exact AEEqFun.coeFn_mk f hf.1

private theorem qmap_eq_iff {f : X → ℂ} (hf : MemLp f ∞ μ) {y : ↥(LinftySub μ)} :
    qmap μ f = y ↔ f =ᵐ[μ] rep y := by
  constructor
  · rintro rfl; exact (rep_qmap hf).symm
  · rintro h; exact rep_injective ((rep_qmap hf).trans h)

private theorem qmap_surjective (y : ↥(LinftySub μ)) :
    ∃ f, IsBoundedMeasurable X f ∧ qmap μ f = y := by
  set g : X → ℂ := rep y with hg
  have hgm : Measurable g := (AEEqFun.stronglyMeasurable (y : X →ₘ[μ] ℂ)).measurable
  set M : ℝ := (eLpNormEssSup g μ).toReal with hM
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  have hbdd : ∀ᵐ x ∂μ, ‖g x‖ ≤ M := by
    filter_upwards [ENNReal.ae_le_essSup (fun x => ‖g x‖ₑ) (μ := μ)] with x hx
    have := ENNReal.toReal_mono (rep_essSup_lt_top y).ne hx
    simpa using this
  refine ⟨fun x => if ‖g x‖ ≤ M then g x else 0, ⟨?_, M, ?_⟩, ?_⟩
  · exact Measurable.ite (measurableSet_le hgm.norm measurable_const) hgm measurable_const
  · intro x
    by_cases h : ‖g x‖ ≤ M <;> simp [h, hMnn]
  · refine (qmap_eq_iff ?_).mpr ?_
    · refine memLp_top_of_bound ?_ M (.of_forall ?_)
      · exact (Measurable.ite (measurableSet_le hgm.norm measurable_const) hgm
          measurable_const).aestronglyMeasurable
      · intro x; by_cases h : ‖g x‖ ≤ M <;> simp [h, hMnn]
    · filter_upwards [hbdd] with x hx
      simp only [hx, ↓reduceIte]
      exact congrFun hg x

/-! ### Integration -/

private theorem memLp_rep (a : ↥(LinftySub μ)) : MemLp (rep a) ∞ μ :=
  ⟨AEEqFun.aestronglyMeasurable _, by rw [eLpNorm_exponent_top]; exact rep_essSup_lt_top a⟩

variable [IsFiniteMeasure μ]

private theorem integrable_rep (a : ↥(LinftySub μ)) : Integrable (rep a) μ :=
  (memLp_rep a).integrable le_top

/-- Integration on `L^∞(X)`. -/
private noncomputable def tauFun (a : ↥(LinftySub μ)) : ℂ := ∫ x, rep a x ∂μ

omit [IsFiniteMeasure μ] in
private theorem tauFun_congr {a : ↥(LinftySub μ)} {f : X → ℂ} (h : rep a =ᵐ[μ] f) :
    tauFun a = ∫ x, f x ∂μ := integral_congr_ae h

private noncomputable def tauMap : (↥(LinftySub μ)) →ₚ[ℂ] ℂ where
  toFun := tauFun
  map_add' a b := by
    rw [tauFun, tauFun, tauFun, integral_congr_ae (rep_add a b)]
    exact integral_add (integrable_rep a) (integrable_rep b)
  map_smul' r a := by
    rw [RingHom.id_apply, tauFun, tauFun, integral_congr_ae (rep_smul r a), smul_eq_mul]
    simpa using integral_smul r (rep a)
  monotone' a b hab := by
    refine integral_mono_ae (integrable_rep a) (integrable_rep b) ?_
    exact linfty_le_iff.mp hab

private theorem tau_re (a : ↥(LinftySub μ)) : (tauFun a).re = ∫ x, (rep a x).re ∂μ :=
  (ContinuousLinearMap.integral_comp_comm Complex.reCLM (integrable_rep a)).symm

private theorem tau_im (a : ↥(LinftySub μ)) : (tauFun a).im = ∫ x, (rep a x).im ∂μ :=
  (ContinuousLinearMap.integral_comp_comm Complex.imCLM (integrable_rep a)).symm

private theorem tau_ofReal (a : ↥(LinftySub μ)) (ha : ∀ᵐ x ∂μ, (rep a x).im = 0) :
    tauFun a = ((∫ x, (rep a x).re ∂μ : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, tau_re]
  · rw [Complex.ofReal_im, tau_im, integral_congr_ae (g := fun _ => (0:ℝ)) ha, integral_zero]

private theorem tau_faithful (a : ↥(LinftySub μ)) (ha : 0 ≤ a) (h : tauFun a = 0) : a = 0 := by
  have hnn : ∀ᵐ x ∂μ, 0 ≤ rep a x := by
    filter_upwards [linfty_le_iff.mp ha, rep_zero (μ := μ)] with x h1 h2
    rwa [h2] at h1
  have hre : ∀ᵐ x ∂μ, (0:ℝ) ≤ (rep a x).re := by
    filter_upwards [hnn] with x hx using (Complex.le_def.mp hx).1
  have hint : ∫ x, (rep a x).re ∂μ = 0 := by
    have := congrArg Complex.re h
    rwa [tau_re, Complex.zero_re] at this
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hre
    ((integrable_rep a).re)).mp hint
  refine rep_injective ?_
  filter_upwards [hnn, hzero, rep_zero (μ := μ)] with x h1 h2 h3
  rw [h3]
  refine Complex.ext ?_ ?_
  · simpa using h2
  · simpa using ((Complex.le_def.mp h1).2).symm

/-! ### Bounded ascending sequences -/

omit [IsFiniteMeasure μ] in
private theorem rep_ae_bound (a : ↥(LinftySub μ)) : ∀ᵐ x ∂μ, ‖rep a x‖ ≤ ‖a‖ := by
  filter_upwards [ENNReal.ae_le_essSup (fun x => ‖rep a x‖ₑ) (μ := μ)] with x hx
  rw [norm_linfty]
  have h2 := ENNReal.toReal_mono (rep_essSup_lt_top a).ne hx
  rw [show ‖rep a x‖ₑ.toReal = ‖rep a x‖ by simp] at h2
  exact h2

omit [IsFiniteMeasure μ] in
private theorem isSelfAdjoint_rep {a : ↥(LinftySub μ)} (ha : IsSelfAdjoint a) :
    ∀ᵐ x ∂μ, (rep a x).im = 0 := by
  have h : rep (star a) = rep a := congrArg rep ha.star_eq
  filter_upwards [rep_star a] with x h1
  have h2 : star (rep a x) = rep a x := by rw [← Pi.star_apply, ← h1, h]
  exact Complex.conj_eq_iff_im.mp h2

private theorem isLUB_ofReal_seq {f : ℕ → ℝ} {r : ℝ} (h : IsLUB (Set.range f) r) :
    IsLUB (Set.range fun n => ((f n : ℝ) : ℂ)) (r : ℂ) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    rw [Complex.le_def]
    exact ⟨by simpa using h.1 ⟨n, rfl⟩, by simp⟩
  · rintro z hz
    have h0 := Complex.le_def.mp (hz ⟨0, rfl⟩)
    rw [Complex.le_def]
    refine ⟨h.2 ?_, by simpa using h0.2⟩
    rintro _ ⟨n, rfl⟩
    simpa using (Complex.le_def.mp (hz ⟨n, rfl⟩)).1

private theorem exists_isLUB_seq (a : ℕ → selfAdjoint ↥(LinftySub μ))
    (hmono : Monotone a) (hbdd : BddAbove (Set.range a)) :
    ∃ s : selfAdjoint ↥(LinftySub μ), IsLUB (Set.range a) s ∧
      IsLUB (Set.range fun n => tauFun (a n : ↥(LinftySub μ)))
        (tauFun (s : ↥(LinftySub μ))) := by
  classical
  obtain ⟨b, hb⟩ := hbdd
  set g : ℕ → X → ℂ := fun n => rep ((a n : ↥(LinftySub μ))) with hgdef
  have hgm : ∀ n, Measurable (g n) :=
    fun n => (AEEqFun.stronglyMeasurable ((a n : ↥(LinftySub μ)) : X →ₘ[μ] ℂ)).measurable
  have him : ∀ᵐ x ∂μ, ∀ n, (g n x).im = 0 := by
    rw [ae_all_iff]; intro n; exact isSelfAdjoint_rep (a n).2
  have hbim : ∀ᵐ x ∂μ, (rep ((b : ↥(LinftySub μ))) x).im = 0 := isSelfAdjoint_rep b.2
  have hstep : ∀ᵐ x ∂μ, ∀ n, (g n x).re ≤ (g (n+1) x).re := by
    rw [ae_all_iff]; intro n
    filter_upwards [linfty_le_iff.mp (Subtype.coe_le_coe.mpr (hmono (Nat.le_succ n)))] with x hx
    exact (Complex.le_def.mp hx).1
  have hupper : ∀ᵐ x ∂μ, ∀ n, (g n x).re ≤ (rep ((b : ↥(LinftySub μ))) x).re := by
    rw [ae_all_iff]; intro n
    filter_upwards [linfty_le_iff.mp (Subtype.coe_le_coe.mpr (hb ⟨n, rfl⟩))] with x hx
    exact (Complex.le_def.mp hx).1
  set h : X → ℝ := fun x => ⨆ n, (g n x).re with hhdef
  have hhm : Measurable h := Measurable.iSup (fun n => by
    simpa [RCLike.re_to_complex] using (hgm n).re)
  -- the good set
  have hgood : ∀ᵐ x ∂μ, (Monotone fun n => (g n x).re) ∧
      BddAbove (Set.range fun n => (g n x).re) := by
    filter_upwards [hstep, hupper] with x h1 h2
    exact ⟨monotone_nat_of_le_succ h1, ⟨(rep ((b : ↥(LinftySub μ))) x).re, by
      rintro _ ⟨n, rfl⟩; exact h2 n⟩⟩
  have hbound : ∀ᵐ x ∂μ, ‖(h x : ℂ)‖ ≤ ‖(a 0 : ↥(LinftySub μ))‖ + ‖(b : ↥(LinftySub μ))‖ := by
    filter_upwards [hgood, hupper, rep_ae_bound ((a 0 : ↥(LinftySub μ))),
      rep_ae_bound ((b : ↥(LinftySub μ)))] with x hx h2 h3 h4
    have hlow : (g 0 x).re ≤ h x := le_ciSup hx.2 0
    have hhigh : h x ≤ (rep ((b : ↥(LinftySub μ))) x).re := ciSup_le (fun n => h2 n)
    have e1 : (g 0 x).re ≥ -‖(a 0 : ↥(LinftySub μ))‖ := by
      have := (Complex.abs_re_le_norm (g 0 x)).trans h3
      cases abs_le.mp this with | intro l r => exact l
    have e2 : (rep ((b : ↥(LinftySub μ))) x).re ≤ ‖(b : ↥(LinftySub μ))‖ :=
      (Complex.abs_re_le_norm _).trans' (le_abs_self _) |>.trans h4
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · have : -‖(a 0 : ↥(LinftySub μ))‖ ≤ h x := e1.trans hlow
      linarith [norm_nonneg ((b : ↥(LinftySub μ)))]
    · have : h x ≤ ‖(b : ↥(LinftySub μ))‖ := hhigh.trans e2
      linarith [norm_nonneg ((a 0 : ↥(LinftySub μ)))]
  have hmem : MemLp (fun x => (h x : ℂ)) ∞ μ :=
    memLp_top_of_bound (by fun_prop) _ hbound
  set s0 : ↥(LinftySub μ) := qmap μ (fun x => (h x : ℂ)) with hs0
  have hreps : rep s0 =ᵐ[μ] fun x => (h x : ℂ) := rep_qmap hmem
  have hsa : IsSelfAdjoint s0 := by
    refine rep_injective ?_
    filter_upwards [rep_star s0, hreps] with x h1 h2
    rw [h1]
    simp [h2]
  refine ⟨⟨s0, hsa⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨n, rfl⟩
    rw [← Subtype.coe_le_coe, linfty_le_iff]
    filter_upwards [hgood, hreps, him] with x hx h2 h3
    rw [h2, Complex.le_def]
    exact ⟨le_ciSup hx.2 n, by rw [Complex.ofReal_im]; exact h3 n⟩
  · intro c hc
    rw [← Subtype.coe_le_coe, linfty_le_iff]
    have hcn : ∀ n, ∀ᵐ x ∂μ, (g n x).re ≤ (rep ((c : ↥(LinftySub μ))) x).re := by
      intro n
      filter_upwards [linfty_le_iff.mp (Subtype.coe_le_coe.mpr (hc ⟨n, rfl⟩))] with x hx
      exact (Complex.le_def.mp hx).1
    rw [← ae_all_iff] at hcn
    filter_upwards [hcn, hreps, isSelfAdjoint_rep c.2] with x h1 h2 h3
    rw [h2, Complex.le_def]
    exact ⟨ciSup_le h1, by simp [h3]⟩
  · -- the integral part
    have hint : ∀ n, Integrable (fun x => (g n x).re) μ := fun n => by
      simpa [RCLike.re_to_complex] using (integrable_rep ((a n : ↥(LinftySub μ)))).re
    have hinth : Integrable h μ := by
      refine Integrable.congr (f := fun x => (rep s0 x).re) ?_ ?_
      · simpa [RCLike.re_to_complex] using (integrable_rep s0).re
      · filter_upwards [hreps] with x hx using by simp [hx]
    have htend : Tendsto (fun n => ∫ x, (g n x).re ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) := by
      refine integral_tendsto_of_tendsto_of_monotone hint hinth ?_ ?_
      · filter_upwards [hgood] with x hx using hx.1
      · filter_upwards [hgood] with x hx using tendsto_atTop_ciSup hx.1 hx.2
    have hmono2 : Monotone fun n => ∫ x, (g n x).re ∂μ := by
      intro m n hmn
      refine integral_mono_ae (hint m) (hint n) ?_
      filter_upwards [linfty_le_iff.mp (Subtype.coe_le_coe.mpr (hmono hmn))] with x hx
      exact (Complex.le_def.mp hx).1
    have hlub := isLUB_of_tendsto_atTop hmono2 htend
    have heq1 : ∀ n, tauFun ((a n : ↥(LinftySub μ))) = ((∫ x, (g n x).re ∂μ : ℝ) : ℂ) :=
      fun n => tau_ofReal _ (by filter_upwards [him] with x hx using hx n)
    have heq2 : tauFun s0 = ((∫ x, h x ∂μ : ℝ) : ℂ) := by
      rw [tau_ofReal s0 (by filter_upwards [hreps] with x hx using by simp [hx])]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hreps] with x hx using by simp [hx]
    simp only [heq1, heq2]
    exact isLUB_ofReal_seq hlub

/-! ### `q` is a ∗-homomorphism -/

omit [IsFiniteMeasure μ] in
private theorem bm_add {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f + g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.add hgm, Cf + Cg, fun x => (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩

omit [IsFiniteMeasure μ] in
private theorem bm_mul {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f * g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, max Cf 0 * max Cg 0, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul ((hCf x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

omit [IsFiniteMeasure μ] in
private theorem bm_star {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (star f) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  exact ⟨(Complex.continuous_conj.measurable).comp hfm, Cf, fun x => by simpa using hCf x⟩

omit [IsFiniteMeasure μ] in
private theorem bm_one : IsBoundedMeasurable X (1 : X → ℂ) :=
  ⟨measurable_const, 1, fun x => by simp⟩

omit [IsFiniteMeasure μ] in
private theorem qmap_add {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : qmap μ (f + g) = qmap μ f + qmap μ g := by
  refine rep_injective ?_
  filter_upwards [rep_qmap (memLp_of_isBoundedMeasurable (bm_add hf hg)),
    rep_add (qmap μ f) (qmap μ g), rep_qmap (memLp_of_isBoundedMeasurable hf),
    rep_qmap (memLp_of_isBoundedMeasurable hg)] with x h1 h2 h3 h4
  rw [h1, h2]
  simp [h3, h4]

omit [IsFiniteMeasure μ] in
private theorem qmap_mul {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : qmap μ (f * g) = qmap μ f * qmap μ g := by
  refine rep_injective ?_
  filter_upwards [rep_qmap (memLp_of_isBoundedMeasurable (bm_mul hf hg)),
    rep_mul (qmap μ f) (qmap μ g), rep_qmap (memLp_of_isBoundedMeasurable hf),
    rep_qmap (memLp_of_isBoundedMeasurable hg)] with x h1 h2 h3 h4
  rw [h1, h2]
  simp [h3, h4]

omit [IsFiniteMeasure μ] in
private theorem qmap_star {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    qmap μ (star f) = star (qmap μ f) := by
  refine rep_injective ?_
  filter_upwards [rep_qmap (memLp_of_isBoundedMeasurable (bm_star hf)),
    rep_star (qmap μ f), rep_qmap (memLp_of_isBoundedMeasurable hf)] with x h1 h2 h3
  rw [h1, h2]
  simp [h3]

omit [IsFiniteMeasure μ] in
private theorem qmap_one : qmap μ (1 : X → ℂ) = 1 := by
  refine rep_injective ?_
  filter_upwards [rep_qmap (memLp_of_isBoundedMeasurable (bm_one (X := X))),
    rep_one (μ := μ)] with x h1 h2
  rw [h1, h2]

omit [IsFiniteMeasure μ] in
private theorem qmap_eq_zero_iff {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    qmap μ f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [qmap_eq_iff (memLp_of_isBoundedMeasurable hf)]
  constructor
  · intro h; filter_upwards [h, rep_zero (μ := μ)] with x h1 h2 using by rw [h1, h2]
  · intro h; filter_upwards [h, rep_zero (μ := μ)] with x h1 h2 using by rw [h1, h2]

omit [IsFiniteMeasure μ] in
private theorem tau_qmap {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    tauFun (qmap μ f) = ∫ x, f x ∂μ :=
  tauFun_congr (rep_qmap (memLp_of_isBoundedMeasurable hf))


omit [IsFiniteMeasure μ] in
private theorem bm_smul (z : ℂ) {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (z • f) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.const_smul z, ‖z‖ * max C 0, fun x => ?_⟩
  have hx : ‖(z • f) x‖ = ‖z‖ * ‖f x‖ := by simp
  rw [hx]
  exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg z)

omit [IsFiniteMeasure μ] in
private theorem qmap_smul (z : ℂ) {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    qmap μ (z • f) = z • qmap μ f := by
  refine rep_injective ?_
  filter_upwards [rep_qmap (memLp_of_isBoundedMeasurable (bm_smul z hf)),
    rep_smul z (qmap μ f), rep_qmap (memLp_of_isBoundedMeasurable hf)] with x h1 h2 h3
  rw [h1, h2]
  simp [h3]

omit [IsFiniteMeasure μ] in
private theorem qmap_congr {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) (h : f =ᵐ[μ] g) : qmap μ f = qmap μ g :=
  (qmap_eq_iff (memLp_of_isBoundedMeasurable hf)).mpr
    (h.trans (rep_qmap (memLp_of_isBoundedMeasurable hg)).symm)

end LinftyConstruction

/-! ### `L^∞(X, μ)` as a carrier: the public interface

Everything above is `private`, and the algebraic instances on `X →ₘ[μ] ℂ`
are `local`, so the ring structure Mathlib declines to put on `AEEqFun` does
not leave this section.  What follows exports the *result* — the type
`L^∞(X, μ)` itself, with its commutative von Neumann algebra structure, the
quotient map `f ↦ [f]` and integration — under public names, so that
**54XI**'s `f ↦ f°` has an object to land in (`cvn_faithful_6` below, which
until this interface existed could only be rendered in presentation form).

It is a small named interface and nothing more.  `Linfty μ` is a *reducible*
abbreviation for `↥(LinftySub μ)`, declared here, inside the section, so the
`local` instances are baked into it once and for all: no instance on
`X →ₘ[μ] ℂ` is published, and typeclass search downstream never has to look
for one — it unfolds `Linfty μ` and finds the closed instances on
`↥(LinftySub μ)` proved above.  The rest of the block stays private. -/

section LinftyCarrier

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

attribute [local instance] LinftyConstruction.aeCommRing LinftyConstruction.aeAlgebra
  LinftyConstruction.aeStarRing LinftyConstruction.aeStarModule
  LinftyConstruction.fact_one_le_top

variable (μ) in
/-- `L^∞(X, μ)`, the carrier: the essentially bounded elements of
`X →ₘ[μ] ℂ`, that is, the bounded measurable functions `X → ℂ` modulo
equality `μ`-almost everywhere.  It is a commutative C*-algebra, and a von
Neumann algebra as soon as `μ` is finite (`Linfty.instVonNeumannAlgebra`),
which is **51IX** `Linfty_vn` with the existential unpacked. -/
abbrev Linfty : Type u := ↥(LinftyConstruction.LinftySub μ)

namespace Linfty

variable (μ) in
/-- The quotient map `𝓛^∞(X, μ) → L^∞(X, μ)`, `f ↦ [f]`: the thesis's
`f ↦ f°` before its domain is cut down to the continuous functions. -/
noncomputable def mk (f : X → ℂ) : Linfty μ := LinftyConstruction.qmap μ f

theorem mk_add {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : mk μ (f + g) = mk μ f + mk μ g :=
  LinftyConstruction.qmap_add hf hg

theorem mk_smul (z : ℂ) {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    mk μ (z • f) = z • mk μ f :=
  LinftyConstruction.qmap_smul z hf

theorem mk_mul {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : mk μ (f * g) = mk μ f * mk μ g :=
  LinftyConstruction.qmap_mul hf hg

theorem mk_star {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    mk μ (star f) = star (mk μ f) :=
  LinftyConstruction.qmap_star hf

theorem mk_one : mk μ (1 : X → ℂ) = 1 :=
  LinftyConstruction.qmap_one

/-- The kernel of `f ↦ [f]` is exactly the `μ`-a.e.-zero functions. -/
theorem mk_eq_zero_iff {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    mk μ f = 0 ↔ f =ᵐ[μ] 0 :=
  LinftyConstruction.qmap_eq_zero_iff hf

/-- `f ↦ [f]` identifies exactly the functions that agree `μ`-almost
everywhere: this is the injectivity half of **51IX**'s quotient. -/
theorem mk_eq_iff {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : mk μ f = mk μ g ↔ f =ᵐ[μ] g := by
  rw [show mk μ f = LinftyConstruction.qmap μ f from rfl,
    show mk μ g = LinftyConstruction.qmap μ g from rfl,
    LinftyConstruction.qmap_eq_iff (LinftyConstruction.memLp_of_isBoundedMeasurable hf)]
  constructor
  · exact fun h => h.trans
      (LinftyConstruction.rep_qmap (LinftyConstruction.memLp_of_isBoundedMeasurable hg))
  · exact fun h => h.trans
      (LinftyConstruction.rep_qmap (LinftyConstruction.memLp_of_isBoundedMeasurable hg)).symm

theorem mk_congr {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) (h : f =ᵐ[μ] g) : mk μ f = mk μ g :=
  LinftyConstruction.qmap_congr hf hg h

/-- `f ↦ [f]` is onto: every element of `L^∞(X, μ)` is the class of a
genuinely bounded measurable function. -/
theorem mk_surjective (y : Linfty μ) :
    ∃ f, IsBoundedMeasurable X f ∧ mk μ f = y :=
  LinftyConstruction.qmap_surjective y

section Finite

variable [IsFiniteMeasure μ]

/-- Integration `a ↦ ∫ a dμ` on `L^∞(X, μ)`. -/
noncomputable def integral (a : Linfty μ) : ℂ := LinftyConstruction.tauFun a

omit [IsFiniteMeasure μ] in
theorem integral_mk {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    integral (mk μ f) = ∫ x, f x ∂μ :=
  LinftyConstruction.tau_qmap hf

theorem integral_faithful (a : Linfty μ) (ha : 0 ≤ a) (h : integral a = 0) :
    a = 0 :=
  LinftyConstruction.tau_faithful a ha h

/-- **51IX** (`Linfty-vn`, vn.tex:1638) for the carrier: `L^∞(X, μ)` is a von
Neumann algebra.  This is the `hvn` of `Linfty_vn`'s proof, lifted out. -/
instance instVonNeumannAlgebra : VonNeumannAlgebra (Linfty μ) := by
  have hfaith : ∀ a : Linfty μ, 0 ≤ a → LinftyConstruction.tauMap a = 0 → a = 0 :=
    LinftyConstruction.tau_faithful
  exact vna_of_faithful_countably_normal_1 LinftyConstruction.tauMap hfaith
    LinftyConstruction.exists_isLUB_seq

/-- **51IX**: integration is a (faithful, by `integral_faithful`)
np-functional on `L^∞(X, μ)`. -/
noncomputable def integralNP : NPFunctional (Linfty μ) := by
  have hfaith : ∀ a : Linfty μ, 0 ≤ a → LinftyConstruction.tauMap a = 0 → a = 0 :=
    LinftyConstruction.tau_faithful
  exact ⟨LinftyConstruction.tauMap,
    vna_of_faithful_countably_normal_2 LinftyConstruction.tauMap hfaith
      LinftyConstruction.exists_isLUB_seq⟩

theorem coe_integralNP : ⇑(integralNP (μ := μ)) = integral (μ := μ) := rfl

end Finite

end Linfty

end LinftyCarrier

end LinftyConstruction

/-- **51IX** (`Linfty-vn`, vn.tex:1638, Corollary): for a finite complete
measure space `X`, the C*-algebra `L^∞(X)` — bounded measurable functions
modulo equality almost everywhere — is a commutative von Neumann algebra on
which integration is a faithful normal positive functional.  (Since Mathlib
has no C*-algebra of classes of bounded measurable functions, `L^∞(X)` is
rendered as an existentially quantified commutative von Neumann algebra `𝒜`
with a quotient map `q` from `𝓛^∞(X)`.  The witness is not anonymous: it is
`Linfty μ` with `Linfty.mk`, exported above, and `Linfty.instVonNeumannAlgebra`
is this statement's `VonNeumannAlgebra 𝒜` clause on the nose.) -/
theorem Linfty_vn (X : Type u) [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (hμ : μ.IsComplete) :
    ∃ (𝒜 : Type u) (_ : CommCStarAlgebra 𝒜) (_ : PartialOrder 𝒜)
      (_ : StarOrderedRing 𝒜) (q : (X → ℂ) → 𝒜) (τ : 𝒜 → ℂ),
      VonNeumannAlgebra 𝒜 ∧
      -- `q` is a surjective miu-map on `𝓛^∞(X)` with kernel the a.e.-null
      -- functions.  (ℂ-homogeneity is part of "miu": it was omitted until
      -- 2026-09-02, QUESTIONS A9, now closed, and is restored under the D1 ruling that
      -- added the same clause to `IsLinftyOf`.)
      (∀ y : 𝒜, ∃ f, IsBoundedMeasurable X f ∧ q f = y) ∧
      (∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
        q (f + g) = q f + q g ∧ q (f * g) = q f * q g ∧
          q (star f) = star (q f)) ∧
      (∀ (z : ℂ) f, IsBoundedMeasurable X f → q (z • f) = z • q f) ∧
      q 1 = 1 ∧
      (∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0)) ∧
      -- integration descends to a faithful normal positive functional:
      (∃ τ' : NPFunctional 𝒜, ⇑τ' = τ) ∧
      (∀ y : 𝒜, 0 ≤ y → τ y = 0 → y = 0) ∧
      (∀ f, IsBoundedMeasurable X f → τ (q f) = ∫ x, f x ∂μ) := by
  open LinftyConstruction in
  have hfaith : ∀ a : ↥(LinftySub μ), 0 ≤ a → tauMap a = 0 → a = 0 := tau_faithful
  have hsup : ∀ a : ℕ → selfAdjoint ↥(LinftySub μ), Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint ↥(LinftySub μ), IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => tauMap (a n : ↥(LinftySub μ)))
          (tauMap (s : ↥(LinftySub μ))) := exists_isLUB_seq
  have hvn : VonNeumannAlgebra ↥(LinftySub μ) :=
    vna_of_faithful_countably_normal_1 tauMap hfaith hsup
  refine ⟨↥(LinftySub μ), inferInstance, inferInstance, inferInstance, qmap μ, tauFun,
    hvn, qmap_surjective, ?_, fun z f hf => qmap_smul z hf, qmap_one,
    fun f hf => qmap_eq_zero_iff hf,
    ⟨⟨tauMap, vna_of_faithful_countably_normal_2 tauMap hfaith hsup⟩, rfl⟩,
    hfaith, fun f hf => tau_qmap hf⟩
  exact fun f g hf hg => ⟨qmap_add hf hg, qmap_mul hf hg, qmap_star hf⟩

end Measure

/-! ## Parsec 520 (`classification-cvn`): meagre subsets

**52I** (vn.tex:1648): plan of the classification — nothing to formalize.

**52II** (`meagre`, vn.tex:1711, Definition): *meagre* subsets — a subset
contained in a countable increasing union of closed sets with empty
interior — coincide with Mathlib's `IsMeagre` (complement in the `residual`
filter); we use Mathlib's notion.  The derived notions `≈` and *almost
clopen* are defined here.

**52IIIa** (vn.tex:1767): meagreness vs. negligibility — narrative. -/

section Meagre

variable {X : Type*} [TopologicalSpace X]

/-- **52II** (`meagre`, vn.tex:1711, Definition), part 2: `A ≈ B` iff the
symmetric difference `A ∪ B \ A ∩ B` is meagre. -/
def MeagreEquiv (s t : Set X) : Prop := IsMeagre (s ∆ t)

/-- **52II** (`meagre`, vn.tex:1711, Definition), part 3: a subset is
**almost clopen** when it is `≈` to a clopen subset. -/
def AlmostClopen (s : Set X) : Prop := ∃ C : Set X, IsClopen C ∧ MeagreEquiv s C

/-! `≈` is an equivalence relation (used silently throughout vn.tex §520–540). -/

@[refl] theorem MeagreEquiv.refl (s : Set X) : MeagreEquiv s s := by
  simpa [MeagreEquiv] using (IsMeagre.empty : IsMeagre (∅ : Set X))

@[symm] theorem MeagreEquiv.symm {s t : Set X} (h : MeagreEquiv s t) :
    MeagreEquiv t s := by
  rwa [MeagreEquiv, symmDiff_comm]

theorem MeagreEquiv.trans {s t u : Set X} (h : MeagreEquiv s t)
    (h' : MeagreEquiv t u) : MeagreEquiv s u :=
  IsMeagre.mono (symmDiff_triangle s t u) (h.union h')

/-- **52III** (`meagre-basic`, vn.tex:1737, Exercise), part 1: a countable
union of meagre sets is meagre.  (Mathlib: `IsMeagre` is closed under
countable unions.) -/
theorem meagre_basic_1 (s : ℕ → Set X) (h : ∀ n, IsMeagre (s n)) :
    IsMeagre (⋃ n, s n) :=
  isMeagre_iUnion h

/-- **52III** (`meagre-basic`, vn.tex:1737, Exercise), part 2: a subset of a
meagre set is meagre. -/
theorem meagre_basic_2 (s t : Set X) (hst : s ⊆ t) (h : IsMeagre t) :
    IsMeagre s :=
  h.mono hst

/-- **52III** (`meagre-basic`, vn.tex:1737, Exercise), part 3:
`closure U ≈ U` for every open `U`. -/
theorem meagre_basic_3 (U : Set X) (hU : IsOpen U) :
    MeagreEquiv (closure U) U := by
  -- the thesis's hint: `closure U \ U` is closed with empty interior
  have heq : closure U ∆ U = closure U \ U := by
    rw [Set.symmDiff_def]
    simp [Set.sdiff_eq_empty.mpr (subset_closure : U ⊆ closure U)]
  have hclosed : IsClosed (closure U \ U) := isClosed_closure.sdiff hU
  refine (IsNowhereDense.isMeagre ?_).mono heq.subset
  rw [hclosed.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxU : x ∈ closure U := (interior_subset hx).1
  obtain ⟨y, hyi, hyU⟩ := mem_closure_iff.mp hxU _ isOpen_interior hx
  exact (interior_subset hyi).2 hyU

/-- **52III** (`meagre-basic`, vn.tex:1737, Exercise), part 4:
`⋃ₙ Aₙ ≈ ⋃ₙ Bₙ` when `Aₙ ≈ Bₙ` for all `n`. -/
theorem meagre_basic_4 (s t : ℕ → Set X) (h : ∀ n, MeagreEquiv (s n) (t n)) :
    MeagreEquiv (⋃ n, s n) (⋃ n, t n) := by
  refine IsMeagre.mono ?_ (isMeagre_iUnion h)
  intro x hx
  rw [Set.mem_symmDiff] at hx
  simp only [Set.mem_iUnion, not_exists] at hx
  obtain ⟨⟨n, hn⟩, hnot⟩ | ⟨⟨n, hn⟩, hnot⟩ := hx <;>
    exact Set.mem_iUnion.mpr ⟨n, by rw [Set.mem_symmDiff]; tauto⟩

/-- **52III** (`meagre-basic`, vn.tex:1737, Exercise), part 5:
`A \ B ≈ A' \ B'` when `A ≈ A'` and `B ≈ B'`. -/
theorem meagre_basic_5 (s s' t t' : Set X) (hs : MeagreEquiv s s')
    (ht : MeagreEquiv t t') : MeagreEquiv (s \ t) (s' \ t') := by
  refine IsMeagre.mono ?_ (hs.union ht)
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_union] at hx ⊢
  tauto

/-- **52III** (`meagre-basic`, vn.tex:1737, Exercise), part 6: unions and
differences of almost clopen sets are almost clopen. -/
theorem meagre_basic_6 (s t : Set X) (hs : AlmostClopen s)
    (ht : AlmostClopen t) : AlmostClopen (s ∪ t) ∧ AlmostClopen (s \ t) := by
  obtain ⟨C, hC, hsC⟩ := hs
  obtain ⟨D, hD, htD⟩ := ht
  refine ⟨⟨C ∪ D, hC.union hD, ?_⟩, ⟨C \ D, hC.diff hD, meagre_basic_5 _ _ _ _ hsC htD⟩⟩
  refine IsMeagre.mono ?_ (hsC.union htD)
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_union] at hx ⊢
  tauto

end Meagre

/-- **52IIIb** (vn.tex:1776, Example): there is a meagre subset of `[0,1]`
of Lebesgue measure `1`.

The thesis's own construction: enumerate the rationals as `q₀, q₁, …` and
put `Bₘ = ⋃ₙ (qₙ − 2⁻ⁿ/2(m+1), qₙ + 2⁻ⁿ/2(m+1))`.  Each `Bₘ` is open and
dense (it contains every rational) and has Lebesgue measure at most
`2/(m+1)`, so `B = ⋂ₘ Bₘ` is negligible while remaining comeagre; hence
`[0,1] \ B` is meagre of measure `1`.  (The thesis intersects each `Bₘ`
with `[0,1]` and enumerates only the rationals *in* `[0,1]`; neither
restriction is needed, and dropping them keeps the estimate the same.) -/
theorem meagre_full_measure :
    ∃ s : Set ℝ, s ⊆ Set.Icc 0 1 ∧ IsMeagre s ∧ volume s = 1 := by
  classical
  set q : ℕ → ℝ := fun n => ((Denumerable.eqv ℚ).symm n : ℚ) with hq
  set r : ℕ → ℕ → ℝ := fun m n => (1 / 2 : ℝ) ^ n / (2 * (m + 1)) with hr
  set U : ℕ → Set ℝ := fun m => ⋃ n, Set.Ioo (q n - r m n) (q n + r m n) with hU
  have hrpos : ∀ m n, 0 < r m n := by
    intro m n
    rw [hr]
    positivity
  have hUopen : ∀ m, IsOpen (U m) := fun m => isOpen_iUnion fun n => isOpen_Ioo
  have hQU : ∀ m, Set.range ((↑) : ℚ → ℝ) ⊆ U m := by
    rintro m _ ⟨s, rfl⟩
    refine Set.mem_iUnion.mpr ⟨Denumerable.eqv ℚ s, ?_⟩
    have hqs : q (Denumerable.eqv ℚ s) = (s : ℝ) := by
      rw [hq]
      simp
    rw [Set.mem_Ioo, hqs]
    exact ⟨by linarith [hrpos m (Denumerable.eqv ℚ s)],
      by linarith [hrpos m (Denumerable.eqv ℚ s)]⟩
  have hUvol : ∀ m : ℕ, volume (U m) ≤ ENNReal.ofReal (2 / (m + 1)) := by
    intro m
    have hsum : Summable (fun n : ℕ => 2 * r m n) := by
      rw [hr]
      simp only
      exact ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const
        (2 * (m + 1))).mul_left 2
    calc volume (U m) ≤ ∑' n, volume (Set.Ioo (q n - r m n) (q n + r m n)) :=
          measure_iUnion_le _
      _ = ∑' n, ENNReal.ofReal (2 * r m n) := by
          refine tsum_congr fun n => ?_
          rw [Real.volume_Ioo]
          congr 1
          ring
      _ = ENNReal.ofReal (∑' n, 2 * r m n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
      _ = ENNReal.ofReal (2 / (m + 1)) := by
          congr 1
          rw [hr]
          simp only
          rw [tsum_mul_left, tsum_div_const,
            tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          field_simp
          norm_num
  have hBres : (⋂ m : ℕ, U m) ∈ residual ℝ :=
    countable_iInter_mem.mpr fun m =>
      residual_of_dense_open (hUopen m) (Rat.denseRange_cast.mono (hQU m))
  have hB0 : volume (⋂ m : ℕ, U m) = 0 := by
    have hle : ∀ m : ℕ, volume (⋂ m : ℕ, U m) ≤ ENNReal.ofReal (2 / (m + 1)) :=
      fun m => le_trans (measure_mono (Set.iInter_subset U m)) (hUvol m)
    have htend : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (2 / ((m : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      rw [← ENNReal.ofReal_zero]
      refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
      have h1 : Filter.Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1)))
          Filter.atTop (nhds (2 * 0)) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul 2
      rw [mul_zero] at h1
      refine h1.congr fun m => ?_
      ring
    exact le_antisymm (ge_of_tendsto htend (Filter.Eventually.of_forall hle)) zero_le
  refine ⟨Set.Icc 0 1 \ (⋂ m : ℕ, U m), Set.sdiff_subset, ?_, ?_⟩
  · exact Filter.mem_of_superset hBres fun x hx hx' => hx'.2 hx
  · rw [measure_sdiff_null hB0, Real.volume_Icc]
    norm_num

/-! ## Parsec 530: extremal disconnectedness of the spectrum -/

section Gelfand

variable (A : Type*) [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open WeakDual

/-- **53II** (`ngelfand`, vn.tex:1807, Exercise), part 1: for a commutative
von Neumann algebra `A`, the C*-algebra `C(spec A)` of continuous functions
on its spectrum is a (commutative) von Neumann algebra. -/
theorem ngelfand_vna [VonNeumannAlgebra A] :
    VonNeumannAlgebra C(characterSpace ℂ A, ℂ) :=
  vonNeumannAlgebra_of_starAlgEquiv (gelfandStarTransform A)

/-- **53II** (`ngelfand`, vn.tex:1807, Exercise), part 2: the Gelfand
representation `γ_A : A → C(spec A)` (Mathlib: `gelfandStarTransform`), an
miu-isomorphism by cstar.tex 27XXVII, is normal, hence an
nmiu-isomorphism. -/
theorem ngelfand_normal [VonNeumannAlgebra A] :
    PreservesDirSups ⇑(gelfandStarTransform A) :=
  starAlgEquiv_preservesDirSups (gelfandStarTransform A)

/-- **53III** (`vn-spectrum-extremally-disconnected`, vn.tex:1821,
Proposition): the spectrum of a commutative von Neumann algebra is
extremally disconnected: the closure of every open set is open. -/
theorem vn_spectrum_extremally_disconnected [VonNeumannAlgebra A] :
    ExtremallyDisconnected (characterSpace ℂ A) := by
  have hvna := ngelfand_vna A
  refine ⟨fun U hU => ?_⟩
  -- the real-to-complex embedding of continuous functions, into the
  -- self-adjoint part
  set rc : C(characterSpace ℂ A, ℝ) → selfAdjoint C(characterSpace ℂ A, ℂ) :=
    fun f => ⟨⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
      selfAdjoint.mem_iff.mpr (by ext x; simp)⟩ with hrc
  have hrcapp : ∀ (f : C(characterSpace ℂ A, ℝ)) (x : characterSpace ℂ A),
      ((rc f : C(characterSpace ℂ A, ℂ))) x = (f x : ℂ) := fun f x => rfl
  -- `D = {f ∈ C(spec A) : 0 ≤ f ≤ 1, f = 0 off U}`, a cofinal subset of the
  -- thesis's `{f : f ≤ 1_U}`
  set D : Set (selfAdjoint C(characterSpace ℂ A, ℂ)) :=
    {g | (∀ x, 0 ≤ (g : C(characterSpace ℂ A, ℂ)) x ∧
            (g : C(characterSpace ℂ A, ℂ)) x ≤ 1) ∧
          ∀ x ∉ U, (g : C(characterSpace ℂ A, ℂ)) x = 0} with hDdef
  have hzero : (0 : selfAdjoint C(characterSpace ℂ A, ℂ)) ∈ D :=
    ⟨fun _ => ⟨le_rfl, zero_le_one⟩, fun _ _ => rfl⟩
  have hne : D.Nonempty := ⟨0, hzero⟩
  set one' : selfAdjoint C(characterSpace ℂ A, ℂ) :=
    ⟨1, selfAdjoint.mem_iff.mpr (IsSelfAdjoint.one _)⟩ with hone'
  have hone : ∀ g ∈ D, g ≤ one' := fun g hg =>
    Subtype.coe_le_coe.mp (ContinuousMap.le_def.mpr fun x => (hg.1 x).2)
  have hbdd : BddAbove D := ⟨one', hone⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    intro g hg h hh
    have hcont : Continuous fun x => max ((g : C(characterSpace ℂ A, ℂ)) x).re
        ((h : C(characterSpace ℂ A, ℂ)) x).re :=
      (Complex.continuous_re.comp (g : C(characterSpace ℂ A, ℂ)).continuous).max
        (Complex.continuous_re.comp (h : C(characterSpace ℂ A, ℂ)).continuous)
    set mR : C(characterSpace ℂ A, ℝ) := ⟨_, hcont⟩ with hmR
    have hmRapp : ∀ x, mR x = max ((g : C(characterSpace ℂ A, ℂ)) x).re
        ((h : C(characterSpace ℂ A, ℂ)) x).re := fun _ => rfl
    refine ⟨rc mR, ⟨fun x => ?_, fun x hx => ?_⟩, ?_, ?_⟩
    · rw [hrcapp, hmRapp]
      refine ⟨?_, ?_⟩
      · exact_mod_cast le_max_of_le_left (Complex.nonneg_iff.mp (hg.1 x).1).1
      · have h1 := (Complex.le_def.mp (hg.1 x).2).1
        have h2 := (Complex.le_def.mp (hh.1 x).2).1
        rw [Complex.one_re] at h1 h2
        exact_mod_cast max_le h1 h2
    · rw [hrcapp, hmRapp, hg.2 x hx, hh.2 x hx]
      simp
    · refine Subtype.coe_le_coe.mp (ContinuousMap.le_def.mpr fun x => ?_)
      rw [hrcapp, hmRapp]
      exact Complex.le_def.mpr ⟨by simp,
        by simp [← (Complex.nonneg_iff.mp (hg.1 x).1).2]⟩
    · refine Subtype.coe_le_coe.mp (ContinuousMap.le_def.mpr fun x => ?_)
      rw [hrcapp, hmRapp]
      exact Complex.le_def.mpr ⟨by simp,
        by simp [← (Complex.nonneg_iff.mp (hh.1 x).1).2]⟩
  set s : selfAdjoint C(characterSpace ℂ A, ℂ) := dirSup D ⟨hne, hdir, hbdd⟩ with hs
  have hlub : IsLUB D s := isLUB_dirSup D ⟨hne, hdir, hbdd⟩
  have hs0 : ∀ x, 0 ≤ (s : C(characterSpace ℂ A, ℂ)) x := fun x =>
    ContinuousMap.le_def.mp (Subtype.coe_le_coe.mpr (hlub.1 hzero)) x
  have hs1 : ∀ x, (s : C(characterSpace ℂ A, ℂ)) x ≤ 1 := fun x =>
    ContinuousMap.le_def.mp (Subtype.coe_le_coe.mpr (hlub.2 hone)) x
  -- Urysohn: on `U` the supremum is `1`
  have hU1 : ∀ x ∈ U, (s : C(characterSpace ℂ A, ℂ)) x = 1 := by
    intro x hx
    obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_compl_iff.mpr hU) (isClosed_singleton (x := x))
      (Set.disjoint_singleton_right.mpr (by simpa using hx))
    have hmem : rc f ∈ D := by
      refine ⟨fun y => ⟨?_, ?_⟩, fun y hy => ?_⟩
      · rw [hrcapp]; exact_mod_cast (hf01 y).1
      · rw [hrcapp]; exact_mod_cast (hf01 y).2
      · rw [hrcapp, hf0 hy]; simp
    have hle := ContinuousMap.le_def.mp (Subtype.coe_le_coe.mpr (hlub.1 hmem)) x
    rw [hrcapp, hf1 rfl] at hle
    exact le_antisymm (hs1 x) (by exact_mod_cast hle)
  -- off the closure of `U` the supremum is `0`
  have hU0 : ∀ x ∉ closure U, (s : C(characterSpace ℂ A, ℂ)) x = 0 := by
    intro x hx
    obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x)) isClosed_closure
      (Set.disjoint_singleton_left.mpr hx)
    have hub : ∀ g ∈ D, g ≤ rc f := by
      intro g hg
      refine Subtype.coe_le_coe.mp (ContinuousMap.le_def.mpr fun y => ?_)
      rw [hrcapp]
      by_cases hy : y ∈ U
      · rw [hf1 (subset_closure hy)]
        simpa using (hg.1 y).2
      · rw [hg.2 y hy]
        exact_mod_cast (hf01 y).1
    have hle := ContinuousMap.le_def.mp (Subtype.coe_le_coe.mpr (hlub.2 hub)) x
    rw [hrcapp, hf0 rfl] at hle
    exact le_antisymm (by simpa using hle) (hs0 x)
  -- hence `⋁ D` is the indicator of `closure U`, which is therefore open
  have hcl : closure U = (s : C(characterSpace ℂ A, ℂ)) ⁻¹' {z : ℂ | (1 / 2 : ℝ) < z.re} := by
    apply Set.eq_of_subset_of_subset
    · have hclosed : IsClosed {y | (s : C(characterSpace ℂ A, ℂ)) y = 1} :=
        isClosed_eq (s : C(characterSpace ℂ A, ℂ)).continuous continuous_const
      intro x hx
      have hx1 : (s : C(characterSpace ℂ A, ℂ)) x = 1 :=
        hclosed.closure_subset_iff.mpr hU1 hx
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hx1, Complex.one_re]
      norm_num
    · intro x hx
      by_contra hxc
      rw [Set.mem_preimage, Set.mem_ofPred_eq, hU0 x hxc] at hx
      norm_num at hx
  rw [hcl]
  exact IsOpen.preimage (s : C(characterSpace ℂ A, ℂ)).continuous
    (isOpen_lt continuous_const Complex.continuous_re)

end Gelfand

section AlmostClopenSigma

variable (X : Type*) [TopologicalSpace X]

/-- The σ-algebra generated by the almost clopen subsets of a topological
space (auxiliary for **53V** and **54XI**). -/
def almostClopenMS : MeasurableSpace X :=
  MeasurableSpace.generateFrom {s : Set X | AlmostClopen s}

/-- **53V** (vn.tex:1876, Corollary): in an extremally disconnected
topological space the almost clopen subsets form a σ-algebra, i.e. every
member of the σ-algebra they generate is itself almost clopen. -/
theorem almostClopen_sigmaAlgebra [ExtremallyDisconnected X] (s : Set X) :
    MeasurableSet[almostClopenMS X] s ↔ AlmostClopen s := by
  constructor
  · refine MeasurableSpace.generateFrom_induction
      {s : Set X | AlmostClopen s} (fun t _ => AlmostClopen t)
      (fun t ht _ => ht) ⟨∅, isClopen_empty, MeagreEquiv.refl ∅⟩
      (fun t _ ht => ?_) (fun u _ hu => ?_) s
    · -- complements: `tᶜ = X \ t`, and 52III.6 covers differences
      have h := (meagre_basic_6 Set.univ t ⟨Set.univ, isClopen_univ,
        MeagreEquiv.refl _⟩ ht).2
      rwa [← Set.compl_eq_univ_diff] at h
    · -- countable unions: the thesis's argument, using that `X` is
      -- extremally disconnected so `closure (⋃ Cₙ)` is clopen
      choose C hC hUC using hu
      have h1 : MeagreEquiv (⋃ n, u n) (⋃ n, C n) :=
        meagre_basic_4 _ _ hUC
      have hopen : IsOpen (⋃ n, C n) := isOpen_iUnion fun n => (hC n).2
      refine ⟨closure (⋃ n, C n),
        ⟨isClosed_closure, ExtremallyDisconnected.open_closure _ hopen⟩, ?_⟩
      exact h1.trans (meagre_basic_3 _ hopen).symm
  · intro hs
    exact MeasurableSpace.measurableSet_generateFrom hs

end AlmostClopenSigma

/-! ## Parsec 540: Baire category and the classification -/

section Baire

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **54II** (`baire-category-theorem`, vn.tex:1909, Baire category
theorem): a meagre subset of a compact Hausdorff space has empty
interior. -/
theorem baire_category_theorem (s : Set X) (h : IsMeagre s) :
    interior s = ∅ := by
  -- a compact Hausdorff space is locally compact regular, hence Baire
  by_contra hne
  exact not_isMeagre_of_isOpen isOpen_interior (Set.nonempty_iff_ne_empty.mpr hne)
    (h.mono interior_subset)

/-- **54IV** (`approx-closure`, vn.tex:1949, Lemma): for open subsets `U`,
`V` of a compact Hausdorff space:
`U ≈ V ↔ closure U ≈ closure V ↔ closure U = closure V`. -/
theorem approx_closure (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    (MeagreEquiv U V ↔ MeagreEquiv (closure U) (closure V)) ∧
      (MeagreEquiv (closure U) (closure V) ↔ closure U = closure V) := by
  -- `U ≈ closure U` by 52III.3, so only `closure U ≈ closure V → closure U =
  -- closure V` needs an argument, and that is Baire's theorem.
  have hcl : ∀ W : Set X, IsOpen W → MeagreEquiv (closure W) W := fun W hW =>
    meagre_basic_3 W hW
  have key : ∀ W W' : Set X, IsOpen W → IsOpen W' →
      MeagreEquiv (closure W) (closure W') → closure W ⊆ closure W' := by
    intro W W' hW hW' hWW'
    have hsub : W \ closure W' ⊆ closure W ∆ closure W' := by
      intro x hx
      exact Or.inl ⟨subset_closure hx.1, hx.2⟩
    have hopen : IsOpen (W \ closure W') := hW.sdiff isClosed_closure
    have : W \ closure W' = ∅ := by
      rw [← hopen.interior_eq]
      exact baire_category_theorem _ (hWW'.mono hsub)
    have : W ⊆ closure W' := by
      intro x hx
      by_contra hx'
      exact (Set.eq_empty_iff_forall_notMem.mp this x) ⟨hx, hx'⟩
    exact closure_minimal this isClosed_closure
  refine ⟨⟨fun h => ((hcl U hU).trans h).trans (hcl V hV).symm,
    fun h => (((hcl U hU).symm).trans h).trans (hcl V hV)⟩, ⟨fun h => ?_, ?_⟩⟩
  · exact subset_antisymm (key U V hU hV h) (key V U hV hU h.symm)
  · intro h
    rw [h]

/-- **54VI** (vn.tex:1975, Corollary; proof label
`almost-meagre-fundamental`): an almost clopen subset of a compact Hausdorff
space is `≈` to exactly one clopen set. -/
theorem almost_meagre_fundamental (s : Set X) (hs : AlmostClopen s) :
    ∃! C : Set X, IsClopen C ∧ MeagreEquiv s C := by
  obtain ⟨C, hC, hsC⟩ := hs
  refine ⟨C, ⟨hC, hsC⟩, fun C' ⟨hC', hsC'⟩ => ?_⟩
  -- `C' ≈ s ≈ C`, so `C' = C` by `approx_closure`
  have h : MeagreEquiv C' C := hsC'.symm.trans hsC
  have h2 := ((approx_closure C' C hC'.2 hC.2).1.mp h)
  have h3 := (approx_closure C' C hC'.2 hC.2).2.mp h2
  rwa [hC'.1.closure_eq, hC.1.closure_eq] at h3

/-- **54IX** (`open-almost-clopen`, vn.tex:1991, Proposition): a compact
Hausdorff space is extremally disconnected iff every open subset is almost
clopen. -/
theorem open_almost_clopen :
    ExtremallyDisconnected X ↔ ∀ U : Set X, IsOpen U → AlmostClopen U := by
  constructor
  · intro hX U hU
    exact ⟨closure U, ⟨isClosed_closure, hX.open_closure U hU⟩,
      (meagre_basic_3 U hU).symm⟩
  · intro h
    refine ⟨fun U hU => ?_⟩
    obtain ⟨C, hC, hUC⟩ := h U hU
    have h2 := (approx_closure U C hU hC.2).1.mp hUC
    have h3 := (approx_closure U C hU hC.2).2.mp h2
    rw [h3, hC.1.closure_eq]
    exact hC.2

end Baire

/-! ### Machinery for **54XI**: measures on a Stonean space

Everything up to the `CVNFaithful` section below is stated for an arbitrary
**compact Hausdorff extremally disconnected** space `X` carrying an
np-functional `τ` on `C(X, ℂ)` — for **54XI** these are `X = spec 𝒜` (by
**53III**) and `τ = ω ∘ γ_𝒜⁻¹` (by **53II**), but nothing else in the
development uses that.  The vocabulary is: `chi C` (the continuous indicator
of a clopen `C`), `nu τ C = τ(1_C)` (the finitely additive measure on the
clopen sets), `clRep s` (the unique clopen `≈ s` of **54VI**), and finally
`mac`/`macMeasure` (the measure of 54XI itself).  Normality of `τ` enters at
exactly one place, `isLUB_nu`. -/

section Stone

variable {X : Type*} [TopologicalSpace X]

open Classical in
/-- The continuous indicator of a clopen set (`0` on non-clopen sets, so
that it is a total function). -/
noncomputable def chi (C : Set X) : C(X, ℂ) :=
  if h : IsClopen C then ⟨Set.indicator C (fun _ => 1), h.continuous_indicator continuous_const⟩
  else 0

theorem chi_apply {C : Set X} (hC : IsClopen C) (x : X) :
    chi C x = Set.indicator C (fun _ => 1) x := by
  rw [chi, dif_pos hC]; rfl

theorem chi_of_mem {C : Set X} (hC : IsClopen C) {x : X} (hx : x ∈ C) :
    chi C x = 1 := by
  rw [chi_apply hC, Set.indicator_of_mem hx]

theorem chi_of_notMem {C : Set X} (hC : IsClopen C) {x : X} (hx : x ∉ C) :
    chi C x = 0 := by
  rw [chi_apply hC, Set.indicator_of_notMem hx]

theorem chi_isSelfAdjoint (C : Set X) : IsSelfAdjoint (chi C) := by
  rw [isSelfAdjoint_iff]
  ext x
  by_cases h : IsClopen C
  · by_cases hx : x ∈ C
    · simp [ContinuousMap.star_apply, chi_of_mem h hx]
    · simp [ContinuousMap.star_apply, chi_of_notMem h hx]
  · rw [chi, dif_neg h]; simp

/-- The continuous indicator, as an element of the self-adjoint part. -/
noncomputable def chiSA (C : Set X) : selfAdjoint C(X, ℂ) :=
  ⟨chi C, chi_isSelfAdjoint C⟩

@[simp] theorem chiSA_coe (C : Set X) : (chiSA C : C(X, ℂ)) = chi C := rfl

theorem chi_nonneg (C : Set X) : (0 : C(X, ℂ)) ≤ chi C := by
  refine ContinuousMap.le_def.mpr fun x => ?_
  by_cases h : IsClopen C
  · by_cases hx : x ∈ C
    · rw [chi_of_mem h hx]; simp
    · rw [chi_of_notMem h hx]; simp
  · rw [chi, dif_neg h]

theorem chi_mono {C D : Set X} (hC : IsClopen C) (hD : IsClopen D) (h : C ⊆ D) :
    chi C ≤ chi D := by
  refine ContinuousMap.le_def.mpr fun x => ?_
  by_cases hx : x ∈ C
  · rw [chi_of_mem hC hx, chi_of_mem hD (h hx)]
  · rw [chi_of_notMem hC hx]
    by_cases hx' : x ∈ D
    · rw [chi_of_mem hD hx']; simp
    · rw [chi_of_notMem hD hx']

@[simp] theorem chi_empty : chi (∅ : Set X) = 0 := by
  ext x; rw [chi_of_notMem isClopen_empty (Set.notMem_empty x)]; rfl

@[simp] theorem chi_univ : chi (Set.univ : Set X) = 1 := by
  ext x; rw [chi_of_mem isClopen_univ (Set.mem_univ x)]; rfl

theorem chi_union_of_disjoint {C D : Set X} (hC : IsClopen C) (hD : IsClopen D)
    (h : Disjoint C D) : chi (C ∪ D) = chi C + chi D := by
  ext x
  simp only [ContinuousMap.add_apply]
  by_cases hx : x ∈ C
  · rw [chi_of_mem (hC.union hD) (Or.inl hx), chi_of_mem hC hx,
      chi_of_notMem hD (Set.disjoint_left.mp h hx)]
    simp
  · by_cases hx' : x ∈ D
    · rw [chi_of_mem (hC.union hD) (Or.inr hx'), chi_of_mem hD hx',
        chi_of_notMem hC hx]
      simp
    · rw [chi_of_notMem (hC.union hD) (by simp [hx, hx']), chi_of_notMem hC hx,
        chi_of_notMem hD hx']
      simp

theorem chi_eq_zero_iff {C : Set X} (hC : IsClopen C) : chi C = 0 ↔ C = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := chi_of_mem hC hx
    rw [h] at this
    exact one_ne_zero this.symm
  · rintro rfl; exact chi_empty

variable [CompactSpace X] [T2Space X]

/-- In a compact Hausdorff extremally disconnected space the clopen sets form
a base: every neighbourhood of a point contains a clopen neighbourhood. -/
theorem exists_clopen_subset [ExtremallyDisconnected X] {U : Set X} (hU : IsOpen U)
    {x : X} (hx : x ∈ U) : ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ U := by
  obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hx)
  refine ⟨closure (interior t), ⟨isClosed_closure,
    ExtremallyDisconnected.open_closure _ isOpen_interior⟩,
    subset_closure (mem_interior_iff_mem_nhds.mpr ht), ?_⟩
  exact (closure_minimal interior_subset htc).trans htU

omit [CompactSpace X] [T2Space X] in
/-- The interior of a closed set in an extremally disconnected space is
clopen. -/
theorem isClopen_interior [ExtremallyDisconnected X] {F : Set X} (hF : IsClosed F) :
    IsClopen (interior F) := by
  refine ⟨?_, isOpen_interior⟩
  rw [interior_eq_compl_closure_compl]
  exact (ExtremallyDisconnected.open_closure _ hF.isOpen_compl).isClosed_compl

/-- The supremum, in the self-adjoint part of `C(X, ℂ)`, of the indicators of
a family of clopen sets is the indicator of the closure of their union. -/
theorem selfAdjoint_im_eq_zero (g : selfAdjoint C(X, ℂ)) (x : X) :
    ((g : C(X, ℂ)) x).im = 0 := by
  have h : (star (g : C(X, ℂ))) x = (g : C(X, ℂ)) x := by rw [g.2.star_eq]
  rw [ContinuousMap.star_apply, Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h

theorem isLUB_chiSA [ExtremallyDisconnected X] {𝒞 : Set (Set X)}
    (hcl : ∀ C ∈ 𝒞, IsClopen C) (hne : 𝒞.Nonempty) :
    IsLUB (chiSA '' 𝒞) (chiSA (closure (⋃₀ 𝒞))) := by
  have hopen : IsOpen (⋃₀ 𝒞) := isOpen_sUnion fun C hC => (hcl C hC).2
  have hclos : IsClopen (closure (⋃₀ 𝒞)) :=
    ⟨isClosed_closure, ExtremallyDisconnected.open_closure _ hopen⟩
  constructor
  · rintro _ ⟨C, hC, rfl⟩
    exact Subtype.coe_le_coe.mp (chi_mono (hcl C hC) hclos
      ((Set.subset_sUnion_of_mem hC).trans subset_closure))
  · intro g hg
    have hg1 : ∀ y ∈ closure (⋃₀ 𝒞), (1 : ℂ) ≤ (g : C(X, ℂ)) y := by
      have hclosed : IsClosed {y : X | (1 : ℝ) ≤ ((g : C(X, ℂ)) y).re} :=
        isClosed_le continuous_const
          (Complex.continuous_re.comp (g : C(X, ℂ)).continuous)
      have hsub : ⋃₀ 𝒞 ⊆ {y : X | (1 : ℝ) ≤ ((g : C(X, ℂ)) y).re} := by
        rintro y ⟨C, hC, hyC⟩
        have h := ContinuousMap.le_def.mp (Subtype.coe_le_coe.mpr (hg ⟨C, hC, rfl⟩)) y
        rw [chiSA_coe, chi_of_mem (hcl C hC) hyC] at h
        exact (Complex.le_def.mp h).1
      intro y hy
      have := hclosed.closure_subset_iff.mpr hsub hy
      exact Complex.le_def.mpr ⟨by simpa using this,
        by rw [Complex.one_im, selfAdjoint_im_eq_zero g y]⟩
    refine Subtype.coe_le_coe.mp (ContinuousMap.le_def.mpr fun x => ?_)
    by_cases hx : x ∈ closure (⋃₀ 𝒞)
    · rw [chiSA_coe, chi_of_mem hclos hx]
      exact hg1 x hx
    · rw [chiSA_coe, chi_of_notMem hclos hx]
      obtain ⟨C₀, hC₀⟩ := hne
      have h0 := ContinuousMap.le_def.mp (Subtype.coe_le_coe.mpr (hg ⟨C₀, hC₀, rfl⟩)) x
      refine le_trans ?_ h0
      have := ContinuousMap.le_def.mp (chi_nonneg (X := X) C₀) x
      simpa using this

/-! ### The finitely additive measure attached to an np-functional -/

variable [ExtremallyDisconnected X]

/-- The value `ν(C) = τ(1_C)` of an np-functional on the indicator of a
clopen set. -/
noncomputable def nu (τ : NPFunctional C(X, ℂ)) (C : Set X) : ℝ := (τ (chi C)).re

variable (τ : NPFunctional C(X, ℂ))

theorem npFunctional_chi_re (C : Set X) : (τ (chi C) : ℂ) = (nu τ C : ℝ) := by
  rw [nu, Complex.ext_iff]
  exact ⟨by simp, by simp [npFunctional_im_eq_zero τ (chi_isSelfAdjoint C)]⟩

theorem nu_nonneg (C : Set X) : 0 ≤ nu τ C :=
  (Complex.le_def.mp (npFunctional_nonneg τ (chi_nonneg C))).1

theorem nu_mono {C D : Set X} (hC : IsClopen C) (hD : IsClopen D) (h : C ⊆ D) :
    nu τ C ≤ nu τ D :=
  (Complex.le_def.mp (npFunctional_mono τ (chi_mono hC hD h))).1

@[simp] theorem nu_empty : nu τ (∅ : Set X) = 0 := by
  rw [nu, chi_empty, npFunctional_zero]; simp

theorem nu_union {C D : Set X} (hC : IsClopen C) (hD : IsClopen D)
    (h : Disjoint C D) : nu τ (C ∪ D) = nu τ C + nu τ D := by
  rw [nu, nu, nu, chi_union_of_disjoint hC hD h, npFunctional_add]
  simp

theorem nu_finset_biUnion {ι : Type*} (s : Finset ι) {C : ι → Set X}
    (hcl : ∀ i, IsClopen (C i)) (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    nu τ (⋃ i ∈ s, C i) = ∑ i ∈ s, nu τ (C i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hdis : Disjoint (C a) (⋃ i ∈ s, C i) := by
      rw [Set.disjoint_iUnion₂_right]
      exact fun i hi => hdisj a i (by rintro rfl; exact ha hi)
    rw [Finset.set_biUnion_insert, nu_union τ (hcl a)
      (isClopen_biUnion_finset fun i _ => hcl i) hdis, ih, Finset.sum_insert ha]

/-- Normality of `τ`, in the form used for the measure: the value of `ν` on
the closure of the union of an upward directed family of clopen sets is the
supremum of the values on the family. -/
theorem isLUB_nu {𝒞 : Set (Set X)} (hcl : ∀ C ∈ 𝒞, IsClopen C) (hne : 𝒞.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) 𝒞) :
    IsLUB (nu τ '' 𝒞) (nu τ (closure (⋃₀ 𝒞))) := by
  have h1 := isLUB_chiSA hcl hne
  have hdir' : DirectedOn (· ≤ ·) (chiSA '' 𝒞) := by
    rintro _ ⟨C, hC, rfl⟩ _ ⟨D, hD, rfl⟩
    obtain ⟨E, hE, hCE, hDE⟩ := hdir C hC D hD
    exact ⟨chiSA E, ⟨E, hE, rfl⟩,
      Subtype.coe_le_coe.mp (chi_mono (hcl C hC) (hcl E hE) hCE),
      Subtype.coe_le_coe.mp (chi_mono (hcl D hD) (hcl E hE) hDE)⟩
  have h2 := τ.preservesDirSups' (chiSA '' 𝒞) (chiSA (closure (⋃₀ 𝒞)))
    (hne.image _) hdir' h1
  have hreal : ∀ w ∈ (fun d : selfAdjoint C(X, ℂ) => (τ (d : C(X, ℂ)) : ℂ)) '' (chiSA '' 𝒞),
      w.im = 0 := by
    rintro _ ⟨_, ⟨C, _, rfl⟩, rfl⟩
    exact npFunctional_im_eq_zero τ (chi_isSelfAdjoint C)
  have h3 := isLUB_re_of_isLUB hreal h2
  have hset : Complex.re ''
      ((fun d : selfAdjoint C(X, ℂ) => (τ (d : C(X, ℂ)) : ℂ)) '' (chiSA '' 𝒞))
      = nu τ '' 𝒞 := by
    rw [← Set.image_comp, ← Set.image_comp]
    rfl
  rwa [hset] at h3

/-- Countable additivity of `ν` on clopen sets: for a pairwise disjoint
sequence of clopen sets, `ν(closure(⋃ Cₙ)) = ∑ ν(Cₙ)`. -/
theorem hasSum_nu {C : ℕ → Set X} (hcl : ∀ n, IsClopen (C n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    HasSum (fun n => nu τ (C n)) (nu τ (closure (⋃ n, C n))) := by
  classical
  set 𝒞 : Set (Set X) := Set.range (fun F : Finset ℕ => ⋃ i ∈ F, C i) with h𝒞
  have hcl' : ∀ D ∈ 𝒞, IsClopen D := by
    rintro _ ⟨F, rfl⟩; exact isClopen_biUnion_finset fun i _ => hcl i
  have hne : 𝒞.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ⊆ ·) 𝒞 := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    refine ⟨_, ⟨F ∪ G, rfl⟩, ?_, ?_⟩ <;>
      exact Set.biUnion_subset_biUnion_left (by simp)
  have hunion : ⋃₀ 𝒞 = ⋃ n, C n := by
    apply Set.Subset.antisymm
    · rintro x ⟨_, ⟨F, rfl⟩, hx⟩
      obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨_, ⟨({i} : Finset ℕ), rfl⟩, Set.mem_iUnion₂.mpr ⟨i, by simp, hi⟩⟩
  have h := isLUB_nu τ hcl' hne hdir
  rw [hunion] at h
  have himg : nu τ '' 𝒞 = Set.range (fun F : Finset ℕ => ∑ i ∈ F, nu τ (C i)) := by
    rw [h𝒞, ← Set.range_comp]
    congr 1
    funext F
    exact nu_finset_biUnion τ F hcl hdisj
  rw [himg] at h
  exact hasSum_of_isLUB_of_nonneg _ (fun n => nu_nonneg τ (C n)) h

/-! ### The clopen representative of an almost clopen set -/

open Classical in
/-- The unique clopen set `≈` to an almost clopen set (`∅` otherwise). -/
noncomputable def clRep (s : Set X) : Set X :=
  if h : AlmostClopen s then h.choose else ∅

theorem clRep_isClopen (s : Set X) : IsClopen (clRep s) := by
  by_cases h : AlmostClopen s
  · rw [clRep, dif_pos h]; exact h.choose_spec.1
  · rw [clRep, dif_neg h]; exact isClopen_empty

theorem clRep_equiv {s : Set X} (hs : AlmostClopen s) : MeagreEquiv s (clRep s) := by
  rw [clRep, dif_pos hs]; exact hs.choose_spec.2

theorem clRep_eq {s C : Set X} (hC : IsClopen C) (h : MeagreEquiv s C) : clRep s = C := by
  have hs : AlmostClopen s := ⟨C, hC, h⟩
  obtain ⟨D, _, huniq⟩ := almost_meagre_fundamental s hs
  rw [huniq _ ⟨clRep_isClopen s, clRep_equiv hs⟩, huniq _ ⟨hC, h⟩]

theorem clRep_of_isClopen {C : Set X} (hC : IsClopen C) : clRep C = C :=
  clRep_eq hC (MeagreEquiv.refl C)

@[simp] theorem clRep_empty : clRep (∅ : Set X) = ∅ :=
  clRep_of_isClopen isClopen_empty

/-- A clopen meagre set is empty (Baire). -/
theorem eq_empty_of_isClopen_of_isMeagre {C : Set X} (hC : IsClopen C) (h : IsMeagre C) :
    C = ∅ := by
  have h2 := baire_category_theorem C h
  rwa [hC.2.interior_eq] at h2

theorem isMeagre_iff_clRep_eq_empty {s : Set X} (hs : AlmostClopen s) :
    IsMeagre s ↔ clRep s = ∅ := by
  constructor
  · intro h
    refine eq_empty_of_isClopen_of_isMeagre (clRep_isClopen s) (IsMeagre.mono ?_
      (h.union (clRep_equiv hs)))
    intro x hx
    rw [Set.mem_union, Set.mem_symmDiff]
    by_cases hxs : x ∈ s
    · exact Or.inl hxs
    · exact Or.inr (Or.inr ⟨hx, hxs⟩)
  · intro h
    have h2 := clRep_equiv hs
    rw [MeagreEquiv, h] at h2
    simpa [Set.symmDiff_def] using h2

theorem clRep_disjoint {s t : Set X} (hs : AlmostClopen s) (ht : AlmostClopen t)
    (h : Disjoint s t) : Disjoint (clRep s) (clRep t) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  refine eq_empty_of_isClopen_of_isMeagre ((clRep_isClopen s).inter (clRep_isClopen t))
    (IsMeagre.mono ?_ ((clRep_equiv hs).union (clRep_equiv ht)))
  rintro x ⟨hxs, hxt⟩
  rw [Set.mem_union, Set.mem_symmDiff, Set.mem_symmDiff]
  by_cases hx : x ∈ s
  · exact Or.inr (Or.inr ⟨hxt, Set.disjoint_left.mp h hx⟩)
  · exact Or.inl (Or.inr ⟨hxs, hx⟩)

/-! ### The measure -/

/-- The value of the measure of **54XI** on an almost clopen set. -/
noncomputable def mac (s : Set X) : ℝ≥0∞ := ENNReal.ofReal (nu τ (clRep s))

@[simp] theorem mac_empty : mac τ (∅ : Set X) = 0 := by
  rw [mac, clRep_empty, nu_empty, ENNReal.ofReal_zero]

theorem mac_of_isClopen {C : Set X} (hC : IsClopen C) :
    mac τ C = ENNReal.ofReal (nu τ C) := by
  rw [mac, clRep_of_isClopen hC]

theorem mac_iUnion {f : ℕ → Set X} (hf : ∀ n, AlmostClopen (f n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    mac τ (⋃ n, f n) = ∑' n, mac τ (f n) := by
  have hcl : ∀ n, IsClopen (clRep (f n)) := fun n => clRep_isClopen _
  have hd : ∀ i j, i ≠ j → Disjoint (clRep (f i)) (clRep (f j)) := fun i j hij =>
    clRep_disjoint (hf i) (hf j) (hdisj i j hij)
  have hsum := hasSum_nu τ hcl hd
  have hopen : IsOpen (⋃ n, clRep (f n)) := isOpen_iUnion fun n => (hcl n).2
  have hrep : clRep (⋃ n, f n) = closure (⋃ n, clRep (f n)) := by
    refine clRep_eq ⟨isClosed_closure, ExtremallyDisconnected.open_closure _ hopen⟩ ?_
    exact (meagre_basic_4 f (fun n => clRep (f n)) fun n => clRep_equiv (hf n)).trans
      (meagre_basic_3 _ hopen).symm
  simp only [mac]
  rw [hrep, ← hsum.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun n => nu_nonneg τ _) hsum.summable]

/-- The measure of **54XI**. -/
noncomputable def macMeasure : @Measure X (almostClopenMS X) :=
  @Measure.ofMeasurable X (almostClopenMS X) (fun s _ => mac τ s) (mac_empty τ)
    (fun f h hd => mac_iUnion τ (fun n => (almostClopen_sigmaAlgebra X (f n)).mp (h n))
      (fun _ _ hij => hd hij))

theorem macMeasure_apply {s : Set X} (hs : AlmostClopen s) :
    macMeasure τ s = mac τ s :=
  @Measure.ofMeasurable_apply X (almostClopenMS X) _ _ _ s
    ((almostClopen_sigmaAlgebra X s).mpr hs)

variable (hfaith : ∀ f : C(X, ℂ), 0 ≤ f → τ f = 0 → f = 0)

include hfaith in
theorem nu_eq_zero_iff {C : Set X} (hC : IsClopen C) : nu τ C = 0 ↔ C = ∅ := by
  constructor
  · intro h
    rw [← chi_eq_zero_iff hC]
    refine hfaith _ (chi_nonneg C) ?_
    rw [npFunctional_chi_re, h]
    simp
  · rintro rfl; simp

include hfaith in
theorem mac_eq_zero_iff {s : Set X} (hs : AlmostClopen s) :
    mac τ s = 0 ↔ IsMeagre s := by
  have h1 : mac τ s = 0 ↔ nu τ (clRep s) = 0 := by
    rw [mac, ENNReal.ofReal_eq_zero]
    exact ⟨fun h => le_antisymm h (nu_nonneg _ _), fun h => h.le⟩
  rw [h1, nu_eq_zero_iff τ hfaith (clRep_isClopen s), ← isMeagre_iff_clRep_eq_empty hs]

/-- Any measure on the almost clopen σ-algebra which is null exactly on the
meagre sets and takes the value `ν` on clopen sets is `mac`. -/
theorem measure_eq_mac (μ : @Measure X (almostClopenMS X))
    (h0 : ∀ s : Set X, AlmostClopen s → (μ s = 0 ↔ IsMeagre s))
    (hcl : ∀ C : Set X, IsClopen C → μ C = ENNReal.ofReal (nu τ C))
    {s : Set X} (hs : AlmostClopen s) : μ s = mac τ s := by
  have hC : AlmostClopen (clRep s) := ⟨clRep s, clRep_isClopen s, MeagreEquiv.refl _⟩
  have hd1 : AlmostClopen (s \ clRep s) := (meagre_basic_6 s (clRep s) hs hC).2
  have hd2 : AlmostClopen (clRep s \ s) := (meagre_basic_6 (clRep s) s hC hs).2
  have hm1 : μ (s \ clRep s) = 0 := (h0 _ hd1).mpr
    ((clRep_equiv hs).mono (fun x hx => Or.inl hx))
  have hm2 : μ (clRep s \ s) = 0 := (h0 _ hd2).mpr
    ((clRep_equiv hs).mono (fun x hx => Or.inr ⟨hx.1, hx.2⟩))
  have e1 : μ s ≤ μ (clRep s) := by
    calc μ s ≤ μ (clRep s ∪ (s \ clRep s)) :=
          measure_mono (fun x hx => by by_cases h : x ∈ clRep s <;> simp [h, hx])
      _ ≤ μ (clRep s) + μ (s \ clRep s) := measure_union_le _ _
      _ = μ (clRep s) := by rw [hm1, add_zero]
  have e2 : μ (clRep s) ≤ μ s := by
    calc μ (clRep s) ≤ μ (s ∪ (clRep s \ s)) :=
          measure_mono (fun x hx => by by_cases h : x ∈ s <;> simp [h, hx])
      _ ≤ μ s + μ (clRep s \ s) := measure_union_le _ _
      _ = μ s := by rw [hm2, add_zero]
  rw [le_antisymm e1 e2, hcl _ (clRep_isClopen s), mac]

end Stone

/-- An np-functional is bounded, with `‖ω‖ ≤ ω(1)`: Kadison's inequality
`‖ω a‖ ≤ ‖a‖_ω √(ω 1)` together with `‖a‖_ω = ‖a·1‖_ω ≤ ‖a‖‖1‖_ω`.  (There is
a private copy of this in `A/Proc/Tensor.lean`, which is why this one is
private too.) -/
private theorem npFunctional_norm_le (ω : NPFunctional A) (a : A) :
    ‖ω a‖ ≤ (ω 1).re * ‖a‖ := by
  have h0 : (0 : ℝ) ≤ (ω 1).re := by
    simpa using (Complex.le_def.mp (npFunctional_nonneg ω zero_le_one)).1
  have h1 := norm_apply_le_omegaNorm ω a
  have h2 : omegaNorm A ω a ≤ ‖a‖ * Real.sqrt (ω 1).re := by
    have h := omegaNorm_mul_le ω a 1
    rwa [mul_one, omegaNorm_one] at h
  have h3 : Real.sqrt (ω 1).re * Real.sqrt (ω 1).re = (ω 1).re :=
    Real.mul_self_sqrt h0
  nlinarith [Real.sqrt_nonneg (ω 1).re, norm_nonneg a, omegaNorm_nonneg ω a]

/-! ### The second half: distributivity, measurability, and the integral

`isMeagre_closure_of_isMeagre` — *every meagre subset of `X` is nowhere
dense* — is the theorem that **54XI**'s measurability clause needs and that
vn.tex does not state (see ERRATA **54XII**); it is **false** without a
faithful np-functional, e.g. in the Gleason cover of `[0,1]`.  It is proved
here from normality and faithfulness of `τ` alone, before any measure is in
sight. -/

section Stone2

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [ExtremallyDisconnected X] (τ : NPFunctional C(X, ℂ))

omit [CompactSpace X] [T2Space X] [ExtremallyDisconnected X] in
theorem interior_union_of_isClopen {P Q : Set X} (hP : IsClopen P) :
    interior (P ∪ Q) = P ∪ interior Q := by
  refine subset_antisymm (fun x hx => ?_) (Set.union_subset
    (hP.2.subset_interior_iff.mpr Set.subset_union_left)
    (interior_mono Set.subset_union_right))
  by_cases hxP : x ∈ P
  · exact Or.inl hxP
  · refine Or.inr (interior_maximal ?_ (isOpen_interior.sdiff hP.1) ⟨hx, hxP⟩)
    rintro y ⟨hy, hyP⟩
    exact (interior_subset hy).resolve_left hyP

theorem nu_sdiff {C P : Set X} (hC : IsClopen C) (hP : IsClopen P) (h : P ⊆ C) :
    nu τ (C \ P) = nu τ C - nu τ P := by
  have hd : Disjoint P (C \ P) := Set.disjoint_sdiff_right
  have : nu τ C = nu τ P + nu τ (C \ P) := by
    rw [← nu_union τ hP (hC.diff hP) hd, Set.union_diff_cancel h]
  linarith

theorem nu_inter_ge {C P Q : Set X} (hC : IsClopen C) (hP : IsClopen P)
    (hQ : IsClopen Q) (hPC : P ⊆ C) (hQC : Q ⊆ C) :
    nu τ P + nu τ Q - nu τ C ≤ nu τ (P ∩ Q) := by
  have h1 : nu τ (P ∪ Q) = nu τ P + nu τ (Q \ P) := by
    rw [← nu_union τ hP (hQ.diff hP) Set.disjoint_sdiff_right, Set.union_diff_self]
  have h2 : nu τ Q = nu τ (Q ∩ P) + nu τ (Q \ P) := by
    rw [← nu_union τ (hQ.inter hP) (hQ.diff hP)
      (Set.disjoint_of_subset_left Set.inter_subset_right Set.disjoint_sdiff_right)]
    congr 1
    rw [Set.inter_union_diff]
  have h3 : nu τ (P ∪ Q) ≤ nu τ C :=
    nu_mono τ (hP.union hQ) hC (Set.union_subset hPC hQC)
  rw [Set.inter_comm]
  linarith

/-- Inside a clopen set `C`, a clopen subset of a dense open subset of `C`
can be chosen with `ν` arbitrarily close to `ν C` — this is normality of
`τ`. -/
theorem exists_clopen_nu_gt {C U : Set X} (hC : IsClopen C) (hU : IsOpen U)
    (hdense : C ⊆ closure U) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Set X, IsClopen D ∧ D ⊆ U ∩ C ∧ nu τ C - ε < nu τ D := by
  set 𝒞 : Set (Set X) := {D | IsClopen D ∧ D ⊆ U ∩ C} with h𝒞
  have hcl : ∀ D ∈ 𝒞, IsClopen D := fun D hD => hD.1
  have hne : 𝒞.Nonempty := ⟨∅, isClopen_empty, Set.empty_subset _⟩
  have hdir : DirectedOn (· ⊆ ·) 𝒞 := by
    rintro D ⟨hD, hDs⟩ E ⟨hE, hEs⟩
    exact ⟨D ∪ E, ⟨hD.union hE, Set.union_subset hDs hEs⟩,
      Set.subset_union_left, Set.subset_union_right⟩
  have hsU : ⋃₀ 𝒞 = U ∩ C := by
    refine subset_antisymm (Set.sUnion_subset fun D hD => hD.2) fun x hx => ?_
    obtain ⟨D, hD, hxD, hDs⟩ := exists_clopen_subset (hU.inter hC.2) hx
    exact ⟨D, ⟨hD, hDs⟩, hxD⟩
  have hclosure : closure (⋃₀ 𝒞) = C := by
    rw [hsU]
    refine subset_antisymm (closure_minimal Set.inter_subset_right hC.1) fun x hx => ?_
    refine mem_closure_iff.mpr fun V hV hxV => ?_
    obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp (hdense hx) (V ∩ C) (hV.inter hC.2) ⟨hxV, hx⟩
    exact ⟨y, hyV.1, hyU, hyV.2⟩
  have h := isLUB_nu τ hcl hne hdir
  rw [hclosure] at h
  by_contra hcon
  push_neg at hcon
  have : nu τ C ≤ nu τ C - ε := h.2 (by rintro _ ⟨D, hD, rfl⟩; exact hcon D hD.1 hD.2)
  linarith

/-- **The key distributivity property of the spectrum of a commutative von
Neumann algebra with a faithful np-functional**: given a sequence of closed
nowhere dense subsets `Nₙ` and a nonempty clopen `C`, there is a nonempty
clopen `b ⊆ C` disjoint from every `Nₙ`.  (In Boolean-algebraic terms: the
projection lattice is weakly `(σ,∞)`-distributive.) -/
theorem exists_clopen_disjoint_iUnion
    (hfaith : ∀ f : C(X, ℂ), 0 ≤ f → τ f = 0 → f = 0)
    {N : ℕ → Set X} (hNc : ∀ n, IsClosed (N n)) (hNd : ∀ n, interior (N n) = ∅)
    {C : Set X} (hC : IsClopen C) (hCne : C.Nonempty) :
    ∃ b : Set X, IsClopen b ∧ b.Nonempty ∧ b ⊆ C ∧ ∀ n, Disjoint b (N n) := by
  have hCpos : 0 < nu τ C := by
    rcases (nu_nonneg τ C).lt_or_eq with h | h
    · exact h
    · exact absurd ((nu_eq_zero_iff τ hfaith hC).mp h.symm)
        (Set.nonempty_iff_ne_empty.mp hCne)
  -- (1) clopen sets `D n ⊆ C \ N n` with `ν (D n)` close to `ν C`
  have hstep : ∀ n : ℕ, ∃ D : Set X, IsClopen D ∧ D ⊆ (C \ N n) ∩ C ∧
      nu τ C - nu τ C / 2 ^ (n + 2) < nu τ D := by
    intro n
    refine exists_clopen_nu_gt τ hC (hC.2.sdiff (hNc n)) (fun x hx => ?_)
      (by positivity)
    refine mem_closure_iff.mpr fun V hV hxV => ?_
    have hVC : (V ∩ C).Nonempty := ⟨x, hxV, hx⟩
    have : ¬ (V ∩ C ⊆ N n) := by
      intro hsub
      have : (V ∩ C).Nonempty → (interior (N n)).Nonempty := fun ⟨y, hy⟩ =>
        ⟨y, interior_maximal hsub (hV.inter hC.2) hy⟩
      rw [hNd n] at this
      exact (this hVC).ne_empty rfl
    obtain ⟨y, hy⟩ := Set.not_subset.mp this
    exact ⟨y, hy.1.1, hy.1.2, hy.2⟩
  choose D hDcl hDsub hDnu using hstep
  -- (2) the decreasing intersections
  set E : ℕ → Set X := fun n => ⋂ i ∈ Finset.range (n + 1), D i with hE
  have hEcl : ∀ n, IsClopen (E n) := fun n =>
    isClopen_biInter_finset fun i _ => hDcl i
  have hEsub : ∀ n, E n ⊆ C := by
    intro n x hx
    have : x ∈ D 0 := Set.mem_iInter₂.mp hx 0 (by simp)
    exact (hDsub 0 this).2
  have hEanti : ∀ {m n : ℕ}, m ≤ n → E n ⊆ E m := by
    intro m n hmn
    exact Set.biInter_subset_biInter_left (by
      simpa using Nat.succ_le_succ hmn)
  have htpos : ∀ n : ℕ, 0 < nu τ C / 2 ^ (n + 2) := fun n => by positivity
  have htsucc : ∀ n : ℕ, nu τ C / 2 ^ (n + 1 + 2) = nu τ C / 2 ^ (n + 2) / 2 := by
    intro n
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_succ]
    ring
  have hEnu : ∀ n, nu τ C / 2 + nu τ C / 2 ^ (n + 2) ≤ nu τ (E n) := by
    intro n
    induction n with
    | zero =>
      have h0 : E 0 = D 0 := by simp [hE]
      have h1 := hDnu 0
      rw [h0]
      norm_num at h1 ⊢
      linarith
    | succ n ih =>
      have hsucc : E (n + 1) = D (n + 1) ∩ E n := by
        rw [hE]
        simp only []
        rw [Finset.range_add_one, Finset.set_biInter_insert]
      have hge := nu_inter_ge τ hC (hDcl (n + 1)) (hEcl n)
        (fun x hx => (hDsub (n + 1) hx).2) (hEsub n)
      have hd := hDnu (n + 1)
      have ht := htsucc n
      rw [hsucc]
      linarith
  have hEhalf : ∀ n, nu τ C / 2 ≤ nu τ (E n) := fun n => by
    linarith [hEnu n, htpos n]
  -- (3) the clopen `b`
  set b : Set X := interior (⋂ n, E n) with hb
  have hbcl : IsClopen b := isClopen_interior (isClosed_iInter fun n => (hEcl n).1)
  have hbsub : b ⊆ C := (interior_subset).trans ((Set.iInter_subset _ 0).trans (hEsub 0))
  -- `ν b ≥ ν C / 2`
  have hFdir : DirectedOn (· ⊆ ·) (Set.range fun n => C \ E n) := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    refine ⟨C \ E (max m n), ⟨max m n, rfl⟩, ?_, ?_⟩
    · exact Set.diff_subset_diff_right (hEanti (le_max_left m n))
    · exact Set.diff_subset_diff_right (hEanti (le_max_right m n))
  have hFcl : ∀ F ∈ Set.range fun n => C \ E n, IsClopen F := by
    rintro _ ⟨n, rfl⟩; exact hC.diff (hEcl n)
  have hFunion : ⋃₀ (Set.range fun n => C \ E n) = C \ ⋂ n, E n := by
    rw [Set.sUnion_range, ← Set.diff_iInter]
  have hFclosure : closure (C \ ⋂ n, E n) = C \ b := by
    rw [closure_eq_compl_interior_compl]
    have h1 : (C \ ⋂ n, E n)ᶜ = Cᶜ ∪ ⋂ n, E n := by
      rw [Set.diff_eq, Set.compl_inter, compl_compl]
    rw [h1, interior_union_of_isClopen hC.compl, ← hb, Set.compl_union, compl_compl,
      Set.diff_eq]
  have hlub := isLUB_nu τ hFcl ⟨_, ⟨0, rfl⟩⟩ hFdir
  rw [hFunion, hFclosure] at hlub
  have hbnu : nu τ C / 2 ≤ nu τ b := by
    have hub : ∀ r ∈ nu τ '' (Set.range fun n => C \ E n), r ≤ nu τ C - nu τ C / 2 := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      rw [nu_sdiff τ hC (hEcl n) (hEsub n)]
      linarith [hEhalf n]
    have h2 := hlub.2 hub
    rw [nu_sdiff τ hC hbcl hbsub] at h2
    linarith
  refine ⟨b, hbcl, ?_, hbsub, fun n => ?_⟩
  · rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, nu_empty] at hbnu
    linarith
  · refine Set.disjoint_left.mpr fun x hx hxN => ?_
    have h1 : x ∈ E n := (interior_subset hx) |> fun h => Set.mem_iInter.mp h n
    have h2 : x ∈ D n := Set.mem_iInter₂.mp h1 n (by simp)
    exact ((hDsub n h2).1).2 hxN

/-- **The closure of a meagre subset of the spectrum is meagre.**  (Weak
`(σ,∞)`-distributivity; false in a general extremally disconnected compact
Hausdorff space, e.g. in the Gleason cover of `[0,1]`.) -/
theorem isMeagre_closure_of_isMeagre
    (hfaith : ∀ f : C(X, ℂ), 0 ≤ f → τ f = 0 → f = 0)
    {s : Set X} (h : IsMeagre s) : IsMeagre (closure s) := by
  obtain ⟨S, hSnd, hScount, hSsub⟩ := isMeagre_iff_countable_union_isNowhereDense.mp h
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS] at hSsub
    simp only [Set.sUnion_empty, Set.subset_empty_iff] at hSsub
    rw [hSsub]
    simpa using (IsMeagre.empty : IsMeagre (∅ : Set X))
  obtain ⟨f, hf⟩ := hScount.exists_eq_range hS
  set N : ℕ → Set X := fun n => closure (f n) with hN
  have hNc : ∀ n, IsClosed (N n) := fun n => isClosed_closure
  have hNd : ∀ n, interior (N n) = ∅ := by
    intro n
    have : IsNowhereDense (f n) := hSnd _ (by rw [hf]; exact ⟨n, rfl⟩)
    exact this
  have hsub : s ⊆ ⋃ n, N n := by
    refine hSsub.trans (Set.sUnion_subset fun t ht => ?_)
    rw [hf] at ht
    obtain ⟨n, rfl⟩ := ht
    exact (subset_closure).trans (Set.subset_iUnion N n)
  have hnd : IsNowhereDense (⋃ n, N n) := by
    rw [IsNowhereDense]
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨C, hC, hxC, hCsub⟩ := exists_clopen_subset isOpen_interior hx
    obtain ⟨b, hbcl, hbne, hbC, hbd⟩ :=
      exists_clopen_disjoint_iUnion τ hfaith hNc hNd hC ⟨x, hxC⟩
    obtain ⟨y, hy⟩ := hbne
    have hy2 : y ∈ closure (⋃ n, N n) := interior_subset (hCsub (hbC hy))
    have : (b ∩ ⋃ n, N n).Nonempty := mem_closure_iff.mp hy2 b hbcl.2 hy
    obtain ⟨z, hzb, hz⟩ := this
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (hbd n) hzb hzn
  exact (IsNowhereDense.isMeagre (hnd.closure.mono (closure_mono hsub)))

/-- A function continuous outside a meagre set is measurable for the almost
clopen σ-algebra. -/
theorem measurable_of_continuousAt_compl {f : X → ℂ} {E : Set X} (hE : IsMeagre E)
    (hc : ∀ x ∈ Eᶜ, ContinuousAt f x) : @Measurable _ _ (almostClopenMS X) _ f := by
  refine @measurable_of_isOpen ℂ X _ _ _ (almostClopenMS X) f (fun W hW => ?_)
  refine (almostClopen_sigmaAlgebra X _).mpr ?_
  have hsub : (f ⁻¹' W) ∆ interior (f ⁻¹' W) ⊆ E := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · by_contra hxE
      exact hx2 (mem_interior_iff_mem_nhds.mpr (hc x hxE (hW.mem_nhds hx1)))
    · exact absurd (interior_subset hx1) hx2
  refine ⟨closure (interior (f ⁻¹' W)),
    ⟨isClosed_closure, ExtremallyDisconnected.open_closure _ isOpen_interior⟩, ?_⟩
  exact MeagreEquiv.trans (show MeagreEquiv (f ⁻¹' W) (interior (f ⁻¹' W)) from
    hE.mono hsub) (meagre_basic_3 _ isOpen_interior).symm

/-- **Conversely**: a function measurable for the almost clopen σ-algebra is
continuous outside a meagre set — this is where weak distributivity
(`isMeagre_closure_of_isMeagre`) is needed. -/
theorem exists_isMeagre_continuousAt_of_measurable
    (hfaith : ∀ f : C(X, ℂ), 0 ≤ f → τ f = 0 → f = 0)
    {f : X → ℂ} (hmeas : @Measurable _ _ (almostClopenMS X) _ f) :
    ∃ E : Set X, IsMeagre E ∧ ∀ x ∈ Eᶜ, ContinuousAt f x := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis ℂ
  have hac : ∀ B ∈ b, AlmostClopen (f ⁻¹' B) := fun B hB =>
    (almostClopen_sigmaAlgebra X _).mp (hmeas (hb.isOpen hB).measurableSet)
  set M : Set X := ⋃ B ∈ b, (f ⁻¹' B) ∆ clRep (f ⁻¹' B) with hM
  have hMm : IsMeagre M := isMeagre_biUnion hbc fun B hB => clRep_equiv (hac B hB)
  refine ⟨closure M, isMeagre_closure_of_isMeagre τ hfaith hMm, fun x hx => ?_⟩
  have hxM : x ∉ M := fun h => hx (subset_closure h)
  show Filter.Tendsto f (nhds x) (nhds (f x))
  refine Filter.tendsto_def.mpr fun W hW => ?_
  obtain ⟨W₀, hW₀sub, hW₀open, hxW₀⟩ := mem_nhds_iff.mp hW
  obtain ⟨B, hB, hfxB, hBW⟩ := hb.exists_subset_of_mem_open hxW₀ hW₀open
  have hmem : ∀ y ∉ M, (y ∈ f ⁻¹' B ↔ y ∈ clRep (f ⁻¹' B)) := by
    intro y hy
    by_cases h1 : y ∈ f ⁻¹' B
    · refine ⟨fun _ => ?_, fun _ => h1⟩
      by_contra h2
      exact hy (Set.mem_biUnion hB (Or.inl ⟨h1, h2⟩))
    · refine ⟨fun h => absurd h h1, fun h2 => ?_⟩
      exact absurd (Set.mem_biUnion hB (Or.inr ⟨h2, h1⟩)) hy
  have hxC : x ∈ clRep (f ⁻¹' B) := (hmem x hxM).mp hfxB
  refine Filter.mem_of_superset
    (((clRep_isClopen (f ⁻¹' B)).2.sdiff isClosed_closure).mem_nhds ⟨hxC, hx⟩) ?_
  rintro y ⟨hyC, hyM⟩
  exact hW₀sub (hBW ((hmem y (fun h => hyM (subset_closure h))).mpr hyC))

/-! ### Uniform approximation by clopen combinations, and the integral -/

/-- Every continuous function on a compact Hausdorff extremally disconnected
space is uniformly approximated by `ℂ`-combinations of indicators of clopen
sets (the atoms of the finite Boolean algebra generated by a finite clopen
cover of small oscillation). -/
theorem exists_clopen_approx (f : C(X, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (Set X)) (c : Set X → ℂ), (∀ E ∈ s, IsClopen E) ∧
      ∀ x : X, ‖f x - ∑ E ∈ s, c E * chi E x‖ ≤ ε := by
  classical
  have hstep : ∀ y : X, ∃ D : Set X, IsClopen D ∧ y ∈ D ∧
      ∀ z ∈ D, ‖f z - f y‖ < ε / 2 := by
    intro y
    have hopen : IsOpen (f ⁻¹' Metric.ball (f y) (ε / 2)) :=
      Metric.isOpen_ball.preimage f.continuous
    have hy : y ∈ f ⁻¹' Metric.ball (f y) (ε / 2) := by
      simp [Metric.mem_ball, hε]
    obtain ⟨D, hD, hyD, hDsub⟩ := exists_clopen_subset hopen hy
    refine ⟨D, hD, hyD, fun z hz => ?_⟩
    have := hDsub hz
    simpa [Metric.mem_ball, dist_eq_norm] using this
  choose D hDcl hDmem hDvar using hstep
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover D (fun y => (hDcl y).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hDmem x⟩)
  set A : ({y // y ∈ t} → Bool) → Set X := fun σ =>
    ⋂ i ∈ (Finset.univ : Finset {y // y ∈ t}), (cond (σ i) (D i) (D i)ᶜ) with hAdef
  have hAcl : ∀ σ, IsClopen (A σ) := by
    intro σ
    refine isClopen_biInter_finset fun i _ => ?_
    cases hσi : σ i
    · simpa only [hσi, Bool.cond_false] using (hDcl i).compl
    · simpa only [hσi, Bool.cond_true] using hDcl i
  have hAdisj : ∀ σ σ', σ ≠ σ' → Disjoint (A σ) (A σ') := by
    intro σ σ' hne
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ σ' i := by
      by_contra hcon
      push_neg at hcon
      exact hne (funext hcon)
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h1 := Set.mem_iInter₂.mp hx i (Finset.mem_univ i)
    have h2 := Set.mem_iInter₂.mp hx' i (Finset.mem_univ i)
    have hcases : (σ i = true ∧ σ' i = false) ∨ (σ i = false ∧ σ' i = true) := by
      cases hσi : σ i <;> cases hσ'i : σ' i <;> simp_all
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, Bool.cond_true] at h1
      rw [hb, Bool.cond_false] at h2
      exact h2 h1
    · rw [ha, Bool.cond_false] at h1
      rw [hb, Bool.cond_true] at h2
      exact h1 h2
  refine ⟨Finset.image A Finset.univ,
    fun E => if h : E.Nonempty then f h.choose else 0, ?_, fun x => ?_⟩
  · rintro E hE
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hE
    exact hAcl σ
  · set σx : {y // y ∈ t} → Bool := fun i => decide (x ∈ D i) with hσx
    have hxA : x ∈ A σx := by
      refine Set.mem_iInter₂.mpr fun i _ => ?_
      by_cases h : x ∈ D i
      · simp [hσx, h]
      · simp [hσx, h]
    have hsum : ∑ E ∈ Finset.image A Finset.univ,
        (if h : E.Nonempty then f h.choose else 0) * chi E x
        = (if h : (A σx).Nonempty then f h.choose else 0) * chi (A σx) x := by
      refine Finset.sum_eq_single_of_mem (A σx)
        (Finset.mem_image_of_mem A (Finset.mem_univ σx)) ?_
      rintro E hE hne
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hE
      have hσ : σ ≠ σx := fun h => hne (by rw [h])
      rw [chi_of_notMem (hAcl σ) (Set.disjoint_left.mp (hAdisj σ σx hσ) · hxA |> fun h => h),
        mul_zero]
    rw [hsum, chi_of_mem (hAcl σx) hxA, mul_one, dif_pos ⟨x, hxA⟩]
    -- `x` and the chosen point of `A σx` lie in a common `D i`
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hσxi : σx ⟨i, hi⟩ = true := by simp [hσx, hxi]
    have hsub : A σx ⊆ D i := by
      intro z hz
      have := Set.mem_iInter₂.mp hz ⟨i, hi⟩ (Finset.mem_univ _)
      simpa [hσxi] using this
    have hy := hsub (Exists.choose_spec (⟨x, hxA⟩ : (A σx).Nonempty))
    have h1 := hDvar i x hxi
    have h2 := hDvar i _ hy
    calc ‖f x - f (Exists.choose (⟨x, hxA⟩ : (A σx).Nonempty))‖
        = ‖(f x - f i) - (f (Exists.choose (⟨x, hxA⟩ : (A σx).Nonempty)) - f i)‖ := by
          congr 1; ring
      _ ≤ ‖f x - f i‖ + ‖f (Exists.choose (⟨x, hxA⟩ : (A σx).Nonempty)) - f i‖ :=
          norm_sub_le _ _
      _ ≤ ε := by linarith

/-- **The integral against the measure of 54XI computes `τ`.** -/
theorem integral_eq_npFunctional (μ : @Measure X (almostClopenMS X))
    (hμC : ∀ C : Set X, IsClopen C → μ C = ENNReal.ofReal (nu τ C)) (f : C(X, ℂ)) :
    ∫ x, f x ∂μ = τ f := by
  letI : MeasurableSpace X := almostClopenMS X
  have hms : ∀ C : Set X, IsClopen C → MeasurableSet C := fun C hC =>
    (almostClopen_sigmaAlgebra X C).mpr ⟨C, hC, MeagreEquiv.refl _⟩
  haveI hfin : IsFiniteMeasure μ := ⟨by
    rw [hμC Set.univ isClopen_univ]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : ∀ g : C(X, ℂ), Measurable (g : X → ℂ) := fun g =>
    measurable_of_continuousAt_compl IsMeagre.empty
      (fun x _ => g.continuous.continuousAt)
  have hint : ∀ g : C(X, ℂ), Integrable (g : X → ℂ) μ := fun g =>
    (integrable_const ‖g‖).mono' (hmeas g).stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall (g.norm_coe_le_norm))
  have hchi : ∀ C : Set X, IsClopen C → ∫ x, chi C x ∂μ = τ (chi C) := by
    intro C hC
    have h1 : (fun x => chi C x) = Set.indicator C (fun _ => (1 : ℂ)) :=
      funext (chi_apply hC)
    rw [h1, integral_indicator_const (1 : ℂ) (hms C hC), npFunctional_chi_re,
      measureReal_def, hμC C hC, ENNReal.toReal_ofReal (nu_nonneg τ C)]
    simp
  set K : ℝ := μ.real Set.univ + (τ 1).re with hK
  have hK0 : 0 ≤ K := by
    have : (0:ℝ) ≤ (τ 1).re :=
      (Complex.le_def.mp (npFunctional_nonneg τ zero_le_one)).1
    have h2 : (0:ℝ) ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    linarith
  have key : ∀ ε : ℝ, 0 < ε → ‖(∫ x, f x ∂μ) - τ f‖ ≤ ε * K := by
    intro ε hε
    obtain ⟨s, c, hcl, happ⟩ := exists_clopen_approx f hε
    classical
    set g : C(X, ℂ) := ∑ E ∈ s, c E • chi E with hg
    have hgapp : ∀ x, ‖(f - g) x‖ ≤ ε := by
      intro x
      have : (g : X → ℂ) x = ∑ E ∈ s, c E * chi E x := by
        rw [hg, ContinuousMap.coe_sum]
        simp [Finset.sum_apply]
      simpa [this] using happ x
    have hgnorm : ‖f - g‖ ≤ ε := (ContinuousMap.norm_le _ hε.le).mpr hgapp
    have hIg : ∫ x, g x ∂μ = τ g := by
      have h1 : (fun x => (g : X → ℂ) x) = fun x => ∑ E ∈ s, c E * chi E x := by
        funext x
        rw [hg, ContinuousMap.coe_sum]
        simp [Finset.sum_apply]
      rw [h1, integral_finsetSum s (fun E _ => (hint (chi E)).const_mul (c E))]
      have h2 : ∀ E ∈ s, ∫ x, c E * chi E x ∂μ = c E * τ (chi E) := by
        intro E hE
        rw [integral_const_mul, hchi E (hcl E hE)]
      rw [Finset.sum_congr rfl h2, hg,
        show (τ (∑ E ∈ s, c E • chi E) : ℂ) = ∑ E ∈ s, (τ (c E • chi E) : ℂ) from
          map_sum τ.toPositiveLinearMap _ s]
      refine (Finset.sum_congr rfl fun E _ => ?_).symm
      exact (map_smul τ.toPositiveLinearMap (c E) (chi E)).trans (smul_eq_mul _ _)
    have hdiff : (∫ x, f x ∂μ) - τ f
        = (∫ x, (f - g) x ∂μ) + τ (g - f) := by
      have h1 : ∫ x, (f - g) x ∂μ = (∫ x, f x ∂μ) - ∫ x, g x ∂μ := by
        simpa using integral_sub (hint f) (hint g)
      have h2 : (τ (g - f) : ℂ) = τ g - τ f := by
        have := map_sub τ.toPositiveLinearMap g f
        exact this
      rw [h1, h2, hIg]
      ring
    have hb1 : ‖∫ x, (f - g) x ∂μ‖ ≤ ε * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hgapp)
    have hb2 : ‖(τ (g - f) : ℂ)‖ ≤ (τ 1).re * ε := by
      refine (npFunctional_norm_le τ (g - f)).trans ?_
      have h0 : (0:ℝ) ≤ (τ 1).re :=
        (Complex.le_def.mp (npFunctional_nonneg τ zero_le_one)).1
      have : ‖g - f‖ = ‖f - g‖ := by rw [← norm_neg]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hgnorm h0
    rw [hdiff]
    calc ‖(∫ x, (f - g) x ∂μ) + τ (g - f)‖
        ≤ ‖∫ x, (f - g) x ∂μ‖ + ‖(τ (g - f) : ℂ)‖ := norm_add_le _ _
      _ ≤ ε * μ.real Set.univ + (τ 1).re * ε := add_le_add hb1 hb2
      _ = ε * K := by rw [hK]; ring
  have hzero : ‖(∫ x, f x ∂μ) - τ f‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := key (ε / (K + 1)) (by positivity)
    have h2 : ε / (K + 1) * K ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < K + 1)]
      nlinarith
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

end Stone2

/-! ### The continuous representative of a bounded measurable function

The last clause of **54XI** — that `f ↦ f°` is an nmiu-isomorphism
`C(spec 𝒜) → L^∞(spec 𝒜)` — needs one piece of mathematics beyond
`cvn_faithful_2`: a bounded measurable function on the spectrum agrees
*almost everywhere with a continuous function*, not merely (as
`cvn_faithful_2` says) at almost every point.  The thesis gets this from
surjectivity of `ϱ : f ↦ f°`, which is the erratum recorded for 54XII; the
construction below is the classical one, from the clopen representatives
`Cᵣ = clRep {f < r}` (`r` rational) of the sublevel sets, by
`g(x) = inf {r : x ∈ Cᵣ}`.  It is extremal disconnectedness of the spectrum,
through `clRep`, that makes it work; uniqueness of the continuous
representative is Baire (`eq_of_isMeagre_ne`).

Everything in this section is `private`; `cvn_faithful_4` and
`cvn_faithful_6` below are what it is for. -/

section ContRep

namespace ContRep

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [ExtremallyDisconnected X] [MeasurableSpace X]

private theorem clRep_mono {s t : Set X} (hs : AlmostClopen s) (ht : AlmostClopen t)
    (hst : s ⊆ t) : clRep s ⊆ clRep t := by
  have hmeagre : IsMeagre (clRep s \ clRep t) := by
    refine IsMeagre.mono ?_ ((clRep_equiv hs).union (clRep_equiv ht))
    rintro x ⟨hxs, hxt⟩
    rw [Set.mem_union, Set.mem_symmDiff, Set.mem_symmDiff]
    by_cases hx : x ∈ s
    · exact Or.inr (Or.inl ⟨hst hx, hxt⟩)
    · exact Or.inl (Or.inr ⟨hxs, hx⟩)
  have h := eq_empty_of_isClopen_of_isMeagre
    ((clRep_isClopen s).diff (clRep_isClopen t)) hmeagre
  exact Set.diff_eq_empty.mp h

/-- A continuous function that vanishes off a meagre set vanishes. -/
private theorem eq_of_isMeagre_ne {g h : X → ℂ} (hg : Continuous g) (hh : Continuous h)
    (hm : IsMeagre {x | g x ≠ h x}) : g = h := by
  have hopen : IsOpen {x | g x ≠ h x} := by
    have : {x | g x ≠ h x} = (fun x => g x - h x) ⁻¹' {(0 : ℂ)}ᶜ := by
      ext x; simp [sub_eq_zero]
    rw [this]
    exact (hg.sub hh).isOpen_preimage _ (isClosed_singleton.isOpen_compl)
  have h0 : {x | g x ≠ h x} = ∅ := by
    have := baire_category_theorem _ hm
    rwa [hopen.interior_eq] at this
  funext x
  by_contra hne
  exact absurd (Set.eq_empty_iff_forall_notMem.mp h0 x) (by simpa using hne)

/-- Every bounded measurable real function on the spectrum agrees off a meagre
set with a continuous one.  The representative is built from the clopen
representatives `Cᵣ` of the sublevel sets `{f < r}` (`r` rational) by
`g(x) = inf {r : x ∈ Cᵣ}`; `Cᵣ` is increasing in `r`, empty below `-M` and
everything above `M`, which makes the infimum well defined, and
`{g < r} = ⋃_{q<r} C_q`, `{g > r} = ⋃_{q>r} C_qᶜ` are open. -/
private theorem exists_contRep_real
    (hms : ∀ s : Set X, MeasurableSet s ↔ AlmostClopen s) (f : X → ℝ)
    (hfm : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∃ g : X → ℝ, Continuous g ∧ IsMeagre {x | f x ≠ g x} := by
  classical
  have hac : ∀ r : ℚ, AlmostClopen {y : X | f y < (r : ℝ)} := fun r =>
    (hms _).mp (hfm measurableSet_Iio)
  set C : ℚ → Set X := fun r => clRep {y : X | f y < (r : ℝ)} with hCdef
  have hCclopen : ∀ r, IsClopen (C r) := fun r => clRep_isClopen _
  have hCmono : ∀ r r' : ℚ, r ≤ r' → C r ⊆ C r' := by
    intro r r' hrr
    refine clRep_mono (hac r) (hac r') fun y hy => ?_
    show f y < (r' : ℝ)
    exact lt_of_lt_of_le hy (by exact_mod_cast hrr)
  have hClow : ∀ r : ℚ, (r : ℝ) ≤ -M → C r = ∅ := by
    intro r hr
    have : {y : X | f y < (r : ℝ)} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hr (neg_le_of_abs_le (hM y))
    rw [hCdef]; simp only; rw [this, clRep_empty]
  have hChigh : ∀ r : ℚ, M < (r : ℝ) → C r = Set.univ := by
    intro r hr
    have h1 : {y : X | f y < (r : ℝ)} = Set.univ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_le_of_lt (le_of_abs_le (hM y)) hr
    rw [hCdef]; simp only; rw [h1, clRep_of_isClopen isClopen_univ]
  set S : X → Set ℝ := fun x => (fun r : ℚ => (r : ℝ)) '' {r : ℚ | x ∈ C r} with hSdef
  obtain ⟨r₁, hr₁⟩ := exists_rat_gt M
  have hSne : ∀ x, (S x).Nonempty := by
    intro x
    exact ⟨(r₁ : ℝ), ⟨r₁, by rw [Set.mem_setOf_eq, hChigh r₁ hr₁]; trivial, rfl⟩⟩
  have hSbdd : ∀ x, BddBelow (S x) := by
    intro x
    refine ⟨-M, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    by_contra hlt
    rw [not_le] at hlt
    rw [Set.mem_setOf_eq, hClow r hlt.le] at hr
    exact hr
  set g : X → ℝ := fun x => sInf (S x) with hgdef
  have hlt : ∀ (x : X) (r : ℝ), g x < r ↔ ∃ q : ℚ, (q : ℝ) < r ∧ x ∈ C q := by
    intro x r
    rw [hgdef]
    simp only
    rw [csInf_lt_iff (hSbdd x) (hSne x)]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, hlt⟩
      exact ⟨q, hlt, hq⟩
    · rintro ⟨q, hq, hxq⟩
      exact ⟨(q : ℝ), ⟨q, hxq, rfl⟩, hq⟩
  have hgt : ∀ (x : X) (r : ℝ), r < g x ↔ ∃ q : ℚ, r < (q : ℝ) ∧ x ∉ C q := by
    intro x r
    constructor
    · intro h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
      refine ⟨q, hq1, fun hxq => ?_⟩
      have : g x ≤ (q : ℝ) := csInf_le (hSbdd x) ⟨q, hxq, rfl⟩
      exact absurd hq2 (not_lt.mpr this)
    · rintro ⟨q, hq, hxq⟩
      refine lt_of_lt_of_le hq ?_
      refine le_csInf (hSne x) ?_
      rintro _ ⟨q', hq', rfl⟩
      simp only
      by_contra hcon
      rw [not_le] at hcon
      have hq'q : q' ≤ q := by exact_mod_cast hcon.le
      exact hxq (hCmono q' q hq'q hq')
  have hopen1 : ∀ r : ℝ, IsOpen {x : X | g x < r} := by
    intro r
    have : {x : X | g x < r} = ⋃ q : {q : ℚ // (q : ℝ) < r}, C q.1 := by
      ext x
      rw [Set.mem_setOf_eq, hlt x r, Set.mem_iUnion]
      exact ⟨fun ⟨q, hq, hx⟩ => ⟨⟨q, hq⟩, hx⟩, fun ⟨q, hx⟩ => ⟨q.1, q.2, hx⟩⟩
    rw [this]
    exact isOpen_iUnion fun q => (hCclopen q.1).2
  have hopen2 : ∀ r : ℝ, IsOpen {x : X | r < g x} := by
    intro r
    have : {x : X | r < g x} = ⋃ q : {q : ℚ // r < (q : ℝ)}, (C q.1)ᶜ := by
      ext x
      rw [Set.mem_setOf_eq, hgt x r, Set.mem_iUnion]
      exact ⟨fun ⟨q, hq, hx⟩ => ⟨⟨q, hq⟩, hx⟩, fun ⟨q, hx⟩ => ⟨q.1, q.2, hx⟩⟩
    rw [this]
    exact isOpen_iUnion fun q => (hCclopen q.1).1.isOpen_compl
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Filter.eventually_of_mem ((hopen2 a).mem_nhds ha) fun y hy => hy
    · exact Filter.eventually_of_mem ((hopen1 a).mem_nhds ha) fun y hy => hy
  refine ⟨g, hcont, ?_⟩
  set N : Set X := ⋃ q : ℚ, symmDiff {y : X | f y < (q : ℝ)} (C q) with hNdef
  have hNm : IsMeagre N := isMeagre_iUnion fun q => clRep_equiv (hac q)
  refine IsMeagre.mono ?_ hNm
  intro x hx
  by_contra hxN
  have hkey : ∀ q : ℚ, (f x < (q : ℝ) ↔ x ∈ C q) := by
    intro q
    by_contra hcon
    refine hxN (Set.mem_iUnion.mpr ⟨q, ?_⟩)
    rw [Set.mem_symmDiff]
    rcases not_iff.mp hcon with h
    by_cases hf : f x < (q : ℝ)
    · exact Or.inl ⟨hf, fun hc => (h.mpr hc) hf⟩
    · exact Or.inr ⟨by tauto, hf⟩
  refine hx ?_
  rcases lt_trichotomy (f x) (g x) with h | h | h
  · obtain ⟨q, hq1, hq2⟩ := (hgt x (f x)).mp h
    exact absurd ((hkey q).mp hq1) hq2
  · exact h
  · obtain ⟨q, hq1, hq2⟩ := (hlt x (f x)).mp h
    exact absurd ((hkey q).mpr hq2) (not_lt.mpr hq1.le)

/-- Every bounded measurable function on the spectrum agrees off a meagre set
with a continuous one. -/
private theorem exists_contRep
    (hms : ∀ s : Set X, MeasurableSet s ↔ AlmostClopen s) (f : X → ℂ)
    (hf : IsBoundedMeasurable X f) :
    ∃ g : C(X, ℂ), IsMeagre {x | f x ≠ g x} := by
  obtain ⟨hfm, M, hMf⟩ := hf
  obtain ⟨g₁, hg₁c, hg₁m⟩ := exists_contRep_real hms (fun x => (f x).re)
    (Complex.measurable_re.comp hfm) M
    (fun x => (abs_le.mpr ⟨by
      have := Complex.abs_re_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.1], by
      have := Complex.abs_re_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.2]⟩))
  obtain ⟨g₂, hg₂c, hg₂m⟩ := exists_contRep_real hms (fun x => (f x).im)
    (Complex.measurable_im.comp hfm) M
    (fun x => (abs_le.mpr ⟨by
      have := Complex.abs_im_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.1], by
      have := Complex.abs_im_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.2]⟩))
  refine ⟨⟨fun x => (g₁ x : ℂ) + (g₂ x : ℂ) * Complex.I, ?_⟩, ?_⟩
  · exact (Complex.continuous_ofReal.comp hg₁c).add
      ((Complex.continuous_ofReal.comp hg₂c).mul continuous_const)
  · refine IsMeagre.mono ?_ (hg₁m.union hg₂m)
    intro x hx
    by_contra hxN
    rw [Set.mem_union] at hxN
    push_neg at hxN
    simp only [Set.mem_setOf_eq, not_not] at hxN
    refine hx ?_
    show f x = (g₁ x : ℂ) + (g₂ x : ℂ) * Complex.I
    rw [← hxN.1, ← hxN.2]
    exact (Complex.re_add_im (f x)).symm


/-- **54XI**, the isomorphism clause, in presentation form and for an
arbitrary C\*-algebra `𝒞` with `𝒞 ≃⋆ₐ[ℂ] C(X, ℂ)`: `q` is "take the
continuous representative, then apply `γ⁻¹`". -/
private theorem exists_presentation
    (hms : ∀ s : Set X, MeasurableSet s ↔ AlmostClopen s)
    (μ : Measure X)
    (hμ : ∀ s : Set X, AlmostClopen s → (μ s = 0 ↔ IsMeagre s))
    (𝒞 : Type*) [CStarAlgebra 𝒞] (γ : 𝒞 ≃⋆ₐ[ℂ] C(X, ℂ)) :
    ∃ q : (X → ℂ) → 𝒞,
      (∀ y : 𝒞, ∃ f, IsBoundedMeasurable X f ∧ q f = y) ∧
      (∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
        q (f + g) = q f + q g) ∧
      (∀ (z : ℂ) f, IsBoundedMeasurable X f → q (z • f) = z • q f) ∧
      (∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
        q (f * g) = q f * q g) ∧
      (∀ f, IsBoundedMeasurable X f → q (star f) = star (q f)) ∧
      q 1 = 1 ∧
      (∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0)) ∧
      (∀ f : C(X, ℂ), q (f : X → ℂ) = γ.symm f) := by
  classical
  -- an open set is almost clopen, so a continuous function is measurable
  have hopenac : ∀ U : Set X, IsOpen U → AlmostClopen U :=
    open_almost_clopen.mp inferInstance
  have hcontmeas : ∀ g : C(X, ℂ), Measurable (⇑g) := by
    intro g
    refine measurable_of_isOpen fun U hU => ?_
    exact (hms _).mpr (hopenac _ (hU.preimage g.continuous))
  have hbm : ∀ g : C(X, ℂ), IsBoundedMeasurable X (⇑g) :=
    fun g => ⟨hcontmeas g, ‖g‖, fun x => g.norm_coe_le_norm x⟩
  -- meagre sets are null
  have hnull : ∀ s : Set X, IsMeagre s → μ s = 0 := by
    intro s hs
    refine (hμ s ⟨∅, isClopen_empty, ?_⟩).mpr hs
    show IsMeagre (symmDiff s (∅ : Set X))
    simpa [Set.symmDiff_def] using hs
  -- a continuous function that is null-supported vanishes
  have hzero : ∀ g : C(X, ℂ), μ {x | (g : X → ℂ) x ≠ 0} = 0 → g = 0 := by
    intro g hg
    have hop : IsOpen {x | (g : X → ℂ) x ≠ 0} :=
      g.continuous.isOpen_preimage _ isClosed_singleton.isOpen_compl
    have hm : IsMeagre {x | (g : X → ℂ) x ≠ 0} :=
      (hμ _ (hopenac _ hop)).mp hg
    have h0 := baire_category_theorem _ hm
    rw [hop.interior_eq] at h0
    ext x
    by_contra hne
    exact absurd (Set.eq_empty_iff_forall_notMem.mp h0 x) (by simpa using hne)
  set q : (X → ℂ) → 𝒞 := fun f =>
    if h : ∃ g : C(X, ℂ), IsMeagre {x | f x ≠ (g : X → ℂ) x}
      then γ.symm h.choose else 0 with hqdef
  have hqspec : ∀ (f : X → ℂ) (g : C(X, ℂ)),
      IsMeagre {x | f x ≠ (g : X → ℂ) x} → q f = γ.symm g := by
    intro f g hfg
    have hex : ∃ g : C(X, ℂ), IsMeagre {x | f x ≠ (g : X → ℂ) x} := ⟨g, hfg⟩
    have hch := hex.choose_spec
    have heq : (hex.choose : X → ℂ) = (g : X → ℂ) := by
      refine eq_of_isMeagre_ne hex.choose.continuous g.continuous ?_
      refine IsMeagre.mono ?_ (hch.union hfg)
      intro x hx
      rw [Set.mem_union]
      by_cases hf : f x = (hex.choose : X → ℂ) x
      · refine Or.inr (show f x ≠ (g : X → ℂ) x from fun hc => hx ?_)
        show (hex.choose : X → ℂ) x = (g : X → ℂ) x
        rw [← hf]; exact hc
      · exact Or.inl hf
    rw [hqdef]
    simp only [dif_pos hex]
    congr 1
    exact DFunLike.coe_injective heq
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- surjectivity
    intro y
    refine ⟨⇑(γ y), hbm _, ?_⟩
    rw [hqspec _ (γ y) (by simpa using (IsMeagre.empty : IsMeagre (∅ : Set X)))]
    exact γ.symm_apply_apply y
  · -- additivity
    intro f f' hf hf'
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    obtain ⟨g', hg'⟩ := exists_contRep hms f' hf'
    rw [hqspec f g hg, hqspec f' g' hg', ← map_add]
    refine hqspec (f + f') (g + g') ?_
    refine IsMeagre.mono ?_ (hg.union hg')
    intro x hx
    rw [Set.mem_union]
    by_contra hcon
    push_neg at hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.add_apply, hcon.1, hcon.2])
  · -- scalars
    intro z f hf
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    rw [hqspec f g hg, ← map_smul]
    refine hqspec (z • f) (z • g) ?_
    refine IsMeagre.mono ?_ hg
    intro x hx
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.smul_apply, hcon])
  · -- multiplicativity
    intro f f' hf hf'
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    obtain ⟨g', hg'⟩ := exists_contRep hms f' hf'
    rw [hqspec f g hg, hqspec f' g' hg', ← map_mul]
    refine hqspec (f * f') (g * g') ?_
    refine IsMeagre.mono ?_ (hg.union hg')
    intro x hx
    rw [Set.mem_union]
    by_contra hcon
    push_neg at hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.mul_apply, hcon.1, hcon.2])
  · -- involution
    intro f hf
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    rw [hqspec f g hg, ← map_star]
    refine hqspec (star f) (star g) ?_
    refine IsMeagre.mono ?_ hg
    intro x hx
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.star_apply, hcon])
  · -- unitality
    rw [hqspec (1 : X → ℂ) 1 (by simpa using (IsMeagre.empty : IsMeagre (∅ : Set X)))]
    exact map_one _
  · -- kernel
    intro f hf
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    have hfg0 : μ {x | f x ≠ (g : X → ℂ) x} = 0 := hnull _ hg
    rw [hqspec f g hg]
    constructor
    · intro h0
      have hg0 : g = 0 := by
        have := congrArg γ h0
        rwa [γ.apply_symm_apply, map_zero] at this
      have hsub : {x | f x ≠ (0 : X → ℂ) x} ⊆ {x | f x ≠ (g : X → ℂ) x} := by
        intro x hx hc
        exact hx (by rw [hc, hg0]; rfl)
      exact measure_mono_null hsub hfg0
    · intro h0
      have hf0 : μ {x | f x ≠ (0 : X → ℂ) x} = 0 := h0
      have hsub : {x | (g : X → ℂ) x ≠ 0} ⊆
          {x | f x ≠ (g : X → ℂ) x} ∪ {x | f x ≠ (0 : X → ℂ) x} := by
        intro x hx
        rw [Set.mem_union]
        by_cases hc : f x = (g : X → ℂ) x
        · exact Or.inr (fun hz => hx (by rw [← hc]; exact hz))
        · exact Or.inl hc
      have := measure_mono_null hsub (measure_union_null hfg0 hf0)
      rw [hzero g this, map_zero]
  · -- the commuting triangle: on a continuous `f`, `q` is `γ⁻¹`
    intro f
    exact hqspec _ f (by simpa using (IsMeagre.empty : IsMeagre (∅ : Set X)))

/-- On the spectrum, where the measurable sets are the almost clopen ones, a
continuous function is bounded measurable. -/
private theorem bm_coe (hms : ∀ s : Set X, MeasurableSet s ↔ AlmostClopen s)
    (g : C(X, ℂ)) : IsBoundedMeasurable X (g : X → ℂ) := by
  have hopenac : ∀ U : Set X, IsOpen U → AlmostClopen U :=
    open_almost_clopen.mp inferInstance
  refine ⟨measurable_of_isOpen fun U hU => ?_, ‖g‖, fun x => g.norm_coe_le_norm x⟩
  exact (hms _).mpr (hopenac _ (hU.preimage g.continuous))

/-- **54XI**'s isomorphism clause with a *carrier* on the right: `f ↦ f°`,
the map sending a continuous function to its class modulo `μ`-a.e. equality,
is a ∗-isomorphism `C(X, ℂ) ≃⋆ₐ[ℂ] L^∞(X, μ)`.

Injectivity is Baire — a continuous function vanishing off a meagre set
vanishes — and surjectivity is `exists_contRep`, that every bounded
measurable function agrees off a meagre set with a continuous one.  The
algebraic clauses are `Linfty.mk`'s, applied to continuous functions through
`bm_coe`. -/
private theorem exists_linftyEquiv
    (hms : ∀ s : Set X, MeasurableSet s ↔ AlmostClopen s)
    (μ : Measure X)
    (hμ : ∀ s : Set X, AlmostClopen s → (μ s = 0 ↔ IsMeagre s)) :
    ∃ e : C(X, ℂ) ≃⋆ₐ[ℂ] Linfty μ,
      ∀ g : C(X, ℂ), e g = Linfty.mk μ (g : X → ℂ) := by
  classical
  have hopenac : ∀ U : Set X, IsOpen U → AlmostClopen U :=
    open_almost_clopen.mp inferInstance
  have hbm : ∀ g : C(X, ℂ), IsBoundedMeasurable X (g : X → ℂ) := bm_coe hms
  -- meagre sets are null
  have hnull : ∀ s : Set X, IsMeagre s → μ s = 0 := by
    intro s hs
    refine (hμ s ⟨∅, isClopen_empty, ?_⟩).mpr hs
    show IsMeagre (symmDiff s (∅ : Set X))
    simpa [Set.symmDiff_def] using hs
  -- a continuous function that is null-supported vanishes
  have hzero : ∀ g : C(X, ℂ), μ {x | (g : X → ℂ) x ≠ 0} = 0 → g = 0 := by
    intro g hg
    have hop : IsOpen {x | (g : X → ℂ) x ≠ 0} :=
      g.continuous.isOpen_preimage _ isClosed_singleton.isOpen_compl
    have hm : IsMeagre {x | (g : X → ℂ) x ≠ 0} :=
      (hμ _ (hopenac _ hop)).mp hg
    have h0 := baire_category_theorem _ hm
    rw [hop.interior_eq] at h0
    ext x
    by_contra hne
    exact absurd (Set.eq_empty_iff_forall_notMem.mp h0 x) (by simpa using hne)
  have hmk0 : Linfty.mk μ ((0 : C(X, ℂ)) : X → ℂ) = 0 := by
    refine (Linfty.mk_eq_zero_iff (hbm 0)).mpr ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    simp
  have hcomm : ∀ r : ℂ,
      Linfty.mk μ ((algebraMap ℂ C(X, ℂ) r : C(X, ℂ)) : X → ℂ)
        = algebraMap ℂ (Linfty μ) r := by
    intro r
    have h1 : ((algebraMap ℂ C(X, ℂ) r : C(X, ℂ)) : X → ℂ) = r • (1 : X → ℂ) := by
      ext x; simp
    rw [h1, Linfty.mk_smul r LinftyConstruction.bm_one, Linfty.mk_one,
      Algebra.algebraMap_eq_smul_one]
  have hinj : Function.Injective (fun g : C(X, ℂ) => Linfty.mk μ (g : X → ℂ)) := by
    intro g₁ g₂ hg
    have hae : (g₁ : X → ℂ) =ᵐ[μ] (g₂ : X → ℂ) :=
      (Linfty.mk_eq_iff (hbm g₁) (hbm g₂)).mp hg
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hae
    refine sub_eq_zero.mp (hzero (g₁ - g₂) ?_)
    refine Eq.trans ?_ hae
    congr 1
    ext x
    simp [sub_eq_zero]
  have hsurj : Function.Surjective (fun g : C(X, ℂ) => Linfty.mk μ (g : X → ℂ)) := by
    intro y
    obtain ⟨f, hf, hfy⟩ := Linfty.mk_surjective y
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    refine ⟨g, ?_⟩
    have hae : f =ᵐ[μ] (g : X → ℂ) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      exact hnull _ hg
    exact (Linfty.mk_congr hf (hbm g) hae).symm.trans hfy
  exact ⟨StarAlgEquiv.ofBijective
    ({ toFun := fun g => Linfty.mk μ (g : X → ℂ)
       map_one' := Linfty.mk_one
       map_mul' := fun g h => Linfty.mk_mul (hbm g) (hbm h)
       map_zero' := hmk0
       map_add' := fun g h => Linfty.mk_add (hbm g) (hbm h)
       commutes' := hcomm
       map_star' := fun g => Linfty.mk_star (hbm g) } : C(X, ℂ) →⋆ₐ[ℂ] Linfty μ)
    ⟨hinj, hsurj⟩, fun g => rfl⟩

end ContRep

end ContRep

/-! ### Normality of an `L^∞`-presentation — the "n" of **54XI**'s
"nmiu-isomorphism"

`cvn_faithful_4` below renders 54XI's clause that
`f ↦ f° : C(spec 𝒜) → L^∞(spec 𝒜)` is an nmiu-isomorphism in *presentation*
form — a map `q` from the bounded measurable functions onto `𝒜` that is
additive, ℂ-homogeneous, multiplicative, ∗-preserving and unital with kernel
exactly the `μ`-a.e.-zero functions — which is the convention 51IX
`Linfty_vn` and `A/Proc/Duplicators`' `IsLinftyOf` also follow.  That form
delivers "miu-isomorphism" but *not* the leading "n".

Normality of an actual `≃⋆ₐ` is `starAlgEquiv_preservesDirSups`, and it does
apply to `cvn_faithful_6`, which lands in the exported carrier `Linfty μ`.
It does not apply to a bare presentation, which has no `≃⋆ₐ` in it.  What
follows supplies the clause for presentations directly, and in the strongest
form: **every** such presentation is automatically normal — which is more
than `cvn_faithful_6` gives, and is what `cvn_faithful_5` reports.
The route is the one `starAlgHom_le_iff` (**48VI**.2) takes for an injective
∗-homomorphism, transported across `q`'s kernel clause rather than across
injectivity:

* `linftyPresentation_le_iff` — `q f ≤ q g` iff `f ≤ g` almost everywhere.
  Forward by the square root of the difference; backward by the thesis's own
  cube trick, `n q(f) n = -q(n)³` for `n` the negative part, which forces
  `q(n)³ = 0` and hence `q n = 0` (`eq_zero_of_pow_three_eq_zero`).
* `linftyPresentation_isLUB` — `q` carries a supremum for the a.e. order to a
  supremum in `𝒞`, which is normality.  Note that *no directedness is
  needed*: `q` is an order isomorphism modulo a.e. equality, so it preserves
  whichever suprema exist, and `PreservesDirSups`'s directed ones in
  particular.  Since the presentation is a bijection modulo a.e. equality,
  normality of `q` is normality of `f ↦ f°`, which is what 54XI asserts. -/

section LinftyPresentation

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {𝒞 : Type u} [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

private theorem pres_bm_sub {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f - g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun x => (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))⟩

private theorem pres_bm_mul {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f * g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, max Cf 0 * max Cg 0, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul ((hCf x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private theorem pres_bm_neg {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (-f) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  exact ⟨hfm.neg, Cf, fun x => by simpa using hCf x⟩

private theorem pres_bm_star {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (star f) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  exact ⟨(Complex.continuous_conj.measurable).comp hfm, Cf, fun x => by simpa using hCf x⟩

omit [PartialOrder 𝒞] [StarOrderedRing 𝒞] in
/-- A presentation respects equality almost everywhere: that is what its
kernel clause says. -/
private theorem pres_congr_ae {q : (X → ℂ) → 𝒞}
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0))
    {f g : X → ℂ} (hf : IsBoundedMeasurable X f) (hg : IsBoundedMeasurable X g)
    (hfg : f =ᵐ[μ] g) : q f = q g := by
  have hsub : IsBoundedMeasurable X (f - g) := pres_bm_sub hf hg
  have h0 : q (f - g) = 0 := (hker _ hsub).mpr (by filter_upwards [hfg] with x hx; simp [hx])
  have h := hadd (f - g) g hsub hg
  rw [sub_add_cancel, h0, zero_add] at h
  exact h

omit [PartialOrder 𝒞] [StarOrderedRing 𝒞] in
private theorem pres_zero {q : (X → ℂ) → 𝒞}
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0)) : q 0 = 0 :=
  (hker 0 ⟨measurable_const, 0, fun x => by simp⟩).mpr (by rfl)

omit [PartialOrder 𝒞] [StarOrderedRing 𝒞] in
private theorem pres_neg {q : (X → ℂ) → 𝒞}
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0))
    {f : X → ℂ} (hf : IsBoundedMeasurable X f) : q (-f) = - q f := by
  have h := hadd (-f) f (pres_bm_neg hf) hf
  rw [neg_add_cancel, pres_zero hker] at h
  have h2 : q (-f) + q f = -q f + q f := by rw [← h]; simp
  exact add_right_cancel h2

omit [PartialOrder 𝒞] [StarOrderedRing 𝒞] in
private theorem pres_sub {q : (X → ℂ) → 𝒞}
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    {f g : X → ℂ} (hf : IsBoundedMeasurable X f) (hg : IsBoundedMeasurable X g) :
    q (f - g) = q f - q g := by
  have h := hadd (f - g) g (pres_bm_sub hf hg) hg
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- A presentation is positive: an almost-everywhere nonnegative bounded
measurable `f` is `g* g` for the bounded measurable `g = √(ℜf)`, so `q f` is
`q(g)* q(g)`. -/
private theorem pres_nonneg {q : (X → ℂ) → 𝒞}
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    (hmul : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f * g) = q f * q g)
    (hstar : ∀ f, IsBoundedMeasurable X f → q (star f) = star (q f))
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0))
    {f : X → ℂ} (hf : IsBoundedMeasurable X f) (hpos : 0 ≤ᵐ[μ] f) :
    0 ≤ q f := by
  obtain ⟨hfm, C, hC⟩ := hf
  set s : X → ℂ := fun x => ((Real.sqrt (f x).re : ℝ) : ℂ) with hs
  have hsm : Measurable s :=
    Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (Complex.measurable_re.comp hfm))
  have hsb : IsBoundedMeasurable X s := by
    refine ⟨hsm, Real.sqrt C, fun x => ?_⟩
    have h1 : ‖s x‖ = Real.sqrt (f x).re := by
      simp [hs, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [h1]
    exact Real.sqrt_le_sqrt ((Complex.abs_re_le_norm (f x)).trans' (le_abs_self _) |>.trans (hC x))
  have hss : (s * s) =ᵐ[μ] f := by
    filter_upwards [hpos] with x hx
    have hre : (0:ℝ) ≤ (f x).re := (Complex.le_def.mp hx).1
    have him : (f x).im = 0 := ((Complex.le_def.mp hx).2).symm
    have hfx : (f x) = ((f x).re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [Pi.mul_apply, hs]
    simp only
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hre, ← hfx]
  have hstarS : star s = s := by
    funext x; simp [hs, Pi.star_apply, Complex.conj_ofReal]
  have hq : q f = star (q s) * q s := by
    rw [← pres_congr_ae hadd hker (pres_bm_mul hsb hsb) ⟨hfm, C, hC⟩ hss,
      hmul s s hsb hsb, ← hstar s hsb, hstarS]
  rw [hq]
  exact star_mul_self_nonneg _

/-- A presentation *reflects* positivity.  The thesis's cube trick, in the
form `starAlgHom_le_iff` uses it: with `n` the negative part of `f`,
`n f n = -n³` almost everywhere, so `q(n)³ ≤ 0` while `0 ≤ q(n)³`, whence
`q n = 0` and `n` vanishes almost everywhere. -/
private theorem pres_ae_nonneg {q : (X → ℂ) → 𝒞}
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    (hmul : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f * g) = q f * q g)
    (hstar : ∀ f, IsBoundedMeasurable X f → q (star f) = star (q f))
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0))
    {f : X → ℂ} (hf : IsBoundedMeasurable X f) (hq : 0 ≤ q f) :
    0 ≤ᵐ[μ] f := by
  obtain ⟨hfm, C, hC⟩ := hf
  have hf' : IsBoundedMeasurable X f := ⟨hfm, C, hC⟩
  -- `q f` is self-adjoint, so `f` is real almost everywhere
  have hreal : ∀ᵐ x ∂μ, (f x).im = 0 := by
    have h1 : q (star f) = q f := by
      rw [hstar f hf', (IsSelfAdjoint.of_nonneg hq).star_eq]
    have h2 := hadd (star f - f) f (pres_bm_sub (pres_bm_star hf') hf') hf'
    rw [sub_add_cancel, h1] at h2
    have h3 : q (star f - f) = 0 := by
      have h4 : q (star f - f) + q f = 0 + q f := by rw [← h2]; simp
      exact add_right_cancel h4
    have h5 := (hker _ (pres_bm_sub (pres_bm_star hf') hf')).mp h3
    filter_upwards [h5] with x hx
    have hx0 : star f x - f x = 0 := hx
    have h7 : (starRingEnd ℂ) (f x) = f x := sub_eq_zero.mp hx0
    have h6 := congrArg Complex.im h7
    simp only [Complex.conj_im] at h6
    linarith
  -- the negative part of `f`
  set n : X → ℂ := fun x => ((max (-(f x).re) 0 : ℝ) : ℂ) with hn
  have hnm : Measurable n :=
    Complex.measurable_ofReal.comp
      (((Complex.measurable_re.comp hfm).neg).max measurable_const)
  have hnb : IsBoundedMeasurable X n := by
    refine ⟨hnm, max C 0, fun x => ?_⟩
    have h1 : ‖n x‖ = max (-(f x).re) 0 := by
      simp [hn, Complex.norm_real, abs_of_nonneg (le_max_right _ (0:ℝ))]
    rw [h1]
    refine max_le ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left C 0)
    refine le_trans ?_ (hC x)
    have h2 := Complex.abs_re_le_norm (f x)
    have h3 : -(f x).re ≤ |(f x).re| := neg_le_abs _
    linarith
  have hnstar : star n = n := by
    funext x; simp [hn, Pi.star_apply, Complex.conj_ofReal]
  have hnnonneg : 0 ≤ᵐ[μ] n := by
    filter_upwards with x
    have h1 : (0:ℝ) ≤ max (-(f x).re) 0 := le_max_right _ _
    simp [hn, Complex.le_def, h1]
  have hqn : 0 ≤ q n := pres_nonneg hadd hmul hstar hker hnb hnnonneg
  have hqnsa : IsSelfAdjoint (q n) := IsSelfAdjoint.of_nonneg hqn
  have hkey : (n * f * n) =ᵐ[μ] (-(n * n * n)) := by
    filter_upwards [hreal] with x hx
    have hfx : f x = ((f x).re : ℂ) := by apply Complex.ext <;> simp [hx]
    rcases le_or_gt 0 ((f x).re) with h | h
    · have h0 : n x = 0 := by simp [hn, max_eq_right (by linarith : -(f x).re ≤ (0:ℝ))]
      simp [Pi.mul_apply, Pi.neg_apply, h0]
    · have h0 : n x = ((-(f x).re : ℝ) : ℂ) := by
        simp [hn, max_eq_left (by linarith : (0:ℝ) ≤ -(f x).re)]
      rw [Pi.mul_apply, Pi.mul_apply, Pi.neg_apply, Pi.mul_apply, Pi.mul_apply, h0, hfx]
      push_cast
      simp only [Complex.ofReal_re]
      ring
  have hcube : q n * q f * q n = -(q n ^ 3) := by
    have h1 : q (n * f * n) = q n * q f * q n := by
      rw [hmul _ _ (pres_bm_mul hnb hf') hnb, hmul _ _ hnb hf']
    have h2 : q (-(n * n * n)) = -(q n ^ 3) := by
      rw [pres_neg hadd hker (pres_bm_mul (pres_bm_mul hnb hnb) hnb),
        hmul _ _ (pres_bm_mul hnb hnb) hnb, hmul _ _ hnb hnb]
      noncomm_ring
    rw [← h1, ← h2]
    exact pres_congr_ae hadd hker (pres_bm_mul (pres_bm_mul hnb hf') hnb)
      (pres_bm_neg (pres_bm_mul (pres_bm_mul hnb hnb) hnb)) hkey
  have hle : q n ^ 3 ≤ 0 := by
    have h1 : (0:𝒞) ≤ star (q n) * q f * q n := star_left_conjugate_nonneg hq _
    rw [hqnsa.star_eq, hcube] at h1
    exact neg_nonneg.mp h1
  have hge : (0:𝒞) ≤ q n ^ 3 := CStarAlgebra.pow_nonneg hqn 3
  have hz : q n = 0 := eq_zero_of_pow_three_eq_zero hqnsa (le_antisymm hle hge)
  have hn0 := (hker n hnb).mp hz
  filter_upwards [hreal, hn0] with x hx hx0
  have h1 : max (-(f x).re) 0 = 0 := by
    have h2 : ((max (-(f x).re) 0 : ℝ) : ℂ) = 0 := hx0
    exact_mod_cast h2
  have h3 : (0:ℝ) ≤ (f x).re := by
    have h4 := le_max_left (-(f x).re) (0:ℝ)
    rw [h1] at h4
    linarith
  exact Complex.le_def.mpr ⟨h3, hx.symm⟩

/-- **54XI**, the "n" of "nmiu", first half: an `L^∞`-presentation `q` of a
C\*-algebra `𝒞` — additive, multiplicative, ∗-preserving, with kernel exactly
the `μ`-a.e.-zero functions — is an *order embedding* for the almost-everywhere
order.  This is `starAlgHom_le_iff` (**48VI**.2) with `q`'s kernel clause in
place of injectivity, and neither ℂ-homogeneity nor unitality is needed. -/
theorem linftyPresentation_le_iff {q : (X → ℂ) → 𝒞}
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    (hmul : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f * g) = q f * q g)
    (hstar : ∀ f, IsBoundedMeasurable X f → q (star f) = star (q f))
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0))
    {f g : X → ℂ} (hf : IsBoundedMeasurable X f) (hg : IsBoundedMeasurable X g) :
    q f ≤ q g ↔ f ≤ᵐ[μ] g := by
  have hsub : IsBoundedMeasurable X (g - f) := pres_bm_sub hg hf
  have hqs : q (g - f) = q g - q f := pres_sub hadd hg hf
  constructor
  · intro h
    have h0 : 0 ≤ q (g - f) := by rw [hqs]; exact sub_nonneg.mpr h
    have h1 := pres_ae_nonneg hadd hmul hstar hker hsub h0
    filter_upwards [h1] with x hx
    have h2 : (0:ℂ) ≤ g x - f x := hx
    exact sub_nonneg.mp h2
  · intro h
    have h0 : 0 ≤ᵐ[μ] (g - f) := by
      filter_upwards [h] with x hx
      show (0:ℂ) ≤ g x - f x
      exact sub_nonneg.mpr hx
    have h1 := pres_nonneg hadd hmul hstar hker hsub h0
    rw [hqs] at h1
    exact sub_nonneg.mp h1

/-- **54XI**, the "n" of "nmiu": an `L^∞`-presentation is **normal**.  If `s`
is a least upper bound of `D` for the almost-everywhere order on bounded
measurable functions, then `q s` is a least upper bound of `q '' D` in `𝒞`.

Directedness of `D` is not assumed and is not needed: by
`linftyPresentation_le_iff` together with surjectivity, `q` is an order
isomorphism modulo equality almost everywhere, so it carries *every* supremum
that exists to a supremum — the directed ones of `PreservesDirSups` among
them.  Because `q` is that isomorphism, this is equally the normality of the
map `f ↦ f°` of 54XI, of which `q` is the inverse. -/
theorem linftyPresentation_isLUB {q : (X → ℂ) → 𝒞}
    (hsurj : ∀ y : 𝒞, ∃ f, IsBoundedMeasurable X f ∧ q f = y)
    (hadd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f + g) = q f + q g)
    (hmul : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q (f * g) = q f * q g)
    (hstar : ∀ f, IsBoundedMeasurable X f → q (star f) = star (q f))
    (hker : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0))
    {D : Set (X → ℂ)} {s : X → ℂ}
    (hD : ∀ f ∈ D, IsBoundedMeasurable X f) (hs : IsBoundedMeasurable X s)
    (hub : ∀ f ∈ D, f ≤ᵐ[μ] s)
    (hleast : ∀ t : X → ℂ, IsBoundedMeasurable X t →
      (∀ f ∈ D, f ≤ᵐ[μ] t) → s ≤ᵐ[μ] t) :
    IsLUB (q '' D) (q s) := by
  constructor
  · rintro _ ⟨f, hfD, rfl⟩
    exact (linftyPresentation_le_iff hadd hmul hstar hker (hD f hfD) hs).mpr (hub f hfD)
  · intro a ha
    obtain ⟨t, ht, rfl⟩ := hsurj a
    refine (linftyPresentation_le_iff hadd hmul hstar hker hs ht).mpr
      (hleast t ht fun f hfD => ?_)
    exact (linftyPresentation_le_iff hadd hmul hstar hker (hD f hfD) ht).mp (ha ⟨f, hfD, rfl⟩)

end LinftyPresentation


section CVNFaithful

variable {A : Type*} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A]

open WeakDual

/-- The np-functional `ω ∘ γ_A⁻¹` on `C(spec A, ℂ)` transported along the
Gelfand isomorphism (**53II**). -/
noncomputable def gelfandNP (ω : NPFunctional A) : NPFunctional C(characterSpace ℂ A, ℂ) :=
  compNP (starAlgHomP (gelfandStarTransform A).symm.toStarAlgHom)
    (starAlgEquiv_preservesDirSups (gelfandStarTransform A).symm) ω

theorem gelfandNP_apply (ω : NPFunctional A) (f : C(characterSpace ℂ A, ℂ)) :
    gelfandNP ω f = ω ((gelfandStarTransform A).symm f) := rfl

theorem gelfandNP_faithful (ω : NPFunctional A)
    (hω : ∀ a : A, 0 ≤ a → ω a = 0 → a = 0) :
    ∀ f : C(characterSpace ℂ A, ℂ), 0 ≤ f → gelfandNP ω f = 0 → f = 0 := by
  intro f hf h
  have h1 : (0 : A) ≤ (gelfandStarTransform A).symm f :=
    starAlgHom_nonneg (gelfandStarTransform A).symm.toStarAlgHom hf
  have h3 := congrArg (gelfandStarTransform A) (hω _ h1 h)
  simpa using h3

/-- The continuous indicator of a clopen set is the only continuous function
whose values are those of the set-theoretic indicator. -/
theorem eq_chi_of_indicator {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : IsClopen C) (f : C(X, ℂ)) (hf : ∀ x, f x = C.indicator (fun _ => 1) x) :
    f = chi C := by
  ext x; rw [hf x, chi_apply hC]

/-- **54XI** (`cvn-faithful`, vn.tex:2014, Theorem), part 1: for a
commutative von Neumann algebra `A` with a faithful np-functional `ω` there
is a unique measure `μ` on the σ-algebra of almost clopen subsets of
`spec A` such that `μ(s) = 0` iff `s` is meagre, and
`μ(C) = ω(γ_A⁻¹(𝟙_C))` for clopen `C`; and `μ` is finite and complete. -/
theorem cvn_faithful_1 (ω : NPFunctional A)
    (hω : ∀ a : A, 0 ≤ a → ω a = 0 → a = 0) :
    ∃! μ : @Measure (characterSpace ℂ A) (almostClopenMS _),
      (∀ s : Set (characterSpace ℂ A), AlmostClopen s →
        (μ s = 0 ↔ IsMeagre s)) ∧
      (∀ (C : Set (characterSpace ℂ A)), IsClopen C →
        ∀ f : C(characterSpace ℂ A, ℂ),
          (∀ x, f x = C.indicator (fun _ => 1) x) →
          μ C = ENNReal.ofReal (ω ((gelfandStarTransform A).symm f)).re) ∧
      @IsFiniteMeasure _ (almostClopenMS _) μ ∧
      @Measure.IsComplete _ (almostClopenMS _) μ := by
  have := vn_spectrum_extremally_disconnected A
  set τ := gelfandNP ω with hτ
  have hfaith := gelfandNP_faithful ω hω
  have hclop : ∀ (C : Set (characterSpace ℂ A)), IsClopen C →
      ∀ f : C(characterSpace ℂ A, ℂ), (∀ x, f x = C.indicator (fun _ => 1) x) →
        ENNReal.ofReal (ω ((gelfandStarTransform A).symm f)).re
          = ENNReal.ofReal (nu τ C) := by
    intro C hC f hf
    rw [eq_chi_of_indicator hC f hf]
    rfl
  refine ⟨macMeasure τ, ⟨fun s hs => ?_, fun C hC f hf => ?_, ?_, ?_⟩, ?_⟩
  · rw [macMeasure_apply τ hs]
    exact mac_eq_zero_iff τ hfaith hs
  · rw [hclop C hC f hf, macMeasure_apply τ ⟨C, hC, MeagreEquiv.refl _⟩,
      mac_of_isClopen τ hC]
  · refine ⟨?_⟩
    rw [macMeasure_apply τ ⟨Set.univ, isClopen_univ, MeagreEquiv.refl _⟩,
      mac_of_isClopen τ isClopen_univ]
    exact ENNReal.ofReal_lt_top
  · refine ⟨fun s hs => ?_⟩
    obtain ⟨t, hst, ht, ht0⟩ :=
      @exists_measurable_superset_of_null _ (almostClopenMS _) _ _ hs
    have hta : AlmostClopen t := (almostClopen_sigmaAlgebra _ t).mp ht
    have htm : IsMeagre t := (mac_eq_zero_iff τ hfaith hta).mp
      (by rw [← macMeasure_apply τ hta]; exact ht0)
    refine (almostClopen_sigmaAlgebra _ s).mpr ⟨∅, isClopen_empty, ?_⟩
    show IsMeagre (s ∆ (∅ : Set (characterSpace ℂ A)))
    simpa [Set.symmDiff_def] using htm.mono hst
  · rintro μ ⟨h0, hC2, -, -⟩
    refine @Measure.ext _ (almostClopenMS _) _ _ (fun s hs => ?_)
    have hsa := (almostClopen_sigmaAlgebra _ s).mp hs
    rw [measure_eq_mac τ μ h0 (fun C hC => by
        rw [hC2 C hC (chi C) (fun x => (chi_apply hC x)), hclop C hC (chi C)
          (fun x => (chi_apply hC x))]) hsa,
      macMeasure_apply τ hsa]


/-- **54XI** (`cvn-faithful`, vn.tex:2014, Theorem), part 2: with respect to
this measure(-space) structure, a bounded function `f : spec A → ℂ` is
measurable iff it is continuous almost everywhere. -/
theorem cvn_faithful_2 (ω : NPFunctional A)
    (hω : ∀ a : A, 0 ≤ a → ω a = 0 → a = 0)
    (μ : @Measure (characterSpace ℂ A) (almostClopenMS _))
    (hμ : ∀ s : Set (characterSpace ℂ A), AlmostClopen s →
      (μ s = 0 ↔ IsMeagre s))
    (f : characterSpace ℂ A → ℂ) (hf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    @Measurable _ _ (almostClopenMS _) _ f ↔
      ∃ E : Set (characterSpace ℂ A), μ E = 0 ∧ ∀ x ∈ Eᶜ, ContinuousAt f x := by
  have := vn_spectrum_extremally_disconnected A
  have hnull : ∀ s : Set (characterSpace ℂ A), IsMeagre s → μ s = 0 := by
    intro s hs
    refine (hμ s ⟨∅, isClopen_empty, ?_⟩).mpr hs
    show IsMeagre (s ∆ (∅ : Set (characterSpace ℂ A)))
    simpa [Set.symmDiff_def] using hs
  have hmeagre : ∀ s : Set (characterSpace ℂ A), μ s = 0 → IsMeagre s := by
    intro s hs
    obtain ⟨t, hst, ht, ht0⟩ :=
      @exists_measurable_superset_of_null _ (almostClopenMS _) _ _ hs
    exact ((hμ t ((almostClopen_sigmaAlgebra _ t).mp ht)).mp ht0).mono hst
  constructor
  · intro hm
    obtain ⟨E, hE, hc⟩ := exists_isMeagre_continuousAt_of_measurable (gelfandNP ω)
      (gelfandNP_faithful ω hω) hm
    exact ⟨E, hnull E hE, hc⟩
  · rintro ⟨E, hE0, hc⟩
    exact measurable_of_continuousAt_compl (hmeagre E hE0) hc

/-- **54XI** (`cvn-faithful`, vn.tex:2014, Theorem), part 3: the diagram
commutes: `∫ f dμ = ω(γ_A⁻¹(f))` for every continuous `f` on `spec A`.
(The other half of the same paragraph — that `f ↦ f°` is an
nmiu-isomorphism `C(spec A) → L^∞(spec A)` — is `cvn_faithful_4` below.) -/
theorem cvn_faithful_3 (ω : NPFunctional A)
    (hω : ∀ a : A, 0 ≤ a → ω a = 0 → a = 0)
    (μ : @Measure (characterSpace ℂ A) (almostClopenMS _))
    (hμ : ∀ s : Set (characterSpace ℂ A), AlmostClopen s →
      (μ s = 0 ↔ IsMeagre s))
    (hμC : ∀ (C : Set (characterSpace ℂ A)), IsClopen C →
      ∀ f : C(characterSpace ℂ A, ℂ),
        (∀ x, f x = C.indicator (fun _ => 1) x) →
        μ C = ENNReal.ofReal (ω ((gelfandStarTransform A).symm f)).re)
    (f : C(characterSpace ℂ A, ℂ)) :
    ∫ x, f x ∂μ = ω ((gelfandStarTransform A).symm f) := by
  have := vn_spectrum_extremally_disconnected A
  have hclop : ∀ C : Set (characterSpace ℂ A), IsClopen C →
      μ C = ENNReal.ofReal (nu (gelfandNP ω) C) := by
    intro C hC
    rw [hμC C hC (chi C) (fun x => chi_apply hC x)]
    rfl
  exact integral_eq_npFunctional (gelfandNP ω) μ hclop f

/-- **54XI** (`cvn-faithful`, vn.tex:2014, Theorem), part 3, the other half:
`f ↦ f°` is an nmiu-**isomorphism** `C(spec A) → L^∞(spec A)`.

This is the *presentation* form, the one `Linfty_vn` and
`A/Proc/Duplicators`' `IsLinftyOf` use, and the one the consumers downstream
are stated against.  (For 54XI's clause with a carrier on the right — an
honest `≃⋆ₐ[ℂ]` onto `Linfty μ` — see `cvn_faithful_6`.)  It is: a map `q : 𝓛^∞(spec A) → A` which is surjective,
additive, `ℂ`-homogeneous, multiplicative, `∗`-preserving and unital, and
whose kernel is *exactly* the `μ`-a.e.-zero functions — so that `q` descends
to a miu-isomorphism `L^∞(spec A) ≅ A` — together with the commuting
triangle `q f = γ_A⁻¹(f)` for **continuous** `f`.  Reading the triangle
backwards through that descent: the induced map `C(spec A) → L^∞(spec A)` is
`f ↦ f°`, and it is a bijective miu-map.  Its normality is automatic, a
`∗`-isomorphism of von Neumann algebras being normal
(`starAlgEquiv_preservesDirSups`), which is also how 53II
(`gelfandNP`) already uses `γ_A`; `cvn_faithful_6` takes exactly that route,
and `cvn_faithful_5` takes a stronger one that works for presentations.

The `ℂ`-homogeneity clause `q (z • f) = z • q f` is stated: without it `q`
would be a `∗`-*ring* map only and the statement would not say "miu" — the
defect QUESTIONS **A9** raised against 51IX's own rendering, and the one
ruled in for `IsLinftyOf` on 2026-08-16 (that item was filed as **D1** in
`QUESTIONS.md` and deleted from it in the implementing commit 43e270f).
(A9 is now closed, deleted 2026-09-02, the clause restored in `Linfty_vn` too.)

Neither `ω` nor its faithfulness occurs: all the isomorphism needs of the
measure is that its null sets are the meagre almost clopen sets, which is
what `cvn_faithful_1` delivers.  The measurable structure is likewise given
abstractly by `hms` — any σ-algebra whose measurable sets are exactly the
almost clopen ones, which by 53V (`almostClopen_sigmaAlgebra`) is
`almostClopenMS (spec A)`.

The one piece of mathematics is `ContRep.exists_contRep`: every bounded
measurable function agrees off a meagre set with a continuous one. -/
theorem cvn_faithful_4 [MeasurableSpace (characterSpace ℂ A)]
    (hms : ∀ s : Set (characterSpace ℂ A), MeasurableSet s ↔ AlmostClopen s)
    (μ : Measure (characterSpace ℂ A))
    (hμ : ∀ s : Set (characterSpace ℂ A), AlmostClopen s →
      (μ s = 0 ↔ IsMeagre s)) :
    ∃ q : (characterSpace ℂ A → ℂ) → A,
      (∀ y : A, ∃ f, IsBoundedMeasurable (characterSpace ℂ A) f ∧ q f = y) ∧
      (∀ f g, IsBoundedMeasurable (characterSpace ℂ A) f →
        IsBoundedMeasurable (characterSpace ℂ A) g →
        q (f + g) = q f + q g) ∧
      (∀ (z : ℂ) f, IsBoundedMeasurable (characterSpace ℂ A) f →
        q (z • f) = z • q f) ∧
      (∀ f g, IsBoundedMeasurable (characterSpace ℂ A) f →
        IsBoundedMeasurable (characterSpace ℂ A) g →
        q (f * g) = q f * q g) ∧
      (∀ f, IsBoundedMeasurable (characterSpace ℂ A) f →
        q (star f) = star (q f)) ∧
      q 1 = 1 ∧
      (∀ f, IsBoundedMeasurable (characterSpace ℂ A) f →
        (q f = 0 ↔ f =ᵐ[μ] 0)) ∧
      (∀ f : C(characterSpace ℂ A, ℂ),
        q (f : characterSpace ℂ A → ℂ) = (gelfandStarTransform A).symm f) := by
  haveI := vn_spectrum_extremally_disconnected A
  exact ContRep.exists_presentation hms μ hμ A (gelfandStarTransform A)

/-- **54XI** (vn.tex:2035-2037), the isomorphism clause **in full**: the
presentation of `cvn_faithful_4` is not merely an miu-isomorphism but an
**nmiu**-isomorphism — `q` is *normal*.

The eight conjuncts before the last are `cvn_faithful_4`'s, verbatim; the
last is the "n".  It says that `q` carries a least upper bound for the
almost-everywhere order on `𝓛^∞(spec 𝒜)` to a least upper bound in `𝒜`, and
since `q` is a bijection modulo a.e. equality that is exactly normality of
the thesis's `f ↦ f°` in the direction the presentation form makes
available.  Directedness of `D` is not needed (see
`linftyPresentation_isLUB`), so the clause is stronger than
`PreservesDirSups` would ask.

Normality is *not* available from `starAlgEquiv_preservesDirSups` here: that
lemma is about an actual `≃⋆ₐ`, and a presentation is not one.  (Where there
is an `≃⋆ₐ` — `cvn_faithful_6`, into the carrier `Linfty μ` — that is
precisely the route taken.)  It is, however, automatic from the other eight
clauses, by `linftyPresentation_isLUB`, and in a form no `≃⋆ₐ` argument
gives: without directedness. -/
theorem cvn_faithful_5 [MeasurableSpace (characterSpace ℂ A)]
    (hms : ∀ s : Set (characterSpace ℂ A), MeasurableSet s ↔ AlmostClopen s)
    (μ : Measure (characterSpace ℂ A))
    (hμ : ∀ s : Set (characterSpace ℂ A), AlmostClopen s →
      (μ s = 0 ↔ IsMeagre s)) :
    ∃ q : (characterSpace ℂ A → ℂ) → A,
      (∀ y : A, ∃ f, IsBoundedMeasurable (characterSpace ℂ A) f ∧ q f = y) ∧
      (∀ f g, IsBoundedMeasurable (characterSpace ℂ A) f →
        IsBoundedMeasurable (characterSpace ℂ A) g →
        q (f + g) = q f + q g) ∧
      (∀ (z : ℂ) f, IsBoundedMeasurable (characterSpace ℂ A) f →
        q (z • f) = z • q f) ∧
      (∀ f g, IsBoundedMeasurable (characterSpace ℂ A) f →
        IsBoundedMeasurable (characterSpace ℂ A) g →
        q (f * g) = q f * q g) ∧
      (∀ f, IsBoundedMeasurable (characterSpace ℂ A) f →
        q (star f) = star (q f)) ∧
      q 1 = 1 ∧
      (∀ f, IsBoundedMeasurable (characterSpace ℂ A) f →
        (q f = 0 ↔ f =ᵐ[μ] 0)) ∧
      (∀ f : C(characterSpace ℂ A, ℂ),
        q (f : characterSpace ℂ A → ℂ) = (gelfandStarTransform A).symm f) ∧
      (∀ (D : Set (characterSpace ℂ A → ℂ)) (s : characterSpace ℂ A → ℂ),
        (∀ f ∈ D, IsBoundedMeasurable (characterSpace ℂ A) f) →
        IsBoundedMeasurable (characterSpace ℂ A) s →
        (∀ f ∈ D, f ≤ᵐ[μ] s) →
        (∀ t, IsBoundedMeasurable (characterSpace ℂ A) t →
          (∀ f ∈ D, f ≤ᵐ[μ] t) → s ≤ᵐ[μ] t) →
        IsLUB (q '' D) (q s)) := by
  obtain ⟨q, hsurj, hadd, hsmul, hmul, hstar, hone, hker, hcont⟩ :=
    cvn_faithful_4 hms μ hμ
  exact ⟨q, hsurj, hadd, hsmul, hmul, hstar, hone, hker, hcont,
    fun D s hD hs hub hleast =>
      linftyPresentation_isLUB hsurj hadd hmul hstar hker hD hs hub hleast⟩

/-! **54XIII** (vn.tex:2172): transition to the projections needed for the
full classification (70III, `Theses/A/VN/Projections.lean`) — nothing to
formalize. -/


/-- **54XI** (`cvn-faithful`, vn.tex:2035, Theorem), the isomorphism clause
**with a carrier**: `f ↦ f°` is an nmiu-isomorphism
`C(spec A) → L^∞(spec A)` — stated as the thesis states it, a ∗-isomorphism
onto the object `L^∞(spec A, μ)`, rather than in the presentation form of
`cvn_faithful_4`.

The carrier is `Linfty μ`, exported from the `L^∞` construction that proves
**51IX** (`Linfty_vn`); it is a commutative von Neumann algebra
(`Linfty.instVonNeumannAlgebra`), and 54XI's `f ↦ f°` is
`f ↦ Linfty.mk μ ⇑f`, the class of `f` modulo `μ`-a.e. equality.  The leading
"n" is `starAlgEquiv_preservesDirSups`: a ∗-isomorphism of C*-algebras is
automatically normal, which is the reading the doc of `cvn_faithful_4`
records as unavailable in presentation form.  The last clause is the `∫`
edge of 54XI's commuting triangle, with integration as an np-functional
(`Linfty.integralNP`, **51IX**); composed with `cvn_faithful_3` it gives
`∫ f° = ω (γ_A⁻¹ f)`, which is the triangle itself.

`cvn_faithful_4` and `cvn_faithful_5` are the same clause in presentation
form and are kept: they are what the `IsLinftyOf` consumers in
`A/Proc/Duplicators` are stated against, and `cvn_faithful_5`'s normality
clause is in fact stronger than `PreservesDirSups`, needing no
directedness. -/
theorem cvn_faithful_6 [MeasurableSpace (characterSpace ℂ A)]
    (hms : ∀ s : Set (characterSpace ℂ A), MeasurableSet s ↔ AlmostClopen s)
    (μ : Measure (characterSpace ℂ A)) [IsFiniteMeasure μ]
    (hμ : ∀ s : Set (characterSpace ℂ A), AlmostClopen s →
      (μ s = 0 ↔ IsMeagre s)) :
    ∃ e : C(characterSpace ℂ A, ℂ) ≃⋆ₐ[ℂ] Linfty μ,
      (∀ f : C(characterSpace ℂ A, ℂ),
        e f = Linfty.mk μ (f : characterSpace ℂ A → ℂ)) ∧
      PreservesDirSups ⇑e ∧
      (∀ f : C(characterSpace ℂ A, ℂ),
        Linfty.integralNP (e f) = ∫ x, f x ∂μ) := by
  have := vn_spectrum_extremally_disconnected A
  obtain ⟨e, he⟩ := ContRep.exists_linftyEquiv hms μ hμ
  refine ⟨e, he, starAlgEquiv_preservesDirSups e, fun f => ?_⟩
  rw [he f, Linfty.coe_integralNP]
  exact Linfty.integral_mk (ContRep.bm_coe hms f)
end CVNFaithful

end Topologies

end Theses.A.VN
