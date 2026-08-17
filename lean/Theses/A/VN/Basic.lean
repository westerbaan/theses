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

Statements only; every proof is `sorry`.  See CONVENTIONS.md for the
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

variable {I : Type*} (𝒜 : I → Type u) [∀ i, CStarAlgebra (𝒜 i)]
  [∀ i, Nontrivial (𝒜 i)]

/-- The direct sum `⊕ᵢ 𝒜ᵢ = lp 𝒜 ∞` of unital C*-algebras is a unital
C*-algebra (Mathlib provides all the pieces but only registers the
commutative unital instance; this mirrors `lp.inftyCommCStarAlgebra`). -/
noncomputable instance : CStarAlgebra (lp 𝒜 ∞) where

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
`lp 𝒜 ∞`) of a family of von Neumann algebras is a von Neumann algebra. -/
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

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 1:
computation rules `(|n⟩⟨m|)* = |m⟩⟨n|` and
`|n⟩⟨m| |l⟩⟨k| = δ_{m,l} |n⟩⟨k|`. -/
private theorem ketbraNat_apply (n m : ℕ) (z : ℓ²) :
    ketbraNat n m z = (⟪lp.single 2 m (1 : ℂ), z⟫ : ℂ) • lp.single 2 n (1 : ℂ) :=
  rfl

private theorem inner_single_nat (m l : ℕ) :
    (⟪(lp.single 2 m (1 : ℂ) : ℓ²), (lp.single 2 l (1 : ℂ) : ℓ²)⟫ : ℂ) =
      if m = l then 1 else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  simp [Pi.single_apply]

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

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 11: `B(ℓ²)`
is not ultraweakly complete: there is an ultraweakly Cauchy net (built from
an unbounded functional on `ℓ²` via Riesz representation on finite
dimensional subspaces) with no ultraweak limit. -/
theorem vn_counterexamples_11 :
    ∃ (ι : Type) (l : Filter ι), l.NeBot ∧ ∃ x : ι → (ℓ² →L[ℂ] ℓ²),
      (∀ ω : NPFunctional (ℓ² →L[ℂ] ℓ²), Cauchy (l.map fun i => ω (x i))) ∧
      ¬∃ T, UWTendsto x l T :=
  sorry

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
/-- A map into a von Neumann algebra is ultraweakly continuous as soon as
every np-functional composed with it is: the ultraweak topology of the
codomain *is* the initial topology of the np-functionals (**42III**). -/
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

/-- **34XIV** (`cp-cs`, cstar.tex:5629, Kadison's inequality) for an
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

/-- **44XV** (`p-uwcont`, vn.tex:799, Exercise), conclusion: `b ↦ a* b a` is
ultraweakly continuous for every `a` in a von Neumann algebra (it is normal
by **44VIII**). -/
theorem p_uwcont_ad [VonNeumannAlgebra A] (a : A) :
    @Continuous A A (ultraweak A) (ultraweak A) fun b => star a * b * a := by
  refine ((p_uwcont (adPositive a)).out 2 0).mp ?_
  intro D s hne hdir hlub
  have hh : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D :=
    ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hsup : dirSup D hh = s := (isLUB_dirSup D hh).unique hlub
  have := ad_normal a D hh
  rwa [hsup] at this

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

/-- **45I** (vn.tex:829, Exercise), part 2: the converse fails — there is a
normal positive map (e.g. the transpose on `B(ℓ²)`) that is not
ultrastrongly continuous. -/
theorem normal_not_us_cont :
    ∃ f : (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) →ₚ[ℂ]
        (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      PreservesDirSups ⇑f ∧
        ¬@Continuous _ _ (ultrastrong _) (ultrastrong _) ⇑f :=
  sorry

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

/-- **45IV** (`mult-uws-cont`, vn.tex:868, Exercise), part 1: `a ↦ b* a b`
is ultrastrongly continuous for every `b` in a von Neumann algebra. -/
theorem mult_uws_cont_ad [VonNeumannAlgebra A] (b : A) :
    @Continuous A A (ultrastrong A) (ultrastrong A) fun a => star b * a * b := by
  -- `‖b* x b‖_ω = ‖b* x‖_{b*ω} ≤ ‖b‖ ‖x‖_{b*ω}`.  (The thesis obtains this
  -- from `cp_uscont` and `ad_cp`; the direct estimate is shorter and avoids
  -- the passage through complete positivity.)
  refine continuous_ultrastrong_of_omegaNorm_bound (fun x y => by noncomm_ring) ?_
  intro ω
  refine ⟨conjNP b ω, ‖b‖, norm_nonneg b, fun x => ?_⟩
  rw [omegaNorm_mul_right]
  simpa using omegaNorm_mul_le (conjNP b ω) (star b) x

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
categorical structure itself is not bundled here — the product (47IV) and
equaliser (47V) below are stated through their universal properties, which
is what the thesis uses.

**47VI** (`vn-effectus`, vn.tex:1017): the sketch that `(W*_cpsu)^op` is an
effectus refers forward to the precise treatment in thesis B (eff.tex);
nothing is formalized here. -/

section Products

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

section Elementary

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **47V** (`vn-equalisers`, vn.tex:1006, Exercise): for nmiu-maps
`f, g : A → B` between von Neumann algebras, the set
`E = {a ∈ A | f(a) = g(a)}` is (the carrier of) a von Neumann subalgebra of
`A`; its inclusion is then automatically the equaliser of `f` and `g` in
`W*_miu` and `W*_cpsu`. -/
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

/-- A ∗-homomorphism between C*-algebras is positive. -/
theorem starAlgHom_nonneg (φ : A →⋆ₐ[ℂ] C) {x : A} (hx : 0 ≤ x) : 0 ≤ φ x := by
  have hs : CFC.sqrt x * CFC.sqrt x = x := CFC.sqrt_mul_sqrt_self x hx
  have hsa : IsSelfAdjoint (CFC.sqrt x) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)
  have h : φ x = star (φ (CFC.sqrt x)) * φ (CFC.sqrt x) := by
    rw [← map_star, hsa.star_eq, ← map_mul, hs]
  rw [h]
  exact star_mul_self_nonneg _

/-- A ∗-homomorphism between C*-algebras is monotone. -/
theorem starAlgHom_mono (φ : A →⋆ₐ[ℂ] C) {x y : A} (hxy : x ≤ y) : φ x ≤ φ y := by
  have h := starAlgHom_nonneg φ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  exact sub_nonneg.mp h

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

/-- **48VI**.2 in its general C*-form: an *injective* ∗-homomorphism between
C*-algebras reflects the order (hence is an order embedding). -/
theorem starAlgHom_le_iff (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) {x y : A} :
    φ x ≤ φ y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => starAlgHom_mono φ h⟩
  set z : A := y - x with hz
  have hφz : (0 : C) ≤ φ z := by rw [hz, map_sub]; exact sub_nonneg.mpr h
  have hzsa : IsSelfAdjoint z := by
    have h1 : φ (star z) = φ z := by rw [map_star, (IsSelfAdjoint.of_nonneg hφz).star_eq]
    exact hφ h1
  have hn0 : negPart z = 0 := by
    have hnn : (0 : A) ≤ negPart z := CFC.negPart_nonneg z
    have hcube : (0 : A) ≤ negPart z ^ 3 := CStarAlgebra.pow_nonneg hnn 3
    have hnsa : IsSelfAdjoint (negPart z) := IsSelfAdjoint.of_nonneg hnn
    have hconj : negPart z * z * negPart z = -(negPart z ^ 3) := by
      have hd : posPart z - negPart z = z := CFC.posPart_sub_negPart z hzsa
      have hnp : negPart z * posPart z = 0 := CFC.negPart_mul_posPart z
      calc negPart z * z * negPart z
          = negPart z * (posPart z - negPart z) * negPart z := by rw [hd]
        _ = negPart z * posPart z * negPart z - negPart z ^ 3 := by noncomm_ring
        _ = -(negPart z ^ 3) := by rw [hnp, zero_mul, zero_sub]
    have hle : φ (negPart z ^ 3) ≤ 0 := by
      have hpos : (0 : C) ≤ star (φ (negPart z)) * φ z * φ (negPart z) :=
        star_left_conjugate_nonneg hφz _
      rw [← map_star, hnsa.star_eq] at hpos
      have hrw : φ (negPart z) * φ z * φ (negPart z) = -φ (negPart z ^ 3) := by
        rw [← map_mul, ← map_mul, hconj, map_neg]
      rw [hrw] at hpos
      exact neg_nonneg.mp hpos
    have hzero : φ (negPart z ^ 3) = 0 :=
      le_antisymm hle (starAlgHom_nonneg φ hcube)
    have h3 : negPart z ^ 3 = 0 := by
      have := hφ (by rw [hzero, map_zero] : φ (negPart z ^ 3) = φ 0)
      exact this
    exact eq_zero_of_pow_three_eq_zero hnsa h3
  have hzpos : (0 : A) ≤ z := by
    have hd : posPart z - negPart z = z := CFC.posPart_sub_negPart z hzsa
    rw [hn0, sub_zero] at hd
    rw [← hd]
    exact CFC.posPart_nonneg z
  rw [hz] at hzpos
  exact sub_nonneg.mp hzpos


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

theorem gnsElemVecs_separating (R : gnsHilb A →L[ℂ] gnsHilb A)
    (h : ∀ y ∈ gnsElemVecs (A := A), R y = 0) : R = 0 :=
  gnsElemVecsFam_separating _ R h

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

/-- **48VI**.1 in its general form: the image of an injective normal
∗-homomorphism between von Neumann algebras is a von Neumann subalgebra. -/
theorem isVNSubalgebra_range (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
    (hn : PreservesDirSups ⇑φ) : IsVNSubalgebra C φ.range := by
  classical
  have hnorm : ∀ x : A, ‖φ x‖ = ‖x‖ := NonUnitalStarAlgHom.norm_map φ hφ
  have hiso : Isometry (φ : A → C) := NonUnitalStarAlgHom.isometry φ hφ
  have hrange : ((φ.range : StarSubalgebra ℂ C) : Set C) = Set.range (φ : A → C) := by
    ext x
    exact ⟨fun hx => hx, fun hx => hx⟩
  have hsaMap : ∀ x : selfAdjoint A, IsSelfAdjoint (φ (x : A)) := fun x => by
    show star (φ (x : A)) = φ (x : A)
    rw [← map_star, x.2.star_eq]
  set saMap : selfAdjoint A → selfAdjoint C := fun x => ⟨φ (x : A), hsaMap x⟩ with hsaMapDef
  refine ⟨?_, ?_⟩
  · rw [hrange]
    exact (hiso.isUniformInducing.isComplete_range).isClosed
  intro D s hDsub hne hdir hlub
  -- every member of `D` comes from a self-adjoint element of `A`
  have hpull : ∀ d ∈ D, ∃ x : selfAdjoint A, saMap x = d := by
    intro d hd
    have hmem : (d : C) ∈ (φ.range : Set C) := hDsub d hd
    rw [hrange] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcsa : IsSelfAdjoint c := by
      refine hφ ?_
      rw [map_star, hc, d.2.star_eq]
    exact ⟨⟨c, hcsa⟩, Subtype.ext hc⟩
  -- pass to the cofinal tail above a fixed `d₀ ∈ D`
  obtain ⟨d₀, hd₀⟩ := hne
  set Dt : Set (selfAdjoint C) := {d | d ∈ D ∧ d₀ ≤ d} with hDtDef
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
  set D' : Set (selfAdjoint A) := saMap ⁻¹' Dt with hD'Def
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
        ((starAlgHom_le_iff φ hφ).mp (Subtype.coe_le_coe.mpr (hz ▸ hxd)))
    · exact Subtype.coe_le_coe.mp
        ((starAlgHom_le_iff φ hφ).mp (Subtype.coe_le_coe.mpr (hz ▸ hyd)))
  -- the pullback is norm bounded, hence order bounded
  set M : ℝ := ‖(s : C) - (d₀ : C)‖ + ‖(d₀ : C)‖ with hMDef
  have hM0 : 0 ≤ M := by positivity
  have hD'bdd : BddAbove D' := by
    have hsa : IsSelfAdjoint (algebraMap ℂ A ((M : ℝ) : ℂ)) :=
      IsSelfAdjoint.of_nonneg (Theses.A.CStar.algebraMap_ofReal_nonneg hM0)
    refine ⟨⟨algebraMap ℂ A ((M : ℝ) : ℂ), hsa⟩, fun x hx => ?_⟩
    have hd : saMap x ∈ Dt := hx
    have h1 : (0 : C) ≤ (saMap x : C) - (d₀ : C) :=
      sub_nonneg.mpr (Subtype.coe_le_coe.mpr hd.2)
    have h2 : (saMap x : C) - (d₀ : C) ≤ (s : C) - (d₀ : C) :=
      sub_le_sub_right (Subtype.coe_le_coe.mpr (hDtlub.1 hd)) _
    have h3 : ‖(saMap x : C) - (d₀ : C)‖ ≤ ‖(s : C) - (d₀ : C)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le h1 h2
    have h4 : ‖(saMap x : C)‖ ≤ M := by
      have := norm_add_le ((saMap x : C) - (d₀ : C)) ((d₀ : C))
      simp only [sub_add_cancel] at this
      exact le_trans this (by rw [hMDef]; gcongr)
    have h5 : ‖(x : A)‖ ≤ M := by rw [← hnorm]; exact h4
    refine Subtype.coe_le_coe.mp ?_
    refine le_trans ?_ (Theses.A.CStar.algebraMap_ofReal_mono h5)
    have := IsSelfAdjoint.le_algebraMap_norm_self x.2
    rwa [Theses.A.CStar.algebraMap_real_eq] at this
  -- the supremum of the pullback maps onto `s`
  set t : selfAdjoint A := dirSup D' ⟨hD'ne, hD'dir, hD'bdd⟩ with htDef
  have htlub : IsLUB D' t := isLUB_dirSup D' ⟨hD'ne, hD'dir, hD'bdd⟩
  have hkey := hn D' t hD'ne hD'dir htlub
  have hsets : (fun x : selfAdjoint A => φ (x : A)) '' D' = Subtype.val '' Dt := by
    rw [← himg, ← Set.image_comp]
    rfl
  rw [hsets] at hkey
  have hslub : IsLUB (Subtype.val '' Dt) ((s : selfAdjoint C) : C) :=
    isLUB_coe_of_isLUB hDtne hDtlub
  have hst : φ (t : A) = (s : C) := hkey.unique hslub
  show (s : C) ∈ (φ.range : Set C)
  rw [hrange, ← hst]
  exact ⟨(t : A), rfl⟩

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
/-- **48V** (`varrho-Omega-normal`, vn.tex:1113, Exercise): the direct-sum
GNS representation `ρ_Ω` of any collection `Ω` of np-functionals on a von
Neumann algebra is normal (rendered, as in **48III**, as the existence of a
normal representation in which every `ω ∈ Ω` is a vector functional). -/
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

/-- **48VI** (`injective-nmiu-iso-on-image`, vn.tex:1120, Lemma), part 2: an
injective nmiu-map `f` restricts to an nmiu-isomorphism onto its image; in
particular it is an order embedding (whence its inverse on the image is
normal). -/
theorem injective_nmiu_iso_on_image_2 [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NMIUMap A B) (hf : Function.Injective f)
    (a b : A) : f a ≤ f b ↔ a ≤ b :=
  starAlgHom_le_iff f.toStarAlgHom hf

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
-- FIXME(typecheck): not converted — the C*-algebra `B^a(X)` (cstar.tex
32XIII, `bax-cstar`) has no Mathlib counterpart and is not formalized in
`Theses/A/CStar`; its rôle here (producing `M_N(𝒜)`) is covered by the
direct statement 49IV below. -/

/-! ### Auxiliary machinery for **49IV**: the `𝒜`-valued quadratic form of a
matrix

The thesis proves 49IV.1 by way of 49II (`bah-vn`), i.e. by realising
`M_N(𝒜)` as `B^a(𝒜^N)`; `B^a(X)` has no Mathlib counterpart and is not
formalized (see the FIXME above), so the supremum is constructed here
directly, out of the same ingredient that makes 49II work: the `𝒜`-valued
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
ultraweakly and ultrastrongly continuous; for `a = b` it is moreover normal
(and completely positive).  (Placed after the second half, which its proof
uses.) -/
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

/-- **51VII** (vn.tex:1581, Proposition), part 1: a C*-algebra `A` with a
faithful positive functional `τ` such that every bounded ascending sequence
of self-adjoint elements has a supremum preserved by `τ` is a von Neumann
algebra. -/
theorem vna_of_faithful_countably_normal_1 (τ : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, 0 ≤ a → τ a = 0 → a = 0)
    (hsup : ∀ a : ℕ → selfAdjoint A, Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint A, IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => τ (a n : A)) (τ (s : A))) :
    VonNeumannAlgebra A :=
  sorry

/-- **51VII** (vn.tex:1581, Proposition), part 2: such a `τ` is moreover
normal. -/
theorem vna_of_faithful_countably_normal_2 (τ : A →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : A, 0 ≤ a → τ a = 0 → a = 0)
    (hsup : ∀ a : ℕ → selfAdjoint A, Monotone a → BddAbove (Set.range a) →
      ∃ s : selfAdjoint A, IsLUB (Set.range a) s ∧
        IsLUB (Set.range fun n => τ (a n : A)) (τ (s : A))) :
    PreservesDirSups ⇑τ :=
  sorry

variable (X : Type u) [MeasurableSpace X] in
/-- A function `X → ℂ` on a measure(able) space that is measurable and
bounded — a member of the thesis's `𝓛^∞(X)` (vn.tex 51II). -/
def IsBoundedMeasurable (f : X → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

/-- **51IX** (`Linfty-vn`, vn.tex:1638, Corollary): for a finite complete
measure space `X`, the C*-algebra `L^∞(X)` — bounded measurable functions
modulo equality almost everywhere — is a commutative von Neumann algebra on
which integration is a faithful normal positive functional.  (Since Mathlib
has no C*-algebra of classes of bounded measurable functions, `L^∞(X)` is
rendered as an existentially quantified commutative von Neumann algebra `𝒜`
with a quotient map `q` from `𝓛^∞(X)`.) -/
theorem Linfty_vn (X : Type u) [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (hμ : μ.IsComplete) :
    ∃ (𝒜 : Type u) (_ : CommCStarAlgebra 𝒜) (_ : PartialOrder 𝒜)
      (_ : StarOrderedRing 𝒜) (q : (X → ℂ) → 𝒜) (τ : 𝒜 → ℂ),
      VonNeumannAlgebra 𝒜 ∧
      -- `q` is a surjective miu-map on `𝓛^∞(X)` with kernel the a.e.-null
      -- functions:
      (∀ y : 𝒜, ∃ f, IsBoundedMeasurable X f ∧ q f = y) ∧
      (∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
        q (f + g) = q f + q g ∧ q (f * g) = q f * q g ∧
          q (star f) = star (q f)) ∧
      q 1 = 1 ∧
      (∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0)) ∧
      -- integration descends to a faithful normal positive functional:
      (∃ τ' : NPFunctional 𝒜, ⇑τ' = τ) ∧
      (∀ y : 𝒜, 0 ≤ y → τ y = 0 → y = 0) ∧
      (∀ f, IsBoundedMeasurable X f → τ (q f) = ∫ x, f x ∂μ) :=
  sorry

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
of Lebesgue measure `1`. -/
theorem meagre_full_measure :
    ∃ s : Set ℝ, s ⊆ Set.Icc 0 1 ∧ IsMeagre s ∧ volume s = 1 := by
  -- As in the thesis: cover `ℚ` by open (hence dense) sets `Uₙ` of measure
  -- `< 1/(n+1)`; then `B = ⋂ₙ Uₙ` is negligible and comeagre, and
  -- `[0,1] \ B` is meagre of measure `1`.  (The thesis writes down explicit
  -- intervals around an enumeration of `ℚ ∩ [0,1]`; we get the `Uₙ` from
  -- outer regularity of Lebesgue measure instead.)
  have hQ0 : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range _).measure_zero _
  have hpos : ∀ n : ℕ, volume (Set.range ((↑) : ℚ → ℝ)) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    rw [hQ0]
    exact ENNReal.inv_pos.mpr (by simp)
  choose U hUsub hUopen hUvol using fun n : ℕ =>
    Set.exists_isOpen_lt_of_lt (μ := volume) (Set.range ((↑) : ℚ → ℝ))
      (((n : ℝ≥0∞) + 1)⁻¹) (hpos n)
  have hBres : (⋂ n : ℕ, U n) ∈ residual ℝ :=
    countable_iInter_mem.mpr fun n =>
      residual_of_dense_open (hUopen n) (Rat.denseRange_cast.mono (hUsub n))
  have hB0 : volume (⋂ n : ℕ, U n) = 0 := by
    by_contra h
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
    have h1 : volume (⋂ n : ℕ, U n) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      lt_of_le_of_lt (measure_mono (Set.iInter_subset U n)) (hUvol n)
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (le_add_right le_rfl)
    exact absurd (h1.trans_le h2) (not_lt.mpr hn.le)
  refine ⟨Set.Icc 0 1 \ (⋂ n : ℕ, U n), Set.sdiff_subset, ?_, ?_⟩
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

section CVNFaithful

variable {A : Type*} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A]

open WeakDual

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
      @Measure.IsComplete _ (almostClopenMS _) μ :=
  sorry

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
      ∃ E : Set (characterSpace ℂ A), μ E = 0 ∧ ∀ x ∈ Eᶜ, ContinuousAt f x :=
  sorry

/-- **54XI** (`cvn-faithful`, vn.tex:2014, Theorem), part 3: the diagram
commutes: `∫ f dμ = ω(γ_A⁻¹(f))` for every continuous `f` on `spec A`.
(The full statement — that `f ↦ f°` is an nmiu-isomorphism
`C(spec A) → L^∞(spec A)` — is not rendered since `L^∞` has no Mathlib
carrier; cf. 51IX.) -/
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
    ∫ x, f x ∂μ = ω ((gelfandStarTransform A).symm f) :=
  sorry

/-! **54XIII** (vn.tex:2172): transition to the projections needed for the
full classification (70III, `Theses/A/VN/Projections.lean`) — nothing to
formalize. -/

end CVNFaithful

end Topologies

end Theses.A.VN
