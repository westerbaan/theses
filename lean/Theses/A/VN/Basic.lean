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

/-- The "balls" `{a | ‖a - b‖_ω < ε}` of **42III** are ultrastrong
neighbourhoods of `b` (they are among the generators of the topology). -/
theorem ultrastrong_ball_mem_nhds (ω : NPFunctional A) (b : A) {ε : ℝ}
    (hε : 0 < ε) : {a : A | omegaNorm A ω (a - b) < ε} ∈ @nhds A (ultrastrong A) b :=
  @IsOpen.mem_nhds A (ultrastrong A) _ _
    (TopologicalSpace.isOpen_generateFrom_of_mem ⟨ω, b, ε, hε, rfl⟩) (by simp [hε])

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

/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 2: the
C*-algebra `B(H)` of bounded operators on a Hilbert space `H` is a von
Neumann algebra: it has bounded directed suprema of self-adjoint elements by
cstar.tex 37IX, and the vector states are order separating by cstar.tex
25III. -/
instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : VonNeumannAlgebra (H →L[ℂ] H) := sorry

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

/-- **42V** (`von-neumann-examples`, vn.tex:262, Examples), part 3 (also
**47IV**, `vn-products`, part 1): the direct sum `⊕ᵢ 𝒜ᵢ` (Mathlib:
`lp 𝒜 ∞`) of a family of von Neumann algebras is a von Neumann algebra. -/
instance vonNeumannAlgebra_lp_infty [∀ i, VonNeumannAlgebra (𝒜 i)] :
    VonNeumannAlgebra (lp 𝒜 ∞) := sorry

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
theorem vn_counterexamples_1 (k l m n : ℕ) :
    star (ketbraNat n m) = ketbraNat m n ∧
      ketbraNat n m * ketbraNat l k =
        (if m = l then ketbraNat n k else 0) :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 2 (first
half): `⋁_N ∑_{n≤N} |n⟩⟨n| = 1` in `B(ℓ²)`. -/
theorem vn_counterexamples_2_sup :
    IsLUB {T : ℓ² →L[ℂ] ℓ² |
        ∃ N : ℕ, T = ∑ n ∈ Finset.range N, ketbraNat n n}
      1 :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 2 (second
half): `(|n⟩⟨n|)_n` converges ultrastrongly (hence ultraweakly) to `0`; so
ultrastrong convergence does not imply norm convergence, and `‖·‖` is not
ultraweakly continuous. -/
theorem vn_counterexamples_2_tendsto :
    USTendsto (fun n : ℕ => ketbraNat n n) atTop 0 :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 3: already in
`ℂ`, the sequence `(e^{in})_n` does not converge ultraweakly, although the
products `e^{-in}·e^{in} = 1` are norm-bounded and converge; so ultraweak
convergence of `(b_α* b_α)_α` and norm-boundedness do not imply ultrastrong
convergence of `(b_α)_α`. -/
theorem vn_counterexamples_3 :
    ¬∃ z : ℂ, UWTendsto (fun n : ℕ => Complex.exp (Complex.I * n)) atTop z :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 4 (first
half): `(|0⟩⟨n|)_n` converges ultrastrongly to `0`. -/
theorem vn_counterexamples_4_ket :
    USTendsto (fun n : ℕ => ketbraNat 0 n) atTop 0 :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 4 (second
half): `(|n⟩⟨0|)_n` converges ultraweakly to `0` but does not converge
ultrastrongly at all. -/
theorem vn_counterexamples_4_bra :
    UWTendsto (fun n : ℕ => ketbraNat n 0) atTop 0 ∧
      ¬∃ T : ℓ² →L[ℂ] ℓ², USTendsto (fun n : ℕ => ketbraNat n 0) atTop T :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 4
(conclusion): `a ↦ a*` is not ultrastrongly continuous on `B(ℓ²)`. -/
theorem vn_counterexamples_4_star :
    ¬@Continuous (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²)
        (ultrastrong _) (ultrastrong _) star :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 5: the unit
ball of `B(ℓ²)` is not ultrastrongly compact (the sequence `(|0⟩⟨n|)_n` has
no ultrastrongly convergent subnet). -/
theorem vn_counterexamples_5 :
    ¬@IsCompact (ℓ² →L[ℂ] ℓ²) (ultrastrong _)
        (Metric.closedBall (0 : ℓ² →L[ℂ] ℓ²) 1) :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6:
`|n⟩⟨0| + |0⟩⟨n| → 0` ultraweakly while its squares converge ultraweakly to
`|0⟩⟨0| ≠ 0`. -/
theorem vn_counterexamples_6 :
    UWTendsto (fun n : ℕ => ketbraNat n 0 + ketbraNat 0 n) atTop 0 ∧
      UWTendsto (fun n : ℕ => (ketbraNat n 0 + ketbraNat 0 n) ^ 2) atTop
        (ketbraNat 0 0) :=
  sorry

/-- **43II** (`vn-counterexamples`, vn.tex:374, Exercise), part 6
(conclusion): squaring — hence also multiplication jointly, `|·|`, and
`√·` (part 8) — is not ultraweakly continuous on `B(ℓ²)`. -/
theorem vn_counterexamples_6_sq :
    ¬@Continuous (ℓ² →L[ℂ] ℓ²) (ℓ² →L[ℂ] ℓ²) (ultraweak _) (ultraweak _)
        (fun a => a * a) :=
  sorry

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

/-- **44VIII** (`ad-normal`, vn.tex:704, Proposition):
`⋁_{d∈D} a* d a = a* (⋁D) a` for every bounded directed set `D` of
self-adjoint elements and every `a ∈ A` (stated as an `IsLUB` in `A`; upper
bounds of sets of self-adjoint elements are automatically self-adjoint). -/
theorem ad_normal [VonNeumannAlgebra A] (a : A) (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) :
    IsLUB ((fun d : selfAdjoint A => star a * (d : A) * a) '' D)
      (star a * ((dirSup D h : selfAdjoint A) : A) * a) :=
  sorry

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), preliminary claim:
the np-functionals on a von Neumann algebra are not only faithful but order
separating. -/
theorem np_orderSeparating [VonNeumannAlgebra A] (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : ∀ ω : NPFunctional A, ω a ≤ ω b) : a ≤ b :=
  sorry

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), part 1: the
ultraweak and ultrastrong topologies are Hausdorff. -/
theorem vn_positive_basic_1 [VonNeumannAlgebra A] :
    @T2Space A (ultraweak A) ∧ @T2Space A (ultrastrong A) :=
  sorry

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), part 2: the
positive cone, the self-adjoint part, and the set of effects are ultraweakly
(hence, by **43I**, ultrastrongly) closed. -/
theorem vn_positive_basic_2 [VonNeumannAlgebra A] :
    @IsClosed A (ultraweak A) {a : A | 0 ≤ a} ∧
      @IsClosed A (ultraweak A) {a : A | IsSelfAdjoint a} ∧
      @IsClosed A (ultraweak A) (effects A) :=
  sorry

/-- **44XI** (`vn-positive-basic`, vn.tex:756, Exercise), part 3: the unit
ball is ultrastrongly closed.  (It is ultraweakly closed too, but that is
seen only in 73VIII, `ultraclosed`.) -/
theorem vn_positive_basic_3 [VonNeumannAlgebra A] :
    @IsClosed A (ultrastrong A) (Metric.closedBall (0 : A) 1) :=
  sorry

/-- **44XIII** (`vna-supremum-commutes`, vn.tex:787): if `a` commutes with
every member of a bounded directed set `D` of self-adjoint elements, then
`a` commutes with `⋁D`. -/
theorem vna_supremum_commutes [VonNeumannAlgebra A]
    (D : Set (selfAdjoint A))
    (h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D) (a : A)
    (hc : ∀ d ∈ D, a * (d : A) = (d : A) * a) :
    a * ((dirSup D h : selfAdjoint A) : A) =
      ((dirSup D h : selfAdjoint A) : A) * a :=
  sorry

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
       ∀ ω : NPFunctional B, PreservesDirSups fun a => ω (f a)] :=
  sorry

/-- **44XV** (`p-uwcont`, vn.tex:799, Exercise), conclusion: `b ↦ a* b a` is
ultraweakly continuous for every `a` in a von Neumann algebra (it is normal
by **44VIII**). -/
theorem p_uwcont_ad [VonNeumannAlgebra A] (a : A) :
    @Continuous A A (ultraweak A) (ultraweak A) fun b => star a * b * a :=
  sorry

/-! ## Parsec 450 -/

/-- **45I** (vn.tex:829, Exercise), part 1: a positive linear map between
von Neumann algebras which is ultrastrongly continuous on `[0,1]_A` is
normal. -/
theorem us_cont_normal [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (f : A →ₚ[ℂ] B)
    (h : @ContinuousOn A B (ultrastrong A) (ultrastrong B) f (effects A)) :
    PreservesDirSups ⇑f :=
  sorry

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
    @Continuous A B (ultrastrong A) (ultrastrong B) ⇑f :=
  sorry

/-- **45IV** (`mult-uws-cont`, vn.tex:868, Exercise), part 1: `a ↦ b* a b`
is ultrastrongly continuous for every `b` in a von Neumann algebra. -/
theorem mult_uws_cont_ad [VonNeumannAlgebra A] (b : A) :
    @Continuous A A (ultrastrong A) (ultrastrong A) fun a => star b * a * b :=
  sorry

/-- **45IV** (`mult-uws-cont`, vn.tex:868, Exercise), part 2: multiplication
by a fixed element, `b ↦ ab` and `b ↦ ba`, is ultraweakly and ultrastrongly
continuous. -/
theorem mult_uws_cont [VonNeumannAlgebra A] (a : A) :
    (@Continuous A A (ultraweak A) (ultraweak A) fun b => a * b) ∧
      (@Continuous A A (ultraweak A) (ultraweak A) fun b => b * a) ∧
      (@Continuous A A (ultrastrong A) (ultrastrong A) fun b => a * b) ∧
      (@Continuous A A (ultrastrong A) (ultrastrong A) fun b => b * a) :=
  sorry

/-- **45VI** (`mult-jus-cont`, vn.tex:892, Proposition): if nets `(a_α)_α`,
`(b_α)_α` converge ultrastrongly to `a`, `b` respectively and `(a_α)_α` is
norm-bounded, then `(a_α b_α)_α` converges ultrastrongly to `ab`. -/
theorem mult_jus_cont [VonNeumannAlgebra A] {ι : Type*} {l : Filter ι}
    (x y : ι → A) (a b : A) (hx : USTendsto x l a) (hy : USTendsto y l b)
    (hbdd : ∃ C : ℝ, ∀ i, ‖x i‖ ≤ C) :
    USTendsto (fun i => x i * y i) l (a * b) :=
  sorry

/-! ## Parsec 460 -/

/-- **46II** (`usconv`, vn.tex:930, Exercise): a net `(b_α)_α` converges
ultrastrongly to `b` iff both `b_α* b_α → b* b` and `b_α → b`
ultraweakly. -/
theorem usconv [VonNeumannAlgebra A] {ι : Type*} (x : ι → A) (l : Filter ι)
    (b : A) :
    USTendsto x l b ↔
      UWTendsto (fun i => star (x i) * x i) l (star b * b) ∧
        UWTendsto x l b :=
  sorry

/-- **46III** (`npuws`, vn.tex:940, Exercise): for a positive functional `ω`
on a von Neumann algebra, the following are equivalent: (1) `ω` is normal;
(2) `ω` is ultraweakly continuous; (3) `ω` is ultrastrongly continuous. -/
theorem npuws [VonNeumannAlgebra A] (ω : A →ₚ[ℂ] ℂ) :
    List.TFAE
      [PreservesDirSups ⇑ω,
       @Continuous A ℂ (ultraweak A) _ ⇑ω,
       @Continuous A ℂ (ultrastrong A) _ ⇑ω] :=
  sorry

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
    PreservesDirSups fun a : lp 𝒜 ∞ => (a : ∀ i, 𝒜 i) j :=
  sorry

/-- **47IV** (`vn-products`, vn.tex:988, Exercise), part 3 (`W*_miu`):
`⊕ᵢ𝒜ᵢ` with the projections `π_j` is the product of the `𝒜ᵢ` in `W*_miu`:
every family of nmiu-maps `f_i : B → 𝒜ᵢ` factors through a unique nmiu-map
`g : B → ⊕ᵢ𝒜ᵢ`. -/
theorem vn_products_nmiu {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : ∀ i, NMIUMap B (𝒜 i)) :
    ∃! g : NMIUMap B (lp 𝒜 ∞), ∀ (j : I) (b : B),
      ((g b : lp 𝒜 ∞) : ∀ i, 𝒜 i) j = f j b :=
  sorry

/-- **47IV** (`vn-products`, vn.tex:988, Exercise), part 3 (`W*_cpsu`):
`⊕ᵢ𝒜ᵢ` is also the product in `W*_cpsu`: every family of ncpsu-maps
`f_i : B → 𝒜ᵢ` factors through a unique ncpsu-map `g : B → ⊕ᵢ𝒜ᵢ`. -/
theorem vn_products_ncpsu {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [VonNeumannAlgebra B] (f : ∀ i, NCPSUMap B (𝒜 i)) :
    ∃! g : NCPSUMap B (lp 𝒜 ∞), ∀ (j : I) (b : B),
      ((g.toNCPMap b : lp 𝒜 ∞) : ∀ i, 𝒜 i) j = (f j).toNCPMap b :=
  sorry

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
      (S : Set A) = {a : A | f a = g a} :=
  sorry

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
      ∀ ω ∈ Ω, PreservesDirSups fun a => ω (f a) :=
  sorry

/-- **48III** (vn.tex:1091, Proposition): the GNS representation
`ρ_ω : A → B(H_ω)` of an np-functional `ω` on a von Neumann algebra is
normal.  (The GNS construction, cstar.tex 30VI, is not formalized, so this
is rendered as: `ω` admits a *normal* cyclic representation.) -/
theorem gns_normal [VonNeumannAlgebra A] (ω : NPFunctional A) :
    ∃ (ι : Type u) (ρ : MIUMap A
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
      (ξ : lp (fun _ : ι => ℂ) 2),
      (∀ a : A, ω a = ⟪ξ, ρ a ξ⟫) ∧
        Dense (Set.range fun a : A => ρ a ξ) ∧
        PreservesDirSups ⇑ρ :=
  sorry

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
          ∀ a : A, ω a = ⟪ξ, ρ a ξ⟫ :=
  sorry

/-- **48VI** (`injective-nmiu-iso-on-image`, vn.tex:1120, Lemma), part 1:
the image of an injective nmiu-map `f : A → B` between von Neumann algebras
is a von Neumann subalgebra of `B`. -/
theorem injective_nmiu_iso_on_image_1 [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NMIUMap A B) (hf : Function.Injective f) :
    IsVNSubalgebra B f.toStarAlgHom.range :=
  sorry

/-- **48VI** (`injective-nmiu-iso-on-image`, vn.tex:1120, Lemma), part 2: an
injective nmiu-map `f` restricts to an nmiu-isomorphism onto its image; in
particular it is an order embedding (whence its inverse on the image is
normal). -/
theorem injective_nmiu_iso_on_image_2 [VonNeumannAlgebra A]
    [VonNeumannAlgebra B] (f : NMIUMap A B) (hf : Function.Injective f)
    (a b : A) : f a ≤ f b ↔ a ≤ b :=
  sorry

/-- **48VIII** (`ngns`, vn.tex:1144, Theorem (normal Gelfand–Naimark)):
every von Neumann algebra is nmiu-isomorphic to a von Neumann algebra of
operators on a Hilbert space: there is an injective nmiu-map into some
`B(ℓ²(ι))` whose range is a von Neumann subalgebra. -/
theorem ngns (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [VonNeumannAlgebra A] :
    ∃ (ι : Type u) (f : NMIUMap A
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)),
      Function.Injective f ∧ IsVNSubalgebra _ f.toStarAlgHom.range :=
  sorry

/-! ## Parsec 490: matrices over a von Neumann algebra

**49II** (`bah-vn`, vn.tex:1177, Theorem): for a von Neumann algebra `𝒜`,
the C*-algebra `B^a(X)` of bounded adjointable module maps on a self-dual
Hilbert `𝒜`-module `X` is a von Neumann algebra, and `⟨x,(·)x⟩` is normal
for every `x ∈ X`.
-- FIXME(typecheck): not converted — the C*-algebra `B^a(X)` (cstar.tex
32XIII, `bax-cstar`) has no Mathlib counterpart and is not formalized in
`Theses/A/CStar`; its rôle here (producing `M_N(𝒜)`) is covered by the
direct statement 49IV below. -/

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 1: the C*-algebra
`M_N(𝒜)` of `N×N`-matrices over a von Neumann algebra `𝒜` (Mathlib:
`CStarMatrix (Fin N) (Fin N) 𝒜`) is a von Neumann algebra. -/
instance mn_vna_1 [VonNeumannAlgebra A] (N : ℕ) :
    VonNeumannAlgebra (CStarMatrix (Fin N) (Fin N) A) := sorry

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 2 (first half): for
`a₁,…,a_N, b₁,…,b_N ∈ 𝒜`, the map `M ↦ ∑ᵢⱼ aᵢ* Mᵢⱼ bⱼ : M_N(𝒜) → 𝒜` is
ultraweakly and ultrastrongly continuous; for `a = b` it is moreover normal
(and completely positive). -/
theorem mn_vna_2 [VonNeumannAlgebra A] (N : ℕ) (a b : Fin N → A) :
    @Continuous _ _ (ultraweak (CStarMatrix (Fin N) (Fin N) A)) (ultraweak A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          ∑ i, ∑ j, star (a i) * CStarMatrix.ofMatrix.symm M i j * b j) ∧
      @Continuous _ _ (ultrastrong (CStarMatrix (Fin N) (Fin N) A))
        (ultrastrong A)
        (fun M : CStarMatrix (Fin N) (Fin N) A =>
          ∑ i, ∑ j, star (a i) * CStarMatrix.ofMatrix.symm M i j * b j) ∧
      PreservesDirSups (fun M : CStarMatrix (Fin N) (Fin N) A =>
        ∑ i, ∑ j, star (a i) * CStarMatrix.ofMatrix.symm M i j * a j) :=
  sorry

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
          (CStarMatrix.ofMatrix.symm M₀ i j)) :=
  sorry

/-- **49IV** (`mn-vna`, vn.tex:1272, Exercise), part 3: for an ncp-map
`f : 𝒜 → ℬ` between von Neumann algebras, the entrywise map
`M_N f : M_N(𝒜) → M_N(ℬ)` (cstar.tex 33III, `mnf`) is normal. -/
theorem mn_vna_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B] (N : ℕ)
    (f : NCPMap A B) :
    PreservesDirSups fun M : CStarMatrix (Fin N) (Fin N) A =>
      CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm M).map f) :=
  sorry

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
  sorry

/-- **53II** (`ngelfand`, vn.tex:1807, Exercise), part 2: the Gelfand
representation `γ_A : A → C(spec A)` (Mathlib: `gelfandStarTransform`), an
miu-isomorphism by cstar.tex 27XXVII, is normal, hence an
nmiu-isomorphism. -/
theorem ngelfand_normal [VonNeumannAlgebra A] :
    PreservesDirSups ⇑(gelfandStarTransform A) :=
  sorry

/-- **53III** (`vn-spectrum-extremally-disconnected`, vn.tex:1821,
Proposition): the spectrum of a commutative von Neumann algebra is
extremally disconnected: the closure of every open set is open. -/
theorem vn_spectrum_extremally_disconnected [VonNeumannAlgebra A] :
    ExtremallyDisconnected (characterSpace ℂ A) :=
  sorry

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
