/-
Papers/SEA/JBWSEA.lean

**SEA 16** (`ex:canonical-sea`, second.tex:475), JBW sentence, general JBW-algebras:
the structure step from the named Props REC 52 (`HancheOlsenStormerDecomposition`)
and REC 55 (`ShultzExceptionalStructure`).

Plan / findings (2026-09-26).
* Route: `V ≅ V_JW ⊕ C(X, M₃(𝕆)_sa)`; `[0,1]` of a direct sum is a product of SEAs;
  the JW summand is `sea16_special_normal`, the exceptional one pointwise `sea16_eja`.
* Obstacle 1 (done here).  Shultz's Prop applies to a JBW-*type* that is purely
  exceptional, but H-O–S only hands over the central idempotent `c`; the summand
  `cV = {x ; cx = x}` must be built as a JBW-algebra.  Its order unit axioms need
  `x ≥ 0 ⇒ cx ≥ 0`, i.e. positivity of `L_c`, which the tree lacked (no JB
  functional calculus).  Supplied: **approximate square roots** in any JB-algebra
  (`exists_sq_add`: `x ≥ 0`, `ε > 0` ⇒ `x + ε1 = s²`, `s ≥ 0`), by Banach's fixed
  point theorem for `z ↦ ½(y + z²)` on a ball (`exists_sqrt_near_one`; only
  commutativity, bilinearity and `‖ab‖ ≤ ‖a‖‖b‖` are used, no power-associativity).
  Consequences: every Jordan homomorphism into a C*-algebra is positive
  (`jordanHom_nonneg`); `L_c` is positive for a central idempotent (`cmul_nonneg`);
  `cV` is a JBW-algebra (`Corner`, `corner_jbw`) and, by H-O–S, purely exceptional
  (`corner_purelyExceptional`); hence `jbw_structure`: every JBW-algebra has a positive
  normal Jordan homomorphism `φ` into a von Neumann algebra with kernel `cV` and a
  surjective multiplicative `Ψ : V → C(X, M₃(𝕆)_sa)` (X hyperstonean) with kernel
  `(1-c)V`, jointly injective.
* Obstacle 2 (open).  The SEA product needs the *exact* root `√a ∈ V` and order
  *reflection* (`U_{√a} b ∈ [0,1]_V`, the `⊥` of S1).  The Props as stated give
  neither: REC 52's `φ` is only a Jordan homomorphism with kernel `cV` (not an
  isometry of `(1-c)V` onto a JW-algebra), and REC 55's `Φ` only a multiplicative
  linear bijection (the source's is isometric and an order isomorphism).  Recovering
  them needs Hanche-Olsen–Størmer 3.2.4 (`C(a) ≅ C(sp a)`) and 3.4.3 (injective
  Jordan homomorphisms are isometric), i.e. a JB functional calculus.
* Obstacle 3 (open).  Normality on `C(X, M₃(𝕆)_sa)`: directed suprema are not
  pointwise; S6 needs `U_{√a}` normal on a JBW-algebra (H-O–S 4.1.x) or a Stonean
  regularisation argument; also continuity of `√` on `M₃(𝕆)_sa` for the pointwise
  product.  The non-normal JB sentence for exceptional JB-algebras additionally needs
  the Alfsen–Shultz–Størmer Gelfand–Neumark theorem; out of reach.
-/
import Papers.SEA.JBSEA
import Papers.REC.Monoidal

set_option linter.unusedSectionVars false

namespace Papers.SEA.JBW

open Theses.B.Eff Papers.REC Filter Topology

universe u v

/-! ### Approximate square roots in a JB-algebra -/

section Sqrt

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- A closed-cone form of the Archimedean property. -/
theorem nonneg_of_forall_add {w : V} (hw : ∀ ε : ℝ, 0 < ε → 0 ≤ w + ε • ouUnit V) : 0 ≤ w := by
  refine IsOUS.cone_closed w fun ε hε => ⟨w + (ε / 2) • ouUnit V, hw _ (by positivity), ?_⟩
  rw [sub_add_cancel_left, ousNorm_neg]
  refine lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ le_rfl) (by linarith)
  exact neg_le_self (ou_smul_nonneg (by positivity) ou_unit_nonneg)

theorem sq_sub_sq (a b : V) : a * a - b * b = (a - b) * (a + b) := by
  rw [jb_sub_mul, jb_mul_add, jb_mul_add, JBAlgebra.mul_comm b a]; abel

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-- **Square roots near `1`**: if `‖y‖ ≤ q < 1` then `1 - y = s²` with `s ≥ 0`.  Banach's
fixed point theorem for `z ↦ ½(y + z²)` on the ball of radius `ρ = 1 - √(1-q)`, where
it is a `ρ`-contraction (`z² - w² = (z - w)(z + w)`); then `s = 1 - z`. -/
theorem exists_sqrt_near_one {y : V} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hy : ousNorm V y ≤ q) : ∃ s : V, 0 ≤ s ∧ s * s = ouUnit V - y := by
  have := completeSpace_of_banach (W := V) hJ.banach
  set r := Real.sqrt (1 - q) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r * r = 1 - q := Real.mul_self_sqrt (by linarith)
  have hr1 : r ≤ 1 := by rw [hr]; exact Real.sqrt_le_one.mpr (by linarith)
  set ρ := 1 - r with hρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hρq : q + ρ * ρ = 2 * ρ := by rw [hρ]; nlinarith
  let f : V → V := fun z => (2⁻¹ : ℝ) • (y + z * z)
  let s := Metric.closedBall (0 : V) ρ
  have hmaps : Set.MapsTo f s s := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa [s] using hz
    show f z ∈ Metric.closedBall (0 : V) ρ
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖(2⁻¹ : ℝ) • (y + z * z)‖ ≤ ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    have h1 : ‖y + z * z‖ ≤ q + ρ * ρ := by
      refine (norm_add_le _ _).trans (add_le_add hy ?_)
      exact (jb_norm_mul_le z z).trans (mul_le_mul hz' hz' (ousNorm_nonneg_rc _) hρ0)
    linarith
  let K : NNReal := ⟨ρ, hρ0⟩
  have hK1 : K < 1 := NNReal.coe_lt_coe.1 hρ1
  have hK : ContractingWith K (hmaps.restrict f s s) := by
    refine ⟨hK1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha : ‖a.1‖ ≤ ρ := by
      have h : a.1 ∈ Metric.closedBall (0 : V) ρ := a.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hb : ‖b.1‖ ≤ ρ := by
      have h : b.1 ∈ Metric.closedBall (0 : V) ρ := b.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    show dist (f a.1) (f b.1) ≤ ρ * dist a.1 b.1
    rw [dist_eq_norm, dist_eq_norm]
    have e : f a.1 - f b.1 = (2⁻¹ : ℝ) • ((a.1 - b.1) * (a.1 + b.1)) := by
      simp only [f]; rw [← sq_sub_sq, ← smul_sub]; congr 1; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    have h2 : ‖a.1 + b.1‖ ≤ 2 * ρ := (norm_add_le _ _).trans (by linarith)
    calc 2⁻¹ * ‖(a.1 - b.1) * (a.1 + b.1)‖ ≤ 2⁻¹ * (‖a.1 - b.1‖ * (2 * ρ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact (jb_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (ousNorm_nonneg_rc _))
      _ = ρ * ‖a.1 - b.1‖ := by ring
  obtain ⟨z, hz, hfz, -⟩ := ContractingWith.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmaps hK (Metric.mem_closedBall_self hρ0) (edist_ne_top _ _)
  have hz' : ousNorm V z ≤ ρ := by
    have h : z ∈ Metric.closedBall (0 : V) ρ := hz
    rw [Metric.mem_closedBall, dist_zero_right] at h; exact h
  have e2 : z * z = (2 : ℝ) • z - y := by
    have h : (2⁻¹ : ℝ) • (y + z * z) = z := hfz
    calc z * z = (2 : ℝ) • ((2⁻¹ : ℝ) • (y + z * z)) - y := by
          rw [smul_smul]; norm_num
      _ = _ := by rw [h]
  refine ⟨ouUnit V - z, ?_, ?_⟩
  · rw [sub_nonneg]
    refine (ousNorm_bounds_le z).2.trans ?_
    calc ousNorm V z • ouUnit V ≤ (1 : ℝ) • ouUnit V := ou_smul_unit_mono (by linarith)
      _ = ouUnit V := one_smul _ _
  · rw [jb_sub_mul, jb_mul_sub, jb_mul_sub]
    simp only [JBAlgebra.one_mul, JBAlgebra.mul_one]
    rw [e2]; module

/-- **Approximate square roots**: for `x ≥ 0` and `ε > 0`, `x + ε1 = s²` with `s ≥ 0`. -/
theorem exists_sq_add {x : V} (hx : 0 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : V, 0 ≤ s ∧ s * s = x + ε • ouUnit V := by
  set M := ousNorm V x + ε with hMdef
  have hM : 0 < M := by have := ousNorm_nonneg_rc x; linarith
  set y := ouUnit V - M⁻¹ • (x + ε • ouUnit V) with hydef
  have hq0 : 0 ≤ 1 - ε / M := by
    rw [sub_nonneg, div_le_one hM]; have := ousNorm_nonneg_rc x; linarith
  have hq1 : 1 - ε / M < 1 := by have := div_pos hε hM; linarith
  have hxM : x + ε • ouUnit V ≤ M • ouUnit V := by
    rw [hMdef, add_smul]; exact add_le_add (ousNorm_bounds_le x).2 le_rfl
  have hy : ousNorm V y ≤ 1 - ε / M := by
    refine ousNorm_le_rc hq0 ?_ ?_
    · refine (neg_nonpos.2 (ou_smul_unit_nonneg hq0)).trans ?_
      rw [hydef, sub_nonneg]
      calc M⁻¹ • (x + ε • ouUnit V) ≤ M⁻¹ • (M • ouUnit V) :=
            ou_smul_le_smul (inv_nonneg.2 hM.le) hxM
        _ = ouUnit V := by rw [smul_smul, inv_mul_cancel₀ hM.ne', one_smul]
    · have e : y = (1 - ε / M) • ouUnit V - M⁻¹ • x := by rw [hydef]; module
      rw [e]; exact sub_le_self _ (ou_smul_nonneg (inv_nonneg.2 hM.le) hx)
  obtain ⟨s, hs0, hss⟩ := exists_sqrt_near_one hq0 hq1 hy
  refine ⟨Real.sqrt M • s, ou_smul_nonneg (Real.sqrt_nonneg _) hs0, ?_⟩
  rw [JBAlgebra.smul_mul, jb_mul_smul, smul_smul, Real.mul_self_sqrt hM.le, hss, hydef,
    sub_sub_cancel, smul_smul, mul_inv_cancel₀ hM.ne', one_smul]

/-- **Jordan homomorphisms into C*-algebras are positive** (REC 50/51's
`IsJordanHomInto`): `φ(x) + εφ(1) = φ(s)² ≥ 0` for every `ε > 0`. -/
theorem jordanHom_nonneg {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
    {φ : V →ₗ[ℝ] 𝔄} (hφ : IsJordanHomInto V 𝔄 φ) {x : V} (hx : 0 ≤ x) : 0 ≤ φ x := by
  have hsq : ∀ s : V, 0 ≤ φ (s * s) := by
    intro s
    rw [hφ.2, ← two_smul ℝ (φ s * φ s), smul_smul, show (2⁻¹ * 2 : ℝ) = 1 by norm_num, one_smul]
    have := star_mul_self_nonneg (φ s)
    rwa [(hφ.1 s).star_eq] at this
  have hc : Continuous fun ε : ℝ => φ x + ε • φ (ouUnit V) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun ε : ℝ => φ x + ε • φ (ouUnit V)) (𝓝[>] 0) (𝓝 (φ x)) := by
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  obtain ⟨s, -, hs⟩ := exists_sq_add hx hε
  have := hsq s
  rwa [hs, map_add, map_smul] at this

end Sqrt


/-! ### Central idempotents and the corner `cV` -/

/-- A **central idempotent** in REC 52's form: `c² = c` and `c(xy) = x(cy)`. -/
structure CentralIdem (V : Type u) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] where
  c : V
  idem : c * c = c
  central : ∀ x y : V, c * (x * y) = x * (c * y)

namespace CentralIdem

section Basic

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V] (e : CentralIdem V)

include hJ

theorem mul_mul_self (z : V) : e.c * (e.c * z) = e.c * z := by
  have h := e.central z e.c
  rw [e.idem, JBAlgebra.mul_comm z e.c] at h
  exact h

/-- `x ↦ cx` is multiplicative. -/
theorem mul_hom (x y : V) : (e.c * x) * (e.c * y) = e.c * (x * y) := by
  rw [← e.central (e.c * x) y, JBAlgebra.mul_comm (e.c * x) y, ← e.central y x, e.mul_mul_self,
    JBAlgebra.mul_comm y x]

theorem c_nonneg : 0 ≤ e.c := by rw [← e.idem]; exact jb_sq_nonneg _

/-- `1 - c` is again a central idempotent. -/
def compl : CentralIdem V where
  c := ouUnit V - e.c
  idem := by
    simp only [jb_sub_mul, jb_mul_sub, JBAlgebra.one_mul, JBAlgebra.mul_one, e.idem]; abel
  central x y := by simp only [jb_sub_mul, jb_mul_sub, JBAlgebra.one_mul, e.central]

theorem compl_c : e.compl.c = ouUnit V - e.c := rfl

theorem le_one : e.c ≤ ouUnit V := sub_nonneg.1 (c_nonneg (hJ := hJ) e.compl)

/-- **`L_c` is positive**: `c(x + ε1) = (cs)²` for the approximate root `s`. -/
theorem cmul_nonneg {x : V} (hx : 0 ≤ x) : 0 ≤ e.c * x := by
  refine nonneg_of_forall_add fun ε hε => ?_
  obtain ⟨s, -, hs⟩ := exists_sq_add hx hε
  have h1 : 0 ≤ e.c * (x + ε • ouUnit V) := by rw [← hs, ← e.mul_hom]; exact jb_sq_nonneg _
  rw [jb_mul_add, jb_mul_smul, JBAlgebra.mul_one] at h1
  exact h1.trans (add_le_add le_rfl (ou_smul_le_smul hε.le e.le_one))

theorem cmul_mono {x y : V} (h : x ≤ y) : e.c * x ≤ e.c * y := by
  rw [← sub_nonneg, ← jb_mul_sub]; exact e.cmul_nonneg (sub_nonneg.2 h)

theorem compl_mul (x : V) : e.compl.c * x = x - e.c * x := by
  rw [compl_c, jb_sub_mul, JBAlgebra.one_mul]

/-- `0 ≤ x ≤ c` forces `cx = x`. -/
theorem mul_eq_of_le {x : V} (h0 : 0 ≤ x) (h1 : x ≤ e.c) : e.c * x = x := by
  have a1 := e.compl.cmul_nonneg h0
  have a2 := e.compl.cmul_mono h1
  rw [compl_mul, compl_mul, e.idem, sub_self] at a2
  rw [compl_mul] at a1
  exact (sub_eq_zero.1 (le_antisymm a2 a1)).symm

/-- The summand `cV = {x ; cx = x}`. -/
def sub : Submodule ℝ V where
  carrier := {x | e.c * x = x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [jb_mul_add, ha, hb]
  zero_mem' := by simp only [Set.mem_ofPred_eq]; exact jb_mul_zero _
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [jb_mul_smul, hx]

theorem mem_sub {x : V} : x ∈ e.sub ↔ e.c * x = x := Iff.rfl

/-- The corner `cV` as a type. -/
abbrev Corner := ↥e.sub

theorem cx (x : e.Corner) : e.c * x.1 = x.1 := x.2

instance : OrderUnitSpace e.Corner where
  add_le_add_left x y h z := by
    show x.1 + z.1 ≤ y.1 + z.1
    exact add_le_add h le_rfl
  smul_nonneg {r x} hr hx := by
    show (0 : V) ≤ r • x.1
    exact ou_smul_nonneg hr hx
  unit := ⟨e.c, e.idem⟩
  exists_le_smul_unit x := by
    obtain ⟨n, hn⟩ := ou_exists_le_smul_unit x.1
    refine ⟨n, ?_⟩
    show x.1 ≤ (n : ℝ) • e.c
    have := e.cmul_mono hn
    rwa [e.cx x, jb_mul_smul, JBAlgebra.mul_one] at this

instance : Mul e.Corner :=
  ⟨fun x y => ⟨x.1 * y.1, show e.c * (x.1 * y.1) = _ by rw [e.central, e.cx y]⟩⟩

theorem unit_val : (ouUnit e.Corner).1 = e.c := rfl

theorem mul_val (x y : e.Corner) : (x * y).1 = x.1 * y.1 := rfl

/-- The order-unit norm of `cV` (unit `c`) is that of `V`. -/
theorem ousNorm_eq (x : e.Corner) : ousNorm e.Corner x = ousNorm V x.1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨b1, b2⟩ := ousNorm_bounds_le x.1
    refine ousNorm_le_rc (ousNorm_nonneg_rc _) ?_ ?_
    · show -(ousNorm V x.1 • e.c) ≤ x.1
      have := e.cmul_mono b1
      rwa [jb_mul_neg, jb_mul_smul, JBAlgebra.mul_one, e.cx x] at this
    · show x.1 ≤ ousNorm V x.1 • e.c
      have := e.cmul_mono b2
      rwa [jb_mul_smul, JBAlgebra.mul_one, e.cx x] at this
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have ht : 0 ≤ ousNorm e.Corner x + δ := by have := ousNorm_nonneg_rc x; linarith
    obtain ⟨b1, b2⟩ := ousNorm_bounds (v := x) (ε := ousNorm e.Corner x + δ) (by linarith)
    have b1' : -((ousNorm e.Corner x + δ) • e.c) ≤ x.1 := b1
    have b2' : x.1 ≤ (ousNorm e.Corner x + δ) • e.c := b2
    have hm := ou_smul_le_smul ht e.le_one
    exact ousNorm_le_rc ht ((neg_le_neg hm).trans b1') (b2'.trans hm)

instance : IsOUS e.Corner where
  norm_eq_zero v hv := Subtype.ext (IsOUS.norm_eq_zero v.1 (by rw [← e.ousNorm_eq]; exact hv))
  cone_closed v hv := by
    show (0 : V) ≤ v.1
    refine IsOUS.cone_closed v.1 fun ε hε => ?_
    obtain ⟨w, hw, hvw⟩ := hv ε hε
    rw [e.ousNorm_eq] at hvw
    exact ⟨w.1, hw, hvw⟩

theorem norm_c_le : ousNorm V e.c ≤ 1 := by
  refine ousNorm_le_rc zero_le_one ?_ ?_
  · rw [one_smul]; exact (neg_nonpos.2 ou_unit_nonneg).trans e.c_nonneg
  · rw [one_smul]; exact e.le_one

/-- **`cV` is a JB-algebra** (REC 44) with unit `c`. -/
instance : JBAlgebra e.Corner where
  toIsOUS := inferInstance
  banach s hs := by
    obtain ⟨v, hv⟩ := hJ.banach (fun n => (s n).1) (fun ε hε => by
      obtain ⟨N, hN⟩ := hs ε hε
      exact ⟨N, fun m hm n hn => by have := hN m hm n hn; rwa [e.ousNorm_eq] at this⟩)
    have hcv : e.c * v = v := by
      have h0 : ousNorm V (e.c * v - v) = 0 := by
        refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (ousNorm_nonneg_rc _)
        obtain ⟨N, hN⟩ := hv (δ / 2) (by positivity)
        have hN' := hN N le_rfl
        have e1 : e.c * v - v = e.c * (v - (s N).1) + ((s N).1 - v) := by
          rw [jb_mul_sub, e.cx]; abel
        rw [e1, zero_add]
        refine (ousNorm_add_le _ _).trans ?_
        have h2 : ousNorm V (e.c * (v - (s N).1)) ≤ ousNorm V ((s N).1 - v) := by
          refine (jb_norm_mul_le _ _).trans ?_
          rw [ousNorm_sub_comm v]
          calc ousNorm V e.c * ousNorm V ((s N).1 - v) ≤ 1 * ousNorm V ((s N).1 - v) :=
                mul_le_mul_of_nonneg_right e.norm_c_le (ousNorm_nonneg_rc _)
            _ = _ := one_mul _
        linarith
      exact sub_eq_zero.1 (IsOUS.norm_eq_zero _ h0)
    exact ⟨⟨v, hcv⟩, fun ε hε => by
      obtain ⟨N, hN⟩ := hv ε hε
      exact ⟨N, fun n hn => by rw [e.ousNorm_eq]; exact hN n hn⟩⟩
  mul_comm a b := Subtype.ext (JBAlgebra.mul_comm a.1 b.1)
  mul_one a := Subtype.ext (show a.1 * e.c = a.1 by rw [JBAlgebra.mul_comm]; exact e.cx a)
  one_mul a := Subtype.ext (e.cx a)
  jordan a b := Subtype.ext (JBAlgebra.jordan a.1 b.1)
  sq_mem a h1 h2 := by
    have h1' : -e.c ≤ a.1 := h1
    have h2' : a.1 ≤ e.c := h2
    obtain ⟨s1, s2⟩ := JBAlgebra.sq_mem a.1 ((neg_le_neg e.le_one).trans h1') (h2'.trans e.le_one)
    refine ⟨s1, ?_⟩
    show a.1 * a.1 ≤ e.c
    have := e.cmul_mono s2
    rwa [show e.c * (a.1 * a.1) = a.1 * a.1 from e.cx (a * a), JBAlgebra.mul_one] at this
  add_mul a b c := Subtype.ext (JBAlgebra.add_mul a.1 b.1 c.1)
  smul_mul r a b := Subtype.ext (JBAlgebra.smul_mul r a.1 b.1)

/-- A least upper bound in `cV` of a non-empty set is one in `V`. -/
theorem isLUB_val {S : Set e.Corner} (hne : S.Nonempty) {s : e.Corner} (hs : IsLUB S s) :
    IsLUB (Subtype.val '' S) s.1 := by
  refine ⟨by rintro _ ⟨t, ht, rfl⟩; exact hs.1 ht, fun u hu => ?_⟩
  obtain ⟨t0, ht0⟩ := hne
  have hcu : e.c * u ≤ u := by
    have h1 := e.compl.cmul_mono (hu ⟨t0, ht0, rfl⟩)
    rw [compl_mul, compl_mul, e.cx t0, sub_self, sub_nonneg] at h1
    exact h1
  have : s ≤ ⟨e.c * u, e.mul_mul_self u⟩ := hs.2 (by
    intro t ht
    show t.1 ≤ e.c * u
    have := e.cmul_mono (hu ⟨t, ht, rfl⟩)
    rwa [e.cx t] at this)
  exact le_trans (show s.1 ≤ e.c * u from this) hcu

/-- The projection `x ↦ cx` of `V` onto `cV`. -/
def proj : V →ₗ[ℝ] e.Corner where
  toFun x := ⟨e.c * x, e.mul_mul_self x⟩
  map_add' _ _ := Subtype.ext (jb_mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (jb_mul_smul _ _ _)

theorem proj_val (x : V) : (e.proj x).1 = e.c * x := rfl

theorem proj_mul (a b : V) : e.proj (a * b) = e.proj a * e.proj b :=
  Subtype.ext (e.mul_hom a b).symm

theorem proj_of_mem (w : e.Corner) : e.proj w.1 = w := Subtype.ext (e.cx w)

theorem proj_c : e.proj e.c = ouUnit e.Corner := Subtype.ext e.idem

/-- The summand `cV` is **purely exceptional** (REC 51) when every Jordan homomorphism of
`V` into a C*-algebra vanishes on it (REC 52's clause). -/
theorem corner_purelyExceptional
    (hvan : ∀ (𝔅 : Type u) [CStarAlgebra 𝔅] (ψ : V →ₗ[ℝ] 𝔅), IsJordanHomInto V 𝔅 ψ →
      ∀ x, e.c * x = x → ψ x = 0) :
    IsPurelyExceptional.{u, u} e.Corner := by
  intro 𝔅 _ ψ hψ
  have hJ' : IsJordanHomInto V 𝔅 (ψ ∘ₗ e.proj) :=
    ⟨fun a => hψ.1 _, fun a b => by
      show ψ (e.proj (a * b)) = _
      rw [e.proj_mul]; exact hψ.2 _ _⟩
  ext w
  have := hvan 𝔅 (ψ ∘ₗ e.proj) hJ' w.1 (e.cx w)
  rw [LinearMap.comp_apply, e.proj_of_mem] at this
  rw [this, LinearMap.zero_apply]

end Basic

section W

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V] (e : CentralIdem V)

include hW

/-- **`cV` is a JBW-algebra** (REC 48): directed suprema in `[0,c]` are those of `V`
(they stay below `c`, so in `cV`), and a normal state `ω` of `V` separating two points
of `cV` has `ω(c) > 0`, so `ω(c)⁻¹ ω` is a normal state of `cV`. -/
instance : JBWAlgebra e.Corner where
  directedComplete D hD hdir := by
    have hD' : Subtype.val '' D ⊆ Set.Icc 0 (ouUnit V) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨(hD ht).1, le_trans (show t.1 ≤ e.c from (hD ht).2) e.le_one⟩
    obtain ⟨s, ⟨hs0, -⟩, hub, hleast⟩ := hW.directedComplete _ hD' (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨z, hz, h1, h2⟩ := hdir a ha b hb
      exact ⟨z.1, ⟨z, hz, rfl⟩, h1, h2⟩)
    have hsc : s ≤ e.c := hleast e.c ⟨e.c_nonneg, e.le_one⟩ (by
      rintro _ ⟨t, ht, rfl⟩; exact (hD ht).2)
    refine ⟨⟨s, e.mul_eq_of_le hs0 hsc⟩, ⟨hs0, hsc⟩, fun d hd => hub _ ⟨d, hd, rfl⟩,
      fun t ht htub => hleast t.1 ⟨ht.1, le_trans (show t.1 ≤ e.c from ht.2) e.le_one⟩ ?_⟩
    rintro _ ⟨d, hd, rfl⟩; exact htub d hd
  separating x y hxy := by
    obtain ⟨ω, hωn, hωxy⟩ := hW.separating x.1 y.1 (fun h => hxy (Subtype.ext h))
    set k := ω.toLin e.c with hk_def
    have hk0 : 0 ≤ k := ω.nonneg _ e.c_nonneg
    have hmono : ∀ a b : V, a ≤ b → ω.toLin a ≤ ω.toLin b := fun a b h => by
      have := ω.nonneg _ (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this
    have hk : 0 < k := by
      refine lt_of_le_of_ne hk0 fun hk => hωxy ?_
      have hz := (x - y).2
      obtain ⟨b1, b2⟩ := ousNorm_bounds_le (x - y).1
      have c1 := hmono _ _ (e.cmul_mono b1)
      have c2 := hmono _ _ (e.cmul_mono b2)
      rw [e.cx (x - y), jb_mul_neg, jb_mul_smul, JBAlgebra.mul_one, map_neg, map_smul, ← hk_def,
        ← hk, smul_zero, neg_zero] at c1
      rw [e.cx (x - y), jb_mul_smul, JBAlgebra.mul_one, map_smul, ← hk_def, ← hk,
        smul_zero] at c2
      have := le_antisymm c2 c1
      rw [show (x - y).1 = x.1 - y.1 from rfl, map_sub, sub_eq_zero] at this
      exact this
    let ω' : OUSState e.Corner :=
      { toLin := k⁻¹ • (ω.toLin ∘ₗ e.sub.subtype)
        nonneg := fun a ha => by
          show 0 ≤ k⁻¹ * ω.toLin a.1
          exact mul_nonneg (inv_nonneg.2 hk0) (ω.nonneg _ ha)
        unital := by
          show k⁻¹ * ω.toLin e.c = 1
          exact inv_mul_cancel₀ hk.ne' }
    have hω' : ∀ a : e.Corner, ω'.toLin a = k⁻¹ * ω.toLin a.1 := fun a => rfl
    refine ⟨ω', ?_, ?_⟩
    · intro S s hne hdir hs
      have hV := hωn _ _ (hne.image _) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨z, hz, h1, h2⟩ := hdir a ha b hb
        exact ⟨z.1, ⟨z, hz, rfl⟩, h1, h2⟩) (e.isLUB_val hne hs)
      refine ⟨?_, fun b hb => ?_⟩
      · rintro _ ⟨t, ht, rfl⟩
        rw [hω', hω']
        exact mul_le_mul_of_nonneg_left (hV.1 ⟨t.1, ⟨t, ht, rfl⟩, rfl⟩) (inv_nonneg.2 hk0)
      · rw [hω', inv_mul_le_iff₀ hk]
        refine hV.2 ?_
        rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        have := hb ⟨t, ht, rfl⟩
        rw [hω', inv_mul_le_iff₀ hk] at this
        exact this
    · rw [hω', hω']
      intro h
      exact hωxy (mul_left_cancel₀ (inv_ne_zero hk.ne') h)

end W

end CentralIdem


/-! ### The structure of a JBW-algebra from REC 52 and REC 55 -/

open Papers.EJA.Albert in
/-- **The JW ⊕ `C(X, M₃(𝕆)_sa)` structure of a JBW-algebra**, from the named Props
REC 52 (`HancheOlsenStormerDecomposition`) and REC 55 (`ShultzExceptionalStructure`):
every JBW-algebra `V` has a central idempotent `c`, a *positive* normal Jordan
homomorphism `φ` into a von Neumann algebra with kernel `cV`, and a surjective
multiplicative linear `Ψ : V → C(X, M₃(𝕆)_sa)` (`X` hyperstonean) with `Ψ(c) = 1` and
kernel `(1-c)V`; together they are injective.  Shultz's theorem is applied to the summand
`cV`, made a purely exceptional JBW-algebra (`CentralIdem.Corner`); `Ψ = Φ ∘ (x ↦ cx)`. -/
theorem jbw_structure (hHOS : HancheOlsenStormerDecomposition.{v})
    (hSh : ShultzExceptionalStructure.{v}) (V : Type v) [AddCommGroup V] [Module ℝ V]
    [PartialOrder V] [OrderUnitSpace V] [Mul V] (hV : JBWAlgebra V) :
    ∃ c : V, c * c = c ∧ (∀ x y : V, c * (x * y) = x * (c * y)) ∧
      ∃ (𝔄 : Type v) (_ : CStarAlgebra 𝔄) (_ : PartialOrder 𝔄) (_ : StarOrderedRing 𝔄)
          (_ : Theses.VonNeumannAlgebra 𝔄) (φ : V →ₗ[ℝ] 𝔄),
        IsJordanHomInto V 𝔄 φ ∧ IsNormalMap φ ∧ (∀ x, φ x = 0 ↔ c * x = x) ∧
        (∀ x, 0 ≤ x → 0 ≤ φ x) ∧
      ∃ (X : Type v) (_ : TopologicalSpace X), IsHyperstonean X ∧
        ∃ Ψ : V →ₗ[ℝ] C(X, Alb), Function.Surjective Ψ ∧
          (∀ (a b : V) (t : X), Ψ (a * b) t = Ψ a t * Ψ b t) ∧ (∀ t : X, Ψ c t = 1) ∧
          (∀ x, Ψ x = 0 ↔ c * x = 0) ∧ (∀ x, φ x = 0 → Ψ x = 0 → x = 0) := by
  have := hV
  obtain ⟨c, hcc, hcen, ⟨𝔄, i1, i2, i3, i4, φ, hφJ, hφn, hker⟩, hvan⟩ := hHOS V hV
  let e : CentralIdem V := ⟨c, hcc, hcen⟩
  obtain ⟨X, iX, hX, Φ, hΦ⟩ := hSh e.Corner inferInstance
    (e.corner_purelyExceptional fun 𝔅 _ ψ hψ x hx => hvan 𝔅 ψ hψ x hx)
  refine ⟨c, hcc, hcen, 𝔄, i1, i2, i3, i4, φ, hφJ, hφn, hker, fun x hx => jordanHom_nonneg hφJ hx,
    X, iX, hX, Φ.toLinearMap ∘ₗ e.proj, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, rfl⟩ := Φ.surjective g
    exact ⟨w.1, by rw [LinearMap.comp_apply, e.proj_of_mem]; rfl⟩
  · intro a b t
    show Φ (e.proj (a * b)) t = Φ (e.proj a) t * Φ (e.proj b) t
    rw [e.proj_mul, hΦ]
  · intro t
    show Φ (e.proj e.c) t = 1
    rw [e.proj_c]
    have := congrArg (fun y => Φ y t)
      (JBAlgebra.one_mul (A := e.Corner) (Φ.symm (ContinuousMap.const X 1)))
    simp only [hΦ, LinearEquiv.apply_symm_apply, ContinuousMap.const_apply] at this
    rwa [mul_one'] at this
  · intro x
    show Φ (e.proj x) = 0 ↔ c * x = 0
    rw [LinearEquiv.map_eq_zero_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · intro x h1 h2
    have a1 := (hker x).1 h1
    have a2 : Φ (e.proj x) = 0 := h2
    rw [LinearEquiv.map_eq_zero_iff] at a2
    have a3 : c * x = 0 := congrArg Subtype.val a2
    rw [← a1, a3]

end Papers.SEA.JBW

#print axioms Papers.SEA.JBW.jbw_structure
