/-
Papers/SEA/JBAllSEA.lean

**SEA 16** (`ex:canonical-sea`, second.tex:475), the Jordan sentence for *all* JB- and
JBW-algebras: "any JB-algebra is a convex SEA, while any JBW-algebra is a convex normal SEA",
with `a ∘ b = U_{√a} b` (cited from van de Wetering 2019, arXiv:1803.11139v3).

Plan (2026-09-26; budget ~4 h).  `A` is a JB-algebra in REC 44's sense (`JBAlgebra`);
`√a` is `jbSqrt` (H-O–S 3.2.4, `JBCalculus`), `U_x y = 2x(xy) − x²y` is `jQ`.
1. The product on `[0,1]_A` (`jbSeq`): `0 ≤ U_{√a} b` is `jQ_nonneg` (H-O–S 3.3.6,
   `JBMacdonald`), `U_{√a} b ≤ U_{√a} 1 = a ≤ 1` by linearity.  S1 (linear in `b`), S2
   (`√1 = 1`), and S3 by the swap identity `swap_pow`: `U_{√a} b = 0` gives
   `(U_{√b} a)² = U_{√b} U_{√a} U_{√a} b = 0`, and `‖x²‖ = ‖x‖²`.  Convexity is SEA 9.
2. Operator commutation.  `OpComm x y`: `L_x L_y = L_y L_x`; `Compat a b`: every element of
   `C(a)` operator-commutes with every element of `C(b)`.  Unconditionally: `C(c)` is
   operator-commutative (power-associativity `jb_pow_aux` + continuity); **the easy half of
   van de Wetering's theorem**, `Compat a b ⇒ U_{√a} b = ab = U_{√b} a`; and the S4
   consequences of `Compat`: `Compat a (1 − b)`, `√(ab) = √a √b` and
   `U_{√(ab)} = U_{√a} U_{√b}` (fundamental formula `Uo_Uo` with `√a √b = U_{a^{1/4}} √b`).
3. The hard half (a ∘ b = b ∘ a ⇒ `Compat a b`, van de Wetering 2019; in the literature via
   Shirshov–Cohn or the bidual `A**` and spectral projections) and "the operator commutant
   of `C(c)` is a Jordan subalgebra" (H-O–S, again via `A**`) are NOT proved: they are the
   explicit hypothesis `JBCommutation A`.  Under it, S4/S5 hold: `[0,1]_A` is a convex SEA
   (`jbSEA`, `sea16_jb`).
4. Normality (JBW, S6), first half unconditional: `U_{√a}` preserves suprema of directed
   subsets of `[0,1]_A` (`jbw_seq_sup`): `U_{√a + ε}` is an order automorphism
   (`= e^{2L_h}`, inverse `e^{−2L_h}`, both positive by `exp_mulC_pos`), and
   `U_{√a + ε} → U_{√a}` uniformly on `[0,1]` (error `(4ε + 2ε²)1`).  The second half
   (commutants closed under directed suprema) is the hypothesis `JBWCommSup A`; under both,
   `[0,1]_A` is a convex normal SEA (`jbwNormalSEA`, `sea16_jbw`).
5. Sanity: both hypotheses hold for special algebras (`jbCommutation_of_special`,
   `jbwCommSup_of_special`, via Gudder–Greechie and `commute_of_isLUB`).
Status: 1–5 done, no sorry, axiom-clean.  Open: the two hypotheses for exceptional
algebras (a Jordan-intrinsic Kleinecke–Shirokov / spectral argument was not found).
-/
import Papers.SEA.JBSEA
import Papers.REC.JBMacdonald

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.SEA.JBAll

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Papers.REC.JBMac Filter Topology NormedSpace

universe u

noncomputable section

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hJ : JBAlgebra A]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

/-! ## 1. Basic facts on `U`, square roots and the unit interval -/

theorem jQ_eq_Uo (a b : A) : jQ a b = Uo a b := (Uo_apply a b).symm

theorem jQ_add (a b c : A) : jQ a (b + c) = jQ a b + jQ a c := by
  rw [jQ_eq_Uo, jQ_eq_Uo, jQ_eq_Uo, map_add]

theorem jQ_sub (a b c : A) : jQ a (b - c) = jQ a b - jQ a c := by
  rw [jQ_eq_Uo, jQ_eq_Uo, jQ_eq_Uo, map_sub]

theorem jQ_smul (a : A) (r : ℝ) (b : A) : jQ a (r • b) = r • jQ a b := by
  rw [jQ_eq_Uo, jQ_eq_Uo, map_smul]

theorem jQ_zero (a : A) : jQ a (0 : A) = 0 := by rw [jQ_eq_Uo, map_zero]

theorem jQ_one (a : A) : jQ a (ouUnit A) = a * a := by rw [jQ_eq_Uo, Uo_apply_one]

theorem jQ_mono (a : A) {b c : A} (h : b ≤ c) : jQ a b ≤ jQ a c := by
  have := jQ_nonneg a (sub_nonneg.2 h)
  rw [jQ_sub] at this
  exact sub_nonneg.1 this

theorem jbSqrt_one : jbSqrt (ouUnit A) = ouUnit A :=
  (jbSqrt_unique ou_unit_nonneg ou_unit_nonneg (JBAlgebra.mul_one _)).symm

theorem jQ_one_left (b : A) : jQ (ouUnit A) b = b := by
  rw [jQ_eq_Uo, Uo_one]; rfl

theorem ousNorm_le_one_of_mem {a : A} (h0 : 0 ≤ a) (h1 : a ≤ ouUnit A) : ousNorm A a ≤ 1 :=
  ousNorm_le_rc zero_le_one (by
    rw [one_smul]; exact le_trans (neg_nonpos.2 ou_unit_nonneg) h0) (by rwa [one_smul])

theorem le_one_of_ousNorm_le {a : A} (h : ousNorm A a ≤ 1) : a ≤ ouUnit A :=
  (ousNorm_bounds_le a).2.trans (by
    have := ou_smul_unit_mono (X := A) h; rwa [one_smul] at this)

theorem neg_one_le_of_ousNorm_le {a : A} (h : ousNorm A a ≤ 1) : -ouUnit A ≤ a := by
  refine le_trans ?_ (ousNorm_bounds_le a).1
  have := ou_smul_unit_mono (X := A) h
  rw [one_smul] at this
  exact neg_le_neg this

theorem jbSqrt_le_one {a : A} (h0 : 0 ≤ a) (h1 : a ≤ ouUnit A) : jbSqrt a ≤ ouUnit A := by
  refine le_one_of_ousNorm_le ?_
  have hn := jb_norm_mul_self (jbSqrt a)
  rw [jbSqrt_mul_self h0] at hn
  have := ousNorm_le_one_of_mem h0 h1
  have h0' := ousNorm_nonneg_rc (jbSqrt a)
  nlinarith

/-- The sequential product on `A`: `a ∘ b = U_{√a} b`. -/
def sq (a b : A) : A := jQ (jbSqrt a) b

theorem sq_nonneg (a : A) {b : A} (hb : 0 ≤ b) : 0 ≤ sq a b := jQ_nonneg _ hb

theorem sq_one_right {a : A} (ha : 0 ≤ a) : sq a (ouUnit A) = a := by
  rw [sq, jQ_one, jbSqrt_mul_self ha]

theorem sq_le {a b : A} (ha : 0 ≤ a) (hb : b ≤ ouUnit A) : sq a b ≤ a := by
  have := jQ_mono (jbSqrt a) hb
  rwa [← sq, ← sq, sq_one_right ha] at this

/-- **S3 in every JB-algebra**: `U_{√a} b = 0` implies `U_{√b} a = 0`.  The swap identity
(`swap_pow`, `n = 1`) gives `(U_{√b} a)² = U_{√b} U_{√a} (U_{√a} b) = 0`. -/
theorem sq_eq_zero_comm {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : sq a b = 0) : sq b a = 0 := by
  set r := jbSqrt a
  set s := jbSqrt b
  have hsw := swap_pow s r 1
  have hy : Uo r (s * s) = 0 := by
    rw [Uo_apply, jbSqrt_mul_self hb]; exact h
  rw [hy, jbPow_one, map_zero, map_zero, jbPow_succ, jbPow_one] at hsw
  have hx : Uo s (r * r) = sq b a := by rw [Uo_apply, jbSqrt_mul_self ha]; rfl
  rw [hx] at hsw
  have hn := jb_norm_mul_self (sq b a)
  rw [hsw] at hn
  have h0 : ousNorm A (0 : A) = 0 := by
    have := ousNorm_nonneg_rc (0 : A)
    exact le_antisymm (ousNorm_le_rc le_rfl (by simp) (by simp)) this
  rw [h0] at hn
  refine IsOUS.norm_eq_zero _ ?_
  have := ousNorm_nonneg_rc (sq b a)
  nlinarith

/-! ## 2. The unit interval and the product on it -/

variable (A) in
/-- `[0,1]_A` with the effect algebra of SEA 4 (the same as JBSEA's). -/
abbrev jbEA : EffectAlgebra (Set.Icc (0 : A) (ouUnit A)) := JC.SpecialEmbedding.jbEA A

/-- The sequential product on `[0,1]_A`. -/
def jbSeq (a b : Set.Icc (0 : A) (ouUnit A)) : Set.Icc (0 : A) (ouUnit A) :=
  ⟨sq a.1 b.1, sq_nonneg _ b.2.1, (sq_le a.2.1 b.2.2).trans a.2.2⟩

@[simp] theorem jbSeq_val (a b : Set.Icc (0 : A) (ouUnit A)) :
    (jbSeq a b).1 = jQ (jbSqrt a.1) b.1 := rfl

/-! ## 3. Operator commutation -/

/-- `x` and `y` **operator commute**: `L_x L_y = L_y L_x`. -/
def OpComm (x y : A) : Prop := ∀ w : A, x * (y * w) = y * (x * w)

theorem OpComm.symm {x y : A} (h : OpComm x y) : OpComm y x := fun w => (h w).symm

theorem opComm_add_left {x x' y : A} (h : OpComm x y) (h' : OpComm x' y) :
    OpComm (x + x') y := fun w => by
  rw [JBAlgebra.add_mul, JBAlgebra.add_mul, jb_mul_add, h w, h' w]

theorem opComm_smul_left {x y : A} (r : ℝ) (h : OpComm x y) : OpComm (r • x) y := fun w => by
  rw [JBAlgebra.smul_mul, JBAlgebra.smul_mul, jb_mul_smul, h w]

theorem opComm_zero_left (y : A) : OpComm 0 y := fun w => by
  rw [jb_zero_mul, jb_zero_mul, jb_mul_zero]

theorem opComm_one_left (y : A) : OpComm (ouUnit A) y := fun w => by
  rw [JBAlgebra.one_mul, JBAlgebra.one_mul]

theorem isClosed_opComm_left (y : A) : IsClosed {x : A | OpComm x y} := by
  have : {x : A | OpComm x y} = ⋂ w : A, {x | x * (y * w) = y * (x * w)} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_iInter]; rfl
  rw [this]
  refine isClosed_iInter fun w => isClosed_eq ?_ ?_
  · exact jb_continuous_mul.comp (continuous_id.prodMk continuous_const)
  · exact jb_continuous_mul.comp
      (continuous_const.prodMk (jb_continuous_mul.comp (continuous_id.prodMk continuous_const)))

theorem opComm_jbEv (c : A) (p q : Polynomial ℝ) : OpComm (jbEv c p) (jbEv c q) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => rw [map_add]; exact opComm_add_left hp hp'
  | monomial n r =>
    rw [jbEv_monomial]
    refine opComm_smul_left r ?_
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [map_add]; exact (opComm_add_left hq.symm hq'.symm).symm
    | monomial m s =>
      rw [jbEv_monomial]
      refine (opComm_smul_left s ?_).symm
      intro w; exact (jb_pow_aux c (m + n)).2 m n le_rfl w

/-- **`C(c)` is operator-commutative**: `L_x L_y = L_y L_x` for `x, y ∈ C(c)`
(power-associativity `jb_pow_aux`, then continuity). -/
theorem opComm_Ca {c x y : A} (hx : x ∈ (Ca c).carrier) (hy : y ∈ (Ca c).carrier) :
    OpComm x y := by
  have h1 : ∀ q, ∀ x ∈ (Ca c).carrier, OpComm x (jbEv c q) := by
    intro q x hx
    have hsub : Set.range (jbEv c) ⊆ {x | OpComm x (jbEv c q)} := by
      rintro _ ⟨p, rfl⟩; exact opComm_jbEv c p q
    exact (isClosed_opComm_left _).closure_subset_iff.2 hsub (mem_Ca.1 hx)
  have hsub : Set.range (jbEv c) ⊆ {y | OpComm y x} := by
    rintro _ ⟨q, rfl⟩; exact (h1 q x hx).symm
  exact ((isClosed_opComm_left _).closure_subset_iff.2 hsub (mem_Ca.1 hy)).symm

theorem commute_mulC {u v : A} (h : OpComm u v) : Commute (mulC u) (mulC v) := by
  ext w; simp only [mul_apply_eq_comp, mulC_apply]; exact h w

/-- Operator-commuting `u, v` (with their squares) have commuting `U_u`, `U_v`. -/
theorem commute_Uo {u v : A} (h1 : OpComm u v) (h2 : OpComm u (v * v)) (h3 : OpComm (u * u) v)
    (h4 : OpComm (u * u) (v * v)) : Commute (Uo u) (Uo v) := by
  have c1 := commute_mulC h1
  have c2 := commute_mulC h2
  have c3 := commute_mulC h3
  have c4 := commute_mulC h4
  have d1 : Commute (mulC u * mulC u) (mulC v * mulC v) :=
    (c1.mul_right c1).mul_left (c1.mul_right c1)
  have d2 : Commute (mulC u * mulC u) (mulC (v * v)) := c2.mul_left c2
  have d3 : Commute (mulC (u * u)) (mulC v * mulC v) := c3.mul_right c3
  unfold Uo
  exact ((d1.smul_left _).smul_right _ |>.sub_right (d2.smul_left _)).sub_left
    (d3.smul_right _ |>.sub_right c4)

/-- `U_r v = r² v` when `r` and `v` operator commute. -/
theorem jQ_of_opComm {r v : A} (h : OpComm r v) : jQ r v = (r * r) * v := by
  have e : r * (r * v) = (r * r) * v := by
    rw [JBAlgebra.mul_comm r v, h r, JBAlgebra.mul_comm]
  rw [jQ, e, two_smul, add_sub_cancel_right]

/-- `a` and `b` are **compatible**: every element of `C(a)` operator-commutes with every
element of `C(b)`. -/
def Compat (a b : A) : Prop := ∀ x ∈ (Ca a).carrier, ∀ y ∈ (Ca b).carrier, OpComm x y

theorem Compat.symm {a b : A} (h : Compat a b) : Compat b a :=
  fun x hx y hy => (h y hy x hx).symm

theorem Compat.mono {a b a' b' : A} (h : Compat a b) (ha : a' ∈ (Ca a).carrier)
    (hb : b' ∈ (Ca b).carrier) : Compat a' b' :=
  fun x hx y hy => h x (Ca_le (Ca a) ha hx) y (Ca_le (Ca b) hb hy)

theorem sq_eq_mul_of_compat {a b : A} (ha : 0 ≤ a) (h : Compat a b) : sq a b = a * b := by
  rw [sq, jQ_of_opComm (h _ (jbSqrt_mem a) _ (self_mem_Ca b)), jbSqrt_mul_self ha]

/-- **The easy half of van de Wetering's commutation theorem**, in every JB-algebra:
compatible `a, b ≥ 0` commute sequentially, `U_{√a} b = ab = U_{√b} a`. -/
theorem sq_comm_of_compat {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Compat a b) :
    sq a b = sq b a := by
  rw [sq_eq_mul_of_compat ha h, sq_eq_mul_of_compat hb h.symm, JBAlgebra.mul_comm]

theorem one_sub_mem_Ca (b : A) : ouUnit A - b ∈ (Ca b).carrier :=
  (Ca b).carrier.sub_mem (Ca b).one_mem (self_mem_Ca b)

/-- S4, first half, from compatibility: `Compat a b ⇒ Compat a (1 − b)`. -/
theorem compat_orth {a b : A} (h : Compat a b) : Compat a (ouUnit A - b) :=
  h.mono (self_mem_Ca a) (one_sub_mem_Ca b)

/-- For compatible `a, b ≥ 0`: `√(ab) = √a √b`, and `U_{√(ab)} = U_{√a} U_{√b}`. -/
theorem Uo_sqrt_mul_of_compat {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Compat a b) :
    Uo (jbSqrt (a * b)) = Uo (jbSqrt a) * Uo (jbSqrt b) := by
  set x := jbSqrt a
  set y := jbSqrt b
  set z := jbSqrt x
  have hx0 : 0 ≤ x := jbSqrt_nonneg a
  have hxx : x * x = a := jbSqrt_mul_self ha
  have hyy : y * y = b := jbSqrt_mul_self hb
  have hzz : z * z = x := jbSqrt_mul_self hx0
  have hxC : x ∈ (Ca a).carrier := jbSqrt_mem a
  have hzC : z ∈ (Ca a).carrier := Ca_le (Ca a) hxC (jbSqrt_mem x)
  have hyC : y ∈ (Ca b).carrier := jbSqrt_mem b
  have hmC : ∀ {c u : A}, u ∈ (Ca c).carrier → u * u ∈ (Ca c).carrier :=
    fun hu => (Ca _).mul_mem hu hu
  -- `xy = U_z y ≥ 0`
  have hxy : x * y = jQ z y := by rw [jQ_of_opComm (h z hzC y hyC), hzz]
  have hxy0 : 0 ≤ x * y := by rw [hxy]; exact jQ_nonneg z (jbSqrt_nonneg b)
  have hcomm : Commute (Uo z) (Uo y) := commute_Uo (h z hzC y hyC) (h z hzC _ (hmC hyC))
    (h _ (hmC hzC) y hyC) (h _ (hmC hzC) _ (hmC hyC))
  -- `(xy)² = ab`
  have hsq : (x * y) * (x * y) = a * b := by
    calc (x * y) * (x * y) = Uo (Uo z y) (ouUnit A) := by rw [Uo_apply_one, Uo_apply, hxy]
      _ = Uo z (Uo y (Uo z (ouUnit A))) := Uo_Uo_apply _ _ _
      _ = Uo z (Uo y x) := by rw [Uo_apply_one, hzz]
      _ = Uo y (Uo z x) := by
          rw [← mul_apply_eq_comp, hcomm.eq, mul_apply_eq_comp]
      _ = a * b := by
          rw [Uo_apply z, jQ_of_opComm (opComm_Ca hzC hxC), hzz, hxx, Uo_apply,
            jQ_of_opComm (h a (self_mem_Ca a) y hyC).symm, hyy, JBAlgebra.mul_comm]
  have hroot : jbSqrt (a * b) = x * y :=
    (jbSqrt_unique (by rw [← hsq]; exact jb_sq_nonneg _) hxy0 hsq).symm
  rw [hroot, hxy, ← Uo_apply, Uo_Uo, mul_assoc, ← hcomm.eq, ← mul_assoc, ← Uo_mul_self,
    hzz]

/-- S4, second half, from compatibility: `a ∘ (b ∘ c) = (a ∘ b) ∘ c`. -/
theorem sq_assoc_of_compat {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Compat a b) (c : A) :
    sq (sq a b) c = sq a (sq b c) := by
  rw [sq_eq_mul_of_compat ha h, sq, sq, sq, jQ_eq_Uo, Uo_sqrt_mul_of_compat ha hb h,
    mul_apply_eq_comp, ← jQ_eq_Uo, ← jQ_eq_Uo]


/-! ## 4. The commutant of `C(c)`, and the hypothesis -/

/-- The **operator commutant** of `C(c)`: the `y` with `L_x L_y = L_y L_x` for all `x ∈ C(c)`. -/
def comm (c : A) : Set A := {y | ∀ x ∈ (Ca c).carrier, OpComm x y}

theorem compat_iff_subset {a b : A} : Compat a b ↔ ((Ca b).carrier : Set A) ⊆ comm a :=
  ⟨fun h _ hy x hx => h x hx _ hy, fun h x hx _y hy => h hy x hx⟩

theorem mem_comm_of_compat {a b : A} (h : Compat a b) : b ∈ comm a :=
  compat_iff_subset.1 h (self_mem_Ca b)

variable (A) in
/-- **The cited input, as an explicit hypothesis** (not proved here).
* `mem_comm`: *van de Wetering's commutation theorem* (2019, the source SEA 16 cites) with
  Hanche-Olsen–Størmer's passage from `a` to `C(a)`: for `a, b ≥ 0`, `U_{√a} b = U_{√b} a`
  implies that `b` operator-commutes with every element of `C(a)`.  (The converse is proved,
  `sq_comm_of_compat`.)
* `mul_mem`: for `c ≥ 0` the operator commutant of `C(c)` is closed under the Jordan product
  (in a JBW-algebra: the intersection of the Peirce subalgebras `A₁(p) ⊕ A₀(p)` over the
  spectral idempotents `p` of `c`; for JB-algebras through the bidual). -/
structure JBCommutation : Prop where
  mem_comm : ∀ a b : A, 0 ≤ a → 0 ≤ b → sq a b = sq b a → b ∈ comm a
  mul_mem : ∀ c y z : A, 0 ≤ c → y ∈ comm c → z ∈ comm c → y * z ∈ comm c

theorem opComm_add_right {x y y' : A} (h : OpComm x y) (h' : OpComm x y') :
    OpComm x (y + y') := (opComm_add_left h.symm h'.symm).symm

theorem opComm_smul_right {x y : A} (r : ℝ) (h : OpComm x y) : OpComm x (r • y) :=
  (opComm_smul_left r h.symm).symm

/-- The commutant of `C(c)` as a closed subspace. -/
def commSubmodule (c : A) : Submodule ℝ A where
  carrier := comm c
  add_mem' := fun hy hz x hx => opComm_add_right (hy x hx) (hz x hx)
  zero_mem' := fun _ _ => (opComm_zero_left _).symm
  smul_mem' := fun r _ hy x hx => opComm_smul_right r (hy x hx)

theorem comm_closed (c : A) (y : A)
    (hy : ∀ ε : ℝ, 0 < ε → ∃ z ∈ comm c, ousNorm A (y - z) < ε) : y ∈ comm c := by
  intro x hx
  have hcl : IsClosed {y : A | OpComm y x} := isClosed_opComm_left x
  have : y ∈ closure {y : A | OpComm y x} := Metric.mem_closure_iff.2 fun ε hε => by
    obtain ⟨z, hz, hyz⟩ := hy ε hε
    exact ⟨z, (hz x hx).symm, by rw [dist_eq_norm]; exact hyz⟩
  exact (hcl.closure_subset this : OpComm y x).symm

/-- Under `JBCommutation`, the commutant of `C(c)` (`c ≥ 0`) is a closed unital subalgebra. -/
def commSub (H : JBCommutation A) {c : A} (hc : 0 ≤ c) : ClosedJBSub A where
  carrier := commSubmodule c
  one_mem := fun _ _ => (opComm_one_left _).symm
  mul_mem := fun hy hz => H.mul_mem _ _ _ hc hy hz
  closed := comm_closed c

theorem compat_of_mem_comm (H : JBCommutation A) {c b : A} (hc : 0 ≤ c) (hb : b ∈ comm c) :
    Compat c b :=
  compat_iff_subset.2 (Ca_le (commSub H hc) hb)

/-- **The commutation theorem** (under `JBCommutation`): for `a, b ≥ 0`,
`U_{√a} b = U_{√b} a` iff `a` and `b` are compatible. -/
theorem sq_comm_iff (H : JBCommutation A) {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sq a b = sq b a ↔ Compat a b :=
  ⟨fun h => compat_of_mem_comm H ha (H.mem_comm a b ha hb h), sq_comm_of_compat ha hb⟩

/-- S5 (products), under `JBCommutation`. -/
theorem compat_sq (H : JBCommutation A) {a b c : A} (hc : 0 ≤ c)
    (hca : Compat c a) (hcb : Compat c b) : Compat c (sq a b) := by
  have hsa : jbSqrt a ∈ comm c :=
    Ca_le (commSub H hc) (mem_comm_of_compat hca) (jbSqrt_mem a)
  have hb := mem_comm_of_compat hcb
  have hm : ∀ {y z : A}, y ∈ comm c → z ∈ comm c → y * z ∈ comm c :=
    fun hy hz => H.mul_mem _ _ _ hc hy hz
  have hmem : sq a b ∈ comm c := by
    show jQ (jbSqrt a) b ∈ commSubmodule c
    exact (commSubmodule c).sub_mem ((commSubmodule c).smul_mem _ (hm hsa (hm hsa hb)))
      (hm (hm hsa hsa) hb)
  exact compat_of_mem_comm H hc hmem

/-- S5 (sums), under `JBCommutation`. -/
theorem compat_add (H : JBCommutation A) {a b c : A} (hc : 0 ≤ c)
    (hca : Compat c a) (hcb : Compat c b) : Compat c (a + b) :=
  compat_of_mem_comm H hc ((commSubmodule c).add_mem (mem_comm_of_compat hca)
    (mem_comm_of_compat hcb))

/-! ## 5. `[0,1]_A` is a convex SEA -/

/-- **SEA 16, the unconditional part, in every JB-algebra** (REC 44): `[0,1]_A` is convex;
`a ∘ b = U_{√a} b` maps `[0,1]_A × [0,1]_A` into `[0,1]_A` and is additive in `b` (S1);
`1 ∘ b = b` (S2); `a ∘ b = 0 ⇒ b ∘ a = 0` (S3); and compatible `a, b` (every element of
`C(a)` operator-commutes with every element of `C(b)`) commute sequentially, `a` stays
compatible with `1 − b`, and `a ∘ (b ∘ c) = (a ∘ b) ∘ c` (the S4 conclusions).  Missing for
S4/S5: that sequential commutation implies compatibility, and that compatibility is closed
under the product (`JBCommutation`). -/
theorem sea16_jb_unconditional :
    @IsConvex _ (jbEA A) ∧
    (∀ a b : A, 0 ≤ a → a ≤ ouUnit A → 0 ≤ b → b ≤ ouUnit A →
      0 ≤ sq a b ∧ sq a b ≤ ouUnit A) ∧
    (∀ a b c : A, sq a (b + c) = sq a b + sq a c) ∧
    (∀ b : A, sq (ouUnit A) b = b) ∧
    (∀ a b : A, 0 ≤ a → 0 ≤ b → sq a b = 0 → sq b a = 0) ∧
    (∀ a b : A, 0 ≤ a → 0 ≤ b → Compat a b →
      sq a b = sq b a ∧ Compat a (ouUnit A - b) ∧ ∀ c : A, sq (sq a b) c = sq a (sq b c)) := by
  have := Papers.OAP.ous_posSMulMono A
  have := Papers.OAP.ous_smulPosMono A
  refine ⟨sea9_interval_convex A (ouUnit A) ou_unit_nonneg,
    fun a b _ ha1 hb0 hb1 => ⟨sq_nonneg a hb0, ?_⟩, fun a b c => jQ_add _ _ _,
    fun b => by rw [sq, jbSqrt_one, jQ_one_left], fun a b ha hb h => sq_eq_zero_comm ha hb h,
    fun a b ha hb h => ⟨sq_comm_of_compat ha hb h, compat_orth h, sq_assoc_of_compat ha hb h⟩⟩
  · exact (sq_le (by assumption) hb1).trans ha1


theorem jbSeq_comm_iff (H : JBCommutation A) {a b : Set.Icc (0 : A) (ouUnit A)} :
    jbSeq a b = jbSeq b a ↔ Compat a.1 b.1 :=
  ⟨fun h => (sq_comm_iff H a.2.1 b.2.1).1 (congrArg Subtype.val h),
    fun h => Subtype.ext ((sq_comm_iff H a.2.1 b.2.1).2 h)⟩

/-- `[0,1]_A` is a SEA with `a ∘ b = U_{√a} b`, for every JB-algebra satisfying the
commutation input `JBCommutation`. -/
@[instance_reducible] def jbSEA (H : JBCommutation A) :
    @SEAlgebra (Set.Icc (0 : A) (ouUnit A)) (jbEA A) := by
  letI := jbEA A
  exact
  { seq := jbSeq
    seq_add := fun c {a b} h => by
      have hp : Perp (jbSeq c a) (jbSeq c b) := by
        show sq c.1 a.1 + sq c.1 b.1 ≤ ouUnit A
        rw [sq, sq, ← jQ_add]
        exact (sq_le c.2.1 (show a.1 + b.1 ≤ ouUnit A from h)).trans c.2.2
      exact ⟨hp, Subtype.ext (by
        show sq c.1 a.1 + sq c.1 b.1 = sq c.1 (a.1 + b.1)
        rw [sq, sq, sq, jQ_add])⟩
    one_seq := fun a => Subtype.ext (by
      show jQ (jbSqrt (ouUnit A)) a.1 = a.1
      rw [jbSqrt_one, jQ_one_left])
    seq_zero_comm := fun a b h => Subtype.ext
      (sq_eq_zero_comm a.2.1 b.2.1 (congrArg Subtype.val h))
    seq_comm_orth := fun {a b} h => (jbSeq_comm_iff H).2 (compat_orth ((jbSeq_comm_iff H).1 h))
    seq_comm_assoc := fun {a b} h c => Subtype.ext
      (sq_assoc_of_compat a.2.1 b.2.1 ((jbSeq_comm_iff H).1 h) c.1)
    seq_comm_compat := fun {a b c} h hca hcb => by
      have h1 := (jbSeq_comm_iff H).1 hca
      have h2 := (jbSeq_comm_iff H).1 hcb
      exact ⟨(jbSeq_comm_iff H).2 (compat_sq H c.2.1 h1 h2),
        (jbSeq_comm_iff H).2 (compat_add H c.2.1 h1 h2)⟩
    seq_comm_seq := fun {a b c} hca hcb => by
      have h1 := (jbSeq_comm_iff H).1 hca
      have h2 := (jbSeq_comm_iff H).1 hcb
      exact (jbSeq_comm_iff H).2 (compat_sq H c.2.1 h1 h2) }

/-- **SEA 16** (`ex:canonical-sea`, second.tex:475), "any JB-algebra is a convex SEA", for
every JB-algebra `A` (REC 44) satisfying the commutation input `JBCommutation A` (van de
Wetering's theorem, the hard half): `[0,1]_A` is convex, and a SEA (`jbSEA`) whose product
is `a ∘ b = U_r b = 2r(rb) − (rr)b` for the unique `r ≥ 0` with `rr = a` (`r = √a`). -/
theorem sea16_jb (H : JBCommutation A) :
    @IsConvex _ (jbEA A) ∧
    ∀ a b : Set.Icc (0 : A) (ouUnit A),
      ∃! r : A, 0 ≤ r ∧ r * r = a.1 ∧
        (@SequentialEffectAlgebra.seq _ (jbEA A) (jbSEA H).toSequentialEffectAlgebra a b).1 =
          (2 : ℝ) • (r * (r * b.1)) - (r * r) * b.1 := by
  have := Papers.OAP.ous_posSMulMono A
  have := Papers.OAP.ous_smulPosMono A
  refine ⟨sea9_interval_convex A (ouUnit A) ou_unit_nonneg, fun a b => ?_⟩
  refine ⟨jbSqrt a.1, ⟨jbSqrt_nonneg _, jbSqrt_mul_self a.2.1, rfl⟩, ?_⟩
  rintro r ⟨hr0, hrr, -⟩
  exact jbSqrt_unique a.2.1 hr0 hrr


/-! ## 6. Normality of `U_{√a}` -/

attribute [local instance] jbComplete opRat

theorem bounds_of_norm_le {v : A} {m : ℝ} (h : ousNorm A v ≤ m) :
    -(m • ouUnit A) ≤ v ∧ v ≤ m • ouUnit A :=
  ⟨le_trans (neg_le_neg (ou_smul_unit_mono h)) (ousNorm_bounds_le v).1,
    (ousNorm_bounds_le v).2.trans (ou_smul_unit_mono h)⟩

theorem le_of_forall_le_add {u v : A} (h : ∀ δ : ℝ, 0 < δ → u ≤ v + δ • ouUnit A) : u ≤ v := by
  refine sub_nonneg.1 (Papers.SEA.JBW.nonneg_of_forall_add fun δ hδ => ?_)
  have := h δ hδ
  rw [sub_add_eq_add_sub, sub_nonneg]; exact this

/-- For `c ≥ δ1` (`δ > 0`), `U_c` is an order automorphism: `U_c = e^{L_h} e^{L_h}` with
`h = log c`, inverse `e^{−L_h} e^{−L_h}`, both positive (`exp_mulC_pos`). -/
theorem Uo_orderAut {c : A} {δ : ℝ} (hδ : 0 < δ) (hc : δ • ouUnit A ≤ c) :
    Uo c ∈ posOps (W := A) ∧
      ∃ T : A →L[ℝ] A, T ∈ posOps (W := A) ∧ Uo c * T = 1 ∧ T * Uo c = 1 := by
  obtain ⟨h, hh⟩ := exists_eE_eq hδ hc
  set X := mulC h
  have hp : exp (-X) ∈ posOps (W := A) := by
    have := exp_mulC_pos h (-1); rwa [neg_one_smul] at this
  refine ⟨by rw [← hh]; exact Uo_eE_pos h, exp (-X) * exp (-X), mul_mem hp hp, ?_, ?_⟩
  · rw [← hh, Uo_eE, mul_assoc, ← mul_assoc (exp X) (exp (-X)), exp_mul_exp_neg, one_mul,
      exp_mul_exp_neg]
  · rw [← hh, Uo_eE, mul_assoc, ← mul_assoc (exp (-X)) (exp X), exp_neg_mul_exp, one_mul,
      exp_neg_mul_exp]

theorem posOps_mono {T : A →L[ℝ] A} (hT : T ∈ posOps (W := A)) {v w : A} (h : v ≤ w) :
    T v ≤ T w := by
  have := hT (w - v) (sub_nonneg.2 h)
  rwa [map_sub, sub_nonneg] at this

theorem apply_of_mul_eq_one {Φ Ψ : A →L[ℝ] A} (h : Φ * Ψ = 1) (v : A) : Φ (Ψ v) = v := by
  rw [← mul_apply_eq_comp, h]; rfl

/-- An order automorphism preserves least upper bounds. -/
theorem isLUB_image_of_orderAut {Φ Ψ : A →L[ℝ] A} (hΦ : Φ ∈ posOps (W := A))
    (hΨ : Ψ ∈ posOps (W := A)) (h1 : Φ * Ψ = 1) (h2 : Ψ * Φ = 1) {S : Set A} {x : A}
    (hx : IsLUB S x) : IsLUB (Φ '' S) (Φ x) := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact posOps_mono hΦ (hx.1 hs)
  · have hΨu : x ≤ Ψ u := hx.2 fun s hs => by
      have := posOps_mono hΨ (hu ⟨s, hs, rfl⟩)
      rwa [apply_of_mul_eq_one h2] at this
    have := posOps_mono hΦ hΨu
    rwa [apply_of_mul_eq_one h1] at this

/-- `U_{r+ε} v = U_r v + ε·2(rv) + ε²v`. -/
theorem Uo_add_unit (r v : A) (ε : ℝ) :
    Uo (r + ε • ouUnit A) v = jQ r v + (ε • ((2 : ℝ) • (r * v)) + (ε * ε) • v) := by
  simp only [Uo_apply, jQ, JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul,
    JBAlgebra.one_mul, JBAlgebra.mul_one, JBAlgebra.mul_comm (ouUnit A) v, _root_.smul_smul]
  module

theorem err_norm_le {r v : A} (hr : ousNorm A r ≤ 1) (hv : ousNorm A v ≤ 1) {ε : ℝ}
    (hε : 0 ≤ ε) : ousNorm A (ε • ((2 : ℝ) • (r * v)) + (ε * ε) • v) ≤ 2 * ε + ε * ε := by
  have hrv : ousNorm A (r * v) ≤ 1 := (jb_norm_mul_le r v).trans (by
    have := ousNorm_nonneg_rc r; have := ousNorm_nonneg_rc v; nlinarith)
  refine (ousNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h2 : ousNorm A ((2 : ℝ) • (r * v)) ≤ 2 :=
      (ousNorm_smul_le _ _).trans (by rw [abs_two]; linarith)
    refine (ousNorm_smul_le _ _).trans ?_
    rw [abs_of_nonneg hε]
    nlinarith [ousNorm_nonneg_rc ((2 : ℝ) • (r * v))]
  · refine (ousNorm_smul_le _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg hε hε)]
    nlinarith [ousNorm_nonneg_rc v]

/-- **`U_r` preserves least upper bounds in `[0,1]`** (`0 ≤ r ≤ 1`), in every JB-algebra:
`U_{r+ε}` is an order automorphism (`Uo_orderAut`) within `(4ε + 2ε²)1` of `U_r` on
`[0,1]_A`. -/
theorem jQ_isLUB {r : A} (hr0 : 0 ≤ r) (hr1 : r ≤ ouUnit A) {S : Set A}
    (hS : S ⊆ Set.Icc 0 (ouUnit A)) {x : A} (hx1 : x ∈ Set.Icc 0 (ouUnit A)) (hx : IsLUB S x) :
    IsLUB (jQ r '' S) (jQ r x) := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact jQ_mono r (hx.1 hs)
  have hrn := ousNorm_le_one_of_mem hr0 hr1
  refine le_of_forall_le_add fun δ hδ => ?_
  set ε := min 1 (δ / 6) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε6 : ε ≤ δ / 6 := min_le_right _ _
  set η := 2 * ε + ε * ε
  have hη : 2 * η ≤ δ := by nlinarith
  have herr : ∀ v ∈ Set.Icc 0 (ouUnit A),
      -(η • ouUnit A) ≤ ε • ((2 : ℝ) • (r * v)) + (ε * ε) • v ∧
        ε • ((2 : ℝ) • (r * v)) + (ε * ε) • v ≤ η • ouUnit A :=
    fun v hv => bounds_of_norm_le (err_norm_le hrn (ousNorm_le_one_of_mem hv.1 hv.2) hε0.le)
  have hc : ε • ouUnit A ≤ r + ε • ouUnit A := le_add_of_nonneg_left hr0
  obtain ⟨hΦ, T, hT, h1, h2⟩ := Uo_orderAut hε0 hc
  have hL := isLUB_image_of_orderAut hΦ hT h1 h2 hx
  have hΦx : Uo (r + ε • ouUnit A) x ≤ u + η • ouUnit A := hL.2 (by
    rintro _ ⟨s, hs, rfl⟩
    rw [Uo_add_unit]
    exact add_le_add (hu ⟨s, hs, rfl⟩) (herr s (hS hs)).2)
  rw [Uo_add_unit] at hΦx
  have h3 := (herr x hx1).1
  have hδη : (2 * η) • ouUnit A ≤ δ • ouUnit A := ou_smul_unit_mono hη
  calc jQ r x ≤ u + η • ouUnit A + η • ouUnit A := by
        have := add_le_add hΦx (neg_le_neg h3)
        rw [neg_neg] at this
        calc jQ r x = jQ r x + (ε • ((2 : ℝ) • (r * x)) + (ε * ε) • x) +
              -(ε • ((2 : ℝ) • (r * x)) + (ε * ε) • x) := by abel
          _ ≤ _ := this
    _ = u + (2 * η) • ouUnit A := by rw [add_assoc, ← add_smul, two_mul]
    _ ≤ u + δ • ouUnit A := add_le_add (le_refl u) hδη


end

/-! ## 7. The hypothesis holds for special JB-algebras -/

noncomputable section Special

open JC

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hV : JBAlgebra V] {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (E : SpecialEmbedding V B)

include hV

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

theorem sp_opComm_iff {x y : V} : OpComm x y ↔ Commute (E.φ x) (E.φ y) := by
  have hr := opComm_iff E.toJC (LinearMap.mem_range_self E.φ x) (LinearMap.mem_range_self E.φ y)
  constructor
  · intro h
    refine hr.1 ?_
    rintro _ ⟨w, rfl⟩
    rw [← E.map_mul, ← E.map_mul, ← E.map_mul, ← E.map_mul, h w]
  · intro h w
    apply E.injective
    rw [E.map_mul, E.map_mul, E.map_mul, E.map_mul]
    exact hr.2 h _ (LinearMap.mem_range_self E.φ w)

theorem sp_sqrt {a : V} (ha : 0 ≤ a) : E.φ (jbSqrt a) = CFC.sqrt (E.φ a) := by
  have h1 : E.φ (jbSqrt a) * E.φ (jbSqrt a) = E.φ a := by
    rw [← jmul_self, ← E.map_mul, jbSqrt_mul_self ha]
  rw [← h1]
  exact (CFC.sqrt_mul_self _ ((E.nonneg_iff _).1 (jbSqrt_nonneg a))).symm

theorem sp_sq {a : V} (ha : 0 ≤ a) (b : V) : E.φ (sq a b) = sqrtConj (E.φ a) (E.φ b) := by
  rw [sq, jQ, map_sub, map_smul, E.map_mul, E.map_mul, E.map_mul, E.map_mul, ← jU, jU_eq,
    sp_sqrt E ha]
  rfl

theorem sp_continuous : Continuous E.φ :=
  AddMonoidHomClass.continuous_of_bound E.φ 1 fun x => by
    rw [one_mul, E.isometric]; rfl

theorem sp_commute_Ca {a b x : V} (hx : x ∈ (Ca a).carrier) (h : Commute (E.φ a) (E.φ b)) :
    Commute (E.φ x) (E.φ b) := by
  have hpow : ∀ n, E.φ (jbPow a n) = E.φ a ^ n := by
    intro n
    induction n with
    | zero => rw [jbPow_zero, E.unital, pow_zero]
    | succ n ih =>
      rw [jbPow_succ, E.map_mul, ih, jmul_of_commute ((Commute.refl _).pow_right n), pow_succ']
  have hpoly : ∀ p : Polynomial ℝ, Commute (E.φ (jbEv a p)) (E.φ b) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add]; exact hp.add_left hq
    | monomial n r =>
      rw [jbEv_monomial, map_smul, hpow]
      exact (h.pow_left n).smul_left r
  have hcl : IsClosed {x : V | Commute (E.φ x) (E.φ b)} :=
    isClosed_eq ((continuous_mul_const _).comp (sp_continuous E))
      ((continuous_const_mul _).comp (sp_continuous E))
  have hsub : Set.range (jbEv a) ⊆ {x : V | Commute (E.φ x) (E.φ b)} := by
    rintro _ ⟨p, rfl⟩; exact hpoly p
  exact hcl.closure_subset_iff.2 hsub (mem_Ca.1 hx)

/-- **The commutation input holds for every special JB-algebra**: van de Wetering's theorem
is Gudder–Greechie's `√a b √a = √b a √b ⇒ ab = ba` there, and the commutant of `C(c)` is the
(Jordan) intersection with a commutant in `B`. -/
theorem jbCommutation_of_special (E : SpecialEmbedding V B) : JBCommutation V where
  mem_comm a b ha hb h := by
    have hc : Commute (E.φ a) (E.φ b) :=
      commute_of_sqrtConj_eq ((E.nonneg_iff _).1 ha) ((E.nonneg_iff _).1 hb)
        (by rw [← sp_sq E ha, ← sp_sq E hb, h])
    exact fun x hx => (sp_opComm_iff E).2 (sp_commute_Ca E hx hc)
  mul_mem c y z _ hy hz := fun x hx => by
    have h1 := (sp_opComm_iff E).1 (hy x hx)
    have h2 := (sp_opComm_iff E).1 (hz x hx)
    refine (sp_opComm_iff E).2 ?_
    rw [E.map_mul]
    unfold jmul
    exact ((h1.mul_right h2).add_right (h2.mul_right h1)).smul_right _


end Special

/-! ## 8. JBW-algebras: `[0,1]_A` is a convex normal SEA -/

noncomputable section

variable {A : Type u} [AddCommGroup A] [Module ℝ A] [PartialOrder A] [OrderUnitSpace A] [Mul A]
  [hW : JBWAlgebra A]

include hW

/-- In `[0,1]_A` (`A` JBW), the supremum of a directed set is its least upper bound in `A`. -/
theorem isLUB_of_eIsSup {S : Set (Set.Icc (0 : A) (ouUnit A))} (hS : @EDirected _ (jbEA A) S)
    {x : Set.Icc (0 : A) (ouUnit A)} (hx : @EIsSup _ (jbEA A) S x) :
    IsLUB (Subtype.val '' S) x.1 := by
  let _ := jbEA A
  have hle := interval_le_iff (ouUnit A) (ou_unit_nonneg (X := A))
  obtain ⟨hne, hdir⟩ := hS
  refine JC.isLUB_of_Icc_sup hW.directedComplete (by rintro _ ⟨v, _, rfl⟩; exact v.2)
    (hne.image _) ?_ (by rintro _ ⟨v, hv, rfl⟩; exact (hle v x).mp (hx.1 v hv)) ?_
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz, h1, h2⟩ := hdir v hv w hw
    exact ⟨z.1, ⟨z, hz, rfl⟩, (hle v z).mp h1, (hle w z).mp h2⟩
  · intro t ht htub
    exact (hle x ⟨t, ht⟩).mp (hx.2 ⟨t, ht⟩ fun v hv => (hle v ⟨t, ht⟩).mpr (htub _ ⟨v, hv, rfl⟩))

theorem directedOn_val {S : Set (Set.Icc (0 : A) (ouUnit A))} (hS : @EDirected _ (jbEA A) S) :
    DirectedOn (· ≤ ·) (Subtype.val '' S) := by
  let _ := jbEA A
  have hle := interval_le_iff (ouUnit A) (ou_unit_nonneg (X := A))
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  obtain ⟨z, hz, h1, h2⟩ := hS.2 v hv w hw
  exact ⟨z.1, ⟨z, hz, rfl⟩, (hle v z).mp h1, (hle w z).mp h2⟩

/-- **S6, first half, in every JBW-algebra** (unconditional): `b ↦ U_{√a} b` preserves
suprema of directed subsets of `[0,1]_A`. -/
theorem jbw_seq_sup (a : Set.Icc (0 : A) (ouUnit A)) {S : Set (Set.Icc (0 : A) (ouUnit A))}
    {x : Set.Icc (0 : A) (ouUnit A)} (hS : @EDirected _ (jbEA A) S)
    (hx : @EIsSup _ (jbEA A) S x) : @EIsSup _ (jbEA A) (jbSeq a '' S) (jbSeq a x) := by
  let _ := jbEA A
  have hle := interval_le_iff (ouUnit A) (ou_unit_nonneg (X := A))
  have hL := jQ_isLUB (jbSqrt_nonneg a.1) (jbSqrt_le_one a.2.1 a.2.2)
    (by rintro _ ⟨v, _, rfl⟩; exact v.2) x.2 (isLUB_of_eIsSup hS hx)
  refine ⟨?_, fun y hy => (hle _ _).mpr (hL.2 ?_)⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (hle _ _).mpr (hL.1 ⟨s.1, ⟨s, hs, rfl⟩, rfl⟩)
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact (hle _ _).mp (hy _ ⟨s, hs, rfl⟩)

theorem jbw_directedComplete : @DirectedComplete _ (jbEA A) := by
  let _ := jbEA A
  have hle := interval_le_iff (ouUnit A) (ou_unit_nonneg (X := A))
  intro S hS
  obtain ⟨t, ht, htub, htleast⟩ := hW.directedComplete (Subtype.val '' S)
    (by rintro _ ⟨v, _, rfl⟩; exact v.2) (directedOn_val hS)
  exact ⟨⟨t, ht⟩, fun v hv => (hle v ⟨t, ht⟩).mpr (htub _ ⟨v, hv, rfl⟩),
    fun y hy => (hle ⟨t, ht⟩ y).mpr (htleast y.1 y.2 fun _ ⟨v, hv, e⟩ => by
      rw [← e]; exact (hle v y).mp (hy v hv))⟩

variable (A) in
/-- **The cited input for S6, second half, as an explicit hypothesis** (not proved here): in
the JBW-algebra `A`, for `c ≥ 0` the operator commutant of `C(c)` is closed under least
upper bounds of directed subsets of `[0,1]_A` (it is the fixed-point set of the normal maps
`U_p + U_{1−p}`, `p` the spectral idempotents of `c`). -/
structure JBWCommSup : Prop where
  comm_sup : ∀ c : A, 0 ≤ c → ∀ D : Set A, D ⊆ Set.Icc 0 (ouUnit A) → D.Nonempty →
    DirectedOn (· ≤ ·) D → ∀ x : A, IsLUB D x → D ⊆ comm c → x ∈ comm c

/-- **The JBW commutation input holds for every JBW-algebra with a normal special
embedding** (so `sea16_jbw` recovers `JC.sea16_special_normal`'s case). -/
theorem jbwCommSup_of_special {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (E : JC.SpecialEmbedding A B) (hn : IsNormalMap E.φ) : JBWCommSup A where
  comm_sup c _ D _ hne hdir x hx hDc := fun x' hx' => by
    refine (sp_opComm_iff E).2 ?_
    have hB := hn D x hne hdir hx
    let D' : Set (selfAdjoint B) := (fun v : A => (⟨E.φ v, E.sa v⟩ : selfAdjoint B)) '' D
    have hD' : IsLUB D' ⟨E.φ x, E.sa x⟩ := by
      refine ⟨?_, fun t ht => ?_⟩
      · rintro _ ⟨v, hv, rfl⟩; exact hB.1 ⟨v, hv, rfl⟩
      · exact hB.2 (by rintro _ ⟨v, hv, rfl⟩; exact ht ⟨v, hv, rfl⟩)
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ousNorm A x' + 1 := ⟨_, rfl⟩
    have hM : 0 < M := by have := ousNorm_nonneg_rc x'; rw [hMdef]; positivity
    set z := (2 * M)⁻¹ • (x' + M • ouUnit A)
    have hbd := ousNorm_bounds_le x'
    have hz0 : 0 ≤ z := ou_smul_nonneg (by positivity) (by
      have : -(M • ouUnit A) ≤ x' := le_trans (neg_le_neg (ou_smul_unit_mono (by linarith)))
        hbd.1
      rw [← sub_nonneg, sub_neg_eq_add] at this; exact this)
    have hz1 : z ≤ ouUnit A := by
      have hx'M : x' ≤ M • ouUnit A := hbd.2.trans (ou_smul_unit_mono (by linarith))
      have h1 : x' + M • ouUnit A ≤ (2 * M) • ouUnit A := by
        rw [two_mul, add_smul]
        exact add_le_add hx'M le_rfl
      have := ou_smul_le_smul (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * M)) h1
      rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this
    have hφz : E.φ z = (2 * M)⁻¹ • (E.φ x' + M • (1 : B)) := by
      rw [map_smul, map_add, map_smul, E.unital]
    have hφx' : E.φ x' = (2 * M) • E.φ z - M • (1 : B) := by
      rw [hφz, smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel_right]
    have hc : ∀ d ∈ D', Commute (E.φ z) (d : B) := by
      rintro _ ⟨v, hv, rfl⟩
      have h := (sp_opComm_iff E).1 (hDc hv x' hx')
      rw [hφz]
      exact (h.add_left ((Commute.one_left _).smul_left M)).smul_left _
    have hz := commute_of_isLUB ((E.nonneg_iff z).1 hz0)
      (by rw [← E.unital]; exact (E.le_iff _ _).1 hz1) (hne.image _) hD' hc
    rw [hφx']
    exact (hz.smul_left _).sub_left ((Commute.one_left _).smul_left M)

/-- `[0,1]_A` is a normal SEA with `a ∘ b = U_{√a} b`, for every JBW-algebra satisfying the
commutation inputs `JBCommutation` and `JBWCommSup`. -/
@[instance_reducible] def jbwNormalSEA (H : JBCommutation A) (H' : JBWCommSup A) :
    @NormalSEA (Set.Icc (0 : A) (ouUnit A)) (jbEA A) := by
  letI := jbEA A
  exact
  { jbSEA H with
    directedComplete := jbw_directedComplete
    seq_sup := fun a {_ _} hS hx => jbw_seq_sup a hS hx
    comm_sup := fun a {S x} hS hx hcomm => by
      refine (jbSeq_comm_iff H).2 (compat_of_mem_comm H a.2.1 ?_)
      refine H'.comm_sup a.1 a.2.1 (Subtype.val '' S) (by rintro _ ⟨v, _, rfl⟩; exact v.2)
        (hS.1.image _) (directedOn_val hS) x.1 (isLUB_of_eIsSup hS hx) ?_
      rintro _ ⟨s, hs, rfl⟩
      exact mem_comm_of_compat ((jbSeq_comm_iff H).1 (hcomm s hs)) }

/-- **SEA 16** (`ex:canonical-sea`, second.tex:475), "any JBW-algebra is a convex normal SEA",
for every JBW-algebra `A` (REC 48) satisfying the commutation inputs `JBCommutation A` and
`JBWCommSup A`: `[0,1]_A` is convex and a normal SEA (`jbwNormalSEA`) with product
`a ∘ b = U_r b`, `r` the unique positive square root of `a`. -/
theorem sea16_jbw (H : JBCommutation A) (H' : JBWCommSup A) :
    @IsConvex _ (jbEA A) ∧
    ∀ a b : Set.Icc (0 : A) (ouUnit A),
      ∃! r : A, 0 ≤ r ∧ r * r = a.1 ∧
        (@SequentialEffectAlgebra.seq _ (jbEA A)
          (jbwNormalSEA H H').toSequentialEffectAlgebra a b).1 =
          (2 : ℝ) • (r * (r * b.1)) - (r * r) * b.1 :=
  sea16_jb H


end

end Papers.SEA.JBAll
