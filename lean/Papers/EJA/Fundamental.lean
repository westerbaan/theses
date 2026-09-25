/-
Papers/EJA/Fundamental.lean

EJA 9, item 5: the **fundamental formula** `Q_{Q_a b} = Q_a Q_b Q_a` of the
quadratic representation, for the theses tree's (finite-dimensional)
Euclidean Jordan algebras, together with item 6 (`Q_a` is invertible iff `a`
is, with `Q_a⁻¹ = Q_{a⁻¹}`) and the power law `Q_{aⁿ} = Q_aⁿ`.
A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, arXiv:1805.11496, `../papers/1805.11496/main.tex`.

The paper cites the formula (Hanche-Olsen–Størmer 2.4.13, through Macdonald's
theorem).  Macdonald's theorem is not available, and the proof here is
**Macdonald-free and tree-native** (the route of `docs/research/eja-dagger.md`
§1, "reduction of the general FF to the two-valued case"):

1. **The Jordan triple product** `{x y z} = (x y) z + (y z) x − (x z) y`
   (`ffT`) has `U_b y = {b y b}`, and every multiplication operator `L_c` is a
   *triple derivation*: `c {x y z} = {(c x) y z} − {x (c y) z} + {x y (c z)}`
   (`ffT_der`).  This is a multilinear identity of degree 4, and it is the sum
   of three instances of the linearised Jordan identity `eja_lin` (found by
   solving the linear system over the free commutative magma in degree 4).
2. Consequently, for an idempotent `c` the triple product of Peirce
   eigenvectors of eigenvalues `i, j, k` is an eigenvector of eigenvalue
   `i − j + k`, hence zero unless `i − j + k ∈ {0, ½, 1}` (the Peirce cubic
   `eja_idem_cubic`): the **Peirce rules for the triple product**.
3. For a *two-valued* `a = λ c + μ (1 − c)`, `U_a` acts on the Peirce space
   of eigenvalue `m` as the scalar `f m` (`λ²`, `λμ`, `μ²`), and the Peirce
   rules make `U_{U_a b} x = U_a U_b U_a x` a term-by-term identity over the
   27 triples of Peirce components: `f i f k = f j f (i − j + k)`
   (`ejaU_ejaU_two_valued`).
4. The fundamental formula is closed under composition of commuting
   quadratic representations (`ffFF_comp`), and by the spectral theorem and
   the one-family composition law `eja_U_family_comp'` a general `U_a` is a
   commuting product of two-valued ones, one per spectral value
   (`ejaU_ejaU`).

Items 6 and the power law are then short: `U_a` is bijective iff `a` has a
Jordan inverse (`a * b = 1`, `a² * b = a`), iff some `b` has `a * b = 1`, iff
no spectral value of `a` vanishes; in that case `U_b` is the two-sided inverse
of `U_a`.  Item 6 does not need the fundamental formula; the power law does.
-/
import Theses.B.Eff.JordanAlgebras

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra

universe u

section Fundamental

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-! ## The Jordan triple product and its derivations -/

/-- The **Jordan triple product** `{x y z} = (x y) z + (y z) x − (x z) y`
(in a special Jordan algebra, `½ (x y z + z y x)`). -/
def ffT (x y z : V) : V := x * y * z + y * z * x - x * z * y

omit [Module ℝ V] [One V] [PartialOrder V] [EuclideanJordanAlgebra V] in
theorem ffT_def (x y z : V) : ffT x y z = x * y * z + y * z * x - x * z * y := rfl

/-- `U_b y = {b y b}`. -/
theorem ejaU_eq_ffT (b y : V) : ejaU b y = ffT b y b := by
  rw [ejaU_apply, ffT_def, eja_mul_comm (b * y) b, eja_mul_comm (y * b) b,
    eja_mul_comm y b]
  module

theorem ffT_add_left (x x' y z : V) : ffT (x + x') y z = ffT x y z + ffT x' y z := by
  simp only [ffT_def, eja_add_mul, eja_mul_add]; abel

theorem ffT_add_mid (x y y' z : V) : ffT x (y + y') z = ffT x y z + ffT x y' z := by
  simp only [ffT_def, eja_add_mul, eja_mul_add]; abel

theorem ffT_add_right (x y z z' : V) : ffT x y (z + z') = ffT x y z + ffT x y z' := by
  simp only [ffT_def, eja_add_mul, eja_mul_add]; abel

theorem ffT_smul_left (r : ℝ) (x y z : V) : ffT (r • x) y z = r • ffT x y z := by
  simp only [ffT_def, eja_smul_mul, eja_mul_smul, smul_sub, smul_add]

theorem ffT_smul_mid (r : ℝ) (x y z : V) : ffT x (r • y) z = r • ffT x y z := by
  simp only [ffT_def, eja_smul_mul, eja_mul_smul, smul_sub, smul_add]

theorem ffT_smul_right (r : ℝ) (x y z : V) : ffT x y (r • z) = r • ffT x y z := by
  simp only [ffT_def, eja_smul_mul, eja_mul_smul, smul_sub, smul_add]

/-- The triple product as a trilinear map. -/
def ffTL : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V where
  toFun x := LinearMap.mk₂ ℝ (fun y z => ffT x y z) (fun y y' z => ffT_add_mid x y y' z)
    (fun r y z => ffT_smul_mid r x y z) (fun y z z' => ffT_add_right x y z z')
    (fun r y z => ffT_smul_right r x y z)
  map_add' x x' := by ext y z; exact ffT_add_left x x' y z
  map_smul' r x := by ext y z; exact ffT_smul_left r x y z

@[simp] theorem ffTL_apply (x y z : V) : ffTL x y z = ffT x y z := rfl

/-- **Every multiplication operator is a triple derivation**:
`c {x y z} = {(c x) y z} − {x (c y) z} + {x y (c z)}`.  The sum of the three
instances `(c,x,y,z)`, `(c,x,z,y)` (negated) and `(c,y,z,x)` of the
linearised Jordan identity. -/
theorem ffT_der (c x y z : V) :
    c * ffT x y z = ffT (c * x) y z - ffT x (c * y) z + ffT x y (c * z) := by
  have h1 := eja_lin c x y z
  have h2 := eja_lin c x z y
  have h3 := eja_lin c y z x
  simp only [ffT_def, eja_mul_sub, eja_mul_add]
  simp only [eja_mul_comm] at h1 h2 h3 ⊢
  linear_combination (norm := module) h1 - h2 + h3

/-- The triple product of eigenvectors of `L_c` with eigenvalues `i, j, k` is
an eigenvector with eigenvalue `i − j + k`. -/
theorem ffT_eigen {c u y v : V} {i j k : ℝ} (hu : c * u = i • u) (hy : c * y = j • y)
    (hv : c * v = k • v) : c * ffT u y v = (i - j + k) • ffT u y v := by
  rw [ffT_der, hu, hy, hv, ffT_smul_left, ffT_smul_mid, ffT_smul_right]
  module

/-- **The Peirce cubic on an eigenvector**: for an idempotent `c` and
`c w = m w`, `(2 m³ − 3 m² + m) w = 0`, so `w = 0` unless `m ∈ {0, ½, 1}`. -/
theorem ff_eigen_cubic {c w : V} (hc : c * c = c) {m : ℝ} (hw : c * w = m • w) :
    (2 * m ^ 3 - 3 * m ^ 2 + m) • w = 0 := by
  have h := eja_idem_cubic c hc w
  simp only [hw, eja_mul_smul, smul_smul] at h
  linear_combination (norm := module) h

/-! ## The two-valued case -/

/-- The scalar by which `U (λ c + μ (1 − c))` acts on the Peirce space of
eigenvalue `m` (`λ²`, `λμ`, `μ²` at `m = 1, ½, 0`: Lagrange interpolation). -/
def ffCoef (l m t : ℝ) : ℝ :=
  l * l * (t * (2 * t - 1)) + l * m * (4 * t * (1 - t)) + m * m * ((1 - t) * (1 - 2 * t))

/-- `U (λ c + μ (1 − c))` on any eigenvector of `L_c`. -/
theorem ejaU_two_valued_eigen {c w : V} (hc : c * c = c) (l m : ℝ) {t : ℝ}
    (hw : c * w = t • w) : ejaU (l • c + m • (1 - c)) w = ffCoef l m t • w := by
  have hw' : (1 - c) * w = (1 - t) • w := by
    rw [eja_sub_mul, eja_one_mul, hw]; module
  rw [ejaU_two_valued hc l m w, ejaPone_apply, ejaPone_apply, ejaPhalf_apply, hw, hw',
    eja_mul_smul, eja_mul_smul, hw, hw', smul_smul, smul_smul, ffCoef]
  module

/-- The Peirce eigenvalues `1, ½, 0`. -/
noncomputable def ffEv : Fin 3 → ℝ := ![1, 2⁻¹, 0]

/-- The Peirce projections `P₁, P½, P₀` of `c`. -/
def ffPr (c : V) : Fin 3 → V →ₗ[ℝ] V := ![ejaPone c, ejaPhalf c, ejaPone (1 - c)]

theorem ffPr_sum (c y : V) : ∑ i, ffPr c i y = y := by
  rw [Fin.sum_univ_three]
  exact eja_peirce_sum c y

theorem ffPr_eigen {c : V} (hc : c * c = c) (i : Fin 3) (y : V) :
    c * ffPr c i y = ffEv i • ffPr c i y := by
  fin_cases i
  · simp only [ffPr, ffEv, Fin.zero_eta, Matrix.cons_val_zero, one_smul]
    exact eja_mul_pone c hc y
  · simp only [ffPr, ffEv, Fin.mk_one, Matrix.cons_val_one]
    exact eja_mul_phalf c hc y
  · simp only [ffPr, ffEv, Fin.reduceFinMk, Matrix.cons_val, zero_smul]
    exact eja_mul_pzero hc y

/-- **The Peirce rules, weighted**: for Peirce components `u, y, v` of
eigenvalues `i, j, k`, `f i f k {u y v} = f j f (i − j + k) {u y v}`; when
`i − j + k ∉ {0, ½, 1}` both sides vanish because `{u y v} = 0`. -/
theorem ff_weight {c : V} (hc : c * c = c) (l m : ℝ) (i j k : Fin 3) {u y v : V}
    (hu : c * u = ffEv i • u) (hy : c * y = ffEv j • y) (hv : c * v = ffEv k • v) :
    (ffCoef l m (ffEv i) * ffCoef l m (ffEv k)) • ffT u y v
      = ffCoef l m (ffEv j) • (ffCoef l m (ffEv i - ffEv j + ffEv k) • ffT u y v) := by
  have hcub := ff_eigen_cubic hc (ffT_eigen hu hy hv)
  rw [smul_smul]
  rcases smul_eq_zero.mp hcub with h | h
  · congr 1
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      (try simp only [ffEv, ffCoef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢) <;>
      (try norm_num at h) <;> (try norm_num) <;> ring
  · rw [h, smul_zero, smul_zero]

/-- **The fundamental formula for a two-valued element** `a = λ c + μ (1 − c)`
at an idempotent `c`. -/
theorem ejaU_ejaU_two_valued {c : V} (hc : c * c = c) (l m : ℝ) (b : V) :
    ejaU (ejaU (l • c + m • (1 - c)) b)
      = ejaU (l • c + m • (1 - c)) * ejaU b * ejaU (l • c + m • (1 - c)) := by
  set a := l • c + m • (1 - c) with ha
  have hUa : ∀ y : V, ejaU a y = ∑ i, ffCoef l m (ffEv i) • ffPr c i y := by
    intro y
    conv_lhs => rw [← ffPr_sum c y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => ejaU_two_valued_eigen hc l m (ffPr_eigen hc i y)
  ext x
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hL : ejaU (ejaU a b) x = ffTL (∑ i, ffCoef l m (ffEv i) • ffPr c i b)
      (∑ j, ffPr c j x) (∑ k, ffCoef l m (ffEv k) • ffPr c k b) := by
    rw [ejaU_eq_ffT, hUa b, ffPr_sum]; rfl
  have hR : ejaU a (ejaU b (ejaU a x)) = ejaU a (ffTL (∑ i, ffPr c i b)
      (∑ j, ffCoef l m (ffEv j) • ffPr c j x) (∑ k, ffPr c k b)) := by
    rw [ejaU_eq_ffT b, hUa x, ffPr_sum]; rfl
  rw [hL, hR]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [ffTL_apply, ejaU_two_valued_eigen hc l m
    (ffT_eigen (ffPr_eigen hc k b) (ffPr_eigen hc j x) (ffPr_eigen hc i b)), mul_comm]
  exact ff_weight hc l m k j i (ffPr_eigen hc k b) (ffPr_eigen hc j x) (ffPr_eigen hc i b)

/-! ## Reduction to the two-valued case -/

/-- `a` satisfies the fundamental formula for every `b`. -/
def ffFF (a : V) : Prop := ∀ b : V, ejaU (ejaU a b) = ejaU a * ejaU b * ejaU a

theorem ffFF_one : ffFF (1 : V) := by
  intro b
  ext y
  simp [ejaU_one]

/-- **The fundamental formula is closed under commuting composition**: if it
holds for `a₁` and `a₂` and `U a₁ U a₂ = U a = U a₂ U a₁`, it holds for `a`. -/
theorem ffFF_comp {a a₁ a₂ : V} (h₁ : ffFF a₁) (h₂ : ffFF a₂)
    (h12 : ejaU a₁ * ejaU a₂ = ejaU a) (h21 : ejaU a₂ * ejaU a₁ = ejaU a) : ffFF a := by
  intro b
  have hb : ejaU a b = ejaU a₁ (ejaU a₂ b) := by rw [← h12]; rfl
  calc ejaU (ejaU a b) = ejaU a₁ * (ejaU a₂ * ejaU b * ejaU a₂) * ejaU a₁ := by
        rw [hb, h₁, h₂]
    _ = (ejaU a₁ * ejaU a₂) * ejaU b * (ejaU a₂ * ejaU a₁) := by simp only [mul_assoc]
    _ = ejaU a * ejaU b * ejaU a := by rw [h12, h21]

/-- **EJA 9** (`prop:quadraticrep`, main.tex:323, Proposition), item 5: the
**fundamental formula** (the paper's "fundamental equality")
`Q_{Q_a b} = Q_a Q_b Q_a`, for the tree's finite-dimensional Euclidean Jordan
algebras, `Q_a = ejaU a = 2 L_a² − L_{a²}`.  The paper cites
Hanche-Olsen–Størmer 2.4.13 (through Macdonald's theorem); the proof here is
Macdonald-free: by the spectral theorem `a = ∑ λ e_λ`, and `U_a` is the
commuting product over the spectral values of the two-valued
`U (λ e_λ + (1 − e_λ))` (one-family law `eja_U_family_comp'`), for each of
which the formula is the Peirce computation `ejaU_ejaU_two_valued`; the
formula passes to commuting products (`ffFF_comp`). -/
theorem ejaU_ejaU (a b : V) : ejaU (ejaU a b) = ejaU a * ejaU b * ejaU a := by
  classical
  obtain ⟨s, e, hidem, horth, -, hone, ha⟩ := eja_spectral a
  have hU : ∀ g g' : ℝ → ℝ, ejaU (∑ l ∈ s, g l • e l) * ejaU (∑ l ∈ s, g' l • e l)
      = ejaU (∑ l ∈ s, (g l * g' l) • e l) := fun g g' =>
    LinearMap.ext (eja_U_family_comp' g g' hidem horth hone)
  have key : ∀ t : Finset ℝ, ffFF (∑ l ∈ s, (if l ∈ t then l else 1) • e l) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, ite_false, one_smul, hone]
      exact ffFF_one
    | insert l₀ t hl₀ ih =>
      set g₁ : ℝ → ℝ := fun l => if l = l₀ then l₀ else 1 with hg₁
      set g₂ : ℝ → ℝ := fun l => if l ∈ t then l else 1 with hg₂
      have hg : ∀ l, (if l ∈ insert l₀ t then l else 1) = g₁ l * g₂ l := by
        intro l
        simp only [hg₁, hg₂, Finset.mem_insert]
        by_cases h0 : l = l₀
        · subst h0; simp [hl₀]
        · by_cases ht : l ∈ t <;> simp [h0, ht]
      have hsum : (∑ l ∈ s, (if l ∈ insert l₀ t then l else 1) • e l)
          = ∑ l ∈ s, (g₁ l * g₂ l) • e l :=
        Finset.sum_congr rfl fun l _ => by rw [hg l]
      have hsum' : (∑ l ∈ s, (g₁ l * g₂ l) • e l) = ∑ l ∈ s, (g₂ l * g₁ l) • e l :=
        Finset.sum_congr rfl fun l _ => by rw [mul_comm]
      -- the two-valued factor
      set c : V := if l₀ ∈ s then e l₀ else 0 with hc
      have hcc : c * c = c := by
        by_cases h : l₀ ∈ s
        · simp only [hc, ite_eq_left h]; exact hidem l₀ h
        · simp only [hc, ite_eq_right h, eja_mul_zero]
      have hcsum : (∑ l ∈ s, (if l = l₀ then e l else 0)) = c := by
        rw [Finset.sum_ite_eq']
      have h1 : (∑ l ∈ s, g₁ l • e l) = l₀ • c + (1 : ℝ) • (1 - c) := by
        have : ∀ l ∈ s, g₁ l • e l = e l + (l₀ - 1) • (if l = l₀ then e l else 0) := by
          intro l _
          simp only [hg₁]
          by_cases h0 : l = l₀
          · subst h0; simp only [ite_true]; module
          · simp only [h0, ite_false, one_smul, smul_zero, add_zero]
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.smul_sum, hcsum, hone]
        module
      have hF₁ : ffFF (∑ l ∈ s, g₁ l • e l) := by
        rw [h1]; exact ejaU_ejaU_two_valued hcc l₀ 1
      rw [hsum]
      refine ffFF_comp hF₁ ih (hU g₁ g₂) ?_
      rw [hU g₂ g₁, hsum']
  have hfin : a = ∑ l ∈ s, (if l ∈ s then l else 1) • e l := by
    rw [ha]
    exact Finset.sum_congr rfl fun l hl => by rw [ite_eq_left hl]
  rw [hfin]
  exact key s b

/-- The fundamental formula applied to a vector. -/
theorem ejaU_ejaU_apply (a b y : V) :
    ejaU (ejaU a b) y = ejaU a (ejaU b (ejaU a y)) := by
  rw [ejaU_ejaU]; rfl

/-! ## Item 6: invertibility, and the power law -/

/-- Multiplying a combination of a spectral family by one of its members. -/
theorem ff_family_mul {s : Finset ℝ} {e : ℝ → V}
    (hidem : ∀ l ∈ s, e l * e l = e l)
    (horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0) (g : ℝ → ℝ) {l₀ : ℝ}
    (hl₀ : l₀ ∈ s) : (∑ l ∈ s, g l • e l) * e l₀ = g l₀ • e l₀ := by
  classical
  have he : e l₀ = ∑ k ∈ s, (if k = l₀ then (1 : ℝ) else 0) • e k := by
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', ite_eq_left hl₀]
  rw [he, eja_ortho_mul hidem horth, ← he]
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', ite_eq_left hl₀]

/-- **The spectral inverse**: if no spectral value of `a = ∑ λ e_λ` vanishes,
`a' = ∑ λ⁻¹ e_λ` is a Jordan inverse of `a` (`a a' = 1`, `a² a' = a`) and
`U a'` is the two-sided inverse of `U a`. -/
theorem ff_spectral_inv {s : Finset ℝ} {e : ℝ → V}
    (hidem : ∀ l ∈ s, e l * e l = e l)
    (horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0) (hone : ∑ l ∈ s, e l = 1)
    (hnz : ∀ l ∈ s, l ≠ 0) :
    (∑ l ∈ s, l • e l) * (∑ l ∈ s, l⁻¹ • e l) = 1 ∧
    ((∑ l ∈ s, l • e l) * (∑ l ∈ s, l • e l)) * (∑ l ∈ s, l⁻¹ • e l) = ∑ l ∈ s, l • e l ∧
    ejaU (∑ l ∈ s, l • e l) * ejaU (∑ l ∈ s, l⁻¹ • e l) = 1 ∧
    ejaU (∑ l ∈ s, l⁻¹ • e l) * ejaU (∑ l ∈ s, l • e l) = 1 := by
  have h1 : (∑ l ∈ s, (l * l⁻¹) • e l) = 1 := by
    rw [← hone]
    exact Finset.sum_congr rfl fun l hl => by rw [mul_inv_cancel₀ (hnz l hl), one_smul]
  have h1' : (∑ l ∈ s, (l⁻¹ * l) • e l) = 1 := by
    rw [← hone]
    exact Finset.sum_congr rfl fun l hl => by rw [inv_mul_cancel₀ (hnz l hl), one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eja_ortho_mul hidem horth (fun l => l) (fun l => l⁻¹)]; exact h1
  · rw [eja_ortho_mul hidem horth (fun l => l) (fun l => l),
      eja_ortho_mul hidem horth (fun l => l * l) (fun l => l⁻¹)]
    exact Finset.sum_congr rfl fun l hl => by
      rw [mul_assoc, mul_inv_cancel₀ (hnz l hl), mul_one]
  · ext y
    rw [Module.End.mul_apply, eja_U_family_comp' (fun l => l) (fun l => l⁻¹) hidem horth hone,
      h1, ejaU_one]
    rfl
  · ext y
    rw [Module.End.mul_apply, eja_U_family_comp' (fun l => l⁻¹) (fun l => l) hidem horth hone,
      h1', ejaU_one]
    rfl

/-- If `a b = 1` then no spectral value of `a` vanishes: an idempotent `e`
with `a e = 0` has `τ(e) = B(a b, e) = B(b, a e) = 0`, so `e = 0`. -/
theorem ff_spectral_ne_zero_of_mul_eq_one {a b : V} (hab : a * b = 1) {s : Finset ℝ}
    {e : ℝ → V} (hidem : ∀ l ∈ s, e l * e l = e l)
    (horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0) (hne : ∀ l ∈ s, e l ≠ 0)
    (ha : a = ∑ l ∈ s, l • e l) : ∀ l ∈ s, l ≠ 0 := by
  intro l hl h0
  subst h0
  have hae : a * e 0 = 0 := by
    rw [ha, ff_family_mul hidem horth (fun l => l) hl, zero_smul]
  have hB : ejaB (a * b) (e 0) = 0 := by
    rw [ejaB_assoc, hae, ejaB, eja_mul_zero, map_zero]
  rw [hab, ejaB, eja_one_mul] at hB
  exact absurd hB (ne_of_gt (eja_tr_idem_pos (e 0) (hidem 0 hl) (hne 0 hl)))

/-- **EJA 9** (`prop:quadraticrep`, main.tex:323, Proposition), item 6, first
half, with "`a` invertible" read as "`a` has a right inverse for the Jordan
product": `Q_a` is invertible iff `a * b = 1` for some `b`. -/
theorem ejaU_bijective_iff_exists_mul_eq_one (a : V) :
    Function.Bijective (ejaU a) ↔ ∃ b : V, a * b = 1 := by
  obtain ⟨s, e, hidem, horth, hne, hone, ha⟩ := eja_spectral a
  constructor
  · intro hbij
    have hnz : ∀ l ∈ s, l ≠ 0 := by
      intro l hl h0
      subst h0
      have hae : a * e 0 = 0 := by
        rw [ha, ff_family_mul hidem horth (fun l => l) hl, zero_smul]
      have haae : (a * a) * e 0 = 0 := by
        rw [ha, eja_ortho_mul hidem horth (fun l => l) (fun l => l),
          ff_family_mul hidem horth (fun l => l * l) hl, mul_zero, zero_smul]
      have hU : ejaU a (e 0) = ejaU a 0 := by
        rw [ejaU_apply, hae, haae, eja_mul_zero, smul_zero, sub_zero, map_zero]
      exact hne 0 hl (hbij.1 hU)
    exact ⟨_, ha ▸ (ff_spectral_inv hidem horth hone hnz).1⟩
  · rintro ⟨b, hab⟩
    have hnz := ff_spectral_ne_zero_of_mul_eq_one hab hidem horth hne ha
    obtain ⟨-, -, h3, h4⟩ := ff_spectral_inv hidem horth hone hnz
    rw [← ha] at h3 h4
    refine Function.bijective_iff_has_inverse.mpr ⟨ejaU (∑ l ∈ s, l⁻¹ • e l), ?_, ?_⟩
    · intro y; exact congrArg (fun f : V →ₗ[ℝ] V => f y) h4
    · intro y; exact congrArg (fun f : V →ₗ[ℝ] V => f y) h3

/-- **EJA 9** (`prop:quadraticrep`, main.tex:323, Proposition), item 6, first
half, with the usual (McCrimmon) notion of a **Jordan inverse** `b` of `a`:
`a * b = 1` and `a² * b = a`.  `Q_a` is invertible iff `a` is. -/
theorem ejaU_bijective_iff (a : V) :
    Function.Bijective (ejaU a) ↔ ∃ b : V, a * b = 1 ∧ (a * a) * b = a := by
  constructor
  · intro hbij
    obtain ⟨s, e, hidem, horth, hne, hone, ha⟩ := eja_spectral a
    obtain ⟨b, hab⟩ := (ejaU_bijective_iff_exists_mul_eq_one a).mp hbij
    have hnz := ff_spectral_ne_zero_of_mul_eq_one hab hidem horth hne ha
    obtain ⟨h1, h2, -, -⟩ := ff_spectral_inv hidem horth hone hnz
    rw [← ha] at h1 h2
    exact ⟨_, h1, h2⟩
  · rintro ⟨b, hab, -⟩
    exact (ejaU_bijective_iff_exists_mul_eq_one a).mpr ⟨b, hab⟩

/-- `Q_a` is a unit of `End V` iff `a` has a Jordan inverse. -/
theorem isUnit_ejaU_iff (a : V) :
    IsUnit (ejaU a) ↔ ∃ b : V, a * b = 1 ∧ (a * a) * b = a := by
  rw [Module.End.isUnit_iff, ejaU_bijective_iff]

/-- `U_a b = a` for a Jordan inverse `b` of `a`. -/
theorem ejaU_jordan_inv {a b : V} (h1 : a * b = 1) (h2 : (a * a) * b = a) :
    ejaU a b = a := by
  rw [ejaU_apply, h1, h2, eja_mul_one]; module

/-- **EJA 9** (`prop:quadraticrep`, main.tex:323, Proposition), item 6, second
half: **`Q_a⁻¹ = Q_{a⁻¹}`**.  For a Jordan inverse `b` of `a` (`a * b = 1`,
`a² * b = a`), `U b` is the two-sided inverse of `U a`.  (`b` is the spectral
inverse `∑ λ⁻¹ e_λ`: both are sent to `a` by the injective `U a`.) -/
theorem ejaU_inv {a b : V} (h1 : a * b = 1) (h2 : (a * a) * b = a) :
    ejaU a * ejaU b = 1 ∧ ejaU b * ejaU a = 1 := by
  obtain ⟨s, e, hidem, horth, hne, hone, ha⟩ := eja_spectral a
  have hnz := ff_spectral_ne_zero_of_mul_eq_one h1 hidem horth hne ha
  obtain ⟨k1, k2, k3, k4⟩ := ff_spectral_inv hidem horth hone hnz
  rw [← ha] at k1 k2 k3 k4
  have hbij := (ejaU_bijective_iff_exists_mul_eq_one a).mpr ⟨b, h1⟩
  have hb : b = ∑ l ∈ s, l⁻¹ • e l :=
    hbij.1 (by rw [ejaU_jordan_inv h1 h2, ejaU_jordan_inv k1 k2])
  rw [hb]
  exact ⟨k3, k4⟩

/-- The Jordan inverse is unique. -/
theorem ff_jordan_inv_unique {a b b' : V} (h1 : a * b = 1) (h2 : (a * a) * b = a)
    (h1' : a * b' = 1) (h2' : (a * a) * b' = a) : b = b' :=
  ((ejaU_bijective_iff_exists_mul_eq_one a).mpr ⟨b, h1⟩).1
    (by rw [ejaU_jordan_inv h1 h2, ejaU_jordan_inv h1' h2'])

/-- `U_a a^n = a^(n+2)` (power-associativity). -/
theorem ejaU_ejaPow (a : V) (n : ℕ) : ejaU a (ejaPow a n) = ejaPow a (n + 2) := by
  have h2 : (a * a) * ejaPow a n = ejaPow a (n + 2) := by
    rw [← ejaPow_two, eja_pow_mul_pow, add_comm]
  rw [ejaU_apply, h2, ← ejaPow_succ, ← ejaPow_succ]
  module

/-- **The power law** `U_{aⁿ} = (U_a)ⁿ`, from the fundamental formula:
`U_{a^(n+2)} = U_{U_a aⁿ} = U_a U_{aⁿ} U_a`. -/
theorem ejaU_pow (a : V) (n : ℕ) : ejaU (ejaPow a n) = ejaU a ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [ejaPow_zero, ejaU_one, pow_zero]; rfl
    | 1, _ => rw [ejaPow_one, pow_one]
    | n + 2, ih =>
      rw [← ejaU_ejaPow, ejaU_ejaU, ih n (by omega), pow_succ, pow_succ',
        (Commute.pow_right (Commute.refl (ejaU a)) n).eq, mul_assoc]

end Fundamental

end Papers.EJA
