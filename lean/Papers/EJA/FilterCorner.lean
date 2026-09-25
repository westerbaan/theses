import Papers.EJA.Prelim

/-!
# EJA §3: filters and corners (points 14–25)

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex`, Section 3 up to
the polar decomposition.  Over the tree's (finite-dimensional) Euclidean Jordan
algebras and positive subunital maps (`EJAPsu`, `EJAPSUMap`); see
`Papers/EJA/PLAN.md` §0 and the header of `Prelim.lean`.

Infrastructure first (not numbered in the paper, but used by EJA 25 and stated
in the text before it): the positive square root `√q`, which the paper calls
"the unique positive element with `√q * √q = q`" — its uniqueness is
`ejaSqrt_unique`, by polynomial interpolation on the spectrum; and the filter
data at an effect, with the support idempotent identified as `⌈q⌉`.
-/

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra CategoryTheory

universe u

section Sqrt

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

open Polynomial

/-- Powers of a combination of an orthogonal family of idempotents summing to
`1`. -/
theorem ejaPow_ortho {s : Finset ℝ} {e : ℝ → V} (hidem : ∀ l ∈ s, e l * e l = e l)
    (horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0) (hsum : ∑ l ∈ s, e l = 1)
    (μ : ℝ → ℝ) (n : ℕ) :
    ejaPow (∑ l ∈ s, μ l • e l) n = ∑ l ∈ s, (μ l ^ n) • e l := by
  induction n with
  | zero => simp [hsum]
  | succ n ih =>
    rw [ejaPow_succ, ih, eja_ortho_mul hidem horth]
    exact Finset.sum_congr rfl fun l _ => by rw [pow_succ, mul_comm]

/-- Evaluating a polynomial at a combination of an orthogonal family of
idempotents summing to `1` evaluates it at the coefficients. -/
theorem ejaEv_ortho {s : Finset ℝ} {e : ℝ → V} (hidem : ∀ l ∈ s, e l * e l = e l)
    (horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0) (hsum : ∑ l ∈ s, e l = 1)
    (μ : ℝ → ℝ) (P : ℝ[X]) :
    ejaEv (∑ l ∈ s, μ l • e l) P = ∑ l ∈ s, (P.eval (μ l)) • e l := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, hP, hQ, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [eval_add, add_smul]
  | monomial n a =>
    rw [ejaEv_monomial, ejaPow_ortho hidem horth hsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [eval_monomial, smul_smul]

/-- **Uniqueness of positive square roots** (main.tex, the text before EJA 25:
"`√q` … is the unique positive element such that `√q * √q = q`"). -/
theorem sqrt_unique {b c : V} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : b * b = c * c) : b = c := by
  classical
  obtain ⟨s, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral b
  obtain ⟨s', e', hidem', horth', hne0', hsum', hdec'⟩ := eja_spectral c
  set T : Finset ℝ := (s ∪ s').image fun l => l * l with hTdef
  set P : ℝ[X] := Lagrange.interpolate T id (fun x => Real.sqrt x) with hPdef
  have hP : ∀ x ∈ T, P.eval x = Real.sqrt x := fun x hx =>
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => h) hx
  have key : ∀ {x : V} {t : Finset ℝ} {f : ℝ → V}, 0 ≤ x →
      (∀ l ∈ t, f l * f l = f l) → (∀ l ∈ t, ∀ k ∈ t, l ≠ k → f l * f k = 0) →
      (∀ l ∈ t, f l ≠ 0) → ∑ l ∈ t, f l = 1 → x = ∑ l ∈ t, l • f l →
      (∀ l ∈ t, l * l ∈ T) → x = ejaEv (x * x) P := by
    intro x t f hx hidf horf hnef hsumf hdecf hTt
    have hl : ∀ l ∈ t, 0 ≤ l := by
      refine (eja_ortho_isSumSq_iff hidf horf hnef (fun r => r)).mp ?_
      rw [← hdecf]; exact (eja_nonneg_iff x).mp hx
    have hxx : x * x = ∑ l ∈ t, (l * l) • f l := by
      rw [hdecf, eja_ortho_mul hidf horf]
    rw [hxx, ejaEv_ortho hidf horf hsumf (fun l => l * l)]
    conv_lhs => rw [hdecf]
    refine Finset.sum_congr rfl fun l hl' => ?_
    rw [hP _ (hTt l hl'), Real.sqrt_mul_self (hl l hl')]
  have hb' := key hb hidem horth hne0 hsum hdec (fun l hl => by
    rw [hTdef]; exact Finset.mem_image.mpr ⟨l, Finset.mem_union_left _ hl, rfl⟩)
  have hc' := key hc hidem' horth' hne0' hsum' hdec' (fun l hl => by
    rw [hTdef]; exact Finset.mem_image.mpr ⟨l, Finset.mem_union_right _ hl, rfl⟩)
  rw [hb', hc', h]

open Classical in
/-- The positive square root `√q` of a positive `q` (junk `0` elsewhere). -/
noncomputable def ejaSqrt (q : V) : V :=
  if h : 0 ≤ q then (eja_exists_nonneg_sqrt h).choose else 0

theorem ejaSqrt_spec {q : V} (hq : 0 ≤ q) : 0 ≤ ejaSqrt q ∧ ejaSqrt q * ejaSqrt q = q := by
  rw [ejaSqrt, dif_pos hq]
  exact (eja_exists_nonneg_sqrt hq).choose_spec

theorem ejaSqrt_unique {q b : V} (hb : 0 ≤ b) (hbb : b * b = q) : ejaSqrt q = b := by
  have hq : 0 ≤ q := by rw [← hbb, eja_nonneg_iff]; exact IsSumSq.mul_self b
  obtain ⟨h0, h1⟩ := ejaSqrt_spec hq
  exact sqrt_unique h0 hb (by rw [h1, hbb])

end Sqrt

/-! ### Ceiling of an idempotent; the filter data at an effect -/

section CeilData

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

theorem ejaCeil_of_least {a p : V} (h : IsLeastIdemAbove a p) : ejaCeil a = p := by
  classical
  have hex : ∃ p, IsLeastIdemAbove a p := ⟨p, h⟩
  rw [ejaCeil, dif_pos hex]
  exact hex.choose_spec.unique h

/-- `⌈a⌉` is always an idempotent (junk value `0` included). -/
theorem ejaCeil_idem (a : V) : ejaCeil a * ejaCeil a = ejaCeil a := by
  classical
  by_cases hex : ∃ p, IsLeastIdemAbove a p
  · rw [ejaCeil_of_least hex.choose_spec]; exact hex.choose_spec.1
  · rw [ejaCeil, dif_neg hex, eja_mul_zero]

theorem ejaFloor_idem (a : V) : ejaFloor a * ejaFloor a = ejaFloor a :=
  eja_one_sub_idem (ejaCeil_idem _)

/-- `⌈p⌉ = p` for an idempotent `p`. -/
theorem ejaCeil_idem_eq {p : V} (hp : p * p = p) : ejaCeil p = p :=
  ejaCeil_of_least ⟨hp, le_rfl, fun _ _ h => h⟩

/-- `⌊p⌋ = p` for an idempotent `p`; hence `{E|p} = E_p` (main.tex, after
EJA 20). -/
theorem ejaFloor_idem_eq {p : V} (hp : p * p = p) : ejaFloor p = p := by
  rw [ejaFloor, ejaCeil_idem_eq (eja_one_sub_idem hp), sub_sub_cancel]

/-- `⌈q⌉ * q = q` for an effect `q`. -/
theorem ejaCeil_mul {q : V} (h0 : 0 ≤ q) (h1 : q ≤ 1) : ejaCeil q * q = q :=
  (idem_le_iff_mul (ejaCeil_idem q) h0 h1).mp (EJAceilfloor h0 h1).2.2.1.2.1

/-- **The filter data at an effect `q`**: with `b = √q` and `c = ⌈q⌉`, there is
`b'` (the pseudo-inverse of `b` in the corner `V₁(c)`) with
`U_b U_b' = U_b' U_b = P₁(c)`, `U_b'` landing in `V₁(c)`, and `U_b c = q`.  The
tree's `eja_exists_filter`, redone so that its support idempotent is `⌈q⌉` and
its square root is `√q`. -/
theorem filter_data {q : V} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∃ b' : V, (∀ x, ejaU (ejaSqrt q) (ejaU b' x) = ejaPone (ejaCeil q) x) ∧
      (∀ x, ejaU b' (ejaU (ejaSqrt q) x) = ejaPone (ejaCeil q) x) ∧
      (∀ x, ejaCeil q * ejaU b' x = ejaU b' x) ∧
      ejaU (ejaSqrt q) (ejaCeil q) = q := by
  classical
  obtain ⟨t, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral q
  have hc : ∀ l ∈ t, 0 ≤ l := by
    refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)).mp ?_
    rw [← hdec]
    exact (eja_nonneg_iff q).mp h0
  set g : ℝ → ℝ := fun l => Real.sqrt l with hgdef
  set g' : ℝ → ℝ := fun l => if l = 0 then 0 else (Real.sqrt l)⁻¹ with hg'def
  set h : ℝ → ℝ := fun l => if l = 0 then 0 else 1 with hhdef
  have hsqrt_ne : ∀ l ∈ t, l ≠ 0 → Real.sqrt l ≠ 0 := by
    intro l hl hl0
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (hc l hl) (Ne.symm hl0)))
  have hgg' : ∀ l ∈ t, g l * g' l = h l := by
    intro l hl
    rw [hgdef, hg'def, hhdef]
    by_cases hl0 : l = 0
    · simp [hl0]
    · simp only [hl0, ite_false]
      exact mul_inv_cancel₀ (hsqrt_ne l hl hl0)
  have hg'g : ∀ l ∈ t, g' l * g l = h l := by
    intro l hl; rw [mul_comm]; exact hgg' l hl
  have hhh : ∀ l : ℝ, h l * h l = h l := by
    intro l; rw [hhdef]; by_cases hl0 : l = 0 <;> simp [hl0]
  have hhg' : ∀ l : ℝ, h l * g' l = g' l := by
    intro l; rw [hhdef, hg'def]; by_cases hl0 : l = 0 <;> simp [hl0]
  have hs : (∑ l ∈ t, h l • e l) * (∑ l ∈ t, h l • e l) = ∑ l ∈ t, h l • e l := by
    rw [eja_ortho_mul hidem horth]
    exact Finset.sum_congr rfl fun l _ => by rw [hhh l]
  -- the support idempotent is the ceiling
  have hceil : ejaCeil q = ∑ l ∈ t, h l • e l := by
    let ι := ↥(t.filter fun l => l ≠ 0)
    have hsumq : q = ∑ i : ι, (i : ℝ) • e i := by
      rw [Finset.sum_coe_sort (t.filter fun l => l ≠ 0) (fun l => l • e l),
        Finset.sum_filter_of_ne (p := fun l : ℝ => l ≠ 0)
          (fun l _ hne h0 => hne (by rw [h0, zero_smul]))]
      exact hdec
    have hmem : ∀ i : ι, (i : ℝ) ∈ t ∧ (i : ℝ) ≠ 0 := fun i => Finset.mem_filter.mp i.2
    rw [(EJAceilfloor h0 h1).2.1 ι (fun i => (i : ℝ)) (fun i => e i)
      (fun i => lt_of_le_of_ne (hc _ (hmem i).1) (Ne.symm (hmem i).2))
      (fun i => hidem _ (hmem i).1)
      (fun i j hij => horth _ (hmem i).1 _ (hmem j).1 (fun h => hij (Subtype.ext h)))
      hsumq]
    rw [Finset.sum_coe_sort (t.filter fun l => l ≠ 0) e, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hhdef]
    by_cases hl0 : l = 0 <;> simp [hl0]
  -- the square root
  have hsqrt : ejaSqrt q = ∑ l ∈ t, g l • e l := by
    refine ejaSqrt_unique ?_ ?_
    · rw [eja_nonneg_iff, eja_ortho_isSumSq_iff hidem horth hne0]
      exact fun l _ => Real.sqrt_nonneg l
    · rw [eja_ortho_mul hidem horth]
      conv_rhs => rw [hdec]
      exact Finset.sum_congr rfl fun l hl => by rw [hgdef, Real.mul_self_sqrt (hc l hl)]
  have hcomp : ∀ (u v : ℝ → ℝ), (∀ l ∈ t, u l * v l = h l) →
      ∀ x : V, ejaU (∑ l ∈ t, u l • e l) (ejaU (∑ l ∈ t, v l • e l) x)
        = ejaPone (∑ l ∈ t, h l • e l) x := by
    intro u v huv x
    rw [eja_U_family_comp' u v hidem horth hsum x]
    have heq : (∑ l ∈ t, (u l * v l) • e l) = ∑ l ∈ t, h l • e l :=
      Finset.sum_congr rfl fun l hl => by rw [huv l hl]
    rw [heq, ejaU_idem hs]
  refine ⟨∑ l ∈ t, g' l • e l, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hsqrt, hceil]; exact hcomp g g' hgg' x
  · intro x; rw [hsqrt, hceil]; exact hcomp g' g hg'g x
  · intro x
    rw [hceil]
    have hx : ejaU (∑ l ∈ t, h l • e l) (ejaU (∑ l ∈ t, g' l • e l) x)
        = ejaU (∑ l ∈ t, g' l • e l) x := by
      rw [eja_U_family_comp' h g' hidem horth hsum x]
      exact congrArg (fun w => ejaU w x)
        (Finset.sum_congr rfl fun l _ => by rw [hhg' l])
    rw [ejaU_idem hs] at hx
    exact (eja_pone_eq_self_iff _ hs _).mp hx
  · rw [hsqrt, hceil]
    have h1' : (∑ l ∈ t, h l • e l) = ejaU (∑ l ∈ t, h l • e l) 1 := by
      rw [ejaU_apply_one, hs]
    rw [h1', eja_U_family_comp' g h hidem horth hsum, ejaU_apply_one,
      eja_ortho_mul hidem horth]
    conv_rhs => rw [hdec]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hgdef, hhdef]
    by_cases hl0 : l = 0
    · simp [hl0]
    · simp only [hl0, ite_false, mul_one]
      rw [Real.mul_self_sqrt (hc l hl)]

end CeilData

/-! ## EJA 14, 16, 18: corners, filters, purity -/

section Defs

/-- **EJA 14** (main.tex:451, Definition): a *corner* for an effect `q ∈ E` is a
positive subunital `π : E → C` with `π(1) = π(q)` that is initial with this
property: every positive subunital `g : E → F` with `g(1) = g(q)` factors as
`g = ḡ ∘ π` for a unique positive subunital `ḡ`.  The paper names the codomain
`{E|q}` before defining it (Def 20); as the text after Note 17 uses it, the
codomain here is arbitrary. -/
def IsCorner {E C : EJAPsu.{u}} (q : E.carrier) (π : E ⟶ C) : Prop :=
  π.toLinearMap 1 = π.toLinearMap q ∧
    ∀ (F : EJAPsu.{u}) (g : E ⟶ F), g.toLinearMap 1 = g.toLinearMap q →
      ∃! gb : C ⟶ F, π ≫ gb = g

/-- **EJA 16** (main.tex:469, Definition): a *filter* for an effect `q ∈ E` is a
positive subunital `ξ : D → E` with `ξ(1) ≤ q` that is final with this
property: every positive subunital `f : F → E` with `f(1) ≤ q` factors as
`f = ξ ∘ f̄` for a unique positive subunital `f̄`.  (Domain arbitrary, as for
EJA 14.) -/
def IsFilter {E D : EJAPsu.{u}} (q : E.carrier) (ξ : D ⟶ E) : Prop :=
  ξ.toLinearMap 1 ≤ q ∧
    ∀ (F : EJAPsu.{u}) (f : F ⟶ E), f.toLinearMap 1 ≤ q →
      ∃! fb : F ⟶ D, fb ≫ ξ = f

/-- **EJA 18** (`def:purity`, main.tex:484, Definition): a positive subunital
`f : E → F` is *pure* when `f = ξ ∘ π` for some corner `π` (for an effect of
`E`) and some filter `ξ` (for an effect of `F`), not necessarily for the same
effect. -/
def IsPure {E F : EJAPsu.{u}} (f : E ⟶ F) : Prop :=
  ∃ (C : EJAPsu.{u}) (q : E.carrier) (q' : F.carrier) (π : E ⟶ C) (ξ : C ⟶ F),
    (0 ≤ q ∧ q ≤ 1) ∧ (0 ≤ q' ∧ q' ≤ 1) ∧ IsCorner q π ∧ IsFilter q' ξ ∧ f = π ≫ ξ

end Defs

/-! ## EJA 19–20: the Peirce `1`-space and the objects `{E|q}`, `E_q` -/

section Peirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- **EJA 19** (`prop:peircedecomp`, main.tex:490, Proposition; Alfsen–Shultz
1.43): for an idempotent `p`, `E₁(p) := Q_p(E)` consists exactly of the
elements fixed by `Q_p`, which are those with `p * y = y`.  That this is a
sub-EJA is the tree's `EJACorner` (`peirce_subEJA`). -/
theorem peircedecomp {p : V} (hp : p * p = p) (y : V) :
    (y ∈ LinearMap.range (ejaU p) ↔ ejaU p y = y) ∧ (ejaU p y = y ↔ p * y = y) := by
  refine ⟨⟨?_, fun h => ⟨y, h⟩⟩, ?_⟩
  · rintro ⟨x, rfl⟩
    exact congrArg (fun f : V →ₗ[ℝ] V => f x) (idem_Q_idem hp)
  · rw [ejaU_idem hp]; exact eja_pone_eq_self_iff p hp y

/-- **EJA 19**, second half: `E₁(p)` is a Euclidean Jordan algebra with unit
`p` (the tree's instance on `EJACorner`). -/
theorem peirce_subEJA (p : EJAIdem V) : EuclideanJordanAlgebra (EJACorner p) :=
  inferInstance

/-- The floor of an element, bundled as an idempotent. -/
noncomputable def floorIdem (q : V) : EJAIdem V := ⟨ejaFloor q, ejaFloor_idem q⟩

/-- The ceiling of an element, bundled as an idempotent. -/
noncomputable def ceilIdem (q : V) : EJAIdem V := ⟨ejaCeil q, ejaCeil_idem q⟩

/-- **EJA 20** (main.tex:496, Definition): `E_q := E₁(⌊qᗮ⌋ᗮ) = E₁(⌈q⌉)` — the
identity `⌊qᗮ⌋ᗮ = ⌈q⌉`. -/
theorem floor_perp_perp (q : V) : 1 - ejaFloor (1 - q) = ejaCeil q := by
  rw [ejaFloor, sub_sub_cancel, sub_sub_cancel]

/-- `⌊q⌋ * q = ⌊q⌋` for an effect `q`. -/
theorem ejaFloor_mul {q : V} (h0 : 0 ≤ q) (h1 : q ≤ 1) : ejaFloor q * q = ejaFloor q := by
  have hb0 : (0 : V) ≤ 1 - q := eja_sub_nonneg.mpr h1
  have hb1 : 1 - q ≤ 1 := by rw [← eja_sub_nonneg, sub_sub_cancel]; exact h0
  have h := ejaCeil_mul hb0 hb1
  have he : ejaCeil (1 - q) = 1 - ejaFloor q := by rw [ejaFloor, sub_sub_cancel]
  rw [he, eja_sub_mul, eja_one_mul, eja_mul_sub, eja_mul_one] at h
  have : ejaFloor q * q = ejaFloor q := by
    have h' : (1 : V) - q - (ejaFloor q - ejaFloor q * q) = 1 - q := h
    have h'' : ejaFloor q - ejaFloor q * q = 0 := by
      have := congrArg (fun x => 1 - q - x) h'
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    exact (sub_eq_zero.mp h'').symm
  exact this

end Peirce

/-- **EJA 20**: the object `{E|q} := E₁(⌊q⌋)` of the standard corner. -/
noncomputable abbrev cornerObj (E : EJAPsu.{u}) (q : E.carrier) : EJAPsu.{u} :=
  EJAPsu.of (EJACorner (floorIdem q))

/-- **EJA 20**: the object `E_q := E₁(⌈q⌉)` of the standard filter. -/
noncomputable abbrev filterObj (E : EJAPsu.{u}) (q : E.carrier) : EJAPsu.{u} :=
  EJAPsu.of (EJACorner (ceilIdem q))

/-! ## EJA 21–23 -/

section Factor

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

theorem real_eq_zero_of_forall {c d : ℝ} (h : ∀ t : ℝ, 0 ≤ t * c + d) : c = 0 := by
  by_contra hc
  have h1 := h (-(d + 1) / c)
  rw [div_mul_cancel₀ _ hc] at h1
  linarith

/-- **EJA 21** (main.tex:505, Lemma): if `ω : E → ℝ` is positive linear and
`ω(p) = ω(1)` for an idempotent `p`, then `ω(Q_p a) = ω(a)` for all `a`.  The
paper's proof: `⟨a, b⟩_ω := ω(a * b)` is positive semi-definite, so
Cauchy–Schwarz with `ω(pᗮ * pᗮ) = ω(pᗮ) = 0` gives `ω(pᗮ * a) = 0`. -/
theorem omega_Q (ω : V →ₗ[ℝ] ℝ) (hω : ∀ a : V, 0 ≤ a → 0 ≤ ω a) {p : V}
    (hp : p * p = p) (h : ω p = ω 1) (a : V) : ω (ejaU p a) = ω a := by
  set r : V := 1 - p with hr
  have hrr : r * r = r := eja_one_sub_idem hp
  have hωr : ω r = 0 := by rw [hr, map_sub, h, sub_self]
  have hmul : ∀ x : V, ω (r * x) = 0 := by
    intro x
    have hexp : ∀ t : ℝ, (t • r + x) * (t • r + x)
        = (t * t) • (r * r) + (2 * t) • (r * x) + x * x := by
      intro t
      rw [eja_add_mul_add]
      simp only [eja_smul_mul, eja_mul_smul, smul_smul]
      rw [eja_mul_comm x r]
      module
    have hpos : ∀ t : ℝ, 0 ≤ t * (2 * ω (r * x)) + ω (x * x) := by
      intro t
      have h1 := hω _ ((eja_nonneg_iff _).mpr (IsSumSq.mul_self (t • r + x)))
      rw [hexp t, map_add, map_add, map_smul, map_smul, hrr, hωr, smul_zero, zero_add,
        smul_eq_mul] at h1
      linarith
    have := real_eq_zero_of_forall hpos
    linarith
  have hpx : ∀ x : V, ω (p * x) = ω x := by
    intro x
    have h1 := hmul x
    rw [hr, eja_sub_mul, eja_one_mul, map_sub, sub_eq_zero] at h1
    exact h1.symm
  rw [ejaU_apply, map_sub, map_smul, hpx, hpx, hp, hpx, smul_eq_mul]
  ring

/-- **EJA 22** (`cor:factorimage`, main.tex:521, Corollary): if `g : E → W` is
positive linear with `g(p) = g(1)` for an idempotent `p`, then
`g(Q_p a) = g(a)`: EJA 21 applied to the states of `W`, which separate its
points (tree `eja_exists_state_ne_zero`). -/
theorem factorimage {W : Type u} [AddCommGroup W] [Module ℝ W] [Mul W] [One W]
    [PartialOrder W] [EuclideanJordanAlgebra W] (g : V →ₗ[ℝ] W) (hg : IsPositiveMap g)
    {p : V} (hp : p * p = p) (h : g p = g 1) (a : V) : g (ejaU p a) = g a := by
  by_contra hne
  have hx : g (ejaU p a) - g a ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨f, hfpos, _, hfne⟩ := eja_exists_state_ne_zero hx
  have h1 := omega_Q (f.comp g) (fun x hx => hfpos _ (hg x hx)) hp
    (by simp only [LinearMap.comp_apply, h]) a
  apply hfne
  simp only [LinearMap.comp_apply] at h1
  rw [map_sub, h1, sub_self]

/-- **EJA 23** (`lem:EJAfloor1`, main.tex:529, Lemma): if `g : E → F` is
positive linear with `g(q) = g(1)` for an effect `q`, then `g(⌊q⌋) = g(1)`.
The paper's proof: decompose `qᗮ = ∑ λᵢ pᵢ` with `λᵢ > 0` (EJA 13); `g` kills
each `pᵢ`, hence `⌈qᗮ⌉ = ∑ pᵢ`. -/
theorem floor_one {W : Type u} [AddCommGroup W] [Module ℝ W] [Mul W] [One W]
    [PartialOrder W] [EuclideanJordanAlgebra W] (g : V →ₗ[ℝ] W) (hg : IsPositiveMap g)
    {q : V} (h0 : 0 ≤ q) (h1 : q ≤ 1) (h : g q = g 1) : g (ejaFloor q) = g 1 := by
  classical
  have hb0 : (0 : V) ≤ 1 - q := eja_sub_nonneg.mpr h1
  have hb1 : 1 - q ≤ 1 := by rw [← eja_sub_nonneg, sub_sub_cancel]; exact h0
  have hgr : g (1 - q) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨⟨ι, _, lam, p, hpos, hat, horth, hdec⟩, hceil, _, _⟩ := EJAceilfloor hb0 hb1
  have hidem : ∀ i, p i * p i = p i := fun i => (hat i).1
  have hterm : ∀ j, 0 ≤ lam j • p j := fun j => (eja_nonneg_iff _).mpr
    (eja_isSumSq_smul (hpos j).le ((eja_nonneg_iff _).mp (eja_idem_nonneg (hidem j))))
  have hgp : ∀ i, g (p i) = 0 := by
    intro i
    have hle : 0 ≤ (1 - q) - lam i • p i := by
      rw [hdec, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
      exact eja_sum_nonneg fun j _ => hterm j
    have ha := hg _ hle
    rw [map_sub, hgr, zero_sub] at ha
    have hb := hg _ (hterm i)
    have hz : g (lam i • p i) = 0 := by
      refine le_antisymm ?_ hb
      rw [eja_nonneg_iff] at ha
      rw [eja_le_iff, zero_sub]
      exact ha
    rw [map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left (hpos i).ne'
  rw [ejaFloor, hceil ι lam p hpos hidem horth hdec, map_sub, map_sum,
    Finset.sum_eq_zero fun i _ => hgp i, sub_zero]

end Factor

/-! ## EJA 24: the standard corner -/

section StdCorner

variable (E : EJAPsu.{u})

/-- **EJA 24**, the map: the *standard corner* `π_q = r ∘ Q_{⌊q⌋} : E → {E|q}`,
the compression by `⌊q⌋` corestricted to its Peirce `1`-space (the paper's
orthogonal projection `r` is the identity on the range of `Q_{⌊q⌋}`, EJA 19;
tree `ejaPoneCorner`). -/
noncomputable def stdCorner (q : E.carrier) : E ⟶ cornerObj E q where
  toLinearMap := ejaPoneCorner (floorIdem q)
  map_nonneg' _ hx := eja_pone_nonneg_corner _ hx
  map_subunital' := le_of_eq (EJACorner.val_injective (by
    rw [ejaPoneCorner_val, eja_pone_one _ (floorIdem q).idem]; rfl))

@[simp] theorem stdCorner_val (q x : E.carrier) :
    EJACorner.val ((stdCorner E q).toLinearMap x) = ejaPone (ejaFloor q) x := rfl

/-- **EJA 24** (`eja:quot`, main.tex:538, Proposition): the standard corner
`π_q` is a corner for the effect `q`.  The paper's proof: `ḡ` is the
restriction of `g` to `E₁(⌊q⌋)`, using EJA 23 and EJA 22. -/
theorem stdCorner_isCorner {q : E.carrier} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsCorner q (stdCorner E q) := by
  have hfl : ejaFloor q * ejaFloor q = ejaFloor q := ejaFloor_idem q
  have hflq : ejaFloor q * q = ejaFloor q := ejaFloor_mul h0 h1
  refine ⟨EJACorner.val_injective ?_, fun F g hg => ?_⟩
  · rw [stdCorner_val, stdCorner_val, eja_pone_one _ hfl, ejaPone_apply, hflq, hfl]
    module
  have hgpos : IsPositiveMap g.toLinearMap := g.map_nonneg'
  have hgfl : g.toLinearMap (ejaFloor q) = g.toLinearMap 1 :=
    floor_one g.toLinearMap hgpos h0 h1 hg.symm
  let gb : cornerObj E q ⟶ F :=
    { toLinearMap := g.toLinearMap.comp (EJACorner.valLin (floorIdem q))
      map_nonneg' := fun y hy => g.map_nonneg' _ (eja_corner_val_nonneg hy)
      map_subunital' := by
        show g.toLinearMap (ejaFloor q) ≤ 1
        rw [hgfl]; exact g.map_subunital' }
  have hfac : stdCorner E q ≫ gb = g := by
    refine ejapsu_hom_ext fun x => ?_
    rw [ejapsu_comp_apply]
    show g.toLinearMap (ejaPone (ejaFloor q) x) = g.toLinearMap x
    rw [← ejaU_idem hfl]
    exact factorimage g.toLinearMap hgpos hfl hgfl x
  refine ⟨gb, hfac, fun k hk => ejapsu_hom_ext fun y => ?_⟩
  have hy : (stdCorner E q).toLinearMap (EJACorner.val y) = y :=
    EJACorner.val_injective (by
      rw [stdCorner_val]
      exact (eja_pone_eq_self_iff _ hfl _).mpr (EJACorner.val_prop y))
  have h2 := congrArg (fun m : E ⟶ F => m.toLinearMap (EJACorner.val y)) (hk.trans hfac.symm)
  simp only [ejapsu_comp_apply, hy] at h2
  exact h2

end StdCorner

/-! ## EJA 25: the standard filter -/

section StdFilter

variable (E : EJAPsu.{u})

/-- **EJA 25**, the map: the *standard filter* `ξ_q = Q_{√q} ∘ ι : E_q → E`,
`ι` the inclusion of `E_q = E₁(⌈q⌉)`. -/
noncomputable def stdFilter {q : E.carrier} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    filterObj E q ⟶ E where
  toLinearMap := (ejaU (ejaSqrt q)).comp (EJACorner.valLin (ceilIdem q))
  map_nonneg' _ hy := eja_U_nonneg' _ (eja_corner_val_nonneg hy)
  map_subunital' := by
    obtain ⟨_, _, _, _, hq⟩ := filter_data h0 h1
    show ejaU (ejaSqrt q) (ejaCeil q) ≤ 1
    rw [hq]; exact h1

theorem stdFilter_apply {q : E.carrier} (h0 : 0 ≤ q) (h1 : q ≤ 1) (y : filterObj E q) :
    (stdFilter E h0 h1).toLinearMap y = ejaU (ejaSqrt q) (EJACorner.val y) := rfl

/-- **EJA 25** (`eja:filter`, main.tex:565, Proposition): the standard filter
`ξ_q` is a filter for the effect `q`, with `ξ_q(1) = q`.  The paper's proof:
every `f` with `f(1) ≤ q` has range in `E₁(⌈q⌉)`, and `f̄ = Q_{√(q⁻¹)} ∘ f`
with the pseudo-inverse `q⁻¹` (`filter_data`). -/
theorem stdFilter_isFilter {q : E.carrier} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (stdFilter E h0 h1).toLinearMap 1 = q ∧ IsFilter q (stdFilter E h0 h1) := by
  obtain ⟨b', hUU', hU'U, hmem, hq⟩ := filter_data h0 h1
  set c := ejaCeil q with hc
  have hcc : c * c = c := ejaCeil_idem q
  have hcq : c * q = q := ejaCeil_mul h0 h1
  have hone : (stdFilter E h0 h1).toLinearMap 1 = q := hq
  refine ⟨hone, le_of_eq hone, fun F f hf => ?_⟩
  -- the range of `f` lies in the corner `E₁(⌈q⌉)`
  have hnn : ∀ y : F.carrier, 0 ≤ y → c * f.toLinearMap y = f.toLinearMap y := by
    intro y hy
    obtain ⟨n, _, hn⟩ := chu_strong_unit y
    have hle : f.toLinearMap y ≤ (n : ℝ) • q := by
      have h2 := f.mono hn
      rw [map_smul] at h2
      refine le_trans h2 ?_
      rw [← eja_sub_nonneg, ← smul_sub, eja_nonneg_iff]
      exact eja_isSumSq_smul (Nat.cast_nonneg n) ((eja_nonneg_iff _).mp (eja_sub_nonneg.mpr hf))
    exact eja_corner_of_le_smul hcc hcq (f.map_nonneg' y hy) hle
  have hrange : ∀ x : F.carrier, c * f.toLinearMap x = f.toLinearMap x := by
    intro x
    obtain ⟨n, hn, _⟩ := chu_strong_unit x
    have hpos : 0 ≤ x + (n : ℝ) • (1 : F.carrier) := by
      rw [← eja_sub_nonneg] at hn
      convert hn using 1; abel
    have hone' : (0 : F.carrier) ≤ (n : ℝ) • 1 := by
      rw [eja_nonneg_iff]; exact eja_isSumSq_smul_one (Nat.cast_nonneg n)
    have hx : x = (x + (n : ℝ) • (1 : F.carrier)) - (n : ℝ) • 1 := by abel
    rw [hx, map_sub, eja_mul_sub, hnn _ hpos, hnn _ hone']
  let fbl : F.carrier →ₗ[ℝ] EJACorner (ceilIdem q) :=
    { toFun := fun x => EJACorner.mk' (ejaU b' (f.toLinearMap x)) (hmem _)
      map_add' := fun x y => EJACorner.val_injective (by
        change ejaU b' (f.toLinearMap (x + y))
          = ejaU b' (f.toLinearMap x) + ejaU b' (f.toLinearMap y)
        rw [map_add, map_add])
      map_smul' := fun r x => EJACorner.val_injective (by
        change ejaU b' (f.toLinearMap (r • x)) = r • ejaU b' (f.toLinearMap x)
        rw [map_smul, map_smul]) }
  have hfbl : ∀ x, EJACorner.val (fbl x) = ejaU b' (f.toLinearMap x) := fun _ => rfl
  let fb : F ⟶ filterObj E q :=
    { toLinearMap := fbl
      map_nonneg' := fun x hx => (eja_corner_nonneg_iff _ _).mpr (by
        rw [hfbl]; exact eja_U_nonneg' _ (f.map_nonneg' x hx))
      map_subunital' := by
        rw [EJACorner.le_iff', ← eja_nonneg_iff]
        refine (eja_corner_nonneg_iff _ _).mpr ?_
        rw [EJACorner.val_sub, hfbl, EJACorner.val_one, eja_sub_nonneg]
        have h2 := eja_U_mono b' hf
        have h3 : ejaU b' q = c := by
          rw [← hq, hU'U]
          exact (eja_pone_eq_self_iff _ hcc _).mpr hcc
        rw [h3] at h2
        exact h2 }
  have hfac : fb ≫ stdFilter E h0 h1 = f := by
    refine ejapsu_hom_ext fun x => ?_
    rw [ejapsu_comp_apply, stdFilter_apply]
    show ejaU (ejaSqrt q) (ejaU b' (f.toLinearMap x)) = f.toLinearMap x
    rw [hUU']
    exact (eja_pone_eq_self_iff _ hcc _).mpr (hrange x)
  refine ⟨fb, hfac, fun k hk => ejapsu_hom_ext fun x => EJACorner.val_injective ?_⟩
  have h2 := congrArg (fun m : F ⟶ E => m.toLinearMap x) hk
  simp only [ejapsu_comp_apply] at h2
  show EJACorner.val (k.toLinearMap x) = ejaU b' (f.toLinearMap x)
  rw [← h2, stdFilter_apply, hU'U]
  have hv : ejaCeil q * EJACorner.val (k.toLinearMap x) = EJACorner.val (k.toLinearMap x) :=
    EJACorner.val_prop (p := ceilIdem q) (k.toLinearMap x)
  exact ((eja_pone_eq_self_iff _ hcc _).mpr hv).symm

end StdFilter

end Papers.EJA
