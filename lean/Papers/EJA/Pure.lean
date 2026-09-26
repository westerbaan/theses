import Papers.EJA.FilterCorner
import Papers.EJA.Fundamental

/-!
# EJA §3.1 and §4: polar decomposition, pure maps compose, ⋄-adjointness,
# Jordan isomorphisms, Lemma 38 (points 26–39)

A. Westerbaan, B. Westerbaan, J. van de Wetering, *Pure Maps between Euclidean
Jordan Algebras*, QPL 2018, `../papers/1805.11496/main.tex`.  Over the tree's
(finite-dimensional) Euclidean Jordan algebras; see `Papers/EJA/PLAN.md` §0, §2, §6.

Contents.
* Frames: finite orthogonal families of idempotents summing to `1`, and the
  calculus of `Q` on their span (`frame_U_comp`, reindexing the tree's
  `eja_U_family_comp'`) — the "one associative subalgebra" facts the paper
  uses silently.
* EJA 35–37: order-sharp = idempotent; a unital order isomorphism is a Jordan
  isomorphism; `Θ ∘ Q_a = Q_{Θ a} ∘ Θ`.
* EJA 28–29: the image of a positive map; it exists and is an idempotent.
* EJA 32–33: `f^⋄`, `f_⋄`, ⋄-adjointness, ⋄-self-adjointness, ⋄-positivity; the
  zero-pattern criterion; self-adjoint maps and `Q_a` are ⋄-self-adjoint.
* EJA 38: **false as printed** (`eja38_false_as_printed`, on `ℝ ⊕ ℝ`), and the
  repaired Lemma 38′ (`eja38'`): `Θ(√f(1))` operator-commutes with `√f(1)`
  (indeed both are diagonal in one Jordan frame) and `Θ ∘ Θ = id`.
* EJA 39 and 34, with the ⋄-self-adjoint root assumed pure (the hypothesis the
  printed proofs use; PLAN §2, "B15 recurs"), proved from 38′.
* EJA 26–27: adjoints, partial isometries, the polar decomposition (with the
  fundamental formula `ejaU_ejaU` of `Fundamental.lean`); supports `⌈x⌉` of
  positive elements.
* EJA 30–31: `π ∘ ξ` is pure; corners compose, filters compose, pure maps
  compose.
-/

namespace Papers.EJA

open Theses.B.Eff Theses.B.Eff.EuclideanJordanAlgebra CategoryTheory

universe u

/-! ## Frames -/

section Frames

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- A finite family of pairwise orthogonal idempotents summing to `1`. -/
structure IsOrthFrame {ι : Type*} [Fintype ι] (p : ι → V) : Prop where
  idem : ∀ i, p i * p i = p i
  orth : ∀ i j, i ≠ j → p i * p j = 0
  sum_one : ∑ i, p i = 1

variable {ι : Type*} [Fintype ι] {p : ι → V}

theorem frame_mul (hp : IsOrthFrame p) (c d : ι → ℝ) :
    (∑ i, c i • p i) * (∑ i, d i • p i) = ∑ i, (c i * d i) • p i := by
  rw [eja_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eja_mul_smul, sum_idem_of_orth hp.idem hp.orth c j, smul_smul, mul_comm]

theorem frame_mul_elt (hp : IsOrthFrame p) (c : ι → ℝ) (j : ι) :
    (∑ i, c i • p i) * p j = c j • p j := sum_idem_of_orth hp.idem hp.orth c j

theorem frame_one (hp : IsOrthFrame p) : ∑ i, (1 : ℝ) • p i = 1 := by
  simp only [one_smul]; exact hp.sum_one

theorem frame_U_elt (hp : IsOrthFrame p) (c : ι → ℝ) (j : ι) :
    ejaU (∑ i, c i • p i) (p j) = (c j * c j) • p j := by
  rw [ejaU_apply, frame_mul_elt hp, eja_mul_smul, frame_mul_elt hp, frame_mul hp,
    frame_mul_elt hp, smul_smul]
  module

theorem frame_nonneg (hp : IsOrthFrame p) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    0 ≤ ∑ i, c i • p i :=
  eja_sum_nonneg fun i _ => (eja_nonneg_iff _).mpr
    (eja_isSumSq_smul (hc i) ((eja_nonneg_iff _).mp (eja_idem_nonneg (hp.idem i))))

/-- Reading a coefficient off a frame combination. -/
theorem frame_coeff (hp : IsOrthFrame p) {c d : ι → ℝ}
    (h : ∑ i, c i • p i = ∑ i, d i • p i) (j : ι) (hj : p j ≠ 0) : c j = d j := by
  have h1 := congrArg (fun x => x * p j) h
  simp only [frame_mul_elt hp] at h1
  have h2 : (c j - d j) • p j = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 hj

/-- **`Q` on the span of a frame is multiplicative**: `Q_a Q_b = Q_{ab}` for
`a, b` combinations of one frame (the tree's `eja_U_family_comp'`, reindexed
from `Finset ℝ` to an arbitrary finite index type). -/
theorem frame_U_comp (hp : IsOrthFrame p) (c d : ι → ℝ) (y : V) :
    ejaU (∑ i, c i • p i) (ejaU (∑ i, d i • p i) y) = ejaU (∑ i, (c i * d i) • p i) y := by
  classical
  set eqv := Fintype.equivFin ι
  let idx : ι → ℝ := fun i => ((eqv i : ℕ) : ℝ)
  have hinj : Function.Injective idx := by
    intro i j h
    have h' : ((eqv i : ℕ) : ℝ) = ((eqv j : ℕ) : ℝ) := h
    have : (eqv i : ℕ) = eqv j := by exact_mod_cast h'
    exact eqv.injective (Fin.ext this)
  let lift : ∀ {α : Type u} [AddCommMonoid α], (ι → α) → ℝ → α :=
    fun f l => ∑ i, if idx i = l then f i else 0
  have hlift : ∀ {α : Type u} [AddCommMonoid α] (f : ι → α) (j : ι), lift f (idx j) = f j := by
    intro α _ f j
    show (∑ i, if idx i = idx j then f i else 0) = f j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hinj.ne hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  let liftR : (ι → ℝ) → ℝ → ℝ := fun f l => ∑ i, if idx i = l then f i else 0
  have hliftR : ∀ (f : ι → ℝ) (j : ι), liftR f (idx j) = f j := by
    intro f j
    show (∑ i, if idx i = idx j then f i else 0) = f j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hinj.ne hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  set s : Finset ℝ := Finset.univ.image idx
  set e : ℝ → V := lift p
  have he : ∀ j, e (idx j) = p j := fun j => hlift p j
  have hsum : ∀ g : ℝ → ℝ, ∑ l ∈ s, g l • e l = ∑ i, g (idx i) • p i := by
    intro g
    rw [Finset.sum_image (fun i _ j _ h => hinj h)]
    exact Finset.sum_congr rfl fun i _ => by rw [he]
  have hmem : ∀ l ∈ s, ∃ i, idx i = l := fun l hl => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hl; exact ⟨i, hi⟩
  have hidem : ∀ l ∈ s, e l * e l = e l := by
    intro l hl; obtain ⟨i, rfl⟩ := hmem l hl; rw [he]; exact hp.idem i
  have horth : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → e l * e k = 0 := by
    intro l hl k hk hlk
    obtain ⟨i, rfl⟩ := hmem l hl; obtain ⟨j, rfl⟩ := hmem k hk
    rw [he, he]; exact hp.orth i j (fun h => hlk (by rw [h]))
  have hone : ∑ l ∈ s, e l = 1 := by
    have := hsum (fun _ => 1); simp only [one_smul] at this; rw [this, hp.sum_one]
  have key := eja_U_family_comp' (liftR c) (liftR d) hidem horth hone y
  rw [hsum, hsum, hsum] at key
  simp only [hliftR] at key
  exact key

/-- Elements of the span of one frame operator-commute. -/
theorem frame_commute (hp : IsOrthFrame p) (c d : ι → ℝ) (x : V) :
    (∑ i, c i • p i) * ((∑ i, d i • p i) * x) = (∑ i, d i • p i) * ((∑ i, c i • p i) * x) := by
  have hc : ∀ i j, p i * (p j * x) = p j * (p i * x) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact eja_commute_of_peirce_zero (hp.idem i) (hp.orth i j hij) x
  simp only [eja_sum_mul, eja_mul_sum, eja_smul_mul, eja_mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hc, mul_comm]

/-- `Q` of a frame combination with non-zero coefficients is injective. -/
theorem frame_U_injective (hp : IsOrthFrame p) {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) :
    Function.Injective (ejaU (∑ i, c i • p i)) := by
  intro x y h
  have key : ∀ z, ejaU (∑ i, (c i)⁻¹ • p i) (ejaU (∑ i, c i • p i) z) = z := by
    intro z
    rw [frame_U_comp hp]
    have : ∑ i, ((c i)⁻¹ * c i) • p i = 1 := by
      simp only [inv_mul_cancel₀ (hc _), one_smul]; exact hp.sum_one
    rw [this, ejaU_one]; rfl
  rw [← key x, h, key y]

/-- `⟨Q_c w, w⟩ ≥ 0` for every `w` when `c` is a non-negative frame
combination: `Q_c = Q_e²` with `e = √c` on the frame. -/
theorem frame_U_psd (hp : IsOrthFrame p) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (w : V) :
    0 ≤ ejaB (ejaU (∑ i, c i • p i) w) w := by
  have h : ejaU (∑ i, c i • p i) w
      = ejaU (∑ i, Real.sqrt (c i) • p i) (ejaU (∑ i, Real.sqrt (c i) • p i) w) := by
    rw [frame_U_comp hp]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by rw [Real.mul_self_sqrt (hc i)]
  rw [h, ← ejaB_U_self_adj]
  rw [ejaB_symm]
  exact ejaB_self_nonneg _

end Frames

/-! ## Elementary facts about idempotents and positive elements -/

section Elem

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- For `x ≥ 0` and an idempotent `t`: `t * x = 0 ⟺ ⟨x, t⟩ = 0` (trace form). -/
theorem idem_mul_eq_zero_iff_ejaB {x t : V} (hx : 0 ≤ x) (ht : t * t = t) :
    t * x = 0 ↔ ejaB x t = 0 := by
  constructor
  · intro h
    show ejaTrL (x * t) = 0
    rw [eja_mul_comm, h, map_zero]
  · intro h
    exact eja_idem_mul_nonneg_eq_zero ht hx (by rw [ejaB_symm]; exact h)

/-- For an effect `a` and an idempotent `e`: `a ≤ e ⟺ (1 - e) * a = 0`. -/
theorem le_idem_iff_mul_one_sub {a e : V} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (he : e * e = e) :
    a ≤ e ↔ (1 - e) * a = 0 := by
  rw [idem_le_iff_mul he ha0 ha1, eja_sub_mul, eja_one_mul, sub_eq_zero, eq_comm]

/-- For idempotents: `s * e = s ⟺ s ≤ e`. -/
theorem idem_le_idem_iff {s e : V} (hs : s * s = s) (he : e * e = e) :
    s ≤ e ↔ e * s = s :=
  idem_le_iff_mul he (eja_idem_nonneg hs) (eja_idem_le_one hs)

/-- A positive element annihilated by `1 - v`, `v` primitive, is a multiple of
`v`. -/
theorem line_of_perp {x v : V} (hv : EJAPrimitive v) (h : (1 - v) * x = 0) :
    ∃ μ : ℝ, x = μ • v := by
  have h1 : v * x = x := by
    rw [eja_sub_mul, eja_one_mul, sub_eq_zero] at h; exact h.symm
  exact hv.line x h1

/-- Two non-zero idempotents on one line are equal. -/
theorem idem_eq_of_smul {u v : V} (hu : u * u = u) (hv : v * v = v) (hu0 : u ≠ 0) {r : ℝ}
    (h : u = r • v) : u = v := by
  have hv0 : v ≠ 0 := by rintro rfl; rw [smul_zero] at h; exact hu0 h
  have h1 : (r * r - r) • v = 0 := by
    have := hu
    rw [h, eja_smul_mul, eja_mul_smul, hv, smul_smul] at this
    rw [sub_smul, this, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · have : r = 0 ∨ r = 1 := by
      have : r * (r - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (by linarith)
    rcases this with h3 | h3
    · rw [h3, zero_smul] at h; exact absurd h hu0
    · rw [h3, one_smul] at h; exact h
  · exact absurd h2 hv0

/-- The coefficient of a positive multiple of a non-zero idempotent is
non-negative. -/
theorem smul_idem_nonneg_coeff {v : V} (hv : v * v = v) (hv0 : v ≠ 0) {μ : ℝ}
    (h : 0 ≤ μ • v) : 0 ≤ μ := by
  have h1 := eja_isSumSq_ejaB_idem_nonneg ((eja_nonneg_iff _).mp h) v hv
  rw [ejaB_smul_left] at h1
  exact nonneg_of_mul_nonneg_left h1 (ejaB_self_pos hv0)

/-- Two positive elements with the same zero pattern against idempotents have
the same zero pattern against positive elements (spectral theorem). -/
theorem zero_pattern_extend {x y : V} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ w : V, w * w = w → (ejaB x w = 0 ↔ ejaB y w = 0)) {z : V} (hz : 0 ≤ z) :
    ejaB x z = 0 ↔ ejaB y z = 0 := by
  classical
  obtain ⟨s, e, hidem, horth, hne0, _, hdec⟩ := eja_spectral z
  have hl : ∀ l ∈ s, 0 ≤ l := by
    refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)).mp ?_
    rw [← hdec]; exact (eja_nonneg_iff z).mp hz
  have hexp : ∀ a : V, 0 ≤ a → (ejaB a z = 0 ↔ ∀ l ∈ s, l = 0 ∨ ejaB a (e l) = 0) := by
    intro a ha
    have hterm : ∀ l ∈ s, 0 ≤ l * ejaB a (e l) := fun l hl' =>
      mul_nonneg (hl l hl') (eja_isSumSq_ejaB_idem_nonneg ((eja_nonneg_iff _).mp ha) _
        (hidem l hl'))
    have hsum : ejaB a z = ∑ l ∈ s, l * ejaB a (e l) := by
      rw [hdec, ejaB_sum_right]
      exact Finset.sum_congr rfl fun l _ => ejaB_smul_right _ _ _
    rw [hsum, Finset.sum_eq_zero_iff_of_nonneg hterm]
    exact forall₂_congr fun l _ => mul_eq_zero
  rw [hexp x hx, hexp y hy]
  exact forall₂_congr fun l hl' => or_congr Iff.rfl (h (e l) (hidem l hl'))

end Elem

/-! ## EJA 35–37: order-sharp elements and Jordan isomorphisms -/

section Jordan

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]
variable {W : Type u} [AddCommGroup W] [Module ℝ W] [Mul W] [One W]
  [PartialOrder W] [EuclideanJordanAlgebra W]

/-- An effect `p` is **order-sharp** when `q = 0` whenever `0 ≤ q`, `q ≤ p` and
`q ≤ pᗮ` (EJA 35; `q` ranges over positive elements — over *all* elements the
condition fails for `q = -1`). -/
def IsOrderSharp (p : V) : Prop :=
  ∀ q : V, 0 ≤ q → q ≤ p → q ≤ 1 - p → q = 0

/-- **EJA 35** (`ordersharpprop`, main.tex:782, Lemma): an effect is order-sharp
iff it is an idempotent.  The paper's proof: spectrally, `rᵢ pᵢ ≤ a, aᗮ` with
`rᵢ = min(λᵢ, 1 - λᵢ)`; conversely `q ≤ p` gives `q = Q_p q ≤ Q_p pᗮ = 0`. -/
theorem ordersharpprop {p : V} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsOrderSharp p ↔ p * p = p := by
  classical
  constructor
  · intro hs
    obtain ⟨s, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral p
    have hl0 : ∀ l ∈ s, 0 ≤ l := by
      refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)).mp ?_
      rw [← hdec]; exact (eja_nonneg_iff p).mp hp0
    have h1p : 1 - p = ∑ l ∈ s, (1 - l) • e l := by
      conv_lhs => rw [← hsum, hdec]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [sub_smul, one_smul]
    have hl1 : ∀ l ∈ s, 0 ≤ 1 - l := by
      refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => 1 - r)).mp ?_
      rw [← h1p]; exact (eja_nonneg_iff _).mp (eja_sub_nonneg.mpr hp1)
    -- a single spectral term below a combination with larger coefficients
    have hterm : ∀ (c : ℝ → ℝ), (∀ l ∈ s, 0 ≤ c l) → ∀ k ∈ s, ∀ r : ℝ, 0 ≤ r → r ≤ c k →
        r • e k ≤ ∑ l ∈ s, c l • e l := by
      intro c hc k hk r hr hrk
      rw [← eja_sub_nonneg, eja_nonneg_iff]
      have : (∑ l ∈ s, c l • e l) - r • e k
          = ∑ l ∈ s, (c l - if l = k then r else 0) • e l := by
        rw [Finset.sum_congr rfl (fun l _ => sub_smul (c l) _ (e l)), Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_eq_single k]
        · simp
        · intro l _ hlk; simp [hlk]
        · intro h; exact absurd hk h
      rw [this, eja_ortho_isSumSq_iff hidem horth hne0]
      intro l hl
      by_cases hlk : l = k
      · subst hlk; simp; linarith
      · simp [hlk]; exact hc l hl
    have hl01 : ∀ l ∈ s, l = 0 ∨ l = 1 := by
      intro l hl
      obtain ⟨r, hr⟩ : ∃ r, r = min l (1 - l) := ⟨_, rfl⟩
      have hr0 : 0 ≤ r := hr ▸ le_min (hl0 l hl) (hl1 l hl)
      have hq := hs (r • e l) ((eja_nonneg_iff _).mpr
          (eja_isSumSq_smul hr0 ((eja_nonneg_iff _).mp (eja_idem_nonneg (hidem l hl)))))
        (by rw [hdec]; exact hterm (fun r => r) hl0 l hl r hr0 (hr ▸ min_le_left _ _))
        (by rw [h1p]; exact hterm (fun r => 1 - r) hl1 l hl r hr0 (hr ▸ min_le_right _ _))
      rcases smul_eq_zero.mp hq with h | h
      · rcases min_choice l (1 - l) with h' | h'
        · rw [h', h] at hr; exact Or.inl hr.symm
        · rw [h', h] at hr; exact Or.inr (by linarith)
      · exact absurd h (hne0 l hl)
    rw [hdec, eja_ortho_mul hidem horth]
    refine Finset.sum_congr rfl fun l hl => ?_
    rcases hl01 l hl with h | h <;> rw [h] <;> norm_num
  · intro hp q hq0 hqp hqp'
    have hq1 : q ≤ 1 := le_trans hqp hp1
    have h1 : ejaU p q = q := (idem_Q_eq_self_iff hp hq0 hq1).mpr hqp
    have h2 : ejaU p q ≤ ejaU p (1 - p) := eja_U_mono p hqp'
    have h3 : ejaU p (1 - p) = 0 := by
      rw [ejaU_apply, eja_mul_sub, eja_mul_one, hp, sub_self, eja_mul_zero, eja_mul_sub,
        eja_mul_one, hp, sub_self]; simp
    rw [h1, h3] at h2
    exact le_antisymm h2 hq0

/-- Idempotents `p, q` are orthogonal iff `p ≤ 1 - q`. -/
theorem idem_orth_iff_le {p q : V} (hp : p * p = p) (hq : q * q = q) :
    p * q = 0 ↔ p ≤ 1 - q := by
  rw [idem_le_idem_iff hp (eja_one_sub_idem hq), eja_sub_mul, eja_one_mul, sub_eq_self,
    eja_mul_comm]

/-- A **unital Jordan isomorphism**: a linear isomorphism preserving `1` and the
Jordan product. -/
structure IsJordanIso (Θ : V ≃ₗ[ℝ] W) : Prop where
  map_one : Θ 1 = 1
  map_mul : ∀ a b : V, Θ (a * b) = Θ a * Θ b

namespace IsJordanIso

variable {Θ : V ≃ₗ[ℝ] W}

theorem symm (h : IsJordanIso Θ) : IsJordanIso Θ.symm where
  map_one := by rw [← h.map_one, LinearEquiv.symm_apply_apply]
  map_mul a b := by
    apply Θ.injective
    rw [h.map_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

theorem trans {X : Type u} [AddCommGroup X] [Module ℝ X] [Mul X] [One X]
    [PartialOrder X] [EuclideanJordanAlgebra X] {Φ : W ≃ₗ[ℝ] X}
    (h : IsJordanIso Θ) (h' : IsJordanIso Φ) : IsJordanIso (Θ.trans Φ) where
  map_one := by simp [h.map_one, h'.map_one]
  map_mul a b := by simp [h.map_mul, h'.map_mul]

theorem idem (h : IsJordanIso Θ) {p : V} (hp : p * p = p) : Θ p * Θ p = Θ p := by
  rw [← h.map_mul, hp]

theorem nonneg (h : IsJordanIso Θ) {x : V} (hx : 0 ≤ x) : 0 ≤ Θ x := by
  obtain ⟨b, rfl⟩ := (eja_nonneg_iff_exists_sq x).mp hx
  rw [h.map_mul, eja_nonneg_iff]; exact IsSumSq.mul_self _

theorem nonneg_iff (h : IsJordanIso Θ) (x : V) : 0 ≤ Θ x ↔ 0 ≤ x := by
  refine ⟨fun hx => ?_, h.nonneg⟩
  have := h.symm.nonneg hx
  rwa [LinearEquiv.symm_apply_apply] at this

theorem primitive (h : IsJordanIso Θ) {p : V} (hp : EJAPrimitive p) : EJAPrimitive (Θ p) where
  idem := h.idem hp.idem
  ne_zero := by
    intro h0; apply hp.ne_zero; rw [← map_zero Θ] at h0; exact Θ.injective h0
  line y hy := by
    obtain ⟨r, hr⟩ := hp.line (Θ.symm y) (by
      apply Θ.injective
      rw [h.map_mul, LinearEquiv.apply_symm_apply, hy])
    exact ⟨r, by rw [← LinearEquiv.apply_symm_apply Θ y, hr, map_smul]⟩

/-- **EJA 37** for Jordan isomorphisms: `Θ(Q_a b) = Q_{Θ a}(Θ b)`. -/
theorem map_U (h : IsJordanIso Θ) (a b : V) : Θ (ejaU a b) = ejaU (Θ a) (Θ b) := by
  simp only [ejaU_apply, map_sub, map_smul, h.map_mul]

end IsJordanIso

/-- **EJA 36** (main.tex:788, Proposition): a unital order isomorphism between
Euclidean Jordan algebras is a Jordan isomorphism.  The paper's proof: it maps
idempotents (= order-sharp effects, EJA 35) to idempotents and orthogonal ones
to orthogonal ones, so it preserves spectral decompositions and hence squares;
polarise. -/
theorem unital_order_iso_jordan (Θ : V ≃ₗ[ℝ] W) (h1 : Θ 1 = 1)
    (hpos : ∀ x, 0 ≤ Θ x ↔ 0 ≤ x) : IsJordanIso Θ := by
  classical
  have hle : ∀ x y, Θ x ≤ Θ y ↔ x ≤ y := by
    intro x y; rw [← eja_sub_nonneg, ← map_sub, hpos, eja_sub_nonneg]
  have hpos' : ∀ z : W, 0 ≤ Θ.symm z ↔ 0 ≤ z := by
    intro z; rw [← hpos, LinearEquiv.apply_symm_apply]
  have hle' : ∀ x y : W, Θ.symm x ≤ Θ.symm y ↔ x ≤ y := by
    intro x y; rw [← hle, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have h1' : Θ.symm 1 = 1 := by rw [← h1, LinearEquiv.symm_apply_apply]
  -- idempotents go to idempotents
  have hidem : ∀ e : V, e * e = e → Θ e * Θ e = Θ e := by
    intro e he
    have he0 := eja_idem_nonneg he
    have he1 := eja_idem_le_one he
    have h0 : 0 ≤ Θ e := (hpos e).mpr he0
    have h1e : Θ e ≤ 1 := by rw [← h1]; exact (hle e 1).mpr he1
    refine (ordersharpprop h0 h1e).mp fun q hq0 hqe hqe' => ?_
    have hs := (ordersharpprop he0 he1).mpr he (Θ.symm q) ((hpos' q).mpr hq0)
      (by rw [← hle', LinearEquiv.symm_apply_apply] at hqe; exact hqe)
      (by
        have : Θ.symm q ≤ Θ.symm (1 - Θ e) := (hle' _ _).mpr hqe'
        rwa [map_sub, h1', LinearEquiv.symm_apply_apply] at this)
    rw [← LinearEquiv.apply_symm_apply Θ q, hs, map_zero]
  -- orthogonal idempotents go to orthogonal idempotents
  have horth : ∀ e f : V, e * e = e → f * f = f → e * f = 0 → Θ e * Θ f = 0 := by
    intro e f he hf hef
    rw [idem_orth_iff_le (hidem e he) (hidem f hf), ← h1, ← map_sub, hle]
    exact (idem_orth_iff_le he hf).mp hef
  -- squares
  have hsq : ∀ a : V, Θ (a * a) = Θ a * Θ a := by
    intro a
    obtain ⟨s, e, hid, hor, _, _, hdec⟩ := eja_spectral a
    have hid' : ∀ l ∈ s, Θ (e l) * Θ (e l) = Θ (e l) := fun l hl => hidem _ (hid l hl)
    have hor' : ∀ l ∈ s, ∀ k ∈ s, l ≠ k → Θ (e l) * Θ (e k) = 0 := fun l hl k hk hlk =>
      horth _ _ (hid l hl) (hid k hk) (hor l hl k hk hlk)
    have hΘa : Θ a = ∑ l ∈ s, l • Θ (e l) := by
      rw [hdec, map_sum]; exact Finset.sum_congr rfl fun l _ => map_smul _ _ _
    rw [hΘa, eja_ortho_mul hid' hor', hdec, eja_ortho_mul hid hor, map_sum]
    exact Finset.sum_congr rfl fun l _ => map_smul _ _ _
  refine ⟨h1, fun a b => ?_⟩
  have hpol : ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [Mul X] [One X]
      [PartialOrder X] [EuclideanJordanAlgebra X] (x y : X),
      x * y = (1 / 2 : ℝ) • ((x + y) * (x + y) - x * x - y * y) := by
    intro X _ _ _ _ _ _ x y
    rw [eja_add_mul_add, eja_mul_comm y x]; module
  rw [hpol a b, hpol (Θ a) (Θ b), map_smul, map_sub, map_sub, hsq, hsq, hsq, map_add]

/-- **EJA 37** (main.tex:803, Corollary): for a unital order isomorphism `Θ`,
`Θ ∘ Q_a = Q_{Θ a} ∘ Θ`, equivalently `Q_a ∘ Θ = Θ ∘ Q_{Θ⁻¹ a}`. -/
theorem unital_order_iso_U (Θ : V ≃ₗ[ℝ] W) (h1 : Θ 1 = 1)
    (hpos : ∀ x, 0 ≤ Θ x ↔ 0 ≤ x) (a : V) (b : W) :
    (∀ x, Θ (ejaU a x) = ejaU (Θ a) (Θ x)) ∧ ejaU (Θ a) b = Θ (ejaU a (Θ.symm b)) := by
  have hJ := unital_order_iso_jordan Θ h1 hpos
  refine ⟨hJ.map_U a, ?_⟩
  rw [hJ.map_U, LinearEquiv.apply_symm_apply]

end Jordan

/-! ## EJA 28–29: images -/

section Image

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]
variable {W : Type u} [AddCommGroup W] [Module ℝ W] [Mul W] [One W]
  [PartialOrder W] [EuclideanJordanAlgebra W]

theorem IsPositiveMap.mono {f : V →ₗ[ℝ] W} (hf : IsPositiveMap f) {x y : V} (h : x ≤ y) :
    f x ≤ f y := by
  rw [← eja_sub_nonneg, ← map_sub]; exact hf _ (eja_sub_nonneg.mpr h)

/-- **EJA 28** (main.tex:660, Definition): `p` is *the image* of a positive linear
map `g` when it is the smallest effect with `g(p) = g(1)`. -/
def IsImageOf (g : V →ₗ[ℝ] W) (p : V) : Prop :=
  (0 ≤ p ∧ p ≤ 1) ∧ g p = g 1 ∧ ∀ e : V, 0 ≤ e → e ≤ 1 → g e = g 1 → p ≤ e

theorem IsImageOf.unique {g : V →ₗ[ℝ] W} {p p' : V} (h : IsImageOf g p)
    (h' : IsImageOf g p') : p = p' :=
  le_antisymm (h.2.2 p' h'.1.1 h'.1.2 h'.2.1) (h'.2.2 p h.1.1 h.1.2 h.2.1)

/-- For an idempotent `s` and an effect `e`: `s ≤ e ⟺ s * (1 - e) = 0`. -/
theorem idem_le_effect_iff {s e : V} (hs : s * s = s) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    s ≤ e ↔ s * (1 - e) = 0 := by
  have h0 : (0 : V) ≤ 1 - e := eja_sub_nonneg.mpr he1
  have h1 : 1 - e ≤ 1 := by rw [← eja_sub_nonneg, sub_sub_cancel]; exact he0
  have := le_idem_iff_mul_one_sub h0 h1 (eja_one_sub_idem hs)
  rw [sub_sub_cancel] at this
  have hrw : (1 - s) - (1 - e) = e - s := by abel
  rw [← this, ← eja_sub_nonneg, ← eja_sub_nonneg (a := 1 - e), hrw]

/-- **EJA 29** (`eja:im`, main.tex:668, Proposition): every positive linear map
`g` between Euclidean Jordan algebras has an image, and it is an idempotent.
The paper argues through JBW-algebras (idempotents form a complete lattice,
states are normal); in finite dimension we take the support of the Riesz
representative of `tr ∘ g` (tree `eja_exists_riesz`, `eja_exists_supp`). -/
theorem eja_im (g : V →ₗ[ℝ] W) (hg : IsPositiveMap g) :
    ∃ p : V, p * p = p ∧ IsImageOf g p := by
  obtain ⟨w, hw⟩ := eja_exists_riesz (ejaTrL.comp g)
  have hω : ∀ x : V, ejaB w x = ejaB (g x) 1 := by
    intro x; rw [← hw]; show ejaTrL (g x) = ejaTrL (g x * 1); rw [eja_mul_one]
  have hker : ∀ x : V, 0 ≤ x → (g x = 0 ↔ ejaB w x = 0) := by
    intro x hx
    rw [hω, ← idem_mul_eq_zero_iff_ejaB (hg x hx) (eja_mul_one 1), eja_one_mul]
  have hw0 : 0 ≤ w := eja_nonneg_of_forall_idem fun t ht => by
    rw [hω]; exact eja_isSumSq_ejaB_idem_nonneg ((eja_nonneg_iff _).mp (hg t (eja_idem_nonneg ht)))
      1 (eja_mul_one 1)
  obtain ⟨s, hs, hs0, hs1, hsupp⟩ := eja_exists_supp hw0
  have key : ∀ e : V, 0 ≤ e → e ≤ 1 → (g e = g 1 ↔ s ≤ e) := by
    intro e he0 he1
    have h0 : (0 : V) ≤ 1 - e := eja_sub_nonneg.mpr he1
    rw [idem_le_effect_iff hs he0 he1, idem_mul_eq_zero_iff_ejaB h0 hs, ejaB_symm,
      ← hsupp _ h0, ← hker _ h0, map_sub, sub_eq_zero, eq_comm]
  exact ⟨s, hs, ⟨hs0, hs1⟩, (key s hs0 hs1).mpr le_rfl, fun e he0 he1 he => (key e he0 he1).mp he⟩

open Classical in
/-- The image `im g` (junk `0` if it does not exist; by EJA 29 it always does for
positive `g`). -/
noncomputable def ejaIm (g : V →ₗ[ℝ] W) : V :=
  if h : ∃ p, IsImageOf g p then h.choose else 0

theorem ejaIm_spec {g : V →ₗ[ℝ] W} (hg : IsPositiveMap g) :
    ejaIm g * ejaIm g = ejaIm g ∧ IsImageOf g (ejaIm g) := by
  obtain ⟨p, hp, himp⟩ := eja_im g hg
  have hex : ∃ p, IsImageOf g p := ⟨p, himp⟩
  have heq : ejaIm g = p := by
    rw [ejaIm, dif_pos hex]; exact hex.choose_spec.unique himp
  rw [heq]; exact ⟨hp, himp⟩

/-- `im g ≤ e ⟺ g(e) = g(1)` for an effect `e`. -/
theorem ejaIm_le_iff {g : V →ₗ[ℝ] W} (hg : IsPositiveMap g) {e : V} (he0 : 0 ≤ e)
    (he1 : e ≤ 1) : ejaIm g ≤ e ↔ g e = g 1 := by
  obtain ⟨_, ⟨hi0, hi1⟩, hgi, hmin⟩ := ejaIm_spec hg
  refine ⟨fun h => le_antisymm (hg.mono he1) ?_, fun h => hmin e he0 he1 h⟩
  rw [← hgi]; exact hg.mono h

/-- Main.tex, before EJA 38: a positive map `f` is *faithful* (`f(a) = 0`,
`a ≥ 0` ⟹ `a = 0`) iff `im f = 1`. -/
theorem faithful_iff_im (g : V →ₗ[ℝ] W) (hg : IsPositiveMap g) :
    (∀ a : V, 0 ≤ a → g a = 0 → a = 0) ↔ ejaIm g = 1 := by
  obtain ⟨hid, ⟨hi0, hi1⟩, hgi, hmin⟩ := ejaIm_spec hg
  constructor
  · intro hf
    have h0 : (0 : V) ≤ 1 - ejaIm g := eja_sub_nonneg.mpr hi1
    have := hf _ h0 (by rw [map_sub, hgi, sub_self])
    exact (sub_eq_zero.mp this).symm
  · intro h1 a ha hga
    obtain ⟨n, _, hn⟩ := chu_strong_unit a
    set t : ℝ := 1 / ((n : ℝ) + 1) with htdef
    have ht : 0 < t := by positivity
    have htn : t * n ≤ 1 := by
      rw [htdef, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    set e : V := 1 - t • a with hedef
    have hta : 0 ≤ t • a := (eja_nonneg_iff _).mpr (eja_isSumSq_smul ht.le ((eja_nonneg_iff _).mp ha))
    have he1 : e ≤ 1 := by rw [← eja_sub_nonneg, hedef, sub_sub_cancel]; exact hta
    have he0 : 0 ≤ e := by
      rw [hedef, eja_nonneg_iff]
      have h1 : t • a ≤ (t * n) • (1 : V) := by
        rw [← eja_sub_nonneg, mul_smul, ← smul_sub, eja_nonneg_iff]
        exact eja_isSumSq_smul ht.le ((eja_nonneg_iff _).mp (eja_sub_nonneg.mpr hn))
      have h2 : (t * n) • (1 : V) ≤ 1 := by
        rw [← eja_sub_nonneg, eja_nonneg_iff]
        have : (1 : V) - (t * n) • 1 = (1 - t * n) • 1 := by rw [sub_smul, one_smul]
        rw [this]; exact eja_isSumSq_smul_one (by linarith)
      exact (eja_nonneg_iff _).mp (eja_sub_nonneg.mpr (le_trans h1 h2))
    have hge : g e = g 1 := by rw [hedef, map_sub, map_smul, hga, smul_zero, sub_zero]
    have hle := hmin e he0 he1 hge
    rw [h1, ← eja_sub_nonneg, hedef, sub_sub_cancel_left] at hle
    have hneg : t • a ≤ 0 := by
      rw [← eja_sub_nonneg, zero_sub]; exact hle
    have hta0 : t • a = 0 := le_antisymm hneg hta
    exact (smul_eq_zero.mp hta0).resolve_left ht.ne'

end Image

/-! ## EJA 32–33: ⋄-adjointness -/

section Diamond

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]
variable {W : Type u} [AddCommGroup W] [Module ℝ W] [Mul W] [One W]
  [PartialOrder W] [EuclideanJordanAlgebra W]

/-- **EJA 32** (main.tex:730, Definition), `f^⋄(p) = ⌈f(p)⌉` on idempotents.
The print writes `⌈p ∘ f⌉`, reading `f` in the effectus direction; its uses
(proofs of EJA 33 and 38) evaluate `f` at `p` (PLAN §2).  For a positive
subunital `f` the argument `f(p)` is an effect, where `⌈·⌉` is EJA 13. -/
noncomputable def diaUp (f : V →ₗ[ℝ] W) (p : V) : W := ejaCeil (f p)

/-- **EJA 32**, `f_⋄(q) = im(Q_q ∘ f)`. -/
noncomputable def diaDown (f : V →ₗ[ℝ] W) (q : W) : V := ejaIm ((ejaU q).comp f)

/-- **EJA 32**: `f : V → W` is *⋄-adjoint* to `g : W → V` when `f^⋄ = g_⋄` on
idempotents. -/
def IsDiaAdjoint (f : V →ₗ[ℝ] W) (g : W →ₗ[ℝ] V) : Prop :=
  ∀ p : V, p * p = p → diaUp f p = diaDown g p

/-- **EJA 32**: `f` is *⋄-self-adjoint* when it is ⋄-adjoint to itself. -/
def IsDiaSA (f : V →ₗ[ℝ] V) : Prop := IsDiaAdjoint f f

/-- **EJA 32**: `f` is *⋄-positive* when `f = g ∘ g` for a ⋄-self-adjoint
positive subunital `g`. -/
def IsDiaPos (f : V →ₗ[ℝ] V) : Prop :=
  ∃ g : V →ₗ[ℝ] V, IsPositiveMap g ∧ g 1 ≤ 1 ∧ IsDiaSA g ∧ f = g.comp g

theorem effect_of_psu {f : V →ₗ[ℝ] W} (hf : IsPositiveMap f) (hf1 : f 1 ≤ 1) {x : V}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ f x ∧ f x ≤ 1 :=
  ⟨hf x hx0, le_trans (hf.mono hx1) hf1⟩

/-- `f^⋄(s) ≤ 1 - t ⟺ t * f(s) = 0`. -/
theorem diaUp_le_iff {f : V →ₗ[ℝ] W} (hf : IsPositiveMap f) (hf1 : f 1 ≤ 1) {s : V}
    (hs : s * s = s) {t : W} (ht : t * t = t) : diaUp f s ≤ 1 - t ↔ t * f s = 0 := by
  obtain ⟨h0, h1⟩ := effect_of_psu hf hf1 (eja_idem_nonneg hs) (eja_idem_le_one hs)
  obtain ⟨_, hle, hmin⟩ := (EJAceilfloor h0 h1).2.2.1
  have ht' := eja_one_sub_idem ht
  rw [diaUp]
  constructor
  · intro h
    have := (le_idem_iff_mul_one_sub h0 h1 ht').mp (le_trans hle h)
    rwa [sub_sub_cancel] at this
  · intro h
    refine hmin _ ht' ?_
    rw [le_idem_iff_mul_one_sub h0 h1 ht', sub_sub_cancel]; exact h

/-- `f_⋄(t) ≤ 1 - s ⟺ t * f(s) = 0`. -/
theorem diaDown_le_iff {f : V →ₗ[ℝ] W} (hf : IsPositiveMap f) {s : V} (hs : s * s = s)
    {t : W} (ht : t * t = t) : diaDown f t ≤ 1 - s ↔ t * f s = 0 := by
  have hg : IsPositiveMap ((ejaU t).comp f) := fun x hx => eja_U_nonneg' t (hf x hx)
  have hs' := eja_one_sub_idem hs
  rw [diaDown, ejaIm_le_iff hg (eja_idem_nonneg hs') (eja_idem_le_one hs')]
  simp only [LinearMap.comp_apply, map_sub, sub_eq_self]
  rw [eja_U_eq_zero_iff (eja_idem_nonneg ht) (hf s (eja_idem_nonneg hs))]

theorem diaUp_idem (f : V →ₗ[ℝ] W) (p : V) : diaUp f p * diaUp f p = diaUp f p :=
  ejaCeil_idem _

theorem diaDown_idem {f : V →ₗ[ℝ] W} (hf : IsPositiveMap f) (q : W) :
    diaDown f q * diaDown f q = diaDown f q :=
  (ejaIm_spec (g := (ejaU q).comp f) (fun x hx => eja_U_nonneg' q (hf x hx))).1

/-- Idempotents with the same idempotents above their complements agree. -/
theorem idem_eq_of_le_one_sub_iff {a b : V} (ha : a * a = a) (hb : b * b = b)
    (h : ∀ e : V, e * e = e → (a ≤ 1 - e ↔ b ≤ 1 - e)) : a = b := by
  have h1 := (h (1 - a) (eja_one_sub_idem ha)).mp (by rw [sub_sub_cancel])
  have h2 := (h (1 - b) (eja_one_sub_idem hb)).mpr (by rw [sub_sub_cancel])
  rw [sub_sub_cancel] at h1 h2
  exact le_antisymm h2 h1

/-- **The ⋄-adjointness criterion** (EJA 33's proof, via B §207III):
`f` is ⋄-adjoint to `g` iff `t * f(s) = 0 ⟺ s * g(t) = 0` for all idempotents
`s, t` (equivalently `⟨f(s), t⟩ = 0 ⟺ ⟨s, g(t)⟩ = 0`, `idem_mul_eq_zero_iff_ejaB`). -/
theorem diaAdjoint_iff {f : V →ₗ[ℝ] W} {g : W →ₗ[ℝ] V} (hf : IsPositiveMap f) (hf1 : f 1 ≤ 1)
    (hg : IsPositiveMap g) :
    IsDiaAdjoint f g ↔ ∀ s : V, s * s = s → ∀ t : W, t * t = t → (t * f s = 0 ↔ s * g t = 0) := by
  constructor
  · intro h s hs t ht
    rw [← diaUp_le_iff hf hf1 hs ht, h s hs, diaDown_le_iff hg ht hs]
  · intro h p hp
    refine idem_eq_of_le_one_sub_iff (diaUp_idem f p) (diaDown_idem hg p) fun e he => ?_
    rw [diaUp_le_iff hf hf1 hp he, diaDown_le_iff hg he hp]
    exact h p hp e he

/-- **EJA 32**, "equivalently": `f^⋄ = g_⋄` iff `f_⋄ = g^⋄`, i.e. `f` is
⋄-adjoint to `g` iff `g` is ⋄-adjoint to `f`. -/
theorem diaAdjoint_symm {f : V →ₗ[ℝ] W} {g : W →ₗ[ℝ] V} (hf : IsPositiveMap f) (hf1 : f 1 ≤ 1)
    (hg : IsPositiveMap g) (hg1 : g 1 ≤ 1) : IsDiaAdjoint f g ↔ IsDiaAdjoint g f := by
  rw [diaAdjoint_iff hf hf1 hg, diaAdjoint_iff hg hg1 hf]
  constructor <;> intro h
  · intro t ht s hs; exact (h s hs t ht).symm
  · intro s hs t ht; exact (h t ht s hs).symm

/-- The zero pattern of ⋄-self-adjointness. -/
theorem diaSA_iff {f : V →ₗ[ℝ] V} (hf : IsPositiveMap f) (hf1 : f 1 ≤ 1) :
    IsDiaSA f ↔ ∀ s : V, s * s = s → ∀ t : V, t * t = t → (t * f s = 0 ↔ s * f t = 0) :=
  diaAdjoint_iff hf hf1 hf

/-- For `x ≥ 0` and an idempotent `t`: `t * x = 0 ⟺ ⟨x, t⟩ = 0`, for any
associative inner product. -/
theorem idem_mul_eq_zero_iff_form (F : EJAForm V) {x t : V} (hx : 0 ≤ x) (ht : t * t = t) :
    t * x = 0 ↔ F.B x t = 0 := by
  rw [← eja_U_eq_zero_iff (eja_idem_nonneg ht) hx, idem_Q_eq_zero_iff F ht hx]

/-- **EJA 33** (`prop:diamond-adjointness`, main.tex:746, Proposition), first
claim: a positive subunital map that is self-adjoint for an associative inner
product is ⋄-self-adjoint.  ("Self-adjoint operator" must be positive
subunital for `f^⋄`, `f_⋄` to be defined; PLAN §2.) -/
theorem diamond_adjointness (F : EJAForm V) {f : V →ₗ[ℝ] V} (hf : IsPositiveMap f)
    (hf1 : f 1 ≤ 1) (hsa : ∀ x y, F.B (f x) y = F.B x (f y)) : IsDiaSA f := by
  rw [diaSA_iff hf hf1]
  intro s hs t ht
  rw [idem_mul_eq_zero_iff_form F (hf s (eja_idem_nonneg hs)) ht,
    idem_mul_eq_zero_iff_form F (hf t (eja_idem_nonneg ht)) hs, hsa, F.symm]

/-- **EJA 33**, second claim: `Q_a` is ⋄-self-adjoint (for `Q_a` subunital,
`a² ≤ 1`). -/
theorem diamond_adjointness_Q (a : V) (ha : a * a ≤ 1) : IsDiaSA (ejaU a) :=
  diamond_adjointness (EJAForm.trace V) (fun x hx => eja_U_nonneg' a hx)
    (by rw [ejaU_apply_one]; exact ha) (fun x y => (EJAForm.trace V).U_self_adj a x y)

/-- `Q_{b²} = Q_b ∘ Q_b`, without the fundamental formula (the one-family law,
tree `eja_U_family_comp'`). -/
theorem ejaU_mul_self (b y : V) : ejaU (b * b) y = ejaU b (ejaU b y) := by
  classical
  obtain ⟨s, e, hidem, horth, _, hsum, hdec⟩ := eja_spectral b
  rw [hdec, eja_ortho_mul hidem horth, eja_U_family_comp' _ _ hidem horth hsum]

/-- **EJA 33**, third claim: for an effect `a`, `Q_a` is ⋄-positive:
`Q_a = Q_{√a} ∘ Q_{√a}` (the paper cites the fundamental formula; the one-family
law suffices) with `Q_{√a}` ⋄-self-adjoint. -/
theorem diamond_positive_Q {a : V} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : IsDiaPos (ejaU a) := by
  obtain ⟨hs0, hss⟩ := ejaSqrt_spec ha0
  refine ⟨ejaU (ejaSqrt a), fun x hx => eja_U_nonneg' _ hx, ?_, ?_, ?_⟩
  · rw [ejaU_apply_one, hss]; exact ha1
  · exact diamond_adjointness_Q _ (by rw [hss]; exact ha1)
  · ext y; rw [LinearMap.comp_apply, ← ejaU_mul_self, hss]

end Diamond

/-! ## EJA 38′: the repaired Lemma 38, algebraic core -/

section Lemma38

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- The coefficients of a positive frame combination are non-negative. -/
theorem frame_coeff_nonneg {ι : Type*} [Fintype ι] {p : ι → V} (hp : IsOrthFrame p)
    (hne : ∀ i, p i ≠ 0) {c : ι → ℝ} (h : 0 ≤ ∑ i, c i • p i) (i : ι) : 0 ≤ c i := by
  have h1 := eja_isSumSq_ejaB_idem_nonneg ((eja_nonneg_iff _).mp h) (p i) (hp.idem i)
  have h2 : ejaB (∑ j, c j • p j) (p i) = ejaB (c i • p i) (p i) := by
    show ejaTrL (_ * _) = ejaTrL (_ * _)
    rw [frame_mul_elt hp, eja_smul_mul, hp.idem]
  rw [h2, ejaB_smul_left] at h1
  exact nonneg_of_mul_nonneg_left h1 (ejaB_self_pos (hne i))

/-- An eigenvector of `T²` is an eigenvector of `T`, for `T` trace-self-adjoint
and positive semidefinite. -/
theorem eigen_of_sq {T : V →ₗ[ℝ] V} (hsa : ∀ x y, ejaB (T x) y = ejaB x (T y))
    (hpsd : ∀ w, 0 ≤ ejaB (T w) w) {u : V} {κ : ℝ} (h : T (T u) = κ • u) :
    ∃ α : ℝ, T u = α • u := by
  by_cases hκ : κ ≤ 0
  · refine ⟨0, ?_⟩
    have h1 : ejaB (T u) (T u) = κ * ejaB u u := by
      rw [← hsa, h, ejaB_smul_left]
    have h2 : ejaB (T u) (T u) ≤ 0 := by
      rw [h1]; exact mul_nonpos_of_nonpos_of_nonneg hκ (ejaB_self_nonneg u)
    rw [zero_smul]
    exact eja_eq_zero_of_ejaB_self (le_antisymm h2 (ejaB_self_nonneg _))
  · push Not at hκ
    set m := Real.sqrt κ with hm
    have hmm : m * m = κ := Real.mul_self_sqrt hκ.le
    have hm0 : 0 < m := Real.sqrt_pos.mpr hκ
    set v := T u - m • u with hv
    have hTv : T v = (-m) • v := by
      rw [hv, map_sub, map_smul, h, ← hmm, smul_sub, smul_smul]; module
    have h1 : ejaB (T v) v = -m * ejaB v v := by rw [hTv, ejaB_smul_left]
    have h2 : ejaB v v ≤ 0 := by
      have := hpsd v
      rw [h1] at this
      nlinarith [ejaB_self_nonneg v]
    have hv0 : v = 0 := eja_eq_zero_of_ejaB_self (le_antisymm h2 (ejaB_self_nonneg _))
    exact ⟨m, sub_eq_zero.mp hv0⟩

/-- **EJA 38′, algebraic core** (the repair of EJA 38, `docs/research/review-eja38.md`
and PLAN §2).  Let `q ≥ 0` with `Q_q` faithful, `Θ` a unital Jordan
automorphism, and suppose `f = Q_q ∘ Θ` has the ⋄-self-adjoint zero pattern
(`diaSA_iff`).  Then `q` and `Θ(q)` are diagonal in one Jordan frame of
primitive idempotents (so `Θ(q)` operator-commutes with `q`), and `Θ ∘ Θ = id`.

Proof (steps A–D of the PLAN): the printed proof's valid part gives
`f(qᵢ) = μᵢ Θ⁻¹(qᵢ)` on a frame `(qᵢ)` of `q`; summing and uniqueness of square
roots put `q` on the frame `rᵢ = Θ⁻¹(qᵢ)`, whence `Θ(qᵢ) = rᵢ`.  For `Θ² = id`:
with `Q_{Θq} = Q_q Q_c` (`c > 0` on the frame) the zero pattern gives
`⟨Q_c Θ²(s), w⟩ = 0 ⟺ ⟨s, w⟩ = 0`; so `Q_c` maps each primitive `u` onto the
line of `Θ⁻²(u)`, preserves orthogonality, hence `Q_c² u ∈ ℝu`, hence
`Q_c u ∈ ℝu` (`Q_c ≥ 0` as an operator), hence `Θ⁻²(u) = u`. -/
theorem eja38'_core {q : V} (hq : 0 ≤ q) (hqf : ∀ x, 0 ≤ x → ejaU q x = 0 → x = 0)
    {Θ : V ≃ₗ[ℝ] V} (hΘ : IsJordanIso Θ)
    (hZ : ∀ s : V, s * s = s → ∀ t : V, t * t = t →
      (t * ejaU q (Θ s) = 0 ↔ s * ejaU q (Θ t) = 0)) :
    (∃ (ι : Type) (_ : Fintype ι) (r : ι → V) (a b : ι → ℝ),
      (∀ i, EJAPrimitive (r i)) ∧ IsOrthFrame r ∧ (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      q = ∑ i, a i • r i ∧ Θ q = ∑ i, b i • r i) ∧
    (∀ x, q * (Θ q * x) = Θ q * (q * x)) ∧ (∀ x, Θ (Θ x) = x) := by
  classical
  obtain ⟨ι, hι, lam, qq, hprim, horth, hsum, hdec⟩ := spectral_primitive q
  have hfq : IsOrthFrame qq := ⟨fun i => (hprim i).idem, horth, hsum⟩
  have hlam0 : ∀ i, 0 ≤ lam i :=
    frame_coeff_nonneg hfq (fun i => (hprim i).ne_zero) (hdec ▸ hq)
  have hQqq : ∀ i, ejaU q (qq i) = (lam i * lam i) • qq i := by
    intro i; rw [hdec]; exact frame_U_elt hfq lam i
  have hlampos : ∀ i, 0 < lam i := by
    intro i
    refine lt_of_le_of_ne (hlam0 i) fun h => (hprim i).ne_zero ?_
    exact hqf _ (eja_idem_nonneg (hprim i).idem) (by rw [hQqq, ← h, mul_zero, zero_smul])
  -- Step A
  set r : ι → V := fun i => Θ.symm (qq i) with hrdef
  have hΘs := hΘ.symm
  have hrprim : ∀ i, EJAPrimitive (r i) := fun i => hΘs.primitive (hprim i)
  have hr : IsOrthFrame r := by
    refine ⟨fun i => (hrprim i).idem, fun i j hij => ?_, ?_⟩
    · show Θ.symm (qq i) * Θ.symm (qq j) = 0
      rw [← hΘs.map_mul, horth i j hij, map_zero]
    · show ∑ i, Θ.symm (qq i) = 1
      rw [← map_sum, hsum, hΘs.map_one]
  have hΘr : ∀ i, Θ (r i) = qq i := fun i => LinearEquiv.apply_symm_apply Θ (qq i)
  have hqq : q * q = ∑ i, (lam i * lam i) • qq i := by rw [hdec]; exact frame_mul hfq lam lam
  have hA : ∀ i, ∃ μ : ℝ, ejaU q (Θ (qq i)) = μ • r i := by
    intro i
    have hri := (hrprim i).idem
    have h := (hZ (qq i) (hprim i).idem (1 - r i) (eja_one_sub_idem hri)).mpr (by
      rw [map_sub, hΘ.map_one, hΘr, map_sub, ejaU_apply_one, hQqq, hqq, eja_mul_sub,
        eja_mul_comm, frame_mul_elt hfq, eja_mul_smul, (hprim i).idem, sub_self])
    exact line_of_perp (hrprim i) h
  choose μ hμ using hA
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => smul_idem_nonneg_coeff (hrprim i).idem (hrprim i).ne_zero
    (by rw [← hμ]; exact eja_U_nonneg' q (hΘ.nonneg (eja_idem_nonneg (hprim i).idem)))
  -- Step B
  have hqq' : q * q = ∑ i, μ i • r i := by
    rw [← ejaU_apply_one, ← hΘ.map_one, ← hsum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hμ i
  set a : ι → ℝ := fun i => Real.sqrt (μ i) with hadef
  have hqa : q = ∑ i, a i • r i := by
    refine sqrt_unique hq (frame_nonneg hr fun i => Real.sqrt_nonneg _) ?_
    rw [frame_mul hr, hqq']
    exact Finset.sum_congr rfl fun i _ => by
      show μ i • r i = (Real.sqrt (μ i) * Real.sqrt (μ i)) • r i
      rw [Real.mul_self_sqrt (hμ0 i)]
  have hQr : ∀ i, ejaU q (r i) = μ i • r i := by
    intro i; rw [hqa, frame_U_elt hr]; congr 1; exact Real.mul_self_sqrt (hμ0 i)
  have hane : ∀ i, a i ≠ 0 := by
    intro i h
    have hμi : μ i = 0 := by
      have h2 : Real.sqrt (μ i) = 0 := h
      rwa [Real.sqrt_eq_zero (hμ0 i)] at h2
    exact (hrprim i).ne_zero (hqf _ (eja_idem_nonneg (hrprim i).idem)
      (by rw [hQr, hμi, zero_smul]))
  have hapos : ∀ i, 0 < a i := fun i => lt_of_le_of_ne (Real.sqrt_nonneg _) (hane i).symm
  have hQinj : Function.Injective (ejaU q) := by rw [hqa]; exact frame_U_injective hr hane
  have hΘqq : ∀ i, Θ (qq i) = r i := fun i => hQinj (by rw [hμ, hQr])
  have hΘq : Θ q = ∑ i, lam i • r i := by
    rw [hdec, map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hΘqq]
  have hcomm : ∀ x, q * (Θ q * x) = Θ q * (q * x) := by
    intro x; rw [hΘq, hqa]; exact frame_commute hr a lam x
  refine ⟨⟨ι, hι, r, a, lam, hrprim, hr, hapos, hlampos, hqa, hΘq⟩, hcomm, ?_⟩
  -- Step C
  set c : ι → ℝ := fun i => lam i / a i with hcdef
  have hcpos : ∀ i, 0 < c i := fun i => div_pos (hlampos i) (hapos i)
  set C : V := ∑ i, c i • r i with hCdef
  have hQ' : ∀ y, ejaU (Θ q) y = ejaU q (ejaU C y) := by
    intro y
    rw [hΘq, hqa, hCdef, frame_U_comp hr]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by rw [hcdef, mul_div_cancel₀ _ (hane i)]
  have hmulΘ : ∀ w x : V, (Θ.symm w * x = 0 ↔ w * Θ x = 0) := by
    intro w x
    constructor
    · intro h; rw [← LinearEquiv.apply_symm_apply Θ w, ← hΘ.map_mul, h, map_zero]
    · intro h
      apply Θ.injective
      rw [hΘ.map_mul, LinearEquiv.apply_symm_apply, h, map_zero]
  have hswap : ∀ s w : V, s * s = s → w * w = w →
      (s * ejaU q w = 0 ↔ w * ejaU q s = 0) := by
    intro s w hs hw
    rw [idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' q (eja_idem_nonneg hw)) hs,
      idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' q (eja_idem_nonneg hs)) hw,
      ← ejaB_U_self_adj, ejaB_symm]
  have hR2 : ∀ s w : V, s * s = s → w * w = w →
      (ejaB (ejaU q (ejaU C (Θ (Θ s)))) w = 0 ↔ ejaB (ejaU q s) w = 0) := by
    intro s w hs hw
    have h := hZ s hs (Θ.symm w) (hΘs.idem hw)
    rw [hmulΘ, LinearEquiv.apply_symm_apply, hswap s w hs hw, hΘ.map_U, hQ'] at h
    rw [← idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' q (eja_U_nonneg' C
        (hΘ.nonneg (hΘ.nonneg (eja_idem_nonneg hs))))) hw,
      ← idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' q (eja_idem_nonneg hs)) hw]
    exact h
  set qi : V := ∑ i, (a i)⁻¹ • r i with hqidef
  have hQQi : ∀ w, ejaU q (ejaU qi w) = w := by
    intro w
    rw [hqa, hqidef, frame_U_comp hr]
    have : ∑ i, (a i * (a i)⁻¹) • r i = 1 := by
      simp only [mul_inv_cancel₀ (hane _), one_smul]; exact hr.sum_one
    rw [this, ejaU_one]; rfl
  have hR3 : ∀ s w : V, s * s = s → w * w = w →
      (ejaB (ejaU C (Θ (Θ s))) w = 0 ↔ ejaB s w = 0) := by
    intro s w hs hw
    have hx : 0 ≤ ejaU C (Θ (Θ s)) := eja_U_nonneg' C (hΘ.nonneg (hΘ.nonneg (eja_idem_nonneg hs)))
    have hy : 0 ≤ s := eja_idem_nonneg hs
    have hz : 0 ≤ ejaU qi w := eja_U_nonneg' qi (eja_idem_nonneg hw)
    have key := zero_pattern_extend (eja_U_nonneg' q hx) (eja_U_nonneg' q hy)
      (fun w' hw' => hR2 s w' hs hw') hz
    rw [← ejaB_U_self_adj q _ (ejaU qi w), ← ejaB_U_self_adj q s (ejaU qi w), hQQi] at key
    exact key
  -- Step D
  set J : V ≃ₗ[ℝ] V := Θ.symm.trans Θ.symm with hJdef
  have hJ : IsJordanIso J := hΘs.trans hΘs
  have hΘΘJ : ∀ x, Θ (Θ (J x)) = x := by
    intro x; simp [hJdef]
  have hCpsd : ∀ w, 0 ≤ ejaB (ejaU C w) w := fun w => frame_U_psd hr (fun i => (hcpos i).le) w
  have hCsa : ∀ x y, ejaB (ejaU C x) y = ejaB x (ejaU C y) := fun x y => (ejaB_U_self_adj C x y).symm
  have hCinj : Function.Injective (ejaU C) := frame_U_injective hr fun i => (hcpos i).ne'
  have hline : ∀ u : V, EJAPrimitive u → ∃ ν : ℝ, ejaU C u = ν • J u := by
    intro u hu
    have hv := hJ.primitive hu
    have h := (hR3 (J u) (1 - J u) hv.idem (eja_one_sub_idem hv.idem)).mpr (by
      show ejaTrL (J u * (1 - J u)) = 0
      rw [eja_mul_sub, eja_mul_one, hv.idem, sub_self, map_zero])
    rw [hΘΘJ] at h
    rw [← idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' C (eja_idem_nonneg hu.idem))
      (eja_one_sub_idem hv.idem)] at h
    exact line_of_perp hv h
  have hfix : ∀ u : V, EJAPrimitive u → Θ (Θ u) = u := by
    intro u hu
    obtain ⟨ν, hν⟩ := hline u hu
    -- `Q_C² u ∈ ℝ u`
    have hperp : ∀ u' : V, EJAPrimitive u' → u * u' = 0 → ejaB (ejaU C (ejaU C u)) u' = 0 := by
      intro u' hu' huu'
      obtain ⟨ν', hν'⟩ := hline u' hu'
      rw [hCsa, hν, hν', ejaB_smul_left, ejaB_smul_right]
      have : J u * J u' = 0 := by rw [← hJ.map_mul, huu', map_zero]
      show ν * (ν' * ejaTrL (J u * J u')) = 0
      rw [this, map_zero, mul_zero, mul_zero]
    obtain ⟨m, f, hfprim, _, hfmem, hfsum⟩ :=
      idem_sum_primitive _ (1 - u) (eja_one_sub_idem hu.idem) le_rfl
    have hB : ejaB (ejaU C (ejaU C u)) (1 - u) = 0 := by
      rw [hfsum, ejaB_sum_right]
      refine Finset.sum_eq_zero fun k _ => hperp (f k) (hfprim k) ?_
      have := hfmem k
      rw [eja_sub_mul, eja_one_mul, sub_eq_self] at this
      exact this
    rw [← idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' C (eja_U_nonneg' C (eja_idem_nonneg hu.idem)))
      (eja_one_sub_idem hu.idem)] at hB
    obtain ⟨κ, hκ⟩ := line_of_perp hu hB
    obtain ⟨α, hα⟩ := eigen_of_sq (T := ejaU C) hCsa hCpsd hκ
    have hα0 : α ≠ 0 := by
      intro h0
      apply hu.ne_zero
      apply hCinj
      rw [hα, h0, zero_smul, map_zero]
    have hJu : J u = u := by
      have h1 : u = (α⁻¹ * ν) • J u := by
        rw [mul_smul, ← hν, hα, smul_smul, inv_mul_cancel₀ hα0, one_smul]
      exact (idem_eq_of_smul hu.idem (hJ.primitive hu).idem hu.ne_zero h1).symm
    have := hΘΘJ u
    rw [hJu] at this
    exact this
  intro x
  obtain ⟨κ, _, lam', p', hp'prim, _, _, hx⟩ := spectral_primitive x
  rw [hx, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hfix _ (hp'prim i)]

end Lemma38

/-! ## EJA 38: filters, corners and the decomposition `f = Q_{√f(1)} ∘ Θ` -/

section Decomp

/-- The inclusion `E₁(p) → E` of a corner, a morphism of `EJA_psu`. -/
def cornerVal (E : EJAPsu.{u}) (p : EJAIdem E.carrier) : EJAPsu.of (EJACorner p) ⟶ E where
  toLinearMap := EJACorner.valLin p
  map_nonneg' _ hy := eja_corner_val_nonneg hy
  map_subunital' := by
    show EJACorner.val (1 : EJACorner p) ≤ 1
    rw [EJACorner.val_one]; exact eja_idem_le_one p.idem

@[simp] theorem cornerVal_apply (E : EJAPsu.{u}) (p : EJAIdem E.carrier) (y : EJACorner p) :
    (cornerVal E p).toLinearMap y = EJACorner.val y := rfl

/-- For `p = 1`, the corestriction `E → E₁(1)`. -/
def cornerMk (E : EJAPsu.{u}) (p : EJAIdem E.carrier) (hp : p.elt = 1) :
    E ⟶ EJAPsu.of (EJACorner p) where
  toLinearMap :=
    { toFun := fun x => EJACorner.mk' x (by rw [hp, eja_one_mul])
      map_add' := fun x y => EJACorner.val_injective (by simp)
      map_smul' := fun r x => EJACorner.val_injective (by simp) }
  map_nonneg' x hx := (eja_corner_nonneg_iff _ _).mpr (by simpa using hx)
  map_subunital' := le_of_eq (EJACorner.val_injective (by simp [hp]))

@[simp] theorem cornerMk_val (E : EJAPsu.{u}) (p : EJAIdem E.carrier) (hp : p.elt = 1)
    (x : E.carrier) : EJACorner.val ((cornerMk E p hp).toLinearMap x) = x := rfl

theorem cornerMk_val_comp (E : EJAPsu.{u}) (p : EJAIdem E.carrier) (hp : p.elt = 1) :
    cornerMk E p hp ≫ cornerVal E p = 𝟙 E := ejapsu_hom_ext fun _ => rfl

theorem cornerVal_mk_comp (E : EJAPsu.{u}) (p : EJAIdem E.carrier) (hp : p.elt = 1) :
    cornerVal E p ≫ cornerMk E p hp = 𝟙 _ :=
  ejapsu_hom_ext fun _ => EJACorner.val_injective rfl

theorem ejapsu_id_apply (A : EJAPsu.{u}) (x : A.carrier) : (𝟙 A : A ⟶ A).toLinearMap x = x := rfl

theorem ejapsu_inv_apply {A B : EJAPsu.{u}} {φ : A ⟶ B} {ψ : B ⟶ A} (h : φ ≫ ψ = 𝟙 A)
    (x : A.carrier) : ψ.toLinearMap (φ.toLinearMap x) = x := by
  have := congrArg (fun m : A ⟶ A => m.toLinearMap x) h
  simpa [ejapsu_comp_apply, ejapsu_id_apply] using this

/-- An isomorphism of `EJA_psu` is unital. -/
theorem ejapsu_iso_unital {A B : EJAPsu.{u}} {φ : A ⟶ B} {ψ : B ⟶ A} (h1 : φ ≫ ψ = 𝟙 A)
    (h2 : ψ ≫ φ = 𝟙 B) : φ.toLinearMap 1 = 1 := by
  have hψ1 : ψ.toLinearMap 1 = 1 := by
    refine le_antisymm ψ.map_subunital' ?_
    have := ψ.mono φ.map_subunital'
    rwa [ejapsu_inv_apply h1] at this
  rw [← hψ1, ejapsu_inv_apply h2]

/-- An isomorphism is a corner for `1`. -/
theorem isCorner_one_of_iso {E C : EJAPsu.{u}} {π : E ⟶ C} {π' : C ⟶ E} (h1 : π ≫ π' = 𝟙 E)
    (h2 : π' ≫ π = 𝟙 C) : IsCorner (1 : E.carrier) π := by
  refine ⟨rfl, fun F g _ => ⟨π' ≫ g, by dsimp only; rw [← Category.assoc, h1, Category.id_comp], ?_⟩⟩
  intro k hk
  rw [← hk, ← Category.assoc, h2, Category.id_comp]

/-- A corner for `1` is an isomorphism. -/
theorem iso_of_isCorner_one {E C : EJAPsu.{u}} {π : E ⟶ C} (h : IsCorner (1 : E.carrier) π) :
    ∃ π' : C ⟶ E, π ≫ π' = 𝟙 E ∧ π' ≫ π = 𝟙 C := by
  obtain ⟨π', hπ', _⟩ := h.2 E (𝟙 E) rfl
  refine ⟨π', hπ', ?_⟩
  obtain ⟨k, _, hk⟩ := h.2 C π rfl
  have e1 := hk (π' ≫ π) (by dsimp only; rw [← Category.assoc, hπ', Category.id_comp])
  have e2 := hk (𝟙 C) (Category.comp_id π)
  rw [e1, e2]

/-- Two filters for the same effect differ by an isomorphism. -/
theorem filter_iso {E C D : EJAPsu.{u}} {q : E.carrier} {ξ : C ⟶ E} {σ : D ⟶ E}
    (hξ : IsFilter q ξ) (hσ : IsFilter q σ) :
    ∃ (θ : C ⟶ D) (θ' : D ⟶ C), θ ≫ σ = ξ ∧ θ ≫ θ' = 𝟙 C ∧ θ' ≫ θ = 𝟙 D := by
  obtain ⟨θ, hθ, _⟩ := hσ.2 C ξ hξ.1
  obtain ⟨θ', hθ', _⟩ := hξ.2 D σ hσ.1
  refine ⟨θ, θ', hθ, ?_, ?_⟩
  · obtain ⟨_, _, hu⟩ := hξ.2 C ξ hξ.1
    rw [hu (θ ≫ θ') (by dsimp only; rw [Category.assoc, hθ', hθ]), hu (𝟙 C) (Category.id_comp ξ)]
  · obtain ⟨_, _, hu⟩ := hσ.2 D σ hσ.1
    rw [hu (θ' ≫ θ) (by dsimp only; rw [Category.assoc, hθ, hθ']), hu (𝟙 D) (Category.id_comp σ)]

/-- **EJA 38, first part of the printed proof** (main.tex:817–850, valid): a
faithful pure ⋄-self-adjoint `f : E → E` is `Q_{√f(1)} ∘ Θ` for a unital Jordan
automorphism `Θ`, and `⌈f(1)⌉ = 1`.  By the universal properties the corner
of `f` is an isomorphism (faithfulness forces its effect to be `1`) and its
filter is the standard filter `ξ_{f(1)}` up to isomorphism (EJA 25); `⌈f(1)⌉ =
f^⋄(1) = f_⋄(1) = im f = 1`; the resulting unital order isomorphism is Jordan
(EJA 36). -/
theorem eja38_decomp {E : EJAPsu.{u}} (f : E ⟶ E) (hpure : IsPure f)
    (hfaith : ∀ a : E.carrier, 0 ≤ a → f.toLinearMap a = 0 → a = 0)
    (hsa : IsDiaSA f.toLinearMap) :
    ∃ Θ : E.carrier ≃ₗ[ℝ] E.carrier, IsJordanIso Θ ∧ ejaCeil (f.toLinearMap 1) = 1 ∧
      ∀ x, f.toLinearMap x = ejaU (ejaSqrt (f.toLinearMap 1)) (Θ x) := by
  obtain ⟨C, q, q', π, ξ, ⟨hq0, hq1⟩, ⟨hq'0, hq'1⟩, hπ, hξ, hf⟩ := hpure
  have hfpos : IsPositiveMap f.toLinearMap := f.map_nonneg'
  -- the corner is for `1`
  have hq : q = 1 := by
    have h0 : (0 : E.carrier) ≤ 1 - q := eja_sub_nonneg.mpr hq1
    have := hfaith _ h0 (by
      rw [hf, ejapsu_comp_apply, map_sub, map_sub, hπ.1, sub_self])
    exact (sub_eq_zero.mp this).symm
  subst hq
  obtain ⟨π', hππ', hπ'π⟩ := iso_of_isCorner_one hπ
  -- the filter is the standard one
  obtain ⟨hσ1, hσ⟩ := stdFilter_isFilter E hq'0 hq'1
  obtain ⟨θ, θ', hθσ, hθθ', hθ'θ⟩ := filter_iso hξ hσ
  have hf1 : f.toLinearMap 1 = q' := by
    rw [hf, ejapsu_comp_apply, ejapsu_iso_unital hππ' hπ'π, ← hθσ, ejapsu_comp_apply,
      ejapsu_iso_unital hθθ' hθ'θ, hσ1]
  -- `⌈f(1)⌉ = 1`
  have hceil : ejaCeil (f.toLinearMap 1) = 1 := by
    have h := hsa 1 (eja_mul_one 1)
    rw [diaUp, diaDown, ejaU_one, LinearMap.id_comp] at h
    rw [h]
    exact (faithful_iff_im _ hfpos).mp hfaith
  have hc : (ceilIdem q').elt = 1 := by rw [← hf1]; exact hceil
  -- the automorphism
  set κ := cornerMk E (ceilIdem q') hc
  let Φ : E ⟶ E := π ≫ θ ≫ cornerVal E (ceilIdem q')
  let Φ' : E ⟶ E := κ ≫ θ' ≫ π'
  have hΦΦ' : Φ ≫ Φ' = 𝟙 E := by
    simp only [Φ, Φ', Category.assoc]
    rw [← Category.assoc (cornerVal E _), cornerVal_mk_comp, Category.id_comp,
      ← Category.assoc θ, hθθ', Category.id_comp, hππ']
  have hΦ'Φ : Φ' ≫ Φ = 𝟙 E := by
    simp only [Φ, Φ', Category.assoc]
    rw [← Category.assoc π', hπ'π, Category.id_comp, ← Category.assoc θ', hθ'θ,
      Category.id_comp, cornerMk_val_comp]
  let Θ : E.carrier ≃ₗ[ℝ] E.carrier :=
    { Φ.toLinearMap with
      invFun := Φ'.toLinearMap
      left_inv := fun x => ejapsu_inv_apply hΦΦ' x
      right_inv := fun y => ejapsu_inv_apply hΦ'Φ y }
  have hΘ1 : Θ 1 = 1 := ejapsu_iso_unital hΦΦ' hΦ'Φ
  have hΘpos : ∀ x, 0 ≤ Θ x ↔ 0 ≤ x := by
    intro x
    refine ⟨fun h => ?_, fun h => Φ.map_nonneg' x h⟩
    have := Φ'.map_nonneg' _ h
    rwa [show Φ'.toLinearMap (Θ x) = x from ejapsu_inv_apply hΦΦ' x] at this
  refine ⟨Θ, unital_order_iso_jordan Θ hΘ1 hΘpos, hceil, fun x => ?_⟩
  rw [hf1, hf, ejapsu_comp_apply, ← hθσ, ejapsu_comp_apply, stdFilter_apply]
  rfl

end Decomp

/-! ## EJA 38′ and EJA 39 -/

section Lemma38Main

/-- EJA 38′ with the frame data (used by EJA 39). -/
theorem eja38'_frame {E : EJAPsu.{u}} (f : E ⟶ E) (hpure : IsPure f)
    (hfaith : ∀ a : E.carrier, 0 ≤ a → f.toLinearMap a = 0 → a = 0)
    (hsa : IsDiaSA f.toLinearMap) :
    ∃ Θ : E.carrier ≃ₗ[ℝ] E.carrier, IsJordanIso Θ ∧
      (∀ x, f.toLinearMap x = ejaU (ejaSqrt (f.toLinearMap 1)) (Θ x)) ∧
      (∃ (ι : Type) (_ : Fintype ι) (r : ι → E.carrier) (a b : ι → ℝ),
        (∀ i, EJAPrimitive (r i)) ∧ IsOrthFrame r ∧ (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
        ejaSqrt (f.toLinearMap 1) = ∑ i, a i • r i ∧ Θ (ejaSqrt (f.toLinearMap 1)) = ∑ i, b i • r i) ∧
      (∀ x, ejaSqrt (f.toLinearMap 1) * (Θ (ejaSqrt (f.toLinearMap 1)) * x)
          = Θ (ejaSqrt (f.toLinearMap 1)) * (ejaSqrt (f.toLinearMap 1) * x)) ∧
      (∀ x, Θ (Θ x) = x) := by
  obtain ⟨Θ, hΘ, _, hfac⟩ := eja38_decomp f hpure hfaith hsa
  have hfpos : IsPositiveMap f.toLinearMap := f.map_nonneg'
  set q := ejaSqrt (f.toLinearMap 1) with hqdef
  have hq : 0 ≤ q := (ejaSqrt_spec (hfpos 1 (eja_idem_nonneg (eja_mul_one 1)))).1
  have hqf : ∀ x, 0 ≤ x → ejaU q x = 0 → x = 0 := by
    intro x hx h
    have hy : 0 ≤ Θ.symm x := hΘ.symm.nonneg hx
    have := hfaith _ hy (by rw [hfac, LinearEquiv.apply_symm_apply]; exact h)
    rw [← LinearEquiv.apply_symm_apply Θ x, this, map_zero]
  have hZ : ∀ s, s * s = s → ∀ t, t * t = t → (t * ejaU q (Θ s) = 0 ↔ s * ejaU q (Θ t) = 0) := by
    intro s hs t ht
    rw [← hfac, ← hfac]
    exact (diaSA_iff hfpos f.map_subunital').mp hsa s hs t ht
  obtain ⟨hfr, hcomm, hinv⟩ := eja38'_core hq hqf hΘ hZ
  exact ⟨Θ, hΘ, hfac, hfr, hcomm, hinv⟩

/-- **EJA 38′** (repair of EJA 38, main.tex:815, Lemma; see
`eja38_false_as_printed`): a faithful pure ⋄-self-adjoint `f : E → E` is
`f = Q_{√f(1)} ∘ Θ` for a unital Jordan isomorphism `Θ` with `Θ = Θ⁻¹`, such that
`Θ(√f(1))` **operator-commutes** with `√f(1)` (the print claims `Θ(√f(1)) =
√f(1)`, which is false). -/
theorem eja38' {E : EJAPsu.{u}} (f : E ⟶ E) (hpure : IsPure f)
    (hfaith : ∀ a : E.carrier, 0 ≤ a → f.toLinearMap a = 0 → a = 0)
    (hsa : IsDiaSA f.toLinearMap) :
    ∃ Θ : E.carrier ≃ₗ[ℝ] E.carrier, IsJordanIso Θ ∧
      (∀ x, f.toLinearMap x = ejaU (ejaSqrt (f.toLinearMap 1)) (Θ x)) ∧
      (∀ x, ejaSqrt (f.toLinearMap 1) * (Θ (ejaSqrt (f.toLinearMap 1)) * x)
          = Θ (ejaSqrt (f.toLinearMap 1)) * (ejaSqrt (f.toLinearMap 1) * x)) ∧
      (∀ x, Θ (Θ x) = x) := by
  obtain ⟨Θ, hΘ, hfac, _, hcomm, hinv⟩ := eja38'_frame f hpure hfaith hsa
  exact ⟨Θ, hΘ, hfac, hcomm, hinv⟩

/-- **EJA 39** (main.tex:891, Proposition), with the ⋄-self-adjoint root pure: if
`g` is faithful and pure, and `g = f ∘ f` for a **pure** ⋄-self-adjoint `f`,
then `g = Q_{√g(1)}`.  The print's Def 32 does not ask the root of a
⋄-positive map to be pure, but its proof of 39 uses it (PLAN §2, "B15
recurs").  The printed proof goes through the false clause `Θ(q) = q` of EJA 38
(`g = Q_{q²}`); from EJA 38′ instead `g = Q_q Q_{Θq} Θ² = Q_{q·Θq}` (one frame),
so `√g(1) = q·Θq`. -/
theorem eja39 {E : EJAPsu.{u}} (g : E ⟶ E) (_hgpure : IsPure g)
    (hg : ∀ a : E.carrier, 0 ≤ a → g.toLinearMap a = 0 → a = 0)
    (hpos : ∃ f : E ⟶ E, IsPure f ∧ IsDiaSA f.toLinearMap ∧ g = f ≫ f) :
    ∀ x, g.toLinearMap x = ejaU (ejaSqrt (g.toLinearMap 1)) x := by
  obtain ⟨f, hfpure, hfsa, rfl⟩ := hpos
  have hfaith : ∀ a : E.carrier, 0 ≤ a → f.toLinearMap a = 0 → a = 0 := by
    intro a ha h
    exact hg a ha (by rw [ejapsu_comp_apply, h, map_zero])
  obtain ⟨Θ, hΘ, hfac, ⟨ι, _, r, a, b, _, hr, ha, hb, hqa, hΘq⟩, _, hinv⟩ :=
    eja38'_frame f hfpure hfaith hfsa
  set q := ejaSqrt (f.toLinearMap 1)
  have hg' : ∀ x, (f ≫ f).toLinearMap x = ejaU (∑ i, (a i * b i) • r i) x := by
    intro x
    rw [ejapsu_comp_apply, hfac, hfac, hΘ.map_U, hinv, hΘq, hqa, frame_U_comp hr]
  have hg1 : (f ≫ f).toLinearMap 1 = (∑ i, (a i * b i) • r i) * (∑ i, (a i * b i) • r i) := by
    rw [hg', ejaU_apply_one]
  have hsq : ejaSqrt ((f ≫ f).toLinearMap 1) = ∑ i, (a i * b i) • r i :=
    ejaSqrt_unique (frame_nonneg hr fun i => (mul_pos (ha i) (hb i)).le) hg1.symm
  intro x
  rw [hsq, hg']

end Lemma38Main

/-! ## EJA 38 is false as printed -/

section Counterexample38

/-- The map `f(x, y) = (y/4, x)` on `ℝ ⊕ ℝ`: `f = Q_q ∘ swap` with `q = (1/2, 1)`. -/
noncomputable def ex38Lin : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun x := ((1 / 4 : ℝ) * x.2, x.1)
  map_add' x y := by ext <;> simp; ring
  map_smul' r x := by ext <;> simp; ring

theorem prod_nonneg_iff (x : ℝ × ℝ) : 0 ≤ x ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 := Prod.le_def

/-- The counterexample, as a morphism of `EJA_psu`. -/
noncomputable def ex38 : EJAPsu.of (ℝ × ℝ) ⟶ EJAPsu.of (ℝ × ℝ) where
  toLinearMap := ex38Lin
  map_nonneg' x hx := by
    rw [prod_nonneg_iff] at hx ⊢
    exact ⟨by simp [ex38Lin]; linarith [hx.2], by simpa [ex38Lin] using hx.1⟩
  map_subunital' := by
    show ex38Lin 1 ≤ 1
    rw [Prod.le_def]; simp [ex38Lin]; norm_num

theorem ex38_apply (x : ℝ × ℝ) : ex38.toLinearMap x = ((1 / 4 : ℝ) * x.2, x.1) := rfl

/-- The swap of `ℝ ⊕ ℝ`, a unital order automorphism. -/
noncomputable def swapHom : EJAPsu.of (ℝ × ℝ) ⟶ EJAPsu.of (ℝ × ℝ) where
  toLinearMap := (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
  map_nonneg' x hx := by
    rw [prod_nonneg_iff] at hx ⊢; exact ⟨hx.2, hx.1⟩
  map_subunital' := le_of_eq rfl

theorem swapHom_swapHom : swapHom ≫ swapHom = 𝟙 _ := ejapsu_hom_ext fun _ => rfl

/-- `q₂ = f(1) = (1/4, 1)`. -/
noncomputable abbrev ex38q : ℝ × ℝ := ((1 / 4 : ℝ), 1)

theorem ex38q_nonneg : (0 : ℝ × ℝ) ≤ ex38q := by rw [prod_nonneg_iff]; norm_num

theorem ex38q_le_one : ex38q ≤ 1 := by rw [Prod.le_def]; norm_num

theorem ex38_sqrt : ejaSqrt ex38q = ((1 / 2 : ℝ), (1 : ℝ)) :=
  ejaSqrt_unique (by rw [prod_nonneg_iff]; norm_num) (by ext <;> simp <;> norm_num)

theorem ex38_ceil : ejaCeil ex38q = 1 := by
  refine ejaCeil_of_least ⟨eja_mul_one 1, ex38q_le_one, fun p hp hle => ?_⟩
  have h1 : p.1 * p.1 = p.1 := congrArg Prod.fst hp
  have h2 : p.2 * p.2 = p.2 := congrArg Prod.snd hp
  rw [Prod.le_def] at hle ⊢
  simp only [Prod.fst_one, Prod.snd_one] at hle ⊢
  have hp1 : p.1 = 1 := by
    rcases mul_eq_zero.mp (show p.1 * (p.1 - 1) = 0 by linarith) with h | h
    · linarith [hle.1]
    · linarith
  have hp2 : p.2 = 1 := by
    rcases mul_eq_zero.mp (show p.2 * (p.2 - 1) = 0 by linarith) with h | h
    · linarith [hle.2]
    · linarith
  exact ⟨hp1.ge, hp2.ge⟩

theorem ejaU_prod (a y : ℝ × ℝ) : ejaU a y = (a.1 * a.1 * y.1, a.2 * a.2 * y.2) := by
  rw [ejaU_apply]; ext <;> simp <;> ring

theorem ex38_isPure : IsPure ex38 := by
  set E := EJAPsu.of (ℝ × ℝ)
  have hc : (ceilIdem (V := ℝ × ℝ) ex38q).elt = 1 := ex38_ceil
  refine ⟨filterObj E ex38q, 1, ex38q, swapHom ≫ cornerMk E _ hc,
    stdFilter E ex38q_nonneg ex38q_le_one, ⟨eja_idem_nonneg (eja_mul_one 1), le_rfl⟩,
    ⟨ex38q_nonneg, ex38q_le_one⟩, ?_, (stdFilter_isFilter E _ _).2, ?_⟩
  · refine isCorner_one_of_iso (π' := cornerVal E _ ≫ swapHom) ?_ ?_
    · rw [Category.assoc, ← Category.assoc (cornerMk E _ hc), cornerMk_val_comp,
        Category.id_comp, swapHom_swapHom]
    · rw [Category.assoc, ← Category.assoc swapHom, swapHom_swapHom, Category.id_comp,
        cornerVal_mk_comp]
  · refine ejapsu_hom_ext fun x => ?_
    rw [ejapsu_comp_apply, ejapsu_comp_apply, stdFilter_apply, cornerMk_val, ex38_sqrt,
      ejaU_prod, ex38_apply]
    exact Prod.ext (by show (1 / 4 : ℝ) * x.2 = 1 / 2 * (1 / 2) * x.2; ring)
      (by show x.1 = 1 * 1 * x.1; ring)

theorem ex38_faithful (a : ℝ × ℝ) (_ : 0 ≤ a) (h : ex38.toLinearMap a = 0) : a = 0 := by
  rw [ex38_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp at h1 h2
  ext <;> simp [h1, h2]

theorem ex38_diaSA : IsDiaSA ex38.toLinearMap := by
  rw [diaSA_iff ex38.map_nonneg' ex38.map_subunital']
  intro s _ t _
  change t * ((1 / 4 : ℝ) * s.2, s.1) = 0 ↔ s * ((1 / 4 : ℝ) * t.2, t.1) = 0
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_zero,
    Prod.snd_zero, mul_eq_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  tauto

/-- **EJA 38 as printed** (main.tex:815, Lemma): a faithful pure ⋄-self-adjoint
`f : E → E` is `Q_{√f(1)} ∘ Θ` for a unital Jordan isomorphism `Θ` with
`Θ(√f(1)) = √f(1)` and `Θ = Θ⁻¹`. -/
def Lemma38AsPrinted : Prop :=
  ∀ (E : EJAPsu.{0}) (f : E ⟶ E), IsPure f →
    (∀ a : E.carrier, 0 ≤ a → f.toLinearMap a = 0 → a = 0) → IsDiaSA f.toLinearMap →
    ∃ Θ : E.carrier ≃ₗ[ℝ] E.carrier, IsJordanIso Θ ∧
      (∀ x, f.toLinearMap x = ejaU (ejaSqrt (f.toLinearMap 1)) (Θ x)) ∧
      Θ (ejaSqrt (f.toLinearMap 1)) = ejaSqrt (f.toLinearMap 1) ∧ (∀ x, Θ (Θ x) = x)

/-- **EJA 38 is false as printed**: on `ℝ ⊕ ℝ`, `f(x, y) = (y/4, x)` is pure
(`Q_{(1/2,1)}` is the standard filter of `f(1) = (1/4, 1)`, the swap a corner
for `1`), faithful and ⋄-self-adjoint, but no `Θ` with `f = Q_{√f(1)} ∘ Θ`
fixes `√f(1) = (1/2, 1)`: that would give `f(√f(1)) = √f(1)³ = (1/8, 1)`,
while `f(1/2, 1) = (1/4, 1/2)`.  (EJA 38′ is the repair.) -/
theorem eja38_false_as_printed : ¬ Lemma38AsPrinted := by
  intro h
  obtain ⟨Θ, _, hfac, hfix, _⟩ := h _ ex38 ex38_isPure ex38_faithful ex38_diaSA
  have h1 : ex38.toLinearMap 1 = ex38q := by
    rw [ex38_apply]; ext <;> simp
  have h2 := hfac (ejaSqrt (ex38.toLinearMap 1))
  rw [hfix, h1, ex38_sqrt, ex38_apply, ejaU_prod] at h2
  have h3 := congrArg Prod.snd h2
  norm_num at h3

end Counterexample38

/-! ## EJA 34: pure ⋄-positive maps -/

section Thm34

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

theorem val_ejaU {p : EJAIdem V} (a y : EJACorner p) :
    EJACorner.val (ejaU a y) = ejaU (EJACorner.val a) (EJACorner.val y) := by
  simp [ejaU_apply]

/-- For an idempotent `p` and an effect `e`: `P₁(p) e = p ⟺ p ≤ e`. -/
theorem pone_eq_self_iff_le {p e : V} (hp : p * p = p) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ejaPone p e = p ↔ p ≤ e := by
  have h0 : (0 : V) ≤ 1 - e := eja_sub_nonneg.mpr he1
  rw [idem_le_effect_iff hp he0 he1, idem_mul_eq_zero_iff_ejaB h0 hp, ejaB_symm,
    ← ejaU_idem hp]
  have h1 := idem_Q_eq_zero_iff (EJAForm.trace V) hp h0
  change ejaU p (1 - e) = 0 ↔ ejaB (1 - e) p = 0 at h1
  rw [ejaB_symm] at h1
  rw [← h1, map_sub, ejaU_apply_one, hp, sub_eq_zero, eq_comm]

/-- `z * t = 0` for `z ≥ 0` and an idempotent `t` with `(z * z) * t = 0`. -/
theorem mul_idem_eq_zero_of_sq {z t : V} (hz : 0 ≤ z) (ht : t * t = t) (h : t * (z * z) = 0) :
    t * z = 0 := by
  have hzz : 0 ≤ z * z := (eja_nonneg_iff _).mpr (IsSumSq.mul_self z)
  have h1 : ejaB (z * z) t = 0 := (idem_mul_eq_zero_iff_ejaB hzz ht).mp h
  have h2 : ejaB (ejaU z t) 1 = 0 := by
    rw [← ejaB_U_self_adj, ejaU_apply_one, ejaB_symm]; exact h1
  have h3 : ejaU z t = 0 := by
    have := (idem_mul_eq_zero_iff_ejaB (eja_U_nonneg' z (eja_idem_nonneg ht)) (eja_mul_one 1)).mpr h2
    rwa [eja_one_mul] at this
  have h4 := ((eja_Q_eq_zero_iff_mul_eq_zero hz (eja_idem_nonneg ht)).1.trans
    (eja_Q_eq_zero_iff_mul_eq_zero hz (eja_idem_nonneg ht)).2).mp h3
  rw [eja_mul_comm]; exact h4

/-- `√q ∈ E₁(⌈q⌉)` for an effect `q`. -/
theorem ceil_mul_sqrt {q : V} (h0 : 0 ≤ q) (h1 : q ≤ 1) : ejaCeil q * ejaSqrt q = ejaSqrt q := by
  obtain ⟨hs0, hss⟩ := ejaSqrt_spec h0
  have hc := ejaCeil_idem q
  have hcq := ejaCeil_mul h0 h1
  have h := mul_idem_eq_zero_of_sq hs0 (eja_one_sub_idem hc) (by
    rw [hss, eja_sub_mul, eja_one_mul, hcq, sub_self])
  rw [eja_sub_mul, eja_one_mul, sub_eq_zero] at h
  exact h.symm

end Thm34

section Thm34Main

/-- Two corners for the same effect differ by an isomorphism. -/
theorem corner_iso {E C D : EJAPsu.{u}} {b : E.carrier} {π : E ⟶ C} {ρ : E ⟶ D}
    (hπ : IsCorner b π) (hρ : IsCorner b ρ) :
    ∃ (ι : D ⟶ C) (ι' : C ⟶ D), ρ ≫ ι = π ∧ ι ≫ ι' = 𝟙 D ∧ ι' ≫ ι = 𝟙 C := by
  obtain ⟨ι, hι, _⟩ := hρ.2 C π hπ.1
  obtain ⟨ι', hι', _⟩ := hπ.2 D ρ hρ.1
  refine ⟨ι, ι', hι, ?_, ?_⟩
  · obtain ⟨_, _, hu⟩ := hρ.2 D ρ hρ.1
    rw [hu (ι ≫ ι') (by dsimp only; rw [← Category.assoc, hι, hι']),
      hu (𝟙 D) (Category.comp_id ρ)]
  · obtain ⟨_, _, hu⟩ := hπ.2 C π hπ.1
    rw [hu (ι' ≫ ι) (by dsimp only; rw [← Category.assoc, hι', hι]),
      hu (𝟙 C) (Category.comp_id π)]

/-- Corners at idempotents with the same element are isomorphic. -/
def cornerCast (E : EJAPsu.{u}) (p p' : EJAIdem E.carrier) (h : p.elt = p'.elt) :
    EJAPsu.of (EJACorner p) ⟶ EJAPsu.of (EJACorner p') where
  toLinearMap :=
    { toFun := fun y => EJACorner.mk' (EJACorner.val y) (by rw [← h]; exact EJACorner.val_prop y)
      map_add' := fun x y => EJACorner.val_injective (by simp)
      map_smul' := fun r x => EJACorner.val_injective (by simp) }
  map_nonneg' y hy := (eja_corner_nonneg_iff _ _).mpr (by simpa using eja_corner_val_nonneg hy)
  map_subunital' := le_of_eq (EJACorner.val_injective (by simp [h]))

@[simp] theorem cornerCast_val (E : EJAPsu.{u}) (p p' : EJAIdem E.carrier) (h : p.elt = p'.elt)
    (y : EJACorner p) : EJACorner.val ((cornerCast E p p' h).toLinearMap y) = EJACorner.val y := rfl

theorem cornerCast_comp (E : EJAPsu.{u}) (p p' : EJAIdem E.carrier) (h : p.elt = p'.elt) :
    cornerCast E p p' h ≫ cornerCast E p' p h.symm = 𝟙 _ :=
  ejapsu_hom_ext fun _ => EJACorner.val_injective rfl

/-- **The decomposition of a pure ⋄-self-adjoint map** (main.tex, proof of EJA
34 and first part of the proof of EJA 38, without faithfulness): with
`s = ⌈f(1)⌉`, `f = Q_{√f(1)} ∘ ι ∘ Θ ∘ π_s` for a unital Jordan automorphism
`Θ` of the corner `E₁(s)` (`ι` its inclusion, `π_s` the compression). -/
theorem pure_diaSA_decomp {E : EJAPsu.{u}} (f : E ⟶ E) (hpure : IsPure f)
    (hsa : IsDiaSA f.toLinearMap) :
    ∃ Θ : EJACorner (ceilIdem (f.toLinearMap 1)) ≃ₗ[ℝ] EJACorner (ceilIdem (f.toLinearMap 1)),
      IsJordanIso Θ ∧ ∀ x, f.toLinearMap x = ejaU (ejaSqrt (f.toLinearMap 1))
        (EJACorner.val (Θ (ejaPoneCorner (ceilIdem (f.toLinearMap 1)) x))) := by
  obtain ⟨C, b, q', π, ξ, ⟨hb0, hb1⟩, ⟨hq'0, hq'1⟩, hπ, hξ, hf⟩ := hpure
  have hfpos : IsPositiveMap f.toLinearMap := f.map_nonneg'
  obtain ⟨hσ1, hσ⟩ := stdFilter_isFilter E hq'0 hq'1
  obtain ⟨θ, θ', hθσ, hθθ', hθ'θ⟩ := filter_iso hξ hσ
  obtain ⟨ι, ι', hρι, hιι', hι'ι⟩ := corner_iso hπ (stdCorner_isCorner E hb0 hb1)
  set σ := stdFilter E hq'0 hq'1
  set ρ := stdCorner E b
  have hfac : f = ρ ≫ ι ≫ θ ≫ σ := by rw [hf, ← hρι, ← hθσ]; simp only [Category.assoc]
  have hρ1 : ρ.toLinearMap 1 = 1 := EJACorner.val_injective (by
    rw [stdCorner_val, eja_pone_one _ (ejaFloor_idem b)]; rfl)
  have hf1 : f.toLinearMap 1 = q' := by
    rw [hfac, ejapsu_comp_apply, ejapsu_comp_apply, ejapsu_comp_apply, hρ1,
      ejapsu_iso_unital hιι' hι'ι, ejapsu_iso_unital hθθ' hθ'θ, hσ1]
  -- the standard filter is injective
  have hσinj : Function.Injective σ.toLinearMap := by
    obtain ⟨b', _, hU'U, _, _⟩ := filter_data hq'0 hq'1
    intro y y' h
    apply EJACorner.val_injective
    have h1 := congrArg (ejaU b') h
    rw [stdFilter_apply, stdFilter_apply, hU'U, hU'U,
      (eja_pone_eq_self_iff _ (ejaCeil_idem q') _).mpr (EJACorner.val_prop y),
      (eja_pone_eq_self_iff _ (ejaCeil_idem q') _).mpr (EJACorner.val_prop y')] at h1
    exact h1
  have hrestinj : ∀ y y', (ι ≫ θ ≫ σ).toLinearMap y = (ι ≫ θ ≫ σ).toLinearMap y' → y = y' := by
    intro y y' h
    simp only [ejapsu_comp_apply] at h
    have h2 := hσinj h
    have h3 := congrArg θ'.toLinearMap h2
    rw [ejapsu_inv_apply hθθ', ejapsu_inv_apply hθθ'] at h3
    have h4 := congrArg ι'.toLinearMap h3
    rwa [ejapsu_inv_apply hιι', ejapsu_inv_apply hιι'] at h4
  -- `im f = ⌊b⌋`
  have himf : IsImageOf f.toLinearMap (ejaFloor b) := by
    have hfl := ejaFloor_idem b
    have key : ∀ e : E.carrier, 0 ≤ e → e ≤ 1 → (f.toLinearMap e = f.toLinearMap 1 ↔ ejaFloor b ≤ e) := by
      intro e he0 he1
      rw [hfac, ejapsu_comp_apply, ejapsu_comp_apply (f := ρ)]
      constructor
      · intro h
        have h2 := congrArg EJACorner.val (hrestinj _ _ h)
        rw [stdCorner_val, stdCorner_val, eja_pone_one _ hfl] at h2
        exact (pone_eq_self_iff_le hfl he0 he1).mp h2
      · intro h
        congr 1
        apply EJACorner.val_injective
        rw [stdCorner_val, stdCorner_val, eja_pone_one _ hfl]
        exact (pone_eq_self_iff_le hfl he0 he1).mpr h
    exact ⟨⟨eja_idem_nonneg hfl, eja_idem_le_one hfl⟩,
      (key _ (eja_idem_nonneg hfl) (eja_idem_le_one hfl)).mpr le_rfl,
      fun e he0 he1 he => (key e he0 he1).mp he⟩
  have hceil : ejaCeil q' = ejaFloor b := by
    have h := hsa 1 (eja_mul_one 1)
    rw [diaUp, diaDown, ejaU_one, LinearMap.id_comp, hf1] at h
    rw [h]
    exact (ejaIm_spec hfpos).2.unique himf
  subst hf1
  set s := ceilIdem (f.toLinearMap 1)
  have hsb : s.elt = (floorIdem b).elt := hceil
  -- the automorphism of the corner
  let Φ : EJAPsu.of (EJACorner s) ⟶ EJAPsu.of (EJACorner s) :=
    cornerCast E s (floorIdem b) hsb ≫ ι ≫ θ
  let Φ' : EJAPsu.of (EJACorner s) ⟶ EJAPsu.of (EJACorner s) :=
    θ' ≫ ι' ≫ cornerCast E (floorIdem b) s hsb.symm
  have hΦΦ' : Φ ≫ Φ' = 𝟙 _ := by
    simp only [Φ, Φ', Category.assoc]
    rw [← Category.assoc θ θ', hθθ', Category.id_comp, ← Category.assoc ι ι', hιι',
      Category.id_comp, cornerCast_comp]
  have hΦ'Φ : Φ' ≫ Φ = 𝟙 _ := by
    simp only [Φ, Φ', Category.assoc]
    rw [← Category.assoc (cornerCast E _ _ _) (cornerCast E _ _ _), cornerCast_comp,
      Category.id_comp, ← Category.assoc ι' ι, hι'ι, Category.id_comp, hθ'θ]
  let Θ : EJACorner s ≃ₗ[ℝ] EJACorner s :=
    { Φ.toLinearMap with
      invFun := Φ'.toLinearMap
      left_inv := fun x => ejapsu_inv_apply hΦΦ' x
      right_inv := fun y => ejapsu_inv_apply hΦ'Φ y }
  have hΘ1 : Θ 1 = 1 := ejapsu_iso_unital hΦΦ' hΦ'Φ
  have hΘpos : ∀ x, 0 ≤ Θ x ↔ 0 ≤ x := by
    intro x
    refine ⟨fun h => ?_, fun h => Φ.map_nonneg' x h⟩
    have := Φ'.map_nonneg' _ h
    rwa [show Φ'.toLinearMap (Θ x) = x from ejapsu_inv_apply hΦΦ' x] at this
  refine ⟨Θ, unital_order_iso_jordan Θ hΘ1 hΘpos, fun x => ?_⟩
  have hρx : ρ.toLinearMap x
      = (cornerCast E s (floorIdem b) hsb).toLinearMap (ejaPoneCorner s x) :=
    EJACorner.val_injective (by
      rw [stdCorner_val, cornerCast_val, ejaPoneCorner_val]
      show ejaPone (ejaFloor b) x = ejaPone (ejaCeil (f.toLinearMap 1)) x
      rw [hceil])
  have h1 : f.toLinearMap x
      = σ.toLinearMap (θ.toLinearMap (ι.toLinearMap (ρ.toLinearMap x))) :=
    (congrArg (fun m : E ⟶ E => m.toLinearMap x) hfac).trans rfl
  rw [h1, stdFilter_apply, hρx]
  rfl

end Thm34Main

section Thm34Main2

/-- **EJA 34** (`super-duper-theorem`, main.tex:775, Theorem), with the
⋄-self-adjoint root pure (as in EJA 39): a pure ⋄-positive `g` is `Q_{√g(1)}`.
The paper corestricts to `E₁(im f)` and applies EJA 39 there, using that pure
maps compose (EJA 31) for the purity of the corestriction; here the
decomposition `f = Q_{√f(1)} ∘ ι ∘ Θ ∘ π_s` (`pure_diaSA_decomp`) is used
directly, and EJA 38′ is applied to `Q_{√f(1)} ∘ Θ` on the corner `E₁(s)`,
`s = ⌈f(1)⌉ = im f`.  The last step `Q_w Q_s = Q_w` for `w ∈ E₁(s)` uses the
fundamental formula (`ejaU_ejaU`). -/
theorem super_duper_theorem {E : EJAPsu.{u}} (g : E ⟶ E) (_hgpure : IsPure g)
    (hpos : ∃ f : E ⟶ E, IsPure f ∧ IsDiaSA f.toLinearMap ∧ g = f ≫ f) :
    ∀ x, g.toLinearMap x = ejaU (ejaSqrt (g.toLinearMap 1)) x := by
  obtain ⟨f, hfpure, hfsa, rfl⟩ := hpos
  have hfpos : IsPositiveMap f.toLinearMap := f.map_nonneg'
  obtain ⟨Θ, hΘ, hdec⟩ := pure_diaSA_decomp f hfpure hfsa
  have hq'0 : 0 ≤ f.toLinearMap 1 := hfpos 1 (eja_idem_nonneg (eja_mul_one 1))
  have hq'1 : f.toLinearMap 1 ≤ 1 := f.map_subunital'
  have hs := (ceilIdem (f.toLinearMap 1)).idem
  have hq0 : 0 ≤ ejaSqrt (f.toLinearMap 1) := (ejaSqrt_spec hq'0).1
  have hsq : (ceilIdem (f.toLinearMap 1)).elt * ejaSqrt (f.toLinearMap 1)
      = ejaSqrt (f.toLinearMap 1) := ceil_mul_sqrt hq'0 hq'1
  let qc : EJACorner (ceilIdem (f.toLinearMap 1)) := EJACorner.mk' _ hsq
  have hqcv : EJACorner.val qc = ejaSqrt (f.toLinearMap 1) := rfl
  have hP : ∀ y : EJACorner (ceilIdem (f.toLinearMap 1)),
      ejaPoneCorner (ceilIdem (f.toLinearMap 1)) (EJACorner.val y) = y := fun y =>
    EJACorner.val_injective (by
      rw [ejaPoneCorner_val]; exact (eja_pone_eq_self_iff _ hs _).mpr (EJACorner.val_prop y))
  have hkey : ∀ y, f.toLinearMap (EJACorner.val y) = EJACorner.val (ejaU qc (Θ y)) := by
    intro y; rw [hdec, hP, val_ejaU, hqcv]
  -- zero pattern in the corner
  have hZE := (diaSA_iff hfpos f.map_subunital').mp hfsa
  have hZ : ∀ a : EJACorner (ceilIdem (f.toLinearMap 1)), a * a = a →
      ∀ t : EJACorner (ceilIdem (f.toLinearMap 1)), t * t = t →
      (t * ejaU qc (Θ a) = 0 ↔ a * ejaU qc (Θ t) = 0) := by
    intro a ha t ht
    have hva : EJACorner.val a * EJACorner.val a = EJACorner.val a := by
      rw [← EJACorner.val_mul, ha]
    have hvt : EJACorner.val t * EJACorner.val t = EJACorner.val t := by
      rw [← EJACorner.val_mul, ht]
    have h := hZE _ hva _ hvt
    rw [hkey, hkey, ← EJACorner.val_mul, ← EJACorner.val_mul] at h
    constructor
    · intro h1; apply EJACorner.val_injective
      rw [EJACorner.val_zero]; exact h.mp (by rw [h1, EJACorner.val_zero])
    · intro h1; apply EJACorner.val_injective
      rw [EJACorner.val_zero]; exact h.mpr (by rw [h1, EJACorner.val_zero])
  have hqc0 : 0 ≤ qc := (eja_corner_nonneg_iff _ _).mpr hq0
  have hqcf : ∀ y, 0 ≤ y → ejaU qc y = 0 → y = 0 := by
    intro y _ hy
    obtain ⟨b', _, hU'U, _, _⟩ := filter_data hq'0 hq'1
    have h1 := congrArg EJACorner.val hy
    rw [val_ejaU, EJACorner.val_zero, hqcv] at h1
    have h2 := congrArg (ejaU b') h1
    rw [hU'U, map_zero, (eja_pone_eq_self_iff _ (ejaCeil_idem _) _).mpr
      (EJACorner.val_prop y)] at h2
    exact EJACorner.val_injective (by rw [h2, EJACorner.val_zero])
  obtain ⟨⟨ι, _, r, a, b, _, hr, ha, hb, hqa, hΘq⟩, _, hinv⟩ := eja38'_core hqc0 hqcf hΘ hZ
  have hw0 : (0 : EJACorner (ceilIdem (f.toLinearMap 1))) ≤ ∑ i, (a i * b i) • r i :=
    frame_nonneg hr fun i => (mul_pos (ha i) (hb i)).le
  have hfc : ∀ y, ejaU qc (Θ (ejaU qc (Θ y))) = ejaU (∑ i, (a i * b i) • r i) y := by
    intro y
    rw [hΘ.map_U, hinv, hΘq, hqa, frame_U_comp hr]
  set wv := EJACorner.val (∑ i, (a i * b i) • r i) with hwv
  have hvw : (ceilIdem (f.toLinearMap 1)).elt * wv = wv := EJACorner.val_prop _
  have hUw : ∀ x, ejaU wv (ejaU (ceilIdem (f.toLinearMap 1)).elt x) = ejaU wv x := by
    intro x
    have hsw : ejaU (ceilIdem (f.toLinearMap 1)).elt wv = wv := by
      rw [ejaU_idem hs]; exact (eja_pone_eq_self_iff _ hs _).mpr hvw
    have hFF := ejaU_ejaU (ceilIdem (f.toLinearMap 1)).elt wv
    rw [hsw] at hFF
    have hss : ejaU (ceilIdem (f.toLinearMap 1)).elt (ejaU (ceilIdem (f.toLinearMap 1)).elt x)
        = ejaU (ceilIdem (f.toLinearMap 1)).elt x := by
      rw [← Module.End.mul_apply, idem_Q_idem hs]
    rw [hFF]
    simp only [Module.End.mul_apply]
    rw [hss]
  have hg : ∀ x, (f ≫ f).toLinearMap x = ejaU wv x := by
    intro x
    rw [ejapsu_comp_apply, hdec x, ← hqcv, ← val_ejaU, hkey, hfc, val_ejaU, ejaPoneCorner_val,
      ← ejaU_idem hs, hUw]
  have hg1 : ejaSqrt ((f ≫ f).toLinearMap 1) = wv := by
    refine ejaSqrt_unique (eja_corner_val_nonneg hw0) ?_
    rw [hg, ejaU_apply_one]
  intro x
  rw [hg1, hg]

end Thm34Main2

/-! ## EJA 26–27: adjoints, partial isometries, polar decomposition -/

section Polar

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- **EJA 26** (main.tex:639, Definition): `Ψ` is the adjoint `Φ*` of `Φ` with
respect to the inner product `F`: `⟨Ψ a, b⟩ = ⟨a, Φ b⟩`. -/
def IsFAdjoint (F : EJAForm V) (Φ Ψ : V →ₗ[ℝ] V) : Prop := ∀ a b, F.B (Ψ a) b = F.B a (Φ b)

/-- **EJA 26**, the adjoint exists and is unique (finite dimension; Mathlib's
`LinearMap.BilinForm.leftAdjointOfNondegenerate`). -/
theorem EJAForm.exists_adjoint (F : EJAForm V) (Φ : V →ₗ[ℝ] V) :
    ∃! Ψ : V →ₗ[ℝ] V, IsFAdjoint F Φ Ψ := by
  have hnd : LinearMap.BilinForm.Nondegenerate F.B :=
    ⟨fun x hx => F.eq_zero_of_self x (hx x),
      fun y hy => F.eq_zero_of_self y (by rw [F.symm]; exact hy y)⟩
  refine ⟨LinearMap.BilinForm.leftAdjointOfNondegenerate F.B hnd Φ,
    LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate F.B hnd Φ, fun Ψ hΨ => ?_⟩
  exact (LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate F.B hnd Ψ Φ).mp hΨ

/-- A *projection*: an `F`-self-adjoint idempotent operator. -/
def IsFProjection (F : EJAForm V) (P : V →ₗ[ℝ] V) : Prop :=
  P * P = P ∧ ∀ a b, F.B (P a) b = F.B a (P b)

/-- **EJA 26**: `Φ` (with adjoint `Ψ`) is a *partial isometry* when `ΦΦ*` and
`Φ*Φ` are projections. -/
def IsPartialIsometry (F : EJAForm V) (Φ Ψ : V →ₗ[ℝ] V) : Prop :=
  IsFAdjoint F Φ Ψ ∧ IsFProjection F (Φ * Ψ) ∧ IsFProjection F (Ψ * Φ)

/-- `Q_p` is a projection for an idempotent `p`. -/
theorem idem_U_isFProjection (F : EJAForm V) {p : V} (hp : p * p = p) :
    IsFProjection F (ejaU p) := ⟨idem_Q_idem hp, F.U_self_adj p⟩

/-! ### Supports of positive elements -/

/-- `p` is the *support* `⌈x⌉` of `x`: the least idempotent with `p * x = x`.
For an effect this is EJA 13's ceiling (`ejaSupp_eq_ceil`); Thm 27 applies
`⌈·⌉` to positive elements. -/
def IsSupp (x p : V) : Prop :=
  p * p = p ∧ p * x = x ∧ ∀ e : V, e * e = e → e * x = x → p ≤ e

theorem IsSupp.unique {x p p' : V} (h : IsSupp x p) (h' : IsSupp x p') : p = p' :=
  le_antisymm (h.2.2 p' h'.1 h'.2.1) (h'.2.2 p h.1 h.2.1)

theorem exists_isSupp {x : V} (hx : 0 ≤ x) : ∃ p, IsSupp x p := by
  obtain ⟨n, _, hn⟩ := chu_strong_unit x
  set t : ℝ := 1 / ((n : ℝ) + 1) with htdef
  have ht : 0 < t := by positivity
  have htn : t * n ≤ 1 := by
    rw [htdef, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hy0 : 0 ≤ t • x := (eja_nonneg_iff _).mpr (eja_isSumSq_smul ht.le ((eja_nonneg_iff _).mp hx))
  have hy1 : t • x ≤ 1 := by
    have h1 : t • x ≤ (t * n) • (1 : V) := by
      rw [← eja_sub_nonneg, mul_smul, ← smul_sub, eja_nonneg_iff]
      exact eja_isSumSq_smul ht.le ((eja_nonneg_iff _).mp (eja_sub_nonneg.mpr hn))
    have h2 : (t * n) • (1 : V) ≤ 1 := by
      rw [← eja_sub_nonneg, eja_nonneg_iff]
      have : (1 : V) - (t * n) • 1 = (1 - t * n) • 1 := by rw [sub_smul, one_smul]
      rw [this]; exact eja_isSumSq_smul_one (by linarith)
    exact le_trans h1 h2
  obtain ⟨hc, hle, hmin⟩ := (EJAceilfloor hy0 hy1).2.2.1
  have key : ∀ e : V, e * e = e → (e * x = x ↔ t • x ≤ e) := by
    intro e he
    rw [idem_le_iff_mul he hy0 hy1, eja_mul_smul]
    exact ⟨fun h => by rw [h], fun h => smul_right_injective V ht.ne' h⟩
  exact ⟨ejaCeil (t • x), hc, (key _ hc).mpr hle, fun e he hex => hmin e he ((key e he).mp hex)⟩

open Classical in
/-- The support `⌈x⌉` of a positive element (junk `0` elsewhere). -/
noncomputable def ejaSupp (x : V) : V := if h : ∃ p, IsSupp x p then h.choose else 0

theorem ejaSupp_spec {x : V} (hx : 0 ≤ x) : IsSupp x (ejaSupp x) := by
  have hex := exists_isSupp hx
  rw [ejaSupp, dif_pos hex]; exact hex.choose_spec

theorem ejaSupp_of_isSupp {x p : V} (h : IsSupp x p) : ejaSupp x = p := by
  have hex : ∃ p, IsSupp x p := ⟨p, h⟩
  rw [ejaSupp, dif_pos hex]; exact hex.choose_spec.unique h

theorem ejaSupp_idem {p : V} (hp : p * p = p) : ejaSupp p = p :=
  ejaSupp_of_isSupp ⟨hp, hp, fun e he hep => (idem_le_idem_iff hp he).mpr hep⟩

/-- For an effect, the support is EJA 13's ceiling. -/
theorem ejaSupp_eq_ceil {x : V} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ejaSupp x = ejaCeil x := by
  obtain ⟨hc, hle, hmin⟩ := (EJAceilfloor hx0 hx1).2.2.1
  refine ejaSupp_of_isSupp ⟨hc, (idem_le_iff_mul hc hx0 hx1).mp hle, fun e he hex => ?_⟩
  exact hmin e he ((idem_le_iff_mul he hx0 hx1).mpr hex)

/-- Same zero pattern against idempotents (trace form). -/
def SameZP (x y : V) : Prop := ∀ t : V, t * t = t → (ejaB x t = 0 ↔ ejaB y t = 0)

theorem SameZP.symm {x y : V} (h : SameZP x y) : SameZP y x := fun t ht => (h t ht).symm

theorem SameZP.trans {x y z : V} (h : SameZP x y) (h' : SameZP y z) : SameZP x z :=
  fun t ht => (h t ht).trans (h' t ht)

/-- Positive elements with the same zero pattern have the same support. -/
theorem SameZP.supp_eq {x y : V} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : SameZP x y) :
    ejaSupp x = ejaSupp y := by
  have key : ∀ e : V, e * e = e → (e * x = x ↔ e * y = y) := by
    intro e he
    have he' := eja_one_sub_idem he
    have hx' : e * x = x ↔ (1 - e) * x = 0 := by
      rw [eja_sub_mul, eja_one_mul, sub_eq_zero, eq_comm]
    have hy' : e * y = y ↔ (1 - e) * y = 0 := by
      rw [eja_sub_mul, eja_one_mul, sub_eq_zero, eq_comm]
    rw [hx', hy', idem_mul_eq_zero_iff_ejaB hx he', idem_mul_eq_zero_iff_ejaB hy he']
    exact h _ he'
  obtain ⟨hs, hsy, hmin⟩ := ejaSupp_spec hy
  exact ejaSupp_of_isSupp ⟨hs, (key _ hs).mpr hsy, fun e he hex => hmin e he ((key e he).mp hex)⟩

/-- `x` and `x²` have the same zero pattern for `x ≥ 0`. -/
theorem sameZP_sq {x : V} (hx : 0 ≤ x) : SameZP x (x * x) := by
  intro t ht
  have hxx : 0 ≤ x * x := (eja_nonneg_iff _).mpr (IsSumSq.mul_self x)
  rw [← idem_mul_eq_zero_iff_ejaB hx ht, ← idem_mul_eq_zero_iff_ejaB hxx ht]
  exact ⟨fun h => eja_peirce_zero_mul_zero ht h h, mul_idem_eq_zero_of_sq hx ht⟩

/-- `Q_a` preserves "same zero pattern" of positive elements. -/
theorem SameZP.U {x y : V} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : SameZP x y) (a : V) :
    SameZP (ejaU a x) (ejaU a y) := by
  intro t ht
  rw [← ejaB_U_self_adj, ← ejaB_U_self_adj]
  exact zero_pattern_extend hx hy h (eja_U_nonneg' a (eja_idem_nonneg ht))

/-- Combinations of one spectral family with the same zero coefficients have the
same zero pattern. -/
theorem sameZP_spectral {s : Finset ℝ} {e : ℝ → V} (hidem : ∀ l ∈ s, e l * e l = e l)
    {g h : ℝ → ℝ} (hg : ∀ l ∈ s, 0 ≤ g l) (hh : ∀ l ∈ s, 0 ≤ h l)
    (hgh : ∀ l ∈ s, g l = 0 ↔ h l = 0) :
    SameZP (∑ l ∈ s, g l • e l) (∑ l ∈ s, h l • e l) := by
  intro t ht
  have hexp : ∀ c : ℝ → ℝ, (∀ l ∈ s, 0 ≤ c l) →
      (ejaB (∑ l ∈ s, c l • e l) t = 0 ↔ ∀ l ∈ s, c l = 0 ∨ ejaB (e l) t = 0) := by
    intro c hc
    have hterm : ∀ l ∈ s, 0 ≤ c l * ejaB (e l) t := fun l hl =>
      mul_nonneg (hc l hl) (eja_isSumSq_ejaB_idem_nonneg
        ((eja_nonneg_iff _).mp (eja_idem_nonneg (hidem l hl))) t ht)
    rw [ejaB_sum_left]
    simp only [ejaB_smul_left]
    rw [Finset.sum_eq_zero_iff_of_nonneg hterm]
    exact forall₂_congr fun l _ => mul_eq_zero
  rw [hexp g hg, hexp h hh]
  exact forall₂_congr fun l hl => or_congr (hgh l hl) Iff.rfl

/-- The range of a positive `T` lies in `E₁(e)` when `T(1)` does. -/
theorem range_in_corner {T : V →ₗ[ℝ] V} (hT : IsPositiveMap T) {e : V} (he : e * e = e)
    (h1 : e * T 1 = T 1) (x : V) : e * T x = T x := by
  have hnn : ∀ y : V, 0 ≤ y → e * T y = T y := by
    intro y hy
    obtain ⟨n, _, hn⟩ := chu_strong_unit y
    have hle : T y ≤ (n : ℝ) • T 1 := by
      have h2 := hT.mono hn
      rwa [map_smul] at h2
    exact eja_corner_of_le_smul he h1 (hT y hy) hle
  obtain ⟨n, hn, _⟩ := chu_strong_unit x
  have hpos : 0 ≤ x + (n : ℝ) • (1 : V) := by
    rw [← eja_sub_nonneg] at hn
    convert hn using 1; abel
  have hone' : (0 : V) ≤ (n : ℝ) • 1 := by
    rw [eja_nonneg_iff]; exact eja_isSumSq_smul_one (Nat.cast_nonneg n)
  have hx : x = (x + (n : ℝ) • (1 : V)) - (n : ℝ) • 1 := by abel
  rw [hx, map_sub, eja_mul_sub, hnn _ hpos, hnn _ hone']

theorem eq_of_ejaB {u v : V} (h : ∀ y, ejaB u y = ejaB v y) : u = v := by
  have h1 : ejaB (u - v) (u - v) = 0 := by rw [ejaB_sub_left, h, sub_self]
  exact sub_eq_zero.mp (eja_eq_zero_of_ejaB_self h1)

/-- **EJA 27** (`theor:polardecomp`, main.tex:647, Theorem, *polar
decomposition*): for positive `p, q` there is a positive partial isometry `Φ`
(adjoint `Φ*` for any associative inner product `F`) with
`Q_q Q_p = Φ Q_{√(Q_p q²)}`, `Φ(1) = ⌈Q_q p⌉`, `Φ*(1) = ⌈Q_p q⌉`,
`Φ*Φ = Q_{⌈Q_p q⌉}` and `ΦΦ* = Q_{⌈Q_q p⌉}`.  `Φ = Q_q Q_p Q_{(Q_p q²)^{-1/2}}`
(pseudo-inverse) as printed; `Φ*Φ` by the fundamental formula as printed.  For
`ΦΦ*` the print shows it is a projection (Kadison–Ringrose 6.1.1) with
`(ΦΦ*)(1) = ⌈Q_q p⌉` and calls that sufficient — it is not (the projection onto
`ℝ1` in `M₂` also fixes `1`); here instead `ΦΦ* = Q_{Φ(1)}` by the fundamental
formula, and `Q_{Φ(1)}` idempotent forces `Φ(1)` idempotent. -/
theorem polardecomp (F : EJAForm V) {p q : V} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∃ Φ Φs : V →ₗ[ℝ] V, IsPositiveMap Φ ∧ IsPartialIsometry F Φ Φs ∧
      ejaU q * ejaU p = Φ * ejaU (ejaSqrt (ejaU p (q * q))) ∧
      Φ 1 = ejaSupp (ejaU q p) ∧ Φs 1 = ejaSupp (ejaU p q) ∧
      Φs * Φ = ejaU (ejaSupp (ejaU p q)) ∧ Φ * Φs = ejaU (ejaSupp (ejaU q p)) := by
  classical
  have hqq : 0 ≤ q * q := (eja_nonneg_iff _).mpr (IsSumSq.mul_self q)
  have hpp : 0 ≤ p * p := (eja_nonneg_iff _).mpr (IsSumSq.mul_self p)
  set a := ejaU p (q * q) with hadef
  have ha : 0 ≤ a := eja_U_nonneg' p hqq
  obtain ⟨s, e, hidem, horth, hne0, hsum, hdec⟩ := eja_spectral a
  have hl : ∀ l ∈ s, 0 ≤ l := by
    refine (eja_ortho_isSumSq_iff hidem horth hne0 (fun r => r)).mp ?_
    rw [← hdec]; exact (eja_nonneg_iff a).mp ha
  set fe : ℝ → ℝ := fun l => if l = 0 then 0 else 1 with hfe
  set fc : ℝ → ℝ := fun l => if l = 0 then 0 else (Real.sqrt l)⁻¹ with hfc
  set E1 : V := ∑ l ∈ s, fe l • e l with hE1
  set c : V := ∑ l ∈ s, fc l • e l with hc
  have hsqrtl : ∀ l ∈ s, l ≠ 0 → Real.sqrt l ≠ 0 := fun l hl' h0 =>
    (Real.sqrt_pos.mpr (lt_of_le_of_ne (hl l hl') (Ne.symm h0))).ne'
  -- the spectral calculus
  have hFam := fun (g g' : ℝ → ℝ) (y : V) => eja_U_family_comp' g g' hidem horth hsum y
  have hcongr : ∀ (g g' : ℝ → ℝ), (∀ l ∈ s, g l = g' l) → ∀ y,
      ejaU (∑ l ∈ s, g l • e l) y = ejaU (∑ l ∈ s, g' l • e l) y := by
    intro g g' h y; rw [Finset.sum_congr rfl fun l hl => by rw [h l hl]]
  have hE1idem : E1 * E1 = E1 := by
    rw [hE1, eja_ortho_mul hidem horth]
    exact Finset.sum_congr rfl fun l _ => by by_cases h : l = 0 <;> simp [hfe, h]
  have hE1a : E1 * a = a := by
    rw [hE1]; conv_lhs => rw [hdec]
    rw [eja_ortho_mul hidem horth]; conv_rhs => rw [hdec]
    exact Finset.sum_congr rfl fun l _ => by by_cases h : l = 0 <;> simp [hfe, h]
  have hsqrt : ejaSqrt a = ∑ l ∈ s, Real.sqrt l • e l := by
    refine ejaSqrt_unique ?_ ?_
    · rw [eja_nonneg_iff, eja_ortho_isSumSq_iff hidem horth hne0]
      exact fun l _ => Real.sqrt_nonneg l
    · rw [eja_ortho_mul hidem horth]; conv_rhs => rw [hdec]
      exact Finset.sum_congr rfl fun l hl' => by rw [Real.mul_self_sqrt (hl l hl')]
  have hc_sqrt : ∀ y, ejaU c (ejaU (ejaSqrt a) y) = ejaU E1 y := by
    intro y
    rw [hsqrt, hc, hFam, hE1]
    refine hcongr _ _ (fun l hl' => ?_) y
    by_cases h : l = 0
    · simp [hfc, hfe, h]
    · simp only [hfc, hfe, h, if_false]; exact inv_mul_cancel₀ (hsqrtl l hl' h)
  have hc_a_c : ∀ y, ejaU c (ejaU a (ejaU c y)) = ejaU E1 y := by
    intro y
    have ha' : a = ∑ l ∈ s, l • e l := hdec
    rw [ha', hc, hFam, hFam, hE1]
    refine hcongr _ _ (fun l hl' => ?_) y
    by_cases h : l = 0
    · simp [hfc, hfe, h]
    · simp only [hfc, hfe, h, if_false]
      rw [show (Real.sqrt l)⁻¹ * l * (Real.sqrt l)⁻¹ = l / (Real.sqrt l * Real.sqrt l) by ring,
        Real.mul_self_sqrt (hl l hl'), div_self h]
  have hc_E1 : ∀ y, ejaU c (ejaU E1 y) = ejaU c y := by
    intro y
    rw [hc, hE1, hFam]
    refine hcongr _ _ (fun l _ => ?_) y
    by_cases h : l = 0 <;> simp [hfc, hfe, h]
  have hca : ejaU c a = E1 := by
    have : a = ejaU (ejaSqrt a) 1 := by rw [ejaU_apply_one, (ejaSqrt_spec ha).2]
    rw [this, hc_sqrt, ejaU_apply_one, hE1idem]
  -- the range of `Q_p Q_q` lies in `E₁(E1)`
  have hQE1 : ∀ y, ejaU E1 (ejaU p (ejaU q y)) = ejaU p (ejaU q y) := by
    intro y
    have hT : IsPositiveMap ((ejaU p).comp (ejaU q)) := fun x hx =>
      eja_U_nonneg' p (eja_U_nonneg' q hx)
    have h1 : E1 * ((ejaU p).comp (ejaU q)) 1 = ((ejaU p).comp (ejaU q)) 1 := by
      simp only [LinearMap.comp_apply, ejaU_apply_one q]; exact hE1a
    have := range_in_corner hT hE1idem h1 y
    simp only [LinearMap.comp_apply] at this
    rw [ejaU_idem hE1idem]; exact (eja_pone_eq_self_iff _ hE1idem _).mpr this
  have hkill : ∀ x, ejaU q (ejaU p (ejaU E1 x)) = ejaU q (ejaU p x) := by
    intro x
    refine eq_of_ejaB fun y => ?_
    rw [← ejaB_U_self_adj, ← ejaB_U_self_adj, ← ejaB_U_self_adj, hQE1, ejaB_U_self_adj,
      ejaB_U_self_adj]
  -- the maps
  set Φ : V →ₗ[ℝ] V := ejaU q * ejaU p * ejaU c with hΦ
  set Φs : V →ₗ[ℝ] V := ejaU c * ejaU p * ejaU q with hΦs
  have hΦapp : ∀ x, Φ x = ejaU q (ejaU p (ejaU c x)) := fun x => rfl
  have hΦsapp : ∀ x, Φs x = ejaU c (ejaU p (ejaU q x)) := fun x => rfl
  have hΦpos : IsPositiveMap Φ := fun x hx => by
    rw [hΦapp]; exact eja_U_nonneg' q (eja_U_nonneg' p (eja_U_nonneg' c hx))
  have hadj : IsFAdjoint F Φ Φs := by
    intro x y
    rw [hΦsapp, hΦapp, F.U_self_adj, F.U_self_adj, F.U_self_adj]
  -- `Φ* Φ = Q_{E1}`
  have hΦsΦ : Φs * Φ = ejaU E1 := by
    ext x
    rw [Module.End.mul_apply, hΦsapp, hΦapp, ← ejaU_mul_self q, ← ejaU_ejaU_apply,
      hc_a_c]
  -- `E1 = ⌈Q_p q⌉`
  have hzpE1 : SameZP E1 a := by
    rw [hE1]; conv_rhs => rw [hdec]
    refine sameZP_spectral hidem (fun l _ => by by_cases h : l = 0 <;> simp [hfe, h])
      hl (fun l _ => ?_)
    by_cases h : l = 0 <;> simp [hfe, h]
  have hE1supp : E1 = ejaSupp (ejaU p q) := by
    have hzp : SameZP E1 (ejaU p q) :=
      hzpE1.trans (((sameZP_sq hq).symm).U hqq hq p)
    rw [← hzp.supp_eq (eja_idem_nonneg hE1idem) (eja_U_nonneg' p hq), ejaSupp_idem hE1idem]
  have hΦs1 : Φs 1 = E1 := by
    rw [hΦsapp, ejaU_apply_one, ← hadef, hca]
  -- `ΦΦ* = Q_{Φ(1)}`, and `Φ(1)` is an idempotent
  set w := Φ 1 with hw
  have hw0 : 0 ≤ w := hΦpos 1 (eja_idem_nonneg (eja_mul_one 1))
  have hΦΦs : Φ * Φs = ejaU w := by
    ext x
    rw [Module.End.mul_apply, hΦapp, hΦsapp, ← ejaU_mul_self c, ← ejaU_ejaU_apply,
      ← ejaU_ejaU_apply, hw, hΦapp, ejaU_apply_one]
  have hΦE1 : Φ * ejaU E1 = Φ := by
    ext x; rw [Module.End.mul_apply, hΦapp, hΦapp, hc_E1]
  have hidemΦΦs : ejaU w * ejaU w = ejaU w := by
    rw [← hΦΦs, show Φ * Φs * (Φ * Φs) = Φ * (Φs * Φ) * Φs by simp only [mul_assoc], hΦsΦ, hΦE1]
  have hww : w * w = w := by
    have h1 : ejaU (w * w) 1 = ejaU w 1 := by
      rw [show ejaU (w * w) 1 = ejaU w (ejaU w 1) from ejaU_mul_self w 1,
        ← Module.End.mul_apply, hidemΦΦs]
    rw [ejaU_apply_one, ejaU_apply_one] at h1
    have hv0 : 0 ≤ w * w := (eja_nonneg_iff _).mpr (IsSumSq.mul_self w)
    exact sqrt_unique hv0 hw0 h1
  have hwsupp : w = ejaSupp (ejaU q p) := by
    have hcc : c * c = ∑ l ∈ s, (fc l * fc l) • e l := by rw [hc, eja_ortho_mul hidem horth]
    have hzp1 : SameZP (c * c) E1 := by
      rw [hcc, hE1]
      refine sameZP_spectral hidem (fun l _ => mul_self_nonneg _)
        (fun l _ => by by_cases h : l = 0 <;> simp [hfe, h]) (fun l hl' => ?_)
      by_cases h : l = 0
      · simp [hfc, hfe, h]
      · simp only [hfc, hfe, h, if_false, mul_self_eq_zero, inv_eq_zero, one_ne_zero, iff_false]
        exact hsqrtl l hl' h
    have hcc0 : 0 ≤ c * c := (eja_nonneg_iff _).mpr (IsSumSq.mul_self c)
    have hE10 := eja_idem_nonneg hE1idem
    have hz2 : SameZP w (ejaU q (ejaU p E1)) := by
      rw [hw, hΦapp, ejaU_apply_one]
      exact (hzp1.U hcc0 hE10 p).U (eja_U_nonneg' p hcc0) (eja_U_nonneg' p hE10) q
    have hE1' : ejaU q (ejaU p E1) = ejaU q (p * p) := by
      have := hkill 1
      rwa [ejaU_apply_one E1, hE1idem, ejaU_apply_one p] at this
    rw [hE1'] at hz2
    have hz3 : SameZP w (ejaU q p) := hz2.trans (((sameZP_sq hp).symm).U hpp hp q)
    rw [← hz3.supp_eq hw0 (eja_U_nonneg' q hp), ejaSupp_idem hww]
  refine ⟨Φ, Φs, hΦpos, ⟨hadj, ?_, ?_⟩, ?_, hwsupp, by rw [hΦs1, hE1supp], by rw [hΦsΦ, hE1supp],
    by rw [hΦΦs, ← hwsupp]⟩
  · rw [hΦΦs]; exact idem_U_isFProjection F hww
  · rw [hΦsΦ]; exact idem_U_isFProjection F hE1idem
  · ext x
    rw [Module.End.mul_apply, Module.End.mul_apply, hΦapp, hc_sqrt, hkill]

end Polar

/-! ## EJA 30–31: helpers -/

section PolarHelpers

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Mul V] [One V]
  [PartialOrder V] [EuclideanJordanAlgebra V]

/-- A partial isometry satisfies `Φ Φ* Φ = Φ` (Kadison–Ringrose 6.1.1). -/
theorem IsPartialIsometry.left {F : EJAForm V} {Φ Ψ : V →ₗ[ℝ] V} (h : IsPartialIsometry F Φ Ψ)
    (x : V) : Φ (Ψ (Φ x)) = Φ x := by
  obtain ⟨hadj, _, ⟨hP, _⟩⟩ := h
  set y := x - Ψ (Φ x)
  have hPy : Ψ (Φ y) = 0 := by
    have h1 : Ψ (Φ (Ψ (Φ x))) = Ψ (Φ x) := by
      have := congrArg (fun m : V →ₗ[ℝ] V => m x) hP
      simpa [Module.End.mul_apply] using this
    simp only [y, map_sub, h1, sub_self]
  have h2 : F.B (Φ y) (Φ y) = 0 := by rw [← hadj, hPy, map_zero, LinearMap.zero_apply]
  have h3 := F.eq_zero_of_self _ h2
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

/-- A partial isometry satisfies `Φ* Φ Φ* = Φ*`. -/
theorem IsPartialIsometry.right {F : EJAForm V} {Φ Ψ : V →ₗ[ℝ] V} (h : IsPartialIsometry F Φ Ψ)
    (x : V) : Ψ (Φ (Ψ x)) = Ψ x := by
  obtain ⟨hadj, ⟨hP, _⟩, _⟩ := h
  set y := x - Φ (Ψ x)
  have hPy : Φ (Ψ y) = 0 := by
    have h1 : Φ (Ψ (Φ (Ψ x))) = Φ (Ψ x) := by
      have := congrArg (fun m : V →ₗ[ℝ] V => m x) hP
      simpa [Module.End.mul_apply] using this
    simp only [y, map_sub, h1, sub_self]
  have h2 : F.B (Ψ y) (Ψ y) = 0 := by rw [hadj, hPy, map_zero]
  have h3 := F.eq_zero_of_self _ h2
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

/-- The adjoint of a positive map for the trace form is positive (self-duality). -/
theorem adjoint_nonneg {Φ Ψ : V →ₗ[ℝ] V} (hΦ : IsPositiveMap Φ)
    (hadj : IsFAdjoint (EJAForm.trace V) Φ Ψ) : IsPositiveMap Ψ := by
  intro x hx
  refine eja_nonneg_of_forall_idem fun t ht => ?_
  have := hadj x t
  change ejaB (Ψ x) t = ejaB x (Φ t) at this
  rw [this]
  exact (EJAForm.trace V).nonneg_nonneg hx (hΦ t (eja_idem_nonneg ht))

theorem supp_mul_of_mul {x e : V} (hx : 0 ≤ x) (he : e * e = e) (h : e * x = x) :
    e * ejaSupp x = ejaSupp x := by
  obtain ⟨hs, _, hmin⟩ := ejaSupp_spec hx
  exact (idem_le_idem_iff hs he).mp (hmin e he h)

/-- `E₁(e) ⊆ E₁(e')` for idempotents `e ≤ e'`. -/
theorem peirce_one_mono {e e' u : V} (he : e * e = e) (hee' : e' * e = e) (hu : e * u = u) :
    e' * u = u := by
  have h1 : e * (1 - e') = 0 := by
    rw [eja_mul_sub, eja_mul_one, eja_mul_comm, hee', sub_self]
  have h2 := eja_peirce_one_mul_zero he hu h1
  rw [eja_mul_sub, eja_mul_one, sub_eq_zero] at h2
  rw [eja_mul_comm]; exact h2.symm

theorem mul_of_supp_mul {x e : V} (hx : 0 ≤ x) (he : e * e = e) (h : e * ejaSupp x = ejaSupp x) :
    e * x = x := by
  obtain ⟨hs, hsx, _⟩ := ejaSupp_spec hx
  exact peirce_one_mono hs h hsx

theorem val_ejaPone {p : EJAIdem V} (y x : EJACorner p) :
    EJACorner.val (ejaPone y x) = ejaPone (EJACorner.val y) (EJACorner.val x) := by
  simp [ejaPone_apply]

theorem corner_le_iff {p : EJAIdem V} (y z : EJACorner p) :
    y ≤ z ↔ EJACorner.val y ≤ EJACorner.val z := by
  rw [← eja_sub_nonneg, eja_corner_nonneg_iff, EJACorner.val_sub, eja_sub_nonneg]

/-- The ceiling in a corner is the support in `V`. -/
theorem corner_ceil_val {p : EJAIdem V} {y : EJACorner p} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    EJACorner.val (ejaCeil y) = ejaSupp (EJACorner.val y) := by
  have hv0 : 0 ≤ EJACorner.val y := eja_corner_val_nonneg h0
  have hv1 : EJACorner.val y ≤ 1 := by
    have := eja_corner_val_le h1
    rw [EJACorner.val_one] at this
    exact le_trans this (eja_idem_le_one p.idem)
  obtain ⟨hs, hsy, hmin⟩ := ejaSupp_spec hv0
  have hps : p.elt * ejaSupp (EJACorner.val y) = ejaSupp (EJACorner.val y) :=
    supp_mul_of_mul hv0 p.idem (EJACorner.val_prop y)
  set z : EJACorner p := EJACorner.mk' _ hps
  have hz : z * z = z := EJACorner.val_injective (by simp [z, hs])
  have key : ∀ e : EJACorner p, e * e = e → (y ≤ e ↔ z ≤ e) := by
    intro e he
    have hve : EJACorner.val e * EJACorner.val e = EJACorner.val e := by
      rw [← EJACorner.val_mul, he]
    rw [corner_le_iff, corner_le_iff, idem_le_iff_mul hve hv0 hv1]
    show _ ↔ ejaSupp (EJACorner.val y) ≤ EJACorner.val e
    exact ⟨fun h => hmin _ hve h, fun h => mul_of_supp_mul hv0 hve ((idem_le_idem_iff hs hve).mp h)⟩
  have hle : IsLeastIdemAbove y z :=
    ⟨hz, (key z hz).mpr le_rfl, fun e he hye => (key e he).mp hye⟩
  rw [ejaCeil_of_least hle]
  rfl

/-- The square root in a corner is the square root in `V`. -/
theorem corner_sqrt_val {p : EJAIdem V} {y : EJACorner p} (h0 : 0 ≤ y) :
    EJACorner.val (ejaSqrt y) = ejaSqrt (EJACorner.val y) := by
  obtain ⟨hs0, hss⟩ := ejaSqrt_spec h0
  exact (ejaSqrt_unique (eja_corner_val_nonneg hs0) (by rw [← EJACorner.val_mul, hss])).symm

end PolarHelpers

section PureCompose

/-- A corner followed by an isomorphism is a corner. -/
theorem IsCorner.comp_iso {E C C' : EJAPsu.{u}} {b : E.carrier} {π : E ⟶ C} (h : IsCorner b π)
    {θ : C ⟶ C'} {θ' : C' ⟶ C} (h1 : θ ≫ θ' = 𝟙 C) (h2 : θ' ≫ θ = 𝟙 C') :
    IsCorner b (π ≫ θ) := by
  refine ⟨by rw [ejapsu_comp_apply, ejapsu_comp_apply, h.1], fun F g hg => ?_⟩
  obtain ⟨gb, hgb, hu⟩ := h.2 F g hg
  refine ⟨θ' ≫ gb, by dsimp only; rw [Category.assoc, ← Category.assoc θ, h1, Category.id_comp, hgb],
    fun k hk => ?_⟩
  have := hu (θ ≫ k) (by dsimp only; rw [← Category.assoc]; exact hk)
  rw [← this, ← Category.assoc, h2, Category.id_comp]

/-- An isomorphism followed by a filter is a filter. -/
theorem IsFilter.iso_comp {E D D' : EJAPsu.{u}} {q : E.carrier} {ξ : D ⟶ E} (h : IsFilter q ξ)
    {θ : D' ⟶ D} {θ' : D ⟶ D'} (h1 : θ ≫ θ' = 𝟙 D') (h2 : θ' ≫ θ = 𝟙 D) :
    IsFilter q (θ ≫ ξ) := by
  refine ⟨by rw [ejapsu_comp_apply, ejapsu_iso_unital h1 h2]; exact h.1, fun F f hf => ?_⟩
  obtain ⟨fb, hfb, hu⟩ := h.2 F f hf
  refine ⟨fb ≫ θ', by dsimp only; rw [Category.assoc, ← Category.assoc θ', h2, Category.id_comp, hfb],
    fun k hk => ?_⟩
  have := hu (k ≫ θ) (by dsimp only; rw [Category.assoc]; exact hk)
  rw [← this, Category.assoc, h1, Category.comp_id]

/-- The standard filter reflects the order. -/
theorem stdFilter_reflect (E : EJAPsu.{u}) {q : E.carrier} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    {x y : (filterObj E q).carrier}
    (h : (stdFilter E h0 h1).toLinearMap x ≤ (stdFilter E h0 h1).toLinearMap y) : x ≤ y := by
  obtain ⟨b', _, hU'U, _, _⟩ := filter_data h0 h1
  rw [stdFilter_apply, stdFilter_apply] at h
  have h2 := eja_U_mono b' h
  rw [hU'U, hU'U, (eja_pone_eq_self_iff _ (ejaCeil_idem q) _).mpr (EJACorner.val_prop x),
    (eja_pone_eq_self_iff _ (ejaCeil_idem q) _).mpr (EJACorner.val_prop y)] at h2
  exact (corner_le_iff x y).mpr h2

/-- Every filter reflects the order. -/
theorem IsFilter.reflect {E D : EJAPsu.{u}} {q : E.carrier} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {ξ : D ⟶ E} (h : IsFilter q ξ) {x y : D.carrier} (hxy : ξ.toLinearMap x ≤ ξ.toLinearMap y) :
    x ≤ y := by
  obtain ⟨_, hσ⟩ := stdFilter_isFilter E hq0 hq1
  obtain ⟨θ, θ', hθσ, hθθ', _⟩ := filter_iso h hσ
  rw [← hθσ, ejapsu_comp_apply, ejapsu_comp_apply] at hxy
  have h2 := θ'.mono (stdFilter_reflect E hq0 hq1 hxy)
  rwa [ejapsu_inv_apply hθθ', ejapsu_inv_apply hθθ'] at h2

/-- **Filters compose** (thesis B 197IX, used in EJA 31): if `ξ` is a filter for
`q` and `ξ'` one for the effect `q'`, then `ξ' ≫ ξ` is a filter for `ξ(q')`. -/
theorem IsFilter.comp {E D D' : EJAPsu.{u}} {q : E.carrier} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {ξ : D ⟶ E} (h : IsFilter q ξ) {q' : D.carrier} (hq'1 : q' ≤ 1) {ξ' : D' ⟶ D}
    (h' : IsFilter q' ξ') : IsFilter (ξ.toLinearMap q') (ξ' ≫ ξ) := by
  refine ⟨by rw [ejapsu_comp_apply]; exact ξ.mono h'.1, fun F f hf => ?_⟩
  obtain ⟨fb, hfb, hu⟩ := h.2 F f (le_trans hf (le_trans (ξ.mono hq'1) h.1))
  have hfb1 : fb.toLinearMap 1 ≤ q' := by
    refine h.reflect hq0 hq1 ?_
    rw [← ejapsu_comp_apply, hfb]; exact hf
  obtain ⟨fbb, hfbb, hu'⟩ := h'.2 F fb hfb1
  refine ⟨fbb, by dsimp only; rw [← Category.assoc, hfbb, hfb], fun k hk => ?_⟩
  exact hu' k (hu (k ≫ ξ') (by dsimp only; rw [Category.assoc]; exact hk))

/-- Every corner is unital. -/
theorem IsCorner.unital {E C : EJAPsu.{u}} {b : E.carrier} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {π : E ⟶ C} (h : IsCorner b π) : π.toLinearMap 1 = 1 := by
  obtain ⟨ι, ι', hρι, hιι', hι'ι⟩ := corner_iso h (stdCorner_isCorner E hb0 hb1)
  have hρ1 : (stdCorner E b).toLinearMap 1 = 1 := EJACorner.val_injective (by
    rw [stdCorner_val, eja_pone_one _ (ejaFloor_idem b)]; rfl)
  rw [← hρι, ejapsu_comp_apply, hρ1, ejapsu_iso_unital hιι' hι'ι]

/-- An isomorphism of `EJA_psu` preserves the Jordan product (EJA 36). -/
theorem ejapsu_iso_mul {A B : EJAPsu.{u}} {φ : A ⟶ B} {ψ : B ⟶ A} (h1 : φ ≫ ψ = 𝟙 A)
    (h2 : ψ ≫ φ = 𝟙 B) (x y : A.carrier) :
    φ.toLinearMap (x * y) = φ.toLinearMap x * φ.toLinearMap y := by
  let Θ : A.carrier ≃ₗ[ℝ] B.carrier :=
    { φ.toLinearMap with
      invFun := ψ.toLinearMap
      left_inv := fun x => ejapsu_inv_apply h1 x
      right_inv := fun y => ejapsu_inv_apply h2 y }
  have hpos : ∀ x, 0 ≤ Θ x ↔ 0 ≤ x := by
    intro x
    refine ⟨fun h => ?_, fun h => φ.map_nonneg' x h⟩
    have := ψ.map_nonneg' _ h
    rwa [show ψ.toLinearMap (Θ x) = x from ejapsu_inv_apply h1 x] at this
  exact (unital_order_iso_jordan Θ (ejapsu_iso_unital h1 h2) hpos).map_mul x y

/-- **Corners compose** (thesis B 197IX, used in EJA 31): if `π` is a corner for
`b` and `π'` one for `b'`, then `π ≫ π'` is a corner for an idempotent `e`
(the lift of `⌊b'⌋`). -/
theorem IsCorner.comp {E C C' : EJAPsu.{u}} {b : E.carrier} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {π : E ⟶ C} (h : IsCorner b π) {b' : C.carrier} (hb'0 : 0 ≤ b') (hb'1 : b' ≤ 1)
    {π' : C ⟶ C'} (h' : IsCorner b' π') : ∃ e : E.carrier, e * e = e ∧ IsCorner e (π ≫ π') := by
  obtain ⟨ι, ι', hρι, hιι', hι'ι⟩ := corner_iso h (stdCorner_isCorner E hb0 hb1)
  have hfl' := ejaFloor_idem b'
  set y := ι'.toLinearMap (ejaFloor b') with hy
  have hyy : y * y = y := by rw [hy, ← ejapsu_iso_mul hι'ι hιι', hfl']
  set e := EJACorner.val y with he
  have hee : e * e = e := by rw [he, ← EJACorner.val_mul, hyy]
  have hπe : π.toLinearMap e = ejaFloor b' := by
    rw [← hρι, ejapsu_comp_apply]
    have : (stdCorner E b).toLinearMap e = y := EJACorner.val_injective (by
      rw [stdCorner_val]; exact (eja_pone_eq_self_iff _ (ejaFloor_idem b) _).mpr
        (EJACorner.val_prop y))
    rw [this, hy, ejapsu_inv_apply hι'ι]
  have hπ1 := h.unital hb0 hb1
  obtain ⟨_, hfle, _⟩ := (EJAceilfloor hb0 hb1).2.2.2
  obtain ⟨_, hfle', _⟩ := (EJAceilfloor hb'0 hb'1).2.2.2
  have hey : e ≤ ejaFloor b := by
    have h2 : y ≤ 1 := eja_idem_le_one hyy
    have := eja_corner_val_le h2
    rwa [EJACorner.val_one] at this
  have hπ'fl : π'.toLinearMap (ejaFloor b') = π'.toLinearMap 1 :=
    floor_one π'.toLinearMap π'.map_nonneg' hb'0 hb'1 h'.1.symm
  refine ⟨e, hee, ⟨by rw [ejapsu_comp_apply, ejapsu_comp_apply, hπ1, hπe, hπ'fl], fun F g hg => ?_⟩⟩
  have hgb : g.toLinearMap 1 = g.toLinearMap b := by
    refine le_antisymm ?_ (g.mono hb1)
    rw [hg]; exact g.mono (le_trans hey hfle)
  obtain ⟨gb, hgbπ, hu⟩ := h.2 F g hgb
  have hgb1 : gb.toLinearMap 1 = gb.toLinearMap b' := by
    have e1 : gb.toLinearMap 1 = g.toLinearMap 1 := by rw [← hπ1, ← ejapsu_comp_apply, hgbπ]
    have e2 : gb.toLinearMap (ejaFloor b') = g.toLinearMap e := by
      rw [← hπe, ← ejapsu_comp_apply, hgbπ]
    refine le_antisymm ?_ (gb.mono hb'1)
    rw [e1, hg, ← e2]; exact gb.mono hfle'
  obtain ⟨gbb, hgbb, hu'⟩ := h'.2 F gb hgb1
  refine ⟨gbb, by dsimp only; rw [Category.assoc, hgbb, hgbπ], fun k hk => ?_⟩
  exact hu' k (hu (π' ≫ k) (by dsimp only; rw [← Category.assoc]; exact hk))

end PureCompose

/-! ## EJA 30–31: `π ∘ ξ` is pure; pure maps compose -/

section Eja30

/-- **EJA 30** (main.tex:704, Proposition): a standard filter followed by a
standard corner, `π_b ∘ ξ_q`, is `ξ_a ∘ Φ ∘ π_c` for effects `a, c` and an
isomorphism `Φ`; in other words it is pure (`eja30_isPure`).  The print takes
the corner at an idempotent `p`; `π_b` depends only on `⌊b⌋`, so any effect `b`
is allowed.  Paper's proof: `f̄ = Q_{(Q_p q)^{-1/2}} f` and the polar
decomposition (EJA 27); here the polar decomposition `Q_{√q} Q_p = Ψ Q_{√(Q_p q)}`
(`polardecomp`) is taken adjoint: `Q_p Q_{√q} = Q_{√(Q_p q)} Ψ*`, and `Ψ*`
restricts to an isomorphism `E₁(⌈Q_{√q} p⌉) → E₁(⌈Q_p q⌉)` with inverse `Ψ`. -/
theorem eja30 (E : EJAPsu.{u}) {q b : E.carrier} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) :
    ∃ (a : (cornerObj E b).carrier) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
      (c : (filterObj E q).carrier) (_ : 0 ≤ c) (_ : c ≤ 1)
      (Φ : cornerObj (filterObj E q) c ⟶ filterObj (cornerObj E b) a)
      (Φ' : filterObj (cornerObj E b) a ⟶ cornerObj (filterObj E q) c),
      Φ ≫ Φ' = 𝟙 _ ∧ Φ' ≫ Φ = 𝟙 _ ∧
      stdFilter E hq0 hq1 ≫ stdCorner E b
        = stdCorner (filterObj E q) c ≫ Φ ≫ stdFilter (cornerObj E b) ha0 ha1 := by
  classical
  have hP := ejaFloor_idem b
  have hCq := ejaCeil_idem q
  obtain ⟨hsq0, hsqsq⟩ := ejaSqrt_spec hq0
  have hP0 := eja_idem_nonneg hP
  have hA0 : 0 ≤ ejaU (ejaFloor b) q := eja_U_nonneg' _ hq0
  -- the effect `a = π_b(q)` of the corner
  set a : (cornerObj E b).carrier := (stdCorner E b).toLinearMap q with ha
  have hav : EJACorner.val a = ejaU (ejaFloor b) q := by rw [ha, stdCorner_val, ← ejaU_idem hP]
  have ha0 : 0 ≤ a := (stdCorner E b).map_nonneg' q hq0
  have ha1 : a ≤ 1 := le_trans ((stdCorner E b).mono hq1) (stdCorner E b).map_subunital'
  -- the idempotent `c = ⌈Q_{√q} p⌉` of the filter's domain
  have hcE0 : 0 ≤ ejaU (ejaSqrt q) (ejaFloor b) := eja_U_nonneg' _ hP0
  obtain ⟨hsCi, _, _⟩ := ejaSupp_spec hcE0
  have hT : IsPositiveMap (ejaU (ejaSqrt q)) := fun x hx => eja_U_nonneg' _ hx
  have hCqq : ejaCeil q * ejaU (ejaSqrt q) 1 = ejaU (ejaSqrt q) 1 := by
    rw [ejaU_apply_one, hsqsq]; exact ejaCeil_mul hq0 hq1
  have hCq_range := range_in_corner hT hCq hCqq
  have hCqsC : ejaCeil q * ejaSupp (ejaU (ejaSqrt q) (ejaFloor b))
      = ejaSupp (ejaU (ejaSqrt q) (ejaFloor b)) := supp_mul_of_mul hcE0 hCq (hCq_range _)
  set sC := ejaSupp (ejaU (ejaSqrt q) (ejaFloor b)) with hsC
  set c : (filterObj E q).carrier := EJACorner.mk' sC hCqsC with hc
  have hcc : c * c = c := EJACorner.val_injective (by rw [EJACorner.val_mul]; exact hsCi)
  have hc0 : 0 ≤ c := eja_idem_nonneg hcc
  have hc1 : c ≤ 1 := eja_idem_le_one hcc
  have hfc : EJACorner.val (floorIdem c).elt = sC := by
    show EJACorner.val (ejaFloor c) = sC
    rw [ejaFloor_idem_eq hcc]; rfl
  -- the polar decomposition of `Q_{√q} Q_p`
  obtain ⟨Ψ, Ψs, hΨpos, hPI, hfac, hΨ1, hΨs1, hΨsΨ, hΨΨs⟩ :=
    polardecomp (EJAForm.trace E.carrier) hP0 hsq0
  rw [hsqsq] at hfac
  set sA := ejaSupp (ejaU (ejaFloor b) q) with hsA
  have hsA' : ejaSupp (ejaU (ejaFloor b) (ejaSqrt q)) = sA := by
    have h := (sameZP_sq hsq0).U hsq0 ((eja_nonneg_iff _).mpr (IsSumSq.mul_self _)) (ejaFloor b)
    rw [hsqsq] at h
    exact h.supp_eq (eja_U_nonneg' _ hsq0) hA0
  rw [hsA'] at hΨs1 hΨsΨ
  obtain ⟨hsAi, _, _⟩ := ejaSupp_spec hA0
  have hca : EJACorner.val (ceilIdem a).elt = sA := by
    show EJACorner.val (ejaCeil a) = sA
    rw [corner_ceil_val ha0 ha1, hav]
  have hΨspos : IsPositiveMap Ψs := adjoint_nonneg hΨpos hPI.1
  have hkey : ∀ x, ejaU (ejaFloor b) (ejaU (ejaSqrt q) x)
      = ejaU (ejaSqrt (ejaU (ejaFloor b) q)) (Ψs x) := by
    intro x
    refine eq_of_ejaB fun y => ?_
    have hf' : ejaU (ejaSqrt q) (ejaU (ejaFloor b) y)
        = Ψ (ejaU (ejaSqrt (ejaU (ejaFloor b) q)) y) := congrArg (fun m : E.carrier →ₗ[ℝ] E.carrier => m y) hfac
    rw [← ejaB_U_self_adj, ← ejaB_U_self_adj, hf', ← ejaB_U_self_adj]
    exact (hPI.1 x _).symm
  have hΨsΨx : ∀ x, Ψs (Ψ x) = ejaU sA x := fun x => congrArg (fun m : E.carrier →ₗ[ℝ] E.carrier => m x) hΨsΨ
  have hΨΨsx : ∀ x, Ψ (Ψs x) = ejaU sC x := fun x => congrArg (fun m : E.carrier →ₗ[ℝ] E.carrier => m x) hΨΨs
  have hΨs_rng : ∀ x, sA * Ψs x = Ψs x := by
    intro x
    have h := hPI.right x
    rw [hΨsΨx, ejaU_idem hsAi] at h
    rw [← h]; exact eja_mul_pone _ hsAi _
  have hΨ_rng : ∀ x, sC * Ψ x = Ψ x := by
    intro x
    have h := hPI.left x
    rw [← Module.End.mul_apply Ψ Ψs, hΨΨs, ejaU_idem hsCi] at h
    rw [← h]; exact eja_mul_pone _ hsCi _
  have hΨs_kill : ∀ x, Ψs (ejaU sC x) = Ψs x := fun x => by rw [← hΨΨsx, hPI.right]
  have hPsA : ejaFloor b * sA = sA := supp_mul_of_mul hA0 hP (by
    rw [ejaU_idem hP]; exact eja_mul_pone _ hP _)
  have hPu : ∀ u, sA * u = u → ejaFloor b * u = u := fun u hu => peirce_one_mono hsAi hPsA hu
  have hCqv : ∀ v, sC * v = v → ejaCeil q * v = v := fun v hv => peirce_one_mono hsCi hCqsC hv
  have hfix_sC : ∀ v, sC * v = v → ejaU sC v = v := fun v hv => by
    rw [ejaU_idem hsCi]; exact (eja_pone_eq_self_iff _ hsCi _).mpr hv
  have hfix_sA : ∀ v, sA * v = v → ejaU sA v = v := fun v hv => by
    rw [ejaU_idem hsAi]; exact (eja_pone_eq_self_iff _ hsAi _).mpr hv
  -- the isomorphism `Φ = Ψ*` restricted, and its inverse `Ψ` restricted
  have hmemC : ∀ y : EJACorner (floorIdem c), sC * EJACorner.val (EJACorner.val y)
      = EJACorner.val (EJACorner.val y) := by
    intro y
    have h := congrArg EJACorner.val (EJACorner.val_prop y)
    rwa [EJACorner.val_mul, hfc] at h
  have hmemA : ∀ z : EJACorner (ceilIdem a), sA * EJACorner.val (EJACorner.val z)
      = EJACorner.val (EJACorner.val z) := by
    intro z
    have h := congrArg EJACorner.val (EJACorner.val_prop z)
    rwa [EJACorner.val_mul, hca] at h
  let mkA : (u : E.carrier) → sA * u = u → EJACorner (ceilIdem a) := fun u hu =>
    EJACorner.mk' (EJACorner.mk' (p := floorIdem b) u (by show ejaFloor b * u = u; exact hPu u hu))
      (EJACorner.val_injective (by rw [EJACorner.val_mul, hca]; exact hu))
  let mkC : (v : E.carrier) → sC * v = v → EJACorner (floorIdem c) := fun v hv =>
    EJACorner.mk' (EJACorner.mk' (p := ceilIdem q) v (by show ejaCeil q * v = v; exact hCqv v hv))
      (EJACorner.val_injective (by rw [EJACorner.val_mul, hfc]; exact hv))
  have hmkA : ∀ u hu, EJACorner.val (EJACorner.val (mkA u hu)) = u := fun _ _ => rfl
  have hmkC : ∀ v hv, EJACorner.val (EJACorner.val (mkC v hv)) = v := fun _ _ => rfl
  let Φl : EJACorner (floorIdem c) →ₗ[ℝ] EJACorner (ceilIdem a) :=
    { toFun := fun y => mkA (Ψs (EJACorner.val (EJACorner.val y))) (hΨs_rng _)
      map_add' := fun y y' => EJACorner.val_injective (EJACorner.val_injective (by
        simp only [EJACorner.val_add, hmkA, map_add]))
      map_smul' := fun r y => EJACorner.val_injective (EJACorner.val_injective (by
        simp only [EJACorner.val_smul, hmkA, map_smul, RingHom.id_apply])) }
  let Φl' : EJACorner (ceilIdem a) →ₗ[ℝ] EJACorner (floorIdem c) :=
    { toFun := fun z => mkC (Ψ (EJACorner.val (EJACorner.val z))) (hΨ_rng _)
      map_add' := fun z z' => EJACorner.val_injective (EJACorner.val_injective (by
        simp only [EJACorner.val_add, hmkC, map_add]))
      map_smul' := fun r z => EJACorner.val_injective (EJACorner.val_injective (by
        simp only [EJACorner.val_smul, hmkC, map_smul, RingHom.id_apply])) }
  have hvv1C : EJACorner.val (EJACorner.val (1 : EJACorner (floorIdem c))) = sC := by
    rw [EJACorner.val_one, hfc]
  have hvv1A : EJACorner.val (EJACorner.val (1 : EJACorner (ceilIdem a))) = sA := by
    rw [EJACorner.val_one, hca]
  have hnn : ∀ {pp : EJAIdem E.carrier} {rr : EJAIdem (EJACorner pp)} (y : EJACorner rr),
      0 ≤ y ↔ 0 ≤ EJACorner.val (EJACorner.val y) := by
    intro pp rr y
    rw [eja_corner_nonneg_iff, eja_corner_nonneg_iff]
  let Φ : cornerObj (filterObj E q) c ⟶ filterObj (cornerObj E b) a :=
    { toLinearMap := Φl
      map_nonneg' := fun y hy => (hnn _).mpr (hΨspos _ ((hnn y).mp hy))
      map_subunital' := le_of_eq (EJACorner.val_injective (EJACorner.val_injective (by
        show Ψs (EJACorner.val (EJACorner.val (1 : EJACorner (floorIdem c))))
          = EJACorner.val (EJACorner.val (1 : EJACorner (ceilIdem a)))
        have hs1 : sC = ejaU sC 1 := by rw [ejaU_apply_one, hsCi]
        rw [hvv1C, hvv1A]
        conv_lhs => rw [hs1]
        rw [hΨs_kill, hΨs1]))) }
  let Φ' : filterObj (cornerObj E b) a ⟶ cornerObj (filterObj E q) c :=
    { toLinearMap := Φl'
      map_nonneg' := fun z hz => (hnn _).mpr (hΨpos _ ((hnn z).mp hz))
      map_subunital' := le_of_eq (EJACorner.val_injective (EJACorner.val_injective (by
        show Ψ (EJACorner.val (EJACorner.val (1 : EJACorner (ceilIdem a))))
          = EJACorner.val (EJACorner.val (1 : EJACorner (floorIdem c)))
        have hs1 : sA = Ψs (Ψ 1) := by rw [hΨsΨx, ejaU_apply_one, hsAi]
        rw [hvv1C, hvv1A, hs1, hPI.left, hΨ1]))) }
  refine ⟨a, ha0, ha1, c, hc0, hc1, Φ, Φ', ?_, ?_, ?_⟩
  · refine ejapsu_hom_ext fun y => EJACorner.val_injective (EJACorner.val_injective ?_)
    show Ψ (Ψs (EJACorner.val (EJACorner.val y))) = EJACorner.val (EJACorner.val y)
    rw [hΨΨsx, hfix_sC _ (hmemC y)]
  · refine ejapsu_hom_ext fun z => EJACorner.val_injective (EJACorner.val_injective ?_)
    show Ψs (Ψ (EJACorner.val (EJACorner.val z))) = EJACorner.val (EJACorner.val z)
    rw [hΨsΨx, hfix_sA _ (hmemA z)]
  · refine ejapsu_hom_ext fun x => EJACorner.val_injective ?_
    rw [ejapsu_comp_apply, stdCorner_val, stdFilter_apply, ejapsu_comp_apply, ejapsu_comp_apply,
      stdFilter_apply, val_ejaU, corner_sqrt_val ha0, hav]
    show ejaPone (ejaFloor b) (ejaU (ejaSqrt q) (EJACorner.val x))
      = ejaU (ejaSqrt (ejaU (ejaFloor b) q))
          (Ψs (EJACorner.val (EJACorner.val ((stdCorner (filterObj E q) c).toLinearMap x))))
    rw [stdCorner_val, val_ejaPone, ejaFloor_idem_eq hcc]
    show _ = ejaU (ejaSqrt (ejaU (ejaFloor b) q)) (Ψs (ejaPone sC (EJACorner.val x)))
    rw [← ejaU_idem hsCi, hΨs_kill, ← hkey, ejaU_idem hP]

/-- **EJA 30**, "in other words": `π_b ∘ ξ_q` is pure. -/
theorem eja30_isPure (E : EJAPsu.{u}) {q b : E.carrier} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : IsPure (stdFilter E hq0 hq1 ≫ stdCorner E b) := by
  obtain ⟨a, ha0, ha1, c, hc0, hc1, Φ, Φ', h1, h2, hf⟩ := eja30 E hq0 hq1 hb0 hb1
  exact ⟨_, c, a, stdCorner _ c ≫ Φ, stdFilter _ ha0 ha1, ⟨hc0, hc1⟩, ⟨ha0, ha1⟩,
    (stdCorner_isCorner _ hc0 hc1).comp_iso h1 h2, (stdFilter_isFilter _ ha0 ha1).2,
    by rw [hf, Category.assoc]⟩

/-- **EJA 31** (`cor:purepure`, main.tex:718, Corollary): the composition of pure
maps is pure.  The paper's proof: `ξ₁ ∘ π₁ ∘ ξ₂ ∘ π₂` with `π₁ ∘ ξ₂` pure by
EJA 30 (up to the isomorphisms relating arbitrary filters and corners to the
standard ones), then corners compose and filters compose (thesis B 197IX,
`IsCorner.comp`, `IsFilter.comp`). -/
theorem purepure {A B C : EJAPsu.{u}} {g : A ⟶ B} {h : B ⟶ C} (hg : IsPure g) (hh : IsPure h) :
    IsPure (g ≫ h) := by
  obtain ⟨Cg, bg, qg, πg, ξg, ⟨hbg0, hbg1⟩, ⟨hqg0, hqg1⟩, hπg, hξg, rfl⟩ := hg
  obtain ⟨Ch, bh, qh, πh, ξh, ⟨hbh0, hbh1⟩, ⟨hqh0, hqh1⟩, hπh, hξh, rfl⟩ := hh
  obtain ⟨θ, θ', hθσ, hθθ', hθ'θ⟩ := filter_iso hξg (stdFilter_isFilter B hqg0 hqg1).2
  obtain ⟨ι, ι', hρι, hιι', hι'ι⟩ := corner_iso hπh (stdCorner_isCorner B hbh0 hbh1)
  obtain ⟨a, ha0, ha1, c, hc0, hc1, Φ, Φ', h1, h2, hf⟩ := eja30 B hqg0 hqg1 hbh0 hbh1
  -- the corner part
  have hK0 : IsCorner bg (πg ≫ θ) := hπg.comp_iso hθθ' hθ'θ
  obtain ⟨e, he, hK1⟩ := hK0.comp hbg0 hbg1 hc0 hc1 (stdCorner_isCorner _ hc0 hc1)
  have hK := hK1.comp_iso h1 h2
  -- the filter part
  have hL0 : IsFilter qh (ι ≫ ξh) := hξh.iso_comp hιι' hι'ι
  have hL := hL0.comp hqh0 hqh1 ha1 (stdFilter_isFilter _ ha0 ha1).2
  have hq'0 : 0 ≤ (ι ≫ ξh).toLinearMap a := (ι ≫ ξh).map_nonneg' a ha0
  have hq'1 : (ι ≫ ξh).toLinearMap a ≤ 1 :=
    le_trans ((ι ≫ ξh).mono ha1) (ι ≫ ξh).map_subunital'
  refine ⟨_, e, _, _, _, ⟨eja_idem_nonneg he, eja_idem_le_one he⟩, ⟨hq'0, hq'1⟩, hK, hL, ?_⟩
  rw [← hθσ, ← hρι]
  simp only [Category.assoc]
  rw [reassoc_of% hf]

end Eja30

end Papers.EJA
