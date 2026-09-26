import Papers.REC.Monoidal

/-!
# REC 128 in full generality

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707, `short.tex` §6, `prop:tensor-quadratic` (line 2346):
for arbitrary `a ∈ V_A` and `b ∈ V_B`, `Q_{a⊗b} = Q_a ⊗ Q_b`.

`Monoidal.lean`'s `rec128` proves this only for two-block combinations
`a = αe + βe⊥`, `b = γf + δf⊥`.  Here (`rec128_general`) it is proved for all `a`, `b`,
in the same form (on product vectors: `Q_{a⊗b}(c ⊗ d) = Q_a c ⊗ Q_b d`; the operator
`Q_a ⊗ Q_b` is not defined on `V_{A⊗B}`, which is not an algebraic tensor product), so it
is a strict generalisation of `rec128` (`rec128_of_general`).  No named hypotheses beyond
those `rec128` carries (§5's three).

## Proof

Not the printed one: the print splits `a = a⁺ − a⁻` and needs `Q_a = asrt_{a²}` for
effects `a` (van de Wetering's thesis 4.6.17), which is avoided.  Instead:

1. sharp `e`, `f`: `Q_{e⊗f} = asrt_{e⊗f} = asrt_e ⊗ asrt_f` (REC 123, as in `rec128`);
2. a *symmetric bilinear* `D` on `V` (bounded, `‖D x y‖ ≤ K ‖x‖ ‖y‖`) that vanishes on
   the diagonal at idempotents vanishes on the whole diagonal (`bil_diag_eq_zero`):
   for commuting idempotents `x, y`, `D(x, y) = 0` by splitting `y = xy + x⊥y` and
   using that `x`, `xy`, `x⊥y`, `x + x⊥y = 1 − x⊥y⊥` are idempotents; so `D(z, z) = 0`
   for `z` a combination of *pairwise commuting* idempotents; these are norm-dense
   (`spec_pair_approx`, the level sets of one spectral representation), and
   `D(x,x) − D(z,z) = D(x − z, x) + D(z, x − z)`;
3. apply 2 to `b ↦ Q_{e⊗b}(c⊗d) − Q_e c ⊗ Q_b d` (polarised in `b`) with `e` sharp, then
   to `a ↦ Q_{a⊗b}(c⊗d) − Q_a c ⊗ Q_b d` (polarised in `a`).

The partition approximations of the plan are replaced by step 2's pairwise-commuting
polarisation, which needs no `k`-block identity.
-/

open CategoryTheory
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ## Norm-density of combinations of pairwise commuting idempotents -/

section PairApprox

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]

/-- **The spectral theorem, pairwise commuting form** (REC 58): every effect `y` is a norm
limit of combinations of *pairwise commuting* idempotents (the level-set idempotents of `y`'s
spectral representation all lie in the commutative range of `Ψ`).  A copy of
`spec_comm_approx` (Monoidal.lean) with this conclusion instead of "commuting with `y`". -/
theorem spec_pair_approx_eff (y : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × E), (∀ p ∈ l, Papers.SEA.IsIdempotent p.2) ∧
      (∀ p ∈ l, ∀ q ∈ l, Commutes p.2 q.2) ∧
      ousNorm (GP.Vec E) (GP.gmap y - (l.map fun p => p.1 • GP.gmap p.2).sum) < ε := by
  obtain ⟨B, _, X, _, _, _, hED, Ψ, hadd, hone, hmul, -, b, f, rfl⟩ := spectral_rep y
  set G : B → Set.Icc (0 : C(X, ℝ)) 1 → GP.Vec E := fun b f => GP.gmap (Ψ b f) with hG
  have hGadd := fun {b b' f f' k} hb hk => spec_G_add (E := E) Ψ hadd (b := b) (b' := b')
    (f := f) (f' := f') (k := k) hb hk
  have hG0 : G ⊥ kzero = 0 := by simp only [hG]; rw [spec_zero Ψ hadd, GP.gmap_zero]
  have hGnn : ∀ b f, 0 ≤ G b f := fun b f => GP.gmap_nonneg _
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnε : 1 / (n : ℝ) < ε := by
    rw [div_lt_iff₀ hnR]; rw [div_lt_iff₀ hε] at hn; linarith
  let S : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j =>
    kmk ((f : C(X, ℝ)) ⊓ ContinuousMap.const X ((j : ℝ) / n))
      (fun t => le_min (cIcc_nonneg f t) (by simp; positivity))
      (fun t => min_le_of_left_le (cIcc_le_one f t))
  have hS : ∀ j t, (S j : C(X, ℝ)) t = min ((f : C(X, ℝ)) t) ((j : ℝ) / n) := fun j t => by
    simp [S]
  have hSmono : ∀ j t, (S j : C(X, ℝ)) t ≤ (S (j + 1) : C(X, ℝ)) t := fun j t => by
    rw [hS, hS]; exact min_le_min_left _ (div_le_div_of_nonneg_right (by push_cast; linarith)
      hnR.le)
  let L : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j =>
    kmk ((S (j + 1) : C(X, ℝ)) - S j) (fun t => by simp only [ContinuousMap.sub_apply]; linarith [hSmono j t])
      (fun t => by
        simp only [ContinuousMap.sub_apply]
        have := cIcc_le_one (S (j + 1)) t; have := cIcc_nonneg (S j) t; linarith)
  have hL : ∀ j t, (L j : C(X, ℝ)) t = (S (j + 1) : C(X, ℝ)) t - (S j : C(X, ℝ)) t :=
    fun j t => rfl
  have hWc : ∀ j : ℕ, IsClopen (closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}) := fun j =>
    ⟨isClosed_closure, hED.open_closure _ (isOpen_lt continuous_const (f : C(X, ℝ)).continuous)⟩
  have hWf : ∀ j : ℕ, ∀ t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t},
      (j : ℝ) / n ≤ (f : C(X, ℝ)) t := fun j t ht =>
    closure_minimal (fun s hs => le_of_lt hs) (isClosed_le continuous_const
      (f : C(X, ℝ)).continuous) ht
  have hWn : ∀ j : ℕ, ∀ t ∉ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t},
      (f : C(X, ℝ)) t ≤ (j : ℝ) / n := fun j t ht => by
    by_contra hc; push Not at hc; exact ht (subset_closure hc)
  let χ : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun j => kind _ (hWc j)
  have hχ : ∀ j t, (χ j : C(X, ℝ)) t =
      (closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}).indicator (fun _ => (1 : ℝ)) t :=
    fun j t => rfl
  have hn1 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) / n := by positivity
  have hn2 : ((1 : ℕ) : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hnpos
  have hup : ∀ j, G ⊥ (L j) ≤ (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) := by
    intro j
    rw [← spec_G_rat Ψ hadd (χ j) hnpos 1 hn1 hn2]
    refine spec_G_bot_mono Ψ hadd fun t => ?_
    simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ, hL, hS]
    by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t}
    · rw [Set.indicator_of_mem ht, mul_one]
      have h1 := min_le_right ((f : C(X, ℝ)) t) (((j + 1 : ℕ) : ℝ) / n)
      have h2 := hWf j t ht
      rw [min_eq_right h2]; push_cast at h1 ⊢
      have : ((j : ℝ) + 1) / n = (j : ℝ) / n + 1 / n := by ring
      linarith
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have h2 := hWn j t ht
      rw [min_eq_left h2, min_eq_left (h2.trans (div_le_div_of_nonneg_right (by push_cast; linarith)
        hnR.le))]; simp
  have hlow : ∀ j, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ (L j) := by
    intro j
    rw [← spec_G_rat Ψ hadd (χ (j + 1)) hnpos 1 hn1 hn2]
    refine spec_G_bot_mono Ψ hadd fun t => ?_
    simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ, hL, hS]
    by_cases ht : t ∈ closure {t | ((j + 1 : ℕ) : ℝ) / n < (f : C(X, ℝ)) t}
    · rw [Set.indicator_of_mem ht, mul_one]
      have h2 := hWf (j + 1) t ht
      rw [min_eq_right h2, min_eq_right ((div_le_div_of_nonneg_right (by push_cast; linarith)
        hnR.le).trans h2)]
      push_cast; ring_nf; rfl
    · rw [Set.indicator_of_notMem ht, mul_zero]
      linarith [hSmono j t, hS j t, hS (j + 1) t]
  have hsum : ∀ m, G ⊥ (S m) = ∑ j ∈ Finset.range m, G ⊥ (L j) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero]
      have : S 0 = kzero := kext fun t => by
        rw [hS]; simp [min_eq_right (cIcc_nonneg f t)]
      rw [this, hG0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have := hGadd (b := ⊥) (b' := ⊥) (f := S m) (f' := L m) (k := S (m + 1)) (inf_idem _)
        (fun t => by rw [hL]; ring)
      rwa [sup_idem] at this
  have hSn : S n = f := kext fun t => by
    rw [hS, div_self hnR.ne']; exact min_eq_left (cIcc_le_one f t)
  have hGf : G ⊥ f = ∑ j ∈ Finset.range n, G ⊥ (L j) := by rw [← hSn]; exact hsum n
  set T : GP.Vec E := ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) with hT
  have hfT : G ⊥ f ≤ T := by rw [hGf]; exact Finset.sum_le_sum fun j _ => hup j
  have hGone : G ⊥ kone ≤ GP.gunit := by
    have := hGadd (b := ⊤) (b' := ⊥) (f := kzero) (f' := kone) (k := kone) (inf_bot_eq _)
      (fun t => by simp)
    rw [sup_bot_eq] at this
    have hu : GP.gunit = G ⊤ kone := by simp only [hG]; rw [hone]; rfl
    rw [hu]; simp only [hG]; rw [this]; exact le_add_of_nonneg_left (GP.gmap_nonneg _)
  have hTf : T - (((1 : ℕ) : ℝ) / n) • GP.gunit ≤ G ⊥ f := by
    have h1 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ f := by
      rw [hGf]; exact Finset.sum_le_sum fun j _ => hlow j
    have h2 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) =
        T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) + (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) := by
      rw [hT]
      have := Finset.sum_range_succ' (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
      have h3 := Finset.sum_range_succ (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
      rw [this] at h3
      rw [eq_sub_of_add_eq h3.symm]; abel
    have h4 : G ⊥ (χ 0) ≤ G ⊥ kone := spec_G_bot_mono Ψ hadd fun t => cIcc_le_one _ t
    calc T - (((1 : ℕ) : ℝ) / n) • GP.gunit ≤ T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) :=
          sub_le_sub_left (smul_le_smul_of_nonneg_left (h4.trans hGone) hn1) _
      _ ≤ T - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) + (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) :=
          le_add_of_nonneg_right (smul_nonneg hn1 (hGnn _ _))
      _ = _ := h2.symm
      _ ≤ G ⊥ f := h1
  have hR : ∀ p ∈ ((((1 : ℝ), Ψ b kzero) ::
      (List.range n).map (fun j => ((((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j)))) : List (ℝ × E)),
      ∃ b' f', p.2 = Ψ b' f' := by
    intro p hp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨j, -, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  refine ⟨((1 : ℝ), Ψ b kzero) ::
      (List.range n).map (fun j => ((((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j))), ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | ⟨j, -, rfl⟩
    · exact spec_idem (b := b) (f := kzero) Ψ hmul (kext fun t => by simp)
    · exact spec_idem (b := ⊥) (f := χ j) Ψ hmul (kext fun t => by
        simp only [kmul_val, ContinuousMap.mul_apply, hχ]
        by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t} <;> simp [ht])
  · intro p hp q hq
    obtain ⟨b1, f1, e1⟩ := hR p hp
    obtain ⟨b2, f2, e2⟩ := hR q hq
    rw [e1, e2]; exact commutes_psi Ψ hmul _ _ _ _
  · have hsumL : ((((1 : ℝ), Ψ b kzero) ::
        (List.range n).map (fun j => ((((1 : ℕ) : ℝ) / n), Ψ ⊥ (χ j)))).map
          fun p : ℝ × E => p.1 • GP.gmap p.2).sum = G b kzero + T := by
      rw [List.map_cons, List.sum_cons, List.map_map, list_range_map_sum, hT, one_smul]
      rfl
    have e1 : G b f = G b kzero + G ⊥ f := by
      have := hGadd (b := b) (b' := ⊥) (f := kzero) (f' := f) (k := f) (inf_bot_eq _)
        (fun t => by simp)
      rwa [sup_bot_eq] at this
    have hdiff : GP.gmap (Ψ b f) - (G b kzero + T) = G ⊥ f - T := by
      show G b f - _ = _
      rw [e1]; abel
    rw [hsumL, hdiff]
    refine lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ ?_) hnε
    · have h := hTf
      rw [Nat.cast_one] at h
      rw [neg_le_sub_iff_le_add]
      exact sub_le_iff_le_add.1 h
    · exact (sub_nonpos.2 hfT).trans (smul_nonneg (by positivity) (GP.gmap_nonneg _))

omit [EffectAlgebra E] [NormalSEA E] [EffectModule I E] in
theorem list_map_scale_sum {V : Type w} [AddCommGroup V] [Module ℝ V] (F : E → V) (r : ℝ)
    (l : List (ℝ × E)) :
    ((l.map (fun p => (r * p.1, p.2))).map fun p : ℝ × E => p.1 • F p.2).sum =
      r • (l.map fun p : ℝ × E => p.1 • F p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, ih, smul_add, _root_.smul_smul]

/-- Every `w ∈ V` is a norm limit of combinations of pairwise commuting idempotents. -/
theorem spec_pair_approx (w : GP.Vec E) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × E), (∀ p ∈ l, Papers.SEA.IsIdempotent p.2) ∧
      (∀ p ∈ l, ∀ q ∈ l, Commutes p.2 q.2) ∧
      ousNorm (GP.Vec E) (w - (l.map fun p => p.1 • GP.gmap p.2).sum) < ε := by
  obtain ⟨N, a, hN, rfl⟩ := gp_affine_repr w
  obtain ⟨l, hl1, hl2, hn⟩ := spec_pair_approx_eff a (ε := ε / (2 * N)) (by positivity)
  have h1 : ∀ x : E, Commutes (1 : E) x := fun x => by
    show (1 : E) ⊙ x = x ⊙ 1
    rw [one_seq, seq_one]
  refine ⟨((-N), (1 : E)) :: l.map (fun p => (2 * N * p.1, p.2)), ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact isIdempotent_one
    · exact hl1 q hq
  · intro p hp q hq
    simp only [List.mem_cons, List.mem_map] at hp hq
    rcases hp with rfl | ⟨p', hp', rfl⟩ <;> rcases hq with rfl | ⟨q', hq', rfl⟩
    · exact commutes_refl _
    · exact h1 _
    · exact (h1 _).symm
    · exact hl2 p' hp' q' hq'
  · rw [List.map_cons, List.sum_cons, list_map_scale_sum]
    have e : (2 * N) • GP.gmap a - N • GP.gunit -
        ((-N) • GP.gmap (1 : E) + (2 * N) • (l.map fun p : ℝ × E => p.1 • GP.gmap p.2).sum) =
        (2 * N) • (GP.gmap a - (l.map fun p : ℝ × E => p.1 • GP.gmap p.2).sum) := by
      rw [show (GP.gmap (1 : E) : GP.Vec E) = GP.gunit from rfl]; module
    rw [e]
    refine (ousNorm_smul_le _ _).trans_lt ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
    calc (2 * N) * ousNorm (GP.Vec E) _ < (2 * N) * (ε / (2 * N)) :=
          mul_lt_mul_of_pos_left hn (by positivity)
      _ = ε := by field_simp

end PairApprox

/-! ## Symmetric bilinear maps vanishing on the idempotents -/

section Bilin

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  {W : Type w} [AddCommGroup W] [Module ℝ W] [PartialOrder W] [OrderUnitSpace W]

omit [EffectModule I E] in
/-- The product of commuting idempotents is an idempotent. -/
theorem idem_seq_of_comm {x y : E} (h : Commutes x y) (hx : Papers.SEA.IsIdempotent x)
    (hy : Papers.SEA.IsIdempotent y) : Papers.SEA.IsIdempotent (x ⊙ y) := by
  have hx' : x ⊙ x = x := hx
  have hy' : y ⊙ y = y := hy
  show (x ⊙ y) ⊙ (x ⊙ y) = x ⊙ y
  calc (x ⊙ y) ⊙ (x ⊙ y) = x ⊙ (y ⊙ (x ⊙ y)) := (h.assoc _).symm
    _ = x ⊙ (y ⊙ (y ⊙ x)) := by rw [show x ⊙ y = y ⊙ x from h]
    _ = x ⊙ ((y ⊙ y) ⊙ x) := by rw [(commutes_refl y).assoc]
    _ = x ⊙ (y ⊙ x) := by rw [hy']
    _ = x ⊙ (x ⊙ y) := by rw [show y ⊙ x = x ⊙ y from h.symm]
    _ = (x ⊙ x) ⊙ y := (commutes_refl x).assoc y
    _ = x ⊙ y := by rw [hx']

omit [NormalSEA E] [EffectModule I E] [PartialOrder W] [OrderUnitSpace W] in
theorem bil_zero_of_sum {V : Type*} [AddCommGroup V] [Module ℝ V] (D : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hsym : ∀ x y, D x y = D y x) {x y : V} (hx : D x x = 0) (hy : D y y = 0)
    (hxy : D (x + y) (x + y) = 0) : D x y = 0 := by
  have e : D (x + y) (x + y) = D x x + (2 : ℝ) • D x y + D y y := by
    simp only [map_add, LinearMap.add_apply]
    rw [hsym y x]; module
  rw [e, hx, hy, zero_add, add_zero] at hxy
  exact (smul_eq_zero.1 hxy).resolve_left two_ne_zero

omit [PartialOrder W] [OrderUnitSpace W] in
/-- For commuting idempotents `x`, `y`: `D(x, y) = 0` when `D` vanishes on the diagonal at
idempotents. -/
theorem bil_comm_idem (D : GP.Vec E →ₗ[ℝ] GP.Vec E →ₗ[ℝ] W) (hsym : ∀ x y, D x y = D y x)
    (h0 : ∀ e : E, Papers.SEA.IsIdempotent e → D (GP.gmap e) (GP.gmap e) = 0)
    {x y : E} (h : Commutes x y) (hx : Papers.SEA.IsIdempotent x)
    (hy : Papers.SEA.IsIdempotent y) : D (GP.gmap x) (GP.gmap y) = 0 := by
  have hu := idem_seq_of_comm h hx hy
  have hv := idem_seq_of_comm h.symm.orth_l hy.compl hx
  have hw := idem_seq_of_comm h.orth_l hx.compl hy
  have hw' := idem_seq_of_comm h.symm.orth_l.orth_r hy.compl hx.compl
  have ey : GP.gmap (x ⊙ y) + GP.gmap (orth x ⊙ y) = GP.gmap y := gmap_split_comm h
  have ex : GP.gmap (y ⊙ x) + GP.gmap (orth y ⊙ x) = GP.gmap x := gmap_split_comm h.symm
  have ex' : GP.gmap (y ⊙ orth x) + GP.gmap (orth y ⊙ orth x) = GP.gmap (orth x) :=
    gmap_split_comm h.symm.orth_r
  rw [show y ⊙ x = x ⊙ y from h.symm] at ex
  rw [show y ⊙ orth x = orth x ⊙ y from h.orth_l.symm] at ex'
  have d1 : D (GP.gmap x) (GP.gmap (x ⊙ y)) = 0 := by
    rw [← ex, map_add, LinearMap.add_apply, h0 _ hu, zero_add, hsym]
    exact bil_zero_of_sum D hsym (h0 _ hu) (h0 _ hv) (by rw [ex]; exact h0 _ hx)
  have hsum : GP.gmap x + GP.gmap (orth x ⊙ y) = GP.gmap (orth (orth y ⊙ orth x)) := by
    have h1 := Papers.OAP.gmap_add_orth (orth y ⊙ orth x)
    have h2 := Papers.OAP.gmap_add_orth x
    rw [← ex'] at h2
    rw [eq_sub_of_add_eq' h1, ← h2]; abel
  have d2 : D (GP.gmap x) (GP.gmap (orth x ⊙ y)) = 0 :=
    bil_zero_of_sum D hsym (h0 _ hx) (h0 _ hw) (by rw [hsum]; exact h0 _ hw'.compl)
  rw [← ey, map_add, d1, d2, add_zero]

omit [NormalSEA E] [PartialOrder W] [OrderUnitSpace W] in
theorem bil_list_left (D : GP.Vec E →ₗ[ℝ] GP.Vec E →ₗ[ℝ] W) (l : List (ℝ × E)) (z : GP.Vec E)
    (h : ∀ p ∈ l, D (GP.gmap p.2) z = 0) : D ((l.map fun p => p.1 • GP.gmap p.2).sum) z = 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, h p List.mem_cons_self, smul_zero, zero_add]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

omit [PartialOrder W] [OrderUnitSpace W] in
theorem bil_list_zero (D : GP.Vec E →ₗ[ℝ] GP.Vec E →ₗ[ℝ] W) (hsym : ∀ x y, D x y = D y x)
    (h0 : ∀ e : E, Papers.SEA.IsIdempotent e → D (GP.gmap e) (GP.gmap e) = 0)
    (l : List (ℝ × E)) (hl1 : ∀ p ∈ l, Papers.SEA.IsIdempotent p.2)
    (hl2 : ∀ p ∈ l, ∀ q ∈ l, Commutes p.2 q.2) :
    D ((l.map fun p => p.1 • GP.gmap p.2).sum) ((l.map fun p => p.1 • GP.gmap p.2).sum) = 0 :=
  bil_list_left D l _ fun p hp => by
    rw [hsym]
    exact bil_list_left D l _ fun q hq =>
      bil_comm_idem D hsym h0 (hl2 q hq p hp) (hl1 q hq) (hl1 p hp)

/-- **Polarised density**: a bounded symmetric bilinear map out of `V = GP.Vec E` whose
quadratic form vanishes at the idempotents has vanishing quadratic form. -/
theorem bil_diag_eq_zero [IsOUS W] (D : GP.Vec E →ₗ[ℝ] GP.Vec E →ₗ[ℝ] W)
    (hsym : ∀ x y, D x y = D y x)
    (h0 : ∀ e : E, Papers.SEA.IsIdempotent e → D (GP.gmap e) (GP.gmap e) = 0) (K : ℝ)
    (hK : ∀ x y, ousNorm W (D x y) ≤ K * ousNorm (GP.Vec E) x * ousNorm (GP.Vec E) y)
    (x : GP.Vec E) : D x x = 0 := by
  set M := |K| * (2 * ousNorm (GP.Vec E) x + 1) with hM
  have hx0 := ousNorm_nonneg_rc x
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ousNorm W (D x x) ≤ δ * M := by
    intro δ hδ hδ1
    obtain ⟨l, hl1, hl2, hn⟩ := spec_pair_approx x hδ
    set z := (l.map fun p => p.1 • GP.gmap p.2).sum with hz
    have hzz : D z z = 0 := bil_list_zero D hsym h0 l hl1 hl2
    have e : D x x = D (x - z) x + D z (x - z) := by
      simp only [map_sub, LinearMap.sub_apply, hzz]; abel
    have n1 := ousNorm_nonneg_rc (x - z)
    have n3 := ousNorm_nonneg_rc z
    have nz : ousNorm (GP.Vec E) z ≤ ousNorm (GP.Vec E) x + δ := by
      have h := ousNorm_add_le x (z - x)
      rw [add_sub_cancel, ousNorm_sub_comm] at h
      linarith
    rw [e]
    refine (ousNorm_add_le _ _).trans ?_
    have h1 : ousNorm W (D (x - z) x) ≤ |K| * δ * ousNorm (GP.Vec E) x := by
      refine (hK _ _).trans ?_
      have := mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self K) hn.le n1 (abs_nonneg K)) hx0
      exact this
    have h2 : ousNorm W (D z (x - z)) ≤ |K| * (ousNorm (GP.Vec E) x + 1) * δ := by
      refine (hK _ _).trans ?_
      have a1 : K * ousNorm (GP.Vec E) z ≤ |K| * (ousNorm (GP.Vec E) x + 1) :=
        mul_le_mul (le_abs_self K) (by linarith) n3 (abs_nonneg K)
      exact mul_le_mul a1 hn.le n1 (by positivity)
    have : |K| * δ * ousNorm (GP.Vec E) x + |K| * (ousNorm (GP.Vec E) x + 1) * δ = δ * M := by
      rw [hM]; ring
    linarith
  refine eq_zero_of_ousNorm_small fun ε hε => ?_
  set δ := min 1 (ε / (M + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (M + 1) := min_le_right _ _
  refine (key δ hδ0 hδ1).trans ?_
  calc δ * M ≤ ε / (M + 1) * M := mul_le_mul_of_nonneg_right hδε hM0
    _ ≤ ε / (M + 1) * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε := div_mul_cancel₀ _ (by positivity)

end Bilin

/-! ## REC 128 -/

section Rec128General

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C) (hAS : AlfsenShultzJordanFromDerivations.{v})
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- `bil_diag_eq_zero` on `V_X`. -/
theorem va_diag_eq_zero {X Y : C} (D : VA σs X →ₗ[ℝ] VA σs X →ₗ[ℝ] VA σs Y)
    (hsym : ∀ x y, D x y = D y x)
    (h0 : ∀ e : CPt σs X, Papers.SEA.IsIdempotent e → D (GP.gmap e) (GP.gmap e) = 0) (K : ℝ)
    (hK : ∀ x y, ousNorm (VA σs Y) (D x y) ≤ K * ousNorm (VA σs X) x * ousNorm (VA σs X) y)
    (x : VA σs X) : D x x = 0 := by
  have := VA_isOUS σs Y
  exact bil_diag_eq_zero D hsym h0 K hK x

/-- `‖Q_{a,a'} w‖ ≤ 3 ‖a‖ ‖a'‖ ‖w‖`. -/
theorem jQ2L_norm_le (X : C) (w a a' : VA σs X) :
    ousNorm (VA σs X) (jQ2L σs hAS hRC h119 X w a a') ≤
      3 * ousNorm (VA σs X) a * ousNorm (VA σs X) a' * ousNorm (VA σs X) w := by
  simp only [jQ2L, LinearMap.mk₂_apply]
  have na := ousNorm_nonneg_rc a
  have na' := ousNorm_nonneg_rc a'
  have nw := ousNorm_nonneg_rc w
  have t1 := (jm_norm_le σs hAS hRC h119 X a (jm σs hAS hRC h119 X a' w)).trans
    (mul_le_mul_of_nonneg_left (jm_norm_le σs hAS hRC h119 X a' w) na)
  have t2 := (jm_norm_le σs hAS hRC h119 X a' (jm σs hAS hRC h119 X a w)).trans
    (mul_le_mul_of_nonneg_left (jm_norm_le σs hAS hRC h119 X a w) na')
  have t3 := (jm_norm_le σs hAS hRC h119 X (jm σs hAS hRC h119 X a a') w).trans
    (mul_le_mul_of_nonneg_right (jm_norm_le σs hAS hRC h119 X a a') nw)
  rw [sub_eq_add_neg]
  refine (ousNorm_add_le _ _).trans ?_
  rw [ousNorm_neg]
  refine (add_le_add_left (ousNorm_add_le (V := VA σs X) _ _) _).trans ?_
  nlinarith

theorem mul3_le {a a' b b' w : ℝ} (ha : a ≤ a') (hb : b ≤ b') (h0a : 0 ≤ a) (h0b : 0 ≤ b)
    (hw : 0 ≤ w) : 3 * a * b * w ≤ 3 * a' * b' * w := by
  have h := mul_le_mul ha hb h0b (h0a.trans ha)
  calc 3 * a * b * w = (3 * w) * (a * b) := by ring
    _ ≤ (3 * w) * (a' * b') := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 3 * a' * b' * w := by ring

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C] (h0 : σs.s = 0)

include h0

/-- REC 128 for sharp `e`, `f` (REC 123: `Q_{e⊗f} = asrt_{e⊗f} = asrt_e ⊗ asrt_f`). -/
theorem rec128_sharp {A B : C} {e : CPt σs A} {f : CPt σs B} (he : Papers.SEA.IsIdempotent e)
    (hf : Papers.SEA.IsIdempotent f) (c : VA σs A) (d : VA σs B) :
    jQA σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap e) (GP.gmap f)) (tensV σs c d) =
      tensV σs (jQA σs hAS hRC h119 A (GP.gmap e) c) (jQA σs hAS hRC h119 B (GP.gmap f) d) := by
  rw [tensV_gmap, jQA_idem σs hAS hRC h119 _ (cptTens_idem σs h0 he hf),
    Uop_cptTens_apply σs h0, jQA_idem σs hAS hRC h119 _ he, jQA_idem σs hAS hRC h119 _ hf]

/-- REC 128 for sharp `e` and arbitrary `b`. -/
theorem rec128_sharp_left {A B : C} {e : CPt σs A} (he : Papers.SEA.IsIdempotent e)
    (b : VA σs B) (c : VA σs A) (d : VA σs B) :
    jQA σs hAS hRC h119 (A ⊗ B) (tensV σs (GP.gmap e) b) (tensV σs c d) =
      tensV σs (jQA σs hAS hRC h119 A (GP.gmap e) c) (jQA σs hAS hRC h119 B b d) := by
  set v := tensV σs c d with hv
  set qe := jQA σs hAS hRC h119 A (GP.gmap e) c with hqe
  let L : VA σs B →ₗ[ℝ] VA σs (A ⊗ B) := (vtens σs (A := A) (B := B)).flip (GP.gmap e)
  let M : VA σs B →ₗ[ℝ] VA σs (A ⊗ B) := (vtens σs (A := A) (B := B)).flip qe
  let D : VA σs B →ₗ[ℝ] VA σs B →ₗ[ℝ] VA σs (A ⊗ B) :=
    (jQ2L σs hAS hRC h119 (A ⊗ B) v).compl₁₂ L L - (jQ2L σs hAS hRC h119 B d).compr₂ M
  have hD : ∀ x y, D x y = jQ2L σs hAS hRC h119 (A ⊗ B) v (tensV σs (GP.gmap e) x)
      (tensV σs (GP.gmap e) y) - tensV σs qe (jQ2L σs hAS hRC h119 B d x y) := fun x y => rfl
  have hsym : ∀ x y, D x y = D y x := by
    intro x y
    rw [hD, hD, jQ2L_symm σs hAS hRC h119 (A ⊗ B) v (tensV σs (GP.gmap e) x),
      jQ2L_symm σs hAS hRC h119 B d x]
  have ne := ousNorm_nonneg_rc (GP.gmap e : VA σs A)
  have nv := ousNorm_nonneg_rc v
  have nq := ousNorm_nonneg_rc qe
  have hK : ∀ x y, ousNorm _ (D x y) ≤
      (3 * ousNorm (VA σs A) (GP.gmap e) * ousNorm (VA σs A) (GP.gmap e) * ousNorm _ v +
        ousNorm (VA σs A) qe * (3 * ousNorm (VA σs B) d)) *
        ousNorm (VA σs B) x * ousNorm (VA σs B) y := by
    intro x y
    have nx := ousNorm_nonneg_rc x
    have ny := ousNorm_nonneg_rc y
    have t1 := (jQ2L_norm_le σs hAS hRC h119 (A ⊗ B) v (tensV σs (GP.gmap e) x)
      (tensV σs (GP.gmap e) y)).trans (mul3_le (tensV_norm_le σs _ x) (tensV_norm_le σs _ y)
        (ousNorm_nonneg_rc _) (ousNorm_nonneg_rc _) nv)
    have t2 := (tensV_norm_le σs qe (jQ2L σs hAS hRC h119 B d x y)).trans
      (mul_le_mul_of_nonneg_left (jQ2L_norm_le σs hAS hRC h119 B d x y) nq)
    rw [hD, sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    ring
  have := va_diag_eq_zero σs D hsym (fun f hf => by
    rw [hD, ← jQA_eq_jQ2L, ← jQA_eq_jQ2L, rec128_sharp σs hAS hRC h119 h0 he hf, sub_self]) _ hK b
  rw [hD, ← jQA_eq_jQ2L, ← jQA_eq_jQ2L] at this
  exact sub_eq_zero.1 this

/-- **REC 128** (`prop:tensor-quadratic`, short.tex:2346, Proposition), in full generality:
for arbitrary `a ∈ V_A`, `b ∈ V_B`, `Q_{a⊗b} = Q_a ⊗ Q_b` on product vectors,
`Q_{a⊗b}(c ⊗ d) = Q_a c ⊗ Q_b d`.  (`V_{A⊗B}` is not an algebraic tensor product, so the
printed `Q_a ⊗ Q_b` is read on product vectors, as in `rec128`, of which this is a strict
generalisation: `rec128_of_general`.)  Proof: the sharp case (REC 123), then polarised
density in `b` and in `a` (`bil_diag_eq_zero`); the print's route via `a = a⁺ − a⁻` and
`Q_a = asrt_{a²}` (van de Wetering's thesis 4.6.17) is not needed. -/
theorem rec128_general {A B : C} (a c : VA σs A) (b d : VA σs B) :
    jQA σs hAS hRC h119 (A ⊗ B) (tensV σs a b) (tensV σs c d) =
      tensV σs (jQA σs hAS hRC h119 A a c) (jQA σs hAS hRC h119 B b d) := by
  set v := tensV σs c d with hv
  set qb := jQA σs hAS hRC h119 B b d with hqb
  let L : VA σs A →ₗ[ℝ] VA σs (A ⊗ B) := vtens σs (A := A) (B := B) b
  let M : VA σs A →ₗ[ℝ] VA σs (A ⊗ B) := vtens σs (A := A) (B := B) qb
  let D : VA σs A →ₗ[ℝ] VA σs A →ₗ[ℝ] VA σs (A ⊗ B) :=
    (jQ2L σs hAS hRC h119 (A ⊗ B) v).compl₁₂ L L - (jQ2L σs hAS hRC h119 A c).compr₂ M
  have hD : ∀ x y, D x y = jQ2L σs hAS hRC h119 (A ⊗ B) v (tensV σs x b)
      (tensV σs y b) - tensV σs (jQ2L σs hAS hRC h119 A c x y) qb := fun x y => rfl
  have hsym : ∀ x y, D x y = D y x := by
    intro x y
    rw [hD, hD, jQ2L_symm σs hAS hRC h119 (A ⊗ B) v (tensV σs x b),
      jQ2L_symm σs hAS hRC h119 A c x]
  have nb := ousNorm_nonneg_rc b
  have nv := ousNorm_nonneg_rc v
  have nq := ousNorm_nonneg_rc qb
  have hK : ∀ x y, ousNorm _ (D x y) ≤
      (3 * ousNorm (VA σs B) b * ousNorm (VA σs B) b * ousNorm _ v +
        3 * ousNorm (VA σs A) c * ousNorm (VA σs B) qb) *
        ousNorm (VA σs A) x * ousNorm (VA σs A) y := by
    intro x y
    have nx := ousNorm_nonneg_rc x
    have ny := ousNorm_nonneg_rc y
    have t1 := (jQ2L_norm_le σs hAS hRC h119 (A ⊗ B) v (tensV σs x b)
      (tensV σs y b)).trans (mul3_le (tensV_norm_le σs x b) (tensV_norm_le σs y b)
        (ousNorm_nonneg_rc _) (ousNorm_nonneg_rc _) nv)
    have t2 := (tensV_norm_le σs (jQ2L σs hAS hRC h119 A c x y) qb).trans
      (mul_le_mul_of_nonneg_right (jQ2L_norm_le σs hAS hRC h119 A c x y) nq)
    rw [hD, sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    refine (add_le_add t1 t2).trans (le_of_eq ?_)
    ring
  have := va_diag_eq_zero σs D hsym (fun e he => by
    rw [hD, ← jQA_eq_jQ2L, ← jQA_eq_jQ2L, rec128_sharp_left σs hAS hRC h119 h0 he, sub_self])
    _ hK a
  rw [hD, ← jQA_eq_jQ2L, ← jQA_eq_jQ2L] at this
  exact sub_eq_zero.1 this

/-- `rec128` (two-block `a`, `b`) is the special case `a = αe + βe⊥`, `b = γf + δf⊥`. -/
theorem rec128_of_general {A B : C} {e : CPt σs A} {f : CPt σs B}
    (_he : Papers.SEA.IsIdempotent e) (_hf : Papers.SEA.IsIdempotent f) (α β γ δ : ℝ)
    (c : VA σs A) (d : VA σs B) :
    jQA σs hAS hRC h119 (A ⊗ B)
        (tensV σs (α • GP.gmap e + β • GP.gmap (orth e)) (γ • GP.gmap f + δ • GP.gmap (orth f)))
        (tensV σs c d) =
      tensV σs (jQA σs hAS hRC h119 A (α • GP.gmap e + β • GP.gmap (orth e)) c)
        (jQA σs hAS hRC h119 B (γ • GP.gmap f + δ • GP.gmap (orth f)) d) :=
  rec128_general σs hAS hRC h119 h0 _ _ _ _

end Rec128General

end Papers.REC

