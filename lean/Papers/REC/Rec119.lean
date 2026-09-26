import Papers.REC.Resolvent

/-!
# REC 119 (`lem:state-order-lemma`), proved: `WeteringStateOrderLemma` holds

B. Westerbaan, J. van de Wetering, *A computer scientist's reconstruction of
quantum theory*, arXiv:2109.10707, `short.tex` §5.4, Lemma 119: for a sharp `p`, a
predicate `a` and a (total) state `ω` with `a ∘ ω = 0`, `(p & a) ∘ ω = (p⊥ & a) ∘ ω`.
The print's proof is "exactly as" van de Wetering 2019 (arXiv:1803.11139v3), Prop. 46,
whose argument is: sharp case from compressibility + quadraticity, then general `a`
by simple approximants.  Here it is carried out with the effectus's internal states.

Plan.
1. (`r119_cross`, SEA algebra) For idempotent `q`, `r := q⊥` and any `p'` with the
   quadratic law `(r&p')² = r&(p'&r)`: `r&(p'&q) = x&y` with `x = r&p'`, `y = r&p'⊥`.
   Indeed `r&p' = r&(p'&q) ⊕ r&(p'&r) = r&(p'&q) ⊕ x²` (S1, `q ⊕ r = 1`), and
   `x = x&r = x² ⊕ x&y` (`x ≤ r`, `r = x ⊕ y`); cancel `x²`.
2. (`r119_sharp_seq`) For sharp `p, q`: `q⊥&(p&q) = q⊥&(p⊥&q)`: both sides are `x&y`
   resp. `y&x` by 1 (for `p'` = `p`, `p⊥`), and `x | y` since `x | x`, `x | r = x ⊕ y`.
   The quadratic law is REC 115 (`rec115`).
3. (`r119_sharp_state`) If `e` is sharp and `e ∘ ω = 0`, then `e⊥ ∘ ω = 1`, so by
   compressibility (REC 112) `ω(b) = ω(e⊥ & b)` for all `b`; apply 2 with `q = e`.
4. Scalars (REC 35 split, `rec102_trivial_factor`): `s = 1` or `s = 0`.
   * `s = 1` (`r119_bool`): the predicates are an orthoalgebra-like SEA: `a & a⊥` is
     self-summable (SEA 19), and a self-summable predicate vanishes (states + `σs.bool`),
     so every `a` is sharp; apply 3 with `e = a`.
   * `s = 0` (`r119_convex`): every predicate is in the convex part.  Work in `V_A`
     with `Φ := Ω ∘ D_p`, `Ω = stateLin ω`.  The spectral theorem (`spectral_rep`)
     writes `a = Ψ(b, f)`; with the clopen level sets `χ_j = 1_{cl{f > j/n}}`
     (`r119_layer`), `a = Ψ(b,0) + Σ_{j<n} (1/n) Ψ(⊥, χ_{j+1}) + v`, `0 ≤ v ≤ 1/n`.
     `Ψ(b,0)` and `Ψ(⊥,χ_{j+1})` are idempotent and `≤ n·a`, so `ω` kills them and 3
     gives `Φ = 0` on them; `|Φ v| ≤ 1/n` since `0 ≤ U_q v ≤ 1/n`.  So `Φ(a)` has norm
     `≤ 1/n` for all `n`, whence `0` (Archimedean `V_I`); read off in `Pred(I)`.
5. `rec102_hypfree`, `rec103_hypfree`, `rec136_hypfree`: the `_unconditional`
   versions (`Resolvent.lean`) applied to `weteringStateOrderLemma_holds`.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v w

/-! ### Step 1–2: the sharp identity in a quadratic SEA -/

section R119SEA

open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [Papers.SEA.SEAlgebra E]

/-- vdW 2019, Prop. 46, the core computation: for an idempotent `q`, `r = q⊥`, and a
`p'` with `(r & p')² = r & (p' & r)`, `r & (p' & q) = (r & p') & (r & p'⊥)`. -/
theorem r119_cross {p' q : E} (hq : Papers.SEA.IsIdempotent q)
    (hquad : (orth q ⊙ p') ⊙ (orth q ⊙ p') = orth q ⊙ (p' ⊙ orth q)) :
    orth q ⊙ (p' ⊙ q) = (orth q ⊙ p') ⊙ (orth q ⊙ orth p') := by
  have hri : Papers.SEA.IsIdempotent (orth q) := hq.compl
  -- `p' = p'&q ⊕ p'&r`
  obtain ⟨h1, e1⟩ := Papers.SEA.seq_ovee p' (EffectAlgebra.perp_orth q)
  rw [EffectAlgebra.ovee_orth, Papers.SEA.seq_one] at e1
  -- `r&p' = r&(p'&q) ⊕ r&(p'&r)`
  obtain ⟨h2, e2⟩ := Papers.SEA.seq_ovee (orth q) h1
  rw [← e1] at e2
  -- `r = x ⊕ y`, `x & r = x`
  obtain ⟨h3, e3⟩ := Papers.SEA.seq_split (orth q) p'
  have hxr : (orth q ⊙ p') ⊙ orth q = orth q ⊙ p' :=
    ((Papers.SEA.sea17_5 hri _).2.1).1 (Papers.SEA.seq_le_left _ _)
  obtain ⟨h4, e4⟩ := Papers.SEA.seq_ovee (orth q ⊙ p') h3
  rw [e3, hxr] at e4
  have h2' : Perp ((orth q ⊙ p') ⊙ (orth q ⊙ p')) (orth q ⊙ (p' ⊙ q)) := by
    rw [hquad]; exact PCM.perp_comm h2
  have eA : ovee ((orth q ⊙ p') ⊙ (orth q ⊙ p')) (orth q ⊙ (p' ⊙ q)) h2' = orth q ⊙ p' :=
    calc _ = ovee (orth q ⊙ (p' ⊙ orth q)) (orth q ⊙ (p' ⊙ q)) (PCM.perp_comm h2) :=
          PCM.ovee_congr hquad rfl _ _
      _ = ovee (orth q ⊙ (p' ⊙ q)) (orth q ⊙ (p' ⊙ orth q)) h2 := (PCM.ovee_comm h2).symm
      _ = orth q ⊙ p' := e2.symm
  exact Papers.SEA.cancel_left h2' h4 (eA.trans e4)

/-- vdW 2019, Prop. 46, sharp case (as an identity): for idempotents `p, q` in a SEA
satisfying the quadratic law at `q⊥`, `q⊥ & (p & q) = q⊥ & (p⊥ & q)`. -/
theorem r119_sharp_seq {p q : E} (hp : Papers.SEA.IsIdempotent p)
    (hq : Papers.SEA.IsIdempotent q)
    (hquad : ∀ p' : E, Papers.SEA.IsIdempotent p' →
      (orth q ⊙ p') ⊙ (orth q ⊙ p') = orth q ⊙ (p' ⊙ orth q)) :
    orth q ⊙ (p ⊙ q) = orth q ⊙ (orth p ⊙ q) := by
  rw [r119_cross hq (hquad p hp), r119_cross hq (hquad _ hp.compl), Papers.SEA.orth_orth]
  -- `x | y` for `x = r&p`, `y = r&p⊥`
  have hri : Papers.SEA.IsIdempotent (orth q) := hq.compl
  obtain ⟨h3, e3⟩ := Papers.SEA.seq_split (orth q) p
  have hxr : Papers.SEA.Commutes (orth q ⊙ p) (orth q) := by
    have hle := Papers.SEA.seq_le_left (orth q) p
    show (orth q ⊙ p) ⊙ orth q = orth q ⊙ (orth q ⊙ p)
    rw [((Papers.SEA.sea17_5 hri _).2.1).1 hle, ((Papers.SEA.sea17_5 hri _).1).1 hle]
  obtain ⟨h', e⟩ := Papers.SEA.orth_right_eq h3
  have hc1 : Papers.SEA.Commutes (orth q ⊙ p) (orth (ovee _ _ h3)) := by
    rw [e3]; exact hxr.orth_r
  have hc := Papers.SEA.Commutes.ovee h' (Papers.SEA.commutes_refl _) hc1
  rw [e] at hc
  exact hc.of_orth_r

end R119SEA

/-! ### Step 3–4: REC 119 in a sequential effectus -/

section R119

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

/-- For sharp `p, q ∈ Pred(A)`: `q⊥ & (p & q) = q⊥ & (p⊥ & q)` (REC 115 supplies the
quadratic law). -/
theorem r119_sharp_pred {A : C} {p q : Pred A} (hp : IsSharp p) (hq : IsSharp q) :
    SEA.seq (orth q) (SEA.seq p q) = SEA.seq (orth q) (SEA.seq (orth p) q) :=
  r119_sharp_seq (E := Pred A) (isIdempotent_of_isSharp hp) (isIdempotent_of_isSharp hq)
    fun _ hp' => rec115 (isSharp_orth hq) (isSharp_of_isIdempotent hp')

/-- REC 119 for a **sharp** `e` (vdW 2019, Prop. 46, sharp case): compressibility
(REC 112) at `e⊥` and `r119_sharp_pred`. -/
theorem r119_sharp_state {A : C} {p e : Pred A} (hp : IsSharp p) (he : IsSharp e)
    (ω : Stat A) (h : ω.1 ≫ e = 0) :
    ω.1 ≫ SEA.seq p e = ω.1 ≫ SEA.seq (orth p) e := by
  have ht : ω.1 ≫ truth A = 𝟙 _ := ω.2.trans truth_effObj_eq_id
  have h1 : ω.1 ≫ orth e = 𝟙 _ := by
    have := (comp_orth_eq_zero_iff ω.1 (orth e)).1 (by rw [eabasics_orth_orth]; exact h)
    rw [this, ht]
  rw [← rec112 (isSharp_orth he) ω h1 (SEA.seq p e),
    ← rec112 (isSharp_orth he) ω h1 (SEA.seq (orth p) e), r119_sharp_pred hp he]

/-- With Boolean scalars (`s = 1`) every predicate is sharp: `a & a⊥` is
self-summable (SEA 19), and a self-summable predicate is killed by every state. -/
theorem r119_bool (σs : ScalarSplit C) (h1 : σs.s = 𝟙 _) {A : C} (a : Pred A) :
    IsSharp a := by
  refine isSharp_of_isIdempotent ?_
  have hx := Papers.SEA.sea19_selfSummable a
  have h0 : SequentialEffectAlgebra.seq a (orth a) = 0 :=
    separatedByStates _ _ fun ω => by
      rw [FinPAC.comp_zero]
      exact σs.bool _ (by rw [h1, Category.comp_id]) (FinPAC.ovee_comp hx ω.1).1
  exact (Papers.SEA.isIdempotent_iff a).2 h0

end R119

/-! ### The level-set approximation (for step 4, convex case) -/

section R119Layer

open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [Papers.SEA.NormalSEA E] [EffectModule I E]
  {B : Type u} [CompleteBooleanAlgebra B] {X : Type u} [TopologicalSpace X]
  (Ψ : B → Set.Icc (0 : C(X, ℝ)) 1 → E)
  (hadd : ∀ (b b' : B) (f f' : Set.Icc (0 : C(X, ℝ)) 1) (_ : b ⊓ b' = ⊥)
    (hf : (f : C(X, ℝ)) + f' ≤ 1),
    ∃ h' : Perp (Ψ b f) (Ψ b' f'), Ψ (b ⊔ b') (kadd f f' hf) = ovee (Ψ b f) (Ψ b' f') h')

include hadd in
/-- `Ψ(⊥, f)` lies between `T := Σ_{j<n} (1/n)·Ψ(⊥, χ_{j+1})` and `T + (1/n)·1`, where
`χ_j` is the indicator of the clopen level set `cl {f > j/n}`; each `Ψ(⊥, χ_{j+1})`
is `≤ n·Ψ(⊥, f)` (the level sets `j ≥ 1` stay inside `{f ≥ 1/n}`). -/
theorem r119_layer (hED : ExtremallyDisconnected X) (f : Set.Icc (0 : C(X, ℝ)) 1)
    {n : ℕ} (hnpos : 0 < n) :
    ∃ χ : ℕ → Set.Icc (0 : C(X, ℝ)) 1, (∀ j, kmul (χ j) (χ j) = χ j) ∧
      (∀ j, GP.gmap (Ψ ⊥ (χ (j + 1))) ≤ (n : ℝ) • GP.gmap (Ψ ⊥ f)) ∧
      (∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • GP.gmap (Ψ ⊥ (χ (j + 1)))) ≤
        GP.gmap (Ψ ⊥ f) ∧
      GP.gmap (Ψ ⊥ f) ≤ (((1 : ℕ) : ℝ) / n) • GP.gunit +
        ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • GP.gmap (Ψ ⊥ (χ (j + 1))) := by
  set G : B → Set.Icc (0 : C(X, ℝ)) 1 → GP.Vec E := fun b f => GP.gmap (Ψ b f) with hG
  have hGadd := fun {b b' f f' k} hb hk => spec_G_add (E := E) Ψ hadd (b := b) (b' := b')
    (f := f) (f' := f') (k := k) hb hk
  have hG0 : G ⊥ kzero = 0 := by simp only [hG]; rw [spec_zero Ψ hadd, GP.gmap_zero]
  have hGnn : ∀ b f, 0 ≤ G b f := fun b f => GP.gmap_nonneg _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- partial sums `S j = min(f, j/n)` and layers
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
    kmk ((S (j + 1) : C(X, ℝ)) - S j)
      (fun t => by simp only [ContinuousMap.sub_apply]; linarith [hSmono j t])
      (fun t => by
        simp only [ContinuousMap.sub_apply]
        have := cIcc_le_one (S (j + 1)) t; have := cIcc_nonneg (S j) t; linarith)
  have hL : ∀ j t, (L j : C(X, ℝ)) t = (S (j + 1) : C(X, ℝ)) t - (S j : C(X, ℝ)) t :=
    fun j t => rfl
  -- the clopen level sets
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
  -- bounds on the layers
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
  -- `G ⊥ f` is the sum of the layers
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
  refine ⟨χ, fun j => kext fun t => ?_, fun j => ?_, ?_, ?_⟩
  · simp only [kmul_val, ContinuousMap.mul_apply, hχ]
    by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t} <;> simp [ht]
  · -- `(1/n)·χ_{j+1} ≤ f` pointwise
    have hm : G ⊥ (kscale (((1 : ℕ) : ℝ) / n) hn1 hn2 (χ (j + 1))) ≤ G ⊥ f := by
      refine spec_G_bot_mono Ψ hadd fun t => ?_
      simp only [kscale_val, ContinuousMap.smul_apply, smul_eq_mul, hχ]
      by_cases ht : t ∈ closure {t | ((j + 1 : ℕ) : ℝ) / n < (f : C(X, ℝ)) t}
      · rw [Set.indicator_of_mem ht, mul_one]
        refine le_trans ?_ (hWf (j + 1) t ht)
        exact div_le_div_of_nonneg_right (by push_cast; linarith) hnR.le
      · rw [Set.indicator_of_notMem ht, mul_zero]; exact cIcc_nonneg f t
    change GP.gmap (Ψ ⊥ _) ≤ GP.gmap (Ψ ⊥ f) at hm
    rw [spec_G_rat Ψ hadd (χ (j + 1)) hnpos 1 hn1 hn2] at hm
    have := smul_le_smul_of_nonneg_left hm (show (0 : ℝ) ≤ n from hnR.le)
    rw [_root_.smul_smul, Nat.cast_one, mul_one_div_cancel hnR.ne', one_smul] at this
    exact this
  · show ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) ≤ G ⊥ f
    rw [hGf]; exact Finset.sum_le_sum fun j _ => hlow j
  · -- `G ⊥ f ≤ Σ_{j<n} (1/n) G ⊥ χ_j ≤ (1/n)·1 + Σ_{j<n} (1/n) G ⊥ χ_{j+1}`
    have h1 : G ⊥ f ≤ ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) := by
      rw [hGf]; exact Finset.sum_le_sum fun j _ => hup j
    have h2 := Finset.sum_range_succ' (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
    have h3 := Finset.sum_range_succ (fun j => (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j)) n
    have h4 : G ⊥ (χ 0) ≤ GP.gunit := (gmap_mono (Papers.SEA.le_one' _) :
      GP.gmap (Ψ ⊥ (χ 0)) ≤ GP.gmap 1)
    have h5 : 0 ≤ (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) := smul_nonneg hn1 (hGnn _ _)
    have h6 : (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) ≤ (((1 : ℕ) : ℝ) / n) • GP.gunit :=
      smul_le_smul_of_nonneg_left h4 hn1
    have h7 : ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ j) =
        ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) +
          (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) - (((1 : ℕ) : ℝ) / n) • G ⊥ (χ n) := by
      rw [← h2, h3]; abel
    refine h1.trans (le_of_le_of_eq ?_ (add_comm _ _))
    rw [h7]
    calc _ ≤ ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • G ⊥ (χ (j + 1)) +
          (((1 : ℕ) : ℝ) / n) • G ⊥ (χ 0) := sub_le_self _ h5
      _ ≤ _ := add_le_add_right h6 _

end R119Layer

section R119Convex

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus
open scoped Papers.SEA

/-- REC 119 with convex scalars (`s = 0`): the spectral approximation of `a` by
idempotents that `ω` kills, in `V_A`. -/
theorem r119_convex (σs : ScalarSplit C) (hs0 : σs.s = 0) {A : C} {p a : Pred A}
    (hp : IsSharp p) (ω : Stat A) (ha : ω.1 ≫ a = 0) :
    ω.1 ≫ SEA.seq p a = ω.1 ≫ SEA.seq (orth p) a := by
  have hin : ∀ x : Pred A, x ≫ orth σs.s = x := fun x => by
    rw [hs0, eabasics_orth_zero, scal_one_eq, Category.comp_id]
  set p' : CPt σs A := cptMk σs p (hin p) with hp'
  set a' : CPt σs A := cptMk σs a (hin a) with ha'
  have hΩ1 : stateLin σs ω.1 GP.gunit = GP.gunit := by
    show stateLin σs ω.1 (GP.gmap 1) = GP.gmap 1
    rw [stateLin_gmap]; congr 1; apply Subtype.ext
    show ω.1 ≫ (truth A ≫ orth σs.s) = truth (effObj C) ≫ orth σs.s
    rw [← Category.assoc, ω.2]
  -- (Z): `Φ` vanishes on idempotents killed by `ω`
  have hZ : ∀ e : CPt σs A, Papers.SEA.IsIdempotent e → ω.1 ≫ e.1 = 0 →
      stateLin σs ω.1 (Dop σs p' (GP.gmap e)) = 0 := by
    intro e he h0
    have hes : IsSharp e.1 := isSharp_of_isIdempotent ((cpt_idem_iff σs e).1 he)
    rw [Dop, LinearMap.sub_apply, map_sub, Uop_gmap, Uop_gmap, stateLin_gmap, stateLin_gmap,
      sub_eq_zero]
    congr 1; apply Subtype.ext
    show ω.1 ≫ SEA.seq p'.1 e.1 = ω.1 ≫ SEA.seq (orth p').1 e.1
    rw [cpt_seq_orth]; exact r119_sharp_state hp hes ω h0
  -- (V): `ω` kills whatever is below a multiple of `a`
  have hΩa : stateLin σs ω.1 (GP.gmap a') = 0 := by
    rw [stateLin_gmap, ← GP.gmap_zero]; congr 1; exact Subtype.ext ha
  have hV : ∀ (e : CPt σs A) (c : ℝ), GP.gmap e ≤ c • GP.gmap a' → ω.1 ≫ e.1 = 0 := by
    intro e c hle
    have h1 := stateLin_nonneg σs ω.1 (sub_nonneg.2 hle)
    rw [map_sub, map_smul, hΩa, smul_zero, zero_sub, neg_nonneg] at h1
    have h2 := stateLin_nonneg σs ω.1 (GP.gmap_nonneg e)
    have h3 := le_antisymm h1 h2
    rw [stateLin_gmap] at h3
    exact congrArg (fun x : CPt σs (effObj C) => x.1)
      (GP.gmap_injective (h3.trans (GP.gmap_zero (E := CPt σs (effObj C))).symm))
  -- (Bd): `|Φ v| ≤ δ` for `0 ≤ v ≤ δ`
  have hBd : ∀ (v : VA σs A) (δ : ℝ), 0 ≤ δ → 0 ≤ v → v ≤ δ • GP.gunit →
      -(δ • GP.gunit) ≤ stateLin σs ω.1 (Dop σs p' v) ∧
        stateLin σs ω.1 (Dop σs p' v) ≤ δ • GP.gunit := by
    intro v δ hδ hv0 hv1
    have hU : ∀ q : CPt σs A, 0 ≤ stateLin σs ω.1 (Uop σs q v) ∧
        stateLin σs ω.1 (Uop σs q v) ≤ δ • GP.gunit := by
      intro q
      refine ⟨stateLin_nonneg σs ω.1 (Uop_nonneg σs q hv0), ?_⟩
      have h1 : Uop σs q v ≤ δ • GP.gunit := by
        have h := Uop_nonneg σs q (sub_nonneg.2 hv1)
        rw [map_sub, map_smul] at h
        have hq1 : Uop σs q GP.gunit ≤ GP.gunit := by
          rw [show (GP.gunit : VA σs A) = ouUnit (VA σs A) from rfl, Uop_unit]
          exact (gmap_mono (Papers.SEA.le_one' _) : GP.gmap q ≤ GP.gmap 1)
        exact (sub_nonneg.1 h).trans (smul_le_smul_of_nonneg_left hq1 hδ)
      have h2 := stateLin_nonneg σs ω.1 (sub_nonneg.2 h1)
      rw [map_sub, map_smul, hΩ1, sub_nonneg] at h2
      exact h2
    obtain ⟨u1, u2⟩ := hU p'
    obtain ⟨w1, w2⟩ := hU (orth p')
    rw [Dop, LinearMap.sub_apply, map_sub]
    refine ⟨?_, ?_⟩
    · have := sub_le_sub u1 w2; rwa [zero_sub] at this
    · have := sub_le_sub u2 w1; rwa [sub_zero] at this
  -- the spectral step
  obtain ⟨B, _, X, _, _, _, hED, Ψ, hadd, -, hmul, -, b, f, hbf⟩ := spectral_rep a'
  have eb : ∀ g, GP.gmap (Ψ b g) = GP.gmap (Ψ b kzero) + GP.gmap (Ψ ⊥ g) := fun g => by
    have := spec_G_add (E := CPt σs A) Ψ hadd (b := b) (b' := ⊥) (f := kzero) (f' := g)
      (k := g) (inf_bot_eq _) (fun t => by simp)
    rwa [sup_bot_eq] at this
  have hab : GP.gmap a' = GP.gmap (Ψ b kzero) + GP.gmap (Ψ ⊥ f) := by rw [← hbf, eb]
  have hb0 : stateLin σs ω.1 (Dop σs p' (GP.gmap (Ψ b kzero))) = 0 := by
    refine hZ _ (spec_idem Ψ hmul (kext fun t => by simp)) (hV _ 1 ?_)
    rw [one_smul, hab]; exact le_add_of_nonneg_right (GP.gmap_nonneg _)
  have hfa : GP.gmap (Ψ ⊥ f) ≤ GP.gmap a' := by
    rw [hab]; exact le_add_of_nonneg_left (GP.gmap_nonneg _)
  have hsmall : ∀ n : ℕ, 0 < n →
      -((((1 : ℕ) : ℝ) / n) • GP.gunit) ≤ stateLin σs ω.1 (Dop σs p' (GP.gmap a')) ∧
        stateLin σs ω.1 (Dop σs p' (GP.gmap a')) ≤ (((1 : ℕ) : ℝ) / n) • GP.gunit := by
    intro n hn
    obtain ⟨χ, hχi, hχb, hlo, hhi⟩ := r119_layer Ψ hadd hED f hn
    set T := ∑ j ∈ Finset.range n, (((1 : ℕ) : ℝ) / n) • GP.gmap (Ψ ⊥ (χ (j + 1))) with hT
    have hT0 : stateLin σs ω.1 (Dop σs p' T) = 0 := by
      rw [hT, map_sum, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, map_smul]
      refine (congrArg _ (hZ _ (spec_idem Ψ hmul (hχi (j + 1))) (hV _ n ?_))).trans
        (smul_zero _)
      exact (hχb j).trans (smul_le_smul_of_nonneg_left hfa (Nat.cast_nonneg n))
    have hdec : GP.gmap a' = GP.gmap (Ψ b kzero) + T + (GP.gmap (Ψ ⊥ f) - T) := by
      rw [hab]; abel
    have hv := hBd (GP.gmap (Ψ ⊥ f) - T) (((1 : ℕ) : ℝ) / n) (by positivity) (sub_nonneg.2 hlo)
      (by rw [sub_le_iff_le_add]; exact hhi)
    rw [hdec, map_add, map_add, map_add, map_add, hb0, hT0, zero_add, zero_add]
    exact hv
  have hΦ : stateLin σs ω.1 (Dop σs p' (GP.gmap a')) = 0 := by
    have := VA_isOUS σs (effObj C)
    refine eq_zero_of_ousNorm_small fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    have hnpos : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
      exact_mod_cast this
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    obtain ⟨h1, h2⟩ := hsmall n hnpos
    refine (ousNorm_le_rc (by positivity) h1 h2).trans ?_
    rw [Nat.cast_one, div_le_iff₀ hnR]
    rw [div_lt_iff₀ hε] at hn
    linarith
  rw [Dop, LinearMap.sub_apply, map_sub, Uop_gmap, Uop_gmap, stateLin_gmap, stateLin_gmap,
    sub_eq_zero] at hΦ
  have h := congrArg (fun x : CPt σs (effObj C) => x.1) (GP.gmap_injective hΦ)
  have h' : ω.1 ≫ SEA.seq p'.1 a'.1 = ω.1 ≫ SEA.seq (orth p').1 a'.1 := h
  rw [cpt_seq_orth] at h'
  exact h'

end R119Convex

/-! ### REC 119, and REC 102, 103, 136 without it -/

section Rec119Holds

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus

/-- **REC 119** (`lem:state-order-lemma`, short.tex:2165, Lemma), **proved**: in a
sequential effectus, for a sharp `p`, a predicate `a` and a (total) state `ω` with
`a ∘ ω = 0`, `(p & a) ∘ ω = (p⊥ & a) ∘ ω`.  The print's proof is a citation of van de
Wetering 2019 (arXiv v3), Prop. 46; its argument is carried out here with internal states:
the sharp case from compressibility (REC 112) and quadraticity (REC 115), then the
scalars are Boolean (every predicate sharp) or convex, where `a` is approximated in
`V_A` by idempotents that `ω` kills (the spectral theorem, REC 58). -/
theorem weteringStateOrderLemma_holds : WeteringStateOrderLemma C := by
  intro A p a ω hp ha
  obtain ⟨σs⟩ := scalarSplit_exists rec34_holds.{v} (normal (C := C)).1
  rcases rec102_trivial_factor σs with h0 | h1
  · exact r119_convex σs h0 hp ω ha
  · exact r119_sharp_state hp (r119_bool σs h1 a) ω ha

/-- **REC 102** (`thm:JB-embedding`, short.tex:1869, Theorem) with **no named
hypotheses**: `rec102_unconditional` with REC 119 discharged. -/
theorem rec102_hypfree :
    ∃ σs : ScalarSplit C,
      Nonempty (C ≌ (dcSplitting σs separatedByStates).ε.Part ×
        (dcSplitting σs separatedByStates).ε'.Part) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε.Part, Nonempty (CBAOn (Pred P))) ∧
      (∀ P : (dcSplitting σs separatedByStates).ε'.Part,
        ∃ _ : Mul (VA σs P.obj.X), JBAlgebra (VA σs P.obj.X) ∧
          IsDirectedCompleteOUS (VA σs P.obj.X) ∧
          ∃ e : Pred P ≃ Set.Icc (0 : VA σs P.obj.X) (ouUnit (VA σs P.obj.X)),
            (∀ a b : Pred P, a ≼ b ↔ (e a : VA σs P.obj.X) ≤ e b) ∧
            (∀ (a b : Pred P) (h : Perp a b), (e (ovee a b h) : VA σs P.obj.X) = e a + e b) ∧
            (e (truth P) : VA σs P.obj.X) = ouUnit (VA σs P.obj.X)) ∧
      ((rec102_cbaFunctor σs).Faithful ∧
          (rec102_jbFunctor σs alfsenShultzResolventCriterion_holds
            weteringStateOrderLemma_holds).Faithful ↔
        SeparatingPredicates C) :=
  rec102_unconditional weteringStateOrderLemma_holds

/-- **REC 103** (`thm:JBW-CBA`, short.tex:1874, Theorem) with **no named
hypotheses**: `rec103_unconditional` with REC 119 discharged. -/
theorem rec103_hypfree (hirr : IsIrreducible (Scal C)) :
    (∃ hB : ∀ A : C, CBAOn (Pred A), (cbaPredFunctor hB).Faithful ↔ SeparatingPredicates C) ∨
    (∃ (σs : ScalarSplit C) (hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _
        (jbMul σs alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds A)),
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : VA σs A) (ouUnit (VA σs A)),
        (∀ a b : Pred A, a ≼ b ↔ (e a : VA σs A) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b), (e (ovee a b h) : VA σs A) = e a + e b) ∧
        (e (truth A) : VA σs A) = ouUnit (VA σs A)) ∧
      ((rec103_jbwFunctor alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds
          σs hJBW).Faithful ↔
        SeparatingPredicates C)) :=
  rec103_unconditional weteringStateOrderLemma_holds hirr

open MonoidalCategory in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem) with REC 119 discharged.
Remaining named hypotheses: REC 52 (`hHOS`), REC 55 (`hSh`), REC 132 (`hAS4`). -/
theorem rec136_hypfree [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C]
    (hHOS : HancheOlsenStormerDecomposition.{v}) (hSh : ShultzExceptionalStructure.{v})
    (hAS4 : AlfsenShultzFourExchangeable.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_unconditional weteringStateOrderLemma_holds hHOS hSh hAS4 hirr h01

end Rec119Holds

end Papers.REC

#print axioms Papers.REC.weteringStateOrderLemma_holds
#print axioms Papers.REC.rec102_hypfree
#print axioms Papers.REC.rec103_hypfree
#print axioms Papers.REC.rec136_hypfree
