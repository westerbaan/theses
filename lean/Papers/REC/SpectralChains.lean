import Papers.REC.Reconstruction

/-!
# REC 121: chain density of `V_A` with commuting chain members

Research note `docs/research/as943-transplant.md` (§7 and its Review, item 6): the
9.43 transplant needs, besides the Jordan symmetry, (G1) a norm-dense set of *chain*
combinations `λ₀·1 + Σ_k α_k e_{j_k}` with `α_k ≥ 0` and `e_{j_1} ≥ e_{j_2} ≥ …`, and
(G2) `U_{j_k} U_{c j_{k'}} = U_{c j_{k'}} U_{j_k}` for the members of each chain.

`spectral_dense_core`'s list `[(2N, Ψ(b,0)), (−N, 1), (2N/n, Ψ(⊥,χ_j))]` is not a chain
(`Ψ(b,0)` and `Ψ(⊥,χ_j)` are orthogonal).  Here the same vector is rewritten as
`−N·1 + Σ_j (2N/n)·Ψ(b,χ_j)`: the members `Ψ(b,χ_j)` are idempotent (`spec_idem`),
nested (`χ_{j'} ≤ χ_j` for `j ≤ j'`, then `spec_G_add`), and pairwise `⊙`-commuting
(range of the multiplicative `Ψ`), hence their compressions commute with each other's
complements (`Commutes.orth_r`, `Commutes.assoc`, `gp_linearMap_ext`).

* `spectral_chain_core` — the chain form of `spectral_dense_core`.
* `spectral_chain` — every `w ∈ GP.Vec E` is a norm limit of chains of pairwise
  commuting idempotents.
* `va_chainDense` — `ChainDense` (defined in `Reconstruction.lean`) for exactly the
  family `(ι, e, U, c)` that `rec121` feeds to `jb_of_chainDense`.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v

section SpecChain

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]
  {B : Type u} [CompleteBooleanAlgebra B] {X : Type u} [TopologicalSpace X]
  (Ψ : B → Set.Icc (0 : C(X, ℝ)) 1 → E)
  (hadd : ∀ (b b' : B) (f f' : Set.Icc (0 : C(X, ℝ)) 1) (_ : b ⊓ b' = ⊥)
    (hf : (f : C(X, ℝ)) + f' ≤ 1),
    ∃ h' : Perp (Ψ b f) (Ψ b' f'), Ψ (b ⊔ b') (kadd f f' hf) = ovee (Ψ b f) (Ψ b' f') h')
  (hmul : ∀ b b' f f', Ψ (b ⊓ b') (kmul f f') = Ψ b f ⊙ Ψ b' f')

include hadd in
/-- **The chain form of `spectral_dense_core`**: `2N·Ψ(b,f) - N·1` is within `ε` of
`−N·1 + Σ_{j<n} (2N/n)·Ψ(b,χ_j)`, with `χ_j` the indicators of the clopen level sets
`closure {f > j/n}`: idempotent and decreasing in `j`. -/
theorem spectral_chain_core (hED : ExtremallyDisconnected X) (hone : Ψ ⊤ kone = 1)
    {N : ℝ} (hN : 0 < N) (b : B) (f : Set.Icc (0 : C(X, ℝ)) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (χ : ℕ → Set.Icc (0 : C(X, ℝ)) 1),
      (∀ j, kmul (χ j) (χ j) = χ j) ∧
      (∀ j j', j ≤ j' → ∀ t, (χ j' : C(X, ℝ)) t ≤ (χ j : C(X, ℝ)) t) ∧
      ousNorm (GP.Vec E) (((2 * N) • GP.gmap (Ψ b f) - N • GP.gunit) -
        ((-N) • GP.gunit + ∑ k : Fin n, (2 * N / n) • GP.gmap (Ψ b (χ k)))) < ε := by
  set G : B → Set.Icc (0 : C(X, ℝ)) 1 → GP.Vec E := fun b f => GP.gmap (Ψ b f) with hG
  have hGadd := fun {b b' f f' k} hb hk => spec_G_add (E := E) Ψ hadd (b := b) (b' := b')
    (f := f) (f' := f') (k := k) hb hk
  have hG0 : G ⊥ kzero = 0 := by simp only [hG]; rw [spec_zero Ψ hadd, GP.gmap_zero]
  have hGnn : ∀ b f, 0 ≤ G b f := fun b f => GP.gmap_nonneg _
  -- choose `n` with `2N/n < ε`
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * N / ε)
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnε : 2 * N / n < ε := by
    rw [div_lt_iff₀ hnR]; rw [div_lt_iff₀ hε] at hn; linarith
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
    kmk ((S (j + 1) : C(X, ℝ)) - S j) (fun t => by simp only [ContinuousMap.sub_apply]; linarith [hSmono j t])
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
  -- the chain
  refine ⟨n, χ, fun j => kext fun t => ?_, fun j j' hjj' t => ?_, ?_⟩
  · simp only [kmul_val, ContinuousMap.mul_apply, hχ]
    by_cases ht : t ∈ closure {t | (j : ℝ) / n < (f : C(X, ℝ)) t} <;> simp [ht]
  · rw [hχ, hχ]
    refine Set.indicator_le_indicator_of_subset (closure_mono fun s hs => ?_)
      (fun _ => zero_le_one) t
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by exact_mod_cast hjj') hnR.le) hs
  · -- `G b χ_j = G b 0 + G ⊥ χ_j`
    have eb : ∀ g, G b g = G b kzero + G ⊥ g := fun g => by
      have := hGadd (b := b) (b' := ⊥) (f := kzero) (f' := g) (k := g) (inf_bot_eq _)
        (fun t => by simp)
      rwa [sup_bot_eq] at this
    have hsumC : ∑ k : Fin n, (2 * N / n) • GP.gmap (Ψ b (χ k)) =
        (2 * N) • G b kzero + (2 * N) • T := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (2 * N / n) • GP.gmap (Ψ b (χ j))) n]
      show ∑ j ∈ Finset.range n, (2 * N / n) • G b (χ j) = _
      rw [Finset.sum_congr rfl fun j _ => by rw [eb (χ j), smul_add], Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range]
      rw [hT, Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℝ, _root_.smul_smul,
        mul_div_cancel₀ _ hnR.ne']
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [_root_.smul_smul]; congr 1; push_cast; ring
    have hdiff : ((2 * N) • GP.gmap (Ψ b f) - N • GP.gunit) -
        ((-N) • GP.gunit + ∑ k : Fin n, (2 * N / n) • GP.gmap (Ψ b (χ k))) =
          (2 * N) • (G ⊥ f - T) := by
      rw [hsumC]
      show (2 * N) • G b f - _ - _ = _
      rw [eb f]; module
    rw [hdiff]
    refine lt_of_le_of_lt (ousNorm_le_rc (by positivity) ?_ ?_) hnε
    · have h1 : -((((1 : ℕ) : ℝ) / n) • GP.gunit) ≤ G ⊥ f - T := by
        rw [neg_le_sub_iff_le_add]; rw [sub_le_iff_le_add] at hTf
        exact hTf
      have := smul_le_smul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * N by positivity)
      calc -((2 * N / n) • GP.gunit) = (2 * N) • -((((1 : ℕ) : ℝ) / n) • GP.gunit) := by
            rw [smul_neg, _root_.smul_smul]; congr 2; push_cast; ring
        _ ≤ _ := this
    · have h1 : G ⊥ f - T ≤ 0 := sub_nonpos.2 hfT
      calc (2 * N) • (G ⊥ f - T) ≤ 0 := smul_nonpos_of_nonneg_of_nonpos (by positivity) h1
        _ ≤ (2 * N / n) • GP.gunit := smul_nonneg (by positivity) (GP.gmap_nonneg _)

end SpecChain

section SpecChainTop

open Papers.SEA
open scoped Papers.SEA

variable {E : Type u} [EffectAlgebra E] [NormalSEA E] [EffectModule I E]

/-- **Chain density of sharp combinations** (REC 58 in chain form, G1 + G2 of the
9.43 transplant): every `w ∈ V` is a norm limit of `l0·1 + Σ_k α_k q_k` with `α_k ≥ 0`,
`q_k` idempotent, `q_k` decreasing in `k`, and the `q_k` pairwise commuting. -/
theorem spectral_chain (w : GP.Vec E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (l0 : ℝ) (α : Fin n → ℝ) (q : Fin n → E),
      (∀ k, Papers.SEA.IsIdempotent (q k)) ∧ (∀ k, 0 ≤ α k) ∧
      (∀ k k' : Fin n, k ≤ k' → GP.gmap (q k') ≤ GP.gmap (q k)) ∧
      (∀ k k', Commutes (q k) (q k')) ∧
      ousNorm (GP.Vec E) (w - (l0 • GP.gunit + ∑ k, α k • GP.gmap (q k))) < ε := by
  obtain ⟨N, a, hN, rfl⟩ := gp_affine_repr w
  obtain ⟨B, _, X, _, _, _, hED, Ψ, hadd, hone, hmul, -, b, f, rfl⟩ := spectral_rep a
  obtain ⟨n, χ, hχi, hχm, hnorm⟩ := spectral_chain_core Ψ hadd hED hone hN b f hε
  refine ⟨n, -N, fun _ => 2 * N / n, fun k => Ψ b (χ k), fun k => spec_idem Ψ hmul (hχi k),
    fun _ => by positivity, fun k k' hkk' => ?_, fun k k' => ?_, hnorm⟩
  · have eb : ∀ g, GP.gmap (Ψ b g) = GP.gmap (Ψ b kzero) + GP.gmap (Ψ ⊥ g) := fun g => by
      have := spec_G_add (E := E) Ψ hadd (b := b) (b' := ⊥) (f := kzero) (f' := g) (k := g)
        (inf_bot_eq _) (fun t => by simp)
      rwa [sup_bot_eq] at this
    show GP.gmap (Ψ b (χ k')) ≤ GP.gmap (Ψ b (χ k))
    rw [eb, eb (χ k)]
    exact add_le_add le_rfl (spec_G_bot_mono Ψ hadd (hχm k k' hkk'))
  · show Ψ b (χ k) ⊙ Ψ b (χ k') = Ψ b (χ k') ⊙ Ψ b (χ k)
    have hc : kmul (χ k) (χ k') = kmul (χ k') (χ k) := kext fun t => by
      simp only [kmul_val, ContinuousMap.mul_apply]; ring
    rw [← hmul, ← hmul, hc]

end SpecChainTop

section VAChain

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]

open SequentialEffectus
open scoped Papers.SEA

variable (σs : ScalarSplit C)

/-- **G1 + G2 for REC's `V_A`**: chain density with commuting chain members, for exactly
the family `rec121` feeds to `jb_of_chainDense` — `ι` the idempotents
of the convex part, `e i = gmap i`, `U i = Uop i`, `c i = orth i`.  No hypotheses. -/
theorem va_chainDense (A : C) :
    ChainDense (VA σs A) {q : CPt σs A // Papers.SEA.IsIdempotent q}
      (fun i => GP.gmap i.1) (fun i => Uop σs i.1) (fun i => ⟨orth i.1, i.2.compl⟩) := by
  intro w ε hε
  obtain ⟨n, l0, α, q, hq, hα, hnest, hcomm, hnorm⟩ := spectral_chain w hε
  refine ⟨n, l0, α, fun k => ⟨q k, hq k⟩, hα, hnest, fun k k' => ?_, hnorm⟩
  have h : Papers.SEA.Commutes (q k) (orth (q k')) := (hcomm k k').orth_r
  refine gp_linearMap_ext fun x => ?_
  show Uop σs (q k) (Uop σs (orth (q k')) (GP.gmap x)) =
    Uop σs (orth (q k')) (Uop σs (q k) (GP.gmap x))
  rw [Uop_gmap, Uop_gmap, Uop_gmap, Uop_gmap, h.assoc, h.symm.assoc, h]

end VAChain

end Papers.REC

#print axioms Papers.REC.va_chainDense
