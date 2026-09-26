/-
Papers/SIG/Normalisation.lean

SIG §4 "Separation properties and normalization" (main.tex:1024–1158) with
its proofs in Appendix B (main.tex:2851–3033), points SIG 36, 38, 39, 40:
predicate-, substate- and state-separation, normalisation, and the
equivalence of normalisation with division, absence of zero divisors and
epicity of nonzero scalars in a σ-effectus.  (SIG 37 needs the functors
`Pred` and `sSt` of SIG 29/34 and lives with them.)
-/
import Papers.SIG.SigmaEffectus

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff

namespace Papers.SIG

open SigmaPAM

universe u v

/-! ## Definitions, in any effectus -/

section Effectus

variable (C : Type u) [Category.{v} C] [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)]
  [FinPAC C] [EffectusPartialForm C]

/-- **SIG 36** (main.tex:1035, Definition): an effectus is
**predicate-separated** when `p ∘ f = p ∘ g` for all predicates `p` implies
`f = g` (the tree's `SeparatingPredicates`, 190II.7). -/
def PredicateSeparated : Prop :=
  ∀ ⦃A B : C⦄ (f g : A ⟶ B), (∀ p : Pred B, f ≫ p = g ≫ p) → f = g

theorem predicateSeparated_iff : PredicateSeparated C ↔ SeparatingPredicates C := Iff.rfl

/-- **SIG 36** (main.tex:1040, Definition): an effectus is
**substate-separated** when `f ∘ ω = g ∘ ω` for all substates `ω` implies
`f = g`. -/
def SubstateSeparated : Prop :=
  ∀ ⦃A B : C⦄ (f g : A ⟶ B), (∀ ω : Substate A, ω ≫ f = ω ≫ g) → f = g

/-- **SIG 36** (text after SIG 37, main.tex:1073): an effectus is
**state-separated** when `f ∘ ω = g ∘ ω` for all states `ω` implies `f = g`
(the tree's `SeparatingStates`, 190II.7). -/
def StateSeparated : Prop :=
  ∀ ⦃A B : C⦄ (f g : A ⟶ B), (∀ ω : Stat A, ω.1 ≫ f = ω.1 ≫ g) → f = g

theorem stateSeparated_iff : StateSeparated C ↔ SeparatingStates C := Iff.rfl

/-- **SIG 38** (main.tex:1088, Definition): an effectus **admits
normalization** if for each nonzero substate `ω : I ⟶ A` there is a unique
state `ω̄` with `ω = ω̄ ∘ (1 ∘ ω)`. -/
def AdmitsNormalisation : Prop :=
  ∀ (A : C) (ω : Substate A), ω ≠ 0 →
    ∃! ωb : Substate A, IsTotal ωb ∧ ω = (ω ≫ truth A) ≫ ωb

/-- **SIG 40** (ii) (`thm:normalisation-equiv`, main.tex:1120): the effect
monoid of scalars **admits division**: for `s ≤ t` with `t ≠ 0` there is a
unique `s/t` with `(s/t) · t = s`. -/
def AdmitsDivision : Prop :=
  ∀ s t : Scal C, s ≼ t → t ≠ 0 → ∃! r : Scal C, r * t = s

/-- **SIG 40** (iii) (main.tex:1124): the scalars have **no nontrivial zero
divisors**: `s · t = 0` implies `s = 0` or `t = 0`. -/
def ScalarsNoZeroDivisors : Prop :=
  ∀ s t : Scal C, s * t = 0 → s = 0 ∨ t = 0

/-- **SIG 40** (iv) (main.tex:1128): every nonzero scalar is an epi. -/
def NonzeroScalarsEpi : Prop :=
  ∀ s : Scal C, s ≠ 0 → Epi s

variable {C}

/-- **SIG 39** (`prop:state-sep-equiv-substate-sep`, main.tex:1097,
Proposition): a (σ-)effectus with normalization is state-separated iff it is
substate-separated.  (Proof as printed in Appendix B.) -/
theorem stateSeparated_iff_substateSeparated (hN : AdmitsNormalisation C) :
    StateSeparated C ↔ SubstateSeparated C := by
  constructor
  · -- "only if" (printed: "obvious"): states are substates
    intro h A B f g hfg
    exact h f g fun ω => hfg ω.1
  · intro h A B f g hfg
    refine h f g fun ρ => ?_
    by_cases hρ : ρ = 0
    · rw [hρ, FinPAC.zero_comp, FinPAC.zero_comp]
    · obtain ⟨ρb, ⟨hρb, e⟩, -⟩ := hN A ρ hρ
      have hb : ρb ≫ f = ρb ≫ g := hfg ⟨ρb, hρb⟩
      calc ρ ≫ f = ((ρ ≫ truth A) ≫ ρb) ≫ f := by rw [← e]
        _ = (ρ ≫ truth A) ≫ (ρb ≫ f) := Category.assoc _ _ _
        _ = (ρ ≫ truth A) ≫ (ρb ≫ g) := by rw [hb]
        _ = ((ρ ≫ truth A) ≫ ρb) ≫ g := (Category.assoc _ _ _).symm
        _ = ρ ≫ g := by rw [← e]

/-- Pairing with equal components gives equal maps. -/
theorem effPair_congr {Z X Y : C} {f f' : Z ⟶ X} {g g' : Z ⟶ Y} (hf : f = f') (hg : g = g')
    (h : Perp (f ≫ truth X) (g ≫ truth Y)) (h' : Perp (f' ≫ truth X) (g' ≫ truth Y)) :
    effPair f g h = effPair f' g' h' := by
  subst hf; subst hg; rfl

/-- **SIG 40**, (i) ⇒ (ii) (main.tex:2876, citing [Cho15, Prop. 6.4]): in an
effectus, normalisation gives division.  Our proof: for `s ⊕ d = t ≠ 0`
normalise the substate `ω = ⟨s, d⟩ : I → I + I` to `ω̄` and put
`s/t = ▷₁ ∘ ω̄`; any `r` with `r · t = s` gives the state `⟨r, r^⊥⟩` whose
restriction along `t` is `ω`, so it is `ω̄`. -/
theorem admitsDivision_of_admitsNormalisation (hN : AdmitsNormalisation C) :
    AdmitsDivision C := by
  intro s t hst ht
  obtain ⟨d, hsd, hd⟩ := hst
  have hI : truth (effObj C) = 𝟙 (effObj C) := truth_effObj_eq_id
  have hp : Perp (s ≫ truth (effObj C)) (d ≫ truth (effObj C)) := by
    rw [hI, Category.comp_id, Category.comp_id]; exact hsd
  set ω := effPair s d hp with hωdef
  have hω1 : ω ≫ truth (effObj C ⨿ effObj C) = t := by
    rw [eff_prod_rules_2, ← hd]
    exact PCM.ovee_congr (by rw [hI, Category.comp_id]) (by rw [hI, Category.comp_id]) _ _
  have hω0 : ω ≠ 0 := fun h => ht (by rw [← hω1, h, FinPAC.zero_comp])
  obtain ⟨ωb, ⟨hωb, hωe⟩, huniq⟩ := hN _ ω hω0
  refine ⟨ωb ≫ pproj₁ (effObj C) (effObj C), ?_, ?_⟩
  · show t ≫ ωb ≫ pproj₁ (effObj C) (effObj C) = s
    rw [← hω1, ← Category.assoc, ← hωe]
    exact (effPair_spec s d hp).1
  · intro r hr
    have hr' : t ≫ r = s := hr
    have hq : Perp (r ≫ truth (effObj C)) (orth r ≫ truth (effObj C)) := by
      rw [hI, Category.comp_id, Category.comp_id]; exact EffectAlgebra.perp_orth r
    set ρ := effPair r (orth r) hq with hρdef
    have hρtot : IsTotal ρ := by
      show ρ ≫ truth (effObj C ⨿ effObj C) = truth (effObj C)
      rw [eff_prod_rules_2]
      refine (PCM.ovee_congr (by rw [hI, Category.comp_id]) (by rw [hI, Category.comp_id]) _
        (EffectAlgebra.perp_orth r)).trans ?_
      exact EffectAlgebra.ovee_orth r
    -- `t ∘ r^⊥ = d`, by cancellation from `t ∘ r ⊕ t ∘ r^⊥ = t ∘ 1 = t = s ⊕ d`
    have htd : t ≫ orth r = d := by
      obtain ⟨h1, e1⟩ := FinPAC.ovee_comp (EffectAlgebra.perp_orth r) t
      have e2 : ovee (t ≫ r) (t ≫ orth r) h1 = t := by
        rw [← e1, EffectAlgebra.ovee_orth]
        show t ≫ truth (effObj C) = t
        rw [hI, Category.comp_id]
      have h1' : Perp s (t ≫ orth r) := by rw [← hr']; exact h1
      have e3 : ovee s (t ≫ orth r) h1' = ovee s d hsd :=
        (PCM.ovee_congr hr'.symm rfl h1' h1).trans (e2.trans hd.symm)
      exact eabasics_cancellation (PCM.perp_comm h1') (PCM.perp_comm hsd)
        ((PCM.ovee_comm _).symm.trans (e3.trans (PCM.ovee_comm _)))
    have hq' : Perp ((t ≫ r) ≫ truth (effObj C)) ((t ≫ orth r) ≫ truth (effObj C)) := by
      rw [hr', htd]; exact hp
    have htρ : t ≫ ρ = ω := by
      rw [hρdef, eff_prod_rules_4 r (orth r) hq t hq', hωdef]
      exact effPair_congr hr' htd _ _
    have := huniq ρ ⟨hρtot, by rw [hω1]; exact htρ.symm⟩
    show r = ωb ≫ pproj₁ (effObj C) (effObj C)
    rw [← this]
    exact (effPair_spec r (orth r) hq).1.symm

/-- **SIG 40**, (ii) ⇒ (iii) (main.tex:2881, as printed): if
`s · t = 0` and `t ≠ 0`, then both `s` and `0` divide `s · t = 0` by `t`, so
`s = 0`. -/
theorem noZeroDivisors_of_admitsDivision (hD : AdmitsDivision C) :
    ScalarsNoZeroDivisors C := by
  intro s t hst
  by_cases ht : t = 0
  · exact Or.inr ht
  · left
    obtain ⟨r, -, hr⟩ := hD (s * t) t (emon_mul_le_self_right s t) ht
    rw [hr s rfl, hr 0 (by rw [hst]; exact (exc_emonzero t).2)]

/-- **SIG 40**, (iv) ⇒ (iii) (main.tex:2997, as printed). -/
theorem noZeroDivisors_of_nonzeroScalarsEpi (hE : NonzeroScalarsEpi C) :
    ScalarsNoZeroDivisors C := by
  intro s t hst
  by_cases ht : t = 0
  · exact Or.inr ht
  · left
    have := hE t ht
    refine (cancel_epi t).1 ?_
    rw [FinPAC.comp_zero]
    exact hst

/-- **SIG 40**, (i) ⇒ (iv) (main.tex:3007, as printed, using (ii) and
(iii)). -/
theorem nonzeroScalarsEpi_of_admitsNormalisation (hN : AdmitsNormalisation C)
    (hZ : ScalarsNoZeroDivisors C) : NonzeroScalarsEpi C := by
  have hD := admitsDivision_of_admitsNormalisation hN
  intro s hs
  constructor
  intro A ω₁ ω₂ he
  -- nonzero substates stay nonzero after `s`
  have key : ∀ {ω : Substate A}, ω ≠ 0 → s ≫ ω ≠ 0 := by
    intro ω hω h
    have h1 : (ω ≫ truth A) * s = 0 := by
      show s ≫ ω ≫ truth A = 0
      rw [← Category.assoc, h, FinPAC.zero_comp]
    rcases hZ _ _ h1 with h2 | h2
    · exact hω (EffectusPartialForm.eq_zero_of_one_zero h2)
    · exact hs h2
  by_cases h₁ : ω₁ = 0
  · by_cases h₂ : ω₂ = 0
    · rw [h₁, h₂]
    · exact absurd (by rw [← he, h₁, FinPAC.comp_zero]) (key h₂)
  by_cases h₂ : ω₂ = 0
  · exact absurd (by rw [he, h₂, FinPAC.comp_zero]) (key h₁)
  -- `t = 1 ∘ ω₁ ∘ s = 1 ∘ ω₂ ∘ s ≠ 0`, and `1 ∘ ω₁ = t/s = 1 ∘ ω₂`
  set t := s ≫ ω₁ ≫ truth A with ht
  have ht₂ : t = s ≫ ω₂ ≫ truth A := by rw [ht, ← Category.assoc, he, Category.assoc]
  have ht0 : t ≠ 0 := by
    intro h
    exact key h₁ (EffectusPartialForm.eq_zero_of_one_zero (by rw [Category.assoc]; exact h))
  obtain ⟨r, -, hr⟩ := hD t s (emon_mul_le_self_right (ω₁ ≫ truth A) s) hs
  have hq : ω₁ ≫ truth A = ω₂ ≫ truth A :=
    (hr _ ht.symm).trans (hr _ ht₂.symm).symm
  -- normalise `ω₁`, `ω₂`, and compare the normalisations of `ω₁ ∘ s`
  obtain ⟨ω₁b, ⟨hω₁b, e₁⟩, -⟩ := hN A ω₁ h₁
  obtain ⟨ω₂b, ⟨hω₂b, e₂⟩, -⟩ := hN A ω₂ h₂
  have hρ : s ≫ ω₁ ≠ 0 := key h₁
  obtain ⟨ρb, -, hu⟩ := hN A (s ≫ ω₁) hρ
  have hρt : (s ≫ ω₁) ≫ truth A = t := by rw [Category.assoc]
  have h1 : ω₁b = ρb := hu ω₁b ⟨hω₁b, by
    rw [hρt, ht, Category.assoc, ← e₁]⟩
  have h2 : ω₂b = ρb := hu ω₂b ⟨hω₂b, by
    rw [hρt, ht₂, Category.assoc, ← e₂, he]⟩
  calc ω₁ = (ω₁ ≫ truth A) ≫ ω₁b := e₁
    _ = (ω₂ ≫ truth A) ≫ ω₂b := by rw [hq, h1, h2]
    _ = ω₂ := e₂.symm

end Effectus

/-! ## In a σ-effectus -/

section Sigma

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- A binary sum of predicates, as a σ-sum. -/
theorem sumsTo_orth {A : C} (p : Pred A) : SumsTo ![p, orth p] (truth A) :=
  ⟨EffectAlgebra.perp_orth p, EffectAlgebra.ovee_orth p⟩

theorem pair_comp_left {X Y Z : C} {a b s : X ⟶ Y} (h : SumsTo ![a, b] s) (k : Y ⟶ Z) :
    SumsTo ![a ≫ k, b ≫ k] (s ≫ k) :=
  (sumsTo_congr (by intro i; fin_cases i <;> rfl)).1 (comp_sumsTo_left k h)

theorem pair_comp_right {W X Y : C} {a b s : X ⟶ Y} (h : SumsTo ![a, b] s) (k : W ⟶ X) :
    SumsTo ![k ≫ a, k ≫ b] (k ≫ s) :=
  (sumsTo_congr (by intro i; fin_cases i <;> rfl)).1 (comp_sumsTo_right k h)

/-- Cancellation in `Pred A`, for σ-sums. -/
theorem pred_cancel {A : C} {a b c s : Pred A} (h₁ : SumsTo ![a, c] s)
    (h₂ : SumsTo ![b, c] s) : a = b := by
  obtain ⟨p₁, e₁⟩ := h₁
  obtain ⟨p₂, e₂⟩ := h₂
  exact eabasics_cancellation p₁ p₂ (e₁.trans e₂.symm)

/-- The countable form of effectus axiom (iii): a family whose truths are
summable is summable.  (Needed by SIG 40 and SIG 69; it follows from the
binary axiom, PCM associativity and the limit axiom.) -/
theorem summable_of_summable_truth {J : Type} [Countable J] {A B : C} (g : J → (A ⟶ B))
    (h : Summable (fun j => g j ≫ truth B)) : Summable g := by
  -- families over `Fin n`, by induction
  have hfin : ∀ (n : ℕ) (g : Fin n → (A ⟶ B)), Summable (fun j => g j ≫ truth B) →
      Summable g := by
    intro n
    induction n with
    | zero => intro g _; exact summable_of_isEmpty g
    | succ n ih =>
      intro g hg
      obtain ⟨u, hu, hul⟩ := (sumsTo_fin_last_iff _ _).1 (sumsTo_sum hg)
      obtain ⟨σ, hσ⟩ : ∃ σ, SumsTo (fun i : Fin n => g i.castSucc) σ :=
        ⟨_, sumsTo_sum (ih _ hu.summable)⟩
      have h1 := comp_sumsTo_left (truth B) hσ
      have hu' : u = σ ≫ truth B := hu.unique h1
      rw [hu'] at hul
      have hp : Perp σ (g (Fin.last n)) := EffectusPartialForm.perp_of_one_perp hul.summable
      exact ((sumsTo_fin_last_iff g _).2 ⟨σ, hσ, sumsTo_sum hp⟩).summable
  refine limit g fun F => ?_
  let e : Fin F.card ≃ F := F.equivFin.symm
  have h1 : Summable (fun i : Fin F.card => g (e i).1 ≫ truth B) :=
    summable_comp_injective h (fun i => (e i).1) fun i j hij => e.injective (Subtype.ext hij)
  have h2 := hfin _ (fun i => g (e i).1) h1
  exact ((sumsTo_comp_equiv' e.symm (fun i : Fin F.card => g (e i).1) (fun j : F => g j.1)
    (by intro j; simp) _).2 (sumsTo_sum h2)).summable

/-- Powers `sⁿ` of a scalar, `s^{n+1} = sⁿ ∘ s`. -/
noncomputable def spow (s : Scal C) : ℕ → Scal C
  | 0 => 𝟙 _
  | n + 1 => s ≫ spow s n

theorem spow_comm (s : Scal C) (n : ℕ) : s ≫ spow s n = spow s n ≫ s := by
  induction n with
  | zero => simp [spow]
  | succ n ih =>
    show s ≫ (s ≫ spow s n) = (s ≫ spow s n) ≫ s
    calc s ≫ (s ≫ spow s n) = s ≫ (spow s n ≫ s) := by rw [ih]
      _ = (s ≫ spow s n) ≫ s := (Category.assoc _ _ _).symm

/-- Scalars commute with orthocomplements: `s ∘ s^⊥ = s^⊥ ∘ s`. -/
theorem orth_comm (s : Scal C) : s ≫ orth s = orth s ≫ s := by
  have hI : truth (effObj C) = 𝟙 (effObj C) := truth_effObj_eq_id
  have h1 := pair_comp_left (sumsTo_orth s) s
  have h2 := pair_comp_right (sumsTo_orth s) s
  rw [hI, Category.id_comp] at h1
  rw [hI, Category.comp_id] at h2
  exact pred_cancel (sumsTo_pair_comm h2) (sumsTo_pair_comm h1)

theorem orth_spow_comm (s : Scal C) (n : ℕ) : orth s ≫ spow s n = spow s n ≫ orth s := by
  induction n with
  | zero => simp [spow]
  | succ n ih =>
    simp only [spow]
    rw [← Category.assoc, ← orth_comm, Category.assoc, ih, Category.assoc]

/-- The telescoping partial sums `s^⊥ ⊕ s^⊥ s ⊕ ⋯ ⊕ s^⊥ s^N ⊕ s^{N+1} = 1`. -/
theorem telescope (s : Scal C) (N : ℕ) :
    ∃ σ, SumsTo (fun i : Fin (N + 1) => spow s i ≫ orth s) σ ∧
      SumsTo ![σ, spow s (N + 1)] (𝟙 (effObj C)) := by
  have hI : truth (effObj C) = 𝟙 (effObj C) := truth_effObj_eq_id
  have hso : SumsTo ![orth s, s] (𝟙 (effObj C)) := by
    rw [← hI]
    have := sumsTo_orth (orth s)
    rwa [eabasics_orth_orth] at this
  induction N with
  | zero =>
    refine ⟨orth s, ?_, ?_⟩
    · have := sumsTo_of_unique' (fun i : Fin 1 => spow s i ≫ orth s) 0
      simpa [spow] using this
    · simpa [spow] using hso
  | succ N ih =>
    obtain ⟨σ, hσ, hσs⟩ := ih
    -- `s^{N+1} = s^{N+1} s^⊥ ⊕ s^{N+2}`
    have hsplit := pair_comp_right hso (spow s (N + 1))
    rw [Category.comp_id, ← spow_comm] at hsplit
    obtain ⟨σ', h1, h2⟩ := sumsTo_pair_assoc' hsplit hσs
    refine ⟨σ', (sumsTo_fin_last_iff _ _).2 ⟨σ, hσ, ?_⟩, ?_⟩
    · simpa using h1
    · simpa [spow] using h2

/-- **SIG 40**, (iii) ⇒ (i) (main.tex:2890, as printed except for the
existence of `⋁ₙ ω ∘ sⁿ`, which the paper takes from Manes–Arbib's iteration
theorem [MA86, Thm. 3.2.24]; we get it from the telescoping partial sums, the
limit axiom and the countable form of effectus axiom (iii)). -/
theorem admitsNormalisation_of_noZeroDivisors (hZ : ScalarsNoZeroDivisors C) :
    AdmitsNormalisation C := by
  have hI : truth (effObj C) = 𝟙 (effObj C) := truth_effObj_eq_id
  intro A ω hω
  set c := ω ≫ truth A with hc
  set s := orth c with hs
  have hsc : orth s = c := eabasics_orth_orth c
  -- the truths `sⁿ s^⊥` are summable, with sum `t`
  have hsum : Summable (fun n : ℕ => spow s n ≫ c) := by
    refine summable_nat_of_fin _ fun n => ?_
    cases n with
    | zero => exact summable_of_isEmpty _
    | succ N =>
      obtain ⟨σ, hσ, -⟩ := telescope s N
      rw [hsc] at hσ
      exact hσ.summable
  -- the family `ω ∘ sⁿ` is summable, with sum `ω̃`
  have hg : Summable (fun n : ℕ => spow s n ≫ ω) := by
    refine summable_of_summable_truth _ ?_
    simpa only [Category.assoc, ← hc] using hsum
  set ωt := sum _ hg with hωt
  have hωts : SumsTo (fun n : ℕ => spow s n ≫ ω) ωt := sumsTo_sum hg
  set t := ωt ≫ truth A with htdef
  have hts : SumsTo (fun n : ℕ => spow s n ≫ c) t := by
    have := comp_sumsTo_left (truth A) hωts
    simpa only [Category.assoc, ← hc] using this
  -- `t = t·s ⊕ s^⊥`
  have ht1 : SumsTo ![s ≫ t, c] t := by
    obtain ⟨u, hu, hu0⟩ := (sumsTo_nat_succ_iff _ _).1 hts
    have h2 : SumsTo (fun n : ℕ => spow s (n + 1) ≫ c) (s ≫ t) := by
      have := comp_sumsTo_right s hts
      simpa only [spow, Category.assoc] using this
    rw [hu.unique h2] at hu0
    simpa [spow] using hu0
  -- `t = t·(s ⊕ s^⊥) = t·s ⊕ t·s^⊥`, so `t·s^⊥ = s^⊥`
  have ht2 : SumsTo ![s ≫ t, c ≫ t] t := by
    have := pair_comp_left (sumsTo_pair_comm (sumsTo_orth c)) t
    rwa [hI, Category.id_comp] at this
  have ht3 : c ≫ t = c := pred_cancel (sumsTo_pair_comm ht2) (sumsTo_pair_comm ht1)
  -- `s^⊥ = s^⊥ ⊕ t^⊥ s^⊥`, so `t^⊥ s^⊥ = 0`, so `t^⊥ = 0`
  have ht4 : c ≫ orth t = 0 := by
    have h1 := pair_comp_right (sumsTo_orth t) c
    rw [hI, Category.comp_id, ht3] at h1
    have h0 : SumsTo ![c, 0] c := sumsTo_pair_comm (sumsTo_zero_pair c)
    exact pred_cancel (sumsTo_pair_comm h1) (sumsTo_pair_comm h0)
  have hc0 : c ≠ 0 := fun h => hω (EffectusPartialForm.eq_zero_of_one_zero h)
  have ht5 : t = 𝟙 (effObj C) := by
    rcases hZ (orth t) c ht4 with h | h
    · rw [← eabasics_orth_orth t, h, eabasics_orth_zero]; exact hI
    · exact absurd h hc0
  -- `ω̃` is a state and normalises `ω`
  have hscomm : ∀ n, c ≫ spow s n = spow s n ≫ c := by
    intro n; rw [← hsc]; exact orth_spow_comm s n
  refine ⟨ωt, ⟨?_, ?_⟩, ?_⟩
  · show ωt ≫ truth A = truth (effObj C)
    rw [← htdef, ht5, hI]
  · have h1 := comp_sumsTo_right c hωts
    have h2 := comp_sumsTo_left ω hts
    rw [ht5, Category.id_comp] at h2
    refine h2.unique ((sumsTo_congr fun n => ?_).1 h1)
    rw [← Category.assoc, hscomm]
  · rintro ρ ⟨hρ, hρe⟩
    have h2 := comp_sumsTo_left ρ hts
    rw [ht5, Category.id_comp] at h2
    refine h2.unique ((sumsTo_congr fun n => ?_).2 hωts)
    rw [Category.assoc, ← hρe]

/-- **SIG 40** (`thm:normalisation-equiv`, main.tex:1112, Theorem): for a
σ-effectus the following are equivalent: (i) it admits normalization;
(ii) its scalars admit division; (iii) its scalars have no nontrivial zero
divisors; (iv) every nonzero scalar is epic. -/
theorem normalisation_tfae :
    List.TFAE [AdmitsNormalisation C, AdmitsDivision C, ScalarsNoZeroDivisors C,
      NonzeroScalarsEpi C] := by
  tfae_have 1 → 2 := admitsDivision_of_admitsNormalisation
  tfae_have 2 → 3 := noZeroDivisors_of_admitsDivision
  tfae_have 3 → 1 := admitsNormalisation_of_noZeroDivisors
  tfae_have 4 → 3 := noZeroDivisors_of_nonzeroScalarsEpi
  tfae_have 1 → 4 := fun hN =>
    nonzeroScalarsEpi_of_admitsNormalisation hN
      (noZeroDivisors_of_admitsDivision (admitsDivision_of_admitsNormalisation hN))
  tfae_finish

end Sigma

end Papers.SIG
