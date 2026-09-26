/-
Copyright: the authors of the theses formalisation.

# SEA §4: almost-convex sequential effect algebras

A. Westerbaan, B. Westerbaan, J. van de Wetering, *The three types of normal
sequential effect algebras*, Quantum 2020 (arXiv:2004.12749),
`../papers/2004.12749/second.tex`, §4 (`sec:almostconvex`), points
**SEA 45**–**SEA 60**.

Conventions: `Papers/README.md`; plan: `Papers/SEA/PLAN.md`.

* An *a-convex action* (SEA 45) is the structure `AConvexAction`; a convex
  action is `ConvexAction E = EffectModule I E` (SEA 8), and SEA 46 relates
  the two (`sea46_convex_iff`).
* The theory — floors (SEA 49, 50), unique division (51), additive maps
  `[0,1] → E` (52), halves (53, 54), a-convex actions from additive maps (55),
  the seven characterisations of convexity (57), the maximal a-convex
  idempotent (58) and the splitting `E ≅ E₁ ⊕ E₂` (59, 60) — comes first.
* Horizontal sums (SEA 47) come last, with the examples SEA 48 (`HH`) and
  SEA 56 (`E56`), because those examples use SEA 52–57.  The horizontal sum is
  encoded by canonical representatives (`HSum`), and the sequential products
  of both examples are instances of one construction (`HSMaps`,
  `HSum.hsSEA`, `HSum.hsNormalSEA`).
* The representation theorem of directed-complete effect monoids enters
  through Basic's `dcem_structure`: SEA 35 (OAP 57 + 69) is the explicit
  hypothesis `h35 : SEA35` of SEA 51, 52.4, 55, 57–60 (it is discharged in
  `Papers/SEA/Discharge.lean`, which has no olean yet); OAP 47 is
  `oap47_holds`, SEA 42 is `sea42_central` and SEA 44 is `sea44_complete`
  (all `Papers/SEA/Boolean.lean`).
-/
import Papers.SEA.Boolean

namespace Papers.SEA

open Theses.B.Eff
open scoped unitInterval

universe u v

/-! ## Preliminaries: a few effect-algebra facts -/

section EAMore

variable {E : Type u} [EffectAlgebra E]

/-- `c ⊖ b ≼ c ⊖ a` for `a ≼ b ≼ c`. -/
theorem ominus_anti {a b c : E} (hab : a ≼ b) (hbc : b ≼ c) :
    ominus c b hbc ≼ ominus c a (le_trans' hab hbc) := by
  obtain ⟨d, had, rfl⟩ := hab
  obtain ⟨h1, e1⟩ := ovee_ominus hbc
  have e2 := PCM.ovee_assoc had h1
  have hdx := PCM.perp_of_ovee_perp had h1
  have : ominus c a (le_trans' ⟨d, had, rfl⟩ hbc) = ovee d (ominus c (ovee a d had) hbc) hdx :=
    ominus_eq _ (PCM.perp_ovee_of_ovee_perp had h1) (e2.symm.trans e1)
  rw [this]; exact right_le_ovee hdx

/-- An element below a summable element is summable (for the second argument). -/
theorem ovee_le_ovee_left {a b c : E} (hab : a ≼ b) (h : Perp b c) :
    ∃ h' : Perp a c, ovee a c h' ≼ ovee b c h :=
  eabasics_le_perp_compat hab h

/-- Sums of lists are monotone: if `l` has sum `s` and `l'` is below `l`
entrywise, then `l'` has a sum below `s`. -/
theorem isSumOf_le_of_forall₂ {l l' : List E} {s : E} (hs : PCM.IsSumOf l s)
    (hl : List.Forall₂ (fun x y => x ≼ y) l' l) : ∃ t, PCM.IsSumOf l' t ∧ t ≼ s := by
  induction hl generalizing s with
  | nil => exact ⟨0, PCM.IsSumOf.nil, by rw [PCM.isSumOf_nil_iff.mp hs]; exact le_refl' _⟩
  | @cons x y l' l hxy _ ih =>
    obtain ⟨s', hs', h1, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    obtain ⟨t, ht, hts⟩ := ih hs'
    obtain ⟨h2, hle2⟩ := ovee_le_ovee_right hts h1
    obtain ⟨h3, hle3⟩ := ovee_le_ovee_left hxy h2
    exact ⟨_, PCM.IsSumOf.cons ht h3, le_trans' hle3 hle2⟩

/-- If `n·e` exists and `d ≼ e`, then `n·d` exists (and lies below `n·e`). -/
theorem isSumOf_replicate_le {n : ℕ} {d e s : E} (hs : PCM.IsSumOf (List.replicate n e) s)
    (hde : d ≼ e) : ∃ t, PCM.IsSumOf (List.replicate n d) t ∧ t ≼ s := by
  refine isSumOf_le_of_forall₂ hs ?_
  clear hs
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih => exact List.Forall₂.cons hde ih

/-- The `n`-fold sum `n·0 = 0`. -/
theorem isSumOf_replicate_zero (n : ℕ) : PCM.IsSumOf (List.replicate n (0 : E)) 0 := by
  induction n with
  | zero => exact PCM.IsSumOf.nil
  | succ n ih =>
    have := PCM.IsSumOf.cons (a := (0 : E)) ih (PCM.zero_perp 0)
    rwa [zero_ovee_eq] at this

/-- `(n+1)·a = a ⋁ n·a`, packaged. -/
theorem isSumOf_replicate_succ' {n : ℕ} {a t : E} (ht : PCM.IsSumOf (List.replicate n a) t)
    (h : Perp a t) : PCM.IsSumOf (List.replicate (n + 1) a) (ovee a t h) :=
  PCM.IsSumOf.cons ht h

/-- `1·a = a`. -/
theorem isSumOf_replicate_one (a : E) : PCM.IsSumOf (List.replicate 1 a) a := by
  have := PCM.IsSumOf.cons (a := a) PCM.IsSumOf.nil (PCM.perp_zero a)
  rwa [ovee_zero_eq] at this

/-- `2·a` is `a ⋁ a`. -/
theorem isSumOf_two_iff {a s : E} :
    PCM.IsSumOf (List.replicate 2 a) s ↔ ∃ h : Perp a a, ovee a a h = s := by
  constructor
  · intro hs
    obtain ⟨t, ht, h, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    have : t = a := isSumOf_unique ht (isSumOf_replicate_one a)
    subst this; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact isSumOf_pair h

end EAMore

/-! ## Sequential-effect-algebra facts used throughout §4 -/

section SEAMore

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- If `c` commutes with every entry of a summable list, it commutes with the
sum (S5, iterated). -/
theorem commutes_isSumOf {c : E} {l : List E} {s : E} (hs : PCM.IsSumOf l s)
    (hc : ∀ x ∈ l, Commutes c x) : Commutes c s := by
  induction hs with
  | nil => show c ⊙ 0 = 0 ⊙ c; rw [seq_zero, zero_seq]
  | @cons a l s _ h ih =>
    exact Commutes.ovee h (hc a (List.mem_cons_self ..))
      (ih fun x hx => hc x (List.mem_cons_of_mem _ hx))

/-- An element commutes with its multiples: `b | n·b`. -/
theorem commutes_replicate {n : ℕ} {b s : E} (hs : PCM.IsSumOf (List.replicate n b) s) :
    Commutes b s :=
  commutes_isSumOf hs fun x hx => by rw [List.eq_of_mem_replicate hx]; exact commutes_refl b

/-- Multiples of a common element commute: `k·u | l·u`. -/
theorem commutes_replicate_replicate {k l : ℕ} {u s t : E}
    (hs : PCM.IsSumOf (List.replicate k u) s) (ht : PCM.IsSumOf (List.replicate l u) t) :
    Commutes s t :=
  commutes_isSumOf ht fun x hx => by
    rw [List.eq_of_mem_replicate hx]; exact (commutes_replicate hs).symm

/-- `c ⊙ (n·a) = n·(c ⊙ a)` (S1, iterated). -/
theorem seq_isSumOf (c : E) {l : List E} {s : E} (hs : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map (c ⊙ ·)) (c ⊙ s) := by
  induction hs with
  | nil => rw [seq_zero]; exact PCM.IsSumOf.nil
  | @cons a l s _ h ih =>
    obtain ⟨h', e⟩ := seq_ovee c h
    rw [e]; exact PCM.IsSumOf.cons ih h'

/-- SEA 18 for lists: a sum of elements below an idempotent `p` is below `p`. -/
theorem isSumOf_le_idempotent {p : E} (hp : IsIdempotent p) {l : List E} {s : E}
    (hs : PCM.IsSumOf l s) (hl : ∀ x ∈ l, x ≼ p) : s ≼ p := by
  induction hs with
  | nil => exact zero_le' p
  | @cons a l s _ h ih =>
    exact sea18_ovee_le hp (hl a (List.mem_cons_self ..))
      (ih fun x hx => hl x (List.mem_cons_of_mem _ hx)) h

/-- The only self-summable idempotent is `0` (SEA 18 with `a = b = p`). -/
theorem idempotent_selfSummable_eq_zero {p : E} (hp : IsIdempotent p) (h : Perp p p) :
    p = 0 := by
  have hle := sea18_ovee_le hp (le_refl' p) (le_refl' p) h
  exact eq_zero_of_ovee_self h (le_antisymm' hle (left_le_ovee h))

end SEAMore

/-! ## Infima in a normal SEA -/

section NormalInf

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

omit [NormalSEA E] in
theorem orth_image_directed {S : Set E} (hS : EFiltered S) : EDirected (orth '' S) := by
  obtain ⟨⟨s, hs⟩, h⟩ := hS
  refine ⟨⟨orth s, s, hs, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hca, hcb⟩ := h a ha b hb
  exact ⟨orth c, ⟨c, hc, rfl⟩, orth_le_orth hca, orth_le_orth hcb⟩

omit [NormalSEA E] in
/-- The directed image of a directed set under a monotone map. -/
theorem eDirected_image {F : Type v} [EffectAlgebra F] {S : Set E} (hS : EDirected S)
    {f : E → F} (hf : ∀ a b, a ≼ b → f a ≼ f b) : EDirected (f '' S) := by
  obtain ⟨⟨s, hs⟩, h⟩ := hS
  refine ⟨⟨f s, s, hs, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := h a ha b hb
  exact ⟨f c, ⟨c, hc, rfl⟩, hf _ _ hac, hf _ _ hbc⟩

/-- S6 for filtered infima: `a ⊙ ⋀S = ⋀_{s∈S} a ⊙ s` (via `(·)⊥`, SEA 14). -/
theorem seq_inf (a : E) {S : Set E} {x : E} (hS : EFiltered S) (hx : EIsInf S x) :
    EIsInf ((a ⊙ ·) '' S) (a ⊙ x) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact seq_mono a (hx.1 s hs)
  · intro y hy
    have hD := orth_image_directed hS
    have hsup : EIsSup (orth '' S) (orth x) := eIsSup_orth_of_eIsInf hx
    have hsup' := NormalSEA.seq_sup a hD hsup
    -- `y ⊥ a ⊙ s⊥` for every `s`, with `y ⋁ a ⊙ s⊥ ≼ a`
    have hperp : ∀ z ∈ (a ⊙ ·) '' (orth '' S), Perp z y := by
      rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      obtain ⟨h, _⟩ := seq_split a s
      exact PCM.perp_comm (perp_of_le_left (hy _ ⟨s, hs, rfl⟩) h)
    have hne : ((a ⊙ ·) '' (orth '' S)).Nonempty := by
      obtain ⟨⟨s, hs⟩, _⟩ := hS; exact ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩⟩
    obtain ⟨hyx, hsupy⟩ := ovee_isSup hne hsup' (fun z hz => PCM.perp_comm (hperp z hz))
    have hle : ovee y (a ⊙ orth x) hyx ≼ a := hsupy.2 a (by
      rintro _ ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, h, rfl⟩
      obtain ⟨h1, e1⟩ := seq_split a s
      obtain ⟨h2, hle2⟩ := ovee_le_ovee_left (hy _ ⟨s, hs, rfl⟩) h1
      rw [e1] at hle2
      exact le_trans' (le_of_eq' (PCM.ovee_congr rfl rfl h h2)) hle2)
    obtain ⟨h1, e1⟩ := seq_split a x
    have h1' : Perp (a ⊙ orth x) (a ⊙ x) := PCM.perp_comm h1
    have hyx' : Perp (a ⊙ orth x) y := PCM.perp_comm hyx
    refine le_of_ovee_le_ovee hyx' h1' ?_
    rw [← PCM.ovee_comm hyx, ← PCM.ovee_comm h1, e1]
    exact hle
where
  le_of_eq' {a b : E} (h : a = b) : a ≼ b := h ▸ le_refl' a

/-- S6 for filtered infima, commutation half: `a | s` for all `s ∈ S` gives
`a | ⋀S`. -/
theorem comm_inf (a : E) {S : Set E} {x : E} (hS : EFiltered S) (hx : EIsInf S x)
    (h : ∀ s ∈ S, Commutes a s) : Commutes a x := by
  have hsup : EIsSup (orth '' S) (orth x) := eIsSup_orth_of_eIsInf hx
  have := NormalSEA.comm_sup a (orth_image_directed hS) hsup (by
    rintro _ ⟨s, hs, rfl⟩; exact (h s hs).orth_r)
  exact Commutes.of_orth_r this

omit [NormalSEA E] in
/-- The range of an antitone sequence is filtered. -/
theorem eFiltered_range_of_antitone {f : ℕ → E} (hf : ∀ n, f (n + 1) ≼ f n) :
    EFiltered (Set.range f) := by
  have mono : ∀ n m, n ≤ m → f m ≼ f n := by
    intro n m hnm
    induction hnm with
    | refl => exact le_refl' _
    | step _ ih => exact le_trans' (hf _) ih
  refine ⟨⟨f 0, 0, rfl⟩, ?_⟩
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
  exact ⟨f (max n m), ⟨_, rfl⟩, mono _ _ (le_max_left _ _), mono _ _ (le_max_right _ _)⟩

end NormalInf

/-! ## Almost-convex actions (SEA 45, 46) -/

/-- **SEA 45** (`def:almostconvex`, second.tex:1146, Definition): an
*a-convex action* (almost-convex action) on an effect algebra `E` is a map
`· : [0,1] × E → E` such that for all `a ∈ E` and `λ, μ ∈ [0,1]`:
`λ · (μ · a) = (λμ) · a`; if `λ + μ ≤ 1` then `λ · a ⊥ μ · a` and
`λ · a ⋁ μ · a = (λ + μ) · a`; and `1 · a = a`.  (The second axiom is
stated for `λ + μ = ν`, to keep the sum inside `[0,1]` without a proof
term.) -/
@[ext]
structure AConvexAction (E : Type u) [EffectAlgebra E] where
  /-- The action `λ · a`. -/
  act : I → E → E
  act_act : ∀ (l m : I) (a : E), act l (act m a) = act (l * m) a
  act_add : ∀ (l m n : I) (a : E), (l : ℝ) + m = n →
    ∃ h : Perp (act l a) (act m a), ovee (act l a) (act m a) h = act n a
  one_act : ∀ a : E, act 1 a = a

/-- **SEA 45** (`def:almostconvex`, second.tex:1146, Definition): `E` is
*a-convex* when it carries at least one a-convex action. -/
def IsAConvex (E : Type u) [EffectAlgebra E] : Prop := Nonempty (AConvexAction E)

/-- A convex action (an effect module over `[0,1]`, SEA 8) is an a-convex
action. -/
def AConvexAction.ofConvex {E : Type u} [EffectAlgebra E] (C : ConvexAction E) :
    AConvexAction E where
  act l a := l • a
  act_act l m a := (EffectModule.mul_smul l m a).symm
  act_add l m n a hlmn := by
    have hp : Perp l m := show (l : ℝ) + m ≤ 1 by rw [hlmn]; exact n.2.2
    obtain ⟨h', e⟩ := EffectModule.perp_smul (M := I) hp a
    refine ⟨h', e.trans ?_⟩
    congr 1; exact Subtype.ext hlmn
  one_act a := EffectModule.one_smul (M := I) a

/-- An a-convex action that is additive in `E` is a convex action. -/
@[instance_reducible] def AConvexAction.toConvex {E : Type u} [EffectAlgebra E] (A : AConvexAction E)
    (hadd : ∀ (l : I) {a b : E} (h : Perp a b),
      ∃ h' : Perp (A.act l a) (A.act l b), ovee (A.act l a) (A.act l b) h' = A.act l (ovee a b h)) :
    ConvexAction E where
  smul l a := A.act l a
  mul_smul l m a := (A.act_act l m a).symm
  smul_perp l _ _ h := hadd l h
  perp_smul {l m} h a := A.act_add l m (ovee l m h) a rfl
  one_smul a := A.one_act a

/-- **SEA 46** (second.tex:1166, Remark): a convex action is precisely an
a-convex action that is moreover additive, `λ · (a ⋁ b) = λ · a ⋁ λ · b`; so
`E` is convex iff it has an additive a-convex action. -/
theorem sea46_convex_iff {E : Type u} [EffectAlgebra E] :
    IsConvex E ↔ ∃ A : AConvexAction E, ∀ (l : I) {a b : E} (h : Perp a b),
      ∃ h' : Perp (A.act l a) (A.act l b), ovee (A.act l a) (A.act l b) h' = A.act l (ovee a b h) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨AConvexAction.ofConvex C, fun l _ _ h => EffectModule.smul_perp (M := I) l h⟩
  · rintro ⟨A, hA⟩
    exact ⟨A.toConvex hA⟩

/-! ## The floor of an element (SEA 49, 50) -/

section Floor

variable {E : Type u} [EffectAlgebra E]

/-- Sequential powers: `a⁰ = 1`, `aⁿ⁺¹ = a ⊙ aⁿ`. -/
def seqPow [SEAlgebra E] (a : E) : ℕ → E
  | 0 => 1
  | n + 1 => a ⊙ seqPow a n

section
variable [SEAlgebra E]

@[simp] theorem seqPow_zero (a : E) : seqPow a 0 = 1 := rfl

theorem seqPow_succ (a : E) (n : ℕ) : seqPow a (n + 1) = a ⊙ seqPow a n := rfl

theorem seqPow_one (a : E) : seqPow a 1 = a := seq_one a

theorem commutes_seqPow (a : E) (n : ℕ) : Commutes a (seqPow a n) := by
  induction n with
  | zero => show a ⊙ 1 = 1 ⊙ a; rw [seq_one, one_seq]
  | succ n ih => exact (commutes_refl a).seq ih

theorem seqPow_succ_le (a : E) (n : ℕ) : seqPow a (n + 1) ≼ seqPow a n := by
  rw [seqPow_succ, commutes_seqPow a n]; exact seq_le_left _ _

/-- If `p ⊙ a = p` and `p | a`, then `p ⊙ aⁿ = p`. -/
theorem seq_seqPow_of {p a : E} (hpa : p ⊙ a = p) (hc : Commutes p a) (n : ℕ) :
    p ⊙ seqPow a n = p := by
  induction n with
  | zero => exact seq_one p
  | succ n ih => rw [seqPow_succ, hc.assoc, hpa, ih]

end

variable [NormalSEA E]

/-- **SEA 49** (`def:floor`, second.tex:1228, Definition): in a normal SEA the
*floor* of `a` is `⌊a⌋ := ⋀ₙ aⁿ` (it exists by SEA 14, the powers being
decreasing). -/
noncomputable def floor (a : E) : E :=
  (exists_inf_of_antitone NormalSEA.directedComplete (seqPow_succ_le a)).choose

theorem floor_isInf (a : E) : EIsInf (Set.range (seqPow a)) (floor a) :=
  (exists_inf_of_antitone NormalSEA.directedComplete (seqPow_succ_le a)).choose_spec

theorem floor_filtered (a : E) : EFiltered (Set.range (seqPow a)) :=
  eFiltered_range_of_antitone (seqPow_succ_le a)

/-- **SEA 50** (second.tex:1232, Lemma): in a normal SEA, `⌊a⌋ ≼ a`, and
`⌊a⌋` is the largest idempotent below `a`.  Proof as printed: `a | ⌊a⌋` and
`⌊a⌋ ⊙ a = a ⊙ ⌊a⌋ = ⋀ₙ aⁿ⁺¹ = ⌊a⌋`, so `⌊a⌋ ⊙ aⁿ = ⌊a⌋` and
`⌊a⌋² = ⋀ₙ ⌊a⌋ ⊙ aⁿ = ⌊a⌋`; an idempotent `p ≼ a` has `p ⊙ aⁿ = p`, so
`p ⊙ ⌊a⌋ = p`, i.e. `p ≼ ⌊a⌋`. -/
theorem sea50_floor (a : E) :
    floor a ≼ a ∧ IsIdempotent (floor a) ∧
      ∀ p : E, IsIdempotent p → p ≼ a → p ≼ floor a := by
  have hinf := floor_isInf a
  have hfil := floor_filtered a
  have hle : floor a ≼ a := by have := hinf.1 _ ⟨1, rfl⟩; rwa [seqPow_one] at this
  -- `a | ⌊a⌋`
  have hc : Commutes a (floor a) :=
    comm_inf a hfil hinf (by rintro _ ⟨n, rfl⟩; exact commutes_seqPow a n)
  -- `a ⊙ ⌊a⌋ = ⌊a⌋`
  have h1 : a ⊙ floor a = floor a := by
    have hi := seq_inf a hfil hinf
    have himg : (a ⊙ ·) '' Set.range (seqPow a) = Set.range (fun n => seqPow a (n + 1)) := by
      ext y; constructor
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [himg] at hi
    refine hi.unique ⟨?_, ?_⟩
    · rintro _ ⟨n, rfl⟩; exact hinf.1 _ ⟨n + 1, rfl⟩
    · intro y hy
      refine hinf.2 y ?_
      rintro _ ⟨n, rfl⟩
      exact le_trans' (hy _ ⟨n, rfl⟩) (seqPow_succ_le a n)
  have h2 : floor a ⊙ a = floor a := by rw [← hc]; exact h1
  have hpow : ∀ n, floor a ⊙ seqPow a n = floor a := seq_seqPow_of h2 hc.symm
  -- `p ⊙ ⌊a⌋ = p` when `p ⊙ aⁿ = p` for all `n`
  have key : ∀ p : E, (∀ n, p ⊙ seqPow a n = p) → p ⊙ floor a = p := by
    intro p hp
    have hi := seq_inf p hfil hinf
    have himg : (p ⊙ ·) '' Set.range (seqPow a) = {p} := by
      ext y; constructor
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact hp n
      · intro hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact ⟨_, ⟨0, rfl⟩, hp 0⟩
    rw [himg] at hi
    exact hi.unique ⟨fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact le_refl' _,
      fun y hy => hy p rfl⟩
  refine ⟨hle, key _ hpow, fun p hp hpa => ?_⟩
  have e1 : p ⊙ a = p := ((sea17_4 hp a).1).mp hpa
  have e2 : a ⊙ p = p := ((sea17_4 hp a).2.1).mp hpa
  have hpc : Commutes p a := e1.trans e2.symm
  exact ((sea17_4 hp (floor a)).1).mpr (key p (seq_seqPow_of e1 hpc))

theorem floor_le (a : E) : floor a ≼ a := (sea50_floor a).1

theorem floor_idempotent (a : E) : IsIdempotent (floor a) := (sea50_floor a).2.1

theorem le_floor {a p : E} (hp : IsIdempotent p) (hpa : p ≼ a) : p ≼ floor a :=
  (sea50_floor a).2.2 p hp hpa

/-- `⌊a⌋ = 0` iff `0` is the only idempotent below `a`. -/
theorem floor_eq_zero_iff (a : E) :
    floor a = 0 ↔ ∀ p : E, IsIdempotent p → p ≼ a → p = 0 := by
  constructor
  · intro h p hp hpa; exact eq_zero_of_le_zero (h ▸ le_floor hp hpa)
  · intro h; exact h _ (floor_idempotent a) (floor_le a)

end Floor


/-! ## Transport along isomorphisms; the model `[0,1]_{C(X)} ⊕ B` -/

section Transport

variable {E : Type u} [EffectAlgebra E]

/-- Sums in a sub-effect algebra are sums in `E`. -/
theorem subEA_isSumOf_val {T : SubEffectAlgebra E} {l : List T.carrier} {s : T.carrier}
    (h : PCM.IsSumOf l s) : PCM.IsSumOf (l.map Subtype.val) s.1 := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | cons _ h ih => exact PCM.IsSumOf.cons ih h

/-- A sum in `E` of elements of a sub-effect algebra lies in it and is a sum
there. -/
theorem subEA_isSumOf_of_val {T : SubEffectAlgebra E} {l : List T.carrier} {s : E}
    (h : PCM.IsSumOf (l.map Subtype.val) s) : ∃ hs : s ∈ T.carrier, PCM.IsSumOf l ⟨s, hs⟩ := by
  induction l generalizing s with
  | nil => rw [PCM.isSumOf_nil_iff.mp h]; exact ⟨T.zero_mem, PCM.IsSumOf.nil⟩
  | cons x l ih =>
    obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
    obtain ⟨htT, ht'⟩ := ih ht
    exact ⟨T.ovee_mem hp x.2 htT, PCM.IsSumOf.cons (s := (⟨t, htT⟩ : T.carrier)) ht' hp⟩

variable {F : Type v} [EffectAlgebra F]

theorem EAIso.map_zero' (f : EAIso E F) : f.toFun 0 = 0 := by
  have h00 : Perp (0 : E) 0 := PCM.zero_perp 0
  have e := f.map_ovee 0 0 h00 ((f.perp_iff 0 0).mpr h00)
  rw [zero_ovee_eq] at e
  exact eq_zero_of_ovee_self _ e.symm

theorem EAIso.isSumOf_map (f : EAIso E F) {l : List E} {s : E} (h : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map f.toFun) (f.toFun s) := by
  induction h with
  | nil => rw [EAIso.map_zero']; exact PCM.IsSumOf.nil
  | @cons a l s _ h ih =>
    rw [f.map_ovee a s h ((f.perp_iff a s).mpr h)]
    exact PCM.IsSumOf.cons ih _

theorem EAIso.map_le (f : EAIso E F) {a b : E} (h : a ≼ b) : f.toFun a ≼ f.toFun b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨f.toFun c, (f.perp_iff a c).mpr hc, (f.map_ovee a c hc _).symm⟩

end Transport

section Model

attribute [local instance] booleanEffectMonoid

variable {X : Type u} [TopologicalSpace X] {B : Type u} [CompleteBooleanAlgebra B]

/-- In the interval effect algebra `[0,1]_{C(X)}`, a sum of a list is the sum
of its values. -/
theorem cxi_isSumOf_sum {l : List (CXI X)} {s : CXI X} (h : PCM.IsSumOf l s) :
    (l.map Subtype.val).sum = s.1 := by
  induction h with
  | nil => rfl
  | @cons a l s _ h ih =>
    show a.1 + (l.map Subtype.val).sum = a.1 + s.1
    rw [ih]

omit [TopologicalSpace X] in
/-- Sums in a product are componentwise. -/
theorem prod_isSumOf_fst {E F : Type u} [EffectAlgebra E] [EffectAlgebra F] {l : List (E × F)}
    {s : E × F} (h : PCM.IsSumOf l s) : PCM.IsSumOf (l.map Prod.fst) s.1 := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | cons _ h ih => exact PCM.IsSumOf.cons ih h.1

omit [TopologicalSpace X] in
theorem prod_isSumOf_snd {E F : Type u} [EffectAlgebra E] [EffectAlgebra F] {l : List (E × F)}
    {s : E × F} (h : PCM.IsSumOf l s) : PCM.IsSumOf (l.map Prod.snd) s.2 := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | cons _ h ih => exact PCM.IsSumOf.cons ih h.2

omit [TopologicalSpace X] in
/-- In a Boolean algebra, `(n+1)·x = x`. -/
theorem bool_isSumOf_replicate {n : ℕ} {x s : B} (h : PCM.IsSumOf (List.replicate (n + 1) x) s) :
    s = x := by
  induction n generalizing s with
  | zero =>
    obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
    have e : t = 0 := PCM.isSumOf_nil_iff.mp ht
    subst e; exact ovee_zero_eq x _
  | succ n ih =>
    obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
    have e : t = x := ih ht
    subst e; exact sup_idem t

/-- `r · c` for `c ∈ [0,1]_{C(X)}` and `r ∈ [0,1]`. -/
noncomputable def cxScale (r : I) (c : CXI X) : CXI X :=
  ⟨(r : ℝ) • c.1, by
    refine ContinuousMap.le_def.mpr fun x => ?_
    simpa using mul_nonneg r.2.1 (by simpa using ContinuousMap.le_def.mp c.2.1 x),
   by
    refine ContinuousMap.le_def.mpr fun x => ?_
    have h1 : c.1 x ≤ 1 := by simpa using ContinuousMap.le_def.mp c.2.2 x
    have h0 : 0 ≤ c.1 x := by simpa using ContinuousMap.le_def.mp c.2.1 x
    simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.one_apply]
    nlinarith [r.2.1, r.2.2]⟩

/-- In `[0,1]_{C(X)}`, `n · ((1/n) · c) = c`. -/
theorem cxi_isSumOf_div {n : ℕ} (hn : 0 < n) (c : CXI X) (r : I) (hr : (r : ℝ) = 1 / n) :
    PCM.IsSumOf (List.replicate n (cxScale r c)) c := by
  refine interval_isSumOf cx_zero_le_one _ _ ?_
  rw [List.map_replicate, List.sum_replicate]
  show n • ((r : ℝ) • c.1) = c.1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hr]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mul_one_div_cancel this, one_smul]

/-- Division by `n > 0` is unique in `[0,1]_{C(X)} ⊕ B`: `n·x = n·y` gives
`x = y`. -/
theorem cxb_replicate_cancel {n : ℕ} (hn : 0 < n) {x y s : CXI X × B}
    (hx : PCM.IsSumOf (List.replicate n x) s) (hy : PCM.IsSumOf (List.replicate n y) s) :
    x = y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := prod_isSumOf_fst hx
  have h2 := prod_isSumOf_fst hy
  rw [List.map_replicate] at h1 h2
  have e1 := cxi_isSumOf_sum h1
  have e2 := cxi_isSumOf_sum h2
  rw [List.map_replicate, List.sum_replicate] at e1 e2
  have e : (m + 1) • x.1.1 = (m + 1) • y.1.1 := e1.trans e2.symm
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ (m + 1) y.1.1] at e
  have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have e' := congrArg (fun z : C(X, ℝ) => (((m + 1 : ℕ) : ℝ)⁻¹) • z) e
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at e'
  have h3 := prod_isSumOf_snd hx
  have h4 := prod_isSumOf_snd hy
  rw [List.map_replicate] at h3 h4
  exact Prod.ext (Subtype.ext e')
    ((bool_isSumOf_replicate h3).symm.trans (bool_isSumOf_replicate h4))

/-- In `[0,1]_{C(X)} ⊕ B`: `n·(c/n, ⊥) = (c, ⊥)`. -/
theorem cxb_isSumOf_div {n : ℕ} (hn : 0 < n) (c : CXI X) (r : I) (hr : (r : ℝ) = 1 / n) :
    PCM.IsSumOf (List.replicate n ((cxScale r c, (⊥ : B)) : CXI X × B)) (c, ⊥) := by
  have := isSumOf_prod _ _ _ _ (cxi_isSumOf_div hn c r hr)
    (isSumOf_replicate_zero (E := B) n) (by simp)
  rwa [List.zipWith_replicate', ] at this

end Model

/-! ## Additive maps `[0,1] → E` -/

section Additive

variable {E : Type u} [EffectAlgebra E]

/-- A map `φ : [0,1] → E` is *additive* when `λ + μ ≤ 1` gives
`φ(λ) ⊥ φ(μ)` and `φ(λ) ⋁ φ(μ) = φ(λ + μ)` (stated for `λ + μ = ν`). -/
def IsAdditive (φ : I → E) : Prop :=
  ∀ l m n : I, (l : ℝ) + m = n → ∃ h : Perp (φ l) (φ m), ovee (φ l) (φ m) h = φ n

/-- The element `r ∈ [0,1]`. -/
def mkI (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : I := ⟨r, h0, h1⟩

@[simp] theorem mkI_val (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : (mkI r h0 h1 : ℝ) = r := rfl

variable {φ : I → E}

theorem IsAdditive.map_zero (hφ : IsAdditive φ) : φ 0 = 0 := by
  obtain ⟨h, e⟩ := hφ 0 0 0 (by simp)
  exact eq_zero_of_ovee_self h e

theorem IsAdditive.mono (hφ : IsAdditive φ) {l m : I} (hlm : l ≤ m) : φ l ≼ φ m := by
  have hlm' : (l : ℝ) ≤ m := hlm
  obtain ⟨h, e⟩ := hφ l (mkI (m - l) (by linarith) (by linarith [l.2.1, m.2.2])) m (by simp)
  rw [← e]; exact left_le_ovee h

/-- `φ(m) ⊖ φ(l) = φ(m - l)`. -/
theorem IsAdditive.ominus_eq (hφ : IsAdditive φ) {l m : I} (hlm : l ≤ m) :
    ominus (φ m) (φ l) (hφ.mono hlm) =
      φ (mkI (m - l) (by have : (l : ℝ) ≤ m := hlm; linarith) (by linarith [l.2.1, m.2.2])) := by
  obtain ⟨h, e⟩ := hφ l (mkI (m - l) (by have : (l : ℝ) ≤ m := hlm; linarith)
    (by linarith [l.2.1, m.2.2])) m (by simp)
  exact Papers.SEA.ominus_eq _ h e

/-- `k · φ(x) = φ(k x)` when `k x ≤ 1`. -/
theorem IsAdditive.replicate (hφ : IsAdditive φ) (k : ℕ) (x y : I) (hxy : (k : ℝ) * x = y) :
    PCM.IsSumOf (List.replicate k (φ x)) (φ y) := by
  induction k generalizing y with
  | zero =>
    have : y = 0 := Subtype.ext (by simp at hxy; simp [← hxy])
    rw [this, hφ.map_zero]; exact PCM.IsSumOf.nil
  | succ k ih =>
    have hz0 : (0 : ℝ) ≤ k * x := mul_nonneg (Nat.cast_nonneg k) x.2.1
    have hz1 : (k : ℝ) * x ≤ 1 := by
      have := y.2.2; push_cast at hxy; nlinarith [x.2.1]
    have ih' := ih (mkI _ hz0 hz1) rfl
    obtain ⟨h, e⟩ := hφ x (mkI _ hz0 hz1) y (by simp; push_cast at hxy; linarith)
    rw [List.replicate_succ, ← e]
    exact PCM.IsSumOf.cons ih' h

/-- `λ ↦ a ⊙ φ(λ)` is additive (S1). -/
theorem IsAdditive.seq [SEAlgebra E] (hφ : IsAdditive φ) (a : E) :
    IsAdditive (fun l => a ⊙ φ l) := by
  intro l m n h
  obtain ⟨h1, e1⟩ := hφ l m n h
  obtain ⟨h2, e2⟩ := seq_ovee a h1
  exact ⟨h2, by rw [← e2, e1]⟩

/-- `λ ↦ φ(λ μ)` is additive. -/
theorem IsAdditive.comp_mul (hφ : IsAdditive φ) (m : I) : IsAdditive (fun l => φ (l * m)) := by
  intro l l' n h
  exact hφ (l * m) (l' * m) (n * m) (by simp only [Set.Icc.coe_mul]; rw [← h]; ring)

/-- The image of a non-empty subset of `[0,1]` under a monotone map is
directed. -/
theorem eDirected_image_I (hφ : IsAdditive φ) {D : Set I} (hD : D.Nonempty) :
    EDirected (φ '' D) := by
  obtain ⟨d, hd⟩ := hD
  refine ⟨⟨φ d, d, hd, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rcases le_total a b with hab | hab
  · exact ⟨φ b, ⟨b, hb, rfl⟩, hφ.mono hab, le_refl' _⟩
  · exact ⟨φ a, ⟨a, ha, rfl⟩, le_refl' _, hφ.mono hab⟩

end Additive

/-! ### Density of fractions -/

/-- The fractions `a λ / b ≤ x` (`a, b ∈ ℕ`, `b > 0`) in `[0,1]`. -/
def fracSet (lam : ℝ) (x : I) : Set I :=
  {q | q ≤ x ∧ ∃ a b : ℕ, 0 < b ∧ (q : ℝ) = a * lam / b}

theorem fracSet_nonempty (lam : ℝ) (x : I) : (fracSet lam x).Nonempty :=
  ⟨0, show ((0 : I) : ℝ) ≤ x from x.2.1, 0, 1, one_pos, by simp⟩

/-- The fractions `a λ / b` below `x` have supremum `x` (for `λ > 0`). -/
theorem fracSet_isLUB {lam : ℝ} (hlam : 0 < lam) (x : I) : IsLUB (fracSet lam x) x := by
  refine ⟨fun q hq => hq.1, fun y hy => ?_⟩
  by_contra hxy
  have hyx : (y : ℝ) < x := lt_of_not_ge hxy
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (div_lt_div_of_pos_right hyx hlam)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (div_nonneg y.2.1 hlam.le) hr1
  have hrpos : 0 < r := by exact_mod_cast hr0
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
  have hrab : (r : ℝ) = (r.num.toNat : ℕ) / (r.den : ℕ) := by
    rw [Rat.cast_def]
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
  have hq1 : (r : ℝ) * lam < x := by rwa [lt_div_iff₀ hlam] at hr2
  have hq0 : (0 : ℝ) ≤ r * lam := by positivity
  have hq : mkI (r * lam) hq0 (by linarith [x.2.2]) ∈ fracSet lam x := by
    refine ⟨show (r : ℝ) * lam ≤ x from hq1.le, r.num.toNat, r.den, r.pos, ?_⟩
    simp only [mkI_val]; rw [hrab]; ring
  have h1 : (r : ℝ) * lam ≤ y := hy hq
  have h2 : (y : ℝ) < r * lam := by rwa [div_lt_iff₀ hlam] at hr1
  linarith

/-! ## Unique division (SEA 51) and additive maps into a normal SEA (SEA 52) -/

section Division

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

attribute [local instance] booleanEffectMonoid

/-- **SEA 51** (`lem:uniquedivision`, second.tex:1255, Lemma): if `⌊a⌋ = 0`
and `n > 0`, there is a unique `a'` with `a = n a'`; moreover `a' ∈ {a}''`.
Proof as printed: in `{a}'' ≅ [0,1]_{C(X)} ⊕ B` (SEA 36) write `a = (c, b)`;
`(0, b)` is an idempotent below `a`, so `b = 0` as `⌊a⌋ = 0` (SEA 50), and
`a' = (c/n, 0)` works.  If `a = n b` then `b | a`, so `b | a'`, and in
`{b, a'}'' ≅ [0,1]_{C(X)} ⊕ B` division by `n` is unique.  Uses SEA 35 and
OAP 47: the representation theorem, SEA 35 an explicit hypothesis, OAP 47
`oap47_holds` (`Papers/SEA/Boolean.lean`). -/
theorem sea51_division (h35 : SEA35.{u}) {a : E} (ha : floor a = 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ a' ∈ bicommutant ({a} : Set E), PCM.IsSumOf (List.replicate n a') a ∧
      ∀ b : E, PCM.IsSumOf (List.replicate n b) a → b = a' := by
  -- existence, in `{a}''`
  let _ := bicommEM {a} (singleton_commuting a)
  obtain ⟨X, tX, cX, hX, -, B, cB, ⟨Φ⟩⟩ :=
    @dcem_structure h35 oap47_holds _ (bicommEM {a} (singleton_commuting a))
      (bicommEM_dc {a} (singleton_commuting a))
  let aM : (bicommutantSub ({a} : Set E)).carrier := ⟨a, subset_bicommutant _ rfl⟩
  set c := Φ.toFun aM with hc
  -- the Boolean part of `a` vanishes
  have hb : c.2 = ⊥ := by
    let p := Φ.invFun ((0 : CXI X), c.2)
    have hpid : p * p = p := by
      show Φ.symm.toFun _ * Φ.symm.toFun _ = Φ.symm.toFun _
      rw [← Φ.symm.map_mul]
      congr 1
      exact Prod.ext (Subtype.ext (mul_zero _)) (inf_idem _)
    have hple : p ≼ aM := by
      have h1 : ((0 : CXI X), c.2) ≼ c := by
        refine ⟨(c.1, ⊥), ⟨show (0 : C(X, ℝ)) + c.1.1 ≤ 1 by rw [zero_add]; exact c.1.2.2,
          show c.2 ⊓ ⊥ = ⊥ from inf_bot_eq _⟩, ?_⟩
        exact Prod.ext (Subtype.ext (zero_add _)) (sup_bot_eq _)
      have := Φ.symm.toEAIso.map_le h1
      rwa [show Φ.symm.toEAIso.toFun c = aM from Φ.symm_apply aM] at this
    have hp0 : p.1 = 0 := (floor_eq_zero_iff a).mp ha p.1 (congrArg Subtype.val hpid)
      (subEA_le_iff.mp hple)
    have hp0' : p = 0 := Subtype.ext hp0
    have : ((0 : CXI X), c.2) = Φ.toFun p := (Φ.apply_symm _).symm
    rw [hp0', Φ.toEAIso.map_zero'] at this
    exact congrArg Prod.snd this
  have hcn : (c.1, (⊥ : B)) = c := Prod.ext rfl hb.symm
  let r : I := mkI (1 / n) (by positivity) (by
    rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn)
  let a'M := Φ.invFun (cxScale r c.1, ⊥)
  have hsum : PCM.IsSumOf (List.replicate n a'M) aM := by
    have := Φ.symm.toEAIso.isSumOf_map (cxb_isSumOf_div hn c.1 r rfl)
    rw [List.map_replicate, hcn] at this
    rwa [show Φ.symm.toEAIso.toFun c = aM from Φ.symm_apply aM] at this
  have hsumE : PCM.IsSumOf (List.replicate n a'M.1) a := by
    have := subEA_isSumOf_val hsum
    rwa [List.map_replicate] at this
  refine ⟨a'M.1, a'M.2, hsumE, fun b hbs => ?_⟩
  -- uniqueness, in `{b, a'}''`
  have hba : b ∈ commutant ({a} : Set E) := by
    intro s hs; rw [Set.mem_singleton_iff.mp hs]; exact commutes_replicate hbs
  have hab : Commutes a'M.1 b := a'M.2 b hba
  let S : Set E := {a'M.1, b}
  have hS : ∀ x ∈ S, ∀ y ∈ S, Commutes x y := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  let _ := bicommEM S hS
  obtain ⟨X2, tX2, cX2, hX2, -, B2, cB2, ⟨Ψ⟩⟩ :=
    @dcem_structure h35 oap47_holds _ (bicommEM S hS) (bicommEM_dc S hS)
  let bM : (bicommutantSub S).carrier := ⟨b, subset_bicommutant S (Or.inr rfl)⟩
  let a'M2 : (bicommutantSub S).carrier := ⟨a'M.1, subset_bicommutant S (Or.inl rfl)⟩
  obtain ⟨haS, h1⟩ := subEA_isSumOf_of_val (T := (bicommutantSub S).toSubEffectAlgebra)
    (l := List.replicate n bM) (by rw [List.map_replicate]; exact hbs)
  obtain ⟨haS', h2⟩ := subEA_isSumOf_of_val (T := (bicommutantSub S).toSubEffectAlgebra)
    (l := List.replicate n a'M2) (by rw [List.map_replicate]; exact hsumE)
  have h1' := Ψ.toEAIso.isSumOf_map h1
  have h2' := Ψ.toEAIso.isSumOf_map h2
  rw [List.map_replicate] at h1' h2'
  have := cxb_replicate_cancel hn h1' h2'
  exact congrArg Subtype.val (Ψ.injective this)

variable {φ : I → E}

/-- **SEA 52.1** (`prop:add-into-nsea`, second.tex:1297, Proposition): an
additive `φ : [0,1] → E` into a normal SEA is normal, `φ(⋁D) = ⋁_{λ∈D} φ(λ)`
for directed (in `[0,1]`: non-empty) `D`.  Proof as printed: the difference
`φ(⋁D) ⊖ ⋁ φ(D)` lies below every `φ(1/n)`, hence has all `n`-fold sums, and
is `0` by SEA 21. -/
theorem sea52_1_normal (hφ : IsAdditive φ) {D : Set I} {x : I} (hD : D.Nonempty)
    (hx : IsLUB D x) : EIsSup (φ '' D) (φ x) := by
  obtain ⟨s, hs⟩ := NormalSEA.directedComplete _ (eDirected_image_I hφ hD)
  have hsx : s ≼ φ x := hs.2 _ (by rintro _ ⟨l, hl, rfl⟩; exact hφ.mono (hx.1 hl))
  -- the difference is below every `φ(1/k)`
  have hsmall : ∀ k : ℕ, 0 < k → ∀ hk0 hk1, ominus (φ x) s hsx ≼ φ (mkI (1 / k) hk0 hk1) := by
    intro k hk hk0 hk1
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    obtain ⟨μ, hμD, hμ⟩ : ∃ μ ∈ D, (x : ℝ) - μ ≤ 1 / k := by
      by_cases hxk : (x : ℝ) ≤ 1 / k
      · obtain ⟨μ, hμ⟩ := hD; exact ⟨μ, hμ, by linarith [μ.2.1]⟩
      · push Not at hxk
        obtain ⟨c, hcD, hc1, -⟩ := hx.exists_between
          (show mkI ((x : ℝ) - 1 / k) (by linarith) (by linarith [x.2.2, one_div_pos.mpr hk'])
            < x from show (x : ℝ) - 1 / k < x by linarith [one_div_pos.mpr hk'])
        exact ⟨c, hcD, by have : (x : ℝ) - 1 / k < c := hc1; linarith⟩
    have hμx : μ ≤ x := hx.1 hμD
    have hμs : φ μ ≼ s := hs.1 _ ⟨μ, hμD, rfl⟩
    refine le_trans' (ominus_anti hμs hsx) ?_
    rw [hφ.ominus_eq hμx]
    exact hφ.mono (show (x : ℝ) - μ ≤ 1 / k from hμ)
  have hzero : ominus (φ x) s hsx = 0 := by
    refine sea21_archimedean NormalSEA.directedComplete fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, PCM.IsSumOf.nil⟩
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
      have hk1 : (1 : ℝ) / k ≤ 1 := by rw [div_le_one hk']; exact_mod_cast hk
      have hrep := hφ.replicate k (mkI (1 / k) hk0 hk1) 1 (by simp; field_simp)
      obtain ⟨t, ht, -⟩ := isSumOf_replicate_le hrep (hsmall k hk hk0 hk1)
      exact ⟨t, ht⟩
  obtain ⟨h1, e1⟩ := ovee_ominus hsx
  have : s = φ x := by
    rw [← e1, PCM.ovee_congr rfl hzero h1 (PCM.perp_zero s), ovee_zero_eq]
  rw [← this]; exact hs

/-- **SEA 52.2** (`prop:add-into-nsea`, second.tex:1297, Proposition):
`φ(λ) | φ(μ)` for all `λ, μ`.  Proof as printed: for rationals, `φ(k/n)` and
`φ(l/m)` are multiples of `φ(1/nm)` and commute by S5; in general, write
`λ, μ` as suprema of rationals and use S6 with SEA 52.1. -/
theorem sea52_2_commute (hφ : IsAdditive φ) (l m : I) : Commutes (φ l) (φ m) := by
  -- rationals commute
  have hrat : ∀ q ∈ fracSet 1 l, ∀ r ∈ fracSet 1 m, Commutes (φ q) (φ r) := by
    rintro q ⟨-, a, b, hb, hq⟩ r ⟨-, c, d, hd, hr⟩
    have hN : 0 < b * d := Nat.mul_pos hb hd
    have hN' : (0 : ℝ) < (b * d : ℕ) := by exact_mod_cast hN
    let u : I := mkI (1 / (b * d : ℕ)) (by positivity) (by
      rw [div_le_one hN']; exact_mod_cast hN)
    have h1 := hφ.replicate (a * d) u q (by
      simp only [u, mkI_val, hq]; push_cast; field_simp)
    have h2 := hφ.replicate (c * b) u r (by
      simp only [u, mkI_val, hr]; push_cast; field_simp)
    exact commutes_replicate_replicate h1 h2
  have hsupl := sea52_1_normal hφ (fracSet_nonempty 1 l) (fracSet_isLUB one_pos l)
  have hsupm := sea52_1_normal hφ (fracSet_nonempty 1 m) (fracSet_isLUB one_pos m)
  -- `φ(r) | φ(l)` for rational `r ≤ m`
  have h1 : ∀ r ∈ fracSet 1 m, Commutes (φ r) (φ l) := by
    intro r hr
    exact NormalSEA.comm_sup (φ r) (eDirected_image_I hφ (fracSet_nonempty 1 l)) hsupl
      (by rintro _ ⟨q, hq, rfl⟩; exact (hrat q hq r hr).symm)
  exact NormalSEA.comm_sup (φ l) (eDirected_image_I hφ (fracSet_nonempty 1 m)) hsupm
    (by rintro _ ⟨r, hr, rfl⟩; exact (h1 r hr).symm)

/-- **SEA 52.3** (`prop:add-into-nsea`, second.tex:1297, Proposition):
`⌊φ(λ)⌋ = 0` for `λ < 1`.  Proof as printed: with `λ ≤ 1 - 1/n`, an
idempotent `p ≼ φ(1 - 1/n)` has `φ(1/n) ≼ p⊥`, so `φ(1) = n φ(1/n) ≼ p⊥`
(SEA 18), and `p ≼ φ(1) ≼ p⊥` makes `p` self-summable, hence `0`. -/
theorem sea52_3_floor (hφ : IsAdditive φ) {l : I} (hl : (l : ℝ) < 1) : floor (φ l) = 0 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - (l : ℝ)))
  have h1l : (0 : ℝ) < 1 - l := by linarith
  have hk0 : (0 : ℝ) < k := lt_trans (one_div_pos.mpr h1l) hk
  have hkpos : 0 < k := by exact_mod_cast hk0
  have hv0 : (0 : ℝ) ≤ 1 / k := by positivity
  have hv1 : (1 : ℝ) / k ≤ 1 := by rw [div_le_one hk0]; exact_mod_cast hkpos
  let v : I := mkI (1 / k) hv0 hv1
  let w : I := mkI (1 - 1 / k) (by linarith) (by linarith)
  have hlw : l ≤ w := by
    show (l : ℝ) ≤ 1 - 1 / k
    have : 1 / (k : ℝ) < 1 - l := by
      rw [div_lt_iff₀ hk0]; rw [div_lt_iff₀ h1l] at hk; linarith
    linarith
  refine (floor_eq_zero_iff _).mpr fun p hp hpl => ?_
  have hpw : p ≼ φ w := le_trans' hpl (hφ.mono hlw)
  obtain ⟨hwv, ewv⟩ := hφ w v 1 (by simp [w, v])
  have hv : φ v ≼ orth p :=
    le_trans' (perp_iff_le_orth.mp (PCM.perp_comm hwv)) (orth_le_orth hpw)
  have hrep := hφ.replicate k v 1 (by simp [v]; field_simp)
  have h1 : φ 1 ≼ orth p := isSumOf_le_idempotent hp.compl hrep (fun x hx => by
    rw [List.eq_of_mem_replicate hx]; exact hv)
  have hp1 : p ≼ φ 1 := le_trans' hpl (hφ.mono (show (l : ℝ) ≤ 1 from l.2.2))
  exact idempotent_selfSummable_eq_zero hp (perp_iff_le_orth.mpr (le_trans' hp1 h1))

/-- The core of SEA 52.4: two additive maps agreeing at `λ > 0`, where `φ(λ)`
has unique `n`-th parts, agree everywhere (they agree on the dense set of
`mλ/n`, and SEA 52.1). -/
theorem additive_eq_of_div {ψ : I → E} (hφ : IsAdditive φ) (hψ : IsAdditive ψ) {l : I}
    (hl0 : 0 < (l : ℝ)) (h : φ l = ψ l)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ b c : E, PCM.IsSumOf (List.replicate n b) (φ l) →
      PCM.IsSumOf (List.replicate n c) (φ l) → b = c) :
    φ = ψ := by
  have hdiv' : ∀ b : ℕ, 0 < b → ∀ hb0 hb1, φ (mkI (l / b) hb0 hb1) = ψ (mkI (l / b) hb0 hb1) := by
    intro b hb hb0 hb1
    refine hdiv b hb _ _ (hφ.replicate b (mkI (l / b) hb0 hb1) l (by simp; field_simp)) ?_
    rw [h]; exact hψ.replicate b (mkI (l / b) hb0 hb1) l (by simp; field_simp)
  have hfrac : ∀ x : I, ∀ q ∈ fracSet l x, φ q = ψ q := by
    rintro x q ⟨-, a, b, hb, hq⟩
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hb0 : (0 : ℝ) ≤ l / b := by positivity
    have hb1 : (l : ℝ) / b ≤ 1 := by
      rw [div_le_one hb']; have : (1 : ℝ) ≤ b := by exact_mod_cast hb
      linarith [l.2.2]
    have e1 := hφ.replicate a (mkI (l / b) hb0 hb1) q (by simp [hq]; ring)
    have e2 := hψ.replicate a (mkI (l / b) hb0 hb1) q (by simp [hq]; ring)
    rw [hdiv' b hb hb0 hb1] at e1
    exact isSumOf_unique e1 e2
  funext x
  have s1 := sea52_1_normal hφ (fracSet_nonempty l x) (fracSet_isLUB hl0 x)
  have s2 := sea52_1_normal hψ (fracSet_nonempty l x) (fracSet_isLUB hl0 x)
  rw [Set.image_congr (hfrac x)] at s1
  exact s1.unique s2

/-- **SEA 52.4** (`prop:add-into-nsea`, second.tex:1297, Proposition): if
`φ(λ) = ψ(λ)` for some `λ ∈ (0,1)` and additive `φ, ψ`, then `φ = ψ`.  Proof
as printed: `φ(λ/n) = ψ(λ/n)` by unique division (SEA 51, with SEA 52.3), so
`φ = ψ` on the dense set of `mλ/n`, hence everywhere by SEA 52.1
(`additive_eq_of_div`).  Takes SEA 35 as a hypothesis (through SEA 51). -/
theorem sea52_4_unique (h35 : SEA35.{u}) {ψ : I → E} (hφ : IsAdditive φ)
    (hψ : IsAdditive ψ) {l : I} (hl0 : 0 < (l : ℝ)) (hl1 : (l : ℝ) < 1) (h : φ l = ψ l) :
    φ = ψ := by
  refine additive_eq_of_div hφ hψ hl0 h fun n hn b c hb hc => ?_
  obtain ⟨a', -, -, huniq⟩ := sea51_division h35 (sea52_3_floor hφ hl1) hn
  exact (huniq b hb).trans (huniq c hc).symm

end Division


/-! ## Halves (SEA 53, 54) -/

/-- The scalar `1/2 ∈ [0,1]`. -/
noncomputable def halfI : I := mkI (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem halfI_val : ((halfI : I) : ℝ) = 1 / 2 := rfl

/-- **SEA 53** (`prophalvecentral`, second.tex:1428, Definition): `h` is a
*half* when `h ⋁ h = 1`. -/
def IsHalf {E : Type u} [EffectAlgebra E] (h : E) : Prop := ∃ hh : Perp h h, ovee h h hh = 1

section Halves

variable {E : Type u} [EffectAlgebra E]

omit [EffectAlgebra E] in
/-- A four-term rearrangement: `(a ⋁ b) ⋁ (c ⋁ d) = (a ⋁ c) ⋁ (b ⋁ d)`. -/
theorem ovee_ovee_comm4 {E : Type u} [EffectAlgebra E] {a b c d : E} (hab : Perp a b)
    (hcd : Perp c d) (hac : Perp a c) (hbd : Perp b d)
    (h : Perp (ovee a c hac) (ovee b d hbd)) :
    ∃ h' : Perp (ovee a b hab) (ovee c d hcd),
      ovee (ovee a b hab) (ovee c d hcd) h' = ovee (ovee a c hac) (ovee b d hbd) h := by
  have hsum := isSumOf_append (isSumOf_pair hac) (isSumOf_pair hbd) h
  have hperm : ([a, c] ++ [b, d]).Perm ([a, b] ++ [c, d]) := by
    simp only [List.cons_append, List.nil_append]
    exact List.Perm.cons _ (List.Perm.swap _ _ _)
  obtain ⟨t, t', ht, ht', h', e⟩ := isSumOf_append_split (PCM.isSumOf_perm hperm hsum)
  have e1 := isSumOf_unique ht (isSumOf_pair hab)
  have e2 := isSumOf_unique ht' (isSumOf_pair hcd)
  subst e1; subst e2
  exact ⟨h', e⟩

variable [SEAlgebra E]

/-- Commuting halves are equal (first half of the proof of SEA 54). -/
theorem halves_eq_of_commutes {h g : E} (hh : IsHalf h) (hg : IsHalf g) (hc : Commutes h g) :
    h = g := by
  obtain ⟨hhh, eh⟩ := hh
  obtain ⟨hgg, eg⟩ := hg
  obtain ⟨h1, e1⟩ := seq_ovee h hgg
  obtain ⟨h2, e2⟩ := seq_ovee g hhh
  calc h = h ⊙ 1 := (seq_one h).symm
    _ = h ⊙ ovee g g hgg := by rw [eg]
    _ = ovee (h ⊙ g) (h ⊙ g) h1 := e1
    _ = ovee (g ⊙ h) (g ⊙ h) h2 := PCM.ovee_congr hc hc _ _
    _ = g ⊙ ovee h h hhh := e2.symm
    _ = g := by rw [eh, seq_one]

/-- `a = (a ⊙ h) ⋁ (a ⊙ h)` for a half `h`. -/
theorem isSumOf_seq_half {h : E} (hh : IsHalf h) (a : E) :
    PCM.IsSumOf (List.replicate 2 (a ⊙ h)) a := by
  obtain ⟨hhh, eh⟩ := hh
  have := seq_isSumOf a (isSumOf_pair hhh)
  rw [eh, seq_one] at this
  exact this

/-- **SEA 54** (`prophalvecentral`, second.tex:1431, Proposition): a half is
central iff it is the only half.  Proof as printed: commuting halves are equal;
conversely `a ⊙ h ⋁ a⊥ ⊙ h` is a half, hence `h`, and `a` commutes with both
summands.  (Normality, assumed in the print, is not used.) -/
theorem sea54_half_central_iff {h : E} (hh : IsHalf h) :
    IsCentral h ↔ ∀ g : E, IsHalf g → g = h := by
  constructor
  · intro hc g hg; exact (halves_eq_of_commutes hh hg (hc g)).symm
  · intro hu b
    have hp : Perp (b ⊙ h) (orth b ⊙ h) :=
      perp_of_le (seq_le_left b h) (seq_le_left (orth b) h) (EffectAlgebra.perp_orth b)
    -- `k = b ⊙ h ⋁ b⊥ ⊙ h` is a half
    have hk : IsHalf (ovee (b ⊙ h) (orth b ⊙ h) hp) := by
      have h1 := isSumOf_seq_half hh b
      have h2 := isSumOf_seq_half hh (orth b)
      have hsum := isSumOf_append h1 h2 (EffectAlgebra.perp_orth b)
      rw [EffectAlgebra.ovee_orth] at hsum
      have hperm : (List.replicate 2 (b ⊙ h) ++ List.replicate 2 (orth b ⊙ h)).Perm
          ([b ⊙ h, orth b ⊙ h] ++ [b ⊙ h, orth b ⊙ h]) := by
        simp only [List.replicate, List.cons_append, List.nil_append]
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      obtain ⟨t, t', ht, ht', h', e⟩ := isSumOf_append_split (PCM.isSumOf_perm hperm hsum)
      have e1 := isSumOf_unique ht (isSumOf_pair hp)
      have e2 := isSumOf_unique ht' (isSumOf_pair hp)
      subst e1; subst e2
      exact ⟨h', e⟩
    have hkh := hu _ hk
    have c1 : Commutes (b ⊙ h) b := commutes_replicate (isSumOf_seq_half hh b)
    have c2 : Commutes (orth b ⊙ h) b := by
      have := (commutes_replicate (isSumOf_seq_half hh (orth b))).orth_r
      rwa [orth_orth] at this
    have := Commutes.ovee hp c1.symm c2.symm
    rw [hkh] at this
    exact this.symm

end Halves

/-! ## A-convex actions from additive maps (SEA 55) -/

section FromPhi

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

theorem halfI_pos : (0 : ℝ) < (halfI : I) := by simp

theorem halfI_lt_one : ((halfI : I) : ℝ) < 1 := by simp; norm_num

/-- `2 · (1/2) = 1` in `[0,1]`. -/
theorem two_mul_halfI : ((2 : ℕ) : ℝ) * (halfI : I) = ((1 : I) : ℝ) := by simp

/-- The action of an a-convex action on a fixed element is additive in the
scalar. -/
theorem AConvexAction.additive {F : Type u} [EffectAlgebra F] (A : AConvexAction F) (a : F) :
    IsAdditive (fun l => A.act l a) := fun l m n h => A.act_add l m n a h

/-- `½ · a` is a half of `a`. -/
theorem AConvexAction.half_sum {F : Type u} [EffectAlgebra F] (A : AConvexAction F) (a : F) :
    PCM.IsSumOf (List.replicate 2 (A.act halfI a)) a := by
  have := (A.additive a).replicate 2 halfI 1 two_mul_halfI
  rwa [A.one_act] at this

/-- The a-convex action `λ ·_φ a = a ⊙ φ(λ)` of SEA 55. -/
noncomputable def actOfPhi (h35 : SEA35.{u}) {φ : I → E} (hφ : IsAdditive φ)
    (h1 : φ 1 = 1) : AConvexAction E where
  act l a := a ⊙ φ l
  act_act l m a := by
    show (a ⊙ φ m) ⊙ φ l = a ⊙ φ (l * m)
    have hF := hφ.seq (a ⊙ φ m)
    have hG := (hφ.comp_mul m).seq a
    have hhalf : (a ⊙ φ m) ⊙ φ halfI = a ⊙ φ (halfI * m) := by
      by_cases hm : (m : ℝ) = 1
      · have : m = 1 := Subtype.ext hm
        subst this
        rw [h1, seq_one, mul_one]
      · have hm' : (m : ℝ) < 1 := lt_of_le_of_ne m.2.2 hm
        obtain ⟨a', -, -, huniq⟩ :=
          sea51_division h35 (sea52_3_floor (hφ.seq a) hm') two_pos
        have e1 : (a ⊙ φ m) ⊙ φ halfI = a' := huniq _ (by
          have := hF.replicate 2 halfI 1 two_mul_halfI
          simp only [h1, seq_one] at this; exact this)
        have e2 : a ⊙ φ (halfI * m) = a' := huniq _ (by
          have := hG.replicate 2 halfI 1 two_mul_halfI
          simp only [one_mul] at this; exact this)
        rw [e1, e2]
    have := sea52_4_unique h35 hF hG halfI_pos halfI_lt_one hhalf
    exact congrFun this l
  act_add l m n a h := (hφ.seq a) l m n h
  one_act a := by show a ⊙ φ 1 = a; rw [h1, seq_one]

/-- **SEA 55** (`prop:a-convex-from-phi`, second.tex:1465, Proposition): in a
normal SEA, a unital additive `φ : [0,1] → E` gives an a-convex action
`λ ·_φ a = a ⊙ φ(λ)` (`actOfPhi`); and an a-convex action `·` is of this form
iff `λ · a = a ⊙ (λ · 1)` for all `a, λ`.  Proof as printed: the only
non-trivial axiom, `μ ·_φ (λ ·_φ a) = (μλ) ·_φ a`, reduces by SEA 52.4 to
`μ = 1/2`, where both sides are halves of `λ ·_φ a`, whose floor is `0`
(SEA 52.3 for `μ ↦ a ⊙ φ(μ)`), so they agree by SEA 51.  Uses SEA 35 and
OAP 47 (through SEA 51, 52.4); SEA 35 is a hypothesis. -/
theorem sea55_aconvex_from_phi (h35 : SEA35.{u}) :
    (∀ (φ : I → E) (hφ : IsAdditive φ) (h1 : φ 1 = 1) (l : I) (a : E),
      (actOfPhi h35 hφ h1).act l a = a ⊙ φ l) ∧
    ∀ A : AConvexAction E,
      (∃ (φ : I → E) (hφ : IsAdditive φ) (h1 : φ 1 = 1), A = actOfPhi h35 hφ h1) ↔
        ∀ (l : I) (a : E), A.act l a = a ⊙ A.act l 1 := by
  refine ⟨fun _ _ _ _ _ => rfl, fun A => ⟨?_, fun hA => ?_⟩⟩
  · rintro ⟨φ, hφ, h1, rfl⟩ l a
    show a ⊙ φ l = a ⊙ ((1 : E) ⊙ φ l)
    rw [one_seq]
  · refine ⟨fun l => A.act l 1, A.additive 1, A.one_act 1, ?_⟩
    ext l a
    exact hA l a

/-! ### Scalars in the bicommutant of a half -/

attribute [local instance] booleanEffectMonoid in
/-- The scalars of `{h}''` for a half `h` (used in SEA 57 and 58): the
bicommutant `{h}''` is a directed-complete effect monoid with a half, hence
`[0,1]_{C(X)}` (SEA 35; the Boolean summand vanishes), and `λ ↦ λ𝟙` gives a
unital additive `φ : [0,1] → E` with `φ(1/2) = h` and values in `{h}''`.
Uses SEA 35 (a hypothesis) and OAP 47 (`oap47_holds`). -/
theorem half_scalars (h35 : SEA35.{u}) {h : E} (hh : IsHalf h) :
    ∃ φ : I → E, IsAdditive φ ∧ φ 1 = 1 ∧ φ halfI = h ∧
      ∀ l, φ l ∈ bicommutant ({h} : Set E) := by
  let _ := bicommEM {h} (singleton_commuting h)
  obtain ⟨X, tX, cX, hX, -, B, cB, ⟨Φ⟩⟩ :=
    @dcem_structure h35 oap47_holds _ (bicommEM {h} (singleton_commuting h))
      (bicommEM_dc {h} (singleton_commuting h))
  let hM : (bicommutantSub ({h} : Set E)).carrier := ⟨h, subset_bicommutant _ rfl⟩
  obtain ⟨hhh, eh⟩ := hh
  have hMM : Perp hM hM := hhh
  have eM : ovee hM hM hMM = 1 := Subtype.ext eh
  have hPP : Perp (Φ.toFun hM) (Φ.toFun hM) := (Φ.perp_iff _ _).mpr hMM
  have eP := Φ.map_ovee hM hM hMM hPP
  rw [eM, Φ.map_one] at eP
  set f := Φ.toFun hM with hf
  have hb1 : f.2 ⊓ f.2 = ⊥ := hPP.2
  have hb2 : f.2 ⊔ f.2 = ⊤ := (congrArg Prod.snd eP).symm
  have hf2 : f.2 = ⊥ := by rw [← hb1, inf_idem]
  have hbt : (⊥ : B) = ⊤ := by rw [← hb2, sup_idem, hf2]
  have hf1 : f.1.1 + f.1.1 = 1 := (congrArg (fun z : CXI X × B => z.1.1) eP).symm
  let ψ : I → CXI X × B := fun l => (cxScale l 1, ⊥)
  have hψadd : ∀ l m n : I, (l : ℝ) + m = n →
      ∃ hp : Perp (ψ l) (ψ m), ovee (ψ l) (ψ m) hp = ψ n := by
    intro l m n hlmn
    have hp : Perp (ψ l) (ψ m) := by
      refine ⟨?_, show (⊥ : B) ⊓ ⊥ = ⊥ from inf_idem _⟩
      show (l : ℝ) • (1 : C(X, ℝ)) + (m : ℝ) • 1 ≤ 1
      rw [← add_smul, hlmn]; exact (cxScale n 1).2.2
    refine ⟨hp, Prod.ext (Subtype.ext ?_) (sup_idem _)⟩
    show (l : ℝ) • (1 : C(X, ℝ)) + (m : ℝ) • 1 = (n : ℝ) • 1
    rw [← add_smul, hlmn]
  refine ⟨fun l => (Φ.invFun (ψ l)).1, ?_, ?_, ?_, fun l => (Φ.invFun (ψ l)).2⟩
  · intro l m n hlmn
    obtain ⟨hp, e⟩ := hψadd l m n hlmn
    have hp' := (Φ.symm.perp_iff (ψ l) (ψ m)).mpr hp
    refine ⟨hp', ?_⟩
    have := Φ.symm.map_ovee (ψ l) (ψ m) hp hp'
    rw [e] at this
    exact (congrArg Subtype.val this).symm
  · have : ψ 1 = 1 := Prod.ext (Subtype.ext (one_smul ℝ _)) hbt
    show (Φ.symm.toFun (ψ 1)).1 = 1
    rw [this]; exact congrArg Subtype.val Φ.symm.map_one
  · have : ψ halfI = f := by
      refine Prod.ext (Subtype.ext ?_) hf2.symm
      show ((1 / 2 : ℝ)) • (1 : C(X, ℝ)) = f.1.1
      have h2 : (1 / 2 : ℝ) • (f.1.1 + f.1.1) = f.1.1 := by
        rw [← two_smul ℝ, smul_smul]; norm_num
      rw [hf1] at h2; exact h2
    show (Φ.invFun (ψ halfI)).1 = h
    rw [this, hf, Φ.symm_apply]

end FromPhi


/-! ## Characterisations of convexity (SEA 57) -/

/-- The centre `Z(E)` as a sub-normal-SEA: the commutant of `E` (SEA 26, 28). -/
noncomputable def centerSub (E : Type u) [EffectAlgebra E] [NormalSEA E] : SubNormalSEA E :=
  commutantSub Set.univ

theorem mem_centerSub {E : Type u} [EffectAlgebra E] [NormalSEA E] {a : E} :
    a ∈ (centerSub E).carrier ↔ a ∈ center E :=
  ⟨fun h b => h b trivial, fun h b _ => h b⟩

/-- A convex action restricts to a sub-effect algebra closed under it. -/
@[instance_reducible] noncomputable def restrictConvex {E : Type u} [EffectAlgebra E]
    (C : ConvexAction E) (T : SubEffectAlgebra E)
    (hT : ∀ (l : I) (a : E), a ∈ T.carrier → (AConvexAction.ofConvex C).act l a ∈ T.carrier) :
    ConvexAction T.carrier :=
  let _ := C
  { smul := fun l a => ⟨l • a.1, hT l a.1 a.2⟩
    mul_smul := fun l m a => Subtype.ext (EffectModule.mul_smul l m a.1)
    smul_perp := fun l {a b} h => by
      obtain ⟨h', e⟩ := EffectModule.smul_perp (M := I) l (show Perp a.1 b.1 from h)
      exact ⟨h', Subtype.ext e⟩
    perp_smul := fun {l m} h a => by
      obtain ⟨h', e⟩ := EffectModule.perp_smul (M := I) h a.1
      exact ⟨h', Subtype.ext e⟩
    one_smul := fun a => Subtype.ext (EffectModule.one_smul (M := I) a.1) }

section Thm57

/-- In a convex effect algebra every half is `½ · 1` (proof of SEA 57,
1 ⇒ 4, as printed: `h = (½ ⋁ ½)·h = ½·h ⋁ ½·h = ½·(h ⋁ h) = ½·1`). -/
theorem convex_half_eq {E : Type u} [EffectAlgebra E] (C : ConvexAction E) {h : E}
    (hh : IsHalf h) : h = (AConvexAction.ofConvex C).act halfI 1 := by
  let _ := C
  obtain ⟨hhh, eh⟩ := hh
  have hp : Perp halfI halfI := show ((halfI : I) : ℝ) + halfI ≤ 1 by
    simp only [halfI_val]; norm_num
  have e1 : ovee halfI halfI hp = (1 : I) := Subtype.ext (by
    show ((halfI : I) : ℝ) + halfI = 1; simp only [halfI_val]; norm_num)
  obtain ⟨h1, e2⟩ := EffectModule.perp_smul (M := I) hp h
  obtain ⟨h2, e3⟩ := EffectModule.smul_perp (M := I) halfI hhh
  rw [e1, EffectModule.one_smul] at e2
  rw [eh] at e3
  show h = halfI • (1 : E)
  rw [← e2, ← e3]

/-- **SEA 57**, 1 ⇒ 4. -/
theorem sea57_1_4 {E : Type u} [EffectAlgebra E] (hc : IsConvex E) : ∃! h : E, IsHalf h := by
  obtain ⟨C⟩ := hc
  exact ⟨(AConvexAction.ofConvex C).act halfI 1,
    isSumOf_two_iff.mp ((AConvexAction.ofConvex C).half_sum 1), fun g hg => convex_half_eq C hg⟩

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 57**, 4 ⇒ 3 (SEA 54). -/
theorem sea57_4_3 (H : ∃! h : E, IsHalf h) : ∃ h : E, IsCentral h ∧ IsHalf h := by
  obtain ⟨h, hh, hu⟩ := H
  exact ⟨h, (sea54_half_central_iff hh).mpr hu, hh⟩

/-- **SEA 57**, 3 ⇒ 5: with a central half `h`, every `a` has the unique half
`h ⊙ a`. -/
theorem sea57_3_5 (H : ∃ h : E, IsCentral h ∧ IsHalf h) :
    ∀ a : E, ∃! b : E, ∃ hb : Perp b b, ovee b b hb = a := by
  obtain ⟨h, hc, hh⟩ := H
  intro a
  refine ⟨a ⊙ h, isSumOf_two_iff.mp (isSumOf_seq_half hh a), fun b ⟨hbb, eb⟩ => ?_⟩
  obtain ⟨hhh, eh⟩ := hh
  obtain ⟨h1, e1⟩ := seq_ovee b hhh
  obtain ⟨h2, e2⟩ := seq_ovee h hbb
  calc b = b ⊙ 1 := (seq_one b).symm
    _ = b ⊙ ovee h h hhh := by rw [eh]
    _ = ovee (b ⊙ h) (b ⊙ h) h1 := e1
    _ = ovee (h ⊙ b) (h ⊙ b) h2 := PCM.ovee_congr (hc b).symm (hc b).symm _ _
    _ = h ⊙ ovee b b hbb := e2.symm
    _ = h ⊙ a := by rw [eb]
    _ = a ⊙ h := hc a

/-- With unique halves there is at most one a-convex action (SEA 57, 5 ⇒ 2,
uniqueness: both `½ ·ᵢ a` are halves of `a`, then SEA 52.4). -/
theorem aconvex_eq_of_halves (h35 : SEA35.{u})
    (H : ∀ a : E, ∃! b : E, ∃ hb : Perp b b, ovee b b hb = a) (A1 A2 : AConvexAction E) :
    A1 = A2 := by
  ext l a
  have e : A1.act halfI a = A2.act halfI a := by
    obtain ⟨b, -, hu⟩ := H a
    exact (hu _ (isSumOf_two_iff.mp (A1.half_sum a))).trans
      (hu _ (isSumOf_two_iff.mp (A2.half_sum a))).symm
  exact congrFun (sea52_4_unique h35 (A1.additive a) (A2.additive a) halfI_pos halfI_lt_one e) l

/-- **SEA 57**, 5 ⇒ 2: uniqueness as above; existence from the scalars of
`{h}''` for a half `h` of `1` (`half_scalars`) and SEA 55. -/
theorem sea57_5_2 (h35 : SEA35.{u})
    (H : ∀ a : E, ∃! b : E, ∃ hb : Perp b b, ovee b b hb = a) :
    ∃ A : AConvexAction E, ∀ A' : AConvexAction E, A' = A := by
  obtain ⟨h, hh, -⟩ := H 1
  obtain ⟨φ, hφ, h1, -, -⟩ := half_scalars h35 hh
  exact ⟨actOfPhi h35 hφ h1, fun A' => aconvex_eq_of_halves h35 H A' _⟩

/-- **SEA 57**, 2 ⇒ 4: `½ · 1` is a half; any half `h` is `φ(½)` for the
scalars `φ` of `{h}''`, and `·_φ` is the unique action, so `h = ½ · 1`. -/
theorem sea57_2_4 (h35 : SEA35.{u})
    (H : ∃ A : AConvexAction E, ∀ A' : AConvexAction E, A' = A) : ∃! h : E, IsHalf h := by
  obtain ⟨A, hA⟩ := H
  refine ⟨A.act halfI 1, isSumOf_two_iff.mp (A.half_sum 1), fun g hg => ?_⟩
  obtain ⟨φ, hφ, h1, hφh, -⟩ := half_scalars h35 hg
  rw [← hA (actOfPhi h35 hφ h1)]
  show g = (1 : E) ⊙ φ halfI
  rw [one_seq, hφh]

/-- `λ · a ≼ a` for an a-convex action. -/
theorem AConvexAction.act_le {F : Type u} [EffectAlgebra F] (A : AConvexAction F) (l : I)
    (a : F) : A.act l a ≼ a := by
  obtain ⟨hp, e⟩ := A.act_add l (mkI (1 - l) (by linarith [l.2.2]) (by linarith [l.2.1])) 1 a
    (by simp)
  rw [A.one_act] at e
  have := left_le_ovee hp; rwa [e] at this

/-- **SEA 57**, 2 ⇒ 1: the unique a-convex action is additive, since
`λ ↦ λ·(a ⋁ b)` and `λ ↦ λ·a ⋁ λ·b` are additive (the latter defined as
`λ·a ≼ a` and `λ·b ≼ b`) and agree at `½` by uniqueness of halves (2 ⇒ 4 ⇒ 3
⇒ 5), hence everywhere by SEA 52.4. -/
theorem sea57_2_1 (h35 : SEA35.{u})
    (H : ∃ A : AConvexAction E, ∀ A' : AConvexAction E, A' = A) : IsConvex E := by
  have Hhalves := sea57_3_5 (sea57_4_3 (sea57_2_4 h35 H))
  obtain ⟨A, -⟩ := H
  refine ⟨A.toConvex fun l a b hab => ?_⟩
  have hperp : ∀ l : I, Perp (A.act l a) (A.act l b) := fun l =>
    perp_of_le (A.act_le l a) (A.act_le l b) hab
  let G : I → E := fun l => ovee (A.act l a) (A.act l b) (hperp l)
  have hG : IsAdditive G := by
    intro l m n hlmn
    obtain ⟨ha, ea⟩ := A.act_add l m n a hlmn
    obtain ⟨hb, eb⟩ := A.act_add l m n b hlmn
    have hn : Perp (ovee (A.act l a) (A.act m a) ha) (ovee (A.act l b) (A.act m b) hb) := by
      rw [ea, eb]; exact hperp n
    obtain ⟨h', e⟩ := ovee_ovee_comm4 (hperp l) (hperp m) ha hb hn
    exact ⟨h', e.trans (PCM.ovee_congr ea eb _ _)⟩
  have ehalf : A.act halfI (ovee a b hab) = G halfI := by
    obtain ⟨c, -, hu⟩ := Hhalves (ovee a b hab)
    refine (hu _ (isSumOf_two_iff.mp (A.half_sum _))).trans (hu _ ?_).symm
    obtain ⟨hp, e⟩ := hG halfI halfI 1 (by simp only [halfI_val, Set.Icc.coe_one]; norm_num)
    exact ⟨hp, e.trans (PCM.ovee_congr (A.one_act a) (A.one_act b) _ _)⟩
  have := congrFun (sea52_4_unique h35 (A.additive (ovee a b hab)) hG halfI_pos
    halfI_lt_one ehalf) l
  exact ⟨hperp l, this.symm⟩

/-- For the unique a-convex action, `λ · a = a ⊙ (λ · 1)` (SEA 55 gives the
action `a ⊙ (λ · 1)`, which must be the same). -/
theorem act_eq_seq_of_unique (h35 : SEA35.{u}) (A : AConvexAction E)
    (hA : ∀ A' : AConvexAction E, A' = A) (l : I) (a : E) : A.act l a = a ⊙ A.act l 1 := by
  have e := hA (actOfPhi h35 (A.additive 1) (A.one_act 1))
  exact (congrArg (fun B : AConvexAction E => B.act l a) e).symm

/-- **SEA 57**, 2 ⇒ 6: `λ · a = a ⊙ (λ · 1)`; `½ · 1` is the unique half,
hence central (SEA 54), so `{½ · 1}'' = Z(E)`; the scalars of `{½·1}''` agree
with `λ ↦ λ · 1` at `½`, hence everywhere (SEA 52.4), so `λ · 1` is central,
and so is `a ⊙ (λ · 1)` for central `a`. -/
theorem sea57_2_6 (h35 : SEA35.{u})
    (H : ∃ A : AConvexAction E, ∀ A' : AConvexAction E, A' = A) :
    IsAConvex E ∧ ∀ A : AConvexAction E, ∀ (l : I) (a : E), a ∈ center E →
      A.act l a ∈ center E := by
  have Hu := sea57_2_4 h35 H
  obtain ⟨A, hA⟩ := H
  refine ⟨⟨A⟩, fun A' l a ha => ?_⟩
  rw [hA A', act_eq_seq_of_unique h35 A hA l a]
  have hhalf : IsHalf (A.act halfI 1) := isSumOf_two_iff.mp (A.half_sum 1)
  have hcent : IsCentral (A.act halfI 1) :=
    (sea54_half_central_iff hhalf).mpr fun g hg => Hu.unique hg hhalf
  obtain ⟨φ, hφ, -, hφh, hφmem⟩ := half_scalars h35 hhalf
  have hφeq : φ = fun l => A.act l 1 :=
    sea52_4_unique h35 hφ (A.additive 1) halfI_pos halfI_lt_one hφh
  have hc : IsCentral (A.act l 1) := by
    have hmem := hφmem l
    rw [hφeq] at hmem
    intro b
    exact hmem b (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact (hcent b).symm)
  intro b
  exact (Commutes.seq (ha b).symm (hc b).symm).symm

/-- **SEA 57**, 6 ⇒ 3: `½ · 1` is a central half. -/
theorem sea57_6_3
    (H : IsAConvex E ∧ ∀ A : AConvexAction E, ∀ (l : I) (a : E), a ∈ center E →
      A.act l a ∈ center E) : ∃ h : E, IsCentral h ∧ IsHalf h := by
  obtain ⟨⟨A⟩, hres⟩ := H
  refine ⟨A.act halfI 1, hres A halfI 1 (fun b => ?_), isSumOf_two_iff.mp (A.half_sum 1)⟩
  show (1 : E) ⊙ b = b ⊙ 1
  rw [one_seq, seq_one]

/-- **SEA 57**, (1 & 6) ⇒ 7: the convex action restricts to `Z(E)`. -/
theorem sea57_1_7 (h35 : SEA35.{u}) (hc : IsConvex E) :
    IsConvex (centerSub E).carrier := by
  have H6 := sea57_2_6 h35 (sea57_5_2 h35 (sea57_3_5 (sea57_4_3 (sea57_1_4 hc))))
  obtain ⟨C⟩ := hc
  exact ⟨restrictConvex C (centerSub E).toSubEffectAlgebra fun l a ha =>
    mem_centerSub.mpr (H6.2 _ l a (mem_centerSub.mp ha))⟩

/-- **SEA 57**, 7 ⇒ 3: `½ · 1` computed in `Z(E)` is a central half. -/
theorem sea57_7_3 (hc : IsConvex (centerSub E).carrier) : ∃ h : E, IsCentral h ∧ IsHalf h := by
  obtain ⟨C⟩ := hc
  let k := (AConvexAction.ofConvex C).act halfI 1
  obtain ⟨hp, e⟩ := isSumOf_two_iff.mp ((AConvexAction.ofConvex C).half_sum 1)
  exact ⟨k.1, mem_centerSub.mp k.2, hp, congrArg Subtype.val e⟩

/-- **SEA 57** (`thm-a-convex-thm`, second.tex:1539, Theorem): for a normal
SEA `E` the following are equivalent:
1. there is a convex action on `E`;
2. there is precisely one a-convex action on `E`;
3. there is a central `h` with `h ⋁ h = 1`;
4. there is precisely one `h` with `h ⋁ h = 1`;
5. every `a` has precisely one `b` with `b ⋁ b = a`;
6. there is an a-convex action, and every a-convex action restricts to `Z(E)`;
7. `Z(E)` is convex.

Proof as printed: 1 ⇒ 4 ⇒ 3 ⇒ 5 ⇒ 2 ⇒ 1 (with 2 ⇒ 4), 6 ⇒ 3, 2 ⇒ 6,
1 & 6 ⇒ 7, and 7 ⇒ 3 ("7 ⇒ 1 is obvious": through the central half `½ · 1`).
Takes SEA 35 as a hypothesis (the scalars of `{h}''`, SEA 51, 52.4). -/
theorem sea57_convex_tfae (h35 : SEA35.{u}) :
    List.TFAE [IsConvex E,
      (∃ A : AConvexAction E, ∀ A' : AConvexAction E, A' = A),
      (∃ h : E, IsCentral h ∧ IsHalf h),
      (∃! h : E, IsHalf h),
      (∀ a : E, ∃! b : E, ∃ hb : Perp b b, ovee b b hb = a),
      (IsAConvex E ∧ ∀ A : AConvexAction E, ∀ (l : I) (a : E), a ∈ center E →
        A.act l a ∈ center E),
      IsConvex (centerSub E).carrier] := by
  tfae_have 1 → 4 := sea57_1_4
  tfae_have 4 → 3 := sea57_4_3
  tfae_have 3 → 5 := sea57_3_5
  tfae_have 5 → 2 := sea57_5_2 h35
  tfae_have 2 → 1 := sea57_2_1 h35
  tfae_have 2 → 6 := sea57_2_6 h35
  tfae_have 6 → 3 := sea57_6_3
  tfae_have 1 → 7 := sea57_1_7 h35
  tfae_have 7 → 3 := sea57_7_3
  tfae_finish

/-- **SEA 57** (`thm-a-convex-thm`, second.tex:1539, Theorem), "moreover":
when `E` is convex, the unique a-convex action satisfies
`λ · a = a ⊙ (λ · 1)`. -/
theorem sea57_moreover (h35 : SEA35.{u}) (hc : IsConvex E)
    (A : AConvexAction E) (l : I) (a : E) : A.act l a = a ⊙ A.act l 1 := by
  obtain ⟨A0, hA0⟩ := sea57_5_2 h35 (sea57_3_5 (sea57_4_3 (sea57_1_4 hc)))
  have hA : ∀ A' : AConvexAction E, A' = A := fun A' => (hA0 A').trans (hA0 A).symm
  exact act_eq_seq_of_unique h35 A hA l a

end Thm57


/-! ## The maximal a-convex idempotent (SEA 58) and the splitting (SEA 59, 60) -/

/-- The SEA of a Boolean algebra, `a ⊙ b = a ∧ b` (SEA 30 with SEA 32). -/
@[instance_reducible] noncomputable def boolSEA (B : Type u) [BooleanAlgebra B] :
    @SEAlgebra B (booleanEffectAlgebra B) :=
  @commEMToSEA B (booleanEffectMonoid B) (fun x y => inf_comm x y)

/-- A copy of `F`, to carry a Boolean-algebra structure on `F` without
clashing with the effect algebra of `F`. -/
def BoolCopy (F : Type u) : Type u := F

/-- The identity from a Boolean SEA to its Boolean algebra (SEA 44), as an
isomorphism of SEAs onto the SEA of a Boolean algebra. -/
noncomputable def boolCopyIso {F : Type u} [EffectAlgebra F] [SEAlgebra F]
    [cba : CompleteBooleanAlgebra F] (hseq : ∀ a b : F, a ⊙ b = a ⊓ b)
    (hperp : ∀ a b : F, Perp a b ↔ a ⊓ b = ⊥)
    (hovee : ∀ (a b : F) (h : Perp a b), ovee a b h = a ⊔ b) (h1 : (1 : F) = ⊤) :
    @SEAIso F (BoolCopy F) _ (@booleanEffectAlgebra (BoolCopy F) cba.toBooleanAlgebra) _
      (@boolSEA (BoolCopy F) cba.toBooleanAlgebra) :=
  letI : EffectAlgebra (BoolCopy F) := @booleanEffectAlgebra (BoolCopy F) cba.toBooleanAlgebra
  letI : SEAlgebra (BoolCopy F) := @boolSEA (BoolCopy F) cba.toBooleanAlgebra
  ⟨⟨⟨fun a => a, fun a => a, fun _ => rfl, fun _ => rfl⟩, h1, fun a b => (hperp a b).symm,
    fun a b h _ => hovee a b h⟩, fun a b => hseq a b⟩

/-- SEA 44 (`sea44_complete`, `Papers/SEA/Boolean.lean`) in the form SEA 59
and 60 use: a normal Boolean SEA is isomorphic, as a SEA with `a ⊙ b = a ∧ b`,
to a complete Boolean algebra. -/
theorem boolean_normal_iso {F : Type u} [EffectAlgebra F] [NormalSEA F] (hB : IsBooleanSEA F) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
      Nonempty (@SEAIso F B _ (booleanEffectAlgebra B) _ (boolSEA B)) := by
  obtain ⟨cba, -, hseq, hperp, hovee, -, h1, -⟩ := sea44_complete hB
  exact ⟨BoolCopy F, cba, ⟨boolCopyIso hseq hperp hovee h1⟩⟩

section Thm58

variable {E : Type u} [EffectAlgebra E]

/-- `[x, y]` has sum `t` iff `x ⊥ y` and `x ⋁ y = t`. -/
theorem isSumOf_pair_iff {x y t : E} : PCM.IsSumOf [x, y] t ↔ ∃ h : Perp x y, ovee x y h = t := by
  constructor
  · intro hs
    obtain ⟨t0, ht0, h, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
    have : t0 = y := isSumOf_unique ht0 (isSumOf_replicate_one y)
    subst this; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact isSumOf_pair h

/-- `(x ⋁ x) ⊥ (a ⋁ a)` gives `x ⊥ a` and `(x ⋁ a) ⊥ (x ⋁ a)`. -/
theorem selfSummable_of_doubles {x a : E} (hx : Perp x x) (ha : Perp a a)
    (h : Perp (ovee x x hx) (ovee a a ha)) :
    ∃ hxa : Perp x a, Perp (ovee x a hxa) (ovee x a hxa) := by
  have hsum := isSumOf_append (isSumOf_pair hx) (isSumOf_pair ha) h
  have hperm : ([x, x] ++ [a, a]).Perm ([x, a] ++ [x, a]) := by
    simp only [List.cons_append, List.nil_append]
    exact List.Perm.cons _ (List.Perm.swap _ _ _)
  obtain ⟨t, t', ht, ht', h', -⟩ := isSumOf_append_split (PCM.isSumOf_perm hperm hsum)
  obtain ⟨hxa, e1⟩ := isSumOf_pair_iff.mp ht
  obtain ⟨hxa', e2⟩ := isSumOf_pair_iff.mp ht'
  subst e1; subst e2
  exact ⟨hxa, h'⟩

variable [NormalSEA E]

/-- **SEA 58** (`thm:a-convexthm`, second.tex:1768, Theorem): in a normal SEA
`E`, the set `S` of idempotents `p` for which `p ⊙ E` carries an a-convex
action has a greatest (in particular maximal) element `p₀`; `p₀` is central
and `p₀⊥ ⊙ E` is Boolean.  Proof as printed: Zorn gives a maximal
self-summable `a` (a chain's supremum `u` has `u ≼ ⋀ d⊥ = u⊥`); `p = a ⋁ a`
is idempotent because `(p⊥)² ⊙ p ⋁ a` is self-summable (so `(p⊥)² ⊙ p = 0`,
`(p⊥ ⊙ p)² = 0`, SEA 22); `p⊥` is Boolean because `a ⋁ s ⊙ s⊥` is
self-summable for `s ≼ p⊥` (SEA 18, 19); `p, p⊥` are central (SEA 42); `a` is
a half of `p` in the normal SEA `p ⊙ E`, whose scalars give the a-convex action
(SEA 55); and for `q ∈ S`, `½ · (p⊥ ⊙ q)` is a self-summable idempotent, so
`p⊥ ⊙ q = 0`, i.e. `q ≼ p`.  Takes SEA 35 as a hypothesis (the scalars,
SEA 55); SEA 42 is `sea42_central` (`Papers/SEA/Boolean.lean`). -/
theorem sea58_maximal (h35 : SEA35.{u}) :
    ∃ p0 : E, (IsIdempotent p0 ∧ IsAConvex (Downset p0)) ∧
      (∀ q : E, IsIdempotent q → IsAConvex (Downset q) → q ≼ p0) ∧
      IsCentral p0 ∧ IsBooleanIdempotent (orth p0) := by
  -- a maximal self-summable element, by Zorn's lemma
  have hchain : ∀ c : Set {x : E // Perp x x}, IsChain (fun x y => x.1 ≼ y.1) c →
      ∃ ub : {x : E // Perp x x}, ∀ z ∈ c, z.1 ≼ ub.1 := by
    intro c hc
    rcases c.eq_empty_or_nonempty with hce | hcne
    · exact ⟨⟨0, PCM.zero_perp 0⟩, by simp [hce]⟩
    · let D : Set E := Subtype.val '' c
      have hD : EDirected D := by
        obtain ⟨z, hz⟩ := hcne
        refine ⟨⟨z.1, z, hz, rfl⟩, ?_⟩
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        by_cases hxy : x = y
        · subst hxy; exact ⟨x.1, ⟨x, hx, rfl⟩, le_refl' _, le_refl' _⟩
        · rcases hc hx hy hxy with h | h
          · exact ⟨y.1, ⟨y, hy, rfl⟩, h, le_refl' _⟩
          · exact ⟨x.1, ⟨x, hx, rfl⟩, le_refl' _, h⟩
      obtain ⟨u, hu⟩ := NormalSEA.directedComplete D hD
      have hdd : ∀ d ∈ D, ∀ d' ∈ D, d' ≼ orth d := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        by_cases hxy : x = y
        · subst hxy; exact perp_iff_le_orth.mp x.2
        · rcases hc hx hy hxy with h | h
          · exact le_trans' (perp_iff_le_orth.mp y.2) (orth_le_orth h)
          · exact le_trans' h (perp_iff_le_orth.mp x.2)
      have huu : u ≼ orth u := by
        have hinf := eIsInf_orth_of_eIsSup hu
        refine hinf.2 u ?_
        rintro _ ⟨d, hd, rfl⟩
        exact hu.2 _ (fun d' hd' => hdd d hd d' hd')
      exact ⟨⟨u, perp_iff_le_orth.mpr huu⟩, fun z hz => hu.1 _ ⟨z, hz, rfl⟩⟩
  obtain ⟨⟨a, ha⟩, hmax⟩ := exists_maximal_of_chains_bounded
    (r := fun x y : {x : E // Perp x x} => x.1 ≼ y.1) hchain (fun h1 h2 => le_trans' h1 h2)
  -- maximality in the form used twice below
  have hext : ∀ z (hz : Perp z z), Perp (ovee z z hz) (ovee a a ha) → z = 0 := by
    intro z hz h
    obtain ⟨hza, hself⟩ := selfSummable_of_doubles hz ha h
    have h1 : a ≼ ovee z a hza := right_le_ovee hza
    have e : ovee z a hza = a := le_antisymm' (hmax ⟨ovee z a hza, hself⟩ h1) h1
    have e' : ovee a z (PCM.perp_comm hza) = a := by rw [← PCM.ovee_comm hza]; exact e
    exact eq_zero_of_ovee_eq_self _ e'
  set p := ovee a a ha with hpdef
  -- `p` is an idempotent
  have hqp : Commutes (orth p) p := (commutes_orth_self p).symm
  have hqq : Perp (orth p ⊙ p) (orth p ⊙ p) := by
    have := sea19_selfSummable (orth p); rwa [orth_orth] at this
  obtain ⟨h2, e2⟩ := seq_ovee (orth p) hqq
  have hz0 : orth p ⊙ (orth p ⊙ p) = 0 := by
    have hle : ovee _ _ h2 ≼ orth p := by rw [← e2]; exact seq_le_left _ _
    exact hext _ h2 (perp_iff_le_orth.mpr hle)
  have hsq : (orth p ⊙ p) ⊙ (orth p ⊙ p) = 0 :=
    calc (orth p ⊙ p) ⊙ (orth p ⊙ p) = (p ⊙ orth p) ⊙ (orth p ⊙ p) :=
          congrArg (fun w => w ⊙ (orth p ⊙ p)) hqp
      _ = p ⊙ (orth p ⊙ (orth p ⊙ p)) := (hqp.symm.assoc _).symm
      _ = 0 := by rw [hz0, seq_zero]
  have hpid : IsIdempotent p :=
    (isIdempotent_iff p).mpr (seq_zero_comm (sea22_noNilpotents hsq))
  -- `p⊥` is Boolean
  have hbool : ∀ s : E, s ≼ orth p → IsIdempotent s := by
    intro s hs
    have hss := sea19_selfSummable s
    have hle : ovee _ _ hss ≼ orth p := sea18_ovee_le hpid.compl
      (le_trans' (seq_le_left _ _) hs) (le_trans' (seq_le_left _ _) hs) hss
    exact (isIdempotent_iff s).mpr (hext _ hss (perp_iff_le_orth.mpr hle))
  have hqc : IsCentral (orth p) := sea42_central ⟨hpid.compl, hbool⟩
  have hpc : IsCentral p := by have := hqc.orth_central; rwa [orth_orth] at this
  -- `p ⊙ E` is a-convex: `a` is a half of `p`
  have hconv : IsAConvex (Downset p) := by
    let _ : NormalSEA (Downset p) := cornerNormalSEA hpid
    let a' : Downset p := ⟨a, left_le_ovee ha⟩
    have hhalf : IsHalf a' := ⟨⟨ha, le_refl' p⟩, Subtype.ext rfl⟩
    obtain ⟨φ, hφ, h1, -, -⟩ := half_scalars h35 hhalf
    exact ⟨actOfPhi h35 hφ h1⟩
  refine ⟨p, ⟨hpid, hconv⟩, fun q hq ⟨B⟩ => ?_, hpc, hpid.compl, hbool⟩
  -- maximality: `½ · (p⊥ ⊙ q)` is a self-summable idempotent
  have hr1 : orth p ⊙ q ≼ orth p := seq_le_left _ _
  have hr2 : orth p ⊙ q ≼ q := by rw [hqc q]; exact seq_le_left _ _
  let r' : Downset q := ⟨orth p ⊙ q, hr2⟩
  obtain ⟨hp2, e2⟩ := isSumOf_two_iff.mp (B.half_sum r')
  have hk : (B.act halfI r').1 ≼ orth p := le_trans' (downset_le_iff.mp (B.act_le halfI r')) hr1
  have hk0 : (B.act halfI r').1 = 0 :=
    idempotent_selfSummable_eq_zero (hbool _ hk) hp2.1
  have hr0 : orth p ⊙ q = 0 := by
    have := congrArg Subtype.val e2
    simp only [downset_ovee_val] at this
    rw [PCM.ovee_congr hk0 hk0 hp2.1 (PCM.zero_perp 0), zero_ovee_eq] at this
    exact this.symm
  exact ((sea17_5 hpid q).2.2.2).mpr hr0

/-- **SEA 59** (`thm:SEAsplitupinconvexandsharp`, second.tex:1856, Theorem): a
normal SEA is `E ≅ E₁ ⊕ E₂` with `E₁` a-convex and `E₂` a complete Boolean
algebra.  Proof as printed: `p₀` of SEA 58 is central, `E ≅ p₀ ⊙ E ⊕ p₀⊥ ⊙ E`
(SEA 24), and the Boolean normal SEA `p₀⊥ ⊙ E` is a complete Boolean algebra
(SEA 44, `sea44_complete`).  Takes SEA 35 as a hypothesis. -/
theorem sea59_split (h35 : SEA35.{u}) :
    ∃ (E1 E2 : Type u) (_ : EffectAlgebra E1) (_ : SEAlgebra E1) (_ : EffectAlgebra E2)
      (_ : SEAlgebra E2), IsAConvex E1 ∧
      (∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@SEAIso E2 B _ (booleanEffectAlgebra B) _ (boolSEA B))) ∧
      Nonempty (@SEAIso E (E1 × E2) _ _ _ (prodSEA E1 E2)) := by
  obtain ⟨p, ⟨hp, hconv⟩, -, hc, hb⟩ := sea58_maximal (E := E) h35
  let _ : NormalSEA (Downset (orth p)) := cornerNormalSEA hp.compl
  have hBool : IsBooleanSEA (Downset (orth p)) := (isBooleanIdempotent_iff hp.compl).mpr hb.2
  obtain ⟨B, cB, hiso⟩ := boolean_normal_iso hBool
  exact ⟨Downset p, Downset (orth p), _, cornerSEA hp, _, cornerSEA hp.compl, hconv,
    ⟨B, cB, hiso⟩, ⟨sea24_centralSplit hp hc⟩⟩

end Thm58

section Finite

variable {E : Type u} [EffectAlgebra E]

/-- A greatest element of `S` is its supremum. -/
theorem eIsSup_of_max {S : Set E} {m : E} (hm : m ∈ S) (h : ∀ s ∈ S, s ≼ m) : EIsSup S m :=
  ⟨h, fun _ hy => hy m hm⟩

/-- A directed subset of a finite effect algebra has a greatest element. -/
theorem finite_directed_max [Finite E] {S : Set E} (hS : EDirected S) :
    ∃ m ∈ S, ∀ s ∈ S, s ≼ m := by
  classical
  obtain ⟨⟨s0, hs0⟩, hdir⟩ := hS
  have key : ∀ T : Finset E, (↑T ⊆ S) → ∃ m ∈ S, ∀ t ∈ T, t ≼ m := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨s0, hs0, by simp⟩
    | insert x T _ ih =>
      intro hT
      obtain ⟨m, hm, hmT⟩ := ih (fun y hy => hT (Finset.mem_insert_of_mem hy))
      obtain ⟨c, hc, hxc, hmc⟩ := hdir x (hT (Finset.mem_insert_self x T)) m hm
      refine ⟨c, hc, fun t ht => ?_⟩
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hxc
      · exact le_trans' (hmT t ht) hmc
  obtain ⟨m, hm, hmS⟩ := key (Set.toFinite S).toFinset (by simp)
  exact ⟨m, hm, fun s hs => hmS s (by simp [hs])⟩

/-- A finite SEA is normal (first step of the proof of SEA 60: a directed set
contains its supremum). -/
@[instance_reducible] noncomputable def finiteNormalSEA (E : Type u) [EffectAlgebra E]
    [SEAlgebra E] [Finite E] : NormalSEA E :=
  { (inferInstance : SEAlgebra E) with
    directedComplete := fun S hS =>
      let ⟨m, hm, hmax⟩ := finite_directed_max hS
      ⟨m, eIsSup_of_max hm hmax⟩
    seq_sup := fun a S x hS hx => by
      obtain ⟨m, hm, hmax⟩ := finite_directed_max hS
      have : x = m := hx.unique (eIsSup_of_max hm hmax)
      subst this
      exact eIsSup_of_max ⟨x, hm, rfl⟩ (by rintro _ ⟨s, hs, rfl⟩; exact seq_mono a (hmax s hs))
    comm_sup := fun a S x hS hx hc => by
      obtain ⟨m, hm, hmax⟩ := finite_directed_max hS
      have : x = m := hx.unique (eIsSup_of_max hm hmax)
      subst this; exact hc x hm }

/-- On a non-trivial effect algebra, `λ ↦ λ · 1` is injective for any
a-convex action (so a non-trivial a-convex effect algebra is infinite). -/
theorem AConvexAction.injective_of_ne (A : AConvexAction E) (hne : (1 : E) ≠ 0) :
    Function.Injective (fun l : I => A.act l 1) := by
  have key : ∀ l m : I, l < m → A.act l 1 = A.act m 1 → False := by
    intro l m hlm e
    have hlm' : (l : ℝ) < m := hlm
    have hφ := A.additive 1
    let δ : I := mkI (m - l) (by linarith) (by linarith [l.2.1, m.2.2])
    obtain ⟨h1, e1⟩ := A.act_add l δ m 1 (by simp [δ])
    have hδ : A.act δ 1 = 0 := by
      rw [← e] at e1; exact eq_zero_of_ovee_eq_self h1 e1
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ((m : ℝ) - l))
    have hδpos : (0 : ℝ) < m - l := by linarith
    have hn0 : (0 : ℝ) < n := lt_trans (one_div_pos.mpr hδpos) hn
    have hv0 : (0 : ℝ) ≤ 1 / n := by positivity
    have hv1 : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hn0]; have : 0 < n := by exact_mod_cast hn0
      exact_mod_cast this
    have hvδ : mkI (1 / n) hv0 hv1 ≤ δ := by
      show (1 : ℝ) / n ≤ m - l
      rw [div_le_iff₀ hn0]; rw [div_lt_iff₀ hδpos] at hn; linarith
    have hv : A.act (mkI (1 / n) hv0 hv1) 1 = 0 := eq_zero_of_le_zero (hδ ▸ hφ.mono hvδ)
    have hrep := hφ.replicate n (mkI (1 / n) hv0 hv1) 1 (by simp; field_simp)
    rw [hv] at hrep
    have h10 : A.act 1 1 = 0 := isSumOf_unique hrep (isSumOf_replicate_zero n)
    exact hne (by rw [← h10, A.one_act])
  intro l m e
  rcases lt_trichotomy l m with h | h | h
  · exact (key l m h e).elim
  · exact h
  · exact (key m l h e.symm).elim

/-- **SEA 60** (`cor:finite-Boolean`, second.tex:1869, Corollary): a SEA with
finitely many elements is a Boolean algebra (with `a ⊙ b = a ∧ b`).  Proof as
printed: `E` is normal (directed sets contain their suprema); in the splitting
of SEA 58/59 the a-convex part would contain a continuum of elements unless it
is `{0}`, so `E` is Boolean, hence a Boolean algebra (SEA 44).  Takes SEA 35
as a hypothesis. -/
theorem sea60_finite_boolean (h35 : SEA35.{u})
    (E : Type u) [EffectAlgebra E] [SEAlgebra E] [Finite E] :
    ∃ (B : Type u) (_ : BooleanAlgebra B),
      Nonempty (@SEAIso E B _ (booleanEffectAlgebra B) _ (boolSEA B)) := by
  let _ : NormalSEA E := finiteNormalSEA E
  obtain ⟨p, ⟨hp, ⟨A⟩⟩, -, -, hb⟩ := sea58_maximal (E := E) h35
  have h10 : (1 : Downset p) = 0 := by
    by_contra hne
    have hinj := A.injective_of_ne hne
    have : Finite I := Finite.of_injective _ hinj
    have hinf : Infinite I := Set.Icc.infinite (by norm_num)
    exact not_finite I
  have hp0 : p = 0 := congrArg Subtype.val h10
  have hBool : IsBooleanSEA E := fun s => hb.2 s (by rw [hp0, eabasics_orth_zero]; exact le_one' s)
  obtain ⟨B, cB, hiso⟩ := boolean_normal_iso hBool
  exact ⟨B, inferInstance, hiso⟩

end Finite

/-! ## Horizontal sums (SEA 47) -/

/-- **SEA 47** (`def:horizontal-sum`, second.tex:1179, Definition): the
*horizontal sum* `HS(E_α, I)` of effect algebras `E_α`: their disjoint union
with all zeros identified and all ones identified.  Encoded with canonical
representatives: `zero`, `one`, and `mid α a` for `a ∈ E_α \ {0, 1}`.  (The
print's quotient `(∐ E_α)/∼` agrees with this when every `E_α` is non-trivial
and `I` is non-empty; see `HSum.mk_eq_mk_iff_of_ne`, `HSum.mk_perp_mk_iff_of_ne`.) -/
inductive HSum {ι : Type v} (E : ι → Type u) [∀ i, EffectAlgebra (E i)] : Type (max u v) where
  | zero : HSum E
  | one : HSum E
  | mid (i : ι) (a : E i) (h0 : a ≠ 0) (h1 : a ≠ 1) : HSum E

namespace HSum

variable {ι : Type v} {E : ι → Type u} [∀ i, EffectAlgebra (E i)]

open Classical in
/-- The element `(a, α)` of the horizontal sum. -/
noncomputable def mk (i : ι) (a : E i) : HSum E :=
  if h0 : a = 0 then zero else if h1 : a = 1 then one else mid i a h0 h1

theorem mk_of_eq_zero {i : ι} {a : E i} (h : a = 0) : mk i a = zero := by
  unfold mk; split_ifs; rfl

theorem mk_zero (i : ι) : mk i (0 : E i) = zero := mk_of_eq_zero rfl

theorem mk_of_eq_one {i : ι} {a : E i} (h0 : a ≠ 0) (h : a = 1) : mk i a = one := by
  unfold mk; split_ifs <;> first | rfl | contradiction

theorem mk_of_ne {i : ι} {a : E i} (h0 : a ≠ 0) (h1 : a ≠ 1) : mk i a = mid i a h0 h1 := by
  unfold mk; split_ifs <;> first | rfl | contradiction

theorem mk_cases (i : ι) (a : E i) :
    (a = 0 ∧ mk i a = zero) ∨ (a ≠ 0 ∧ a = 1 ∧ mk i a = one) ∨
      ∃ h0 h1, mk i a = mid i a h0 h1 := by
  by_cases h0 : a = 0
  · exact Or.inl ⟨h0, mk_of_eq_zero h0⟩
  · by_cases h1 : a = 1
    · exact Or.inr (Or.inl ⟨h0, h1, mk_of_eq_one h0 h1⟩)
    · exact Or.inr (Or.inr ⟨h0, h1, mk_of_ne h0 h1⟩)

theorem mk_eq_zero_iff {i : ι} {a : E i} : mk i a = zero ↔ a = 0 := by
  rcases mk_cases i a with ⟨h, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;> rw [hm]
  · exact Iff.intro (fun _ => h) (fun _ => rfl)
  · exact Iff.intro (fun e => by cases e) (fun e => absurd e h0)
  · exact Iff.intro (fun e => by cases e) (fun e => absurd e h0)

theorem mk_eq_one_iff {i : ι} {a : E i} : mk i a = one ↔ a ≠ 0 ∧ a = 1 := by
  rcases mk_cases i a with ⟨h, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;> rw [hm]
  · exact Iff.intro (fun e => by cases e) (fun e => absurd h e.1)
  · exact Iff.intro (fun _ => ⟨h0, h1⟩) (fun _ => rfl)
  · exact Iff.intro (fun e => by cases e) (fun e => absurd e.2 h1)

/-- Summability in the horizontal sum. -/
def Perp' : HSum E → HSum E → Prop
  | zero, _ => True
  | one, zero => True
  | one, one => False
  | one, mid .. => False
  | mid .., zero => True
  | mid .., one => False
  | mid i a _ _, mid j b _ _ => ∃ e : i = j, Perp (e ▸ a : E j) b

/-- The partial sum in the horizontal sum. -/
noncomputable def ovee' : (x y : HSum E) → Perp' x y → HSum E
  | zero, y, _ => y
  | one, zero, _ => one
  | one, one, h => False.elim h
  | one, mid .., h => False.elim h
  | mid i a h0 h1, zero, _ => mid i a h0 h1
  | mid _ _ _ _, one, h => False.elim h
  | mid _ a _ _, mid j b _ _, h => mk j (ovee (h.1 ▸ a : E j) b h.2)

/-- The complement in the horizontal sum, `(a, α)⊥ = (a⊥, α)`. -/
def orth' : HSum E → HSum E
  | zero => one
  | one => zero
  | mid i a h0 h1 => mid i (orth a)
      (fun h => h1 (by rw [← orth_orth a, h, eabasics_orth_zero]))
      (fun h => h0 (by rw [← orth_orth a, h, eabasics_orth_one]))

theorem perp_mid_mid {i : ι} {a b : E i} {ha0 ha1 hb0 hb1} :
    Perp' (mid i a ha0 ha1) (mid i b hb0 hb1) ↔ Perp a b :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

theorem ovee_mid_mid {i : ι} {a b : E i} {ha0 ha1 hb0 hb1}
    (h : Perp' (mid i a ha0 ha1) (mid i b hb0 hb1)) :
    ovee' _ _ h = mk i (ovee a b (perp_mid_mid.mp h)) := rfl

theorem ovee'_congr {x x' y y' : HSum E} (hx : x = x') (hy : y = y') (h : Perp' x y)
    (h' : Perp' x' y') : ovee' x y h = ovee' x' y' h' := by
  subst hx; subst hy; rfl

/-- `a ↦ (a, α)` is additive. -/
theorem mk_perp_ovee {i : ι} {a b : E i} (h : Perp a b) :
    ∃ h' : Perp' (mk i a) (mk i b), ovee' (mk i a) (mk i b) h' = mk i (ovee a b h) := by
  rcases mk_cases i a with ⟨ha, hma⟩ | ⟨ha0, ha1, hma⟩ | ⟨ha0, ha1, hma⟩
  · subst ha; rw [hma]; exact ⟨trivial, by rw [zero_ovee_eq]; rfl⟩
  · have hb : b = 0 := EffectAlgebra.eq_zero_of_perp_one (PCM.perp_comm (ha1 ▸ h))
    subst hb; rw [hma, mk_zero]
    exact ⟨trivial, by rw [ovee_zero_eq, hma]; rfl⟩
  · rcases mk_cases i b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩
    · subst hb; rw [hma, hmb]; exact ⟨trivial, by rw [ovee_zero_eq, hma]; rfl⟩
    · exact absurd (EffectAlgebra.eq_zero_of_perp_one (hb1 ▸ h)) ha0
    · rw [hma, hmb]; exact ⟨perp_mid_mid.mpr h, rfl⟩

/-- `(a, α)` determines `a`. -/
theorem mk_injective (i : ι) : Function.Injective (mk (E := E) i) := by
  intro a b e
  rcases mk_cases i a with ⟨ha, hma⟩ | ⟨ha0, ha1, hma⟩ | ⟨ha0, ha1, hma⟩
  · rw [hma, eq_comm, mk_eq_zero_iff] at e; rw [ha, e]
  · rw [hma, eq_comm, mk_eq_one_iff] at e; rw [ha1, e.2]
  · rw [hma] at e
    rcases mk_cases i b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩ <;> rw [hmb] at e
    · exact nomatch e
    · exact nomatch e
    · cases e; rfl

/-- **SEA 47**, the identification of the print: for non-trivial summands,
`(a, α) = (b, β)` with `α ≠ β` iff `a = b = 0` or `a = b = 1`. -/
theorem mk_eq_mk_iff_of_ne {i j : ι} (hij : i ≠ j) (hi : (1 : E i) ≠ 0) (hj : (1 : E j) ≠ 0)
    (a : E i) (b : E j) : mk i a = mk j b ↔ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  constructor
  · intro e
    rcases mk_cases i a with ⟨ha, hma⟩ | ⟨ha0, ha1, hma⟩ | ⟨ha0, ha1, hma⟩ <;> rw [hma] at e
    · exact Or.inl ⟨ha, mk_eq_zero_iff.mp e.symm⟩
    · exact Or.inr ⟨ha1, (mk_eq_one_iff.mp e.symm).2⟩
    · rcases mk_cases j b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩ <;> rw [hmb] at e
      · exact nomatch e
      · exact nomatch e
      · exact absurd (HSum.mid.inj e).1 hij
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [mk_zero, mk_zero]
    · rw [mk_of_eq_one hi rfl, mk_of_eq_one hj rfl]

noncomputable instance : EffectAlgebra (HSum E) where
  zero := zero
  one := one
  Perp := Perp'
  ovee := ovee'
  orth := orth'
  perp_comm := by
    intro x y h
    cases x <;> cases y <;> first
      | trivial
      | exact h
      | (obtain ⟨rfl, h⟩ := h; exact ⟨rfl, PCM.perp_comm h⟩)
  ovee_comm := by
    intro x y h
    cases x <;> cases y <;> first
      | rfl
      | exact (False.elim h)
      | (obtain ⟨rfl, h⟩ := h; exact congrArg (mk _) (PCM.ovee_comm h))
  perp_of_ovee_perp := by
    intro x y z hxy h
    cases x with
    | zero => exact h
    | one =>
      cases y with
      | zero => trivial
      | one => exact False.elim hxy
      | mid => exact False.elim hxy
    | mid i a ha0 ha1 =>
      cases y with
      | zero => trivial
      | one => exact False.elim hxy
      | mid j b hb0 hb1 =>
        obtain ⟨rfl, hab⟩ := hxy
        change Perp' (mk i (ovee a b hab)) z at h
        cases z with
        | zero => trivial
        | one =>
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩ <;>
            rw [hm] at h
          · exact absurd (eabasics_positivity hab hs).1 ha0
          · exact h
          · exact h
        | mid k c hc0 hc1 =>
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩ <;>
            rw [hm] at h
          · exact absurd (eabasics_positivity hab hs).1 ha0
          · exact False.elim h
          · obtain ⟨rfl, h⟩ := h
            exact ⟨rfl, PCM.perp_of_ovee_perp hab h⟩
  perp_ovee_of_ovee_perp := by
    intro x y z hxy h
    cases x with
    | zero => trivial
    | one =>
      cases y with
      | zero => exact h
      | one => exact False.elim hxy
      | mid => exact False.elim hxy
    | mid i a ha0 ha1 =>
      cases y with
      | zero => exact h
      | one => exact False.elim hxy
      | mid j b hb0 hb1 =>
        obtain ⟨rfl, hab⟩ := hxy
        change Perp' (mk i (ovee a b hab)) z at h
        cases z with
        | zero => exact ⟨rfl, hab⟩
        | one =>
          exfalso
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩ <;>
            rw [hm] at h
          · exact ha0 (eabasics_positivity hab hs).1
          · exact h
          · exact h
        | mid k c hc0 hc1 =>
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩ <;>
            rw [hm] at h
          · exact absurd (eabasics_positivity hab hs).1 ha0
          · exact False.elim h
          · obtain ⟨rfl, h⟩ := h
            have hbc := PCM.perp_of_ovee_perp hab h
            have hapc := PCM.perp_ovee_of_ovee_perp hab h
            show Perp' (mid i a ha0 ha1) (mk i (ovee b c hbc))
            rcases mk_cases i (ovee b c hbc) with ⟨hs', hm'⟩ | ⟨hs0', hs1', hm'⟩ | ⟨hs0', hs1'', hm'⟩ <;>
              rw [hm']
            · trivial
            · exact ha0 (EffectAlgebra.eq_zero_of_perp_one (hs1' ▸ hapc))
            · exact perp_mid_mid.mpr hapc
  ovee_assoc := by
    intro x y z hxy h
    cases x with
    | zero => rfl
    | one =>
      cases y with
      | zero =>
        cases z with
        | zero => rfl
        | one => exact False.elim h
        | mid => exact False.elim h
      | one => exact False.elim hxy
      | mid => exact False.elim hxy
    | mid i a ha0 ha1 =>
      cases y with
      | zero =>
        cases z with
        | zero => rfl
        | one => exact False.elim h
        | mid => rfl
      | one => exact False.elim hxy
      | mid j b hb0 hb1 =>
        obtain ⟨rfl, hab⟩ := hxy
        cases z with
        | zero =>
          show ovee' (mk i (ovee a b hab)) zero h = mk i (ovee a b _)
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩
          · rw [ovee'_congr hm rfl h trivial]; exact hm.symm
          · rw [ovee'_congr hm rfl h trivial]; exact hm.symm
          · rw [ovee'_congr hm rfl h trivial]; exact hm.symm
        | one =>
          exfalso
          change Perp' (mk i (ovee a b hab)) one at h
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩ <;>
            rw [hm] at h
          · exact ha0 (eabasics_positivity hab hs).1
          · exact h
          · exact h
        | mid k c hc0 hc1 =>
          have h' := h
          change Perp' (mk i (ovee a b hab)) (mid k c hc0 hc1) at h'
          rcases mk_cases i (ovee a b hab) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩ <;>
            rw [hm] at h'
          · exact absurd (eabasics_positivity hab hs).1 ha0
          · exact False.elim h'
          · obtain ⟨rfl, habc⟩ := h'
            have hab' : Perp a b := hab
            have habc' : Perp (ovee a b hab') c := habc
            have hbc := PCM.perp_of_ovee_perp hab' habc'
            have hapc := PCM.perp_ovee_of_ovee_perp hab' habc'
            have hbc0 : ovee b c hbc ≠ 0 := fun e => hb0 (eabasics_positivity hbc e).1
            have hbc1 : ovee b c hbc ≠ 1 := fun e =>
              ha0 (EffectAlgebra.eq_zero_of_perp_one (e ▸ hapc))
            have e1 : ovee' (ovee' (mid i a ha0 ha1) (mid i b hb0 hb1) (perp_mid_mid.mpr hab'))
                (mid i c hc0 hc1) h = mk i (ovee (ovee a b hab') c habc') :=
              (ovee'_congr hm rfl h (perp_mid_mid.mpr habc')).trans rfl
            have e2 : ∀ p q, ovee' (mid i a ha0 ha1) (ovee' (mid i b hb0 hb1) (mid i c hc0 hc1) p) q
                = mk i (ovee a (ovee b c hbc) hapc) := by
              intro p q
              exact (ovee'_congr rfl (show ovee' (mid i b hb0 hb1) (mid i c hc0 hc1) p
                = mid i (ovee b c hbc) hbc0 hbc1 from mk_of_ne hbc0 hbc1) q
                (perp_mid_mid.mpr hapc)).trans rfl
            exact e1.trans ((congrArg (mk i) (PCM.ovee_assoc hab' habc')).trans (e2 _ _).symm)
  zero_perp := fun _ => trivial
  zero_ovee := fun _ => rfl
  perp_orth := by
    intro x
    cases x with
    | zero => trivial
    | one => trivial
    | mid i a h0 h1 => exact ⟨rfl, EffectAlgebra.perp_orth a⟩
  ovee_orth := by
    intro x
    cases x with
    | zero => rfl
    | one => rfl
    | mid i a h0 h1 =>
      show mk i (ovee a (orth a) _) = one
      rw [EffectAlgebra.ovee_orth]
      refine mk_of_eq_one (fun h => h0 ?_) rfl
      exact eq_zero_of_le_zero (h ▸ le_one' a)
  orth_unique := by
    intro x y h e
    cases x with
    | zero => exact e
    | one =>
      cases y with
      | zero => rfl
      | one => exact False.elim h
      | mid => exact False.elim h
    | mid i a h0 h1 =>
      cases y with
      | zero => exact nomatch e
      | one => exact False.elim h
      | mid j b hb0 hb1 =>
        obtain ⟨rfl, hab⟩ := h
        change mk i (ovee a b hab) = one at e
        have e' := EffectAlgebra.orth_unique hab (mk_eq_one_iff.mp e).2
        subst e'; rfl
  eq_zero_of_perp_one := by
    intro x h
    cases x with
    | zero => rfl
    | one => exact False.elim h
    | mid => exact False.elim h

@[simp] theorem zero_def : (0 : HSum E) = zero := rfl

@[simp] theorem one_def : (1 : HSum E) = one := rfl

theorem perp_def {x y : HSum E} : Perp x y ↔ Perp' x y := Iff.rfl

theorem ovee_def {x y : HSum E} (h : Perp x y) : ovee x y h = ovee' x y h := rfl

/-- **SEA 47**, summability of the print across summands: `(a, α) ⊥ (b, β)`
with `α ≠ β` iff `a = 0` or `b = 0`. -/
theorem mk_perp_mk_iff_of_ne {i j : ι} (hij : i ≠ j) (a : E i) (b : E j) :
    Perp (mk i a) (mk j b) ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rcases mk_cases i a with ⟨ha, hma⟩ | ⟨ha0, ha1, hma⟩ | ⟨ha0, ha1, hma⟩
    · exact Or.inl ha
    · rw [hma] at h
      rcases mk_cases j b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩
      · exact Or.inr hb
      · rw [hmb] at h; exact False.elim h
      · rw [hmb] at h; exact False.elim h
    · rw [hma] at h
      rcases mk_cases j b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩
      · exact Or.inr hb
      · rw [hmb] at h; exact False.elim h
      · rw [hmb] at h; obtain ⟨e, -⟩ := h; exact absurd e hij
  · rintro (rfl | rfl)
    · rw [mk_zero]; trivial
    · rw [mk_zero]; exact PCM.perp_zero _


/-! ### Order and suprema in a horizontal sum -/

theorem mk_ovee {i : ι} {a b : E i} (h : Perp a b) :
    ∃ h' : Perp (mk i a) (mk i b), ovee (mk i a) (mk i b) h' = mk i (ovee a b h) :=
  mk_perp_ovee h

theorem mk_perp_iff {i : ι} {a b : E i} : Perp (mk i a) (mk i b) ↔ Perp a b := by
  refine ⟨fun h => ?_, fun h => (mk_ovee h).1⟩
  rcases mk_cases i a with ⟨ha, hma⟩ | ⟨ha0, ha1, hma⟩ | ⟨ha0, ha1, hma⟩
  · rw [ha]; exact PCM.zero_perp b
  · rw [hma] at h
    rcases mk_cases i b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩ <;> rw [hmb] at h
    · rw [hb]; exact PCM.perp_zero a
    · exact False.elim h
    · exact False.elim h
  · rw [hma] at h
    rcases mk_cases i b with ⟨hb, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩ <;> rw [hmb] at h
    · rw [hb]; exact PCM.perp_zero a
    · exact False.elim h
    · exact perp_mid_mid.mp h

theorem mk_le_mk_of_le {i : ι} {a b : E i} (h : a ≼ b) : mk i a ≼ mk i b := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨h', e⟩ := mk_ovee (i := i) hd
  exact ⟨mk i d, h', e⟩

theorem mid_le_iff {i : ι} {a : E i} {h0 h1} {y : HSum E} :
    mid i a h0 h1 ≼ y ↔ y = one ∨ ∃ b h0' h1', y = mid i b h0' h1' ∧ a ≼ b := by
  constructor
  · rintro ⟨d, hd, e⟩
    cases d with
    | zero => exact Or.inr ⟨a, h0, h1, e.symm, le_refl' a⟩
    | one => exact False.elim hd
    | mid j c hc0 hc1 =>
      obtain ⟨rfl, hac⟩ := hd
      change mk i (ovee a c hac) = y at e
      rcases mk_cases i (ovee a c hac) with ⟨hs, hm⟩ | ⟨hs0, hs1, hm⟩ | ⟨hs0, hs1, hm⟩
      · exact absurd (eabasics_positivity hac hs).1 h0
      · exact Or.inl (e.symm.trans hm)
      · exact Or.inr ⟨_, hs0, hs1, e.symm.trans hm, left_le_ovee hac⟩
  · rintro (rfl | ⟨b, h0', h1', rfl, hab⟩)
    · exact le_one' _
    · have := mk_le_mk_of_le (i := i) hab
      rwa [mk_of_ne h0 h1, mk_of_ne h0' h1'] at this

theorem one_le_iff {y : HSum E} : one ≼ y ↔ y = one :=
  ⟨fun h => le_antisymm' (le_one' y) h, fun h => h ▸ le_refl' _⟩

theorem mk_le_mk_iff {i : ι} {a b : E i} : mk i a ≼ mk i b ↔ a ≼ b := by
  refine ⟨fun h => ?_, mk_le_mk_of_le⟩
  rcases mk_cases i a with ⟨ha, hma⟩ | ⟨ha0, ha1, hma⟩ | ⟨ha0, ha1, hma⟩
  · rw [ha]; exact zero_le' b
  · rw [hma] at h
    have := (mk_eq_one_iff.mp (one_le_iff.mp h)).2
    rw [ha1, this]; exact le_refl' _
  · rw [hma] at h
    rcases mid_le_iff.mp h with hb | ⟨b', h0', h1', hb, hab⟩
    · rw [(mk_eq_one_iff.mp hb).2]; exact le_one' a
    · rcases mk_cases i b with ⟨hb0, hmb⟩ | ⟨hb0, hb1, hmb⟩ | ⟨hb0, hb1, hmb⟩ <;>
        rw [hmb] at hb
      · exact nomatch hb
      · exact nomatch hb
      · cases hb; exact hab

theorem mk_le_mid_ne {i k : ι} (hik : i ≠ k) {v : E i} {w : E k} {h0 h1}
    (h : mk i v ≼ mid k w h0 h1) : v = 0 := by
  rcases mk_cases i v with ⟨hv, -⟩ | ⟨hv0, hv1, hm⟩ | ⟨hv0, hv1, hm⟩
  · exact hv
  · rw [hm, one_le_iff] at h; exact nomatch h
  · rw [hm] at h
    rcases mid_le_iff.mp h with h' | ⟨b, hb0, hb1, h', -⟩
    · exact nomatch h'
    · exact absurd (HSum.mid.inj h').1.symm hik

/-- `a ↦ (a, α)` preserves suprema. -/
theorem mk_isSup {i : ι} {T : Set (E i)} {t : E i} (ht : EIsSup T t) :
    EIsSup (mk i '' T) (mk i t) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩; exact mk_le_mk_of_le (ht.1 v hv)
  · by_cases hall : ∀ v ∈ T, v = 0
    · have : t = 0 :=
        le_antisymm' (ht.2 0 fun v hv => by rw [hall v hv]; exact le_refl' _) (zero_le' t)
      rw [this, mk_zero]; exact zero_le' y
    · push Not at hall
      obtain ⟨v0, hv0, hv00⟩ := hall
      cases y with
      | zero =>
        exact absurd (mk_eq_zero_iff.mp (eq_zero_of_le_zero (hy _ ⟨v0, hv0, rfl⟩))) hv00
      | one => exact le_one' _
      | mid k w hw0 hw1 =>
        by_cases hk : i = k
        · subst hk
          rw [← mk_of_ne hw0 hw1]
          refine mk_le_mk_of_le (ht.2 w fun v hv => mk_le_mk_iff.mp ?_)
          rw [mk_of_ne hw0 hw1]; exact hy _ ⟨v, hv, rfl⟩
        · exact absurd (mk_le_mid_ne hk (hy _ ⟨v0, hv0, rfl⟩)) hv00

/-- A directed subset of a horizontal sum contains `1`, or is `{0}`, or lies in
one summand. -/
theorem directed_cases {S : Set (HSum E)} (hS : EDirected S) :
    one ∈ S ∨ (∀ x ∈ S, x = zero) ∨
      ∃ (i : ι) (a : E i) (h0 : a ≠ 0) (h1 : a ≠ 1), mid i a h0 h1 ∈ S ∧
        ∀ x ∈ S, ∃ v : E i, x = mk i v := by
  by_cases h1S : one ∈ S
  · exact Or.inl h1S
  by_cases hz : ∀ x ∈ S, x = zero
  · exact Or.inr (Or.inl hz)
  push Not at hz
  obtain ⟨x, hx, hx0⟩ := hz
  cases x with
  | zero => exact absurd rfl hx0
  | one => exact absurd hx h1S
  | mid i a h0 h1 =>
    refine Or.inr (Or.inr ⟨i, a, h0, h1, hx, fun y hy => ?_⟩)
    cases y with
    | zero => exact ⟨0, (mk_zero i).symm⟩
    | one => exact absurd hy h1S
    | mid j b hb0 hb1 =>
      obtain ⟨c, hc, hac, hbc⟩ := hS.2 _ hx _ hy
      rcases mid_le_iff.mp hac with hc1 | ⟨c', hc0', hc1', rfl, -⟩
      · exact absurd (hc1 ▸ hc) h1S
      · rcases mid_le_iff.mp hbc with hc1 | ⟨c'', hc0'', hc1'', e, -⟩
        · exact nomatch hc1
        · obtain ⟨hij, -⟩ := HSum.mid.inj e
          subst hij; exact ⟨b, (mk_of_ne hb0 hb1).symm⟩

/-- A directed set inside one summand is the image of a directed set there. -/
theorem side_directed {i : ι} {S : Set (HSum E)} (hS : EDirected S)
    (hside : ∀ x ∈ S, ∃ v : E i, x = mk i v) :
    S = mk i '' {v | mk i v ∈ S} ∧ EDirected {v : E i | mk i v ∈ S} := by
  have hSeq : S = mk i '' {v | mk i v ∈ S} := by
    ext x; constructor
    · intro hx; obtain ⟨v, rfl⟩ := hside x hx; exact ⟨v, hx, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact hv
  refine ⟨hSeq, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hS.1; obtain ⟨v, rfl⟩ := hside x hx; exact ⟨v, hx⟩
  · intro u hu w hw
    obtain ⟨c, hc, huc, hwc⟩ := hS.2 _ hu _ hw
    obtain ⟨v, rfl⟩ := hside c hc
    exact ⟨v, hc, mk_le_mk_iff.mp huc, mk_le_mk_iff.mp hwc⟩

/-- **SEA 48** (first claim, in general): a horizontal sum of directed-complete
effect algebras is directed complete. -/
theorem directedComplete (hE : ∀ i, DirectedComplete (E i)) : DirectedComplete (HSum E) := by
  intro S hS
  rcases directed_cases hS with h1 | hz | ⟨i, a, h0, h1, ha, hside⟩
  · exact ⟨one, fun x _ => le_one' x, fun y hy => hy one h1⟩
  · exact ⟨zero, fun x hx => by rw [hz x hx]; exact le_refl' _, fun y _ => zero_le' y⟩
  · obtain ⟨hSeq, hT⟩ := side_directed hS hside
    obtain ⟨t, ht⟩ := hE i _ hT
    rw [hSeq]
    exact ⟨mk i t, mk_isSup ht⟩

end HSum

/-! ### Sequential products on horizontal sums -/

/-- The data of a sequential product on a horizontal sum of SEAs `E_α` (the
products of SEA 48 and SEA 56 are instances): maps `F α β : E_β → E_α`,
unital and additive, with `F α α = id`, such that `a ⊙ F α β b ≠ 0` for
`a ∈ E_α`, `b ∈ E_β` outside `{0, 1}` and `α ≠ β`.  The product is
`(a, α) ⊙ (b, β) = (a ⊙ F α β b, α)`. -/
structure HSMaps {ι : Type v} (E : ι → Type u) [∀ i, EffectAlgebra (E i)]
    [∀ i, SEAlgebra (E i)] where
  F : ∀ i j, E j → E i
  F_self : ∀ i (a : E i), F i i a = a
  F_one : ∀ i j, F i j 1 = 1
  F_add : ∀ i j {a b : E j} (h : Perp a b),
    ∃ h' : Perp (F i j a) (F i j b), ovee (F i j a) (F i j b) h' = F i j (ovee a b h)
  F_ne_zero : ∀ i j, i ≠ j → ∀ (a : E i) (b : E j), a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 →
    a ⊙ F i j b ≠ 0

namespace HSum

variable {ι : Type v} {E : ι → Type u} [∀ i, EffectAlgebra (E i)] [∀ i, SEAlgebra (E i)]
  (M : HSMaps E)

theorem hsmaps_F_zero (i j : ι) : M.F i j 0 = 0 := by
  obtain ⟨h', e⟩ := M.F_add i j (PCM.zero_perp (0 : E j))
  rw [zero_ovee_eq] at e
  exact eq_zero_of_ovee_self h' e

/-- The component of an element in the summand `E_α`, via `F`. -/
def proj (i : ι) : HSum E → E i
  | zero => 0
  | one => 1
  | mid j b _ _ => M.F i j b

/-- The sequential product on the horizontal sum. -/
noncomputable def seqH : HSum E → HSum E → HSum E
  | zero, _ => zero
  | one, y => y
  | mid i a _ _, y => mk i (a ⊙ proj M i y)

theorem proj_mk (i j : ι) (b : E j) : proj M i (mk j b) = M.F i j b := by
  rcases mk_cases j b with ⟨hb, hm⟩ | ⟨hb0, hb1, hm⟩ | ⟨hb0, hb1, hm⟩ <;> rw [hm]
  · rw [hb, hsmaps_F_zero M]; rfl
  · rw [hb1, M.F_one]; rfl
  · rfl

theorem proj_add (i : ι) {x y : HSum E} (h : Perp x y) :
    ∃ h' : Perp (proj M i x) (proj M i y), ovee (proj M i x) (proj M i y) h' = proj M i (ovee x y h) := by
  cases x with
  | zero => exact ⟨PCM.zero_perp _, zero_ovee_eq _ _⟩
  | one =>
    cases y with
    | zero => exact ⟨PCM.perp_zero _, ovee_zero_eq _ _⟩
    | one => exact False.elim h
    | mid => exact False.elim h
  | mid j a ha0 ha1 =>
    cases y with
    | zero => exact ⟨PCM.perp_zero _, ovee_zero_eq _ _⟩
    | one => exact False.elim h
    | mid k b hb0 hb1 =>
      obtain ⟨rfl, hab⟩ := h
      obtain ⟨h', e⟩ := M.F_add i j hab
      refine ⟨h', e.trans ?_⟩
      exact (proj_mk M i j _).symm

theorem seqH_zero_r (x : HSum E) : seqH M x zero = zero := by
  cases x with
  | zero => rfl
  | one => rfl
  | mid i a _ _ => show mk i (a ⊙ 0) = zero; rw [seq_zero, mk_zero]

theorem seqH_one_r (x : HSum E) : seqH M x one = x := by
  cases x with
  | zero => rfl
  | one => rfl
  | mid i a h0 h1 => show mk i (a ⊙ 1) = _; rw [seq_one, mk_of_ne h0 h1]

theorem seqH_mk_left {i : ι} {u : E i} (hu : u ≠ 1) (y : HSum E) :
    seqH M (mk i u) y = mk i (u ⊙ proj M i y) := by
  rcases mk_cases i u with ⟨h, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;> rw [hm]
  · rw [h, zero_seq, mk_zero]; rfl
  · exact absurd h1 hu
  · rfl

theorem seqH_mk_mk {i : ι} (u v : E i) : seqH M (mk i u) (mk i v) = mk i (u ⊙ v) := by
  by_cases hu : u = 1
  · have h10 : mk i u = one ∨ mk i u = zero := by
      rcases mk_cases i u with ⟨h, hm⟩ | ⟨-, -, hm⟩ | ⟨-, h1, -⟩
      · exact Or.inr hm
      · exact Or.inl hm
      · exact absurd hu h1
    rcases h10 with hm | hm
    · rw [hm, hu, one_seq]; rfl
    · rw [hm]
      have : u = 0 := mk_eq_zero_iff.mp hm
      rw [this, zero_seq, mk_zero]; rfl
  · rw [seqH_mk_left M hu, proj_mk, M.F_self]

omit [∀ i, SEAlgebra (E i)] in
theorem one_ne_zero_of_mid {i : ι} {a : E i} (h0 : a ≠ 0) : (1 : E i) ≠ 0 :=
  fun h => h0 (eq_zero_of_le_zero (h ▸ le_one' a))

omit [∀ i, SEAlgebra (E i)] in
theorem mk_one_of {i : ι} (h10 : (1 : E i) ≠ 0) : mk i (1 : E i) = one := mk_of_eq_one h10 rfl

omit [∀ i, SEAlgebra (E i)] in
theorem orth_mk {i : ι} (h10 : (1 : E i) ≠ 0) (u : E i) : orth (mk i u) = mk i (orth u) := by
  rcases mk_cases i u with ⟨h, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;> rw [hm]
  · rw [h, eabasics_orth_zero, mk_one_of h10]; rfl
  · rw [h1, eabasics_orth_one, mk_zero]; rfl
  · show mid i (orth u) _ _ = _
    rw [mk_of_ne]

/-- Elements commuting with `(z, α)` are the `(u, α)` with `z | u`. -/
theorem comm_mid_iff {i : ι} {z : E i} {h0 h1} {y : HSum E} :
    seqH M (mid i z h0 h1) y = seqH M y (mid i z h0 h1) ↔
      ∃ u : E i, y = mk i u ∧ z ⊙ u = u ⊙ z := by
  have hz : mid i z h0 h1 = mk i z := (mk_of_ne h0 h1).symm
  constructor
  · intro h
    cases y with
    | zero => exact ⟨0, (mk_zero i).symm, by rw [seq_zero, zero_seq]⟩
    | one => exact ⟨1, (mk_one_of (one_ne_zero_of_mid h0)).symm, by rw [seq_one, one_seq]⟩
    | mid j w hw0 hw1 =>
      by_cases hij : i = j
      · subst hij
        rw [hz, (mk_of_ne hw0 hw1).symm, seqH_mk_mk, seqH_mk_mk] at h
        exact ⟨w, (mk_of_ne hw0 hw1).symm, mk_injective i h⟩
      · exfalso
        have n1 := M.F_ne_zero i j hij z w h0 h1 hw0 hw1
        have n2 := M.F_ne_zero j i (Ne.symm hij) w z hw0 hw1 h0 h1
        have m1 : z ⊙ M.F i j w ≠ 1 := fun e => h1 (le_antisymm' (le_one' z)
          (e ▸ seq_le_left z _))
        have m2 : w ⊙ M.F j i z ≠ 1 := fun e => hw1 (le_antisymm' (le_one' w)
          (e ▸ seq_le_left w _))
        change mk i (z ⊙ proj M i (mid j w hw0 hw1)) = mk j (w ⊙ proj M j (mid i z h0 h1)) at h
        change mk i (z ⊙ M.F i j w) = mk j (w ⊙ M.F j i z) at h
        rw [mk_of_ne n1 m1, mk_of_ne n2 m2] at h
        exact hij (HSum.mid.inj h).1
  · rintro ⟨u, rfl, hu⟩
    rw [hz, seqH_mk_mk, seqH_mk_mk, hu]

/-- **SEA 48/56** (the general construction): the horizontal sum of SEAs with
the product `(a, α) ⊙ (b, β) = (a ⊙ F α β b, α)` is a SEA. -/
@[instance_reducible] noncomputable def hsSEA : SEAlgebra (HSum E) where
  seq := seqH M
  seq_add := by
    intro c a b h
    cases c with
    | zero => exact ⟨trivial, rfl⟩
    | one => exact ⟨h, rfl⟩
    | mid i z h0 h1 =>
      obtain ⟨hp, ep⟩ := proj_add M i h
      obtain ⟨hs, es⟩ := SequentialEffectAlgebra.seq_add z hp
      obtain ⟨hm, em⟩ := mk_ovee (i := i) hs
      refine ⟨hm, ?_⟩
      show ovee (mk i (z ⊙ proj M i a)) (mk i (z ⊙ proj M i b)) hm = mk i (z ⊙ proj M i (ovee a b h))
      rw [em, es, ep]
  one_seq := fun _ => rfl
  seq_zero_comm := by
    intro a b h
    cases a with
    | zero => exact seqH_zero_r M b
    | one => change b = zero at h; subst h; rfl
    | mid i x hx0 hx1 =>
      change mk i (x ⊙ proj M i b) = zero at h
      have h' := mk_eq_zero_iff.mp h
      cases b with
      | zero => rfl
      | one => exact absurd (by rwa [show proj M i one = 1 from rfl, seq_one] at h') hx0
      | mid j y hy0 hy1 =>
        by_cases hij : i = j
        · subst hij
          change x ⊙ M.F i i y = 0 at h'
          rw [M.F_self] at h'
          show mk i (y ⊙ M.F i i x) = zero
          rw [M.F_self, SequentialEffectAlgebra.seq_zero_comm x y h', mk_zero]
        · exact absurd h' (M.F_ne_zero i j hij x y hx0 hx1 hy0 hy1)
  seq_comm_orth := by
    intro a b h
    cases a with
    | zero => exact (seqH_zero_r M _).symm
    | one => exact (seqH_one_r M _).symm
    | mid i z h0 h1 =>
      obtain ⟨u, rfl, hu⟩ := (comm_mid_iff M).mp h
      refine (comm_mid_iff M).mpr ⟨orth u, orth_mk (one_ne_zero_of_mid h0) u, ?_⟩
      exact Commutes.orth_r (E := E i) hu
  seq_comm_assoc := by
    intro a b h c
    cases a with
    | zero => rfl
    | one => rfl
    | mid i z h0 h1 =>
      obtain ⟨u, rfl, hu⟩ := (comm_mid_iff M).mp h
      have hz : mid i z h0 h1 = mk i z := (mk_of_ne h0 h1).symm
      have hzu1 : z ⊙ u ≠ 1 := fun e => h1 (le_antisymm' (le_one' z) (e ▸ seq_le_left z u))
      show seqH M (seqH M (mid i z h0 h1) (mk i u)) c = seqH M (mid i z h0 h1) (seqH M (mk i u) c)
      rw [hz, seqH_mk_mk, seqH_mk_left M hzu1]
      by_cases hu1 : u = 1
      · subst hu1
        rw [mk_one_of (one_ne_zero_of_mid h0), seq_one, seqH_mk_left M h1]
        rfl
      · rw [seqH_mk_left M hu1 c, seqH_mk_left M h1, proj_mk, M.F_self,
          SequentialEffectAlgebra.seq_comm_assoc hu]
  seq_comm_compat := by
    intro a b c h hca hcb
    cases c with
    | zero => exact ⟨(seqH_zero_r M _).symm, (seqH_zero_r M _).symm⟩
    | one => exact ⟨(seqH_one_r M _).symm, (seqH_one_r M _).symm⟩
    | mid i z h0 h1 =>
      obtain ⟨u, rfl, hu⟩ := (comm_mid_iff M).mp hca
      obtain ⟨v, rfl, hv⟩ := (comm_mid_iff M).mp hcb
      have huv : Perp u v := mk_perp_iff.mp h
      refine ⟨(comm_mid_iff M).mpr ⟨u ⊙ v, seqH_mk_mk M u v, ?_⟩,
        (comm_mid_iff M).mpr ⟨ovee u v huv, (mk_ovee huv).2, ?_⟩⟩
      · exact (SequentialEffectAlgebra.seq_comm_compat huv hu hv).1
      · exact (SequentialEffectAlgebra.seq_comm_compat huv hu hv).2
  seq_comm_seq := by
    intro a b c hca hcb
    cases c with
    | zero => exact (seqH_zero_r M _).symm
    | one => exact (seqH_one_r M _).symm
    | mid i z h0 h1 =>
      obtain ⟨u, rfl, hu⟩ := (comm_mid_iff M).mp hca
      obtain ⟨v, rfl, hv⟩ := (comm_mid_iff M).mp hcb
      exact (comm_mid_iff M).mpr ⟨u ⊙ v, seqH_mk_mk M u v, SEAlgebra.seq_comm_seq hu hv⟩

end HSum


/-! ### Normality of horizontal sums -/

/-- The maps `F` of `HSMaps` are *normal*: they preserve directed suprema. -/
def HSMaps.IsNormal {ι : Type v} {E : ι → Type u} [∀ i, EffectAlgebra (E i)]
    [∀ i, SEAlgebra (E i)] (M : HSMaps E) : Prop :=
  ∀ i j {S : Set (E j)} {x : E j}, EDirected S → EIsSup S x → EIsSup (M.F i j '' S) (M.F i j x)

namespace HSum

variable {ι : Type v} {E : ι → Type u} [∀ i, EffectAlgebra (E i)] [∀ i, NormalSEA (E i)]
  (M : HSMaps E)

theorem proj_mono (i : ι) {x y : HSum E} (h : x ≼ y) : proj M i x ≼ proj M i y := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨h', e⟩ := proj_add M i hd
  rw [← e]; exact left_le_ovee h'

theorem proj_isSup (hF : M.IsNormal) (i : ι) {S : Set (HSum E)} {x : HSum E}
    (hS : EDirected S) (hx : EIsSup S x) : EIsSup (proj M i '' S) (proj M i x) := by
  rcases directed_cases hS with h1 | hz | ⟨j, a, h0, h1, ha, hside⟩
  · have hx1 : x = one := one_le_iff.mp (hx.1 one h1)
    subst hx1
    exact ⟨by rintro _ ⟨y, _, rfl⟩; exact le_one' _, fun y hy => hy _ ⟨one, h1, rfl⟩⟩
  · have hx0 : x = zero :=
      eq_zero_of_le_zero (hx.2 zero fun y hy => by rw [hz y hy]; exact le_refl' _)
    subst hx0
    refine ⟨?_, fun y _ => zero_le' y⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hz y hy]; exact le_refl' _
  · obtain ⟨hSeq, hT⟩ := side_directed hS hside
    obtain ⟨t, ht⟩ := NormalSEA.directedComplete _ hT
    have hxt : x = mk j t := hx.unique (by rw [hSeq]; exact mk_isSup ht)
    have hfun : (fun v => proj M i (mk j v)) = M.F i j := funext (proj_mk M i j)
    rw [hxt, hSeq, Set.image_image, hfun, proj_mk]
    exact hF i j hT ht

/-- **SEA 48/56** (the general construction): the horizontal sum of normal
SEAs, with normal maps `F`, is a normal SEA. -/
@[instance_reducible] noncomputable def hsNormalSEA (hF : M.IsNormal) : NormalSEA (HSum E) :=
  { hsSEA M with
    directedComplete := directedComplete fun _ => NormalSEA.directedComplete
    seq_sup := by
      intro a S x hS hx
      cases a with
      | zero =>
        refine ⟨?_, fun y _ => zero_le' y⟩
        rintro _ ⟨y, _, rfl⟩; exact le_refl' _
      | one =>
        show EIsSup ((fun y => y) '' S) x
        rw [Set.image_id']; exact hx
      | mid i z h0 h1 =>
        have h2 := proj_isSup M hF i hS hx
        have hD : EDirected (proj M i '' S) := eDirected_image hS fun _ _ => proj_mono M i
        have h3 := NormalSEA.seq_sup z hD h2
        have h4 := mk_isSup (i := i) h3
        show EIsSup ((fun y => mk i (z ⊙ proj M i y)) '' S) (mk i (z ⊙ proj M i x))
        rwa [Set.image_image, Set.image_image] at h4
    comm_sup := by
      intro a S x hS hx hc
      cases a with
      | zero => exact (seqH_zero_r M x).symm
      | one => exact (seqH_one_r M x).symm
      | mid i z h0 h1 =>
        have hside : ∀ y ∈ S, ∃ v : E i, y = mk i v := fun y hy =>
          let ⟨u, e, _⟩ := (comm_mid_iff M).mp (hc y hy); ⟨u, e⟩
        obtain ⟨hSeq, hT⟩ := side_directed hS hside
        obtain ⟨t, ht⟩ := NormalSEA.directedComplete _ hT
        have hxt : x = mk i t := hx.unique (by rw [hSeq]; exact mk_isSup ht)
        refine (comm_mid_iff M).mpr ⟨t, hxt, ?_⟩
        refine NormalSEA.comm_sup z hT ht fun u hu => ?_
        obtain ⟨u', e, hu'⟩ := (comm_mid_iff M).mp (hc _ hu)
        rw [mk_injective i e]; exact hu' }

end HSum

/-! ### `[0,1]` and direct sums as normal SEAs -/

theorem unitInterval_le_iff {x y : I} : x ≼ y ↔ x ≤ y := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    show (x : ℝ) ≤ x + d; linarith [d.2.1]
  · intro h
    have h' : (x : ℝ) ≤ y := h
    refine ⟨mkI (y - x) (by linarith) (by linarith [x.2.1, y.2.2]),
      show (x : ℝ) + (y - x) ≤ 1 by linarith [y.2.2], Subtype.ext ?_⟩
    show (x : ℝ) + (y - x) = y; ring

/-- A supremum in `[0,1]` can be approached from below. -/
theorem unitInterval_exists_gt {T : Set I} {a : I} (hT : T.Nonempty) (ha : EIsSup T a) {r : ℝ}
    (hr : r < a) : ∃ t ∈ T, r < t := by
  by_contra hcon
  push Not at hcon
  by_cases hr0 : 0 ≤ r
  · have := ha.2 (mkI r hr0 (by linarith [a.2.2])) fun t ht =>
      unitInterval_le_iff.mpr (show (t : ℝ) ≤ r from hcon t ht)
    have := unitInterval_le_iff.mp this
    exact absurd (show (a : ℝ) ≤ r from this) (not_le.mpr hr)
  · obtain ⟨t, ht⟩ := hT
    have := hcon t ht
    linarith [t.2.1]

/-- `[0,1]` as a SEA, `a ⊙ b = ab` (SEA 32 with its commutative effect monoid). -/
@[instance_reducible] noncomputable def unitSEA : SEAlgebra I :=
  commEMToSEA I (fun a b => mul_comm a b)

/-- `[0,1]` is a normal SEA. -/
noncomputable instance unitNormalSEA : NormalSEA I :=
  { unitSEA with
    directedComplete := by
      intro S hS
      have hne : (Subtype.val '' S).Nonempty := hS.1.image _
      have hbdd : BddAbove (Subtype.val '' S) := ⟨1, by rintro _ ⟨x, _, rfl⟩; exact x.2.2⟩
      obtain ⟨_, ⟨x0, hx0, rfl⟩⟩ := hne
      have hs0 : (0 : ℝ) ≤ sSup (Subtype.val '' S) := le_trans x0.2.1 (le_csSup hbdd ⟨x0, hx0, rfl⟩)
      have hs1 : sSup (Subtype.val '' S) ≤ 1 :=
        csSup_le ⟨_, ⟨x0, hx0, rfl⟩⟩ (by rintro _ ⟨x, _, rfl⟩; exact x.2.2)
      refine ⟨mkI _ hs0 hs1, fun x hx => unitInterval_le_iff.mpr ?_, fun y hy => ?_⟩
      · exact le_csSup hbdd ⟨x, hx, rfl⟩
      · have hne' : (Subtype.val '' S).Nonempty := ⟨_, ⟨x0, hx0, rfl⟩⟩
        refine unitInterval_le_iff.mpr (csSup_le hne' ?_)
        rintro _ ⟨x, hx, rfl⟩; exact unitInterval_le_iff.mp (hy x hx)
    seq_sup := by
      intro a S x hS hx
      refine ⟨?_, fun y hy => ?_⟩
      · rintro _ ⟨s, hs, rfl⟩
        refine unitInterval_le_iff.mpr ?_
        show (a : ℝ) * s ≤ a * x
        exact mul_le_mul_of_nonneg_left (unitInterval_le_iff.mp (hx.1 s hs)) a.2.1
      · refine unitInterval_le_iff.mpr ?_
        show (a : ℝ) * x ≤ y
        by_contra hlt
        push Not at hlt
        have ha : (0 : ℝ) < a := by
          by_contra h; push Not at h
          have : (a : ℝ) = 0 := le_antisymm h a.2.1
          rw [this, zero_mul] at hlt; linarith [y.2.1]
        obtain ⟨s, hs, hlt'⟩ := unitInterval_exists_gt hS.1 hx
          (show (y : ℝ) / a < x by rw [div_lt_iff₀ ha]; linarith)
        have := unitInterval_le_iff.mp (hy _ ⟨s, hs, rfl⟩)
        have h2 : (a : ℝ) * s ≤ y := this
        rw [div_lt_iff₀ ha] at hlt'
        linarith
    comm_sup := fun a _ x _ _ _ => mul_comm a x }

theorem unit_seq (a b : I) : a ⊙ b = a * b := rfl

section ProdNormal

variable {E F : Type u} [EffectAlgebra E] [EffectAlgebra F]

theorem prod_le_iff {x y : E × F} : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2 := by
  constructor
  · rintro ⟨d, hd, rfl⟩; exact ⟨⟨d.1, hd.1, rfl⟩, ⟨d.2, hd.2, rfl⟩⟩
  · rintro ⟨⟨d1, h1, e1⟩, ⟨d2, h2, e2⟩⟩; exact ⟨(d1, d2), ⟨h1, h2⟩, Prod.ext e1 e2⟩

theorem prod_isSup {S : Set (E × F)} {a : E} {b : F} (ha : EIsSup (Prod.fst '' S) a)
    (hb : EIsSup (Prod.snd '' S) b) : EIsSup S (a, b) := by
  refine ⟨fun x hx => prod_le_iff.mpr ⟨ha.1 _ ⟨x, hx, rfl⟩, hb.1 _ ⟨x, hx, rfl⟩⟩, fun y hy => ?_⟩
  refine prod_le_iff.mpr ⟨ha.2 _ ?_, hb.2 _ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact (prod_le_iff.mp (hy x hx)).1
  · rintro _ ⟨x, hx, rfl⟩; exact (prod_le_iff.mp (hy x hx)).2

theorem prod_directed {S : Set (E × F)} (hS : EDirected S) :
    EDirected (Prod.fst '' S) ∧ EDirected (Prod.snd '' S) :=
  ⟨eDirected_image hS fun _ _ h => (prod_le_iff.mp h).1,
    eDirected_image hS fun _ _ h => (prod_le_iff.mp h).2⟩

/-- The direct sum of two normal SEAs is a normal SEA. -/
@[instance_reducible] noncomputable def prodNormalSEA (E F : Type u) [EffectAlgebra E]
    [EffectAlgebra F] [NormalSEA E] [NormalSEA F] : NormalSEA (E × F) :=
  { prodSEA E F with
    directedComplete := by
      intro S hS
      obtain ⟨a, ha⟩ := NormalSEA.directedComplete _ (prod_directed hS).1
      obtain ⟨b, hb⟩ := NormalSEA.directedComplete _ (prod_directed hS).2
      exact ⟨(a, b), prod_isSup ha hb⟩
    seq_sup := by
      intro c S x hS hx
      obtain ⟨a, ha⟩ := NormalSEA.directedComplete _ (prod_directed hS).1
      obtain ⟨b, hb⟩ := NormalSEA.directedComplete _ (prod_directed hS).2
      have hx' : x = (a, b) := hx.unique (prod_isSup ha hb)
      subst hx'
      refine prod_isSup ?_ ?_
      · have := NormalSEA.seq_sup c.1 (prod_directed hS).1 ha
        rwa [Set.image_image] at this ⊢
      · have := NormalSEA.seq_sup c.2 (prod_directed hS).2 hb
        rwa [Set.image_image] at this ⊢
    comm_sup := by
      intro c S x hS hx hc
      obtain ⟨a, ha⟩ := NormalSEA.directedComplete _ (prod_directed hS).1
      obtain ⟨b, hb⟩ := NormalSEA.directedComplete _ (prod_directed hS).2
      have hx' : x = (a, b) := hx.unique (prod_isSup ha hb)
      subst hx'
      refine Prod.ext ?_ ?_
      · refine NormalSEA.comm_sup c.1 (prod_directed hS).1 ha ?_
        rintro _ ⟨s, hs, rfl⟩; exact congrArg Prod.fst (hc s hs)
      · refine NormalSEA.comm_sup c.2 (prod_directed hS).2 hb ?_
        rintro _ ⟨s, hs, rfl⟩; exact congrArg Prod.snd (hc s hs) }

end ProdNormal


theorem HSum.proj_isSumOf {ι : Type v} {E : ι → Type u} [∀ i, EffectAlgebra (E i)]
    [∀ i, SEAlgebra (E i)] (M : HSMaps E) (i : ι) {l : List (HSum E)} {s : HSum E}
    (h : PCM.IsSumOf l s) : PCM.IsSumOf (l.map (HSum.proj M i)) (HSum.proj M i s) := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | @cons a l s _ h ih =>
    obtain ⟨h', e⟩ := HSum.proj_add M i h
    rw [← e]; exact PCM.IsSumOf.cons ih h'

/-- In `[0,1]`, a sum of a list is the sum of its values. -/
theorem unit_isSumOf_sum {l : List I} {s : I} (h : PCM.IsSumOf l s) :
    (l.map Subtype.val).sum = s.1 := by
  induction h with
  | nil => rfl
  | @cons a l s _ h ih =>
    show a.1 + (l.map Subtype.val).sum = a.1 + s.1
    rw [ih]

theorem unit_one_ne_zero : (1 : I) ≠ 0 := fun h => by
  have := congrArg Subtype.val h; norm_num at this

/-! ## Example 48: `H = HS([0,1], [0,1])` -/

/-- The two copies of `[0,1]` in `H`: left and right. -/
inductive Side
  | L
  | R
  deriving DecidableEq

/-- **SEA 48** (`ex:horizontal-interval`, second.tex:1195, Example): `H`, the
horizontal sum of the unit interval with itself; `λ_A` is `HSum.mk A λ`. -/
abbrev HH : Type := HSum (fun _ : Side => I)

/-- The horizontal sum of copies of `[0,1]` indexed by `ι`, with the product
`λ_α ⊙ μ_β = (λμ)_α` (all `F` are identities).  SEA 48 is `ι = Side`; SEA 73
uses general `ι`. -/
noncomputable def unitMaps (ι : Type v) : HSMaps (fun _ : ι => I) where
  F _ _ := id
  F_self _ _ := rfl
  F_one _ _ := rfl
  F_add _ _ _ _ h := ⟨h, rfl⟩
  F_ne_zero := by
    intro i j _ a b ha0 _ hb0 _ h
    have h' : ((a * b : I) : ℝ) = 0 := congrArg Subtype.val h
    rw [Set.Icc.coe_mul] at h'
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact ha0 (Subtype.ext h'')
    · exact hb0 (Subtype.ext h'')

theorem unitMaps_normal (ι : Type v) : (unitMaps ι).IsNormal := by
  intro i j S x _ hx
  show EIsSup (id '' S) x
  rwa [Set.image_id]

/-- A horizontal sum of copies of `[0,1]` is a normal SEA. -/
noncomputable instance unitHSumNormalSEA (ι : Type v) : NormalSEA (HSum (fun _ : ι => I)) :=
  HSum.hsNormalSEA (unitMaps ι) (unitMaps_normal ι)

/-- The product maps of `H`. -/
noncomputable abbrev hhMaps : HSMaps (fun _ : Side => I) := unitMaps Side

theorem hhMaps_normal : hhMaps.IsNormal := unitMaps_normal Side

/-- **SEA 48**: the product of `H` is `λ_A ⊙ μ_B = (λμ)_A` (for `λ ≠ 1`; the
print's formula with `λ = 1` must be read as `1 ⊙ x = x`, since `1_L = 1_R`). -/
theorem sea48_seq (A B : Side) {l : I} (hl : l ≠ 1) (m : I) :
    HSum.mk A l ⊙ (HSum.mk B m : HH) = HSum.mk A (l * m) := by
  show HSum.seqH hhMaps (HSum.mk A l) (HSum.mk B m) = _
  rw [HSum.seqH_mk_left hhMaps hl, HSum.proj_mk]; rfl

/-- The action of SEA 48 with `λ · 1 = λ_s`, `λ · μ_A = (λμ)_A`. -/
noncomputable def actHf (s : Side) (l : I) : HH → HH
  | .zero => .zero
  | .one => HSum.mk s l
  | .mid A t _ _ => HSum.mk A (l * t)

theorem actHf_mk (s : Side) (l : I) (A : Side) (t : I) (h : t ≠ 1 ∨ A = s) :
    actHf s l (HSum.mk A t) = HSum.mk A (l * t) := by
  rcases HSum.mk_cases (E := fun _ : Side => I) A t with ⟨ht, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;>
    rw [hm]
  · rw [ht, mul_zero, HSum.mk_zero]; rfl
  · rcases h with h | h
    · exact absurd h1 h
    · subst h; show HSum.mk (E := fun _ : Side => I) A l = _; rw [h1, mul_one]
  · rfl

theorem unit_mul_ne_one {m t : I} (ht : t ≠ 1) : m * t ≠ 1 := by
  intro h
  have h' : (m : ℝ) * t = 1 := by
    have := congrArg Subtype.val h; rwa [Set.Icc.coe_mul] at this
  have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun e => ht (Subtype.ext e))
  nlinarith [m.2.1, m.2.2, t.2.1]

/-- **SEA 48**: the two a-convex actions on `H`, `λ · 1 = λ_s` (`s = L, R`)
and `λ · μ_A = (λμ)_A`. -/
noncomputable def actH (s : Side) : AConvexAction HH where
  act := actHf s
  act_act l m x := by
    cases x with
    | zero => rfl
    | one =>
      show actHf s l (HSum.mk s m) = HSum.mk s (l * m)
      exact actHf_mk s l s m (Or.inr rfl)
    | mid A t h0 h1 =>
      show actHf s l (HSum.mk A (m * t)) = HSum.mk A (l * m * t)
      rw [actHf_mk s l A _ (Or.inl (unit_mul_ne_one h1)), mul_assoc]
  act_add l m n x h := by
    have hlm : Perp l m := show (l : ℝ) + m ≤ 1 by rw [h]; exact n.2.2
    have hn : ovee l m hlm = n := Subtype.ext h
    cases x with
    | zero => exact ⟨trivial, rfl⟩
    | one =>
      obtain ⟨h', e⟩ := HSum.mk_ovee (E := fun _ : Side => I) (i := s) hlm
      exact ⟨h', e.trans (by rw [hn]; rfl)⟩
    | mid A t h0 h1 =>
      have hp : Perp (l * t) (m * t) := by
        show ((l * t : I) : ℝ) + (m * t : I) ≤ 1
        rw [Set.Icc.coe_mul, Set.Icc.coe_mul, ← add_mul, h]
        nlinarith [n.2.1, n.2.2, t.2.1, t.2.2]
      obtain ⟨h', e⟩ := HSum.mk_ovee (E := fun _ : Side => I) (i := A) hp
      refine ⟨h', e.trans (congrArg _ (Subtype.ext ?_))⟩
      show ((l * t : I) : ℝ) + (m * t : I) = (n * t : I)
      rw [Set.Icc.coe_mul, Set.Icc.coe_mul, Set.Icc.coe_mul, ← add_mul, h]
  one_act x := by
    cases x with
    | zero => rfl
    | one => exact HSum.mk_one_of (E := fun _ : Side => I) (i := s) unit_one_ne_zero
    | mid A t h0 h1 =>
      show HSum.mk (E := fun _ : Side => I) A (1 * t) = _; rw [one_mul, HSum.mk_of_ne h0 h1]

/-- The value map `H → [0,1]`, `λ_A ↦ λ`. -/
noncomputable def hhVal : HH → I := HSum.proj hhMaps Side.L

theorem halfI_ne_zero : halfI ≠ 0 := fun h => by
  have := congrArg Subtype.val h; simp at this

theorem halfI_ne_one : halfI ≠ 1 := fun h => by
  have := congrArg Subtype.val h; norm_num at this

/-- Division by `n` of an element `t_A ∉ {0, 1}` of `H` is unique:
`n · b = t_A` forces `b = (t/n)_A`. -/
theorem hh_div_unique {n : ℕ} (hn : 0 < n) {A : Side} {t : I} {h0 : t ≠ 0} {h1 : t ≠ 1}
    {b : HH} (hb : PCM.IsSumOf (List.replicate n b) (HSum.mid A t h0 h1)) :
    ∃ u : I, (n : ℝ) * u = t ∧ b = HSum.mk A u := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hle : b ≼ HSum.mid A t h0 h1 := by
    obtain ⟨t', -, hp, e⟩ := PCM.isSumOf_cons_iff.mp hb
    rw [← e]; exact left_le_ovee hp
  have hval := unit_isSumOf_sum (HSum.proj_isSumOf hhMaps Side.L hb)
  rw [List.map_replicate, List.map_replicate, List.sum_replicate, nsmul_eq_mul] at hval
  cases b with
  | zero =>
    exfalso; apply h0; apply Subtype.ext
    have : ((HSum.proj hhMaps Side.L (HSum.mid A t h0 h1) : I) : ℝ) = t := rfl
    rw [← this, ← hval]; show ((m + 1 : ℕ) : ℝ) * 0 = 0; ring
  | one =>
    exact absurd (HSum.one_le_iff.mp hle) (fun h => nomatch h)
  | mid B u hu0 hu1 =>
    rcases HSum.mid_le_iff.mp hle with h | ⟨b', hb0', hb1', e, -⟩
    · exact nomatch h
    · obtain ⟨hAB, -⟩ := HSum.mid.inj e
      subst hAB
      exact ⟨u, hval, (HSum.mk_of_ne hu0 hu1).symm⟩

theorem hh_div_eq {n : ℕ} (hn : 0 < n) {A : Side} {t : I} {h0 : t ≠ 0} {h1 : t ≠ 1}
    {b c : HH} (hb : PCM.IsSumOf (List.replicate n b) (HSum.mid A t h0 h1))
    (hc : PCM.IsSumOf (List.replicate n c) (HSum.mid A t h0 h1)) : b = c := by
  obtain ⟨u, hu, rfl⟩ := hh_div_unique hn hb
  obtain ⟨w, hw, rfl⟩ := hh_div_unique hn hc
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : u = w := Subtype.ext (mul_left_cancel₀ hn' (hu.trans hw.symm))
  rw [this]

/-- The halves of `1` in `H` are `½_L` and `½_R`. -/
theorem hh_half_one {h : HH} (hh : IsHalf h) : ∃ s : Side, h = HSum.mk s halfI := by
  obtain ⟨hp, e⟩ := hh
  cases h with
  | zero => exact nomatch e
  | one => exact False.elim hp
  | mid s t h0 h1 =>
    obtain ⟨_, htt⟩ := hp
    have htt' : Perp t t := htt
    change HSum.mk (E := fun _ : Side => I) s (ovee t t htt') = HSum.one at e
    have e' := (HSum.mk_eq_one_iff (E := fun _ : Side => I)).mp e |>.2
    have ht : (t : ℝ) = 1 / 2 := by
      have := congrArg Subtype.val e'; change (t : ℝ) + t = 1 at this; linarith
    refine ⟨s, ?_⟩
    rw [← HSum.mk_of_ne h0 h1]
    congr 1; exact Subtype.ext ht

theorem mk_half_isHalf (s : Side) : IsHalf (HSum.mk s halfI : HH) := by
  have hp : Perp halfI halfI := show ((halfI : I) : ℝ) + halfI ≤ 1 by simp; norm_num
  obtain ⟨h', e⟩ := HSum.mk_ovee (E := fun _ : Side => I) (i := s) hp
  refine ⟨h', e.trans ?_⟩
  have : ovee halfI halfI hp = (1 : I) := Subtype.ext (by
    show ((halfI : I) : ℝ) + halfI = 1; simp; norm_num)
  rw [this]; exact HSum.mk_one_of unit_one_ne_zero

theorem mk_L_ne_mk_R {l : I} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    (HSum.mk Side.L l : HH) ≠ HSum.mk Side.R l := by
  rw [HSum.mk_of_ne h0 h1, HSum.mk_of_ne h0 h1]
  intro e; exact nomatch (HSum.mid.inj e).1

/-- **SEA 48**: every a-convex action on `H` is one of the two of `actH`
("for every other element there is a unique choice"): `½ · 1` is a half of
`1`, i.e. `½_L` or `½_R`, and `λ ↦ λ · x` is determined by its value at `½`
(SEA 52.4's argument, with division in `H` in place of SEA 51). -/
theorem sea48_actions (A : AConvexAction HH) : A = actH Side.L ∨ A = actH Side.R := by
  obtain ⟨s, hs⟩ := hh_half_one (isSumOf_two_iff.mp (A.half_sum 1))
  suffices A = actH s by cases s <;> [exact Or.inl this; exact Or.inr this]
  ext l x
  cases x with
  | zero =>
    exact (eq_zero_of_le_zero (A.act_le l HSum.zero)).trans rfl
  | one =>
    have heq : A.act halfI HSum.one = (actH s).act halfI HSum.one := hs
    have hmid : A.act halfI HSum.one = HSum.mid s halfI halfI_ne_zero halfI_ne_one :=
      hs.trans (HSum.mk_of_ne _ _)
    refine congrFun (additive_eq_of_div (A.additive _) ((actH s).additive _) halfI_pos heq
      fun n hn b c hb hc => ?_) l
    rw [hmid] at hb hc
    exact hh_div_eq hn hb hc
  | mid B t h0 h1 =>
    let t2 : I := halfI * t
    have ht20 : t2 ≠ 0 := fun h => by
      have := congrArg Subtype.val h
      rw [Set.Icc.coe_mul] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact halfI_ne_zero (Subtype.ext h')
      · exact h0 (Subtype.ext h')
    have ht21 : t2 ≠ 1 := unit_mul_ne_one h1
    have hA : A.act halfI (HSum.mid B t h0 h1) = HSum.mid B t2 ht20 ht21 := by
      obtain ⟨u, hu, e⟩ := hh_div_unique two_pos (A.half_sum _)
      rw [e, ← HSum.mk_of_ne ht20 ht21]
      congr 1
      apply Subtype.ext
      show (u : ℝ) = ((halfI * t : I) : ℝ)
      rw [Set.Icc.coe_mul, halfI_val]; push_cast at hu; linarith
    have heq : A.act halfI (HSum.mid B t h0 h1) = (actH s).act halfI (HSum.mid B t h0 h1) := by
      rw [hA, ← HSum.mk_of_ne ht20 ht21]; rfl
    refine congrFun (additive_eq_of_div (A.additive _) ((actH s).additive _) halfI_pos heq
      fun n hn b c hb hc => ?_) l
    rw [hA] at hb hc
    exact hh_div_eq hn hb hc

/-- **SEA 48** (`ex:horizontal-interval`, second.tex:1195, Example): `H` is a
directed-complete effect algebra and a normal SEA with
`λ_A ⊙ μ_B = (λμ)_A` (`sea48_seq`; the instance is `HSum.hsNormalSEA`); it has
exactly two a-convex actions, `λ · 1 = λ_L` and `λ · 1 = λ_R` (with
`λ · μ_A = (λμ)_A`); and it is not convex.  The print shows that neither action
is convex by `λ · (½_R ⋁ ½_R) = λ_L ≠ λ_R = λ · ½_R ⋁ λ · ½_R`
(`sea48_not_additive`); that no convex action exists at all follows from the
two distinct halves `½_L, ½_R` (SEA 57, 1 ⇒ 4). -/
theorem sea48_example :
    DirectedComplete HH ∧
      (∀ (A B : Side) (l m : I), l ≠ 1 → HSum.mk A l ⊙ (HSum.mk B m : HH) = HSum.mk A (l * m)) ∧
      actH Side.L ≠ actH Side.R ∧
      (∀ A : AConvexAction HH, A = actH Side.L ∨ A = actH Side.R) ∧
      (∀ (s : Side) (l : I) (A : Side) (t : I), t ≠ 1 →
        (actH s).act l (HSum.mk A t) = HSum.mk A (l * t)) ∧
      ¬ IsConvex HH := by
  refine ⟨NormalSEA.directedComplete, fun A B l m hl => sea48_seq A B hl m, fun h => ?_,
    sea48_actions, fun s l A t ht => actHf_mk s l A t (Or.inl ht), fun hc => ?_⟩
  · have := congrArg (fun B : AConvexAction HH => B.act halfI HSum.one) h
    exact mk_L_ne_mk_R halfI_ne_zero halfI_ne_one this
  · obtain ⟨h, -, hu⟩ := sea57_1_4 hc
    exact mk_L_ne_mk_R halfI_ne_zero halfI_ne_one
      ((hu _ (mk_half_isHalf Side.L)).trans (hu _ (mk_half_isHalf Side.R)).symm)

/-- **SEA 48**, the printed computation: for `λ ∈ (0,1)` and the action with
`λ · 1 = λ_L`, `λ · (½_R ⋁ ½_R) = λ_L` while `λ · ½_R ⋁ λ · ½_R = λ_R`. -/
theorem sea48_not_additive {l : I} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    ∃ (hp : Perp (HSum.mk Side.R halfI : HH) (HSum.mk Side.R halfI))
      (hp' : Perp ((actH Side.L).act l (HSum.mk Side.R halfI))
        ((actH Side.L).act l (HSum.mk Side.R halfI))),
      (actH Side.L).act l (ovee _ _ hp) = HSum.mk Side.L l ∧
      ovee _ _ hp' = HSum.mk Side.R l ∧ (HSum.mk Side.L l : HH) ≠ HSum.mk Side.R l := by
  obtain ⟨hp, e⟩ := mk_half_isHalf Side.R
  have e1 : (actH Side.L).act l (HSum.mk Side.R halfI) = HSum.mk Side.R (l * halfI) :=
    actHf_mk _ _ _ _ (Or.inl halfI_ne_one)
  have hq : Perp (l * halfI) (l * halfI) := by
    show ((l * halfI : I) : ℝ) + (l * halfI : I) ≤ 1
    rw [Set.Icc.coe_mul, halfI_val]; linarith [l.2.2]
  obtain ⟨hq', e2⟩ := HSum.mk_ovee (E := fun _ : Side => I) (i := Side.R) hq
  have hsum : ovee (l * halfI) (l * halfI) hq = l := Subtype.ext (by
    show ((l * halfI : I) : ℝ) + (l * halfI : I) = l
    rw [Set.Icc.coe_mul, halfI_val]; ring)
  refine ⟨hp, by rw [e1]; exact hq', ?_, ?_, mk_L_ne_mk_R hl0 hl1⟩
  · rw [e]; rfl
  · rw [PCM.ovee_congr e1 e1 _ hq', e2, hsum]


/-! ## Example 56: `HS(H ⊕ H, [0,1])` -/

/-- The summands of the example of SEA 56: `H ⊕ H` (index `true`) and `[0,1]`
(index `false`). -/
abbrev G56 : Bool → Type
  | true => HH × HH
  | false => I

noncomputable instance G56.ea : ∀ b, EffectAlgebra (G56 b)
  | true => inferInstanceAs (EffectAlgebra (HH × HH))
  | false => inferInstanceAs (EffectAlgebra I)

noncomputable instance G56.nsea : ∀ b, NormalSEA (G56 b)
  | true => prodNormalSEA HH HH
  | false => unitNormalSEA

theorem hhVal_le_one (x : HH) : (hhVal x : ℝ) ≤ 1 := (hhVal x).2.2

theorem hhVal_eq_zero {x : HH} (h : hhVal x = 0) : x = HSum.zero := by
  cases x with
  | zero => rfl
  | one => exact absurd h unit_one_ne_zero
  | mid A t h0 h1 => exact absurd h h0

/-- The maps of SEA 56: `μ ↦ (μ_R, μ_R)` and `(a, b) ↦ ½(|a| + |b|)`. -/
noncomputable def F56 : ∀ i j : Bool, G56 j → G56 i
  | true, true => id
  | false, false => id
  | true, false => fun μ => ((HSum.mk Side.R μ : HH), (HSum.mk Side.R μ : HH))
  | false, true => fun p => mkI (((hhVal p.1 : ℝ) + hhVal p.2) / 2)
      (by linarith [(hhVal p.1).2.1, (hhVal p.2).2.1])
      (by linarith [hhVal_le_one p.1, hhVal_le_one p.2])

theorem hhVal_add {x y : HH} (h : Perp x y) :
    ((hhVal (ovee x y h) : I) : ℝ) = hhVal x + hhVal y := by
  obtain ⟨h', e⟩ := HSum.proj_add hhMaps Side.L h
  show ((HSum.proj hhMaps Side.L (ovee x y h) : I) : ℝ) = _
  rw [← e]; rfl

/-- `x ⊙ μ_R ≠ 0` for `x ≠ 0` in `H` and `μ ∉ {0,1}`. -/
theorem hh_seq_mkR_ne_zero {x : HH} (hx : x ≠ HSum.zero) {μ : I} (h0 : μ ≠ 0) (h1 : μ ≠ 1) :
    x ⊙ HSum.mk (E := fun _ : Side => I) Side.R μ ≠ HSum.zero := by
  cases x with
  | zero => exact absurd rfl hx
  | one =>
    show HSum.mk (E := fun _ : Side => I) Side.R μ ≠ HSum.zero
    rw [HSum.mk_of_ne h0 h1]; exact fun h => nomatch h
  | mid A t ht0 ht1 =>
    rw [← HSum.mk_of_ne ht0 ht1, sea48_seq A Side.R ht1 μ]
    intro h
    have h' := (HSum.mk_eq_zero_iff (E := fun _ : Side => I)).mp h
    have h'' : ((t * μ : I) : ℝ) = 0 := congrArg Subtype.val h'
    rw [Set.Icc.coe_mul] at h''
    rcases mul_eq_zero.mp h'' with e | e
    · exact ht0 (Subtype.ext e)
    · exact h0 (Subtype.ext e)

noncomputable def maps56 : HSMaps G56 where
  F := F56
  F_self i a := by cases i <;> rfl
  F_one i j := by
    cases i <;> cases j
    · rfl
    · apply Subtype.ext
      show ((hhVal HSum.one : ℝ) + hhVal HSum.one) / 2 = 1
      show ((1 : ℝ) + 1) / 2 = 1; norm_num
    · exact Prod.ext (HSum.mk_one_of (E := fun _ : Side => I) unit_one_ne_zero)
        (HSum.mk_one_of (E := fun _ : Side => I) unit_one_ne_zero)
    · rfl
  F_add i j a b h := by
    cases i <;> cases j
    · exact ⟨h, rfl⟩
    · have h1 := hhVal_add h.1
      have h2 := hhVal_add h.2
      refine ⟨?_, Subtype.ext ?_⟩
      · show ((hhVal a.1 : ℝ) + hhVal a.2) / 2 + ((hhVal b.1 : ℝ) + hhVal b.2) / 2 ≤ 1
        have := hhVal_le_one (ovee a.1 b.1 h.1)
        have := hhVal_le_one (ovee a.2 b.2 h.2)
        linarith
      · show ((hhVal a.1 : ℝ) + hhVal a.2) / 2 + ((hhVal b.1 : ℝ) + hhVal b.2) / 2
          = ((hhVal (ovee a.1 b.1 h.1) : ℝ) + hhVal (ovee a.2 b.2 h.2)) / 2
        rw [h1, h2]; ring
    · obtain ⟨h', e⟩ := HSum.mk_ovee (E := fun _ : Side => I) (i := Side.R) h
      exact ⟨⟨h', h'⟩, Prod.ext e e⟩
    · exact ⟨h, rfl⟩
  F_ne_zero i j hij a b ha0 ha1 hb0 hb1 := by
    cases i <;> cases j
    · exact absurd rfl hij
    · -- `μ ⊙ ½(|a| + |b|) ≠ 0`
      intro h
      have hpos : (0 : ℝ) < (hhVal b.1 : ℝ) + hhVal b.2 := by
        by_contra hle
        push Not at hle
        have e1 : hhVal b.1 = 0 := Subtype.ext (show (hhVal b.1 : ℝ) = 0 by
          linarith [(hhVal b.1).2.1, (hhVal b.2).2.1])
        have e2 : hhVal b.2 = 0 := Subtype.ext (show (hhVal b.2 : ℝ) = 0 by
          linarith [(hhVal b.1).2.1, (hhVal b.2).2.1])
        exact hb0 (Prod.ext (hhVal_eq_zero e1) (hhVal_eq_zero e2))
      have h' : ((a * F56 false true b : I) : ℝ) = 0 := congrArg Subtype.val h
      rw [Set.Icc.coe_mul] at h'
      rcases mul_eq_zero.mp h' with e | e
      · exact ha0 (Subtype.ext e)
      · have : ((F56 false true b : I) : ℝ) = ((hhVal b.1 : ℝ) + hhVal b.2) / 2 := rfl
        rw [this] at e; linarith
    · -- `(a, b) ⊙ (μ_R, μ_R) ≠ 0`
      intro h
      have ha : a.1 ≠ HSum.zero ∨ a.2 ≠ HSum.zero := by
        by_contra hc; push Not at hc; exact ha0 (Prod.ext hc.1 hc.2)
      rcases ha with ha | ha
      · exact hh_seq_mkR_ne_zero ha hb0 hb1 (congrArg Prod.fst h)
      · exact hh_seq_mkR_ne_zero ha hb0 hb1 (congrArg Prod.snd h)
    · exact absurd rfl hij

/-- In `[0,1]`: the supremum of the averages of two monotone families is the
average of the suprema. -/
theorem unit_isSup_avg {X : Type u} [EffectAlgebra X] {S : Set X} (hS : EDirected S)
    {f g : X → I} (hf : ∀ a b, a ≼ b → f a ≼ f b) (hg : ∀ a b, a ≼ b → g a ≼ g b)
    {α β : I} (hα : EIsSup (f '' S) α) (hβ : EIsSup (g '' S) β)
    (h0 : ∀ s, (0 : ℝ) ≤ ((f s : ℝ) + g s) / 2) (h1 : ∀ s, ((f s : ℝ) + g s) / 2 ≤ 1)
    (h0' : (0 : ℝ) ≤ ((α : ℝ) + β) / 2) (h1' : ((α : ℝ) + β) / 2 ≤ 1) :
    EIsSup ((fun s => mkI (((f s : ℝ) + g s) / 2) (h0 s) (h1 s)) '' S)
      (mkI (((α : ℝ) + β) / 2) h0' h1') := by
  refine ⟨?_, fun y hy => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine unitInterval_le_iff.mpr ?_
    show ((f s : ℝ) + g s) / 2 ≤ ((α : ℝ) + β) / 2
    have := unitInterval_le_iff.mp (hα.1 _ ⟨s, hs, rfl⟩)
    have := unitInterval_le_iff.mp (hβ.1 _ ⟨s, hs, rfl⟩)
    have h3 : (f s : ℝ) ≤ α := by assumption
    have h4 : (g s : ℝ) ≤ β := by assumption
    linarith
  · refine unitInterval_le_iff.mpr ?_
    show ((α : ℝ) + β) / 2 ≤ y
    by_contra hlt
    push Not at hlt
    set ε := ((α : ℝ) + β) / 2 - y with hε
    obtain ⟨_, ⟨s1, hs1, rfl⟩, h1'⟩ := unitInterval_exists_gt (hS.1.image f) hα
      (show (α : ℝ) - ε < α by linarith)
    obtain ⟨_, ⟨s2, hs2, rfl⟩, h2'⟩ := unitInterval_exists_gt (hS.1.image g) hβ
      (show (β : ℝ) - ε < β by linarith)
    obtain ⟨s3, hs3, h13, h23⟩ := hS.2 s1 hs1 s2 hs2
    have e1 : (f s1 : ℝ) ≤ f s3 := unitInterval_le_iff.mp (hf _ _ h13)
    have e2 : (g s2 : ℝ) ≤ g s3 := unitInterval_le_iff.mp (hg _ _ h23)
    have e3 : ((f s3 : ℝ) + g s3) / 2 ≤ y := unitInterval_le_iff.mp (hy _ ⟨s3, hs3, rfl⟩)
    linarith

theorem maps56_normal : maps56.IsNormal := by
  intro i j S x hS hx
  cases i <;> cases j
  · show EIsSup (id '' S) x; rwa [Set.image_id]
  · -- `(a, b) ↦ ½(|a| + |b|)`
    have hS' : EDirected S := hS
    obtain ⟨a, ha⟩ := NormalSEA.directedComplete (E := HH) _ (prod_directed hS').1
    obtain ⟨b, hb⟩ := NormalSEA.directedComplete (E := HH) _ (prod_directed hS').2
    have hx' : x = (a, b) := hx.unique (prod_isSup ha hb)
    subst hx'
    have hva := HSum.proj_isSup hhMaps hhMaps_normal Side.L (prod_directed hS').1 ha
    have hvb := HSum.proj_isSup hhMaps hhMaps_normal Side.L (prod_directed hS').2 hb
    rw [Set.image_image] at hva hvb
    exact unit_isSup_avg hS' (f := fun p : HH × HH => hhVal p.1) (g := fun p => hhVal p.2)
      (fun p q h => HSum.proj_mono hhMaps Side.L (prod_le_iff.mp h).1)
      (fun p q h => HSum.proj_mono hhMaps Side.L (prod_le_iff.mp h).2) hva hvb
      (fun s => by linarith [(hhVal s.1).2.1, (hhVal s.2).2.1])
      (fun s => by linarith [hhVal_le_one s.1, hhVal_le_one s.2])
      (by linarith [(HSum.proj hhMaps Side.L a).2.1, (HSum.proj hhMaps Side.L b).2.1])
      (by linarith [(HSum.proj hhMaps Side.L a).2.2, (HSum.proj hhMaps Side.L b).2.2])
  · -- `μ ↦ (μ_R, μ_R)`
    have h1 := HSum.mk_isSup (E := fun _ : Side => I) (i := Side.R) hx
    refine prod_isSup ?_ ?_
    · show EIsSup (Prod.fst '' ((fun μ : I => ((HSum.mk Side.R μ : HH), (HSum.mk Side.R μ : HH))) '' S)) _
      rw [Set.image_image]; exact h1
    · show EIsSup (Prod.snd '' ((fun μ : I => ((HSum.mk Side.R μ : HH), (HSum.mk Side.R μ : HH))) '' S)) _
      rw [Set.image_image]; exact h1
  · show EIsSup (id '' S) x; rwa [Set.image_id]

/-- **SEA 56** (`ex-aconvex-not-determined-by-scalars`, second.tex:1531,
Example): `E = HS(H ⊕ H, [0,1])`. -/
abbrev E56 : Type := HSum G56

noncomputable instance : NormalSEA E56 := HSum.hsNormalSEA maps56 maps56_normal

/-- **SEA 56**: the sequential product of `E` as printed: `μ ⊙ μ' = μμ'`,
`μ ⊙ (a, b) = ½(μ|a| + μ|b|)`, `(a, b) ⊙ (a', b') = (a ⊙ a', b ⊙ b')` and
`(a, b) ⊙ μ = (a ⊙ μ_R, b ⊙ μ_R)` (for `μ ≠ 1`, `(a, b) ≠ (1, 1)`; `1 ⊙ x = x`). -/
theorem sea56_seq (μ μ' : I) (q q' : HH × HH) (hμ : μ ≠ 1) (hq : q ≠ 1) :
    (HSum.mk false μ : E56) ⊙ HSum.mk false μ' = HSum.mk false (μ * μ') ∧
    (HSum.mk false μ : E56) ⊙ HSum.mk true q =
      HSum.mk false (mkI (((μ : ℝ) * hhVal q.1 + μ * hhVal q.2) / 2)
        (by nlinarith [μ.2.1, (hhVal q.1).2.1, (hhVal q.2).2.1])
        (by nlinarith [μ.2.1, μ.2.2, (hhVal q.1).2.1, (hhVal q.2).2.1, hhVal_le_one q.1,
          hhVal_le_one q.2])) ∧
    (HSum.mk true q : E56) ⊙ HSum.mk true q' = HSum.mk true (q.1 ⊙ q'.1, q.2 ⊙ q'.2) ∧
    (HSum.mk true q : E56) ⊙ HSum.mk false μ =
      HSum.mk true (q.1 ⊙ (HSum.mk Side.R μ : HH), q.2 ⊙ (HSum.mk Side.R μ : HH)) := by
  refine ⟨HSum.seqH_mk_mk maps56 (i := false) μ μ', ?_,
    HSum.seqH_mk_mk maps56 (i := true) q q', ?_⟩
  · show HSum.seqH maps56 (HSum.mk false μ) (HSum.mk true q) = _
    rw [HSum.seqH_mk_left maps56 hμ, HSum.proj_mk]
    congr 1; apply Subtype.ext
    show (μ : ℝ) * (((hhVal q.1 : ℝ) + hhVal q.2) / 2) = ((μ : ℝ) * hhVal q.1 + μ * hhVal q.2) / 2
    ring
  · show HSum.seqH maps56 (HSum.mk true q) (HSum.mk false μ) = _
    rw [HSum.seqH_mk_left maps56 hq, HSum.proj_mk]; rfl

/-- `λ · (a, b) = (λ · a, λ · b)` with the action of `H` with `λ · 1 = λ_L`. -/
noncomputable def actP (l : I) (q : HH × HH) : HH × HH :=
  ((actH Side.L).act l q.1, (actH Side.L).act l q.2)

theorem actH_ne_one {x : HH} (hx : x ≠ HSum.one) (l : I) : (actH Side.L).act l x ≠ HSum.one := by
  cases x with
  | zero => exact fun h => nomatch h
  | one => exact absurd rfl hx
  | mid A t h0 h1 =>
    show HSum.mk (E := fun _ : Side => I) A (l * t) ≠ HSum.one
    intro h
    exact unit_mul_ne_one h1 ((HSum.mk_eq_one_iff (E := fun _ : Side => I)).mp h).2

theorem actP_ne_one {q : HH × HH} (hq : q ≠ 1) (l : I) : actP l q ≠ 1 := by
  intro h
  have h1 : q.1 ≠ HSum.one ∨ q.2 ≠ HSum.one := by
    by_contra hc; push Not at hc; exact hq (Prod.ext hc.1 hc.2)
  rcases h1 with h1 | h1
  · exact actH_ne_one h1 l (congrArg Prod.fst h)
  · exact actH_ne_one h1 l (congrArg Prod.snd h)

/-- The a-convex action of SEA 56: `λ · (a, b) = (λ · a, λ · b)`,
`λ · μ = λμ`, and `λ · 1 = λ` in the `[0,1]` summand. -/
noncomputable def act56f (l : I) : E56 → E56
  | .zero => .zero
  | .one => HSum.mk false l
  | .mid true p _ _ => HSum.mk true (actP l p)
  | .mid false t _ _ => HSum.mk false (l * t)

theorem act56_mk_false (l t : I) : act56f l (HSum.mk false t) = HSum.mk false (l * t) := by
  rcases HSum.mk_cases (E := G56) false t with ⟨ht, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;>
    rw [hm]
  · rw [show t = 0 from ht, mul_zero, HSum.mk_zero]; rfl
  · show HSum.mk (E := G56) false l = _; rw [show t = 1 from h1, mul_one]
  · rfl

theorem act56_mk_true (l : I) {q : HH × HH} (hq : q ≠ 1) :
    act56f l (HSum.mk true q) = HSum.mk true (actP l q) := by
  rcases HSum.mk_cases (E := G56) true q with ⟨ht, hm⟩ | ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩ <;>
    rw [hm]
  · have : actP l q = 0 := by rw [show q = 0 from ht]; rfl
    rw [this, HSum.mk_zero]; rfl
  · exact absurd h1 hq
  · rfl

/-- **SEA 56**: the a-convex action on `E`. -/
noncomputable def act56 : AConvexAction E56 where
  act := act56f
  act_act l m x := by
    cases x with
    | zero => rfl
    | one => exact act56_mk_false l m
    | mid i p h0 h1 =>
      cases i with
      | true =>
        show act56f l (HSum.mk true (actP m p)) = HSum.mk true (actP (l * m) p)
        rw [act56_mk_true l (actP_ne_one h1 m)]
        congr 1
        exact Prod.ext ((actH Side.L).act_act l m p.1) ((actH Side.L).act_act l m p.2)
      | false =>
        show act56f l (HSum.mk false (m * p)) = HSum.mk false (l * m * p)
        rw [act56_mk_false, mul_assoc]
  act_add l m n x h := by
    cases x with
    | zero => exact ⟨trivial, rfl⟩
    | one =>
      have hlm : Perp l m := show (l : ℝ) + m ≤ 1 by rw [h]; exact n.2.2
      obtain ⟨h', e⟩ := HSum.mk_ovee (E := G56) (i := false) hlm
      exact ⟨h', e.trans (congrArg _ (Subtype.ext h))⟩
    | mid i p h0 h1 =>
      cases i with
      | true =>
        obtain ⟨ha, ea⟩ := (actH Side.L).act_add l m n p.1 h
        obtain ⟨hb, eb⟩ := (actH Side.L).act_add l m n p.2 h
        have hp : Perp (actP l p) (actP m p) := ⟨ha, hb⟩
        obtain ⟨h', e⟩ := HSum.mk_ovee (E := G56) (i := true) hp
        exact ⟨h', e.trans (congrArg _ (Prod.ext ea eb))⟩
      | false =>
        have hp : Perp (l * p) (m * p) := by
          show ((l * p : I) : ℝ) + (m * p : I) ≤ 1
          rw [Set.Icc.coe_mul, Set.Icc.coe_mul, ← add_mul, h]
          have : (p : ℝ) ≤ 1 := p.2.2
          nlinarith [n.2.1, n.2.2, (p : I).2.1]
        obtain ⟨h', e⟩ := HSum.mk_ovee (E := G56) (i := false) hp
        refine ⟨h', e.trans (congrArg _ (Subtype.ext ?_))⟩
        show ((l * p : I) : ℝ) + (m * p : I) = (n * p : I)
        rw [Set.Icc.coe_mul, Set.Icc.coe_mul, Set.Icc.coe_mul, ← add_mul, h]
  one_act x := by
    cases x with
    | zero => rfl
    | one => exact HSum.mk_one_of (E := G56) (i := false) unit_one_ne_zero
    | mid i p h0 h1 =>
      cases i with
      | true =>
        show HSum.mk (E := G56) true (actP 1 p) = _
        have : actP 1 p = p := Prod.ext ((actH Side.L).one_act p.1) ((actH Side.L).one_act p.2)
        rw [this, HSum.mk_of_ne h0 h1]
      | false =>
        show HSum.mk (E := G56) false (1 * p) = _
        rw [one_mul, HSum.mk_of_ne h0 h1]

/-- **SEA 56** (`ex-aconvex-not-determined-by-scalars`, second.tex:1531,
Example): on the normal SEA `E = HS(H ⊕ H, [0,1])` (with the product of
`sea56_seq`) the a-convex action `act56` has `λ · (1, 0) = (λ_L, 0)` while
`(1, 0) ⊙ (λ · 1) = (λ_R, 0)`; for `λ ∈ (0,1)` these differ, so the action is
not of the form `λ · a = a ⊙ (λ · 1)` of SEA 55. -/
theorem sea56_example {l : I} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    act56.act l (HSum.mk true ((HSum.one, HSum.zero) : HH × HH)) =
        HSum.mk true ((HSum.mk Side.L l, HSum.zero) : HH × HH) ∧
    (HSum.mk true ((HSum.one, HSum.zero) : HH × HH) : E56) ⊙ act56.act l 1 =
        HSum.mk true ((HSum.mk Side.R l, HSum.zero) : HH × HH) ∧
    act56.act l (HSum.mk true ((HSum.one, HSum.zero) : HH × HH)) ≠
      (HSum.mk true ((HSum.one, HSum.zero) : HH × HH) : E56) ⊙ act56.act l 1 := by
  have hq : ((HSum.one, HSum.zero) : HH × HH) ≠ 1 := fun h => nomatch congrArg Prod.snd h
  have e1 : act56.act l (HSum.mk true ((HSum.one, HSum.zero) : HH × HH)) =
      HSum.mk true ((HSum.mk Side.L l, HSum.zero) : HH × HH) :=
    act56_mk_true l hq
  have e2 : (HSum.mk true ((HSum.one, HSum.zero) : HH × HH) : E56) ⊙ act56.act l 1 =
      HSum.mk true ((HSum.mk Side.R l, HSum.zero) : HH × HH) := by
    show HSum.seqH maps56 (HSum.mk true ((HSum.one, HSum.zero) : HH × HH)) (HSum.mk false l) = _
    rw [HSum.seqH_mk_left maps56 hq, HSum.proj_mk]
    exact congrArg _ (Prod.ext (one_seq _) (zero_seq _))
  refine ⟨e1, e2, ?_⟩
  rw [e1, e2]
  intro h
  have := congrArg Prod.fst (HSum.mk_injective (E := G56) true h)
  exact mk_L_ne_mk_R hl0 hl1 this

end Papers.SEA
