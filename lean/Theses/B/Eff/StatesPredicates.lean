/-
Theses/B/Eff/StatesPredicates.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
2070–3662: predicates, states and scalars of an effectus (parsec 190), the
effectus of effect modules and the representation theorem (191), the
distribution monad `𝒟_M`, abstract `M`-convex sets and their category
`AConv_M` (192–194), effect divisoids (195), and the theorem that `AConv_M`
is an effectus when `M` is an effect divisoid (196).

Design:
* The scalars `Scal C = C(1,1)` of an effectus in partial form carry an
  effect monoid structure (`λ ⊙ μ = λ ∘ μ`), and each `Pred X = C(X,1)` an
  effect module structure over it; both are instances (they are the claims
  of 190II) and both are fully proved.
* Formal `M`-convex combinations `MConvexComb M X` are functions `X → M`
  which sum to `1` over a finite support (via `PCM.IsSumOf`).  The
  functorial action `map`, and the monad multiplication `mu`, are obtained
  by choice from `sorry`-ed unique-existence lemmas (FIXME(choice)), since
  their values are partial sums.
* An abstract `M`-convex set is a *structure* `MConvex M X` (the pair
  `(X, h)` of the thesis), so that statements can quantify over convex
  structures; `AConvMCat M` is the bundled category.
* Not separately formalized: the example lists 190IV/190V and 192V.2
  (`OUS`, `OUG`, `CRng`, `CH`, `EJA`, and the non-cancellative triangle),
  the derivation-based description of the least congruence in 193IV and of
  coproduct elements in 193IX (only the resulting existence statements are
  stated), and 195V.4 (division effect monoids of Cho–Westerbaan).
-/
import Theses.B.Eff.Effectus

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Theses.B.Eff

universe u v w t

/-! ### Helper lemmas on iterated partial sums in a PCM -/

/-- A one-element list sums to its only entry. -/
theorem isSumOf_singleton {M : Type u} [PCM M] (a : M) :
    PCM.IsSumOf [a] a := by
  have h := PCM.IsSumOf.cons (PCM.IsSumOf.nil (M := M)) (PCM.perp_zero a)
  rwa [PCM.ovee_zero] at h

/-- The sum of a one-element list is its only entry. -/
theorem eq_of_isSumOf_singleton {M : Type u} [PCM M] {a s : M}
    (h : PCM.IsSumOf [a] s) : s = a := by
  cases h with
  | cons hl hp =>
      cases hl
      exact PCM.ovee_zero a hp

/-- Sums of concatenated lists: if `l₁` sums to `s₁`, `l₂` to `s₂` and
`s₁ ⊥ s₂`, then `l₁ ++ l₂` sums to `s₁ ⋁ s₂`. -/
theorem isSumOf_append {M : Type u} [PCM M] {l₁ l₂ : List M} {s₁ s₂ : M}
    (h₁ : PCM.IsSumOf l₁ s₁) (h₂ : PCM.IsSumOf l₂ s₂) :
    ∀ h : Perp s₁ s₂, PCM.IsSumOf (l₁ ++ l₂) (ovee s₁ s₂ h) := by
  induction h₁ with
  | nil =>
      intro h
      have hz : ovee (0 : M) s₂ h = s₂ := PCM.zero_ovee s₂
      rw [List.nil_append, hz]
      exact h₂
  | @cons a l s hl hp ih =>
      intro h
      have hps : Perp s s₂ := PCM.perp_of_ovee_perp hp h
      have hcons := PCM.IsSumOf.cons (ih hps) (PCM.perp_ovee_of_ovee_perp hp h)
      rw [← PCM.ovee_assoc hp h] at hcons
      exact hcons

/-- A two-element list sums to the partial sum of its entries. -/
theorem isSumOf_pair {M : Type u} [PCM M] (a b : M) (h : Perp a b) :
    PCM.IsSumOf [a, b] (ovee a b h) :=
  isSumOf_append (isSumOf_singleton a) (isSumOf_singleton b) h

/-- Transport a sum along an equality of its value. -/
theorem isSumOf_congr {M : Type u} [PCM M] {l : List M} {s t : M}
    (h : PCM.IsSumOf l s) (e : s = t) : PCM.IsSumOf l t := e ▸ h

/-- A four-element list sums to `(a ⋁ b) ⋁ (c ⋁ d)`. -/
theorem isSumOf_four {M : Type u} [PCM M] (a b c d s : M)
    (hab : Perp a b) (hcd : Perp c d)
    (h : Perp (ovee a b hab) (ovee c d hcd))
    (e : ovee (ovee a b hab) (ovee c d hcd) h = s) :
    PCM.IsSumOf [a, b, c, d] s :=
  isSumOf_congr (isSumOf_append (isSumOf_pair a b hab) (isSumOf_pair c d hcd) h) e

/-- Sums in a product effect algebra are computed componentwise. -/
theorem isSumOf_prod {M N : Type u} [EffectAlgebra M] [EffectAlgebra N]
    {l : List (M × N)} {s₁ : M} {s₂ : N}
    (h₁ : PCM.IsSumOf (l.map Prod.fst) s₁)
    (h₂ : PCM.IsSumOf (l.map Prod.snd) s₂) :
    PCM.IsSumOf l (s₁, s₂) := by
  induction l generalizing s₁ s₂ with
  | nil => cases h₁; cases h₂; exact PCM.IsSumOf.nil
  | cons a l ih =>
      rw [List.map_cons] at h₁ h₂
      cases h₁ with
      | cons hl₁ hp₁ =>
        cases h₂ with
        | cons hl₂ hp₂ => exact PCM.IsSumOf.cons (ih hl₁ hl₂) ⟨hp₁, hp₂⟩

/- (`emon_mul_ovee` — one-sided distributivity of `⊙` over `⋁` — used to be
duplicated here; it now lives in `EffectAlgebras.lean` next to
`exc_emonzero`, with the same statement.) -/

/-- Helper: `0 ≼ a` in any PCM. -/
theorem pcm_zero_le {M : Type u} [PCM M] (a : M) : (0 : M) ≼ a :=
  ⟨a, PCM.zero_perp a, PCM.zero_ovee a⟩

/-- Helper: `a ≼ 1` in any effect algebra (witness `aᵖ`). -/
theorem ea_le_one {E : Type u} [EffectAlgebra E] (a : E) : a ≼ 1 :=
  ⟨orth a, EffectAlgebra.perp_orth a, EffectAlgebra.ovee_orth a⟩

/-- Helper: an effect algebra with `1 = 0` is trivial. -/
theorem eq_zero_of_one_eq_zero {E : Type u} [EffectAlgebra E] (h : (1 : E) = 0)
    (a : E) : a = 0 := by
  obtain ⟨c, hc, hac⟩ := ea_le_one a
  rw [h] at hac
  exact (eabasics_positivity hc hac).1

/-- Helper: multiplication in an effect monoid is monotone in its right
argument (a consequence of distributivity). -/
theorem emon_mul_le_mul_left {M : Type u} [EffectMonoid M] (x : M) {c d : M}
    (h : c ≼ d) : x * c ≼ x * d := by
  obtain ⟨e, he, rfl⟩ := h
  have hd := EffectMonoid.distrib (PCM.perp_zero x) he
  rw [PCM.ovee_zero x (PCM.perp_zero x)] at hd
  -- the first entry of a sum is below the sum
  have key : ∀ s : M, PCM.IsSumOf [x * c, 0 * c, x * e, 0 * e] s → x * c ≼ s := by
    intro s hs
    cases hs with
    | cons hl hp => exact ⟨_, hp, rfl⟩
  exact key _ hd

/-- Helper: the sum of a list is uniquely determined by the list. -/
theorem isSumOf_unique {M : Type u} [PCM M] {l : List M} {s t : M}
    (hs : PCM.IsSumOf l s) (ht : PCM.IsSumOf l t) : s = t := by
  induction hs generalizing t with
  | nil => exact (PCM.isSumOf_nil_iff.mp ht).symm
  | @cons a l s hl hp ih =>
      obtain ⟨t', ht', hp', rfl⟩ := PCM.isSumOf_cons_iff.mp ht
      exact PCM.ovee_congr rfl (ih ht') hp hp'

/-- Helper: prefixing a zero does not change a sum. -/
theorem isSumOf_zero_cons {M : Type u} [PCM M] {l : List M} {s : M} :
    PCM.IsSumOf (0 :: l) s ↔ PCM.IsSumOf l s := by
  constructor
  · intro h
    obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
    rwa [PCM.zero_ovee' t hp]
  · intro h
    have h2 := PCM.IsSumOf.cons h (PCM.zero_perp s)
    rwa [PCM.zero_ovee' s (PCM.zero_perp s)] at h2

/-- Helper: a sum over a concatenation splits into the two partial sums. -/
theorem isSumOf_split {M : Type u} [PCM M] {l₁ l₂ : List M} {s : M}
    (h : PCM.IsSumOf (l₁ ++ l₂) s) :
    ∃ (s₁ s₂ : M) (_ : PCM.IsSumOf l₁ s₁) (_ : PCM.IsSumOf l₂ s₂)
      (hp : Perp s₁ s₂), ovee s₁ s₂ hp = s := by
  induction l₁ generalizing s with
  | nil =>
      exact ⟨0, s, PCM.IsSumOf.nil, h, PCM.zero_perp s, PCM.zero_ovee' s _⟩
  | cons a l ih =>
      rw [List.cons_append, PCM.isSumOf_cons_iff] at h
      obtain ⟨t, ht, hpat, rfl⟩ := h
      obtain ⟨s₁, s₂, h₁, h₂, hp, rfl⟩ := ih ht
      obtain ⟨has₁, h', he⟩ := PCM.assoc_left hp hpat
      exact ⟨ovee a s₁ has₁, s₂, PCM.IsSumOf.cons h₁ has₁, h₂, h', he⟩

/-- Helper: an element of a summable list is below its sum. -/
theorem isSumOf_le_of_mem {M : Type u} [PCM M] {l : List M} {a s : M}
    (ha : a ∈ l) (h : PCM.IsSumOf l s) : a ≼ s := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem ha
  obtain ⟨s₁, s₂, h₁, h₂, hp, rfl⟩ := isSumOf_split h
  refine pcm_preorder_trans (PCM.le_of_isSumOf_cons h₂) ?_
  exact ⟨s₁, PCM.perp_comm hp, (PCM.ovee_comm hp).symm⟩

/-- Helper: `a ≼ 0` forces `a = 0` in an effect algebra. -/
theorem eq_zero_of_le_zero {E : Type u} [EffectAlgebra E] {a : E} (h : a ≼ 0) :
    a = 0 := by
  obtain ⟨c, hc, hac⟩ := h
  exact (eabasics_positivity hc hac).1

/-- Helper: a sublist of a summable list is itself summable, with a smaller
sum. -/
theorem isSumOf_sublist {M : Type u} [EffectAlgebra M] {l' l : List M}
    (hsub : l'.Sublist l) {s : M} (h : PCM.IsSumOf l s) :
    ∃ s', PCM.IsSumOf l' s' ∧ s' ≼ s := by
  induction hsub generalizing s with
  | slnil => exact ⟨0, PCM.IsSumOf.nil, pcm_zero_le s⟩
  | cons a hsub ih =>
      obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
      obtain ⟨s', hs', hle⟩ := ih ht
      exact ⟨s', hs', pcm_preorder_trans hle ⟨a, PCM.perp_comm hp, (PCM.ovee_comm hp).symm⟩⟩
  | cons_cons a hsub ih =>
      obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
      obtain ⟨s', hs', hle⟩ := ih ht
      have hps' : Perp a s' := eabasics_perp_iff_le_orth.mpr
        (pcm_preorder_trans (eabasics_perp_iff_le_orth.mp hp)
          (eabasics_le_iff_orth_le.mp hle))
      refine ⟨ovee a s' hps', PCM.IsSumOf.cons hs' hps', ?_⟩
      obtain ⟨hs'a, hle2⟩ := eabasics_le_perp_compat hle (PCM.perp_comm hp)
      rw [PCM.ovee_comm hps', PCM.ovee_comm hp]
      exact hle2

/-- Helper: terms of a sum whose value is `0` may be dropped. -/
theorem isSumOf_map_filter {X : Type v} {M : Type u} [PCM M] (p : X → M)
    (q : X → Bool) :
    ∀ {l : List X}, (∀ x ∈ l, q x = false → p x = 0) → ∀ {s : M},
      (PCM.IsSumOf ((l.filter q).map p) s ↔ PCM.IsSumOf (l.map p) s) := by
  intro l
  induction l with
  | nil => intro _ s; simp
  | cons a l ih =>
      intro hz s
      have hz' : ∀ x ∈ l, q x = false → p x = 0 :=
        fun x hx => hz x (List.mem_cons_of_mem a hx)
      rw [List.filter_cons]
      by_cases h : q a = true
      · rw [if_pos h, List.map_cons, List.map_cons]
        constructor
        · intro hs
          obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
          exact PCM.IsSumOf.cons ((ih hz').mp ht) hp
        · intro hs
          obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
          exact PCM.IsSumOf.cons ((ih hz').mpr ht) hp
      · have hpa : p a = 0 := hz a List.mem_cons_self (by simpa using h)
        rw [if_neg h, List.map_cons, hpa, isSumOf_zero_cons]
        exact ih hz'

open Classical in
/-- Helper: a sum can be computed by grouping the terms into the fibres of a
map `f`, provided the fibre sums are known. -/
theorem isSumOf_map_fiber {X : Type v} {Y : Type w} {M : Type u} [PCM M]
    (p : X → M) (f : X → Y) (s : Y → M) :
    ∀ {lY : List Y}, lY.Nodup → ∀ {L : List X}, (∀ x ∈ L, f x ∈ lY) →
      (∀ y ∈ lY, PCM.IsSumOf ((L.filter (fun x => decide (f x = y))).map p) (s y)) →
      ∀ {S : M}, PCM.IsSumOf (L.map p) S → PCM.IsSumOf (lY.map s) S := by
  intro lY
  induction lY with
  | nil =>
      intro _ L hmem _ S hS
      have hL : L = [] :=
        List.eq_nil_iff_forall_not_mem.mpr fun x hx => by simpa using hmem x hx
      subst hL
      rw [List.map_nil, PCM.isSumOf_nil_iff] at hS
      subst hS
      exact PCM.IsSumOf.nil
  | cons y lY ih =>
      intro hnd L hmem hs S hS
      have hperm : ((L.filter (fun x => decide (f x = y))) ++
          (L.filter (fun x => !decide (f x = y)))).Perm L :=
        List.filter_append_perm _ _
      have hS' : PCM.IsSumOf (((L.filter (fun x => decide (f x = y))) ++
          (L.filter (fun x => !decide (f x = y)))).map p) S :=
        PCM.isSumOf_perm (List.Perm.map p hperm).symm hS
      rw [List.map_append] at hS'
      obtain ⟨s₁, s₂, h₁, h₂, hp, hovee⟩ := isSumOf_split hS'
      have hsy : s₁ = s y := isSumOf_unique h₁ (hs y List.mem_cons_self)
      subst hsy
      have hmemB : ∀ x ∈ L.filter (fun x => !decide (f x = y)), f x ∈ lY := by
        intro x hx
        rw [List.mem_filter] at hx
        have h1 := hmem x hx.1
        have h2 : f x ≠ y := by simpa using hx.2
        exact (List.mem_cons.mp h1).resolve_left h2
      have hsB : ∀ y' ∈ lY, PCM.IsSumOf
          (((L.filter (fun x => !decide (f x = y))).filter
            (fun x => decide (f x = y'))).map p) (s y') := by
        intro y' hy'
        have hne : y' ≠ y := by
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 hy'
        have he : (L.filter (fun x => !decide (f x = y))).filter
            (fun x => decide (f x = y')) = L.filter (fun x => decide (f x = y')) := by
          rw [List.filter_filter]
          refine List.filter_congr ?_
          intro x _
          by_cases hx : f x = y'
          · simp [hx, hne]
          · simp [hx]
        rw [he]
        exact hs y' (List.mem_cons_of_mem y hy')
      have hIH := ih (List.nodup_cons.mp hnd).2 hmemB hsB h₂
      rw [List.map_cons, ← hovee]
      exact PCM.IsSumOf.cons hIH hp

/-- Helper: a list dominated termwise by a summable list is itself summable. -/
theorem isSumOf_of_forall₂_le {M : Type u} [EffectAlgebra M] {l' l : List M}
    (hle : List.Forall₂ (· ≼ ·) l' l) {s : M} (h : PCM.IsSumOf l s) :
    ∃ s', PCM.IsSumOf l' s' ∧ s' ≼ s := by
  induction hle generalizing s with
  | nil => exact ⟨0, PCM.IsSumOf.nil, pcm_zero_le s⟩
  | @cons a' a l' l hab _ ih =>
      obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp h
      obtain ⟨s'', hs'', hle''⟩ := ih ht
      have hpas : Perp a s'' := eabasics_perp_iff_le_orth.mpr
        (pcm_preorder_trans (eabasics_perp_iff_le_orth.mp hp)
          (eabasics_le_iff_orth_le.mp hle''))
      have hpa's : Perp a' s'' := eabasics_perp_iff_le_orth.mpr
        (pcm_preorder_trans hab (eabasics_perp_iff_le_orth.mp hpas))
      refine ⟨ovee a' s'' hpa's, PCM.IsSumOf.cons hs'' hpa's, ?_⟩
      obtain ⟨h1, hle1⟩ := eabasics_le_perp_compat hab hpas
      obtain ⟨h2, hle2⟩ := eabasics_le_perp_compat hle'' (PCM.perp_comm hp)
      refine pcm_preorder_trans hle1 ?_
      rw [PCM.ovee_comm hpas, PCM.ovee_comm hp]
      exact hle2

/-- Helper: a sum all of whose terms are `0` is `0`. -/
theorem isSumOf_eq_zero {M : Type u} [PCM M] {l : List M} (h : ∀ a ∈ l, a = 0)
    {s : M} (hs : PCM.IsSumOf l s) : s = 0 := by
  induction l generalizing s with
  | nil => exact PCM.isSumOf_nil_iff.mp hs
  | cons a l ih =>
      obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp hs
      have ha : a = 0 := h a List.mem_cons_self
      have ht0 : t = 0 := ih (fun b hb => h b (List.mem_cons_of_mem a hb)) ht
      subst ha; subst ht0
      exact PCM.zero_ovee' 0 hp

/-- Helper: multiplication in an effect monoid distributes over a finite
partial sum. -/
theorem isSumOf_mul_left {M : Type u} [EffectMonoid M] (x : M) {l : List M}
    {s : M} (h : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map fun a => x * a) (x * s) := by
  induction h with
  | nil => rw [List.map_nil, (exc_emonzero x).1]; exact PCM.IsSumOf.nil
  | @cons a l t hl hp ih =>
      obtain ⟨h', he⟩ := emon_mul_ovee x hp
      rw [List.map_cons, he]
      exact PCM.IsSumOf.cons ih h'

/-- Helper: multiplication in an effect monoid distributes over a partial sum
in its *left* argument (the mirror image of `emon_mul_ovee`). -/
theorem emon_ovee_mul {M : Type u} [EffectMonoid M] (x : M) {p q : M}
    (hpq : Perp p q) :
    ∃ h' : Perp (p * x) (q * x),
      ovee p q hpq * x = ovee (p * x) (q * x) h' := by
  have hd := EffectMonoid.distrib hpq (PCM.perp_zero x)
  rw [PCM.ovee_zero x (PCM.perp_zero x), (exc_emonzero p).1,
    (exc_emonzero q).1] at hd
  obtain ⟨t1, h1, hp1, e1⟩ := PCM.isSumOf_cons_iff.mp hd
  obtain ⟨t2, h2, hp2, e2⟩ := PCM.isSumOf_cons_iff.mp h1
  obtain ⟨t3, h3, hp3, e3⟩ := PCM.isSumOf_cons_iff.mp h2
  obtain ⟨t4, h4, hp4, e4⟩ := PCM.isSumOf_cons_iff.mp h3
  have ht4 : t4 = 0 := PCM.isSumOf_nil_iff.mp h4
  have ht3 : t3 = 0 := by rw [← e4, PCM.zero_ovee' t4 hp4]; exact ht4
  have ht2 : t2 = 0 := by rw [← e3, PCM.zero_ovee' t3 hp3]; exact ht3
  have ht1 : t1 = q * x := by
    rw [← e2, PCM.ovee_congr rfl ht2 hp2 (PCM.perp_zero (q * x))]
    exact PCM.ovee_zero _ _
  have hp' : Perp (p * x) (q * x) := by rw [← ht1]; exact hp1
  refine ⟨hp', ?_⟩
  rw [← e1]
  exact PCM.ovee_congr rfl ht1 hp1 hp'

/-- Helper: multiplication in an effect monoid distributes over a finite
partial sum in its left argument. -/
theorem isSumOf_mul_right {M : Type u} [EffectMonoid M] (x : M) {l : List M}
    {s : M} (h : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map fun a => a * x) (s * x) := by
  induction h with
  | nil => rw [List.map_nil, (exc_emonzero x).2]; exact PCM.IsSumOf.nil
  | @cons a l t hl hp ih =>
      obtain ⟨h', he⟩ := emon_ovee_mul x hp
      rw [List.map_cons, he]
      exact PCM.IsSumOf.cons ih h'

open Classical in
/-- Helper: a sum of a finitely supported family does not depend on the chosen
(repetition-free) list of indices containing its support. -/
theorem isSumOf_map_of_support {X : Type v} {M : Type u} [PCM M] (u : X → M)
    {l l' : List X} (hnd : l.Nodup) (hnd' : l'.Nodup)
    (hs : ∀ x, u x ≠ 0 → x ∈ l) (hs' : ∀ x, u x ≠ 0 → x ∈ l') {S : M}
    (h : PCM.IsSumOf (l.map u) S) : PCM.IsSumOf (l'.map u) S := by
  have hz : ∀ L : List X, ∀ x ∈ L, (decide (u x ≠ 0)) = false → u x = 0 := by
    intro L x _ hd; simpa using hd
  have h1 : PCM.IsSumOf ((l.filter (fun x => decide (u x ≠ 0))).map u) S :=
    (isSumOf_map_filter u _ (hz l)).mpr h
  have hperm : (l.filter (fun x => decide (u x ≠ 0))).Perm
      (l'.filter (fun x => decide (u x ≠ 0))) :=
    (List.perm_ext_iff_of_nodup (List.Nodup.filter _ hnd)
      (List.Nodup.filter _ hnd')).mpr (by
        intro x
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨fun hx => ⟨hs' x hx.2, hx.2⟩, fun hx => ⟨hs x hx.2, hx.2⟩⟩)
  exact (isSumOf_map_filter u _ (hz l')).mp
    (PCM.isSumOf_perm (List.Perm.map u hperm) h1)

open Classical in
/-- Helper: enlarging the (repetition-free) index list by indices where the
summand vanishes does not change the sum.  (Unlike `isSumOf_map_of_support`
this does not require the two lists to contain the *whole* support of `u`,
only that they agree where `u` is non-zero.) -/
theorem isSumOf_map_of_subset {X : Type v} {M : Type u} [PCM M] (u : X → M)
    {l l' : List X} (hnd : l.Nodup) (hnd' : l'.Nodup)
    (hsub : ∀ x ∈ l, x ∈ l') (hz : ∀ x ∈ l', x ∉ l → u x = 0) {S : M}
    (h : PCM.IsSumOf (l.map u) S) : PCM.IsSumOf (l'.map u) S := by
  have hz' : ∀ x ∈ l', (decide (x ∈ l)) = false → u x = 0 := by
    intro x hx hd
    exact hz x hx (by simpa using hd)
  refine (isSumOf_map_filter u (fun x => decide (x ∈ l)) hz').mp ?_
  have hperm : (l'.filter (fun x => decide (x ∈ l))).Perm l :=
    (List.perm_ext_iff_of_nodup (List.Nodup.filter _ hnd') hnd).mpr (by
      intro x
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun hx => hx.2, fun hx => ⟨hsub x hx, hx⟩⟩)
  exact PCM.isSumOf_perm (List.Perm.map u hperm.symm) h

/-- Helper: a sum of sums is the sum of the concatenation. -/
theorem isSumOf_flatMap {A : Type v} {M : Type u} [PCM M] (L : A → List M)
    (r : A → M) {la : List A} (hr : ∀ a ∈ la, PCM.IsSumOf (L a) (r a)) {S : M}
    (hS : PCM.IsSumOf (la.map r) S) : PCM.IsSumOf (la.flatMap L) S := by
  induction la generalizing S with
  | nil =>
      rw [List.map_nil, PCM.isSumOf_nil_iff] at hS
      subst hS
      exact PCM.IsSumOf.nil
  | cons a la ih =>
      rw [List.map_cons] at hS
      obtain ⟨t, ht, hp, rfl⟩ := PCM.isSumOf_cons_iff.mp hS
      rw [List.flatMap_cons]
      exact isSumOf_append (hr a List.mem_cons_self)
        (ih (fun b hb => hr b (List.mem_cons_of_mem a hb)) ht) hp

/-- Helper: the converse of `isSumOf_flatMap`. -/
theorem isSumOf_of_flatMap {A : Type v} {M : Type u} [PCM M] (L : A → List M)
    (r : A → M) {la : List A} (hr : ∀ a ∈ la, PCM.IsSumOf (L a) (r a)) {S : M}
    (hS : PCM.IsSumOf (la.flatMap L) S) : PCM.IsSumOf (la.map r) S := by
  induction la generalizing S with
  | nil =>
      rw [List.flatMap_nil, PCM.isSumOf_nil_iff] at hS
      subst hS
      exact PCM.IsSumOf.nil
  | cons a la ih =>
      rw [List.flatMap_cons] at hS
      obtain ⟨s₁, s₂, h₁, h₂, hp, rfl⟩ := isSumOf_split hS
      have e : s₁ = r a := isSumOf_unique h₁ (hr a List.mem_cons_self)
      subst e
      rw [List.map_cons]
      exact PCM.IsSumOf.cons (ih (fun b hb => hr b (List.mem_cons_of_mem a hb)) h₂) hp

/-- Helper: `flatMap` distributes over pointwise concatenation, up to a
permutation. -/
theorem flatMap_append_perm {A : Type v} {B : Type w} (l : List A)
    (f g : A → List B) :
    (l.flatMap fun a => f a ++ g a).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
      have e1 : (f a ++ g a) ++ (l.flatMap f ++ l.flatMap g)
          = f a ++ ((g a ++ l.flatMap f) ++ l.flatMap g) := by
        simp only [List.append_assoc]
      have e2 : f a ++ ((l.flatMap f ++ g a) ++ l.flatMap g)
          = (f a ++ l.flatMap f) ++ (g a ++ l.flatMap g) := by
        simp only [List.append_assoc]
      have s2 : ((f a ++ g a) ++ (l.flatMap f ++ l.flatMap g)).Perm
          ((f a ++ l.flatMap f) ++ (g a ++ l.flatMap g)) := by
        rw [e1, ← e2]
        exact List.Perm.append_left _ (List.Perm.append_right _ List.perm_append_comm)
      exact (List.Perm.append_left _ ih).trans s2

/-- Helper: `flatMap` of singletons is `map`. -/
theorem flatMap_singleton_map {B : Type w} {C : Type v} (lb : List B) (c : B → C) :
    (lb.flatMap fun b => [c b]) = lb.map c := by
  induction lb with
  | nil => rfl
  | cons b lb ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

/-- Helper (Fubini): the two ways of enumerating a finite "matrix" of terms
give permutations of one another. -/
theorem flatMap_map_comm {A : Type v} {B : Type w} {C : Type t} (la : List A)
    (lb : List B) (F : A → B → C) :
    (la.flatMap fun a => lb.map (F a)).Perm
      (lb.flatMap fun b => la.map fun a => F a b) := by
  induction la with
  | nil => simp
  | cons a la ih =>
      have h1 := flatMap_append_perm lb (fun b => [F a b])
        (fun b => la.map fun a' => F a' b)
      rw [flatMap_singleton_map] at h1
      refine List.Perm.trans ?_ h1.symm
      rw [List.flatMap_cons]
      exact List.Perm.append_left _ ih

/-! ## Predicates, states and scalars (parsec 190) -/

section Internal

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **190II.1** (`dfn-mandso`, eff.tex:2075, Definition): a **predicate** on
an object `X` of an effectus in partial form is a map `X ⟶ 1` (here: to the
effect object `I`); the set `Pred X` of predicates is an effect algebra
(instance `predEffectAlgebra`). -/
abbrev Pred (X : C) : Type v := X ⟶ effObj C

/-- **190II.2** (`dfn-mandso`, eff.tex:2085, Definition): a **scalar** of an
effectus in partial form is a predicate on `1`, i.e. a map `1 ⟶ 1`.  The set
of scalars is written `Scal C ≡ M ≡ Pred 1`. -/
abbrev Scal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Type v :=
  effObj C ⟶ effObj C

/-- Helper (`one-m-is-id`, 181XIII, eff.tex:1181): the truth predicate on the
effect object `I` is the identity.  (Proof of the thesis: `1 = id ⋁ idᵖ` in
the effect algebra `C(I,I)`, so `1 ∘ 1 = 1 ⋁ (1 ∘ idᵖ)`; by the zero–one
axiom `1 ∘ idᵖ = 0`, whence `idᵖ = 0` and `id = 1`.) -/
theorem truth_effObj_eq_id : truth (effObj C) = 𝟙 (effObj C) := by
  set e : effObj C ⟶ effObj C := orth (𝟙 (effObj C)) with he
  have hperp : Perp (𝟙 (effObj C)) e := EffectAlgebra.perp_orth _
  have hovee : ovee (𝟙 (effObj C)) e hperp = truth (effObj C) :=
    EffectAlgebra.ovee_orth _
  obtain ⟨h', -⟩ := FinPAC.comp_ovee hperp (truth (effObj C))
  rw [Category.id_comp] at h'
  have hz : e ≫ truth (effObj C) = 0 :=
    EffectAlgebra.eq_zero_of_perp_one (PCM.perp_comm h')
  have he0 : e = 0 := EffectusPartialForm.eq_zero_of_one_zero hz
  have h2 := eabasics_orth_orth (𝟙 (effObj C))
  rw [← he, he0, eabasics_orth_zero] at h2
  exact h2

/-- **190II.2** (`dfn-mandso`, eff.tex:2090, Definition): the scalars `Scal C`
form an effect monoid with multiplication `λ ⊙ μ = λ ∘ μ` (composition; note
`1_M = id` by 181XIII). -/
noncomputable instance scalEffectMonoid : EffectMonoid (Scal C) :=
  { predEffectAlgebra (effObj C) with
    mul := fun l m => m ≫ l
    one_mul := fun a => by
      show a ≫ truth (effObj C) = a
      rw [truth_effObj_eq_id, Category.comp_id]
    mul_one := fun a => by
      show truth (effObj C) ≫ a = a
      rw [truth_effObj_eq_id, Category.id_comp]
    mul_assoc := fun a b c => (Category.assoc c b a).symm
    distrib := by
      intro a b c d hab hcd
      obtain ⟨h1, e1⟩ := FinPAC.comp_ovee hcd (ovee a b hab)
      obtain ⟨h2, e2⟩ := FinPAC.ovee_comp hab c
      obtain ⟨h3, e3⟩ := FinPAC.ovee_comp hab d
      have hp : Perp (ovee (c ≫ a) (c ≫ b) h2) (ovee (d ≫ a) (d ≫ b) h3) := by
        rw [← e2, ← e3]; exact h1
      have key : ovee c d hcd ≫ ovee a b hab
          = ovee (ovee (c ≫ a) (c ≫ b) h2) (ovee (d ≫ a) (d ≫ b) h3) hp :=
        e1.trans (PCM.ovee_congr e2 e3 h1 hp)
      show PCM.IsSumOf [c ≫ a, c ≫ b, d ≫ a, d ≫ b] (ovee c d hcd ≫ ovee a b hab)
      rw [key]
      exact isSumOf_append (isSumOf_pair _ _ h2) (isSumOf_pair _ _ h3) hp }

/-- **190II.3** (`dfn-mandso`, eff.tex:2097, Definition): a **real effectus**
is an effectus whose effect monoid of scalars is isomorphic to `[0,1]`. -/
def IsRealEffectus (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∃ φ : EffectMonoidHom (Scal C) I, Function.Bijective φ.toFun

/-- **190II.4** (`dfn-mandso`, eff.tex:2101, Definition): scalar
multiplication `λ · p = λ ∘ p` turns each `Pred X` into an effect module
over the scalars `Scal C`. -/
noncomputable instance predEffectModule (X : C) :
    EffectModule (Scal C) (Pred X) where
  smul l p := p ≫ l
  mul_smul l m a := (Category.assoc a m l).symm
  smul_perp := by
    intro l a b h
    exact Exists.imp (fun _ hh => hh.symm) (FinPAC.comp_ovee h l)
  perp_smul := by
    intro l m h a
    exact Exists.imp (fun _ hh => hh.symm) (FinPAC.ovee_comp h a)
  one_smul a := by
    show a ≫ truth (effObj C) = a
    rw [truth_effObj_eq_id, Category.comp_id]

/-- **190II.5** (`dfn-mandso`, eff.tex:2108, Definition): the substitution
map `Pred f : Pred Y → Pred X` of `f : X ⟶ Y`, given by
`Pred(f)(p) = p ∘ f`. -/
def predMap {X Y : C} (f : X ⟶ Y) : Pred Y → Pred X := fun p => f ≫ p

/-- **190II.5** (`dfn-mandso`, eff.tex:2112, Definition): for total `f` the
map `Pred f` is an effect module homomorphism, and `Pred` is in fact a
functor `Tot C → EMod_M^op` (the substitution functor). -/
theorem predMap_functor :
    ∃ F : Tot C ⥤ (EModCat.{v, v} (Scal C))ᵒᵖ,
      ∀ X : Tot C, (F.obj X).unop.carrier = Pred X.base := by
  -- effect module homomorphisms are determined by their underlying function
  have emext : ∀ {E F : Type v} [EffectAlgebra E] [EffectAlgebra F]
      [EffectModule (Scal C) E] [EffectModule (Scal C) F]
      (f g : EffectModuleHom (Scal C) E F), f.toFun = g.toFun → f = g := by
    intro E F _ _ _ _ f g
    obtain ⟨⟨⟨f₁, -, -⟩, -⟩, -⟩ := f
    obtain ⟨⟨⟨g₁, -, -⟩, -⟩, -⟩ := g
    intro h
    dsimp only at h
    subst h
    rfl
  -- `Pred f = (– ∘ f)` is an effect module map for total `f`: it preserves
  -- `1` (totality), partial sums (`FinPAC.ovee_comp`) and scalars
  -- (associativity)
  refine ⟨{ obj := fun X => Opposite.op (EModCat.of (Scal C) (Pred X.base))
            map := fun {X Y} f => Quiver.Hom.op
              ({ toFun := fun p => f.1 ≫ p
                 perp_map := fun {a b} h => (FinPAC.ovee_comp h f.1).choose
                 ovee_map := fun {a b} h => (FinPAC.ovee_comp h f.1).choose_spec
                 map_one := f.2
                 map_smul := fun l p => (Category.assoc f.1 p l).symm } :
                EffectModuleHom (Scal C) (Pred Y.base) (Pred X.base))
            map_id := fun X => congrArg Quiver.Hom.op
              (emext _ _ (funext fun p => Category.id_comp p))
            map_comp := fun {X Y Z} f g => congrArg Quiver.Hom.op
              (emext _ _ (funext fun p => Category.assoc f.1 g.1 p)) },
    fun X => rfl⟩

/-- **190II.6** (`dfn-mandso`, eff.tex:2118, Definition): a **substate** of
`X` is a map `ω : 1 ⟶ X`. -/
abbrev Substate (X : C) : Type v := effObj C ⟶ X

/-- **190II.6** (`dfn-mandso`, eff.tex:2119, Definition): a **state** is a
total substate; `Stat X` denotes the set of states of `X`. -/
def Stat (X : C) : Type v := { ω : effObj C ⟶ X // IsTotal ω }

/-- **190II.7** (`dfn-mandso`, eff.tex:2125, Definition): an effectus has
**separating predicates** if for every `X` the predicates on `X` are jointly
monic. -/
def SeparatingPredicates (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∀ ⦃Y X : C⦄ (f g : Y ⟶ X), (∀ p : Pred X, f ≫ p = g ≫ p) → f = g

/-- **190II.7** (`dfn-mandso`, eff.tex:2129, Definition): an effectus has
**separating states** if for every `X` the states of `X` are jointly
epic. -/
def SeparatingStates (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ ω : Stat X, ω.1 ≫ f = ω.1 ≫ g) → f = g

end Internal

/-- **190III** (eff.tex:2136, Examples): the effectus `vNᵒᵖ` (in partial
form: `(W*_ncpsu)ᵒᵖ`, cf. `effectus_vn_partial`) is a real effectus with
separating states and predicates.  (Its predicates on `𝒜` correspond to the
effects `[0,1]_𝒜` and its states to the normal states.) -/
theorem effectus_vn_real_separating
    (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    IsRealEffectus WStarCPSU.{u}ᵒᵖ ∧ SeparatingPredicates WStarCPSU.{u}ᵒᵖ ∧
      SeparatingStates WStarCPSU.{u}ᵒᵖ := sorry

/-! ## The effectus of effect modules (parsec 191) -/

/-- **191II** (`emod-effectus`, eff.tex:2206, Theorem), first half: for any
effect monoid `M` the category `EMod_M^op` is an effectus in total form
(with scalars `M` and separating predicates). -/
theorem emod_effectus (M : Type u) [EffectMonoid M] :
    Nonempty (EffectusTotalStructure (EModCat.{u, u} M)ᵒᵖ) := sorry

/-- **191II** (`emod-effectus`, eff.tex:2210, Theorem), second half
(*representation*, proved in 191VII): an effectus with separating predicates
embeds into `EMod_M^op` — the substitution functor `Pred` on the total maps
is faithful.  (Stated for an effectus in partial form with scalars
`M = Scal C`.) -/
theorem emod_effectus_representation {C : Type u} [Category.{v} C]
    [HasFiniteCoproducts C] [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C]
    [EffectusPartialForm C] (hsep : SeparatingPredicates C) :
    ∃ F : Tot C ⥤ (EModCat.{v, v} (Scal C))ᵒᵖ,
      (∀ X : Tot C, (F.obj X).unop.carrier = Pred X.base) ∧ F.Faithful :=
  sorry

/-- **191VIII** (`exc-rng-eff`, eff.tex:2337, Exercise): the category
`Rngᵒᵖ` of unital rings with unit-preserving homomorphisms, in the opposite
direction, is an effectus in total form.  (Its predicates on `R` correspond
to the idempotents of `R`; its scalars are `2`.) -/
theorem exc_rng_eff : Nonempty (EffectusTotalStructure RingCat.{u}ᵒᵖ) := sorry

/-- **191VIII.2** (`exc-rng-eff`, eff.tex:2351, Exercise): there is no
unit-preserving ring homomorphism `ℤ₂ → ℤ` (whence `Rngᵒᵖ` does not have
separating states). -/
theorem exc_rng_eff_no_hom : IsEmpty (ZMod 2 →+* ℤ) := by
  constructor
  intro f
  have h : ((1 : ZMod 2) + 1) = 0 := by decide
  have h2 := congrArg f h
  rw [map_add, map_one, map_zero] at h2
  norm_num at h2

/-! ## The distribution monad `𝒟_M` (parsec 192) -/

/-- **192II** (eff.tex:2364, Definition): a **formal `M`-convex
combination** over a set `X`, for an effect monoid `M`: a function
`p : X → M` with finite support whose values sum to `1` (the sum being the
iterated partial sum of the effect algebra `M`).  The set of all formal
`M`-convex combinations over `X` is the thesis's `𝒟_M X`, written
`λ₁|x₁⟩ ⋁ ⋯ ⋁ λₙ|xₙ⟩` for the combination supported on `x₁, …, xₙ`. -/
structure MConvexComb (M : Type u) [EffectMonoid M] (X : Type v) :
    Type (max u v) where
  toFun : X → M
  sum_one : ∃ l : List X, l.Nodup ∧ (∀ x, x ∈ l ↔ toFun x ≠ 0) ∧
    PCM.IsSumOf (l.map toFun) 1

namespace MConvexComb

variable {M : Type u} [EffectMonoid M]

instance {X : Type v} : CoeFun (MConvexComb M X) (fun _ => X → M) := ⟨toFun⟩

open Classical in
/-- The Dirac (point) distribution `1|x⟩ = η(x)` (192III.2). -/
noncomputable def eta {X : Type v} (x : X) : MConvexComb M X :=
  ⟨fun y => if y = x then 1 else 0, by
    by_cases h1 : (1 : M) = 0
    · refine ⟨[], List.nodup_nil, fun y => ?_, ?_⟩
      · have hy0 : (if y = x then (1 : M) else 0) = 0 := by
          by_cases hyx : y = x
          · rw [if_pos hyx, h1]
          · rw [if_neg hyx]
        simp [hy0]
      · rw [List.map_nil, h1]
        exact PCM.IsSumOf.nil
    · refine ⟨[x], List.nodup_singleton x, fun y => ?_, ?_⟩
      · rw [List.mem_singleton]
        refine ⟨fun hy => ?_, fun hy => ?_⟩
        · rw [if_pos hy]; exact h1
        · by_contra hyx; rw [if_neg hyx] at hy; exact hy rfl
      · have hl : (List.map (fun y => if y = x then (1 : M) else 0) [x]) = [1] := by
          simp
        rw [hl]
        exact isSumOf_singleton 1⟩

open Classical in
/-- FIXME(choice): the pushforward `𝒟_M f` of a formal convex combination
along `f : X → Y` — `(𝒟_M f)(p)(y) = ⋁_{x : f(x) = y} p(x)` (192III.1) —
exists (the partial sums exist because subsums of `1` exist); stated as an
existence lemma from which `map` is obtained by choice. -/
theorem exists_map {X : Type v} {Y : Type w} (p : MConvexComb M X)
    (f : X → Y) :
    ∃ q : MConvexComb M Y, ∀ (y : Y) (l : List X), l.Nodup →
      (∀ x, x ∈ l ↔ (p.toFun x ≠ 0 ∧ f x = y)) →
      PCM.IsSumOf (l.map p.toFun) (q.toFun y) := by
  obtain ⟨l₀, hnd₀, hmem₀, hsum₀⟩ := p.sum_one
  -- each fibre of `f` over `y` has a sum, being a sublist of a summable list
  have hfib : ∀ y : Y, ∃ s : M,
      PCM.IsSumOf ((l₀.filter (fun x => decide (f x = y))).map p.toFun) s := by
    intro y
    obtain ⟨s, hs, -⟩ :=
      isSumOf_sublist (List.Sublist.map p.toFun List.filter_sublist) hsum₀
    exact ⟨s, hs⟩
  choose g hg using hfib
  have hmemfib : ∀ (y : Y) (x : X),
      x ∈ l₀.filter (fun x => decide (f x = y)) ↔ (p.toFun x ≠ 0 ∧ f x = y) := by
    intro y x
    rw [List.mem_filter, hmem₀ x]
    simp
  -- the specification holds for every list with the right members
  have hspec : ∀ (y : Y) (l : List X), l.Nodup →
      (∀ x, x ∈ l ↔ (p.toFun x ≠ 0 ∧ f x = y)) →
      PCM.IsSumOf (l.map p.toFun) (g y) := by
    intro y l hnd hm
    have hperm : (l₀.filter (fun x => decide (f x = y))).Perm l :=
      (List.perm_ext_iff_of_nodup (List.Nodup.filter _ hnd₀) hnd).mpr
        fun x => by rw [hmemfib y x, hm x]
    exact PCM.isSumOf_perm (List.Perm.map p.toFun hperm) (hg y)
  -- a `y` with a non-zero fibre sum lies in the image of the support of `p`
  have hzero : ∀ y : Y, g y ≠ 0 → y ∈ l₀.map f := by
    intro y hy
    by_contra hmem
    refine hy ?_
    have hnil : l₀.filter (fun x => decide (f x = y)) = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
      rw [List.mem_filter] at hx
      exact hmem (List.mem_map.mpr ⟨x, hx.1, by simpa using hx.2⟩)
    have h := hg y
    rw [hnil, List.map_nil, PCM.isSumOf_nil_iff] at h
    exact h
  refine ⟨⟨g, ⟨((l₀.map f).dedup).filter (fun y => decide (g y ≠ 0)), ?_, ?_, ?_⟩⟩, hspec⟩
  · exact List.Nodup.filter _ (List.nodup_dedup _)
  · intro y
    rw [List.mem_filter]
    exact ⟨fun h => by simpa using h.2,
      fun h => ⟨List.mem_dedup.mpr (hzero y h), by simpa using h⟩⟩
  · refine (isSumOf_map_filter g (fun y => decide (g y ≠ 0)) ?_).mpr ?_
    · intro y _ h
      simpa using h
    · refine isSumOf_map_fiber p.toFun f g (List.nodup_dedup _) ?_ ?_ hsum₀
      · intro x hx
        exact List.mem_dedup.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      · intro y _
        exact hg y

/-- **192III.1** (`exc-dm-effectus`, eff.tex:2386): the functorial action
`𝒟_M f` of `𝒟_M` on `f : X → Y`. -/
noncomputable def map {X : Type v} {Y : Type w} (p : MConvexComb M X)
    (f : X → Y) : MConvexComb M Y :=
  (exists_map p f).choose

/-- Two formal convex combinations with the same values are equal. -/
theorem ext {X : Type v} {p q : MConvexComb M X} (h : p.toFun = q.toFun) :
    p = q := by
  cases p; cases q; cases h; rfl

/-- The pushforward along the identity is the identity (read off from the
specification of `map`). -/
theorem map_id {X : Type v} (p : MConvexComb M X) :
    p.map _root_.id = p := by
  have hspec := (exists_map p (_root_.id : X → X)).choose_spec
  refine MConvexComb.ext ?_
  funext y
  by_cases hy : p.toFun y = 0
  · have h := hspec y [] List.nodup_nil (by
      intro x
      constructor
      · intro hx; simp at hx
      · rintro ⟨hx0, rfl⟩; exact absurd hy hx0)
    rw [List.map_nil] at h
    show (exists_map p _root_.id).choose.toFun y = p.toFun y
    rw [PCM.isSumOf_nil_iff.mp h, hy]
  · have h := hspec y [y] (List.nodup_singleton y) (by
      intro x
      constructor
      · intro hx
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hy, rfl⟩
      · intro hx
        exact List.mem_singleton.mpr hx.2)
    rw [List.map_cons, List.map_nil] at h
    show (exists_map p _root_.id).choose.toFun y = p.toFun y
    exact eq_of_isSumOf_singleton h

/-- The specification of `map`, in the form in which it is used. -/
theorem map_spec {X : Type v} {Y : Type w} (p : MConvexComb M X) (f : X → Y)
    (y : Y) (l : List X) (hnd : l.Nodup)
    (hm : ∀ x, x ∈ l ↔ (p.toFun x ≠ 0 ∧ f x = y)) :
    PCM.IsSumOf (l.map p.toFun) ((p.map f).toFun y) :=
  (exists_map p f).choose_spec y l hnd hm

open Classical in
/-- **192III.1**: functoriality of `𝒟_M`: pushing forward along `f` and then
along `g` is pushing forward along `g ∘ f`. -/
theorem map_comp {X : Type v} {Y : Type w} {Z : Type t} (p : MConvexComb M X)
    (f : X → Y) (g : Y → Z) : (p.map f).map g = p.map (g ∘ f) := by
  refine MConvexComb.ext (funext fun z => ?_)
  obtain ⟨l₀, hnd₀, hmem₀, hsum₀⟩ := p.sum_one
  obtain ⟨lY₁, hndY₁, hmemY₁, -⟩ := (p.map f).sum_one
  have hmemL : ∀ x, x ∈ l₀.filter (fun x => decide (g (f x) = z)) ↔
      (p.toFun x ≠ 0 ∧ (g ∘ f) x = z) := by
    intro x
    rw [List.mem_filter, hmem₀ x]
    simp [Function.comp_apply]
  have hLsum : PCM.IsSumOf ((l₀.filter (fun x => decide (g (f x) = z))).map p.toFun)
      ((p.map (g ∘ f)).toFun z) :=
    map_spec p (g ∘ f) z _ (List.Nodup.filter _ hnd₀) hmemL
  have hmemlY : ∀ y, y ∈ lY₁.filter (fun y => decide (g y = z)) ↔
      ((p.map f).toFun y ≠ 0 ∧ g y = z) := by
    intro y
    rw [List.mem_filter, hmemY₁ y]
    simp
  have hfibmem : ∀ (y : Y) (x : X),
      x ∈ l₀.filter (fun x => decide (f x = y)) ↔ (p.toFun x ≠ 0 ∧ f x = y) := by
    intro y x
    rw [List.mem_filter, hmem₀ x]
    simp
  -- over each `y` with `g y = z`, the fibre of `f` inside `L` is the whole fibre
  have hfib : ∀ y ∈ lY₁.filter (fun y => decide (g y = z)),
      PCM.IsSumOf (((l₀.filter (fun x => decide (g (f x) = z))).filter
        (fun x => decide (f x = y))).map p.toFun) ((p.map f).toFun y) := by
    intro y hy
    have hgy : g y = z := ((hmemlY y).mp hy).2
    have he : (l₀.filter (fun x => decide (g (f x) = z))).filter
        (fun x => decide (f x = y)) = l₀.filter (fun x => decide (f x = y)) := by
      rw [List.filter_filter]
      refine List.filter_congr ?_
      intro x _
      by_cases hx : f x = y
      · simp [hx, hgy]
      · simp [hx]
    rw [he]
    exact map_spec p f y _ (List.Nodup.filter _ hnd₀) (hfibmem y)
  -- and `f x` is then one of those `y`, as `p x ≠ 0` forces `(𝒟_M f)(p)(f x) ≠ 0`
  have hmapmem : ∀ x ∈ l₀.filter (fun x => decide (g (f x) = z)),
      f x ∈ lY₁.filter (fun y => decide (g y = z)) := by
    intro x hx
    have hx' := (hmemL x).mp hx
    have hsp : PCM.IsSumOf ((l₀.filter (fun x' => decide (f x' = f x))).map p.toFun)
        ((p.map f).toFun (f x)) :=
      map_spec p f (f x) _ (List.Nodup.filter _ hnd₀) (hfibmem (f x))
    refine (hmemlY (f x)).mpr ⟨?_, hx'.2⟩
    intro hz0
    refine hx'.1 (eq_zero_of_le_zero ?_)
    have hxmem : x ∈ l₀.filter (fun x' => decide (f x' = f x)) :=
      (hfibmem (f x) x).mpr ⟨hx'.1, rfl⟩
    have hle := isSumOf_le_of_mem (List.mem_map.mpr ⟨x, hxmem, rfl⟩) hsp
    rwa [hz0] at hle
  have hkey := isSumOf_map_fiber p.toFun f (p.map f).toFun
    (List.Nodup.filter _ hndY₁) hmapmem hfib hLsum
  exact isSumOf_unique
    (map_spec (p.map f) g z _ (List.Nodup.filter _ hndY₁) hmemlY) hkey

open Classical in
/-- FIXME(choice): the monad multiplication
`μ(Φ)(x) = ⋁_φ Φ(φ) ⊙ φ(x)` (192III.2) exists; stated as an existence
lemma from which `mu` is obtained by choice. -/
theorem exists_mu {X : Type v} (Φ : MConvexComb M (MConvexComb M X)) :
    ∃ q : MConvexComb M X, ∀ (x : X) (l : List (MConvexComb M X)),
      l.Nodup → (∀ φ, φ ∈ l ↔ Φ.toFun φ ≠ 0) →
      PCM.IsSumOf (l.map fun φ => Φ.toFun φ * φ.toFun x) (q.toFun x) := by
  obtain ⟨lΦ, hndΦ, hmemΦ, hsumΦ⟩ := Φ.sum_one
  choose supp hsuppnd hsuppmem hsuppsum using
    (fun φ : MConvexComb M X => φ.sum_one)
  -- the pointwise sums exist, being dominated by the summable list `lΦ.map Φ`
  have hdom : ∀ (x : X) (L : List (MConvexComb M X)), List.Forall₂ (· ≼ ·)
      (L.map fun φ => Φ.toFun φ * φ.toFun x) (L.map Φ.toFun) := by
    intro x L
    induction L with
    | nil => exact List.Forall₂.nil
    | cons φ L ih => exact List.Forall₂.cons (emon_mul_le_self _ _) ih
  have hex : ∀ x : X, ∃ s : M,
      PCM.IsSumOf (lΦ.map fun φ => Φ.toFun φ * φ.toFun x) s := by
    intro x
    obtain ⟨s, hs, -⟩ := isSumOf_of_forall₂_le (hdom x lΦ) hsumΦ
    exact ⟨s, hs⟩
  choose q hq using hex
  -- the specification, for any repetition-free enumeration of the support
  have hspec : ∀ (x : X) (l : List (MConvexComb M X)), l.Nodup →
      (∀ φ, φ ∈ l ↔ Φ.toFun φ ≠ 0) →
      PCM.IsSumOf (l.map fun φ => Φ.toFun φ * φ.toFun x) (q x) := by
    intro x l hnd hm
    have hperm : lΦ.Perm l :=
      (List.perm_ext_iff_of_nodup hndΦ hnd).mpr fun φ => by rw [hmemΦ φ, hm φ]
    exact PCM.isSumOf_perm (List.Perm.map _ hperm) (hq x)
  -- a repetition-free list of indices containing the support of `q`
  have hmemX : ∀ (φ : MConvexComb M X) (x : X), φ ∈ lΦ → φ.toFun x ≠ 0 →
      x ∈ (lΦ.flatMap supp).dedup := by
    intro φ x hφ hx
    exact List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨φ, hφ, (hsuppmem φ x).mpr hx⟩)
  have hqsupp : ∀ x : X, q x ≠ 0 → x ∈ (lΦ.flatMap supp).dedup := by
    intro x hx
    by_contra hmem
    refine hx (isSumOf_eq_zero ?_ (hq x))
    intro a ha
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp ha
    have hφx : φ.toFun x = 0 := by
      by_contra h0
      exact hmem (hmemX φ x hφ h0)
    rw [hφx, (exc_emonzero (Φ.toFun φ)).1]
  -- the row sums: `⋁ₓ Φ(φ) ⊙ φ(x) = Φ(φ) ⊙ 1 = Φ(φ)`
  have hrow : ∀ φ ∈ lΦ, PCM.IsSumOf
      (((lΦ.flatMap supp).dedup).map fun x => Φ.toFun φ * φ.toFun x)
      (Φ.toFun φ) := by
    intro φ hφ
    have h1 : PCM.IsSumOf (((lΦ.flatMap supp).dedup).map φ.toFun) 1 :=
      isSumOf_map_of_support φ.toFun (hsuppnd φ) (List.nodup_dedup _)
        (fun x hx => (hsuppmem φ x).mpr hx) (fun x hx => hmemX φ x hφ hx)
        (hsuppsum φ)
    have h2 := isSumOf_mul_left (Φ.toFun φ) h1
    rw [List.map_map, EffectMonoid.mul_one] at h2
    exact h2
  -- and now Fubini: summing the matrix `Φ(φ) ⊙ φ(x)` by rows gives `1`
  have hflat : PCM.IsSumOf
      (lΦ.flatMap fun φ => ((lΦ.flatMap supp).dedup).map fun x => Φ.toFun φ * φ.toFun x)
      1 := isSumOf_flatMap _ Φ.toFun hrow hsumΦ
  have hflat2 : PCM.IsSumOf
      (((lΦ.flatMap supp).dedup).flatMap fun x => lΦ.map fun φ => Φ.toFun φ * φ.toFun x)
      1 := PCM.isSumOf_perm (flatMap_map_comm lΦ _ (fun φ x => Φ.toFun φ * φ.toFun x)) hflat
  have hsumX : PCM.IsSumOf (((lΦ.flatMap supp).dedup).map q) 1 :=
    isSumOf_of_flatMap _ q (fun x _ => hq x) hflat2
  refine ⟨⟨q, ⟨((lΦ.flatMap supp).dedup).filter (fun x => decide (q x ≠ 0)),
    ?_, ?_, ?_⟩⟩, hspec⟩
  · exact List.Nodup.filter _ (List.nodup_dedup _)
  · intro x
    rw [List.mem_filter]
    exact ⟨fun h => by simpa using h.2, fun h => ⟨hqsupp x h, by simpa using h⟩⟩
  · refine (isSumOf_map_filter q (fun x => decide (q x ≠ 0)) ?_).mpr hsumX
    intro x _ h
    simpa using h

/-- **192III.2** (`exc-dm-effectus`, eff.tex:2397): the multiplication
`μ : 𝒟_M 𝒟_M X → 𝒟_M X`. -/
noncomputable def mu {X : Type v} (Φ : MConvexComb M (MConvexComb M X)) :
    MConvexComb M X :=
  (exists_mu Φ).choose

/-- The specification of `mu`, in the form in which it is used. -/
theorem mu_spec {X : Type v} (Φ : MConvexComb M (MConvexComb M X)) (x : X)
    (l : List (MConvexComb M X)) (hnd : l.Nodup)
    (hm : ∀ φ, φ ∈ l ↔ Φ.toFun φ ≠ 0) :
    PCM.IsSumOf (l.map fun φ => Φ.toFun φ * φ.toFun x) ((mu Φ).toFun x) :=
  (exists_mu Φ).choose_spec x l hnd hm

open Classical in
/-- **192III.2**: the left unit law of the monad `𝒟_M`: `μ ∘ η = id`. -/
theorem mu_eta {X : Type v} (p : MConvexComb M X) : mu (eta p) = p := by
  refine MConvexComb.ext (funext fun x => ?_)
  by_cases h1 : (1 : M) = 0
  · rw [eq_zero_of_one_eq_zero h1 ((mu (eta p)).toFun x),
      eq_zero_of_one_eq_zero h1 (p.toFun x)]
  · have hm : ∀ φ, φ ∈ [p] ↔
        (eta p : MConvexComb M (MConvexComb M X)).toFun φ ≠ 0 := by
      intro φ
      rw [List.mem_singleton]
      show φ = p ↔ (if φ = p then (1 : M) else 0) ≠ 0
      constructor
      · rintro rfl; rw [if_pos rfl]; exact h1
      · intro h; by_contra hne; rw [if_neg hne] at h; exact h rfl
    have h := mu_spec (eta p) x [p] (List.nodup_singleton p) hm
    rw [List.map_cons, List.map_nil] at h
    have hval : (eta p : MConvexComb M (MConvexComb M X)).toFun p = 1 := by
      show (if p = p then (1 : M) else 0) = 1
      rw [if_pos rfl]
    rw [hval, EffectMonoid.one_mul] at h
    exact eq_of_isSumOf_singleton h

open Classical in
/-- **192III.2**: the associativity law of the monad `𝒟_M`:
`μ ∘ μ = μ ∘ 𝒟_M μ`. -/
theorem mu_mu {X : Type v}
    (Φ : MConvexComb M (MConvexComb M (MConvexComb M X))) :
    mu (mu Φ) = mu (Φ.map mu) := by
  refine MConvexComb.ext (funext fun x => ?_)
  obtain ⟨LΨ, hndΨ, hmemΨ, hsumΨ⟩ := Φ.sum_one
  choose supp hsuppnd hsuppmem hsuppsum using
    (fun Ψ : MConvexComb M (MConvexComb M X) => Ψ.sum_one)
  obtain ⟨Lψ, hndψ, hmemψ⟩ : ∃ L : List (MConvexComb M X), L.Nodup ∧
      ∀ Ψ ∈ LΨ, ∀ ψ, Ψ.toFun ψ ≠ 0 → ψ ∈ L :=
    ⟨(LΨ.flatMap supp).dedup, List.nodup_dedup _, fun Ψ hΨ ψ hψ =>
      List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨Ψ, hΨ, (hsuppmem Ψ ψ).mpr hψ⟩)⟩
  obtain ⟨Lχ, hndχ, hmemχ⟩ : ∃ L : List (MConvexComb M X), L.Nodup ∧
      ∀ Ψ ∈ LΨ, mu Ψ ∈ L :=
    ⟨(LΨ.map mu).dedup, List.nodup_dedup _, fun Ψ hΨ =>
      List.mem_dedup.mpr (List.mem_map.mpr ⟨Ψ, hΨ, rfl⟩)⟩
  -- the outer sum of the left-hand side, over `Lψ`
  have h1 : PCM.IsSumOf (Lψ.map fun ψ => (mu Φ).toFun ψ * ψ.toFun x)
      ((mu (mu Φ)).toFun x) := by
    obtain ⟨L1, hnd1, hmem1, -⟩ := (mu Φ).sum_one
    refine isSumOf_map_of_support _ hnd1 hndψ ?_ ?_
      (mu_spec (mu Φ) x L1 hnd1 hmem1)
    · intro ψ hψ
      refine (hmem1 ψ).mpr fun h0 => hψ ?_
      rw [h0, (exc_emonzero (ψ.toFun x)).2]
    · intro ψ hψ
      have hne : (mu Φ).toFun ψ ≠ 0 := by
        intro h0; exact hψ (by rw [h0, (exc_emonzero (ψ.toFun x)).2])
      by_contra hnot
      refine hne (isSumOf_eq_zero ?_ (mu_spec Φ ψ LΨ hndΨ hmemΨ))
      intro a ha
      obtain ⟨Ψ, hΨ, rfl⟩ := List.mem_map.mp ha
      have hz : Ψ.toFun ψ = 0 := by
        by_contra h0
        exact hnot (hmemψ Ψ hΨ ψ h0)
      rw [hz, (exc_emonzero (Φ.toFun Ψ)).1]
  -- expanding each term and flattening
  have h2 : ∀ ψ ∈ Lψ, PCM.IsSumOf
      (LΨ.map fun Ψ => (Φ.toFun Ψ * Ψ.toFun ψ) * ψ.toFun x)
      ((mu Φ).toFun ψ * ψ.toFun x) := by
    intro ψ _
    have h := isSumOf_mul_right (ψ.toFun x) (mu_spec Φ ψ LΨ hndΨ hmemΨ)
    rwa [List.map_map] at h
  have h3 : PCM.IsSumOf
      (Lψ.flatMap fun ψ => LΨ.map fun Ψ => (Φ.toFun Ψ * Ψ.toFun ψ) * ψ.toFun x)
      ((mu (mu Φ)).toFun x) := isSumOf_flatMap _ _ h2 h1
  -- Fubini
  have h4 : PCM.IsSumOf
      (LΨ.flatMap fun Ψ => Lψ.map fun ψ => (Φ.toFun Ψ * Ψ.toFun ψ) * ψ.toFun x)
      ((mu (mu Φ)).toFun x) :=
    PCM.isSumOf_perm
      (flatMap_map_comm Lψ LΨ (fun ψ Ψ => (Φ.toFun Ψ * Ψ.toFun ψ) * ψ.toFun x)) h3
  -- the rows, using associativity of `⊙`
  have h5 : ∀ Ψ ∈ LΨ, PCM.IsSumOf
      (Lψ.map fun ψ => (Φ.toFun Ψ * Ψ.toFun ψ) * ψ.toFun x)
      (Φ.toFun Ψ * (mu Ψ).toFun x) := by
    intro Ψ hΨ
    have hin : PCM.IsSumOf (Lψ.map fun ψ => Ψ.toFun ψ * ψ.toFun x)
        ((mu Ψ).toFun x) := by
      obtain ⟨L2, hnd2, hmem2, -⟩ := Ψ.sum_one
      refine isSumOf_map_of_support _ hnd2 hndψ ?_ ?_ (mu_spec Ψ x L2 hnd2 hmem2)
      · intro ψ hψ
        refine (hmem2 ψ).mpr fun h0 => hψ ?_
        rw [h0, (exc_emonzero (ψ.toFun x)).2]
      · intro ψ hψ
        refine hmemψ Ψ hΨ ψ fun h0 => hψ ?_
        rw [h0, (exc_emonzero (ψ.toFun x)).2]
    have h := isSumOf_mul_left (Φ.toFun Ψ) hin
    rw [List.map_map] at h
    have heq : (Lψ.map fun ψ => (Φ.toFun Ψ * Ψ.toFun ψ) * ψ.toFun x)
        = (Lψ.map fun ψ => Φ.toFun Ψ * (Ψ.toFun ψ * ψ.toFun x)) :=
      List.map_congr_left fun ψ _ => EffectMonoid.mul_assoc _ _ _
    rw [heq]
    exact h
  have h6 : PCM.IsSumOf (LΨ.map fun Ψ => Φ.toFun Ψ * (mu Ψ).toFun x)
      ((mu (mu Φ)).toFun x) := isSumOf_of_flatMap _ _ h5 h4
  -- grouping by the fibres of `μ`
  have hfibmem : ∀ (χ : MConvexComb M X) (Ψ : MConvexComb M (MConvexComb M X)),
      Ψ ∈ LΨ.filter (fun Ψ => decide (mu Ψ = χ)) ↔ (Φ.toFun Ψ ≠ 0 ∧ mu Ψ = χ) := by
    intro χ Ψ
    rw [List.mem_filter, hmemΨ Ψ]
    simp
  have h7 : ∀ χ ∈ Lχ, PCM.IsSumOf
      ((LΨ.filter (fun Ψ => decide (mu Ψ = χ))).map
        fun Ψ => Φ.toFun Ψ * (mu Ψ).toFun x)
      ((Φ.map mu).toFun χ * χ.toFun x) := by
    intro χ _
    have hmap : PCM.IsSumOf ((LΨ.filter (fun Ψ => decide (mu Ψ = χ))).map Φ.toFun)
        ((Φ.map mu).toFun χ) :=
      map_spec Φ mu χ _ (List.Nodup.filter _ hndΨ) (hfibmem χ)
    have h := isSumOf_mul_right (χ.toFun x) hmap
    rw [List.map_map] at h
    have heq : ((LΨ.filter (fun Ψ => decide (mu Ψ = χ))).map
        fun Ψ => Φ.toFun Ψ * (mu Ψ).toFun x)
        = ((LΨ.filter (fun Ψ => decide (mu Ψ = χ))).map
        fun Ψ => Φ.toFun Ψ * χ.toFun x) := by
      refine List.map_congr_left fun Ψ hΨ => ?_
      rw [((hfibmem χ Ψ).mp hΨ).2]
    rw [heq]
    exact h
  have h8 : PCM.IsSumOf (Lχ.map fun χ => (Φ.map mu).toFun χ * χ.toFun x)
      ((mu (mu Φ)).toFun x) :=
    isSumOf_map_fiber (fun Ψ => Φ.toFun Ψ * (mu Ψ).toFun x) mu
      (fun χ => (Φ.map mu).toFun χ * χ.toFun x) hndχ hmemχ h7 h6
  -- and the same list computes the right-hand side
  have h9 : PCM.IsSumOf (Lχ.map fun χ => (Φ.map mu).toFun χ * χ.toFun x)
      ((mu (Φ.map mu)).toFun x) := by
    obtain ⟨L3, hnd3, hmem3, -⟩ := (Φ.map mu).sum_one
    refine isSumOf_map_of_support _ hnd3 hndχ ?_ ?_
      (mu_spec (Φ.map mu) x L3 hnd3 hmem3)
    · intro χ hχ
      refine (hmem3 χ).mpr fun h0 => hχ ?_
      rw [h0, (exc_emonzero (χ.toFun x)).2]
    · intro χ hχ
      have hne : (Φ.map mu).toFun χ ≠ 0 := by
        intro h0; exact hχ (by rw [h0, (exc_emonzero (χ.toFun x)).2])
      by_contra hnot
      refine hne ?_
      have hmap : PCM.IsSumOf
          ((LΨ.filter (fun Ψ => decide (mu Ψ = χ))).map Φ.toFun)
          ((Φ.map mu).toFun χ) :=
        map_spec Φ mu χ _ (List.Nodup.filter _ hndΨ) (hfibmem χ)
      have hnil : LΨ.filter (fun Ψ => decide (mu Ψ = χ)) = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr fun Ψ hΨ => ?_
        have hΨ' := (hfibmem χ Ψ).mp hΨ
        exact hnot (hΨ'.2 ▸ hmemχ Ψ ((hmemΨ Ψ).mpr hΨ'.1))
      rw [hnil, List.map_nil, PCM.isSumOf_nil_iff] at hmap
      exact hmap
  exact isSumOf_unique h8 h9

open Classical in
/-- **192III.1** (`exc-dm-effectus`, bsols.tex:2013): naturality of `η`:
`𝒟_M f ∘ η_X = η_Y ∘ f`. -/
theorem map_eta {X : Type v} {Y : Type w} (x : X) (f : X → Y) :
    (eta x : MConvexComb M X).map f = eta (f x) := by
  refine MConvexComb.ext (funext fun z => ?_)
  have hval : ∀ x' : X, (eta x : MConvexComb M X).toFun x' =
      if x' = x then (1 : M) else 0 := fun _ => rfl
  by_cases h1 : (1 : M) = 0
  · rw [eq_zero_of_one_eq_zero h1 (((eta x : MConvexComb M X).map f).toFun z),
      eq_zero_of_one_eq_zero h1 ((eta (f x) : MConvexComb M Y).toFun z)]
  by_cases hz : z = f x
  · -- the fibre of `f` over `z = f x` meets the support of `η(x)` in `x` only
    have hm : ∀ x' : X, x' ∈ [x] ↔
        ((eta x : MConvexComb M X).toFun x' ≠ 0 ∧ f x' = z) := by
      intro x'
      rw [List.mem_singleton, hval x']
      constructor
      · rintro rfl; rw [if_pos rfl, hz]; exact ⟨h1, rfl⟩
      · rintro ⟨h0, -⟩
        by_contra hne
        rw [if_neg hne] at h0
        exact h0 rfl
    have h := map_spec (eta x : MConvexComb M X) f z [x] (List.nodup_singleton x) hm
    rw [List.map_cons, List.map_nil, hval x, if_pos rfl] at h
    show ((eta x : MConvexComb M X).map f).toFun z = _
    rw [eq_of_isSumOf_singleton h]
    show (1 : M) = if z = f x then (1 : M) else 0
    rw [if_pos hz]
  · -- and is empty when `z ≠ f x`
    have hm : ∀ x' : X, x' ∈ ([] : List X) ↔
        ((eta x : MConvexComb M X).toFun x' ≠ 0 ∧ f x' = z) := by
      intro x'
      rw [hval x']
      constructor
      · intro hx'; simp at hx'
      · rintro ⟨h0, hfx⟩
        by_cases hne : x' = x
        · subst hne; exact absurd hfx.symm hz
        · rw [if_neg hne] at h0; exact absurd rfl h0
    have h := map_spec (eta x : MConvexComb M X) f z [] List.nodup_nil hm
    rw [List.map_nil] at h
    show ((eta x : MConvexComb M X).map f).toFun z = _
    rw [PCM.isSumOf_nil_iff.mp h]
    show (0 : M) = if z = f x then (1 : M) else 0
    rw [if_neg hz]

open Classical in
/-- **192III.2** (`exc-dm-effectus`, bsols.tex:2026): naturality of `μ`:
`𝒟_M f ∘ μ_X = μ_Y ∘ 𝒟_M 𝒟_M f`.  (The author's proof: expand `μ`, exchange
the two sums, contract the inner one to `(𝒟_M f)(φ)(y)`, and regroup the
outer one along the fibres of `φ ↦ 𝒟_M f (φ)`.) -/
theorem mu_map {X : Type v} {Y : Type w}
    (Φ : MConvexComb M (MConvexComb M X)) (f : X → Y) :
    (mu Φ).map f = mu (Φ.map fun φ => φ.map f) := by
  refine MConvexComb.ext (funext fun y => ?_)
  obtain ⟨LΦ, hndΦ, hmemΦ, hsumΦ⟩ := Φ.sum_one
  choose supp hsuppnd hsuppmem hsuppsum using
    (fun φ : MConvexComb M X => φ.sum_one)
  -- `A φ` enumerates the part of the support of `φ` lying over `y`
  obtain ⟨A, hndA, hmemA⟩ : ∃ A : MConvexComb M X → List X,
      (∀ φ, (A φ).Nodup) ∧
      (∀ (φ : MConvexComb M X) (x : X),
        x ∈ A φ ↔ (φ.toFun x ≠ 0 ∧ f x = y)) :=
    ⟨fun φ => (supp φ).filter (fun x => decide (f x = y)),
     fun φ => List.Nodup.filter _ (hsuppnd φ), fun φ x => by
       simp only [List.mem_filter, decide_eq_true_eq]
       rw [hsuppmem φ x]⟩
  -- and `LX` collects them all
  obtain ⟨LX, hndX, hmemX, hsubX⟩ : ∃ L : List X, L.Nodup ∧
      (∀ x ∈ L, f x = y) ∧ (∀ φ ∈ LΦ, ∀ x ∈ A φ, x ∈ L) :=
    ⟨(LΦ.flatMap A).dedup, List.nodup_dedup _, by
      intro x hx
      rw [List.mem_dedup, List.mem_flatMap] at hx
      obtain ⟨φ, -, hxφ⟩ := hx
      exact ((hmemA φ x).mp hxφ).2,
     fun φ hφ x hx =>
       List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨φ, hφ, hx⟩)⟩
  -- over `LX`, each `φ` sums to `(𝒟_M f)(φ)(y)`
  have key : ∀ φ ∈ LΦ, PCM.IsSumOf (LX.map φ.toFun) ((φ.map f).toFun y) := by
    intro φ hφ
    refine isSumOf_map_of_subset φ.toFun (hndA φ) hndX (hsubX φ hφ) ?_
      (map_spec φ f y (A φ) (hndA φ) (hmemA φ))
    intro x hx hnx
    by_contra h0
    exact hnx ((hmemA φ x).mpr ⟨h0, hmemX x hx⟩)
  -- the left-hand side is the sum of `μ(Φ)` over `LX`
  have h1 : PCM.IsSumOf (LX.map (mu Φ).toFun) (((mu Φ).map f).toFun y) := by
    obtain ⟨L1, hnd1, hmem1, -⟩ := (mu Φ).sum_one
    have hB : ∀ x, x ∈ L1.filter (fun x => decide (f x = y)) ↔
        ((mu Φ).toFun x ≠ 0 ∧ f x = y) := by
      intro x
      simp only [List.mem_filter, decide_eq_true_eq]
      rw [hmem1 x]
    refine isSumOf_map_of_subset (mu Φ).toFun (List.Nodup.filter _ hnd1) hndX
      ?_ ?_ (map_spec (mu Φ) f y _ (List.Nodup.filter _ hnd1) hB)
    · -- `μ(Φ)(x) ≠ 0` forces some `φ ∈ LΦ` with `φ(x) ≠ 0`, whence `x ∈ LX`
      intro x hx
      obtain ⟨hx0, hxy⟩ := (hB x).mp hx
      by_contra hnot
      refine hx0 (isSumOf_eq_zero ?_ (mu_spec Φ x LΦ hndΦ hmemΦ))
      intro a ha
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp ha
      have hzz : φ.toFun x = 0 := by
        by_contra h0
        exact hnot (hsubX φ hφ x ((hmemA φ x).mpr ⟨h0, hxy⟩))
      rw [hzz, (exc_emonzero (Φ.toFun φ)).1]
    · intro x hx hnx
      by_contra h0
      exact hnx ((hB x).mpr ⟨h0, hmemX x hx⟩)
  -- expand each `μ(Φ)(x)` and flatten
  have h2 : ∀ x ∈ LX, PCM.IsSumOf (LΦ.map fun φ => Φ.toFun φ * φ.toFun x)
      ((mu Φ).toFun x) := fun x _ => mu_spec Φ x LΦ hndΦ hmemΦ
  have h3 : PCM.IsSumOf
      (LX.flatMap fun x => LΦ.map fun φ => Φ.toFun φ * φ.toFun x)
      (((mu Φ).map f).toFun y) := isSumOf_flatMap _ _ h2 h1
  -- Fubini
  have h4 : PCM.IsSumOf
      (LΦ.flatMap fun φ => LX.map fun x => Φ.toFun φ * φ.toFun x)
      (((mu Φ).map f).toFun y) :=
    PCM.isSumOf_perm
      (flatMap_map_comm LX LΦ (fun x φ => Φ.toFun φ * φ.toFun x)) h3
  -- the rows contract to `Φ(φ) ⊙ (𝒟_M f)(φ)(y)`
  have h5 : ∀ φ ∈ LΦ, PCM.IsSumOf (LX.map fun x => Φ.toFun φ * φ.toFun x)
      (Φ.toFun φ * (φ.map f).toFun y) := by
    intro φ hφ
    have h := isSumOf_mul_left (Φ.toFun φ) (key φ hφ)
    rwa [List.map_map] at h
  have h6 : PCM.IsSumOf (LΦ.map fun φ => Φ.toFun φ * (φ.map f).toFun y)
      (((mu Φ).map f).toFun y) := isSumOf_of_flatMap _ _ h5 h4
  -- grouping along the fibres of `φ ↦ 𝒟_M f (φ)`
  obtain ⟨Lq, hndq, hmemq⟩ : ∃ L : List (MConvexComb M Y), L.Nodup ∧
      ∀ φ ∈ LΦ, φ.map f ∈ L :=
    ⟨(LΦ.map fun φ => φ.map f).dedup, List.nodup_dedup _, fun φ hφ =>
      List.mem_dedup.mpr (List.mem_map.mpr ⟨φ, hφ, rfl⟩)⟩
  have hfibmem : ∀ (q : MConvexComb M Y) (φ : MConvexComb M X),
      φ ∈ LΦ.filter (fun φ => decide (φ.map f = q)) ↔
        (Φ.toFun φ ≠ 0 ∧ φ.map f = q) := by
    intro q φ
    rw [List.mem_filter, hmemΦ φ]
    simp
  have h7 : ∀ q ∈ Lq, PCM.IsSumOf
      ((LΦ.filter (fun φ => decide (φ.map f = q))).map
        fun φ => Φ.toFun φ * (φ.map f).toFun y)
      ((Φ.map fun φ => φ.map f).toFun q * q.toFun y) := by
    intro q _
    have hmap : PCM.IsSumOf
        ((LΦ.filter (fun φ => decide (φ.map f = q))).map Φ.toFun)
        ((Φ.map fun φ => φ.map f).toFun q) :=
      map_spec Φ (fun φ => φ.map f) q _ (List.Nodup.filter _ hndΦ) (hfibmem q)
    have h := isSumOf_mul_right (q.toFun y) hmap
    rw [List.map_map] at h
    have heq : ((LΦ.filter (fun φ => decide (φ.map f = q))).map
        fun φ => Φ.toFun φ * (φ.map f).toFun y)
        = ((LΦ.filter (fun φ => decide (φ.map f = q))).map
        fun φ => Φ.toFun φ * q.toFun y) := by
      refine List.map_congr_left fun φ hφ => ?_
      rw [((hfibmem q φ).mp hφ).2]
    rw [heq]
    exact h
  have h8 : PCM.IsSumOf
      (Lq.map fun q => (Φ.map fun φ => φ.map f).toFun q * q.toFun y)
      (((mu Φ).map f).toFun y) :=
    isSumOf_map_fiber (fun φ => Φ.toFun φ * (φ.map f).toFun y)
      (fun φ => φ.map f)
      (fun q => (Φ.map fun φ => φ.map f).toFun q * q.toFun y)
      hndq hmemq h7 h6
  -- and the same list computes the right-hand side
  have h9 : PCM.IsSumOf
      (Lq.map fun q => (Φ.map fun φ => φ.map f).toFun q * q.toFun y)
      ((mu (Φ.map fun φ => φ.map f)).toFun y) := by
    obtain ⟨L3, hnd3, hmem3, -⟩ := (Φ.map fun φ => φ.map f).sum_one
    refine isSumOf_map_of_support _ hnd3 hndq ?_ ?_
      (mu_spec (Φ.map fun φ => φ.map f) y L3 hnd3 hmem3)
    · intro q hq
      refine (hmem3 q).mpr fun h0 => hq ?_
      rw [h0, (exc_emonzero (q.toFun y)).2]
    · intro q hq
      have hne : (Φ.map fun φ => φ.map f).toFun q ≠ 0 := by
        intro h0; exact hq (by rw [h0, (exc_emonzero (q.toFun y)).2])
      by_contra hnot
      refine hne ?_
      have hmap : PCM.IsSumOf
          ((LΦ.filter (fun φ => decide (φ.map f = q))).map Φ.toFun)
          ((Φ.map fun φ => φ.map f).toFun q) :=
        map_spec Φ (fun φ => φ.map f) q _ (List.Nodup.filter _ hndΦ) (hfibmem q)
      have hnil : LΦ.filter (fun φ => decide (φ.map f = q)) = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr fun φ hφ => ?_
        have hφ' := (hfibmem q φ).mp hφ
        exact hnot (hφ'.2 ▸ hmemq φ ((hmemΦ φ).mpr hφ'.1))
      rw [hnil, List.map_nil, PCM.isSumOf_nil_iff] at hmap
      exact hmap
  exact isSumOf_unique h8 h9

open Classical in
/-- **192III.2** (`exc-dm-effectus`, bsols.tex:2075): the right unit law of
the monad `𝒟_M`: `μ ∘ 𝒟_M η = id`. -/
theorem mu_map_eta {X : Type v} (p : MConvexComb M X) :
    mu (p.map eta) = p := by
  refine MConvexComb.ext (funext fun z => ?_)
  by_cases h1 : (1 : M) = 0
  · rw [eq_zero_of_one_eq_zero h1 ((mu (p.map eta)).toFun z),
      eq_zero_of_one_eq_zero h1 (p.toFun z)]
  have hval : ∀ x x' : X, (eta x : MConvexComb M X).toFun x' =
      if x' = x then (1 : M) else 0 := fun _ _ => rfl
  -- `η` is injective (as `1 ≠ 0`)
  have hinj : Function.Injective (eta : X → MConvexComb M X) := by
    intro x x' hxx
    by_contra hne
    have h : (eta x : MConvexComb M X).toFun x =
        (eta x' : MConvexComb M X).toFun x :=
      congrArg (fun q => MConvexComb.toFun q x) hxx
    rw [hval x x, hval x' x, if_pos rfl, if_neg hne] at h
    exact h1 h
  obtain ⟨Lp, hndp, hmemp, -⟩ := p.sum_one
  -- `(𝒟_M η)(p)(η x) = p(x)`
  have hmapval : ∀ x ∈ Lp,
      (p.map (eta : X → MConvexComb M X)).toFun (eta x) = p.toFun x := by
    intro x hx
    have hm : ∀ x' : X, x' ∈ [x] ↔
        (p.toFun x' ≠ 0 ∧ (eta x' : MConvexComb M X) = eta x) := by
      intro x'
      rw [List.mem_singleton]
      constructor
      · intro h
        rw [h]
        exact ⟨(hmemp x).mp hx, rfl⟩
      · exact fun h => hinj h.2
    have h := map_spec p eta (eta x) [x] (List.nodup_singleton x) hm
    rw [List.map_cons, List.map_nil] at h
    exact eq_of_isSumOf_singleton h
  -- the sum defining `μ` may be taken over `η(Lp)`
  have hndL : (Lp.map eta).Nodup := List.Nodup.map hinj hndp
  have h1' : PCM.IsSumOf
      ((Lp.map eta).map fun φ => (p.map eta).toFun φ * φ.toFun z)
      ((mu (p.map eta)).toFun z) := by
    obtain ⟨L1, hnd1, hmem1, -⟩ := (p.map (eta : X → MConvexComb M X)).sum_one
    refine isSumOf_map_of_support _ hnd1 hndL ?_ ?_
      (mu_spec (p.map (eta : X → MConvexComb M X)) z L1 hnd1 hmem1)
    · intro φ hφ
      refine (hmem1 φ).mpr fun h0 => hφ ?_
      rw [h0, (exc_emonzero (φ.toFun z)).2]
    · intro φ hφ
      have hne : (p.map eta).toFun φ ≠ 0 := by
        intro h0; exact hφ (by rw [h0, (exc_emonzero (φ.toFun z)).2])
      -- a non-zero value of `𝒟_M η (p)` forces a non-empty fibre
      have hfib : ∀ x, x ∈ Lp.filter (fun x => decide ((eta x : MConvexComb M X) = φ))
          ↔ (p.toFun x ≠ 0 ∧ (eta x : MConvexComb M X) = φ) := by
        intro x
        rw [List.mem_filter, hmemp x]
        simp
      by_contra hnot
      refine hne ?_
      have hmap := map_spec p eta φ _ (List.Nodup.filter _ hndp) hfib
      have hnil : Lp.filter (fun x => decide ((eta x : MConvexComb M X) = φ))
          = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
        obtain ⟨hx0, hxφ⟩ := (hfib x).mp hx
        exact hnot (hxφ ▸ List.mem_map.mpr ⟨x, (hmemp x).mpr hx0, rfl⟩)
      rw [hnil, List.map_nil, PCM.isSumOf_nil_iff] at hmap
      exact hmap
  -- each term is `p(x)` at `x = z` and `0` elsewhere
  have heq : ((Lp.map eta).map fun φ => (p.map eta).toFun φ * φ.toFun z)
      = Lp.map fun x => if z = x then p.toFun x else 0 := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    show (p.map eta).toFun (eta x) * (eta x : MConvexComb M X).toFun z = _
    rw [hmapval x hx, hval x z]
    by_cases hzx : z = x
    · rw [if_pos hzx, if_pos hzx, EffectMonoid.mul_one]
    · rw [if_neg hzx, if_neg hzx, (exc_emonzero (p.toFun x)).1]
  rw [heq] at h1'
  -- and that list sums to `p(z)`
  have h2' : PCM.IsSumOf (Lp.map fun x => if z = x then p.toFun x else 0)
      (p.toFun z) := by
    refine isSumOf_map_of_support (fun x => if z = x then p.toFun x else 0)
      (List.nodup_singleton z) hndp ?_ ?_ ?_
    · intro x hx
      by_cases hzx : z = x
      · rw [List.mem_singleton]; exact hzx.symm
      · rw [if_neg hzx] at hx; exact absurd rfl hx
    · intro x hx
      by_cases hzx : z = x
      · refine (hmemp x).mpr ?_
        rw [if_pos hzx] at hx; exact hx
      · rw [if_neg hzx] at hx; exact absurd rfl hx
    · rw [List.map_cons, List.map_nil, if_pos rfl]
      exact isSumOf_singleton (p.toFun z)
  exact isSumOf_unique h1' h2'

open Classical in
/-- Helper for `bin` (192II): the function which is `1` at `x` when `x = y`,
and otherwise `λ` at `x` and `λᵖ` at `y`, is a formal convex combination.
(Four cases: `x = y`, `λ = 0`, `λᵖ = 0`, and the generic one; the degenerate
effect monoid `1 = 0` is dealt with first.) -/
theorem bin_sum_one {X : Type v} (f : X → M) (l : M) (x y : X)
    (hf : ∀ z, f z = if x = y then (if z = x then 1 else 0)
      else if z = x then l else if z = y then orth l else 0) :
    ∃ s : List X, s.Nodup ∧ (∀ z, z ∈ s ↔ f z ≠ 0) ∧
      PCM.IsSumOf (s.map f) 1 := by
  by_cases h1 : (1 : M) = 0
  · refine ⟨[], List.nodup_nil, fun z => ?_, ?_⟩
    · simp only [List.not_mem_nil, false_iff, ne_eq, not_not]
      exact eq_zero_of_one_eq_zero h1 _
    · rw [List.map_nil, h1]
      exact PCM.IsSumOf.nil
  by_cases hxy : x = y
  · have hfx : f x = 1 := by rw [hf x, if_pos hxy, if_pos rfl]
    have hfz : ∀ z, z ≠ x → f z = 0 := by
      intro z hz; rw [hf z, if_pos hxy, if_neg hz]
    refine ⟨[x], List.nodup_singleton x, fun z => ?_, ?_⟩
    · rw [List.mem_singleton]
      refine ⟨?_, fun hz => ?_⟩
      · rintro rfl; rw [hfx]; exact h1
      · by_contra hzx; exact hz (hfz z hzx)
    · rw [List.map_cons, List.map_nil, hfx]
      exact isSumOf_singleton 1
  -- `x ≠ y` from here on
  have hfx : f x = l := by rw [hf x, if_neg hxy, if_pos rfl]
  have hfy : f y = orth l := by
    rw [hf y, if_neg hxy, if_neg (fun h : y = x => hxy h.symm), if_pos rfl]
  have hfz : ∀ z, z ≠ x → z ≠ y → f z = 0 := by
    intro z hzx hzy; rw [hf z, if_neg hxy, if_neg hzx, if_neg hzy]
  by_cases hl0 : l = 0
  · have hfy1 : f y = 1 := by rw [hfy, hl0, eabasics_orth_zero]
    refine ⟨[y], List.nodup_singleton y, fun z => ?_, ?_⟩
    · rw [List.mem_singleton]
      refine ⟨?_, fun hz => ?_⟩
      · rintro rfl; rw [hfy1]; exact h1
      · by_contra hzy
        by_cases hzx : z = x
        · exact hz (by rw [hzx, hfx, hl0])
        · exact hz (hfz z hzx hzy)
    · rw [List.map_cons, List.map_nil, hfy1]
      exact isSumOf_singleton 1
  by_cases hlo : orth l = 0
  · have hl1 : l = 1 := by
      have h := eabasics_orth_orth l
      rw [hlo, eabasics_orth_zero] at h
      exact h.symm
    refine ⟨[x], List.nodup_singleton x, fun z => ?_, ?_⟩
    · rw [List.mem_singleton]
      refine ⟨?_, fun hz => ?_⟩
      · rintro rfl; rw [hfx]; exact hl0
      · by_contra hzx
        by_cases hzy : z = y
        · exact hz (by rw [hzy, hfy, hlo])
        · exact hz (hfz z hzx hzy)
    · rw [List.map_cons, List.map_nil, hfx, hl1]
      exact isSumOf_singleton 1
  refine ⟨[x, y], ?_, fun z => ?_, ?_⟩
  · simp [hxy]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, fun hz => ?_⟩
    · rintro (rfl | rfl)
      · rw [hfx]; exact hl0
      · rw [hfy]; exact hlo
    · by_contra hcon
      push_neg at hcon
      exact hz (hfz z hcon.1 hcon.2)
  · rw [List.map_cons, List.map_cons, List.map_nil, hfx, hfy]
    have h := isSumOf_pair l (orth l) (EffectAlgebra.perp_orth l)
    rwa [EffectAlgebra.ovee_orth l] at h

open Classical in
/-- The binary convex combination `λ|x⟩ ⋁ λᵖ|y⟩` (used for cancellativity,
192IV). -/
noncomputable def bin {X : Type v} (l : M) (x y : X) : MConvexComb M X :=
  ⟨fun z =>
    if x = y then (if z = x then 1 else 0)
    else if z = x then l else if z = y then orth l else 0,
   bin_sum_one _ l x y fun _ => rfl⟩

end MConvexComb

section DMMonad

variable (M : Type u) [EffectMonoid M]

/-- **192III.1** (`exc-dm-effectus`, eff.tex:2380, Exercise\*): `𝒟_M` is a
functor `Set → Set` (with the action of `map`). -/
theorem exc_dm_effectus_functor :
    ∃ F : Type u ⥤ Type u, ∀ X : Type u, F.obj X = MConvexComb M X :=
  ⟨{ obj := fun X => MConvexComb M X
     map := fun {_ _} f => TypeCat.ofHom fun p => p.map (TypeCat.Hom.hom f)
     map_id := fun X => by
       ext p
       exact MConvexComb.map_id p
     map_comp := fun f g => by
       ext p
       exact (MConvexComb.map_comp p (⇑(TypeCat.Hom.hom f))
         (⇑(TypeCat.Hom.hom g))).symm },
   fun _ => rfl⟩

/-- **192III.2** (`exc-dm-effectus`, eff.tex:2397, Exercise\*):
`(𝒟_M, η, μ)` is a monad on `Set`. -/
theorem exc_dm_effectus_monad :
    ∃ T : Monad (Type u), ∀ X : Type u,
      T.toFunctor.obj X = MConvexComb M X := by
  refine ⟨{ toFunctor :=
              { obj := fun X => MConvexComb M X
                map := fun {_ _} f => TypeCat.ofHom fun p => p.map (TypeCat.Hom.hom f)
                map_id := fun X => by
                  ext p
                  exact MConvexComb.map_id p
                map_comp := fun f g => by
                  ext p
                  exact (MConvexComb.map_comp p (⇑(TypeCat.Hom.hom f))
                    (⇑(TypeCat.Hom.hom g))).symm }
            η := { app := fun X =>
                     TypeCat.ofHom (MConvexComb.eta : X → MConvexComb M X)
                   naturality := fun X Y f => by
                     ext x
                     exact (MConvexComb.map_eta x (⇑(TypeCat.Hom.hom f))).symm }
            μ := { app := fun X =>
                     TypeCat.ofHom
                       (MConvexComb.mu :
                         MConvexComb M (MConvexComb M X) → MConvexComb M X)
                   naturality := fun X Y f => by
                     ext Φ
                     exact (MConvexComb.mu_map Φ (⇑(TypeCat.Hom.hom f))).symm }
            assoc := fun X => by
              ext Φ
              exact (MConvexComb.mu_mu Φ).symm
            left_unit := fun X => by
              ext p
              exact MConvexComb.mu_eta p
            right_unit := fun X => by
              ext p
              exact MConvexComb.mu_map_eta p }, fun _ => rfl⟩

/-- **192III.3** (`exc-dm-effectus`, eff.tex:2410, Exercise\*): the Kleisli
category of `𝒟_M` is an effectus (in total form) with scalars `M`. -/
theorem exc_dm_effectus_kleisli (T : Monad (Type u))
    (hT : ∀ X : Type u, T.toFunctor.obj X = MConvexComb M X) :
    Nonempty (EffectusTotalStructure (Kleisli T)) := sorry

end DMMonad

/-! ## Abstract `M`-convex sets (parsec 192, continued) -/

/-- **192IV** (eff.tex:2419, Definition): an **abstract `M`-convex set**: a
set `X` with a map `h : 𝒟_M X → X` such that `h(1|x⟩) = x` and
`h ∘ μ = h ∘ 𝒟_M h` (i.e. an Eilenberg–Moore algebra of the monad `𝒟_M`).
Formalized as a structure (the pair `(X, h)` of the thesis). -/
structure MConvex (M : Type u) [EffectMonoid M] (X : Type v) :
    Type (max u v) where
  h : MConvexComb M X → X
  h_eta : ∀ x : X, h (MConvexComb.eta x) = x
  h_mu : ∀ Φ : MConvexComb M (MConvexComb M X), h (MConvexComb.mu Φ) = h (Φ.map h)

/-- **192IV** (eff.tex:2438, Definition): a map `f : X → Y` between abstract
`M`-convex sets is **`M`-affine** if `f(h_X(⋁ᵢ λᵢ|xᵢ⟩)) = h_Y(⋁ᵢ λᵢ|f xᵢ⟩)`,
i.e. `f ∘ h_X = h_Y ∘ 𝒟_M f`. -/
def MConvex.IsAffine {M : Type u} [EffectMonoid M] {X : Type v} {Y : Type w}
    (sX : MConvex M X) (sY : MConvex M Y) (f : X → Y) : Prop :=
  ∀ p : MConvexComb M X, f (sX.h p) = sY.h (p.map f)

/-- Composites of `M`-affine maps are `M`-affine (functoriality of `𝒟_M`). -/
theorem MConvex.IsAffine.comp {M : Type u} [EffectMonoid M]
    {X : Type v} {Y : Type w} {Z : Type t}
    {sX : MConvex M X} {sY : MConvex M Y} {sZ : MConvex M Z}
    {f : X → Y} {g : Y → Z}
    (hf : MConvex.IsAffine sX sY f) (hg : MConvex.IsAffine sY sZ g) :
    MConvex.IsAffine sX sZ (g ∘ f) := by
  intro p
  show g (f (sX.h p)) = sZ.h (p.map (g ∘ f))
  rw [hf p, hg (p.map f), MConvexComb.map_comp]

/-- A subset of an abstract `M`-convex set that is closed under `h` is again
an abstract `M`-convex set, and the inclusion is affine (by `rfl`). -/
noncomputable def MConvex.restrict {M : Type u} [EffectMonoid M] {Z : Type w}
    (sZ : MConvex M Z) (P : Z → Prop)
    (hP : ∀ Ψ : MConvexComb M {z // P z}, P (sZ.h (Ψ.map Subtype.val))) :
    MConvex M {z // P z} :=
  { h := fun Ψ => ⟨sZ.h (Ψ.map Subtype.val), hP Ψ⟩
    h_eta := fun s => Subtype.ext
      ((congrArg sZ.h (MConvexComb.map_eta s Subtype.val)).trans (sZ.h_eta _))
    h_mu := fun Φ => Subtype.ext
      ((congrArg sZ.h (MConvexComb.mu_map Φ Subtype.val)).trans
        ((sZ.h_mu _).trans
          ((congrArg sZ.h (MConvexComb.map_comp Φ
              (fun Ψ : MConvexComb M {z // P z} => Ψ.map Subtype.val) sZ.h)).trans
            (congrArg sZ.h (MConvexComb.map_comp Φ
              (fun Ψ : MConvexComb M {z // P z} =>
                (⟨sZ.h (Ψ.map Subtype.val), hP Ψ⟩ : {z // P z}))
              Subtype.val)).symm))) }

/-- **192IV** (eff.tex:2456, Definition): an abstract `M`-convex set `(X,h)`
is **cancellative** when `h(λ|y⟩ ⋁ λᵖ|x₁⟩) = h(λ|y⟩ ⋁ λᵖ|x₂⟩)` implies
`x₁ = x₂`, for `λ ≠ 1`. -/
def MConvex.Cancellative {M : Type u} [EffectMonoid M] {X : Type v}
    (st : MConvex M X) : Prop :=
  ∀ (y x₁ x₂ : X) (l : M), l ≠ 1 →
    st.h (MConvexComb.bin l y x₁) = st.h (MConvexComb.bin l y x₂) → x₁ = x₂

/-- **192IV** (eff.tex:2449, Definition): the category `AConv_M` of abstract
`M`-convex sets with `M`-affine maps (equivalently, the Eilenberg–Moore
category of `𝒟_M`). -/
structure AConvMCat (M : Type u) [EffectMonoid M] : Type (max u (v + 1)) where
  carrier : Type v
  str : MConvex M carrier

instance (M : Type u) [EffectMonoid M] : CoeSort (AConvMCat.{u, v} M) (Type v) :=
  ⟨AConvMCat.carrier⟩

/-- The category structure of `AConv_M` (192IV). -/
noncomputable instance (M : Type u) [EffectMonoid M] :
    Category.{v} (AConvMCat.{u, v} M) where
  Hom X Y := { f : X.carrier → Y.carrier // MConvex.IsAffine X.str Y.str f }
  id X := ⟨_root_.id, fun p => by rw [MConvexComb.map_id]; rfl⟩
  comp f g := ⟨g.1 ∘ f.1, f.2.comp g.2⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

/-- **192V.1** (eff.tex:2496, Examples): every convex subset `s` of a real
vector space is a cancellative abstract `[0,1]`-convex set, with
`h(⋁ᵢ λᵢ|xᵢ⟩) = Σᵢ λᵢ xᵢ`. -/
theorem convex_subset_mconvex {V : Type u} [AddCommGroup V] [Module ℝ V]
    (s : Set V) (hs : Convex ℝ s) :
    ∃ st : MConvex I s, st.Cancellative := sorry

/-- **192V.3** (eff.tex:2577, Examples): every (join-)semilattice is an
abstract `2`-convex set (in fact semilattices are *exactly* the abstract
`2`-convex sets). -/
theorem semilattice_two_convex (L : Type u) [SemilatticeSup L] :
    Nonempty (MConvex Bool L) := by
  classical
  -- Over `M = 2` the only summable family of non-zero scalars is a single
  -- `1`, so every formal `2`-convex combination is a Dirac distribution.
  have hdirac : ∀ (X : Type u) (p : MConvexComb Bool X),
      ∃ x : X, p = MConvexComb.eta x := by
    intro X p
    obtain ⟨l, hnd, hmem, hsum⟩ := p.sum_one
    have h0 : (0 : Bool) = false := rfl
    have hone : ∀ y : X, y ∈ l → p.toFun y = true := by
      intro y hy
      rcases Bool.eq_false_or_eq_true (p.toFun y) with hb | hb
      · exact hb
      · exact absurd (hb.trans h0.symm) ((hmem y).mp hy)
    -- the support list is a singleton
    have hsingle : ∃ a : X, l = [a] := by
      match l, hnd, hmem, hsum with
      | [], _, _, hsum =>
        rw [List.map_nil, PCM.isSumOf_nil_iff] at hsum
        exact absurd hsum.symm (by decide)
      | a :: t, _, hmem', hsum =>
        rw [List.map_cons, PCM.isSumOf_cons_iff] at hsum
        obtain ⟨s, hs, hperp, he⟩ := hsum
        have hpa : p.toFun a = true := hone a (List.mem_cons_self ..)
        have hs0 : s = false := by
          have : p.toFun a ⊓ s = ⊥ := hperp
          rw [hpa] at this
          revert this; cases s <;> simp [show (⊥ : Bool) = false from rfl]
        subst hs0
        refine ⟨a, ?_⟩
        match t, hs with
        | [], _ => rfl
        | b :: t', hs =>
          rw [List.map_cons, PCM.isSumOf_cons_iff] at hs
          obtain ⟨s', _, _, he'⟩ := hs
          have hpb : p.toFun b = true := hone b (List.mem_cons_of_mem _
            (List.mem_cons_self ..))
          have hcon : p.toFun b ⊔ s' = false := he'
          rw [hpb] at hcon
          exact absurd hcon (by simp)
    obtain ⟨a, rfl⟩ := hsingle
    refine ⟨a, MConvexComb.ext (funext fun y => ?_)⟩
    show p.toFun y = if y = a then (1 : Bool) else 0
    by_cases hy : y = a
    · subst hy; rw [if_pos rfl]; exact hone y (List.mem_cons_self ..)
    · rw [if_neg hy]
      by_contra hcon
      exact hy (List.mem_singleton.mp ((hmem y).mpr hcon))
  -- `η` is injective (as `1 ≠ 0` in `2`), so `h p := the `x` with `p = η x``
  -- inverts `η`, and the algebra laws are then formal
  have hinj : ∀ x y : L, (MConvexComb.eta x : MConvexComb Bool L) =
      MConvexComb.eta y → x = y := by
    intro x y hxy
    by_contra hne
    have hval := congrArg (fun q : MConvexComb Bool L => q.toFun x) hxy
    have hL : (MConvexComb.eta x : MConvexComb Bool L).toFun x = 1 := by
      show (if x = x then (1 : Bool) else 0) = 1
      rw [if_pos rfl]
    have hR : (MConvexComb.eta y : MConvexComb Bool L).toFun x = 0 := by
      show (if x = y then (1 : Bool) else 0) = 0
      rw [if_neg hne]
    rw [hL, hR] at hval
    exact absurd hval (by decide)
  have heta : ∀ x : L, (hdirac L (MConvexComb.eta x)).choose = x := fun x =>
    (hinj _ _ (hdirac L (MConvexComb.eta x)).choose_spec.symm)
  refine ⟨⟨fun p => (hdirac L p).choose, heta, fun Φ => ?_⟩⟩
  -- `Φ = η(φ)`, so `μ Φ = φ` and `𝒟(h)(Φ) = η(h φ)`
  obtain ⟨φ, hφ⟩ := hdirac _ Φ
  subst hφ
  rw [MConvexComb.mu_eta, MConvexComb.map_eta, heta]

/-- Helper for 192V.3: in `[0,1]` a finite partial sum vanishes iff all its
summands do (it is the real sum of non-negative reals). -/
theorem unitInterval_isSumOf_eq_zero_iff {l : List I} {s : I}
    (h : PCM.IsSumOf l s) : s = 0 ↔ ∀ a ∈ l, a = 0 := by
  have hI0 : ((0 : I) : ℝ) = 0 := rfl
  induction h with
  | nil => simp
  | @cons a l s hl hp ih =>
    have hcoe : ((ovee a s hp : I) : ℝ) = (a : ℝ) + (s : ℝ) := rfl
    constructor
    · intro h0
      have hc : (a : ℝ) + (s : ℝ) = 0 := by
        rw [← hcoe, h0, hI0]
      have ha : a = 0 := Subtype.ext (by rw [hI0]; linarith [a.2.1, s.2.1])
      have hs : s = 0 := Subtype.ext (by rw [hI0]; linarith [a.2.1, s.2.1])
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact ih.mp hs b hb
    · intro hall
      have ha : a = 0 := hall a (List.mem_cons_self ..)
      have hs : s = 0 := ih.mpr fun b hb => hall b (List.mem_cons_of_mem _ hb)
      refine Subtype.ext ?_
      rw [hcoe, ha, hs, hI0]
      ring

/-- Helper for 192V.3: `[0,1]` has no zero divisors. -/
theorem unitInterval_mul_eq_zero {a b : I} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have hI0 : ((0 : I) : ℝ) = 0 := rfl
  have hc : (a : ℝ) * (b : ℝ) = 0 := by
    have hv := congrArg Subtype.val h
    rwa [show ((a * b : I) : ℝ) = (a : ℝ) * (b : ℝ) from rfl, hI0] at hv
  rcases mul_eq_zero.mp hc with h0 | h0
  · exact Or.inl (Subtype.ext (by rw [h0, hI0]))
  · exact Or.inr (Subtype.ext (by rw [h0, hI0]))

/-- Helper for 192V.3: the join `⋁ (a :: l)` of a non-empty list in a
join-semilattice. -/
def listJoin {L : Type u} [SemilatticeSup L] (a : L) (l : List L) : L :=
  l.foldr (· ⊔ ·) a

/-- `⋁ (a :: l)` is the least upper bound of `a :: l`. -/
theorem listJoin_le_iff {L : Type u} [SemilatticeSup L] (a : L) (l : List L)
    (x : L) : listJoin a l ≤ x ↔ ∀ y ∈ a :: l, y ≤ x := by
  induction l with
  | nil => simp [listJoin]
  | cons b t ih =>
    show b ⊔ listJoin a t ≤ x ↔ _
    rw [sup_le_iff, ih]
    constructor
    · rintro ⟨hb, hall⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hall y (List.mem_cons_self ..)
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hb
        · exact hall y (List.mem_cons_of_mem _ hy)
    · intro hall
      refine ⟨hall b (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hall y (List.mem_cons_self ..)
      · exact hall y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))

/-- Every member of `a :: l` is below `⋁ (a :: l)`. -/
theorem le_listJoin {L : Type u} [SemilatticeSup L] (a : L) (l : List L)
    {x : L} (h : x ∈ a :: l) : x ≤ listJoin a l :=
  (listJoin_le_iff a l (listJoin a l)).mp le_rfl x h

/-- `⋁ (a :: l)` only depends on the set of members of `a :: l`. -/
theorem listJoin_congr {L : Type u} [SemilatticeSup L] {a b : L}
    {l m : List L} (h : ∀ x : L, x ∈ a :: l ↔ x ∈ b :: m) :
    listJoin a l = listJoin b m :=
  le_antisymm ((listJoin_le_iff _ _ _).mpr fun y hy => le_listJoin b m ((h y).mp hy))
    ((listJoin_le_iff _ _ _).mpr fun y hy => le_listJoin a l ((h y).mpr hy))

/-- **192V.3** (eff.tex:2581, Examples): every semilattice is also an
abstract `[0,1]`-convex set with `h(⋁ᵢ λᵢ|xᵢ⟩) = ⋁_{i : λᵢ ≠ 0} xᵢ`. -/
theorem semilattice_unitInterval_convex (L : Type u) [SemilatticeSup L] :
    Nonempty (MConvex I L) := by
  classical
  have hI0 : ((0 : I) : ℝ) = 0 := rfl
  have hI1 : ((1 : I) : ℝ) = 1 := rfl
  have hIne : (1 : I) ≠ 0 := fun hc => by
    have hv := congrArg Subtype.val hc
    rw [hI1, hI0] at hv
    norm_num at hv
  -- the support of a formal `[0,1]`-convex combination is a non-empty list
  have hsupp : ∀ (Y : Type u) (p : MConvexComb I Y), ∃ al : Y × List Y,
      (al.1 :: al.2).Nodup ∧ ∀ x : Y, x ∈ al.1 :: al.2 ↔ p.toFun x ≠ 0 := by
    intro Y p
    obtain ⟨l, hnd, hmem, hsum⟩ := p.sum_one
    match l, hnd, hmem, hsum with
    | [], _, _, hsum =>
      rw [List.map_nil, PCM.isSumOf_nil_iff] at hsum
      exact absurd hsum hIne
    | a :: t, hnd, hmem, _ => exact ⟨(a, t), hnd, hmem⟩
  let sel : ∀ Y : Type u, MConvexComb I Y → Y × List Y :=
    fun Y p => (hsupp Y p).choose
  have hselnd : ∀ (Y : Type u) (p : MConvexComb I Y),
      ((sel Y p).1 :: (sel Y p).2).Nodup := fun Y p => (hsupp Y p).choose_spec.1
  have hsel : ∀ (Y : Type u) (p : MConvexComb I Y) (x : Y),
      x ∈ (sel Y p).1 :: (sel Y p).2 ↔ p.toFun x ≠ 0 :=
    fun Y p => (hsupp Y p).choose_spec.2
  -- `H p` is the join of the support of `p`
  let H : MConvexComb I L → L := fun p => listJoin (sel L p).1 (sel L p).2
  have hH : ∀ (p : MConvexComb I L) (a : L) (l : List L),
      (∀ x : L, x ∈ a :: l ↔ p.toFun x ≠ 0) → H p = listJoin a l :=
    fun p a l hal => listJoin_congr fun x => (hsel L p x).trans (hal x).symm
  refine ⟨⟨H, fun x => ?_, fun Φ => ?_⟩⟩
  · -- `η x` is supported on `{x}`
    have hsp : ∀ y : L, y ∈ [x] ↔ (MConvexComb.eta x : MConvexComb I L).toFun y ≠ 0 := by
      intro y
      show y ∈ [x] ↔ (if y = x then (1 : I) else 0) ≠ 0
      rw [List.mem_singleton]
      by_cases hy : y = x
      · rw [if_pos hy]
        exact ⟨fun _ => hIne, fun _ => hy⟩
      · rw [if_neg hy]
        exact ⟨fun h => absurd h hy, fun h => absurd rfl h⟩
    show H (MConvexComb.eta x) = x
    rw [hH (MConvexComb.eta x) x [] hsp]
    rfl
  · -- support of `μ Φ` and of `𝒟(H)(Φ)`, computed from the support of `Φ`
    set b := (sel _ Φ).1 with hbdef
    set m := (sel _ Φ).2 with hmdef
    have hΦmem : ∀ φ : MConvexComb I L, φ ∈ b :: m ↔ Φ.toFun φ ≠ 0 := hsel _ Φ
    let supp : MConvexComb I L → List L := fun φ => (sel L φ).1 :: (sel L φ).2
    have hsuppmem : ∀ (φ : MConvexComb I L) (x : L), x ∈ supp φ ↔ φ.toFun x ≠ 0 :=
      fun φ => hsel L φ
    have hsuppjoin : ∀ φ : MConvexComb I L, H φ = listJoin (sel L φ).1 (sel L φ).2 :=
      fun _ => rfl
    -- (1) `(μ Φ) x ≠ 0` iff `x` lies in the support of some `φ` in `supp Φ`
    have hmu : ∀ x : L, (MConvexComb.mu Φ).toFun x ≠ 0 ↔
        ∃ φ ∈ b :: m, φ.toFun x ≠ 0 := by
      intro x
      have hs := MConvexComb.mu_spec Φ x (b :: m) (hselnd _ Φ) hΦmem
      have hz := unitInterval_isSumOf_eq_zero_iff hs
      constructor
      · intro hne
        by_contra hcon
        push_neg at hcon
        refine hne (hz.mpr ?_)
        rintro c hc
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hc
        show Φ.toFun φ * φ.toFun x = 0
        rw [hcon φ hφ]
        exact (exc_emonzero _).1
      · rintro ⟨φ, hφ, hx⟩ h0
        have hprod := (hz.mp h0) (Φ.toFun φ * φ.toFun x) (List.mem_map_of_mem hφ)
        rcases unitInterval_mul_eq_zero hprod with h1 | h1
        · exact (hΦmem φ).mp hφ h1
        · exact hx h1
    -- (2) `(𝒟(H) Φ) z ≠ 0` iff `z = H φ` for some `φ` in `supp Φ`
    have hmap : ∀ z : L, (Φ.map H).toFun z ≠ 0 ↔ ∃ φ ∈ b :: m, H φ = z := by
      intro z
      have hfil : ∀ φ : MConvexComb I L,
          φ ∈ (b :: m).filter (fun φ => decide (H φ = z)) ↔
            (Φ.toFun φ ≠ 0 ∧ H φ = z) := by
        intro φ
        rw [List.mem_filter, hΦmem φ]
        simp
      have hs := MConvexComb.map_spec Φ H z _ ((hselnd _ Φ).filter _) hfil
      have hz := unitInterval_isSumOf_eq_zero_iff hs
      constructor
      · intro hne
        by_contra hcon
        push_neg at hcon
        refine hne (hz.mpr ?_)
        rintro c hc
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hc
        exact absurd ((hfil φ).mp hφ).2 (hcon φ ((hΦmem φ).mpr ((hfil φ).mp hφ).1))
      · rintro ⟨φ, hφ, hz'⟩ h0
        exact ((hΦmem φ).mp hφ)
          ((hz.mp h0) _ (List.mem_map_of_mem ((hfil φ).mpr ⟨(hΦmem φ).mp hφ, hz'⟩)))
    -- the support of `μ Φ` is the union of the supports of the `φ`s
    have hcons : (b :: m).flatMap supp =
        (sel L b).1 :: ((sel L b).2 ++ m.flatMap supp) := by
      rw [List.flatMap_cons]
      rfl
    have hbig : ∀ x : L,
        x ∈ (sel L b).1 :: ((sel L b).2 ++ m.flatMap supp) ↔
          (MConvexComb.mu Φ).toFun x ≠ 0 := by
      intro x
      rw [← hcons, List.mem_flatMap, hmu x]
      exact exists_congr fun φ => and_congr_right fun _ => hsuppmem φ x
    have hHmu : H (MConvexComb.mu Φ) =
        listJoin (sel L b).1 ((sel L b).2 ++ m.flatMap supp) := hH _ _ _ hbig
    have hHmap : H (Φ.map H) = listJoin (H b) (m.map H) := by
      refine hH (Φ.map H) (H b) (m.map H) fun z => ?_
      rw [hmap z]
      constructor
      · intro hz
        rcases List.mem_cons.mp hz with hz1 | hz1
        · exact ⟨b, List.mem_cons_self .., hz1.symm⟩
        · obtain ⟨φ, hφ, hφz⟩ := List.mem_map.mp hz1
          exact ⟨φ, List.mem_cons_of_mem _ hφ, hφz⟩
      · rintro ⟨φ, hφ, hφz⟩
        rcases List.mem_cons.mp hφ with hφ1 | hφ1
        · exact List.mem_cons.mpr (Or.inl (by rw [← hφz, hφ1]))
        · exact List.mem_cons_of_mem _ (hφz ▸ List.mem_map_of_mem hφ1)
    -- the join of the union is the join of the joins
    rw [hHmu, hHmap]
    refine le_antisymm ((listJoin_le_iff _ _ _).mpr fun y hy => ?_)
      ((listJoin_le_iff _ _ _).mpr fun y hy => ?_)
    · obtain ⟨φ, hφ, hyφ⟩ := (hmu y).mp ((hbig y).mp hy)
      refine le_trans (le_listJoin (sel L φ).1 (sel L φ).2 ((hsuppmem φ y).mpr hyφ)) ?_
      rw [← hsuppjoin φ]
      refine le_listJoin (H b) (m.map H) ?_
      rcases List.mem_cons.mp hφ with hφ1 | hφ1
      · exact List.mem_cons.mpr (Or.inl (by rw [hφ1]))
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hφ1)
    · have hy' : ∃ φ ∈ b :: m, H φ = y := by
        rcases List.mem_cons.mp hy with hy1 | hy1
        · exact ⟨b, List.mem_cons_self .., hy1.symm⟩
        · obtain ⟨φ, hφ, hφy⟩ := List.mem_map.mp hy1
          exact ⟨φ, List.mem_cons_of_mem _ hφ, hφy⟩
      obtain ⟨φ, hφ, hφy⟩ := hy'
      rw [← hφy, hsuppjoin φ]
      refine (listJoin_le_iff _ _ _).mpr fun z hz => ?_
      exact le_listJoin _ _ ((hbig z).mpr
        ((hmu z).mpr ⟨φ, hφ, (hsuppmem φ z).mp hz⟩))


/-- **192V.4** (eff.tex:2591, Examples): every cancellative abstract
`[0,1]`-convex set is isomorphic (by an affine bijection) to a convex subset
of a real vector space. -/
theorem cancellative_iso_convex {X : Type u} (st : MConvex I X)
    (hc : st.Cancellative) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℝ V) (s : Set V)
      (_ : Convex ℝ s) (st' : MConvex I s) (f : X → s),
        Function.Bijective f ∧ st.IsAffine st' f := sorry

/-! ### The opposite effect monoid, and states as a convex set (192VII) -/

section Opposite

variable (M : Type u) [EffectMonoid M]

/-- The effect algebra structure of `Mᵐᵒᵖ` — the same effect algebra as `M`
(needed for the opposite effect monoid). -/
instance : PCM Mᵐᵒᵖ where
  zero := 0
  Perp a b := Perp a.unop b.unop
  ovee a b h := .op (ovee a.unop b.unop h)
  perp_comm h := PCM.perp_comm h
  ovee_comm h := congrArg MulOpposite.op (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := congrArg MulOpposite.op (PCM.ovee_assoc hab h)
  zero_perp a := PCM.zero_perp a.unop
  zero_ovee a := congrArg MulOpposite.op (PCM.zero_ovee a.unop)

/-- Sums in `Mᵐᵒᵖ` are the sums of `M`, transported along `op`. -/
theorem isSumOf_op {l : List M} {s : M} (h : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map MulOpposite.op) (MulOpposite.op s) := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | @cons a l s hl hp ih => exact PCM.IsSumOf.cons ih hp

instance : EffectAlgebra Mᵐᵒᵖ :=
  { (inferInstance : PCM Mᵐᵒᵖ) with
    one := 1
    orth := fun a => .op (orth a.unop)
    perp_orth := fun a => EffectAlgebra.perp_orth a.unop
    ovee_orth := fun a => congrArg MulOpposite.op (EffectAlgebra.ovee_orth a.unop)
    orth_unique := fun {a b} h h1 =>
      congrArg MulOpposite.op
        (EffectAlgebra.orth_unique (a := a.unop) (b := b.unop) h
          (congrArg MulOpposite.unop h1))
    eq_zero_of_perp_one := fun {a} h =>
      congrArg MulOpposite.op (EffectAlgebra.eq_zero_of_perp_one (a := a.unop) h) }

/-- The **opposite effect monoid** `Mᵒᵖ`: same effect algebra, multiplication
reversed (used in 192VII for the convex structure on states). -/
instance : EffectMonoid Mᵐᵒᵖ :=
  { (inferInstance : EffectAlgebra Mᵐᵒᵖ) with
    mul := (· * ·)
    one_mul := fun a => congrArg MulOpposite.op (EffectMonoid.mul_one a.unop)
    mul_one := fun a => congrArg MulOpposite.op (EffectMonoid.one_mul a.unop)
    mul_assoc := fun a b c =>
      congrArg MulOpposite.op
        (EffectMonoid.mul_assoc c.unop b.unop a.unop).symm
    distrib := by
      intro a b c d hab hcd
      have hperm :
          ([c.unop * a.unop, d.unop * a.unop, c.unop * b.unop, d.unop * b.unop] :
            List M).Perm
            [c.unop * a.unop, c.unop * b.unop, d.unop * a.unop, d.unop * b.unop] :=
        List.Perm.cons _ (List.Perm.swap _ _ _)
      exact isSumOf_op _ (PCM.isSumOf_perm hperm (EffectMonoid.distrib hcd hab)) }

end Opposite

section StatConvex

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

/-- **192VII** (eff.tex:2613, Proposition), first half: for an effectus `C`
with scalars `M`, the states `Stat X` form an abstract `Mᵒᵖ`-convex set,
with `h(⋁ᵢ λᵢ|φᵢ⟩) = [φ₁, …, φₙ] ∘ ⟨λ₁, …, λₙ⟩`. -/
theorem stat_mconvex (X : C) :
    Nonempty (MConvex (Scal C)ᵐᵒᵖ (Stat X)) := sorry

/-- **192VII** (eff.tex:2622, Proposition), second half: `Stat f = f ∘ (–)`
is affine for total `f`, and `Stat : Tot C → AConv_{Mᵒᵖ}` is a functor. -/
theorem stat_functor :
    ∃ F : Tot C ⥤ AConvMCat.{v, v} (Scal C)ᵐᵒᵖ,
      ∀ X : Tot C, (F.obj X).carrier = Stat X.base := sorry

end StatConvex

/-! ## Congruences and coproducts of abstract `M`-convex sets (parsec 193) -/

section Congruence

variable {M : Type u} [EffectMonoid M] {X : Type v}

/-- **193II** (`aconv-cong`, eff.tex:2685, Exercise): an equivalence
relation `∼` on an abstract `M`-convex set `(X, h)` is a **congruence** when
`𝒟_M(q)(φ) = 𝒟_M(q)(ψ)` implies `q(h(φ)) = q(h(ψ))`, where `q : X → X/∼` is
the quotient map. -/
def MConvex.IsCongruence (st : MConvex M X) (r : Setoid X) : Prop :=
  ∀ φ ψ : MConvexComb M X,
    φ.map (Quotient.mk r) = ψ.map (Quotient.mk r) →
      Quotient.mk r (st.h φ) = Quotient.mk r (st.h ψ)

/-- **193II.1** (`aconv-cong`, eff.tex:2702, Exercise): the maps `𝒟_M q` and
`𝒟_M 𝒟_M q` are surjective (as is `q` itself). -/
theorem aconv_cong_surjective (r : Setoid X) :
    Function.Surjective
      (fun p : MConvexComb M X => p.map (Quotient.mk r)) ∧
    Function.Surjective
      (fun P : MConvexComb M (MConvexComb M X) =>
        P.map (fun p => p.map (Quotient.mk r))) := by
  -- the author's proof: `𝒟_M` (and `𝒟_M 𝒟_M`) of a section of `q` is a
  -- section of `𝒟_M q` (resp. `𝒟_M 𝒟_M q`)
  have hsec : (Quotient.mk r ∘ Quotient.out : Quotient r → Quotient r) =
      _root_.id := funext fun z => z.out_eq
  have key : ∀ q : MConvexComb M (Quotient r),
      (q.map Quotient.out).map (Quotient.mk r) = q := by
    intro q
    rw [MConvexComb.map_comp, hsec, MConvexComb.map_id]
  refine ⟨fun q => ⟨q.map Quotient.out, key q⟩, fun Q => ⟨Q.map
    (fun q => q.map Quotient.out), ?_⟩⟩
  show (Q.map fun q => q.map Quotient.out).map
    (fun p : MConvexComb M X => p.map (Quotient.mk r)) = Q
  rw [MConvexComb.map_comp,
    show ((fun p : MConvexComb M X => p.map (Quotient.mk r)) ∘
      fun q : MConvexComb M (Quotient r) => q.map Quotient.out) = _root_.id from
      funext key,
    MConvexComb.map_id]

/-- **193II.2** (`aconv-cong`, eff.tex:2705, Exercise): `∼` is a congruence
iff the convex structure `h` descends to `X/∼` — there is (a necessarily
unique) `h_∼` with `h_∼ ∘ 𝒟_M q = q ∘ h`. -/
theorem aconv_cong_iff (st : MConvex M X) (r : Setoid X) :
    st.IsCongruence r ↔
      ∃ h' : MConvexComb M (Quotient r) → Quotient r,
        ∀ p : MConvexComb M X,
          h' (p.map (Quotient.mk r)) = Quotient.mk r (st.h p) := by
  constructor
  · -- `h_∼` exists by the congruence property along the section of `q`
    intro hc
    refine ⟨fun P => Quotient.mk r (st.h (P.map Quotient.out)), fun p => ?_⟩
    refine hc _ p ?_
    rw [MConvexComb.map_comp,
      show (Quotient.mk r ∘ Quotient.out : Quotient r → Quotient r) = _root_.id
        from funext fun z => z.out_eq,
      MConvexComb.map_id]
  · -- conversely `q ∘ h` factors through `𝒟_M q`, which is the congruence
    rintro ⟨h', hh'⟩ φ ψ hq
    rw [← hh' φ, ← hh' ψ, hq]

/-- **193II.3** (`aconv-cong`, eff.tex:2714, Exercise): for a congruence
`∼`, the quotient `(X/∼, h_∼)` is an abstract `M`-convex set and the
quotient map is `M`-affine. -/
theorem aconv_cong_quotient (st : MConvex M X) (r : Setoid X)
    (hc : st.IsCongruence r) :
    ∃ st' : MConvex M (Quotient r),
      st.IsAffine st' (Quotient.mk r) := by
  obtain ⟨h', hh'⟩ := (aconv_cong_iff st r).mp hc
  refine ⟨⟨h', ?_, ?_⟩, fun p => (hh' p).symm⟩
  · -- `h_∼ ∘ η ∘ q = h_∼ ∘ 𝒟_M q ∘ η = q ∘ h ∘ η = q`, by naturality of `η`
    refine Quotient.ind fun x => ?_
    rw [← MConvexComb.map_eta x (Quotient.mk r), hh' (MConvexComb.eta x),
      st.h_eta]
  · -- `h_∼ ∘ μ = h_∼ ∘ 𝒟_M h_∼` after precomposing with the surjection
    -- `𝒟_M 𝒟_M q`, by naturality of `μ`
    intro Φ
    obtain ⟨Ψ, hΨ⟩ := (aconv_cong_surjective (M := M) r).2 Φ
    have hΨ' : Ψ.map (fun p : MConvexComb M X => p.map (Quotient.mk r)) = Φ :=
      hΨ
    subst hΨ'
    have hL : MConvexComb.mu
        (Ψ.map fun p : MConvexComb M X => p.map (Quotient.mk r)) =
        (MConvexComb.mu Ψ).map (Quotient.mk r) :=
      (MConvexComb.mu_map Ψ (Quotient.mk r)).symm
    have hR : (Ψ.map fun p : MConvexComb M X => p.map (Quotient.mk r)).map h' =
        (Ψ.map st.h).map (Quotient.mk r) := by
      rw [MConvexComb.map_comp, MConvexComb.map_comp]
      congr 1
      funext p
      exact hh' p
    rw [hL, hR, hh' (MConvexComb.mu Ψ), hh' (Ψ.map st.h), st.h_mu Ψ]

/-- **193III** (`affine-kernel-cong`, eff.tex:2726, Exercise): the kernel
`{(x,y) : f(x) = f(y)}` of an affine map `f` between abstract `M`-convex
sets is a congruence. -/
theorem affine_kernel_cong {Y : Type v} (st : MConvex M X)
    (st' : MConvex M Y) (f : X → Y) (hf : st.IsAffine st' f) :
    st.IsCongruence (Setoid.ker f) := by
  intro φ ψ hq
  -- `f = f_∼ ∘ q`, so `𝒟_M f (φ) = 𝒟_M f (ψ)`, and `f` is affine
  have key : ∀ p : MConvexComb M X, p.map f =
      (p.map (Quotient.mk (Setoid.ker f))).map
        (Quotient.lift f fun _ _ h => h) := by
    intro p; rw [MConvexComb.map_comp]; rfl
  refine Quotient.sound ?_
  change f (st.h φ) = f (st.h ψ)
  rw [hf φ, hf ψ, key φ, key ψ, hq]

/-- **193IV** (`least-conv-cong`, eff.tex:2732, Exercise): every relation
`R ⊆ X²` on an abstract `M`-convex set is contained in a least congruence.
(The thesis moreover gives a syntactic description of this congruence by
derivations, which is not formalized here.) -/
theorem least_conv_cong (st : MConvex M X) (R : X → X → Prop) :
    ∃ r : Setoid X, st.IsCongruence r ∧ (∀ x y, R x y → r.r x y) ∧
      ∀ r' : Setoid X, st.IsCongruence r' → (∀ x y, R x y → r'.r x y) →
        ∀ x y, r.r x y → r'.r x y := by
  classical
  -- The intersection of all congruences containing `R` (the family is
  -- non-empty: the total relation is one).  Congruences are closed under
  -- arbitrary intersections because a smaller congruence `r` makes `𝒟_M(q_r)`
  -- refine `𝒟_M(q_{r'})` for every larger `r'`.
  set P : Setoid X → Prop :=
    fun r' => st.IsCongruence r' ∧ ∀ x y, R x y → r'.r x y with hP
  let r : Setoid X :=
    { r := fun x y => ∀ r' : Setoid X, P r' → r'.r x y
      iseqv :=
        ⟨fun x r' _ => r'.refl x, fun h r' hr' => r'.symm (h r' hr'),
          fun h₁ h₂ r' hr' => r'.trans (h₁ r' hr') (h₂ r' hr')⟩ }
  have hmono : ∀ (r' : Setoid X), P r' → ∀ x y, r.r x y → r'.r x y :=
    fun r' hr' _ _ h => h r' hr'
  refine ⟨r, ?_, fun x y hxy r' hr' => hr'.2 x y hxy, fun r' h₁ h₂ => hmono r' ⟨h₁, h₂⟩⟩
  intro φ ψ hq
  refine Quotient.sound (fun r' hr' => ?_)
  -- the canonical map `k : X/r → X/r'`
  let k : Quotient r → Quotient r' :=
    Quotient.lift (Quotient.mk r') fun a b hab => Quotient.sound (hmono r' hr' a b hab)
  have hk : ∀ p : MConvexComb M X, p.map (Quotient.mk r') = (p.map (Quotient.mk r)).map k :=
    fun p => by rw [MConvexComb.map_comp]; rfl
  exact Quotient.exact (hr'.1 φ ψ (by rw [hk φ, hk ψ, hq]))

end Congruence

/-- **193V** (`aconv-coprod`, eff.tex:2778, Proposition): `AConv_M` has
binary coproducts (constructed as a quotient of `𝒟_M(X + Y)` by the least
congruence making `η ∘ κ₁` and `η ∘ κ₂` affine).

⚠ Universe level: the coproduct carrier is a quotient of `𝒟_M(X + Y)`, whose
underlying type is `X + Y → M`, so it lands in `Type (max u v)` and **not** in
`Type v`.  The statement is therefore about `AConvMCat.{u, max u v}`; at
`AConvMCat.{u, v}` with `v < u` it is *false* (already `1 + 1 ≅ 𝒟_M {1,2}`
has as many elements as `M`).  See PROVING-LOG. -/
theorem aconv_coprod (M : Type u) [EffectMonoid M] :
    HasBinaryCoproducts (AConvMCat.{u, max u v} M) := by
  classical
  have : ∀ {X Y : AConvMCat.{u, max u v} M}, HasColimit (pair X Y) := by
    intro X Y
    -- the free abstract `M`-convex set on `X + Y`
    let D : MConvex M (MConvexComb M (X.carrier ⊕ Y.carrier)) :=
      ⟨MConvexComb.mu, MConvexComb.mu_eta, MConvexComb.mu_mu⟩
    -- the relation of eff.tex:2790, whose least congruence makes `η∘κᵢ` affine
    let R : MConvexComb M (X.carrier ⊕ Y.carrier) →
        MConvexComb M (X.carrier ⊕ Y.carrier) → Prop := fun a b =>
      (∃ χ : MConvexComb M X.carrier,
        a = χ.map Sum.inl ∧ b = MConvexComb.eta (Sum.inl (X.str.h χ))) ∨
      (∃ χ : MConvexComb M Y.carrier,
        a = χ.map Sum.inr ∧ b = MConvexComb.eta (Sum.inr (Y.str.h χ)))
    obtain ⟨r, hrc, hrR, hrleast⟩ := least_conv_cong D R
    obtain ⟨stC, hqaff⟩ := aconv_cong_quotient D r hrc
    let Cobj : AConvMCat.{u, max u v} M := ⟨Quotient r, stC⟩
    -- the coprojections `cᵢ = q ∘ η ∘ κᵢ` are affine (eff.tex:2806)
    have hc1 : MConvex.IsAffine X.str stC
        (fun x => Quotient.mk r (MConvexComb.eta (Sum.inl x))) := by
      intro p
      have h1 : Quotient.mk r (p.map Sum.inl)
          = Quotient.mk r (MConvexComb.eta (Sum.inl (X.str.h p))) :=
        Quotient.sound (hrR _ _ (Or.inl ⟨p, rfl, rfl⟩))
      have h2 := hqaff ((p.map Sum.inl).map MConvexComb.eta)
      rw [show D.h ((p.map Sum.inl).map MConvexComb.eta) = p.map Sum.inl from
        MConvexComb.mu_map_eta _] at h2
      show Quotient.mk r (MConvexComb.eta (Sum.inl (X.str.h p))) = _
      rw [← h1, h2, MConvexComb.map_comp, MConvexComb.map_comp]
      rfl
    have hc2 : MConvex.IsAffine Y.str stC
        (fun y => Quotient.mk r (MConvexComb.eta (Sum.inr y))) := by
      intro p
      have h1 : Quotient.mk r (p.map Sum.inr)
          = Quotient.mk r (MConvexComb.eta (Sum.inr (Y.str.h p))) :=
        Quotient.sound (hrR _ _ (Or.inr ⟨p, rfl, rfl⟩))
      have h2 := hqaff ((p.map Sum.inr).map MConvexComb.eta)
      rw [show D.h ((p.map Sum.inr).map MConvexComb.eta) = p.map Sum.inr from
        MConvexComb.mu_map_eta _] at h2
      show Quotient.mk r (MConvexComb.eta (Sum.inr (Y.str.h p))) = _
      rw [← h1, h2, MConvexComb.map_comp, MConvexComb.map_comp]
      rfl
    let c₁ : X ⟶ Cobj := ⟨fun x => Quotient.mk r (MConvexComb.eta (Sum.inl x)), hc1⟩
    let c₂ : Y ⟶ Cobj := ⟨fun y => Quotient.mk r (MConvexComb.eta (Sum.inr y)), hc2⟩
    -- `h_Z ∘ 𝒟_M[f,g]` is affine (eff.tex:2830) …
    have hFaff : ∀ (Z : AConvMCat.{u, max u v} M)
        (e : X.carrier ⊕ Y.carrier → Z.carrier),
        MConvex.IsAffine D Z.str (fun p => Z.str.h (p.map e)) := by
      intro Z e Φ
      show Z.str.h ((MConvexComb.mu Φ).map e) = _
      rw [MConvexComb.mu_map, Z.str.h_mu, MConvexComb.map_comp]
      rfl
    -- … and its kernel is a congruence containing `R`, hence contains `∼`
    have hFker : ∀ (Z : AConvMCat.{u, max u v} M) (f : X ⟶ Z) (g : Y ⟶ Z)
        (a b : MConvexComb M (X.carrier ⊕ Y.carrier)), r.r a b →
        Z.str.h (a.map (Sum.elim f.1 g.1)) = Z.str.h (b.map (Sum.elim f.1 g.1)) := by
      intro Z f g a b hab
      refine hrleast (Setoid.ker fun p => Z.str.h (p.map (Sum.elim f.1 g.1)))
        (affine_kernel_cong D Z.str _ (hFaff Z (Sum.elim f.1 g.1))) ?_ a b hab
      rintro a' b' (⟨χ, rfl, rfl⟩ | ⟨χ, rfl, rfl⟩)
      · show Z.str.h _ = Z.str.h _
        rw [MConvexComb.map_comp, MConvexComb.map_eta]
        show Z.str.h (χ.map (Sum.elim f.1 g.1 ∘ Sum.inl)) = _
        rw [Z.str.h_eta]
        exact (f.2 χ).symm
      · show Z.str.h _ = Z.str.h _
        rw [MConvexComb.map_comp, MConvexComb.map_eta]
        show Z.str.h (χ.map (Sum.elim f.1 g.1 ∘ Sum.inr)) = _
        rw [Z.str.h_eta]
        exact (g.2 χ).symm
    -- so `h_Z ∘ 𝒟_M[f,g]` descends to the mediating map `k` (eff.tex:2856)
    have hdesc : ∀ (Z : AConvMCat.{u, max u v} M) (f : X ⟶ Z) (g : Y ⟶ Z),
        ∃ k : Cobj ⟶ Z, ∀ p,
          k.1 (Quotient.mk r p) = Z.str.h (p.map (Sum.elim f.1 g.1)) := by
      intro Z f g
      refine ⟨⟨Quotient.lift (fun p => Z.str.h (p.map (Sum.elim f.1 g.1)))
        (fun a b hab => hFker Z f g a b hab), ?_⟩, fun p => rfl⟩
      intro P
      obtain ⟨P₀, hP₀⟩ := (aconv_cong_surjective (M := M) r).1 P
      have hP₀' : P₀.map (Quotient.mk r) = P := hP₀
      subst hP₀'
      rw [← hqaff P₀, MConvexComb.map_comp]
      exact hFaff Z (Sum.elim f.1 g.1) P₀
    -- uniqueness: `k' ∘ q = k' ∘ q ∘ μ ∘ 𝒟_M η = h_Z ∘ 𝒟_M[f,g]` (eff.tex:2876)
    have huniq : ∀ (Z : AConvMCat.{u, max u v} M) (f : X ⟶ Z) (g : Y ⟶ Z)
        (m : Cobj ⟶ Z), c₁ ≫ m = f → c₂ ≫ m = g →
        ∀ p, m.1 (Quotient.mk r p) = Z.str.h (p.map (Sum.elim f.1 g.1)) := by
      intro Z f g m hm1 hm2 z
      have he : ((m.1 ∘ Quotient.mk r) ∘ MConvexComb.eta) = Sum.elim f.1 g.1 := by
        funext s
        cases s with
        | inl x => exact congrArg (fun t : X ⟶ Z => t.1 x) hm1
        | inr y => exact congrArg (fun t : Y ⟶ Z => t.1 y) hm2
      have h1 : Quotient.mk r z
          = stC.h ((z.map MConvexComb.eta).map (Quotient.mk r)) := by
        have := hqaff (z.map MConvexComb.eta)
        rwa [show D.h (z.map MConvexComb.eta) = z from
          MConvexComb.mu_map_eta _] at this
      rw [h1, m.2, MConvexComb.map_comp, MConvexComb.map_comp, he]
    refine HasColimit.mk ⟨BinaryCofan.mk c₁ c₂, BinaryCofan.IsColimit.mk _
      (fun {Z} f g => (hdesc Z f g).choose) ?_ ?_ ?_⟩
    · intro Z f g
      refine Subtype.ext (funext fun x => ?_)
      have hx := (hdesc Z f g).choose_spec (MConvexComb.eta (Sum.inl x))
      show (hdesc Z f g).choose.1 (Quotient.mk r (MConvexComb.eta (Sum.inl x))) = f.1 x
      rw [hx, MConvexComb.map_eta, Z.str.h_eta]
      rfl
    · intro Z f g
      refine Subtype.ext (funext fun y => ?_)
      have hy := (hdesc Z f g).choose_spec (MConvexComb.eta (Sum.inr y))
      show (hdesc Z f g).choose.1 (Quotient.mk r (MConvexComb.eta (Sum.inr y))) = g.1 y
      rw [hy, MConvexComb.map_eta, Z.str.h_eta]
      rfl
    · intro Z f g m hm1 hm2
      refine Subtype.ext (funext fun z => ?_)
      refine Quotient.inductionOn z fun p => ?_
      rw [huniq Z f g m hm1 hm2 p, (hdesc Z f g).choose_spec p]
  exact hasBinaryCoproducts_of_hasColimit_pair _

/-- The one-element abstract `M`-convex set `1` (193X). -/
def AConvMCat.punit (M : Type u) [EffectMonoid M] : AConvMCat.{u, v} M :=
  ⟨PUnit, ⟨fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩⟩

/-- The free abstract `M`-convex structure `μ` on `𝒟_M X` (the algebra laws
are the monad laws `mu_eta` and `mu_mu`). -/
noncomputable def MConvexComb.freeStr (M : Type u) [EffectMonoid M]
    (X : Type v) : MConvex M (MConvexComb M X) :=
  ⟨MConvexComb.mu, MConvexComb.mu_eta, MConvexComb.mu_mu⟩

/-- The free abstract `M`-convex set `(𝒟_M X, μ)` on a set `X` (used in
193X; the algebra laws are the monad laws `mu_eta` and `mu_mu`). -/
noncomputable def AConvMCat.free (M : Type u) [EffectMonoid M] (X : Type v) :
    AConvMCat.{u, max u v} M :=
  ⟨MConvexComb M X, MConvexComb.freeStr M X⟩

/-! ### Freeness of `𝒟_M X`, and `𝒟_M 1 = 1`

`𝒟_M` is a left adjoint to the forgetful functor `AConv_M → Set` — the fact
the thesis suggests using for 193X.  The three lemmas below are that
adjunction in elementary form (existence, computation, uniqueness of the
mediating map), and they are what 193X and 194I.3 are proved from. -/

/-- **Freeness of `𝒟_M X`, existence half**: for an abstract `M`-convex set
`(Z, h_Z)` and a function `f : X → Z`, the map `p ↦ h_Z(𝒟_M f (p))` is affine
on the free convex set `(𝒟_M X, μ)`. -/
theorem MConvexComb.freeStr_desc_isAffine {M : Type u} [EffectMonoid M]
    {X : Type v} {Z : Type w} (sZ : MConvex M Z) (f : X → Z) :
    MConvex.IsAffine (MConvexComb.freeStr M X) sZ (fun p => sZ.h (p.map f)) := by
  intro Φ
  show sZ.h ((MConvexComb.mu Φ).map f) = _
  rw [MConvexComb.mu_map, sZ.h_mu, MConvexComb.map_comp]
  rfl

/-- **Freeness of `𝒟_M X`, uniqueness half**: an affine map out of the free
convex set `(𝒟_M X, μ)` is determined by its values on the Diracs `η(x)`. -/
theorem MConvexComb.freeStr_ext {M : Type u} [EffectMonoid M]
    {X : Type v} {Z : Type w} (sZ : MConvex M Z) (k : MConvexComb M X → Z)
    (hk : MConvex.IsAffine (MConvexComb.freeStr M X) sZ k)
    (p : MConvexComb M X) :
    k p = sZ.h (p.map (fun x => k (MConvexComb.eta x))) := by
  have h := hk (p.map MConvexComb.eta)
  rw [show (MConvexComb.freeStr M X).h (p.map MConvexComb.eta) = p from
    MConvexComb.mu_map_eta p, MConvexComb.map_comp] at h
  exact h

/-- Functoriality of the free convex set: `𝒟_M f` is affine. -/
theorem MConvexComb.freeStr_map_isAffine {M : Type u} [EffectMonoid M]
    {X : Type v} {Y : Type w} (f : X → Y) :
    MConvex.IsAffine (MConvexComb.freeStr M X) (MConvexComb.freeStr M Y)
      (fun p => p.map f) := by
  intro Φ
  show (MConvexComb.mu Φ).map f = _
  rw [MConvexComb.mu_map]
  rfl

/-- `𝒟_M f : 𝒟_M X ⟶ 𝒟_M Y` as an arrow of `AConv_M`. -/
noncomputable def AConvMCat.freeMap (M : Type u) [EffectMonoid M]
    {X Y : Type v} (f : X → Y) :
    AConvMCat.free.{u, v} M X ⟶ AConvMCat.free.{u, v} M Y :=
  ⟨fun p => p.map f, MConvexComb.freeStr_map_isAffine f⟩

@[simp]
theorem AConvMCat.freeMap_apply (M : Type u) [EffectMonoid M] {X Y : Type v}
    (f : X → Y) (p : MConvexComb M X) :
    (AConvMCat.freeMap M f).1 p = p.map f := rfl

@[simp]
theorem AConvMCat.freeMap_comp (M : Type u) [EffectMonoid M] {X Y Z : Type v}
    (f : X → Y) (g : Y → Z) :
    AConvMCat.freeMap M f ≫ AConvMCat.freeMap M g = AConvMCat.freeMap M (g ∘ f) :=
  Subtype.ext (funext fun p => MConvexComb.map_comp p f g)

@[simp]
theorem AConvMCat.freeMap_id (M : Type u) [EffectMonoid M] {X : Type v} :
    AConvMCat.freeMap M (_root_.id : X → X) = 𝟙 (AConvMCat.free.{u, v} M X) :=
  Subtype.ext (funext fun p => MConvexComb.map_id p)

/-- `𝒟_M` of a one-element set is a one-element set: every formal
`M`-convex combination over `PUnit` is the Dirac one.  (This holds also for
the trivial effect monoid `1 = 0`, where both sides are the zero function —
cf. QUESTIONS B7.) -/
theorem MConvexComb.eq_eta_punit {M : Type u} [EffectMonoid M]
    (p : MConvexComb M PUnit.{v + 1}) : p = MConvexComb.eta PUnit.unit := by
  classical
  have hval : ∀ z : PUnit.{v + 1},
      (MConvexComb.eta PUnit.unit : MConvexComb M PUnit.{v + 1}).toFun z =
        (1 : M) := fun z => if_pos rfl
  by_cases h1 : (1 : M) = 0
  · refine MConvexComb.ext (funext fun z => ?_)
    rw [eq_zero_of_one_eq_zero h1 (p.toFun z),
      eq_zero_of_one_eq_zero h1
        ((MConvexComb.eta PUnit.unit : MConvexComb M PUnit.{v + 1}).toFun z)]
  · obtain ⟨l, hnd, hmem, hs⟩ := p.sum_one
    have hone : p.toFun PUnit.unit = 1 := by
      match l, hnd, hs with
      | [], _, hs => exact absurd (PCM.isSumOf_nil_iff.mp hs) h1
      | [_], _, hs => exact (eq_of_isSumOf_singleton hs).symm
      | _ :: _ :: _, hnd, _ =>
          exact absurd (List.mem_cons_self ..) (List.nodup_cons.mp hnd).1
    exact MConvexComb.ext (funext fun z => by rw [hval z]; exact hone)

/-- Every function out of a one-element abstract `M`-convex set is affine. -/
theorem MConvexComb.punit_isAffine {M : Type u} [EffectMonoid M] {Z : Type w}
    (sP : MConvex M PUnit.{v + 1}) (sZ : MConvex M Z) (z : Z) :
    MConvex.IsAffine sP sZ (fun _ => z) := by
  intro p
  rw [MConvexComb.eq_eta_punit p, MConvexComb.map_eta]
  exact (sZ.h_eta z).symm

/-- `𝒟_M 1 = 1`: the free abstract `M`-convex set on a one-element set is
final. -/
noncomputable def AConvMCat.free_punit_isTerminal (M : Type u) [EffectMonoid M] :
    IsTerminal (AConvMCat.free.{u, v} M PUnit.{v + 1}) := by
  have hsub : ∀ p q : MConvexComb M PUnit.{v + 1}, p = q := fun p q => by
    rw [MConvexComb.eq_eta_punit p, MConvexComb.eq_eta_punit q]
  exact IsTerminal.ofUniqueHom
    (fun Z => ⟨fun _ => MConvexComb.eta PUnit.unit, fun p => hsub _ _⟩)
    (fun _ _ => Subtype.ext (funext fun _ => hsub _ _))

/-- **`𝒟_M` preserves binary coproducts** (the fact behind 193X and 194I.3):
if `X ≅ 𝒟_M A` and `Y ≅ 𝒟_M B`, then `𝒟_M (A + B)` is a coproduct of `X`
and `Y`, with coprojections `𝒟_M κᵢ` composed with the isomorphisms. -/
noncomputable def AConvMCat.isColimit_freeBinaryCofan {M : Type u} [EffectMonoid M]
    {A B : Type v} {X Y : AConvMCat.{u, max u v} M}
    (a : X ≅ AConvMCat.free M A) (b : Y ≅ AConvMCat.free M B) :
    IsColimit (BinaryCofan.mk
      (a.hom ≫ AConvMCat.freeMap M (Sum.inl : A → A ⊕ B))
      (b.hom ≫ AConvMCat.freeMap M (Sum.inr : B → A ⊕ B))) := by
  classical
  refine BinaryCofan.IsColimit.mk _ (fun {T} f g =>
    ⟨fun p => T.str.h (p.map (Sum.elim (fun x => (a.inv ≫ f).1 (MConvexComb.eta x))
      (fun y => (b.inv ≫ g).1 (MConvexComb.eta y)))),
      MConvexComb.freeStr_desc_isAffine _ _⟩) ?_ ?_ ?_
  · intro T f g
    refine Subtype.ext (funext fun x => ?_)
    have h1 : T.str.h ((((a.hom.1 x : MConvexComb M A)).map (Sum.inl : A → A ⊕ B)).map
        (Sum.elim (fun x => (a.inv ≫ f).1 (MConvexComb.eta x))
          (fun y => (b.inv ≫ g).1 (MConvexComb.eta y))))
        = (a.inv ≫ f).1 (a.hom.1 x) :=
      (congrArg T.str.h (MConvexComb.map_comp (a.hom.1 x) (Sum.inl : A → A ⊕ B)
          (Sum.elim (fun x => (a.inv ≫ f).1 (MConvexComb.eta x))
            (fun y => (b.inv ≫ g).1 (MConvexComb.eta y))))).trans
        (MConvexComb.freeStr_ext T.str (a.inv ≫ f).1 (a.inv ≫ f).2
          (a.hom.1 x)).symm
    exact h1.trans (congrArg (fun m : X ⟶ T => m.1 x) (a.hom_inv_id_assoc f))
  · intro T f g
    refine Subtype.ext (funext fun y => ?_)
    have h1 : T.str.h ((((b.hom.1 y : MConvexComb M B)).map (Sum.inr : B → A ⊕ B)).map
        (Sum.elim (fun x => (a.inv ≫ f).1 (MConvexComb.eta x))
          (fun y => (b.inv ≫ g).1 (MConvexComb.eta y))))
        = (b.inv ≫ g).1 (b.hom.1 y) :=
      (congrArg T.str.h (MConvexComb.map_comp (b.hom.1 y) (Sum.inr : B → A ⊕ B)
          (Sum.elim (fun x => (a.inv ≫ f).1 (MConvexComb.eta x))
            (fun y => (b.inv ≫ g).1 (MConvexComb.eta y))))).trans
        (MConvexComb.freeStr_ext T.str (b.inv ≫ g).1 (b.inv ≫ g).2
          (b.hom.1 y)).symm
    exact h1.trans (congrArg (fun m : Y ⟶ T => m.1 y) (b.hom_inv_id_assoc g))
  · intro T f g m hm1 hm2
    have hm1' : AConvMCat.freeMap M (Sum.inl : A → A ⊕ B) ≫ m = a.inv ≫ f := by
      have h : a.hom ≫ (AConvMCat.freeMap M (Sum.inl : A → A ⊕ B) ≫ m) = f :=
        (Category.assoc a.hom (AConvMCat.freeMap M (Sum.inl : A → A ⊕ B)) m).symm.trans hm1
      rw [← h, Iso.inv_hom_id_assoc]
    have hm2' : AConvMCat.freeMap M (Sum.inr : B → A ⊕ B) ≫ m = b.inv ≫ g := by
      have h : b.hom ≫ (AConvMCat.freeMap M (Sum.inr : B → A ⊕ B) ≫ m) = g :=
        (Category.assoc b.hom (AConvMCat.freeMap M (Sum.inr : B → A ⊕ B)) m).symm.trans hm2
      rw [← h, Iso.inv_hom_id_assoc]
    have hz : (fun z => m.1 (MConvexComb.eta z)) =
        Sum.elim (fun x => (a.inv ≫ f).1 (MConvexComb.eta x))
          (fun y => (b.inv ≫ g).1 (MConvexComb.eta y)) := by
      funext z
      rcases z with x | y
      · have h : m.1 ((MConvexComb.eta x).map (Sum.inl : A → A ⊕ B))
            = (a.inv ≫ f).1 (MConvexComb.eta x) :=
          congrArg (fun t : AConvMCat.free M A ⟶ T => t.1 (MConvexComb.eta x)) hm1'
        rw [MConvexComb.map_eta] at h
        exact h
      · have h : m.1 ((MConvexComb.eta y).map (Sum.inr : B → A ⊕ B))
            = (b.inv ≫ g).1 (MConvexComb.eta y) :=
          congrArg (fun t : AConvMCat.free M B ⟶ T => t.1 (MConvexComb.eta y)) hm2'
        rw [MConvexComb.map_eta] at h
        exact h
    refine Subtype.ext (funext fun p => ?_)
    have hfin := MConvexComb.freeStr_ext T.str m.1 m.2 p
    rw [hz] at hfin
    exact hfin

/-- **193X** (`n-times-one-aconvm`, eff.tex:2954, Exercise), first half: the
one-element convex set is the final object of `AConv_M`. -/
theorem n_times_one_aconvm_terminal (M : Type u) [EffectMonoid M] :
    Nonempty (IsTerminal (AConvMCat.punit.{u, v} M)) :=
  ⟨IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => PUnit.unit, fun _ => rfl⟩)
    (fun _ _ => Subtype.ext rfl)⟩

/-- Two affine maps out of a free abstract `M`-convex set that agree on the
Diracs are equal. -/
theorem AConvMCat.free_hom_ext {M : Type u} [EffectMonoid M] {A : Type v}
    {T : AConvMCat.{u, max u v} M} (m₁ m₂ : AConvMCat.free M A ⟶ T)
    (h : ∀ a : A, m₁.1 (MConvexComb.eta a) = m₂.1 (MConvexComb.eta a)) :
    m₁ = m₂ := by
  refine Subtype.ext (funext fun p => ?_)
  rw [MConvexComb.freeStr_ext T.str m₁.1 m₁.2 p,
    MConvexComb.freeStr_ext T.str m₂.1 m₂.2 p]
  exact congrArg T.str.h (congrArg p.map (funext h))

/-- Helper for 194I: the coproduct of two free abstract `M`-convex sets,
*with* its two coprojections — the form in which 193X is used in 194I.3. -/
theorem AConvMCat.exists_binaryCoprod_iso {M : Type u} [EffectMonoid M]
    {A B : Type v} {X Y : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X Y]
    (a : X ≅ AConvMCat.free M A) (b : Y ≅ AConvMCat.free M B) :
    ∃ e : (X ⨿ Y) ≅ AConvMCat.free M (A ⊕ B),
      coprod.inl ≫ e.hom = a.hom ≫ AConvMCat.freeMap M (Sum.inl : A → A ⊕ B) ∧
      coprod.inr ≫ e.hom = b.hom ≫ AConvMCat.freeMap M (Sum.inr : B → A ⊕ B) := by
  refine ⟨colimit.isoColimitCocone ⟨_, AConvMCat.isColimit_freeBinaryCofan a b⟩, ?_, ?_⟩
  · exact colimit.isoColimitCocone_ι_hom _ (Discrete.mk WalkingPair.left)
  · exact colimit.isoColimitCocone_ι_hom _ (Discrete.mk WalkingPair.right)

/-- **193X** (`n-times-one-aconvm`, eff.tex:2954, Exercise), second half: in
`AConv_M` the `n`-fold coproduct `n · 1 = 1 + ⋯ + 1` is isomorphic to
`𝒟_M {1, …, n}`.

The thesis's hint is "use that `𝒟_M`, as a left adjoint, preserves
coproducts", and that is the proof: `𝒟_M {1,…,n}` *is* the `n`-fold coproduct
of `𝒟_M 1 = 1`, by the freeness of `𝒟_M X` (`MConvexComb.freeStr_desc_isAffine`
and `MConvexComb.freeStr_ext` above) — no computation with the coproduct of
193V is needed.

The `HasFiniteCoproducts` hypothesis is only there to make `∐` meaningful;
it is discharged by `aconvalmosteffectus_coproducts.{u, u} M` (194I.1). -/
theorem n_times_one_aconvm (M : Type u) [EffectMonoid M] (n : ℕ)
    [HasFiniteCoproducts (AConvMCat.{u, u} M)] :
    Nonempty ((∐ fun _ : Fin n => AConvMCat.punit.{u, u} M) ≅
      AConvMCat.free M (ULift.{u} (Fin n))) := by
  classical
  let F : AConvMCat.{u, u} M := AConvMCat.free M (ULift.{u} (Fin n))
  let c : ∀ _ : Fin n, AConvMCat.punit.{u, u} M ⟶ F := fun i =>
    ⟨fun _ => MConvexComb.eta (ULift.up i),
      MConvexComb.punit_isAffine (AConvMCat.punit.{u, u} M).str F.str _⟩
  have hcol : IsColimit (Cofan.mk F c) := by
    refine Cofan.IsColimit.mk _ (fun t =>
      ⟨fun p => t.pt.str.h (p.map (fun j => (t.inj j.down).1 PUnit.unit)),
        MConvexComb.freeStr_desc_isAffine _ _⟩) ?_ ?_
    · intro t i
      refine Subtype.ext (funext fun _ => ?_)
      have h1 : t.pt.str.h ((MConvexComb.eta (ULift.up i) :
            MConvexComb M (ULift.{u} (Fin n))).map
            (fun j : ULift.{u} (Fin n) => (t.inj j.down).1 PUnit.unit))
          = (t.inj i).1 PUnit.unit := by
        rw [MConvexComb.map_eta, t.pt.str.h_eta]
      exact h1
    · intro t m hm
      have hz : (fun z : ULift.{u} (Fin n) => m.1 (MConvexComb.eta z)) =
          (fun j : ULift.{u} (Fin n) => (t.inj j.down).1 PUnit.unit) := by
        funext z
        exact congrArg (fun w : AConvMCat.punit.{u, u} M ⟶ t.pt => w.1 PUnit.unit)
          (hm z.down)
      refine Subtype.ext (funext fun p => ?_)
      have hfin := MConvexComb.freeStr_ext t.pt.str m.1 m.2 p
      rw [hz] at hfin
      exact hfin
  exact ⟨colimit.isoColimitCocone ⟨_, hcol⟩⟩

/-- Helper: the value of `𝒟_M f (p)` at a point `y` whose `f`-fibre is the
single point `x₀` is `p(x₀)`. -/
theorem MConvexComb.map_apply_of_unique_fiber {M : Type u} [EffectMonoid M]
    {X : Type v} {Y : Type w} (p : MConvexComb M X) (f : X → Y) {y : Y} {x₀ : X}
    (h : ∀ x, f x = y ↔ x = x₀) : (p.map f).toFun y = p.toFun x₀ := by
  classical
  by_cases hz : p.toFun x₀ = 0
  · have hm : ∀ x, x ∈ ([] : List X) ↔ (p.toFun x ≠ 0 ∧ f x = y) := by
      intro x
      simp only [List.not_mem_nil, false_iff, not_and]
      intro hx hfx
      exact hx (by rw [(h x).mp hfx]; exact hz)
    have hsp := MConvexComb.map_spec p f y [] List.nodup_nil hm
    rw [List.map_nil, PCM.isSumOf_nil_iff] at hsp
    rw [hsp, hz]
  · have hm : ∀ x, x ∈ [x₀] ↔ (p.toFun x ≠ 0 ∧ f x = y) := by
      intro x
      rw [List.mem_singleton]
      refine ⟨fun hx => ?_, fun hx => (h x).mp hx.2⟩
      rw [hx]
      exact ⟨hz, (h x₀).mpr rfl⟩
    have hsp := MConvexComb.map_spec p f y [x₀] (List.nodup_singleton x₀) hm
    rw [List.map_cons, List.map_nil] at hsp
    exact eq_of_isSumOf_singleton hsp

/-- Helper: every entry of a summable list is below the sum. -/
theorem PCM.le_of_mem_isSumOf {M : Type u} [PCM M] {A : Type v} (f : A → M)
    {l : List A} {a : A} (ha : a ∈ l) {s : M}
    (h : PCM.IsSumOf (l.map f) s) : f a ≼ s := by
  classical
  have hperm : (l.map f).Perm (f a :: (l.erase a).map f) := by
    have := (List.perm_cons_erase ha).map f
    simpa using this
  exact PCM.le_of_isSumOf_cons (PCM.isSumOf_perm hperm h)

/-- Helper: if `𝒟_M f (p)` vanishes at `y`, then `p` vanishes on the whole
`f`-fibre of `y`. -/
theorem MConvexComb.eq_zero_of_map_eq_zero {M : Type u} [EffectMonoid M]
    {X : Type v} {Y : Type w} (p : MConvexComb M X) (f : X → Y) {y : Y}
    (h : (p.map f).toFun y = 0) {x : X} (hx : f x = y) : p.toFun x = 0 := by
  classical
  by_contra hne
  obtain ⟨l, hnd, hmem, -⟩ := p.sum_one
  have hmemfib : ∀ x' : X,
      x' ∈ l.filter (fun x' => decide (f x' = y)) ↔ (p.toFun x' ≠ 0 ∧ f x' = y) := by
    intro x'
    rw [List.mem_filter, hmem x']
    simp
  have hsp := MConvexComb.map_spec p f y _ (List.Nodup.filter _ hnd) hmemfib
  rw [h] at hsp
  exact hne (eq_zero_of_le_zero
    (PCM.le_of_mem_isSumOf p.toFun ((hmemfib x).mpr ⟨hne, hx⟩) hsp))

/-- Helper: `𝒟_M` of a constant map is the Dirac distribution at its value. -/
theorem MConvexComb.map_const {M : Type u} [EffectMonoid M] {X : Type v}
    {Z : Type w} (p : MConvexComb M X) (z : Z) :
    p.map (fun _ => z) = MConvexComb.eta z := by
  classical
  obtain ⟨l, hnd, hmem, hs⟩ := p.sum_one
  refine MConvexComb.ext (funext fun w => ?_)
  by_cases hw : w = z
  · subst hw
    have hsp := MConvexComb.map_spec p (fun _ : X => w) w l hnd
      (fun x => by rw [hmem x]; simp)
    rw [isSumOf_unique hsp hs]
    exact (if_pos rfl).symm
  · have hsp := MConvexComb.map_spec p (fun _ : X => z) w [] List.nodup_nil
      (fun x => by
        simp only [List.not_mem_nil, false_iff, not_and]
        exact fun _ h => absurd h.symm hw)
    rw [List.map_nil, PCM.isSumOf_nil_iff] at hsp
    rw [hsp]
    exact (if_neg hw).symm

/-- Helper: a formal combination over `A + B` that vanishes on `B` is
`𝒟_M κ₁` of a formal combination over `A`. -/
theorem MConvexComb.exists_map_inl {M : Type u} [EffectMonoid M]
    {A B : Type v} (p : MConvexComb M (A ⊕ B))
    (h : ∀ b : B, p.toFun (Sum.inr b) = 0) :
    ∃ χ : MConvexComb M A, χ.map Sum.inl = p := by
  classical
  obtain ⟨l, hnd, hmem, hs⟩ := p.sum_one
  have hall : ∀ z ∈ l, ∃ a : A, z = Sum.inl a := by
    rintro (a | b) hz
    · exact ⟨a, rfl⟩
    · exact absurd (h b) ((hmem _).mp hz)
  have hll : ∀ L : List (A ⊕ B), (∀ z ∈ L, ∃ a : A, z = Sum.inl a) →
      (L.filterMap Sum.getLeft?).map Sum.inl = L := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons z L ih =>
        intro hz
        obtain ⟨a, rfl⟩ := hz z List.mem_cons_self
        rw [List.filterMap_cons]
        simp only [Sum.getLeft?_inl, List.map_cons, List.cons.injEq, true_and]
        exact ih fun w hw => hz w (List.mem_cons_of_mem _ hw)
  have hl' : (l.filterMap Sum.getLeft?).map Sum.inl = l := hll l hall
  have hinj : Function.Injective (Sum.inl : A → A ⊕ B) := fun _ _ h => by
    simpa using h
  have hmem' : ∀ a : A, a ∈ l.filterMap Sum.getLeft? ↔ p.toFun (Sum.inl a) ≠ 0 := by
    intro a
    rw [← hmem (Sum.inl a)]
    constructor
    · intro ha
      rw [← hl']
      exact List.mem_map_of_mem ha
    · intro ha
      rw [← hl'] at ha
      obtain ⟨a', ha', he⟩ := List.mem_map.mp ha
      rwa [hinj he] at ha'
  have hsum : PCM.IsSumOf ((l.filterMap Sum.getLeft?).map
      (fun a => p.toFun (Sum.inl a))) 1 := by
    rw [show (l.filterMap Sum.getLeft?).map (fun a => p.toFun (Sum.inl a))
        = ((l.filterMap Sum.getLeft?).map Sum.inl).map p.toFun from
      (List.map_map ..).symm, hl']
    exact hs
  refine ⟨⟨fun a => p.toFun (Sum.inl a),
    ⟨l.filterMap Sum.getLeft?, ?_, hmem', hsum⟩⟩, ?_⟩
  · exact List.Nodup.of_map Sum.inl (hl' ▸ hnd)
  · refine MConvexComb.ext (funext fun z => ?_)
    rcases z with a | b
    · exact MConvexComb.map_apply_of_unique_fiber _ Sum.inl
        (fun x => ⟨fun hx => (hinj hx), fun hx => by rw [hx]⟩)
    · have hsp := MConvexComb.map_spec (⟨fun a => p.toFun (Sum.inl a),
        ⟨l.filterMap Sum.getLeft?, List.Nodup.of_map Sum.inl (hl' ▸ hnd),
          hmem', hsum⟩⟩ : MConvexComb M A) Sum.inl (Sum.inr b) []
        List.nodup_nil (fun x => by simp)
      rw [List.map_nil, PCM.isSumOf_nil_iff] at hsp
      rw [hsp, h b]

/-- Helper for 194I.3: the thesis's computation with `1+1+1` as the set of
triples `(a,b,c) ∈ M³` with `a ⋁ b ⋁ c = 1`.  If `A` has exactly the three
elements `a₁,a₂,a₃` and `σ₁,σ₂ : A → B` single out `a₁` resp. `a₂` over a
point `b₁ ∈ B`, then `𝒟_M σ₁` and `𝒟_M σ₂` are jointly injective: they
determine the first two coordinates, and the third is the orthocomplement of
their sum. -/
theorem MConvexComb.jointly_injective_of_three {M : Type u} [EffectMonoid M]
    {A : Type v} {B : Type w} {a₁ a₂ a₃ : A} {b₁ : B}
    (hA : ∀ x : A, x = a₁ ∨ x = a₂ ∨ x = a₃)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    {σ₁ σ₂ : A → B}
    (hs₁ : ∀ x : A, σ₁ x = b₁ ↔ x = a₁) (hs₂ : ∀ x : A, σ₂ x = b₁ ↔ x = a₂)
    {p q : MConvexComb M A}
    (e₁ : p.map σ₁ = q.map σ₁) (e₂ : p.map σ₂ = q.map σ₂) : p = q := by
  classical
  -- the first two coordinates are read off from `𝒟_M σ₁` and `𝒟_M σ₂`
  have hv₁ : p.toFun a₁ = q.toFun a₁ := by
    rw [← MConvexComb.map_apply_of_unique_fiber p σ₁ hs₁,
      ← MConvexComb.map_apply_of_unique_fiber q σ₁ hs₁, e₁]
  have hv₂ : p.toFun a₂ = q.toFun a₂ := by
    rw [← MConvexComb.map_apply_of_unique_fiber p σ₂ hs₂,
      ← MConvexComb.map_apply_of_unique_fiber q σ₂ hs₂, e₂]
  -- the three coordinates sum to `1`
  have hnd : ([a₁, a₂, a₃] : List A).Nodup := by
    simp [h12, h13, h23]
  have hsum : ∀ r : MConvexComb M A,
      PCM.IsSumOf (([a₁, a₂, a₃] : List A).map r.toFun) 1 := by
    intro r
    obtain ⟨l, hndl, hmem, hs⟩ := r.sum_one
    refine isSumOf_map_of_support r.toFun hndl hnd (fun x hx => (hmem x).mpr hx)
      (fun x _ => ?_) hs
    rcases hA x with rfl | rfl | rfl <;> simp
  -- so the third is the orthocomplement of the sum of the first two
  have hthird : ∀ r : MConvexComb M A, ∃ hp : Perp (r.toFun a₁) (r.toFun a₂),
      r.toFun a₃ = orth (ovee (r.toFun a₁) (r.toFun a₂) hp) := by
    intro r
    obtain ⟨t, ht, hpt, het⟩ := PCM.isSumOf_cons_iff.mp (hsum r)
    obtain ⟨s, hs', hps, hes⟩ := PCM.isSumOf_cons_iff.mp ht
    have hsv : s = r.toFun a₃ := eq_of_isSumOf_singleton hs'
    subst hsv
    subst hes
    obtain ⟨hab, h', he'⟩ := PCM.assoc_left hps hpt
    exact ⟨hab, (EffectAlgebra.orth_unique h' (he'.trans het)).symm ▸ rfl⟩
  obtain ⟨hpp, hp3⟩ := hthird p
  obtain ⟨hqq, hq3⟩ := hthird q
  have hv₃ : p.toFun a₃ = q.toFun a₃ := by
    rw [hp3, hq3, PCM.ovee_congr hv₁ hv₂ hpp hqq]
  refine MConvexComb.ext (funext fun x => ?_)
  rcases hA x with rfl | rfl | rfl
  · exact hv₁
  · exact hv₂
  · exact hv₃

/-! ### The canonical surjection `𝒟_M(X+Y) ↠ X ⨿ Y`

193IX (`elements-coprod-conv`) records that every element of `X + Y` is of the
form `h(⋁ᵢ λᵢ|κ₁xᵢ⟩ ⋁ ⋁ⱼ σⱼ|κ₂yⱼ⟩)`, i.e. that the canonical affine map
`𝒟_M(X+Y) → X + Y` is **surjective**; it then gives an explicit description of
when two such expressions are equal (by *derivations*), which is what the
thesis uses for 194I.4.  That description is not formalized (see 193IV).  It
turns out not to be needed: surjectivity alone suffices, and it can be proved
from the universal property alone, by cutting `X + Y` down to the image of
`𝒟_M(X+Y)` and observing that the cut-down object again receives `κ₁` and
`κ₂`, so that the corestriction splits the inclusion. -/

/-- The canonical affine map `𝒟_M(X + Y) → X ⨿ Y`, `φ ↦ h(𝒟_M[κ₁,κ₂](φ))`. -/
noncomputable def AConvMCat.coprodQuot {M : Type u} [EffectMonoid M]
    (X Y : AConvMCat.{u, max u v} M) [HasBinaryCoproduct X Y] :
    AConvMCat.free M (X.carrier ⊕ Y.carrier) ⟶ X ⨿ Y :=
  ⟨fun p => (X ⨿ Y).str.h (p.map (Sum.elim (coprod.inl : X ⟶ X ⨿ Y).1
      (coprod.inr : Y ⟶ X ⨿ Y).1)),
    MConvexComb.freeStr_desc_isAffine _ _⟩

theorem AConvMCat.coprodQuot_eta_inl {M : Type u} [EffectMonoid M]
    {X Y : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X Y] (x : X.carrier) :
    (AConvMCat.coprodQuot X Y).1 (MConvexComb.eta (Sum.inl x))
      = (coprod.inl : X ⟶ X ⨿ Y).1 x := by
  show (X ⨿ Y).str.h ((MConvexComb.eta (Sum.inl x)).map _) = _
  rw [MConvexComb.map_eta]
  exact (X ⨿ Y).str.h_eta _

theorem AConvMCat.coprodQuot_eta_inr {M : Type u} [EffectMonoid M]
    {X Y : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X Y] (y : Y.carrier) :
    (AConvMCat.coprodQuot X Y).1 (MConvexComb.eta (Sum.inr y))
      = (coprod.inr : Y ⟶ X ⨿ Y).1 y := by
  show (X ⨿ Y).str.h ((MConvexComb.eta (Sum.inr y)).map _) = _
  rw [MConvexComb.map_eta]
  exact (X ⨿ Y).str.h_eta _

/-- **193IX** (`elements-coprod-conv`, eff.tex:2887, Remark), existence half:
every element of `X ⨿ Y` is `h(⋁ λᵢ|κ₁xᵢ⟩ ⋁ ⋁ σⱼ|κ₂yⱼ⟩)` for some formal
combination.  (The argument is ours: the thesis reads this off its explicit
construction of the coproduct, while the proof below uses only the universal
property.) -/
theorem AConvMCat.coprodQuot_surjective {M : Type u} [EffectMonoid M]
    (X Y : AConvMCat.{u, max u v} M) [HasBinaryCoproduct X Y] :
    Function.Surjective (AConvMCat.coprodQuot X Y).1 := by
  classical
  -- the image of `𝒟_M(X+Y)` in `X ⨿ Y`
  choose ch hch using
    (fun s : {w : (X ⨿ Y).carrier // ∃ p, (AConvMCat.coprodQuot X Y).1 p = w} => s.2)
  have hclosed : ∀ Ψ : MConvexComb M {w : (X ⨿ Y).carrier //
        ∃ p, (AConvMCat.coprodQuot X Y).1 p = w},
      ∃ p, (AConvMCat.coprodQuot X Y).1 p =
        (X ⨿ Y).str.h (Ψ.map (fun s => (s : (X ⨿ Y).carrier))) := by
    intro Ψ
    refine ⟨MConvexComb.mu (Ψ.map ch), ?_⟩
    have h2 : Ψ.map (fun s => (s : (X ⨿ Y).carrier))
        = (Ψ.map ch).map (AConvMCat.coprodQuot X Y).1 := by
      rw [MConvexComb.map_comp]
      exact congrArg Ψ.map (funext fun s => (hch s).symm)
    rw [h2]
    exact (AConvMCat.coprodQuot X Y).2 (Ψ.map ch)
  -- it is again an abstract `M`-convex set, and `val` is affine
  let SObj : AConvMCat.{u, max u v} M :=
    ⟨_, MConvex.restrict (X ⨿ Y).str
      (fun w => ∃ p, (AConvMCat.coprodQuot X Y).1 p = w) hclosed⟩
  let vv : SObj ⟶ X ⨿ Y := ⟨Subtype.val, fun _ => rfl⟩
  -- the coprojections corestrict to the image
  let k₁ : X ⟶ SObj :=
    ⟨fun x => ⟨(coprod.inl : X ⟶ X ⨿ Y).1 x,
        ⟨MConvexComb.eta (Sum.inl x), AConvMCat.coprodQuot_eta_inl x⟩⟩,
      fun p => Subtype.ext (by
        show (coprod.inl : X ⟶ X ⨿ Y).1 (X.str.h p) = (X ⨿ Y).str.h ((p.map _).map _)
        rw [MConvexComb.map_comp]
        exact (coprod.inl : X ⟶ X ⨿ Y).2 p)⟩
  let k₂ : Y ⟶ SObj :=
    ⟨fun y => ⟨(coprod.inr : Y ⟶ X ⨿ Y).1 y,
        ⟨MConvexComb.eta (Sum.inr y), AConvMCat.coprodQuot_eta_inr y⟩⟩,
      fun p => Subtype.ext (by
        show (coprod.inr : Y ⟶ X ⨿ Y).1 (Y.str.h p) = (X ⨿ Y).str.h ((p.map _).map _)
        rw [MConvexComb.map_comp]
        exact (coprod.inr : Y ⟶ X ⨿ Y).2 p)⟩
  have hm : coprod.desc k₁ k₂ ≫ vv = 𝟙 (X ⨿ Y) := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.comp_id]
      exact Subtype.ext rfl
    · rw [← Category.assoc, coprod.inr_desc, Category.comp_id]
      exact Subtype.ext rfl
  intro w
  refine ⟨((coprod.desc k₁ k₂).1 w).2.choose, ?_⟩
  rw [((coprod.desc k₁ k₂).1 w).2.choose_spec]
  exact congrArg (fun t : (X ⨿ Y) ⟶ (X ⨿ Y) => t.1 w) hm

/-- **194I.4**, first ingredient: `κ₁ : X → X + Y` is injective in `AConv_M`.

⚠ Divergence from the thesis.  eff.tex:3057–3175 proves this by an induction
over *derivations* (193IX), the longest argument of parsec 194, and one that
needs the syntactic description of the least congruence that 193IV leaves to
the reader.  It is unnecessary: constant maps are affine (`map_const`), so for
non-empty `X` the cotuple `[id_X, const x₀] : X + Y → X` is a retraction of
`κ₁`, and for empty `X` there is nothing to prove. -/
theorem AConvMCat.coprod_inl_injective {M : Type u} [EffectMonoid M]
    (X Y : AConvMCat.{u, max u v} M) [HasBinaryCoproduct X Y] :
    Function.Injective (coprod.inl : X ⟶ X ⨿ Y).1 := by
  classical
  rcases isEmpty_or_nonempty X.carrier with hE | hN
  · exact fun x => (hE.false x).elim
  · obtain ⟨x₀⟩ := hN
    have hconst : MConvex.IsAffine Y.str X.str (fun _ => x₀) := fun p => by
      rw [MConvexComb.map_const p x₀, X.str.h_eta]
    have hr := coprod.inl_desc (𝟙 X) (⟨fun _ => x₀, hconst⟩ : Y ⟶ X)
    intro x x' hxx
    have e1 : (coprod.desc (𝟙 X) (⟨fun _ => x₀, hconst⟩ : Y ⟶ X)).1
        ((coprod.inl : X ⟶ X ⨿ Y).1 x) = x :=
      congrArg (fun t : X ⟶ X => t.1 x) hr
    have e2 : (coprod.desc (𝟙 X) (⟨fun _ => x₀, hconst⟩ : Y ⟶ X)).1
        ((coprod.inl : X ⟶ X ⨿ Y).1 x') = x' :=
      congrArg (fun t : X ⟶ X => t.1 x') hr
    rw [← e1, ← e2, hxx]

/-! ## `AConv_M` is almost an effectus (parsec 194) -/

section AlmostEffectus

variable (M : Type u) [EffectMonoid M]

/-- **194I** (`aconvalmosteffectus`, eff.tex:2968, Proposition), part 1:
`AConv_M` has finite coproducts (binary ones by 193V; the empty set is the
initial object).

⚠ Two caveats, both recorded in PROVING-LOG.  (i) The universe level is
`max u v`, for the reason given at `aconv_coprod`.  (ii) "the empty set is the
initial object" fails for the **trivial** effect monoid `M` (`1 = 0`): there
`𝒟_M ∅` is a *singleton*, so `∅` carries no `h : 𝒟_M ∅ → ∅` and is not an
object of `AConv_M` at all.  `AConv_M` is then equivalent to the one-object,
one-arrow category and `1` is initial, so the proposition itself survives —
the proof below splits on `1 = 0`. -/
theorem aconvalmosteffectus_coproducts :
    HasFiniteCoproducts (AConvMCat.{u, max u v} M) := by
  classical
  have := aconv_coprod.{u, v} M
  have hinit : HasInitial (AConvMCat.{u, max u v} M) := by
    by_cases h1 : (1 : M) = 0
    · -- `1 = 0`: every abstract `M`-convex set is a singleton, so `1` is initial
      have hcombeq : ∀ (Z : Type (max u v)) (p q : MConvexComb M Z), p = q := fun Z p q =>
        MConvexComb.ext (funext fun z => by
          rw [eq_zero_of_one_eq_zero h1 (p.toFun z), eq_zero_of_one_eq_zero h1 (q.toFun z)])
      have hsub : ∀ (W : AConvMCat.{u, max u v} M) (x y : W.carrier), x = y := by
        intro W x y
        rw [← W.str.h_eta x, ← W.str.h_eta y,
          hcombeq _ (MConvexComb.eta x) (MConvexComb.eta y)]
      have hne : ∀ W : AConvMCat.{u, max u v} M, Nonempty W.carrier := by
        intro W
        refine ⟨W.str.h ⟨fun _ => 0, [], List.nodup_nil, fun x => by simp, ?_⟩⟩
        rw [List.map_nil, PCM.isSumOf_nil_iff]
        exact h1
      refine (IsInitial.ofUniqueHom (X := AConvMCat.punit.{u, max u v} M)
        (fun W => ?_) (fun W m => ?_)).hasInitial
      · exact Subtype.mk (fun _ => (hne W).some) (fun p => hsub W _ _)
      · exact Subtype.ext (funext fun _ => hsub W _ _)
    · -- `1 ≠ 0`: `𝒟_M` of an empty type is empty, so `∅` is an object, and initial
      have hemp : ∀ Z : Type (max u v), IsEmpty Z → IsEmpty (MConvexComb M Z) := by
        intro Z hZ
        refine ⟨fun p => ?_⟩
        obtain ⟨l, -, -, hs⟩ := p.sum_one
        cases l with
        | nil => rw [List.map_nil, PCM.isSumOf_nil_iff] at hs; exact h1 hs
        | cons a t => exact (hZ.false a).elim
      have h0 : IsEmpty (MConvexComb M (PEmpty.{max u v + 1})) := hemp _ inferInstance
      have h00 : IsEmpty (MConvexComb M (MConvexComb M (PEmpty.{max u v + 1}))) :=
        hemp _ h0
      let E : AConvMCat.{u, max u v} M :=
        ⟨PEmpty, ⟨fun p => (h0.false p).elim, fun x => x.elim,
          fun Φ => (h00.false Φ).elim⟩⟩
      refine (IsInitial.ofUniqueHom (X := E) (fun W => ?_) (fun W m => ?_)).hasInitial
      · exact Subtype.mk (fun x => x.elim) (fun p => (h0.false p).elim)
      · exact Subtype.ext (funext fun x => x.elim)
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-- **194I** (`aconvalmosteffectus`, eff.tex:2968, Proposition), part 2:
`AConv_M` has a final object (the one-element convex set, 193X). -/
theorem aconvalmosteffectus_terminal :
    HasTerminal (AConvMCat.{u, v} M) :=
  (n_times_one_aconvm_terminal.{u, v} M).some.hasTerminal

/-- **194I** (`aconvalmosteffectus`, eff.tex:2979, Proposition), part 3: the
cotuples `[κ₁,κ₂,κ₂], [κ₂,κ₁,κ₂] : 1+1+1 → 1+1` are jointly monic in
`AConv_M`.

⚠ Universe level: as for part 1, the statement is about
`AConvMCat.{u, max u v}` — its coproducts are quotients of function spaces
into `M`, so at `AConvMCat.{u, v}` with `v < u` the `HasFiniteCoproducts`
hypothesis is not instantiable and the hypothesised coproducts need not be
the ones the thesis computes with.  See PROVING-LOG.

The proof is the thesis's: identify `1+1+1` with `𝒟_M{1,2,3}` and `1+1` with
`𝒟_M{1,2}` (193X), under which the two cotuples become
`(a,b,c) ↦ (a, b⋁c)` and `(a,b,c) ↦ (b, a⋁c)`; these are jointly *injective*
(`MConvexComb.jointly_injective_of_three`), hence jointly monic. -/
theorem aconvalmosteffectus_jointlyMonic
    [HasFiniteCoproducts (AConvMCat.{u, max u v} M)]
    [HasTerminal (AConvMCat.{u, max u v} M)] :
    JointlyMonic
      (coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr :
        ((⊤_ AConvMCat.{u, max u v} M) ⨿ (⊤_ AConvMCat.{u, max u v} M)) ⨿
          (⊤_ AConvMCat.{u, max u v} M) ⟶
        (⊤_ AConvMCat.{u, max u v} M) ⨿ (⊤_ AConvMCat.{u, max u v} M))
      (coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr) := by
  classical
  have hT : IsTerminal (AConvMCat.free.{u, max u v} M PUnit.{max u v + 1}) :=
    AConvMCat.free_punit_isTerminal M
  obtain ⟨e2, e2l, e2r⟩ := AConvMCat.exists_binaryCoprod_iso
    (X := ⊤_ AConvMCat.{u, max u v} M) (Y := ⊤_ AConvMCat.{u, max u v} M)
    (terminalIsoIsTerminal hT) (terminalIsoIsTerminal hT)
  obtain ⟨e3, e3l, e3r⟩ :=
    AConvMCat.exists_binaryCoprod_iso e2 (terminalIsoIsTerminal hT)
  -- the two cotuples become `𝒟_M σ₁` and `𝒟_M σ₂` for these two maps of sets
  have key₁ : e3.hom ≫ AConvMCat.freeMap M
        (Sum.elim (Sum.elim Sum.inl Sum.inr) Sum.inr)
      = coprod.desc (coprod.desc coprod.inl coprod.inr) coprod.inr ≫ e2.hom := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
      simp [reassoc_of% e3l, reassoc_of% e3r, e2l, e2r,
        coprod.inl_desc, coprod.inr_desc]
  have key₂ : e3.hom ≫ AConvMCat.freeMap M
        (Sum.elim (Sum.elim Sum.inr Sum.inl) Sum.inr)
      = coprod.desc (coprod.desc coprod.inr coprod.inl) coprod.inr ≫ e2.hom := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
      simp [reassoc_of% e3l, reassoc_of% e3r, reassoc_of% e2l, reassoc_of% e2r,
        e2l, e2r, coprod.inl_desc, coprod.inr_desc]
  intro W a b ha hb
  refine (Iso.cancel_iso_hom_right a b e3).mp ?_
  have ha' : (a ≫ e3.hom) ≫ AConvMCat.freeMap M
        (Sum.elim (Sum.elim Sum.inl Sum.inr) Sum.inr)
      = (b ≫ e3.hom) ≫ AConvMCat.freeMap M
        (Sum.elim (Sum.elim Sum.inl Sum.inr) Sum.inr) := by
    rw [Category.assoc, Category.assoc, key₁, ← Category.assoc, ← Category.assoc, ha]
  have hb' : (a ≫ e3.hom) ≫ AConvMCat.freeMap M
        (Sum.elim (Sum.elim Sum.inr Sum.inl) Sum.inr)
      = (b ≫ e3.hom) ≫ AConvMCat.freeMap M
        (Sum.elim (Sum.elim Sum.inr Sum.inl) Sum.inr) := by
    rw [Category.assoc, Category.assoc, key₂, ← Category.assoc, ← Category.assoc, hb]
  refine Subtype.ext (funext fun z => ?_)
  have hz₁ : ((a ≫ e3.hom).1 z : MConvexComb M
        ((PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) ⊕ PUnit.{max u v + 1})).map
        (Sum.elim (Sum.elim Sum.inl Sum.inr) Sum.inr)
      = ((b ≫ e3.hom).1 z : MConvexComb M
        ((PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) ⊕ PUnit.{max u v + 1})).map
        (Sum.elim (Sum.elim Sum.inl Sum.inr) Sum.inr) :=
    congrArg (fun m : W ⟶ AConvMCat.free M
      (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 z) ha'
  have hz₂ : ((a ≫ e3.hom).1 z : MConvexComb M
        ((PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) ⊕ PUnit.{max u v + 1})).map
        (Sum.elim (Sum.elim Sum.inr Sum.inl) Sum.inr)
      = ((b ≫ e3.hom).1 z : MConvexComb M
        ((PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) ⊕ PUnit.{max u v + 1})).map
        (Sum.elim (Sum.elim Sum.inr Sum.inl) Sum.inr) :=
    congrArg (fun m : W ⟶ AConvMCat.free M
      (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 z) hb'
  exact MConvexComb.jointly_injective_of_three
    (a₁ := Sum.inl (Sum.inl PUnit.unit)) (a₂ := Sum.inl (Sum.inr PUnit.unit))
    (a₃ := Sum.inr PUnit.unit) (b₁ := Sum.inl PUnit.unit)
    (fun x => by rcases x with (x | x) | x <;> simp) (by simp) (by simp) (by simp)
    (fun x => by rcases x with (x | x) | x <;> simp)
    (fun x => by rcases x with (x | x) | x <;> simp) hz₁ hz₂

/-- **194I** (`aconvalmosteffectus`, eff.tex:3008, Proposition), part 4: the
right pullback squares of the effectus axioms (`(κ₁; !)`-squares) hold in
`AConv_M`; only the left squares remain open (settled in 196II when `M` is
an effect divisoid).

⚠ Universe level: `max u v`, as for parts 1 and 3; see PROVING-LOG.

The thesis's argument is followed for the *existence* of the mediating map
(if `(!+!) ∘ α = κ₁ ∘ !` then each `α(z)` has zero `Y`-mass, hence is
`κ₁(x_z)`, and `γ = x_(–)` is affine because `κ₁` is monic), but two
ingredients are proved differently, both times avoiding the unformalized
derivation calculus of 193IX/193IV:

* surjectivity of `𝒟_M(X+Y) → X+Y` (193IX) is obtained from the universal
  property, see `AConvMCat.coprodQuot_surjective`;
* injectivity of `κ₁` is obtained from the retraction `[id, const x₀]`, see
  `AConvMCat.coprod_inl_injective`, instead of by induction over
  derivations. -/
theorem aconvalmosteffectus_kappaPullback
    [HasFiniteCoproducts (AConvMCat.{u, max u v} M)]
    [HasTerminal (AConvMCat.{u, max u v} M)] (X Y : AConvMCat.{u, max u v} M) :
    IsPullback (terminal.from X) (coprod.inl : X ⟶ X ⨿ Y)
      (coprod.inl : (⊤_ AConvMCat.{u, max u v} M) ⟶ _)
      (coprod.map (terminal.from X) (terminal.from Y)) := by
  classical
  have hT : IsTerminal (AConvMCat.free.{u, max u v} M PUnit.{max u v + 1}) :=
    AConvMCat.free_punit_isTerminal M
  obtain ⟨e2, e2l, e2r⟩ := AConvMCat.exists_binaryCoprod_iso
    (X := ⊤_ AConvMCat.{u, max u v} M) (Y := ⊤_ AConvMCat.{u, max u v} M)
    (terminalIsoIsTerminal hT) (terminalIsoIsTerminal hT)
  -- `(!+!) ∘ q` is the pushforward along the collapse `X + Y → 1 + 1`
  have hlegl : (coprod.inl : X ⟶ X ⨿ Y) ≫
        coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom
      = terminal.from X ≫ (terminalIsoIsTerminal hT).hom ≫
        AConvMCat.freeMap M (Sum.inl : PUnit.{max u v + 1} → _) := by
    rw [← Category.assoc, coprod.inl_map, Category.assoc, e2l]
  have hlegr : (coprod.inr : Y ⟶ X ⨿ Y) ≫
        coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom
      = terminal.from Y ≫ (terminalIsoIsTerminal hT).hom ≫
        AConvMCat.freeMap M (Sum.inr : PUnit.{max u v + 1} → _) := by
    rw [← Category.assoc, coprod.inr_map, Category.assoc, e2r]
  have hcol : AConvMCat.coprodQuot X Y ≫
        coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom
      = AConvMCat.freeMap M (Sum.elim (fun _ => Sum.inl PUnit.unit)
          (fun _ => Sum.inr PUnit.unit) :
          X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) := by
    refine AConvMCat.free_hom_ext _ _ ?_
    rintro (x | y)
    · show (coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom).1
          ((AConvMCat.coprodQuot X Y).1 (MConvexComb.eta (Sum.inl x))) = _
      have hl : (coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom).1
            ((coprod.inl : X ⟶ X ⨿ Y).1 x)
          = ((terminal.from X ≫ (terminalIsoIsTerminal hT).hom).1 x).map
              (Sum.inl : PUnit.{max u v + 1} → _) :=
        congrArg (fun m : X ⟶ AConvMCat.free M
          (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 x) hlegl
      rw [AConvMCat.coprodQuot_eta_inl, AConvMCat.freeMap_apply, MConvexComb.map_eta,
        hl, MConvexComb.eq_eta_punit
          ((terminal.from X ≫ (terminalIsoIsTerminal hT).hom).1 x),
        MConvexComb.map_eta]
      rfl
    · show (coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom).1
          ((AConvMCat.coprodQuot X Y).1 (MConvexComb.eta (Sum.inr y))) = _
      have hl : (coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom).1
            ((coprod.inr : Y ⟶ X ⨿ Y).1 y)
          = ((terminal.from Y ≫ (terminalIsoIsTerminal hT).hom).1 y).map
              (Sum.inr : PUnit.{max u v + 1} → _) :=
        congrArg (fun m : Y ⟶ AConvMCat.free M
          (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 y) hlegr
      rw [AConvMCat.coprodQuot_eta_inr, AConvMCat.freeMap_apply, MConvexComb.map_eta,
        hl, MConvexComb.eq_eta_punit
          ((terminal.from Y ≫ (terminalIsoIsTerminal hT).hom).1 y),
        MConvexComb.map_eta]
      rfl
  refine IsPullback.mk' (coprod.inl_map _ _).symm ?_ ?_
  · intro T φ φ' _ h2
    exact Subtype.ext (funext fun z => AConvMCat.coprod_inl_injective X Y
      (congrArg (fun m : T ⟶ X ⨿ Y => m.1 z) h2))
  · intro T a b hab
    have hchain : a ≫ (coprod.inl : (⊤_ AConvMCat.{u, max u v} M) ⟶ _) ≫ e2.hom
        = b ≫ coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom := by
      rw [← Category.assoc, ← Category.assoc, hab]
    -- every `α(z)` has zero `Y`-mass, hence is `κ₁` of something
    have hex : ∀ z : T.carrier,
        ∃ x : X.carrier, (coprod.inl : X ⟶ X ⨿ Y).1 x = b.1 z := by
      intro z
      obtain ⟨φ, hφ⟩ := AConvMCat.coprodQuot_surjective X Y (b.1 z)
      have h1 : (b ≫ coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom).1 z
          = φ.map (Sum.elim (fun _ => Sum.inl PUnit.unit)
              (fun _ => Sum.inr PUnit.unit) :
              X.carrier ⊕ Y.carrier →
                PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) := by
        show (coprod.map (terminal.from X) (terminal.from Y) ≫ e2.hom).1 (b.1 z) = _
        rw [← hφ]
        exact congrArg (fun m : AConvMCat.free M (X.carrier ⊕ Y.carrier) ⟶
          AConvMCat.free M (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) =>
          m.1 φ) hcol
      have h2 : (a ≫ (coprod.inl : (⊤_ AConvMCat.{u, max u v} M) ⟶ _) ≫ e2.hom).1 z
          = MConvexComb.eta (Sum.inl PUnit.unit) := by
        rw [e2l]
        show ((a ≫ (terminalIsoIsTerminal hT).hom).1 z).map
          (Sum.inl : PUnit.{max u v + 1} → _) = _
        rw [MConvexComb.eq_eta_punit ((a ≫ (terminalIsoIsTerminal hT).hom).1 z),
          MConvexComb.map_eta]
      have hmapφ : φ.map (Sum.elim (fun _ => Sum.inl PUnit.unit)
          (fun _ => Sum.inr PUnit.unit) :
          X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1})
          = MConvexComb.eta (Sum.inl PUnit.unit) := by
        rw [← h1, ← congrArg (fun m : T ⟶ AConvMCat.free M
          (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 z) hchain]
        exact h2
      have hzero : ∀ y : Y.carrier, φ.toFun (Sum.inr y) = 0 := by
        intro y
        refine MConvexComb.eq_zero_of_map_eq_zero φ
          (Sum.elim (fun _ => Sum.inl PUnit.unit) (fun _ => Sum.inr PUnit.unit) :
            X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1})
          (y := Sum.inr PUnit.unit) ?_ (x := Sum.inr y) rfl
        rw [hmapφ]
        exact if_neg (by simp)
      obtain ⟨χ, hχ⟩ := MConvexComb.exists_map_inl φ hzero
      refine ⟨X.str.h χ, ?_⟩
      rw [← hφ, ← hχ]
      show (coprod.inl : X ⟶ X ⨿ Y).1 (X.str.h χ)
        = (X ⨿ Y).str.h ((χ.map (Sum.inl : X.carrier → X.carrier ⊕ Y.carrier)).map _)
      rw [MConvexComb.map_comp]
      exact (coprod.inl : X ⟶ X ⨿ Y).2 χ
    choose g hg using hex
    have hgaff : MConvex.IsAffine T.str X.str g := by
      intro p
      refine AConvMCat.coprod_inl_injective X Y ?_
      rw [hg (T.str.h p), b.2 p, (coprod.inl : X ⟶ X ⨿ Y).2 (p.map g),
        MConvexComb.map_comp]
      exact congrArg (X ⨿ Y).str.h (congrArg p.map (funext hg).symm)
    exact ⟨⟨g, hgaff⟩, terminalIsTerminal.hom_ext _ _,
      Subtype.ext (funext fun z => hg z)⟩

end AlmostEffectus

/-! ## Effect divisoids (parsec 195) -/

/-- **195II** (`dfn-effect-divisoid`, eff.tex:3187, Definition): an **effect
divisoid** is an effect monoid `M` with a partial division `a/b` (defined
for `a ≼ b`; formalized as a total operation whose axioms are guarded by
`a ≼ b`, cf. the *Beware* 195IIa) such that

1. `a/b` is the unique element with `a/b ≼ b/b` and `b ⊙ (a/b) = a`;
2. `a ≼ a/a`; and
3. `(a/a)/(a/a) = a/a`. -/
class EffectDivisoid (M : Type u) [EffectMonoid M] where
  /-- The partial division `a/b` (meaningful for `a ≼ b`). -/
  div : M → M → M
  div_le : ∀ {a b : M}, a ≼ b → div a b ≼ div b b
  mul_div : ∀ {a b : M}, a ≼ b → b * div a b = a
  div_unique : ∀ {a b c : M}, a ≼ b → c ≼ div b b → b * c = a → c = div a b
  le_div_self : ∀ a : M, a ≼ div a a
  div_div_self : ∀ a : M, div (div a a) (div a a) = div a a

export EffectDivisoid (div)

section DivisoidBasics

variable {M : Type u} [EffectMonoid M] [EffectDivisoid M]

/-- **195IV.1** (`exc-divisoid-basics`, eff.tex:3226, Exercise): `0/0 = 0`,
`1/1 = 1`, `a/1 = a`, `(a/a) ⊙ (a/a) = a/a` and `(a ⊙ b)/a = (a/a) ⊙ b`. -/
theorem exc_divisoid_basics_1 (a b : M) :
    div (0 : M) 0 = 0 ∧ div (1 : M) 1 = 1 ∧ div a 1 = a ∧
      div a a * div a a = div a a ∧ div (a * b) a = div a a * b := by
  -- `a/1 = 1 ⊙ (a/1) = a`; the rest is uniqueness of the division.
  have hdiv_one : ∀ x : M, div x 1 = x := by
    intro x
    have h := EffectDivisoid.mul_div (ea_le_one x)
    rwa [EffectMonoid.one_mul] at h
  have hself : ∀ x : M, x * div x x = x := fun x =>
    EffectDivisoid.mul_div (pcm_preorder_refl x)
  refine ⟨?_, hdiv_one 1, hdiv_one a, ?_, ?_⟩
  · -- `0 ≼ 0/0` and `0 ⊙ 0 = 0`, so `0 = 0/0` by uniqueness.
    exact (EffectDivisoid.div_unique (pcm_preorder_refl (0 : M))
      (pcm_zero_le _) (exc_emonzero (0 : M)).1).symm
  · -- `(a/a) ⊙ (a/a) ≼ a/a` and `a ⊙ (a/a) ⊙ (a/a) = a ⊙ (a/a) = a`.
    refine EffectDivisoid.div_unique (pcm_preorder_refl a)
      (emon_mul_le_self _ _) ?_
    rw [← EffectMonoid.mul_assoc, hself a, hself a]
  · -- `(a/a) ⊙ b ≼ a/a` and `a ⊙ (a/a) ⊙ b = a ⊙ b`.
    refine (EffectDivisoid.div_unique (emon_mul_le_self a b)
      (emon_mul_le_self _ _) ?_).symm
    rw [← EffectMonoid.mul_assoc, hself a]

/-- **195IV.2** (`exc-divisoid-basics`, eff.tex:3233, Exercise): for
`a ≼ b ≼ c` we have `(b/c) ⊙ (a/b) = a/c`. -/
theorem exc_divisoid_basics_2 {a b c : M} (hab : a ≼ b) (hbc : b ≼ c) :
    div b c * div a b = div a c := by
  -- `(b/c) ⊙ (a/b) ≼ b/c ≼ c/c` and `c ⊙ (b/c) ⊙ (a/b) = b ⊙ (a/b) = a`.
  refine EffectDivisoid.div_unique (pcm_preorder_trans hab hbc)
    (pcm_preorder_trans (emon_mul_le_self _ _) (EffectDivisoid.div_le hbc)) ?_
  rw [← EffectMonoid.mul_assoc, EffectDivisoid.mul_div hbc,
    EffectDivisoid.mul_div hab]

end DivisoidBasics

/-- Helper: the algebraic order `≼` of the effect algebra `[0,1]` is the
usual order of the reals. -/
theorem unitInterval_le_iff {a b : I} : a ≼ b ↔ (a : ℝ) ≤ (b : ℝ) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    show (a : ℝ) ≤ (a : ℝ) + (c : ℝ)
    linarith [c.2.1]
  · intro h
    refine ⟨⟨(b : ℝ) - (a : ℝ), by linarith [a.2.1], by linarith [b.2.2, a.2.1]⟩,
      ?_, ?_⟩
    · show (a : ℝ) + ((b : ℝ) - (a : ℝ)) ≤ 1
      linarith [b.2.2]
    · apply Subtype.ext
      show (a : ℝ) + ((b : ℝ) - (a : ℝ)) = (b : ℝ)
      ring

/-- **195V.1** (eff.tex:3243, Examples): `[0,1]` is an effect divisoid with
`a/b` the ordinary quotient (and `0/0 = 0`). -/
noncomputable instance unitInterval.effectDivisoid : EffectDivisoid I where
  -- `div` must be *total*, while the thesis's division is only meaningful for
  -- `a ≼ b`; we truncate at `1`, which changes nothing when `a ≤ b` (then
  -- `a/b ≤ 1`), so this really is "the ordinary quotient" where it matters.
  div a b := if (b : ℝ) = 0 then 0
    else ⟨min ((a : ℝ) / b) 1,
      le_min (div_nonneg a.2.1 b.2.1) zero_le_one, min_le_right _ _⟩
  div_le := by
    intro a b _
    refine unitInterval_le_iff.mpr ?_
    split_ifs with hb
    · exact le_rfl
    · show min ((a : ℝ) / (b : ℝ)) 1 ≤ min ((b : ℝ) / (b : ℝ)) 1
      rw [div_self hb, min_self]
      exact min_le_right _ _
  mul_div := by
    intro a b hab
    have hab' : (a : ℝ) ≤ (b : ℝ) := unitInterval_le_iff.mp hab
    apply Subtype.ext
    split_ifs with hb
    · have ha0 : (a : ℝ) = 0 := le_antisymm (by rw [← hb]; exact hab') a.2.1
      show (b : ℝ) * (0 : ℝ) = (a : ℝ)
      rw [ha0, mul_zero]
    · have hbne : (b : ℝ) ≠ 0 := hb
      have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_le_of_ne b.2.1 (Ne.symm hb)
      have hmin : min ((a : ℝ) / (b : ℝ)) 1 = (a : ℝ) / (b : ℝ) :=
        min_eq_left ((div_le_one hb0).mpr hab')
      show (b : ℝ) * min ((a : ℝ) / (b : ℝ)) 1 = (a : ℝ)
      rw [hmin]
      field_simp
  div_unique := by
    intro a b c hab hc hbc
    have hab' : (a : ℝ) ≤ (b : ℝ) := unitInterval_le_iff.mp hab
    have hval : (b : ℝ) * (c : ℝ) = (a : ℝ) := congrArg Subtype.val hbc
    apply Subtype.ext
    split_ifs with hb
    · rw [if_pos hb] at hc
      have hc' : (c : ℝ) ≤ 0 := unitInterval_le_iff.mp hc
      show (c : ℝ) = (0 : ℝ)
      exact le_antisymm hc' c.2.1
    · have hbne : (b : ℝ) ≠ 0 := hb
      have hdiv : (a : ℝ) / (b : ℝ) = (c : ℝ) := by
        rw [← hval]; field_simp
      show (c : ℝ) = min ((a : ℝ) / (b : ℝ)) 1
      rw [hdiv]
      exact (min_eq_left c.2.2).symm
  le_div_self := by
    intro a
    refine unitInterval_le_iff.mpr ?_
    split_ifs with ha
    · show (a : ℝ) ≤ (0 : ℝ)
      exact le_of_eq ha
    · show (a : ℝ) ≤ min ((a : ℝ) / (a : ℝ)) 1
      rw [div_self ha, min_self]
      exact a.2.2
  div_div_self := by
    intro a
    split_ifs with ha h2 h3
    · rfl
    · exact absurd rfl h2
    · -- `a ≠ 0` makes `a/a = 1`, so the second condition cannot hold
      have h1 : min ((a : ℝ) / (a : ℝ)) 1 = 1 := by rw [div_self ha, min_self]
      have hone : (1 : ℝ) = 0 := by rw [← h1]; exact h3
      exact absurd hone one_ne_zero
    · have h1 : min ((a : ℝ) / (a : ℝ)) 1 = 1 := by rw [div_self ha, min_self]
      apply Subtype.ext
      show min (min ((a : ℝ) / (a : ℝ)) 1 / min ((a : ℝ) / (a : ℝ)) 1) 1
        = min ((a : ℝ) / (a : ℝ)) 1
      rw [h1, div_self one_ne_zero, min_self]

/-- **195V.1** (eff.tex:3246, Examples): the two-element effect monoid `2`
is an effect divisoid (with `a/b = a`). -/
instance : EffectDivisoid Bool where
  div a _ := a
  div_le h := h
  mul_div := by
    rintro a b ⟨c, hc, rfl⟩
    show (a ⊔ c) ⊓ a = a
    exact inf_eq_right.mpr le_sup_left
  div_unique := by
    rintro a b c _ ⟨e, he, rfl⟩ hmul
    rw [← hmul]
    exact (inf_eq_right.mpr le_sup_left).symm
  le_div_self a := pcm_preorder_refl a
  div_div_self _ := rfl

/-- Helper: the algebraic order of a product effect algebra is
componentwise. -/
theorem prod_le_iff {M N : Type u} [EffectAlgebra M] [EffectAlgebra N]
    {p q : M × N} : p ≼ q ↔ p.1 ≼ q.1 ∧ p.2 ≼ q.2 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c.1, hc.1, rfl⟩, ⟨c.2, hc.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁, e₁⟩, ⟨c₂, h₂, e₂⟩⟩
    exact ⟨(c₁, c₂), ⟨h₁, h₂⟩, Prod.ext_iff.mpr ⟨e₁, e₂⟩⟩

/-- The product of two effect monoids, with componentwise multiplication
(needed for 195V.2). -/
instance prodEffectMonoid (M N : Type u) [EffectMonoid M] [EffectMonoid N] :
    EffectMonoid (M × N) :=
  { prodEffectAlgebra M N with
    mul := fun p q => (p.1 * q.1, p.2 * q.2)
    one_mul := fun a => by
      show ((1 : M) * a.1, (1 : N) * a.2) = a
      rw [EffectMonoid.one_mul, EffectMonoid.one_mul]
    mul_one := fun a => by
      show (a.1 * (1 : M), a.2 * (1 : N)) = a
      rw [EffectMonoid.mul_one, EffectMonoid.mul_one]
    mul_assoc := fun a b c => by
      show (a.1 * b.1 * c.1, a.2 * b.2 * c.2) = (a.1 * (b.1 * c.1), a.2 * (b.2 * c.2))
      rw [EffectMonoid.mul_assoc, EffectMonoid.mul_assoc]
    distrib := by
      intro a b c d hab hcd
      exact isSumOf_prod (l := [(a.1 * c.1, a.2 * c.2), (b.1 * c.1, b.2 * c.2),
          (a.1 * d.1, a.2 * d.2), (b.1 * d.1, b.2 * d.2)])
        (EffectMonoid.distrib hab.1 hcd.1) (EffectMonoid.distrib hab.2 hcd.2) }

/-- **195V.2** (eff.tex:3249, Examples): the product of two effect divisoids
is an effect divisoid, with componentwise division (in particular `[0,1]ⁿ`
is an effect divisoid). -/
instance prodEffectDivisoid (M N : Type u) [EffectMonoid M] [EffectMonoid N]
    [EffectDivisoid M] [EffectDivisoid N] : EffectDivisoid (M × N) where
  div p q := (div p.1 q.1, div p.2 q.2)
  div_le h :=
    prod_le_iff.mpr ⟨EffectDivisoid.div_le (prod_le_iff.mp h).1,
      EffectDivisoid.div_le (prod_le_iff.mp h).2⟩
  mul_div := fun {p q} h => by
    show (q.1 * div p.1 q.1, q.2 * div p.2 q.2) = p
    rw [EffectDivisoid.mul_div (prod_le_iff.mp h).1,
      EffectDivisoid.mul_div (prod_le_iff.mp h).2]
  div_unique := fun {p q r} hpq hr hmul => by
    show r = (div p.1 q.1, div p.2 q.2)
    rw [← EffectDivisoid.div_unique (prod_le_iff.mp hpq).1 (prod_le_iff.mp hr).1
        (congrArg Prod.fst hmul),
      ← EffectDivisoid.div_unique (prod_le_iff.mp hpq).2 (prod_le_iff.mp hr).2
        (congrArg Prod.snd hmul)]
  le_div_self p :=
    prod_le_iff.mpr ⟨EffectDivisoid.le_div_self p.1, EffectDivisoid.le_div_self p.2⟩
  div_div_self p := by
    show (div (div p.1 p.1) (div p.1 p.1), div (div p.2 p.2) (div p.2 p.2))
        = (div p.1 p.1, div p.2 p.2)
    rw [EffectDivisoid.div_div_self, EffectDivisoid.div_div_self]

/-! ### Helpers for the unit interval of `C(X, ℝ)` (195VI) -/

section ContinuousIcc

variable {X : Type u} [TopologicalSpace X]

/-- The order of `C(X, ℝ)` is the pointwise one (introduction). -/
theorem cont_le_of_forall {f g : C(X, ℝ)} (h : ∀ x, f x ≤ g x) : f ≤ g := h

/-- The order of `C(X, ℝ)` is the pointwise one (elimination). -/
theorem cont_apply_le {f g : C(X, ℝ)} (h : f ≤ g) (x : X) : f x ≤ g x := h x

/-- Membership in `[0,1]_{C(X)}`, pointwise. -/
theorem cIcc_mem {g : C(X, ℝ)} (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) :
    g ∈ Set.Icc (0 : C(X, ℝ)) 1 :=
  ⟨cont_le_of_forall h0, cont_le_of_forall h1⟩

/-- An element of `[0,1]_{C(X)}` is pointwise nonnegative. -/
theorem cIcc_nonneg (f : Set.Icc (0 : C(X, ℝ)) 1) (x : X) : 0 ≤ (f : C(X, ℝ)) x :=
  cont_apply_le f.2.1 x

/-- An element of `[0,1]_{C(X)}` is pointwise at most `1`. -/
theorem cIcc_le_one (f : Set.Icc (0 : C(X, ℝ)) 1) (x : X) : (f : C(X, ℝ)) x ≤ 1 :=
  cont_apply_le f.2.2 x

/-- Pointwise introduction of the orthogonality relation of `[0,1]_{C(X)}`. -/
theorem cIcc_perp_of {f g : Set.Icc (0 : C(X, ℝ)) 1}
    (h : ∀ x, (f : C(X, ℝ)) x + (g : C(X, ℝ)) x ≤ 1) : (f : C(X, ℝ)) + g ≤ 1 :=
  cont_le_of_forall h

/-- Pointwise elimination of the orthogonality relation of `[0,1]_{C(X)}`. -/
theorem cIcc_perp_apply {f g : Set.Icc (0 : C(X, ℝ)) 1}
    (h : (f : C(X, ℝ)) + g ≤ 1) (x : X) :
    (f : C(X, ℝ)) x + (g : C(X, ℝ)) x ≤ 1 := cont_apply_le h x

end ContinuousIcc

/-- The effect monoid on the unit interval `[0,1]_{C(X)}` of the continuous
real functions on a topological space `X` (needed for 195VI). -/
noncomputable def continuousUnitIntervalEffectMonoid (X : Type u)
    [TopologicalSpace X] : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1) where
  zero := ⟨0, cIcc_mem (fun _ => le_refl 0) (fun _ => zero_le_one)⟩
  one := ⟨1, cIcc_mem (fun _ => zero_le_one) (fun _ => le_refl 1)⟩
  Perp f g := (f : C(X, ℝ)) + g ≤ 1
  ovee f g h := ⟨(f : C(X, ℝ)) + g,
    cIcc_mem (fun x => add_nonneg (cIcc_nonneg f x) (cIcc_nonneg g x))
      (fun x => cIcc_perp_apply h x)⟩
  orth f := ⟨1 - (f : C(X, ℝ)),
    cIcc_mem (fun x => by
        have := cIcc_le_one f x
        show (0 : ℝ) ≤ 1 - (f : C(X, ℝ)) x
        linarith)
      (fun x => by
        have := cIcc_nonneg f x
        show (1 : ℝ) - (f : C(X, ℝ)) x ≤ 1
        linarith)⟩
  mul f g := ⟨(f : C(X, ℝ)) * g,
    cIcc_mem (fun x => mul_nonneg (cIcc_nonneg f x) (cIcc_nonneg g x))
      (fun x => by
        show (f : C(X, ℝ)) x * (g : C(X, ℝ)) x ≤ 1
        nlinarith [cIcc_nonneg f x, cIcc_le_one f x, cIcc_nonneg g x,
          cIcc_le_one g x])⟩
  perp_comm := fun {a b} h => cIcc_perp_of fun x => by
    have h1 : (a : C(X, ℝ)) x + (b : C(X, ℝ)) x ≤ 1 := cIcc_perp_apply h x
    show (b : C(X, ℝ)) x + (a : C(X, ℝ)) x ≤ 1
    linarith
  ovee_comm := fun _ => Subtype.ext (add_comm _ _)
  perp_of_ovee_perp := fun {a b c} hab h => cIcc_perp_of fun x => by
    have h1 : (a : C(X, ℝ)) x + (b : C(X, ℝ)) x + (c : C(X, ℝ)) x ≤ 1 :=
      cIcc_perp_apply h x
    have h2 := cIcc_nonneg a x
    show (b : C(X, ℝ)) x + (c : C(X, ℝ)) x ≤ 1
    linarith
  perp_ovee_of_ovee_perp := fun {a b c} hab h => cIcc_perp_of fun x => by
    have h1 : (a : C(X, ℝ)) x + (b : C(X, ℝ)) x + (c : C(X, ℝ)) x ≤ 1 :=
      cIcc_perp_apply h x
    show (a : C(X, ℝ)) x + ((b : C(X, ℝ)) x + (c : C(X, ℝ)) x) ≤ 1
    linarith
  ovee_assoc := fun {a b c} hab h => Subtype.ext (by
    show (a : C(X, ℝ)) + (b : C(X, ℝ)) + (c : C(X, ℝ))
        = (a : C(X, ℝ)) + ((b : C(X, ℝ)) + (c : C(X, ℝ)))
    ring)
  zero_perp := fun a => cIcc_perp_of fun x => by
    have := cIcc_le_one a x
    show (0 : ℝ) + (a : C(X, ℝ)) x ≤ 1
    linarith
  zero_ovee := fun a => Subtype.ext (by
    show (0 : C(X, ℝ)) + (a : C(X, ℝ)) = (a : C(X, ℝ))
    ring)
  perp_orth := fun a => cIcc_perp_of fun x => by
    show (a : C(X, ℝ)) x + (1 - (a : C(X, ℝ)) x) ≤ 1
    linarith
  ovee_orth := fun a => Subtype.ext (by
    show (a : C(X, ℝ)) + (1 - (a : C(X, ℝ))) = (1 : C(X, ℝ))
    ring)
  orth_unique := fun {a b} h h1 => Subtype.ext (by
    have hv : (a : C(X, ℝ)) + (b : C(X, ℝ)) = (1 : C(X, ℝ)) :=
      congrArg Subtype.val h1
    show (b : C(X, ℝ)) = 1 - (a : C(X, ℝ))
    exact eq_sub_of_add_eq' hv)
  eq_zero_of_perp_one := fun {a} h => Subtype.ext (by
    have h1 : ∀ x, (a : C(X, ℝ)) x + 1 ≤ 1 := fun x => cIcc_perp_apply h x
    ext x
    have h2 := cIcc_nonneg a x
    have h3 := h1 x
    show (a : C(X, ℝ)) x = 0
    linarith)
  one_mul := fun a => Subtype.ext (by
    show (1 : C(X, ℝ)) * (a : C(X, ℝ)) = (a : C(X, ℝ))
    ring)
  mul_one := fun a => Subtype.ext (by
    show (a : C(X, ℝ)) * (1 : C(X, ℝ)) = (a : C(X, ℝ))
    ring)
  mul_assoc := fun a b c => Subtype.ext (by
    show (a : C(X, ℝ)) * (b : C(X, ℝ)) * (c : C(X, ℝ))
        = (a : C(X, ℝ)) * ((b : C(X, ℝ)) * (c : C(X, ℝ)))
    ring)
  distrib := by
    intro a b c d hab hcd
    refine @isSumOf_four _ ?inst _ _ _ _ _ ?_ ?_ ?_ ?_
    · refine cIcc_perp_of fun x => ?_
      show (a : C(X, ℝ)) x * (c : C(X, ℝ)) x + (b : C(X, ℝ)) x * (c : C(X, ℝ)) x ≤ 1
      nlinarith [cIcc_perp_apply hab x, cIcc_nonneg a x, cIcc_nonneg b x,
        cIcc_nonneg c x, cIcc_le_one c x]
    · refine cIcc_perp_of fun x => ?_
      show (a : C(X, ℝ)) x * (d : C(X, ℝ)) x + (b : C(X, ℝ)) x * (d : C(X, ℝ)) x ≤ 1
      nlinarith [cIcc_perp_apply hab x, cIcc_nonneg a x, cIcc_nonneg b x,
        cIcc_nonneg d x, cIcc_le_one d x]
    · refine cIcc_perp_of fun x => ?_
      show (a : C(X, ℝ)) x * (c : C(X, ℝ)) x + (b : C(X, ℝ)) x * (c : C(X, ℝ)) x
          + ((a : C(X, ℝ)) x * (d : C(X, ℝ)) x + (b : C(X, ℝ)) x * (d : C(X, ℝ)) x)
          ≤ 1
      nlinarith [cIcc_perp_apply hab x, cIcc_perp_apply hcd x, cIcc_nonneg a x,
        cIcc_nonneg b x, cIcc_nonneg c x, cIcc_nonneg d x]
    · refine Subtype.ext ?_
      show (a : C(X, ℝ)) * (c : C(X, ℝ)) + (b : C(X, ℝ)) * (c : C(X, ℝ))
          + ((a : C(X, ℝ)) * (d : C(X, ℝ)) + (b : C(X, ℝ)) * (d : C(X, ℝ)))
          = ((a : C(X, ℝ)) + (b : C(X, ℝ))) * ((c : C(X, ℝ)) + (d : C(X, ℝ)))
      ring

/-- A topological space is **basically disconnected** when the closure of
the support of every continuous real function is open (195VI). -/
def BasicallyDisconnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(X, ℝ), IsOpen (closure (Function.support f))

/-- **195VI** (`basic-divisoid-equiv`, eff.tex:3275, Exercise\*): for a
compact Hausdorff space `X`, the unit interval of `C(X)` is an effect
divisoid if and only if `X` is basically disconnected (equivalently, `C(X)`
is σ-Dedekind complete).  In particular the unit interval of `C[0,1]` is
*not* an effect divisoid, while that of `L^∞[0,1]` is. -/
theorem basic_divisoid_equiv (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] :
    letI := continuousUnitIntervalEffectMonoid X
    (Nonempty (EffectDivisoid (Set.Icc (0 : C(X, ℝ)) 1)) ↔
      BasicallyDisconnected X) := sorry

/-- **195VII** (eff.tex:3328, Proposition): if `a ⊥ b` and `a ⋁ b ≼ c` in an
effect divisoid, then `(a ⋁ b)/c = a/c ⋁ b/c`. -/
theorem divisoid_div_ovee {M : Type u} [EffectMonoid M] [EffectDivisoid M]
    {a b c : M} (hab : Perp a b) (hc : ovee a b hab ≼ c) :
    ∃ h' : Perp (div a c) (div b c),
      div (ovee a b hab) c = ovee (div a c) (div b c) h' := by
  -- Write `s = a ⋁ b`.  The key step is that `a/s ⊥ b/s` with
  -- `a/s ⋁ b/s = s/s`: a complement `w` of `a/s` below `s/s` satisfies
  -- `s ⊙ w = b`, hence *is* `b/s` by uniqueness of the division.
  set s := ovee a b hab with hs
  have has : a ≼ s := ⟨b, hab, hs.symm⟩
  have hbs : b ≼ s := ⟨a, PCM.perp_comm hab, by
    rw [← PCM.ovee_comm hab]⟩
  have hss : s * div s s = s := EffectDivisoid.mul_div (pcm_preorder_refl s)
  obtain ⟨w, hw, hwe⟩ := EffectDivisoid.div_le has
  obtain ⟨h₂, e₂⟩ := emon_mul_ovee s hw
  rw [hwe, hss] at e₂
  have hsu : s * div a s = a := EffectDivisoid.mul_div has
  have hpa : Perp a (s * w) := by rw [← hsu]; exact h₂
  have e₂' : ovee a (s * w) hpa = ovee a b hab :=
    ((PCM.ovee_congr hsu rfl h₂ hpa).symm.trans e₂.symm).trans hs
  have e₂'' : ovee (s * w) a (PCM.perp_comm hpa)
      = ovee b a (PCM.perp_comm hab) := by
    rw [← PCM.ovee_comm hpa, ← PCM.ovee_comm hab]
    exact e₂'
  have hswb : s * w = b :=
    eabasics_cancellation (PCM.perp_comm hpa) (PCM.perp_comm hab) e₂''
  have hwle : w ≼ div s s := ⟨div a s, PCM.perp_comm hw, by
    rw [← PCM.ovee_comm hw]; exact hwe⟩
  have hwv : w = div b s := EffectDivisoid.div_unique hbs hwle hswb
  have hw' : Perp (div a s) (div b s) := by rw [← hwv]; exact hw
  have hovee_uv : ovee (div a s) (div b s) hw' = div s s := by
    rw [← PCM.ovee_congr rfl hwv hw hw']
    exact hwe
  -- now divide by `c`, using `(b/c) ⊙ (a/b) = a/c` three times
  have hEu : div s c * div a s = div a c := exc_divisoid_basics_2 has hc
  have hEv : div s c * div b s = div b c := exc_divisoid_basics_2 hbs hc
  have hEs : div s c * div s s = div s c :=
    exc_divisoid_basics_2 (pcm_preorder_refl s) hc
  obtain ⟨h₃, e₃⟩ := emon_mul_ovee (div s c) hw'
  rw [hovee_uv, hEs] at e₃
  have h' : Perp (div a c) (div b c) := by rw [← hEu, ← hEv]; exact h₃
  refine ⟨h', ?_⟩
  rw [e₃]
  exact PCM.ovee_congr hEu hEv h₃ h'

/-! ## `AConv_M` is an effectus for an effect divisoid `M` (parsec 196) -/

/-! ### Machinery for 196II: binary mixtures `λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩`

The proof of 196II below needs to compute with the elements of `X + Y`.  The
thesis does this with the *derivations* of 193IX/193IV, which are not
formalized; instead we show (`AConvMCat.exists_mix`) that over an effect
divisoid **every** element of `X + Y` is already a *binary* mixture
`λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩`, which is what the divisoid buys and all that 196II uses.
The lemmas below build up to that. -/

namespace MConvexComb

variable {M : Type u} [EffectMonoid M]

open Classical in
/-- The values of the binary combination `bin l x y` when `x ≠ y`. -/
theorem bin_apply {X : Type v} (l : M) {x y : X} (hxy : x ≠ y) (z : X) :
    (bin l x y).toFun z = if z = x then l else if z = y then orth l else 0 := by
  show (if x = y then (if z = x then (1 : M) else 0)
    else if z = x then l else if z = y then orth l else 0) = _
  rw [if_neg hxy]

open Classical in
/-- `bin l x x = η x`. -/
theorem bin_self {X : Type v} (l : M) (x : X) : bin l x x = eta x := by
  refine MConvexComb.ext (funext fun z => ?_)
  show (if x = x then (if z = x then (1 : M) else 0)
    else if z = x then l else if z = x then orth l else 0) = _
  rw [if_pos rfl]
  rfl

open Classical in
/-- The support of `bin l x y` is contained in `{x, y}`. -/
theorem bin_eq_zero {X : Type v} (l : M) (x y z : X) (hzx : z ≠ x) (hzy : z ≠ y) :
    (bin l x y).toFun z = 0 := by
  by_cases hxy : x = y
  · subst hxy
    rw [bin_self]
    show (if z = x then (1 : M) else 0) = 0
    rw [if_neg hzx]
  · rw [bin_apply l hxy z, if_neg hzx, if_neg hzy]

open Classical in
/-- `bin 1 a b = η a`. -/
theorem bin_one {X : Type v} (a b : X) : bin (1 : M) a b = eta a := by
  by_cases hab : a = b
  · subst hab; exact bin_self 1 a
  refine MConvexComb.ext (funext fun z => ?_)
  rw [bin_apply (1 : M) hab z, eabasics_orth_one]
  show _ = if z = a then (1 : M) else 0
  by_cases hz : z = a
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    by_cases hz2 : z = b
    · rw [if_pos hz2]
    · rw [if_neg hz2]

open Classical in
/-- `bin 0 a b = η b`. -/
theorem bin_zero {X : Type v} (a b : X) : bin (0 : M) a b = eta b := by
  by_cases hab : a = b
  · subst hab; exact bin_self 0 a
  refine MConvexComb.ext (funext fun z => ?_)
  rw [bin_apply (0 : M) hab z, eabasics_orth_zero]
  show _ = if z = b then (1 : M) else 0
  by_cases hz : z = a
  · rw [if_pos hz, if_neg (by rw [hz]; exact hab)]
  · rw [if_neg hz]

/-- Variant of `map_spec`: the value of `𝒟_M f (p)` at `y` may be computed
over any repetition-free list of elements of the fibre of `y` containing the
whole support of `p` in that fibre. -/
theorem map_spec_of_list {X : Type v} {Y : Type w} (p : MConvexComb M X)
    (f : X → Y) (y : Y) (L : List X) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, f x = y)
    (hsupp : ∀ x, p.toFun x ≠ 0 → f x = y → x ∈ L) :
    PCM.IsSumOf (L.map p.toFun) ((p.map f).toFun y) := by
  classical
  have hmem' : ∀ x, x ∈ L.filter (fun x => decide (p.toFun x ≠ 0)) ↔
      (p.toFun x ≠ 0 ∧ f x = y) := by
    intro x
    rw [List.mem_filter]
    simp only [decide_eq_true_eq]
    exact ⟨fun h => ⟨h.2, hL x h.1⟩, fun h => ⟨hsupp x h.1 h.2, h.1⟩⟩
  have h1 := map_spec p f y _ (List.Nodup.filter _ hnd) hmem'
  refine isSumOf_map_of_subset p.toFun (List.Nodup.filter _ hnd) hnd
    (fun x hx => List.mem_of_mem_filter hx) (fun x hx hnx => ?_) h1
  by_contra h0
  exact hnx (List.mem_filter.mpr ⟨hx, by simpa using h0⟩)

open Classical in
/-- The pushforward of a binary combination is a binary combination. -/
theorem map_bin {X : Type v} {Y : Type w} (l : M) (x y : X) (f : X → Y) :
    (bin l x y).map f = bin l (f x) (f y) := by
  by_cases hxy : x = y
  · subst hxy
    rw [bin_self, map_eta, bin_self]
  have hvx : (bin l x y).toFun x = l := by rw [bin_apply l hxy, if_pos rfl]
  have hvy : (bin l x y).toFun y = orth l := by
    rw [bin_apply l hxy, if_neg (fun h : y = x => hxy h.symm), if_pos rfl]
  refine MConvexComb.ext (funext fun z => ?_)
  by_cases hfxy : f x = f y
  · -- both coefficients land on the same point of `Y`
    have hR : bin l (f x) (f y) = (eta (f x) : MConvexComb M Y) := by
      rw [← hfxy, bin_self]
    rw [hR]
    by_cases hz : z = f x
    · subst hz
      have h := map_spec_of_list (bin l x y) f (f x) [x, y] (by simp [hxy])
        (fun w hw => by
          rcases List.mem_cons.mp hw with rfl | hw
          · rfl
          · rw [List.mem_singleton.mp hw]; exact hfxy.symm)
        (fun w hw _ => by
          by_cases hwx : w = x
          · exact List.mem_cons.mpr (Or.inl hwx)
          by_cases hwy : w = y
          · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr hwy))
          · exact absurd (bin_eq_zero l x y w hwx hwy) hw)
      rw [List.map_cons, List.map_cons, List.map_nil, hvx, hvy] at h
      have h2 := isSumOf_pair l (orth l) (EffectAlgebra.perp_orth l)
      rw [EffectAlgebra.ovee_orth l] at h2
      rw [isSumOf_unique h h2]
      show (1 : M) = if f x = f x then (1 : M) else 0
      rw [if_pos rfl]
    · have h := map_spec_of_list (bin l x y) f z [] List.nodup_nil
        (fun w hw => absurd hw (List.not_mem_nil))
        (fun w hw hfw => by
          by_cases hwx : w = x
          · subst hwx; exact absurd hfw.symm hz
          by_cases hwy : w = y
          · subst hwy; exact absurd (hfxy.trans hfw).symm hz
          · exact absurd (bin_eq_zero l x y w hwx hwy) hw)
      rw [List.map_nil, PCM.isSumOf_nil_iff] at h
      rw [h]
      show (0 : M) = if z = f x then (1 : M) else 0
      rw [if_neg hz]
  · rw [bin_apply l hfxy z]
    by_cases hz : z = f x
    · subst hz
      have h := map_spec_of_list (bin l x y) f (f x) [x] (List.nodup_singleton x)
        (fun w hw => by rw [List.mem_singleton.mp hw])
        (fun w hw hfw => by
          by_cases hwx : w = x
          · exact List.mem_singleton.mpr hwx
          by_cases hwy : w = y
          · exact absurd ((hwy ▸ hfw : f y = f x)) (fun hh => hfxy hh.symm)
          · exact absurd (bin_eq_zero l x y w hwx hwy) hw)
      rw [List.map_cons, List.map_nil, hvx] at h
      rw [eq_of_isSumOf_singleton h, if_pos rfl]
    · by_cases hz2 : z = f y
      · subst hz2
        have h := map_spec_of_list (bin l x y) f (f y) [y] (List.nodup_singleton y)
          (fun w hw => by rw [List.mem_singleton.mp hw])
          (fun w hw hfw => by
            by_cases hwy : w = y
            · exact List.mem_singleton.mpr hwy
            by_cases hwx : w = x
            · exact absurd ((hwx ▸ hfw : f x = f y)) hfxy
            · exact absurd (bin_eq_zero l x y w hwx hwy) hw)
        rw [List.map_cons, List.map_nil, hvy] at h
        rw [eq_of_isSumOf_singleton h, if_neg hz, if_pos rfl]
      · have h := map_spec_of_list (bin l x y) f z [] List.nodup_nil
          (fun w hw => absurd hw (List.not_mem_nil))
          (fun w hw hfw => by
            by_cases hwx : w = x
            · exact absurd (hwx ▸ hfw : f x = z) (fun hh => hz hh.symm)
            by_cases hwy : w = y
            · exact absurd (hwy ▸ hfw : f y = z) (fun hh => hz2 hh.symm)
            · exact absurd (bin_eq_zero l x y w hwx hwy) hw)
        rw [List.map_nil, PCM.isSumOf_nil_iff] at h
        rw [h, if_neg hz, if_neg hz2]

/-- Variant of `mu_spec`: the value of `μ(Φ)` may be computed over any
repetition-free list containing the support of `Φ`. -/
theorem mu_spec_of_subset {X : Type v} (Φ : MConvexComb M (MConvexComb M X))
    (x : X) (l : List (MConvexComb M X)) (hnd : l.Nodup)
    (hsupp : ∀ φ, Φ.toFun φ ≠ 0 → φ ∈ l) :
    PCM.IsSumOf (l.map fun φ => Φ.toFun φ * φ.toFun x) ((mu Φ).toFun x) := by
  classical
  obtain ⟨L, hndL, hmemL, -⟩ := Φ.sum_one
  refine isSumOf_map_of_support _ hndL hnd ?_ ?_ (mu_spec Φ x L hndL hmemL)
  · intro φ hφ
    refine (hmemL φ).mpr fun h0 => hφ ?_
    show Φ.toFun φ * φ.toFun x = 0
    rw [h0, (exc_emonzero (φ.toFun x)).2]
  · intro φ hφ
    refine hsupp φ fun h0 => hφ ?_
    show Φ.toFun φ * φ.toFun x = 0
    rw [h0, (exc_emonzero (φ.toFun x)).2]

open Classical in
/-- `μ` of a binary combination of two distributions is their `λ`-mixture. -/
theorem mu_bin {X : Type v} (l : M) (P Q : MConvexComb M X) (x : X) :
    PCM.IsSumOf [l * P.toFun x, orth l * Q.toFun x] ((mu (bin l P Q)).toFun x) := by
  by_cases hPQ : P = Q
  · subst hPQ
    rw [bin_self, mu_eta]
    obtain ⟨h', he⟩ := emon_ovee_mul (P.toFun x) (EffectAlgebra.perp_orth l)
    rw [EffectAlgebra.ovee_orth l, EffectMonoid.one_mul] at he
    have hp2 := isSumOf_pair (l * P.toFun x) (orth l * P.toFun x) h'
    rwa [← he] at hp2
  · have h := mu_spec_of_subset (bin l P Q) x [P, Q] (by simp [hPQ]) (fun φ hφ => by
      by_cases hP : φ = P
      · exact List.mem_cons.mpr (Or.inl hP)
      by_cases hQ : φ = Q
      · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr hQ))
      · exact absurd (bin_eq_zero l P Q φ hP hQ) hφ)
    rw [List.map_cons, List.map_cons, List.map_nil, bin_apply l hPQ P, if_pos rfl,
      bin_apply l hPQ Q, if_neg (fun hh : Q = P => hPQ hh.symm), if_pos rfl] at h
    exact h

/-- A formal combination over `A + B` that vanishes on `A` is `𝒟_M κ₂` of a
formal combination over `B` (the mirror image of `exists_map_inl`). -/
theorem exists_map_inr {A B : Type v} (p : MConvexComb M (A ⊕ B))
    (h : ∀ a : A, p.toFun (Sum.inl a) = 0) :
    ∃ ψ : MConvexComb M B, ψ.map Sum.inr = p := by
  have hval : ∀ a : A, (p.map Sum.swap).toFun (Sum.inr a) = 0 := by
    intro a
    rw [MConvexComb.map_apply_of_unique_fiber p Sum.swap
      (x₀ := Sum.inl a) (fun w => by rcases w with b | b <;> simp)]
    exact h a
  obtain ⟨χ, hχ⟩ := MConvexComb.exists_map_inl (p.map Sum.swap) hval
  refine ⟨χ, ?_⟩
  have h2 : (χ.map (Sum.inl : B → B ⊕ A)).map Sum.swap = (p.map Sum.swap).map Sum.swap := by
    rw [hχ]
  rw [MConvexComb.map_comp, MConvexComb.map_comp] at h2
  have h3 : (Sum.swap ∘ (Sum.inl : B → B ⊕ A)) = (Sum.inr : B → A ⊕ B) := rfl
  have h4 : (Sum.swap ∘ (Sum.swap : A ⊕ B → B ⊕ A)) = id := by
    funext w; rcases w with a | b <;> rfl
  rw [h3, h4, MConvexComb.map_id] at h2
  exact h2

end MConvexComb

section Divisoid

variable {M : Type u} [EffectMonoid M] [EffectDivisoid M]

/-- `0/c = 0`. -/
theorem div_zero_left (c : M) : div (0 : M) c = 0 :=
  (EffectDivisoid.div_unique (pcm_zero_le c) (pcm_zero_le _)
    (exc_emonzero c).1).symm

/-- Division by a fixed `c` preserves finite partial sums (the `n`-ary form
of 195VII). -/
theorem isSumOf_div : ∀ {l : List M} {s : M}, PCM.IsSumOf l s → ∀ {c : M}, s ≼ c →
    PCM.IsSumOf (l.map (fun a => div a c)) (div s c) := by
  intro l s h
  induction h with
  | nil =>
      intro c _
      rw [List.map_nil, div_zero_left c]
      exact PCM.IsSumOf.nil
  | @cons a l t hl hp ih =>
      intro c hsc
      have hac : a ≼ c := pcm_preorder_trans ⟨t, hp, rfl⟩ hsc
      have htc : t ≼ c :=
        pcm_preorder_trans ⟨a, PCM.perp_comm hp, (PCM.ovee_comm hp).symm⟩ hsc
      obtain ⟨h', he⟩ := divisoid_div_ovee hp hsc
      rw [List.map_cons, he]
      exact PCM.IsSumOf.cons (ih htc) h'

open Classical in
/-- **The normalization lemma for effect divisoids**: a finitely supported
family `f : A → M` whose values sum to `l` is `l ⊙ (–)` of a formal convex
combination `χ`.  The naive `χ(a) = f(a)/l` sums to `l/l`, which need not be
`1`; the deficit `(l/l)ᵖ` is put at a chosen point `a₀` (this is the thesis's
correction term `r` in the proof of 196II), and it is invisible after
multiplying by `l` because `l ⊙ (l/l)ᵖ = 0`. -/
theorem MConvexComb.exists_of_div {A : Type v} (f : A → M) (a₀ : A) (l : M)
    (L : List A) (hnd : L.Nodup) (hsupp : ∀ a, f a ≠ 0 → a ∈ L)
    (hsum : PCM.IsSumOf (L.map f) l) :
    ∃ χ : MConvexComb M A, ∀ a, l * χ.toFun a = f a := by
  classical
  have hle : ∀ a, f a ≼ l := fun a => by
    by_cases ha : f a = 0
    · rw [ha]; exact pcm_zero_le l
    · exact isSumOf_le_of_mem (List.mem_map_of_mem (hsupp a ha)) hsum
  let e : M := div l l
  let d : A → M := fun a => div (f a) l
  have hdle : ∀ a, d a ≼ e := fun a => EffectDivisoid.div_le (hle a)
  have hperp : Perp (d a₀) (orth e) :=
    eabasics_perp_iff_le_orth.mpr (by rw [eabasics_orth_orth]; exact hdle a₀)
  let u : A → M := fun a => if a = a₀ then ovee (d a₀) (orth e) hperp else d a
  have hu₀ : u a₀ = ovee (d a₀) (orth e) hperp := if_pos rfl
  have hune : ∀ a, a ≠ a₀ → u a = d a := fun a h => if_neg h
  -- the divided family sums to `e = l/l`
  have hde : PCM.IsSumOf (L.map d) e := by
    have h := isSumOf_div hsum (pcm_preorder_refl l)
    rwa [List.map_map] at h
  -- split off `a₀`
  have hndR : (L.erase a₀).Nodup := List.Nodup.erase _ hnd
  have hnotmem : a₀ ∉ L.erase a₀ := List.Nodup.not_mem_erase hnd
  obtain ⟨t, hRt, hpt, hovt⟩ : ∃ t, PCM.IsSumOf ((L.erase a₀).map d) t ∧
      ∃ hp : Perp (d a₀) t, ovee (d a₀) t hp = e := by
    by_cases hmem : a₀ ∈ L
    · have h2 := PCM.isSumOf_perm (List.Perm.map d (List.perm_cons_erase hmem)) hde
      rw [List.map_cons] at h2
      obtain ⟨t, ht, hp, he⟩ := PCM.isSumOf_cons_iff.mp h2
      exact ⟨t, ht, hp, he⟩
    · have hd0 : d a₀ = 0 := by
        show div (f a₀) l = 0
        rw [show f a₀ = 0 from by by_contra h0; exact hmem (hsupp a₀ h0), div_zero_left]
      refine ⟨e, by rw [List.erase_of_not_mem hmem]; exact hde, ?_⟩
      rw [hd0]
      exact ⟨PCM.zero_perp e, PCM.zero_ovee' e _⟩
  -- reassociate `(d a₀ ⋁ t) ⋁ eᵖ = 1` into `(d a₀ ⋁ eᵖ) ⋁ t = 1`
  have hpe : Perp (orth e) (ovee (d a₀) t hpt) := by
    rw [hovt]; exact PCM.perp_comm (EffectAlgebra.perp_orth e)
  obtain ⟨hpo, hpo2, heq⟩ := PCM.assoc_left hpt hpe
  have hone : ovee (orth e) (ovee (d a₀) t hpt) hpe = 1 := by
    rw [PCM.ovee_congr rfl hovt hpe
      (show Perp (orth e) e from PCM.perp_comm (EffectAlgebra.perp_orth e)),
      PCM.ovee_comm]
    exact EffectAlgebra.ovee_orth e
  have hua : u a₀ = ovee (orth e) (d a₀) hpo := by
    rw [hu₀, PCM.ovee_comm hperp]
  have hpu : Perp (u a₀) t := by rw [hua]; exact hpo2
  have hval : ovee (u a₀) t hpu = 1 := by
    rw [PCM.ovee_congr hua rfl hpu hpo2, heq, hone]
  have hsumT : PCM.IsSumOf ((a₀ :: L.erase a₀).map u) 1 := by
    rw [List.map_cons,
      show (L.erase a₀).map u = (L.erase a₀).map d from
        List.map_congr_left (fun a ha => hune a (fun h => hnotmem (h ▸ ha))),
      ← hval]
    exact PCM.IsSumOf.cons hRt hpu
  have hndT : (a₀ :: L.erase a₀).Nodup := List.nodup_cons.mpr ⟨hnotmem, hndR⟩
  have husupp : ∀ a, u a ≠ 0 → a ∈ a₀ :: L.erase a₀ := by
    intro a ha
    by_cases haa : a = a₀
    · exact List.mem_cons.mpr (Or.inl haa)
    · refine List.mem_cons.mpr (Or.inr ((List.Nodup.mem_erase_iff hnd).mpr ⟨haa, ?_⟩))
      refine hsupp a fun h0 => ha ?_
      rw [hune a haa]
      show div (f a) l = 0
      rw [h0, div_zero_left]
  refine ⟨⟨u, ⟨(a₀ :: L.erase a₀).filter (fun a => decide (u a ≠ 0)),
    List.Nodup.filter _ hndT, ?_, ?_⟩⟩, ?_⟩
  · intro a
    rw [List.mem_filter]
    exact ⟨fun h => by simpa using h.2, fun h => ⟨husupp a h, by simpa using h⟩⟩
  · exact (isSumOf_map_filter u _ (fun a _ h => by simpa using h)).mpr hsumT
  · intro a
    show l * u a = f a
    by_cases haa : a = a₀
    · subst haa
      rw [hu₀]
      obtain ⟨h', he'⟩ := emon_mul_ovee l hperp
      rw [he']
      have hld : l * d a = f a := EffectDivisoid.mul_div (hle a)
      have hlo : l * orth e = 0 := by
        obtain ⟨h2, he2⟩ := emon_mul_ovee l (EffectAlgebra.perp_orth e)
        rw [EffectAlgebra.ovee_orth e, EffectMonoid.mul_one] at he2
        have hself : l * e = l := EffectDivisoid.mul_div (pcm_preorder_refl l)
        have hA : ovee (l * orth e) (l * e) (PCM.perp_comm h2) = l := by
          rw [PCM.ovee_comm (PCM.perp_comm h2)]
          exact he2.symm
        have hB : ovee (0 : M) (l * e) (PCM.zero_perp _) = l := by
          rw [PCM.zero_ovee' (l * e) (PCM.zero_perp _)]
          exact hself
        exact eabasics_cancellation (PCM.perp_comm h2) (PCM.zero_perp _)
          (hA.trans hB.symm)
      rw [PCM.ovee_congr hld hlo h' (show Perp (f a) 0 from PCM.perp_zero _),
        PCM.ovee_zero]
    · rw [hune a haa]
      exact EffectDivisoid.mul_div (hle a)

end Divisoid

namespace MConvexComb

variable {M : Type u} [EffectMonoid M]

/-- `𝒟_M κ₂ (ψ)` vanishes on the left summand. -/
theorem map_inr_apply_inl {A B : Type v} (ψ : MConvexComb M B) (a : A) :
    (ψ.map (Sum.inr : B → A ⊕ B)).toFun (Sum.inl a) = 0 := by
  have h := map_spec_of_list ψ (Sum.inr : B → A ⊕ B) (Sum.inl a) []
    List.nodup_nil (fun w hw => absurd hw (List.not_mem_nil))
    (fun w _ hw => absurd hw (by simp))
  rw [List.map_nil, PCM.isSumOf_nil_iff] at h
  exact h

/-- `𝒟_M κ₁ (χ)` vanishes on the right summand. -/
theorem map_inl_apply_inr {A B : Type v} (χ : MConvexComb M A) (b : B) :
    (χ.map (Sum.inl : A → A ⊕ B)).toFun (Sum.inr b) = 0 := by
  have h := map_spec_of_list χ (Sum.inl : A → A ⊕ B) (Sum.inr b) []
    List.nodup_nil (fun w hw => absurd hw (List.not_mem_nil))
    (fun w _ hw => absurd hw (by simp))
  rw [List.map_nil, PCM.isSumOf_nil_iff] at h
  exact h

/-- On a two-element set the second coefficient is the orthosupplement of the
first. -/
theorem eq_orth_of_two {A : Type v} (p : MConvexComb M A) {a b : A}
    (hab : a ≠ b) (hall : ∀ z : A, z = a ∨ z = b) :
    p.toFun b = orth (p.toFun a) := by
  classical
  obtain ⟨L, hndL, hmemL, hsL⟩ := p.sum_one
  have hsum : PCM.IsSumOf (([a, b] : List A).map p.toFun) 1 :=
    isSumOf_map_of_support p.toFun hndL (by simp [hab])
      (fun x hx => (hmemL x).mpr hx)
      (fun x _ => by rcases hall x with rfl | rfl <;> simp) hsL
  rw [List.map_cons, List.map_cons, List.map_nil] at hsum
  obtain ⟨t, ht, hp, he⟩ := PCM.isSumOf_cons_iff.mp hsum
  have htb : t = p.toFun b := eq_of_isSumOf_singleton ht
  subst htb
  exact EffectAlgebra.orth_unique hp he

/-- The mass of the left summand: a repetition-free list of the left-hand
support, together with the fact that the corresponding values sum to the
`𝒟_M g`-mass of the left point. -/
theorem exists_left_sum {A B : Type v} {W : Type w} (p : MConvexComb M (A ⊕ B))
    (g : A ⊕ B → W) (w : W) (hgl : ∀ a : A, g (Sum.inl a) = w)
    (hgr : ∀ b : B, g (Sum.inr b) ≠ w) :
    ∃ LA : List A, LA.Nodup ∧ (∀ a, p.toFun (Sum.inl a) ≠ 0 → a ∈ LA) ∧
      PCM.IsSumOf (LA.map fun a => p.toFun (Sum.inl a)) ((p.map g).toFun w) := by
  classical
  obtain ⟨L, hnd, hmem, -⟩ := p.sum_one
  set L₁ : List (A ⊕ B) := L.filter (fun z => z.isLeft) with hL₁
  have hleft : ∀ z ∈ L₁, ∃ a : A, z = Sum.inl a := by
    intro z hz
    rcases z with a | b
    · exact ⟨a, rfl⟩
    · rw [hL₁, List.mem_filter] at hz
      exact absurd hz.2 (by simp)
  have hll : ∀ K : List (A ⊕ B), (∀ z ∈ K, ∃ a : A, z = Sum.inl a) →
      (K.filterMap Sum.getLeft?).map Sum.inl = K := by
    intro K
    induction K with
    | nil => intro _; rfl
    | cons z K ih =>
        intro hz
        obtain ⟨a, rfl⟩ := hz z List.mem_cons_self
        rw [List.filterMap_cons]
        simp only [Sum.getLeft?_inl, List.map_cons, List.cons.injEq, true_and]
        exact ih fun v hv => hz v (List.mem_cons_of_mem _ hv)
  have hmap : (L₁.filterMap Sum.getLeft?).map Sum.inl = L₁ := hll L₁ hleft
  have hnd₁ : L₁.Nodup := List.Nodup.filter _ hnd
  have hinj : Function.Injective (Sum.inl : A → A ⊕ B) := fun _ _ h => by simpa using h
  refine ⟨L₁.filterMap Sum.getLeft?, List.Nodup.of_map Sum.inl (hmap ▸ hnd₁),
    ?_, ?_⟩
  · intro a ha
    have h1 : Sum.inl a ∈ L₁ := by
      rw [hL₁, List.mem_filter]
      exact ⟨(hmem _).mpr ha, by simp⟩
    rw [← hmap] at h1
    obtain ⟨a', ha', he⟩ := List.mem_map.mp h1
    rwa [hinj he] at ha'
  · have h := map_spec_of_list p g w L₁ hnd₁
      (fun z hz => by obtain ⟨a, rfl⟩ := hleft z hz; exact hgl a)
      (fun z hz hgz => by
        rcases z with a | b
        · rw [hL₁, List.mem_filter]
          exact ⟨(hmem _).mpr hz, by simp⟩
        · exact absurd hgz (hgr b))
    rw [← hmap, List.map_map] at h
    exact h

/-- The mirror image of `exists_left_sum`. -/
theorem exists_right_sum {A B : Type v} {W : Type w} (p : MConvexComb M (A ⊕ B))
    (g : A ⊕ B → W) (w : W) (hgr : ∀ b : B, g (Sum.inr b) = w)
    (hgl : ∀ a : A, g (Sum.inl a) ≠ w) :
    ∃ LB : List B, LB.Nodup ∧ (∀ b, p.toFun (Sum.inr b) ≠ 0 → b ∈ LB) ∧
      PCM.IsSumOf (LB.map fun b => p.toFun (Sum.inr b)) ((p.map g).toFun w) := by
  have hswap : ∀ b : B, (p.map (Sum.swap : A ⊕ B → B ⊕ A)).toFun (Sum.inl b)
      = p.toFun (Sum.inr b) := fun b =>
    map_apply_of_unique_fiber p Sum.swap (x₀ := Sum.inr b)
      (fun z => by rcases z with a | b' <;> simp)
  obtain ⟨LB, hnd, hsupp, hsum⟩ := exists_left_sum (p.map (Sum.swap : A ⊕ B → B ⊕ A))
    (g ∘ (Sum.swap : B ⊕ A → A ⊕ B)) w (fun b => hgr b) (fun a => hgl a)
  refine ⟨LB, hnd, fun b hb => hsupp b (by rw [hswap b]; exact hb), ?_⟩
  have hcomp : (p.map (Sum.swap : A ⊕ B → B ⊕ A)).map (g ∘ (Sum.swap : B ⊕ A → A ⊕ B))
      = p.map g := by
    rw [map_comp]
    exact congrArg p.map (funext fun z => by rcases z with a | b <;> rfl)
  rw [hcomp] at hsum
  rw [show (LB.map fun b => p.toFun (Sum.inr b))
      = LB.map fun b => (p.map (Sum.swap : A ⊕ B → B ⊕ A)).toFun (Sum.inl b) from
    List.map_congr_left (fun b _ => (hswap b).symm)]
  exact hsum

end MConvexComb

/-! ## The `M × X × Y` picture of `X ⨿ Y` for an effect divisoid -/

namespace AConvMCat

variable {M : Type u} [EffectMonoid M]

/-- The constant map to `w : W` is affine (`𝒟_M` of a constant map is a
Dirac at its value). -/
noncomputable def constHom (Z W : AConvMCat.{u, v} M) (w : W.carrier) : Z ⟶ W :=
  ⟨fun _ => w, fun p => by rw [MConvexComb.map_const p w, W.str.h_eta]⟩

@[simp]
theorem comp_constHom {Z Z' W : AConvMCat.{u, v} M} (f : Z ⟶ Z') (w : W.carrier) :
    f ≫ constHom Z' W w = constHom Z W w := Subtype.ext rfl

/-- An affine map takes a binary mixture to a binary mixture. -/
theorem hom_apply_bin {Z W : AConvMCat.{u, v} M} (f : Z ⟶ W) (l : M)
    (a b : Z.carrier) :
    f.1 (Z.str.h (MConvexComb.bin l a b))
      = W.str.h (MConvexComb.bin l (f.1 a) (f.1 b)) := by
  rw [f.2 (MConvexComb.bin l a b), MConvexComb.map_bin]

section Mix

variable (X Y : AConvMCat.{u, max u v} M) [HasBinaryCoproduct X Y]

/-- The mixture `λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩ ∈ X ⨿ Y`. -/
noncomputable def mix (l : M) (x : X.carrier) (y : Y.carrier) : (X ⨿ Y).carrier :=
  (X ⨿ Y).str.h (MConvexComb.bin l ((coprod.inl : X ⟶ X ⨿ Y).1 x)
    ((coprod.inr : Y ⟶ X ⨿ Y).1 y))

/-- The mass map `X ⨿ Y ⟶ 𝒟_M(1+1)`: `κ₁x ↦ η(κ₁•)` and `κ₂y ↦ η(κ₂•)`. -/
noncomputable def massMap :
    X ⨿ Y ⟶ AConvMCat.free M (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) :=
  coprod.desc (constHom X _ (MConvexComb.eta (Sum.inl PUnit.unit)))
    (constHom Y _ (MConvexComb.eta (Sum.inr PUnit.unit)))

theorem massMap_inl :
    (coprod.inl : X ⟶ X ⨿ Y) ≫ massMap X Y
      = constHom X _ (MConvexComb.eta (Sum.inl PUnit.unit)) :=
  coprod.inl_desc _ _

theorem massMap_inr :
    (coprod.inr : Y ⟶ X ⨿ Y) ≫ massMap X Y
      = constHom Y _ (MConvexComb.eta (Sum.inr PUnit.unit)) :=
  coprod.inr_desc _ _

theorem massMap_inl_apply (x : X.carrier) :
    (massMap X Y).1 ((coprod.inl : X ⟶ X ⨿ Y).1 x)
      = MConvexComb.eta (Sum.inl PUnit.unit) :=
  congrArg (fun m : X ⟶ AConvMCat.free M
    (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 x) (massMap_inl X Y)

theorem massMap_inr_apply (y : Y.carrier) :
    (massMap X Y).1 ((coprod.inr : Y ⟶ X ⨿ Y).1 y)
      = MConvexComb.eta (Sum.inr PUnit.unit) :=
  congrArg (fun m : Y ⟶ AConvMCat.free M
    (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 y) (massMap_inr X Y)

/-- The mass of an element of `X ⨿ Y`: its `1+1`-coefficient at the left
point. -/
noncomputable def mass (w : (X ⨿ Y).carrier) : M :=
  ((massMap X Y).1 w).toFun (Sum.inl PUnit.unit)

theorem massMap_mix (l : M) (x : X.carrier) (y : Y.carrier) :
    (massMap X Y).1 (mix X Y l x y)
      = MConvexComb.bin l (Sum.inl PUnit.unit) (Sum.inr PUnit.unit) := by
  have h1 : (massMap X Y).1 ((coprod.inl : X ⟶ X ⨿ Y).1 x)
      = MConvexComb.eta (Sum.inl PUnit.unit) :=
    congrArg (fun m : X ⟶ AConvMCat.free M
      (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 x) (massMap_inl X Y)
  have h2 : (massMap X Y).1 ((coprod.inr : Y ⟶ X ⨿ Y).1 y)
      = MConvexComb.eta (Sum.inr PUnit.unit) :=
    congrArg (fun m : Y ⟶ AConvMCat.free M
      (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 y) (massMap_inr X Y)
  rw [mix, hom_apply_bin, h1, h2]
  show MConvexComb.mu (MConvexComb.bin l (MConvexComb.eta _) (MConvexComb.eta _)) = _
  rw [← MConvexComb.map_bin, MConvexComb.mu_map_eta]

theorem mass_mix (l : M) (x : X.carrier) (y : Y.carrier) :
    mass X Y (mix X Y l x y) = l := by
  rw [mass, massMap_mix, MConvexComb.bin_apply l (by simp), if_pos rfl]

theorem massMap_map {X' Y' : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X' Y']
    (f : X ⟶ X') (g : Y ⟶ Y') :
    coprod.map f g ≫ massMap X' Y' = massMap X Y := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_map, Category.assoc, massMap_inl, massMap_inl]
    exact comp_constHom f _
  · rw [← Category.assoc, coprod.inr_map, Category.assoc, massMap_inr, massMap_inr]
    exact comp_constHom g _

theorem mass_map {X' Y' : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X' Y']
    (f : X ⟶ X') (g : Y ⟶ Y') (w : (X ⨿ Y).carrier) :
    mass X' Y' ((coprod.map f g).1 w) = mass X Y w :=
  congrArg (fun m : (X ⨿ Y) ⟶ AConvMCat.free M
    (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) =>
      (m.1 w).toFun (Sum.inl PUnit.unit)) (massMap_map X Y f g)

theorem massMap_map_apply {X' Y' : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X' Y']
    (f : X ⟶ X') (g : Y ⟶ Y') (w : (X ⨿ Y).carrier) :
    (massMap X' Y').1 ((coprod.map f g).1 w) = (massMap X Y).1 w :=
  congrArg (fun m : (X ⨿ Y) ⟶ AConvMCat.free M
    (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 w) (massMap_map X Y f g)

/-- The image of a mixture under a cotuple. -/
theorem desc_apply_mix {W : AConvMCat.{u, max u v} M} (a : X ⟶ W) (b : Y ⟶ W)
    (l : M) (x : X.carrier) (y : Y.carrier) :
    (coprod.desc a b).1 (mix X Y l x y)
      = W.str.h (MConvexComb.bin l (a.1 x) (b.1 y)) := by
  have h1 : (coprod.desc a b).1 ((coprod.inl : X ⟶ X ⨿ Y).1 x) = a.1 x :=
    congrArg (fun m : X ⟶ W => m.1 x) (coprod.inl_desc a b)
  have h2 : (coprod.desc a b).1 ((coprod.inr : Y ⟶ X ⨿ Y).1 y) = b.1 y :=
    congrArg (fun m : Y ⟶ W => m.1 y) (coprod.inr_desc a b)
  rw [mix, hom_apply_bin, h1, h2]

/-- The image of a mixture under `f + g`. -/
theorem map_apply_mix {X' Y' : AConvMCat.{u, max u v} M} [HasBinaryCoproduct X' Y']
    (f : X ⟶ X') (g : Y ⟶ Y') (l : M) (x : X.carrier) (y : Y.carrier) :
    (coprod.map f g).1 (mix X Y l x y) = mix X' Y' l (f.1 x) (g.1 y) := by
  have h1 : (coprod.map f g).1 ((coprod.inl : X ⟶ X ⨿ Y).1 x)
      = (coprod.inl : X' ⟶ X' ⨿ Y').1 (f.1 x) :=
    congrArg (fun m : X ⟶ X' ⨿ Y' => m.1 x) (coprod.inl_map f g)
  have h2 : (coprod.map f g).1 ((coprod.inr : Y ⟶ X ⨿ Y).1 y)
      = (coprod.inr : Y' ⟶ X' ⨿ Y').1 (g.1 y) :=
    congrArg (fun m : Y ⟶ X' ⨿ Y' => m.1 y) (coprod.inr_map f g)
  rw [mix, hom_apply_bin, h1, h2]
  rfl

/-- `κ₁ x` is the mixture with `λ = 1`. -/
theorem mix_one (x : X.carrier) (y : Y.carrier) :
    mix X Y 1 x y = (coprod.inl : X ⟶ X ⨿ Y).1 x := by
  rw [mix, MConvexComb.bin_one]
  exact (X ⨿ Y).str.h_eta _

/-- `κ₂ y` is the mixture with `λ = 0`. -/
theorem mix_zero (x : X.carrier) (y : Y.carrier) :
    mix X Y 0 x y = (coprod.inr : Y ⟶ X ⨿ Y).1 y := by
  rw [mix, MConvexComb.bin_zero]
  exact (X ⨿ Y).str.h_eta _

/-- `q(𝒟_M κ₁ (χ)) = κ₁(h_X χ)`. -/
theorem coprodQuot_map_inl (χ : MConvexComb M X.carrier) :
    (coprodQuot X Y).1 (χ.map Sum.inl)
      = (coprod.inl : X ⟶ X ⨿ Y).1 (X.str.h χ) := by
  show (X ⨿ Y).str.h ((χ.map Sum.inl).map _) = _
  rw [MConvexComb.map_comp]
  exact ((coprod.inl : X ⟶ X ⨿ Y).2 χ).symm

/-- `q(𝒟_M κ₂ (ψ)) = κ₂(h_Y ψ)`. -/
theorem coprodQuot_map_inr (ψ : MConvexComb M Y.carrier) :
    (coprodQuot X Y).1 (ψ.map Sum.inr)
      = (coprod.inr : Y ⟶ X ⨿ Y).1 (Y.str.h ψ) := by
  show (X ⨿ Y).str.h ((ψ.map Sum.inr).map _) = _
  rw [MConvexComb.map_comp]
  exact ((coprod.inr : Y ⟶ X ⨿ Y).2 ψ).symm

/-- The mass map computed on the canonical surjection: `mass ∘ q` is the
pushforward along the collapse `X + Y → 1 + 1`. -/
theorem coprodQuot_massMap :
    coprodQuot X Y ≫ massMap X Y
      = AConvMCat.freeMap M (Sum.elim (fun _ => Sum.inl PUnit.unit)
          (fun _ => Sum.inr PUnit.unit) :
          X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) := by
  refine AConvMCat.free_hom_ext _ _ ?_
  rintro (x | y)
  · have h1 : (massMap X Y).1 ((coprod.inl : X ⟶ X ⨿ Y).1 x)
        = MConvexComb.eta (Sum.inl PUnit.unit) :=
      congrArg (fun m : X ⟶ AConvMCat.free M
        (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 x) (massMap_inl X Y)
    show (massMap X Y).1 ((coprodQuot X Y).1 (MConvexComb.eta (Sum.inl x))) = _
    rw [coprodQuot_eta_inl, h1, AConvMCat.freeMap_apply, MConvexComb.map_eta]
    rfl
  · have h2 : (massMap X Y).1 ((coprod.inr : Y ⟶ X ⨿ Y).1 y)
        = MConvexComb.eta (Sum.inr PUnit.unit) :=
      congrArg (fun m : Y ⟶ AConvMCat.free M
        (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 y) (massMap_inr X Y)
    show (massMap X Y).1 ((coprodQuot X Y).1 (MConvexComb.eta (Sum.inr y))) = _
    rw [coprodQuot_eta_inr, h2, AConvMCat.freeMap_apply, MConvexComb.map_eta]
    rfl

theorem massMap_coprodQuot (φ : MConvexComb M (X.carrier ⊕ Y.carrier)) :
    (massMap X Y).1 ((coprodQuot X Y).1 φ)
      = φ.map (Sum.elim (fun _ => Sum.inl PUnit.unit) (fun _ => Sum.inr PUnit.unit) :
          X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) :=
  congrArg (fun m : AConvMCat.free M (X.carrier ⊕ Y.carrier) ⟶
    AConvMCat.free M (PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1}) => m.1 φ)
    (coprodQuot_massMap X Y)

/-- **194I.4's key step, isolated**: an element of `X ⨿ Y` whose mass is the
left point is `κ₁` of an element of `X`. -/
theorem exists_inl_of_massMap (w : (X ⨿ Y).carrier)
    (h : (massMap X Y).1 w = MConvexComb.eta (Sum.inl PUnit.unit)) :
    ∃ x : X.carrier, (coprod.inl : X ⟶ X ⨿ Y).1 x = w := by
  classical
  obtain ⟨φ, hφ⟩ := coprodQuot_surjective X Y w
  have hmass := massMap_coprodQuot X Y φ
  rw [hφ, h] at hmass
  have hzero : ∀ y : Y.carrier, φ.toFun (Sum.inr y) = 0 := by
    intro y
    refine MConvexComb.eq_zero_of_map_eq_zero φ
      (Sum.elim (fun _ => Sum.inl PUnit.unit) (fun _ => Sum.inr PUnit.unit) :
        X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1})
      (y := Sum.inr PUnit.unit) ?_ (x := Sum.inr y) rfl
    rw [← hmass]
    exact if_neg (by simp)
  obtain ⟨χ, hχ⟩ := MConvexComb.exists_map_inl φ hzero
  exact ⟨X.str.h χ, by rw [← hφ, ← hχ, coprodQuot_map_inl]⟩

/-- The mirror image of `exists_inl_of_massMap`. -/
theorem exists_inr_of_massMap (w : (X ⨿ Y).carrier)
    (h : (massMap X Y).1 w = MConvexComb.eta (Sum.inr PUnit.unit)) :
    ∃ y : Y.carrier, (coprod.inr : Y ⟶ X ⨿ Y).1 y = w := by
  classical
  obtain ⟨φ, hφ⟩ := coprodQuot_surjective X Y w
  have hmass := massMap_coprodQuot X Y φ
  rw [hφ, h] at hmass
  have hzero : ∀ x : X.carrier, φ.toFun (Sum.inl x) = 0 := by
    intro x
    refine MConvexComb.eq_zero_of_map_eq_zero φ
      (Sum.elim (fun _ => Sum.inl PUnit.unit) (fun _ => Sum.inr PUnit.unit) :
        X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1})
      (y := Sum.inl PUnit.unit) ?_ (x := Sum.inl x) rfl
    rw [← hmass]
    exact if_neg (by simp)
  obtain ⟨ψ, hψ⟩ := MConvexComb.exists_map_inr φ hzero
  exact ⟨Y.str.h ψ, by rw [← hφ, ← hψ, coprodQuot_map_inr]⟩

/-- `κ₂ : Y → X ⨿ Y` is injective (the mirror image of
`AConvMCat.coprod_inl_injective`; same proof, the retraction being the cotuple
`[const y₀, id]`). -/
theorem coprod_inr_injective : Function.Injective (coprod.inr : Y ⟶ X ⨿ Y).1 := by
  classical
  rcases isEmpty_or_nonempty Y.carrier with hE | hN
  · exact fun y => (hE.false y).elim
  · obtain ⟨y₀⟩ := hN
    have hr := coprod.inr_desc (constHom X Y y₀) (𝟙 Y)
    intro y y' hyy
    have e1 : (coprod.desc (constHom X Y y₀) (𝟙 Y)).1
        ((coprod.inr : Y ⟶ X ⨿ Y).1 y) = y :=
      congrArg (fun t : Y ⟶ Y => t.1 y) hr
    have e2 : (coprod.desc (constHom X Y y₀) (𝟙 Y)).1
        ((coprod.inr : Y ⟶ X ⨿ Y).1 y') = y' :=
      congrArg (fun t : Y ⟶ Y => t.1 y') hr
    rw [← e1, ← e2, hyy]

/-- If `X` is empty then `κ₂ : Y → X ⨿ Y` is surjective. -/
theorem exists_inr_of_isEmpty (hX : IsEmpty X.carrier) (w : (X ⨿ Y).carrier) :
    ∃ y : Y.carrier, (coprod.inr : Y ⟶ X ⨿ Y).1 y = w := by
  obtain ⟨φ, hφ⟩ := coprodQuot_surjective X Y w
  obtain ⟨ψ, hψ⟩ := MConvexComb.exists_map_inr φ (fun x => (hX.false x).elim)
  exact ⟨Y.str.h ψ, by rw [← hφ, ← hψ, coprodQuot_map_inr]⟩

/-- If `Y` is empty then `κ₁ : X → X ⨿ Y` is surjective. -/
theorem exists_inl_of_isEmpty (hY : IsEmpty Y.carrier) (w : (X ⨿ Y).carrier) :
    ∃ x : X.carrier, (coprod.inl : X ⟶ X ⨿ Y).1 x = w := by
  obtain ⟨φ, hφ⟩ := coprodQuot_surjective X Y w
  obtain ⟨χ, hχ⟩ := MConvexComb.exists_map_inl φ (fun y => (hY.false y).elim)
  exact ⟨X.str.h χ, by rw [← hφ, ← hχ, coprodQuot_map_inl]⟩

/-- **The normal form for `X ⨿ Y` over an effect divisoid**: every element of
`X ⨿ Y` is a *binary* mixture `λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩`.

This is where the divisoid is used, and it is the only place: a general
element is `q(φ)` for a formal combination `φ` over `X + Y`
(`coprodQuot_surjective`, 193IX), and `φ` is normalized by dividing its
left-hand part by its total left mass `λ` and its right-hand part by `λᵖ`
(`MConvexComb.exists_of_div`, where the deficits `(λ/λ)ᵖ` and `(λᵖ/λᵖ)ᵖ` are
absorbed at the chosen points `x₀`, `y₀`).  Compare the thesis's `r` in the
proof of 196II. -/
theorem exists_mix [EffectDivisoid M] (x₀ : X.carrier) (y₀ : Y.carrier)
    (w : (X ⨿ Y).carrier) :
    ∃ (l : M) (x : X.carrier) (y : Y.carrier), w = mix X Y l x y := by
  classical
  obtain ⟨φ, hφ⟩ := coprodQuot_surjective X Y w
  let g : X.carrier ⊕ Y.carrier → PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1} :=
    Sum.elim (fun _ => Sum.inl PUnit.unit) (fun _ => Sum.inr PUnit.unit)
  obtain ⟨LA, hndA, hsuppA, hsumA⟩ := MConvexComb.exists_left_sum φ g
    (Sum.inl PUnit.unit) (fun _ => rfl) (fun _ hh => by
      have h0 : (Sum.inr PUnit.unit : PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1})
        = Sum.inl PUnit.unit := hh
      simp at h0)
  obtain ⟨LB, hndB, hsuppB, hsumB⟩ := MConvexComb.exists_right_sum φ g
    (Sum.inr PUnit.unit) (fun _ => rfl) (fun _ hh => by
      have h0 : (Sum.inl PUnit.unit : PUnit.{max u v + 1} ⊕ PUnit.{max u v + 1})
        = Sum.inr PUnit.unit := hh
      simp at h0)
  have horth : (φ.map g).toFun (Sum.inr PUnit.unit)
      = orth ((φ.map g).toFun (Sum.inl PUnit.unit)) :=
    MConvexComb.eq_orth_of_two _ (by simp) (fun z => by
      rcases z with a | a
      · exact Or.inl (by cases a; rfl)
      · exact Or.inr (by cases a; rfl))
  rw [horth] at hsumB
  obtain ⟨χ, hχ⟩ := MConvexComb.exists_of_div (fun x => φ.toFun (Sum.inl x)) x₀
    _ LA hndA hsuppA hsumA
  obtain ⟨ψ, hψ⟩ := MConvexComb.exists_of_div (fun y => φ.toFun (Sum.inr y)) y₀
    _ LB hndB hsuppB hsumB
  refine ⟨(φ.map g).toFun (Sum.inl PUnit.unit), X.str.h χ, Y.str.h ψ, ?_⟩
  set l : M := (φ.map g).toFun (Sum.inl PUnit.unit) with hl
  have hkey : φ = MConvexComb.mu
      (MConvexComb.bin l (χ.map Sum.inl) (ψ.map Sum.inr)) := by
    refine MConvexComb.ext (funext fun z => ?_)
    rcases z with x | y
    · have h := MConvexComb.mu_bin l (χ.map Sum.inl) (ψ.map Sum.inr) (Sum.inl x)
      rw [MConvexComb.map_apply_of_unique_fiber χ Sum.inl
          (fun z => ⟨fun hz => by simpa using hz, fun hz => by rw [hz]⟩),
        MConvexComb.map_inr_apply_inl ψ x, (exc_emonzero (orth l)).1, hχ x] at h
      have h2 : PCM.IsSumOf [φ.toFun (Sum.inl x), (0 : M)] (φ.toFun (Sum.inl x)) := by
        have h3 := isSumOf_pair (φ.toFun (Sum.inl x)) 0 (PCM.perp_zero _)
        rwa [PCM.ovee_zero] at h3
      exact isSumOf_unique h2 h
    · have h := MConvexComb.mu_bin l (χ.map Sum.inl) (ψ.map Sum.inr) (Sum.inr y)
      rw [MConvexComb.map_apply_of_unique_fiber ψ Sum.inr
          (fun z => ⟨fun hz => by simpa using hz, fun hz => by rw [hz]⟩),
        MConvexComb.map_inl_apply_inr χ y, (exc_emonzero l).1, hψ y] at h
      have h2 : PCM.IsSumOf [(0 : M), φ.toFun (Sum.inr y)] (φ.toFun (Sum.inr y)) :=
        isSumOf_zero_cons.mpr (isSumOf_singleton _)
      exact isSumOf_unique h2 h
  rw [← hφ, hkey]
  refine Eq.trans
    (hom_apply_bin (coprodQuot X Y) l (χ.map Sum.inl) (ψ.map Sum.inr)) ?_
  rw [coprodQuot_map_inl, coprodQuot_map_inr]
  rfl

end Mix

end AConvMCat

/-! ### 196II: the left pullback square -/

section LeftSquare

variable {M : Type u} [EffectMonoid M] [EffectDivisoid M]
  [HasFiniteCoproducts (AConvMCat.{u, max u v} M)]
  [HasTerminal (AConvMCat.{u, max u v} M)]

namespace AConvMCat

/-- The final object of `AConv_M` has exactly one element (it is isomorphic to
`𝒟_M 1`, which is a singleton by `MConvexComb.eq_eta_punit`). -/
theorem terminal_carrier_subsingleton
    (t t' : (⊤_ AConvMCat.{u, max u v} M).carrier) : t = t' := by
  have hT : IsTerminal (AConvMCat.free.{u, max u v} M PUnit.{max u v + 1}) :=
    AConvMCat.free_punit_isTerminal M
  set e := terminalIsoIsTerminal hT with he
  have h1 : ∀ z : (⊤_ AConvMCat.{u, max u v} M).carrier, e.inv.1 (e.hom.1 z) = z :=
    fun z => congrArg (fun m : (⊤_ AConvMCat.{u, max u v} M) ⟶
      (⊤_ AConvMCat.{u, max u v} M) => m.1 z) e.hom_inv_id
  rw [← h1 t, ← h1 t', MConvexComb.eq_eta_punit (e.hom.1 t),
    MConvexComb.eq_eta_punit (e.hom.1 t')]

variable (X Y : AConvMCat.{u, max u v} M)

/-- **196II, the uniqueness half**: `(id+!)` and `(!+id)` are jointly injective
on `X ⨿ Y`.

The argument avoids the derivation calculus: by the normal form
(`AConvMCat.exists_mix`) both elements are binary mixtures `λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩`,
their `λ`s agree because the mass map factors through both legs, and the
`x`- and `y`-parts are transported back into `X ⨿ Y` along the cotuples
`[κ₁, const κ₂y']` and `[const κ₁x, κ₂]` — which are maps of `AConv_M`
because constant maps are affine. -/
theorem coprod_jointly_injective {w w' : (X ⨿ Y).carrier}
    (h1 : (coprod.map (𝟙 X) (terminal.from Y)).1 w
      = (coprod.map (𝟙 X) (terminal.from Y)).1 w')
    (h2 : (coprod.map (terminal.from X) (𝟙 Y)).1 w
      = (coprod.map (terminal.from X) (𝟙 Y)).1 w') : w = w' := by
  classical
  rcases isEmpty_or_nonempty X.carrier with hX | ⟨⟨x₀⟩⟩
  · -- `X` empty: everything is `κ₂ y`, and `κ₂` is injective into `1 ⨿ Y`
    obtain ⟨y, rfl⟩ := exists_inr_of_isEmpty X Y hX w
    obtain ⟨y', rfl⟩ := exists_inr_of_isEmpty X Y hX w'
    have e : ∀ z : Y.carrier, (coprod.map (terminal.from X) (𝟙 Y)).1
        ((coprod.inr : Y ⟶ X ⨿ Y).1 z)
        = (coprod.inr : Y ⟶ (⊤_ AConvMCat.{u, max u v} M) ⨿ Y).1 z := fun z =>
      congrArg (fun m : Y ⟶ (⊤_ AConvMCat.{u, max u v} M) ⨿ Y => m.1 z)
        (coprod.inr_map (terminal.from X) (𝟙 Y))
    rw [e y, e y'] at h2
    rw [coprod_inr_injective _ Y h2]
  rcases isEmpty_or_nonempty Y.carrier with hY | ⟨⟨y₀⟩⟩
  · -- `Y` empty: everything is `κ₁ x`, and `κ₁` is injective into `X ⨿ 1`
    obtain ⟨x, rfl⟩ := exists_inl_of_isEmpty X Y hY w
    obtain ⟨x', rfl⟩ := exists_inl_of_isEmpty X Y hY w'
    have e : ∀ z : X.carrier, (coprod.map (𝟙 X) (terminal.from Y)).1
        ((coprod.inl : X ⟶ X ⨿ Y).1 z)
        = (coprod.inl : X ⟶ X ⨿ (⊤_ AConvMCat.{u, max u v} M)).1 z := fun z =>
      congrArg (fun m : X ⟶ X ⨿ (⊤_ AConvMCat.{u, max u v} M) => m.1 z)
        (coprod.inl_map (𝟙 X) (terminal.from Y))
    rw [e x, e x'] at h1
    rw [AConvMCat.coprod_inl_injective X _ h1]
  -- the main case: both non-empty, so the normal form applies
  obtain ⟨l, x, y, rfl⟩ := exists_mix X Y x₀ y₀ w
  obtain ⟨l', x', y', rfl⟩ := exists_mix X Y x₀ y₀ w'
  -- the two `λ`s agree, because the mass map factors through the left leg
  have hll : l = l' := by
    have hm : mass X (⊤_ AConvMCat.{u, max u v} M)
          ((coprod.map (𝟙 X) (terminal.from Y)).1 (mix X Y l x y))
        = mass X (⊤_ AConvMCat.{u, max u v} M)
          ((coprod.map (𝟙 X) (terminal.from Y)).1 (mix X Y l' x' y')) := by
      rw [h1]
    rwa [mass_map X Y (𝟙 X) (terminal.from Y), mass_map X Y (𝟙 X) (terminal.from Y),
      mass_mix, mass_mix] at hm
  subst hll
  -- transport the two component equalities back into `X ⨿ Y`
  have hy : mix X Y l x y = mix X Y l x y' := by
    have hd := congrArg (coprod.desc (constHom (⊤_ AConvMCat.{u, max u v} M) (X ⨿ Y)
      ((coprod.inl : X ⟶ X ⨿ Y).1 x)) (coprod.inr : Y ⟶ X ⨿ Y)).1 h2
    rw [map_apply_mix, map_apply_mix, desc_apply_mix, desc_apply_mix] at hd
    rw [mix, mix]
    exact hd
  have hx : mix X Y l x y' = mix X Y l x' y' := by
    have hd := congrArg (coprod.desc (coprod.inl : X ⟶ X ⨿ Y)
      (constHom (⊤_ AConvMCat.{u, max u v} M) (X ⨿ Y)
        ((coprod.inr : Y ⟶ X ⨿ Y).1 y'))).1 h1
    rw [map_apply_mix, map_apply_mix, desc_apply_mix, desc_apply_mix] at hd
    rw [mix, mix]
    exact hd
  rw [hy, hx]

/-- **196II, the existence half**: a compatible pair of elements of `X ⨿ 1`
and `1 ⨿ Y` comes from an element of `X ⨿ Y`. -/
theorem coprod_exists_lift {a : (X ⨿ (⊤_ AConvMCat.{u, max u v} M)).carrier}
    {b : ((⊤_ AConvMCat.{u, max u v} M) ⨿ Y).carrier}
    (h : (coprod.map (terminal.from X) (𝟙 (⊤_ AConvMCat.{u, max u v} M))).1 a
      = (coprod.map (𝟙 (⊤_ AConvMCat.{u, max u v} M)) (terminal.from Y)).1 b) :
    ∃ w : (X ⨿ Y).carrier,
      (coprod.map (𝟙 X) (terminal.from Y)).1 w = a ∧
      (coprod.map (terminal.from X) (𝟙 Y)).1 w = b := by
  classical
  rcases isEmpty_or_nonempty X.carrier with hX | ⟨⟨x₀⟩⟩
  · -- `X` empty: `a = κ₂ t`, so `b` has mass `κ₂` and is `κ₂ y`
    obtain ⟨t, rfl⟩ := exists_inr_of_isEmpty X _ hX a
    have hb : (massMap (⊤_ AConvMCat.{u, max u v} M) Y).1 b
        = MConvexComb.eta (Sum.inr PUnit.unit) := by
      rw [← massMap_map_apply (⊤_ AConvMCat.{u, max u v} M) Y
        (𝟙 (⊤_ AConvMCat.{u, max u v} M)) (terminal.from Y) b, ← h,
        massMap_map_apply X (⊤_ AConvMCat.{u, max u v} M) (terminal.from X)
          (𝟙 (⊤_ AConvMCat.{u, max u v} M)), massMap_inr_apply]
    obtain ⟨y, rfl⟩ := exists_inr_of_massMap _ Y b hb
    refine ⟨(coprod.inr : Y ⟶ X ⨿ Y).1 y, ?_, ?_⟩
    · have e : (coprod.map (𝟙 X) (terminal.from Y)).1 ((coprod.inr : Y ⟶ X ⨿ Y).1 y)
          = (coprod.inr : (⊤_ AConvMCat.{u, max u v} M) ⟶
              X ⨿ (⊤_ AConvMCat.{u, max u v} M)).1 ((terminal.from Y).1 y) :=
        congrArg (fun m : Y ⟶ X ⨿ (⊤_ AConvMCat.{u, max u v} M) => m.1 y)
          (coprod.inr_map (𝟙 X) (terminal.from Y))
      rw [e, terminal_carrier_subsingleton ((terminal.from Y).1 y) t]
    · exact congrArg (fun m : Y ⟶ (⊤_ AConvMCat.{u, max u v} M) ⨿ Y => m.1 y)
        (coprod.inr_map (terminal.from X) (𝟙 Y))
  rcases isEmpty_or_nonempty Y.carrier with hY | ⟨⟨y₀⟩⟩
  · -- `Y` empty: `b = κ₁ t`, so `a` has mass `κ₁` and is `κ₁ x`
    obtain ⟨t, rfl⟩ := exists_inl_of_isEmpty _ Y hY b
    have ha : (massMap X (⊤_ AConvMCat.{u, max u v} M)).1 a
        = MConvexComb.eta (Sum.inl PUnit.unit) := by
      rw [← massMap_map_apply X (⊤_ AConvMCat.{u, max u v} M) (terminal.from X)
        (𝟙 (⊤_ AConvMCat.{u, max u v} M)) a, h,
        massMap_map_apply (⊤_ AConvMCat.{u, max u v} M) Y
          (𝟙 (⊤_ AConvMCat.{u, max u v} M)) (terminal.from Y), massMap_inl_apply]
    obtain ⟨x, rfl⟩ := exists_inl_of_massMap X _ a ha
    refine ⟨(coprod.inl : X ⟶ X ⨿ Y).1 x, ?_, ?_⟩
    · exact congrArg (fun m : X ⟶ X ⨿ (⊤_ AConvMCat.{u, max u v} M) => m.1 x)
        (coprod.inl_map (𝟙 X) (terminal.from Y))
    · have e : (coprod.map (terminal.from X) (𝟙 Y)).1 ((coprod.inl : X ⟶ X ⨿ Y).1 x)
          = (coprod.inl : (⊤_ AConvMCat.{u, max u v} M) ⟶
              (⊤_ AConvMCat.{u, max u v} M) ⨿ Y).1 ((terminal.from X).1 x) :=
        congrArg (fun m : X ⟶ (⊤_ AConvMCat.{u, max u v} M) ⨿ Y => m.1 x)
          (coprod.inl_map (terminal.from X) (𝟙 Y))
      rw [e, terminal_carrier_subsingleton ((terminal.from X).1 x) t]
  -- the main case: normal forms on both sides, with the same `λ`
  obtain ⟨t₀⟩ : Nonempty (⊤_ AConvMCat.{u, max u v} M).carrier :=
    ⟨(terminal.from X).1 x₀⟩
  obtain ⟨la, x, s, rfl⟩ := exists_mix X _ x₀ t₀ a
  obtain ⟨lb, s', y, rfl⟩ := exists_mix _ Y t₀ y₀ b
  have hlab : la = lb := by
    have hm := congrArg (mass (⊤_ AConvMCat.{u, max u v} M)
      (⊤_ AConvMCat.{u, max u v} M)) h
    rwa [mass_map X (⊤_ AConvMCat.{u, max u v} M) (terminal.from X)
        (𝟙 (⊤_ AConvMCat.{u, max u v} M)),
      mass_map (⊤_ AConvMCat.{u, max u v} M) Y (𝟙 (⊤_ AConvMCat.{u, max u v} M))
        (terminal.from Y), mass_mix, mass_mix] at hm
  subst hlab
  refine ⟨mix X Y la x y, ?_, ?_⟩
  · rw [map_apply_mix, terminal_carrier_subsingleton ((terminal.from Y).1 y) s]
    rfl
  · rw [map_apply_mix, terminal_carrier_subsingleton ((terminal.from X).1 x) s']
    rfl

/-- **196II** (`aconvm-is-effectus`, eff.tex:3381), the left pullback square of
the effectus axioms in `AConv_M`. -/
theorem aconv_left_pullback (X Y : AConvMCat.{u, max u v} M) :
    IsPullback (coprod.map (𝟙 X) (terminal.from Y))
      (coprod.map (terminal.from X) (𝟙 Y))
      (coprod.map (terminal.from X) (𝟙 (⊤_ AConvMCat.{u, max u v} M)))
      (coprod.map (𝟙 (⊤_ AConvMCat.{u, max u v} M)) (terminal.from Y)) := by
  classical
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [coprod.map_map, coprod.map_map, Category.id_comp, Category.comp_id,
      Category.comp_id, Category.id_comp]
  · intro T φ φ' h1 h2
    refine Subtype.ext (funext fun z => coprod_jointly_injective X Y ?_ ?_)
    · exact congrArg (fun m : T ⟶ X ⨿ (⊤_ AConvMCat.{u, max u v} M) => m.1 z) h1
    · exact congrArg (fun m : T ⟶ (⊤_ AConvMCat.{u, max u v} M) ⨿ Y => m.1 z) h2
  · intro T a b hab
    have hex : ∀ z : T.carrier, ∃ w : (X ⨿ Y).carrier,
        (coprod.map (𝟙 X) (terminal.from Y)).1 w = a.1 z ∧
        (coprod.map (terminal.from X) (𝟙 Y)).1 w = b.1 z := fun z =>
      coprod_exists_lift X Y
        (congrArg (fun m : T ⟶ (⊤_ AConvMCat.{u, max u v} M) ⨿
          (⊤_ AConvMCat.{u, max u v} M) => m.1 z) hab)
    choose γ hγ₁ hγ₂ using hex
    -- `γ` is affine *because* the two legs are jointly injective: both
    -- `γ(h_T p)` and `h(𝒟_M γ (p))` are sent to `h(𝒟_M α (p))` and
    -- `h(𝒟_M β (p))` by the two legs.  (This replaces the thesis's
    -- eff.tex:3592–3657.)
    have haff : MConvex.IsAffine T.str (X ⨿ Y).str γ := by
      intro p
      have hc1 : (p.map γ).map (coprod.map (𝟙 X) (terminal.from Y)).1 = p.map a.1 := by
        rw [MConvexComb.map_comp]
        exact congrArg (fun f => p.map f) (funext hγ₁)
      have hc2 : (p.map γ).map (coprod.map (terminal.from X) (𝟙 Y)).1 = p.map b.1 := by
        rw [MConvexComb.map_comp]
        exact congrArg (fun f => p.map f) (funext hγ₂)
      refine coprod_jointly_injective X Y ?_ ?_
      · rw [hγ₁ (T.str.h p), a.2 p,
          (coprod.map (𝟙 X) (terminal.from Y)).2 (p.map γ), hc1]
      · rw [hγ₂ (T.str.h p), b.2 p,
          (coprod.map (terminal.from X) (𝟙 Y)).2 (p.map γ), hc2]
    exact ⟨⟨γ, haff⟩, Subtype.ext (funext hγ₁), Subtype.ext (funext hγ₂)⟩

end AConvMCat

end LeftSquare

/-- **196II** (`aconvm-is-effectus`, eff.tex:3381, Theorem): if `M` is an
effect divisoid, then `AConv_M` is an effectus (in total form).

⚠ Universe level `max u v`, as for 193V and 194I: an `EffectusTotalStructure`
carries `HasFiniteCoproducts`, and the coproducts of `AConv_M` are quotients
of function spaces into `M`, so they exist only at `AConvMCat.{u, max u v}`.
See PROVING-LOG.

The four other ingredients are 194I.1–.4 (`aconvalmosteffectus_coproducts`,
`_terminal`, `_jointlyMonic`, `_kappaPullback`); the left pullback square is
`AConvMCat.aconv_left_pullback` above.

⚠ Divergence from the thesis (eff.tex:3383–3657).  The thesis proves the left
square by interleaving two *derivations* (193IX/193IV) into one, which needs
the syntactic description of the least congruence that 193IV leaves to the
reader.  That is avoided here: over an effect divisoid every element of
`X + Y` is a **binary** mixture `λ|κ₁x⟩ ⋁ λᵖ|κ₂y⟩` (`AConvMCat.exists_mix`,
proved by dividing a general combination by its left mass `λ`, exactly the
thesis's own normalization step), and the rest is then two applications of the
fact that constant maps are affine.  Affineness of the mediating map `γ`
(eff.tex:3592–3657) is likewise free: `γ` is *defined* by a universal
property, so it is affine because its two legs are jointly injective. -/
theorem aconvm_is_effectus (M : Type u) [EffectMonoid M] [EffectDivisoid M] :
    Nonempty (EffectusTotalStructure (AConvMCat.{u, max u v} M)) := by
  letI hfc : HasFiniteCoproducts (AConvMCat.{u, max u v} M) :=
    aconvalmosteffectus_coproducts.{u, v} M
  letI hter : HasTerminal (AConvMCat.{u, max u v} M) :=
    aconvalmosteffectus_terminal.{u, max u v} M
  exact ⟨{ hasFiniteCoproducts := hfc
           hasTerminal := hter
           effectus :=
             { isPullback_plus := fun X Y => AConvMCat.aconv_left_pullback X Y
               isPullback_kappa := fun X Y =>
                 aconvalmosteffectus_kappaPullback.{u, v} M X Y
               jointlyMonic_cotuples :=
                 aconvalmosteffectus_jointlyMonic.{u, v} M } }⟩


end Theses.B.Eff
