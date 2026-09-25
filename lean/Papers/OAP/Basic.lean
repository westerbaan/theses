/-
Papers/OAP/Basic.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`: §2 *Preliminaries*, §3 *Overview* (no
numbered points) and §4 *Basic results* — points **OAP 1**–**OAP 26**.

Conventions (see `Papers/README.md` and `Papers/OAP/PLAN.md`):

* Effect algebras and effect monoids are the theses' `Theses.B.Eff.EffectAlgebra`
  and `Theses.B.Eff.EffectMonoid` (Perp-relation style).  Where the paper's
  definition differs from the tree's (OAP 1, OAP 5) both directions of the
  equivalence are proved here.
* The paper's order `≤` on an effect algebra is the algebraic order `≼`,
  registered below as the *scoped* instance `Papers.OAP.eaPartialOrder`
  (priority 100, so a concrete carrier's own order wins; OAP 3 and OAP 15
  prove that the two agree on the carriers used).  Later OAP files
  `open scoped Papers.OAP`.
* `a ⋎ b` is the partial sum made total (`= ovee a b h` when `Perp a b`,
  junk `0` otherwise) and `b ⊖ a` the difference made total (`= b ⊖ a` when
  `a ≤ b`, junk `0` otherwise).  Every statement carries the definedness
  hypotheses the print leaves implicit ("`a ⋁ b` exists").
* In an effect monoid the scoped instance `Papers.OAP.emMonoid` makes `M` a
  Mathlib `Monoid`, so `a ^ n` is the paper's `aⁿ`.
-/
import Theses.B.Eff.EffectAlgebras

set_option warn.classDefReducibility false

namespace Papers.OAP

open Theses.B.Eff

universe u v

/-! ## Effect algebras: the order and the total sum -/

section EAOrder

variable {E : Type u} [EffectAlgebra E]

/-- The algebraic order `a ≤ b ⟺ ∃ c, a ⋁ c = b` of an effect algebra
(OAP 1: "This turns `E` into a poset"), bundled as a partial order. -/
def eaPartialOrder (E : Type u) [EffectAlgebra E] : PartialOrder E where
  le := PCM.le
  le_refl := pcm_preorder_refl
  le_trans _ _ _ := pcm_preorder_trans
  le_antisymm _ _ := eabasics_le_antisymm

attribute [scoped instance 100] eaPartialOrder

theorem le_iff_pcmLe {a b : E} : a ≤ b ↔ a ≼ b := Iff.rfl

open Classical in
/-- The partial sum `⋁` made total: `a ⋎ b = a ⋁ b` when `a ⊥ b`, and the
junk value `0` otherwise. -/
noncomputable def oplus (a b : E) : E := if h : Perp a b then ovee a b h else 0

@[inherit_doc] scoped infixl:65 " ⋎ " => oplus

theorem oplus_eq {a b : E} (h : Perp a b) : a ⋎ b = ovee a b h := by
  classical simp only [oplus, h, dite_true]

theorem perp_symm {a b : E} : Perp a b ↔ Perp b a := ⟨PCM.perp_comm, PCM.perp_comm⟩

theorem oplus_comm (a b : E) : a ⋎ b = b ⋎ a := by
  by_cases h : Perp a b
  · rw [oplus_eq h, oplus_eq (PCM.perp_comm h)]; exact PCM.ovee_comm h
  · have h' : ¬ Perp b a := fun h' => h (PCM.perp_comm h')
    classical simp only [oplus, h, h', dite_false]

theorem perp_zero (a : E) : Perp a 0 := PCM.perp_zero a

theorem zero_perp (a : E) : Perp 0 a := PCM.zero_perp a

@[simp] theorem oplus_zero (a : E) : a ⋎ 0 = a := by
  rw [oplus_eq (PCM.perp_zero a)]; exact PCM.ovee_zero a _

@[simp] theorem zero_oplus (a : E) : 0 ⋎ a = a := by
  rw [oplus_comm]; exact oplus_zero a

theorem perp_of_oplus_perp {a b c : E} (hab : Perp a b) (h : Perp (a ⋎ b) c) :
    Perp b c :=
  PCM.perp_of_ovee_perp hab (by rwa [oplus_eq hab] at h)

theorem perp_oplus_of_oplus_perp {a b c : E} (hab : Perp a b) (h : Perp (a ⋎ b) c) :
    Perp a (b ⋎ c) := by
  have h' : Perp (ovee a b hab) c := by rwa [oplus_eq hab] at h
  rw [oplus_eq (perp_of_oplus_perp hab h)]
  exact PCM.perp_ovee_of_ovee_perp hab h'

theorem oplus_assoc {a b c : E} (hab : Perp a b) (h : Perp (a ⋎ b) c) :
    a ⋎ b ⋎ c = a ⋎ (b ⋎ c) := by
  have h' : Perp (ovee a b hab) c := by rwa [oplus_eq hab] at h
  rw [oplus_eq hab, oplus_eq h', oplus_eq (PCM.perp_of_ovee_perp hab h'),
    oplus_eq (PCM.perp_ovee_of_ovee_perp hab h')]
  exact PCM.ovee_assoc hab h'

/-- Associativity, right to left. -/
theorem perp_assoc_left {a b c : E} (hbc : Perp b c) (h : Perp a (b ⋎ c)) :
    Perp a b ∧ Perp (a ⋎ b) c := by
  rw [oplus_eq hbc] at h
  obtain ⟨hab, h', -⟩ := PCM.assoc_left hbc h
  exact ⟨hab, by rwa [oplus_eq hab]⟩

theorem oplus_assoc' {a b c : E} (hbc : Perp b c) (h : Perp a (b ⋎ c)) :
    a ⋎ b ⋎ c = a ⋎ (b ⋎ c) :=
  oplus_assoc (perp_assoc_left hbc h).1 (perp_assoc_left hbc h).2

theorem le_def {a b : E} : a ≤ b ↔ ∃ c, Perp a c ∧ a ⋎ c = b :=
  ⟨fun ⟨c, h, e⟩ => ⟨c, h, by rw [oplus_eq h, e]⟩,
    fun ⟨c, h, e⟩ => ⟨c, h, by rw [← oplus_eq h, e]⟩⟩

theorem le_oplus_left {a b : E} (h : Perp a b) : a ≤ a ⋎ b := le_def.2 ⟨b, h, rfl⟩

theorem le_oplus_right {a b : E} (h : Perp a b) : b ≤ a ⋎ b := by
  rw [oplus_comm]; exact le_oplus_left (PCM.perp_comm h)

theorem zero_le' (a : E) : (0 : E) ≤ a := GP.ea_zero_le a

theorem le_one' (a : E) : a ≤ (1 : E) := GP.ea_le_one a

theorem orth_orth (a : E) : orth (orth a) = a := eabasics_orth_orth a

theorem perp_orth (a : E) : Perp a (orth a) := EffectAlgebra.perp_orth a

theorem oplus_orth (a : E) : a ⋎ orth a = 1 := by
  rw [oplus_eq (perp_orth a)]; exact EffectAlgebra.ovee_orth a

theorem orth_oplus (a : E) : orth a ⋎ a = 1 := by rw [oplus_comm]; exact oplus_orth a

theorem eq_orth_of_oplus {a b : E} (h : Perp a b) (e : a ⋎ b = 1) : b = orth a :=
  EffectAlgebra.orth_unique h (by rwa [oplus_eq h] at e)

theorem orth_le_orth_iff {a b : E} : orth a ≤ orth b ↔ b ≤ a :=
  eabasics_le_iff_orth_le.symm

theorem orth_le_orth {a b : E} (h : a ≤ b) : orth b ≤ orth a := orth_le_orth_iff.2 h

theorem perp_iff_le_orth {a b : E} : Perp a b ↔ a ≤ orth b := eabasics_perp_iff_le_orth

theorem perp_of_le {a a' b b' : E} (ha : a ≤ a') (hb : b ≤ b') (h : Perp a' b') :
    Perp a b := GP.perp_of_le' ha hb h

theorem oplus_le_oplus {a a' b b' : E} (ha : a ≤ a') (hb : b ≤ b') (h : Perp a' b') :
    a ⋎ b ≤ a' ⋎ b' := by
  obtain ⟨h1, h2⟩ := GP.ovee_le_ovee' ha hb h
  rw [oplus_eq h1, oplus_eq h]; exact h2

theorem oplus_left_cancel {a b c : E} (hb : Perp a b) (hc : Perp a c)
    (h : a ⋎ b = a ⋎ c) : b = c := by
  refine eabasics_cancellation (c := a) (PCM.perp_comm hb) (PCM.perp_comm hc) ?_
  rw [← PCM.ovee_comm hb, ← PCM.ovee_comm hc, ← oplus_eq hb, ← oplus_eq hc, h]

theorem oplus_right_cancel {a b c : E} (ha : Perp a c) (hb : Perp b c)
    (h : a ⋎ c = b ⋎ c) : a = b := by
  rw [oplus_comm a, oplus_comm b] at h
  exact oplus_left_cancel (PCM.perp_comm ha) (PCM.perp_comm hb) h

theorem oplus_eq_zero {a b : E} (h : Perp a b) (h0 : a ⋎ b = 0) : a = 0 ∧ b = 0 :=
  eabasics_positivity h (by rwa [oplus_eq h] at h0)

theorem eq_zero_of_le_zero {a : E} (h : a ≤ 0) : a = 0 := le_antisymm h (zero_le' a)

theorem le_orth_of_perp {a b : E} (h : Perp a b) :
    b ≤ orth a := by
  rw [← perp_iff_le_orth]; exact PCM.perp_comm h

/-- `a ≤ a ⋎ b` reflects: `a ⋎ b ≤ a ⋎ c` iff `b ≤ c`. -/
theorem oplus_le_oplus_left_iff {a b c : E} (hb : Perp a b) (hc : Perp a c) :
    a ⋎ b ≤ a ⋎ c ↔ b ≤ c := by
  refine ⟨fun h => ?_, fun h => oplus_le_oplus le_rfl h hc⟩
  obtain ⟨d, hd, e⟩ := le_def.1 h
  have h1 := perp_of_oplus_perp hb hd
  rw [oplus_assoc hb hd] at e
  exact le_def.2 ⟨d, h1, oplus_left_cancel (perp_oplus_of_oplus_perp hb hd) hc e⟩

theorem perp_one_iff {a : E} : Perp a 1 ↔ a = 0 :=
  ⟨EffectAlgebra.eq_zero_of_perp_one, fun h => h ▸ zero_perp 1⟩

open Classical in
/-- The difference `b ⊖ a` (OAP 1) made total: the unique `c` with
`a ⋁ c = b` when `a ≤ b`, the junk value `0` otherwise. -/
noncomputable def osub (b a : E) : E := if h : a ≤ b then ominus b a h else 0

@[inherit_doc] scoped infixl:65 " ⊖ " => osub

theorem perp_osub {a b : E} (h : a ≤ b) : Perp a (b ⊖ a) := by
  have := isDiff_ominus h
  classical
  simp only [osub, h, dite_true]
  exact this.1

theorem oplus_osub {a b : E} (h : a ≤ b) : a ⋎ (b ⊖ a) = b := by
  rw [oplus_eq (perp_osub h)]
  have := isDiff_ominus h
  classical
  simp only [osub, h, dite_true]
  exact this.2

theorem osub_eq_iff {a b c : E} (h : a ≤ b) : b ⊖ a = c ↔ Perp a c ∧ a ⋎ c = b := by
  refine ⟨fun e => e ▸ ⟨perp_osub h, oplus_osub h⟩, fun ⟨hc, e⟩ => ?_⟩
  refine oplus_left_cancel (perp_osub h) hc ?_
  rw [oplus_osub h, e]

theorem osub_le {a b : E} (h : a ≤ b) : b ⊖ a ≤ b := by
  conv_rhs => rw [← oplus_osub h]
  exact le_oplus_right (perp_osub h)

theorem oplus_osub_cancel {a c : E} (h : Perp a c) : (a ⋎ c) ⊖ a = c :=
  (osub_eq_iff (le_oplus_left h)).2 ⟨h, rfl⟩

theorem one_osub (a : E) : (1 : E) ⊖ a = orth a :=
  (osub_eq_iff (le_one' a)).2 ⟨perp_orth a, oplus_orth a⟩

theorem osub_le_orth {x y : E} (h : x ≤ y) : y ⊖ x ≤ orth x := by
  rw [← perp_iff_le_orth]; exact PCM.perp_comm (perp_osub h)

/-- `a ↦ a ⊖ x` is monotone on `[x, 1]`. -/
theorem osub_le_osub_left {x a b : E} (hx : x ≤ a) (hab : a ≤ b) : a ⊖ x ≤ b ⊖ x := by
  have hb : x ≤ b := le_trans hx hab
  rw [← oplus_le_oplus_left_iff (perp_osub hx) (perp_osub hb), oplus_osub hx, oplus_osub hb]
  exact hab

theorem osub_le_osub_left_iff {x a b : E} (hx : x ≤ a) (hb : x ≤ b) :
    a ⊖ x ≤ b ⊖ x ↔ a ≤ b := by
  rw [← oplus_le_oplus_left_iff (perp_osub hx) (perp_osub hb), oplus_osub hx, oplus_osub hb]

theorem osub_osub {x a : E} (h : a ≤ x) : x ⊖ (x ⊖ a) = a :=
  (osub_eq_iff (osub_le h)).2 ⟨PCM.perp_comm (perp_osub h), by
    rw [oplus_comm]; exact oplus_osub h⟩

/-- `a ↦ x ⊖ a` is antitone on `[0, x]`. -/
theorem osub_le_osub_right {x a b : E} (ha : a ≤ x) (hba : b ≤ a) : x ⊖ a ≤ x ⊖ b := by
  obtain ⟨d, hbd, rfl⟩ := le_def.1 hba
  have h1 : Perp (b ⋎ d) (x ⊖ (b ⋎ d)) := perp_osub ha
  have e : x ⊖ b = d ⋎ (x ⊖ (b ⋎ d)) := by
    refine (osub_eq_iff (le_trans (le_oplus_left hbd) ha)).2
      ⟨perp_oplus_of_oplus_perp hbd h1, ?_⟩
    rw [← oplus_assoc hbd h1, oplus_osub ha]
  rw [e]; exact le_oplus_right (perp_of_oplus_perp hbd h1)

theorem osub_le_osub_right_iff {x a b : E} (ha : a ≤ x) (hb : b ≤ x) :
    x ⊖ a ≤ x ⊖ b ↔ b ≤ a := by
  refine ⟨fun h => ?_, osub_le_osub_right ha⟩
  have := osub_le_osub_right (osub_le hb) h
  rwa [osub_osub ha, osub_osub hb] at this

end EAOrder


/-! ## Finite sums as lists -/

section Lists

variable {E : Type u} [EffectAlgebra E]

theorem isSumOf_cons' {a : E} {l : List E} {s : E} :
    PCM.IsSumOf (a :: l) s ↔ ∃ t, PCM.IsSumOf l t ∧ Perp a t ∧ s = a ⋎ t := by
  rw [PCM.isSumOf_cons_iff]
  constructor
  · rintro ⟨t, ht, h, rfl⟩; exact ⟨t, ht, h, (oplus_eq h).symm⟩
  · rintro ⟨t, ht, h, rfl⟩; exact ⟨t, ht, h, (oplus_eq h).symm⟩

theorem isSumOf_append {l l' : List E} {r : E} :
    PCM.IsSumOf (l ++ l') r ↔
      ∃ s t, PCM.IsSumOf l s ∧ PCM.IsSumOf l' t ∧ Perp s t ∧ r = s ⋎ t := by
  induction l generalizing r with
  | nil =>
    simp only [List.nil_append, PCM.isSumOf_nil_iff]
    constructor
    · intro h; exact ⟨0, r, rfl, h, zero_perp r, (zero_oplus r).symm⟩
    · rintro ⟨s, t, rfl, ht, -, rfl⟩; rwa [zero_oplus]
  | cons a l ih =>
    simp only [List.cons_append, isSumOf_cons']
    constructor
    · rintro ⟨u, hu, hau, rfl⟩
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := ih.1 hu
      obtain ⟨has, h2⟩ := perp_assoc_left hst hau
      exact ⟨a ⋎ s, t, ⟨s, hs, has, rfl⟩, ht, h2, (oplus_assoc has h2).symm⟩
    · rintro ⟨s', t, ⟨s, hs, has, rfl⟩, ht, h2, rfl⟩
      exact ⟨s ⋎ t, ih.2 ⟨s, t, hs, ht, perp_of_oplus_perp has h2, rfl⟩,
        perp_oplus_of_oplus_perp has h2, oplus_assoc has h2⟩

theorem isSumOf_singleton {a s : E} : PCM.IsSumOf [a] s ↔ s = a := by
  rw [isSumOf_cons']
  constructor
  · rintro ⟨t, ht, -, rfl⟩; rw [PCM.isSumOf_nil_iff.1 ht, oplus_zero]
  · rintro rfl; exact ⟨0, PCM.IsSumOf.nil, perp_zero _, (oplus_zero _).symm⟩

theorem isSumOf_pair {a b s : E} : PCM.IsSumOf [a, b] s ↔ Perp a b ∧ s = a ⋎ b := by
  rw [isSumOf_cons']
  constructor
  · rintro ⟨t, ht, h, rfl⟩; rw [isSumOf_singleton.1 ht] at h ⊢; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨b, isSumOf_singleton.2 rfl, h, rfl⟩

/-- The four-term rearrangement `(a ⋁ d) ⋁ (a' ⋁ d') = (a ⋁ a') ⋁ (d ⋁ d')`. -/
theorem oplus_oplus_comm {a d a' d' : E} (h1 : Perp a d) (h2 : Perp a' d')
    (h : Perp (a ⋎ d) (a' ⋎ d')) :
    Perp a a' ∧ Perp d d' ∧ Perp (a ⋎ a') (d ⋎ d') ∧
      a ⋎ d ⋎ (a' ⋎ d') = a ⋎ a' ⋎ (d ⋎ d') := by
  have hs : PCM.IsSumOf ([a, d] ++ [a', d']) (a ⋎ d ⋎ (a' ⋎ d')) :=
    isSumOf_append.2 ⟨_, _, isSumOf_pair.2 ⟨h1, rfl⟩, isSumOf_pair.2 ⟨h2, rfl⟩, h, rfl⟩
  have hp : ([a, d] ++ [a', d']).Perm ([a, a'] ++ [d, d']) := by
    simp only [List.cons_append, List.nil_append]
    exact List.Perm.cons a (List.Perm.swap a' d [d'])
  obtain ⟨s, t, hs1, ht1, hst, e⟩ := isSumOf_append.1 (PCM.isSumOf_perm hp hs)
  obtain ⟨ha, rfl⟩ := isSumOf_pair.1 hs1
  obtain ⟨hd, rfl⟩ := isSumOf_pair.1 ht1
  exact ⟨ha, hd, hst, e⟩

end Lists

/-! ## §2 Preliminaries -/

section OAP1

variable {E : Type u} [EffectAlgebra E]

/-- **OAP 1** (first.tex:347, Definition): the print's unit is `1 ≡ 0^⊥`; the
tree's effect algebra (thesis B 175I) has `1` as a field, and the two
agree. -/
theorem oap1_one_eq_orth_zero : (1 : E) = orth 0 := eabasics_orth_zero.symm

/-- **OAP 1** (first.tex:347, Definition), the *Zero* axiom as printed:
`x ⊥ 0` and `x ⋁ 0 = x` (the tree states it on the left). -/
theorem oap1_zero (x : E) : ∃ h : Perp x 0, ovee x 0 h = x :=
  ⟨PCM.perp_zero x, PCM.ovee_zero x _⟩

/-- **OAP 1** (first.tex:347, Definition): conversely, a set with `0`, a
partial sum and a complement satisfying the print's five axioms (with
`1 ≡ 0^⊥`) is an effect algebra in the tree's sense. -/
def EffectAlgebra.ofPaper (E : Type u) [Zero E] (P : E → E → Prop)
    (ov : (a b : E) → P a b → E) (or : E → E)
    (comm : ∀ {x y : E}, P x y → P y x)
    (ov_comm : ∀ {x y : E} (h : P x y), ov x y h = ov y x (comm h))
    (p_zero : ∀ x : E, P x 0) (ov_zero : ∀ x : E, ov x 0 (p_zero x) = x)
    (assoc1 : ∀ {x y z : E} (hxy : P x y), P (ov x y hxy) z → P y z)
    (assoc2 : ∀ {x y z : E} (hxy : P x y) (h : P (ov x y hxy) z),
      P x (ov y z (assoc1 hxy h)))
    (assoc3 : ∀ {x y z : E} (hxy : P x y) (h : P (ov x y hxy) z),
      ov (ov x y hxy) z h = ov x (ov y z (assoc1 hxy h)) (assoc2 hxy h))
    (p_or : ∀ x : E, P x (or x)) (ov_or : ∀ x : E, ov x (or x) (p_or x) = or 0)
    (or_unique : ∀ {x y : E} (h : P x y), ov x y h = or 0 → y = or x)
    (zero_one : ∀ {x : E}, P x (or 0) → x = 0) : EffectAlgebra E where
  zero := 0
  one := or 0
  Perp := P
  ovee := ov
  perp_comm := comm
  ovee_comm := ov_comm
  perp_of_ovee_perp := assoc1
  perp_ovee_of_ovee_perp := assoc2
  ovee_assoc := assoc3
  zero_perp a := comm (p_zero a)
  zero_ovee a := (ov_comm _).trans (ov_zero a)
  orth := or
  perp_orth := p_or
  ovee_orth := ov_or
  orth_unique := or_unique
  eq_zero_of_perp_one := zero_one

/-- **OAP 1** (first.tex:347, Definition): the order turns `E` into a poset
(the instance `eaPartialOrder`) with minimum `0` and maximum `1`. -/
theorem oap1_bounded (a : E) : 0 ≤ a ∧ a ≤ 1 := ⟨zero_le' a, le_one' a⟩

/-- **OAP 1** (first.tex:347, Definition): `x ↦ x^⊥` is an order
anti-isomorphism (antitone, order-reflecting, involutive). -/
theorem oap1_orth_antiIso (a b : E) :
    (orth a ≤ orth b ↔ b ≤ a) ∧ orth (orth a) = a :=
  ⟨orth_le_orth_iff, orth_orth a⟩

/-- **OAP 1** (first.tex:347, Definition): `x ⊥ y` iff `x ≤ y^⊥`. -/
theorem oap1_perp_iff (a b : E) : Perp a b ↔ a ≤ orth b := perp_iff_le_orth

/-- **OAP 1** (first.tex:347, Definition): if `x ≤ y` the `z` with
`x ⋁ z = y` is unique (it is `y ⊖ x`). -/
theorem oap1_osub_unique {x y : E} (h : x ≤ y) :
    ∃! z, ∃ hz : Perp x z, ovee x z hz = y :=
  ⟨y ⊖ x, ⟨perp_osub h, by rw [← oplus_eq]; exact oplus_osub h⟩,
    fun z ⟨hz, e⟩ => ((osub_eq_iff h).2 ⟨hz, by rw [oplus_eq hz, e]⟩).symm⟩

/-- **OAP 1** (first.tex:347, Definition): an **embedding** of effect
algebras is an order-reflecting morphism. -/
structure EAEmbedding (E : Type u) (F : Type v) [EffectAlgebra E] [EffectAlgebra F]
    extends EAHom E F where
  reflect : ∀ {a b : E}, toFun a ≤ toFun b → a ≤ b

/-- **OAP 1** (first.tex:347, Definition): an isomorphism of effect algebras
is a bijective morphism whose inverse is a morphism too. -/
def EAIsIso {E : Type u} {F : Type v} [EffectAlgebra E] [EffectAlgebra F]
    (f : EAHom E F) : Prop :=
  ∃ g : EAHom F E, (∀ a, g.toFun (f.toFun a) = a) ∧ ∀ b, f.toFun (g.toFun b) = b

/-- **OAP 1** (first.tex:347, Definition): "an embedding is automatically
injective". -/
theorem EAEmbedding.injective {E : Type u} {F : Type v} [EffectAlgebra E]
    [EffectAlgebra F] (f : EAEmbedding E F) : Function.Injective f.toFun :=
  fun _ _ h => le_antisymm (f.reflect h.le) (f.reflect h.ge)

section Morphisms

variable {F : Type u} [EffectAlgebra F]

/-- **OAP 1** (first.tex:347, Definition): a morphism preserves the
complement and the order. -/
theorem oap1_hom_orth_mono (f : EAHom E F) :
    (∀ a, f.toFun (orth a) = orth (f.toFun a)) ∧
      ∀ {a b : E}, a ≤ b → f.toFun a ≤ f.toFun b :=
  ⟨exc_eamorphism_map_orth f, fun h => exc_eamorphism_monotone f h⟩

/-- **OAP 1** (first.tex:347, Definition): "an isomorphism is the same as a
surjective embedding". -/
theorem oap1_isIso_iff (f : EAHom E F) :
    EAIsIso f ↔ Function.Surjective f.toFun ∧ ∀ {a b : E}, f.toFun a ≤ f.toFun b → a ≤ b := by
  constructor
  · rintro ⟨g, hgf, hfg⟩
    refine ⟨fun b => ⟨g.toFun b, hfg b⟩, fun {a b} h => ?_⟩
    have := (oap1_hom_orth_mono g).2 h
    rwa [hgf, hgf] at this
  · rintro ⟨hs, hr⟩
    have hinj : Function.Injective f.toFun :=
      fun _ _ h => le_antisymm (hr h.le) (hr h.ge)
    let g : F → E := Function.surjInv hs
    have hfg : ∀ b, f.toFun (g b) = b := Function.surjInv_eq hs
    have hgf : ∀ a, g (f.toFun a) = a := fun a => hinj (hfg _)
    have hperp : ∀ {x y : F}, Perp x y → Perp (g x) (g y) := by
      intro x y h
      rw [perp_iff_le_orth] at h ⊢
      apply hr
      rwa [(oap1_hom_orth_mono f).1, hfg, hfg]
    refine ⟨{ toFun := g, perp_map := hperp, ovee_map := ?_, map_one := ?_ }, hgf, hfg⟩
    · intro x y h
      apply hinj
      rw [hfg, f.ovee_map (hperp h)]
      exact PCM.ovee_congr (hfg x).symm (hfg y).symm _ _
    · apply hinj; rw [hfg, f.map_one]

end Morphisms

/-- **OAP 4** (first.tex:425, Remark): "An effect algebra is a bounded
poset".  (The rest of the remark — the Kalmbach extension and monad — is
cited literature and is not formalised.) -/
theorem oap4_boundedPoset : (∀ a : E, 0 ≤ a) ∧ ∀ a : E, a ≤ 1 :=
  ⟨zero_le', le_one'⟩

end OAP1

/-! **OAP 10** (first.tex:523, Remark): a physical theory whose probabilities
are of the form `[0,1]_{C(X)}` "can be seen as a theory with a natural notion
of space".  Interpretation only; nothing to formalise. -/

/-! ### Directed completeness (OAP 13, OAP 14) -/

section Completeness

variable {E : Type u} [EffectAlgebra E]

/-- **OAP 13** (first.tex:545, Definition): a **directed set** is a non-empty
`S` such that any two elements of `S` have an upper bound in `S`. -/
def IsDirectedSet (S : Set E) : Prop := S.Nonempty ∧ DirectedOn (· ≤ ·) S

/-- **OAP 13** (first.tex:545, Definition): `E` is **directed complete** when
every directed set has a supremum. -/
class DirectedComplete (E : Type u) [EffectAlgebra E] : Prop where
  exists_isLUB : ∀ S : Set E, IsDirectedSet S → ∃ s, IsLUB S s

/-- **OAP 13** (first.tex:545, Definition): `E` is **ω-complete** when every
increasing sequence `a₁ ≤ a₂ ≤ …` has a supremum. -/
class OmegaComplete (E : Type u) [EffectAlgebra E] : Prop where
  exists_isLUB : ∀ f : ℕ → E, Monotone f → ∃ s, IsLUB (Set.range f) s

/-- **OAP 13** (first.tex:545, Definition): "or equivalently" — `E` is
ω-complete iff every countable directed set has a supremum. -/
theorem oap13_omegaComplete_iff :
    OmegaComplete E ↔ ∀ S : Set E, S.Countable → IsDirectedSet S → ∃ s, IsLUB S s := by
  constructor
  · intro hE S hc ⟨hne, hd⟩
    obtain ⟨g, rfl⟩ := hc.exists_eq_range hne
    have hd' : ∀ m n : ℕ, ∃ k, g m ≤ g k ∧ g n ≤ g k := by
      intro m n
      obtain ⟨_, ⟨k, rfl⟩, h1, h2⟩ := hd _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact ⟨k, h1, h2⟩
    choose k hk1 hk2 using hd'
    let idx : ℕ → ℕ := fun n => Nat.rec 0 (fun n i => k i (n + 1)) n
    have hmono : Monotone (g ∘ idx) := monotone_nat_of_le_succ fun n => hk1 (idx n) (n + 1)
    have hge : ∀ n, g n ≤ g (idx n) := by
      intro n; cases n with
      | zero => exact le_rfl
      | succ n => exact hk2 (idx n) (n + 1)
    obtain ⟨s, hs⟩ := hE.exists_isLUB _ hmono
    refine ⟨s, ?_, ?_⟩
    · rintro _ ⟨n, rfl⟩; exact le_trans (hge n) (hs.1 ⟨n, rfl⟩)
    · intro u hu
      exact hs.2 (by rintro _ ⟨n, rfl⟩; exact hu ⟨idx n, rfl⟩)
  · intro h
    refine ⟨fun f hf => h _ (Set.countable_range f) ⟨Set.range_nonempty f, ?_⟩⟩
    exact directedOn_range.2 hf.directed_le

/-- **OAP 13**: a directed-complete effect algebra is ω-complete. -/
instance (priority := 100) DirectedComplete.omegaComplete [DirectedComplete E] :
    OmegaComplete E :=
  ⟨fun f hf => DirectedComplete.exists_isLUB _
    ⟨Set.range_nonempty f, directedOn_range.2 hf.directed_le⟩⟩

theorem isGLB_orth_of_isLUB {S : Set E} {m : E} (h : IsLUB (orth '' S) m) :
    IsGLB S (orth m) := by
  refine ⟨fun s hs => ?_, fun l hl => ?_⟩
  · rw [← orth_le_orth_iff, orth_orth]; exact h.1 ⟨s, hs, rfl⟩
  · rw [← orth_le_orth_iff, orth_orth]
    exact h.2 (by rintro _ ⟨s, hs, rfl⟩; exact orth_le_orth (hl hs))

theorem isLUB_orth_of_isGLB {S : Set E} {m : E} (h : IsGLB (orth '' S) m) :
    IsLUB S (orth m) := by
  refine ⟨fun s hs => ?_, fun l hl => ?_⟩
  · rw [← orth_le_orth_iff, orth_orth]; exact h.1 ⟨s, hs, rfl⟩
  · rw [← orth_le_orth_iff, orth_orth]
    exact h.2 (by rintro _ ⟨s, hs, rfl⟩; exact orth_le_orth (hl hs))

theorem orth_image_orth_image (S : Set E) : orth '' (orth '' S) = S := by
  rw [Set.image_image]; simp only [orth_orth, Set.image_id']

/-- **OAP 14** (first.tex:554, Remark): "we could have equivalently defined
directed completeness with respect to downwards directed sets, as the
complement is an order anti-isomorphism". -/
theorem oap14_directedComplete_iff :
    DirectedComplete E ↔
      ∀ S : Set E, S.Nonempty → DirectedOn (· ≥ ·) S → ∃ s, IsGLB S s := by
  have dual : ∀ S : Set E, DirectedOn (· ≥ ·) S → DirectedOn (· ≤ ·) (orth '' S) := by
    rintro S hS _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, h1, h2⟩ := hS a ha b hb
    exact ⟨orth c, ⟨c, hc, rfl⟩, orth_le_orth h1, orth_le_orth h2⟩
  have dual' : ∀ S : Set E, DirectedOn (· ≤ ·) S → DirectedOn (· ≥ ·) (orth '' S) := by
    rintro S hS _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, h1, h2⟩ := hS a ha b hb
    exact ⟨orth c, ⟨c, hc, rfl⟩, orth_le_orth h1, orth_le_orth h2⟩
  constructor
  · intro hE S hne hd
    obtain ⟨m, hm⟩ := hE.exists_isLUB _ ⟨hne.image _, dual S hd⟩
    exact ⟨_, isGLB_orth_of_isLUB hm⟩
  · intro h
    refine ⟨fun S ⟨hne, hd⟩ => ?_⟩
    obtain ⟨m, hm⟩ := h _ (hne.image _) (dual' S hd)
    exact ⟨_, isLUB_orth_of_isGLB hm⟩

/-- **OAP 14** (first.tex:554, Remark), the ω-version used in OAP 26: in an
ω-complete effect algebra every decreasing sequence has an infimum. -/
theorem OmegaComplete.exists_isGLB [OmegaComplete E] (f : ℕ → E) (hf : Antitone f) :
    ∃ s, IsGLB (Set.range f) s := by
  obtain ⟨m, hm⟩ := OmegaComplete.exists_isLUB (orth ∘ f)
    (fun a b h => orth_le_orth (hf h))
  refine ⟨orth m, isGLB_orth_of_isLUB ?_⟩
  rwa [← Set.range_comp]

end Completeness

/-! ## §4 Basic results for effect algebras (OAP 22, OAP 24) -/

section EABasic

variable {E : Type u} [EffectAlgebra E]

/-- **OAP 22** (`lem:forcing`, first.tex:727, Lemma): if `a ≤ b`, `a' ≤ b'`
and `b ⋁ b' ≤ a ⋁ a'`, then `a = b` and `a' = b'`. -/
theorem oap22_forcing {a b a' b' : E} (hab : a ≤ b) (hab' : a' ≤ b')
    (hb : Perp b b') (h : b ⋎ b' ≤ a ⋎ a') : a = b ∧ a' = b' := by
  -- `a ⋁ a' ≤ b ⋁ b'`, hence equality
  have heq : a ⋎ a' = b ⋎ b' := le_antisymm (oplus_le_oplus hab hab' hb) h
  -- `0 = (b ⋁ b') ⊖ (a ⋁ a') = (b ⊖ a) ⋁ (b' ⊖ a')`
  obtain ⟨d, hd, rfl⟩ := le_def.1 hab
  obtain ⟨d', hd', rfl⟩ := le_def.1 hab'
  obtain ⟨-, hdd, hsum, e⟩ := oplus_oplus_comm hd hd' hb
  rw [e] at heq
  have h0 : d ⋎ d' = 0 := by
    refine (oplus_left_cancel hsum (perp_zero _) ?_)
    rw [oplus_zero]; exact heq.symm
  obtain ⟨rfl, rfl⟩ := oplus_eq_zero hdd h0
  simp only [oplus_zero, and_self]

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 1: for
non-empty `S ⊆ [0, x^⊥]`, if `⋁ S` exists then `x ⋁ ⋁S = ⋁ (x ⋁ S)`. -/
theorem oap24_1 {x m : E} {S : Set E} (hne : S.Nonempty) (hS : ∀ s ∈ S, s ≤ orth x)
    (h : IsLUB S m) : Perp x m ∧ IsLUB ((x ⋎ ·) '' S) (x ⋎ m) := by
  have hm : Perp x m := PCM.perp_comm (perp_iff_le_orth.2 (h.2 hS))
  refine ⟨hm, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact oplus_le_oplus le_rfl (h.1 hs) hm
  · intro u hu
    obtain ⟨s0, hs0⟩ := hne
    have hxu : x ≤ u := le_trans (le_oplus_left
      (PCM.perp_comm (perp_iff_le_orth.2 (hS s0 hs0)))) (hu ⟨s0, hs0, rfl⟩)
    have key : m ≤ u ⊖ x := h.2 fun s hs => by
      rw [← oplus_le_oplus_left_iff (PCM.perp_comm (perp_iff_le_orth.2 (hS s hs)))
        (perp_osub hxu), oplus_osub hxu]
      exact hu ⟨s, hs, rfl⟩
    calc x ⋎ m ≤ x ⋎ (u ⊖ x) := oplus_le_oplus le_rfl key (perp_osub hxu)
      _ = u := oplus_osub hxu

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 2: for
non-empty `S ⊆ [0, x^⊥]`, if `⋀ (x ⋁ S)` exists then so does `⋀ S`, and
`x ⋁ ⋀S = ⋀ (x ⋁ S)`. -/
theorem oap24_2 {x n : E} {S : Set E} (hne : S.Nonempty) (hS : ∀ s ∈ S, s ≤ orth x)
    (h : IsGLB ((x ⋎ ·) '' S) n) : ∃ m, IsGLB S m ∧ Perp x m ∧ x ⋎ m = n := by
  have hpx : ∀ s ∈ S, Perp x s := fun s hs => PCM.perp_comm (perp_iff_le_orth.2 (hS s hs))
  have hxn : x ≤ n := h.2 (by rintro _ ⟨s, hs, rfl⟩; exact le_oplus_left (hpx s hs))
  refine ⟨n ⊖ x, ⟨fun s hs => ?_, fun l hl => ?_⟩, perp_osub hxn, oplus_osub hxn⟩
  · rw [← oplus_le_oplus_left_iff (perp_osub hxn) (hpx s hs), oplus_osub hxn]
    exact h.1 ⟨s, hs, rfl⟩
  · obtain ⟨s0, hs0⟩ := hne
    have hxl : Perp x l :=
      PCM.perp_comm (perp_iff_le_orth.2 (le_trans (hl hs0) (hS s0 hs0)))
    rw [← oplus_le_oplus_left_iff hxl (perp_osub hxn), oplus_osub hxn]
    exact h.2 (by rintro _ ⟨s, hs, rfl⟩; exact oplus_le_oplus le_rfl (hl hs) (hpx s hs))

theorem image_oplus_image_osub {x : E} {S : Set E} (hS : ∀ s ∈ S, x ≤ s) :
    (x ⋎ ·) '' ((· ⊖ x) '' S) = S := by
  rw [Set.image_image]
  conv_rhs => rw [← Set.image_id S]
  exact Set.image_congr fun s hs => oplus_osub (hS s hs)

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 3 **as
corrected**: for non-empty `S ⊆ [x, 1]`, if `⋁_{s ∈ S} s ⊖ x` exists then so
does `⋁ S`, and `(⋁S) ⊖ x = ⋁_{s∈S} s ⊖ x`.  The print's premise reads
`⋀_{s∈S} s ⊖ x` (an infimum), which makes the clause false:
`oap24_3_false_as_printed`. -/
theorem oap24_3 {x m : E} {S : Set E} (hne : S.Nonempty) (hS : ∀ s ∈ S, x ≤ s)
    (h : IsLUB ((· ⊖ x) '' S) m) : ∃ j, IsLUB S j ∧ j ⊖ x = m := by
  obtain ⟨hm, hj⟩ := oap24_1 (hne.image _) (by
    rintro _ ⟨s, hs, rfl⟩; exact osub_le_orth (hS s hs)) h
  rw [image_oplus_image_osub hS] at hj
  exact ⟨_, hj, oplus_osub_cancel hm⟩

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 3
**as printed is false**: with the premise "`⋀_{s∈S} s ⊖ x` exists" the
conclusion "`(⋁S) ⊖ x = ⋁_{s∈S} s ⊖ x`, both sides existing" fails in the
Wright triangle (the tree's `WrightTriangle.W`) for `x = 0`,
`S = {a₁, a₂}`: `⋀ S = 0` exists but `⋁ S` does not. -/
theorem oap24_3_false_as_printed :
    ¬ ∀ (E : Type) [EffectAlgebra E] (x m : E) (S : Set E), S.Nonempty →
      (∀ s ∈ S, x ≤ s) → IsGLB ((· ⊖ x) '' S) m →
        ∃ j, IsLUB S j ∧ j ⊖ x = m := by
  intro H
  open WrightTriangle in
  have hS : (· ⊖ (0 : W)) '' {W.a1, W.a2} = {W.a1, W.a2} := by
    conv_rhs => rw [← Set.image_id {W.a1, W.a2}]
    exact Set.image_congr fun s _ => (osub_eq_iff (zero_le' s)).2 ⟨zero_perp s, zero_oplus s⟩
  have hglb : IsGLB ((· ⊖ (0 : W)) '' {W.a1, W.a2}) 0 := by
    rw [hS]
    obtain ⟨-, -, h⟩ := WrightTriangle.isInf_a1_a2
    refine ⟨fun s _ => zero_le' s, fun l hl => h l (hl (by simp)) (hl (by simp))⟩
  obtain ⟨j, hj, -⟩ := H WrightTriangle.W 0 0 {W.a1, W.a2} ⟨_, Set.mem_insert _ _⟩
    (fun s _ => zero_le' s) hglb
  exact WrightTriangle.no_sup_a1_a2 ⟨j, hj.1 (by simp), hj.1 (by simp),
    fun c h1 h2 => hj.2 (by
      rintro s (rfl | rfl)
      · exact h1
      · exact h2)⟩

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 4: for
non-empty `S ⊆ [x, 1]`, if `⋀ S` exists then `(⋀S) ⊖ x = ⋀_{s∈S} s ⊖ x`. -/
theorem oap24_4 {x n : E} {S : Set E} (hne : S.Nonempty) (hS : ∀ s ∈ S, x ≤ s)
    (h : IsGLB S n) : IsGLB ((· ⊖ x) '' S) (n ⊖ x) := by
  have h' : IsGLB ((x ⋎ ·) '' ((· ⊖ x) '' S)) n := by rwa [image_oplus_image_osub hS]
  obtain ⟨m, hm, hxm, rfl⟩ := oap24_2 (hne.image _) (by
    rintro _ ⟨s, hs, rfl⟩; exact osub_le_orth (hS s hs)) h'
  rwa [oplus_osub_cancel hxm]

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 5: for
non-empty `S ⊆ [0, x]`, if `⋁ S` exists then `x ⊖ ⋁S = ⋀ (x ⊖ S)`. -/
theorem oap24_5 {x j : E} {S : Set E} (hne : S.Nonempty) (hS : ∀ s ∈ S, s ≤ x)
    (h : IsLUB S j) : IsGLB ((x ⊖ ·) '' S) (x ⊖ j) := by
  have hj : j ≤ x := h.2 hS
  refine ⟨?_, fun l hl => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact osub_le_osub_right hj (h.1 hs)
  · obtain ⟨s0, hs0⟩ := hne
    have hlx : l ≤ x := le_trans (hl ⟨s0, hs0, rfl⟩) (osub_le (hS s0 hs0))
    have key : j ≤ x ⊖ l := h.2 fun s hs => by
      have := hl ⟨s, hs, rfl⟩
      rw [← osub_osub hlx] at this
      exact (osub_le_osub_right_iff (osub_le hlx) (hS s hs)).1 this
    have := osub_le_osub_right (osub_le hlx) key
    rwa [osub_osub hlx] at this

/-- **OAP 24** (`lem:additionisnormal`, first.tex:778, Lemma), clause 6: for
non-empty `S ⊆ [0, x]`, if `⋁ (x ⊖ S)` exists then so does `⋀ S`, and
`x ⊖ ⋀S = ⋁ (x ⊖ S)`. -/
theorem oap24_6 {x m : E} {S : Set E} (hne : S.Nonempty) (hS : ∀ s ∈ S, s ≤ x)
    (h : IsLUB ((x ⊖ ·) '' S) m) : ∃ n, IsGLB S n ∧ x ⊖ n = m := by
  have hmx : m ≤ x := h.2 (by rintro _ ⟨s, hs, rfl⟩; exact osub_le (hS s hs))
  refine ⟨x ⊖ m, ⟨fun s hs => ?_, fun l hl => ?_⟩, osub_osub hmx⟩
  · have := osub_le_osub_right hmx (h.1 ⟨s, hs, rfl⟩)
    rwa [osub_osub (hS s hs)] at this
  · obtain ⟨s0, hs0⟩ := hne
    have hlx : l ≤ x := le_trans (hl hs0) (hS s0 hs0)
    have key : m ≤ x ⊖ l :=
      h.2 (by rintro _ ⟨s, hs, rfl⟩; exact osub_le_osub_right (hS s hs) (hl hs))
    have := osub_le_osub_right (osub_le hlx) key
    rwa [osub_osub hlx] at this

end EABasic

/-! ### `n`-fold sums -/

section NSum

variable {E : Type u} [EffectAlgebra E]

/-- `IsNSum a n s`: the `n`-fold sum `na = a ⋁ ⋯ ⋁ a` exists and equals `s`
(first.tex:858). -/
inductive IsNSum (a : E) : ℕ → E → Prop
  | zero : IsNSum a 0 0
  | succ {n : ℕ} {s : E} : IsNSum a n s → Perp s a → IsNSum a (n + 1) (s ⋎ a)

theorem isNSum_succ_iff {a : E} {n : ℕ} {s : E} :
    IsNSum a (n + 1) s ↔ ∃ t, IsNSum a n t ∧ Perp t a ∧ s = t ⋎ a := by
  constructor
  · intro h; cases h with
    | succ h hp => exact ⟨_, h, hp, rfl⟩
  · rintro ⟨t, h, hp, rfl⟩; exact h.succ hp

theorem IsNSum.unique {a : E} {n : ℕ} {s t : E} (hs : IsNSum a n s) (ht : IsNSum a n t) :
    s = t := by
  induction n generalizing s t with
  | zero => cases hs; cases ht; rfl
  | succ n ih =>
    obtain ⟨s', hs', -, rfl⟩ := isNSum_succ_iff.1 hs
    obtain ⟨t', ht', -, rfl⟩ := isNSum_succ_iff.1 ht
    rw [ih hs' ht']

theorem isNSum_one (a : E) : IsNSum a 1 a := by
  have := (IsNSum.zero (a := a)).succ (zero_perp a)
  rwa [zero_oplus] at this

theorem IsNSum.le_of_le {a : E} {m n : ℕ} {s : E} (hs : IsNSum a n s) (hmn : m ≤ n) :
    ∃ t, IsNSum a m t ∧ t ≤ s := by
  induction n generalizing s with
  | zero => obtain rfl : m = 0 := Nat.le_zero.1 hmn; exact ⟨s, hs, le_rfl⟩
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hmn with h | rfl
    · obtain ⟨s', hs', hp, rfl⟩ := isNSum_succ_iff.1 hs
      obtain ⟨t, ht, hts⟩ := ih hs' (Nat.lt_succ_iff.1 h)
      exact ⟨t, ht, le_trans hts (le_oplus_left hp)⟩
    · exact ⟨s, hs, le_rfl⟩

theorem IsNSum.add {a : E} {m n : ℕ} {s t : E} (hs : IsNSum a m s) (ht : IsNSum a n t)
    (hst : Perp s t) : IsNSum a (m + n) (s ⋎ t) := by
  induction n generalizing t with
  | zero => cases ht; rw [oplus_zero]; exact hs
  | succ n ih =>
    obtain ⟨t', ht', hp, rfl⟩ := isNSum_succ_iff.1 ht
    obtain ⟨h1, h2⟩ := perp_assoc_left hp hst
    rw [← oplus_assoc h1 h2]
    exact (ih ht' h1).succ h2

theorem IsNSum.of_le {a b : E} {n : ℕ} {s : E} (hs : IsNSum a n s) (hba : b ≤ a) :
    ∃ t, IsNSum b n t ∧ t ≤ s := by
  induction n generalizing s with
  | zero => cases hs; exact ⟨0, IsNSum.zero, le_rfl⟩
  | succ n ih =>
    obtain ⟨s', hs', hp, rfl⟩ := isNSum_succ_iff.1 hs
    obtain ⟨t, ht, hts⟩ := ih hs'
    have hp' : Perp t b := perp_of_le hts hba hp
    exact ⟨_, ht.succ hp', oplus_le_oplus hts hba hp⟩

/-- **OAP 26** (`lem:archemedeanomegadirectedcomplete`, first.tex:876,
Lemma), point 1: in an ω-complete effect algebra, if `na` exists for all
`n` then `a = 0`.  (The print states it for an ω-complete effect *monoid*;
the proof uses only the effect algebra structure — cf. the commented-out
version at first.tex:917, which is stated for effect algebras.) -/
theorem oap26_1 [OmegaComplete E] {a : E} (h : ∀ n, ∃ s, IsNSum a n s) : a = 0 := by
  choose f hf using h
  have hsucc : ∀ n, f (n + 1) = f n ⋎ a ∧ Perp (f n) a := by
    intro n
    obtain ⟨t, ht, hp, e⟩ := isNSum_succ_iff.1 (hf (n + 1))
    rw [ht.unique (hf n)] at hp e
    exact ⟨e, hp⟩
  have hmono : Monotone f :=
    monotone_nat_of_le_succ fun n => by rw [(hsucc n).1]; exact le_oplus_left (hsucc n).2
  obtain ⟨s, hs⟩ := OmegaComplete.exists_isLUB f hmono
  -- `a ⋁ ⋁ₙ na = ⋁ₙ (a ⋁ na) = ⋁ₙ (n+1)a = ⋁ₙ na`
  obtain ⟨has, h1⟩ := oap24_1 (Set.range_nonempty f)
    (by rintro _ ⟨n, rfl⟩; exact perp_iff_le_orth.1 (hsucc n).2) hs
  have himg : (a ⋎ ·) '' Set.range f = Set.range (fun n => f (n + 1)) := by
    rw [← Set.range_comp]; congr 1; funext n
    simp only [Function.comp_apply, (hsucc n).1, oplus_comm]
  rw [himg] at h1
  have h2 : IsLUB (Set.range fun n => f (n + 1)) s := by
    refine ⟨fun _ ⟨n, e⟩ => e ▸ hs.1 ⟨n + 1, rfl⟩, fun u hu => hs.2 ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero =>
      have : f 0 = 0 := (hf 0).unique IsNSum.zero
      rw [this]; exact zero_le' u
    | succ n => exact hu ⟨n, rfl⟩
  have e : a ⋎ s = 0 ⋎ s := by rw [h1.unique h2, zero_oplus]
  exact oplus_right_cancel has (zero_perp s) e

end NSum


/-! ## Effect monoids -/

section EMBasic

variable {M : Type u} [EffectMonoid M]

/-- An effect monoid is a monoid under `·` (used for the powers `aⁿ`). -/
@[reducible] def emMonoid (M : Type u) [EffectMonoid M] : Monoid M where
  mul := (· * ·)
  one := 1
  mul_assoc := EffectMonoid.mul_assoc
  one_mul := EffectMonoid.one_mul
  mul_one := EffectMonoid.mul_one

attribute [scoped instance 100] emMonoid

theorem mul_oplus (a : M) {b c : M} (h : Perp b c) :
    Perp (a * b) (a * c) ∧ a * (b ⋎ c) = a * b ⋎ a * c := by
  obtain ⟨h', e⟩ := emon_mul_ovee a h
  exact ⟨h', by rw [oplus_eq h, oplus_eq h', e]⟩

theorem oplus_mul (a : M) {b c : M} (h : Perp b c) :
    Perp (b * a) (c * a) ∧ (b ⋎ c) * a = b * a ⋎ c * a := by
  obtain ⟨h', e⟩ := emon_ovee_mul a h
  exact ⟨h', by rw [oplus_eq h, oplus_eq h', e]⟩

@[simp] theorem emul_zero (a : M) : a * 0 = 0 := (exc_emonzero a).1

@[simp] theorem ezero_mul (a : M) : (0 : M) * a = 0 := (exc_emonzero a).2

@[simp] theorem emul_one (a : M) : a * 1 = a := EffectMonoid.mul_one a

@[simp] theorem eone_mul (a : M) : (1 : M) * a = a := EffectMonoid.one_mul a

theorem emul_assoc (a b c : M) : a * b * c = a * (b * c) := EffectMonoid.mul_assoc a b c

theorem emul_le_left (a b : M) : a * b ≤ a := emon_mul_le_self a b

theorem emul_le_right (a b : M) : a * b ≤ b := emon_mul_le_self_right a b

theorem emul_le_emul_left (a : M) {b c : M} (h : b ≤ c) : a * b ≤ a * c :=
  emon_mul_mono_right a h

theorem emul_le_emul_right {b c : M} (h : b ≤ c) (a : M) : b * a ≤ c * a :=
  emon_mul_mono_left h a

/-- `a·b ⋁ a·b^⊥ = a`. -/
theorem emul_oplus_emul_orth (a b : M) :
    Perp (a * b) (a * orth b) ∧ a * b ⋎ a * orth b = a := by
  obtain ⟨h, e⟩ := mul_oplus a (perp_orth b)
  rw [oplus_orth, emul_one] at e
  exact ⟨h, e.symm⟩

/-- `b·a ⋁ b^⊥·a = a`. -/
theorem emul_oplus_orth_emul (b a : M) :
    Perp (b * a) (orth b * a) ∧ b * a ⋎ orth b * a = a := by
  obtain ⟨h, e⟩ := oplus_mul a (perp_orth b)
  rw [oplus_orth, eone_mul] at e
  exact ⟨h, e.symm⟩

theorem emul_pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a := pow_succ a n

/-- **OAP 5** (`def:effectmonoid`, first.tex:447, Definition): the tree's
effect monoid (thesis B 178II, a four-fold distributive law) satisfies the
print's axiom *Distributivity*: `·` is bi-additive. -/
theorem oap5_distrib (a : M) {b c : M} (h : Perp b c) :
    Perp (a * b) (a * c) ∧ Perp (b * a) (c * a) ∧
      a * (b ⋎ c) = a * b ⋎ a * c ∧ (b ⋎ c) * a = b * a ⋎ c * a :=
  ⟨(mul_oplus a h).1, (oplus_mul a h).1, (mul_oplus a h).2, (oplus_mul a h).2⟩

/-- **OAP 5** (`def:effectmonoid`, first.tex:447, Definition): conversely,
an effect algebra with a unital associative bi-additive operation — the
print's definition — is an effect monoid in the tree's sense. -/
def EffectMonoid.ofBiadditive (M : Type u) [EffectAlgebra M] [Mul M]
    (one_mul : ∀ a : M, 1 * a = a) (mul_one : ∀ a : M, a * 1 = a)
    (mul_assoc : ∀ a b c : M, a * (b * c) = a * b * c)
    (left : ∀ (a : M) {b c : M}, Perp b c → Perp (a * b) (a * c) ∧ a * (b ⋎ c) = a * b ⋎ a * c)
    (right : ∀ (a : M) {b c : M}, Perp b c → Perp (b * a) (c * a) ∧ (b ⋎ c) * a = b * a ⋎ c * a) :
    EffectMonoid M :=
  { ‹EffectAlgebra M›, ‹Mul M› with
    one_mul := one_mul
    mul_one := mul_one
    mul_assoc := fun a b c => (mul_assoc a b c).symm
    distrib := by
      intro a b c d hab hcd
      rw [← oplus_eq hab, ← oplus_eq hcd]
      obtain ⟨h1, e1⟩ := right c hab
      obtain ⟨h2, e2⟩ := right d hab
      obtain ⟨h3, e3⟩ := left (a ⋎ b) hcd
      rw [e3, e1, e2] at *
      exact isSumOf_append.2 ⟨_, _, isSumOf_pair.2 ⟨h1, rfl⟩, isSumOf_pair.2 ⟨h2, rfl⟩,
        h3, rfl⟩ }

/-- **OAP 5** (`def:effectmonoid`, first.tex:447, Definition): `p` is
**idempotent** when `p² = p`. -/
def IsIdempotent (p : M) : Prop := p * p = p

/-- **OAP 5** (`def:effectmonoid`, first.tex:447, Definition): the set
`P(M)` of idempotents. -/
def idempotents (M : Type u) [EffectMonoid M] : Set M := {p | p * p = p}

/-- **OAP 5** (`def:effectmonoid`, first.tex:447, Definition): `a` and `b` are
**orthogonal** when `a·b = b·a = 0`. -/
def Orthogonal (a b : M) : Prop := a * b = 0 ∧ b * a = 0

/-! ### §4: OAP 17–20, 23, 25, 26 -/

/-- **OAP 17** (`lem:ssperpcommute`, first.tex:667, Lemma): `a·a^⊥ = a^⊥·a`.
The tree proves it (`emon_mul_orth_comm`) by the print's argument: both
`a² ⋁ a^⊥·a` and `a² ⋁ a·a^⊥` equal `a`; cancel `a²`. -/
theorem oap17 (a : M) : a * orth a = orth a * a := emon_mul_orth_comm a

/-- **OAP 18** (`lem:idempotentiff`, first.tex:678, Lemma): `p` is idempotent
iff `p·p^⊥ = 0`. -/
theorem oap18 (p : M) : p * p = p ↔ p * orth p = 0 := by
  -- `p = p·1 = p·(p ⋁ p^⊥) = p² ⋁ p·p^⊥`
  obtain ⟨h, e⟩ := emul_oplus_emul_orth p p
  constructor
  · intro hp
    rw [hp] at h e
    exact oplus_left_cancel h (perp_zero p) (by rw [e, oplus_zero])
  · intro h0
    rw [h0, oplus_zero] at e; exact e

theorem idem_orth {p : M} (hp : p * p = p) : orth p * orth p = orth p := by
  rw [oap18, orth_orth, ← oap17]; exact (oap18 p).1 hp

theorem emul_orth_eq_zero_of_le {p a : M} (hp : p * p = p) (ha : a ≤ p) :
    a * orth p = 0 :=
  eq_zero_of_le_zero ((oap18 p).1 hp ▸ emul_le_emul_right ha (orth p))

theorem orth_emul_eq_zero_of_le {p a : M} (hp : p * p = p) (ha : a ≤ p) :
    orth p * a = 0 :=
  eq_zero_of_le_zero (by
    have := emul_le_emul_left (orth p) ha
    rwa [← oap17, (oap18 p).1 hp] at this)

/-- **OAP 19** (`lem:preserveunderidempotent`, first.tex:686, Lemma): for an
idempotent `p`, `p·a = a ⟺ a·p = a ⟺ a ≤ p`. -/
theorem oap19 {p a : M} (hp : p * p = p) :
    (p * a = a ↔ a * p = a) ∧ (a * p = a ↔ a ≤ p) := by
  have h1 : a ≤ p → a * p = a ∧ p * a = a := by
    intro ha
    refine ⟨?_, ?_⟩
    · obtain ⟨-, e⟩ := emul_oplus_emul_orth a p
      rwa [emul_orth_eq_zero_of_le hp ha, oplus_zero] at e
    · obtain ⟨-, e⟩ := emul_oplus_orth_emul p a
      rwa [orth_emul_eq_zero_of_le hp ha, oplus_zero] at e
  have h2 : p * a = a → a ≤ p := fun e => e ▸ emul_le_left p a
  have h3 : a * p = a → a ≤ p := fun e => e ▸ emul_le_right a p
  exact ⟨⟨fun e => (h1 (h2 e)).1, fun e => (h1 (h3 e)).2⟩, ⟨h3, fun h => (h1 h).1⟩⟩

theorem emul_eq_of_le {p a : M} (hp : p * p = p) (ha : a ≤ p) : p * a = a :=
  (oap19 hp).1.2 ((oap19 hp).2.2 ha)

theorem emul_eq_of_le' {p a : M} (hp : p * p = p) (ha : a ≤ p) : a * p = a :=
  (oap19 hp).2.2 ha

/-- **OAP 20** (`lem:idempotentscommute`, first.tex:707, Lemma): an idempotent
commutes with every element. -/
theorem oap20 {p : M} (hp : p * p = p) (a : M) : p * a = a * p := by
  have e1 : p * a * p = p * a := emul_eq_of_le' hp (emul_le_left p a)
  have e2 : p * (a * p) = a * p := emul_eq_of_le hp (emul_le_right a p)
  rw [← e1, emul_assoc, e2]

/-- **OAP 23** (`lem:summableunderidempotent`, first.tex:744, Lemma): if
`a, b ≤ p` for an idempotent `p` and `a ⋁ b` exists, then `a ⋁ b ≤ p`. -/
theorem oap23 {p a b : M} (hp : p * p = p) (ha : a ≤ p) (hb : b ≤ p) (h : Perp a b) :
    a ⋎ b ≤ p := by
  -- `(a ⋁ b)·p^⊥ = a·p^⊥ ⋁ b·p^⊥ = 0`, so `(a ⋁ b)·p = a ⋁ b`
  have h0 : (a ⋎ b) * orth p = 0 := by
    rw [(oplus_mul (orth p) h).2, emul_orth_eq_zero_of_le hp ha,
      emul_orth_eq_zero_of_le hp hb, oplus_zero]
  obtain ⟨-, e⟩ := emul_oplus_emul_orth (a ⋎ b) p
  rw [h0, oplus_zero] at e
  exact (oap19 hp).2.1 e

/-- **OAP 25** (`lem:selfsummable`, first.tex:864, Lemma): `a·a^⊥` is
summable with itself. -/
theorem oap25 (a : M) : Perp (a * orth a) (a * orth a) := by
  -- `1 = (a ⋁ a^⊥)·(a ⋁ a^⊥) = a·a ⋁ a^⊥·a ⋁ a·a^⊥ ⋁ a^⊥·a^⊥`
  have hd := EffectMonoid.distrib (perp_orth a) (perp_orth a)
  obtain ⟨t1, ht1, -, -⟩ := isSumOf_cons'.1 hd
  obtain ⟨t2, ht2, hp2, rfl⟩ := isSumOf_cons'.1 ht1
  obtain ⟨t3, -, hp3, rfl⟩ := isSumOf_cons'.1 ht2
  have := perp_of_le le_rfl (le_oplus_left hp3) hp2
  rwa [← oap17] at this

theorem perp_self_of_sq_zero {a : M} (h : a * a = 0) : Perp a a := by
  obtain ⟨-, e⟩ := emul_oplus_emul_orth a a
  rw [h, zero_oplus] at e
  have := oap25 a
  rwa [e] at this

theorem sq_oplus_self {a : M} (hp : Perp a a) (h : a * a = 0) : (a ⋎ a) * (a ⋎ a) = 0 := by
  rw [(mul_oplus (a ⋎ a) hp).2, (oplus_mul a hp).2, h, oplus_zero, zero_oplus]

theorem IsNSum.emul_right {x y : M} {k : ℕ} {s : M} (hs : IsNSum x k s) :
    IsNSum (x * y) k (s * y) := by
  induction k generalizing s with
  | zero => cases hs; rw [ezero_mul]; exact IsNSum.zero
  | succ k ih =>
    obtain ⟨t, ht, hp, rfl⟩ := isNSum_succ_iff.1 hs
    obtain ⟨hp', e⟩ := oplus_mul y hp
    rw [e]; exact (ih ht).succ hp'

theorem exists_isNSum_of_two_pow {a : M} (h : ∀ k : ℕ, ∃ s, IsNSum a (2 ^ k) s) (n : ℕ) :
    ∃ s, IsNSum a n s := by
  obtain ⟨s, hs⟩ := h n
  obtain ⟨t, ht, -⟩ := hs.le_of_le (Nat.lt_two_pow_self).le
  exact ⟨t, ht⟩

/-- **OAP 26** (`lem:archemedeanomegadirectedcomplete`, first.tex:876,
Lemma), point 2: in an ω-complete effect monoid `a² = 0` implies `a = 0`. -/
theorem oap26_2 [OmegaComplete M] {a : M} (h : a * a = 0) : a = 0 := by
  -- `2ᵏa` exists and squares to `0`, for every `k`
  have key : ∀ k : ℕ, ∃ s, IsNSum a (2 ^ k) s ∧ s * s = 0 := by
    intro k
    induction k with
    | zero => exact ⟨a, by simpa using isNSum_one a, h⟩
    | succ k ih =>
      obtain ⟨s, hs, hs0⟩ := ih
      have hp := perp_self_of_sq_zero hs0
      refine ⟨s ⋎ s, ?_, sq_oplus_self hp hs0⟩
      rw [pow_succ, mul_two]
      exact hs.add hs hp
  exact oap26_1 (exists_isNSum_of_two_pow fun k => (key k).imp fun _ h => h.1)

/-- **OAP 26** (`lem:archemedeanomegadirectedcomplete`, first.tex:876,
Lemma), point 3: in an ω-complete effect monoid, if `a ⊥ a` then
`⋀ₙ aⁿ = 0` (the infimum existing). -/
theorem oap26_3 [OmegaComplete M] {a : M} (h : Perp a a) :
    IsGLB (Set.range fun n : ℕ => a ^ n) 0 := by
  have hanti : Antitone fun n : ℕ => a ^ n :=
    antitone_nat_of_succ_le fun n => by rw [emul_pow_succ]; exact emul_le_left _ _
  obtain ⟨b, hb⟩ := OmegaComplete.exists_isGLB _ hanti
  -- `(2a)ⁿ = 2ⁿaⁿ`
  have key : ∀ n : ℕ, IsNSum (a ^ n) (2 ^ n) ((a ⋎ a) ^ n) := by
    intro n
    induction n with
    | zero => simpa using isNSum_one (1 : M)
    | succ n ih =>
      obtain ⟨hp, e⟩ := mul_oplus ((a ⋎ a) ^ n) h
      rw [emul_pow_succ, emul_pow_succ, e, pow_succ 2, mul_two]
      exact ih.emul_right.add ih.emul_right hp
  -- `b ≤ aⁿ`, so `2ⁿb` exists for all `n`
  have hb0 : b = 0 := oap26_1 (exists_isNSum_of_two_pow fun k => by
    obtain ⟨t, ht, -⟩ := (key k).of_le (hb.1 ⟨k, rfl⟩)
    exact ⟨t, ht⟩)
  exact hb0 ▸ hb

end EMBasic


/-! ## §2 Examples and constructions: OAP 8, 11, 12, 21 -/

section Constructions

/-- **OAP 8** (first.tex:506, Definition): an **embedding** of effect monoids
is an order-reflecting effect monoid morphism (the morphisms are the tree's
`EffectMonoidHom`, 178II). -/
structure EMEmbedding (M : Type u) (N : Type v) [EffectMonoid M] [EffectMonoid N]
    extends EffectMonoidHom M N where
  reflect : ∀ {a b : M}, toFun a ≤ toFun b → a ≤ b

/-- **OAP 8** (first.tex:506, Definition): an isomorphism of effect monoids:
a bijective morphism whose inverse is a morphism. -/
def EMIsIso {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) : Prop :=
  ∃ g : EffectMonoidHom N M, (∀ a, g.toFun (f.toFun a) = a) ∧ ∀ b, f.toFun (g.toFun b) = b

/-- **OAP 8** (first.tex:506, Definition): "an isomorphism of effect monoids
is the same thing as a surjective embedding of effect monoids". -/
theorem oap8_isIso_iff {M N : Type u} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) :
    EMIsIso f ↔ Function.Surjective f.toFun ∧ ∀ {a b : M}, f.toFun a ≤ f.toFun b → a ≤ b := by
  constructor
  · rintro ⟨g, hgf, hfg⟩
    exact (oap1_isIso_iff f.toEAHom).1 ⟨g.toEAHom, hgf, hfg⟩
  · intro h
    obtain ⟨g, hgf, hfg⟩ := (oap1_isIso_iff f.toEAHom).2 h
    have hinj : Function.Injective f.toFun := fun a b e => by rw [← hgf a, ← hgf b]; exact congrArg _ e
    refine ⟨{ g with map_mul := fun x y => hinj ?_ }, hgf, hfg⟩
    show f.toFun (g.toFun (x * y)) = f.toFun (g.toFun x * g.toFun y)
    rw [f.map_mul, hfg, hfg, hfg]

theorem prod_oplus {M N : Type u} [EffectAlgebra M] [EffectAlgebra N] {x y : M × N}
    (h : Perp x y) : x ⋎ y = (x.1 ⋎ y.1, x.2 ⋎ y.2) := by
  rw [oplus_eq h, oplus_eq h.1, oplus_eq h.2]; rfl

theorem prod_le_iff {M N : Type u} [EffectAlgebra M] [EffectAlgebra N] {x y : M × N} :
    @LE.le _ (@Preorder.toLE _ (@PartialOrder.toPreorder _ (eaPartialOrder (M × N)))) x y ↔
      x.1 ≤ y.1 ∧ x.2 ≤ y.2 := by
  show PCM.le x y ↔ _
  constructor
  · rintro ⟨c, h, e⟩
    exact ⟨⟨c.1, h.1, congrArg Prod.fst e⟩, ⟨c.2, h.2, congrArg Prod.snd e⟩⟩
  · rintro ⟨⟨c, h, e⟩, ⟨d, h', e'⟩⟩
    exact ⟨(c, d), ⟨h, h'⟩, Prod.ext e e'⟩

/-- **OAP 11** (first.tex:527, Example): the **direct sum** `M₁ ⊕ M₂` of two
effect monoids — the cartesian product with pointwise operations — is an
effect monoid.  (For effect algebras this is the tree's `prodEffectAlgebra`,
thesis B 175III.) -/
instance prodEffectMonoid (M N : Type u) [EffectMonoid M] [EffectMonoid N] :
    EffectMonoid (M × N) :=
  EffectMonoid.ofBiadditive (M × N)
    (fun a => Prod.ext (eone_mul a.1) (eone_mul a.2))
    (fun a => Prod.ext (emul_one a.1) (emul_one a.2))
    (fun a b c => Prod.ext (emul_assoc _ _ _).symm (emul_assoc _ _ _).symm)
    (fun a _ _ h => by
      have h' : Perp (a * _) (a * _) := ⟨(mul_oplus a.1 h.1).1, (mul_oplus a.2 h.2).1⟩
      refine ⟨h', ?_⟩
      rw [prod_oplus h, prod_oplus h']
      exact Prod.ext (mul_oplus a.1 h.1).2 (mul_oplus a.2 h.2).2)
    (fun a _ _ h => by
      have h' : Perp (_ * a) (_ * a) := ⟨(oplus_mul a.1 h.1).1, (oplus_mul a.2 h.2).1⟩
      refine ⟨h', ?_⟩
      rw [prod_oplus h, prod_oplus h']
      exact Prod.ext (oplus_mul a.1 h.1).2 (oplus_mul a.2 h.2).2)

variable {M : Type u} [EffectMonoid M]

/-- **OAP 12** (`cornersexample`, first.tex:534, Example): the **left corner**
`pM ≡ {p·a ; a ∈ M}`. -/
def leftCorner (p : M) : Set M := Set.range (p * ·)

theorem leftCorner_eq_Iic {p : M} (hp : p * p = p) : leftCorner p = Set.Iic p := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact emul_le_left p a
  · intro hx; exact ⟨x, emul_eq_of_le hp hx⟩

theorem le_of_mem_leftCorner {p : M} (hp : p * p = p) {x : M} (hx : x ∈ leftCorner p) :
    x ≤ p := by rw [leftCorner_eq_Iic hp] at hx; exact hx

theorem mem_leftCorner_of_le {p : M} (hp : p * p = p) {x : M} (hx : x ≤ p) :
    x ∈ leftCorner p := by rw [leftCorner_eq_Iic hp]; exact hx

/-- **OAP 12** (`cornersexample`, first.tex:534, Example): the effect algebra
structure of the corner `pM`: sums inherited from `M` (they stay in `pM` by
OAP 23), unit `p`, and complement `(p·a)^⊥ ≡ p·a^⊥` — computed here at the
representative `a = x` of `x ∈ pM` (`x = p·x` by OAP 19; independence of the
representative is `corner_orth_mk`). -/
noncomputable def cornerEffectAlgebra (p : M) (hp : p * p = p) : EffectAlgebra (leftCorner p) where
  zero := ⟨0, 0, emul_zero p⟩
  one := ⟨p, 1, emul_one p⟩
  Perp x y := Perp x.1 y.1
  ovee x y h := ⟨x.1 ⋎ y.1, mem_leftCorner_of_le hp
    (oap23 hp (le_of_mem_leftCorner hp x.2) (le_of_mem_leftCorner hp y.2) h)⟩
  orth x := ⟨p * orth x.1, orth x.1, rfl⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (oplus_comm _ _)
  perp_of_ovee_perp hab h := perp_of_oplus_perp hab h
  perp_ovee_of_ovee_perp hab h := perp_oplus_of_oplus_perp hab h
  ovee_assoc hab h := Subtype.ext (oplus_assoc hab h)
  zero_perp a := zero_perp a.1
  zero_ovee a := Subtype.ext (zero_oplus a.1)
  perp_orth x := by
    show Perp x.1 (p * orth x.1)
    have := (mul_oplus p (perp_orth x.1)).1
    rwa [emul_eq_of_le hp (le_of_mem_leftCorner hp x.2)] at this
  ovee_orth x := by
    apply Subtype.ext
    show x.1 ⋎ p * orth x.1 = p
    have := (mul_oplus p (perp_orth x.1)).2
    rwa [emul_eq_of_le hp (le_of_mem_leftCorner hp x.2), oplus_orth, emul_one, eq_comm] at this
  orth_unique := by
    intro x y h e
    apply Subtype.ext
    have e : x.1 ⋎ y.1 = p := congrArg Subtype.val e
    show y.1 = p * orth x.1
    have h2 := mul_oplus p (perp_orth x.1)
    rw [emul_eq_of_le hp (le_of_mem_leftCorner hp x.2), oplus_orth, emul_one] at h2
    exact oplus_left_cancel h h2.1 (e.trans h2.2)
  eq_zero_of_perp_one := by
    intro x h
    apply Subtype.ext
    have h : Perp x.1 p := h
    have hx : x.1 ≤ p := le_of_mem_leftCorner hp x.2
    -- `x ≤ p^⊥` and `x ≤ p` force `x = x·p = 0`
    have h1 : x.1 * orth (orth p) = 0 :=
      emul_orth_eq_zero_of_le (idem_orth hp) (perp_iff_le_orth.1 h)
    rw [orth_orth, emul_eq_of_le' hp hx] at h1
    exact h1

theorem corner_oplus {p : M} (hp : p * p = p) {x y : leftCorner p}
    (h : @Perp _ (cornerEffectAlgebra p hp).toPCM x y) :
    (@oplus _ (cornerEffectAlgebra p hp) x y).1 = x.1 ⋎ y.1 := by
  let _ := cornerEffectAlgebra p hp
  rw [oplus_eq h]; rfl

theorem corner_le_iff {p : M} (hp : p * p = p) {x y : leftCorner p} :
    @LE.le _ (@Preorder.toLE _ (@PartialOrder.toPreorder _
      (@eaPartialOrder _ (cornerEffectAlgebra p hp)))) x y ↔ x.1 ≤ y.1 := by
  let _ := cornerEffectAlgebra p hp
  constructor
  · rintro ⟨c, h, e⟩
    exact le_def.2 ⟨c.1, h, by rw [← congrArg Subtype.val e]; rfl⟩
  · intro hxy
    have hy : y.1 ≤ p := le_of_mem_leftCorner hp y.2
    refine ⟨⟨y.1 ⊖ x.1, mem_leftCorner_of_le hp (le_trans (osub_le hxy) hy)⟩,
      perp_osub hxy, Subtype.ext ?_⟩
    exact oplus_osub hxy

/-- **OAP 12** (`cornersexample`, first.tex:534, Example): the corner `pM` of
an idempotent `p` is an effect monoid, with the multiplication of `M`. -/
noncomputable def cornerEffectMonoid (p : M) (hp : p * p = p) : EffectMonoid (leftCorner p) :=
  letI := cornerEffectAlgebra p hp
  letI : Mul (leftCorner p) := ⟨fun x y => ⟨x.1 * y.1, mem_leftCorner_of_le hp
    (le_trans (emul_le_left _ _) (le_of_mem_leftCorner hp x.2))⟩⟩
  EffectMonoid.ofBiadditive (leftCorner p)
    (fun a => Subtype.ext (emul_eq_of_le hp (le_of_mem_leftCorner hp a.2)))
    (fun a => Subtype.ext (emul_eq_of_le' hp (le_of_mem_leftCorner hp a.2)))
    (fun a b c => Subtype.ext (emul_assoc a.1 b.1 c.1).symm)
    (fun a b c h => by
      have h' : Perp (a * b) (a * c) := (mul_oplus a.1 h).1
      refine ⟨h', Subtype.ext ?_⟩
      show a.1 * (b ⋎ c).1 = (a * b ⋎ a * c).1
      rw [corner_oplus hp h, corner_oplus hp h']
      exact (mul_oplus a.1 h).2)
    (fun a b c h => by
      have h' : Perp (b * a) (c * a) := (oplus_mul a.1 h).1
      refine ⟨h', Subtype.ext ?_⟩
      show (b ⋎ c).1 * a.1 = (b * a ⋎ c * a).1
      rw [corner_oplus hp h, corner_oplus hp h']
      exact (oplus_mul a.1 h).2)

/-- **OAP 12** (`cornersexample`, first.tex:534, Example): the complement of
the corner is `(p·a)^⊥ = p·a^⊥` for *every* representative `a`. -/
theorem corner_orth_mk {p : M} (hp : p * p = p) (a : M) :
    (@orth _ (cornerEffectAlgebra p hp) ⟨p * a, a, rfl⟩).1 = p * orth a := by
  show p * orth (p * a) = p * orth a
  have h1 := mul_oplus p (perp_orth (p * a))
  have h2 := mul_oplus p (perp_orth a)
  rw [oplus_orth, emul_one, ← emul_assoc, hp] at h1
  rw [oplus_orth, emul_one] at h2
  exact oplus_left_cancel h1.1 h2.1 (h1.2.symm.trans h2.2)

/-- **OAP 12** (`cornersexample`, first.tex:534, Example): "Analogous facts
hold for the right corner `Mp`" — indeed `Mp = pM` (OAP 20). -/
theorem oap12_rightCorner {p : M} (hp : p * p = p) :
    Set.range (· * p) = leftCorner p := by
  ext x; simp only [leftCorner, Set.mem_range, oap20 hp]

/-- **OAP 21** (`cor:corneriso`, first.tex:718, Corollary): for an idempotent
`p`, the map `e ↦ (p·e, p^⊥·e)` is an isomorphism `M ≅ pM ⊕ p^⊥M`. -/
theorem oap21 {p : M} (hp : p * p = p) :
    letI := cornerEffectMonoid p hp
    letI := cornerEffectMonoid (orth p) (idem_orth hp)
    ∃ f : EffectMonoidHom M (leftCorner p × leftCorner (orth p)),
      (∀ e, f.toFun e = (⟨p * e, e, rfl⟩, ⟨orth p * e, e, rfl⟩)) ∧ EMIsIso f := by
  let _ := cornerEffectMonoid p hp
  let _ := cornerEffectMonoid (orth p) (idem_orth hp)
  have hq := idem_orth hp
  let φ : M → leftCorner p × leftCorner (orth p) :=
    fun e => (⟨p * e, e, rfl⟩, ⟨orth p * e, e, rfl⟩)
  have hperp : ∀ {e f : M}, Perp e f → Perp (φ e) (φ f) :=
    fun h => ⟨(mul_oplus p h).1, (mul_oplus (orth p) h).1⟩
  let f : EffectMonoidHom M (leftCorner p × leftCorner (orth p)) :=
    { toFun := φ
      perp_map := hperp
      ovee_map := fun {e f} h => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show p * ovee e f h = p * e ⋎ p * f
          rw [← oplus_eq h]; exact (mul_oplus p h).2
        · show orth p * ovee e f h = orth p * e ⋎ orth p * f
          rw [← oplus_eq h]; exact (mul_oplus (orth p) h).2
      map_one := Prod.ext (Subtype.ext (emul_one p)) (Subtype.ext (emul_one (orth p)))
      map_mul := fun e f => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show p * (e * f) = p * e * (p * f)
          rw [emul_assoc, ← emul_assoc e p f, ← oap20 hp e, emul_assoc, ← emul_assoc p p, hp]
        · show orth p * (e * f) = orth p * e * (orth p * f)
          rw [emul_assoc, ← emul_assoc e (orth p) f, ← oap20 hq e, emul_assoc,
            ← emul_assoc (orth p) (orth p), hq] }
  refine ⟨f, fun e => rfl, (oap8_isIso_iff f).2 ⟨?_, ?_⟩⟩
  · -- surjective: `(x, y) = φ (x ⋁ y)`
    rintro ⟨x, y⟩
    have hx : x.1 ≤ p := le_of_mem_leftCorner hp x.2
    have hy : y.1 ≤ orth p := le_of_mem_leftCorner hq y.2
    have hxy : Perp x.1 y.1 := perp_iff_le_orth.2
      (le_trans hx (by rw [← orth_le_orth_iff, orth_orth]; exact hy))
    refine ⟨x.1 ⋎ y.1, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · show p * (x.1 ⋎ y.1) = x.1
      have h0 : p * y.1 = 0 := by
        have := orth_emul_eq_zero_of_le hq hy; rwa [orth_orth] at this
      rw [(mul_oplus p hxy).2, emul_eq_of_le hp hx, h0, oplus_zero]
    · show orth p * (x.1 ⋎ y.1) = y.1
      rw [(mul_oplus (orth p) hxy).2, emul_eq_of_le hq hy,
        orth_emul_eq_zero_of_le hp hx, zero_oplus]
  · -- order reflecting: `e = p·e ⋁ p^⊥·e ≤ p·f ⋁ p^⊥·f = f`
    intro e f h
    have h := prod_le_iff.1 h
    have h1 := (corner_le_iff hp).1 h.1
    have h2 := (corner_le_iff hq).1 h.2
    obtain ⟨he, ee⟩ := emul_oplus_orth_emul p e
    obtain ⟨hf, ef⟩ := emul_oplus_orth_emul p f
    rw [← ee, ← ef]
    exact oplus_le_oplus h1 h2 hf

end Constructions

/-! ## §2 Examples: OAP 2, 3, 6, 7, 9, 15, 16 -/

section Examples

/-! ### OAP 2: orthomodular lattices -/

namespace MO2

/-- The orthomodular lattice `MO2` ("Chinese lantern"): `⊥ < a, a', b, b' < ⊤`
with `a^⊥ = a'`, `b^⊥ = b'`. -/
inductive T where
  | bot | top | a | a' | b | b'
  deriving DecidableEq

open T

/-- The order of `MO2`, as a boolean table. -/
def leb : T → T → Bool
  | bot, _ => true
  | _, top => true
  | x, y => decide (x = y)

instance : LE T := ⟨fun x y => leb x y = true⟩

instance : DecidableRel (α := T) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (leb x y = true))

instance : Fintype T where
  elems := ⟨[bot, top, a, a', b, b'], by decide⟩
  complete := by intro x; cases x <;> decide

def sup' (x y : T) : T := if leb x y then y else if leb y x then x else top

def inf' (x y : T) : T := if leb x y then x else if leb y x then y else bot

def compl' : T → T
  | bot => top | top => bot | a => a' | a' => a | b => b' | b' => b

instance : Lattice T where
  le := (· ≤ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := sup'
  inf := inf'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder T where
  top := top
  le_top := by decide
  bot := bot
  bot_le := by decide

instance : Compl T := ⟨compl'⟩

instance : OrthomodularLattice T where
  inf_compl := by decide
  sup_compl := by decide
  compl_antitone := by decide
  compl_compl := by decide
  orthomodular := by decide

end MO2

/-- **OAP 2** (`ex:orthomodularlattice`, first.tex:390, Example) **is false as
printed**: with `x ⊥ y ⟺ x ∧ y = 0`, `x ⋁ y = x ∨ y` and the orthocomplement
as complement, an orthomodular lattice is in general *not* an effect
algebra.  In `MO2` the atoms `a`, `b` have `a ∧ b = 0` and `a ∨ b = 1`, so
uniqueness of the complement would force `b = a^⊥ = a'`.  The correct
orthogonality is `x ⊥ y ⟺ x ≤ y^⊥` (the tree's `orthomodularEffectAlgebra`,
thesis B 175II.4); the two agree in a Boolean algebra. -/
theorem oap2_false_as_printed :
    ∃ (L : Type) (_ : OrthomodularLattice L),
      ¬ ∃ inst : EffectAlgebra L,
        (∀ x y : L, @Perp L inst.toPCM x y ↔ x ⊓ y = ⊥) ∧
        (∀ (x y : L) (h : @Perp L inst.toPCM x y), @ovee L inst.toPCM x y h = x ⊔ y) ∧
        ∀ x : L, @orth L inst x = xᶜ := by
  refine ⟨MO2.T, inferInstance, ?_⟩
  rintro ⟨inst, hP, hO, hC⟩
  have hab : @Perp MO2.T inst.toPCM MO2.T.a MO2.T.b := (hP _ _).2 (by decide)
  have hone := @EffectAlgebra.ovee_orth MO2.T inst MO2.T.a
  rw [hO, hC] at hone
  have e : @ovee MO2.T inst.toPCM _ _ hab = 1 := by
    rw [hO, ← hone]; decide
  have := @EffectAlgebra.orth_unique MO2.T inst _ _ hab e
  rw [hC] at this
  exact absurd this (by decide)

/-- **OAP 2** (`ex:orthomodularlattice`, first.tex:390, Example), with the
orthogonality repaired to `x ⊥ y ⟺ x ≤ y^⊥` (the tree's
`orthomodularEffectAlgebra`): "the lattice order coincides with the effect
algebra order". -/
theorem oap2_le_iff (L : Type u) [OrthomodularLattice L] (x y : L) :
    @PCM.le L (orthomodularEffectAlgebra L).toPCM x y ↔ x ≤ y := by
  let _ := orthomodularEffectAlgebra L
  constructor
  · rintro ⟨c, -, rfl⟩; exact le_sup_left
  · intro h
    refine ⟨xᶜ ⊓ y, ?_, OrthomodularLattice.orthomodular h⟩
    show x ≤ (xᶜ ⊓ y)ᶜ
    exact Ortholattice.le_compl_comm inf_le_left

/-! ### OAP 3: order intervals of ordered groups -/

/-- **OAP 3** (`ex:cstaralgebra`, first.tex:397, Example): for an ordered
abelian group `G` and `u ≥ 0` the interval `[0,u]_G` is an effect algebra (the
tree's `orderIntervalEffectAlgebra`, thesis B 175II.2), and "the effect
algebra order on `[0,u]_G` coincides with the regular order on `G`". -/
theorem oap3_le_iff (G : Type u) [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (u : G) (hu : 0 ≤ u) (x y : Set.Icc (0 : G) u) :
    @PCM.le _ (orderIntervalEffectAlgebra G u hu).toPCM x y ↔ x ≤ y := by
  let _ := orderIntervalEffectAlgebra G u hu
  constructor
  · rintro ⟨c, -, rfl⟩
    show (x : G) ≤ (x : G) + c
    exact le_add_of_nonneg_right c.2.1
  · intro h
    have h' : (x : G) ≤ y := h
    refine ⟨⟨(y : G) - x, sub_nonneg.2 h', le_trans (sub_le_self _ x.2.1) y.2.2⟩, ?_,
      Subtype.ext ?_⟩
    · show (x : G) + ((y : G) - x) ≤ u
      rw [add_sub_cancel]; exact y.2.2
    · show (x : G) + ((y : G) - x) = y
      rw [add_sub_cancel]

/-- The effect algebra order of `[0,u]_G` *is* the subtype order (OAP 3). -/
theorem orderInterval_order_eq (G : Type u) [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (u : G) (hu : 0 ≤ u) :
    @eaPartialOrder _ (orderIntervalEffectAlgebra G u hu) = Subtype.partialOrder _ :=
  PartialOrder.ext fun x y => oap3_le_iff G u hu x y

/-- **OAP 3** (`ex:cstaralgebra`, first.tex:397, Example): "In particular, the
set of effects `[0,1]_C` of a unital C*-algebra `C` forms an effect algebra
with `a ⊥ b ⟺ a + b ≤ 1` and `a^⊥ = 1 - a`" — the case `G = C`, `u = 1`. -/
noncomputable def oap3_cstar (C : Type u) [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] : EffectAlgebra (Set.Icc (0 : C) 1) :=
  orderIntervalEffectAlgebra C 1 zero_le_one

/-! ### OAP 6: Boolean algebras -/

/-- **OAP 6** (`ex:booleanalgebra`, first.tex:474, Example): the effect
algebra order of a Boolean algebra (with `x ⊥ y ⟺ x ∧ y = 0`, the tree's
`booleanEffectAlgebra`) is its lattice order. -/
theorem boolean_le_iff (B : Type u) [BooleanAlgebra B] (x y : B) :
    @PCM.le B (booleanEffectAlgebra B).toPCM x y ↔ x ≤ y := by
  let _ := booleanEffectAlgebra B
  constructor
  · rintro ⟨c, -, rfl⟩; exact le_sup_left
  · intro h
    refine ⟨y \ x, ?_, sup_sdiff_cancel_right h⟩
    show x ⊓ y \ x = ⊥
    exact inf_sdiff_self_right

theorem boolean_order_eq (B : Type u) [BooleanAlgebra B] :
    @eaPartialOrder B (booleanEffectAlgebra B) = (inferInstance : PartialOrder B) :=
  PartialOrder.ext fun x y => boolean_le_iff B x y

/-- **OAP 6** (`ex:booleanalgebra`, first.tex:474, Example): a Boolean algebra
is a *commutative* effect monoid with `x·y = x ∧ y` (the tree's
`booleanEffectMonoid`, thesis B 178III.2). -/
theorem oap6_commutative (B : Type u) [BooleanAlgebra B] :
    @EffectMonoid.Commutative B (booleanEffectMonoid B) ∧
      ∀ x y : B, @HMul.hMul B B B (@instHMul B (booleanEffectMonoid B).toMul) x y = x ⊓ y :=
  ⟨fun x y => inf_comm x y, fun _ _ => rfl⟩

/-- **OAP 6** (`ex:booleanalgebra`, first.tex:474, Example), the converse:
an orthomodular lattice in which `∧` distributes over `⋁` (sums of
orthogonal elements, `x ≤ y^⊥`) is distributive.  The print gives no proof;
ours: every pair commutes (`a = (a ∧ b) ∨ (a ∧ b^⊥)`), whence
`b ∨ c = b ⋁ (c ∧ b^⊥)`. -/
theorem oap6_distrib (L : Type u) [OrthomodularLattice L]
    (H : ∀ a x y : L, x ≤ yᶜ → a ⊓ (x ⊔ y) = a ⊓ x ⊔ a ⊓ y) (a b c : L) :
    a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  have hcc : ∀ x : L, x ≤ xᶜᶜ := fun x => (Ortholattice.compl_compl x).ge
  have step1 : ∀ x y : L, x = x ⊓ y ⊔ x ⊓ yᶜ := fun x y => by
    rw [← H x y yᶜ (hcc y), Ortholattice.sup_compl, inf_top_eq]
  have step2 : b ⊔ c = b ⊔ c ⊓ bᶜ := by
    conv_lhs => rw [step1 c b]
    rw [← sup_assoc, sup_eq_left.2 (inf_le_right : c ⊓ b ≤ b)]
  have hb : b ≤ (c ⊓ bᶜ)ᶜ :=
    (hcc b).trans (Ortholattice.compl_antitone inf_le_right)
  rw [step2, H a b (c ⊓ bᶜ) hb]
  conv_rhs => rw [step1 (a ⊓ c) b]
  rw [← sup_assoc, sup_eq_left.2
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : a ⊓ c ⊓ b ≤ a ⊓ b), inf_assoc]

/-- **OAP 6** (`ex:booleanalgebra`, first.tex:474, Example), the converse:
such an orthomodular lattice *is* a Boolean algebra (same order, complement
the orthocomplement). -/
def oap6_booleanAlgebra (L : Type u) [OrthomodularLattice L]
    (H : ∀ a x y : L, x ≤ yᶜ → a ⊓ (x ⊔ y) = a ⊓ x ⊔ a ⊓ y) : BooleanAlgebra L :=
  letI : DistribLattice L :=
    DistribLattice.ofInfSupLe fun a b c => (oap6_distrib L H a b c).le
  { (inferInstance : DistribLattice L), (inferInstance : BoundedOrder L) with
    compl := compl
    inf_compl_le_bot := fun a => (Ortholattice.inf_compl a).le
    top_le_sup_compl := fun a => (Ortholattice.sup_compl a).ge }

/-! ### OAP 7: unit intervals of ordered rings -/

/-- **OAP 7** (`ex:CX`, first.tex:486, Example): the unit interval `[0,1]_R`
of a partially ordered unital ring `R` in which sums and products of
positive elements are positive (Mathlib's `IsOrderedRing`) is an effect
monoid, with the effect algebra structure of OAP 3 and the product of `R`. -/
noncomputable def unitIntervalEffectMonoid (R : Type u) [Ring R] [PartialOrder R]
    [IsOrderedRing R] : EffectMonoid (Set.Icc (0 : R) 1) :=
  letI := orderIntervalEffectAlgebra R 1 zero_le_one
  EffectMonoid.ofBiadditive (Set.Icc (0 : R) 1)
    (fun a => Subtype.ext (one_mul (a : R)))
    (fun a => Subtype.ext (mul_one (a : R)))
    (fun a b c => Subtype.ext (mul_assoc (a : R) b c).symm)
    (fun a b c h => by
      have hbc : (b : R) + c ≤ 1 := h
      have h' : Perp (a * b) (a * c) := by
        show (a : R) * b + a * c ≤ 1
        rw [← mul_add]
        exact mul_le_one₀ a.2.2 (add_nonneg b.2.1 c.2.1) hbc
      refine ⟨h', Subtype.ext ?_⟩
      rw [oplus_eq h, oplus_eq h']
      exact mul_add (a : R) b c)
    (fun a b c h => by
      have hbc : (b : R) + c ≤ 1 := h
      have h' : Perp (b * a) (c * a) := by
        show (b : R) * a + c * a ≤ 1
        rw [← add_mul]
        exact mul_le_one₀ hbc a.2.1 a.2.2
      refine ⟨h', Subtype.ext ?_⟩
      rw [oplus_eq h, oplus_eq h']
      exact add_mul (b : R) c a)

/-- **OAP 7** (`ex:CX`, first.tex:486, Example): for a topological space `X`,
`[0,1]_{C(X)} = {f : X → [0,1]}` (continuous), and it is a *commutative*
effect monoid.  (`C(X)` is taken real-valued; the print's `C(X)` is complex,
whose unit interval consists of the same real-valued functions.) -/
theorem oap7_CX (X : Type u) [TopologicalSpace X] :
    (∀ f : C(X, ℝ), f ∈ Set.Icc (0 : C(X, ℝ)) 1 ↔ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      @EffectMonoid.Commutative _ (unitIntervalEffectMonoid C(X, ℝ)) := by
  refine ⟨fun f => ?_, fun a b => Subtype.ext (mul_comm (a : C(X, ℝ)) b)⟩
  simp only [Set.mem_Icc, ContinuousMap.le_def, ContinuousMap.zero_apply,
    ContinuousMap.one_apply, forall_and]

/-! ### OAP 9: the Stone embedding -/

section Stone

variable (B : Type u) [BooleanAlgebra B]

/-- The Stone space of a Boolean algebra `B`: the Boolean homomorphisms
`B → 2`, with the topology of pointwise convergence. -/
def stoneSet : Set (B → Bool) :=
  {φ | (∀ x y, φ (x ⊓ y) = (φ x && φ y)) ∧ (∀ x y, φ (x ⊔ y) = (φ x || φ y)) ∧
    φ ⊤ = true ∧ φ ⊥ = false}

theorem isClosed_stoneSet : IsClosed (stoneSet B) := by
  have c : ∀ x : B, Continuous fun φ : B → Bool => φ x := fun x => continuous_apply x
  have c2 : Continuous fun p : Bool × Bool => (p.1 && p.2) := continuous_of_discreteTopology
  have c3 : Continuous fun p : Bool × Bool => (p.1 || p.2) := continuous_of_discreteTopology
  simp only [stoneSet, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (c _)
    (c2.comp ((c x).prodMk (c y)))).inter ((isClosed_iInter fun x => isClosed_iInter
      fun y => isClosed_eq (c _) (c3.comp ((c x).prodMk (c y)))).inter
        ((isClosed_eq (c _) continuous_const).inter (isClosed_eq (c _) continuous_const)))

instance : CompactSpace (stoneSet B) :=
  isCompact_iff_compactSpace.1 (isClosed_stoneSet B).isCompact

/-- The indicator function of the basic clopen `{φ ; φ(b) = 1}`. -/
noncomputable def stoneMap (b : B) : Set.Icc (0 : C(stoneSet B, ℝ)) 1 :=
  ⟨⟨fun φ => if φ.1 b then 1 else 0,
    (continuous_of_discreteTopology (f := fun t : Bool => if t then (1 : ℝ) else 0)).comp
      ((continuous_apply b).comp continuous_subtype_val)⟩,
    fun φ => by show (0 : ℝ) ≤ if φ.1 b then 1 else 0; split_ifs <;> norm_num,
    fun φ => by show (if φ.1 b then (1 : ℝ) else 0) ≤ 1; split_ifs <;> norm_num⟩

theorem stoneMap_apply (b : B) (φ : stoneSet B) :
    ((stoneMap B b : C(stoneSet B, ℝ)) φ) = if φ.1 b then 1 else 0 := rfl

/-- The prime ideal theorem, in the form needed: if `b ≰ c` some Boolean
homomorphism `φ` has `φ b = 1`, `φ c = 0`. -/
theorem exists_stone_separating {b c : B} (h : ¬ b ≤ c) :
    ∃ φ ∈ stoneSet B, φ b = true ∧ φ c = false := by
  classical
  have hd : Disjoint ((Order.PFilter.principal b : Order.PFilter B) : Set B)
      (Order.Ideal.principal c : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact h (le_trans (Order.PFilter.mem_principal.1 hx) (Order.Ideal.mem_principal.1 hx'))
  obtain ⟨J, hJ, hIJ, hFJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  have hlow : ∀ {x y : B}, x ≤ y → y ∈ J → x ∈ J := fun hxy hy => J.lower hxy hy
  refine ⟨fun x => decide (x ∉ J), ⟨fun x y => ?_, fun x y => ?_, ?_, ?_⟩, ?_, ?_⟩
  · have : x ⊓ y ∈ J ↔ x ∈ J ∨ y ∈ J :=
      ⟨hJ.mem_or_mem, fun h => h.elim (hlow inf_le_left) (hlow inf_le_right)⟩
    by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;> simp_all
  · have : x ⊔ y ∈ J ↔ x ∈ J ∧ y ∈ J := Order.Ideal.sup_mem_iff
    by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;> simp_all
  · simp only [decide_eq_true_eq]
    intro htop
    exact hJ.toIsProper.ne_univ (Set.eq_univ_of_forall fun x => hlow le_top htop)
  · simp only [decide_eq_false_iff_not, not_not]; exact J.bot_mem
  · simp only [decide_eq_true_eq]
    intro hb
    exact Set.disjoint_left.1 hFJ (Order.PFilter.mem_principal.2 le_rfl) hb
  · simp only [decide_eq_false_iff_not, not_not]
    exact Order.Ideal.mem_of_mem_of_le Order.Ideal.mem_principal_self hIJ

/-- **OAP 9** (`ex:stone-embedding`, first.tex:516, Example): a Boolean
algebra `B` embeds, as an effect monoid, into `[0,1]_{C(X_B)}` for its Stone
space `X_B` (a compact Hausdorff space): `b` goes to the indicator of the
clopen `{φ ; φ(b) = 1}`. -/
theorem oap9_stone :
    letI := booleanEffectMonoid B
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      letI := unitIntervalEffectMonoid C(X, ℝ)
      Nonempty (EMEmbedding B (Set.Icc (0 : C(X, ℝ)) 1)) := by
  let _ := booleanEffectMonoid B
  let _ := unitIntervalEffectMonoid C(stoneSet B, ℝ)
  refine ⟨stoneSet B, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have hext : ∀ {f g : Set.Icc (0 : C(stoneSet B, ℝ)) 1},
      (∀ φ, (f : C(stoneSet B, ℝ)) φ = (g : C(stoneSet B, ℝ)) φ) → f = g :=
    fun h => Subtype.ext (ContinuousMap.ext h)
  have hperp : ∀ {x y : B}, Perp x y → Perp (stoneMap B x) (stoneMap B y) := by
    intro x y h
    have h' : x ⊓ y = ⊥ := h
    show (stoneMap B x : C(stoneSet B, ℝ)) + stoneMap B y ≤ 1
    refine ContinuousMap.le_def.2 fun φ => ?_
    have e1 := φ.2.1 x y
    rw [h', φ.2.2.2.2] at e1
    rw [ContinuousMap.add_apply, stoneMap_apply, stoneMap_apply, ContinuousMap.one_apply]
    cases hx : φ.1 x <;> cases hy : φ.1 y <;> simp_all
  exact
    { toFun := stoneMap B
      perp_map := hperp
      ovee_map := fun {x y} h => by
        have h' : x ⊓ y = ⊥ := h
        apply hext; intro φ
        show (stoneMap B (x ⊔ y) : C(stoneSet B, ℝ)) φ =
          (stoneMap B x : C(stoneSet B, ℝ)) φ + (stoneMap B y : C(stoneSet B, ℝ)) φ
        have e1 := φ.2.1 x y
        have e2 := φ.2.2.1 x y
        rw [h', φ.2.2.2.2] at e1
        simp only [stoneMap_apply]
        cases hx : φ.1 x <;> cases hy : φ.1 y <;> simp_all
      map_one := by
        apply hext; intro φ
        show (stoneMap B ⊤ : C(stoneSet B, ℝ)) φ = 1
        simp only [stoneMap_apply, φ.2.2.2.1, ite_true]
      map_mul := fun x y => by
        apply hext; intro φ
        show (stoneMap B (x ⊓ y) : C(stoneSet B, ℝ)) φ =
          (stoneMap B x : C(stoneSet B, ℝ)) φ * (stoneMap B y : C(stoneSet B, ℝ)) φ
        simp only [stoneMap_apply, φ.2.1 x y]
        cases φ.1 x <;> cases φ.1 y <;> simp
      reflect := fun {x y} h => by
        have h := (oap3_le_iff _ _ _ _ _).1 h
        refine (boolean_le_iff B x y).2 ?_
        by_contra hxy
        obtain ⟨φ, hφ, h1, h2⟩ := exists_stone_separating B hxy
        have : (stoneMap B x : C(stoneSet B, ℝ)) ⟨φ, hφ⟩ ≤
            (stoneMap B y : C(stoneSet B, ℝ)) ⟨φ, hφ⟩ := h ⟨φ, hφ⟩
        rw [stoneMap_apply, stoneMap_apply] at this
        simp [h1, h2] at this
        exact absurd this (by norm_num) }

end Stone

/-! ### OAP 15, 16: complete examples -/

/-- **OAP 15** (first.tex:558, Example): an ω-complete Boolean algebra (every
increasing sequence has a supremum) is an ω-complete effect monoid. -/
theorem oap15_omega (B : Type u) [BooleanAlgebra B]
    (hB : ∀ f : ℕ → B, Monotone f → ∃ s, IsLUB (Set.range f) s) :
    @OmegaComplete B (booleanEffectAlgebra B) := by
  let _ := booleanEffectAlgebra B
  constructor
  rw [boolean_order_eq]
  exact hB

/-- **OAP 15** (first.tex:558, Example): a complete Boolean algebra is a
directed-complete effect monoid. -/
theorem oap15_complete (B : Type u) [CompleteBooleanAlgebra B] :
    @DirectedComplete B (booleanEffectAlgebra B) := by
  let _ := booleanEffectAlgebra B
  constructor
  unfold IsDirectedSet
  rw [boolean_order_eq]
  exact fun S _ => ⟨sSup S, isLUB_sSup S⟩

/-- **OAP 16** (first.tex:565, Example): "basically disconnected": every
cozero set has open closure. -/
def BasicallyDisconnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(X, ℝ), IsOpen (closure {x | f x ≠ 0})

section DedekindComplete

variable {X : Type u} [TopologicalSpace X]

/-- A non-empty family `S` in `[0,1]_{C(X)}` has a supremum as soon as the
closures `U_r` of the open sets `⋃_{f ∈ S} {f > r}` are open: the supremum is
`g(x) = sup {r ; x ∈ U_r}`. -/
theorem exists_isLUB_Icc (S : Set (Set.Icc (0 : C(X, ℝ)) 1)) (hne : S.Nonempty)
    (hopen : ∀ r : ℝ, IsOpen (closure (⋃ f ∈ S, {x | r < (f : C(X, ℝ)) x}))) :
    ∃ g, IsLUB S g := by
  set U : ℝ → Set X := fun r => closure (⋃ f ∈ S, {x | r < (f : C(X, ℝ)) x}) with hU
  obtain ⟨f0, hf0⟩ := hne
  have hneg : ∀ x (r : ℝ), r < 0 → x ∈ U r := fun x r hr =>
    subset_closure (Set.mem_biUnion hf0 (lt_of_lt_of_le hr (f0.2.1 x)))
  have hone : ∀ x (r : ℝ), x ∈ U r → r < 1 := by
    intro x r hx
    by_contra h
    push Not at h
    have : (⋃ f ∈ S, {x | r < (f : C(X, ℝ)) x}) = ∅ := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_exists, not_lt]
      intro f _; exact le_trans (f.2.2 y) h
    simp only [hU, this, closure_empty, Set.mem_empty_iff_false] at hx
  have hanti : ∀ {r r' : ℝ}, r ≤ r' → U r' ⊆ U r := fun h =>
    closure_mono (Set.biUnion_mono le_rfl fun f _ y hy => lt_of_le_of_lt h hy)
  have hA : ∀ x, ({r | x ∈ U r} : Set ℝ).Nonempty := fun x => ⟨-1, hneg x _ (by norm_num)⟩
  have hB : ∀ x, BddAbove ({r | x ∈ U r} : Set ℝ) := fun x => ⟨1, fun r hr => (hone x r hr).le⟩
  set g : X → ℝ := fun x => sSup {r | x ∈ U r} with hg
  have hlt : ∀ x (a : ℝ), a < g x ↔ ∃ r, a < r ∧ x ∈ U r := by
    intro x a
    constructor
    · intro h
      obtain ⟨r, hr, har⟩ := exists_lt_of_lt_csSup (hA x) h
      exact ⟨r, har, hr⟩
    · rintro ⟨r, har, hr⟩; exact lt_of_lt_of_le har (le_csSup (hB x) hr)
  have hgt : ∀ x (a : ℝ), g x < a ↔ ∃ r, r < a ∧ x ∉ U r := by
    intro x a
    constructor
    · intro h
      obtain ⟨r, h1, h2⟩ := exists_between h
      exact ⟨r, h2, fun hr => absurd (le_csSup (hB x) hr) (not_le.2 h1)⟩
    · rintro ⟨r, hra, hr⟩
      refine lt_of_le_of_lt (csSup_le (hA x) fun r' hr' => ?_) hra
      by_contra h
      exact hr (hanti (not_le.1 h).le hr')
  have hcont : Continuous g := by
    refine continuous_iff_continuousAt.2 fun x => tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have ho : IsOpen {y | a < g y} := by
        have : {y | a < g y} = ⋃ r ∈ Set.Ioi a, U r := by
          ext y; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ioi, hlt, exists_prop]
        rw [this]; exact isOpen_biUnion fun r _ => hopen r
      exact ho.mem_nhds ha
    · have ho : IsOpen {y | g y < a} := by
        have : {y | g y < a} = ⋃ r ∈ Set.Iio a, (U r)ᶜ := by
          ext y; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Iio, hgt, exists_prop,
            Set.mem_compl_iff]
        rw [this]; exact isOpen_biUnion fun r _ => isClosed_closure.isOpen_compl
      exact ho.mem_nhds ha
  have hge : ∀ f ∈ S, ∀ x, (f : C(X, ℝ)) x ≤ g x := by
    intro f hf x
    by_contra h
    obtain ⟨r, h1, h2⟩ := exists_between (not_le.1 h)
    have hx : x ∈ U r := subset_closure (Set.mem_biUnion hf h2)
    exact absurd (le_csSup (hB x) hx) (not_le.2 h1)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    by_contra h
    obtain ⟨r, h1, h2⟩ := exists_between (not_le.1 h)
    exact absurd (le_csSup (hB x) (hneg x r h2)) (not_le.2 h1)
  have hg1 : ∀ x, g x ≤ 1 := fun x => csSup_le (hA x) fun r hr => (hone x r hr).le
  refine ⟨⟨⟨g, hcont⟩, fun x => hg0 x, fun x => hg1 x⟩,
    fun f hf => ContinuousMap.le_def.2 fun x => hge f hf x, fun h hh => ?_⟩
  refine ContinuousMap.le_def.2 fun x => csSup_le (hA x) fun r hr => ?_
  have hsub : U r ⊆ {y | r ≤ (h : C(X, ℝ)) y} :=
    closure_minimal (Set.iUnion₂_subset fun f hf y hy =>
      le_trans (le_of_lt hy) (ContinuousMap.le_def.1 (hh hf) y))
      (isClosed_le continuous_const (h : C(X, ℝ)).continuous)
  exact hsub hr

/-- **OAP 16** (first.tex:565, Example): for an extremally disconnected
compact Hausdorff space `X`, `[0,1]_{C(X)}` is directed complete.  The print
gives no proof; ours: every non-empty family in `[0,1]_{C(X)}` has a
supremum, `g(x) = sup {r ; x ∈ cl ⋃_{f} {f > r}}` (`exists_isLUB_Icc`). -/
theorem oap16_extremally (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] :
    @DirectedComplete (Set.Icc (0 : C(X, ℝ)) 1) (orderIntervalEffectAlgebra C(X, ℝ) 1 zero_le_one) := by
  let _ := orderIntervalEffectAlgebra C(X, ℝ) 1 zero_le_one
  constructor
  unfold IsDirectedSet
  rw [orderInterval_order_eq C(X, ℝ) 1 zero_le_one]
  rintro S ⟨hne, -⟩
  exact exists_isLUB_Icc S hne fun r => ExtremallyDisconnected.open_closure _
    (isOpen_biUnion fun f _ => isOpen_lt continuous_const (f : C(X, ℝ)).continuous)

/-- **OAP 16** (first.tex:565, Example): for a basically disconnected compact
Hausdorff space `X`, `[0,1]_{C(X)}` is ω-complete.  The print cites
[Gillman–Jerison 3N.5]; ours: for an increasing sequence `fₙ` the open set
`⋃ₙ {fₙ > r}` is the cozero set of `Σₙ 2⁻ⁿ·clamp(fₙ - r)`, so its closure is
open and `exists_isLUB_Icc` applies. -/
theorem oap16_basically (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hX : BasicallyDisconnected X) :
    @OmegaComplete (Set.Icc (0 : C(X, ℝ)) 1) (orderIntervalEffectAlgebra C(X, ℝ) 1 zero_le_one) := by
  let _ := orderIntervalEffectAlgebra C(X, ℝ) 1 zero_le_one
  constructor
  rw [orderInterval_order_eq C(X, ℝ) 1 zero_le_one]
  intro f _
  refine exists_isLUB_Icc _ (Set.range_nonempty f) fun r => ?_
  set t : ℕ → X → ℝ := fun n x => ((1 : ℝ) / 2) ^ n * max (min ((f n : C(X, ℝ)) x - r) 1) 0
    with ht
  have ht0 : ∀ n x, 0 ≤ t n x := fun n x => mul_nonneg (by positivity) (le_max_right _ _)
  have ht1 : ∀ n x, t n x ≤ ((1 : ℝ) / 2) ^ n := fun n x =>
    mul_le_of_le_one_right (by positivity) (max_le (min_le_right _ _) zero_le_one)
  have hcont : ∀ n, Continuous (t n) := fun n =>
    continuous_const.mul ((((f n : C(X, ℝ)).continuous.sub continuous_const).min
      continuous_const).max continuous_const)
  have hsum : ∀ x, Summable fun n => t n x := fun x =>
    Summable.of_nonneg_of_le (fun n => ht0 n x) (fun n => ht1 n x) summable_geometric_two
  let h : C(X, ℝ) := ⟨fun x => ∑' n, t n x, continuous_tsum hcont summable_geometric_two
    fun n x => by rw [Real.norm_eq_abs, abs_of_nonneg (ht0 n x)]; exact ht1 n x⟩
  have hset : {x | h x ≠ 0} = ⋃ g ∈ Set.range f, {x | r < (g : C(X, ℝ)) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range, exists_prop,
      exists_exists_eq_and]
    constructor
    · intro hx
      by_contra hno
      push Not at hno
      apply hx
      show ∑' n, t n x = 0
      have : ∀ n, t n x = 0 := fun n => by
        simp only [ht]
        rw [max_eq_right (min_le_of_left_le (by linarith [hno n])), mul_zero]
      simp only [this, tsum_zero]
    · rintro ⟨n, hn⟩
      refine ne_of_gt (Summable.tsum_pos (hsum x) (fun n => ht0 n x) n ?_)
      simp only [ht]
      exact mul_pos (by positivity) (lt_max_of_lt_left (lt_min (by linarith) one_pos))
  rw [← hset]
  exact hX h

end DedekindComplete

end Examples

end Papers.OAP
