/-
Papers/OAP/Embedding.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`: §7 *Embedding theorems* — points
**OAP 51**–**OAP 57**.

Conventions (see `Papers/README.md`, `Papers/OAP/PLAN.md`):

* The print's `⨁_{e∈E} Me` of an arbitrary family is the cartesian product
  `∀ e : E, leftCorner e` with pointwise operations (`piEffectAlgebra`,
  `piEffectMonoid`); the right corner `Me` is the left corner `eM` (OAP 12).
  The binary `M₁ ⊕ M₂` is Basic's `prodEffectMonoid`.
* A "maximal collection of non-zero orthogonal idempotents" is
  `Maximal IsOrthIdemFamily E` (Mathlib's `Maximal` for `⊆`), with
  "orthogonal" the print's `a·b = b·a = 0` (OAP 5, `Orthogonal`).
* "`M₂` is an ω-complete (complete) Boolean algebra" is stated as in OAP 47:
  `M₂` is a Boolean effect monoid, `M₂ ≅ P(M₂)` as effect monoids (OAP 45),
  and every countable (every) subset of `P(M₂)` has a supremum.
* Corners, products and sub-effect monoids are *defs*, not instances; their
  order is the effect algebra order `eaPartialOrder` (never the subtype or
  product order), handled through `corner_le_iff`, `pi_le_iff`,
  `sub_le_iff`, applied by term.
-/
import Papers.OAP.Boolean

set_option warn.classDefReducibility false

namespace Papers.OAP

open Theses.B.Eff
open scoped Papers.OAP unitInterval

universe u v

/-! ## Infrastructure: products of families, corners -/

section Pi

variable {ι : Type u} (α : ι → Type u)

/-- The product `∏ᵢ αᵢ` of a family of effect algebras, with pointwise
operations (the infinite version of the tree's `prodEffectAlgebra`, 175III). -/
def piEffectAlgebra [∀ i, EffectAlgebra (α i)] : EffectAlgebra (∀ i, α i) where
  zero := fun _ => 0
  one := fun _ => 1
  Perp x y := ∀ i, Perp (x i) (y i)
  ovee x y h := fun i => ovee (x i) (y i) (h i)
  orth x := fun i => orth (x i)
  perp_comm h := fun i => PCM.perp_comm (h i)
  ovee_comm h := funext fun i => PCM.ovee_comm (h i)
  perp_of_ovee_perp hab h := fun i => PCM.perp_of_ovee_perp (hab i) (h i)
  perp_ovee_of_ovee_perp hab h := fun i => PCM.perp_ovee_of_ovee_perp (hab i) (h i)
  ovee_assoc hab h := funext fun i => PCM.ovee_assoc (hab i) (h i)
  zero_perp a := fun i => PCM.zero_perp (a i)
  zero_ovee a := funext fun i => PCM.zero_ovee (a i)
  perp_orth a := fun i => EffectAlgebra.perp_orth (a i)
  ovee_orth a := funext fun i => EffectAlgebra.ovee_orth (a i)
  orth_unique h heq := funext fun i => EffectAlgebra.orth_unique (h i) (congrFun heq i)
  eq_zero_of_perp_one h := funext fun i => EffectAlgebra.eq_zero_of_perp_one (h i)

variable {α}

theorem pi_oplus [∀ i, EffectAlgebra (α i)] {x y : ∀ i, α i}
    (h : @Perp _ (piEffectAlgebra α).toPCM x y) :
    @oplus _ (piEffectAlgebra α) x y = fun i => x i ⋎ y i := by
  let _ := piEffectAlgebra α
  rw [oplus_eq h]
  funext i
  exact (oplus_eq (h i)).symm

/-- The effect algebra order of a product is the pointwise order. -/
theorem pi_le_iff [∀ i, EffectAlgebra (α i)] {x y : ∀ i, α i} :
    @PCM.le _ (piEffectAlgebra α).toPCM x y ↔ ∀ i, x i ≤ y i := by
  let _ := piEffectAlgebra α
  constructor
  · rintro ⟨c, h, e⟩ i
    exact le_def.2 ⟨c i, h i, by rw [oplus_eq (h i)]; exact congrFun e i⟩
  · intro h
    refine ⟨fun i => y i ⊖ x i, fun i => perp_osub (h i), funext fun i => ?_⟩
    show ovee (x i) (y i ⊖ x i) (perp_osub (h i)) = y i
    rw [← oplus_eq]; exact oplus_osub (h i)

/-- A product of ω-complete effect algebras is ω-complete (suprema are
computed pointwise). -/
theorem pi_omegaComplete [∀ i, EffectAlgebra (α i)] [∀ i, OmegaComplete (α i)] :
    @OmegaComplete _ (piEffectAlgebra α) := by
  let _ := piEffectAlgebra α
  refine ⟨fun f hf => ?_⟩
  have hfi : ∀ i, Monotone fun n => f n i := fun i m n h => pi_le_iff.1 (hf h) i
  choose s hs using fun i => OmegaComplete.exists_isLUB _ (hfi i)
  refine ⟨s, ?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact pi_le_iff.2 fun i => (hs i).1 ⟨n, rfl⟩
  · exact pi_le_iff.2 fun i => (hs i).2 (by
      rintro _ ⟨n, rfl⟩; exact pi_le_iff.1 (hu ⟨n, rfl⟩) i)

/-- A product of halvable effect algebras is halvable. -/
theorem pi_halvable [∀ i, EffectAlgebra (α i)] (h : ∀ i, HalvableEA (α i)) :
    @HalvableEA _ (piEffectAlgebra α) := by
  let _ := piEffectAlgebra α
  choose b hb e using h
  have hp : Perp b b := fun i => hb i
  exact ⟨b, hp, by rw [pi_oplus hp]; funext i; exact e i⟩

variable (α) in
/-- The product `∏ᵢ αᵢ` of a family of effect monoids, with pointwise
operations: the print's `⨁_{e∈E} Me` (OAP 53). -/
def piEffectMonoid [∀ i, EffectMonoid (α i)] : EffectMonoid (∀ i, α i) :=
  letI := piEffectAlgebra α
  letI : Mul (∀ i, α i) := ⟨fun x y i => x i * y i⟩
  EffectMonoid.ofBiadditive (∀ i, α i)
    (fun a => funext fun i => eone_mul (a i))
    (fun a => funext fun i => emul_one (a i))
    (fun a b c => funext fun i => (emul_assoc (a i) (b i) (c i)).symm)
    (fun a b c h => by
      have h' : Perp (a * b) (a * c) := fun i => (mul_oplus (a i) (h i)).1
      refine ⟨h', ?_⟩
      rw [pi_oplus h, pi_oplus h']
      funext i
      exact (mul_oplus (a i) (h i)).2)
    (fun a b c h => by
      have h' : Perp (b * a) (c * a) := fun i => (oplus_mul (a i) (h i)).1
      refine ⟨h', ?_⟩
      rw [pi_oplus h, pi_oplus h']
      funext i
      exact (oplus_mul (a i) (h i)).2)

/-- A product of Boolean effect monoids is Boolean. -/
theorem pi_isBooleanEM [∀ i, EffectMonoid (α i)] (h : ∀ i, IsBooleanEM (α i)) :
    @IsBooleanEM _ (piEffectMonoid α) := by
  let _ := piEffectMonoid α
  refine isBooleanEM_iff.2 fun a => funext fun i => ?_
  exact isBooleanEM_iff.1 (h i) (a i)

end Pi

section Corner

variable {M : Type u} [EffectMonoid M] {p : M} (hp : p * p = p)
include hp

/-- The corner `pM` of an ω-complete effect monoid is ω-complete: an
increasing sequence in `pM` has its supremum in `M`, which lies below `p`. -/
theorem corner_omegaComplete [OmegaComplete M] :
    letI := cornerEffectMonoid p hp
    OmegaComplete (leftCorner p) := by
  let _ := cornerEffectMonoid p hp
  refine ⟨fun f hf => ?_⟩
  have hf' : Monotone fun n => (f n).1 := fun a b h => (corner_le_iff hp).1 (hf h)
  obtain ⟨m, hm⟩ := OmegaComplete.exists_isLUB _ hf'
  have hmp : m ≤ p := hm.2 (by rintro _ ⟨n, rfl⟩; exact le_of_mem_leftCorner hp (f n).2)
  refine ⟨⟨m, mem_leftCorner_of_le hp hmp⟩, ?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩; exact (corner_le_iff hp).2 (hm.1 ⟨n, rfl⟩)
  · exact (corner_le_iff hp).2 (hm.2 (by
      rintro _ ⟨n, rfl⟩; exact (corner_le_iff hp).1 (hu ⟨n, rfl⟩)))

/-- The corner `pM` of a directed-complete effect monoid is directed
complete. -/
theorem corner_directedComplete [DirectedComplete M] :
    letI := cornerEffectMonoid p hp
    DirectedComplete (leftCorner p) := by
  let _ := cornerEffectMonoid p hp
  refine ⟨fun S ⟨hne, hd⟩ => ?_⟩
  have hd' : IsDirectedSet (Subtype.val '' S) := by
    refine ⟨hne.image _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, h1, h2⟩ := hd x hx y hy
    exact ⟨z.1, ⟨z, hz, rfl⟩, (corner_le_iff hp).1 h1, (corner_le_iff hp).1 h2⟩
  obtain ⟨m, hm⟩ := DirectedComplete.exists_isLUB _ hd'
  have hmp : m ≤ p := hm.2 (by rintro _ ⟨x, -, rfl⟩; exact le_of_mem_leftCorner hp x.2)
  refine ⟨⟨m, mem_leftCorner_of_le hp hmp⟩, fun x hx => ?_, fun u hu => ?_⟩
  · exact (corner_le_iff hp).2 (hm.1 ⟨x, hx, rfl⟩)
  · exact (corner_le_iff hp).2 (hm.2 (by
      rintro _ ⟨x, hx, rfl⟩; exact (corner_le_iff hp).1 (hu hx)))

/-- If `p` is halvable in `M`, the corner `pM` is halvable: the half `b` of
`p` lies below `p`. -/
theorem corner_halvable (hh : IsHalvable p) :
    letI := cornerEffectMonoid p hp
    HalvableEA (leftCorner p) := by
  let _ := cornerEffectMonoid p hp
  obtain ⟨b, hbb, e⟩ := hh
  have hb : b ≤ p := e ▸ le_oplus_left hbb
  let b' : leftCorner p := ⟨b, mem_leftCorner_of_le hp hb⟩
  have hbb' : Perp b' b' := hbb
  refine ⟨b', hbb', Subtype.ext ?_⟩
  exact (corner_oplus hp hbb').trans e

/-- If `p` is Boolean in `M` (every element below it is idempotent), the
corner `pM` is a Boolean effect monoid. -/
theorem corner_isBooleanEM (hB : IsBooleanElem p) :
    letI := cornerEffectMonoid p hp
    IsBooleanEM (leftCorner p) := by
  let _ := cornerEffectMonoid p hp
  exact isBooleanEM_iff.2 fun x => Subtype.ext (hB x.1 (le_of_mem_leftCorner hp x.2))

end Corner

/-! ## OAP 51: the ceiling of a halvable element -/

section OAP51

variable {M : Type u} [EffectMonoid M] [OmegaComplete M]

/-- **OAP 51** (`lem:ceilhalveable`, first.tex:1922, Lemma): in an
ω-complete effect monoid the ceiling `⌈a⌉` of a halvable element `a` is
halvable.  As printed: for `a = b ⋁ b`,
`⌈a⌉ = ⋁ₙ (b ⋁ b)(a^⊥)ⁿ = (⋁ₙ b(a^⊥)ⁿ) ⋁ (⋁ₙ b(a^⊥)ⁿ)`. -/
theorem oap51 {a : M} (ha : IsHalvable a) : IsHalvable (ceil a) := by
  obtain ⟨b, hbb, rfl⟩ := ha
  set a := b ⋎ b
  let x : ℕ → M := fun n => b * orth a ^ n
  have hxx : ∀ n, Perp (x n) (x n) ∧ a * orth a ^ n = x n ⋎ x n :=
    fun n => oplus_mul (orth a ^ n) hbb
  have hz : SeqSummable fun n => x n ⋎ x n := by
    have e : (fun n => x n ⋎ x n) = fun n => a * orth a ^ n :=
      funext fun n => (hxx n).2.symm
    rw [e]; exact seqSummable_mul_orth_pow a
  have hx : SeqSummable x :=
    (psum_le_psum hz fun n => le_oplus_left (hxx n).1).1
  obtain ⟨s, hs⟩ := exists_hasSeqSum hx
  obtain ⟨hss, hsum⟩ := HasSeqSum.oplus (fun n => (hxx n).1) hz hs hs
  refine ⟨s, hss, ?_⟩
  have e : (fun n => x n ⋎ x n) = fun n => a * orth a ^ n :=
    funext fun n => (hxx n).2.symm
  rw [e] at hsum
  exact hsum.unique (hasSeqSum_ceil a)

end OAP51

/-! ## OAP 52: a maximal family of halvable or Boolean idempotents -/

section Families

variable {M : Type u} [EffectMonoid M]

/-- A collection of non-zero pairwise orthogonal (OAP 5: `e·f = f·e = 0`)
idempotents. -/
def IsOrthIdemFamily (E : Set M) : Prop :=
  (∀ e ∈ E, e * e = e ∧ e ≠ 0) ∧ E.Pairwise Orthogonal

/-- Zorn's lemma for orthogonal families of non-zero idempotents with a
property `P`: every such family extends to a maximal one. -/
theorem exists_maximal_family (P : M → Prop) {H : Set M}
    (hH : IsOrthIdemFamily H ∧ ∀ e ∈ H, P e) :
    ∃ E, H ⊆ E ∧ Maximal (fun F => IsOrthIdemFamily F ∧ ∀ e ∈ F, P e) E := by
  obtain ⟨m, hHm, hm⟩ :=
    zorn_subset_nonempty {F | IsOrthIdemFamily F ∧ ∀ e ∈ F, P e} (fun c hc hch _ => by
      refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro e ⟨F, hF, he⟩; exact (hc hF).1.1 e he
      · rintro e ⟨F, hF, he⟩ f ⟨G, hG, hf⟩ hef
        rcases hch.total hF hG with h | h
        · exact (hc hG).1.2 (h he) hf hef
        · exact (hc hF).1.2 he (h hf) hef
      · rintro e ⟨F, hF, he⟩; exact (hc hF).2 e he) H hH
  exact ⟨m, hHm, hm⟩

theorem maximal_of_maximal_true {E : Set M}
    (h : Maximal (fun F => IsOrthIdemFamily F ∧ ∀ e ∈ F, True) E) :
    Maximal IsOrthIdemFamily E :=
  ⟨h.1.1, fun _ hF hsub => h.2 ⟨hF, fun _ _ => trivial⟩ hsub⟩

theorem maximal_true_of_maximal {E : Set M} (h : Maximal IsOrthIdemFamily E) :
    Maximal (fun F => IsOrthIdemFamily F ∧ ∀ e ∈ F, True) E :=
  ⟨⟨h.1, fun _ _ => trivial⟩, fun _ hF hsub => h.2 hF.1 hsub⟩

/-- Maximality: an idempotent `q` with property `P`, orthogonal to every
member of a maximal family, is zero (else it could be added). -/
theorem eq_zero_of_maximal_family (P : M → Prop) {E : Set M}
    (hE : Maximal (fun F => IsOrthIdemFamily F ∧ ∀ e ∈ F, P e) E) {q : M}
    (hq : q * q = q) (hPq : P q) (horth : ∀ e ∈ E, q * e = 0) : q = 0 := by
  by_contra hq0
  have hfam : IsOrthIdemFamily (insert q E) ∧ ∀ e ∈ insert q E, P e := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro e (rfl | he)
      · exact ⟨hq, hq0⟩
      · exact hE.1.1.1 e he
    · refine hE.1.1.2.insert fun e he _ => ?_
      have h1 := horth e he
      have h2 : e * q = 0 := by rw [← oap20 hq e]; exact h1
      exact ⟨⟨h1, h2⟩, ⟨h2, h1⟩⟩
    · rintro e (rfl | he)
      · exact hPq
      · exact hE.1.2 e he
  have hqE : q ∈ E := hE.2 hfam (Set.subset_insert q E) (Set.mem_insert q E)
  exact hq0 (hq.symm.trans (horth q hqE))

/-- "The only idempotent that is both Boolean and halvable is zero" (remark
after OAP 52, first.tex:1985); in fact any halvable Boolean element is `0`. -/
theorem eq_zero_of_halvable_boolean {q : M} (hh : IsHalvable q) (hB : IsBooleanElem q) :
    q = 0 := by
  obtain ⟨b, hbb, rfl⟩ := hh
  have hbi : b * b = b := hB b (le_oplus_left hbb)
  have hb0 : b * b = 0 := by
    have := emul_orth_eq_zero_of_le (idem_orth hbi) (le_orth_of_perp hbb)
    rwa [orth_orth] at this
  rw [← hbi, hb0, oplus_zero]

variable [OmegaComplete M]

/-- **OAP 52** (`prop:maxcollectionbooleanhalveable`, first.tex:1944,
Proposition): every ω-complete effect monoid has a maximal collection `E` of
non-zero orthogonal idempotents each of which is halvable or Boolean.
Proof as printed: `H` maximal among halvable such families, `E ⊇ H` maximal
among all; for `a ≤ e ∈ E \ H` the idempotent `⌈2(a^⊥a)⌉ ≤ e` is halvable
(OAP 51) and orthogonal to `H`, hence `0`, so `a^⊥a = 0` and `a` is
idempotent (OAP 18). -/
theorem oap52 :
    ∃ E : Set M, Maximal IsOrthIdemFamily E ∧ ∀ e ∈ E, IsHalvable e ∨ IsBooleanElem e := by
  obtain ⟨H, -, hH⟩ := exists_maximal_family (M := M) IsHalvable (H := ∅)
    ⟨⟨by simp, Set.pairwise_empty _⟩, by simp⟩
  obtain ⟨E, hHE, hE⟩ := exists_maximal_family (fun _ => True) (H := H)
    ⟨hH.1.1, fun _ _ => trivial⟩
  refine ⟨E, maximal_of_maximal_true hE, fun e he => ?_⟩
  by_cases heH : e ∈ H
  · exact Or.inl (hH.1.2 e heH)
  right
  intro a hae
  have hee := (hE.1.1.1 e he).1
  set c := orth a * a
  have hcc : Perp c c := by have := oap25 a; rwa [oap17] at this
  have hce : c ≤ e := le_trans (emul_le_right _ _) hae
  -- `2(a^⊥a) ≤ e`: the print computes `2(a^⊥a)·e = 2(a^⊥a)`; OAP 23 says the same
  have hde : c ⋎ c ≤ e := oap23 hee hce hce hcc
  set q := ceil (c ⋎ c)
  have hqe : q ≤ e := ceil_le hee hde
  have hq : q * q = q := ceil_idem _
  have hqh : IsHalvable q := oap51 ⟨c, hcc, rfl⟩
  have horth : ∀ h ∈ H, q * h = 0 := by
    intro h hh
    have hne : e ≠ h := fun h' => heH (h' ▸ hh)
    have heh : e * h = 0 := (hE.1.1.2 he (hHE hh) hne).1
    calc q * h = q * e * h := by rw [emul_eq_of_le' hee hqe]
      _ = 0 := by rw [emul_assoc, heh, emul_zero]
  have hq0 : q = 0 := eq_zero_of_maximal_family IsHalvable hH hq hqh horth
  have hcq : c ≤ q := le_trans (le_oplus_left hcc) (le_ceil _)
  rw [hq0] at hcq
  have hc0 : c = 0 := eq_zero_of_le_zero hcq
  exact (oap18 a).2 (by rw [oap17]; exact hc0)

end Families

/-! ## OAP 53: the embedding into the product of corners -/

section OAP53

variable {M : Type u} [EffectMonoid M]

/-- The corners `eM` of a set `F` of idempotents, as a family of effect
monoids. -/
noncomputable def cornerFamily (F : Set M) (hF : ∀ e ∈ F, e * e = e) :
    ∀ e : F, EffectMonoid (leftCorner e.1) :=
  fun e => cornerEffectMonoid e.1 (hF e.1 e.2)

/-- The product `⨁_{e∈F} eM` of the corners of a set of idempotents. -/
noncomputable def cornerPiEM (F : Set M) (hF : ∀ e ∈ F, e * e = e) :
    EffectMonoid (∀ e : F, leftCorner e.1) :=
  @piEffectMonoid _ (fun e : F => leftCorner e.1) (cornerFamily F hF)

/-- For an idempotent `e` (central by OAP 20), `a·b·e = (a·e)·(b·e)`. -/
theorem mul_mul_idem {e : M} (he : e * e = e) (a b : M) : a * b * e = a * e * (b * e) := by
  rw [emul_assoc a e, ← emul_assoc e b e, oap20 he b, emul_assoc b e e, he, emul_assoc]

/-- The map `a ↦ (a·e)_{e∈F} : M → ⨁_{e∈F} eM` (`a·e = e·a ∈ eM` by OAP 20)
is an effect monoid morphism. -/
noncomputable def cornerPiHom (F : Set M) (hF : ∀ e ∈ F, e * e = e) :
    @EffectMonoidHom M (∀ e : F, leftCorner e.1) _ (cornerPiEM F hF) :=
  letI := cornerPiEM F hF
  { toFun := fun a e => ⟨a * e.1, a, oap20 (hF e.1 e.2) a⟩
    perp_map := fun {a b} h e => (oplus_mul e.1 h).1
    ovee_map := fun {a b} h => funext fun e => Subtype.ext (by
      show ovee a b h * e.1 = a * e.1 ⋎ b * e.1
      rw [← oplus_eq h]; exact (oplus_mul e.1 h).2)
    map_one := funext fun e => Subtype.ext (eone_mul e.1)
    map_mul := fun a b => funext fun e => Subtype.ext (mul_mul_idem (hF e.1 e.2) a b) }

theorem cornerPiHom_apply (F : Set M) (hF : ∀ e ∈ F, e * e = e) (a : M) (e : F) :
    letI := cornerPiEM F hF
    ((cornerPiHom F hF).toFun a e).1 = a * e.1 := rfl

/-- The order of `⨁_{e∈F} eM` read off at `(a·e)_e`, `(b·e)_e`. -/
theorem cornerPiHom_le_iff (F : Set M) (hF : ∀ e ∈ F, e * e = e) (a b : M) :
    letI := cornerPiEM F hF
    @PCM.le _ (cornerPiEM F hF).toPCM ((cornerPiHom F hF).toFun a)
      ((cornerPiHom F hF).toFun b) ↔ ∀ e ∈ F, a * e ≤ b * e := by
  let _ := cornerFamily F hF
  refine (pi_le_iff (α := fun e : F => leftCorner e.1)).trans ⟨fun h e he => ?_, fun h e => ?_⟩
  · exact (corner_le_iff (hF e he)).1 (h ⟨e, he⟩)
  · exact (corner_le_iff (hF e.1 e.2)).2 (h e.1 e.2)

variable [OmegaComplete M]

/-- The core of the proof of OAP 53: a maximal collection `E` of non-zero
orthogonal idempotents has supremum `1`.  For an upper bound `u`, `⌊u⌋` is an
upper bound too, so the idempotent `⌊u⌋^⊥ = ⌈u^⊥⌉` is orthogonal to `E`,
hence `0` by maximality; thus `u^⊥ = 0`. -/
theorem isLUB_one_of_maximal {E : Set M} (hE : Maximal IsOrthIdemFamily E) : IsLUB E 1 := by
  refine ⟨fun e _ => le_one' e, fun u hu => ?_⟩
  have hf : ∀ e ∈ E, e ≤ floor u := fun e he => le_floor (hE.1.1 e he).1 (hu he)
  have hq : orth (floor u) * orth (floor u) = orth (floor u) := idem_orth (floor_idem u)
  have horth : ∀ e ∈ E, orth (floor u) * e = 0 := fun e he =>
    orth_emul_eq_zero_of_le (floor_idem u) (hf e he)
  have hq0 : orth (floor u) = 0 :=
    eq_zero_of_maximal_family (fun _ => True) (maximal_true_of_maximal hE) hq trivial horth
  have h1 : orth u ≤ orth (floor u) := by rw [(oap35_3 u).2]; exact le_ceil _
  rw [hq0] at h1
  have h2 : orth u = 0 := eq_zero_of_le_zero h1
  have h3 : u = 1 := by rw [← orth_orth u, h2, ← oap1_one_eq_orth_zero]
  rw [h3]

/-- The order-reflection step of OAP 53: if `a·e ≤ b·e` for all `e` of a
maximal family `E`, then `a = a·⋁E = ⋁ a·e ≤ b` (OAP 43). -/
theorem le_of_mul_le_of_maximal {E : Set M} (hE : Maximal IsOrthIdemFamily E) {a b : M}
    (h : ∀ e ∈ E, a * e ≤ b * e) : a ≤ b := by
  have h1 := isLUB_one_of_maximal hE
  rcases E.eq_empty_or_nonempty with hE0 | hne
  · rw [hE0] at h1
    exact le_trans (le_one' a) (h1.2 (by simp))
  · have h2 := isLUB_mul_left hne h1 a
    rw [emul_one] at h2
    exact h2.2 (by rintro _ ⟨e, he, rfl⟩; exact le_trans (h e he) (emul_le_left b e))

/-- **OAP 53** (first.tex:2001, Proposition): for a maximal orthogonal
collection `E` of non-zero idempotents of an ω-complete effect monoid `M`,
`a ↦ (a·e)_e : M → ⨁_{e∈E} Me` is an embedding of effect monoids.  (`⨁` of
the family is the product `∏_{e∈E} eM`; `Me = eM` by OAP 12.) -/
theorem oap53 {E : Set M} (hE : Maximal IsOrthIdemFamily E) :
    letI := cornerPiEM E fun e he => (hE.1.1 e he).1
    ∃ f : @EMEmbedding M (∀ e : E, leftCorner e.1) _
        (cornerPiEM E fun e he => (hE.1.1 e he).1),
      ∀ a (e : E), (f.toFun a e).1 = a * e.1 := by
  have hF : ∀ e ∈ E, e * e = e := fun e he => (hE.1.1 e he).1
  let _ := cornerPiEM E hF
  exact ⟨{ cornerPiHom E hF with
    reflect := fun {a b} h =>
      le_of_mul_le_of_maximal hE ((cornerPiHom_le_iff E hF a b).1 h) }, fun _ _ => rfl⟩

end OAP53

/-! ## OAP 54: embedding into a convex and a Boolean part -/

section OAP54

variable {M : Type u} [EffectMonoid M]

/-- Pairing of effect monoid morphisms `M → N₁`, `M → N₂` into `N₁ ⊕ N₂`. -/
def EffectMonoidHom.pair {N₁ N₂ : Type u} [EffectMonoid N₁] [EffectMonoid N₂]
    (f : EffectMonoidHom M N₁) (g : EffectMonoidHom M N₂) : EffectMonoidHom M (N₁ × N₂) where
  toFun a := (f.toFun a, g.toFun a)
  perp_map h := ⟨f.perp_map h, g.perp_map h⟩
  ovee_map h := Prod.ext (f.ovee_map h) (g.ovee_map h)
  map_one := Prod.ext f.map_one g.map_one
  map_mul a b := Prod.ext (f.map_mul a b) (g.map_mul a b)

variable [OmegaComplete M]

/-- **OAP 54** (`thm:omegacompleteembed`, first.tex:2036, Theorem): an
ω-complete effect monoid `M` embeds into `M₁ ⊕ M₂` with `M₁`, `M₂`
ω-complete, `M₁` convex and `M₂` an ω-complete Boolean algebra (in the form of
OAP 47: `M₂` is Boolean, `M₂ ≅ P(M₂)`, and countable subsets of `P(M₂)` have
suprema).  As printed: `E = H ∪ B` from OAP 52, `M₁ = ⨁_{p∈H} pM` is
halvable hence convex (OAP 50), `M₂ = ⨁_{q∈B} qM` is Boolean (OAP 47), and
`M` embeds by OAP 53. -/
theorem oap54 :
    ∃ (M₁ M₂ : Type u) (_ : EffectMonoid M₁) (_ : EffectMonoid M₂),
      OmegaComplete M₁ ∧ OmegaComplete M₂ ∧ IsConvex M₁ ∧
      (∃ hB : IsBooleanEM M₂,
        @EMIsIso M₂ (idempotents M₂) _ (booleanEffectMonoid _) (booleanIso hB) ∧
        ∀ A : Set (idempotents M₂), A.Countable → ∃ s, IsLUB A s) ∧
      Nonempty (EMEmbedding M (M₁ × M₂)) := by
  obtain ⟨E, hE, hHB⟩ := oap52 (M := M)
  have hEi : ∀ e ∈ E, e * e = e := fun e he => (hE.1.1 e he).1
  let H : Set M := {e | e ∈ E ∧ IsHalvable e}
  let B : Set M := {e | e ∈ E ∧ ¬ IsHalvable e}
  have hHi : ∀ e ∈ H, e * e = e := fun e he => hEi e he.1
  have hBi : ∀ e ∈ B, e * e = e := fun e he => hEi e he.1
  let _ := cornerFamily H hHi
  let _ := cornerFamily B hBi
  let _i1 := cornerPiEM H hHi
  let _i2 := cornerPiEM B hBi
  have hω : ∀ (F : Set M) (hF : ∀ e ∈ F, e * e = e),
      @OmegaComplete _ (cornerPiEM F hF).toEffectAlgebra := fun F hF =>
    @pi_omegaComplete _ (fun e : F => leftCorner e.1) (fun e => (cornerFamily F hF e).toEffectAlgebra)
      (fun e => corner_omegaComplete (hF e.1 e.2))
  have hω1 : OmegaComplete (∀ e : H, leftCorner e.1) := hω H hHi
  have hω2 : OmegaComplete (∀ e : B, leftCorner e.1) := hω B hBi
  have hBool : IsBooleanEM (∀ e : B, leftCorner e.1) :=
    @pi_isBooleanEM _ (fun e : B => leftCorner e.1) (cornerFamily B hBi) fun e =>
      corner_isBooleanEM (hBi e.1 e.2) ((hHB e.1 e.2.1).resolve_left e.2.2)
  refine ⟨∀ e : H, leftCorner e.1, ∀ e : B, leftCorner e.1, _i1, _i2, hω1, hω2, ?_,
    ⟨hBool, (oap47 hBool).1, (oap47 hBool).2.1⟩, ⟨?_⟩⟩
  · exact oap50 (@pi_halvable _ (fun e : H => leftCorner e.1)
      (fun e => (cornerFamily H hHi e).toEffectAlgebra)
      fun e => corner_halvable (hHi e.1 e.2) e.2.2)
  · refine { EffectMonoidHom.pair (cornerPiHom H hHi) (cornerPiHom B hBi) with
      reflect := fun {a b} h => le_of_mul_le_of_maximal hE fun e he => ?_ }
    have h' := prod_le_iff.1 h
    by_cases hh : IsHalvable e
    · exact (cornerPiHom_le_iff H hHi a b).1 h'.1 e ⟨he, hh⟩
    · exact (cornerPiHom_le_iff B hBi a b).1 h'.2 e ⟨he, hh⟩

end OAP54

/-! ## OAP 55: the embedding of OAP 54 is not an isomorphism in general -/

section Sub

variable {N : Type u} [EffectMonoid N]

/-- A subset of an effect monoid containing `0` and closed under `(·)^⊥`,
defined sums and products: a sub-effect monoid. -/
structure IsSubEM (S : Set N) : Prop where
  zero_mem : (0 : N) ∈ S
  orth_mem : ∀ x ∈ S, orth x ∈ S
  oplus_mem : ∀ x ∈ S, ∀ y ∈ S, Perp x y → x ⋎ y ∈ S
  mul_mem : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S

variable {S : Set N} (hS : IsSubEM S)
include hS

/-- The effect algebra structure of a sub-effect monoid. -/
noncomputable def subEffectAlgebra : EffectAlgebra S where
  zero := ⟨0, hS.zero_mem⟩
  one := ⟨1, by rw [oap1_one_eq_orth_zero]; exact hS.orth_mem 0 hS.zero_mem⟩
  Perp x y := Perp x.1 y.1
  ovee x y h := ⟨x.1 ⋎ y.1, hS.oplus_mem _ x.2 _ y.2 h⟩
  orth x := ⟨orth x.1, hS.orth_mem _ x.2⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := Subtype.ext (oplus_comm _ _)
  perp_of_ovee_perp hab h := perp_of_oplus_perp hab h
  perp_ovee_of_ovee_perp hab h := perp_oplus_of_oplus_perp hab h
  ovee_assoc hab h := Subtype.ext (oplus_assoc hab h)
  zero_perp a := zero_perp a.1
  zero_ovee a := Subtype.ext (zero_oplus a.1)
  perp_orth x := perp_orth x.1
  ovee_orth x := Subtype.ext (oplus_orth x.1)
  orth_unique h e := Subtype.ext (eq_orth_of_oplus h (congrArg Subtype.val e))
  eq_zero_of_perp_one h := Subtype.ext (perp_one_iff.1 h)

theorem sub_oplus {x y : S} (h : @Perp _ (subEffectAlgebra hS).toPCM x y) :
    (@oplus _ (subEffectAlgebra hS) x y).1 = x.1 ⋎ y.1 := by
  let _ := subEffectAlgebra hS
  rw [oplus_eq h]; rfl

/-- The order of a sub-effect monoid is the restricted order: `y ⊖ x =
(x ⋁ y^⊥)^⊥` stays in `S`. -/
theorem sub_le_iff {x y : S} : @PCM.le _ (subEffectAlgebra hS).toPCM x y ↔ x.1 ≤ y.1 := by
  let _ := subEffectAlgebra hS
  constructor
  · rintro ⟨c, h, e⟩
    exact le_def.2 ⟨c.1, h, by rw [← congrArg Subtype.val e]; rfl⟩
  · intro hxy
    have hxy' : Perp x.1 (orth y.1) := perp_iff_le_orth.2 (by rw [orth_orth]; exact hxy)
    have hmem : y.1 ⊖ x.1 ∈ S := by
      have e : y.1 ⊖ x.1 = orth (x.1 ⋎ orth y.1) := by
        have h1 := perp_osub hxy
        have h2 := oplus_osub hxy
        have h3 : Perp (orth y.1) (x.1 ⋎ (y.1 ⊖ x.1)) := by
          rw [h2]; exact PCM.perp_comm (perp_orth y.1)
        obtain ⟨h4, h5⟩ := perp_assoc_left h1 h3
        refine eq_orth_of_oplus (a := x.1 ⋎ orth y.1) ?_ ?_
        · rw [oplus_comm]; exact h5
        · rw [oplus_comm x.1, oplus_assoc h4 h5, h2]; exact orth_oplus y.1
      rw [e]; exact hS.orth_mem _ (hS.oplus_mem _ x.2 _ (hS.orth_mem _ y.2) hxy')
    refine ⟨⟨y.1 ⊖ x.1, hmem⟩, perp_osub hxy, Subtype.ext ?_⟩
    exact oplus_osub hxy

/-- A sub-effect monoid is an effect monoid. -/
noncomputable def subEffectMonoid : EffectMonoid S :=
  letI := subEffectAlgebra hS
  letI : Mul S := ⟨fun x y => ⟨x.1 * y.1, hS.mul_mem _ x.2 _ y.2⟩⟩
  EffectMonoid.ofBiadditive S
    (fun a => Subtype.ext (eone_mul a.1))
    (fun a => Subtype.ext (emul_one a.1))
    (fun a b c => Subtype.ext (emul_assoc a.1 b.1 c.1).symm)
    (fun a b c h => by
      have h' : Perp (a * b) (a * c) := (mul_oplus a.1 h).1
      refine ⟨h', Subtype.ext ?_⟩
      show a.1 * (b ⋎ c).1 = (a * b ⋎ a * c).1
      rw [sub_oplus hS h, sub_oplus hS h']
      exact (mul_oplus a.1 h).2)
    (fun a b c h => by
      have h' : Perp (b * a) (c * a) := (oplus_mul a.1 h).1
      refine ⟨h', Subtype.ext ?_⟩
      show (b ⋎ c).1 * a.1 = (b * a ⋎ c * a).1
      rw [sub_oplus hS h, sub_oplus hS h']
      exact (oplus_mul a.1 h).2)

end Sub

section Transport

/-- Effect algebra morphisms preserve halvability. -/
theorem IsHalvable.map {E F : Type u} [EffectAlgebra E] [EffectAlgebra F] (f : EAHom E F)
    {a : E} (h : IsHalvable a) : IsHalvable (f.toFun a) := by
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨f.toFun b, f.perp_map hb, by rw [oplus_eq hb, oplus_eq (f.perp_map hb), f.ovee_map]⟩

/-- A convex effect algebra is halvable: `½·1 ⋁ ½·1 = 1·1 = 1`. -/
theorem halvable_of_convex {E : Type u} [EffectAlgebra E] (h : IsConvex E) : HalvableEA E := by
  obtain ⟨c⟩ := h
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨hp, e⟩ := c.add_act half half 1 1 (by
    show (1 / 2 : ℝ) + 1 / 2 = ((1 : I) : ℝ)
    rw [Set.Icc.coe_one]; norm_num)
  exact ⟨c.act half 1, hp, by rw [e, c.one_act]⟩

variable {M₁ M₂ : Type u} [EffectMonoid M₁] [EffectMonoid M₂]

/-- In `M₁ ⊕ M₂` with `M₁` halvable and `M₂` Boolean, `(1, 0)` is a halvable
idempotent above every halvable element (a halvable element of the Boolean
`M₂` is `0`). -/
theorem prod_halvable_idem (h1 : HalvableEA M₁) (h2 : IsBooleanEM M₂) :
    ((1, 0) : M₁ × M₂) * (1, 0) = (1, 0) ∧ IsHalvable ((1, 0) : M₁ × M₂) ∧
      ∀ x : M₁ × M₂, IsHalvable x → x ≼ (1, 0) := by
  refine ⟨Prod.ext (eone_mul 1) (ezero_mul 0), ?_, fun x hx => ?_⟩
  · obtain ⟨b, hb, e⟩ := h1
    have hp : Perp ((b, 0) : M₁ × M₂) (b, 0) := ⟨hb, zero_perp 0⟩
    exact ⟨(b, 0), hp, by rw [prod_oplus hp, e, oplus_zero]⟩
  · obtain ⟨b, hb, rfl⟩ := hx
    have h0 : b.2 ⋎ b.2 = 0 :=
      eq_zero_of_halvable_boolean ⟨b.2, hb.2, rfl⟩ fun c _ => isBooleanEM_iff.1 h2 c
    refine prod_le_iff.2 ⟨?_, ?_⟩
    · exact le_one' _
    · show (b ⋎ b).2 ≤ 0
      have e : (b ⋎ b).2 = b.2 ⋎ b.2 := by rw [prod_oplus hb]
      rw [e, h0]

end Transport

namespace Ex55

open Classical

variable (X₁ X₂ : Type u)

/-- A point outside a countable subset of an uncountable type. -/
theorem exists_not_mem {α : Type u} [Uncountable α] {s : Set α} (hs : s.Countable) :
    ∃ a, a ∉ s := by
  by_contra h
  push Not at h
  exact not_countable (Set.countable_univ_iff.1 (hs.mono fun a _ => h a))

/-- The example's condition on `f = (f₁, f₂) : X₁ ⊔ X₂ → [0,1]`: `f₂` is
`{0,1}`-valued, and `f ∈ S₀` (`f ≠ 0` only at countably many points) or
`f ∈ S₁` (`f ≠ 1` only at countably many points). -/
def P (g : X₁ ⊕ X₂ → ℝ) : Prop :=
  (∀ y, g (Sum.inr y) = 0 ∨ g (Sum.inr y) = 1) ∧
    ({i | g i ≠ 0}.Countable ∨ {i | g i ≠ 1}.Countable)

variable {X₁ X₂}

theorem P_zero : P X₁ X₂ 0 :=
  ⟨fun _ => Or.inl rfl, Or.inl (by simp)⟩

theorem P_orth {g : X₁ ⊕ X₂ → ℝ} (hg : P X₁ X₂ g) : P X₁ X₂ (1 - g) := by
  refine ⟨fun y => ?_, ?_⟩
  · rcases hg.1 y with h | h <;> simp [h]
  · rcases hg.2 with h | h
    · refine Or.inr (h.mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.one_apply] at hi ⊢
      intro h0; apply hi; rw [h0]; norm_num
    · refine Or.inl (h.mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.one_apply] at hi ⊢
      intro h1; apply hi; rw [h1]; norm_num

theorem P_add [Uncountable X₁] {g h : X₁ ⊕ X₂ → ℝ}
    (hgh : ∀ i, g i + h i ≤ 1) (hg : P X₁ X₂ g) (hh : P X₁ X₂ h) : P X₁ X₂ (g + h) := by
  refine ⟨fun y => ?_, ?_⟩
  · have := hgh (Sum.inr y)
    simp only [Pi.add_apply] at this ⊢
    rcases hg.1 y with h1 | h1 <;> rcases hh.1 y with h2 | h2 <;> rw [h1, h2] at this ⊢
    · left; norm_num
    · right; norm_num
    · right; norm_num
    · norm_num at this
  · rcases hg.2 with h1 | h1 <;> rcases hh.2 with h2 | h2
    · refine Or.inl ((h1.union h2).mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at hi ⊢
      by_contra hc; push Not at hc; apply hi; rw [hc.1, hc.2]; norm_num
    · refine Or.inr ((h1.union h2).mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at hi ⊢
      by_contra hc; push Not at hc; apply hi; rw [hc.1, hc.2]; norm_num
    · refine Or.inr ((h1.union h2).mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at hi ⊢
      by_contra hc; push Not at hc; apply hi; rw [hc.1, hc.2]; norm_num
    · exfalso
      obtain ⟨x, hx⟩ := exists_not_mem ((h1.union h2).preimage Sum.inl_injective)
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hx
      have := hgh (Sum.inl x)
      rw [hx.1, hx.2] at this; norm_num at this

theorem P_mul {g h : X₁ ⊕ X₂ → ℝ} (hg : P X₁ X₂ g) (hh : P X₁ X₂ h) : P X₁ X₂ (g * h) := by
  refine ⟨fun y => ?_, ?_⟩
  · rcases hg.1 y with h1 | h1 <;> rcases hh.1 y with h2 | h2 <;> simp [h1, h2]
  · rcases hg.2 with h1 | h1
    · refine Or.inl (h1.mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Pi.mul_apply] at hi ⊢
      intro h0; apply hi; rw [h0, zero_mul]
    rcases hh.2 with h2 | h2
    · refine Or.inl (h2.mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Pi.mul_apply] at hi ⊢
      intro h0; apply hi; rw [h0, mul_zero]
    · refine Or.inr ((h1.union h2).mono fun i hi => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.mul_apply] at hi ⊢
      by_contra hc; push Not at hc; apply hi; rw [hc.1, hc.2, one_mul]

/-- The ambient effect monoid `A = [0,1]_{ℝ^{X₁⊔X₂}}` (OAP 7). -/
noncomputable def ambient : EffectMonoid (Set.Icc (0 : X₁ ⊕ X₂ → ℝ) 1) :=
  unitIntervalEffectMonoid _

attribute [local instance] ambient

variable (X₁ X₂) in
/-- The example's `M = S₀ ∪ S₁ ⊆ A`, as a subset of `[0,1]_{ℝ^{X₁⊔X₂}}`. -/
def carrier : Set (Set.Icc (0 : X₁ ⊕ X₂ → ℝ) 1) := {f | P X₁ X₂ f.1}

theorem ambient_oplus {x y : Set.Icc (0 : X₁ ⊕ X₂ → ℝ) 1} (h : Perp x y) :
    (x ⋎ y).1 = x.1 + y.1 := by
  rw [oplus_eq h]; rfl

theorem isSubEM_carrier [Uncountable X₁] : IsSubEM (carrier X₁ X₂) where
  zero_mem := P_zero
  orth_mem x hx := P_orth hx
  oplus_mem x hx y hy h := by
    show P X₁ X₂ (x ⋎ y).1
    rw [ambient_oplus h]
    have h' : x.1 + y.1 ≤ 1 := h
    exact P_add (fun i => h' i) hx hy
  mul_mem x hx y hy := P_mul hx hy

variable (X₁ X₂) in
/-- **OAP 55**: the effect monoid `M = S₀ ∪ S₁` of the example. -/
def M55 : Type u := carrier X₁ X₂

noncomputable instance [Uncountable X₁] : EffectMonoid (M55 X₁ X₂) :=
  subEffectMonoid isSubEM_carrier

/-- The function `(f₁, f₂) : X₁ ⊔ X₂ → [0,1]` of an element of `M`. -/
def val (x : M55 X₁ X₂) : X₁ ⊕ X₂ → ℝ := x.1.1

theorem val_nonneg (x : M55 X₁ X₂) (i : X₁ ⊕ X₂) : 0 ≤ val x i := x.1.2.1 i

theorem val_le_one (x : M55 X₁ X₂) (i : X₁ ⊕ X₂) : val x i ≤ 1 := x.1.2.2 i

theorem val_P (x : M55 X₁ X₂) : P X₁ X₂ (val x) := x.2

/-- An element of `M` from a function. -/
def mk (g : X₁ ⊕ X₂ → ℝ) (h0 : ∀ i, 0 ≤ g i) (h1 : ∀ i, g i ≤ 1) (hP : P X₁ X₂ g) :
    M55 X₁ X₂ :=
  ⟨⟨g, h0, h1⟩, hP⟩

theorem val_mk (g : X₁ ⊕ X₂ → ℝ) (h0 h1 hP) : val (mk g h0 h1 hP) = g := rfl

theorem ext {x y : M55 X₁ X₂} (h : ∀ i, val x i = val y i) : x = y :=
  Subtype.ext (Subtype.ext (funext h))

variable [Uncountable X₁]

/-- The order of `M` is the pointwise order. -/
theorem le_iff {x y : M55 X₁ X₂} : x ≤ y ↔ ∀ i, val x i ≤ val y i :=
  (sub_le_iff isSubEM_carrier).trans ((oap3_le_iff _ 1 zero_le_one x.1 y.1).trans Pi.le_def)

theorem perp_iff {x y : M55 X₁ X₂} : Perp x y ↔ ∀ i, val x i + val y i ≤ 1 := by
  show x.1.1 + y.1.1 ≤ 1 ↔ _
  exact Pi.le_def

theorem val_oplus {x y : M55 X₁ X₂} (h : Perp x y) : val (x ⋎ y) = val x + val y := by
  rw [oplus_eq h]
  show (x.1 ⋎ y.1).1 = _
  rw [ambient_oplus h]; rfl

theorem val_mul (x y : M55 X₁ X₂) : val (x * y) = val x * val y := rfl

/-- **OAP 55**, first claim: `M` is an ω-complete effect monoid (it is an
effect monoid by construction).  The supremum of an increasing sequence is
its pointwise supremum: it stays in `S₀` if every term is in `S₀` (a countable
union of countable sets), and is in `S₁` as soon as one term is. -/
theorem oap55_omegaComplete : OmegaComplete (M55 X₁ X₂) := by
  refine ⟨fun f hf => ?_⟩
  have hbdd : ∀ i, BddAbove (Set.range fun n => val (f n) i) :=
    fun i => ⟨1, by rintro _ ⟨n, rfl⟩; exact val_le_one _ _⟩
  let s : X₁ ⊕ X₂ → ℝ := fun i => ⨆ n, val (f n) i
  have hle : ∀ n i, val (f n) i ≤ s i := fun n i => le_ciSup (hbdd i) n
  have hs1 : ∀ i, s i ≤ 1 := fun i => ciSup_le fun n => val_le_one _ _
  have hs0 : ∀ i, 0 ≤ s i := fun i => le_trans (val_nonneg (f 0) i) (hle 0 i)
  have hs_one : ∀ n i, val (f n) i = 1 → s i = 1 := fun n i h =>
    le_antisymm (hs1 i) (h ▸ hle n i)
  have hs_zero : ∀ i, (∀ n, val (f n) i = 0) → s i = 0 := fun i h =>
    le_antisymm (ciSup_le fun n => (h n).le) (hs0 i)
  have hP : P X₁ X₂ s := by
    refine ⟨fun y => ?_, ?_⟩
    · by_cases h : ∃ n, val (f n) (Sum.inr y) = 1
      · obtain ⟨n, hn⟩ := h
        exact Or.inr (hs_one n _ hn)
      · push Not at h
        exact Or.inl (hs_zero _ fun n => ((val_P (f n)).1 y).resolve_right (h n))
    · by_cases h : ∃ n, {i | val (f n) i ≠ 1}.Countable
      · obtain ⟨n, hn⟩ := h
        refine Or.inr (hn.mono fun i hi => ?_)
        simp only [Set.mem_ofPred_eq] at hi ⊢
        exact fun h1 => hi (hs_one n i h1)
      · push Not at h
        refine Or.inl ((Set.countable_iUnion fun n =>
          (val_P (f n)).2.resolve_right (h n)).mono fun i hi => ?_)
        simp only [Set.mem_ofPred_eq] at hi
        by_contra hc
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hc
        exact hi (hs_zero i hc)
  refine ⟨mk s hs0 hs1 hP, ?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact le_iff.2 fun i => hle n i
  · exact le_iff.2 fun i => ciSup_le fun n => le_iff.1 (hu ⟨n, rfl⟩) i

theorem val_idem {x : M55 X₁ X₂} (h : x * x = x) (i : X₁ ⊕ X₂) :
    val x i = 0 ∨ val x i = 1 := by
  have e : val x i * val x i = val x i := by
    have := congrArg (fun z => val z i) h
    simpa [val_mul] using this
  have : val x i * (val x i - 1) = 0 := by rw [mul_sub, e, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

/-- A halvable element of `M` vanishes on `X₂` (`f₂` is `{0,1}`-valued, so
its half is `0` there). -/
theorem val_inr_of_halvable {x : M55 X₁ X₂} (h : IsHalvable x) (y : X₂) :
    val x (Sum.inr y) = 0 := by
  obtain ⟨b, hbb, rfl⟩ := h
  rw [val_oplus hbb]
  have h1 := perp_iff.1 hbb (Sum.inr y)
  rcases (val_P b).1 y with h0 | h0
  · simp [h0]
  · rw [h0] at h1; norm_num at h1

variable [Uncountable X₂]

/-- **OAP 55**, second claim: `M` has no maximal halvable idempotent.  A
halvable idempotent `p` vanishes on `X₂`, so it lies in `S₀`; adding one of
the uncountably many points of `X₁` where `p = 0` gives a strictly larger
halvable idempotent. -/
theorem oap55_no_maximal :
    ¬ ∃ p : M55 X₁ X₂, Maximal (fun q => q * q = q ∧ IsHalvable q) p := by
  rintro ⟨p, ⟨hpi, hph⟩, hmax⟩
  have hinr := val_inr_of_halvable hph
  have hS0 : {i | val p i ≠ 0}.Countable := by
    refine (val_P p).2.resolve_right fun hc => ?_
    obtain ⟨y, hy⟩ := exists_not_mem (hc.preimage Sum.inr_injective)
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not, hinr y] at hy
    norm_num at hy
  obtain ⟨j, hj⟩ := exists_not_mem (hS0.preimage Sum.inl_injective)
  have hj0 : val p (Sum.inl j) = 0 := by
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] using hj
  let g : X₁ ⊕ X₂ → ℝ := fun i => if i = Sum.inl j then 1 else val p i
  have hg01 : ∀ i, g i = 0 ∨ g i = 1 := fun i => by
    by_cases hi : i = Sum.inl j
    · simp [g, hi]
    · simp only [g, hi, ite_false]; exact val_idem hpi i
  have hg0 : ∀ i, 0 ≤ g i := fun i => by rcases hg01 i with h | h <;> simp [h]
  have hg1 : ∀ i, g i ≤ 1 := fun i => by rcases hg01 i with h | h <;> simp [h]
  have hginr : ∀ y, g (Sum.inr y) = 0 := fun y => by simp [g, hinr y]
  have hgS0 : {i | g i ≠ 0}.Countable := by
    refine (hS0.union (Set.countable_singleton (Sum.inl j))).mono fun i hi => ?_
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff] at hi ⊢
    by_cases h : i = Sum.inl j
    · exact Or.inr h
    · left; simpa [g, h] using hi
  let q := mk g hg0 hg1 ⟨fun y => Or.inl (hginr y), Or.inl hgS0⟩
  have hq : q * q = q := ext fun i => by
    show g i * g i = g i
    rcases hg01 i with h | h <;> rw [h] <;> norm_num
  -- the half of `q`
  have hh0 : ∀ i, 0 ≤ g i / 2 := fun i => by have := hg0 i; positivity
  have hh1 : ∀ i, g i / 2 ≤ 1 := fun i => by have := hg1 i; linarith
  have hhP : P X₁ X₂ fun i => g i / 2 := by
    refine ⟨fun y => Or.inl (by simp [hginr y]), Or.inl (hgS0.mono fun i hi => ?_)⟩
    simp only [Set.mem_ofPred_eq] at hi ⊢
    intro h0; apply hi; simp [h0]
  let hf := mk (fun i => g i / 2) hh0 hh1 hhP
  have hff : Perp hf hf := perp_iff.2 fun i => by
    show g i / 2 + g i / 2 ≤ 1
    linarith [hg1 i]
  have hqh : IsHalvable q := ⟨hf, hff, ext fun i => by
    rw [val_oplus hff]
    show g i / 2 + g i / 2 = g i
    ring⟩
  have hpq : p ≤ q := le_iff.2 fun i => by
    show val p i ≤ g i
    by_cases hi : i = Sum.inl j
    · simp only [g, hi, ite_true]; rw [hj0]; norm_num
    · simp [g, hi]
  have hqp := le_iff.1 (hmax ⟨hq, hqh⟩ hpq) (Sum.inl j)
  have : val q (Sum.inl j) = 1 := by show g (Sum.inl j) = 1; simp [g]
  rw [this, hj0] at hqp
  norm_num at hqp

/-- **OAP 55**, third claim: `M` is not `M₁ ⊕ M₂` for any halvable `M₁` and
Boolean `M₂`: an isomorphism would carry the greatest halvable idempotent
`(1, 0)` of `M₁ ⊕ M₂` to a maximal halvable idempotent of `M`. -/
theorem oap55_not_iso {M₁ M₂ : Type u} [EffectMonoid M₁] [EffectMonoid M₂]
    (h1 : HalvableEA M₁) (h2 : IsBooleanEM M₂) (f : EffectMonoidHom (M55 X₁ X₂) (M₁ × M₂)) :
    ¬ EMIsIso f := by
  rintro ⟨g, hgf, -⟩
  obtain ⟨hi, hh, hle⟩ := prod_halvable_idem h1 h2
  apply oap55_no_maximal (X₁ := X₁) (X₂ := X₂)
  refine ⟨g.toFun (1, 0), ⟨by rw [← g.map_mul, hi], hh.map g.toEAHom⟩,
    fun q ⟨_, hqh⟩ _ => ?_⟩
  have := exc_eamorphism_monotone g.toEAHom (hle _ (hqh.map f.toEAHom))
  rw [hgf] at this
  exact this

/-- **OAP 55** (first.tex:2056, Example): for uncountable `X₁`, `X₂`, the
effect monoid `M = S₀ ∪ S₁` is ω-complete, has no maximal halvable
idempotent, and is not isomorphic to `M₁ ⊕ M₂` for any halvable `M₁` and
Boolean `M₂`.  (The print's "straightforward to check" is checked here:
`M` is a sub-effect monoid of `[0,1]_{ℝ^{X₁⊔X₂}}` because a sum of two
elements of `S₁` never exists, and its order is the pointwise order.) -/
theorem oap55 :
    OmegaComplete (M55 X₁ X₂) ∧
      (¬ ∃ p : M55 X₁ X₂, Maximal (fun q => q * q = q ∧ IsHalvable q) p) ∧
      ∀ (M₁ M₂ : Type u) [EffectMonoid M₁] [EffectMonoid M₂], HalvableEA M₁ →
        IsBooleanEM M₂ → ∀ f : EffectMonoidHom (M55 X₁ X₂) (M₁ × M₂), ¬ EMIsIso f :=
  ⟨oap55_omegaComplete, oap55_no_maximal,
    fun _ _ _ _ h1 h2 f => oap55_not_iso h1 h2 f⟩

/-- **OAP 55**, the point of the example: the embedding of OAP 54 cannot be
strengthened to an isomorphism — the ω-complete `M` is not `M₁ ⊕ M₂` with
`M₁` convex and `M₂` Boolean (a convex effect algebra is halvable). -/
theorem oap55_not_oap54_iso {M₁ M₂ : Type u} [EffectMonoid M₁] [EffectMonoid M₂]
    (h1 : IsConvex M₁) (h2 : IsBooleanEM M₂) (f : EffectMonoidHom (M55 X₁ X₂) (M₁ × M₂)) :
    ¬ EMIsIso f :=
  oap55_not_iso (halvable_of_convex h1) h2 f

end Ex55

/-! ## OAP 56, OAP 57: the directed-complete case -/

section OAP56

variable {M : Type u} [EffectMonoid M]

/-- If `a` is maximal with `a ⊥ a`, `y ⊥ y` and `a ⋁ a ⊥ y ⋁ y`, then
`y = 0`: `a ⋁ y ≥ a` is summable with itself. -/
theorem eq_zero_of_maximal_self_perp {a : M} (ha : Maximal (fun s => Perp s s) a) {y : M}
    (hyy : Perp y y) (h : Perp (a ⋎ a) (y ⋎ y)) : y = 0 := by
  obtain ⟨hay, -, hsum, -⟩ := oplus_oplus_comm ha.1 hyy h
  have e : a ⋎ y = a := le_antisymm (ha.2 hsum (le_oplus_left hay)) (le_oplus_left hay)
  exact oplus_left_cancel hay (perp_zero a) (e.trans (oplus_zero a).symm)

variable [OmegaComplete M]

/-- OAP 56, point 1, as printed: for `b ⊥ a ⋁ a` (in the print
`b = (a ⋁ a)^⊥`), `b·(b·b^⊥) ⋁ b·(b·b^⊥) ≤ b`, so `b²b^⊥ = 0` by
maximality, hence `(b·b^⊥)² = 0`, `b·b^⊥ = 0` (OAP 26) and `b` is
idempotent (OAP 18). -/
theorem idem_of_perp_maximal {a b : M} (hm : Maximal (fun s => Perp s s) a)
    (hab : Perp (a ⋎ a) b) : b * b = b := by
  have hx := oap25 b
  obtain ⟨hbx, ebx⟩ := mul_oplus b hx
  have hle : b * (b * orth b) ⋎ b * (b * orth b) ≤ b := by rw [← ebx]; exact emul_le_left _ _
  have hc0 : b * (b * orth b) = 0 :=
    eq_zero_of_maximal_self_perp hm hbx (perp_of_le le_rfl hle hab)
  have hxx : b * orth b * (b * orth b) = 0 := by
    rw [emul_assoc b (orth b), ← emul_assoc (orth b) b, ← oap17 b,
      ← emul_assoc b (b * orth b), hc0, ezero_mul]
  exact (oap18 b).2 (oap26_2 hxx)

omit [OmegaComplete M] in
/-- OAP 56, point 2, as printed: for `s ≤ b` (`b` idempotent, `b ⊥ a ⋁ a`),
`s·s^⊥ ⋁ s·s^⊥ ≤ b` (OAP 25, OAP 23), so `s·s^⊥ = 0` by maximality. -/
theorem idem_of_le_perp_maximal {a b : M} (hm : Maximal (fun s => Perp s s) a)
    (hab : Perp (a ⋎ a) b) (hb : b * b = b) {s : M} (hs : s ≤ b) : s * s = s := by
  have hy := oap25 s
  have hyb : s * orth s ≤ b := le_trans (emul_le_left s _) hs
  have hle : s * orth s ⋎ s * orth s ≤ b := oap23 hb hyb hyb hy
  exact (oap18 s).2 (eq_zero_of_maximal_self_perp hm hy (perp_of_le le_rfl hle hab))

omit [OmegaComplete M] in
/-- **OAP 56** (`lem:maximalsummableelement`, first.tex:2077, Lemma): a
directed-complete effect monoid has an element `a` maximal among those with
`a ⊥ a`; moreover `a ⋁ a` is idempotent, and every `s ≤ (a ⋁ a)^⊥` is
idempotent.  Zorn's lemma as printed: a non-empty chain `D` of self-summable
elements has a supremum `s` (directed completeness), `d ⊥ d'` for
`d, d' ∈ D`, so `d ⊥ s` and then `s ⊥ s` because addition preserves suprema
(OAP 24). -/
theorem oap56 [DirectedComplete M] :
    ∃ a : M, (Perp a a ∧ ∀ b, a ≤ b → Perp b b → b = a) ∧
      (a ⋎ a) * (a ⋎ a) = a ⋎ a ∧ ∀ s : M, s ≤ orth (a ⋎ a) → s * s = s := by
  obtain ⟨a, ha⟩ := zorn_le₀ {s : M | Perp s s} (fun c hc hch => by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, zero_perp 0, by simp⟩
    obtain ⟨s, hs⟩ := DirectedComplete.exists_isLUB c ⟨hne, hch.directedOn⟩
    have hdd : ∀ d ∈ c, ∀ d' ∈ c, d' ≤ orth d := by
      intro d hd d' hd'
      rcases hch.total hd hd' with h | h
      · exact le_trans (le_orth_of_perp (hc hd')) (orth_le_orth h)
      · exact le_trans h (le_orth_of_perp (hc hd))
    -- `d ⋁ ⋁D = ⋁_{d'∈D} d ⋁ d'`: in particular `d ⊥ s`
    have hds : ∀ d ∈ c, d ≤ orth s := fun d hd =>
      le_orth_of_perp (PCM.perp_comm (oap24_1 hne (hdd d hd) hs).1)
    -- `(⋁D) ⋁ s = ⋁_{d∈D} d ⋁ s`: in particular `s ⊥ s`
    exact ⟨s, (oap24_1 hne hds hs).1, fun z hz => hs.1 hz⟩)
  have hm : Maximal (fun s : M => Perp s s) a := ha
  have hb := idem_of_perp_maximal hm (perp_orth (a ⋎ a))
  refine ⟨a, ⟨ha.1, fun b hab hb => le_antisymm (ha.2 hb hab) hab⟩, ?_,
    fun s hs => idem_of_le_perp_maximal hm (perp_orth (a ⋎ a)) hb hs⟩
  have := idem_orth hb
  rwa [orth_orth] at this

end OAP56

section OAP57

variable {N : Type u} [EffectMonoid N]

/-- "An adaptation of OAP 47 to directed-complete effect monoids": in a
directed-complete Boolean effect monoid every subset `A` of `P(N)` has a
supremum — the supremum of the directed set of finite joins of `A`, which is
idempotent because everything is. -/
theorem boolean_dc_isLUB [DirectedComplete N] (hB : IsBooleanEM N)
    (A : Set (idempotents N)) : ∃ s, IsLUB A s := by
  classical
  let D : Set N := {x | ∃ F : Finset (idempotents N), (↑F : Set (idempotents N)) ⊆ A ∧
    x = (F.sup id).1}
  have hD : IsDirectedSet D := by
    refine ⟨⟨_, ∅, by simp, rfl⟩, ?_⟩
    rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
    refine ⟨_, ⟨F ∪ G, by rw [Finset.coe_union]; exact Set.union_subset hF hG, rfl⟩, ?_, ?_⟩
    · exact idem_le_iff.1 (Finset.sup_mono Finset.subset_union_left)
    · exact idem_le_iff.1 (Finset.sup_mono Finset.subset_union_right)
  obtain ⟨s, hs⟩ := DirectedComplete.exists_isLUB D hD
  refine ⟨⟨s, isBooleanEM_iff.1 hB s⟩, fun a ha => ?_, fun u hu => ?_⟩
  · exact idem_le_iff.2 (hs.1 ⟨{a}, by simpa using ha, by simp⟩)
  · exact idem_le_iff.2 (hs.2 (by
      rintro _ ⟨F, hF, rfl⟩
      exact idem_le_iff.1 (Finset.sup_le fun b hb => hu (hF hb))))

variable {M : Type u} [EffectMonoid M]

/-- **OAP 57** (`thm:directedcompleteisconvex`, first.tex:2148, Theorem): a
directed-complete effect monoid is `M ≅ M₁ ⊕ M₂` with `M₁` a convex
directed-complete effect monoid and `M₂` a complete Boolean algebra (in the
form of OAP 47: `M₂` Boolean, `M₂ ≅ P(M₂)`, and every subset of `P(M₂)` has a
supremum).  As printed: with `a` from OAP 56, `M₂ = pM` for
`p = (a ⋁ a)^⊥` is Boolean, `M₁ = p^⊥M` is halvable (by `a`) hence convex
(OAP 50), and `M ≅ p^⊥M ⊕ pM` (OAP 21). -/
theorem oap57 [DirectedComplete M] :
    ∃ (M₁ M₂ : Type u) (_ : EffectMonoid M₁) (_ : EffectMonoid M₂),
      DirectedComplete M₁ ∧ IsConvex M₁ ∧ DirectedComplete M₂ ∧
      (∃ hB : IsBooleanEM M₂,
        @EMIsIso M₂ (idempotents M₂) _ (booleanEffectMonoid _) (booleanIso hB) ∧
        ∀ A : Set (idempotents M₂), ∃ s, IsLUB A s) ∧
      ∃ f : EffectMonoidHom M (M₁ × M₂), EMIsIso f := by
  obtain ⟨a, ⟨haa, -⟩, hp, hB⟩ := oap56 (M := M)
  have hq := idem_orth hp
  obtain ⟨f, -, hf⟩ := oap21 hp
  let _i1 := cornerEffectMonoid (a ⋎ a) hp
  let _i2 := cornerEffectMonoid (orth (a ⋎ a)) hq
  have hd1 : DirectedComplete (leftCorner (a ⋎ a)) := corner_directedComplete hp
  have hd2 : DirectedComplete (leftCorner (orth (a ⋎ a))) := corner_directedComplete hq
  have hBool : IsBooleanEM (leftCorner (orth (a ⋎ a))) := corner_isBooleanEM hq hB
  refine ⟨leftCorner (a ⋎ a), leftCorner (orth (a ⋎ a)), _i1, _i2, hd1, ?_, hd2,
    ⟨hBool, (oap47 hBool).1, boolean_dc_isLUB hBool⟩, f, hf⟩
  exact oap50 (corner_halvable hp ⟨a, haa, rfl⟩)

end OAP57

end Papers.OAP
