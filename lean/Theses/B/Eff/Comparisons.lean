/-
Theses/B/Eff/Comparisons.lean

Statements of eff.tex (thesis B, "Diamond, andthen, dagger"), lines
7119–8137 (end of chapter): comparisons of †-effectuses with structures
from the literature — dagger kernel categories (parsec 224), sequential
effect algebras (225), and Grandis' homological categories with the Snake
Lemma (226–228).

Design:
* †-mono/†-epi/†-partial isometries/†-kernels are defined for a general
  `DaggerCat`; the results about `Pure C` for a †-effectus `C` are stated
  with the †'-form (`DaggerPrimeEffectus`, equivalent by 215III) or with
  an explicit `DaggerEffectus` structure where the dagger itself occurs.
* The homological notions (kernel order, exact maps, exactness of a
  composable pair) are defined directly in the effectus with its
  PCM-enrichment zero maps; Grandis' `Nsb A` and the transfer maps
  `f_*, f^*` are *not* formalized separately — following 227III, sharp
  predicates and `f_⋄, f^□` are used in their stead, exactly as the
  thesis itself does in the Snake Lemma 228II.
* Not separately formalized: the introductory comparisons 224I/225I–III
  (Gudder–Latrémolière axioms), the summarizing remarks 224VIII/224VIIIa
  (Tull's phased biproducts) and 228IX, and the `Nsb`-side of
  227II–227IV.
-/
import Theses.B.Eff.Dagger

set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits

namespace Theses.B.Eff

universe u v

/-! ## Dagger kernel categories (parsec 224) -/

section DaggerKernel

variable {D : Type u} [Category.{v} D] [DaggerCat D]

/-- **224II** (eff.tex:7138, Definition): in a †-category, `f` is
**†-mono** when `f† ∘ f = id`. -/
def DaggerCat.DagMono {X Y : D} (f : X ⟶ Y) : Prop :=
  f ≫ DaggerCat.dag f = 𝟙 X

/-- **224II** (eff.tex:7138, Definition): dually, `f` is **†-epi** when
`f ∘ f† = id`. -/
def DaggerCat.DagEpi {X Y : D} (f : X ⟶ Y) : Prop :=
  DaggerCat.dag f ≫ f = 𝟙 Y

/-- **224II** (eff.tex:7147, Definition): `f` is a **†-partial isometry**
when `f = m ∘ e` for a †-mono `m` and †-epi `e`. -/
def DaggerCat.DagPartialIsometry {X Y : D} (f : X ⟶ Y) : Prop :=
  ∃ (Z : D) (e : X ⟶ Z) (m : Z ⟶ Y),
    DaggerCat.DagEpi e ∧ DaggerCat.DagMono m ∧ f = e ≫ m

/-- **224II** (eff.tex:7153, Definition): a **†-kernel** of `f` is an
equalizer of `f` with `0` which is †-mono; a **†-kernel category** is a
†-category with a zero object in which every arrow has a †-kernel. -/
class DaggerKernelCategory (D : Type u) [Category.{v} D] [DaggerCat D]
    [HasZeroObject D] [HasZeroMorphisms D] : Prop where
  dagKernel : ∀ {X Y : D} (f : X ⟶ Y),
    ∃ (W : D) (k : W ⟶ X), DaggerCat.DagMono k ∧ k ≫ f = 0 ∧
      ∀ ⦃Z : D⦄ (g : Z ⟶ X), g ≫ f = 0 → ∃! g' : Z ⟶ W, g' ≫ k = g

end DaggerKernel

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]

section PureDaggerKernel

variable [AndThenEffectus C]

/-- The zero maps of an effectus are pure (used to speak of zero morphisms
in `Pure C`; implicit in 224III). -/
theorem isPure_zero {X Y : C} : IsPure (0 : X ⟶ Y) :=
  ⟨⊥_ C, 0, 0, 1, 0, quotient_basics_4 _, compr_basics_4 _,
    (FinPAC.zero_comp _).symm⟩

/-- **224III.1** (eff.tex:7162, Proposition): in `Pure C` for a †-effectus
`C`, a map is †-mono iff it is a comprehension. -/
theorem pure_dagMono_iff_compr (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    (DaggerCat.DagMono f ↔ ∃ p : Pred Q.base, IsComprehension p f.1) := sorry

/-- **224III.1** (eff.tex:7162, Proposition), dually: a map of `Pure C` is
†-epi iff it is a quotient for a sharp predicate. -/
theorem pure_dagEpi_iff_quot (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    (DaggerCat.DagEpi f ↔
      ∃ s : Pred P.base, IsSharp s ∧ IsQuotient s f.1) := sorry

/-- **224III.2** (eff.tex:7162, Proposition): the †-partial isometries of
`Pure C` are exactly the pristine maps. -/
theorem pure_dagPartialIsometry_iff_pristine (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    (DaggerCat.DagPartialIsometry f ↔ Pristine f.1) := sorry

/-- **224III** (eff.tex:7173, Proposition): `Pure C` is a †-kernel
category: the †-kernel of `f` is given by the comprehension
`π_{(1∘f)ᵖ}`. -/
theorem pure_daggerKernelCategory (d : DaggerEffectus C)
    {P Q : PureCat C} (f : P ⟶ Q) :
    letI := d.daggerCat
    ∃ (W : PureCat C) (k : W ⟶ P),
      DaggerCat.DagMono k ∧
      IsComprehension (orth (f.1 ≫ truth Q.base)) k.1 ∧
      k.1 ≫ f.1 = 0 ∧
      ∀ ⦃Z : PureCat C⦄ (g : Z ⟶ P), g.1 ≫ f.1 = 0 →
        ∃! g' : Z ⟶ W, g' ≫ k = g := sorry

end PureDaggerKernel

/-- **224VI** (`exc-purec-no-biproduct`, eff.tex:7206, Exercise\*):
`Pure (vNᵒᵖ)` does not have finite (bi)products — in particular it has no
binary coproducts. -/
theorem exc_purec_no_biproduct (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ¬ HasBinaryCoproducts (PureCat WStarCPSU.{u}ᵒᵖ) := sorry

/-- **224VII** (`exc-purec-equal`, eff.tex:7235, Exercise\*):
`Pure (vNᵒᵖ)` does not have all coequalizers. -/
theorem exc_purec_equal (s : EffectusPartialStructure WStarCPSU.{u}ᵒᵖ) :
    letI := s.hasFiniteCoproducts
    letI := s.homPCM
    letI := s.finPAC
    letI := s.effectus
    ∀ hA : AndThenEffectus WStarCPSU.{u}ᵒᵖ,
      letI := hA
      ¬ HasCoequalizers (PureCat WStarCPSU.{u}ᵒᵖ) := sorry

/-! ## Sequential effect algebras (parsec 225) -/

/-- **225IV** (eff.tex:7369, Definition): a **sequential effect algebra**
(SEA) is an effect algebra with a binary operation `&` satisfying

* (S1) `c & (–)` is additive;
* (S2) `1 & a = a`;
* (S3) `a & b = 0` implies `b & a = 0`;
* (S4) if `a & b = b & a` then `a & bᵖ = bᵖ & a` and
  `(a & b) & c = a & (b & c)`;
* (S5) if `c` commutes (w.r.t. `&`) with `a` and with `b`, and `a ⊥ b`,
  then `c` commutes with `a & b` and with `a ⋁ b`. -/
class SequentialEffectAlgebra (E : Type u) [EffectAlgebra E] where
  seq : E → E → E
  seq_add : ∀ (c : E) {a b : E} (h : Perp a b),
    ∃ h' : Perp (seq c a) (seq c b),
      ovee (seq c a) (seq c b) h' = seq c (ovee a b h)
  one_seq : ∀ a : E, seq 1 a = a
  seq_zero_comm : ∀ a b : E, seq a b = 0 → seq b a = 0
  seq_comm_orth : ∀ {a b : E}, seq a b = seq b a → seq a (orth b) = seq (orth b) a
  seq_comm_assoc : ∀ {a b : E}, seq a b = seq b a →
    ∀ c : E, seq (seq a b) c = seq a (seq b c)
  seq_comm_compat : ∀ {a b c : E} (h : Perp a b),
    seq c a = seq a c → seq c b = seq b c →
      seq c (seq a b) = seq (seq a b) c ∧
      seq c (ovee a b h) = seq (ovee a b h) c

/-- **225V** (eff.tex:7398, Examples): the effect algebra `[0,1]_𝒜` of a
von Neumann algebra is a sequential effect algebra with
`a & b = √a b √a`. -/
theorem effects_sea (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Theses.VonNeumannAlgebra A] :
    Nonempty (SequentialEffectAlgebra (Theses.effects A)) := sorry

/-- **225V** (eff.tex:7398, Examples): any commutative effect monoid is a
sequential effect algebra with `a & b = a ⊙ b`. -/
theorem commutative_effectMonoid_sea (M : Type u) [EffectMonoid M]
    (hc : EffectMonoid.Commutative M) :
    Nonempty (SequentialEffectAlgebra M) :=
  ⟨{ seq := fun a b => a * b
     seq_add := fun c _ _ h =>
       let ⟨h', e⟩ := emon_mul_ovee c h
       ⟨h', e.symm⟩
     one_seq := EffectMonoid.one_mul
     seq_zero_comm := fun a b hab => (hc b a).trans hab
     seq_comm_orth := fun {a b} _ => hc a (orth b)
     seq_comm_assoc := fun {a b} _ c => EffectMonoid.mul_assoc a b c
     seq_comm_compat := fun {a b c} h _ _ => ⟨hc c (a * b), hc c (ovee a b h)⟩ }⟩

/-- **225VI** (eff.tex:7405, Proposition): in a †-effectus, the predicates
`Pred X` with `p & q = q ∘ asrt_p` satisfy axioms (S1), (S2) and (S3) of a
sequential effect algebra.  (Whether they form a SEA is open, 225VIII.) -/
theorem pred_sea_s1_s2_s3 [AndThenEffectus C] [DaggerPrimeEffectus C]
    (X : C) :
    (∀ (c : Pred X) {p q : Pred X} (h : Perp p q),
      ∃ h' : Perp (andThen c p) (andThen c q),
        ovee (andThen c p) (andThen c q) h' = andThen c (ovee p q h)) ∧
    (∀ p : Pred X, andThen 1 p = p) ∧
    (∀ p q : Pred X, andThen p q = 0 → andThen q p = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (S1): `c & (–)` is additive, because precomposition with `asrt c`
    -- preserves partial sums (`FinPAC.ovee_comp`).
    intro c p q h
    obtain ⟨h', e⟩ := FinPAC.ovee_comp h (asrt c)
    exact ⟨h', e.symm⟩
  · -- (S2): `asrt_1 = id`, by the absorption rule 211XV for the sharp
    -- predicate `1` (`1 ∘ p ≤ 1` always holds).
    intro p
    exact ((asrt_absorp_rule p (isSharp_one (effObj C)) (isSharp_one X)).2).mp
      (pred_le_truth _)
  · -- (S3): the thesis (eff.tex:7415) applies the dagger to
    -- `asrt_q ∘ asrt_p = 0 = asrt_0`.  We avoid `pureDagger` (still `sorry`)
    -- and argue instead with the `asrt_sq` axiom of a †-effectus together
    -- with the uniqueness of square roots; see the errata note.
    intro p q h
    -- `asrt p ≫ asrt q = 0`, since `1 ∘ asrt_q = q`.
    have hpq : asrt p ≫ asrt q = (0 : X ⟶ X) := by
      refine EffectusPartialForm.eq_zero_of_one_zero ?_
      show (asrt p ≫ asrt q) ≫ truth X = 0
      rw [Category.assoc, (asrt_spec q).2]
      exact h
    -- Hence `asrt_{q&p} ∘ asrt_{q&p} = asrt_q ∘ asrt_p ∘ asrt_p ∘ asrt_q = 0`.
    have hsq : asrt (andThen q p) ≫ asrt (andThen q p) = (0 : X ⟶ X) := by
      rw [DaggerPrimeEffectus.asrt_sq q p, hpq, FinPAC.comp_zero,
        FinPAC.comp_zero]
    -- So `(q&p) & (q&p) = 0 = 0 & 0`, and square roots of `0` are unique.
    have hr : andThen (andThen q p) (andThen q p) = (0 : Pred X) := by
      have e : andThen (andThen q p) (andThen q p)
          = (asrt (andThen q p) ≫ asrt (andThen q p)) ≫ truth X := by
        show asrt (andThen q p) ≫ andThen q p = _
        rw [Category.assoc, (asrt_spec (andThen q p)).2]
      rw [e, hsq, FinPAC.zero_comp]
    have hz : andThen (0 : Pred X) 0 = (0 : Pred X) := FinPAC.comp_zero _
    exact (DaggerPrimeEffectus.sqrt_existsUnique (0 : Pred X)).unique hr hz

/-! ## Homological categories (parsecs 226–228) -/

section Homological

variable [AndThenEffectus C]

/-- **226II** (`homology-lemma`, eff.tex:7440, Lemma): for sharp predicates
`s, t` on the same object of a †-effectus with `sᵖ ≤ t`, the predicate
`s & t` is sharp. -/
theorem homology_lemma [DaggerPrimeEffectus C] {X : C} {s t : Pred X}
    (hs : IsSharp s) (ht : IsSharp t) (h : orth s ≼ t) :
    IsSharp (andThen s t) := sorry

/-- **226IV.1** (eff.tex:7483, Definition): the preorder on kernels:
`n ≤ m` when `n` factors through `m` (Grandis; `n ≈ m` when both `n ≤ m`
and `m ≤ n`, and `Nsb A` is the poset of kernels modulo `≈` — the latter
is represented in a ⋄-effectus by `SPred A`, cf. 227III). -/
def KernelLE {W W' X : C} (n : W ⟶ X) (m : W' ⟶ X) : Prop :=
  ∃ f : W ⟶ W', f ≫ m = n

/-- **226IV.2** (eff.tex:7483, Definition): a map `f` is **exact** when the
unique `g` with `f = ker (cok f) ∘ g ∘ cok (ker f)` is an isomorphism.
(An effectus with comprehension, quotients and images is *pointed
semiexact*: it has a zero object and all kernels and cokernels, by 200III
and 205II.) -/
def IsExactMap {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (W Q K Q' : C) (kf : W ⟶ X) (ckf : X ⟶ Q) (cf : Y ⟶ Q') (kcf : K ⟶ Y)
    (g : Q ⟶ K),
    IsKernel f kf ∧ IsCokernel kf ckf ∧ IsCokernel f cf ∧ IsKernel cf kcf ∧
      IsIso g ∧ f = ckf ≫ g ≫ kcf

/-- **226V.1** (eff.tex:7523, Theorem): in a †-effectus (in partial form)
a map is a kernel iff it is a comprehension. -/
theorem homological_kernels [DaggerPrimeEffectus C] {W X : C} (f : W ⟶ X) :
    (∃ (Y : C) (g : X ⟶ Y), IsKernel g f) ↔
      ∃ p : Pred X, IsComprehension p f := sorry

/-- **226V.2** (eff.tex:7523, Theorem): a map is a cokernel iff it is a
quotient for a sharp predicate. -/
theorem homological_cokernels [DaggerPrimeEffectus C] {X Y : C}
    (f : X ⟶ Y) :
    (∃ (Z : C) (g : Z ⟶ X), IsCokernel g f) ↔
      ∃ s : Pred X, IsSharp s ∧ IsQuotient s f := sorry

/-- **226V.3** (eff.tex:7523, Theorem): a map is exact iff it is
pristine. -/
theorem homological_exact [DaggerPrimeEffectus C] {X Y : C} (f : X ⟶ Y) :
    IsExactMap f ↔ Pristine f := sorry

/-- **226V** (eff.tex:7523, Theorem): a †-effectus is a pointed
homological category: kernels and cokernels are closed under composition,
and (**226VII**, homology axiom) for a kernel `m` and cokernel `q` with
`ker q ≤ m`, the composite `q ∘ m` is exact. -/
theorem homological_category [DaggerPrimeEffectus C] :
    (∀ {W X Y Z : C} (m₁ : W ⟶ X) (m₂ : X ⟶ Y),
      (∃ g : X ⟶ Z, IsKernel g m₁) → (∃ (Z' : C) (g : Y ⟶ Z'), IsKernel g m₂) →
        ∃ (Z'' : C) (g : Y ⟶ Z''), IsKernel g (m₁ ≫ m₂)) ∧
    (∀ {X Y Z W' : C} (q₁ : X ⟶ Y) (q₂ : Y ⟶ Z),
      (∃ g : W' ⟶ X, IsCokernel g q₁) →
      (∃ (W'' : C) (g : W'' ⟶ Y), IsCokernel g q₂) →
        ∃ (W''' : C) (g : W''' ⟶ X), IsCokernel g (q₁ ≫ q₂)) ∧
    (∀ {M A Q : C} (m : M ⟶ A) (q : A ⟶ Q)
      (_ : ∃ (Y : C) (g : A ⟶ Y), IsKernel g m)
      (_ : ∃ (Z : C) (g : Z ⟶ A), IsCokernel g q)
      (_ : ∀ (K : C) (kq : K ⟶ A), IsKernel q kq → KernelLE kq m),
        IsExactMap (m ≫ q)) := sorry

/-- **227II.1** (eff.tex:7586, Definition): a composable pair
`A → f → B → g → C` is **exact at** `B` when `ker (cok f) ≈ ker g`.  (In a
†-effectus this amounts to `imᵖ f = ⌈1 ∘ g⌉`, 227III.1.) -/
def ExactAt {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∃ (Q K K' : C) (cf : Y ⟶ Q) (k : K ⟶ Y) (k' : K' ⟶ Y),
    IsCokernel f cf ∧ IsKernel cf k ∧ IsKernel g k' ∧
      KernelLE k k' ∧ KernelLE k' k

/-- **227III.1** (eff.tex:7622, Example): in a †-effectus, `f ∘ g` is
exact at the middle object iff `imᵖ f = ⌈1 ∘ g⌉`. -/
theorem exactAt_iff [DaggerPrimeEffectus C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    ExactAt f g ↔ orth (imPred f) = ceilPred (g ≫ truth Z) := sorry

/-- **227V** (`diamondboxlemma`, eff.tex:7653, Lemma), first half: in a
†-effectus, `π^□ ∘ π_⋄ = id` for any comprehension `π`. -/
theorem diamondboxlemma_compr [DaggerPrimeEffectus C] {W X : C}
    {p : Pred X} {π : W ⟶ X} (hπ : IsComprehension p π) (s : SPred W) :
    boxPull π (diaPush π s) = s := sorry

/-- **227V** (`diamondboxlemma`, eff.tex:7653, Lemma), second half:
`ζ_⋄ ∘ ζ^□ = id` for any sharp quotient `ζ`. -/
theorem diamondboxlemma_quot [DaggerPrimeEffectus C] {X W : C}
    {s₀ : Pred X} (hs : IsSharp s₀) {ζ : X ⟶ W}
    (hζ : IsQuotient s₀ ζ) (t : SPred W) :
    diaPush ζ (boxPull ζ t) = t := sorry

end Homological

section Snake

variable [AndThenEffectus C] [DaggerPrimeEffectus C]

/-- **228II** (eff.tex:7687, Snake Lemma; Grandis): suppose the diagram

```
        A --f--> B --g--> C --> 0
        |a       |b       |c
        v        v        v
  0 --> A'--h--> B'--k--> C'
```

commutes in a †-effectus with exact rows and the modularity conditions
(1)–(8) below (stated, following 227III, in terms of `(–)_⋄` and `(–)^□`
on sharp predicates):

1. `b^□(b_⋄(im f)) = ⌈1∘b⌉ᵖ ∨ im f`;
2. `b_⋄(b^□(im h)) = im h ∧ im b`;
3. `k^□(k_⋄(im b)) = im h ∨ im b`;
4. `f_⋄(f^□(b^□(0))) = ⌈1∘b⌉ᵖ ∧ im f`;
5. `imᵖ f = ⌈1∘g⌉` (exactness at `B`);
6. `imᵖ h = ⌈1∘k⌉` (exactness at `B'`);
7. `g` is a quotient for a sharp predicate; and
8. `h` is a comprehension.

Then, writing `a_π = π_{(1∘a)ᵖ}`, `a_ζ = ξ_{im a}` (and likewise for `b`,
`c`) for the chosen kernels and cokernels and

* `f̄ = b_π† ∘ f ∘ a_π`, `ḡ = c_π† ∘ g ∘ b_π`,
* `h̄ = b_ζ ∘ h ∘ a_ζ†`, `k̄ = c_ζ ∘ k ∘ b_ζ†`,

there is a connecting map `d : ker c ⟶ cok a` making

`ker a → ker b → ker c → cok a → cok b → cok c`

a long exact sequence. -/
theorem snake_lemma {A B C₃ A' B' C₃' : C}
    (f : A ⟶ B) (g : B ⟶ C₃) (a : A ⟶ A') (b : B ⟶ B') (c : C₃ ⟶ C₃')
    (h : A' ⟶ B') (k : B' ⟶ C₃')
    (w₁ : f ≫ b = a ≫ h) (w₂ : g ≫ c = b ≫ k)
    -- exact rows (conditions 5 and 6):
    (row₁ : ExactAt f g) (row₂ : ExactAt h k)
    -- conditions 7 and 8:
    (hg : ∃ s : Pred B, IsSharp s ∧ IsQuotient s g)
    (hh : ∃ p : Pred B', IsComprehension p h)
    -- modularity conditions (1)–(4):
    (m₁ : SPred.IsSup
      (SPred.orth ⟨ceilPred (b ≫ truth B'), isSharp_ceil _⟩)
      ⟨imPred f, isSharp_imPred C f⟩
      (boxPull b (diaPush b ⟨imPred f, isSharp_imPred C f⟩)))
    (m₂ : SPred.IsInf ⟨imPred h, isSharp_imPred C h⟩
      ⟨imPred b, isSharp_imPred C b⟩
      (diaPush b (boxPull b ⟨imPred h, isSharp_imPred C h⟩)))
    (m₃ : SPred.IsSup ⟨imPred h, isSharp_imPred C h⟩
      ⟨imPred b, isSharp_imPred C b⟩
      (boxPull k (diaPush k ⟨imPred b, isSharp_imPred C b⟩)))
    (m₄ : SPred.IsInf
      (SPred.orth ⟨ceilPred (b ≫ truth B'), isSharp_ceil _⟩)
      ⟨imPred f, isSharp_imPred C f⟩
      (diaPush f (boxPull f (boxPull b ⟨0, dia_isSharp_zero _⟩)))) :
    ∃ d : comprObj (orth (c ≫ truth C₃')) ⟶ quotObj (imPred a),
      -- the connecting sequence, with the induced maps on (co)kernels:
      letI fbar := comprMap (orth (a ≫ truth A')) ≫ f ≫
        pureDagger (comprMap (orth (b ≫ truth B')))
          (isPure_comprehension C (isComprehension_comprMap _))
      letI gbar := comprMap (orth (b ≫ truth B')) ≫ g ≫
        pureDagger (comprMap (orth (c ≫ truth C₃')))
          (isPure_comprehension C (isComprehension_comprMap _))
      letI hbar := pureDagger (quotMap (imPred a))
          (isPure_quotient C (isQuotient_quotMap _)) ≫ h ≫
        quotMap (imPred b)
      letI kbar := pureDagger (quotMap (imPred b))
          (isPure_quotient C (isQuotient_quotMap _)) ≫ k ≫
        quotMap (imPred c)
      ExactAt fbar gbar ∧ ExactAt gbar d ∧ ExactAt d hbar ∧
        ExactAt hbar kbar := sorry

end Snake

end Theses.B.Eff
