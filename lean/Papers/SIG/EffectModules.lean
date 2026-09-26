/-
Papers/SIG/EffectModules.lean

SIG §3.1 "Effect monoids and modules", the effect-module half
(main.tex:769–867), with its proofs in Appendix A (main.tex:2093–2326):
points SIG 24–29, 66, 67, and the σ-effectus lemmas they need (the
countable form of effectus axiom (iii), SIG 69 `lem:decomposition-bijection`).

Design:
* An effect `M`-module is the tree's `EffectModule M E` (179II), whose
  axioms are biadditivity of the action (`effectModule_biadditive`).  A
  σ-effect module is `IsSigmaEffectModule M E`: `E` ω-complete and the action
  σ-biadditive for the canonical sums (SIG 17).
* `sEMod[M]` is `SEMod M`: bundled σ-effect modules and σ-additive,
  action-preserving (subunital) maps.  Its countable products are explicit
  Π-types; its opposite is a σ-effectus (SIG 28/66) whose hom-sets carry the
  pointwise sums, built by the generic `pointwiseSigmaPAM`.
-/
import Papers.SIG.Classification

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff Opposite

namespace Papers.SIG

open SigmaPAM

universe u v w

/-! ## σ-PAM helpers -/

section SigmaHelpers

variable {M : Type u} [SigmaPAM M]

/-- The fibre of `Prod.fst` over `j` is `I`. -/
def fibreFst (J I : Type) (j : J) : I ≃ {q : J × I // q.1 = j} where
  toFun i := ⟨(j, i), rfl⟩
  invFun q := q.1.2
  left_inv i := rfl
  right_inv := by rintro ⟨⟨j', i⟩, rfl⟩; rfl

/-- Double sums, grouped by rows. -/
theorem sumsTo_prod_iff {J I : Type} [Countable J] [Countable I] (x : J × I → M) (s : M) :
    SumsTo x s ↔ ∃ t : J → M, (∀ j, SumsTo (fun i => x (j, i)) (t j)) ∧ SumsTo t s := by
  rw [sumsTo_partition_iff x Prod.fst]
  refine exists_congr fun t => and_congr_left fun _ => forall_congr' fun j => ?_
  exact (sumsTo_comp_equiv' (fibreFst J I j) _ _ (fun _ => rfl) _).symm

/-- Double sums, grouped by columns. -/
theorem sumsTo_prod_iff' {J I : Type} [Countable J] [Countable I] (x : J × I → M) (s : M) :
    SumsTo x s ↔ ∃ t : I → M, (∀ i, SumsTo (fun j => x (j, i)) (t i)) ∧ SumsTo t s := by
  rw [← sumsTo_comp_equiv' (Equiv.prodComm I J) x (fun q => x (q.2, q.1)) (fun _ => rfl) s]
  exact sumsTo_prod_iff _ s

/-- Families of zeros sum to zero (partition the empty family into empty
blocks indexed by `J`). -/
theorem sumsTo_zero_family (J : Type) [Countable J] : SumsTo (fun _ : J => (zero : M)) zero := by
  obtain ⟨t, ht, hts⟩ := (sumsTo_partition_iff (Empty.elim : Empty → M) (Empty.elim : Empty → J)
    zero).1 (sumsTo_of_isEmpty _)
  have : t = fun _ => zero := funext fun k => by
    have : IsEmpty {j : Empty // (Empty.elim j : J) = k} := ⟨fun j => j.1.elim⟩
    exact (ht k).unique (sumsTo_of_isEmpty _)
  rwa [this] at hts

end SigmaHelpers

/-! ## A σ-PAM of maps with pointwise sums -/

section Pointwise

variable {H : Type w} {D : Type v} {E : D → Type u} [∀ a, SigmaPAM (E a)] (ev : H → ∀ a, E a)

/-- `PSumsTo ev f g`: the maps `f j` sum pointwise to `g`. -/
def PSumsTo {J : Type} [Countable J] (f : J → H) (g : H) : Prop :=
  ∀ a, SumsTo (fun j => ev (f j) a) (ev g a)

/-- The data making pointwise sums a σ-PAM: evaluation is injective,
pointwise sums of subfamilies of summable families are again maps, and so are
pointwise sums of families whose finite subfamilies have them. -/
structure PointwiseData : Prop where
  inj : Function.Injective ev
  nonempty : Nonempty H
  sub : ∀ {J : Type} [Countable J] (f : J → H) (P : J → Prop), (∃ g, PSumsTo ev f g) →
    ∃ g, PSumsTo ev (fun j : {j // P j} => f j.1) g
  lim : ∀ {J : Type} [Countable J] (f : J → H),
    (∀ F : Finset J, ∃ g, PSumsTo ev (fun j : F => f j.1) g) → ∃ g, PSumsTo ev f g

variable {ev}

/-- The σ-PAM of pointwise sums. -/
noncomputable def pointwiseSigmaPAM (hd : PointwiseData ev) : SigmaPAM H where
  Summable f := ∃ g, PSumsTo ev f g
  sum f h := h.choose
  nonempty := hd.nonempty
  summable_iff_partition f p := by
    constructor
    · rintro ⟨g, hg⟩
      have hfib : ∀ k, ∃ g', PSumsTo ev (fun j : {j // p j = k} => f j.1) g' :=
        fun k => hd.sub f _ ⟨g, hg⟩
      refine ⟨hfib, g, fun a => ?_⟩
      obtain ⟨t, ht, hts⟩ := (sumsTo_partition_iff (fun j => ev (f j) a) p _).1 (hg a)
      have : (fun k => ev (hfib k).choose a) = t :=
        funext fun k => ((hfib k).choose_spec a).unique (ht k)
      show SumsTo (fun k => ev (hfib k).choose a) (ev g a)
      rw [this]; exact hts
    · rintro ⟨h, g, hg⟩
      exact ⟨g, fun a => (sumsTo_partition_iff _ p _).2
        ⟨fun k => ev (h k).choose a, fun k => (h k).choose_spec a, hg a⟩⟩
  sum_partition f p hx h h' := by
    apply hd.inj; funext a
    exact (hx.choose_spec a).unique ((sumsTo_partition_iff _ p _).2
      ⟨_, fun k => (h k).choose_spec a, h'.choose_spec a⟩)
  summable_unique f := ⟨f default, fun a => sumsTo_of_unique (fun j => ev (f j) a)⟩
  sum_unique f h := hd.inj (funext fun a =>
    (h.choose_spec a).unique (sumsTo_of_unique (fun j => ev (f j) a)))
  limit f h := hd.lim f h

theorem pointwise_sumsTo_iff (hd : PointwiseData ev) {J : Type} [Countable J] (f : J → H)
    (g : H) : @SumsTo H (pointwiseSigmaPAM hd) J _ f g ↔ PSumsTo ev f g := by
  constructor
  · rintro ⟨h, rfl⟩; exact h.choose_spec
  · intro h; exact ⟨⟨g, h⟩, hd.inj (funext fun a => (⟨g, h⟩ : ∃ g, PSumsTo ev f g).choose_spec a
      |>.unique (h a))⟩

end Pointwise

/-! ## SIG 24–27: effect modules -/

section ModuleBasics

variable {M : Type u} [EffectMonoid M] {E : Type v} [EffectAlgebra E] [EffectModule M E]

theorem ea_eq_zero_of_ovee_self {X : Type w} [EffectAlgebra X] {x : X} (h : Perp x x)
    (e : ovee x x h = x) : x = 0 :=
  eabasics_cancellation h (PCM.zero_perp x) (e.trans (PCM.zero_ovee x).symm)

theorem emod_smul_zero (r : M) : r • (0 : E) = 0 := by
  obtain ⟨h, e⟩ := EffectModule.smul_perp r (PCM.zero_perp (0 : E))
  refine ea_eq_zero_of_ovee_self h (e.trans ?_)
  rw [PCM.zero_ovee]

theorem emod_zero_smul (a : E) : (0 : M) • a = 0 := by
  obtain ⟨h, e⟩ := EffectModule.perp_smul (PCM.zero_perp (0 : M)) a
  refine ea_eq_zero_of_ovee_self h (e.trans ?_)
  rw [PCM.zero_ovee]

/-- **SIG 24** (main.tex:771, Definition): an effect `M`-module is an effect
algebra with a biadditive `M`-action (`1 · x = x`, `(rs) · x = r · (s · x)`):
the tree's `EffectModule` (179II), whose axioms are exactly biadditivity
(`0 · a = 0 = r · 0` included, `emod_smul_zero`, `emod_zero_smul`). -/
theorem effectModule_biadditive : IsBiadditive (fun (r : M) (a : E) => r • a) := by
  refine ⟨fun r => ⟨emod_smul_zero r, fun h => ?_⟩, fun a => ⟨emod_zero_smul a, fun h => ?_⟩⟩
  · obtain ⟨h', e⟩ := EffectModule.smul_perp r h; exact ⟨h', e⟩
  · obtain ⟨h', e⟩ := EffectModule.perp_smul h a; exact ⟨h', e⟩

variable (M E)

/-- **SIG 24** (main.tex:771, Definition): a **σ-effect `M`-module** (over a
σ-effect monoid `M`) is a σ-effect algebra `E` with a σ-biadditive action. -/
def IsSigmaEffectModule : Prop :=
  OmegaComplete E ∧ (∀ r : M, IsSigmaAdditiveC (fun a : E => r • a)) ∧
    ∀ a : E, IsSigmaAdditiveC (fun r : M => r • a)

end ModuleBasics

/-- Every effect monoid is an effect module over itself. -/
def selfEffectModule (M : Type u) [EffectMonoid M] : EffectModule M M where
  smul r s := r * s
  mul_smul l m a := EffectMonoid.mul_assoc l m a
  smul_perp := by
    intro l a b h
    obtain ⟨h', e⟩ := emon_mul_ovee l h; exact ⟨h', e.symm⟩
  perp_smul := by
    intro l m h a
    obtain ⟨h', e⟩ := emon_ovee_mul a h; exact ⟨h', e.symm⟩
  one_smul a := EffectMonoid.one_mul a

theorem self_isSigmaEffectModule (M : Type u) [EffectMonoid M] (hM : IsSigmaEffectMonoid M) :
    @IsSigmaEffectModule M _ M _ (selfEffectModule M) :=
  ⟨hM.1, hM.2.1, hM.2.2⟩

/-- **SIG 25** (main.tex:797, Example): in a σ-effectus the predicates
`Pred A` form a σ-effect module over the scalars, with `r · p = r ∘ p` (the
effect module structure is the tree's `predEffectModule`, 190II.4). -/
theorem pred_isSigmaEffectModule {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C] (A : C) :
    IsSigmaEffectModule (Scal C) (Pred A) := by
  have hc := fun {B : C} => (pred_sigmaEffectAlgebra B).2
  refine ⟨(pred_sigmaEffectAlgebra A).1, fun r J _ x s hs => ?_, fun a J _ x s hs => ?_⟩
  · exact (hc J _ _).1 (comp_sumsTo_left r ((hc J x s).2 hs))
  · exact (hc J _ _).1 (comp_sumsTo_right a ((hc J x s).2 hs))

/-- **SIG 26** (main.tex:805, Example): an effect `{0,1}`-module is just an
effect algebra: every effect algebra is one (the tree's `effectModuleBool`),
and the action is forced, `1 · a = a`, `0 · a = 0`. -/
theorem effectModule_bool_unique {E : Type v} [EffectAlgebra E] (m : EffectModule Bool E)
    (a : E) : m.smul true a = a ∧ m.smul false a = 0 :=
  ⟨m.one_smul a, @emod_zero_smul Bool _ E _ m a⟩

/-! **SIG 27** (main.tex:811, Example): effect `[0,1]`-modules are the convex
effect algebras, i.e. the intervals `[0,u]_V` of ordered vector spaces: the
tree's `orderIntervalEffectModule` and `effectModule_unitInterval_representation`
(179III.2, Gudder–Pulmannová). -/

/-! ## Products of effect algebras and modules -/

section Pi

variable {J : Type w} {D : J → Type v} [∀ j, EffectAlgebra (D j)]

/-- The product `∏ D_j` of effect algebras, componentwise. -/
instance piEffectAlgebra : EffectAlgebra (∀ j, D j) where
  zero := fun _ => 0
  one := fun _ => 1
  Perp a b := ∀ j, Perp (a j) (b j)
  ovee a b h := fun j => ovee (a j) (b j) (h j)
  orth a := fun j => orth (a j)
  perp_comm h := fun j => PCM.perp_comm (h j)
  ovee_comm h := funext fun j => PCM.ovee_comm (h j)
  perp_of_ovee_perp hab h := fun j => PCM.perp_of_ovee_perp (hab j) (h j)
  perp_ovee_of_ovee_perp hab h := fun j => PCM.perp_ovee_of_ovee_perp (hab j) (h j)
  ovee_assoc hab h := funext fun j => PCM.ovee_assoc (hab j) (h j)
  zero_perp a := fun j => PCM.zero_perp (a j)
  zero_ovee a := funext fun j => PCM.zero_ovee (a j)
  perp_orth a := fun j => EffectAlgebra.perp_orth (a j)
  ovee_orth a := funext fun j => EffectAlgebra.ovee_orth (a j)
  orth_unique h e := funext fun j => EffectAlgebra.orth_unique (h j) (congrFun e j)
  eq_zero_of_perp_one h := funext fun j => EffectAlgebra.eq_zero_of_perp_one (h j)

theorem pi_le_iff (a b : ∀ j, D j) : a ≼ b ↔ ∀ j, a j ≼ b j := by
  constructor
  · rintro ⟨c, h, rfl⟩ j; exact ⟨c j, h j, rfl⟩
  · intro h
    choose c hc he using h
    exact ⟨c, hc, funext he⟩

theorem isSumOf_pi_iff (l : List (∀ j, D j)) (s : ∀ j, D j) :
    PCM.IsSumOf l s ↔ ∀ j, PCM.IsSumOf (l.map (· j)) (s j) := by
  constructor
  · intro h j
    induction h with
    | nil => exact PCM.IsSumOf.nil
    | cons _ hp ih => exact PCM.IsSumOf.cons ih (hp j)
  · induction l generalizing s with
    | nil =>
      intro h
      have : s = 0 := funext fun j => PCM.isSumOf_nil_iff.1 (h j)
      rw [this]; exact PCM.IsSumOf.nil
    | cons a l ih =>
      intro h
      have h' : ∀ j, ∃ t, PCM.IsSumOf (l.map (· j)) t ∧ ∃ hp : Perp (a j) t, ovee (a j) t hp = s j :=
        fun j => by
          obtain ⟨t, ht, hp, e⟩ := PCM.isSumOf_cons_iff.1 (h j)
          exact ⟨t, ht, hp, e⟩
      choose t ht hp he using h'
      have := PCM.IsSumOf.cons (ih t ht) (show Perp a t from hp)
      convert this using 1
      exact (funext he).symm

theorem finSum_pi_iff {I : Type} (x : I → ∀ j, D j) (F : Finset I) (s : ∀ j, D j) :
    FinSum x F s ↔ ∀ j, FinSum (fun i => x i j) F (s j) := by
  unfold FinSum
  rw [isSumOf_pi_iff]
  refine forall_congr' fun j => ?_
  rw [List.map_map]; rfl

theorem isCSum_pi_iff {I : Type} (x : I → ∀ j, D j) (s : ∀ j, D j) :
    IsCSum x s ↔ ∀ j, IsCSum (fun i => x i j) (s j) := by
  classical
  constructor
  · intro hs j
    refine ⟨fun F => ?_, ?_, fun c hc => ?_⟩
    · obtain ⟨T, hT⟩ := hs.1 F; exact ⟨T j, (finSum_pi_iff x F T).1 hT j⟩
    · rintro t ⟨F, hF⟩
      obtain ⟨T, hT⟩ := hs.1 F
      rw [finSum_unique hF ((finSum_pi_iff x F T).1 hT j)]
      exact (pi_le_iff _ _).1 (hs.finSum_le hT) j
    · let c' : ∀ k, D k := fun k => if h : k = j then h ▸ c else s k
      have hle : s ≼ c' := hs.2.2 c' (by
        rintro T ⟨F, hF⟩
        refine (pi_le_iff _ _).2 fun k => ?_
        by_cases hk : k = j
        · subst hk
          simp only [c']
          exact hc _ ⟨F, (finSum_pi_iff x F T).1 hF k⟩
        · simp only [c', hk]
          exact (pi_le_iff _ _).1 (hs.finSum_le hF) k)
      have := (pi_le_iff _ _).1 hle j
      simpa [c'] using this
  · intro h
    have hfin : ∀ F : Finset I, ∃ T, FinSum x F T := by
      intro F
      choose T hT using fun j => (h j).1 F
      exact ⟨T, (finSum_pi_iff x F T).2 hT⟩
    refine ⟨hfin, ?_, fun c hc => (pi_le_iff _ _).2 fun j => (h j).2.2 (c j) ?_⟩
    · rintro T ⟨F, hF⟩
      exact (pi_le_iff _ _).2 fun j => (h j).finSum_le ((finSum_pi_iff x F T).1 hF j)
    · rintro t ⟨F, hF⟩
      obtain ⟨T, hT⟩ := hfin F
      rw [finSum_unique hF ((finSum_pi_iff x F T).1 hT j)]
      exact (pi_le_iff _ _).1 (hc T ⟨F, hT⟩) j

theorem pi_omegaComplete (h : ∀ j, OmegaComplete (D j)) : OmegaComplete (∀ j, D j) := by
  intro a ha
  have ha' : ∀ j n, a n j ≼ a (n + 1) j := fun j n => (pi_le_iff _ _).1 (ha n) j
  choose s hs using fun j => h j (fun n => a n j) (ha' j)
  refine ⟨s, ?_, fun c hc => (pi_le_iff _ _).2 fun j => (hs j).2 (c j) ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (pi_le_iff _ _).2 fun j => (hs j).1 _ ⟨n, rfl⟩
  · rintro _ ⟨n, rfl⟩
    exact (pi_le_iff _ _).1 (hc _ ⟨n, rfl⟩) j

variable {M : Type u} [EffectMonoid M] [∀ j, EffectModule M (D j)]

/-- The product of effect modules, componentwise. -/
instance piEffectModule : EffectModule M (∀ j, D j) where
  smul r a := fun j => r • a j
  mul_smul l m a := funext fun j => EffectModule.mul_smul l m (a j)
  smul_perp := by
    intro l a b h
    choose h' e using fun j => EffectModule.smul_perp l (h j)
    exact ⟨h', funext e⟩
  perp_smul := by
    intro l m h a
    choose h' e using fun j => EffectModule.perp_smul h (a j)
    exact ⟨h', funext e⟩
  one_smul a := funext fun j => EffectModule.one_smul (a j)

theorem pi_isSigmaEffectModule (h : ∀ j, IsSigmaEffectModule M (D j)) :
    IsSigmaEffectModule M (∀ j, D j) := by
  refine ⟨pi_omegaComplete fun j => (h j).1, fun r I _ x s hs => ?_, fun a I _ x s hs => ?_⟩
  · refine (isCSum_pi_iff _ _).2 fun j => ?_
    show IsCSum (fun i => r • x i j) (r • s j)
    exact (h j).2.1 r I (fun i => x i j) (s j) ((isCSum_pi_iff x s).1 hs j)
  · refine (isCSum_pi_iff _ _).2 fun j => ?_
    show IsCSum (fun i => x i • a j) (s • a j)
    exact (h j).2.2 (a j) I x s hs

theorem pi_smul_apply (r : M) (a : ∀ j, D j) (j : J) : (r • a) j = r • a j := rfl

end Pi

/-! ## The category `sEMod[M]` -/

/-- **SIG 24** (main.tex:787, Definition): an object of `sEMod[M]`: a
σ-effect `M`-module. -/
structure SEMod (M : Type u) [EffectMonoid M] : Type (u + 1) where
  carrier : Type u
  [ea : EffectAlgebra carrier]
  [mod : EffectModule M carrier]
  sigma : IsSigmaEffectModule M carrier

attribute [instance] SEMod.ea SEMod.mod

namespace SEMod

variable {M : Type u} [EffectMonoid M]

instance : CoeSort (SEMod M) (Type u) := ⟨SEMod.carrier⟩

/-- The canonical σ-PAM of (the underlying σ-effect algebra of) an object. -/
noncomputable instance sigmaPAM (E : SEMod M) : SigmaPAM E.carrier :=
  canonicalSigmaPAM E.sigma.1

theorem sumsTo_iff (E : SEMod M) {J : Type} [Countable J] (x : J → E.carrier) (s : E.carrier) :
    SumsTo x s ↔ IsCSum x s := canonical_sumsTo_iff E.sigma.1 x s

/-- **SIG 24** (main.tex:787, Definition): a morphism of `sEMod[M]`: a
σ-additive map preserving the action (subunital: not required to preserve
`1`). -/
@[ext]
structure Hom (E F : SEMod M) : Type u where
  toFun : E.carrier → F.carrier
  additive : IsAdditive toFun
  map_smul : ∀ (r : M) (a : E.carrier), toFun (r • a) = r • toFun a
  sigma : IsSigmaAdditiveC toFun

theorem IsAdditive.comp' {X Y Z : Type*} [PCM X] [PCM Y] [PCM Z] {f : X → Y} {g : Y → Z}
    (hf : IsAdditive f) (hg : IsAdditive g) : IsAdditive (g ∘ f) := by
  refine ⟨by simp [Function.comp, hf.1, hg.1], fun h => ?_⟩
  obtain ⟨h₁, e₁⟩ := hf.2 h
  obtain ⟨h₂, e₂⟩ := hg.2 h₁
  exact ⟨h₂, by show ovee (g (f _)) (g (f _)) h₂ = g (f _); rw [e₂, e₁]⟩

instance : Category (SEMod M) where
  Hom := Hom
  id E := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl, fun _ _ _ _ h => h⟩
  comp f g := ⟨g.toFun ∘ f.toFun, IsAdditive.comp' f.additive g.additive,
    fun r a => by simp [f.map_smul, g.map_smul],
    fun J _ x s h => g.sigma J _ _ (f.sigma J x s h)⟩

@[simp] theorem id_toFun (E : SEMod M) : (𝟙 E : Hom E E).toFun = id := rfl
@[simp] theorem comp_toFun {E F G : SEMod M} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {E F : SEMod M} {f g : E ⟶ F} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

theorem Hom.map_zero {E F : SEMod M} (f : E ⟶ F) : f.toFun 0 = 0 := f.additive.1

theorem Hom.mono {E F : SEMod M} (f : E ⟶ F) {a b : E.carrier} (h : a ≼ b) :
    f.toFun a ≼ f.toFun b := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h', e⟩ := f.additive.2 hc
  exact ⟨f.toFun c, h', e⟩

theorem Hom.sumsTo {E F : SEMod M} (f : E ⟶ F) {J : Type} [Countable J] {x : J → E.carrier}
    {s : E.carrier} (h : SumsTo x s) : SumsTo (fun j => f.toFun (x j)) (f.toFun s) :=
  (sumsTo_iff F _ _).2 (f.sigma J x s ((sumsTo_iff E _ _).1 h))

theorem Hom.map_ovee {E F : SEMod M} (f : E ⟶ F) {a b : E.carrier} (h : Perp a b) :
    ∃ h' : Perp (f.toFun a) (f.toFun b), ovee (f.toFun a) (f.toFun b) h' = f.toFun (ovee a b h) :=
  f.additive.2 h

/-- The unit object `M` (for a σ-effect monoid `M`). -/
def unit (M : Type u) [EffectMonoid M] (hM : IsSigmaEffectMonoid M) : SEMod M :=
  @SEMod.mk M _ M _ (selfEffectModule M) (self_isSigmaEffectModule M hM)

/-- The product `∏ D_j` in `sEMod[M]`. -/
def pi {J : Type} (D : J → SEMod M) : SEMod M where
  carrier := ∀ j, (D j).carrier
  sigma := pi_isSigmaEffectModule fun j => (D j).sigma

/-- The projection `∏ D_j → D_j`. -/
def piProj {J : Type} (D : J → SEMod M) (j : J) : pi D ⟶ D j where
  toFun a := a j
  additive := ⟨rfl, fun h => ⟨h j, rfl⟩⟩
  map_smul r a := pi_smul_apply r a j
  sigma _ _ x s hs := (isCSum_pi_iff x s).1 hs j

/-- The tupling `X → ∏ D_j`. -/
def piLift {J : Type} {D : J → SEMod M} {X : SEMod M} (f : ∀ j, X ⟶ D j) : X ⟶ pi D where
  toFun x j := (f j).toFun x
  additive := ⟨funext fun j => (f j).map_zero, fun h => by
    choose h' e using fun j => (f j).map_ovee h
    exact ⟨h', funext e⟩⟩
  map_smul r a := funext fun j => ((f j).map_smul r a).trans
    (pi_smul_apply (D := fun j => (D j).carrier) r (fun j => (f j).toFun a) j).symm
  sigma I _ x s hs := (isCSum_pi_iff _ _).2 fun j => (f j).sigma I x s hs

/-- **SIG 28** (main.tex:816): products in `sEMod[M]` are cartesian
products with pointwise operations. -/
def piFan {J : Type} (D : J → SEMod M) : Fan D := Fan.mk (pi D) (piProj D)

def piFanIsLimit {J : Type} (D : J → SEMod M) : IsLimit (piFan D) :=
  Fan.IsLimit.mk _ (fun s => piLift s.proj) (fun s j => hom_ext fun x => rfl)
    (fun s m hm => hom_ext fun x => funext fun j => by
      have h := congrArg (fun g => Hom.toFun g x) (hm j)
      exact h)

instance hasProductsOfShape (J : Type) : HasProductsOfShape J (SEMod M) :=
  ⟨fun F => by
    have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) := HasLimit.mk ⟨_, piFanIsLimit _⟩
    exact hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

instance : HasCountableCoproducts (SEMod M)ᵒᵖ :=
  ⟨fun _ _ => inferInstance⟩

end SEMod

/-! ## The hom-sets of `sEMod[M]ᵒᵖ` and their pointwise sums -/

theorem forall₂_map {α β : Type*} (R : β → β → Prop) (f g : α → β) (h : ∀ a, R (f a) (g a)) :
    ∀ l : List α, List.Forall₂ R (l.map f) (l.map g)
  | [] => List.Forall₂.nil
  | a :: l => List.Forall₂.cons (h a) (forall₂_map R f g h l)

/-- A family dominated by a summable one is summable. -/
theorem CSummable.of_le {E : Type u} [EffectAlgebra E] {J : Type} {x y : J → E}
    (hx : CSummable x) (h : ∀ j, y j ≼ x j) : CSummable y := fun F => by
  obtain ⟨s, hs⟩ := hx F
  obtain ⟨t, ht, -⟩ := isSumOf_of_forall₂_le (forall₂_map _ y x h F.toList) hs
  exact ⟨t, ht⟩

theorem isCSum_const_zero {E : Type u} [EffectAlgebra E] {J : Type} :
    IsCSum (fun _ : J => (0 : E)) 0 := by
  have hz : ∀ (F : Finset J) (t : E), FinSum (fun _ : J => (0 : E)) F t → t = 0 :=
    fun F t ht => isSumOf_eq_zero (by simp) ht
  have h0 : ∀ F : Finset J, FinSum (fun _ : J => (0 : E)) F 0 := by
    intro F
    unfold FinSum
    induction F.toList with
    | nil => exact PCM.IsSumOf.nil
    | cons a l ih =>
      have := PCM.IsSumOf.cons ih (PCM.zero_perp (0 : E))
      rwa [PCM.zero_ovee] at this
  refine ⟨fun F => ⟨0, h0 F⟩, ?_, fun c _ => pcm_zero_le c⟩
  rintro t ⟨F, hF⟩
  rw [hz F t hF]; exact pcm_preorder_refl _

namespace SEMod

variable {M : Type u} [EffectMonoid M]

theorem summable_of_le {E : SEMod M} {J : Type} [Countable J] {x y : J → E.carrier}
    (hx : Summable x) (h : ∀ j, y j ≼ x j) : Summable y :=
  CSummable.of_le hx h

theorem sigmaExtends (E : SEMod M) : SigmaPAMExtends E.carrier :=
  canonicalSigmaPAM_extends E.sigma.1

theorem zero_eq (E : SEMod M) : (zero : E.carrier) = 0 := zero_eq_of_extends E.sigmaExtends

theorem perp_iff_summable {E : SEMod M} (a b : E.carrier) : Perp a b ↔ Summable ![a, b] :=
  ⟨fun h => ((E.sigmaExtends a b _).1 ⟨h, rfl⟩).summable,
    fun h => ((E.sigmaExtends a b _).2 (sumsTo_sum h)).1⟩

/-- The zero map. -/
def zeroHom (D E : SEMod M) : D ⟶ E where
  toFun _ := 0
  additive := ⟨rfl, fun _ => ⟨PCM.zero_perp 0, PCM.zero_ovee 0⟩⟩
  map_smul r _ := (emod_smul_zero r).symm
  sigma _ _ _ _ _ := isCSum_const_zero

/-- The map `r ↦ r · e` out of the unit object. -/
def smulMap (E : SEMod M) (hM : IsSigmaEffectMonoid M) (e : E.carrier) : unit M hM ⟶ E where
  toFun := fun (r : M) => r • e
  additive := ⟨emod_zero_smul (M := M) e, fun h => EffectModule.perp_smul (M := M) h e⟩
  map_smul r s := EffectModule.mul_smul (M := M) (E := E.carrier) r s e
  sigma := E.sigma.2.2 e

/-- Every map out of the unit object is `r ↦ r · p(1)`. -/
theorem eq_smulMap {E : SEMod M} {hM : IsSigmaEffectMonoid M} (p : unit M hM ⟶ E) :
    p = smulMap E hM (p.toFun 1) := by
  refine hom_ext fun (r : M) => ?_
  have h := p.map_smul r 1
  show p.toFun r = r • p.toFun 1
  rw [← h]
  congr 1
  exact (EffectMonoid.mul_one r).symm

/-- The inclusion `E → ∏_{k∈J} E` at `j` (the tupling of `id` at `j` and
`0` elsewhere). -/
noncomputable def inj (E : SEMod M) {J : Type} (j : J) : E ⟶ pi (fun _ : J => E) := by
  classical
  exact piLift fun k => if k = j then 𝟙 E else zeroHom E E

open Classical in
theorem inj_apply (E : SEMod M) {J : Type} (j k : J) (a : E.carrier) :
    (inj E j).toFun a k = if k = j then a else 0 := by
  unfold inj
  show (if k = j then 𝟙 E else zeroHom E E).toFun a = _
  split_ifs <;> rfl

/-- The family `(ι_j a)_j` sums to the constant `a` in `∏ E`. -/
theorem sumsTo_inj (E : SEMod M) {J : Type} [Countable J] (a : E.carrier) :
    @SumsTo (pi (fun _ : J => E)).carrier _ J _ (fun j => (inj E j).toFun a)
      (fun _ : J => a) := by
  classical
  refine (sumsTo_iff (pi fun _ : J => E) _ _).2 ((isCSum_pi_iff _ _).2 fun k => ?_)
  refine (sumsTo_iff E _ _).1 ?_
  show SumsTo (fun j => (inj E j).toFun a k) a
  rw [sumsTo_congr (fun j => inj_apply E j k a), sumsTo_split _ (fun j => k = j)]
  refine ⟨a, zero, ?_, ?_, sumsTo_pair_comm (sumsTo_zero_pair a)⟩
  · have : Unique {j // k = j} := ⟨⟨⟨k, rfl⟩⟩, fun j => Subtype.ext j.2.symm⟩
    refine (sumsTo_congr fun j => ?_).1 (sumsTo_of_unique' (fun _ : {j // k = j} => a) default)
    split_ifs with h
    · rfl
    · exact absurd j.2 h
  · refine (sumsTo_congr fun j => ?_).1 (sumsTo_zero_family _)
    split_ifs with h
    · exact absurd h j.2
    · exact E.zero_eq

theorem iso_hom_one {E F : SEMod M} (e : E ≅ F) : e.hom.toFun 1 = 1 := by
  have h1 : e.inv.toFun (e.hom.toFun 1) = 1 := congrArg (fun g => Hom.toFun g 1) e.hom_inv_id
  have h2 : e.inv.toFun 1 = 1 :=
    eabasics_le_antisymm (ea_le_one _) (h1 ▸ e.inv.mono (ea_le_one _))
  have h3 : e.hom.toFun (e.inv.toFun 1) = 1 := congrArg (fun g => Hom.toFun g 1) e.inv_hom_id
  rwa [h2] at h3

theorem prod_fst_one (A B : SEMod M) : (prod.fst : A ⨯ B ⟶ A).toFun 1 = 1 := by
  let t : LimitCone (pair A B) := ⟨piFan (pairFunction A B), piFanIsLimit _⟩
  have h := limit.isoLimitCone_hom_π t ⟨WalkingPair.left⟩
  have := congrArg (fun g => Hom.toFun g 1) h
  rw [show (prod.fst : A ⨯ B ⟶ A) = limit.π (pair A B) ⟨WalkingPair.left⟩ from rfl, ← this]
  show ((limit.isoLimitCone t).hom.toFun 1) WalkingPair.left = 1
  rw [iso_hom_one]; rfl

theorem prod_snd_one (A B : SEMod M) : (prod.snd : A ⨯ B ⟶ B).toFun 1 = 1 := by
  let t : LimitCone (pair A B) := ⟨piFan (pairFunction A B), piFanIsLimit _⟩
  have h := limit.isoLimitCone_hom_π t ⟨WalkingPair.right⟩
  have := congrArg (fun g => Hom.toFun g 1) h
  rw [show (prod.snd : A ⨯ B ⟶ B) = limit.π (pair A B) ⟨WalkingPair.right⟩ from rfl, ← this]
  show ((limit.isoLimitCone t).hom.toFun 1) WalkingPair.right = 1
  rw [iso_hom_one]; rfl

/-- The core computation of SIG 66 (iv): maps whose values at `1` are
summable have pointwise sums, which are again morphisms. -/
theorem exists_pointwise_sum {D E : SEMod M} {J : Type} [Countable J] (f : J → (D ⟶ E))
    (h1 : Summable (fun j => (f j).toFun 1)) :
    ∃ g : D ⟶ E, ∀ a, SumsTo (fun j => (f j).toFun a) (g.toFun a) := by
  have hs : ∀ a, Summable (fun j => (f j).toFun a) := fun a =>
    summable_of_le h1 (fun j => (f j).mono (ea_le_one a))
  let G : D.carrier → E.carrier := fun a => sum _ (hs a)
  have hG : ∀ a, SumsTo (fun j => (f j).toFun a) (G a) := fun a => sumsTo_sum (hs a)
  have hext := E.sigmaExtends
  refine ⟨⟨G, ⟨?_, fun {a b} hab => ?_⟩, fun r a => ?_, fun I _ x s hs' => ?_⟩, hG⟩
  · have h0 : SumsTo (fun j => (f j).toFun 0) (zero : E.carrier) :=
      (sumsTo_congr fun j => by rw [(f j).map_zero, E.zero_eq]).1 (sumsTo_zero_family J)
    exact ((hG 0).unique h0).trans E.zero_eq
  · let x : J × Fin 2 → E.carrier := fun q => ![(f q.1).toFun a, (f q.1).toFun b] q.2
    have hrow : ∀ j, SumsTo (fun i => x (j, i)) ((f j).toFun (ovee a b hab)) := by
      intro j
      obtain ⟨h', e⟩ := (f j).map_ovee hab
      exact (sumsTo_congr (by intro i; fin_cases i <;> rfl)).1 ((hext _ _ _).1 ⟨h', e⟩)
    have hx : SumsTo x (G (ovee a b hab)) := (sumsTo_prod_iff x _).2 ⟨_, hrow, hG _⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff' x _).1 hx
    have ht' : t = ![G a, G b] := by
      funext i; fin_cases i
      · exact (ht 0).unique (hG a)
      · exact (ht 1).unique (hG b)
    rw [ht'] at hts
    exact (hext _ _ _).2 hts
  · have h1 := (sumsTo_iff E _ _).2 (E.sigma.2.1 r J _ _ ((sumsTo_iff E _ _).1 (hG a)))
    have h2 : SumsTo (fun j => (f j).toFun (r • a)) (r • G a) :=
      (sumsTo_congr fun j => ((f j).map_smul r a).symm).1 h1
    exact (hG _).unique h2
  · rw [← sumsTo_iff] at hs' ⊢
    let y : J × I → E.carrier := fun q => (f q.1).toFun (x q.2)
    have hy : SumsTo y (G s) :=
      (sumsTo_prod_iff y _).2 ⟨_, fun j => (f j).sumsTo hs', hG s⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff' y _).1 hy
    have ht' : t = fun i => G (x i) := funext fun i => (ht i).unique (hG (x i))
    rw [ht'] at hts
    exact hts

/-- The data of the pointwise σ-PAM on `sEMod[M]ᵒᵖ(X, Y) = sEMod[M](Y, X)`. -/
theorem homData (X Y : (SEMod M)ᵒᵖ) :
    PointwiseData (fun (f : X ⟶ Y) (a : Y.unop.carrier) => f.unop.toFun a) where
  inj f g h := Quiver.Hom.unop_inj (Hom.ext h)
  nonempty := ⟨(zeroHom Y.unop X.unop).op⟩
  sub f P := by
    rintro ⟨g, hg⟩
    obtain ⟨g', hg'⟩ := exists_pointwise_sum (fun j : {j // P j} => (f j.1).unop)
      (summable_subfamily (hg 1).summable P)
    exact ⟨g'.op, hg'⟩
  lim f h := by
    have h1 : Summable (fun j => (f j).unop.toFun 1) := limit _ fun F => by
      obtain ⟨g, hg⟩ := h F; exact (hg 1).summable
    obtain ⟨g', hg'⟩ := exists_pointwise_sum (fun j => (f j).unop) h1
    exact ⟨g'.op, hg'⟩

/-- **SIG 63** (proof, (iv)): the σ-PAM on the hom-sets of `sEMod[M]ᵒᵖ`:
pointwise sums. -/
noncomputable instance homSigmaPAM (X Y : (SEMod M)ᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  pointwiseSigmaPAM (homData X Y)

theorem hom_sumsTo_iff {X Y : (SEMod M)ᵒᵖ} {J : Type} [Countable J] (f : J → (X ⟶ Y))
    (g : X ⟶ Y) : SumsTo f g ↔ ∀ a, SumsTo (fun j => (f j).unop.toFun a) (g.unop.toFun a) :=
  pointwise_sumsTo_iff (homData X Y) f g

/-- **SIG 63** (proof, (iv)): a countable family in `sEMod[M]ᵒᵖ(E, D)`
(maps `D → E`) is summable iff `(f_j(1))_j` is summable in `E`. -/
theorem hom_summable_iff {X Y : (SEMod M)ᵒᵖ} {J : Type} [Countable J] (f : J → (X ⟶ Y)) :
    Summable f ↔ Summable (fun j => (f j).unop.toFun 1) := by
  constructor
  · rintro ⟨g, hg⟩; exact (hg 1).summable
  · intro h
    obtain ⟨g, hg⟩ := exists_pointwise_sum (fun j => (f j).unop) h
    exact ⟨g.op, hg⟩

theorem hom_zero_eq (X Y : (SEMod M)ᵒᵖ) : (0 : X ⟶ Y) = (zeroHom Y.unop X.unop).op := by
  apply Quiver.Hom.unop_inj
  refine hom_ext fun a => ?_
  have h := (hom_sumsTo_iff (Empty.elim : Empty → (X ⟶ Y)) _).1 (sumsTo_of_isEmpty _) a
  exact (h.unique (sumsTo_of_isEmpty _)).trans X.unop.zero_eq

theorem hom_perp_iff {X Y : (SEMod M)ᵒᵖ} (p q : X ⟶ Y) :
    Perp p q ↔ Perp (p.unop.toFun 1) (q.unop.toFun 1) := by
  show SigmaPAM.Summable ![p, q] ↔ _
  rw [hom_summable_iff, perp_iff_summable]
  exact iff_of_eq (congrArg SigmaPAM.Summable (funext fun i => by fin_cases i <;> rfl))

theorem hom_ovee_apply {X Y : (SEMod M)ᵒᵖ} {p q : X ⟶ Y} (h : Perp p q) (a : Y.unop.carrier) :
    ∃ h' : Perp (p.unop.toFun a) (q.unop.toFun a),
      ovee (p.unop.toFun a) (q.unop.toFun a) h' = (ovee p q h).unop.toFun a := by
  have := (hom_sumsTo_iff _ _).1 (sumsTo_sum (show SigmaPAM.Summable ![p, q] from h)) a
  refine (X.unop.sigmaExtends _ _ _).2 ((sumsTo_congr fun i => ?_).1 this)
  fin_cases i <;> rfl

theorem unop_comp_apply {X Y Z : (SEMod M)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (z : Z.unop.carrier) :
    (f ≫ g).unop.toFun z = f.unop.toFun (g.unop.toFun z) := rfl

/-! ### `sEMod[M]ᵒᵖ` is a σ-effectus (SIG 28, 66) -/

/-- The chosen coproduct `∐_J B` of `sEMod[M]ᵒᵖ` is the product `∏_J B` of
`sEMod[M]`. -/
noncomputable def coprodIso (B : (SEMod M)ᵒᵖ) (J : Type) :
    ∐ (fun _ : J => B) ≅ op (pi (fun _ : J => B.unop)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (Fan.IsLimit.op (piFanIsLimit (fun _ : J => B.unop)))

theorem inj_comp_piProj_self (E : SEMod M) {J : Type} (j : J) :
    inj E j ≫ piProj (fun _ : J => E) j = 𝟙 E := by
  classical
  refine hom_ext fun a => ?_
  show (inj E j).toFun a j = a
  rw [inj_apply]; simp

theorem inj_comp_piProj_ne (E : SEMod M) {J : Type} {j k : J} (h : k ≠ j) :
    inj E j ≫ piProj (fun _ : J => E) k = zeroHom E E := by
  classical
  refine hom_ext fun a => ?_
  show (inj E j).toFun a k = 0
  rw [inj_apply]; simp [h]

/-- The partial projections of `∐_J B` are the inclusions of `∏_J B`. -/
theorem pproj_eq (B : (SEMod M)ᵒᵖ) {J : Type} (j : J) :
    pproj (fun _ : J => B) j = (coprodIso B J).hom ≫ (inj B.unop j).op := by
  refine Sigma.hom_ext _ _ fun k => ?_
  have hι : Sigma.ι (fun _ : J => B) k ≫ (coprodIso B J).hom =
      (piProj (fun _ : J => B.unop) k).op :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk k)
  rw [← Category.assoc, hι, ← op_comp]
  by_cases hk : k = j
  · subst hk
    rw [ι_pproj_self]
    exact (congrArg Quiver.Hom.op (inj_comp_piProj_self B.unop k)).symm
  · rw [ι_pproj_ne _ hk, hom_zero_eq]
    exact congrArg Quiver.Hom.op (inj_comp_piProj_ne B.unop hk).symm

theorem coprod_inl_one (B : (SEMod M)ᵒᵖ) :
    (coprod.inl : B ⟶ B ⨿ B).unop.toFun 1 = 1 := by
  have h := congrArg (fun g => Hom.toFun g 1) (opProdIsoCoprod_hom_fst (A := B.unop) (B := B.unop))
  have h2 : (prod.fst : B.unop ⨯ B.unop ⟶ B.unop).toFun
      ((opProdIsoCoprod B.unop B.unop).hom.unop.toFun 1) = 1 := by
    rw [show (opProdIsoCoprod B.unop B.unop).hom.unop.toFun 1 = 1 from
      iso_hom_one (opProdIsoCoprod B.unop B.unop).unop, prod_fst_one]
  exact h.symm.trans h2

theorem coprod_inr_one (B : (SEMod M)ᵒᵖ) :
    (coprod.inr : B ⟶ B ⨿ B).unop.toFun 1 = 1 := by
  have h := congrArg (fun g => Hom.toFun g 1) (opProdIsoCoprod_hom_snd (A := B.unop) (B := B.unop))
  have h2 : (prod.snd : B.unop ⨯ B.unop ⟶ B.unop).toFun
      ((opProdIsoCoprod B.unop B.unop).hom.unop.toFun 1) = 1 := by
    rw [show (opProdIsoCoprod B.unop B.unop).hom.unop.toFun 1 = 1 from
      iso_hom_one (opProdIsoCoprod B.unop B.unop).unop, prod_snd_one]
  exact h.symm.trans h2

/-- **SIG 63** (proof, (i)–(iv)): `sEMod[M]ᵒᵖ` is a σ-PAC: countable
coproducts are products of `sEMod[M]`, composition is σ-biadditive for the
pointwise sums, compatible families are summable, and untying holds. -/
instance sigmaPAC : SigmaPAC (SEMod M)ᵒᵖ where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s hs => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s hs => ?_⟩
    · rw [hom_sumsTo_iff] at hs ⊢
      exact fun z => hs (g.unop.toFun z)
    · rw [hom_sumsTo_iff] at hs ⊢
      exact fun z => f.unop.sumsTo (hs z)
  compatible_sum {J} _ {A B} f := by
    rintro ⟨h, hh⟩
    rw [hom_summable_iff]
    let H := (h ≫ (coprodIso B J).hom).unop
    have hval : ∀ j, (f j).unop.toFun 1 = H.toFun ((inj B.unop j).toFun 1) := by
      intro j
      rw [← hh j, pproj_eq, ← Category.assoc]
      rfl
    rw [show (fun j => (f j).unop.toFun 1) = fun j => H.toFun ((inj B.unop j).toFun 1) from
      funext hval]
    exact (H.sumsTo (sumsTo_inj B.unop 1)).summable
  untying {A B f g} h := by
    rw [hom_summable_iff] at h ⊢
    have e : (fun j => (![f ≫ coprod.inl, g ≫ coprod.inr] j).unop.toFun 1) =
        fun j => (![f, g] j).unop.toFun 1 := by
      funext j
      fin_cases j
      · show f.unop.toFun ((coprod.inl : B ⟶ B ⨿ B).unop.toFun 1) = f.unop.toFun 1
        rw [coprod_inl_one]
      · show g.unop.toFun ((coprod.inr : B ⟶ B ⨿ B).unop.toFun 1) = g.unop.toFun 1
        rw [coprod_inr_one]
    rw [e]; exact h

variable (hM : IsSigmaEffectMonoid M)

theorem smulMap_one_apply (E : SEMod M) (e : E.carrier) :
    (smulMap E hM e).toFun 1 = e := EffectModule.one_smul e

theorem perp_orth' {X : (SEMod M)ᵒᵖ} (p : X ⟶ op (unit M hM)) :
    Perp p (smulMap X.unop hM (orth (p.unop.toFun 1))).op := by
  rw [hom_perp_iff]
  show Perp (p.unop.toFun 1) ((smulMap X.unop hM _).toFun 1)
  rw [smulMap_one_apply]
  exact EffectAlgebra.perp_orth _

theorem zero_of_apply_one {X Y : (SEMod M)ᵒᵖ} {f : X ⟶ Y} (h : f.unop.toFun 1 = 0) : f = 0 := by
  rw [hom_zero_eq]
  apply Quiver.Hom.unop_inj
  refine hom_ext fun a => ?_
  show f.unop.toFun a = 0
  exact eq_zero_of_le_zero (h ▸ f.unop.mono (ea_le_one a))

/-- **SIG 28** (`prop:emod-effectus`, main.tex:816), σ-case, = **SIG 63**
(`prop:sEMod-sigma-effectus`, main.tex:2093): for a σ-effect monoid `M`,
`sEMod[M]ᵒᵖ` is a σ-effectus, with unit object `M`, truth maps
`1_E : r ↦ r · 1`, and countable coproducts the cartesian products. -/
noncomputable def sigmaEffectus : SigmaEffectus (SEMod M)ᵒᵖ where
  I := op (unit M hM)
  one X := (smulMap X.unop hM 1).op
  orth {X} p := (smulMap X.unop hM (orth (p.unop.toFun 1))).op
  perp_orth p := perp_orth' hM p
  ovee_orth {X} p := by
    apply Quiver.Hom.unop_inj
    refine hom_ext fun (r : M) => ?_
    obtain ⟨h', e⟩ := hom_ovee_apply (perp_orth' hM p) r
    have hp : p.unop.toFun r = r • p.unop.toFun 1 :=
      congrArg (fun g => Hom.toFun g r) (eq_smulMap (hM := hM) p.unop)
    obtain ⟨h'', e''⟩ := EffectModule.smul_perp r (EffectAlgebra.perp_orth (p.unop.toFun 1))
    rw [← e]
    calc ovee (p.unop.toFun r) _ h'
        = ovee (r • p.unop.toFun 1) (r • orth (p.unop.toFun 1)) h'' :=
          PCM.ovee_congr hp rfl h' h''
      _ = r • ovee (p.unop.toFun 1) (orth (p.unop.toFun 1)) _ := e''
      _ = r • 1 := by rw [EffectAlgebra.ovee_orth]
  orth_unique {X p q} h e := by
    obtain ⟨h', e'⟩ := hom_ovee_apply h 1
    have h1 : ovee (p.unop.toFun 1) (q.unop.toFun 1) h' = 1 := by
      rw [e', e]; exact smulMap_one_apply hM X.unop 1
    have hq : q.unop.toFun 1 = orth (p.unop.toFun 1) := EffectAlgebra.orth_unique h' h1
    apply Quiver.Hom.unop_inj
    rw [eq_smulMap (hM := hM) q.unop, hq]
    rfl
  eq_zero_of_perp_one {X p} h := by
    rw [hom_perp_iff] at h
    have h1 : (smulMap X.unop hM 1).op.unop.toFun 1 = 1 := smulMap_one_apply hM X.unop 1
    rw [h1] at h
    exact zero_of_apply_one (EffectAlgebra.eq_zero_of_perp_one h)
  eq_zero_of_one_zero {X Y f} h := by
    apply zero_of_apply_one
    have h1 := congrArg (fun g : X ⟶ op (unit M hM) => g.unop.toFun 1) h
    simp only at h1
    rw [hom_zero_eq] at h1
    have h2 : (f ≫ (smulMap Y.unop hM 1).op).unop.toFun 1 = f.unop.toFun 1 := by
      show f.unop.toFun ((smulMap Y.unop hM 1).toFun 1) = _
      rw [smulMap_one_apply]
    rw [← h2]; exact h1
  perp_of_one_perp {X Y f g} h := by
    rw [hom_perp_iff] at h ⊢
    have e : ∀ k : X ⟶ Y, (k ≫ (smulMap Y.unop hM 1).op).unop.toFun 1 = k.unop.toFun 1 := by
      intro k
      show k.unop.toFun ((smulMap Y.unop hM 1).toFun 1) = _
      rw [smulMap_one_apply]
    rw [e, e] at h
    exact h

/-- **SIG 28** (main.tex:822): the countable coproducts of `sEMod[M]ᵒᵖ` are
the cartesian products with pointwise operations. -/
noncomputable def coproductIsColimit {J : Type} (D : J → SEMod M) : IsColimit (piFan D).op :=
  Fan.IsLimit.op (piFanIsLimit D)

/-- Right multiplication `t ↦ t · r` on the unit object. -/
def rmul (r : M) : unit M hM ⟶ unit M hM where
  toFun := fun (t : M) => t * r
  additive := ⟨(exc_emonzero r).2, fun {a b} h => by
    obtain ⟨h', e⟩ := emon_ovee_mul r h; exact ⟨h', e.symm⟩⟩
  map_smul s t := EffectMonoid.mul_assoc s t r
  sigma := hM.2.2 r

/-- **SIG 28** (main.tex:816), "with scalars `M`": the scalars of the
σ-effectus `sEMod[M]ᵒᵖ` form an effect monoid isomorphic to `M`, via
`p ↦ p(1)`. -/
theorem sigmaEffectus_scalars :
    letI := sigmaEffectus hM
    EMIso (Scal (SEMod M)ᵒᵖ) M := by
  let _ := sigmaEffectus hM
  let φ : EffectMonoidHom (Scal (SEMod M)ᵒᵖ) M :=
    { toFun := fun p => p.unop.toFun 1
      perp_map := fun {p q} h => (hom_perp_iff p q).1 h
      ovee_map := fun {p q} h => by
        obtain ⟨h', e⟩ := hom_ovee_apply h 1
        exact e.symm
      map_one := smulMap_one_apply hM (unit M hM) 1
      map_mul := fun l m => by
        show (m ≫ l).unop.toFun 1 = @HMul.hMul M M M _ (l.unop.toFun 1) (m.unop.toFun 1)
        exact congrArg (fun g => Hom.toFun g (l.unop.toFun 1)) (eq_smulMap (hM := hM) m.unop) }
  let ψ : EffectMonoidHom M (Scal (SEMod M)ᵒᵖ) :=
    { toFun := fun r => (rmul hM r).op
      perp_map := fun {r s} h => (hom_perp_iff _ _).2 (by
        show Perp (@HMul.hMul M M M _ 1 r) (@HMul.hMul M M M _ 1 s)
        rw [EffectMonoid.one_mul, EffectMonoid.one_mul]; exact h)
      ovee_map := fun {r s} h => by
        have hp : Perp (rmul hM r).op (rmul hM s).op := (hom_perp_iff _ _).2 (by
          show Perp (@HMul.hMul M M M _ 1 r) (@HMul.hMul M M M _ 1 s)
          rw [EffectMonoid.one_mul, EffectMonoid.one_mul]; exact h)
        apply Quiver.Hom.unop_inj
        refine hom_ext fun (t : M) => ?_
        obtain ⟨h', e⟩ := hom_ovee_apply hp t
        obtain ⟨h'', e''⟩ := emon_mul_ovee t h
        refine e''.trans (Eq.trans ?_ e)
        exact PCM.ovee_congr rfl rfl _ _
      map_one := by
        apply Quiver.Hom.unop_inj
        exact hom_ext fun (t : M) => rfl
      map_mul := fun r s => by
        apply Quiver.Hom.unop_inj
        refine hom_ext fun (t : M) => ?_
        show t * (r * s) = (t * r) * s
        exact (EffectMonoid.mul_assoc t r s).symm }
  refine ⟨φ, ψ, fun p => ?_, fun r => EffectMonoid.one_mul r⟩
  apply Quiver.Hom.unop_inj
  refine hom_ext fun (t : M) => ?_
  exact (congrArg (fun g => Hom.toFun g t) (eq_smulMap (hM := hM) p.unop)).symm

end SEMod


/-! ## Countable coproducts in a σ-effectus (SIG 69) -/

section SigmaCoproducts

/-- A family supported at one index sums to its value there. -/
theorem sumsTo_single {M : Type u} [SigmaPAM M] {Λ : Type} [Countable Λ] (x : Λ → M) (i : Λ)
    (h : ∀ l, l ≠ i → x l = zero) : SumsTo x (x i) := by
  rw [sumsTo_split x (· = i)]
  refine ⟨x i, zero, ?_, ?_, sumsTo_pair_comm (sumsTo_zero_pair (x i))⟩
  · have : Unique {l // l = i} := ⟨⟨⟨i, rfl⟩⟩, fun (l : {l // l = i}) => Subtype.ext l.2⟩
    refine (sumsTo_congr fun (l : {l // l = i}) => ?_).1
      (sumsTo_of_unique' (fun _ : {l // l = i} => x i) default)
    show x i = x l.1
    rw [l.2]
  · exact (sumsTo_congr fun (l : {l // ¬ l = i}) => (h l.1 l.2).symm).1 (sumsTo_zero_family _)

variable {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

theorem le_comp_left' {W X Y : C} {a b : X ⟶ Y} (h : a ≼ b) (k : W ⟶ X) :
    (k ≫ a) ≼ (k ≫ b) := by
  obtain ⟨c, hac, rfl⟩ := h
  obtain ⟨h', e⟩ := FinPAC.ovee_comp hac k
  exact ⟨k ≫ c, h', e.symm⟩

/-- Countable coprojections are total. -/
theorem ι_truth {Λ : Type} [Countable Λ] (B : Λ → C) (i : Λ) :
    Sigma.ι B i ≫ truth (∐ B) = truth (B i) := by
  refine eabasics_le_antisymm (ea_le_one (E := B i ⟶ effObj C) _) ?_
  have h := le_comp_left' (ea_le_one (E := ∐ B ⟶ effObj C) (pproj B i ≫ truth (B i)))
    (Sigma.ι B i)
  rwa [← Category.assoc, ι_pproj_self, Category.id_comp] at h

/-- `⋁_λ κ_λ ∘ ▷_λ = id` (the hidden proof of SIG 69). -/
theorem sumsTo_pproj_ι {Λ : Type} [Countable Λ] (B : Λ → C) :
    SumsTo (fun i => pproj B i ≫ Sigma.ι B i) (𝟙 (∐ B)) := by
  classical
  let m : ∐ B ⟶ ∐ (fun _ : Λ => ∐ B) :=
    Sigma.desc fun l => Sigma.ι B l ≫ Sigma.ι (fun _ : Λ => ∐ B) l
  have hm : ∀ i, m ≫ pproj (fun _ : Λ => ∐ B) i = pproj B i ≫ Sigma.ι B i := by
    intro i
    refine Sigma.hom_ext _ _ fun l => ?_
    rw [Sigma.ι_desc_assoc, Category.assoc]
    by_cases hl : l = i
    · subst hl
      rw [ι_pproj_self, ← Category.assoc, ι_pproj_self, Category.id_comp, Category.comp_id]
    · rw [ι_pproj_ne _ hl, ← Category.assoc, ι_pproj_ne _ hl, FinPAC.comp_zero,
        FinPAC.zero_comp]
  obtain ⟨E, hE⟩ : ∃ E, SumsTo (fun i => pproj B i ≫ Sigma.ι B i) E :=
    ⟨_, sumsTo_sum (SigmaPAC.compatible_sum _ ⟨m, hm⟩)⟩
  have hE1 : E = 𝟙 (∐ B) := by
    refine Sigma.hom_ext _ _ fun l => ?_
    have h1 := comp_sumsTo_right (Sigma.ι B l) hE
    have h2 := sumsTo_single (fun i => Sigma.ι B l ≫ pproj B i ≫ Sigma.ι B i) l (by
      intro i hi
      rw [← Category.assoc, ι_pproj_ne _ (Ne.symm hi), FinPAC.zero_comp]; rfl)
    rw [h1.unique h2, ← Category.assoc, ι_pproj_self, Category.id_comp, Category.comp_id]
  rwa [hE1] at hE

/-- `f = ⋁_λ κ_λ ∘ ▷_λ ∘ f` for `f : A → ∐ B_λ`. -/
theorem sumsTo_decomp {Λ : Type} [Countable Λ] (B : Λ → C) {A : C} (f : A ⟶ ∐ B) :
    SumsTo (fun i => (f ≫ pproj B i) ≫ Sigma.ι B i) f := by
  have := comp_sumsTo_right f (sumsTo_pproj_ι B)
  rw [Category.comp_id] at this
  exact (sumsTo_congr fun i => (Category.assoc _ _ _).symm).1 this

/-- **SIG 66** (`lem:decomposition-bijection`, main.tex:2738, Lemma): maps
`f : A → ∐ B_λ` correspond bijectively, via `f_λ = ▷_λ ∘ f`, to families
`(f_λ : A → B_λ)` with `(1 ∘ f_λ)_λ` summable.  (Printed without proof, "in
the same manner as the finite case"; ours follows the hidden Auxproof: the
identity `⋁ κ_λ ▷_λ = id` and the countable form of effectus axiom (iii).) -/
theorem decomposition_bijection {Λ : Type} [Countable Λ] (B : Λ → C) (A : C) :
    (∀ f : A ⟶ ∐ B, Summable (fun i => (f ≫ pproj B i) ≫ truth (B i))) ∧
      ∀ g : ∀ i, A ⟶ B i, Summable (fun i => g i ≫ truth (B i)) →
        ∃! f : A ⟶ ∐ B, ∀ i, f ≫ pproj B i = g i := by
  have hdec : ∀ f : A ⟶ ∐ B, SumsTo (fun i => (f ≫ pproj B i) ≫ Sigma.ι B i) f :=
    fun f => sumsTo_decomp B f
  refine ⟨fun f => ?_, fun g hg => ?_⟩
  · have := comp_sumsTo_left (truth (∐ B)) (hdec f)
    refine ((sumsTo_congr fun i => ?_).1 this).summable
    rw [Category.assoc, ι_truth]
  · have hy : Summable (fun i => g i ≫ Sigma.ι B i) := by
      refine summable_of_summable_truth _ ?_
      refine ((sumsTo_congr fun i => ?_).1 (sumsTo_sum hg)).summable
      rw [Category.assoc, ι_truth]
    obtain ⟨f, hf⟩ : ∃ f, SumsTo (fun i => g i ≫ Sigma.ι B i) f := ⟨_, sumsTo_sum hy⟩
    refine ⟨f, fun j => ?_, fun f' hf' => ?_⟩
    · have h1 := comp_sumsTo_left (pproj B j) hf
      have h2 := sumsTo_single (fun i => (g i ≫ Sigma.ι B i) ≫ pproj B j) j (by
        intro i hi
        rw [Category.assoc, ι_pproj_ne _ hi, FinPAC.comp_zero]; rfl)
      rw [h1.unique h2, Category.assoc, ι_pproj_self, Category.comp_id]
    · refine (hdec f').unique ((sumsTo_congr fun i => ?_).2 hf)
      rw [hf' i]

/-- Cotupling of predicates is σ-additive (the countable form of 181IV). -/
theorem sigma_desc_sumsTo {Λ : Type} [Countable Λ] (A : Λ → C) {I : Type} [Countable I]
    (q : I → ∀ l, A l ⟶ effObj C) (s : ∀ l, A l ⟶ effObj C)
    (h : ∀ l, SumsTo (fun i => q i l) (s l)) :
    SumsTo (fun i => Sigma.desc (q i)) (Sigma.desc s) := by
  have hI : truth (effObj C) = 𝟙 (effObj C) := truth_effObj_eq_id
  -- each `(q_i(l))_i` is compatible, via some `h_l : A_l → ∐_I I`
  have hc : ∀ l, ∃ hl : A l ⟶ ∐ (fun _ : I => effObj C),
      ∀ i, hl ≫ pproj (fun _ : I => effObj C) i = q i l := by
    intro l
    refine ((decomposition_bijection (fun _ : I => effObj C) (A l)).2 (fun i => q i l) ?_).exists
    refine ((sumsTo_congr fun i => ?_).1 (h l)).summable
    rw [hI, Category.comp_id]
  choose hl hhl using hc
  have hcomp : Compatible (A := fun _ : I => effObj C) (fun i => Sigma.desc (q i)) := by
    refine ⟨Sigma.desc hl, fun i => Sigma.hom_ext _ _ fun l => ?_⟩
    rw [Sigma.ι_desc_assoc, hhl, Sigma.ι_desc]
  obtain ⟨S, hS⟩ : ∃ S, SumsTo (fun i => Sigma.desc (q i)) S :=
    ⟨_, sumsTo_sum (SigmaPAC.compatible_sum _ hcomp)⟩
  have : S = Sigma.desc s := Sigma.hom_ext _ _ fun l => by
    have h1 := comp_sumsTo_right (Sigma.ι A l) hS
    rw [Sigma.ι_desc]
    exact h1.unique ((sumsTo_congr fun i => (Sigma.ι_desc _ _).symm).1 (h l))
  rwa [this] at hS

end SigmaCoproducts

/-! ## SIG 29, 67: the predicate functor -/

section PredFunctor

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- The scalars of a σ-effectus form a σ-effect monoid. -/
theorem scal_isSigmaEffectMonoid : IsSigmaEffectMonoid (Scal C) := by
  have hc := (pred_sigmaEffectAlgebra (C := C) (effObj C)).2
  refine ⟨(pred_sigmaEffectAlgebra (effObj C)).1, fun a J _ x s hs => ?_,
    fun b J _ x s hs => ?_⟩
  · exact (hc J _ _).1 (comp_sumsTo_left a ((hc J x s).2 hs))
  · exact (hc J _ _).1 (comp_sumsTo_right b ((hc J x s).2 hs))

/-- `Pred A` as an object of `sEMod[M]` (SIG 25). -/
noncomputable def predObj (A : C) : SEMod (Scal C) where
  carrier := Pred A
  sigma := pred_isSigmaEffectModule A

/-- `Pred f = (-) ∘ f`. -/
noncomputable def predMap {A B : C} (f : A ⟶ B) : predObj B ⟶ predObj A where
  toFun p := f ≫ p
  additive := ⟨FinPAC.comp_zero f, fun h => by
    obtain ⟨h', e⟩ := FinPAC.ovee_comp h f; exact ⟨h', e.symm⟩⟩
  map_smul r p := (Category.assoc f p r).symm
  sigma J _ x s hs := by
    have hc := fun {X : C} => (pred_sigmaEffectAlgebra (C := C) X).2
    exact (hc J _ _).1 (comp_sumsTo_right f ((hc J x s).2 hs))

/-- **SIG 29/67**: the functor `Pred : C → sEMod[M]ᵒᵖ`, `A ↦ Pred A`. -/
noncomputable def predFunctor : C ⥤ (SEMod (Scal C))ᵒᵖ where
  obj A := op (predObj A)
  map f := (predMap f).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    exact SEMod.hom_ext fun p => Category.id_comp p
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    exact SEMod.hom_ext fun p => Category.assoc f g p

/-- `Pred (∐ A_j) ≅ ∏ Pred A_j` (the bijection in the proof of SIG 67). -/
noncomputable def predCoprodIso {J : Type} [Countable J] (A : J → C) :
    predObj (∐ A) ≅ SEMod.pi (fun j => predObj (A j)) where
  hom :=
    { toFun := fun p j => Sigma.ι A j ≫ p
      additive := ⟨funext fun j => FinPAC.comp_zero _, fun {p q} h => by
        choose h' e using fun j => FinPAC.ovee_comp h (Sigma.ι A j)
        exact ⟨h', funext fun j => (e j).symm⟩⟩
      map_smul := fun r p => funext fun j => (Category.assoc _ p r).symm
      sigma := fun I _ x s hs => by
        have hc := fun {X : C} => (pred_sigmaEffectAlgebra (C := C) X).2
        refine (isCSum_pi_iff _ _).2 fun j => ?_
        exact (hc I _ _).1 (comp_sumsTo_right (Sigma.ι A j) ((hc I x s).2 hs)) }
  inv :=
    { toFun := fun q => Sigma.desc q
      additive := ⟨Sigma.hom_ext _ _ fun j => by
          show Sigma.ι A j ≫ Sigma.desc (fun j => (0 : A j ⟶ effObj C)) = Sigma.ι A j ≫ 0
          rw [Sigma.ι_desc, FinPAC.comp_zero], fun {p q} h => by
        have := sigma_desc_sumsTo A ![p, q] (ovee p q h) (fun j => by
          have := sumsTo_sum
            (show SigmaPAM.Summable (![p j, q j] : Fin 2 → (A j ⟶ effObj C)) from h j)
          exact (sumsTo_congr (x := (![p j, q j] : Fin 2 → (A j ⟶ effObj C)))
            (y := fun i => ![p, q] i j) (fun i => by fin_cases i <;> rfl)).1 this)
        have this' := (sumsTo_congr (y := ![Sigma.desc p, Sigma.desc q])
          (fun i => by fin_cases i <;> rfl)).1 this
        exact ⟨this'.summable, this'.sum_eq _⟩⟩
      map_smul := fun r q => by
        show Sigma.desc (fun j => q j ≫ r) = Sigma.desc q ≫ r
        refine Sigma.hom_ext _ _ fun j => ?_
        rw [Sigma.ι_desc]
        exact (Sigma.ι_desc_assoc q j r).symm
      sigma := fun I _ x s hs => by
        have hc := fun {X : C} => (pred_sigmaEffectAlgebra (C := C) X).2
        have hs' := (isCSum_pi_iff x s).1 hs
        exact (hc I _ _).1 (sigma_desc_sumsTo A (fun i => x i) s fun j =>
          (hc I _ _).2 (hs' j)) }
  hom_inv_id := by
    refine SEMod.hom_ext fun p => ?_
    exact Sigma.hom_ext _ _ fun j => Sigma.ι_desc _ _
  inv_hom_id := by
    refine SEMod.hom_ext fun q => funext fun j => ?_
    exact Sigma.ι_desc _ _

end PredFunctor


section PredMorphism

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- The chosen coproduct `∐ D_j` of `sEMod[M]ᵒᵖ` is the product `∏ D_j`. -/
noncomputable def SEMod.coprodIsoGen {M : Type u} [EffectMonoid M] {J : Type}
    (D : J → SEMod M) : ∐ (fun j => op (D j)) ≅ op (SEMod.pi D) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (Fan.IsLimit.op (SEMod.piFanIsLimit D))

/-- The comparison `∐ Pred A_j → Pred (∐ A_j)` of `sEMod[M]ᵒᵖ`, as an iso. -/
noncomputable def predSigmaIso {J : Type} [Countable J] (A : J → C) :
    ∐ (fun b => (predFunctor (C := C)).obj (A b)) ≅ (predFunctor (C := C)).obj (∐ A) :=
  SEMod.coprodIsoGen (fun j => predObj (A j)) ≪≫ (predCoprodIso A).op

theorem predFunctor_sigmaComparison {J : Type} [Countable J] (A : J → C) :
    sigmaComparison predFunctor A = (predSigmaIso A).hom := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [ι_comp_sigmaComparison]
  have hι : Sigma.ι (fun j => op (predObj (A j))) j ≫ (SEMod.coprodIsoGen _).hom =
      (SEMod.piProj (fun j => predObj (A j)) j).op :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk j)
  have h3 := hι =≫ (predCoprodIso A).hom.op
  rw [Category.assoc] at h3
  have h2 : (predFunctor (C := C)).map (Sigma.ι A j) =
      (SEMod.piProj (fun j => predObj (A j)) j).op ≫ (predCoprodIso A).hom.op := by
    apply Quiver.Hom.unop_inj
    exact SEMod.hom_ext fun p => rfl
  exact h2.trans h3.symm

instance predFunctor_preservesColimitsOfShape (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J) (predFunctor (C := C)) := by
  constructor
  intro K
  have key : ∀ A : J → C, PreservesColimit (Discrete.functor A) (predFunctor (C := C)) := by
    intro A
    have : IsIso (sigmaComparison (predFunctor (C := C)) A) := by
      rw [predFunctor_sigmaComparison]; infer_instance
    exact PreservesCoproduct.of_iso_comparison _ _
  have := key (K.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- `Pred I` is the unit object `M = C(I, I)`. -/
noncomputable def unitPredIso :
    predObj (effObj C) ≅ SEMod.unit (Scal C) (scal_isSigmaEffectMonoid (C := C)) where
  hom := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl, fun _ _ _ _ h => h⟩
  inv := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl, fun _ _ _ _ h => h⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **SIG 29** (main.tex:840, Proposition), σ-case, = **SIG 64**
(`prop:pred-functor-sigma-effectus`, main.tex:2303): for a σ-effectus `C`
with scalars `M`, `A ↦ Pred A` is a morphism of σ-effectuses
`C → sEMod[M]ᵒᵖ`: it preserves the unit (`Pred I = M`), the truth maps, and
countable coproducts (`Pred (∐ A_j) ≅ ∏ Pred A_j`, cotupling being a
σ-additive bijection). -/
noncomputable def predMorphism :
    letI := SEMod.sigmaEffectus (scal_isSigmaEffectMonoid (C := C))
    SigmaEffectusMorphism C (SEMod (Scal C))ᵒᵖ := by
  letI := SEMod.sigmaEffectus (scal_isSigmaEffectMonoid (C := C))
  exact
  { F := predFunctor
    preserves := fun J _ => inferInstance
    u := unitPredIso.op
    map_truth := fun A => by
      apply Quiver.Hom.unop_inj
      exact SEMod.hom_ext fun p => rfl }

/-- **SIG 37** (`prop:separation-faithful`, main.tex:1051, Proposition),
first half: a σ-effectus is predicate-separated iff `Pred` is faithful.
(Printed: "an immediate consequence of the definition".) -/
theorem predicateSeparated_iff_faithful :
    PredicateSeparated C ↔ (predFunctor (C := C)).Faithful := by
  constructor
  · intro h
    refine ⟨fun {X Y f g} hfg => h f g fun p => ?_⟩
    exact congrArg (fun (k : (predFunctor (C := C)).obj X ⟶ (predFunctor (C := C)).obj Y) =>
      k.unop.toFun p) hfg
  · intro hF A B f g hfg
    refine hF.map_injective ?_
    apply Quiver.Hom.unop_inj
    exact SEMod.hom_ext fun p => hfg p

end PredMorphism

end Papers.SIG
