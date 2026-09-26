/-
Papers/SIG/WeightModules.lean

SIG §3.1, the weight-module half (main.tex:855–1022), with its proofs in
Appendix A (main.tex:2328–2850): points SIG 30–35, 37 (second half), 68, 70.

Design:
* A σ-weight `M`-module (over a σ-effect monoid `M`) is `SWMod M`: a σ-PAM
  with an `M`-action and a weight `X → M`.  Sums in `M` are its canonical
  sums (the relation `IsCSum`, SIG 17), so no σ-PAM instance on `M` is needed
  in the definition.
* `sWMod[M]` is the category `SWMod M` of weight-decreasing σ-additive
  action-preserving maps.  Its countable coproducts are explicit (tuples with
  summable weights) and need `M` to be a σ-effect monoid, supplied as
  `[Fact (IsSigmaEffectMonoid M)]`.
-/
import Papers.SIG.EffectModules

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff Opposite

namespace Papers.SIG

open SigmaPAM

universe u v w

/-! ## Canonical sums in an effect algebra: monotonicity -/

theorem IsCSum.mono {E : Type u} [EffectAlgebra E] {J : Type} {x y : J → E} {s t : E}
    (hs : IsCSum x s) (ht : IsCSum y t) (h : ∀ j, x j ≼ y j) : s ≼ t := by
  refine hs.2.2 t ?_
  rintro a ⟨F, hF⟩
  obtain ⟨b, hb⟩ := ht.1 F
  obtain ⟨a', ha', hle⟩ := isSumOf_of_forall₂_le (forall₂_map _ x y h F.toList) hb
  rw [finSum_unique hF ha']
  exact pcm_preorder_trans hle (ht.finSum_le hb)

theorem finSum_const_zero {E : Type u} [EffectAlgebra E] {J : Type} (F : Finset J) :
    FinSum (fun _ : J => (0 : E)) F 0 := by
  unfold FinSum
  induction F.toList with
  | nil => exact PCM.IsSumOf.nil
  | cons a l ih =>
    have := PCM.IsSumOf.cons ih (PCM.zero_perp (0 : E))
    rwa [PCM.zero_ovee] at this

/-! ## SIG 30: σ-weight modules -/

/-- **SIG 30** (`def:wpmod`, main.tex:869, Definition): a **σ-weight
`M`-module** is a σ-PAM `X` with a σ-biadditive `M`-action and a weight
`|·| : X → M` which is σ-additive and preserves the action
(`|r x| = r |x|`), such that `|x| = 0` implies `x = 0` and countable
families are summable when their weights are.  Sums in `M` are its canonical
sums. -/
structure SWMod (M : Type u) [EffectMonoid M] : Type (u + 1) where
  carrier : Type u
  [pam : SigmaPAM carrier]
  [act : SMul M carrier]
  weight : carrier → M
  one_smul : ∀ x : carrier, (1 : M) • x = x
  mul_smul : ∀ (r s : M) (x : carrier), (r * s) • x = r • s • x
  smul_left : ∀ (x : carrier) {J : Type} [Countable J] (r : J → M) (s : M),
    IsCSum r s → SumsTo (fun j => r j • x) (s • x)
  smul_right : ∀ (r : M) {J : Type} [Countable J] (x : J → carrier) (s : carrier),
    SumsTo x s → SumsTo (fun j => r • x j) (r • s)
  weight_sumsTo : ∀ {J : Type} [Countable J] (x : J → carrier) (s : carrier),
    SumsTo x s → IsCSum (fun j => weight (x j)) (weight s)
  weight_smul : ∀ (r : M) (x : carrier), weight (r • x) = r * weight x
  eq_zero_of_weight : ∀ x : carrier, weight x = 0 → x = zero
  summable_of_weight : ∀ {J : Type} [Countable J] (x : J → carrier),
    CSummable (fun j => weight (x j)) → Summable x

attribute [instance] SWMod.pam SWMod.act

namespace SWMod

variable {M : Type u} [EffectMonoid M]

instance : CoeSort (SWMod M) (Type u) := ⟨SWMod.carrier⟩

theorem weight_zero (X : SWMod M) : X.weight zero = 0 := by
  have := X.weight_sumsTo (Empty.elim : Empty → X.carrier) zero (sumsTo_of_isEmpty _)
  exact this.unique (isCSum_of_isEmpty _)

theorem smul_zero (X : SWMod M) (r : M) : r • (zero : X.carrier) = zero := by
  have := X.smul_right r (Empty.elim : Empty → X.carrier) zero (sumsTo_of_isEmpty _)
  exact this.unique (sumsTo_of_isEmpty _)

/-- **SIG 30** (main.tex:891): a morphism of `sWMod[M]`: a σ-additive,
action-preserving, **weight-decreasing** map. -/
@[ext]
structure Hom (X Y : SWMod M) : Type u where
  toFun : X.carrier → Y.carrier
  sigma : ∀ {J : Type} [Countable J] (x : J → X.carrier) (s : X.carrier),
    SumsTo x s → SumsTo (fun j => toFun (x j)) (toFun s)
  map_smul : ∀ (r : M) (x : X.carrier), toFun (r • x) = r • toFun x
  weight_le : ∀ x : X.carrier, Y.weight (toFun x) ≼ X.weight x

/-- **SIG 30** (main.tex:891, Definition): the category `sWMod[M]`. -/
instance : Category (SWMod M) where
  Hom := Hom
  id X := ⟨id, fun _ _ h => h, fun _ _ => rfl, fun _ => pcm_preorder_refl _⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun x s h => g.sigma _ _ (f.sigma x s h),
    fun r x => by simp [f.map_smul, g.map_smul],
    fun x => pcm_preorder_trans (g.weight_le _) (f.weight_le x)⟩

@[simp] theorem comp_toFun {X Y Z : SWMod M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {X Y : SWMod M} {f g : X ⟶ Y} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

theorem Hom.map_zero {X Y : SWMod M} (f : X ⟶ Y) : f.toFun zero = zero := by
  have := f.sigma (Empty.elim : Empty → X.carrier) zero (sumsTo_of_isEmpty _)
  exact this.unique (sumsTo_of_isEmpty _)

/-- The unit object: `M` itself, with its canonical sums, `r · s = rs` and
`|s| = s`. -/
noncomputable def unit (M : Type u) [EffectMonoid M] (hM : IsSigmaEffectMonoid M) : SWMod M :=
  @SWMod.mk M _ M (canonicalSigmaPAM hM.1) ⟨fun r s => r * s⟩ id
    (fun x => EffectMonoid.one_mul x) (fun r s x => EffectMonoid.mul_assoc r s x)
    (fun x J _ r s h => (canonical_sumsTo_iff hM.1 _ _).2 (hM.2.2 x J r s h))
    (fun r J _ x s h => (canonical_sumsTo_iff hM.1 _ _).2
      (hM.2.1 r J x s ((canonical_sumsTo_iff hM.1 _ _).1 h)))
    (fun x s h => (canonical_sumsTo_iff hM.1 x s).1 h)
    (fun _ _ => rfl)
    (fun _ h => h.trans (@zero_eq_of_extends M _ (canonicalSigmaPAM hM.1)
      (canonicalSigmaPAM_extends hM.1)).symm)
    (fun _ h => h)

/-- The carrier of the unit object is `M`, with its effect monoid structure. -/
instance unitEffectMonoid (hM : IsSigmaEffectMonoid M) : EffectMonoid (unit M hM).carrier :=
  inferInstanceAs (EffectMonoid M)

/-! ### Countable coproducts (SIG 33, 68) -/

section Coprod

variable [hM : Fact (IsSigmaEffectMonoid M)] {Λ : Type} [Countable Λ] (X : Λ → SWMod M)

/-- The carrier of `∐ X_λ`: tuples with summable weights. -/
def CoprodCarrier : Type u :=
  {x : ∀ l, (X l).carrier // CSummable (fun l => (X l).weight (x l))}

/-- The weight `⋁_λ |x_λ|` of a tuple. -/
noncomputable def coprodWeight (x : CoprodCarrier X) : M := (exists_isCSum hM.out.1 x.2).choose

theorem coprodWeight_spec (x : CoprodCarrier X) :
    IsCSum (fun l => (X l).weight (x.1 l)) (coprodWeight X x) :=
  (exists_isCSum hM.out.1 x.2).choose_spec

/-- Pointwise sums of tuples exist (and are tuples) iff the weights are
summable. -/
theorem coprod_psum_iff {J : Type} [Countable J] (f : J → CoprodCarrier X) :
    (∃ g : CoprodCarrier X, ∀ l, SumsTo (fun j => (f j).1 l) (g.1 l)) ↔
      CSummable (fun j => coprodWeight X (f j)) := by
  let _ : SigmaPAM M := canonicalSigmaPAM hM.out.1
  have hc := fun {I : Type} [Countable I] (x : I → M) (s : M) =>
    (canonical_sumsTo_iff hM.out.1 x s)
  let w : J × Λ → M := fun q => (X q.2).weight ((f q.1).1 q.2)
  constructor
  · rintro ⟨g, hg⟩
    have hcol : ∀ l, SumsTo (fun j => w (j, l)) ((X l).weight (g.1 l)) :=
      fun l => (hc _ _).2 ((X l).weight_sumsTo _ _ (hg l))
    have hw : SumsTo w (coprodWeight X g) :=
      (sumsTo_prod_iff' w _).2 ⟨_, hcol, (hc _ _).2 (coprodWeight_spec X g)⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff w _).1 hw
    have : t = fun j => coprodWeight X (f j) :=
      funext fun j => (ht j).unique ((hc _ _).2 (coprodWeight_spec X (f j)))
    rw [this] at hts
    exact ((hc _ _).1 hts).1
  · intro h
    obtain ⟨σ, hσ⟩ := exists_isCSum hM.out.1 h
    have hw : SumsTo w σ := (sumsTo_prod_iff w σ).2
      ⟨_, fun j => (hc _ _).2 (coprodWeight_spec X (f j)), (hc _ _).2 hσ⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff' w σ).1 hw
    have hs : ∀ l, Summable (fun j => (f j).1 l) := fun l =>
      (X l).summable_of_weight _ ((hc _ _).1 (ht l)).1
    let s : ∀ l, (X l).carrier := fun l => sum _ (hs l)
    have hts' : t = fun l => (X l).weight (s l) := funext fun l =>
      (ht l).unique ((hc _ _).2 ((X l).weight_sumsTo _ _ (sumsTo_sum (hs l))))
    rw [hts'] at hts
    exact ⟨⟨s, ((hc _ _).1 hts).1⟩, fun l => sumsTo_sum (hs l)⟩

theorem coprodData : PointwiseData (fun (x : CoprodCarrier X) (l : Λ) => x.1 l) where
  inj x y h := Subtype.ext h
  nonempty := ⟨⟨fun _ => zero, fun F => ⟨0, by
    have e : (fun l => (X l).weight zero) = fun _ => (0 : M) := funext fun l => weight_zero _
    rw [e]; exact finSum_const_zero F⟩⟩⟩
  sub f P := by
    rintro ⟨g, hg⟩
    have hw := (coprod_psum_iff X f).1 ⟨g, hg⟩
    exact (coprod_psum_iff X _).2 (hw.comp ⟨Subtype.val, Subtype.val_injective⟩)
  lim f h := by
    refine (coprod_psum_iff X f).2 fun F => ?_
    obtain ⟨t, ht⟩ := ((coprod_psum_iff X _).1 (h F)) Finset.univ
    exact ⟨t, (finSum_univ_iff (fun j => coprodWeight X (f j)) F t).1 ht⟩

noncomputable instance coprodPAM : SigmaPAM (CoprodCarrier X) := pointwiseSigmaPAM (coprodData X)

theorem coprod_sumsTo_iff {J : Type} [Countable J] (f : J → CoprodCarrier X) (g : CoprodCarrier X) :
    SumsTo f g ↔ ∀ l, SumsTo (fun j => (f j).1 l) (g.1 l) :=
  pointwise_sumsTo_iff (coprodData X) f g

theorem coprod_zero_apply (l : Λ) : (zero : CoprodCarrier X).1 l = zero :=
  ((coprod_sumsTo_iff X (Empty.elim : Empty → CoprodCarrier X) zero).1
    (sumsTo_of_isEmpty _) l).unique (sumsTo_of_isEmpty _)

theorem csummable_smul (r : M) (x : CoprodCarrier X) :
    CSummable (fun l => (X l).weight (r • x.1 l)) := by
  have h := hM.out.2.1 r Λ _ _ (coprodWeight_spec X x)
  have e : (fun l => (X l).weight (r • x.1 l)) = fun l => r * (X l).weight (x.1 l) :=
    funext fun l => (X l).weight_smul r _
  rw [e]; exact h.1

/-- **SIG 33** (`prop:wmod-effectus`, main.tex:964) / **SIG 65**: the
coproduct `∐ X_λ = {(x_λ) ∈ ∏ X_λ | (|x_λ|)_λ summable in M}`, with pointwise
operations and weight `⋁_λ |x_λ|`. -/
noncomputable def coprod : SWMod M where
  carrier := CoprodCarrier X
  act := ⟨fun r x => ⟨fun l => r • x.1 l, csummable_smul X r x⟩⟩
  weight := coprodWeight X
  one_smul x := Subtype.ext (funext fun l => (X l).one_smul _)
  mul_smul r s x := Subtype.ext (funext fun l => (X l).mul_smul _ _ _)
  smul_left x J _ r s h := (coprod_sumsTo_iff X _ _).2 fun l => (X l).smul_left (x.1 l) r s h
  smul_right r J _ x s h := (coprod_sumsTo_iff X _ _).2 fun l =>
    (X l).smul_right r _ _ ((coprod_sumsTo_iff X _ _).1 h l)
  weight_sumsTo {J} _ x s h := by
    let _ : SigmaPAM M := canonicalSigmaPAM hM.out.1
    have hp := (coprod_sumsTo_iff X _ _).1 h
    let w : J × Λ → M := fun q => (X q.2).weight ((x q.1).1 q.2)
    have hw : SumsTo w (coprodWeight X s) := (sumsTo_prod_iff' w _).2
      ⟨_, fun l => (canonical_sumsTo_iff hM.out.1 _ _).2 ((X l).weight_sumsTo _ _ (hp l)),
        (canonical_sumsTo_iff hM.out.1 _ _).2 (coprodWeight_spec X s)⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff w _).1 hw
    have : t = fun j => coprodWeight X (x j) := funext fun j =>
      (ht j).unique ((canonical_sumsTo_iff hM.out.1 _ _).2 (coprodWeight_spec X (x j)))
    rw [this] at hts
    exact (canonical_sumsTo_iff hM.out.1 _ _).1 hts
  weight_smul r x := by
    have h := hM.out.2.1 r Λ _ _ (coprodWeight_spec X x)
    refine (coprodWeight_spec X _).unique ?_
    have e : (fun l => (X l).weight (r • x.1 l)) = fun l => r * (X l).weight (x.1 l) :=
      funext fun l => (X l).weight_smul r _
    exact e ▸ h
  eq_zero_of_weight x h := by
    apply (coprodData X).inj
    funext l
    show x.1 l = (zero : CoprodCarrier X).1 l
    rw [coprod_zero_apply]
    refine (X l).eq_zero_of_weight _ (eq_zero_of_le_zero ?_)
    rw [← h]
    exact (coprodWeight_spec X x).finSum_le (finSum_singleton _ l)
  summable_of_weight x h := (coprod_psum_iff X x).2 h

open Classical in
/-- The tuple with `a` at `λ` and `0` elsewhere. -/
noncomputable def incFun (l : Λ) (a : (X l).carrier) : ∀ k, (X k).carrier :=
  Function.update (fun _ => zero) l a

theorem incFun_self (l : Λ) (a : (X l).carrier) : incFun X l a l = a := by
  classical
  unfold incFun; convert Function.update_self l a (fun k => (zero : (X k).carrier))

theorem incFun_ne {l k : Λ} (h : k ≠ l) (a : (X l).carrier) : incFun X l a k = zero := by
  classical
  unfold incFun; convert Function.update_of_ne h a (fun k => (zero : (X k).carrier))

theorem incFun_weights (l : Λ) (a : (X l).carrier) :
    IsCSum (fun k => (X k).weight (incFun X l a k)) ((X l).weight a) := by
  let _ : SigmaPAM M := canonicalSigmaPAM hM.out.1
  have hz : (zero : M) = 0 :=
    @zero_eq_of_extends M _ (canonicalSigmaPAM hM.out.1) (canonicalSigmaPAM_extends hM.out.1)
  have := sumsTo_single (fun k => (X k).weight (incFun X l a k)) l (fun k hk => by
    rw [incFun_ne X hk, weight_zero, hz])
  rw [incFun_self] at this
  exact (canonical_sumsTo_iff hM.out.1 _ _).1 this

/-- The coprojection `κ_λ : X_λ → ∐ X`. -/
noncomputable def inc (l : Λ) : X l ⟶ coprod X where
  toFun a := ⟨incFun X l a, (incFun_weights X l a).1⟩
  sigma {J} _ x s h := by
    refine (coprod_sumsTo_iff X _ _).2 fun k => ?_
    show SumsTo (fun j => incFun X l (x j) k) (incFun X l s k)
    by_cases hk : k = l
    · subst hk
      rw [incFun_self]
      exact (sumsTo_congr fun j => (incFun_self X k (x j)).symm).1 h
    · rw [incFun_ne X hk]
      exact (sumsTo_congr fun j => (incFun_ne X hk (x j)).symm).1 (sumsTo_zero_family J)
  map_smul r a := by
    apply (coprodData X).inj
    funext k
    show incFun X l (r • a) k = r • incFun X l a k
    by_cases hk : k = l
    · subst hk; rw [incFun_self, incFun_self]
    · rw [incFun_ne X hk, incFun_ne X hk, smul_zero]
  weight_le a := by
    have h := (coprodWeight_spec X ⟨incFun X l a, (incFun_weights X l a).1⟩).unique
      (incFun_weights X l a)
    exact Eq.subst (motive := fun z => z ≼ (X l).weight a) h.symm (pcm_preorder_refl _)

variable {X} {Y : SWMod M}

theorem desc_summable (f : ∀ l, X l ⟶ Y) (t : CoprodCarrier X) :
    Summable (fun l => (f l).toFun (t.1 l)) :=
  Y.summable_of_weight _ (CSummable.of_le t.2 fun l => (f l).weight_le _)

/-- The cotuple `[f_λ] : ∐ X → Y`, `t ↦ ⋁_λ f_λ(t_λ)`. -/
noncomputable def desc (f : ∀ l, X l ⟶ Y) : coprod X ⟶ Y where
  toFun t := sum _ (desc_summable f t)
  sigma {J} _ x s h := by
    have hp := (coprod_sumsTo_iff X _ _).1 h
    let w : J × Λ → Y.carrier := fun q => (f q.2).toFun ((x q.1).1 q.2)
    have hw : SumsTo w (sum _ (desc_summable f s)) := (sumsTo_prod_iff' w _).2
      ⟨_, fun l => (f l).sigma _ _ (hp l), sumsTo_sum _⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff w _).1 hw
    have : t = fun j => sum _ (desc_summable f (x j)) :=
      funext fun j => (ht j).unique (sumsTo_sum _)
    rw [this] at hts
    exact hts
  map_smul r t := by
    have h := Y.smul_right r _ _ (sumsTo_sum (desc_summable f t))
    refine (sumsTo_sum (desc_summable f (r • t))).unique ((sumsTo_congr fun l => ?_).1 h)
    exact ((f l).map_smul r (t.1 l)).symm
  weight_le t := (Y.weight_sumsTo _ _ (sumsTo_sum (desc_summable f t))).mono
    (coprodWeight_spec X t) fun l => (f l).weight_le _

theorem inc_desc (f : ∀ l, X l ⟶ Y) (l : Λ) : inc X l ≫ desc f = f l := by
  refine hom_ext fun a => ?_
  show sum _ (desc_summable f ⟨incFun X l a, _⟩) = (f l).toFun a
  have h := sumsTo_single (fun k => (f k).toFun (incFun X l a k)) l (fun k hk => by
    rw [incFun_ne X hk, Hom.map_zero])
  rw [incFun_self] at h
  exact (sumsTo_sum _).unique h

theorem sumsTo_inc (t : CoprodCarrier X) :
    SumsTo (fun l => (inc X l).toFun (t.1 l)) t := by
  refine (coprod_sumsTo_iff X _ _).2 fun k => ?_
  show SumsTo (fun l => incFun X l (t.1 l) k) (t.1 k)
  have h := sumsTo_single (fun l => incFun X l (t.1 l) k) k (fun l hl => incFun_ne X (Ne.symm hl) _)
  rwa [incFun_self] at h

theorem desc_unique (f : ∀ l, X l ⟶ Y) (m : coprod X ⟶ Y) (hm : ∀ l, inc X l ≫ m = f l) :
    m = desc f := by
  refine hom_ext fun t => ?_
  have h := m.sigma _ _ (sumsTo_inc t)
  refine h.unique ((sumsTo_congr fun l => ?_).2 (sumsTo_sum (desc_summable f t)))
  rw [← hm l]; rfl

/-- The coproduct cofan. -/
noncomputable def coprodCofan : Cofan X := Cofan.mk (coprod X) (inc X)

noncomputable def coprodIsColimit : IsColimit (coprodCofan (X := X)) :=
  Cofan.IsColimit.mk _ (fun s => desc s.inj) (fun s l => inc_desc s.inj l)
    (fun s m hm => desc_unique s.inj m hm)

end Coprod

/-! ### Hom-sets and their sums (SIG 68 (iv)) -/

section Homs

variable [hM : Fact (IsSigmaEffectMonoid M)] {Λ : Type} [Countable Λ]

theorem isCSum_iff_finSum_univ {E : Type u} [EffectAlgebra E] {J : Type} [Fintype J]
    (x : J → E) (s : E) : IsCSum x s ↔ FinSum x Finset.univ s := by
  refine ⟨fun h => ?_, isCSum_of_finSum_univ⟩
  obtain ⟨t, ht⟩ := h.1 Finset.univ
  rwa [h.unique (isCSum_of_finSum_univ ht)]

/-- The zero map. -/
noncomputable def zeroHom (X Y : SWMod M) : X ⟶ Y where
  toFun _ := zero
  sigma {J} _ _ _ _ := sumsTo_zero_family J
  map_smul r _ := (smul_zero Y r).symm
  weight_le _ := by rw [weight_zero]; exact pcm_zero_le _

/-- The core of SIG 68 (iv): a family of maps whose weights at each `x` sum to
at most `|x|` has pointwise sums, which are again morphisms. -/
theorem exists_pointwise_sum {X Y : SWMod M} {J : Type} [Countable J] (f : J → (X ⟶ Y))
    (h : ∀ x, ∃ w, IsCSum (fun j => Y.weight ((f j).toFun x)) w ∧ w ≼ X.weight x) :
    ∃ g : X ⟶ Y, ∀ x, SumsTo (fun j => (f j).toFun x) (g.toFun x) := by
  have hs : ∀ x, Summable (fun j => (f j).toFun x) := fun x =>
    Y.summable_of_weight _ (h x).choose_spec.1.1
  let G : X.carrier → Y.carrier := fun x => sum _ (hs x)
  have hG : ∀ x, SumsTo (fun j => (f j).toFun x) (G x) := fun x => sumsTo_sum (hs x)
  refine ⟨⟨G, fun {I} _ x s hx => ?_, fun r x => ?_, fun x => ?_⟩, hG⟩
  · let w : J × I → Y.carrier := fun q => (f q.1).toFun (x q.2)
    have hw : SumsTo w (G s) := (sumsTo_prod_iff w _).2 ⟨_, fun j => (f j).sigma _ _ hx, hG s⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff' w _).1 hw
    have : t = fun i => G (x i) := funext fun i => (ht i).unique (hG (x i))
    rwa [this] at hts
  · have h1 := Y.smul_right r _ _ (hG x)
    exact (hG _).unique ((sumsTo_congr fun j => ((f j).map_smul r x).symm).1 h1)
  · obtain ⟨w, hw, hle⟩ := h x
    rw [(Y.weight_sumsTo _ _ (hG x)).unique hw]
    exact hle

theorem homData (X Y : SWMod M) :
    PointwiseData (fun (f : X ⟶ Y) (x : X.carrier) => f.toFun x) where
  inj f g h := Hom.ext h
  nonempty := ⟨zeroHom X Y⟩
  sub f P := by
    rintro ⟨g, hg⟩
    refine exists_pointwise_sum _ fun x => ?_
    have hw := Y.weight_sumsTo _ _ (hg x)
    obtain ⟨w, hw'⟩ := exists_isCSum hM.out.1 (hw.1.comp (Function.Embedding.subtype P))
    exact ⟨w, hw', pcm_preorder_trans (hw.le_of_comp (Function.Embedding.subtype P) hw')
      (g.weight_le x)⟩
  lim := by
    intro J _ f h
    refine exists_pointwise_sum _ fun x => ?_
    have hfin : ∀ F : Finset J, ∃ t, FinSum (fun j => Y.weight ((f j).toFun x)) F t ∧
        t ≼ X.weight x := by
      intro F
      obtain ⟨g, hg⟩ := h F
      have hw := Y.weight_sumsTo _ _ (hg x)
      refine ⟨_, (finSum_univ_iff (fun j => Y.weight ((f j).toFun x)) F _).1
        ((isCSum_iff_finSum_univ _ _).1 hw), g.weight_le x⟩
    obtain ⟨w, hw⟩ := exists_isCSum hM.out.1 (fun F => (hfin F).imp fun _ h => h.1)
    refine ⟨w, hw, hw.2.2 _ ?_⟩
    rintro t ⟨F, hF⟩
    obtain ⟨t', ht', hle⟩ := hfin F
    rwa [finSum_unique hF ht']

/-- The σ-PAM of pointwise sums on `sWMod[M](X, Y)`. -/
noncomputable instance homSigmaPAM (X Y : SWMod M) : SigmaPAM (X ⟶ Y) :=
  pointwiseSigmaPAM (homData X Y)

theorem hom_sumsTo_iff {X Y : SWMod M} {J : Type} [Countable J] (f : J → (X ⟶ Y))
    (g : X ⟶ Y) : SumsTo f g ↔ ∀ x, SumsTo (fun j => (f j).toFun x) (g.toFun x) :=
  pointwise_sumsTo_iff (homData X Y) f g

/-- **SIG 65** (proof, (iv)): a countable family `f_j : X → Y` is summable
iff for each `x`, `⋁_j |f_j(x)|` is defined and at most `|x|`. -/
theorem hom_summable_iff {X Y : SWMod M} {J : Type} [Countable J] (f : J → (X ⟶ Y)) :
    Summable f ↔ ∀ x, ∃ w, IsCSum (fun j => Y.weight ((f j).toFun x)) w ∧ w ≼ X.weight x := by
  constructor
  · rintro ⟨g, hg⟩ x
    exact ⟨_, Y.weight_sumsTo _ _ (hg x), g.weight_le x⟩
  · intro h
    exact exists_pointwise_sum f h

theorem hom_zero_eq (X Y : SWMod M) : (0 : X ⟶ Y) = zeroHom X Y := by
  refine hom_ext fun x => ?_
  have h := (hom_sumsTo_iff (Empty.elim : Empty → (X ⟶ Y)) _).1 (sumsTo_of_isEmpty _) x
  exact h.unique (sumsTo_of_isEmpty _)

/-- The projection `▷_j : ∐ X → X_j`, `t ↦ t_j`. -/
noncomputable def coprodProj (X : Λ → SWMod M) (l : Λ) : coprod X ⟶ X l where
  toFun t := t.1 l
  sigma _ _ h := (coprod_sumsTo_iff X _ _).1 h l
  map_smul _ _ := rfl
  weight_le t := (coprodWeight_spec X t).finSum_le (finSum_singleton _ l)

theorem inc_coprodProj_self (X : Λ → SWMod M) (l : Λ) : inc X l ≫ coprodProj X l = 𝟙 _ :=
  hom_ext fun a => incFun_self X l a

theorem inc_coprodProj_ne (X : Λ → SWMod M) {l k : Λ} (h : l ≠ k) :
    inc X l ≫ coprodProj X k = zeroHom _ _ :=
  hom_ext fun a => incFun_ne X (Ne.symm h) a

theorem iso_weight {X Y : SWMod M} (e : X ≅ Y) (x : X.carrier) :
    Y.weight (e.hom.toFun x) = X.weight x := by
  refine eabasics_le_antisymm (e.hom.weight_le x) ?_
  have h := e.inv.weight_le (e.hom.toFun x)
  have e1 : e.inv.toFun (e.hom.toFun x) = x := congrArg (fun g => Hom.toFun g x) e.hom_inv_id
  rwa [e1] at h

end Homs

instance hasCoproductsOfShape [Fact (IsSigmaEffectMonoid M)] (Λ : Type) [Countable Λ] :
    HasCoproductsOfShape Λ (SWMod M) :=
  ⟨fun F => by
    have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
      HasColimit.mk ⟨_, coprodIsColimit (X := F.obj ∘ Discrete.mk)⟩
    exact hasColimit_of_iso Discrete.natIsoFunctor⟩

instance [Fact (IsSigmaEffectMonoid M)] : HasCountableCoproducts (SWMod M) :=
  ⟨fun _ _ => inferInstance⟩

theorem ominus_congr {E : Type u} [EffectAlgebra E] {a a' b b' : E} (hb : b = b') (ha : a = a')
    (h : a ≼ b) (h' : a' ≼ b') : ominus b a h = ominus b' a' h' := by
  subst hb; subst ha; rfl

theorem ominus_smul {N : Type u} [EffectMonoid N] (r b a : N) (h : a ≼ b) (h' : r * a ≼ r * b) :
    ominus (r * b) (r * a) h' = r * ominus b a h := by
  obtain ⟨hp, e⟩ := isDiff_ominus h
  obtain ⟨hp', e'⟩ := emon_mul_ovee r hp
  exact isDiff_unique (isDiff_ominus h') ⟨hp', e'.symm.trans (congrArg (r * ·) e)⟩

/-! ### `sWMod[M]` is a σ-effectus (SIG 33, 68) -/

section Effectus

variable [hM : Fact (IsSigmaEffectMonoid M)]

/-- The chosen coproduct of `sWMod[M]` is the explicit one. -/
noncomputable def coprodIsoC {Λ : Type} [Countable Λ] (X : Λ → SWMod M) : ∐ X ≅ coprod X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (coprodIsColimit (X := X))

theorem ι_coprodIsoC {Λ : Type} [Countable Λ] (X : Λ → SWMod M) (l : Λ) :
    Sigma.ι X l ≫ (coprodIsoC X).hom = inc X l :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk l)

theorem pproj_eq' {Λ : Type} [Countable Λ] (X : Λ → SWMod M) (l : Λ) :
    pproj X l = (coprodIsoC X).hom ≫ coprodProj X l := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, ι_coprodIsoC]
  by_cases hk : k = l
  · subst hk; rw [ι_pproj_self, inc_coprodProj_self]
  · rw [ι_pproj_ne _ hk, inc_coprodProj_ne X hk, hom_zero_eq]

theorem coprod_inl_weight (B : SWMod M) (y : B.carrier) :
    (B ⨿ B).weight ((coprod.inl : B ⟶ B ⨿ B).toFun y) = B.weight y := by
  let t : ColimitCocone (pair B B) := ⟨coprodCofan (X := pairFunction B B), coprodIsColimit⟩
  have h := colimit.isoColimitCocone_ι_hom t ⟨WalkingPair.left⟩
  have h1 := iso_weight (colimit.isoColimitCocone t) ((coprod.inl : B ⟶ B ⨿ B).toFun y)
  have h2 : (colimit.isoColimitCocone t).hom.toFun ((coprod.inl : B ⟶ B ⨿ B).toFun y) =
      (inc (pairFunction B B) WalkingPair.left).toFun y := congrArg (fun g => Hom.toFun g y) h
  have h3 := (coprodWeight_spec (pairFunction B B)
    ⟨incFun (pairFunction B B) WalkingPair.left y,
      (incFun_weights (pairFunction B B) WalkingPair.left y).1⟩).unique
    (incFun_weights (pairFunction B B) WalkingPair.left y)
  rw [← h1, h2]; exact h3

theorem coprod_inr_weight (B : SWMod M) (y : B.carrier) :
    (B ⨿ B).weight ((coprod.inr : B ⟶ B ⨿ B).toFun y) = B.weight y := by
  let t : ColimitCocone (pair B B) := ⟨coprodCofan (X := pairFunction B B), coprodIsColimit⟩
  have h := colimit.isoColimitCocone_ι_hom t ⟨WalkingPair.right⟩
  have h1 := iso_weight (colimit.isoColimitCocone t) ((coprod.inr : B ⟶ B ⨿ B).toFun y)
  have h2 : (colimit.isoColimitCocone t).hom.toFun ((coprod.inr : B ⟶ B ⨿ B).toFun y) =
      (inc (pairFunction B B) WalkingPair.right).toFun y := congrArg (fun g => Hom.toFun g y) h
  have h3 := (coprodWeight_spec (pairFunction B B)
    ⟨incFun (pairFunction B B) WalkingPair.right y,
      (incFun_weights (pairFunction B B) WalkingPair.right y).1⟩).unique
    (incFun_weights (pairFunction B B) WalkingPair.right y)
  rw [← h1, h2]; exact h3

/-- **SIG 65** (proof, (i)–(iv)): `sWMod[M]` is a σ-PAC. -/
instance sigmaPAC : SigmaPAC (SWMod M) where
  comp_sigmaBiadditive X Y Z := by
    refine ⟨fun g => isSigmaAdditive_of_sumsTo fun x s hs => ?_,
      fun f => isSigmaAdditive_of_sumsTo fun x s hs => ?_⟩
    · rw [hom_sumsTo_iff] at hs ⊢
      exact fun z => g.sigma _ _ (hs z)
    · rw [hom_sumsTo_iff] at hs ⊢
      exact fun z => hs (f.toFun z)
  compatible_sum {J} _ {A B} f := by
    rintro ⟨h, hh⟩
    rw [hom_summable_iff]
    intro x
    let H := h ≫ (coprodIsoC (fun _ : J => B)).hom
    have e : ∀ j, (f j).toFun x = (H.toFun x).1 j := by
      intro j; rw [← hh j, pproj_eq', ← Category.assoc]; rfl
    refine ⟨coprodWeight _ (H.toFun x), ?_, H.weight_le x⟩
    have := coprodWeight_spec (fun _ : J => B) (H.toFun x)
    exact (funext fun j => congrArg B.weight (e j)) ▸ this
  untying {A B f g} hfg := by
    rw [hom_summable_iff] at hfg ⊢
    intro x
    obtain ⟨w, hw, hle⟩ := hfg x
    refine ⟨w, ?_, hle⟩
    have e : (fun j => (B ⨿ B).weight ((![f ≫ coprod.inl, g ≫ coprod.inr] j).toFun x)) =
        fun j => B.weight ((![f, g] j).toFun x) := by
      funext j; fin_cases j
      · exact coprod_inl_weight B (f.toFun x)
      · exact coprod_inr_weight B (g.toFun x)
    rw [e]; exact hw

/-- The truth map `1_X = |·| : X → M`. -/
noncomputable def oneHom (X : SWMod M) : X ⟶ unit M hM.out where
  toFun := X.weight
  sigma x s h := (canonical_sumsTo_iff hM.out.1 _ _).2 (X.weight_sumsTo x s h)
  map_smul r x := X.weight_smul r x
  weight_le _ := pcm_preorder_refl _

theorem unit_sumsTo_iff {J : Type} [Countable J] (x : J → M) (s : M) :
    @SumsTo (unit M hM.out).carrier (unit M hM.out).pam J _ x s ↔ IsCSum x s :=
  canonical_sumsTo_iff hM.out.1 x s

/-- The orthosupplement `p^⊥ : x ↦ |x| ⊖ p(x)`. -/
noncomputable def orthHom {X : SWMod M} (p : X ⟶ unit M hM.out) : X ⟶ unit M hM.out where
  toFun x := ominus (E := M) (X.weight x) (p.toFun x) (p.weight_le x)
  sigma {J} _ x s h := by
    let _ : SigmaPAM M := canonicalSigmaPAM hM.out.1
    have hext := canonicalSigmaPAM_extends (E := M) hM.out.1
    let D : J → M := fun j => ominus (E := M) (X.weight (x j)) (p.toFun (x j)) (p.weight_le _)
    let w : J × Fin 2 → M := fun q => ![p.toFun (x q.1), D q.1] q.2
    have hrow : ∀ j, SumsTo (fun i => w (j, i)) (X.weight (x j)) := by
      intro j
      obtain ⟨hp, e⟩ := isDiff_ominus (E := M) (p.weight_le (x j))
      exact (sumsTo_congr (by intro i; fin_cases i <;> rfl)).1 ((hext _ _ _).1 ⟨hp, e⟩)
    have hw : SumsTo w (X.weight s) := (sumsTo_prod_iff w _).2
      ⟨_, hrow, (canonical_sumsTo_iff hM.out.1 _ _).2 (X.weight_sumsTo _ _ h)⟩
    obtain ⟨t, ht, hts⟩ := (sumsTo_prod_iff' w _).1 hw
    have h0 : t 0 = p.toFun s := (ht 0).unique (p.sigma _ _ h)
    have hts' : SumsTo ![p.toFun s, t 1] (X.weight s) := by
      refine (sumsTo_congr fun i => ?_).1 hts
      fin_cases i
      · exact h0
      · rfl
    obtain ⟨hp, e⟩ := (hext _ _ _).2 hts'
    have hd : t 1 = ominus (E := M) (X.weight s) (p.toFun s) (p.weight_le s) :=
      isDiff_unique ⟨hp, e⟩ (isDiff_ominus (E := M) _)
    rw [← hd]
    exact ht 1
  map_smul r x := by
    let pv : X.carrier → M := fun x => p.toFun x
    have h1 : pv (r • x) = r * pv x := p.map_smul r x
    have hle : r * pv x ≼ r * X.weight x := emon_mul_mono_right r (p.weight_le x)
    calc ominus (E := M) (X.weight (r • x)) (pv (r • x)) (p.weight_le _)
        = ominus (E := M) (r * X.weight x) (r * pv x) hle :=
          ominus_congr (X.weight_smul r x) h1 _ _
      _ = r * ominus (E := M) (X.weight x) (pv x) (p.weight_le x) :=
          ominus_smul r _ _ _ hle
  weight_le x := exc_dposet_D2 (isDiff_ominus (E := M) _)

theorem unit_zero : (zero : (unit M hM.out).carrier) = (0 : M) :=
  @zero_eq_of_extends M _ (canonicalSigmaPAM hM.out.1) (canonicalSigmaPAM_extends hM.out.1)

theorem hom_perp_iff' {X : SWMod M} (p q : X ⟶ unit M hM.out) :
    Perp p q ↔ ∀ x, ∃ w, IsCSum (E := M) ![p.toFun x, q.toFun x] w ∧ w ≼ X.weight x := by
  show SigmaPAM.Summable ![p, q] ↔ _
  rw [hom_summable_iff]
  refine forall_congr' fun x => exists_congr fun w => and_congr_left fun _ => ?_
  exact iff_of_eq (congrArg (fun y => IsCSum y w) (funext fun j => by fin_cases j <;> rfl))

theorem pair_apply {X : SWMod M} {p q : X ⟶ unit M hM.out} (h : Perp p q) (x : X.carrier) :
    IsCSum (E := M) ![p.toFun x, q.toFun x] ((ovee p q h).toFun x) := by
  have := (hom_sumsTo_iff _ _).1 (sumsTo_sum (show SigmaPAM.Summable ![p, q] from h)) x
  have h2 := (canonical_sumsTo_iff hM.out.1 _ _).1 this
  exact (congrArg (fun y => IsCSum y ((ovee p q h).toFun x))
    (funext fun j => by fin_cases j <;> rfl)).mp h2

/-- **SIG 33** (`prop:wmod-effectus`, main.tex:964), σ-case, = **SIG 65**
(`prop:sWMod-sigma-effectus`, main.tex:2328): for a σ-effect monoid `M`,
`sWMod[M]` is a σ-effectus with unit object `M`, truth maps the weights, and
countable coproducts the tuples with summable weights (`coprodIsColimit`). -/
noncomputable instance sigmaEffectus : SigmaEffectus (SWMod M) where
  I := unit M hM.out
  one X := oneHom X
  orth p := orthHom p
  perp_orth {X} p := (hom_perp_iff' _ _).2 fun x =>
    ⟨X.weight x, (isCSum_pair_iff (E := M) (p.toFun x) ((orthHom p).toFun x) (X.weight x)).2
      (isDiff_ominus (E := M) (p.weight_le x)), pcm_preorder_refl _⟩
  ovee_orth {X} p := by
    refine hom_ext fun x => ?_
    have hd : IsCSum (E := M) ![p.toFun x, (orthHom p).toFun x] (X.weight x) :=
      (isCSum_pair_iff (E := M) (p.toFun x) ((orthHom p).toFun x) (X.weight x)).2
        (isDiff_ominus (E := M) (p.weight_le x))
    have h := pair_apply ((hom_perp_iff' _ _).2 fun x =>
      ⟨X.weight x, (isCSum_pair_iff (E := M) (p.toFun x) ((orthHom p).toFun x) (X.weight x)).2
        (isDiff_ominus (E := M) (p.weight_le x)), pcm_preorder_refl _⟩) x
    exact h.unique hd
  orth_unique {X p q} h e := hom_ext fun x => by
    have h1 := pair_apply h x
    rw [e] at h1
    exact isDiff_unique (E := M) ((isCSum_pair_iff _ _ _).1 h1) (isDiff_ominus (E := M) _)
  eq_zero_of_perp_one {X p} h := by
    rw [hom_zero_eq]
    refine hom_ext fun x => ?_
    obtain ⟨w, hw, hle⟩ := (hom_perp_iff' _ _).1 h x
    obtain ⟨hp, e⟩ := (isCSum_pair_iff (E := M) _ _ _).1 hw
    let px : M := p.toFun x
    have hp' : Perp px (X.weight x) := hp
    have e' : ovee px (X.weight x) hp' = w := e
    have h2 : ovee (X.weight x) px (PCM.perp_comm hp') ≼
        ovee (X.weight x) 0 (PCM.perp_zero _) :=
      calc ovee (X.weight x) px (PCM.perp_comm hp') = ovee px (X.weight x) hp' :=
            (PCM.ovee_comm hp').symm
        _ = w := e'
        _ ≼ X.weight x := hle
        _ = ovee (X.weight x) 0 (PCM.perp_zero _) := (PCM.ovee_zero _ _).symm
    have h3 : px = 0 := eq_zero_of_le_zero (le_of_ovee_le_ovee _ _ h2)
    exact h3.trans unit_zero.symm
  eq_zero_of_one_zero {X Y f} h := by
    rw [hom_zero_eq] at h ⊢
    refine hom_ext fun x => Y.eq_zero_of_weight _ ?_
    have := congrArg (fun g : X ⟶ unit M hM.out => g.toFun x) h
    exact this.trans unit_zero
  perp_of_one_perp {X Y f g} h := by
    show SigmaPAM.Summable ![f, g]
    have h' : SigmaPAM.Summable ![f ≫ oneHom Y, g ≫ oneHom Y] := h
    rw [hom_summable_iff] at h' ⊢
    intro x
    obtain ⟨w, hw, hle⟩ := h' x
    refine ⟨w, ?_, hle⟩
    exact (congrArg (fun y => IsCSum y w) (funext fun j => by fin_cases j <;> rfl)).mp hw

end Effectus

end SWMod

/-! ## SIG 31, 34, 70: the substate functor -/

/-- The opposite effect monoid `Mᵒᵖ`, as a type. -/
def MOp (M : Type u) : Type u := M

instance {M : Type u} [EffectMonoid M] : EffectMonoid (MOp M) := opEffectMonoid M

theorem mop_isSigmaEffectMonoid {M : Type u} [EffectMonoid M] (hM : IsSigmaEffectMonoid M) :
    IsSigmaEffectMonoid (MOp M) :=
  ⟨hM.1, fun a => hM.2.2 a, fun b => hM.2.1 b⟩

section SubstateFunctor

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

theorem predSumsTo_iff {X : C} {J : Type} [Countable J] (x : J → Pred X) (s : Pred X) :
    SumsTo x s ↔ IsCSum x s := (pred_sigmaEffectAlgebra X).2 J x s

theorem pred_summable_of_csummable {X : C} {J : Type} [Countable J] {x : J → Pred X}
    (h : CSummable x) : SigmaPAM.Summable x :=
  ((predSumsTo_iff x _).2 (exists_isCSum (pred_sigmaEffectAlgebra X).1 h).choose_spec).summable

/-- **SIG 31** (main.tex:910, Example): the substates `sSt(A) = C(I, A)` of a
σ-effectus with scalars `M` form a σ-weight `Mᵒᵖ`-module, with action
`r · ω = ω ∘ r` and weight `|ω| = 1 ∘ ω`. -/
noncomputable def sStObj (A : C) : SWMod (MOp (Scal C)) where
  carrier := Substate A
  act := ⟨fun r ω => (show Scal C from r) ≫ ω⟩
  weight ω := ω ≫ truth A
  one_smul ω := by
    show truth (effObj C) ≫ ω = ω
    rw [truth_effObj_eq_id, Category.id_comp]
  mul_smul r s ω := Category.assoc (show Scal C from r) (show Scal C from s) ω
  smul_left ω J _ r s h := comp_sumsTo_left ω ((predSumsTo_iff _ _).2 h)
  smul_right r J _ x s h := comp_sumsTo_right (show Scal C from r) h
  weight_sumsTo {J} _ x s h := (predSumsTo_iff _ _).1 (comp_sumsTo_left (truth A) h)
  weight_smul r ω := Category.assoc (show Scal C from r) ω (truth A)
  eq_zero_of_weight ω h := EffectusPartialForm.eq_zero_of_one_zero h
  summable_of_weight x h := summable_of_summable_truth x (pred_summable_of_csummable h)

/-- **SIG 31** (main.tex:919): states are the substates of weight `1`. -/
theorem isTotal_iff_weight (A : C) (ω : Substate A) :
    IsTotal ω ↔ (sStObj A).weight ω = 1 := Iff.rfl

/-- `sSt f = f ∘ (-)`. -/
noncomputable def sStMap {A B : C} (f : A ⟶ B) : sStObj A ⟶ sStObj B where
  toFun ω := ω ≫ f
  sigma x s h := comp_sumsTo_left f h
  map_smul r ω := Category.assoc _ ω f
  weight_le := fun (ω : effObj C ⟶ A) => by
    show (ω ≫ f) ≫ truth B ≼ ω ≫ truth A
    rw [Category.assoc]
    exact le_comp_left' (ea_le_one (E := A ⟶ effObj C) (f ≫ truth B)) ω

/-- **SIG 34/70**: the functor `sSt : C → sWMod[Mᵒᵖ]`, `A ↦ C(I, A)`. -/
noncomputable def sStFunctor : C ⥤ SWMod (MOp (Scal C)) where
  obj A := sStObj A
  map f := sStMap f
  map_id _ := SWMod.hom_ext fun ω => Category.comp_id ω
  map_comp f g := SWMod.hom_ext fun ω => (Category.assoc ω f g).symm

/-- **SIG 37** (`prop:separation-faithful`, main.tex:1051), second half: a
σ-effectus is substate-separated iff `sSt` is faithful. -/
theorem substateSeparated_iff_faithful :
    SubstateSeparated C ↔ (sStFunctor (C := C)).Faithful := by
  constructor
  · intro h
    exact ⟨fun {X Y f g} hfg => h f g fun ω =>
      congrArg (fun k : sStObj X ⟶ sStObj Y => k.toFun ω) hfg⟩
  · intro hF A B f g hfg
    exact hF.map_injective (SWMod.hom_ext fun ω => hfg ω)

end SubstateFunctor

section SubstateMorphism

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

instance sStFact : Fact (IsSigmaEffectMonoid (MOp (Scal C))) :=
  ⟨mop_isSigmaEffectMonoid scal_isSigmaEffectMonoid⟩

theorem sSt_weight_decomp {Λ : Type} [Countable Λ] (A : Λ → C) (ω : Substate (∐ A)) :
    IsCSum (fun l => (ω ≫ pproj A l) ≫ truth (A l)) (ω ≫ truth (∐ A)) := by
  have h := comp_sumsTo_left (truth (∐ A)) (sumsTo_decomp A ω)
  refine (predSumsTo_iff _ _).1 ((sumsTo_congr fun l => ?_).1 h)
  rw [Category.assoc, ι_truth]

section Inv

variable {Λ : Type} [Countable Λ] (A : Λ → C)

/-- The inverse of `ω ↦ (▷_λ ∘ ω)_λ`, from SIG 69. -/
noncomputable def sStInv (t : (SWMod.coprod (fun l => sStObj (A l))).carrier) : Substate (∐ A) :=
  ((decomposition_bijection A (effObj C)).2 (fun l => t.1 l)
    (pred_summable_of_csummable t.2)).exists.choose

theorem sStInv_spec (t : (SWMod.coprod (fun l => sStObj (A l))).carrier) (l : Λ) :
    sStInv A t ≫ pproj A l = t.1 l :=
  ((decomposition_bijection A (effObj C)).2 (fun l => t.1 l)
    (pred_summable_of_csummable t.2)).exists.choose_spec l

theorem sStInv_unique (t : (SWMod.coprod (fun l => sStObj (A l))).carrier) (ω : Substate (∐ A))
    (h : ∀ l, ω ≫ pproj A l = t.1 l) : ω = sStInv A t :=
  ((decomposition_bijection A (effObj C)).2 (fun l => t.1 l)
    (pred_summable_of_csummable t.2)).unique h (sStInv_spec A t)

theorem sStInv_weight (t : (SWMod.coprod (fun l => sStObj (A l))).carrier) :
    SWMod.coprodWeight (fun l => sStObj (A l)) t = sStInv A t ≫ truth (∐ A) := by
  have h := sSt_weight_decomp A (sStInv A t)
  have e : (fun l => (sStInv A t ≫ pproj A l) ≫ truth (A l)) =
      fun l => (sStObj (A l)).weight (t.1 l) :=
    funext fun l => by rw [sStInv_spec]; rfl
  rw [e] at h
  exact (SWMod.coprodWeight_spec _ t).unique h

end Inv

/-- `sSt(∐ A_λ) ≅ ∐ sSt(A_λ)` (the bijection of SIG 70, via SIG 69). -/
noncomputable def sStCoprodIso {Λ : Type} [Countable Λ] (A : Λ → C) :
    sStObj (∐ A) ≅ SWMod.coprod (fun l => sStObj (A l)) where
  hom :=
    { toFun := fun ω => ⟨fun l => ω ≫ pproj A l, (sSt_weight_decomp A ω).1⟩
      sigma := fun x s h => (SWMod.coprod_sumsTo_iff _ _ _).2 fun l =>
        comp_sumsTo_left (pproj A l) h
      map_smul := fun r ω => Subtype.ext (funext fun l => Category.assoc _ ω _)
      weight_le := fun ω => by
        have h := (SWMod.coprodWeight_spec (fun l => sStObj (A l))
          ⟨fun l => ω ≫ pproj A l, (sSt_weight_decomp A ω).1⟩).unique (sSt_weight_decomp A ω)
        exact Eq.subst (motive := fun z => z ≼ ω ≫ truth (∐ A)) h.symm (pcm_preorder_refl _) }
  inv :=
    { toFun := sStInv A
      sigma := fun {J} _ x s h => by
        have hw := (SWMod.coprod (fun l => sStObj (A l))).weight_sumsTo x s h
        have hw' : CSummable (fun j => sStInv A (x j) ≫ truth (∐ A)) := by
          have e : (fun j => sStInv A (x j) ≫ truth (∐ A)) =
              fun j => (SWMod.coprod (fun l => sStObj (A l))).weight (x j) :=
            funext fun j => (sStInv_weight A (x j)).symm
          rw [e]; exact hw.1
        have hs := summable_of_summable_truth _ (pred_summable_of_csummable hw')
        obtain ⟨Ω, hΩ⟩ : ∃ Ω, SumsTo (fun j => sStInv A (x j)) Ω := ⟨_, sumsTo_sum hs⟩
        have hΩs : Ω = sStInv A s := sStInv_unique A s Ω fun l => by
          have h1 := comp_sumsTo_left (pproj A l) hΩ
          have h2 := (SWMod.coprod_sumsTo_iff _ _ _).1 h l
          exact h1.unique ((sumsTo_congr fun j => (sStInv_spec A (x j) l).symm).1 h2)
        rw [← hΩs]; exact hΩ
      map_smul := fun r t => (sStInv_unique A (r • t) _ fun l => by
          show ((show Scal C from r) ≫ sStInv A t) ≫ pproj A l = (show Scal C from r) ≫ t.1 l
          rw [Category.assoc, sStInv_spec]).symm
      weight_le := fun t => by
        have h := sStInv_weight A t
        exact Eq.subst (motive := fun z => sStInv A t ≫ truth (∐ A) ≼ z) h.symm
          (pcm_preorder_refl _) }
  hom_inv_id := SWMod.hom_ext fun ω => (sStInv_unique A _ ω fun l => rfl).symm
  inv_hom_id := SWMod.hom_ext fun t => Subtype.ext (funext fun l => sStInv_spec A t l)

/-- The comparison `∐ sSt(A_λ) → sSt(∐ A_λ)` of `sWMod[Mᵒᵖ]`, as an iso. -/
noncomputable def sStSigmaIso {Λ : Type} [Countable Λ] (A : Λ → C) :
    ∐ (fun l => (sStFunctor (C := C)).obj (A l)) ≅ (sStFunctor (C := C)).obj (∐ A) :=
  SWMod.coprodIsoC (fun l => sStObj (A l)) ≪≫ (sStCoprodIso A).symm

theorem sStFunctor_sigmaComparison {Λ : Type} [Countable Λ] (A : Λ → C) :
    sigmaComparison sStFunctor A = (sStSigmaIso A).hom := by
  refine Sigma.hom_ext _ _ fun l => ?_
  rw [ι_comp_sigmaComparison]
  have h1 : Sigma.ι (fun l => sStObj (A l)) l ≫ (SWMod.coprodIsoC _).hom =
      SWMod.inc (fun l => sStObj (A l)) l := SWMod.ι_coprodIsoC _ l
  have h3 := h1 =≫ (sStCoprodIso A).inv
  rw [Category.assoc] at h3
  have h2 : (sStFunctor (C := C)).map (Sigma.ι A l) =
      SWMod.inc (fun l => sStObj (A l)) l ≫ (sStCoprodIso A).inv := by
    refine SWMod.hom_ext fun (ω : effObj C ⟶ A l) => ?_
    refine sStInv_unique A _ (ω ≫ Sigma.ι A l) fun k => ?_
    show (ω ≫ Sigma.ι A l) ≫ pproj A k = SWMod.incFun (fun l => sStObj (A l)) l ω k
    by_cases hk : k = l
    · subst hk
      rw [Category.assoc, ι_pproj_self, Category.comp_id]
      exact (SWMod.incFun_self (fun l => sStObj (A l)) k ω).symm
    · rw [Category.assoc, ι_pproj_ne _ (Ne.symm hk), FinPAC.comp_zero]
      exact (SWMod.incFun_ne (fun l => sStObj (A l)) hk ω).symm
  exact h2.trans h3.symm

instance sStFunctor_preservesColimitsOfShape (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J) (sStFunctor (C := C)) := by
  constructor
  intro K
  have key : ∀ A : J → C, PreservesColimit (Discrete.functor A) (sStFunctor (C := C)) := by
    intro A
    have : IsIso (sigmaComparison (sStFunctor (C := C)) A) := by
      rw [sStFunctor_sigmaComparison]; infer_instance
    exact PreservesCoproduct.of_iso_comparison _ _
  have := key (K.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- `sSt I` is the unit object `Mᵒᵖ`. -/
noncomputable def unitSStIso :
    SWMod.unit (MOp (Scal C)) (sStFact (C := C)).out ≅ sStObj (effObj C) where
  hom :=
    { toFun := fun (s : Scal C) => s
      sigma := fun x s h => (predSumsTo_iff _ _).2
        ((canonical_sumsTo_iff (sStFact (C := C)).out.1 _ _).1 h)
      map_smul := fun _ _ => rfl
      weight_le := fun (s : Scal C) => by
        show s ≫ truth (effObj C) ≼ s
        rw [truth_effObj_eq_id, Category.comp_id]; exact pcm_preorder_refl _ }
  inv :=
    { toFun := fun (s : Scal C) => s
      sigma := fun x s h => (canonical_sumsTo_iff (sStFact (C := C)).out.1 _ _).2
        ((predSumsTo_iff _ _).1 h)
      map_smul := fun _ _ => rfl
      weight_le := fun (s : Scal C) => by
        show s ≼ s ≫ truth (effObj C)
        rw [truth_effObj_eq_id, Category.comp_id]; exact pcm_preorder_refl _ }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **SIG 34** (main.tex:987, Proposition), σ-case, = **SIG 67**
(`prop:sst-functor-sigma-effectus`, main.tex:2806): for a σ-effectus `C` with
scalars `M`, `A ↦ sSt(A) = C(I, A)` is a morphism of σ-effectuses
`C → sWMod[Mᵒᵖ]`: it preserves the unit (`sSt(I) = Mᵒᵖ`), the truth maps
(`sSt(1_A) = |·|`), and countable coproducts (`sSt(∐ A) ≅ ∐ sSt(A_λ)`, by
SIG 69). -/
noncomputable def sStMorphism : SigmaEffectusMorphism C (SWMod (MOp (Scal C))) where
  F := sStFunctor
  preserves := fun _ _ => inferInstance
  u := unitSStIso
  map_truth _ := SWMod.hom_ext fun _ => rfl

end SubstateMorphism

end Papers.SIG
