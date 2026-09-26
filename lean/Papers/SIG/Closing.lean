/-
Papers/SIG/Closing.lean

Cleanup pass (2026-09-26): SIG rows graded `weaker` closed by new
declarations, without touching the committed statements.

* **SIG 32** (`ex:weight-module-bool`), finite half: `WMod[{0,1}] ≅ pSet` is
  an *isomorphism* of categories, as printed — `WMod.toPointed` is full,
  faithful and bijective on objects (`wMod_bool_iso_pointed`), because the
  whole structure of a weight `{0,1}`-module is determined by its carrier and
  its zero (`WMod.ofPointed_toPointed`).  (Finite.lean proved an
  equivalence.)
* **SIG 23** (`ex:CX`): the scalars of `W*ᵒᵖ` are `[0,1]`
  (`sig23_wstar_scalars`, for the print's `W*` of normal positive subunital
  maps, through `pvnSigmaEffectus`); the preceding unnumbered claim "any
  ω-complete effect monoid is a σ-effect monoid" (from OAP 43 and SIG 20,
  `isSigmaEffectMonoid_of_omegaComplete`); and the `C(X)` clause:
  `[0,1]_{C(X)}` is ω-complete iff `X` is basically disconnected, and then a
  σ-effect monoid (`sig23_CX`, both directions of the cited Gillman–Jerison
  fact from `Papers.OAP`: `oap16_basically` and
  `basicallyDisconnected_of_relSup`).
-/
import Papers.SIG.Examples
import Papers.SIG.Finite
import Papers.OAP.FloorCeiling
import Papers.OAP.OUS

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff Opposite

namespace Papers.SIG

universe u

/-! ## SIG 32 (finite half): an isomorphism of categories -/

/-- Two PCM structures on one type with the same zero, orthogonality and
sums are equal. -/
theorem pcm_ext' {T : Type u} {p q : PCM T}
    (h0 : @Zero.zero T p.toZero = @Zero.zero T q.toZero)
    (hperp : ∀ x y, @Perp T p x y ↔ @Perp T q x y)
    (hovee : ∀ x y (hp : @Perp T p x y) (hq : @Perp T q x y), @ovee T p x y hp = @ovee T q x y hq) :
    p = q := by
  rcases p with @⟨⟨z⟩, P, o, _, _, _, _, _, _, _⟩
  rcases q with @⟨⟨z'⟩, P', o', _, _, _, _, _, _, _⟩
  have e0 : z = z' := h0
  have eP : P = P' := funext fun x => funext fun y => propext (hperp x y)
  subst e0 eP
  have eo : o = o' := funext fun x => funext fun y => funext fun h => hovee x y h h
  subst eo
  rfl

namespace WMod

/-- Weight modules with the same carrier, PCM, action and weight are
equal. -/
theorem ext_of_heq {M : Type u} [EffectMonoid M] {X Y : WMod M} (hc : X.carrier = Y.carrier)
    (hp : HEq X.pcm Y.pcm) (ha : HEq X.act Y.act) (hw : HEq X.weight Y.weight) : X = Y := by
  cases X; cases Y
  cases hc; cases hp; cases ha; cases hw
  rfl

open Classical in
/-- **SIG 32** (main.tex:958): a weight `{0,1}`-module is the weight module
of its pointed set `(X, 0)` — its PCM, action and weight are determined by the
carrier and `0` (`bool_perp_iff`, `bool_weight_eq_true_iff`). -/
theorem ofPointed_toPointed (X : WMod Bool) : ofPointed (toPointed.obj X) = X := by
  have hperp : ∀ x y : X.carrier, (x = 0 ∨ y = 0) ↔ @Perp X.carrier X.pcm x y :=
    fun x y => (bool_perp_iff X x y).symm
  have hovee : ∀ (x y : X.carrier) (hq : @Perp X.carrier X.pcm x y),
      (if x = (0 : X.carrier) then y else x) = ovee x y hq := by
    intro x y hq
    by_cases hx : x = 0
    · subst hx
      rw [ite_eq_left_iff.2 fun h => absurd rfl h]
      exact (PCM.zero_ovee y).symm
    · rw [ite_eq_right_iff.2 fun h => absurd h hx]
      have hy : y = 0 := ((bool_perp_iff X x y).1 hq).resolve_left hx
      subst hy
      exact (PCM.ovee_zero x hq).symm
  have hact : (⟨fun r x => if r then x else 0⟩ : SMul Bool X.carrier) = X.act := by
    have : X.act = ⟨fun r x => r • x⟩ := rfl
    rw [this]
    congr 1
    funext r x
    cases r
    · exact (X.zero_smul x).symm
    · exact (X.one_smul x).symm
  have hw : (fun x : X.carrier => decide (x ≠ 0)) = X.weight := by
    funext x
    by_cases hx : x = 0
    · subst hx
      rw [X.weight_zero]
      simp; rfl
    · rw [decide_eq_true hx]
      exact ((bool_weight_eq_true_iff X x).2 hx).symm
  refine ext_of_heq rfl (heq_of_eq ?_) (heq_of_eq hact) (heq_of_eq hw)
  exact pcm_ext' (T := X.carrier) rfl hperp fun x y _ hq => hovee x y hq

theorem toPointed_ofPointed (P : Pointed.{0}) : toPointed.obj (ofPointed P) = P := by
  cases P; rfl

end WMod

/-- **SIG 32** (`ex:weight-module-bool`, main.tex:947, Example), finite half
as printed: weight `{0,1}`-modules are precisely pointed sets,
`WMod[{0,1}] ≅ pSet`: the functor `X ↦ (X, 0)` is full, faithful and
bijective on objects (an isomorphism of categories).  With
`sWMod_bool_iso_pointed` (the σ half, Pfn.lean) this gives the printed
`WMod[{0,1}] ≅ sWMod[{0,1}] ≅ pSet`. -/
theorem wMod_bool_iso_pointed :
    WMod.toPointed.Full ∧ WMod.toPointed.Faithful ∧ Function.Bijective WMod.toPointed.obj :=
  ⟨inferInstance, inferInstance,
    ⟨fun X Y h => (WMod.ofPointed_toPointed X).symm.trans
      ((congrArg WMod.ofPointed h).trans (WMod.ofPointed_toPointed Y)),
    fun P => ⟨WMod.ofPointed P, WMod.toPointed_ofPointed P⟩⟩⟩

/-! ## SIG 23: ω-complete effect monoids, `[0,1]_{C(X)}`, the scalars of `W*ᵒᵖ` -/

section OmegaSigma

variable {M : Type u} [EffectMonoid M]

theorem isSupOf_iff_isLUB (S : Set M) (s : M) :
    IsSupOf S s ↔ @IsLUB M (Papers.OAP.eaPartialOrder M).toPreorder.toLE S s :=
  ⟨fun h => ⟨fun t ht => h.1 t ht, fun c hc => h.2 c hc⟩,
    fun h => ⟨fun _ ht => h.1 ht, fun _ hc => h.2 hc⟩⟩

/-- **SIG** (main.tex:700, the remark before SIG 22, citing OAP 43 with
SIG 20): an ω-complete effect monoid is a σ-effect monoid — σ-biadditivity of
the product follows from biadditivity. -/
theorem isSigmaEffectMonoid_of_omegaComplete (hω : OmegaComplete M) : IsSigmaEffectMonoid M := by
  have hO : Papers.OAP.OmegaComplete M := omegaComplete_iff_oap.1 hω
  have hcont : ∀ b b' : M, IsOmegaContinuous (fun a : M => b * a * b') := by
    intro b b' a _ s hs
    rw [isSupOf_iff_isLUB] at hs ⊢
    have h := Papers.OAP.oap43_1 (Set.range_nonempty a) hs b b'
    rw [← Set.range_comp] at h
    exact h
  have haddL : ∀ a : M, IsAdditive (fun b : M => a * b) := fun a =>
    ⟨(exc_emonzero a).1, fun h => by
      obtain ⟨h', e⟩ := emon_mul_ovee a h
      exact ⟨h', e.symm⟩⟩
  have haddR : ∀ b : M, IsAdditive (fun a : M => a * b) := fun b =>
    ⟨(exc_emonzero b).2, fun h => by
      obtain ⟨h', e⟩ := emon_ovee_mul b h
      exact ⟨h', e.symm⟩⟩
  refine ⟨hω, fun a => (sigmaAdditive_iff_omegaContinuous (haddL a)).2 ?_,
    fun b => (sigmaAdditive_iff_omegaContinuous (haddR b)).2 ?_⟩
  · have := hcont a 1
    simp only [EffectMonoid.mul_one] at this
    exact this
  · have := hcont 1 b
    simp only [EffectMonoid.one_mul] at this
    exact this

end OmegaSigma

section CX

variable (X : Type u) [TopologicalSpace X]

/-- In `[0,1]_{C(X)}` (the tree's `continuousUnitIntervalEffectMonoid`) the
algebraic order is the pointwise order. -/
theorem cx_le_iff (a b : Set.Icc (0 : C(X, ℝ)) 1) :
    @PCM.le _ (continuousUnitIntervalEffectMonoid X).toPCM a b ↔ (a : C(X, ℝ)) ≤ b := by
  letI := continuousUnitIntervalEffectMonoid X
  constructor
  · rintro ⟨c, _, rfl⟩
    show (a : C(X, ℝ)) ≤ a + c
    exact le_add_of_nonneg_right c.2.1
  · intro h
    refine ⟨⟨(b : C(X, ℝ)) - a, sub_nonneg.mpr h, le_trans (sub_le_self _ a.2.1) b.2.2⟩, ?_, ?_⟩
    · show (a : C(X, ℝ)) + ((b : C(X, ℝ)) - a) ≤ 1
      rw [add_sub_cancel]; exact b.2.2
    · exact Subtype.ext (add_sub_cancel _ _)

theorem cx_isSupOf_iff (S : Set (Set.Icc (0 : C(X, ℝ)) 1)) (s : Set.Icc (0 : C(X, ℝ)) 1) :
    @IsSupOf _ (continuousUnitIntervalEffectMonoid X).toEffectAlgebra S s ↔ IsLUB S s := by
  letI := continuousUnitIntervalEffectMonoid X
  simp only [IsSupOf, cx_le_iff]
  rfl

/-- **SIG 23** (`ex:CX`, main.tex:732, Example), the `C(X)` clause: for a
compact Hausdorff space `X`, the effect monoid `[0,1]_{C(X)}` is ω-complete
iff `X` is basically disconnected (every cozero set has open closure), and
then it is a σ-effect monoid.  The print cites Gillman–Jerison 1H, 3N.5; both
directions are proved in `Papers.OAP` (`oap16_basically`,
`basicallyDisconnected_of_relSup`). -/
theorem sig23_CX [CompactSpace X] [T2Space X] :
    letI := continuousUnitIntervalEffectMonoid X
    (OmegaComplete (Set.Icc (0 : C(X, ℝ)) 1) ↔ Theses.B.Eff.BasicallyDisconnected X) ∧
      (OmegaComplete (Set.Icc (0 : C(X, ℝ)) 1) → IsSigmaEffectMonoid (Set.Icc (0 : C(X, ℝ)) 1)) := by
  letI := continuousUnitIntervalEffectMonoid X
  refine ⟨⟨fun hω => ?_, fun hX => ?_⟩, isSigmaEffectMonoid_of_omegaComplete⟩
  · -- ω-complete ⟹ basically disconnected
    have h := Papers.OAP.basicallyDisconnected_of_relSup (X := X) fun h hmono hb => by
      let a : ℕ → Set.Icc (0 : C(X, ℝ)) 1 := fun n => ⟨h n, (hb n).1, (hb n).2⟩
      obtain ⟨s, hs⟩ := hω a fun n => (cx_le_iff X _ _).2 (hmono (Nat.le_succ n))
      rw [cx_isSupOf_iff] at hs
      refine ⟨s, s.2.1, s.2.2, ?_, fun w hw0 hw1 hw => ?_⟩
      · rintro _ ⟨n, rfl⟩
        exact hs.1 ⟨n, rfl⟩
      · exact hs.2 (show (⟨w, hw0, hw1⟩ : Set.Icc (0 : C(X, ℝ)) 1) ∈ upperBounds (Set.range a)
          from by rintro _ ⟨n, rfl⟩; exact hw _ ⟨n, rfl⟩)
    exact h
  · -- basically disconnected ⟹ ω-complete
    have hO := Papers.OAP.oap16_basically X hX
    intro a ha
    let _ := orderIntervalEffectAlgebra C(X, ℝ) 1 zero_le_one
    obtain ⟨s, hs⟩ := @Papers.OAP.OmegaComplete.exists_isLUB _ _ hO a
      (@monotone_nat_of_le_succ _ (Papers.OAP.eaPartialOrder _).toPreorder a fun n =>
        (Papers.OAP.oap3_le_iff C(X, ℝ) 1 zero_le_one _ _).2 ((cx_le_iff X _ _).1 (ha n)))
    refine ⟨s, (cx_isSupOf_iff X _ _).2 ⟨fun t ht => ?_, fun c hc => ?_⟩⟩
    · exact (Papers.OAP.oap3_le_iff C(X, ℝ) 1 zero_le_one _ _).1 (hs.1 ht)
    · exact (Papers.OAP.oap3_le_iff C(X, ℝ) 1 zero_le_one _ _).1
        (hs.2 fun t ht => (Papers.OAP.oap3_le_iff C(X, ℝ) 1 zero_le_one _ _).2 (hc ht))

end CX

section WStarScalars

open scoped ComplexOrder

/-- The value `p(1) ∈ ℂ` of a scalar `p : ℂ ⟶ ℂ` of `W*ᵒᵖ`. -/
noncomputable def wv (p : psuI.{u} ⟶ psuI.{u}) : ℂ := @ULift.down.{u, 0} ℂ (ap p.unop 1)

theorem wv_apply (p : psuI.{u} ⟶ psuI.{u}) (z : ULift.{u} ℂ) :
    @ULift.down.{u, 0} ℂ (ap p.unop z) = z.down * wv p := by
  have hz : z = z.down • (1 : ULift.{u} ℂ) := Theses.A.VN.CU.down_injective (by simp)
  have key : ap p.unop z = z.down • ap p.unop 1 := by
    conv_lhs => rw [hz]
    exact (ap p.unop).map_smul _ _
  unfold wv
  rw [key]
  rfl

theorem wv_ext {p q : psuI.{u} ⟶ psuI.{u}} (h : wv p = wv q) : p = q :=
  Quiver.Hom.unop_inj (NPSUMap.scal_ext (Theses.A.VN.CU.down_injective h))

theorem wv_nonneg (p : psuI.{u} ⟶ psuI.{u}) : (0 : ℂ) ≤ wv p := (ap p.unop).one_nonneg

theorem wv_le_one (p : psuI.{u} ⟶ psuI.{u}) : wv p ≤ 1 := (ap p.unop).subunital

theorem wv_im (p : psuI.{u} ⟶ psuI.{u}) : (wv p).im = 0 :=
  ((Complex.le_def.1 (wv_nonneg p)).2).symm

theorem wv_re_nonneg (p : psuI.{u} ⟶ psuI.{u}) : 0 ≤ (wv p).re := (Complex.le_def.1 (wv_nonneg p)).1

theorem wv_re_le_one (p : psuI.{u} ⟶ psuI.{u}) : (wv p).re ≤ 1 := (Complex.le_def.1 (wv_le_one p)).1

theorem wv_ofReal (p : psuI.{u} ⟶ psuI.{u}) : (((wv p).re : ℝ) : ℂ) = wv p :=
  Complex.ext (by simp) (by simp [wv_im])

theorem wv_perp_iff (p q : psuI.{u} ⟶ psuI.{u}) : Perp p q ↔ wv p + wv q ≤ 1 :=
  pvn_perp_iff p q

theorem wv_ovee {p q : psuI.{u} ⟶ psuI.{u}} (h : Perp p q) : wv (ovee p q h) = wv p + wv q :=
  congrArg (@ULift.down.{u, 0} ℂ) (pvn_ovee_apply h 1)

theorem wv_comp (m l : psuI.{u} ⟶ psuI.{u}) : wv (m ≫ l) = wv l * wv m := by
  unfold wv
  rw [show ap (m ≫ l).unop 1 = ap m.unop (ap l.unop 1) from psuop_comp_apply m l 1]
  exact wv_apply m _

theorem wv_one : wv (psuOne psuI.{u}) = 1 := congrArg (@ULift.down.{u, 0} ℂ) (psuOne_one psuI.{u})

/-- The scalar `λ` of `W*ᵒᵖ`, the map `z ↦ λz`. -/
noncomputable def wScalOf (t : unitInterval) : psuI.{u} ⟶ psuI.{u} :=
  pvnPredOf (X := psuI.{u}) ⟨(⟨(t : ℂ)⟩ : ULift.{u} ℂ),
    show (0 : ℂ) ≤ (t : ℂ) from Complex.zero_le_real.2 t.2.1,
    show (t : ℂ) ≤ 1 from by exact_mod_cast t.2.2⟩

theorem wv_wScalOf (t : unitInterval) : wv (wScalOf.{u} t) = t := by
  have h := pvnPredOf_one (X := psuI.{u}) ⟨(⟨(t : ℂ)⟩ : ULift.{u} ℂ),
    show (0 : ℂ) ≤ (t : ℂ) from Complex.zero_le_real.2 t.2.1,
    show (t : ℂ) ≤ 1 from by exact_mod_cast t.2.2⟩
  exact congrArg (@ULift.down.{u, 0} ℂ) h

/-- **SIG 23** (`ex:CX`, main.tex:719, Example), first sentence: the scalars
`W*ᵒᵖ(ℂ, ℂ)` of the σ-effectus `W*ᵒᵖ` (SIG 15, `pvnSigmaEffectus`: von
Neumann algebras and normal positive subunital maps) are the real unit
interval `[0,1]` with its usual multiplication and partial addition: `p ↦ p(1)`
is an isomorphism of effect monoids.  (Via `pvn_pred_effects`: the
predicates on `ℂ` are the effects of `ℂ`, which are real.) -/
theorem sig23_wstar_scalars : EMIso (Scal WStarPSU.{u}ᵒᵖ) unitInterval := by
  let φ : EffectMonoidHom (Scal WStarPSU.{u}ᵒᵖ) unitInterval :=
    { toFun := fun p => ⟨(wv p).re, wv_re_nonneg p, wv_re_le_one p⟩
      perp_map := fun {p q} h => by
        have h' := (wv_perp_iff p q).1 h
        show (wv p).re + (wv q).re ≤ 1
        have := (Complex.le_def.1 h').1
        simpa using this
      ovee_map := fun {p q} h => Subtype.ext (by
        show (wv (ovee p q h)).re = (wv p).re + (wv q).re
        rw [wv_ovee h, Complex.add_re])
      map_one := Subtype.ext (by
        show (wv (psuOne psuI.{u})).re = 1
        rw [wv_one, Complex.one_re])
      map_mul := fun l m => Subtype.ext (by
        show (wv (m ≫ l)).re = (wv l).re * (wv m).re
        rw [wv_comp, Complex.mul_re, wv_im, wv_im]
        ring) }
  let ψ : EffectMonoidHom unitInterval (Scal WStarPSU.{u}ᵒᵖ) :=
    { toFun := wScalOf.{u}
      perp_map := fun {t s} h => by
        refine (wv_perp_iff _ _).2 ?_
        rw [wv_wScalOf, wv_wScalOf]
        have h' : (t : ℝ) + s ≤ 1 := h
        exact_mod_cast h'
      ovee_map := fun {t s} h => wv_ext (by
        rw [wv_ovee, wv_wScalOf, wv_wScalOf, wv_wScalOf]
        rw [show ((ovee t s h : unitInterval) : ℝ) = (t : ℝ) + s from rfl]
        push_cast; rfl)
      map_one := wv_ext (by
        rw [wv_wScalOf]
        exact (show (((1 : unitInterval) : ℝ) : ℂ) = 1 by simp).trans wv_one.symm)
      map_mul := fun t s => wv_ext (by
        show wv (wScalOf.{u} (t * s)) = wv (wScalOf.{u} s ≫ wScalOf.{u} t)
        rw [wv_comp, wv_wScalOf, wv_wScalOf, wv_wScalOf]
        push_cast; ring) }
  refine ⟨φ, ψ, fun p => wv_ext ?_, fun t => Subtype.ext ?_⟩
  · show wv (wScalOf.{u} ⟨(wv p).re, wv_re_nonneg p, wv_re_le_one p⟩) = wv p
    rw [wv_wScalOf]
    exact wv_ofReal p
  · show (wv (wScalOf.{u} t)).re = t
    rw [wv_wScalOf, Complex.ofReal_re]

end WStarScalars

/-! ## SIG 56 in every universe

`sig56` (Convex.lean) is stated for `C : Type` with hom-sets in `Type`,
because `sBOUS` (`SBOUS : Type 1`, carriers in `Type`) and `sEMod[[0,1]]`
(`[0,1] : Type`) live in universe `0`.  Here `sBOUS` is rebuilt in every
universe `u` (`SBOUSU.{u}`, carriers in `Type u`) and shown equivalent to
`sEMod[[0,1]]` over the lifted scalars `ULift.{u} [0,1]`, which gives SIG 56
for every `C : Type u` with hom-sets in `Type u` (the universe convention of
SIG 64, `predMorphism`, on which the proof rests). -/

section ULiftEM

universe w

variable {E : Type u}

/-- The PCM `ULift E`, with the operations of `E`. -/
@[instance_reducible] def ulPCM [PCM E] : PCM (ULift.{w} E) where
  zero := ⟨0⟩
  Perp a b := Perp a.down b.down
  ovee a b h := ⟨ovee a.down b.down h⟩
  perp_comm h := PCM.perp_comm h
  ovee_comm h := congrArg ULift.up (PCM.ovee_comm h)
  perp_of_ovee_perp hab h := PCM.perp_of_ovee_perp hab h
  perp_ovee_of_ovee_perp hab h := PCM.perp_ovee_of_ovee_perp hab h
  ovee_assoc hab h := congrArg ULift.up (PCM.ovee_assoc hab h)
  zero_perp a := PCM.zero_perp a.down
  zero_ovee a := congrArg ULift.up (PCM.zero_ovee a.down)

/-- The effect algebra `ULift E`. -/
instance ulEffectAlgebra [EffectAlgebra E] : EffectAlgebra (ULift.{w} E) :=
  { ulPCM with
    one := ⟨1⟩
    orth a := ⟨orth a.down⟩
    perp_orth a := EffectAlgebra.perp_orth a.down
    ovee_orth a := congrArg ULift.up (EffectAlgebra.ovee_orth a.down)
    orth_unique h e := congrArg ULift.up (EffectAlgebra.orth_unique h (congrArg ULift.down e))
    eq_zero_of_perp_one h := congrArg ULift.up (EffectAlgebra.eq_zero_of_perp_one h) }

theorem ul_isSumOf [EffectAlgebra E] {l : List E} {s : E} (h : PCM.IsSumOf l s) :
    PCM.IsSumOf (l.map ULift.up.{w}) (ULift.up s) := by
  induction h with
  | nil => exact PCM.IsSumOf.nil
  | cons hl hp ih => exact PCM.IsSumOf.cons (s := ULift.up _) ih hp

/-- The effect monoid `ULift E`. -/
instance ulEffectMonoid [EffectMonoid E] : EffectMonoid (ULift.{w} E) :=
  { ulEffectAlgebra with
    mul a b := ⟨a.down * b.down⟩
    one_mul a := congrArg ULift.up (EffectMonoid.one_mul a.down)
    mul_one a := congrArg ULift.up (EffectMonoid.mul_one a.down)
    mul_assoc a b c := congrArg ULift.up (EffectMonoid.mul_assoc a.down b.down c.down)
    distrib hab hcd := ul_isSumOf (EffectMonoid.distrib hab hcd) }

theorem ul_le_iff [EffectAlgebra E] (a b : ULift.{w} E) : a ≼ b ↔ a.down ≼ b.down :=
  ⟨fun ⟨c, h, e⟩ => ⟨c.down, h, congrArg ULift.down e⟩,
    fun ⟨c, h, e⟩ => ⟨⟨c⟩, h, congrArg ULift.up e⟩⟩

theorem ul_isSupOf_iff [EffectAlgebra E] (S : Set (ULift.{w} E)) (s : ULift.{w} E) :
    IsSupOf S s ↔ IsSupOf (ULift.down '' S) s.down := by
  simp only [IsSupOf, ul_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rintro _ ⟨t, ht, rfl⟩; exact h1 t ht, fun c hc => h2 ⟨c⟩ fun t ht => hc _ ⟨t, ht, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun t ht => h1 _ ⟨t, ht, rfl⟩, fun c hc => h2 c.down (by rintro _ ⟨t, ht, rfl⟩; exact hc t ht)⟩

theorem ul_omegaComplete [EffectAlgebra E] (h : OmegaComplete E) : OmegaComplete (ULift.{w} E) := by
  intro a ha
  obtain ⟨s, hs⟩ := h (fun n => (a n).down) fun n => (ul_le_iff _ _).1 (ha n)
  refine ⟨⟨s⟩, (ul_isSupOf_iff _ _).2 ?_⟩
  rw [← Set.range_comp]
  exact hs

theorem ul_down_isSigmaAdditiveC [EffectAlgebra E] (h : OmegaComplete E) :
    IsSigmaAdditiveC (ULift.down.{w} : ULift.{w} E → E) := by
  refine (sigmaAdditive_iff_omegaContinuous (E := ULift.{w} E) (D := E)
    ⟨rfl, fun hp => ⟨hp, rfl⟩⟩).2 fun a _ s hs => ?_
  rw [ul_isSupOf_iff, ← Set.range_comp] at hs
  exact hs

/-- `E → ULift E` as an effect monoid map. -/
def ulUp [EffectMonoid E] : EffectMonoidHom E (ULift.{w} E) where
  toFun := ULift.up
  perp_map h := h
  ovee_map _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

/-- `ULift E → E` as an effect monoid map. -/
def ulDown [EffectMonoid E] : EffectMonoidHom (ULift.{w} E) E where
  toFun := ULift.down
  perp_map h := h
  ovee_map _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

end ULiftEM

/-- A module along an effect-monoid map, in any universes (`restrictModule`
has all three types in one universe). -/
@[instance_reducible] def restrictModuleU {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (φ : EffectMonoidHom M N) (E : Type w) [EffectAlgebra E] [EffectModule N E] :
    EffectModule M E where
  smul r x := φ.toFun r • x
  mul_smul l m a := by
    show φ.toFun (l * m) • a = φ.toFun l • φ.toFun m • a
    rw [φ.map_mul, EffectModule.mul_smul]
  smul_perp l _ _ h := EffectModule.smul_perp (φ.toFun l) h
  perp_smul {l m} h a := by
    obtain ⟨h', e⟩ := EffectModule.perp_smul (φ.perp_map h) a
    refine ⟨h', ?_⟩
    show ovee (φ.toFun l • a) (φ.toFun m • a) h' = φ.toFun (ovee l m h) • a
    rw [e, φ.ovee_map h]
  one_smul a := by
    show φ.toFun 1 • a = a
    rw [φ.map_one, EffectModule.one_smul]

theorem IsSigmaAdditiveC.compU {X : Type u} {Y : Type v} {Z : Type w} [EffectAlgebra X]
    [EffectAlgebra Y] [EffectAlgebra Z] {f : X → Y} {g : Y → Z} (hf : IsSigmaAdditiveC f)
    (hg : IsSigmaAdditiveC g) : IsSigmaAdditiveC (g ∘ f) :=
  fun J _ x s h => hg J _ _ (hf J x s h)

/-- `[0,1]` lifted to universe `u`. -/
abbrev IU : Type u := ULift.{u} unitInterval

/-- `[0,1] → ULift [0,1]`. -/
noncomputable def iuUp : EffectMonoidHom unitInterval IU.{u} := ulUp

/-- `ULift [0,1] → [0,1]`. -/
noncomputable def iuDown : EffectMonoidHom IU.{u} unitInterval := ulDown

theorem iu_isSigmaEffectMonoid : IsSigmaEffectMonoid IU.{u} :=
  isSigmaEffectMonoid_of_omegaComplete (ul_omegaComplete unitInterval_isSigmaEffectMonoid.1)

section SBOUSU

attribute [local instance] Papers.OAP.ousEA Papers.OAP.ousEMod

/-- **SIG 54** (main.tex:1539, Definition) in universe `u`: an object of
`sBOUS`, a monotone σ-complete Banach order-unit space with carrier in
`Type u` (`SBOUS` is the case `u = 0`). -/
structure SBOUSU : Type (u + 1) where
  toOVSu : OVSu.{u}
  msc : MonotoneSigmaComplete toOVSu.carrier
  banach : IsBanachOUS toOVSu.carrier

namespace SBOUSU

/-- **SIG 54** in universe `u`: the category `sBOUS` (σ-normal subunital
positive linear maps). -/
instance : Category SBOUSU.{u} where
  Hom A B := {f : A.toOVSu ⟶ B.toOVSu // SigmaNormal f.toLin}
  id A := ⟨𝟙 A.toOVSu, fun _ _ _ _ hs => by simpa using hs⟩
  comp f g := ⟨f.1 ≫ g.1, SigmaNormal.comp (f := f.1.toLin) (g := g.1.toLin)
    (fun _ _ h => f.1.mono h) f.2 g.2⟩

theorem hom_ext {A B : SBOUSU.{u}} {f g : A ⟶ B} (h : f.1 = g.1) : f = g := Subtype.ext h

end SBOUSU

/-- `[0,u]_V` as an effect `[0,1]`-module over the lifted scalars. -/
@[instance_reducible] noncomputable def ivlModU (V : Type u) [AddCommGroup V] [Module ℝ V]
    [PartialOrder V] [OrderUnitSpace V] : EffectModule IU.{u} (Ivl V) :=
  restrictModuleU iuDown (Ivl V)

/-- `[0,u]_A` of `A ∈ sBOUS`, as a σ-effect module over `ULift [0,1]`. -/
noncomputable def sbousObjU (A : SBOUSU.{u}) : SEMod IU.{u} :=
  @SEMod.mk IU.{u} _ (Ivl A.toOVSu.carrier) _ (ivlModU A.toOVSu.carrier)
    ⟨(sig72 (sig69.1 A.msc)).1, fun r => (sig72 (sig69.1 A.msc)).2.1 r.down,
      fun a => IsSigmaAdditiveC.compU (ul_down_isSigmaAdditiveC unitInterval_isSigmaEffectMonoid.1)
        ((sig72 (sig69.1 A.msc)).2.2 a)⟩

/-- **SIG 55** in universe `u`: the functor `sBOUS → sEMod[[0,1]]`,
`A ↦ [0,u]_A`. -/
noncomputable def sbousFunctorU : SBOUSU.{u} ⥤ SEMod IU.{u} where
  obj := sbousObjU
  map {A B} f := ⟨ivlRes f.1.toLin f.1.pos f.1.subunital,
    ⟨Subtype.ext (map_zero f.1.toLin), fun {x y} h => by
      refine ⟨?_, Subtype.ext (map_add f.1.toLin x.1 y.1).symm⟩
      show f.1.toLin x.1 + f.1.toLin y.1 ≤ ouUnit B.toOVSu.carrier
      rw [← map_add]
      exact (f.1.mono h).trans f.1.subunital⟩,
    fun r x => Subtype.ext (map_smul f.1.toLin ((r.down : unitInterval) : ℝ) x.1),
    (sigmaAdditive_iff_omegaContinuous ⟨Subtype.ext (map_zero f.1.toLin), fun {x y} h => by
      refine ⟨?_, Subtype.ext (map_add f.1.toLin x.1 y.1).symm⟩
      show f.1.toLin x.1 + f.1.toLin y.1 ≤ ouUnit B.toOVSu.carrier
      rw [← map_add]
      exact (f.1.mono h).trans f.1.subunital⟩).2
      ((sig70 A.msc B.msc f.1.toLin f.1.pos f.1.subunital).1 f.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance sbousFunctorU_faithful : sbousFunctorU.{u}.Faithful :=
  ⟨fun {A B} f g h => SBOUSU.hom_ext (OVSu.hom_ext fun x => linear_ext_ivl (fun a h0 h1 => by
    have := congrArg (fun k : sbousObjU A ⟶ sbousObjU B =>
      (show Ivl B.toOVSu.carrier from k.toFun ⟨a, h0, h1⟩).1) h
    exact this) x)⟩

instance sbousFunctorU_full : sbousFunctorU.{u}.Full := by
  refine ⟨fun {A B} g => ?_⟩
  let gf : Ivl A.toOVSu.carrier → Ivl B.toOVSu.carrier := g.toFun
  have hadd : IsAdditive gf := g.additive
  have hsm : ∀ (r : unitInterval) (a : Ivl A.toOVSu.carrier), gf (r • a) = r • gf a :=
    fun r a => g.map_smul ⟨r⟩ a
  have haff : IsAffineIvl (V := A.toOVSu.carrier) (W := B.toOVSu.carrier) gf :=
    isAffineIvl_of hadd hsm
  let f : A.toOVSu ⟶ B.toOVSu :=
    ⟨extLin haff, fun _ hx => extLin_nonneg haff hx, by rw [extLin_unit]; exact (gf 1).2.2⟩
  have hres : ivlRes f.toLin f.pos f.subunital = gf :=
    funext fun a => Subtype.ext (extF_ivl haff a)
  have hn : SigmaNormal f.toLin := by
    refine (sig70 A.msc B.msc _ f.pos f.subunital).2 ?_
    rw [hres]
    exact (sigmaAdditive_iff_omegaContinuous hadd).1 g.sigma
  exact ⟨⟨f, hn⟩, SEMod.hom_ext fun a => Subtype.ext (extF_ivl haff a)⟩

/-- The Gudder–Pulmannová space of a σ-effect module over `ULift [0,1]`, as an
object of `sBOUS` in universe `u`. -/
noncomputable def gpSBOUSU (E : SEMod IU.{u}) : SBOUSU.{u} :=
  letI : EffectModule unitInterval E.carrier := restrictModuleU iuUp E.carrier
  have : Papers.OAP.OmegaComplete E.carrier := omegaComplete_iff_oap.1 E.sigma.1
  have hmsc : MonotoneSigmaComplete (GP.Vec E.carrier) :=
    sig69.2 (omegaComplete_iff_oap.2 Papers.OAP.gp_omegaComplete)
  ⟨OVSu.mk (GP.Vec E.carrier), hmsc, sig71 hmsc⟩

/-- `[0,u]_{GP(E)} ≅ E` in `sEMod[ULift [0,1]]`. -/
noncomputable def gpIsoU (E : SEMod IU.{u}) : sbousFunctorU.obj (gpSBOUSU E) ≅ E :=
  letI : EffectModule unitInterval E.carrier := restrictModuleU iuUp E.carrier
  SEMod.isoOfEMod
    (EModS.isoOfEquiv (E := EModS.mk (M := IU.{u}) E.carrier)
      (F := EModS.mk (M := IU.{u}) (sbousFunctorU.obj (gpSBOUSU E)).carrier)
      (Papers.OAP.gpEquiv E.carrier)
      ⟨Subtype.ext GP.gmap_zero, fun {a b} h =>
        ⟨Papers.OAP.gmap_perp_iff.1 h, Subtype.ext (GP.gmap_ovee h).symm⟩⟩
      (fun a b h => Papers.OAP.gmap_perp_iff.2 h)
      (fun r a => Subtype.ext (GP.gmap_smul r.down a))).symm

instance sbousFunctorU_essSurj : sbousFunctorU.{u}.EssSurj :=
  ⟨fun E => ⟨gpSBOUSU E, ⟨gpIsoU E⟩⟩⟩

/-- **SIG 55** (`prop:sBOUS-equiv-sEMod`, main.tex:1551, Proposition) in
every universe: `sBOUS ≃ sEMod[[0,1]]` (with `[0,1]` lifted to `Type u`). -/
theorem sig55U : sbousFunctorU.{u}.IsEquivalence := { }

attribute [instance] sig55U

/-- `sEMod[ULift [0,1]]ᵒᵖ` with its σ-effectus structure (SIG 28/63). -/
noncomputable instance semodIU_sigmaEffectus : SigmaEffectus (SEMod IU.{u})ᵒᵖ :=
  SEMod.sigmaEffectus iu_isSigmaEffectMonoid

instance : HasCountableCoproducts SBOUSU.{u}ᵒᵖ :=
  ⟨fun _ _ => Adjunction.hasColimitsOfShape_of_equivalence sbousFunctorU.op⟩

noncomputable instance sbousUHomPAM (X Y : SBOUSU.{u}ᵒᵖ) : SigmaPAM (X ⟶ Y) :=
  SigmaPAM.ofEquiv ((Functor.FullyFaithful.ofFullyFaithful sbousFunctorU.op).homEquiv)

theorem sbousU_sumsCompatible : SumsCompatible sbousFunctorU.{u}.op :=
  fun x s => SigmaPAM.ofEquiv_sumsTo_iff _ x s

/-- The unit object of `sBOUSᵒᵖ` in universe `u`. -/
noncomputable def sbousUUnit : SBOUSU.{u}ᵒᵖ :=
  op (gpSBOUSU (SEMod.unit IU.{u} iu_isSigmaEffectMonoid))

noncomputable def sbousUUnitIso :
    sbousFunctorU.op.obj sbousUUnit.{u} ≅ SigmaEffectus.«I» (C := (SEMod IU.{u})ᵒᵖ) :=
  (gpIsoU (SEMod.unit IU.{u} iu_isSigmaEffectMonoid)).symm.op

/-- **SIG 55** (main.tex:1554) in every universe: `sBOUSᵒᵖ` is a
σ-effectus (transported along SIG 55). -/
noncomputable instance sbousU_sigmaEffectus : SigmaEffectus SBOUSU.{u}ᵒᵖ :=
  sbousU_sumsCompatible.sigmaEffectus sbousUUnit sbousUUnitIso (fun _ _ => inferInstance)

/-- `sBOUSᵒᵖ → sEMod[[0,1]]ᵒᵖ` is a morphism of σ-effectuses (universe `u`). -/
noncomputable def sbousUMorphism : SigmaEffectusMorphism SBOUSU.{u}ᵒᵖ (SEMod IU.{u})ᵒᵖ :=
  sbousU_sumsCompatible.morphism sbousUUnit sbousUUnitIso (fun _ _ => inferInstance)

end SBOUSU

section SIG56U

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- **SIG 56** (`thm:convex-effectus-embedding`, main.tex:1560, Theorem), for
a σ-effectus `C : Type u` with hom-sets in `Type u`, in every universe `u`
(`sig56` is the case `u = 0`): if `C` is predicate-separated with scalars
`C(I,I) ≅ [0,1]`, there is a faithful morphism of σ-effectuses
`F : C → sBOUSᵒᵖ` (`sBOUS` in universe `u`), with `Pred(A) ≅ [0,u]_{FA}` as
σ-effect `C(I,I)`-modules (the scalars acting on `[0,u]_{FA}` through the
isomorphism).  Proof as `sig56`: SIG 37, SIG 64 and SIG 55 (`sig55U`). -/
theorem sig56U (hsep : PredicateSeparated C) (φ : EffectMonoidHom (Scal C) unitInterval)
    (ψ : EffectMonoidHom unitInterval (Scal C)) (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a)
    (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b) :
    ∃ (F : SigmaEffectusMorphism C SBOUSU.{u}ᵒᵖ)
      (hφ : IsSigmaAdditiveC (emHomComp iuUp.{u} φ).toFun), F.F.Faithful ∧
      ∀ A : C, Nonempty (predObj A ≅ restrictObj (emHomComp iuUp.{u} φ) hφ
        (sbousObjU (F.F.obj A).unop)) := by
  let _ := SEMod.sigmaEffectus (scal_isSigmaEffectMonoid (C := C))
  let φ' : EffectMonoidHom (Scal C) IU.{u} := emHomComp iuUp φ
  let ψ' : EffectMonoidHom IU.{u} (Scal C) := emHomComp ψ iuDown
  have hψφ' : ∀ a, ψ'.toFun (φ'.toFun a) = a := hψφ
  have hφψ' : ∀ b, φ'.toFun (ψ'.toFun b) = b := fun b => congrArg ULift.up (hφψ b.down)
  have hφ : IsSigmaAdditiveC φ'.toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive φ') (emHom_isAdditive ψ') hψφ' hφψ'
  have hψ : IsSigmaAdditiveC ψ'.toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive ψ') (emHom_isAdditive φ') hφψ' hψφ'
  let B := restrictMorphism φ' hφ ψ' hψ hψφ' hφψ' (scal_isSigmaEffectMonoid (C := C))
    iu_isSigmaEffectMonoid
  let G := sigmaMorphismComp sbousUMorphism B
  have := restrictFunctor_isEquivalence φ' hφ ψ' hψ hψφ' hφψ'
  have : G.F.IsEquivalence := by
    show (sbousFunctorU.op ⋙ (restrictFunctor φ' hφ).op).IsEquivalence
    infer_instance
  have hpred : (predFunctor (C := C)).Faithful := (predicateSeparated_iff_faithful).1 hsep
  let Φ := predMorphism (C := C)
  have h : ∀ A : C, ∃ Y : SBOUSU.{u}ᵒᵖ, Nonempty (G.F.obj Y ≅ Φ.F.obj A) :=
    fun A => ⟨G.F.objPreimage (Φ.F.obj A), ⟨G.F.objObjPreimageIso _⟩⟩
  refine ⟨liftMorphism G Φ h, hφ, ?_, fun A => ?_⟩
  · have : Φ.F.Faithful := hpred
    exact liftMorphism_faithful G Φ h
  · exact ⟨((liftIso G Φ h).app A).unop⟩

end SIG56U

/-! ## SIG 60 and SIG 61 in every universe

`sig60` rests on `sBBNS ≃ sCWMod[[0,1]]` (SIG 59), built in Convex.lean at
universe `0` (`OVSt`, `CWMod`, `SBBNS`, `SCWMod : Type 1`, and `sWMod[[0,1]]`
with `[0,1] : Type`).  Below, that construction (Convex.lean, SIG 57–59 and 73:
ordered vector spaces with trace, subbases, cancellative weight modules, the
base norm, the σ-structure on the subbase) is repeated verbatim in namespace
`Papers.SIG.U` with the carriers in `Type u`, the only changes being that the
σ-weight modules are over `[0,1]` lifted to `Type u` (`IU`), through the
`[0,1]`-level views `wI`, `smulI`, `wI_sumsTo`, … below.  The generic parts
(namespace `CW`: formal multiples and differences, sums in `[0,1]`) are the
originals, already universe-polymorphic. -/

section ULiftSums

universe w

variable {E : Type u} [EffectAlgebra E]

theorem ul_isSumOf_iff {l : List (ULift.{w} E)} {s : ULift.{w} E} :
    PCM.IsSumOf l s ↔ PCM.IsSumOf (l.map ULift.down) s.down := by
  constructor
  · intro h
    induction h with
    | nil => exact PCM.IsSumOf.nil
    | cons hl hp ih => exact PCM.IsSumOf.cons ih hp
  · intro h
    have := (ul_isSumOf h : PCM.IsSumOf ((l.map ULift.down).map ULift.up.{w}) (ULift.up.{w} s.down))
    rwa [List.map_map, show (ULift.up ∘ ULift.down : ULift.{w} E → ULift.{w} E) = id from rfl,
      List.map_id] at this

theorem ul_finSum_iff {J : Type} {x : J → ULift.{w} E} {F : Finset J} {s : ULift.{w} E} :
    FinSum x F s ↔ FinSum (fun j => (x j).down) F s.down := by
  unfold FinSum
  rw [ul_isSumOf_iff, List.map_map]
  rfl

theorem ul_csummable_iff {J : Type} {x : J → ULift.{w} E} :
    CSummable x ↔ CSummable (fun j => (x j).down) :=
  ⟨fun h F => let ⟨s, hs⟩ := h F; ⟨s.down, ul_finSum_iff.1 hs⟩,
    fun h F => let ⟨s, hs⟩ := h F; ⟨⟨s⟩, ul_finSum_iff.2 hs⟩⟩

theorem ul_isCSum_iff {J : Type} {x : J → ULift.{w} E} {s : ULift.{w} E} :
    IsCSum x s ↔ IsCSum (fun j => (x j).down) s.down := by
  have hset : ULift.down '' {t | ∃ F, FinSum x F t} =
      {t | ∃ F, FinSum (fun j => (x j).down) F t} := by
    ext t
    constructor
    · rintro ⟨t, ⟨F, h⟩, rfl⟩; exact ⟨F, ul_finSum_iff.1 h⟩
    · rintro ⟨F, h⟩; exact ⟨⟨t⟩, ⟨F, ul_finSum_iff.2 h⟩, rfl⟩
  unfold IsCSum
  rw [ul_csummable_iff, ul_isSupOf_iff, hset]

end ULiftSums

section SWModIU

variable (X : SWMod IU.{u})

/-- The `[0,1]`-action of a σ-weight module over the lifted `[0,1]`. -/
instance smulI : SMul unitInterval X.carrier := ⟨fun r x => (⟨r⟩ : IU.{u}) • x⟩

/-- The weight, in `[0,1]`. -/
def wI (x : X.carrier) : unitInterval := (X.weight x).down

theorem wI_sumsTo {J : Type} [Countable J] (x : J → X.carrier) (s : X.carrier)
    (h : SigmaPAM.SumsTo x s) : IsCSum (fun j => wI X (x j)) (wI X s) :=
  ul_isCSum_iff.1 (X.weight_sumsTo x s h)

theorem summable_of_wI {J : Type} [Countable J] (x : J → X.carrier)
    (h : CSummable (fun j => wI X (x j))) : SigmaPAM.Summable x :=
  X.summable_of_weight x (ul_csummable_iff.2 h)

theorem wI_smul (r : unitInterval) (x : X.carrier) : wI X (r • x) = r * wI X x :=
  congrArg ULift.down (X.weight_smul ⟨r⟩ x)

theorem eq_zero_of_wI (x : X.carrier) (h : wI X x = 0) : x = SigmaPAM.zero :=
  X.eq_zero_of_weight x (congrArg ULift.up h)

theorem wI_zero : wI X SigmaPAM.zero = 0 := congrArg ULift.down X.weight_zero

theorem smul_left_I (x : X.carrier) {J : Type} [Countable J] (r : J → unitInterval)
    (s : unitInterval) (h : IsCSum r s) : SigmaPAM.SumsTo (fun j => r j • x) (s • x) :=
  X.smul_left x (fun j => ⟨r j⟩) ⟨s⟩ (ul_isCSum_iff.2 h)

theorem smul_right_I (r : unitInterval) {J : Type} [Countable J] (x : J → X.carrier)
    (s : X.carrier) (h : SigmaPAM.SumsTo x s) : SigmaPAM.SumsTo (fun j => r • x j) (r • s) :=
  X.smul_right ⟨r⟩ x s h

end SWModIU

namespace U

open scoped unitInterval NNReal
open SigmaPAM

set_option warn.classDefReducibility false

/-- `CW.sumsTo_pairs` for σ-PAMs in any universe (the original is for `Type`). -/
theorem sumsTo_pairsU {M : Type u} [SigmaPAM M] (f g P : ℕ → M)
    (hP : ∀ n, SigmaPAM.SumsTo ![f n, g n] (P n)) (U : M) :
    SigmaPAM.SumsTo (Sum.elim f g) U ↔ SigmaPAM.SumsTo P U := by
  have hfib : ∀ n, SigmaPAM.SumsTo
      (fun j : {j : ℕ ⊕ ℕ // Sum.elim id id j = n} => Sum.elim f g j.1) (P n) := by
    intro n
    refine (SigmaPAM.sumsTo_comp_equiv' (CW.fibEquiv n) _ ![f n, g n] ?_ (P n)).1 (hP n)
    intro i; fin_cases i <;> rfl
  rw [SigmaPAM.sumsTo_partition_iff (Sum.elim f g) (Sum.elim id id)]
  constructor
  · rintro ⟨t, ht, htU⟩
    have : t = P := funext fun n => (ht n).unique (hfib n)
    rwa [this] at htU
  · intro h; exact ⟨P, hfib, h⟩

/-! ## SIG 57: ordered vector spaces with trace, subbases, `CWMod` -/

/-- **SIG 57** (main.tex:1569, Definition): an **ordered vector space with
trace**: an ordered real vector space `V` (translation-invariant order, cone
closed under non-negative scalars) that is positively generated
(`V = V₊ - V₊`), with a linear functional `τ` (the trace) that is strictly
positive (`x > 0` implies `τ x > 0`). -/
structure OVSt : Type (u + 1) where
  carrier : Type u
  [grp : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [ord : PartialOrder carrier]
  [oam : IsOrderedAddMonoid carrier]
  [psm : PosSMulMono ℝ carrier]
  gen : ∀ x : carrier, ∃ a b : carrier, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b
  tr : carrier →ₗ[ℝ] ℝ
  tr_pos : ∀ x : carrier, 0 < x → 0 < tr x

attribute [instance] OVSt.grp OVSt.mod OVSt.ord OVSt.oam OVSt.psm

namespace OVSt

theorem tr_nonneg (V : OVSt) {x : V.carrier} (h : 0 ≤ x) : 0 ≤ V.tr x := by
  rcases h.lt_or_eq with h | h
  · exact (V.tr_pos x h).le
  · rw [← h, map_zero]

/-- **SIG 57** (main.tex:1584, Definition): a morphism of `OVSt`: a
trace-decreasing positive linear map. -/
@[ext]
structure Hom (V W : OVSt) where
  toLin : V.carrier →ₗ[ℝ] W.carrier
  pos : ∀ x, 0 ≤ x → 0 ≤ toLin x
  tr_le : ∀ x, 0 ≤ x → W.tr (toLin x) ≤ V.tr x

/-- **SIG 57** (main.tex:1587, Definition): the category `OVSt`. -/
instance : Category OVSt where
  Hom := Hom
  id V := ⟨LinearMap.id, fun _ h => h, fun _ _ => le_rfl⟩
  comp f g := ⟨g.toLin ∘ₗ f.toLin, fun x h => g.pos _ (f.pos x h),
    fun x h => (g.tr_le _ (f.pos x h)).trans (f.tr_le x h)⟩

@[simp] theorem id_toLin (V : OVSt) : (𝟙 V : Hom V V).toLin = LinearMap.id := rfl
@[simp] theorem comp_toLin {U V W : OVSt} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).toLin = g.toLin ∘ₗ f.toLin := rfl

theorem hom_ext {V W : OVSt} {f g : V ⟶ W} (h : ∀ x, f.toLin x = g.toLin x) : f = g :=
  Hom.ext (LinearMap.ext h)

end OVSt

/-- **SIG 57** (main.tex:1593, Definition, text): the **subbase**
`sBase(V) = {x ∈ V₊ | τ x ≤ 1}`, with weight `τ`. -/
abbrev SubB (V : OVSt.{u}) : Type u := {x : V.carrier // 0 ≤ x ∧ V.tr x ≤ 1}

namespace SubB

variable {V : OVSt}

theorem ext {a b : SubB V} (h : a.1 = b.1) : a = b := Subtype.ext h

theorem tr_nonneg (a : SubB V) : 0 ≤ V.tr a.1 := V.tr_nonneg a.2.1

/-- The partial sum of the subbase: `x ⊥ y` iff `τ x + τ y ≤ 1`, and then
`x ⊕ y = x + y`. -/
instance pcm : PCM (SubB V) where
  zero := ⟨0, le_rfl, by rw [map_zero]; exact zero_le_one⟩
  Perp a b := V.tr a.1 + V.tr b.1 ≤ 1
  ovee a b h := ⟨a.1 + b.1, add_nonneg a.2.1 b.2.1, by rw [map_add]; exact h⟩
  perp_comm h := by rw [add_comm]; exact h
  ovee_comm h := ext (add_comm _ _)
  perp_of_ovee_perp {a b c} _ h := by
    have h' : V.tr (a.1 + b.1) + V.tr c.1 ≤ 1 := h
    rw [map_add] at h'; linarith [tr_nonneg a]
  perp_ovee_of_ovee_perp {a b c} _ h := by
    have h' : V.tr (a.1 + b.1) + V.tr c.1 ≤ 1 := h
    show V.tr a.1 + V.tr (b.1 + c.1) ≤ 1
    rw [map_add] at h' ⊢; linarith
  ovee_assoc _ _ := ext (add_assoc _ _ _)
  zero_perp a := by show V.tr 0 + V.tr a.1 ≤ 1; rw [map_zero, zero_add]; exact a.2.2
  zero_ovee a := ext (zero_add _)

@[simp] theorem zero_val : ((0 : SubB V)).1 = 0 := rfl
theorem perp_iff {a b : SubB V} : Perp a b ↔ V.tr a.1 + V.tr b.1 ≤ 1 := Iff.rfl
@[simp] theorem ovee_val {a b : SubB V} (h : Perp a b) : (ovee a b h).1 = a.1 + b.1 := rfl

/-- The weight module structure of the subbase: `r · x = r x`, `|x| = τ x`. -/
noncomputable instance wmod : WeightMod (SubB V) where
  smul r x := ⟨(r : ℝ) • x.1, smul_nonneg r.2.1 x.2.1, by
    rw [map_smul, smul_eq_mul]
    exact le_trans (mul_le_of_le_one_left (tr_nonneg x) r.2.2) x.2.2⟩
  wt x := ⟨V.tr x.1, tr_nonneg x, x.2.2⟩
  mul_smul l m a := ext (mul_smul (l : ℝ) (m : ℝ) a.1)
  one_smul a := ext (one_smul ℝ a.1)
  smul_perp l a b h := ⟨by
      show V.tr ((l : ℝ) • a.1) + V.tr ((l : ℝ) • b.1) ≤ 1
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add]
      exact le_trans (mul_le_of_le_one_left (add_nonneg (tr_nonneg a) (tr_nonneg b)) l.2.2) h,
    ext (smul_add (l : ℝ) a.1 b.1).symm⟩
  perp_smul {l m} h a := ⟨by
      have h' : (l : ℝ) + m ≤ 1 := h
      show V.tr ((l : ℝ) • a.1) + V.tr ((m : ℝ) • a.1) ≤ 1
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← add_mul]
      exact le_trans (mul_le_of_le_one_left (tr_nonneg a) h') a.2.2,
    ext (add_smul (l : ℝ) (m : ℝ) a.1).symm⟩
  smul_zero l := ext (smul_zero (l : ℝ))
  zero_smul a := ext (zero_smul ℝ a.1)
  wt_zero := Subtype.ext (show V.tr 0 = 0 from map_zero _)
  wt_ovee h := show V.tr (_ + _) = _ from map_add _ _ _
  wt_smul l a := Subtype.ext (show V.tr ((l : ℝ) • a.1) = (l : ℝ) * V.tr a.1 by
    rw [map_smul, smul_eq_mul])
  eq_zero_of_wt a h := by
    have h' : V.tr a.1 = 0 := congrArg Subtype.val h
    refine ext ?_
    rcases a.2.1.lt_or_eq with hlt | heq
    · exact absurd h' (V.tr_pos _ hlt).ne'
    · exact heq.symm
  perp_of_wt h := h

@[simp] theorem smul_val (r : I) (a : SubB V) : (r • a).1 = (r : ℝ) • a.1 := rfl
@[simp] theorem wt_val (a : SubB V) : ((wt a : I) : ℝ) = V.tr a.1 := rfl

/-- **SIG 57** (main.tex:1596, Definition, text): the subbase is cancellative. -/
theorem cancellative : WeightMod.Cancellative (SubB V) := by
  intro x y z hy hz h
  exact ext (add_left_cancel (congrArg Subtype.val h : x.1 + y.1 = x.1 + z.1))

end SubB

/-- **SIG 57** (main.tex:1598, Definition, text): the category `CWMod[[0,1]]`
of cancellative weight `[0,1]`-modules (a full subcategory of `WMod[[0,1]]`). -/
structure CWMod : Type (u + 1) where
  carrier : Type u
  [pcm : PCM carrier]
  [wm : WeightMod carrier]
  cancel : WeightMod.Cancellative carrier

attribute [instance] CWMod.pcm CWMod.wm

namespace CWMod

/-- **SIG 57** (SIG 30 at `M = [0,1]`): a morphism of `WMod[[0,1]]`: an
additive, action-preserving, weight-decreasing map. -/
@[ext]
structure Hom (X Y : CWMod) where
  toFun : X.carrier → Y.carrier
  additive : IsAdditive toFun
  map_smul : ∀ (r : I) (x : X.carrier), toFun (r • x) = r • toFun x
  wt_le : ∀ x, ((wt (toFun x) : I) : ℝ) ≤ wt x

instance : Category CWMod where
  Hom := Hom
  id X := ⟨id, ⟨rfl, fun h => ⟨h, rfl⟩⟩, fun _ _ => rfl, fun _ => le_rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, SEMod.IsAdditive.comp' f.additive g.additive,
    fun r a => by simp [f.map_smul, g.map_smul],
    fun x => (g.wt_le _).trans (f.wt_le x)⟩

@[simp] theorem id_toFun (X : CWMod) : (𝟙 X : Hom X X).toFun = id := rfl
@[simp] theorem comp_toFun {X Y Z : CWMod} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

theorem hom_ext {X Y : CWMod} {f g : X ⟶ Y} (h : ∀ a, f.toFun a = g.toFun a) : f = g :=
  Hom.ext (funext h)

theorem Hom.map_ovee {X Y : CWMod} (f : X ⟶ Y) {a b : X.carrier} (h : Perp a b) :
    ∃ h' : Perp (f.toFun a) (f.toFun b), ovee _ _ h' = f.toFun (ovee a b h) :=
  f.additive.2 h

end CWMod

/-- **SIG 57** (main.tex:1600, Definition, text): the functor
`sBase : OVSt → CWMod[[0,1]]`. -/
noncomputable abbrev sBase : OVSt ⥤ CWMod where
  obj V := ⟨SubB V, SubB.cancellative⟩
  map {V W} f :=
    { toFun := fun x => ⟨f.toLin x.1, f.pos _ x.2.1, (f.tr_le _ x.2.1).trans x.2.2⟩
      additive := ⟨SubB.ext (map_zero f.toLin), fun {a b} h =>
        ⟨show W.tr (f.toLin a.1) + W.tr (f.toLin b.1) ≤ 1 by
          have h' : V.tr a.1 + V.tr b.1 ≤ 1 := h
          linarith [f.tr_le _ a.2.1, f.tr_le _ b.2.1],
         SubB.ext (map_add f.toLin a.1 b.1).symm⟩⟩
      map_smul := fun r x => SubB.ext (map_smul f.toLin (r : ℝ) x.1)
      wt_le := fun x => f.tr_le _ x.2.1 }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem sBase_map_val {V W : OVSt} (f : V ⟶ W) (x : SubB V) :
    ((sBase.map f).toFun x).1 = f.toLin x.1 := rfl


/-! ## SIG 58: `OVSt ≃ CWMod[[0,1]]` -/


namespace OVSt

variable {V : OVSt}

theorem tr_div_le {x : V.carrier} (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) (hle : V.tr x ≤ t) :
    V.tr (t⁻¹ • x) ≤ 1 := by
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ ht, mul_one]; exact hle

/-- `t⁻¹ x ∈ sBase V` for `x ≥ 0` and `τ x ≤ t`. -/
noncomputable def sc (x : V.carrier) (hx : 0 ≤ x) (t : ℝ) (ht : 0 < t) (hle : V.tr x ≤ t) :
    SubB V :=
  ⟨t⁻¹ • x, smul_nonneg (inv_nonneg.2 ht.le) hx, tr_div_le hx ht hle⟩

theorem smul_sc (x : V.carrier) (hx : 0 ≤ x) (t : ℝ) (ht : 0 < t) (hle : V.tr x ≤ t) :
    t • (sc x hx t ht hle).1 = x := by
  show t • t⁻¹ • x = x
  rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

theorem tr_le_succ {x : V.carrier} : V.tr x ≤ |V.tr x| + 1 := by
  linarith [le_abs_self (V.tr x)]

theorem succ_pos (x : V.carrier) : 0 < |V.tr x| + 1 := by positivity

/-- Linear maps out of `V` agree once they agree on the subbase. -/
theorem linear_ext_subB {W : Type*} [AddCommGroup W] [Module ℝ W]
    {F G : V.carrier →ₗ[ℝ] W} (h : ∀ a : SubB V, F a.1 = G a.1) : F = G := by
  have hpos : ∀ a : V.carrier, 0 ≤ a → F a = G a := by
    intro a ha
    rw [← smul_sc a ha _ (succ_pos a) tr_le_succ, map_smul, map_smul, h]
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, b, ha, hb, rfl⟩ := V.gen x
  rw [map_sub, map_sub, hpos a ha, hpos b hb]

end OVSt

section Full

variable {V W : OVSt} (f : sBase.obj V ⟶ sBase.obj W)

theorem cw_sc_eq_smul (x : V.carrier) (hx : 0 ≤ x) {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (hle : V.tr x ≤ t) :
    OVSt.sc x hx t' (ht.trans_le htt) (hle.trans htt)
      = (⟨t / t', ⟨div_nonneg ht.le (ht.le.trans htt), (div_le_one (ht.trans_le htt)).2 htt⟩⟩ : I)
        • OVSt.sc x hx t ht hle := by
  refine SubB.ext ?_
  show t'⁻¹ • x = (t / t') • t⁻¹ • x
  rw [smul_smul]
  congr 1
  have : t' ≠ 0 := (ht.trans_le htt).ne'
  field_simp

theorem cw_scale_mono (x : V.carrier) (hx : 0 ≤ x) {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (hle : V.tr x ≤ t) :
    t' • (f.toFun (OVSt.sc x hx t' (ht.trans_le htt) (hle.trans htt))).1
      = t • (f.toFun (OVSt.sc x hx t ht hle)).1 := by
  rw [cw_sc_eq_smul x hx ht htt hle, f.map_smul, SubB.smul_val, smul_smul]
  congr 1
  show t' * (t / t') = t
  have : t' ≠ 0 := (ht.trans_le htt).ne'
  field_simp

theorem cw_scale_indep (x : V.carrier) (hx : 0 ≤ x) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t')
    (hle : V.tr x ≤ t) (hle' : V.tr x ≤ t') :
    t • (f.toFun (OVSt.sc x hx t ht hle)).1 = t' • (f.toFun (OVSt.sc x hx t' ht' hle')).1 := by
  rw [← cw_scale_mono f x hx ht (le_max_left t t') hle,
    ← cw_scale_mono f x hx ht' (le_max_right t t') hle']

open Classical in
/-- The extension of `f` to the positive cone. -/
noncomputable def cwExtG (x : V.carrier) : W.carrier :=
  if hx : 0 ≤ x then (|V.tr x| + 1) • (f.toFun (OVSt.sc x hx _ (OVSt.succ_pos x) OVSt.tr_le_succ)).1
  else 0

theorem cwExtG_eq (x : V.carrier) (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) (hle : V.tr x ≤ t) :
    cwExtG f x = t • (f.toFun (OVSt.sc x hx t ht hle)).1 := by
  rw [cwExtG, dite_cond_eq_true (eq_true hx)]; exact cw_scale_indep f x hx _ ht _ hle

theorem cwExtG_nonneg (x : V.carrier) : 0 ≤ cwExtG f x := by
  unfold cwExtG; split_ifs with hx
  · exact smul_nonneg (OVSt.succ_pos x).le (f.toFun _).2.1
  · exact le_rfl

theorem cwExtG_add (a b : V.carrier) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cwExtG f (a + b) = cwExtG f a + cwExtG f b := by
  have hta := V.tr_nonneg ha; have htb := V.tr_nonneg hb
  set T := V.tr a + V.tr b + 1 with hT
  have hT0 : 0 < T := by positivity
  have hp : Perp (OVSt.sc a ha T hT0 (by linarith)) (OVSt.sc b hb T hT0 (by linarith)) := by
    show V.tr (T⁻¹ • a) + V.tr (T⁻¹ • b) ≤ 1
    rw [← map_add, ← smul_add]
    exact OVSt.tr_div_le (add_nonneg ha hb) hT0 (by rw [map_add]; linarith)
  have e : OVSt.sc (a + b) (add_nonneg ha hb) T hT0 (by rw [map_add]; linarith)
      = ovee _ _ hp := SubB.ext (smul_add _ _ _)
  rw [cwExtG_eq f _ (add_nonneg ha hb) hT0 (by rw [map_add]; linarith), e,
    cwExtG_eq f a ha hT0 (by linarith), cwExtG_eq f b hb hT0 (by linarith), ← smul_add]
  obtain ⟨_, e'⟩ := f.map_ovee hp
  rw [← e']; rfl

theorem cwExtG_zero : cwExtG f (0 : V.carrier) = 0 := by
  have := cwExtG_add f 0 0 le_rfl le_rfl
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem cwExtG_smul (c : ℝ) (a : V.carrier) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    cwExtG f (c • a) = c • cwExtG f a := by
  rcases hc.lt_or_eq with hc | hc
  · have hta := V.tr_nonneg ha
    have hT : 0 < V.tr a + 1 := by positivity
    have h1 : 0 < c * (V.tr a + 1) := by positivity
    have hle : V.tr (c • a) ≤ c * (V.tr a + 1) := by rw [map_smul, smul_eq_mul]; nlinarith
    have e : OVSt.sc (c • a) (smul_nonneg hc.le ha) _ h1 hle
        = OVSt.sc a ha _ hT (by linarith) := by
      refine SubB.ext ?_
      show (c * (V.tr a + 1))⁻¹ • c • a = (V.tr a + 1)⁻¹ • a
      rw [smul_smul, mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
    rw [cwExtG_eq f a ha hT (by linarith), cwExtG_eq f (c • a) (smul_nonneg hc.le ha) h1 hle, e,
      smul_smul]
  · rw [← hc, zero_smul, zero_smul, cwExtG_zero]

theorem cwExtG_subB (y : SubB V) : cwExtG f y.1 = (f.toFun y).1 := by
  rw [cwExtG_eq f y.1 y.2.1 one_pos y.2.2, one_smul]
  congr 2
  exact SubB.ext (by show (1 : ℝ)⁻¹ • y.1 = y.1; rw [inv_one, one_smul])

theorem cwExtG_tr_le (x : V.carrier) (hx : 0 ≤ x) : W.tr (cwExtG f x) ≤ V.tr x := by
  rw [cwExtG_eq f x hx (OVSt.succ_pos x) OVSt.tr_le_succ, map_smul, smul_eq_mul]
  have := f.wt_le (OVSt.sc x hx _ (OVSt.succ_pos x) OVSt.tr_le_succ)
  rw [SubB.wt_val, SubB.wt_val] at this
  calc (|V.tr x| + 1) * W.tr (f.toFun _).1 ≤ (|V.tr x| + 1) * V.tr ((|V.tr x| + 1)⁻¹ • x) :=
        mul_le_mul_of_nonneg_left this (OVSt.succ_pos x).le
    _ = V.tr x := by
        rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (OVSt.succ_pos x).ne', one_mul]

/-- The extension of a `CWMod`-morphism `sBase V → sBase W` to `V → W`. -/
noncomputable def cwExtHom : V ⟶ W :=
  let hF := CW.exists_linear_of_cone V.gen (cwExtG f) (cwExtG_add f) (cwExtG_smul f)
  { toLin := hF.choose
    pos := fun x hx => by rw [hF.choose_spec x hx]; exact cwExtG_nonneg f x
    tr_le := fun x hx => by rw [hF.choose_spec x hx]; exact cwExtG_tr_le f x hx }

theorem cwExtHom_apply (x : V.carrier) (hx : 0 ≤ x) : (cwExtHom f).toLin x = cwExtG f x :=
  (CW.exists_linear_of_cone V.gen (cwExtG f) (cwExtG_add f) (cwExtG_smul f)).choose_spec x hx

theorem sBase_map_extHom : sBase.map (cwExtHom f) = f := by
  refine CWMod.hom_ext fun y => SubB.ext ?_
  rw [sBase_map_val, cwExtHom_apply f y.1 y.2.1, cwExtG_subB]

end Full

instance sBase_faithful : sBase.Faithful where
  map_injective {V W} f g h := by
    refine OVSt.hom_ext fun x => ?_
    have := OVSt.linear_ext_subB (F := f.toLin) (G := g.toLin) fun a => by
      have := congrArg (fun φ : sBase.obj V ⟶ sBase.obj W => (φ.toFun a).1) h
      simpa using this
    rw [this]

instance sBase_full : sBase.Full where
  map_surjective f := ⟨cwExtHom f, sBase_map_extHom f⟩

/-- The ordered vector space with trace `V(X)` of a cancellative weight
`[0,1]`-module (the construction of the print's proof of SIG 58, by formal
multiples and differences). -/
noncomputable def vOf (X : CWMod) : OVSt :=
  haveI : Fact (WeightMod.Cancellative X.carrier) := ⟨X.cancel⟩
  { carrier := CW.Vec X.carrier
    gen := CW.Vec.gen
    tr := CW.Vec.tr
    tr_pos := fun _ h => CW.Vec.tr_pos h }

section Ess

variable (X : CWMod)

instance : Fact (WeightMod.Cancellative X.carrier) := ⟨X.cancel⟩

/-- `a ↦ 1 · a`, as a morphism `X → sBase V(X)`. -/
noncomputable def toVOf : X ⟶ sBase.obj (vOf X) where
  toFun a := ⟨CW.gmap a, CW.gmap_nonneg a, by
    show CW.Vec.tr (CW.gmap a) ≤ 1
    rw [CW.tr_gmap]; exact (wt a).2.2⟩
  additive := ⟨SubB.ext CW.gmap_zero, fun {a b} h =>
    ⟨show CW.Vec.tr (CW.gmap a) + CW.Vec.tr (CW.gmap b) ≤ 1 from CW.gmap_perp_iff.1 h,
      SubB.ext (CW.gmap_ovee h).symm⟩⟩
  map_smul r a := SubB.ext (CW.gmap_smul r a)
  wt_le a := by
    show CW.Vec.tr (CW.gmap a) ≤ _
    rw [CW.tr_gmap]

theorem cw_exists_gmap (x : SubB (vOf X)) : ∃ a : X.carrier, CW.gmap a = x.1 :=
  CW.gmap_surjective (X := X.carrier) x.2.1 x.2.2

/-- The inverse of `toVOf`. -/
noncomputable def fromVOf : sBase.obj (vOf X) ⟶ X where
  toFun x := (cw_exists_gmap X x).choose
  additive := by
    have hs := fun x => (cw_exists_gmap X x).choose_spec
    refine ⟨CW.gmap_injective (by rw [hs 0, CW.gmap_zero]; rfl), fun {x y} h => ?_⟩
    have hp : Perp (cw_exists_gmap X x).choose (cw_exists_gmap X y).choose := by
      rw [CW.gmap_perp_iff, hs x, hs y]; exact h
    refine ⟨hp, CW.gmap_injective ?_⟩
    rw [CW.gmap_ovee, hs x, hs y, hs]; rfl
  map_smul r x := by
    have hs := fun x => (cw_exists_gmap X x).choose_spec
    refine CW.gmap_injective ?_
    rw [CW.gmap_smul, hs, hs]; rfl
  wt_le x := by
    have := CW.tr_gmap (X := X.carrier) (cw_exists_gmap X x).choose
    rw [(cw_exists_gmap X x).choose_spec] at this
    rw [← this]; exact le_rfl

/-- `sBase V(X) ≅ X`. -/
noncomputable def vOfIso : sBase.obj (vOf X) ≅ X where
  hom := fromVOf X
  inv := toVOf X
  hom_inv_id := CWMod.hom_ext fun x => SubB.ext (cw_exists_gmap X x).choose_spec
  inv_hom_id := CWMod.hom_ext fun a => CW.gmap_injective (X := X.carrier)
    (cw_exists_gmap X ((toVOf X).toFun a)).choose_spec

end Ess

instance sBase_essSurj : sBase.EssSurj := ⟨fun X => ⟨vOf X, ⟨vOfIso X⟩⟩⟩

/-- **SIG 58** (`prop:OVSt-equiv-CWMod`, main.tex:1605, Proposition): the
functor `sBase : OVSt → CWMod[[0,1]]` is an equivalence of categories.  The
print sketches the inverse (totalization of `X`, then formal differences) and
refers to Cho's thesis §7.2.1; ours builds `V(X)` as formal multiples `r · a`
modulo rescaling, then formal differences (the tree's Gudder–Pulmannová route,
179III.2, with sums made total by the weight), and proves fullness by
extending a morphism from the subbase to the positive cone and then linearly. -/
instance sBase_isEquivalence : sBase.IsEquivalence where


/-! ## Canonical sums in `[0,1]` are real sums -/


/-! ## SIG 57: the base norm; pre-base-norm, Banach, σ-closed subbase -/

namespace OVSt

variable (V : OVSt)

/-- The values `τ x₁ + τ x₂` over decompositions `x = x₁ - x₂`, `xᵢ ≥ 0`. -/
def normSet (x : V.carrier) : Set ℝ :=
  {r | ∃ a b : V.carrier, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b ∧ r = V.tr a + V.tr b}

/-- **SIG 57** (main.tex:1612, Definition, text): the intrinsic seminorm (base norm)
`‖x‖ = inf {τ x₁ + τ x₂ | x = x₁ - x₂, x₁, x₂ ∈ V₊}`. -/
noncomputable def bnorm (x : V.carrier) : ℝ := sInf (V.normSet x)

/-- **SIG 57** (main.tex:1622, Definition, text): `V` is a **pre-base-norm space** if the
seminorm is a norm. -/
def IsPreBaseNorm : Prop := ∀ x : V.carrier, V.bnorm x = 0 → x = 0

/-- Completeness for the base (semi)norm: Cauchy sequences converge. -/
def BNComplete : Prop :=
  ∀ s : ℕ → V.carrier, (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, V.bnorm (s m - s n) < ε) →
    ∃ v : V.carrier, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, V.bnorm (s n - v) < ε

/-- **SIG 57** (main.tex:1625, Definition, text): a **Banach pre-base-norm space**: a
pre-base-norm space complete in the base norm. -/
def IsBanachPBN : Prop := V.IsPreBaseNorm ∧ V.BNComplete

/-- The series `∑ₙ xₙ` converges to `v` in the base norm. -/
def SeriesTo (x : ℕ → V.carrier) (v : V.carrier) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, V.bnorm ((∑ i ∈ Finset.range n, x i) - v) < ε

/-- **SIG 57** (main.tex:1630, Definition, text): a **σ-closed subbase**: for every sequence
`(xₙ)` in `sBase(V)` with `∑ τ(xₙ) ≤ 1` the series `∑ xₙ` converges to an
element of `sBase(V)`. -/
def SigmaClosedSubbase : Prop :=
  ∀ x : ℕ → V.carrier, (∀ n, 0 ≤ x n) → (∀ N, ∑ i ∈ Finset.range N, V.tr (x i) ≤ 1) →
    ∃ v : V.carrier, 0 ≤ v ∧ V.tr v ≤ 1 ∧ V.SeriesTo x v

variable {V}

theorem normSet_nonempty (x : V.carrier) : (V.normSet x).Nonempty := by
  obtain ⟨a, b, ha, hb, h⟩ := V.gen x
  exact ⟨_, a, b, ha, hb, h, rfl⟩

theorem normSet_bdd (x : V.carrier) : BddBelow (V.normSet x) :=
  ⟨0, by rintro _ ⟨a, b, ha, hb, -, rfl⟩; exact add_nonneg (V.tr_nonneg ha) (V.tr_nonneg hb)⟩

theorem bnorm_nonneg (x : V.carrier) : 0 ≤ V.bnorm x :=
  le_csInf (normSet_nonempty x) (by
    rintro _ ⟨a, b, ha, hb, -, rfl⟩; exact add_nonneg (V.tr_nonneg ha) (V.tr_nonneg hb))

theorem bnorm_le {x a b : V.carrier} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x = a - b) :
    V.bnorm x ≤ V.tr a + V.tr b :=
  csInf_le (normSet_bdd x) ⟨a, b, ha, hb, h, rfl⟩

theorem exists_lt_of_bnorm_lt {x : V.carrier} {ε : ℝ} (hε : V.bnorm x < ε) :
    ∃ a b : V.carrier, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b ∧ V.tr a + V.tr b < ε := by
  obtain ⟨r, ⟨a, b, ha, hb, h, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (normSet_nonempty x) hε
  exact ⟨a, b, ha, hb, h, hr⟩

theorem le_bnorm {x : V.carrier} {c : ℝ}
    (h : ∀ a b : V.carrier, 0 ≤ a → 0 ≤ b → x = a - b → c ≤ V.tr a + V.tr b) :
    c ≤ V.bnorm x :=
  le_csInf (normSet_nonempty x) (by rintro _ ⟨a, b, ha, hb, hx, rfl⟩; exact h a b ha hb hx)

/-- **SIG 73** (proof, main.tex:3386, citing Furber Cor. 2.2.5): on the
positive cone the base norm is the trace. -/
theorem bnorm_of_nonneg {x : V.carrier} (hx : 0 ≤ x) : V.bnorm x = V.tr x := by
  refine le_antisymm ?_ (le_bnorm fun a b ha hb h => ?_)
  · have := bnorm_le hx le_rfl (sub_zero x).symm
    rwa [map_zero, add_zero] at this
  · rw [h, map_sub]; linarith [V.tr_nonneg hb]

theorem bnorm_zero : V.bnorm 0 = 0 := by rw [bnorm_of_nonneg le_rfl, map_zero]

theorem abs_tr_le (x : V.carrier) : |V.tr x| ≤ V.bnorm x :=
  le_bnorm fun a b ha hb h => by
    rw [h, map_sub, abs_le]
    constructor <;> linarith [V.tr_nonneg ha, V.tr_nonneg hb]

theorem bnorm_add_le (x y : V.carrier) : V.bnorm (x + y) ≤ V.bnorm x + V.bnorm y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, b, ha, hb, hx, h1⟩ := exists_lt_of_bnorm_lt
    (lt_add_of_pos_right (V.bnorm x) (half_pos hε))
  obtain ⟨c, d, hc, hd, hy, h2⟩ := exists_lt_of_bnorm_lt
    (lt_add_of_pos_right (V.bnorm y) (half_pos hε))
  calc V.bnorm (x + y) ≤ V.tr (a + c) + V.tr (b + d) :=
        bnorm_le (add_nonneg ha hc) (add_nonneg hb hd) (by rw [hx, hy]; abel)
    _ < V.bnorm x + V.bnorm y + ε := by rw [map_add, map_add]; linarith

theorem bnorm_neg (x : V.carrier) : V.bnorm (-x) = V.bnorm x := by
  have : ∀ y : V.carrier, V.bnorm (-y) ≤ V.bnorm y := fun y =>
    le_bnorm fun a b ha hb h => by
      have := bnorm_le (x := -y) hb ha (by rw [h]; abel)
      linarith
  exact le_antisymm (this x) (by simpa using this (-x))

theorem bnorm_sub_comm (x y : V.carrier) : V.bnorm (x - y) = V.bnorm (y - x) := by
  rw [← bnorm_neg, neg_sub]

theorem bnorm_smul_le {c : ℝ} (hc : 0 ≤ c) (x : V.carrier) : V.bnorm (c • x) ≤ c * V.bnorm x := by
  rcases hc.lt_or_eq with hc | hc
  · have : c⁻¹ * V.bnorm (c • x) ≤ V.bnorm x := le_bnorm fun a b ha hb h => by
      have := bnorm_le (x := c • x) (smul_nonneg hc.le ha) (smul_nonneg hc.le hb)
        (by rw [h, smul_sub])
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add] at this
      rw [inv_mul_le_iff₀ hc]; exact this
    rwa [inv_mul_le_iff₀ hc] at this
  · rw [← hc, zero_smul, zero_mul, bnorm_zero]

theorem bnorm_smul (c : ℝ) (x : V.carrier) : V.bnorm (c • x) = |c| * V.bnorm x := by
  have key : ∀ {c : ℝ}, 0 ≤ c → ∀ x : V.carrier, V.bnorm (c • x) = c * V.bnorm x := by
    intro c hc x
    refine le_antisymm (bnorm_smul_le hc x) ?_
    rcases hc.lt_or_eq with hc | hc
    · have := bnorm_smul_le (inv_nonneg.2 hc.le) (c • x)
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      rw [← le_div_iff₀' hc, div_eq_inv_mul]; exact this
    · rw [← hc, zero_mul]; exact bnorm_nonneg _
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, key hc]
  · rw [abs_of_nonpos hc, show c • x = (-c) • (-x) by rw [smul_neg, neg_smul, neg_neg],
      key (neg_nonneg.2 hc), bnorm_neg]

end OVSt


/-! ## SIG 73: a σ-weight module structure on the subbase makes `V` a Banach
pre-base-norm space -/


theorem SubB.val_eq_zero_of_tr {V : OVSt} (a : SubB V) (h : V.tr a.1 = 0) : a.1 = 0 := by
  rcases a.2.1.lt_or_eq with hlt | heq
  · exact absurd h (V.tr_pos _ hlt).ne'
  · exact heq.symm

/-- The σ-weight `[0,1]`-module `X` is a structure on `sBase(V)` **extending**
its weight-module structure (SIG 73's hypothesis), presented by a bijection
`e : X ≃ sBase(V)` preserving the action, the weight, and binary sums. -/
structure SigmaExtension (V : OVSt.{u}) (X : SWMod IU.{u}) where
  e : X.carrier ≃ SubB V
  map_smul : ∀ (r : I) (x : X.carrier), e (r • x) = r • e x
  wt_eq : ∀ x : X.carrier, ((wI X x : I) : ℝ) = V.tr (e x).1
  pair : ∀ x y s : X.carrier, SigmaPAM.SumsTo ![x, y] s ↔
    V.tr (e x).1 + V.tr (e y).1 ≤ 1 ∧ (e s).1 = (e x).1 + (e y).1


namespace SigmaExtension

variable {V : OVSt.{u}} {X : SWMod IU.{u}} (E : SigmaExtension V X)

theorem e_zero : (E.e SigmaPAM.zero).1 = 0 :=
  SubB.val_eq_zero_of_tr _ (by rw [← E.wt_eq, wI_zero X]; rfl)

theorem fin_sum : ∀ (N : ℕ) (f : Fin N → X.carrier) (u : X.carrier), SigmaPAM.SumsTo f u →
    (E.e u).1 = ∑ i, (E.e (f i)).1 := by
  intro N
  induction N with
  | zero =>
    intro f u h
    rw [h.unique (SigmaPAM.sumsTo_of_isEmpty f), E.e_zero, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ N ih =>
    intro f u h
    obtain ⟨u', hu', hp⟩ := (SigmaPAM.sumsTo_fin_last_iff f u).1 h
    rw [((E.pair _ _ _).1 hp).2, ih _ u' hu', Fin.sum_univ_castSucc]

theorem hasSum_tr {x : ℕ → X.carrier} {s : X.carrier} (h : SigmaPAM.SumsTo x s) :
    HasSum (fun n => V.tr (E.e (x n)).1) (V.tr (E.e s).1) := by
  have := CW.hasSum_of_isCSum (wI_sumsTo X x s h)
  simp only [E.wt_eq] at this
  exact this

theorem sub_nonneg_split {x : ℕ → X.carrier} {s : X.carrier} (h : SigmaPAM.SumsTo x s) (n : ℕ) :
    ∃ v : X.carrier, (E.e s).1 = (∑ i ∈ Finset.range n, (E.e (x i)).1) + (E.e v).1 := by
  obtain ⟨u, v, hu, hv, huv⟩ := (SigmaPAM.sumsTo_split x (· < n) s).1 h
  have hu' : SigmaPAM.SumsTo (fun i : Fin n => x i) u :=
    (SigmaPAM.sumsTo_comp_equiv' Fin.equivSubtype (fun j : {i // i < n} => x j.1)
      (fun i : Fin n => x i) (fun _ => rfl) u).2 hu
  refine ⟨v, ?_⟩
  rw [((E.pair _ _ _).1 huv).2, E.fin_sum n _ u hu', Fin.sum_univ_eq_sum_range
    (fun i => (E.e (x i)).1)]

/-- **SIG 73**, second claim: the series `∑ xₙ` converges to `⋁ xₙ` in the
base norm (proof as printed, with Furber's `‖x‖ = τ x` on `V₊`). -/
theorem seriesTo {x : ℕ → X.carrier} {s : X.carrier} (h : SigmaPAM.SumsTo x s) :
    V.SeriesTo (fun n => (E.e (x n)).1) (E.e s).1 := by
  intro ε hε
  have ht := (E.hasSum_tr h).tendsto_sum_nat
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨v, hv⟩ := E.sub_nonneg_split h n
  have hd := hN n hn
  rw [Real.dist_eq] at hd
  have e1 : (∑ i ∈ Finset.range n, (E.e (x i)).1) - (E.e s).1 = -(E.e v).1 := by
    rw [hv]; abel
  rw [e1, OVSt.bnorm_neg, OVSt.bnorm_of_nonneg (E.e v).2.1]
  have e2 : V.tr (E.e v).1 = V.tr (E.e s).1 - ∑ i ∈ Finset.range n, V.tr (E.e (x i)).1 := by
    rw [hv, map_add, map_sum]; ring
  rw [e2]
  have := abs_sub_comm (∑ i ∈ Finset.range n, V.tr (E.e (x i)).1) (V.tr (E.e s).1)
  exact lt_of_le_of_lt (le_abs_self _) (this ▸ hd)

/-- Elements of `X` from small positive vectors. -/
noncomputable def ofVec (y : V.carrier) (hy : 0 ≤ y) (ht : V.tr y ≤ 1) : X.carrier :=
  E.e.symm (⟨y, hy, ht⟩ : SubB V)

theorem e_ofVec (y : V.carrier) (hy : 0 ≤ y) (ht : V.tr y ≤ 1) :
    (E.e (E.ofVec y hy ht)).1 = y := by
  exact congrArg Subtype.val (E.e.apply_symm_apply _)

/-- A sequence of small positive vectors is summable in `X`. -/
theorem sumsTo_of_small (y : ℕ → V.carrier) (hy : ∀ n, 0 ≤ y n)
    (hs : ∀ n, V.tr (y n) ≤ (1 / 2) ^ (n + 2)) :
    ∃ a : X.carrier, SigmaPAM.SumsTo (fun n => E.ofVec (y n) (hy n)
      ((hs n).trans (by
        have : ((1 : ℝ) / 2) ^ (n + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        exact this))) a ∧ V.tr (E.e a).1 ≤ 1 / 2 := by
  have hsum := summable_of_wI X (fun n => E.ofVec (y n) (hy n) ((hs n).trans
    (pow_le_one₀ (by norm_num) (by norm_num)))) ((CW.csummable_I_iff _).2 fun F => by
      simp only [E.wt_eq, e_ofVec]
      exact (CW.sum_geom_le _ (fun n => V.tr_nonneg (hy n)) hs F).trans (by norm_num))
  refine ⟨_, SigmaPAM.sumsTo_sum hsum, ?_⟩
  have := E.hasSum_tr (SigmaPAM.sumsTo_sum hsum)
  simp only [e_ofVec] at this
  exact CW.hasSum_geom_le _ hs this

include E in
/-- **SIG 73**, first claim: `V` is a pre-base-norm space (proof as printed;
the print's preliminary rescaling of `a = x̃ - ỹ` into the subbase is not
needed, since the decompositions `a = wₙ - zₙ` are small anyway). -/
theorem isPreBaseNorm : V.IsPreBaseNorm := by
  intro a ha
  have hlt : ∀ n : ℕ, V.bnorm a < (1 / 2) ^ (n + 3) := fun n => by rw [ha]; positivity
  choose w z hw hz hwz hsmall using fun n => OVSt.exists_lt_of_bnorm_lt (hlt n)
  have hw1 : ∀ n, V.tr (w n) ≤ (1 / 2) ^ (n + 2) := fun n => by
    have := hsmall n; have := V.tr_nonneg (hz n)
    have : ((1 : ℝ) / 2) ^ (n + 3) ≤ (1 / 2) ^ (n + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hz1 : ∀ n, V.tr (z n) ≤ (1 / 2) ^ (n + 2) := fun n => by
    have := hsmall n; have := V.tr_nonneg (hw n)
    have : ((1 : ℝ) / 2) ^ (n + 3) ≤ (1 / 2) ^ (n + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hw1' : ∀ n, V.tr (w (n + 1)) ≤ (1 / 2) ^ (n + 2) := fun n =>
    (hw1 (n + 1)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hz1' : ∀ n, V.tr (z (n + 1)) ≤ (1 / 2) ^ (n + 2) := fun n =>
    (hz1 (n + 1)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hle1 : ∀ n, ((1 : ℝ) / 2) ^ (n + 2) ≤ 1 / 4 := fun n => by
    calc ((1 : ℝ) / 2) ^ (n + 2) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have rel : ∀ n, z n + w (n + 1) = z (n + 1) + w n := fun n => by
    have := (hwz n).symm.trans (hwz (n + 1))
    rw [sub_eq_sub_iff_add_eq_add] at this
    rw [add_comm (z n), ← this, add_comm]
  -- the elements of `X`
  let Zs : ℕ → X.carrier := fun n => E.ofVec (z n) (hz n) ((hz1 n).trans (by linarith [hle1 n]))
  let Ws : ℕ → X.carrier := fun n => E.ofVec (w n) (hw n) ((hw1 n).trans (by linarith [hle1 n]))
  have hPtr : ∀ n, V.tr (z n + w (n + 1)) ≤ 1 := fun n => by
    rw [map_add]; linarith [hz1 n, hw1' n, hle1 n]
  let P : ℕ → X.carrier := fun n => E.ofVec (z n + w (n + 1)) (add_nonneg (hz n) (hw (n + 1)))
    (hPtr n)
  have hP1 : ∀ n, SigmaPAM.SumsTo ![Zs n, Ws (n + 1)] (P n) := fun n => by
    refine (E.pair _ _ _).2 ⟨?_, ?_⟩
    · simp only [Zs, Ws, e_ofVec]; rw [← map_add]; exact hPtr n
    · simp only [Zs, Ws, P, e_ofVec]
  have hP2 : ∀ n, SigmaPAM.SumsTo ![Zs (n + 1), Ws n] (P n) := fun n => by
    refine (E.pair _ _ _).2 ⟨?_, ?_⟩
    · simp only [Zs, Ws, e_ofVec]; rw [← map_add, ← rel]; exact hPtr n
    · simp only [Zs, Ws, P, e_ofVec]; exact rel n
  -- the four partial families
  obtain ⟨a₁, ha₁, ta₁⟩ := E.sumsTo_of_small z hz hz1
  obtain ⟨b₁, hb₁, tb₁⟩ := E.sumsTo_of_small (fun n => w (n + 1)) (fun n => hw (n + 1)) hw1'
  obtain ⟨a₂, ha₂, ta₂⟩ := E.sumsTo_of_small (fun n => z (n + 1)) (fun n => hz (n + 1)) hz1'
  obtain ⟨b₂, hb₂, tb₂⟩ := E.sumsTo_of_small w hw hw1
  have pair_of : ∀ p q : X.carrier, V.tr (E.e p).1 ≤ 1 / 2 → V.tr (E.e q).1 ≤ 1 / 2 →
      ∃ c, SigmaPAM.SumsTo ![p, q] c := fun p q hp hq => by
    have htr : V.tr ((E.e p).1 + (E.e q).1) ≤ 1 := by rw [map_add]; linarith
    refine ⟨E.ofVec _ (add_nonneg (E.e p).2.1 (E.e q).2.1) htr, (E.pair _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [← map_add]; exact htr
    · rw [e_ofVec]
  obtain ⟨U, hU⟩ := pair_of a₁ b₁ ta₁ tb₁
  obtain ⟨U', hU'⟩ := pair_of a₂ b₂ ta₂ tb₂
  have hA : SigmaPAM.SumsTo (Sum.elim Zs (fun n => Ws (n + 1))) U :=
    (SigmaPAM.sumsTo_sum_iff _ _ _).2 ⟨a₁, b₁, ha₁, hb₁, hU⟩
  have hB : SigmaPAM.SumsTo (Sum.elim (fun n => Zs (n + 1)) Ws) U' :=
    (SigmaPAM.sumsTo_sum_iff _ _ _).2 ⟨a₂, b₂, ha₂, hb₂, hU'⟩
  have hUU : U = U' :=
    ((sumsTo_pairsU _ _ P hP1 U).1 hA).unique ((sumsTo_pairsU _ _ P hP2 U').1 hB)
  -- split off `z₀` and `w₀`
  obtain ⟨a', ha', ha'1⟩ := (SigmaPAM.sumsTo_nat_succ_iff Zs a₁).1 ha₁
  obtain ⟨b', hb', hb'1⟩ := (SigmaPAM.sumsTo_nat_succ_iff Ws b₂).1 hb₂
  have ea : a' = a₂ := ha'.unique ha₂
  have eb : b' = b₁ := hb'.unique hb₁
  subst ea; subst eb
  have v1 := ((E.pair _ _ _).1 hU).2
  have v2 := ((E.pair _ _ _).1 hU').2
  have v3 := ((E.pair _ _ _).1 ha'1).2
  have v4 := ((E.pair _ _ _).1 hb'1).2
  rw [hUU, v2, v4] at v1
  rw [v3] at v1
  have hz0 : (E.e (Zs 0)).1 = z 0 := e_ofVec _ _ _ _
  have hw0 : (E.e (Ws 0)).1 = w 0 := e_ofVec _ _ _ _
  rw [hz0] at v1; rw [hw0] at v1
  have : w 0 = z 0 := by
    first
    | linear_combination (norm := module) v1
    | linear_combination (norm := module) -v1
  rw [hwz 0, this, sub_self]

include E in
/-- **SIG 73**, completeness: `V` is complete in the base norm (proof as
printed: absolutely convergent series converge, via the second claim; we run
the argument on a fast Cauchy subsequence). -/
theorem bnComplete : V.BNComplete := by
  intro s hs
  choose Nf hNf using fun k : ℕ => hs ((1 / 2) ^ (k + 3)) (by positivity)
  let n : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), Nf i
  have hnk : ∀ k, Nf k ≤ n k := fun k =>
    Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hnmono : Monotone n := fun i j hij =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hij))
  have hx : ∀ k, V.bnorm (s (n (k + 1)) - s (n k)) < (1 / 2) ^ (k + 3) := fun k =>
    hNf k _ ((hnk k).trans (hnmono (Nat.le_succ k))) _ (hnk k)
  choose y z hy hz hyz hsmall using fun k => OVSt.exists_lt_of_bnorm_lt (hx k)
  have hy1 : ∀ k, V.tr (y k) ≤ (1 / 2) ^ (k + 2) := fun k => by
    have := hsmall k; have := V.tr_nonneg (hz k)
    have : ((1 : ℝ) / 2) ^ (k + 3) ≤ (1 / 2) ^ (k + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hz1 : ∀ k, V.tr (z k) ≤ (1 / 2) ^ (k + 2) := fun k => by
    have := hsmall k; have := V.tr_nonneg (hy k)
    have : ((1 : ℝ) / 2) ^ (k + 3) ≤ (1 / 2) ^ (k + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  obtain ⟨a, ha, -⟩ := E.sumsTo_of_small y hy hy1
  obtain ⟨b, hb, -⟩ := E.sumsTo_of_small z hz hz1
  have sa := E.seriesTo ha
  have sb := E.seriesTo hb
  simp only [e_ofVec] at sa sb
  refine ⟨s (n 0) + (E.e a).1 - (E.e b).1, fun ε hε => ?_⟩
  obtain ⟨Ka, hKa⟩ := sa (ε / 3) (by positivity)
  obtain ⟨Kb, hKb⟩ := sb (ε / 3) (by positivity)
  obtain ⟨Kc, hKc⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 3 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set K := max (max Ka Kb) Kc
  refine ⟨n K, fun m hm => ?_⟩
  have htel : s (n K) - s (n 0) = ∑ k ∈ Finset.range K, (y k - z k) := by
    rw [← Finset.sum_congr rfl (fun k _ => hyz k)]
    exact (Finset.sum_range_sub (fun k => s (n k)) K).symm
  have h1 : V.bnorm (s m - s (n K)) < ε / 3 := by
    have := hNf K m ((hnk K).trans hm) (n K) (hnk K)
    have hp : ((1 : ℝ) / 2) ^ (K + 3) ≤ (1 / 2) ^ Kc :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have h2 : V.bnorm (s (n K) - (s (n 0) + (E.e a).1 - (E.e b).1)) < 2 * (ε / 3) := by
    have e : s (n K) - (s (n 0) + (E.e a).1 - (E.e b).1)
        = ((∑ k ∈ Finset.range K, y k) - (E.e a).1)
          - ((∑ k ∈ Finset.range K, z k) - (E.e b).1) := by
      rw [show s (n K) = s (n 0) + (s (n K) - s (n 0)) by abel, htel, Finset.sum_sub_distrib]
      abel
    rw [e]
    have hadd := OVSt.bnorm_add_le (V := V) ((∑ k ∈ Finset.range K, y k) - (E.e a).1)
      (-((∑ k ∈ Finset.range K, z k) - (E.e b).1))
    rw [← sub_eq_add_neg, OVSt.bnorm_neg] at hadd
    refine lt_of_le_of_lt hadd ?_
    have := hKa K (le_trans (le_max_left _ _) (le_max_left _ _))
    have := hKb K (le_trans (le_max_right _ _) (le_max_left _ _))
    linarith
  calc V.bnorm (s m - (s (n 0) + (E.e a).1 - (E.e b).1))
      = V.bnorm ((s m - s (n K)) + (s (n K) - (s (n 0) + (E.e a).1 - (E.e b).1))) := by
        congr 1; abel
    _ ≤ _ := OVSt.bnorm_add_le _ _
    _ < ε / 3 + 2 * (ε / 3) := by linarith
    _ = ε := by ring

/-- **SIG 73** (`lem:bbns-if-subbase-sigma-wmod`, main.tex:3318, Lemma): let
`V` be an ordered vector space with trace whose subbase carries a (cancellative)
σ-weight `[0,1]`-module structure `X` extending its weight-module structure.
Then `V` is a Banach pre-base-norm space, and for every summable sequence in
`X` the series converges in the base norm to its σ-sum.  (The cancellation
step of the print's proof is done on vectors, where it is automatic.) -/
theorem sig73 :
    V.IsBanachPBN ∧ ∀ (x : ℕ → X.carrier) (s : X.carrier), SigmaPAM.SumsTo x s →
      V.SeriesTo (fun n => (E.e (x n)).1) (E.e s).1 :=
  ⟨⟨isPreBaseNorm E, bnComplete E⟩, fun _ _ h => E.seriesTo h⟩

end SigmaExtension


/-! ## SIG 57, 59: `sBBNS`, and the σ-weight module of its subbases -/

/-- **SIG 57** (main.tex:1639, Definition, text): the category `sBBNS`: Banach
pre-base-norm spaces with a σ-closed subbase, a full subcategory of `OVSt`. -/
structure SBBNS : Type (u + 1) where
  toOVSt : OVSt
  banach : toOVSt.IsBanachPBN
  sigma : toOVSt.SigmaClosedSubbase

namespace SBBNS

instance : Category SBBNS where
  Hom V W := V.toOVSt ⟶ W.toOVSt
  id V := 𝟙 V.toOVSt
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The inclusion `sBBNS ↪ OVSt`. -/
def incl : SBBNS ⥤ OVSt where
  obj V := V.toOVSt
  map f := f

instance : incl.Full := ⟨fun f => ⟨f, rfl⟩⟩
instance : incl.Faithful := ⟨fun h => h⟩

variable (V : SBBNS)

/-- The base norm, as a `Norm`. -/
noncomputable abbrev normI : Norm V.toOVSt.carrier := ⟨V.toOVSt.bnorm⟩

theorem core : @NormedSpace.Core ℝ V.toOVSt.carrier _ _ _ (normI V) := by
  letI := normI V
  exact
    { norm_nonneg := OVSt.bnorm_nonneg
      norm_smul := fun c x => by
        show V.toOVSt.bnorm (c • x) = ‖c‖ * V.toOVSt.bnorm x
        rw [OVSt.bnorm_smul, Real.norm_eq_abs]
      norm_triangle := OVSt.bnorm_add_le
      norm_eq_zero_iff := fun x => ⟨V.banach.1 x, fun h => h ▸ OVSt.bnorm_zero⟩ }

/-- The base norm makes `V` a normed space. -/
noncomputable abbrev nag : NormedAddCommGroup V.toOVSt.carrier :=
  letI := normI V
  NormedAddCommGroup.ofCore (core V)

noncomputable abbrev nsp : @NormedSpace ℝ V.toOVSt.carrier _ (nag V).toSeminormedAddCommGroup :=
  letI := nag V
  NormedSpace.ofCore (core V)

attribute [local instance] nag nsp

theorem norm_eq (x : V.toOVSt.carrier) : ‖x‖ = V.toOVSt.bnorm x := rfl

instance complete : CompleteSpace V.toOVSt.carrier := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨v, hv⟩ := V.banach.2 u (fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    exact ⟨N, fun m hm n hn => by
      have := hN m hm n hn; rwa [dist_eq_norm, norm_eq] at this⟩)
  exact ⟨v, Metric.tendsto_atTop.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hv ε hε
    exact ⟨N, fun n hn => by rw [dist_eq_norm, norm_eq]; exact hN n hn⟩⟩

/-- The trace as a continuous linear functional (`|τ x| ≤ ‖x‖`). -/
noncomputable def trL : V.toOVSt.carrier →L[ℝ] ℝ :=
  LinearMap.mkContinuous V.toOVSt.tr 1 fun x => by
    rw [one_mul, Real.norm_eq_abs, norm_eq]; exact OVSt.abs_tr_le x

theorem trL_apply (x : V.toOVSt.carrier) : trL V x = V.toOVSt.tr x :=
  LinearMap.mkContinuous_apply _ _ _ x

/-- `SeriesTo` is convergence of partial sums in the norm topology. -/
theorem seriesTo_iff (x : ℕ → V.toOVSt.carrier) (v : V.toOVSt.carrier) :
    V.toOVSt.SeriesTo x v ↔
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, x i) Filter.atTop (nhds v) := by
  rw [Metric.tendsto_atTop]
  refine forall₂_congr fun ε _ => exists_congr fun N => forall₂_congr fun n _ => ?_
  rw [dist_eq_norm, norm_eq]
  try exact Iff.rfl

variable {V}

/-- Summability for the subbase: finite partial traces are `≤ 1`. -/
def SSummable {J : Type} (x : J → SubB V.toOVSt) : Prop :=
  ∀ F : Finset J, ∑ j ∈ F, V.toOVSt.tr (x j).1 ≤ 1

theorem SSummable.real {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    Summable fun j => V.toOVSt.tr (x j).1 :=
  summable_of_sum_le (fun j => SubB.tr_nonneg (x j)) h

theorem SSummable.vec {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    Summable fun j => (x j).1 := by
  refine Summable.of_norm ?_
  simp only [norm_eq, OVSt.bnorm_of_nonneg (x _).2.1]
  exact h.real

theorem SSummable.tr_tsum {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    V.toOVSt.tr (∑' j, (x j).1) = ∑' j, V.toOVSt.tr (x j).1 := by
  rw [← trL_apply, (trL V).map_tsum h.vec]; simp only [trL_apply]

theorem SSummable.tr_le {J : Type} {x : J → SubB V.toOVSt} (h : SSummable x) :
    V.toOVSt.tr (∑' j, (x j).1) ≤ 1 := by
  rw [h.tr_tsum]; exact tsum_le_of_sum_le' zero_le_one h

/-- The sum of a summable family is again positive: the σ-closed subbase. -/
theorem SSummable.nonneg {J : Type} [Countable J] {x : J → SubB V.toOVSt} (h : SSummable x) :
    0 ≤ ∑' j, (x j).1 := by
  rcases finite_or_infinite J with hJ | hJ
  · haveI := Fintype.ofFinite J
    rw [tsum_fintype]; exact Finset.sum_nonneg fun j _ => (x j).2.1
  · obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := J)
    obtain ⟨v, hv0, -, hv⟩ := V.sigma (fun n => (x (e n)).1) (fun n => (x (e n)).2.1)
      (fun N => by
        have := h ((Finset.range N).map e.toEmbedding)
        rwa [Finset.sum_map] at this)
    have hs : HasSum (fun n => (x (e n)).1) (∑' j, (x j).1) :=
      (e.hasSum_iff (f := fun j => (x j).1)).2 h.vec.hasSum
    have := tendsto_nhds_unique hs.tendsto_sum_nat ((seriesTo_iff V _ _).1 hv)
    rw [this]; exact hv0

/-- The σ-sum of the subbase. -/
noncomputable def ssum {J : Type} [Countable J] (x : J → SubB V.toOVSt) (h : SSummable x) :
    SubB V.toOVSt :=
  ⟨∑' j, (x j).1, h.nonneg, h.tr_le⟩

theorem fibre_ssummable {J K : Type} {x : J → SubB V.toOVSt} (h : SSummable x) (p : J → K)
    (k : K) : SSummable (fun j : {j // p j = k} => x j.1) := fun F => by
  have := h (F.map (Function.Embedding.subtype _))
  rwa [Finset.sum_map] at this

theorem hasSum_fibre {J K : Type} {x : J → SubB V.toOVSt} (h : SSummable x) (p : J → K)
    {f : J → ℝ} (hf : HasSum f (∑' j, f j)) (hfs : Summable f) :
    HasSum (fun k => ∑' j : {j // p j = k}, f j.1) (∑' j, f j) := by
  have h1 : HasSum (f ∘ Equiv.sigmaFiberEquiv p) (∑' j, f j) :=
    ((Equiv.sigmaFiberEquiv p).hasSum_iff).2 hf
  exact h1.sigma fun k => (hfs.subtype _).hasSum

/-- The σ-PAM of the subbase of `V ∈ sBBNS`: summable iff the traces sum to
at most `1`, the sum being the sum of the series (in the base norm). -/
noncomputable instance spam (V : SBBNS) : SigmaPAM (SubB V.toOVSt) where
  Summable x := SSummable x
  sum x h := ssum x h
  nonempty := ⟨0⟩
  summable_iff_partition x p := by
    constructor
    · intro h
      refine ⟨fibre_ssummable h p, fun G => ?_⟩
      have hr := h.real
      have hK := hasSum_fibre h p hr.hasSum hr
      simp only [ssum]
      simp only [(fibre_ssummable h p _).tr_tsum]
      refine le_trans (sum_le_hasSum G (fun k _ => tsum_nonneg fun j => SubB.tr_nonneg _) hK) ?_
      exact tsum_le_of_sum_le' zero_le_one h
    · rintro ⟨hk, hK⟩ F
      classical
      rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := F.image p)
        (fun j hj => Finset.mem_image_of_mem p hj)]
      refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hK (F.image p))
      simp only [ssum]
      rw [(hk k).tr_tsum]
      have := sum_le_hasSum ((F.filter fun j => p j = k).subtype fun j => p j = k)
        (fun j _ => SubB.tr_nonneg (x j.1)) (hk k).real.hasSum
      refine le_trans (le_of_eq ?_) this
      have e := Finset.sum_map ((F.filter fun j => p j = k).subtype fun j => p j = k)
        (Function.Embedding.subtype fun j => p j = k) (fun j => V.toOVSt.tr (x j).1)
      rw [Finset.subtype_map, Finset.filter_filter] at e
      exact Eq.trans (Finset.sum_congr (by ext j; simp) (fun _ _ => rfl)) (e.trans rfl)
  sum_partition x p hx h h' := by
    refine SubB.ext ?_
    show ∑' j, (x j).1 = ∑' k, (ssum (fun j : {j // p j = k} => x j.1) (h k)).1
    have h1 : HasSum ((fun j => (x j).1) ∘ Equiv.sigmaFiberEquiv p) (∑' j, (x j).1) :=
      ((Equiv.sigmaFiberEquiv p).hasSum_iff).2 hx.vec.hasSum
    exact (h1.sigma fun k => (h k).vec.hasSum).tsum_eq.symm
  summable_unique x F := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      fun j _ _ => SubB.tr_nonneg (x j)) ?_
    rw [Fintype.sum_unique]; exact (x default).2.2
  sum_unique x h := SubB.ext (by
    show ∑' j, (x j).1 = (x default).1
    rw [tsum_fintype, Fintype.sum_unique])
  limit x h F := by
    have := h F Finset.univ
    rwa [Finset.sum_coe_sort F (fun j => V.toOVSt.tr (x j).1)] at this

theorem sumsTo_iff {J : Type} [Countable J] (x : J → SubB V.toOVSt) (s : SubB V.toOVSt) :
    SigmaPAM.SumsTo x s ↔ SSummable x ∧ HasSum (fun j => (x j).1) s.1 := by
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, h.vec.hasSum⟩
  · rintro ⟨h, hs⟩; exact ⟨h, SubB.ext hs.tsum_eq⟩

theorem zero_eq : (SigmaPAM.zero : SubB V.toOVSt) = 0 :=
  SubB.ext (by
    show ∑' j : Empty, (Empty.elim j : SubB V.toOVSt).1 = 0
    exact tsum_empty)

theorem sumsTo_pair_iff (a b s : SubB V.toOVSt) :
    SigmaPAM.SumsTo ![a, b] s ↔ V.toOVSt.tr a.1 + V.toOVSt.tr b.1 ≤ 1 ∧ s.1 = a.1 + b.1 := by
  rw [sumsTo_iff]
  have hfin : ∀ F : Finset (Fin 2), ∑ j ∈ F, V.toOVSt.tr (![a, b] j).1 ≤
      V.toOVSt.tr a.1 + V.toOVSt.tr b.1 := fun F => by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      fun j _ _ => SubB.tr_nonneg _) ?_
    rw [Fin.sum_univ_two]; rfl
  constructor
  · rintro ⟨h, hs⟩
    refine ⟨?_, ?_⟩
    · have := h Finset.univ; rwa [Fin.sum_univ_two] at this
    · rw [← hs.tsum_eq, tsum_fintype, Fin.sum_univ_two]; rfl
  · rintro ⟨h, hs⟩
    refine ⟨fun F => (hfin F).trans h, ?_⟩
    rw [hs]
    convert hasSum_fintype (fun j : Fin 2 => (![a, b] j).1) using 1
    rw [Fin.sum_univ_two]; rfl

/-- The `[0,1]`-action on the subbase respects canonical sums of scalars. -/
theorem sigmaObj_smul_left (x : SubB V.toOVSt) {J : Type} [Countable J] (r : J → I) (s : I)
    (h : IsCSum r s) : SigmaPAM.SumsTo (fun j => r j • x) (s • x) := by
    rw [sumsTo_iff]
    have hr := CW.hasSum_of_isCSum h
    have hc := (CW.csummable_I_iff r).1 h.1
    refine ⟨fun F => ?_, ?_⟩
    · simp only [SubB.smul_val, map_smul, smul_eq_mul]
      rw [← Finset.sum_mul]
      exact le_trans (mul_le_of_le_one_right (Finset.sum_nonneg fun j _ => (r j).2.1) x.2.2)
        (hc F)
    · simp only [SubB.smul_val]
      exact hr.smul_const x.1

theorem sigmaObj_smul_right (r : I) {J : Type} [Countable J] (x : J → SubB V.toOVSt)
    (s : SubB V.toOVSt) (h : SigmaPAM.SumsTo x s) : SigmaPAM.SumsTo (fun j => r • x j) (r • s) := by
    rw [sumsTo_iff] at h ⊢
    refine ⟨fun F => ?_, ?_⟩
    · simp only [SubB.smul_val, map_smul, smul_eq_mul]
      rw [← Finset.mul_sum]
      exact le_trans (mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => SubB.tr_nonneg _)
        r.2.2) (h.1 F)
    · simp only [SubB.smul_val]
      exact h.2.const_smul (r : ℝ)

theorem sigmaObj_weight_sumsTo {J : Type} [Countable J] (x : J → SubB V.toOVSt)
    (s : SubB V.toOVSt) (h : SigmaPAM.SumsTo x s) : IsCSum (fun j => wt (x j)) (wt s) := by
    rw [sumsTo_iff] at h
    refine CW.isCSum_of_hasSum ?_
    simp only [SubB.wt_val]
    exact (trL V).hasSum h.2

theorem sigmaObj_summable_of_weight {J : Type} [Countable J] (x : J → SubB V.toOVSt)
    (h : CSummable (fun j => wt (x j))) : SSummable x := by
    intro F
    have := (CW.csummable_I_iff _).1 h F
    simpa only [SubB.wt_val] using this

/-- **SIG 59** (proof, main.tex:3434), in universe `u`: the subbase of
`V ∈ sBBNS` is a σ-weight `[0,1]`-module (scalars lifted to `Type u`), whose
countable addition is given by sums of series. -/
noncomputable abbrev sigmaObj (V : SBBNS.{u}) : SWMod IU.{u} where
  carrier := SubB V.toOVSt
  pam := spam V
  act := ⟨fun r x => r.down • x⟩
  weight := fun x => ⟨wt x⟩
  one_smul := fun x => WeightMod.one_smul x
  mul_smul := fun r s x => WeightMod.mul_smul r.down s.down x
  smul_left x J _ r s h := sigmaObj_smul_left x (fun j => (r j).down) s.down (ul_isCSum_iff.1 h)
  smul_right r J _ x s h := sigmaObj_smul_right r.down x s h
  weight_sumsTo x s h := ul_isCSum_iff.2 (sigmaObj_weight_sumsTo x s h)
  weight_smul r x := congrArg ULift.up (WeightMod.wt_smul r.down x)
  eq_zero_of_weight x h := by
    rw [zero_eq]; exact WeightMod.eq_zero_of_wt x (congrArg ULift.down h)
  summable_of_weight x h := sigmaObj_summable_of_weight x (ul_csummable_iff.1 h)

end SBBNS


namespace SBBNS

attribute [local instance] nag nsp

theorem bnorm_map_le {V W : OVSt} (f : V ⟶ W) (x : V.carrier) :
    W.bnorm (f.toLin x) ≤ V.bnorm x :=
  OVSt.le_bnorm fun a b ha hb h => by
    have := OVSt.bnorm_le (x := f.toLin x) (f.pos a ha) (f.pos b hb) (by rw [h, map_sub])
    linarith [f.tr_le a ha, f.tr_le b hb]

/-- A morphism of `sBBNS` is bounded (norm-decreasing), hence continuous. -/
noncomputable def mapL {V W : SBBNS} (f : V ⟶ W) :
    V.toOVSt.carrier →L[ℝ] W.toOVSt.carrier :=
  LinearMap.mkContinuous f.toLin 1 fun x => by
    rw [one_mul, norm_eq, norm_eq]; exact bnorm_map_le f x

theorem mapL_apply {V W : SBBNS} (f : V ⟶ W) (x : V.toOVSt.carrier) : mapL f x = f.toLin x :=
  LinearMap.mkContinuous_apply _ _ _ x

/-- **SIG 59** (main.tex:1650, and its proof main.tex:3434): the functor
`sBase : sBBNS → sWMod[[0,1]]`, the subbase with sums of series. -/
noncomputable abbrev sBaseS : SBBNS.{u} ⥤ SWMod IU.{u} where
  obj V := sigmaObj V
  map {V W} f :=
    { toFun := fun x => ⟨f.toLin x.1, f.pos _ x.2.1, (f.tr_le _ x.2.1).trans x.2.2⟩
      sigma := fun x s h => by
        rw [sumsTo_iff] at h ⊢
        refine ⟨fun F => le_trans (Finset.sum_le_sum fun j _ => f.tr_le _ (x j).2.1) (h.1 F), ?_⟩
        have := (mapL f).hasSum h.2
        simp only [mapL_apply] at this
        exact this
      map_smul := fun r x => SubB.ext (map_smul f.toLin ((r.down : I) : ℝ) x.1)
      weight_le := fun x => (ul_le_iff _ _).2 (unitInterval_le_iff.2 (f.tr_le _ x.2.1)) }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem sBaseS_map_apply {V W : SBBNS} (f : V ⟶ W) (x : SubB V.toOVSt) :
    ((sBaseS.map f).toFun x).1 = f.toLin x.1 := rfl

instance sBaseS_faithful : sBaseS.Faithful where
  map_injective {V W} f g h := by
    refine OVSt.hom_ext fun x => ?_
    have := OVSt.linear_ext_subB (F := f.toLin) (G := g.toLin) fun a => by
      have := congrArg (fun φ : sBaseS.obj V ⟶ sBaseS.obj W => (φ.toFun a).1) h
      simpa [sBaseS_map_apply] using this
    rw [this]

/-- A morphism of σ-weight modules between subbases is a morphism of the
underlying (finite) weight modules. -/
noncomputable def toCW {V W : SBBNS} (φ : sBaseS.obj V ⟶ sBaseS.obj W) :
    sBase.obj V.toOVSt ⟶ sBase.obj W.toOVSt where
  toFun := φ.toFun
  additive := by
    refine ⟨?_, fun {a b} h => ?_⟩
    · have := φ.map_zero
      rw [zero_eq (V := V), zero_eq (V := W)] at this
      exact this
    · have hs : SigmaPAM.SumsTo ![a, b] (ovee a b h) := (sumsTo_pair_iff _ _ _).2 ⟨h, rfl⟩
      have := φ.sigma _ _ hs
      have e : (fun j => φ.toFun (![a, b] j)) = ![φ.toFun a, φ.toFun b] := by
        funext j; fin_cases j <;> rfl
      rw [e, sumsTo_pair_iff] at this
      exact ⟨this.1, SubB.ext this.2.symm⟩
  map_smul := fun r a => φ.map_smul ⟨r⟩ a
  wt_le x := unitInterval_le_iff.1 ((ul_le_iff _ _).1 (φ.weight_le x))

instance sBaseS_full : sBaseS.Full where
  map_surjective {V W} φ := by
    refine ⟨cwExtHom (toCW φ), SWMod.hom_ext fun a => ?_⟩
    have := congrArg (fun ψ : sBase.obj V.toOVSt ⟶ sBase.obj W.toOVSt => ψ.toFun a)
      (sBase_map_extHom (toCW φ))
    exact SubB.ext (congrArg Subtype.val this)

theorem sBaseS_cancellative (V : SBBNS) : (sBaseS.obj V).IsCancellative := by
  intro x y z s hy hz
  rw [sumsTo_pair_iff] at hy hz
  exact SubB.ext (add_left_cancel (hy.2.symm.trans hz.2))

end SBBNS

/-- **SIG 57** (main.tex:1643, Definition, text): the category `sCWMod[[0,1]]` of
cancellative σ-weight `[0,1]`-modules, a full subcategory of `sWMod[[0,1]]`. -/
structure SCWMod : Type (u + 1) where
  toSWMod : SWMod IU.{u}
  cancel : toSWMod.IsCancellative

namespace SCWMod

noncomputable instance : Category SCWMod where
  Hom X Y := X.toSWMod ⟶ Y.toSWMod
  id X := 𝟙 X.toSWMod
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The inclusion `sCWMod ↪ sWMod`. -/
noncomputable def incl : SCWMod.{u} ⥤ SWMod IU.{u} where
  obj X := X.toSWMod
  map f := f

instance : incl.Full := ⟨fun f => ⟨f, rfl⟩⟩
instance : incl.Faithful := ⟨fun h => h⟩

end SCWMod

/-! ### The inverse construction for SIG 59 -/

section WModOfU

variable (X : SWMod IU.{u})

/-- The finite weight-module structure underlying a σ-weight module over the
lifted `[0,1]` (its PCM is the one derived from its σ-PAM). -/
noncomputable def wmodOfU : @WeightMod X.carrier SigmaPAM.toPCM :=
  letI : PCM X.carrier := SigmaPAM.toPCM
  { toSMul := smulI X
    wt := wI X
    mul_smul := fun r s x => X.mul_smul ⟨r⟩ ⟨s⟩ x
    one_smul := X.one_smul
    smul_perp := fun l {a b} h => by
      have := smul_right_I X l ![a, b] _ ((SigmaPAM.toPCM_sumsTo_iff a b _).1 ⟨h, rfl⟩)
      have e : (fun j => l • ![a, b] j) = ![l • a, l • b] := by funext j; fin_cases j <;> rfl
      rw [e] at this
      exact (SigmaPAM.toPCM_sumsTo_iff _ _ _).2 this
    perp_smul := fun {l m} h a => by
      have := smul_left_I X a ![l, m] _ ((isCSum_pair_iff l m _).2 ⟨h, rfl⟩)
      have e : (fun j => ![l, m] j • a) = ![l • a, m • a] := by funext j; fin_cases j <;> rfl
      rw [e] at this
      exact (SigmaPAM.toPCM_sumsTo_iff _ _ _).2 this
    smul_zero := fun l => X.smul_zero ⟨l⟩
    zero_smul := fun a => by
      have := smul_left_I X a (Empty.elim : Empty → I) 0 (isCSum_of_isEmpty _)
      exact this.unique (SigmaPAM.sumsTo_of_isEmpty _)
    wt_zero := wI_zero X
    wt_ovee := fun {a b} h => by
      have := wI_sumsTo X ![a, b] _ ((SigmaPAM.toPCM_sumsTo_iff a b _).1 ⟨h, rfl⟩)
      have e : (fun j => wI X (![a, b] j)) = ![wI X a, wI X b] := by
        funext j; fin_cases j <;> rfl
      rw [e, isCSum_pair_iff] at this
      obtain ⟨hp, hs⟩ := this
      rw [← hs, GP.I_coe_ovee]
    wt_smul := wI_smul X
    eq_zero_of_wt := eq_zero_of_wI X
    perp_of_wt := fun {a b} h => by
      refine summable_of_wI X ![a, b] ((CW.csummable_I_iff _).2 fun F => ?_)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        fun j _ _ => (wI X _).2.1) ?_
      rw [Fin.sum_univ_two]; exact h }

/-- The cancellative (finite) weight module of a cancellative σ-weight
module over the lifted `[0,1]`. -/
noncomputable def toCWU (hX : X.IsCancellative) : CWMod.{u} :=
  @CWMod.mk X.carrier SigmaPAM.toPCM (wmodOfU X) (by
    letI : PCM X.carrier := SigmaPAM.toPCM
    intro x y z hy hz h
    exact hX x y z _ ((SigmaPAM.toPCM_sumsTo_iff _ _ _).1 ⟨hy, rfl⟩)
      ((SigmaPAM.toPCM_sumsTo_iff _ _ _).1 ⟨hz, h.symm⟩))

end WModOfU

section EssS

variable (X : SWMod IU.{u}) (hX : X.IsCancellative)

/-- The bijection `X ≃ sBase V(X)`. -/
noncomputable def cwEquiv : X.carrier ≃ SubB (vOf (toCWU X hX)) where
  toFun := (toVOf (toCWU X hX)).toFun
  invFun := (fromVOf (toCWU X hX)).toFun
  left_inv a := congrArg (fun φ : toCWU X hX ⟶ toCWU X hX => φ.toFun a) (vOfIso (toCWU X hX)).inv_hom_id
  right_inv x := congrArg (fun φ : sBase.obj (vOf (toCWU X hX)) ⟶ sBase.obj (vOf (toCWU X hX)) =>
    φ.toFun x) (vOfIso (toCWU X hX)).hom_inv_id

/-- `X` is a σ-structure on `sBase V(X)` extending its weight-module
structure. -/
noncomputable def cwExt : SigmaExtension (vOf (toCWU X hX)) X where
  e := cwEquiv X hX
  map_smul r a := (toVOf (toCWU X hX)).map_smul r a
  wt_eq a := (CW.tr_gmap (X := (toCWU X hX).carrier) a).symm
  pair x y s := by
    constructor
    · rintro ⟨hp, hs⟩
      obtain ⟨h', e⟩ := (toVOf (toCWU X hX)).additive.2 (hp : @Perp (toCWU X hX).carrier _ x y)
      refine ⟨h', ?_⟩
      have e' := congrArg Subtype.val e
      subst hs
      exact e'.symm
    · rintro ⟨h1, h2⟩
      have hp := (@CW.gmap_perp_iff (toCWU X hX).carrier _ _ ⟨(toCWU X hX).cancel⟩ x y).2 h1
      refine ⟨hp, ?_⟩
      refine (cwEquiv X hX).injective (SubB.ext ?_)
      show @CW.gmap (toCWU X hX).carrier _ _ ⟨(toCWU X hX).cancel⟩
        (@ovee (toCWU X hX).carrier _ x y hp) = _
      rw [CW.gmap_ovee hp]; exact h2.symm

theorem cw_sigmaClosed : (vOf (toCWU X hX)).SigmaClosedSubbase := by
  intro y hy hsum
  have hy1 : ∀ n, (vOf (toCWU X hX)).tr (y n) ≤ 1 := fun n => by
    have := hsum (n + 1)
    rw [Finset.sum_range_succ] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) =>
      (vOf (toCWU X hX)).tr_nonneg (hy i)]
  let E := cwExt X hX
  let xs : ℕ → X.carrier := fun n => E.ofVec (y n) (hy n) (hy1 n)
  have hs : SigmaPAM.Summable xs := summable_of_wI X xs ((CW.csummable_I_iff _).2 fun F => by
    obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range F
    simp only [xs, E.wt_eq, SigmaExtension.e_ofVec]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hM
      fun i _ _ => (vOf (toCWU X hX)).tr_nonneg (hy i)) (hsum M))
  refine ⟨(E.e (SigmaPAM.sum xs hs)).1, (E.e _).2.1, (E.e _).2.2, ?_⟩
  have := E.seriesTo (SigmaPAM.sumsTo_sum hs)
  simpa only [xs, SigmaExtension.e_ofVec] using this

/-- The object `V(X)` of `sBBNS`. -/
noncomputable def sbbnsOf : SBBNS :=
  ⟨vOf (toCWU X hX), ((cwExt X hX).sig73).1, cw_sigmaClosed X hX⟩

attribute [local instance] SBBNS.nag SBBNS.nsp

/-- `cwEquiv`, with codomain the subbase of `V(X) ∈ sBBNS`. -/
noncomputable def cwEquivS : X.carrier ≃ SubB (sbbnsOf X hX).toOVSt := cwEquiv X hX

theorem cwEquivS_tr (a : X.carrier) :
    (sbbnsOf X hX).toOVSt.tr (cwEquivS X hX a).1 = wI X a :=
  ((cwExt X hX).wt_eq a).symm

theorem cwEquivS_smul (r : I) (a : X.carrier) :
    cwEquivS X hX (r • a) = r • cwEquivS X hX a :=
  (cwExt X hX).map_smul r a

theorem cw_sumsTo {J : Type} [Countable J] {x : J → X.carrier} {s : X.carrier}
    (h : SigmaPAM.SumsTo x s) :
    @SigmaPAM.SumsTo (SubB (sbbnsOf X hX).toOVSt) (SBBNS.spam _) J _
      (fun j => cwEquivS X hX (x j)) (cwEquivS X hX s) := by
  let V := sbbnsOf X hX
  let E := cwExt X hX
  have hss : SBBNS.SSummable (V := V) fun j => cwEquivS X hX (x j) := fun F => by
    have := (CW.csummable_I_iff _).1 (wI_sumsTo X x s h).1 F
    simpa only [← cwEquivS_tr X hX] using this
  refine (SBBNS.sumsTo_iff (V := V) _ _).2 ⟨hss, ?_⟩
  have hS := (SBBNS.SSummable.vec hss).hasSum
  rcases finite_or_infinite J with hJ | hJ
  · haveI := Fintype.ofFinite J
    have e := (Fintype.equivFin J).symm
    have h' : SigmaPAM.SumsTo (x ∘ e) s := (SigmaPAM.sumsTo_comp_equiv e x s).2 h
    have hfs : ((cwEquivS X hX s).1 : V.toOVSt.carrier)
        = ∑ i, ((cwEquivS X hX (x (e i))).1 : V.toOVSt.carrier) := E.fin_sum _ _ s h'
    rw [hfs, Equiv.sum_comp e (fun j => ((cwEquivS X hX (x j)).1 : V.toOVSt.carrier))]
    exact hasSum_fintype _
  · obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := J)
    have h' : SigmaPAM.SumsTo (x ∘ e) s := (SigmaPAM.sumsTo_comp_equiv e x s).2 h
    have hser := (SBBNS.seriesTo_iff V _ _).1 (E.seriesTo h')
    have hS' : HasSum (fun n => ((cwEquivS X hX (x (e n))).1 : V.toOVSt.carrier))
        (∑' j, ((cwEquivS X hX (x j)).1 : V.toOVSt.carrier)) :=
      (e.hasSum_iff (f := fun j => ((cwEquivS X hX (x j)).1 : V.toOVSt.carrier))).2 hS
    have := tendsto_nhds_unique hS'.tendsto_sum_nat hser
    rw [this] at hS
    exact hS

/-- `sBase V(X) ≅ X` in `sWMod[[0,1]]`. -/
noncomputable def sbbnsIso : SBBNS.sBaseS.obj (sbbnsOf X hX) ≅ X where
  hom :=
    { toFun := (cwEquivS X hX).symm
      sigma := fun y t h => by
        have h0 := (SBBNS.sumsTo_iff (V := sbbnsOf X hX) y t).1 h
        have hs : SigmaPAM.Summable (fun j => (cwEquivS X hX).symm (y j)) :=
          summable_of_wI X _ ((CW.csummable_I_iff _).2 fun F => by
            have := h0.1 F
            simpa only [← cwEquivS_tr X hX, Equiv.apply_symm_apply] using this)
        have h2 := (SBBNS.sumsTo_iff (V := sbbnsOf X hX) _ _).1
          (cw_sumsTo X hX (SigmaPAM.sumsTo_sum hs))
        simp only [Equiv.apply_symm_apply] at h2
        have ht := h2.2.unique h0.2
        have : SigmaPAM.sum _ hs = (cwEquivS X hX).symm t := by
          rw [Equiv.eq_symm_apply]; exact SubB.ext ht
        rw [← this]; exact SigmaPAM.sumsTo_sum hs
      map_smul := fun r y => (cwEquivS X hX).symm_apply_eq.2
        ((cwEquivS_smul X hX r.down _).trans
          (congrArg (fun z => r.down • z) ((cwEquivS X hX).apply_symm_apply y))).symm
      weight_le := fun y => by
        have h1 := cwEquivS_tr X hX ((cwEquivS X hX).symm y)
        rw [Equiv.apply_symm_apply] at h1
        exact (ul_le_iff _ _).2 (unitInterval_le_iff.2 (le_of_eq (h1.symm.trans rfl))) }
  inv :=
    { toFun := cwEquivS X hX
      sigma := fun x s h => cw_sumsTo X hX h
      map_smul := fun r x => cwEquivS_smul X hX r.down x
      weight_le := fun x =>
        (ul_le_iff _ _).2 (unitInterval_le_iff.2 (le_of_eq ((cwEquivS_tr X hX x).trans rfl))) }
  hom_inv_id := SWMod.hom_ext fun y => (cwEquivS X hX).apply_symm_apply y
  inv_hom_id := SWMod.hom_ext fun x => (cwEquivS X hX).symm_apply_apply x

end EssS

/-- **SIG 59** (`prop:sBBNS-equiv-sCWMod`, main.tex:1650, Proposition): the
functor `sBase : sBBNS → sCWMod[[0,1]]`, landing in the cancellative σ-weight
modules. -/
noncomputable def sBaseC : SBBNS ⥤ SCWMod where
  obj V := ⟨SBBNS.sBaseS.obj V, SBBNS.sBaseS_cancellative V⟩
  map f := SBBNS.sBaseS.map f
  map_id V := SBBNS.sBaseS.map_id V
  map_comp f g := SBBNS.sBaseS.map_comp f g

instance : sBaseC.Faithful := ⟨fun h => SBBNS.sBaseS.map_injective h⟩
instance : sBaseC.Full := ⟨fun f => SBBNS.sBaseS.map_surjective (X := _) (Y := _) f⟩
instance : sBaseC.EssSurj := ⟨fun X => ⟨sbbnsOf X.toSWMod X.cancel,
  ⟨{ hom := (sbbnsIso X.toSWMod X.cancel).hom, inv := (sbbnsIso X.toSWMod X.cancel).inv,
     hom_inv_id := (sbbnsIso X.toSWMod X.cancel).hom_inv_id,
     inv_hom_id := (sbbnsIso X.toSWMod X.cancel).inv_hom_id }⟩⟩⟩

/-- **SIG 59** (`prop:sBBNS-equiv-sCWMod`, main.tex:1650, Proposition): there
is an equivalence of categories `sBBNS ≃ sCWMod[[0,1]]`.  Proof as printed:
the subbase of `V ∈ sBBNS` is a σ-weight module under sums of series
(`SBBNS.sigmaObj`); conversely, for a cancellative σ-weight module `X`, SIG 73
makes `V(X)` of SIG 58 a Banach pre-base-norm space with a σ-closed subbase,
and the σ-sums of `X` are the sums of series (`cw_hasSum`); fullness is
SIG 58's extension, which is automatically σ-normal. -/
instance sBaseC_isEquivalence : sBaseC.IsEquivalence where

/-- For theorem 60: the essential image of `sBase : sBBNS → sWMod[[0,1]]` is
the cancellative modules. -/
theorem sBaseS_essImage (X : SWMod IU.{u}) (hX : X.IsCancellative) :
    ∃ V : SBBNS, Nonempty (SBBNS.sBaseS.obj V ≅ X) :=
  ⟨sbbnsOf X hX, ⟨sbbnsIso X hX⟩⟩

/-- The unit object `[0,1]` of `sWMod[[0,1]]` (lifted) is cancellative. -/
theorem unitIU_isCancellative : (SWMod.unit IU.{u} iu_isSigmaEffectMonoid).IsCancellative := by
  intro x y z s hy hz
  have hy' := ul_isCSum_iff.1 ((canonical_sumsTo_iff iu_isSigmaEffectMonoid.1 _ _).1 hy)
  have hz' := ul_isCSum_iff.1 ((canonical_sumsTo_iff iu_isSigmaEffectMonoid.1 _ _).1 hz)
  have e1 : (fun j => (![x, y] j : IU.{u}).down) = ![x.down, y.down] := by
    funext j; fin_cases j <;> rfl
  have e2 : (fun j => (![x, z] j : IU.{u}).down) = ![x.down, z.down] := by
    funext j; fin_cases j <;> rfl
  rw [e1] at hy'
  rw [e2] at hz'
  obtain ⟨hpy, ey⟩ := (isCSum_pair_iff _ _ _).1 hy'
  obtain ⟨hpz, ez⟩ := (isCSum_pair_iff _ _ _).1 hz'
  have f1 := (GP.I_coe_ovee hpy).symm.trans (congrArg Subtype.val ey)
  have f2 := (GP.I_coe_ovee hpz).symm.trans (congrArg Subtype.val ez)
  exact congrArg ULift.up (Subtype.ext (by linarith))

/-- Countable coproducts of cancellative σ-weight modules are cancellative. -/
theorem coprod_isCancellativeU {M : Type u} [EffectMonoid M] [Fact (IsSigmaEffectMonoid M)]
    {Λ : Type} [Countable Λ] (X : Λ → SWMod M) (h : ∀ l, (X l).IsCancellative) :
    (SWMod.coprod X).IsCancellative := by
  intro x y z s hy hz
  have hy' := (SWMod.coprod_sumsTo_iff X _ _).1 hy
  have hz' := (SWMod.coprod_sumsTo_iff X _ _).1 hz
  refine Subtype.ext (funext fun l => h l (x.1 l) (y.1 l) (z.1 l) (s.1 l) ?_ ?_)
  · refine (SigmaPAM.sumsTo_congr fun j => ?_).1 (hy' l); fin_cases j <;> rfl
  · refine (SigmaPAM.sumsTo_congr fun j => ?_).1 (hz' l); fin_cases j <;> rfl


/-! ## `sBBNS` is a σ-effectus -/

section SBBNSEffectus

open SigmaPAM

instance fact_iu_sigma : Fact (IsSigmaEffectMonoid IU.{u}) :=
  ⟨iu_isSigmaEffectMonoid⟩

/-- The essential image of `sBase : sBBNS → sWMod[[0,1]]` (the cancellative
modules, SIG 59) is closed under countable coproducts. -/
theorem sbbns_hcop (J : Type) [Countable J] (X : J → SBBNS) :
    ∃ Y : SBBNS, Nonempty (SBBNS.sBaseS.obj Y ≅ ∐ fun j => SBBNS.sBaseS.obj (X j)) := by
  obtain ⟨Y, ⟨e⟩⟩ := sBaseS_essImage (SWMod.coprod fun j => SBBNS.sBaseS.obj (X j))
    (coprod_isCancellativeU _ fun j => SBBNS.sBaseS_cancellative (X j))
  exact ⟨Y, ⟨e ≪≫ (SWMod.coprodIsoC _).symm⟩⟩

/-- `sBBNS` has countable coproducts (SIG 59: those of `sWMod[[0,1]]`). -/
instance : HasCountableCoproducts SBBNS :=
  hasCountableCoproducts_of_ff SBBNS.sBaseS sbbns_hcop

/-- The hom-sets of `sBBNS` as σ-PAMs, transported along SIG 59. -/
noncomputable instance sbbnsHomPAM (X Y : SBBNS) : SigmaPAM (X ⟶ Y) :=
  SigmaPAM.ofEquiv ((Functor.FullyFaithful.ofFullyFaithful SBBNS.sBaseS).homEquiv)

theorem sbbns_sumsCompatible : SumsCompatible SBBNS.sBaseS :=
  fun x s => SigmaPAM.ofEquiv_sumsTo_iff _ x s

/-- The unit object of `sBBNS` (a base-norm space with subbase `[0,1]`). -/
noncomputable def sbbnsUnit : SBBNS :=
  (sBaseS_essImage (SWMod.unit IU.{u} iu_isSigmaEffectMonoid)
    unitIU_isCancellative).choose

noncomputable def sbbnsUnitIso :
    SBBNS.sBaseS.obj sbbnsUnit ≅ SigmaEffectus.«I» (C := SWMod IU.{u}) :=
  (sBaseS_essImage (SWMod.unit IU.{u} iu_isSigmaEffectMonoid)
    unitIU_isCancellative).choose_spec.some

/-- **SIG 59** (main.tex:1653): "As `sCWMod[[0,1]]` is a full subcategory of
`sWMod[[0,1]]`, it is a σ-effectus, and hence so is `sBBNS`": the structure
transported along the fully faithful `sBase : sBBNS → sWMod[[0,1]]`. -/
noncomputable instance sbbns_sigmaEffectus : SigmaEffectus SBBNS :=
  sbbns_sumsCompatible.sigmaEffectus sbbnsUnit sbbnsUnitIso
    (preserves_of_ff SBBNS.sBaseS sbbns_hcop)

/-- `sBase : sBBNS → sWMod[[0,1]]` is a morphism of σ-effectuses. -/
noncomputable def sbbnsMorphism : SigmaEffectusMorphism SBBNS.{u} (SWMod IU.{u}) :=
  sbbns_sumsCompatible.morphism sbbnsUnit sbbnsUnitIso
    (preserves_of_ff SBBNS.sBaseS sbbns_hcop)

end SBBNSEffectus
end U

section SIG60U

variable {C : Type u} [Category.{u} C] [HasCountableCoproducts C]
  [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]

/-- **SIG 60** (`thm:convex-effectus-embedding-2`, main.tex:1659, Theorem),
for a σ-effectus `C : Type u` with hom-sets in `Type u`, in every universe
`u` (`sig60` is the case `u = 0`): a state-separated σ-effectus with scalars
`[0,1]` whose substates are cancellative has a faithful morphism of
σ-effectuses `G : C → sBBNS` (`sBBNS` in universe `u`, `U.SBBNS`), with
`sSt(A) ≅ sBase(GA)` as σ-weight modules over `C(I,I)ᵒᵖ`.  Proof as `sig60`,
over `U.sbbnsMorphism` (SIG 59 in universe `u`). -/
theorem sig60U (hsep : StateSeparated C) (φ : EffectMonoidHom (Scal C) unitInterval)
    (ψ : EffectMonoidHom unitInterval (Scal C)) (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a)
    (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b) (hcanc : ∀ A : C, (sStObj A).IsCancellative) :
    ∃ (G : SigmaEffectusMorphism C U.SBBNS.{u})
      (hφ : IsSigmaAdditiveC (emHomComp iuUp.{u} (emHomToMOp φ)).toFun)
      (hψ : IsSigmaAdditiveC (emHomComp (emHomFromMOp ψ) iuDown.{u}).toFun), G.F.Faithful ∧
      ∀ A : C, Nonempty (sStObj A ≅ restrictSWObj (emHomComp iuUp.{u} (emHomToMOp φ)) hφ
        (emHomComp (emHomFromMOp ψ) iuDown.{u}) hψ (fun a => hψφ a)
        (fun b => congrArg ULift.up (hφψ b.down)) (U.SBBNS.sBaseS.obj (G.F.obj A))) := by
  let φ' : EffectMonoidHom (MOp (Scal C)) IU.{u} := emHomComp iuUp (emHomToMOp φ)
  let ψ' : EffectMonoidHom IU.{u} (MOp (Scal C)) := emHomComp (emHomFromMOp ψ) iuDown
  have hψφ' : ∀ a, ψ'.toFun (φ'.toFun a) = a := fun a => hψφ a
  have hφψ' : ∀ b, φ'.toFun (ψ'.toFun b) = b := fun b => congrArg ULift.up (hφψ b.down)
  have hφ : IsSigmaAdditiveC φ'.toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive φ') (emHom_isAdditive ψ') hψφ' hφψ'
  have hψ : IsSigmaAdditiveC ψ'.toFun :=
    isSigmaAdditiveC_of_inverse (emHom_isAdditive ψ') (emHom_isAdditive φ') hφψ' hψφ'
  let B := restrictSWMorphism φ' hφ ψ' hψ hψφ' hφψ'
  let G := sigmaMorphismComp U.sbbnsMorphism B
  have := restrictSWFunctor_full φ' hφ ψ' hψ hψφ' hφψ'
  have : G.F.Full := by
    show (U.SBBNS.sBaseS ⋙ restrictSWFunctor _ hφ _ hψ hψφ' hφψ').Full
    infer_instance
  have := restrictSWFunctor_faithful φ' hφ ψ' hψ hψφ' hφψ'
  have := U.SBBNS.sBaseS_faithful
  have : G.F.Faithful := by
    show (U.SBBNS.sBaseS ⋙ restrictSWFunctor _ hφ _ hψ hψφ' hφψ').Faithful
    infer_instance
  let Φ := sStMorphism (C := C)
  have h : ∀ A : C, ∃ Y : U.SBBNS.{u}, Nonempty (G.F.obj Y ≅ Φ.F.obj A) := by
    intro A
    obtain ⟨Y, ⟨e⟩⟩ := U.sBaseS_essImage
      (restrictSWObj ψ' hψ φ' hφ hφψ' hψφ' (sStObj A)) (hcanc A)
    exact ⟨Y, ⟨(restrictSWFunctor φ' hφ ψ' hψ hψφ' hφψ').mapIso e ≪≫
      restrictSWRoundTrip φ' hφ ψ' hψ hψφ' hφψ' (sStObj A)⟩⟩
  have hN : AdmitsNormalisation C :=
    admitsNormalisation_of_noZeroDivisors
      (EMIso.noZeroDivisors ⟨φ, ψ, hψφ, hφψ⟩ emNoZeroDivisors_unitInterval)
  have hsst : (sStFunctor (C := C)).Faithful :=
    substateSeparated_iff_faithful.1 ((stateSeparated_iff_substateSeparated hN).1 hsep)
  refine ⟨liftMorphism G Φ h, hφ, hψ, ?_, fun A => ?_⟩
  · have : Φ.F.Faithful := hsst
    exact liftMorphism_faithful G Φ h
  · exact ⟨((liftIso G Φ h).app A).symm⟩

/-- **SIG 61** (main.tex:1667, Remark), second sentence, in every universe
(`sig61` is the case `u = 0`): a state- and predicate-separated σ-effectus
`C : Type u` (hom-sets in `Type u`) with scalars `[0,1]` embeds (faithful
morphisms of σ-effectuses) into both `sBBNS` and `sBOUSᵒᵖ` (in universe `u`):
SIG 60 and SIG 56 in universe `u` (`sig60U`, `sig56U`) and the first sentence
(`sig61_cancellative`). -/
theorem sig61U (hstate : StateSeparated C) (hpred : PredicateSeparated C)
    (φ : EffectMonoidHom (Scal C) unitInterval) (ψ : EffectMonoidHom unitInterval (Scal C))
    (hψφ : ∀ a, ψ.toFun (φ.toFun a) = a) (hφψ : ∀ b, φ.toFun (ψ.toFun b) = b) :
    (∃ G : SigmaEffectusMorphism C U.SBBNS.{u}, G.F.Faithful) ∧
      ∃ F : SigmaEffectusMorphism C SBOUSU.{u}ᵒᵖ, F.F.Faithful := by
  obtain ⟨G, -, -, hG, -⟩ := sig60U hstate φ ψ hψφ hφψ (sig61_cancellative hpred)
  obtain ⟨F, -, hF, -⟩ := sig56U hpred φ ψ hψφ hφψ
  exact ⟨⟨G, hG⟩, ⟨F, hF⟩⟩

end SIG60U

end Papers.SIG
