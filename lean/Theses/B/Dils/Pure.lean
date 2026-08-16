/-
Thesis B (Bas Westerbaan, *Dagger and Dilation in the Category of Von
Neumann Algebras*, arXiv:1803.01911), chapter 2: Dilations — dils.tex,
lines 5966–6550.

  parsec 1680:  introduction to pure maps
  parsec 1690:  corners and filters
  parsec 1700:  pure maps
  parsec 1710:  the Paschke dilation of a corner; pure ⟺ ϱ surjective
  parsec 1720:  ncp-extreme maps

All von Neumann algebras live in one universe `u`.  The corner algebras
`pAp` appear as the type `cornerSet A p` (a subtype); their C*-, order- and
von Neumann structure — proc.tex **94II**, with unit `p` — is *proved*
below rather than asserted.  Corners and filters (proc.tex parsecs 950–980
of thesis A) are defined here from scratch following **169II** and
**169VIII**; `Theses/A/Proc/Measurement.lean` has since acquired a parallel
development, which should be merged with this one once `Theses.A.Proc` is
on this chapter's import path.
-/
import Theses.B.Dils.SelfDual

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u

namespace Theses.B.Dils

/-! **168I**–**168IV** (dils.tex:5968–6054, `dils-pure-discussion`):
introduction and discussion of rejected alternative notions of purity —
nothing to formalize. -/

/-! ## The corner algebra `pAp` -/

section CornerSet

variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **corner algebra** `pAp = {a : p a p = a}` of `A` at `p` (used for
a projection, or with `⌊a⌋` for an effect `a`; cf. proc.tex 94I). -/
def cornerSet (p : A) : Type u :=
  {a : A // p * a * p = a}

/-! ### The algebraic structure of `pAp`

Every operation below is carried by `Subtype.val` from `A`, except the
unit, which is `p`.  These are the ingredients out of which the three
instances of proc.tex **94II** parts 5–6 — and the von Neumann structure of
part 8 — are assembled; they are arranged so that `Subtype.val` is a
non-unital ∗-algebra isometry onto the norm-closed set `{a | p·a·p = a}`.

The projection hypothesis is not decoration: for a non-idempotent `p` the
set `{a | p·a·p = a}` is not closed under multiplication (`p(ab)p =
p²ap·pbp²`), so `cornerSet A p` carries no ring structure whatsoever and
the instances are *false* as unconditional statements.  They are therefore
guarded by `[Fact (IsStarProjection p)]`, which for the `⌊a⌋`, `⌈a⌉` of
this chapter is discharged automatically by `fact_isStarProjection_floor`
and `fact_isStarProjection_ceil` below.

`Theses/A/Proc/Measurement.lean` carries the *same* construction for its
own bundled corner type `Theses.A.Proc.Corner A e`; the two should be
merged once `Theses.A.Proc` is on this chapter's import path. -/

namespace cornerSet

set_option linter.unusedSectionVars false

variable {A}

theorem val_injective {p : A} :
    Function.Injective (Subtype.val : cornerSet A p → A) :=
  fun _ _ h => Subtype.ext h

/-- The corner is norm-closed: it is the zero set of the continuous map
`a ↦ p·a·p − a`. -/
theorem isClosed_setOf (p : A) : IsClosed {a : A | p * a * p = a} := by
  have hcont : Continuous (fun a : A => p * a * p - a) := by fun_prop
  have h : {a : A | p * a * p = a} = (fun a : A => p * a * p - a) ⁻¹' {0} := by
    ext a; simp [sub_eq_zero]
  rw [h]
  exact isClosed_singleton.preimage hcont

theorem range_val (p : A) :
    Set.range (Subtype.val : cornerSet A p → A) = {a : A | p * a * p = a} := by
  ext a
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩

section Proj

variable {p : A} [hFp : Fact (IsStarProjection p)]

/-- The projection hypothesis carried by the `Fact` instance. -/
theorem proj (p : A) [hFp : Fact (IsStarProjection p)] : IsStarProjection p :=
  hFp.out

theorem mul_left (a : cornerSet A p) : p * a.1 = a.1 := by
  have hpp : p * p = p := (proj p).isIdempotentElem.eq
  calc p * a.1 = p * (p * a.1 * p) := by rw [a.2]
    _ = (p * p) * a.1 * p := by noncomm_ring
    _ = p * a.1 * p := by rw [hpp]
    _ = a.1 := a.2

theorem mul_right (a : cornerSet A p) : a.1 * p = a.1 := by
  have hpp : p * p = p := (proj p).isIdempotentElem.eq
  calc a.1 * p = (p * a.1 * p) * p := by rw [a.2]
    _ = p * a.1 * (p * p) := by noncomm_ring
    _ = p * a.1 * p := by rw [hpp]
    _ = a.1 := a.2

instance : Zero (cornerSet A p) := ⟨⟨0, by simp⟩⟩
instance : Add (cornerSet A p) :=
  ⟨fun a b => ⟨a.1 + b.1, by rw [mul_add, add_mul, a.2, b.2]⟩⟩
instance : Neg (cornerSet A p) := ⟨fun a => ⟨-a.1, by rw [mul_neg, neg_mul, a.2]⟩⟩
instance : Sub (cornerSet A p) :=
  ⟨fun a b => ⟨a.1 - b.1, by rw [mul_sub, sub_mul, a.2, b.2]⟩⟩
instance : SMul ℕ (cornerSet A p) :=
  ⟨fun n a => ⟨n • a.1, by rw [mul_smul_comm, smul_mul_assoc, a.2]⟩⟩
instance : SMul ℤ (cornerSet A p) :=
  ⟨fun n a => ⟨n • a.1, by rw [mul_smul_comm, smul_mul_assoc, a.2]⟩⟩
instance : SMul ℂ (cornerSet A p) :=
  ⟨fun z a => ⟨z • a.1, by rw [mul_smul_comm, smul_mul_assoc, a.2]⟩⟩
instance : One (cornerSet A p) :=
  ⟨⟨p, by rw [(proj p).isIdempotentElem.eq, (proj p).isIdempotentElem.eq]⟩⟩
instance : Mul (cornerSet A p) :=
  ⟨fun a b => ⟨a.1 * b.1, by
    have h1 := mul_left a
    have h2 := mul_right b
    calc p * (a.1 * b.1) * p = (p * a.1) * (b.1 * p) := by noncomm_ring
      _ = a.1 * b.1 := by rw [h1, h2]⟩⟩
instance : Star (cornerSet A p) :=
  ⟨fun a => ⟨star a.1, by
    have hs : star p = p := (proj p).isSelfAdjoint.star_eq
    conv_rhs => rw [← a.2]
    rw [star_mul, star_mul, hs, mul_assoc]⟩⟩

@[simp] theorem val_zero : (0 : cornerSet A p).1 = 0 := rfl
@[simp] theorem val_add (a b : cornerSet A p) : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem val_neg (a : cornerSet A p) : (-a).1 = -a.1 := rfl
@[simp] theorem val_sub (a b : cornerSet A p) : (a - b).1 = a.1 - b.1 := rfl
@[simp] theorem val_one : (1 : cornerSet A p).1 = p := rfl
@[simp] theorem val_mul (a b : cornerSet A p) : (a * b).1 = a.1 * b.1 := rfl
@[simp] theorem val_star (a : cornerSet A p) : (star a).1 = star a.1 := rfl
@[simp] theorem val_smul (z : ℂ) (a : cornerSet A p) : (z • a).1 = z • a.1 := rfl
@[simp] theorem val_nsmul (n : ℕ) (a : cornerSet A p) : (n • a).1 = n • a.1 := rfl
@[simp] theorem val_zsmul (n : ℤ) (a : cornerSet A p) : (n • a).1 = n • a.1 := rfl

instance instAddCommGroup : AddCommGroup (cornerSet A p) :=
  Function.Injective.addCommGroup (Subtype.val : cornerSet A p → A) val_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

instance instRing : Ring (cornerSet A p) where
  __ := instAddCommGroup
  mul_assoc _ _ _ := val_injective (mul_assoc _ _ _)
  one_mul a := val_injective (mul_left a)
  mul_one a := val_injective (mul_right a)
  left_distrib _ _ _ := val_injective (mul_add _ _ _)
  right_distrib _ _ _ := val_injective (add_mul _ _ _)
  zero_mul _ := val_injective (zero_mul _)
  mul_zero _ := val_injective (mul_zero _)

/-- `Subtype.val` on the corner as an additive monoid homomorphism. -/
def valAddHom : cornerSet A p →+ A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance instModule : Module ℂ (cornerSet A p) :=
  Function.Injective.module ℂ valAddHom val_injective (fun _ _ => rfl)

noncomputable instance instAlgebra : Algebra ℂ (cornerSet A p) :=
  Algebra.ofModule (fun r x y => val_injective (smul_mul_assoc r x.1 y.1))
    (fun r x y => val_injective (mul_smul_comm r x.1 y.1))

instance instStarRing : StarRing (cornerSet A p) where
  star_involutive a := val_injective (star_star a.1)
  star_mul a b := val_injective (star_mul a.1 b.1)
  star_add a b := val_injective (star_add a.1 b.1)

instance instStarModule : StarModule ℂ (cornerSet A p) where
  star_smul r a := val_injective (star_smul r a.1)

/-- `Subtype.val` on the corner as a non-unital ring homomorphism.  It is
*not* unital: `(1 : cornerSet A p).1 = p`. -/
def valNonUnitalRingHom : cornerSet A p →ₙ+* A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance instNormedRing : NormedRing (cornerSet A p) :=
  NormedRing.induced (cornerSet A p) A valNonUnitalRingHom val_injective

@[simp] theorem norm_def (a : cornerSet A p) : ‖a‖ = ‖a.1‖ := rfl

noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (cornerSet A p) where
  norm_smul_le r a := by simpa [norm_def] using (norm_smul_le r a.1)

theorem isometry_val : Isometry (Subtype.val : cornerSet A p → A) :=
  AddMonoidHomClass.isometry_of_norm valAddHom (fun _ => rfl)

instance instCompleteSpace : CompleteSpace (cornerSet A p) := by
  refine (isometry_val (p := p)).isUniformInducing.completeSpace ?_
  rw [range_val]
  exact (isClosed_setOf p).isComplete

instance instCStarRing : CStarRing (cornerSet A p) where
  norm_mul_self_le a := CStarRing.norm_star_mul_self (x := a.1) |>.symm.le

/-- The square root of a positive element of the corner lies again in the
corner: if `p·a·p = a` then `(1−p)·a·(1−p) = 0`, so for `s = √a` one has
`‖s(1−p)‖² = ‖(1−p)·a·(1−p)‖ = 0`, i.e. `s = s·p = p·s`. -/
theorem sqrt_mem (a : A) (ha : 0 ≤ a) (hmem : p * a * p = a) :
    p * CFC.sqrt a * p = CFC.sqrt a := by
  set s := CFC.sqrt a with hs
  have hsa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have hss : s * s = a := CFC.sqrt_mul_sqrt_self a ha
  have hpp : p * p = p := (proj p).isIdempotentElem.eq
  have hsp : star p = p := (proj p).isSelfAdjoint.star_eq
  have hkey : (1 - p) * a * (1 - p) = 0 := by
    conv_lhs => rw [← hmem]
    have h1 : (1 - p) * p = 0 := by noncomm_ring [hpp]
    have h2 : p * (1 - p) = 0 := by noncomm_ring [hpp]
    calc (1 - p) * (p * a * p) * (1 - p)
        = ((1 - p) * p) * a * (p * (1 - p)) := by noncomm_ring
      _ = 0 := by rw [h1, h2]; simp
  have hnorm : ‖s * (1 - p)‖ = 0 := by
    have hstar : star (s * (1 - p)) * (s * (1 - p)) = (1 - p) * a * (1 - p) := by
      rw [star_mul, hsa.star_eq, star_sub, star_one, hsp]
      calc (1 - p) * s * (s * (1 - p)) = (1 - p) * (s * s) * (1 - p) := by
            noncomm_ring
        _ = (1 - p) * a * (1 - p) := by rw [hss]
    have h2 : ‖s * (1 - p)‖ * ‖s * (1 - p)‖ = ‖(1 - p) * a * (1 - p)‖ := by
      rw [← hstar, CStarRing.norm_star_mul_self]
    rw [hkey, norm_zero] at h2
    nlinarith [norm_nonneg (s * (1 - p))]
  have hzero : s * (1 - p) = 0 := by rwa [norm_eq_zero] at hnorm
  have hsp' : s * p = s := by
    have h := hzero
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  have hps : p * s = s := by
    have h := congrArg star hsp'
    rwa [star_mul, hsp, hsa.star_eq] at h
  rw [hps, hsp']

end Proj

end cornerSet

/-- **94II** part 5 (proc.tex `corner-vna-basic`): `pAp` is a C*-algebra
with unit `p` **for a projection `p`**, with the operations and the norm
inherited from `A`. -/
noncomputable instance cornerSet.instCStarAlgebra (p : A)
    [Fact (IsStarProjection p)] :
    CStarAlgebra (cornerSet A p) where

/-- **94II** parts 5–6: the canonical (Loewner) order on `pAp` is the one
inherited from `A`. -/
noncomputable instance cornerSet.instPartialOrder (p : A)
    [Fact (IsStarProjection p)] :
    PartialOrder (cornerSet A p) :=
  PartialOrder.lift (Subtype.val : cornerSet A p → A) cornerSet.val_injective

/-- **94II** parts 5–6: that order is the star-order of the C*-algebra
`pAp` — the point being that `√a` lies in the corner whenever `a` does
(`cornerSet.sqrt_mem`). -/
instance cornerSet.instStarOrderedRing (p : A)
    [Fact (IsStarProjection p)] :
    StarOrderedRing (cornerSet A p) := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · change z.1 + x.1 ≤ z.1 + y.1
    exact add_le_add le_rfl (show x.1 ≤ y.1 from hxy)
  · constructor
    · intro hx
      have hx' : (0 : A) ≤ x.1 := hx
      refine ⟨⟨CFC.sqrt x.1, cornerSet.sqrt_mem x.1 hx' x.2⟩, ?_⟩
      refine cornerSet.val_injective ?_
      have hsa : IsSelfAdjoint (CFC.sqrt x.1) :=
        IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x.1)
      change x.1 = star (CFC.sqrt x.1) * CFC.sqrt x.1
      rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self x.1 hx']
    · rintro ⟨s, rfl⟩
      change (0 : A) ≤ star s.1 * s.1
      exact star_mul_self_nonneg s.1

theorem cornerSet.le_def {p : A} [Fact (IsStarProjection p)]
    (a b : cornerSet A p) : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

namespace cornerSet

set_option linter.unusedSectionVars false

variable {A}
variable {p : A} [Fact (IsStarProjection p)] [VonNeumannAlgebra A]

/-- A self-adjoint element of the corner, viewed in `A`. -/
def saMap (d : selfAdjoint (cornerSet A p)) : selfAdjoint A :=
  ⟨d.1.1, congrArg Subtype.val (show star d.1 = d.1 from d.2)⟩

@[simp] theorem saMap_coe (d : selfAdjoint (cornerSet A p)) :
    ((saMap d : selfAdjoint A) : A) = d.1.1 := rfl

/-- **94II** part 6: the supremum in `A` of a nonempty directed set of
self-adjoint elements of the corner lies again in the corner — because
`a ↦ p·a·p` is normal (**44VIII** `ad_normal`) and fixes the set. -/
theorem isLUB_mem (D : Set (selfAdjoint A)) (s : selfAdjoint A)
    (hD : ∀ d ∈ D, p * (d : A) * p = (d : A)) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    p * (s : A) * p = (s : A) := by
  have h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D :=
    ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hstar : star p = p := (proj p).isSelfAdjoint.star_eq
  have hnat := ad_normal p D h
  rw [hstar] at hnat
  have himg : (fun d : selfAdjoint A => p * (d : A) * p) '' D = Subtype.val '' D :=
    Set.image_congr fun d hd => hD d hd
  rw [himg] at hnat
  have huniq := hnat.unique (isLUB_coe_of_isLUB h.1 (isLUB_dirSup D h))
  have hsd : s = dirSup D h := hlub.unique (isLUB_dirSup D h)
  rw [hsd]
  exact huniq

/-- Restriction of an np-functional on `A` to the corner (**94II** part 8). -/
noncomputable def restrictNP (p : A) [Fact (IsStarProjection p)] (ω : NPFunctional A) :
    NPFunctional (cornerSet A p) where
  toPositiveLinearMap :=
    { toFun := fun a => ω a.1
      map_add' := fun _ _ => map_add ω.toPositiveLinearMap _ _
      map_smul' := fun _ _ => map_smul ω.toPositiveLinearMap _ _
      monotone' := fun _ _ hxy => ω.toPositiveLinearMap.monotone hxy }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hlub' : IsLUB (saMap '' D) (saMap s) := by
      have hne' : (saMap '' D).Nonempty := hne.image _
      have hdir' : DirectedOn (· ≤ ·) (saMap '' D) := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
        obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
        exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩
      have hbdd' : BddAbove (saMap '' D) := by
        refine ⟨saMap s, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        exact hlub.1 hx
      obtain ⟨s₀, hs₀⟩ :=
        VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
      have hmem : p * (s₀ : A) * p = (s₀ : A) := by
        refine isLUB_mem _ s₀ ?_ hne' hdir' hs₀
        rintro _ ⟨x, hx, rfl⟩
        exact x.1.2
      set t : cornerSet A p := ⟨(s₀ : A), hmem⟩ with ht
      have htsa : IsSelfAdjoint t := val_injective s₀.2
      have hlubt : IsLUB D ⟨t, htsa⟩ := by
        refine ⟨fun d hd => hs₀.1 ⟨d, hd, rfl⟩, fun u hu => ?_⟩
        have hub : saMap u ∈ upperBounds (saMap '' D) := by
          rintro _ ⟨x, hx, rfl⟩
          exact hu hx
        exact hs₀.2 hub
      have hst : s = ⟨t, htsa⟩ := hlub.unique hlubt
      have hsm : saMap (⟨t, htsa⟩ : selfAdjoint (cornerSet A p)) = s₀ :=
        Subtype.ext rfl
      rw [hst, hsm]
      exact hs₀
    have hkey := ω.preservesDirSups' (saMap '' D) (saMap s) (hne.image _)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
        obtain ⟨u, hu, hxu, hzu⟩ := hdir x hx z hz
        exact ⟨saMap u, ⟨u, hu, rfl⟩, hxu, hzu⟩)
      hlub'
    rw [← Set.image_comp] at hkey
    exact hkey

@[simp] theorem restrictNP_apply (p : A) [Fact (IsStarProjection p)]
    (ω : NPFunctional A) (a : cornerSet A p) : restrictNP p ω a = ω a.1 := rfl

end cornerSet

/-- **94II** part 8 (proc.tex `corner-vna-basic`): `pAp` is a von Neumann
algebra when `A` is (and `p` is a projection).  Suprema are computed as in
`A` (part 6), and the np-functionals of `pAp` include the restrictions of
those of `A`, which already separate. -/
theorem cornerSet_vonNeumannAlgebra [VonNeumannAlgebra A] (p : A)
    [Fact (IsStarProjection p)] :
    VonNeumannAlgebra (cornerSet A p) where
  isLUB_of_bddAbove_directed := by
    intro D hne hdir hbdd
    obtain ⟨u, hu⟩ := hbdd
    have hne' : (cornerSet.saMap '' D).Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) (cornerSet.saMap '' D) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨v, hv, hxv, hzv⟩ := hdir x hx z hz
      exact ⟨cornerSet.saMap v, ⟨v, hv, rfl⟩, hxv, hzv⟩
    have hbdd' : BddAbove (cornerSet.saMap '' D) := by
      refine ⟨cornerSet.saMap u, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hu hx
    obtain ⟨s₀, hs₀⟩ :=
      VonNeumannAlgebra.isLUB_of_bddAbove_directed _ hne' hdir' hbdd'
    have hmem : p * (s₀ : A) * p = (s₀ : A) := by
      refine cornerSet.isLUB_mem _ s₀ ?_ hne' hdir' hs₀
      rintro _ ⟨x, hx, rfl⟩
      exact x.1.2
    refine ⟨⟨⟨(s₀ : A), hmem⟩, cornerSet.val_injective s₀.2⟩, ?_, ?_⟩
    · intro d hd
      exact hs₀.1 ⟨d, hd, rfl⟩
    · intro v hv
      have hub : cornerSet.saMap v ∈ upperBounds (cornerSet.saMap '' D) := by
        rintro _ ⟨x, hx, rfl⟩
        exact hv hx
      exact hs₀.2 hub
  np_faithful := by
    intro a ha hω
    refine cornerSet.val_injective ?_
    exact VonNeumannAlgebra.np_faithful a.1 ha
      (fun ω => hω (cornerSet.restrictNP p ω))

/-- `⌊b⌋` is a projection (**56VI**; the junk value off the effects is `0`),
so the corner `⌊b⌋A⌊b⌋` gets the structure above without further ado. -/
instance fact_isStarProjection_floor [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (floor b)) := by
  refine ⟨?_⟩
  by_cases hb : b ∈ effects A
  · exact (floor_spec hb).1
  · simp only [floor, hb, dite_false]
    exact IsStarProjection.zero A

/-- `⌈b⌉` is a projection (**56I**/**59I**; the junk value off the positive
cone is `0`), so the corner `⌈b⌉A⌈b⌉` gets the structure above without
further ado. -/
instance fact_isStarProjection_ceil [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (ceil b)) := by
  refine ⟨?_⟩
  by_cases hb : (0 : A) ≤ b
  · exact (ceil_spec hb).1
  · simp only [ceil, hb, dite_false]
    exact IsStarProjection.zero A

/-- `⌈⌈b⌉⌉` is a projection (**68III** `cceil_isLeast`: the central support
is by definition the least *central projection* absorbing `b`), so the
corner `⌈⌈b⌉⌉A⌈⌈b⌉⌉` gets the structure above without further ado. -/
instance fact_isStarProjection_cceil [VonNeumannAlgebra A] (b : A) :
    Fact (IsStarProjection (cceil b)) :=
  ⟨(cceil_isLeast b).1.1⟩

end CornerSet

/-! ## The scalars in universe `u`

The universal properties of **169II** and **169VIII** quantify their test
algebra over `Type u`, the universe this chapter's von Neumann algebras live
in, while `ℂ` sits in `Type 0`.  The cheapest test maps available are the
ones *out of the scalars*: the ncp-maps `ℂ → A` are exactly `z ↦ z·a` for
`0 ≤ a ∈ A`, so the uniqueness half of such a universal property becomes an
injectivity statement about elements of `A` — which is how **169XII** below
is proved.  The scalars therefore have to be lifted.  Mathlib carries the
ring, norm, algebra and completeness of `ULift ℂ` but neither its
∗-structure nor its order; those are supplied here. -/

section Scalars

/-- `ℂ`, lifted into the universe `u` of this chapter's algebras. -/
abbrev CU : Type u := ULift.{u} ℂ

namespace CU

theorem down_injective : Function.Injective (ULift.down : CU.{u} → ℂ) :=
  fun a b h => by cases a; cases b; exact congrArg ULift.up h

instance : StarRing CU.{u} where
  star x := ⟨star x.down⟩
  star_involutive x := down_injective (star_star x.down)
  star_mul x y := down_injective (star_mul x.down y.down)
  star_add x y := down_injective (star_add x.down y.down)

@[simp] theorem down_star (x : CU.{u}) : (star x).down = star x.down := rfl
@[simp] theorem down_one : (1 : CU.{u}).down = 1 := rfl
@[simp] theorem down_mul (x y : CU.{u}) : (x * y).down = x.down * y.down := rfl
@[simp] theorem down_smul (r : ℂ) (x : CU.{u}) : (r • x).down = r * x.down := rfl

instance : StarModule ℂ CU.{u} where
  star_smul r x := down_injective (star_smul r x.down)

instance : CStarRing CU.{u} where
  norm_mul_self_le x := CStarRing.norm_mul_self_le (x := x.down)

noncomputable instance : CStarAlgebra CU.{u} where

instance : PartialOrder CU.{u} := PartialOrder.lift ULift.down down_injective

theorem le_def {x y : CU.{u}} : x ≤ y ↔ x.down ≤ y.down := Iff.rfl

instance : StarOrderedRing CU.{u} := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ?_)
  · exact le_def.mpr (add_le_add (le_refl z.down) (le_def.mp hxy))
  · constructor
    · intro hx
      obtain ⟨s, hs⟩ :=
        CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (le_def.mp hx)
      exact ⟨⟨s⟩, down_injective hs⟩
    · rintro ⟨s, rfl⟩
      exact le_def.mpr (star_mul_self_nonneg s.down)

theorem isSelfAdjoint_down {x : CU.{u}} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint x.down :=
  congrArg ULift.down hx

end CU

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The linear map `ℂᵤ → A`, `z ↦ z·a`. -/
private noncomputable def smulLin (a : A) : CU.{u} →ₗ[ℂ] A where
  toFun z := z.down • a
  map_add' x y := by simp [add_smul]
  map_smul' r x := by simp [mul_smul]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem smulLin_apply (a : A) (z : CU.{u}) : smulLin a z = z.down • a := rfl

/-- Complete positivity of `z ↦ z·a`: `∑ᵢⱼ bᵢ* (cᵢ*cⱼ · a) bⱼ = v* a v` for
`v = ∑ᵢ cᵢbᵢ`. -/
private theorem smulLin_cp {a : A} (ha : 0 ≤ a) :
    IsCompletelyPositiveMap (smulLin (A := A) a) := by
  intro n c b
  have h : ∀ i j : Fin n,
      star (b i) * smulLin a (star (c i) * c j) * b j
        = star ((c i).down • b i) * a * ((c j).down • b j) := by
    intro i j
    simp only [smulLin_apply, CU.down_mul, CU.down_star, star_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]
  simp_rw [h]
  have hsum : ∑ i, ∑ j, star ((c i).down • b i) * a * ((c j).down • b j)
      = star (∑ i, (c i).down • b i) * a * (∑ j, (c j).down • b j) := by
    rw [star_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hsum]
  exact star_left_conjugate_nonneg ha _

/-- Transfer of a supremum in `sa(ℂᵤ)` to `ℝ`. -/
private theorem isLUB_re {D : Set (selfAdjoint CU.{u})} {s : selfAdjoint CU.{u}}
    (hlub : IsLUB D s) :
    IsLUB ((fun d : selfAdjoint CU.{u} => ((d : CU.{u}).down).re) '' D)
      (((s : CU.{u}).down).re) := by
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact (Complex.le_def.mp (CU.le_def.mp (Subtype.coe_le_coe.mpr (hlub.1 hd)))).1
  · intro r hr
    have hsa : IsSelfAdjoint (⟨((r : ℝ) : ℂ)⟩ : CU.{u}) :=
      CU.down_injective
        ((Complex.im_eq_zero_iff_isSelfAdjoint _).mp (Complex.ofReal_im _))
    have hub : (⟨⟨((r : ℝ) : ℂ)⟩, hsa⟩ : selfAdjoint CU.{u}) ∈ upperBounds D := by
      intro d hd
      refine Subtype.coe_le_coe.mp
        (CU.le_def.mpr (Complex.le_def.mpr ⟨hr ⟨d, hd, rfl⟩, ?_⟩))
      rw [Complex.ofReal_im, Complex.im_eq_zero_iff_isSelfAdjoint]
      exact CU.isSelfAdjoint_down d.2
    exact (Complex.le_def.mp (CU.le_def.mp (Subtype.coe_le_coe.mpr (hlub.2 hub)))).1

/-- Normality of `z ↦ z·a`: the positive cone of `A` is closed, and a
supremum in `ℝ` lies in the closure of its set. -/
private theorem smulLin_normal {a : A} (ha : 0 ≤ a) :
    PreservesDirSups ⇑(smulLin (A := A) a) := by
  intro D s hne _ hlub
  have hre := isLUB_re hlub
  have hmono : ∀ t r : ℝ, t ≤ r → ((t : ℂ)) • a ≤ ((r : ℂ)) • a := by
    intro t r htr
    have h : (0 : A) ≤ ((r - t : ℝ) : ℂ) • a := cstar_positive_1 a ha _ (by linarith)
    have he : ((r - t : ℝ) : ℂ) • a = (r : ℂ) • a - (t : ℂ) • a := by
      push_cast; rw [sub_smul]
    rw [he] at h
    exact sub_nonneg.mp h
  have hcoe : ∀ d : selfAdjoint CU.{u},
      (((((d : CU.{u}).down).re : ℝ)) : ℂ) = (d : CU.{u}).down := by
    intro d
    have him : ((d : CU.{u}).down).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (CU.isSelfAdjoint_down d.2)
    apply Complex.ext <;> simp [him]
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    show (d : CU.{u}).down • a ≤ (s : CU.{u}).down • a
    rw [← hcoe d, ← hcoe s]
    exact hmono _ _ (hre.1 ⟨d, hd, rfl⟩)
  · intro u hu
    show (s : CU.{u}).down • a ≤ u
    have hclosed : IsClosed {t : ℝ | ((t : ℂ)) • a ≤ u} :=
      isClosed_Iic.preimage (by fun_prop)
    have hsub : (fun d : selfAdjoint CU.{u} => ((d : CU.{u}).down).re) '' D
        ⊆ {t : ℝ | ((t : ℂ)) • a ≤ u} := by
      rintro _ ⟨d, hd, rfl⟩
      show ((((d : CU.{u}).down).re : ℝ) : ℂ) • a ≤ u
      rw [hcoe d]
      exact hu ⟨d, hd, rfl⟩
    have hmem := hre.mem_closure (hne.image _)
    have hfin := hclosed.closure_subset_iff.mpr hsub hmem
    rw [← hcoe s]
    exact hfin

/-- Every positive element `a` of a C*-algebra `A` is the value at `1` of an
ncp-map `ℂᵤ → A`, namely `z ↦ z·a`.  (Conversely every ncp-map `ℂᵤ → A` is
of this form, by linearity; that direction is not needed here.) -/
noncomputable def ncpOfNonneg {a : A} (ha : 0 ≤ a) : NCPMap CU.{u} A where
  toCompletelyPositiveMap :=
    { toLinearMap := smulLin a
      map_cstarMatrix_nonneg' :=
        (cp_iff (smulLin (A := A) a)).out 0 1 |>.mp (smulLin_cp ha) }
  preservesDirSups' := smulLin_normal ha

@[simp] theorem ncpOfNonneg_apply {a : A} (ha : 0 ≤ a) (z : CU.{u}) :
    ncpOfNonneg ha z = z.down • a := rfl

end Scalars

/-! ## Parsec 1690: corners and filters

**169I** (dils.tex:6056) and **169VII** (dils.tex:6113): introduction —
nothing to formalize.  **169III**, **169IX** (Remarks) — not converted. -/

section CornersFilters

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **169II** (`dils-corner`, dils.tex:6060, Definition): an ncp-map
`h : A → B` is a **corner** for an effect `a ∈ [0,1]_A` when `h(a) = h(1)`
and every ncp-map `f : A → C` with `f(a) = f(1)` factors uniquely through
`h` (as `f = f' ∘ h`). -/
def IsCornerFor (h : NCPMap A B) (a : A) : Prop :=
  a ∈ effects A ∧ h a = h 1 ∧
  ∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (f : NCPMap A C), f a = f 1 →
    ∃! f' : NCPMap B C, ∀ x, f' (h x) = f x

/-- **169II** (`dils-corner`, dils.tex:6060, Definition): a **corner** is
an ncp-map which is a corner for some effect. -/
def IsCorner (h : NCPMap A B) : Prop :=
  ∃ a : A, IsCornerFor h a

/-- **169IV** (`standard-corner-dils`, dils.tex:6080, Example): the
**standard corner** `h_a : A → ⌊a⌋A⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋`, is a corner for
the effect `a` (see proc.tex 98I, 95II). -/
theorem standard_corner_dils [VonNeumannAlgebra A] (a : A)
    (ha : a ∈ effects A) :
    ∃ h : NCPMap A (cornerSet A (floor a)),
      (∀ b : A, (h b).1 = floor a * b * floor a) ∧ IsCornerFor h a :=
  sorry

/-- **169V** (`h-is-corner-for-unital-map`, dils.tex:6088, Lemma): if
`(𝒫, ϱ, h)` is a Paschke dilation of a *unital* ncp-map, then `h` is a
corner.

**169VI** is the proof — not converted. -/
theorem h_is_corner_for_unital_map (φ : NCPMap A B) (hu : φ 1 = 1)
    (D : PaschkeTriple A B) (hD : IsPaschkeDilationOf D ⇑φ) :
    IsCorner D.h :=
  sorry

/-- **169VIII** (`dils-def-filter`, dils.tex:6116, Definition): an ncp-map
`c : A → B` is a **filter** for `b ∈ B`, `b ≥ 0`, when `c(1) ≤ b` and
every ncp-map `f : C → B` with `f(1) ≤ b` factors uniquely through `c` (as
`f = c ∘ f'`) **by a subunital `f'`**.

⚠️ **Repaired, by a ruling of the author (2026-08-16; QUESTIONS B11, now
closed; ERRATA).**  As printed, dils.tex asks only for an *ncp* mediating
map `f'`, and under that reading **169XI**.2a `dils_filter_basics_2a` is
false: for `A = B = C' = ℂ`, `φ = id` and `c' = ½·id` the factorisation
`f' = 2·id` is ncp, so `c'` is a filter for `φ(1) = 1`, yet no *unital* `φ'`
has `c' ∘ φ' = φ`.

The defect is in the mediating map only, and `c 1 ≤ b` is **kept** (it is
not the problem).  eff.tex **197II** `dfn-quotient` — of which 169IX's own
Remark says filters are the direction-reversed counterpart — has exactly
this shape with `b = p^⊥`, but lives in an effectus, where the mediating map
must be a *morphism*, i.e. subunital; our `NCPMap` is genuinely not
subunital (`NCPSUMap` is a separate structure in `Theses/Common.lean`), and
that gap is the whole counterexample.  The quantification over `f` needs no
change: when `b` is an effect, `f(1) ≤ b ≤ 1` already forces `f` subunital,
so only `f'` escapes.  With the repair, `f' = 2·id` is excluded and 169XI.2a
is provable (below).

`IsFilter` below, "a filter for *some* `b`", was insensitive to the
difference already. -/
def IsFilterFor (c : NCPMap A B) (b : B) : Prop :=
  0 ≤ b ∧ c 1 ≤ b ∧
  ∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (f : NCPMap C B), f 1 ≤ b →
    ∃! f' : NCPSUMap C A, ∀ x, c (f'.toNCPMap x) = f x

/-- **169VIII** (`dils-def-filter`, dils.tex:6116, Definition): a
**filter** is an ncp-map which is a filter for some positive element. -/
def IsFilter (c : NCPMap A B) : Prop :=
  ∃ b : B, IsFilterFor c b

/-- **169X** (`dils-stand-filter`, dils.tex:6150, Example): the **standard
filter** `c_b : ⌈b⌉B⌈b⌉ → B`, `a ↦ √b a √b`, is a filter for `b ≥ 0` (see
proc.tex 96V, 98I). -/
theorem dils_stand_filter [VonNeumannAlgebra B] (b : B) (hb : 0 ≤ b) :
    ∃ c : NCPMap (cornerSet B (ceil b)) B,
      (∀ a : cornerSet B (ceil b), c a = CFC.sqrt b * a.1 * CFC.sqrt b) ∧
      IsFilterFor c b :=
  sorry

/- **169XI** (`dils-filter-basics-exercise`) follows **169XII** below: both
its parts use the injectivity of filters, and Lean needs that declaration
first.  The three statements are otherwise unchanged. -/

/-- **169XII** (`dils-filters-injective`, dils.tex:6180, Exercise): filters
are injective.

The hint (and the `bsols.tex` solution) route this through the *standard*
filter `c_b` of **169X**: `c = c_b ∘ ϑ` for an ncp-isomorphism `ϑ`, and `c_b`
is injective by `mult-cancellation`.  **169X** is still `sorry`, and it is not
needed: the *uniqueness* half of `c`'s own universal property already gives
injectivity, tested against the ncp-maps out of the scalars
(`ncpOfNonneg` above).  For effects `x, y` with `c x = c y`, the map
`z ↦ z·(c x)` is an ncp-map `ℂᵤ → B` whose value at `1` is `c x ≤ c 1 ≤ b`,
and both `z ↦ z·x` and `z ↦ z·y` factor it through `c`; so they agree, and
`x = y`.  Scaling by `(1+‖x‖+‖y‖)⁻¹` extends this to all positive elements,
and `w = w⁺ − w⁻` together with `c(w*) = (c w)*` to all of `A`. -/
theorem dils_filters_injective (c : NCPMap A B) (hc : IsFilter c) :
    Function.Injective ⇑c := by
  obtain ⟨b, -, hc1, huniv⟩ := hc
  set L : A →ₗ[ℂ] B := c.toCompletelyPositiveMap.toLinearMap with hLdef
  have hLc : ∀ x : A, L x = c x := fun _ => rfl
  have hcp : IsCompletelyPositiveMap L :=
    (cp_iff L).out 1 0 |>.mp fun N M hM =>
      c.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hpos : IsPositiveMap L := astara_pos_basic_2_cp L hcp
  have hmono : ∀ x y : A, x ≤ y → c x ≤ c y := by
    intro x y hxy
    have h := hpos (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub, hLc, hLc] at h
    exact sub_nonneg.mp h
  have hsmul : ∀ (z : ℂ) (x : A), c (z • x) = z • c x := by
    intro z x
    rw [← hLc, ← hLc, map_smul]
  -- (1) `c` is injective on the effects
  have keyEff : ∀ x y : A, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → c x = c y → x = y := by
    intro x y hx hx1 hy hy1 hxy
    have hcx : (0 : B) ≤ c x := by rw [← hLc]; exact hpos x hx
    have hbnd : (ncpOfNonneg hcx : NCPMap CU.{u} B) 1 ≤ b := by
      rw [ncpOfNonneg_apply, CU.down_one, one_smul]
      exact le_trans (hmono x 1 hx1) hc1
    obtain ⟨g, -, hgu⟩ :=
      huniv CU.{u} inferInstance inferInstance inferInstance (ncpOfNonneg hcx) hbnd
    -- the two candidate factorisations are **subunital**, because `x, y ≤ 1`
    have hsu : ∀ {w : A}, (hw : 0 ≤ w) → w ≤ 1 → Subunital ⇑(ncpOfNonneg hw) := by
      intro w hw hw1
      show (ncpOfNonneg hw) 1 ≤ 1
      rw [ncpOfNonneg_apply, CU.down_one, one_smul]
      exact hw1
    have h1 : (⟨ncpOfNonneg hx, hsu hx hx1⟩ : NCPSUMap CU.{u} A)
        = ⟨ncpOfNonneg hy, hsu hy hy1⟩ := by
      refine (hgu _ ?_).trans (hgu _ ?_).symm
      · intro z
        rw [ncpOfNonneg_apply, ncpOfNonneg_apply, hsmul]
      · intro z
        rw [ncpOfNonneg_apply, ncpOfNonneg_apply, hsmul, hxy]
    have hval := congrArg (fun f : NCPSUMap CU.{u} A => f.toNCPMap 1) h1
    simpa [ncpOfNonneg_apply] using hval
  -- (2) `c` is injective on the positive cone, by scaling into the effects
  have keyPos : ∀ x y : A, 0 ≤ x → 0 ≤ y → c x = c y → x = y := by
    intro x y hx hy hxy
    set t : ℝ := (1 + ‖x‖ + ‖y‖)⁻¹ with htdef
    have hden : (0 : ℝ) < 1 + ‖x‖ + ‖y‖ := by
      have := norm_nonneg x; have := norm_nonneg y; linarith
    have htpos : 0 < t := by rw [htdef]; exact inv_pos.mpr hden
    have hshrink : ∀ w : A, 0 ≤ w → ‖w‖ ≤ 1 + ‖x‖ + ‖y‖ → (t : ℂ) • w ≤ 1 := by
      intro w hw hwn
      have h1 : w ≤ algebraMap ℂ A ((‖w‖ : ℝ) : ℂ) := by
        have h := IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hw)
        rwa [algebraMap_real_eq] at h
      have h2 : (t : ℂ) • w ≤ (t : ℂ) • algebraMap ℂ A ((‖w‖ : ℝ) : ℂ) := by
        have h0 : (0 : A) ≤ (t : ℂ) • (algebraMap ℂ A ((‖w‖ : ℝ) : ℂ) - w) :=
          cstar_positive_1 _ (sub_nonneg.mpr h1) t htpos.le
        rw [smul_sub] at h0
        exact sub_nonneg.mp h0
      have h3 : (t : ℂ) • algebraMap ℂ A ((‖w‖ : ℝ) : ℂ)
          = algebraMap ℂ A (((t * ‖w‖ : ℝ)) : ℂ) := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          smul_smul]
        push_cast
        ring_nf
      have h4 : algebraMap ℂ A (((t * ‖w‖ : ℝ)) : ℂ) ≤ (1 : A) := by
        have hle : t * ‖w‖ ≤ 1 := by
          rw [htdef]
          rw [inv_mul_le_iff₀ hden]
          simpa using hwn
        have h := algebraMap_ofReal_mono (𝒜 := A) hle
        rwa [show (((1 : ℝ)) : ℂ) = 1 by norm_num, map_one] at h
      exact h2.trans (h3 ▸ h4)
    have htx : (t : ℂ) • x ≤ 1 := by
      refine hshrink x hx ?_
      have := norm_nonneg y; linarith
    have hty : (t : ℂ) • y ≤ 1 := by
      refine hshrink y hy ?_
      have := norm_nonneg x; linarith
    have hstep : (t : ℂ) • x = (t : ℂ) • y :=
      keyEff _ _ (cstar_positive_1 x hx t htpos.le) htx
        (cstar_positive_1 y hy t htpos.le) hty
        (by rw [hsmul, hsmul, hxy])
    have htne : ((t : ℂ)) ≠ 0 := by exact_mod_cast htpos.ne'
    exact smul_right_injective A htne hstep
  -- (3) all of `A`, by `w = w⁺ − w⁻` and the Cartesian decomposition
  have hstar : ∀ w : A, c (star w) = star (c w) := by
    intro w
    have h := cstar_p_implies_i L hpos w
    rw [hLc, hLc] at h
    exact h
  have hsa : ∀ w : A, IsSelfAdjoint w → c w = 0 → w = 0 := by
    intro w hw hcw
    have h1 : w⁺ - w⁻ = w := CFC.posPart_sub_negPart w hw
    have h2 : c (w⁺) = c (w⁻) := by
      have h : c (w⁺ - w⁻) = 0 := by rw [h1]; exact hcw
      rw [← hLc, map_sub, hLc, hLc, sub_eq_zero] at h
      exact h
    have h3 := keyPos _ _ (CFC.posPart_nonneg w) (CFC.negPart_nonneg w) h2
    rw [← h1, h3, sub_self]
  have hzero : ∀ z : A, c z = 0 → z = 0 := by
    intro z hz
    have hzs : c (star z) = 0 := by rw [hstar, hz, star_zero]
    have hadd : ∀ v w : A, c (v + w) = c v + c w := by
      intro v w
      rw [← hLc, map_add, hLc, hLc]
    have hsub : ∀ v w : A, c (v - w) = c v - c w := by
      intro v w
      rw [← hLc, map_sub, hLc, hLc]
    have hu : z + star z = 0 := by
      refine hsa _ (IsSelfAdjoint.add_star_self z) ?_
      rw [hadd, hz, hzs, add_zero]
    have hv : Complex.I • (z - star z) = 0 := by
      refine hsa _ ?_ ?_
      · rw [IsSelfAdjoint, star_smul, star_sub, star_star, RCLike.star_def,
          Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
      · rw [hsmul, hsub, hz, hzs, sub_zero, smul_zero]
    have hv' : z - star z = 0 := by
      have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
      exact smul_right_injective A hI (by simpa using hv)
    have : (2 : ℂ) • z = 0 := by
      have := congrArg₂ (· + ·) hu hv'
      simp only [add_zero] at this
      rw [← this]
      module
    have h2 : ((2 : ℂ)) ≠ 0 := two_ne_zero
    exact smul_right_injective A h2 (by simpa using this)
  intro x y hxy
  have h : c (x - y) = 0 := by
    rw [← hLc, map_sub, hLc, hLc, hxy, sub_self]
  exact sub_eq_zero.mp (hzero _ h)

/-! ### Auxiliary: ncp-maps compose and scale

`Theses/B/Dils/Stinespring.lean` carries the same three constructions, but
as `private` declarations, so they are repeated here rather than exported
(a merge is noted in that file's header). -/

/-- An ncp-map, as a positive linear map. -/
private noncomputable def ncpPos {P Q : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] (f : NCPMap P Q) : P →ₚ[ℂ] Q where
  toLinearMap := f.toCompletelyPositiveMap.toLinearMap
  monotone' := fun x y hxy => by
    have hcp : IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
      (cp_iff _).out 1 0 |>.mp fun N M hM =>
        f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
    have h := astara_pos_basic_2_cp _ hcp (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h

/-- The composition of two ncp-maps is an ncp-map. -/
private theorem exists_ncpComp {P Q R : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    (f : NCPMap Q R) (g : NCPMap P Q) :
    ∃ k : NCPMap P R, ∀ a, k a = f (g a) := by
  set Lg : P →ₗ[ℂ] Q := g.toCompletelyPositiveMap.toLinearMap with hLg
  set Lf : Q →ₗ[ℂ] R := f.toCompletelyPositiveMap.toLinearMap with hLf
  have hLgcp : IsCompletelyPositiveMap Lg :=
    (cp_iff Lg).out 1 0 |>.mp fun N M hM =>
      g.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hLfcp : IsCompletelyPositiveMap Lf :=
    (cp_iff Lf).out 1 0 |>.mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  exact ⟨{ toCompletelyPositiveMap :=
             { toLinearMap := Lf.comp Lg
               map_cstarMatrix_nonneg' :=
                 (cp_iff (Lf.comp Lg)).out 0 1 |>.mp
                   (cp_comp Lg Lf hLgcp hLfcp) }
           preservesDirSups' :=
             preservesDirSups_pmap_comp (ncpPos g) g.preservesDirSups'
               (ncpPos f) f.preservesDirSups' },
    fun _ => rfl⟩

/-- Multiplication by a positive real is an order isomorphism of a
C*-algebra (auxiliary for `exists_ncpSmul`). -/
private theorem smul_le_smul_iff_pos {P : Type*} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] {l : ℝ} (hl : 0 < l) (x y : P) :
    (l : ℂ) • x ≤ (l : ℂ) • y ↔ x ≤ y := by
  have main : ∀ (m : ℝ), 0 ≤ m → ∀ u v : P, u ≤ v → (m : ℂ) • u ≤ (m : ℂ) • v := by
    intro m hm u v huv
    have h0 : (0 : P) ≤ (m : ℂ) • (v - u) :=
      cstar_positive_1 _ (sub_nonneg.mpr huv) m hm
    rw [smul_sub] at h0
    rwa [← sub_nonneg]
  refine ⟨fun h => ?_, main l hl.le x y⟩
  have h' := main l⁻¹ (inv_nonneg.mpr hl.le) _ _ h
  rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hl.ne',
    Complex.ofReal_one, one_smul, one_smul] at h'

/-- A positive real multiple of an ncp-map is an ncp-map. -/
private theorem exists_ncpSmul {P Q : Type*} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q] [StarOrderedRing Q]
    (f : NCPMap P Q) {l : ℝ} (hl : 0 < l) :
    ∃ g : NCPMap P Q, ∀ a, g a = (l : ℂ) • f a := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := (l : ℂ) • (f.toCompletelyPositiveMap.toLinearMap)
                map_cstarMatrix_nonneg' := fun k M hM => ?_ }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  · have h1 : (0 : CStarMatrix (Fin k) (Fin k) Q)
        ≤ M.map f.toCompletelyPositiveMap.toLinearMap :=
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
    have h2 : M.map ((l : ℂ) • f.toCompletelyPositiveMap.toLinearMap)
        = (l : ℂ) • M.map f.toCompletelyPositiveMap.toLinearMap := rfl
    rw [h2]
    exact cstar_positive_1 _ h1 l hl.le
  · intro D s hne hdir hlub
    have h := f.preservesDirSups' D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact (smul_le_smul_iff_pos hl _ _).mpr (h.1 ⟨d, hd, rfl⟩)
    · intro u hu
      have hu' : (l : ℂ)⁻¹ • u ∈ upperBounds ((fun d : selfAdjoint P => f d) '' D) := by
        rintro _ ⟨d, hd, rfl⟩
        have := hu ⟨d, hd, rfl⟩
        have hle : (l : ℂ) • (f d) ≤ (l : ℂ) • ((l : ℂ)⁻¹ • u) := by
          rwa [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hl.ne'), one_smul]
        exact (smul_le_smul_iff_pos hl _ _).mp hle
      have := h.2 hu'
      have hle : (l : ℂ) • f s ≤ (l : ℂ) • ((l : ℂ)⁻¹ • u) :=
        (smul_le_smul_iff_pos hl _ _).mpr this
      rwa [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hl.ne'), one_smul] at hle

/-- `(1 + ‖w‖)⁻¹ w ≤ 1` for `w ≥ 0`: the rescaling that makes an arbitrary
positive element subunital.  (Auxiliary for **169XI**.1.) -/
private theorem smul_norm_succ_inv_le_one {P : Type*} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] {w : P} (hw : 0 ≤ w) :
    (((‖w‖ + 1)⁻¹ : ℝ) : ℂ) • w ≤ 1 := by
  set t : ℝ := (‖w‖ + 1)⁻¹ with htdef
  have hden : (0 : ℝ) < ‖w‖ + 1 := by positivity
  have htpos : 0 < t := by rw [htdef]; exact inv_pos.mpr hden
  have h1 : w ≤ algebraMap ℂ P ((‖w‖ : ℝ) : ℂ) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hw)
    rwa [algebraMap_real_eq] at h
  have h2 : (t : ℂ) • w ≤ (t : ℂ) • algebraMap ℂ P ((‖w‖ : ℝ) : ℂ) := by
    have h0 : (0 : P) ≤ (t : ℂ) • (algebraMap ℂ P ((‖w‖ : ℝ) : ℂ) - w) :=
      cstar_positive_1 _ (sub_nonneg.mpr h1) t htpos.le
    rw [smul_sub] at h0
    exact sub_nonneg.mp h0
  have h3 : (t : ℂ) • algebraMap ℂ P ((‖w‖ : ℝ) : ℂ)
      = algebraMap ℂ P (((t * ‖w‖ : ℝ)) : ℂ) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_smul]
    push_cast
    ring_nf
  have h4 : algebraMap ℂ P (((t * ‖w‖ : ℝ)) : ℂ) ≤ (1 : P) := by
    have hle : t * ‖w‖ ≤ 1 := by
      rw [htdef, inv_mul_le_iff₀ hden]
      linarith [norm_nonneg w]
    have h := algebraMap_ofReal_mono (𝒜 := P) hle
    rwa [show (((1 : ℝ)) : ℂ) = 1 by norm_num, map_one] at h
  exact h2.trans (h3 ▸ h4)

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 1: if `(𝒫, ϱ, h)` is a Paschke dilation of `φ : A → B` and
`c : B → C` a filter, then `(𝒫, ϱ, c ∘ h)` is a Paschke dilation of
`c ∘ φ`.

The author's solution (`bsols.tex`, `dils-filter-basics-exercise`.1) is
transcribed, with **two divergences**, both recorded in PROVING-LOG.

*(i)* The solution first assumes `φ(1) ≤ 1`, so that the mediating
`h' : 𝒫' → 𝒞` of a competing triple satisfies `h'(1) = c(φ(1)) ≤ c(1) ≤ b`
and `c`'s universal property applies; the general case is then reduced to it
by rescaling the *whole dilation* through **140X**.4 twice.  Here the
rescaling is done to `h'` alone — `λ := (‖φ(1)‖+1)⁻¹` makes `λ h'(1) ≤ b`,
and the factorisation `h''` of `λ h'` is scaled back by `λ⁻¹` — which needs
no case split and no appeal to 140X.4.

*(ii)* Where the solution derives `φ = h'' ∘ ϱ'` and the uniqueness of `σ`
from *uniqueness* in `c`'s universal property, we use the injectivity of `c`
(**169XII**) directly; it is proved above and is the same fact. -/
theorem dils_filter_basics_1 {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) (c : NCPMap B C) (hc : IsFilter c) :
    ∃ h' : NCPMap D.P C, (∀ x, h' x = c (D.h x)) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ fun a => c (φ a) := by
  have hcinj : Function.Injective ⇑c := dils_filters_injective c hc
  obtain ⟨b, -, hcb, huniv⟩ := hc
  -- linearity and monotonicity of `c`
  set Lc : B →ₗ[ℂ] C := c.toCompletelyPositiveMap.toLinearMap with hLcdef
  have hLc : ∀ x : B, Lc x = c x := fun _ => rfl
  have hccp : IsCompletelyPositiveMap Lc :=
    (cp_iff Lc).out 1 0 |>.mp fun N M hM =>
      c.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hcpos : IsPositiveMap Lc := astara_pos_basic_2_cp Lc hccp
  have hcmono : ∀ x y : B, x ≤ y → c x ≤ c y := by
    intro x y hxy
    have h := hcpos (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub, hLc, hLc] at h
    exact sub_nonneg.mp h
  have hcsmul : ∀ (z : ℂ) (x : B), c (z • x) = z • c x := by
    intro z x
    rw [← hLc, ← hLc, map_smul]
  -- `h' := c ∘ h`
  obtain ⟨h', hh'⟩ := exists_ncpComp c D.h
  refine ⟨h', hh', fun a => by rw [hh', hD.1 a], ?_⟩
  intro D' hD'
  -- `λ = (‖φ(1)‖+1)⁻¹`, so that `λ·φ(1) ≤ 1` and hence `λ·h''(1) ≤ b`
  have hφ1 : (0 : B) ≤ φ 1 := by
    have h := (astara_pos_basic_2_cp (φ.toCompletelyPositiveMap.toLinearMap)
      ((cp_iff _).out 1 0 |>.mp fun N M hM =>
        φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM)) 1 zero_le_one
    exact h
  set l : ℝ := (‖(φ 1 : B)‖ + 1)⁻¹ with hldef
  have hlpos : 0 < l := by
    rw [hldef]; positivity
  have hlne : ((l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlpos.ne'
  have hsub : ((l : ℝ) : ℂ) • (φ 1 : B) ≤ 1 := smul_norm_succ_inv_le_one hφ1
  obtain ⟨k, hk⟩ := exists_ncpSmul D'.h hlpos
  have hρ1 : (D'.ρ (1 : A) : D'.P) = 1 := map_one D'.ρ.toStarAlgHom
  have hh1 : (D'.h (1 : D'.P) : C) = c (φ 1) := by
    rw [← hρ1]; exact hD' 1
  have hk1 : (k 1 : C) ≤ b := by
    rw [hk, hh1, ← hcsmul]
    exact le_trans (hcmono _ _ hsub) hcb
  -- factor `λ h''` through `c`, then scale back
  obtain ⟨g₀, hg₀, -⟩ :=
    huniv D'.P inferInstance inferInstance inferInstance k hk1
  obtain ⟨g, hg⟩ := exists_ncpSmul g₀.toNCPMap (inv_pos.mpr hlpos)
  have hcg : ∀ x : D'.P, (c (g x) : C) = D'.h x := by
    intro x
    rw [hg, hcsmul, hg₀ x, hk x, smul_smul, Complex.ofReal_inv,
      inv_mul_cancel₀ hlne, one_smul]
  -- `g ∘ ϱ' = φ`, because `c` is injective
  have hgρ : ∀ a : A, (g (D'.ρ a) : B) = φ a := by
    intro a
    refine hcinj ?_
    rw [hcg (D'.ρ a)]
    exact hD' a
  obtain ⟨σ, ⟨hσ1, hσ2⟩, hσu⟩ := hD.2 ⟨D'.P, D'.vn, D'.ρ, g⟩ hgρ
  refine ⟨σ, ⟨hσ1, fun x => ?_⟩, ?_⟩
  · show (h' (σ x) : C) = D'.h x
    rw [hh', hσ2 x, hcg x]
  · rintro σ' ⟨hσ'1, hσ'2⟩
    refine hσu σ' ⟨hσ'1, fun x => ?_⟩
    refine hcinj ?_
    have h := hσ'2 x
    show (c (D.h (σ' x)) : C) = c (g x)
    rw [← hh', hcg x]
    exact h

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 2, first half: for a filter `c' : C' → B` of `φ(1)` there is a unique
unital ncp-map `φ'` with `φ = c' ∘ φ'`.

This was `sorry` for six sessions as **false under the printed reading of
`IsFilterFor`** (QUESTIONS B11): with a merely *ncp* mediating map,
`A = B = C' = ℂ`, `φ = id`, `c' = ½·id` makes `c'` a filter for `φ(1) = 1`
(factor `f` as `f' = 2f`), yet the unital `φ'` demanded here would need
`c'(1) = φ(1)`, i.e. `½ = 1`.  The author ruled on 2026-08-16 that the
mediating map is **subunital**; `IsFilterFor` now says so, and the argument
below is the thesis's own two-liner.

Note it does **not** need faithfulness or bipositivity of `c'`, only
monotonicity: subunitality of the mediating `ψ` gives
`φ(1) = c'(ψ(1)) ≤ c'(1)`, the filter clause gives `c'(1) ≤ φ(1)`, so
`c'(ψ(1)) = c'(1)` and injectivity of a filter (**169XII**
`dils_filters_injective`) yields `ψ(1) = 1`. -/
theorem dils_filter_basics_2a {C' : Type u} [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (φ : NCPMap A B)
    (c' : NCPMap C' B) (hc : IsFilterFor c' (φ 1)) :
    ∃! φ' : NCPMap A C', φ' 1 = 1 ∧ ∀ a, c' (φ' a) = φ a := by
  have hcinj : Function.Injective ⇑c' := dils_filters_injective c' ⟨φ 1, hc⟩
  obtain ⟨-, hc1, huniv⟩ := hc
  have hcmono : ∀ x y : C', x ≤ y → (c' x : B) ≤ c' y := fun _ _ h =>
    (ncpPos c').monotone h
  -- factor `φ` through `c'` (legal: `φ(1) ≤ φ(1)`)
  obtain ⟨ψ, hψ, hψu⟩ :=
    huniv A inferInstance inferInstance inferInstance φ le_rfl
  -- the mediating map is unital, because it is subunital and `c'` injective
  have hψ1 : (ψ.toNCPMap 1 : C') = 1 := by
    refine hcinj ?_
    have h1 : (c' (ψ.toNCPMap 1) : B) = φ 1 := hψ 1
    have h2 : (c' (ψ.toNCPMap 1) : B) ≤ c' 1 := hcmono _ _ ψ.subunital'
    rw [h1] at h2
    rw [h1]
    exact le_antisymm h2 hc1
  refine ⟨ψ.toNCPMap, ⟨hψ1, hψ⟩, ?_⟩
  rintro φ' ⟨hφ'1, hφ'2⟩
  have hsu : Subunital ⇑φ' := by
    show (φ' 1 : C') ≤ 1
    rw [hφ'1]
  exact congrArg NCPSUMap.toNCPMap (hψu ⟨φ', hsu⟩ hφ'2)

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 2, second half: if moreover `(𝒫, ϱ, h)` is a Paschke dilation of
`φ'`, then `(𝒫, ϱ, c' ∘ h)` is a Paschke dilation of `φ`.

The author's solution is "by the previous point" — that is, part 1 applied
to the filter `c'` and the dilation of `φ'` — and that is what is done
here; the unitality of `φ'` is not used.  (So this half does *not* inherit
the defect of part 2's first half, which is the only place `c(1) = b` is
needed.) -/
theorem dils_filter_basics_2b {C' : Type u} [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (φ : NCPMap A B)
    (c' : NCPMap C' B) (hc : IsFilterFor c' (φ 1)) (φ' : NCPMap A C')
    (hφ' : φ' 1 = 1 ∧ ∀ a, c' (φ' a) = φ a) (D : PaschkeTriple A C')
    (hD : IsPaschkeDilationOf D ⇑φ') :
    ∃ h' : NCPMap D.P B, (∀ x, h' x = c' (D.h x)) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ ⇑φ := by
  obtain ⟨h', hh', hdil⟩ := dils_filter_basics_1 φ' D hD c' ⟨φ 1, hc⟩
  refine ⟨h', hh', ?_⟩
  have hfun : (fun a => c' (φ' a)) = ⇑φ := funext hφ'.2
  rwa [hfun] at hdil

end CornersFilters

/-! ## Parsec 1700: pure maps -/

section Pure

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **170I** (`dils-def-pure`, dils.tex:6186, Definition): an ncp-map is
**pure** when it is a composition of filters and corners; equivalently (by
proc.tex 100III `pure-fundamental`, cf. **170Ia**) a filter after a
corner, which is the form used here. -/
def IsPureMap (φ : NCPMap A B) : Prop :=
  ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (h : NCPMap A C) (c : NCPMap C B),
    IsCorner h ∧ IsFilter c ∧ ∀ a, φ a = c (h a)

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **170II** (`dils-examples-pure`, dils.tex:6195, Examples), part 1: the
pure maps `B(ℋ) → B(𝒦)` are precisely the maps `ad_T` for bounded
operators `T : 𝒦 → ℋ`. -/
theorem dils_examples_pure_1 (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    IsPureMap φ ↔ ∃ T : K →L[ℂ] H, ∀ a, φ a = conjOperator T a :=
  sorry

/-- **170II** (`dils-examples-pure`, dils.tex:6195, Examples), part 2: the
right-hand side `h` of any Paschke dilation is pure (it is `c ∘ h'` for a
filter `c` and corner `h'` by **169V** and **169XI**).

**170III** (Remark, the †-structure preview: there is a unique dagger on
the category of von Neumann algebras with pure maps, `(ad_V)† = ad_{V*}`;
see eff.tex 215III `dagger-theorem`) — not converted here. -/
theorem dils_examples_pure_2 (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    IsPureMap D.h :=
  sorry

/-- **170IV** (`surjective-nmiu`, dils.tex:6223, Exercise), first half:
every surjective nmiu-map **between von Neumann algebras** is a corner of a
central projection (hence pure).

The two `[VonNeumannAlgebra]` binders are the exercise's own hypothesis; they
were missing from the first transcription of this point, which therefore
claimed the result for arbitrary C\*-algebras (QUESTIONS **D5**, ruled on by
Bas: restore the hypothesis).  They are not decoration — the central
projection is produced by **69IV** `carrier_miu`, which needs them. -/
theorem surjective_nmiu_1 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ϱ : NMIUMap A B) (hs : Function.Surjective ⇑ϱ)
    (φ : NCPMap A B) (hφ : ∀ a, φ a = ϱ a) :
    ∃ z : A, IsStarProjection z ∧ IsCentral A z ∧ IsCornerFor φ z := by
  classical
  -- ### the algebra of `ϱ`
  have hϱmul : ∀ x y : A, (ϱ (x * y) : B) = ϱ x * ϱ y := fun x y =>
    map_mul ϱ.toStarAlgHom x y
  have hϱstar : ∀ x : A, (ϱ (star x) : B) = star (ϱ x) := fun x =>
    map_star ϱ.toStarAlgHom x
  have hϱadd : ∀ x y : A, (ϱ (x + y) : B) = ϱ x + ϱ y := fun x y =>
    map_add ϱ.toStarAlgHom x y
  have hϱsmul : ∀ (c : ℂ) (x : A), (ϱ (c • x) : B) = c • ϱ x := fun c x =>
    map_smul ϱ.toStarAlgHom c x
  have hϱone : (ϱ 1 : B) = 1 := map_one ϱ.toStarAlgHom
  have hϱmono : ∀ x y : A, x ≤ y → (ϱ x : B) ≤ ϱ y := fun _ _ h =>
    starAlgHom_mono ϱ.toStarAlgHom h
  -- ### the central projection `z = ⌈ϱ⌉`, from **69IV** `carrier_miu`
  -- The author routes `ker ϱ` through **69II** `weakly-closed-ideal`; 69IV is
  -- the same conclusion for the special case of an nmiu-map and is proved.
  obtain ⟨z, hzproj, hzcen, hzone, hker⟩ :
      ∃ z : A, IsStarProjection z ∧ IsCentral A z ∧ (ϱ z : B) = 1 ∧
        ∀ a b : A, ((ϱ a : B) = ϱ b ↔ z * a = z * b) := by
    refine ⟨carrier (nmiuP ϱ) ϱ.preservesDirSups', (carrier_spec _ _).1,
      (carrier_miu ϱ (nmiuP ϱ) ϱ.preservesDirSups' (fun _ => rfl)).1, ?_,
      fun a b =>
        (nmiu_factors ϱ (nmiuP ϱ) ϱ.preservesDirSups' (fun _ => rfl) a b).2⟩
    have h := (nmiu_factors ϱ (nmiuP ϱ) ϱ.preservesDirSups' (fun _ => rfl) 1 1).1
    rw [mul_one] at h
    rw [← h]
    exact map_one ϱ.toStarAlgHom
  have hzz : z * z = z := hzproj.isIdempotentElem.eq
  have hzstar : star z = z := hzproj.isSelfAdjoint.star_eq
  have he2 : ((1 : A) - z) * (1 - z) = 1 - z := hzproj.one_sub.isIdempotentElem.eq
  have hestar : star ((1 : A) - z) = 1 - z := hzproj.one_sub.isSelfAdjoint.star_eq
  have hecen : ∀ x : A, ((1 : A) - z) * x = x * (1 - z) := by
    intro x; rw [sub_mul, mul_sub, one_mul, mul_one, hzcen x]
  -- ### the section `σ : B → A` of `ϱ`, i.e. the inverse of `ϱ' : zA → B`
  obtain ⟨σ0, hσspec⟩ :
      ∃ σ0 : B → A, ∀ (b : B) (a : A), (ϱ a : B) = b → σ0 b = z * a := by
    refine ⟨fun b => z * Function.surjInv hs b, fun b a hab => ?_⟩
    exact (hker _ a).mp (by rw [Function.surjInv_eq hs b]; exact hab.symm)
  have hσϱ : ∀ a : A, σ0 (ϱ a) = z * a := fun a => hσspec _ a rfl
  have hϱσ : ∀ b : B, (ϱ (σ0 b) : B) = b := by
    intro b
    obtain ⟨a, ha⟩ := hs b
    rw [hσspec b a ha, hϱmul, hzone, one_mul, ha]
  have hσadd : ∀ b₁ b₂ : B, σ0 (b₁ + b₂) = σ0 b₁ + σ0 b₂ := by
    intro b₁ b₂
    obtain ⟨a₁, ha₁⟩ := hs b₁
    obtain ⟨a₂, ha₂⟩ := hs b₂
    rw [hσspec _ (a₁ + a₂) (by rw [hϱadd, ha₁, ha₂]), hσspec _ a₁ ha₁,
      hσspec _ a₂ ha₂, mul_add]
  have hσsmul : ∀ (c : ℂ) (b : B), σ0 (c • b) = c • σ0 b := by
    intro c b
    obtain ⟨a, ha⟩ := hs b
    rw [hσspec _ (c • a) (by rw [hϱsmul, ha]), hσspec _ a ha, mul_smul_comm]
  have hσsub : ∀ b₁ b₂ : B, σ0 (b₁ - b₂) = σ0 b₁ - σ0 b₂ := by
    intro b₁ b₂
    have hneg : σ0 (-b₂) = -σ0 b₂ := by
      have h := hσsmul (-1) b₂; simpa using h
    rw [sub_eq_add_neg, hσadd, hneg, ← sub_eq_add_neg]
  have hσmul : ∀ b₁ b₂ : B, σ0 (b₁ * b₂) = σ0 b₁ * σ0 b₂ := by
    intro b₁ b₂
    obtain ⟨a₁, ha₁⟩ := hs b₁
    obtain ⟨a₂, ha₂⟩ := hs b₂
    rw [hσspec _ (a₁ * a₂) (by rw [hϱmul, ha₁, ha₂]), hσspec _ a₁ ha₁,
      hσspec _ a₂ ha₂]
    calc z * (a₁ * a₂) = (z * z) * (a₁ * a₂) := by rw [hzz]
      _ = z * (z * a₁) * a₂ := by noncomm_ring
      _ = z * (a₁ * z) * a₂ := by rw [hzcen a₁]
      _ = (z * a₁) * (z * a₂) := by noncomm_ring
  have hσstar : ∀ b : B, σ0 (star b) = star (σ0 b) := by
    intro b
    obtain ⟨a, ha⟩ := hs b
    rw [hσspec _ (star a) (by rw [hϱstar, ha]), hσspec _ a ha, star_mul, hzstar]
    exact hzcen (star a)
  -- `σ` is positive — it is a (non-unital) ∗-homomorphism — hence monotone
  have hσnonneg : ∀ b : B, 0 ≤ b → 0 ≤ σ0 b := by
    intro b hb
    have hsq : CFC.sqrt b * CFC.sqrt b = b := CFC.sqrt_mul_sqrt_self b hb
    have hsa : IsSelfAdjoint (CFC.sqrt b) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)
    have h : σ0 b = star (σ0 (CFC.sqrt b)) * σ0 (CFC.sqrt b) := by
      rw [← hσstar, hsa.star_eq, ← hσmul, hsq]
    rw [h]
    exact star_mul_self_nonneg _
  have hσmono : ∀ b₁ b₂ : B, b₁ ≤ b₂ → σ0 b₁ ≤ σ0 b₂ := by
    intro b₁ b₂ h
    have h0 := hσnonneg _ (sub_nonneg.mpr h)
    rw [hσsub] at h0
    exact sub_nonneg.mp h0
  -- `σ` kills nothing and lands in `zA`
  have hσz : ∀ b : B, ((1 : A) - z) * σ0 b = 0 := by
    intro b
    obtain ⟨a, ha⟩ := hs b
    rw [hσspec b a ha]
    calc ((1 : A) - z) * (z * a) = (z - z * z) * a := by noncomm_ring
      _ = 0 := by rw [hzz, sub_self, zero_mul]
  -- `σ` is normal: an upper bound `u` of `σ(D)` satisfies `(1−z)u ≥ 0`, so
  -- `σ(⋁D) ≤ σ(ϱ(u)) = zu ≤ u`
  have hσnormal : PreservesDirSups σ0 := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact hσmono _ _ (hlub.1 hd)
    · intro u hu
      obtain ⟨d₀, hd₀⟩ := hne
      have hd₀le : σ0 (d₀ : B) ≤ u := hu ⟨d₀, hd₀, rfl⟩
      have hd₀sa : IsSelfAdjoint (σ0 (d₀ : B)) := by
        show star (σ0 (d₀ : B)) = σ0 (d₀ : B)
        rw [← hσstar, show star (d₀ : B) = d₀ from d₀.2]
      have husa : IsSelfAdjoint u := by
        have h1 : IsSelfAdjoint (u - σ0 (d₀ : B)) :=
          IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hd₀le)
        have h2 := h1.add hd₀sa
        simpa using h2
      have hϱusa : IsSelfAdjoint (ϱ u : B) := by
        show star (ϱ u : B) = ϱ u
        rw [← hϱstar, husa.star_eq]
      -- `(1−z)u ≥ 0`
      have heu : (0 : A) ≤ ((1 : A) - z) * u := by
        have h0 : (0 : A) ≤ star ((1 : A) - z) * (u - σ0 (d₀ : B)) * (1 - z) :=
          star_left_conjugate_nonneg (sub_nonneg.mpr hd₀le) _
        rw [hestar] at h0
        have hrw : ((1 : A) - z) * (u - σ0 (d₀ : B)) * (1 - z)
            = ((1 : A) - z) * u := by
          calc ((1 : A) - z) * (u - σ0 (d₀ : B)) * (1 - z)
              = ((1 : A) - z) * (((1 : A) - z) * (u - σ0 (d₀ : B))) := by
                rw [mul_assoc, ← hecen]
            _ = (((1 : A) - z) * (1 - z)) * (u - σ0 (d₀ : B)) := by
                rw [mul_assoc]
            _ = ((1 : A) - z) * (u - σ0 (d₀ : B)) := by rw [he2]
            _ = ((1 : A) - z) * u - ((1 : A) - z) * σ0 (d₀ : B) := by rw [mul_sub]
            _ = ((1 : A) - z) * u := by rw [hσz, sub_zero]
        rwa [hrw] at h0
      -- `s ≤ ϱ(u)`
      have hub : (⟨(ϱ u : B), hϱusa⟩ : selfAdjoint B) ∈ upperBounds D := by
        intro d hd
        show (d : B) ≤ ϱ u
        have h1 : σ0 (d : B) ≤ u := hu ⟨d, hd, rfl⟩
        have h2 : (ϱ (σ0 (d : B)) : B) ≤ ϱ u := hϱmono _ _ h1
        rwa [hϱσ] at h2
      have hsle : (s : B) ≤ ϱ u := hlub.2 hub
      have h3 : σ0 (s : B) ≤ z * u := by
        have h4 := hσmono _ _ hsle
        rwa [hσϱ] at h4
      refine h3.trans ?_
      have h5 : u - z * u = ((1 : A) - z) * u := by noncomm_ring
      rw [← sub_nonneg, h5]
      exact heu
  -- `σ` as an ncp-map: a ∗-homomorphism is completely positive (**34IV**.3)
  obtain ⟨σ, hσ⟩ : ∃ σ : NCPMap B A, ∀ b, σ b = σ0 b := by
    refine ⟨{ toCompletelyPositiveMap :=
                { toLinearMap :=
                    { toFun := σ0
                      map_add' := hσadd
                      map_smul' := fun c b => hσsmul c b }
                  map_cstarMatrix_nonneg' := by
                    refine (cp_iff _).out 0 1 |>.mp (cp_of_mi _ ?_ ?_)
                    · intro x y; exact hσmul x y
                    · intro x; exact hσstar x }
              preservesDirSups' := hσnormal }, fun _ => rfl⟩
  -- ### `z` is the corner
  refine ⟨z, hzproj, hzcen, Set.mem_Icc.mpr ⟨hzproj.nonneg, hzproj.le_one⟩, ?_, ?_⟩
  · rw [hφ, hφ, hzone, hϱone]
  intro C _ _ _ f hfz
  -- `f((1−z)x) = 0` by Kadison–Schwarz (**34XIV** `cp-cs`), since `f(1−z) = 0`
  have hLfcp : IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
    (cp_iff _).out 1 0 |>.mp fun N M hM =>
      f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hLfpos : IsPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
    astara_pos_basic_2_cp _ hLfcp
  have hLfval : ∀ x : A, f.toCompletelyPositiveMap.toLinearMap x = f x := fun _ => rfl
  have hfsub : ∀ x y : A, (f (x - y) : C) = f x - f y := fun x y =>
    map_sub f.toCompletelyPositiveMap.toLinearMap x y
  have hfe : (f ((1 : A) - z) : C) = 0 := by rw [hfsub, hfz, sub_self]
  have hkill : ∀ x : A, (f (((1 : A) - z) * x) : C) = 0 := by
    intro x
    have h := cp_cs f.toCompletelyPositiveMap.toLinearMap hLfpos
      (fun a b => hLfcp 2 a b) x ((1 : A) - z)
    rw [hestar, he2] at h
    simp only [hLfval] at h
    rw [hfe, norm_zero, zero_smul] at h
    have hsa : (f (star x * ((1 : A) - z)) : C) = star (f (((1 : A) - z) * x)) := by
      have h1 := cstar_p_implies_i _ hLfpos (((1 : A) - z) * x)
      rw [star_mul, hestar] at h1
      simpa only [hLfval] using h1
    rw [hsa] at h
    have h0 : (0 : C) ≤ star (f (((1 : A) - z) * x)) * f (((1 : A) - z) * x) :=
      star_mul_self_nonneg _
    exact (CStarRing.star_mul_self_eq_zero_iff _).mp (le_antisymm h h0)
  have hfzx : ∀ x : A, (f (z * x) : C) = f x := by
    intro x
    have h := hkill x
    rw [sub_mul, one_mul, hfsub, sub_eq_zero] at h
    exact h.symm
  -- the factorisation `f' = f ∘ σ`, unique because `ϱ` is surjective
  obtain ⟨k, hk⟩ := exists_ncpComp f σ
  refine ⟨k, fun x => ?_, fun k' hk' => ?_⟩
  · rw [hk, hσ, hφ, hσϱ, hfzx]
  · refine DFunLike.ext _ _ fun b => ?_
    obtain ⟨a, ha⟩ := hs b
    have h1 : (φ a : B) = b := by rw [hφ, ha]
    rw [← h1, hk' a, hk, hσ, hφ, hσϱ, hfzx]

/-- **170IV** (`surjective-nmiu`, dils.tex:6223, Exercise), second half:
conversely, every corner of a central projection **in a von Neumann
algebra** is (equal as a map to) a surjective nmiu-map.  (For the
`[VonNeumannAlgebra]` binders see the first half.) -/
theorem surjective_nmiu_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (z : A)
    (hz : IsStarProjection z) (hcentral : IsCentral A z)
    (hφ : IsCornerFor φ z) :
    ∃ ϱ : NMIUMap A B, (∀ a, ϱ a = φ a) ∧ Function.Surjective ⇑ϱ :=
  sorry

end Pure

/-! ## Parsec 1710: purity via the Paschke dilation

**171I** (dils.tex:6232): introduction; **171III**–**171VI** and
**171VIII** are proofs — not converted. -/

section PaschkePure

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **171II** (`paschke-corner`, dils.tex:6237, Theorem): for a projection
`p` in a von Neumann algebra `A`, a Paschke dilation of the standard
corner `h_p : A → pAp` is `(⌈⌈p⌉⌉A, h_{⌈⌈p⌉⌉}, h'_p)`, where `⌈⌈p⌉⌉` is
the central carrier of `p`, `h_{⌈⌈p⌉⌉}` the standard corner for `⌈⌈p⌉⌉`,
and `h'_p` the restriction of `h_p` to `⌈⌈p⌉⌉A`.

The hypothesis `IsStarProjection p` of the thesis is carried as an instance
`[Fact (IsStarProjection p)]`, which is what the corner `pAp` needs to be an
algebra at all (see `cornerSet.instCStarAlgebra`).  That `⌈⌈p⌉⌉` is a
projection too is **68III**, now proved in `Theses.A.VN.Projections`, so it
is supplied by `fact_isStarProjection_cceil` rather than assumed. -/
theorem paschke_corner [VonNeumannAlgebra A] (p : A)
    [Fact (IsStarProjection p)]
    (hp' : NCPMap A (cornerSet A p))
    (hval : ∀ a : A, (hp' a).1 = p * a * p) :
    ∃ (ρ : NMIUMap A (cornerSet A (cceil p)))
      (h : NCPMap (cornerSet A (cceil p)) (cornerSet A p)),
      (∀ a : A, (ρ a).1 = cceil p * a * cceil p) ∧
      (∀ c : cornerSet A (cceil p), (h c).1 = p * c.1 * p) ∧
      IsPaschkeDilationOf
        ⟨cornerSet A (cceil p), cornerSet_vonNeumannAlgebra A (cceil p),
          ρ, h⟩ ⇑hp' :=
  sorry

/-- **171VII** (`paschke-pure`, dils.tex:6365, Theorem): an ncp-map `φ`
with Paschke dilation `(𝒫, ϱ, h)` is pure if and only if `ϱ` is
surjective. -/
theorem paschke_pure [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    IsPureMap φ ↔ Function.Surjective ⇑D.ρ :=
  sorry

end PaschkePure

/-! ## Parsec 1720: ncp-extreme maps

**172I** (dils.tex:6404): introduction; **172IV**–**172VII**, **172IX**,
**172XI** are proofs — not converted. -/

section Extreme

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **172II** (dils.tex:6408, Definition): an ncp-map `φ` is
**ncp-extreme** when it is an extreme point among the ncp-maps with the
same value on `1`: `λφ₁ + (1-λ)φ₂ = φ` with `0 < λ < 1` and
`φ₁(1) = φ₂(1) = φ(1)` forces `φ₁ = φ₂ = φ`. -/
def NCPExtreme (φ : NCPMap A B) : Prop :=
  ∀ l : ℝ, 0 < l → l < 1 → ∀ φ₁ φ₂ : NCPMap A B,
    φ₁ 1 = φ 1 → φ₂ 1 = φ 1 →
    (∀ a, φ a = (l : ℂ) • φ₁ a + ((1 - l : ℝ) : ℂ) • φ₂ a) →
    (∀ a, φ₁ a = φ a) ∧ ∀ a, φ₂ a = φ a

/-- **172III** (`ncp-extreme-paschke`, dils.tex:6426, Theorem): for an
ncp-map `φ` with Paschke dilation `(𝒫, ϱ, h)` the following are
equivalent: (1) `h` is injective on the commutant `ϱ(A)′`; (2) `h` is
injective on `[0,1]_{ϱ(A)′}`; (3) `φ` is ncp-extreme. -/
theorem ncp_extreme_paschke [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    List.TFAE
      [Set.InjOn ⇑D.h (commutant D.P (Set.range ⇑D.ρ)),
       Set.InjOn ⇑D.h
         (commutant D.P (Set.range ⇑D.ρ) ∩ Set.Icc (0 : D.P) 1),
       NCPExtreme φ] :=
  sorry

/-- **172VIII** (`nmiu-ncp-extreme`, dils.tex:6512, Corollary): every
nmiu-map (as an ncp-map) is ncp-extreme. -/
theorem nmiu_ncp_extreme (ϱ : NMIUMap A B) (φ : NCPMap A B)
    (hφ : ∀ a, φ a = ϱ a) :
    NCPExtreme φ := by
  -- The author's proof (**172IX**) is: `(ℬ, ϱ, id)` is a Paschke dilation of
  -- `ϱ` and `id` is injective, so **172III** `ncp_extreme_paschke` applies.
  -- That theorem is still `sorry`, so we argue directly instead, by strict
  -- convexity of `b ↦ b* b` together with Choi's inequality **34XVIII**.1.
  intro l hl0 hl1 φ₁ φ₂ h1 h2 hsum
  -- Kadison–Schwarz for a unital ncp-map (**34XVIII**.1 `choi_1`).
  have kad : ∀ ψ : NCPMap A B, ψ 1 = 1 → ∀ a : A,
      star (ψ a) * ψ a ≤ ψ (star a * a) := by
    intro ψ hu a
    set f : A →ₗ[ℂ] B := ψ.toCompletelyPositiveMap.toLinearMap with hf
    have hcp : IsCompletelyPositiveMap f :=
      (cp_iff f).out 1 0 |>.mp fun N M hM =>
        ψ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
    exact choi_1 f hcp hu a
  have hϱ1 : φ (1 : A) = 1 := by rw [hφ]; exact map_one ϱ.toStarAlgHom
  have hu1 : φ₁ (1 : A) = 1 := by rw [h1, hϱ1]
  have hu2 : φ₂ (1 : A) = 1 := by rw [h2, hϱ1]
  set L : ℂ := (l : ℂ) with hLdef
  have hNL : ((1 - l : ℝ) : ℂ) = 1 - L := by rw [hLdef]; push_cast; ring
  -- The heart: `φ₁` and `φ₂` agree.
  have key : ∀ a : A, φ₁ a = φ₂ a := by
    intro a
    set b₁ := φ₁ a with hb1
    set b₂ := φ₂ a with hb2
    set d₁ := φ₁ (star a * a) - star b₁ * b₁ with hd1def
    set d₂ := φ₂ (star a * a) - star b₂ * b₂ with hd2def
    set e := star (b₁ - b₂) * (b₁ - b₂) with hedef
    have hd1 : 0 ≤ d₁ := sub_nonneg.mpr (kad φ₁ hu1 a)
    have hd2 : 0 ≤ d₂ := sub_nonneg.mpr (kad φ₂ hu2 a)
    have he : (0 : B) ≤ e := star_mul_self_nonneg _
    -- `ϱ` is multiplicative and involution preserving
    have hmul : φ (star a * a) = star (φ a) * φ a := by
      have hm : ϱ (star a * a) = ϱ (star a) * ϱ a := map_mul ϱ.toStarAlgHom _ _
      have hst : ϱ (star a) = star (ϱ a) := map_star ϱ.toStarAlgHom a
      rw [hφ, hm, hst, hφ a]
    have hsa : φ a = L • b₁ + (1 - L) • b₂ := by
      rw [hsum a, hNL, hb1, hb2]
    have hs2 : φ (star a * a) = L • φ₁ (star a * a) + (1 - L) • φ₂ (star a * a) := by
      rw [hsum (star a * a), hNL]
    -- strict convexity of `b ↦ b* b`
    have hid : L • (star b₁ * b₁) + (1 - L) • (star b₂ * b₂)
        - (L * (1 - L)) • e
        = star (L • b₁ + (1 - L) • b₂) * (L • b₁ + (1 - L) • b₂) := by
      have hLs : star L = L := by rw [hLdef]; exact Complex.conj_ofReal l
      simp only [hedef, star_add, star_smul, star_sub, hLs, star_one,
        smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, add_mul, mul_add,
        smul_sub, smul_add, sub_smul]
      match_scalars <;> ring
    have hbal : L • φ₁ (star a * a) + (1 - L) • φ₂ (star a * a)
        = L • (star b₁ * b₁) + (1 - L) • (star b₂ * b₂) - (L * (1 - L)) • e := by
      rw [hid, ← hsa, ← hs2, hmul]
    have hzero : L • d₁ + (1 - L) • d₂ + (L * (1 - L)) • e = 0 := by
      have hrw : L • d₁ + (1 - L) • d₂ + (L * (1 - L)) • e
          = (L • φ₁ (star a * a) + (1 - L) • φ₂ (star a * a))
            - (L • (star b₁ * b₁) + (1 - L) • (star b₂ * b₂)
                - (L * (1 - L)) • e) := by
        rw [hd1def, hd2def]; module
      rw [hrw, hbal, sub_self]
    -- all three summands are positive, so all three vanish
    have hp1 : (0 : B) ≤ L • d₁ := cstar_positive_1 _ hd1 l hl0.le
    have hp2 : (0 : B) ≤ (1 - L) • d₂ := by
      rw [← hNL]; exact cstar_positive_1 _ hd2 (1 - l) (by linarith)
    have hp3 : (0 : B) ≤ (L * (1 - L)) • e := by
      have hc : L * (1 - L) = ((l * (1 - l) : ℝ) : ℂ) := by
        rw [hLdef]; push_cast; ring
      rw [hc]
      exact cstar_positive_1 _ he _ (by nlinarith)
    have hz : (L * (1 - L)) • e = 0 := by
      refine le_antisymm ?_ hp3
      have : (L * (1 - L)) • e ≤ L • d₁ + (1 - L) • d₂ + (L * (1 - L)) • e := by
        have := add_le_add hp1 hp2
        rw [add_zero] at this
        simpa using add_le_add_right this ((L * (1 - L)) • e)
      rwa [hzero] at this
    have hcne : L * (1 - L) ≠ 0 := by
      have h1' : L ≠ 0 := by
        rw [hLdef]; exact_mod_cast ne_of_gt hl0
      have h2' : (1 : ℂ) - L ≠ 0 := by
        rw [← hNL]
        exact_mod_cast ne_of_gt (show (0 : ℝ) < 1 - l by linarith)
      exact mul_ne_zero h1' h2'
    have he0 : e = 0 := by
      have h := congrArg (fun x : B => (L * (1 - L))⁻¹ • x) hz
      simp only [smul_smul, inv_mul_cancel₀ hcne, one_smul, smul_zero] at h
      exact h
    have hnorm : ‖b₁ - b₂‖ * ‖b₁ - b₂‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, ← hedef, he0, norm_zero]
    have : b₁ - b₂ = 0 := by
      have := mul_self_eq_zero.mp hnorm
      exact norm_eq_zero.mp this
    exact sub_eq_zero.mp this
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have hs := hsum a
    rw [← key a, hNL, ← add_smul] at hs
    rw [hs, hLdef]
    rw [show (l : ℂ) + (1 - (l : ℂ)) = 1 by ring, one_smul]
  · have hs := hsum a
    rw [key a, hNL, ← add_smul] at hs
    rw [hs, hLdef]
    rw [show (l : ℂ) + (1 - (l : ℂ)) = 1 by ring, one_smul]

/-- **172X** (dils.tex:6520, Theorem): every pure ncp-map is
ncp-extreme. -/
theorem pure_ncp_extreme [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (hpure : IsPureMap φ) :
    NCPExtreme φ :=
  sorry

/-- **172XII** (`ncp-extreme-comp`, dils.tex:6544, Corollary): every
ncp-map is the composition of two ncp-extreme maps. -/
theorem ncp_extreme_comp [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) :
    ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C) (ψ₁ : NCPMap A C) (ψ₂ : NCPMap C B),
      NCPExtreme ψ₁ ∧ NCPExtreme ψ₂ ∧ ∀ a, φ a = ψ₂ (ψ₁ a) :=
  sorry

end Extreme

end Theses.B.Dils
