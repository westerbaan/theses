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
`f = c ∘ f'`). -/
def IsFilterFor (c : NCPMap A B) (b : B) : Prop :=
  0 ≤ b ∧ c 1 ≤ b ∧
  ∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (f : NCPMap C B), f 1 ≤ b →
    ∃! f' : NCPMap C A, ∀ x, c (f' x) = f x

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

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 1: if `(𝒫, ϱ, h)` is a Paschke dilation of `φ : A → B` and
`c : B → C` a filter, then `(𝒫, ϱ, c ∘ h)` is a Paschke dilation of
`c ∘ φ`. -/
theorem dils_filter_basics_1 {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) (c : NCPMap B C) (hc : IsFilter c) :
    ∃ h' : NCPMap D.P C, (∀ x, h' x = c (D.h x)) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ fun a => c (φ a) :=
  sorry

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 2, first half: for a filter `c' : C' → B` of `φ(1)` there is a unique
unital ncp-map `φ'` with `φ = c' ∘ φ'`. -/
theorem dils_filter_basics_2a {C' : Type u} [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (φ : NCPMap A B)
    (c' : NCPMap C' B) (hc : IsFilterFor c' (φ 1)) :
    ∃! φ' : NCPMap A C', φ' 1 = 1 ∧ ∀ a, c' (φ' a) = φ a :=
  sorry

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6158, Exercise),
part 2, second half: if moreover `(𝒫, ϱ, h)` is a Paschke dilation of
`φ'`, then `(𝒫, ϱ, c' ∘ h)` is a Paschke dilation of `φ`. -/
theorem dils_filter_basics_2b {C' : Type u} [CStarAlgebra C']
    [PartialOrder C'] [StarOrderedRing C'] (φ : NCPMap A B)
    (c' : NCPMap C' B) (hc : IsFilterFor c' (φ 1)) (φ' : NCPMap A C')
    (hφ' : φ' 1 = 1 ∧ ∀ a, c' (φ' a) = φ a) (D : PaschkeTriple A C')
    (hD : IsPaschkeDilationOf D ⇑φ') :
    ∃ h' : NCPMap D.P B, (∀ x, h' x = c' (D.h x)) ∧
      IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, h'⟩ ⇑φ :=
  sorry

/-- **169XII** (`dils-filters-injective`, dils.tex:6180, Exercise): filters
are injective. -/
theorem dils_filters_injective (c : NCPMap A B) (hc : IsFilter c) :
    Function.Injective ⇑c :=
  sorry

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
every surjective nmiu-map is a corner of a central projection (hence
pure). -/
theorem surjective_nmiu_1 (ϱ : NMIUMap A B) (hs : Function.Surjective ⇑ϱ)
    (φ : NCPMap A B) (hφ : ∀ a, φ a = ϱ a) :
    ∃ z : A, IsStarProjection z ∧ IsCentral A z ∧ IsCornerFor φ z :=
  sorry

/-- **170IV** (`surjective-nmiu`, dils.tex:6223, Exercise), second half:
conversely, every corner of a central projection is (equal as a map to) a
surjective nmiu-map. -/
theorem surjective_nmiu_2 (φ : NCPMap A B) (z : A)
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
