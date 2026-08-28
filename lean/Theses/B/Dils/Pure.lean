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
development, which should be merged with this one.

⚠️ **The two developments are not interchangeable, and the merge is a
project rather than an edit.**  `Theses.A.Proc.Measurement` *is* on this
file's import path (`Theses.B.Dils.SelfDual → Theses.A.Proc.Tensor →
Theses.A.Proc.Measurement`), so its declarations are already reachable — the
earlier claim that it is "off this import path", repeated in several doc
comments below, was wrong.  What blocks reuse is that the predicates differ:

* `IsCornerFor`/`IsFilterFor` here quantify their test object over
  **C\*-algebras**, where `Theses.A.Proc.IsCornerOf`/`.IsFilter` quantify
  over **von Neumann algebras** — so ours are strictly *stronger* and cannot
  be obtained from theirs;
* `IsFilterFor` here carries the author's 2026-08-16 repair (the mediating
  map is **subunital**, `NCPSUMap`) and a filtered element `b` with only
  `c 1 ≤ b`, where `Theses.A.Proc.IsFilter` has an unrepaired *ncp*
  mediating map and reads `f 1 ≤ c 1`;
* `Theses.A.Proc.IsCornerMap` (the corner half of its `IsPure`) is
  **unital**, where `IsCorner` here is not;
* `Theses.A.Proc.IsPure` is the inductive "filters, corners and their
  composites" of **170I**, with a `[VonNeumannAlgebra]` binder on every
  intermediate algebra, where `IsPureMap` here is the normal form.

Consequently proc.tex **100III** `Theses.A.Proc.pure_fundamental` — proved,
and reachable — does *not* bridge `Theses.A.Proc.IsPure` to `IsPureMap`;
see the doc of `IsPureMap` at parsec 1700.
-/
import Theses.B.Dils.SelfDual

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
open Filter Topology Theses Theses.A.CStar Theses.A.VN

universe u

namespace Theses.B.Dils

/-! **168I**–**168IV** (dils.tex:5976–6054, `dils-pure-discussion`):
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
own bundled corner type `Theses.A.Proc.Corner A e` (reachable from here —
see the file header — but built on a different set of instances); the two
should be merged. -/

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
`a ↦ p·a·p` is normal (**44VIII** `ad_normal`) and fixes the set.

Stated before `saMap_isLUB`, which is the same fact read as "suprema of the
corner are computed in `A`". -/
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

/-- **94II** part 6: a directed supremum of the corner *is* the supremum
taken in `A` — `saMap` carries an `IsLUB` in `sa(pAp)` to an `IsLUB` in
`sa(A)`.  The supremum in `A` exists because `A` is a von Neumann algebra,
lies in the corner by `isLUB_mem`, and is then a least upper bound there
as well; uniqueness of least upper bounds identifies it with `s`. -/
theorem saMap_isLUB {D : Set (selfAdjoint (cornerSet A p))}
    {s : selfAdjoint (cornerSet A p)} (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hlub : IsLUB D s) :
    IsLUB (saMap '' D) (saMap s) := by
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

/-- The inclusion `pAp ⊆ A` preserves directed suprema, for **any**
projection `p` — a direct consequence of `saMap_isLUB`.  (No centrality is
needed: the point is not that the corner is a direct summand, but that its
suprema are computed in `A`.) -/
theorem val_normal : PreservesDirSups (fun c : cornerSet A p => c.1) := by
  intro D s hne hdir hlub
  have h := isLUB_coe_of_isLUB (hne.image _) (saMap_isLUB hne hdir hlub)
  have himg : Subtype.val '' (saMap '' D)
      = (fun d : selfAdjoint (cornerSet A p) => ((d : cornerSet A p)).1) '' D := by
    rw [← Set.image_comp]; rfl
  rwa [himg] at h

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
    have hlub' : IsLUB (saMap '' D) (saMap s) := saMap_isLUB hne hdir hlub
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

**169I** (dils.tex:6064) and **169VII** (dils.tex:6121): introduction —
nothing to formalize.  **169III**, **169IX** (Remarks) — not converted. -/

section CornersFilters

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **169II** (`dils-corner`, dils.tex:6068, Definition): an ncp-map
`h : A → B` is a **corner** for an effect `a ∈ [0,1]_A` when `h(a) = h(1)`
and every ncp-map `f : A → C` with `f(a) = f(1)` factors uniquely through
`h` (as `f = f' ∘ h`). -/
def IsCornerFor (h : NCPMap A B) (a : A) : Prop :=
  a ∈ effects A ∧ h a = h 1 ∧
  ∀ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (f : NCPMap A C), f a = f 1 →
    ∃! f' : NCPMap B C, ∀ x, f' (h x) = f x

/-- **169II** (`dils-corner`, dils.tex:6068, Definition): a **corner** is
an ncp-map which is a corner for some effect. -/
def IsCorner (h : NCPMap A B) : Prop :=
  ∃ a : A, IsCornerFor h a

/-! ### Auxiliary: ncp-maps compose

`Theses/B/Dils/Stinespring.lean` carries the same constructions, but as
`private` declarations, so they are repeated here rather than exported (a
merge is noted in that file's header).  They are placed here, before parsec
1690, because **169IV** already needs the composite `f ∘ ζ`. -/

/-- The **identity ncp-map** `P → P`.  (Complete positivity and normality of
the identity are both immediate; `Theses.A.Proc.ncpId` is the same map, built
there from an existential.) -/
noncomputable def ncpId (P : Type*) [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] : NCPMap P P where
  toCompletelyPositiveMap :=
    { toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := fun _ _ hM => by simpa using hM }
  preservesDirSups' := by
    intro D s hne _ hlub
    exact isLUB_coe_of_isLUB hne hlub

@[simp] theorem ncpId_apply {P : Type*} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] (a : P) : ncpId P a = a := rfl

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

/-! ### **169IV**: the standard corner `h_a : A → ⌊a⌋A⌊a⌋`

dils.tex states 169IV as an Example, citing proc.tex **95II** `prop-corner`,
which proves it for a partial isometry `u` with `⌊p⌋ = uu*`; the standard
corner is the case `u = ⌊a⌋`, where `u*u = uu* = ⌊a⌋` and `π(b) = ⌊a⌋b⌊a⌋`.
That proof runs:

* `π` is ncp (**44X** `ad-ncp`);
* `π(a^⊥) = 0`, i.e. `⌊a⌋a⌊a⌋ = ⌊a⌋`;
* uniqueness of the mediating map, from surjectivity of `π`;
* existence: the mediating map is `f ∘ ζ` for the inclusion
  `ζ : ⌊a⌋A⌊a⌋ ⊆ A`, and `f = f ∘ ζ ∘ π` is **63IV** `cp-comprehension`,
  whose hypothesis `f(⌊a⌋^⊥) = 0` follows from
  `⌈f(⌊a⌋^⊥)⌉ = ⌈f(⌈a^⊥⌉)⌉ = ⌈f(a^⊥)⌉ = ⌈0⌉ = 0`.

Two divergences, both forced by our `IsCornerFor` being *more general* than
the thesis's definition, which quantifies its test object over von Neumann
algebras where ours quantifies over C*-algebras (**a stronger statement**,
since the universal property has to hold against more maps `f`):

* the last step cannot go through **60V** `ncp_ceil`, which computes a
  ceiling in the *target*.  We use the thesis's own construction of the
  ceiling instead — `⌈b⌉ = ⋁ₙ b^{1/2ⁿ}` (**56I** `vna_ceil_sup`) — together
  with Kadison's inequality (**34XIV** `cp-cs`, as `ncp_cp_cs`) to get from
  `f(b) = 0` to `f(√b) = 0`;
* `ζ` is ncp by `cornerSet.val_normal`, which needs no centrality and no
  `ad-ncp`; the corner's suprema simply *are* those of `A`. -/

section StandardCorner

set_option linter.unusedSectionVars false

variable {A C : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- If an ncp-map kills a positive `b`, it kills `√b`: Kadison's inequality
gives `f(√b)* f(√b) ≤ ‖f(1)‖·f(√b* √b) = ‖f(1)‖·f(b) = 0`. -/
private theorem ncp_eq_zero_sqrt (f : NCPMap A C) {b : A} (hb : 0 ≤ b)
    (h : (f b : C) = 0) : (f (CFC.sqrt b) : C) = 0 := by
  have hsa : IsSelfAdjoint (CFC.sqrt b) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)
  have hbb : star (CFC.sqrt b) * CFC.sqrt b = b := by
    rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self b hb]
  have hcs := ncp_cp_cs f (CFC.sqrt b)
  rw [hbb, h, smul_zero] at hcs
  exact (CStarRing.star_mul_self_eq_zero_iff _).mp
    (le_antisymm hcs (star_mul_self_nonneg _))

/-- **169IV**, the only real step: an ncp-map that kills an effect `b`
kills `⌈b⌉`, because `b^{1/2ⁿ} ↑ ⌈b⌉` (**56I** `vna_ceil_sup`) and `f`
kills every `b^{1/2ⁿ}` by `ncp_eq_zero_sqrt`. -/
private theorem ncp_eq_zero_ceil [VonNeumannAlgebra A] (f : NCPMap A C)
    {b : A} (hb : b ∈ effects A) (h : (f b : C) = 0) :
    (f (ceil b) : C) = 0 := by
  set g : ℕ → A := fun n => (fun x : A => CFC.sqrt x)^[n] b with hg
  have hgsucc : ∀ n, g (n + 1) = CFC.sqrt (g n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hgeff : ∀ n, g n ∈ effects A := by
    intro n
    induction n with
    | zero => exact hb
    | succ n ih => rw [hgsucc]; exact sqrt_mem_effects ih
  have hgzero : ∀ n, (f (g n) : C) = 0 := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => rw [hgsucc]; exact ncp_eq_zero_sqrt f (hgeff n).1 ih
  have hmono : Monotone g := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hmul := mul_self_le_self (sqrt_mem_effects (hgeff n))
    rwa [CFC.sqrt_mul_sqrt_self _ (hgeff n).1, ← hgsucc] at hmul
  set E : ℕ → selfAdjoint A := fun n =>
    ⟨g n, IsSelfAdjoint.of_nonneg (hgeff n).1⟩ with hE
  set D : Set (selfAdjoint A) := Set.range E with hD
  have hne : D.Nonempty := ⟨E 0, 0, rfl⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨E (max m n), ⟨max m n, rfl⟩,
      Subtype.coe_le_coe.mp (hmono (le_max_left m n)),
      Subtype.coe_le_coe.mp (hmono (le_max_right m n))⟩
  have hceilsa : IsSelfAdjoint (ceil b) := (ceil_spec hb.1).1.isSelfAdjoint
  have hlub : IsLUB D (⟨ceil b, hceilsa⟩ : selfAdjoint A) := by
    refine isLUB_sa_of_isLUB ?_
    have himg : Subtype.val '' D = Set.range g := by
      rw [hD, ← Set.range_comp]; rfl
    rw [himg]
    exact vna_ceil_sup b hb
  have hkey := f.preservesDirSups' D _ hne hdir hlub
  have hub0 : (0 : C) ∈ upperBounds
      ((fun d : selfAdjoint A => (f (d : A) : C)) '' D) := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact le_of_eq (hgzero n)
  have hmem0 : (f (g 0) : C) ∈ (fun d : selfAdjoint A => (f (d : A) : C)) '' D :=
    ⟨E 0, ⟨0, rfl⟩, rfl⟩
  have hge := hkey.1 hmem0
  rw [hgzero 0] at hge
  exact le_antisymm (hkey.2 hub0) hge

variable [VonNeumannAlgebra A] {p : A} [Fact (IsStarProjection p)]

/-- An `IsLUB` in `A` that lands in the corner is an `IsLUB` in the corner
(the order of `pAp` being the one inherited from `A`). -/
private theorem cornerSet_isLUB_of_isLUB {S : Set (cornerSet A p)}
    {t : cornerSet A p} (h : IsLUB (Subtype.val '' S) t.1) : IsLUB S t :=
  ⟨fun x hx => h.1 ⟨x, hx, rfl⟩,
    fun u hu => h.2 (by rintro _ ⟨x, hx, rfl⟩; exact hu hx)⟩

/-- The **standard corner** `h_p : A → pAp`, `b ↦ pbp`, of a projection `p`,
as a linear map. -/
private noncomputable def cornerLin (p : A) [Fact (IsStarProjection p)] :
    A →ₗ[ℂ] cornerSet A p where
  toFun b := ⟨p * b * p, by
    have hpp : p * p = p := (cornerSet.proj p).isIdempotentElem.eq
    calc p * (p * b * p) * p = (p * p) * b * (p * p) := by noncomm_ring
      _ = p * b * p := by rw [hpp]⟩
  map_add' x y := Subtype.ext (by
    show p * (x + y) * p = p * x * p + p * y * p
    noncomm_ring)
  map_smul' r x := Subtype.ext (by
    show p * (r • x) * p = r • (p * x * p)
    rw [mul_smul_comm, smul_mul_assoc])

@[simp] private theorem cornerLin_val (b : A) :
    (cornerLin p b).1 = p * b * p := rfl

/-- Complete positivity of `b ↦ pbp` into the corner is **34V**.1 `ad-cp`:
the order of `pAp` is inherited from `A`, so the defining sum is the one of
`ad_cp_1 p` evaluated at the underlying elements of the `bᵢ`. -/
private theorem cornerLin_cp : IsCompletelyPositiveMap (cornerLin p) := by
  intro n c b
  have hsum : ∀ F : Fin n → cornerSet A p, (∑ i, F i).1 = ∑ i, (F i).1 :=
    fun F => map_sum cornerSet.valAddHom F Finset.univ
  have hps : star p = p := (cornerSet.proj p).isSelfAdjoint.star_eq
  show (0 : A) ≤ (∑ i, ∑ j, star (b i) * cornerLin p (star (c i) * c j) * b j).1
  have hval : (∑ i, ∑ j, star (b i) * cornerLin p (star (c i) * c j) * b j).1
      = ∑ i, ∑ j, star ((b i).1) *
          ((LinearMap.mulLeft ℂ (star p)).comp (LinearMap.mulRight ℂ p))
            (star (c i) * c j) * (b j).1 := by
    simp only [hsum, cornerSet.val_mul, cornerSet.val_star, cornerLin_val,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, hps, mul_assoc]
  rw [hval]
  exact ad_cp_1 p n c fun i => (b i).1

/-- Normality of `b ↦ pbp` is **44VIII** `ad_normal`, read in the corner:
the supremum `ad_normal` produces already lies there, and the order of the
corner is the inherited one (`cornerSet_isLUB_of_isLUB`). -/
private theorem cornerLin_normal : PreservesDirSups ⇑(cornerLin p) := by
  intro D s hne hdir hlub
  have h3 : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D :=
    ⟨hne, hdir, ⟨s, hlub.1⟩⟩
  have hnat := ad_normal p D h3
  have hsd : s = dirSup D h3 := hlub.unique (isLUB_dirSup D h3)
  rw [← hsd, (cornerSet.proj p).isSelfAdjoint.star_eq] at hnat
  refine cornerSet_isLUB_of_isLUB ⟨?_, fun u hu => hnat.2 ?_⟩
  · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact hnat.1 ⟨d, hd, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact hu ⟨cornerLin p (d : A), ⟨d, hd, rfl⟩, rfl⟩

/-- The **standard corner** `h_p : A → pAp` as an ncp-map. -/
private noncomputable def cornerNcp (p : A) [Fact (IsStarProjection p)] :
    NCPMap A (cornerSet A p) where
  toCompletelyPositiveMap :=
    { toLinearMap := cornerLin p
      map_cstarMatrix_nonneg' := (cp_iff (cornerLin p)).out 0 1 |>.mp cornerLin_cp }
  preservesDirSups' := cornerLin_normal

private theorem cornerNcp_val (b : A) : (cornerNcp p b).1 = p * b * p := rfl

/-- The inclusion `pAp ⊆ A` as an ncp-map, for **any** projection `p`
(the `ζ` of proc.tex 95II): complete positivity because `Subtype.val` is a
non-unital ∗-homomorphism (**34IV**.3 `cp_of_mi`), normality by
`cornerSet.val_normal`. -/
private noncomputable def cornerInclNcp (p : A) [Fact (IsStarProjection p)] :
    NCPMap (cornerSet A p) A where
  toCompletelyPositiveMap :=
    { toLinearMap :=
        { toFun := fun c => c.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_cstarMatrix_nonneg' :=
        (cp_iff _).out 0 1 |>.mp
          (cp_of_mi _ (fun x y => cornerSet.val_mul x y)
            (fun x => cornerSet.val_star x)) }
  preservesDirSups' := cornerSet.val_normal

private theorem cornerInclNcp_apply (c : cornerSet A p) :
    (cornerInclNcp p c : A) = c.1 := rfl

end StandardCorner

/-- **169IV** (`standard-corner-dils`, dils.tex:6088, Example): the
**standard corner** `h_a : A → ⌊a⌋A⌊a⌋`, `b ↦ ⌊a⌋b⌊a⌋`, is a corner for
the effect `a` (see proc.tex 98I, 95II). -/
theorem standard_corner_dils [VonNeumannAlgebra A] (a : A)
    (ha : a ∈ effects A) :
    ∃ h : NCPMap A (cornerSet A (floor a)),
      (∀ b : A, (h b).1 = floor a * b * floor a) ∧ IsCornerFor h a := by
  set p : A := floor a with hp
  have hproj : IsStarProjection p := (cornerSet.proj p)
  have hps : star p = p := hproj.isSelfAdjoint.star_eq
  have hpp : p * p = p := hproj.isIdempotentElem.eq
  have hpeff : p ∈ effects A := ⟨hproj.nonneg, hproj.le_one⟩
  -- `⌊a⌋a⌊a⌋ = ⌊a⌋`, i.e. `h(a) = h(1)`
  have hconj : p * a * p = p := by
    refine le_antisymm ?_ ?_
    · have h := star_left_conjugate_le_conjugate ha.2 p
      rw [hps, mul_one, hpp] at h
      exact h
    · have h := star_left_conjugate_le_conjugate (floor_le ha) p
      rw [hps] at h
      calc p = p * p * p := by rw [hpp, hpp]
        _ ≤ p * a * p := h
  refine ⟨cornerNcp p, fun b => rfl, ha, Subtype.ext ?_, ?_⟩
  · rw [cornerNcp_val, cornerNcp_val, hconj, mul_one, hpp]
  intro C _ _ _ f hf
  -- `f(⌊a⌋^⊥) = f(⌈a^⊥⌉) = 0`
  have hfa : (f (1 - a) : C) = 0 := by
    have hL : (f (1 - a) : C) = f 1 - f a :=
      map_sub f.toCompletelyPositiveMap.toLinearMap 1 a
    rw [hL, hf, sub_self]
  have hcompl : (1 - a) ∈ effects A := effect_orthosupplement a ha
  have hceil : (f (ceil (1 - a)) : C) = 0 := ncp_eq_zero_ceil f hcompl hfa
  have hfp : (f (1 - p) : C) = 0 := by
    rw [hp, floor_eq_one_sub_ceil ha, sub_sub_cancel]
    exact hceil
  -- the mediating map is `f ∘ ζ`, and `f = f ∘ ζ ∘ h_p` by `cp-comprehension`
  obtain ⟨f', hf'⟩ := exists_ncpComp f (cornerInclNcp p)
  refine ⟨f', fun x => ?_, fun g hg => ?_⟩
  · rw [hf']
    exact ((cp_comprehension (ncpPositive f) p hpeff hfp x).2.2).symm
  · refine DFunLike.ext _ _ fun c => ?_
    have hc : cornerNcp p c.1 = c := Subtype.ext c.2
    rw [← hc, hg c.1, hf', cornerInclNcp_apply, cornerNcp_val]
    exact (cp_comprehension (ncpPositive f) p hpeff hfp c.1).2.2

/-! ### **169V**: `h` is a corner, for a unital map

`ϑ : ℬ → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ`, `b ↦ |e·b⟩⟨e|` (mirrored: `|b • e⟩⟨e|`), with
`e = 1 ⊗ 1`, and `q = ϑ(1) = |e⟩⟨e|`.  The two identities

* `h ∘ ϑ = id` (`pdil_h_theta`), and
* `ϑ ∘ h = q(·)q` (`pdil_theta_h`),

are all that is needed for `IsCornerFor`: the first gives uniqueness of the
mediating map and the second turns **63IV** `cp_comprehension` into its
existence, so **169IV** is not used.  The same two identities are also
exactly what makes the thesis's corestriction `ℬ ≅ q𝒫q` an
miu-**isomorphism** with inverse `q T q ↦ h(q T q)`, and that is how
`pdil_theta_normal` below gets normality, as the thesis does; the
corestriction is formed inside that proof rather than as a definition.

Everything is checked in the mirrored convention of `Paschke.lean`, where
`|x⟩⟨y| : z ↦ ⟨y,z⟩ • x` (`mketbra`) and the product of `𝒫 = 𝒷ᵃ(X)ᵐᵒᵖ` is
*reversed* composition, which is what makes `ϑ` multiplicative rather than
antimultiplicative: `ϑ(b)ϑ(c) = op(|c•e⟩⟨e| ∘ |b•e⟩⟨e|) = ϑ(bc)`, using
`⟨e,e⟩ = φ(1) = 1`.  Complete positivity of `ϑ` is then **34IV**.3
`cp_of_mi`; normality is **169VI**'s own "an miu-isomorphism, and thus also
normal" — see `pdil_theta_normal`. -/

section StandardPaschkeCorner

set_option linter.unusedSectionVars false

/-- An nmiu-map is an ncp-map (**34IV**.3 for `cp`; normality is carried). -/
private theorem pcorner_exists_ncpOfNmiu {P Q : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] (f : NMIUMap P Q) :
    ∃ g : NCPMap P Q, ∀ a, g a = f a :=
  ⟨{ toCompletelyPositiveMap :=
       { toLinearMap := (f.toStarAlgHom : P →ₐ[ℂ] Q).toLinearMap
         map_cstarMatrix_nonneg' :=
           (cp_iff _).out 0 1 |>.mp
             (cp_of_mi _ (fun x y => map_mul f.toStarAlgHom x y)
               (fun x => map_star f.toStarAlgHom x)) }
     preservesDirSups' := f.preservesDirSups' }, fun _ => rfl⟩

/-- The inverse of a **bijective** nmiu-map is an ncp-map.  Complete
positivity is **34IV**.3 `cp_of_mi` (a ∗-homomorphism is completely
positive), and normality follows from that of `f` together with
`starAlgHom_nonneg` (`Paschke.lean`), which makes `f` an order isomorphism.
(`nmiuInv` in `Theses/A/Proc/Tensor.lean` is the same construction; that
file *is* imported, but `nmiuInv` is `private` there.) -/
private theorem pcorner_exists_ncpInv {P Q : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] (f : NMIUMap P Q) (hbij : Function.Bijective ⇑f) :
    ∃ g : NCPMap Q P, (∀ x : P, g (f x) = x) ∧ ∀ y : Q, f (g y) = y := by
  classical
  set L : P →ₗ[ℂ] Q := (f.toStarAlgHom : P →ₐ[ℂ] Q).toLinearMap with hL
  have hLbij : Function.Bijective ⇑L := hbij
  set E : P ≃ₗ[ℂ] Q := LinearEquiv.ofBijective L hLbij with hE
  set g : Q →ₗ[ℂ] P := (E.symm : Q →ₗ[ℂ] P) with hg
  have hfg : ∀ y : Q, f (g y) = y := fun y => E.apply_symm_apply y
  have hgf : ∀ x : P, g (f x) = x := fun x => E.symm_apply_apply x
  have hmul : ∀ x y : Q, g (x * y) = g x * g y := by
    intro x y
    refine hbij.1 ?_
    have h1 : f (g x * g y) = f (g x) * f (g y) := map_mul f.toStarAlgHom _ _
    rw [hfg, h1, hfg, hfg]
  have hstar : ∀ y : Q, g (star y) = star (g y) := by
    intro y
    refine hbij.1 ?_
    have h1 : f (star (g y)) = star (f (g y)) := map_star f.toStarAlgHom _
    rw [hfg, h1, hfg]
  have hcp : IsCompletelyPositiveMap g := cp_of_mi g hmul hstar
  have hmono : ∀ x y : Q, x ≤ y → g x ≤ g y := by
    intro x y hxy
    have h := astara_pos_basic_2_cp g hcp (y - x) (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  have hfmono : ∀ x y : P, x ≤ y → f x ≤ f y := by
    intro x y hxy
    have h := starAlgHom_nonneg f.toStarAlgHom (sub_nonneg.mpr hxy)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := g
                map_cstarMatrix_nonneg' := (cp_iff g).out 0 1 |>.mp hcp }
            preservesDirSups' := ?_ }, hgf, hfg⟩
  intro D s hne hdir hlub
  have hcoe := isLUB_coe_of_isLUB hne hlub
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact hmono _ _ (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · have hub : f u ∈ upperBounds (Subtype.val '' D) := by
      rintro _ ⟨d, hd, rfl⟩
      have h1 : g ((d : selfAdjoint Q) : Q) ≤ u := hu ⟨d, hd, rfl⟩
      have h2 := hfmono _ _ h1
      rwa [hfg] at h2
    have h3 := hcoe.2 hub
    have h4 := hmono _ _ h3
    rwa [hgf] at h4

section Theta

variable {𝒜 ℬ : Type u}
  [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [VonNeumannAlgebra 𝒜] [VonNeumannAlgebra ℬ]
  {φ : NCPMap 𝒜 ℬ} (M : PaschkeModule φ)

/-- `⟨e,e⟩ = φ(1) = 1` for `e = 1 ⊗ 1`, when `φ` is unital. -/
private theorem pdil_inner_ee (hu : φ 1 = 1) :
    (inner ℬ (M.tprod 1 1) (M.tprod 1 1) : ℬ) = 1 := by
  rw [M.inner_tprod]
  simp [hu]

/-- `|x⟩⟨y|* = |y⟩⟨x|` in `𝒷ᵃ(X)` (**159III**, as an identity of algebra
elements rather than of `ModuleAdjointTo` data). -/
private theorem pdil_mketbraBa_star (x y : M.X) :
    star (mketbraBa (ℬ := ℬ) x y) = mketbraBa y x :=
  Subtype.ext (DFunLike.coe_injective
    (moduleAdjointTo_unique (𝒜 := ℬ) _ _ _
      (baSubalgebra_star_spec (𝒷 := ℬ) (X := M.X) (mketbraBa x y))
      (mketbra_adjointable ℬ x y)))

/-- The map `ϑ : ℬ → 𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ`, `b ↦ |e·b⟩⟨e|` (mirrored:
`|b • e⟩⟨e|`) of **169VI**. -/
private noncomputable def pdil_theta (b : ℬ) : (Ba ℬ M.X)ᵐᵒᵖ :=
  MulOpposite.op (mketbraBa (b • M.tprod 1 1) (M.tprod 1 1))

private theorem pdil_theta_unop_apply (b : ℬ) (z : M.X) :
    (pdil_theta M b).unop.1 z
      = (inner ℬ (M.tprod 1 1) z : ℬ) • (b • M.tprod 1 1) := rfl

private theorem pdil_theta_mul (hu : φ 1 = 1) (b c : ℬ) :
    pdil_theta M b * pdil_theta M c = pdil_theta M (b * c) := by
  refine congrArg MulOpposite.op (Subtype.ext (ContinuousLinearMap.ext fun z => ?_))
  show (inner ℬ (M.tprod 1 1) ((inner ℬ (M.tprod 1 1) z : ℬ) • (b • M.tprod 1 1)) : ℬ)
        • (c • M.tprod 1 1)
    = (inner ℬ (M.tprod 1 1) z : ℬ) • ((b * c) • M.tprod 1 1)
  rw [CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_right,
    pdil_inner_ee M hu, mul_one, op_mul_smul, op_mul_smul]

private theorem pdil_theta_star (b : ℬ) :
    star (pdil_theta M b) = pdil_theta M (star b) := by
  refine congrArg MulOpposite.op ?_
  show star (mketbraBa (ℬ := ℬ) (b • M.tprod 1 1) (M.tprod 1 1))
    = mketbraBa (star b • M.tprod 1 1) (M.tprod 1 1)
  rw [pdil_mketbraBa_star]
  refine Subtype.ext (ContinuousLinearMap.ext fun z => ?_)
  show (inner ℬ (b • M.tprod 1 1) z : ℬ) • M.tprod 1 1
    = (inner ℬ (M.tprod 1 1) z : ℬ) • (star b • M.tprod 1 1)
  rw [CStarModule.inner_op_smul_left, op_mul_smul]

private theorem pdil_theta_one :
    pdil_theta M (1 : ℬ)
      = MulOpposite.op (mketbraBa (M.tprod 1 1) (M.tprod 1 1)) := by
  rw [pdil_theta, op_one_smul]

/-- `h ∘ ϑ = id`: `h(|e·b⟩⟨e|) = ⟨e,e⟩ b ⟨e,e⟩ = b`. -/
private theorem pdil_h_theta (hu : φ 1 = 1) (b : ℬ) :
    M.h (pdil_theta M b) = b := by
  rw [M.h_def, pdil_theta_unop_apply, CStarModule.inner_op_smul_right,
    CStarModule.inner_op_smul_right, pdil_inner_ee M hu, mul_one, one_mul]

/-- `ϑ ∘ h = q(·)q` for `q = ϑ(1) = |e⟩⟨e|`. -/
private theorem pdil_theta_h (T : (Ba ℬ M.X)ᵐᵒᵖ) :
    pdil_theta M (M.h T) = pdil_theta M 1 * T * pdil_theta M 1 := by
  have hlin : ∀ (b : ℬ) (x : M.X), T.unop.1 (b • x) = b • T.unop.1 x := by
    intro b x
    exact (moduleAdjointable_linear (𝒜 := ℬ) ⇑T.unop.1 T.unop.2).2.2 b x
  rw [pdil_theta_one]
  refine MulOpposite.unop_injective ?_
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
  refine Subtype.ext (ContinuousLinearMap.ext fun z => ?_)
  show (inner ℬ (M.tprod 1 1) z : ℬ) • (M.h T • M.tprod 1 1)
    = (inner ℬ (M.tprod 1 1)
        (T.unop.1 ((inner ℬ (M.tprod 1 1) z : ℬ) • M.tprod 1 1)) : ℬ) • M.tprod 1 1
  rw [hlin, CStarModule.inner_op_smul_right, M.h_def, op_mul_smul]

/-- `ϑ` as a linear map. -/
private noncomputable def pdil_thetaLin : ℬ →ₗ[ℂ] (Ba ℬ M.X)ᵐᵒᵖ where
  toFun := pdil_theta M
  map_add' b c := by
    refine congrArg MulOpposite.op (Subtype.ext (ContinuousLinearMap.ext fun z => ?_))
    show (inner ℬ (M.tprod 1 1) z : ℬ) • ((b + c) • M.tprod 1 1)
      = (inner ℬ (M.tprod 1 1) z : ℬ) • (b • M.tprod 1 1)
        + (inner ℬ (M.tprod 1 1) z : ℬ) • (c • M.tprod 1 1)
    rw [op_add_smul, op_smul_add]
  map_smul' r b := by
    refine congrArg MulOpposite.op (Subtype.ext (ContinuousLinearMap.ext fun z => ?_))
    show (inner ℬ (M.tprod 1 1) z : ℬ) • ((r • b) • M.tprod 1 1)
      = r • ((inner ℬ (M.tprod 1 1) z : ℬ) • (b • M.tprod 1 1))
    rw [op_smul_complex_smul, op_smul_comm_complex]

private theorem pdil_thetaLin_apply (b : ℬ) :
    pdil_thetaLin M b = pdil_theta M b := rfl

private theorem pdil_theta_cp (hu : φ 1 = 1) :
    IsCompletelyPositiveMap (pdil_thetaLin M) :=
  cp_of_mi _ (fun x y => (pdil_theta_mul M hu x y).symm)
    (fun x => (pdil_theta_star M x).symm)

/-- Normality of `ϑ`, by **169VI**'s own argument.  The thesis corestricts
`ϑ` to the corner `q𝒫q` of `q = ϑ(1) = |e⟩⟨e|` and observes that the
corestriction is an miu-**isomorphism**, with inverse `qTq ↦ h(qTq)`: that
is exactly the pair of identities `h ∘ ϑ = id` (`pdil_h_theta`) and
`ϑ ∘ h = q(·)q` (`pdil_theta_h`), the second of which also supplies
`q ϑ(b) q = ϑ(b)`, i.e. that the corestriction is well defined.  Then "so
`ϑ` is an miu-isomorphism and thus also normal" — a ∗-isomorphism is an
order isomorphism, `Theses.A.VN.starAlgEquiv_preservesDirSups`.  Finally
`ϑ` itself is that corestriction followed by the inclusion `q𝒫q ⊆ 𝒫`,
which is normal because the corner's suprema *are* those of `𝒫` (**94II**.6
`cornerSet.val_normal`).  `𝒫 = 𝒷ᵃ(X)ᵐᵒᵖ` is a von Neumann algebra by
**152X** `ba_vonNeumannAlgebra` and `vonNeumannAlgebra_mulOpposite`. -/
private theorem pdil_theta_normal (hu : φ 1 = 1) :
    PreservesDirSups (pdil_theta M) := by
  have : VonNeumannAlgebra (Ba ℬ M.X) := ba_vonNeumannAlgebra M.selfDual
  have : Fact (IsStarProjection (pdil_theta M 1)) :=
    ⟨⟨by rw [IsIdempotentElem, pdil_theta_mul M hu, mul_one],
      by rw [IsSelfAdjoint, pdil_theta_star M 1, star_one]⟩⟩
  -- `ϑ(b) = ϑ(h(ϑ(b))) = q ϑ(b) q`: the corestriction to `q𝒫q` is defined
  have hmem : ∀ b : ℬ,
      pdil_theta M 1 * pdil_theta M b * pdil_theta M 1 = pdil_theta M b := by
    intro b
    have h := pdil_theta_h M (pdil_theta M b)
    rw [pdil_h_theta M hu b] at h
    exact h.symm
  -- the corestriction, an miu-isomorphism `ℬ ≅ q𝒫q` with inverse `h`
  set Φ : ℬ ≃⋆ₐ[ℂ] cornerSet (Ba ℬ M.X)ᵐᵒᵖ (pdil_theta M 1) :=
    { toFun := fun b => ⟨pdil_theta M b, hmem b⟩
      invFun := fun s => M.h s.1
      left_inv := fun b => pdil_h_theta M hu b
      right_inv := fun s => Subtype.ext ((pdil_theta_h M s.1).trans s.2)
      map_mul' := fun b c => Subtype.ext (pdil_theta_mul M hu b c).symm
      map_add' := fun b c => Subtype.ext (map_add (pdil_thetaLin M) b c)
      map_smul' := fun r b => Subtype.ext (map_smul (pdil_thetaLin M) r b)
      map_star' := fun b => Subtype.ext (pdil_theta_star M b).symm } with hΦ
  -- the inclusion `q𝒫q ⊆ 𝒫` as a positive linear map
  set ι : cornerSet (Ba ℬ M.X)ᵐᵒᵖ (pdil_theta M 1) →ₚ[ℂ] (Ba ℬ M.X)ᵐᵒᵖ :=
    { toFun := fun s => s.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      monotone' := fun _ _ h => h } with hι
  exact preservesDirSups_pmap_comp (starAlgHomP Φ.toStarAlgHom)
    (starAlgEquiv_preservesDirSups Φ) ι cornerSet.val_normal

/-- `ϑ` as an ncp-map. -/
private noncomputable def pdil_thetaNcp (hu : φ 1 = 1) :
    NCPMap ℬ (Ba ℬ M.X)ᵐᵒᵖ where
  toCompletelyPositiveMap :=
    { toLinearMap := pdil_thetaLin M
      map_cstarMatrix_nonneg' :=
        (cp_iff (pdil_thetaLin M)).out 0 1 |>.mp (pdil_theta_cp M hu) }
  preservesDirSups' := pdil_theta_normal M hu

private theorem pdil_thetaNcp_apply (hu : φ 1 = 1) (b : ℬ) :
    pdil_thetaNcp M hu b = pdil_theta M b := rfl

/-- `q = ϑ(1) = |e⟩⟨e|` is a projection, because `⟨e,e⟩ = 1`. -/
private theorem pdil_theta_one_isStarProjection (hu : φ 1 = 1) :
    IsStarProjection (pdil_theta M 1) :=
  ⟨by rw [IsIdempotentElem, pdil_theta_mul M hu, mul_one],
    by rw [IsSelfAdjoint, pdil_theta_star M 1, star_one]⟩

private theorem pdil_h_one (hu : φ 1 = 1) : M.h (1 : (Ba ℬ M.X)ᵐᵒᵖ) = 1 := by
  rw [M.h_def]
  show (inner ℬ (M.tprod 1 1) (M.tprod 1 1) : ℬ) = 1
  exact pdil_inner_ee M hu

/-- **169VI** for the *standard* dilation of **154III**: `h` is a corner for
`q = |e⟩⟨e|`.  Existence of the mediating map is **63IV** `cp_comprehension`
(`f(q^⊥) = 0` since `f(q) = f(1)`) read through `ϑ ∘ h = q(·)q`; uniqueness
is `h ∘ ϑ = id`. -/
private theorem pdil_isCornerFor (hu : φ 1 = 1) :
    IsCornerFor M.h (pdil_theta M 1) := by
  have hproj := pdil_theta_one_isStarProjection M hu
  have hq : pdil_theta M 1 ∈ effects ((Ba ℬ M.X)ᵐᵒᵖ) := ⟨hproj.nonneg, hproj.le_one⟩
  refine ⟨hq, by rw [pdil_h_theta M hu 1, pdil_h_one M hu], ?_⟩
  intro C _ _ _ f hf
  have hfq : (f (1 - pdil_theta M 1) : C) = 0 := by
    have hL : (f (1 - pdil_theta M 1) : C) = f 1 - f (pdil_theta M 1) :=
      map_sub f.toCompletelyPositiveMap.toLinearMap 1 (pdil_theta M 1)
    rw [hL, hf, sub_self]
  obtain ⟨f', hf'⟩ := exists_ncpComp f (pdil_thetaNcp M hu)
  refine ⟨f', fun T => ?_, fun g hg => ?_⟩
  · rw [hf', pdil_thetaNcp_apply, pdil_theta_h M T]
    exact ((cp_comprehension (ncpPositive f) (pdil_theta M 1) hq hfq T).2.2).symm
  · refine DFunLike.ext _ _ fun b => ?_
    rw [hf', pdil_thetaNcp_apply, ← hg (pdil_theta M b), pdil_h_theta M hu b]

end Theta

end StandardPaschkeCorner

/-- **169V** (`h-is-corner-for-unital-map`, dils.tex:6096, Lemma): if
`(𝒫, ϱ, h)` is a Paschke dilation of a *unital* ncp-map, then `h` is a
corner.

⚠️ **The two `[VonNeumannAlgebra]` binders are new** (session 70).  They are
the chapter's standing hypothesis — dils.tex **140II** opens "let
`φ : 𝒜 → ℬ` be any ncp-map **between von Neumann algebras**", and every
sibling statement about a `PaschkeTriple` carries them (**171VII**
`paschke_pure`, **172X** `pure_ncp_extreme`) — but they were dropped in the
first transcription of this point, which therefore claimed the lemma for
arbitrary C\*-algebras `A`, `B`.  That is strictly stronger and out of
reach: the proof below (and the thesis's) reduces to the *standard* dilation
of **154III**, whose construction `existence_paschke` needs both algebras to
be von Neumann.  This is the same repair the author ruled on for **170IV**
(QUESTIONS **D5**, "restore the hypothesis"); see PROVING-LOG session 70.

**169VI** is the proof, transcribed: it is enough to prove it for the
standard dilation `(𝒷ᵃ(𝒜 ⊗_φ ℬ)ᵐᵒᵖ, ϱ, h)` of **154III**, because
`exists_paschke_iso_paschkeModule` (**140VIII**) makes any other dilation
nmiu-isomorphic to it over `h`; there `h` is a corner for `q = |e⟩⟨e|`
(`pdil_isCornerFor`).  The corner property is carried back along the
isomorphism `ϑ` by hand — the corner is `ϑ⁻¹(q)`, and the mediating maps are
composed with `ϑ⁻¹` (`pcorner_exists_ncpInv`). -/
theorem h_is_corner_for_unital_map [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (hu : φ 1 = 1)
    (D : PaschkeTriple A B) (hD : IsPaschkeDilationOf D ⇑φ) :
    IsCorner D.h := by
  obtain ⟨M⟩ := existence_paschke φ
  obtain ⟨ϑ, ⟨hbij, -, hh⟩, -⟩ := exists_paschke_iso_paschkeModule φ M D hD
  obtain ⟨ϑinv, hgf, hfg⟩ := pcorner_exists_ncpInv ϑ hbij
  have hcorner := pdil_isCornerFor M hu
  have hϑ1 : (ϑ (1 : D.P) : (Ba B M.X)ᵐᵒᵖ) = 1 := map_one ϑ.toStarAlgHom
  have hinv1 : ϑinv (1 : (Ba B M.X)ᵐᵒᵖ) = 1 := by rw [← hϑ1, hgf]
  have hinvmono : ∀ x y : (Ba B M.X)ᵐᵒᵖ, x ≤ y → ϑinv x ≤ ϑinv y :=
    fun x y hxy => (ncpPos ϑinv).monotone hxy
  refine ⟨ϑinv (pdil_theta M 1), ⟨?_, ?_⟩, ?_, ?_⟩
  · have h0 : (0 : D.P) = ϑinv 0 := (map_zero ϑinv.toCompletelyPositiveMap).symm
    rw [h0]
    exact hinvmono _ _ hcorner.1.1
  · rw [← hinv1]
    exact hinvmono _ _ hcorner.1.2
  · rw [← hh (ϑinv (pdil_theta M 1)), ← hh 1, hfg, hϑ1, hcorner.2.1]
  · intro C _ _ _ f hf
    obtain ⟨f₀, hf₀⟩ := exists_ncpComp f ϑinv
    have hf₀q : f₀ (pdil_theta M 1) = f₀ 1 := by
      rw [hf₀, hf₀, hinv1, hf]
    obtain ⟨f', hf'1, hf'2⟩ := hcorner.2.2 C ‹_› ‹_› ‹_› f₀ hf₀q
    refine ⟨f', fun c => ?_, fun g hg => ?_⟩
    · rw [← hh c, hf'1 (ϑ c), hf₀, hgf]
    · refine hf'2 g fun T => ?_
      rw [hf₀, ← hg (ϑinv T), ← hh (ϑinv T), hfg]

/-- **169VIII** (`dils-def-filter`, dils.tex:6124, Definition): an ncp-map
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

/-- **169VIII** (`dils-def-filter`, dils.tex:6124, Definition): a
**filter** is an ncp-map which is a filter for some positive element. -/
def IsFilter (c : NCPMap A B) : Prop :=
  ∃ b : B, IsFilterFor c b

/-- **The identity is a filter for `1`.**  Unfolding `IsFilterFor` leaves
`0 ≤ 1`, `1 ≤ 1`, and: every ncp-map `f : C → B` with `f(1) ≤ 1` factors
uniquely through the identity by a *subunital* map — namely `f` itself,
whose subunitality *is* the hypothesis `f(1) ≤ 1`, and which is unique
because the factorisation equation pins the underlying function.

This is the ingredient **170IV**.1's "hence pure" needs: it exhibits the
identity as a filter, and hence (`isPureMap_of_isCorner` at parsec 1700)
makes every corner a pure map.  It is also why the author's `IsFilterFor`
repair (the mediating map is subunital) costs nothing here: the quantified
`f` is already subunital, since `b = 1`. -/
theorem isFilterFor_ncpId : IsFilterFor (ncpId B) (1 : B) := by
  refine ⟨zero_le_one, le_rfl, ?_⟩
  intro C _ _ _ f hf1
  refine ⟨⟨f, hf1⟩, fun x => rfl, ?_⟩
  rintro ⟨g, hg⟩ hgx
  have hgf : g = f := DFunLike.ext _ _ fun x => hgx x
  subst hgf
  rfl

/-- **The identity is a filter** (for `1`). -/
theorem isFilter_ncpId : IsFilter (ncpId B) := ⟨1, isFilterFor_ncpId⟩

/-! ### **169X**: the standard filter `c_b : ⌈b⌉B⌈b⌉ → B` -/

section StandardFilter

set_option linter.unusedSectionVars false

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- proc.tex **96III**.1 (`ncp-uwlim`): a pointwise ultraweak limit of
completely positive maps is completely positive.  Re-derived here because
the domain needs no von Neumann structure, which
`Theses.A.Proc.ncp_uwlim_1` (reachable — see the file header) asks for and
never uses. -/
private theorem sfilter_cp_uwlim [VonNeumannAlgebra B] {ι : Type*}
    (l : Filter ι) [l.NeBot] (f : ι → (D →ₗ[ℂ] B)) (g : D →ₗ[ℂ] B)
    (hlim : ∀ a : D, UWTendsto (fun i => f i a) l (g a))
    (hcp : ∀ i, IsCompletelyPositiveMap (f i)) :
    IsCompletelyPositiveMap g := by
  intro n a bb
  have hclosed : @IsClosed B (ultraweak B) {x : B | 0 ≤ x} := vn_positive_basic_2.1
  have hlim2 : UWTendsto
      (fun i => ∑ p, ∑ q, star (bb p) * (f i) (star (a p) * a q) * bb q) l
      (∑ p, ∑ q, star (bb p) * g (star (a p) * a q) * bb q) := by
    rw [uwTendsto_iff]
    intro ω
    have hterm : ∀ p q : Fin n,
        Tendsto (fun i => (ω (star (bb p) * (f i) (star (a p) * a q) * bb q) : ℂ)) l
          (𝓝 (ω (star (bb p) * g (star (a p) * a q) * bb q))) := by
      intro p q
      have hc := @Continuous.tendsto B ℂ (ultraweak B) _
        (fun x : B => (ω (star (bb p) * x * bb q) : ℂ))
        (continuous_ultraweak_conj ω (star (bb p)) (bb q)) (g (star (a p) * a q))
      exact hc.comp (hlim (star (a p) * a q))
    have hsum := tendsto_finsetSum Finset.univ
      (fun p _ => tendsto_finsetSum Finset.univ (fun q _ => hterm p q))
    have hms : ∀ F : Fin n → B, (ω (∑ p, F p) : ℂ) = ∑ p, ω (F p) :=
      fun F => map_sum ω.toPositiveLinearMap F Finset.univ
    simp only [hms]
    exact hsum
  refine @IsClosed.mem_of_tendsto B (ultraweak B) ι _ _ _ l _ hclosed hlim2 ?_
  filter_upwards with i using hcp i n a bb

/-- `x ↦ d* x d : B → B` as a linear map. -/
private noncomputable def sfilterAdLin (d : B) : B →ₗ[ℂ] B where
  toFun := fun x => star d * x * d
  map_add' := fun x y => by noncomm_ring
  map_smul' := fun z x => by
    simp only [RingHom.id_apply]
    rw [mul_smul_comm, smul_mul_assoc]

@[simp] private theorem sfilterAdLin_apply (d x : B) :
    sfilterAdLin d x = star d * x * d := rfl

private theorem sfilterAdLin_cp (d : B) : IsCompletelyPositiveMap (sfilterAdLin d) := by
  have heq : sfilterAdLin d
      = (LinearMap.mulLeft ℂ (star d)).comp (LinearMap.mulRight ℂ d) := by
    ext x
    simp [mul_assoc]
  rw [heq]
  exact ad_cp_1 d

/-- The ncp-map `x ↦ d* x d : B → B` (**34V** `ad-cp`, **44VIII**
`ad-normal`). -/
private theorem exists_sfilterAd [VonNeumannAlgebra B] (d : B) :
    ∃ c : NCPMap B B, ∀ x : B, c x = star d * x * d := by
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := sfilterAdLin d
                map_cstarMatrix_nonneg' :=
                  (cp_iff (sfilterAdLin d)).out 0 1 |>.mp (sfilterAdLin_cp d) }
            preservesDirSups' := ?_ }, fun _ => rfl⟩
  intro Ds s hne hdir hlub
  have hbdd : BddAbove Ds := ⟨s, hlub.1⟩
  have h3 : Ds.Nonempty ∧ DirectedOn (· ≤ ·) Ds ∧ BddAbove Ds := ⟨hne, hdir, hbdd⟩
  have hs : s = dirSup Ds h3 := hlub.unique (isLUB_dirSup Ds h3)
  have hnat := ad_normal d Ds h3
  rw [← hs] at hnat
  exact hnat


/-- Auxiliary for **169X** (proc.tex 96V): `t` is an approximate
pseudoinverse of `a` iff `t*` is one of `a*`.  Each of the six clauses is
the star-image of another; the partial-sum sets coincide on the nose,
because `tₙa` and `atₙ` are projections, hence self adjoint. -/
private theorem sfilter_approxPseudo_star [VonNeumannAlgebra B] {a : B}
    {t : ℕ → B} (h : IsApproxPseudoinverse B a t) :
    IsApproxPseudoinverse B (star a) (fun n => star (t n)) := by
  have hL : ∀ n, star (t n) * star a = a * t n := by
    intro n; rw [← star_mul, (h.proj_right n).isSelfAdjoint.star_eq]
  have hR : ∀ n, star a * star (t n) = t n * a := by
    intro n; rw [← star_mul, (h.proj_left n).isSelfAdjoint.star_eq]
  refine { proj_left := ?_, proj_right := ?_, sum_left := ?_, sum_range := ?_,
           sum_right := ?_, sum_supp := ?_ }
  · intro n; rw [hL n]; exact h.proj_right n
  · intro n; rw [hR n]; exact h.proj_left n
  · have he : {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, star (t n) * star a}
        = {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, a * t n} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [hL]⟩
    rw [he, suppProj_star]
    exact h.sum_right
  · have he : {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (star (t n))}
        = {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (t n)} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [rangeProj_star]⟩
    rw [he, suppProj_star]
    exact h.sum_supp
  · have he : {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, star a * star (t n)}
        = {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, t n * a} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [hR]⟩
    rw [he, rangeProj_star]
    exact h.sum_left
  · have he : {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, suppProj (star (t n))}
        = {x : B | ∃ N : ℕ, x = ∑ n ∈ Finset.range N, rangeProj (t n)} := by
      ext x
      constructor <;> rintro ⟨N, rfl⟩ <;> exact ⟨N, by simp only [suppProj_star]⟩
    rw [he, rangeProj_star]
    exact h.sum_range

/-- Auxiliary for **169X** (proc.tex 96V, from **81II**): for `x` in the
corner `⌊d⌉B⌊d⌉` one has `d*∖(d*xd)/d = x`. -/
private theorem sfilter_ldiv_div [VonNeumannAlgebra B] (d x : B)
    (hx : rangeProj d * x * rangeProj d = x) :
    ldiv (star d) (div (star d * x * d) d) = x := by
  have hqq : rangeProj d * rangeProj d = rangeProj d :=
    ((ceill_basic_2 d).1.1).isIdempotentElem.eq
  have hxq : x * rangeProj d = x := by
    calc x * rangeProj d
        = (rangeProj d * x * rangeProj d) * rangeProj d := by rw [hx]
      _ = rangeProj d * x * (rangeProj d * rangeProj d) := by noncomm_ring
      _ = rangeProj d * x * rangeProj d := by rw [hqq]
      _ = x := hx
  have hqx : rangeProj d * x = x := by
    calc rangeProj d * x
        = rangeProj d * (rangeProj d * x * rangeProj d) := by rw [hx]
      _ = (rangeProj d * rangeProj d) * x * rangeProj d := by noncomm_ring
      _ = rangeProj d * x * rangeProj d := by rw [hqq]
      _ = x := hx
  have h1 : div (star d * x * d) d = star d * x :=
    div_eq rfl (by rw [mul_assoc, hxq])
  rw [h1]
  exact ldiv_eq rfl (by rw [suppProj_star, hqx])

/-- Bipositivity of `x ↦ d* x d` on the corner `⌊d⌉B⌊d⌉` (**81VI**.2). -/
private theorem sfilter_bipos [VonNeumannAlgebra B] (d x : B)
    (hx : rangeProj d * x * rangeProj d = x) (h : 0 ≤ star d * x * d) : 0 ≤ x := by
  have h2 := sequential_douglas_2 (star d * x * d) d h ⟨x, rfl⟩
  rwa [sfilter_ldiv_div d x hx] at h2

/-- `⌈b⌉ = ⌊√b⌉` for `b ≥ 0`. -/
private theorem sfilter_ceil_eq [VonNeumannAlgebra B] (b : B) (hb : 0 ≤ b) :
    ceil b = rangeProj (CFC.sqrt b) := by
  have hsa : IsSelfAdjoint (CFC.sqrt b) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)
  rw [rangeProj, hsa.star_eq, CFC.sqrt_mul_sqrt_self b hb]

/-- The heart of **169X** (proc.tex 96V): an ncp-map `f : D → B` with
`f(1) ≤ d*d` factors as `f = d* g(·) d` through an ncp-map
`g : D → ⌊d⌉B⌊d⌉`, namely `g(x) = d*∖f(x)/d`.

The author's argument (proc.tex:426), with the same divergence as
`Theses.A.Proc.canonicalFilter_factor`: *existence* of the value is
`sequential-douglas` (**81VI**.1) applied to `0 ≤ f(x) ≤ ‖x‖f(1) ≤ ‖x‖d*d`,
extended off the positive cone by linearity; *positivity* is **81VI**.2;
*complete positivity* is `ncp-uwlim` (**96III**.1) applied to the completely
positive approximants `(∑_{n<N}tₙ)* f(·) (∑_{n<N}tₙ)`, which converge
pointwise to `g` by `div-approx` (**81VII**); *normality* is taken from
normality of `f` together with the bipositivity of `d*(·)d` on the corner,
rather than from `div-usc` (**81IX**).

*(Corrected session 95.  This used to read "**81IX**, whose relevant half is
false — see `Theses.A.VN.div_usc`", and both halves have expired.  There is
no `Theses.A.VN.div_usc`: what is false is the *printed*, ultra**strong**
form, recorded in the section note above `div_uwc` in `A/VN/Division`.  On
the author's ruling of **2026-08-17** both 81IX and its vn.tex proof run
*ultraweakly*, which is sound and proved as `Theses.A.VN.div_uwc`; the
sibling `Theses.A.Proc.canonicalFilter_factor` was updated to say so.  The
thesis's route is therefore **valid again**, and this proof is one of two —
kept, not forced.)* -/
private theorem sfilter_factor [VonNeumannAlgebra B] (d : B) (q : B)
    [Fact (IsStarProjection q)] (hqr : q = rangeProj d)
    (f : NCPMap D B) (hf1 : (f 1 : B) ≤ star d * d) :
    ∃ g : NCPMap D (cornerSet B q),
      ∀ x : D, star d * (g x).1 * d = (f x : B) := by
  classical
  subst hqr
  set q : B := rangeProj d with hqdef
  have hq : IsStarProjection q := (ceill_basic_2 d).1.1
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hqd : q * d = d := (ceill_basic_2 d).1.2
  have hdq : star d * q = star d := by
    have h := congrArg star hqd
    rwa [star_mul, hq.isSelfAdjoint.star_eq] at h
  -- linearity helpers for `f`
  have hfadd : ∀ x y : D, (f (x + y) : B) = f x + f y :=
    fun x y => map_add f.toCompletelyPositiveMap x y
  have hfsmul : ∀ (z : ℂ) (x : D), (f (z • x) : B) = z • f x :=
    fun z x => map_smul f.toCompletelyPositiveMap z x
  have hfsub : ∀ x y : D, (f (x - y) : B) = f x - f y :=
    fun x y => map_sub f.toCompletelyPositiveMap x y
  have hfmono : ∀ {x y : D}, x ≤ y → (f x : B) ≤ f y :=
    fun h => (ncpPos f).monotone h
  have hf0 : (f (0 : D) : B) = 0 := map_zero f.toCompletelyPositiveMap
  have hfnn : ∀ {x : D}, 0 ≤ x → (0 : B) ≤ f x := by
    intro x hx
    have h : (f (0 : D) : B) ≤ f x := hfmono hx
    rwa [hf0] at h
  -- (1) the inversion formula, (2) bipositivity and injectivity
  have hinv : ∀ x : B, q * x * q = x → ldiv (star d) (div (star d * x * d) d) = x :=
    fun x hx => sfilter_ldiv_div d x hx
  have hbipos : ∀ x : B, q * x * q = x → 0 ≤ star d * x * d → 0 ≤ x := by
    intro x hx hpos
    have h := sequential_douglas_2 (star d * x * d) d hpos ⟨x, rfl⟩
    rwa [hinv x hx] at h
  have hinj : ∀ x y : B, q * x * q = x → q * y * q = y →
      star d * x * d = star d * y * d → x = y := by
    intro x y hx hy h
    rw [← hinv x hx, ← hinv y hy, h]
  -- (3) every value of `f` lies in `d*Bd`
  have hsmulmono : ∀ (r : ℝ), 0 ≤ r → ∀ x z : B, x ≤ z →
      ((r : ℂ)) • x ≤ ((r : ℂ)) • z := by
    intro r hr x z h
    have h2 := ofReal_smul_nonneg (sub_nonneg.mpr h) hr
    rwa [smul_sub, sub_nonneg] at h2
  have hposmem : ∀ y : D, 0 ≤ y →
      ∃ e : B, ‖e‖ ≤ ‖y‖ ∧ (f y : B) = star d * e * d := by
    intro y hy
    have hyle : y ≤ algebraMap ℂ D ((‖y‖ : ℝ) : ℂ) := by
      rw [← algebraMap_real_eq]
      exact (IsSelfAdjoint.of_nonneg hy).le_algebraMap_norm_self
    have h1 : (f y : B) ≤ ((‖y‖ : ℝ) : ℂ) • (f 1 : B) := by
      have h := hfmono hyle
      rwa [Algebra.algebraMap_eq_smul_one, hfsmul] at h
    have h2 : (f y : B) ≤ ((‖y‖ : ℝ) : ℂ) • (star d * d) :=
      h1.trans (hsmulmono ‖y‖ (norm_nonneg y) _ _ hf1)
    exact (sequential_douglas_1 (f y) d (hfnn hy) ‖y‖ (norm_nonneg y)).1.2 h2
  have hmem : ∀ x : D, ∃ e : B, (f x : B) = star d * e * d := by
    intro x
    obtain ⟨e1, -, h1⟩ := hposmem _ (CFC.posPart_nonneg ((realPart x : D)))
    obtain ⟨e2, -, h2⟩ := hposmem _ (CFC.negPart_nonneg ((realPart x : D)))
    obtain ⟨e3, -, h3⟩ := hposmem _ (CFC.posPart_nonneg ((imaginaryPart x : D)))
    obtain ⟨e4, -, h4⟩ := hposmem _ (CFC.negPart_nonneg ((imaginaryPart x : D)))
    refine ⟨e1 - e2 + Complex.I • (e3 - e4), ?_⟩
    have hb : (realPart x : D) + Complex.I • (imaginaryPart x : D) = x :=
      realPart_add_I_smul_imaginaryPart x
    have hr : posPart ((realPart x : D)) - negPart ((realPart x : D))
        = (realPart x : D) := CFC.posPart_sub_negPart _ (realPart x).2
    have hi : posPart ((imaginaryPart x : D)) - negPart ((imaginaryPart x : D))
        = (imaginaryPart x : D) := CFC.posPart_sub_negPart _ (imaginaryPart x).2
    rw [← hb, ← hr, ← hi, hfadd, hfsmul, hfsub, hfsub, h1, h2, h3, h4]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  -- (4) the factorisation, elementwise
  set F : D → B := fun x => ldiv (star d) (div ((f x : B)) d) with hFdef
  have hFapp : ∀ x : D, F x = ldiv (star d) (div ((f x : B)) d) := fun x => by rw [hFdef]
  have hF : ∀ x : D, q * F x * q = F x ∧ star d * F x * d = (f x : B) := by
    intro x
    obtain ⟨e, he⟩ := hmem x
    have hcorner : q * (q * e * q) * q = q * e * q := by
      calc q * (q * e * q) * q = (q * q) * e * (q * q) := by noncomm_ring
        _ = q * e * q := by rw [hqq]
    have hfe : (f x : B) = star d * (q * e * q) * d := by
      rw [he]
      calc star d * e * d = (star d * q) * e * (q * d) := by rw [hdq, hqd]
        _ = star d * (q * e * q) * d := by noncomm_ring
    have hFb : F x = q * e * q := by
      rw [hFapp x, hfe]
      exact hinv _ hcorner
    exact ⟨by rw [hFb]; exact hcorner, by rw [hFb, ← hfe]⟩
  -- (5) linearity and positivity of `F`
  have hFadd : ∀ x y : D, F (x + y) = F x + F y := by
    intro x y
    refine hinj _ _ (hF (x + y)).1 ?_ ?_
    · rw [mul_add, add_mul, (hF x).1, (hF y).1]
    · rw [(hF (x + y)).2, hfadd, mul_add, add_mul, (hF x).2, (hF y).2]
  have hFsmul : ∀ (z : ℂ) (x : D), F (z • x) = z • F x := by
    intro z x
    refine hinj _ _ (hF (z • x)).1 ?_ ?_
    · rw [mul_smul_comm, smul_mul_assoc, (hF x).1]
    · rw [(hF (z • x)).2, hfsmul, mul_smul_comm, smul_mul_assoc, (hF x).2]
  set Flin : D →ₗ[ℂ] B :=
    { toFun := F, map_add' := hFadd, map_smul' := hFsmul } with hFlin
  have hFlinapp : ∀ x : D, Flin x = F x := fun _ => rfl
  have hFpos : ∀ y : D, 0 ≤ y → 0 ≤ F y := by
    intro y hy
    obtain ⟨e, he⟩ := hmem y
    rw [hFapp y]
    exact sequential_douglas_2 ((f y : B)) d (hfnn hy) ⟨e, he⟩
  have hFmono : ∀ {x y : D}, x ≤ y → F x ≤ F y := by
    intro x y h
    have h0 := hFpos (y - x) (sub_nonneg.mpr h)
    rw [show F (y - x) = F y - F x from map_sub Flin y x, sub_nonneg] at h0
    exact h0
  -- (6) complete positivity: `div-approx` + `ncp-uwlim`
  have hFcp : IsCompletelyPositiveMap Flin := by
    obtain ⟨t, ht⟩ := approximate_pseudoinverse d
    have hst : IsApproxPseudoinverse B (star d) (fun n => star (t n)) :=
      sfilter_approxPseudo_star ht
    set T : ℕ → B := fun N => ∑ n ∈ Finset.range N, t n with hTdef
    have hTstar : ∀ N : ℕ, (∑ n ∈ Finset.range N, star (t n)) = star (T N) := by
      intro N; rw [hTdef, star_sum]
    obtain ⟨adT, hadT⟩ : ∃ c : ℕ → NCPMap B B, ∀ (N : ℕ) (x : B),
        c N x = star (T N) * x * T N := by
      choose c hc using fun N => exists_sfilterAd (T N)
      exact ⟨c, hc⟩
    obtain ⟨hN, hNapp⟩ : ∃ c : ℕ → NCPMap D B, ∀ (N : ℕ) (x : D),
        c N x = star (T N) * (f x : B) * T N := by
      choose c hc using fun N => exists_ncpComp (adT N) f
      exact ⟨c, fun N x => by rw [hc N x, hadT]⟩
    -- pointwise ultrastrong convergence, first for `0 ≤ y` with `‖y‖ ≤ 1`
    have hbase : ∀ y : D, 0 ≤ y → ‖y‖ ≤ 1 →
        USTendsto (fun N => star (T N) * (f y : B) * T N) atTop (F y) := by
      intro y hy hy1
      obtain ⟨e, hen, he⟩ := hposmem y hy
      have hconv := div_approx ((f y : B)) d (star d) t (fun n => star (t n)) ht
        hst ⟨e, hen.trans hy1, he⟩
      rw [hFapp y]
      simpa only [hTstar] using hconv
    have hadd : ∀ x y : D,
        USTendsto (fun N => star (T N) * (f x : B) * T N) atTop (F x) →
        USTendsto (fun N => star (T N) * (f y : B) * T N) atTop (F y) →
        USTendsto (fun N => star (T N) * (f (x + y) : B) * T N) atTop (F (x + y)) := by
      intro x y hx hy
      have h := usTendsto_add hx hy
      rw [hFadd]
      refine h.congr fun N => ?_
      rw [hfadd, mul_add, add_mul]
    have hsmulc : ∀ (z : ℂ) (x : D),
        USTendsto (fun N => star (T N) * (f x : B) * T N) atTop (F x) →
        USTendsto (fun N => star (T N) * (f (z • x) : B) * T N) atTop (F (z • x)) := by
      intro z x hx
      have h := usTendsto_smul z hx
      rw [hFsmul]
      refine h.congr fun N => ?_
      rw [hfsmul, mul_smul_comm, smul_mul_assoc]
    have hpos : ∀ y : D, 0 ≤ y →
        USTendsto (fun N => star (T N) * (f y : B) * T N) atTop (F y) := by
      intro y hy
      rcases eq_or_lt_of_le (norm_nonneg y) with hn | hn
      · have hy0 : y = 0 := norm_eq_zero.mp hn.symm
        subst hy0
        have hF0 : F (0 : D) = 0 := by
          refine hinj _ _ (hF 0).1 (by simp) ?_
          rw [(hF 0).2, hf0]; simp
        rw [hF0]
        simp only [hf0, mul_zero, zero_mul]
        exact usTendsto_const 0
      · have hu0 : (0 : D) ≤ ((‖y‖⁻¹ : ℝ) : ℂ) • y :=
          ofReal_smul_nonneg hy (by positivity)
        have hu1 : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ ≤ 1 := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hn)]
          rw [inv_mul_cancel₀ (ne_of_gt hn)]
        have hy' : ((‖y‖ : ℝ) : ℂ) • (((‖y‖⁻¹ : ℝ) : ℂ) • y) = y := by
          rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hn)]
          simp
        have h := hsmulc ((‖y‖ : ℝ) : ℂ) _ (hbase _ hu0 hu1)
        rwa [hy'] at h
    have hsa : ∀ y : D, IsSelfAdjoint y →
        USTendsto (fun N => star (T N) * (f y : B) * T N) atTop (F y) := by
      intro y hy
      have hd0 : posPart y + (-1 : ℂ) • negPart y = y := by
        rw [neg_one_smul, ← sub_eq_add_neg]
        exact CFC.posPart_sub_negPart y hy
      have h := hadd _ _ (hpos _ (CFC.posPart_nonneg y))
        (hsmulc (-1 : ℂ) _ (hpos _ (CFC.negPart_nonneg y)))
      rwa [hd0] at h
    have hall : ∀ x : D,
        USTendsto (fun N => star (T N) * (f x : B) * T N) atTop (F x) := by
      intro x
      have hb : (realPart x : D) + Complex.I • (imaginaryPart x : D) = x :=
        realPart_add_I_smul_imaginaryPart x
      have h := hadd _ _ (hsa _ (realPart x).2)
        (hsmulc Complex.I _ (hsa _ (imaginaryPart x).2))
      rwa [hb] at h
    refine sfilter_cp_uwlim atTop
      (fun N => (hN N).toCompletelyPositiveMap.toLinearMap) Flin ?_ ?_
    · intro x
      have h := uwweaker_2 _ atTop _ (hall x)
      rw [hFlinapp x]
      exact h.congr fun N => (hNapp N x).symm
    · intro N
      exact (cp_iff _).out 1 0 |>.mp fun k M hM =>
        (hN N).toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
  -- (7) assemble
  set G : D →ₗ[ℂ] cornerSet B q :=
    { toFun := fun x => ⟨F x, (hF x).1⟩
      map_add' := fun x y => cornerSet.val_injective (hFadd x y)
      map_smul' := fun z x => cornerSet.val_injective (hFsmul z x) } with hGdef
  have hGval : ∀ x : D, (G x).1 = F x := fun _ => rfl
  have hGcp : IsCompletelyPositiveMap G := by
    intro n a bb
    have hsum : ∀ E : Fin n → cornerSet B q, (∑ i, E i).1 = ∑ i, (E i).1 :=
      fun E => map_sum cornerSet.valAddHom E Finset.univ
    show (0 : B) ≤ (∑ i, ∑ j, star (bb i) * G (star (a i) * a j) * bb j).1
    have hval : (∑ i, ∑ j, star (bb i) * G (star (a i) * a j) * bb j).1
        = ∑ i, ∑ j, star ((bb i).1) * Flin (star (a i) * a j) * (bb j).1 := by
      simp only [hsum, cornerSet.val_mul, cornerSet.val_star, hGval, hFlinapp]
    rw [hval]
    exact hFcp n a fun i => (bb i).1
  refine ⟨{ toCompletelyPositiveMap :=
              { toLinearMap := G
                map_cstarMatrix_nonneg' := (cp_iff G).out 0 1 |>.mp hGcp }
            preservesDirSups' := ?_ }, fun x => (hF x).2⟩
  intro Ds s hne hdir hlub
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    exact hFmono (hlub.1 hy)
  · intro u hu
    have hu' : ∀ y ∈ Ds, F ((y : selfAdjoint D) : D) ≤ (u : cornerSet B q).1 :=
      fun y hy => hu ⟨y, hy, rfl⟩
    have hfle : ∀ y ∈ Ds,
        (f ((y : selfAdjoint D) : D) : B) ≤ star d * (u : cornerSet B q).1 * d := by
      intro y hy
      have h2 := star_left_conjugate_le_conjugate (hu' y hy) d
      rwa [(hF _).2] at h2
    have hfl := f.preservesDirSups' Ds s hne hdir hlub
    have hfs : (f ((s : selfAdjoint D) : D) : B)
        ≤ star d * (u : cornerSet B q).1 * d := by
      refine hfl.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hfle y hy
    have hz : q * ((u : cornerSet B q).1 - F ((s : selfAdjoint D) : D)) * q
        = (u : cornerSet B q).1 - F ((s : selfAdjoint D) : D) := by
      rw [mul_sub, sub_mul, (u : cornerSet B q).2, (hF _).1]
    have hzz : 0 ≤ star d * ((u : cornerSet B q).1 - F ((s : selfAdjoint D) : D)) * d := by
      rw [mul_sub, sub_mul, (hF _).2, sub_nonneg]
      exact hfs
    have h := hbipos _ hz hzz
    show F ((s : selfAdjoint D) : D) ≤ (u : cornerSet B q).1
    rwa [sub_nonneg] at h

end StandardFilter
/-- **169X** (`dils-stand-filter`, dils.tex:6158, Example): the **standard
filter** `c_b : ⌈b⌉B⌈b⌉ → B`, `a ↦ √b a √b`, is a filter for `b ≥ 0` (see
proc.tex 96V, 98I). -/
theorem dils_stand_filter [VonNeumannAlgebra B] (b : B) (hb : 0 ≤ b) :
    ∃ c : NCPMap (cornerSet B (ceil b)) B,
      (∀ a : cornerSet B (ceil b), c a = CFC.sqrt b * a.1 * CFC.sqrt b) ∧
      IsFilterFor c b := by
  classical
  set d : B := CFC.sqrt b with hd
  have hsa : IsSelfAdjoint d := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)
  have hds : star d = d := hsa.star_eq
  have hdd : d * d = b := CFC.sqrt_mul_sqrt_self b hb
  have hqr : ceil b = rangeProj d := sfilter_ceil_eq b hb
  have hcd : ceil b * d = d := by rw [hqr]; exact (ceill_basic_2 d).1.2
  have hdc : d * ceil b = d := by
    have h := congrArg star hcd
    rwa [star_mul, hds, ((ceil_spec hb).1).isSelfAdjoint.star_eq] at h
  have hstd : star d * d = b := by rw [hds, hdd]
  have hdcd : star d * (1 : cornerSet B (ceil b)).1 * d = b := by
    show star d * ceil b * d = b
    rw [hds, hdc, hdd]
  -- the standard filter `c_b`
  obtain ⟨ad, had⟩ := exists_sfilterAd d
  obtain ⟨c, hc⟩ := exists_ncpComp ad (cornerInclNcp (A := B) (ceil b))
  have hcval : ∀ a : cornerSet B (ceil b), (c a : B) = star d * a.1 * d := by
    intro a
    rw [hc, cornerInclNcp_apply, had]
  refine ⟨c, fun a => by rw [hcval a, hds], hb, ?_, ?_⟩
  · rw [hcval 1, hdcd]
  intro C _ _ _ f hf1
  have hf1' : (f 1 : B) ≤ star d * d := by rwa [hstd]
  obtain ⟨g, hg⟩ := sfilter_factor (D := C) d (ceil b) hqr f hf1'
  have hsub : Subunital ⇑g := by
    show g 1 ≤ 1
    show (g 1).1 ≤ (1 : cornerSet B (ceil b)).1
    rw [← sub_nonneg]
    refine sfilter_bipos d _ ?_ ?_
    · rw [← hqr, mul_sub, sub_mul, (1 : cornerSet B (ceil b)).2, (g 1).2]
    · rw [mul_sub, sub_mul, hg 1, hdcd, sub_nonneg]
      exact hf1
  refine ⟨⟨g, hsub⟩, fun x => ?_, ?_⟩
  · show (c (g x) : B) = f x
    rw [hcval (g x), hg x]
  · rintro ⟨g', hsub'⟩ hg'
    have key : g' = g := by
      refine DFunLike.ext _ _ fun x => cornerSet.val_injective ?_
      refine mult_cancellation_3 d _ _ ?_ ?_ ?_
      · rw [← hqr]; exact (g' x).2
      · rw [← hqr]; exact (g x).2
      · have h1 : (c (g' x) : B) = f x := hg' x
        rw [hcval (g' x)] at h1
        exact h1.trans (hg x).symm
    subst key
    rfl

/- **169XI** (`dils-filter-basics-exercise`) follows **169XII** below: both
its parts use the injectivity of filters, and Lean needs that declaration
first.  The three statements are otherwise unchanged. -/

/-- **169XII** (`dils-filters-injective`, dils.tex:6188, Exercise): filters
are injective.

The hint (and the `bsols.tex` solution) route this through the *standard*
filter `c_b` of **169X**: `c = c_b ∘ ϑ` for an ncp-isomorphism `ϑ`, and `c_b`
is injective by `mult-cancellation`.  **169X** is proved (above), but it is
not needed here: the *uniqueness* half of `c`'s own universal property already gives
injectivity, tested against the ncp-maps out of the scalars
(`ncpOfNonneg` above).  For effects `x, y` with `c x = c y`, the map
`z ↦ z·(c x)` is an ncp-map `ℂᵤ → B` whose value at `1` is `c x ≤ c 1 ≤ b`,
and both `z ↦ z·x` and `z ↦ z·y` factor it through `c`; so they agree, and
`x = y`.  Scaling by `(1+‖x‖+‖y‖)⁻¹` extends this to all positive elements,
and `w = w⁺ − w⁻` together with `c(w*) = (c w)*` to all of `A`.

**No `[VonNeumannAlgebra]` binders**, where the exercise says "between von
Neumann algebras" — deliberately: the argument above never uses them, and
`pure_ncp_extreme` applies this lemma to the filter half of an `IsPureMap`,
whose intermediate algebra is only a C\*-algebra.  Adding the exercise's
binders would therefore break that call site.  (Restoring them for
**169XI**.2 costs nothing and *is* done: see `dils_filter_basics_2a`.) -/
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

/-! ### Auxiliary: ncp-maps scale (companion of the composition block above) -/

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

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6166, Exercise),
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
(**169XII**) directly; it is proved above and is the same fact.

**No `[VonNeumannAlgebra]` binders** on `A`, `B`, `C`, where the exercise
says "between von Neumann algebras".  As for `dils_filters_injective`, this
is forced by the call sites: `paschke_pure` and `pure_ncp_extreme` both
apply this part at the intermediate algebra of an `IsPureMap`, which carries
only a C\*-structure.  The generality is free — the proof never uses a von
Neumann structure on any of the three. -/
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

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6166, Exercise),
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
`dils_filters_injective`) yields `ψ(1) = 1`.

The three `[VonNeumannAlgebra]` binders are the exercise's own standing
setting ("between von Neumann algebras"); they were missing from the first
transcription, and are restored here because every call site (in this file
and in `Theses/B/Eff/VNExamples.lean`) already has them.  Contrast
`dils_filters_injective` and `dils_filter_basics_1` above, which must stay
binder-free: `paschke_pure` and `pure_ncp_extreme` apply them at the
intermediate algebra of an `IsPureMap`, which is only a C\*-algebra. -/
theorem dils_filter_basics_2a [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {C' : Type u} [CStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
    [VonNeumannAlgebra C'] (φ : NCPMap A B)
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

/-- **169XI** (`dils-filter-basics-exercise`, dils.tex:6166, Exercise),
part 2, second half: if moreover `(𝒫, ϱ, h)` is a Paschke dilation of
`φ'`, then `(𝒫, ϱ, c' ∘ h)` is a Paschke dilation of `φ`.

The author's solution is "by the previous point" — that is, part 1 applied
to the filter `c'` and the dilation of `φ'` — and that is what is done
here; the unitality of `φ'` is not used.  (So this half does *not* inherit
the defect of part 2's first half, which is the only place `c(1) = b` is
needed.)

The three `[VonNeumannAlgebra]` binders are the exercise's own standing
setting, restored together with those of part 2's first half; the appeal to
part 1 below goes through because part 1 is proved *without* them. -/
theorem dils_filter_basics_2b [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    {C' : Type u} [CStarAlgebra C'] [PartialOrder C'] [StarOrderedRing C']
    [VonNeumannAlgebra C'] (φ : NCPMap A B)
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

/-- **170I** (`dils-def-pure`, dils.tex:6194, Definition): an ncp-map is
**pure** when it is a composition of filters and corners; equivalently (by
proc.tex 100III `pure-fundamental`, cf. **170Ia**) a filter after a
corner, which is the form used here.

⚠️ **This is 168IV's normal form, not 170I's inductive definition**, and the
equivalence is *asserted*, not proved in the tree.  proc.tex 100III is
proved as `Theses.A.Proc.pure_fundamental` and is reachable from here, but
it states the equivalence for `Theses.A.Proc.IsPure` / `.IsCornerMap` /
`.IsFilter`, and none of those three is the predicate used here (test
objects von Neumann rather than C\*; corners unital; filters without the
author's subunitality repair; `[VonNeumannAlgebra]` on every intermediate
algebra).  Bridging them is a merge of the two developments, not a lemma;
see the file header.

The gap is not idle.  Both base cases of 170I are available —
`isPureMap_of_isCorner` and `isPureMap_of_isFilter` below — but the closure
under *composition* is not, which is why **171VII** `paschke_pure` has to
compose two corners by hand (`isCornerFor_comp`) where the thesis simply
says "a composite of pure maps is pure". -/
def IsPureMap (φ : NCPMap A B) : Prop :=
  ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
    (_ : StarOrderedRing C) (h : NCPMap A C) (c : NCPMap C B),
    IsCorner h ∧ IsFilter c ∧ ∀ a, φ a = c (h a)

/-- **Every corner is pure.**  `IsPureMap` asks for the normal form "a filter
after a corner" (**170I**, via **168IV**), so a bare corner `h` has to be
written `h = id ∘ h`; the identity is a filter for `1` (`isFilter_ncpId`).

Together with `isFilter_ncpId` this is the whole of **170I**'s "filters and
corners are pure" for the corner half — and it is what supplies the trailing
"hence pure" of **170IV**.1 (`surjective_nmiu_1_pure`). -/
theorem isPureMap_of_isCorner (h : NCPMap A B) (hh : IsCorner h) :
    IsPureMap h :=
  ⟨B, inferInstance, inferInstance, inferInstance, h, ncpId B, hh,
    isFilter_ncpId, fun _ => rfl⟩

/-- **Every filter is pure** — the other half of "filters and corners are
pure": `c = c ∘ id`, and the identity is a corner for `1` (its universal
property is trivial, the mediating map being `f` itself). -/
theorem isPureMap_of_isFilter (c : NCPMap A B) (hc : IsFilter c) :
    IsPureMap c :=
  ⟨A, inferInstance, inferInstance, inferInstance, ncpId A, c,
    ⟨1, ⟨zero_le_one, le_rfl⟩, rfl, fun _ _ _ _ f _ =>
      ⟨f, fun _ => rfl, fun _ hf => DFunLike.ext _ _ fun x => hf x⟩⟩,
    hc, fun _ => rfl⟩

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### **170II**.1: the pure maps `B(ℋ) → B(𝒦)`

**170II**.1 `dils_examples_pure_1` is proved at the **foot of parsec 1710**
(section `PureTypeI` below), because its proof runs through **171VII**
`paschke_pure` — "pure ⟺ the `ϱ`-leg of a Paschke dilation is surjective".
There is no circularity: `paschke_pure` consumes **170II**.2
`dils_examples_pure_2`, immediately below, and never **170II**.1. -/

/-- Auxiliary for **170II**.2: a corner precomposed with a *bijective*
nmiu-map is again a corner (for the preimage of its effect).  Both the
factorisation and its uniqueness transport along the ncp inverse
(`pcorner_exists_ncpInv`). -/
private theorem isCorner_comp_nmiuBij {P Q R : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    (h : NCPMap Q R) (hh : IsCorner h) (ϑ : NMIUMap P Q)
    (hbij : Function.Bijective ⇑ϑ) (k : NCPMap P R) (hk : ∀ x, k x = h (ϑ x)) :
    IsCorner k := by
  obtain ⟨a, ha01, hha, huniv⟩ := hh
  obtain ⟨g, hgϑ, hϑg⟩ := pcorner_exists_ncpInv ϑ hbij
  have hϑ1 : (ϑ (1 : P) : Q) = 1 := map_one ϑ.toStarAlgHom
  have hg1 : (g (1 : Q) : P) = 1 := by rw [← hϑ1, hgϑ]
  have hgmono : ∀ x y : Q, x ≤ y → g x ≤ g y := fun _ _ hxy => (ncpPos g).monotone hxy
  refine ⟨g a, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h0 : (0 : P) = g 0 := (map_zero g.toCompletelyPositiveMap).symm
    rw [h0]
    exact hgmono _ _ ha01.1
  · rw [← hg1]
    exact hgmono _ _ ha01.2
  · rw [hk, hk, hϑg, hϑ1, hha]
  · intro C _ _ _ f hf
    obtain ⟨fg, hfg⟩ := exists_ncpComp f g
    have hfga : (fg a : C) = fg 1 := by rw [hfg, hfg, hg1, ← hf]
    obtain ⟨f', hf'1, hf'2⟩ := huniv C ‹_› ‹_› ‹_› fg hfga
    refine ⟨f', fun x => ?_, fun f'' hf'' => ?_⟩
    · rw [hk, hf'1 (ϑ x), hfg, hgϑ]
    · refine hf'2 f'' fun y => ?_
      have h1 : (f'' (h y) : C) = f'' (k (g y)) := by rw [hk, hϑg]
      rw [h1, hf'' (g y), hfg]
/-- **170II** (`dils-examples-pure`, dils.tex:6203, Examples), part 2: the
right-hand side `h` of any Paschke dilation is pure.

⚠️ **The two `[VonNeumannAlgebra]` binders are new.**  They are the
chapter's standing hypothesis (dils.tex **140II** opens "let `φ : 𝒜 → ℬ` be
any ncp-map **between von Neumann algebras**") and every sibling statement
about a `PaschkeTriple` carries them; they were dropped in the first
transcription of this point.  This is the same repair the author ruled on
for **169V** and for **170IV** (QUESTIONS **D5**, "restore the
hypothesis"): the proof reduces to the *standard* dilation of **154III**,
whose construction `existence_paschke` needs both algebras to be von
Neumann.

**Proof**, transcribed from dils.tex:6205.  `c'` is the standard filter of
`φ(1)` (**169X** `dils_stand_filter`), `φ'` the unique unital ncp-map with
`φ = c' ∘ φ'` (**169XI**.2a), and `(𝒫', ϱ', h')` a Paschke dilation of `φ'`
(**154III**).  Then `h'` is a *corner* by **169V**
`h_is_corner_for_unital_map`, `(𝒫', ϱ', c' ∘ h')` is a Paschke dilation of
`φ` by **169XI**.2b, and `paschke_unique_up_to_iso` (**140VIII**) supplies
the nmiu-isomorphism `ϑ : 𝒫 ≅ 𝒫'` with `c' ∘ h' ∘ ϑ = h`.  So
`h = c' ∘ (h' ∘ ϑ)` with `h' ∘ ϑ` a corner (`isCorner_comp_nmiuBij`) and
`c'` a filter — i.e. `h` is pure.

**170III** (Remark, the †-structure preview: there is a unique dagger on
the category of von Neumann algebras with pure maps, `(ad_V)† = ad_{V*}`;
see eff.tex 215III `dagger-theorem`) — not converted here. -/
theorem dils_examples_pure_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    IsPureMap D.h := by
  classical
  let _ := D.vn
  have hmono : ∀ {x y : A}, x ≤ y → (φ x : B) ≤ φ y := fun h => (ncpPos φ).monotone h
  have hφ0 : (φ (0 : A) : B) = 0 := map_zero φ.toCompletelyPositiveMap
  have hb : (0 : B) ≤ φ 1 := by
    have h := hmono (zero_le_one' A)
    rwa [hφ0] at h
  -- the standard filter for `φ(1)`
  obtain ⟨c', -, hc'⟩ := dils_stand_filter (φ 1) hb
  let _ : VonNeumannAlgebra (cornerSet B (ceil (φ 1))) :=
    cornerSet_vonNeumannAlgebra B (ceil (φ 1))
  -- the unique unital `φ'` with `φ = c' ∘ φ'`, and a Paschke dilation of it
  obtain ⟨φ', ⟨hφ'1, hφ'2⟩, -⟩ := dils_filter_basics_2a φ c' hc'
  obtain ⟨M⟩ := existence_paschke φ'
  set D' : PaschkeTriple A (cornerSet B (ceil (φ 1))) :=
    ⟨(Ba (cornerSet B (ceil (φ 1))) M.X)ᵐᵒᵖ,
      @vonNeumannAlgebra_mulOpposite (Ba (cornerSet B (ceil (φ 1))) M.X) _ _ _
        (ba_vonNeumannAlgebra M.selfDual), M.ρ, M.h⟩ with hD'def
  have hD' : IsPaschkeDilationOf D' ⇑φ' := existence_paschke_5 φ' M
  -- `169V`: the right leg of a dilation of a *unital* map is a corner
  have hcorner : IsCorner D'.h := h_is_corner_for_unital_map φ' hφ'1 D' hD'
  -- `169XI`.2: composing with the filter gives a dilation of `φ`
  obtain ⟨h₂, hh₂, hD₂⟩ := dils_filter_basics_2b φ c' hc' φ' ⟨hφ'1, hφ'2⟩ D' hD'
  -- and Paschke dilations are unique up to nmiu-isomorphism
  obtain ⟨ϑ, ⟨hbij, -, hϑh⟩, -⟩ :=
    paschke_unique_up_to_iso ⇑φ D ⟨D'.P, D'.vn, D'.ρ, h₂⟩ hD hD₂
  obtain ⟨ϑc, hϑc⟩ := pcorner_exists_ncpOfNmiu ϑ
  obtain ⟨k, hkdef⟩ := exists_ncpComp D'.h ϑc
  have hkval : ∀ x : D.P, (k x : cornerSet B (ceil (φ 1))) = D'.h (ϑ x) := by
    intro x; rw [hkdef, hϑc]
  refine ⟨cornerSet B (ceil (φ 1)), inferInstance, inferInstance, inferInstance,
    k, c', isCorner_comp_nmiuBij D'.h hcorner ϑ hbij k hkval, ⟨φ 1, hc'⟩, fun x => ?_⟩
  rw [hkval, ← hh₂, hϑh]

/-- **170IV** (`surjective-nmiu`, dils.tex:6231, Exercise), first half:
every surjective nmiu-map **between von Neumann algebras** is a corner of a
central projection (hence pure).

The two `[VonNeumannAlgebra]` binders are the exercise's own hypothesis; they
were missing from the first transcription of this point, which therefore
claimed the result for arbitrary C\*-algebras (QUESTIONS **D5**, ruled on by
Bas: restore the hypothesis).  They are not decoration — the central
projection is produced by **69IV** `carrier_miu`, which needs them.

The exercise's trailing **"hence pure"** is `surjective_nmiu_1_pure`
immediately below, *not* a fourth conjunct here: this statement is
destructured positionally inside `paschke_pure`, and appending a conjunct
would silently rebind its components. -/
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

/-- **170IV** (`surjective-nmiu`, dils.tex:6231, Exercise), first half, the
trailing clause: a surjective nmiu-map between von Neumann algebras is
**pure**.

The exercise reads "…is a corner of a central projection, hence pure", and
this is the "hence pure": `surjective_nmiu_1` (above) supplies the corner,
and `isPureMap_of_isCorner` turns any corner into a pure map by writing it
as `id ∘ h`, the identity being a filter for `1` (`isFilter_ncpId`).  It is
a separate declaration rather than a fourth conjunct of `surjective_nmiu_1`
because that statement is destructured positionally in `paschke_pure`. -/
theorem surjective_nmiu_1_pure [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ϱ : NMIUMap A B) (hs : Function.Surjective ⇑ϱ)
    (φ : NCPMap A B) (hφ : ∀ a, φ a = ϱ a) :
    IsPureMap φ := by
  obtain ⟨z, -, -, hcorner⟩ := surjective_nmiu_1 ϱ hs φ hφ
  exact isPureMap_of_isCorner φ ⟨z, hcorner⟩

/-- **170IV** (`surjective-nmiu`, dils.tex:6231, Exercise), second half:
conversely, every corner of a central projection **in a von Neumann
algebra** is (equal as a map to) a surjective nmiu-map.  (For the
`[VonNeumannAlgebra]` binders see the first half.)

⚠️ **False as stated**, and deliberately left `sorry` — see
`surjective_nmiu_2_false` immediately below for a machine-checked
counterexample, and QUESTIONS **D7**. -/
theorem surjective_nmiu_2 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (z : A)
    (hz : IsStarProjection z) (hcentral : IsCentral A z)
    (hφ : IsCornerFor φ z) :
    ∃ ϱ : NMIUMap A B, (∀ a, ϱ a = φ a) ∧ Function.Surjective ⇑ϱ :=
  sorry

/-- **Negative result**, kept in the tree (QUESTIONS **D7**): the converse
half of **170IV** — `surjective_nmiu_2` above — is **false** under **169II**
as printed, and so is the step of the author's solution
(`bsols.tex`, `surjective-nmiu`) that reads "`ϑ₁` is an ncp-isomorphism and
consequently an nmiu-isomorphism by `iso`": proc.tex **99IX** `iso`
(`Theses.A.Proc.iso`, reachable from here) is about **ncpsu**-isomorphisms,
and the two universal properties yield only an *ncp*-isomorphism.

The witness is as small as it gets: `𝒜 = ℬ = ℂ`, `z = 1`, `φ = λ·id` for any
`λ > 0`, `λ ≠ 1`.  A positive multiple of a corner is again a corner under
169II as printed, because the mediating map `f' = λ⁻¹f` is ncp; but
`φ 1 = λ ≠ 1`, and every nmiu-map is unital.  The same scaling breaks the
claim at every central projection `z` (take `φ = λ·h_z`), so nothing is
special about `z = 1`.

This is the *same* defect as the one already ruled on for **filters** in
**169VIII** (QUESTIONS **B11**, `IsFilterFor`): the mediating map of a
universal property among ncp-maps has to be subunital.  It is not repaired by
the same edit, though — for filters the hypothesis `f(1) ≤ b ≤ 1` makes the
quantified `f` subunital by itself, whereas `f a = f 1` constrains nothing,
so for corners the quantified `f` needs restricting to ncpsu as well (else
`h_z` itself stops being a corner, `f = 2·h_z` witnessing). -/
theorem surjective_nmiu_2_false {l : ℝ} (hl : 0 < l) (hl1 : l ≠ 1) :
    ∃ φ : NCPMap CU.{u} CU.{u},
      (∀ a, φ a = ((l : ℝ) : ℂ) • a) ∧
      IsStarProjection (1 : CU.{u}) ∧ IsCentral CU.{u} (1 : CU.{u}) ∧
      IsCornerFor φ (1 : CU.{u}) ∧
      ¬ ∃ ϱ : NMIUMap CU.{u} CU.{u}, ∀ a, ϱ a = φ a := by
  classical
  have hll : ((l : ℝ) : ℂ) * ((l⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hl.ne', Complex.ofReal_one]
  -- the identity as an ncp-map, and `φ = λ·id`
  obtain ⟨idm, hid⟩ : ∃ f : NCPMap CU.{u} CU.{u}, ∀ a, f a = a := by
    refine ⟨{ toCompletelyPositiveMap :=
                { toLinearMap := LinearMap.id
                  map_cstarMatrix_nonneg' :=
                    (cp_iff _).out 0 1 |>.mp
                      (cp_of_mi _ (fun _ _ => rfl) (fun _ => rfl)) }
              preservesDirSups' := ?_ }, fun _ => rfl⟩
    intro D s hne _ hlub
    exact isLUB_coe_of_isLUB hne hlub
  obtain ⟨φ, hφ⟩ := exists_ncpSmul idm hl
  have hφa : ∀ a : CU.{u}, φ a = ((l : ℝ) : ℂ) • a := fun a => by rw [hφ, hid]
  refine ⟨φ, hφa, IsStarProjection.one CU.{u}, fun b => by rw [one_mul, mul_one],
    ⟨Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩, rfl, ?_⟩, ?_⟩
  · -- the universal property: `f' = λ⁻¹f` is ncp, and it is forced
    intro C iC iP iS f _
    letI := iC; letI := iP; letI := iS
    obtain ⟨g, hg⟩ := exists_ncpSmul f (inv_pos.mpr hl)
    have hfsmul : ∀ (r : ℂ) (x : CU.{u}), f (r • x) = r • f x := fun r x =>
      map_smul f.toCompletelyPositiveMap.toLinearMap r x
    have hy : ∀ y : CU.{u}, φ (((l⁻¹ : ℝ) : ℂ) • y) = y := by
      intro y
      rw [hφa, smul_smul, hll, one_smul]
    refine ⟨g, fun x => ?_, fun g' hg' => ?_⟩
    · rw [hg, hφa, hfsmul, smul_smul, mul_comm, hll, one_smul]
    · refine DFunLike.ext _ _ fun y => ?_
      have h1 := hg' (((l⁻¹ : ℝ) : ℂ) • y)
      rw [hy] at h1
      rw [h1, hg, hfsmul]
  · -- but `φ` is not unital, so it is no nmiu-map
    rintro ⟨ϱ, hϱ⟩
    have h1 : (ϱ 1 : CU.{u}) = 1 := map_one ϱ.toStarAlgHom
    rw [hϱ 1, hφa] at h1
    have h3 : ((l : ℝ) : ℂ) = 1 := by
      have := congrArg ULift.down h1
      simpa using this
    exact hl1 (by exact_mod_cast h3)

end Pure


/-! ### The standard corner of a central projection

For a **central** projection `z` the corner `z𝒜` is a direct summand, and
`a ↦ zaz` is an nmiu-map onto it.  This is the `h_{⌈⌈p⌉⌉}` of **171II**.
(Normality of the inclusion `z𝒜 ⊆ 𝒜` is *not* special to central `z`; see
`cornerSet.val_normal`.) -/

section CentralCorner

set_option linter.unusedSectionVars false

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A] {z : A} [Fact (IsStarProjection z)]

omit [VonNeumannAlgebra A] in
private theorem pcorner_mem_of_central (a : A) :
    z * (z * a * z) * z = z * a * z := by
  have hzz : z * z = z := (cornerSet.proj z).isIdempotentElem.eq
  calc z * (z * a * z) * z = (z * z) * a * (z * z) := by noncomm_ring
    _ = z * a * z := by rw [hzz]

/-- The inclusion `z𝒜 ⊆ 𝒜` of a central corner preserves directed suprema.
Centrality is **not** needed: `cornerSet.val_normal` says the suprema of any
corner are computed in `𝒜`.  The hypothesis is kept only so that the call
sites below read as the thesis's argument does. -/
private theorem pcorner_val_normal (hc : IsCentral A z) :
    PreservesDirSups (fun c : cornerSet A z => c.1) :=
  cornerSet.val_normal

/-- The **standard corner** `h_z : 𝒜 → z𝒜`, `a ↦ zaz`, of a central
projection, as an nmiu-map (**170IV**.2 for the concrete corner). -/
private noncomputable def pcorner_centralCorner (hc : IsCentral A z) :
    NMIUMap A (cornerSet A z) where
  toStarAlgHom :=
    { toFun := fun a => ⟨z * a * z, pcorner_mem_of_central a⟩
      map_one' := Subtype.ext (by
        show z * 1 * z = z
        rw [mul_one]
        exact (cornerSet.proj z).isIdempotentElem.eq)
      map_mul' := fun a b => Subtype.ext (by
        show z * (a * b) * z = (z * a * z) * (z * b * z)
        have hzz : z * z = z := (cornerSet.proj z).isIdempotentElem.eq
        symm
        calc (z * a * z) * (z * b * z) = z * a * (z * z) * b * z := by noncomm_ring
          _ = z * a * (z * b) * z := by rw [hzz]; noncomm_ring
          _ = z * a * (b * z) * z := by rw [hc b]
          _ = z * a * b * (z * z) := by noncomm_ring
          _ = z * (a * b) * z := by rw [hzz]; noncomm_ring)
      map_zero' := Subtype.ext (by show z * 0 * z = 0; simp)
      map_add' := fun a b => Subtype.ext (by
        show z * (a + b) * z = z * a * z + z * b * z
        noncomm_ring)
      commutes' := fun r => Subtype.ext (by
        show z * (algebraMap ℂ A r) * z = (algebraMap ℂ (cornerSet A z) r).1
        have h1 : algebraMap ℂ A r = r • (1 : A) := Algebra.algebraMap_eq_smul_one r
        have h2 : (algebraMap ℂ (cornerSet A z) r).1 = r • (1 : cornerSet A z).1 := by
          rw [Algebra.algebraMap_eq_smul_one r]; rfl
        rw [h1, h2, cornerSet.val_one]
        have hzz : z * z = z := (cornerSet.proj z).isIdempotentElem.eq
        rw [mul_smul_comm, smul_mul_assoc, mul_one, hzz])
      map_star' := fun a => Subtype.ext (by
        show z * star a * z = star (z * a * z)
        have hzs : star z = z := (cornerSet.proj z).isSelfAdjoint.star_eq
        rw [star_mul, star_mul, hzs]
        noncomm_ring) }
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hzs : star z = z := (cornerSet.proj z).isSelfAdjoint.star_eq
    have hbdd : BddAbove D := ⟨s, hlub.1⟩
    have hA := ad_normal z D ⟨hne, hdir, hbdd⟩
    have hsd : dirSup D ⟨hne, hdir, hbdd⟩ = s :=
      (isLUB_dirSup D ⟨hne, hdir, hbdd⟩).unique hlub
    rw [hsd, hzs] at hA
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      refine Subtype.coe_le_coe.mp ?_
      show z * ((d : selfAdjoint A) : A) * z ≤ z * ((s : selfAdjoint A) : A) * z
      exact hA.1 ⟨d, hd, rfl⟩
    · intro u hu
      refine Subtype.coe_le_coe.mp ?_
      refine hA.2 ?_
      rintro _ ⟨d, hd, rfl⟩
      exact Subtype.coe_le_coe.mpr (hu ⟨d, hd, rfl⟩)

private theorem pcorner_centralCorner_apply (hc : IsCentral A z) (a : A) :
    (pcorner_centralCorner hc a).1 = z * a * z := rfl

/-- The inclusion `z𝒜 ⊆ 𝒜` of a central corner as an **ncp**-map: complete
positivity because `Subtype.val` is a (non-unital) ∗-homomorphism
(**34IV**.3 `cp_of_mi`), normality by `pcorner_val_normal`.  Composing an
ncp-map `𝒜 → p𝒜p` with it is how `h'_p : ⌈⌈p⌉⌉𝒜 → p𝒜p` of **171II** is
obtained. -/
private theorem pcorner_exists_inclNcp (hc : IsCentral A z) :
    ∃ g : NCPMap (cornerSet A z) A, ∀ c : cornerSet A z, g c = c.1 :=
  ⟨{ toCompletelyPositiveMap :=
       { toLinearMap :=
           { toFun := fun c => c.1
             map_add' := fun _ _ => rfl
             map_smul' := fun _ _ => rfl }
         map_cstarMatrix_nonneg' :=
           (cp_iff _).out 0 1 |>.mp
             (cp_of_mi _ (fun x y => cornerSet.val_mul x y)
               (fun x => cornerSet.val_star x)) }
     preservesDirSups' := pcorner_val_normal hc }, fun _ => rfl⟩

end CentralCorner

/-! ### Infrastructure for **171II**: the module `𝒜 ⊗_{h_p} p𝒜p`

The thesis proves `paschke-corner` in three steps: `𝒜p` is a self-dual
Hilbert `p𝒜p`-module, `𝒜 ⊗_{h_p} p𝒜p ≅ 𝒜p`, and `𝒷ᵃ(𝒜p) ≅ ⌈⌈p⌉⌉𝒜`.  The
development below **replaces the first two steps**: `𝒜p` is never
constructed.  Everything is done inside the abstract `PaschkeModule` of
**154III**, using three observations:

* every elementary tensor is of the form `a ⊗ 1` (`pcorner_tprod_eq_one`),
  because `a ⊗ pbp = (pbp·a) ⊗ 1`; so the elementary tensors form a
  `p𝒜p`-submodule, ultranorm dense by **160IV**.2 together with
  `paschkeModule_inner_tprod_separating` (`pcorner_unDense_tprod`);
* the thesis's orthonormal basis transports to `(uᵢ ⊗ 1)ᵢ`, for the partial
  isometries of **83V** `cceil_sum` (`pcorner_onb_data`,
  `pcorner_isONBasis_tprod`) — the only analytic step, and it is the
  thesis's own: `⟨uᵢ ⊗ 1, a ⊗ 1⟩ • (uᵢ ⊗ 1) = p a qᵢ ⊗ 1` and `∑ᵢ qᵢ ↑ ⌈⌈p⌉⌉`
  ultrastrongly, which is `npFunctional_tendsto_of_isLUB` for the
  np-functional `x ↦ ω(φ(p a x a* p))`;
* `|a ⊗ 1⟩⟨b ⊗ 1| = ϱ(b* p a)` (`pcorner_mketbra_tprod`), an identity
  checked on elementary tensors — this is what makes `ϱ` surjective, since
  by **159IV** `ketbra_ultraweakly_dense` the ketbras of a basis span an
  ultraweakly dense subspace and the basis above consists of elementary
  tensors.

`pcorner_rho_eq_zero_iff` and `pcorner_forall_mul_eq_zero_iff` compute the
kernel: `ϱ(a) = 0` iff `pxa = 0` for all `x` iff `⌈⌈p⌉⌉a = 0`, the second
step by **68I** `cceil_fundamental`. -/

/-- Auxiliary: `star x * x = 0` forces `x = 0`. -/
private theorem pcorner_eq_zero_of_star_mul_self {C : Type*} [CStarAlgebra C] (x : C)
    (h : star x * x = 0) : x = 0 := by
  have h1 : ‖x‖ * ‖x‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, h, norm_zero]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])

/-- np-functionals transfer back from the opposite algebra (the converse of
`npFunctionalOp`). -/
private noncomputable def pcorner_npUnop {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (ν : NPFunctional Cᵐᵒᵖ) : NPFunctional C where
  toPositiveLinearMap :=
    PositiveLinearMap.mk₀
      ((ν.toPositiveLinearMap : Cᵐᵒᵖ →ₗ[ℂ] ℂ).comp
        ((MulOpposite.opLinearEquiv ℂ).toLinearMap : C →ₗ[ℂ] Cᵐᵒᵖ))
      (fun x hx => npFunctional_nonneg ν ((mop_nonneg_iff _).mpr hx))
  preservesDirSups' := by
    intro D s hne hdir hlub
    have hlub' : IsLUB (selfAdjointUnop.symm '' D) (selfAdjointUnop.symm s) :=
      selfAdjointUnop.symm.isLUB_image'.mpr hlub
    have h := ν.preservesDirSups' (selfAdjointUnop.symm '' D) (selfAdjointUnop.symm s)
      (hne.image _) (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        obtain ⟨w, hw, hxw, hyw⟩ := hdir x hx y hy
        exact ⟨selfAdjointUnop.symm w, ⟨w, hw, rfl⟩, hxw, hyw⟩) hlub'
    rw [Set.image_image] at h
    exact h

private theorem pcorner_uwTendsto_op {C : Type u} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] {κ : Type*} {l : Filter κ} (f : κ → C) (c : C)
    (h : UWTendsto f l c) :
    UWTendsto (fun i => MulOpposite.op (f i)) l (MulOpposite.op c) := by
  rw [uwTendsto_iff]
  intro ν
  exact (uwTendsto_iff f l c).mp h (pcorner_npUnop ν)

/-! ### Auxiliary: transporting a Paschke dilation along a bijective nmiu-map

The two lemmas this needs — an nmiu-map is an ncp-map, and the inverse of a
*bijective* one is again an ncp-map — are `pcorner_exists_ncpOfNmiu` and
`pcorner_exists_ncpInv`, stated above at **169V**, which needs the second one
too.

`pcorner_transport` is the transport lemma: a Paschke dilation stays one
along a bijective nmiu-map compatible with `ϱ` and `h`.  Note this is *not*
**140VIII** `paschke_unique_up_to_iso`, which goes the other way: it produces
such an isomorphism between two dilations of the same map, and cannot be used
to promote a triple that is not yet known to be a dilation. -/

/-- **Transport**: if `D₁` is a Paschke dilation of `φ` and `ϑ : D₂.𝒫 → D₁.𝒫`
is a *bijective* nmiu-map with `ϑ ∘ ϱ₂ = ϱ₁` and `h₁ ∘ ϑ = h₂`, then `D₂` is a
Paschke dilation of `φ` too.  Mediate with `ϑ⁻¹ ∘ σ₁`; uniqueness comes from
the injectivity of `ϑ`. -/
private theorem pcorner_transport {𝒜 ℬ : Type u} [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [CStarAlgebra ℬ] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (φ : 𝒜 → ℬ) (D₁ D₂ : PaschkeTriple 𝒜 ℬ)
    (hD₁ : IsPaschkeDilationOf D₁ φ) (ϑ : NMIUMap D₂.P D₁.P)
    (hbij : Function.Bijective ⇑ϑ) (hρ : ∀ a, ϑ (D₂.ρ a) = D₁.ρ a)
    (hh : ∀ c, D₁.h (ϑ c) = D₂.h c) :
    IsPaschkeDilationOf D₂ φ := by
  obtain ⟨ϑinv, hgf, hfg⟩ := pcorner_exists_ncpInv ϑ hbij
  obtain ⟨ϑn, hϑn⟩ := pcorner_exists_ncpOfNmiu ϑ
  refine ⟨fun a => ?_, fun D' hD' => ?_⟩
  · rw [← hh (D₂.ρ a), hρ a]
    exact hD₁.1 a
  · obtain ⟨σ₁, ⟨hσa, hσb⟩, huniq⟩ := hD₁.2 D' hD'
    obtain ⟨τ, hτ⟩ := exists_ncpComp ϑinv σ₁
    have hϑτ : ∀ c, ϑ (τ c) = σ₁ c := fun c => by rw [hτ, hfg]
    refine ⟨τ, ⟨fun a => ?_, fun c => ?_⟩, fun τ' hτ' => ?_⟩
    · rw [hτ, hσa a, ← hρ a, hgf]
    · rw [← hh (τ c), hϑτ c, hσb c]
    · obtain ⟨κ, hκ⟩ := exists_ncpComp ϑn τ'
      have hκ1 : ∀ a, κ (D'.ρ a) = D₁.ρ a := fun a => by
        rw [hκ, hϑn, hτ'.1 a, hρ a]
      have hκ2 : ∀ c, D₁.h (κ c) = D'.h c := fun c => by
        rw [hκ, hϑn, hh (τ' c), hτ'.2 c]
      have hκσ : κ = σ₁ := huniq κ ⟨hκ1, hκ2⟩
      refine DFunLike.ext _ _ fun c => hbij.1 ?_
      have h1 : ϑ (τ' c) = κ c := by rw [hκ, hϑn]
      rw [h1, hκσ, hϑτ c]


section PaschkeCornerAux

set_option linter.unusedSectionVars false

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [VonNeumannAlgebra A] {p : A} [Fact (IsStarProjection p)]
  {φ : NCPMap A (cornerSet A p)} (hval : ∀ a : A, (φ a).1 = p * a * p)

include hval

private theorem pcorner_map_mul_left (b : cornerSet A p) (y : A) : φ (b.1 * y) = b * φ y := by
  have hbl : p * b.1 = b.1 := cornerSet.mul_left b
  have hbr : b.1 * p = b.1 := cornerSet.mul_right b
  refine Subtype.ext ?_
  rw [hval, cornerSet.val_mul, hval]
  calc p * (b.1 * y) * p = (p * b.1) * y * p := by noncomm_ring
    _ = b.1 * y * p := by rw [hbl]
    _ = (b.1 * p) * y * p := by rw [hbr]
    _ = b.1 * (p * y * p) := by noncomm_ring

private theorem pcorner_map_mul_right (b : cornerSet A p) (y : A) : φ (y * star b.1) = φ y * star b := by
  have hbl : p * b.1 = b.1 := cornerSet.mul_left b
  have hbr : b.1 * p = b.1 := cornerSet.mul_right b
  have hbl' : star b.1 * p = star b.1 := by
    have := congrArg star hbl
    simpa [star_mul, (cornerSet.proj p).isSelfAdjoint.star_eq] using this
  have hbr' : p * star b.1 = star b.1 := by
    have := congrArg star hbr
    simpa [star_mul, (cornerSet.proj p).isSelfAdjoint.star_eq] using this
  refine Subtype.ext ?_
  rw [hval, cornerSet.val_mul, hval, cornerSet.val_star]
  calc p * (y * star b.1) * p = p * y * (star b.1 * p) := by noncomm_ring
    _ = p * y * star b.1 := by rw [hbl']
    _ = p * y * (p * star b.1) := by rw [hbr']
    _ = (p * y * p) * star b.1 := by noncomm_ring

variable [VonNeumannAlgebra (cornerSet A p)] (M : PaschkeModule φ)

/-- Every elementary tensor is of the form `a ⊗ 1`. -/
private theorem pcorner_tprod_eq_one (a : A) (b : cornerSet A p) :
    M.tprod a b = M.tprod (b.1 * a) 1 := by
  have h : (inner (cornerSet A p) (M.tprod a b - M.tprod (b.1 * a) 1)
      (M.tprod a b - M.tprod (b.1 * a) 1) : cornerSet A p) = 0 := by
    rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_sub_right, M.inner_tprod, M.inner_tprod, M.inner_tprod,
      M.inner_tprod]
    have e1 : (1 : cornerSet A p) * φ (b.1 * a * star a) * star b
        = b * φ (a * star a) * star b := by
      rw [one_mul, mul_assoc b.1 a (star a), pcorner_map_mul_left hval]
    have e2 : b * φ (a * star (b.1 * a)) * star (1 : cornerSet A p)
        = b * φ (a * star a) * star b := by
      rw [star_one, mul_one, star_mul, ← mul_assoc a (star a) (star b.1),
        pcorner_map_mul_right hval, ← mul_assoc]
    have e3 : (1 : cornerSet A p) * φ (b.1 * a * star (b.1 * a))
        * star (1 : cornerSet A p) = b * φ (a * star a) * star b := by
      rw [star_one, mul_one, one_mul, star_mul, mul_assoc b.1 a (star a * star b.1),
        pcorner_map_mul_left hval, ← mul_assoc a (star a) (star b.1), pcorner_map_mul_right hval, ← mul_assoc]
    rw [e1, e2, e3]
    abel
  have := (CStarModule.inner_self (A := cornerSet A p)).mp h
  exact sub_eq_zero.mp this

/-- `a ⊗ 1 = pa ⊗ 1`. -/
private theorem pcorner_tprod_p_left (a : A) : M.tprod a 1 = M.tprod (p * a) 1 := by
  have hpp : p * p = p := (cornerSet.proj p).isIdempotentElem.eq
  have hps : star p = p := (cornerSet.proj p).isSelfAdjoint.star_eq
  have hφ0 : φ (0 : A) = 0 := Subtype.ext (by rw [hval]; simp)
  have hL : ∀ x : A, φ (p * x) = φ x := fun x => Subtype.ext (by
    rw [hval, hval]
    calc p * (p * x) * p = (p * p) * x * p := by noncomm_ring
      _ = p * x * p := by rw [hpp])
  have hR : ∀ x : A, φ (x * p) = φ x := fun x => Subtype.ext (by
    rw [hval, hval]
    calc p * (x * p) * p = p * x * (p * p) := by noncomm_ring
      _ = p * x * p := by rw [hpp])
  have hkey : ∀ x y : A, φ (p * x * star (p * y)) = φ (x * star y) := by
    intro x y
    rw [star_mul, hps, mul_assoc, hL, ← mul_assoc, hR]
  have h : (inner (cornerSet A p) (M.tprod a 1 - M.tprod (p * a) 1)
      (M.tprod a 1 - M.tprod (p * a) 1) : cornerSet A p) = 0 := by
    rw [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
      CStarModule.inner_sub_right, M.inner_tprod, M.inner_tprod, M.inner_tprod,
      M.inner_tprod, hkey a a]
    have e1 : φ (p * a * star a) = φ (a * star a) := by rw [mul_assoc]; exact hL _
    have e2 : φ (a * star (p * a)) = φ (a * star a) := by
      rw [star_mul, hps, ← mul_assoc]; exact hR _
    rw [e1, e2]
    abel
  have := (CStarModule.inner_self (A := cornerSet A p)).mp h
  exact sub_eq_zero.mp this

/-- The ketbra of two elementary tensors is in the image of `ϱ`. -/
private theorem pcorner_mketbra_tprod (x y : A) :
    mketbraBa (M.tprod x 1) (M.tprod y 1) = (M.ρ (star y * p * x)).unop := by
  refine paschkeModule_ba_ext φ M fun a b => ?_
  have hbr : b.1 * p = b.1 := cornerSet.mul_right b
  show (inner (cornerSet A p) (M.tprod y 1) (M.tprod a b) : cornerSet A p)
      • M.tprod x 1 = _
  rw [M.inner_tprod, M.ρ_tprod, star_one, mul_one]
  rw [M.compat.smul_action, mul_one,
    pcorner_tprod_eq_one hval M x (b * φ (a * star y)),
    pcorner_tprod_eq_one hval M (a * (star y * p * x)) b]
  congr 1
  show (b * φ (a * star y)).1 * x = b.1 * (a * (star y * p * x))
  rw [cornerSet.val_mul, hval]
  calc b.1 * (p * (a * star y) * p) * x = (b.1 * p) * (a * star y) * (p * x) := by
        noncomm_ring
    _ = b.1 * (a * (star y * p * x)) := by rw [hbr]; noncomm_ring


/-- Sums pull out of the first argument of `⊗`. -/
private theorem pcorner_tprod_sum {κ : Type*} (s : Finset κ) (f : κ → A) (b : cornerSet A p) :
    ∑ i ∈ s, M.tprod (f i) b = M.tprod (∑ i ∈ s, f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : M.tprod (0 : A) b = 0 := by
        have := M.compat.smul_complex 0 0 b
        simpa using this
      simp [h0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
      M.compat.add_left]

/-- The orthonormal family `(uᵢ ⊗ 1)` built from `cceil-sum`: the partial
isometries `uᵢ` have pairwise orthogonal supports `qᵢ = uᵢ*uᵢ` with
`⋁ᵢ qᵢ = ⌈⌈p⌉⌉`, and ranges `uᵢuᵢ* ≤ p`. -/
private theorem pcorner_onb_data :
    ∃ (κ : Type u) (v : κ → A) (q : κ → A),
      (∀ i, IsStarProjection (q i)) ∧ (Pairwise fun i j => q i * q j = 0) ∧
      (∀ i, star (v i) * v i = q i) ∧ (∀ i, p * v i = v i) ∧
      cceil p = projSup (Set.range q) ∧
      OrthonormalFam (cornerSet A p) (fun i => M.tprod (v i) 1) := by
  classical
  obtain ⟨κ, e', hE, hpair, hsum⟩ := cceil_sum p (cornerSet.proj p)
  choose u hpi hu1 hu2 using fun i => (hE i).2.2
  have hproj : ∀ i, IsStarProjection (e' i) := fun i => (hE i).1
  have hps : star p = p := (cornerSet.proj p).isSelfAdjoint.star_eq
  have hφ0 : φ (0 : A) = 0 := Subtype.ext (by rw [hval]; simp)
  -- `u q = u`
  have huq : ∀ i, u i * e' i = u i := by
    intro i
    have hq2 : e' i * e' i = e' i := (hproj i).isIdempotentElem.eq
    have hqs : star (e' i) = e' i := (hproj i).isSelfAdjoint.star_eq
    refine sub_eq_zero.mp (pcorner_eq_zero_of_star_mul_self _ ?_)
    rw [star_sub, star_mul, hqs]
    calc (e' i * star (u i) - star (u i)) * (u i * e' i - u i)
        = e' i * (star (u i) * u i) * e' i - e' i * (star (u i) * u i)
          - (star (u i) * u i) * e' i + star (u i) * u i := by noncomm_ring
      _ = 0 := by rw [hu1]; noncomm_ring [hq2]
  -- `u u*` is a projection, hence `p u = u`
  have hqproj : ∀ i, IsStarProjection (u i * star (u i)) := by
    intro i
    refine ⟨?_, ?_⟩
    · show (u i * star (u i)) * (u i * star (u i)) = u i * star (u i)
      calc (u i * star (u i)) * (u i * star (u i))
          = u i * (star (u i) * u i) * star (u i) := by noncomm_ring
        _ = u i * e' i * star (u i) := by rw [hu1]
        _ = u i * star (u i) := by rw [huq]
    · show star (u i * star (u i)) = u i * star (u i)
      rw [star_mul, star_star]
  have huu : ∀ i, u i * star (u i) * u i = u i := by
    intro i; rw [mul_assoc, hu1, huq]
  have hpu : ∀ i, p * u i = u i := by
    intro i
    have h1 : p * (u i * star (u i)) = u i * star (u i) := by
      have h := ((hqproj i).le_iff_mul_eq_left (cornerSet.proj p)).mp (hu2 i)
      have h2 := congrArg star h
      rwa [star_mul, (hqproj i).isSelfAdjoint.star_eq, hps] at h2
    calc p * u i = p * (u i * star (u i) * u i) := by rw [huu]
      _ = (p * (u i * star (u i))) * u i := by noncomm_ring
      _ = u i := by rw [h1, huu]
  -- `uⱼ uᵢ* = 0` for `i ≠ j`
  have hcross : ∀ i j, i ≠ j → u j * star (u i) = 0 := by
    intro i j hij
    refine pcorner_eq_zero_of_star_mul_self _ ?_
    rw [star_mul, star_star]
    calc u i * star (u j) * (u j * star (u i))
        = u i * (star (u j) * u j) * star (u i) := by noncomm_ring
      _ = u i * e' j * star (u i) := by rw [hu1]
      _ = (u i * e' i) * e' j * star (u i) := by rw [huq]
      _ = u i * (e' i * e' j) * star (u i) := by noncomm_ring
      _ = 0 := by rw [hpair hij]; simp
  refine ⟨κ, u, e', hproj, hpair, hu1, hpu, hsum, ⟨?_, ?_⟩⟩
  · -- orthogonality
    intro i j hij
    show (inner (cornerSet A p) (M.tprod (u i) 1) (M.tprod (u j) 1)
      : cornerSet A p) = 0
    rw [M.inner_tprod, hcross i j hij, hφ0]
    simp
  · -- normalization
    intro i
    have hval' : (inner (cornerSet A p) (M.tprod (u i) 1) (M.tprod (u i) 1)
        : cornerSet A p).1 = u i * star (u i) := by
      have hup : star (u i) * p = star (u i) := by
        have h := congrArg star (hpu i)
        rwa [star_mul, hps] at h
      rw [M.inner_tprod]
      simp only [star_one, mul_one, one_mul, hval]
      calc p * (u i * star (u i)) * p = (p * u i) * (star (u i) * p) := by
            noncomm_ring
        _ = u i * star (u i) := by rw [hpu, hup]
    constructor
    · refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · show (inner (cornerSet A p) (M.tprod (u i) 1) (M.tprod (u i) 1) *
          inner (cornerSet A p) (M.tprod (u i) 1) (M.tprod (u i) 1)
            : cornerSet A p).1 = _
        rw [cornerSet.val_mul, hval', (hqproj i).isIdempotentElem.eq]
      · show (star (inner (cornerSet A p) (M.tprod (u i) 1) (M.tprod (u i) 1))
          : cornerSet A p).1 = _
        rw [cornerSet.val_star, hval', (hqproj i).isSelfAdjoint.star_eq]
    · intro h0
      have h1 : u i * star (u i) = 0 := by rw [← hval', h0]; rfl
      have h2 : u i = 0 := by
        have := huu i
        rw [h1] at this; simpa using this.symm
      exact (hE i).2.1 (by rw [← hu1 i, h2]; simp)


/-- The elementary tensors `a ⊗ 1` are ultranorm dense in `𝒜 ⊗_φ p𝒜p`.
`160IV`.2 (`hilbmod_projthm_2`) applied to `V = {a ⊗ 1}`, whose
orthocomplement is `{0}` by `paschkeModule_inner_tprod_separating`. -/
private theorem pcorner_unDense_tprod (x : M.X) (n : ℕ) (ωs : Fin n → NPFunctional (cornerSet A p))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ∀ i, unSeminorm (ωs i) (inner (cornerSet A p)) (x - M.tprod a 1) ≤ ε := by
  classical
  set V : Set M.X := {y : M.X | ∃ a : A, y = M.tprod a 1} with hVdef
  have hbspan : bSpan (cornerSet A p) V ⊆ V := by
    rintro y ⟨m, c, b, w, hw, rfl⟩
    have hstep : ∀ i, ∃ a : A, c i • b i • w i = M.tprod a 1 := by
      intro i
      obtain ⟨a, ha⟩ := hw i
      refine ⟨(b i).1 * (c i • a), ?_⟩
      rw [ha, M.compat.smul_action, mul_one, ← M.compat.smul_complex,
        pcorner_tprod_eq_one hval M (c i • a) (b i)]
    choose f hf using hstep
    refine ⟨∑ i, f i, ?_⟩
    rw [← pcorner_tprod_sum hval M]
    exact Finset.sum_congr rfl fun i _ => hf i
  have horth : orthoCompl (cornerSet A p) V ⊆ {0} := by
    intro w hw
    refine Set.mem_singleton_iff.mpr (paschkeModule_inner_tprod_separating φ M ?_)
    intro a b
    have h := hw (M.tprod (b.1 * a) 1) ⟨b.1 * a, rfl⟩
    rw [pcorner_tprod_eq_one hval M a b]
    have h2 := congrArg star h
    rwa [CStarModule.star_inner, star_zero] at h2
  have hx : x ∈ unClosure (cornerSet A p) (inner (cornerSet A p)) (bSpan (cornerSet A p) V) := by
    rw [← hilbmod_projthm_2 M.selfDual V]
    intro y hy
    have hy0 : y = 0 := horth hy
    rw [hy0]
    exact CStarModule.inner_zero_right
  obtain ⟨d, hd, hdle⟩ := hx n ωs ε hε
  obtain ⟨a, rfl⟩ := hbspan hd
  exact ⟨a, hdle⟩


/-- Subtraction in the first argument of `⊗`. -/
private theorem pcorner_tprod_sub (x y : A) (b : cornerSet A p) :
    M.tprod (x - y) b = M.tprod x b - M.tprod y b := by
  have h1 : M.tprod (x + -y) b = M.tprod x b + M.tprod (-y) b :=
    M.compat.add_left _ _ _
  have h2 : M.tprod (-y) b = -M.tprod y b := by
    have := M.compat.smul_complex (-1) y b
    simpa using this
  rw [sub_eq_add_neg, h1, h2, sub_eq_add_neg]

/-- The core convergence step of **171II**: `p a Qₛ ⊗ 1 → a ⊗ 1` ultranorm,
along the net of finite partial sums `Qₛ` of an orthogonal family of
projections with `⋁ᵢ qᵢ = ⌈⌈p⌉⌉`. -/
private theorem pcorner_untendsto_tprod_proj {κ : Type u} (q : κ → A)
    (hq : ∀ i, IsStarProjection (q i)) (hpair : Pairwise fun i j => q i * q j = 0)
    (hz : cceil p = projSup (Set.range q)) (a : A) :
    UnTendsto (inner (cornerSet A p))
      (fun s : Finset κ => M.tprod (p * a * ∑ i ∈ s, q i) 1) atTop
      (M.tprod a 1) := by
  classical
  set Q : Finset κ → A := fun s => ∑ i ∈ s, q i with hQdef
  have hzproj : IsStarProjection (cceil p) := (cceil_isLeast p).1.1
  have hzc : ∀ b : A, cceil p * b = b * cceil p := (cceil_isLeast p).1.2.1
  have hzp : cceil p * p = p := (cceil_isLeast p).1.2.2
  have hqz : ∀ i, q i ≤ cceil p := by
    intro i
    rw [hz]
    exact (projSup_spec (fun r hr => by obtain ⟨j, rfl⟩ := hr; exact hq j)).2.1
      _ ⟨i, rfl⟩
  have hQproj : ∀ s, IsStarProjection (Q s) := fun s =>
    isStarProjection_sum s q hq fun i _ j _ hij => hpair hij
  have hQz : ∀ s, Q s ≤ cceil p := by
    intro s
    refine ((hQproj s).le_iff_mul_eq_right hzproj).mpr ?_
    rw [hQdef]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => ((hq i).le_iff_mul_eq_right hzproj).mp (hqz i)
  have hQmono : Monotone Q := by
    intro s t hst
    exact Finset.sum_le_sum_of_subset_of_nonneg hst fun i _ _ => (hq i).nonneg
  -- `⋁ₛ Qₛ = z`
  have hlubA : IsLUB (Set.range Q) (cceil p) := by
    have hDproj : ∀ r ∈ Set.range Q, IsStarProjection r := by
      rintro _ ⟨s, rfl⟩; exact hQproj s
    have hdir : DirectedOn (· ≤ ·) (Set.range Q) := by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨Q (s ∪ t), ⟨s ∪ t, rfl⟩, hQmono Finset.subset_union_left,
        hQmono Finset.subset_union_right⟩
    have hps : projSup (Set.range Q) = cceil p := by
      refine projSup_eq hDproj hzproj (by rintro _ ⟨s, rfl⟩; exact hQz s) ?_
      intro r hr hub
      rw [hz]
      refine (projSup_spec (fun w hw => by obtain ⟨j, rfl⟩ := hw; exact hq j)).2.2
        r hr ?_
      rintro _ ⟨i, rfl⟩
      have := hub (Q {i}) ⟨{i}, rfl⟩
      simpa [hQdef] using this
    have := isLUB_projSup_of_directed (Set.range Q) hDproj ⟨Q ∅, ⟨∅, rfl⟩⟩ hdir
    rwa [hps] at this
  -- the seminorm estimate
  intro ω
  set ν : NPFunctional A := compNP (ncpPos φ) φ.preservesDirSups' ω with hνdef
  set μ : NPFunctional A := conjNP (star (p * a)) ν with hμdef
  have hμval : ∀ x : A, μ x = ω (φ (p * a * x * star (p * a))) := by
    intro x
    rw [hμdef, conjNP_apply, star_star]
    rfl
  -- the difference is `p a (Qₛ − z) ⊗ 1`
  have hdiff : ∀ s : Finset κ,
      M.tprod (p * a * Q s) 1 - M.tprod a 1 = M.tprod (p * a * (Q s - cceil p)) 1 := by
    intro s
    have hpaz : p * a * cceil p = p * a := by
      rw [mul_assoc, ← hzc a, ← mul_assoc]
      have : p * cceil p = p := by
        have h := congrArg star hzp
        rwa [star_mul, hzproj.isSelfAdjoint.star_eq,
          (cornerSet.proj p).isSelfAdjoint.star_eq] at h
      rw [this]
    rw [mul_sub, pcorner_tprod_sub hval M, hpaz, ← pcorner_tprod_p_left hval M]
  have hinner : ∀ s : Finset κ,
      (inner (cornerSet A p) (M.tprod (p * a * (Q s - cceil p)) 1)
        (M.tprod (p * a * (Q s - cceil p)) 1) : cornerSet A p)
        = φ (p * a * (cceil p - Q s) * star (p * a)) := by
    intro s
    rw [M.inner_tprod, star_one, mul_one, one_mul]
    congr 1
    have hsub : IsStarProjection (cceil p - Q s) :=
      projection_below_projection _ _ (hQproj s) hzproj (hQz s)
    have hss : (Q s - cceil p) * star (Q s - cceil p) = cceil p - Q s := by
      have h1 : star (Q s - cceil p) = -(cceil p - Q s) := by
        rw [star_sub, (hQproj s).isSelfAdjoint.star_eq, hzproj.isSelfAdjoint.star_eq]
        abel
      rw [h1]
      have h2 : Q s - cceil p = -(cceil p - Q s) := by abel
      rw [h2]
      simp only [neg_mul_neg]
      exact hsub.isIdempotentElem.eq
    calc p * a * (Q s - cceil p) * star (p * a * (Q s - cceil p))
        = p * a * ((Q s - cceil p) * star (Q s - cceil p)) * star (p * a) := by
          rw [star_mul]; noncomm_ring
      _ = p * a * (cceil p - Q s) * star (p * a) := by rw [hss]
  -- convergence of `μ(Qₛ) → μ(z)`
  have hre : Tendsto (fun s : Finset κ => (μ (Q s)).re) atTop (𝓝 ((μ (cceil p)).re)) := by
    set D : Set (selfAdjoint A) :=
      {d : selfAdjoint A | ∃ s : Finset κ, (d : A) = Q s} with hDdef
    have hDval : Subtype.val '' D = Set.range Q := by
      ext w
      constructor
      · rintro ⟨d, ⟨s, hs⟩, rfl⟩; exact ⟨s, hs.symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨⟨Q s, (hQproj s).isSelfAdjoint⟩, ⟨s, rfl⟩, rfl⟩
    have hzsa : IsSelfAdjoint (cceil p) := hzproj.isSelfAdjoint
    have hlubD : IsLUB D (⟨cceil p, hzsa⟩ : selfAdjoint A) := by
      refine isLUB_sa_of_isLUB ?_
      rw [hDval]
      exact hlubA
    have hne : D.Nonempty := ⟨⟨Q ∅, (hQproj ∅).isSelfAdjoint⟩, ⟨∅, rfl⟩⟩
    have hdirD : DirectedOn (· ≤ ·) D := by
      rintro d ⟨s, hs⟩ d' ⟨t, ht⟩
      refine ⟨⟨Q (s ∪ t), (hQproj _).isSelfAdjoint⟩, ⟨s ∪ t, rfl⟩, ?_, ?_⟩
      · show (d : A) ≤ Q (s ∪ t); rw [hs]; exact hQmono Finset.subset_union_left
      · show (d' : A) ≤ Q (s ∪ t); rw [ht]; exact hQmono Finset.subset_union_right
    have hIm := μ.preservesDirSups' D ⟨cceil p, hzsa⟩ hne hdirD hlubD
    have hreal : ∀ w ∈ (fun d : selfAdjoint A => (μ (d : A) : ℂ)) '' D, w.im = 0 := by
      rintro w ⟨d, -, rfl⟩
      exact npFunctional_im_eq_zero μ d.2
    have hlubRe := isLUB_re_of_isLUB hreal hIm
    have hrange : Complex.re '' ((fun d : selfAdjoint A => (μ (d : A) : ℂ)) '' D)
        = Set.range (fun s : Finset κ => (μ (Q s)).re) := by
      ext r
      constructor
      · rintro ⟨w, ⟨d, ⟨s, hs⟩, rfl⟩, rfl⟩
        refine ⟨s, ?_⟩
        show (μ (Q s)).re = (μ ((d : selfAdjoint A) : A)).re
        rw [hs]
      · rintro ⟨s, rfl⟩
        exact ⟨μ (Q s), ⟨⟨Q s, (hQproj s).isSelfAdjoint⟩, ⟨s, rfl⟩, rfl⟩, rfl⟩
    rw [hrange] at hlubRe
    refine tendsto_atTop_isLUB ?_ hlubRe
    intro s t hst
    have h := npFunctional_mono μ (hQmono hst)
    exact (Complex.le_def.mp h).1
  -- conclude
  have heq : ∀ s : Finset κ,
      unSeminorm ω (inner (cornerSet A p))
        (M.tprod (p * a * Q s) 1 - M.tprod a 1)
        = Real.sqrt ((μ (cceil p)).re - (μ (Q s)).re) := by
    intro s
    rw [hdiff s]
    show Real.sqrt (ω (inner (cornerSet A p) _ _)).re = _
    rw [hinner s]
    congr 1
    have h1 : μ (cceil p - Q s) = ω (φ (p * a * (cceil p - Q s) * star (p * a))) := hμval _
    have h2 : μ (cceil p - Q s) = μ (cceil p) - μ (Q s) := npFunctional_sub μ _ _
    rw [← h1, h2]
    simp
  have h0 : Tendsto (fun s : Finset κ => (μ (cceil p)).re - (μ (Q s)).re) atTop (𝓝 0) := by
    have := hre.const_sub ((μ (cceil p)).re)
    simpa using this
  have hfinal : Tendsto
      (fun s : Finset κ => Real.sqrt ((μ (cceil p)).re - (μ (Q s)).re)) atTop (𝓝 0) := by
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h1
    exact h1
  exact hfinal.congr fun s => (heq s).symm


/-- The family `(vᵢ ⊗ 1)` is an orthonormal *basis*. -/
private theorem pcorner_isONBasis_tprod {κ : Type u} (v : κ → A) (q : κ → A)
    (hq : ∀ i, IsStarProjection (q i)) (hpair : Pairwise fun i j => q i * q j = 0)
    (hvq : ∀ i, star (v i) * v i = q i) (hpv : ∀ i, p * v i = v i)
    (hz : cceil p = projSup (Set.range q))
    (hon : OrthonormalFam (cornerSet A p) (fun i => M.tprod (v i) 1)) :
    IsONBasis (cornerSet A p) (fun i => M.tprod (v i) 1) := by
  classical
  set e : κ → M.X := fun i => M.tprod (v i) 1 with hedef
  -- the partial sums on an elementary tensor
  have hpartial : ∀ (a : A) (s : Finset κ),
      ∑ i ∈ s, (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i
        = M.tprod (p * a * ∑ i ∈ s, q i) 1 := by
    intro a s
    have hterm : ∀ i : κ,
        (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i
          = M.tprod (p * a * q i) 1 := by
      intro i
      rw [hedef]
      show (inner (cornerSet A p) (M.tprod (v i) 1) (M.tprod a 1) : cornerSet A p)
        • M.tprod (v i) 1 = _
      rw [M.inner_tprod, star_one, mul_one, one_mul, M.compat.smul_action, mul_one,
        pcorner_tprod_eq_one hval M (v i) (φ (a * star (v i)))]
      congr 1
      show (φ (a * star (v i))).1 * v i = p * a * q i
      rw [hval]
      calc p * (a * star (v i)) * p * v i = p * a * (star (v i) * (p * v i)) := by
            noncomm_ring
        _ = p * a * (star (v i) * v i) := by rw [hpv]
        _ = p * a * q i := by rw [hvq]
    simp only [hterm]
    rw [pcorner_tprod_sum hval M, Finset.mul_sum]
  -- clause (a) on the elementary tensors
  have hbase : ∀ a : A, UnTendsto (inner (cornerSet A p))
      (fun s : Finset κ => ∑ i ∈ s, (inner (cornerSet A p) (e i) (M.tprod a 1)
        : cornerSet A p) • e i) atTop (M.tprod a 1) := by
    intro a
    have h := pcorner_untendsto_tprod_proj hval M q hq hpair hz a
    intro ω
    exact (h ω).congr fun s => by simp only [hpartial a s]
  -- `p_S` is a contraction for every `‖·‖_ω`
  have hcontr : ∀ (ω : NPFunctional (cornerSet A p)) (y : M.X) (s : Finset κ),
      unSeminorm ω (inner (cornerSet A p))
          (∑ i ∈ s, (inner (cornerSet A p) (e i) y : cornerSet A p) • e i)
        ≤ unSeminorm ω (inner (cornerSet A p)) y := by
    intro ω y s
    have hgram : (inner (cornerSet A p)
        (∑ i ∈ s, (inner (cornerSet A p) (e i) y : cornerSet A p) • e i)
        (∑ i ∈ s, (inner (cornerSet A p) (e i) y : cornerSet A p) • e i)
        : cornerSet A p)
        = ∑ i ∈ s, (inner (cornerSet A p) (e i) y : cornerSet A p)
            * star (inner (cornerSet A p) (e i) y) :=
      inner_sum_smul_self hon.1 _ (fun i => onbasis_coef_absorb hon y i) s
    have hbess := mod_bessel hon y s
    have hle : (inner (cornerSet A p)
        (∑ i ∈ s, (inner (cornerSet A p) (e i) y : cornerSet A p) • e i)
        (∑ i ∈ s, (inner (cornerSet A p) (e i) y : cornerSet A p) • e i)
        : cornerSet A p) ≤ inner (cornerSet A p) y y := by
      rw [hgram]
      refine le_trans (le_of_eq ?_) hbess
      exact Finset.sum_congr rfl fun i _ => by rw [CStarModule.star_inner]
    have hmono := npFunctional_mono ω hle
    have h1 := (Complex.le_def.mp hmono).1
    exact Real.sqrt_le_sqrt h1
  refine ⟨hon, fun x => ?_, fun b hb =>
    exists_unTendsto_of_l2Summable (bddUnComplete_of_selfDual M.selfDual) hon b hb⟩
  -- clause (a) in general, by an ε/3 argument
  intro ω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, ha⟩ := pcorner_unDense_tprod hval M x 1 (fun _ => ω) (ε / 3) (by linarith)
  have hxd : unSeminorm ω (inner (cornerSet A p)) (x - M.tprod a 1) ≤ ε / 3 := ha 0
  have hd := hbase a ω
  rw [Metric.tendsto_atTop] at hd
  obtain ⟨s₀, hs₀⟩ := hd (ε / 3) (by linarith)
  refine ⟨s₀, fun s hs => ?_⟩
  have hds : unSeminorm ω (inner (cornerSet A p))
      ((∑ i ∈ s, (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i)
        - M.tprod a 1) < ε / 3 := by
    have := hs₀ s hs
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (unSeminorm_nonneg _ _ _)] at this
  -- split `p_S x − x`
  have hsplit : (∑ i ∈ s, (inner (cornerSet A p) (e i) x : cornerSet A p) • e i) - x
      = (∑ i ∈ s, (inner (cornerSet A p) (e i) (x - M.tprod a 1) : cornerSet A p) • e i)
        + ((∑ i ∈ s, (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i)
            - M.tprod a 1) + (M.tprod a 1 - x) := by
    have hlin : ∀ i : κ, (inner (cornerSet A p) (e i) (x - M.tprod a 1) : cornerSet A p) • e i
        = (inner (cornerSet A p) (e i) x : cornerSet A p) • e i
          - (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i := by
      intro i
      rw [CStarModule.inner_sub_right]
      have h := op_add_smul ((inner (cornerSet A p) (e i) x : cornerSet A p)
        - inner (cornerSet A p) (e i) (M.tprod a 1))
        (inner (cornerSet A p) (e i) (M.tprod a 1)) (e i)
      rw [sub_add_cancel] at h
      rw [h]; abel
    simp only [hlin, Finset.sum_sub_distrib]
    abel
  have hneg : unSeminorm ω (inner (cornerSet A p)) (M.tprod a 1 - x)
      = unSeminorm ω (inner (cornerSet A p)) (x - M.tprod a 1) := by
    have h : (M.tprod a 1 - x) = -(x - M.tprod a 1) := by abel
    rw [h]
    show Real.sqrt (ω (inner (cornerSet A p) _ _)).re = _
    congr 2
    rw [CStarModule.inner_neg_left, CStarModule.inner_neg_right, neg_neg]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (unSeminorm_nonneg _ _ _), hsplit]
  have ht1 := unSeminorm_add_le ω (cstarBInner (cornerSet A p) M.X)
    ((∑ i ∈ s, (inner (cornerSet A p) (e i) (x - M.tprod a 1) : cornerSet A p) • e i)
      + ((∑ i ∈ s, (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i)
          - M.tprod a 1)) (M.tprod a 1 - x)
  have ht2 := unSeminorm_add_le ω (cstarBInner (cornerSet A p) M.X)
    (∑ i ∈ s, (inner (cornerSet A p) (e i) (x - M.tprod a 1) : cornerSet A p) • e i)
    ((∑ i ∈ s, (inner (cornerSet A p) (e i) (M.tprod a 1) : cornerSet A p) • e i)
      - M.tprod a 1)
  have ht3 := hcontr ω (x - M.tprod a 1) s
  have hBI : (cstarBInner (cornerSet A p) M.X).inner
      = (inner (cornerSet A p) : M.X → M.X → cornerSet A p) := rfl
  rw [hBI] at ht1 ht2
  rw [hneg] at ht1
  linarith


/-- `a ⊗ 1 = 0` iff `pa = 0`. -/
private theorem pcorner_tprod_eq_zero_iff (y : A) : M.tprod y 1 = 0 ↔ p * y = 0 := by
  rw [← CStarModule.inner_self (A := cornerSet A p) (x := M.tprod y 1)]
  rw [M.inner_tprod, star_one, mul_one, one_mul]
  constructor
  · intro h
    have h1 : p * y * star (p * y) = 0 := by
      have h2 : (φ (y * star y)).1 = 0 := by rw [h]; rfl
      rw [hval] at h2
      calc p * y * star (p * y) = p * (y * star y) * p := by
            rw [star_mul, (cornerSet.proj p).isSelfAdjoint.star_eq]; noncomm_ring
        _ = 0 := h2
    have h3 : star (star (p * y)) * star (p * y) = 0 := by rwa [star_star]
    exact star_eq_zero.mp (pcorner_eq_zero_of_star_mul_self _ h3)
  · intro h
    refine Subtype.ext ?_
    rw [hval]
    calc p * (y * star y) * p = (p * y) * star (p * y) := by
          rw [star_mul, (cornerSet.proj p).isSelfAdjoint.star_eq]; noncomm_ring
      _ = 0 := by rw [h]; simp

/-- The kernel of `ϱ`, computed on the module: `ϱ(a) = 0` iff `p x a = 0`
for every `x`. -/
private theorem pcorner_rho_eq_zero_iff (a : A) : M.ρ a = 0 ↔ ∀ x : A, p * x * a = 0 := by
  constructor
  · intro h x
    have h1 : (M.ρ a).unop.1 (M.tprod x 1) = 0 := by
      rw [h]; rfl
    rw [M.ρ_tprod] at h1
    have h2 := (pcorner_tprod_eq_zero_iff hval M (x * a)).mp h1
    rw [← mul_assoc] at h2
    exact h2
  · intro h
    have hba : (M.ρ a).unop = 0 := by
      refine paschkeModule_ba_ext φ M fun x b => ?_
      show (M.ρ a).unop.1 (M.tprod x b) = (0 : Ba (cornerSet A p) M.X).1 _
      rw [M.ρ_tprod, pcorner_tprod_eq_one hval M (x * a) b]
      have : p * (b.1 * (x * a)) = 0 := by
        have h1 := h (b.1 * x)
        calc p * (b.1 * (x * a)) = p * (b.1 * x) * a := by noncomm_ring
          _ = 0 := h1
      rw [(pcorner_tprod_eq_zero_iff hval M _).mpr this]
      rfl
    have := congrArg MulOpposite.op hba
    simpa using this

/-- `p x a = 0` for all `x` iff `⌈⌈p⌉⌉ a = 0`: the central carrier computed
through **68I** `cceil_fundamental`. -/
private theorem pcorner_forall_mul_eq_zero_iff (a : A) :
    (∀ x : A, p * x * a = 0) ↔ cceil p * a = 0 := by
  have hzproj : IsStarProjection (cceil p) := (cceil_isLeast p).1.1
  have hzc : ∀ b : A, cceil p * b = b * cceil p := (cceil_isLeast p).1.2.1
  have hzp : cceil p * p = p := (cceil_isLeast p).1.2.2
  have hzs : star (cceil p) = cceil p := hzproj.isSelfAdjoint.star_eq
  constructor
  · intro h
    set b : A := a * star a with hbdef
    have hb0 : 0 ≤ b := mul_star_self_nonneg a
    have hbsa : star b = b := by rw [hbdef, star_mul, star_star]
    have hcb : IsStarProjection (ceil b) := (ceil_spec hb0).1
    have hcbs : star (ceil b) = ceil b := hcb.isSelfAdjoint.star_eq
    have hcbb : ceil b * b = b := by
      have h1 := (ceil_spec hb0).2.1
      have h2 := congrArg star h1
      rwa [star_mul, hcbs, hbsa] at h2
    have hps : star p = p := (cornerSet.proj p).isSelfAdjoint.star_eq
    have husa : ∀ x : A, star (star x * p * x) = star x * p * x := by
      intro x
      rw [star_mul, star_mul, star_star, hps]
      noncomm_ring
    have hnn : ∀ x : A, 0 ≤ star x * p * x := fun x =>
      star_left_conjugate_nonneg (cornerSet.proj p).nonneg x
    have hstep : ∀ x : A, (star x * p * x) * ceil b = 0 := by
      intro x
      have h1 : (star x * p * x) * b = 0 := by
        rw [hbdef]
        calc star x * p * x * (a * star a) = star x * (p * x * a) * star a := by
              noncomm_ring
          _ = 0 := by rw [h x]; simp
      have h2 : b * (star x * p * x) = 0 := by
        have h3 := congrArg star h1
        rwa [star_mul, husa x, hbsa, star_zero] at h3
      have h4 : ceil b * (star x * p * x) = 0 := ceil_mul_eq_zero hb0 h2
      have h5 := congrArg star h4
      rwa [star_mul, husa x, hcbs, star_zero] at h5
    have hproj : ∀ r ∈ {x : A | ∃ y : A, x = ceil (star y * p * y)},
        IsStarProjection r := by
      rintro _ ⟨y, rfl⟩
      exact (ceil_spec (hnn y)).1
    have hub : ∀ r ∈ {x : A | ∃ y : A, x = ceil (star y * p * y)}, r ≤ 1 - ceil b := by
      rintro _ ⟨y, rfl⟩
      refine (ceil_le_iff (hnn y) hcb.one_sub).mpr ?_
      rw [mul_sub, mul_one, hstep y, sub_zero]
    have hzle : cceil p ≤ 1 - ceil b := by
      rw [(cceil_fundamental p (cornerSet.proj p)).2]
      exact (projSup_spec hproj).2.2 _ hcb.one_sub hub
    have hzcb : cceil p * ceil b = 0 := by
      have h1 := (hzproj.le_iff_mul_eq_right hcb.one_sub).mp hzle
      rw [sub_mul, one_mul] at h1
      have h2 : ceil b * cceil p = 0 := sub_eq_self.mp h1
      have h3 := congrArg star h2
      rwa [star_mul, hzs, hcbs, star_zero] at h3
    have hzb : cceil p * b = 0 := by
      calc cceil p * b = cceil p * (ceil b * b) := by rw [hcbb]
        _ = (cceil p * ceil b) * b := by noncomm_ring
        _ = 0 := by rw [hzcb]; simp
    refine star_eq_zero.mp (pcorner_eq_zero_of_star_mul_self _ ?_)
    rw [star_star]
    calc cceil p * a * star (cceil p * a)
        = cceil p * (a * star a) * cceil p := by
          rw [star_mul, hzs]; noncomm_ring
      _ = 0 := by rw [← hbdef, hzb]; simp
  · intro h x
    calc p * x * a = cceil p * p * x * a := by rw [hzp]
      _ = p * x * (cceil p * a) := by
          rw [hzc p, mul_assoc p (cceil p) x, hzc x]; noncomm_ring
      _ = 0 := by rw [h]; simp



/-! ### `ϱ` is surjective, with kernel `⌈⌈p⌉⌉^⊥𝒜`

`|a ⊗ 1⟩⟨b ⊗ 1| = ϱ(b* p a)`, the basis of **159IV** consists of elementary
tensors, and the range of `ϱ` is ultraweakly closed (**48VI**.1 applied to
the injective corestriction `σ : ⌈⌈p⌉⌉𝒜 → 𝒷ᵃ(𝒜 ⊗_{h_p} p𝒜p)ᵐᵒᵖ`, plus
**73IX** `vnsac`).  This is the thesis's "`ϱ₀` is surjective and
`⌈ϱ₀⌉ = ⌈⌈p⌉⌉`", without `𝒜p`. -/

/-- The corestriction of `ϱ` to `⌈⌈p⌉⌉𝒜`: an **injective** nmiu-map with the
same range. -/
private noncomputable def pcorner_sigma (hv : ∀ a : A, (φ a).1 = p * a * p)
    (Mm : PaschkeModule φ) :
    NMIUMap (cornerSet A (cceil p)) (Ba (cornerSet A p) Mm.X)ᵐᵒᵖ where
  toStarAlgHom :=
    { toFun := fun c => Mm.ρ c.1
      map_one' := by
        have h0 : Mm.ρ (1 - cceil p) = 0 := by
          refine (pcorner_rho_eq_zero_iff hv Mm _).mpr ?_
          refine (pcorner_forall_mul_eq_zero_iff hv _).mpr ?_
          rw [mul_sub, mul_one, (cceil_isLeast p).1.1.isIdempotentElem.eq, sub_self]
        have h1 : Mm.ρ (1 - cceil p) = Mm.ρ 1 - Mm.ρ (cceil p) :=
          map_sub Mm.ρ.toStarAlgHom 1 (cceil p)
        have h2 : Mm.ρ (1 : A) = 1 := map_one Mm.ρ.toStarAlgHom
        rw [h1, h2] at h0
        show Mm.ρ (cceil p) = 1
        have := sub_eq_zero.mp h0
        exact this.symm
      map_mul' := fun c d => map_mul Mm.ρ.toStarAlgHom c.1 d.1
      map_zero' := map_zero Mm.ρ.toStarAlgHom
      map_add' := fun c d => map_add Mm.ρ.toStarAlgHom c.1 d.1
      commutes' := fun r => by
        have h0 : Mm.ρ (1 - cceil p) = 0 := by
          refine (pcorner_rho_eq_zero_iff hv Mm _).mpr ?_
          refine (pcorner_forall_mul_eq_zero_iff hv _).mpr ?_
          rw [mul_sub, mul_one, (cceil_isLeast p).1.1.isIdempotentElem.eq, sub_self]
        have hone : Mm.ρ (cceil p) = 1 := by
          have h1 : Mm.ρ (1 - cceil p) = Mm.ρ 1 - Mm.ρ (cceil p) :=
            map_sub Mm.ρ.toStarAlgHom 1 (cceil p)
          have h2 : Mm.ρ (1 : A) = 1 := map_one Mm.ρ.toStarAlgHom
          rw [h1, h2] at h0
          exact (sub_eq_zero.mp h0).symm
        show Mm.ρ ((algebraMap ℂ (cornerSet A (cceil p)) r).1) = algebraMap ℂ _ r
        have h3 : (algebraMap ℂ (cornerSet A (cceil p)) r).1 = r • cceil p := by
          rw [Algebra.algebraMap_eq_smul_one r]; rfl
        have h4 : Mm.ρ (r • cceil p) = r • Mm.ρ (cceil p) :=
          map_smul Mm.ρ.toStarAlgHom r (cceil p)
        rw [h3, h4, hone, Algebra.algebraMap_eq_smul_one r]
      map_star' := fun c => map_star Mm.ρ.toStarAlgHom c.1 }
  preservesDirSups' := by
    have hval' : ∀ c : cornerSet A (cceil p), (c : cornerSet A (cceil p)).1
        = (c : cornerSet A (cceil p)).1 := fun _ => rfl
    set valP : cornerSet A (cceil p) →ₚ[ℂ] A :=
      { toFun := fun c => c.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        monotone' := fun _ _ h => h } with hvalP
    exact preservesDirSups_pmap_comp valP (pcorner_val_normal (cceil_isLeast p).1.2.1)
      (starAlgHomP Mm.ρ.toStarAlgHom) Mm.ρ.preservesDirSups'

private theorem pcorner_sigma_apply (c : cornerSet A (cceil p)) :
    pcorner_sigma hval M c = M.ρ c.1 := rfl

private theorem pcorner_sigma_injective :
    Function.Injective ⇑(pcorner_sigma hval M) := by
  have hzc : ∀ b : A, cceil p * b = b * cceil p := (cceil_isLeast p).1.2.1
  intro c d hcd
  have h0 : M.ρ (c.1 - d.1) = 0 := by
    have hsub : M.ρ (c.1 - d.1) = M.ρ c.1 - M.ρ d.1 :=
      map_sub M.ρ.toStarAlgHom c.1 d.1
    have h1 : M.ρ c.1 = M.ρ d.1 := hcd
    rw [hsub, h1, sub_self]
  have h2 : cceil p * (c.1 - d.1) = 0 :=
    (pcorner_forall_mul_eq_zero_iff hval _).mp
      ((pcorner_rho_eq_zero_iff hval M _).mp h0)
  refine Subtype.ext ?_
  have h3 : cceil p * (c.1 - d.1) * cceil p = c.1 - d.1 := by
    have hc' : cceil p * c.1 * cceil p = c.1 := c.2
    have hd' : cceil p * d.1 * cceil p = d.1 := d.2
    rw [mul_sub, sub_mul, hc', hd']
  have h4 : c.1 - d.1 = 0 := by rw [← h3, h2, zero_mul]
  exact sub_eq_zero.mp h4

/-- `ϱ(⌈⌈p⌉⌉a⌈⌈p⌉⌉) = ϱ(a)`: the kernel computation
`pcorner_forall_mul_eq_zero_iff` says `ϱ` kills `a − ⌈⌈p⌉⌉a⌈⌈p⌉⌉`.  This is
`σ ∘ h_{⌈⌈p⌉⌉} = ϱ`, and with `pcorner_rho_surjective` also the surjectivity
of `σ`. -/
private theorem pcorner_rho_cceil (a : A) :
    M.ρ (cceil p * a * cceil p) = M.ρ a := by
  have hzz : cceil p * cceil p = cceil p := (cceil_isLeast p).1.1.isIdempotentElem.eq
  have hzc : ∀ b : A, cceil p * b = b * cceil p := (cceil_isLeast p).1.2.1
  have h0 : M.ρ (a - cceil p * a * cceil p) = 0 := by
    refine (pcorner_rho_eq_zero_iff hval M _).mpr ?_
    refine (pcorner_forall_mul_eq_zero_iff hval _).mpr ?_
    rw [mul_sub]
    have h1 : cceil p * (cceil p * a * cceil p) = cceil p * a := by
      calc cceil p * (cceil p * a * cceil p)
          = (cceil p * cceil p) * a * cceil p := by noncomm_ring
        _ = cceil p * a * cceil p := by rw [hzz]
        _ = cceil p * (cceil p * a) := by rw [mul_assoc, ← hzc a]
        _ = (cceil p * cceil p) * a := by noncomm_ring
        _ = cceil p * a := by rw [hzz]
    rw [h1, sub_self]
  have hsub : M.ρ (a - cceil p * a * cceil p)
      = M.ρ a - M.ρ (cceil p * a * cceil p) :=
    map_sub M.ρ.toStarAlgHom a (cceil p * a * cceil p)
  rw [hsub] at h0
  exact (sub_eq_zero.mp h0).symm

/-- `σ ∘ h_{⌈⌈p⌉⌉} = ϱ`. -/
private theorem pcorner_sigma_centralCorner (a : A) :
    pcorner_sigma hval M (pcorner_centralCorner (cceil_isLeast p).1.2.1 a)
      = M.ρ a :=
  pcorner_rho_cceil hval M a

/-- **171II**, step 3: `ϱ` is surjective. -/
private theorem pcorner_rho_surjective : Function.Surjective ⇑M.ρ := by
  classical
  letI : VonNeumannAlgebra (cornerSet A (cceil p)) :=
    cornerSet_vonNeumannAlgebra A (cceil p)
  letI : VonNeumannAlgebra (Ba (cornerSet A p) M.X) := ba_vonNeumannAlgebra M.selfDual
  obtain ⟨κ, v, q, hq, hpair, hvq, hpv, hz, hon⟩ := pcorner_onb_data hval M
  have hbasis := pcorner_isONBasis_tprod hval M v q hq hpair hvq hpv hz hon
  set e : κ → M.X := fun i => M.tprod (v i) 1 with hedef
  set σ := pcorner_sigma hval M with hσdef
  have hVN := injective_nmiu_iso_on_image_1 σ (pcorner_sigma_injective hval M)
  have hclosed := (vnsac _ hVN).2
  -- the range of `ϱ` and of `σ` agree
  have hrange : ∀ a : A, M.ρ a ∈ σ.toStarAlgHom.range := fun a =>
    ⟨pcorner_centralCorner (cceil_isLeast p).1.2.1 a,
      pcorner_sigma_centralCorner hval M a⟩
  intro T
  obtain ⟨approx, hspan, htend⟩ :=
    ketbra_ultraweakly_dense M.selfDual e hbasis T.unop
  -- the generators of `159IV` lie in the range
  have hgen : ∀ S : Ba (cornerSet A p) M.X,
      (∃ (i j : κ) (b : cornerSet A p), S.1 = mketbra (cornerSet A p) (b • e i) (e j)) →
      MulOpposite.op S ∈ σ.toStarAlgHom.range := by
    rintro S ⟨i, j, b, hS⟩
    have hbe : b • e i = M.tprod (b.1 * v i) 1 := by
      rw [hedef]
      show b • M.tprod (v i) 1 = _
      rw [M.compat.smul_action, mul_one, pcorner_tprod_eq_one hval M (v i) b]
    have hSeq : S = mketbraBa (M.tprod (b.1 * v i) 1) (M.tprod (v j) 1) := by
      refine Subtype.ext ?_
      rw [hS, hbe]
      rfl
    have hk := pcorner_mketbra_tprod hval M (b.1 * v i) (v j)
    rw [hSeq, hk]
    have := hrange (star (v j) * p * (b.1 * v i))
    simpa using this
  -- the preimage of the range is a submodule containing them
  set R : Submodule ℂ (Ba (cornerSet A p) M.X) :=
    { carrier := {S | MulOpposite.op S ∈ σ.toStarAlgHom.range}
      zero_mem' := by
        have h : MulOpposite.op (0 : Ba (cornerSet A p) M.X)
            ∈ σ.toStarAlgHom.range := by
          simpa using (σ.toStarAlgHom.range).zero_mem
        exact h
      add_mem' := by
        intro x y hx hy
        have h : MulOpposite.op (x + y) ∈ σ.toStarAlgHom.range := by
          rw [MulOpposite.op_add]
          exact Subalgebra.add_mem _ hx hy
        exact h
      smul_mem' := by
        intro r x hx
        have h : MulOpposite.op (r • x) ∈ σ.toStarAlgHom.range := by
          rw [MulOpposite.op_smul]
          exact Subalgebra.smul_mem _ hx r
        exact h } with hRdef
  have hle : Submodule.span ℂ
      {S : Ba (cornerSet A p) M.X |
        ∃ (i j : κ) (b : cornerSet A p), S.1 = mketbra (cornerSet A p) (b • e i) (e j)} ≤ R := by
    refine Submodule.span_le.mpr ?_
    rintro S hS
    exact hgen S hS
  have hmem : ∀ s : Finset κ, MulOpposite.op (approx s) ∈ σ.toStarAlgHom.range :=
    fun s => hle (hspan s)
  have htend' : UWTendsto (fun s : Finset κ => MulOpposite.op (approx s)) atTop T := by
    have := pcorner_uwTendsto_op approx T.unop htend
    simpa using this
  letI : TopologicalSpace ((Ba (cornerSet A p) M.X)ᵐᵒᵖ) :=
    ultraweak ((Ba (cornerSet A p) M.X)ᵐᵒᵖ)
  have hTmem : T ∈ (σ.toStarAlgHom.range : Set ((Ba (cornerSet A p) M.X)ᵐᵒᵖ)) :=
    hclosed.mem_of_tendsto htend' (Filter.Eventually.of_forall hmem)
  obtain ⟨c, hc⟩ := hTmem
  exact ⟨c.1, hc⟩

/-- `σ` is bijective: injective by `pcorner_sigma_injective`, surjective
because it has the same range as `ϱ` (`pcorner_sigma_centralCorner`), which
is everything. -/
private theorem pcorner_sigma_bijective :
    Function.Bijective ⇑(pcorner_sigma hval M) := by
  refine ⟨pcorner_sigma_injective hval M, fun T => ?_⟩
  obtain ⟨a, ha⟩ := pcorner_rho_surjective hval M T
  exact ⟨pcorner_centralCorner (cceil_isLeast p).1.2.1 a,
    (pcorner_sigma_centralCorner hval M a).trans ha⟩

end PaschkeCornerAux

/-! ### Infrastructure for **172X**: from an abstract corner to a standard one

`IsPureMap` gives an *abstract* corner `h : A → C`; the thesis's proof of
172X runs through proc.tex 100III `pure-fundamental`, which hands it the
*standard* corner `h_p` directly.  The gap is closed by **169IV**: `h_p` for
`p = ⌊a⌋` is a corner for the same effect `a`, so the two universal
properties produce mutually inverse ncp-maps `u`, `v` between `C` and `pAp`
with `v ∘ h_p = h` (`pext_corner_iso`).  `v` is an ncp-*isomorphism* but
**not** unital in general (QUESTIONS **D7**: `λ·h_p` is again a corner under
**169II** as printed), which is why the Paschke dilation is transported along
`v` at the level of the *dilating triple* (`pext_dilation_target_iso`) rather
than by claiming that `c ∘ v` is again a filter — the latter is exactly the
step that D7 puts in doubt. -/

/-- The identity as an ncp-map (`ncpId`, in the existential form the
universal properties below consume). -/
private theorem pext_exists_ncpId (P : Type*) [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] : ∃ f : NCPMap P P, ∀ a : P, f a = a :=
  ⟨ncpId P, fun _ => rfl⟩

/-- **169IV** + the universal property of **169II**: a corner `h` for `a` is
the standard corner `h_{⌊a⌋}` followed by an ncp-isomorphism `v`. -/
private theorem pext_corner_iso {P C : Type u} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] [VonNeumannAlgebra P] [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (h : NCPMap P C) (a : P) (hc : IsCornerFor h a) :
    ∃ (hp : NCPMap P (cornerSet P (floor a)))
      (v : NCPMap (cornerSet P (floor a)) C)
      (u : NCPMap C (cornerSet P (floor a))),
      (∀ b : P, (hp b).1 = floor a * b * floor a) ∧
      (∀ x : P, v (hp x) = h x) ∧
      (∀ y : C, v (u y) = y) ∧ ∀ z : cornerSet P (floor a), u (v z) = z := by
  obtain ⟨hp, hval, hpc⟩ := standard_corner_dils a hc.1
  obtain ⟨v, hv, -⟩ :=
    hpc.2.2 C inferInstance inferInstance inferInstance h hc.2.1
  obtain ⟨u, hu, -⟩ :=
    hc.2.2 (cornerSet P (floor a)) inferInstance inferInstance inferInstance hp
      hpc.2.1
  refine ⟨hp, v, u, hval, hv, ?_, ?_⟩
  · -- `v ∘ u = id`, both mediating `h` through `h`
    obtain ⟨w, hw⟩ := exists_ncpComp v u
    obtain ⟨idm, hidm⟩ := pext_exists_ncpId C
    obtain ⟨w₀, -, huniq⟩ := hc.2.2 C inferInstance inferInstance inferInstance h hc.2.1
    have h1 : w = idm := (huniq w fun x => by rw [hw, hu, hv]).trans
      (huniq idm fun x => by rw [hidm]).symm
    intro y
    have := DFunLike.congr_fun h1 y
    rw [hw, hidm] at this
    exact this
  · -- `u ∘ v = id`, both mediating `h_p` through `h_p`
    obtain ⟨w, hw⟩ := exists_ncpComp u v
    obtain ⟨idm, hidm⟩ := pext_exists_ncpId (cornerSet P (floor a))
    obtain ⟨w₀, -, huniq⟩ := hpc.2.2 (cornerSet P (floor a)) inferInstance
      inferInstance inferInstance hp hpc.2.1
    have h1 : w = idm := (huniq w fun x => by rw [hw, hv, hu]).trans
      (huniq idm fun x => by rw [hidm]).symm
    intro z
    have := DFunLike.congr_fun h1 z
    rw [hw, hidm] at this
    exact this

/-- A Paschke dilation stays one when its `h`-leg is post-composed with an
ncp-isomorphism of the target: mediate through `u ∘ h'` and use `v ∘ u = id`
both ways.  (No unitality of `u`, `v` is needed.) -/
private theorem pext_dilation_target_iso {P B₁ B₂ : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra B₁] [PartialOrder B₁]
    [StarOrderedRing B₁] [CStarAlgebra B₂] [PartialOrder B₂] [StarOrderedRing B₂]
    (ψ : P → B₁) (D : PaschkeTriple P B₁) (hD : IsPaschkeDilationOf D ψ)
    (v : NCPMap B₁ B₂) (u : NCPMap B₂ B₁) (hvu : ∀ y : B₂, v (u y) = y)
    (huv : ∀ z : B₁, u (v z) = z) (H : NCPMap D.P B₂)
    (hH : ∀ x : D.P, H x = v (D.h x)) :
    IsPaschkeDilationOf ⟨D.P, D.vn, D.ρ, H⟩ fun x => v (ψ x) := by
  refine ⟨fun x => ?_, fun D' hD' => ?_⟩
  · show (H (D.ρ x) : B₂) = v (ψ x)
    rw [hH, hD.1 x]
  obtain ⟨k, hk⟩ := exists_ncpComp u D'.h
  have hk1 : ∀ x : P, (k (D'.ρ x) : B₁) = ψ x := by
    intro x
    rw [hk, hD' x, huv]
  obtain ⟨σ, ⟨hσρ, hσh⟩, hσuniq⟩ := hD.2 ⟨D'.P, D'.vn, D'.ρ, k⟩ hk1
  refine ⟨σ, ⟨hσρ, fun c => ?_⟩, fun σ' hσ' => ?_⟩
  · show (H (σ c) : B₂) = D'.h c
    rw [hH, hσh c]
    show (v (k c) : B₂) = D'.h c
    rw [hk, hvu]
  · refine hσuniq σ' ⟨hσ'.1, fun c => ?_⟩
    show (D.h (σ' c) : B₁) = k c
    have h1 : (H (σ' c) : B₂) = D'.h c := hσ'.2 c
    rw [hH] at h1
    rw [hk, ← h1, huv]


/-! ## Parsec 1710: purity via the Paschke dilation

**171I** (dils.tex:6240): introduction; **171III**–**171VI** and
**171VIII** are proofs — not converted. -/

section PaschkePure

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **171II** (`paschke-corner`, dils.tex:6245, Theorem): for a projection
`p` in a von Neumann algebra `A`, a Paschke dilation of the standard
corner `h_p : A → pAp` is `(⌈⌈p⌉⌉A, h_{⌈⌈p⌉⌉}, h'_p)`, where `⌈⌈p⌉⌉` is
the central carrier of `p`, `h_{⌈⌈p⌉⌉}` the standard corner for `⌈⌈p⌉⌉`,
and `h'_p` the restriction of `h_p` to `⌈⌈p⌉⌉A`.

The hypothesis `IsStarProjection p` of the thesis is carried as an instance
`[Fact (IsStarProjection p)]`, which is what the corner `pAp` needs to be an
algebra at all (see `cornerSet.instCStarAlgebra`).  That `⌈⌈p⌉⌉` is a
projection too is **68III**, now proved in `Theses.A.VN.Projections`, so it
is supplied by `fact_isStarProjection_cceil` rather than assumed.

**Proof.**  The thesis (dils.tex:6237) argues in three steps: `𝒜p` is a
self-dual Hilbert `p𝒜p`-module; `𝒜 ⊗_{h_p} p𝒜p ≅ 𝒜p`; and
`𝒷ᵃ(𝒜p) ≅ ⌈⌈p⌉⌉𝒜`.  Steps 1 and 2 exist only to transport an orthonormal
basis and the ketbra calculus into a concrete model, and are **not needed**:
inside the abstract `PaschkeModule` of **154III** every elementary tensor is
already of the form `a ⊗ 1` (`pcorner_tprod_eq_one`), the thesis's own basis
transports as `(uᵢ ⊗ 1)ᵢ` (`pcorner_isONBasis_tprod`), and
`|a ⊗ 1⟩⟨b ⊗ 1| = ϱ(b*pa)` (`pcorner_mketbra_tprod`) — whence
`pcorner_rho_surjective`, step 3, with `⌈ϱ⌉ = ⌈⌈p⌉⌉`
(`pcorner_forall_mul_eq_zero_iff`).  So the corestriction
`σ : ⌈⌈p⌉⌉𝒜 → 𝒷ᵃ(𝒜 ⊗_{h_p} p𝒜p)ᵐᵒᵖ` is a *bijective* nmiu-map with
`σ ∘ h_{⌈⌈p⌉⌉} = ϱ` and `h ∘ σ = h'_p`, and `pcorner_transport` carries the
Paschke dilation of **154III**.5 across it.  See PROVING-LOG sessions 67–68;
the divergence (steps 1 and 2 can be dropped) is recorded there. -/
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
          ρ, h⟩ ⇑hp' := by
  classical
  letI : VonNeumannAlgebra (cornerSet A p) := cornerSet_vonNeumannAlgebra A p
  letI : VonNeumannAlgebra (cornerSet A (cceil p)) :=
    cornerSet_vonNeumannAlgebra A (cceil p)
  obtain ⟨M⟩ := existence_paschke hp'
  obtain ⟨incl, hincl⟩ :=
    pcorner_exists_inclNcp (z := cceil p) (cceil_isLeast p).1.2.1
  obtain ⟨h', hh'⟩ := exists_ncpComp hp' incl
  refine ⟨pcorner_centralCorner (cceil_isLeast p).1.2.1, h', fun _ => rfl,
    fun c => ?_, ?_⟩
  · rw [hh', hincl]
    exact hval c.1
  · refine pcorner_transport ⇑hp' _ _ (existence_paschke_5 hp' M)
      (pcorner_sigma hval M) (pcorner_sigma_bijective hval M)
      (fun a => pcorner_sigma_centralCorner hval M a) (fun c => ?_)
    show M.h (M.ρ c.1) = h' c
    rw [paschkeModule_h_ρ, hh', hincl]

/-- Auxiliary for **171VII** ⇐: **corners compose**.  If `h₁` is a corner
for `a₁` and *unital*, `h₂` a corner for `a₂`, and `e ≤ a₁` an effect with
`h₁(e) = a₂`, then `h₂ ∘ h₁` is a corner for `e`.

(The thesis takes this for granted — dils.tex **170I** *defines* pure maps
as arbitrary composites of filters and corners, and appeals to proc.tex
100III `pure-fundamental` to bring them to the normal form "filter after
corner" used by `IsPureMap`.  100III is proved and reachable as
`Theses.A.Proc.pure_fundamental`, but for *its* corner/filter/pure
predicates, which are not these (file header); in the case needed for 171VII
the first corner is a surjective nmiu-map, so the elementary argument below
suffices and no normal-form theorem is needed.) -/
private theorem isCornerFor_comp {P Q R : Type u} [CStarAlgebra P]
    [PartialOrder P] [StarOrderedRing P] [CStarAlgebra Q] [PartialOrder Q]
    [StarOrderedRing Q] [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    (h₁ : NCPMap P Q) (a₁ : P) (hc₁ : IsCornerFor h₁ a₁) (hu₁ : (h₁ 1 : Q) = 1)
    (h₂ : NCPMap Q R) (a₂ : Q) (hc₂ : IsCornerFor h₂ a₂)
    (e : P) (he : e ∈ effects P) (hea : e ≤ a₁) (h1e : (h₁ e : Q) = a₂)
    (k : NCPMap P R) (hk : ∀ x : P, k x = h₂ (h₁ x)) :
    IsCornerFor k e := by
  refine ⟨he, ?_, ?_⟩
  · rw [hk, hk, h1e, hu₁, hc₂.2.1]
  intro C _ _ _ f hf
  -- `f(e) = f(1)` forces `f(a₁) = f(1)`, so `f` factors through `h₁`
  have hfmono : ∀ {x y : P}, x ≤ y → (f x : C) ≤ f y := fun h => (ncpPos f).monotone h
  have hfa₁ : (f a₁ : C) = f 1 := by
    refine le_antisymm (hfmono hc₁.1.2) ?_
    rw [← hf]
    exact hfmono hea
  obtain ⟨g, hg, hguniq⟩ := hc₁.2.2 C ‹_› ‹_› ‹_› f hfa₁
  -- and then `g(a₂) = g(1)`, so `g` factors through `h₂`
  have hga₂ : (g a₂ : C) = g 1 := by rw [← h1e, hg e, hf, ← hu₁, hg 1]
  obtain ⟨f', hf', hf'uniq⟩ := hc₂.2.2 C ‹_› ‹_› ‹_› g hga₂
  refine ⟨f', fun x => ?_, fun f'' hf'' => ?_⟩
  · rw [hk, hf' (h₁ x), hg x]
  · refine hf'uniq f'' fun y => ?_
    obtain ⟨g'', hg''⟩ := exists_ncpComp f'' h₂
    have hg''g : g'' = g := hguniq g'' fun x => by rw [hg'', ← hk, hf'' x]
    rw [← hg'', hg''g]

/-- **171VII** (`paschke-pure`, dils.tex:6373, Theorem): an ncp-map `φ`
with Paschke dilation `(𝒫, ϱ, h)` is pure if and only if `ϱ` is
surjective.

**171VIII** is the proof, transcribed.

**⇐** `ϱ` surjective is a corner (of a central projection) by **170IV**.1
`surjective_nmiu_1` — this is the thesis's "`ker ϱ = z𝒜` by
`weakly-closed-ideal`, so `ϱ` is a corner by the isomorphism theorem",
already available in the tree in that form.  `h` is pure by **170II**.2
`dils_examples_pure_2`, say `h = c ∘ k` with `k` a corner, and then
`φ = c ∘ (k ∘ ϱ)` with `k ∘ ϱ` a corner by `isCornerFor_comp`.  (Where the
thesis says "a composition of pure maps is pure", `IsPureMap` demands the
normal form *filter after corner*, so what is actually needed is that
*corners* compose; see `isCornerFor_comp`.)

**⇒** `φ = c ∘ h` for a filter `c` and an abstract corner `h`, which
`pext_corner_iso` (**169IV**) identifies with the standard corner `h_p`,
`p = ⌊a⌋`, up to an ncp-isomorphism; **171II** `paschke_corner` and
**169XI**.1 `dils_filter_basics_1` then assemble a Paschke dilation of `φ`
whose `ϱ`-leg is the standard corner `h_{⌈⌈p⌉⌉}`, visibly surjective.  Any
other dilation has an `ϱ` differing from it by a bijective nmiu-map
(`paschke_unique_up_to_iso`, **140VIII**), hence is surjective too.  This is
the same opening as **172X** `pure_ncp_extreme`. -/
theorem paschke_pure [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    IsPureMap φ ↔ Function.Surjective ⇑D.ρ := by
  classical
  let _ := D.vn
  constructor
  · rintro ⟨C, iC, iP, iS, h, c, hcorner, hfilter, hcomp⟩
    letI := iC; letI := iP; letI := iS
    obtain ⟨a, hca⟩ := hcorner
    obtain ⟨hp, v, u, hval, hvhp, hvu, huv⟩ := pext_corner_iso h a hca
    set p : A := floor a with hpdef
    letI : VonNeumannAlgebra (cornerSet A (cceil p)) :=
      cornerSet_vonNeumannAlgebra A (cceil p)
    obtain ⟨ρ₀, h₀, hρval, hh₀val, hD₀⟩ := paschke_corner p hp hval
    obtain ⟨H₁, hH₁⟩ := exists_ncpComp v h₀
    have hD₁ : IsPaschkeDilationOf
        ⟨cornerSet A (cceil p), cornerSet_vonNeumannAlgebra A (cceil p), ρ₀, H₁⟩
        (fun x => v (hp x)) :=
      pext_dilation_target_iso ⇑hp _ hD₀ v u hvu huv H₁ hH₁
    have hvhp' : (fun x => v (hp x)) = ⇑h := funext hvhp
    rw [hvhp'] at hD₁
    obtain ⟨H₂, hH₂, hD₂⟩ := dils_filter_basics_1 h _ hD₁ c hfilter
    have hcomp' : (fun x => c (h x)) = ⇑φ := (funext hcomp).symm
    rw [hcomp'] at hD₂
    have hρ0surj : Function.Surjective ⇑ρ₀ := by
      intro y
      exact ⟨y.1, Subtype.ext (by rw [hρval]; exact y.2)⟩
    obtain ⟨ϑ, ⟨hbij, hϑρ, -⟩, -⟩ :=
      paschke_unique_up_to_iso ⇑φ
        ⟨cornerSet A (cceil p), cornerSet_vonNeumannAlgebra A (cceil p), ρ₀, H₂⟩
        D hD₂ hD
    intro y
    obtain ⟨w, hw⟩ := hbij.2 y
    obtain ⟨x, hx⟩ := hρ0surj w
    exact ⟨x, by rw [← hϑρ x, hx, hw]⟩
  · intro hsurj
    -- `ϱ`, as an ncp-map, is a corner of a central projection (**170IV**.1)
    obtain ⟨ϱc, hϱc⟩ := pcorner_exists_ncpOfNmiu D.ρ
    obtain ⟨z, -, -, hzcorner⟩ := surjective_nmiu_1 D.ρ hsurj ϱc hϱc
    have hϱ1 : (ϱc 1 : D.P) = 1 := by rw [hϱc]; exact map_one D.ρ.toStarAlgHom
    -- `h` is pure (**170II**.2): `h = c ∘ k` with `k` a corner, `c` a filter
    obtain ⟨C, iC, iP, iS, k, c, hkcorner, hcfilter, hkc⟩ :=
      dils_examples_pure_2 φ D hD
    letI := iC; letI := iP; letI := iS
    obtain ⟨a₂, ha₂⟩ := hkcorner
    -- an effect `e ≤ ⌊z⌋ ≤ z` of `A` with `ϱ(e) = a₂`
    obtain ⟨hp₀, v₀, u₀, hval₀, hv₀, hv₀u₀, hu₀v₀⟩ := pext_corner_iso ϱc z hzcorner
    have hzfloor : floor z ∈ effects A := ⟨(floor_spec hzcorner.1).1.nonneg,
      (floor_spec hzcorner.1).1.le_one⟩
    have hp₀1 : (hp₀ (1 : A) : cornerSet A (floor z)) = 1 := by
      refine Subtype.ext ?_
      rw [hval₀, mul_one]
      exact (floor_spec hzcorner.1).1.isIdempotentElem.eq
    have hv₀1 : (v₀ (1 : cornerSet A (floor z)) : D.P) = 1 := by
      rw [← hp₀1, hv₀ 1, hϱ1]
    have hu₀1 : (u₀ (1 : D.P) : cornerSet A (floor z)) = 1 := by
      rw [← hv₀1, hu₀v₀]
    set e : A := (u₀ a₂).1 with hedef
    have hu₀mono : ∀ x y : D.P, x ≤ y → u₀ x ≤ u₀ y :=
      fun _ _ hxy => (ncpPos u₀).monotone hxy
    have he0 : (0 : A) ≤ e := by
      have h0 : (0 : cornerSet A (floor z)) = u₀ 0 :=
        (map_zero u₀.toCompletelyPositiveMap).symm
      have h1 : (0 : cornerSet A (floor z)) ≤ u₀ a₂ := by
        rw [h0]; exact hu₀mono _ _ ha₂.1.1
      exact h1
    have hefl : e ≤ floor z := by
      have h1 : u₀ a₂ ≤ (1 : cornerSet A (floor z)) := by
        rw [← hu₀1]; exact hu₀mono _ _ ha₂.1.2
      exact h1
    have hez : e ≤ z := hefl.trans (floor_le hzcorner.1)
    have he : e ∈ effects A := ⟨he0, hez.trans hzcorner.1.2⟩
    have hϱe : (ϱc e : D.P) = a₂ := by
      have h1 : hp₀ e = u₀ a₂ := Subtype.ext (by rw [hval₀]; exact (u₀ a₂).2)
      rw [← hv₀ e, h1, hv₀u₀]
    -- assemble
    obtain ⟨kϱ, hkϱ⟩ := exists_ncpComp k ϱc
    refine ⟨C, iC, iP, iS, kϱ, c,
      ⟨e, isCornerFor_comp ϱc z hzcorner hϱ1 k a₂ ha₂ e he hez hϱe kϱ hkϱ⟩,
      hcfilter, fun x => ?_⟩
    rw [hkϱ, hϱc, ← hkc, hD.1 x]

end PaschkePure

section PureTypeI

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### **170II**.1: the pure maps `B(ℋ) → B(𝒦)`

dils.tex states 170II.1 as an *Example*, with **no proof** and no solution
in `bsols.tex`; proc.tex **99XI** `ad-pure` gives the corresponding picture
for `a*(·)a : s𝒜s → t𝒜t` inside one von Neumann algebra, via the polar
decomposition `a = [a]√(a*a)`, but not for two `B(ℋ)`s.  The route taken
here is the chapter's own later theorem instead: **171VII** `paschke_pure`
("pure ⟺ the `ϱ`-leg of a Paschke dilation is surjective") combined with
**140III** `stinespring_is_paschke` ("a *minimal normal Stinespring*
dilation is a Paschke dilation").  So for `φ : B(ℋ) → B(𝒦)` with minimal
Stinespring dilation `(𝒦₀, ϱ, V)`,

  `φ` is pure  ⟺  `ϱ : B(ℋ) → B(𝒦₀)` is surjective,

and the classification is then read off **138II** `nmiu_between_type_I` and
**138VI** `typei_inner_auto`: a surjective `ϱ` is also *injective* (write
`ϱ(a) = U*(a ⊗ 1)U` with `U` unitary; `𝒦₀ ≠ 0` forces `𝒦' ≠ 0`, and
`‖a x ⊗ y‖ = ‖a x‖‖y‖` then turns `a ⊗ 1 = 0` into `a = 0`), hence an
nmiu-*isomorphism*, hence `ad_{U₀}` for a unitary `U₀ : 𝒦₀ → ℋ`, and
`φ = ad_V ∘ ad_{U₀} = ad_{U₀ V}`.  Conversely `ad_T` for `T ≠ 0` has the
*identity* dilation `(ℋ, id, T)`, which is minimal because
`B(ℋ)·T x₀ = ℋ` for any `x₀` with `T x₀ ≠ 0`, and whose `ϱ = id` is
surjective; and `ad_0 = 0`, whose minimal dilation lives on the zero
Hilbert space (from `φ(1) = 0` one gets `V*V = 0`, so `V = 0`, so the span
of `ϱ(B(ℋ))V𝒦` is `{0}`), where `ϱ` is again surjective.

This is a **different route** from proc.tex's polar-decomposition
factorisation `π_{⌈a⌉}` then `c_{a*a}`; see PROVING-LOG session 92. -/

private theorem pure_conjOperator_comp {X Y Z : Type u}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (V : X →L[ℂ] Y) (S : Y →L[ℂ] Z) (T : Z →L[ℂ] Z) :
    conjOperator V (conjOperator S T) = conjOperator (S.comp V) T := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp [conjOperator, ContinuousLinearMap.adjoint_comp]

private theorem pure_subsingleton_hilbTensor {K' : Type u} [NormedAddCommGroup K']
    [InnerProductSpace ℂ K'] [CompleteSpace K'] (h : Subsingleton K')
    (v : hilbTensor H K') : v = 0 := by
  have hts : ∀ z : TensorProduct ℂ H K', z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim y (0 : K'), TensorProduct.tmul_zero]
    | add z z' hz hz' => rw [hz, hz', add_zero]
  have hrange : Set.range (fun z : TensorProduct ℂ H K' => (z : hilbTensor H K'))
      ⊆ ({0} : Set (hilbTensor H K')) := by
    rintro _ ⟨z, rfl⟩
    simp only [Set.mem_singleton_iff]
    rw [hts z]
    exact UniformSpace.Completion.coe_zero
  have h1 : closure (Set.range (fun z : TensorProduct ℂ H K' => (z : hilbTensor H K')))
      = Set.univ := hilbTensor_denseRange_coe.closure_eq
  have h2 : (Set.univ : Set (hilbTensor H K')) ⊆ closure ({0} : Set (hilbTensor H K')) := by
    rw [← h1]; exact closure_mono hrange
  have h3 := h2 (Set.mem_univ v)
  rwa [closure_singleton, Set.mem_singleton_iff] at h3

private theorem pure_iff_stinespring_surjective
    (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) (D : StinespringDilation ⇑φ)
    (hmin : D.Minimal) : IsPureMap φ ↔ Function.Surjective ⇑D.ρ := by
  obtain ⟨vnK, hncp, hval, hpasch⟩ := stinespring_is_paschke φ D hmin
  exact paschke_pure φ _ hpasch

/-- **170II** (`dils-examples-pure`, dils.tex:6203, Examples), part 1: the
pure maps `B(ℋ) → B(𝒦)` are precisely the maps `ad_T` for bounded
operators `T : 𝒦 → ℋ`.

Proof: see the section header above. -/
theorem dils_examples_pure_1 (φ : NCPMap (H →L[ℂ] H) (K →L[ℂ] K)) :
    IsPureMap φ ↔ ∃ T : K →L[ℂ] H, ∀ a, φ a = conjOperator T a := by
  constructor
  · -- `⇒`
    intro hpure
    obtain ⟨D, hmin⟩ := exists_minimal_stinespringDilation φ
    have hsurj : Function.Surjective ⇑D.ρ :=
      (pure_iff_stinespring_surjective φ D hmin).mp hpure
    by_cases hs : Subsingleton D.K
    · refine ⟨0, fun a => ?_⟩
      have h0 : (D.ρ a : D.K →L[ℂ] D.K) = 0 :=
        ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
      rw [D.eq a, h0]
      simp [conjOperator]
    · rw [not_subsingleton_iff_nontrivial] at hs
      have hone : (1 : D.K →L[ℂ] D.K) ≠ 0 := by
        intro hc
        obtain ⟨x, y, hxy⟩ := hs
        refine hxy ?_
        have hx := congrArg (fun T : D.K →L[ℂ] D.K => T x) hc
        have hy := congrArg (fun T : D.K →L[ℂ] D.K => T y) hc
        simp only [one_apply_eq_self, zero_apply] at hx hy
        rw [hx, hy]
      have hρ1 : (D.ρ 1 : D.K →L[ℂ] D.K) = 1 := map_one D.ρ.toStarAlgHom
      obtain ⟨K', i1, i2, i3, U, hUU, hUU', hU⟩ :=
        nmiu_between_type_I D.ρ ⟨1, by rw [hρ1]; exact hone⟩
      letI := i1; letI := i2; letI := i3
      have hadj : ∀ z : D.K, ContinuousLinearMap.adjoint U (U z) = z := by
        intro z
        have h := congrArg (fun T : D.K →L[ℂ] D.K => T z) hUU
        simpa using h
      have hUsurj : ∀ w : hilbTensor H K', U (ContinuousLinearMap.adjoint U w) = w := by
        intro w
        have h := congrArg (fun T : hilbTensor H K' →L[ℂ] hilbTensor H K' => T w) hUU'
        simpa using h
      have hK' : Nontrivial K' := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        refine (not_subsingleton_iff_nontrivial.mpr hs) ⟨fun z w => ?_⟩
        rw [← hadj z, ← hadj w, pure_subsingleton_hilbTensor hsub (U z),
          pure_subsingleton_hilbTensor hsub (U w)]
      have hzero : ∀ c : H →L[ℂ] H, (D.ρ c : D.K →L[ℂ] D.K) = 0 → c = 0 := by
        intro c hc
        have hc' : conjOperator U (tensorCLM c 1) = 0 := by rw [← hU c]; exact hc
        have h1 : ∀ v : D.K, (tensorCLM c 1) (U v) = 0 := by
          intro v
          have h2 := congrArg (fun T : D.K →L[ℂ] D.K => T v) hc'
          simp only [conjOperator, LinearMap.coe_mk, AddHom.coe_mk,
            ContinuousLinearMap.coe_comp, Function.comp_apply, zero_apply] at h2
          have h3 := congrArg (fun z : D.K => U z) h2
          simp only [map_zero] at h3
          rwa [hUsurj] at h3
        have h4 : tensorCLM c (1 : K' →L[ℂ] K') = 0 := by
          refine ContinuousLinearMap.ext fun w => ?_
          rw [← hUsurj w, h1]
          simp
        obtain ⟨y, hy⟩ := exists_ne (0 : K')
        refine ContinuousLinearMap.ext fun x => ?_
        have h5 : hilbTensorMk (c x) y = (0 : hilbTensor H K') := by
          have h5' := tensorCLM_mk c (1 : K' →L[ℂ] K') x y
          rw [h4] at h5'
          simpa using h5'.symm
        have h6 : ‖c x‖ * ‖y‖ = 0 := by
          rw [← norm_hilbTensorMk (c x) y, h5, norm_zero]
        have h7 : ‖c x‖ = 0 := by
          rcases mul_eq_zero.mp h6 with h | h
          · exact h
          · exact absurd (norm_eq_zero.mp h) hy
        simpa using norm_eq_zero.mp h7
      have hinj : Function.Injective ⇑D.ρ := by
        intro a b hab
        have h0 : (D.ρ (a - b) : D.K →L[ℂ] D.K) = 0 := by
          have hsub := map_sub D.ρ.toStarAlgHom a b
          show (D.ρ.toStarAlgHom (a - b) : D.K →L[ℂ] D.K) = 0
          rw [hsub]
          show (D.ρ a : D.K →L[ℂ] D.K) - D.ρ b = 0
          rw [hab, sub_self]
        exact sub_eq_zero.mp (hzero _ h0)
      obtain ⟨U₀, -, -, hU₀⟩ := (typei_inner_auto D.ρ).mp ⟨hinj, hsurj⟩
      exact ⟨U₀.comp D.V, fun a => by rw [D.eq a, hU₀ a, pure_conjOperator_comp]⟩
  · -- `⇐`
    rintro ⟨T, hT⟩
    by_cases hT0 : T = 0
    · -- `ad_0 = 0`: the minimal dilation of the zero map lives on the zero space
      have hz : ∀ a, (φ a : K →L[ℂ] K) = 0 := by
        intro a
        rw [hT a, hT0]
        simp [conjOperator]
      obtain ⟨D, hmin⟩ := exists_minimal_stinespringDilation φ
      refine (pure_iff_stinespring_surjective φ D hmin).mpr ?_
      have hV : D.V = 0 := by
        have h2 : (D.ρ 1 : D.K →L[ℂ] D.K) = 1 := map_one D.ρ.toStarAlgHom
        have h1 : ∀ x : K, ContinuousLinearMap.adjoint D.V (D.V x) = 0 := by
          intro x
          have h0 := (D.eq 1).symm
          rw [hz, h2] at h0
          have h3 := congrArg (fun T : K →L[ℂ] K => T x) h0
          simpa [conjOperator] using h3
        refine ContinuousLinearMap.ext fun x => ?_
        have h4 : (⟪D.V x, D.V x⟫ : ℂ) = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_right, h1 x, inner_zero_right]
        simpa using inner_self_eq_zero.mp h4
      have hset : {k : D.K | ∃ (a : H →L[ℂ] H) (x : K), k = D.ρ a (D.V x)} = {0} := by
        ext k
        constructor
        · rintro ⟨a, x, rfl⟩
          simp [hV]
        · rintro rfl
          exact ⟨1, 0, by simp [hV]⟩
      have hdense : Dense ((⊥ : Submodule ℂ D.K) : Set D.K) := by
        have hm := hmin
        unfold StinespringDilation.Minimal at hm
        rwa [hset, Submodule.span_zero_singleton] at hm
      have hsub : ∀ v : D.K, v = 0 := by
        intro v
        rw [Submodule.bot_coe] at hdense
        have hcl := dense_iff_closure_eq.mp hdense
        rw [closure_singleton] at hcl
        have hv : v ∈ ({0} : Set D.K) := by rw [hcl]; exact Set.mem_univ v
        exact hv
      intro y
      exact ⟨1, ContinuousLinearMap.ext fun x => by rw [hsub x]; simp [hsub]⟩
    · -- `T ≠ 0`: the identity dilation `(ℋ, id, T)` is minimal, and its `ϱ` is onto
      refine (pure_iff_stinespring_surjective φ
        { K := H, ρ := Theses.A.Proc.nmiuId (H →L[ℂ] H), V := T,
          eq := fun a => hT a } ?_).mpr ?_
      · show Dense ((Submodule.span ℂ
          {k : H | ∃ (a : H →L[ℂ] H) (x : K), k = a (T x)} : Submodule ℂ H) : Set H)
        obtain ⟨x₀, hx₀⟩ : ∃ x : K, T x ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hT0 (ContinuousLinearMap.ext hc)
        have hspan : Submodule.span ℂ
            {k : H | ∃ (a : H →L[ℂ] H) (x : K), k = a (T x)} = ⊤ := by
          refine eq_top_iff.mpr fun v _ => ?_
          refine Submodule.subset_span
            ⟨ketbra ((⟪T x₀, T x₀⟫ : ℂ)⁻¹ • v) (T x₀), x₀, ?_⟩
          rw [ketbra_apply', smul_smul,
            mul_inv_cancel₀ (inner_self_ne_zero.mpr hx₀), one_smul]
        rw [hspan]
        simp
      · intro y
        exact ⟨y, rfl⟩


end PureTypeI


/-! ## Parsec 1720: ncp-extreme maps

**172I** (dils.tex:6412): introduction; **172IV**–**172VII**, **172IX**,
**172XI** are proofs — not converted. -/

section Extreme

variable {A B : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **172II** (dils.tex:6416, Definition): an ncp-map `φ` is
**ncp-extreme** when it is an extreme point among the ncp-maps with the
same value on `1`: `λφ₁ + (1-λ)φ₂ = φ` with `0 < λ < 1` and
`φ₁(1) = φ₂(1) = φ(1)` forces `φ₁ = φ₂ = φ`. -/
def NCPExtreme (φ : NCPMap A B) : Prop :=
  ∀ l : ℝ, 0 < l → l < 1 → ∀ φ₁ φ₂ : NCPMap A B,
    φ₁ 1 = φ 1 → φ₂ 1 = φ 1 →
    (∀ a, φ a = (l : ℂ) • φ₁ a + ((1 - l : ℝ) : ℂ) • φ₂ a) →
    (∀ a, φ₁ a = φ a) ∧ ∀ a, φ₂ a = φ a

/-- Auxiliary: multiplication by a nonnegative real is monotone on a
C\*-algebra (Mathlib has no `PosSMulMono ℝ` instance here; this is the
`√r`-conjugation workaround of **25I**, via `ofReal_smul_nonneg`). -/
private theorem smulReal_mono_aux {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    {x y : C} (h : x ≤ y) {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) • x ≤ (r : ℂ) • y := by
  have h0 := ofReal_smul_nonneg (sub_nonneg.mpr h) hr
  rwa [smul_sub, sub_nonneg] at h0

/-- Auxiliary: `x ↦ r·x` preserves suprema for `r ≥ 0` (for `r = 0` this
needs the set to be non-empty, which normality supplies). -/
private theorem isLUB_ofReal_smul {S : Set B} {t : B} (h : IsLUB S t) {r : ℝ} (hr : 0 ≤ r)
    (hne : S.Nonempty) : IsLUB ((fun x : B => (r : ℂ) • x) '' S) ((r : ℂ) • t) := by
  rcases hr.eq_or_lt with hr0 | hrpos
  · have himg : (fun x : B => (r : ℂ) • x) '' S = {0} := by
      ext y
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, -, rfl⟩; simp [← hr0]
      · rintro rfl; obtain ⟨x, hx⟩ := hne; exact ⟨x, hx, by simp [← hr0]⟩
    rw [himg, ← hr0]
    simp
  · have hrne : (r : ℂ) ≠ 0 := by simpa using hrpos.ne'
    constructor
    · rintro y ⟨x, hx, rfl⟩
      exact smulReal_mono_aux (h.1 hx) hr
    · intro b hb
      have hcancel : ∀ x : B, ((r⁻¹ : ℝ) : ℂ) • ((r : ℂ) • x) = x := by
        intro x
        rw [smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hrne, one_smul]
      have hub : t ≤ ((r⁻¹ : ℝ) : ℂ) • b := by
        refine h.2 fun x hx => ?_
        have := smulReal_mono_aux (hb ⟨x, hx, rfl⟩) (le_of_lt (inv_pos.mpr hrpos))
        rwa [hcancel x] at this
      have h2 := smulReal_mono_aux hub hr
      have hrr : (r : ℂ) * ((r⁻¹ : ℝ) : ℂ) = 1 := by
        push_cast
        exact mul_inv_cancel₀ hrne
      rwa [smul_smul, hrr, one_smul] at h2

/-- Auxiliary: a nonnegative real multiple of an ncp-map is an ncp-map.
Needed to feed `λψ` to **157IV**.3 `paschke_correspondence_surjective`
(`ncpInterval` takes *bundled* ncp-maps), and to build the two halves
`λ⁻¹φ_t`, `(1-λ)⁻¹φ_{1-t}` of the convex decomposition in 3 ⇒ 1. -/
private noncomputable def ncpSMul (r : ℝ) (hr : 0 ≤ r) (f : NCPMap A B) : NCPMap A B where
  toCompletelyPositiveMap :=
    { toLinearMap := (r : ℂ) • f.toCompletelyPositiveMap.toLinearMap
      map_cstarMatrix_nonneg' := by
        refine (cp_iff _).out 0 1 |>.mp ((cp_iff _).out 2 0 |>.mp ?_)
        intro N a
        have hf : IsCompletelyPositiveMap f.toCompletelyPositiveMap.toLinearMap :=
          (cp_iff _).out 1 0 |>.mp fun N M hM =>
            f.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
        have h3 : ∀ (N : ℕ) (a : Fin N → A),
            0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j =>
              f.toCompletelyPositiveMap.toLinearMap (star (a i) * a j)) :=
          (cp_iff f.toCompletelyPositiveMap.toLinearMap).out 0 2 |>.mp hf
        have hbase := h3 N a
        have heq : CStarMatrix.ofMatrix
              (Matrix.of fun i j => ((r : ℂ) • f.toCompletelyPositiveMap.toLinearMap)
                 (star (a i) * a j))
            = (r : ℂ) • CStarMatrix.ofMatrix
                (Matrix.of fun i j =>
                  f.toCompletelyPositiveMap.toLinearMap (star (a i) * a j)) := by
          ext i j
          simp
        rw [heq]
        exact ofReal_smul_nonneg hbase hr }
  preservesDirSups' := by
    have key : PreservesDirSups ⇑((r : ℂ) • f.toCompletelyPositiveMap.toLinearMap) := by
      intro Ds s hne hdir hlub
      have h := f.preservesDirSups' Ds s hne hdir hlub
      have himg : ((fun d : selfAdjoint A =>
          ((r : ℂ) • f.toCompletelyPositiveMap.toLinearMap) (d : A)) '' Ds)
          = (fun x : B => (r : ℂ) • x) ''
              ((fun d : selfAdjoint A => (f (d : A) : B)) '' Ds) := by
        rw [Set.image_image]
        rfl
      rw [himg]
      exact isLUB_ofReal_smul h hr (hne.image _)
    exact key

@[simp] private theorem ncpSMul_apply (r : ℝ) (hr : 0 ≤ r) (f : NCPMap A B) (a : A) :
    ncpSMul r hr f a = (r : ℂ) • f a := rfl

/-- **172III**'s "Using `cstar-positive` and some easy algebra, we can find
`0 < μ, λ` such that `¼ ≤ μa + λ ≤ ¾`" (dils.tex:6492), for self-adjoint `a`.
`cstar-positive`.2 (cstar.tex:1209) is `-‖a‖ ≤ a ≤ ‖a‖`, i.e. Mathlib's
`norm_le_iff_neg_algebraMap_le`; scaling by `μ = (4(‖a‖+1))⁻¹` puts `μa` in
`[-¼, ¼]` and `λ = ½` shifts it into `[¼, ¾]`.

Deliberately stated as an **existential**: the proof of 172III below uses
only `0 < μ`, `0 < λ` and the two bounds, never the values, so that the
upper bound `λ < 1` has to be read off `ptp = λp` as the thesis reads it. -/
private theorem exists_mu_lambda {P : Type*} [CStarAlgebra P] [PartialOrder P]
    [StarOrderedRing P] {a : P} (hsa : IsSelfAdjoint a) :
    ∃ μ l : ℝ, 0 < μ ∧ 0 < l ∧
      ((1/4 : ℝ) : ℂ) • (1 : P) ≤ ((μ : ℝ) : ℂ) • a + ((l : ℝ) : ℂ) • (1 : P) ∧
      ((μ : ℝ) : ℂ) • a + ((l : ℝ) : ℂ) • (1 : P) ≤ ((3/4 : ℝ) : ℂ) • (1 : P) := by
  have hden : (0 : ℝ) < 4 * (‖a‖ + 1) := by positivity
  set μ : ℝ := (4 * (‖a‖ + 1))⁻¹ with hμdef
  have hμ0 : 0 < μ := by rw [hμdef]; positivity
  have hsa' : IsSelfAdjoint (((μ : ℝ) : ℂ) • a) := by
    refine IsSelfAdjoint.smul ?_ hsa
    simp [IsSelfAdjoint]
  have hna' : ‖((μ : ℝ) : ℂ) • a‖ ≤ 1 / 4 := by
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ0]
    rw [hμdef]
    rw [inv_mul_eq_div, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
    nlinarith [norm_nonneg a]
  have hb := (norm_le_iff_neg_algebraMap_le hsa' (by norm_num : (0:ℝ) ≤ 1/4)).mp hna'
  have halg : ∀ r : ℝ, algebraMap ℂ P ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) • (1 : P) :=
    fun r => Algebra.algebraMap_eq_smul_one _
  rw [halg] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hneg : -((((1/4 : ℝ)) : ℂ) • (1 : P)) = (((-(1/4) : ℝ)) : ℂ) • (1 : P) := by
    push_cast; rw [neg_smul]
  rw [hneg] at hb1
  refine ⟨μ, 1/2, hμ0, by norm_num, ?_, ?_⟩
  · have h4 : ((((-(1/4) : ℝ)) : ℂ) • (1 : P)) + ((((1/2 : ℝ)) : ℂ) • 1)
        = ((((1/4 : ℝ)) : ℂ) • (1 : P)) := by
      rw [← add_smul]; push_cast; ring_nf
    calc (((1/4 : ℝ) : ℂ) • (1 : P))
        = ((((-(1/4) : ℝ)) : ℂ) • (1 : P)) + ((((1/2 : ℝ)) : ℂ) • 1) := h4.symm
      _ ≤ ((μ : ℝ) : ℂ) • a + ((((1/2 : ℝ)) : ℂ) • 1) := add_le_add hb1 le_rfl
  · have h4 : ((((1/4 : ℝ)) : ℂ) • (1 : P)) + ((((1/2 : ℝ)) : ℂ) • 1)
        = ((((3/4 : ℝ)) : ℂ) • (1 : P)) := by
      rw [← add_smul]; push_cast; ring_nf
    calc ((μ : ℝ) : ℂ) • a + ((((1/2 : ℝ)) : ℂ) • 1)
        ≤ ((((1/4 : ℝ)) : ℂ) • (1 : P)) + ((((1/2 : ℝ)) : ℂ) • 1) := add_le_add hb2 le_rfl
      _ = ((((3/4 : ℝ)) : ℂ) • (1 : P)) := h4

/-- **172III** (`ncp-extreme-paschke`, dils.tex:6434, Theorem): for an
ncp-map `φ` with Paschke dilation `(𝒫, ϱ, h)` the following are
equivalent: (1) `h` is injective on the commutant `ϱ(A)′`; (2) `h` is
injective on `[0,1]_{ϱ(A)′}`; (3) `φ` is ncp-extreme.

**1 ⇒ 2** is a restriction and **2 ⇒ 3** is the thesis's argument verbatim:
`λψ ≤_ncp φ`, so `λψ = φ_t` for some `t ∈ [0,1]_{ϱ(A)′}` by **157IV**.3, and
`h(t) = φ_t(1) = λφ(1) = h(λ1)` forces `t = λ1`.

**3 ⇒ 1 is the thesis's own argument** (dils.tex:6475-6510), step for step.
For self-adjoint `a` in the commutant with `h(a) = 0`: by **170II**.2
`dils_examples_pure_2` the map `h` is pure, so `h = c ∘ k` with `k` a corner
(the thesis's standard corner `h_p`, `p = ⌈h⌉`) and `c` a filter; filters are
injective (**169XII** `dils_filters_injective`), so `k(a) = 0` — the thesis's
`pap = 0`.  `cstar-positive`.2 (cstar.tex:1209, `-‖x‖ ≤ x ≤ ‖x‖`) supplies
`0 < μ, λ` with `¼ ≤ t ≤ ¾` for `t = μa + λ` (`exists_mu_lambda`; the values
are *not* used below, only the existential, exactly as in the thesis).
Applying `k` gives `k(t) = λ k(1)` — the thesis's `ptp = λp` — and hence
`¼ k(1) ≤ λ k(1) ≤ ¾ k(1)`, off which `0 < λ < 1` is read: if `λ ≥ 1` then
`k(1) = 0`, which is the thesis's degenerate case `p = 0`.  There the thesis
says "`φ = 0` hence `𝒫 = {0}`"; that minimality is available here as the
injectivity of `t ↦ φ_t` (**157IV**.2), which turns `φ_0 = φ_1` into
`0 = 1` in `𝒫`, so `a = 0`.  In the non-trivial case `ψ₁ = λ⁻¹φ_t` and
`ψ₂ = (1-λ)⁻¹φ_{1-t}` are ncp-maps with `ψ₁(1) = ψ₂(1) = φ(1)` and
`λψ₁ + (1-λ)ψ₂ = φ`, so ncp-extremity gives `φ_t = λφ = φ_{λ1}`, whence
`t = λ1` by **157IV**.2 and `μa = 0`, i.e. `a = 0`.
The general element is handled by its real and imaginary parts, which are
again in the commutant and again killed by `h`, as the thesis does
(dils.tex:6478). -/
theorem ncp_extreme_paschke [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (D : PaschkeTriple A B)
    (hD : IsPaschkeDilationOf D ⇑φ) :
    List.TFAE
      [Set.InjOn ⇑D.h (commutant D.P (Set.range ⇑D.ρ)),
       Set.InjOn ⇑D.h
         (commutant D.P (Set.range ⇑D.ρ) ∩ Set.Icc (0 : D.P) 1),
       NCPExtreme φ] := by
  let _ := D.vn
  have hρ1 : (D.ρ (1 : A) : D.P) = 1 := map_one D.ρ.toStarAlgHom
  have hhadd : ∀ x y : D.P, (D.h (x + y) : B) = D.h x + D.h y := fun x y =>
    map_add D.h.toCompletelyPositiveMap.toLinearMap x y
  have hhsub : ∀ x y : D.P, (D.h (x - y) : B) = D.h x - D.h y := fun x y =>
    map_sub D.h.toCompletelyPositiveMap.toLinearMap x y
  have hhsmul : ∀ (c : ℂ) (x : D.P), (D.h (c • x) : B) = c • D.h x := fun c x =>
    map_smul D.h.toCompletelyPositiveMap.toLinearMap c x
  have hh1 : (D.h (1 : D.P) : B) = φ 1 := by rw [← hρ1]; exact hD.1 1
  have hphiT1 : ∀ t : D.P, phiT D t 1 = D.h t := by
    intro t
    show (D.h (t * D.ρ 1) : B) = D.h t
    rw [hρ1, mul_one]
  have hcomm_smul_one : ∀ c : ℂ, (c • (1 : D.P)) ∈ commutant D.P (Set.range ⇑D.ρ) := by
    rintro c m ⟨a, rfl⟩
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hphiT_smul_one : ∀ (c : ℂ) (a : A), phiT D (c • (1 : D.P)) a = c • φ a := by
    intro c a
    show (D.h ((c • (1 : D.P)) * D.ρ a) : B) = c • φ a
    rw [smul_mul_assoc, one_mul, hhsmul, hD.1 a]
  have hone_mono : ∀ {c d : ℝ}, c ≤ d →
      ((c : ℂ) • (1 : D.P)) ≤ ((d : ℂ) • (1 : D.P)) := by
    intro c d hcd
    have h := ofReal_smul_nonneg (zero_le_one (α := D.P)) (sub_nonneg.mpr hcd)
    have he : ((d - c : ℝ) : ℂ) • (1 : D.P) = (d : ℂ) • 1 - (c : ℂ) • 1 := by
      push_cast; rw [sub_smul]
    rw [he, sub_nonneg] at h
    exact h
  have hsmul_one_one : ((1 : ℝ) : ℂ) • (1 : D.P) = 1 := by push_cast; rw [one_smul]
  have hphiT_inj : ∀ s t : D.P, s ∈ commutant D.P (Set.range ⇑D.ρ) → 0 ≤ s → s ≤ 1 →
      t ∈ commutant D.P (Set.range ⇑D.ρ) → 0 ≤ t → t ≤ 1 →
      (∀ a, phiT D s a = phiT D t a) → s = t := by
    intro s t hs hs0 hs1 ht ht0 ht1 heq
    have hzero : ∀ a, (ncpSMul (0 : ℝ) le_rfl φ) a = 0 := by
      intro a; rw [ncpSMul_apply]; simp
    have hle1 : NCPLe (phiT D t) (phiT D s) :=
      ⟨ncpSMul (0 : ℝ) le_rfl φ, fun a => by rw [hzero a, add_zero, heq a]⟩
    have hle2 : NCPLe (phiT D s) (phiT D t) :=
      ⟨ncpSMul (0 : ℝ) le_rfl φ, fun a => by rw [hzero a, add_zero, heq a]⟩
    exact le_antisymm
      ((paschke_correspondence_embedding φ D hD t s ht ht0 ht1 hs hs0 hs1).mp hle2)
      ((paschke_correspondence_embedding φ D hD s t hs hs0 hs1 ht ht0 ht1).mp hle1)
  tfae_have 1 → 2 := fun h => h.mono Set.inter_subset_left
  tfae_have 2 → 3 := by
    intro hinj
    have key : ∀ m : ℝ, 0 < m → m < 1 → ∀ ψ χ : NCPMap A B, ψ 1 = φ 1 →
        (∀ a, φ a = (m : ℂ) • ψ a + ((1 - m : ℝ) : ℂ) • χ a) → ∀ a, ψ a = φ a := by
      intro m hm0 hm1 ψ χ hψ1 hsum'
      have hmem : (fun a => (m : ℂ) • ψ a) ∈ ncpInterval ⇑φ := by
        refine ⟨⟨ncpSMul m hm0.le ψ, fun a => by rw [ncpSMul_apply, zero_add]⟩,
          ⟨ncpSMul (1 - m) (by linarith) χ, fun a => by
            rw [ncpSMul_apply]; exact hsum' a⟩⟩
      obtain ⟨t, htc, ht0, ht1, htφ⟩ :=
        paschke_correspondence_surjective φ D hD _ hmem
      have hs0 : (0 : D.P) ≤ ((m : ℝ) : ℂ) • (1 : D.P) :=
        ofReal_smul_nonneg zero_le_one hm0.le
      have hs1 : ((m : ℝ) : ℂ) • (1 : D.P) ≤ 1 := by
        have := hone_mono (le_of_lt hm1)
        rwa [hsmul_one_one] at this
      have hhts : (D.h t : B) = D.h (((m : ℝ) : ℂ) • (1 : D.P)) := by
        rw [← hphiT1 t, ← hphiT1 (((m : ℝ) : ℂ) • (1 : D.P)), hphiT_smul_one]
        have := congrFun htφ 1
        rw [this, hψ1]
      have hts : t = ((m : ℝ) : ℂ) • (1 : D.P) :=
        hinj ⟨htc, ht0, ht1⟩ ⟨hcomm_smul_one _, hs0, hs1⟩ hhts
      intro a
      have h1 := congrFun htφ a
      rw [hts, hphiT_smul_one] at h1
      have hmne : ((m : ℝ) : ℂ) ≠ 0 := by simpa using hm0.ne'
      exact (smul_right_injective B hmne h1).symm
    intro l hl0 hl1 φ₁ φ₂ h1 h2 hsum
    refine ⟨key l hl0 hl1 φ₁ φ₂ h1 hsum, key (1 - l) (by linarith) (by linarith) φ₂ φ₁ h2
      (fun a => ?_)⟩
    rw [hsum a]
    have hc : ((1 - (1 - l) : ℝ) : ℂ) = ((l : ℝ) : ℂ) := by push_cast; ring
    rw [hc, add_comm]
  tfae_have 3 → 1 := by
    intro hext
    have hhpos : IsPositiveMap D.h.toCompletelyPositiveMap.toLinearMap := by
      intro x hx
      have h1 : (D.h (0 : D.P) : B) ≤ D.h x :=
        OrderHomClass.mono D.h.toCompletelyPositiveMap hx
      have h2 : (D.h (0 : D.P) : B) = 0 :=
        map_zero D.h.toCompletelyPositiveMap.toLinearMap
      rw [h2] at h1
      exact h1
    have hhstar : ∀ x : D.P, (D.h (star x) : B) = star (D.h x) :=
      cstar_p_implies_i _ hhpos
    have hcstar : ∀ x ∈ commutant D.P (Set.range ⇑D.ρ),
        star x ∈ commutant D.P (Set.range ⇑D.ρ) := by
      rintro x hx m ⟨a, rfl⟩
      have h := hx (D.ρ (star a)) ⟨star a, rfl⟩
      have h2 := congrArg star h
      rw [star_mul, star_mul] at h2
      have h3 : star (D.ρ (star a) : D.P) = D.ρ a := by
        rw [show (D.ρ (star a) : D.P) = star (D.ρ a) from map_star D.ρ.toStarAlgHom a,
          star_star]
      rw [h3] at h2
      exact h2.symm
    -- **170II**.2 (dils.tex:6484): `h` is pure, so it splits as `h = c ∘ k`
    -- with `k` a corner (the thesis's standard corner `h_p`, `p = ⌈h⌉`) and
    -- `c` a filter.
    obtain ⟨Cp, _, _, _, k, c, -, hcfilter, hsplit⟩ := dils_examples_pure_2 φ D hD
    -- **169XII** (dils.tex:6489): filters are injective.
    have hcinj : Function.Injective ⇑c := dils_filters_injective c hcfilter
    have hc0 : (c (0 : Cp) : B) = 0 := map_zero c.toCompletelyPositiveMap
    have hcsmul : ∀ (z : ℂ) (x : Cp), (c (z • x) : B) = z • c x := fun z x =>
      map_smul c.toCompletelyPositiveMap.toLinearMap z x
    have hkadd : ∀ x y : D.P, (k (x + y) : Cp) = k x + k y := fun x y =>
      map_add k.toCompletelyPositiveMap.toLinearMap x y
    have hksmul : ∀ (z : ℂ) (x : D.P), (k (z • x) : Cp) = z • k x := fun z x =>
      map_smul k.toCompletelyPositiveMap.toLinearMap z x
    have hkmono : ∀ x y : D.P, x ≤ y → (k x : Cp) ≤ k y := fun _ _ hxy =>
      (ncpPos k).monotone hxy
    have hk1 : (0 : Cp) ≤ k 1 := by
      have h := hkmono 0 1 zero_le_one
      rwa [show (k (0 : D.P) : Cp) = 0 from map_zero k.toCompletelyPositiveMap] at h
    -- the self-adjoint core
    have hcore : ∀ a : D.P, a ∈ commutant D.P (Set.range ⇑D.ρ) → IsSelfAdjoint a →
        (D.h a : B) = 0 → a = 0 := by
      intro a ha hsa h0
      -- `c` is injective and `0 = h(a) = c(k a)`, so `k a = 0` (`pap = 0`)
      have hka : (k a : Cp) = 0 := by
        refine hcinj ?_
        show (c (k a) : B) = c 0
        rw [← hsplit a, h0, hc0]
      -- `cstar-positive` and some easy algebra: `¼ ≤ μa + λ ≤ ¾` (dils.tex:6492)
      obtain ⟨μ, l, hμ0, hl0, hlo, hhi⟩ := exists_mu_lambda hsa
      have hμne : ((μ : ℝ) : ℂ) ≠ 0 := by simpa using hμ0.ne'
      have hcancel : ∀ r : ℝ, r ≠ 0 → ∀ x : B,
          ((r⁻¹ : ℝ) : ℂ) • (((r : ℝ) : ℂ) • x) = x := by
        intro r hr x
        rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr, Complex.ofReal_one,
          one_smul]
      have hcancel' : ∀ r : ℝ, r ≠ 0 → ∀ x : B,
          ((r : ℝ) : ℂ) • (((r⁻¹ : ℝ) : ℂ) • x) = x := by
        intro r hr x
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one,
          one_smul]
      set t : D.P := ((μ : ℝ) : ℂ) • a + ((l : ℝ) : ℂ) • 1 with htdef
      have hq0 : (0 : D.P) ≤ ((1/4 : ℝ) : ℂ) • (1 : D.P) :=
        ofReal_smul_nonneg zero_le_one (by norm_num)
      have ht0 : (0 : D.P) ≤ t := le_trans hq0 hlo
      have ht1 : t ≤ 1 := by
        refine le_trans hhi ?_
        have h := hone_mono (by norm_num : (3/4 : ℝ) ≤ 1)
        rwa [hsmul_one_one] at h
      have htc : ∀ b : A, t * D.ρ b = D.ρ b * t := by
        intro b
        have hab := (ha (D.ρ b) ⟨b, rfl⟩).symm
        rw [htdef, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hab,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      have htcm : t ∈ commutant D.P (Set.range ⇑D.ρ) := by
        rintro m ⟨b, rfl⟩
        exact (htc b).symm
      -- `k t = λ k 1`, the thesis's `ptp = λp` (dils.tex:6497)
      have hkt : (k t : Cp) = ((l : ℝ) : ℂ) • k 1 := by
        rw [htdef, hkadd, hksmul, hksmul, hka, smul_zero, zero_add]
      -- so `λ k 1 ≤ ¾ k 1`, off which `λ < 1` is read
      have hbnd : ((l : ℝ) : ℂ) • (k 1 : Cp) ≤ ((3/4 : ℝ) : ℂ) • k 1 := by
        have h := hkmono _ _ hhi
        rwa [hkt, hksmul] at h
      have hht : (D.h t : B) = ((l : ℝ) : ℂ) • φ 1 := by
        rw [hsplit t, hkt, hcsmul, ← hsplit 1, hh1]
      by_cases hl1 : l < 1
      · -- the non-trivial case `0 < λ < 1` (dils.tex:6503)
        have hnl0 : (0 : ℝ) < 1 - l := by linarith
        obtain ⟨δ₁, hδ₁⟩ := exists_phiT_ncp D t ht0 htc
        obtain ⟨δ₂, hδ₂⟩ := exists_phiT_ncp D (1 - t) (sub_nonneg.mpr ht1)
          (fun b => by rw [sub_mul, mul_sub, one_mul, mul_one, htc b])
        set ψ₁ : NCPMap A B := ncpSMul l⁻¹ (inv_pos.mpr hl0).le δ₁ with hψ₁def
        set ψ₂ : NCPMap A B := ncpSMul (1 - l)⁻¹ (inv_pos.mpr hnl0).le δ₂ with hψ₂def
        have hh1t : (D.h (1 - t) : B) = ((1 - l : ℝ) : ℂ) • φ 1 := by
          rw [hhsub, hh1, hht]
          push_cast
          module
        have hψ₁1 : ψ₁ 1 = φ 1 := by
          rw [hψ₁def, ncpSMul_apply, hδ₁ 1, hρ1, mul_one, hht]
          exact hcancel l hl0.ne' (φ 1)
        have hψ₂1 : ψ₂ 1 = φ 1 := by
          rw [hψ₂def, ncpSMul_apply, hδ₂ 1, hρ1, mul_one, hh1t]
          exact hcancel (1 - l) hnl0.ne' (φ 1)
        have hsum : ∀ b, φ b
            = ((l : ℝ) : ℂ) • ψ₁ b + ((1 - l : ℝ) : ℂ) • ψ₂ b := by
          intro b
          have hkey : (D.h (t * D.ρ b) : B) + D.h ((1 - t) * D.ρ b) = φ b := by
            rw [← hhadd, show t * D.ρ b + (1 - t) * D.ρ b = D.ρ b by noncomm_ring,
              hD.1 b]
          rw [hψ₁def, hψ₂def, ncpSMul_apply, ncpSMul_apply, hδ₁ b, hδ₂ b,
            hcancel' l hl0.ne' _, hcancel' (1 - l) hnl0.ne' _, hkey]
        obtain ⟨hex1, -⟩ := hext l hl0 hl1 ψ₁ ψ₂ hψ₁1 hψ₂1 hsum
        have hs0 : (0 : D.P) ≤ ((l : ℝ) : ℂ) • (1 : D.P) :=
          ofReal_smul_nonneg zero_le_one hl0.le
        have hs1 : ((l : ℝ) : ℂ) • (1 : D.P) ≤ 1 := by
          have h := hone_mono hl1.le
          rwa [hsmul_one_one] at h
        have hphit : ∀ b, phiT D t b = phiT D (((l : ℝ) : ℂ) • (1 : D.P)) b := by
          intro b
          have h1 := hex1 b
          rw [hψ₁def, ncpSMul_apply, hδ₁ b] at h1
          rw [hphiT_smul_one]
          show (D.h (t * D.ρ b) : B) = ((l : ℝ) : ℂ) • φ b
          rw [← h1, hcancel' l hl0.ne' _]
        have hteq := hphiT_inj t _ htcm ht0 ht1 (hcomm_smul_one _) hs0 hs1 hphit
        rw [htdef] at hteq
        have hz : ((μ : ℝ) : ℂ) • a = 0 := by
          have h := sub_eq_zero.mpr hteq
          simpa using h
        exact (smul_eq_zero.mp hz).resolve_left hμne
      · -- `λ ≥ 1` is the thesis's degenerate case `p = 0` (dils.tex:6501)
        push_neg at hl1
        have hs : (0 : ℝ) < l - 3/4 := by linarith
        have hzk : (((l - 3/4 : ℝ)) : ℂ) • (k 1 : Cp) = 0 := by
          refine le_antisymm ?_ (ofReal_smul_nonneg hk1 hs.le)
          have hsub : ((l : ℝ) : ℂ) • (k 1 : Cp) - ((3/4 : ℝ) : ℂ) • k 1 ≤ 0 :=
            sub_nonpos.mpr hbnd
          have he : (((l - 3/4 : ℝ)) : ℂ) • (k 1 : Cp)
              = ((l : ℝ) : ℂ) • k 1 - ((3/4 : ℝ) : ℂ) • k 1 := by
            push_cast; rw [sub_smul]
          rw [he]
          exact hsub
        have hk10 : (k (1 : D.P) : Cp) = 0 :=
          (smul_eq_zero.mp hzk).resolve_left (Complex.ofReal_ne_zero.mpr hs.ne')
        -- `p = 0` means `h = 0`, hence `φ = 0`
        have hh10 : (D.h (1 : D.P) : B) = 0 := by rw [hsplit 1, hk10, hc0]
        have hhzero : ∀ x : D.P, (D.h x : B) = 0 := by
          intro x
          have hcs := ncp_cp_cs D.h x
          rw [hh10, norm_zero, zero_smul] at hcs
          exact (CStarRing.star_mul_self_eq_zero_iff _).mp
            (le_antisymm hcs (star_mul_self_nonneg _))
        -- and then `𝒫 = {0}`, by the injectivity of `t ↦ φ_t` (**157IV**.2)
        have hzm : (0 : D.P) ∈ commutant D.P (Set.range ⇑D.ρ) := by
          rintro m ⟨b, rfl⟩
          rw [mul_zero, zero_mul]
        have hom : (1 : D.P) ∈ commutant D.P (Set.range ⇑D.ρ) := by
          rintro m ⟨b, rfl⟩
          rw [mul_one, one_mul]
        have heq01 : ∀ b : A, phiT D 0 b = phiT D 1 b := by
          intro b
          show (D.h (0 * D.ρ b) : B) = D.h (1 * D.ρ b)
          rw [hhzero, hhzero]
        have h01 : (0 : D.P) = 1 :=
          hphiT_inj 0 1 hzm le_rfl zero_le_one hom zero_le_one le_rfl heq01
        calc a = a * 1 := (mul_one a).symm
          _ = a * 0 := by rw [← h01]
          _ = 0 := mul_zero a
    -- ### the general case, by taking real and imaginary parts
    intro x hx y hy hxy
    have hw : (x - y) ∈ commutant D.P (Set.range ⇑D.ρ) := by
      rintro m ⟨b, rfl⟩
      rw [mul_sub, sub_mul, hx (D.ρ b) ⟨b, rfl⟩, hy (D.ρ b) ⟨b, rfl⟩]
    have hw0 : (D.h (x - y) : B) = 0 := by rw [hhsub, hxy, sub_self]
    set w : D.P := x - y with hwdef
    have hws : star w ∈ commutant D.P (Set.range ⇑D.ρ) := hcstar _ hw
    have hp : w + star w = 0 := by
      refine hcore _ (fun m hm => ?_) ?_ ?_
      · rw [mul_add, add_mul, hw m hm, hws m hm]
      · show star (w + star w) = w + star w
        rw [star_add, star_star, add_comm]
      · rw [hhadd, hhstar, hw0, star_zero, add_zero]
    have hq : (Complex.I • (w - star w)) = 0 := by
      refine hcore _ (fun m hm => ?_) ?_ ?_
      · rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hw m hm, hws m hm]
      · show star (Complex.I • (w - star w)) = Complex.I • (w - star w)
        rw [star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
          neg_smul, ← smul_neg, neg_sub]
      · rw [hhsmul, hhsub, hhstar, hw0, star_zero, sub_zero, smul_zero]
    have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hws' : star w = w := by
      have := (smul_eq_zero.mp hq).resolve_left hIne
      have h2 : w - star w = 0 := this
      exact (sub_eq_zero.mp h2).symm
    have hww : (2 : ℂ) • w = 0 := by
      rw [two_smul]
      rw [hws'] at hp
      exact hp
    have hw00 : w = 0 := (smul_eq_zero.mp hww).resolve_left two_ne_zero
    exact sub_eq_zero.mp hw00
  tfae_finish

/-- **172VIII** (`nmiu-ncp-extreme`, dils.tex:6520, Corollary): every
nmiu-map (as an ncp-map) is ncp-extreme.

**The thesis's own proof is `nmiu_ncp_extreme_paschke` below** — 172IX,
dils.tex:6523: `(ℬ, ϱ, id)` is a Paschke dilation of `ϱ` and `id` is
injective, so **172III** `ncp_extreme_paschke` applies.  That route needs
`[VonNeumannAlgebra]` on both algebras (172III does, and a Paschke dilation
needs it to exist at all), which is the corollary's own setting.

This declaration is the **strictly stronger generalisation**: no
`[VonNeumannAlgebra]` binders, so it holds for arbitrary C\*-algebras.  It
is kept, with its direct argument, precisely because the thesis's route
cannot reach it; the printed route is discharged by
`nmiu_ncp_extreme_paschke`. -/
theorem nmiu_ncp_extreme (ϱ : NMIUMap A B) (φ : NCPMap A B)
    (hφ : ∀ a, φ a = ϱ a) :
    NCPExtreme φ := by
  -- The author's proof (**172IX**) is `nmiu_ncp_extreme_paschke` below; it
  -- carries `[VonNeumannAlgebra]` on both algebras, which this statement does
  -- not.  We argue directly, by strict convexity of `b ↦ b* b` with Choi's
  -- inequality **34XVIII**.1.
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

/-- **172VIII** (`nmiu-ncp-extreme`, dils.tex:6520, Corollary) **in the
thesis's own setting** — both algebras von Neumann — **by the thesis's own
proof**, **172IX** (dils.tex:6523): "Easy: `(ℬ, ϱ, id)` is a Paschke dilation
of `ϱ` and `id` is injective."

Both halves are immediate.  The universal property of `(ℬ, ϱ, id)` holds
because the mediating map for a competing triple `(𝒫′, ϱ′, h′)` is forced to
be `h′` itself by `id ∘ σ = h′`, and `h′` does satisfy `h′ ∘ ϱ′ = ϱ`; and
`id` is injective on every subset.  **172III** `ncp_extreme_paschke`, clause
1 ⇒ 3, then gives ncp-extremity.

`nmiu_ncp_extreme` above is the same corollary without the
`[VonNeumannAlgebra]` binders — strictly stronger, and out of reach of this
route, which is why both are kept.  (Same shape as **157VII**
`phiT_reflects_nonneg` in `Paschke.lean`.) -/
theorem nmiu_ncp_extreme_paschke [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (ϱ : NMIUMap A B) (φ : NCPMap A B) (hφ : ∀ a, φ a = ϱ a) :
    NCPExtreme φ := by
  have hD : IsPaschkeDilationOf
      (⟨B, ‹VonNeumannAlgebra B›, ϱ, ncpId B⟩ : PaschkeTriple A B) ⇑φ := by
    refine ⟨fun a => (hφ a).symm, ?_⟩
    intro D' hD'
    refine ⟨D'.h, ⟨fun a => ?_, fun c => rfl⟩, ?_⟩
    · show (D'.h (D'.ρ a) : B) = ϱ a
      rw [hD' a, hφ a]
    · rintro σ ⟨-, hσ⟩
      exact DFunLike.ext _ _ fun c => hσ c
  refine ((ncp_extreme_paschke φ ⟨B, ‹VonNeumannAlgebra B›, ϱ, ncpId B⟩ hD).out 0 2).mp ?_
  intro x _ y _ hxy
  exact hxy

/-- **172X** (dils.tex:6528, Theorem): every pure ncp-map is
ncp-extreme.

**172XI** is the proof, transcribed with two divergences.

*(i)* Where the thesis quotes proc.tex 100III `pure-fundamental` for the
factorisation `φ = c ∘ h_p` through a **standard** corner, `IsPureMap` only
supplies an abstract one; `pext_corner_iso` (i.e. **169IV** plus the
uniqueness half of **169II**) supplies the isomorphism `v` with
`v ∘ h_p = h`, and `pext_dilation_target_iso` carries the Paschke dilation
of `h_p` given by **171II** `paschke_corner` across it.  The composite with
the filter `c` is then a Paschke dilation of `φ` by **169XI**.1
`dils_filter_basics_1`, exactly as the thesis says.

*(ii)* The injectivity computation is shorter than the thesis's.  For `t`,
`t'` in the commutant of `ϱ(A)` — which, `ϱ = h_{⌈⌈p⌉⌉}` being surjective,
means central in `⌈⌈p⌉⌉A⌈⌈p⌉⌉` and hence (as `⌈⌈p⌉⌉` is central) central in
`A` — the hypothesis gives `p(t−t')p = 0`, so `x = t − t'` satisfies
`px = 0` and therefore `pyx = pxy = 0` for **every** `y`, whence
`⌈⌈p⌉⌉x = 0` by **68I** `cceil_fundamental` (here
`pcorner_forall_mul_eq_zero_iff`) and `x = ⌈⌈p⌉⌉x = 0`.  The thesis instead
argues `p ≤ 1 − ⌈t⌉`, `⌈⌈p⌉⌉ ≤ ⌈⌈p⌉⌉ − ⌈t⌉`, `t ≤ ⌈t⌉ = 0`, which needs
`t ≥ 0` (so a positive-part split for the difference) and the centrality of
`⌈t⌉`; neither is needed above. -/
theorem pure_ncp_extreme [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) (hpure : IsPureMap φ) :
    NCPExtreme φ := by
  classical
  obtain ⟨C, iC, iP, iS, h, c, hcorner, hfilter, hcomp⟩ := hpure
  letI := iC; letI := iP; letI := iS
  obtain ⟨a, hca⟩ := hcorner
  obtain ⟨hp, v, u, hval, hvhp, hvu, huv⟩ := pext_corner_iso h a hca
  set p : A := floor a with hpdef
  letI : VonNeumannAlgebra (cornerSet A (cceil p)) :=
    cornerSet_vonNeumannAlgebra A (cceil p)
  obtain ⟨ρ₀, h₀, hρval, hh₀val, hD₀⟩ := paschke_corner p hp hval
  -- transport the dilation of `h_p` along `v`
  obtain ⟨H₁, hH₁⟩ := exists_ncpComp v h₀
  have hD₁ : IsPaschkeDilationOf
      ⟨cornerSet A (cceil p), cornerSet_vonNeumannAlgebra A (cceil p), ρ₀, H₁⟩
      (fun x => v (hp x)) :=
    pext_dilation_target_iso ⇑hp _ hD₀ v u hvu huv H₁ hH₁
  have hvhp' : (fun x => v (hp x)) = ⇑h := funext hvhp
  rw [hvhp'] at hD₁
  -- compose with the filter `c`
  obtain ⟨H₂, hH₂, hD₂⟩ := dils_filter_basics_1 h _ hD₁ c hfilter
  have hcomp' : (fun x => c (h x)) = ⇑φ := (funext hcomp).symm
  rw [hcomp'] at hD₂
  refine ((ncp_extreme_paschke φ
    ⟨cornerSet A (cceil p), cornerSet_vonNeumannAlgebra A (cceil p), ρ₀, H₂⟩
    hD₂).out 1 2).mp ?_
  -- injectivity of `c ∘ v ∘ h₀` on the commutant
  have hcinj : Function.Injective ⇑c := dils_filters_injective c hfilter
  have hvinj : Function.Injective ⇑v := by
    intro z z' hzz
    rw [← huv z, ← huv z', hzz]
  have hzc : ∀ b : A, cceil p * b = b * cceil p := (cceil_isLeast p).1.2.1
  have hzp : cceil p * p = p := (cceil_isLeast p).1.2.2
  intro t ht t' ht' heq
  -- `h₀ t = h₀ t'`
  have h1 : (h₀ t : cornerSet A p) = h₀ t' := by
    refine hvinj (hcinj ?_)
    have e1 : (H₂ t : B) = c (v (h₀ t)) := by rw [hH₂, hH₁]
    have e2 : (H₂ t' : B) = c (v (h₀ t')) := by rw [hH₂, hH₁]
    rw [← e1, ← e2]
    exact heq
  set z : A := cceil p with hzdef
  have hzproj : IsStarProjection z := (cceil_isLeast p).1.1
  have hz2 : z * z = z := hzproj.isIdempotentElem.eq
  have hpproj : IsStarProjection p := cornerSet.proj p
  have hp2 : p * p = p := hpproj.isIdempotentElem.eq
  -- elements of the corner absorb `⌈⌈p⌉⌉` on both sides
  have hzabs : ∀ s : cornerSet A z, z * s.1 = s.1 ∧ s.1 * z = s.1 := by
    intro s
    have h2 : z * s.1 * z = s.1 := s.2
    have hl : z * s.1 = s.1 := by
      calc z * s.1 = z * (z * s.1 * z) := by rw [h2]
        _ = (z * z) * s.1 * z := by noncomm_ring
        _ = z * s.1 * z := by rw [hz2]
        _ = s.1 := h2
    refine ⟨hl, ?_⟩
    calc s.1 * z = (z * s.1) * z := by rw [hl]
      _ = s.1 := h2
  -- an element of the commutant of `ϱ(A)` is central in `A`
  have hcentral : ∀ s : cornerSet A z,
      s ∈ commutant (cornerSet A z) (Set.range ⇑ρ₀) → ∀ b : A, s.1 * b = b * s.1 := by
    intro s hs b
    obtain ⟨hzs, hsz⟩ := hzabs s
    have hcomm := hs (ρ₀ b) ⟨b, rfl⟩
    have hcomm' : s.1 * (z * b * z) = (z * b * z) * s.1 := by
      have h6 := congrArg (fun y : cornerSet A z => y.1) hcomm
      simp only [cornerSet.val_mul, hρval] at h6
      exact h6.symm
    have h3 : s.1 * (z * b * z) = s.1 * b := by
      calc s.1 * (z * b * z) = (s.1 * z) * (b * z) := by noncomm_ring
        _ = s.1 * (b * z) := by rw [hsz]
        _ = s.1 * (z * b) := by rw [hzc b]
        _ = (s.1 * z) * b := by noncomm_ring
        _ = s.1 * b := by rw [hsz]
    have h4 : (z * b * z) * s.1 = b * s.1 := by
      calc z * b * z * s.1 = (z * b) * (z * s.1) := by noncomm_ring
        _ = (z * b) * s.1 := by rw [hzs]
        _ = (b * z) * s.1 := by rw [← hzc b]
        _ = b * (z * s.1) := by noncomm_ring
        _ = b * s.1 := by rw [hzs]
    rw [← h3, ← h4, hcomm']
  set x : A := t.1 - t'.1 with hxdef
  have hxc : ∀ b : A, x * b = b * x := by
    intro b
    rw [hxdef, sub_mul, mul_sub, hcentral t ht.1 b, hcentral t' ht'.1 b]
  -- `p x = 0`
  have hpx : p * x = 0 := by
    have h2 : p * t.1 * p = p * t'.1 * p := by
      have h5 := congrArg (fun y : cornerSet A p => y.1) h1
      rw [hh₀val, hh₀val] at h5
      exact h5
    have h3 : p * x * p = 0 := by
      rw [hxdef, mul_sub, sub_mul, h2, sub_self]
    have h4 : p * x * p = p * x := by
      calc p * x * p = p * (x * p) := by noncomm_ring
        _ = p * (p * x) := by rw [hxc p]
        _ = (p * p) * x := by noncomm_ring
        _ = p * x := by rw [hp2]
    rw [← h4, h3]
  -- `⌈⌈p⌉⌉ x = 0`, hence `x = 0`
  have hall : ∀ y : A, p * y * x = 0 := by
    intro y
    calc p * y * x = p * (y * x) := by noncomm_ring
      _ = p * (x * y) := by rw [← hxc y]
      _ = (p * x) * y := by noncomm_ring
      _ = 0 := by rw [hpx, zero_mul]
  letI : VonNeumannAlgebra (cornerSet A p) := cornerSet_vonNeumannAlgebra A p
  have hzx : z * x = 0 := (pcorner_forall_mul_eq_zero_iff hval x).mp hall
  have hxz : z * x = x := by
    rw [hxdef, mul_sub, (hzabs t).1, (hzabs t').1]
  have hx0 : x = 0 := by rw [← hxz, hzx]
  exact Subtype.ext (sub_eq_zero.mp hx0)

/-- **172XII** (`ncp-extreme-comp`, dils.tex:6552, Corollary): every
ncp-map is the composition of two ncp-extreme maps. -/
theorem ncp_extreme_comp [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (φ : NCPMap A B) :
    ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C)
      (_ : StarOrderedRing C) (ψ₁ : NCPMap A C) (ψ₂ : NCPMap C B),
      NCPExtreme ψ₁ ∧ NCPExtreme ψ₂ ∧ ∀ a, φ a = ψ₂ (ψ₁ a) := by
  classical
  obtain ⟨M⟩ := existence_paschke φ
  set D : PaschkeTriple A B :=
    ⟨(Ba B M.X)ᵐᵒᵖ,
      @vonNeumannAlgebra_mulOpposite (Ba B M.X) _ _ _
        (ba_vonNeumannAlgebra M.selfDual), M.ρ, M.h⟩ with hDdef
  have hD : IsPaschkeDilationOf D ⇑φ := existence_paschke_5 φ M
  let _ := D.vn
  obtain ⟨ϱ, hϱ⟩ := pcorner_exists_ncpOfNmiu D.ρ
  exact ⟨D.P, inferInstance, inferInstance, inferInstance, ϱ, D.h,
    nmiu_ncp_extreme D.ρ ϱ hϱ,
    pure_ncp_extreme D.h (dils_examples_pure_2 φ D hD),
    fun a => by rw [hϱ, hD.1 a]⟩

end Extreme

end Theses.B.Dils
