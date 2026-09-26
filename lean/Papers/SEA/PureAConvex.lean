/-
Copyright: the authors of the theses formalisation.

# SEA §5–6: pure a-convexity and associative sequential products

A. Westerbaan, B. Westerbaan, J. van de Wetering, *The three types of normal
sequential effect algebras*, Quantum 2020 (arXiv:2004.12749),
`../papers/2004.12749/second.tex`, §5 (`sec:purea-convex`, points
**SEA 61**–**SEA 68**) and §6 (`sec:assoc`, points **SEA 69**–**SEA 73**).

Conventions: `Papers/README.md`; plan: `Papers/SEA/PLAN.md`.

* The representation theorem of directed-complete effect monoids (SEA 35, cited
  from OAP 57 + 69) is used unconditionally: `sea35` (`Papers/SEA/Discharge.lean`,
  proved from `Papers.OAP.oap69_corner`).  The declarations of §4 that took it
  as a hypothesis `h35 : SEA35` are restated here without it
  (`sea51_division_unconditional`, …, `sea60_finite_boolean_unconditional`).
* §5: purely a-convex SEAs and a-convex factors (61), the splitting of an
  a-convex normal SEA into a convex and a purely a-convex part (62, 63), the
  main theorem `E ≅ B ⊕ E_c ⊕ E_ac` (64), convex sub-SEAs (65), commuting
  halves (66–68).
* §6: associative SEAs (69–73); SEA 73 uses OAP 71 (`Papers.OAP.oap71`) and
  is false as printed for the one-element SEA (`sea73_false_as_printed`),
  proved for non-trivial `E` (`sea73_assoc_factor`).
-/
import Papers.SEA.AlmostConvex
import Papers.SEA.Discharge

namespace Papers.SEA

open Theses.B.Eff
open scoped unitInterval

universe u v w

/-! ## The declarations of §4 that took `SEA35`, unconditionally -/

section Unconditional

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 51** (`lem:uniquedivision`, second.tex:1255, Lemma),
unconditionally: if `⌊a⌋ = 0` and `n > 0` there is a unique `a'` with
`a = n a'`, and `a' ∈ {a}''`.  `sea51_division` with `SEA35` discharged by
**OAP 69** (`sea35`). -/
theorem sea51_division_unconditional {a : E} (ha : floor a = 0) {n : ℕ} (hn : 0 < n) :
    ∃ a' ∈ bicommutant ({a} : Set E), PCM.IsSumOf (List.replicate n a') a ∧
      ∀ b : E, PCM.IsSumOf (List.replicate n b) a → b = a' :=
  sea51_division sea35 ha hn

/-- **SEA 52.4** (`prop:add-into-nsea`, second.tex:1297, Proposition),
unconditionally: additive `φ, ψ : [0,1] → E` agreeing at some `λ ∈ (0,1)`
are equal.  `sea52_4_unique` with `SEA35` discharged by **OAP 69**
(`sea35`). -/
theorem sea52_4_unique_unconditional {φ ψ : I → E} (hφ : IsAdditive φ) (hψ : IsAdditive ψ)
    {l : I} (hl0 : 0 < (l : ℝ)) (hl1 : (l : ℝ) < 1) (h : φ l = ψ l) : φ = ψ :=
  sea52_4_unique sea35 hφ hψ hl0 hl1 h

/-- **SEA 55** (`prop:a-convex-from-phi`, second.tex:1465, Proposition),
unconditionally: a unital additive `φ : [0,1] → E` gives the a-convex action
`λ ·_φ a = a ⊙ φ(λ)`, and an a-convex action is of this form iff
`λ · a = a ⊙ (λ · 1)`.  `sea55_aconvex_from_phi` with `SEA35` discharged by
**OAP 69** (`sea35`). -/
theorem sea55_aconvex_from_phi_unconditional :
    (∀ (φ : I → E) (hφ : IsAdditive φ) (h1 : φ 1 = 1) (l : I) (a : E),
      (actOfPhi sea35 hφ h1).act l a = a ⊙ φ l) ∧
    ∀ A : AConvexAction E,
      (∃ (φ : I → E) (hφ : IsAdditive φ) (h1 : φ 1 = 1), A = actOfPhi sea35 hφ h1) ↔
        ∀ (l : I) (a : E), A.act l a = a ⊙ A.act l 1 :=
  sea55_aconvex_from_phi sea35

/-- **SEA 57** (`thm-a-convex-thm`, second.tex:1539, Theorem), unconditionally:
the seven characterisations of convexity of a normal SEA are equivalent.
`sea57_convex_tfae` with `SEA35` discharged by **OAP 69** (`sea35`). -/
theorem sea57_convex_tfae_unconditional :
    List.TFAE [IsConvex E,
      (∃ A : AConvexAction E, ∀ A' : AConvexAction E, A' = A),
      (∃ h : E, IsCentral h ∧ IsHalf h),
      (∃! h : E, IsHalf h),
      (∀ a : E, ∃! b : E, ∃ hb : Perp b b, ovee b b hb = a),
      (IsAConvex E ∧ ∀ A : AConvexAction E, ∀ (l : I) (a : E), a ∈ center E →
        A.act l a ∈ center E),
      IsConvex (centerSub E).carrier] :=
  sea57_convex_tfae sea35

/-- **SEA 57** (`thm-a-convex-thm`, second.tex:1539, Theorem), "moreover",
unconditionally: in a convex normal SEA every a-convex action satisfies
`λ · a = a ⊙ (λ · 1)`.  `sea57_moreover` with `SEA35` discharged by
**OAP 69** (`sea35`). -/
theorem sea57_moreover_unconditional (hc : IsConvex E) (A : AConvexAction E) (l : I) (a : E) :
    A.act l a = a ⊙ A.act l 1 :=
  sea57_moreover sea35 hc A l a

/-- **SEA 58** (`thm:a-convexthm`, second.tex:1768, Theorem), unconditionally:
the idempotents `p` with `p ⊙ E` a-convex have a greatest element `p₀`, which
is central with `p₀⊥ ⊙ E` Boolean.  `sea58_maximal` with `SEA35` discharged
by **OAP 69** (`sea35`). -/
theorem sea58_maximal_unconditional :
    ∃ p0 : E, (IsIdempotent p0 ∧ IsAConvex (Downset p0)) ∧
      (∀ q : E, IsIdempotent q → IsAConvex (Downset q) → q ≼ p0) ∧
      IsCentral p0 ∧ IsBooleanIdempotent (orth p0) :=
  sea58_maximal sea35

/-- **SEA 59** (`thm:SEAsplitupinconvexandsharp`, second.tex:1856, Theorem),
unconditionally: `E ≅ E₁ ⊕ E₂` with `E₁` a-convex and `E₂` a complete Boolean
algebra.  `sea59_split` with `SEA35` discharged by **OAP 69** (`sea35`). -/
theorem sea59_split_unconditional :
    ∃ (E1 E2 : Type u) (_ : EffectAlgebra E1) (_ : SEAlgebra E1) (_ : EffectAlgebra E2)
      (_ : SEAlgebra E2), IsAConvex E1 ∧
      (∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
        Nonempty (@SEAIso E2 B _ (booleanEffectAlgebra B) _ (boolSEA B))) ∧
      Nonempty (@SEAIso E (E1 × E2) _ _ _ (prodSEA E1 E2)) :=
  sea59_split sea35

end Unconditional

/-- **SEA 60** (`cor:finite-Boolean`, second.tex:1869, Corollary),
unconditionally: a finite SEA is a Boolean algebra.  `sea60_finite_boolean`
with `SEA35` discharged by **OAP 69** (`sea35`). -/
theorem sea60_finite_boolean_unconditional (E : Type u) [EffectAlgebra E] [SEAlgebra E]
    [Finite E] :
    ∃ (B : Type u) (_ : BooleanAlgebra B),
      Nonempty (@SEAIso E B _ (booleanEffectAlgebra B) _ (boolSEA B)) :=
  sea60_finite_boolean sea35 E

/-! ## Preliminaries: isomorphisms, corners, restricted actions -/

namespace SEAIso

variable {E : Type u} {F : Type v} {G : Type w} [EffectAlgebra E] [EffectAlgebra F]
  [EffectAlgebra G] [SEAlgebra E] [SEAlgebra F] [SEAlgebra G]

/-- Composition of SEA isomorphisms. -/
def trans (f : SEAIso E F) (g : SEAIso F G) : SEAIso E G where
  toEquiv := f.toEquiv.trans g.toEquiv
  map_one := by
    show g.toFun (f.toFun 1) = 1; rw [f.map_one, g.map_one]
  perp_iff := fun a b => (g.perp_iff _ _).trans (f.perp_iff a b)
  map_ovee := fun a b h h' => by
    show g.toFun (f.toFun (ovee a b h)) = ovee (g.toFun (f.toFun a)) (g.toFun (f.toFun b)) h'
    rw [f.map_ovee a b h ((f.perp_iff a b).mpr h)]
    exact g.map_ovee _ _ _ _
  map_seq := fun a b => by
    show g.toFun (f.toFun (a ⊙ b)) = g.toFun (f.toFun a) ⊙ g.toFun (f.toFun b)
    rw [f.map_seq, g.map_seq]

end SEAIso

/-- The direct sum of two SEA isomorphisms. -/
def SEAIso.prodMap {E E' F F' : Type u} [EffectAlgebra E] [EffectAlgebra E'] [EffectAlgebra F]
    [EffectAlgebra F'] [SEAlgebra E] [SEAlgebra E'] [SEAlgebra F] [SEAlgebra F']
    (f : SEAIso E E') (g : SEAIso F F') : SEAIso (E × F) (E' × F') where
  toEquiv := f.toEquiv.prodCongr g.toEquiv
  map_one := Prod.ext f.map_one g.map_one
  perp_iff := fun a b => and_congr (f.perp_iff a.1 b.1) (g.perp_iff a.2 b.2)
  map_ovee := fun _ _ _ h' => Prod.ext (f.map_ovee _ _ _ h'.1) (g.map_ovee _ _ _ h'.2)
  map_seq := fun _ _ => Prod.ext (f.map_seq _ _) (g.map_seq _ _)

/-- The symmetry `E ⊕ F ≅ F ⊕ E` of SEAs. -/
def SEAIso.prodComm (E F : Type u) [EffectAlgebra E] [EffectAlgebra F] [SEAlgebra E]
    [SEAlgebra F] : SEAIso (E × F) (F × E) where
  toEquiv := Equiv.prodComm E F
  map_one := rfl
  perp_iff := fun _ _ => And.comm
  map_ovee := fun _ _ _ _ => rfl
  map_seq := fun _ _ => rfl

/-- An a-convex action restricts to every downset `[0,q]` (`λ · a ≼ a`). -/
def AConvexAction.restrict {E : Type u} [EffectAlgebra E] (A : AConvexAction E) (q : E) :
    AConvexAction (Downset q) where
  act l a := ⟨A.act l a.1, le_trans' (A.act_le l a.1) a.2⟩
  act_act l m a := Subtype.ext (A.act_act l m a.1)
  act_add l m n a h := by
    obtain ⟨hp, e⟩ := A.act_add l m n a.1 h
    exact ⟨⟨hp, by rw [e]; exact le_trans' (A.act_le n a.1) a.2⟩, Subtype.ext e⟩
  one_act a := Subtype.ext (A.one_act a.1)

section CornerCentre

variable {E : Type u} [EffectAlgebra E] [SEAlgebra E]

/-- For a central idempotent `q`, an element of the corner `q ⊙ E` that is
central in the corner is central in `E`: `c ⊙ b = c ⊙ (q ⊙ b)` and
`b ⊙ c = (q ⊙ b) ⊙ c`. -/
theorem isCentral_of_corner {q : E} (hq : IsIdempotent q) (hqc : IsCentral q) (c : Downset q)
    (hc : @IsCentral _ _ (cornerSEA hq) c) : IsCentral c.1 := by
  intro b
  have hcq : c.1 ⊙ q = c.1 := ((sea17_5 hq c.1).2.1).mp c.2
  have hqc' : q ⊙ c.1 = c.1 := ((sea17_5 hq c.1).1).mp c.2
  have e1 : c.1 ⊙ b = c.1 ⊙ (q ⊙ b) := by rw [(hqc c.1).symm.assoc b, hcq]
  have e2 : b ⊙ c.1 = (q ⊙ b) ⊙ c.1 := by
    conv_lhs => rw [← hqc']
    rw [(hqc b).symm.assoc c.1, hqc b]
  have e3 : c.1 ⊙ (q ⊙ b) = (q ⊙ b) ⊙ c.1 :=
    congrArg Subtype.val (hc ⟨q ⊙ b, seq_le_left q b⟩)
  exact e1.trans (e3.trans e2.symm)

/-- An element of a corner that is central in `E` is central in the corner. -/
theorem corner_isCentral {q : E} (hq : IsIdempotent q) (c : Downset q) (hc : IsCentral c.1) :
    @IsCentral _ _ (cornerSEA hq) c :=
  fun b => Subtype.ext (hc b.1)

end CornerCentre

/-! ## §5: Pure a-convexity -/

/-- **SEA 61** (second.tex:1887, Definition): an a-convex SEA `E` is *purely
a-convex* when its centre `Z(E)` is Boolean (every central element is an
idempotent). -/
def IsPurelyAConvex (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Prop :=
  IsAConvex E ∧ ∀ a ∈ center E, IsIdempotent a

/-- **SEA 61** (second.tex:1887, Definition): an a-convex SEA `E` is an
*a-convex factor* when `Z(E) = {0, 1}`. -/
def IsAConvexFactor (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Prop :=
  IsAConvex E ∧ center E = {0, 1}

section Sec5

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 62** (`prop:a-convexsplitinconvexandsharp`, second.tex:1895,
Proposition): in a normal a-convex SEA `E` there is a central idempotent `p`
with `p ⊙ E` convex and `p⊥ ⊙ E` purely a-convex.  Proof as printed: `Z(E)`
is a commutative normal SEA, hence a directed-complete effect monoid, so
SEA 35 (**OAP 69**, `sea35`) gives an idempotent `p ∈ Z(E)` with `p ⊙ Z(E)`
convex and `p⊥ ⊙ Z(E)` Boolean; `Z(p⊥ ⊙ E) = p⊥ ⊙ Z(E)`
(`isCentral_of_corner`) is Boolean, and `½ · p` computed in `p ⊙ Z(E)` is a
central half of `p` in `p ⊙ E`, which is therefore convex (SEA 57, 3 ⇒ 1).
The a-convex action of `p⊥ ⊙ E` is the restriction of that of `E`. -/
theorem sea62_split (hE : IsAConvex E) :
    ∃ (p : E) (hp : IsIdempotent p), IsCentral p ∧ IsConvex (Downset p) ∧
      @IsPurelyAConvex (Downset (orth p)) _ (cornerSEA hp.compl) := by
  obtain ⟨A⟩ := hE
  let Z := centerSub E
  have hZc : IsCommutativeSEA Z.carrier := fun a b => Subtype.ext (a.2 b.1 trivial)
  let _iM : EffectMonoid Z.carrier := seaToEM hZc
  have hdc : @DirectedComplete _ (seaToEM hZc).toEffectAlgebra :=
    (show DirectedComplete Z.carrier from NormalSEA.directedComplete)
  obtain ⟨p, hp, ⟨C⟩, hbool, -⟩ := @sea35 Z.carrier (seaToEM hZc) hdc
  have hpid : IsIdempotent p.1 := congrArg Subtype.val hp
  have hpc : IsCentral p.1 := fun b => p.2 b trivial
  -- a central half of `p` in the corner `p ⊙ E`
  let k := (AConvexAction.ofConvex C).act halfI 1
  obtain ⟨hk, ek⟩ := isSumOf_two_iff.mp ((AConvexAction.ofConvex C).half_sum 1)
  have hkk : Perp k.1.1 k.1.1 := hk.1
  have ek' : ovee k.1.1 k.1.1 hkk = p.1 := congrArg (fun z => z.1.1) ek
  let _ : NormalSEA (Downset p.1) := cornerNormalSEA hpid
  let k' : Downset p.1 := ⟨k.1.1, by rw [← ek']; exact left_le_ovee hkk⟩
  have hhalf : IsHalf k' := ⟨⟨hkk, by rw [ek']; exact le_refl' _⟩, Subtype.ext ek'⟩
  have hk'c : IsCentral k' := fun b => Subtype.ext (k.1.2 b.1 trivial)
  have hconv : IsConvex (Downset p.1) :=
    sea57_2_1 sea35 (sea57_5_2 sea35 (sea57_3_5 ⟨k', hk'c, hhalf⟩))
  refine ⟨p.1, hpid, hpc, hconv, ⟨A.restrict (orth p.1)⟩, fun c hc => ?_⟩
  have hc' : IsCentral c.1 := isCentral_of_corner hpid.compl hpc.orth_central c hc
  let z : Z.carrier := ⟨c.1, mem_centerSub.mpr hc'⟩
  have hz : z ≼ orth p := (subEA_le_iff (T := Z.toSubEffectAlgebra)).mpr c.2
  exact Subtype.ext (show c.1 ⊙ c.1 = c.1 from congrArg Subtype.val (hbool z hz))

/-- **SEA 63** (`cor-aconvex`, second.tex:1914, Corollary): for a normal
a-convex SEA `E`, `E` is purely a-convex iff the only central idempotent `p`
with `p ⊙ E` convex is `p = 0`.  Proof as printed: (1 ⇒ 2) the half of `p` in
the convex `p ⊙ E` is central there (SEA 57), hence in `E`
(`isCentral_of_corner`), hence idempotent and self-summable, hence `0`;
(2 ⇒ 1) SEA 62 with `p = 0`. -/
theorem sea63_purely_iff (hE : IsAConvex E) :
    IsPurelyAConvex E ↔
      ∀ p : E, IsIdempotent p → IsCentral p → IsConvex (Downset p) → p = 0 := by
  constructor
  · rintro ⟨-, hZ⟩ p hp hpc hconv
    let _ : NormalSEA (Downset p) := cornerNormalSEA hp
    obtain ⟨h, hhc, hh, eh⟩ := sea57_4_3 (sea57_1_4 hconv)
    have hc := isCentral_of_corner hp hpc h hhc
    have h0 : h.1 = 0 := idempotent_selfSummable_eq_zero (hZ h.1 hc) hh.1
    have e := congrArg Subtype.val eh
    simp only [downset_ovee_val, downset_one_val] at e
    rw [PCM.ovee_congr h0 h0 hh.1 (PCM.zero_perp 0), zero_ovee_eq] at e
    exact e.symm
  · intro H
    obtain ⟨p, hp, hpc, hconv, -, hZ⟩ := sea62_split hE
    have hp0 := H p hp hpc hconv
    refine ⟨hE, fun c hc => ?_⟩
    have hle : c ≼ orth p := by rw [hp0, eabasics_orth_zero]; exact le_one' c
    exact congrArg Subtype.val (hZ ⟨c, hle⟩ (corner_isCentral hp.compl ⟨c, hle⟩ hc))

end Sec5

/-- **SEA 64** (`thm:maintheorem`, second.tex:1950, Theorem; the main theorem):
for a normal SEA `E` there are a complete Boolean algebra `B`, a convex normal
SEA `E_c` and a purely a-convex (normal) SEA `E_ac` with
`E ≅ B ⊕ E_c ⊕ E_ac`.  Proof ("combining previous results"): SEA 58/59 split
`E ≅ p₀ ⊙ E ⊕ p₀⊥ ⊙ E` with `p₀ ⊙ E` a-convex and `p₀⊥ ⊙ E` a complete Boolean
algebra (SEA 44); SEA 62 splits `p₀ ⊙ E ≅ E_c ⊕ E_ac` (SEA 24).  Uses SEA 35
(**OAP 69**, `sea35`). -/
theorem sea64_main (E : Type u) [EffectAlgebra E] [NormalSEA E] :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B) (Ec : Type u) (_ : EffectAlgebra Ec)
      (_ : NormalSEA Ec) (Eac : Type u) (_ : EffectAlgebra Eac) (_ : NormalSEA Eac),
      IsConvex Ec ∧ IsPurelyAConvex Eac ∧
      Nonempty (letI := booleanEffectAlgebra B; letI := boolSEA B; SEAIso E (B × (Ec × Eac))) := by
  obtain ⟨p0, ⟨hp, hA⟩, -, hc, hb⟩ := sea58_maximal (E := E) sea35
  let i1 : NormalSEA (Downset p0) := cornerNormalSEA hp
  let i2 : NormalSEA (Downset (orth p0)) := cornerNormalSEA hp.compl
  have hBool : IsBooleanSEA (Downset (orth p0)) := (isBooleanIdempotent_iff hp.compl).mpr hb.2
  obtain ⟨B, cB, ⟨ψ⟩⟩ := boolean_normal_iso hBool
  obtain ⟨q, hq, hqc, hconv, hpure⟩ := sea62_split hA
  let _ : NormalSEA (Downset q) := cornerNormalSEA hq
  let _ : NormalSEA (Downset (orth q)) := cornerNormalSEA hq.compl
  refine ⟨B, cB, Downset q, _, inferInstance, Downset (orth q), _, inferInstance, hconv, hpure,
    ⟨?_⟩⟩
  letI := booleanEffectAlgebra B
  letI := boolSEA B
  exact ((sea24_centralSplit hp hc).trans ((sea24_centralSplit hq hqc).prodMap ψ)).trans
    (SEAIso.prodComm _ _)

section Sec5b

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 65** (second.tex:1974, Proposition): an a-convex normal SEA is the
(possibly non-disjoint) union of convex normal sub-SEAs: every `a` lies in
one.  Proof as printed: with `x = ½ · a`, let `q` be the convex-part
idempotent of `{x}''` (SEA 35); `x ≼ q` (`x ⊙ q⊥` is an idempotent below the
self-summable `x`, hence `0`); `y = ½ · q⊥` and a half `b` of `q` in `{x}''`
commute with `x` and each other (their products vanish), and
`D = {x, y, b}''` contains `a = x ⋁ x` and the central half `y ⋁ b` of `1`, so
`D` is convex (SEA 57, 3 ⇒ 1).  Uses SEA 35 (**OAP 69**, `sea35`). -/
theorem sea65_union (hE : IsAConvex E) (a : E) :
    ∃ T : SubNormalSEA E, a ∈ T.carrier ∧ IsConvex T.carrier := by
  obtain ⟨A⟩ := hE
  set x := A.act halfI a with hxdef
  obtain ⟨hxx, ex⟩ := isSumOf_two_iff.mp (A.half_sum a)
  have hxin : x ∈ commutant ({x} : Set E) := fun s hs => by
    rw [Set.mem_singleton_iff.mp hs]; exact commutes_refl x
  let _iM := bicommEM {x} (singleton_commuting x)
  obtain ⟨Q, hQ, ⟨C⟩, hbool, -⟩ :=
    @sea35 _ (bicommEM {x} (singleton_commuting x)) (bicommEM_dc {x} (singleton_commuting x))
  have hQid : IsIdempotent Q.1 := congrArg Subtype.val hQ
  let x' : (bicommutantSub ({x} : Set E)).carrier := ⟨x, subset_bicommutant _ rfl⟩
  -- `x ⊙ q⊥ = 0`, so `x ≼ q`
  have hxQc : Commutes x Q.1 := (Q.2 x hxin).symm
  let y0 := x' * orth Q
  have hy0 : y0.1 = x ⊙ orth Q.1 := rfl
  have hle0 : y0 ≼ orth Q := by
    refine (subEA_le_iff (T := (bicommutantSub ({x} : Set E)).toSubEffectAlgebra)).mpr ?_
    show x ⊙ orth Q.1 ≼ orth Q.1
    rw [hxQc.orth_r]; exact seq_le_left _ _
  have hid0 : IsIdempotent y0.1 := congrArg Subtype.val (hbool y0 hle0)
  have hperp0 : Perp y0.1 y0.1 := by
    rw [hy0]; exact perp_of_le (seq_le_left _ _) (seq_le_left _ _) hxx
  have hxQ : x ⊙ orth Q.1 = 0 := by rw [← hy0]; exact idempotent_selfSummable_eq_zero hid0 hperp0
  -- `y = ½ · q⊥` commutes with `x`
  set y := A.act halfI (orth Q.1) with hydef
  obtain ⟨hyy, ey⟩ := isSumOf_two_iff.mp (A.half_sum (orth Q.1))
  have hyle : y ≼ orth Q.1 := A.act_le _ _
  have hxy : Commutes x y := by
    have h0 : x ⊙ y = 0 := by
      have := seq_mono x hyle; rw [hxQ] at this; exact eq_zero_of_le_zero this
    show x ⊙ y = y ⊙ x; rw [h0, seq_zero_comm h0]
  -- a half `b` of `q` in `{x}''`
  let k := (AConvexAction.ofConvex C).act halfI 1
  obtain ⟨hk, ek⟩ := isSumOf_two_iff.mp ((AConvexAction.ofConvex C).half_sum 1)
  set b := k.1.1 with hbdef
  have hbb : Perp b b := hk.1
  have eb : ovee b b hbb = Q.1 := congrArg (fun z => z.1.1) ek
  have hbQ : b ≼ Q.1 := by rw [← eb]; exact left_le_ovee hbb
  have hby : Commutes b y := by
    have h1 : b ⊙ orth Q.1 = 0 := ((sea17_5 hQid b).2.2.1).mp hbQ
    have h0 : b ⊙ y = 0 := by
      have := seq_mono b hyle; rw [h1] at this; exact eq_zero_of_le_zero this
    show b ⊙ y = y ⊙ b; rw [h0, seq_zero_comm h0]
  have hxb : Commutes x b := (k.1.2 x hxin).symm
  -- `D = {x, y, b}''`
  let S : Set E := {x, y, b}
  have hS : ∀ u ∈ S, ∀ v ∈ S, Commutes u v := by
    have hc : ∀ u ∈ S, ∀ v ∈ S, u = x ∧ v = y ∨ u = x ∧ v = b ∨ u = y ∧ v = b ∨
        v = x ∧ u = y ∨ v = x ∧ u = b ∨ v = y ∧ u = b ∨ u = v := by
      intro u hu v hv
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> simp
    intro u hu v hv
    rcases hc u hu v hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | rfl
    · exact hxy
    · exact hxb
    · exact hby.symm
    · exact hxy.symm
    · exact hxb.symm
    · exact hby
    · exact commutes_refl u
  let T := bicommutantSub S
  have hxT : x ∈ T.carrier := subset_bicommutant S (by simp [S])
  have hyT : y ∈ T.carrier := subset_bicommutant S (by simp [S])
  have hbT : b ∈ T.carrier := subset_bicommutant S (by simp [S])
  refine ⟨T, ?_, ?_⟩
  · rw [← ex]; exact T.ovee_mem hxx hxT hxT
  · have hyb : Perp y b := perp_of_le hyle hbQ (PCM.perp_comm (EffectAlgebra.perp_orth Q.1))
    have hP : Perp (ovee y y hyy) (ovee b b hbb) := by
      rw [ey, eb]; exact PCM.perp_comm (EffectAlgebra.perp_orth Q.1)
    obtain ⟨h', e'⟩ := ovee_ovee_comm4 hyb hyb hyy hbb hP
    have e1 : ovee (ovee y b hyb) (ovee y b hyb) h' = 1 := by
      rw [e', PCM.ovee_congr ey eb hP (PCM.perp_comm (EffectAlgebra.perp_orth Q.1)),
        ovee_comm' _ (EffectAlgebra.perp_orth Q.1), EffectAlgebra.ovee_orth]
    let w : T.carrier := ⟨ovee y b hyb, T.ovee_mem hyb hyT hbT⟩
    have hw : IsHalf w := ⟨h', Subtype.ext e1⟩
    have hwc : IsCentral w := fun c => (sea28_bicommutant_commutative S hS).2 w c
    exact sea57_2_1 sea35 (sea57_5_2 sea35 (sea57_3_5 ⟨w, hwc, hw⟩))

end Sec5b

/-- **SEA 66** (second.tex:1987, Definition): a SEA has *commuting halves*
when `a | b` and `b = c ⋁ c` imply `a | c`. -/
def HasCommutingHalves (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Prop :=
  ∀ a b c : E, Commutes a b → (∃ h : Perp c c, ovee c c h = b) → Commutes a c

section Sec5c

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 67** (`prop:a-convexcommutewithhalves`, second.tex:1991,
Proposition): a normal a-convex SEA is convex iff it has commuting halves.
Proof as printed: (⇒) halves are unique, `c = b ⊙ (½ · 1)` with `½ · 1`
central (SEA 57), so `a | c`; (⇐) `½ · 1` is a half of `1`, which commutes
with every `a`, so `½ · 1` is central and `E` is convex (SEA 57, 3 ⇒ 1).  The
first half does not use a-convexity. -/
theorem sea67_convex_iff (hE : IsAConvex E) : IsConvex E ↔ HasCommutingHalves E := by
  constructor
  · intro hc a b c hab hcb
    obtain ⟨h, hhc, hh⟩ := sea57_4_3 (sea57_1_4 hc)
    obtain ⟨-, -, hu⟩ := sea57_3_5 ⟨h, hhc, hh⟩ b
    have e : c = b ⊙ h := by
      obtain ⟨d, hd, hdu⟩ := sea57_3_5 ⟨h, hhc, hh⟩ b
      exact (hdu c hcb).trans (hdu _ (isSumOf_two_iff.mp (isSumOf_seq_half hh b))).symm
    rw [e]; exact hab.seq (hhc a).symm
  · intro H
    obtain ⟨A⟩ := hE
    have hh : IsHalf (A.act halfI 1) := isSumOf_two_iff.mp (A.half_sum 1)
    have hc : IsCentral (A.act halfI 1) := fun a => (H a 1 _ (by
      show a ⊙ 1 = 1 ⊙ a; rw [seq_one, one_seq]) hh).symm
    exact sea57_2_1 sea35 (sea57_5_2 sea35 (sea57_3_5 ⟨_, hc, hh⟩))

/-- Commuting halves pass to corners (the operations of `p ⊙ E` are those of
`E`). -/
theorem hasCommutingHalves_corner (H : HasCommutingHalves E) {p : E} (hp : IsIdempotent p) :
    @HasCommutingHalves (Downset p) _ (cornerSEA hp) := by
  intro a b c hab ⟨hcc, ecb⟩
  exact Subtype.ext (H a.1 b.1 c.1 (congrArg Subtype.val hab) ⟨hcc.1, congrArg Subtype.val ecb⟩)

end Sec5c

/-- **SEA 68** (`thm:commuting-halves`, second.tex:2015, Theorem): a normal
SEA `E` with commuting halves is `E ≅ B ⊕ E_c` with `B` a complete Boolean
algebra and `E_c` a convex normal SEA.  Proof ("combining SEA 67 with
SEA 64"): in the splitting `E ≅ p₀ ⊙ E ⊕ p₀⊥ ⊙ E` of SEA 58/59 (the first
step of SEA 64), the a-convex part `p₀ ⊙ E` has commuting halves, hence is
convex by SEA 67 (so SEA 64's purely a-convex summand is not needed).  Uses
SEA 35 (**OAP 69**, `sea35`). -/
theorem sea68_split (E : Type u) [EffectAlgebra E] [NormalSEA E] (H : HasCommutingHalves E) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B) (Ec : Type u) (_ : EffectAlgebra Ec)
      (_ : NormalSEA Ec), IsConvex Ec ∧
      Nonempty (letI := booleanEffectAlgebra B; letI := boolSEA B; SEAIso E (B × Ec)) := by
  obtain ⟨p0, ⟨hp, hA⟩, -, hc, hb⟩ := sea58_maximal (E := E) sea35
  let i1 : NormalSEA (Downset p0) := cornerNormalSEA hp
  let i2 : NormalSEA (Downset (orth p0)) := cornerNormalSEA hp.compl
  have hBool : IsBooleanSEA (Downset (orth p0)) := (isBooleanIdempotent_iff hp.compl).mpr hb.2
  obtain ⟨B, cB, ⟨ψ⟩⟩ := boolean_normal_iso hBool
  have hconv : IsConvex (Downset p0) := (sea67_convex_iff hA).mpr (hasCommutingHalves_corner H hp)
  refine ⟨B, cB, Downset p0, _, inferInstance, hconv, ⟨?_⟩⟩
  letI := booleanEffectAlgebra B
  letI := boolSEA B
  have e1 : SEAIso (Downset p0) (Downset p0) :=
    { toEquiv := Equiv.refl _, map_one := rfl, perp_iff := fun _ _ => Iff.rfl,
      map_ovee := fun _ _ _ _ => rfl, map_seq := fun _ _ => rfl }
  exact ((sea24_centralSplit hp hc).trans (e1.prodMap ψ)).trans (SEAIso.prodComm _ _)

/-! ## §6: Associative sequential products -/

/-- A SEA is *associative* when `a ⊙ (b ⊙ c) = (a ⊙ b) ⊙ c` for all `a, b, c`
(second.tex:2037). -/
def IsAssociativeSEA (E : Type u) [EffectAlgebra E] [SEAlgebra E] : Prop :=
  ∀ a b c : E, a ⊙ (b ⊙ c) = (a ⊙ b) ⊙ c

/-- **SEA 69** (`prop:assoc-is-commutative`, second.tex:2055, Proposition): in
an associative SEA every idempotent is central.  Proof as printed:
`p⊥ ⊙ a ≼ p⊥` gives `0 = (p⊥ ⊙ a) ⊙ p = p⊥ ⊙ (a ⊙ p)`, so `p⊥ | a ⊙ p` and
`p | a ⊙ p`; likewise `p | a ⊙ p⊥`; so `p | a ⊙ p ⋁ a ⊙ p⊥ = a`. -/
theorem sea69_idempotent_central {E : Type u} [EffectAlgebra E] [SEAlgebra E]
    (hE : IsAssociativeSEA E) {p : E} (hp : IsIdempotent p) : IsCentral p := by
  intro a
  have k1 : (orth p ⊙ a) ⊙ p = 0 := by
    have h := ((sea17_5 hp.compl (orth p ⊙ a)).2.2.2).mp (seq_le_left _ _)
    rw [orth_orth] at h
    exact seq_zero_comm h
  have k2 : (p ⊙ a) ⊙ orth p = 0 := seq_zero_comm (((sea17_5 hp (p ⊙ a)).2.2.2).mp
    (seq_le_left _ _))
  have c1 : Commutes p (a ⊙ p) := by
    have h0 : orth p ⊙ (a ⊙ p) = 0 := by rw [hE]; exact k1
    have hc : Commutes (orth p) (a ⊙ p) := by
      show orth p ⊙ (a ⊙ p) = (a ⊙ p) ⊙ orth p; rw [h0, seq_zero_comm h0]
    have := hc.orth_l; rwa [orth_orth] at this
  have c2 : Commutes p (a ⊙ orth p) := by
    have h0 : p ⊙ (a ⊙ orth p) = 0 := by rw [hE]; exact k2
    show p ⊙ (a ⊙ orth p) = (a ⊙ orth p) ⊙ p; rw [h0, seq_zero_comm h0]
  obtain ⟨h, e⟩ := seq_split a p
  have := Commutes.ovee h c1 c2
  rwa [e] at this

section Sec6

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- **SEA 71** (`lem:multfloor`, second.tex:2095, Lemma): in a normal SEA,
`a ⊙ b = a` implies `a ⊙ ⌊b⌋ = a`.  Proof as printed, repaired: `a ⊙ b = a`
gives `a ⊙ b⊥ = 0`, so `a | b`; then `a ⊙ bⁿ = a` for all `n` (the print
detours through `b^{2ⁿ}`, writes `= 0` for `= a`, and reverses `bⁿ ≼ b^{2ⁿ}`;
induction on `n` needs neither), and `a ⊙ ⌊b⌋ = ⋀ₙ a ⊙ bⁿ = a` (S6 for
filtered infima, `seq_inf`). -/
theorem sea71_floor {a b : E} (h : a ⊙ b = a) : a ⊙ floor b = a := by
  have h0 : a ⊙ orth b = 0 := seq_eq_self_iff.mp h
  have hc : Commutes a b := by
    have hc' : Commutes a (orth b) := by
      show a ⊙ orth b = orth b ⊙ a; rw [h0, seq_zero_comm h0]
    exact hc'.of_orth_r
  have hpow := seq_seqPow_of h hc
  have hi := seq_inf a (floor_filtered b) (floor_isInf b)
  have himg : (a ⊙ ·) '' Set.range (seqPow b) = {a} := by
    ext y; constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact hpow n
    · intro hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact ⟨_, ⟨0, rfl⟩, hpow 0⟩
  rw [himg] at hi
  exact hi.unique ⟨fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact le_refl' _,
    fun y hy => hy a rfl⟩

/-- **SEA 72** (second.tex:2114, Lemma): if the only idempotents of a normal
SEA are `0` and `1`, then `a ⊙ b = 0` implies `a = 0` or `b = 0`.  Proof as
printed: `a ⊙ b⊥ = a`, so `a ⊙ ⌊b⊥⌋ = a` (SEA 71); `⌊b⊥⌋ = 0` gives `a = 0`,
and `⌊b⊥⌋ = 1` gives `b⊥ = 1`. -/
theorem sea72_no_zero_divisors (H : ∀ p : E, IsIdempotent p → p = 0 ∨ p = 1) {a b : E}
    (h : a ⊙ b = 0) : a = 0 ∨ b = 0 := by
  have h1 : a ⊙ orth b = a := seq_eq_zero_iff.mp h
  have h2 := sea71_floor h1
  rcases H _ (floor_idempotent (orth b)) with hf | hf
  · left; rw [← h2, hf, seq_zero]
  · right
    have hle : (1 : E) ≼ orth b := hf ▸ floor_le (orth b)
    have : orth b = 1 := le_antisymm' (le_one' _) hle
    rw [← orth_orth b, this, eabasics_orth_one]

end Sec6

/-! ### Simple elements of `[0,1]_{C(X)}` (for SEA 70)

The proof of SEA 70 approximates an element of `[0,1]_{C(X)}`, `X` extremally
disconnected, from below by "simple" elements `∑ λᵢ 1_{Uᵢ}` with `Uᵢ` clopen:
`g_n = ∑_{k < 2ⁿ} 2⁻ⁿ 1_{U_{(k+1)/2ⁿ}}` with `U_t = cl {f > t}` (clopen, as `X`
is extremally disconnected) increases to `f`, with `f - 2⁻ⁿ ≤ g_n ≤ f`. -/

section SimpleApprox

variable {X : Type u} [TopologicalSpace X]

/-- The level set `cl {x ; t < f x}`. -/
def lvl (f : C(X, ℝ)) (t : ℝ) : Set X := closure {x | t < f x}

theorem lvl_isClopen [ExtremallyDisconnected X] (f : C(X, ℝ)) (t : ℝ) : IsClopen (lvl f t) :=
  ⟨isClosed_closure,
    ExtremallyDisconnected.open_closure _ (isOpen_lt continuous_const f.continuous)⟩

theorem le_of_mem_lvl {f : C(X, ℝ)} {t : ℝ} {x : X} (hx : x ∈ lvl f t) : t ≤ f x :=
  closure_lt_subset_le continuous_const f.continuous hx

theorem mem_lvl {f : C(X, ℝ)} {t : ℝ} {x : X} (hx : t < f x) : x ∈ lvl f t := subset_closure hx

theorem lvl_anti {f : C(X, ℝ)} {s t : ℝ} (h : s ≤ t) : lvl f t ⊆ lvl f s :=
  closure_mono fun _ hx => lt_of_le_of_lt h hx

/-- `max 0 (min y c)`. -/
def clampR (y c : ℝ) : ℝ := max 0 (min y c)

theorem clampR_step (y a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    clampR y a + clampR (y - a) d = clampR y (a + d) := by
  simp only [clampR, max_def, min_def]
  split_ifs <;> linarith

theorem clampR_tele (y d : ℝ) (hd : 0 ≤ d) (N : ℕ) :
    ∑ k ∈ Finset.range N, clampR (y - k * d) d = clampR y (N * d) := by
  induction N with
  | zero => simp [clampR]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, clampR_step y _ d (by positivity) hd]
    push_cast; ring_nf

/-- The step `2⁻ⁿ 1_{U_{(k+1)/2ⁿ}}(x)`. -/
noncomputable def stepFn (f : C(X, ℝ)) (n k : ℕ) (x : X) : ℝ :=
  (lvl f (((k : ℝ) + 1) / 2 ^ n)).indicator (fun _ => (1 / 2 ^ n : ℝ)) x

theorem stepFn_nonneg (f : C(X, ℝ)) (n k : ℕ) (x : X) : 0 ≤ stepFn f n k x := by
  unfold stepFn Set.indicator; split_ifs <;> positivity

theorem stepFn_le (f : C(X, ℝ)) (n k : ℕ) (x : X) : stepFn f n k x ≤ 1 / 2 ^ n := by
  unfold stepFn Set.indicator; split_ifs <;> first | exact le_rfl | positivity

theorem stepFn_lower (f : C(X, ℝ)) (n k : ℕ) (x : X) :
    clampR (f x - 1 / 2 ^ n - k * (1 / 2 ^ n)) (1 / 2 ^ n) ≤ stepFn f n k x := by
  have hd : (0 : ℝ) < 1 / 2 ^ n := by positivity
  unfold stepFn Set.indicator
  split_ifs with hx
  · simp only [clampR, max_def, min_def]; split_ifs <;> linarith
  · have : ¬ (((k : ℝ) + 1) / 2 ^ n < f x) := fun h => hx (mem_lvl h)
    push Not at this
    have e : ((k : ℝ) + 1) / 2 ^ n = 1 / 2 ^ n + k * (1 / 2 ^ n) := by ring
    rw [e] at this
    simp only [clampR, max_def, min_def]; split_ifs <;> linarith

theorem stepFn_upper (f : C(X, ℝ)) (n k : ℕ) (x : X) :
    stepFn f n k x ≤ clampR (f x - k * (1 / 2 ^ n)) (1 / 2 ^ n) := by
  have hd : (0 : ℝ) < 1 / 2 ^ n := by positivity
  unfold stepFn Set.indicator
  split_ifs with hx
  · have h := le_of_mem_lvl hx
    have e : ((k : ℝ) + 1) / 2 ^ n = 1 / 2 ^ n + k * (1 / 2 ^ n) := by ring
    rw [e] at h
    simp only [clampR, max_def, min_def]; split_ifs <;> linarith
  · simp only [clampR, max_def, min_def]; split_ifs <;> linarith

/-- `∑_{k < m} 2⁻ⁿ 1_{U_{(k+1)/2ⁿ}}(x)`. -/
noncomputable def psumFn (f : C(X, ℝ)) (n m : ℕ) (x : X) : ℝ :=
  ∑ k ∈ Finset.range m, stepFn f n k x

theorem psumFn_nonneg (f : C(X, ℝ)) (n m : ℕ) (x : X) : 0 ≤ psumFn f n m x :=
  Finset.sum_nonneg fun k _ => stepFn_nonneg f n k x

theorem psumFn_le (f : C(X, ℝ)) (n m : ℕ) (x : X) : psumFn f n m x ≤ m * (1 / 2 ^ n) := by
  have := Finset.sum_le_sum (s := Finset.range m) fun k _ => stepFn_le f n k x
  simpa [psumFn] using this

theorem two_pow_mul_inv (n : ℕ) : ((2 ^ n : ℕ) : ℝ) * (1 / 2 ^ n) = 1 := by
  push_cast; field_simp

theorem psumFn_le_f (f : C(X, ℝ)) (n : ℕ) (x : X) (h0 : 0 ≤ f x) (h1 : f x ≤ 1) :
    psumFn f n (2 ^ n) x ≤ f x := by
  have hd : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  calc psumFn f n (2 ^ n) x ≤ ∑ k ∈ Finset.range (2 ^ n), clampR (f x - k * (1 / 2 ^ n)) (1 / 2 ^ n) :=
        Finset.sum_le_sum fun k _ => stepFn_upper f n k x
    _ = clampR (f x) 1 := by rw [clampR_tele _ _ hd, two_pow_mul_inv]
    _ = f x := by simp only [clampR, max_def, min_def]; split_ifs <;> linarith

theorem f_le_psumFn (f : C(X, ℝ)) (n : ℕ) (x : X) (h1 : f x ≤ 1) :
    f x - 1 / 2 ^ n ≤ psumFn f n (2 ^ n) x := by
  have hd : (0 : ℝ) < 1 / 2 ^ n := by positivity
  calc f x - 1 / 2 ^ n ≤ clampR (f x - 1 / 2 ^ n) 1 := by
        simp only [clampR, max_def, min_def]; split_ifs <;> linarith
    _ = ∑ k ∈ Finset.range (2 ^ n), clampR (f x - 1 / 2 ^ n - k * (1 / 2 ^ n)) (1 / 2 ^ n) := by
        rw [clampR_tele _ _ hd.le, two_pow_mul_inv]
    _ ≤ psumFn f n (2 ^ n) x := Finset.sum_le_sum fun k _ => stepFn_lower f n k x

theorem sum_range_two_mul (a : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), a j = ∑ k ∈ Finset.range N, (a (2 * k) + a (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

theorem stepFn_split (f : C(X, ℝ)) (n k : ℕ) (x : X) :
    stepFn f n k x ≤ stepFn f (n + 1) (2 * k) x + stepFn f (n + 1) (2 * k + 1) x := by
  have e1 : (((2 * k + 1 : ℕ) : ℝ) + 1) / 2 ^ (n + 1) = ((k : ℝ) + 1) / 2 ^ n := by
    push_cast; rw [pow_succ]; field_simp; ring
  have e2 : (((2 * k : ℕ) : ℝ) + 1) / 2 ^ (n + 1) ≤ ((k : ℝ) + 1) / 2 ^ n := by
    rw [← e1]; gcongr; linarith
  have e3 : (1 / 2 ^ (n + 1) : ℝ) + 1 / 2 ^ (n + 1) = 1 / 2 ^ n := by rw [pow_succ]; field_simp; ring
  unfold stepFn
  rw [e1]
  by_cases hx : x ∈ lvl f (((k : ℝ) + 1) / 2 ^ n)
  · have hx' := lvl_anti e2 hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx', add_comm, e3]
  · rw [Set.indicator_of_notMem hx]
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)
      (Set.indicator_nonneg (fun _ _ => by positivity) _)

theorem psumFn_mono (f : C(X, ℝ)) (n : ℕ) (x : X) :
    psumFn f n (2 ^ n) x ≤ psumFn f (n + 1) (2 ^ (n + 1)) x := by
  unfold psumFn
  rw [pow_succ, mul_comm, sum_range_two_mul]
  exact Finset.sum_le_sum fun k _ => stepFn_split f n k x

variable [ExtremallyDisconnected X]

/-- `psumFn` as a continuous function. -/
noncomputable def psumC (f : C(X, ℝ)) (n m : ℕ) : C(X, ℝ) :=
  ⟨psumFn f n m, continuous_finsetSum _ fun _ _ =>
    (lvl_isClopen f _).continuous_indicator continuous_const⟩

end SimpleApprox

section CXIInduction

variable {X : Type u} [TopologicalSpace X]

/-- An element of `[0,1]_{C(X)}` from a function with values in `[0,1]`. -/
noncomputable def mkC (g : C(X, ℝ)) (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) : CXI X :=
  ⟨g, ContinuousMap.le_def.mpr fun x => by simpa using h0 x,
    ContinuousMap.le_def.mpr fun x => by simpa using h1 x⟩

/-- The indicator of a clopen set, in `[0,1]_{C(X)}`. -/
noncomputable def indC (U : Set X) (hU : IsClopen U) : CXI X :=
  mkC ⟨U.indicator fun _ => (1 : ℝ), hU.continuous_indicator continuous_const⟩
    (fun x => by
      show (0 : ℝ) ≤ U.indicator (fun _ => (1 : ℝ)) x
      unfold Set.indicator; split_ifs <;> norm_num)
    (fun x => by
      show U.indicator (fun _ => (1 : ℝ)) x ≤ 1
      unfold Set.indicator; split_ifs <;> norm_num)

theorem inv_two_pow_le_one (n : ℕ) : (1 : ℝ) / 2 ^ n ≤ 1 := by
  rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)

/-- The constant `2⁻ⁿ`, in `[0,1]_{C(X)}`. -/
noncomputable def constC (n : ℕ) : CXI X :=
  mkC (ContinuousMap.const X (1 / 2 ^ n)) (fun _ => by simp)
    (fun _ => inv_two_pow_le_one n)

theorem cxi_le_iff {a b : CXI X} : a ≼ b ↔ ∀ x, a.1 x ≤ b.1 x :=
  (interval_le_iff (1 : C(X, ℝ)) cx_zero_le_one a b).trans ContinuousMap.le_def

theorem cxi_ext {a b : CXI X} (h : ∀ x, a.1 x = b.1 x) : a = b :=
  Subtype.ext (ContinuousMap.ext h)

/-- Induction over the simple elements of `[0,1]_{C(X)}`, `X` extremally
disconnected: a property of elements that holds for the clopen indicators and
the constant `½`, and is closed under products, sums and suprema of increasing
sequences, holds everywhere (every `f` is the supremum of the increasing
simple `g_n` of `psumC`). -/
theorem cxi_induction [ExtremallyDisconnected X] (P : CXI X → Prop)
    (hind : ∀ (U : Set X) (hU : IsClopen U), P (indC U hU)) (hhalf : P (constC 1))
    (hmul : ∀ y z, P y → P z → P (y * z))
    (hadd : ∀ y z (h : Perp y z), P y → P z → P (ovee y z h))
    (hsup : ∀ (G : ℕ → CXI X) (s : CXI X), (∀ n, G n ≼ G (n + 1)) →
      EIsSup (Set.range G) s → (∀ n, P (G n)) → P s)
    (f : CXI X) : P f := by
  have hf0 : ∀ x, 0 ≤ f.1 x := fun x => ContinuousMap.le_def.mp f.2.1 x
  have hf1 : ∀ x, f.1 x ≤ 1 := fun x => ContinuousMap.le_def.mp f.2.2 x
  -- the constants `2⁻ⁿ`
  have hc : ∀ n, P (constC n) := by
    intro n
    induction n with
    | zero =>
      have : constC 0 = indC (X := X) Set.univ isClopen_univ := cxi_ext fun x => by
        simp [constC, indC, mkC]
      rw [this]; exact hind _ _
    | succ n ih =>
      have : constC (n + 1) = constC n * constC (X := X) 1 := cxi_ext fun x => by
        show (1 : ℝ) / 2 ^ (n + 1) = 1 / 2 ^ n * (1 / 2 ^ 1)
        rw [pow_succ]; field_simp
      rw [this]; exact hmul _ _ ih hhalf
  -- the steps
  have hT : ∀ n k, P (mkC ⟨stepFn f.1 n k, (lvl_isClopen f.1 _).continuous_indicator
      continuous_const⟩ (stepFn_nonneg f.1 n k) (fun x => le_trans (stepFn_le f.1 n k x) (inv_two_pow_le_one n))) := by
    intro n k
    have : mkC ⟨stepFn f.1 n k, (lvl_isClopen f.1 _).continuous_indicator continuous_const⟩
        (stepFn_nonneg f.1 n k) (fun x => le_trans (stepFn_le f.1 n k x) (inv_two_pow_le_one n)) =
        constC n * indC _ (lvl_isClopen f.1 (((k : ℝ) + 1) / 2 ^ n)) := cxi_ext fun x => by
      show stepFn f.1 n k x = 1 / 2 ^ n * (lvl f.1 _).indicator (fun _ => (1 : ℝ)) x
      unfold stepFn Set.indicator; split_ifs <;> simp
    rw [this]; exact hmul _ _ (hc n) (hind _ _)
  -- the partial sums
  have hle1 : ∀ n m, m ≤ 2 ^ n → ∀ x, psumFn f.1 n m x ≤ 1 := by
    intro n m hm x
    refine le_trans (psumFn_le f.1 n m x) ?_
    calc (m : ℝ) * (1 / 2 ^ n) ≤ ((2 ^ n : ℕ) : ℝ) * (1 / 2 ^ n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
      _ = 1 := two_pow_mul_inv n
  have hS : ∀ n m (hm : m ≤ 2 ^ n),
      P (mkC (psumC f.1 n m) (psumFn_nonneg f.1 n m) (hle1 n m hm)) := by
    intro n m
    induction m with
    | zero =>
      intro _
      have : mkC (psumC f.1 n 0) (psumFn_nonneg f.1 n 0) (hle1 n 0 (Nat.zero_le _)) =
          indC (X := X) ∅ isClopen_empty := cxi_ext fun x => by
        show psumFn f.1 n 0 x = (∅ : Set X).indicator (fun _ => (1 : ℝ)) x
        simp [psumFn]
      rw [this]; exact hind _ _
    | succ m ih =>
      intro hm
      have hm' : m ≤ 2 ^ n := Nat.le_of_succ_le hm
      have hperp : Perp (mkC (psumC f.1 n m) (psumFn_nonneg f.1 n m) (hle1 n m hm'))
          (mkC ⟨stepFn f.1 n m, (lvl_isClopen f.1 _).continuous_indicator continuous_const⟩
            (stepFn_nonneg f.1 n m) (fun x => le_trans (stepFn_le f.1 n m x) (inv_two_pow_le_one n))) := by
        show psumC f.1 n m + _ ≤ 1
        refine ContinuousMap.le_def.mpr fun x => ?_
        have := hle1 n (m + 1) hm x
        show psumFn f.1 n m x + stepFn f.1 n m x ≤ 1
        simpa [psumFn, Finset.sum_range_succ] using this
      have : mkC (psumC f.1 n (m + 1)) (psumFn_nonneg f.1 n (m + 1)) (hle1 n (m + 1) hm) =
          ovee _ _ hperp := cxi_ext fun x => by
        show psumFn f.1 n (m + 1) x = psumFn f.1 n m x + stepFn f.1 n m x
        simp [psumFn, Finset.sum_range_succ]
      rw [this]; exact hadd _ _ _ (ih hm') (hT n m)
  -- the supremum
  let G : ℕ → CXI X := fun n => mkC (psumC f.1 n (2 ^ n)) (psumFn_nonneg f.1 n _)
    (hle1 n _ le_rfl)
  refine hsup G f (fun n => cxi_le_iff.mpr fun x => psumFn_mono f.1 n x) ⟨?_, ?_⟩
    (fun n => hS n _ le_rfl)
  · rintro _ ⟨n, rfl⟩
    exact cxi_le_iff.mpr fun x => psumFn_le_f f.1 n x (hf0 x) (hf1 x)
  · intro u hu
    refine cxi_le_iff.mpr fun x => le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := Papers.OAP.exists_inv_two_pow_lt hε
    have h1 := f_le_psumFn f.1 n x (hf1 x)
    have h2 := cxi_le_iff.mp (hu _ ⟨n, rfl⟩) x
    have h3 : psumFn f.1 n (2 ^ n) x = (G n).1 x := rfl
    linarith

end CXIInduction

/-- An isomorphism of effect monoids preserves suprema. -/
theorem EMIso.isSup_map {M N : Type u} [EffectMonoid M] [EffectMonoid N] (f : EMIso M N)
    {S : Set M} {x : M} (h : EIsSup S x) : EIsSup (f.toFun '' S) (f.toFun x) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩; exact f.toEAIso.map_le (h.1 s hs)
  · have hx : x ≼ f.invFun y := h.2 _ fun s hs => by
      have := f.symm.toEAIso.map_le (hy _ ⟨s, hs, rfl⟩)
      rwa [show f.symm.toFun (f.toFun s) = s from f.symm_apply s] at this
    have := f.toEAIso.map_le hx
    rwa [show f.toFun (f.invFun y) = y from f.apply_symm y] at this

/-- The core of SEA 70: a normal SEA whose idempotents are central and which
has a central half `h` of `1` is commutative.  For `a ∈ E`, `{a}'' ≅
[0,1]_{C(X)} ⊕ B` (SEA 36, unconditional); the half `h ∈ {a}''` forces
`B = {0}` and `h ↦ ½`; the elements of `[0,1]_{C(X)}` corresponding to central
elements contain the clopen indicators (idempotents) and `½`, and are closed
under products, sums and increasing suprema (S5, S6), so they are everything
(`cxi_induction`, the print's "simple elements"). -/
theorem commutative_of_central_half {E : Type u} [EffectAlgebra E] [NormalSEA E]
    (hid : ∀ p : E, IsIdempotent p → IsCentral p) {h : E} (hh : IsHalf h) (hc : IsCentral h) :
    IsCommutativeSEA E := by
  suffices H : ∀ a : E, IsCentral a from fun a b => H a b
  intro a
  obtain ⟨X, tX, cX, hX, hED, B, cB, ⟨Φ⟩⟩ := sea36_spectral_unconditional a
  let _iM := bicommEM {a} (singleton_commuting a)
  let _iB := booleanEffectMonoid B
  let T := bicommutantSub ({a} : Set E)
  let hM : T.carrier := ⟨h, fun s _ => hc s⟩
  obtain ⟨hhh, eh⟩ := hh
  have hMM : Perp hM hM := hhh
  have eM : ovee hM hM hMM = 1 := Subtype.ext eh
  have hPP : Perp (Φ.toFun hM) (Φ.toFun hM) := (Φ.perp_iff _ _).mpr hMM
  have eP := Φ.map_ovee hM hM hMM hPP
  rw [eM, Φ.map_one] at eP
  set u := Φ.toFun hM with hu
  have hb1 : u.2 ⊓ u.2 = ⊥ := hPP.2
  have hb2 : u.2 ⊔ u.2 = ⊤ := (congrArg Prod.snd eP).symm
  have hu2 : u.2 = ⊥ := by rw [← hb1, inf_idem]
  have hbt : (⊥ : B) = ⊤ := by rw [← hb2, sup_idem, hu2]
  have hB : ∀ β : B, β = ⊥ := fun β => le_bot_iff.mp (hbt ▸ le_top)
  have hu1 : u.1.1 + u.1.1 = 1 := (congrArg (fun z : CXI X × B => z.1.1) eP).symm
  -- the property: the corresponding element of `{a}''` is central
  let Q : CXI X × B → Prop := fun z => IsCentral (Φ.invFun z).1
  have hQ : ∀ z : CXI X × B, Q z ↔ Q (z.1, ⊥) := fun z => by
    rw [show z = (z.1, ⊥) from Prod.ext rfl (hB _)]
  let P : CXI X → Prop := fun y => Q (y, ⊥)
  have hsymm : ∀ z : CXI X × B, Φ.symm.toFun z = Φ.invFun z := fun _ => rfl
  have hPall : ∀ y, P y := by
    refine cxi_induction P ?_ ?_ ?_ ?_ ?_
    · -- clopen indicators are idempotents
      intro U hU
      let z : CXI X × B := (indC U hU, ⊥)
      have hz : z * z = z := Prod.ext (cxi_ext fun x => by
        show U.indicator (fun _ => (1 : ℝ)) x * U.indicator (fun _ => (1 : ℝ)) x =
          U.indicator (fun _ => (1 : ℝ)) x
        unfold Set.indicator; split_ifs <;> simp) (inf_idem _)
      have hm : Φ.invFun z * Φ.invFun z = Φ.invFun z := by
        rw [← hsymm, ← Φ.symm.map_mul, hz]
      exact hid _ (show (Φ.invFun z).1 ⊙ (Φ.invFun z).1 = (Φ.invFun z).1 from
        congrArg Subtype.val hm)
    · -- the half
      have e : (constC 1, (⊥ : B)) = u := Prod.ext (cxi_ext fun x => by
        have := congrArg (fun g : C(X, ℝ) => g x) hu1
        simp only [ContinuousMap.add_apply, ContinuousMap.one_apply] at this
        show (1 : ℝ) / 2 ^ 1 = u.1.1 x
        linarith) hu2.symm
      show IsCentral (Φ.invFun (constC 1, ⊥)).1
      rw [e, hu, Φ.symm_apply]
      exact hc
    · intro y z hy hz
      have e : ((y * z, ⊥) : CXI X × B) = (y, ⊥) * (z, ⊥) := Prod.ext rfl (inf_idem _).symm
      show IsCentral (Φ.invFun (y * z, ⊥)).1
      rw [e, ← hsymm, Φ.symm.map_mul]
      intro c
      exact (Commutes.seq (hy c).symm (hz c).symm).symm
    · intro y z hyz hy hz
      have hp : Perp ((y, ⊥) : CXI X × B) (z, ⊥) := ⟨hyz, inf_idem _⟩
      have e : ((ovee y z hyz, ⊥) : CXI X × B) = ovee (y, ⊥) (z, ⊥) hp :=
        Prod.ext rfl (hB _).symm
      have hp' := (Φ.symm.perp_iff _ _).mpr hp
      show IsCentral (Φ.invFun (ovee y z hyz, ⊥)).1
      rw [e, ← hsymm, Φ.symm.map_ovee _ _ hp hp']
      intro c
      exact (Commutes.ovee (E := E) hp' (hy c).symm (hz c).symm).symm
    · intro G s hG hs hPG
      let g : ℕ → T.carrier := fun n => Φ.invFun (G n, ⊥)
      have hgmono : ∀ n, g n ≼ g (n + 1) := fun n =>
        Φ.symm.toEAIso.map_le (prod_le_iff.mpr ⟨hG n, le_refl' _⟩)
      have hsup' : EIsSup (Set.range fun n => ((G n, ⊥) : CXI X × B)) (s, ⊥) := by
        refine prod_isSup ?_ ?_
        · rw [← Set.range_comp]; exact hs
        · refine ⟨fun β _ => by rw [hB β]; exact le_refl' _, fun β _ => by
            rw [hB β]; exact le_refl' _⟩
      have hsupM := Φ.symm.isSup_map hsup'
      rw [← Set.range_comp] at hsupM
      have hdir : EDirected (Set.range g) := eDirected_range_of_monotone hgmono
      have hsupE := subNormal_isSup_val T hdir hsupM
      have hdirE := (subEA_directed_iff (T := T.toSubEffectAlgebra)).mp hdir
      intro c
      refine (NormalSEA.comm_sup c hdirE hsupE ?_).symm
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact (hPG n c).symm
  have ha : Q (Φ.toFun ⟨a, subset_bicommutant _ rfl⟩) := (hQ _).mpr (hPall _)
  change IsCentral (Φ.invFun (Φ.toFun _)).1 at ha
  rwa [Φ.symm_apply] at ha

/-- **SEA 70** (`prop-assoc-comm-halves`, second.tex:2075, Proposition): an
associative normal SEA with commuting halves is commutative.  Proof as printed
(route through the pieces of SEA 68): idempotents are central (SEA 69); in the
splitting `E ≅ p₀ ⊙ E ⊕ p₀⊥ ⊙ E` of SEA 58 the Boolean part consists of
idempotents, hence central elements, and the a-convex part `p₀ ⊙ E` has
commuting halves, so it is convex with a central half (SEA 67, 57); there
every element is a supremum of an increasing sequence of simple elements
`⋁ λᵢ pᵢ` (the spectral theorem SEA 36, `cxi_induction`), which are central, so
`p₀ ⊙ E` is commutative (`commutative_of_central_half`); and
`a = p₀ ⊙ a ⋁ p₀⊥ ⊙ a` is central.  Uses SEA 35 (**OAP 69**, `sea35`). -/
theorem sea70_commutative {E : Type u} [EffectAlgebra E] [NormalSEA E]
    (hA : IsAssociativeSEA E) (hH : HasCommutingHalves E) : IsCommutativeSEA E := by
  have hid : ∀ p : E, IsIdempotent p → IsCentral p := fun p hp => sea69_idempotent_central hA hp
  obtain ⟨p0, ⟨hp, hAc⟩, -, hc, hb⟩ := sea58_maximal (E := E) sea35
  let _ : NormalSEA (Downset p0) := cornerNormalSEA hp
  have hconv : IsConvex (Downset p0) :=
    (sea67_convex_iff hAc).mpr (hasCommutingHalves_corner hH hp)
  obtain ⟨k, hkc, hk⟩ := sea57_4_3 (sea57_1_4 hconv)
  have hidF : ∀ q : Downset p0, IsIdempotent q → IsCentral q := fun q hq =>
    corner_isCentral hp q (hid q.1 (congrArg Subtype.val hq))
  have hF : IsCommutativeSEA (Downset p0) := commutative_of_central_half hidF hk hkc
  have key : ∀ a : E, IsCentral a := by
    intro a
    obtain ⟨h, e⟩ := seq_split a p0
    have c1 : IsCentral (a ⊙ p0) := by
      rw [← hc a]
      exact isCentral_of_corner hp hc ⟨p0 ⊙ a, seq_le_left _ _⟩ fun b => hF _ b
    have c2 : IsCentral (a ⊙ orth p0) := by
      rw [← hc.orth_central a]
      exact hid _ (hb.2 _ (seq_le_left _ _))
    intro b
    have := Commutes.ovee h (c1 b).symm (c2 b).symm
    rw [e] at this
    exact this.symm
  exact fun a b => key a b

/-! ### SEA 73: associative a-convex factors -/

/-- The inverse of a SEA isomorphism. -/
def SEAIso.symm {E : Type u} {F : Type v} [EffectAlgebra E] [EffectAlgebra F] [SEAlgebra E]
    [SEAlgebra F] (f : SEAIso E F) : SEAIso F E where
  toEquiv := f.toEquiv.symm
  map_one := f.toEquiv.injective (by
    show f.toFun (f.invFun 1) = f.toFun 1; rw [f.right_inv, f.map_one])
  perp_iff := fun a b => by
    have := f.perp_iff (f.invFun a) (f.invFun b)
    rw [f.right_inv a, f.right_inv b] at this
    exact this.symm
  map_ovee := fun a b h h' => f.toEquiv.injective (by
    show f.toFun (f.invFun (ovee a b h)) = f.toFun (ovee (f.invFun a) (f.invFun b) h')
    rw [f.right_inv, f.map_ovee (f.invFun a) (f.invFun b) h' ((f.perp_iff _ _).mpr h')]
    exact PCM.ovee_congr (f.right_inv a).symm (f.right_inv b).symm _ _)
  map_seq := fun a b => f.toEquiv.injective (by
    show f.toFun (f.invFun (a ⊙ b)) = f.toFun (f.invFun a ⊙ f.invFun b)
    rw [f.right_inv, f.map_seq, f.right_inv, f.right_inv])

theorem isAdditive_id : IsAdditive (fun x : I => x) := fun l m n h =>
  ⟨show (l : ℝ) + m ≤ 1 by rw [h]; exact n.2.2, Subtype.ext h⟩

/-- A unital additive map `[0,1] → [0,1]` is the identity. -/
theorem unit_additive_eq_id {g : I → I} (hg : IsAdditive g) (h1 : g 1 = 1) :
    g = fun x => x := by
  refine additive_eq_of_div hg isAdditive_id (l := 1) (by simp) h1 fun n hn b c hb hc => ?_
  have e1 := unit_isSumOf_sum hb
  have e2 := unit_isSumOf_sum hc
  simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul] at e1 e2
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact Subtype.ext (mul_left_cancel₀ hn' (e1.trans e2.symm))

/-- Splitting `k (a ⋁ b) = s` into `k a ⋁ k b = s`. -/
theorem isSumOf_replicate_ovee {E : Type u} [EffectAlgebra E] {a b : E} (hab : Perp a b) :
    ∀ (k : ℕ) {s : E}, PCM.IsSumOf (List.replicate k (ovee a b hab)) s →
      ∃ a' b', PCM.IsSumOf (List.replicate k a) a' ∧ PCM.IsSumOf (List.replicate k b) b' ∧
        ∃ h : Perp a' b', ovee a' b' h = s
  | 0, s, hs => ⟨0, 0, PCM.IsSumOf.nil, PCM.IsSumOf.nil, PCM.zero_perp 0, by
      rw [PCM.isSumOf_nil_iff.mp hs, zero_ovee_eq]⟩
  | k + 1, s, hs => by
    obtain ⟨t, ht, h1, rfl⟩ := isSumOf_replicate_succ.mp hs
    obtain ⟨a', b', ha', hb', h2, rfl⟩ := isSumOf_replicate_ovee hab k ht
    have hsum := isSumOf_append (isSumOf_pair hab) (isSumOf_pair h2) h1
    have hperm : ([a, b] ++ [a', b']).Perm ([a, a'] ++ [b, b']) := by
      simp only [List.cons_append, List.nil_append]
      exact List.Perm.cons _ (List.Perm.swap _ _ _)
    obtain ⟨t1, t2, ht1, ht2, h3, e3⟩ := isSumOf_append_split (PCM.isSumOf_perm hperm hsum)
    obtain ⟨haa, rfl⟩ := isSumOf_pair_iff.mp ht1
    obtain ⟨hbb, rfl⟩ := isSumOf_pair_iff.mp ht2
    exact ⟨_, _, isSumOf_replicate_succ.mpr ⟨a', ha', haa, rfl⟩,
      isSumOf_replicate_succ.mpr ⟨b', hb', hbb, rfl⟩, h3, e3⟩

/-- `x ∈ T''` gives `{x}'' ⊆ T''`. -/
theorem bicommutant_singleton_subset {E : Type u} [EffectAlgebra E] [SEAlgebra E] {T : Set E}
    {x : E} (hx : x ∈ bicommutant T) : bicommutant ({x} : Set E) ⊆ bicommutant T :=
  commutant_anti fun y hy s hs => by rw [Set.mem_singleton_iff.mp hs]; exact (hx y hy).symm

/-- The unital additive maps `[0,1] → E`: the index set of SEA 73 (each
parametrises one copy of `[0,1]` in `E`; they correspond one-to-one to the
print's maximal collection of mutually non-commuting elements). -/
def Line (E : Type u) [EffectAlgebra E] : Type u := {φ : I → E // IsAdditive φ ∧ φ 1 = 1}

section Lines

variable {E : Type u} [EffectAlgebra E]

theorem line_zero (φ : Line E) : φ.1 0 = 0 := φ.2.1.map_zero

/-- The map `HS([0,1]_φ) → E` of SEA 73: `(λ, φ) ↦ φ(λ)`. -/
noncomputable def theta73 : HSum (fun _ : Line E => I) → E
  | .zero => 0
  | .one => 1
  | .mid φ l _ _ => φ.1 l

theorem theta73_mk (φ : Line E) (l : I) : theta73 (HSum.mk φ l) = φ.1 l := by
  rcases HSum.mk_cases (E := fun _ : Line E => I) φ l with ⟨h, hm⟩ | ⟨-, h, hm⟩ | ⟨h0, h1, hm⟩ <;> rw [hm]
  · rw [h, line_zero]; rfl
  · rw [h, φ.2.2]; rfl
  · rfl

theorem hsum_exists_mk (φ0 : Line E) (x : HSum (fun _ : Line E => I)) :
    ∃ φ l, x = HSum.mk φ l := by
  cases x with
  | zero => exact ⟨φ0, 0, (HSum.mk_zero φ0).symm⟩
  | one => exact ⟨φ0, 1, (HSum.mk_one_of (i := φ0) unit_one_ne_zero).symm⟩
  | mid φ l h0 h1 => exact ⟨φ, l, (HSum.mk_of_ne h0 h1).symm⟩

theorem line_eq_zero (h10 : (1 : E) ≠ 0) (φ : Line E) {l : I} (h : φ.1 l = 0) : l = 0 := by
  by_contra hl
  have hl0 : (0 : ℝ) < l := lt_of_le_of_ne l.2.1 (fun e => hl (Subtype.ext e.symm))
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (l : ℝ))
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 < k := by exact_mod_cast hk0
    exact_mod_cast this
  have hv1 : (1 : ℝ) / k ≤ 1 := by rw [div_le_one hk0]; exact hk1
  have hvl : mkI (1 / k) (by positivity) hv1 ≤ l := by
    show (1 : ℝ) / k ≤ l
    rw [div_le_iff₀ hk0]; rw [div_lt_iff₀ hl0] at hk; linarith
  have hv : φ.1 (mkI (1 / k) (by positivity) hv1) = 0 := by
    have := φ.2.1.mono hvl; rw [h] at this; exact eq_zero_of_le_zero this
  have hrep := φ.2.1.replicate k (mkI (1 / k) (by positivity) hv1) 1 (by simp; field_simp)
  rw [hv, φ.2.2] at hrep
  exact h10 (isSumOf_unique hrep (isSumOf_replicate_zero k))

theorem line_eq_one (h10 : (1 : E) ≠ 0) (φ : Line E) {l : I} (h : φ.1 l = 1) : l = 1 := by
  obtain ⟨hp, -⟩ := φ.2.1 l (mkI (1 - l) (by linarith [l.2.2]) (by linarith [l.2.1])) 1 (by simp)
  rw [h] at hp
  have h0 := line_eq_zero h10 φ (EffectAlgebra.eq_zero_of_perp_one (PCM.perp_comm hp))
  have := congrArg Subtype.val h0
  simp only [mkI_val, Set.Icc.coe_zero] at this
  exact Subtype.ext (show (l : ℝ) = ((1 : I) : ℝ) by rw [Set.Icc.coe_one]; linarith)

end Lines

section Sec73

variable {E : Type u} [EffectAlgebra E] [NormalSEA E]

/-- A line `ψ` meeting an injective, summability-reflecting line `χ` at
`ψ(½)` is `χ` (the half pins the parameter, then SEA 52.4). -/
theorem line_eq_of_half {χ ψ : Line E} (hinj : Function.Injective χ.1)
    (hperp : ∀ l m, Perp (χ.1 l) (χ.1 m) → (l : ℝ) + m ≤ 1) {l' : I} (h : ψ.1 halfI = χ.1 l') :
    ψ = χ := by
  obtain ⟨hψ, eψ⟩ := ψ.2.1 halfI halfI 1 (by simp only [halfI_val, Set.Icc.coe_one]; norm_num)
  rw [ψ.2.2] at eψ
  have hχ : Perp (χ.1 l') (χ.1 l') := h ▸ hψ
  have hll := hperp l' l' hχ
  obtain ⟨hχ', eχ⟩ := χ.2.1 l' l' (mkI _ (by linarith [l'.2.1]) hll) rfl
  have e1 : χ.1 (mkI _ (by linarith [l'.2.1]) hll) = χ.1 1 :=
    calc χ.1 (mkI _ (by linarith [l'.2.1]) hll) = ovee (χ.1 l') (χ.1 l') hχ' := eχ.symm
      _ = ovee (ψ.1 halfI) (ψ.1 halfI) hψ := PCM.ovee_congr h.symm h.symm _ _
      _ = 1 := eψ
      _ = χ.1 1 := χ.2.2.symm
  have e2 := congrArg Subtype.val (hinj e1)
  simp only [mkI_val, Set.Icc.coe_one] at e2
  have hl' : l' = halfI := Subtype.ext (by simp only [halfI_val]; linarith)
  subst hl'
  exact Subtype.ext (sea52_4_unique_unconditional ψ.2.1 χ.2.1 halfI_pos halfI_lt_one h)

variable (hid : ∀ p : E, IsIdempotent p → p = 0 ∨ p = 1) (h10 : (1 : E) ≠ 0)
include hid h10

/-- In the setting of SEA 73 (only trivial idempotents, `1 ≠ 0`): the
bicommutant `S''` of a commuting set containing an `s ∉ {0,1}` is `[0,1]`.
`S''` is a directed-complete effect monoid without zero divisors (SEA 72), so
**OAP 71** (`Papers.OAP.oap71`) makes it `{0}`, `{0,1}` or `[0,1]`, and the
first two are excluded by `1 ≠ 0` and `s`. -/
theorem bicomm_iso_unit {S : Set E} (hS : ∀ a ∈ S, ∀ b ∈ S, Commutes a b) {s : E}
    (hs : s ∈ S) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Nonempty (@EMIso (bicommutantSub S).carrier I (bicommEM S hS) _) := by
  let _iM := bicommEM S hS
  have : Papers.OAP.DirectedComplete (bicommutantSub S).carrier :=
    sea_directedComplete_toOAP (bicommEM_dc S hS)
  have hM : ∀ a b : (bicommutantSub S).carrier, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    rcases sea72_no_zero_divisors hid (show a.1 ⊙ b.1 = 0 from congrArg Subtype.val hab) with
      h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rcases Papers.OAP.oap71 (M := (bicommutantSub S).carrier) hM with h | ⟨-, h⟩ | ⟨f, hf⟩
  · exact absurd (show (1 : E) = 0 from congrArg Subtype.val (h 1)) h10
  · rcases h ⟨s, subset_bicommutant S hs⟩ with e | e
    · exact absurd (congrArg Subtype.val e) hs0
    · exact absurd (congrArg Subtype.val e) hs1
  · exact nonempty_emIso_of_OAP f hf

/-- A line through a commuting set `S` with an element outside `{0,1}`:
`λ ↦ Ψ⁻¹(λ)` for `Ψ : S'' ≅ [0,1]`; its range is `S''`, and it is injective
and reflects summability. -/
theorem exists_line_of_commuting {S : Set E} (hS : ∀ a ∈ S, ∀ b ∈ S, Commutes a b) {s : E}
    (hs : s ∈ S) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ∃ χ : Line E, (∀ l, χ.1 l ∈ bicommutant S) ∧ (∀ x ∈ bicommutant S, ∃ l, χ.1 l = x) ∧
      Function.Injective χ.1 ∧ ∀ l m, Perp (χ.1 l) (χ.1 m) → (l : ℝ) + m ≤ 1 := by
  let _iM := bicommEM S hS
  obtain ⟨Ψ⟩ := bicomm_iso_unit hid h10 hS hs hs0 hs1
  refine ⟨⟨fun l => (Ψ.invFun l).1, ?_, ?_⟩, fun l => (Ψ.invFun l).2,
    fun x hx => ⟨Ψ.toFun ⟨x, hx⟩, ?_⟩, ?_, ?_⟩
  · intro l m n hlmn
    have hp : Perp l m := show (l : ℝ) + m ≤ 1 by rw [hlmn]; exact n.2.2
    have e : ovee l m hp = n := Subtype.ext hlmn
    have hp' := (Ψ.symm.perp_iff l m).mpr hp
    refine ⟨hp', ?_⟩
    have := Ψ.symm.map_ovee l m hp hp'
    rw [e] at this
    exact (congrArg Subtype.val this).symm
  · show (Ψ.invFun 1).1 = 1
    exact congrArg Subtype.val Ψ.symm.map_one
  · show (Ψ.invFun (Ψ.toFun ⟨x, hx⟩)).1 = x
    rw [Ψ.symm_apply]
  · intro l m e
    have e' : Ψ.invFun l = Ψ.invFun m := Subtype.ext e
    have := congrArg Ψ.toFun e'
    rwa [Ψ.apply_symm, Ψ.apply_symm] at this
  · intro l m h
    exact (Ψ.symm.perp_iff l m).mp h

/-- Every line has range `{φ(½)}''` and is injective and reflects
summability. -/
theorem line_good (φ : Line E) :
    (∀ l, φ.1 l ∈ bicommutant ({φ.1 halfI} : Set E)) ∧
      (∀ x ∈ bicommutant ({φ.1 halfI} : Set E), ∃ l, φ.1 l = x) ∧
      Function.Injective φ.1 ∧ ∀ l m, Perp (φ.1 l) (φ.1 m) → (l : ℝ) + m ≤ 1 := by
  have h0 : φ.1 halfI ≠ 0 := fun e => halfI_ne_zero (line_eq_zero h10 φ e)
  have h1 : φ.1 halfI ≠ 1 := fun e => halfI_ne_one (line_eq_one h10 φ e)
  obtain ⟨χ, hmem, hrange, hinj, hperp⟩ :=
    exists_line_of_commuting hid h10 (singleton_commuting _) rfl h0 h1
  obtain ⟨l', hl'⟩ := hrange _ (subset_bicommutant _ rfl)
  have := line_eq_of_half hinj hperp hl'.symm
  subst this
  exact ⟨hmem, hrange, hinj, hperp⟩

/-- Two lines through a common point outside `{0,1}` coincide. -/
theorem line_eq_of_meet {φ ψ : Line E} {l m : I} (h : φ.1 l = ψ.1 m) (h0 : φ.1 l ≠ 0)
    (h1 : φ.1 l ≠ 1) : φ = ψ := by
  obtain ⟨χ, hmem, -, -, -⟩ :=
    exists_line_of_commuting hid h10 (singleton_commuting (φ.1 l)) rfl h0 h1
  have key : ∀ ρ : Line E, ∀ k, ρ.1 k = φ.1 l → χ = ρ := by
    intro ρ k hk
    obtain ⟨hmemρ, hrangeρ, hinjρ, hperpρ⟩ := line_good hid h10 ρ
    have hsub := bicommutant_singleton_subset (hk ▸ hmemρ k)
    obtain ⟨l'', hl''⟩ := hrangeρ _ (hsub (hmem halfI))
    exact line_eq_of_half hinjρ hperpρ hl''.symm
  exact (key φ l rfl).symm.trans (key ψ m h.symm)

/-- Every element of `E` lies on a line (given one line, for `0` and `1`). -/
theorem exists_line_through (φ0 : Line E) (x : E) : ∃ (φ : Line E) (l : I), φ.1 l = x := by
  by_cases hx0 : x = 0
  · exact ⟨φ0, 0, by rw [hx0, line_zero]⟩
  by_cases hx1 : x = 1
  · exact ⟨φ0, 1, by rw [hx1, φ0.2.2]⟩
  obtain ⟨χ, -, hrange, -, -⟩ := exists_line_of_commuting hid h10 (singleton_commuting x) rfl hx0 hx1
  obtain ⟨l, hl⟩ := hrange x (subset_bicommutant _ rfl)
  exact ⟨χ, l, hl⟩

/-- Multiplicativity (proof of SEA 73): `φ(λ) ⊙ ψ(μ) = φ(λμ)` for `λ ≠ 1`.
As printed, for `μ = ½`: `y = φ(λ) ⊙ ψ(½)` has `y ⋁ y = φ(λ)`, so `y` commutes
with `φ(λ)` and lies on the line of `{φ(λ), y}''`, which is `φ`; so
`y = φ(λ/2)`.  Both sides are additive in `μ` and agree at `½` (SEA 52.4).
(Associativity is not used here: only through SEA 69, for the idempotents.) -/
theorem line_mul {φ ψ : Line E} {l : I} (hl : l ≠ 1) (m : I) :
    φ.1 l ⊙ ψ.1 m = φ.1 (l * m) := by
  by_cases hl0 : l = 0
  · rw [hl0, line_zero, zero_seq, zero_mul, line_zero]
  have hx0 : φ.1 l ≠ 0 := fun e => hl0 (line_eq_zero h10 φ e)
  have hx1 : φ.1 l ≠ 1 := fun e => hl (line_eq_one h10 φ e)
  set x := φ.1 l with hxdef
  obtain ⟨hψ, eψ⟩ := ψ.2.1 halfI halfI 1 (by simp only [halfI_val, Set.Icc.coe_one]; norm_num)
  rw [ψ.2.2] at eψ
  obtain ⟨hyy, eyy⟩ := seq_ovee x hψ
  rw [eψ, seq_one] at eyy
  set y := x ⊙ ψ.1 halfI with hydef
  have hyx : Commutes y x := by
    have := Commutes.ovee hyy (commutes_refl y) (commutes_refl y)
    rwa [← eyy] at this
  let S : Set E := {x, y}
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commutes a b := by
    intro a ha b hb
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact commutes_refl _
    · exact hyx.symm
    · exact hyx
    · exact commutes_refl _
  obtain ⟨χ, -, hrange, -, -⟩ :=
    exists_line_of_commuting hid h10 hS (show x ∈ S by simp [S]) hx0 hx1
  obtain ⟨l1, hl1⟩ := hrange x (subset_bicommutant S (by simp [S]))
  have hχ : φ = χ := line_eq_of_meet hid h10 hl1.symm hx0 hx1
  obtain ⟨ζ, hζ⟩ := hrange y (subset_bicommutant S (by simp [S]))
  rw [← hχ] at hζ
  obtain ⟨-, -, hinj, hperp⟩ := line_good hid h10 φ
  have hζζ : Perp (φ.1 ζ) (φ.1 ζ) := by rw [hζ]; exact hyy
  have h2 := hperp ζ ζ hζζ
  obtain ⟨hpz, e2⟩ := φ.2.1 ζ ζ (mkI _ (by linarith [ζ.2.1]) h2) rfl
  have e3 : φ.1 (mkI _ (by linarith [ζ.2.1]) h2) = φ.1 l :=
    calc φ.1 (mkI _ (by linarith [ζ.2.1]) h2) = ovee (φ.1 ζ) (φ.1 ζ) hpz := e2.symm
      _ = ovee y y hyy := PCM.ovee_congr hζ hζ _ _
      _ = x := eyy.symm
  have e4 := congrArg Subtype.val (hinj e3)
  simp only [mkI_val] at e4
  have hy : y = φ.1 (halfI * l) := by
    rw [← hζ]
    exact congrArg φ.1 (Subtype.ext (by simp only [Set.Icc.coe_mul, halfI_val]; linarith))
  have := sea52_4_unique_unconditional (ψ.2.1.seq x) (φ.2.1.comp_mul l) halfI_pos
    halfI_lt_one (show x ⊙ ψ.1 halfI = φ.1 (halfI * l) from hy)
  exact (congrFun this m).trans (congrArg φ.1 (mul_comm m l))

/-- Summability across lines (proof of SEA 73): if `φ(λ) ⊥ ψ(μ)` with
`λ, μ > 0` then `φ = ψ`.  As printed: with `ε = 1/2k ≤ λ, μ`, the sum
`u = φ(ε) ⋁ ψ(ε)` is `χ(ζ)` for some line `χ`; multiplying by `χ(½)` gives
`χ(ζ/2) = χ(ε/2) ⋁ χ(ε/2) = χ(ε)`, so `ζ = 2ε` and `k u = 1`, which splits
as `φ(½) ⋁ ψ(½) = 1`; so `ψ(½) = φ(½)⊥ = φ(½)` and `φ = ψ` (SEA 52.4). -/
theorem line_eq_of_perp (φ0 : Line E) {φ ψ : Line E} {l m : I} (hl : 0 < (l : ℝ))
    (hm : 0 < (m : ℝ)) (h : Perp (φ.1 l) (ψ.1 m)) : φ = ψ := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / min (l : ℝ) m)
  have hmin : 0 < min (l : ℝ) m := lt_min hl hm
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 < k := by exact_mod_cast hk0
    exact_mod_cast this
  have hε1 : (1 : ℝ) / (2 * k) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  set ε : I := mkI (1 / (2 * k)) (by positivity) hε1 with hεdef
  have hεmin : (ε : ℝ) ≤ min (l : ℝ) m := by
    show 1 / (2 * (k : ℝ)) ≤ min (l : ℝ) m
    rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hmin] at hk; nlinarith
  have hP : Perp (φ.1 ε) (ψ.1 ε) :=
    perp_of_le (φ.2.1.mono (le_trans hεmin (min_le_left _ _)))
      (ψ.2.1.mono (le_trans hεmin (min_le_right _ _))) h
  obtain ⟨χ, ζ, hζ⟩ := exists_line_through hid h10 φ0 (ovee (φ.1 ε) (ψ.1 ε) hP)
  obtain ⟨-, -, hinj, -⟩ := line_good hid h10 χ
  -- `χ(½) ⊙ u`, two ways
  have hne : halfI ≠ 1 := halfI_ne_one
  obtain ⟨h1, e1⟩ := seq_ovee (χ.1 halfI) hP
  have hεε : ((halfI * ε : I) : ℝ) + (halfI * ε : I) = ε := by
    simp only [Set.Icc.coe_mul, halfI_val]; ring
  obtain ⟨h2, e2⟩ := χ.2.1 _ _ _ hεε
  have e3 : χ.1 (halfI * ζ) = χ.1 ε :=
    calc χ.1 (halfI * ζ) = χ.1 halfI ⊙ χ.1 ζ := (line_mul hid h10 hne ζ).symm
      _ = χ.1 halfI ⊙ ovee (φ.1 ε) (ψ.1 ε) hP := by rw [hζ]
      _ = ovee (χ.1 halfI ⊙ φ.1 ε) (χ.1 halfI ⊙ ψ.1 ε) h1 := e1
      _ = ovee (χ.1 (halfI * ε)) (χ.1 (halfI * ε)) h2 :=
          PCM.ovee_congr (line_mul hid h10 hne ε) (line_mul hid h10 hne ε) _ _
      _ = χ.1 ε := e2
  have e4 := congrArg Subtype.val (hinj e3)
  simp only [Set.Icc.coe_mul, halfI_val] at e4
  -- `k u = 1`
  have hkζ : (k : ℝ) * ζ = ((1 : I) : ℝ) := by
    simp only [Set.Icc.coe_one]; rw [show (ζ : ℝ) = 2 * ε by linarith, hεdef, mkI_val]
    field_simp
  have hrep := χ.2.1.replicate k ζ 1 hkζ
  rw [hζ, χ.2.2] at hrep
  obtain ⟨a', b', ha', hb', hab, eab⟩ := isSumOf_replicate_ovee hP k hrep
  have hkε : (k : ℝ) * ε = (halfI : ℝ) := by
    rw [hεdef, mkI_val, halfI_val]; field_simp
  have ea := isSumOf_unique ha' (φ.2.1.replicate k ε halfI hkε)
  have eb := isSumOf_unique hb' (ψ.2.1.replicate k ε halfI hkε)
  subst ea; subst eb
  obtain ⟨hφ, eφ⟩ := φ.2.1 halfI halfI 1 (by simp only [halfI_val, Set.Icc.coe_one]; norm_num)
  rw [φ.2.2] at eφ
  have e5 : ψ.1 halfI = φ.1 halfI := cancel_left hab hφ (eab.trans eφ.symm)
  exact Subtype.ext (sea52_4_unique_unconditional φ.2.1 ψ.2.1 halfI_pos halfI_lt_one e5.symm)

theorem theta73_bijective (φ0 : Line E) : Function.Bijective (theta73 (E := E)) := by
  constructor
  · intro x y e
    obtain ⟨φ, l, rfl⟩ := hsum_exists_mk φ0 x
    obtain ⟨ψ, m, rfl⟩ := hsum_exists_mk φ0 y
    rw [theta73_mk, theta73_mk] at e
    by_cases hl0 : φ.1 l = 0
    · rw [line_eq_zero h10 φ hl0, line_eq_zero h10 ψ (e.symm.trans hl0), HSum.mk_zero,
        HSum.mk_zero]
    by_cases hl1 : φ.1 l = 1
    · rw [line_eq_one h10 φ hl1, line_eq_one h10 ψ (e.symm.trans hl1),
        HSum.mk_one_of unit_one_ne_zero, HSum.mk_one_of unit_one_ne_zero]
    have hφψ := line_eq_of_meet hid h10 e hl0 hl1
    subst hφψ
    rw [(line_good hid h10 φ).2.2.1 e]
  · intro x
    obtain ⟨φ, l, hl⟩ := exists_line_through hid h10 φ0 x
    exact ⟨HSum.mk φ l, by rw [theta73_mk, hl]⟩

theorem theta73_perp_iff (φ0 : Line E) (x y : HSum (fun _ : Line E => I)) :
    Perp (theta73 x) (theta73 y) ↔ Perp x y := by
  obtain ⟨φ, l, rfl⟩ := hsum_exists_mk φ0 x
  obtain ⟨ψ, m, rfl⟩ := hsum_exists_mk φ0 y
  rw [theta73_mk, theta73_mk]
  by_cases hφψ : φ = ψ
  · subst hφψ
    rw [HSum.mk_perp_iff]
    exact ⟨fun h => (line_good hid h10 φ).2.2.2 l m h, fun h => (φ.2.1 l m (ovee l m h) rfl).1⟩
  · rw [HSum.mk_perp_mk_iff_of_ne (E := fun _ : Line E => I) hφψ]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have hl : 0 < (l : ℝ) := lt_of_le_of_ne l.2.1 (fun e => hc.1 (Subtype.ext e.symm))
      have hm : 0 < (m : ℝ) := lt_of_le_of_ne m.2.1 (fun e => hc.2 (Subtype.ext e.symm))
      exact hφψ (line_eq_of_perp hid h10 φ0 hl hm h)
    · rintro (rfl | rfl)
      · rw [line_zero]; exact PCM.zero_perp _
      · rw [line_zero]; exact PCM.perp_zero _

omit hid h10 [NormalSEA E] in
theorem theta73_ovee (φ0 : Line E) (x y : HSum (fun _ : Line E => I)) (h : Perp x y)
    (h' : Perp (theta73 x) (theta73 y)) :
    theta73 (ovee x y h) = ovee (theta73 x) (theta73 y) h' := by
  obtain ⟨φ, l, rfl⟩ := hsum_exists_mk φ0 x
  obtain ⟨ψ, m, rfl⟩ := hsum_exists_mk φ0 y
  by_cases hφψ : φ = ψ
  · subst hφψ
    have hlm : Perp l m := HSum.mk_perp_iff.mp h
    obtain ⟨h2, e2⟩ := HSum.mk_ovee (E := fun _ : Line E => I) (i := φ) hlm
    refine (congrArg theta73 e2).trans ?_
    rw [theta73_mk]
    obtain ⟨h3, e3⟩ := φ.2.1 l m (ovee l m hlm) rfl
    exact e3.symm.trans (PCM.ovee_congr (theta73_mk φ l).symm (theta73_mk φ m).symm _ _)
  · rcases (HSum.mk_perp_mk_iff_of_ne (E := fun _ : Line E => I) hφψ l m).mp h with rfl | rfl
    · have e : ovee (HSum.mk (E := fun _ : Line E => I) φ 0) (HSum.mk ψ m) h = HSum.mk ψ m := by
        rw [PCM.ovee_congr (HSum.mk_zero φ) rfl h (PCM.zero_perp _)]; exact zero_ovee_eq _ _
      rw [e]
      exact (zero_ovee_eq _ (PCM.zero_perp _)).symm.trans
        (PCM.ovee_congr (by rw [theta73_mk, line_zero]) rfl _ _)
    · have e : ovee (HSum.mk (E := fun _ : Line E => I) φ l) (HSum.mk ψ 0) h = HSum.mk φ l := by
        rw [PCM.ovee_congr rfl (HSum.mk_zero ψ) h (PCM.perp_zero _)]; exact ovee_zero_eq _ _
      rw [e]
      exact (ovee_zero_eq _ (PCM.perp_zero _)).symm.trans
        (PCM.ovee_congr rfl (by rw [theta73_mk, line_zero]) _ _)

theorem theta73_seq (φ0 : Line E) (x y : HSum (fun _ : Line E => I)) :
    theta73 (x ⊙ y) = theta73 x ⊙ theta73 y := by
  obtain ⟨ψ, m, rfl⟩ := hsum_exists_mk φ0 y
  cases x with
  | zero => show (0 : E) = 0 ⊙ _; rw [zero_seq]
  | one => show theta73 (HSum.mk ψ m) = 1 ⊙ _; rw [one_seq]
  | mid φ l h0 h1 =>
    show theta73 (HSum.mk φ (l ⊙ HSum.proj (unitMaps (Line E)) φ (HSum.mk ψ m))) =
      φ.1 l ⊙ theta73 (HSum.mk ψ m)
    rw [HSum.proj_mk, theta73_mk, theta73_mk]
    exact (line_mul hid h10 h1 m).symm

end Sec73

/-- **SEA 73** (`prop:assoc-a-convex`, second.tex:2129, Proposition), false as
printed: "a normal a-convex factor with an associative sequential product is
isomorphic to the horizontal sum of `#I` copies of `[0,1]` for some `I`" fails
for the one-element SEA `{0 = 1}` (here the corner `[0, 0]` of `[0,1]`): it is
a normal associative a-convex factor (`Z = {0} = {0, 1}`), but every horizontal
sum of copies of `[0,1]` has `0 ≠ 1` (for `I = ∅` it is `{0, 1}`).  The
corrected statement assumes `0 ≠ 1`: `sea73_assoc_factor`. -/
theorem sea73_false_as_printed :
    ¬ ∀ (E : Type) [EffectAlgebra E] [NormalSEA E], IsAConvexFactor E → IsAssociativeSEA E →
      ∃ ι : Type, Nonempty (SEAIso E (HSum (fun _ : ι => I))) := by
  intro H
  let _ : NormalSEA (Downset (0 : I)) := cornerNormalSEA isIdempotent_zero
  have hsub : ∀ a b : Downset (0 : I), a = b := fun a b =>
    Subtype.ext ((eq_zero_of_le_zero a.2).trans (eq_zero_of_le_zero b.2).symm)
  have hfac : IsAConvexFactor (Downset (0 : I)) := by
    refine ⟨⟨(actOfPhi sea35 isAdditive_id rfl).restrict 0⟩, ?_⟩
    ext c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun _ => Or.inl (hsub _ _), fun _ b => hsub _ _⟩
  obtain ⟨ι, ⟨f⟩⟩ := H (Downset (0 : I)) hfac (fun _ _ _ => hsub _ _)
  have e0 := f.toEAIso.map_zero'
  have e1 := f.map_one
  rw [show (0 : Downset (0 : I)) = 1 from hsub _ _, e1] at e0
  simp only [HSum.one_def, HSum.zero_def] at e0
  cases e0

/-- **SEA 73** (`prop:assoc-a-convex`, second.tex:2129, Proposition), corrected
(`E ≠ {0}`): a non-trivial normal a-convex factor `E` with an associative
sequential product is isomorphic to a horizontal sum of copies of `[0,1]`,
with the product `(λ, α) ⊙ (μ, β) = (λμ, α)` (`unitHSumNormalSEA`).

Proof as printed: idempotents are central (SEA 69), so `0, 1` are the only
ones and there are no zero divisors (SEA 72); for commuting `S` with an
element outside `{0,1}`, `S''` is a directed-complete effect monoid without
zero divisors, hence `[0,1]` (**OAP 71**, `bicomm_iso_unit`), giving the
"lines" `φ : [0,1] → E` (unital additive maps; the index set is the type
`Line E` of all of them, which the print indexes by a maximal family of
mutually non-commuting elements).  `Θ(λ, φ) = φ(λ)` is a bijection (two lines
through a common point outside `{0,1}` coincide, `line_eq_of_meet`; every
element lies on a line), multiplicative (`line_mul`) and reflects summability
(`line_eq_of_perp`, the print's `φ_a(½) ⋁ φ_b(½) = 1` argument).  The print's
detour through `q_c` is not needed: OAP 71 applies to `S''` directly. -/
theorem sea73_assoc_factor {E : Type u} [EffectAlgebra E] [NormalSEA E]
    (hF : IsAConvexFactor E) (hA : IsAssociativeSEA E) (h10 : (1 : E) ≠ 0) :
    ∃ ι : Type u, Nonempty (SEAIso E (HSum (fun _ : ι => I))) := by
  have hid : ∀ p : E, IsIdempotent p → p = 0 ∨ p = 1 := by
    intro p hp
    have : p ∈ center E := sea69_idempotent_central hA hp
    rw [hF.2] at this
    simpa using this
  obtain ⟨A⟩ := hF.1
  let φ0 : Line E := ⟨fun l => A.act l 1, A.additive 1, A.one_act 1⟩
  exact ⟨Line E, ⟨SEAIso.symm
    { toEquiv := Equiv.ofBijective _ (theta73_bijective hid h10 φ0)
      map_one := rfl
      perp_iff := theta73_perp_iff hid h10 φ0
      map_ovee := theta73_ovee φ0
      map_seq := theta73_seq hid h10 φ0 }⟩⟩

end Papers.SEA
