import Papers.REC.Rec136Hyps

/-!
# REC 136: the Albert-algebra hypothesis weakened to a bounded-rank ideal

Plan / analysis (follow-up to `Rec136Hyps.lean`).  `rec136_weak_hypfree` uses
`JBWExceptionalSummand` (from H-O–S 7.2.7) and `ExceptionalAlbertPoint` (from Shultz 1979
Thm 3.9), the latter with two parts: (i) an exchangeable family of `n ≥ 2` orthogonal
idempotents summing to `1`, (ii) a multiplicative `χ : V → M₃(𝕆)_sa` with `χ 1 ≠ 0`.

What `tower_absurd` really needs from (ii) is only this: the kernel of `χ` is a *proper
ideal* (`1 ∉ I`, `V * I ⊆ I`) of *bounded rank*: at most `D` pairwise orthogonal
idempotents lie outside it, with `D` **uniform** over all purely exceptional algebras (the
tower object `X` is chosen after `D`, and the corner of `V_X` depends on `X`, so a bound
depending on the algebra would be circular).  The all-or-none argument for an
exchangeable family goes through for any ideal: `Q_s p = 2 s(s p) - s² p ∈ I` when
`p ∈ I`.  Hence
* `ExceptionalBoundedRank` (∃ D, every non-zero purely exceptional JBW-algebra has (i)
  and a proper ideal of rank ≤ D) replaces `ExceptionalAlbertPoint`; it is implied by it
  (`exceptionalBoundedRank_of_albert`, `D = dim M₃(𝕆)_sa`), and also by the "finite
  quotient" form `ExceptionalFiniteQuotient` (∃ D, a non-zero linear map into `ℝ^D` whose
  kernel is an ideal: any non-zero quotient of dimension ≤ D, no Jordan or Albert
  structure asked; `exceptionalBoundedRank_of_finiteQuotient`).
* The single Prop `JBWBoundedObstruction` (per JBW-algebra: JW, or an exceptional
  summand, and when purely exceptional and non-zero, (i) plus a bounded-rank proper
  ideal) is implied by REC 52 + REC 55 and gives `rec136` (`rec136_bounded_hypfree`).

What does not go away, and why:
* (i) is needed, and only in `rec135` on the exceptional corner `W` of `V_A`: the
  counting needs a *tensor-stable* family whose members are all-or-none outside every
  ideal; exchangeability by symmetries is what REC 134 transports through `⊗`.  Without
  it (e.g. a single idempotent `p` and the family `p^{±} ⊗ …`) the quotient map may send
  all tensor factors to the same idempotent, and the count stays at 2.  Replacing (i) by
  "any non-trivial idempotent" would need that finite-dimensional exceptional Jordan
  algebras contain no large operator-commuting families of non-special subalgebras — the
  classification of formally real Jordan algebras, not available here.
* The uniform bound is essential (see above); "some non-zero Jordan hom into *a*
  finite-dimensional Jordan algebra" without a bound does not suffice for this argument.
* (ii) in the bounded form could alternatively be cited from the
  Alfsen–Shultz–Størmer Gelfand–Neumark theorem (every JB-algebra embeds in
  `B(H)_sa ⊕ C(X, M₃(𝕆)_sa)`; H-O–S 7.2.3/7.2.4), a result independent of Shultz 1979;
  (i) still needs Shultz (or A–S *Geometry* 4.23 with the H₃(𝕆) structure).
* `JBWExceptionalSummand` is used on `V_A` (to get the corner) and on the tower object
  `V_X`; both uses need the pure exceptionality of a *corner as an object of `C`*, which
  REC's comprehension supplies; merging it with (i)/(ii) into a statement about `V` alone
  would need the corner `cV` as a JBW-algebra type (not built), so the single Prop keeps
  the pure-exceptionality guard.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v

/-! ## The weakened hypotheses -/

section Props

/-- Part (i) of `ExceptionalAlbertPoint` for `V`: `n ≥ 2` pairwise orthogonal idempotents
summing to `1`, mutually exchangeable by symmetries. -/
def HasExchFamily (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ∃ q : Fin n → V, (∀ i, q i * q i = q i) ∧
    (∀ i j, i ≠ j → q i * q j = 0) ∧ ∑ i, q i = ouUnit V ∧
    ∀ i j, ∃ s : V, IsSymmetry s ∧ jQ s (q i) = q j

/-- `V` has a proper ideal `I` (`1 ∉ I`, `V * I ⊆ I`) of rank at most `D`: at most `D`
pairwise orthogonal idempotents lie outside `I`. -/
def HasBoundedRankIdeal (D : ℕ) (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] : Prop :=
  ∃ J : Submodule ℝ V, (∀ a ∈ J, ∀ b : V, b * a ∈ J) ∧ ouUnit V ∉ J ∧
    ∀ (m : ℕ) (f : Fin m → V), (∀ i, f i * f i = f i) → (∀ i j, i ≠ j → f i * f j = 0) →
      (∀ i, f i ∉ J) → m ≤ D

/-- Weakening of `ExceptionalAlbertPoint` (a corollary of **REC 55**, Shultz 1979 Thm 3.9):
there is a uniform `D` such that every non-zero purely exceptional JBW-algebra has (i) an
exchangeable family of `n ≥ 2` orthogonal idempotents summing to `1`, and (ii) a proper
ideal of rank at most `D` (in place of a unital-at-a-point map into `M₃(𝕆)_sa`). -/
def ExceptionalBoundedRank : Prop :=
  ∃ D : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    [Mul V], JBWAlgebra V → IsPurelyExceptional.{v, v} V → ouUnit V ≠ 0 →
      HasExchFamily V ∧ HasBoundedRankIdeal D V

/-- The finite-quotient form of (ii): a uniform `D` such that every non-zero purely
exceptional JBW-algebra has (i), and a linear map into `ℝ^D` not killing `1` whose kernel
is an ideal (i.e. a non-zero quotient algebra of dimension `≤ D`). -/
def ExceptionalFiniteQuotient : Prop :=
  ∃ D : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    [Mul V], JBWAlgebra V → IsPurelyExceptional.{v, v} V → ouUnit V ≠ 0 →
      HasExchFamily V ∧ ∃ χ : V →ₗ[ℝ] (Fin D → ℝ), χ (ouUnit V) ≠ 0 ∧
        ∀ a b : V, χ a = 0 → χ (b * a) = 0

/-- One Prop for both inputs: every JBW-algebra is JW, or it has a non-zero central
idempotent with purely exceptional summand and, if it is itself purely exceptional and
non-zero, an exchangeable family (i) and a proper ideal of rank `≤ D` (uniform `D`).
Implied by REC 52 + REC 55 (`jbwBoundedObstruction_of_HOS_shultz`). -/
def JBWBoundedObstruction : Prop :=
  ∃ D : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    [Mul V], JBWAlgebra V → IsJWAlgebra V ∨
      ((∃ c : V, c ≠ 0 ∧ c * c = c ∧ (∀ x y : V, c * (x * y) = x * (c * y)) ∧
        ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] (ψ : V →ₗ[ℝ] 𝔅), IsJordanHomInto V 𝔅 ψ →
          ∀ x, c * x = x → ψ x = 0) ∧
        (IsPurelyExceptional.{v, v} V → ouUnit V ≠ 0 →
          HasExchFamily V ∧ HasBoundedRankIdeal D V))

theorem exceptionalBoundedRank_of_albert (hS : ExceptionalAlbertPoint.{v}) :
    ExceptionalBoundedRank.{v} := by
  open Papers.EJA.Albert in
  refine ⟨Module.finrank ℝ Alb, fun V _ _ _ _ _ hV hpe hne => ?_⟩
  obtain ⟨hfam, χ, hχm, hχ1⟩ := hS V hV hpe hne
  refine ⟨hfam, LinearMap.ker χ, fun a ha b => ?_, hχ1, fun m f hf1 hf2 hfI => ?_⟩
  · rw [LinearMap.mem_ker] at ha ⊢
    rw [hχm, ha, alb_mul_zero]
  · have := alb_orth_idem_card_le (fun i => χ (f i)) (fun i => by rw [← hχm, hf1])
      (fun i j hij => by rw [← hχm, hf2 i j hij, map_zero])
      (fun i h => hfI i (LinearMap.mem_ker.2 h))
    simpa using this

theorem exceptionalFiniteQuotient_of_albert (hS : ExceptionalAlbertPoint.{v}) :
    ExceptionalFiniteQuotient.{v} := by
  open Papers.EJA.Albert in
  refine ⟨Module.finrank ℝ Alb, fun V _ _ _ _ _ hV hpe hne => ?_⟩
  obtain ⟨hfam, χ, hχm, hχ1⟩ := hS V hV hpe hne
  let E := (Module.finBasis ℝ Alb).equivFun
  refine ⟨hfam, E.toLinearMap ∘ₗ χ, fun h => hχ1 (E.injective (h.trans (map_zero E).symm)),
    fun a b ha => ?_⟩
  have ha' : χ a = 0 := E.injective (ha.trans (map_zero E).symm)
  show E (χ (b * a)) = 0
  rw [hχm, ha', alb_mul_zero, map_zero]

theorem exceptionalBoundedRank_of_finiteQuotient (hF : ExceptionalFiniteQuotient.{v}) :
    ExceptionalBoundedRank.{v} := by
  obtain ⟨D, hD⟩ := hF
  refine ⟨D, fun V _ _ _ _ _ hV hpe hne => ?_⟩
  have : JBAlgebra V := hV.toJBAlgebra
  obtain ⟨hfam, χ, hχ1, hχi⟩ := hD V hV hpe hne
  refine ⟨hfam, LinearMap.ker χ, fun a ha b => ?_, hχ1, fun m f hf1 hf2 hfI => ?_⟩
  · exact LinearMap.mem_ker.2 (hχi a b (LinearMap.mem_ker.1 ha))
  · have hli : LinearIndependent ℝ (fun i => χ (f i)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hy : χ (∑ j, g j • f j) = 0 := by
        rw [map_sum]; simpa only [map_smul] using hg
      let L : V →ₗ[ℝ] V :=
        { toFun := fun x => f i * x
          map_add' := fun x y => jb_mul_add _ _ _
          map_smul' := fun r x => jb_mul_smul r _ _ }
      have hL : L (∑ j, g j • f j) = g i • f i := by
        rw [map_sum]
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, jb_mul_smul]
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [hf2 i j (Ne.symm hj), smul_zero])
          (fun h => (h (Finset.mem_univ i)).elim), hf1]
      have h2 : χ (g i • f i) = 0 := by
        rw [← hL]; exact hχi _ _ hy
      rw [map_smul] at h2
      exact (smul_eq_zero.1 h2).resolve_right (fun h => hfI i (LinearMap.mem_ker.2 h))
    have := hli.fintype_card_le_finrank
    simpa using this

/-- A non-zero purely exceptional JBW-algebra is not JW. -/
theorem not_jw_of_pe (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] (hpe : IsPurelyExceptional.{v, v} V) (hne : ouUnit V ≠ 0) :
    ¬ IsJWAlgebra V := by
  rintro ⟨𝔄, i1, -, -, -, φ, hφ, hinj, -⟩
  have h0 := hpe 𝔄 φ hφ
  apply hne
  apply hinj
  rw [h0, map_zero, LinearMap.zero_apply]

theorem jbwBoundedObstruction_of_weak (hP : JBWExceptionalSummand.{v})
    (hS : ExceptionalBoundedRank.{v}) : JBWBoundedObstruction.{v} := by
  obtain ⟨D, hD⟩ := hS
  refine ⟨D, fun V _ _ _ _ _ hV => ?_⟩
  rcases hP V hV with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, fun hpe hne => hD V hV hpe hne⟩

theorem summand_of_bounded (hQ : JBWBoundedObstruction.{v}) : JBWExceptionalSummand.{v} := by
  obtain ⟨D, hD⟩ := hQ
  intro V _ _ _ _ _ hV
  rcases hD V hV with h | h
  · exact Or.inl h
  · exact Or.inr h.1

theorem boundedRank_of_bounded (hQ : JBWBoundedObstruction.{v}) :
    ExceptionalBoundedRank.{v} := by
  obtain ⟨D, hD⟩ := hQ
  refine ⟨D, fun V _ _ _ _ _ hV hpe hne => ?_⟩
  rcases hD V hV with h | h
  · exact (not_jw_of_pe V hpe hne h).elim
  · exact h.2 hpe hne

/-- `JBWBoundedObstruction` follows from REC 52 and REC 55 (via the corollaries of
`Rec136Hyps`). -/
theorem jbwBoundedObstruction_of_HOS_shultz (hHOS : HancheOlsenStormerDecomposition.{v})
    (hSh : ShultzExceptionalStructure.{v}) : JBWBoundedObstruction.{v} :=
  jbwBoundedObstruction_of_weak (jbwExceptionalSummand_of_HOS hHOS)
    (exceptionalBoundedRank_of_albert (exceptionalAlbertPoint_of_shultz hSh))

end Props

/-! ## REC 135 and 136 from the bounded-rank hypothesis -/

section Rec135Bounded

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- As `tower_absurd`, with a bounded-rank proper ideal of the exceptional corner in place
of a map into `M₃(𝕆)_sa`. -/
theorem tower_absurd_bounded (hP : JBWExceptionalSummand.{v}) (D : ℕ)
    (hR : ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
      [Mul V], JBWAlgebra V → IsPurelyExceptional.{v, v} V → ouUnit V ≠ 0 →
        HasBoundedRankIdeal D V)
    {W X : C} (hWne : ouUnit (VA (realSplit ψ₀) W) ≠ 0)
    (hpe : letI := jbMul (realSplit ψ₀) hRC h119 W;
      IsPurelyExceptional.{v, v} (VA (realSplit ψ₀) W))
    {ι : Type} [Fintype ι] (p : ι → VA (realSplit ψ₀) X)
    (hk : D < Fintype.card ι)
    (hp : VFam (realSplit ψ₀) hRC h119 X p)
    (e : VA (realSplit ψ₀) W →ₗ[ℝ] VA (realSplit ψ₀) X) (he : Function.Injective e)
    (hem : ∀ a b, e (jm (realSplit ψ₀) hRC h119 W a b) =
      jm (realSplit ψ₀) hRC h119 X (e a) (e b)) : False := by
  letI iX := jbMul (realSplit ψ₀) hRC h119 X
  rcases hP (VA (realSplit ψ₀) X) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 X) with
    ⟨𝔄, j1, j2, j3, j4, φ', hφ'J, hφ'i, -⟩ | ⟨d, hd0, hdd, hdcen, hdvan⟩
  · letI iW := jbMul (realSplit ψ₀) hRC h119 W
    have hψ : IsJordanHomInto (VA (realSplit ψ₀) W) 𝔄 (φ' ∘ₗ e) := by
      refine ⟨fun a => hφ'J.1 _, fun a b => ?_⟩
      show φ' (e (jm (realSplit ψ₀) hRC h119 W a b)) = _
      rw [hem]
      exact hφ'J.2 _ _
    have hz := LinearMap.congr_fun (hpe 𝔄 _ hψ) (ouUnit (VA (realSplit ψ₀) W))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    exact hWne (he ((hφ'i (hz.trans (map_zero φ').symm)).trans (map_zero e).symm))
  · obtain ⟨W', ⟨ω'⟩, hpe', π, hπ1, hπm⟩ :=
      corner_of_summand (realSplit ψ₀) hRC h119 rfl X hd0 hdd hdcen hdvan
    letI iW' := jbMul (realSplit ψ₀) hRC h119 W'
    obtain ⟨J, hJi, hJ1, hJr⟩ :=
      hR (VA (realSplit ψ₀) W') (jbw_real hRC h119 φ₀ ψ₀ h1 h2 W') hpe'
        (unit_ne_zero_real φ₀ ψ₀ ⟨ω'⟩)
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    have hsum : ∑ i, π (p i) = ouUnit (VA (realSplit ψ₀) W') := by
      rw [← map_sum, hp3, hπ1]
    have hall : ∀ i, π (p i) ∉ J := by
      intro i hi
      apply hJ1
      rw [← hsum]
      refine J.sum_mem fun j _ => ?_
      obtain ⟨s, -, hsj⟩ := hp4 i j
      rw [← hsj]
      show π ((2 : ℝ) • jm (realSplit ψ₀) hRC h119 X s (jm (realSplit ψ₀) hRC h119 X s (p i)) -
        jm (realSplit ψ₀) hRC h119 X (jm (realSplit ψ₀) hRC h119 X s s) (p i)) ∈ J
      rw [map_sub, map_smul, hπm, hπm, hπm]
      exact J.sub_mem (J.smul_mem _ (hJi _ (hJi _ hi _) _)) (hJi _ hi _)
    let f : Fin (Fintype.card ι) → VA (realSplit ψ₀) W' :=
      fun t => π (p ((Fintype.equivFin ι).symm t))
    have hle := hJr _ f (fun t => by
        show jm (realSplit ψ₀) hRC h119 W' (π _) (π _) = π _
        rw [← hπm, hp1])
      (fun t t' htt' => by
        show jm (realSplit ψ₀) hRC h119 W' (π _) (π _) = 0
        rw [← hπm, hp2 _ _ (fun h => htt' ((Fintype.equivFin ι).symm.injective h)), map_zero])
      (fun t => hall _)
    omega

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition) from `JBWExceptionalSummand` (corollary of
REC 52) and `ExceptionalBoundedRank` (weaker than the corollary `ExceptionalAlbertPoint` of
REC 55): with scalars `[0,1]`, every `V_A` is a JW-algebra. -/
theorem rec135_bounded (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalBoundedRank.{v})
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (A : C) :
    letI := jbMul (realSplit ψ₀) hRC h119 A; IsJWAlgebra (VA (realSplit ψ₀) A) := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  obtain ⟨D, hD⟩ := hS
  letI iA := jbMul σs hRC h119 A
  rcases hP (VA σs A) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 A) with hJW | ⟨c, hc0, hcc, hcen, hvan⟩
  · exact hJW
  exfalso
  obtain ⟨W, ⟨ω⟩, hpe, -⟩ := corner_of_summand σs hRC h119 h0 A hc0 hcc hcen hvan
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ ⟨ω⟩
  letI iW := jbMul σs hRC h119 W
  obtain ⟨⟨n, hn, q, hq1, hq2, hq3, hq4⟩, -⟩ :=
    hD (VA σs W) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 W) hpe hWne
  obtain ⟨X, ι, _, p, hk, hp, e, he, hem⟩ :=
    tower σs hRC h119 h0 W ⟨ω⟩ hn q ⟨hq1, hq2, hq3, hq4⟩ D
  exact tower_absurd_bounded hRC h119 φ₀ ψ₀ h1 h2 hP D
    (fun V _ _ _ _ _ hV hpe hne => (hD V hV hpe hne).2) hWne hpe p hk hp e he hem

end Rec135Bounded

section Rec136Bounded

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

include hRC h119 in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem), statement exactly as `rec136`,
from `JBWExceptionalSummand` and `ExceptionalBoundedRank`. -/
theorem rec136_bounded (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalBoundedRank.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) := by
  rcases seq_scal_cases hirr with h | h | ⟨φ₀, ψ₀, h1, h2⟩
  · set σs := trivSplit h
    have hJBW : ∀ A : C, @JBWAlgebra (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) := fun A =>
      haveI := va_subsingleton h A
      @JBWAlgebra.mk (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) (jbMul_spec σs hRC h119 A)
        (VA_dc σs A) (fun a b hab => (hab (Subsingleton.elim a b)).elim)
    have hJW : ∀ A : C, letI := jbMul σs hRC h119 A; IsJWAlgebra (VA σs A) := fun A =>
      haveI := va_subsingleton h A
      @isJW_of_subsingleton (VA σs A) _ _ _ _ (jbMul σs hRC h119 A) _
    exact jwFunctor_spec hRC h119 σs rfl hJBW hJW
  · exact (h01 h).elim
  · exact jwFunctor_spec hRC h119 (realSplit ψ₀) rfl
      (jbw_real hRC h119 φ₀ ψ₀ h1 h2) (rec135_bounded hRC h119 φ₀ ψ₀ h1 h2 hP hS)

/-- **REC 136** with REC 119 and REC 121's criterion discharged, from
`JBWExceptionalSummand` and `ExceptionalBoundedRank` only. -/
theorem rec136_bounded_weak_hypfree (hP : JBWExceptionalSummand.{v})
    (hS : ExceptionalBoundedRank.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_bounded alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds hP hS
    hirr h01

/-- **REC 136** (`rec136_hypfree`'s statement) from the single named hypothesis
`JBWBoundedObstruction` (implied by REC 52 + REC 55, `jbwBoundedObstruction_of_HOS_shultz`). -/
theorem rec136_bounded_hypfree (hQ : JBWBoundedObstruction.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_bounded_weak_hypfree (summand_of_bounded hQ) (boundedRank_of_bounded hQ) hirr h01

end Rec136Bounded

end Papers.REC

#print axioms Papers.REC.exceptionalBoundedRank_of_albert
#print axioms Papers.REC.exceptionalBoundedRank_of_finiteQuotient
#print axioms Papers.REC.exceptionalFiniteQuotient_of_albert
#print axioms Papers.REC.jbwBoundedObstruction_of_HOS_shultz
#print axioms Papers.REC.rec135_bounded
#print axioms Papers.REC.rec136_bounded_weak_hypfree
#print axioms Papers.REC.rec136_bounded_hypfree
