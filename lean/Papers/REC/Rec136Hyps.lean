import Papers.REC.Rec119

/-!
# REC 136's literature hypotheses, reduced: REC 132 eliminated, REC 52 and 55 weakened

Plan / analysis (B. Westerbaan, J. van de Wetering, arXiv:2109.10707, §6).
`rec136` needs only `rec135` (every `V_A` is JW, scalars `[0,1]`).  What `rec135` really
uses from the three named results:
* REC 52 (H-O–S 7.2.7, `HancheOlsenStormerDecomposition`): only "V is JW, or V has a
  non-zero central idempotent `c` with every Jordan hom into a C*-algebra vanishing on
  `cV`" (the φ-clause is used only for `c = 0`).  Named here `JBWExceptionalSummand`;
  `jbwExceptionalSummand_of_HOS` proves it from REC 52.
* REC 55 (Shultz 1979 Thm 3.9, `ShultzExceptionalStructure`): only via REC 133 (three
  exchangeable idempotents).  The argument below uses two consequences: a non-zero purely
  exceptional JBW-algebra has (i) `n ≥ 2` mutually exchangeable orthogonal idempotents
  summing to `1`, and (ii) a multiplicative linear map into the Albert algebra `M₃(𝕆)_sa`
  not killing `1` (evaluation of `C(X, M₃(𝕆)_sa)` at a point).  Named here
  `ExceptionalAlbertPoint`; `exceptionalAlbertPoint_of_shultz` proves it from REC 55.
* REC 132 (A–S *Geometry* 4.4, `AlfsenShultzFourExchangeable`): **not needed**.  The
  paper uses it only to make `V_{W⊗W}` JW (`W` the exceptional corner).  Replacement,
  inside REC's setting:
  1. (`fam_tens`) mutually exchangeable orthogonal idempotent families summing to `1` in
     `V_X`, `V_Y` tensor to one in `V_{X⊗Y}` (REC 124/128/134, as in `rec135`).
  2. (`tower`) from the `n ≥ 2` family of (i) in `V_W`, get for every `k` an object `X`
     with such a family of more than `k` members and an injective Jordan embedding
     `V_W → V_X` (iterate `a ↦ a ⊗ 1`, REC 127).  Take `k = dim M₃(𝕆)_sa`.
  3. (`tower_absurd`) apply `JBWExceptionalSummand` to `V_X`.  If JW, `V_W` embeds
     into a C*-algebra by a Jordan hom — contradiction with purely exceptional.  Else the
     exceptional corner `W'` of `X` is purely exceptional and non-zero; the corner map
     `π : V_X → V_{W'}` (Jordan, unital) followed by the map `χ` of (ii) sends the
     family to orthogonal idempotents of `M₃(𝕆)_sa` which are all non-zero (exchangeable
     ⇒ all-or-none zero, and they sum to `χ 1 ≠ 0`), hence linearly independent: more
     than `dim M₃(𝕆)_sa` of them, absurd (`alb_orth_idem_card_le`).
  So Lemma 4.4 (Jacobson coordinatization) is replaced by a dimension count in the
  Albert algebra, using the tensor structure that REC's `V_A` come with.
Estimates for (a): proving REC 132 outright needs Jacobson coordinatization for `n ≥ 4`
plus a JW-embedding of `H_n(D)` (well over 3,000 lines); REC 52 needs `W*(V)`, Glennie's
identity and the central-support machinery; REC 55 needs the Stonean fibration.  None is
attempted; instead (b): `rec135_weak`/`rec136_weak` use only the two weaker Props, and
`rec136_hypfree_noAS4` is REC 136 from REC 52 + REC 55 alone.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open scoped unitInterval

namespace Papers.REC

universe u v

/-! ## The two weaker named hypotheses, and their derivation from REC 52 and REC 55 -/

section WeakProps

/-- A direct corollary of **REC 52** (Hanche-Olsen–Størmer, *Jordan operator algebras*,
Thm 7.2.7): a JBW-algebra is a JW-algebra, or it has a non-zero central idempotent `c`
(`c² = c`, `c(xy) = x(cy)`) whose summand `cV = {x ; cx = x}` is purely exceptional
(every Jordan homomorphism into a C*-algebra vanishes on it).  Proved from
`HancheOlsenStormerDecomposition` in `jbwExceptionalSummand_of_HOS`. -/
def JBWExceptionalSummand : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → IsJWAlgebra V ∨
      ∃ c : V, c ≠ 0 ∧ c * c = c ∧ (∀ x y : V, c * (x * y) = x * (c * y)) ∧
        ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] (ψ : V →ₗ[ℝ] 𝔅), IsJordanHomInto V 𝔅 ψ →
          ∀ x, c * x = x → ψ x = 0

/-- A direct corollary of **REC 55** (Shultz 1979, Thm 3.9: a purely exceptional
JBW-algebra is `C(X, M₃(𝕆)_sa)`): a non-zero purely exceptional JBW-algebra has
(i) `n ≥ 2` pairwise orthogonal idempotents summing to `1`, mutually exchangeable by
symmetries (REC 133 gives `n = 3`), and (ii) a multiplicative linear map into the Albert
algebra `M₃(𝕆)_sa` (`Papers.EJA.Albert.Alb`) not vanishing at `1` (evaluation at a
point).  Proved from `ShultzExceptionalStructure` in `exceptionalAlbertPoint_of_shultz`. -/
def ExceptionalAlbertPoint : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → IsPurelyExceptional.{v, v} V → ouUnit V ≠ 0 →
      (∃ n : ℕ, 2 ≤ n ∧ ∃ q : Fin n → V, (∀ i, q i * q i = q i) ∧
        (∀ i j, i ≠ j → q i * q j = 0) ∧ ∑ i, q i = ouUnit V ∧
        ∀ i j, ∃ s : V, IsSymmetry s ∧ jQ s (q i) = q j) ∧
      ∃ χ : V →ₗ[ℝ] Papers.EJA.Albert.Alb, (∀ a b : V, χ (a * b) = χ a * χ b) ∧
        χ (ouUnit V) ≠ 0

theorem jbwExceptionalSummand_of_HOS (h : HancheOlsenStormerDecomposition.{v}) :
    JBWExceptionalSummand.{v} := by
  intro V _ _ _ _ _ hV
  obtain ⟨c, hcc, hcen, ⟨𝔄, i1, i2, i3, i4, φ, hφJ, hφn, hker⟩, hvan⟩ := h V hV
  by_cases hc0 : c = 0
  · left
    refine ⟨𝔄, i1, i2, i3, i4, φ, hφJ, fun x y hxy => ?_, hφn⟩
    have e1 : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have e2 := (hker (x - y)).1 e1
    rw [hc0, jb_zero_mul] at e2
    exact sub_eq_zero.1 e2.symm
  · exact Or.inr ⟨c, hc0, hcc, hcen, fun 𝔅 _ ψ hψ x hx => hvan 𝔅 ψ hψ x hx⟩

open Papers.EJA.Albert in
theorem alb_mul_zero (x : Alb) : x * 0 = 0 := by
  have := mul_smul' 0 x 0
  rwa [zero_smul, zero_smul] at this

open Papers.EJA.Albert in
theorem alb_one_ne_zero : (1 : Alb) ≠ 0 := by
  intro h
  apply AlbertFacts.aE_ne_zero 0
  rw [← mul_one' (AlbertFacts.aE 0), h, alb_mul_zero]

theorem exceptionalAlbertPoint_of_shultz (hSh : ShultzExceptionalStructure.{v}) :
    ExceptionalAlbertPoint.{v} := by
  open Papers.EJA.Albert in
  intro V _ _ _ _ _ hV hpe hne
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := rec133 hSh V hV hpe ⟨_, hne⟩
    exact ⟨3, by norm_num, q, fun i => (hq1 i).1, hq2, hq3, hq4⟩
  · obtain ⟨X, iX, -, Φ, hΦ⟩ := hSh V hV hpe
    have hX : Nonempty X := by
      by_contra hc
      apply hne
      apply Φ.injective
      ext t
      exact (hc ⟨t⟩).elim
    obtain ⟨t⟩ := hX
    let χ : V →ₗ[ℝ] Alb :=
      { toFun := fun w => Φ w t
        map_add' := fun a b => by simp
        map_smul' := fun r a => by simp }
    refine ⟨χ, fun a b => hΦ a b t, ?_⟩
    have h1 : Φ (ouUnit V) t = 1 := by
      have := congrArg (fun y => Φ y t)
        (JBAlgebra.one_mul (A := V) (Φ.symm (ContinuousMap.const X 1)))
      simp only [hΦ, LinearEquiv.apply_symm_apply, ContinuousMap.const_apply] at this
      rwa [mul_one'] at this
    show Φ (ouUnit V) t ≠ 0
    rw [h1]
    exact alb_one_ne_zero

open Papers.EJA.Albert in
/-- Pairwise orthogonal non-zero idempotents of `M₃(𝕆)_sa` are linearly independent, so
there are at most `dim M₃(𝕆)_sa` of them. -/
theorem alb_orth_idem_card_le {ι : Type} [Fintype ι] (f : ι → Alb) (h1 : ∀ i, f i * f i = f i)
    (h2 : ∀ i j, i ≠ j → f i * f j = 0) (h3 : ∀ i, f i ≠ 0) :
    Fintype.card ι ≤ Module.finrank ℝ Alb := by
  apply LinearIndependent.fintype_card_le_finrank
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let L : Alb →ₗ[ℝ] Alb :=
    { toFun := fun x => f i * x
      map_add' := fun x y => mul_add' _ _ _
      map_smul' := fun r x => mul_smul' r _ _ }
  have := congrArg L hg
  rw [map_sum, map_zero] at this
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, mul_smul'] at this
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [h2 i j (Ne.symm hj), smul_zero])
    (fun h => (h (Finset.mem_univ i)).elim), h1] at this
  exact (smul_eq_zero.1 this).resolve_right (h3 i)

end WeakProps

/-! ## Exchangeable families in `V_X` and their tensors -/

section Families

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C)
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

/-- A family of pairwise orthogonal idempotents of `V_X` summing to `1`, mutually
exchangeable by symmetries. -/
def VFam (X : C) {ι : Type} [Fintype ι] (p : ι → VA σs X) : Prop :=
  (∀ i, jm σs hRC h119 X (p i) (p i) = p i) ∧
    (∀ i j, i ≠ j → jm σs hRC h119 X (p i) (p j) = 0) ∧ ∑ i, p i = ouUnit (VA σs X) ∧
    ∀ i j, ∃ s, jm σs hRC h119 X s s = ouUnit (VA σs X) ∧ jQA σs hRC h119 X s (p i) = p j

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C] (h0 : σs.s = 0)

include h0 in
/-- Tensors of exchangeable families are exchangeable families (REC 124, 128, 134). -/
theorem fam_tens {X Y : C} {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → VA σs X}
    {q : κ → VA σs Y} (hp : VFam σs hRC h119 X p) (hq : VFam σs hRC h119 Y q) :
    VFam σs hRC h119 (X ⊗ Y) (fun ik : ι × κ => tensV σs (p ik.1) (q ik.2)) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  choose x hx hpx using fun i => jm_idem_gmap σs hRC h119 X (hp1 i)
  choose y hy hqy using fun k => jm_idem_gmap σs hRC h119 Y (hq1 k)
  refine ⟨fun ik => ?_, fun ik jl hne => ?_, ?_, fun ik jl => ?_⟩
  · obtain ⟨z, hz, e⟩ := jm_idem_tens σs hRC h119 (hp1 ik.1) (hq1 ik.2) h0
    show jm σs hRC h119 (X ⊗ Y) (tensV σs (p ik.1) (q ik.2)) (tensV σs (p ik.1) (q ik.2)) =
      tensV σs (p ik.1) (q ik.2)
    rw [e]; exact jm_gmap_idem σs hRC h119 h0 hz
  · show jm σs hRC h119 (X ⊗ Y) (tensV σs (p ik.1) (q ik.2)) (tensV σs (p jl.1) (q jl.2)) = 0
    rw [hpx ik.1, hqy ik.2, hpx jl.1, hqy jl.2, tensV_gmap, tensV_gmap]
    refine jm_zero_of_Uop hRC h119 (cptTens_idem σs h0 (hx _) (hy _)) ?_
    rw [← tensV_gmap, Uop_cptTens_apply σs h0]
    have h' : ik.1 ≠ jl.1 ∨ ik.2 ≠ jl.2 := by
      by_contra hc
      push Not at hc
      exact hne (Prod.ext hc.1 hc.2)
    rcases h' with h | h
    · have := hp2 _ _ h
      rw [hpx, hpx] at this
      rw [Uop_zero_of_jm hRC h119 (hx _) this, tensV_zero_left]
    · have := hq2 _ _ h
      rw [hqy, hqy] at this
      rw [Uop_zero_of_jm hRC h119 (hy _) this, tensV_zero_right]
  · rw [Fintype.sum_prod_type]
    have hin : ∀ i, ∑ k, tensV σs (p i) (q k) = tensV σs (p i) (ouUnit (VA σs Y)) := by
      intro i
      rw [← hq3]
      show ∑ k, vtens σs (q k) (p i) = vtens σs (∑ k, q k) (p i)
      rw [map_sum, LinearMap.sum_apply]
    simp only [hin]
    rw [← tensV_unit σs, ← hp3]
    show ∑ i, vtens σs (ouUnit (VA σs Y)) (p i) = vtens σs (ouUnit (VA σs Y)) (∑ i, p i)
    rw [map_sum]
  · obtain ⟨s₁, hs₁, e₁⟩ := hp4 ik.1 jl.1
    obtain ⟨s₂, hs₂, e₂⟩ := hq4 ik.2 jl.2
    have := rec134 σs hRC h119 h0 (hp1 _) (hp1 _) hs₁ e₁ (hq1 _) (hq1 _) hs₂ e₂
    exact ⟨tensV σs s₁ s₂, this.2.2.1, this.2.2.2⟩

include h0 in
/-- From an exchangeable family of `n ≥ 2` members in `V_W`: for every `k`, an object `X`
with an exchangeable family of more than `k` members, and an injective Jordan embedding
`V_W → V_X` (iterating `X ↦ X ⊗ W`, `a ↦ a ⊗ 1`, REC 127). -/
theorem tower (W : C) (hW : Nonempty (Stat W)) {n : ℕ} (hn : 2 ≤ n) (q : Fin n → VA σs W)
    (hq : VFam σs hRC h119 W q) (k : ℕ) :
    ∃ (X : C) (ι : Type) (_ : Fintype ι) (p : ι → VA σs X), k < Fintype.card ι ∧
      VFam σs hRC h119 X p ∧ ∃ e : VA σs W →ₗ[ℝ] VA σs X, Function.Injective e ∧
        ∀ a b, e (jm σs hRC h119 W a b) = jm σs hRC h119 X (e a) (e b) := by
  induction k with
  | zero =>
    exact ⟨W, Fin n, inferInstance, q, by rw [Fintype.card_fin]; omega, hq, LinearMap.id,
      Function.injective_id, fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨X, ι, _, p, hk, hp, e, he, hem⟩ := ih
    refine ⟨X ⊗ W, ι × Fin n, inferInstance, _, ?_, fam_tens σs hRC h119 h0 hp hq,
      vtens σs (ouUnit (VA σs W)) ∘ₗ e, ?_, fun a b => ?_⟩
    · rw [Fintype.card_prod, Fintype.card_fin]
      nlinarith
    · exact ((rec127 σs hRC h119 h0 X W).2.2.2.2 hW).comp he
    · show tensV σs (e (jm σs hRC h119 W a b)) (ouUnit _) =
        jm σs hRC h119 (X ⊗ W) (tensV σs (e a) (ouUnit _)) (tensV σs (e b) (ouUnit _))
      rw [hem, (rec127 σs hRC h119 h0 X W).1]

end Families

/-! ## Corners of central idempotents -/

section CornerSummand

open SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (σs : ScalarSplit C)
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C) (h0 : σs.s = 0)

include h0 in
/-- A non-zero central idempotent of `V_X` with purely exceptional summand gives an object
`W` (the comprehension) with a state, `V_W` purely exceptional, and the unital Jordan
corner map `V_X → V_W` (as in `rec135`). -/
theorem corner_of_summand (X : C) {c : VA σs X} (hc0 : c ≠ 0)
    (hcc : jm σs hRC h119 X c c = c)
    (hcen : ∀ x y : VA σs X, jm σs hRC h119 X c (jm σs hRC h119 X x y) =
      jm σs hRC h119 X x (jm σs hRC h119 X c y))
    (hvan : ∀ (𝔅 : Type v) [CStarAlgebra 𝔅] (ψ : VA σs X →ₗ[ℝ] 𝔅),
      (letI := jbMul σs hRC h119 X; IsJordanHomInto (VA σs X) 𝔅 ψ) →
        ∀ x, jm σs hRC h119 X c x = x → ψ x = 0) :
    ∃ W : C, Nonempty (Stat W) ∧
      (letI := jbMul σs hRC h119 W; IsPurelyExceptional.{v, v} (VA σs W)) ∧
      ∃ π : VA σs X →ₗ[ℝ] VA σs W, π (ouUnit (VA σs X)) = ouUnit (VA σs W) ∧
        ∀ x w, π (jm σs hRC h119 X x w) = jm σs hRC h119 W (π x) (π w) := by
  obtain ⟨c₀, hc₀, rfl⟩ := jm_idem_gmap σs hRC h119 X hcc
  have hcs : IsSharp c₀.1 := isSharp_of_isIdempotent ((cpt_idem_iff σs c₀).1 hc₀)
  have hcomm : ∀ w : Pred X, SEA.seq w c₀.1 = SEA.seq c₀.1 w := by
    intro w
    have := central_of_jordan σs hRC h119 hc₀ hcen (cptMk σs w (cpt_all σs h0 w))
    have e : SEA.seq c₀.1 w = SEA.seq w c₀.1 := congrArg Subtype.val this
    exact e.symm
  have hc0' : c₀.1 ≠ 0 := fun h => hc0 (by
    rw [show c₀ = 0 from Subtype.ext h, GP.gmap_zero])
  refine ⟨comprObj c₀.1, exists_state_compr hcs hc0',
    corner_purelyExceptional hcs σs hRC h119 h0 rfl hc₀ hcomm hvan,
    stateLin σs (comprMap c₀.1), ?_, fun x w => corner_jordan hcs σs hRC h119 h0 hcomm x w⟩
  show stateLin σs (comprMap c₀.1) (GP.gmap 1) = GP.gmap 1
  rw [stateLin_gmap]; congr 1; apply Subtype.ext
  show comprMap c₀.1 ≫ (1 : CPt σs X).1 = (1 : CPt σs (comprObj c₀.1)).1
  rw [cpt_one_val0 σs h0, cpt_one_val0 σs h0]
  exact compr_total (isComprehension_comprMap c₀.1)

end CornerSummand

/-! ## REC 135 from the two weaker hypotheses -/

section Rec135Weak

open MonoidalCategory SequentialEffectus
open scoped Papers.SEA

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- The contradiction: a purely exceptional non-zero `V_W` cannot embed (Jordan,
injectively) into a `V_X` carrying an exchangeable family of more than `dim M₃(𝕆)_sa`
members. -/
theorem tower_absurd (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertPoint.{v})
    {W X : C} (hWne : ouUnit (VA (realSplit ψ₀) W) ≠ 0)
    (hpe : letI := jbMul (realSplit ψ₀) hRC h119 W;
      IsPurelyExceptional.{v, v} (VA (realSplit ψ₀) W))
    {ι : Type} [Fintype ι] (p : ι → VA (realSplit ψ₀) X)
    (hk : Module.finrank ℝ Papers.EJA.Albert.Alb < Fintype.card ι)
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
    obtain ⟨-, χ, hχm, hχ1⟩ :=
      hS (VA (realSplit ψ₀) W') (jbw_real hRC h119 φ₀ ψ₀ h1 h2 W') hpe' (unit_ne_zero_real φ₀ ψ₀ ⟨ω'⟩)
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    let g := χ ∘ₗ π
    have gm : ∀ a b, g (jm (realSplit ψ₀) hRC h119 X a b) = g a * g b := fun a b => by
      show χ (π (jm (realSplit ψ₀) hRC h119 X a b)) = _
      rw [hπm]
      exact hχm _ _
    have hsum : ∑ i, g (p i) = χ (ouUnit (VA (realSplit ψ₀) W')) := by
      rw [← map_sum, hp3]
      show χ (π _) = _
      rw [hπ1]
    have hall : ∀ i, g (p i) ≠ 0 := by
      intro i hi
      apply hχ1
      rw [← hsum]
      refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨s, -, hsj⟩ := hp4 i j
      rw [← hsj]
      show g ((2 : ℝ) • jm (realSplit ψ₀) hRC h119 X s (jm (realSplit ψ₀) hRC h119 X s (p i)) -
        jm (realSplit ψ₀) hRC h119 X (jm (realSplit ψ₀) hRC h119 X s s) (p i)) = 0
      rw [map_sub, map_smul, gm, gm, gm, hi, alb_mul_zero, alb_mul_zero, alb_mul_zero,
        smul_zero, sub_self]
    have hle := alb_orth_idem_card_le (fun i => g (p i))
      (fun i => by rw [← gm, hp1]) (fun i j hij => by rw [← gm, hp2 i j hij, map_zero]) hall
    omega

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition) from the two weaker named hypotheses
`JBWExceptionalSummand` (a corollary of REC 52) and `ExceptionalAlbertPoint` (a corollary
of REC 55); REC 132 (`AlfsenShultzFourExchangeable`) is not used.  With scalars `[0,1]`,
every `V_A` is a JW-algebra. -/
theorem rec135_weak (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertPoint.{v})
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (A : C) :
    letI := jbMul (realSplit ψ₀) hRC h119 A; IsJWAlgebra (VA (realSplit ψ₀) A) := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  letI iA := jbMul σs hRC h119 A
  rcases hP (VA σs A) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 A) with hJW | ⟨c, hc0, hcc, hcen, hvan⟩
  · exact hJW
  exfalso
  obtain ⟨W, ⟨ω⟩, hpe, -⟩ := corner_of_summand σs hRC h119 h0 A hc0 hcc hcen hvan
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ ⟨ω⟩
  letI iW := jbMul σs hRC h119 W
  obtain ⟨⟨n, hn, q, hq1, hq2, hq3, hq4⟩, -⟩ :=
    hS (VA σs W) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 W) hpe hWne
  obtain ⟨X, ι, _, p, hk, hp, e, he, hem⟩ :=
    tower σs hRC h119 h0 W ⟨ω⟩ hn q ⟨hq1, hq2, hq3, hq4⟩ (Module.finrank ℝ Papers.EJA.Albert.Alb)
  exact tower_absurd hRC h119 φ₀ ψ₀ h1 h2 hP hS hWne hpe p hk hp e he hem

end Rec135Weak

/-! ## REC 136 from the two weaker hypotheses -/

section Rec136Weak

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

include hRC h119 in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem), statement exactly as `rec136`,
from `JBWExceptionalSummand` and `ExceptionalAlbertPoint` (in place of REC 52, 55, 132);
proof as `rec136`, with `rec135_weak` for `rec135`. -/
theorem rec136_weak (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertPoint.{v})
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
      (jbw_real hRC h119 φ₀ ψ₀ h1 h2) (rec135_weak hRC h119 φ₀ ψ₀ h1 h2 hP hS)

/-- **REC 136** with REC 119 and REC 121's criterion discharged (as `rec136_hypfree`),
from the two weaker named hypotheses only. -/
theorem rec136_weak_hypfree (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertPoint.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_weak alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds hP hS hirr h01

/-- **REC 136** (`rec136_hypfree`'s statement) from REC 52 and REC 55 only: REC 132
(`AlfsenShultzFourExchangeable`, A–S *Geometry* Lemma 4.4) is not needed. -/
theorem rec136_hypfree_noAS4 (hHOS : HancheOlsenStormerDecomposition.{v})
    (hSh : ShultzExceptionalStructure.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_weak_hypfree (jbwExceptionalSummand_of_HOS hHOS) (exceptionalAlbertPoint_of_shultz hSh)
    hirr h01

end Rec136Weak

end Papers.REC

#print axioms Papers.REC.jbwExceptionalSummand_of_HOS
#print axioms Papers.REC.exceptionalAlbertPoint_of_shultz
#print axioms Papers.REC.rec135_weak
#print axioms Papers.REC.rec136_weak_hypfree
#print axioms Papers.REC.rec136_hypfree_noAS4
