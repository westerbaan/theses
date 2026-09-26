import Papers.REC.JBWProj
import Papers.REC.Rec136Native

/-!
# REC 136 from `JBWExceptionalSummand` and `ExceptionalNoFourExch` (route (b2))

Plan (research note `docs/research/rec136-noalbert.md` §3, route (b2), as reviewed
2026-09-26; one simplification: the JW case uses `a ↦ c₀(a ⊗ 1)`, not `a ↦ c₀(a ⊗ f)`).
* `ExceptionalNoFourExch`: a purely exceptional JBW-algebra has no four non-zero pairwise
  orthogonal idempotents, pairwise `ExchangeableBySymmetry` (REC 131's notion).  JBW-intrinsic;
  no Albert algebra in the statement.  `exceptionalNoFourExch_of_shultz`: from REC 55
  (evaluate at a point where the first idempotent is non-zero; exchange keeps the others
  non-zero there; four non-zero orthogonal idempotents of `M₃(𝕆)_sa` have trace `≥ 4 > 3`).
* §A, abstract core (`nofour_core`), in a JBW-algebra `V`: given a unital Jordan hom
  `ι : U → V` of a purely exceptional `U`, and `t : Fin 4 → V` pairwise orthogonal, pairwise
  exchangeable, `t 0 ≠ 0`, contradiction.  `c₀ := centralCover (t 0)`; `JBWExceptionalSummand`
  on the JBW-algebra `c₀V` (`CentralIdem.Corner`):
  - JW: `a ↦ φ'(c₀ ι a)` is a Jordan hom of `U` into a C*-algebra, non-zero at `1`
    (`φ'` injective, `c₀ ≠ 0` since `t 0 ≤ c₀`);
  - exceptional: `d` central in `c₀V`, `e := d` as a `CentralIdem (c₀V)`, `K := e.Corner`
    purely exceptional (`corner_purelyExceptional`), JBW.  `P i := e(c₀ t i) ∈ K` are
    orthogonal and exchangeable (`x ↦ cx` is a Jordan hom for central `c`: `exch_proj`).
    `P 0 ≠ 0`: else `d t₀ = 0` (`c₀ t₀ = t₀`); `d` is central in `V` (`central_of_corner`),
    so `1 − d` is a central idempotent above `t₀`, hence above `c₀`, and `d = d c₀ ≤ d(1−d) = 0`.
    All-or-none: `P 0 = Q_σ (P i)` (`i ≠ 0`), so `P i = 0 ⟹ P 0 = 0`.  `ExceptionalNoFourExch`
    on `K` concludes.
* §B, REC glue (`nofour_absurd`): `V_W ≠ 0` purely exceptional; `pe_exists_exch_pair` gives
  `p ⊥ q`, `Q_s p = q`, `s² = 1`; with `pq = ![p, q]` every ordered pair is exchanged by
  `1` or `s` (`exch_symm`).  In `V_{W⊗W}`: `T (i, j) = pq i ⊗ pq j` are pairwise orthogonal
  and exchangeable (REC 124/128/134, as in `fam_tens`, without the sum), `T (0,0) = p ⊗ p ≠ 0`
  (`tens_ne_zero`); `ι a = a ⊗ 1` (REC 127).  `t := T ∘ finProdFinEquiv.symm`, then §A.
* §C: `rec135_nofour`, `rec136_nofour`, `rec136_nofour_hypfree` (statement exactly as
  `rec136_hypfree`), glue as in `Rec136Native`; `rec136_nofour_HOS_shultz` from REC 52 + 55.
  Deviations from the note: the central cover is of `p ⊗ p` (not `f ⊗ f`), and REC 128 enters
  only through REC 134 (`rec128_general` is not needed).
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open scoped InnerProductSpace unitInterval

namespace Papers.REC

universe u v

/-! ## The hypothesis -/

/-- **No four exchangeable idempotents** (a consequence of Shultz 1979 Thm 3.9, REC 55, and
of the proof of Hanche-Olsen–Størmer 7.2.7, REC 52): a purely exceptional JBW-algebra has no
four non-zero, pairwise orthogonal idempotents that are pairwise exchangeable by symmetries
(REC 131).  Proved from `ShultzExceptionalStructure` in `exceptionalNoFourExch_of_shultz`. -/
def ExceptionalNoFourExch : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → IsPurelyExceptional.{v, v} V → ∀ p : Fin 4 → V, (∀ i, p i ≠ 0) →
      (∀ i j, i ≠ j → p i * p j = 0) → (∀ i j, i ≠ j → ExchangeableBySymmetry (p i) (p j)) →
        False

/-! ## §A. The abstract core -/

namespace NoFour

open Papers.SEA.JBW JBWProj

section Generic

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

theorem proj_unit (e : Papers.SEA.JBW.CentralIdem V) : e.proj (ouUnit V) = ouUnit e.Corner :=
  Subtype.ext (JBAlgebra.mul_one e.c)

theorem proj_jQ (e : Papers.SEA.JBW.CentralIdem V) (a b : V) : e.proj (jQ a b) = jQ (e.proj a) (e.proj b) := by
  simp only [jQ, map_sub, map_smul, e.proj_mul]

/-- `x ↦ cx` (`c` central) preserves exchangeability. -/
theorem exch_proj (e : Papers.SEA.JBW.CentralIdem V) {x y : V} (h : ExchangeableBySymmetry x y) :
    ExchangeableBySymmetry (e.proj x) (e.proj y) := by
  obtain ⟨hx, hy, s, hs, hsxy⟩ := h
  refine ⟨by rw [← e.proj_mul, hx], by rw [← e.proj_mul, hy], e.proj s, ?_, by
    rw [← proj_jQ, hsxy]⟩
  show e.proj s * e.proj s = ouUnit e.Corner
  rw [← e.proj_mul, hs, proj_unit]

theorem jQ_zero_right (a : V) : jQ a 0 = 0 := by
  simp only [jQ, jb_mul_zero, smul_zero, sub_zero]

/-- A central idempotent of a central summand `c₀V` is central in `V`. -/
theorem central_of_corner (c₀ : Papers.SEA.JBW.CentralIdem V) (d : c₀.Corner)
    (hd : ∀ x y : c₀.Corner, d * (x * y) = x * (d * y)) (x y : V) :
    d.1 * (x * y) = x * (d.1 * y) := by
  have hdc : c₀.c * d.1 = d.1 := c₀.cx d
  have h1 : ∀ z, d.1 * z = d.1 * (c₀.c * z) := by
    intro z
    have a := c₀.central z d.1
    have b := c₀.central d.1 z
    rw [hdc, JBAlgebra.mul_comm z d.1] at a
    rw [← b, a]
  have h2 : ∀ w, c₀.c * w = w → (c₀.c * x) * w = x * w := by
    intro w hw
    have a := c₀.central w x
    rw [JBAlgebra.mul_comm (c₀.c * x) w, ← a, JBAlgebra.mul_comm w x, c₀.central x w, hw]
  have h3 : c₀.c * (d.1 * y) = d.1 * y := by rw [c₀.central d.1 y, ← h1]
  have key := congrArg Subtype.val (hd (c₀.proj x) (c₀.proj y))
  change d.1 * ((c₀.c * x) * (c₀.c * y)) = (c₀.c * x) * (d.1 * (c₀.c * y)) at key
  rw [c₀.mul_hom, ← h1, ← h1, h2 _ h3] at key
  exact key

end Generic

section Core

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **The abstract core of route (b2)**: a JBW-algebra `V` receiving a unital Jordan hom of a
purely exceptional `U`, and carrying four pairwise orthogonal, pairwise exchangeable
idempotents with `t 0 ≠ 0`, is impossible under `JBWExceptionalSummand` and
`ExceptionalNoFourExch`. -/
theorem nofour_core (hP : JBWExceptionalSummand.{v}) (hN : ExceptionalNoFourExch.{v})
    {U : Type v} [AddCommGroup U] [Module ℝ U] [PartialOrder U] [OrderUnitSpace U] [Mul U]
    (hpe : IsPurelyExceptional.{v, v} U) (ι : U →ₗ[ℝ] V) (hι : ∀ a b, ι (a * b) = ι a * ι b)
    (hι1 : ι (ouUnit U) = ouUnit V) (t : Fin 4 → V) (ht0 : t 0 ≠ 0)
    (horth : ∀ i j, i ≠ j → t i * t j = 0)
    (hex : ∀ i j, i ≠ j → ExchangeableBySymmetry (t i) (t j)) : False := by
  obtain ⟨hid0, -, -⟩ := hex 0 1 (by decide)
  set c₀ := centralCover hid0 with hc₀def
  have ht0le : t 0 ≤ c₀.c := (centralCover_spec hid0).1
  have ht0nn : 0 ≤ t 0 := idem_nonneg hid0
  have hc₀t : c₀.c * t 0 = t 0 := c₀.mul_eq_of_le ht0nn ht0le
  have hc₀ne : c₀.c ≠ 0 := fun h => ht0 (le_antisymm (h ▸ ht0le) ht0nn)
  have hunit : ouUnit c₀.Corner ≠ 0 := fun h => hc₀ne (by
    have := congrArg Subtype.val h
    rwa [Papers.SEA.JBW.CentralIdem.unit_val] at this)
  rcases hP c₀.Corner inferInstance with
    ⟨𝔄, j1, j2, j3, j4, φ', hφ'J, hφ'i, -⟩ | ⟨d, hd0, hdd, hdcen, hdvan⟩
  · -- `c₀V` JW: `a ↦ φ'(c₀ ι a)` is a non-zero Jordan hom of `U`
    have hψ : IsJordanHomInto U 𝔄 (φ' ∘ₗ c₀.proj ∘ₗ ι) := by
      refine ⟨fun a => hφ'J.1 _, fun a b => ?_⟩
      show φ' (c₀.proj (ι (a * b))) = _
      rw [hι, c₀.proj_mul]
      exact hφ'J.2 _ _
    have hz := LinearMap.congr_fun (hpe 𝔄 _ hψ) (ouUnit U)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hι1, proj_unit] at hz
    exact hunit (hφ'i (hz.trans (map_zero φ').symm))
  · -- the purely exceptional summand `K = d(c₀V)` carries four exchangeable idempotents
    let e : Papers.SEA.JBW.CentralIdem c₀.Corner := ⟨d, hdd, hdcen⟩
    have hpeK : IsPurelyExceptional.{v, v} e.Corner := e.corner_purelyExceptional hdvan
    let P : Fin 4 → e.Corner := fun i => e.proj (c₀.proj (t i))
    have hPex : ∀ i j, i ≠ j → ExchangeableBySymmetry (P i) (P j) :=
      fun i j h => exch_proj e (exch_proj c₀ (hex i j h))
    have hPorth : ∀ i j, i ≠ j → P i * P j = 0 := fun i j h => by
      show e.proj _ * e.proj _ = 0
      rw [← e.proj_mul, ← c₀.proj_mul, horth i j h, map_zero, map_zero]
    have hP0 : P 0 ≠ 0 := by
      intro h
      have h' : d.1 * t 0 = 0 := by
        have := congrArg (fun z : e.Corner => z.1.1) h
        change d.1 * (c₀.c * t 0) = 0 at this
        rwa [hc₀t] at this
      let D : Papers.SEA.JBW.CentralIdem V := ⟨d.1, congrArg Subtype.val hdd, central_of_corner c₀ d hdcen⟩
      have hle : t 0 ≤ D.compl.c := by
        have e1 : D.compl.c * t 0 = t 0 := by
          rw [D.compl_mul]
          show t 0 - d.1 * t 0 = t 0
          rw [h', sub_zero]
        have := D.compl.cmul_mono (idem_le_one hid0)
        rwa [e1, JBAlgebra.mul_one] at this
      have hc₀le := (centralCover_spec hid0).2 D.compl hle
      have hm := D.cmul_mono hc₀le
      rw [D.compl_c, jb_mul_sub, JBAlgebra.mul_one, D.idem, sub_self] at hm
      have hm' : c₀.c * d.1 ≤ 0 := by
        rw [JBAlgebra.mul_comm]; exact hm
      rw [c₀.cx d] at hm'
      exact hd0 (Subtype.ext (le_antisymm hm' D.c_nonneg))
    have hPne : ∀ i, P i ≠ 0 := by
      intro i hi
      by_cases h : i = 0
      · exact hP0 (h ▸ hi)
      · obtain ⟨-, -, s, -, hs⟩ := hPex i 0 h
        rw [hi, jQ_zero_right] at hs
        exact hP0 hs.symm
    exact hN e.Corner inferInstance hpeK P hPne hPorth hPex

end Core

end NoFour

/-! ## §B. The REC glue -/

section Rec135NoFour

open MonoidalCategory SequentialEffectus
open NoFour

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- The contradiction (research note §3, route (b2)): a purely exceptional `V_W ≠ 0` is
impossible.  `pe_exists_exch_pair` gives `p ⊥ q` exchanged by a symmetry `s`; in
`V_{W⊗W}` the four products `x ⊗ y` (`x, y ∈ {p, q}`) are pairwise orthogonal and pairwise
exchangeable (REC 124, 128, 134), `p ⊗ p ≠ 0`, and `a ↦ a ⊗ 1` is a unital Jordan hom
(REC 127); `nofour_core` concludes. -/
theorem nofour_absurd (hP : JBWExceptionalSummand.{v}) (hN : ExceptionalNoFourExch.{v})
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] {W : C} (hW : Nonempty (Stat W))
    (hpe : letI := jbMul (realSplit ψ₀) hRC h119 W;
      IsPurelyExceptional.{v, v} (VA (realSplit ψ₀) W)) : False := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ hW
  let iW := jbMul σs hRC h119 W
  have jW : JBWAlgebra (VA σs W) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 W
  obtain ⟨p, q, hpq, hp0, hq0, hp, hq, s, hs, hspq⟩ := JBWProj.pe_exists_exch_pair hpe hWne
  have hu : ∀ a : VA σs W, ouUnit (VA σs W) * a = a := JBAlgebra.one_mul
  have hqs : jQ s q = p := JBPeirce.exch_symm hu hs hspq
  have hqp : q * p = 0 := by rw [JBAlgebra.mul_comm]; exact hpq
  let pq : Fin 2 → VA σs W := ![p, q]
  have hpq1 : ∀ i, jm σs hRC h119 W (pq i) (pq i) = pq i := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  have hpq2 : ∀ i j, i ≠ j → jm σs hRC h119 W (pq i) (pq j) = 0 := by
    intro i j hij; fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hpq
    · exact hqp
    · exact (hij rfl).elim
  have hpq4 : ∀ i j, ∃ g : VA σs W, jm σs hRC h119 W g g = ouUnit (VA σs W) ∧
      jQA σs hRC h119 W g (pq i) = pq j := by
    have h1u : jm σs hRC h119 W (ouUnit (VA σs W)) (ouUnit (VA σs W)) = ouUnit (VA σs W) :=
      hu _
    intro i j; fin_cases i <;> fin_cases j
    · exact ⟨_, h1u, JBPeirce.jQ_unit hu p⟩
    · exact ⟨s, hs, hspq⟩
    · exact ⟨s, hs, hqs⟩
    · exact ⟨_, h1u, JBPeirce.jQ_unit hu q⟩
  -- the four products in `V_{W⊗W}`
  let iX := jbMul σs hRC h119 (W ⊗ W)
  have jX : JBWAlgebra (VA σs (W ⊗ W)) := jbw_real hRC h119 φ₀ ψ₀ h1 h2 (W ⊗ W)
  let T : Fin 2 × Fin 2 → VA σs (W ⊗ W) := fun ik => tensV σs (pq ik.1) (pq ik.2)
  choose x hx hpx using fun i => jm_idem_gmap σs hRC h119 W (hpq1 i)
  have hT2 : ∀ ik jl, ik ≠ jl → T ik * T jl = 0 := by
    intro ik jl hne
    show jm σs hRC h119 (W ⊗ W) (tensV σs (pq ik.1) (pq ik.2))
      (tensV σs (pq jl.1) (pq jl.2)) = 0
    rw [hpx ik.1, hpx ik.2, hpx jl.1, hpx jl.2, tensV_gmap, tensV_gmap]
    refine jm_zero_of_Uop hRC h119 (cptTens_idem σs h0 (hx _) (hx _)) ?_
    rw [← tensV_gmap, Uop_cptTens_apply σs h0]
    have h' : ik.1 ≠ jl.1 ∨ ik.2 ≠ jl.2 := by
      by_contra hc
      push Not at hc
      exact hne (Prod.ext hc.1 hc.2)
    rcases h' with h | h
    · have := hpq2 _ _ h
      rw [hpx, hpx] at this
      rw [Uop_zero_of_jm hRC h119 (hx _) this, tensV_zero_left]
    · have := hpq2 _ _ h
      rw [hpx, hpx] at this
      rw [Uop_zero_of_jm hRC h119 (hx _) this, tensV_zero_right]
  have hT4 : ∀ ik jl, ExchangeableBySymmetry (T ik) (T jl) := by
    intro ik jl
    obtain ⟨s₁, hs₁, e₁⟩ := hpq4 ik.1 jl.1
    obtain ⟨s₂, hs₂, e₂⟩ := hpq4 ik.2 jl.2
    have := rec134 σs hRC h119 h0 (hpq1 _) (hpq1 _) hs₁ e₁ (hpq1 _) (hpq1 _) hs₂ e₂
    exact ⟨this.1, this.2.1, tensV σs s₁ s₂, this.2.2.1, this.2.2.2⟩
  let t : Fin 4 → VA σs (W ⊗ W) := fun k => T (finProdFinEquiv.symm k)
  have ht0 : t 0 ≠ 0 := by
    show T (finProdFinEquiv.symm (0 : Fin (2 * 2))) ≠ 0
    have e0 : finProdFinEquiv.symm (0 : Fin (2 * 2)) = ((0 : Fin 2), (0 : Fin 2)) := by decide
    rw [e0]
    exact tens_ne_zero φ₀ ψ₀ h1 h2 hp0 hp0
  have R := rec127 σs hRC h119 h0 W W
  let ι : VA σs W →ₗ[ℝ] VA σs (W ⊗ W) := vtens σs (A := W) (B := W) (ouUnit (VA σs W))
  exact nofour_core hP hN hpe ι (fun a b => (R.1 a b).symm) (tensV_unit σs) t ht0
    (fun i j h => hT2 _ _ (finProdFinEquiv.symm.injective.ne h))
    (fun i j _ => hT4 _ _)

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition) from `JBWExceptionalSummand` (a corollary of
REC 52) and `ExceptionalNoFourExch` (a corollary of REC 55) only, by route (b2): no Albert
algebra, no exchangeable family summing to `1`, two tensor factors.  With scalars `[0,1]`,
every `V_A` is a JW-algebra. -/
theorem rec135_nofour (hP : JBWExceptionalSummand.{v}) (hN : ExceptionalNoFourExch.{v})
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] (A : C) :
    letI := jbMul (realSplit ψ₀) hRC h119 A; IsJWAlgebra (VA (realSplit ψ₀) A) := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  let iA := jbMul σs hRC h119 A
  rcases hP (VA σs A) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 A) with hJW | ⟨c, hc0, hcc, hcen, hvan⟩
  · exact hJW
  exfalso
  obtain ⟨W, hW, hpe, -⟩ := corner_of_summand σs hRC h119 h0 A hc0 hcc hcen hvan
  exact nofour_absurd hRC h119 φ₀ ψ₀ h1 h2 hP hN hW hpe

end Rec135NoFour

/-! ## §C. REC 136 -/

section Rec136NoFour

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

include hRC h119 in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem), statement exactly as `rec136`,
from `JBWExceptionalSummand` and `ExceptionalNoFourExch`; proof as `rec136_native`, with
`rec135_nofour` for `rec135_native`. -/
theorem rec136_nofour (hP : JBWExceptionalSummand.{v}) (hN : ExceptionalNoFourExch.{v})
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
      (jbw_real hRC h119 φ₀ ψ₀ h1 h2) (rec135_nofour hRC h119 φ₀ ψ₀ h1 h2 hP hN)

/-- **REC 136** (`rec136_hypfree`'s statement) with REC 119 and REC 121's criterion
discharged, from `JBWExceptionalSummand` (corollary of REC 52) and `ExceptionalNoFourExch`
(corollary of REC 55, `exceptionalNoFourExch_of_shultz`) only. -/
theorem rec136_nofour_hypfree (hP : JBWExceptionalSummand.{v}) (hN : ExceptionalNoFourExch.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_nofour alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds hP hN hirr h01

end Rec136NoFour

/-! ## From REC 55 -/

section FromShultz

open Papers.EJA Papers.EJA.Albert AlbNoGo JBPeirce

/-- `ExceptionalNoFourExch` from **REC 55** (Shultz 1979 Thm 3.9, `C(X, M₃(𝕆)_sa)`):
evaluate at a point `x` with `Φ(p₀)(x) ≠ 0`; evaluation is multiplicative, so the four values
are orthogonal idempotents of `M₃(𝕆)_sa`, all non-zero (`Φ(p₀)(x) = U_{Φ(s)(x)} Φ(pᵢ)(x)`),
hence of trace `≥ 1` each, while their sum is an idempotent, of trace `≤ 3`. -/
theorem exceptionalNoFourExch_of_shultz (hSh : ShultzExceptionalStructure.{v}) :
    ExceptionalNoFourExch.{v} := by
  intro V _ _ _ _ _ hV hpe p hp0 horth hex
  obtain ⟨X, iX, -, Φ, hΦ⟩ := hSh V hV hpe
  obtain ⟨x, hx⟩ : ∃ x, Φ (p 0) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hp0 0 (Φ.injective (by rw [map_zero]; ext y; exact h y))
  let a : Fin 4 → Alb := fun i => Φ (p i) x
  have hΦQ : ∀ g y : V, Φ (jQ g y) x = jQ (Φ g x) (Φ y x) := by
    intro g y
    simp only [jQ, map_sub, map_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply, hΦ]
  have hid : ∀ i, p i * p i = p i := by
    intro i
    fin_cases i
    · exact (hex 0 1 (by decide)).1
    · exact (hex 1 0 (by decide)).1
    · exact (hex 2 0 (by decide)).1
    · exact (hex 3 0 (by decide)).1
  have ha1 : ∀ i, a i * a i = a i := fun i => by
    show Φ (p i) x * Φ (p i) x = Φ (p i) x
    rw [← hΦ, hid]
  have ha2 : ∀ i j, i ≠ j → a i * a j = 0 := fun i j h => by
    show Φ (p i) x * Φ (p j) x = 0
    rw [← hΦ, horth i j h, map_zero, ContinuousMap.zero_apply]
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i hi
    by_cases h : i = 0
    · exact hx (h ▸ hi)
    · obtain ⟨-, -, g, -, hg⟩ := hex i 0 h
      have := congrArg (fun z : V => Φ z x) hg
      simp only [hΦQ] at this
      change jQ (Φ g x) (a i) = a 0 at this
      rw [hi] at this
      simp only [jQ, jmul_zero, smul_zero, sub_zero] at this
      exact hx this.symm
  have hT : ∀ i, 1 ≤ T (a i) := fun i => by
    rcases T_pos_cases (ha1 i) (ha0 i) with h | h | h <;> rw [h] <;> norm_num
  have o01 := add_idem_of_orth (ha1 0) (ha1 1) (ha2 0 1 (by decide))
  have o012 := add_idem_of_orth o01 (ha1 2) (by
    rw [jadd_mul, ha2 0 2 (by decide), ha2 1 2 (by decide), add_zero])
  have o0123 := add_idem_of_orth o012 (ha1 3) (by
    rw [jadd_mul, jadd_mul, ha2 0 3 (by decide), ha2 1 3 (by decide), ha2 2 3 (by decide),
      add_zero, add_zero])
  have hsum : T (a 0 + a 1 + a 2 + a 3) ≤ 3 := by
    rcases T_idem_cases o0123 with h | h | h | h <;> rw [h] <;> norm_num
  rw [T_add, T_add, T_add] at hsum
  linarith [hT 0, hT 1, hT 2, hT 3]

/-- **REC 136** (`rec136_hypfree`'s statement) from REC 52 and REC 55 alone, by route (b2). -/
theorem rec136_nofour_HOS_shultz {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C]
    (hHOS : HancheOlsenStormerDecomposition.{v})
    (hSh : ShultzExceptionalStructure.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_nofour_hypfree (jbwExceptionalSummand_of_HOS hHOS)
    (exceptionalNoFourExch_of_shultz hSh) hirr h01

end FromShultz

end Papers.REC

#print axioms Papers.REC.NoFour.nofour_core
#print axioms Papers.REC.rec135_nofour
#print axioms Papers.REC.rec136_nofour
#print axioms Papers.REC.rec136_nofour_hypfree
#print axioms Papers.REC.exceptionalNoFourExch_of_shultz
#print axioms Papers.REC.rec136_nofour_HOS_shultz
