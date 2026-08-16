import Theses.A.Proc.QuantumLambda

/-!
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex),
§Duplicators and Monoids (parsecs 1260–1320): every von Neumann algebra
carrying a duplicator (an npsu-map `δ : 𝒜 ⊗ 𝒜 → 𝒜` with a unit) is
nmiu-isomorphic to `ℓ^∞(X)` for some set `X` (127III), via Tomiyama's
theorem and a measure-theoretic analysis of `L^∞`-spaces; and
`ℓ^∞(nsp(𝒜))` is the free (commutative) monoid on `𝒜` in `W*_miu`
(132IV), with the `W*_cpsu` analogue (132VI).

## Encoding

* A **duplicator** (127I) is the structure `Duplicator A` (an npsu-map
  out of the chosen tensor `VNT A A` with a two-sided unit);
  `Duplicable A` is its `Nonempty`.
* `L^∞(X)` of a measure space is rendered, as in vn.tex 51IX
  (`Linfty_vn`), by a quotient map `q : (X → ℂ) → 𝒜` onto an abstract
  von Neumann algebra, packaged in the Prop `IsLinftyOf`.
* Atomic/discrete/continuous measure spaces (129II) are `AtomicSet`,
  `DiscreteSpace`, `ContinuousSpace` on a `Measure`.
* Monoids in the symmetric monoidal categories `W*_miu` / `W*_cpsu`
  (132II) are rendered concretely as `MonoidInWmiu` / `MonoidInWcpsu`
  (multiplication plus unit element, with associativity and unit laws
  stated on pure tensors); the categorical statements of 132III are
  phrased through these.
* `nsp`, `linf`, `tmapM`, `braiding` are reused from
  `QuantumLambda.lean` / `Tensor.lean`.
-/

open scoped ComplexOrder CStarAlgebra TensorProduct ENNReal
open Filter Topology MeasureTheory Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

variable {A B C : Type u}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-! ### Auxiliary: the effects span `𝒜`

Both **128VIII** and the "usual reasoning" it appeals to ("it suffices to show
that all `p ∈ [0,1]_𝒜` are central") need that the effects span `𝒜` linearly:
`a = ℜa + i·ℑa`, a self-adjoint element is `a⁺ − a⁻` (`CFC.posPart_sub_negPart`)
and a positive element is `‖a‖` times an effect. -/

section Effects

private theorem mem_span_effects (a : A) : a ∈ Submodule.span ℂ (effects A) := by
  have hpos : ∀ x : A, 0 ≤ x → x ∈ Submodule.span ℂ (effects A) := by
    intro x hx
    rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
    · have hx0 : x = 0 := by rw [← norm_eq_zero]; exact h0.symm
      rw [hx0]
      exact Submodule.zero_mem _
    · have hxle : x ≤ algebraMap ℂ A ((‖x‖ : ℝ) : ℂ) := by
        rw [← Theses.A.CStar.algebraMap_real_eq]
        exact (IsSelfAdjoint.of_nonneg hx).le_algebraMap_norm_self
      have hp : (((‖x‖⁻¹ : ℝ) : ℂ) • x) ∈ effects A := by
        refine Set.mem_Icc.mpr ⟨Theses.A.CStar.ofReal_smul_nonneg hx (by positivity), ?_⟩
        rw [← sub_nonneg]
        have hrw : (1 : A) - ((‖x‖⁻¹ : ℝ) : ℂ) • x
            = ((‖x‖⁻¹ : ℝ) : ℂ) • (algebraMap ℂ A ((‖x‖ : ℝ) : ℂ) - x) := by
          rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, ← Complex.ofReal_mul,
            inv_mul_cancel₀ h0.ne', Complex.ofReal_one, one_smul]
        rw [hrw]
        exact Theses.A.CStar.ofReal_smul_nonneg (sub_nonneg.mpr hxle) (by positivity)
      have hx' : x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0.ne', Complex.ofReal_one,
          one_smul]
      rw [hx']
      exact Submodule.smul_mem _ _ (Submodule.subset_span hp)
  have hsa : ∀ x : A, IsSelfAdjoint x → x ∈ Submodule.span ℂ (effects A) := by
    intro x hx
    rw [← CFC.posPart_sub_negPart x hx]
    exact Submodule.sub_mem _ (hpos _ (CFC.posPart_nonneg x)) (hpos _ (CFC.negPart_nonneg x))
  rw [← realPart_add_I_smul_imaginaryPart a]
  exact Submodule.add_mem _ (hsa _ (realPart a).property)
    (Submodule.smul_mem _ _ (hsa _ (imaginaryPart a).property))

/-- Induction principle: a property of elements of `𝒜` that holds on the
effects and is closed under `0`, `+` and scalars holds everywhere. -/
private theorem effects_induction {P : A → Prop} (h0 : P 0)
    (hadd : ∀ x y : A, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) (x : A), P x → P (c • x))
    (heff : ∀ p ∈ effects A, P p) (a : A) : P a := by
  have ha := mem_span_effects a
  induction ha using Submodule.span_induction with
  | mem u hu => exact heff u hu
  | zero => exact h0
  | add u v _ _ hu hv => exact hadd u v hu hv
  | smul c u _ hu => exact hsmul c u hu

end Effects

/-! ## Parsec 1270: duplicators -/

variable (A) in
/-- **127I** (`def:duplicator`, proc.tex:5854, Definition): a
**duplicator** on a von Neumann algebra `𝒜` is an npsu-map
`δ : 𝒜 ⊗ 𝒜 → 𝒜` together with a **unit** `u ∈ [0,1]_𝒜` satisfying
`δ(a ⊗ u) = a = δ(u ⊗ a)`.  (Neither associativity nor commutativity is
required.) -/
structure Duplicator [VonNeumannAlgebra A] : Type u where
  δ : VNT A A →ₚ[ℂ] A
  normal : PreservesDirSups ⇑δ
  subunital : δ 1 ≤ 1
  unit : A
  unit_mem : unit ∈ effects A
  left_unit : ∀ a : A, δ (unit ⊗ᵥ a) = a
  right_unit : ∀ a : A, δ (a ⊗ᵥ unit) = a

variable (A) in
/-- **127I** (`def:duplicator`, proc.tex:5854, Definition): a von Neumann
algebra is **duplicable** if there is a duplicator on it. -/
def Duplicable [VonNeumannAlgebra A] : Prop := Nonempty (Duplicator A)

/-- **127III** (`duplicable`, proc.tex:5881, Theorem), main equivalence: a
von Neumann algebra `𝒜` is duplicable iff it is nmiu-isomorphic to
`ℓ^∞(X)` for some set `X`. -/
theorem duplicable [VonNeumannAlgebra A] :
    Duplicable A ↔
      ∃ (X : Type u) (φ : NMIUMap A (linf X)), Function.Bijective ⇑φ :=
  sorry

/-! **127III** (`duplicable`, proc.tex:5881, Theorem), uniqueness, is
`duplicable_unique` below — it is stated after **128VIII**
`uniqueness_duplicator`, which supplies its second conjunct. -/

/-- **127VI** (`lem:unit-duplicator`, proc.tex:5925, Lemma): the unit of a
duplicator is `1`, and `δ(1 ⊗ 1) = 1`. -/
theorem unit_duplicator [VonNeumannAlgebra A] (d : Duplicator A) :
    d.unit = 1 ∧ d.δ ((1 : A) ⊗ᵥ (1 : A)) = 1 := by
  -- The thesis's proof (proc.tex:5932) verbatim.
  obtain ⟨hu0, hu1⟩ := Set.mem_Icc.mp d.unit_mem
  have hone : ((1 : A) ⊗ᵥ (1 : A)) = (1 : VNT A A) :=
    (vnTensor A A).isTensorProduct.miu.1
  -- `1 = δ(u ⊗ 1) ≤ δ(1 ⊗ 1) ≤ 1`, so `δ(1 ⊗ 1) = 1`.
  have h1 : d.δ (d.unit ⊗ᵥ (1 : A)) = 1 := d.left_unit 1
  have hmono : d.δ (d.unit ⊗ᵥ (1 : A)) ≤ d.δ ((1 : A) ⊗ᵥ (1 : A)) :=
    OrderHomClass.mono d.δ
      ((tensor_simple_facts_1 d.unit (1 : A) hu0 zero_le_one).2 1 1 hu1 le_rfl)
  have hsub : d.δ ((1 : A) ⊗ᵥ (1 : A)) ≤ 1 := by rw [hone]; exact d.subunital
  have hδ11 : d.δ ((1 : A) ⊗ᵥ (1 : A)) = 1 :=
    le_antisymm hsub (le_trans (le_of_eq h1.symm) hmono)
  -- Hence `δ(u^⊥ ⊗ 1) = 0`.
  have hbil : ((1 - d.unit) ⊗ᵥ (1 : A))
      = ((1 : A) ⊗ᵥ (1 : A)) - (d.unit ⊗ᵥ (1 : A)) := by
    show (vnTensor A A).map (1 - d.unit) 1 = _
    rw [map_sub]; rfl
  have hcompl : d.δ ((1 - d.unit) ⊗ᵥ (1 : A)) = 0 := by
    rw [hbil, map_sub, hδ11, h1, sub_self]
  -- But `u^⊥ = δ(u^⊥ ⊗ u) ≤ δ(u^⊥ ⊗ 1) = 0`, so `u^⊥ = 0`.
  have hu0' : (0 : A) ≤ 1 - d.unit := sub_nonneg.mpr hu1
  have hru : d.δ ((1 - d.unit) ⊗ᵥ d.unit) = 1 - d.unit := d.right_unit _
  have hle : d.δ ((1 - d.unit) ⊗ᵥ d.unit) ≤ d.δ ((1 - d.unit) ⊗ᵥ (1 : A)) :=
    OrderHomClass.mono d.δ
      ((tensor_simple_facts_1 (1 - d.unit) d.unit hu0' hu0).2 (1 - d.unit) 1 le_rfl hu1)
  have hle0 : (1 : A) - d.unit ≤ 0 := by rw [← hru, ← hcompl]; exact hle
  exact ⟨(sub_eq_zero.mp (le_antisymm hle0 hu0')).symm, hδ11⟩

/-! ## Parsec 1280: Tomiyama's theorem and commutativity -/

/-- **128II** (`tomiyama`, proc.tex:5948, Theorem (Tomiyama)): a linear
surjection `f : 𝒜 → ℬ` of a von Neumann algebra onto a von Neumann
subalgebra `ℬ ⊆ 𝒜` with `f ∘ f = f` and `‖f(a)‖ ≤ ‖a‖` satisfies
`b·f(a) = f(b·a)` for all `a ∈ 𝒜`, `b ∈ ℬ`. -/
theorem tomiyama [VonNeumannAlgebra A] (S : StarSubalgebra ℂ A)
    (hS : IsVNSubalgebra A S) (f : A →ₗ[ℂ] A)
    (hrange : Set.range ⇑f = (S : Set A)) (hproj : ∀ a, f (f a) = f a)
    (hnorm : ∀ a, ‖f a‖ ≤ ‖a‖) :
    ∀ b ∈ S, ∀ a : A, b * f a = f (b * a) := by
  -- `f` lands in `ℬ = S`, and fixes it pointwise (`f` is surjective onto `S`
  -- and idempotent).
  have hfS : ∀ x : A, f x ∈ S := by
    intro x
    have : f x ∈ (S : Set A) := by rw [← hrange]; exact Set.mem_range_self x
    simpa using this
  have hfix : ∀ x ∈ S, f x = x := by
    intro x hx
    have hx' : x ∈ Set.range ⇑f := by rw [hrange]; simpa using hx
    obtain ⟨y, hy⟩ := hx'
    rw [← hy, hproj]
  have hfc : Continuous ⇑f := by
    refine AddMonoidHomClass.continuous_of_bound f 1 fun x => ?_
    simpa using hnorm x
  -- **The heart of the argument**: `e^⊥ f(ea) = 0` for a projection `e ∈ ℬ`.
  have key : ∀ e : A, IsStarProjection e → e ∈ S → ∀ a : A,
      (1 - e) * f (e * a) = 0 := by
    intro e he heS a
    have hep : IsStarProjection (1 - e) := he.one_sub
    set c : A := (1 - e) * f (e * a) with hcdef
    -- `c ∈ ℬ`, hence `f(c) = c`; this is what makes the estimate close.
    have hcS : c ∈ S := by
      rw [hcdef]; exact mul_mem (sub_mem (one_mem S) heS) (hfS _)
    have hfcc : f c = c := hfix c hcS
    have hpc : (1 - e) * c = c := by
      rw [hcdef, ← mul_assoc, hep.isIdempotentElem.eq]
    have hec : e * c = 0 := by
      rw [hcdef, ← mul_assoc, mul_sub, mul_one, he.isIdempotentElem.eq, sub_self,
        zero_mul]
    have hcestar : star c * e = 0 := by
      have h0 : star (e * c) = 0 := by rw [hec, star_zero]
      rwa [star_mul, he.isSelfAdjoint.star_eq] at h0
    have hxc : star (e * a) * c = 0 := by
      rw [star_mul, he.isSelfAdjoint.star_eq, mul_assoc, hec, mul_zero]
    have hce : star c * (e * a) = 0 := by rw [← mul_assoc, hcestar, zero_mul]
    -- `(1 + 2t)‖c‖² ≤ ‖ea‖²` for every `t ≥ 0`.
    have main : ∀ t : ℝ, 0 ≤ t → (1 + 2 * t) * ‖c‖ ^ 2 ≤ ‖e * a‖ ^ 2 := by
      intro t ht
      set x : A := e * a + (t : ℂ) • c with hxdef
      have hfx : f x = f (e * a) + (t : ℂ) • c := by
        rw [hxdef, map_add, map_smul, hfcc]
      have hlhs : (1 - e) * f x = c + (t : ℂ) • c := by
        rw [hfx, mul_add, mul_smul_comm, hpc, ← hcdef]
      have e0 : c + (t : ℂ) • c = ((1 + t : ℝ) : ℂ) • c := by
        push_cast
        rw [add_smul, one_smul]
      have e1 : ‖c + (t : ℂ) • c‖ = (1 + t) * ‖c‖ := by
        rw [e0, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t)]
      have hn1 : (1 + t) * ‖c‖ ≤ ‖x‖ := by
        calc (1 + t) * ‖c‖ = ‖(1 - e) * f x‖ := by rw [hlhs, e1]
          _ ≤ ‖(1 - e : A)‖ * ‖f x‖ := norm_mul_le _ _
          _ ≤ 1 * ‖x‖ :=
              mul_le_mul (IsStarProjection.norm_le _ hep) (hnorm x)
                (norm_nonneg _) zero_le_one
          _ = ‖x‖ := one_mul _
      have hstx : star x = star (e * a) + (t : ℂ) • star c := by
        rw [hxdef, star_add, star_smul]
        simp
      have hexp : star x * x
          = star (e * a) * (e * a) + ((t : ℂ) * (t : ℂ)) • (star c * c) := by
        conv_lhs => rw [hstx, hxdef]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hxc, hce,
          smul_zero, add_zero, zero_add, smul_smul]
      have hn2 : ‖x‖ ^ 2 ≤ ‖e * a‖ ^ 2 + t ^ 2 * ‖c‖ ^ 2 := by
        have hnx : ‖x‖ ^ 2 = ‖star x * x‖ := by
          rw [CStarRing.norm_star_mul_self]; ring
        rw [hnx, hexp]
        calc ‖star (e * a) * (e * a) + ((t : ℂ) * (t : ℂ)) • (star c * c)‖
            ≤ ‖star (e * a) * (e * a)‖ + ‖((t : ℂ) * (t : ℂ)) • (star c * c)‖ :=
              norm_add_le _ _
          _ = ‖e * a‖ ^ 2 + t ^ 2 * ‖c‖ ^ 2 := by
              rw [CStarRing.norm_star_mul_self, norm_smul,
                CStarRing.norm_star_mul_self]
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              rw [abs_mul_abs_self]
              ring
      have hsq : ((1 + t) * ‖c‖) ^ 2 ≤ ‖x‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hn1 2
      nlinarith [hsq, hn2]
    -- letting `t → ∞` forces `c = 0`
    by_contra hne
    have hcpos : (0:ℝ) < ‖c‖ ^ 2 := by
      have : 0 < ‖c‖ := norm_pos_iff.mpr hne
      positivity
    have h := main (‖e * a‖ ^ 2 / ‖c‖ ^ 2) (by positivity)
    have hkey : ‖c‖ ^ 2 + 2 * ‖e * a‖ ^ 2 ≤ ‖e * a‖ ^ 2 := by
      calc ‖c‖ ^ 2 + 2 * ‖e * a‖ ^ 2
          = (1 + 2 * (‖e * a‖ ^ 2 / ‖c‖ ^ 2)) * ‖c‖ ^ 2 := by
            field_simp
        _ ≤ ‖e * a‖ ^ 2 := h
    nlinarith [hcpos, sq_nonneg ‖e * a‖]
  -- the set of `b` intertwining `f` is a norm-closed `ℂ`-subspace …
  set V : Submodule ℂ A :=
    { carrier := {b : A | ∀ a : A, b * f a = f (b * a)}
      add_mem' := by
        intro x y hx hy a
        rw [add_mul, hx a, hy a, ← map_add, ← add_mul]
      zero_mem' := by intro a; simp
      smul_mem' := by
        intro r x hx a
        rw [smul_mul_assoc, hx a, ← map_smul, smul_mul_assoc] } with hVdef
  have hVclosed : IsClosed (V : Set A) := by
    have hV : (V : Set A) = ⋂ a : A, {b : A | b * f a = f (b * a)} := by
      ext b; simp [hVdef, Set.mem_iInter]
    rw [hV]
    refine isClosed_iInter fun a => ?_
    exact isClosed_eq (continuous_id.mul continuous_const)
      (hfc.comp (continuous_id.mul continuous_const))
  -- … containing every projection of `ℬ`, by `key` applied to `e` and `e^⊥`.
  have hprojV : ∀ p : A, IsStarProjection p → p ∈ S → p ∈ V := by
    intro e he heS
    show ∀ a : A, e * f a = f (e * a)
    intro a
    have h1 := key e he heS a
    have h2 := key (1 - e) he.one_sub (sub_mem (one_mem S) heS) a
    rw [sub_sub_cancel] at h2
    have h3 : f (e * a) = e * f (e * a) := by
      have := h1
      rw [sub_mul, one_mul, sub_eq_zero] at this
      exact this
    have ha : e * a + (1 - e) * a = a := by rw [sub_mul, one_mul]; abel
    calc e * f a = e * f (e * a + (1 - e) * a) := by rw [ha]
      _ = e * f (e * a) + e * f ((1 - e) * a) := by rw [map_add, mul_add]
      _ = e * f (e * a) := by rw [h2, add_zero]
      _ = f (e * a) := h3.symm
  -- 65IV relativised to `ℬ` finishes the proof.
  intro b hb a
  exact mem_of_isClosed_of_projections_subalgebra hS V hVclosed hprojV hb a

/- **128IV–V** (proc.tex:6011): moved/removed points — nothing to
convert. -/

section Pairs

variable [Nontrivial A]

/-- The element `(a, b)` of the direct sum `𝒜 ⊕ 𝒜 = lp (Fin 2 → 𝒜) ∞`
(helper for 128VI). -/
noncomputable def pairLp (a b : A) : lp (fun _ : Fin 2 => A) ∞ :=
  lp.single ∞ 0 a + lp.single ∞ 1 b

/-! Auxiliary for **128VI**: the elementary algebra of `pairLp`, the
diagonal `{(a,a)} ⊆ 𝒜 ⊕ 𝒜` as a von Neumann subalgebra, and the fact that
`x ↦ (f x, f x)` is the norm-one idempotent onto it that Tomiyama's theorem
(**128II**) applies to. -/

section PairAux

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem pairLp_apply (a b : A) (i : Fin 2) :
    ((pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) : ∀ _ : Fin 2, A) i = if i = 0 then a else b := by
  rw [pairLp, lp.coeFn_add]
  simp only [lp.coeFn_single, Pi.add_apply, Pi.single_apply]
  fin_cases i <;> simp

theorem pairLp_apply_zero (a b : A) :
    ((pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) : ∀ _ : Fin 2, A) 0 = a := by simp [pairLp_apply]

theorem pairLp_apply_one (a b : A) :
    ((pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) : ∀ _ : Fin 2, A) 1 = b := by simp [pairLp_apply]

theorem pairLp_eta (x : (lp (fun _ : Fin 2 => A) ∞)) :
    pairLp ((x : ∀ _ : Fin 2, A) 0) ((x : ∀ _ : Fin 2, A) 1) = x := by
  apply lp.ext
  funext i
  rw [pairLp_apply]
  fin_cases i <;> simp

theorem pairLp_mul (a b c d : A) :
    (pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) * pairLp c d = pairLp (a * c) (b * d) := by
  apply lp.ext
  funext i
  rw [lp.infty_coeFn_mul]
  simp only [Pi.mul_apply, pairLp_apply]
  split <;> rfl

theorem pairLp_add (a b c d : A) :
    (pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) + pairLp c d = pairLp (a + c) (b + d) := by
  apply lp.ext
  funext i
  rw [lp.coeFn_add]
  simp only [Pi.add_apply, pairLp_apply]
  split <;> rfl

theorem pairLp_star (a b : A) :
    star (pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) = pairLp (star a) (star b) := by
  apply lp.ext
  funext i
  rw [lp.coeFn_star]
  simp only [Pi.star_apply, pairLp_apply]
  split <;> rfl

end PairAux

omit [PartialOrder A] [StarOrderedRing A] in
theorem pairLp_one : (pairLp (1 : A) 1 : (lp (fun _ : Fin 2 => A) ∞)) = 1 := by
  apply lp.ext
  funext i
  rw [lp.infty_coeFn_one, pairLp_apply]
  split <;> rfl

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
theorem norm_pairLp_le (c : A) : ‖(pairLp c c : (lp (fun _ : Fin 2 => A) ∞))‖ ≤ ‖c‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg c) fun i => ?_
  rw [pairLp_apply]
  split <;> exact le_rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem pairLp_smul (c : ℂ) (a b : A) :
    c • (pairLp a b : (lp (fun _ : Fin 2 => A) ∞)) = pairLp (c • a) (c • b) := by
  apply lp.ext
  funext i
  rw [lp.coeFn_smul]
  simp only [Pi.smul_apply, pairLp_apply]
  split <;> rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem continuous_lpEval2 (i : Fin 2) :
    Continuous fun x : (lp (fun _ : Fin 2 => A) ∞) => (x : ∀ _ : Fin 2, A) i := by
  have := AddMonoidHomClass.continuous_of_bound
    (lpEvalSAH (𝒜 := fun _ : Fin 2 => A) i) 1 (fun x => by
      simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero x i)
  exact this

/-- The diagonal `{(a,a)} ⊆ 𝒜 ⊕ 𝒜`. -/
def diagSub : StarSubalgebra ℂ (lp (fun _ : Fin 2 => A) ∞) :=
  StarAlgHom.equalizer (lpEvalSAH (𝒜 := fun _ : Fin 2 => A) 0)
    (lpEvalSAH (𝒜 := fun _ : Fin 2 => A) 1)

omit [PartialOrder A] [StarOrderedRing A] in
theorem mem_diagSub (x : (lp (fun _ : Fin 2 => A) ∞)) :
    x ∈ (diagSub : StarSubalgebra ℂ (lp (fun _ : Fin 2 => A) ∞)) ↔
      (x : ∀ _ : Fin 2, A) 0 = (x : ∀ _ : Fin 2, A) 1 := Iff.rfl

theorem isVNSubalgebra_diagSub [VonNeumannAlgebra A] :
    IsVNSubalgebra (lp (fun _ : Fin 2 => A) ∞) (diagSub (A := A)) := by
  constructor
  · have h : ((diagSub (A := A) : StarSubalgebra ℂ (lp (fun _ : Fin 2 => A) ∞)) : Set (lp (fun _ : Fin 2 => A) ∞))
        = {x : (lp (fun _ : Fin 2 => A) ∞) | (x : ∀ _ : Fin 2, A) 0 = (x : ∀ _ : Fin 2, A) 1} :=
      Set.ext fun x => Iff.rfl
    rw [h]
    exact isClosed_eq (continuous_lpEval2 0) (continuous_lpEval2 1)
  · intro D s hDS hne hdir hlub
    obtain ⟨s', hs', hev⟩ := lp_infty_exists_isLUB D hne hdir ⟨s, hlub.1⟩
    obtain rfl := hlub.unique hs'
    rw [mem_diagSub]
    have himg : lpEvalSA (𝒜 := fun _ : Fin 2 => A) 0 '' D
        = lpEvalSA (𝒜 := fun _ : Fin 2 => A) 1 '' D := by
      ext y
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, Subtype.ext (hDS d hd).symm⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, Subtype.ext (hDS d hd)⟩
    have := (hev 0).unique (himg ▸ hev 1)
    exact congrArg Subtype.val this

/-- **128VI** (`lem:sef-instrument`, proc.tex:6015, Lemma): for a pu-map
`f : 𝒜 ⊕ 𝒜 → 𝒜` with `f(a,a) = a`, the element `p := f(1,0)` is
central and `f(a,b) = a·p + b·p^⊥`. -/
theorem sef_instrument [VonNeumannAlgebra A]
    (f : lp (fun _ : Fin 2 => A) ∞ →ₗ[ℂ] A)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hu : f 1 = 1)
    (hdiag : ∀ a : A, f (pairLp a a) = a) :
    f (pairLp 1 0) ∈ centre A ∧
      ∀ a b : A, f (pairLp a b) =
        a * f (pairLp 1 0) + b * (1 - f (pairLp 1 0)) := by
  have hposmap : Theses.A.CStar.IsPositiveMap f := hpos
  have hinv := Theses.A.CStar.cstar_p_implies_i f hposmap
  set f' : (lp (fun _ : Fin 2 => A) ∞) →ₗ[ℂ] (lp (fun _ : Fin 2 => A) ∞) :=
    { toFun := fun x => pairLp (f x) (f x)
      map_add' := fun x y => by rw [map_add, ← pairLp_add]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, pairLp_smul] } with hf'def
  have hf'app : ∀ x : (lp (fun _ : Fin 2 => A) ∞), f' x = pairLp (f x) (f x) := fun _ => rfl
  have hrange : Set.range ⇑f' = ((diagSub (A := A) : StarSubalgebra ℂ (lp (fun _ : Fin 2 => A) ∞)) : Set (lp (fun _ : Fin 2 => A) ∞)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [SetLike.mem_coe, mem_diagSub, hf'app, pairLp_apply_zero, pairLp_apply_one]
    · intro hy
      rw [SetLike.mem_coe, mem_diagSub] at hy
      refine ⟨y, ?_⟩
      have hfy : f y = (y : ∀ _ : Fin 2, A) 0 := by
        conv_lhs => rw [← pairLp_eta y, ← hy]
        exact hdiag _
      have hyy : (pairLp ((y : ∀ _ : Fin 2, A) 0) ((y : ∀ _ : Fin 2, A) 0) : (lp (fun _ : Fin 2 => A) ∞)) = y := by
        conv_rhs => rw [← pairLp_eta y]
        rw [hy]
      rw [hf'app, hfy, hyy]
  have hproj : ∀ x : (lp (fun _ : Fin 2 => A) ∞), f' (f' x) = f' x := by
    intro x
    rw [hf'app, hf'app, hdiag]
  have hnorm : ∀ x : (lp (fun _ : Fin 2 => A) ∞), ‖f' x‖ ≤ ‖x‖ := by
    intro x
    refine (norm_pairLp_le (f x)).trans ?_
    have h := Theses.A.CStar.russo_dye_cor f hposmap x
    rwa [hu, norm_one, one_mul] at h
  have htom := tomiyama (diagSub (A := A)) isVNSubalgebra_diagSub f' hrange hproj hnorm
  -- the thesis's `a f(c,d) = f(ac, ad)`
  have hleft : ∀ a c d : A, a * f (pairLp c d) = f (pairLp (a * c) (a * d)) := by
    intro a c d
    have hmem : (pairLp a a : (lp (fun _ : Fin 2 => A) ∞)) ∈ (diagSub (A := A) : StarSubalgebra ℂ (lp (fun _ : Fin 2 => A) ∞)) := by
      rw [mem_diagSub, pairLp_apply_zero, pairLp_apply_one]
    have h := htom _ hmem (pairLp c d)
    rw [hf'app, pairLp_mul, pairLp_mul, hf'app] at h
    have h0 := congrArg (fun z : (lp (fun _ : Fin 2 => A) ∞) => (z : ∀ _ : Fin 2, A) 0) h
    simpa only [pairLp_apply_zero] using h0
  have hright : ∀ b c d : A, f (pairLp c d) * b = f (pairLp (c * b) (d * b)) := by
    intro b c d
    have h := hleft (star b) (star c) (star d)
    have h2 := congrArg star h
    rw [star_mul, star_star, ← hinv, ← hinv, pairLp_star, pairLp_star, star_star,
      star_star, star_mul, star_mul, star_star, star_star, star_star] at h2
    exact h2
  refine ⟨?_, ?_⟩
  · intro a _
    have h1 := hleft a 1 0
    have h2 := hright a 1 0
    rw [mul_one, mul_zero] at h1
    rw [one_mul, zero_mul] at h2
    rw [h2, ← h1]
  · intro a b
    have hq : f (pairLp 0 1) = 1 - f (pairLp 1 0) := by
      have hsum : (pairLp (1 : A) 0 : (lp (fun _ : Fin 2 => A) ∞)) + pairLp 0 1 = pairLp 1 1 := by
        rw [pairLp_add, add_zero, zero_add]
      have := congrArg f hsum
      rw [map_add, hdiag] at this
      linear_combination (norm := abel1) this
    have h1 : a * f (pairLp 1 0) = f (pairLp a 0) := by
      have := hleft a 1 0
      rwa [mul_one, mul_zero] at this
    have h2 : b * (1 - f (pairLp 1 0)) = f (pairLp 0 b) := by
      rw [← hq]
      have := hleft b 0 1
      rwa [mul_zero, mul_one] at this
    rw [h1, h2, ← map_add, pairLp_add, add_zero, zero_add]

end Pairs

/-- **128VIII** (`lem:uniqueness-duplicator`, proc.tex:6059, Lemma): a
von Neumann algebra with a duplicator `δ` is commutative, and
`δ(a ⊗ b) = a·b`. -/
theorem uniqueness_duplicator [VonNeumannAlgebra A] (d : Duplicator A) :
    (∀ a b : A, a * b = b * a) ∧ ∀ a b : A, d.δ (a ⊗ᵥ b) = a * b := by
  -- The thesis's proof (proc.tex:6067) verbatim, through **128VI**
  -- `sef_instrument`.  (`sef_instrument` needs `Nontrivial`; the trivial
  -- algebra is handled separately.)
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · haveI := hsub
    exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  haveI := hnt
  have hunit : d.unit = 1 := (unit_duplicator d).1
  have hleft : ∀ a : A, d.δ ((1 : A) ⊗ᵥ a) = a := fun a => by
    rw [← hunit]; exact d.left_unit a
  have hright : ∀ a : A, d.δ (a ⊗ᵥ (1 : A)) = a := fun a => by
    rw [← hunit]; exact d.right_unit a
  have hzeroL : ∀ b : A, ((0 : A) ⊗ᵥ b) = 0 := by
    intro b
    show (vnTensor A A).map 0 b = 0
    rw [map_zero]; rfl
  -- For each effect `p`, apply **128VI** to `f(a,b) := δ(a ⊗ p + b ⊗ p^⊥)`.
  have key : ∀ p ∈ effects A,
      (∀ m : A, m * p = p * m) ∧ ∀ a : A, d.δ (a ⊗ᵥ p) = a * p := by
    intro p hp
    obtain ⟨hp0, hp1⟩ := Set.mem_Icc.mp hp
    have hp0' : (0 : A) ≤ 1 - p := sub_nonneg.mpr hp1
    set L : lp (fun _ : Fin 2 => A) ∞ →ₗ[ℂ] VNT A A :=
      (LinearMap.flip (vnTensor A A).map p).comp (lpEvalₗ (fun _ : Fin 2 => A) 0) +
        (LinearMap.flip (vnTensor A A).map (1 - p)).comp
          (lpEvalₗ (fun _ : Fin 2 => A) 1) with hLdef
    set f : lp (fun _ : Fin 2 => A) ∞ →ₗ[ℂ] A := d.δ.toLinearMap.comp L with hfdef
    have hfapp : ∀ x : lp (fun _ : Fin 2 => A) ∞,
        f x = d.δ (((x : ∀ _ : Fin 2, A) 0) ⊗ᵥ p +
          ((x : ∀ _ : Fin 2, A) 1) ⊗ᵥ (1 - p)) := fun _ => rfl
    have hfpair : ∀ a b : A, f (pairLp a b) = d.δ (a ⊗ᵥ p + b ⊗ᵥ (1 - p)) := by
      intro a b
      rw [hfapp, pairLp_apply_zero, pairLp_apply_one]
    -- `a ⊗ p + a ⊗ p^⊥ = a ⊗ 1`
    have hbil : ∀ a : A, (a ⊗ᵥ p) + (a ⊗ᵥ (1 - p)) = a ⊗ᵥ (1 : A) := by
      intro a
      show (vnTensor A A).map a p + (vnTensor A A).map a (1 - p)
        = (vnTensor A A).map a 1
      rw [← map_add]
      congr 1
      abel
    have hpos : ∀ x : lp (fun _ : Fin 2 => A) ∞, 0 ≤ x → 0 ≤ f x := by
      intro x hx
      rw [hfapp]
      exact d.δ.map_nonneg (add_nonneg
        (vtmul_nonneg _ _ ((lp_infty_nonneg_iff x).mp hx 0) hp0)
        (vtmul_nonneg _ _ ((lp_infty_nonneg_iff x).mp hx 1) hp0'))
    have hu : f 1 = 1 := by
      have h0 : ((1 : lp (fun _ : Fin 2 => A) ∞) : ∀ _ : Fin 2, A) 0 = 1 := by
        rw [lp.infty_coeFn_one]; rfl
      have h1 : ((1 : lp (fun _ : Fin 2 => A) ∞) : ∀ _ : Fin 2, A) 1 = 1 := by
        rw [lp.infty_coeFn_one]; rfl
      rw [hfapp, h0, h1, hbil]
      exact hright 1
    have hdiag : ∀ a : A, f (pairLp a a) = a := by
      intro a; rw [hfpair, hbil]; exact hright a
    have hf10 : f (pairLp (1 : A) 0) = p := by
      rw [hfpair, hzeroL, add_zero]; exact hleft p
    obtain ⟨hcentre, hform⟩ := sef_instrument f hpos hu hdiag
    rw [hf10] at hcentre hform
    refine ⟨fun m => hcentre m (Set.mem_univ m), fun a => ?_⟩
    have h := hform a 0
    rw [hfpair, hzeroL, add_zero, zero_mul, add_zero] at h
    exact h
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · -- commutativity: both sides are linear in `b` and agree on the effects
    refine effects_induction (P := fun b => a * b = b * a) (by simp) ?_ ?_ ?_ b
    · intro x y hx hy; rw [mul_add, hx, hy, add_mul]
    · intro c x hx; rw [mul_smul_comm, hx, smul_mul_assoc]
    · intro q hq; exact (key q hq).1 a
  · -- `δ(a ⊗ b) = a·b`: likewise linear in `b`
    refine effects_induction (P := fun b => d.δ (a ⊗ᵥ b) = a * b) ?_ ?_ ?_ ?_ b
    · have hz : (a ⊗ᵥ (0 : A)) = 0 := by
        show (vnTensor A A).map a 0 = 0
        rw [map_zero]
      rw [hz, map_zero, mul_zero]
    · intro x y hx hy
      have ha : (a ⊗ᵥ (x + y)) = (a ⊗ᵥ x) + (a ⊗ᵥ y) := by
        show (vnTensor A A).map a (x + y) = _
        rw [map_add]; rfl
      rw [ha, map_add, hx, hy, mul_add]
    · intro c x hx
      have hs : (a ⊗ᵥ (c • x)) = c • (a ⊗ᵥ x) := by
        show (vnTensor A A).map a (c • x) = _
        rw [map_smul]; rfl
      rw [hs, map_smul, hx, mul_smul_comm]
    · intro q hq; exact (key q hq).2 a

/-- **127III** (`duplicable`, proc.tex:5881, Theorem), uniqueness: in that
case the duplicator is unique, given by `δ(a ⊗ b) = a·b` and `u = 1`.
(Stated here rather than at parsec 1270 because its second conjunct is
**128VIII**.) -/
theorem duplicable_unique [VonNeumannAlgebra A] (d : Duplicator A) :
    d.unit = 1 ∧ ∀ a b : A, d.δ (a ⊗ᵥ b) = a * b :=
  ⟨(unit_duplicator d).1, (uniqueness_duplicator d).2⟩

/-- **128XI** (`cor:duplicability-multiplication`, proc.tex:6109,
Corollary): `𝒜` is duplicable iff there is an np-map
`δ : 𝒜 ⊗ 𝒜 → 𝒜` with `δ(a ⊗ b) = a·b` (and in that case `𝒜` is
commutative). -/
theorem duplicability_multiplication [VonNeumannAlgebra A] :
    (Duplicable A ↔
      ∃ δ : VNT A A →ₚ[ℂ] A, PreservesDirSups ⇑δ ∧
        ∀ a b : A, δ (a ⊗ᵥ b) = a * b) ∧
    (Duplicable A → ∀ a b : A, a * b = b * a) := by
  have hone : ((1 : A) ⊗ᵥ (1 : A)) = (1 : VNT A A) :=
    (vnTensor A A).isTensorProduct.miu.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- a duplicator is multiplication, by **128VIII**
    rintro ⟨d⟩
    exact ⟨d.δ, d.normal, (uniqueness_duplicator d).2⟩
  · -- conversely, multiplication is a duplicator with unit `1`
    rintro ⟨δ, hnormal, hmul⟩
    have hδone : δ (1 : VNT A A) = 1 := by rw [← hone, hmul, one_mul]
    exact ⟨{ δ := δ
             normal := hnormal
             subunital := hδone.le
             unit := 1
             unit_mem := Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
             left_unit := fun a => by rw [hmul, one_mul]
             right_unit := fun a => by rw [hmul, mul_one] }⟩
  · rintro ⟨d⟩
    exact (uniqueness_duplicator d).1

/-- **128XIII** (`cor:duplicable-product`, proc.tex:6128, Corollary): when
a direct sum of von Neumann algebras is duplicable, so is each summand.
(Stated for an arbitrary family; the thesis states the binary case
`𝒜 ⊕ ℬ`.) -/
theorem duplicable_product {I : Type u} (𝒜 : I → Type u)
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] (h : Duplicable (lp 𝒜 ∞)) (i : I) :
    Duplicable (𝒜 i) := sorry

/-! ## Parsec 1290: measure-theoretic interlude -/

section MeasureTheory

variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

/-- **129II** (proc.tex:6188, Definition), part 1: a measurable subset `S`
of a finite complete measure space is **atomic** if `0 < μ(S)` and every
measurable `S' ⊆ S` of positive measure has `μ(S') = μ(S)`. -/
def AtomicSet (S : Set X) : Prop :=
  MeasurableSet S ∧ 0 < μ S ∧
    ∀ S' ⊆ S, MeasurableSet S' → 0 < μ S' → μ S' = μ S

/-- **129II** (proc.tex:6188, Definition), part 2: `X` is **discrete** if
it is covered by atomic measurable subsets. -/
def DiscreteSpace : Prop :=
  ∃ 𝒞 : Set (Set X), (∀ S ∈ 𝒞, AtomicSet μ S) ∧ Set.univ ⊆ ⋃₀ 𝒞

/-- **129II** (proc.tex:6188, Definition), part 3: `X` is **continuous**
(atomless) if it contains no atomic subsets. -/
def ContinuousSpace : Prop := ∀ S : Set X, ¬ AtomicSet μ S

/-- **129IV** (`lem:measure-zorn`, proc.tex:6221, Lemma; a choice-free
variant of Zorn's lemma): if a collection `𝒮` of measurable subsets of a
finite complete measure space is closed under countable ascending chains,
then every `A ∈ 𝒮` is contained in a `B ∈ 𝒮` that is maximal in the
sense that `μ(B') = μ(B)` for every `B' ∈ 𝒮` containing `B`.

Note that neither the completeness of `μ` nor the measurability of the
members of `𝒮` is used (the unused-variable warnings on `hμ` and `hmeas`
are left in place as the evidence): the lemma holds for an arbitrary
collection of subsets of a finite measure space, `μ` being an outer
measure on all of them.  Only `IsFiniteMeasure` is needed, for
`β_C ≤ μ(X) < ∞`. -/
theorem measure_zorn [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (𝒮 : Set (Set X)) (hmeas : ∀ S ∈ 𝒮, MeasurableSet S)
    (hchain : ∀ f : ℕ → Set X, (∀ n, f n ∈ 𝒮) → Monotone f →
      ∃ S ∈ 𝒮, ∀ n, f n ⊆ S) :
    ∀ S ∈ 𝒮, ∃ T ∈ 𝒮, S ⊆ T ∧ ∀ T' ∈ 𝒮, T ⊆ T' → μ T' = μ T := by
  intro A hA
  set β : Set X → ℝ≥0∞ := fun C => ⨆ D ∈ {D | D ∈ 𝒮 ∧ C ⊆ D}, μ D with hβ
  have hβle : ∀ C, β C ≤ μ Set.univ := fun C =>
    iSup₂_le fun D _ => measure_mono (Set.subset_univ D)
  have hβtop : ∀ C, β C ≠ ⊤ := fun C =>
    ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (hβle C)
  have hβmono : ∀ C₁ C₂ : Set X, C₁ ⊆ C₂ → β C₂ ≤ β C₁ := by
    intro C₁ C₂ h
    refine iSup₂_le fun D hD => ?_
    exact le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ 𝒮 ∧ C₁ ⊆ D}) => μ D) D
      ⟨hD.1, h.trans hD.2⟩
  have hself : ∀ C ∈ 𝒮, μ C ≤ β C := fun C hC =>
    le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ 𝒮 ∧ C ⊆ D}) => μ D) C ⟨hC, subset_rfl⟩
  -- the approximation step
  have hstep : ∀ C : Set X, C ∈ 𝒮 → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ D, D ∈ 𝒮 ∧ C ⊆ D ∧ β C ≤ μ D + ε := by
    intro C hC ε hε
    rcases eq_or_ne (β C) 0 with h0 | h0
    · exact ⟨C, hC, subset_rfl, by simp [h0]⟩
    have hlt : β C - ε < β C := ENNReal.sub_lt_self (hβtop C) h0 hε.ne'
    rw [hβ] at hlt
    obtain ⟨D, hD⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hDmem, hDlt⟩ := lt_iSup_iff.mp hD
    exact ⟨D, hDmem.1, hDmem.2, tsub_le_iff_right.mp hDlt.le⟩
  choose! Dfun hD𝒮 hDsub hDβ using hstep
  -- the sequence `B₁ = A ⊆ B₂ ⊆ ⋯`
  set B : ℕ → Set X := fun n =>
    Nat.rec A (fun k b => Dfun b ((k : ℝ≥0∞) + 1)⁻¹) n with hBdef
  have hB0 : B 0 = A := rfl
  have hBsucc : ∀ n, B (n + 1) = Dfun (B n) ((n : ℝ≥0∞) + 1)⁻¹ := fun n => rfl
  have hεpos : ∀ n : ℕ, (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    simp [ENNReal.inv_pos]
  have hB𝒮 : ∀ n, B n ∈ 𝒮 := by
    intro n
    induction n with
    | zero => exact hA
    | succ k ih => rw [hBsucc k]; exact hD𝒮 _ ih _ (hεpos k)
  have hBmono : Monotone B := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [hBsucc n]
    exact hDsub _ (hB𝒮 n) _ (hεpos n)
  obtain ⟨T, hT𝒮, hTsub⟩ := hchain B hB𝒮 hBmono
  have hkey : ∀ n : ℕ, β T ≤ μ T + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    calc β T ≤ β (B n) := hβmono _ _ (hTsub n)
      _ ≤ μ (B (n + 1)) + ((n : ℝ≥0∞) + 1)⁻¹ := by
          have h := hDβ (B n) (hB𝒮 n) _ (hεpos n)
          rwa [← hBsucc n] at h
      _ ≤ μ T + ((n : ℝ≥0∞) + 1)⁻¹ :=
          add_le_add (measure_mono (hTsub (n + 1))) le_rfl
  have hβT : β T ≤ μ T := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt
      (show ((ε : ℝ≥0∞)) ≠ 0 by simpa using hε.ne')
    refine (hkey n).trans (add_le_add le_rfl ?_)
    exact le_trans (ENNReal.inv_le_inv.mpr le_self_add) hn.le
  refine ⟨T, hT𝒮, hB0 ▸ hTsub 0, fun T' hT' hTT' => ?_⟩
  refine le_antisymm ?_ (measure_mono hTT')
  exact le_trans (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ 𝒮 ∧ T ⊆ D}) => μ D) T'
    ⟨hT', hTT'⟩) hβT

/-- **129VI** (`lem:measure-space-continuous-discrete`, proc.tex:6279,
Lemma): each finite complete measure space contains a discrete measurable
subset `D` such that `X ∖ D` is continuous. -/
theorem measure_space_continuous_discrete [IsFiniteMeasure μ]
    (hμ : μ.IsComplete) :
    ∃ D : Set X, MeasurableSet D ∧
      (∃ 𝒞 : Set (Set X), (∀ S ∈ 𝒞, AtomicSet μ S) ∧ D ⊆ ⋃₀ 𝒞) ∧
      ∀ S : Set X, S ⊆ Set.univ \ D → ¬ AtomicSet μ S := by
  set 𝒮 : Set (Set X) :=
    {S | MeasurableSet S ∧ ∃ 𝒞 : Set (Set X),
      (∀ T ∈ 𝒞, AtomicSet μ T) ∧ S ⊆ ⋃₀ 𝒞} with h𝒮
  have hempty : (∅ : Set X) ∈ 𝒮 :=
    ⟨MeasurableSet.empty, ∅, fun T hT => absurd hT (Set.notMem_empty T),
      Set.empty_subset _⟩
  have hchain : ∀ f : ℕ → Set X, (∀ n, f n ∈ 𝒮) → Monotone f →
      ∃ S ∈ 𝒮, ∀ n, f n ⊆ S := by
    intro f hf _
    refine ⟨⋃ n, f n, ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩,
      fun n => Set.subset_iUnion f n⟩
    refine ⟨⋃ n, (hf n).2.choose, ?_, ?_⟩
    · rintro T hT
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hT
      exact (hf n).2.choose_spec.1 T hn
    · rintro x hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨T, hT, hxT⟩ := (hf n).2.choose_spec.2 hn
      exact ⟨T, Set.mem_iUnion.mpr ⟨n, hT⟩, hxT⟩
  obtain ⟨D, hD𝒮, -, hDmax⟩ :=
    measure_zorn μ hμ 𝒮 (fun S hS => hS.1) hchain ∅ hempty
  refine ⟨D, hD𝒮.1, hD𝒮.2, fun S hS hSat => ?_⟩
  have hunion : D ∪ S ∈ 𝒮 := by
    obtain ⟨𝒞, h𝒞, hD𝒞⟩ := hD𝒮.2
    exact ⟨hD𝒮.1.union hSat.1, insert S 𝒞,
      fun T hT => by rcases hT with rfl | hT; exacts [hSat, h𝒞 T hT],
      Set.union_subset (hD𝒞.trans (Set.sUnion_subset_sUnion (Set.subset_insert _ _)))
        fun x hx => ⟨S, Set.mem_insert _ _, hx⟩⟩
  have hdisj : Disjoint D S := Set.disjoint_left.mpr fun x hxD hxS => (hS hxS).2 hxD
  have hadd : μ (D ∪ S) = μ D + μ S := measure_union hdisj hSat.1
  have heq : μ (D ∪ S) = μ D := hDmax _ hunion Set.subset_union_left
  rw [hadd] at heq
  have : μ S = 0 := by
    have h := measure_ne_top μ D
    exact (ENNReal.add_right_inj h).mp (by rw [heq, add_zero])
  exact absurd hSat.2.1 (by rw [this]; exact lt_irrefl 0)

/-- **129VIII** (`lem:continuous-measure-space`, proc.tex:6305, Lemma):
for a continuous finite complete measure space `X` and
`r ∈ [0, μ(X)]` there is a measurable `A ⊆ X` with `μ(A) = r`. -/
theorem continuous_measure_space [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hc : ContinuousSpace μ) (r : ℝ≥0∞) (hr : r ≤ μ Set.univ) :
    ∃ S : Set X, MeasurableSet S ∧ μ S = r := by
  have hhalf : ∀ B : Set X, MeasurableSet B → 0 < μ B →
      ∃ C : Set X, C ⊆ B ∧ MeasurableSet C ∧ 0 < μ C ∧ 2 * μ C ≤ μ B := by
    intro B hB hBpos
    have hnot := hc B
    rw [AtomicSet] at hnot
    push_neg at hnot
    obtain ⟨S, hSB, hSm, hSpos, hSne⟩ := hnot hB hBpos
    have hsplit : μ S + μ (B \ S) = μ B := by
      rw [measure_add_sdiff hSm.nullMeasurableSet B, Set.union_eq_self_of_subset_left hSB]
    have hdpos : 0 < μ (B \ S) := by
      rcases eq_zero_or_pos (μ (B \ S)) with h | h
      · rw [h, add_zero] at hsplit; exact absurd hsplit hSne
      · exact h
    rcases le_total (2 * μ S) (μ B) with h | h
    · exact ⟨S, hSB, hSm, hSpos, h⟩
    · refine ⟨B \ S, Set.diff_subset, hB.diff hSm, hdpos, ?_⟩
      have h2 : μ (B \ S) ≤ μ S := by
        have h3 : μ S + μ (B \ S) ≤ μ S + μ S := by
          rw [hsplit, ← two_mul]; exact h
        exact (ENNReal.add_le_add_iff_left (measure_ne_top μ S)).mp h3
      calc 2 * μ (B \ S) = μ (B \ S) + μ (B \ S) := two_mul _
        _ ≤ μ S + μ (B \ S) := by gcongr
        _ = μ B := hsplit
  have hsmall : ∀ B : Set X, MeasurableSet B → 0 < μ B →
      ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ C : Set X, C ⊆ B ∧ MeasurableSet C ∧ 0 < μ C ∧ μ C ≤ ε := by
    intro B hB hBpos ε hε
    choose! Cfun hCsub hCm hCpos hChalf using hhalf
    set F : ℕ → Set X := fun n => Nat.rec B (fun _ b => Cfun b) n with hF
    have hFm : ∀ n, MeasurableSet (F n) ∧ 0 < μ (F n) ∧ F n ⊆ B := by
      intro n
      induction n with
      | zero => exact ⟨hB, hBpos, subset_rfl⟩
      | succ k ih =>
          exact ⟨hCm _ ih.1 ih.2.1, hCpos _ ih.1 ih.2.1,
            (hCsub _ ih.1 ih.2.1).trans ih.2.2⟩
    have hFdec : ∀ n, 2 ^ n * μ (F n) ≤ μ B := by
      intro n
      induction n with
      | zero => simp [hF]
      | succ k ih =>
          have h := hChalf (F k) (hFm k).1 (hFm k).2.1
          calc 2 ^ (k + 1) * μ (F (k + 1)) = 2 ^ k * (2 * μ (F (k + 1))) := by
                ring
            _ ≤ 2 ^ k * μ (F k) := by gcongr
            _ ≤ μ B := ih
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hε.ne' (measure_ne_top μ B)
    refine ⟨F n, (hFm n).2.2, (hFm n).1, (hFm n).2.1, ?_⟩
    by_contra hcon
    push_neg at hcon
    have hpow : (n : ℝ≥0∞) ≤ 2 ^ n := by
      have h := Nat.lt_two_pow_self (n := n)
      exact_mod_cast h.le
    have hchain2 : (n : ℝ≥0∞) * ε ≤ μ B :=
      calc (n : ℝ≥0∞) * ε ≤ 2 ^ n * μ (F n) := by gcongr
        _ ≤ μ B := hFdec n
    exact absurd hn (not_lt.mpr hchain2)
  set 𝒮 : Set (Set X) := {S | MeasurableSet S ∧ μ S ≤ r} with h𝒮
  have hempty : (∅ : Set X) ∈ 𝒮 := ⟨MeasurableSet.empty, by simp⟩
  have hchain : ∀ f : ℕ → Set X, (∀ n, f n ∈ 𝒮) → Monotone f →
      ∃ S ∈ 𝒮, ∀ n, f n ⊆ S := by
    intro f hf hmono
    refine ⟨⋃ n, f n, ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩,
      fun n => Set.subset_iUnion f n⟩
    rw [hmono.measure_iUnion]
    exact iSup_le fun n => (hf n).2
  obtain ⟨A, hA𝒮, -, hAmax⟩ := measure_zorn μ hμ 𝒮 (fun S hS => hS.1) hchain ∅ hempty
  refine ⟨A, hA𝒮.1, ?_⟩
  by_contra hne
  have hlt : μ A < r := lt_of_le_of_ne hA𝒮.2 hne
  set ε : ℝ≥0∞ := r - μ A with hεdef
  have hεpos : 0 < ε := tsub_pos_of_lt hlt
  have hcompl : 0 < μ (Set.univ \ A) := by
    have h := measure_sdiff (Set.subset_univ A) hA𝒮.1.nullMeasurableSet
      (measure_ne_top μ A)
    rw [h]
    exact lt_of_lt_of_le hεpos (tsub_le_tsub_right hr _)
  obtain ⟨C, hCsub, hCm, hCpos, hCle⟩ :=
    hsmall (Set.univ \ A) (MeasurableSet.univ.diff hA𝒮.1) hcompl ε hεpos
  have hdisj : Disjoint A C := Set.disjoint_left.mpr fun x hxA hxC => (hCsub hxC).2 hxA
  have hAC : μ (A ∪ C) = μ A + μ C := measure_union hdisj hCm
  have hAC𝒮 : A ∪ C ∈ 𝒮 := by
    refine ⟨hA𝒮.1.union hCm, ?_⟩
    rw [hAC]
    calc μ A + μ C ≤ μ A + ε := by gcongr
      _ = r := by rw [hεdef, add_tsub_cancel_of_le hA𝒮.2]
  have heq := hAmax _ hAC𝒮 Set.subset_union_left
  rw [hAC] at heq
  have hC0 : μ C = 0 := (ENNReal.add_right_inj (measure_ne_top μ A)).mp
    (by rw [heq, add_zero])
  exact absurd hCpos (by rw [hC0]; exact lt_irrefl 0)

variable (𝒜 : Type u) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] in
/-- The Prop "`𝒜` is (a copy of) `L^∞(X, μ)` via the quotient map `q`"
(mirroring the rendering of vn.tex 51IX, `Linfty_vn`).

This predicate is ours: 51IX itself only says that `L^∞(X)` is a commutative
von Neumann algebra with `∫` faithful normal positive, so there is no source
statement to transcribe here and the fields were assembled to say "`q`
presents `𝒜` as `L^∞(X, μ)`".

`smul` was added on 2026-08-16 (QUESTIONS D1, ruled by Bas).  Without it the
fields make `q` only a `∗`-*ring* map, and the intended reading of the
consumers — "every `f` is a.e. constant, hence `L^∞ ≅ ℂ`, hence an nmiu-map"
— does not follow: a `∗`-ring isomorphism `ℂ → 𝒜` need not be `ℂ`-linear, as
complex conjugation shows.  **130II** `atomic_measure_space` was proved before
the fix by routing through Gelfand–Mazur (**16VII**) instead, so it does not
depend on `smul`; the other three consumers (**129X**, **130IV**, **130V**)
were still `sorry` when the field was added. -/
structure IsLinftyOf (q : (X → ℂ) → 𝒜) : Prop where
  surj : ∀ y : 𝒜, ∃ f, IsBoundedMeasurable X f ∧ q f = y
  add : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
    q (f + g) = q f + q g
  smul : ∀ (z : ℂ) f, IsBoundedMeasurable X f → q (z • f) = z • q f
  mul : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
    q (f * g) = q f * q g
  star_map : ∀ f, IsBoundedMeasurable X f → q (star f) = star (q f)
  one : q 1 = 1
  kernel : ∀ f, IsBoundedMeasurable X f → (q f = 0 ↔ f =ᵐ[μ] 0)

/-- **129X** (`lem:continuous-finite-measure-space-not-duplicable`,
proc.tex:6363, Lemma): if `X` is a continuous finite complete measure
space for which `L^∞(X)` is duplicable, then `μ(X) = 0`. -/
theorem continuous_finite_measure_space_not_duplicable
    [IsFiniteMeasure μ] (hμ : μ.IsComplete) (hc : ContinuousSpace μ)
    (𝒜 : Type u) [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [VonNeumannAlgebra 𝒜] (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q)
    (hd : Duplicable 𝒜) : μ Set.univ = 0 := sorry

/-! ## Parsec 1300: the discrete case -/

/-- Auxiliary for **130II**, the author's opening observation
(proc.tex:6483): in an atomic measure space a measurable set is either
null or co-null. -/
theorem atomic_dichotomy [IsFiniteMeasure μ] (hX : AtomicSet μ Set.univ)
    (S : Set X) (hS : MeasurableSet S) : μ S = 0 ∨ μ Sᶜ = 0 := by
  rcases eq_or_ne (μ S) 0 with h | h
  · exact Or.inl h
  · right
    have hpos : 0 < μ S := pos_iff_ne_zero.mpr h
    have := hX.2.2 S (Set.subset_univ S) hS hpos
    rw [measure_compl hS (measure_ne_top μ S), this, tsub_self]

/-- Auxiliary for **130II**: a bounded measurable *real* function on an
atomic measure space is almost everywhere constant.

This is the author's argument (proc.tex:6489) with `f°` read back into
the measure space: he takes the two closed sets `L = {t | t ≤ f°}` and
`U = {t | f° ≤ t}`, notes that `atomic_dichotomy` makes them cover `ℝ`
and that connectedness of `ℝ` therefore puts a point in `L ∩ U`.  Here
`L` is realised concretely as `{t | μ{g < t} = 0}` and the point is its
supremum; the connectedness step becomes the (equivalent, and shorter in
Lean) observation that `μ{g < r} = μ{g > r} = 0` for `r = sup L`. -/
theorem ae_const_real_of_atomic [IsFiniteMeasure μ]
    (hX : AtomicSet μ Set.univ) (g : X → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ x, |g x| ≤ C) : ∃ r : ℝ, g =ᵐ[μ] fun _ => r := by
  set L : Set ℝ := {t : ℝ | μ {x | g x < t} = 0} with hL
  have hdown : ∀ t t' : ℝ, t' ≤ t → t ∈ L → t' ∈ L := fun t t' hle ht =>
    measure_mono_null (fun x hx => lt_of_lt_of_le hx hle) ht
  have hne : (-C - 1) ∈ L := by
    have he : {x | g x < -C - 1} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have := abs_le.mp (hC x); linarith [this.1]
    rw [hL]; simp [he]
  have hbdd : ∀ t ∈ L, t ≤ C + 1 := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have huniv : {x | g x < t} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have := abs_le.mp (hC x); linarith [this.2]
    rw [hL, Set.mem_ofPred_eq, huniv] at ht
    exact absurd ht hX.2.1.ne'
  set r := sSup L with hr
  have hLne : L.Nonempty := ⟨_, hne⟩
  have hLbdd : BddAbove L := ⟨C + 1, hbdd⟩
  have hlow : ∀ t < r, t ∈ L := by
    intro t ht
    obtain ⟨t', ht'L, ht'⟩ := exists_lt_of_lt_csSup hLne ht
    exact hdown t' t ht'.le ht'L
  have hbelow : μ {x | g x < r} = 0 := by
    have hcover : {x | g x < r} = ⋃ n : ℕ, {x | g x < r - 1 / (n + 1)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < r - g x by linarith)
        exact ⟨n, by linarith [hn]⟩
      · rintro ⟨n, hn⟩
        have : (0:ℝ) < 1 / (n + 1) := by positivity
        linarith
    rw [hcover]
    refine measure_iUnion_null fun n => hlow _ ?_
    have : (0:ℝ) < 1 / (n + 1) := by positivity
    linarith
  have habove : μ {x | r < g x} = 0 := by
    have hup : ∀ t, r < t → μ {x | t ≤ g x} = 0 := by
      intro t ht
      have htn : t ∉ L := fun h => absurd (le_csSup hLbdd h) (not_le.mpr ht)
      rcases atomic_dichotomy μ hX {x | g x < t}
        (measurableSet_lt hg measurable_const) with h | h
      · exact absurd h htn
      · exact measure_mono_null (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]; exact hx) h
    have hcover : {x | r < g x} = ⋃ n : ℕ, {x | r + 1 / (n + 1) ≤ g x} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < g x - r by linarith)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0:ℝ) < 1 / (n + 1) := by positivity
        linarith
    rw [hcover]
    refine measure_iUnion_null fun n => hup _ ?_
    have : (0:ℝ) < 1 / (n + 1) := by positivity
    linarith
  refine ⟨r, measure_mono_null (fun x hx => ?_) (measure_union_null hbelow habove)⟩
  rcases lt_trichotomy (g x) r with h | h | h
  · exact Or.inl h
  · exact absurd h hx
  · exact Or.inr h

/-- Auxiliary for **130II**: the complex case of
`ae_const_real_of_atomic`, by the author's reduction ("we only need to
consider the case that `f` takes its values in `ℝ`, because we may split
`f` in its real and imaginary parts"). -/
theorem ae_const_of_atomic [IsFiniteMeasure μ] (hX : AtomicSet μ Set.univ)
    (f : X → ℂ) (hf : IsBoundedMeasurable X f) :
    ∃ z : ℂ, f =ᵐ[μ] fun _ => z := by
  obtain ⟨hmeas, C, hC⟩ := hf
  obtain ⟨r₁, h₁⟩ := ae_const_real_of_atomic μ hX (fun x => (f x).re)
    (Complex.measurable_re.comp hmeas) C
    (fun x => le_trans (Complex.abs_re_le_norm _) (hC x))
  obtain ⟨r₂, h₂⟩ := ae_const_real_of_atomic μ hX (fun x => (f x).im)
    (Complex.measurable_im.comp hmeas) C
    (fun x => le_trans (Complex.abs_im_le_norm _) (hC x))
  refine ⟨⟨r₁, r₂⟩, ?_⟩
  filter_upwards [h₁, h₂] with x hx1 hx2
  exact Complex.ext hx1 hx2

/-- Auxiliary for **130II**: `algebraMap ℂ 𝒞` as a ∗-homomorphism. -/
def algebraMapStarHom (𝒞 : Type*) [CStarAlgebra 𝒞] : ℂ →⋆ₐ[ℂ] 𝒞 :=
  { Algebra.ofId ℂ 𝒞 with map_star' := fun z => algebraMap_star_comm z }

/-- Auxiliary for **130II**: in a nontrivial C*-algebra `algebraMap`
*reflects* positivity.  (`Theses.A.CStar.algebraMap_ofReal_nonneg` is the
forward direction.)  A positive `algebraMap ℂ 𝒞 d` is self-adjoint, so
`d` is real by injectivity of `algebraMap`; and if `d < 0` then
`algebraMap ℂ 𝒞 (-d) ≥ 0` squeezes `algebraMap ℂ 𝒞 d` to `0`. -/
theorem algebraMap_nonneg_reflect {𝒞 : Type*} [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] [Nontrivial 𝒞] {d : ℂ}
    (hpos : (0 : 𝒞) ≤ algebraMap ℂ 𝒞 d) : 0 ≤ d := by
  have hinj : Function.Injective (algebraMap ℂ 𝒞) := (algebraMap ℂ 𝒞).injective
  have hsa : IsSelfAdjoint (algebraMap ℂ 𝒞 d) := IsSelfAdjoint.of_nonneg hpos
  have hstar : star d = d := hinj (by rw [algebraMap_star_comm]; exact hsa)
  have hre : ((d.re : ℝ) : ℂ) = d := Complex.conj_eq_iff_re.mp hstar
  have hr : 0 ≤ d.re := by
    by_contra hcon
    push_neg at hcon
    have h1 : (0 : 𝒞) ≤ algebraMap ℂ 𝒞 ((-d.re : ℝ) : ℂ) :=
      Theses.A.CStar.algebraMap_ofReal_nonneg (by linarith)
    rw [Complex.ofReal_neg, map_neg, neg_nonneg, hre] at h1
    have hz : algebraMap ℂ 𝒞 d = 0 := le_antisymm h1 hpos
    have hd0 : d = 0 := hinj (by rw [hz, map_zero])
    have : d.re = 0 := by rw [hd0]; simp
    linarith
  rw [← hre]
  exact Complex.zero_le_real.mpr hr

/-- **130II** (`lem:atomic-measure-space`, proc.tex:6471, Lemma): for an
atomic measure space `A` we have `L^∞(A) ≅ ℂ`.

The author's argument (proc.tex:6474) is the first half: every
`f ∈ 𝓛^∞(A)` is almost everywhere constant, i.e. `𝒜` is the image of
`ψ : z ↦ q(const z)`.  Since `ψ` is an injective unital ∗-ring
homomorphism *onto* `𝒜`, every nonzero element of `𝒜` is invertible, so
Gelfand–Mazur (**16VII**) makes `algebraMap ℂ 𝒜` surjective — which is
how "`L^∞(X) ≅ ℂ`" is turned into an nmiu-isomorphism.  (Going through
Gelfand–Mazur avoids having to show by hand that `ψ` is the `ℂ`-algebra
map: `IsLinftyOf` records only that `q` is additive and multiplicative,
and a ∗-ring isomorphism `ℂ → 𝒜` need not be `ℂ`-linear — complex
conjugation is one.)

Note `hμ : μ.IsComplete` is not used; nor is `𝒜`'s von-Neumann-ness, in
the sense that the argument shows `𝒜` is C*-isomorphic to `ℂ` and only
then reads off normality. -/
theorem atomic_measure_space [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hX : AtomicSet μ Set.univ) (𝒜 : Type u) [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q) :
    ∃ φ : NMIUMap 𝒜 ℂ, Function.Bijective ⇑φ := by
  classical
  have hconstBM : ∀ z : ℂ, IsBoundedMeasurable X (fun _ : X => z) :=
    fun z => ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩
  have hsubBM : ∀ f g : X → ℂ, IsBoundedMeasurable X f →
      IsBoundedMeasurable X g → IsBoundedMeasurable X (f - g) := by
    rintro f g ⟨hf, Cf, hCf⟩ ⟨hg, Cg, hCg⟩
    exact ⟨hf.sub hg, Cf + Cg, fun x =>
      le_trans (norm_sub_le _ _) (add_le_add (hCf x) (hCg x))⟩
  have hqcongr : ∀ f g : X → ℂ, IsBoundedMeasurable X f →
      IsBoundedMeasurable X g → f =ᵐ[μ] g → q f = q g := by
    intro f g hf hg h
    have hsub := hsubBM f g hf hg
    have h0 : q (f - g) = 0 := by
      refine (hq.kernel _ hsub).mpr ?_
      filter_upwards [h] with x hx
      simp [hx]
    have hadd := hq.add (f - g) g hsub hg
    rw [sub_add_cancel, h0, zero_add] at hadd
    exact hadd
  set ψ : ℂ → 𝒜 := fun z => q (fun _ => z) with hψdef
  have hψadd : ∀ z w : ℂ, ψ (z + w) = ψ z + ψ w := by
    intro z w
    have h := hq.add (fun _ => z) (fun _ => w) (hconstBM z) (hconstBM w)
    have heq : ((fun _ : X => z) + (fun _ : X => w)) = (fun _ : X => z + w) := rfl
    rw [heq] at h
    exact h
  have hψmul : ∀ z w : ℂ, ψ (z * w) = ψ z * ψ w := by
    intro z w
    have h := hq.mul (fun _ => z) (fun _ => w) (hconstBM z) (hconstBM w)
    have heq : ((fun _ : X => z) * (fun _ : X => w)) = (fun _ : X => z * w) := rfl
    rw [heq] at h
    exact h
  have hψone : ψ 1 = 1 := hq.one
  have hconst_ae : ∀ c : ℂ, (fun _ : X => c) =ᵐ[μ] 0 → c = 0 := by
    intro c hc
    by_contra hne
    have hset : {x : X | ¬ ((fun _ : X => c) x = (0 : X → ℂ) x)} = Set.univ := by
      ext x; simp [hne]
    have h := ae_iff.mp hc
    rw [hset] at h
    exact absurd h hX.2.1.ne'
  have hψzero : ψ 0 = 0 := (hq.kernel _ (hconstBM 0)).mpr (by rfl)
  have hψinj : Function.Injective ψ := by
    intro z w h
    have hz : ψ (z - w) = 0 := by
      have h2 := hψadd (z - w) w
      rw [sub_add_cancel, h] at h2
      exact (add_eq_right).mp h2.symm
    exact sub_eq_zero.mp (hconst_ae _ ((hq.kernel _ (hconstBM (z - w))).mp hz))
  -- the author's claim: `𝒜` is exactly the set of classes of constants
  have hψsurj : ∀ y : 𝒜, ∃ z : ℂ, y = ψ z := by
    intro y
    obtain ⟨f, hfBM, hfy⟩ := hq.surj y
    obtain ⟨z, hz⟩ := ae_const_of_atomic μ hX f hfBM
    exact ⟨z, by rw [← hfy, hqcongr f _ hfBM (hconstBM z) hz]⟩
  have hunit : ∀ a : 𝒜, a ≠ 0 → IsUnit a := by
    intro a ha
    obtain ⟨z, rfl⟩ := hψsurj a
    have hz : z ≠ 0 := fun h => ha (by rw [h, hψzero])
    exact ⟨⟨ψ z, ψ z⁻¹, by rw [← hψmul, mul_inv_cancel₀ hz, hψone],
      by rw [← hψmul, inv_mul_cancel₀ hz, hψone]⟩, rfl⟩
  have hnt : Nontrivial 𝒜 := by
    refine ⟨1, 0, fun h => one_ne_zero (hψinj ?_)⟩
    rw [hψone, hψzero, h]
  -- Gelfand–Mazur turns that into surjectivity of `algebraMap`
  have hsurjA : Function.Surjective (algebraMap ℂ 𝒜) := by
    intro a
    obtain ⟨z, hz⟩ := Theses.A.CStar.gelfand_mazur hunit a
    exact ⟨z, hz.symm⟩
  have hinjA : Function.Injective (algebraMap ℂ 𝒜) := (algebraMap ℂ 𝒜).injective
  have hbij : Function.Bijective ⇑(algebraMapStarHom 𝒜) := ⟨hinjA, hsurjA⟩
  set e : ℂ ≃⋆ₐ[ℂ] 𝒜 := StarAlgEquiv.ofBijective (algebraMapStarHom 𝒜) hbij with he
  set φ : 𝒜 ≃⋆ₐ[ℂ] ℂ := e.symm with hφ
  have hφe : ∀ z : ℂ, φ (algebraMap ℂ 𝒜 z) = z := fun z => e.symm_apply_apply z
  have heφ : ∀ a : 𝒜, algebraMap ℂ 𝒜 (φ a) = a := fun a => e.apply_symm_apply a
  have hmono' : ∀ z w : ℂ, z ≤ w → algebraMap ℂ 𝒜 z ≤ algebraMap ℂ 𝒜 w := by
    intro z w h
    obtain ⟨hre, him⟩ := Complex.le_def.mp h
    have heq : w - z = ((w.re - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [← sub_nonneg, ← map_sub, heq]
    exact Theses.A.CStar.algebraMap_ofReal_nonneg (by linarith)
  have hmono : ∀ a b : 𝒜, a ≤ b → φ a ≤ φ b := by
    intro a b h
    refine sub_nonneg.mp (algebraMap_nonneg_reflect (𝒞 := 𝒜) (d := φ b - φ a) ?_)
    rw [map_sub, heφ, heφ, sub_nonneg]
    exact h
  -- normality: `φ` and its inverse are monotone, so suprema transport
  have hnorm : PreservesDirSups ⇑(φ : 𝒜 →⋆ₐ[ℂ] ℂ) := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact hmono _ _ (hlub.1 hd)
    · intro u hu
      obtain ⟨d₀, hd₀⟩ := hne
      have hu0 : φ (d₀ : 𝒜) ≤ u := hu ⟨d₀, hd₀, rfl⟩
      have hsa0 : star (φ (d₀ : 𝒜)) = φ (d₀ : 𝒜) := by
        rw [← map_star]; exact congrArg _ d₀.2
      have him0 : (φ (d₀ : 𝒜)).im = 0 := Complex.conj_eq_iff_im.mp hsa0
      have himu : u.im = 0 := by
        have h := (Complex.le_def.mp hu0).2
        rw [him0] at h
        exact h.symm
      have hure : ((u.re : ℝ) : ℂ) = u := by apply Complex.ext <;> simp [himu]
      have hsaA : IsSelfAdjoint (algebraMap ℂ 𝒜 u) := by
        rw [← hure]; exact Theses.A.CStar.isSelfAdjoint_algebraMap_ofReal u.re
      have hub : (⟨algebraMap ℂ 𝒜 u, hsaA⟩ : selfAdjoint 𝒜) ∈ upperBounds D := by
        intro d hd
        have hle : φ (d : 𝒜) ≤ u := hu ⟨d, hd, rfl⟩
        have h2 := hmono' _ _ hle
        rw [heφ] at h2
        exact h2
      have h4 := hmono _ _ (hlub.2 hub)
      rwa [hφe] at h4
  exact ⟨{ toStarAlgHom := (φ : 𝒜 →⋆ₐ[ℂ] ℂ), preservesDirSups' := hnorm },
    φ.bijective⟩

/-- **130IV** (`lem:measure-space-partition`, proc.tex:6518, Exercise):
`L^∞(X) ≅ ⊕_{A ∈ 𝒫} L^∞(A)` for every countable partition `𝒫` of a
finite measure space `X` into measurable subsets (rendered for a
partition indexed by `ℕ` and abstract copies `ℬₙ` of the
`L^∞(Pₙ)`). -/
theorem measure_space_partition [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (P : ℕ → Set X) (hmeas : ∀ n, MeasurableSet (P n))
    (hdisj : Pairwise (Function.onFun Disjoint P))
    (hcover : Set.univ ⊆ ⋃ n, P n) (𝒜 : Type u) [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q) (ℬ : ℕ → Type u)
    [∀ n, CStarAlgebra (ℬ n)] [∀ n, Nontrivial (ℬ n)]
    [∀ n, PartialOrder (ℬ n)] [∀ n, StarOrderedRing (ℬ n)]
    [∀ n, VonNeumannAlgebra (ℬ n)] (qB : ∀ n, (X → ℂ) → ℬ n)
    (hqB : ∀ n, IsLinftyOf (μ.restrict (P n)) (ℬ n) (qB n)) :
    ∃ φ : NMIUMap 𝒜 (lp ℬ ∞), Function.Bijective ⇑φ := sorry

/-- **130V** (`cor:discrete-ell-x`, proc.tex:6525, Corollary): for a
discrete measure space `X` with `μ(X) < ∞` there is a set `Y` with
`L^∞(X) ≅ ℓ^∞(Y)`. -/
theorem discrete_ell_x [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hd : DiscreteSpace μ) (𝒜 : Type u) [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q) :
    ∃ (Y : Type u) (φ : NMIUMap 𝒜 (linf Y)), Function.Bijective ⇑φ :=
  sorry

end MeasureTheory

/-! ## Parsec 1320: monoids in `W*_miu` and `W*_cpsu`

**132II** (proc.tex:6607): the standard notions of (commutative) monoid
and monoid morphism in a symmetric monoidal category — rendered
concretely below (multiplication + unit element, laws on pure tensors),
cf. the file docstring. -/

variable (A) in
/-- **132II** (proc.tex:6607), rendered: a monoid on `𝒜` in `W*_cpsu`
(multiplication an ncpsu-map, unit an effect; associativity and unit laws
on pure tensors). -/
structure MonoidInWcpsu [VonNeumannAlgebra A] : Type u where
  m : NCPSUMap (VNT A A) A
  e : A
  e_mem : e ∈ effects A
  assoc : ∀ a b c : A,
    m.toNCPMap (m.toNCPMap (a ⊗ᵥ b) ⊗ᵥ c) =
      m.toNCPMap (a ⊗ᵥ m.toNCPMap (b ⊗ᵥ c))
  left_unit : ∀ a : A, m.toNCPMap (e ⊗ᵥ a) = a
  right_unit : ∀ a : A, m.toNCPMap (a ⊗ᵥ e) = a

variable (A) in
/-- **132II** (proc.tex:6607), rendered: a monoid on `𝒜` in `W*_miu`
(multiplication an nmiu-map; the unit map `ℂ → 𝒜`, being unital, is
determined and its value at `1` is `1`). -/
structure MonoidInWmiu [VonNeumannAlgebra A] : Type u where
  m : NMIUMap (VNT A A) A
  assoc : ∀ a b c : A,
    m (m (a ⊗ᵥ b) ⊗ᵥ c) = m (a ⊗ᵥ m (b ⊗ᵥ c))
  left_unit : ∀ a : A, m ((1 : A) ⊗ᵥ a) = a
  right_unit : ∀ a : A, m (a ⊗ᵥ (1 : A)) = a

/-- **132III** (`prop:dup-vna-is-monoid`, proc.tex:6677, Exercise),
part 1: any monoid structure on `𝒜` in `W*_cpsu` is a duplicator. -/
theorem dup_vna_is_monoid_1 [VonNeumannAlgebra A] (M : MonoidInWcpsu A) :
    Duplicable A :=
  -- A monoid in `W*_cpsu` is a duplicator on the nose: an ncpsu-map is in
  -- particular a positive, normal, subunital map, and the unit laws are the
  -- monoid's own (associativity and commutativity are not required of a
  -- duplicator).
  ⟨{ δ := PositiveLinearMap.ofClass M.m.toNCPMap.toCompletelyPositiveMap
     normal := M.m.toNCPMap.preservesDirSups'
     subunital := M.m.subunital'
     unit := M.e
     unit_mem := M.e_mem
     left_unit := M.left_unit
     right_unit := M.right_unit }⟩

/-- The multiplication of a monoid in `W*_cpsu` is the algebra's own, and its
unit is `1` — **128VIII** applied to the duplicator of `dup_vna_is_monoid_1`. -/
private theorem monoid_e_and_mul [VonNeumannAlgebra A] (M : MonoidInWcpsu A) :
    M.e = 1 ∧ ∀ a b : A, M.m.toNCPMap (a ⊗ᵥ b) = a * b := by
  set d : Duplicator A :=
    { δ := PositiveLinearMap.ofClass M.m.toNCPMap.toCompletelyPositiveMap
      normal := M.m.toNCPMap.preservesDirSups'
      subunital := M.m.subunital'
      unit := M.e
      unit_mem := M.e_mem
      left_unit := M.left_unit
      right_unit := M.right_unit } with hd
  exact ⟨(unit_duplicator d).1, (uniqueness_duplicator d).2⟩

/-- **132III** (`prop:dup-vna-is-monoid`, proc.tex:6677, Exercise),
part 2: there is a monoid structure on `𝒜` in `W*_miu` or `W*_cpsu` iff
`𝒜` is duplicable iff `𝒜 ≅ ℓ^∞(X)` for some `X`; and in that case the
multiplication is commutative and uniquely fixed by `m(a ⊗ b) = a·b`. -/
theorem dup_vna_is_monoid_2 [VonNeumannAlgebra A] :
    (Nonempty (MonoidInWmiu A) ↔ Duplicable A) ∧
      (Nonempty (MonoidInWcpsu A) ↔ Duplicable A) ∧
      (Duplicable A ↔ ∃ (X : Type u) (φ : NMIUMap A (linf X)),
        Function.Bijective ⇑φ) ∧
      (∀ M : MonoidInWcpsu A, ∀ a b : A,
        M.m.toNCPMap (a ⊗ᵥ b) = a * b) := sorry

/-- **132III** (`prop:dup-vna-is-monoid`, proc.tex:6677, Exercise),
part 3: the monoid morphisms in `W*_miu` and `W*_cpsu` are precisely the
(unital, multiplicative — hence nmiu) maps. -/
theorem dup_vna_is_monoid_3 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (M₁ : MonoidInWcpsu A) (M₂ : MonoidInWcpsu B) (f : NCPSUMap A B) :
    ((∀ a b : A, f.toNCPMap (M₁.m.toNCPMap (a ⊗ᵥ b)) =
        M₂.m.toNCPMap (f.toNCPMap a ⊗ᵥ f.toNCPMap b)) ∧
      f.toNCPMap M₁.e = M₂.e) ↔
      (f.toNCPMap 1 = 1 ∧
        ∀ a b : A, f.toNCPMap (a * b) = f.toNCPMap a * f.toNCPMap b) := by
  -- By 128VIII both multiplications are the algebras' own and both units are
  -- `1`, so the two sides say the same thing.
  obtain ⟨he₁, hm₁⟩ := monoid_e_and_mul M₁
  obtain ⟨he₂, hm₂⟩ := monoid_e_and_mul M₂
  constructor
  · rintro ⟨hmul, hunit⟩
    refine ⟨by rw [← he₁, hunit, he₂], fun a b => ?_⟩
    have h := hmul a b
    rwa [hm₁, hm₂] at h
  · rintro ⟨hunit, hmul⟩
    refine ⟨fun a b => ?_, by rw [he₁, hunit, he₂]⟩
    rw [hm₁, hm₂]
    exact hmul a b

/-- **132III** (`prop:dup-vna-is-monoid`, proc.tex:6677, Exercise),
part 4: `CMon(W*_miu) = Mon(W*_miu) = CMon(W*_cpsu) = Mon(W*_cpsu)` —
rendered: every monoid in `W*_cpsu` is commutative (`m ∘ γ = m`) and its
multiplication is an nmiu-map. -/
theorem dup_vna_is_monoid_4 [VonNeumannAlgebra A] (M : MonoidInWcpsu A) :
    (∀ t : VNT A A, M.m.toNCPMap (braiding A A t) = M.m.toNCPMap t) ∧
      ∃ ρ : NMIUMap (VNT A A) A, ∀ t, ρ t = M.m.toNCPMap t := sorry

/-- **132III** (`prop:dup-vna-is-monoid`, proc.tex:6677, Exercise),
part 5: `Mon(W*_miu) ≅ dW*_miu ≃ Set^op` — rendered: for duplicable
`𝒜`, `ℬ` the functor `nsp` is bijective on nmiu-maps `𝒜 → ℬ`. -/
theorem dup_vna_is_monoid_5 [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (hA : Duplicable A) (hB : Duplicable B) :
    Function.Bijective
      (fun f : NMIUMap A B => (nspMap f : nsp B → nsp A)) := sorry

/-- **132IV** (`thm:free-monoid-in-vNAMIU`, proc.tex:6719, Theorem),
well-definedness of the unit: `η : 𝒜 → ℓ^∞(nsp(𝒜))`,
`η(a)(φ) = φ(a)`, is an nmiu-map. -/
theorem exists_freeMonoidUnit [VonNeumannAlgebra A] :
    ∃ η : NMIUMap A (linf (nsp A)),
      ∀ (a : A) (φ : nsp A), η a φ = φ a := by
  -- `η(a) = (φ ↦ φ(a))` is bounded by `‖a‖` because nmiu-maps are contractive;
  -- it is a ∗-homomorphism because the operations on `ℓ^∞` are pointwise; and
  -- it is normal because the order on `ℓ^∞` is pointwise and each `φ` is normal.
  have hmem : ∀ a : A, Memℓp (fun φ : nsp A => φ a) ∞ := by
    intro a
    refine memℓp_infty ⟨‖a‖, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le φ.toStarAlgHom a
  have halg : ∀ c : ℂ,
      ((algebraMap ℂ (linf (nsp A)) c : linf (nsp A)) : nsp A → ℂ) = fun _ => c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, lp.coeFn_smul, lp.infty_coeFn_one]
    funext φ
    simp
  have hstar : ∀ a : A, ∀ φ : nsp A, φ (star a) = star (φ a) :=
    fun a φ => map_star φ.toStarAlgHom a
  refine ⟨{ toStarAlgHom :=
              { toFun := fun a => ⟨fun φ : nsp A => φ a, hmem a⟩
                map_one' := by
                  apply lp.ext
                  rw [lp.infty_coeFn_one]
                  funext φ
                  exact map_one φ.toStarAlgHom
                map_mul' := fun a b => by
                  apply lp.ext
                  rw [lp.infty_coeFn_mul]
                  funext φ
                  exact map_mul φ.toStarAlgHom a b
                map_zero' := by
                  apply lp.ext
                  rw [lp.coeFn_zero]
                  funext φ
                  exact map_zero φ.toStarAlgHom
                map_add' := fun a b => by
                  apply lp.ext
                  rw [lp.coeFn_add]
                  funext φ
                  exact map_add φ.toStarAlgHom a b
                commutes' := fun c => by
                  apply lp.ext
                  rw [halg c]
                  funext φ
                  show φ.toStarAlgHom (algebraMap ℂ A c) = c
                  exact φ.toStarAlgHom.commutes c
                map_star' := fun a => by
                  apply lp.ext
                  rw [lp.coeFn_star]
                  funext φ
                  exact hstar a φ }
            preservesDirSups' := ?_ }, fun _ _ => rfl⟩
  intro D s hne hdir hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    rw [lp_infty_le_iff]
    intro φ
    exact OrderHomClass.mono φ.toStarAlgHom (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · intro u hu
    rw [lp_infty_le_iff]
    intro φ
    have hφ := φ.preservesDirSups' D s hne hdir hlub
    refine hφ.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    exact (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) φ

/-- The unit `η : 𝒜 → ℓ^∞(nsp(𝒜))` of 132IV, by choice. -/
noncomputable def freeMonoidUnit [VonNeumannAlgebra A] :
    NMIUMap A (linf (nsp A)) := (exists_freeMonoidUnit (A := A)).choose

/-- **132IV** (`thm:free-monoid-in-vNAMIU`, proc.tex:6719, Theorem):
`ℓ^∞(nsp(𝒜))` is the free (commutative) monoid on `𝒜` in `W*_miu` via
`η`: for every monoid `ℬ` in `W*_miu` and nmiu-map `f : 𝒜 → ℬ` there is
a unique monoid morphism `g : ℓ^∞(nsp(𝒜)) → ℬ` with `g ∘ η = f`. -/
theorem free_monoid_in_vNAMIU [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (M : MonoidInWmiu B) (f : NMIUMap A B) :
    ∃! g : NMIUMap (linf (nsp A)) B,
      (∀ h₁ h₂ : linf (nsp A), g (h₁ * h₂) = M.m (g h₁ ⊗ᵥ g h₂)) ∧
        ∀ a : A, f a = g (freeMonoidUnit a) := sorry

/-- **132VI** (proc.tex:6766, Corollary), well-definedness of the unit:
evaluation `𝒜 → ℓ^∞(W*_cpsu(𝒜, ℂ))` is an ncpsu-map. -/
theorem exists_freeMonoidUnitCpsu [VonNeumannAlgebra A] :
    ∃ η : NCPSUMap A (linf (NCPSUMap A ℂ)),
      ∀ (a : A) (ω : NCPSUMap A ℂ), η.toNCPMap a ω = ω.toNCPMap a := sorry

/-- **132VI** (proc.tex:6766, Corollary): `ℓ^∞(W*_cpsu(𝒜, ℂ))` is the
free (commutative) monoid on `𝒜` in `W*_cpsu`: every ncpsu-map from `𝒜`
to a monoid in `W*_cpsu` factors uniquely through it by a monoid
morphism. -/
theorem free_monoid_in_Wcpsu [VonNeumannAlgebra A] [VonNeumannAlgebra B]
    (η : NCPSUMap A (linf (NCPSUMap A ℂ)))
    (hη : ∀ (a : A) (ω : NCPSUMap A ℂ), η.toNCPMap a ω = ω.toNCPMap a)
    (M : MonoidInWcpsu B) (f : NCPSUMap A B) :
    ∃! g : NMIUMap (linf (NCPSUMap A ℂ)) B,
      (∀ h₁ h₂ : linf (NCPSUMap A ℂ),
        g (h₁ * h₂) = M.m.toNCPMap (g h₁ ⊗ᵥ g h₂)) ∧
        ∀ a : A, f.toNCPMap a = g (η.toNCPMap a) := sorry

end Theses.A.Proc
