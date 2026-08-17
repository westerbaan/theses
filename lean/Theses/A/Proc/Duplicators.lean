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

/-- **127III** (`duplicable`, proc.tex:5881, Theorem), the easy direction:
`ℓ^∞(X)` is duplicable.

The thesis says only "the result is obviously true for discrete spaces"
(proc.tex:5905); here is the argument.  **123I**.3 `linf_tensor` says that
`(f, g) ↦ ((x,y) ↦ f(x)g(y))` is a tensor product of `ℓ^∞(X)` with itself
on `ℓ^∞(X × X)`, so **114II** `tensor_uniqueness` gives an nmiu-isomorphism
`φ : ℓ^∞(X) ⊗ ℓ^∞(X) ≅ ℓ^∞(X × X)`; restriction along the diagonal
`ℓ^∞(X × X) → ℓ^∞(X)` is `linfMap (fun x => (x, x))` (**122II**), and the
composite sends `f ⊗ g` to `f · g`, so **128XI**
`duplicability_multiplication` turns it into a duplicator. -/
private theorem linf_duplicable (X : Type u) : Duplicable (linf X) := by
  classical
  obtain ⟨γ, hγ, hγT⟩ := linf_tensor X X
  obtain ⟨φ, hφ, -, -⟩ :=
    tensor_uniqueness (vnTensor (linf X) (linf X)).map γ
      (vnTensor (linf X) (linf X)).isTensorProduct hγT
  set d : NMIUMap (VNT (linf X) (linf X)) (linf X) :=
    nmiuComp (linfMap (fun x : X => (x, x))) φ with hd
  have hdiag : ∀ (g : linf (X × X)) (x : X),
      ((linfMap (fun x : X => (x, x)) g : linf X) : ∀ _ : X, ℂ) x
        = (g : ∀ _ : X × X, ℂ) (x, x) :=
    (exists_linfMap (fun x : X => (x, x))).choose_spec
  refine (duplicability_multiplication (A := linf X)).1.mpr
    ⟨PositiveLinearMap.ofClass (nmiuNCP d).toCompletelyPositiveMap,
      (nmiuNCP d).preservesDirSups', fun a b => ?_⟩
  show d (a ⊗ᵥ b) = a * b
  rw [hd, nmiuComp_apply,
    show ((a ⊗ᵥ b) : VNT (linf X) (linf X))
      = (vnTensor (linf X) (linf X)).map a b from rfl, hφ a b]
  refine lp.ext (funext fun x => ?_)
  rw [hdiag, hγ a b x x, lp.infty_coeFn_mul, Pi.mul_apply]

/-- Auxiliary for **128XIII**: the inclusion `κᵢ : 𝒜ᵢ → ⊕ⱼ𝒜ⱼ` is normal.
(The projections are **47IV**.2, `vn_products_proj_normal`.)  Directed
suprema in `⊕ⱼ𝒜ⱼ` are computed coordinatewise, and `κᵢ` is `0` off `i`. -/
private theorem lpKappa_normal {I : Type u} (𝒜 : I → Type u)
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)] (i : I) :
    PreservesDirSups (fun a : 𝒜 i => lpKappa i a) := by
  intro D s hne _ hlub
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    exact lpKappa_le i (Subtype.coe_le_coe.mpr (hlub.1 hd))
  · intro u hu
    obtain ⟨d₀, hd₀⟩ := hne
    have hu₀ : lpKappa i (d₀ : 𝒜 i) ≤ u := hu ⟨d₀, hd₀, rfl⟩
    have husa : IsSelfAdjoint u := by
      have h1 : IsSelfAdjoint (u - lpKappa i (d₀ : 𝒜 i)) :=
        IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hu₀)
      have h2 := h1.add (lpKappa_sa' i d₀.2)
      rwa [sub_add_cancel] at h2
    rw [lp_infty_le_iff]
    intro j
    by_cases hj : j = i
    · subst hj
      rw [lpKappa_apply_self]
      have hub : (⟨(u : ∀ j, 𝒜 j) j, lp_infty_isSelfAdjoint husa j⟩ :
          selfAdjoint (𝒜 j)) ∈ upperBounds D := by
        intro d hd
        rw [← Subtype.coe_le_coe]
        have h2 := (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) j
        rwa [lpKappa_apply_self] at h2
      exact Subtype.coe_le_coe.mpr (hlub.2 hub)
    · rw [lpKappa_apply_ne _ _ hj]
      have h2 := (lp_infty_le_iff _ _).mp hu₀ j
      rwa [lpKappa_apply_ne _ _ hj] at h2

/-- **128XIII** (`cor:duplicable-product`, proc.tex:6128, Corollary): when
a direct sum of von Neumann algebras is duplicable, so is each summand.
(Stated for an arbitrary family; the thesis states the binary case
`𝒜 ⊕ ℬ`.) -/
theorem duplicable_product {I : Type u} (𝒜 : I → Type u)
    [∀ i, CStarAlgebra (𝒜 i)] [∀ i, Nontrivial (𝒜 i)]
    [∀ i, PartialOrder (𝒜 i)] [∀ i, StarOrderedRing (𝒜 i)]
    [∀ i, VonNeumannAlgebra (𝒜 i)] (h : Duplicable (lp 𝒜 ∞)) (i : I) :
    Duplicable (𝒜 i) := by
  -- **128XII** turns the duplicator on `⊕ⱼ𝒜ⱼ` into its multiplication
  obtain ⟨δ, hδnorm, hδmul⟩ := (duplicability_multiplication (A := lp 𝒜 ∞)).1.mp h
  -- the inclusion `κᵢ : 𝒜ᵢ → ⊕ⱼ𝒜ⱼ` is an ncp-map: it is an mi-map (**34IV**.3)
  set κlin : 𝒜 i →ₗ[ℂ] lp 𝒜 ∞ :=
    { toFun := fun a => lpKappa i a
      map_add' := lpKappa_add i
      map_smul' := fun c a => lpKappa_smul i c a } with hκlin
  have hκcp : Theses.A.CStar.IsCompletelyPositiveMap κlin :=
    Theses.A.CStar.cp_of_mi κlin (fun a b => (lpKappa_mul i a b).symm)
      (fun a => (lpKappa_star i a).symm)
  set κ : NCPMap (𝒜 i) (lp 𝒜 ∞) :=
    { toCompletelyPositiveMap :=
        { toLinearMap := κlin
          map_cstarMatrix_nonneg' :=
            (Theses.A.CStar.cp_iff κlin).out 0 1 |>.mp hκcp }
      preservesDirSups' := lpKappa_normal 𝒜 i } with hκ
  have hκapp : ∀ a : 𝒜 i, κ a = lpKappa i a := fun _ => rfl
  -- `δᵢ := πᵢ ∘ δ ∘ (κᵢ ⊗ κᵢ)`, with `κᵢ ⊗ κᵢ` from **115II**
  set Pκ : VNT (𝒜 i) (𝒜 i) →ₚ[ℂ] VNT (lp 𝒜 ∞) (lp 𝒜 ∞) :=
    PositiveLinearMap.ofClass (tmap κ κ).toCompletelyPositiveMap with hPκ
  set Pπ : lp 𝒜 ∞ →ₚ[ℂ] 𝒜 i :=
    { toLinearMap := lpEvalₗ 𝒜 i
      monotone' := fun a b hab => (lp_infty_le_iff a b).mp hab i } with hPπ
  refine (duplicability_multiplication (A := 𝒜 i)).1.mpr
    ⟨Pπ.comp (δ.comp Pκ), ?_, ?_⟩
  · -- normality of a composite of normal maps
    have h1 : PreservesDirSups (fun t : VNT (𝒜 i) (𝒜 i) => δ (Pκ t)) :=
      preservesDirSups_comp (fun _ hx => isSelfAdjoint_map_of_pos Pκ hx)
        (fun _ _ hxy => Pκ.monotone' hxy) (tmap κ κ).preservesDirSups' hδnorm
    exact preservesDirSups_comp (f := fun t : VNT (𝒜 i) (𝒜 i) => δ (Pκ t))
      (g := fun x : lp 𝒜 ∞ => Pπ x)
      (fun _ hx => isSelfAdjoint_map_of_pos (δ.comp Pκ) hx)
      (fun _ _ hxy => (δ.comp Pκ).monotone' hxy) h1 (vn_products_proj_normal 𝒜 i)
  · -- `πᵢ(δ(κᵢa ⊗ κᵢb)) = πᵢ(κᵢa · κᵢb) = πᵢ(κᵢ(ab)) = ab`
    intro a b
    show Pπ (δ (Pκ (a ⊗ᵥ b))) = a * b
    have hPκa : Pκ (a ⊗ᵥ b) = κ a ⊗ᵥ κ b := tmap_apply κ κ a b
    rw [hPκa, hκapp, hκapp, hδmul, lpKappa_mul]
    exact lpKappa_apply_self i (a * b)

/-- **128XIII** for corners: a corner `e𝒜e` of a duplicable von Neumann
algebra is duplicable.  (The thesis states only the direct-sum case
`cor:duplicable-product`; the two-block splitting of `L^∞(X)` into its
discrete and continuous parts that **127III** needs is a splitting into
corners, not into an `lp`-sum, so this is the form actually used.)

By **128XI** the duplicator of `𝒜` is multiplication, and
`x ↦ e·δ(ι x)·e` with `ι = cornerIncl e ⊗ cornerIncl e` (**115II**) is
multiplication on `e𝒜e`: the compression `a ↦ e·a·e` is positive
(**25II**.1) and normal (**44VIII** `ad_normal`), and `e·(a·b)·e = a·b`
for `a, b` in the corner. -/
private theorem duplicable_corner [VonNeumannAlgebra A] (e : A)
    [Fact (IsStarProjection e)] (hd : Duplicable A) : Duplicable (Corner A e) := by
  classical
  obtain ⟨δ, hδnorm, hδmul⟩ := (duplicability_multiplication (A := A)).1.mp hd
  have he : IsStarProjection e := Corner.proj e
  have hse : star e = e := he.isSelfAdjoint.star_eq
  have hee : e * e = e := he.isIdempotentElem.eq
  have hmem : ∀ a : A, e * (e * a * e) * e = e * a * e := by
    intro a
    calc e * (e * a * e) * e = (e * e) * a * (e * e) := by noncomm_ring
      _ = e * a * e := by rw [hee]
  -- the compression `a ↦ e·a·e : 𝒜 → e𝒜e`
  set π : A →ₚ[ℂ] Corner A e :=
    { toLinearMap :=
        { toFun := fun a => ⟨e * a * e, hmem a⟩
          map_add' := fun a b => Corner.val_injective (by
            show e * (a + b) * e = e * a * e + e * b * e
            rw [mul_add, add_mul])
          map_smul' := fun c a => Corner.val_injective (by
            show e * (c • a) * e = c • (e * a * e)
            rw [mul_smul_comm, smul_mul_assoc]) }
      monotone' := fun a b hab => by
        show e * a * e ≤ e * b * e
        have h := Theses.A.CStar.astara_pos_basic_1 e a b hab
        rwa [hse] at h } with hπ
  have hπval : ∀ a : A, (π a).val = e * a * e := fun _ => rfl
  have hπnorm : PreservesDirSups (fun a : A => π a) := by
    intro D s hne hdir hlub
    have h : D.Nonempty ∧ DirectedOn (· ≤ ·) D ∧ BddAbove D := ⟨hne, hdir, ⟨s, hlub.1⟩⟩
    have hnat := ad_normal e D h
    rw [hse] at hnat
    have hs : dirSup D h = s := (isLUB_dirSup D h).unique hlub
    rw [hs] at hnat
    refine Corner.isLUB_of_isLUB_image_val ?_
    have himg : Corner.val '' ((fun d : selfAdjoint A => π (d : A)) '' D)
        = (fun d : selfAdjoint A => e * (d : A) * e) '' D := by
      rw [← Set.image_comp]; rfl
    rw [himg, hπval]
    exact hnat
  -- the inclusion `e𝒜e → 𝒜`, tensored with itself
  set ι : NCPMap (Corner A e) A := (cornerIncl e).toNCPMap with hι
  have hιval : ∀ a : Corner A e, ι a = a.val := fun a => cornerIncl_apply e a
  set Pι : VNT (Corner A e) (Corner A e) →ₚ[ℂ] VNT A A :=
    PositiveLinearMap.ofClass (tmap ι ι).toCompletelyPositiveMap with hPι
  refine (duplicability_multiplication (A := Corner A e)).1.mpr
    ⟨π.comp (δ.comp Pι), ?_, ?_⟩
  · have h1 : PreservesDirSups (fun t : VNT (Corner A e) (Corner A e) => δ (Pι t)) :=
      preservesDirSups_comp (fun _ hx => isSelfAdjoint_map_of_pos Pι hx)
        (fun _ _ hxy => Pι.monotone' hxy) (tmap ι ι).preservesDirSups' hδnorm
    exact preservesDirSups_comp (f := fun t : VNT (Corner A e) (Corner A e) => δ (Pι t))
      (g := fun x : A => π x)
      (fun _ hx => isSelfAdjoint_map_of_pos (δ.comp Pι) hx)
      (fun _ _ hxy => (δ.comp Pι).monotone' hxy) h1 hπnorm
  · intro a b
    show π (δ (Pι (a ⊗ᵥ b))) = a * b
    have hea : e * a.val = a.val := by
      calc e * a.val = e * (e * a.val * e) := by rw [a.property]
        _ = (e * e) * a.val * e := by noncomm_ring
        _ = e * a.val * e := by rw [hee]
        _ = a.val := a.property
    have hbe : b.val * e = b.val := by
      calc b.val * e = (e * b.val * e) * e := by rw [b.property]
        _ = e * b.val * (e * e) := by noncomm_ring
        _ = e * b.val * e := by rw [hee]
        _ = b.val := b.property
    have hPιab : Pι (a ⊗ᵥ b) = a.val ⊗ᵥ b.val := by
      show (tmap ι ι) (a ⊗ᵥ b) = a.val ⊗ᵥ b.val
      rw [tmap_apply, hιval, hιval]
    rw [hPιab, hδmul]
    refine Corner.val_injective ?_
    rw [hπval, Corner.val_mul]
    calc e * (a.val * b.val) * e = (e * a.val) * (b.val * e) := by noncomm_ring
      _ = a.val * b.val := by rw [hea, hbe]

/-! ## Parsec 1290: measure-theoretic interlude -/

section MeasureTheory

variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

/-- **129II** (proc.tex:6188, Definition), part 1: a measurable subset `S`
of a finite complete measure space is **atomic** if `0 < μ(S)` and every
measurable `S' ⊆ S` of positive measure has `μ(S') = μ(S)`. -/
def AtomicSet (S : Set X) : Prop :=
  MeasurableSet S ∧ 0 < μ S ∧
    ∀ S' ⊆ S, MeasurableSet S' → 0 < μ S' → μ S' = μ S

/-- **129II** (proc.tex:6188, Definition), part 2, **as repaired by the
author** (ruling of Bas Westerbaan, 2026-08-16, QUESTIONS **A6**): `X` is
**discrete** if `X` can be *partitioned* into atomic measurable subsets.

⚠️ **This is deliberately not the printed definition**, and is the one
place in `A/Proc` where a transcribed statement was changed.
proc.tex:6199 reads "`X` is **discrete** if `X` is covered by atomic
measurable subsets", with the parenthetical "(This coincides with being
'purely atomic' from 211K of [fremlin].)".  The parenthetical is false
and the printed definition is strictly weaker: for `X = [0,1]` with
`μ = λ + δ₀` completed, every `{0,x}` is an atom and these cover `X`,
yet `(0,1]` is non-negligible and includes no atom.  Under the printed
definition **130V** is false, **129VI** is vacuous, and the proof of the
chapter's main theorem **127III** has a gap.  The author's ruling is to
replace "covered" by "partitioned" — the partition form rather than
Fremlin's phrasing, because it hands **130V** the index set of its
`ℓ^∞(Y)` directly instead of requiring an exhaustion argument to
manufacture one.  `discrete_iff_purelyAtomic` below shows the repaired
definition does coincide with Fremlin's 211K, so the thesis's
parenthetical becomes honest — with one exception, recorded there. -/
def DiscreteSpace : Prop :=
  ∃ 𝒬 : Set (Set X), (∀ S ∈ 𝒬, AtomicSet μ S) ∧ 𝒬.PairwiseDisjoint id ∧
    ⋃₀ 𝒬 = Set.univ

/-- Fremlin's **purely atomic** (211K of [fremlin], cited by 129II.2):
every measurable set of non-zero measure includes an atom.  Stated here
so that the parenthetical of 129II.2 can be *proved* rather than
asserted; see `discrete_iff_purelyAtomic`. -/
def PurelyAtomic : Prop :=
  ∀ E : Set X, MeasurableSet E → 0 < μ E → ∃ A ⊆ E, AtomicSet μ A

/-- **129II** (proc.tex:6188, Definition), part 3: `X` is **continuous**
(atomless) if it contains no atomic subsets. -/
def ContinuousSpace : Prop := ∀ S : Set X, ¬ AtomicSet μ S

/-- A pairwise disjoint family of atoms in a finite measure space is
countable — atoms have positive measure, and only countably many members
of a disjoint family can.  (This is what makes the partition of a
discrete space automatically countable, so that 129II.2 need not say so
and **130IV**, which is stated for countable partitions, applies.) -/
theorem atom_family_countable [IsFiniteMeasure μ] {𝒞 : Set (Set X)}
    (h𝒞 : ∀ S ∈ 𝒞, AtomicSet μ S) (hdisj : 𝒞.PairwiseDisjoint id) :
    𝒞.Countable := by
  have hcount : Set.Countable {i : 𝒞 | 0 < μ (i : Set X)} :=
    MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion
      (fun i => (h𝒞 (i : Set X) i.2).1)
      (fun i j hij => hdisj i.2 j.2 (fun h => hij (Subtype.ext h)))
  have huniv : {i : 𝒞 | 0 < μ (i : Set X)} = Set.univ := by
    ext i
    simp [(h𝒞 (i : Set X) i.2).2.1]
  rw [huniv] at hcount
  exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hcount)

/-- Every discrete space is purely atomic (Fremlin 211K): a
non-negligible `E` must meet some block `A` of the partition in positive
measure, and `E ∩ A` is then itself an atom inside `E`. -/
theorem discrete_purelyAtomic [IsFiniteMeasure μ] (hd : DiscreteSpace μ) :
    PurelyAtomic μ := by
  obtain ⟨𝒬, hat, hdisj, hcov⟩ := hd
  have hcount := atom_family_countable μ hat hdisj
  intro E hE hEpos
  have hex : ∃ A ∈ 𝒬, 0 < μ (E ∩ A) := by
    by_contra hcon
    push_neg at hcon
    have hnull : μ (⋃ A ∈ 𝒬, E ∩ A) = 0 :=
      (measure_biUnion_null_iff hcount).mpr fun A hA =>
        nonpos_iff_eq_zero.mp (hcon A hA)
    have hsub : E ⊆ ⋃ A ∈ 𝒬, E ∩ A := by
      intro x hx
      obtain ⟨A, hA, hxA⟩ := (Set.eq_univ_iff_forall.mp hcov) x
      exact Set.mem_biUnion hA ⟨hx, hxA⟩
    exact absurd (measure_mono_null hsub hnull) hEpos.ne'
  obtain ⟨A, hA, hApos⟩ := hex
  obtain ⟨hAm, -, hAat⟩ := hat A hA
  have hEA : μ (E ∩ A) = μ A := hAat _ Set.inter_subset_right (hE.inter hAm) hApos
  refine ⟨E ∩ A, Set.inter_subset_left, hE.inter hAm, hApos, fun S hS hSm hSpos => ?_⟩
  rw [hEA]
  exact hAat S (hS.trans Set.inter_subset_right) hSm hSpos

/-- A maximal pairwise disjoint family of atoms, by Zorn's lemma.  It is
countable, so its union is measurable, and by maximality the complement
of that union contains no atom at all.  This is the engine of both
**129VI** and the converse half of `discrete_iff_purelyAtomic`. -/
theorem exists_maximal_atom_family [IsFiniteMeasure μ] :
    ∃ 𝒞 : Set (Set X), (∀ A ∈ 𝒞, AtomicSet μ A) ∧ 𝒞.PairwiseDisjoint id ∧
      𝒞.Countable ∧ ∀ S : Set X, S ⊆ Set.univ \ ⋃₀ 𝒞 → ¬ AtomicSet μ S := by
  classical
  set 𝒮 : Set (Set (Set X)) :=
    {𝒞 | (∀ A ∈ 𝒞, AtomicSet μ A) ∧ 𝒞.PairwiseDisjoint id} with h𝒮
  have hzorn : ∀ c ⊆ 𝒮, IsChain (· ⊆ ·) c → ∃ ub ∈ 𝒮, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨fun A hA => ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨𝒞, h𝒞c, hA𝒞⟩ := hA
      exact (hc h𝒞c).1 A hA𝒞
    · rintro A ⟨𝒞₁, h₁c, hA₁⟩ B ⟨𝒞₂, h₂c, hB₂⟩ hAB
      rcases eq_or_ne 𝒞₁ 𝒞₂ with rfl | hne
      · exact (hc h₁c).2 hA₁ hB₂ hAB
      · rcases hchain h₁c h₂c hne with hsub | hsub
        · exact (hc h₂c).2 (hsub hA₁) hB₂ hAB
        · exact (hc h₁c).2 hA₁ (hsub hB₂) hAB
  obtain ⟨𝒞, hmax⟩ := zorn_subset 𝒮 hzorn
  obtain ⟨hat, hdisj⟩ := hmax.1
  refine ⟨𝒞, hat, hdisj, atom_family_countable μ hat hdisj, fun S hS hSat => ?_⟩
  have hSdisj : ∀ A ∈ 𝒞, Disjoint S A := by
    intro A hA
    refine Set.disjoint_left.mpr fun x hxS hxA => ?_
    exact (hS hxS).2 ⟨A, hA, hxA⟩
  have hins : insert S 𝒞 ∈ 𝒮 := by
    refine ⟨fun A hA => ?_, ?_⟩
    · rcases hA with rfl | hA
      · exact hSat
      · exact hat A hA
    · rintro A (rfl | hA) B (rfl | hB) hAB
      · exact absurd rfl hAB
      · exact hSdisj B hB
      · exact (hSdisj A hA).symm
      · exact hdisj hA hB hAB
  have hSmem : S ∈ 𝒞 :=
    hmax.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact absurd (Set.disjoint_left.mp (hSdisj S hSmem)) (by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hSat.2.1.ne'
    exact fun h => h hx hx)

/-- The parenthetical of **129II**.2, proved: for a finite measure space
carrying *some* non-negligible set, the repaired "discrete" (partitioned
into atoms) coincides with Fremlin 211K's "purely atomic".

The hypothesis `0 < μ(X)` is necessary and cannot be dropped: with
`μ = 0` on a non-empty `X` the space is purely atomic vacuously, yet has
no atoms at all and therefore admits no partition into atoms.  See
`purelyAtomic_not_discrete_of_measure_zero`.  This is harmless for
**130V**, which is trivially true there (both sides are the zero
algebra) — and note the forward implication `discrete_purelyAtomic`
needs no side condition.

Note also that **completeness of `μ` is not needed** anywhere in the
equivalence: the absorption of the leftover null set `R` into one atom
`A₁` stays inside the definition of `AtomicSet`, which quantifies only
over *measurable* subsets of `A₁ ∪ R`. -/
theorem discrete_iff_purelyAtomic [IsFiniteMeasure μ] (hpos : 0 < μ Set.univ) :
    DiscreteSpace μ ↔ PurelyAtomic μ := by
  classical
  refine ⟨discrete_purelyAtomic μ, fun hpa => ?_⟩
  obtain ⟨𝒞, hat, hdisj, hcount, hnoatom⟩ := exists_maximal_atom_family μ
  set D : Set X := ⋃₀ 𝒞 with hD
  have hDm : MeasurableSet D := MeasurableSet.sUnion hcount fun A hA => (hat A hA).1
  set R : Set X := Set.univ \ D with hR
  have hRm : MeasurableSet R := MeasurableSet.univ.diff hDm
  -- the leftover is null, since a positive-measure leftover would contain an atom
  have hRnull : μ R = 0 := by
    by_contra hne
    obtain ⟨A, hAR, hAat⟩ := hpa R hRm (pos_iff_ne_zero.mpr hne)
    exact hnoatom A hAR hAat
  -- hence `𝒞` is non-empty
  have hCne : 𝒞.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝒞 with rfl | h
    · exfalso
      have : (Set.univ : Set X) = R := by simp [hR, hD]
      rw [this] at hpos
      exact absurd hRnull hpos.ne'
    · exact h
  obtain ⟨A₁, hA₁⟩ := hCne
  have hA₁at := hat A₁ hA₁
  -- absorb the null leftover into one atom
  have habs : AtomicSet μ (A₁ ∪ R) := by
    refine ⟨hA₁at.1.union hRm, lt_of_lt_of_le hA₁at.2.1 (measure_mono Set.subset_union_left),
      fun S hS hSm hSpos => ?_⟩
    have hsplit : S = (S ∩ A₁) ∪ (S ∩ R) := by
      rw [← Set.inter_union_distrib_left, Set.inter_eq_self_of_subset_left hS]
    have hSRnull : μ (S ∩ R) = 0 :=
      measure_mono_null Set.inter_subset_right hRnull
    have hSle : μ S ≤ μ (S ∩ A₁) := by
      calc μ S = μ ((S ∩ A₁) ∪ (S ∩ R)) := by rw [← hsplit]
        _ ≤ μ (S ∩ A₁) + μ (S ∩ R) := measure_union_le _ _
        _ = μ (S ∩ A₁) := by rw [hSRnull, add_zero]
    have hSeq : μ (S ∩ A₁) = μ S :=
      le_antisymm (measure_mono Set.inter_subset_left) hSle
    have hSA₁ : μ (S ∩ A₁) = μ A₁ :=
      hA₁at.2.2 _ Set.inter_subset_right (hSm.inter hA₁at.1) (hSeq ▸ hSpos)
    have hAR : μ (A₁ ∪ R) = μ A₁ :=
      le_antisymm (le_trans (measure_union_le _ _) (by rw [hRnull, add_zero]))
        (measure_mono Set.subset_union_left)
    rw [hAR, ← hSeq, hSA₁]
  refine ⟨insert (A₁ ∪ R) (𝒞 \ {A₁}), ?_, ?_, ?_⟩
  · rintro S (rfl | ⟨hS, -⟩)
    · exact habs
    · exact hat S hS
  · have hdisjR : ∀ B ∈ 𝒞 \ {A₁}, Disjoint (A₁ ∪ R) B := by
      rintro B ⟨hB, hBne⟩
      refine Set.disjoint_union_left.mpr ⟨hdisj hA₁ hB (fun h => hBne (h ▸ rfl)), ?_⟩
      exact Set.disjoint_left.mpr fun x hxR hxB => hxR.2 ⟨B, hB, hxB⟩
    rintro A (rfl | hA) B (rfl | hB) hAB
    · exact absurd rfl hAB
    · exact hdisjR B hB
    · exact (hdisjR A hA).symm
    · exact hdisj hA.1 hB.1 hAB
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hxD : x ∈ D
    · obtain ⟨B, hB, hxB⟩ := hxD
      by_cases hBA : B = A₁
      · exact ⟨A₁ ∪ R, Set.mem_insert _ _, Or.inl (hBA ▸ hxB)⟩
      · exact ⟨B, Set.mem_insert_of_mem _ ⟨hB, hBA⟩, hxB⟩
    · exact ⟨A₁ ∪ R, Set.mem_insert _ _, Or.inr ⟨Set.mem_univ x, hxD⟩⟩

/-- The exception in `discrete_iff_purelyAtomic`, machine-checked: the
zero measure on a one-point space is purely atomic (vacuously) but not
discrete (it has no atoms, so nothing to partition `X` into). -/
theorem purelyAtomic_not_discrete_of_measure_zero :
    PurelyAtomic (0 : Measure Unit) ∧ ¬ DiscreteSpace (0 : Measure Unit) := by
  constructor
  · intro E _ hE
    simp at hE
  · rintro ⟨𝒬, hat, -, hcov⟩
    obtain ⟨A, hA, -⟩ := (Set.eq_univ_iff_forall.mp hcov) ()
    exact absurd (hat A hA).2.1 (by simp)

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
subset `D` such that `X ∖ D` is continuous.

Rendered against the **repaired** 129II.2 (see `DiscreteSpace`): "`D` is
discrete" now means "`D` is *partitioned* by atoms", not "`D` is covered
by atoms".  Under the printed definition the statement is true but
vacuous (in the `μ = λ + δ₀` counterexample `D = X` satisfies both
conjuncts), so this is the form that carries information.

⚠️ **The printed proof (proc.tex:6283) does not survive the repair.**  It
applies **129IV** `measure_zorn` to the collection of discrete measurable
subsets, justified by "clearly the countable union of discrete measurable
subsets of `X` is again discrete" — which is exactly what fails for the
partition form: an ascending union of sets each *partitioned* by atoms
need not be partitioned by atoms, because the successive partitions need
not refine one another, and the leftovers `A ∖ Dₙ` of positive-measure
atoms may be null and non-empty.  The repair used here is to run Zorn on
*pairwise disjoint families of atoms* instead of on subsets
(`exists_maximal_atom_family`), which yields the partition directly; note
that this replaces the thesis's choice-free 129IV by ordinary Zorn.  It
is **not** the repair conjectured in ERRATA ("`𝒮` = countable disjoint
unions of atoms"), which runs into the same non-refinement problem. -/
theorem measure_space_continuous_discrete [IsFiniteMeasure μ]
    (hμ : μ.IsComplete) :
    ∃ D : Set X, MeasurableSet D ∧
      (∃ 𝒬 : Set (Set X), (∀ S ∈ 𝒬, AtomicSet μ S) ∧ 𝒬.PairwiseDisjoint id ∧
        ⋃₀ 𝒬 = D) ∧
      ∀ S : Set X, S ⊆ Set.univ \ D → ¬ AtomicSet μ S := by
  obtain ⟨𝒞, hat, hdisj, hcount, hnoatom⟩ := exists_maximal_atom_family μ
  exact ⟨⋃₀ 𝒞, MeasurableSet.sUnion hcount fun A hA => (hat A hA).1,
    ⟨𝒞, hat, hdisj, rfl⟩, hnoatom⟩

/-- **129VIII** (`lem:continuous-measure-space`, proc.tex:6305, Lemma), in
the *relative* form the dyadic partition of **129X** needs: for a
continuous finite complete measure space `X`, a measurable `B ⊆ X` and
`r ∈ [0, μ(B)]` there is a measurable `A ⊆ B` with `μ(A) = r`.

This is the thesis's own proof, with `B` in place of `X` throughout — the
argument never uses that the ambient set is everything.  It is stated
separately rather than obtained from `continuous_measure_space` applied to
`μ.restrict B` because a restriction of a complete measure is not
complete. -/
private theorem continuous_measure_space_subset [IsFiniteMeasure μ]
    (hμ : μ.IsComplete) (hc : ContinuousSpace μ) (B₀ : Set X)
    (hB₀ : MeasurableSet B₀) (r : ℝ≥0∞) (hr : r ≤ μ B₀) :
    ∃ S : Set X, S ⊆ B₀ ∧ MeasurableSet S ∧ μ S = r := by
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
  set 𝒮 : Set (Set X) := {S | S ⊆ B₀ ∧ MeasurableSet S ∧ μ S ≤ r} with h𝒮
  have hempty : (∅ : Set X) ∈ 𝒮 :=
    ⟨Set.empty_subset _, MeasurableSet.empty, by simp⟩
  have hchain : ∀ f : ℕ → Set X, (∀ n, f n ∈ 𝒮) → Monotone f →
      ∃ S ∈ 𝒮, ∀ n, f n ⊆ S := by
    intro f hf hmono
    refine ⟨⋃ n, f n, ⟨Set.iUnion_subset fun n => (hf n).1,
      MeasurableSet.iUnion fun n => (hf n).2.1, ?_⟩,
      fun n => Set.subset_iUnion f n⟩
    rw [hmono.measure_iUnion]
    exact iSup_le fun n => (hf n).2.2
  obtain ⟨A, hA𝒮, -, hAmax⟩ := measure_zorn μ hμ 𝒮 (fun S hS => hS.2.1) hchain ∅ hempty
  refine ⟨A, hA𝒮.1, hA𝒮.2.1, ?_⟩
  by_contra hne
  have hlt : μ A < r := lt_of_le_of_ne hA𝒮.2.2 hne
  set ε : ℝ≥0∞ := r - μ A with hεdef
  have hεpos : 0 < ε := tsub_pos_of_lt hlt
  have hcompl : 0 < μ (B₀ \ A) := by
    have h := measure_sdiff hA𝒮.1 hA𝒮.2.1.nullMeasurableSet (measure_ne_top μ A)
    rw [h]
    exact lt_of_lt_of_le hεpos (tsub_le_tsub_right hr _)
  obtain ⟨C, hCsub, hCm, hCpos, hCle⟩ :=
    hsmall (B₀ \ A) (hB₀.diff hA𝒮.2.1) hcompl ε hεpos
  have hdisj : Disjoint A C := Set.disjoint_left.mpr fun x hxA hxC => (hCsub hxC).2 hxA
  have hAC : μ (A ∪ C) = μ A + μ C := measure_union hdisj hCm
  have hAC𝒮 : A ∪ C ∈ 𝒮 := by
    refine ⟨Set.union_subset hA𝒮.1 (fun x hx => (hCsub hx).1), hA𝒮.2.1.union hCm, ?_⟩
    rw [hAC]
    calc μ A + μ C ≤ μ A + ε := by gcongr
      _ = r := by rw [hεdef, add_tsub_cancel_of_le hA𝒮.2.2]
  have heq := hAmax _ hAC𝒮 Set.subset_union_left
  rw [hAC] at heq
  have hC0 : μ C = 0 := (ENNReal.add_right_inj (measure_ne_top μ A)).mp
    (by rw [heq, add_zero])
  exact absurd hCpos (by rw [hC0]; exact lt_irrefl 0)

/-- **129VIII** (`lem:continuous-measure-space`, proc.tex:6305, Lemma):
for a continuous finite complete measure space `X` and
`r ∈ [0, μ(X)]` there is a measurable `A ⊆ X` with `μ(A) = r`. -/
theorem continuous_measure_space [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hc : ContinuousSpace μ) (r : ℝ≥0∞) (hr : r ≤ μ Set.univ) :
    ∃ S : Set X, MeasurableSet S ∧ μ S = r := by
  obtain ⟨S, -, hSm, hSr⟩ :=
    continuous_measure_space_subset μ hμ hc Set.univ MeasurableSet.univ r hr
  exact ⟨S, hSm, hSr⟩

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

/-! ### The `IsLinftyOf` dictionary

These elementary facts about a presentation `q : L^∞(X) → 𝒜` are shared by
**129X** below and by the **130IV** development further down (where they
were first written): closure of `IsBoundedMeasurable` under the algebraic
operations, and that `q` only sees the a.e.-class of its argument. -/

private theorem bm_const (z : ℂ) : IsBoundedMeasurable X (fun _ : X => z) :=
  ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩

private theorem bm_one : IsBoundedMeasurable X (1 : X → ℂ) := bm_const 1

private theorem bm_zero : IsBoundedMeasurable X (0 : X → ℂ) := bm_const 0

private theorem bm_nonneg {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨-, C, hC⟩ := hf
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

private theorem bm_add {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f + g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.add hgm, Cf + Cg, fun x => ?_⟩
  exact (norm_add_le (f x) (g x)).trans (add_le_add (hCf x) (hCg x))

private theorem bm_sub {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f - g) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.sub hgm, Cf + Cg, fun x => ?_⟩
  exact (norm_sub_le (f x) (g x)).trans (add_le_add (hCf x) (hCg x))

private theorem bm_mul {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : IsBoundedMeasurable X (f * g) := by
  obtain ⟨Cf, hCf0, hCf⟩ := bm_nonneg hf
  obtain ⟨Cg, hCg0, hCg⟩ := bm_nonneg hg
  refine ⟨hf.1.mul hg.1, Cf * Cg, fun x => ?_⟩
  exact (norm_mul_le (f x) (g x)).trans
    (mul_le_mul (hCf x) (hCg x) (norm_nonneg _) hCf0)

private theorem bm_star {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (star f) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  exact ⟨continuous_star.measurable.comp hfm, Cf, fun x => by simpa using hCf x⟩

private theorem bm_smul (z : ℂ) {f : X → ℂ} (hf : IsBoundedMeasurable X f) :
    IsBoundedMeasurable X (z • f) := by
  obtain ⟨C, hC0, hC⟩ := bm_nonneg hf
  refine ⟨hf.1.const_smul z, ‖z‖ * C, fun x => ?_⟩
  simpa [norm_smul] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg z)

/-- Auxiliary for **130IV**: `q` only depends on the a.e.-class of its
argument.  (This is the argument already made inline in **130II**.) -/
private theorem linfty_congr (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) (h : f =ᵐ[ν] g) : p f = p g := by
  have hsub := bm_sub hf hg
  have h0 : p (f - g) = 0 := by
    refine (hp.kernel _ hsub).mpr ?_
    filter_upwards [h] with x hx
    simp [hx]
  have hadd := hp.add (f - g) g hsub hg
  rw [sub_add_cancel, h0, zero_add] at hadd
  exact hadd

/-- Auxiliary for **130IV**: `q` is additive, hence subtractive. -/
private theorem linfty_sub (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) : p (f - g) = p f - p g := by
  have h := hp.add (f - g) g (bm_sub hf hg) hg
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

private theorem linfty_zero (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) : p 0 = 0 :=
  (hp.kernel _ bm_zero).mpr (Filter.EventuallyEq.refl _ _)

/-- Auxiliary: `q` is bipositive, first half.  (`0 ≤ z` in `ℂ` says that
`z` is a nonnegative real, so the hypothesis is "`f ≥ 0` a.e.".)  The
witness is `√f`, which is bounded measurable because `√` is. -/
private theorem linfty_nonneg (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f : X → ℂ} (hf : IsBoundedMeasurable X f)
    (h : ∀ᵐ x ∂ν, 0 ≤ f x) : 0 ≤ p f := by
  obtain ⟨C, hC0, hC⟩ := bm_nonneg hf
  set g : X → ℂ := fun x => ((Real.sqrt (f x).re : ℝ) : ℂ) with hg
  have hgm : Measurable g :=
    Complex.measurable_ofReal.comp (Complex.measurable_re.comp hf.1).sqrt
  have hgb : IsBoundedMeasurable X g := by
    refine ⟨hgm, Real.sqrt C, fun x => ?_⟩
    rw [hg]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (le_trans (Complex.re_le_norm _) (hC x))
  have hae : star g * g =ᵐ[ν] f := by
    filter_upwards [h] with x hx
    obtain ⟨hre, him⟩ := Complex.le_def.mp hx
    simp only [Complex.zero_re, Complex.zero_im] at hre him
    have h1 : (star g * g) x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.conj_mul (g x)
    rw [h1, hg]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt hre]
    exact (Complex.ext rfl (by simpa using him))
  calc (0 : 𝒞) ≤ star (p g) * p g := star_mul_self_nonneg _
    _ = p (star g * g) := by
        rw [hp.mul _ _ (bm_star hgb) hgb, hp.star_map _ hgb]
    _ = p f := linfty_congr ν 𝒞 p hp (bm_mul (bm_star hgb) hgb) hf hae

/-- Auxiliary: `q` is monotone for the a.e. order. -/
private theorem linfty_mono (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) (h : ∀ᵐ x ∂ν, f x ≤ g x) : p f ≤ p g := by
  have h0 : (0 : 𝒞) ≤ p (g - f) := by
    refine linfty_nonneg ν 𝒞 p hp (bm_sub hg hf) ?_
    filter_upwards [h] with x hx
    simpa using sub_nonneg.mpr hx
  rw [linfty_sub ν 𝒞 p hp hg hf] at h0
  exact sub_nonneg.mp h0

/-- Auxiliary: `q` is bipositive, second half — the converse of
`linfty_nonneg`.  With `S = {x | Re f(x) < 0}` and `s = 1_S`, the element
`q(s·f)` is *both* `≤ 0` (because `s·f ≤ 0` pointwise) and `≥ 0` (because
it is the compression `q(s)·q(f)·q(s)` of a positive element), hence `0`;
so `s·f` vanishes a.e., which forces `μ(S) = 0`. -/
private theorem linfty_ae_nonneg (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f : X → ℂ} (hf : IsBoundedMeasurable X f)
    (h : 0 ≤ p f) : ∀ᵐ x ∂ν, 0 ≤ f x := by
  -- `q f` is self-adjoint, so `f` is a.e. real
  have hstar : p (star f) = p f := by
    rw [hp.star_map _ hf]
    exact (IsSelfAdjoint.of_nonneg h).star_eq
  have hreal : star f - f =ᵐ[ν] 0 := by
    refine (hp.kernel _ (bm_sub (bm_star hf) hf)).mp ?_
    rw [linfty_sub ν 𝒞 p hp (bm_star hf) hf, hstar, sub_self]
  have him : ∀ᵐ x ∂ν, (f x).im = 0 := by
    filter_upwards [hreal] with x hx
    have hx' : star f x - f x = 0 := by
      simpa using hx
    have hx'' : (starRingEnd ℂ) (f x) = f x := sub_eq_zero.mp hx'
    have h2 := congrArg Complex.im hx''
    simp only [Complex.conj_im] at h2
    linarith
  -- the real part, as a bounded measurable function
  set f₀ : X → ℂ := fun x => (((f x).re : ℝ) : ℂ) with hf₀
  obtain ⟨C, hC0, hC⟩ := bm_nonneg hf
  have hf₀b : IsBoundedMeasurable X f₀ := by
    refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_re.comp hf.1), C,
      fun x => ?_⟩
    rw [hf₀]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (Complex.abs_re_le_norm _) (hC x)
  have hf₀ae : f₀ =ᵐ[ν] f := by
    filter_upwards [him] with x hx
    exact (Complex.ext rfl (by simp [hf₀, hx]))
  have hpf₀ : p f₀ = p f := linfty_congr ν 𝒞 p hp hf₀b hf hf₀ae
  -- the negative part is null
  set S : Set X := {x | (f x).re < 0} with hS
  have hSm : MeasurableSet S :=
    measurableSet_lt (Complex.measurable_re.comp hf.1) measurable_const
  set s : X → ℂ := S.indicator 1 with hs
  have hsm : Measurable s := (measurable_const : Measurable (1 : X → ℂ)).indicator hSm
  have hsb : IsBoundedMeasurable X s := by
    refine ⟨hsm, 1, fun x => ?_⟩
    by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
  have hss : s * s = s := by
    funext x; by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
  have hsstar : star s = s := by
    funext x; by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
  have hle : p (s * f₀) ≤ 0 := by
    have h1 : p (s * f₀) ≤ p 0 := by
      refine linfty_mono ν 𝒞 p hp (bm_mul hsb hf₀b) bm_zero (Filter.Eventually.of_forall ?_)
      intro x
      by_cases hx : x ∈ S
      · have : (s * f₀) x = (((f x).re : ℝ) : ℂ) := by
          simp [hs, hf₀, Set.indicator_apply, hx]
        rw [this]
        refine Complex.le_def.mpr ⟨?_, by simp⟩
        simpa using (le_of_lt (by simpa [hS] using hx))
      · simp [hs, hf₀, Set.indicator_apply, hx]
    rwa [linfty_zero ν 𝒞 p hp] at h1
  have hge : (0 : 𝒞) ≤ p (s * f₀) := by
    have hconj : p (s * f₀) = star (p s) * p f₀ * p s := by
      have h1 : s * f₀ = star s * f₀ * s := by
        rw [hsstar]
        funext x
        by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx] <;> ring
      rw [h1, hp.mul _ _ (bm_mul (bm_star hsb) hf₀b) hsb,
        hp.mul _ _ (bm_star hsb) hf₀b, hp.star_map _ hsb]
    rw [hconj, hpf₀]
    exact star_left_conjugate_nonneg h _
  have hzero : p (s * f₀) = 0 := le_antisymm hle hge
  have hae0 : s * f₀ =ᵐ[ν] 0 := (hp.kernel _ (bm_mul hsb hf₀b)).mp hzero
  have hSnull : ν S = 0 := by
    have hsub : S ⊆ {x | ¬ (s * f₀) x = (0 : X → ℂ) x} := by
      intro x hx
      have h1 : (s * f₀) x = (((f x).re : ℝ) : ℂ) := by
        simp [hs, hf₀, Set.indicator_apply, hx]
      simp only [Set.mem_setOf_eq, h1, Pi.zero_apply]
      exact fun hcon => absurd (Complex.ofReal_eq_zero.mp hcon) (ne_of_lt (by
        simpa [hS] using hx))
    exact measure_mono_null hsub (ae_iff.mp hae0)
  have hSae : ∀ᵐ x ∂ν, ¬ (f x).re < 0 := by
    rw [ae_iff]
    simpa [hS] using hSnull
  filter_upwards [him, hSae] with x h1 h2
  exact Complex.le_def.mpr ⟨by simpa using not_lt.mp h2, by simpa using h1.symm⟩

/-- Auxiliary: the converse of `linfty_mono`. -/
private theorem linfty_ae_le (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f g : X → ℂ} (hf : IsBoundedMeasurable X f)
    (hg : IsBoundedMeasurable X g) (h : p f ≤ p g) : ∀ᵐ x ∂ν, f x ≤ g x := by
  have h0 : (0 : 𝒞) ≤ p (g - f) := by
    rw [linfty_sub ν 𝒞 p hp hg hf]
    exact sub_nonneg.mpr h
  filter_upwards [linfty_ae_nonneg ν 𝒞 p hp (bm_sub hg hf) h0] with x hx
  simpa using sub_nonneg.mp hx

/-! ### Auxiliaries for **129X**

Three ingredients that the thesis's proof (proc.tex:6371) uses without
comment: normality read as preservation of *infima* (it takes
`δ(⋀ₙ qₙ) = ⋀ₙ δ(qₙ)`), the regrouping of a level-`N+1` sum into pairs,
and the dyadic partition itself. -/

omit [MeasurableSpace X] in
/-- A normal positive map preserves the infima of filtered sets of
self-adjoint elements: apply normality to `−D`.  (The same three-line
device as the private `preservesDirInfs` of `A/VN/Projections.lean`, which
is not exported.) -/
private theorem dup_preservesDirInfs {A₁ : Type*} {B₁ : Type*}
    [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
    [CStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁]
    (f : A₁ →ₚ[ℂ] B₁) (hf : PreservesDirSups ⇑f)
    (D : Set (selfAdjoint A₁)) (s : selfAdjoint A₁) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≥ ·) D) (hglb : IsGLB D s) :
    IsGLB ((fun d : selfAdjoint A₁ => f (d : A₁)) '' D) (f (s : A₁)) := by
  have hnegle : ∀ x y : selfAdjoint A₁, x ≤ y ↔ -y ≤ -x := by
    intro x y
    constructor <;> intro h <;>
      exact Subtype.coe_le_coe.mp (by
        simpa using neg_le_neg (Subtype.coe_le_coe.mpr h))
  set E : Set (selfAdjoint A₁) := (fun d : selfAdjoint A₁ => -d) '' D with hE
  have hEne : E.Nonempty := hne.image _
  have hEdir : DirectedOn (· ≤ ·) E := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzx, hzy⟩ := hdir x hx y hy
    exact ⟨-z, ⟨z, hz, rfl⟩, (hnegle z x).mp hzx, (hnegle z y).mp hzy⟩
  have hElub : IsLUB E (-s) := by
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      exact (hnegle s d).mp (hglb.1 hd)
    · intro u hu
      have h1 : ∀ d ∈ D, -u ≤ d := by
        intro d hd
        exact (hnegle (-u) d).mpr (by simpa using hu ⟨d, hd, rfl⟩)
      simpa using (hnegle (-u) s).mp (hglb.2 h1)
  have hkey := hf E (-s) hEne hEdir hElub
  have himg : (fun d : selfAdjoint A₁ => f (d : A₁)) '' E
      = (fun z : B₁ => -z) '' ((fun d : selfAdjoint A₁ => f (d : A₁)) '' D) := by
    rw [hE, ← Set.image_comp, ← Set.image_comp]
    refine Set.image_congr fun d _ => ?_
    show f ((-d : selfAdjoint A₁) : A₁) = -f (d : A₁)
    rw [show ((-d : selfAdjoint A₁) : A₁) = -(d : A₁) from rfl, map_neg]
  have hfs : f ((-s : selfAdjoint A₁) : A₁) = -f (s : A₁) := by
    rw [show ((-s : selfAdjoint A₁) : A₁) = -(s : A₁) from rfl, map_neg]
  rw [himg, hfs] at hkey
  constructor
  · rintro _ ⟨d, hd, rfl⟩
    have := hkey.1 ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa using neg_le_neg this
  · intro u hu
    have h1 : ∀ z ∈ (fun z : B₁ => -z) ''
        ((fun d : selfAdjoint A₁ => f (d : A₁)) '' D), z ≤ -u := by
      rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      exact neg_le_neg (hu ⟨d, hd, rfl⟩)
    have := hkey.2 h1
    simpa using neg_le_neg this

omit [MeasurableSpace X] in
/-- Regrouping a sum over `{0,…,2n−1}` into consecutive pairs: this is how
the level-`N+1` sum `∑_{|w|=N+1} p_w ⊗ p_w` is compared with the level-`N`
one. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (2 * n), f j
      = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have h : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      abel

/-- The **dyadic scale** behind the partition of **129X** (proc.tex:6382).
Instead of indexing the halves by words `w ∈ {1,2}*` we index the level-`N`
partition by its *initial segments*: `S N j` is the union of the first `j`
blocks of level `N`, so that the blocks themselves are the differences
`S N (j+1) ∖ S N j`, the level-`N` block `j` splits into the level-`N+1`
blocks `2j` and `2j+1` (that is the clause `S (N+1) (2i) = S N i`), and
every block of level `N` has measure `2^{-N}μ(X)`.

Each halving step is one application of `continuous_measure_space_subset`
— the thesis's `lem:continuous-measure-space`, which is where continuity
of `X` enters. -/
private theorem exists_dyadic_scale [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hc : ContinuousSpace μ) :
    ∃ S : ℕ → ℕ → Set X,
      (∀ N j, MeasurableSet (S N j)) ∧
      (∀ N j, S N j ⊆ S N (j + 1)) ∧
      (∀ N, S N 0 = ∅) ∧
      (∀ N j, 2 ^ N ≤ j → S N j = Set.univ) ∧
      (∀ N i, S (N + 1) (2 * i) = S N i) ∧
      (∀ N j, j < 2 ^ N → μ (S N (j + 1) \ S N j) * 2 ^ N = μ Set.univ) := by
  -- one halving step: a measurable set midway between `A ⊆ B`
  have hhalf : ∀ A B : Set X, MeasurableSet A → MeasurableSet B → A ⊆ B →
      ∃ C : Set X, MeasurableSet C ∧ A ⊆ C ∧ C ⊆ B ∧
        μ (C \ A) + μ (C \ A) = μ (B \ A) ∧
        μ (B \ C) + μ (B \ C) = μ (B \ A) := by
    intro A B hA hB hAB
    set r : ℝ≥0∞ := μ (B \ A) / 2 with hr
    have hrr : r + r = μ (B \ A) := ENNReal.add_halves _
    have hrle : r ≤ μ (B \ A) := by rw [← hrr]; exact le_add_self
    have hrtop : r ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ _) hrle
    obtain ⟨D, hDsub, hDm, hDr⟩ :=
      continuous_measure_space_subset μ hμ hc (B \ A) (hB.diff hA) r hrle
    refine ⟨A ∪ D, hA.union hDm, Set.subset_union_left,
      Set.union_subset hAB fun x hx => (hDsub hx).1, ?_, ?_⟩
    · have h1 : (A ∪ D) \ A = D := by
        ext x
        constructor
        · rintro ⟨hx, hxA⟩
          rcases hx with h | h
          · exact absurd h hxA
          · exact h
        · intro hx
          exact ⟨Or.inr hx, fun hxA => (hDsub hx).2 hxA⟩
      rw [h1, hDr, hrr]
    · have h2 : B \ (A ∪ D) = (B \ A) \ D := by
        ext x
        simp only [Set.mem_diff, Set.mem_union, not_or]
        tauto
      rw [h2, measure_diff hDsub hDm.nullMeasurableSet (measure_ne_top _ _), hDr,
        ← hrr, ENNReal.add_sub_cancel_right hrtop, hrr]
  choose! half hhm hhA hhB hhC1 hhC2 using hhalf
  refine ⟨fun N => Nat.rec (motive := fun _ => ℕ → Set X)
    (fun j => if j = 0 then ∅ else Set.univ)
    (fun _ T j => if j % 2 = 0 then T (j / 2) else half (T (j / 2)) (T (j / 2 + 1)))
    N, ?_⟩
  set S : ℕ → ℕ → Set X := fun N => Nat.rec (motive := fun _ => ℕ → Set X)
    (fun j => if j = 0 then ∅ else Set.univ)
    (fun _ T j => if j % 2 = 0 then T (j / 2) else half (T (j / 2)) (T (j / 2 + 1)))
    N with hSdef
  have hS0j : ∀ j, S 0 j = if j = 0 then ∅ else Set.univ := fun _ => rfl
  have hSsucc : ∀ N j, S (N + 1) j =
      if j % 2 = 0 then S N (j / 2) else half (S N (j / 2)) (S N (j / 2 + 1)) :=
    fun _ _ => rfl
  have hSeven : ∀ N i, S (N + 1) (2 * i) = S N i := by
    intro N i
    rw [hSsucc]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hSodd : ∀ N i, S (N + 1) (2 * i + 1)
      = half (S N i) (S N (i + 1)) := by
    intro N i
    rw [hSsucc]
    have h1 : (2 * i + 1) % 2 = 1 := by omega
    have h2 : (2 * i + 1) / 2 = i := by omega
    simp [h1, h2]
  -- the level-`N` invariants, all five at once
  have key : ∀ N, (∀ j, MeasurableSet (S N j)) ∧ (∀ j, S N j ⊆ S N (j + 1)) ∧
      S N 0 = ∅ ∧ (∀ j, 2 ^ N ≤ j → S N j = Set.univ) ∧
      (∀ j, j < 2 ^ N → μ (S N (j + 1) \ S N j) * 2 ^ N = μ Set.univ) := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun j => ?_, fun j => ?_, rfl, fun j hj => ?_, fun j hj => ?_⟩
        · rw [hS0j]
          split <;> simp
        · rw [hS0j, hS0j]
          split
          · simp
          · simp
        · rw [hS0j]
          have hj' : 1 ≤ j := by simpa using hj
          have hjne : j ≠ 0 := by omega
          simp [hjne]
        · have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hj)
          subst hj0
          rw [hS0j, hS0j]
          simp
    | succ N ih =>
        obtain ⟨ihm, ihmono, ih0, ihtop, ihblock⟩ := ih
        have hmeas : ∀ j, MeasurableSet (S (N + 1) j) := by
          intro j
          rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
          · rw [show j = 2 * i by omega, hSeven]; exact ihm i
          · rw [show j = 2 * i + 1 by omega, hSodd]
            exact hhm _ _ (ihm i) (ihm (i + 1)) (ihmono i)
        have hmono : ∀ j, S (N + 1) j ⊆ S (N + 1) (j + 1) := by
          intro j
          rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
          · rw [show j = 2 * i by omega, show 2 * i + 1 = 2 * i + 1 from rfl,
              hSeven, hSodd]
            exact hhA _ _ (ihm i) (ihm (i + 1)) (ihmono i)
          · rw [show j = 2 * i + 1 by omega, show 2 * i + 1 + 1 = 2 * (i + 1) by ring,
              hSodd, hSeven]
            exact hhB _ _ (ihm i) (ihm (i + 1)) (ihmono i)
        refine ⟨hmeas, hmono, ?_, ?_, ?_⟩
        · rw [show (0 : ℕ) = 2 * 0 by ring, hSeven]; exact ih0
        · intro j hj
          rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
          · rw [show j = 2 * i by omega, hSeven]
            refine ihtop i ?_
            have h2 : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
            omega
          · rw [show j = 2 * i + 1 by omega, hSodd]
            have hi' : 2 ^ N ≤ i := by
              have h2 : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
              omega
            rw [ihtop i hi', ihtop (i + 1) (le_trans hi' (Nat.le_succ i))]
            exact Set.eq_univ_of_univ_subset
              (hhA _ _ MeasurableSet.univ MeasurableSet.univ (subset_refl _))
        · intro j hj
          have hpow : (2 : ℝ≥0∞) ^ (N + 1) = 2 ^ N * 2 := by ring
          rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
          · have hji : j = 2 * i := by omega
            have hilt : i < 2 ^ N := by
              have h2 : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
              omega
            rw [hji, hSeven, show 2 * i + 1 = 2 * i + 1 from rfl, hSodd, hpow]
            have hC := hhC1 (S N i) (S N (i + 1)) (ihm i) (ihm (i + 1)) (ihmono i)
            calc μ (half (S N i) (S N (i + 1)) \ S N i) * (2 ^ N * 2)
                = (μ (half (S N i) (S N (i + 1)) \ S N i)
                    + μ (half (S N i) (S N (i + 1)) \ S N i)) * 2 ^ N := by ring
              _ = μ (S N (i + 1) \ S N i) * 2 ^ N := by rw [hC]
              _ = μ Set.univ := ihblock i hilt
          · have hji : j = 2 * i + 1 := by omega
            have hilt : i < 2 ^ N := by
              have h2 : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
              omega
            rw [hji, hSodd, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, hSeven, hpow]
            have hC := hhC2 (S N i) (S N (i + 1)) (ihm i) (ihm (i + 1)) (ihmono i)
            calc μ (S N (i + 1) \ half (S N i) (S N (i + 1))) * (2 ^ N * 2)
                = (μ (S N (i + 1) \ half (S N i) (S N (i + 1)))
                    + μ (S N (i + 1) \ half (S N i) (S N (i + 1)))) * 2 ^ N := by ring
              _ = μ (S N (i + 1) \ S N i) * 2 ^ N := by rw [hC]
              _ = μ Set.univ := ihblock i hilt
  exact ⟨fun N j => (key N).1 j, fun N j => (key N).2.1 j, fun N => (key N).2.2.1,
    fun N j hj => (key N).2.2.2.1 j hj, hSeven,
    fun N j hj => (key N).2.2.2.2 j hj⟩

/-- **129X** (`lem:continuous-finite-measure-space-not-duplicable`,
proc.tex:6363, Lemma): if `X` is a continuous finite complete measure
space for which `L^∞(X)` is duplicable, then `μ(X) = 0`. -/
theorem continuous_finite_measure_space_not_duplicable
    [IsFiniteMeasure μ] (hμ : μ.IsComplete) (hc : ContinuousSpace μ)
    (𝒜 : Type u) [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [VonNeumannAlgebra 𝒜] (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q)
    (hd : Duplicable 𝒜) : μ Set.univ = 0 := by
  classical
  by_contra hpos
  obtain ⟨d⟩ := hd
  ---- (0) the indicator dictionary -------------------------------------
  have hindbm : ∀ T : Set X, MeasurableSet T →
      IsBoundedMeasurable X (T.indicator (1 : X → ℂ)) := by
    intro T hT
    refine ⟨(measurable_const : Measurable (1 : X → ℂ)).indicator hT, 1, fun x => ?_⟩
    by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  obtain ⟨qi, hqi⟩ : ∃ f : Set X → 𝒜, ∀ T, f T = q (T.indicator (1 : X → ℂ)) :=
    ⟨_, fun _ => rfl⟩
  have hqiuniv : qi Set.univ = 1 := by
    rw [hqi, show (Set.univ : Set X).indicator (1 : X → ℂ) = 1 by funext x; simp]
    exact hq.one
  have hqiempty : qi (∅ : Set X) = 0 := by
    rw [hqi, show (∅ : Set X).indicator (1 : X → ℂ) = 0 by funext x; simp]
    exact linfty_zero μ 𝒜 q hq
  have hqiproj : ∀ T : Set X, MeasurableSet T → IsStarProjection (qi T) := by
    intro T hT
    refine ⟨?_, ?_⟩
    · show qi T * qi T = qi T
      rw [hqi, ← hq.mul _ _ (hindbm T hT) (hindbm T hT)]
      congr 1
      funext x
      by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
    · show star (qi T) = qi T
      rw [hqi, ← hq.star_map _ (hindbm T hT)]
      congr 1
      funext x
      by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  have hqinonneg : ∀ T : Set X, MeasurableSet T → (0 : 𝒜) ≤ qi T :=
    fun T hT => (hqiproj T hT).nonneg
  have hqimono : ∀ T T' : Set X, MeasurableSet T → MeasurableSet T' → T ⊆ T' →
      qi T ≤ qi T' := by
    intro T T' hT hT' hsub
    rw [hqi, hqi]
    refine linfty_mono μ 𝒜 q hq (hindbm T hT) (hindbm T' hT')
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ T
    · simp [Set.indicator_apply, hx, hsub hx]
    · by_cases hx' : x ∈ T' <;> simp [Set.indicator_apply, hx, hx']
  have hqidiff : ∀ T T' : Set X, MeasurableSet T → MeasurableSet T' → T ⊆ T' →
      qi T' - qi T = qi (T' \ T) := by
    intro T T' hT hT' hsub
    rw [hqi, hqi, hqi, ← linfty_sub μ 𝒜 q hq (hindbm T' hT') (hindbm T hT)]
    congr 1
    funext x
    by_cases hx : x ∈ T
    · simp [Set.indicator_apply, hx, hsub hx, Set.mem_diff]
    · by_cases hx' : x ∈ T' <;> simp [Set.indicator_apply, hx, hx', Set.mem_diff]
  ---- (1) `𝒜` is nontrivial, and carries a nonzero np-functional -------
  have hone : (1 : 𝒜) ≠ 0 := by
    intro h0
    refine hpos ?_
    have h1 : q (1 : X → ℂ) = 0 := by rw [hq.one, h0]
    have h2 := ae_iff.mp ((hq.kernel 1 bm_one).mp h1)
    have h3 : {x : X | ¬ (1 : X → ℂ) x = (0 : X → ℂ) x} = Set.univ := by
      ext x; simp
    rwa [h3] at h2
  haveI : Nontrivial 𝒜 := ⟨⟨1, 0, hone⟩⟩
  obtain ⟨ω, hω1⟩ : ∃ ω : NPFunctional 𝒜, ω 1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hone (VonNeumannAlgebra.np_faithful 1 zero_le_one hcon)
  have hωre : ∀ a : 𝒜, 0 ≤ a → (ω a : ℂ) = (((ω a).re : ℝ) : ℂ) := by
    intro a ha
    obtain ⟨-, h2⟩ := Complex.le_def.mp (npFunctional_nonneg ω ha)
    simp only [Complex.zero_im] at h2
    exact Complex.ext (by simp) (by simp [← h2])
  have hωnn : ∀ a : 𝒜, 0 ≤ a → 0 ≤ (ω a).re := by
    intro a ha
    obtain ⟨h1, -⟩ := Complex.le_def.mp (npFunctional_nonneg ω ha)
    simpa using h1
  ---- (2) absolute continuity of `ω` ------------------------------------
  -- The thesis takes for `ω` the *integral* state `μ(X)⁻¹∫·dμ`, for which
  -- `ω(p_w) = 2^{-#w}` is immediate; that state is normal by `Linfty-vn`
  -- (**51IX**), which is still `sorry` in the tree.  We take instead an
  -- arbitrary non-zero np-functional and get the decay of `ω(p_w)` from
  -- normality directly, in the form of absolute continuity.
  have habs : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ T : Set X, MeasurableSet T →
      μ T * 2 ^ n ≤ μ Set.univ → (ω (qi T)).re ≤ ε := by
    intro ε hε
    by_contra hcon
    push_neg at hcon
    choose T hTm hTμ hTω using hcon
    -- the sets `T n` are small, so their tails have null intersection
    have h2ne : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ n) ≠ 0 := fun n => by
      simp [pow_ne_zero]
    have h2top : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ n) ≠ ⊤ := fun n => by
      simp [ENNReal.pow_ne_top]
    have hTle : ∀ n, μ (T n) ≤ μ Set.univ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
      intro n
      calc μ (T n) = μ (T n) * 2 ^ n * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel (h2ne n) (h2top n), mul_one]
        _ ≤ μ Set.univ * ((2 : ℝ≥0∞) ^ n)⁻¹ := by gcongr; exact hTμ n
        _ = μ Set.univ * ((2 : ℝ≥0∞)⁻¹) ^ n := by rw [ENNReal.inv_pow]
    have hsum : ∑' n, μ (T n) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hTle)
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
      exact ENNReal.mul_ne_top (measure_ne_top μ _) (by simp)
    obtain ⟨U, hU⟩ : ∃ U : ℕ → Set X, ∀ N, U N = ⋃ k, T (k + N) :=
      ⟨_, fun _ => rfl⟩
    have hUm : ∀ N, MeasurableSet (U N) := by
      intro N; rw [hU]; exact MeasurableSet.iUnion fun k => hTm _
    have hUanti : ∀ N, U (N + 1) ⊆ U N := by
      intro N
      rw [hU, hU]
      refine Set.iUnion_subset fun k => ?_
      refine Set.subset_iUnion_of_subset (k + 1) ?_
      rw [show k + 1 + N = k + (N + 1) by ring]
    have hUle : ∀ N, μ (U N) ≤ ∑' k, μ (T (k + N)) := by
      intro N; rw [hU]; exact measure_iUnion_le _
    have hUnull : μ (⋂ N, U N) = 0 := by
      refine le_antisymm ?_ (by simp)
      refine ge_of_tendsto (ENNReal.tendsto_sum_nat_add (fun n => μ (T n)) hsum) ?_
      refine Filter.Eventually.of_forall fun N => ?_
      exact le_trans (measure_mono (Set.iInter_subset _ N)) (hUle N)
    -- their projections have infimum `0`, so `ω(qi (U N)) → 0`
    have hglb : IsGLB {x : selfAdjoint 𝒜 | ∃ N, (x : 𝒜) = qi (U N)}
        (0 : selfAdjoint 𝒜) := by
      constructor
      · rintro x ⟨N, hN⟩
        exact Subtype.coe_le_coe.mp (by rw [hN]; exact hqinonneg _ (hUm N))
      · intro b hb
        refine Subtype.coe_le_coe.mp ?_
        obtain ⟨g, hgbm, hgq⟩ := hq.surj (b : 𝒜)
        have hgle : ∀ N, ∀ᵐ x ∂μ, g x ≤ (U N).indicator (1 : X → ℂ) x := by
          intro N
          refine linfty_ae_le μ 𝒜 q hq hgbm (hindbm _ (hUm N)) ?_
          rw [hgq, ← hqi]
          exact hb (show (⟨qi (U N), (hqiproj _ (hUm N)).isSelfAdjoint⟩ :
            selfAdjoint 𝒜) ∈ {x : selfAdjoint 𝒜 | ∃ N, (x : 𝒜) = qi (U N)} from ⟨N, rfl⟩)
        have hall : ∀ᵐ x ∂μ, ∀ N, g x ≤ (U N).indicator (1 : X → ℂ) x :=
          ae_all_iff.mpr hgle
        have hgle0 : ∀ᵐ x ∂μ, g x ≤ (0 : X → ℂ) x := by
          have hint : ∀ᵐ x ∂μ, x ∉ ⋂ N, U N := by
            rw [ae_iff]
            have hset : {x : X | ¬ (x ∉ ⋂ N, U N)} = ⋂ N, U N := by
              ext x; simp
            rw [hset]
            exact hUnull
          filter_upwards [hall, hint] with x hx hxi
          obtain ⟨N, hN⟩ : ∃ N, x ∉ U N := by
            by_contra hcon2
            push_neg at hcon2
            exact hxi (Set.mem_iInter.mpr hcon2)
          have := hx N
          simpa [Set.indicator_apply, hN] using this
        have := linfty_mono μ 𝒜 q hq hgbm bm_zero hgle0
        rw [hgq, linfty_zero μ 𝒜 q hq] at this
        simpa using this
    have hne : ({x : selfAdjoint 𝒜 | ∃ N, (x : 𝒜) = qi (U N)}).Nonempty :=
      ⟨⟨qi (U 0), (hqiproj _ (hUm 0)).isSelfAdjoint⟩, ⟨0, rfl⟩⟩
    have hdir : DirectedOn (· ≥ ·) {x : selfAdjoint 𝒜 | ∃ N, (x : 𝒜) = qi (U N)} := by
      rintro x ⟨N, hN⟩ y ⟨M, hM⟩
      have hmono : ∀ N M : ℕ, N ≤ M → U M ⊆ U N := by
        intro N M h
        induction M with
        | zero => simpa using (by omega : N = 0) ▸ subset_rfl
        | succ K ih =>
            rcases Nat.lt_or_ge N (K + 1) with h1 | h1
            · exact (hUanti K).trans (ih (by omega))
            · have : N = K + 1 := by omega
              subst this
              exact subset_rfl
      refine ⟨⟨qi (U (max N M)), (hqiproj _ (hUm _)).isSelfAdjoint⟩, ⟨max N M, rfl⟩,
        ?_, ?_⟩
      · exact Subtype.coe_le_coe.mp (by
          rw [hN]
          exact hqimono _ _ (hUm _) (hUm _) (hmono N (max N M) (le_max_left _ _)))
      · exact Subtype.coe_le_coe.mp (by
          rw [hM]
          exact hqimono _ _ (hUm _) (hUm _) (hmono M (max N M) (le_max_right _ _)))
    have himg := dup_preservesDirInfs ω.toPositiveLinearMap ω.preservesDirSups' _ _
      hne hdir hglb
    -- but every `ω(qi (U N))` is `> ε`
    have hlow : ((ε : ℝ) : ℂ) ∈ lowerBounds
        ((fun x : selfAdjoint 𝒜 => (ω.toPositiveLinearMap (x : 𝒜) : ℂ)) ''
          {x : selfAdjoint 𝒜 | ∃ N, (x : 𝒜) = qi (U N)}) := by
      rintro _ ⟨x, ⟨N, hN⟩, rfl⟩
      have h1 : (ω (qi (T N)) : ℂ).re ≤ (ω (qi (U N))).re := by
        have := npFunctional_mono ω (hqimono (T N) (U N) (hTm N) (hUm N) (by
          rw [hU]
          exact Set.subset_iUnion_of_subset 0 (by simp)))
        exact (Complex.le_def.mp this).1
      have h2 : ε ≤ (ω (qi (U N))).re := le_of_lt (lt_of_lt_of_le (hTω N) h1)
      have h3 : (ω (qi (U N)) : ℂ) = (((ω (qi (U N))).re : ℝ) : ℂ) :=
        hωre _ (hqinonneg _ (hUm N))
      show ((ε : ℝ) : ℂ) ≤ ω.toPositiveLinearMap (x : 𝒜)
      rw [show (ω.toPositiveLinearMap (x : 𝒜) : ℂ) = ω (qi (U N)) by rw [hN]; rfl, h3]
      exact Complex.le_def.mpr ⟨by simpa using h2, by simp⟩
    have hfin := himg.2 hlow
    have : ((ε : ℝ) : ℂ) ≤ 0 := by
      simpa using hfin
    have := (Complex.le_def.mp this).1
    simp only [Complex.ofReal_re, Complex.zero_re] at this
    linarith
  ---- (3) the dyadic partition ------------------------------------------
  obtain ⟨S, hSm, hSmono, hS0, hStop, hSref, hSblock⟩ := exists_dyadic_scale μ hμ hc
  obtain ⟨e, he⟩ : ∃ f : ℕ → ℕ → 𝒜, ∀ N j, f N j = qi (S N j) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ f : ℕ → ℕ → 𝒜, ∀ N j, f N j = e N (j + 1) - e N j :=
    ⟨_, fun _ _ => rfl⟩
  have hpind : ∀ N j, p N j = qi (S N (j + 1) \ S N j) := by
    intro N j
    rw [hp, he, he]
    exact hqidiff _ _ (hSm N j) (hSm N (j + 1)) (hSmono N j)
  have hpproj : ∀ N j, IsStarProjection (p N j) := by
    intro N j
    rw [hpind]
    exact hqiproj _ ((hSm N (j + 1)).diff (hSm N j))
  have hpnonneg : ∀ N j, (0 : 𝒜) ≤ p N j := fun N j => (hpproj N j).nonneg
  have hpsum : ∀ N, ∑ j ∈ Finset.range (2 ^ N), p N j = 1 := by
    intro N
    have h := Finset.sum_range_sub (f := fun j => e N j) (n := 2 ^ N)
    simp only [← hp] at h
    rw [h, he, he, hS0 N, hStop N (2 ^ N) le_rfl, hqiuniv, hqiempty, sub_zero]
  have hpsplit : ∀ N i, p N i = p (N + 1) (2 * i) + p (N + 1) (2 * i + 1) := by
    intro N i
    have h1 : S (N + 1) (2 * i) = S N i := hSref N i
    have h2 : S (N + 1) (2 * i + 1 + 1) = S N (i + 1) := by
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring]
      exact hSref N (i + 1)
    simp only [hp, he, h1, h2]
    abel
  have hpsmall : ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ j < 2 ^ N, (ω (p N j)).re ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := habs ε hε
    refine ⟨n, fun j hj => ?_⟩
    rw [hpind]
    refine hn _ ((hSm n (j + 1)).diff (hSm n j)) ?_
    exact le_of_eq (hSblock n j hj)
  ---- (4) the descending sequence `q_N` ----------------------------------
  obtain ⟨Q, hQ⟩ : ∃ f : ℕ → VNT 𝒜 𝒜,
      ∀ N, f N = ∑ j ∈ Finset.range (2 ^ N), (p N j ⊗ᵥ p N j) := ⟨_, fun _ => rfl⟩
  have hQnonneg : ∀ N, (0 : VNT 𝒜 𝒜) ≤ Q N := by
    intro N
    rw [hQ]
    exact Finset.sum_nonneg fun j _ => vtmul_nonneg _ _ (hpnonneg N j) (hpnonneg N j)
  have hQsa : ∀ N, IsSelfAdjoint (Q N) := fun N => IsSelfAdjoint.of_nonneg (hQnonneg N)
  have hQ0 : Q 0 = 1 := by
    rw [hQ]
    have h1 : ∑ j ∈ Finset.range (2 ^ 0), p 0 j = 1 := hpsum 0
    simp only [pow_zero, Finset.sum_range_one] at h1 ⊢
    rw [h1]
    exact (show ((1 : 𝒜) ⊗ᵥ (1 : 𝒜)) = (1 : VNT 𝒜 𝒜) from
      (vnTensor 𝒜 𝒜).isTensorProduct.miu.1)
  have hQanti : ∀ N, Q (N + 1) ≤ Q N := by
    intro N
    have h1 : (2 : ℕ) ^ (N + 1) = 2 * 2 ^ N := by ring
    rw [hQ, hQ, h1, sum_range_two_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : (0 : 𝒜) ≤ p (N + 1) (2 * i) := hpnonneg _ _
    have hb : (0 : 𝒜) ≤ p (N + 1) (2 * i + 1) := hpnonneg _ _
    have hexp : p N i ⊗ᵥ p N i
        = ((p (N + 1) (2 * i) ⊗ᵥ p (N + 1) (2 * i))
            + (p (N + 1) (2 * i + 1) ⊗ᵥ p (N + 1) (2 * i + 1)))
          + ((p (N + 1) (2 * i) ⊗ᵥ p (N + 1) (2 * i + 1))
            + (p (N + 1) (2 * i + 1) ⊗ᵥ p (N + 1) (2 * i))) := by
      simp only [vtmul]
      rw [hpsplit N i, map_add]
      simp only [LinearMap.add_apply, map_add]
      abel
    rw [hexp]
    exact le_add_of_nonneg_right
      (add_nonneg (vtmul_nonneg _ _ ha hb) (vtmul_nonneg _ _ hb ha))
  have hQanti' : ∀ N M : ℕ, N ≤ M → Q M ≤ Q N := by
    intro N M h
    induction M with
    | zero => simpa using (by omega : N = 0) ▸ le_rfl
    | succ K ih =>
        rcases Nat.lt_or_ge N (K + 1) with h1 | h1
        · exact (hQanti K).trans (ih (by omega))
        · have : N = K + 1 := by omega
          subst this
          exact le_rfl
  ---- (5) `δ(q_N) = 1` and `(ω⊗ω)(q_N) ≤ ε·ω(1)` -------------------------
  have hδmul := (uniqueness_duplicator d).2
  have hδQ : ∀ N, d.δ (Q N) = 1 := by
    intro N
    rw [hQ, map_sum]
    have : ∀ j ∈ Finset.range (2 ^ N), d.δ (p N j ⊗ᵥ p N j) = p N j := by
      intro j _
      rw [hδmul, (hpproj N j).isIdempotentElem.eq]
    rw [Finset.sum_congr rfl this, hpsum N]
  set χ : NPFunctional (VNT 𝒜 𝒜) := prodNP (vnTensor 𝒜 𝒜).isTensorProduct ω ω with hχdef
  have hχtmul : ∀ a b : 𝒜, χ (a ⊗ᵥ b) = ω a * ω b :=
    fun a b => prodNP_apply (vnTensor 𝒜 𝒜).isTensorProduct ω ω a b
  have hχQ : ∀ N, (χ (Q N) : ℂ)
      = ((∑ j ∈ Finset.range (2 ^ N), (ω (p N j)).re * (ω (p N j)).re : ℝ) : ℂ) := by
    intro N
    rw [hQ, show (χ (∑ j ∈ Finset.range (2 ^ N), (p N j ⊗ᵥ p N j)) : ℂ)
        = ∑ j ∈ Finset.range (2 ^ N), (χ (p N j ⊗ᵥ p N j) : ℂ) from
      map_sum χ.toPositiveLinearMap _ _]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hχtmul]
    conv_lhs => rw [hωre _ (hpnonneg N j)]
  have hωsum : ∀ N, ∑ j ∈ Finset.range (2 ^ N), (ω (p N j)).re = (ω 1).re := by
    intro N
    have h : (ω (∑ j ∈ Finset.range (2 ^ N), p N j) : ℂ)
        = ∑ j ∈ Finset.range (2 ^ N), (ω (p N j) : ℂ) :=
      map_sum ω.toPositiveLinearMap _ _
    rw [hpsum N] at h
    have h2 := congrArg Complex.re h
    simpa using h2.symm
  ---- (6) the infimum ----------------------------------------------------
  obtain ⟨Qi, hQi⟩ : ∃ i : selfAdjoint (VNT 𝒜 𝒜),
      IsGLB {x : selfAdjoint (VNT 𝒜 𝒜) | ∃ N, (x : VNT 𝒜 𝒜) = Q N} i := by
    refine infima_in_vna _ ⟨⟨Q 0, hQsa 0⟩, ⟨0, rfl⟩⟩ ?_ ⟨(0 : selfAdjoint (VNT 𝒜 𝒜)), ?_⟩
    · rintro x ⟨N, hN⟩ y ⟨M, hM⟩
      refine ⟨⟨Q (max N M), hQsa _⟩, ⟨max N M, rfl⟩, ?_, ?_⟩
      · exact Subtype.coe_le_coe.mp (by rw [hN]; exact hQanti' _ _ (le_max_left N M))
      · exact Subtype.coe_le_coe.mp (by rw [hM]; exact hQanti' _ _ (le_max_right N M))
    · rintro x ⟨N, hN⟩
      exact Subtype.coe_le_coe.mp (by rw [hN]; exact hQnonneg N)
  have hQine : ({x : selfAdjoint (VNT 𝒜 𝒜) | ∃ N, (x : VNT 𝒜 𝒜) = Q N}).Nonempty :=
    ⟨⟨Q 0, hQsa 0⟩, ⟨0, rfl⟩⟩
  have hQidir : DirectedOn (· ≥ ·)
      {x : selfAdjoint (VNT 𝒜 𝒜) | ∃ N, (x : VNT 𝒜 𝒜) = Q N} := by
    rintro x ⟨N, hN⟩ y ⟨M, hM⟩
    refine ⟨⟨Q (max N M), hQsa _⟩, ⟨max N M, rfl⟩, ?_, ?_⟩
    · exact Subtype.coe_le_coe.mp (by rw [hN]; exact hQanti' _ _ (le_max_left N M))
    · exact Subtype.coe_le_coe.mp (by rw [hM]; exact hQanti' _ _ (le_max_right N M))
  have hQile : ∀ N, (Qi : VNT 𝒜 𝒜) ≤ Q N := by
    intro N
    exact Subtype.coe_le_coe.mpr (hQi.1 (show (⟨Q N, hQsa N⟩ : selfAdjoint (VNT 𝒜 𝒜))
      ∈ {x : selfAdjoint (VNT 𝒜 𝒜) | ∃ N, (x : VNT 𝒜 𝒜) = Q N} from ⟨N, rfl⟩))
  have hQinn : (0 : VNT 𝒜 𝒜) ≤ (Qi : VNT 𝒜 𝒜) := by
    have h : (0 : selfAdjoint (VNT 𝒜 𝒜)) ≤ Qi := by
      refine hQi.2 ?_
      rintro x ⟨N, hN⟩
      exact Subtype.coe_le_coe.mp (by rw [hN]; exact hQnonneg N)
    simpa using Subtype.coe_le_coe.mpr h
  ---- (7) `δ(q) = 1` -----------------------------------------------------
  have hδQi : d.δ (Qi : VNT 𝒜 𝒜) = 1 := by
    have hglb := dup_preservesDirInfs d.δ d.normal _ Qi hQine hQidir hQi
    refine le_antisymm ?_ ?_
    · have h : d.δ (Qi : VNT 𝒜 𝒜) ≤ d.δ (Q 0) :=
        hglb.1 ⟨⟨Q 0, hQsa 0⟩, ⟨0, rfl⟩, rfl⟩
      rwa [hδQ 0] at h
    · refine hglb.2 ?_
      rintro _ ⟨x, ⟨N, hN⟩, rfl⟩
      show (1 : 𝒜) ≤ d.δ (x : VNT 𝒜 𝒜)
      rw [hN, hδQ N]
  ---- (8) `(ω⊗ω)(q) = 0` -------------------------------------------------
  have hχnn : (0 : ℂ) ≤ χ (Qi : VNT 𝒜 𝒜) := npFunctional_nonneg χ hQinn
  have hχ0 : (χ (Qi : VNT 𝒜 𝒜) : ℂ) = 0 := by
    have hc0 : 0 ≤ (ω 1).re := hωnn 1 zero_le_one
    have hre : (χ (Qi : VNT 𝒜 𝒜)).re ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨N, hN⟩ := hpsmall (δ / ((ω 1).re + 1)) (by positivity)
      have h1 : (χ (Qi : VNT 𝒜 𝒜)).re ≤ (χ (Q N)).re := by
        have := npFunctional_mono χ (hQile N)
        exact (Complex.le_def.mp this).1
      have h2 : (χ (Q N)).re
          = ∑ j ∈ Finset.range (2 ^ N), (ω (p N j)).re * (ω (p N j)).re := by
        rw [hχQ N]
        simp
      have h3 : ∑ j ∈ Finset.range (2 ^ N), (ω (p N j)).re * (ω (p N j)).re
          ≤ (δ / ((ω 1).re + 1)) * ∑ j ∈ Finset.range (2 ^ N), (ω (p N j)).re := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j < 2 ^ N := Finset.mem_range.mp hj
        exact mul_le_mul_of_nonneg_right (hN j hj') (hωnn _ (hpnonneg N j))
      rw [hωsum N] at h3
      have h4 : (δ / ((ω 1).re + 1)) * (ω 1).re ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      have := h1.trans (le_of_eq h2)
      linarith [this.trans (h3.trans h4)]
    have h5 : 0 ≤ (χ (Qi : VNT 𝒜 𝒜)).re := (Complex.le_def.mp hχnn).1.trans_eq (by simp)
    have h6 : (χ (Qi : VNT 𝒜 𝒜)).re = 0 := le_antisymm hre (by simpa using h5)
    have h7 : (χ (Qi : VNT 𝒜 𝒜)).im = 0 := by
      have := (Complex.le_def.mp hχnn).2
      simpa using this.symm
    exact Complex.ext (by simpa using h6) (by simpa using h7)
  ---- (9) the contradiction ----------------------------------------------
  have hcarrier : npCarrier χ = npCarrier ω ⊗ᵥ npCarrier ω :=
    carrier_tensor_4 ω ω χ hχtmul
  have hceille : ceil (Qi : VNT 𝒜 𝒜) ≤ 1 - npCarrier χ := by
    have hc : ceil ((χ.toPositiveLinearMap) (ceil (Qi : VNT 𝒜 𝒜))) = 0 := by
      rw [← ncp_ceil χ.toPositiveLinearMap χ.preservesDirSups' _ hQinn]
      rw [show (χ.toPositiveLinearMap (Qi : VNT 𝒜 𝒜) : ℂ) = 0 from hχ0, ceil_zero]
    have hfc : (χ.toPositiveLinearMap (ceil (Qi : VNT 𝒜 𝒜)) : ℂ) = 0 :=
      (ceil_basic_3 _ (npFunctional_nonneg χ (ceil_spec hQinn).1.nonneg)).mpr hc
    have hle : npCarrier χ ≤ 1 - ceil (Qi : VNT 𝒜 𝒜) := by
      refine (carrier_spec χ.toPositiveLinearMap χ.preservesDirSups').2.2 _
        (ceil_spec hQinn).1.one_sub ?_
      rwa [sub_sub_cancel]
    exact le_sub_comm.mp hle
  have hQile1 : (Qi : VNT 𝒜 𝒜) ≤ 1 - npCarrier χ := by
    refine le_trans ?_ hceille
    -- `q ≤ ⌈q⌉` for the effect `q`
    have heff : (Qi : VNT 𝒜 𝒜) ≤ 1 := le_trans (hQile 0) (le_of_eq hQ0)
    obtain ⟨hp1, hac, -⟩ := ceil_spec hQinn
    have hca : ceil (Qi : VNT 𝒜 𝒜) * (Qi : VNT 𝒜 𝒜) = (Qi : VNT 𝒜 𝒜) := by
      have h := congrArg star hac
      rwa [star_mul, hp1.isSelfAdjoint.star_eq,
        (IsSelfAdjoint.of_nonneg hQinn).star_eq] at h
    calc (Qi : VNT 𝒜 𝒜) = ceil (Qi : VNT 𝒜 𝒜) * (Qi : VNT 𝒜 𝒜) * ceil (Qi : VNT 𝒜 𝒜) := by
          rw [hca, hac]
      _ ≤ ceil (Qi : VNT 𝒜 𝒜) * 1 * ceil (Qi : VNT 𝒜 𝒜) :=
          IsSelfAdjoint.conjugate_le_conjugate heff hp1.isSelfAdjoint
      _ = ceil (Qi : VNT 𝒜 𝒜) := by rw [mul_one, hp1.isIdempotentElem.eq]
  have hone11 : ((1 : 𝒜) ⊗ᵥ (1 : 𝒜)) = (1 : VNT 𝒜 𝒜) :=
    (vnTensor 𝒜 𝒜).isTensorProduct.miu.1
  have hδ1 : d.δ (1 : VNT 𝒜 𝒜) = 1 := by
    rw [← hone11]
    exact (unit_duplicator d).2
  have hωproj : IsStarProjection (npCarrier ω) :=
    (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').1
  have hfinal : (1 : 𝒜) ≤ 1 - npCarrier ω := by
    calc (1 : 𝒜) = d.δ (Qi : VNT 𝒜 𝒜) := hδQi.symm
      _ ≤ d.δ (1 - npCarrier χ) := OrderHomClass.mono d.δ hQile1
      _ = d.δ 1 - d.δ (npCarrier χ) := map_sub d.δ _ _
      _ = 1 - npCarrier ω := by
          rw [hδ1, hcarrier, hδmul, hωproj.isIdempotentElem.eq]
  have hcω : npCarrier ω = 0 := by
    have h : (1 : 𝒜) - 1 ≤ (1 - npCarrier ω) - 1 := sub_le_sub_right hfinal 1
    rw [sub_self] at h
    have h2 : (0 : 𝒜) ≤ -npCarrier ω := by
      calc (0 : 𝒜) ≤ 1 - npCarrier ω - 1 := h
        _ = -npCarrier ω := by abel
    exact le_antisymm (neg_nonneg.mp h2) hωproj.nonneg
  refine hω1 ?_
  have h : (ω (1 - npCarrier ω) : ℂ) = 0 :=
    (carrier_spec ω.toPositiveLinearMap ω.preservesDirSups').2.1
  rwa [hcω, sub_zero] at h

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

/-! ### Auxiliaries for **130IV**

proc.tex:6518 is a bare Exercise: the thesis gives no argument, so what
follows is ours.  The isomorphism itself is the obvious one,
`q f ↦ (q_{Pₙ} f)ₙ`, and the only real work is that `IsLinftyOf` records
*no* norm information — it says `q` is a surjective ∗-algebra map whose
kernel is the a.e.-zero functions, and nothing else.  Both directions of
the missing dictionary are needed:

* `linfty_norm_le` (a pointwise bound on `f` bounds `‖q f‖`) makes the
  family `(q_{Pₙ} f)ₙ` a member of `ℓ^∞(ℬ)`;
* `linfty_ae_bound` (its converse: `‖q f‖ ≤ M` forces `‖f‖ ≤ M` a.e.) is
  what makes the map *surjective* — the representatives `fₙ` of a given
  `y ∈ ℓ^∞(ℬ)` have to be glued into one *bounded* function on `X`, and
  for that they must be uniformly bounded, which is exactly the converse
  bound.  It is proved by the usual argument: if `‖f‖ > M + ε` on a set
  `S` of positive measure then `p := q 1_S` is a nonzero projection with
  `(M+ε)²p ≤ (q f · p)^* (q f · p)`, whence `(M+ε)² ≤ ‖q f‖² ≤ M²`. -/

/-- Auxiliary for **130IV**: a function that vanishes a.e. on each member
of a countable measurable cover vanishes a.e. -/
private theorem ae_of_ae_restrict_cover (ν : Measure X) (P : ℕ → Set X)
    (hcover : Set.univ ⊆ ⋃ n, P n)
    {f : X → ℂ} (hf : Measurable f)
    (h : ∀ n, f =ᵐ[ν.restrict (P n)] 0) : f =ᵐ[ν] 0 := by
  rw [Filter.EventuallyEq, ae_iff]
  set T : Set X := {x | ¬ f x = (0 : X → ℂ) x} with hT
  have hTm : MeasurableSet T := by
    have : T = f ⁻¹' {0}ᶜ := by ext x; simp [hT]
    rw [this]
    exact hf (measurableSet_singleton 0).compl
  have hsub : T ⊆ ⋃ n, T ∩ P n := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨n, hx, hn⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  have h1 := ae_iff.mp (h n)
  rwa [Measure.restrict_apply hTm] at h1

/-- Auxiliary for **130IV**, the easy half of the norm dictionary: a
pointwise bound on `f` bounds `‖q f‖`.  The proof is the C*-algebraic
form of `|f|² ≤ C²`: the function `√(C² − |f|²)` is again bounded
measurable, so `(q f)^*(q f) + (q h)^*(q h) = C²·1` in `𝒞`. -/
private theorem linfty_norm_le (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] [Nontrivial 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f : X → ℂ} (hf : IsBoundedMeasurable X f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) : ‖p f‖ ≤ C := by
  set h : X → ℂ := fun x => ((Real.sqrt (C ^ 2 - ‖f x‖ ^ 2) : ℝ) : ℂ) with hhdef
  have hhm : Measurable h :=
    Complex.measurable_ofReal.comp (measurable_const.sub (hf.1.norm.pow_const 2)).sqrt
  have hnn : ∀ x, 0 ≤ C ^ 2 - ‖f x‖ ^ 2 := fun x => by
    have := hC x
    nlinarith [norm_nonneg (f x)]
  have hhb : IsBoundedMeasurable X h := by
    refine ⟨hhm, C, fun x => ?_⟩
    rw [hhdef]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (C ^ 2 - ‖f x‖ ^ 2) ≤ Real.sqrt (C ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖f x‖])
      _ = C := Real.sqrt_sq hC0
  -- the pointwise identity `f^*f + h^*h = C²·1`
  have hid : star f * f + star h * h = ((C ^ 2 : ℝ) : ℂ) • (1 : X → ℂ) := by
    funext x
    have h1 : (star f * f) x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.conj_mul (f x)
    have h2 : (star h * h) x = ((C ^ 2 - ‖f x‖ ^ 2 : ℝ) : ℂ) := by
      have : (star h * h) x = ((‖h x‖ ^ 2 : ℝ) : ℂ) := by
        simpa using RCLike.conj_mul (h x)
      rw [this, hhdef]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt (hnn x)]
    simp only [Pi.add_apply, h1, h2, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
      mul_one, ← Complex.ofReal_add]
    ring_nf
  have happ := congrArg p hid
  rw [hp.add _ _ (bm_mul (bm_star hf) hf) (bm_mul (bm_star hhb) hhb),
    hp.mul _ _ (bm_star hf) hf, hp.mul _ _ (bm_star hhb) hhb,
    hp.star_map _ hf, hp.star_map _ hhb, hp.smul _ _ bm_one, hp.one] at happ
  have hle : star (p f) * p f ≤ ((C ^ 2 : ℝ) : ℂ) • (1 : 𝒞) := by
    rw [← happ]
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)
  have hnorm : ‖p f‖ * ‖p f‖ ≤ C ^ 2 := by
    have h1 : ‖star (p f) * p f‖ ≤ ‖((C ^ 2 : ℝ) : ℂ) • (1 : 𝒞)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg _) hle
    rw [CStarRing.norm_star_mul_self] at h1
    refine h1.trans ?_
    rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (p f)]

/-- Auxiliary for **130IV**: `(f^* f)(x) = |f(x)|²`. -/
private theorem star_mul_apply (u : X → ℂ) (x : X) :
    (star u * u) x = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
  simpa using RCLike.conj_mul (u x)

/-- Auxiliary for **130IV**, the hard half of the norm dictionary and the
one thing the construction cannot do without: `‖q f‖ ≤ M` forces
`|f| ≤ M` almost everywhere. -/
private theorem linfty_ae_bound (ν : Measure X) (𝒞 : Type u) [CStarAlgebra 𝒞]
    [PartialOrder 𝒞] [StarOrderedRing 𝒞] [Nontrivial 𝒞] (p : (X → ℂ) → 𝒞)
    (hp : IsLinftyOf ν 𝒞 p) {f : X → ℂ} (hf : IsBoundedMeasurable X f)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ‖p f‖ ≤ M) : ∀ᵐ x ∂ν, ‖f x‖ ≤ M := by
  -- for each `ε > 0` the set `{|f| ≥ M + ε}` is null
  have key : ∀ ε : ℝ, 0 < ε → ν {x | M + ε ≤ ‖f x‖} = 0 := by
    intro ε hε
    set c : ℝ := M + ε with hc
    have hc0 : 0 < c := by positivity
    set S : Set X := {x | c ≤ ‖f x‖} with hS
    have hSm : MeasurableSet S := measurableSet_le measurable_const hf.1.norm
    set s : X → ℂ := S.indicator 1 with hs
    have hsm : Measurable s := (measurable_const : Measurable (1 : X → ℂ)).indicator hSm
    have hsb : IsBoundedMeasurable X s := by
      refine ⟨hsm, 1, fun x => ?_⟩
      by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
    by_contra hne
    -- `P := q 1_S` is a nonzero projection
    have hss : s * s = s := by
      funext x; by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
    have hsstar : star s = s := by
      funext x; by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
    set P : 𝒞 := p s with hP
    have hPP : P * P = P := by rw [hP, ← hp.mul _ _ hsb hsb, hss]
    have hPstar : star P = P := by rw [hP, ← hp.star_map _ hsb, hsstar]
    have hPne : P ≠ 0 := by
      intro h0
      refine hne ?_
      have hae := (hp.kernel _ hsb).mp h0
      have hset : {x | ¬ s x = (0 : X → ℂ) x} = S := by
        ext x
        by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
      have h2 := ae_iff.mp hae
      rwa [hset] at h2
    have hPnorm : ‖P‖ = 1 := by
      have h1 : ‖P‖ * ‖P‖ = 1 * ‖P‖ := by
        rw [one_mul, ← CStarRing.norm_star_mul_self, hPstar, hPP]
      exact mul_right_cancel₀ (fun h => hPne (norm_eq_zero.mp h)) h1
    -- the pointwise identity `(f·1_S)^*(f·1_S) = c²·1_S + w^*w`
    set w : X → ℂ :=
      fun x => ((Real.sqrt (max 0 (‖f x‖ ^ 2 - c ^ 2)) : ℝ) : ℂ) * s x with hw
    have hwm : Measurable w :=
      (Complex.measurable_ofReal.comp
        (measurable_const.max ((hf.1.norm.pow_const 2).sub measurable_const)).sqrt).mul hsm
    have hwb : IsBoundedMeasurable X w := by
      obtain ⟨C, hC0, hC⟩ := bm_nonneg hf
      refine ⟨hwm, Real.sqrt (max 0 (C ^ 2 - c ^ 2)) * 1, fun x => ?_⟩
      rw [hw]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      refine mul_le_mul (Real.sqrt_le_sqrt ?_) ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
      · exact max_le_max le_rfl (by nlinarith [norm_nonneg (f x), hC x])
      · by_cases hx : x ∈ S <;> simp [hs, Set.indicator_apply, hx]
    have hu : IsBoundedMeasurable X (f * s) := bm_mul hf hsb
    have hid : star (f * s) * (f * s) = ((c ^ 2 : ℝ) : ℂ) • s + star w * w := by
      funext x
      rw [star_mul_apply, Pi.add_apply, star_mul_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ S
      · have hfx : c ≤ ‖f x‖ := hx
        have hsx : s x = 1 := by simp [hs, hx]
        have hmax : max 0 (‖f x‖ ^ 2 - c ^ 2) = ‖f x‖ ^ 2 - c ^ 2 :=
          max_eq_right (by nlinarith)
        have hwx : ‖w x‖ = Real.sqrt (‖f x‖ ^ 2 - c ^ 2) := by
          rw [hw]
          simp [hsx, hmax, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hfsx : ‖(f * s) x‖ = ‖f x‖ := by simp [hsx]
        rw [hwx, hfsx, hsx, Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ ‖f x‖ ^ 2 - c ^ 2)]
        push_cast
        ring
      · have hsx : s x = 0 := by simp [hs, Set.indicator_apply, hx]
        have hwx : w x = 0 := by rw [hw]; simp [hsx]
        have hfsx : (f * s) x = 0 := by simp [hsx]
        rw [hwx, hfsx, hsx]
        simp
    have happ := congrArg p hid
    rw [hp.mul _ _ (bm_star hu) hu, hp.star_map _ hu,
      hp.add _ _ (bm_smul _ hsb) (bm_mul (bm_star hwb) hwb),
      hp.smul _ _ hsb, hp.mul _ _ (bm_star hwb) hwb, hp.star_map _ hwb,
      hp.mul _ _ hf hsb, ← hP] at happ
    -- `c²·P ≤ (q f · P)^* (q f · P)`, so `c² ≤ ‖q f‖² ≤ M²`
    have hnn : (0 : 𝒞) ≤ ((c ^ 2 : ℝ) : ℂ) • P := by
      have hsq : ((c ^ 2 : ℝ) : ℂ) • P = star (((c : ℝ) : ℂ) • P) * (((c : ℝ) : ℂ) • P) := by
        rw [star_smul, mul_smul_comm, smul_mul_assoc, hPstar, hPP, smul_smul]
        norm_num [Complex.conj_ofReal, ← Complex.ofReal_mul, sq]
      rw [hsq]
      exact star_mul_self_nonneg _
    have hge : ((c ^ 2 : ℝ) : ℂ) • P ≤ star (p f * P) * (p f * P) := by
      rw [happ]
      exact le_add_of_nonneg_right (star_mul_self_nonneg _)
    have h1 : ‖((c ^ 2 : ℝ) : ℂ) • P‖ ≤ ‖star (p f * P) * (p f * P)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hge
    rw [CStarRing.norm_star_mul_self, norm_smul, hPnorm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : ‖p f * P‖ ≤ M := by
      refine (norm_mul_le _ _).trans ?_
      rw [hPnorm, mul_one]
      exact hM
    nlinarith [norm_nonneg (p f * P)]
  rw [ae_iff]
  have hsub : {x | ¬ ‖f x‖ ≤ M} ⊆ ⋃ k : ℕ, {x | M + 1 / (k + 1 : ℝ) ≤ ‖f x‖} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, not_le] at hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < ‖f x‖ - M by linarith)
    exact Set.mem_iUnion.mpr ⟨k, by simp only [Set.mem_ofPred_eq]; linarith⟩
  exact measure_mono_null hsub
    (measure_iUnion_null fun k => key _ (by positivity))


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
    ∃ φ : NMIUMap 𝒜 (lp ℬ ∞), Function.Bijective ⇑φ := by
  classical
  -- a representative for each class
  have hrepex : ∀ a : 𝒜, ∃ f, IsBoundedMeasurable X f ∧ q f = a := hq.surj
  have hrepBM : ∀ a, IsBoundedMeasurable X (hrepex a).choose :=
    fun a => (hrepex a).choose_spec.1
  have hrepq : ∀ a, q ((hrepex a).choose) = a := fun a => (hrepex a).choose_spec.2
  set rep : 𝒜 → (X → ℂ) := fun a => (hrepex a).choose with hrepdef
  -- the components do not depend on the chosen representative
  have hwd : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
      q f = q g → ∀ n, qB n f = qB n g := by
    intro f g hf hg h n
    have h0 : q (f - g) = 0 := by rw [linfty_sub _ _ _ hq hf hg, h, sub_self]
    have hae : (f - g) =ᵐ[μ] 0 := (hq.kernel _ (bm_sub hf hg)).mp h0
    refine linfty_congr _ _ _ (hqB n) hf hg (ae_restrict_of_ae ?_)
    filter_upwards [hae] with x hx
    have hx' : f x - g x = 0 := hx
    exact sub_eq_zero.mp hx'
  -- the family `(q_{Pₙ} f)ₙ` is uniformly bounded, hence lies in `ℓ^∞(ℬ)`
  have hmem : ∀ f, IsBoundedMeasurable X f → Memℓp (fun n => qB n f) ∞ := by
    intro f hf
    obtain ⟨C, hC0, hC⟩ := bm_nonneg hf
    refine memℓp_infty ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact linfty_norm_le _ _ _ (hqB n) hf hC0 hC
  obtain ⟨Φ, hΦapp⟩ : ∃ Φ : 𝒜 → lp ℬ ∞,
      ∀ (a : 𝒜) (n : ℕ), (Φ a : ∀ n, ℬ n) n = qB n (rep a) :=
    ⟨fun a => ⟨fun n => qB n (rep a), hmem _ (hrepBM a)⟩, fun _ _ => rfl⟩
  have hΦrep : ∀ (a : 𝒜) (f : X → ℂ), IsBoundedMeasurable X f → q f = a →
      ∀ n, (Φ a : ∀ n, ℬ n) n = qB n f := fun a f hf hfa n =>
    (hΦapp a n).trans (hwd _ _ (hrepBM a) hf ((hrepq a).trans hfa.symm) n)
  -- `Φ` is a unital ∗-algebra map
  have hΦadd : ∀ a b, Φ (a + b) = Φ a + Φ b := by
    intro a b
    refine lp.ext ?_
    funext n
    rw [lp.coeFn_add, Pi.add_apply,
      hΦrep (a + b) (rep a + rep b) (bm_add (hrepBM a) (hrepBM b))
        (by rw [hq.add _ _ (hrepBM a) (hrepBM b), hrepq, hrepq]) n,
      hΦapp, hΦapp, (hqB n).add _ _ (hrepBM a) (hrepBM b)]
  have hΦmul : ∀ a b, Φ (a * b) = Φ a * Φ b := by
    intro a b
    refine lp.ext ?_
    funext n
    rw [lp.infty_coeFn_mul, Pi.mul_apply,
      hΦrep (a * b) (rep a * rep b) (bm_mul (hrepBM a) (hrepBM b))
        (by rw [hq.mul _ _ (hrepBM a) (hrepBM b), hrepq, hrepq]) n,
      hΦapp, hΦapp, (hqB n).mul _ _ (hrepBM a) (hrepBM b)]
  have hΦstar : ∀ a, Φ (star a) = star (Φ a) := by
    intro a
    refine lp.ext ?_
    funext n
    rw [lp.coeFn_star, Pi.star_apply,
      hΦrep (star a) (star (rep a)) (bm_star (hrepBM a))
        (by rw [hq.star_map _ (hrepBM a), hrepq]) n,
      hΦapp, (hqB n).star_map _ (hrepBM a)]
  have hΦone : Φ 1 = 1 := by
    refine lp.ext ?_
    funext n
    rw [lp.infty_coeFn_one, Pi.one_apply,
      hΦrep 1 1 bm_one hq.one n, (hqB n).one]
  have hΦzero : Φ 0 = 0 := by
    refine lp.ext ?_
    funext n
    have h0 : q (0 : X → ℂ) = 0 := (hq.kernel _ bm_zero).mpr (by rfl)
    rw [lp.coeFn_zero, Pi.zero_apply, hΦrep 0 0 bm_zero h0 n,
      (hqB n).kernel _ bm_zero |>.mpr (by rfl)]
  have hΦsmul : ∀ (c : ℂ) (a : 𝒜), Φ (c • a) = c • Φ a := by
    intro c a
    refine lp.ext ?_
    funext n
    rw [lp.coeFn_smul, Pi.smul_apply,
      hΦrep (c • a) (c • rep a) (bm_smul c (hrepBM a))
        (by rw [hq.smul _ _ (hrepBM a), hrepq]) n,
      hΦapp, (hqB n).smul _ _ (hrepBM a)]
  -- injectivity: a class killed on every block is null on every block
  have hinj : Function.Injective Φ := by
    intro a b hab
    have hcomp : ∀ n, qB n (rep a) = qB n (rep b) := by
      intro n
      have h := congrArg (fun z : lp ℬ ∞ => (z : ∀ n, ℬ n) n) hab
      simpa only [hΦapp] using h
    have hae : (rep a - rep b) =ᵐ[μ] 0 := by
      refine ae_of_ae_restrict_cover μ P hcover
        (bm_sub (hrepBM a) (hrepBM b)).1 fun n => ?_
      refine ((hqB n).kernel _ (bm_sub (hrepBM a) (hrepBM b))).mp ?_
      rw [linfty_sub _ _ _ (hqB n) (hrepBM a) (hrepBM b), hcomp n, sub_self]
    have h0 : q (rep a - rep b) = 0 := (hq.kernel _ (bm_sub (hrepBM a) (hrepBM b))).mpr hae
    rw [linfty_sub _ _ _ hq (hrepBM a) (hrepBM b), hrepq, hrepq, sub_eq_zero] at h0
    exact h0
  -- surjectivity: this is where the uniform bound on the representatives is used
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨M, hM⟩ := memℓp_infty_iff.mp y.2
    have hMn : ∀ n, ‖(y : ∀ n, ℬ n) n‖ ≤ M := fun n => hM (Set.mem_range_self n)
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMn 0)
    choose g hgBM hgy using fun n => (hqB n).surj ((y : ∀ n, ℬ n) n)
    have hgae : ∀ n, ∀ᵐ x ∂(μ.restrict (P n)), ‖g n x‖ ≤ M := fun n =>
      linfty_ae_bound _ _ _ (hqB n) (hgBM n) hM0 (by rw [hgy n]; exact hMn n)
    have hex : ∀ x, ∃ n, x ∈ P n := fun x =>
      Set.mem_iUnion.mp (hcover (Set.mem_univ x))
    -- glue the (truncated) representatives into one bounded measurable function
    set F : ℕ → X → ℂ := fun n x => if ‖g n x‖ ≤ M then g n x else 0 with hFdef
    have hFm : ∀ n, Measurable (F n) := fun n =>
      Measurable.ite (measurableSet_le (hgBM n).1.norm measurable_const)
        (hgBM n).1 measurable_const
    have hFb : ∀ n x, ‖F n x‖ ≤ M := by
      intro n x
      by_cases h : ‖g n x‖ ≤ M
      · simpa [hFdef, h] using h
      · simpa [hFdef, h] using hM0
    obtain ⟨f, hfm, hfeq⟩ : ∃ f : X → ℂ, Measurable f ∧
        ∀ (n : ℕ) (x : X), x ∈ P n → f x = F n x := by
      set Q : ℕ → X → Prop := fun n x => x ∈ P n with hQ
      haveI : ∀ n, DecidablePred (Q n) := fun n => Classical.decPred _
      have hQm : ∀ n, MeasurableSet {x | Q n x} := hmeas
      have hexQ : ∀ x, ∃ n, Q n x := hex
      refine ⟨_, Measurable.find hFm hQm hexQ, ?_⟩
      intro n x hx
      have hfind : Nat.find (hexQ x) = n := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) (Nat.find_spec (hexQ x)) hx
      rw [hfind]
    have hfBM : IsBoundedMeasurable X f := by
      refine ⟨hfm, M, fun x => ?_⟩
      obtain ⟨n, hn⟩ := hex x
      rw [hfeq n x hn]
      exact hFb n x
    -- on `Pₙ` the glued function is (a.e.) the `n`-th representative
    have hfg : ∀ n, f =ᵐ[μ.restrict (P n)] g n := by
      intro n
      have hmemP : ∀ᵐ x ∂(μ.restrict (P n)), x ∈ P n :=
        ae_restrict_of_forall_mem (hmeas n) fun x hx => hx
      filter_upwards [hgae n, hmemP] with x hbd hxP
      rw [hfeq n x hxP]
      simp [hFdef, hbd]
    refine ⟨q f, lp.ext ?_⟩
    funext n
    rw [hΦrep (q f) f hfBM rfl n,
      linfty_congr _ _ _ (hqB n) hfBM (hgBM n) (hfg n), hgy n]
  -- normality is free: a bijective ∗-homomorphism is an order isomorphism
  obtain ⟨Ψ, hΨbij⟩ : ∃ Ψ : 𝒜 →⋆ₐ[ℂ] lp ℬ ∞, Function.Bijective ⇑Ψ :=
    ⟨{ toFun := Φ
       map_one' := hΦone
       map_mul' := hΦmul
       map_zero' := hΦzero
       map_add' := hΦadd
       commutes' := fun c => by
         rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
           hΦsmul, hΦone]
       map_star' := hΦstar }, ⟨hinj, hsurj⟩⟩
  exact ⟨{ toStarAlgHom := Ψ
           preservesDirSups' :=
             starAlgEquiv_preservesDirSups' (StarAlgEquiv.ofBijective Ψ hΨbij) },
    hΨbij⟩

/-- **130V** (`cor:discrete-ell-x`, proc.tex:6525, Corollary): for a
discrete measure space `X` with `μ(X) < ∞` there is a set `Y` with
`L^∞(X) ≅ ℓ^∞(Y)`.

Against the **repaired** 129II.2 (`DiscreteSpace`, the author's ruling of
2026-08-16); under the printed definition this corollary is **false**,
see the counterexample recorded there.  The index set `Y` is the
partition itself, which is why the partition form of the definition was
chosen: no exhaustion argument is needed to produce it.

**Divergence from the printed proof.**  proc.tex:6525 reads "combine
**130IV** with **130II**": partition `X` into atoms, decompose
`L^∞(X) ≅ ⊕ₙ L^∞(Aₙ)`, and turn each `L^∞(Aₙ)` into `ℂ`.  That route is
*not* available in this rendering, for a reason of formalization rather
than mathematics: `measure_space_partition` (130IV) is stated for a
partition indexed by `ℕ` with each block algebra `ℬₙ` **nontrivial**, and
a discrete space may have a *finite* partition into atoms — padding it
out to `ℕ` with `∅` forces `ℬₙ = {0}` there (the `kernel` field makes
`qB 1 = 0`), which the `Nontrivial` hypothesis forbids.  So the argument
is run directly over the index set `↥𝒬`: the block algebras are `ℂ` (this
is 130II's content, and its key lemma `ae_const_of_atomic` is what is
reused), and `Φ a` records the a.e.-constant value of `a` on each atom.
Everything else — gluing representatives with `Measurable.find`,
normality via `starAlgEquiv_preservesDirSups'` — is 130IV's own argument
specialised to `ℬₙ = ℂ`, where the norm dictionary (`linfty_norm_le`,
`linfty_ae_bound`) becomes unnecessary: the value on an atom is attained,
so a pointwise bound on `f` bounds it directly.

`hμ : μ.IsComplete` is not used. -/
theorem discrete_ell_x [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hd : DiscreteSpace μ) (𝒜 : Type u) [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q) :
    ∃ (Y : Type u) (φ : NMIUMap 𝒜 (linf Y)), Function.Bijective ⇑φ := by
  classical
  obtain ⟨𝒬, hat, hdisj, hcov⟩ := hd
  have hcount : 𝒬.Countable := atom_family_countable μ hat hdisj
  haveI hfin : ∀ A : Set X, IsFiniteMeasure (μ.restrict A) := fun A =>
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top μ A⟩
  -- each block is an atom for the measure restricted to it
  have hatr : ∀ A ∈ 𝒬, AtomicSet (μ.restrict A) Set.univ := by
    intro A hA
    obtain ⟨hAm, hApos, hAat⟩ := hat A hA
    refine ⟨MeasurableSet.univ, by rwa [Measure.restrict_apply_univ], ?_⟩
    intro S' _ hS'm hS'pos
    rw [Measure.restrict_apply hS'm] at hS'pos ⊢
    rw [Measure.restrict_apply_univ]
    exact hAat _ Set.inter_subset_right (hS'm.inter hAm) hS'pos
  -- 130II's key lemma: on an atom every bounded measurable `f` is a.e. constant
  have hval : ∀ A ∈ 𝒬, ∀ f : X → ℂ, IsBoundedMeasurable X f →
      ∃ z : ℂ, ∀ᵐ x ∂(μ.restrict A), f x = z := by
    intro A hA f hf
    obtain ⟨z, hz⟩ := ae_const_of_atomic (μ.restrict A) (hatr A hA) f hf
    exact ⟨z, hz⟩
  choose! cval hcval using hval
  have hrpos : ∀ A ∈ 𝒬, μ.restrict A ≠ 0 := by
    intro A hA h
    have h1 := (hat A hA).2.1
    rw [← Measure.restrict_apply_univ, h] at h1
    simp at h1
  have huniq : ∀ A ∈ 𝒬, ∀ (f : X → ℂ) (z : ℂ), IsBoundedMeasurable X f →
      (∀ᵐ x ∂(μ.restrict A), f x = z) → cval A f = z := by
    intro A hA f z hf hz
    haveI : (ae (μ.restrict A)).NeBot := ae_neBot.mpr (hrpos A hA)
    obtain ⟨x, hx1, hx2⟩ := ((hcval A hA f hf).and hz).exists
    rw [← hx1, hx2]
  -- the value on an atom is attained, so pointwise bounds carry over
  have hbound : ∀ A ∈ 𝒬, ∀ (f : X → ℂ) (C : ℝ), IsBoundedMeasurable X f →
      (∀ x, ‖f x‖ ≤ C) → ‖cval A f‖ ≤ C := by
    intro A hA f C hf hC
    haveI : (ae (μ.restrict A)).NeBot := ae_neBot.mpr (hrpos A hA)
    obtain ⟨x, hx⟩ := (hcval A hA f hf).exists
    rw [← hx]
    exact hC x
  have hcvcongr : ∀ A ∈ 𝒬, ∀ f g : X → ℂ, IsBoundedMeasurable X f →
      IsBoundedMeasurable X g → f =ᵐ[μ] g → cval A f = cval A g := by
    intro A hA f g hf hg h
    refine huniq A hA f _ hf ?_
    filter_upwards [ae_restrict_of_ae h, hcval A hA g hg] with x h1 h2
    rw [h1, h2]
  have hcvconst : ∀ A ∈ 𝒬, ∀ z : ℂ, cval A (fun _ => z) = z := fun A hA z =>
    huniq A hA _ z (bm_const z) (Filter.Eventually.of_forall fun _ => rfl)
  have hcvadd : ∀ A ∈ 𝒬, ∀ f g : X → ℂ, IsBoundedMeasurable X f →
      IsBoundedMeasurable X g → cval A (f + g) = cval A f + cval A g := by
    intro A hA f g hf hg
    refine huniq A hA _ _ (bm_add hf hg) ?_
    filter_upwards [hcval A hA f hf, hcval A hA g hg] with x h1 h2
    show f x + g x = _
    rw [h1, h2]
  have hcvmul : ∀ A ∈ 𝒬, ∀ f g : X → ℂ, IsBoundedMeasurable X f →
      IsBoundedMeasurable X g → cval A (f * g) = cval A f * cval A g := by
    intro A hA f g hf hg
    refine huniq A hA _ _ (bm_mul hf hg) ?_
    filter_upwards [hcval A hA f hf, hcval A hA g hg] with x h1 h2
    show f x * g x = _
    rw [h1, h2]
  have hcvstar : ∀ A ∈ 𝒬, ∀ f : X → ℂ, IsBoundedMeasurable X f →
      cval A (star f) = star (cval A f) := by
    intro A hA f hf
    refine huniq A hA _ _ (bm_star hf) ?_
    filter_upwards [hcval A hA f hf] with x h1
    show star (f x) = _
    rw [h1]
  have hcvsmul : ∀ A ∈ 𝒬, ∀ (z : ℂ) (f : X → ℂ), IsBoundedMeasurable X f →
      cval A (z • f) = z • cval A f := by
    intro A hA z f hf
    refine huniq A hA _ _ (bm_smul z hf) ?_
    filter_upwards [hcval A hA f hf] with x h1
    show z • f x = _
    rw [h1]
  -- an `ℕ`-enumeration of the (countable) partition, padded with `∅`
  obtain ⟨g, hg𝒬, hgcov⟩ : ∃ g : ℕ → Set X, (∀ n, g n = ∅ ∨ g n ∈ 𝒬) ∧
      Set.univ ⊆ ⋃ n, g n := by
    rcases Set.eq_empty_or_nonempty 𝒬 with h | h
    · refine ⟨fun _ => ∅, fun _ => Or.inl rfl, ?_⟩
      rw [← hcov, h]
      simp
    · obtain ⟨g, hg⟩ := hcount.exists_eq_range h
      refine ⟨g, fun n => Or.inr (hg ▸ Set.mem_range_self n), ?_⟩
      rw [← hcov, hg, Set.sUnion_range]
  have hcover_ae : ∀ f : X → ℂ, Measurable f →
      (∀ A ∈ 𝒬, f =ᵐ[μ.restrict A] 0) → f =ᵐ[μ] 0 := by
    intro f hf h
    refine ae_of_ae_restrict_cover μ g hgcov hf fun n => ?_
    rcases hg𝒬 n with he | hn
    · rw [he, Measure.restrict_empty]
      simp [Filter.EventuallyEq]
    · exact h _ hn
  -- representatives, as in 130IV
  have hrepex : ∀ a : 𝒜, ∃ f, IsBoundedMeasurable X f ∧ q f = a := hq.surj
  have hrepBM : ∀ a, IsBoundedMeasurable X (hrepex a).choose :=
    fun a => (hrepex a).choose_spec.1
  have hrepq : ∀ a, q ((hrepex a).choose) = a := fun a => (hrepex a).choose_spec.2
  set rep : 𝒜 → (X → ℂ) := fun a => (hrepex a).choose with hrepdef
  have hmemb : ∀ f, IsBoundedMeasurable X f →
      Memℓp (fun A : ↥𝒬 => cval (A : Set X) f) ∞ := by
    intro f hf
    obtain ⟨C, hC0, hC⟩ := bm_nonneg hf
    refine memℓp_infty ⟨C, ?_⟩
    rintro _ ⟨A, rfl⟩
    exact hbound (A : Set X) A.2 f C hf hC
  obtain ⟨Φ, hΦapp⟩ : ∃ Φ : 𝒜 → linf ↥𝒬,
      ∀ (a : 𝒜) (A : ↥𝒬), (Φ a : ∀ _ : ↥𝒬, ℂ) A = cval (A : Set X) (rep a) :=
    ⟨fun a => ⟨fun A => cval (A : Set X) (rep a), hmemb _ (hrepBM a)⟩, fun _ _ => rfl⟩
  have hΦrep : ∀ (a : 𝒜) (f : X → ℂ), IsBoundedMeasurable X f → q f = a →
      ∀ A : ↥𝒬, (Φ a : ∀ _ : ↥𝒬, ℂ) A = cval (A : Set X) f := by
    intro a f hf hfa A
    rw [hΦapp]
    have h0 : q (rep a - f) = 0 := by
      rw [linfty_sub _ _ _ hq (hrepBM a) hf, hrepq, hfa, sub_self]
    have hae : (rep a - f) =ᵐ[μ] 0 := (hq.kernel _ (bm_sub (hrepBM a) hf)).mp h0
    refine hcvcongr _ A.2 _ _ (hrepBM a) hf ?_
    filter_upwards [hae] with x hx
    have hx' : rep a x - f x = 0 := hx
    exact sub_eq_zero.mp hx'
  -- `Φ` is a unital ∗-algebra map
  have hΦadd : ∀ a b, Φ (a + b) = Φ a + Φ b := by
    intro a b
    refine lp.ext ?_
    funext A
    rw [lp.coeFn_add, Pi.add_apply,
      hΦrep (a + b) (rep a + rep b) (bm_add (hrepBM a) (hrepBM b))
        (by rw [hq.add _ _ (hrepBM a) (hrepBM b), hrepq, hrepq]) A,
      hΦapp, hΦapp, hcvadd _ A.2 _ _ (hrepBM a) (hrepBM b)]
  have hΦmul : ∀ a b, Φ (a * b) = Φ a * Φ b := by
    intro a b
    refine lp.ext ?_
    funext A
    rw [lp.infty_coeFn_mul, Pi.mul_apply,
      hΦrep (a * b) (rep a * rep b) (bm_mul (hrepBM a) (hrepBM b))
        (by rw [hq.mul _ _ (hrepBM a) (hrepBM b), hrepq, hrepq]) A,
      hΦapp, hΦapp, hcvmul _ A.2 _ _ (hrepBM a) (hrepBM b)]
  have hΦstar : ∀ a, Φ (star a) = star (Φ a) := by
    intro a
    refine lp.ext ?_
    funext A
    rw [lp.coeFn_star, Pi.star_apply,
      hΦrep (star a) (star (rep a)) (bm_star (hrepBM a))
        (by rw [hq.star_map _ (hrepBM a), hrepq]) A,
      hΦapp, hcvstar _ A.2 _ (hrepBM a)]
  have hΦone : Φ 1 = 1 := by
    refine lp.ext ?_
    funext A
    rw [lp.infty_coeFn_one, Pi.one_apply, hΦrep 1 1 bm_one hq.one A]
    exact hcvconst _ A.2 1
  have hΦzero : Φ 0 = 0 := by
    refine lp.ext ?_
    funext A
    have h0 : q (0 : X → ℂ) = 0 := (hq.kernel _ bm_zero).mpr (by rfl)
    rw [lp.coeFn_zero, Pi.zero_apply, hΦrep 0 0 bm_zero h0 A]
    exact hcvconst _ A.2 0
  have hΦsmul : ∀ (c : ℂ) (a : 𝒜), Φ (c • a) = c • Φ a := by
    intro c a
    refine lp.ext ?_
    funext A
    rw [lp.coeFn_smul, Pi.smul_apply,
      hΦrep (c • a) (c • rep a) (bm_smul c (hrepBM a))
        (by rw [hq.smul _ _ (hrepBM a), hrepq]) A,
      hΦapp, hcvsmul _ A.2 _ _ (hrepBM a)]
  -- injectivity: agreeing on every atom is agreeing almost everywhere
  have hinj : Function.Injective Φ := by
    intro a b hab
    have hcomp : ∀ A ∈ 𝒬, cval A (rep a) = cval A (rep b) := by
      intro A hA
      have h := congrArg (fun z : linf ↥𝒬 => (z : ∀ _ : ↥𝒬, ℂ) ⟨A, hA⟩) hab
      simpa only [hΦapp] using h
    have hae : (rep a - rep b) =ᵐ[μ] 0 := by
      refine hcover_ae _ (bm_sub (hrepBM a) (hrepBM b)).1 fun A hA => ?_
      filter_upwards [hcval A hA (rep a) (hrepBM a),
        hcval A hA (rep b) (hrepBM b)] with x h1 h2
      show rep a x - rep b x = 0
      rw [h1, h2, hcomp A hA, sub_self]
    have h0 : q (rep a - rep b) = 0 :=
      (hq.kernel _ (bm_sub (hrepBM a) (hrepBM b))).mpr hae
    rw [linfty_sub _ _ _ hq (hrepBM a) (hrepBM b), hrepq, hrepq, sub_eq_zero] at h0
    exact h0
  -- surjectivity: a bounded family of values glues to a bounded measurable function
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨M, hM⟩ := memℓp_infty_iff.mp y.2
    set M' : ℝ := max M 0 with hM'
    have hM'0 : 0 ≤ M' := le_max_right _ _
    have hMy : ∀ A : ↥𝒬, ‖(y : ∀ _ : ↥𝒬, ℂ) A‖ ≤ M' :=
      fun A => le_trans (hM (Set.mem_range_self A)) (le_max_left _ _)
    set c : ℕ → ℂ := fun n =>
      if h : g n ∈ 𝒬 then (y : ∀ _ : ↥𝒬, ℂ) ⟨g n, h⟩ else 0 with hc
    have hcM : ∀ n, ‖c n‖ ≤ M' := by
      intro n
      by_cases h : g n ∈ 𝒬
      · simpa [hc, h] using hMy ⟨g n, h⟩
      · simpa [hc, h] using hM'0
    have hexQ : ∀ x, ∃ n, x ∈ g n := fun x =>
      Set.mem_iUnion.mp (hgcov (Set.mem_univ x))
    have hQm : ∀ n, MeasurableSet {x | x ∈ g n} := by
      intro n
      rcases hg𝒬 n with he | hn
      · simpa [he] using MeasurableSet.empty
      · exact (hat _ hn).1
    set F : ℕ → X → ℂ := fun n _ => c n with hF
    have hFm : ∀ n, Measurable (F n) := fun n => measurable_const
    set f : X → ℂ := fun x => F (Nat.find (hexQ x)) x with hf
    have hfm : Measurable f := Measurable.find hFm hQm hexQ
    have hfBM : IsBoundedMeasurable X f := ⟨hfm, M', fun x => hcM _⟩
    have hfval : ∀ (A : Set X) (hA : A ∈ 𝒬), ∀ x ∈ A,
        f x = (y : ∀ _ : ↥𝒬, ℂ) ⟨A, hA⟩ := by
      intro A hA x hxA
      have hxn : x ∈ g (Nat.find (hexQ x)) := Nat.find_spec (hexQ x)
      have hgn : g (Nat.find (hexQ x)) ∈ 𝒬 := by
        rcases hg𝒬 (Nat.find (hexQ x)) with he | hn
        · exact absurd (he ▸ hxn) (Set.notMem_empty x)
        · exact hn
      have hgA : g (Nat.find (hexQ x)) = A := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hgn hA hne) hxn hxA
      have : (⟨g (Nat.find (hexQ x)), hgn⟩ : ↥𝒬) = ⟨A, hA⟩ := Subtype.ext hgA
      simp only [hf, hF, hc, dif_pos hgn]
      rw [this]
    refine ⟨q f, lp.ext ?_⟩
    funext A
    rw [hΦrep (q f) f hfBM rfl A]
    refine huniq (A : Set X) A.2 f _ hfBM ?_
    refine ae_restrict_of_forall_mem (hat (A : Set X) A.2).1 fun x hx => ?_
    have := hfval (A : Set X) A.2 x hx
    simpa using this
  -- normality is free: a bijective ∗-homomorphism is an order isomorphism
  obtain ⟨Ψ, hΨbij⟩ : ∃ Ψ : 𝒜 →⋆ₐ[ℂ] linf ↥𝒬, Function.Bijective ⇑Ψ :=
    ⟨{ toFun := Φ
       map_one' := hΦone
       map_mul' := hΦmul
       map_zero' := hΦzero
       map_add' := hΦadd
       commutes' := fun c => by
         rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
           hΦsmul, hΦone]
       map_star' := hΦstar }, ⟨hinj, hsurj⟩⟩
  exact ⟨↥𝒬, { toStarAlgHom := Ψ
               preservesDirSups' :=
                 starAlgEquiv_preservesDirSups' (StarAlgEquiv.ofBijective Ψ hΨbij) },
    hΨbij⟩

end MeasureTheory

/-! ## The `L^∞` presentation of a commutative von Neumann algebra

`IsLinftyOf` (above) is what **129X** and **130V** consume, and the thesis
gets it from **54XI** (`cvn-faithful`): a commutative von Neumann algebra
with a faithful np-functional *is* an `L^∞`.  54XI.1 (`cvn_faithful_1`,
`A/VN/Basic.lean`) supplies the measure — finite and complete, on the
σ-algebra of almost clopen subsets of `spec 𝒞`, with the null sets exactly
the meagre ones — but not the quotient map `q`, because 54XI's own statement
of it (`f ↦ f°` is an nmiu-isomorphism `C(spec 𝒞) → L^∞(spec 𝒞)`) is not
rendered: `L^∞` has no Mathlib carrier (cf. **51IX** `Linfty_vn`, still
`sorry`).  This section builds `q`.

The one piece of mathematics needed is that **every bounded measurable
function on `spec 𝒞` agrees almost everywhere with a *continuous* one**.
54XI.2 (`cvn_faithful_2`) gives only that it is continuous at almost every
point, which is not enough to name an element of `𝒞`; the construction here
is the classical one from the clopen representatives `Cᵣ = clRep {f < r}`
(`r` rational) of the sublevel sets, `g(x) = inf {r : x ∈ Cᵣ}`, and it is
extremal disconnectedness of `spec 𝒞` (through `clRep`) that makes it work.
Uniqueness of the continuous representative is Baire: two continuous
functions differing on a meagre set differ on an open meagre set. -/

section ContRep

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [ExtremallyDisconnected X] [MeasurableSpace X]

/-- The clopen representative is monotone. -/
private theorem clRep_mono {s t : Set X} (hs : AlmostClopen s) (ht : AlmostClopen t)
    (hst : s ⊆ t) : clRep s ⊆ clRep t := by
  have hmeagre : IsMeagre (clRep s \ clRep t) := by
    refine IsMeagre.mono ?_ ((clRep_equiv hs).union (clRep_equiv ht))
    rintro x ⟨hxs, hxt⟩
    rw [Set.mem_union, Set.mem_symmDiff, Set.mem_symmDiff]
    by_cases hx : x ∈ s
    · exact Or.inr (Or.inl ⟨hst hx, hxt⟩)
    · exact Or.inl (Or.inr ⟨hxs, hx⟩)
  have h := eq_empty_of_isClopen_of_isMeagre
    ((clRep_isClopen s).diff (clRep_isClopen t)) hmeagre
  exact Set.diff_eq_empty.mp h

/-- A continuous function that vanishes off a meagre set vanishes. -/
private theorem eq_of_isMeagre_ne {g h : X → ℂ} (hg : Continuous g) (hh : Continuous h)
    (hm : IsMeagre {x | g x ≠ h x}) : g = h := by
  have hopen : IsOpen {x | g x ≠ h x} := by
    have : {x | g x ≠ h x} = (fun x => g x - h x) ⁻¹' {(0 : ℂ)}ᶜ := by
      ext x; simp [sub_eq_zero]
    rw [this]
    exact (hg.sub hh).isOpen_preimage _ (isClosed_singleton.isOpen_compl)
  have h0 : {x | g x ≠ h x} = ∅ := by
    have := baire_category_theorem _ hm
    rwa [hopen.interior_eq] at this
  funext x
  by_contra hne
  exact absurd (Set.eq_empty_iff_forall_notMem.mp h0 x) (by simpa using hne)

variable (hms : ∀ s : Set X, MeasurableSet s ↔ AlmostClopen s)

include hms

/-- Every bounded measurable real function on the spectrum agrees off a meagre
set with a continuous one.  The representative is built from the clopen
representatives `Cᵣ` of the sublevel sets `{f < r}` (`r` rational) by
`g(x) = inf {r : x ∈ Cᵣ}`; `Cᵣ` is increasing in `r`, empty below `-M` and
everything above `M`, which makes the infimum well defined, and
`{g < r} = ⋃_{q<r} C_q`, `{g > r} = ⋃_{q>r} C_qᶜ` are open. -/
private theorem exists_contRep_real (f : X → ℝ) (hfm : Measurable f)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∃ g : X → ℝ, Continuous g ∧ IsMeagre {x | f x ≠ g x} := by
  classical
  have hac : ∀ r : ℚ, AlmostClopen {y : X | f y < (r : ℝ)} := fun r =>
    (hms _).mp (hfm measurableSet_Iio)
  set C : ℚ → Set X := fun r => clRep {y : X | f y < (r : ℝ)} with hCdef
  have hCclopen : ∀ r, IsClopen (C r) := fun r => clRep_isClopen _
  have hCmono : ∀ r r' : ℚ, r ≤ r' → C r ⊆ C r' := by
    intro r r' hrr
    refine clRep_mono (hac r) (hac r') fun y hy => ?_
    show f y < (r' : ℝ)
    exact lt_of_lt_of_le hy (by exact_mod_cast hrr)
  have hClow : ∀ r : ℚ, (r : ℝ) ≤ -M → C r = ∅ := by
    intro r hr
    have : {y : X | f y < (r : ℝ)} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hr (neg_le_of_abs_le (hM y))
    rw [hCdef]; simp only; rw [this, clRep_empty]
  have hChigh : ∀ r : ℚ, M < (r : ℝ) → C r = Set.univ := by
    intro r hr
    have h1 : {y : X | f y < (r : ℝ)} = Set.univ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_le_of_lt (le_of_abs_le (hM y)) hr
    rw [hCdef]; simp only; rw [h1, clRep_of_isClopen isClopen_univ]
  set S : X → Set ℝ := fun x => (fun r : ℚ => (r : ℝ)) '' {r : ℚ | x ∈ C r} with hSdef
  obtain ⟨r₁, hr₁⟩ := exists_rat_gt M
  have hSne : ∀ x, (S x).Nonempty := by
    intro x
    exact ⟨(r₁ : ℝ), ⟨r₁, by rw [Set.mem_setOf_eq, hChigh r₁ hr₁]; trivial, rfl⟩⟩
  have hSbdd : ∀ x, BddBelow (S x) := by
    intro x
    refine ⟨-M, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    by_contra hlt
    rw [not_le] at hlt
    rw [Set.mem_setOf_eq, hClow r hlt.le] at hr
    exact hr
  set g : X → ℝ := fun x => sInf (S x) with hgdef
  have hlt : ∀ (x : X) (r : ℝ), g x < r ↔ ∃ q : ℚ, (q : ℝ) < r ∧ x ∈ C q := by
    intro x r
    rw [hgdef]
    simp only
    rw [csInf_lt_iff (hSbdd x) (hSne x)]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, hlt⟩
      exact ⟨q, hlt, hq⟩
    · rintro ⟨q, hq, hxq⟩
      exact ⟨(q : ℝ), ⟨q, hxq, rfl⟩, hq⟩
  have hgt : ∀ (x : X) (r : ℝ), r < g x ↔ ∃ q : ℚ, r < (q : ℝ) ∧ x ∉ C q := by
    intro x r
    constructor
    · intro h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
      refine ⟨q, hq1, fun hxq => ?_⟩
      have : g x ≤ (q : ℝ) := csInf_le (hSbdd x) ⟨q, hxq, rfl⟩
      exact absurd hq2 (not_lt.mpr this)
    · rintro ⟨q, hq, hxq⟩
      refine lt_of_lt_of_le hq ?_
      refine le_csInf (hSne x) ?_
      rintro _ ⟨q', hq', rfl⟩
      simp only
      by_contra hcon
      rw [not_le] at hcon
      have hq'q : q' ≤ q := by exact_mod_cast hcon.le
      exact hxq (hCmono q' q hq'q hq')
  have hopen1 : ∀ r : ℝ, IsOpen {x : X | g x < r} := by
    intro r
    have : {x : X | g x < r} = ⋃ q : {q : ℚ // (q : ℝ) < r}, C q.1 := by
      ext x
      rw [Set.mem_setOf_eq, hlt x r, Set.mem_iUnion]
      exact ⟨fun ⟨q, hq, hx⟩ => ⟨⟨q, hq⟩, hx⟩, fun ⟨q, hx⟩ => ⟨q.1, q.2, hx⟩⟩
    rw [this]
    exact isOpen_iUnion fun q => (hCclopen q.1).2
  have hopen2 : ∀ r : ℝ, IsOpen {x : X | r < g x} := by
    intro r
    have : {x : X | r < g x} = ⋃ q : {q : ℚ // r < (q : ℝ)}, (C q.1)ᶜ := by
      ext x
      rw [Set.mem_setOf_eq, hgt x r, Set.mem_iUnion]
      exact ⟨fun ⟨q, hq, hx⟩ => ⟨⟨q, hq⟩, hx⟩, fun ⟨q, hx⟩ => ⟨q.1, q.2, hx⟩⟩
    rw [this]
    exact isOpen_iUnion fun q => (hCclopen q.1).1.isOpen_compl
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Filter.eventually_of_mem ((hopen2 a).mem_nhds ha) fun y hy => hy
    · exact Filter.eventually_of_mem ((hopen1 a).mem_nhds ha) fun y hy => hy
  refine ⟨g, hcont, ?_⟩
  set N : Set X := ⋃ q : ℚ, symmDiff {y : X | f y < (q : ℝ)} (C q) with hNdef
  have hNm : IsMeagre N := isMeagre_iUnion fun q => clRep_equiv (hac q)
  refine IsMeagre.mono ?_ hNm
  intro x hx
  by_contra hxN
  have hkey : ∀ q : ℚ, (f x < (q : ℝ) ↔ x ∈ C q) := by
    intro q
    by_contra hcon
    refine hxN (Set.mem_iUnion.mpr ⟨q, ?_⟩)
    rw [Set.mem_symmDiff]
    rcases not_iff.mp hcon with h
    by_cases hf : f x < (q : ℝ)
    · exact Or.inl ⟨hf, fun hc => (h.mpr hc) hf⟩
    · exact Or.inr ⟨by tauto, hf⟩
  refine hx ?_
  rcases lt_trichotomy (f x) (g x) with h | h | h
  · obtain ⟨q, hq1, hq2⟩ := (hgt x (f x)).mp h
    exact absurd ((hkey q).mp hq1) hq2
  · exact h
  · obtain ⟨q, hq1, hq2⟩ := (hlt x (f x)).mp h
    exact absurd ((hkey q).mpr hq2) (not_lt.mpr hq1.le)

/-- Every bounded measurable function on the spectrum agrees off a meagre set
with a continuous one. -/
private theorem exists_contRep (f : X → ℂ) (hf : IsBoundedMeasurable X f) :
    ∃ g : C(X, ℂ), IsMeagre {x | f x ≠ g x} := by
  obtain ⟨hfm, M, hMf⟩ := hf
  obtain ⟨g₁, hg₁c, hg₁m⟩ := exists_contRep_real hms (fun x => (f x).re)
    (Complex.measurable_re.comp hfm) M
    (fun x => (abs_le.mpr ⟨by
      have := Complex.abs_re_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.1], by
      have := Complex.abs_re_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.2]⟩))
  obtain ⟨g₂, hg₂c, hg₂m⟩ := exists_contRep_real hms (fun x => (f x).im)
    (Complex.measurable_im.comp hfm) M
    (fun x => (abs_le.mpr ⟨by
      have := Complex.abs_im_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.1], by
      have := Complex.abs_im_le_norm (f x); have h2 := hMf x
      rw [abs_le] at this; linarith [this.2]⟩))
  refine ⟨⟨fun x => (g₁ x : ℂ) + (g₂ x : ℂ) * Complex.I, ?_⟩, ?_⟩
  · exact (Complex.continuous_ofReal.comp hg₁c).add
      ((Complex.continuous_ofReal.comp hg₂c).mul continuous_const)
  · refine IsMeagre.mono ?_ (hg₁m.union hg₂m)
    intro x hx
    by_contra hxN
    rw [Set.mem_union] at hxN
    push_neg at hxN
    simp only [Set.mem_setOf_eq, not_not] at hxN
    refine hx ?_
    show f x = (g₁ x : ℂ) + (g₂ x : ℂ) * Complex.I
    rw [← hxN.1, ← hxN.2]
    exact (Complex.re_add_im (f x)).symm

/-- **54XI** in the form the duplicator analysis needs: if a C*-algebra `𝒞` is
∗-isomorphic to `C(X)` for the (extremally disconnected, compact Hausdorff)
space `X`, and `μ` is a measure on `X` whose null sets are exactly the meagre
almost clopen sets, then `𝒞` *is* `L^∞(X, μ)`: every bounded measurable
function agrees `μ`-almost everywhere with a unique continuous one
(`exists_contRep`), and `q` is "take that continuous representative, then apply
`γ⁻¹`". -/
private theorem exists_isLinftyOf_of_starAlgEquiv
    (μ : Measure X)
    (hμ : ∀ s : Set X, AlmostClopen s → (μ s = 0 ↔ IsMeagre s))
    (𝒞 : Type u) [CStarAlgebra 𝒞] (γ : 𝒞 ≃⋆ₐ[ℂ] C(X, ℂ)) :
    ∃ q : (X → ℂ) → 𝒞, IsLinftyOf μ 𝒞 q := by
  classical
  -- an open set is almost clopen, so a continuous function is measurable
  have hopenac : ∀ U : Set X, IsOpen U → AlmostClopen U :=
    open_almost_clopen.mp inferInstance
  have hcontmeas : ∀ g : C(X, ℂ), Measurable (⇑g) := by
    intro g
    refine measurable_of_isOpen fun U hU => ?_
    exact (hms _).mpr (hopenac _ (hU.preimage g.continuous))
  have hbm : ∀ g : C(X, ℂ), IsBoundedMeasurable X (⇑g) :=
    fun g => ⟨hcontmeas g, ‖g‖, fun x => g.norm_coe_le_norm x⟩
  -- meagre sets are null
  have hnull : ∀ s : Set X, IsMeagre s → μ s = 0 := by
    intro s hs
    refine (hμ s ⟨∅, isClopen_empty, ?_⟩).mpr hs
    show IsMeagre (symmDiff s (∅ : Set X))
    simpa [Set.symmDiff_def] using hs
  -- a continuous function that is null-supported vanishes
  have hzero : ∀ g : C(X, ℂ), μ {x | (g : X → ℂ) x ≠ 0} = 0 → g = 0 := by
    intro g hg
    have hop : IsOpen {x | (g : X → ℂ) x ≠ 0} :=
      g.continuous.isOpen_preimage _ isClosed_singleton.isOpen_compl
    have hm : IsMeagre {x | (g : X → ℂ) x ≠ 0} :=
      (hμ _ (hopenac _ hop)).mp hg
    have h0 := baire_category_theorem _ hm
    rw [hop.interior_eq] at h0
    ext x
    by_contra hne
    exact absurd (Set.eq_empty_iff_forall_notMem.mp h0 x) (by simpa using hne)
  set q : (X → ℂ) → 𝒞 := fun f =>
    if h : ∃ g : C(X, ℂ), IsMeagre {x | f x ≠ (g : X → ℂ) x}
      then γ.symm h.choose else 0 with hqdef
  have hqspec : ∀ (f : X → ℂ) (g : C(X, ℂ)),
      IsMeagre {x | f x ≠ (g : X → ℂ) x} → q f = γ.symm g := by
    intro f g hfg
    have hex : ∃ g : C(X, ℂ), IsMeagre {x | f x ≠ (g : X → ℂ) x} := ⟨g, hfg⟩
    have hch := hex.choose_spec
    have heq : (hex.choose : X → ℂ) = (g : X → ℂ) := by
      refine eq_of_isMeagre_ne hex.choose.continuous g.continuous ?_
      refine IsMeagre.mono ?_ (hch.union hfg)
      intro x hx
      rw [Set.mem_union]
      by_cases hf : f x = (hex.choose : X → ℂ) x
      · refine Or.inr (show f x ≠ (g : X → ℂ) x from fun hc => hx ?_)
        show (hex.choose : X → ℂ) x = (g : X → ℂ) x
        rw [← hf]; exact hc
      · exact Or.inl hf
    rw [hqdef]
    simp only [dif_pos hex]
    congr 1
    exact DFunLike.coe_injective heq
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- surjectivity
    intro y
    refine ⟨⇑(γ y), hbm _, ?_⟩
    rw [hqspec _ (γ y) (by simpa using (IsMeagre.empty : IsMeagre (∅ : Set X)))]
    exact γ.symm_apply_apply y
  · -- additivity
    intro f f' hf hf'
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    obtain ⟨g', hg'⟩ := exists_contRep hms f' hf'
    rw [hqspec f g hg, hqspec f' g' hg', ← map_add]
    refine hqspec (f + f') (g + g') ?_
    refine IsMeagre.mono ?_ (hg.union hg')
    intro x hx
    rw [Set.mem_union]
    by_contra hcon
    push_neg at hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.add_apply, hcon.1, hcon.2])
  · -- scalars
    intro z f hf
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    rw [hqspec f g hg, ← map_smul]
    refine hqspec (z • f) (z • g) ?_
    refine IsMeagre.mono ?_ hg
    intro x hx
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.smul_apply, hcon])
  · -- multiplicativity
    intro f f' hf hf'
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    obtain ⟨g', hg'⟩ := exists_contRep hms f' hf'
    rw [hqspec f g hg, hqspec f' g' hg', ← map_mul]
    refine hqspec (f * f') (g * g') ?_
    refine IsMeagre.mono ?_ (hg.union hg')
    intro x hx
    rw [Set.mem_union]
    by_contra hcon
    push_neg at hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.mul_apply, hcon.1, hcon.2])
  · -- involution
    intro f hf
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    rw [hqspec f g hg, ← map_star]
    refine hqspec (star f) (star g) ?_
    refine IsMeagre.mono ?_ hg
    intro x hx
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hx (by simp [Pi.star_apply, hcon])
  · -- unitality
    rw [hqspec (1 : X → ℂ) 1 (by simpa using (IsMeagre.empty : IsMeagre (∅ : Set X)))]
    exact map_one _
  · -- kernel
    intro f hf
    obtain ⟨g, hg⟩ := exists_contRep hms f hf
    have hfg0 : μ {x | f x ≠ (g : X → ℂ) x} = 0 := hnull _ hg
    rw [hqspec f g hg]
    constructor
    · intro h0
      have hg0 : g = 0 := by
        have := congrArg γ h0
        rwa [γ.apply_symm_apply, map_zero] at this
      have hsub : {x | f x ≠ (0 : X → ℂ) x} ⊆ {x | f x ≠ (g : X → ℂ) x} := by
        intro x hx hc
        exact hx (by rw [hc, hg0]; rfl)
      exact measure_mono_null hsub hfg0
    · intro h0
      have hf0 : μ {x | f x ≠ (0 : X → ℂ) x} = 0 := h0
      have hsub : {x | (g : X → ℂ) x ≠ 0} ⊆
          {x | f x ≠ (g : X → ℂ) x} ∪ {x | f x ≠ (0 : X → ℂ) x} := by
        intro x hx
        rw [Set.mem_union]
        by_cases hc : f x = (g : X → ℂ) x
        · exact Or.inr (fun hz => hx (by rw [← hc]; exact hz))
        · exact Or.inl hc
      have := measure_mono_null hsub (measure_union_null hfg0 hf0)
      rw [hzero g this, map_zero]


end ContRep

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
      ∃ ρ : NMIUMap (VNT A A) A, ∀ t, ρ t = M.m.toNCPMap t := by
  -- By **128VIII** the multiplication is the algebra's own on pure tensors and
  -- (**128XII**.2) `𝒜` is commutative; both claims are then the statement that
  -- two *normal* maps agreeing on the pure tensors agree, since the span of the
  -- pure tensors is ultraweakly dense (108II.1) and normal = ultraweakly
  -- continuous (**45III** `p_uwcont`).
  letI : TopologicalSpace (VNT A A) := ultraweak (VNT A A)
  letI : TopologicalSpace A := ultraweak A
  haveI : T2Space A := (vn_positive_basic_1 (A := A)).1
  obtain ⟨-, hm⟩ := monoid_e_and_mul M
  have hm0 : M.m.toNCPMap (0 : VNT A A) = 0 :=
    map_zero M.m.toNCPMap.toCompletelyPositiveMap
  have hmadd : ∀ x y : VNT A A,
      M.m.toNCPMap (x + y) = M.m.toNCPMap x + M.m.toNCPMap y :=
    map_add M.m.toNCPMap.toCompletelyPositiveMap
  have hcomm : ∀ a b : A, a * b = b * a :=
    (duplicability_multiplication (A := A)).2 (dup_vna_is_monoid_1 M)
  have hmc : Continuous (fun t : VNT A A => M.m.toNCPMap t) :=
    ((p_uwcont (ncpPositive M.m.toNCPMap)).out 2 0).mp
      M.m.toNCPMap.preservesDirSups'
  -- the extension principle
  have hdense : Dense (Set.range ⇑(TensorProduct.lift (vnTensor A A).map)) := by
    rw [range_lift_eq_span]
    exact (vnTensor A A).isTensorProduct.dense
  have hext : ∀ F G : VNT A A → A, Continuous F → Continuous G →
      (∀ t : A ⊗[ℂ] A, F (TensorProduct.lift (vnTensor A A).map t)
        = G (TensorProduct.lift (vnTensor A A).map t)) → ∀ x, F x = G x := by
    intro F G hF hG hFG x
    have h : F = G := by
      refine Continuous.ext_on hdense hF hG ?_
      rintro _ ⟨t, rfl⟩
      exact hFG t
    exact congrFun h x
  have hlift : ∀ a b : A,
      TensorProduct.lift (vnTensor A A).map (a ⊗ₜ[ℂ] b) = a ⊗ᵥ b := by
    intro a b
    rw [TensorProduct.lift.tmul]
    rfl
  constructor
  · -- (1) commutativity: `m ∘ γ` and `m` agree on pure tensors
    have hbc : Continuous (fun t : VNT A A => braiding A A t) :=
      ((p_uwcont (nmiuP (braiding A A))).out 2 0).mp (braiding A A).preservesDirSups'
    have hb0 : braiding A A (0 : VNT A A) = 0 :=
      map_zero (braiding A A).toStarAlgHom
    have hbadd : ∀ x y : VNT A A,
        braiding A A (x + y) = braiding A A x + braiding A A y :=
      map_add (braiding A A).toStarAlgHom
    have hbtmul : ∀ a b : A, braiding A A (a ⊗ᵥ b) = b ⊗ᵥ a :=
      (exists_braiding A A).choose_spec.1
    refine hext _ _ (hmc.comp hbc) hmc fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero]
        rw [hb0]
    | tmul a b => rw [hlift, hbtmul, hm, hm, hcomm]
    | add u v hu hv =>
        simp only [map_add]
        rw [hbadd, hmadd, hmadd, hu, hv]
  · -- (2) `m` is multiplicative: `m ∘ γ_⊙` is the lift of the (multiplicative,
    -- because `𝒜` is commutative) bilinear map `(a, b) ↦ ab`
    have hmβ : BilinMult (LinearMap.mul ℂ A) := by
      intro a b c d
      show (a * b) * (c * d) = (a * c) * (b * d)
      rw [mul_assoc, mul_assoc, ← mul_assoc b c d, ← mul_assoc c b d, hcomm b c]
    have hcomp : ∀ t : A ⊗[ℂ] A,
        M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map t)
          = TensorProduct.lift (LinearMap.mul ℂ A) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
          simp only [map_zero]
          exact hm0
      | tmul a b => rw [hlift, hm, TensorProduct.lift.tmul]; rfl
      | add u v hu hv =>
          simp only [map_add]
          rw [hmadd, hu, hv]
    have step1 : ∀ s t : A ⊗[ℂ] A,
        M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map s *
            TensorProduct.lift (vnTensor A A).map t)
          = M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map s) *
            M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map t) := by
      intro s t
      rw [← lift_mul _ (vnTensor A A).isTensorProduct.miu.2.1, hcomp, hcomp,
        hcomp, lift_mul _ hmβ]
    have step2 : ∀ (t : A ⊗[ℂ] A) (x : VNT A A),
        M.m.toNCPMap (x * TensorProduct.lift (vnTensor A A).map t)
          = M.m.toNCPMap x *
            M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map t) := by
      intro t
      refine hext (fun z => M.m.toNCPMap (z * TensorProduct.lift (vnTensor A A).map t))
        (fun z => M.m.toNCPMap z *
          M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map t)) ?_ ?_
        (fun s => step1 s t)
      · exact hmc.comp (mult_uws_cont _).2.1
      · exact (mult_uws_cont
          (M.m.toNCPMap (TensorProduct.lift (vnTensor A A).map t))).2.1.comp hmc
    have hmul : ∀ x y : VNT A A,
        M.m.toNCPMap (x * y) = M.m.toNCPMap x * M.m.toNCPMap y := by
      intro x y
      refine hext (fun z => M.m.toNCPMap (x * z))
        (fun z => M.m.toNCPMap x * M.m.toNCPMap z) ?_ ?_ (fun t => step2 t x) y
      · exact hmc.comp (mult_uws_cont x).1
      · exact (mult_uws_cont (M.m.toNCPMap x)).1.comp hmc
    have hone : M.m.toNCPMap (1 : VNT A A) = 1 := by
      have h1 : ((1 : A) ⊗ᵥ (1 : A)) = (1 : VNT A A) :=
        (vnTensor A A).isTensorProduct.miu.1
      have h := hm 1 1
      rw [h1, one_mul] at h
      exact h
    refine ⟨{ toStarAlgHom :=
                { toFun := fun t => M.m.toNCPMap t,
                  map_one' := hone,
                  map_mul' := hmul,
                  map_zero' := map_zero M.m.toNCPMap.toCompletelyPositiveMap,
                  map_add' := map_add M.m.toNCPMap.toCompletelyPositiveMap,
                  commutes' := fun c => by
                    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
                    show M.m.toNCPMap (c • (1 : VNT A A)) = c • (1 : A)
                    have h2 : M.m.toNCPMap (c • (1 : VNT A A))
                        = c • M.m.toNCPMap (1 : VNT A A) :=
                      map_smul M.m.toNCPMap.toCompletelyPositiveMap c _
                    rw [h2, hone],
                  map_star' := fun t => ncp_star M.m.toNCPMap t },
              preservesDirSups' := M.m.toNCPMap.preservesDirSups' },
      fun _ => rfl⟩

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
      ∀ (a : A) (ω : NCPSUMap A ℂ), η.toNCPMap a ω = ω.toNCPMap a := by
  -- `η` is the mediating map of the `W*_cpsu`-product of the constant family
  -- `(ℂ)_{ω}` for the cone `(ω)_{ω}`.  Its C*-half is **20aI**.4
  -- (`cstar_product_4`, proved), which delivers complete positivity and
  -- subunitality; normality is pointwise, exactly as in **47IV**.3, because
  -- the order on `ℓ^∞` is pointwise (`lp_infty_le_iff`) and each `ω` is
  -- normal.  (**47IV**.3 `vn_products_ncpsu` itself is not needed.)
  have hcp : ∀ ω : NCPSUMap A ℂ, Theses.A.CStar.IsCompletelyPositiveMap
      (ω.toNCPMap.toCompletelyPositiveMap.toLinearMap) := fun ω =>
    (Theses.A.CStar.cp_iff _).out 1 0 |>.mp fun N M hM =>
      ω.toNCPMap.toCompletelyPositiveMap.map_cstarMatrix_nonneg' N M hM
  have hsu : ∀ ω : NCPSUMap A ℂ,
      Subunital ⇑(ω.toNCPMap.toCompletelyPositiveMap.toLinearMap) :=
    fun ω => ω.subunital'
  obtain ⟨g, ⟨hgcp, hgsu, hgval⟩, -⟩ :=
    Theses.A.CStar.cstar_product_4 (𝒜f := fun _ : NCPSUMap A ℂ => ℂ)
      (fun ω => ω.toNCPMap.toCompletelyPositiveMap.toLinearMap) hcp hsu
  have hgcp' : Theses.A.CStar.IsCompletelyPositiveMap g := hgcp
  have hnorm : PreservesDirSups ⇑g := by
    intro D s hne hdir hlub
    constructor
    · rintro _ ⟨d, hd, rfl⟩
      rw [lp_infty_le_iff]
      intro ω
      rw [hgval ω, hgval ω]
      exact (ω.toNCPMap.preservesDirSups' D s hne hdir hlub).1 ⟨d, hd, rfl⟩
    · intro u hu
      rw [lp_infty_le_iff]
      intro ω
      rw [hgval ω]
      refine (ω.toNCPMap.preservesDirSups' D s hne hdir hlub).2 ?_
      rintro _ ⟨d, hd, rfl⟩
      have hd' := (lp_infty_le_iff _ _).mp (hu ⟨d, hd, rfl⟩) ω
      rwa [hgval ω] at hd'
  exact ⟨{ toNCPMap :=
             { toCompletelyPositiveMap :=
                 { toLinearMap := g,
                   map_cstarMatrix_nonneg' :=
                     (Theses.A.CStar.cp_iff g).out 0 1 |>.mp hgcp' },
               preservesDirSups' := hnorm },
           subunital' := hgsu }, fun a ω => hgval ω a⟩

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
