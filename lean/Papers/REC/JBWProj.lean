/-
Papers/REC/JBWProj.lean

**Projections in a JBW-algebra** (Hanche-Olsen–Størmer, *Jordan Operator Algebras*,
§4.1–4.3, 5.2), toward REC 136's remaining input `ExceptionalBoundedRank` (i).

Plan (2026-09-26, all done, no sorry).  No Macdonald / Shirshov–Cohn: positivity of `U_a`
for general `a` is not used; everything goes through idempotents (`U_p = P₁(p)` is positive,
§3) and Cauchy–Schwarz.
1. Monotone completeness (`exists_isLUB_unit`, `exists_isLUB_bdd`); normal states along
   increasing sequences.  2. Cauchy–Schwarz; one multiplication is weakly continuous.
3. `V₁(p)+V₀(p)` closed subalgebra, `p·` multiplicative there; `σ_p` order automorphism;
   `P₁(p)`, `P₀(p)` positive, `ω∘P₁`, `ω∘P₀` normal; `L_p` weakly continuous.
4. Spectral projections `sproj a g = ⋁ₙ min((n+1)g,1)(a)` (`g ≥ 0` on `sp a`): idempotent,
   unit on `g·C(a)`, zero on `h(a)` with `gh = 0`, `P½(p) C(a) = 0`; range projections.
5. Normal states are order-determining (`nonneg_of_normal`).
6. Spectral theorem (`spectral_approx`, `spectral_approx_norm`): `0 ≤ a - (c + δΣqᵢ) ≤ δ`,
   `qᵢ` idempotents with `P½(qᵢ) a = 0`.  7. Non-trivial idempotents (`exists_nontrivial_idem`).
8. Idempotent order `p ≤ q ⟺ qp = p`; `p ∨ q = r(p+q)` (`sup2_spec`).
9. Central ⟺ `P½(e) z = 0` for all idempotents `e` (`central_of_Ph`).
10. Directed sups of idempotents are idempotent; complete lattice (`exists_sSup_idem`);
   central cover (`exists_central_cover`, `centralCover`) = sup of the `σ`-orbit.
11. Purely exceptional ⇒ no associative (type I₁) central summand (`centralIdem_not_assoc`).
12. Comparison step (`exists_connected_sub`, `exists_exch_sub`): `p ⊥ q`,
   `0 ≠ x ∈ V½(p)∩V½(q)` ⇒ non-zero `p' ≤ p`, `q' ≤ q` exchangeable by a symmetry, via the
   partial symmetry `v = r(x⁺) - r(x⁻)` (odd functional calculus stays in `V½`).
13. Not associative ⇒ exchangeable pair (`exists_exch_pair`); purely exceptional ⇒ ditto.
14. Peirce corners `eVe` are JBW-algebras (`ECorner`); **(i) holds in a non-zero corner of
   every non-zero purely exceptional JBW-algebra** (`pe_corner_hasExchFamily`).
Not reached: (i) itself (frame summing to `1`) needs the comparison theorem (Zorn over
orthogonal exchangeable families + additivity of exchange), the type decomposition, and
H-O–S 7.2.7's "purely exceptional ⇒ type I₃" (speciality of spin factors, I_n (n ≥ 4),
II, III); (ii) needs the Albert-algebra structure of the type-I₃ fibres.
-/
import Papers.REC.JBCalculus
import Papers.REC.JBPeirce

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace Papers.REC.JBWProj

open Theses.B.Eff Papers.REC Papers.REC.JBCalc Filter Topology

universe u

noncomputable section

/-! ## 1. Monotone completeness and normal states -/

section Mono

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **Monotone completeness**: a non-empty directed subset of `[0,1]` has a least upper
bound in all of `V` (not only in `[0,1]`), lying in `[0,1]`.  An upper bound `t ≤ N·1`
is compared after scaling the set by `N⁻¹`. -/
theorem exists_isLUB_unit {D : Set V} (hD : D ⊆ Set.Icc 0 (ouUnit V)) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) : ∃ s, IsLUB D s ∧ s ∈ Set.Icc 0 (ouUnit V) := by
  obtain ⟨s, hs, hub, hleast⟩ := hW.directedComplete D hD hdir
  refine ⟨s, ⟨hub, fun t ht => ?_⟩, hs⟩
  obtain ⟨d0, hd0⟩ := hne
  have ht0 : 0 ≤ t := (hD hd0).1.trans (ht hd0)
  obtain ⟨n, hn⟩ := ou_exists_le_smul_unit t
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.2 hN.le
  have htN : t ≤ N • ouUnit V := hn.trans (ou_smul_unit_mono (by linarith))
  have hsc : ∀ x : V, N • (N⁻¹ • x) = x := fun x => by
    rw [_root_.smul_smul, mul_inv_cancel₀ hN.ne', one_smul]
  have hD' : (fun x => N⁻¹ • x) '' D ⊆ Set.Icc 0 (ouUnit V) := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨ou_smul_nonneg hNi (hD hd).1, ?_⟩
    calc N⁻¹ • d ≤ N⁻¹ • ouUnit V := ou_smul_le_smul hNi (hD hd).2
      _ ≤ (1 : ℝ) • ouUnit V := ou_smul_unit_mono (inv_le_one_of_one_le₀ (by linarith))
      _ = _ := one_smul _ _
  obtain ⟨s', hs', hub', hleast'⟩ := hW.directedComplete _ hD' (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨z, hz, h1, h2⟩ := hdir a ha b hb
    exact ⟨_, ⟨z, hz, rfl⟩, ou_smul_le_smul hNi h1, ou_smul_le_smul hNi h2⟩)
  -- `s' ≤ N⁻¹ t`
  have h1 : s' ≤ N⁻¹ • t := hleast' _ ⟨ou_smul_nonneg hNi ht0, by
      calc N⁻¹ • t ≤ N⁻¹ • (N • ouUnit V) := ou_smul_le_smul hNi htN
        _ = ouUnit V := by rw [_root_.smul_smul, inv_mul_cancel₀ hN.ne', one_smul]⟩ (by
    rintro _ ⟨d, hd, rfl⟩; exact ou_smul_le_smul hNi (ht hd))
  -- `s' ≤ N⁻¹ 1`, so `N s' ∈ [0,1]` bounds `D`
  have h2 : s' ≤ N⁻¹ • ouUnit V := hleast' _ ⟨ou_smul_unit_nonneg hNi, by
      calc N⁻¹ • ouUnit V ≤ (1 : ℝ) • ouUnit V :=
            ou_smul_unit_mono (inv_le_one_of_one_le₀ (by linarith))
        _ = _ := one_smul _ _⟩ (by
    rintro _ ⟨d, hd, rfl⟩; exact ou_smul_le_smul hNi (hD hd).2)
  have h3 : s ≤ N • s' := hleast _ ⟨ou_smul_nonneg hN.le hs'.1, by
      have := ou_smul_le_smul hN.le h2; rwa [hsc] at this⟩ (by
    intro d hd
    have := ou_smul_le_smul hN.le (hub' _ ⟨d, hd, rfl⟩); rwa [hsc] at this)
  calc s ≤ N • s' := h3
    _ ≤ N • (N⁻¹ • t) := ou_smul_le_smul hN.le h1
    _ = t := hsc t

/-- An increasing sequence in `[0,1]` has a least upper bound in `V`. -/
theorem exists_isLUB_seq {x : ℕ → V} (hx : Monotone x) (h0 : ∀ n, 0 ≤ x n)
    (h1 : ∀ n, x n ≤ ouUnit V) : ∃ s, IsLUB (Set.range x) s ∧ s ∈ Set.Icc 0 (ouUnit V) :=
  exists_isLUB_unit (by rintro _ ⟨n, rfl⟩; exact ⟨h0 n, h1 n⟩) (Set.range_nonempty x)
    (directedOn_range.2 hx.directed_le)

omit hW in
/-- A state is monotone. -/
theorem state_mono (ω : OUSState V) {a b : V} (h : a ≤ b) : ω.toLin a ≤ ω.toLin b := by
  have := ω.nonneg _ (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this

omit hW in
/-- **Normal states converge along increasing sequences.** -/
theorem normal_tendsto {x : ℕ → V} (hx : Monotone x) {s : V} (hs : IsLUB (Set.range x) s)
    {ω : OUSState V} (hω : IsNormalMap ω.toLin) :
    Tendsto (fun n => ω.toLin (x n)) atTop (𝓝 (ω.toLin s)) := by
  have h := hω (Set.range x) s (Set.range_nonempty x) (directedOn_range.2 hx.directed_le) hs
  rw [← Set.range_comp] at h
  exact tendsto_atTop_isLUB (fun m n hmn => state_mono ω (hx hmn)) h

/-- **Normal states separate points** (REC 48), as an extensionality principle. -/
theorem eq_of_normal {a b : V} (h : ∀ ω : OUSState V, IsNormalMap ω.toLin → ω.toLin a = ω.toLin b) :
    a = b := by
  by_contra hne
  obtain ⟨ω, hω, hne'⟩ := hW.separating a b hne
  exact hne' (h ω hω)

end Mono

/-! ## 2. Cauchy–Schwarz and weak continuity of one multiplication -/

section CS

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- **Cauchy–Schwarz** for a positive functional on a JB-algebra (H-O–S 3.6.2):
`ψ(xy)² ≤ ψ(x²) ψ(y²)`, from `ψ((x + t y)²) ≥ 0`. -/
theorem cs_ineq (ψ : V →ₗ[ℝ] ℝ) (hψ : ∀ v, 0 ≤ v → 0 ≤ ψ v) (x y : V) :
    ψ (x * y) ^ 2 ≤ ψ (x * x) * ψ (y * y) := by
  have key : ∀ t : ℝ, 0 ≤ ψ (x * x) + 2 * t * ψ (x * y) + t ^ 2 * ψ (y * y) := by
    intro t
    have h := hψ _ (jb_sq_nonneg (x + t • y))
    have e : (x + t • y) * (x + t • y) = x * x + (2 * t) • (x * y) + (t ^ 2) • (y * y) := by
      simp only [JBAlgebra.add_mul, jb_mul_add, JBAlgebra.smul_mul, jb_mul_smul,
        JBAlgebra.mul_comm y x]
      module
    rw [e, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    linarith
  set A := ψ (x * x)
  set B := ψ (x * y)
  set C := ψ (y * y)
  have hA : 0 ≤ A := by simpa using key 0
  rcases (hψ _ (jb_sq_nonneg y)).lt_or_eq with hC | hC
  · set t := -B / C with htdef
    have ht : t * C = -B := by rw [htdef, neg_div, neg_mul, div_mul_cancel₀ _ hC.ne']
    have h := key t
    have e : t ^ 2 * C = -(t * B) := by rw [sq, mul_assoc, ht]; ring
    have h' : 0 ≤ A + t * B := by linarith
    have e2 : (A + t * B) * C = A * C - B ^ 2 := by linear_combination B * ht
    have := mul_nonneg h' hC.le
    linarith
  · have hC0 : C = 0 := hC.symm
    rw [hC0, mul_zero]
    by_contra hB
    have hB0 : B ≠ 0 := by rintro h0; rw [h0] at hB; simp at hB
    have h := key (-(A + 1) / (2 * B))
    have e : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by field_simp
    rw [e, hC0, mul_zero] at h
    linarith

/-- `d² ≤ M d` for `0 ≤ d ≤ M·1` (in the associative `C(d)`). -/
theorem sq_le_smul {d : V} {M : ℝ} (hd : 0 ≤ d) (hdM : d ≤ M • ouUnit V) : d * d ≤ M • d := by
  have h1 : M • ouUnit V - d ∈ (Ca d).carrier :=
    (Ca d).carrier.sub_mem ((Ca d).carrier.smul_mem _ (Ca d).one_mem) (self_mem_Ca d)
  have := Ca_mul_nonneg (self_mem_Ca d) h1 hd (sub_nonneg.2 hdM)
  rw [jb_mul_sub, jb_mul_smul, JBAlgebra.mul_one, sub_nonneg] at this
  exact this

/-- `ψ(c d)² ≤ M ψ(c²) ψ(d)` for `0 ≤ d ≤ M·1`. -/
theorem cs_bound (ψ : V →ₗ[ℝ] ℝ) (hψ : ∀ v, 0 ≤ v → 0 ≤ ψ v) (c : V) {d : V} {M : ℝ}
    (hd : 0 ≤ d) (hdM : d ≤ M • ouUnit V) : ψ (c * d) ^ 2 ≤ ψ (c * c) * (M * ψ d) := by
  have h1 := cs_ineq ψ hψ c d
  have h2 : ψ (d * d) ≤ M * ψ d := by
    have := hψ _ (sub_nonneg.2 (sq_le_smul hd hdM))
    rw [map_sub, map_smul, smul_eq_mul, sub_nonneg] at this
    exact this
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (hψ _ (jb_sq_nonneg c)))

/-- **One multiplication is weakly continuous**: if `0 ≤ dₙ ≤ 1` and `ψ(dₙ) → 0` for a
positive functional `ψ`, then `ψ(c dₙ) → 0`. -/
theorem tendsto_mul_zero (ψ : V →ₗ[ℝ] ℝ) (hψ : ∀ v, 0 ≤ v → 0 ≤ ψ v) {d : ℕ → V}
    (hd0 : ∀ n, 0 ≤ d n) (hd1 : ∀ n, d n ≤ ouUnit V)
    (hlim : Tendsto (fun n => ψ (d n)) atTop (𝓝 0)) (c : V) :
    Tendsto (fun n => ψ (c * d n)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n => Real.sqrt (ψ (c * c) * (1 * ψ (d n)))) atTop (𝓝 0) := by
    have := ((hlim.const_mul 1).const_mul (ψ (c * c))).sqrt
    simpa using this
  refine squeeze_zero_norm (fun n => ?_) hg
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (cs_bound ψ hψ c (hd0 n) (by rw [one_smul]; exact hd1 n))

end CS

/-! ## 3. Idempotents: positivity of `U_p`, normality of `ω ∘ U_p`, weak continuity of `L_p` -/

section Idem

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

attribute [local instance] ousNormedAddCommGroup ousNormedSpace

variable {p : V}

theorem P1_self (hp : p * p = p) (x : V) : p * P1 p x = P1 p x := by
  have := P1_mem hp x; rw [mem_peirce, one_smul] at this; exact this

theorem P0_self (hp : p * p = p) (x : V) : p * P0 p x = 0 := by
  have := P0_mem hp x; rw [mem_peirce, zero_smul] at this; exact this

theorem decomp_of_Ph (x : V) (hx : Ph p x = 0) : P1 p x + P0 p x = x := by
  have := peirce_decomp p x; rwa [hx, add_zero] at this

theorem mul_of_Ph (hp : p * p = p) {x : V} (hx : Ph p x = 0) : p * x = P1 p x := by
  conv_lhs => rw [← decomp_of_Ph x hx]
  rw [jmul_add, P1_self hp, P0_self hp, add_zero]

theorem mul_decomp_of_Ph (hp : p * p = p) {x y : V} (hx : Ph p x = 0) (hy : Ph p y = 0) :
    x * y = P1 p x * P1 p y + P0 p x * P0 p y := by
  conv_lhs => rw [← decomp_of_Ph x hx, ← decomp_of_Ph y hy]
  rw [jadd_mul, jmul_add, jmul_add, peirce_one_mul_zero hp (P1_mem hp x) (P0_mem hp y),
    jmul_comm (P0 p x) (P1 p y), peirce_one_mul_zero hp (P1_mem hp y) (P0_mem hp x)]
  abel

/-- `V₁(p) + V₀(p) = ker P½(p)` is closed under the product. -/
theorem Ph_mul (hp : p * p = p) {x y : V} (hx : Ph p x = 0) (hy : Ph p y = 0) :
    Ph p (x * y) = 0 := by
  rw [mul_decomp_of_Ph hp hx hy, map_add,
    Ph_of_mem1 (peirce_one_mul_one hp (P1_mem hp x) (P1_mem hp y)),
    Ph_of_mem0 (peirce_zero_mul_zero hp (P0_mem hp x) (P0_mem hp y)), add_zero]

/-- On `V₁(p) + V₀(p)`, `x ↦ p x` is multiplicative. -/
theorem mul_hom_of_Ph (hp : p * p = p) {x y : V} (hx : Ph p x = 0) (hy : Ph p y = 0) :
    p * (x * y) = (p * x) * (p * y) := by
  have h1 := peirce_one_mul_one hp (P1_mem hp x) (P1_mem hp y)
  have h0 := peirce_zero_mul_zero hp (P0_mem hp x) (P0_mem hp y)
  rw [mem_peirce, one_smul] at h1
  rw [mem_peirce, zero_smul] at h0
  rw [mul_decomp_of_Ph hp hx hy, jmul_add, h1, h0, add_zero, mul_of_Ph hp hx, mul_of_Ph hp hy]

theorem continuous_Lmul (a : V) : Continuous fun x : V => a * x :=
  jb_continuous_mul.comp (continuous_const.prodMk continuous_id)

theorem continuous_Ph (p : V) : Continuous (Ph p) := by
  have e : (Ph p : V → V) = fun x => (4 : ℝ) • (p * x) - (4 : ℝ) • (p * (p * x)) :=
    funext (Ph_apply p)
  rw [e]
  exact ((continuous_Lmul p).const_smul _).sub
    (((continuous_Lmul p).comp (continuous_Lmul p)).const_smul _)

/-- **`V₁(p) + V₀(p)`** as a closed unital subalgebra. -/
def V10 (hp : p * p = p) : ClosedJBSub V where
  carrier := LinearMap.ker (Ph p)
  one_mem := Ph_unit JBAlgebra.one_mul hp
  mul_mem hx hy := Ph_mul hp hx hy
  closed x hx := by
    have hcl : IsClosed {y : V | Ph p y = 0} := isClosed_eq (continuous_Ph p) continuous_const
    refine hcl.closure_subset_iff.2 (fun y hy => hy) (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨y, hy, hxy⟩ := hx ε hε
    exact ⟨y, hy, by rw [dist_eq_norm]; exact hxy⟩

theorem mem_V10 (hp : p * p = p) {x : V} : x ∈ (V10 hp).carrier ↔ Ph p x = 0 :=
  LinearMap.mem_ker

/-- **`p z ≥ 0` for `z ≥ 0` in `V₁(p) + V₀(p)`**: `√z` lies in `C(z) ⊆ V₁ + V₀`, where
`x ↦ p x` is multiplicative, so `p z = (p √z)²`. -/
theorem idem_mul_nonneg (hp : p * p = p) {z : V} (hz : 0 ≤ z) (hz10 : Ph p z = 0) :
    0 ≤ p * z := by
  have hsub := Ca_le (V10 hp) ((mem_V10 hp).2 hz10)
  have hr : Ph p (jbSqrt z) = 0 := (mem_V10 hp).1 (hsub (jbSqrt_mem z))
  rw [← jbSqrt_mul_self hz, mul_hom_of_Ph hp hr hr]
  exact jb_sq_nonneg _

/-- The Peirce reflection `σ_p = U_{2p-1}` is positive (it is a Jordan automorphism, and
positive elements are squares). -/
theorem refl_nonneg (hp : p * p = p) {x : V} (hx : 0 ≤ x) : 0 ≤ peirceRefl p x := by
  rw [← jbSqrt_mul_self hx, peirceRefl_mul hp]; exact jb_sq_nonneg _

theorem refl_mono (hp : p * p = p) {x y : V} (h : x ≤ y) : peirceRefl p x ≤ peirceRefl p y := by
  have := refl_nonneg hp (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this

/-- `σ_p` preserves least upper bounds (an order automorphism). -/
theorem refl_isLUB (hp : p * p = p) {S : Set V} {s : V} (hs : IsLUB S s) :
    IsLUB (peirceRefl p '' S) (peirceRefl p s) := by
  refine ⟨?_, fun t ht => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact refl_mono hp (hs.1 hx)
  · have : s ≤ peirceRefl p t := hs.2 fun x hx => by
      have := refl_mono hp (ht ⟨x, hx, rfl⟩); rwa [peirceRefl_peirceRefl hp] at this
    have := refl_mono hp this; rwa [peirceRefl_peirceRefl hp] at this

theorem P1_add_P0 (x : V) : P1 p x + P0 p x = (2⁻¹ : ℝ) • (x + peirceRefl p x) := by
  have := peirce_decomp p x
  rw [peirceRefl_apply]
  have e : P1 p x + P0 p x = x - Ph p x := by linear_combination (norm := module) this
  rw [e]; module

theorem Ph_P1_add_P0 (hp : p * p = p) (x : V) : Ph p (P1 p x + P0 p x) = 0 := by
  rw [map_add, Ph_of_mem1 (P1_mem hp x), Ph_of_mem0 (P0_mem hp x), add_zero]

/-- **`U_p = P₁(p)` is positive** for an idempotent `p` (without Macdonald's theorem):
`P₁x = p (P₁x + P₀x)` and `P₁x + P₀x = ½(x + σ_p x) ≥ 0`. -/
theorem P1_nonneg (hp : p * p = p) {x : V} (hx : 0 ≤ x) : 0 ≤ P1 p x := by
  have h := idem_mul_nonneg hp (z := P1 p x + P0 p x) (by
    rw [P1_add_P0]; exact ou_smul_nonneg (by norm_num) (add_nonneg hx (refl_nonneg hp hx)))
    (Ph_P1_add_P0 hp x)
  rwa [jmul_add, P1_self hp, P0_self hp, add_zero] at h

theorem Ph_one_sub (x : V) : Ph (ouUnit V - p) x = Ph p x := by
  simp only [Ph_apply, jsub_mul, jmul_sub, JBAlgebra.one_mul]
  module

theorem P0_eq_P1_one_sub (x : V) : P0 p x = P1 (ouUnit V - p) x := by
  simp only [P0_apply, P1_apply, jsub_mul, JBAlgebra.one_mul, jmul_sub]
  module

/-- `P₀(p) = U_{1-p}` is positive. -/
theorem P0_nonneg (hp : p * p = p) {x : V} (hx : 0 ≤ x) : 0 ≤ P0 p x := by
  rw [P0_eq_P1_one_sub]; exact P1_nonneg (one_sub_idem JBAlgebra.one_mul hp) hx

theorem P1_le (hp : p * p = p) {x : V} (hx : 0 ≤ x) :
    P1 p x ≤ (2⁻¹ : ℝ) • (x + peirceRefl p x) := by
  rw [← P1_add_P0]; exact le_add_of_nonneg_right (P0_nonneg hp hx)

theorem P0_le (hp : p * p = p) {x : V} (hx : 0 ≤ x) :
    P0 p x ≤ (2⁻¹ : ℝ) • (x + peirceRefl p x) := by
  rw [← P1_add_P0]; exact le_add_of_nonneg_left (P1_nonneg hp hx)

/-- `L_p = ½(P₁ - P₀ + id)`. -/
theorem L_eq (x : V) : p * x = (2⁻¹ : ℝ) • (P1 p x - P0 p x + x) := by
  simp only [P1_apply, P0_apply]; module

theorem P1_one (hp : p * p = p) : P1 p (ouUnit V) = p := by
  rw [P1_apply, JBPeirce.mul_unit JBAlgebra.one_mul, hp]; module

end Idem

/-! ### Normality of `ω ∘ σ_p`, `ω ∘ P₁(p)`, `ω ∘ P₀(p)`; weak continuity of `L_p` -/

section IdemNormal

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

variable {p : V}

/-- A positive functional dominated on `[0, ∞)` by `½(ω + ω ∘ σ_p)` (for `ω` normal) is
normal: `ψ(s) - ψ(d) ≤ ½(ω(s - d) + ω(σ s - σ d))`, both small for `d` far along `S`. -/
theorem isNormal_of_dom (hp : p * p = p) (ω : OUSState V) (hω : IsNormalMap ω.toLin)
    (ψ : V →ₗ[ℝ] ℝ) (hψ : ∀ v, 0 ≤ v → 0 ≤ ψ v)
    (hdom : ∀ v, 0 ≤ v → ψ v ≤ 2⁻¹ * (ω.toLin v + ω.toLin (peirceRefl p v))) :
    IsNormalMap ψ := by
  intro S s hne hdir hs
  have hmono : ∀ a b : V, a ≤ b → ψ a ≤ ψ b := fun a b h => by
    have := hψ _ (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this
  refine ⟨by rintro _ ⟨x, hx, rfl⟩; exact hmono _ _ (hs.1 hx), fun b hb => ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h1 := hω S s hne hdir hs
  have h2 := hω _ _ (hne.image _) (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨z, hz, h1, h2⟩ := hdir a ha c hc
    exact ⟨_, ⟨z, hz, rfl⟩, refl_mono hp h1, refl_mono hp h2⟩) (refl_isLUB hp hs)
  obtain ⟨_, ⟨d1, hd1, rfl⟩, hlt1, -⟩ := h1.exists_between (sub_lt_self (ω.toLin s) hε)
  obtain ⟨_, ⟨_, ⟨d2, hd2, rfl⟩, rfl⟩, hlt2, -⟩ :=
    h2.exists_between (sub_lt_self (ω.toLin (peirceRefl p s)) hε)
  obtain ⟨d, hd, hd1d, hd2d⟩ := hdir d1 hd1 d2 hd2
  have hsd : 0 ≤ s - d := sub_nonneg.2 (hs.1 hd)
  have e1 := hdom _ hsd
  have m1 := state_mono ω hd1d
  have m2 := state_mono ω (refl_mono hp hd2d)
  simp only [map_sub] at e1
  have hbd := hb ⟨d, hd, rfl⟩
  linarith

/-- `ω ∘ P₁(p)` is a normal positive functional. -/
theorem isNormal_P1 (hp : p * p = p) (ω : OUSState V) (hω : IsNormalMap ω.toLin) :
    IsNormalMap (ω.toLin ∘ₗ P1 p) :=
  isNormal_of_dom hp ω hω _ (fun v hv => ω.nonneg (P1 p v) (P1_nonneg hp hv)) fun v hv => by
    have := state_mono ω (P1_le hp hv)
    rw [map_smul, map_add, smul_eq_mul] at this; exact this

/-- `ω ∘ P₀(p)` is a normal positive functional. -/
theorem isNormal_P0 (hp : p * p = p) (ω : OUSState V) (hω : IsNormalMap ω.toLin) :
    IsNormalMap (ω.toLin ∘ₗ P0 p) :=
  isNormal_of_dom hp ω hω _ (fun v hv => ω.nonneg (P0 p v) (P0_nonneg hp hv)) fun v hv => by
    have := state_mono ω (P0_le hp hv)
    rw [map_smul, map_add, smul_eq_mul] at this; exact this

/-- A normal positive functional converges along increasing sequences. -/
theorem normal_pos_tendsto (ψ : V →ₗ[ℝ] ℝ) (hψ : ∀ v, 0 ≤ v → 0 ≤ ψ v) (hn : IsNormalMap ψ)
    {x : ℕ → V} (hx : Monotone x) {s : V} (hs : IsLUB (Set.range x) s) :
    Tendsto (fun n => ψ (s - x n)) atTop (𝓝 0) := by
  have h := hn (Set.range x) s (Set.range_nonempty x) (directedOn_range.2 hx.directed_le) hs
  rw [← Set.range_comp] at h
  have ht := tendsto_atTop_isLUB (f := ψ ∘ x) (fun m n hmn => by
    have := hψ _ (sub_nonneg.2 (hx hmn)); rwa [map_sub, sub_nonneg] at this) h
  have := (tendsto_const_nhds (x := ψ s)).sub ht
  simp only [sub_self] at this
  simpa [map_sub] using this

/-- **`L_p` is weakly continuous along increasing sequences** (after one more
multiplication): if `xₙ ↑ s` in `[0,1]` then `ω(p (c (s - xₙ))) → 0` for normal `ω`. -/
theorem tendsto_idem_mul (hp : p * p = p) (ω : OUSState V) (hω : IsNormalMap ω.toLin)
    {x : ℕ → V} (hx : Monotone x) (h0 : ∀ n, 0 ≤ x n) {s : V} (hs : IsLUB (Set.range x) s)
    (hs1 : s ≤ ouUnit V) (c : V) :
    Tendsto (fun n => ω.toLin (p * (c * (s - x n)))) atTop (𝓝 0) := by
  have hd0 : ∀ n, 0 ≤ s - x n := fun n => sub_nonneg.2 (hs.1 ⟨n, rfl⟩)
  have hd1 : ∀ n, s - x n ≤ ouUnit V := fun n => (sub_le_self _ (h0 n)).trans hs1
  have key : ∀ (ψ : V →ₗ[ℝ] ℝ), (∀ v, 0 ≤ v → 0 ≤ ψ v) → IsNormalMap ψ →
      Tendsto (fun n => ψ (c * (s - x n))) atTop (𝓝 0) := fun ψ hψ hn =>
    tendsto_mul_zero ψ hψ hd0 hd1 (normal_pos_tendsto ψ hψ hn hx hs) c
  have t1 := key (ω.toLin ∘ₗ P1 p) (fun v hv => ω.nonneg (P1 p v) (P1_nonneg hp hv))
    (isNormal_P1 hp ω hω)
  have t0 := key (ω.toLin ∘ₗ P0 p) (fun v hv => ω.nonneg (P0 p v) (P0_nonneg hp hv))
    (isNormal_P0 hp ω hω)
  have tω := key _ ω.nonneg hω
  have := ((t1.sub t0).add tω).const_mul (2⁻¹ : ℝ)
  simp only [sub_zero, add_zero, mul_zero] at this
  refine this.congr fun n => ?_
  rw [L_eq (p := p) (c * (s - x n)), map_smul, map_add, map_sub, smul_eq_mul]
  rfl

end IdemNormal

/-! ## 4. Spectral projections `sproj a g` (projection onto `{g > 0}` in `W(a)`) -/

section Real

theorem real_min_sub {u N : ℝ} (hu : 0 ≤ u) (hN : 0 < N) :
    0 ≤ u * (1 - min (N * u) 1) ∧ u * (1 - min (N * u) 1) ≤ 1 / N := by
  rcases le_total (N * u) 1 with h | h
  · rw [min_eq_left h]
    refine ⟨mul_nonneg hu (by linarith), ?_⟩
    rw [le_div_iff₀ hN]; nlinarith [mul_nonneg hN.le hu]
  · rw [min_eq_right h, sub_self, mul_zero]; exact ⟨le_rfl, by positivity⟩

theorem real_min_factor {u N : ℝ} (_hu : 0 ≤ u) (_hN : 0 < N) :
    min (N * u) 1 = u * (N / max (N * u) 1) := by
  rcases le_total (N * u) 1 with h | h
  · rw [min_eq_left h, max_eq_right h, div_one, mul_comm]
  · rw [min_eq_right h, max_eq_left h]
    have : N * u ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    rw [← mul_div_assoc, mul_comm u N, div_self this]

theorem real_T3 {u : ℝ} (_hu : 0 ≤ u) :
    min u 1 - min u 1 * min u 1 ≤ min (2 * u) 1 - min u 1 := by
  rcases le_total u 1 with h | h
  · rcases le_total (2 * u) 1 with h' | h'
    · rw [min_eq_left h, min_eq_left h']; nlinarith
    · rw [min_eq_left h, min_eq_right h']; nlinarith [sq_nonneg (1 - u)]
  · rw [min_eq_right h, min_eq_right (by linarith : 1 ≤ 2 * u)]; norm_num

end Real

section CfcExtra

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

theorem jbCfc_sub (a : V) (f g : C(jbSpec a, ℝ)) : jbCfc a (f - g) = jbCfc a f - jbCfc a g := by
  simp [jbCfc, map_sub]

theorem jbCfc_zero (a : V) : jbCfc a 0 = 0 := by simp [jbCfc]

theorem jbCfc_le_iff (a : V) (f g : C(jbSpec a, ℝ)) : jbCfc a f ≤ jbCfc a g ↔ ∀ t, f t ≤ g t := by
  rw [← sub_nonneg, ← jbCfc_sub, jbCfc_nonneg_iff]
  simp only [ContinuousMap.sub_apply, sub_nonneg]

/-- States are continuous along uniformly convergent calculus sequences. -/
theorem tendsto_state_cfc (ω : OUSState V) (a : V) {f : ℕ → C(jbSpec a, ℝ)}
    {f0 : C(jbSpec a, ℝ)} {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∀ n t, |f n t - f0 t| ≤ C * (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ω.toLin (jbCfc a (f n))) atTop (𝓝 (ω.toLin (jbCfc a f0))) := by
  have hC : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) hC
  rw [norm_norm, Real.norm_eq_abs, ← map_sub, ← jbCfc_sub]
  refine (abs_state_le ω.toLin ω.nonneg ω.unital _).trans ?_
  rw [ousNorm_jbCfc]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  rw [Real.norm_eq_abs]; exact h n t

end CfcExtra

section SProj

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- Varying first factor: `ω(yₙ dₙ) → 0` if `0 ≤ yₙ ≤ M`, `0 ≤ dₙ ≤ 1`, `ω(dₙ) → 0`. -/
theorem tendsto_mul_zero' (ω : OUSState V) {M : ℝ} (hM : 0 ≤ M) {y d : ℕ → V}
    (hy0 : ∀ n, 0 ≤ y n) (hyM : ∀ n, y n ≤ M • ouUnit V) (hd0 : ∀ n, 0 ≤ d n)
    (hd1 : ∀ n, d n ≤ ouUnit V) (hlim : Tendsto (fun n => ω.toLin (d n)) atTop (𝓝 0)) :
    Tendsto (fun n => ω.toLin (y n * d n)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n => Real.sqrt (M * M * ω.toLin (d n))) atTop (𝓝 0) := by
    simpa using (hlim.const_mul (M * M)).sqrt
  refine squeeze_zero_norm (fun n => ?_) hg
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h1 := cs_bound ω.toLin ω.nonneg (y n) (hd0 n) (M := 1) (by rw [one_smul]; exact hd1 n)
  have h2 : ω.toLin (y n * y n) ≤ M * ω.toLin (y n) := by
    have := state_mono ω (sq_le_smul (hy0 n) (hyM n)); rwa [map_smul, smul_eq_mul] at this
  have h3 : ω.toLin (y n) ≤ M := by
    have := state_mono ω (hyM n); rwa [map_smul, ω.unital, smul_eq_mul, mul_one] at this
  have h4 : 0 ≤ ω.toLin (d n) := ω.nonneg _ (hd0 n)
  have h5 : 0 ≤ ω.toLin (y n) := ω.nonneg _ (hy0 n)
  calc ω.toLin (y n * d n) ^ 2 ≤ ω.toLin (y n * y n) * (1 * ω.toLin (d n)) := h1
    _ ≤ (M * M) * ω.toLin (d n) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_left h3 hM)) h4
    _ = M * M * ω.toLin (d n) := rfl

variable {a : V}

/-- `min((n+1) g, 1)` on `sp(a)`. -/
def sfun (g : C(jbSpec a, ℝ)) (n : ℕ) : C(jbSpec a, ℝ) :=
  ⟨fun t => min (((n : ℝ) + 1) * g t) 1, (continuous_const.mul g.continuous).min continuous_const⟩

theorem sfun_apply (g : C(jbSpec a, ℝ)) (n : ℕ) (t : jbSpec a) :
    sfun g n t = min (((n : ℝ) + 1) * g t) 1 := rfl

/-- `min((n+1) g, 1)(a)`, increasing to the spectral projection of `{g > 0}`. -/
def sseq (g : C(jbSpec a, ℝ)) (n : ℕ) : V := jbCfc a (sfun g n)

variable {g : C(jbSpec a, ℝ)}

theorem sfun_nonneg (hg : ∀ t, 0 ≤ g t) (n : ℕ) (t : jbSpec a) : 0 ≤ sfun g n t :=
  le_min (mul_nonneg (by positivity) (hg t)) zero_le_one

theorem sseq_nonneg (hg : ∀ t, 0 ≤ g t) (n : ℕ) : 0 ≤ sseq g n :=
  (jbCfc_nonneg_iff a _).2 (sfun_nonneg hg n)

theorem sseq_le_one (n : ℕ) : sseq g n ≤ ouUnit V := by
  rw [sseq, ← jbCfc_one a, jbCfc_le_iff]
  intro t; exact min_le_right _ _

theorem sseq_mono (hg : ∀ t, 0 ≤ g t) : Monotone (sseq g) := by
  intro m n hmn
  rw [sseq, sseq, jbCfc_le_iff]
  intro t
  simp only [sfun_apply]
  refine min_le_min_right _ (mul_le_mul_of_nonneg_right ?_ (hg t))
  have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  linarith

theorem exists_sproj (hg : ∀ t, 0 ≤ g t) :
    ∃ s, IsLUB (Set.range (sseq g)) s ∧ s ∈ Set.Icc 0 (ouUnit V) :=
  exists_isLUB_seq (sseq_mono hg) (sseq_nonneg hg) sseq_le_one

/-- **The spectral projection** of `a` for the open set `{g > 0}` (`g ≥ 0` on `sp(a)`):
the supremum of `min((n+1) g, 1)(a)` (H-O–S 4.2.x; for `g = t⁺` and `a ≥ 0` it is the
range projection `r(a)`). -/
def sproj (g : C(jbSpec a, ℝ)) : V :=
  haveI := Classical.propDecidable (∀ t, 0 ≤ g t)
  if hg : ∀ t, 0 ≤ g t then Classical.choose (exists_sproj hg) else 0

theorem sproj_spec (hg : ∀ t, 0 ≤ g t) :
    IsLUB (Set.range (sseq g)) (sproj g) ∧ sproj g ∈ Set.Icc 0 (ouUnit V) := by
  unfold sproj
  split_ifs
  exact Classical.choose_spec (exists_sproj hg)

theorem sproj_isLUB (hg : ∀ t, 0 ≤ g t) : IsLUB (Set.range (sseq g)) (sproj g) :=
  (sproj_spec hg).1

theorem sproj_nonneg (hg : ∀ t, 0 ≤ g t) : 0 ≤ sproj g := (sproj_spec hg).2.1

theorem sproj_le_one (hg : ∀ t, 0 ≤ g t) : sproj g ≤ ouUnit V := (sproj_spec hg).2.2

/-- `ω(sseq n) → ω(sproj)`. -/
theorem tendsto_sseq (hg : ∀ t, 0 ≤ g t) {ω : OUSState V} (hω : IsNormalMap ω.toLin) :
    Tendsto (fun n => ω.toLin (sseq g n)) atTop (𝓝 (ω.toLin (sproj g))) :=
  normal_tendsto (sseq_mono hg) (sproj_isLUB hg) hω

theorem tendsto_sproj_sub (hg : ∀ t, 0 ≤ g t) {ω : OUSState V} (hω : IsNormalMap ω.toLin) :
    Tendsto (fun n => ω.toLin (sproj g - sseq g n)) atTop (𝓝 0) := by
  have := (tendsto_const_nhds (x := ω.toLin (sproj g))).sub (tendsto_sseq hg hω)
  simpa [map_sub] using this

theorem sproj_sub_nonneg (hg : ∀ t, 0 ≤ g t) (n : ℕ) : 0 ≤ sproj g - sseq g n :=
  sub_nonneg.2 ((sproj_isLUB hg).1 ⟨n, rfl⟩)

theorem sproj_sub_le (hg : ∀ t, 0 ≤ g t) (n : ℕ) : sproj g - sseq g n ≤ ouUnit V :=
  (sub_le_self _ (sseq_nonneg hg n)).trans (sproj_le_one hg)

/-- **Weak limits against a fixed element**: `ω(y · sseq n) → ω(y · sproj)`. -/
theorem tendsto_mul_sseq (hg : ∀ t, 0 ≤ g t) {ω : OUSState V} (hω : IsNormalMap ω.toLin)
    (y : V) : Tendsto (fun n => ω.toLin (y * sseq g n)) atTop (𝓝 (ω.toLin (y * sproj g))) := by
  have h := tendsto_mul_zero ω.toLin ω.nonneg (sproj_sub_nonneg hg) (sproj_sub_le hg)
    (tendsto_sproj_sub hg hω) y
  have := (tendsto_const_nhds (x := ω.toLin (y * sproj g))).sub h
  simp only [sub_zero] at this
  refine this.congr fun n => ?_
  rw [jb_mul_sub, map_sub]; ring

/-- **`sproj a g` is an idempotent.**  With `xₙ = sseq n ↑ p`: `ω(xₙ²) → ω(p²)` by
Cauchy–Schwarz (`p² - xₙ² = (p + xₙ)(p - xₙ)`), and `0 ≤ xₙ - xₙ² ≤ x₂ₙ₊₁ - xₙ`
(calculus), so `ω(xₙ²) → ω(p)`; normal states separate. -/
theorem sproj_idem (hg : ∀ t, 0 ≤ g t) : sproj g * sproj g = sproj g := by
  set p := sproj g with hpdef
  set x := sseq g with hxdef
  refine eq_of_normal fun ω hω => ?_
  have T1 : Tendsto (fun n => ω.toLin (x n)) atTop (𝓝 (ω.toLin p)) := tendsto_sseq hg hω
  have T2 : Tendsto (fun n => ω.toLin ((p + x n) * (p - x n))) atTop (𝓝 0) :=
    tendsto_mul_zero' ω (M := 2) (by norm_num) (fun n => add_nonneg (sproj_nonneg hg)
      (sseq_nonneg hg n)) (fun n => by
        rw [two_smul]; exact add_le_add (sproj_le_one hg) (sseq_le_one n))
      (sproj_sub_nonneg hg) (sproj_sub_le hg) (tendsto_sproj_sub hg hω)
  have e : ∀ n, (p + x n) * (p - x n) = p * p - x n * x n := by
    intro n
    simp only [JBAlgebra.add_mul, jb_mul_sub, JBAlgebra.mul_comm (x n) p]; abel
  have T2' : Tendsto (fun n => ω.toLin (x n * x n)) atTop (𝓝 (ω.toLin (p * p))) := by
    have := (tendsto_const_nhds (x := ω.toLin (p * p))).sub T2
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [e, map_sub]; ring
  have hsq : ∀ n, x n * x n = jbCfc a (sfun g n * sfun g n) := fun n => by
    rw [jbCfc_mul]; rfl
  have hle : ∀ n, x n - x n * x n ≤ x (2 * n + 1) - x n := by
    intro n
    rw [hsq, hxdef, sseq, sseq, ← jbCfc_sub, ← jbCfc_sub, jbCfc_le_iff]
    intro t
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, sfun_apply]
    have e2 : ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by push_cast; ring
    rw [e2, mul_assoc]
    exact real_T3 (mul_nonneg (by positivity) (hg t))
  have hge : ∀ n, 0 ≤ x n - x n * x n := by
    intro n
    rw [hsq, hxdef, sseq, ← jbCfc_sub, jbCfc_nonneg_iff]
    intro t
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply]
    have h0 := sfun_nonneg hg n t
    have h1 : sfun g n t ≤ 1 := min_le_right _ _
    nlinarith
  have T1' : Tendsto (fun n => ω.toLin (x (2 * n + 1))) atTop (𝓝 (ω.toLin p)) :=
    T1.comp (tendsto_atTop_mono (f := id) (g := fun n : ℕ => 2 * n + 1)
      (fun n => by simp only [id]; omega) tendsto_id)
  have T3 : Tendsto (fun n => ω.toLin (x n - x n * x n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ω.nonneg _ (hge n)) (fun n => state_mono ω (hle n)) ?_
    have := T1'.sub T1
    simpa [map_sub] using this
  have T4 : Tendsto (fun n => ω.toLin (x n * x n)) atTop (𝓝 (ω.toLin p)) := by
    have := T1.sub T3
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [map_sub]; ring
  exact tendsto_nhds_unique T2' T4

/-- **`p_g` acts as the identity on `g · C(a)`**: `p_g (g h)(a) = (g h)(a)`, since
`‖min((n+1)g,1) g h - g h‖ ≤ ‖h‖/(n+1)`. -/
theorem sproj_mul_cfc (hg : ∀ t, 0 ≤ g t) (h : C(jbSpec a, ℝ)) :
    sproj g * jbCfc a (g * h) = jbCfc a (g * h) := by
  refine eq_of_normal fun ω hω => ?_
  have T := tendsto_mul_sseq hg hω (jbCfc a (g * h))
  have T' : Tendsto (fun n => ω.toLin (jbCfc a (g * h) * sseq g n)) atTop
      (𝓝 (ω.toLin (jbCfc a (g * h)))) := by
    have e : ∀ n, jbCfc a (g * h) * sseq g n = jbCfc a (sfun g n * (g * h)) := fun n => by
      rw [sseq, JBAlgebra.mul_comm, ← jbCfc_mul]
    simp only [e]
    refine tendsto_state_cfc ω a (C := ‖h‖) (norm_nonneg _) fun n t => ?_
    simp only [ContinuousMap.mul_apply, sfun_apply]
    obtain ⟨b0, b1⟩ := real_min_sub (hg t) (N := (n : ℝ) + 1) (by positivity)
    have hh : |h t| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm t
    have e2 : min (((n : ℝ) + 1) * g t) 1 * (g t * h t) - g t * h t =
        -(h t * (g t * (1 - min (((n : ℝ) + 1) * g t) 1))) := by ring
    rw [e2, abs_neg, abs_mul, abs_of_nonneg b0]
    exact mul_le_mul hh b1 b0 (norm_nonneg _)
  rw [JBAlgebra.mul_comm]
  exact tendsto_nhds_unique T T'

/-- `p_g h(a) = 0` when `g h = 0` on `sp(a)`. -/
theorem sproj_mul_cfc_eq_zero (hg : ∀ t, 0 ≤ g t) {h : C(jbSpec a, ℝ)}
    (hgh : ∀ t, g t * h t = 0) : sproj g * jbCfc a h = 0 := by
  refine eq_of_normal fun ω hω => ?_
  have T := tendsto_mul_sseq hg hω (jbCfc a h)
  have e : ∀ n, jbCfc a h * sseq g n = 0 := fun n => by
    rw [sseq, ← jbCfc_mul, ← jbCfc_zero a]
    congr 1
    ext t
    simp only [ContinuousMap.mul_apply, sfun_apply, ContinuousMap.zero_apply]
    rcases mul_eq_zero.1 (hgh t) with h0 | h0
    · rw [h0, mul_zero, min_eq_left zero_le_one, mul_zero]
    · rw [h0, zero_mul]
  simp only [e, map_zero] at T
  rw [JBAlgebra.mul_comm, map_zero]
  exact tendsto_nhds_unique T tendsto_const_nhds

/-- `sseq g n = g · kₙ` with `kₙ = (n+1)/max((n+1)g, 1)`. -/
theorem sfun_factor (hg : ∀ t, 0 ≤ g t) (n : ℕ) :
    ∃ k : C(jbSpec a, ℝ), sfun g n = g * k := by
  refine ⟨⟨fun t => ((n : ℝ) + 1) / max (((n : ℝ) + 1) * g t) 1,
    continuous_const.div ((continuous_const.mul g.continuous).max continuous_const)
      fun t => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'⟩, ?_⟩
  ext t
  simp only [sfun_apply, ContinuousMap.mul_apply, ContinuousMap.coe_mk]
  exact real_min_factor (N := (n : ℝ) + 1) (hg t) (by positivity)

/-- **`p_g` operator-commutes with `C(a)`**: every `c = h(a)` lies in `V₁(p) + V₀(p)`
(`P½(p) c = 0`).  Weak continuity of `L_p` gives `p(p c) = lim p(c xₙ)`, and
`c xₙ ∈ g · C(a)` is fixed by `p`. -/
theorem Ph_sproj_cfc (hg : ∀ t, 0 ≤ g t) (h : C(jbSpec a, ℝ)) : Ph (sproj g) (jbCfc a h) = 0 := by
  set p := sproj g
  set c := jbCfc a h
  have hp := sproj_idem hg
  have key : p * (p * c) = p * c := by
    refine eq_of_normal fun ω hω => ?_
    have T := tendsto_idem_mul hp ω hω (sseq_mono hg) (sseq_nonneg hg) (sproj_isLUB hg)
      (sproj_le_one hg) c
    have hfix : ∀ n, p * (c * sseq g n) = c * sseq g n := fun n => by
      obtain ⟨k, hk⟩ := sfun_factor hg n
      rw [sseq, ← jbCfc_mul, hk, show h * (g * k) = g * (h * k) by ring]
      exact sproj_mul_cfc hg _
    have T2 := tendsto_mul_sseq hg hω c
    have T3 : Tendsto (fun _ : ℕ => ω.toLin (p * (c * p))) atTop (𝓝 (ω.toLin (c * p))) := by
      have := T2.add T
      simp only [add_zero] at this
      refine this.congr fun n => ?_
      rw [jb_mul_sub, jb_mul_sub, hfix, map_sub]; ring
    rw [JBAlgebra.mul_comm p c]
    exact tendsto_nhds_unique tendsto_const_nhds T3
  rw [Ph_apply, key, sub_self]

/-- Nested spectral projections: `p_g p_{gk} = p_{gk}` for `k ≥ 0`. -/
theorem sproj_mul_sproj_factor (hg : ∀ t, 0 ≤ g t) {k : C(jbSpec a, ℝ)} (hk : ∀ t, 0 ≤ k t) :
    sproj g * sproj (g * k) = sproj (g * k) := by
  have hgk : ∀ t, 0 ≤ (g * k) t := fun t => mul_nonneg (hg t) (hk t)
  refine eq_of_normal fun ω hω => ?_
  have T := tendsto_mul_sseq hgk hω (sproj g)
  have e : ∀ n, sproj g * sseq (g * k) n = sseq (g * k) n := fun n => by
    obtain ⟨k', hk'⟩ := sfun_factor hgk n
    rw [sseq, hk', mul_assoc]
    exact sproj_mul_cfc hg _
  simp only [e] at T
  exact tendsto_nhds_unique T (tendsto_sseq hgk hω)

/-- Orthogonal spectral projections: `p_g p_h = 0` when `g h = 0`. -/
theorem sproj_mul_sproj_eq_zero (hg : ∀ t, 0 ≤ g t) {h : C(jbSpec a, ℝ)} (hh : ∀ t, 0 ≤ h t)
    (hgh : ∀ t, g t * h t = 0) : sproj g * sproj h = 0 := by
  refine eq_of_normal fun ω hω => ?_
  have T := tendsto_mul_sseq hh hω (sproj g)
  have e : ∀ n, sproj g * sseq h n = 0 := fun n => by
    refine sproj_mul_cfc_eq_zero hg fun t => ?_
    simp only [sfun_apply]
    rcases mul_eq_zero.1 (hgh t) with h0 | h0
    · rw [h0, zero_mul]
    · rw [h0, mul_zero, min_eq_left zero_le_one, mul_zero]
  simp only [e, map_zero] at T
  rw [map_zero]
  exact tendsto_nhds_unique T tendsto_const_nhds

/-- `p_g = 1` when `g > 0` on `sp(a)`. -/
theorem sproj_eq_one (hg : ∀ t, 0 < g t) : sproj g = ouUnit V := by
  have hg' : ∀ t, 0 ≤ g t := fun t => (hg t).le
  let k : C(jbSpec a, ℝ) := ⟨fun t => (g t)⁻¹, g.continuous.inv₀ fun t => (hg t).ne'⟩
  have e : g * k = 1 := by
    ext t; simp only [ContinuousMap.mul_apply, ContinuousMap.coe_mk, ContinuousMap.one_apply, k]
    exact mul_inv_cancel₀ (hg t).ne'
  have := sproj_mul_cfc hg' k
  rwa [e, jbCfc_one, JBAlgebra.mul_one] at this

/-- `p_g = 0` forces `g = 0` on `sp(a)`: `g(a) = p_g g(a)`. -/
theorem cfc_eq_zero_of_sproj (hg : ∀ t, 0 ≤ g t) (h0 : sproj g = 0) : jbCfc a g = 0 := by
  have := sproj_mul_cfc hg 1
  rwa [mul_one, h0, jb_zero_mul, eq_comm] at this

end SProj

/-! ## 5. Normal states are order-determining -/

section OrderDet

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

omit hW in
theorem isNormalMap_smul {ψ : V →ₗ[ℝ] ℝ} (hψ : IsNormalMap ψ) {c : ℝ} (hc : 0 < c) :
    IsNormalMap (c • ψ) := by
  intro S s hne hdir hs
  have h := hψ S s hne hdir hs
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (h.1 ⟨x, hx, rfl⟩) hc.le
  · simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [← le_div_iff₀' hc]
    refine h.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [le_div_iff₀' hc]
    have := hb ⟨x, hx, rfl⟩
    simpa using this

/-- The positive and negative parts `t⁺`, `t⁻` on `sp(y)`. -/
def posF (y : V) : C(jbSpec y, ℝ) := ⟨fun t => max t.1 0, continuous_subtype_val.max continuous_const⟩
def negF (y : V) : C(jbSpec y, ℝ) :=
  ⟨fun t => max (-t.1) 0, continuous_subtype_val.neg.max continuous_const⟩

/-- **Normal states are order-determining** (H-O–S 4.1-type): if `ω(y) ≥ 0` for every
normal state then `y ≥ 0`.  With `p` the spectral projection of `{y < 0}`,
`U_p y = p y = -y⁻`, and `ω ∘ U_p` is (a multiple of) a normal state, so `ω(y⁻) = 0` for
all normal `ω`. -/
theorem nonneg_of_normal {y : V} (h : ∀ ω : OUSState V, IsNormalMap ω.toLin → 0 ≤ ω.toLin y) :
    0 ≤ y := by
  have hg : ∀ t, 0 ≤ negF y t := fun t => le_max_right _ _
  set p := sproj (negF y) with hpdef
  have hp : p * p = p := sproj_idem hg
  have hdec : y = jbCfc y (posF y) - jbCfc y (negF y) := by
    rw [← jbCfc_sub]
    conv_lhs => rw [← jbCfc_id y]
    congr 1
    ext t
    simp only [specId, posF, negF, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
    rcases le_total t.1 0 with h0 | h0
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  have hneg : p * jbCfc y (negF y) = jbCfc y (negF y) := by
    have := sproj_mul_cfc hg 1; rwa [mul_one] at this
  have hpos : p * jbCfc y (posF y) = 0 := sproj_mul_cfc_eq_zero hg fun t => by
    simp only [posF, negF, ContinuousMap.coe_mk]
    rcases le_total t.1 0 with h0 | h0
    · rw [max_eq_right h0, mul_zero]
    · rw [max_eq_right (by linarith : -t.1 ≤ 0), zero_mul]
  have hPh : Ph p y = 0 := by
    have := Ph_sproj_cfc hg (specId y); rwa [jbCfc_id] at this
  have hP1 : P1 p y = -jbCfc y (negF y) := by
    rw [← mul_of_Ph hp hPh]
    conv_lhs => rw [hdec]
    rw [jb_mul_sub, hpos, hneg, zero_sub]
  have hn0 : 0 ≤ jbCfc y (negF y) := (jbCfc_nonneg_iff y _).2 hg
  have hzero : jbCfc y (negF y) = 0 := by
    refine eq_of_normal fun ω hω => ?_
    rw [map_zero]
    have hω0 : 0 ≤ ω.toLin (jbCfc y (negF y)) := ω.nonneg _ hn0
    rcases (ω.nonneg _ (sproj_nonneg hg)).lt_or_eq with hwp | hwp
    · -- `ω ∘ U_p / ω(p)` is a normal state
      set k := ω.toLin p
      let ω' : OUSState V :=
        { toLin := k⁻¹ • (ω.toLin ∘ₗ P1 p)
          nonneg := fun v hv => by
            simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
            exact mul_nonneg (inv_nonneg.2 hwp.le) (ω.nonneg _ (P1_nonneg hp hv))
          unital := by
            simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
            rw [P1_one hp]; exact inv_mul_cancel₀ hwp.ne' }
      have hn : IsNormalMap ω'.toLin := isNormalMap_smul (isNormal_P1 hp ω hω) (inv_pos.2 hwp)
      have := h ω' hn
      simp only [ω', LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, hP1, map_neg]
        at this
      have := (mul_nonneg_iff_of_pos_left (inv_pos.2 hwp)).1 this
      linarith
    · -- `ω(p) = 0`: Cauchy–Schwarz kills `ω(p y⁻)`
      have hcs := cs_ineq ω.toLin ω.nonneg p (jbCfc y (negF y))
      rw [hp, ← hwp, zero_mul, hneg] at hcs
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hcs (sq_nonneg _))
  rw [hdec, hzero, sub_zero]
  exact (jbCfc_nonneg_iff y _).2 fun t => le_max_right _ _

theorem le_of_normal {x y : V} (h : ∀ ω : OUSState V, IsNormalMap ω.toLin → ω.toLin x ≤ ω.toLin y) :
    x ≤ y :=
  sub_nonneg.1 (nonneg_of_normal fun ω hω => by rw [map_sub, sub_nonneg]; exact h ω hω)

end OrderDet

/-! ## 6. The spectral theorem: approximation by idempotents -/

section RealClamp

theorem clamp_sum {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : ∀ K : ℕ,
    ∑ j ∈ Finset.range K, min (max (x - j * δ) 0) δ = min (max x 0) (K * δ) := by
  intro K
  induction K with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul]
            exact (min_eq_right (le_max_right _ _)).symm
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have hK : 0 ≤ (K : ℝ) * δ := by positivity
    rcases le_total x (K * δ) with h | h
    · rw [max_eq_right (by linarith : x - K * δ ≤ 0), min_eq_left (le_max_right 0 δ |>.trans'
        le_rfl |> fun _ => hδ.le), add_zero]
      rw [min_eq_left (max_le h hK), min_eq_left (max_le (by linarith) (by positivity))]
    · rw [max_eq_left (by linarith : 0 ≤ x - K * δ), max_eq_left (hK.trans h),
        min_eq_right h]
      rcases le_total (x - K * δ) δ with h' | h'
      · rw [min_eq_left h', min_eq_left (by linarith)]; ring
      · rw [min_eq_right h', min_eq_right (by linarith)]; ring

theorem clamp_le_ramp {δ : ℝ} (hδ : 0 < δ) (x : ℝ) (n : ℕ) :
    min (max x 0) δ ≤ δ * min (((n : ℝ) + 1) * max x 0) 1 + 1 / ((n : ℝ) + 1) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, min_eq_left hδ.le, mul_zero, min_eq_left zero_le_one, mul_zero,
      zero_add]; exact h1
  · rw [max_eq_left hx]
    rcases le_total (((n : ℝ) + 1) * x) 1 with h | h
    · have : x ≤ 1 / ((n : ℝ) + 1) := by rw [le_div_iff₀ hN]; linarith
      have h2 : 0 ≤ δ * min (((n : ℝ) + 1) * x) 1 :=
        mul_nonneg hδ.le (le_min (by positivity) zero_le_one)
      linarith [min_le_left x δ]
    · rw [min_eq_right h, mul_one]; linarith [min_le_right x δ]

theorem ramp_le_clamp {δ : ℝ} (hδ : 0 < δ) (x : ℝ) (n : ℕ) :
    δ * min (((n : ℝ) + 1) * max (x - δ) 0) 1 ≤ min (max x 0) δ := by
  rcases le_total x δ with hx | hx
  · rw [max_eq_right (by linarith : x - δ ≤ 0), mul_zero, min_eq_left zero_le_one, mul_zero]
    exact le_min (le_max_right _ _) hδ.le
  · rw [min_eq_right (le_max_of_le_left hx)]
    calc δ * min (((n : ℝ) + 1) * max (x - δ) 0) 1 ≤ δ * 1 :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
      _ = δ := mul_one δ

end RealClamp

section Spectral

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

theorem jbCfc_sum (a : V) {ι : Type*} (s : Finset ι) (f : ι → C(jbSpec a, ℝ)) :
    jbCfc a (∑ i ∈ s, f i) = ∑ i ∈ s, jbCfc a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact jbCfc_zero a
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, jbCfc_add, ih]

variable (a : V) {δ : ℝ}

/-- The ramp `(t + ‖a‖ - jδ)⁺` on `sp(a)`. -/
def rampF (δ : ℝ) (j : ℕ) : C(jbSpec a, ℝ) :=
  ⟨fun t => max (t.1 + ousNorm V a - j * δ) 0,
    ((continuous_subtype_val.add continuous_const).sub continuous_const).max continuous_const⟩

/-- The clamp `min((t + ‖a‖ - jδ)⁺, δ)` on `sp(a)`. -/
def clampF (δ : ℝ) (j : ℕ) : C(jbSpec a, ℝ) :=
  ⟨fun t => min (max (t.1 + ousNorm V a - j * δ) 0) δ,
    (((continuous_subtype_val.add continuous_const).sub continuous_const).max
      continuous_const).min continuous_const⟩

theorem rampF_nonneg (j : ℕ) (t : jbSpec a) : 0 ≤ rampF a δ j t := le_max_right _ _

/-- `min((t + ‖a‖ - jδ)⁺, δ)(a) ≤ δ p_j` (archimedean closure of `≤ δ xₙ + 1/(n+1)`). -/
theorem clamp_le_proj (hδ : 0 < δ) (j : ℕ) :
    jbCfc a (clampF a δ j) ≤ δ • sproj (rampF a δ j) := by
  have hg := rampF_nonneg (δ := δ) a j
  have hn : ∀ n : ℕ, jbCfc a (clampF a δ j) ≤
      δ • sproj (rampF a δ j) + (1 / ((n : ℝ) + 1)) • ouUnit V := by
    intro n
    have h1 : jbCfc a (clampF a δ j) ≤ δ • sseq (rampF a δ j) n + (1 / ((n : ℝ) + 1)) • ouUnit V := by
      rw [sseq, ← jbCfc_smul, ← jbCfc_one a, ← jbCfc_smul, ← jbCfc_add, jbCfc_le_iff]
      intro t
      simp only [clampF, rampF, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one, sfun_apply, ContinuousMap.coe_mk]
      exact clamp_le_ramp hδ _ n
    exact h1.trans (add_le_add (ou_smul_le_smul hδ.le ((sproj_isLUB hg).1 ⟨n, rfl⟩)) le_rfl)
  refine sub_nonneg.1 (Papers.SEA.JBW.nonneg_of_forall_add fun ε hε => ?_)
  obtain ⟨n, hn'⟩ := exists_nat_one_div_lt hε
  have := sub_nonneg.2 (hn n)
  calc (0 : V) ≤ δ • sproj (rampF a δ j) + (1 / ((n : ℝ) + 1)) • ouUnit V - jbCfc a (clampF a δ j)
        := this
    _ = δ • sproj (rampF a δ j) - jbCfc a (clampF a δ j) + (1 / ((n : ℝ) + 1)) • ouUnit V := by
        abel
    _ ≤ δ • sproj (rampF a δ j) - jbCfc a (clampF a δ j) + ε • ouUnit V :=
        add_le_add le_rfl (ou_smul_unit_mono (X := V) hn'.le)

/-- `δ p_{j+1} ≤ min((t + ‖a‖ - jδ)⁺, δ)(a)` (least upper bound). -/
theorem proj_le_clamp (hδ : 0 < δ) (j : ℕ) :
    δ • sproj (rampF a δ (j + 1)) ≤ jbCfc a (clampF a δ j) := by
  have hg := rampF_nonneg (δ := δ) a (j + 1)
  have hle : sproj (rampF a δ (j + 1)) ≤ δ⁻¹ • jbCfc a (clampF a δ j) := by
    refine (sproj_isLUB hg).2 ?_
    rintro _ ⟨n, rfl⟩
    have : δ • sseq (rampF a δ (j + 1)) n ≤ jbCfc a (clampF a δ j) := by
      rw [sseq, ← jbCfc_smul, jbCfc_le_iff]
      intro t
      simp only [clampF, rampF, ContinuousMap.smul_apply, smul_eq_mul, sfun_apply,
        ContinuousMap.coe_mk]
      have e : t.1 + ousNorm V a - ((j + 1 : ℕ) : ℝ) * δ = (t.1 + ousNorm V a - j * δ) - δ := by
        push_cast; ring
      rw [e]
      exact ramp_le_clamp hδ _ n
    have := ou_smul_le_smul (inv_nonneg.2 hδ.le) this
    rwa [_root_.smul_smul, inv_mul_cancel₀ hδ.ne', one_smul] at this
  have := ou_smul_le_smul hδ.le hle
  rwa [_root_.smul_smul, mul_inv_cancel₀ hδ.ne', one_smul] at this

/-- The clamps add up to `a + ‖a‖` once `Kδ ≥ 2‖a‖`. -/
theorem sum_clamp (hδ : 0 < δ) {K : ℕ} (hK : 2 * ousNorm V a ≤ K * δ) :
    ∑ j ∈ Finset.range K, jbCfc a (clampF a δ j) = a + ousNorm V a • ouUnit V := by
  have e : (∑ j ∈ Finset.range K, clampF a δ j) = specId a + ousNorm V a • (1 : C(jbSpec a, ℝ)) := by
    ext t
    rw [ContinuousMap.sum_apply]
    simp only [clampF, ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, specId]
    have hs := jbSpec_subset a t.2
    have := clamp_sum hδ (t.1 + ousNorm V a) K
    simp only [sub_eq_add_neg] at this ⊢
    rw [this, max_eq_left (by linarith [hs.1]), min_eq_left (by linarith [hs.2])]
  rw [← jbCfc_sum, e, jbCfc_add, jbCfc_id, jbCfc_smul, jbCfc_one]

/-- **The spectral theorem** (H-O–S 4.2.3-type): every element `a` of a JBW-algebra is
within `δ` (in order, hence in norm) of `c·1 + δ Σ_{i<m} qᵢ` for idempotents `qᵢ`
operator-commuting with `a` (`P½(qᵢ) a = 0`): with `λ_j = -‖a‖ + jδ` and
`q_i = p_{λ_{i+1}}` the spectral projection of `{a > λ_{i+1}}`,
`δ Σ q_i ≤ a + ‖a‖ ≤ δ + δ Σ q_i`. -/
theorem spectral_approx (hδ : 0 < δ) :
    ∃ (m : ℕ) (q : ℕ → V) (c : ℝ), (∀ i, q i * q i = q i) ∧ (∀ i, Ph (q i) a = 0) ∧
      0 ≤ a - (c • ouUnit V + δ • ∑ i ∈ Finset.range m, q i) ∧
      a - (c • ouUnit V + δ • ∑ i ∈ Finset.range m, q i) ≤ δ • ouUnit V := by
  set M := ousNorm V a with hM
  set m := ⌈2 * M / δ⌉₊ with hm
  have hK : 2 * M ≤ ((m + 1 : ℕ) : ℝ) * δ := by
    have := Nat.le_ceil (2 * M / δ)
    rw [div_le_iff₀ hδ] at this
    push_cast
    nlinarith
  refine ⟨m, fun i => sproj (rampF a δ (i + 1)), -M, fun i => sproj_idem (rampF_nonneg a _),
    fun i => ?_, ?_, ?_⟩
  · have := Ph_sproj_cfc (rampF_nonneg (δ := δ) a (i + 1)) (specId a)
    rwa [jbCfc_id] at this
  · -- lower bound
    beta_reduce
    have hsum := sum_clamp a hδ hK
    rw [← hM] at hsum
    rw [Finset.sum_range_succ] at hsum
    have h1 : δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1)) ≤
        ∑ i ∈ Finset.range m, jbCfc a (clampF a δ i) := by
      rw [Finset.smul_sum]; exact Finset.sum_le_sum fun i _ => proj_le_clamp a hδ i
    have h2 : 0 ≤ jbCfc a (clampF a δ m) :=
      (jbCfc_nonneg_iff a _).2 fun t => le_min (le_max_right _ _) hδ.le
    have : δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1)) ≤ a + M • ouUnit V := by
      rw [← hsum]; exact h1.trans (le_add_of_nonneg_right h2)
    rw [neg_smul, sub_nonneg]
    calc -(M • ouUnit V) + δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1))
        ≤ -(M • ouUnit V) + (a + M • ouUnit V) := add_le_add le_rfl this
      _ = a := by abel
  · -- upper bound
    beta_reduce
    have hsum := sum_clamp a hδ hK
    rw [← hM] at hsum
    have h1 : ∑ j ∈ Finset.range (m + 1), jbCfc a (clampF a δ j) ≤
        δ • ∑ j ∈ Finset.range (m + 1), sproj (rampF a δ j) := by
      rw [Finset.smul_sum]; exact Finset.sum_le_sum fun j _ => clamp_le_proj a hδ j
    rw [hsum, Finset.sum_range_succ' (fun j => sproj (rampF a δ j)), smul_add] at h1
    have h0 : δ • sproj (rampF a δ 0) ≤ δ • ouUnit V :=
      ou_smul_le_smul hδ.le (sproj_le_one (rampF_nonneg a 0))
    have := h1.trans (add_le_add le_rfl h0)
    rw [neg_smul, sub_le_iff_le_add]
    calc a = a + M • ouUnit V - M • ouUnit V := by abel
      _ ≤ δ • ∑ i ∈ Finset.range m, sproj (rampF a δ (i + 1)) + δ • ouUnit V - M • ouUnit V :=
          sub_le_sub_right this _
      _ = δ • ouUnit V + (-(M • ouUnit V) + δ • ∑ i ∈ Finset.range m,
            sproj (rampF a δ (i + 1))) := by abel

/-- **Every element of a JBW-algebra is a norm limit of finite linear combinations of
idempotents operator-commuting with it.** -/
theorem spectral_approx_norm (hδ : 0 < δ) :
    ∃ (m : ℕ) (q : ℕ → V) (c : ℝ), (∀ i, q i * q i = q i) ∧ (∀ i, Ph (q i) a = 0) ∧
      ousNorm V (a - (c • ouUnit V + δ • ∑ i ∈ Finset.range m, q i)) ≤ δ := by
  obtain ⟨m, q, c, h1, h2, h3, h4⟩ := spectral_approx a hδ
  refine ⟨m, q, c, h1, h2, ousNorm_le_rc hδ.le ?_ h4⟩
  exact (neg_nonpos.2 (ou_smul_unit_nonneg hδ.le)).trans h3

end Spectral

/-! ## 7. Non-trivial idempotents -/

section Nontrivial

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **A JBW-algebra with a non-scalar element has a non-trivial idempotent**, which may
moreover be chosen operator-commuting with that element: split `sp(a)` at the midpoint
of two of its points. -/
theorem exists_nontrivial_idem (a : V) (ha : ∀ r : ℝ, a ≠ r • ouUnit V) :
    ∃ q : V, q * q = q ∧ q ≠ 0 ∧ q ≠ ouUnit V ∧ Ph q a = 0 := by
  have hpts : ∃ t1 t2 : jbSpec a, t1.1 < t2.1 := by
    by_contra hno
    push Not at hno
    rcases isEmpty_or_nonempty (jbSpec a) with he | hne
    · apply ha 0
      have : specId a = 0 := by ext t; exact he.elim t
      rw [zero_smul, ← jbCfc_id a, this, jbCfc_zero]
    · obtain ⟨t0⟩ := hne
      apply ha t0.1
      have : specId a = t0.1 • (1 : C(jbSpec a, ℝ)) := by
        ext t
        simp only [specId, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one]
        exact le_antisymm (hno t0 t) (hno t t0)
      calc a = jbCfc a (specId a) := (jbCfc_id a).symm
        _ = _ := by rw [this, jbCfc_smul, jbCfc_one]
  obtain ⟨t1, t2, h12⟩ := hpts
  set mid := (t1.1 + t2.1) / 2
  let g : C(jbSpec a, ℝ) := ⟨fun t => max (t.1 - mid) 0,
    (continuous_subtype_val.sub continuous_const).max continuous_const⟩
  let h : C(jbSpec a, ℝ) := ⟨fun t => max (mid - t.1) 0,
    (continuous_const.sub continuous_subtype_val).max continuous_const⟩
  have hg : ∀ t, 0 ≤ g t := fun t => le_max_right _ _
  refine ⟨sproj g, sproj_idem hg, fun h0 => ?_, fun h1 => ?_, ?_⟩
  · have := cfc_eq_zero_of_sproj hg h0
    rw [← jbCfc_zero a] at this
    have := congrArg (fun f : C(jbSpec a, ℝ) => f t2) (jbCfc_injective a this)
    simp only [g, ContinuousMap.coe_mk, ContinuousMap.zero_apply] at this
    have : t2.1 - mid ≤ 0 := by rw [← this]; exact le_max_left _ _
    simp only [mid] at this
    linarith
  · have hz := sproj_mul_cfc_eq_zero hg (h := h) fun t => by
      simp only [g, h, ContinuousMap.coe_mk]
      rcases le_total t.1 mid with ht | ht
      · rw [max_eq_right (by linarith : t.1 - mid ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : mid - t.1 ≤ 0), mul_zero]
    rw [h1, JBAlgebra.one_mul, ← jbCfc_zero a] at hz
    have := congrArg (fun f : C(jbSpec a, ℝ) => f t1) (jbCfc_injective a hz)
    simp only [h, ContinuousMap.coe_mk, ContinuousMap.zero_apply] at this
    have : mid - t1.1 ≤ 0 := by rw [← this]; exact le_max_left _ _
    simp only [mid] at this
    linarith
  · have := Ph_sproj_cfc hg (specId a)
    rwa [jbCfc_id] at this

end Nontrivial

/-! ## 8. The order on idempotents; the supremum of two idempotents -/

section IdemOrder

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- For `z ∈ V½(q)`: `P₀(q)(z²) = 0 ⇒ z = 0`.  Then `z² ∈ V₁(q)`, and the Jordan identity
`(zq) z² = z (q z²)` reads `½ z³ = z³`; `‖z⁴‖ = ‖z‖⁴` finishes. -/
theorem half_eq_zero {q z : V} (hq : q * q = q) (hz : z ∈ peirce q (1 / 2))
    (h0 : P0 q (z * z) = 0) : z = 0 := by
  have hPh : Ph q (z * z) = 0 := peirce_half_mul_half hq hz hz
  have hqz2 : q * (z * z) = z * z := by
    rw [mul_of_Ph hq hPh]
    have := peirce_decomp q (z * z)
    rw [hPh, h0, add_zero, add_zero] at this; exact this
  have hz' : z * q = (1 / 2 : ℝ) • z := by rw [JBAlgebra.mul_comm]; exact hz
  have hj := JBAlgebra.jordan z q
  rw [hz', hqz2, JBAlgebra.smul_mul] at hj
  have h3 : z * (z * z) = 0 := by
    have : (1 / 2 : ℝ) • (z * (z * z)) - z * (z * z) = 0 := by rw [hj, sub_self]
    have e : (1 / 2 : ℝ) • (z * (z * z)) - z * (z * z) = (-(1 / 2) : ℝ) • (z * (z * z)) := by
      module
    rw [e] at this
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have h4 : (z * z) * (z * z) = 0 := by
    have := jbPow_mul_jbPow z 2 2
    simp only [jbPow_succ, jbPow_zero, JBAlgebra.mul_one] at this
    rw [this, h3, jb_mul_zero]
  have n1 := jb_norm_mul_self (z * z)
  rw [h4, ousNorm_zero'] at n1
  have n2 : ousNorm V (z * z) = 0 := by
    have := ousNorm_nonneg_rc (z * z)
    nlinarith
  rw [jb_norm_mul_self] at n2
  exact IsOUS.norm_eq_zero z (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 n2)

/-- An idempotent `p` with `P₀(q) p = 0` lies in `V₁(q)`: `q p = p`. -/
theorem idem_mul_of_P0 {p q : V} (hp : p * p = p) (hq : q * q = q) (h0 : P0 q p = 0) :
    q * p = p := by
  have hdec : P1 q p + Ph q p = p := by
    have := peirce_decomp q p; rwa [h0, add_zero] at this
  set p1 := P1 q p
  set z := Ph q p
  have hz : z = 0 := by
    refine half_eq_zero hq (Ph_mem hq p) ?_
    have e : p * p = p1 * p1 + (2 : ℝ) • (p1 * z) + z * z := by
      rw [← hdec]; simp only [jadd_mul, jmul_add, JBAlgebra.mul_comm z p1]; module
    have := congrArg (P0 q) e
    rw [hp, h0, map_add, map_add, map_smul,
      P0_of_mem1 (peirce_one_mul_one hq (P1_mem hq p) (P1_mem hq p)),
      P0_of_memh (peirce_one_mul_half hq (P1_mem hq p) (Ph_mem hq p)), smul_zero, zero_add,
      zero_add] at this
    exact this.symm
  rw [hz, add_zero] at hdec
  rw [← hdec, P1_self hq]

theorem idem_nonneg {p : V} (hp : p * p = p) : 0 ≤ p := hp ▸ jb_sq_nonneg p

theorem idem_one_sub {p : V} (hp : p * p = p) : (ouUnit V - p) * (ouUnit V - p) = ouUnit V - p :=
  one_sub_idem JBAlgebra.one_mul hp

theorem idem_le_one {p : V} (hp : p * p = p) : p ≤ ouUnit V :=
  sub_nonneg.1 (idem_nonneg (idem_one_sub hp))

/-- **The order on idempotents** (H-O–S 4.2-type): `p ≤ q ⟺ q p = p`. -/
theorem idem_le_iff {p q : V} (hp : p * p = p) (hq : q * q = q) : p ≤ q ↔ q * p = p := by
  constructor
  · intro hpq
    refine idem_mul_of_P0 hp hq (le_antisymm ?_ (P0_nonneg hq (idem_nonneg hp)))
    have h1 := P0_nonneg hq (sub_nonneg.2 hpq)
    rw [map_sub, P0_of_mem1 (show q ∈ peirce q 1 by rw [mem_peirce, one_smul]; exact hq),
      zero_sub, neg_nonneg] at h1
    exact h1
  · intro h
    have hqp : (q - p) * (q - p) = q - p := by
      rw [jsub_mul, jmul_sub, jmul_sub, hq, hp, h, JBAlgebra.mul_comm p q, h]; abel
    exact sub_nonneg.1 (hqp ▸ jb_sq_nonneg _)

/-- An element of `V₁(e)` below `1` is below `e` (`U_e = P₁(e)` is positive). -/
theorem le_of_mem_one {e x : V} (he : e * e = e) (hx : x ∈ peirce e 1) (hx1 : x ≤ ouUnit V) :
    x ≤ e := by
  have := P1_nonneg he (sub_nonneg.2 hx1)
  rwa [map_sub, P1_one he, P1_of_mem1 hx, sub_nonneg] at this

end IdemOrder

section Sup2

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- `sp(a) ⊆ [0,∞)` makes `t⁺ = t` there. -/
theorem jbCfc_posF {a : V} (ha : 0 ≤ a) : jbCfc a (posF a) = a := by
  conv_rhs => rw [← jbCfc_id a]
  congr 1
  ext t
  simp only [posF, specId, ContinuousMap.coe_mk]
  exact max_eq_left (jbSpec_nonneg ha t.2)

/-- For `a ≥ 0`, the range projection `r(a) := p_{t⁺}` satisfies `r(a) a = a`, and it is
below every idempotent `e` with `e a = a`. -/
theorem rproj_spec {a : V} (ha : 0 ≤ a) :
    sproj (posF a) * sproj (posF a) = sproj (posF a) ∧ sproj (posF a) * a = a ∧
      ∀ e : V, e * e = e → e * a = a → sproj (posF a) ≤ e := by
  have hg : ∀ t, 0 ≤ posF a t := fun t => le_max_right _ _
  refine ⟨sproj_idem hg, ?_, fun e he hea => ?_⟩
  · have := sproj_mul_cfc hg 1; rwa [mul_one, jbCfc_posF ha] at this
  · refine (sproj_isLUB hg).2 ?_
    rintro _ ⟨n, rfl⟩
    have ha1 : a ∈ peirce e 1 := by rw [mem_peirce, one_smul]; exact hea
    obtain ⟨k, hk⟩ := sfun_factor hg n
    have hmem : sseq (posF a) n ∈ peirce e 1 := by
      rw [sseq, hk, jbCfc_mul, jbCfc_posF ha]
      have hk10 : Ph e (jbCfc a k) = 0 :=
        (mem_V10 he).1 (Ca_le (V10 he) ((mem_V10 he).2 (Ph_of_mem1 ha1)) (jbCfc_mem a k))
      rw [← decomp_of_Ph _ hk10, jmul_add, peirce_one_mul_zero he ha1 (P0_mem he _), add_zero]
      exact peirce_one_mul_one he ha1 (P1_mem he _)
    exact le_of_mem_one he hmem (sseq_le_one n)

/-- **The supremum of two idempotents** `p ∨ q := r(p + q)` (H-O–S 4.2-type): an idempotent
above `p` and `q` and below every idempotent above both. -/
def sup2 (p q : V) : V := sproj (posF (p + q))

theorem sup2_spec {p q : V} (hp : p * p = p) (hq : q * q = q) :
    sup2 p q * sup2 p q = sup2 p q ∧ p ≤ sup2 p q ∧ q ≤ sup2 p q ∧
      ∀ e : V, e * e = e → p ≤ e → q ≤ e → sup2 p q ≤ e := by
  have ha : 0 ≤ p + q := add_nonneg (idem_nonneg hp) (idem_nonneg hq)
  obtain ⟨hr, hra, hmin⟩ := rproj_spec ha
  set r := sup2 p q
  have hP0 : P0 r (p + q) = 0 := P0_of_mem1 (by rw [mem_peirce, one_smul]; exact hra)
  rw [map_add] at hP0
  have h1 := P0_nonneg hr (idem_nonneg hp)
  have h2 := P0_nonneg hr (idem_nonneg hq)
  have hp0 : P0 r p = 0 := le_antisymm (by
    calc P0 r p ≤ P0 r p + P0 r q := le_add_of_nonneg_right h2
      _ = 0 := hP0) h1
  have hq0 : P0 r q = 0 := le_antisymm (by
    calc P0 r q ≤ P0 r p + P0 r q := le_add_of_nonneg_left h1
      _ = 0 := hP0) h2
  refine ⟨hr, (idem_le_iff hp hr).2 (idem_mul_of_P0 hp hr hp0),
    (idem_le_iff hq hr).2 (idem_mul_of_P0 hq hr hq0), fun e he hpe hqe => hmin e he ?_⟩
  rw [jmul_add, (idem_le_iff hp he).1 hpe, (idem_le_iff hq he).1 hqe]

end Sup2

/-! ## 9. Centrality: fixed by every Peirce reflection ⟺ central -/

section Central

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- If `z ∈ V₁(e) + V₀(e)` then `L_e` and `L_z` commute (Peirce rules). -/
theorem comm_of_Ph {e z : V} (he : e * e = e) (hz : Ph e z = 0) (y : V) :
    e * (z * y) = z * (e * y) := by
  have hzd := decomp_of_Ph z hz
  have hyd := peirce_decomp e y
  have ma1 := P1_mem he z
  have ma0 := P0_mem he z
  have mb1 := P1_mem he y
  have mbh := Ph_mem he y
  have mb0 := P0_mem he y
  set a1 := P1 e z
  set a0 := P0 e z
  set b1 := P1 e y
  set bh := Ph e y
  set b0 := P0 e y
  have m11 : e * (a1 * b1) = a1 * b1 := by
    have := peirce_one_mul_one he ma1 mb1; rwa [mem_peirce, one_smul] at this
  have m1h : e * (a1 * bh) = (1 / 2 : ℝ) • (a1 * bh) := peirce_one_mul_half he ma1 mbh
  have m10 : a1 * b0 = 0 := peirce_one_mul_zero he ma1 mb0
  have m01 : a0 * b1 = 0 := by rw [JBAlgebra.mul_comm]; exact peirce_one_mul_zero he mb1 ma0
  have m0h : e * (a0 * bh) = (1 / 2 : ℝ) • (a0 * bh) := peirce_zero_mul_half he ma0 mbh
  have m00 : e * (a0 * b0) = 0 := by
    have := peirce_zero_mul_zero he ma0 mb0; rwa [mem_peirce, zero_smul] at this
  have e1 : e * b1 = b1 := by rw [mem_peirce, one_smul] at mb1; exact mb1
  have eh : e * bh = (1 / 2 : ℝ) • bh := mbh
  have e0 : e * b0 = 0 := by rw [mem_peirce, zero_smul] at mb0; exact mb0
  rw [← hzd, ← hyd]
  simp only [jadd_mul, jmul_add, jmul_smul, m11, m1h, m10, m01, m0h, m00, e1, eh, e0,
    add_zero, zero_add]
  module

/-- A central element commutes, in the Peirce sense, with every idempotent. -/
theorem Ph_of_central {c : V} (hc : ∀ x y : V, c * (x * y) = x * (c * y)) {e : V}
    (he : e * e = e) : Ph e c = 0 := by
  have h := hc e e
  rw [he, JBAlgebra.mul_comm c e] at h
  rw [Ph_apply, ← h, sub_self]

theorem refl_central {c : V} (hc : ∀ x y : V, c * (x * y) = x * (c * y)) {e : V}
    (he : e * e = e) : peirceRefl e c = c := by
  rw [peirceRefl_apply, Ph_of_central hc he, smul_zero, sub_zero]

end Central

section CentralW

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **An element in `V₁(e) + V₀(e)` for every idempotent `e` is central** (H-O–S 4.3-type):
`[L_z, L_x] = 0` for `x` a combination of idempotents, and every `x` is a norm limit of
such (the spectral theorem, `spectral_approx_norm`). -/
theorem central_of_Ph {z : V} (h : ∀ e : V, e * e = e → Ph e z = 0) (x y : V) :
    z * (x * y) = x * (z * y) := by
  let T : V →ₗ[ℝ] V :=
    { toFun := fun x => z * (x * y) - x * (z * y)
      map_add' := fun u v => by simp only [JBAlgebra.add_mul, jb_mul_add]; abel
      map_smul' := fun r u => by
        simp only [JBAlgebra.smul_mul, jb_mul_smul, RingHom.id_apply]; module }
  have hT : ∀ u, T u = z * (u * y) - u * (z * y) := fun u => rfl
  have hT1 : T (ouUnit V) = 0 := by rw [hT, JBAlgebra.one_mul, JBAlgebra.one_mul, sub_self]
  have hTe : ∀ e, e * e = e → T e = 0 := fun e he => by
    rw [hT, ← comm_of_Ph he (h e he) y, sub_self]
  have hbound : ∀ w, ousNorm V (T w) ≤ 2 * ousNorm V z * ousNorm V y * ousNorm V w := by
    intro w
    rw [hT, sub_eq_add_neg]
    refine (ousNorm_add_le _ _).trans ?_
    rw [ousNorm_neg]
    have h1 := jb_norm_mul_le z (w * y)
    have h2 := jb_norm_mul_le w y
    have h3 := jb_norm_mul_le w (z * y)
    have h4 := jb_norm_mul_le z y
    have nz := ousNorm_nonneg_rc z
    have nw := ousNorm_nonneg_rc w
    have ny := ousNorm_nonneg_rc y
    nlinarith [mul_le_mul_of_nonneg_left h2 nz, mul_le_mul_of_nonneg_left h4 nw]
  set K := 2 * ousNorm V z * ousNorm V y
  have hK : 0 ≤ K := by
    have := ousNorm_nonneg_rc z; have := ousNorm_nonneg_rc y; positivity
  have key : ∀ ε : ℝ, 0 < ε → ousNorm V (T x) ≤ K * ε := by
    intro ε hε
    obtain ⟨m, q, c, hq, -, hn⟩ := spectral_approx_norm x hε
    set s := c • ouUnit V + ε • ∑ i ∈ Finset.range m, q i
    have hs : T s = 0 := by
      simp only [s, map_add, map_smul, map_sum, hT1, smul_zero, zero_add]
      rw [Finset.sum_eq_zero fun i _ => hTe (q i) (hq i), smul_zero]
    have : T x = T (x - s) := by rw [map_sub, hs, sub_zero]
    rw [this]
    exact (hbound _).trans (mul_le_mul_of_nonneg_left hn hK)
  have h0 : ousNorm V (T x) = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (ousNorm_nonneg_rc _)
    have := key (ε / (K + 1)) (by positivity)
    rw [zero_add]
    refine this.trans ?_
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := IsOUS.norm_eq_zero _ h0
  rw [hT, sub_eq_zero] at this
  exact this

end CentralW

/-! ## 10. Directed and arbitrary suprema of idempotents; the central cover -/

section Sups

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **The supremum of a directed family of idempotents is an idempotent**: with `e ∈ D`
close to `s` under `ω`, `ω(s² - s) = ω((s + e)(s - e)) - ω(s - e)` and Cauchy–Schwarz. -/
theorem isLUB_idem {D : Set V} (hD : ∀ e ∈ D, e * e = e) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) {s : V} (hs : IsLUB D s) (hs1 : s ≤ ouUnit V) : s * s = s := by
  refine eq_of_normal fun ω hω => ?_
  have hl := hω D s hne hdir hs
  have bound : ∀ n : ℕ, |ω.toLin (s * s) - ω.toLin s| ≤
      Real.sqrt (2 * 2 * (1 / ((n : ℝ) + 1))) + 1 / ((n : ℝ) + 1) := by
    intro n
    have hη : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨e, he, rfl⟩, hlt, -⟩ := hl.exists_between (sub_lt_self (ω.toLin s) hη)
    have he0 : 0 ≤ e := hD e he ▸ jb_sq_nonneg e
    have hd0 : 0 ≤ s - e := sub_nonneg.2 (hs.1 he)
    have hd1 : s - e ≤ ouUnit V := (sub_le_self _ he0).trans hs1
    have hdη : ω.toLin (s - e) ≤ 1 / ((n : ℝ) + 1) := by rw [map_sub]; linarith
    have hdn : 0 ≤ ω.toLin (s - e) := ω.nonneg _ hd0
    have e1 : s * s - s = (s + e) * (s - e) - (s - e) := by
      simp only [JBAlgebra.add_mul, jb_mul_sub, JBAlgebra.mul_comm e s, hD e he]; abel
    have hcs : ω.toLin ((s + e) * (s - e)) ^ 2 ≤ 2 * 2 * (1 / ((n : ℝ) + 1)) := by
      have h1 := cs_bound ω.toLin ω.nonneg (s + e) hd0 (M := 1) (by rw [one_smul]; exact hd1)
      have hse0 : 0 ≤ s + e := add_nonneg (hs.1 he |>.trans' he0) he0
      have hse2 : s + e ≤ (2 : ℝ) • ouUnit V := by
        rw [two_smul]; exact add_le_add hs1 (hs.1 he |>.trans hs1)
      have h2 : ω.toLin ((s + e) * (s + e)) ≤ 2 * ω.toLin (s + e) := by
        have := state_mono ω (sq_le_smul hse0 hse2); rwa [map_smul, smul_eq_mul] at this
      have h3 : ω.toLin (s + e) ≤ 2 := by
        have := state_mono ω hse2; rwa [map_smul, ω.unital, smul_eq_mul, mul_one] at this
      have h4 : 0 ≤ ω.toLin ((s + e) * (s + e)) := ω.nonneg _ (jb_sq_nonneg _)
      calc _ ≤ ω.toLin ((s + e) * (s + e)) * (1 * ω.toLin (s - e)) := h1
        _ ≤ (2 * 2) * (1 / ((n : ℝ) + 1)) := by
          rw [one_mul]
          exact mul_le_mul (h2.trans (by linarith)) hdη hdn (by norm_num)
    have := Real.abs_le_sqrt hcs
    rw [← map_sub, e1, map_sub]
    calc |ω.toLin ((s + e) * (s - e)) - ω.toLin (s - e)|
        ≤ |ω.toLin ((s + e) * (s - e))| + |ω.toLin (s - e)| := abs_sub _ _
      _ ≤ _ := add_le_add this (by rw [abs_of_nonneg hdn]; exact hdη)
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (2 * 2 * (1 / ((n : ℝ) + 1))) + 1 / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    have t := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := ((t.const_mul (2 * 2)).sqrt).add t
    simpa using this
  have := ge_of_tendsto' hlim bound
  have := abs_nonpos_iff.1 this
  linarith

/-- `e` is the join of a finite subfamily of `F`. -/
def IsFinJoin (F : Set V) (e : V) : Prop :=
  e * e = e ∧ ∃ G : Finset V, (G : Set V) ⊆ F ∧ (∀ g ∈ G, g ≤ e) ∧
    ∀ u : V, u * u = u → (∀ g ∈ G, g ≤ u) → e ≤ u

/-- **The idempotents form a complete lattice** (H-O–S 4.2-type): every family of
idempotents has a least upper bound among the idempotents (the supremum of the directed
family of its finite joins). -/
theorem exists_sSup_idem (F : Set V) (hF : ∀ f ∈ F, f * f = f) :
    ∃ s : V, s * s = s ∧ (∀ f ∈ F, f ≤ s) ∧ ∀ u : V, u * u = u → (∀ f ∈ F, f ≤ u) → s ≤ u := by
  classical
  set D := {e | IsFinJoin F e}
  have h0 : (0 : V) ∈ D := ⟨jb_zero_mul 0, ∅, by simp, by simp, fun u hu _ => idem_nonneg hu⟩
  have hFD : ∀ f ∈ F, f ∈ D := fun f hf => ⟨hF f hf, {f}, by simpa using hf, by simp,
    fun u _ hu => hu f (Finset.mem_singleton_self f)⟩
  have hD01 : D ⊆ Set.Icc 0 (ouUnit V) := fun e he => ⟨idem_nonneg he.1, idem_le_one he.1⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro e1 ⟨he1, G1, hG1F, hG1e, hG1m⟩ e2 ⟨he2, G2, hG2F, hG2e, hG2m⟩
    obtain ⟨hr, h1, h2, hmin⟩ := sup2_spec he1 he2
    refine ⟨sup2 e1 e2, ⟨hr, G1 ∪ G2, ?_, ?_, ?_⟩, h1, h2⟩
    · rw [Finset.coe_union]; exact Set.union_subset hG1F hG2F
    · intro g hg
      rcases Finset.mem_union.1 hg with hg | hg
      · exact (hG1e g hg).trans h1
      · exact (hG2e g hg).trans h2
    · intro u hu hGu
      exact hmin u hu (hG1m u hu fun g hg => hGu g (Finset.mem_union_left _ hg))
        (hG2m u hu fun g hg => hGu g (Finset.mem_union_right _ hg))
  obtain ⟨s, hs, hs01⟩ := exists_isLUB_unit hD01 ⟨0, h0⟩ hdir
  refine ⟨s, isLUB_idem (fun e he => he.1) ⟨0, h0⟩ hdir hs hs01.2,
    fun f hf => hs.1 (hFD f hf), fun u hu hFu => hs.2 fun e he => ?_⟩
  obtain ⟨-, G, hGF, -, hGm⟩ := he
  exact hGm u hu fun g hg => hFu g (hGF hg)

/-- A composite of Peirce reflections. -/
def reflList : List V → V → V
  | [], x => x
  | e :: L, x => peirceRefl e (reflList L x)

theorem reflList_mul (L : List V) (hL : ∀ e ∈ L, e * e = e) (x y : V) :
    reflList L (x * y) = reflList L x * reflList L y := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [reflList]
    rw [ih fun f hf => hL f (List.mem_cons_of_mem e hf),
      peirceRefl_mul (hL e (List.mem_cons_self))]

theorem reflList_mono (L : List V) (hL : ∀ e ∈ L, e * e = e) {x y : V} (h : x ≤ y) :
    reflList L x ≤ reflList L y := by
  induction L with
  | nil => exact h
  | cons e L ih =>
    exact refl_mono (hL e List.mem_cons_self) (ih fun f hf => hL f (List.mem_cons_of_mem e hf))

theorem reflList_central (L : List V) (hL : ∀ e ∈ L, e * e = e) {z : V}
    (hz : ∀ x y : V, z * (x * y) = x * (z * y)) : reflList L z = z := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [reflList]
    rw [ih fun f hf => hL f (List.mem_cons_of_mem e hf), refl_central hz (hL e List.mem_cons_self)]

/-- **The central cover** `c(p)` of an idempotent (H-O–S 4.3-type): the least central
idempotent above `p`, built as the supremum of the orbit of `p` under the group generated by
the Peirce reflections `σ_e = U_{2e-1}`; the supremum is fixed by every `σ_e`, hence central
(`central_of_Ph`). -/
theorem exists_central_cover {p : V} (hp : p * p = p) :
    ∃ c : V, c * c = c ∧ (∀ x y : V, c * (x * y) = x * (c * y)) ∧ p ≤ c ∧
      ∀ z : V, z * z = z → (∀ x y : V, z * (x * y) = x * (z * y)) → p ≤ z → c ≤ z := by
  set O := {x : V | ∃ L : List V, (∀ e ∈ L, e * e = e) ∧ x = reflList L p}
  have hO : ∀ x ∈ O, x * x = x := by
    rintro _ ⟨L, hL, rfl⟩; rw [← reflList_mul L hL, hp]
  obtain ⟨c, hc, hcO, hcmin⟩ := exists_sSup_idem O hO
  have hpO : p ∈ O := ⟨[], by simp, rfl⟩
  have hfix : ∀ e : V, e * e = e → peirceRefl e c = c := by
    intro e he
    have hσc : peirceRefl e c * peirceRefl e c = peirceRefl e c := by
      rw [← peirceRefl_mul he, hc]
    have h1 : c ≤ peirceRefl e c := hcmin _ hσc fun x hx => by
      obtain ⟨L, hL, rfl⟩ := hx
      have hmem : peirceRefl e (reflList L p) ∈ O :=
        ⟨e :: L, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact he
          · exact hL f hf, rfl⟩
      have := refl_mono he (hcO _ hmem)
      rwa [peirceRefl_peirceRefl he] at this
    have h2 := refl_mono he h1
    rw [peirceRefl_peirceRefl he] at h2
    exact le_antisymm h2 h1
  have hPh : ∀ e : V, e * e = e → Ph e c = 0 := by
    intro e he
    have := hfix e he
    rw [peirceRefl_apply, sub_eq_self] at this
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  refine ⟨c, hc, central_of_Ph hPh, hcO p hpO, fun z hz hzc hpz => hcmin z hz ?_⟩
  rintro _ ⟨L, hL, rfl⟩
  have := reflList_mono L hL hpz
  rwa [reflList_central L hL hzc] at this

/-- The central cover as a `CentralIdem` (REC 52's central idempotents, `JBWSEA.lean`). -/
def centralCover {p : V} (hp : p * p = p) : Papers.SEA.JBW.CentralIdem V where
  c := Classical.choose (exists_central_cover hp)
  idem := (Classical.choose_spec (exists_central_cover hp)).1
  central := (Classical.choose_spec (exists_central_cover hp)).2.1

theorem centralCover_spec {p : V} (hp : p * p = p) :
    p ≤ (centralCover hp).c ∧ ∀ z : Papers.SEA.JBW.CentralIdem V, p ≤ z.c →
      (centralCover hp).c ≤ z.c :=
  ⟨(Classical.choose_spec (exists_central_cover hp)).2.2.1, fun z hz =>
    (Classical.choose_spec (exists_central_cover hp)).2.2.2 z.c z.idem z.central hz⟩

end Sups

/-! ## 11. Purely exceptional algebras have no associative (type I₁) central summand -/

section NoI1

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- `C(X, ℝ) → C(X, ℂ)`, as a real-linear map. -/
def ofRealL (X : Type u) [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun f := ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  map_add' f g := by ext t; simp
  map_smul' r f := by ext t; simp

omit hJ in
@[simp] theorem ofRealL_apply {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) (t : X) :
    ofRealL X f t = (f t : ℂ) := rfl

/-- **A non-zero central summand of a purely exceptional JB-algebra is not associative**
(so a purely exceptional JBW-algebra has no type I₁ part): an associative summand `cV`
would give the non-zero Jordan homomorphism `x ↦ Γ(cx)` into the C*-algebra `C(X, ℂ)`,
`X` the character space of `cV` (non-empty since `cV ≠ 0`). -/
theorem centralIdem_not_assoc (hpe : IsPurelyExceptional.{u, u} V)
    (e : Papers.SEA.JBW.CentralIdem V) (he : e.c ≠ 0) :
    ¬ ∀ x y z : e.Corner, x * y * z = x * (y * z) := by
  intro hB
  let X := charSet e.Corner
  let φ : V →ₗ[ℝ] C(X, ℂ) := ofRealL X ∘ₗ gelfandL ∘ₗ e.proj
  have hφ : ∀ x, φ x = ofRealL X (gelfand (e.proj x)) := fun x => rfl
  have hjh : IsJordanHomInto V C(X, ℂ) φ := by
    refine ⟨fun a => ?_, fun a b => ?_⟩
    · rw [hφ]; ext t
      simp only [ContinuousMap.star_apply, ofRealL_apply]
      exact Complex.conj_ofReal _
    · rw [hφ, hφ, hφ, e.proj_mul, gelfand_mul]
      ext t
      simp only [ofRealL_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
        ContinuousMap.add_apply, Complex.ofReal_mul]
      rw [Complex.real_smul]; push_cast; ring
  have h0 := hpe C(X, ℂ) φ hjh
  have hne : ouUnit e.Corner ≠ 0 := fun h => he (by
    have := congrArg Subtype.val h; rwa [Papers.SEA.JBW.CentralIdem.unit_val] at this)
  obtain ⟨f, hf, hfb⟩ := exists_state_abs_eq_norm hne
  obtain ⟨χ, hχ, -⟩ := exists_char_eq hB hfb ⟨f, hf, rfl⟩
  have := congrArg (fun g : C(X, ℂ) => g ⟨χ, hχ⟩) (LinearMap.congr_fun h0 e.c)
  simp only [hφ, e.proj_c, gelfand_one, LinearMap.zero_apply, ofRealL_apply,
    ContinuousMap.one_apply, ContinuousMap.zero_apply, Complex.ofReal_one] at this
  exact one_ne_zero this

end NoI1

/-! ## 12. The comparison step: orthogonal idempotents linked by `V½(p) ∩ V½(q) ≠ 0` have
non-zero exchangeable subidempotents -/

section OddCalc

open JBPeirce Polynomial

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- `σ_e` is contractive (a positive unital map). -/
theorem refl_norm_le {e : V} (he : e * e = e) (z : V) :
    ousNorm V (peirceRefl e z) ≤ ousNorm V z := by
  obtain ⟨b1, b2⟩ := ousNorm_bounds_le z
  have hu := peirceRefl_unit JBAlgebra.one_mul he
  have c1 := refl_mono he b1
  have c2 := refl_mono he b2
  rw [map_neg, map_smul, hu] at c1
  rw [map_smul, hu] at c2
  exact ousNorm_le_rc (ousNorm_nonneg_rc z) c1 c2

/-- `σ_e(P(x)) = P(-X)(x)` when `σ_e x = -x`. -/
theorem refl_jbEv {e x : V} (he : e * e = e) (hx : peirceRefl e x = -x) (P : ℝ[X]) :
    peirceRefl e (jbEv x P) = jbEv x (P.comp (-X)) := by
  have hmul := peirceRefl_mul he (e := e)
  have hu := peirceRefl_unit JBAlgebra.one_mul he
  have hpow : ∀ n : ℕ, peirceRefl e (jbEv x (X ^ n)) = jbEv x ((X ^ n : ℝ[X]).comp (-X)) := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_comp, jbEv_one, hu]
    | succ n ih =>
      rw [pow_succ', mul_comp, X_comp, jbEv_mul, jbEv_mul, jbEv_X, hmul, ih, hx, map_neg, jbEv_X]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, add_comp, map_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, C_mul', map_smul, map_smul, hpow, Polynomial.smul_comp, map_smul]

/-- **Odd functions of `x ∈ V½(e)` lie in `V½(e)`**: if `σ_e x = -x` and `G` is odd then
`σ_e(G(x)) = -G(x)` (odd polynomial approximation on `[-‖x‖, ‖x‖]`). -/
theorem refl_cfc_odd {e x : V} (he : e * e = e) (hx : peirceRefl e x = -x) {G : ℝ → ℝ}
    (hG : Continuous G) (hodd : ∀ t, G (-t) = -G t) (f : C(jbSpec x, ℝ))
    (hf : ∀ t, f t = G t.1) : peirceRefl e (jbCfc x f) = -jbCfc x f := by
  set y := jbCfc x f
  set M := ousNorm V x
  have key : ∀ ε : ℝ, 0 < ε → ousNorm V (peirceRefl e y + y) ≤ 2 * ε := by
    intro ε hε
    obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-M) M G hG.continuousOn ε hε
    set Q : ℝ[X] := (1 / 2 : ℝ) • (P - P.comp (-X))
    have hQev : ∀ t, Q.eval t = (1 / 2 : ℝ) * (P.eval t - P.eval (-t)) := fun t => by
      simp [Q, eval_comp]
    have hQσ : peirceRefl e (jbEv x Q) = -jbEv x Q := by
      simp only [Q, map_smul, map_sub, refl_jbEv he hx, comp_neg_X_comp_neg_X]
      rw [smul_sub, smul_sub, neg_sub]
    have happ : ousNorm V (y - jbEv x Q) ≤ ε := by
      rw [← jbCfc_specPoly, ← jbCfc_sub, ousNorm_jbCfc]
      refine (ContinuousMap.norm_le _ hε.le).2 fun t => ?_
      have ht := jbSpec_subset x t.2
      have ht' : -t.1 ∈ Set.Icc (-M) M := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h1 := hP t.1 ht
      have h2 := hP (-t.1) ht'
      simp only [ContinuousMap.sub_apply, specPoly, ContinuousMap.coe_mk, hf, Real.norm_eq_abs,
        hQev]
      rw [hodd] at h2
      rw [abs_le] at *
      constructor <;> nlinarith [abs_lt.1 h1, abs_lt.1 h2]
    have e1 : peirceRefl e y + y = peirceRefl e (y - jbEv x Q) + (y - jbEv x Q) := by
      rw [map_sub, hQσ]; abel
    rw [e1]
    refine (ousNorm_add_le _ _).trans ?_
    linarith [refl_norm_le he (y - jbEv x Q)]
  have h0 : ousNorm V (peirceRefl e y + y) = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (ousNorm_nonneg_rc _)
    have := key (ε / 2) (by positivity)
    linarith
  exact eq_neg_of_add_eq_zero_left (IsOUS.norm_eq_zero _ h0)

theorem refl_of_half {e x : V} (hx : e * x = (1 / 2 : ℝ) • x) : peirceRefl e x = -x := by
  rw [peirceRefl_apply, Ph_of_memh hx]; module

theorem half_of_refl {e y : V} (he : e * e = e) (hy : peirceRefl e y = -y) :
    e * y = (1 / 2 : ℝ) • y := by
  rw [peirceRefl_apply] at hy
  have h2 : Ph e y = y := by
    have : (2 : ℝ) • Ph e y = (2 : ℝ) • y := by linear_combination (norm := module) -hy
    exact smul_right_injective V (two_ne_zero) this
  have := Ph_mem he y
  rwa [h2] at this

end OddCalc

section Compare

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

omit hW in
/-- `min((n+1)t⁺, 1) - min((n+1)t⁻, 1)`, an odd function. -/
def oddF (n : ℕ) (t : ℝ) : ℝ := min (((n : ℝ) + 1) * max t 0) 1 - min (((n : ℝ) + 1) * max (-t) 0) 1

omit hW in
theorem continuous_oddF (n : ℕ) : Continuous (oddF n) := by
  unfold oddF; fun_prop

omit hW in
theorem oddF_neg (n : ℕ) (t : ℝ) : oddF n (-t) = -oddF n t := by
  simp only [oddF, neg_neg]; ring

/-- **The partial symmetry of `x`**: `v = r(x⁺) - r(x⁻)` with `v³ = v`; it lies in every
`V½(e)` containing `x`, and `v = 0` only if `x = 0`. -/
theorem partial_symm (x : V) :
    let v := sproj (posF x) - sproj (negF x)
    v * (v * v) = v ∧ (v * v) * (v * v) = v * v ∧ (x ≠ 0 → v ≠ 0) ∧
      ∀ e : V, e * e = e → e * x = (1 / 2 : ℝ) • x → e * v = (1 / 2 : ℝ) • v := by
  intro v
  have hgp : ∀ t, 0 ≤ posF x t := fun t => le_max_right _ _
  have hgn : ∀ t, 0 ≤ negF x t := fun t => le_max_right _ _
  have hrp := sproj_idem hgp
  have hrn := sproj_idem hgn
  have hpn0 : ∀ t : jbSpec x, posF x t * negF x t = 0 := fun t => by
    simp only [posF, negF, ContinuousMap.coe_mk]
    rcases le_total t.1 0 with h0 | h0
    · rw [max_eq_right h0, zero_mul]
    · rw [max_eq_right (by linarith : -t.1 ≤ 0), mul_zero]
  have horth : sproj (posF x) * sproj (negF x) = 0 := sproj_mul_sproj_eq_zero hgp hgn hpn0
  have horth' : sproj (negF x) * sproj (posF x) = 0 := by rw [JBAlgebra.mul_comm]; exact horth
  have hvv : v * v = sproj (posF x) + sproj (negF x) := by
    simp only [v, jsub_mul, jmul_sub, hrp, hrn, horth, horth']; abel
  refine ⟨?_, ?_, fun hx hv => ?_, fun e he hex => ?_⟩
  · rw [hvv]; simp only [v, jsub_mul, jmul_add, hrp, hrn, horth, horth']; abel
  · rw [hvv]; exact add_idem_of_orth hrp hrn horth
  · -- `v x = |x|`
    have h1 : sproj (posF x) * jbCfc x (posF x) = jbCfc x (posF x) := by
      have := sproj_mul_cfc hgp 1; rwa [mul_one] at this
    have h2 : sproj (posF x) * jbCfc x (negF x) = 0 :=
      sproj_mul_cfc_eq_zero hgp hpn0
    have h3 : sproj (negF x) * jbCfc x (negF x) = jbCfc x (negF x) := by
      have := sproj_mul_cfc hgn 1; rwa [mul_one] at this
    have h4 : sproj (negF x) * jbCfc x (posF x) = 0 :=
      sproj_mul_cfc_eq_zero hgn fun t => by rw [mul_comm]; exact hpn0 t
    have hdec : x = jbCfc x (posF x) - jbCfc x (negF x) := by
      rw [← jbCfc_sub]
      conv_lhs => rw [← jbCfc_id x]
      congr 1; ext t
      simp only [specId, posF, negF, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
      rcases le_total t.1 0 with h0 | h0
      · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
    have hvx : v * x = jbCfc x (posF x + negF x) := by
      rw [jbCfc_add]
      conv_lhs => rw [hdec]
      simp only [v, jsub_mul, jmul_sub, h1, h2, h3, h4]; abel
    rw [hv, jb_zero_mul, ← jbCfc_zero x] at hvx
    have hz := jbCfc_injective x hvx
    apply hx
    rw [← jbCfc_id x, ← jbCfc_zero x]
    congr 1; ext t
    have := congrArg (fun f : C(jbSpec x, ℝ) => f t) hz
    simp only [ContinuousMap.add_apply, ContinuousMap.zero_apply, posF, negF,
      ContinuousMap.coe_mk] at this
    simp only [specId, ContinuousMap.coe_mk, ContinuousMap.zero_apply]
    have a1 := le_max_left t.1 0
    have a2 := le_max_left (-t.1) 0
    have a3 := le_max_right t.1 0
    have a4 := le_max_right (-t.1) 0
    linarith
  · -- `e v = ½ v`: weak limit of the odd functions `oddF n (x) ∈ V½(e)`
    have hσx := refl_of_half hex
    refine eq_of_normal fun ω hω => ?_
    have hw : ∀ n, e * (sseq (posF x) n - sseq (negF x) n) =
        (1 / 2 : ℝ) • (sseq (posF x) n - sseq (negF x) n) := by
      intro n
      refine half_of_refl he ?_
      rw [sseq, sseq, ← jbCfc_sub]
      refine refl_cfc_odd he hσx (continuous_oddF n) (oddF_neg n) _ fun t => ?_
      simp only [ContinuousMap.sub_apply, sfun_apply, posF, negF, ContinuousMap.coe_mk, oddF]
    have T1 := tendsto_idem_mul he ω hω (sseq_mono hgp) (sseq_nonneg hgp) (sproj_isLUB hgp)
      (sproj_le_one hgp) (ouUnit V)
    have T2 := tendsto_idem_mul he ω hω (sseq_mono hgn) (sseq_nonneg hgn) (sproj_isLUB hgn)
      (sproj_le_one hgn) (ouUnit V)
    have T3 := tendsto_sseq hgp hω
    have T4 := tendsto_sseq hgn hω
    have T := (((T3.sub T4).const_mul (1 / 2 : ℝ)).add T1).sub T2
    simp only [add_zero, sub_zero] at T
    have e1 : ∀ n, (1 / 2 : ℝ) * (ω.toLin (sseq (posF x) n) - ω.toLin (sseq (negF x) n)) +
        ω.toLin (e * (ouUnit V * (sproj (posF x) - sseq (posF x) n))) -
        ω.toLin (e * (ouUnit V * (sproj (negF x) - sseq (negF x) n))) = ω.toLin (e * v) := by
      intro n
      have := congrArg ω.toLin (hw n)
      rw [map_smul, smul_eq_mul, map_sub] at this
      rw [← this, JBAlgebra.one_mul, JBAlgebra.one_mul, ← map_add, ← map_sub, ← jb_mul_add,
        ← jb_mul_sub]
      congr 2
      simp only [v]; abel
    simp only [e1] at T
    rw [map_smul, map_sub, smul_eq_mul]
    exact tendsto_nhds_unique tendsto_const_nhds T

/-- **The comparison step** (H-O–S 5.2-type, the "polar decomposition" of a Peirce-½
element): if `p ⊥ q` are idempotents and `0 ≠ x ∈ V½(p) ∩ V½(q)`, then there are non-zero
orthogonal idempotents `p' ≤ p`, `q' ≤ q` that are exchangeable by a symmetry (REC 131).
With `v` the partial symmetry of `x` and `w = v²`: `p' = U_p w`, `q' = U_{1-p} w`, and `v`
connects them (`exch_iff_connect`). -/
theorem exists_connected_sub {p q x : V} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0)
    (hxp : p * x = (1 / 2 : ℝ) • x) (hxq : q * x = (1 / 2 : ℝ) • x) (hx0 : x ≠ 0) :
    ∃ p' q' v : V, p' * p' = p' ∧ q' * q' = q' ∧ p' * q' = 0 ∧ p' ≤ p ∧ q' ≤ q ∧ p' ≠ 0 ∧
      q' ≠ 0 ∧ p' * v = (1 / 2 : ℝ) • v ∧ q' * v = (1 / 2 : ℝ) • v ∧ v * v = p' + q' := by
  obtain ⟨hvvv, hwidem, hv0, hhalf⟩ := partial_symm x
  set v := sproj (posF x) - sproj (negF x)
  have hvp : v ∈ peirce p (1 / 2) := hhalf p hp hxp
  have hvq : v ∈ peirce q (1 / 2) := hhalf q hq hxq
  set w := v * v with hwdef
  have hPh : Ph p w = 0 := peirce_half_mul_half hp hvp hvp
  set p' := P1 p w
  set q' := P0 p w
  have hdec : p' + q' = w := decomp_of_Ph w hPh
  have hmd := mul_decomp_of_Ph hp hPh hPh
  have hp'p' : p' * p' = p' := by
    have := congrArg (P1 p) hmd
    rw [hwidem, map_add, P1_of_mem1 (peirce_one_mul_one hp (P1_mem hp w) (P1_mem hp w)),
      P1_of_mem0 (peirce_zero_mul_zero hp (P0_mem hp w) (P0_mem hp w)), add_zero] at this
    exact this.symm
  have hq'q' : q' * q' = q' := by
    have := congrArg (P0 p) hmd
    rw [hwidem, map_add, P0_of_mem1 (peirce_one_mul_one hp (P1_mem hp w) (P1_mem hp w)),
      P0_of_mem0 (peirce_zero_mul_zero hp (P0_mem hp w) (P0_mem hp w)), zero_add] at this
    exact this.symm
  have horth : p' * q' = 0 := peirce_one_mul_zero hp (P1_mem hp w) (P0_mem hp w)
  have hpw : p * w = p' := mul_of_Ph hp hPh
  have hvw : v * w = v := hvvv
  have hp'v : p' * v = (1 / 2 : ℝ) • v := by
    have hj := JBAlgebra.jordan v p
    rw [JBAlgebra.mul_comm v p, hvp, JBAlgebra.smul_mul, ← hwdef, hvw, hpw] at hj
    rw [JBAlgebra.mul_comm, ← hj]
  have hq'v : q' * v = (1 / 2 : ℝ) • v := by
    have : q' = w - p' := by rw [← hdec]; abel
    rw [this, jsub_mul, JBAlgebra.mul_comm w v, hvw, hp'v]; module
  have hvne := hv0 hx0
  have hqq' : q * q' = q' := by
    have hw1 : w ∈ peirce (p + q) 1 :=
      peirce_one_mul_one (add_idem_of_orth hp hq hpq) (mem_peirce_one_add hvp hvq)
        (mem_peirce_one_add hvp hvq)
    rw [mem_peirce, one_smul, jadd_mul, hpw] at hw1
    have hqp' : q * p' = 0 := by
      rw [JBAlgebra.mul_comm]
      exact peirce_one_mul_zero hp (P1_mem hp w) (mem_peirce_zero_of_orth hpq)
    have : q' = w - p' := by rw [← hdec]; abel
    rw [this, jmul_sub, hqp', sub_zero]
    linear_combination (norm := module) hw1
  refine ⟨p', q', v, hp'p', hq'q', horth, le_of_mem_one hp (P1_mem hp w) (idem_le_one hp'p'),
    le_of_mem_one hq (by rw [mem_peirce, one_smul]; exact hqq') (idem_le_one hq'q'),
    fun h => hvne ?_, fun h => hvne ?_, hp'v, hq'v, hdec.symm⟩
  · rw [h, jb_zero_mul] at hp'v
    exact (smul_eq_zero.1 hp'v.symm).resolve_left (by norm_num)
  · rw [h, jb_zero_mul] at hq'v
    exact (smul_eq_zero.1 hq'v.symm).resolve_left (by norm_num)

/-- **The comparison step**, exchange form: non-zero orthogonal `p' ≤ p`, `q' ≤ q`
exchangeable by a symmetry (REC 131). -/
theorem exists_exch_sub {p q x : V} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0)
    (hxp : p * x = (1 / 2 : ℝ) • x) (hxq : q * x = (1 / 2 : ℝ) • x) (hx0 : x ≠ 0) :
    ∃ p' q' : V, p' * q' = 0 ∧ p' ≤ p ∧ q' ≤ q ∧ p' ≠ 0 ∧ q' ≠ 0 ∧
      ExchangeableBySymmetry p' q' := by
  obtain ⟨p', q', v, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_connected_sub hp hq hpq hxp hxq hx0
  exact ⟨p', q', h3, h4, h5, h6, h7, h1, h2,
    (exch_iff_connect JBAlgebra.one_mul h1 h2 h3).2 ⟨v, h8, h9, h10⟩⟩

end Compare

/-! ## 13. Non-associative JBW-algebras have a non-trivial exchangeable pair -/

section ExchPair

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **A JBW-algebra all of whose idempotents are central is associative** (type I₁):
every idempotent central gives `P½(e) a = 0` for all `a`, so every `a` is central
(`central_of_Ph`), and then `(ab)c = c(ab) = a(cb) = a(bc)`. -/
theorem assoc_of_idem_central (h : ∀ e : V, e * e = e → ∀ x y : V, e * (x * y) = x * (e * y)) :
    ∀ a b c : V, a * b * c = a * (b * c) := by
  have hc : ∀ a x y : V, a * (x * y) = x * (a * y) := fun a =>
    central_of_Ph fun e he => by
      have h1 := h e he a e
      rw [he, JBAlgebra.mul_comm a e] at h1
      rw [Ph_apply, h1, sub_self]
  intro a b c
  rw [JBAlgebra.mul_comm (a * b) c, hc c a b, JBAlgebra.mul_comm c b]

/-- **The first halving step**: a JBW-algebra that is not associative has non-zero
orthogonal idempotents `p' ⊥ q'` exchangeable by a symmetry.  A non-central idempotent `e`
has `0 ≠ z ∈ V½(e) = V½(e) ∩ V½(1 - e)` (`comm_of_Ph`), and `exists_exch_sub` applies to
`e ⊥ 1 - e`. -/
theorem exists_exch_pair (hna : ¬ ∀ a b c : V, a * b * c = a * (b * c)) :
    ∃ p q : V, p * q = 0 ∧ p ≠ 0 ∧ q ≠ 0 ∧ ExchangeableBySymmetry p q := by
  obtain ⟨e, he, hnc⟩ : ∃ e : V, e * e = e ∧ ¬ ∀ x y : V, e * (x * y) = x * (e * y) := by
    by_contra hno
    push Not at hno
    exact hna (assoc_of_idem_central fun e he => hno e he)
  obtain ⟨x, hx⟩ : ∃ x : V, Ph e x ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hnc fun x y => comm_of_Ph he (hno x) y
  set z := Ph e x
  have hze : e * z = (1 / 2 : ℝ) • z := Ph_mem he x
  have he' := idem_one_sub he
  have hz1 : (ouUnit V - e) * z = (1 / 2 : ℝ) • z := by
    rw [jsub_mul, JBAlgebra.one_mul, hze]; module
  have horth : e * (ouUnit V - e) = 0 := by
    rw [jmul_sub, JBAlgebra.mul_comm e (ouUnit V), JBAlgebra.one_mul, he, sub_self]
  obtain ⟨p', q', h1, -, -, h4, h5, h6⟩ := exists_exch_sub he he' horth hze hz1 hx
  exact ⟨p', q', h1, h4, h5, h6⟩

/-- **A non-zero purely exceptional JBW-algebra has non-zero orthogonal idempotents
exchangeable by a symmetry** — the pair-level shadow of `ExceptionalBoundedRank` (i)
(which asks for such a family summing to `1`). -/
theorem pe_exists_exch_pair (hpe : IsPurelyExceptional.{u, u} V) (h1 : ouUnit V ≠ 0) :
    ∃ p q : V, p * q = 0 ∧ p ≠ 0 ∧ q ≠ 0 ∧ ExchangeableBySymmetry p q := by
  refine exists_exch_pair fun hassoc => ?_
  let e : Papers.SEA.JBW.CentralIdem V :=
    { c := ouUnit V
      idem := JBAlgebra.one_mul _
      central := fun x y => by rw [JBAlgebra.one_mul, JBAlgebra.one_mul] }
  exact centralIdem_not_assoc hpe e h1 fun x y z => Subtype.ext (hassoc x.1 y.1 z.1)

end ExchPair

/-! ## 14. Peirce corners `eVe` are JBW-algebras; (i) holds in a corner of every non-zero
purely exceptional JBW-algebra -/

section Bdd

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- **Monotone completeness, general form**: a non-empty directed set bounded above has a
least upper bound (translate by an element, scale into `[0,1]`). -/
theorem exists_isLUB_bdd {D : Set V} (hne : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) {b : V}
    (hb : ∀ d ∈ D, d ≤ b) : ∃ s, IsLUB D s := by
  obtain ⟨d0, hd0⟩ := hne
  set l : ℝ := ousNorm V (b - d0) + 1
  have hl : 0 < l := by have := ousNorm_nonneg_rc (b - d0); linarith
  have hli : 0 ≤ l⁻¹ := inv_nonneg.2 hl.le
  have hbl : b - d0 ≤ l • ouUnit V :=
    (ousNorm_bounds_le _).2.trans (ou_smul_unit_mono (by linarith))
  have hsc : ∀ x : V, l • (l⁻¹ • x) = x := fun x => by
    rw [_root_.smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
  set E := (fun d => l⁻¹ • (d - d0)) '' {d ∈ D | d0 ≤ d}
  have hE : E ⊆ Set.Icc 0 (ouUnit V) := by
    rintro _ ⟨d, ⟨hd, hd0d⟩, rfl⟩
    refine ⟨ou_smul_nonneg hli (sub_nonneg.2 hd0d), ?_⟩
    have := ou_smul_le_smul hli ((sub_le_sub_right (hb d hd) d0).trans hbl)
    rwa [_root_.smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at this
  have hEdir : DirectedOn (· ≤ ·) E := by
    rintro _ ⟨a, ⟨ha, ha0⟩, rfl⟩ _ ⟨c, ⟨hc, -⟩, rfl⟩
    obtain ⟨z, hz, h1, h2⟩ := hdir a ha c hc
    exact ⟨_, ⟨z, ⟨hz, ha0.trans h1⟩, rfl⟩, ou_smul_le_smul hli (sub_le_sub_right h1 _),
      ou_smul_le_smul hli (sub_le_sub_right h2 _)⟩
  obtain ⟨t, ht, -⟩ := exists_isLUB_unit hE ⟨_, ⟨d0, ⟨hd0, le_rfl⟩, rfl⟩⟩ hEdir
  refine ⟨d0 + l • t, fun d hd => ?_, fun u hu => ?_⟩
  · obtain ⟨z, hz, h1, h2⟩ := hdir d hd d0 hd0
    have := ou_smul_le_smul hl.le (ht.1 ⟨z, ⟨hz, h2⟩, rfl⟩)
    rw [hsc] at this
    calc d ≤ z := h1
      _ = d0 + (z - d0) := by abel
      _ ≤ d0 + l • t := add_le_add le_rfl this
  · have h1 : t ≤ l⁻¹ • (u - d0) := ht.2 (by
      rintro _ ⟨d, ⟨hd, -⟩, rfl⟩; exact ou_smul_le_smul hli (sub_le_sub_right (hu hd) _))
    have := ou_smul_le_smul hl.le h1
    rw [hsc] at this
    calc d0 + l • t ≤ d0 + (u - d0) := add_le_add le_rfl this
      _ = u := by abel

end Bdd

section CornerBasic

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

theorem P1_mono {e : V} (he : e * e = e) {x y : V} (h : x ≤ y) : P1 e x ≤ P1 e y := by
  have := P1_nonneg he (sub_nonneg.2 h); rwa [map_sub, sub_nonneg] at this

theorem P1_of_mul {e x : V} (hx : e * x = x) : P1 e x = x :=
  P1_of_mem1 (by rw [mem_peirce, one_smul]; exact hx)

/-- `-‖x‖e ≤ x ≤ ‖x‖e` for `x ∈ V₁(e)`. -/
theorem corner_bounds {e x : V} (he : e * e = e) (hx : e * x = x) :
    -(ousNorm V x • e) ≤ x ∧ x ≤ ousNorm V x • e := by
  obtain ⟨b1, b2⟩ := ousNorm_bounds_le x
  have c1 := P1_mono he b1
  have c2 := P1_mono he b2
  rw [P1_of_mul hx, map_neg, map_smul, P1_one he] at c1
  rw [P1_of_mul hx, map_smul, P1_one he] at c2
  exact ⟨c1, c2⟩

theorem smul_le_smul_elem {a : V} (ha : 0 ≤ a) {r s : ℝ} (h : r ≤ s) : r • a ≤ s • a := by
  have := ou_smul_nonneg (sub_nonneg.2 h) ha
  rwa [sub_smul, sub_nonneg] at this

/-- A positive `y` with `U_{1-e} y = 0` lies in `V₁(e)`: with `w = √y`, `P₀(w²) =
w₀² + P₀(w½²)` is a sum of positives, so `w₀ = 0` and `w½ = 0` (`half_eq_zero`). -/
theorem nonneg_mem_one {e y : V} (he : e * e = e) (hy : 0 ≤ y) (h0 : P0 e y = 0) : e * y = y := by
  have hw : jbSqrt y * jbSqrt y = y := jbSqrt_mul_self hy
  have hwd := peirce_decomp e (jbSqrt y)
  have m1 := P1_mem he (jbSqrt y)
  have mh := Ph_mem he (jbSqrt y)
  have m0 := P0_mem he (jbSqrt y)
  set w1 := P1 e (jbSqrt y)
  set wh := Ph e (jbSqrt y)
  set w0 := P0 e (jbSqrt y)
  have f11 : P0 e (w1 * w1) = 0 := P0_of_mem1 (peirce_one_mul_one he m1 m1)
  have f1h : P0 e (w1 * wh) = 0 := P0_of_memh (peirce_one_mul_half he m1 mh)
  have fh1 : P0 e (wh * w1) = 0 := by rw [JBAlgebra.mul_comm]; exact f1h
  have f10 : w1 * w0 = 0 := peirce_one_mul_zero he m1 m0
  have f01 : w0 * w1 = 0 := by rw [JBAlgebra.mul_comm]; exact f10
  have f0h : P0 e (w0 * wh) = 0 := P0_of_memh (peirce_zero_mul_half he m0 mh)
  have fh0 : P0 e (wh * w0) = 0 := by rw [JBAlgebra.mul_comm]; exact f0h
  have f00 : P0 e (w0 * w0) = w0 * w0 := P0_of_mem0 (peirce_zero_mul_zero he m0 m0)
  have e1 : P0 e y = w0 * w0 + P0 e (wh * wh) := by
    rw [← hw, ← hwd]
    simp only [jadd_mul, jmul_add, map_add, f11, f1h, fh1, f10, f01, f0h, fh0, f00,
      zero_add, add_zero]
    abel
  rw [h0] at e1
  have a1 := jb_sq_nonneg w0
  have a2 := P0_nonneg he (jb_sq_nonneg wh)
  have hw0 : w0 * w0 = 0 := le_antisymm (by
    calc w0 * w0 ≤ w0 * w0 + P0 e (wh * wh) := le_add_of_nonneg_right a2
      _ = 0 := e1.symm) a1
  have hwh : P0 e (wh * wh) = 0 := le_antisymm (by
    calc P0 e (wh * wh) ≤ w0 * w0 + P0 e (wh * wh) := le_add_of_nonneg_left a1
      _ = 0 := e1.symm) a2
  have hw0' : w0 = 0 := by
    have := jb_norm_mul_self w0
    rw [hw0, ousNorm_zero'] at this
    exact IsOUS.norm_eq_zero _ (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.symm)
  have hwh' : wh = 0 := half_eq_zero he mh hwh
  rw [hw0', hwh', add_zero, add_zero] at hwd
  rw [← hw, ← hwd]
  have := peirce_one_mul_one he m1 m1
  rwa [mem_peirce, one_smul] at this

/-- `0 ≤ s ≤ r e` forces `s ∈ V₁(e)`. -/
theorem mem_of_le_smul {e s : V} (he : e * e = e) (hs0 : 0 ≤ s) {r : ℝ} (hsr : s ≤ r • e) :
    e * s = s := by
  refine nonneg_mem_one he hs0 (le_antisymm ?_ (P0_nonneg he hs0))
  have h2 := P0_nonneg he (sub_nonneg.2 hsr)
  rwa [map_sub, map_smul, P0_of_mem1 (show e ∈ peirce e 1 by rw [mem_peirce, one_smul]; exact he),
    smul_zero, zero_sub, neg_nonneg] at h2

/-- The Peirce corner `V₁(e) = {x ; e x = x}` as a submodule. -/
def csub (e : V) : Submodule ℝ V where
  carrier := {x | e * x = x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [jb_mul_add, ha, hb]
  zero_mem' := by simp only [Set.mem_ofPred_eq]; exact jb_mul_zero _
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [jb_mul_smul, hx]

theorem mem_csub {e x : V} : x ∈ csub e ↔ e * x = x := Iff.rfl

end CornerBasic

/-- **The Peirce corner** `eVe = V₁(e)` of an idempotent, as a type. -/
abbrev ECorner {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V]
    [Mul V] [JBAlgebra V] (e : V) := ↥(csub e)

section Corner

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V] (e : V) [hf : Fact (e * e = e)]

include hJ hf

theorem ec_mem (x : ECorner e) : e * x.1 = x.1 := x.2

theorem ec_peirce (x : ECorner e) : x.1 ∈ peirce e 1 := by
  rw [mem_peirce, one_smul]; exact x.2

instance : OrderUnitSpace (ECorner e) where
  add_le_add_left x y h z := by
    show x.1 + z.1 ≤ y.1 + z.1
    exact add_le_add h le_rfl
  smul_nonneg {r x} hr hx := by
    show (0 : V) ≤ r • x.1
    exact ou_smul_nonneg hr hx
  unit := ⟨e, hf.out⟩
  exists_le_smul_unit x := by
    refine ⟨⌈ousNorm V x.1⌉₊, ?_⟩
    show x.1 ≤ (⌈ousNorm V x.1⌉₊ : ℝ) • e
    exact (corner_bounds hf.out x.2).2.trans
      (smul_le_smul_elem (idem_nonneg hf.out) (Nat.le_ceil _))

instance : Mul (ECorner e) :=
  ⟨fun x y => ⟨x.1 * y.1, by
    have := peirce_one_mul_one hf.out (ec_peirce e x) (ec_peirce e y)
    rwa [mem_peirce, one_smul] at this⟩⟩

theorem ec_unit_val : (ouUnit (ECorner e)).1 = e := rfl

theorem ec_mul_val (x y : ECorner e) : (x * y).1 = x.1 * y.1 := rfl

theorem ec_le_one : e ≤ ouUnit V := idem_le_one hf.out

/-- The order-unit norm of `eVe` (unit `e`) is that of `V`. -/
theorem ec_ousNorm (x : ECorner e) : ousNorm (ECorner e) x = ousNorm V x.1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨b1, b2⟩ := corner_bounds hf.out x.2
    exact ousNorm_le_rc (ousNorm_nonneg_rc _) b1 b2
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have ht : 0 ≤ ousNorm (ECorner e) x + δ := by have := ousNorm_nonneg_rc x; linarith
    obtain ⟨b1, b2⟩ := ousNorm_bounds (v := x) (ε := ousNorm (ECorner e) x + δ) (by linarith)
    have b1' : -((ousNorm (ECorner e) x + δ) • e) ≤ x.1 := b1
    have b2' : x.1 ≤ (ousNorm (ECorner e) x + δ) • e := b2
    have hm := ou_smul_le_smul ht (ec_le_one e)
    exact ousNorm_le_rc ht ((neg_le_neg hm).trans b1') (b2'.trans hm)

instance : IsOUS (ECorner e) where
  norm_eq_zero v hv := Subtype.ext (IsOUS.norm_eq_zero v.1 (by rw [← ec_ousNorm]; exact hv))
  cone_closed v hv := by
    show (0 : V) ≤ v.1
    refine IsOUS.cone_closed v.1 fun ε hε => ?_
    obtain ⟨w, hw, hvw⟩ := hv ε hε
    rw [ec_ousNorm] at hvw
    exact ⟨w.1, hw, hvw⟩

theorem ec_norm_le : ousNorm V e ≤ 1 := by
  refine ousNorm_le_rc zero_le_one ?_ ?_
  · rw [one_smul]; exact (neg_nonpos.2 ou_unit_nonneg).trans (idem_nonneg hf.out)
  · rw [one_smul]; exact ec_le_one e

/-- **`eVe` is a JB-algebra** (REC 44) with unit `e`. -/
instance : JBAlgebra (ECorner e) where
  toIsOUS := inferInstance
  banach s hs := by
    obtain ⟨v, hv⟩ := hJ.banach (fun n => (s n).1) (fun ε hε => by
      obtain ⟨N, hN⟩ := hs ε hε
      exact ⟨N, fun m hm n hn => by have := hN m hm n hn; rwa [ec_ousNorm] at this⟩)
    have hcv : e * v = v := by
      have h0 : ousNorm V (e * v - v) = 0 := by
        refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (ousNorm_nonneg_rc _)
        obtain ⟨N, hN⟩ := hv (δ / 2) (by positivity)
        have hN' := hN N le_rfl
        have e1 : e * v - v = e * (v - (s N).1) + ((s N).1 - v) := by
          rw [jb_mul_sub, ec_mem]; abel
        rw [e1, zero_add]
        refine (ousNorm_add_le _ _).trans ?_
        have h2 : ousNorm V (e * (v - (s N).1)) ≤ ousNorm V ((s N).1 - v) := by
          refine (jb_norm_mul_le _ _).trans ?_
          rw [ousNorm_sub_comm v]
          calc ousNorm V e * ousNorm V ((s N).1 - v) ≤ 1 * ousNorm V ((s N).1 - v) :=
                mul_le_mul_of_nonneg_right (ec_norm_le e) (ousNorm_nonneg_rc _)
            _ = _ := one_mul _
        linarith
      exact sub_eq_zero.1 (IsOUS.norm_eq_zero _ h0)
    exact ⟨⟨v, hcv⟩, fun ε hε => by
      obtain ⟨N, hN⟩ := hv ε hε
      exact ⟨N, fun n hn => by rw [ec_ousNorm]; exact hN n hn⟩⟩
  mul_comm a b := Subtype.ext (JBAlgebra.mul_comm a.1 b.1)
  mul_one a := Subtype.ext (show a.1 * e = a.1 by rw [JBAlgebra.mul_comm]; exact ec_mem e a)
  one_mul a := Subtype.ext (ec_mem e a)
  jordan a b := Subtype.ext (JBAlgebra.jordan a.1 b.1)
  sq_mem a h1 h2 := by
    have h1' : -e ≤ a.1 := h1
    have h2' : a.1 ≤ e := h2
    obtain ⟨s1, s2⟩ := JBAlgebra.sq_mem a.1 ((neg_le_neg (ec_le_one e)).trans h1')
      (h2'.trans (ec_le_one e))
    refine ⟨s1, ?_⟩
    show a.1 * a.1 ≤ e
    have := P1_mono hf.out s2
    rwa [P1_of_mul (show e * (a.1 * a.1) = a.1 * a.1 from ec_mem e (a * a)), P1_one hf.out]
      at this
  add_mul a b c := Subtype.ext (JBAlgebra.add_mul a.1 b.1 c.1)
  smul_mul r a b := Subtype.ext (JBAlgebra.smul_mul r a.1 b.1)

end Corner

section CornerW

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V] (e : V) [hf : Fact (e * e = e)]

include hW hf

/-- Least upper bounds of directed sets in `eVe` are those of `V`. -/
theorem ec_isLUB_val {S : Set (ECorner e)} (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S)
    {s : ECorner e} (hs : IsLUB S s) : IsLUB (Subtype.val '' S) s.1 := by
  refine ⟨by rintro _ ⟨t, ht, rfl⟩; exact hs.1 ht, fun u hu => ?_⟩
  have hdir' : DirectedOn (· ≤ ·) (Subtype.val '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨z, hz, h1, h2⟩ := hdir a ha b hb
    exact ⟨z.1, ⟨z, hz, rfl⟩, h1, h2⟩
  obtain ⟨sV, hsV⟩ := exists_isLUB_bdd (hne.image _) hdir' (b := s.1) (by
    rintro _ ⟨t, ht, rfl⟩; exact hs.1 ht)
  obtain ⟨t0, ht0⟩ := hne
  have h1 : t0.1 ≤ sV := hsV.1 ⟨t0, ht0, rfl⟩
  have h2 : sV ≤ s.1 := hsV.2 (by rintro _ ⟨t, ht, rfl⟩; exact hs.1 ht)
  have hd : e * (s.1 - t0.1) = s.1 - t0.1 := by rw [jb_mul_sub, ec_mem, ec_mem]
  have hmem : e * (sV - t0.1) = sV - t0.1 :=
    mem_of_le_smul hf.out (sub_nonneg.2 h1)
      ((sub_le_sub_right h2 _).trans (corner_bounds hf.out hd).2)
  have hsVe : e * sV = sV := by
    have := hmem; rw [jb_mul_sub, ec_mem] at this
    have := congrArg (· + t0.1) this; simpa using this
  have : s ≤ ⟨sV, hsVe⟩ := hs.2 fun t ht => hsV.1 ⟨t, ht, rfl⟩
  exact (show s.1 ≤ sV from this).trans (hsV.2 hu)

/-- **The Peirce corner `eVe` of a JBW-algebra is a JBW-algebra** (REC 48): directed suprema
in `[0,e]` are those of `V`, and a normal state `ω` of `V` separating two points of `eVe`
has `ω(e) > 0`, so `ω(e)⁻¹ ω` is a normal state of `eVe`. -/
instance : JBWAlgebra (ECorner e) where
  directedComplete D hD hdir := by
    have hD' : Subtype.val '' D ⊆ Set.Icc 0 (ouUnit V) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨(hD ht).1, le_trans (show t.1 ≤ e from (hD ht).2) (ec_le_one e)⟩
    obtain ⟨s, ⟨hs0, -⟩, hub, hleast⟩ := hW.directedComplete _ hD' (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨z, hz, h1, h2⟩ := hdir a ha b hb
      exact ⟨z.1, ⟨z, hz, rfl⟩, h1, h2⟩)
    have hse : s ≤ e := hleast e ⟨idem_nonneg hf.out, ec_le_one e⟩ (by
      rintro _ ⟨t, ht, rfl⟩; exact (hD ht).2)
    have hmem : e * s = s := mem_of_le_smul hf.out hs0 (r := 1) (by rwa [one_smul])
    refine ⟨⟨s, hmem⟩, ⟨hs0, hse⟩, fun d hd => hub _ ⟨d, hd, rfl⟩,
      fun t ht htub => hleast t.1 ⟨ht.1, le_trans (show t.1 ≤ e from ht.2) (ec_le_one e)⟩ ?_⟩
    rintro _ ⟨d, hd, rfl⟩; exact htub d hd
  separating x y hxy := by
    obtain ⟨ω, hωn, hωxy⟩ := hW.separating x.1 y.1 (fun h => hxy (Subtype.ext h))
    set k := ω.toLin e with hk_def
    have hk0 : 0 ≤ k := ω.nonneg _ (idem_nonneg hf.out)
    have hk : 0 < k := by
      refine lt_of_le_of_ne hk0 fun hk => hωxy ?_
      obtain ⟨b1, b2⟩ := corner_bounds hf.out (x - y).2
      have c1 := state_mono ω b1
      have c2 := state_mono ω b2
      rw [map_neg, map_smul, ← hk_def, ← hk, smul_zero, neg_zero] at c1
      rw [map_smul, ← hk_def, ← hk, smul_zero] at c2
      have := le_antisymm c2 c1
      rw [show (x - y).1 = x.1 - y.1 from rfl, map_sub, sub_eq_zero] at this
      exact this
    let ω' : OUSState (ECorner e) :=
      { toLin := k⁻¹ • (ω.toLin ∘ₗ (csub e).subtype)
        nonneg := fun a ha => by
          show 0 ≤ k⁻¹ * ω.toLin a.1
          exact mul_nonneg (inv_nonneg.2 hk0) (ω.nonneg _ ha)
        unital := by
          show k⁻¹ * ω.toLin e = 1
          exact inv_mul_cancel₀ hk.ne' }
    have hω' : ∀ a : ECorner e, ω'.toLin a = k⁻¹ * ω.toLin a.1 := fun a => rfl
    refine ⟨ω', ?_, ?_⟩
    · intro S s hne hdir hs
      have hV := hωn _ _ (hne.image _) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨z, hz, h1, h2⟩ := hdir a ha b hb
        exact ⟨z.1, ⟨z, hz, rfl⟩, h1, h2⟩) (ec_isLUB_val e hne hdir hs)
      refine ⟨?_, fun b hb => ?_⟩
      · rintro _ ⟨t, ht, rfl⟩
        rw [hω', hω']
        exact mul_le_mul_of_nonneg_left (hV.1 ⟨t.1, ⟨t, ht, rfl⟩, rfl⟩) (inv_nonneg.2 hk0)
      · rw [hω', inv_mul_le_iff₀ hk]
        refine hV.2 ?_
        rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        have := hb ⟨t, ht, rfl⟩
        rw [hω', inv_mul_le_iff₀ hk] at this
        exact this
    · rw [hω', hω']
      intro h
      exact hωxy (mul_left_cancel₀ (inv_ne_zero hk.ne') h)

end CornerW

section CornerExch

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hJ : JBAlgebra V]

include hJ

/-- A connected pair `p ⊥ q` (`v ∈ V½(p) ∩ V½(q)`, `v² = p + q`) is an exchangeable family
(`HasExchFamily`, part (i) of `ExceptionalBoundedRank`) of the corner `(p+q)V(p+q)`. -/
theorem corner_hasExchFamily {p q v : V} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0)
    (hvp : p * v = (1 / 2 : ℝ) • v) (hvq : q * v = (1 / 2 : ℝ) • v) (hvv : v * v = p + q)
    [Fact ((p + q) * (p + q) = p + q)] : HasExchFamily (ECorner (p + q)) := by
  have hqp : q * p = 0 := by rw [JBAlgebra.mul_comm]; exact hpq
  let P : ECorner (p + q) := ⟨p, show (p + q) * p = p by rw [jadd_mul, hp, hqp, add_zero]⟩
  let Q : ECorner (p + q) := ⟨q, show (p + q) * q = q by rw [jadd_mul, hq, hpq, zero_add]⟩
  let W : ECorner (p + q) := ⟨v, show (p + q) * v = v by
    have := mem_peirce_one_add hvp hvq; rwa [mem_peirce, one_smul] at this⟩
  refine hasExchFamily_of_connected_frame 2 le_rfl ![P, Q] ?_ ?_ ?_ 0 (fun _ => W) ?_ ?_ ?_
  · exact Fin.forall_fin_two.2 ⟨Subtype.ext hp, Subtype.ext hq⟩
  · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h,
      fun _ => Subtype.ext hpq⟩, Fin.forall_fin_two.2 ⟨fun _ => Subtype.ext hqp,
      fun h => absurd rfl h⟩⟩
  · rw [Fin.sum_univ_two]; exact Subtype.ext rfl
  · exact Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => Subtype.ext hvp⟩
  · exact Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => Subtype.ext hvq⟩
  · exact Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => Subtype.ext hvv⟩

end CornerExch

section PECorner

open JBPeirce

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V]
  [hW : JBWAlgebra V]

include hW

/-- Connected-pair form of `exists_exch_pair`. -/
theorem exists_connected_pair (hna : ¬ ∀ a b c : V, a * b * c = a * (b * c)) :
    ∃ p q v : V, p * p = p ∧ q * q = q ∧ p * q = 0 ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p * v = (1 / 2 : ℝ) • v ∧ q * v = (1 / 2 : ℝ) • v ∧ v * v = p + q := by
  obtain ⟨e, he, hnc⟩ : ∃ e : V, e * e = e ∧ ¬ ∀ x y : V, e * (x * y) = x * (e * y) := by
    by_contra hno
    push Not at hno
    exact hna (assoc_of_idem_central fun e he => hno e he)
  obtain ⟨x, hx⟩ : ∃ x : V, Ph e x ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hnc fun x y => comm_of_Ph he (hno x) y
  have hze : e * Ph e x = (1 / 2 : ℝ) • Ph e x := Ph_mem he x
  have hz1 : (ouUnit V - e) * Ph e x = (1 / 2 : ℝ) • Ph e x := by
    rw [jsub_mul, JBAlgebra.one_mul, hze]; module
  have horth : e * (ouUnit V - e) = 0 := by
    rw [jmul_sub, JBAlgebra.mul_comm e (ouUnit V), JBAlgebra.one_mul, he, sub_self]
  obtain ⟨p', q', v, h1, h2, h3, -, -, h6, h7, h8, h9, h10⟩ :=
    exists_connected_sub he (idem_one_sub he) horth hze hz1 hx
  exact ⟨p', q', v, h1, h2, h3, h6, h7, h8, h9, h10⟩

/-- **Part (i) of `ExceptionalBoundedRank` holds in a non-zero corner**: every non-zero
purely exceptional JBW-algebra `V` has a non-zero idempotent `f` whose Peirce corner `fVf`
is a JBW-algebra with an exchangeable family (`HasExchFamily`, `n = 2`). -/
theorem pe_corner_hasExchFamily (hpe : IsPurelyExceptional.{u, u} V) (h1 : ouUnit V ≠ 0) :
    ∃ f : V, ∃ hf : f * f = f, f ≠ 0 ∧
      (letI : Fact (f * f = f) := ⟨hf⟩; JBWAlgebra (ECorner f) ∧ HasExchFamily (ECorner f)) := by
  have hna : ¬ ∀ a b c : V, a * b * c = a * (b * c) := fun hassoc => by
    let e : Papers.SEA.JBW.CentralIdem V :=
      { c := ouUnit V
        idem := JBAlgebra.one_mul _
        central := fun x y => by rw [JBAlgebra.one_mul, JBAlgebra.one_mul] }
    exact centralIdem_not_assoc hpe e h1 fun x y z => Subtype.ext (hassoc x.1 y.1 z.1)
  obtain ⟨p, q, v, hp, hq, hpq, hp0, -, hvp, hvq, hvv⟩ := exists_connected_pair hna
  have hf := add_idem_of_orth hp hq hpq
  refine ⟨p + q, hf, fun h => hp0 ?_, ?_⟩
  · -- `p = (p + q) p = 0`
    have hqp : q * p = 0 := by rw [JBAlgebra.mul_comm]; exact hpq
    have : (p + q) * p = p := by rw [jadd_mul, hp, hqp, add_zero]
    rw [h, jb_zero_mul] at this; exact this.symm
  · have : Fact ((p + q) * (p + q) = p + q) := ⟨hf⟩
    exact ⟨inferInstance, corner_hasExchFamily hp hq hpq hvp hvq hvv⟩

end PECorner

end

end Papers.REC.JBWProj

#print axioms Papers.REC.JBWProj.sproj_idem
#print axioms Papers.REC.JBWProj.Ph_sproj_cfc
#print axioms Papers.REC.JBWProj.nonneg_of_normal
#print axioms Papers.REC.JBWProj.spectral_approx_norm
#print axioms Papers.REC.JBWProj.exists_nontrivial_idem
#print axioms Papers.REC.JBWProj.idem_le_iff
#print axioms Papers.REC.JBWProj.sup2_spec
#print axioms Papers.REC.JBWProj.central_of_Ph
#print axioms Papers.REC.JBWProj.exists_sSup_idem
#print axioms Papers.REC.JBWProj.exists_central_cover
#print axioms Papers.REC.JBWProj.centralIdem_not_assoc
#print axioms Papers.REC.JBWProj.exists_exch_sub
#print axioms Papers.REC.JBWProj.pe_exists_exch_pair
#print axioms Papers.REC.JBWProj.pe_corner_hasExchFamily
