import Papers.REC.JBPeirce

/-!
# REC 136 by a REC-native route: no exchangeable families, only a map into `M₃(𝕆)_sa`

Plan (research note `docs/research/rec136-native.md`, with its review's fixes G1, G2).
* `ExceptionalAlbertMap`: part (ii) of `ExceptionalAlbertPoint` alone (a multiplicative
  `χ : V → M₃(𝕆)_sa` with `χ 1 ≠ 0` for every non-zero purely exceptional JBW `V`);
  `exceptionalAlbertMap_of_point` (so it is implied by Shultz 1979 Thm 3.9).
* §A, the finite-dimensional lemma, in `Alb = M₃(𝕆)_sa` only (`alb_threeway_nogo`): three
  unital subalgebras `S₁, S₂, S₃` of a corner `Alb₁(e)` (`IsCornerSub`), with
  `x(yz) = y(xz)` for `x, z ∈ S_i`, `y ∈ S_j`, `i < j` (`OpComm`), cannot all avoid the
  span of `≤ 3` orthogonal idempotents (`AlbSmallSpan`).  Tools:
  - E2 (`T_idem_cases`): an idempotent has trace `0, 1, 2` or `3` (the cubic `cubic`);
  - E4 (`rank_one_peirce`): `T p = 1`, `p y = y` ⟹ `y = T y · p` (the linearised
    Hamilton–Cayley identity `Phi_eq_zero` at `x = p`, where `p^# = 0`);
  - E3 (`span_of_no_idem`): a unital subalgebra of `Alb₁(f)` with only the idempotents
    `0, f` is `ℝ f` (the spectral theorem `spectral_family`, run on `U ⊕ ℝ(1 − f)` since
    `Calg a ∋ 1`: fix G2);
  - Peirce rules `V₁V₁ ⊆ V₁`, `V₁V₀ = 0` (`JBPeirce`, via `IsJordanMul Alb`).
  Proof: `S₁ = ℝe`, or `S₁ ∋ p₁ ∉ {0, e}`, `p₂ = e − p₁`, traces `(1,1)`, `(1,2)`, `(2,1)`.
  With `T p = 1`, `r` the other: every `y ∈ S₂ ∪ S₃` is `c p + r y`, `r y ∈ V₁(r)` (`dec`).
  `T r = 1`: `S₂ ⊆ ℝp + ℝr`.  `T r = 2`: `y ↦ r y` is multiplicative on `S₂`; if its image
  is `ℝ r`, `S₂ ⊆ ℝp + ℝr`; else it has an idempotent `q₁ ∉ {0, r}`, `T q₁ = T q₂ = 1`
  (`q₂ = r − q₁`), and some idempotent `q̃ = δ p + q₁ ∈ S₂` (fix G1: `q = γ p + q₁` is one
  when `γ² = γ`, else `p = (q − q²)/(γ − γ²) ∈ S₂` and `q̃ = q₁`); `q̃` op-commuting with
  `S₃` forces `S₃ ⊆ ℝp + ℝq₁ + ℝq₂`.
* §B, glue (`false_of_smallSpan`): a multiplicative `g : V → Alb` with `g u ≠ 0` (`u² = u`)
  and range in such a span gives, by the coordinates `⟨x, q_k⟩/⟨q_k, q_k⟩`, a non-zero
  Jordan hom `V → C(ULift (Fin n), ℂ)` — absurd for purely exceptional `V`.
* §C, REC: `V_A` not JW gives (REC 52 as `JBWExceptionalSummand`, `corner_of_summand`) `W`
  with `V_W ≠ 0` purely exceptional.  `X = (W ⊗ W) ⊗ W`, `ι₁ a = (a⊗1)⊗1`, `ι₂ b = (1⊗b)⊗1`,
  `ι₃ c = 1⊗c` (REC 127); REC 126 gives the three commutations (the `(1,2)` one pushed
  through `u ↦ u ⊗ 1`).  `V_X` JW is absurd via `ι₁`; else the exceptional corner of `V_X`
  and `χ` give `ψ : V_X → Alb`, `S_i = ψ(ι_i V_W)`, and §A + §B conclude.
  `rec135_native`, `rec136_native`, `rec136_native_hypfree`.
-/

set_option linter.unusedSectionVars false

open CategoryTheory
open Theses.B.Eff
open scoped InnerProductSpace unitInterval

namespace Papers.REC

universe u v

/-! ## The weaker hypothesis -/

section HypProp

/-- Part (ii) of `ExceptionalAlbertPoint` alone: every non-zero purely exceptional
JBW-algebra has a multiplicative linear map into the Albert algebra `M₃(𝕆)_sa` not
vanishing at `1` (evaluation at a point of Shultz's `C(X, M₃(𝕆)_sa)`, Shultz 1979 Thm 3.9;
also a corollary of the Alfsen–Shultz–Størmer Gelfand–Naimark theorem). -/
def ExceptionalAlbertMap : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℝ V] [PartialOrder V] [OrderUnitSpace V] [Mul V],
    JBWAlgebra V → IsPurelyExceptional.{v, v} V → ouUnit V ≠ 0 →
      ∃ χ : V →ₗ[ℝ] Papers.EJA.Albert.Alb, (∀ a b : V, χ (a * b) = χ a * χ b) ∧
        χ (ouUnit V) ≠ 0

theorem exceptionalAlbertMap_of_point (hS : ExceptionalAlbertPoint.{v}) :
    ExceptionalAlbertMap.{v} :=
  fun V _ _ _ _ _ hV hpe hne => (hS V hV hpe hne).2

theorem exceptionalAlbertMap_of_shultz (hSh : ShultzExceptionalStructure.{v}) :
    ExceptionalAlbertMap.{v} :=
  exceptionalAlbertMap_of_point (exceptionalAlbertPoint_of_shultz hSh)

end HypProp

/-! ## §A. The three-way no-go in the Albert algebra -/

namespace AlbNoGo

open Papers.EJA Papers.EJA.Albert Papers.REC.JBPeirce

instance albIsJordanMul : IsJordanMul Alb :=
  ⟨mul_comm', fun a b c => pj_add_mul a b c, fun r a b => pj_smul_mul r a b, jordan⟩

/-! ### Traces of idempotents -/

theorem T_add (x y : Alb) : T (x + y) = T x + T y := inner_add_left _ _ _

theorem T_sub (x y : Alb) : T (x - y) = T x - T y := inner_sub_left _ _ _

theorem T_smul (r : ℝ) (x : Alb) : T (r • x) = r * T x := real_inner_smul_left _ _ _

theorem T_one : T (1 : Alb) = 3 := by
  unfold T; rw [hermMat_inner]
  simp [ejare]
  rw [show (3 : Oct) = ((3 : ℕ) : Oct) from rfl, Oct.natCast_fst, Quaternion.re_natCast]
  norm_num

theorem T_idem {p : Alb} (hp : p * p = p) : T p = ⟪p, p⟫_ℝ := idem_inner_one hp

theorem eq_zero_of_T {p : Alb} (hp : p * p = p) (h : T p = 0) : p = 0 := by
  rw [T_idem hp] at h
  exact inner_self_eq_zero.mp h

/-- E2: an idempotent of `M₃(𝕆)_sa` has trace `0`, `1`, `2` or `3` (from the cubic). -/
theorem T_idem_cases {p : Alb} (hp : p * p = p) :
    T p = 0 ∨ T p = 1 ∨ T p = 2 ∨ T p = 3 := by
  have hc := cubic p
  rw [hp, hp] at hc
  have hS : S p = (T p * T p - T p) / 2 := by rw [S, ← T_idem hp]
  rw [hS] at hc
  have key : ((T p - 1) * (T p - 2) / 2) • p = N p • (1 : Alb) := by
    linear_combination (norm := module) hc
  by_cases hc0 : (T p - 1) * (T p - 2) / 2 = 0
  · have : (T p - 1) * (T p - 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · right; left; linarith
    · right; right; left; linarith
  · obtain ⟨l, hpl⟩ : ∃ l : ℝ, p = l • (1 : Alb) := by
      refine ⟨((T p - 1) * (T p - 2) / 2)⁻¹ * N p, ?_⟩
      rw [← _root_.smul_smul, ← key, _root_.smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hl : l * l = l := by
      have h2 := hp
      rw [hpl, pj_smul_mul, pj_mul_smul, mul_one', _root_.smul_smul] at h2
      have h3 : (l * l - l) • (1 : Alb) = 0 := by rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right alb_one_ne_zero)
    have htl : T p = l * 3 := by rw [hpl, T_smul, T_one]
    have : l * (l - 1) = 0 := by linear_combination hl
    rcases mul_eq_zero.mp this with h | h
    · left; rw [htl, h]; ring
    · right; right; right; rw [htl, show l = 1 by linarith]; ring

/-- E4: the Peirce `1`-space of a trace-one idempotent is `ℝ p` (the linearised
Hamilton–Cayley identity at `x = p`, where `p^# = 0`). -/
theorem rank_one_peirce {p y : Alb} (hp : p * p = p) (ht : T p = 1) (hy : p * y = y) :
    y = T y • p := by
  have h := Phi_eq_zero p y
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [← T_idem hp, ht]
  have hS : S p = 0 := by rw [S, ht, hpp]; norm_num
  have hsharp : sharp p = 0 := by
    rw [sharp, hp, ht, hS, one_smul, zero_smul, sub_self, add_zero]
  have hpy : ⟪p, y⟫_ℝ = T y := by
    rw [T]
    conv_rhs => rw [← hy]
    rw [inner_mul', mul_one', real_inner_comm]
  have hS2 : S2 p y = 0 := by rw [S2, ht, hpy]; ring
  rw [Phi, hsharp, inner_zero_left, hS2, hS, ht, hp, mul_comm' y p, hy, hy] at h
  linear_combination (norm := module) h

/-! ### E3: subalgebras without non-trivial idempotents -/

/-- E3 (with fix G2): a unital subalgebra `U` of the corner `Alb₁(f)` whose only
idempotents are `0` and `f` is `ℝ f`.  The spectral theorem is applied inside the unital
subalgebra `U ⊕ ℝ(1 − f)` (which contains `Calg x`), and the idempotents cut down by `f`. -/
theorem span_of_no_idem {U : Submodule ℝ Alb} {f : Alb} (hfU : f ∈ U)
    (hmul : ∀ x ∈ U, ∀ y ∈ U, x * y ∈ U) (hunit : ∀ x ∈ U, f * x = x)
    (htriv : ∀ q ∈ U, q * q = q → q = 0 ∨ q = f) : U ≤ Submodule.span ℝ {f} := by
  intro x hx
  have hf : f * f = f := hunit f hfU
  have hsf : ∀ s ∈ U, s * (1 - f) = 0 := fun s hs => by
    rw [mul_sub', mul_one', mul_comm' s f, hunit s hs, sub_self]
  have hsf' : ∀ s ∈ U, (1 - f) * s = 0 := fun s hs => by rw [Albert.mul_comm']; exact hsf s hs
  have hff : (1 - f) * (1 - f) = 1 - f := by
    simp only [pj_sub_mul, pj_mul_sub, pj_one_mul, pj_mul_one, hf]; abel
  have hf1f : f * (1 - f) = 0 := by rw [Albert.mul_comm']; exact hsf' f hfU
  set U' := U ⊔ Submodule.span ℝ {(1 : Alb) - f} with hU'
  have hdec : ∀ a ∈ U', ∃ s ∈ U, ∃ l : ℝ, a = s + l • (1 - f) := by
    intro a ha
    obtain ⟨s, hs, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨s, hs, l, rfl⟩
  have hmem : ∀ s ∈ U, ∀ l : ℝ, s + l • (1 - f) ∈ U' := fun s hs l =>
    Submodule.add_mem _ (Submodule.mem_sup_left hs)
      (Submodule.mem_sup_right (Submodule.smul_mem _ l (Submodule.mem_span_singleton_self _)))
  have hprod : ∀ s ∈ U, ∀ s' ∈ U, ∀ l l' : ℝ,
      (s + l • (1 - f)) * (s' + l' • (1 - f)) = s * s' + (l * l') • (1 - f) := by
    intro s hs s' hs' l l'
    simp only [pj_add_mul, pj_mul_add, pj_smul_mul, pj_mul_smul, hsf s hs, hsf' s' hs', hff,
      smul_zero, add_zero, zero_add]
    module
  have hU'mul : ∀ a ∈ U', ∀ b ∈ U', a * b ∈ U' := by
    intro a ha b hb
    obtain ⟨s, hs, l, rfl⟩ := hdec a ha
    obtain ⟨s', hs', l', rfl⟩ := hdec b hb
    rw [hprod s hs s' hs' l l']
    exact hmem _ (hmul s hs s' hs') _
  have hxU' : x ∈ U' := Submodule.mem_sup_left hx
  have hpow : ∀ n, jpow x n ∈ U' := by
    intro n
    induction n with
    | zero =>
      rw [jpow_zero, show (1 : Alb) = f + (1 : ℝ) • (1 - f) by rw [one_smul]; abel]
      exact hmem f hfU 1
    | succ n ih => rw [jpow_succ]; exact hU'mul _ hxU' _ ih
  have hpoly : polySpan x ≤ U' :=
    Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hpow n)
  have hC : Calg x ≤ U' :=
    Submodule.topologicalClosure_minimal _ hpoly (Submodule.closed_of_finiteDimensional U')
  obtain ⟨Tf, hT, -, hTC, c, hc⟩ := spectral_family x
  have hfp : ∀ p ∈ Tf, f * p ∈ Submodule.span ℝ {f} := by
    intro p hp
    obtain ⟨s, hs, l, hsl⟩ := hdec p (hC (hTC p hp))
    have hfp' : f * p = s := by
      rw [hsl, pj_mul_add, pj_mul_smul, hunit s hs, hf1f, smul_zero, add_zero]
    have hss : s * s = s := by
      have h1 := hT.idem p hp
      rw [hsl, hprod s hs s hs l l] at h1
      have h2 := congrArg (HMul.hMul f) h1
      rw [pj_mul_add, pj_mul_smul, hunit _ (hmul s hs s hs), hf1f, smul_zero, add_zero,
        ← hsl, hfp'] at h2
      exact h2
    rw [hfp']
    rcases htriv s hs hss with h | h
    · rw [h]; exact zero_mem _
    · rw [h]; exact Submodule.mem_span_singleton_self f
  have : f * x ∈ Submodule.span ℝ {f} := by
    rw [hc, pj_mul_sum]
    exact Submodule.sum_mem _ fun p hp => by
      rw [pj_mul_smul]; exact Submodule.smul_mem _ _ (hfp p hp)
  rwa [hunit x hx] at this

/-! ### The lemma -/

/-- `S` lies in the span of at most three pairwise orthogonal idempotents of `M₃(𝕆)_sa`. -/
def AlbSmallSpan (S : Submodule ℝ Alb) : Prop :=
  ∃ n : ℕ, n ≤ 3 ∧ ∃ q : Fin n → Alb, (∀ i, q i * q i = q i) ∧
    (∀ i j, i ≠ j → q i * q j = 0) ∧ S ≤ Submodule.span ℝ (Set.range q)

/-- `S` is a unital subalgebra of the corner `Alb₁(e) = {x ; e x = x}`, with unit `e`. -/
structure IsCornerSub (e : Alb) (S : Submodule ℝ Alb) : Prop where
  unit_mem : e ∈ S
  mul_mem : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S
  unit_mul : ∀ x ∈ S, e * x = x

/-- The multiplication operators of `S` commute with those of `S'` on `S`:
`T_x T_y z = T_y T_x z` for `x, z ∈ S`, `y ∈ S'`. -/
def OpComm (S S' : Submodule ℝ Alb) : Prop :=
  ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S', x * (y * z) = y * (x * z)

theorem OpComm.idem {S S' : Submodule ℝ Alb} (h : OpComm S S') {p : Alb} (hpS : p ∈ S)
    (hp : p * p = p) {y : Alb} (hy : y ∈ S') : p * (p * y) = p * y := by
  have := h p hpS p hpS y hy
  rwa [hp, mul_comm' y p] at this

theorem smallSpan1 {S : Submodule ℝ Alb} {e : Alb} (he : e * e = e)
    (h : S ≤ Submodule.span ℝ {e}) : AlbSmallSpan S :=
  ⟨1, by norm_num, ![e], fun i => by fin_cases i; simpa using he,
    fun i j hij => absurd (Subsingleton.elim i j) hij,
    h.trans (Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨0, rfl⟩))⟩

theorem smallSpan2 {S : Submodule ℝ Alb} {a b : Alb} (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (h : ∀ y ∈ S, ∃ x z : ℝ, y = x • a + z • b) : AlbSmallSpan S := by
  have hba : b * a = 0 := by rw [Albert.mul_comm']; exact hab
  refine ⟨2, by norm_num, ![a, b], fun i => ?_, fun i j hij => ?_, fun y hy => ?_⟩
  · fin_cases i <;> simpa
  · fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨x, z, rfl⟩ := h y hy
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

theorem smallSpan3 {S : Submodule ℝ Alb} {a b c : Alb} (ha : a * a = a) (hb : b * b = b)
    (hc : c * c = c) (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0)
    (h : ∀ y ∈ S, ∃ x z w : ℝ, y = x • a + z • b + w • c) : AlbSmallSpan S := by
  have hba : b * a = 0 := by rw [Albert.mul_comm']; exact hab
  have hca : c * a = 0 := by rw [Albert.mul_comm']; exact hac
  have hcb : c * b = 0 := by rw [Albert.mul_comm']; exact hbc
  refine ⟨3, le_rfl, ![a, b, c], fun i => ?_, fun i j hij => ?_, fun y hy => ?_⟩
  · fin_cases i <;> simpa
  · fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨x, z, w, rfl⟩ := h y hy
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

theorem idem_sub {e p : Alb} (he : e * e = e) (hp : p * p = p) (hep : e * p = p) :
    (e - p) * (e - p) = e - p := by
  have hpe : p * e = p := by rw [Albert.mul_comm']; exact hep
  simp only [pj_sub_mul, pj_mul_sub, he, hp, hep, hpe]; abel

theorem T_pos_cases {p : Alb} (hp : p * p = p) (h0 : p ≠ 0) :
    T p = 1 ∨ T p = 2 ∨ T p = 3 := by
  rcases T_idem_cases hp with h | h | h | h
  · exact (h0 (eq_zero_of_T hp h)).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

section Core

variable {e : Alb} {S₁ S₂ S₃ : Submodule ℝ Alb}

/-- The case analysis once `S₁` contains orthogonal idempotents `p + r = e` with
`T p = 1`, `T r ∈ {1, 2}`. -/
theorem core (h₂ : IsCornerSub e S₂) (h₃ : IsCornerSub e S₃)
    (h12 : OpComm S₁ S₂) (h13 : OpComm S₁ S₃) (h23 : OpComm S₂ S₃) {p r : Alb}
    (hpS : p ∈ S₁) (hp : p * p = p) (hr : r * r = r) (hpr : p * r = 0) (hsum : p + r = e)
    (htp : T p = 1) (htr : T r = 1 ∨ T r = 2) : AlbSmallSpan S₂ ∨ AlbSmallSpan S₃ := by
  have hrp : r * p = 0 := by rw [Albert.mul_comm']; exact hpr
  -- every `y` of `S₂` or `S₃` is `c p + y'` with `y' = r y ∈ V₁(r)`
  have dec : ∀ {S' : Submodule ℝ Alb}, IsCornerSub e S' → OpComm S₁ S' → ∀ y ∈ S',
      ∃ y' : Alb, r * y' = y' ∧ r * y = y' ∧ y = T (p * y) • p + y' := by
    intro S' hS' h1' y hy
    have hpy := rank_one_peirce hp htp (h1'.idem hpS hp hy)
    have hey : p * y + r * y = y := by rw [← pj_add_mul, hsum, hS'.unit_mul y hy]
    set c := T (p * y)
    have hry : r * y = y - c • p := by rw [← hpy]; exact eq_sub_of_add_eq' hey
    refine ⟨r * y, ?_, rfl, ?_⟩
    · conv_lhs => rw [hry]
      rw [pj_mul_sub, pj_mul_smul, hrp, smul_zero, sub_zero]
    · rw [hry]; abel
  rcases htr with htr | htr
  · -- `T r = 1`: `S₂ ⊆ ℝ p + ℝ r`
    left
    refine smallSpan2 hp hr hpr fun y hy => ?_
    obtain ⟨y', hy'C, -, hyeq⟩ := dec h₂ h12 y hy
    exact ⟨T (p * y), T y', by rw [← rank_one_peirce hr htr hy'C]; exact hyeq⟩
  -- `T r = 2`: the Peirce rules for `r`
  have hp0 : p ∈ peirce r 0 := mem_peirce_zero_of_orth hrp
  have hCp : ∀ z, r * z = z → z * p = 0 := fun z hz =>
    peirce_one_mul_zero hr (mem_peirce_one_of_mul hz) hp0
  have hpC : ∀ z, r * z = z → p * z = 0 := fun z hz => by rw [Albert.mul_comm']; exact hCp z hz
  have hCmul : ∀ z w, r * z = z → r * w = w → r * (z * w) = z * w := by
    intro z w hz hw
    have := peirce_one_mul_one hr (mem_peirce_one_of_mul hz) (mem_peirce_one_of_mul hw)
    rwa [mem_peirce, one_smul] at this
  have prodform : ∀ (a b : ℝ) (z w : Alb), r * z = z → r * w = w →
      (a • p + z) * (b • p + w) = (a * b) • p + z * w := by
    intro a b z w hz hw
    simp only [pj_add_mul, pj_mul_add, pj_smul_mul, pj_mul_smul, hp, hpC w hw, hCp z hz,
      smul_zero, add_zero, zero_add]
    module
  have proj : ∀ (a : ℝ) (z : Alb), r * z = z → r * (a • p + z) = z := by
    intro a z hz
    rw [pj_mul_add, pj_mul_smul, hrp, smul_zero, zero_add, hz]
  -- the image `U = r S₂` is a unital subalgebra of `V₁(r)`
  have hre : r * e = r := by rw [← hsum, pj_mul_add, hrp, hr, zero_add]
  set U := S₂.map (jL r) with hU
  have hmemU : ∀ z, z ∈ U ↔ ∃ y ∈ S₂, r * y = z := fun z => by
    simp only [hU, Submodule.mem_map, jL_apply]
  have hrU : r ∈ U := (hmemU r).2 ⟨e, h₂.unit_mem, hre⟩
  have hUunit : ∀ z ∈ U, r * z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hmemU z).1 hz
    obtain ⟨y', hy'C, hry, -⟩ := dec h₂ h12 y hy
    rw [hry, hy'C]
  have hUmul : ∀ z ∈ U, ∀ w ∈ U, z * w ∈ U := by
    intro z hz w hw
    obtain ⟨y, hy, rfl⟩ := (hmemU z).1 hz
    obtain ⟨y₂, hy₂, rfl⟩ := (hmemU w).1 hw
    obtain ⟨y', hy'C, hry, hyeq⟩ := dec h₂ h12 y hy
    obtain ⟨y₂', hy₂'C, hry₂, hy₂eq⟩ := dec h₂ h12 y₂ hy₂
    refine (hmemU _).2 ⟨y * y₂, h₂.mul_mem y hy y₂ hy₂, ?_⟩
    rw [hry, hry₂]
    conv_lhs => rw [hyeq, hy₂eq]
    rw [prodform _ _ _ _ hy'C hy₂'C, proj _ _ (hCmul _ _ hy'C hy₂'C)]
  by_cases hUtriv : ∀ q ∈ U, q * q = q → q = 0 ∨ q = r
  · -- the image is `ℝ r`: `S₂ ⊆ ℝ p + ℝ r`
    left
    have hUr := span_of_no_idem hrU hUmul hUunit hUtriv
    refine smallSpan2 hp hr hpr fun y hy => ?_
    obtain ⟨y', -, hry, hyeq⟩ := dec h₂ h12 y hy
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hUr ((hmemU _).2 ⟨y, hy, hry⟩))
    exact ⟨T (p * y), b, by rw [hb]; exact hyeq⟩
  right
  push Not at hUtriv
  obtain ⟨q₁, hq₁U, hq₁, hq₁0, hq₁r⟩ := hUtriv
  have hq₁C : r * q₁ = q₁ := hUunit q₁ hq₁U
  have hq₁r' : q₁ * r = q₁ := by rw [Albert.mul_comm']; exact hq₁C
  set q₂ := r - q₁ with hq₂def
  have hq₂ : q₂ * q₂ = q₂ := idem_sub hr hq₁ hq₁C
  have hq₂C : r * q₂ = q₂ := by rw [hq₂def, pj_mul_sub, hr, hq₁C]
  have hq₁₂ : q₁ * q₂ = 0 := by rw [hq₂def, pj_mul_sub, hq₁r', hq₁, sub_self]
  have hq₂0 : q₂ ≠ 0 := fun h => hq₁r (sub_eq_zero.mp h).symm
  have hTq : T q₁ + T q₂ = 2 := by rw [hq₂def, T_sub, htr]; ring
  have hTq₁ : T q₁ = 1 := by
    rcases T_pos_cases hq₁ hq₁0 with h | h | h <;> rcases T_pos_cases hq₂ hq₂0 with h' | h' | h' <;>
      linarith
  have hTq₂ : T q₂ = 1 := by linarith
  -- fix G1: an idempotent `q̃ = δ p + q₁` in `S₂`
  obtain ⟨q, hqS, hq⟩ := (hmemU q₁).1 hq₁U
  obtain ⟨q', -, hrq, hqeq⟩ := dec h₂ h12 q hqS
  rw [hq] at hrq
  subst hrq
  set γ := T (p * q)
  have hqq : q * q = (γ * γ) • p + q₁ := by
    conv_lhs => rw [hqeq]
    rw [prodform _ _ _ _ hq₁C hq₁C, hq₁]
  obtain ⟨qt, hqtS, hqt, δ, hqteq⟩ : ∃ qt ∈ S₂, qt * qt = qt ∧ ∃ δ : ℝ, qt = δ • p + q₁ := by
    by_cases hγ : γ * γ = γ
    · refine ⟨q, hqS, ?_, γ, hqeq⟩
      rw [hqq, hγ, ← hqeq]
    · have hne : γ - γ * γ ≠ 0 := fun h => hγ (by linarith)
      have hpS2 : p ∈ S₂ := by
        have h1 : q - q * q = (γ - γ * γ) • p := by
          conv_lhs => rw [hqq]
          conv_lhs => rw [hqeq]
          rw [sub_smul]; abel
        have h2 : p = (γ - γ * γ)⁻¹ • (q - q * q) := by
          rw [h1, _root_.smul_smul, inv_mul_cancel₀ hne, one_smul]
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hqS (h₂.mul_mem q hqS q hqS))
      refine ⟨q₁, ?_, hq₁, 0, by rw [zero_smul, zero_add]⟩
      have : q₁ = q - γ • p := by rw [hqeq]; abel
      rw [this]
      exact Submodule.sub_mem _ hqS (Submodule.smul_mem _ _ hpS2)
  -- `S₃ ⊆ ℝ p + ℝ q₁ + ℝ q₂`
  have hpq₁ : p * q₁ = 0 := hpC q₁ hq₁C
  have hpq₂ : p * q₂ = 0 := hpC q₂ hq₂C
  refine smallSpan3 hp hq₁ hq₂ hpq₁ hpq₂ hq₁₂ fun y hy => ?_
  obtain ⟨y', hy'C, -, hyeq⟩ := dec h₃ h13 y hy
  have hcomm := h23.idem hqtS hqt hy
  set d := T (p * y)
  have hw : r * (q₁ * y') = q₁ * y' := hCmul _ _ hq₁C hy'C
  rw [hqteq, hyeq, prodform _ _ _ _ hq₁C hy'C, prodform _ _ _ _ hq₁C hw] at hcomm
  have hcomm' := congrArg (HMul.hMul r) hcomm
  rw [proj _ _ (hCmul _ _ hq₁C hw), proj _ _ hw] at hcomm'
  have e1 := rank_one_peirce hq₁ hTq₁ hcomm'
  have hq₂y : q₂ * (y' - q₁ * y') = y' - q₁ * y' := by
    rw [pj_mul_sub, e1, pj_mul_smul, mul_comm' q₂ q₁, hq₁₂, smul_zero, sub_zero, hq₂def,
      pj_sub_mul, hy'C, ← e1]
  have e2 := rank_one_peirce hq₂ hTq₂ hq₂y
  refine ⟨d, T (q₁ * y'), T (y' - q₁ * y'), ?_⟩
  conv_lhs => rw [hyeq]
  rw [← e1, ← e2]; abel

end Core

/-- **The three-way no-go in `M₃(𝕆)_sa`** (research note `rec136-native.md` §3, with the
review's fixes G1, G2): three unital subalgebras `S₁, S₂, S₃` of a corner `Alb₁(e)` whose
multiplication operators commute pairwise (`OpComm S_i S_j` for `i < j`) cannot all avoid
the span of at most three pairwise orthogonal idempotents. -/
theorem alb_threeway_nogo {e : Alb} {S₁ S₂ S₃ : Submodule ℝ Alb} (h₁ : IsCornerSub e S₁)
    (h₂ : IsCornerSub e S₂) (h₃ : IsCornerSub e S₃) (h12 : OpComm S₁ S₂) (h13 : OpComm S₁ S₃)
    (h23 : OpComm S₂ S₃) : AlbSmallSpan S₁ ∨ AlbSmallSpan S₂ ∨ AlbSmallSpan S₃ := by
  have he : e * e = e := h₁.unit_mul e h₁.unit_mem
  by_cases hS1 : ∀ q ∈ S₁, q * q = q → q = 0 ∨ q = e
  · exact Or.inl (smallSpan1 he (span_of_no_idem h₁.unit_mem h₁.mul_mem h₁.unit_mul hS1))
  push Not at hS1
  obtain ⟨p₁, hp₁S, hp₁, hp₁0, hp₁e⟩ := hS1
  have hep₁ : e * p₁ = p₁ := h₁.unit_mul p₁ hp₁S
  have hp₁e' : p₁ * e = p₁ := by rw [Albert.mul_comm']; exact hep₁
  set p₂ := e - p₁ with hp₂def
  have hp₂S : p₂ ∈ S₁ := Submodule.sub_mem _ h₁.unit_mem hp₁S
  have hp₂ : p₂ * p₂ = p₂ := idem_sub he hp₁ hep₁
  have hp₁₂ : p₁ * p₂ = 0 := by rw [hp₂def, pj_mul_sub, hp₁e', hp₁, sub_self]
  have hp₂₁ : p₂ * p₁ = 0 := by rw [Albert.mul_comm']; exact hp₁₂
  have hp₂0 : p₂ ≠ 0 := fun h => hp₁e (sub_eq_zero.mp h).symm
  have hsum : T p₁ + T p₂ = T e := by rw [hp₂def, T_sub]; ring
  have hTe : T e ≤ 3 := by
    rcases T_idem_cases he with h | h | h | h <;> linarith
  have hs12 : p₁ + p₂ = e := by rw [hp₂def]; abel
  have hs21 : p₂ + p₁ = e := by rw [hp₂def]; abel
  right
  rcases T_pos_cases hp₁ hp₁0 with a | a | a <;> rcases T_pos_cases hp₂ hp₂0 with b | b | b
  · exact core h₂ h₃ h12 h13 h23 hp₁S hp₁ hp₂ hp₁₂ hs12 a (Or.inl b)
  · exact core h₂ h₃ h12 h13 h23 hp₁S hp₁ hp₂ hp₁₂ hs12 a (Or.inr b)
  · exfalso; linarith
  · exact core h₂ h₃ h12 h13 h23 hp₂S hp₂ hp₁ hp₂₁ hs21 b (Or.inr a)
  all_goals exfalso; linarith

/-! ## §B. A multiplicative map into a small span gives a Jordan hom into `C(ULift (Fin n), ℂ)` -/

theorem coord_mul {n : ℕ} {q : Fin n → Alb} (hq : ∀ i, q i * q i = q i)
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (k : Fin n) {x : Alb}
    (hx : x ∈ Submodule.span ℝ (Set.range q)) :
    x * q k = (⟪x, q k⟫_ℝ / ⟪q k, q k⟫_ℝ) • q k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    by_cases hik : i = k
    · subst hik
      by_cases h0 : q i = 0
      · rw [h0, pj_mul_zero, smul_zero]
      · rw [div_self (inner_self_ne_zero.mpr h0), one_smul, hq]
    · rw [horth i k hik, idem_inner_orth (hq i) (horth i k hik), zero_div, zero_smul]
  | zero => rw [pj_zero_mul, inner_zero_left, zero_div, zero_smul]
  | add x y _ _ hx hy => rw [pj_add_mul, hx, hy, inner_add_left, add_div, add_smul]
  | smul r x _ hx =>
    rw [pj_smul_mul, hx, real_inner_smul_left, mul_div_assoc, _root_.smul_smul]

/-- The glue: a multiplicative linear `g : V → M₃(𝕆)_sa` with `g u ≠ 0` for an idempotent
`u`, whose range lies in the span of orthogonal idempotents `q_k`, gives the non-zero Jordan
homomorphism `a ↦ (⟨g a, q_k⟩ / ⟨q_k, q_k⟩)_k` into the commutative C*-algebra
`C(ULift (Fin n), ℂ)`; so `V` is not purely exceptional. -/
theorem false_of_smallSpan {V : Type v} [AddCommGroup V] [Module ℝ V] [PartialOrder V]
    [OrderUnitSpace V] [Mul V] (hpe : IsPurelyExceptional.{v, v} V) (g : V →ₗ[ℝ] Alb)
    (hg : ∀ a b, g (a * b) = g a * g b) {u : V} (hu : u * u = u) (hne : g u ≠ 0)
    (hS : AlbSmallSpan (LinearMap.range g)) : False := by
  obtain ⟨n, -, q, hq, horth, hsub⟩ := hS
  have hmem : ∀ a, g a ∈ Submodule.span ℝ (Set.range q) := fun a =>
    hsub (LinearMap.mem_range_self g a)
  let κ : Fin n → V → ℝ := fun k a => ⟪g a, q k⟫_ℝ / ⟪q k, q k⟫_ℝ
  have hκmul : ∀ k a b, κ k (a * b) = κ k a * κ k b := by
    intro k a b
    simp only [κ]
    rw [hg, inner_mul', coord_mul hq horth k (hmem a), real_inner_smul_right, mul_div_assoc]
  let Φ : V →ₗ[ℝ] C(ULift.{v} (Fin n), ℂ) :=
    { toFun := fun a => ⟨fun k => ((κ k.down a : ℝ) : ℂ), continuous_of_discreteTopology⟩
      map_add' := fun a b => by
        ext k; simp [κ, inner_add_left, add_div]
      map_smul' := fun r a => by
        ext k; simp [κ, real_inner_smul_left, mul_div_assoc] }
  have hΦ : IsJordanHomInto V C(ULift.{v} (Fin n), ℂ) Φ := by
    refine ⟨fun a => ?_, fun a b => ?_⟩
    · show star (Φ a) = Φ a
      ext k; simp [Φ]
    · ext k
      have := hκmul k.down a b
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk,
        ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply, this]
      simp only [Complex.ofReal_mul, Complex.real_smul]
      push_cast; ring
  have h0 := hpe _ Φ hΦ
  have hκ0 : ∀ k, κ k u = 0 := fun k => by
    have := congrArg (fun F : V →ₗ[ℝ] C(ULift.{v} (Fin n), ℂ) => F u ⟨k⟩) h0
    simpa [Φ] using this
  have hzero : ∀ y ∈ Submodule.span ℝ (Set.range q), g u * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      have := hκ0 k
      simp only [κ] at this
      rw [coord_mul hq horth k (hmem u), this, zero_smul]
    | zero => rw [pj_mul_zero]
    | add x y _ _ hx hy => rw [pj_mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [pj_mul_smul, hx, smul_zero]
  apply hne
  rw [← hu, hg]
  exact hzero _ (hmem u)

theorem cornerSub_range {V : Type*} [AddCommGroup V] [Module ℝ V] (mul : V → V → V)
    (g : V →ₗ[ℝ] Alb) (hg : ∀ a b, g (mul a b) = g a * g b) (u : V) (hu : ∀ a, mul u a = a) :
    IsCornerSub (g u) (LinearMap.range g) where
  unit_mem := LinearMap.mem_range_self g u
  mul_mem := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨mul a b, hg a b⟩
  unit_mul := by
    rintro _ ⟨a, rfl⟩
    rw [← hg, hu]

theorem opComm_range {V : Type*} [AddCommGroup V] [Module ℝ V] (g h : V →ₗ[ℝ] Alb)
    (hc : ∀ a b c, g a * (h b * g c) = h b * (g a * g c)) :
    OpComm (LinearMap.range g) (LinearMap.range h) := by
  rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩ _ ⟨b, rfl⟩
  exact hc a b c

end AlbNoGo

/-! ## §C. REC 135 and REC 136 from `JBWExceptionalSummand` and `ExceptionalAlbertMap` -/

section Rec135Native

open MonoidalCategory SequentialEffectus
open AlbNoGo Papers.EJA.Albert

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)
  (φ₀ : EffectMonoidHom (Scal C) I) (ψ₀ : EffectMonoidHom I (Scal C))
  (h1 : ∀ k, ψ₀.toFun (φ₀.toFun k) = k) (h2 : ∀ r, φ₀.toFun (ψ₀.toFun r) = r)

include h1 h2 in
/-- The contradiction (research note §2): a purely exceptional `V_W ≠ 0` is impossible.
In `X = (W ⊗ W) ⊗ W` the unital Jordan embeddings `ι₁ a = (a⊗1)⊗1`, `ι₂ b = (1⊗b)⊗1`,
`ι₃ c = 1⊗c` (REC 127) operator commute pairwise on the images (REC 126); `V_X` JW is
absurd via `ι₁`; otherwise its exceptional corner and `ExceptionalAlbertMap` give a
multiplicative `ψ : V_X → M₃(𝕆)_sa`, `ψ 1 ≠ 0`, and `alb_threeway_nogo` puts some
`ψ ∘ ι_i` into a span of orthogonal idempotents, contradicting pure exceptionality. -/
theorem native_absurd (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertMap.{v})
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
    [MonoidalSequentialEffectus C] {W : C} (hW : Nonempty (Stat W))
    (hpe : letI := jbMul (realSplit ψ₀) hRC h119 W;
      IsPurelyExceptional.{v, v} (VA (realSplit ψ₀) W)) : False := by
  set σs := realSplit ψ₀ with hσs
  have h0 : σs.s = 0 := rfl
  have hWne : ouUnit (VA σs W) ≠ 0 := unit_ne_zero_real φ₀ ψ₀ hW
  -- the three unital Jordan embeddings of `V_W` into `V_X`, `X = (W ⊗ W) ⊗ W`
  let ι₁ : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W) :=
    vtens σs (A := W ⊗ W) (B := W) (ouUnit (VA σs W)) ∘ₗ vtens σs (A := W) (B := W) (ouUnit (VA σs W))
  let ι₂ : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W) :=
    vtens σs (A := W ⊗ W) (B := W) (ouUnit (VA σs W)) ∘ₗ (vtens σs (A := W) (B := W)).flip (ouUnit (VA σs W))
  let ι₃ : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W) :=
    (vtens σs (A := W ⊗ W) (B := W)).flip (ouUnit (VA σs (W ⊗ W)))
  have ι₁_apply : ∀ a, ι₁ a = tensV σs (tensV σs a (ouUnit (VA σs W))) (ouUnit (VA σs W)) := fun a => rfl
  have ι₂_apply : ∀ b, ι₂ b = tensV σs (tensV σs (ouUnit (VA σs W)) b) (ouUnit (VA σs W)) := fun b => rfl
  have ι₃_apply : ∀ c, ι₃ c = tensV σs (ouUnit (VA σs (W ⊗ W))) c := fun c => rfl
  have R := rec127 σs hRC h119 h0 (W ⊗ W) W
  have RW := rec127 σs hRC h119 h0 W W
  have RWr := rec127_right σs hRC h119 h0 W W
  have R3 := rec127_right σs hRC h119 h0 (W ⊗ W) W
  set JX := jm σs hRC h119 ((W ⊗ W) ⊗ W) with hJX
  set JW := jm σs hRC h119 W with hJW
  have m₁ : ∀ a b, ι₁ (JW a b) = JX (ι₁ a) (ι₁ b) := fun a b => by
    rw [ι₁_apply, ι₁_apply, ι₁_apply, R.1, RW.1]
  have m₂ : ∀ a b, ι₂ (JW a b) = JX (ι₂ a) (ι₂ b) := fun a b => by
    rw [ι₂_apply, ι₂_apply, ι₂_apply, R.1, RWr.1]
  have m₃ : ∀ a b, ι₃ (JW a b) = JX (ι₃ a) (ι₃ b) := fun a b => by
    rw [ι₃_apply, ι₃_apply, ι₃_apply, R3.1]
  have u₁ : ι₁ (ouUnit (VA σs W)) = ouUnit (VA σs ((W ⊗ W) ⊗ W)) := by
    rw [ι₁_apply, tensV_unit, tensV_unit]
  have u₂ : ι₂ (ouUnit (VA σs W)) = ouUnit (VA σs ((W ⊗ W) ⊗ W)) := by
    rw [ι₂_apply, tensV_unit, tensV_unit]
  have u₃ : ι₃ (ouUnit (VA σs W)) = ouUnit (VA σs ((W ⊗ W) ⊗ W)) := by
    rw [ι₃_apply, tensV_unit]
  -- REC 126: the operator commutations
  have c12 : ∀ a b c, JX (ι₁ a) (JX (ι₂ b) (ι₁ c)) = JX (ι₂ b) (JX (ι₁ a) (ι₁ c)) := by
    intro a b c
    simp only [ι₁_apply, ι₂_apply, R.1]
    rw [rec126 σs hRC h119 h0 a b]
  have c13 : ∀ a b c, JX (ι₁ a) (JX (ι₃ b) (ι₁ c)) = JX (ι₃ b) (JX (ι₁ a) (ι₁ c)) :=
    fun a b c => rec126 σs hRC h119 h0 (tensV σs a (ouUnit (VA σs W))) b (ι₁ c)
  have c23 : ∀ a b c, JX (ι₂ a) (JX (ι₃ b) (ι₂ c)) = JX (ι₃ b) (JX (ι₂ a) (ι₂ c)) :=
    fun a b c => rec126 σs hRC h119 h0 (tensV σs (ouUnit (VA σs W)) a) b (ι₂ c)
  have hinj : Function.Injective ι₁ := (R.2.2.2.2 hW).comp (RW.2.2.2.2 hW)
  let iX := jbMul σs hRC h119 ((W ⊗ W) ⊗ W)
  let iW := jbMul σs hRC h119 W
  rcases hP (VA σs ((W ⊗ W) ⊗ W)) (jbw_real hRC h119 φ₀ ψ₀ h1 h2 _) with
    ⟨𝔄, j1, j2, j3, j4, φ', hφ'J, hφ'i, -⟩ | ⟨d, hd0, hdd, hdcen, hdvan⟩
  · -- `V_X` JW: `φ' ∘ ι₁` is a Jordan hom of `V_W` into a C*-algebra
    have hψ : IsJordanHomInto (VA σs W) 𝔄 (φ' ∘ₗ ι₁) := by
      refine ⟨fun a => hφ'J.1 _, fun a b => ?_⟩
      show φ' (ι₁ (JW a b)) = _
      rw [m₁]
      exact hφ'J.2 _ _
    have hz := LinearMap.congr_fun (hpe 𝔄 _ hψ) (ouUnit (VA σs W))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    exact hWne (hinj ((hφ'i (hz.trans (map_zero φ').symm)).trans (map_zero ι₁).symm))
  · -- the exceptional corner of `V_X` and the map into `M₃(𝕆)_sa`
    obtain ⟨W', ⟨ω'⟩, hpe', π, hπ1, hπm⟩ :=
      corner_of_summand σs hRC h119 h0 _ hd0 hdd hdcen hdvan
    let iW' := jbMul σs hRC h119 W'
    obtain ⟨χ, hχm, hχ1⟩ :=
      hS (VA σs W') (jbw_real hRC h119 φ₀ ψ₀ h1 h2 W') hpe' (unit_ne_zero_real φ₀ ψ₀ ⟨ω'⟩)
    let ψ := χ ∘ₗ π
    have ψm : ∀ a b, ψ (JX a b) = ψ a * ψ b := fun a b => by
      show χ (π (JX a b)) = _
      rw [hπm]
      exact hχm _ _
    have ψ1 : ψ (ouUnit (VA σs ((W ⊗ W) ⊗ W))) ≠ 0 := by
      show χ (π _) ≠ 0
      rw [hπ1]
      exact hχ1
    have hone1 : JW (ouUnit (VA σs W)) (ouUnit (VA σs W)) = (ouUnit (VA σs W)) := (jm_jb σs hRC h119 W).one_mul (ouUnit (VA σs W))
    have gm : ∀ (ι : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W)),
        (∀ a b, ι (JW a b) = JX (ι a) (ι b)) → ∀ a b, (ψ ∘ₗ ι) (JW a b) = (ψ ∘ₗ ι) a * (ψ ∘ₗ ι) b :=
      fun ι hι a b => by
        show ψ (ι (JW a b)) = ψ (ι a) * ψ (ι b)
        rw [hι, ψm]
    have hcs : ∀ (ι : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W)),
        (∀ a b, ι (JW a b) = JX (ι a) (ι b)) → ι (ouUnit (VA σs W)) = ouUnit (VA σs ((W ⊗ W) ⊗ W)) →
          IsCornerSub (ψ (ouUnit (VA σs ((W ⊗ W) ⊗ W)))) (LinearMap.range (ψ ∘ₗ ι)) :=
      fun ι hι hu => by
        have := cornerSub_range JW (ψ ∘ₗ ι) (gm ι hι) (ouUnit (VA σs W))
          (fun a => (jm_jb σs hRC h119 W).one_mul a)
        rwa [LinearMap.comp_apply, hu] at this
    have hoc : ∀ (ι κ : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W)),
        (∀ a b c, JX (ι a) (JX (κ b) (ι c)) = JX (κ b) (JX (ι a) (ι c))) →
          OpComm (LinearMap.range (ψ ∘ₗ ι)) (LinearMap.range (ψ ∘ₗ κ)) :=
      fun ι κ hc => opComm_range _ _ fun a b c => by
        show ψ (ι a) * (ψ (κ b) * ψ (ι c)) = ψ (κ b) * (ψ (ι a) * ψ (ι c))
        rw [← ψm, ← ψm, ← ψm, ← ψm, hc]
    have hfalse : ∀ (ι : VA σs W →ₗ[ℝ] VA σs ((W ⊗ W) ⊗ W)),
        (∀ a b, ι (JW a b) = JX (ι a) (ι b)) → ι (ouUnit (VA σs W)) = ouUnit (VA σs ((W ⊗ W) ⊗ W)) →
          AlbSmallSpan (LinearMap.range (ψ ∘ₗ ι)) → False :=
      fun ι hι hu hsm => false_of_smallSpan hpe (ψ ∘ₗ ι) (gm ι hι) hone1
        (by rw [LinearMap.comp_apply, hu]; exact ψ1) hsm
    rcases alb_threeway_nogo (hcs ι₁ m₁ u₁) (hcs ι₂ m₂ u₂) (hcs ι₃ m₃ u₃) (hoc ι₁ ι₂ c12)
      (hoc ι₁ ι₃ c13) (hoc ι₂ ι₃ c23) with h | h | h
    · exact hfalse ι₁ m₁ u₁ h
    · exact hfalse ι₂ m₂ u₂ h
    · exact hfalse ι₃ m₃ u₃ h

include h1 h2 in
/-- **REC 135** (short.tex:2395, Proposition) by the REC-native route: from
`JBWExceptionalSummand` (a corollary of REC 52) and `ExceptionalAlbertMap` (part (ii) of
`ExceptionalAlbertPoint` alone, a corollary of REC 55) only — no exchangeable families
(REC 133/134), no REC 132.  With scalars `[0,1]`, every `V_A` is a JW-algebra. -/
theorem rec135_native (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertMap.{v})
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
  exact native_absurd hRC h119 φ₀ ψ₀ h1 h2 hP hS hW hpe

end Rec135Native

section Rec136Native

open MonoidalCategory SequentialEffectus

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteCoproducts C]
  [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C] [SequentialEffectus C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalEffectus C]
  [MonoidalSequentialEffectus C]
  (hRC : AlfsenShultzResolventCriterion.{v}) (h119 : WeteringStateOrderLemma C)

include hRC h119 in
/-- **REC 136** (`thm:JW-algebra`, short.tex:2409, Theorem), statement exactly as `rec136`,
from `JBWExceptionalSummand` and `ExceptionalAlbertMap` (in place of REC 52, 55, 132);
proof as `rec136`, with `rec135_native` for `rec135`. -/
theorem rec136_native (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertMap.{v})
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
      (jbw_real hRC h119 φ₀ ψ₀ h1 h2) (rec135_native hRC h119 φ₀ ψ₀ h1 h2 hP hS)

/-- **REC 136** (`rec136_hypfree`'s statement) with REC 119 and REC 121's criterion
discharged, from `JBWExceptionalSummand` (corollary of REC 52) and `ExceptionalAlbertMap`
(corollary of REC 55, part (ii) of `ExceptionalAlbertPoint`) only. -/
theorem rec136_native_hypfree (hP : JBWExceptionalSummand.{v}) (hS : ExceptionalAlbertMap.{v})
    (hirr : IsIrreducible (Scal C)) (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_native alfsenShultzResolventCriterion_holds weteringStateOrderLemma_holds hP hS hirr h01

/-- **REC 136** (`rec136_hypfree`'s statement) from REC 52 and REC 55 alone, by the
REC-native route. -/
theorem rec136_native_HOS_shultz (hHOS : HancheOlsenStormerDecomposition.{v})
    (hSh : ShultzExceptionalStructure.{v}) (hirr : IsIrreducible (Scal C))
    (h01 : ¬ ScalarsAreTwo C) :
    ∃ F : C ⥤ JWnpcCat.{v}ᵒᵖ,
      (∀ A : C, ∃ e : Pred A ≃ Set.Icc (0 : (F.obj A).unop.carrier) (ouUnit _),
        (∀ a b : Pred A, a ≼ b ↔ (e a : (F.obj A).unop.carrier) ≤ e b) ∧
        (∀ (a b : Pred A) (h : Perp a b),
          (e (ovee a b h) : (F.obj A).unop.carrier) = e a + e b) ∧
        (e (truth A) : (F.obj A).unop.carrier) = ouUnit _) ∧
      (F.Faithful ↔ SeparatingPredicates C) :=
  rec136_native_hypfree (jbwExceptionalSummand_of_HOS hHOS) (exceptionalAlbertMap_of_shultz hSh)
    hirr h01

end Rec136Native

end Papers.REC

#print axioms Papers.REC.AlbNoGo.alb_threeway_nogo
#print axioms Papers.REC.exceptionalAlbertMap_of_point
#print axioms Papers.REC.rec135_native
#print axioms Papers.REC.rec136_native
#print axioms Papers.REC.rec136_native_hypfree
#print axioms Papers.REC.rec136_native_HOS_shultz
