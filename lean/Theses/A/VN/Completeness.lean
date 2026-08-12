/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines
3781–4999.

  §Completeness
    Closure of a Convex Subset  (parsecs 720–730: ultrastrongly continuous
                                 functionals, radially open sets,
                                 Hahn–Banach, ultraweak = ultrastrong
                                 closure of convex sets)
    Kaplansky's Density Theorem (parsec 740)
    Closedness of Subalgebras   (parsec 750)
    Completeness                (parsecs 760–770: B(H) and every von Neumann
                                 algebra are ultrastrongly complete and
                                 bounded ultraweakly complete; the unit ball
                                 is ultraweakly compact)

Statements only; every proof is `sorry`.  See `Theses/A/VN/Basic.lean` for
the encoding of the ultraweak/ultrastrong topologies; "ultrastrongly Cauchy"
for a net `(x_i)_{l}` is rendered as `‖x_i - x_j‖_ω → 0` along `l ×ˢ l` for
every np-functional `ω`, and "ultraweakly Cauchy" as `Cauchy (l.map (ω ∘ x))`
for every `ω`.
-/
import Theses.A.VN.Projections

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra Pointwise
open Filter Topology Theses Theses.A.CStar

-- `radialTopology` is intentionally a plain def, not an instance:
set_option warn.classDefReducibility false

universe u

namespace Theses.A.VN

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ## Parsec 720: ultrastrongly continuous functionals

**71I** (vn.tex:3783) and **72I** (vn.tex:3823): overview — nothing to
formalize. -/

section Functionals

variable [VonNeumannAlgebra A]

variable (A) in
/-- **72II** (`bstaromega`, vn.tex:3841, Definition): the functional
`b*ω : a ↦ ω(b* a b)` for an np-functional `ω` and `b ∈ A`. -/
noncomputable def bStarOmega (b : A) (ω : NPFunctional A) : A → ℂ :=
  fun a => ω (star b * a * b)

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 1a: `b*ω` is
an np-functional. -/
theorem bstaromega_np (b : A) (ω : NPFunctional A) :
    ∃ ω' : NPFunctional A, ⇑ω' = bStarOmega A b ω :=
  sorry

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 1b:
`|ω(a* b c)| ≤ ‖ω‖ ‖a‖_ω ‖b‖ ‖c‖_ω` (with `‖ω‖ = ω(1)` for the positive
functional `ω`). -/
theorem bstaromega_bound (ω : NPFunctional A) (a b c : A) :
    ‖ω (star a * b * c)‖ ≤
      (ω 1).re * omegaNorm A ω a * ‖b‖ * omegaNorm A ω c :=
  sorry

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 1c:
`‖b*ω - b'*ω‖ ≤ ‖ω‖ ‖b-b'‖_ω (‖b‖_ω + ‖b'‖_ω)` — rendered pointwise. -/
theorem bstaromega_lipschitz (ω : NPFunctional A) (b b' : A) (a : A) :
    ‖bStarOmega A b ω a - bStarOmega A b' ω a‖ ≤
      (ω 1).re * omegaNorm A ω (b - b') *
        (omegaNorm A ω b + omegaNorm A ω b') * ‖a‖ :=
  sorry

/-- **72III** (`bstaromega-basic`, vn.tex:3850, Exercise), part 2: if
`(b_n)_n` is `‖·‖_ω`-Cauchy, then `(b_n * ω)_n` is Cauchy in the operator
norm and converges to an np-functional. -/
theorem bstaromega_cauchy (ω : NPFunctional A) (b : ℕ → A)
    (hb : Tendsto (fun p : ℕ × ℕ => omegaNorm A ω (b p.1 - b p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ f : NPFunctional A, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ∀ a : A,
      ‖bStarOmega A (b n) ω a - f a‖ ≤ ε * ‖a‖ :=
  sorry

/-- **72IV** (vn.tex:3876, Exercise): an ultrastrongly continuous linear
functional `f` on a von Neumann algebra is bounded by `1` on some
`‖·‖_ω`-ball. -/
theorem us_continuous_bounded_on_ball (f : A →ₗ[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultrastrong A) _ ⇑f) :
    ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
      ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ 1 :=
  sorry

/-- **72V** (`normal-functionals-lemma`, vn.tex:3887, Lemma): for an
np-functional `ω` and a linear `f : A → ℂ` the following are equivalent:
(1) `|f(a)| ≤ B` on some `‖·‖_ω`-ball of radius `δ > 0`;
(2) `|f(a)| ≤ B ‖a‖_ω` for some `B > 0`;
(3) `f = [b, ·]_ω` for some `b` in the Hilbert space completion `H_ω` of
`A` for the inner product `[a, c]_ω = ω(a* c)` (rendered by an existential
completion `φ : A → H`);
(4) `f = f₀ + i f₁ - f₂ - i f₃` for np-functionals `f_k` dominated by
`B·ω` on the positive cone. -/
theorem normal_functionals_lemma (ω : NPFunctional A) (f : A →ₗ[ℂ] ℂ) :
    List.TFAE
      [∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
        ∀ a : A, omegaNorm A ω a ≤ δ → ‖f a‖ ≤ B,
       ∃ B : ℝ, 0 < B ∧ ∀ a : A, ‖f a‖ ≤ B * omegaNorm A ω a,
       ∃ (ι : Type u) (φ : A →ₗ[ℂ] lp (fun _ : ι => ℂ) 2),
        DenseRange ⇑φ ∧
        (∀ a c : A, ⟪φ a, φ c⟫ = ω (star a * c)) ∧
        ∃ b : lp (fun _ : ι => ℂ) 2, ∀ a : A, f a = ⟪b, φ a⟫,
       ∃ (g : Fin 4 → NPFunctional A) (B : ℝ), 0 < B ∧
        (∀ a : A, f a = g 0 a + Complex.I * g 1 a - g 2 a -
          Complex.I * g 3 a) ∧
        ∀ (k : Fin 4) (a : A), 0 ≤ a → (g k a).re ≤ B * (ω a).re] :=
  sorry

/-- **72XI** (`luws`, vn.tex:3989, Corollary): for a linear functional
`f : A → ℂ` on a von Neumann algebra the following are equivalent:
(1) `f` is ultrastrongly continuous; (2) `f` is ultraweakly continuous;
(3) `f = f₀ + i f₁ - f₂ - i f₃` for np-functionals `f_k`; (4) `f` is
bounded on some `‖·‖_ω`-ball; (5) `|f(a)| ≤ ‖a‖_ω` for some
np-functional `ω`. -/
theorem luws (f : A →ₗ[ℂ] ℂ) :
    List.TFAE
      [@Continuous A ℂ (ultrastrong A) _ ⇑f,
       @Continuous A ℂ (ultraweak A) _ ⇑f,
       ∃ g : Fin 4 → NPFunctional A, ∀ a : A,
        f a = g 0 a + Complex.I * g 1 a - g 2 a - Complex.I * g 3 a,
       ∃ (ω : NPFunctional A) (δ : ℝ), 0 < δ ∧
        BddAbove {r : ℝ | ∃ a : A, omegaNorm A ω a ≤ δ ∧ r = ‖f a‖},
       ∃ ω : NPFunctional A, ∀ a : A, ‖f a‖ ≤ omegaNorm A ω a] :=
  sorry

end Functionals

/-! ## Parsec 730: radially open sets and Hahn–Banach

**73I** (vn.tex:4019): introduction — nothing to formalize. -/

section Radial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (V) in
/-- **73II** (vn.tex:4025, Definition): a subset `s` of a real vector space
is **radially open** if from each of its points every ray initially stays
in `s`. -/
def RadiallyOpen (s : Set V) : Prop :=
  ∀ a ∈ s, ∀ v : V, ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 ≤ r → r < t → a + r • v ∈ s

variable (V) in
/-- **73III** (vn.tex:4033, Exercise), part 1: the radially open subsets of
a real vector space form a topology. -/
def radialTopology : TopologicalSpace V where
  IsOpen := RadiallyOpen V
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

/-- **73III** (vn.tex:4033, Exercise), part 2: with respect to the radial
topology, translations and scalar multiplication are continuous.
(Parts 3–4 — a radially open non-open subset of `ℝ²`, and the failure of
joint continuity of addition — are pictorial counterexamples, not
converted.) -/
theorem radialTopology_continuous (a : V) (c : ℝ) :
    @Continuous V V (radialTopology V) (radialTopology V) (fun x => x + a) ∧
      @Continuous V V (radialTopology V) (radialTopology V)
        (fun x => c • x) :=
  sorry

/-- **73III** (vn.tex:4033, Exercise), part 5: for radially open
`s ⊆ V` and `x, y ∈ V` the set `{t ∈ ℝ | t•x + (1-t)•y ∈ s}` is open. -/
theorem radialTopology_segment (s : Set V) (hs : RadiallyOpen V s)
    (x y : V) : IsOpen {t : ℝ | t • x + (1 - t) • y ∈ s} :=
  sorry

/-- **73III** (vn.tex:4033, Exercise), part 6: sums and positive dilates of
radially open sets are radially open. -/
theorem radialTopology_add (s t : Set V) (hs : RadiallyOpen V s)
    (ht : RadiallyOpen V t) :
    RadiallyOpen V (s + t) ∧
      RadiallyOpen V {x : V | ∃ l : ℝ, 0 < l ∧ ∃ a ∈ s, x = l • a} :=
  sorry

/-- **73IV** (`hahn-banach`, vn.tex:4072, Theorem): for every radially open
convex subset `K` of a real vector space with `0 ∉ K` there is a linear
`f : V → ℝ` with `f(x) > 0` for all `x ∈ K`. -/
theorem hahn_banach (K : Set V) (hK : RadiallyOpen V K)
    (hconv : Convex ℝ K) (h0 : (0 : V) ∉ K) :
    ∃ f : V →ₗ[ℝ] ℝ, ∀ x ∈ K, 0 < f x :=
  sorry

end Radial

/-- **73VIII** (`ultraclosed`, vn.tex:4160, Exercise): an ultrastrongly
closed *convex* subset of a von Neumann algebra is ultraweakly closed
(hence the ultrastrong and ultraweak closures of convex sets coincide).
The exercise's enumerated items are steps of the proof and are not
converted separately. -/
theorem ultraclosed [VonNeumannAlgebra A] (K : Set A) (hconv : Convex ℝ K)
    (hK : @IsClosed A (ultrastrong A) K) : @IsClosed A (ultraweak A) K :=
  sorry

/-! ## Parsec 740: Kaplansky's density theorem -/

section Kaplansky

variable [VonNeumannAlgebra A]

/-- **74I** (`proto-kaplansky`, vn.tex:4224, Proposition): for a continuous
`f : ℝ → ℝ` with `f(t) = O(t)`, the map `a ↦ f(a)` (continuous functional
calculus) is ultrastrongly continuous on the self-adjoint part of a von
Neumann algebra. -/
theorem proto_kaplansky (f : ℝ → ℝ) (hf : Continuous f)
    (hO : ∃ (n : ℕ) (b : ℝ), ∀ t : ℝ, (n : ℝ) ≤ |t| → |f t| ≤ b * |t|) :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A) (fun a => cfc f a)
      {a : A | IsSelfAdjoint a} :=
  sorry

/-- **74III** (`abs-us-cont`, vn.tex:4331, Corollary): `a ↦ |a|` is
ultrastrongly continuous on the self-adjoint part of a von Neumann
algebra. -/
theorem abs_us_cont :
    @ContinuousOn A A (ultrastrong A) (ultrastrong A)
      (fun a => cfc (fun t : ℝ => |t|) a) {a : A | IsSelfAdjoint a} :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem): if `b`
in a von Neumann algebra `B` is the ultrastrong limit of a net from a
C*-subalgebra `S`, then `b` is the ultrastrong limit of a net `(a_α)_α` in
`S` with `‖a_α‖ ≤ ‖b‖`. -/
theorem kaplansky (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖) ∧ USTendsto a l b :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 1: if moreover `b` is self-adjoint, the `a_α` can be chosen
self-adjoint. -/
theorem kaplansky_sa (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) (hsa : IsSelfAdjoint b) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ IsSelfAdjoint (a i)) ∧
        USTendsto a l b :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 2: if moreover `b` is positive, the `a_α` can be chosen positive. -/
theorem kaplansky_pos (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (b : A) (hb : b ∈ @closure A (ultrastrong A) S) (hpos : 0 ≤ b) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ ‖a i‖ ≤ ‖b‖ ∧ 0 ≤ a i) ∧ USTendsto a l b :=
  sorry

/-- **74IV** (`kaplansky`, vn.tex:4336, Kaplansky's Density Theorem),
part 3: if moreover `b` is an effect, the `a_α` can be chosen to be
effects. -/
theorem kaplansky_effects (S : StarSubalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (b : A)
    (hb : b ∈ @closure A (ultrastrong A) S) (heff : b ∈ effects A) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ a : ι → A,
      (∀ i, a i ∈ S ∧ a i ∈ effects A) ∧ USTendsto a l b :=
  sorry

/-- **74VI** (`dense-subalgebra`, vn.tex:4421, Corollary): given `ε > 0`
and an ultraweakly dense ∗-subalgebra `S` of a von Neumann algebra, every
element `a` is the ultrastrong limit of a net `(s_α)_α` from `S` with
`‖s_α‖ ≤ ‖a‖(1 + ε)`. -/
theorem dense_subalgebra (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (ε : ℝ) (hε : 0 < ε) (a : A) :
    ∃ (ι : Type u) (l : Filter ι), l.NeBot ∧ ∃ s : ι → A,
      (∀ i, s i ∈ S ∧ ‖s i‖ ≤ ‖a‖ * (1 + ε)) ∧ USTendsto s l a :=
  sorry

/-! ## Parsec 750: closedness of subalgebras

**75I** (vn.tex:4460): introduction — nothing to formalize. -/

/-- **75II** (`sequence-separation-lemma`, vn.tex:4469, Lemma): let `S` be
a von Neumann subalgebra of `A`, and let `ω₀`, `ω₁` be npu-functionals on
`A` separated by a net `(b_α)_α` of effects of `S` (i.e.
`ω₀(b_α) → 0` and `ω₁(b_α^⊥) → 0`).  Then `ω₀` and `ω₁` are separated by a
projection `q ∈ S`: `ω₀(q) = 0 = ω₁(q^⊥)`. -/
theorem sequence_separation_lemma (S : StarSubalgebra ℂ A)
    (hS : IsVNSubalgebra A S) (ω₀ ω₁ : NPFunctional A) (hω₀ : ω₀ 1 = 1)
    (hω₁ : ω₁ 1 = 1) {ι : Type*} {l : Filter ι} [l.NeBot] (b : ι → A)
    (hb : ∀ i, b i ∈ S ∧ b i ∈ effects A)
    (h₀ : Tendsto (fun i => ω₀ (b i)) l (𝓝 0))
    (h₁ : Tendsto (fun i => ω₁ (1 - b i)) l (𝓝 0)) :
    ∃ q : A, q ∈ S ∧ IsStarProjection q ∧ ω₀ q = 0 ∧ ω₁ (1 - q) = 0 :=
  sorry

/-- **75VI** (`kadisons-lemma`, vn.tex:4560, Lemma): let `S` be a von
Neumann subalgebra of `A` and `p` a projection of `A` in the ultrastrong
closure of `S`.  For all npu-functionals `ω₀`, `ω₁` with
`ω₀(p) = 0 = ω₁(p^⊥)` there is a projection `q ∈ S` with
`ω₀(q) = 0 = ω₁(q^⊥)`. -/
theorem kadisons_lemma (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S)
    (p : A) (hp : IsStarProjection p)
    (hcl : p ∈ @closure A (ultrastrong A) S) (ω₀ ω₁ : NPFunctional A)
    (hω₀ : ω₀ 1 = 1) (hω₁ : ω₁ 1 = 1) (h₀ : ω₀ p = 0)
    (h₁ : ω₁ (1 - p) = 0) :
    ∃ q : A, q ∈ S ∧ IsStarProjection q ∧ ω₀ q = 0 ∧ ω₁ (1 - q) = 0 :=
  sorry

/-- **75VIII** (`vnsac`, vn.tex:4587, Theorem): a von Neumann subalgebra of
a von Neumann algebra is ultrastrongly and ultraweakly closed. -/
theorem vnsac (S : StarSubalgebra ℂ A) (hS : IsVNSubalgebra A S) :
    @IsClosed A (ultrastrong A) (S : Set A) ∧
      @IsClosed A (ultraweak A) (S : Set A) :=
  sorry

end Kaplansky

/-! ## Parsec 760: completeness of B(H) -/

section BH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **76I** (`bh-us-complete`, vn.tex:4641, Proposition): `B(H)` is
ultrastrongly complete: every ultrastrongly Cauchy net converges
ultrastrongly. -/
theorem bh_us_complete {ι : Type*} (l : Filter ι) [l.NeBot]
    (T : ι → H →L[ℂ] H)
    (hcauchy : ∀ ω : NPFunctional (H →L[ℂ] H),
      Tendsto (fun p : ι × ι => omegaNorm _ ω (T p.1 - T p.2)) (l ×ˢ l)
        (𝓝 0)) :
    ∃ T₀ : H →L[ℂ] H, USTendsto T l T₀ :=
  sorry

/-- **76III** (`bh-bounded-uw-complete`, vn.tex:4744, Proposition): `B(H)`
is bounded ultraweakly complete: every norm-bounded ultraweakly Cauchy net
converges ultraweakly. -/
theorem bh_bounded_uw_complete {ι : Type*} (l : Filter ι) [l.NeBot]
    (T : ι → H →L[ℂ] H) (hbdd : ∃ C : ℝ, ∀ i, ‖T i‖ ≤ C)
    (hcauchy : ∀ ω : NPFunctional (H →L[ℂ] H),
      Cauchy (l.map fun i => ω (T i))) :
    ∃ T₀ : H →L[ℂ] H, UWTendsto T l T₀ :=
  sorry

end BH

/-! ## Parsec 770: completeness of a von Neumann algebra -/

section Complete

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **77I** (`vn-complete`, vn.tex:4808, Theorem), part 1: a von Neumann
algebra is ultrastrongly complete. -/
theorem vn_complete_1 {ι : Type*} (l : Filter ι) [l.NeBot] (x : ι → A)
    (hcauchy : ∀ ω : NPFunctional A,
      Tendsto (fun p : ι × ι => omegaNorm A ω (x p.1 - x p.2)) (l ×ˢ l)
        (𝓝 0)) :
    ∃ a : A, USTendsto x l a :=
  sorry

/-- **77I** (`vn-complete`, vn.tex:4808, Theorem), part 2: a von Neumann
algebra is bounded ultraweakly complete. -/
theorem vn_complete_2 {ι : Type*} (l : Filter ι) [l.NeBot] (x : ι → A)
    (hbdd : ∃ C : ℝ, ∀ i, ‖x i‖ ≤ C)
    (hcauchy : ∀ ω : NPFunctional A, Cauchy (l.map fun i => ω (x i))) :
    ∃ a : A, UWTendsto x l a :=
  sorry

/-- **77III** (`vn-ball-compact`, vn.tex:4847, Theorem): the unit ball of a
von Neumann algebra is ultraweakly compact. -/
theorem vn_ball_compact :
    @IsCompact A (ultraweak A) (Metric.closedBall (0 : A) 1) :=
  sorry

/-- **77V** (`vn-extension`, vn.tex:4879, Proposition): an ultraweakly
continuous bounded linear map `f` on an ultraweakly dense ∗-subalgebra `S`
of a von Neumann algebra `A` extends uniquely to an ultraweakly continuous
(linear) map `g : A → B`. -/
theorem vn_extension (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (f : S →ₗ[ℂ] B)
    (hf : @Continuous S B (TopologicalSpace.induced Subtype.val (ultraweak A))
      (ultraweak B) ⇑f)
    (C : ℝ) (hC : ∀ s : S, ‖f s‖ ≤ C * ‖(s : A)‖) :
    ∃! g : A →ₗ[ℂ] B,
      @Continuous A B (ultraweak A) (ultraweak B) ⇑g ∧ ∀ s : S, g s = f s :=
  sorry

/-- **77V** (`vn-extension`, vn.tex:4879, Proposition), norm part: the
extension `g` is bounded with `‖g‖ = ‖f‖` — rendered: `g` satisfies every
bound `C` that `f` does. -/
theorem vn_extension_norm (S : StarSubalgebra ℂ A)
    (hS : @Dense A (ultraweak A) (S : Set A)) (f : S →ₗ[ℂ] B)
    (hf : @Continuous S B (TopologicalSpace.induced Subtype.val (ultraweak A))
      (ultraweak B) ⇑f)
    (C : ℝ) (hC : ∀ s : S, ‖f s‖ ≤ C * ‖(s : A)‖) (g : A →ₗ[ℂ] B)
    (hg : @Continuous A B (ultraweak A) (ultraweak B) ⇑g)
    (hext : ∀ s : S, g s = f s) (a : A) :
    ‖g a‖ ≤ C * ‖a‖ :=
  sorry

end Complete

end Theses.A.VN
