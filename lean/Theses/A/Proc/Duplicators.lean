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

/-- **127III** (`duplicable`, proc.tex:5881, Theorem), uniqueness: in that
case the duplicator is unique, given by `δ(a ⊗ b) = a·b` and `u = 1`. -/
theorem duplicable_unique [VonNeumannAlgebra A] (d : Duplicator A) :
    d.unit = 1 ∧ ∀ a b : A, d.δ (a ⊗ᵥ b) = a * b := sorry

/-- **127VI** (`lem:unit-duplicator`, proc.tex:5925, Lemma): the unit of a
duplicator is `1`, and `δ(1 ⊗ 1) = 1`. -/
theorem unit_duplicator [VonNeumannAlgebra A] (d : Duplicator A) :
    d.unit = 1 ∧ d.δ ((1 : A) ⊗ᵥ (1 : A)) = 1 := sorry

/-! ## Parsec 1280: Tomiyama's theorem and commutativity -/

/-- **128II** (`tomiyama`, proc.tex:5948, Theorem (Tomiyama)): a linear
surjection `f : 𝒜 → ℬ` of a von Neumann algebra onto a von Neumann
subalgebra `ℬ ⊆ 𝒜` with `f ∘ f = f` and `‖f(a)‖ ≤ ‖a‖` satisfies
`b·f(a) = f(b·a)` for all `a ∈ 𝒜`, `b ∈ ℬ`. -/
theorem tomiyama [VonNeumannAlgebra A] (S : StarSubalgebra ℂ A)
    (hS : IsVNSubalgebra A S) (f : A →ₗ[ℂ] A)
    (hrange : Set.range ⇑f = (S : Set A)) (hproj : ∀ a, f (f a) = f a)
    (hnorm : ∀ a, ‖f a‖ ≤ ‖a‖) :
    ∀ b ∈ S, ∀ a : A, b * f a = f (b * a) := sorry

/- **128IV–V** (proc.tex:6011): moved/removed points — nothing to
convert. -/

section Pairs

variable [Nontrivial A]

/-- The element `(a, b)` of the direct sum `𝒜 ⊕ 𝒜 = lp (Fin 2 → 𝒜) ∞`
(helper for 128VI). -/
noncomputable def pairLp (a b : A) : lp (fun _ : Fin 2 => A) ∞ :=
  lp.single ∞ 0 a + lp.single ∞ 1 b

/-- **128VI** (`lem:sef-instrument`, proc.tex:6015, Lemma): for a pu-map
`f : 𝒜 ⊕ 𝒜 → 𝒜` with `f(a,a) = a`, the element `p := f(1,0)` is
central and `f(a,b) = a·p + b·p^⊥`. -/
theorem sef_instrument [VonNeumannAlgebra A]
    (f : lp (fun _ : Fin 2 => A) ∞ →ₗ[ℂ] A)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hu : f 1 = 1)
    (hdiag : ∀ a : A, f (pairLp a a) = a) :
    f (pairLp 1 0) ∈ centre A ∧
      ∀ a b : A, f (pairLp a b) =
        a * f (pairLp 1 0) + b * (1 - f (pairLp 1 0)) := sorry

end Pairs

/-- **128VIII** (`lem:uniqueness-duplicator`, proc.tex:6059, Lemma): a
von Neumann algebra with a duplicator `δ` is commutative, and
`δ(a ⊗ b) = a·b`. -/
theorem uniqueness_duplicator [VonNeumannAlgebra A] (d : Duplicator A) :
    (∀ a b : A, a * b = b * a) ∧ ∀ a b : A, d.δ (a ⊗ᵥ b) = a * b := sorry

/-- **128XI** (`cor:duplicability-multiplication`, proc.tex:6109,
Corollary): `𝒜` is duplicable iff there is an np-map
`δ : 𝒜 ⊗ 𝒜 → 𝒜` with `δ(a ⊗ b) = a·b` (and in that case `𝒜` is
commutative). -/
theorem duplicability_multiplication [VonNeumannAlgebra A] :
    (Duplicable A ↔
      ∃ δ : VNT A A →ₚ[ℂ] A, PreservesDirSups ⇑δ ∧
        ∀ a b : A, δ (a ⊗ᵥ b) = a * b) ∧
    (Duplicable A → ∀ a b : A, a * b = b * a) := sorry

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
sense that `μ(B') = μ(B)` for every `B' ∈ 𝒮` containing `B`. -/
theorem measure_zorn [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (𝒮 : Set (Set X)) (hmeas : ∀ S ∈ 𝒮, MeasurableSet S)
    (hchain : ∀ f : ℕ → Set X, (∀ n, f n ∈ 𝒮) → Monotone f →
      ∃ S ∈ 𝒮, ∀ n, f n ⊆ S) :
    ∀ S ∈ 𝒮, ∃ T ∈ 𝒮, S ⊆ T ∧ ∀ T' ∈ 𝒮, T ⊆ T' → μ T' = μ T := sorry

/-- **129VI** (`lem:measure-space-continuous-discrete`, proc.tex:6279,
Lemma): each finite complete measure space contains a discrete measurable
subset `D` such that `X ∖ D` is continuous. -/
theorem measure_space_continuous_discrete [IsFiniteMeasure μ]
    (hμ : μ.IsComplete) :
    ∃ D : Set X, MeasurableSet D ∧
      (∃ 𝒞 : Set (Set X), (∀ S ∈ 𝒞, AtomicSet μ S) ∧ D ⊆ ⋃₀ 𝒞) ∧
      ∀ S : Set X, S ⊆ Set.univ \ D → ¬ AtomicSet μ S := sorry

/-- **129VIII** (`lem:continuous-measure-space`, proc.tex:6305, Lemma):
for a continuous finite complete measure space `X` and
`r ∈ [0, μ(X)]` there is a measurable `A ⊆ X` with `μ(A) = r`. -/
theorem continuous_measure_space [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hc : ContinuousSpace μ) (r : ℝ≥0∞) (hr : r ≤ μ Set.univ) :
    ∃ S : Set X, MeasurableSet S ∧ μ S = r := sorry

variable (𝒜 : Type u) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] in
/-- The Prop "`𝒜` is (a copy of) `L^∞(X, μ)` via the quotient map `q`"
(mirroring the rendering of vn.tex 51IX, `Linfty_vn`). -/
structure IsLinftyOf (q : (X → ℂ) → 𝒜) : Prop where
  surj : ∀ y : 𝒜, ∃ f, IsBoundedMeasurable X f ∧ q f = y
  add : ∀ f g, IsBoundedMeasurable X f → IsBoundedMeasurable X g →
    q (f + g) = q f + q g
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

/-- **130II** (`lem:atomic-measure-space`, proc.tex:6471, Lemma): for an
atomic measure space `A` we have `L^∞(A) ≅ ℂ`. -/
theorem atomic_measure_space [IsFiniteMeasure μ] (hμ : μ.IsComplete)
    (hX : AtomicSet μ Set.univ) (𝒜 : Type u) [CStarAlgebra 𝒜]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [VonNeumannAlgebra 𝒜]
    (q : (X → ℂ) → 𝒜) (hq : IsLinftyOf μ 𝒜 q) :
    ∃ φ : NMIUMap 𝒜 ℂ, Function.Bijective ⇑φ := sorry

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
    Duplicable A := sorry

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
        ∀ a b : A, f.toNCPMap (a * b) = f.toNCPMap a * f.toNCPMap b) :=
  sorry

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
      ∀ (a : A) (φ : nsp A), η a φ = φ a := sorry

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
