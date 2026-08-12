/-
Thesis A (Abraham Westerbaan, *The Category of Von Neumann Algebras*,
arXiv:1804.02203), chapter 2: Von Neumann Algebras — vn.tex, lines
6231–7332.

  §Normal Functionals
    Ultraweak Boundedness  (parsecs 860–870: positivity criterion, extreme
                            points of the unit ball, polar decomposition of
                            functionals, the predual, uniform boundedness)
    Ultraweak Permanence   (parsecs 880–900: relative suprema of
                            projections, the double commutant theorem,
                            representation of normal functionals as sums of
                            vector functionals, extension of normal
                            functionals, centre separating collections)

Statements only; every proof is `sorry`.  See `Theses/A/VN/Basic.lean` for
the topologies, and `Theses/A/VN/Projections.lean` for `ceil`, `carrier`,
`cceil`, `commutant` and `projSup`.
-/
import Theses.A.VN.Division

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra ENNReal
open Filter Topology Theses Theses.A.CStar

universe u

namespace Theses.A.VN

variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-! ## Parsec 860: ultraweak boundedness

**85I** (vn.tex:6233) and **86I** (vn.tex:6259): overview — nothing to
formalize. -/

/-- **86II** (`positive-functional-criterion`, vn.tex:6265, Lemma): a
(bounded) linear functional `f` on a C*-algebra is positive iff
`‖f‖ ≤ f(1)`. -/
theorem positive_functional_criterion (f : A →L[ℂ] ℂ) :
    (∀ a : A, 0 ≤ a → 0 ≤ f a) ↔ ((f 1).im = 0 ∧ ‖f‖ ≤ (f 1).re) :=
  sorry

/-- **86VI** (`vn-ball-extreme-point`, vn.tex:6320, Lemma): an extreme
point `u` of the unit ball of a C*-algebra is a partial isometry (i.e.
`u*u` is a projection) with `(uu*)^⊥ A (u*u)^⊥ = {0}`.  (**86VII**,
Remark: the converse also holds but is not needed — not converted.) -/
theorem vn_ball_extreme_point (u : A)
    (hu : u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : A) 1)) :
    IsStarProjection (star u * u) ∧
      ∀ a : A, (1 - u * star u) * a * (1 - star u * u) = 0 :=
  sorry

section VNA

variable [VonNeumannAlgebra A]

/-- **86IX** (`polar-decomposition-of-functional`, vn.tex:6373, Theorem
(Polar decomposition of functionals)): every linear functional `f` on a von
Neumann algebra that is ultraweakly continuous on the unit ball is of the
form `f = f(uu*(·)) = f((·)u*u)` for a partial isometry `u` such that
`f(u(·))` and `f((·)u)` are positive. -/
theorem polar_decomposition_of_functional (f : A →ₗ[ℂ] ℂ)
    (hf : @ContinuousOn A ℂ (ultraweak A) _ ⇑f (Metric.closedBall 0 1)) :
    ∃ u : A, IsPartialIsometry A u ∧
      (∀ a : A, f a = f (u * star u * a)) ∧
      (∀ a : A, f a = f (a * (star u * u))) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ f (u * a)) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ f (a * u)) :=
  sorry

/-- **86XII** (`uwcont-on-ball`, vn.tex:6435, Corollary): a functional on a
von Neumann algebra that is ultraweakly continuous on the unit ball is
ultraweakly continuous. -/
theorem uwcont_on_ball (f : A →ₗ[ℂ] ℂ)
    (hf : @ContinuousOn A ℂ (ultraweak A) _ ⇑f (Metric.closedBall 0 1)) :
    @Continuous A ℂ (ultraweak A) _ ⇑f :=
  sorry

/-- **86XIV** (`functional-norm`, vn.tex:6460, Lemma): for a normal
(= ultraweakly continuous) functional `f` and a partial isometry `u` with
`f(u(·))` positive and `f = f(uu*(·))`: `‖f‖ = f(u)`. -/
theorem functional_norm (f : A →L[ℂ] ℂ)
    (hf : @Continuous A ℂ (ultraweak A) _ ⇑f) (u : A)
    (hu : IsPartialIsometry A u) (hpos : ∀ a : A, 0 ≤ a → 0 ≤ f (u * a))
    (heq : ∀ a : A, f a = f (u * star u * a)) :
    f u = (‖f‖ : ℂ) :=
  sorry

/-! ## Parsec 870: the predual -/

variable (A) in
/-- **87I** (vn.tex:6480, Definition): the **predual** `A_*` of a von
Neumann algebra: the (normed vector) space of ultraweakly continuous
functionals on `A`, rendered as a subset of the continuous dual.
(**87II**, Remark: Sakai's theorem `(A_*)* ≅ A` is neither needed nor
converted.) -/
def predual : Set (A →L[ℂ] ℂ) :=
  {f : A →L[ℂ] ℂ | @Continuous A ℂ (ultraweak A) _ ⇑f}

/-- **87III** (`predual-complete`, vn.tex:6509, Proposition): the predual
of a von Neumann algebra is complete with respect to the operator norm. -/
theorem predual_complete : IsComplete (predual A) :=
  sorry

/-! **87V** (vn.tex:6548): motivation for the next lemma — nothing to
formalize. -/

/-- **87VI** (`norm-predual`, vn.tex:6563, Lemma):
`‖a‖ = sup {|f(a)| : f ∈ (A_*)₁}` for every element `a` of a von Neumann
algebra. -/
theorem norm_predual (a : A) :
    IsLUB {r : ℝ | ∃ f ∈ predual A, ‖f‖ ≤ 1 ∧ r = ‖f a‖} ‖a‖ :=
  sorry

/-- **87VIII** (`ultraweakly-bounded-implies-bounded`, vn.tex:6584,
Theorem): a net `(b_α)_α` in a von Neumann algebra is norm bounded provided
it is **ultraweakly bounded**, i.e. `sup_α |ω(b_α)| < ∞` for every
np-functional `ω`. -/
theorem ultraweakly_bounded_implies_bounded {ι : Type*} (x : ι → A)
    (h : ∀ ω : NPFunctional A, BddAbove (Set.range fun i => ‖ω (x i)‖)) :
    BddAbove (Set.range fun i => ‖x i‖) :=
  sorry

/-! ## Parsec 880: ultraweak permanence and the double commutant theorem

**88I** (vn.tex:6622): overview — nothing to formalize. -/

variable (A) in
/-- **88II** (`commutant-ceil`, vn.tex:6669, Proposition), definition part:
the projection `⌈e⌉_{S^□} = ⋃_{a∈S} ⌈a* e a⌉`. -/
noncomputable def commutantCeil (S : Set A) (e : A) : A :=
  projSup {x : A | ∃ a ∈ S, x = ceil (star a * e * a)}

/-- **88II** (`commutant-ceil`, vn.tex:6669, Proposition): for a subset `S`
of a von Neumann algebra closed under multiplication and involution and
containing `1`, and a projection `e`: `⌈e⌉_{S^□} = ⋃_{a∈S} ⌈a* e a⌉` is
the least projection in `S^□` above `e`. -/
theorem commutant_ceil (S : Set A) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (hone : (1 : A) ∈ S) (e : A)
    (he : IsStarProjection e) :
    IsLeast {p : A | IsStarProjection p ∧ p ∈ commutant A S ∧ e ≤ p}
      (commutantCeil A S e) :=
  sorry

end VNA

section BH

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- **88IV** (`carrier-vector-state`, vn.tex:6714, Exercise): for a vector
`x` of a Hilbert space `H` and a unital ∗-subalgebra `S` of `B(H)`, the
least projection in `S^□` above `⌈|x⟩⟨x|⌉` equals
`⋃_{a∈S} ⌈|ax⟩⟨ax|⌉` and is the projection onto `closure (S x)` (a
projection identified by its fixed points).  (Item 2, identifying it with
the carrier of the vector functional restricted to `S^□`, needs the
relative carrier and is subsumed by the `IsLeast` formulation.) -/
theorem carrier_vector_state (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) =
        projSup {p : H →L[ℂ] H | ∃ T ∈ S, p = ketbra (T x) (T x)} ∧
      {y : H | commutantCeil (H →L[ℂ] H) S (ceil (ketbra x x)) y = y} =
        closure {y : H | ∃ T ∈ S, y = T x} :=
  sorry

/-- **88IV** (`carrier-vector-state`, vn.tex:6714, Exercise), conclusion:
`closure (S^□□ x) = closure (S x)`. -/
theorem carrier_vector_state' (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    closure {y : H | ∃ T ∈ commutant (H →L[ℂ] H)
        (commutant (H →L[ℂ] H) S), y = T x} =
      closure {y : H | ∃ T ∈ S, y = T x} :=
  sorry

/-- **88V** (`proto-double-commutant`, vn.tex:6737): for a unital
∗-subalgebra `S` of `B(H)`, the double commutant `S^□□` is contained in
the ultrastrong closure of `S`.  (The enumerated items are steps of the
proof, not converted separately.) -/
theorem proto_double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) ⊆
      @closure _ (ultrastrong (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) :=
  sorry

/-- **88VI** (`double-commutant`, vn.tex:6781, Double Commutant Theorem):
for a unital ∗-subalgebra `S` of `B(H)` the following coincide: the double
commutant `S^□□`, the ultrastrong closure of `S`, the ultraweak closure of
`S`, and the least von Neumann subalgebra `W*(S)` containing `S`. -/
theorem double_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) =
        @closure _ (ultrastrong (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) ∧
      commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) =
        @closure _ (ultraweak (H →L[ℂ] H)) (S : Set (H →L[ℂ] H)) ∧
      commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) S) =
        (wstar (H →L[ℂ] H) (S : Set (H →L[ℂ] H)) :
          StarSubalgebra ℂ (H →L[ℂ] H)) :=
  sorry

/-- **88VIII** (`centre-commutant`, vn.tex:6824, Exercise): for a von
Neumann subalgebra `R` of `B(H)`: `Z(R) = Z(R^□)`, i.e. the central
elements of `R` coincide with those of its commutant. -/
theorem centre_commutant (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hR : IsVNSubalgebra (H →L[ℂ] H) R) :
    (R : Set (H →L[ℂ] H)) ∩ commutant (H →L[ℂ] H) R =
      commutant (H →L[ℂ] H) R ∩
        commutant (H →L[ℂ] H) (commutant (H →L[ℂ] H) R) :=
  sorry

/-- **88IX** (`commutant-cceil`, vn.tex:6831): for an np-map
`f : B(H) → B` and a von Neumann subalgebra `R` of `B(H)`, the central
carrier of `f` relative to `R` coincides with the central carrier of `f`
relative to `R^□`: some projection is least among the central projections
`p` of `R` with `f(p^⊥) = 0` and least among those of `R^□`. -/
theorem commutant_cceil [VonNeumannAlgebra B]
    (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hR : IsVNSubalgebra (H →L[ℂ] H) R) (f : (H →L[ℂ] H) →ₚ[ℂ] B)
    (hf : PreservesDirSups ⇑f) :
    ∃ c : H →L[ℂ] H,
      IsLeast {p : H →L[ℂ] H | p ∈ R ∧ IsStarProjection p ∧
        (∀ b ∈ R, p * b = b * p) ∧ f (1 - p) = 0} c ∧
      IsLeast {p : H →L[ℂ] H | p ∈ commutant (H →L[ℂ] H) R ∧
        IsStarProjection p ∧
        (∀ b ∈ commutant (H →L[ℂ] H) R, p * b = b * p) ∧
        f (1 - p) = 0} c :=
  sorry

/-! ## Parsec 890: normal functionals as sums of vector functionals -/

variable [VonNeumannAlgebra A]

/-- **89I** (`gns-mapping-property`, vn.tex:6839, Lemma): if an
np-functional `ω` on a von Neumann algebra is represented by nmiu-maps
`ρ : A → B(H)` and `π : A → B(K)` with vectors `x ∈ H`, `y ∈ K` — i.e.
`⟨x,ρ(·)x⟩ = ω = ⟨y,π(·)y⟩` — then there is a bounded `U : K → H` with
`UU*` the projection onto `closure (ρ(A)x)`, `U*U` the projection onto
`closure (π(A)y)`, and `Uπ(a) = ρ(a)U` for all `a`. -/
theorem gns_mapping_property (ω : NPFunctional A)
    (ρ : NMIUMap A (H →L[ℂ] H)) (π : NMIUMap A (K →L[ℂ] K)) (x : H) (y : K)
    (hx : ∀ a : A, ω a = ⟪x, ρ a x⟫) (hy : ∀ a : A, ω a = ⟪y, π a y⟫) :
    ∃ U : K →L[ℂ] H,
      {z : H | (U ∘L ContinuousLinearMap.adjoint U) z = z} =
          closure {z : H | ∃ a : A, z = ρ a x} ∧
      {z : K | (ContinuousLinearMap.adjoint U ∘L U) z = z} =
          closure {z : K | ∃ a : A, z = π a y} ∧
      ∀ a : A, U ∘L π a = ρ a ∘L U :=
  sorry

/-- **89III** (`summing-partial-isometries`, vn.tex:6901, Exercise): given
bounded operators `Uᵢ : H → K` such that the `Uᵢ*Uᵢ` are pairwise
orthogonal projections and the `UᵢUᵢ*` are pairwise orthogonal
projections, there is a bounded `V : H → K` with
`⟪y, Vx⟫ = ∑ᵢ ⟪y, Uᵢx⟫`, `V*V = ∑ᵢ Uᵢ*Uᵢ` and `VV* = ∑ᵢ UᵢUᵢ*` (the
last two sums taken pointwise). -/
theorem summing_partial_isometries {ι : Type*} (U : ι → (H →L[ℂ] K))
    (hproj : ∀ i, IsStarProjection (ContinuousLinearMap.adjoint (U i) ∘L U i))
    (horthL : Pairwise fun i j =>
      (ContinuousLinearMap.adjoint (U i) ∘L U i) ∘L
        (ContinuousLinearMap.adjoint (U j) ∘L U j) = 0)
    (horthR : Pairwise fun i j =>
      (U i ∘L ContinuousLinearMap.adjoint (U i)) ∘L
        (U j ∘L ContinuousLinearMap.adjoint (U j)) = 0) :
    ∃ V : H →L[ℂ] K,
      (∀ (x : H) (y : K), HasSum (fun i => ⟪y, U i x⟫) ⟪y, V x⟫) ∧
      (∀ x : H, HasSum (fun i => (ContinuousLinearMap.adjoint (U i) ∘L U i) x)
        ((ContinuousLinearMap.adjoint V ∘L V) x)) ∧
      (∀ y : K, HasSum (fun i => (U i ∘L ContinuousLinearMap.adjoint (U i)) y)
        ((V ∘L ContinuousLinearMap.adjoint V) y)) :=
  sorry

/-- **89V** (`sigma-weak-lemma-2`, vn.tex:6952, Lemma): let `Ω` be a
collection of np-functionals on a von Neumann algebra `A` with pairwise
orthogonal central carriers, and let `ρ : A → B(H)`, `π : A → B(K)` be
nmiu-maps such that each `ω ∈ Ω` is given by vectors `x_ω ∈ H` and
`y_ω ∈ K`.  Then there is a bounded `U : K → H` intertwining `π` and `ρ`
such that `U*U` is a projection in `π(A)^□` whose least
`Z(π(A)^□)`-majorant is `π(∑_ω ⌈⌈ω⌉⌉)`, and symmetrically for `UU*`. -/
theorem sigma_weak_lemma_2 (Ω : Set (NPFunctional A))
    (horth : ∀ ω ∈ Ω, ∀ ω' ∈ Ω, ω ≠ ω' →
      cceil (npCarrier ω) * cceil (npCarrier ω') = 0)
    (ρ : NMIUMap A (H →L[ℂ] H)) (π : NMIUMap A (K →L[ℂ] K))
    (x : Ω → H) (y : Ω → K)
    (hx : ∀ ω : Ω, ∀ a : A, (ω : NPFunctional A) a = ⟪x ω, ρ a (x ω)⟫)
    (hy : ∀ ω : Ω, ∀ a : A, (ω : NPFunctional A) a = ⟪y ω, π a (y ω)⟫) :
    ∃ U : K →L[ℂ] H,
      (∀ a : A, U ∘L π a = ρ a ∘L U) ∧
      IsStarProjection (ContinuousLinearMap.adjoint U ∘L U) ∧
      ContinuousLinearMap.adjoint U ∘L U ∈
        commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
      IsLeast {p : K →L[ℂ] K |
          p ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
          IsStarProjection p ∧
          (∀ b ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)), p * b = b * p) ∧
          ContinuousLinearMap.adjoint U ∘L U ≤ p}
        (π (projSup {c : A | ∃ ω ∈ Ω, c = cceil (npCarrier ω)})) :=
  sorry

/-- **89VII** (`sigma-weak-lemma`, vn.tex:7052, Corollary): let `A` be
(represented as) a von Neumann algebra of operators on `H` via an injective
nmiu-map `ρ` with von Neumann subalgebra range, and let
`π : A → B(K)` be a representation in which *every* np-functional of `A`
is a vector functional (a universal representation, cf. 48V).  Then there
is a bounded `U : K → H` such that `U*U` is a projection in `π(A)^□` whose
least `Z(π(A)^□)`-majorant is `1`, and `Uπ(a) = ρ(a)U` for all `a`. -/
theorem sigma_weak_lemma (ρ : NMIUMap A (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra (H →L[ℂ] H) ρ.toStarAlgHom.range)
    (π : NMIUMap A (K →L[ℂ] K))
    (huniv : ∀ ω : NPFunctional A, ∃ y : K, ∀ a : A, ω a = ⟪y, π a y⟫) :
    ∃ U : K →L[ℂ] H,
      (∀ a : A, U ∘L π a = ρ a ∘L U) ∧
      IsStarProjection (ContinuousLinearMap.adjoint U ∘L U) ∧
      ContinuousLinearMap.adjoint U ∘L U ∈
        commutant (K →L[ℂ] K) (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
      IsLeast {p : K →L[ℂ] K |
          p ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)) ∧
          IsStarProjection p ∧
          (∀ b ∈ commutant (K →L[ℂ] K)
            (Set.range fun a : A => (π a : K →L[ℂ] K)), p * b = b * p) ∧
          ContinuousLinearMap.adjoint U ∘L U ≤ p}
        1 :=
  sorry

/-- **89IX** (`normal-functional`, vn.tex:7089, Theorem): every
np-functional `ω` on a von Neumann subalgebra `A` of `B(H)` (given by an
injective nmiu-map `ρ : A → B(H)` with von Neumann subalgebra range) is of
the form `ω = ∑ₙ ⟨xₙ,(·)xₙ⟩` for some `x₁, x₂, … ∈ H` with
`∑ₙ ‖xₙ‖² < ∞`. -/
theorem normal_functional (ρ : NMIUMap A (H →L[ℂ] H))
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra (H →L[ℂ] H) ρ.toStarAlgHom.range)
    (ω : NPFunctional A) :
    ∃ x : ℕ → H, (Summable fun n => ‖x n‖ ^ 2) ∧
      ∀ a : A, HasSum (fun n => ⟪x n, ρ a (x n)⟫) (ω a) :=
  sorry

end BH

section Permanence

variable [VonNeumannAlgebra A] [VonNeumannAlgebra B]

/-- **89XI** (`functional-permanence`, vn.tex:7155, Corollary), part 1: for
a von Neumann subalgebra `A` of `B` (an injective nmiu-map `ρ : A → B`
with von Neumann subalgebra range), every np-functional `ω` on `A` extends
to an np-functional `ξ` on `B`: `ξ ∘ ρ = ω`. -/
theorem functional_permanence_1 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) (ω : NPFunctional A) :
    ∃ ξ : NPFunctional B, ∀ a : A, ξ (ρ a) = ω a :=
  sorry

/-- **89XI** (`functional-permanence`, vn.tex:7155, Corollary), part 2
(**ultraweak permanence**): the ultraweak topology of a von Neumann
subalgebra `A` of `B` is the restriction of the ultraweak topology of
`B`. -/
theorem functional_permanence_2 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) :
    ultraweak A = TopologicalSpace.induced ⇑ρ (ultraweak B) :=
  sorry

/-- **89XI** (`functional-permanence`, vn.tex:7155, Corollary), part 3
(**ultrastrong permanence**): likewise for the ultrastrong topologies. -/
theorem functional_permanence_3 (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ)
    (hR : IsVNSubalgebra B ρ.toStarAlgHom.range) :
    ultrastrong A = TopologicalSpace.induced ⇑ρ (ultrastrong B) :=
  sorry

/-- **89XII** (`functional-extension`, vn.tex:7175, Exercise): every
np-functional `ω` on `A` extends along any injective nmiu-map
`ρ : A → B`: there is an np-functional `ω'` on `B` with `ω' ∘ ρ = ω`.
(The thesis writes `ρ ∘ ω' = ω`, an obvious slip.) -/
theorem functional_extension (ρ : NMIUMap A B)
    (hρ : Function.Injective ⇑ρ) (ω : NPFunctional A) :
    ∃ ω' : NPFunctional B, ∀ a : A, ω' (ρ a) = ω a :=
  sorry

/-! ## Parsec 900: centre separating collections

**90I** (vn.tex:7191): introduction — nothing to formalize. -/

/-- **90II** (`vn-center-separating-fundamental`, vn.tex:7206,
Proposition), part 1: for a centre separating collection `Ω` of
np-functionals and an ultrastrongly dense subset `S` of a von Neumann
algebra, the collection `Ω' = {ω(s*(·)s) : ω ∈ Ω, s ∈ S}` is order
separating. -/
theorem vn_center_separating_fundamental_1 (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparating A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) (a b : A) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b)
    (h : ∀ ω ∈ Ω, ∀ s ∈ S, ω (star s * a * s) ≤ ω (star s * b * s)) :
    a ≤ b :=
  sorry

/-- **90II** (`vn-center-separating-fundamental`, vn.tex:7206,
Proposition), part 2: the finite sums `Ω''` of members of `Ω'` are
operator-norm dense in the positive part of the predual: every
np-functional `f` is an operator-norm limit of sums
`∑ₖ ωₖ(sₖ*(·)sₖ)` with `ωₖ ∈ Ω`, `sₖ ∈ S`. -/
theorem vn_center_separating_fundamental_2 (Ω : Set (NPFunctional A))
    (hΩ : CentreSeparating A Ω) (S : Set A)
    (hS : @Dense A (ultrastrong A) S) (f : NPFunctional A) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (n : ℕ) (ω : Fin n → NPFunctional A) (s : Fin n → A),
      (∀ k, ω k ∈ Ω ∧ s k ∈ S) ∧
      ∀ a : A, ‖f a - ∑ k, (ω k) (star (s k) * a * s k)‖ ≤ ε * ‖a‖ :=
  sorry

/-! **91I** (vn.tex:7311): closing remarks of the chapter — nothing to
formalize. -/

end Permanence

end Theses.A.VN
