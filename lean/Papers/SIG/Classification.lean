/-
Papers/SIG/Classification.lean

SIG §5 "Classification of σ-effectuses with normalization", its opening part
(main.tex:1134–1225), points SIG 41–45: the two results cited from the
companion paper OAP (the embedding theorem for ω-complete effect monoids and
the classification of those without zero divisors), commutativity of the
scalars, the trichotomy `{0}`, `{0,1}`, `[0,1]` for σ-effectuses with
normalization, and triviality in the `{0}` case.

OAP is formalised in parallel (`Papers/OAP/`) and cannot be imported this
session: its two theorems enter as explicit hypotheses, the `Prop`s
`EffectMonoidEmbeddingTheorem` (SIG 41) and `NoZeroDivisorsTheorem` (SIG 43).
-/
import Papers.SIG.Normalisation

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits Theses.B.Eff

namespace Papers.SIG

universe u v

/-! ## The statements cited from OAP -/

/-- An ω-complete Boolean algebra: every increasing sequence has a join. -/
def BooleanOmegaComplete (B : Type u) [BooleanAlgebra B] : Prop :=
  ∀ a : ℕ → B, Monotone a → ∃ s, IsLUB (Set.range a) s

/-- An **embedding** of effect monoids (OAP, first.tex:511): an
effect-monoid morphism that reflects the order. -/
def IsEMEmbedding {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) : Prop :=
  ∀ a b : M, f.toFun a ≼ f.toFun b → a ≼ b

theorem IsEMEmbedding.injective {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    {f : EffectMonoidHom M N} (hf : IsEMEmbedding f) : Function.Injective f.toFun :=
  fun a b h => eabasics_le_antisymm (hf a b (h ▸ pcm_preorder_refl _))
    (hf b a (h ▸ pcm_preorder_refl _))

/-- The effect monoid `[0,1]_{C(X)} ⊕ B` (componentwise operations; the
tree's `continuousUnitIntervalEffectMonoid`, `booleanEffectMonoid` and
`prodEffectMonoid`). -/
noncomputable def cxbEffectMonoid (X : Type u) [TopologicalSpace X] (B : Type u)
    [BooleanAlgebra B] : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1 × B) :=
  @prodEffectMonoid _ _ (continuousUnitIntervalEffectMonoid X) (booleanEffectMonoid B)

/-- **SIG 41** (`thm:effect-monoid-char`, main.tex:1159, Theorem, cited as
[OAP, Theorem 54]): every ω-complete effect monoid `M` embeds into
`M₁ ⊕ M₂` with `M₁` an ω-complete Boolean algebra and `M₂ = [0,1]_{C(X)}`
for a basically disconnected compact Hausdorff space `X`.  Not proved here:
this `Prop` is the statement, taken as a hypothesis where it is used (waits
on OAP; in the OAP source this form is OAP 68,
`thm:omega-complete-classification`, and OAP 54 is its convex/Boolean
precursor). -/
def EffectMonoidEmbeddingTheorem : Prop :=
  ∀ (M : Type u) [EffectMonoid M], OmegaComplete M →
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
      (B : Type u) (_ : BooleanAlgebra B),
      BasicallyDisconnected X ∧ BooleanOmegaComplete B ∧
        ∃ f : @EffectMonoidHom M _ _ (cxbEffectMonoid X B),
          @IsEMEmbedding M _ _ (cxbEffectMonoid X B) f

/-- Effect monoids `M` and `N` are **isomorphic**: there are mutually inverse
effect-monoid morphisms (as the tree's `IsRealEffectus`, 190II.3). -/
def EMIso (M : Type u) (N : Type v) [EffectMonoid M] [EffectMonoid N] : Prop :=
  ∃ (φ : EffectMonoidHom M N) (ψ : EffectMonoidHom N M),
    (∀ a, ψ.toFun (φ.toFun a) = a) ∧ ∀ b, φ.toFun (ψ.toFun b) = b

/-- An effect monoid has **no nontrivial zero divisors**. -/
def EMNoZeroDivisors (M : Type u) [EffectMonoid M] : Prop :=
  ∀ s t : M, s * t = 0 → s = 0 ∨ t = 0

/-- **SIG 43** (`thm:no-zero-divisors`, main.tex:1186, Theorem, cited as
[OAP, Theorem 71]): an ω-complete effect monoid without nontrivial zero
divisors is `{0}`, `{0,1}` or `[0,1]`.  This `Prop` is the statement, taken
as a hypothesis where it is used; it is proved in `Papers.SIG.Discharge`
(`noZeroDivisorsTheorem`, from OAP 71). -/
def NoZeroDivisorsTheorem : Prop :=
  ∀ (M : Type u) [EffectMonoid M], OmegaComplete M → EMNoZeroDivisors M →
    EMIso M PUnit.{1} ∨ EMIso M Bool ∨ EMIso M unitInterval

/-! ## SIG 42: commutativity of the scalars -/

/-- The direct sum `[0,1]_{C(X)} ⊕ B` is commutative. -/
theorem commutative_cX_prod_bool (X : Type u) [TopologicalSpace X] (B : Type u)
    [BooleanAlgebra B] :
    @EffectMonoid.Commutative (Set.Icc (0 : C(X, ℝ)) 1 × B) (cxbEffectMonoid X B) := by
  intro a b
  refine Prod.ext (Subtype.ext ?_) (inf_comm a.2 b.2)
  exact mul_comm (a.1 : C(X, ℝ)) b.1

/-- A monoid embedding into a commutative effect monoid forces
commutativity. -/
theorem commutative_of_embedding {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (hN : EffectMonoid.Commutative N) {f : EffectMonoidHom M N} (hf : IsEMEmbedding f) :
    EffectMonoid.Commutative M := fun a b =>
  hf.injective (by rw [f.map_mul, f.map_mul, hN])

/-- **SIG 42** (main.tex:1172, Corollary): the scalars of a σ-effectus are
commutative (from SIG 41, taken as the hypothesis `h41`, and SIG 19). -/
theorem scalars_commutative {C : Type u} [Category.{v} C] [HasCountableCoproducts C]
    [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
    (h41 : EffectMonoidEmbeddingTheorem.{v}) : EffectMonoid.Commutative (Scal C) := by
  obtain ⟨X, _, _, _, B, _, -, -, f, hf⟩ :=
    h41 (Scal C) (pred_sigmaEffectAlgebra (effObj C)).1
  exact @commutative_of_embedding _ _ _ (cxbEffectMonoid X B) (commutative_cX_prod_bool X B) f hf

/-! ## SIG 44: the trichotomy -/

theorem emNoZeroDivisors_punit : EMNoZeroDivisors PUnit.{1} :=
  fun _ _ _ => Or.inl rfl

theorem emNoZeroDivisors_bool : EMNoZeroDivisors Bool := by
  intro s t h
  cases s <;> cases t
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h (by decide)

theorem emNoZeroDivisors_unitInterval : EMNoZeroDivisors unitInterval := by
  intro s t h
  have h' : (s : ℝ) * t = 0 := congrArg Subtype.val h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem emHom_map_zero {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (f : EffectMonoidHom M N) : f.toFun 0 = 0 := by
  have h : Perp (f.toFun 0) (f.toFun 1) := f.perp_map (PCM.zero_perp 1)
  rw [f.map_one] at h
  exact EffectAlgebra.eq_zero_of_perp_one h

theorem EMIso.noZeroDivisors {M : Type u} {N : Type v} [EffectMonoid M] [EffectMonoid N]
    (h : EMIso M N) (hN : EMNoZeroDivisors N) : EMNoZeroDivisors M := by
  obtain ⟨φ, ψ, hψφ, -⟩ := h
  intro s t hst
  have h0 : φ.toFun s * φ.toFun t = 0 := by
    rw [← φ.map_mul, hst]; exact emHom_map_zero φ
  have hz : ψ.toFun 0 = 0 := emHom_map_zero ψ
  rcases hN _ _ h0 with h1 | h1
  · left; rw [← hψφ s, h1, hz]
  · right; rw [← hψφ t, h1, hz]

/-- **SIG 44** (main.tex:1196, Theorem): a σ-effectus admits normalization
iff its effect monoid of scalars is isomorphic to `{0}`, `{0,1}` or `[0,1]`
(from SIG 43, taken as the hypothesis `h43`, SIG 40 and SIG 19). -/
theorem admitsNormalisation_iff_scalars {C : Type u} [Category.{v} C]
    [HasCountableCoproducts C] [∀ X Y : C, SigmaPAM (X ⟶ Y)] [SigmaEffectus C]
    (h43 : NoZeroDivisorsTheorem.{v}) :
    AdmitsNormalisation C ↔
      EMIso (Scal C) PUnit.{1} ∨ EMIso (Scal C) Bool ∨ EMIso (Scal C) unitInterval := by
  have tfae := normalisation_tfae (C := C)
  have h13 : AdmitsNormalisation C ↔ ScalarsNoZeroDivisors C := tfae.out 0 2
  rw [h13]
  constructor
  · intro hZ
    exact h43 (Scal C) (pred_sigmaEffectAlgebra (effObj C)).1 hZ
  · rintro (h | h | h)
    · exact h.noZeroDivisors emNoZeroDivisors_punit
    · exact h.noZeroDivisors emNoZeroDivisors_bool
    · exact h.noZeroDivisors emNoZeroDivisors_unitInterval

/-! ## SIG 45: the trivial case -/

/-- **SIG 45** (main.tex:1210, Proposition): an effectus whose scalars are
isomorphic to `{0}` is equivalent to the trivial category.  (Proof as
printed: `id = 0 : I → I`, so every truth map is `0`, so every map is `0`.) -/
theorem trivial_of_scalars_trivial {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [∀ X Y : C, PCM (X ⟶ Y)] [FinPAC C] [EffectusPartialForm C]
    (h : EMIso (Scal C) PUnit.{1}) : Nonempty (C ≌ Discrete PUnit.{1}) := by
  obtain ⟨φ, ψ, hψφ, -⟩ := h
  -- `id = 0 : I → I`
  have h10 : (1 : Scal C) = 0 :=
    calc (1 : Scal C) = ψ.toFun (φ.toFun 1) := (hψφ 1).symm
      _ = ψ.toFun (φ.toFun 0) := rfl
      _ = 0 := hψφ 0
  have hid : 𝟙 (effObj C) = 0 := by
    rw [← truth_effObj_eq_id]; exact h10
  -- every map is `0`
  have hzero : ∀ {A B : C} (f : A ⟶ B), f = 0 := by
    intro A B f
    refine EffectusPartialForm.eq_zero_of_one_zero ?_
    have : truth B = 0 := by
      rw [← Category.comp_id (truth B), hid, FinPAC.comp_zero]
    show f ≫ truth B = 0
    rw [this, FinPAC.comp_zero]
  have hsub : ∀ {A B : C} (f g : A ⟶ B), f = g := fun f g => (hzero f).trans (hzero g).symm
  have hfull : (Functor.star C).Full := ⟨fun {X Y} _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hfaith : (Functor.star C).Faithful := ⟨fun {X Y} f g _ => hsub f g⟩
  have hess : (Functor.star C).EssSurj :=
    ⟨fun d => ⟨effObj C, ⟨Discrete.eqToIso (Subsingleton.elim _ _)⟩⟩⟩
  have : (Functor.star C).IsEquivalence := { }
  exact ⟨(Functor.star C).asEquivalence⟩

end Papers.SIG
