/-
Papers/OAP/Main.lean

A. Westerbaan, B. Westerbaan, J. van de Wetering, *A characterisation of
ordered abstract probabilities* (LICS 2020, arXiv:1912.10040), source
`../papers/1912.10040/first.tex`, §9 *Main theorems*: points
**OAP 68**–**OAP 73**.

Conventions (see `Papers/README.md`, `Papers/OAP/PLAN.md`):

* `[0,1]_{C(X)}` is `Set.Icc (0 : C(X, ℝ)) 1` with Basic's
  `unitIntervalEffectMonoid` (OAP 7); a Boolean algebra `B` is an effect
  monoid by the tree's `booleanEffectMonoid B` (OAP 6); the direct sum
  `[0,1]_{C(X)} ⊕ B` is Basic's `prodEffectMonoid` of the two, named
  `cxbEM X B` here.
* "`M` embeds into `N`" is `Nonempty (EMEmbedding M N)`; "`M ≅ N`" is an
  effect monoid morphism `f` with `EMIsIso f` (OAP 8).
* "an ω-complete Boolean algebra" is a Boolean algebra in which every
  countable subset has a supremum; "a complete Boolean algebra" is Mathlib's
  `CompleteBooleanAlgebra`.
* The main theorems, as other papers consume them:
  `oap68` (ω-complete: embedding into `[0,1]_{C(X)} ⊕ B`), `oap69`
  (directed-complete: isomorphism), `oap69_corner` (the same in the corner
  form `pM ≅ [0,1]_{C(X)}`, `p^⊥M` Boolean, used by SEA 35), `oap70`
  (commutativity), `oap71` (no zero divisors: `{0}`, `{0,1}` or `[0,1]`, as
  printed) and `oap71_iso` (the same as isomorphisms to the tree's
  `PUnit`, `Bool`, `I`).
-/
import Papers.OAP.Embedding
import Papers.OAP.OUS

set_option warn.classDefReducibility false

namespace Papers.OAP

open Theses.B.Eff
open scoped Papers.OAP unitInterval

universe u v w

/-! ## Infrastructure: composing morphisms, products of morphisms -/

section Homs

variable {M : Type u} {N : Type v} {P : Type w} [EffectMonoid M] [EffectMonoid N]
  [EffectMonoid P]

/-- Composition of effect monoid morphisms. -/
def emComp (g : EffectMonoidHom N P) (f : EffectMonoidHom M N) :
    EffectMonoidHom M P where
  toFun a := g.toFun (f.toFun a)
  perp_map h := g.perp_map (f.perp_map h)
  ovee_map h := by rw [f.ovee_map h]; exact g.ovee_map _
  map_one := by rw [f.map_one, g.map_one]
  map_mul a b := by rw [f.map_mul, g.map_mul]

theorem emComp_apply (g : EffectMonoidHom N P) (f : EffectMonoidHom M N)
    (a : M) : (emComp g f).toFun a = g.toFun (f.toFun a) := rfl

/-- Effect monoid morphisms are monotone (thesis B 176V.2, across universes). -/
theorem emHom_monotone (f : EffectMonoidHom M N) {a b : M} (h : a ≤ b) :
    f.toFun a ≤ f.toFun b := by
  obtain ⟨c, hac, rfl⟩ := le_def.1 h
  exact le_def.2 ⟨f.toFun c, f.perp_map hac,
    by rw [oplus_eq (f.perp_map hac), oplus_eq hac, f.ovee_map hac]⟩

theorem EMIsIso.comp {g : EffectMonoidHom N P} {f : EffectMonoidHom M N} (hg : EMIsIso g)
    (hf : EMIsIso f) : EMIsIso (emComp g f) := by
  obtain ⟨g', hg1, hg2⟩ := hg
  obtain ⟨f', hf1, hf2⟩ := hf
  refine ⟨emComp f' g', fun a => ?_, fun c => ?_⟩
  · show f'.toFun (g'.toFun (g.toFun (f.toFun a))) = a
    rw [hg1, hf1]
  · show g.toFun (f.toFun (f'.toFun (g'.toFun c))) = c
    rw [hf2, hg2]

/-- An isomorphism is an embedding. -/
theorem EMIsIso.reflect {f : EffectMonoidHom M N} (hf : EMIsIso f) {a b : M}
    (h : f.toFun a ≤ f.toFun b) : a ≤ b := by
  obtain ⟨g, hg, -⟩ := hf
  have := emHom_monotone g h
  rwa [hg, hg] at this

/-- An embedding followed by an isomorphism is an embedding. -/
def EMEmbedding.compIso (e : EMEmbedding M N) (g : EffectMonoidHom N P) (hg : EMIsIso g) :
    EMEmbedding M P where
  toEffectMonoidHom := emComp g e.toEffectMonoidHom
  reflect h := e.reflect (hg.reflect h)

theorem EMEmbedding.compIso_apply (e : EMEmbedding M N) (g : EffectMonoidHom N P)
    (hg : EMIsIso g) (a : M) : (e.compIso g hg).toFun a = g.toFun (e.toFun a) := rfl

/-- An embedding is injective (OAP 1/8). -/
theorem EMEmbedding.injective (e : EMEmbedding M N) : Function.Injective e.toFun :=
  fun _ _ h => le_antisymm (e.reflect (le_of_eq h)) (e.reflect (le_of_eq h.symm))

end Homs

section ProdMap

variable {M₁ M₂ : Type u} {N₁ N₂ : Type v} [EffectMonoid M₁] [EffectMonoid M₂]
  [EffectMonoid N₁] [EffectMonoid N₂]

/-- The product `f₁ ⊕ f₂ : M₁ ⊕ M₂ → N₁ ⊕ N₂` of two effect monoid morphisms. -/
def emProdMap (f : EffectMonoidHom M₁ N₁) (g : EffectMonoidHom M₂ N₂) :
    EffectMonoidHom (M₁ × M₂) (N₁ × N₂) where
  toFun a := (f.toFun a.1, g.toFun a.2)
  perp_map h := ⟨f.perp_map h.1, g.perp_map h.2⟩
  ovee_map h := Prod.ext (f.ovee_map h.1) (g.ovee_map h.2)
  map_one := Prod.ext f.map_one g.map_one
  map_mul a b := Prod.ext (f.map_mul a.1 b.1) (g.map_mul a.2 b.2)

theorem EMIsIso.prodMap {f : EffectMonoidHom M₁ N₁} {g : EffectMonoidHom M₂ N₂}
    (hf : EMIsIso f) (hg : EMIsIso g) : EMIsIso (emProdMap f g) := by
  obtain ⟨f', hf1, hf2⟩ := hf
  obtain ⟨g', hg1, hg2⟩ := hg
  exact ⟨emProdMap f' g', fun a => Prod.ext (hf1 a.1) (hg1 a.2),
    fun b => Prod.ext (hf2 b.1) (hg2 b.2)⟩

end ProdMap

/-! ## The effect monoid `[0,1]_{C(X)} ⊕ B` -/

section CXB

/-- The effect monoid `[0,1]_{C(X)} ⊕ B` of the main theorems: the direct sum
(OAP 11) of `[0,1]_{C(X)}` (OAP 7) and the Boolean algebra `B` (OAP 6). -/
@[reducible] noncomputable def cxbEM (X : Type u) [TopologicalSpace X] (B : Type u)
    [BooleanAlgebra B] : EffectMonoid (Set.Icc (0 : C(X, ℝ)) 1 × B) :=
  @prodEffectMonoid _ _ (unitIntervalEffectMonoid C(X, ℝ)) (booleanEffectMonoid B)

/-- `[0,1]_{C(X)} ⊕ B` is commutative (OAP 7 and OAP 6). -/
theorem cxb_commutative (X : Type u) [TopologicalSpace X] (B : Type u) [BooleanAlgebra B] :
    @EffectMonoid.Commutative _ (cxbEM X B) := fun a b =>
  Prod.ext ((oap7_CX X).2 a.1 b.1) ((oap6_commutative B).1 a.2 b.2)

/-- A Boolean algebra in which every subset has a supremum is a complete
Boolean algebra, with the same Boolean algebra structure. -/
noncomputable def completeBooleanAlgebraOfIsLUB (B : Type u) [inst : BooleanAlgebra B]
    (h : ∀ A : Set B, ∃ s, IsLUB A s) : CompleteBooleanAlgebra B :=
  letI : SupSet B := ⟨fun A => Classical.choose (h A)⟩
  { inst, completeLatticeOfSup B (fun A => Classical.choose_spec (h A)) with }

theorem completeBooleanAlgebraOfIsLUB_toBooleanAlgebra (B : Type u) [inst : BooleanAlgebra B]
    (h : ∀ A : Set B, ∃ s, IsLUB A s) :
    (completeBooleanAlgebraOfIsLUB B h).toBooleanAlgebra = inst := rfl

end CXB

/-! ## OAP 68, 69: the representation theorems -/

section Main

attribute [local instance] unitIntervalEffectMonoid

variable {M : Type u} [EffectMonoid M]

/-- **OAP 68** (`thm:omega-complete-classification`, first.tex:2567, Theorem):
an ω-complete effect monoid `M` embeds into `[0,1]_{C(X)} ⊕ B` for a
basically disconnected compact Hausdorff space `X` and an ω-complete Boolean
algebra `B` (every countable subset of `B` has a supremum).

Proof as printed: OAP 54 embeds `M` into `M₁ ⊕ M₂` with `M₁` convex and
ω-complete and `M₂` an ω-complete Boolean algebra (`M₂ ≅ B := P(M₂)`,
OAP 45–47); OAP 66 gives `M₁ ≅ [0,1]_{C(X)}` (its lattice hypothesis is
OAP 37, `isLUB_emSup`; "convex" is turned into an `EffectModule I M₁` by
OAP 49, `oap49_iff`); compose with the product of the two isomorphisms. -/
theorem oap68 [OmegaComplete M] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
      (B : Type u) (_ : BooleanAlgebra B),
      BasicallyDisconnected X ∧ (∀ A : Set B, A.Countable → ∃ s, IsLUB A s) ∧
      Nonempty (@EMEmbedding M (Set.Icc (0 : C(X, ℝ)) 1 × B) _ (cxbEM X B)) := by
  obtain ⟨M₁, M₂, i1, i2, hω1, -, hconv, ⟨hB, hiso, hsup⟩, ⟨e⟩⟩ := oap54 (M := M)
  obtain ⟨mod⟩ := oap49_iff.1 hconv
  let _ := mod
  obtain ⟨X, tX, cX, hX, f, hf, -, hbd, -⟩ :=
    oap66 (M := M₁) (fun a b => ⟨emSup a b, isLUB_emSup a b⟩)
  let _ := booleanEffectMonoid (idempotents M₂)
  refine ⟨X, tX, cX, hX, idempotents M₂, idemBooleanAlgebra M₂, hbd, hsup, ⟨?_⟩⟩
  exact @EMEmbedding.compIso M (M₁ × M₂) _ _ _ (cxbEM X _) e
    (emProdMap f (booleanIso hB)) (EMIsIso.prodMap hf hiso)

/-- **OAP 69** (`mainthmdirectedcomplete`, first.tex:2582, Theorem): a
directed-complete effect monoid `M` is isomorphic to `[0,1]_{C(X)} ⊕ B` for
an extremally disconnected compact Hausdorff space `X` and a complete Boolean
algebra `B`.

Proof as printed ("same as previous theorem but using" OAP 57): OAP 57 gives
`M ≅ M₁ ⊕ M₂` with `M₁` convex directed-complete and `M₂ ≅ P(M₂)` a
Boolean algebra in which every subset has a supremum (made a Mathlib
`CompleteBooleanAlgebra`, `completeBooleanAlgebraOfIsLUB`); OAP 66 gives
`M₁ ≅ [0,1]_{C(X)}` with `X` extremally disconnected. -/
theorem oap69 [DirectedComplete M] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
      (B : Type u) (_ : CompleteBooleanAlgebra B),
      ExtremallyDisconnected X ∧
      ∃ f : @EffectMonoidHom M (Set.Icc (0 : C(X, ℝ)) 1 × B) _ (cxbEM X B),
        @EMIsIso M _ _ (cxbEM X B) f := by
  obtain ⟨M₁, M₂, i1, i2, hd1, hconv, -, ⟨hB, hiso, hsup⟩, f, hf⟩ := oap57 (M := M)
  obtain ⟨mod⟩ := oap49_iff.1 hconv
  let _ := mod
  obtain ⟨X, tX, cX, hX, g, hg, -, -, hED⟩ :=
    oap66 (M := M₁) (fun a b => ⟨emSup a b, isLUB_emSup a b⟩)
  let _ := booleanEffectMonoid (idempotents M₂)
  refine ⟨X, tX, cX, hX, idempotents M₂,
    completeBooleanAlgebraOfIsLUB (idempotents M₂) hsup, hED hd1, ?_⟩
  exact ⟨emComp (emProdMap g (booleanIso hB)) f, EMIsIso.comp (EMIsIso.prodMap hg hiso) hf⟩

/-- **OAP 69** (`mainthmdirectedcomplete`, first.tex:2582, Theorem), in the
corner form of its proof (OAP 57 with OAP 66): in a directed-complete effect
monoid `M` there is an idempotent `p` with `pM` convex and every element
below `p^⊥` idempotent (so `p^⊥M` is a complete Boolean algebra, OAP 57), and
`pM ≅ [0,1]_{C(X)}` for an extremally disconnected compact Hausdorff `X`.
This is the form SEA 35 cites. -/
theorem oap69_corner [DirectedComplete M] :
    ∃ (p : M) (hp : p * p = p),
      @IsConvex (leftCorner p) (cornerEffectMonoid p hp).toEffectAlgebra ∧
      (∀ a : M, a ≤ orth p → a * a = a) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
        ExtremallyDisconnected X ∧
        ∃ f : @EffectMonoidHom (leftCorner p) (Set.Icc (0 : C(X, ℝ)) 1)
            (cornerEffectMonoid p hp) _,
          @EMIsIso (leftCorner p) _ (cornerEffectMonoid p hp) _ f := by
  obtain ⟨a, ⟨haa, -⟩, hp, hB⟩ := oap56 (M := M)
  let _i1 := cornerEffectMonoid (a ⋎ a) hp
  have hd1 : DirectedComplete (leftCorner (a ⋎ a)) := corner_directedComplete hp
  have hconv : IsConvex (leftCorner (a ⋎ a)) := oap50 (corner_halvable hp ⟨a, haa, rfl⟩)
  obtain ⟨mod⟩ := oap49_iff.1 hconv
  let _ := mod
  obtain ⟨X, tX, cX, hX, g, hg, -, -, hED⟩ :=
    oap66 (M := leftCorner (a ⋎ a)) (fun a b => ⟨emSup a b, isLUB_emSup a b⟩)
  exact ⟨a ⋎ a, hp, hconv, hB, X, tX, cX, hX, hED hd1, g, hg⟩

/-! ## OAP 70: commutativity -/

/-- **OAP 70** (first.tex:2592, Corollary): an ω-complete effect monoid is
commutative.

Proof as printed: `M` embeds into `[0,1]_{C(X)} ⊕ B` (OAP 68), whose
multiplication is commutative — pointwise in `C(X)` (OAP 7) and the meet in
`B` (OAP 6; the print says "join", a slip, see ERRATA); an embedding is
injective. -/
theorem oap70 [OmegaComplete M] : EffectMonoid.Commutative M := by
  obtain ⟨X, _, _, _, B, _, -, -, ⟨e⟩⟩ := oap68 (M := M)
  let _ := cxbEM X B
  intro a b
  apply @EMEmbedding.injective M _ _ (cxbEM X B) e
  have h1 := e.map_mul a b
  have h2 := e.map_mul b a
  rw [h1, h2]
  exact cxb_commutative X B _ _

/-! ## OAP 71: no zero divisors -/

section OAP71

variable {X : Type u} [TopologicalSpace X]

/-- Evaluation at a point, `[0,1]_{C(X)} → [0,1]`. -/
noncomputable def evalHom (x₀ : X) : EffectMonoidHom (Set.Icc (0 : C(X, ℝ)) 1) I where
  toFun w := ⟨(w : C(X, ℝ)) x₀, by simpa using ContinuousMap.le_def.1 w.2.1 x₀,
    by simpa using ContinuousMap.le_def.1 w.2.2 x₀⟩
  perp_map {v w} h := by
    have h' : (v : C(X, ℝ)) + w ≤ 1 := h
    show (v : C(X, ℝ)) x₀ + (w : C(X, ℝ)) x₀ ≤ 1
    simpa using ContinuousMap.le_def.1 h' x₀
  ovee_map _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

/-- Constant functions, `[0,1] → [0,1]_{C(X)}`. -/
noncomputable def constHom : EffectMonoidHom I (Set.Icc (0 : C(X, ℝ)) 1) where
  toFun r := ⟨ContinuousMap.const X (r : ℝ), ContinuousMap.le_def.2 fun _ => r.2.1,
    ContinuousMap.le_def.2 fun _ => r.2.2⟩
  perp_map {r s} h := by
    have h' : (r : ℝ) + s ≤ 1 := h
    show ContinuousMap.const X (r : ℝ) + ContinuousMap.const X (s : ℝ) ≤ 1
    exact ContinuousMap.le_def.2 fun _ => h'
  ovee_map _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

/-- For a one-point space, `[0,1]_{C(X)} ≅ [0,1]`. -/
theorem evalHom_isIso [Subsingleton X] (x₀ : X) : EMIsIso (evalHom (X := X) x₀) := by
  refine ⟨constHom, fun w => Subtype.ext (ContinuousMap.ext fun z => ?_), fun r => rfl⟩
  show (w : C(X, ℝ)) x₀ = (w : C(X, ℝ)) z
  rw [Subsingleton.elim z x₀]

end OAP71

/-- In an effect monoid without non-trivial zero divisors the only
idempotents are `0` and `1` (first step of the proof of OAP 71). -/
theorem idem_eq_zero_or_one (hM : ∀ a b : M, a * b = 0 → a = 0 ∨ b = 0) {p : M}
    (hp : p * p = p) : p = 0 ∨ p = 1 := by
  rcases hM p (orth p) ((oap18 p).1 hp) with h | h
  · exact Or.inl h
  · right; rw [← orth_orth p, h]; exact eabasics_orth_zero

/-- **OAP 71** (`thm:no-zero-divisors`, first.tex:2599, Theorem): an
ω-complete effect monoid `M` with no non-trivial zero divisors
(`a·b = 0 ⇒ a = 0 ∨ b = 0`) is `{0}`, or `{0,1}`, or isomorphic to `[0,1]`
(the tree's effect monoid `I`, thesis B 178III.1).

Proof as printed: idempotents are `0` or `1` (`p·p^⊥ = 0`, OAP 18); for
`s ≠ 0, 1`, `s·s^⊥ ≠ 0`, `2(s·s^⊥)` exists (OAP 25) and is halvable, so is
its ceiling (OAP 51), which is an idempotent `≠ 0`, hence `1`; so `M` is
halvable, hence convex (OAP 50), and `M ≅ [0,1]_{C(X)}` with `X` basically
disconnected (OAP 66).  Two points `x ≠ y` of `X`: Urysohn gives `f` with
`f(x) = 0`, `f(y) = 1`; the closure `C` of the support of `g = (f - 1/3)⁺`
is clopen (`X` basically disconnected), so its indicator is an idempotent
of `[0,1]_{C(X)}`, hence `0` or `1`; `y ∈ C`, so `C = X`, but `x` has the
neighbourhood `{f < 1/3}` on which `g = 0`.  (The print takes `g` from a
second application of Urysohn's lemma to the closures of `{f < 1/3}` and
`{f > 2/3}`; `(f - 1/3)⁺` does the same job.)  So `X` is a single point
(non-empty as `M ≠ {0}`) and `[0,1]_{C(X)} ≅ [0,1]` (`evalHom_isIso`). -/
theorem oap71 [OmegaComplete M] (hM : ∀ a b : M, a * b = 0 → a = 0 ∨ b = 0) :
    (∀ a : M, a = 0) ∨ ((0 : M) ≠ 1 ∧ ∀ a : M, a = 0 ∨ a = 1) ∨
      ∃ f : EffectMonoidHom M I, EMIsIso f := by
  by_cases hs : ∃ s : M, s ≠ 0 ∧ s ≠ 1
  swap
  · push Not at hs
    by_cases h01 : (0 : M) = 1
    · left
      intro a
      by_cases ha : a = 0
      · exact ha
      · exact (hs a ha).trans h01.symm
    · right; left
      refine ⟨h01, fun a => ?_⟩
      by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr (hs a ha)
  right; right
  obtain ⟨s, hs0, hs1⟩ := hs
  -- `s·s^⊥ ≠ 0`
  have ht : s * orth s ≠ 0 := by
    intro h
    rcases hM s (orth s) h with h' | h'
    · exact hs0 h'
    · exact hs1 (by rw [← orth_orth s, h']; exact eabasics_orth_zero)
  have hperp := oap25 s
  have hc := oap51 (M := M) ⟨s * orth s, hperp, rfl⟩
  -- the ceiling of `2(s·s^⊥)` is `1`
  have hc1 : ceil (s * orth s ⋎ s * orth s) = 1 := by
    rcases idem_eq_zero_or_one hM (ceil_idem (s * orth s ⋎ s * orth s)) with h | h
    · exact absurd (eq_zero_of_le_zero
        (h ▸ ((le_oplus_left hperp).trans (le_ceil _)))) ht
    · exact h
  have hH : HalvableEA M := by
    show IsHalvable (1 : M)
    rw [← hc1]; exact hc
  obtain ⟨mod⟩ := oap49_iff.1 (oap50 hH)
  let _ := mod
  obtain ⟨X, tX, cX, hX, f, hf, -, hbd, -⟩ :=
    oap66 (M := M) (fun a b => ⟨emSup a b, isLUB_emSup a b⟩)
  obtain ⟨f', hf1, hf2⟩ := hf
  -- `X` has at most one point
  have hsub : ∀ x y : X, x = y := by
    intro x y
    by_contra hxy
    obtain ⟨u, hux, huy, -⟩ := exists_continuous_zero_one_of_isClosed isClosed_singleton
      isClosed_singleton (Set.disjoint_singleton.2 hxy)
    have hux' : u x = 0 := hux rfl
    have huy' : u y = 1 := huy rfl
    let g : C(X, ℝ) := ⟨fun z => max (u z - 1 / 3) 0, by fun_prop⟩
    have hg : ∀ z, g z = max (u z - 1 / 3) 0 := fun _ => rfl
    let C : Set X := closure {z | g z ≠ 0}
    have hC : IsClopen C := ⟨isClosed_closure, hbd g⟩
    have hyC : y ∈ C := subset_closure (by
      show g y ≠ 0
      rw [hg, huy']; norm_num)
    have hxC : x ∉ C := by
      intro hx
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hx {z | u z < 1 / 3}
        (isOpen_lt u.continuous continuous_const) (by simp [hux'])
      apply hz2
      show g z = 0
      rw [hg]
      exact max_eq_right (by linarith [show u z < 1 / 3 from hz1])
    let χ : C(X, ℝ) := ⟨C.indicator 1,
      Continuous.indicator (by simp [hC.frontier_eq]) continuous_const⟩
    have hχ : ∀ z, χ z = C.indicator 1 z := fun _ => rfl
    have hχm : χ ∈ Set.Icc (0 : C(X, ℝ)) 1 := by
      refine ⟨ContinuousMap.le_def.2 fun z => ?_, ContinuousMap.le_def.2 fun z => ?_⟩ <;>
      · by_cases hz : z ∈ C <;> simp [hχ, hz]
    let el : Set.Icc (0 : C(X, ℝ)) 1 := ⟨χ, hχm⟩
    have hel : el * el = el := by
      refine Subtype.ext (ContinuousMap.ext fun z => ?_)
      show χ z * χ z = χ z
      by_cases hz : z ∈ C <;> simp [hχ, hz]
    have hm : f'.toFun el * f'.toFun el = f'.toFun el := by
      exact (f'.map_mul el el).symm.trans (congrArg f'.toFun hel)
    have hval : ∀ z, (el : C(X, ℝ)) z = C.indicator 1 z := fun _ => rfl
    rcases idem_eq_zero_or_one hM hm with h | h
    · have h0 : el = 0 := by
        rw [← hf2 el, h]; exact exc_eamorphism_map_zero f.toEAHom
      have := hval y
      rw [h0, Set.indicator_of_mem hyC] at this
      exact one_ne_zero this.symm
    · have h1 : el = 1 := by rw [← hf2 el, h]; exact f.map_one
      have := hval x
      rw [h1, Set.indicator_of_notMem hxC] at this
      exact one_ne_zero this
  -- `X` is non-empty, since `M ≠ {0}`
  have hne : Nonempty X := by
    by_contra hX0
    rw [not_nonempty_iff] at hX0
    have hall : ∀ w w' : Set.Icc (0 : C(X, ℝ)) 1, w = w' := fun w w' =>
      Subtype.ext (ContinuousMap.ext fun z => isEmptyElim z)
    apply hs0
    rw [← hf1 s, hall (f.toFun s) (f.toFun 0), hf1]
  obtain ⟨x₀⟩ := hne
  have : Subsingleton X := ⟨hsub⟩
  exact ⟨emComp (evalHom x₀) f, EMIsIso.comp (evalHom_isIso x₀) ⟨f', hf1, hf2⟩⟩

/-! ### OAP 71 as isomorphisms `M ≅ 1`, `M ≅ 2`, `M ≅ [0,1]` -/

/-- The unique morphism into the one-element effect monoid. -/
def toPUnitHom : EffectMonoidHom M PUnit.{v + 1} where
  toFun _ := PUnit.unit
  perp_map _ := trivial
  ovee_map _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

/-- If `M = {0}`, the constant map `1 → M` is a morphism. -/
def fromPUnitHom (h : ∀ a : M, a = 0) : EffectMonoidHom PUnit.{v + 1} M where
  toFun _ := 0
  perp_map _ := zero_perp 0
  ovee_map _ := (h _).symm
  map_one := (h 1).symm
  map_mul _ _ := (h _).symm

open Classical in
/-- `a ↦ [a = 1] : M → 2`. -/
noncomputable def boolOf (a : M) : Bool := decide (a = 1)

theorem boolOf_one : boolOf (1 : M) = true := by simp [boolOf]

theorem boolOf_zero (h01 : (0 : M) ≠ 1) : boolOf (0 : M) = false := by simp [boolOf, h01]

/-- If `M = {0,1}` with `0 ≠ 1`, `a ↦ [a = 1]` is a morphism `M → 2`. -/
noncomputable def toBoolHom (h01 : (0 : M) ≠ 1) (h : ∀ a : M, a = 0 ∨ a = 1) :
    EffectMonoidHom M Bool where
  toFun := boolOf
  perp_map {a b} hab := by
    show (boolOf a && boolOf b) = false
    rcases h a with rfl | rfl
    · rw [boolOf_zero h01, Bool.false_and]
    · rcases h b with rfl | rfl
      · rw [boolOf_zero h01, Bool.and_false]
      · exact absurd (EffectAlgebra.eq_zero_of_perp_one hab).symm h01
  ovee_map {a b} hab := by
    rw [← oplus_eq hab]
    show boolOf (a ⋎ b) = (boolOf a || boolOf b)
    rcases h a with rfl | rfl
    · rw [zero_oplus, boolOf_zero h01, Bool.false_or]
    · rcases h b with rfl | rfl
      · rw [oplus_zero, boolOf_zero h01, Bool.or_false]
      · exact absurd (EffectAlgebra.eq_zero_of_perp_one hab).symm h01
  map_one := boolOf_one
  map_mul a b := by
    show boolOf (a * b) = (boolOf a && boolOf b)
    rcases h a with rfl | rfl
    · rw [ezero_mul, boolOf_zero h01, Bool.false_and]
    · rw [eone_mul, boolOf_one, Bool.true_and]

/-- `2 → M`, `b ↦ b ? 1 : 0`. -/
def fromBoolHom : EffectMonoidHom Bool M where
  toFun b := cond b 1 0
  perp_map {b c} hbc := by
    cases b <;> cases c
    · exact zero_perp 0
    · exact zero_perp 1
    · exact perp_zero 1
    · exact absurd (show (true ⊓ true : Bool) = ⊥ from hbc) (by decide)
  ovee_map {b c} hbc := by
    rw [← oplus_eq]
    cases b <;> cases c
    · exact (zero_oplus 0).symm
    · exact (zero_oplus 1).symm
    · exact (oplus_zero 1).symm
    · exact absurd (show (true ⊓ true : Bool) = ⊥ from hbc) (by decide)
  map_one := rfl
  map_mul b c := by
    cases b <;> cases c
    · exact (ezero_mul 0).symm
    · exact (ezero_mul 1).symm
    · exact (emul_zero 1).symm
    · exact (eone_mul 1).symm

/-- **OAP 71** (`thm:no-zero-divisors`, first.tex:2599, Theorem), stated with
isomorphisms: an ω-complete effect monoid without non-trivial zero divisors
is isomorphic to the one-element effect monoid, to `2 = {0,1}` or to
`[0,1]` (the tree's `PUnit`, `Bool` and `I`).  This is the form of SIG 43
(`NoZeroDivisorsTheorem`). -/
theorem oap71_iso [OmegaComplete M] (hM : ∀ a b : M, a * b = 0 → a = 0 ∨ b = 0) :
    (∃ f : EffectMonoidHom M PUnit.{v + 1}, EMIsIso f) ∨
      (∃ f : EffectMonoidHom M Bool, EMIsIso f) ∨ ∃ f : EffectMonoidHom M I, EMIsIso f := by
  rcases oap71 hM with h | ⟨h01, h⟩ | h
  · exact Or.inl ⟨toPUnitHom, fromPUnitHom h, fun a => (h a).symm, fun _ => rfl⟩
  · refine Or.inr (Or.inl ⟨toBoolHom h01 h, fromBoolHom, fun a => ?_, fun b => ?_⟩)
    · show cond (boolOf a) 1 0 = a
      rcases h a with rfl | rfl
      · rw [boolOf_zero h01]; rfl
      · rw [boolOf_one]; rfl
    · show boolOf (cond b 1 0 : M) = b
      cases b
      · exact boolOf_zero h01
      · exact boolOf_one
  · exact Or.inr (Or.inr h)

end Main

/-! ## OAP 72, 73

**OAP 72** (first.tex:2645, Remark): by Cho's thesis (cited) the scalars of a
normalised ω-effectus have no zero divisors, so OAP 71 classifies them; the
cited part is SIG's business (SIG 43–44), not formalised here.

**OAP 73** (first.tex:2654, Remark): outlook on σ-Dedekind-complete ordered
rings (via OAP 7) and a possible characterisation of `ℝ` among ordered
domains; no mathematical claim, not formalised. -/

end Papers.OAP
