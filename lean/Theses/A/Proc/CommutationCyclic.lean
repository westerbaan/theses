/-
Thesis A, chapter "Assorted Structure in W*_cpsu" (proc.tex): **the reduction
of the commutation theorem to the cyclic-and-separating case**.

This is the file the whole amplify-and-cut development exists to produce.

* `A/Proc/CommutationReduction.lean` reduces `CT 𝒜 ℬ : (𝒜 ⊗̄ ℬ)^□ = 𝒜^□ ⊗̄ ℬ^□`
  for arbitrary pairs of von Neumann subalgebras to pairs with a **finite
  jointly cyclic family**.
* `A/Proc/CommutationAmplify.lean` carries that to pairs with a single
  **cyclic** vector (`CT_of_CT_cyclic`), and proves — two ways — that no
  further cutting or amplifying can reach the cyclic-*and*-separating case
  on its own.
* `A/Proc/Compression.lean` supplies the missing orientation of the transport:
  `CT_of_CT_compression_of_dense` moves `CT` across a cut **inside** the
  algebra, using `(f𝒯f)^□ = 𝒯^□f`.

What is left, and what this file is, is the *glue*: for `𝒜` with a cyclic
vector `ξ` the cut is `e := [𝒜^□ξ]`, and everything the transport asks for
falls out of the two facts `e ∈ 𝒜` and `e ξ = ξ`.

## The glue, in full

`Commutation.lean`'s `exists_separating_corner` already builds `e` and proves
the one nontrivial thing about it — that `ξ` is separating for `e𝒜e`.  Given
that:

* **The density hypothesis.**  `CT_of_CT_compression_of_dense` wants
  `[𝒜 e ℋ] = ℋ`, the central carrier condition.  Since `e ξ = ξ`, the set
  `𝒜 e ℋ` contains `𝒜 ξ`, which is dense because `ξ` is cyclic.  One line of
  `Submodule.span_mono`.
* **The corner has a cyclic vector.**  `sub^* ξ` works, and again only
  because `e ξ = ξ`: the orbit of `sub^* ξ` under `e𝒜e` is
  `sub^* (𝒜 ξ)`, and `sub^*` is a continuous *retraction* (`sub^* sub = 1`),
  so it carries a dense set to a dense set — `v = sub^* (sub v)` and
  `image_closure_subset_closure_image`.  No open mapping theorem.
* **The corner has a separating vector, the same one.**  A member of
  `cornerAlgVN` is `cmpr sub x = sub^* x sub` for `x ∈ 𝒜`
  (`coe_cornerAlgVN`), and `(cmpr sub x) (sub^* ξ) = sub^* (x ξ)` while
  `(e x e) ξ = sub (sub^* (x ξ))`; so the two vanish together, and
  `e x e = 0` gives `cmpr sub x = 0` by injectivity of `cext`.

So the *cyclic* and the *separating* halves both reduce to `e ξ = ξ`, and the
only real content — separation — is already in `exists_separating_corner`.

**One correction to the brief.**  It said the separating half "uses
`vnComm_cornerAlgVN` from `Compression.lean`".  It does not: separation is a
statement about the compressed algebra itself, not about its commutant, and
`compressedSet e 𝒜 = cmpr sub '' 𝒜` transported along `cext` is all that is
needed.  `vnComm_cornerAlgVN` is consumed *inside* `CT_of_CT_compression`,
where it belongs, and never appears here.
-/
import Theses.A.Proc.Compression
import Theses.A.Proc.CommutationAmplify

open scoped ComplexOrder ComplexInnerProductSpace CStarAlgebra
  TensorProduct ENNReal
open Filter Topology Theses Theses.A.VN

noncomputable section

namespace Theses.A.Proc

universe u

section CyclicSeparating

variable {H E : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `HasCyclicSeparating S` : the set `S` of operators has a vector that is
both **cyclic** and **separating**.  This is the input Tomita's theorem wants
(`A/VN/Tomita.lean`), and the class the reduction below lands in. -/
def HasCyclicSeparating (S : Set (H →L[ℂ] H)) : Prop :=
  ∃ ξ : H,
    Dense ((Submodule.span ℂ {y : H | ∃ x ∈ S, y = x ξ} : Submodule ℂ H) : Set H) ∧
    SeparatingFor S ξ

/-! ## The corner at `e = [𝒜^□ξ]` has a cyclic and separating vector

Everything here is driven by the single equation `e ξ = ξ`. -/

/-- **The compression of `𝒜` by a projection `e ∈ 𝒜` fixing `ξ` has
`sub^* ξ` as a cyclic vector**, as soon as `ξ` is cyclic for `𝒜`, and as a
**separating** vector as soon as `ξ` is separating for `e 𝒜 e`. -/
theorem hasCyclicSeparating_cornerAlgVN
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsVNSubalgebra (H →L[ℂ] H) SA)
    {sub : E →L[ℂ] H} {e : H →L[ℂ] H} (hs : IsCorner sub e) (heA : e ∈ SA)
    {ξ : H} (heξ : e ξ = ξ)
    (hcyc : Dense
      ((Submodule.span ℂ {y : H | ∃ x ∈ SA, y = x ξ} : Submodule ℂ H) : Set H))
    (hsep : SeparatingFor (compressedSet e (SA : Set (H →L[ℂ] H))) ξ) :
    HasCyclicSeparating ((cornerAlgVN hs SA heA : StarSubalgebra ℂ (E →L[ℂ] E)) :
      Set (E →L[ℂ] E)) := by
  classical
  set A : H →L[ℂ] E := ContinuousLinearMap.adjoint sub with hAdef
  -- the compression of `x` sends `sub^* ξ` to `sub^* (x ξ)`
  have hval : ∀ x : H →L[ℂ] H, cmpr sub x (A ξ) = A (x ξ) := by
    intro x
    show A (x (sub (A ξ))) = A (x ξ)
    rw [hAdef, hs.sub_adjoint_apply, heξ]
  have hmem : ∀ x ∈ SA, cmpr sub x ∈
      ((cornerAlgVN hs SA heA : StarSubalgebra ℂ (E →L[ℂ] E)) : Set (E →L[ℂ] E)) := by
    rw [coe_cornerAlgVN hA]
    exact fun x hx => ⟨x, hx, rfl⟩
  refine ⟨A ξ, ?_, ?_⟩
  · -- **cyclic**: `sub^*` is a continuous retraction, so it carries the dense
    -- orbit `𝒜 ξ` to a dense set.
    set G : Set H := {y : H | ∃ x ∈ SA, y = x ξ} with hG
    set T : Set E := {y : E | ∃ x ∈ ((cornerAlgVN hs SA heA :
      StarSubalgebra ℂ (E →L[ℂ] E)) : Set (E →L[ℂ] E)), y = x (A ξ)} with hT
    have hGT : (A : H → E) '' G ⊆ T := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨cmpr sub x, hmem x hx, (hval x).symm⟩
    have hsub : ∀ h ∈ Submodule.span ℂ G, A h ∈ Submodule.span ℂ T := by
      intro h hh
      induction hh using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hGT ⟨y, hy, rfl⟩)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
    intro v
    have hv : A (sub v) = v := hs.apply_adjoint_apply v
    have h1 : sub v ∈ closure ((Submodule.span ℂ G : Submodule ℂ H) : Set H) := hcyc _
    have h3 := image_closure_subset_closure_image (f := (A : H → E)) A.continuous
      ⟨sub v, h1, rfl⟩
    rw [hv] at h3
    refine closure_mono ?_ h3
    rintro _ ⟨y, hy, rfl⟩
    exact hsub y hy
  · -- **separating**: `e x e = 0` and `sub^* (x ξ) = 0` are the same equation.
    intro y hy hy0
    rw [coe_cornerAlgVN hA] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 : A (x ξ) = 0 := by rw [← hval x]; exact hy0
    have h2 : (e * x * e) ξ = 0 := by
      have hh : (e * x * e) ξ = sub (A (x ξ)) := by
        show e (x (e ξ)) = sub (A (x ξ))
        rw [heξ, hAdef, hs.sub_adjoint_apply]
      rw [hh, h1, map_zero]
    have h3 : e * x * e = 0 := hsep _ ⟨x, hx, rfl⟩ h2
    have h4 : cext sub (cmpr sub x) = cext sub 0 := by
      rw [cext_cmpr hs, cext_zero]; exact h3
    exact cext_injective hs h4

end CyclicSeparating

/-! ## The capstone

`CT_of_CT_cyclic` reduces to the cyclic case; the cut `e = [𝒜^□ξ]` reduces
the cyclic case to the cyclic-and-separating case. -/

section Capstone

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The cut.**  A von Neumann algebra with a cyclic vector admits a
projection `e ∈ 𝒜` with central carrier `1` (in the density form
`[𝒜 e ℋ] = ℋ` that `A/Proc/Compression.lean` consumes) whose compression
`e 𝒜 e ⊆ B(eℋ)` has a vector that is **cyclic and separating**.

The projection is `e = [𝒜^□ ξ]` — `exists_separating_corner`, which is where
the only real content, separation, lives. -/
theorem exists_corner_cyclicSeparating
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsVNSubalgebra (H →L[ℂ] H) SA)
    (hcy : HasCyclic (SA : Set (H →L[ℂ] H))) :
    ∃ (e : H →L[ℂ] H) (he : IsStarProjection e) (heA : e ∈ SA),
      Dense ((Submodule.span ℂ {v : H | ∃ a ∈ SA, ∃ ζ : H, v = a (e ζ)} :
        Submodule ℂ H) : Set H) ∧
      HasCyclicSeparating
        ((cornerAlgVN (cornerRep e he).isCorner SA heA :
            StarSubalgebra ℂ (Cnr e he →L[ℂ] Cnr e he)) :
          Set (Cnr e he →L[ℂ] Cnr e he)) := by
  obtain ⟨ξ, hξ⟩ := hcy
  obtain ⟨e, hep, heA, heξ, hsep, -⟩ := exists_separating_corner SA hA ξ
  refine ⟨e, hep, heA, ?_, ?_⟩
  · -- `𝒜 e ℋ ⊇ 𝒜 ξ`, because `e ξ = ξ`
    refine hξ.mono (Submodule.span_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, ξ, by rw [heξ]⟩
  · exact hasCyclicSeparating_cornerAlgVN hA (cornerRep e hep).isCorner heA heξ hξ hsep

/-- The hypothesis "`CT` holds whenever both algebras have a vector that is
both cyclic and separating", as a `Prop` in one universe.  This is exactly
the input Tomita's theorem plus the tensor factorisation produce. -/
def CyclicSeparatingCTStatement : Prop :=
  ∀ {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (X : StarSubalgebra ℂ (E →L[ℂ] E)) (Y : StarSubalgebra ℂ (F →L[ℂ] F)),
    IsVNSubalgebra (E →L[ℂ] E) X → IsVNSubalgebra (F →L[ℂ] F) Y →
    HasCyclicSeparating (X : Set (E →L[ℂ] E)) →
    HasCyclicSeparating (Y : Set (F →L[ℂ] F)) → CT X Y

/-- **Cyclic-and-separating reduces the cyclic case.**  One cut inside each
algebra, transported by `CT_of_CT_compression_of_dense`. -/
theorem cyclicCTStatement_of_cyclicSeparating
    (hyp : CyclicSeparatingCTStatement.{u}) : CyclicCTStatement.{u} := by
  intro E F _ _ _ _ _ _ X Y hX hY hXc hYc
  obtain ⟨e, hep, heX, hdX, hcsX⟩ := exists_corner_cyclicSeparating hX hXc
  obtain ⟨f, hfp, hfY, hdY, hcsY⟩ := exists_corner_cyclicSeparating hY hYc
  exact CT_of_CT_compression_of_dense hX hY (cornerRep e hep).isCorner
    (cornerRep f hfp).isCorner heX hfY hdX hdY
    (hyp _ _ (isVNSubalgebra_cornerAlgVN _ _ _) (isVNSubalgebra_cornerAlgVN _ _ _)
      hcsX hcsY)

/-- **The reduction of the commutation theorem to the cyclic-and-separating
case.**  If `CT X Y` holds for every pair of von Neumann algebras each of
which has a vector that is both **cyclic and separating**, then
`CT 𝒜 ℬ : (𝒜 ⊗̄ ℬ)^□ = 𝒜^□ ⊗̄ ℬ^□` holds for **every** pair of von Neumann
subalgebras `𝒜 ⊆ B(ℋ)`, `ℬ ⊆ B(𝒦)`.

This is the theorem the whole amplify-and-cut development exists to produce:
`CommutationReduction.lean` (cutting) → `CommutationAmplify.lean` (`ℂⁿ`
amplification, `CT_of_CT_cyclic`) → `Compression.lean` (`(f𝒯f)^□ = 𝒯^□f`,
`CT_of_CT_compression_of_dense`) → the cut `e = [𝒜^□ξ]` of this file. -/
theorem CT_of_CT_cyclicSeparating (hyp : CyclicSeparatingCTStatement.{u})
    {SA : StarSubalgebra ℂ (H →L[ℂ] H)} {SB : StarSubalgebra ℂ (K →L[ℂ] K)}
    (hA : IsVNSubalgebra (H →L[ℂ] H) SA) (hB : IsVNSubalgebra (K →L[ℂ] K) SB) :
    CT SA SB :=
  CT_of_CT_cyclic (cyclicCTStatement_of_cyclicSeparating hyp) hA hB

end Capstone

end Theses.A.Proc
