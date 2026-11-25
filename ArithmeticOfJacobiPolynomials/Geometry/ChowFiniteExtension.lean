/- Assembled by AxiomProver. -/
module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Chow classes over an algebraic Galois extension have finite Galois models

Corollary 6.6, §6.5, uses a finite Galois extension before averaging.
Stacks 0FVQ/0FH6 supplies a finite stage for each Chow class. Enlarging this
stage to its normal closure and pulling back its class gives a finite Galois
model, with the same class over the algebraic extension.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow IntermediateField

universe u

namespace ArithmeticOfJacobiPolynomials.ChowFiniteExtension

/-- A finite family of geometric Chow classes has one common finite Galois
model. This gives a common field for every finite linear combination of classes. -/
theorem exists_galoisStageChowPullback_eq_family
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGalois k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (i : ℤ)
    {ι : Type*} [Finite ι]
    (γ : ι → chowGroup (fieldChowSituation K)
      (pullback.snd X.hom (fieldExtensionBaseChangeSituation k K).g) i) :
    ∃ (E : FiniteSubextension k K) (_ : IsGalois k E.1)
      (δ : ι → chowGroup (fieldChowSituation E.1)
        (pullback.snd X.hom (fieldExtensionBaseChangeSituation k E.1).g) i),
      ∀ j, (algebraicExtensionSystem k K X).stageChowPullback (op E) i (δ j) = γ j := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let s := algebraicExtensionSystem k K X
  choose a β hβ using fun j => s.exists_stageChowPullback_eq i (γ j)
  obtain ⟨a₀, ha₀⟩ := IsCofiltered.inf_objs_exists (Finset.image a Finset.univ)
  let t (j : ι) : a₀ ⟶ a j :=
    (ha₀ (Finset.mem_image_of_mem a (Finset.mem_univ j))).some
  let E : FiniteSubextension k K := a₀.unop
  have : FiniteDimensional k E.1 := E.2
  let N : FiniteSubextension k K :=
    ⟨normalClosure k E.1 K, normalClosure.is_finiteDimensional k E.1 K⟩
  have hEN : E ≤ N := IntermediateField.le_normalClosure E.1
  let n : op N ⟶ a₀ := (homOfLE hEN).op
  refine ⟨N, IsGalois.normalClosure k E.1 K,
    fun j => s.transitionChowPullback (n ≫ t j) i (β j), fun j => ?_⟩
  exact (s.stageChowPullback_transitionChowPullback (n ≫ t j) i (β j)).trans (hβ j)

/-- Every Chow class over an algebraic Galois extension is the base change of
a Chow class over a finite Galois subextension. -/
theorem exists_galoisStageChowPullback_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGalois k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (i : ℤ)
    (γ : chowGroup (fieldChowSituation K)
      (pullback.snd X.hom (fieldExtensionBaseChangeSituation k K).g) i) :
    ∃ (E : FiniteSubextension k K) (_ : IsGalois k E.1)
      (δ : chowGroup (fieldChowSituation E.1)
        (pullback.snd X.hom (fieldExtensionBaseChangeSituation k E.1).g) i),
      (algebraicExtensionSystem k K X).stageChowPullback (op E) i δ = γ := by
  obtain ⟨E, hE, δ, hδ⟩ := exists_galoisStageChowPullback_eq_family k K X i
    (fun _ : Unit => γ)
  exact ⟨E, hE, δ (), hδ ()⟩

/-- Every finite linear combination of images of geometric Chow classes can
be represented using classes over one finite Galois stage. Applied to the
geometric cycle-class map, this supplies the finite field used in averaging. -/
theorem exists_galoisStage_mem_span_range
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGalois k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (i : ℤ)
    {R W : Type*} [Semiring R] [AddCommMonoid W] [Module R W]
    (cl : chowGroup (fieldChowSituation K)
      (pullback.snd X.hom (fieldExtensionBaseChangeSituation k K).g) i → W)
    {w : W} (hw : w ∈ Submodule.span R (Set.range cl)) :
    ∃ (E : FiniteSubextension k K) (_ : IsGalois k E.1),
      w ∈ Submodule.span R
        (Set.range (cl ∘ (algebraicExtensionSystem k K X).stageChowPullback (op E) i)) := by
  classical
  obtain ⟨T, hT, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw
  choose γ hγ using fun z : T => hT z.property
  obtain ⟨E, hE, δ, hδ⟩ := exists_galoisStageChowPullback_eq_family k K X i γ
  refine ⟨E, hE, Submodule.span_mono ?_ hwT⟩
  intro z hz
  let j : T := ⟨z, hz⟩
  refine ⟨δ j, ?_⟩
  change cl ((algebraicExtensionSystem k K X).stageChowPullback (op E) i (δ j)) = z
  rw [hδ j]
  exact hγ j

end ArithmeticOfJacobiPolynomials.ChowFiniteExtension
