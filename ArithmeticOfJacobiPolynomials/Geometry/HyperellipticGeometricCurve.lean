/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBaseChange
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGlobalSections
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric curve properties of the hyperelliptic model

For `f ∈ k[x]` and a field extension `K/k` (in the same universe):

* `isIso_globalStructureMorphism_baseChange`: the structure map `K → Γ(X_K, 𝒪)` of the base change
  `X_K = projectiveModel f ×_k K` is an isomorphism (transported along `baseChangeIso` from
  `isIso_globalStructureMorphism` for `f ⊗ K`); this holds for every `f`;
* `geometricallyConnected_toSpecField`: for `f` separable of degree `≥ 1`, `projectiveModel f` is
  geometrically connected over `k` (from geometric integrality).

Only field extensions are treated (no arbitrary base schemes, no cohomology and base change).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open Polynomial AlgebraicGeometry CategoryTheory Limits

universe u

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] (f : k[X])

/-- **Global sections after base change.** The structure map `K ≅ Γ(Spec K, ⊤) → Γ(X_K, ⊤)` of
`X_K = projectiveModel f ×_k K` is an isomorphism of commutative rings. -/
theorem isIso_globalStructureMorphism_baseChange :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd (toSpecField f) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) := by
  rw [← baseChangeIso_hom_toSpecField K f, Scheme.Hom.comp_appTop, ← Category.assoc]
  have := isIso_globalStructureMorphism (f.map (algebraMap k K))
  have : IsIso (baseChangeIso K f).hom.appTop :=
    (inferInstance : IsIso (Scheme.Γ.map (baseChangeIso K f).hom.op))
  infer_instance

/-- The structure map `K → Γ(X_K, ⊤)` is bijective. -/
theorem globalStructureMap_baseChange_bijective :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd (toSpecField f)
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop).hom := by
  have := isIso_globalStructureMorphism_baseChange K f
  exact ConcreteCategory.bijective_of_isIso _

variable {f}

/-- **The model is geometrically connected** for `f` separable of degree `≥ 1`. -/
theorem geometricallyConnected_toSpecField (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    GeometricallyConnected (toSpecField f) := by
  have h := geometricallyIntegral_toSpecField hf hdeg
  rw [geometricallyIntegral_iff] at h
  rw [geometricallyConnected_iff]
  intro L _ y Z fst snd hZ
  have := h y fst snd hZ
  infer_instance

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
