/- Assembled by AxiomProver. -/
module

public import Mathlib

/-!
# Restriction to a splitting field preserves inertia

Two generic facts used to carry inertia membership between splitting fields (the local-to-global
step of Lemma 5.1 and Lemma 5.16, and the affine transport of Proposition 5.2):

* contraction along a ring homomorphism preserves lying over an ideal of `ℤ`
  (`liesOver_comap_int`);
* restriction `Gal(E/ℚ) → Gal(g/ℚ)` to the splitting field of `g` inside `E` maps the inertia group
  of a prime `P` of `𝓞 E` into the inertia group of its contraction
  (`restrict_mem_inertia_comap`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField

/-- Contraction along a ring homomorphism preserves lying over an ideal of `ℤ` (Mathlib's
`Ideal.comap_liesOver` for the `ℤ`-algebra homomorphism `φ.toIntAlgHom`). -/
theorem liesOver_comap_int {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (P : Ideal B) (q : Ideal ℤ) [P.LiesOver q] : (P.comap φ).LiesOver q :=
  inferInstanceAs ((P.comap φ.toIntAlgHom).LiesOver q)

/-- Restriction to the splitting field of `g` maps the inertia group of a prime `P` of `𝓞 E` into
the inertia group of the contraction of `P`. -/
theorem restrict_mem_inertia_comap {g : ℚ[X]} {E : Type*} [Field E] [Algebra ℚ E]
    [Fact ((g.map (algebraMap ℚ E)).Splits)] {P : Ideal (𝓞 E)} {σ : Gal(E/ℚ)}
    (hσ : σ ∈ P.inertia Gal(E/ℚ)) :
    (Gal.restrict g E σ : Gal(g.SplittingField/ℚ)) ∈
      (P.comap (RingOfIntegers.mapRingHom (algebraMap g.SplittingField E))).inertia
        Gal(g.SplittingField/ℚ) := by
  rw [Ideal.mem_inertia] at hσ
  suffices H : ∀ τ : Gal(g.SplittingField/ℚ), τ = Gal.restrict g E σ →
      τ ∈ (P.comap (RingOfIntegers.mapRingHom (algebraMap g.SplittingField E))).inertia
        Gal(g.SplittingField/ℚ) from H _ rfl
  intro τ hτ
  refine Ideal.mem_inertia.mpr fun x => ?_
  rw [Ideal.mem_comap, map_sub]
  have e : RingOfIntegers.mapRingHom (algebraMap g.SplittingField E) (τ • x) =
      σ • RingOfIntegers.mapRingHom (algebraMap g.SplittingField E) x := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingHom_apply]
    subst hτ
    exact AlgEquiv.restrictNormal_commutes σ g.SplittingField (x : g.SplittingField)
  rw [e]
  exact hσ _

end ArithmeticOfJacobiPolynomials
