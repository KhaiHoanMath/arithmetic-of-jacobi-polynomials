/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Algebra.AbelianWeilPairing

/-!
# Existence and properties of the canonical Jacobian Weil pairing

The general finite Weil-family and polarized-alternation literature inputs
supply the geometric pairing. Compatibility, Tate passage, finite alternation
and perfectness use the proved APIs on the Stacks Tate module.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials.Jacobian

open GroupScheme WeilPairingGeometry

/-- The canonical principal polarization supplies a geometric alternating,
perfect rational Weil pairing on the rational Tate module. -/
theorem IsCanonicalPrincipalPolarization.exists_weilPairing
    (hExist : AbelianVariety.WeilPairingsExist.{u})
    (hAlt : AbelianVariety.PolarizedWeilAlternating.{u})
    {k L : Type u} [Field k] [Field L] [Algebra k L] [IsAlgClosed L]
    {C : Over (Spec (.of k))}
    {J : Grp (Over (Spec (.of k)))} [IsCommMonObj J.X] [IsAbelianVariety k J.X]
    {D : Over (Spec (.of k))} [GrpObj D] [IsCommMonObj D]
    {P : Stacks.Picard.ofScheme (J.X ⊗ D).left} {φ : J.X ⟶ D} [IsMonHom φ]
    (hCan : IsCanonicalPrincipalPolarization C J D P φ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    ∃ W : DualPairingData ℓ L J.X D,
      IsWeilData L J.X D W P ∧ LinearMap.IsAlt (abelianWeilPairing W φ) ∧
        Function.Bijective (abelianWeilPairing W φ) := by
  let : IsIso φ := hCan.principal.isIso
  obtain ⟨e, he⟩ := hExist k J.X D P hCan.poincare.some L
  let W := he.dualPairingData ℓ hℓ
  have hW : IsWeilData L J.X D W P := he.isWeilData ℓ hℓ
  have hℓL : (ℓ : L) ≠ 0 := by
    intro hzero
    apply hℓ
    apply (algebraMap k L).injective
    simpa only [map_natCast, map_zero] using hzero
  have hA : ∀ x, abelianTatePairing W φ x x = 0 :=
    hAlt k J.X D P hCan.poincare.some φ hCan.principal.isPolarization L ℓ hℓL W hW
  exact ⟨W, hW, isAlt_abelianWeilPairing W φ (W.alt_polarized φ hℓL hA),
    abelianWeilPairing_bijective W φ hℓL⟩

end ArithmeticOfJacobiPolynomials.Jacobian
