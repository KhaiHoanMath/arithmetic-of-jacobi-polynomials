/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Applications.JacobianTateLie
public import ArithmeticOfJacobiPolynomials.Applications.JacobianWeilPairing

/-!
# Zarhin's Lie algebra on the canonically polarized Jacobian

Corollary 6.6. The general cited Theorem 2.6
supplies the base-field computation. The finite-extension restriction and
diagonal action on powers are proved on the rational Tate module.
The duality datum is the geometric Weil pairing of the canonical Poincaré polarization.
Its general existence is a separate cited input.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open GroupScheme AbelianTateLie

set_option maxHeartbeats 1000000 in
-- Elaborating the canonical Jacobian and Tate-module transports exceeds the default budget.
/-- The Lie-algebra assertion of Corollary 6.6 and its finite-extension/power
steps, for the Jacobian and the geometric canonical Weil pairing. -/
theorem jacobianTateLie_of_symmetric
    (hZarhin : Zarhin.TateLieAlgebra.{0})
    {L : Type} [Field L] [Algebra ℚ L] [IsAlgClosure ℚ L] [CharZero L]
    {f : ℚ[X]} (hf : f.Separable) (hd : 9 ≤ f.natDegree)
    (hS : GaloisGroupIsSymmetric f)
    (B : BigFppfSite.{0}) (hC : B.Contains (Hyperelliptic.projectiveModel f))
    (hQ : B.Contains (Spec (.of ℚ))) (g : B.obj hC ⟶ B.obj hQ)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField f)
    [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel f) ≤ 1)
    (J : Grp (Over (Spec (.of ℚ)))) [IsCommMonObj J.X]
    (hJ : Jacobian.IsJacobianOf B hC hQ g hdim J)
    (D : Over (Spec (.of ℚ))) [GrpObj D] [IsCommMonObj D]
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D)
    [IsMonHom φ]
    (hCan : Jacobian.IsCanonicalPrincipalPolarization
      (Over.mk (Hyperelliptic.toSpecField f)) J D P φ)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : DualPairingData ℓ L J.X D)
    (hWeil : WeilPairingGeometry.IsWeilData L J.X D W P)
    (m : ℕ) (b : Module.Basis (Fin m) ℚ_[ℓ]
      (rationalTate ℓ (GeomPoints ℚ L J.X)))
    (E : IntermediateField ℚ L) [FiniteDimensional ℚ E] (r : ℕ) [NeZero r] :
    (tateGaloisUnits J.X b).range ≤
        similitudeUnits (transportForm b.equivFun (abelianWeilPairing W φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) =
        scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing W φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
        AbelianTateLie.diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r ''
          scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing W φ)) := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed ℚ
  let : IsIso φ := hCan.principal.isIso
  have hmodel := Zarhin.hyperellipticModel_projectiveModel (by norm_num : (2 : ℚ) ≠ 0)
    hf (by omega : 0 < f.natDegree)
  have hZ := hZarhin ℚ L f hf (by omega) (Zarhin.admissibleGalois_of_symmetric hS)
    (Over.mk (Hyperelliptic.toSpecField f)) hmodel B hC hQ g hg hdim J hJ
    D P φ hCan ℓ W hWeil m b
  have hℓ : (ℓ : L) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero
  exact hJ.arithmeticConclusions_lie_step b W φ hZ hℓ E r

set_option maxHeartbeats 1000000 in
-- The canonical geometry and rational Tate transports exceed the default elaboration budget.
/-- The canonical geometric Weil data can be selected from the general finite
Weil-family citation. Its alternating perfect pairing satisfies Corollary 6.6's
Lie-algebra assertions over every number field and on every nonzero power. -/
theorem exists_jacobianTateLie_of_symmetric
    (hExist : AbelianVariety.WeilPairingsExist.{0})
    (hAlt : AbelianVariety.PolarizedWeilAlternating.{0})
    (hZarhin : Zarhin.TateLieAlgebra.{0})
    {L : Type} [Field L] [Algebra ℚ L] [IsAlgClosure ℚ L] [CharZero L]
    {f : ℚ[X]} (hf : f.Separable) (hd : 9 ≤ f.natDegree)
    (hS : GaloisGroupIsSymmetric f)
    (B : BigFppfSite.{0}) (hC : B.Contains (Hyperelliptic.projectiveModel f))
    (hQ : B.Contains (Spec (.of ℚ))) (g : B.obj hC ⟶ B.obj hQ)
    (hg : B.inclusion.map g = Hyperelliptic.toSpecField f)
    [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim (Hyperelliptic.projectiveModel f) ≤ 1)
    (J : Grp (Over (Spec (.of ℚ)))) [IsCommMonObj J.X]
    (hJ : Jacobian.IsJacobianOf B hC hQ g hdim J)
    (D : Over (Spec (.of ℚ))) [GrpObj D] [IsCommMonObj D]
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D) [IsMonHom φ]
    (hCan : Jacobian.IsCanonicalPrincipalPolarization
      (Over.mk (Hyperelliptic.toSpecField f)) J D P φ)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (m : ℕ) (b : Module.Basis (Fin m) ℚ_[ℓ]
      (rationalTate ℓ (GeomPoints ℚ L J.X)))
    (E : IntermediateField ℚ L) [FiniteDimensional ℚ E] (r : ℕ) [NeZero r] :
    ∃ W : DualPairingData ℓ L J.X D,
      WeilPairingGeometry.IsWeilData L J.X D W P ∧
      LinearMap.IsAlt (abelianWeilPairing W φ) ∧
      Function.Bijective (abelianWeilPairing W φ) ∧
      (tateGaloisUnits J.X b).range ≤
        similitudeUnits (transportForm b.equivFun (abelianWeilPairing W φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) =
        scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing W φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
        AbelianTateLie.diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r ''
          scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing W φ)) := by
  let : IsAlgClosed L := IsAlgClosure.isAlgClosed ℚ
  let : IsAbelianVariety ℚ J.X := hJ.isAbelianVariety
  obtain ⟨W, hWeil, hWA, hWP⟩ := hCan.exists_weilPairing (L := L) hExist hAlt ℓ
    (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
  exact ⟨W, hWeil, hWA, hWP,
    jacobianTateLie_of_symmetric hZarhin hf hd hS B hC hQ g hg hdim J hJ
      D P φ hCan ℓ W hWeil m b E r⟩

end ArithmeticOfJacobiPolynomials
