/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.AbelianTateLie
public import ArithmeticOfJacobiPolynomials.Algebra.TateCyclotomic

/-!
# Corollary 6.6, the Tate/Lie restriction step, for a Jacobian

The proof of Corollary 6.6 says, "Theorem 2.6 [of Zarhin] gives the scalar
plus symplectic `ℓ`-adic Lie algebra. Passing to a number field preserves the Lie algebra because
the Galois subgroup has finite index. For powers, the groups act diagonally on direct sums."

Everything is stated for the rational Tate module `V_ℓ(J(L)) = rationalTate ℓ (GeomPoints k
L J.X)` of a Jacobian `J` (`IsJacobianOf`, which includes that `J.X` is an abelian variety), through
the matrix representation `AbelianTateLie.tateGaloisUnits` of `Aut(L/k)` in a finite basis. The
transfer theorems take the conclusion of Zarhin's Theorem 2.6 as a hypothesis on the Lie algebra
over the base field `k`.

* `Jacobian.IsJacobianOf.continuous_tateGaloisUnits`: the representation is continuous;
* `Jacobian.IsJacobianOf.ellAdicLie_fixingSubgroup_map_tateGaloisUnits`: restriction to a finite
  extension `E/k` in `L` does not change the Lie algebra;
* `Jacobian.IsJacobianOf.ellAdicLie_fixingSubgroup_eq_scalarPlusSymplectic`: the transfer of
  `ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)` from `k` to `E`, for the transported Weil pairing `ψ_b`;
* `AbelianTateLie.tateGaloisUnits_range_le_similitudeUnits`: the image lies in `GSp(V_b, ψ_b)`
  (used in `arithmeticConclusions_lie_step`);
* `Jacobian.IsJacobianOf.ellAdicLie_fixingSubgroup_map_powTateUnits_eq`: on the
  `V_ℓ(J^r(L))`, the image of `Gal(L/E)` (the *same* `σ` on each factor) has Lie algebra the
  diagonal copy of the one on a single factor;
* `Jacobian.IsJacobianOf.arithmeticConclusions_lie_step`: the three together;
* `Jacobian.IsJacobianOf.rat_arithmeticConclusions_lie_step`: the manuscript's case `k = ℚ`, `L =
  ℚ̄`,
  `E` a number field.

The canonical polarization and its Weil pairing are described in `JacobianPolarization` and
`JacobianWeilPairing`. `JacobianArithmetic` assembles the Tate and Hodge statements on powers
and the cycle-class conclusions.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry PadicInt Stacks.AbelianGroup
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

open GroupScheme AbelianTateLie

section General

variable {k : Type u} [Field k] {B : BigFppfSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}
  {hk : B.Contains (Spec (.of k))} {f : B.obj hX ⟶ B.obj hk} [IsProper (B.inclusion.map f)]
  {hdim : topologicalKrullDim X ≤ 1} {J : Grp (Over (Spec (.of k)))} [IsCommMonObj J.X]
  (hJ : IsJacobianOf B hX hk f hdim J) {L : Type u} [Field L] [Algebra k L] [IsAlgClosed L]
  {ℓ : ℕ} [Fact ℓ.Prime]

include hJ

/-- **A finite basis of `V_ℓ(J(L))`**, of size `2 * dim J_L`. -/
noncomputable def IsJacobianOf.tateBasis (hℓ : (ℓ : L) ≠ 0) :
    Module.Basis (Fin (2 * geomDim L J.X)) ℚ_[ℓ] (rationalTate ℓ (GeomPoints k L J.X)) :=
  haveI := hJ.isAbelianVariety
  AbelianTateLie.tateBasis J.X hℓ

variable {m : ℕ} (b : Module.Basis (Fin m) ℚ_[ℓ] (rationalTate ℓ (GeomPoints k L J.X)))

/-- **Continuity of the `ℓ`-adic Galois representation of a Jacobian** on the `V_ℓ(J(L))`
(`L/k` algebraic): the matrix representation `Aut(L/k) → GL_m(ℚ_ℓ)` is continuous. -/
theorem IsJacobianOf.continuous_tateGaloisUnits [Algebra.IsAlgebraic k L] (hℓ : (ℓ : L) ≠ 0) :
    Continuous (tateGaloisUnits J.X b) :=
  haveI := hJ.isAbelianVariety
  AbelianTateLie.continuous_tateGaloisUnits b hℓ

section FiniteExtension

variable [IsGalois k L]

/-- **Passing to a finite extension preserves the Lie algebra.** For every finite extension `E/k`
inside `L`, the image of `Gal(L/E)` in `GL_m(ℚ_ℓ)` (acting on the `V_ℓ(J(L))`) has the same
`ℓ`-adic Lie algebra as the image of `Gal(L/k)`. -/
theorem IsJacobianOf.ellAdicLie_fixingSubgroup_map_tateGaloisUnits (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField k L) [FiniteDimensional k E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) =
      ellAdicLie ℓ (tateGaloisUnits J.X b).range :=
  haveI := hJ.isAbelianVariety
  AbelianTateLie.ellAdicLie_fixingSubgroup_map_tateGaloisUnits b hℓ E

/-- **Transfer of a Lie algebra computation to a finite extension.** If `Lie(ρ_b(Gal(L/k))) = S`
(say the conclusion of Zarhin's Theorem 2.6 for `k`), then `Lie(ρ_b(Gal(L/E))) = S`. -/
theorem IsJacobianOf.ellAdicLie_fixingSubgroup_eq_of_range_eq
    {S : Set ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))}
    (hS : ellAdicLie ℓ (tateGaloisUnits J.X b).range = S) (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField k L) [FiniteDimensional k E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) = S :=
  haveI := hJ.isAbelianVariety
  AbelianTateLie.ellAdicLie_fixingSubgroup_eq_of_range_eq b hS hℓ E

/-- **Corollary 6.6, the Lie algebra over `E`.** Let `ψ` be a bilinear form on `V_ℓ(J(L))` (the
Weil pairing induced by the principal polarization). If `Lie(ρ_b(Gal(L/k))) = ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)`
(Zarhin 2.6 for `k`, an argument), then `Lie(ρ_b(Gal(L/E))) = ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)` for every finite
extension `E/k` in `L`. -/
theorem IsJacobianOf.ellAdicLie_fixingSubgroup_eq_scalarPlusSymplectic {P : Type*} [AddCommGroup P]
    [Module ℚ_[ℓ] P]
    (ψ : rationalTate ℓ (GeomPoints k L J.X) →ₗ[ℚ_[ℓ]] rationalTate ℓ (GeomPoints k L J.X) →ₗ[ℚ_[ℓ]]
      P)
    (hZ : ellAdicLie ℓ (tateGaloisUnits J.X b).range =
      scalarPlusSymplectic ℓ (transportForm b.equivFun ψ))
    (hℓ : (ℓ : L) ≠ 0) (E : IntermediateField k L) [FiniteDimensional k E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) =
      scalarPlusSymplectic ℓ (transportForm b.equivFun ψ) :=
  hJ.ellAdicLie_fixingSubgroup_eq_of_range_eq b hZ hℓ E

/-- **Powers over finite extensions.** For `r ≥ 1`, on the `V_ℓ(J^r(L))` the image of
`Gal(L/E)` acts diagonally (the same `σ` on each factor), and its Lie algebra is the diagonal copy
of `S`, where `S` is the Lie algebra of `ρ_b(Gal(L/k))` on a single factor. -/
theorem IsJacobianOf.ellAdicLie_fixingSubgroup_map_powTateUnits_eq {r : ℕ} [NeZero r]
    {S : Set ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))}
    (hS : ellAdicLie ℓ (tateGaloisUnits J.X b).range = S) (hℓ : (ℓ : L) ≠ 0)
    (E : IntermediateField k L) [FiniteDimensional k E] :
    ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
      diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r '' S :=
  haveI := hJ.isAbelianVariety
  AbelianTateLie.ellAdicLie_fixingSubgroup_map_powTateUnits_eq b hS hℓ E

end FiniteExtension

section Weil

variable {Â : Over (Spec (.of k))} [GrpObj Â] [IsCommMonObj Â]
  (D : DualPairingData ℓ L J.X Â) (φ : J.X ⟶ Â) [IsMonHom φ]

variable [IsGalois k L]

/-- **The Lie step of Corollary 6.6 (§6.5), assembled.** Let `ψ = abelianWeilPairing D φ`
be the Weil pairing of a polarization of the Jacobian `J` and assume the conclusion of Zarhin's
Theorem 2.6 for the base field `k`: `Lie(ρ_b(Gal(L/k))) = ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)`. Then, for every
finite extension `E/k` in `L` and every `r ≥ 1`:

1. `ρ_b(Gal(L/k)) ≤ GSp(V_b, ψ_b)` (so the two forms of the Lie algebra agree);
2. `Lie(ρ_b(Gal(L/E))) = ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)` (passing to a number field);
3. on the `V_ℓ(J^r(L))`, `Lie(ρ(Gal(L/E)))` is the diagonal image of `ℚ_ℓ Id ⊕ 𝔰𝔭(ψ_b)`. -/
theorem IsJacobianOf.arithmeticConclusions_lie_step
    (hZ : ellAdicLie ℓ (tateGaloisUnits J.X b).range =
      scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing D φ)))
    (hℓ : (ℓ : L) ≠ 0) (E : IntermediateField k L) [FiniteDimensional k E] (r : ℕ) [NeZero r] :
    (tateGaloisUnits J.X b).range ≤
        similitudeUnits (transportForm b.equivFun (abelianWeilPairing D φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) =
        scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing D φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
        diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r ''
          scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing D φ)) :=
  ⟨AbelianTateLie.tateGaloisUnits_range_le_similitudeUnits b D φ hℓ,
    hJ.ellAdicLie_fixingSubgroup_eq_scalarPlusSymplectic b _ hZ hℓ E,
    hJ.ellAdicLie_fixingSubgroup_map_powTateUnits_eq b hZ hℓ E⟩

end Weil

end General

section Rat

/-- **The case of the manuscript: `k = ℚ`, `L = ℚ̄`, `E` a number field.** For a Jacobian over
`ℚ`, a prime `ℓ`, and a finite extension `E/ℚ` inside `ℚ̄`, if `Lie(ρ_b(Gal(ℚ̄/ℚ)))` is
`S` (Zarhin 2.6 over `ℚ`, an argument), then `Lie(ρ_b(Gal(ℚ̄/E))) = S`, and on every power the
Lie algebra is the diagonal copy of `S`. -/
theorem IsJacobianOf.rat_arithmeticConclusions_lie_step
    {B : BigFppfSite.{0}} {X : Scheme.{0}} {hX : B.Contains X}
    {hk : B.Contains (Spec (.of ℚ))} {f : B.obj hX ⟶ B.obj hk} [IsProper (B.inclusion.map f)]
    {hdim : topologicalKrullDim X ≤ 1} {J : Grp (Over (Spec (.of ℚ)))} [IsCommMonObj J.X]
    (hJ : IsJacobianOf B hX hk f hdim J) {ℓ : ℕ} [Fact ℓ.Prime] {m : ℕ}
    (b : Module.Basis (Fin m) ℚ_[ℓ] (rationalTate ℓ (GeomPoints ℚ (AlgebraicClosure ℚ) J.X)))
    {S : Set ((Fin m → ℚ_[ℓ]) →L[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]))}
    (hS : ellAdicLie ℓ (tateGaloisUnits J.X b).range = S)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (r : ℕ) [NeZero r] :
    ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits J.X b)) = S ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
        diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r '' S :=
  have hℓ : (ℓ : AlgebraicClosure ℚ) ≠ 0 := natCast_ne_zero_algebraicClosure_rat ℓ
  ⟨hJ.ellAdicLie_fixingSubgroup_eq_of_range_eq b hS hℓ E,
    hJ.ellAdicLie_fixingSubgroup_map_powTateUnits_eq b hS hℓ E⟩

end Rat

end Jacobian

end ArithmeticOfJacobiPolynomials
