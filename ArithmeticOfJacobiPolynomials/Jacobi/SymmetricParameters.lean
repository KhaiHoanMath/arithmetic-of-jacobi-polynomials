/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricAsymptotics
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# Theorem 1.4 (symmetric integral parameters)

`ArithmeticOfJacobiPolynomials.symmetricParametersStatement` proves `SymmetricParametersStatement`
(Theorem 1.4 of the manuscript, both assertions), conditional on the cited
`HansonLcmBound` ([Hanson, Theorem 1]), the proved `intervalVandermondeBound` (Lemma 2.5),
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]) and `DusartThetaBound`
([Dusart10, Theorem 5.2]).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset Real

/-- [Dusart10, Theorem 5.2] in the sum form `∑_{p ≤ x} log p`. -/
theorem dusartThetaBound_sum (hD : DusartThetaBound) (x : ℝ) (hx : 3594641 ≤ x) :
    |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2 := by
  have h := hD x hx
  rw [Chebyshev.theta_eq_sum_Icc] at h
  have e : (Icc 0 ⌊x⌋₊).filter Nat.Prime = (range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, by omega⟩, h2⟩
  rwa [e] at h

/-- **Theorem 1.4.** For integers `r ≥ 0`, `m ≥ 1`, `δ ∈ {0,1}`, `F_{m,r,δ}` is irreducible over
`ℚ` whenever `m ≥ max{100r, 1000}`; and there is `M₀` such that the same holds whenever
`m ≥ max{8r, M₀}`. -/
theorem symmetricParametersStatement (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hD : DusartThetaBound) : SymmetricParametersStatement :=
  ⟨fun _ _ _ hδ hm => irreducible_reducedGegenbauer_of_explicit_range hH hZ hδ hm,
    irreducible_reducedGegenbauer_of_eight_mul_le hZ (dusartThetaBound_sum hD)⟩

end ArithmeticOfJacobiPolynomials
