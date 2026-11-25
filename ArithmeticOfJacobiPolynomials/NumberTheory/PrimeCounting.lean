/- Assembled by AxiomProver. -/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.GCD

/-!
# Prime-counting functions in arithmetic progressions

`π(x; q, a)`, the number of primes `p ≤ x` with `p ≡ a (mod q)`, and the logarithmic
integral `Li(x) = ∫_2^x dt / log t`, in the normalizations of [BMOR].
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- `π(x; q, a)`: the number of primes `p ≤ x` with `p ≡ a (mod q)`. -/
noncomputable def primeCountingAP (x : ℝ) (q : ℕ) (a : ℤ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ a [ZMOD q]).card

theorem primeCountingAP_eq (x : ℝ) (q : ℕ) (a : ℤ) : primeCountingAP x q a =
    ((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ a [ZMOD q]).card :=
  (rfl)

/-- The logarithmic integral `Li(x) = ∫_2^x dt / log t` ([BMOR, (1.4)]). -/
noncomputable def logIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

theorem logIntegral_eq (x : ℝ) : logIntegral x = ∫ t in (2 : ℝ)..x, 1 / Real.log t := (rfl)

end ArithmeticOfJacobiPolynomials
