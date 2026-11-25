/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.UnequalIrreducibility
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# A degree bound for prescribed zeros (remark after Corollary 6.2)

The manuscript remarks after Corollary 6.2: "The same argument gives a degree bound for any
prescribed algebraic number `ξ`: `P_n^{(a,b)}(ξ) ≠ 0` for `n > max{N(a,b), [ℚ(ξ):ℚ]}`."

* `aeval_jacobiP_ne_zero_of_irreducible`: if `P_n^{(a,b)}` is irreducible over `ℚ` and the
  degree of the minimal polynomial of `ξ` is less than `n`, then `P_n^{(a,b)}(ξ) ≠ 0`;
* `exists_forall_aeval_jacobiP_ne_zero`: for distinct nonnegative integers `a, b` there is
  `N` such that `P_n^{(a,b)}(ξ) ≠ 0` whenever `n ≥ N` and `[ℚ(ξ):ℚ] < n`, for every element
  `ξ` of every field of characteristic zero. The threshold is the irreducibility threshold of
  Theorem 1.3 (`exists_forall_irreducible_jacobiP`), conditional on the literature cited
  there.

Here `[ℚ(ξ):ℚ]` is the degree of `minpoly ℚ ξ` (which is `0`, making the hypothesis vacuous
in `n ≥ 1`, when `ξ` is transcendental; the conclusion holds in that case as well).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- An irreducible `P_n^{(a,b)}` does not vanish at an element whose minimal polynomial over
`ℚ` has degree less than `n`. -/
theorem aeval_jacobiP_ne_zero_of_irreducible {a b n : ℕ} (hirr : Irreducible (jacobiP a b n))
    {K : Type*} [Field K] [Algebra ℚ K] (ξ : K) (hdeg : (minpoly ℚ ξ).natDegree < n) :
    aeval ξ (jacobiP a b n) ≠ 0 := by
  intro h0
  have hmin := minpoly.eq_of_irreducible hirr h0
  have hlc : (jacobiP a b n).leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  have hchoose : Ring.choose (2 * (n : ℚ) + (a : ℚ) + (b : ℚ)) n ≠ 0 := by
    rw [show 2 * (n : ℚ) + (a : ℚ) + (b : ℚ) = ((2 * n + a + b : ℕ) : ℚ) by push_cast; ring,
      Ring.choose_natCast]
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hdegP := natDegree_jacobiP (a : ℚ) (b : ℚ) n hchoose
  rw [← hmin, natDegree_mul_C hlc, hdegP] at hdeg
  exact lt_irrefl n hdeg

/-- **Remark after Corollary 6.2.** For distinct nonnegative integers `a, b` there is `N(a,b)`
such that `P_n^{(a,b)}(ξ) ≠ 0` for every `n ≥ N(a,b)` with `n > [ℚ(ξ):ℚ]`, for every `ξ` in
every field of characteristic zero. -/
theorem exists_forall_aeval_jacobiP_ne_zero (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ (K : Type) [Field K] [Algebra ℚ K] (ξ : K) (n : ℕ), N ≤ n →
      (minpoly ℚ ξ).natDegree < n → aeval ξ (jacobiP a b n) ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_forall_irreducible_jacobiP hH hZ hab
  exact ⟨N, fun K _ _ ξ n hn hdeg => aeval_jacobiP_ne_zero_of_irreducible (hN n hn) ξ hdeg⟩

end ArithmeticOfJacobiPolynomials
