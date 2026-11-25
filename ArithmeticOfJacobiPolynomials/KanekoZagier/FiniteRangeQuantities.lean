/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.CarryBudget

/-!
# The quantities of Proposition B.2

This module only *defines* the integers and reals that the manuscript's finite verification of
Proposition B.2 compares, so that the computer-verified hypothesis
`KanekoZagierFastCriterion` can be *stated* in `External.lean` without importing the proof of the
reduction (which depends on `External`). It contains no theorems beyond unfolding lemmas.

* `kzDelta` — `δ = (μ + 1)/2`;
* `kzEndpointTwo`, `kzEndpointThree` — `D_{2,n} = n + ∑_{j ≤ n} v_2(3j + λ)`,
  `D_{3,n} = n + ∑_{j ≤ n} v_3(2j + μ)` (4.16);
* `kzT0` — `T_0(n) = ∑_{5 ≤ p ≤ 12n+5} (m_p^{(1)} + 1_{p ≤ n} e_p) log p` (Appendix B.1),
  with the first-level indicators `m_p`, `e_p` of Lemma 4.2 (`kzLevelM`, `kzLevelE`);
* `kzQ` — `Q(n) = ∑_{p ≥ 5 prime, h ≥ 2, p^h ≤ 12n+5} log p`;
* `kzC2`, `kzC3` — the integers `c_2`, `c_3` (`c_7 = -21 n`);
* `kzFastDelta` — `Δ_n = (c_2 log 2 + c_3 log 3 + c_7 log 7)/48 - T_0(n) - 3 Q(n)`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-- `δ = (μ + 1)/2` (so `δ = 1` for `μ = 1` and `δ = 0` for `μ = -1`). -/
def kzDelta (μ : ℤ) : ℕ := ((μ + 1) / 2).toNat

theorem kzDelta_eq (μ : ℤ) : kzDelta μ = ((μ + 1) / 2).toNat := (rfl)

/-- `D_{2,n} = n + ∑_{j=1}^n v_2(3j + λ)` (4.16). -/
def kzEndpointTwo (l : ℤ) (n : ℕ) : ℕ := n + ∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l)

theorem kzEndpointTwo_eq (l : ℤ) (n : ℕ) :
    kzEndpointTwo l n = n + ∑ j ∈ Icc 1 n, padicValInt 2 (3 * (j : ℤ) + l) := (rfl)

/-- `D_{3,n} = n + ∑_{j=1}^n v_3(2j + μ)` (4.16). -/
def kzEndpointThree (μ : ℤ) (n : ℕ) : ℕ := n + ∑ j ∈ Icc 1 n, padicValInt 3 (2 * (j : ℤ) + μ)

theorem kzEndpointThree_eq (μ : ℤ) (n : ℕ) :
    kzEndpointThree μ n = n + ∑ j ∈ Icc 1 n, padicValInt 3 (2 * (j : ℤ) + μ) := (rfl)

/-- `T_0(n) = ∑_{5 ≤ p ≤ 12n+5} (m_p^{(1)} + 1_{p ≤ n} e_p) log p`. -/
noncomputable def kzT0 (l μ : ℤ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
    ((kzLevelM l μ n p : ℝ) + if p ≤ n then (kzLevelE l μ n p : ℝ) else 0) * Real.log p

theorem kzT0_eq (l μ : ℤ) (n : ℕ) : kzT0 l μ n =
    ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
      ((kzLevelM l μ n p : ℝ) + if p ≤ n then (kzLevelE l μ n p : ℝ) else 0) * Real.log p :=
  (rfl)

/-- `Q(n) = ∑_{p ≥ 5 prime, h ≥ 2, p^h ≤ 12n+5} log p`, the inner sum running over
`2 ≤ h ≤ ⌊log_p (12n+5)⌋`. -/
noncomputable def kzQ (n : ℕ) : ℝ :=
  ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
    ∑ _h ∈ Icc 2 (Nat.log p (12 * n + 5)), Real.log p

theorem kzQ_eq (n : ℕ) : kzQ n = ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
    ∑ _h ∈ Icc 2 (Nat.log p (12 * n + 5)), Real.log p := (rfl)

/-- `c_2 = 216n + 48 v_2(n!) - 24 s_2(n) - 27 D_{2,n} - 192`. -/
def kzC2 (l : ℤ) (n : ℕ) : ℤ :=
  216 * n + 48 * padicValNat 2 n.factorial - 24 * (Nat.digits 2 n).sum - 27 * kzEndpointTwo l n -
    192

theorem kzC2_eq (l : ℤ) (n : ℕ) : kzC2 l n =
    216 * n + 48 * padicValNat 2 n.factorial - 24 * (Nat.digits 2 n).sum -
      27 * kzEndpointTwo l n - 192 := (rfl)

/-- `c_3 = 48 v_3(n!) - 22n - 21 D_{3,n} - 8 s_3(2n + δ)`. -/
def kzC3 (μ : ℤ) (n : ℕ) : ℤ :=
  48 * padicValNat 3 n.factorial - 22 * n - 21 * kzEndpointThree μ n -
    8 * (Nat.digits 3 (2 * n + kzDelta μ)).sum

theorem kzC3_eq (μ : ℤ) (n : ℕ) : kzC3 μ n =
    48 * padicValNat 3 n.factorial - 22 * n - 21 * kzEndpointThree μ n -
      8 * (Nat.digits 3 (2 * n + kzDelta μ)).sum := (rfl)

/-- `Δ_n = (c_2 log 2 + c_3 log 3 + c_7 log 7)/48 - T_0(n) - 3 Q(n)`, `c_7 = -21 n`. -/
noncomputable def kzFastDelta (l μ : ℤ) (n : ℕ) : ℝ :=
  (kzC2 l n * Real.log 2 + kzC3 μ n * Real.log 3 + (-21 * (n : ℝ)) * Real.log 7) / 48 -
    kzT0 l μ n - 3 * kzQ n

theorem kzFastDelta_eq (l μ : ℤ) (n : ℕ) : kzFastDelta l μ n =
    (kzC2 l n * Real.log 2 + kzC3 μ n * Real.log 3 + (-21 * (n : ℝ)) * Real.log 7) / 48 -
      kzT0 l μ n - 3 * kzQ n := (rfl)

end ArithmeticOfJacobiPolynomials
