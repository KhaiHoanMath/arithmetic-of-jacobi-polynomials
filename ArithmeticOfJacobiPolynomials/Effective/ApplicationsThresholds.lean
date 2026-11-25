/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Effective.UnequalGaloisThreshold
public import ArithmeticOfJacobiPolynomials.Effective.SymmetricThresholds
public import ArithmeticOfJacobiPolynomials.Applications.IntegralParameters
public import ArithmeticOfJacobiPolynomials.Applications.CommonRoots
public import ArithmeticOfJacobiPolynomials.Applications.ConeModes

/-!
# Explicit thresholds for Section 6: Corollaries 6.1, 6.2, 6.5 (1) and the exceptional degrees

The explicit thresholds of Theorem 1.3 (`unequalThreshold`, `unequalGaloisThreshold`) and of
Theorem 1.4 (`symmetricAbsoluteThreshold`) transfer to the applications of Section 6:

* **Corollary 6.1** ("effectively in `a, b`"):
  `integralParametersThreshold a b = unequalGaloisThreshold |a| |b| + a_- + b_-`
  (`integralParameters_of_integralParametersThreshold_le`);
* **the exceptional degrees** (§6.6, "for integral parameters the exceptional degrees form an
  effective finite set"): they lie in `range (integralParametersThreshold a b)`
  (`exceptionalDegrees_integralParameters_subset_range`);
* **Corollary 6.2 (1)** ("all such pairs lie in an effective
  range"): two different degrees with a common root are both `< unequalThreshold a b`
  (`lt_unequalThreshold_of_commonRoot`, `jacobiP_commonRoots_subset_range`);
* **Corollary 6.5 (1)** ("an effective integer `L_D`"):
  `coneModesAlgebraicThreshold D = 3 (symmetricAbsoluteThreshold + D) + 6`
  (`coneModes_algebraic_effective`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-! ### Corollary 6.1 -/

/-- The explicit computable threshold of Corollary 6.1:
`unequalGaloisThreshold |a| |b| + a_- + b_-`, `a_- = max(-a, 0)`, `b_- = max(-b, 0)`. -/
def integralParametersThreshold (a b : ℤ) : ℕ :=
  unequalGaloisThreshold a.natAbs b.natAbs + (-a).toNat + (-b).toNat

theorem integralParametersThreshold_eq (a b : ℤ) : integralParametersThreshold a b =
    unequalGaloisThreshold a.natAbs b.natAbs + (-a).toNat + (-b).toNat := (rfl)

/-- **Corollary 6.1, effective form**. For integers `a, b` with
`|a| ≠ |b|` and every `n ≥ integralParametersThreshold a b`, the polynomial
`g = P_n^{(a,b)} / ((x-1)^{a_-} (x+1)^{b_-})` has degree `n - a_- - b_-`, is irreducible over `ℚ`
and has Galois group `S_{n - a_- - b_-}`. Conditional on the cited literature of Theorem 1.3. -/
theorem integralParameters_of_integralParametersThreshold_le (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℤ} (hab : |a| ≠ |b|) :
    ∀ n ≥ integralParametersThreshold a b,
      let g := jacobiP a b n /ₘ ((polyX - 1) ^ (-a).toNat * (polyX + 1) ^ (-b).toNat)
      g.natDegree = n - (-a).toNat - (-b).toNat ∧ Irreducible g ∧ GaloisGroupIsSymmetric g := by
  have hab' : a.natAbs ≠ b.natAbs := by
    intro h; apply hab; rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
  intro n hn
  rw [integralParametersThreshold_eq] at hn
  obtain ⟨c, hc, h⟩ := exists_jacobiP_int_divByMonic_eq a b n (by omega)
  obtain ⟨hirr, hS⟩ := irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le
    hH hZ hJordan hEis hdisc hDusart hab' (n - (-a).toNat - (-b).toNat) (by omega)
  dsimp only
  rw [h, natDegree_C_mul hc, natDegree_jacobiP_nat]
  refine ⟨rfl, ?_, hS.C_mul hc⟩
  rw [irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit hc))]
  exact hirr

/-- Corollary 6.1 (`IntegralParametersStatement`) with the explicit witness. -/
theorem integralParametersStatement_effective (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) :
    IntegralParametersStatement := fun _ _ hab =>
  ⟨_, integralParameters_of_integralParametersThreshold_le hH hZ hJordan hEis hdisc hDusart hab⟩

/-- **The exceptional degrees form an effective finite set** (§6.6). For integers `a, b`
with `|a| ≠ |b|`, every degree `n` for which `P_n^{(a,b)}/((x-1)^{a_-}(x+1)^{b_-})` is reducible
or has Galois group other than `S_{n-a_--b_-}` lies in `range (integralParametersThreshold a b)`.
-/
theorem exceptionalDegrees_integralParameters_subset_range (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℤ} (hab : |a| ≠ |b|) :
    {n : ℕ | ¬ (Irreducible (jacobiP a b n /ₘ ((polyX - 1) ^ (-a).toNat * (polyX + 1) ^
      (-b).toNat)) ∧
        GaloisGroupIsSymmetric
          (jacobiP a b n /ₘ ((polyX - 1) ^ (-a).toNat * (polyX + 1) ^ (-b).toNat)))} ⊆
      ↑(Finset.range (integralParametersThreshold a b)) := by
  intro n hn
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  have hh := integralParameters_of_integralParametersThreshold_le hH hZ hJordan hEis hdisc hDusart
    hab n (not_lt.mp hlt)
  dsimp only at hh
  exact hn ⟨hh.2.1, hh.2.2⟩

/-! ### Corollary 6.2 (1) -/

/-- **Corollary 6.2 (1), effective range**. For distinct nonnegative
integers `a, b`, if `P_{n₁}^{(a,b)}` and `P_{n₂}^{(a,b)}` with `n₁ ≠ n₂` have a common complex
root, then `n₁, n₂ < unequalThreshold a b`. Conditional on `HansonLcmBound`,
`JacobiSimpleRealZeros`. -/
theorem lt_unequalThreshold_of_commonRoot (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) {n₁ n₂ : ℕ} (hne : n₁ ≠ n₂) {z : ℂ}
    (h₁ : aeval z (jacobiP a b n₁) = 0) (h₂ : aeval z (jacobiP a b n₂) = 0) :
    n₁ < unequalThreshold a b ∧ n₂ < unequalThreshold a b := by
  have key : ∀ {k l : ℕ}, k < l → aeval z (jacobiP a b k) = 0 →
      aeval z (jacobiP a b l) = 0 → l < unequalThreshold a b := by
    intro k l hkl hk hl
    by_contra hlN
    refine aeval_ne_zero_of_irreducible_of_natDegree_lt
      (irreducible_jacobiP_of_unequalThreshold_le hH hZ hab l (not_lt.mp hlN))
      (jacobiP_nat_ne_zero a b k) ?_ hl hk
    rw [natDegree_jacobiP_nat, natDegree_jacobiP_nat]
    exact hkl
  rcases lt_or_gt_of_ne hne with h | h
  · have := key h h₁ h₂
    exact ⟨by omega, this⟩
  · have := key h h₂ h₁
    exact ⟨this, by omega⟩

/-- Corollary 6.2 (1) as a set inclusion into the explicit range. -/
theorem jacobiP_commonRoots_subset_range (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) :
    {nn : ℕ × ℕ | nn.1 ≠ nn.2 ∧ ∃ z : ℂ, aeval z (jacobiP a b nn.1) = 0 ∧
        aeval z (jacobiP a b nn.2) = 0} ⊆
      ↑(Finset.range (unequalThreshold a b) ×ˢ Finset.range (unequalThreshold a b)) := by
  rintro ⟨n₁, n₂⟩ ⟨hne, z, h₁, h₂⟩
  obtain ⟨h1, h2⟩ := lt_unequalThreshold_of_commonRoot hH hZ hab hne h₁ h₂
  exact Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩)

/-! ### Corollary 6.5 (1) -/

/-- The explicit computable `L_D` of Corollary 6.5 (1):
`3 (symmetricAbsoluteThreshold + D) + 6`. -/
def coneModesAlgebraicThreshold (D : ℕ) : ℕ := 3 * (symmetricAbsoluteThreshold + D) + 6

theorem coneModesAlgebraicThreshold_eq (D : ℕ) :
    coneModesAlgebraicThreshold D = 3 * (symmetricAbsoluteThreshold + D) + 6 := (rfl)

/-- **Corollary 6.5 (1), effective form**. For every `D`, every nonzero real
algebraic `α ∈ (-1,1)` of degree at most `D`, `ℓ ≥ coneModesAlgebraicThreshold D`, `r ≤ ℓ` and
`P_ℓ^{(r)}(α) = 0` imply `17r > ℓ - 1`. Conditional on
`JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem coneModes_algebraic_effective (hZ : JacobiSimpleRealZeros) (hD : DusartThetaBound) (D : ℕ) :
    ∀ α : ℝ, α ≠ 0 → -1 < α → α < 1 → IsAlgebraic ℚ α →
      (minpoly ℚ α).natDegree ≤ D → ∀ ℓ r : ℕ, coneModesAlgebraicThreshold D ≤ ℓ → r ≤ ℓ →
      aeval α (derivative^[r] (legendreP ℓ)) = 0 → ℓ - 1 < 17 * r := by
  have hM₀ := irreducible_reducedGegenbauer_of_symmetricAbsoluteThreshold_le hZ hD
  obtain ⟨M₀, hM₀e⟩ : ∃ M₀, M₀ = symmetricAbsoluteThreshold := ⟨_, rfl⟩
  rw [← hM₀e] at hM₀
  intro α hα0 _ _ _ hdeg ℓ r hL hr h
  rw [coneModesAlgebraicThreshold_eq, ← hM₀e] at hL
  by_contra hcon
  push Not at hcon
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ : ℕ, δ ≤ 1 ∧ ℓ = 2 * m + δ + r :=
    ⟨(ℓ - r) / 2, (ℓ - r) % 2, by omega, by omega⟩
  have hm8 : 8 * r ≤ m := by omega
  have hmM : M₀ + D + 1 ≤ m := by omega
  have hirr := hM₀ m r δ hδ (by omega) (max_le hm8 (by omega))
  have hR := aeval_reducedGegenbauer_eq_zero hδ hα0 h
  have hmin := minpoly.eq_of_irreducible hirr hR
  have hR0 : reducedGegenbauer m r δ ≠ 0 := hirr.ne_zero
  rw [← hmin, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hR0)),
    natDegree_reducedGegenbauer m r δ hδ] at hdeg
  omega

end ArithmeticOfJacobiPolynomials
