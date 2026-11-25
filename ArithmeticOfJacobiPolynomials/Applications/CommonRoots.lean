/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.IntegralParameters
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCoefficients

/-!
# Common roots (Corollary 6.2)

If two rational polynomials share an algebraic root, an irreducible one divides the other.

* `ArithmeticOfJacobiPolynomials.finite_jacobiP_commonRoots`: **Corollary 6.2 (1)** (Corollary
6.2): for
  distinct nonnegative integers `a, b`, only finitely many pairs of different degrees give
  Jacobi polynomials `P_n^{(a,b)}` with a common complex root. It follows from the
  irreducibility assertion of Theorem 1.3, so it is conditional on the cited
  `HansonLcmBound`, `JacobiSimpleRealZeros`.
* For the Legendre polynomials and their first derivatives, every member `P_ℓ`, `P'_ℓ`
  (`ℓ ≥ 1`) is `x^δ` times a reduced polynomial `L_{m,δ,r} = P^{(r)}_{2m+δ+r} / x^δ` of degree
  `2m` (`r, δ ∈ {0,1}`; `legendreReducedMember`). The ratio of the coefficient of `x^{2m-2}`
  to the leading coefficient of `L_{m,δ,r}` is `-ρ(m,δ,r)` with
  `ρ(m,δ,r) = (2m+δ)(2m+δ-1) / (2(4m+2δ+2r-1))` (`coeff_legendreReducedMember_relation`), and
  `ArithmeticOfJacobiPolynomials.legendre_four_ratios` is the chain
  `m(2m-1)/(4m+1) < m(2m-1)/(4m-1) < m(2m+1)/(4m+3) < m(2m+1)/(4m+1)` of the manuscript, so
  the four reduced polynomials of the same degree are pairwise nonproportional.
* `ArithmeticOfJacobiPolynomials.legendre_no_common_root_of_irreducible`: **Corollary 6.2 (2)**,
from the
  irreducibility of the four reduced polynomials (Theorem 1.5) taken as the explicit
  hypothesis `hirr` (an intermediate step; `commonRootsStatement` discharges it using Theorem 1.5).
* `ArithmeticOfJacobiPolynomials.commonRootsStatement_of_irreducible`: **Corollary 6.2**
(`CommonRootsStatement`)
  from the same inputs.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

section CommonRoot

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Coprime polynomials have no common root. -/
theorem not_aeval_eq_zero_of_isCoprime {f g : K[X]} (h : IsCoprime f g) {z : L}
    (hf : aeval z f = 0) (hg : aeval z g = 0) : False := by
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (aeval z) huv
  simp [hf, hg] at this

/-- An irreducible polynomial shares no root with a nonzero polynomial of smaller degree. -/
theorem aeval_ne_zero_of_irreducible_of_natDegree_lt {f g : K[X]} (hf : Irreducible f)
    (hg : g ≠ 0) (hdeg : g.natDegree < f.natDegree) {z : L} (hz : aeval z f = 0) :
    aeval z g ≠ 0 := by
  intro hgz
  have hndvd : ¬ f ∣ g := fun h => absurd hdeg (not_lt.mpr (natDegree_le_of_dvd h hg))
  exact not_aeval_eq_zero_of_isCoprime (hf.coprime_iff_not_dvd.mpr hndvd) hz hgz

/-- Two irreducible polynomials with a common root are proportional. -/
theorem exists_eq_C_mul_of_irreducible_of_aeval_eq_zero {f g : K[X]} (hf : Irreducible f)
    (hg : Irreducible g) {z : L} (hfz : aeval z f = 0) (hgz : aeval z g = 0) :
    ∃ c : K, c ≠ 0 ∧ g = C c * f := by
  have hdvd : f ∣ g := by
    by_contra h
    exact not_aeval_eq_zero_of_isCoprime (hf.coprime_iff_not_dvd.mpr h) hfz hgz
  obtain ⟨q, hq⟩ := hdvd
  rcases hg.isUnit_or_isUnit hq with hu | hu
  · exact absurd hu hf.not_isUnit
  · obtain ⟨c, hc, hcq⟩ := Polynomial.isUnit_iff.mp hu
    exact ⟨c, hc.ne_zero, by rw [hq, ← hcq, mul_comm]⟩

end CommonRoot

/-- **Corollary 6.2 (1).** For distinct nonnegative integers `a, b`, only
finitely many pairs of different degrees `(n₁, n₂)` give Jacobi polynomials `P_{n₁}^{(a,b)}`,
`P_{n₂}^{(a,b)}` with a common complex root: once the larger degree is at least the threshold
`N(a,b)` of Theorem 1.3, the irreducible polynomial of larger degree cannot share a root with
the other one. -/
theorem finite_jacobiP_commonRoots (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) :
    {nn : ℕ × ℕ | nn.1 ≠ nn.2 ∧ ∃ z : ℂ, aeval z (jacobiP a b nn.1) = 0 ∧
        aeval z (jacobiP a b nn.2) = 0}.Finite := by
  obtain ⟨N, hN⟩ := exists_forall_irreducible_jacobiP hH hZ hab
  have key : ∀ {k l : ℕ}, k < l → ∀ z : ℂ, aeval z (jacobiP a b k) = 0 →
      aeval z (jacobiP a b l) = 0 → l < N := by
    intro k l hkl z hk hl
    by_contra hlN
    refine aeval_ne_zero_of_irreducible_of_natDegree_lt (hN l (by omega))
      (jacobiP_nat_ne_zero a b k) ?_ hl hk
    rw [natDegree_jacobiP_nat, natDegree_jacobiP_nat]
    exact hkl
  refine ((Finset.range N ×ˢ Finset.range N : Finset (ℕ × ℕ)).finite_toSet).subset ?_
  rintro ⟨n₁, n₂⟩ ⟨hne, z, h₁, h₂⟩
  dsimp only at hne h₁ h₂
  refine Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩)
  · change n₁ < N
    rcases lt_or_gt_of_ne hne with h | h
    · have := key h z h₁ h₂; omega
    · exact key h z h₂ h₁
  · change n₂ < N
    rcases lt_or_gt_of_ne hne with h | h
    · exact key h z h₁ h₂
    · have := key h z h₂ h₁; omega

/-! ### The reduced Legendre polynomials and derivatives -/

/-- The reduced polynomial `L_{m,δ,r} = P^{(r)}_{2m+δ+r} / x^δ`, of degree `2m`. For
`r, δ ∈ {0,1}` these are `P_{2m}`, `P_{2m+1}/x`, `P'_{2m+1}` and `P'_{2m+2}/x`. -/
noncomputable def legendreReducedMember (m δ r : ℕ) : ℚ[X] :=
  derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ

theorem legendreReducedMember_eq (m δ r : ℕ) :
    legendreReducedMember m δ r = derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ := (rfl)

theorem X_pow_mul_legendreReducedMember (m δ r : ℕ) (hδ : δ ≤ 1) :
    polyX ^ δ * legendreReducedMember m δ r = derivative^[r] (legendreP (2 * m + δ + r)) :=
  X_pow_mul_iterate_derivative_legendreP_divByMonic m r δ hδ

theorem coeff_legendreReducedMember (m δ r : ℕ) (hδ : δ ≤ 1) (k : ℕ) :
    (legendreReducedMember m δ r).coeff k =
      (derivative^[r] (legendreP (2 * m + δ + r))).coeff (k + δ) := by
  have h := coeff_X_pow_mul (legendreReducedMember m δ r) δ k
  rw [X_pow_mul_legendreReducedMember m δ r hδ] at h
  exact h.symm

theorem natDegree_legendreReducedMember (m δ r : ℕ) :
    (legendreReducedMember m δ r).natDegree = 2 * m := by
  rw [legendreReducedMember_eq, natDegree_divByMonic _ (monic_X_pow δ),
    natDegree_iterate_derivative_legendreP, natDegree_X_pow]
  omega

theorem coeff_legendreReducedMember_top_ne_zero (m δ r : ℕ) (hδ : δ ≤ 1) :
    (legendreReducedMember m δ r).coeff (2 * m) ≠ 0 := by
  rw [coeff_legendreReducedMember m δ r hδ]
  exact coeff_iterate_derivative_legendreP_self_ne_zero (2 * m + δ) r

/-- The reduced polynomials of degree `0` have no roots. -/
theorem aeval_legendreReducedMember_zero_ne_zero (δ r : ℕ) (hδ : δ ≤ 1) (z : ℂ) :
    aeval z (legendreReducedMember 0 δ r) ≠ 0 := by
  have hdeg := natDegree_legendreReducedMember 0 δ r
  have hc := coeff_legendreReducedMember_top_ne_zero 0 δ r hδ
  rw [eq_C_of_natDegree_eq_zero (p := legendreReducedMember 0 δ r) (by simpa using hdeg),
    aeval_C]
  simpa using hc

/-- The coefficient of `x^{n-2}` in `P^{(r)}_{n+r}`, `n = q + 2`:
`2(2n+2r-1) [x^{n-2}] = -n(n-1) [x^n]`. -/
theorem coeff_iterate_derivative_legendreP_sub_two (q r : ℕ) :
    2 * (2 * (q : ℚ) + 2 * r + 3) * (derivative^[r] (legendreP (q + 2 + r))).coeff q =
      -(((q : ℚ) + 2) * ((q : ℚ) + 1)) *
        (derivative^[r] (legendreP (q + 2 + r))).coeff (q + 2) := by
  have h1 := coeff_iterate_derivative_legendreP (q + 2) r 1 (by omega)
  have h0 := coeff_iterate_derivative_legendreP (q + 2) r 0 (by omega)
  rw [show q + 2 - 2 * 1 = q by omega,
    show 2 * (q + 2) + 2 * r - 2 * 1 = 2 * q + 2 * r + 2 by omega,
    show q + 2 + r - 1 = q + r + 1 by omega] at h1
  rw [show q + 2 - 2 * 0 = q + 2 by omega,
    show 2 * (q + 2) + 2 * r - 2 * 0 = 2 * q + 2 * r + 2 + 1 + 1 by omega,
    show q + 2 + r - 0 = q + r + 1 + 1 by omega] at h0
  rw [h1, h0]
  have f1 : ((2 * q + 2 * r + 2 + 1 + 1).factorial : ℚ) =
      (2 * (q : ℚ) + 2 * r + 4) * (2 * q + 2 * r + 3) * (2 * q + 2 * r + 2).factorial := by
    rw [Nat.factorial_succ (2 * q + 2 * r + 2 + 1), Nat.factorial_succ (2 * q + 2 * r + 2)]
    push_cast; ring
  have f2 : ((q + r + 1 + 1).factorial : ℚ) = ((q : ℚ) + r + 2) * (q + r + 1).factorial := by
    rw [Nat.factorial_succ (q + r + 1)]
    push_cast; ring
  have f3 : ((q + 2).factorial : ℚ) = ((q : ℚ) + 2) * ((q : ℚ) + 1) * q.factorial := by
    rw [show q + 2 = q + 1 + 1 from rfl, Nat.factorial_succ (q + 1), Nat.factorial_succ q]
    push_cast; ring
  rw [f1, f2, f3]
  have : ((2 * q + 2 * r + 2).factorial : ℚ) ≠ 0 := by positivity
  have : ((q + r + 1).factorial : ℚ) ≠ 0 := by positivity
  have : (q.factorial : ℚ) ≠ 0 := by positivity
  have : (q : ℚ) + r + 2 ≠ 0 := by positivity
  have : (q : ℚ) + 2 ≠ 0 := by positivity
  have : (q : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `ρ(m,δ,r) = (2m+δ)(2m+δ-1) / (2(4m+2δ+2r-1))`: minus the ratio of the coefficient of
`x^{2m-2}` to the leading coefficient of `L_{m,δ,r}`. -/
noncomputable def legendreRatio (m δ r : ℕ) : ℚ :=
  ((2 * m + δ : ℚ) * (2 * m + δ - 1)) / (2 * (4 * m + 2 * δ + 2 * r - 1))

theorem legendreRatio_eq (m δ r : ℕ) : legendreRatio m δ r =
    ((2 * m + δ : ℚ) * (2 * m + δ - 1)) / (2 * (4 * m + 2 * δ + 2 * r - 1)) := (rfl)

private lemma eq_neg_div_mul {a b N D : ℚ} (hD : D ≠ 0) (h : D * a = -N * b) :
    a = -(N / D) * b :=
  calc a = D * a / D := (mul_div_cancel_left₀ a hD).symm
    _ = -N * b / D := by rw [h]
    _ = -(N / D) * b := by ring

/-- The coefficient of `x^{2m-2}` in `L_{m,δ,r}` is `-ρ(m,δ,r)` times the leading one. -/
theorem coeff_legendreReducedMember_relation (m δ r : ℕ) (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    (legendreReducedMember m δ r).coeff (2 * (m - 1)) =
      -legendreRatio m δ r * (legendreReducedMember m δ r).coeff (2 * m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [coeff_legendreReducedMember _ _ _ hδ, coeff_legendreReducedMember _ _ _ hδ,
    show 2 * (k + 1 - 1) + δ = 2 * k + δ by omega, show 2 * (k + 1) + δ = 2 * k + δ + 2 by ring]
  have base := coeff_iterate_derivative_legendreP_sub_two (2 * k + δ) r
  have hδ0 : (0 : ℚ) ≤ δ := Nat.cast_nonneg δ
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hD : (2 * (4 * ((k + 1 : ℕ) : ℚ) + 2 * δ + 2 * r - 1)) ≠ 0 := by
    push_cast; exact ne_of_gt (by linarith)
  have key : (2 * (4 * ((k + 1 : ℕ) : ℚ) + 2 * δ + 2 * r - 1)) *
      (derivative^[r] (legendreP (2 * k + δ + 2 + r))).coeff (2 * k + δ) =
      -((2 * ((k + 1 : ℕ) : ℚ) + δ) * (2 * ((k + 1 : ℕ) : ℚ) + δ - 1)) *
        (derivative^[r] (legendreP (2 * k + δ + 2 + r))).coeff (2 * k + δ + 2) := by
    push_cast at base ⊢
    linear_combination base
  exact eq_neg_div_mul hD key

/-- **The four coefficient ratios** of the proof of Corollary 6.2:
`m(2m-1)/(4m+1) < m(2m-1)/(4m-1) < m(2m+1)/(4m+3) < m(2m+1)/(4m+1)` for `m ≥ 1`. -/
theorem legendre_four_ratios (m : ℕ) (hm : 1 ≤ m) :
    (m : ℚ) * (2 * m - 1) / (4 * m + 1) < m * (2 * m - 1) / (4 * m - 1) ∧
    (m : ℚ) * (2 * m - 1) / (4 * m - 1) < m * (2 * m + 1) / (4 * m + 3) ∧
    (m : ℚ) * (2 * m + 1) / (4 * m + 3) < m * (2 * m + 1) / (4 * m + 1) := by
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℚ) < m * (2 * m - 1) := mul_pos (by linarith) (by linarith)
  have h2 : (0 : ℚ) < m * (2 * m + 1) := mul_pos (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_⟩ <;> rw [div_lt_div_iff₀ (by linarith) (by linarith)] <;> nlinarith

theorem legendreRatio_zero_one (m : ℕ) (hm : 1 ≤ m) :
    legendreRatio m 0 1 = (m : ℚ) * (2 * m - 1) / (4 * m + 1) := by
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [legendreRatio_eq, div_eq_div_iff (by push_cast; exact ne_of_gt (by linarith))
    (ne_of_gt (by linarith))]
  push_cast; ring

theorem legendreRatio_zero_zero (m : ℕ) (hm : 1 ≤ m) :
    legendreRatio m 0 0 = (m : ℚ) * (2 * m - 1) / (4 * m - 1) := by
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [legendreRatio_eq, div_eq_div_iff (by push_cast; exact ne_of_gt (by linarith))
    (ne_of_gt (by linarith))]
  push_cast; ring

theorem legendreRatio_one_one (m : ℕ) (hm : 1 ≤ m) :
    legendreRatio m 1 1 = (m : ℚ) * (2 * m + 1) / (4 * m + 3) := by
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [legendreRatio_eq, div_eq_div_iff (by push_cast; exact ne_of_gt (by linarith))
    (ne_of_gt (by linarith))]
  push_cast; ring

theorem legendreRatio_one_zero (m : ℕ) (hm : 1 ≤ m) :
    legendreRatio m 1 0 = (m : ℚ) * (2 * m + 1) / (4 * m + 1) := by
  have hx : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [legendreRatio_eq, div_eq_div_iff (by push_cast; exact ne_of_gt (by linarith))
    (ne_of_gt (by linarith))]
  push_cast; ring

/-- **Nonproportionality.** For `m ≥ 1` the four values `ρ(m,δ,r)`, `δ, r ∈ {0,1}`, are
pairwise distinct. -/
theorem legendreRatio_injective {m δ r δ' r' : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1) (hr : r ≤ 1)
    (hδ' : δ' ≤ 1) (hr' : r' ≤ 1) (h : legendreRatio m δ r = legendreRatio m δ' r') :
    δ = δ' ∧ r = r' := by
  have c1 : legendreRatio m 0 1 < legendreRatio m 0 0 := by
    rw [legendreRatio_zero_one m hm, legendreRatio_zero_zero m hm]
    exact (legendre_four_ratios m hm).1
  have c2 : legendreRatio m 0 0 < legendreRatio m 1 1 := by
    rw [legendreRatio_zero_zero m hm, legendreRatio_one_one m hm]
    exact (legendre_four_ratios m hm).2.1
  have c3 : legendreRatio m 1 1 < legendreRatio m 1 0 := by
    rw [legendreRatio_one_one m hm, legendreRatio_one_zero m hm]
    exact (legendre_four_ratios m hm).2.2
  interval_cases δ <;> interval_cases r <;> interval_cases δ' <;> interval_cases r' <;>
    first | exact ⟨rfl, rfl⟩ | (exfalso; linarith)

/-- Every member `P_ℓ` (`b = false`) or `P'_ℓ` (`b = true`), `ℓ ≥ 1`, is `P^{(r)}_{2m+δ+r}`
with `δ, r ∈ {0,1}` and `r = 1` exactly for the derivatives. -/
theorem exists_legendreMember_eq (k : ℕ × Bool) (hk : 1 ≤ k.1) :
    ∃ m δ r : ℕ, δ ≤ 1 ∧ r ≤ 1 ∧ k.1 = 2 * m + δ + r ∧ (k.2 = true ↔ r = 1) ∧
      (if k.2 then derivative (legendreP k.1) else legendreP k.1) =
        derivative^[r] (legendreP (2 * m + δ + r)) := by
  obtain ⟨ℓ, b⟩ := k
  cases b
  · refine ⟨ℓ / 2, ℓ % 2, 0, by omega, by omega, by dsimp only; omega, by simp, ?_⟩
    dsimp only
    rw [show 2 * (ℓ / 2) + ℓ % 2 + 0 = ℓ by omega]
    simp
  · dsimp only at hk
    refine ⟨(ℓ - 1) / 2, (ℓ - 1) % 2, 1, by omega, le_rfl, by dsimp only; omega, by simp, ?_⟩
    dsimp only
    rw [show 2 * ((ℓ - 1) / 2) + (ℓ - 1) % 2 + 1 = ℓ by omega]
    simp

/-- The four reduced polynomials of each degree `2m ≥ 2` are irreducible, given Theorem 1.5. -/
theorem irreducible_legendreReducedMember_of (hirr : ∀ m : ℕ, 1 ≤ m → Irreducible (legendreP (2 *
    m)) ∧
      Irreducible (legendreP (2 * m + 1) /ₘ polyX) ∧ Irreducible (derivative (legendreP (2 * m +
        1))) ∧
      Irreducible (derivative (legendreP (2 * m + 2)) /ₘ polyX))
    {m δ r : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1) (hr : r ≤ 1) :
    Irreducible (legendreReducedMember m δ r) := by
  obtain ⟨h1, h2, h3, h4⟩ := hirr m hm
  rw [legendreReducedMember_eq]
  interval_cases δ <;> interval_cases r
  · simpa using h1
  · simpa using h3
  · simpa using h2
  · rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring]
    simpa using h4

/-- **Corollary 6.2 (2)**, from the irreducibility of the four reduced
polynomials `P_{2m}`, `P_{2m+1}/x`, `P'_{2m+1}`, `P'_{2m+2}/x` (`m ≥ 1`; Theorem 1.5), taken
as the explicit hypothesis `hirr`: no two distinct members of `{P_ℓ, P'_ℓ : ℓ ≥ 1}` have a
common nonzero complex root. -/
theorem legendre_no_common_root_of_irreducible (hirr : ∀ m : ℕ, 1 ≤ m → Irreducible (legendreP (2 *
    m)) ∧
      Irreducible (legendreP (2 * m + 1) /ₘ polyX) ∧ Irreducible (derivative (legendreP (2 * m +
        1))) ∧
      Irreducible (derivative (legendreP (2 * m + 2)) /ₘ polyX))
    (i j : ℕ × Bool) (hi : 1 ≤ i.1) (hj : 1 ≤ j.1) (hij : i ≠ j) (z : ℂ) (hz : z ≠ 0) :
    ¬ (aeval z (if i.2 then derivative (legendreP i.1) else legendreP i.1) = 0 ∧
      aeval z (if j.2 then derivative (legendreP j.1) else legendreP j.1) = 0) := by
  rintro ⟨hzi, hzj⟩
  obtain ⟨mi, δi, ri, hδi, hri, hℓi, hbi, hPi⟩ := exists_legendreMember_eq i hi
  obtain ⟨mj, δj, rj, hδj, hrj, hℓj, hbj, hPj⟩ := exists_legendreMember_eq j hj
  rw [hPi, ← X_pow_mul_legendreReducedMember mi δi ri hδi, map_mul, map_pow, aeval_X] at hzi
  rw [hPj, ← X_pow_mul_legendreReducedMember mj δj rj hδj, map_mul, map_pow, aeval_X] at hzj
  have hRi := (mul_eq_zero.mp hzi).resolve_left (pow_ne_zero _ hz)
  have hRj := (mul_eq_zero.mp hzj).resolve_left (pow_ne_zero _ hz)
  have hmi : 1 ≤ mi := by
    by_contra h
    obtain rfl : mi = 0 := by omega
    exact aeval_legendreReducedMember_zero_ne_zero δi ri hδi z hRi
  have hmj : 1 ≤ mj := by
    by_contra h
    obtain rfl : mj = 0 := by omega
    exact aeval_legendreReducedMember_zero_ne_zero δj rj hδj z hRj
  obtain ⟨c, hc, hcR⟩ := exists_eq_C_mul_of_irreducible_of_aeval_eq_zero
    (irreducible_legendreReducedMember_of hirr hmi hδi hri)
    (irreducible_legendreReducedMember_of hirr hmj hδj hrj) hRi hRj
  have hm : mi = mj := by
    have := congrArg natDegree hcR
    rw [natDegree_C_mul hc, natDegree_legendreReducedMember,
      natDegree_legendreReducedMember] at this
    omega
  rw [← hm] at hcR
  have hrel_i := coeff_legendreReducedMember_relation mi δi ri hmi hδi
  have hrel_j := coeff_legendreReducedMember_relation mi δj rj hmi hδj
  rw [hcR, coeff_C_mul, coeff_C_mul] at hrel_j
  have hlead := coeff_legendreReducedMember_top_ne_zero mi δi ri hδi
  have hρ : legendreRatio mi δi ri = legendreRatio mi δj rj := by
    have h0 : (legendreRatio mi δi ri - legendreRatio mi δj rj) *
        (c * (legendreReducedMember mi δi ri).coeff (2 * mi)) = 0 := by
      linear_combination c * hrel_i - hrel_j
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (mul_ne_zero hc hlead)
  obtain ⟨rfl, rfl⟩ := legendreRatio_injective hmi hδi hri hδj hrj hρ
  apply hij
  exact Prod.ext (by omega) (Bool.eq_iff_iff.mpr (hbi.trans hbj.symm))

/-- **Corollary 6.2**, conditional on the literature inputs of Theorem 1.3
and on the irreducibility of the four reduced polynomials (Theorem 1.5), the latter taken as
the explicit hypothesis `hirr` (an intermediate step; `commonRootsStatement` discharges it using
Theorem 1.5). -/
theorem commonRootsStatement_of_irreducible (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros)
    (hirr : ∀ m : ℕ, 1 ≤ m → Irreducible (legendreP (2 * m)) ∧
      Irreducible (legendreP (2 * m + 1) /ₘ polyX) ∧ Irreducible (derivative (legendreP (2 * m +
        1))) ∧
      Irreducible (derivative (legendreP (2 * m + 2)) /ₘ polyX)) :
    CommonRootsStatement := by
  unfold CommonRootsStatement
  exact ⟨fun a b hab => finite_jacobiP_commonRoots hH hZ hab,
    fun i j hi hj hij z hz => legendre_no_common_root_of_irreducible hirr i j hi hj hij z hz⟩

end ArithmeticOfJacobiPolynomials
