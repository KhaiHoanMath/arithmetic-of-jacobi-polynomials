/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Jacobi.Shift

/-!
# The Kaneko–Zagier source polynomial and the manuscript's normalization (§6.4)

[KZ] (M. Kaneko and D. Zagier, *Supersingular j-invariants, hypergeometric series, and Atkin's
orthogonal polynomials*, AMS/IP Stud. Adv. Math. 7 (1998), 97–126) define, for `k = 12m + 4δ + 6ε`
with `k ≢ 2 (mod 3)`, the polynomial `F̃_k(j)` by [KZ, (12)] (normalization) and give it explicitly
in [KZ, Theorem 5 ii)]; with `σ = (0 ∞)`, `ν₀ = (1 - 2δ)/3`, `ν_∞ = (k + 1)/6`,

  `F̃_k(j) = 1728^m binom(m - ν₀, m) F(-m, -m + ν_∞; 1 - ν₀; j/1728)`.

* `kzSourcePoly ν₀ νinf m`: this terminating hypergeometric polynomial, written out with the
  Pochhammer coefficients (the series stops at `i = m` because `(-m)_i = 0` for `i > m`);
* `kzSourcePoly_eq_scaled_jacobi`: for `α` with `(1 + α)_i ≠ 0` (`i ≤ n`) and any `β`,
  `kzSourcePoly (-α) (2n + α + β + 1) n = 1728^n P_n^{(α,β)}(1 - Y/864)`;
* `kzSourcePoly_eq_kanekoZagierModularPoly`: the manuscript's normalization step (§6.4),
  for `λ, μ ∈ {-1, 1}`: `ν₀ = -λ/3`, `ν_∞ = ℓ/6`, `ℓ = 12n + 6 + 2λ + 3μ`, so
  `kzSourcePoly (-λ/3) (ℓ/6) n = kanekoZagierModularPoly λ μ n` (the manuscript's (6.5));
  no extra scalar is involved;
* `KanekoZagierSupersingularReduction`: [KZ, Theorem 1] in the source's generality, over the
  source polynomial; `kanekoZagierSupersingularReduction_of_source` derives the manuscript-object
  form `KanekoZagierReductionAtManuscriptPoly` from it.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### Pochhammer / binomial bridges -/

private lemma eval_ascPochhammer_add (x : ℚ) (a b : ℕ) :
    (ascPochhammer ℚ (a + b)).eval x =
      (ascPochhammer ℚ a).eval x * (ascPochhammer ℚ b).eval (x + a) := by
  rw [← ascPochhammer_mul]
  simp [eval_comp]

private lemma choose_mul_factorial (x : ℚ) (k : ℕ) :
    Ring.choose (x + k) k * k.factorial = (ascPochhammer ℚ k).eval (x + 1) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (x + k) k
  rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval,
    add_sub_cancel_right, nsmul_eq_mul] at h
  rw [mul_comm]
  exact h.symm

private lemma eval_ascPochhammer_neg_nat (n i : ℕ) (hi : i ≤ n) :
    (ascPochhammer ℚ i).eval (-(n : ℚ)) * ((n - i).factorial : ℚ) =
      (-1) ^ i * (n.factorial : ℚ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have h := Nat.factorial_mul_descFactorial hi
  have h' : ((n - i).factorial : ℚ) * (n.descFactorial i : ℚ) = n.factorial := by
    exact_mod_cast h
  rw [← h']
  ring

/-- The termwise identity behind the normalization: for `i ≤ n`,
`binom(n+α, n) (-n)_i (n+α+β+1)_i / ((1+α)_i i!) = (-1)^i binom(n+α, n-i) binom(n+α+β+i, i)`. -/
private lemma coeff_identity (α β : ℚ) (n i : ℕ) (hi : i ≤ n)
    (hα : (ascPochhammer ℚ i).eval (1 + α) ≠ 0) :
    Ring.choose ((n : ℚ) + α) n *
        ((ascPochhammer ℚ i).eval (-(n : ℚ)) *
          (ascPochhammer ℚ i).eval (-(n : ℚ) + (2 * n + α + β + 1)) /
          ((ascPochhammer ℚ i).eval (1 + α) * i.factorial)) =
      (-1) ^ i * Ring.choose ((n : ℚ) + α) (n - i) * Ring.choose ((n : ℚ) + α + β + i) i := by
  have hnf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hif : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hnif : ((n - i).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have hA : Ring.choose ((n : ℚ) + α) n * n.factorial =
      (ascPochhammer ℚ n).eval (1 + α) := by
    have := choose_mul_factorial α n
    rw [add_comm (n : ℚ) α, this, add_comm]
  have hB := eval_ascPochhammer_neg_nat n i hi
  have hC : Ring.choose ((n : ℚ) + α + β + i) i * i.factorial =
      (ascPochhammer ℚ i).eval (-(n : ℚ) + (2 * n + α + β + 1)) := by
    have := choose_mul_factorial ((n : ℚ) + α + β) i
    rw [this]
    congr 1
    ring
  have hD : Ring.choose ((n : ℚ) + α) (n - i) * (n - i).factorial =
      (ascPochhammer ℚ (n - i)).eval (1 + α + i) := by
    have := choose_mul_factorial (α + i) (n - i)
    have e : α + i + ((n - i : ℕ) : ℚ) = n + α := by
      rw [Nat.cast_sub hi]; ring
    rw [e] at this
    rw [this]
    congr 1
    ring
  have hE : (ascPochhammer ℚ n).eval (1 + α) =
      (ascPochhammer ℚ i).eval (1 + α) * (ascPochhammer ℚ (n - i)).eval (1 + α + i) := by
    have := eval_ascPochhammer_add (1 + α) i (n - i)
    rwa [Nat.add_sub_cancel' hi] at this
  have hBn : Ring.choose ((n : ℚ) + α) n =
      (ascPochhammer ℚ i).eval (1 + α) * (ascPochhammer ℚ (n - i)).eval (1 + α + i) /
        n.factorial := by
    rw [← hE, ← hA]; field_simp
  have hBd : Ring.choose ((n : ℚ) + α) (n - i) =
      (ascPochhammer ℚ (n - i)).eval (1 + α + i) / (n - i).factorial := by
    rw [← hD]; field_simp
  have hBc : (ascPochhammer ℚ i).eval (-(n : ℚ) + (2 * n + α + β + 1)) =
      Ring.choose ((n : ℚ) + α + β + i) i * i.factorial := hC.symm
  have hBp : (ascPochhammer ℚ i).eval (-(n : ℚ)) =
      (-1) ^ i * n.factorial / (n - i).factorial := by
    rw [← hB]; field_simp
  rw [hBn, hBp, hBc, hBd]
  field_simp

/-- **Normalization lemma.** For `α` such that `(1 + α)_i ≠ 0` for all `i ≤ n`, and any `β`,
`kzSourcePoly (-α) (2n + α + β + 1) n = 1728^n P_n^{(α,β)}(1 - Y/864)`. -/
theorem kzSourcePoly_eq_scaled_jacobi (α β : ℚ) (n : ℕ)
    (hα : ∀ i ≤ n, (ascPochhammer ℚ i).eval (1 + α) ≠ 0) :
    kzSourcePoly (-α) (2 * n + α + β + 1) n =
      C ((1728 : ℚ) ^ n) * (jacobiP α β n).comp (C (-1 / 864) * polyX + C 1) := by
  have hsub : (C (-1 / 864) * polyX + C 1 : ℚ[X]) =
      (1 - 2 * polyX : ℚ[X]).comp (C (1 / 1728) * polyX) := by
    have h1 : (C (-1 / 864 : ℚ) : ℚ[X]) = -(C 2 * C (1 / 1728)) := by
      rw [← C_mul, ← C_neg]; norm_num
    have h2 : (2 : ℚ[X]) = C 2 := (map_ofNat C 2).symm
    rw [h2]
    simp only [sub_comp, one_comp, mul_comp, X_comp, C_comp, h1]
    rw [C_1]
    ring
  rw [hsub, ← comp_assoc, jacobiP_comp_one_sub_two_mul_X, kzSourcePoly, Polynomial.sum_comp,
    mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have key := coeff_identity α β n i hin (hα i hin)
  simp only [mul_comp, C_comp, pow_comp, X_comp, sub_neg_eq_add]
  rw [mul_pow, ← C_pow, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
  congr 2
  rw [one_div_pow]
  linear_combination ((1728 : ℚ) ^ n / 1728 ^ i) * key

/-- **The manuscript's normalization step (§6.4).** For `λ, μ ∈ {-1, 1}`,
`n ≥ 0` and `ℓ = 12n + 6 + 2λ + 3μ`, the source polynomial with `ν₀ = -λ/3`, `ν_∞ = ℓ/6` is
the manuscript's `F̃_{ℓ-1}(Y) = 1728^n P_n^{(λ/3,μ/2)}(1 - Y/864)`: no extra scalar.
(For general `λ` the denominators `(1 + λ/3)_i` may vanish, so the statement is for `λ = ±1`;
the proof does not use `μ`, so the identity holds for every integer `μ`, in particular `μ = ±1`.) -/
theorem kzSourcePoly_eq_kanekoZagierModularPoly {l : ℤ} (hl : l = 1 ∨ l = -1) (μ : ℤ) (n : ℕ) :
    kzSourcePoly (-(l : ℚ) / 3) ((12 * n + 6 + 2 * l + 3 * μ : ℚ) / 6) n =
      kanekoZagierModularPoly l μ n := by
  have hpos : ∀ i ≤ n, (ascPochhammer ℚ i).eval (1 + (l : ℚ) / 3) ≠ 0 := fun i _ =>
    (ascPochhammer_pos i _ (by rcases hl with rfl | rfl <;> norm_num)).ne'
  rw [kanekoZagierModularPoly_eq, ← kzSourcePoly_eq_scaled_jacobi _ ((μ : ℚ) / 2) n hpos]
  congr 1 <;> ring

/-- The same identity in the source's parameters: `δ, ε ∈ {0, 1}`, `ν₀ = (1 - 2δ)/3` and
`ν_∞ = (k + 1)/6` with `k = 12m + 4δ + 6ε`; `λ = 2δ - 1`, `μ = 2ε - 1` (any `ε`). -/
theorem kzSourcePoly_eq_of_source_params {δ : ℕ} (hδ : δ ≤ 1) (ε m : ℕ) :
    kzSourcePoly ((1 - 2 * (δ : ℚ)) / 3) (((12 * m + 4 * δ + 6 * ε : ℕ) + 1 : ℚ) / 6) m =
      kanekoZagierModularPoly (2 * (δ : ℤ) - 1) (2 * (ε : ℤ) - 1) m := by
  have hl : (2 * (δ : ℤ) - 1) = 1 ∨ (2 * (δ : ℤ) - 1) = -1 := by omega
  rw [← kzSourcePoly_eq_kanekoZagierModularPoly hl _ m]
  congr 1 <;> push_cast <;> ring

/-- **The manuscript-object form** of the cited reduction : over `kzReduction ℓ`, the reduction of
`Y^a (Y - 1728)^b F̃_{ℓ-1}` with `F̃_{ℓ-1}` the manuscript's (6.5). Not cited; it is derived from
the source form by `kanekoZagierReductionAtManuscriptPoly_of_source`. -/
@[expose] def KanekoZagierReductionAtManuscriptPoly : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ →
    ∃ s : Finset (AlgebraicClosure (ZMod ℓ)),
      (s : Set (AlgebraicClosure (ZMod ℓ))) = supersingularJ ℓ ∧
        (kzReduction ℓ).map (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))) =
          ∏ j ∈ s, (polyX - C j)

/-- For a prime `ℓ ≥ 5`, `(λ, μ, n)` of `ℓ = 12n + 6 + 2λ + 3μ` is `(2δ - 1, 2ε - 1, ℓ/12)`
with `δ, ε ∈ {0, 1}` and `ℓ - 1 = 12n + 4δ + 6ε`. -/
theorem kzSource_params_of_prime {ℓ : ℕ} (hp : ℓ.Prime) (h5 : 5 ≤ ℓ) :
    ∃ δ ε : ℕ, δ ≤ 1 ∧ ε ≤ 1 ∧ ℓ - 1 = 12 * (ℓ / 12) + 4 * δ + 6 * ε ∧
      kzLambda ℓ = 2 * (δ : ℤ) - 1 ∧ kzMu ℓ = 2 * (ε : ℤ) - 1 := by
  have h2 : ¬ 2 ∣ ℓ := fun h => by
    have := hp.eq_one_or_self_of_dvd 2 h
    omega
  have h3 : ¬ 3 ∣ ℓ := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 h
    omega
  by_cases hA : ℓ % 12 = 5 ∨ ℓ % 12 = 11 <;> by_cases hB : ℓ % 12 = 7 ∨ ℓ % 12 = 11
  · exact ⟨1, 1, le_rfl, le_rfl, by omega, by simp [kzLambda, hA],
      by simp [kzMu, hB]⟩
  · exact ⟨1, 0, le_rfl, by omega, by omega, by simp [kzLambda, hA],
      by simp [kzMu, hB]⟩
  · exact ⟨0, 1, by omega, le_rfl, by omega, by simp [kzLambda, hA],
      by simp [kzMu, hB]⟩
  · exact ⟨0, 0, by omega, by omega, by omega, by simp [kzLambda, hA],
      by simp [kzMu, hB]⟩

/-- **Reduction via the source polynomial.** The source-generality
  `KanekoZagierSupersingularReduction` implies the
manuscript-object form `KanekoZagierReductionAtManuscriptPoly` (over `kzReduction`, i.e. over
`Y^a (Y - 1728)^b F̃_{ℓ-1}` with `F̃_{ℓ-1}` the manuscript's (6.5)), through the proved
normalization identity `kzSourcePoly_eq_of_source_params`. -/
theorem kanekoZagierReductionAtManuscriptPoly_of_source
    (h : KanekoZagierSupersingularReduction) : KanekoZagierReductionAtManuscriptPoly := by
  intro ℓ _ h5
  obtain ⟨δ, ε, hδ, hε, hsub, hδl, hεl⟩ := kzSource_params_of_prime (Fact.out : ℓ.Prime) h5
  obtain ⟨-, s, hs, hred⟩ := h ℓ h5 (ℓ / 12) δ ε (by omega) hε hsub
  refine ⟨s, hs, ?_⟩
  have e3 := kzSourcePoly_eq_of_source_params hδ ε (ℓ / 12)
  have e4 : (((12 * (ℓ / 12) + 4 * δ + 6 * ε : ℕ) + 1 : ℚ)) = (ℓ : ℚ) := by
    have : 12 * (ℓ / 12) + 4 * δ + 6 * ε + 1 = ℓ := by omega
    exact_mod_cast this
  rw [e4] at e3
  rw [← hred, kzReduction, kanekoZagierSupersingularPoly, hδl, hεl, ← e3]
  have e1 : ((2 * (δ : ℤ) - 1 + 1) / 2).toNat = δ := by omega
  have e2 : ((2 * (ε : ℤ) - 1 + 1) / 2).toNat = ε := by omega
  rw [e1, e2]

end ArithmeticOfJacobiPolynomials
