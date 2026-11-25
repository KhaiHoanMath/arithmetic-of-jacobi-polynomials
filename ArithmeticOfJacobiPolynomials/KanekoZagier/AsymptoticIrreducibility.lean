/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.MahlburgOnoArchimedean
public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteCriterion
public import ArithmeticOfJacobiPolynomials.Analysis.Margins

/-!
# Eventual irreducibility from the two uniform resultant bounds (§4.4)

Paragraph after (4.18) of the manuscript: *"The two uniform bounds already imply eventual
irreducibility, since `𝔩 - 𝔲 > 1/4`. ... Thus a proper factorization is impossible once `n` is
sufficiently large, with no restriction on the degree of a possible factor."*

The two uniform bounds are
* (4.2), resultant part (`KanekoZagierArithmeticAsymptotics`,
  `kanekoZagierArithmeticAsymptotics`): for every `ε > 0`, eventually in `n`, uniformly in
  `λ, μ ∈ {-1, 1}`, every factorization `H_n = A B` with `deg A ≤ deg B` has
  `log R^{(6)} ≤ (𝔲 + ε) deg A · n`, with `𝔲 = 43/20 - π/√3`;
* (4.18) (`KanekoZagierArchimedeanAsymptotics`, `kanekoZagierArchimedeanAsymptotics`): for every
  `ε > 0`, eventually in `n`, uniformly in `λ, μ` and the factorization with `1 ≤ k = deg A` and
  `2k ≤ n`, `log R^{(6)} ≥ (𝔩 - ε) k n`, with `𝔩 = log(4 + 3√3) - ½ log 2 - ⅓ log 3 - π/(2√3)`;
* the numerical gap `𝔩 - 𝔲 > 1/4` (`positive_gap`).

Taking `ε = 1/8` for both, a proper factorization `H_n = A B` (both factors of positive degree,
the factor `A` of smaller degree, so `2 deg A ≤ n`) would give `(𝔩 - 1/8) k n ≤ log R^{(6)} ≤
(𝔲 + 1/8) k n`, i.e. `(𝔩 - 𝔲 - 1/4) k n ≤ 0`, contradicting `𝔩 - 𝔲 > 1/4` and `k n > 0`.
No restriction on the degree `k` of the possible factor enters: the two bounds hold for all
`1 ≤ k ≤ n/2` simultaneously.

## Main results

* `irreducible_kzPrimitive_of_uniform_bounds`: the pointwise argument at a fixed `n ≥ 1`: if the
  lower and upper resultant bounds with `ε = 1/8` hold for every factorization of `H_n`, then
  `H_n` is irreducible in `ℤ[X]` (the factors of a primitive polynomial of degree zero are units,
  and the factor of smaller degree has `2 deg A ≤ n`).
* `eventually_irreducible_kzPrimitive`: eventually in `n`, for all four `(λ, μ)`,
  `H_n = kzPrimitive λ μ n` is irreducible in `ℤ[X]`.
* `eventually_irreducible_jacobiShifted`: ... `y_n = P_n^{(λ/3, μ/2)}(1 - 2t)` is irreducible over
  `ℚ` (Gauss's lemma, `H_n = (κ_n / g_n) y_n`).
* `eventually_irreducible_kanekoZagierJacobi`: ... `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`.

The last three depend on the following cited inputs:
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]), `NewtonPolygonRootSlopes` ([Berger, Theorem 2.4],
used for the root valuations of Proposition 4.6) and `BMORPrimeCountingBound`
([BMOR, Corollary 1.7]).
They do not use the explicit cutoff (`kanekoZagier_explicit_cutoff`) nor any finite computation.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Filter

/-- **The pointwise contradiction.** Fix `λ, μ ∈ {-1, 1}` and `n ≥ 1`. Suppose that for every
factorization `H_n = A B` in `ℤ[X]` the resultant satisfies the lower bound (4.18) with `ε = 1/8`
when `1 ≤ deg A` and `2 deg A ≤ n`, and the upper bound (4.2) with `ε = 1/8` when
`deg A ≤ deg B`. Then `H_n = kzPrimitive λ μ n` is irreducible in `ℤ[X]`. -/
theorem irreducible_kzPrimitive_of_uniform_bounds {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n)
    (hlow : ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → 1 ≤ A.natDegree → 2 * A.natDegree ≤ n →
      (Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - 1 / 8) *
          A.natDegree * n ≤ Real.log (primeToSixPart (resultant A B)))
    (hup : ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → A.natDegree ≤ B.natDegree →
      Real.log (primeToSixPart (resultant A B)) ≤
        (43 / 20 - Real.pi / √3 + 1 / 8) * A.natDegree * n) :
    Irreducible (kzPrimitive l μ n) := by
  have hprim := isPrimitive_kzPrimitive hl hμ n
  have hdeg := natDegree_kzPrimitive hl hμ n
  have hs3 : √3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hgap := positive_gap
  -- `𝔩 - 𝔲` in the form of `positive_gap`
  have hπ : Real.pi / √3 = 2 * (Real.pi / (2 * √3)) := by
    field_simp
  refine irreducible_iff.mpr ⟨fun hu => ?_, ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    omega
  intro A B hAB
  by_contra hnot
  obtain ⟨hA, hB⟩ := not_or.mp hnot
  have hApr : A.IsPrimitive := isPrimitive_of_dvd hprim ⟨B, hAB⟩
  have hBpr : B.IsPrimitive := isPrimitive_of_dvd hprim ⟨A, by rw [hAB, mul_comm]⟩
  have hA1 : 1 ≤ A.natDegree := by
    by_contra h
    exact hA (isUnit_of_isPrimitive_of_natDegree_eq_zero hApr (by omega))
  have hB1 : 1 ≤ B.natDegree := by
    by_contra h
    exact hB (isUnit_of_isPrimitive_of_natDegree_eq_zero hBpr (by omega))
  have hsum : A.natDegree + B.natDegree = n := by
    rw [← hdeg, hAB, natDegree_mul hApr.ne_zero hBpr.ne_zero]
  -- the factor of smaller degree gives the contradiction
  have key : ∀ F G : ℤ[X], kzPrimitive l μ n = F * G → 1 ≤ F.natDegree →
      F.natDegree ≤ G.natDegree → 2 * F.natDegree ≤ n → False := by
    intro F G hFG hF1 hFG' hF2
    have h1 := hlow F G hFG hF1 hF2
    have h2 := hup F G hFG hFG'
    have hk : (0 : ℝ) < (F.natDegree : ℝ) * n := by
      have : (0 : ℝ) < F.natDegree := by exact_mod_cast hF1
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have h3 := h1.trans h2
    have h4 : (Real.log (4 + 3 * √3) - 1 / 2 * Real.log 2 - 1 / 3 * Real.log 3 - 43 / 20 +
        Real.pi / (2 * √3) - 1 / 4) * ((F.natDegree : ℝ) * n) ≤ 0 := by
      have e : (Real.log (4 + 3 * √3) - 1 / 2 * Real.log 2 - 1 / 3 * Real.log 3 - 43 / 20 +
          Real.pi / (2 * √3) - 1 / 4) * ((F.natDegree : ℝ) * n) =
          (Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - 1 / 8) *
              F.natDegree * n -
            (43 / 20 - Real.pi / √3 + 1 / 8) * F.natDegree * n := by
        rw [hπ]; ring
      rw [e]
      exact sub_nonpos.mpr h3
    have h5 : 0 < (Real.log (4 + 3 * √3) - 1 / 2 * Real.log 2 - 1 / 3 * Real.log 3 - 43 / 20 +
        Real.pi / (2 * √3) - 1 / 4) * ((F.natDegree : ℝ) * n) :=
      mul_pos (by linarith) hk
    linarith
  rcases le_total A.natDegree B.natDegree with hle | hle
  · exact key A B hAB hA1 hle (by omega)
  · exact key B A (by rw [hAB, mul_comm]) hB1 hle (by omega)

/-- **Eventual irreducibility of `H_n` in `ℤ[X]`** from the two uniform resultant bounds (4.2)
and (4.18) and the gap `𝔩 - 𝔲 > 1/4`: there is `N` such that for every `n ≥ N` and every
`λ, μ ∈ {-1, 1}`, `H_n = kzPrimitive λ μ n` is irreducible. There is no restriction on the
degree of a possible factor. Conditional on `JacobiSimpleRealZeros`, `NewtonPolygonRootSlopes`
and `BMORPrimeCountingBound`. -/
theorem eventually_irreducible_kzPrimitive (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes)
    (hBMOR : BMORPrimeCountingBound) :
    ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
      Irreducible (kzPrimitive l μ n) := by
  have hlow := (kanekoZagierArchimedeanAsymptotics_iff.mp
    (kanekoZagierArchimedeanAsymptotics hZ hNP hBMOR)) (1 / 8) (by norm_num)
  have hup := (kanekoZagierArithmeticAsymptotics_iff.mp
    (kanekoZagierArithmeticAsymptotics hBMOR)) (1 / 8) (by norm_num)
  filter_upwards [hlow, hup, eventually_ge_atTop 1] with n h1 h2 hn l μ hl hμ
  exact irreducible_kzPrimitive_of_uniform_bounds hl hμ hn (h1 l μ hl hμ)
    (fun A B hAB hle => ((h2 l μ hl hμ).2 A B hAB hle))

/-- **Eventual irreducibility of `y_n = P_n^{(λ/3, μ/2)}(1 - 2t)` over `ℚ`**, via Gauss's lemma
and `H_n = (κ_n / g_n) y_n`. -/
theorem eventually_irreducible_jacobiShifted (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes)
    (hBMOR : BMORPrimeCountingBound) :
    ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
      Irreducible (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) := by
  filter_upwards [eventually_irreducible_kzPrimitive hZ hNP hBMOR] with n h l μ hl hμ
  have hκ : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hg : (kzContent l μ n : ℚ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have hc : (kzKappa n : ℚ) / kzContent l μ n ≠ 0 := div_ne_zero hκ hg
  have hmap := map_kzPrimitive hl hμ n
  have hprim := isPrimitive_kzPrimitive hl hμ n
  rw [← irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit hc)), ← hmap,
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim]
  exact h l μ hl hμ

/-- **Eventual irreducibility of `P_n^{(λ/3, μ/2)}` over `ℚ`** for all four `(λ, μ)`, with no
restriction on the degree of a possible factor, from the two uniform resultant bounds and the
gap `𝔩 - 𝔲 > 1/4`. Conditional on `JacobiSimpleRealZeros`, `NewtonPolygonRootSlopes` and
`BMORPrimeCountingBound`. -/
theorem eventually_irreducible_kanekoZagierJacobi (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes)
    (hBMOR : BMORPrimeCountingBound) :
    ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
      Irreducible (kanekoZagierJacobi l μ n) := by
  filter_upwards [eventually_irreducible_jacobiShifted hZ hNP hBMOR] with n h l μ hl hμ
  exact (irreducible_kanekoZagierJacobi_iff_jacobiShifted l μ n).mpr (h l μ hl hμ)

end ArithmeticOfJacobiPolynomials
