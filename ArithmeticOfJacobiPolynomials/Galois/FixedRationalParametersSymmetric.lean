/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersDerivatives
public import ArithmeticOfJacobiPolynomials.External

/-!
# Corollary 5.15: symmetric Jacobi families

Fix `a ∈ ℚ` with `a > -1` whose reduced denominator `v` is odd or divisible by `4`, and
`δ ∈ {0,1}`. Let `Q_m^{a,δ}` be defined by `P_{2m+δ}^{(a,a)}(X)/X^δ = Q_m^{a,δ}(X²)` (here
`contract 2 (P_{2m+δ}^{(a,a)} /ₘ X^δ)`). For all large `m`, irreducibility of `Q_m^{a,δ}` implies
`Gal(Q_m^{a,δ}/ℚ) = S_m` and `Gal(P_{2m+δ}^{(a,a)}/X^δ / ℚ) = C_2 ≀ S_m`
(`symmetricJacobi`, Corollary 5.15).

Following the manuscript: the quadratic transformations [DLMF, 18.7.13–18.7.14] and Jacobi
symmetry identify `P_{2m+δ}^{(a,a)}/X^δ` with a nonzero multiple of `P_m^{(δ-1/2,a)}(1 - 2X²)`
(`divByMonic_eq_jacobiP_comp`); the parameters `(δ - 1/2, a)` satisfy the denominator condition
(`denomCond_symmetric`), and Theorem 1.6 with `c = -2` gives the groups
(`symmetricJacobi_core`).

The prose after the corollary (no irreducibility assumption: `Q_m^{a,δ}` has a unique monic
irreducible factor of degree `> m/2`, of degree `m - O(m/(log m)^A)` and symmetric group, and its
substitution `T = X²` is irreducible of twice the degree with full wreath group) is
`symmetricJacobi_dominant`: the same Theorem 1.6 data with the affine change `T ↦ 1 - 2T`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Filter

namespace FixedRationalParameters

/-! ### The denominator condition for `(δ - 1/2, a)` -/

theorem natCoprime_of_isCoprime {x y : ℤ} (h : IsCoprime x y) : Nat.Coprime x.natAbs y.natAbs :=
  Nat.coprime_iff_gcd_eq_one.mpr (by
    rw [← Int.gcd_eq_natAbs]; exact Int.isCoprime_iff_gcd_eq_one.mp h)

/-- For `a > -1` with reduced denominator odd or divisible by `4`, the parameters
`(δ - 1/2, a)` satisfy the denominator condition of Theorem 1.6: the reduced denominator of
`δ - 1/2 + a` is `2v` or `v`, even and at least `max{2, v}`. -/
theorem denomCond_symmetric {a : ℚ} (ha : -1 < a) (hv : Odd a.den ∨ 4 ∣ a.den) (δ : ℕ) :
    DenomCond ((δ : ℚ) - 1 / 2) a := by
  have hred : IsCoprime a.num (a.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact gcd_num_den a
  have hv0 : (0 : ℤ) < a.den := by exact_mod_cast a.den_pos
  have hvQ : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hodd2 : ∀ k : ℕ, Nat.Coprime (2 * (k : ℤ) - 1).natAbs (2 : ℤ).natAbs := by
    intro k
    rw [show (2 : ℤ).natAbs = 2 from rfl, Nat.coprime_two_right, Int.natAbs_odd]
    exact ⟨k - 1, by ring⟩
  have e1 : ((δ : ℚ) - 1 / 2) = ((2 * (δ : ℤ) - 1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
    push_cast; ring
  have hd1 : (((δ : ℚ) - 1 / 2).den : ℤ) = 2 := by
    rw [e1]; exact Rat.den_div_eq_of_coprime (by norm_num) (hodd2 δ)
  have hd1' : ((δ : ℚ) - 1 / 2).den = 2 := by exact_mod_cast hd1
  -- the denominator of the sum: even and at least `max{2, v}`
  have hsum : Even ((δ : ℚ) - 1 / 2 + a).den ∧ 2 ≤ ((δ : ℚ) - 1 / 2 + a).den ∧
      a.den ≤ ((δ : ℚ) - 1 / 2 + a).den := by
    rcases hv with hvo | ⟨w, hw⟩
    · -- `v` odd: the denominator is `2v`
      have hcop2 : IsCoprime (2 * (δ : ℤ) * a.den - a.den + 2 * a.num) 2 := by
        obtain ⟨j, hj⟩ := hvo
        refine ⟨1, -((δ : ℤ) * a.den - j - 1 + a.num), ?_⟩
        have hj' : (a.den : ℤ) = 2 * j + 1 := by exact_mod_cast hj
        rw [hj']; ring
      have h2v : IsCoprime (2 : ℤ) (a.den : ℤ) := by
        obtain ⟨j, hj⟩ := hvo
        have hj' : (a.den : ℤ) = 2 * j + 1 := by exact_mod_cast hj
        exact ⟨-j, 1, by rw [hj']; ring⟩
      have hcopv : IsCoprime (2 * (δ : ℤ) * a.den - a.den + 2 * a.num) (a.den : ℤ) := by
        have := (h2v.mul_left hred).add_mul_left_left (2 * (δ : ℤ) - 1)
        convert this using 1; ring
      have hcop := hcop2.mul_right hcopv
      have e : (δ : ℚ) - 1 / 2 + a = ((2 * (δ : ℤ) * a.den - a.den + 2 * a.num : ℤ) : ℚ) /
          ((2 * (a.den : ℤ) : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den a]
        push_cast
        field_simp
      have hd : (((δ : ℚ) - 1 / 2 + a).den : ℤ) = 2 * a.den := by
        rw [e]; exact Rat.den_div_eq_of_coprime (by omega) (natCoprime_of_isCoprime hcop)
      have hd' : ((δ : ℚ) - 1 / 2 + a).den = 2 * a.den := by exact_mod_cast hd
      have := a.den_pos
      rw [hd']
      exact ⟨even_two_mul _, by omega, by omega⟩
    · -- `v = 4w`: the denominator is `v`
      have hwZ : (a.den : ℤ) = 4 * w := by exact_mod_cast hw
      have hw0 : (0 : ℤ) < w := by omega
      have hbodd : Odd a.num := by
        rw [← Int.not_even_iff_odd]
        intro hb
        have h2b : (2 : ℤ) ∣ a.num := even_iff_two_dvd.mp hb
        have h2v : (2 : ℤ) ∣ (a.den : ℤ) := ⟨2 * w, by rw [hwZ]; ring⟩
        have := Int.dvd_gcd (c := 2) h2b h2v
        rw [gcd_num_den a] at this
        omega
      have hcop2 : IsCoprime (4 * (δ : ℤ) * w - 2 * w + a.num) 2 := by
        obtain ⟨j, hj⟩ := hbodd
        exact ⟨1, -(2 * (δ : ℤ) * w - w + j), by rw [hj]; ring⟩
      have hredw : IsCoprime a.num (w : ℤ) := by
        rw [hwZ] at hred
        exact hred.of_mul_right_right
      have hcopw : IsCoprime (4 * (δ : ℤ) * w - 2 * w + a.num) (w : ℤ) := by
        have := hredw.add_mul_left_left (4 * (δ : ℤ) - 2)
        convert this using 1; ring
      have hcop : IsCoprime (4 * (δ : ℤ) * w - 2 * w + a.num) (2 * 2 * (w : ℤ)) :=
        (hcop2.mul_right hcop2).mul_right hcopw
      have e : (δ : ℚ) - 1 / 2 + a = ((4 * (δ : ℤ) * w - 2 * w + a.num : ℤ) : ℚ) /
          ((2 * 2 * (w : ℤ) : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den a]
        have hw' : (a.den : ℚ) = 4 * w := by exact_mod_cast hw
        rw [hw']
        have hwQ : (w : ℚ) ≠ 0 := by exact_mod_cast (show w ≠ 0 by omega)
        push_cast
        field_simp
        try ring
      have hd : (((δ : ℚ) - 1 / 2 + a).den : ℤ) = 2 * 2 * w := by
        rw [e]; exact Rat.den_div_eq_of_coprime (by omega) (natCoprime_of_isCoprime hcop)
      have hd' : ((δ : ℚ) - 1 / 2 + a).den = 4 * w := by
        have : ((((δ : ℚ) - 1 / 2 + a).den : ℕ) : ℤ) = ((4 * w : ℕ) : ℤ) := by
          rw [hd]; push_cast; ring
        exact_mod_cast this
      rw [hd', ← hw]
      refine ⟨⟨2 * w, by rw [hw]; ring⟩, by omega, le_rfl⟩
  obtain ⟨hev, h2, hvle⟩ := hsum
  refine (denomCond_iff _ _).mpr ⟨hev, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hd1']
    exact max_le h2 hvle
  · have h2' : ((2 * (δ : ℤ) - 1 : ℤ) : ℚ) = ((-(2 * (k : ℤ)) - 2 : ℤ) : ℚ) := by
      push_cast; linarith
    have h3 : 2 * (δ : ℤ) - 1 = -(2 * (k : ℤ)) - 2 := by exact_mod_cast h2'
    omega
  · have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith

/-! ### The core argument -/

open Classical in
/-- **Corollary 5.15, core.** Let `(α, β)` satisfy the denominator condition. For all large `m`,
whenever `F = s · P_m^{(α,β)}(1 - 2X²)` and `Q = s · P_m^{(α,β)}(1 - 2T)` with `s ≠ 0` and `Q`
irreducible, `Gal(Q/ℚ) = S_m` and `Gal(F/ℚ) = W_m`.

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2]
and [Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `h619`, `hBT`, `hJones`. -/
theorem symmetricJacobi_core (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {α β : ℚ} (hcond : DenomCond α β) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ F Q : ℚ[X], ∀ s : ℚ, s ≠ 0 →
      F = C s * (jacobiP α β m).comp (1 + C (-2) * polyX ^ 2) →
      Q = C s * (jacobiP α β m).comp (C (-2) * polyX + C 1) → Irreducible Q →
      GaloisGroupIsSymmetric Q ∧ GaloisGroupIsWreath F := by
  obtain ⟨hD2, hr, -⟩ := denomCond_facts hcond
  have hgr := gcd_num_two_den hcond
  have hDpos := (α + β).den_pos
  have hc : (-2 : ℚ) ≠ 0 := by norm_num
  obtain ⟨Nu, hNu⟩ := exists_unique_isDominant_jacobiP h619 hcond
  obtain ⟨N₀, hN₀⟩ := galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond
  obtain ⟨C₀, N₁, hN₁⟩ := natDegree_isDominant_jacobiP h619 hcond 1 one_pos
  have evo := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgr
  have ev3 := eventually_le_log_natCast (10 * |C₀| + 1)
  have ev4 := eventually_ge_atTop
    (Nu + N₀ + N₁ + 100 * ((α + β).num.natAbs + 1) + (-2 : ℚ).num.natAbs + (-2 : ℚ).den + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (evo.and (ev3.and ev4))
  refine ⟨N, fun n hn F Q s hs hF hQ hQirr => ?_⟩
  obtain ⟨⟨po, hpo, ho1, ho2, ho3, ho4⟩, hL, hn'⟩ := hN n hn
  have hdeg := natDegree_jacobiP_le α β n
  obtain ⟨ho3', hodd⟩ := modEq_and_odd_of_modEq (n := n) hDpos ho4
  have hnDn : n ≤ (α + β).den * n := Nat.le_mul_of_pos_left n hDpos
  -- the dominant factor is everything
  obtain ⟨σ, hσ, -⟩ := exists_isCycle_of_eligible hcond hpo ho1 ho2 ho3'
  have hf0 := ne_zero_of_isCycle hσ
  obtain ⟨h, hh, -⟩ := hNu n (by omega)
  have hhd := (isDominant_iff _ _).mp hh
  obtain ⟨g, κ, hg, hfac⟩ := exists_monic_cofactor hf0 hhd.2.2.1
  obtain ⟨hS, -⟩ := hN₀ n (by omega) h g κ hh hg hfac
  have hκ : κ ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hfac, C_0, zero_mul, zero_mul])
  have hsκ : s * κ ≠ 0 := mul_ne_zero hs hκ
  have hQhg : Q = C (s * κ) * h.comp (C (-2) * polyX + C 1) * g.comp (C (-2) * polyX + C 1) := by
    rw [hQ, hfac, mul_comp, mul_comp, C_comp, C_mul]
    ring
  have hg1 : g = 1 := by
    rcases hQirr.isUnit_or_isUnit hQhg with hu | hu
    · exfalso
      have h0 := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_C_mul hsκ, natDegree_comp, natDegree_linear hc] at h0
      have := hhd.2.1.natDegree_pos
      omega
    · have h0 := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_comp, natDegree_linear hc] at h0
      exact hg.natDegree_eq_zero.mp (by omega)
  have hfac1 : jacobiP α β n = C κ * h := by rw [hfac, hg1, mul_one]
  have hFh : F = C (s * κ) * h.comp (1 + C (-2) * polyX ^ 2) := by
    rw [hF, hfac1, mul_comp, C_comp, C_mul]
    ring
  have hQh : Q = C (s * κ) * h.comp (C (-2) * polyX + C 1) := by
    rw [hQhg, hg1, one_comp, mul_one]
  -- bounds
  have hbo := cycleLength_bounds hDpos (cycleBound_bounds α β).1 ho1 ho2 ho3'
  have hnr : 100 * (|(α + β).num| + 1) ≤ (n : ℤ) := by
    have h0 : ((α + β).num.natAbs : ℤ) = |(α + β).num| := Int.natCast_natAbs _
    have h1 : 100 * ((α + β).num.natAbs + 1) ≤ n := by omega
    have h2 : (100 * (((α + β).num.natAbs : ℤ) + 1) : ℤ) ≤ n := by exact_mod_cast h1
    rw [← h0]
    exact h2
  have huo := cycleLength_le_of_upper hDpos ho3 ho3' hnr
  have hM := hN₁ n (by omega) h hh
  rw [Real.rpow_one] at hM
  have hn100 : (100 : ℝ) ≤ n := by
    have : 100 ≤ n := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log n := by linarith [abs_nonneg C₀]
  have hCn : C₀ * n / Real.log n ≤ 0.1 * n := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n)
      (by linarith [le_abs_self C₀] : (0 : ℝ) ≤ Real.log n - 10 * C₀)]
  have hM9 : 0.9 * (n : ℝ) ≤ h.natDegree := by linarith
  -- the odd quadratic cycle
  have hcp : padicValRat po (-2) = 0 :=
    padicValRat_eq_zero_of_lt hpo hc (by omega) (by omega)
  obtain ⟨σo, hσo, hσoc⟩ := exists_isCycle_comp_of_eligible hcond hpo ho1 ho2 ho3' hc hcp
  generalize hdo : 2 * (n : ℤ) + 1 - ((po : ℤ) - (α + β).num) / (α + β).den = do_ at *
  have hdo0 : 0 ≤ do_ := by omega
  lift do_ to ℕ using hdo0
  have huo' : (100 : ℝ) * do_ ≤ 61 * n := by exact_mod_cast huo
  have hdoM : do_ < h.natDegree := by
    have : (do_ : ℝ) < h.natDegree := by linarith
    exact_mod_cast this
  have hodd' : Odd do_ := (Int.odd_coe_nat _).mp hodd
  have hσoc' : (galPerm _ σo).support.card = 2 * do_ := by exact_mod_cast hσoc
  have hP0 := ne_zero_of_isCycle hσo
  have hFP : F ∣ (jacobiP α β n).comp (1 + C (-2) * polyX ^ 2) := by
    refine ⟨C s⁻¹, ?_⟩
    rw [hF, mul_comm (C s * _), ← mul_assoc, ← C_mul, inv_mul_cancel₀ hs, C_1, one_mul]
  have := fact_splits_of_dvd hP0 hFP
  obtain ⟨hτo, hτoc, -⟩ := galPerm_restrict_isCycle hP0 hFP hσo (fun z _ => by
    rw [hF, aeval_mul, (mem_rootSet.mp z.2).2, mul_zero])
  obtain ⟨hW, -⟩ := galoisGroupIsWreath_C_mul_comp hhd.2.1 hS hc hsκ hFh
    (eval_one_ne_zero_of_dvd ((denomCond_iff _ _).mp hcond).2.2.1 hhd.2.2.1) hτo
    (hτoc.trans hσoc') hodd' hdoM
  refine ⟨?_, hW⟩
  rw [hQh]
  exact GaloisGroupIsSymmetric.affine h 1 hsκ hc hS

/-! ### The quadratic transformations -/

theorem comp_two_mul_X_sq_sub_one (α β : ℚ) (m : ℕ) :
    (jacobiP α β m).comp (2 * polyX ^ 2 - 1) =
      C ((-1 : ℚ) ^ m) * (jacobiP β α m).comp (1 + C (-2) * polyX ^ 2) := by
  have e1 : (1 - 2 * polyX ^ 2 : ℚ[X]) = 1 + C (-2) * polyX ^ 2 := by
    rw [map_neg, map_ofNat]; ring
  rw [show (2 * polyX ^ 2 - 1 : ℚ[X]) = (-polyX).comp (1 - 2 * polyX ^ 2) by simp, ← comp_assoc,
    jacobiP_comp_neg_X, mul_comp, C_comp, e1]

/-- `P_{2m+δ}^{(a,a)}/X^δ = s · P_m^{(δ-1/2, a)}(1 - 2X²)` with `s ≠ 0`
([DLMF, 18.7.13–18.7.14] and Jacobi symmetry). -/
theorem divByMonic_eq_jacobiP_comp (hT : JacobiQuadraticTransformation) {a : ℚ} (ha : -1 < a)
    (m δ : ℕ) (hδ : δ ≤ 1) :
    ∃ s : ℚ, s ≠ 0 ∧ jacobiP a a (2 * m + δ) /ₘ polyX ^ δ =
      C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp (1 + C (-2) * polyX ^ 2) := by
  have hα : ∀ k : ℕ, a ≠ -((k : ℚ) + 1) := by
    intro k hk
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨h0, h1⟩ := hT.rat a ha m
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with rfl | rfl
  · have he : (jacobiP a (-1 / 2) m).eval 1 ≠ 0 := by
      rw [jacobiP_eval_one]; exact ring_choose_add_ne_zero hα m
    have hE : (jacobiP a a (2 * m)).eval 1 ≠ 0 := by
      rw [jacobiP_eval_one]; exact ring_choose_add_ne_zero hα (2 * m)
    refine ⟨((jacobiP a (-1 / 2) m).eval 1)⁻¹ * ((jacobiP a a (2 * m)).eval 1 * (-1) ^ m),
      mul_ne_zero (inv_ne_zero he) (mul_ne_zero hE (pow_ne_zero _ (by norm_num))), ?_⟩
    rw [Nat.add_zero, pow_zero, divByMonic_one, Nat.cast_zero, zero_sub,
      show (-(1 / 2) : ℚ) = -1 / 2 by ring]
    apply mul_left_cancel₀ (C_ne_zero.mpr he)
    rw [h0, comp_two_mul_X_sq_sub_one, C_mul, C_mul]
    have hinv : C ((jacobiP a (-1 / 2) m).eval 1) * C ((jacobiP a (-1 / 2) m).eval 1)⁻¹ =
        (1 : ℚ[X]) := by
      rw [← C_mul, mul_inv_cancel₀ he, C_1]
    linear_combination (-(C ((jacobiP a a (2 * m)).eval 1) * C ((-1 : ℚ) ^ m) *
      (jacobiP (-1 / 2) a m).comp (1 + C (-2) * polyX ^ 2))) * hinv
  · have he : (jacobiP a (1 / 2) m).eval 1 ≠ 0 := by
      rw [jacobiP_eval_one]; exact ring_choose_add_ne_zero hα m
    have hE : (jacobiP a a (2 * m + 1)).eval 1 ≠ 0 := by
      rw [jacobiP_eval_one]; exact ring_choose_add_ne_zero hα (2 * m + 1)
    refine ⟨((jacobiP a (1 / 2) m).eval 1)⁻¹ * ((jacobiP a a (2 * m + 1)).eval 1 * (-1) ^ m),
      mul_ne_zero (inv_ne_zero he) (mul_ne_zero hE (pow_ne_zero _ (by norm_num))), ?_⟩
    rw [pow_one, Nat.cast_one, show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num]
    have hP : jacobiP a a (2 * m + 1) = polyX * (C (((jacobiP a (1 / 2) m).eval 1)⁻¹ *
        ((jacobiP a a (2 * m + 1)).eval 1 * (-1) ^ m)) *
          (jacobiP (1 / 2) a m).comp (1 + C (-2) * polyX ^ 2)) := by
      apply mul_left_cancel₀ (C_ne_zero.mpr he)
      rw [h1, comp_two_mul_X_sq_sub_one, C_mul, C_mul]
      have hinv : C ((jacobiP a (1 / 2) m).eval 1) * C ((jacobiP a (1 / 2) m).eval 1)⁻¹ =
          (1 : ℚ[X]) := by
        rw [← C_mul, mul_inv_cancel₀ he, C_1]
      linear_combination (-(polyX * C ((jacobiP a a (2 * m + 1)).eval 1) * C ((-1 : ℚ) ^ m) *
        (jacobiP (1 / 2) a m).comp (1 + C (-2) * polyX ^ 2))) * hinv
    conv_lhs => rw [hP, mul_divByMonic_cancel_left _ monic_X]

/-! ### Corollary 5.15 -/

/-- **Corollary 5.15**. Fix `a ∈ ℚ` with `a > -1` whose reduced
denominator is odd or divisible by `4`, and `δ ∈ {0,1}`. For all large `m`, if
`Q_m^{a,δ} = contract 2 (P_{2m+δ}^{(a,a)}/X^δ)` (so `P_{2m+δ}^{(a,a)}(X)/X^δ = Q_m^{a,δ}(X²)`) is
irreducible, then `Gal(Q_m^{a,δ}/ℚ) = S_m` and `Gal(P_{2m+δ}^{(a,a)}/X^δ / ℚ) = C_2 ≀ S_m`.

Conditional on [DLMF, 18.7.13–18.7.14] (`hT`), [BMOR, Corollary 1.7], [BMOR, Proposition 6.19],
Brun–Titchmarsh [MV, Theorem 2] and [Jones, Corollary 1.3] (`hBMOR`, `h619`, `hBT`, `hJones`,
through Theorem 1.6). -/
theorem symmetricJacobi (hT : JacobiQuadraticTransformation) (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {a : ℚ} (ha : -1 < a) (hv : Odd a.den ∨ 4 ∣ a.den)
    {δ : ℕ} (hδ : δ ≤ 1) :
    ∃ N : ℕ, ∀ m ≥ N, Irreducible (contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ)) →
      GaloisGroupIsSymmetric (contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ)) ∧
      GaloisGroupIsWreath (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) := by
  obtain ⟨N, hN⟩ := symmetricJacobi_core hBMOR h619 hBT hJones (denomCond_symmetric ha hv δ)
  refine ⟨N, fun m hm hirr => ?_⟩
  obtain ⟨s, hs, hP⟩ := divByMonic_eq_jacobiP_comp hT ha m δ hδ
  have hL : (C (-2) * polyX + C 1 : ℚ[X]).comp (polyX ^ 2) = 1 + C (-2) * polyX ^ 2 := by
    simp only [add_comp, mul_comp, C_comp, X_comp, C_1, one_comp]
    ring
  have hQ : contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) =
      C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp (C (-2) * polyX + C 1) := by
    rw [hP, show C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp (1 + C (-2) * polyX ^ 2) =
      expand ℚ 2 (C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp (C (-2) * polyX + C 1)) by
        rw [map_mul, expand_C, expand_eq_comp_X_pow, comp_assoc, hL]]
    exact contract_expand 2 two_ne_zero
  exact hN m hm _ _ s hs hP hQ hirr

/-! ### The dominant factor of `Q_m^{a,δ}` -/

open Classical in
/-- `Gal = W_n` is invariant under multiplication by a nonzero constant. -/
theorem GaloisGroupIsWreath.C_mul {f : ℚ[X]} {u : ℚ} (hu : u ≠ 0) (hf : GaloisGroupIsWreath f) :
    GaloisGroupIsWreath (C u * f) := by
  have key : GaloisGroupIsWreath (C u * f.comp (C 1 * polyX + C 0)) := by
    have := fact_splits_affine (a := u) (b := (1 : ℚ)) f 0
    set g := C u * f.comp (C 1 * polyX + C 0) with hg
    set ψ := Gal.rootsEquivRootsAux g f.SplittingField with hψ
    set A := affineRootsEquiv f 0 hu one_ne_zero f.SplittingField with hA
    set e := A.trans ψ.symm with he
    set φ := IsScalarTower.toAlgHom ℚ g.SplittingField f.SplittingField with hφ
    have hφinj : Function.Injective φ := φ.toRingHom.injective
    have hco : ∀ x : f.rootSet f.SplittingField,
        φ ((e x : g.rootSet g.SplittingField) : g.SplittingField) = (x : f.SplittingField) := by
      intro x
      have h1 : ((ψ (e x) : g.rootSet f.SplittingField) : f.SplittingField) =
          φ ((e x : g.rootSet g.SplittingField) : g.SplittingField) := rfl
      rw [← h1, he, Equiv.trans_apply, Equiv.apply_symm_apply, hA, coe_affineRootsEquiv]
      simp
    have hneg : ∀ x y : f.rootSet f.SplittingField,
        (y : f.SplittingField) = -(x : f.SplittingField) ↔
          ((e y : g.rootSet g.SplittingField) : g.SplittingField) =
            -((e x : g.rootSet g.SplittingField) : g.SplittingField) := by
      intro x y
      constructor
      · intro h
        apply hφinj
        rw [map_neg, hco, hco]
        exact h
      · intro h
        have h' := congrArg φ h
        rw [map_neg, hco, hco] at h'
        exact h'
    rw [galoisGroupIsWreath_iff] at hf ⊢
    refine le_antisymm (range_galPerm_le_negCommPerm g) ?_
    intro π hπ
    have hπ' : e.symm.permCongr π ∈ negCommPerm (f.rootSet f.SplittingField) := by
      rw [mem_negCommPerm_iff] at hπ ⊢
      intro x y
      rw [hneg x y, hneg (e.symm.permCongr π x) (e.symm.permCongr π y)]
      simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      exact hπ (e x) (e y)
    rw [← hf] at hπ'
    obtain ⟨σ, hσ⟩ := hπ'
    refine ⟨Gal.restrict g f.SplittingField σ, ?_⟩
    rw [galPerm_restrict_affine f 0 hu one_ne_zero σ, hσ]
    change e.permCongr (e.symm.permCongr π) = π
    rw [← Equiv.permCongr_symm]
    exact Equiv.apply_symm_apply _ _
  have e : C u * f.comp (C 1 * polyX + C 0) = C u * f := by simp
  rwa [e] at key

open Classical in
/-- **The unconditional dominant-factor sentence following Corollary 5.15.**
Fix `a ∈ ℚ` with `a > -1` whose reduced denominator is odd or divisible by `4`, `δ ∈ {0,1}`, and
`A > 0`. For all large `m`, `Q_m^{a,δ} = contract 2 (P_{2m+δ}^{(a,a)}/X^δ)` (with no
irreducibility assumption) has a unique monic irreducible factor `q` of degree greater than `m/2`,
with `m - deg q ≤ C m/(log m)^A`; `Gal(q/ℚ)` is symmetric, and `q(X²)` is irreducible of degree
`2 deg q` with full quadratic wreath-product group.

Conditional on the same hypotheses as `symmetricJacobi`: the dominant factor is the monic
normalization of `h(1 - 2T)` for the dominant factor `h` of `P_m^{(δ-1/2,a)}` of Theorem 1.6
with `c = -2`. -/
theorem symmetricJacobi_dominant (hT : JacobiQuadraticTransformation)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) {a : ℚ} (ha : -1 < a)
    (hv : Odd a.den ∨ 4 ∣ a.den) {δ : ℕ} (hδ : δ ≤ 1) :
    ∀ A : ℝ, 0 < A → ∃ (Cst : ℝ) (N : ℕ), ∀ m ≥ N, ∃ q : ℚ[X],
      (q.Monic ∧ Irreducible q ∧
        q ∣ contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) ∧ m < 2 * q.natDegree) ∧
      (∀ q' : ℚ[X], q'.Monic → Irreducible q' →
        q' ∣ contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) → m < 2 * q'.natDegree →
          q' = q) ∧
      ((m : ℝ) - q.natDegree ≤ Cst * m / Real.log m ^ A) ∧
      GaloisGroupIsSymmetric q ∧ Irreducible (q.comp (polyX ^ 2)) ∧
      (q.comp (polyX ^ 2)).natDegree = 2 * q.natDegree ∧
      GaloisGroupIsWreath (q.comp (polyX ^ 2)) := by
  intro A hA
  have hcond := denomCond_symmetric ha hv δ
  have hc : (-2 : ℚ) ≠ 0 := by norm_num
  obtain ⟨Nu, hNu⟩ := exists_unique_isDominant_jacobiP h619 hcond
  obtain ⟨N₀, hN₀⟩ := galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond
  obtain ⟨Cst, N₁, hN₁⟩ := natDegree_isDominant_jacobiP h619 hcond A hA
  obtain ⟨C₀, N₂, hN₂⟩ := natDegree_isDominant_jacobiP h619 hcond 1 one_pos
  obtain ⟨N₃, hN₃⟩ := quadratic_isDominant_jacobiP hBMOR h619 hBT hJones hcond hc
  have ev3 := eventually_le_log_natCast (10 * |C₀| + 1)
  have ev4 := eventually_ge_atTop (Nu + N₀ + N₁ + N₂ + N₃ + 100)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ev3.and ev4)
  refine ⟨Cst, N, fun m hm => ?_⟩
  obtain ⟨hL, hm'⟩ := hN m hm
  have hα : ∀ k : ℕ, ((δ : ℚ) - 1 / 2) ≠ -((k : ℚ) + 1) := by
    intro k hk
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have : (0 : ℚ) ≤ δ := Nat.cast_nonneg δ
    linarith
  have hP0 : jacobiP ((δ : ℚ) - 1 / 2) a m ≠ 0 := by
    intro h0
    have he := ring_choose_add_ne_zero hα m
    rw [← jacobiP_eval_one, h0, eval_zero] at he
    exact he rfl
  obtain ⟨h, hh, -⟩ := hNu m (by omega)
  have hhd := (isDominant_iff _ _).mp hh
  obtain ⟨g, κ, hg, hfac⟩ := exists_monic_cofactor hP0 hhd.2.2.1
  obtain ⟨hS, -⟩ := hN₀ m (by omega) h g κ hh hg hfac
  obtain ⟨hIrrW, hW, -⟩ := hN₃ m (by omega) h g κ hh hg hfac
  have hM := hN₂ m (by omega) h hh
  rw [Real.rpow_one] at hM
  have hm100 : (100 : ℝ) ≤ m := by
    have : 100 ≤ m := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log m := by linarith [abs_nonneg C₀]
  have hCn : C₀ * m / Real.log m ≤ 0.1 * m := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m)
      (by linarith [le_abs_self C₀] : (0 : ℝ) ≤ Real.log m - 10 * C₀)]
  have hM9 : 0.9 * (m : ℝ) ≤ h.natDegree := by linarith
  have hdeg : m < 2 * h.natDegree := by
    have : (m : ℝ) < 2 * h.natDegree := by linarith
    exact_mod_cast this
  -- the normalized factor
  set u : ℚ := ((-2 : ℚ) ^ h.natDegree)⁻¹ with hu_def
  have hu : u ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  set L : ℚ[X] := C (-2) * polyX + C 1 with hL_def
  have hLdeg : L.natDegree = 1 := natDegree_linear hc
  set q : ℚ[X] := C u * h.comp L with hq_def
  have hqdeg : q.natDegree = h.natDegree := by
    rw [hq_def, natDegree_C_mul hu, natDegree_comp, hLdeg, mul_one]
  have hqmonic : q.Monic := by
    rw [Monic, hq_def, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by omega),
      hhd.1.leadingCoeff, one_mul, hL_def, leadingCoeff_linear hc, hu_def, inv_mul_cancel₀]
    exact pow_ne_zero _ hc
  have hqirr : Irreducible q := irreducible_C_mul_comp_affine hhd.2.1 hu hc
  -- identification of `Q`
  obtain ⟨s, hs, hPs⟩ := divByMonic_eq_jacobiP_comp hT ha m δ hδ
  have hLsq : L.comp (polyX ^ 2) = 1 + C (-2) * polyX ^ 2 := by
    simp only [hL_def, add_comp, mul_comp, C_comp, X_comp, C_1, one_comp]
    ring
  have hQ : contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) =
      C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp L := by
    rw [hPs, show C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp (1 + C (-2) * polyX ^ 2) =
      expand ℚ 2 (C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp L) by
        rw [map_mul, expand_C, expand_eq_comp_X_pow, comp_assoc, hLsq]]
    exact contract_expand 2 two_ne_zero
  have hLne : ∀ p : ℚ[X], p ≠ 0 → p.comp L ≠ 0 := by
    intro p hp h0
    rcases comp_eq_zero_iff.mp h0 with h1 | ⟨-, h1⟩
    · exact hp h1
    · have := congrArg natDegree h1
      rw [hLdeg, natDegree_C] at this
      exact one_ne_zero this
  have hQ0 : contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) ≠ 0 := by
    rw [hQ]
    exact mul_ne_zero (C_ne_zero.mpr hs) (hLne _ hP0)
  have hQdeg : (contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ)).natDegree ≤ m := by
    rw [hQ]
    calc (C s * (jacobiP ((δ : ℚ) - 1 / 2) a m).comp L).natDegree
        ≤ ((jacobiP ((δ : ℚ) - 1 / 2) a m).comp L).natDegree := natDegree_C_mul_le _ _
      _ ≤ (jacobiP ((δ : ℚ) - 1 / 2) a m).natDegree * L.natDegree := natDegree_comp_le
      _ ≤ m := by
        rw [hLdeg, mul_one]
        exact natDegree_jacobiP_le _ _ m
  have hqdvd : q ∣ contract 2 (jacobiP a a (2 * m + δ) /ₘ polyX ^ δ) := by
    have hκ : κ ≠ 0 := by
      rintro rfl
      exact hP0 (by rw [hfac, C_0, zero_mul, zero_mul])
    refine ⟨C (s * κ * u⁻¹) * g.comp L, ?_⟩
    have e : C u * C u⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hu, C_1]
    rw [hQ, hfac, mul_comp, mul_comp, C_comp, hq_def, C_mul, C_mul]
    linear_combination (-(C s * C κ * h.comp L * g.comp L)) * e
  refine ⟨q, ⟨hqmonic, hqirr, hqdvd, by rw [hqdeg]; exact hdeg⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- uniqueness
    intro q' hq'm hq'i hq'd hq'deg
    by_contra hne
    have hnd : ¬ q ∣ q' := fun hd =>
      hne (eq_of_monic_of_associated hq'm hqmonic (hqirr.associated_of_dvd hq'i hd).symm)
    have hcop : IsCoprime q q' := hqirr.coprime_iff_not_dvd.mpr hnd
    have hprod := hcop.mul_dvd hqdvd hq'd
    have hle := natDegree_le_of_dvd hprod hQ0
    rw [(hqmonic.natDegree_mul hq'm)] at hle
    omega
  · rw [hqdeg]
    exact hN₁ m (by omega) h hh
  · rw [hq_def]
    exact GaloisGroupIsSymmetric.affine h 1 hu hc hS
  · have e : q.comp (polyX ^ 2) = C u * h.comp (1 + C (-2) * polyX ^ 2) := by
      rw [hq_def, mul_comp, C_comp, comp_assoc, hLsq]
    rw [e, irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit hu))]
    exact hIrrW
  · rw [natDegree_comp, hqdeg, natDegree_X_pow]
    ring
  · have e : q.comp (polyX ^ 2) = C u * h.comp (1 + C (-2) * polyX ^ 2) := by
      rw [hq_def, mul_comp, C_comp, comp_assoc, hLsq]
    rw [e]
    exact GaloisGroupIsWreath.C_mul hu hW

end FixedRationalParameters

end ArithmeticOfJacobiPolynomials
