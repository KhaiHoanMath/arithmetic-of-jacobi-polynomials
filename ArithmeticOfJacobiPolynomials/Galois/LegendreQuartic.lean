/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.LegendreWreath
public import ArithmeticOfJacobiPolynomials.Galois.LegendreQuarticSquareClasses
public import ArithmeticOfJacobiPolynomials.Galois.SquaresBridge
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Data.Rat.Lemmas

/-!
# The exceptional Legendre degree: `Gal(P_5/x) = W_2`

The proof of Theorem 5.9 treats `(n, δ) = (2, 1)` separately: `L_5 = P_5/x` is proportional to
`63x⁴ - 70x² + 15`, and its squared roots `y_±` satisfy `63y² - 70y + 15 = 0`, so
`y_± = (35 ± 2s)/63` with `s² = 70`. We follow the manuscript: `y_+`, `y_-` and `y_+ y_- = 5/21`
are not squares in `ℚ(√70)` (`LegendreQuarticSquareClasses`: a square there has norm a rational
square, and a rational `q` is a square only if `q` or `q/70` is one, which fails for `5/21` and
`1/294`). Hence `[ℚ(x) : ℚ] = 4` and a root `x'` of `y_-` is not in `ℚ(x)`, so the splitting
field has degree at least `8`, and the Galois group, which lies in `W_2` of order `8`, is all of
`W_2`. This case uses no cited hypothesis.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {L : Type*} [Field L] {s : Set L}

/-- `|W_N| ≤ 2^N N!` for `N` opposite pairs. -/
theorem nat_card_negCommPerm_le [Finite s] (h2 : (2 : L) ≠ 0)
    (h0 : (0 : L) ∉ s) (hneg : ∀ x ∈ s, -x ∈ s) :
    Nat.card (negCommPerm s) ≤
      2 ^ Nat.card (squares s) * (Nat.card (squares s)).factorial := by
  classical
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pairPerm (s := s)).ker, mul_comm]
  have hq : Nat.card (negCommPerm s ⧸ (pairPerm (s := s)).ker) ≤
      (Nat.card (squares s)).factorial := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (pairPerm (s := s))).toEquiv,
      ← Nat.card_perm]
    exact Subgroup.card_le_card_group _
  have hk : Nat.card (pairPerm (s := s)).ker ≤ 2 ^ Nat.card (squares s) := by
    have hsurj : Function.Surjective (fun T : Set (squares s) =>
        (⟨⟨signFlip hneg T, signFlip_mem_negCommPerm hneg T⟩, signFlip_mem_ker hneg T⟩ :
          (pairPerm (s := s)).ker)) := by
      rintro ⟨k, hk⟩
      refine ⟨toSquare '' {x | (k : Equiv.Perm s) x ≠ x}, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact (eq_signFlip_of_mem_ker hneg h2 h0 hk).symm
    have : Fintype (squares s) := Fintype.ofFinite _
    refine (Nat.card_le_card_of_surjective _ hsurj).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_set, Nat.card_eq_fintype_card]
  exact Nat.mul_le_mul hk hq

/-- `J_2^1 = 63T² + 70T + 15`. -/
theorem legendreJ_one_two :
    (legendreJ (2 * ((1 : ℕ) : ℤ) - 1) 2).map (Int.castRingHom ℚ) =
      C 63 * polyX ^ 2 + C 70 * polyX + C 15 := by
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [legendreJ_eq, hI]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_pair
    (by norm_num : (1 : ℕ) ≠ 2), Polynomial.map_add, Polynomial.map_mul, map_C,
    zero_add]
  norm_num
  ring

section Degree

open LegendreQuartic

variable {E : Type*} [Field E] [Algebra ℚ E] {s x x' : E}

/-- Every element of `ℚ(x)` is a rational combination of `1, x, x², x³`, when
`63x⁴ - 70x² + 15 = 0`. -/
theorem exists_coeffs_of_mem_adjoin [FiniteDimensional ℚ E]
    (hx4 : 63 * (x ^ 2) ^ 2 - 70 * x ^ 2 + 15 = 0) {y : E}
    (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ c₀ c₁ c₂ c₃ : ℚ, y = c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ E).injective
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    have h1 : y ∈ (IntermediateField.adjoin ℚ {x}).toSubalgebra := hy
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x)] at h1
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  set m : ℚ[X] := polyX ^ 4 + (C (-70 / 63) * polyX ^ 2 + C (15 / 63)) with hm
  have hmm : m.Monic := by
    refine monic_X_pow_add ?_
    compute_degree!
  have hmx : aeval x m = 0 := by
    simp only [hm, map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
    push_cast
    linear_combination (1 / 63 : E) * hx4
  have hp : aeval x p = aeval x (p %ₘ m) := by
    conv_lhs => rw [← modByMonic_add_div p m]
    rw [map_add, map_mul, hmx, zero_mul, add_zero]
  have hm4 : m.natDegree = 4 := by rw [hm]; compute_degree!
  have hdeg : (p %ₘ m).natDegree < 4 := by
    rw [← hm4]
    exact natDegree_modByMonic_lt p hmm (by intro h; rw [h] at hm4; simp at hm4)
  refine ⟨(p %ₘ m).coeff 0, (p %ₘ m).coeff 1, (p %ₘ m).coeff 2, (p %ₘ m).coeff 3, ?_⟩
  change aeval x p = _
  rw [hp, aeval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Algebra.smul_def,
    eq_ratCast, pow_zero, mul_one, pow_one]

/-- **The degree of the splitting field of the exceptional quartic is at least `8`**
(the manuscript's argument): `x² = y_+` and `x'² = y_-` with `y_± = (35 ± 2s)/63`, `s² = 70`;
`ℚ(x)` has degree `4` over `ℚ` and does not contain `x'`. -/
theorem eight_le_finrank [FiniteDimensional ℚ E] (hs : s ^ 2 = 70)
    (hx : x ^ 2 = (35 + 2 * s) / 63) (hx' : x' ^ 2 = (35 - 2 * s) / 63) :
    8 ≤ Module.finrank ℚ E := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ E).injective
  set F := IntermediateField.adjoin ℚ {x} with hF
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self ℚ x
  have hx4 : 63 * (x ^ 2) ^ 2 - 70 * x ^ 2 + 15 = 0 := by
    rw [hx]; linear_combination (4 / 63 : E) * hs
  -- `[ℚ(x) : ℚ] ≥ 4`
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h4 : 4 ≤ Module.finrank ℚ F := by
    rw [hF, IntermediateField.adjoin.finrank hint]
    by_contra hlt
    have hlt' : (minpoly ℚ x).natDegree < 4 := by omega
    have hq0 : minpoly ℚ x ≠ 0 := minpoly.ne_zero hint
    have hqx : aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
    rw [aeval_eq_sum_range' hlt'] at hqx
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Algebra.smul_def,
      eq_ratCast, pow_zero, mul_one, pow_one] at hqx
    obtain ⟨h0, h1, h2, h3⟩ := LegendreQuartic.powers_linearIndependent hs hx
      (c₀ := (minpoly ℚ x).coeff 0) (c₁ := (minpoly ℚ x).coeff 1) (c₂ := (minpoly ℚ x).coeff 2)
      (c₃ := (minpoly ℚ x).coeff 3) (by linear_combination hqx)
    apply hq0
    ext n
    by_cases hn : n < 4
    · interval_cases n <;> simp [h0, h1, h2, h3]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]
  -- `x' ∉ ℚ(x)`
  have hx'F : x' ∉ F := by
    intro hmem
    obtain ⟨c₀, c₁, c₂, c₃, hc⟩ := exists_coeffs_of_mem_adjoin hx4 hmem
    refine LegendreQuartic.ne_add_mul hs hx hx' (A := (c₀ : E) + c₂ * ((35 + 2 * s) / 63))
      (B := (c₁ : E) + c₃ * ((35 + 2 * s) / 63)) ?_ ?_ ?_
    · exact (inK_of_rat c₀).add ((inK_of_rat c₂).mul hs inK_yPlus)
    · exact (inK_of_rat c₁).add ((inK_of_rat c₃).mul hs inK_yPlus)
    · rw [hc, ← hx]; ring
  have h2 : 2 ≤ Module.finrank F E := by
    have hpos : 0 < Module.finrank F E := Module.finrank_pos
    by_contra hlt
    have h1 : Module.finrank F E = 1 := by omega
    rw [finrank_eq_one_iff_of_nonzero' (1 : E) one_ne_zero] at h1
    obtain ⟨c, hc⟩ := h1 x'
    apply hx'F
    have : x' = (c : E) := by rw [← hc, Algebra.smul_def, mul_one]; rfl
    rw [this]; exact c.2
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Module.finrank ℚ F * Module.finrank F E := Nat.mul_le_mul h4 h2
    _ = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ F E


end Degree

/-- `63T² + 70T + 15` is separable over `ℚ`. -/
theorem separable_quarticQuadratic :
    (C 63 * polyX ^ 2 + C 70 * polyX + C 15 : ℚ[X]).Separable := by
  have hJ : (C 63 * polyX ^ 2 + C 70 * polyX + C 15 : ℚ[X]) = 63 * polyX ^ 2 + 70 * polyX + 15 := by
    simp only [map_ofNat]
  rw [hJ, Polynomial.separable_def]
  have hd : derivative (63 * polyX ^ 2 + 70 * polyX + 15 : ℚ[X]) = 126 * polyX + 70 := by
    simp only [derivative_add, derivative_mul, derivative_ofNat, derivative_X_pow,
      derivative_X, zero_mul, zero_add, mul_one, Nat.cast_ofNat, map_ofNat]
    ring
  rw [hd]
  refine ⟨C (-18 / 80) * 1, C (1 / 80) * (9 * polyX + 5), ?_⟩
  have h1 : (18 : ℚ[X]) * (63 * polyX ^ 2 + 70 * polyX + 15) -
      (9 * polyX + 5) * (126 * polyX + 70) = C (-80) := by
    simp only [map_neg, map_ofNat]; ring
  have h2 : (C (-18 / 80) * 1 : ℚ[X]) * (63 * polyX ^ 2 + 70 * polyX + 15) +
      C (1 / 80) * (9 * polyX + 5) * (126 * polyX + 70) =
      C (-1 / 80) * ((18 : ℚ[X]) * (63 * polyX ^ 2 + 70 * polyX + 15) -
        (9 * polyX + 5) * (126 * polyX + 70)) := by
    have e1 : (C (-18 / 80) : ℚ[X]) = C (-1 / 80) * 18 := by
      rw [show (18 : ℚ[X]) = C 18 by simp only [map_ofNat], ← C_mul]; norm_num
    have e2 : (C (1 / 80) : ℚ[X]) = -C (-1 / 80) := by
      rw [← C_neg]; norm_num
    rw [e1, e2]; ring
  rw [h2, h1, ← C_mul]
  norm_num

open Classical in
/-- The Galois group of the even quartic `P` with `(63T² + 70T + 15)(-X²) = 8P` is `W_2`
(the manuscript's argument for `(n, δ) = (2, 1)`): the squared roots `y_±` of `P` satisfy
`63y² - 70y + 15 = 0`, so `y_± = (35 ± 2s)/63` with `s² = 70`; `y_+`, `y_-` and `y_+ y_- = 5/21`
are nonsquares in `ℚ(√70)`, so the splitting field has degree `8` and the Galois group, which lies
in `W_2` of order `8`, is all of `W_2`. -/
theorem galoisGroupIsWreath_of_quartic {P : ℚ[X]}
    (hJL : (C 63 * polyX ^ 2 + C 70 * polyX + C 15 : ℚ[X]).comp (-polyX ^ 2) = C 8 * P) :
    GaloisGroupIsWreath P := by
  classical
  have hk : (8 : ℚ) ≠ 0 := by norm_num
  have hJ0 : (C 63 * polyX ^ 2 + C 70 * polyX + C 15 : ℚ[X]).coeff 0 ≠ 0 := by simp
  have h0 := zero_not_mem_rootSet_of_comp_neg_X_sq hk hJL hJ0
  have hneg : ∀ x ∈ P.rootSet P.SplittingField, -x ∈ P.rootSet P.SplittingField :=
    fun x hx => neg_mem_rootSet_of_comp_neg_X_sq hk hJL hx
  have hΓ := range_galPerm_le_negCommPerm P
  -- the quadratic relation for squared roots
  have hquad : ∀ z : P.rootSet P.SplittingField,
      63 * ((z : P.SplittingField) ^ 2) ^ 2 - 70 * (z : P.SplittingField) ^ 2 + 15 = 0 := by
    intro z
    have h1 := aeval_eq_of_comp_neg_X_sq hk hJL (z : P.SplittingField)
    rw [(mem_rootSet.mp z.2).2, mul_zero] at h1
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow] at h1
    have h63 : (algebraMap ℚ P.SplittingField 63) = 63 := by simp
    have h70 : (algebraMap ℚ P.SplittingField 70) = 70 := by simp
    have h15 : (algebraMap ℚ P.SplittingField 15) = 15 := by simp
    rw [h63, h70, h15] at h1
    linear_combination -h1
  -- the group `W_2` has order at most `8`
  have hdegJ : (C 63 * polyX ^ 2 + C 70 * polyX + C 15 : ℚ[X]).natDegree = 2 := by
    compute_degree!
  have hdegP : P.natDegree = 4 := by rw [natDegree_of_comp_neg_X_sq hk hJL, hdegJ]
  have hsle : Fintype.card (P.rootSet P.SplittingField) ≤ 4 := by
    rw [← Nat.card_eq_fintype_card, rootSet_def, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      ← hdegP]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_map_le))
  have hsq : Nat.card (squares (P.rootSet P.SplittingField)) ≤ 2 := by
    have := nat_card_eq_two_mul_nat_card_squares (s := P.rootSet P.SplittingField) two_ne_zero
      h0 hneg
    rw [Nat.card_eq_fintype_card] at this
    omega
  have hW : Nat.card (negCommPerm (P.rootSet P.SplittingField)) ≤ 8 := by
    refine (nat_card_negCommPerm_le two_ne_zero h0 hneg).trans ?_
    generalize Nat.card (squares (P.rootSet P.SplittingField)) = N at hsq ⊢
    interval_cases N <;> decide
  -- two roots with different squares
  have hcard2 : Nat.card (squares (P.rootSet P.SplittingField)) = 2 := by
    rw [nat_card_squares_of_comp_neg_X_sq hk hJL separable_quarticQuadratic hJ0, hdegJ]
  obtain ⟨q₁, q₂, hne, -⟩ := Nat.card_eq_two_iff.mp hcard2
  obtain ⟨x₁, rfl⟩ := toSquare_surjective q₁
  obtain ⟨x₂, rfl⟩ := toSquare_surjective q₂
  have hne' : (x₁ : P.SplittingField) ^ 2 ≠ (x₂ : P.SplittingField) ^ 2 :=
    fun h => hne (Subtype.ext h)
  have e₁ := hquad x₁
  have e₂ := hquad x₂
  have hsum : 63 * ((x₁ : P.SplittingField) ^ 2 + (x₂ : P.SplittingField) ^ 2) = 70 := by
    have h3 : ((x₁ : P.SplittingField) ^ 2 - (x₂ : P.SplittingField) ^ 2) *
        (63 * ((x₁ : P.SplittingField) ^ 2 + (x₂ : P.SplittingField) ^ 2) - 70) = 0 := by
      linear_combination e₁ - e₂
    have := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne')
    linear_combination this
  -- `s = √70`, `x₁² = (35 + 2s)/63`, `x₂² = (35 - 2s)/63`
  set s : P.SplittingField := (63 * (x₁ : P.SplittingField) ^ 2 - 35) / 2 with hsdef
  have hs : s ^ 2 = 70 := by rw [hsdef]; linear_combination (63 / 4 : P.SplittingField) * e₁
  have hx₁ : (x₁ : P.SplittingField) ^ 2 = (35 + 2 * s) / 63 := by rw [hsdef]; ring
  have hx₂ : (x₂ : P.SplittingField) ^ 2 = (35 - 2 * s) / 63 := by
    rw [hsdef]; linear_combination (1 / 63 : P.SplittingField) * hsum
  -- the degree of the splitting field is at least `8`
  have hdeg8 : 8 ≤ Module.finrank ℚ P.SplittingField := eight_le_finrank hs hx₁ hx₂
  have hcardGal : 8 ≤ Nat.card P.Gal := by
    have : IsGalois ℚ P.SplittingField := {}
    have h : Nat.card P.Gal = Module.finrank ℚ P.SplittingField :=
      IsGalois.card_aut_eq_finrank ℚ P.SplittingField
    omega
  have hrange : Nat.card (galPerm P).range = Nat.card P.Gal :=
    Nat.card_congr (MonoidHom.ofInjective (galPerm_injective P)).toEquiv.symm
  rw [galoisGroupIsWreath_iff]
  exact Subgroup.eq_of_le_of_card_ge hΓ (by omega)

/-- **Theorem 5.9, exceptional case** `(n, δ) = (2, 1)`: the Galois group of
`L_5 = P_5/x ∝ 63x⁴ - 70x² + 15` is `W_2`. Unconditional. -/
theorem galoisGroupIsWreath_reducedLegendre_two_one :
    GaloisGroupIsWreath (reducedLegendre 2 1) := by
  have h := legendreJ_comp_neg_X_sq 2 1 le_rfl
  rw [legendreJ_one_two] at h
  have hJL : (C 63 * polyX ^ 2 + C 70 * polyX + C 15 : ℚ[X]).comp (-polyX ^ 2) =
      C 8 * reducedLegendre 2 1 := by
    rw [h]; norm_num
  exact galoisGroupIsWreath_of_quartic hJL

end ArithmeticOfJacobiPolynomials
