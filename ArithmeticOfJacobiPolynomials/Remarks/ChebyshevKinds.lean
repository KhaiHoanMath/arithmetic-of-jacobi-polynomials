/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.Chebyshev
public import ArithmeticOfJacobiPolynomials.Remarks.ChebyshevCyclotomicField
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricGegenbauer
public import ArithmeticOfJacobiPolynomials.External
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The four Chebyshev specializations have zeros in cyclotomic fields

The manuscript (after Theorem 1.6, and in the discussion of the denominator hypotheses) says that
the denominator hypotheses exclude "the Chebyshev specializations, whose roots lie in cyclotomic
fields and whose Galois groups are abelian". The four Chebyshev families are the Jacobi
polynomials `P_n^{(α,β)}` with `α, β ∈ {±1/2}` ([DLMF, §18.7]). The first kind
`(-1/2,-1/2)` is in `ArithmeticOfJacobiPolynomials.Remarks.Chebyshev`; this file treats the other
three, so that the clause holds for all four.

* `jacobiP_half_half_eq`: `P_n^{(1/2,1/2)} = c U_n` (`U_n` Mathlib's Chebyshev polynomial of the
  second kind), from the differential equation of `U_n` and the uniqueness of the symmetric
  recurrence (`symRecurrence_unique`), unconditionally;
* `splits_jacobiP_half_half`: for `n ≥ 1`, `P_n^{(1/2,1/2)}` splits over every field containing a
  primitive `2(n+1)`-th root of unity, the zeros being `(ζ^k + ζ^{-k})/2`, `1 ≤ k ≤ n`;
* `splits_jacobiP_neg_half_half` and `splits_jacobiP_half_neg_half` (third and fourth kind): the
  same over every field containing a primitive `4(2n+1)`-th (resp. `2(2n+1)`-th) root of unity.
  These use the quadratic transformations `JacobiQuadraticTransformation`
  ([DLMF, 18.7.13–18.7.14], a hypothesis of `External.lean`) to reduce to `T_{2n+1}/x` and
  `U_{2n}`;
* `gal_mul_comm_jacobiP_half`: the Galois groups of all four are abelian (quotients of the Galois
  group of a cyclotomic field).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset
open Polynomial.Chebyshev (T U T_zero T_one U_zero U_one U_add_two map_T map_U natDegree_T
  natDegree_U_natCast leadingCoeff_U_natCast
  one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U)

/-! ### General lemmas -/

/-- A polynomial over a field with `natDegree` many distinct roots splits. -/
theorem splits_of_card_eq_natDegree {L : Type*} [Field L] {f : L[X]} (hf : f ≠ 0)
    (S : Finset L) (hS : ∀ y ∈ S, f.IsRoot y) (hcard : S.card = f.natDegree) : f.Splits := by
  classical
  have hsub : S ⊆ f.roots.toFinset := fun y hy => by
    rw [Multiset.mem_toFinset, mem_roots hf]; exact hS y hy
  have hle : f.natDegree ≤ Multiset.card f.roots :=
    calc f.natDegree = S.card := hcard.symm
      _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
  rw [splits_iff_card_roots]
  exact le_antisymm (card_roots' _) hle

/-- If `ξ` is a primitive `N`-th root of unity, `(ξ^e + ξ^{-e})/2` determines `e` among exponents
with `0 < e₁ + e₂ < 2N`, `e₁ + e₂ ≠ N` and `e₁, e₂ < N`. -/
theorem half_add_inv_injective {K : Type*} [Field K] [CharZero K] {N : ℕ} {ξ : K}
    (hξ : IsPrimitiveRoot ξ N) {e₁ e₂ : ℕ} (h₁ : e₁ < N) (h₂ : e₂ < N) (hpos : 0 < e₁ + e₂)
    (hne : e₁ + e₂ ≠ N) (hlt : e₁ + e₂ < 2 * N)
    (h : (ξ ^ e₁ + (ξ ^ e₁)⁻¹) / 2 = (ξ ^ e₂ + (ξ ^ e₂)⁻¹) / 2) : e₁ = e₂ := by
  have hN : 0 < N := by omega
  have ha0 : ξ ^ e₁ ≠ 0 := pow_ne_zero _ (hξ.ne_zero (by omega))
  have hb0 : ξ ^ e₂ ≠ 0 := pow_ne_zero _ (hξ.ne_zero (by omega))
  set a := ξ ^ e₁ with ha
  set b := ξ ^ e₂ with hb
  have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
  have key : (a - b) * (a * b - 1) = 0 := by
    linear_combination (2 * a * b) * h - b * haa + a * hbb
  rcases mul_eq_zero.mp key with h1 | h1
  · exact hξ.pow_inj h₁ h₂ (sub_eq_zero.mp h1)
  · exfalso
    have hab : ξ ^ (e₁ + e₂) = 1 := by rw [pow_add]; exact sub_eq_zero.mp h1
    have hd := hξ.dvd_of_pow_eq_one _ hab
    obtain ⟨c, hc⟩ := hd
    rcases c with _ | _ | c
    · omega
    · omega
    · have : N * (c + 1 + 1) = N * c + 2 * N := by ring
      omega

/-- If `f` splits over a cyclotomic extension `L` of `ℚ`, its Galois group is abelian. -/
theorem gal_mul_comm_of_splits_cyclotomic (N : ℕ) [NeZero N] (f : ℚ[X]) (L : Type*) [Field L]
    [Algebra ℚ L] [IsCyclotomicExtension {N} ℚ L] (h : (f.map (algebraMap ℚ L)).Splits)
    (σ τ : f.Gal) : σ * τ = τ * σ := by
  have : Fact ((f.map (algebraMap ℚ L)).Splits) := ⟨h⟩
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois (S := {N}) (K := ℚ) (L := L)
  have : IsMulCommutative (L ≃ₐ[ℚ] L) :=
    IsCyclotomicExtension.isMulCommutative (S := {N}) (A := ℚ) (B := L)
  obtain ⟨a, rfl⟩ := Gal.restrict_surjective (p := f) (E := L) σ
  obtain ⟨b, rfl⟩ := Gal.restrict_surjective (p := f) (E := L) τ
  have hab : a * b = b * a := IsMulCommutative.is_comm.comm a b
  rw [← map_mul, hab, map_mul]

/-- If `f` splits over every cyclotomic extension `ℚ(ζ_N)`, its Galois group is abelian. -/
theorem gal_mul_comm_of_forall_splits (N : ℕ) [NeZero N] (f : ℚ[X])
    (h : ∀ (L : Type) [Field L] [Algebra ℚ L] [IsCyclotomicExtension {N} ℚ L],
      (f.map (algebraMap ℚ L)).Splits) (σ τ : f.Gal) : σ * τ = τ * σ := by
  let _ := CyclotomicField.algebra N ℚ
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast (NeZero.ne N)⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact gal_mul_comm_of_splits_cyclotomic N f (CyclotomicField N ℚ) (h _) σ τ

/-- `binom(n + α, n) ≠ 0` for `α > -1`. -/
theorem ring_choose_add_ne_zero {α : ℚ} (hα : -1 < α) (n : ℕ) :
    Ring.choose ((n : ℚ) + α) n ≠ 0 := by
  intro h
  have h1 := factorial_mul_ring_choose ((n : ℚ) + α) n
  rw [h, mul_zero, show (n : ℚ) + α - n + 1 = α + 1 by ring] at h1
  exact (ascPochhammer_pos n (α + 1) (by linarith)).ne' h1.symm

/-- `2((a + a⁻¹)/2)² - 1 = (a² + a⁻²)/2`. -/
theorem two_mul_sq_sub_one_half_add_inv {K : Type*} [Field K] [CharZero K] {a : K} (ha : a ≠ 0) :
    2 * ((a + a⁻¹) / 2) ^ 2 - 1 = (a ^ 2 + (a ^ 2)⁻¹) / 2 := by
  field_simp
  ring

/-! ### The second kind -/

/-- `U_m((z + z⁻¹)/2) (z - z⁻¹) = z^{m+1} - z^{-(m+1)}`. -/
theorem chebyshevU_eval_half_add_inv_mul {K : Type*} [Field K] [CharZero K] {z : K} (hz : z ≠ 0)
    (m : ℕ) : (U K m).eval ((z + z⁻¹) / 2) * (z - z⁻¹) = z ^ (m + 1) - z⁻¹ ^ (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [U_zero]
    · simp only [Nat.cast_one, U_one, eval_mul, eval_ofNat, eval_X, zero_add]
      ring
    · have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hU : U K ((m + 1 + 1 : ℕ) : ℤ) = 2 * polyX * U K ((m + 1 : ℕ) : ℤ) - U K (m : ℤ) := by
        have h := U_add_two (R := K) (m : ℤ)
        rw [show (m : ℤ) + 2 = ((m + 1 + 1 : ℕ) : ℤ) by push_cast; ring,
          show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring] at h
        exact h
      rw [hU, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat]
      set w := z⁻¹ with hw
      have hzw : z * w = 1 := mul_inv_cancel₀ hz
      linear_combination (z + w) * h1 - h0 + (z ^ (m + 1) - w ^ (m + 1)) * hzw

/-- For a primitive `2(n+1)`-th root of unity `ζ` and `1 ≤ k ≤ n`, `(ζ^k + ζ^{-k})/2` is a root of
`U_n`. -/
theorem isRoot_chebyshevU_of_isPrimitiveRoot {K : Type*} [Field K] [CharZero K] {n : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 * (n + 1))) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (U K n).IsRoot ((ζ ^ k + (ζ ^ k)⁻¹) / 2) := by
  have hz : ζ ^ k ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
  have hkey := chebyshevU_eval_half_add_inv_mul hz n
  have hi : ζ ^ (n + 1) = -1 :=
    (hζ.pow (by omega) (show 2 * (n + 1) = (n + 1) * 2 by ring)).eq_neg_one_of_two_right
  have hs : (ζ ^ k) ^ (n + 1) = (-1) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, hi]
  have hs2 : ((-1 : K) ^ k)⁻¹ = (-1) ^ k := by
    rw [← inv_pow, inv_neg_one]
  have hdiff : (ζ ^ k) ^ (n + 1) - (ζ ^ k)⁻¹ ^ (n + 1) = 0 := by
    rw [inv_pow, hs, hs2, sub_self]
  rw [hdiff] at hkey
  have hne : ζ ^ k - (ζ ^ k)⁻¹ ≠ 0 := by
    intro h0
    have hsq : (ζ ^ k) ^ 2 = 1 := by
      have h1 : ζ ^ k * (ζ ^ k)⁻¹ = 1 := mul_inv_cancel₀ hz
      have h2 : ζ ^ k = (ζ ^ k)⁻¹ := sub_eq_zero.mp h0
      calc (ζ ^ k) ^ 2 = ζ ^ k * (ζ ^ k)⁻¹ := by rw [sq]; nth_rewrite 2 [h2]; rfl
        _ = 1 := h1
    rw [← pow_mul] at hsq
    have := hζ.dvd_of_pow_eq_one _ hsq
    have := Nat.le_of_dvd (by omega) this
    omega
  exact (mul_eq_zero.mp hkey).resolve_right hne

/-- For `n ≥ 1` and a primitive `2(n+1)`-th root of unity `ζ`, `U_n` splits. -/
theorem splits_chebyshevU_of_isPrimitiveRoot {L : Type*} [Field L] [Algebra ℚ L] (n : ℕ)
    (hn : 1 ≤ n) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 * (n + 1))) :
    ((U ℚ n).map (algebraMap ℚ L)).Splits := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  rw [map_U]
  have hdeg : (U L n).natDegree = n := by simp [natDegree_U_natCast]
  have hU0 : U L n ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  set x : ℕ → L := fun k => (ζ ^ k + (ζ ^ k)⁻¹) / 2 with hx
  refine splits_of_card_eq_natDegree hU0 ((Icc 1 n).image x) ?_ ?_
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hk
    exact isRoot_chebyshevU_of_isPrimitiveRoot hζ hk.1 hk.2
  · rw [hdeg, card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro k₁ hk₁ k₂ hk₂ h
      have hk₁' := mem_Icc.mp (mem_coe.mp hk₁)
      have hk₂' := mem_Icc.mp (mem_coe.mp hk₂)
      exact half_add_inv_injective hζ (by omega) (by omega) (by omega) (by omega) (by omega) h

/-! ### `P_n^{(1/2,1/2)}` is a multiple of `U_n` -/

/-- `U_n` satisfies the symmetric recurrence with `a = 1/2` (its differential equation is
`(1 - x²) y'' - 3 x y' + n (n + 2) y = 0`). -/
theorem symRecurrence_chebyshevU (n : ℕ) : SymRecurrence (1 / 2 : ℚ) n (U ℚ n) := by
  apply symRecurrence_of_ode
  have h := one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := ℚ) (n : ℤ)
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply] at h
  rw [h]
  have e1 : (C (2 * (1 / 2 : ℚ) + 2) : ℚ[X]) = 3 := by
    rw [show (2 * (1 / 2 : ℚ) + 2) = 3 by norm_num]
    exact map_ofNat C 3
  have e2 : (C ((n : ℚ) * (n + 2 * (1 / 2) + 1)) : ℚ[X]) = ((n : ℚ[X]) + 2) * n := by
    rw [show (n : ℚ) * (n + 2 * (1 / 2) + 1) = (n + 2) * n by ring]
    simp only [map_mul, map_add, map_natCast, map_ofNat]
  rw [e1, e2]
  push_cast
  ring

/-- **`P_n^{(1/2,1/2)}` is a rational multiple of the Chebyshev polynomial of the second kind**
([DLMF, §18.7]), proved from the differential equation. -/
theorem exists_jacobiP_half_half_eq (n : ℕ) :
    ∃ c : ℚ, jacobiP (1 / 2) (1 / 2) n = C c * U ℚ n := by
  have hu := symRecurrence_unique (a := (1 / 2 : ℚ)) (by norm_num) (n := n) (y := U ℚ n)
    (z := jacobiP (1 / 2) (1 / 2) n) (symRecurrence_chebyshevU n) (symRecurrence_jacobiP _ n)
    (fun j hj => coeff_eq_zero_of_natDegree_lt (by rw [natDegree_U_natCast]; exact hj))
    (fun j hj => coeff_eq_zero_of_natDegree_lt ((natDegree_jacobiP_le _ _ n).trans_lt hj))
  have hUn : (U ℚ n).coeff n = 2 ^ n := by
    have := leadingCoeff_U_natCast ℚ n
    rwa [leadingCoeff, natDegree_U_natCast] at this
  rw [hUn] at hu
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  refine ⟨((2 : ℚ) ^ n)⁻¹ * (jacobiP (1 / 2) (1 / 2) n).coeff n, ?_⟩
  calc jacobiP (1 / 2) (1 / 2) n
      = C (((2 : ℚ) ^ n)⁻¹ * 2 ^ n) * jacobiP (1 / 2) (1 / 2) n := by
        rw [inv_mul_cancel₀ h2, C_1, one_mul]
    _ = C (((2 : ℚ) ^ n)⁻¹) * (C ((2 : ℚ) ^ n) * jacobiP (1 / 2) (1 / 2) n) := by
        rw [C_mul, mul_assoc]
    _ = _ := by rw [← hu, ← mul_assoc, ← C_mul]

/-- **Second kind.** For `n ≥ 1` and a primitive `2(n+1)`-th root of unity `ζ`, `P_n^{(1/2,1/2)}`
splits, with zeros `(ζ^k + ζ^{-k})/2`, `1 ≤ k ≤ n`. -/
theorem splits_jacobiP_half_half (n : ℕ) (hn : 1 ≤ n) (L : Type*) [Field L] [Algebra ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (2 * (n + 1))) :
    ((jacobiP (1 / 2) (1 / 2) n).map (algebraMap ℚ L)).Splits := by
  obtain ⟨c, hc⟩ := exists_jacobiP_half_half_eq n
  rw [hc, Polynomial.map_mul, Polynomial.map_C]
  exact (splits_chebyshevU_of_isPrimitiveRoot n hn hζ).C_mul _

/-! ### The third and fourth kinds -/

/-- Common facts on `P_m^{(α,β)}` with `α + β = 0`: it is nonzero of degree `m`. -/
theorem natDegree_eq_and_ne_zero_of_add_eq_zero (α β : ℚ) (m : ℕ) (h : α + β = 0) :
    (jacobiP α β m).natDegree = m ∧ jacobiP α β m ≠ 0 := by
  have hc : Ring.choose (2 * (m : ℚ) + α + β) m ≠ 0 := by
    rw [add_assoc, h, add_zero, show 2 * (m : ℚ) = ((2 * m : ℕ) : ℚ) by push_cast; ring,
      Ring.choose_natCast]
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  refine ⟨natDegree_jacobiP α β m hc, fun h0 => ?_⟩
  have := coeff_jacobiP_self α β m
  rw [h0, coeff_zero] at this
  exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc) this.symm

/-- **Third kind.** `P_m^{(-1/2,1/2)}` splits over every field containing a primitive
`4(2m+1)`-th root of unity `ζ`; its zeros are `(ξ^{2k+1} + ξ^{-(2k+1)})/2`, `0 ≤ k < m`, `ξ = ζ²`.
Conditional on the quadratic transformation [DLMF, 18.7.13–18.7.14]
(`JacobiQuadraticTransformation`), which gives `x P_m^{(-1/2,1/2)}(2x²-1) ∝ T_{2m+1}(x)`. -/
theorem splits_jacobiP_neg_half_half (hQ : JacobiQuadraticTransformation) (m : ℕ) (L : Type*)
    [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ (4 * (2 * m + 1))) :
    ((jacobiP (-1 / 2) (1 / 2) m).map (algebraMap ℚ L)).Splits := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  obtain ⟨hdeg, hf0⟩ := natDegree_eq_and_ne_zero_of_add_eq_zero (-1 / 2) (1 / 2) m (by norm_num)
  set f := jacobiP (-1 / 2 : ℚ) (1 / 2) m with hf
  have hinj := (algebraMap ℚ L).injective
  have hfL : f.map (algebraMap ℚ L) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf0
  have hdegL : (f.map (algebraMap ℚ L)).natDegree = m := by
    rw [natDegree_map_eq_of_injective hinj, hdeg]
  have hq := (hQ.rat (-1 / 2) (by norm_num) m).2
  have hP1 : (jacobiP (-1 / 2) (-1 / 2) (2 * m + 1)).eval 1 ≠ 0 := by
    rw [jacobiP_eval_one]
    exact_mod_cast ring_choose_add_ne_zero (α := -1 / 2) (by norm_num) (2 * m + 1)
  generalize (jacobiP (-1 / 2) (-1 / 2) (2 * m + 1)).eval 1 = P1 at hq hP1
  rw [jacobiP_neg_half_neg_half_eq] at hq
  have hξ : IsPrimitiveRoot (ζ ^ 2) (2 * (2 * m + 1)) :=
    hζ.pow (by omega) (show 4 * (2 * m + 1) = 2 * (2 * (2 * m + 1)) by ring)
  have hi : ζ ^ (2 * (2 * m + 1)) = -1 :=
    (hζ.pow (by omega) (show 4 * (2 * m + 1) = 2 * (2 * m + 1) * 2 by ring)).eq_neg_one_of_two_right
  set x : ℕ → L := fun k => (ζ ^ (2 * k + 1) + (ζ ^ (2 * k + 1))⁻¹) / 2 with hx
  set y : ℕ → L := fun k => ((ζ ^ 2) ^ (2 * k + 1) + ((ζ ^ 2) ^ (2 * k + 1))⁻¹) / 2 with hy
  have hxy : ∀ k, 2 * (x k) ^ 2 - 1 = y k := fun k => by
    have ha : ζ ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    simp only [hx, hy]
    rw [two_mul_sq_sub_one_half_add_inv ha, ← pow_mul, ← pow_mul, mul_comm 2 (2 * k + 1)]
  have hx0 : ∀ k, k < m → x k ≠ 0 := fun k hk h0 => by
    have ha : ζ ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    simp only [hx] at h0
    set a := ζ ^ (2 * k + 1) with haeq
    have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    have h2 : a ^ 2 = -1 := by
      have : a + a⁻¹ = 0 := by linear_combination 2 * h0
      linear_combination a * this - h1
    have h3 : ζ ^ (2 * (2 * k + 1)) = ζ ^ (2 * (2 * m + 1)) := by
      rw [hi, ← h2, haeq, ← pow_mul, mul_comm]
    have := hζ.pow_inj (by omega) (by omega) h3
    omega
  refine splits_of_card_eq_natDegree hfL ((range m).image y) ?_ ?_
  · intro v hv
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
    have hk' := mem_range.mp hk
    have hT := isRoot_chebyshevT_of_isPrimitiveRoot (K := L) (n := 2 * m + 1) (by omega) hζ k
    have hT' : aeval (x k) (T ℚ ((2 * m + 1 : ℕ) : ℤ)) = 0 := by
      rw [Chebyshev.aeval_T]; exact hT
    have haev : aeval (x k) (2 * polyX ^ 2 - 1 : ℚ[X]) = y k := by
      simp only [map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
      exact hxy k
    have h0 := congrArg (aeval (x k)) hq
    simp only [map_mul, aeval_C, aeval_X, aeval_comp, hT', haev, mul_zero] at h0
    have hP1' : algebraMap ℚ L P1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hP1
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h hP1'
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (hx0 k hk')
    · rw [IsRoot.def, eval_map_algebraMap]; exact h
  · rw [hdegL, card_image_of_injOn, card_range]
    intro k₁ hk₁ k₂ hk₂ h
    have hk₁' := mem_range.mp (mem_coe.mp hk₁)
    have hk₂' := mem_range.mp (mem_coe.mp hk₂)
    have := half_add_inv_injective hξ (e₁ := 2 * k₁ + 1) (e₂ := 2 * k₂ + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega) h
    omega

/-- **Fourth kind.** `P_m^{(1/2,-1/2)}` splits over every field containing a primitive
`2(2m+1)`-th root of unity `ζ`; its zeros are `(ζ^{2j} + ζ^{-2j})/2`, `1 ≤ j ≤ m`. Conditional on
the quadratic transformation [DLMF, 18.7.13–18.7.14] (`JacobiQuadraticTransformation`), which gives
`P_m^{(1/2,-1/2)}(2x²-1) ∝ P_{2m}^{(1/2,1/2)}(x) ∝ U_{2m}(x)`. -/
theorem splits_jacobiP_half_neg_half (hQ : JacobiQuadraticTransformation) (m : ℕ) (L : Type*)
    [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 * (2 * m + 1))) :
    ((jacobiP (1 / 2) (-1 / 2) m).map (algebraMap ℚ L)).Splits := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  obtain ⟨hdeg, hf0⟩ := natDegree_eq_and_ne_zero_of_add_eq_zero (1 / 2) (-1 / 2) m (by norm_num)
  set f := jacobiP (1 / 2 : ℚ) (-1 / 2) m with hf
  have hinj := (algebraMap ℚ L).injective
  have hfL : f.map (algebraMap ℚ L) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf0
  have hdegL : (f.map (algebraMap ℚ L)).natDegree = m := by
    rw [natDegree_map_eq_of_injective hinj, hdeg]
  have hq := (hQ.rat (1 / 2) (by norm_num) m).1
  have hP1 : (jacobiP (1 / 2) (1 / 2) (2 * m)).eval 1 ≠ 0 := by
    rw [jacobiP_eval_one]
    exact_mod_cast ring_choose_add_ne_zero (α := 1 / 2) (by norm_num) (2 * m)
  generalize (jacobiP (1 / 2) (1 / 2) (2 * m)).eval 1 = P1 at hq hP1
  obtain ⟨c, hc⟩ := exists_jacobiP_half_half_eq (2 * m)
  rw [hc] at hq
  set x : ℕ → L := fun j => (ζ ^ j + (ζ ^ j)⁻¹) / 2 with hx
  set y : ℕ → L := fun j => (ζ ^ (2 * j) + (ζ ^ (2 * j))⁻¹) / 2 with hy
  have hxy : ∀ j, 2 * (x j) ^ 2 - 1 = y j := fun j => by
    have ha : ζ ^ j ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    simp only [hx, hy]
    rw [two_mul_sq_sub_one_half_add_inv ha, ← pow_mul, mul_comm j 2]
  refine splits_of_card_eq_natDegree hfL ((Icc 1 m).image y) ?_ ?_
  · intro v hv
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    have hj' := mem_Icc.mp hj
    have hU := isRoot_chebyshevU_of_isPrimitiveRoot (K := L) (n := 2 * m) hζ (k := j) hj'.1
      (by omega)
    have hU' : aeval (x j) (U ℚ ((2 * m : ℕ) : ℤ)) = 0 := by
      rw [Chebyshev.aeval_U]; exact hU
    have haev : aeval (x j) (2 * polyX ^ 2 - 1 : ℚ[X]) = y j := by
      simp only [map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
      exact hxy j
    have h0 := congrArg (aeval (x j)) hq
    simp only [map_mul, aeval_C, aeval_comp, hU', haev, mul_zero] at h0
    have hP1' : algebraMap ℚ L P1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hP1
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h hP1'
    · rw [IsRoot.def, eval_map_algebraMap]; exact h
  · rw [hdegL, card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro j₁ hj₁ j₂ hj₂ h
      have hj₁' := mem_Icc.mp (mem_coe.mp hj₁)
      have hj₂' := mem_Icc.mp (mem_coe.mp hj₂)
      have := half_add_inv_injective hζ (e₁ := 2 * j₁) (e₂ := 2 * j₂) (by omega) (by omega)
        (by omega) (by omega) (by omega) h
      omega

/-! ### Abelian Galois groups -/

/-- **The four Chebyshev specializations have abelian Galois groups.** For `n ≥ 1` and
`α, β ∈ {±1/2}`, the Galois group of `P_n^{(α,β)}` over `ℚ` is abelian, being a quotient of the
Galois group of a cyclotomic field over which it splits. The first and second kinds are
unconditional; the third and fourth use `JacobiQuadraticTransformation`. -/
theorem gal_mul_comm_jacobiP_half (hQ : JacobiQuadraticTransformation) {α β : ℚ}
    (hα : α = 1 / 2 ∨ α = -1 / 2) (hβ : β = 1 / 2 ∨ β = -1 / 2) (n : ℕ) (hn : 1 ≤ n)
    (σ τ : (jacobiP α β n).Gal) : σ * τ = τ * σ := by
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
  · have : NeZero (2 * (n + 1)) := ⟨by omega⟩
    refine gal_mul_comm_of_forall_splits (2 * (n + 1)) _ (fun L _ _ _ => ?_) σ τ
    exact splits_jacobiP_half_half n hn L (IsCyclotomicExtension.zeta_spec (2 * (n + 1)) ℚ L)
  · have : NeZero (2 * (2 * n + 1)) := ⟨by omega⟩
    refine gal_mul_comm_of_forall_splits (2 * (2 * n + 1)) _ (fun L _ _ _ => ?_) σ τ
    exact splits_jacobiP_half_neg_half hQ n L
      (IsCyclotomicExtension.zeta_spec (2 * (2 * n + 1)) ℚ L)
  · have : NeZero (4 * (2 * n + 1)) := ⟨by omega⟩
    refine gal_mul_comm_of_forall_splits (4 * (2 * n + 1)) _ (fun L _ _ _ => ?_) σ τ
    exact splits_jacobiP_neg_half_half hQ n L
      (IsCyclotomicExtension.zeta_spec (4 * (2 * n + 1)) ℚ L)
  · exact jacobiP_neg_half_neg_half_gal_mul_comm n hn σ τ

end ArithmeticOfJacobiPolynomials
