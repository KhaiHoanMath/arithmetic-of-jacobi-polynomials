/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.Modular
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The modular form attached to `F̃_{ℓ-1}` (§6.4)

With `F̃ = F̃_{ℓ-1} = kanekoZagierModularPoly l μ n` of degree `n` with coefficients `c_j`, and
`a, b ∈ ℕ`, put
`F_k = ∑_{j ≤ n} c_j Δ^{n-j} E₄^{a+3j} E₆^b`, a modular form of level one and weight
`k = 12n + 4a + 6b`, built from Mathlib's normalized Eisenstein series `E₄`, `E₆` (constant term
`1`, `EisensteinSeries.E_qExpansion_coeff_zero`) and the discriminant `Δ = η^24` (a cusp form,
nonvanishing on `ℍ`, `ModularForm.discriminant_ne_zero`). We prove
* `kzModularForm_apply`: `F_k(z) = Δ(z)^n E₄(z)^a E₆(z)^b F̃(E₄(z)^3/Δ(z))` (so with
  `j = E₄^3/Δ` this is the manuscript's `Δ^n E₄^a E₆^b F̃(j)`);
* `kzModularForm_qExpansion_coeff_zero`: its Fourier constant term is `c_n`, the leading
  coefficient `A_{n,r}` of `F̃` (`leadingCoeff_kanekoZagierModularPoly`).
The manuscript's `a = (λ+1)/2`, `b = (μ+1)/2`; the statements hold for all `a, b`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial ModularForm UpperHalfPlane

open scoped MatrixGroups

local notation "Δ" => ModularForm.discriminant

/-- The discriminant as a modular form. -/
noncomputable abbrev deltaForm : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem coe_deltaForm : ⇑deltaForm = Δ := by
  rw [← CuspForm.coe_discriminant]; rfl

theorem kzWeight_eq (n a b : ℕ) (i : Fin (n + 1)) :
    ((n - (i : ℕ) : ℕ) : ℤ) * 12 + ((((a + 3 * (i : ℕ) : ℕ) : ℤ) * 4) + ((b : ℕ) : ℤ) * 6) =
      12 * n + 4 * a + 6 * b := by
  have hi := i.isLt
  push_cast [Nat.cast_sub (show (i : ℕ) ≤ n by omega)]
  ring

/-- The `i`-th term `c_i Δ^{n-i} E₄^{a+3i} E₆^b`, of weight `12n + 4a + 6b`. -/
noncomputable def kzModularTerm (l μ : ℤ) (n a b : ℕ) (i : Fin (n + 1)) :
    ModularForm 𝒮ℒ (12 * n + 4 * a + 6 * b) :=
  (((kanekoZagierModularPoly l μ n).coeff i : ℚ) : ℂ) •
    mcast (kzWeight_eq n a b i)
      ((deltaForm.pow (n - i)).mul ((E₄.pow (a + 3 * i)).mul (E₆.pow b)))

/-- **The modular form `F_k = ∑_j c_j Δ^{n-j} E₄^{a+3j} E₆^b`** of weight `12n + 4a + 6b`. -/
noncomputable def kzModularForm (l μ : ℤ) (n a b : ℕ) :
    ModularForm 𝒮ℒ (12 * n + 4 * a + 6 * b) :=
  ∑ i : Fin (n + 1), kzModularTerm l μ n a b i

theorem kzModularTerm_apply (l μ : ℤ) (n a b : ℕ) (i : Fin (n + 1)) (z : ℍ) :
    kzModularTerm l μ n a b i z = (((kanekoZagierModularPoly l μ n).coeff i : ℚ) : ℂ) *
      (Δ z ^ (n - i) * (E₄ z ^ (a + 3 * i) * E₆ z ^ b)) := by
  rw [kzModularTerm, FunLike.coe_smul, Pi.smul_apply, coe_mcast, ModularForm.coe_mul,
    Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_pow, ModularForm.coe_pow,
    ModularForm.coe_pow, Pi.pow_apply, Pi.pow_apply, Pi.pow_apply,
    coe_deltaForm, smul_eq_mul]

theorem kzModularForm_apply_sum (l μ : ℤ) (n a b : ℕ) (z : ℍ) :
    kzModularForm l μ n a b z = ∑ i : Fin (n + 1),
      (((kanekoZagierModularPoly l μ n).coeff i : ℚ) : ℂ) *
        (Δ z ^ (n - i) * (E₄ z ^ (a + 3 * i) * E₆ z ^ b)) := by
  rw [kzModularForm]
  have h : ∀ s : Finset (Fin (n + 1)),
      (∑ i ∈ s, kzModularTerm l μ n a b i) z = ∑ i ∈ s, kzModularTerm l μ n a b i z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, FunLike.coe_add, Pi.add_apply, ih]
  rw [h Finset.univ]
  exact Finset.sum_congr rfl fun i _ => kzModularTerm_apply l μ n a b i z

/-- **§6.4.** `F_k(z) = Δ(z)^n E₄(z)^a E₆(z)^b F̃(E₄(z)^3/Δ(z))`. -/
theorem kzModularForm_apply {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n a b : ℕ) (z : ℍ) :
    kzModularForm l μ n a b z = Δ z ^ n * E₄ z ^ a * E₆ z ^ b *
      ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ)).eval (E₄ z ^ 3 / Δ z) := by
  have hΔ := discriminant_ne_zero z
  have hdeg : ((kanekoZagierModularPoly l μ n).map (algebraMap ℚ ℂ)).natDegree < n + 1 := by
    rw [natDegree_map, natDegree_kanekoZagierModularPoly hμ]; omega
  rw [kzModularForm_apply_sum, eval_eq_sum_range' hdeg, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  rw [coeff_map, eq_ratCast, div_pow, ← pow_mul]
  have hsplit : Δ z ^ n = Δ z ^ (n - i) * Δ z ^ (i : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  rw [hsplit, pow_add]
  field_simp

/-- **§6.4.** The Fourier constant term of `F_k` is `c_n = A_{n,r}`, the leading coefficient
of `F̃_{ℓ-1}`. -/
theorem kzModularForm_qExpansion_coeff_zero {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n a b : ℕ) :
    (qExpansion 1 (kzModularForm l μ n a b)).coeff 0 =
      (((kanekoZagierModularPoly l μ n).leadingCoeff : ℚ) : ℂ) := by
  have hh : (0 : ℝ) < 1 := one_pos
  have hΓ := one_mem_strictPeriods_SL
  have hE4 : (qExpansion 1 E₄).coeff 0 = 1 := EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  have hE6 : (qExpansion 1 E₆).coeff 0 = 1 := EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  have hD : (qExpansion 1 deltaForm).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero (f := CuspForm.discriminant) hh hΓ
  -- constant terms of the summands
  have hterm : ∀ i : Fin (n + 1), (qExpansion 1 (kzModularTerm l μ n a b i)).coeff 0 =
      if (i : ℕ) = n then (((kanekoZagierModularPoly l μ n).coeff i : ℚ) : ℂ) else 0 := by
    intro i
    rw [kzModularTerm, FunLike.coe_smul, ModularForm.qExpansion_smul hh hΓ,
      PowerSeries.coeff_smul]
    have hc : qExpansion 1 (mcast (kzWeight_eq n a b i)
        ((deltaForm.pow (n - i)).mul ((E₄.pow (a + 3 * i)).mul (E₆.pow b)))) =
        qExpansion 1 ((deltaForm.pow (n - i)).mul ((E₄.pow (a + 3 * i)).mul (E₆.pow b))) := by
      rw [qExpansion, qExpansion, coe_mcast]
    rw [hc, ModularForm.qExpansion_mul hh hΓ, ModularForm.qExpansion_mul hh hΓ,
      ModularForm.qExpansion_pow hh hΓ, ModularForm.qExpansion_pow hh hΓ,
      ModularForm.qExpansion_pow hh hΓ, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul, map_mul, map_pow, map_pow, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hD, hE4, hE6, one_pow, one_pow, mul_one, mul_one, smul_eq_mul]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    by_cases hin : (i : ℕ) = n
    · rw [hin]
      simp
    · rw [zero_pow (by omega)]
      simp [hin]
  have hsum : ∀ s : Finset (Fin (n + 1)),
      (qExpansion 1 ⇑(∑ i ∈ s, kzModularTerm l μ n a b i)).coeff 0 =
        ∑ i ∈ s, (qExpansion 1 (kzModularTerm l μ n a b i)).coeff 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [UpperHalfPlane.qExpansion_zero]
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, FunLike.coe_add,
        ModularForm.qExpansion_add hh hΓ, map_add, ih]
  rw [kzModularForm, hsum, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_eq_single (Fin.last n) (fun i _ hi => by
      have h : (i : ℕ) ≠ n := fun h => hi (Fin.ext (by simpa using h))
      simp [h]) (fun h => absurd (Finset.mem_univ _) h)]
  simp [leadingCoeff, natDegree_kanekoZagierModularPoly hμ]

end ArithmeticOfJacobiPolynomials
