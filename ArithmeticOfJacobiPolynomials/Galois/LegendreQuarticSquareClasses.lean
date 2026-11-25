/- Assembled by AxiomProver. -/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Square classes in `ℚ(√70)` for the exceptional Legendre quartic

The exceptional case `(n, δ) = (2, 1)` of Theorem 5.9 concerns `63X⁴ - 70X² + 15`. Its squared
roots `y_± = (35 ± 2√70)/63` lie in `K = ℚ(√70)`, and `y_+ y_- = 5/21`. The manuscript shows that
`y_+`, `y_-` and `y_+ y_-` are not squares in `K`: a square in `K` has norm a rational square,
and a rational `q` is a square in `K` only if `q` or `q/70` is a rational square, which fails for
`5/21` and `1/294`.

Here `s = √70` is a square root of `70` in any field `E` of characteristic zero; `InK s z` says
that `z` lies in `ℚ(s)`, i.e. `z = α + β s` with rational `α, β`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace LegendreQuartic

section Rational

private theorem not_isSquare_nat_aux {n : ℕ} (hn : ¬ IsSquare n) : ¬ IsSquare ((n : ℕ) : ℚ) := by
  rwa [Rat.isSquare_natCast_iff]

private theorem not_isSquare_nat_70 : ¬ IsSquare (70 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 9 := by nlinarith
  interval_cases r <;> omega

private theorem not_isSquare_nat_105 : ¬ IsSquare (105 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 11 := by nlinarith
  interval_cases r <;> omega

private theorem not_isSquare_nat_294 : ¬ IsSquare (294 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 18 := by nlinarith
  interval_cases r <;> omega

theorem not_isSquare_seventy : ¬ IsSquare (70 : ℚ) := by
  have := not_isSquare_nat_aux not_isSquare_nat_70
  simpa using this

theorem not_isSquare_five_div_twentyone : ¬ IsSquare (5 / 21 : ℚ) := by
  rintro ⟨r, hr⟩
  apply not_isSquare_nat_aux not_isSquare_nat_105
  refine ⟨21 * r, ?_⟩
  push_cast
  linear_combination (441 : ℚ) * hr

theorem not_isSquare_one_div_294 : ¬ IsSquare (1 / 294 : ℚ) := by
  rintro ⟨r, hr⟩
  apply not_isSquare_nat_aux not_isSquare_nat_294
  refine ⟨294 * r, ?_⟩
  push_cast
  linear_combination (86436 : ℚ) * hr

end Rational

section Field

variable {E : Type*} [Field E] [CharZero E] {s : E}

/-- `z` lies in `ℚ(s)`, i.e. `z = α + β s` with `α, β` rational. -/
def InK (s z : E) : Prop := ∃ α β : ℚ, z = (α : E) + (β : E) * s

omit [CharZero E] in
theorem inK_of_rat (q : ℚ) : InK s (q : E) := ⟨q, 0, by simp⟩

omit [CharZero E] in
theorem inK_self : InK s s := ⟨0, 1, by simp⟩

theorem InK.add {z w : E} (hz : InK s z) (hw : InK s w) : InK s (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩

omit [CharZero E] in
theorem InK.neg {z : E} (hz : InK s z) : InK s (-z) := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨-a, -b, by push_cast; ring⟩

theorem InK.sub {z w : E} (hz : InK s z) (hw : InK s w) : InK s (z - w) := by
  rw [sub_eq_add_neg]; exact hz.add hw.neg

theorem InK.mul (hs : s ^ 2 = 70) {z w : E} (hz : InK s z) (hw : InK s w) : InK s (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  refine ⟨a * c + 70 * (b * d), a * d + b * c, ?_⟩
  push_cast
  linear_combination (b : E) * d * hs

theorem InK.smul_rat (q : ℚ) {z : E} (hz : InK s z) : InK s ((q : E) * z) := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨q * a, q * b, by push_cast; ring⟩

/-- `1` and `s` are linearly independent over `ℚ` when `s² = 70`. -/
theorem rat_add_mul_eq_zero (hs : s ^ 2 = 70) {α β : ℚ} (h : (α : E) + (β : E) * s = 0) :
    α = 0 ∧ β = 0 := by
  have hβ : β = 0 := by
    by_contra hβ
    have hβE : (β : E) ≠ 0 := by exact_mod_cast hβ
    obtain ⟨γ, hγ⟩ : ∃ γ : ℚ, γ = α / β := ⟨_, rfl⟩
    have hγE : (γ : E) = (α : E) / β := by rw [hγ]; push_cast; ring
    have hsq : s = -(γ : E) := by
      rw [hγE]
      field_simp
      linear_combination h
    have h3 : (γ : E) ^ 2 = 70 := by
      rw [hsq] at hs
      linear_combination hs
    have h2 : γ * γ = 70 := by
      have h4 : ((γ * γ : ℚ) : E) = ((70 : ℚ) : E) := by
        push_cast
        linear_combination h3
      exact Rat.cast_injective h4
    exact not_isSquare_seventy ⟨γ, h2.symm⟩
  subst hβ
  refine ⟨?_, rfl⟩
  have : (α : E) = 0 := by simpa using h
  exact_mod_cast this

theorem InK.inv (hs : s ^ 2 = 70) {z : E} (hz : InK s z) (hz0 : z ≠ 0) :
    ∃ w : E, InK s w ∧ z * w = 1 := by
  obtain ⟨a, b, rfl⟩ := hz
  have hN : ((a * a - 70 * (b * b) : ℚ) : E) ≠ 0 := by
    intro h
    apply hz0
    push_cast at h
    have h1 : ((a : E) + b * s) * ((a : E) - b * s) = 0 := by
      linear_combination h - (b : E) ^ 2 * hs
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact h1
    · have := rat_add_mul_eq_zero hs (α := a) (β := -b) (by push_cast; linear_combination h1)
      obtain ⟨rfl, hb⟩ := this
      have : b = 0 := by linarith
      subst this
      simp
  refine ⟨((a * a - 70 * (b * b) : ℚ) : E)⁻¹ * ((a : E) - b * s), ?_, ?_⟩
  · refine ⟨(a * a - 70 * (b * b))⁻¹ * a, (a * a - 70 * (b * b))⁻¹ * (-b), ?_⟩
    push_cast
    ring
  · have hcast : ((a * a - 70 * (b * b) : ℚ) : E) = (a : E) * a - 70 * (b * b) := by
      push_cast; ring
    rw [hcast] at hN ⊢
    have h1 : ((a : E) + b * s) * ((a : E) - b * s) = (a : E) * a - 70 * (b * b) := by
      linear_combination (-(b : E) ^ 2) * hs
    calc ((a : E) + b * s) * (((a : E) * a - 70 * (b * b))⁻¹ * ((a : E) - b * s))
        = ((a : E) * a - 70 * (b * b))⁻¹ * (((a : E) + b * s) * ((a : E) - b * s)) := by ring
      _ = 1 := by rw [h1, inv_mul_cancel₀ hN]

/-- `y_+ = (35 + 2s)/63` is not a square in `ℚ(s)`: its norm `5/21` would be a rational square. -/
theorem not_sq_yPlus (hs : s ^ 2 = 70) {α β : ℚ} :
    ((α : E) + β * s) ^ 2 ≠ (35 + 2 * s) / 63 := by
  intro h
  have h0 : ((α * α + 70 * (β * β) - 5 / 9 : ℚ) : E) + ((2 * α * β - 2 / 63 : ℚ) : E) * s = 0 := by
    push_cast
    linear_combination h - (β : E) ^ 2 * hs
  obtain ⟨e1, e2⟩ := rat_add_mul_eq_zero hs h0
  apply not_isSquare_five_div_twentyone
  refine ⟨α * α - 70 * (β * β), ?_⟩
  linear_combination (-(α * α + 70 * (β * β) + 5 / 9)) * e1 + 280 * (α * β + 1 / 63) * (e2 / 2)

/-- `y_- = (35 - 2s)/63` is not a square in `ℚ(s)`. -/
theorem not_sq_yMinus (hs : s ^ 2 = 70) {α β : ℚ} :
    ((α : E) + β * s) ^ 2 ≠ (35 - 2 * s) / 63 := by
  intro h
  have h0 : ((α * α + 70 * (β * β) - 5 / 9 : ℚ) : E) + ((2 * α * β + 2 / 63 : ℚ) : E) * s = 0 := by
    push_cast
    linear_combination h - (β : E) ^ 2 * hs
  obtain ⟨e1, e2⟩ := rat_add_mul_eq_zero hs h0
  apply not_isSquare_five_div_twentyone
  refine ⟨α * α - 70 * (β * β), ?_⟩
  linear_combination (-(α * α + 70 * (β * β) + 5 / 9)) * e1 + 280 * (α * β - 1 / 63) * (e2 / 2)

/-- `y_+ y_- = 5/21` is not a square in `ℚ(s)`: neither `5/21` nor `(5/21)/70 = 1/294` is a
rational square. -/
theorem not_sq_five_div_twentyone (hs : s ^ 2 = 70) {α β : ℚ} :
    ((α : E) + β * s) ^ 2 ≠ 5 / 21 := by
  intro h
  have h0 : ((α * α + 70 * (β * β) - 5 / 21 : ℚ) : E) + ((2 * α * β : ℚ) : E) * s = 0 := by
    push_cast
    linear_combination h - (β : E) ^ 2 * hs
  obtain ⟨e1, e2⟩ := rat_add_mul_eq_zero hs h0
  have hab : α = 0 ∨ β = 0 := by
    rcases mul_eq_zero.mp (show α * β = 0 by linarith) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hab with rfl | rfl
  · apply not_isSquare_one_div_294
    refine ⟨β, ?_⟩
    linear_combination (-1 / 70 : ℚ) * e1
  · apply not_isSquare_five_div_twentyone
    refine ⟨α, ?_⟩
    linear_combination (-1 : ℚ) * e1

theorem inK_yPlus : InK s ((35 + 2 * s) / 63) :=
  ⟨35 / 63, 2 / 63, by push_cast; ring⟩

theorem inK_yMinus : InK s ((35 - 2 * s) / 63) :=
  ⟨35 / 63, -(2 / 63), by push_cast; ring⟩

variable {x x' : E}

/-- A square root `x` of `y_+` does not lie in `ℚ(s)`. -/
theorem not_inK_x (hs : s ^ 2 = 70) (hx : x ^ 2 = (35 + 2 * s) / 63) : ¬ InK s x := by
  rintro ⟨α, β, rfl⟩
  exact not_sq_yPlus hs hx

/-- The two independent square classes: a square root `x'` of `y_-` is not of the form
`A + B x` with `A, B ∈ ℚ(s)`, for a square root `x` of `y_+`. -/
theorem ne_add_mul (hs : s ^ 2 = 70) (hx : x ^ 2 = (35 + 2 * s) / 63)
    (hx' : x' ^ 2 = (35 - 2 * s) / 63) {A B : E} (hA : InK s A) (hB : InK s B) :
    x' ≠ A + B * x := by
  intro h
  have hsq : x' ^ 2 = A * A + B * B * x ^ 2 + 2 * (A * B) * x := by rw [h]; ring
  by_cases hAB : A * B = 0
  · rcases mul_eq_zero.mp hAB with hA0 | hB0
    · -- `x' = B x`: then `y_+ y_- = (B y_+)²`
      subst hA0
      obtain ⟨α, β, hαβ⟩ : InK s (B * ((35 + 2 * s) / 63)) := hB.mul hs (inK_yPlus)
      refine not_sq_five_div_twentyone hs (α := α) (β := β) ?_
      rw [← hαβ]
      have h1 : (35 - 2 * s) / 63 = B * B * ((35 + 2 * s) / 63) := by
        rw [← hx', ← hx, hsq]; ring
      linear_combination (-((35 + 2 * s) / 63)) * h1 + (-4 / 3969 : E) * hs
    · -- `x' = A`: then `y_-` is a square in `ℚ(s)`
      subst hB0
      obtain ⟨α, β, rfl⟩ := hA
      refine not_sq_yMinus hs (α := α) (β := β) ?_
      rw [← hx', hsq]; ring
  · obtain ⟨w, hw, hAw⟩ := InK.inv hs (hA.mul hs hB) hAB
    have hc : InK s ((35 - 2 * s) / 63 - A * A - B * B * ((35 + 2 * s) / 63)) :=
      (inK_yMinus.sub (hA.mul hs hA)).sub ((hB.mul hs hB).mul hs (inK_yPlus))
    have hK : InK s (((1 / 2 : ℚ) : E) * ((((35 - 2 * s) / 63 - A * A -
        B * B * ((35 + 2 * s) / 63))) * w)) := InK.smul_rat _ (hc.mul hs hw)
    apply not_inK_x hs hx
    convert hK using 1
    rw [← hx', ← hx]
    have hcx : x' ^ 2 - A * A - B * B * x ^ 2 = 2 * (A * B) * x := by rw [hsq]; ring
    rw [hcx]
    push_cast
    linear_combination (-x) * hAw

/-- `1, x, x², x³` are linearly independent over `ℚ`, for a square root `x` of `y_+`. -/
theorem powers_linearIndependent (hs : s ^ 2 = 70) (hx : x ^ 2 = (35 + 2 * s) / 63)
    {c₀ c₁ c₂ c₃ : ℚ}
    (h : (c₀ : E) + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have hA : InK s ((c₀ : E) + c₂ * ((35 + 2 * s) / 63)) :=
    (inK_of_rat c₀).add ((inK_of_rat c₂).mul hs inK_yPlus)
  have hB : InK s ((c₁ : E) + c₃ * ((35 + 2 * s) / 63)) :=
    (inK_of_rat c₁).add ((inK_of_rat c₃).mul hs inK_yPlus)
  have hrel : ((c₀ : E) + c₂ * ((35 + 2 * s) / 63)) +
      ((c₁ : E) + c₃ * ((35 + 2 * s) / 63)) * x = 0 := by
    rw [← hx]; linear_combination h
  have hB0 : (c₁ : E) + c₃ * ((35 + 2 * s) / 63) = 0 := by
    by_contra hne
    obtain ⟨w, hw, hBw⟩ := InK.inv hs hB hne
    apply not_inK_x hs hx
    have hxe : x = -(((c₀ : E) + c₂ * ((35 + 2 * s) / 63)) * w) := by
      linear_combination w * hrel + (-x) * hBw
    rw [hxe]
    exact (hA.mul hs hw).neg
  have hA0 : (c₀ : E) + c₂ * ((35 + 2 * s) / 63) = 0 := by
    rw [hB0, zero_mul, add_zero] at hrel; exact hrel
  have key : ∀ u v : ℚ, (u : E) + v * ((35 + 2 * s) / 63) = 0 → u = 0 ∧ v = 0 := by
    intro u v huv
    have h1 : ((u + 35 * v / 63 : ℚ) : E) + ((2 * v / 63 : ℚ) : E) * s = 0 := by
      push_cast; linear_combination huv
    obtain ⟨e1, e2⟩ := rat_add_mul_eq_zero hs h1
    have hv : v = 0 := by linarith
    refine ⟨by rw [hv] at e1; linarith, hv⟩
  obtain ⟨h0, h2⟩ := key _ _ hA0
  obtain ⟨h1, h3⟩ := key _ _ hB0
  exact ⟨h0, h1, h2, h3⟩

end Field


end LegendreQuartic

end ArithmeticOfJacobiPolynomials
