/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.IntegralNormalization

/-!
# Simple roots of `P_n^{(α,β)}` for rational parameters (proof of Theorem 1.6)

In the proof of Theorem 1.6 the manuscript says: *"In particular, `α + β = r/D` is not an integer,
so the degree of `P_n^{(α,β)}` is `n`. Its endpoint values are nonzero because neither parameter
is a negative integer. Equation (5.6), over a field of characteristic zero, then also shows that
all its roots are simple."*

This module states and proves that sentence for the source's real parameter domain: `α, β ∈ ℚ`
with `α, β ∉ {-1, -2, …}` (the hypothesis of Theorem 1.6), with no restriction to `α, β > -1` and
no use of the real zeros of Jacobi polynomials (`JacobiSimpleRealZeros` is not used).

* `jacobiP_eval_one_ne_zero`, `jacobiP_eval_neg_one_ne_zero`: the endpoint values are nonzero when
  the corresponding parameter is not a negative integer;
* `rootMultiplicity_map_jacobiP_le_one`, `nodup_roots_map_jacobiP`: over every field `E` of
  characteristic zero containing `ℚ`, every root of `P_n^{(α,β)}` is simple;
* `separable_jacobiP`: `P_n^{(α,β)}` is separable over `ℚ`;
* `natDegree_jacobiP_of_one_lt_den`: if `α + β` is not an integer then `deg P_n^{(α,β)} = n`;
* `jacobiP_source_sentence`: the three assertions together under the hypotheses of the proof of
  Theorem 1.6 (`1 < (α + β).den`, which follows from `D ≥ 2` with `α + β = r/D` in lowest terms).

The argument is the manuscript's: a multiple root `z` of a solution of
`(1 - X²) y'' + [β - α - (α + β + 2) X] y' + n (n + α + β + 1) y = 0` must be a zero of `1 - X²`
(`rootMultiplicity_le_one_of_singular_ode`), i.e. `z = ±1`, and the endpoint values are nonzero.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- `binom(n + α, n) ≠ 0` unless `α` is a negative integer. -/
private theorem ring_choose_add_ne_zero_aux {α : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1)) (n : ℕ) :
    Ring.choose ((n : ℚ) + α) n ≠ 0 := by
  have hp : ∀ m : ℕ, (ascPochhammer ℚ m).eval (α + 1) ≠ 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ascPochhammer_succ_eval]
      refine mul_ne_zero ih fun h => hα m ?_
      linarith
  intro h
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose ((n : ℚ) + α) n
  rw [h, smul_zero, descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval] at h1
  apply hp n
  rw [show α + 1 = (n : ℚ) + α - n + 1 by ring]
  exact h1

/-- `P_n^{(α,β)}(1) ≠ 0` when `α` is not a negative integer. -/
theorem jacobiP_eval_one_ne_zero {α : ℚ} (β : ℚ) (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1)) (n : ℕ) :
    (jacobiP α β n).eval 1 ≠ 0 := by
  rw [jacobiP_eval_one]
  exact ring_choose_add_ne_zero_aux hα n

/-- `P_n^{(α,β)}(-1) ≠ 0` when `β` is not a negative integer. -/
theorem jacobiP_eval_neg_one_ne_zero (α : ℚ) {β : ℚ} (hβ : ∀ k : ℕ, β ≠ -((k : ℚ) + 1)) (n : ℕ) :
    (jacobiP α β n).eval (-1) ≠ 0 := by
  rw [jacobiP_eval_neg_one]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ring_choose_add_ne_zero_aux hβ n)

/-- Evaluation commutes with the map `ℚ → E`. -/
private theorem eval_map_algebraMap_aux (E : Type*) [Field E] [Algebra ℚ E] (p : ℚ[X]) (x : ℚ) :
    (p.map (algebraMap ℚ E)).eval (algebraMap ℚ E x) = algebraMap ℚ E (p.eval x) := by
  rw [eval_map, eval₂_at_apply]

/-- The differential equation `(5.6)` over `E`, in the form `A K'' + B K' = c K`. -/
private theorem jacobiP_map_ode (α β : ℚ) (n : ℕ) (E : Type*) [Field E] [Algebra ℚ E] :
    (1 - X ^ 2 : E[X]) * derivative (derivative ((jacobiP α β n).map (algebraMap ℚ E))) +
      (C (algebraMap ℚ E (β - α)) - C (algebraMap ℚ E (α + β + 2)) * X) *
        derivative ((jacobiP α β n).map (algebraMap ℚ E)) =
      C (-(algebraMap ℚ E ((n : ℚ) * (n + α + β + 1)))) *
        (jacobiP α β n).map (algebraMap ℚ E) := by
  have h := congrArg (Polynomial.map (algebraMap ℚ E)) (jacobiP_ode α β n)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← derivative_map,
    Polynomial.map_zero] at h
  rw [C_neg]
  linear_combination h

/-- **Every root of `P_n^{(α,β)}` is simple**, over every field `E ⊇ ℚ` (of characteristic zero),
for rational `α, β` that are not negative integers. -/
theorem rootMultiplicity_map_jacobiP_le_one {α β : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1))
    (hβ : ∀ k : ℕ, β ≠ -((k : ℚ) + 1)) (n : ℕ) (E : Type*) [Field E] [Algebra ℚ E] (z : E) :
    ((jacobiP α β n).map (algebraMap ℚ E)).rootMultiplicity z ≤ 1 := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ E).injective
  have h1 : ((jacobiP α β n).map (algebraMap ℚ E)).eval 1 ≠ 0 := by
    have := eval_map_algebraMap_aux E (jacobiP α β n) 1
    rw [map_one] at this
    rw [this]
    exact (_root_.map_ne_zero _).mpr (jacobiP_eval_one_ne_zero β hα n)
  have hm1 : ((jacobiP α β n).map (algebraMap ℚ E)).eval (-1) ≠ 0 := by
    have := eval_map_algebraMap_aux E (jacobiP α β n) (-1)
    rw [map_neg, map_one] at this
    rw [this]
    exact (_root_.map_ne_zero _).mpr (jacobiP_eval_neg_one_ne_zero α hβ n)
  have hK0 : (jacobiP α β n).map (algebraMap ℚ E) ≠ 0 := fun h0 => h1 (by rw [h0, eval_zero])
  refine rootMultiplicity_le_one_of_singular_ode hK0 (jacobiP_map_ode α β n E) ?_ ?_ z
  · intro m hm _
    exact Nat.cast_ne_zero.mpr (by omega)
  · intro w hw
    simp only [eval_sub, eval_one, eval_pow, eval_X] at hw
    have hw' : (w - 1) * (w + 1) = 0 := by linear_combination -hw
    rcases mul_eq_zero.mp hw' with h | h
    · rw [show w = 1 by linear_combination h]; exact h1
    · rw [show w = -1 by linear_combination h]; exact hm1

/-- Over every field `E ⊇ ℚ`, the roots of `P_n^{(α,β)}` (with multiplicity) have no repeats. -/
theorem nodup_roots_map_jacobiP {α β : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1))
    (hβ : ∀ k : ℕ, β ≠ -((k : ℚ) + 1)) (n : ℕ) (E : Type*) [Field E] [Algebra ℚ E] :
    ((jacobiP α β n).map (algebraMap ℚ E)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  rw [count_roots]
  exact rootMultiplicity_map_jacobiP_le_one hα hβ n E z

/-- `P_n^{(α,β)}` is separable over `ℚ` for rational `α, β` that are not negative integers. -/
theorem separable_jacobiP {α β : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1))
    (hβ : ∀ k : ℕ, β ≠ -((k : ℚ) + 1)) (n : ℕ) : (jacobiP α β n).Separable := by
  classical
  have h1 : (jacobiP α β n).eval 1 ≠ 0 := jacobiP_eval_one_ne_zero β hα n
  have hf0 : jacobiP α β n ≠ 0 := fun h0 => h1 (by rw [h0, eval_zero])
  have hK0 : (jacobiP α β n).map (algebraMap ℚ (AlgebraicClosure ℚ)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr hf0
  have hsep : ((jacobiP α β n).map (algebraMap ℚ (AlgebraicClosure ℚ))).Separable := by
    rw [← nodup_roots_iff_of_splits hK0 (IsAlgClosed.splits _)]
    exact nodup_roots_map_jacobiP hα hβ n _
  exact (separable_map (algebraMap ℚ (AlgebraicClosure ℚ))).mp hsep

/-- `deg P_n^{(α,β)} = n` when `α + β` is not an integer. -/
theorem natDegree_jacobiP_of_one_lt_den {α β : ℚ} (hden : 1 < (α + β).den) (n : ℕ) :
    (jacobiP α β n).natDegree = n := by
  refine natDegree_jacobiP α β n ?_
  have hk : ∀ k : ℕ, (n : ℚ) + α + β ≠ -((k : ℚ) + 1) := by
    intro k hk
    have hint : α + β = (((-(k : ℤ) - 1 - n : ℤ)) : ℚ) := by push_cast; linarith
    have := congrArg Rat.den hint
    rw [Rat.den_intCast] at this
    omega
  have := ring_choose_add_ne_zero_aux hk n
  rwa [show (n : ℚ) + ((n : ℚ) + α + β) = 2 * (n : ℚ) + α + β by ring] at this

/-- **The sentence of the proof of Theorem 1.6.** For rational `α, β`, neither a negative integer,
with `α + β` not an integer (this holds when `α + β = r/D` in lowest terms with `D ≥ 2`): the degree
of `P_n^{(α,β)}` is `n`, its endpoint values at `1` and `-1` are nonzero, and all of its roots are
simple over every field of characteristic zero containing `ℚ`; in particular it is separable. -/
theorem jacobiP_source_sentence {α β : ℚ} (hα : ∀ k : ℕ, α ≠ -((k : ℚ) + 1))
    (hβ : ∀ k : ℕ, β ≠ -((k : ℚ) + 1)) (hden : 1 < (α + β).den) (n : ℕ) :
    (jacobiP α β n).natDegree = n ∧ (jacobiP α β n).eval 1 ≠ 0 ∧ (jacobiP α β n).eval (-1) ≠ 0 ∧
      (∀ (E : Type) [Field E] [Algebra ℚ E],
        ((jacobiP α β n).map (algebraMap ℚ E)).roots.Nodup) ∧ (jacobiP α β n).Separable :=
  ⟨natDegree_jacobiP_of_one_lt_den hden n, jacobiP_eval_one_ne_zero β hα n,
    jacobiP_eval_neg_one_ne_zero α hβ n, fun E _ _ => nodup_roots_map_jacobiP hα hβ n E,
    separable_jacobiP hα hβ n⟩

/-- The hypotheses are satisfiable beyond `α, β > -1`: for `α = -3/2` (not a negative integer) and
`β = 1/3`, `P_n^{(-3/2,1/3)}` is separable of degree `n`. -/
theorem jacobiP_source_sentence_example (n : ℕ) :
    (jacobiP (-3 / 2) (1 / 3) n).natDegree = n ∧ (jacobiP (-3 / 2) (1 / 3) n).Separable := by
  have hα : ∀ k : ℕ, (-3 / 2 : ℚ) ≠ -((k : ℚ) + 1) := by
    intro k hk
    have h2 : (2 * (k : ℚ) + 2) = 3 := by linarith
    have h3 : (2 * (k : ℤ) + 2 = 3) := by exact_mod_cast h2
    omega
  have hβ : ∀ k : ℕ, (1 / 3 : ℚ) ≠ -((k : ℚ) + 1) := by
    intro k hk
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith
  have hden : 1 < ((-3 / 2 : ℚ) + 1 / 3).den := by
    by_contra h
    have h1 : ((-3 / 2 : ℚ) + 1 / 3).den = 1 := by
      have := Rat.den_pos ((-3 / 2 : ℚ) + 1 / 3)
      omega
    have h2 := (Rat.den_eq_one_iff _).mp h1
    have h3 : (6 : ℚ) * (((-3 / 2 : ℚ) + 1 / 3).num : ℚ) = -7 := by
      rw [h2]; norm_num
    have h4 : 6 * ((-3 / 2 : ℚ) + 1 / 3).num = -7 := by exact_mod_cast h3
    omega
  exact ⟨natDegree_jacobiP_of_one_lt_den hden n, separable_jacobiP hα hβ n⟩

end ArithmeticOfJacobiPolynomials
