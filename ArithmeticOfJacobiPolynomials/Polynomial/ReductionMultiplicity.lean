/- Assembled by AxiomProver. -/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Multiple roots of solutions of second-order differential equations in characteristic `p`

The manuscript repeatedly uses the following observation (proofs of Lemmas 3.3 and 4.3 and of
(3.12)): if a polynomial `y` over a field satisfies `σ y'' + τ y' + Λ y = 0` and has a root `ξ`
of multiplicity `t ≥ 2` with `σ(ξ) ≠ 0`, then the lowest-order term of the equation at `ξ` is
`σ(ξ) t (t-1) g(ξ) (X - ξ)^{t-2}`, where `y = (X - ξ)^t g`. Hence `t (t-1) = 0` in the field.
In characteristic `p` this forces `t ≥ p`; in particular a nonzero solution of degree `< p` has
no multiple root off the zeros of `σ`.

We also record the parity variant used for (3.12): if moreover `y(-X) = ± y(X)`, `ξ ≠ -ξ`, then
`(X - ξ)^t (X + ξ)^t ∣ y`, so `2p ≤ deg y`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {K : Type*} [Field K]

/-- The lowest-order term of `σ y'' + τ y' + Λ y` at a root `ξ` of multiplicity `t ≥ 2` of `y`
with `σ(ξ) ≠ 0` is a nonzero multiple of `t (t-1)`; hence `t (t-1) = 0` in `K`. -/
theorem ode_rootMultiplicity_mul_pred_eq_zero {σ τ y : K[X]} {Λ : K}
    (hode : σ * derivative (derivative y) + τ * derivative y + C Λ * y = 0)
    (hy : y ≠ 0) {ξ : K} (hσ : σ.eval ξ ≠ 0) (ht : 2 ≤ y.rootMultiplicity ξ) :
    ((y.rootMultiplicity ξ * (y.rootMultiplicity ξ - 1) : ℕ) : K) = 0 := by
  obtain ⟨g, hyg, hg⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd y hy ξ
  have hgξ : g.eval ξ ≠ 0 := by rwa [dvd_iff_isRoot] at hg
  generalize y.rootMultiplicity ξ = t at *
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  subst hyg
  have hu : derivative (X - C ξ) = 1 := by simp
  have h1 : derivative ((X - C ξ) ^ (s + 2) * g) =
      (X - C ξ) ^ (s + 1) * (C ((s : K) + 2) * g + (X - C ξ) * derivative g) := by
    rw [derivative_mul, derivative_pow, hu, show s + 2 - 1 = s + 1 from rfl]
    simp only [C_add, C_ofNat, Nat.cast_add, Nat.cast_ofNat, mul_one, C_eq_natCast]
    ring
  have h2 : derivative (derivative ((X - C ξ) ^ (s + 2) * g)) =
      (X - C ξ) ^ s * (C (((s : K) + 2) * ((s : K) + 1)) * g +
        (X - C ξ) * (C (2 * ((s : K) + 2)) * derivative g +
          (X - C ξ) * derivative (derivative g))) := by
    rw [h1, derivative_mul, derivative_pow, hu, derivative_add, derivative_mul,
      derivative_mul, hu, derivative_C, show s + 1 - 1 = s from rfl]
    simp only [C_add, C_mul, C_ofNat, C_eq_natCast, Nat.cast_add, Nat.cast_one, C_1,
      mul_one, zero_mul, zero_add, one_mul]
    ring
  rw [h2, h1] at hode
  have key : (X - C ξ) ^ s * (σ * (C (((s : K) + 2) * ((s : K) + 1)) * g +
        (X - C ξ) * (C (2 * ((s : K) + 2)) * derivative g +
          (X - C ξ) * derivative (derivative g))) +
      τ * (X - C ξ) * (C ((s : K) + 2) * g + (X - C ξ) * derivative g) +
      C Λ * (X - C ξ) ^ 2 * g) = 0 := by
    rw [← hode]; ring
  have hQ := (mul_eq_zero.mp key).resolve_left (pow_ne_zero _ (X_sub_C_ne_zero ξ))
  have hev := congrArg (eval ξ) hQ
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, mul_zero,
    add_zero, eval_pow, eval_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hev
  have hs : ((s : K) + 2) * ((s : K) + 1) = 0 := by
    rcases mul_eq_zero.mp hev with h | h
    · exact absurd h hσ
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hgξ
  rw [show s + 2 - 1 = s + 1 by omega]
  push_cast
  exact hs

/-- In characteristic `p`, a root of multiplicity at least `2` of a nonzero solution of
`σ y'' + τ y' + Λ y = 0` at which `σ` does not vanish has multiplicity at least `p`. -/
theorem prime_le_rootMultiplicity_of_ode (p : ℕ) [CharP K p] (hp : p.Prime)
    {σ τ y : K[X]} {Λ : K}
    (hode : σ * derivative (derivative y) + τ * derivative y + C Λ * y = 0)
    (hy : y ≠ 0) {ξ : K} (hσ : σ.eval ξ ≠ 0) (ht : 2 ≤ y.rootMultiplicity ξ) :
    p ≤ y.rootMultiplicity ξ := by
  have h := ode_rootMultiplicity_mul_pred_eq_zero hode hy hσ ht
  rw [CharP.cast_eq_zero_iff K p] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Nat.le_of_dvd (by omega) h
  · have := Nat.le_of_dvd (by omega) h; omega

/-- The multiplicity of a root is at most the degree. -/
theorem rootMultiplicity_le_natDegree_of_ne_zero {y : K[X]} (hy : y ≠ 0) (ξ : K) :
    y.rootMultiplicity ξ ≤ y.natDegree := by
  have h := (le_rootMultiplicity_iff hy (a := ξ)).mp le_rfl
  have := natDegree_le_of_dvd h hy
  rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this

/-- **Mod-`p` multiplicity lemma.** In characteristic `p`, a nonzero polynomial of degree `< p`
satisfying `σ y'' + τ y' + Λ y = 0` has no multiple root off the zeros of `σ`. -/
theorem rootMultiplicity_le_one_of_ode (p : ℕ) [CharP K p] (hp : p.Prime)
    {σ τ y : K[X]} {Λ : K}
    (hode : σ * derivative (derivative y) + τ * derivative y + C Λ * y = 0)
    (hy : y ≠ 0) (hdeg : y.natDegree < p) {ξ : K} (hσ : σ.eval ξ ≠ 0) :
    y.rootMultiplicity ξ ≤ 1 := by
  by_contra h
  have := prime_le_rootMultiplicity_of_ode p hp hode hy hσ (by omega)
  have := rootMultiplicity_le_natDegree_of_ne_zero hy ξ
  omega

/-- A root of a polynomial of fixed parity yields a root of the same multiplicity at its
negative: if `y(-X) = ε y(X)` with `ε ≠ 0` and `(X - ξ)^t ∣ y`, then `(X + ξ)^t ∣ y`. -/
theorem pow_X_sub_C_neg_dvd_of_comp_neg {y : K[X]} {ε : K} (hε : ε ≠ 0)
    (hpar : y.comp (-X) = C ε * y) {ξ : K} {t : ℕ} (h : (X - C ξ) ^ t ∣ y) :
    (X - C (-ξ)) ^ t ∣ y := by
  obtain ⟨g, rfl⟩ := h
  have hc : ((X - C ξ) ^ t * g).comp (-X) = C ((-1) ^ t) * (X - C (-ξ)) ^ t * g.comp (-X) := by
    have e : (-X - C ξ : K[X]) = C (-1) * (X - C (-ξ)) := by simp only [C_neg, C_1]; ring
    rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, e, mul_pow, C_pow]
  rw [hpar] at hc
  have : (X - C (-ξ)) ^ t ∣ C ε * ((X - C ξ) ^ t * g) :=
    ⟨C ((-1) ^ t) * g.comp (-X), by rw [hc]; ring⟩
  exact (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hε)).dvd_mul_left.mp this

/-- **Parity variant.** In characteristic `p`, let `y ≠ 0` satisfy `σ y'' + τ y' + Λ y = 0`
and `y(-X) = ε y(X)` with `ε ≠ 0`. If `ξ ≠ -ξ` is a multiple root of `y` with `σ(ξ) ≠ 0`, then
`2p ≤ deg y`. -/
theorem two_mul_prime_le_natDegree_of_ode_of_parity (p : ℕ) [CharP K p] (hp : p.Prime)
    {σ τ y : K[X]} {Λ ε : K}
    (hode : σ * derivative (derivative y) + τ * derivative y + C Λ * y = 0)
    (hy : y ≠ 0) (hε : ε ≠ 0) (hpar : y.comp (-X) = C ε * y) {ξ : K} (hξ : ξ ≠ -ξ)
    (hσ : σ.eval ξ ≠ 0) (ht : 2 ≤ y.rootMultiplicity ξ) :
    2 * p ≤ y.natDegree := by
  have hpt := prime_le_rootMultiplicity_of_ode p hp hode hy hσ ht
  set t := y.rootMultiplicity ξ
  have h1 : (X - C ξ) ^ t ∣ y := (le_rootMultiplicity_iff hy).mp le_rfl
  have h2 := pow_X_sub_C_neg_dvd_of_comp_neg hε hpar h1
  have hcop : IsCoprime ((X - C ξ) ^ t) ((X - C (-ξ)) ^ t) :=
    (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hξ))).pow
  have h3 := hcop.mul_dvd h1 h2
  have := natDegree_le_of_dvd h3 hy
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C] at this
  omega

end ArithmeticOfJacobiPolynomials
