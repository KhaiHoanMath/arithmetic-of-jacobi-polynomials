/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.InertiaCycle
public import ArithmeticOfJacobiPolynomials.Galois.SourceInertiaCycleGlobal
public import ArithmeticOfJacobiPolynomials.Galois.AffineTransport
public import ArithmeticOfJacobiPolynomials.Jacobi.IntegralNormalization

/-!
# Inertia cycles in Galois groups of Jacobi polynomials (Proposition 5.2)

Under the hypotheses `JacobiCycleHypotheses p n a u b v D r` of Proposition 5.2, with
`k₀ = (p - r)/D - n` and `d = n - k₀ + 1`, the Galois group of
`P_n^{(a/u, b/v)}` over `ℚ` contains a single `d`-cycle, and for `c ∈ ℚ^×` with `v_p(c) = 0`
and `2d < p` the Galois group of `P_n^{(a/u, b/v)}(1 + cX²)` contains a single `2d`-cycle whose
`d`-th power negates every root it moves.

These are global statements about `Gal(P_n/ℚ)`: the Lean conclusions record that the cycle lies
in the Galois group, not that it lies in a specified inertia subgroup at `p` (the manuscript's
proof produces it inside inertia). The inertia forms, with the cycle in the inertia subgroup of
a prime above `p`, are `exists_isCycle_galPerm_jacobiP_mem_inertia` and
`exists_isCycle_galPerm_jacobiP_comp_mem_inertia`
(ArithmeticOfJacobiPolynomials/Galois/InertiaMembership.lean).

The first assertion uses `d ≥ 2`. At `d = 1` the manuscript's single `1`-cycle is the identity.
The proof applies Lemma 5.1 (`SourceInertia.exists_isCycle_galPerm`,
`SourceInertia.exists_isCycle_galPerm_comp`) to the integral normalization `K_n` of ((5.5),
§5.1) and transports the
cycle along the affine change of variables.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

open Classical in
/-- **Proposition 5.2, first assertion.** Under the hypotheses of Proposition 5.2, with
`d = n + 1 - k₀ ≥ 2`, some element of `Gal(P_n^{(a/u,b/v)}/ℚ)` acts on the roots as a single
`d`-cycle. The quadratic-substitution assertion below covers `d ≥ 1` and gives a transposition
of one opposite pair when `d = 1`. -/
theorem exists_isCycle_galPerm_jacobiP {p n : ℕ} {a u b v D r : ℤ}
    (h : JacobiCycleHypotheses p n a u b v D r)
    (hd : 2 ≤ n + 1 - jacobiCycleIndexNat p n D r) :
    ∃ σ : (jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).Gal,
      (galPerm _ σ).IsCycle ∧
      (galPerm _ σ).support.card = n + 1 - jacobiCycleIndexNat p n D r := by
  obtain ⟨-, -, h3, -, h0, hlc, hlc2, hdeg, hsq⟩ := h.localCycle_hypotheses
  obtain ⟨τ, hτ, hcard⟩ := SourceInertia.exists_isCycle_galPerm h.prime hd h3 h0 hlc hlc2 hdeg hsq
  exact exists_isCycle_galPerm_jacobiP_of_integralJacobi a u D r ((b : ℚ) / v) n
    h.u_pos.ne' h.D_pos.ne' h.r_eq τ hτ hcard

/-- A nonzero rational of `p`-adic valuation `0` has numerator and denominator prime to `p`. -/
theorem not_dvd_num_mul_den_of_padicValRat_eq_zero {p : ℕ} [hp : Fact p.Prime] {q : ℚ}
    (hq : q ≠ 0) (hv : padicValRat p q = 0) : ¬ (p : ℤ) ∣ q.num * q.den := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop := q.reduced
  have hnum0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  rw [padicValRat_def] at hv
  have hint : padicValInt p q.num = padicValNat p q.num.natAbs := (rfl)
  intro hd
  rcases hpZ.dvd_or_dvd hd with h | h
  · have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp h
    have h2 : ¬ p ∣ q.den := fun h2 =>
      hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
    have := one_le_padicValNat_of_dvd hnum0 h1
    rw [padicValNat.eq_zero_of_not_dvd h2, hint] at hv
    omega
  · have h1 : p ∣ q.den := Int.natCast_dvd_natCast.mp h
    have h2 : ¬ p ∣ q.num.natAbs := fun h2 =>
      hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1)
    have := one_le_padicValNat_of_dvd q.den_nz h1
    rw [hint, padicValNat.eq_zero_of_not_dvd h2] at hv
    omega

open Classical in
/-- **Proposition 5.2, quadratic assertion.** Under the hypotheses of Proposition 5.2, with
`d = n + 1 - k₀`, let `c ∈ ℚ^×` have `v_p(c) = 0` and `2d < p`. Then some element of
`Gal(P_n^{(a/u,b/v)}(1 + cX²)/ℚ)` acts on the roots as a single `2d`-cycle whose `d`-th power
is negation on the roots it moves (so on opposite pairs it is a single `d`-cycle and its `d`-th
power interchanges exactly those `d` pairs, as in Lemma 5.1). -/
theorem exists_isCycle_galPerm_jacobiP_comp {p n : ℕ} {a u b v D r : ℤ}
    (h : JacobiCycleHypotheses p n a u b v D r) {c : ℚ} (hc : c ≠ 0)
    (hcp : padicValRat p c = 0)
    (h2d : 2 * (n + 1 - jacobiCycleIndexNat p n D r) < p) :
    ∃ σ : ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2)).Gal,
      (galPerm _ σ).IsCycle ∧
      (galPerm _ σ).support.card = 2 * (n + 1 - jacobiCycleIndexNat p n D r) ∧
      ∀ y ∈ (galPerm _ σ).support,
        (((galPerm _ σ ^ (n + 1 - jacobiCycleIndexNat p n D r)) y : _) :
          ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2)).SplittingField) =
          -((y : _) :
          ((jacobiP ((a : ℚ) / u) ((b : ℚ) / v) n).comp (1 + C c * X ^ 2)).SplittingField) := by
  obtain ⟨h1, -, -, -, h0, hlc, hlc2, hdeg, hsq⟩ := h.localCycle_hypotheses
  have : Fact p.Prime := ⟨h.prime⟩
  have hpZ : Prime (p : ℤ) := h.prime_int
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast h.u_pos.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast h.D_pos.ne'
  -- `q = u c / (2D)` has `p`-adic valuation `0`
  set q : ℚ := (u : ℚ) * c / (2 * D) with hq
  have hq0 : q ≠ 0 := div_ne_zero (mul_ne_zero hu' hc) (mul_ne_zero two_ne_zero hD')
  have hp_u : ¬ (p : ℤ) ∣ u := fun hd => h.not_dvd (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left hd _) _)
  have hp_D : ¬ (p : ℤ) ∣ D := fun hd => h.not_dvd (dvd_mul_of_dvd_right hd _)
  have h3 : 3 ≤ p := lt_of_le_of_ne h.prime.two_le (Ne.symm h.odd)
  have hp_2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    have := Int.le_of_dvd two_pos hd
    omega
  have hvint : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → padicValRat p (z : ℚ) = 0 := fun z hz => by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]; simp
  have hvq : padicValRat p q = 0 := by
    have h2 : padicValRat p (2 : ℚ) = 0 := by simpa using hvint 2 hp_2
    rw [hq, padicValRat.div (mul_ne_zero hu' hc) (mul_ne_zero two_ne_zero hD'),
      padicValRat.mul hu' hc, padicValRat.mul two_ne_zero hD', hcp, h2, hvint u hp_u,
      hvint D hp_D]
    simp
  have hst := not_dvd_num_mul_den_of_padicValRat_eq_zero hq0 hvq
  have ht : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have hqst : ((q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) = (u : ℚ) * c / (2 * D) := by
    push_cast; exact Rat.num_div_den q
  obtain ⟨τ, hτ, hcard, hneg⟩ :=
    SourceInertia.exists_isCycle_galPerm_comp (c := q.num * q.den) h.prime h.odd hst h1 h2d h0
      hlc hlc2 hdeg hsq
  exact exists_isCycle_galPerm_jacobiP_quadratic_of_integralJacobi a u D r ((b : ℚ) / v) n
    h.u_pos.ne' h.D_pos.ne' h.r_eq c q.num q.den ht hqst τ hτ hcard hneg

end ArithmeticOfJacobiPolynomials
