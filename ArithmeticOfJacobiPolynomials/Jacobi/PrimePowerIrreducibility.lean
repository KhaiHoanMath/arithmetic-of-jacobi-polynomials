/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.MonicEndpoint
public import ArithmeticOfJacobiPolynomials.Padic.NewtonEdge
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Irreducibility over `ℚ_p` in prime-power degrees (Theorem A.2, Corollary A.3)

* `primePowerCriterion` (Theorem A.2): for `n = p^a`, `a ≥ 1`, `v_p(α) = -e < 0`,
  `v_p(β) ≥ 0` and `v_p((β+1)_n) = v_p(n!)`, the monic endpoint polynomial
  `n! P_n^{(α,β)}(2X-1)/(n+α+β+1)_n` has a single Newton edge from
  `(0, en + (n-1)/(p-1))` to `(n, 0)` with every intermediate coefficient point strictly
  above it, and `P_n^{(α,β)}` is irreducible over `ℚ_p`.
* `irreducible_jacobiP_half_of_odd_prime` (Corollary A.3): for an odd prime `p`, `a ≥ 1` and
  `v_p(α) < 0`, both `P_{p^a}^{(α,∓1/2)}` are irreducible over `ℚ_p`;
  `irreducible_kanekoZagier_three_pow`: in particular all four `P_{3^a}^{(λ/3,μ/2)}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- Rising factorials commute with ring homomorphisms. -/
theorem map_ascPochhammer_eval {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (x : R) (m : ℕ) : f ((ascPochhammer R m).eval x) = (ascPochhammer S m).eval (f x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, map_mul, map_add, ih, map_natCast]

/-- Comparison of `p`-adic norms of rationals gives comparison of valuations. -/
theorem padicValRat_le_of_norm_le {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0)
    (h : ‖(q : ℚ_[p])‖ ≤ ‖(r : ℚ_[p])‖) : padicValRat p r ≤ padicValRat p q := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hr), Padic.valuation_ratCast,
    Padic.valuation_ratCast] at h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have := (zpow_le_zpow_iff_right₀ hp1).mp h
  linarith

theorem norm_ratCast_le_one_of_padicValRat_nonneg {q : ℚ} (hq : 0 ≤ padicValRat p q) :
    ‖(q : ℚ_[p])‖ ≤ 1 := by
  by_cases h0 : q = 0
  · simp [h0]
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_ratCast]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  exact zpow_le_one_of_nonpos₀ hp1 (by linarith)

/-- `p`-integrality of `(x)_m / m!` for `p`-integral `x`: `v_p((x)_m) ≥ v_p(m!)`. -/
theorem padicValNat_factorial_le_padicValRat_ascPochhammer {x : ℚ}
    (hx : 0 ≤ padicValRat p x) (m : ℕ) (h0 : (ascPochhammer ℚ m).eval x ≠ 0) :
    (padicValNat p m.factorial : ℤ) ≤ padicValRat p ((ascPochhammer ℚ m).eval x) := by
  set y : ℤ_[p] := ⟨(x : ℚ_[p]), norm_ratCast_le_one_of_padicValRat_nonneg hx⟩ with hy
  have h1 : (((ascPochhammer ℚ m).eval x : ℚ) : ℚ_[p]) =
      (ascPochhammer ℚ_[p] m).eval (x : ℚ_[p]) :=
    map_ascPochhammer_eval (Rat.castHom ℚ_[p]) x m
  have h2 : (PadicInt.Coe.ringHom ((ascPochhammer ℤ_[p] m).eval y) : ℚ_[p]) =
      (ascPochhammer ℚ_[p] m).eval (PadicInt.Coe.ringHom y) :=
    map_ascPochhammer_eval PadicInt.Coe.ringHom y m
  have h3 : (ascPochhammer ℤ_[p] m).eval y = m.factorial * Ring.multichoose y m := by
    rw [← ascPochhammer_smeval_eq_eval, ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
      nsmul_eq_mul]
  have hyx : (PadicInt.Coe.ringHom y : ℚ_[p]) = x := rfl
  have key : (((ascPochhammer ℚ m).eval x : ℚ) : ℚ_[p]) =
      (m.factorial : ℚ_[p]) * PadicInt.Coe.ringHom (Ring.multichoose y m) := by
    rw [h1, ← hyx, ← h2, h3, map_mul, map_natCast]
  have hle : ‖(((ascPochhammer ℚ m).eval x : ℚ) : ℚ_[p])‖ ≤
      ‖(((m.factorial : ℕ) : ℚ) : ℚ_[p])‖ := by
    rw [key, norm_mul]
    have : ‖(PadicInt.Coe.ringHom (Ring.multichoose y m) : ℚ_[p])‖ ≤ 1 := by
      have := PadicInt.norm_le_one (Ring.multichoose y m)
      rwa [PadicInt.norm_def] at this
    push_cast
    exact mul_le_of_le_one_right (norm_nonneg _) this
  have := padicValRat_le_of_norm_le h0 (by exact_mod_cast m.factorial_ne_zero) hle
  rwa [padicValRat.of_nat] at this

theorem padicValRat_add_natCast_nonneg {β : ℚ} (hβ : 0 ≤ padicValRat p β) (N : ℕ) :
    0 ≤ padicValRat p (β + N) := by
  by_cases h : β + N = 0
  · rw [h, padicValRat.zero]
  · refine le_trans ?_ (padicValRat.min_le_padicValRat_add h)
    rw [padicValRat.of_nat]; exact le_min hβ (by positivity)

/-- A single denominator factor: `v_p(N + α + β) = -e` when `v_p(α) = -e < 0 ≤ v_p(β)`. -/
theorem padicValRat_natCast_add_add_of_neg {α β : ℚ} {e : ℕ} (he : 0 < e)
    (hα : padicValRat p α = -e) (hβ : 0 ≤ padicValRat p β) (N : ℕ) :
    (N : ℚ) + α + β ≠ 0 ∧ padicValRat p ((N : ℚ) + α + β) = -e := by
  have hα0 : α ≠ 0 := by intro h; rw [h, padicValRat.zero] at hα; omega
  have heq : (N : ℚ) + α + β = α + (β + N) := by ring
  have hv := padicValRat_add_natCast_nonneg hβ N
  rw [heq]
  by_cases h0 : β + N = 0
  · rw [h0, add_zero]; exact ⟨hα0, hα⟩
  have hne : α + (β + N) ≠ 0 := by
    intro h'
    have : α = -(β + N) := by linarith
    rw [this, padicValRat.neg] at hα; omega
  refine ⟨hne, ?_⟩
  rw [padicValRat.add_eq_of_lt hne hα0 h0 (by omega)]; exact hα

/-- The denominators of (4.24): `v_p((N+α+β)_m) = -e m`. -/
theorem padicValRat_ascPochhammer_of_neg {α β : ℚ} {e : ℕ} (he : 0 < e)
    (hα : padicValRat p α = -e) (hβ : 0 ≤ padicValRat p β) (N m : ℕ) :
    (ascPochhammer ℚ m).eval ((N : ℚ) + α + β) ≠ 0 ∧
      padicValRat p ((ascPochhammer ℚ m).eval ((N : ℚ) + α + β)) = -(e * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval]
    have hf := padicValRat_natCast_add_add_of_neg he hα hβ (N + m)
    have e1 : (N : ℚ) + α + β + m = ((N + m : ℕ) : ℚ) + α + β := by push_cast; ring
    rw [e1]
    refine ⟨mul_ne_zero ih.1 hf.1, ?_⟩
    rw [padicValRat.mul ih.1 hf.1, ih.2, hf.2]; push_cast; ring

/-- The valuation of a coefficient of (4.24). -/
theorem padicValRat_monicEndpointCoeff (α β : ℚ) (n j : ℕ) (hj : j ≤ n)
    (hnum : (ascPochhammer ℚ (n - j)).eval (β + j + 1) ≠ 0)
    (hden : (ascPochhammer ℚ (n - j)).eval ((n : ℚ) + α + β + j + 1) ≠ 0) :
    monicEndpointCoeff α β n j ≠ 0 ∧ padicValRat p (monicEndpointCoeff α β n j) =
      padicValNat p (n.choose j) + padicValRat p ((ascPochhammer ℚ (n - j)).eval (β + j + 1)) -
        padicValRat p ((ascPochhammer ℚ (n - j)).eval ((n : ℚ) + α + β + j + 1)) := by
  have hs : ((-1 : ℚ) ^ (n - j)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : ((n.choose j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  rw [monicEndpointCoeff_def]
  refine ⟨div_ne_zero (mul_ne_zero (mul_ne_zero hs hc) hnum) hden, ?_⟩
  rw [padicValRat.div (mul_ne_zero (mul_ne_zero hs hc) hnum) hden,
    padicValRat.mul (mul_ne_zero hs hc) hnum, padicValRat.mul hs hc, padicValRat.pow,
    padicValRat.neg, padicValRat.one, padicValRat.of_nat]
  ring

theorem monicEndpointCoeff_eq_zero_of_num {α β : ℚ} {n j : ℕ}
    (h : (ascPochhammer ℚ (n - j)).eval (β + j + 1) = 0) : monicEndpointCoeff α β n j = 0 := by
  simp [monicEndpointCoeff_def, h]

/-- `v_p(binom(n,j)) + v_p(j!) + v_p((n-j)!) = v_p(n!)`. -/
theorem padicValNat_choose_add_factorial (n j : ℕ) (hj : j ≤ n) :
    padicValNat p (n.choose j) + padicValNat p j.factorial + padicValNat p (n - j).factorial =
      padicValNat p n.factorial := by
  rw [← Nat.choose_mul_factorial_mul_factorial hj,
    padicValNat.mul (mul_ne_zero (Nat.choose_pos hj).ne' j.factorial_ne_zero)
      (n - j).factorial_ne_zero,
    padicValNat.mul (Nat.choose_pos hj).ne' j.factorial_ne_zero]

/-- Legendre's formula for `(p^a)!`: `(p - 1) v_p((p^a)!) + 1 = p^a`. -/
theorem sub_one_mul_padicValNat_factorial_prime_pow (a : ℕ) :
    (p - 1) * padicValNat p (p ^ a).factorial + 1 = p ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', padicValNat_factorial_mul]
    have key : ∀ q V m : ℕ, q * V + 1 = m → q * (V + m) + 1 = (q + 1) * m := by
      intro q V m h; subst h; ring
    have := key (p - 1) _ _ ih
    rwa [Nat.sub_add_cancel hp.out.one_lt.le] at this

/-- `v_p((p^a)!) = (p^a - 1)/(p - 1)`. -/
theorem padicValNat_factorial_prime_pow (a : ℕ) :
    padicValNat p (p ^ a).factorial = (p ^ a - 1) / (p - 1) := by
  have h := sub_one_mul_padicValNat_factorial_prime_pow (p := p) a
  have hp1 : 0 < p - 1 := by have := hp.out.one_lt; omega
  symm
  rw [mul_comm] at h
  exact Nat.div_eq_of_eq_mul_left hp1 (by omega)

/-- **Theorem A.2 (prime-power criterion).** Let `p` be a prime, `a ≥ 1`, `n = p^a`, and
`α, β ∈ ℚ` with `v_p(α) = -e < 0`, `v_p(β) ≥ 0` and `v_p((β+1)_n) = v_p(n!)`. Then the monic
polynomial `n! P_n^{(α,β)}(2X-1)/(n+α+β+1)_n` (of degree `n`) has a single Newton edge
joining `(0, en + (n-1)/(p-1))` and `(n, 0)`, with every intermediate coefficient point
strictly above the edge, and `P_n^{(α,β)}` is irreducible over `ℚ_p`. -/
theorem primePowerCriterion (a : ℕ) (ha : 1 ≤ a) (α β : ℚ) (e : ℕ) (he : 0 < e)
    (hα : padicValRat p α = -e) (hβ : 0 ≤ padicValRat p β)
    (hpoch : padicValRat p ((ascPochhammer ℚ (p ^ a)).eval (β + 1)) =
      padicValNat p (p ^ a).factorial) :
    (monicEndpoint α β (p ^ a)).Monic ∧ (monicEndpoint α β (p ^ a)).natDegree = p ^ a ∧
    (monicEndpoint α β (p ^ a)).coeff 0 ≠ 0 ∧
    padicValRat p ((monicEndpoint α β (p ^ a)).coeff 0) =
      ((e * p ^ a + (p ^ a - 1) / (p - 1) : ℕ) : ℤ) ∧
    (∀ j, 0 < j → j < p ^ a → (monicEndpoint α β (p ^ a)).coeff j ≠ 0 →
      ((e * p ^ a + (p ^ a - 1) / (p - 1) : ℕ) : ℤ) * ((p ^ a : ℕ) - j : ℤ) <
        (p ^ a : ℕ) * padicValRat p ((monicEndpoint α β (p ^ a)).coeff j)) ∧
    Irreducible ((jacobiP α β (p ^ a)).map (algebraMap ℚ ℚ_[p])) := by
  set n := p ^ a with hn_def
  set V := padicValNat p n.factorial with hV_def
  have hVeq : (p ^ a - 1) / (p - 1) = V := (padicValNat_factorial_prime_pow a).symm
  rw [hVeq]
  have hLeg : (p - 1) * V + 1 = n := sub_one_mul_padicValNat_factorial_prime_pow a
  have hp2 : 2 ≤ p := hp.out.two_le
  have hnp : p ≤ n := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.out.pos ha
  have hV1 : 1 ≤ V := by
    by_contra h
    have : V = 0 := by omega
    rw [this] at hLeg; omega
  have hn1 : 1 ≤ n := by omega
  -- denominators
  have hden : ∀ j, (ascPochhammer ℚ (n - j)).eval ((n : ℚ) + α + β + j + 1) ≠ 0 ∧
      padicValRat p ((ascPochhammer ℚ (n - j)).eval ((n : ℚ) + α + β + j + 1)) =
        -(e * (n - j : ℕ)) := by
    intro j
    have := padicValRat_ascPochhammer_of_neg he hα hβ (n + j + 1) (n - j)
    have e1 : ((n + j + 1 : ℕ) : ℚ) + α + β = (n : ℚ) + α + β + j + 1 := by push_cast; ring
    rwa [e1] at this
  have hA : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0 := by
    have := (hden 0).1
    simpa using this
  obtain ⟨hmon, hdeg⟩ := monicEndpoint_monic α β n hA
  have hcoeff : ∀ j, j ≤ n → (monicEndpoint α β n).coeff j = monicEndpointCoeff α β n j := by
    intro j hj
    rw [monicEndpoint_coeff α β n hA, ite_eq_left_iff.mpr (fun h => absurd hj h)]
  -- the constant term
  have hnum0 : (ascPochhammer ℚ n).eval (β + 1) ≠ 0 := by
    intro h; rw [h, padicValRat.zero] at hpoch; omega
  have hb0 := padicValRat_monicEndpointCoeff (p := p) α β n 0 (Nat.zero_le _)
    (by simpa using hnum0) (hden 0).1
  have hv0 : padicValRat p ((monicEndpoint α β n).coeff 0) = ((e * n + V : ℕ) : ℤ) := by
    rw [hcoeff 0 (Nat.zero_le _), hb0.2, (hden 0).2]
    simp only [Nat.choose_zero_right, padicValNat_one_right, Nat.cast_zero, add_zero, Nat.sub_zero]
    rw [hpoch]; push_cast; ring
  have h0 : (monicEndpoint α β n).coeff 0 ≠ 0 := by
    rw [hcoeff 0 (Nat.zero_le _)]; exact hb0.1
  -- the intermediate coefficients
  have hedge : ∀ j, 0 < j → j < n → (monicEndpoint α β n).coeff j ≠ 0 →
      ((e * n + V : ℕ) : ℤ) * ((n : ℕ) - j : ℤ) <
        (n : ℕ) * padicValRat p ((monicEndpoint α β n).coeff j) := by
    intro j hj0 hjn hcj
    rw [hcoeff j hjn.le] at hcj ⊢
    have hnum : (ascPochhammer ℚ (n - j)).eval (β + j + 1) ≠ 0 := fun h =>
      hcj (monicEndpointCoeff_eq_zero_of_num h)
    have hbj := padicValRat_monicEndpointCoeff (p := p) α β n j hjn.le hnum (hden j).1
    rw [hbj.2, (hden j).2]
    have hint := padicValNat_factorial_le_padicValRat_ascPochhammer
      (by have := padicValRat_add_natCast_nonneg hβ (j + 1); push_cast at this
          rwa [← add_assoc] at this) (n - j) hnum
    have hch := padicValNat_choose_add_factorial (p := p) n j hjn.le
    have hjfac : (p - 1) * padicValNat p j.factorial < j :=
      sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) (hn := hj0.ne')
    -- integer arithmetic
    set t := padicValNat p j.factorial
    set c := padicValNat p (n.choose j)
    set u := padicValNat p (n - j).factorial
    set w := padicValRat p ((ascPochhammer ℚ (n - j)).eval (β + j + 1))
    have hp1 : (1 : ℤ) ≤ (p : ℤ) - 1 := by
      have : (2 : ℤ) ≤ p := by exact_mod_cast hp2
      linarith
    have hLeg' : ((p : ℤ) - 1) * V + 1 = n := by
      have := hLeg; zify [hp.out.one_lt.le] at this; exact this
    have hjfac' : ((p : ℤ) - 1) * t + 1 ≤ j := by
      have := hjfac; zify [hp.out.one_lt.le] at this; omega
    have hch' : (c : ℤ) + t + u = V := by exact_mod_cast hch
    have hjn' : (j : ℤ) < n := by exact_mod_cast hjn
    have hj0' : (0 : ℤ) < j := by exact_mod_cast hj0
    have hnj : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by push_cast [hjn.le]; ring
    rw [hnj]
    -- `n t < j V`
    have hkey : (n : ℤ) * t < j * V := by
      have h1 : ((p : ℤ) - 1) * (n * t) < ((p : ℤ) - 1) * (j * V) := by
        have h2 : (n : ℤ) * (((p : ℤ) - 1) * t + 1) ≤ n * j :=
          mul_le_mul_of_nonneg_left hjfac' (by positivity)
        have h5 : ((p : ℤ) - 1) * (j * V) = j * n - j := by linear_combination (j : ℤ) * hLeg'
        linarith
      exact lt_of_mul_lt_mul_left h1 (by linarith)
    have hu : (u : ℤ) ≤ w := hint
    have h4 : (n : ℤ) * u ≤ n * w := mul_le_mul_of_nonneg_left hu (by positivity)
    have h3 : (n : ℤ) * c + n * t + n * u = n * V := by rw [← hch']; ring
    push_cast
    linarith
  have hcop : Int.gcd (padicValRat p ((monicEndpoint α β n).coeff 0))
      (monicEndpoint α β n).natDegree = 1 := by
    rw [hv0, hdeg, Int.gcd_natCast_natCast]
    have hpH : ¬ p ∣ e * n + V := by
      intro h
      have h1 : p ∣ e * n := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) e
      have h2 : p ∣ V := (Nat.dvd_add_right h1).mp h
      have h3 : p ∣ (p - 1) * V := Dvd.dvd.mul_left h2 _
      have h4 : p ∣ n := dvd_pow_self p (by omega)
      rw [← hLeg] at h4
      have := (Nat.dvd_add_right h3).mp h4
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    exact Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpH).symm
  have hirr := irreducible_map_padic_of_single_edge (p := p) hmon (by omega) h0 hcop
    (by rw [hdeg]; exact fun j h1 h2 h3 => by rw [hv0]; exact_mod_cast hedge j h1 h2 h3)
  exact ⟨hmon, hdeg, h0, hv0, hedge,
    (irreducible_map_jacobiP_iff (K := ℚ_[p]) α β n hA).mpr hirr⟩

/-- `(1/2)_n = (2n)! / (4^n n!)`. -/
theorem ascPochhammer_eval_half (n : ℕ) :
    (ascPochhammer ℚ n).eval (1 / 2) = (2 * n).factorial / (4 ^ n * n.factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `(3/2)_n = (2n+1)! / (4^n n!)`. -/
theorem ascPochhammer_eval_three_halves (n : ℕ) :
    (ascPochhammer ℚ n).eval (3 / 2) = (2 * n + 1).factorial / (4 ^ n * n.factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring,
      Nat.factorial_succ (2 * n + 1 + 1), Nat.factorial_succ (2 * n + 1), Nat.factorial_succ n]
    push_cast
    field_simp
    ring

theorem not_dvd_two_of_ne_two (hp2 : p ≠ 2) : ¬ p ∣ 2 := by
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)

/-- For odd `p`, `v_p((2p^a)!) = 2 v_p((p^a)!)`. -/
theorem padicValNat_factorial_two_mul_prime_pow (hp2 : p ≠ 2) (a : ℕ) :
    padicValNat p (2 * p ^ a).factorial = 2 * padicValNat p (p ^ a).factorial := by
  induction a with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_two, Nat.factorial_one, padicValNat_one_right,
      mul_zero]
    exact padicValNat.eq_zero_of_not_dvd (not_dvd_two_of_ne_two hp2)
  | succ a ih =>
    rw [pow_succ', show 2 * (p * p ^ a) = p * (2 * p ^ a) by ring, padicValNat_factorial_mul,
      padicValNat_factorial_mul, ih]
    ring

/-- For `a ≥ 1`, `v_p((2p^a+1)!) = v_p((2p^a)!)`. -/
theorem padicValNat_factorial_two_mul_prime_pow_add_one (a : ℕ) (ha : 1 ≤ a) :
    padicValNat p (2 * p ^ a + 1).factorial = padicValNat p (2 * p ^ a).factorial := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha
  rw [pow_succ', show 2 * (p * p ^ b) = p * (2 * p ^ b) by ring]
  exact padicValNat_factorial_mul_add _ hp.out.one_lt

theorem padicValRat_two_of_ne_two (hp2 : p ≠ 2) : padicValRat p 2 = 0 := by
  have : padicValRat p ((2 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (not_dvd_two_of_ne_two hp2)]; rfl
  exact_mod_cast this

/-- `v_p` of `(2n+δ)! / (4^n n!)` for odd `p`. -/
theorem padicValRat_factorial_div (hp2 : p ≠ 2) (m n : ℕ) :
    padicValRat p ((m.factorial : ℚ) / (4 ^ n * n.factorial)) =
      (padicValNat p m.factorial : ℤ) - padicValNat p n.factorial := by
  have h4 : padicValRat p 4 = 0 := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, padicValRat.pow, padicValRat_two_of_ne_two hp2,
      mul_zero]
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.mul (by positivity)
    (by positivity), padicValRat.pow, h4, padicValRat.of_nat, padicValRat.of_nat]
  ring

/-- **Corollary A.3.** Let `p` be an odd prime, `a ≥ 1`, and `α ∈ ℚ` with `v_p(α) < 0`. Then
both `P_{p^a}^{(α,-1/2)}` and `P_{p^a}^{(α,1/2)}` are irreducible over `ℚ_p`. -/
theorem irreducible_jacobiP_half_of_odd_prime (hp2 : p ≠ 2) (a : ℕ) (ha : 1 ≤ a) (α : ℚ)
    (hα : padicValRat p α < 0) :
    Irreducible ((jacobiP α (-1 / 2) (p ^ a)).map (algebraMap ℚ ℚ_[p])) ∧
      Irreducible ((jacobiP α (1 / 2) (p ^ a)).map (algebraMap ℚ ℚ_[p])) := by
  set e := (-padicValRat p α).toNat with he_def
  have he : 0 < e := by omega
  have hαe : padicValRat p α = -e := by omega
  have hhalf : padicValRat p (1 / 2) = 0 := by
    rw [one_div, padicValRat.inv, padicValRat_two_of_ne_two hp2, neg_zero]
  have hV := padicValNat_factorial_two_mul_prime_pow hp2 a
  refine ⟨(primePowerCriterion a ha α (-1 / 2) e he hαe ?_ ?_).2.2.2.2.2,
    (primePowerCriterion a ha α (1 / 2) e he hαe ?_ ?_).2.2.2.2.2⟩
  · rw [neg_div, padicValRat.neg, hhalf]
  · rw [show (-1 / 2 : ℚ) + 1 = 1 / 2 by norm_num, ascPochhammer_eval_half,
      padicValRat_factorial_div hp2, hV]
    push_cast; ring
  · rw [hhalf]
  · rw [show (1 / 2 : ℚ) + 1 = 3 / 2 by norm_num, ascPochhammer_eval_three_halves,
      padicValRat_factorial_div hp2, padicValNat_factorial_two_mul_prime_pow_add_one a ha, hV]
    push_cast; ring

end ArithmeticOfJacobiPolynomials
