/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.ModularFormsODE
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The Jacobi families as pole polynomials (§6.4; [BSS, §3–§4])

The manuscript remarks (§6.4) that the four Jacobi families `P_k^{(λ/3, μ/2)}`
occur as pole polynomials in modular differential equations ([BSS, Theorem 4.2],
arXiv:2508.10788v3). The polynomials and weight-two form below are those of [BSS, §3–§4].

**Polynomials.** For rational `α, β` put (BSS (3.3))
`Q_k^{α,β}(x) = k!/(k+α+β+1)_k · P_k^{(β,α)}(2x - 1)` (`bssQ`) and (BSS (4.9))
`𝒫(X) = 1728^k Q_k^{α,β}(X/1728)` (`polePoly`, in the classical variable `j = 1728 J`). With
`α = λ/3`, `β = μ/2`, `λ, μ ∈ {±1}` (BSS (4.2)) and `ℓ = 12k + 6 + 2λ + 3μ`, `polePoly` is the
monic pole polynomial `𝒫_ℓ`. We prove:

* `bssQ_monic`, `polePoly_monic`: monic of degree `k` (Proposition 4.3);
* `bssQ_ode` (BSS (3.4)) and `polePoly_ode` (BSS (4.11)), from the Jacobi equation;
* `kanekoZagierModularPoly_comp_eq_bssQ`: **Theorem 4.2, (4.7)**
  `F̃_{ℓ-1}(1728x) = (-1)^k 1728^k (k+α+β+1)_k/k! · Q_k^{α,β}(x)`;
* `polePoly_eq_kanekoZagierModularPoly`: **Proposition 4.3, (4.10)**
  `𝒫_ℓ = (-1)^k k!/(k+α+β+1)_k · F̃_{ℓ-1}`;
* `roots_polePoly_map_real` and `polePoly_map_real_eq_prod`: the first equality of (4.9),
  `𝒫(X) = ∏_j (X - 1728 x_{k,j})` over the roots `x_{k,j}` of `Q_k^{α,β}`;
* `bssQ_roots_real`, `polePoly_roots_real`: for `α, β > -1` the roots are simple and lie in
  `(0, 1)`, resp. `(0, 1728)` (conditional on the cited `JacobiSimpleRealZeros`);
* `bssQ_roots_residueSystem`: the roots of `Q_k^{α,β}` solve the residue (Stieltjes) system
  (BSS (3.2)) `(α+1)/x_i + (β+1)/(x_i - 1) + 2 ∑_{j≠i} 1/(x_i - x_j) = 0` — the existence half of
  [BSS, Theorem 3.1];
* `bssWeightTwoForm_residue_eq_zero`: **the pole interpretation.** If `w_1, …, w_k ∈ ℍ` have
  invariants `J(w_j)` equal to the roots of `Q_k^{α,β}`, then the weight-two form (2.2)
  `η^{4+8ε+12δ}/(E₄^ε E₆^δ) ∏_j (J - J(w_j))^{-2}` has zero residue at every `w_i`. This is
  conditional on the residue calculation of [BSS, §2] (quoted there from the literature), stated
  as the hypothesis `BSSResidueCriterion`, and on `JacobiSimpleRealZeros`.

**Modular forms.** With Mathlib's Dedekind `η` (`ModularForm.eta`), `D = (2πi)⁻¹ d/dz` and the
Kaneko–Zagier form `F_{ℓ-1} = kzModularForm l μ k a b` of weight `ℓ - 1 = 12k + 4a + 6b`
(`a = (λ+1)/2`, `b = (μ+1)/2`, so `ε = 2a`, `δ = 2b`):

* `normalizedDerivOfComplex_etaUpper`: `D η = (E₂/24) η` (i.e. `D log η = E₂/24`);
* `kzNormalSolution` `y = F_{ℓ-1}/η^{2ℓ}`, holomorphic on `ℍ` (`mdifferentiable_kzNormalSolution`);
* `kzNormalSolution_normalForm`: **Proposition 4.1, (4.4)** `D²y = (ℓ²/144) E₄ y`;
* `kzNormalSolution_eq_bssQ` and `kzNormalSolution_eq_polePoly`: **Theorem 4.2, (4.8)**
  `y = C · E₄^a E₆^b Q_k^{α,β}(J)/η^{2+4ε+6δ}` with `J = j/1728` and the explicit nonzero rational
  constant `C = (-1)^k 1728^k (k+α+β+1)_k/k!` (`bssConst`, `bssConst_ne_zero`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial ModularForm UpperHalfPlane Derivative

open scoped MatrixGroups Manifold

local notation "Δ" => ModularForm.discriminant

/-! ### The monic shifted Jacobi polynomial `Q_k^{α,β}` (BSS (3.3)) -/

/-- **BSS (3.3).** The monic shifted Jacobi polynomial
`Q_k^{α,β}(x) = k!/(k+α+β+1)_k · P_k^{(β,α)}(2x - 1)`. -/
noncomputable def bssQ (k : ℕ) (α β : ℚ) : ℚ[X] :=
  C ((k.factorial : ℚ) / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1)) *
    (jacobiP β α k).comp (2 * polyX - 1)

theorem bssQ_eq (k : ℕ) (α β : ℚ) : bssQ k α β =
    C ((k.factorial : ℚ) / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1)) *
      (jacobiP β α k).comp (2 * polyX - 1) := (rfl)

theorem bssQ_eq_monicEndpoint (k : ℕ) (α β : ℚ) : bssQ k α β = monicEndpoint β α k := by
  rw [bssQ_eq, monicEndpoint_def, show (k : ℚ) + β + α + 1 = k + α + β + 1 by ring]

theorem two_mul_X_sub_one_eq {R : Type*} [CommRing R] :
    (2 * polyX - 1 : R[X]) = C 2 * polyX + C (-1) := by
  simp only [map_neg, map_one, map_ofNat]
  ring

theorem eval_two_mul_X_sub_one (x : ℚ) : (2 * polyX - 1 : ℚ[X]).eval x = 2 * x - 1 := by
  simp

theorem derivative_comp_two_mul_X_sub_one (p : ℚ[X]) :
    derivative (p.comp (2 * polyX - 1)) = C 2 * (derivative p).comp (2 * polyX - 1) := by
  rw [two_mul_X_sub_one_eq, derivative_comp, derivative_add, derivative_C_mul_X, derivative_C,
    add_zero]

theorem eval_bssQ (k : ℕ) (α β x : ℚ) : (bssQ k α β).eval x =
    k.factorial / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) *
      (jacobiP β α k).eval (2 * x - 1) := by
  rw [bssQ_eq, eval_mul, eval_C, eval_comp, eval_two_mul_X_sub_one]

/-- `(k+α+β+1)_k > 0` for `α, β > -1`. -/
theorem ascPochhammer_bss_pos {k : ℕ} {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) :
    0 < (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · apply ascPochhammer_pos
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith

/-- For the four Kaneko–Zagier families (`μ = ±1`), `(k + λ/3 + μ/2 + 1)_k ≠ 0`. -/
theorem ascPochhammer_kanekoZagier_ne_zero {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (k : ℕ) :
    (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) ≠ 0 := by
  have h := ring_choose_kanekoZagier_ne_zero (l := l) hμ k
  rw [ring_choose_eq_ascPochhammer_div,
    show 2 * (k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 - k + 1 = k + l / 3 + μ / 2 + 1 by ring] at h
  intro h0
  exact h (by rw [h0, zero_div])

/-- **BSS (3.3).** `Q_k^{α,β}` is monic of degree `k` (when `(k+α+β+1)_k ≠ 0`). -/
theorem bssQ_monic {k : ℕ} {α β : ℚ}
    (h : (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) ≠ 0) :
    (bssQ k α β).Monic ∧ (bssQ k α β).natDegree = k := by
  rw [bssQ_eq_monicEndpoint]
  exact monicEndpoint_monic β α k (by rwa [show (k : ℚ) + β + α + 1 = k + α + β + 1 by ring])

theorem eval_derivative_bssQ (k : ℕ) (α β x : ℚ) : (derivative (bssQ k α β)).eval x =
    k.factorial / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) *
      (2 * (derivative (jacobiP β α k)).eval (2 * x - 1)) := by
  rw [bssQ_eq, derivative_C_mul, derivative_comp_two_mul_X_sub_one, eval_mul, eval_C, eval_mul,
    eval_C, eval_comp, eval_two_mul_X_sub_one]

theorem eval_derivative_derivative_bssQ (k : ℕ) (α β x : ℚ) :
    (derivative (derivative (bssQ k α β))).eval x =
      k.factorial / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) *
        (2 * (2 * (derivative (derivative (jacobiP β α k))).eval (2 * x - 1))) := by
  rw [bssQ_eq, derivative_C_mul, derivative_comp_two_mul_X_sub_one, derivative_C_mul,
    derivative_C_mul, derivative_comp_two_mul_X_sub_one]
  simp only [eval_mul, eval_C, eval_comp, eval_two_mul_X_sub_one]

/-- **BSS (3.4)**, pointwise:
`x(1-x) Q'' + [α+1 - (α+β+2)x] Q' + k(k+α+β+1) Q = 0`. -/
theorem bssQ_ode_eval (k : ℕ) (α β x : ℚ) :
    x * (1 - x) * (derivative (derivative (bssQ k α β))).eval x +
      (α + 1 - (α + β + 2) * x) * (derivative (bssQ k α β)).eval x +
      k * (k + α + β + 1) * (bssQ k α β).eval x = 0 := by
  have hode := congrArg (eval (2 * x - 1)) (jacobiP_ode β α k)
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C,
    eval_zero] at hode
  rw [eval_derivative_derivative_bssQ, eval_derivative_bssQ, eval_bssQ]
  linear_combination
    ((k.factorial : ℚ) / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1)) * hode

/-- **BSS (3.4).** `x(1-x) Q'' + [α+1 - (α+β+2)x] Q' + k(k+α+β+1) Q = 0` in `ℚ[X]`. -/
theorem bssQ_ode (k : ℕ) (α β : ℚ) :
    polyX * (1 - polyX) * derivative (derivative (bssQ k α β)) +
      (C (α + 1) - C (α + β + 2) * polyX) * derivative (bssQ k α β) +
      C ((k : ℚ) * (k + α + β + 1)) * bssQ k α β = 0 := by
  refine Polynomial.funext fun x => ?_
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_C, eval_zero]
  linear_combination bssQ_ode_eval k α β x

/-! ### The monic pole polynomial `𝒫` (BSS (4.9)) -/

/-- **BSS (4.9).** The monic pole polynomial in the classical variable `j = 1728 J`,
`𝒫(X) = 1728^k Q_k^{α,β}(X/1728)`; for `α = λ/3`, `β = μ/2` it is `𝒫_ℓ`,
`ℓ = 12k + 6 + 2λ + 3μ`. -/
noncomputable def polePoly (k : ℕ) (α β : ℚ) : ℚ[X] :=
  C ((1728 : ℚ) ^ k) * (bssQ k α β).comp (C (1 / 1728) * polyX)

theorem polePoly_eq (k : ℕ) (α β : ℚ) : polePoly k α β =
    C ((1728 : ℚ) ^ k) * (bssQ k α β).comp (C (1 / 1728) * polyX) := (rfl)

theorem eval_polePoly (k : ℕ) (α β x : ℚ) :
    (polePoly k α β).eval x = 1728 ^ k * (bssQ k α β).eval (x / 1728) := by
  rw [polePoly_eq, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X,
    show (1 / 1728 : ℚ) * x = x / 1728 by ring]

theorem derivative_comp_C_mul_X (p : ℚ[X]) (c : ℚ) :
    derivative (p.comp (C c * polyX)) = C c * (derivative p).comp (C c * polyX) := by
  rw [derivative_comp, derivative_C_mul_X]

/-- **Proposition 4.3.** `𝒫` is monic of degree `k` (when `(k+α+β+1)_k ≠ 0`). -/
theorem polePoly_monic {k : ℕ} {α β : ℚ}
    (h : (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) ≠ 0) :
    (polePoly k α β).Monic ∧ (polePoly k α β).natDegree = k := by
  obtain ⟨hm, hd⟩ := bssQ_monic h
  have hq : (C (1 / 1728 : ℚ) * polyX).natDegree = 1 := natDegree_C_mul_X _ (by norm_num)
  have hq0 : (C (1 / 1728 : ℚ) * polyX).natDegree ≠ 0 := by rw [hq]; norm_num
  have hdeg : (polePoly k α β).natDegree = k := by
    rw [polePoly_eq, natDegree_C_mul (pow_ne_zero k (show (1728 : ℚ) ≠ 0 by norm_num)),
      natDegree_comp, hq, hd, mul_one]
  refine ⟨?_, hdeg⟩
  rw [Monic.def, polePoly_eq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp hq0,
    hm.leadingCoeff, leadingCoeff_C_mul_X, hd, one_mul, ← mul_pow]
  norm_num

/-- **Proposition 4.3, (4.11)**, pointwise. -/
theorem polePoly_ode_eval (k : ℕ) (α β x : ℚ) :
    x * (1728 - x) * (derivative (derivative (polePoly k α β))).eval x +
      (1728 * (α + 1) - (α + β + 2) * x) * (derivative (polePoly k α β)).eval x +
      k * (k + α + β + 1) * (polePoly k α β).eval x = 0 := by
  have h := bssQ_ode_eval k α β (x / 1728)
  rw [polePoly_eq, derivative_C_mul, derivative_C_mul, derivative_comp_C_mul_X,
    derivative_C_mul, derivative_comp_C_mul_X]
  simp only [eval_mul, eval_C, eval_comp, eval_X]
  rw [show (1 / 1728 : ℚ) * x = x / 1728 by ring]
  linear_combination (1728 : ℚ) ^ k * h

/-- **Proposition 4.3, (4.11).**
`X(1728 - X) 𝒫'' + [1728(α+1) - (α+β+2)X] 𝒫' + k(k+α+β+1) 𝒫 = 0` in `ℚ[X]`. -/
theorem polePoly_ode (k : ℕ) (α β : ℚ) :
    polyX * (1728 - polyX) * derivative (derivative (polePoly k α β)) +
      (C (1728 * (α + 1)) - C (α + β + 2) * polyX) * derivative (polePoly k α β) +
      C ((k : ℚ) * (k + α + β + 1)) * polePoly k α β = 0 := by
  refine Polynomial.funext fun x => ?_
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_zero, eval_ofNat]
  linear_combination polePoly_ode_eval k α β x

/-! ### Theorem 4.2 and Proposition 4.3: comparison with `F̃_{ℓ-1}` -/

theorem eval_kanekoZagierModularPoly (l μ : ℤ) (k : ℕ) (y : ℚ) :
    (kanekoZagierModularPoly l μ k).eval y =
      1728 ^ k * (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) k).eval (-1 / 864 * y + 1) := by
  rw [kanekoZagierModularPoly_eq]
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X]

/-- The constant `(-1)^k 1728^k (k+α+β+1)_k / k!` of (4.7) and of `C_{k,ε,δ}` in (4.8). -/
noncomputable def bssConst (k : ℕ) (α β : ℚ) : ℚ :=
  (-1) ^ k * 1728 ^ k * (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) / k.factorial

theorem bssConst_eq (k : ℕ) (α β : ℚ) : bssConst k α β =
    (-1) ^ k * 1728 ^ k * (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) / k.factorial :=
  (rfl)

theorem bssConst_ne_zero {k : ℕ} {α β : ℚ}
    (h : (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) ≠ 0) : bssConst k α β ≠ 0 := by
  rw [bssConst_eq]
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))) h) hf

/-- **Theorem 4.2, (4.7).** With `α = λ/3`, `β = μ/2`,
`F̃_{ℓ-1}(1728x) = (-1)^k 1728^k (k+α+β+1)_k/k! · Q_k^{α,β}(x)` (for `(k+α+β+1)_k ≠ 0`, in
particular for `μ = ±1`, `ascPochhammer_kanekoZagier_ne_zero`). -/
theorem kanekoZagierModularPoly_comp_eq_bssQ (l μ : ℤ) (k : ℕ)
    (h : (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) ≠ 0) :
    (kanekoZagierModularPoly l μ k).comp (C 1728 * polyX) =
      C (bssConst k ((l : ℚ) / 3) ((μ : ℚ) / 2)) * bssQ k ((l : ℚ) / 3) ((μ : ℚ) / 2) := by
  refine Polynomial.funext fun x => ?_
  have hr := congrArg (eval (2 * x - 1)) (jacobiP_comp_neg_X ((μ : ℚ) / 2) ((l : ℚ) / 3) k)
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at hr
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hc : (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) / k.factorial *
      (k.factorial / (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1)) = 1 := by
    rw [div_mul_div_comm, mul_comm (k.factorial : ℚ), div_self (mul_ne_zero h hf)]
  simp only [eval_comp, eval_mul, eval_C, eval_X, eval_bssQ, eval_kanekoZagierModularPoly,
    bssConst_eq]
  rw [show (-1 / 864 : ℚ) * (1728 * x) + 1 = -(2 * x - 1) by ring, hr]
  linear_combination (-((-1 : ℚ) ^ k * 1728 ^ k *
    (jacobiP ((μ : ℚ) / 2) ((l : ℚ) / 3) k).eval (2 * x - 1))) * hc

/-- **Proposition 4.3, (4.10).** `𝒫_ℓ = (-1)^k k!/(k+α+β+1)_k · F̃_{ℓ-1}` for `α = λ/3`,
`β = μ/2` (for all `λ, μ`; for `(k+α+β+1)_k = 0` both sides vanish). -/
theorem polePoly_eq_kanekoZagierModularPoly (l μ : ℤ) (k : ℕ) :
    polePoly k ((l : ℚ) / 3) ((μ : ℚ) / 2) =
      C ((-1) ^ k * k.factorial /
        (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1)) *
        kanekoZagierModularPoly l μ k := by
  refine Polynomial.funext fun x => ?_
  have hr := congrArg (eval (2 * (x / 1728) - 1))
    (jacobiP_comp_neg_X ((μ : ℚ) / 2) ((l : ℚ) / 3) k)
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at hr
  simp only [eval_polePoly, eval_mul, eval_C, eval_bssQ, eval_kanekoZagierModularPoly]
  rw [show (-1 / 864 : ℚ) * x + 1 = -(2 * (x / 1728) - 1) by ring, hr]
  have hs : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  linear_combination (-((1728 : ℚ) ^ k * ((k.factorial : ℚ) /
    (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1)) *
      (jacobiP ((μ : ℚ) / 2) ((l : ℚ) / 3) k).eval (2 * (x / 1728) - 1))) * hs

/-! ### Roots (BSS (4.9) and Proposition 4.3) -/

theorem bssQ_map_eq {K : Type*} [Field K] [Algebra ℚ K] (k : ℕ) (α β : ℚ) :
    (bssQ k α β).map (algebraMap ℚ K) =
      C (algebraMap ℚ K ((k.factorial : ℚ) / (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1))) *
        ((jacobiP β α k).map (algebraMap ℚ K)).comp (C 2 * polyX + C (-1)) := by
  rw [bssQ_eq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp]
  congr 2
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_ofNat]
  exact two_mul_X_sub_one_eq

/-- The real roots of `Q_k^{α,β}` are `(t + 1)/2`, `t` running over the roots of
`P_k^{(β,α)}`. -/
theorem roots_bssQ_map_real {k : ℕ} {α β : ℚ}
    (h : (ascPochhammer ℚ k).eval ((k : ℚ) + α + β + 1) ≠ 0) :
    ((bssQ k α β).map (algebraMap ℚ ℝ)).roots =
      ((jacobiP β α k).map (algebraMap ℚ ℝ)).roots.map fun t => (t + 1) / 2 := by
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [bssQ_map_eq, roots_C_mul _ ((map_ne_zero (algebraMap ℚ ℝ)).mpr (div_ne_zero hf h)),
    roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℝ) ≠ 0))]
  congr 1
  funext t
  rw [Ring.inverse_eq_inv]
  ring

/-- **(4.9), first equality, on roots.** The real roots of `𝒫` are `1728 x`, `x` running over
the roots of `Q_k^{α,β}`. -/
theorem roots_polePoly_map_real {k : ℕ} {α β : ℚ} :
    ((polePoly k α β).map (algebraMap ℚ ℝ)).roots =
      ((bssQ k α β).map (algebraMap ℚ ℝ)).roots.map fun x => 1728 * x := by
  have hC : (algebraMap ℚ ℝ) ((1728 : ℚ) ^ k) ≠ 0 :=
    (map_ne_zero (algebraMap ℚ ℝ)).mpr (pow_ne_zero _ (by norm_num))
  have hu : IsUnit ((algebraMap ℚ ℝ) (1 / 1728)) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero (algebraMap ℚ ℝ)).mpr (by norm_num))
  rw [polePoly_eq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, roots_C_mul _ hC,
    show C ((algebraMap ℚ ℝ) (1 / 1728)) * polyX =
      C ((algebraMap ℚ ℝ) (1 / 1728)) * polyX + C 0 by rw [C_0, add_zero],
    roots_comp_C_mul_X_add_C _ _ _ hu]
  congr 1
  funext x
  rw [Ring.inverse_eq_inv, sub_zero, map_div₀, map_one, map_ofNat]
  norm_num

/-- **BSS (3.3), Theorem 3.1.** For `α, β > -1`, the `k` roots of `Q_k^{α,β}` are real, simple
and lie in `(0, 1)` (conditional on the cited [DLMF, §18.2(vi)], `JacobiSimpleRealZeros`). -/
theorem bssQ_roots_real (hZ : JacobiSimpleRealZeros) {k : ℕ} {α β : ℚ} (hα : -1 < α)
    (hβ : -1 < β) :
    ((bssQ k α β).map (algebraMap ℚ ℝ)).roots.Nodup ∧
      Multiset.card ((bssQ k α β).map (algebraMap ℚ ℝ)).roots = k ∧
      ∀ x ∈ ((bssQ k α β).map (algebraMap ℚ ℝ)).roots, 0 < x ∧ x < 1 := by
  obtain ⟨hnd, hcard, hmem⟩ := hZ.rat β α hβ hα k
  rw [roots_bssQ_map_real (ascPochhammer_bss_pos hα hβ).ne']
  refine ⟨hnd.map fun a b hab => ?_, by rw [Multiset.card_map, hcard], fun x hx => ?_⟩
  · have hab' : (a + 1) / 2 = (b + 1) / 2 := hab
    linarith
  · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hmem a ha
    constructor <;> linarith

/-- **Proposition 4.3.** For `α, β > -1`, the `k` roots of `𝒫` are real, simple and lie in
`(0, 1728)` (conditional on the cited `JacobiSimpleRealZeros`). -/
theorem polePoly_roots_real (hZ : JacobiSimpleRealZeros) {k : ℕ} {α β : ℚ} (hα : -1 < α)
    (hβ : -1 < β) :
    ((polePoly k α β).map (algebraMap ℚ ℝ)).roots.Nodup ∧
      Multiset.card ((polePoly k α β).map (algebraMap ℚ ℝ)).roots = k ∧
      ∀ x ∈ ((polePoly k α β).map (algebraMap ℚ ℝ)).roots, 0 < x ∧ x < 1728 := by
  obtain ⟨hnd, hcard, hmem⟩ := bssQ_roots_real hZ (k := k) hα hβ
  rw [roots_polePoly_map_real]
  refine ⟨hnd.map fun a b hab => ?_, by rw [Multiset.card_map, hcard], fun x hx => ?_⟩
  · have hab' : 1728 * a = 1728 * b := hab
    linarith
  · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hmem a ha
    constructor <;> linarith

/-- **BSS (4.9).** For `α, β > -1`, `𝒫(X) = ∏_{j=1}^k (X - 1728 x_{k,j})` over the roots
`x_{k,j}` of `Q_k^{α,β}` (conditional on the cited `JacobiSimpleRealZeros`). -/
theorem polePoly_map_real_eq_prod (hZ : JacobiSimpleRealZeros) {k : ℕ} {α β : ℚ}
    (hα : -1 < α) (hβ : -1 < β) :
    (polePoly k α β).map (algebraMap ℚ ℝ) =
      (((bssQ k α β).map (algebraMap ℚ ℝ)).roots.map fun x => polyX - C (1728 * x)).prod := by
  have hpoch := (ascPochhammer_bss_pos (k := k) hα hβ).ne'
  obtain ⟨hm, hd⟩ := polePoly_monic hpoch
  have hmR := hm.map (algebraMap ℚ ℝ)
  have hcard : Multiset.card ((polePoly k α β).map (algebraMap ℚ ℝ)).roots =
      ((polePoly k α β).map (algebraMap ℚ ℝ)).natDegree := by
    rw [natDegree_map, hd, roots_polePoly_map_real, Multiset.card_map,
      (bssQ_roots_real hZ (k := k) hα hβ).2.1]
  have h1 := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hmR.leadingCoeff, C_1, one_mul] at h1
  rw [← h1, roots_polePoly_map_real]
  simp only [Multiset.map_map, Function.comp_def]

/-! ### The residue (Stieltjes) system (BSS (3.2), Theorem 3.1) -/

/-- At a simple root `x` of a monic split polynomial `f`,
`f'(x) ≠ 0` and `f''(x) = 2 f'(x) ∑_{y ≠ x} 1/(x - y)`. -/
theorem eval_derivative_derivative_of_simple_root {K : Type*} [Field K] [DecidableEq K]
    {f : K[X]} (hm : f.Monic) (hs : Multiset.card f.roots = f.natDegree) (hnd : f.roots.Nodup)
    {x : K} (hx : x ∈ f.roots) :
    (derivative f).eval x ≠ 0 ∧ (derivative (derivative f)).eval x =
      2 * (derivative f).eval x * ((f.roots.erase x).map fun y => 1 / (x - y)).sum := by
  obtain ⟨R, hR⟩ : ∃ R : K[X], R = ((f.roots.erase x).map fun a => polyX - C a).prod := ⟨_, rfl⟩
  have hf : f = (polyX - C x) * R := by
    have h1 := C_leadingCoeff_mul_prod_multiset_X_sub_C hs
    rw [hm.leadingCoeff, C_1, one_mul] at h1
    rw [← h1]
    conv_lhs => rw [← Multiset.cons_erase hx]
    rw [Multiset.map_cons, Multiset.prod_cons, hR]
  have hRroots : R.roots = f.roots.erase x := by rw [hR, roots_multiset_prod_X_sub_C]
  have hR0 : R ≠ 0 := right_ne_zero_of_mul (hf ▸ hm.ne_zero)
  have hRx : R.eval x ≠ 0 := by
    intro h0
    have hmem : x ∈ R.roots := (mem_roots hR0).mpr h0
    rw [hRroots] at hmem
    exact hnd.notMem_erase hmem
  have hRs : R.Splits := by
    rw [splits_iff_card_roots, hRroots, hR, natDegree_multiset_prod_X_sub_C_eq_card]
  have hlog := hRs.eval_derivative_div_eval_of_ne_zero hRx
  rw [hRroots] at hlog
  have e1 : (derivative f).eval x = R.eval x := by
    rw [hf, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  have e2 : (derivative (derivative f)).eval x = 2 * (derivative R).eval x := by
    rw [hf, derivative_mul, derivative_add, derivative_mul, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, derivative_one, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, one_mul, zero_add, add_zero]
    ring
  have hq : R.eval x * ((derivative R).eval x / R.eval x) = (derivative R).eval x := by
    field_simp
  refine ⟨by rw [e1]; exact hRx, ?_⟩
  rw [e2, e1, ← hlog]
  linear_combination (-2 : K) * hq

/-- **BSS (3.2), Theorem 3.1 (existence).** For `α, β > -1`, the roots `x_{k,1}, …, x_{k,k}` of
`Q_k^{α,β}` solve the residue system
`(α+1)/x_i + (β+1)/(x_i - 1) + 2 ∑_{j≠i} 1/(x_i - x_j) = 0` (conditional on the cited
`JacobiSimpleRealZeros`, which gives that they are simple and lie in `(0, 1)`). -/
theorem bssQ_roots_residueSystem (hZ : JacobiSimpleRealZeros) {k : ℕ} {α β : ℚ}
    (hα : -1 < α) (hβ : -1 < β) :
    ∀ x ∈ ((bssQ k α β).map (algebraMap ℚ ℝ)).roots,
      ((α : ℝ) + 1) / x + ((β : ℝ) + 1) / (x - 1) +
        2 * ((((bssQ k α β).map (algebraMap ℚ ℝ)).roots.erase x).map
          fun y => 1 / (x - y)).sum = 0 := by
  intro x hx
  obtain ⟨hnd, hcard, hmem⟩ := bssQ_roots_real hZ (k := k) hα hβ
  have hpoch := (ascPochhammer_bss_pos (k := k) hα hβ).ne'
  obtain ⟨hm, hd⟩ := bssQ_monic hpoch
  have hmR := hm.map (algebraMap ℚ ℝ)
  have hs : Multiset.card ((bssQ k α β).map (algebraMap ℚ ℝ)).roots =
      ((bssQ k α β).map (algebraMap ℚ ℝ)).natDegree := by
    rw [natDegree_map, hd, hcard]
  obtain ⟨hQ1, hQ2⟩ := eval_derivative_derivative_of_simple_root hmR hs hnd hx
  have hQ0 : ((bssQ k α β).map (algebraMap ℚ ℝ)).eval x = 0 := (isRoot_of_mem_roots hx).eq_zero
  obtain ⟨hx0, hx1⟩ := hmem x hx
  have hODE := congrArg (fun p => (p.map (algebraMap ℚ ℝ)).eval x) (bssQ_ode k α β)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_zero, ← derivative_map, eval_add,
    eval_mul, eval_sub, eval_one, eval_X, eval_C, eval_zero, eq_ratCast] at hODE
  push_cast at hODE
  generalize (derivative (derivative ((bssQ k α β).map (algebraMap ℚ ℝ)))).eval x = q2
    at hODE hQ2
  generalize (derivative ((bssQ k α β).map (algebraMap ℚ ℝ))).eval x = q1 at hODE hQ1 hQ2
  generalize ((bssQ k α β).map (algebraMap ℚ ℝ)).eval x = q0 at hODE hQ0
  generalize ((((bssQ k α β).map (algebraMap ℚ ℝ)).roots.erase x).map
    fun y => 1 / (x - y)).sum = S at hQ2 ⊢
  have hxne : x ≠ 0 := hx0.ne'
  have hx1ne : x - 1 ≠ 0 := by linarith
  have e1 : ((α : ℝ) + 1) / x * x = α + 1 := div_mul_cancel₀ _ hxne
  have e2 : ((β : ℝ) + 1) / (x - 1) * (x - 1) = β + 1 := div_mul_cancel₀ _ hx1ne
  have hmul : (((α : ℝ) + 1) / x + ((β : ℝ) + 1) / (x - 1) + 2 * S) * (q1 * x * (x - 1)) = 0 := by
    linear_combination (q1 * (x - 1)) * e1 + (q1 * x) * e2 - hODE + (x * (1 - x)) * hQ2 +
      ((k : ℝ) * (k + α + β + 1)) * hQ0
  exact (mul_eq_zero.mp hmul).resolve_right (mul_ne_zero (mul_ne_zero hQ1 hxne) hx1ne)

/-! ### Dedekind `η` on `ℍ`: `D log η = E₂/24` -/

/-- Mathlib's Dedekind eta function `η`, as a function on `ℍ`. -/
noncomputable def etaUpper (z : ℍ) : ℂ := eta z

theorem etaUpper_apply (z : ℍ) : etaUpper z = eta z := (rfl)

theorem etaUpper_ne_zero (z : ℍ) : etaUpper z ≠ 0 := by
  rw [etaUpper_apply]
  exact eta_ne_zero z.im_pos

theorem mdifferentiable_etaUpper : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) etaUpper := by
  intro z
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have he : etaUpper ∘ ofComplex =ᶠ[nhds (z : ℂ)] eta :=
    (eventuallyEq_coe_comp_ofComplex z.im_pos).fun_comp eta
  exact (differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos).congr_of_eventuallyEq he

/-- **`D η = (E₂/24) η`**, i.e. `D log η = E₂/24` (from Mathlib's `logDeriv_eta_eq_E2`). -/
theorem normalizedDerivOfComplex_etaUpper (z : ℍ) :
    D etaUpper z = EisensteinSeries.E2 z / 24 * etaUpper z := by
  have he : etaUpper ∘ ofComplex =ᶠ[nhds (z : ℂ)] eta :=
    (eventuallyEq_coe_comp_ofComplex z.im_pos).fun_comp eta
  have hne : eta z ≠ 0 := etaUpper_ne_zero z
  have hd : deriv eta z = logDeriv eta z * eta z := by rw [logDeriv_apply, div_mul_cancel₀ _ hne]
  rw [normalizedDerivOfComplex, he.deriv_eq, hd, logDeriv_eta_eq_E2, etaUpper_apply]
  have hπ : (Real.pi : ℂ) * (Real.pi : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast Real.pi_ne_zero)
  have hI : Complex.I * Complex.I⁻¹ = 1 := mul_inv_cancel₀ Complex.I_ne_zero
  linear_combination (EisensteinSeries.E2 z * eta z / 24) * (Complex.I * Complex.I⁻¹) * hπ +
    (EisensteinSeries.E2 z * eta z / 24) * hI

theorem mdifferentiable_etaUpper_inv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) etaUpper⁻¹ :=
  fun z => (mdifferentiable_etaUpper z).inv (etaUpper_ne_zero z)

/-- `D (1/η) = -(E₂/24) (1/η)`. -/
theorem normalizedDerivOfComplex_etaUpper_inv (z : ℍ) :
    D etaUpper⁻¹ z = -(EisensteinSeries.E2 z / 24) * (etaUpper z)⁻¹ := by
  have h := normalizedDerivOfComplex_mul etaUpper etaUpper⁻¹ mdifferentiable_etaUpper
    mdifferentiable_etaUpper_inv
  have h1 : etaUpper * etaUpper⁻¹ = 1 := by
    funext w
    rw [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_cancel₀ (etaUpper_ne_zero w)]
  have h0 : D (1 : ℍ → ℂ) = 0 := normalizedDerivOfComplex_const 1
  rw [h1, h0] at h
  have hz := congrFun h z
  have hw : etaUpper z * (etaUpper z)⁻¹ = 1 := mul_inv_cancel₀ (etaUpper_ne_zero z)
  simp only [Pi.zero_apply, Pi.add_apply, Pi.mul_apply, Pi.inv_apply] at hz
  rw [normalizedDerivOfComplex_etaUpper] at hz
  linear_combination (-(etaUpper z)⁻¹) * hz -
    (D etaUpper⁻¹ z + EisensteinSeries.E2 z / 24 * (etaUpper z)⁻¹) * hw

theorem normalizedDerivOfComplex_etaUpper_inv_pow_apply (m : ℕ) (z : ℍ) :
    D (etaUpper⁻¹ ^ m) z = -((m : ℂ) / 24 * EisensteinSeries.E2 z) * (etaUpper z)⁻¹ ^ m := by
  rw [normalizedDerivOfComplex_pow _ m mdifferentiable_etaUpper_inv]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.inv_apply,
    normalizedDerivOfComplex_etaUpper_inv]
  cases m with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel, pow_succ]; push_cast; ring

theorem normalizedDerivOfComplex_etaUpper_inv_pow (m : ℕ) :
    D (etaUpper⁻¹ ^ m) = (-(m : ℂ) / 24) • (EisensteinSeries.E2 * etaUpper⁻¹ ^ m) := by
  funext z
  rw [normalizedDerivOfComplex_etaUpper_inv_pow_apply]
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, smul_eq_mul]
  ring

theorem normalizedDerivOfComplex_two_etaUpper_inv_pow_apply (m : ℕ) (z : ℍ) :
    D (D (etaUpper⁻¹ ^ m)) z = (-(m : ℂ) / 24) * (D EisensteinSeries.E2 z * (etaUpper z)⁻¹ ^ m +
      EisensteinSeries.E2 z * (-((m : ℂ) / 24 * EisensteinSeries.E2 z) * (etaUpper z)⁻¹ ^ m)) := by
  have hN := mdifferentiable_etaUpper_inv.pow m
  rw [normalizedDerivOfComplex_etaUpper_inv_pow,
    normalizedDerivOfComplex_smul _ _ (E2_mdifferentiable.mul hN), Pi.smul_apply,
    normalizedDerivOfComplex_mul_apply E2_mdifferentiable hN,
    normalizedDerivOfComplex_etaUpper_inv_pow_apply, smul_eq_mul, Pi.pow_apply, Pi.inv_apply]

/-! ### The normal-form equation (BSS Proposition 4.1) and (4.8) -/

/-- **BSS Proposition 4.1.** `y = F_{ℓ-1}/η^{2ℓ}`, `ℓ = 12k + 4a + 6b + 1`, for the
Kaneko–Zagier modular form `F_{ℓ-1} = kzModularForm l μ k a b` of weight `ℓ - 1`. -/
noncomputable def kzNormalSolution (l μ : ℤ) (k a b : ℕ) (z : ℍ) : ℂ :=
  kzModularForm l μ k a b z / eta z ^ (2 * (12 * k + 4 * a + 6 * b + 1))

theorem kzNormalSolution_apply (l μ : ℤ) (k a b : ℕ) (z : ℍ) : kzNormalSolution l μ k a b z =
    kzModularForm l μ k a b z / eta z ^ (2 * (12 * k + 4 * a + 6 * b + 1)) := (rfl)

theorem kzNormalSolution_eq_mul (l μ : ℤ) (k a b : ℕ) : kzNormalSolution l μ k a b =
    ⇑(kzModularForm l μ k a b) * etaUpper⁻¹ ^ (2 * (12 * k + 4 * a + 6 * b + 1)) := by
  funext z
  rw [kzNormalSolution_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, etaUpper_apply,
    div_eq_mul_inv, inv_pow]

/-- `y = F_{ℓ-1}/η^{2ℓ}` is holomorphic on `ℍ`. -/
theorem mdifferentiable_kzNormalSolution (l μ : ℤ) (k a b : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (kzNormalSolution l μ k a b) := by
  rw [kzNormalSolution_eq_mul]
  exact (ModularFormClass.holo (kzModularForm l μ k a b)).mul
    (mdifferentiable_etaUpper_inv.pow _)

/-- **BSS Proposition 4.1, (4.4).** For `λ, μ ∈ {±1}`, `a = (λ+1)/2`, `b = (μ+1)/2` and
`ℓ = 12k + 4a + 6b + 1` (so `ℓ - 1` is the weight of `F_{ℓ-1}`), the function
`y = F_{ℓ-1}/η^{2ℓ}` satisfies `D²y = (ℓ²/144) E₄ y`, `D = (2πi)⁻¹ d/dz`; equivalently
`y'' + π²(ℓ/6)² E₄ y = 0`. -/
theorem kzNormalSolution_normalForm {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (k a b : ℕ) (ha : (a : ℤ) = (l + 1) / 2) (hb : (b : ℤ) = (μ + 1) / 2) (z : ℍ) :
    D (D (kzNormalSolution l μ k a b)) z =
      (12 * (k : ℂ) + 4 * a + 6 * b + 1) ^ 2 / 144 * E₄ z * kzNormalSolution l μ k a b z := by
  have hF := ModularFormClass.holo (kzModularForm l μ k a b)
  have hG := mdifferentiable_etaUpper_inv.pow (2 * (12 * k + 4 * a + 6 * b + 1))
  have hKZ := kzModularForm_kanekoZagier_ode hl hμ k a b ha hb z
  have hE2 := normalizedDerivOfComplex_E₂_apply z
  rw [kzNormalSolution_eq_mul, normalizedDerivOfComplex_two_mul_apply hF hG,
    normalizedDerivOfComplex_two_etaUpper_inv_pow_apply,
    normalizedDerivOfComplex_etaUpper_inv_pow_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  push_cast
  linear_combination (etaUpper z)⁻¹ ^ (2 * (12 * k + 4 * a + 6 * b + 1)) * hKZ -
    (12 * (k : ℂ) + 4 * a + 6 * b + 1) ^ 2 / 12 * kzModularForm l μ k a b z *
      (etaUpper z)⁻¹ ^ (2 * (12 * k + 4 * a + 6 * b + 1)) * hE2

/-- **BSS Theorem 4.2, (4.8).** For `μ = ±1` (and any `λ = l`, `a`, `b`), with
`J = j/1728`, `ε = 2a`, `δ = 2b`:
`F_{ℓ-1}/η^{2ℓ} = C · E₄^a E₆^b Q_k^{α,β}(J) / η^{2+4ε+6δ}`, `α = λ/3`, `β = μ/2`, with the
nonzero rational constant `C = (-1)^k 1728^k (k+α+β+1)_k/k!` (`bssConst_ne_zero`). -/
theorem kzNormalSolution_eq_bssQ {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (k a b : ℕ) (z : ℍ) :
    kzNormalSolution l μ k a b z =
      (bssConst k ((l : ℚ) / 3) ((μ : ℚ) / 2) : ℂ) * E₄ z ^ a * E₆ z ^ b *
        ((bssQ k ((l : ℚ) / 3) ((μ : ℚ) / 2)).map (algebraMap ℚ ℂ)).eval (jInvariant z / 1728) /
          eta z ^ (2 + 8 * a + 12 * b) := by
  have hrel := congrArg (fun p => (p.map (algebraMap ℚ ℂ)).eval (jInvariant z / 1728))
    (kanekoZagierModularPoly_comp_eq_bssQ l μ k (ascPochhammer_kanekoZagier_ne_zero hμ k))
  simp only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    eval_comp, eval_mul, eval_C, eval_X, eq_ratCast] at hrel
  rw [show ((1728 : ℚ) : ℂ) * (jInvariant z / 1728) = E₄ z ^ 3 / Δ z by
    rw [jInvariant_apply]; push_cast; ring] at hrel
  have hne : eta z ≠ 0 := etaUpper_ne_zero z
  have hΔ : Δ z = eta z ^ 24 := rfl
  rw [kzNormalSolution_apply, kzModularForm_apply hμ, hrel, hΔ,
    div_eq_div_iff (pow_ne_zero _ hne) (pow_ne_zero _ hne),
    show 2 * (12 * k + 4 * a + 6 * b + 1) = 24 * k + (2 + 8 * a + 12 * b) by ring,
    pow_add (eta (z : ℂ)) (24 * k) (2 + 8 * a + 12 * b), ← pow_mul]
  ring

/-- **BSS Theorem 4.2, (4.8)**, in terms of the monic pole polynomial `𝒫_ℓ` in `j`:
`F_{ℓ-1}/η^{2ℓ} = (-1)^k (k+α+β+1)_k/k! · E₄^a E₆^b 𝒫_ℓ(j) / η^{2+4ε+6δ}`. -/
theorem kzNormalSolution_eq_polePoly {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (k a b : ℕ) (z : ℍ) :
    kzNormalSolution l μ k a b z =
      (((-1) ^ k * (ascPochhammer ℚ k).eval ((k : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) /
        k.factorial : ℚ) : ℂ) * E₄ z ^ a * E₆ z ^ b *
        ((polePoly k ((l : ℚ) / 3) ((μ : ℚ) / 2)).map (algebraMap ℚ ℂ)).eval (jInvariant z) /
          eta z ^ (2 + 8 * a + 12 * b) := by
  have hP : ((polePoly k ((l : ℚ) / 3) ((μ : ℚ) / 2)).map (algebraMap ℚ ℂ)).eval (jInvariant z) =
      1728 ^ k *
        ((bssQ k ((l : ℚ) / 3) ((μ : ℚ) / 2)).map (algebraMap ℚ ℂ)).eval (jInvariant z / 1728) := by
    rw [polePoly_eq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_comp,
      eval_mul, eval_C, eval_X]
    simp only [eq_ratCast]
    rw [show ((1 / 1728 : ℚ) : ℂ) * jInvariant z = jInvariant z / 1728 by push_cast; ring,
      Rat.cast_pow, Rat.cast_ofNat]
  rw [kzNormalSolution_eq_bssQ hμ, hP, bssConst_eq]
  push_cast
  ring

/-! ### The pole interpretation (BSS §2 and Theorem 3.1)

In the reducible construction of [BSS, §2] (from [SS]) the pole invariants `x_j = J(w_j)` of the
weight-two form (2.2) must solve the residue system (2.3). The residue calculation is quoted
literature (`BSSResidueCriterion`, taken as a hypothesis); combined with the residue system for the
roots of `Q_k^{α,β}` (`bssQ_roots_residueSystem`) it shows that the roots of `Q_k^{α,β}` are pole
invariants of a residue-free form, i.e. `Q_k^{α,β}` is the pole polynomial
(`bssWeightTwoForm_residue_eq_zero`). -/

/-- `↑(∑_{y ∈ s} 1/(r - y)) = ∑_{c ∈ ↑s} 1/(↑r - c)` for a multiset `s` of reals. -/
theorem ofReal_multiset_sum_one_div (r : ℝ) (s : Multiset ℝ) :
    (((s.map fun y => 1 / (r - y)).sum : ℝ) : ℂ) =
      ((s.map fun t : ℝ => (t : ℂ)).map fun c => 1 / ((r : ℂ) - c)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.ofReal_add, ih, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_sub]

/-- **The Jacobi polynomial `Q_k^{α,β}` is the pole polynomial** ([BSS, §2–§3, Theorem 3.1]).
Let `ε = 2a`, `δ = 2b ∈ {0, 2}`, `α = (ε-1)/3`, `β = (δ-1)/2`, and let `w_1, …, w_k ∈ ℍ` have
invariants `J(w_j) = j(w_j)/1728` equal (as a multiset) to the roots of `Q_k^{α,β}`. Then the
weight-two form `F` of (2.2) with these poles has zero residue at every `w_i`. Conditional on the
cited `JacobiSimpleRealZeros` and `BSSResidueCriterion`. -/
theorem bssWeightTwoForm_residue_eq_zero (hZ : JacobiSimpleRealZeros)
    (hRes : BSSResidueCriterion) {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) {k : ℕ} (w : Fin k → ℍ)
    (hw : Finset.univ.val.map (fun j => jInvariant (w j) / 1728) =
      ((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map (algebraMap ℚ ℝ)).roots.map
        fun t : ℝ => (t : ℂ)) (i : Fin k) :
    ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      circleIntegral (fun z => bssWeightTwoForm a b
        (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) (w i) r = 0 := by
  have ha0 : (0 : ℚ) ≤ a := a.cast_nonneg
  have hb0 : (0 : ℚ) ≤ b := b.cast_nonneg
  have hα : (-1 : ℚ) < (2 * a - 1) / 3 := by linarith
  have hβ : (-1 : ℚ) < (2 * b - 1) / 2 := by linarith
  obtain ⟨hnd, -, hmem⟩ := bssQ_roots_real hZ (k := k) hα hβ
  have hS := bssQ_roots_residueSystem hZ (k := k) hα hβ
  have hnodup : (Finset.univ.val.map fun j => jInvariant (w j) / 1728).Nodup := by
    rw [hw]; exact hnd.map Complex.ofReal_injective
  have hxinj : Function.Injective fun j => jInvariant (w j) / 1728 := fun i j h =>
    Multiset.inj_on_of_nodup_map hnodup i (Finset.mem_val.mpr (Finset.mem_univ i)) j
      (Finset.mem_val.mpr (Finset.mem_univ j)) h
  have hroot : ∀ i, ∃ r ∈ ((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map
      (algebraMap ℚ ℝ)).roots, (r : ℂ) = jInvariant (w i) / 1728 := by
    intro i
    have h1 : jInvariant (w i) / 1728 ∈ Finset.univ.val.map fun j => jInvariant (w j) / 1728 :=
      Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ i))
    rw [hw] at h1
    exact Multiset.mem_map.mp h1
  refine hRes a b ha hb k w (fun i j h => hxinj ?_) (fun i => ?_) (fun i => ?_) i
  · have h' : jInvariant (w i) = jInvariant (w j) := h
    change jInvariant (w i) / 1728 = jInvariant (w j) / 1728
    rw [h']
  · obtain ⟨r, hr, hrx⟩ := hroot i
    obtain ⟨h0, h1⟩ := hmem r hr
    have hJ : jInvariant (w i) = 1728 * (r : ℂ) := by rw [hrx]; ring
    refine ⟨?_, ?_⟩
    · rw [hJ]
      exact mul_ne_zero (by norm_num) (by exact_mod_cast h0.ne')
    · rw [hJ]
      intro h
      have hr1 : (r : ℂ) = 1 := by linear_combination h / 1728
      have hr1' : r = 1 := by exact_mod_cast hr1
      linarith
  · obtain ⟨r, hr, hrx⟩ := hroot i
    have hE : ((((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map (algebraMap ℚ ℝ)).roots.erase
        r).map fun t : ℝ => (t : ℂ)) =
        (Finset.univ.erase i).val.map fun j => jInvariant (w j) / 1728 := by
      rw [Multiset.map_erase _ Complex.ofReal_injective, ← hw, hrx,
        ← Multiset.map_erase _ hxinj, Finset.erase_val]
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ((((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map
        (algebraMap ℚ ℝ)).roots.erase r).map fun y => 1 / (r - y)).sum := ⟨_, rfl⟩
    have hsum : (s : ℂ) = ∑ j ∈ Finset.univ.erase i,
        1 / (jInvariant (w i) / 1728 - jInvariant (w j) / 1728) := by
      rw [hs, ofReal_multiset_sum_one_div, hE, hrx, Finset.sum_eq_multiset_sum]
      simp only [Multiset.map_map, Function.comp_def]
    have hSr := hS r hr
    rw [← hs] at hSr
    have hSC := congrArg (fun t : ℝ => (t : ℂ)) hSr
    push_cast at hSC
    rw [hsum, hrx] at hSC
    linear_combination 6 * hSC

end ArithmeticOfJacobiPolynomials
