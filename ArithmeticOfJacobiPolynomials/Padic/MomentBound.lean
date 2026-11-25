/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Padic.ProjectiveDistance

/-!
# The projective moment bound (Lemma 2.2)

Lemma 2.2 of the manuscript (Section 2.2), with the quadratic
`σ` generalized from `t(1-t)` to any `σ ∈ ℤ_[p][X]` of degree `2` with unit leading
coefficient (this covers the reflected form `σ(X) = X(X+1)` used in Lemma 2.4).

The functional `I` is encoded only through its moments `μ : ℕ → ℚ_[p]`, `μ_j = I(t^j)`
(only `μ_0, …, μ_{2n-1}` matter): orthogonality `I(Hq) = 0` for `deg q < n` is
`∑_i H_i μ_{i+l} = 0` for `l < n`, and
`Q_H(t) = I_s((H(t) - H(s))/(t - s)) = ∑_j H_j ∑_{k<j} μ_{j-1-k} t^k` (`padicMomentQuotient`).
Roots are taken in `PadicAlgCl p`.

Main results:
* `ArithmeticOfJacobiPolynomials.projective_row_bound`: the row bound (2.4)
  `∑_{H(w)=0, w ≠ z} δ_p(z,w) ≤ E_p = v_p(c) - η_p`;
* `ArithmeticOfJacobiPolynomials.projective_roots_nodup`: the roots of `H` are simple;
* `ArithmeticOfJacobiPolynomials.projective_subset_bound`: the subset form
  `∑_{z ∈ S} ∑_{w ∈ T, w ≠ z} δ_p(z,w) ≤ |S| E_p` for sets `S, T` of roots;
* `ArithmeticOfJacobiPolynomials.projective_resultant_bound`: `v_p(Res(A,B)) ≤ deg A · E_p` for
every
  factorization `H = A B` into primitive factors.

The proof follows the manuscript. At a root `z`, write `H = (X - z) g`; then `Q_H(z) = I(g)`,
and orthogonality gives `I(g) = z^{-n} I(t^n g)`. For `‖z‖ ≤ 1` the coefficients of `g` are
integral; for `‖z‖ > 1` they have norm `≤ 1` as well (from `H(z) = 0`), so
`‖Q_H(z)‖ ≤ M ‖z‖^{-n}`, `M = max_{j<2n} ‖μ_j‖`. The Gauss norm root-mass identity turns the
row sum into `v_p(H'(z)) - (n-2) min{v_p(z), 0}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

namespace MomentAlgebra

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

/-- The synthetic-division coefficients `g_i = ∑_{i < j ≤ n} h_j z^{j-1-i}` of
`(∑_j h_j X^j) / (X - z)`. -/
noncomputable def quot (h : ℕ → L) (n : ℕ) (z : L) (i : ℕ) : L :=
  ∑ j ∈ range (n + 1), if i < j then h j * z ^ (j - 1 - i) else 0

/-- `J_l = ∑_{i<n} g_i m_{i+l}`. -/
noncomputable def shifted (h m : ℕ → L) (n : ℕ) (z : L) (l : ℕ) : L :=
  ∑ i ∈ range n, quot h n z i * m (i + l)

omit [IsUltrametricDist L] in
lemma quot_eq_zero (h : ℕ → L) {n : ℕ} (z : L) {i : ℕ} (hi : n ≤ i) : quot h n z i = 0 := by
  unfold quot
  refine sum_eq_zero fun j hj => ?_
  have : ¬ i < j := by simp at hj; omega
  simp [this]

omit [IsUltrametricDist L] in
lemma quot_succ (h : ℕ → L) {n : ℕ} (z : L) {i : ℕ} (hi : i < n) :
    quot h n z i = h (i + 1) + z * quot h n z (i + 1) := by
  unfold quot
  rw [mul_sum]
  have hmem : i + 1 ∈ range (n + 1) := by simp; omega
  have hsingle : h (i + 1) = ∑ j ∈ range (n + 1), if i + 1 = j then h j else 0 := by
    rw [sum_ite_eq, ite_eq_left hmem]
  rw [hsingle, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy j (i + 1) with hj | hj | hj
  · have h1 : ¬ i < j := by omega
    have h2 : ¬ i + 1 < j := by omega
    have h3 : ¬ i + 1 = j := by omega
    simp [h1, h2, h3]
  · subst hj
    simp
  · have h1 : i < j := by omega
    have h3 : ¬ i + 1 = j := by omega
    rw [ite_eq_left h1, ite_eq_right h3, ite_eq_left hj, zero_add, ← mul_assoc, mul_comm z,
      mul_assoc, ← pow_succ']
    congr 2
    omega

omit [IsUltrametricDist L] in
lemma quot_zero_mul (h : ℕ → L) (n : ℕ) (z : L)
    (hz : ∑ j ∈ range (n + 1), h j * z ^ j = 0) : z * quot h n z 0 = -h 0 := by
  have hterm : ∀ j ∈ range (n + 1), z * (if 0 < j then h j * z ^ (j - 1 - 0) else 0) =
      h j * z ^ j - (if j = 0 then h j else 0) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [ite_eq_left hj, ite_eq_right hj.ne', sub_zero, mul_left_comm, ← pow_succ']
      congr 2
      omega
  unfold quot
  rw [mul_sum, sum_congr rfl hterm, sum_sub_distrib, hz, sum_ite_eq' (range (n + 1)) 0,
    ite_eq_left (by simp)]
  ring

omit [IsUltrametricDist L] in
/-- The value of the moment quotient at a point equals `J_0`. -/
lemma moment_sum_eq_shifted_zero (h m : ℕ → L) (n : ℕ) (z : L) :
    ∑ j ∈ range (n + 1), h j * ∑ k ∈ range j, m (j - 1 - k) * z ^ k =
      shifted h m n z 0 := by
  unfold shifted quot
  simp only [add_zero, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  simp only [ite_mul, zero_mul]
  rw [sum_ite, sum_const_zero, add_zero]
  have hfilt : (range n).filter (fun i => i < j) = range j := by
    ext i; simp; omega
  rw [hfilt, mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < j := by simpa using hk
  have : j - 1 - (j - 1 - k) = k := by omega
  rw [this]
  ring

omit [IsUltrametricDist L] in
lemma shifted_succ (h m : ℕ → L) (n : ℕ) (z : L)
    (hz : ∑ j ∈ range (n + 1), h j * z ^ j = 0) {l : ℕ}
    (horth : ∑ j ∈ range (n + 1), h j * m (j + l) = 0) :
    shifted h m n z (l + 1) = z * shifted h m n z l := by
  have h0 := quot_zero_mul h n z hz
  rw [sum_range_succ'] at horth
  simp only [zero_add] at horth
  have hterm : ∀ i ∈ range n, h (i + 1) * m (i + 1 + l) =
      quot h n z i * m (i + (l + 1)) - z * (quot h n z (i + 1) * m (i + 1 + l)) := by
    intro i hi
    rw [quot_succ h z (by simpa using hi)]
    rw [show i + (l + 1) = i + 1 + l by omega]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum] at horth
  have hJ : shifted h m n z l = quot h n z 0 * m l +
      ∑ i ∈ range n, quot h n z (i + 1) * m (i + 1 + l) := by
    unfold shifted
    have := sum_range_succ' (fun i => quot h n z i * m (i + l)) n
    rw [sum_range_succ, quot_eq_zero h z le_rfl, zero_mul, add_zero] at this
    rw [this, add_comm]
    simp only [zero_add]
  unfold shifted at hJ ⊢
  rw [hJ, mul_add, ← mul_assoc, h0]
  linear_combination horth

omit [IsUltrametricDist L] in
lemma shifted_eq_pow_mul (h m : ℕ → L) (n : ℕ) (z : L)
    (hz : ∑ j ∈ range (n + 1), h j * z ^ j = 0)
    (horth : ∀ l < n, ∑ j ∈ range (n + 1), h j * m (j + l) = 0) :
    ∀ k ≤ n, shifted h m n z k = z ^ k * shifted h m n z 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [shifted_succ h m n z hz (horth k (by omega)), ih (by omega), pow_succ]
    ring

lemma norm_quot_le_one_of_norm_le_one (h : ℕ → L) (n : ℕ) {z : L} (hz1 : ‖z‖ ≤ 1)
    (hh : ∀ j, ‖h j‖ ≤ 1) (i : ℕ) : ‖quot h n z i‖ ≤ 1 := by
  unfold quot
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  split_ifs
  · rw [norm_mul, norm_pow]
    calc ‖h j‖ * ‖z‖ ^ (j - 1 - i) ≤ 1 * 1 :=
          mul_le_mul (hh j) (pow_le_one₀ (norm_nonneg _) hz1) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · simp

lemma norm_quot_le_one_of_one_lt_norm (h : ℕ → L) (n : ℕ) {z : L} (hz1 : 1 < ‖z‖)
    (hz : ∑ j ∈ range (n + 1), h j * z ^ j = 0)
    (hh : ∀ j, ‖h j‖ ≤ 1) (i : ℕ) : ‖quot h n z i‖ ≤ 1 := by
  have hmul : z ^ (i + 1) * quot h n z i =
      -∑ j ∈ range (n + 1), if i < j then 0 else h j * z ^ j := by
    rw [eq_neg_iff_add_eq_zero]
    unfold quot
    rw [mul_sum, ← sum_add_distrib]
    refine Eq.trans (sum_congr rfl fun j _ => ?_) hz
    split_ifs with hij
    · rw [add_zero, mul_left_comm, ← pow_add]
      congr 2
      omega
    · simp
  have hbound : ‖z ^ (i + 1) * quot h n z i‖ ≤ ‖z‖ ^ i := by
    rw [hmul, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      fun j _ => ?_
    split_ifs with hij
    · simp
    · rw [norm_mul, norm_pow]
      calc ‖h j‖ * ‖z‖ ^ j ≤ 1 * ‖z‖ ^ j := by gcongr; exact hh j
        _ ≤ ‖z‖ ^ i := by rw [one_mul]; exact pow_le_pow_right₀ hz1.le (by omega)
  rw [norm_mul, norm_pow, pow_succ] at hbound
  have hzi : 0 < ‖z‖ ^ i := by positivity
  by_contra hcon
  push Not at hcon
  have : ‖z‖ ^ i * ‖z‖ * 1 < ‖z‖ ^ i * ‖z‖ * ‖quot h n z i‖ := by
    have : 0 < ‖z‖ ^ i * ‖z‖ := by positivity
    exact mul_lt_mul_of_pos_left hcon this
  nlinarith

/-- The key estimate: at a point `z` with `‖z‖ ≤ 1`, `‖Q(z)‖ ≤ M`. -/
lemma norm_moment_sum_le_of_norm_le_one (h m : ℕ → L) (n : ℕ) {z : L} (hz1 : ‖z‖ ≤ 1)
    (hh : ∀ j, ‖h j‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M) (hm : ∀ i < 2 * n, ‖m i‖ ≤ M) :
    ‖∑ j ∈ range (n + 1), h j * ∑ k ∈ range j, m (j - 1 - k) * z ^ k‖ ≤ M := by
  rw [moment_sum_eq_shifted_zero]
  unfold shifted
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM fun i hi => ?_
  have hi' : i < n := by simpa using hi
  rw [norm_mul]
  calc ‖quot h n z i‖ * ‖m (i + 0)‖ ≤ 1 * M := by
        gcongr
        · exact norm_quot_le_one_of_norm_le_one h n hz1 hh i
        · exact hm _ (by omega)
    _ = M := one_mul M

/-- The key estimate at a nonintegral root: `‖Q(z)‖ · ‖z‖^n ≤ M`. -/
lemma norm_moment_sum_mul_pow_le (h m : ℕ → L) (n : ℕ) {z : L} (hz1 : 1 < ‖z‖)
    (hz : ∑ j ∈ range (n + 1), h j * z ^ j = 0)
    (horth : ∀ l < n, ∑ j ∈ range (n + 1), h j * m (j + l) = 0)
    (hh : ∀ j, ‖h j‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M) (hm : ∀ i < 2 * n, ‖m i‖ ≤ M) :
    ‖∑ j ∈ range (n + 1), h j * ∑ k ∈ range j, m (j - 1 - k) * z ^ k‖ * ‖z‖ ^ n ≤ M := by
  rw [moment_sum_eq_shifted_zero, ← norm_pow, ← norm_mul, mul_comm,
    ← shifted_eq_pow_mul h m n z hz horth n le_rfl]
  unfold shifted
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM fun i hi => ?_
  have hi' : i < n := by simpa using hi
  rw [norm_mul]
  calc ‖quot h n z i‖ * ‖m (i + n)‖ ≤ 1 * M := by
        gcongr
        · exact norm_quot_le_one_of_one_lt_norm h n hz1 hz hh i
        · exact hm _ (by omega)
    _ = M := one_mul M

end MomentAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- The second polynomial `Q_H(t) = I_s((H(t) - H(s))/(t - s))` attached to `H` and a
`ℚ_[p]`-linear functional `I` with moments `μ_j = I(t^j)`. Since
`(t^j - s^j)/(t - s) = ∑_{k<j} s^{j-1-k} t^k`, it is
`Q_H(t) = ∑_{j ≤ n} H_j ∑_{k<j} μ_{j-1-k} t^k`. -/
noncomputable def padicMomentQuotient (H : ℤ_[p][X]) (μ : ℕ → ℚ_[p]) : ℚ_[p][X] :=
  ∑ j ∈ range (H.natDegree + 1), C (H.coeff j : ℚ_[p]) *
    ∑ k ∈ range j, C (μ (j - 1 - k)) * X ^ k

/-- `η_p = min_{0 ≤ j ≤ 2n-1} v_p(μ_j)`, computed as `-log_p max_{j < 2n} ‖μ_j‖`. This is the
minimum of the valuations of the nonzero moments among `μ_0, …, μ_{2n-1}` (vanishing moments
have valuation `+∞` and do not contribute). -/
noncomputable def minMomentVal (p : ℕ) [Fact p.Prime] (μ : ℕ → ℚ_[p]) (n : ℕ) : ℝ :=
  -Real.logb p (((range (2 * n)).sup fun j => ‖μ j‖₊ : NNReal) : ℝ)

lemma padicMomentQuotient_def (H : ℤ_[p][X]) (μ : ℕ → ℚ_[p]) :
    padicMomentQuotient H μ = ∑ j ∈ range (H.natDegree + 1), C (H.coeff j : ℚ_[p]) *
      ∑ k ∈ range j, C (μ (j - 1 - k)) * X ^ k := by
  unfold padicMomentQuotient; rfl

lemma minMomentVal_def (p : ℕ) [Fact p.Prime] (μ : ℕ → ℚ_[p]) (n : ℕ) :
    minMomentVal p μ n = -Real.logb p (((range (2 * n)).sup fun j => ‖μ j‖₊ : NNReal) : ℝ) := by
  unfold minMomentVal; rfl

lemma norm_aeval_le_one_of_norm_le_one (σ : ℤ_[p][X]) {z : K} (hz : ‖z‖ ≤ 1) :
    ‖aeval z σ‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [Algebra.smul_def, norm_mul, norm_algebraMap_padicInt, norm_pow]
  calc ‖σ.coeff i‖ * ‖z‖ ^ i ≤ 1 * 1 :=
        mul_le_mul (σ.coeff i).norm_le_one (pow_le_one₀ (norm_nonneg _) hz) (by positivity)
          zero_le_one
    _ = 1 := one_mul 1

lemma norm_aeval_quadratic {σ : ℤ_[p][X]} (hσ : σ.natDegree = 2)
    (hlc : IsUnit σ.leadingCoeff) {z : K} (hz : 1 < ‖z‖) : ‖aeval z σ‖ = ‖z‖ ^ 2 := by
  rw [aeval_eq_sum_range, hσ]
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, Algebra.smul_def]
  have h2 : ‖σ.coeff 2‖ = 1 := by
    rw [← hσ]
    exact PadicInt.isUnit_iff.mp hlc
  have hlow : ‖algebraMap ℤ_[p] K (σ.coeff 0) * z ^ 0 + algebraMap ℤ_[p] K (σ.coeff 1) * z ^ 1‖
      ≤ ‖z‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_algebraMap_padicInt, pow_zero, norm_one, mul_one]
      exact (σ.coeff 0).norm_le_one.trans hz.le
    · rw [norm_mul, norm_algebraMap_padicInt, pow_one]
      calc ‖σ.coeff 1‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact (σ.coeff 1).norm_le_one
        _ = ‖z‖ := one_mul _
  have htop : ‖algebraMap ℤ_[p] K (σ.coeff 2) * z ^ 2‖ = ‖z‖ ^ 2 := by
    rw [norm_mul, norm_algebraMap_padicInt, h2, one_mul, norm_pow]
  have hlt : ‖z‖ < ‖z‖ ^ 2 := by nlinarith
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [htop]; linarith), htop]
  exact max_eq_right (by linarith)

/-- The hypotheses of the projective moment bound (Lemma 2.2), for a primitive
`H ∈ ℤ_[p][X]` of degree `n`, moments `μ_j = I(t^j)`, a quadratic `σ ∈ ℤ_[p][X]` with unit
leading coefficient and a constant `c ∈ ℚ_[p]^×`:
* orthogonality `I(t^l H) = ∑_i H_i μ_{i+l} = 0` for `l < n`;
* the root identity `σ(z) H'(z) Q_H(z) = c` at every root `z ∈ PadicAlgCl p` of `H`. -/
structure ProjectiveMomentHyp (H : ℤ_[p][X]) (μ : ℕ → ℚ_[p]) (σ : ℤ_[p][X]) (c : ℚ_[p]) :
    Prop where
  isPrimitive : H.IsPrimitive
  orthogonal : ∀ l < H.natDegree,
    ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0
  natDegree_sigma : σ.natDegree = 2
  isUnit_leadingCoeff_sigma : IsUnit σ.leadingCoeff
  ne_zero : c ≠ 0
  root_identity : ∀ z ∈ (H.map (algebraMap ℤ_[p] K)).roots,
    aeval z σ * aeval z (derivative H) * aeval z (padicMomentQuotient H μ) = algebraMap ℚ_[p] K c

namespace ProjectiveMomentHyp

variable {H : ℤ_[p][X]} {μ : ℕ → ℚ_[p]} {σ : ℤ_[p][X]} {c : ℚ_[p]}

lemma map_ne_zero (hyp : ProjectiveMomentHyp H μ σ c) :
    H.map (algebraMap ℤ_[p] K) ≠ 0 :=
  (Polynomial.map_ne_zero_iff algebraMap_padicInt_injective).mpr hyp.isPrimitive.ne_zero

lemma aeval_derivative_eq (z : K) :
    aeval z (derivative H) = (derivative (H.map (algebraMap ℤ_[p] K))).eval z := by
  rw [derivative_map, eval_map_algebraMap]

lemma aeval_derivative_ne_zero (hyp : ProjectiveMomentHyp H μ σ c) {z : K}
    (hz : z ∈ (H.map (algebraMap ℤ_[p] K)).roots) : aeval z (derivative H) ≠ 0 := by
  intro h0
  have := hyp.root_identity z hz
  rw [h0, mul_zero, zero_mul, eq_comm, map_eq_zero_iff _ (algebraMap ℚ_[p] K).injective] at this
  exact hyp.ne_zero this

/-- The root identity forces the roots of `H` to be simple. -/
lemma nodup_roots (hyp : ProjectiveMomentHyp H μ σ c) :
    (H.map (algebraMap ℤ_[p] K)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro w
  rw [count_roots]
  by_contra hlt
  push Not at hlt
  obtain ⟨hroot, hder⟩ := (one_lt_rootMultiplicity_iff_isRoot hyp.map_ne_zero).mp hlt
  have hw : w ∈ (H.map (algebraMap ℤ_[p] K)).roots := (mem_roots hyp.map_ne_zero).mpr hroot
  apply hyp.aeval_derivative_ne_zero hw
  rw [aeval_derivative_eq]
  exact hder

/-- The norm form of the key estimate: at a root `z`,
`‖c‖ · max{1,‖z‖}^{n-1} ≤ M · ‖H'(z)‖ · max{1,‖z‖}`, with `M = max_{j<2n} ‖μ_j‖`. -/
lemma key_norm_bound (hyp : ProjectiveMomentHyp H μ σ c) {z : K}
    (hz : z ∈ (H.map (algebraMap ℤ_[p] K)).roots) :
    ‖c‖ * max 1 ‖z‖ ^ (H.natDegree - 1) ≤
      (((range (2 * H.natDegree)).sup fun j => ‖μ j‖₊ : NNReal) : ℝ) *
        ‖aeval z (derivative H)‖ * max 1 ‖z‖ := by
  set n := H.natDegree with hn
  set M : ℝ := (((range (2 * n)).sup fun j => ‖μ j‖₊ : NNReal) : ℝ) with hM
  set h : ℕ → K := fun j => algebraMap ℚ_[p] K (H.coeff j : ℚ_[p]) with hh
  set m : ℕ → K := fun i => algebraMap ℚ_[p] K (μ i) with hm
  have hM0 : 0 ≤ M := NNReal.coe_nonneg _
  have hcoe : ∀ x : ℤ_[p], algebraMap ℤ_[p] K x = algebraMap ℚ_[p] K (x : ℚ_[p]) := fun x =>
    IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K x
  have hQ : aeval z (padicMomentQuotient H μ) =
      ∑ j ∈ range (n + 1), h j * ∑ k ∈ range j, m (j - 1 - k) * z ^ k := by
    simp [padicMomentQuotient, map_sum, hh, hm, ← hn]
  have hzero : ∑ j ∈ range (n + 1), h j * z ^ j = 0 := by
    have h1 : aeval z H = 0 := by
      rw [← eval_map_algebraMap]
      exact (mem_roots hyp.map_ne_zero).mp hz
    rw [aeval_eq_sum_range] at h1
    rw [← h1]
    refine sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, hcoe]
  have horthK : ∀ l < n, ∑ j ∈ range (n + 1), h j * m (j + l) = 0 := by
    intro l hl
    have := congrArg (algebraMap ℚ_[p] K) (hyp.orthogonal l hl)
    simpa [map_sum, hh, hm, ← hn] using this
  have hhb : ∀ j, ‖h j‖ ≤ 1 := by
    intro j
    simp only [hh, PadicAlgCl.norm_extends]
    exact (H.coeff j).norm_le_one
  have hmb : ∀ i < 2 * n, ‖m i‖ ≤ M := by
    intro i hi
    simp only [hm, PadicAlgCl.norm_extends, hM]
    have : ‖μ i‖₊ ≤ (range (2 * n)).sup fun j => ‖μ j‖₊ :=
      le_sup (f := fun j => ‖μ j‖₊) (mem_range.mpr hi)
    exact_mod_cast this
  have hid := congrArg norm (hyp.root_identity z hz)
  rw [norm_mul, norm_mul, PadicAlgCl.norm_extends, hQ] at hid
  set D := ‖aeval z (derivative H)‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  rcases le_or_gt ‖z‖ 1 with hz1 | hz1
  · rw [max_eq_left hz1, one_pow, mul_one, mul_one, ← hid]
    have hs := norm_aeval_le_one_of_norm_le_one σ hz1
    have hq := MomentAlgebra.norm_moment_sum_le_of_norm_le_one h m n hz1 hhb hM0 hmb
    calc ‖aeval z σ‖ * D * ‖∑ j ∈ range (n + 1), h j * ∑ k ∈ range j, m (j - 1 - k) * z ^ k‖
        ≤ 1 * D * M := by gcongr
      _ = M * D := by ring
  · rw [max_eq_right hz1.le, ← hid, norm_aeval_quadratic hyp.natDegree_sigma
      hyp.isUnit_leadingCoeff_sigma hz1]
    have hq := MomentAlgebra.norm_moment_sum_mul_pow_le h m n hz1 hzero horthK hhb hM0 hmb
    have hnpos : 0 < n := by
      rw [hn, ← natDegree_map_eq_of_injective algebraMap_padicInt_injective H,
        ← IsAlgClosed.card_roots_eq_natDegree]
      exact Multiset.card_pos_iff_exists_mem.mpr ⟨z, hz⟩
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk] at hq
    rw [hk, Nat.add_sub_cancel]
    set q := ‖∑ j ∈ range (k + 1 + 1), h j * ∑ i ∈ range j, m (j - 1 - i) * z ^ i‖
    have hzk : 0 ≤ ‖z‖ ^ k := by positivity
    calc ‖z‖ ^ 2 * D * q * ‖z‖ ^ k = D * ‖z‖ * (q * ‖z‖ ^ (k + 1)) := by ring
      _ ≤ D * ‖z‖ * M := by gcongr
      _ = M * D * ‖z‖ := by ring

open Classical in
/-- The row bound in multiset form: `∑_{w ≠ z} δ_p(z,w) ≤ E_p`. -/
lemma row_bound_multiset (hyp : ProjectiveMomentHyp H μ σ c) {z : K}
    (hz : z ∈ (H.map (algebraMap ℤ_[p] K)).roots) :
    (((H.map (algebraMap ℤ_[p] K)).roots.erase z).map fun w => projDist p z w).sum ≤
      padicVal p c - minMomentVal p μ H.natDegree := by
  set H' := H.map (algebraMap ℤ_[p] K) with hH'
  set R := H'.roots.erase z with hR
  set n := H.natDegree with hn
  set M : ℝ := (((range (2 * n)).sup fun j => ‖μ j‖₊ : NNReal) : ℝ) with hM
  have hinj : Function.Injective (algebraMap ℤ_[p] K) := algebraMap_padicInt_injective
  have hdeg : H'.natDegree = n := natDegree_map_eq_of_injective hinj H
  have hnodup := hyp.nodup_roots
  have hzR : z ∉ R := hnodup.notMem_erase
  have hcons : z ::ₘ R = H'.roots := Multiset.cons_erase hz
  have hcardR : R.card = n - 1 := by
    rw [hR, Multiset.card_erase_of_mem hz, IsAlgClosed.card_roots_eq_natDegree, hdeg]
    rfl
  have hderiv : (derivative H').eval z = H'.leadingCoeff * (R.map fun w => z - w).prod := by
    have hs := (IsAlgClosed.splits H').eq_prod_roots
    have := congrArg (fun f => (derivative f).eval z) hs
    simp only [derivative_C_mul, eval_mul, eval_C] at this
    rw [eval_multiset_prod_X_sub_C_derivative hz] at this
    exact this
  have hlcnorm : ‖H'.leadingCoeff‖ = ‖H.leadingCoeff‖ := by
    rw [hH', leadingCoeff_map_of_injective hinj, norm_algebraMap_padicInt]
  have hdist : ∀ w ∈ R, ‖z - w‖ ≠ 0 := fun w hw =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => hzR (h ▸ hw))
  have hprodR : (R.map fun w => ‖z - w‖).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h0
    exact hdist w hw hw0
  have hlc0 : ‖H.leadingCoeff‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr hyp.isPrimitive.ne_zero)
  have hlogD : Real.logb p ‖aeval z (derivative H)‖ = Real.logb p ‖H.leadingCoeff‖ +
      (R.map fun w => Real.logb p ‖z - w‖).sum := by
    rw [aeval_derivative_eq, ← hH', hderiv, norm_mul, norm_multiset_prod_map, hlcnorm,
      Real.logb_mul hlc0 hprodR, logb_multiset_prod_map _ _ hdist]
  have hmass : Real.logb p ‖H.leadingCoeff‖ +
      (H'.roots.map fun w => Real.logb p (max 1 ‖w‖)).sum = 0 :=
    logb_norm_leadingCoeff_add_sum hyp.isPrimitive
  rw [← hcons, Multiset.map_cons, Multiset.sum_cons] at hmass
  have hrow : (R.map fun w => projDist p z w).sum =
      -(R.map fun w => Real.logb p ‖z - w‖).sum + ((n - 1 : ℕ) : ℝ) * Real.logb p (max 1 ‖z‖) +
        (R.map fun w => Real.logb p (max 1 ‖w‖)).sum := by
    simp only [projDist_eq, Multiset.sum_map_add, Multiset.sum_map_neg, Multiset.map_const',
      Multiset.sum_replicate, nsmul_eq_mul, hcardR]
  set D := ‖aeval z (derivative H)‖ with hD
  have hkey : ‖c‖ * max 1 ‖z‖ ^ (n - 1) ≤ M * D * max 1 ‖z‖ := hyp.key_norm_bound hz
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hyp.ne_zero
  have hDpos : 0 < D := norm_pos_iff.mpr (hyp.aeval_derivative_ne_zero hz)
  have hmz : 0 < max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLHS : 0 < ‖c‖ * max 1 ‖z‖ ^ (n - 1) := by positivity
  have hMpos : 0 < M := by
    rcases (NNReal.coe_nonneg _ : (0 : ℝ) ≤ M).lt_or_eq with h | h
    · exact h
    · have hM0 : M = 0 := h.symm
      rw [hM0, zero_mul, zero_mul] at hkey
      linarith
  have hlog := (Real.logb_le_logb (one_lt_prime_real (p := p)) hLHS (by positivity)).mpr hkey
  rw [Real.logb_mul hc0.ne' (by positivity), Real.logb_pow, Real.logb_mul (by positivity)
    hmz.ne', Real.logb_mul hMpos.ne' hDpos.ne'] at hlog
  rw [hrow, padicVal_def]
  change _ ≤ -Real.logb p ‖c‖ - -Real.logb p M
  linarith

end ProjectiveMomentHyp

open Classical in
/-- **Lemma 2.2 (projective moment bound), row bound (2.4).**
Let `H ∈ ℤ_[p][X]` be primitive of degree `n`, let `μ_j = I(t^j)` be the moments of a
`ℚ_[p]`-linear functional `I` with `I(t^l H) = 0` for `l < n`, let `σ ∈ ℤ_[p][X]` be a
quadratic with unit leading coefficient (e.g. `t(1-t)` or `t(t+1)`), and suppose that
`σ(z) H'(z) Q_H(z) = c` at every root `z ∈ PadicAlgCl p` of `H`, for some `c ∈ ℚ_[p]^×`.
Then for every root `z`,
`∑_{H(w)=0, w ≠ z} δ_p(z,w) ≤ E_p = v_p(c) - η_p`, where `η_p = min_{j ≤ 2n-1} v_p(μ_j)`. -/
theorem projective_row_bound {H : ℤ_[p][X]} (hH : H.IsPrimitive) {μ : ℕ → ℚ_[p]}
    (horth : ∀ l < H.natDegree,
      ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0)
    {σ : ℤ_[p][X]} (hσ : σ.natDegree = 2) (hσlc : IsUnit σ.leadingCoeff)
    {c : ℚ_[p]} (hc : c ≠ 0)
    (hroot : ∀ z ∈ (H.map (algebraMap ℤ_[p] K)).roots,
      aeval z σ * aeval z (derivative H) * aeval z (padicMomentQuotient H μ) = algebraMap ℚ_[p] K c)
    {z : K} (hz : z ∈ (H.map (algebraMap ℤ_[p] K)).roots) :
    ∑ w ∈ (H.map (algebraMap ℤ_[p] K)).roots.toFinset.erase z, projDist p z w ≤
      padicVal p c - minMomentVal p μ H.natDegree := by
  have hyp : ProjectiveMomentHyp H μ σ c := ⟨hH, horth, hσ, hσlc, hc, hroot⟩
  rw [Finset.sum_eq_multiset_sum, Finset.erase_val, Multiset.toFinset_val,
    hyp.nodup_roots.dedup]
  exact hyp.row_bound_multiset hz

/-- **Lemma 2.2**, simplicity of the roots: under the hypotheses of the projective moment
bound the roots of `H` in `PadicAlgCl p` are simple. -/
theorem projective_roots_nodup {H : ℤ_[p][X]} (hH : H.IsPrimitive) {μ : ℕ → ℚ_[p]}
    (horth : ∀ l < H.natDegree,
      ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0)
    {σ : ℤ_[p][X]} (hσ : σ.natDegree = 2) (hσlc : IsUnit σ.leadingCoeff)
    {c : ℚ_[p]} (hc : c ≠ 0)
    (hroot : ∀ z ∈ (H.map (algebraMap ℤ_[p] K)).roots,
      aeval z σ * aeval z (derivative H) * aeval z (padicMomentQuotient H μ) =
        algebraMap ℚ_[p] K c) :
    (H.map (algebraMap ℤ_[p] K)).roots.Nodup :=
  ProjectiveMomentHyp.nodup_roots ⟨hH, horth, hσ, hσlc, hc, hroot⟩

open Classical in
/-- **Lemma 2.2**, subset form: for any sets `S, T` of roots of `H`,
`∑_{z ∈ S} ∑_{w ∈ T, w ≠ z} δ_p(z,w) ≤ |S| · E_p`. -/
theorem projective_subset_bound {H : ℤ_[p][X]} (hH : H.IsPrimitive) {μ : ℕ → ℚ_[p]}
    (horth : ∀ l < H.natDegree,
      ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0)
    {σ : ℤ_[p][X]} (hσ : σ.natDegree = 2) (hσlc : IsUnit σ.leadingCoeff)
    {c : ℚ_[p]} (hc : c ≠ 0)
    (hroot : ∀ z ∈ (H.map (algebraMap ℤ_[p] K)).roots,
      aeval z σ * aeval z (derivative H) * aeval z (padicMomentQuotient H μ) = algebraMap ℚ_[p] K c)
    (S T : Finset K) (hS : ∀ z ∈ S, z ∈ (H.map (algebraMap ℤ_[p] K)).roots)
    (hT : ∀ w ∈ T, w ∈ (H.map (algebraMap ℤ_[p] K)).roots) :
    ∑ z ∈ S, ∑ w ∈ T.erase z, projDist p z w ≤
      S.card * (padicVal p c - minMomentVal p μ H.natDegree) := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun z hzS => ?_
  refine le_trans ?_ (projective_row_bound hH horth hσ hσlc hc hroot (hS z hzS))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => projDist_nonneg z w
  refine Finset.erase_subset_erase _ fun w hw => ?_
  exact Multiset.mem_toFinset.mpr (hT w hw)

/-- **Lemma 2.2 (projective moment bound), resultant bound.** Under the hypotheses of
`projective_row_bound`, for every factorization `H = A B` into primitive `A, B ∈ ℤ_[p][X]`,
`v_p(Res(A,B)) ≤ deg A · E_p`. -/
theorem projective_resultant_bound {H : ℤ_[p][X]} (hH : H.IsPrimitive) {μ : ℕ → ℚ_[p]}
    (horth : ∀ l < H.natDegree,
      ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0)
    {σ : ℤ_[p][X]} (hσ : σ.natDegree = 2) (hσlc : IsUnit σ.leadingCoeff)
    {c : ℚ_[p]} (hc : c ≠ 0)
    (hroot : ∀ z ∈ (H.map (algebraMap ℤ_[p] K)).roots,
      aeval z σ * aeval z (derivative H) * aeval z (padicMomentQuotient H μ) = algebraMap ℚ_[p] K c)
    {A B : ℤ_[p][X]} (hAB : H = A * B) (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    padicVal p (resultant A B) ≤
      A.natDegree * (padicVal p c - minMomentVal p μ H.natDegree) := by
  classical
  have hyp : ProjectiveMomentHyp H μ σ c := ⟨hH, horth, hσ, hσlc, hc, hroot⟩
  set φ := algebraMap ℤ_[p] K with hφ
  have hinj : Function.Injective φ := algebraMap_padicInt_injective
  have hH0 := hyp.map_ne_zero
  have hroots : (H.map φ).roots = (A.map φ).roots + (B.map φ).roots := by
    rw [hAB, Polynomial.map_mul] at hH0 ⊢
    exact roots_mul hH0
  have hnodup := hyp.nodup_roots
  rw [hroots] at hnodup
  obtain ⟨-, -, hdisj⟩ := Multiset.nodup_add.mp hnodup
  have hdisj' : ∀ z ∈ (A.map φ).roots, ∀ w ∈ (B.map φ).roots, z ≠ w := by
    rintro z hz w hw rfl
    exact Multiset.disjoint_left.mp hdisj hz hw
  rw [padicVal_resultant_eq_sum_projDist hA hB hdisj']
  have hcardA : (A.map φ).roots.card = A.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective hinj]
  have hle := Multiset.sum_le_card_nsmul
    ((A.map φ).roots.map fun z => ((B.map φ).roots.map fun w => projDist p z w).sum)
    (padicVal p c - minMomentVal p μ H.natDegree) ?_
  · rwa [Multiset.card_map, hcardA, nsmul_eq_mul] at hle
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  have hzH : z ∈ (H.map φ).roots := by rw [hroots]; exact Multiset.mem_add.mpr (Or.inl hz)
  refine le_trans ?_ (hyp.row_bound_multiset hzH)
  rw [hroots, Multiset.erase_add_left_pos _ hz, Multiset.map_add, Multiset.sum_add]
  refine le_add_of_nonneg_left (Multiset.sum_nonneg fun x hx => ?_)
  obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
  exact projDist_nonneg z w

end ArithmeticOfJacobiPolynomials
