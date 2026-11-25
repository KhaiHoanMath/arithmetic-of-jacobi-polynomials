/- Assembled by AxiomProver. -/
module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The digit-sum function `Φ_{n,δ}` and its lower convex hull (Lemma A.5)

`s_3(r)` is the sum of the base-3 digits of `r`, and for `δ ∈ {0,1}` and `0 ≤ j ≤ n`,
`Φ_{n,δ}(j) = s_3(2j+δ) + s_3(n-j) - s_3(2n+δ)`.

The lower convex hull of finitely many points `(j, Φ(j))`, `0 ≤ j ≤ n`, viewed as a function
on `[0,n]`, is the greatest convex function on `[0,n]` lying below all the points:
`lowerHull n Φ x = sup {φ(x) : φ convex on [0,n], φ(j) ≤ Φ(j) for all j ≤ n}`.

* `lowerHull_dilation` (Lemma A.5): `H_{3m,0}(x) = H_{m,0}(x/3)` on `[0,3m]` and
  `H_{9m,1}(x) = H_{m,0}(x/9)` on `[0,9m]`, and the points whose abscissae are not divisible
  by `3`, respectively `9`, lie strictly above the hull.
* `digitPhi_singleEdge_*`: the integer form of the single-edge property used for
  Theorem A.1.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- The sum of the base-3 digits of `r`. -/
def digitSum3 (r : ℕ) : ℕ := (Nat.digits 3 r).sum

theorem digitSum3_eq (r : ℕ) : digitSum3 r = (Nat.digits 3 r).sum := (rfl)

/-- `Φ_{n,δ}(j) = s_3(2j+δ) + s_3(n-j) - s_3(2n+δ)`. -/
def digitPhi (n δ j : ℕ) : ℤ :=
  (digitSum3 (2 * j + δ) : ℤ) + digitSum3 (n - j) - digitSum3 (2 * n + δ)

theorem digitPhi_eq (n δ j : ℕ) : digitPhi n δ j =
    (digitSum3 (2 * j + δ) : ℤ) + digitSum3 (n - j) - digitSum3 (2 * n + δ) := (rfl)

@[simp] theorem digitSum3_zero : digitSum3 0 = 0 := by simp [digitSum3]

theorem digitSum3_three_mul_add (r d : ℕ) (hd : d < 3) :
    digitSum3 (3 * r + d) = digitSum3 r + d := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp
    · rw [digitSum3, mul_zero, zero_add,
        show d = d + 3 * 0 by ring, Nat.digits_add 3 (by norm_num) d 0 hd (Or.inl hd0.ne')]
      simp
  · rw [digitSum3, show 3 * r + d = d + 3 * r by ring,
      Nat.digits_add 3 (by norm_num) d r hd (Or.inr hr.ne'), List.sum_cons, ← digitSum3]
    ring

theorem digitSum3_three_mul (r : ℕ) : digitSum3 (3 * r) = digitSum3 r := by
  simpa using digitSum3_three_mul_add r 0 (by norm_num)

theorem digitSum3_nine_mul_add (x e : ℕ) (he : e < 9) :
    digitSum3 (9 * x + e) = digitSum3 x + digitSum3 e := by
  have h1 : 9 * x + e = 3 * (3 * x + e / 3) + e % 3 := by omega
  have h2 : e = 3 * (e / 3) + e % 3 := by omega
  rw [h1, digitSum3_three_mul_add _ _ (Nat.mod_lt _ (by norm_num)),
    digitSum3_three_mul_add _ _ (by omega)]
  conv_rhs => rw [h2, digitSum3_three_mul_add _ _ (Nat.mod_lt _ (by norm_num))]
  have : digitSum3 (e / 3) = e / 3 := by
    have : e / 3 < 3 := by omega
    have h := digitSum3_three_mul_add 0 (e / 3) this
    simpa using h
  rw [this]; ring

theorem digitSum3_succ_le (r : ℕ) : digitSum3 (r + 1) ≤ digitSum3 r + 1 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    obtain ⟨q, d, hd, rfl⟩ : ∃ q d, d < 3 ∧ r = 3 * q + d :=
      ⟨r / 3, r % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 3).symm⟩
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
    · rw [digitSum3_three_mul_add _ _ (by norm_num), add_zero,
        digitSum3_three_mul_add _ _ (by norm_num)]
    · rw [digitSum3_three_mul_add _ _ (by norm_num),
        show 3 * q + 1 + 1 = 3 * q + 2 by ring, digitSum3_three_mul_add _ _ (by norm_num)]
    · rw [digitSum3_three_mul_add _ _ (by norm_num),
        show 3 * q + 2 + 1 = 3 * (q + 1) by ring, digitSum3_three_mul]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp [digitSum3]
      · have := ih q (by omega)
        omega

/-- Subadditivity of the digit sum: `s_3(a + b) ≤ s_3(a) + s_3(b)`. -/
theorem digitSum3_add_le (a b : ℕ) : digitSum3 (a + b) ≤ digitSum3 a + digitSum3 b := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ N ih =>
    obtain ⟨a', d, hd, rfl⟩ : ∃ q d, d < 3 ∧ a = 3 * q + d := ⟨a / 3, a % 3,
      Nat.mod_lt _ (by norm_num), (Nat.div_add_mod a 3).symm⟩
    obtain ⟨b', e, he, rfl⟩ : ∃ q d, d < 3 ∧ b = 3 * q + d := ⟨b / 3, b % 3,
      Nat.mod_lt _ (by norm_num), (Nat.div_add_mod b 3).symm⟩
    subst h
    rw [digitSum3_three_mul_add _ _ hd, digitSum3_three_mul_add _ _ he]
    rcases Nat.eq_zero_or_pos (a' + b') with h0 | hpos
    · have ha : a' = 0 := by omega
      have hb : b' = 0 := by omega
      subst ha hb
      simp only [mul_zero, zero_add, digitSum3_zero]
      by_cases hde : d + e < 3
      · have := digitSum3_three_mul_add 0 (d + e) hde
        simp at this; omega
      · have := digitSum3_three_mul_add 1 (d + e - 3) (by omega)
        rw [show 3 * 1 + (d + e - 3) = d + e by omega] at this
        have h1 : digitSum3 1 = 1 := by simpa using digitSum3_three_mul_add 0 1 (by norm_num)
        omega
    · have hlt : a' + b' < 3 * a' + d + (3 * b' + e) := by omega
      by_cases hde : d + e < 3
      · rw [show 3 * a' + d + (3 * b' + e) = 3 * (a' + b') + (d + e) by ring,
          digitSum3_three_mul_add _ _ hde]
        have := ih (a' + b') hlt a' b' rfl
        omega
      · rw [show 3 * a' + d + (3 * b' + e) = 3 * (a' + b' + 1) + (d + e - 3) by omega,
          digitSum3_three_mul_add _ _ (by omega)]
        have h1 := ih (a' + b') hlt a' b' rfl
        have h2 := digitSum3_succ_le (a' + b')
        omega

theorem digitSum3_le (r : ℕ) : digitSum3 r ≤ r := Nat.digit_sum_le 3 r

theorem digitPhi_self (n δ : ℕ) : digitPhi n δ n = 0 := by
  simp [digitPhi]

/-! ### Digit identities -/

theorem digitSum3_two_mul_le (t : ℕ) : digitSum3 (2 * t) ≤ 2 * digitSum3 t := by
  have := digitSum3_add_le t t
  rw [show t + t = 2 * t by ring] at this; omega

/-- `Φ_{m,0}(j) ≥ Φ_{m,0}(0) - j`. -/
theorem digitPhi_ge_left (m j : ℕ) (hj : j ≤ m) : digitPhi m 0 0 - j ≤ digitPhi m 0 j := by
  have h1 := digitSum3_add_le (m - j) j
  rw [Nat.sub_add_cancel hj] at h1
  have h2 := digitSum3_le j
  simp only [digitPhi_eq, mul_zero, add_zero, digitSum3_zero, Nat.sub_zero, Nat.cast_zero,
    zero_add]
  omega

/-- `Φ_{m,0}(j) ≥ Φ_{m,0}(m) - (m - j) = -(m - j)`. -/
theorem digitPhi_ge_right (m j : ℕ) (hj : j ≤ m) :
    digitPhi m 0 m - ((m - j : ℕ) : ℤ) ≤ digitPhi m 0 j := by
  rw [digitPhi_self]
  have h1 := digitSum3_add_le (2 * j) (2 * (m - j))
  rw [show 2 * j + 2 * (m - j) = 2 * m by omega] at h1
  have h2 := digitSum3_two_mul_le (m - j)
  have h3 := digitSum3_le (m - j)
  simp only [digitPhi_eq, add_zero]
  omega

theorem digitPhi_three_mul_grid (m k : ℕ) (hk : k ≤ m) :
    digitPhi (3 * m) 0 (3 * k) = digitPhi m 0 k := by
  simp only [digitPhi_eq, add_zero]
  rw [show 2 * (3 * k) = 3 * (2 * k) by ring, show 3 * m - 3 * k = 3 * (m - k) by omega,
    show 2 * (3 * m) = 3 * (2 * m) by ring, digitSum3_three_mul, digitSum3_three_mul,
    digitSum3_three_mul]

theorem digitPhi_three_mul_one (m k : ℕ) (hk : k < m) :
    digitPhi m 0 k + 3 ≤ digitPhi (3 * m) 0 (3 * k + 1) := by
  simp only [digitPhi_eq, add_zero]
  rw [show 2 * (3 * k + 1) = 3 * (2 * k) + 2 by ring,
    show 3 * m - (3 * k + 1) = 3 * (m - k - 1) + 2 by omega,
    show 2 * (3 * m) = 3 * (2 * m) by ring, digitSum3_three_mul_add _ _ (by norm_num),
    digitSum3_three_mul_add _ _ (by norm_num), digitSum3_three_mul]
  have := digitSum3_succ_le (m - k - 1)
  rw [show m - k - 1 + 1 = m - k by omega] at this
  omega

theorem digitPhi_three_mul_two (m k : ℕ) (hk : k < m) :
    digitPhi m 0 (k + 1) + 1 ≤ digitPhi (3 * m) 0 (3 * k + 2) := by
  simp only [digitPhi_eq, add_zero]
  rw [show 2 * (3 * k + 2) = 3 * (2 * k + 1) + 1 by ring,
    show 3 * m - (3 * k + 2) = 3 * (m - k - 1) + 1 by omega,
    show 2 * (3 * m) = 3 * (2 * m) by ring, digitSum3_three_mul_add _ _ (by norm_num),
    digitSum3_three_mul_add _ _ (by norm_num), digitSum3_three_mul,
    show m - (k + 1) = m - k - 1 by omega]
  have := digitSum3_succ_le (2 * k + 1)
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at this
  omega

theorem digitSum3_nine_mul (x : ℕ) : digitSum3 (9 * x) = digitSum3 x := by
  simpa using digitSum3_nine_mul_add x 0 (by norm_num)

theorem digitSum3_eighteen_mul_add_one (m : ℕ) :
    digitSum3 (2 * (9 * m) + 1) = digitSum3 (2 * m) + 1 := by
  rw [show 2 * (9 * m) + 1 = 9 * (2 * m) + 1 by ring, digitSum3_nine_mul_add _ _ (by norm_num)]
  simp [digitSum3_eq]

theorem digitPhi_nine_mul_grid (m k : ℕ) (hk : k ≤ m) :
    digitPhi (9 * m) 1 (9 * k) = digitPhi m 0 k := by
  simp only [digitPhi_eq, add_zero]
  rw [digitSum3_eighteen_mul_add_one, digitSum3_eighteen_mul_add_one,
    show 9 * m - 9 * k = 9 * (m - k) by omega, digitSum3_nine_mul]
  omega

theorem digitPhi_nine_mul_low (m k r : ℕ) (hk : k < m) (hr0 : 0 < r) (hr : r ≤ 3) :
    digitPhi m 0 k + 3 ≤ digitPhi (9 * m) 1 (9 * k + r) := by
  simp only [digitPhi_eq, add_zero]
  rw [digitSum3_eighteen_mul_add_one,
    show 2 * (9 * k + r) + 1 = 9 * (2 * k) + (2 * r + 1) by ring,
    digitSum3_nine_mul_add _ _ (by omega),
    show 9 * m - (9 * k + r) = 9 * (m - k - 1) + (9 - r) by omega,
    digitSum3_nine_mul_add _ _ (by omega)]
  have := digitSum3_succ_le (m - k - 1)
  rw [show m - k - 1 + 1 = m - k by omega] at this
  have hs : 5 ≤ digitSum3 (2 * r + 1) + digitSum3 (9 - r) := by
    interval_cases r <;> simp [digitSum3_eq]
  omega

theorem digitPhi_nine_mul_high (m k r : ℕ) (hk : k < m) (hr0 : 4 ≤ r) (hr : r < 9) :
    digitPhi m 0 (k + 1) + 1 ≤ digitPhi (9 * m) 1 (9 * k + r) := by
  simp only [digitPhi_eq, add_zero]
  rw [digitSum3_eighteen_mul_add_one,
    show 2 * (9 * k + r) + 1 = 9 * (2 * k + 1) + (2 * r + 1 - 9) by omega,
    digitSum3_nine_mul_add _ _ (by omega),
    show 9 * m - (9 * k + r) = 9 * (m - k - 1) + (9 - r) by omega,
    digitSum3_nine_mul_add _ _ (by omega), show m - (k + 1) = m - k - 1 by omega]
  have := digitSum3_succ_le (2 * k + 1)
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at this
  have hs : 3 ≤ digitSum3 (2 * r + 1 - 9) + digitSum3 (9 - r) := by
    interval_cases r <;> simp [digitSum3_eq]
  omega

/-! ### The integer single-edge property -/

theorem digitPhi_nonneg_of_singleEdge {m δ : ℕ} (h0 : digitPhi m δ 0 = 1)
    (h : ∀ j, 0 < j → j < m → 1 ≤ digitPhi m δ j) (k : ℕ) (hk : k ≤ m) :
    0 ≤ digitPhi m δ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [h0]; norm_num
  rcases hk.lt_or_eq with hlt | rfl
  · have := h k hk0 hlt; omega
  · rw [digitPhi_self]

/-- Multiplying the degree by `3` preserves the single-edge property of `Φ_{·,0}`. -/
theorem digitPhi_singleEdge_three_mul {m : ℕ} (h0 : digitPhi m 0 0 = 1)
    (h : ∀ j, 0 < j → j < m → 1 ≤ digitPhi m 0 j) :
    digitPhi (3 * m) 0 0 = 1 ∧ ∀ j, 0 < j → j < 3 * m → 1 ≤ digitPhi (3 * m) 0 j := by
  have hnn := digitPhi_nonneg_of_singleEdge h0 h
  have hz : digitPhi (3 * m) 0 0 = 1 := by
    rw [show (0 : ℕ) = 3 * 0 from rfl, digitPhi_three_mul_grid m 0 (Nat.zero_le _)]; exact h0
  refine ⟨hz, fun j hj0 hj => ?_⟩
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ j = 3 * k + r :=
    ⟨j / 3, j % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 3).symm⟩
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · rw [add_zero, digitPhi_three_mul_grid m k (by omega)]; exact h k (by omega) (by omega)
  · have := digitPhi_three_mul_one m k (by omega)
    have := hnn k (by omega); omega
  · have := digitPhi_three_mul_two m k (by omega)
    have := hnn (k + 1) (by omega); omega

/-- From `Φ_{m,0}` to `Φ_{9m,1}`. -/
theorem digitPhi_singleEdge_nine_mul {m : ℕ} (h0 : digitPhi m 0 0 = 1)
    (h : ∀ j, 0 < j → j < m → 1 ≤ digitPhi m 0 j) :
    digitPhi (9 * m) 1 0 = 1 ∧ ∀ j, 0 < j → j < 9 * m → 1 ≤ digitPhi (9 * m) 1 j := by
  have hnn := digitPhi_nonneg_of_singleEdge h0 h
  have hz : digitPhi (9 * m) 1 0 = 1 := by
    rw [show (0 : ℕ) = 9 * 0 from rfl, digitPhi_nine_mul_grid m 0 (Nat.zero_le _)]; exact h0
  refine ⟨hz, fun j hj0 hj => ?_⟩
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 9 ∧ j = 9 * k + r :=
    ⟨j / 9, j % 9, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 9).symm⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [add_zero, digitPhi_nine_mul_grid m k (by omega)]; exact h k (by omega) (by omega)
  by_cases hr3 : r ≤ 3
  · have := digitPhi_nine_mul_low m k r (by omega) hr0 hr3
    have := hnn k (by omega); omega
  · have := digitPhi_nine_mul_high m k r (by omega) (by omega) hr
    have := hnn (k + 1) (by omega); omega

/-- The six values `Φ_{5,0}(j)` are `1, 2, 1, 2, 3, 0`. -/
theorem digitPhi_five_zero :
    digitPhi 5 0 0 = 1 ∧ digitPhi 5 0 1 = 2 ∧ digitPhi 5 0 2 = 1 ∧ digitPhi 5 0 3 = 2 ∧
      digitPhi 5 0 4 = 3 ∧ digitPhi 5 0 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [digitPhi_eq, digitSum3_eq]

theorem digitPhi_singleEdge_five :
    digitPhi 5 0 0 = 1 ∧ ∀ j, 0 < j → j < 5 → 1 ≤ digitPhi 5 0 j := by
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := digitPhi_five_zero
  refine ⟨h0, fun j hj0 hj => ?_⟩
  interval_cases j <;> simp [*]

/-- The single-edge property of `Φ_{5·3^a,0}` for all `a`. -/
theorem digitPhi_singleEdge_five_mul_three_pow (a : ℕ) :
    digitPhi (5 * 3 ^ a) 0 0 = 1 ∧
      ∀ j, 0 < j → j < 5 * 3 ^ a → 1 ≤ digitPhi (5 * 3 ^ a) 0 j := by
  induction a with
  | zero => simpa using digitPhi_singleEdge_five
  | succ a ih =>
    rw [pow_succ, show 5 * (3 ^ a * 3) = 3 * (5 * 3 ^ a) by ring]
    exact digitPhi_singleEdge_three_mul ih.1 ih.2

/-- The single-edge property of `Φ_{5·3^a,1}` for `a ≥ 2`. -/
theorem digitPhi_singleEdge_five_mul_three_pow_one (a : ℕ) (ha : 2 ≤ a) :
    digitPhi (5 * 3 ^ a) 1 0 = 1 ∧
      ∀ j, 0 < j → j < 5 * 3 ^ a → 1 ≤ digitPhi (5 * 3 ^ a) 1 j := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha
  have := digitPhi_singleEdge_five_mul_three_pow b
  rw [show 5 * 3 ^ (b + 2) = 9 * (5 * 3 ^ b) by ring]
  exact digitPhi_singleEdge_nine_mul this.1 this.2

/-! ### Lower convex hulls -/

/-- `φ` is a convex function on `[0,n]` lying below the points `(j, Φ(j))`, `0 ≤ j ≤ n`. -/
def IsHullMinorant (n : ℕ) (Φ : ℕ → ℤ) (φ : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc 0 (n : ℝ)) φ ∧ ∀ j ≤ n, φ j ≤ Φ j

theorem isHullMinorant_iff (n : ℕ) (Φ : ℕ → ℤ) (φ : ℝ → ℝ) : IsHullMinorant n Φ φ ↔
    ConvexOn ℝ (Set.Icc 0 (n : ℝ)) φ ∧ ∀ j ≤ n, φ j ≤ Φ j := Iff.rfl

/-- The lower convex hull `H` of the points `(j, Φ(j))`, `0 ≤ j ≤ n`, as a function on
`[0,n]`: the greatest convex function on `[0,n]` lying below all of the points,
`H(x) = sup {φ(x) : φ convex on [0,n], φ(j) ≤ Φ(j) for 0 ≤ j ≤ n}`. -/
noncomputable def lowerHull (n : ℕ) (Φ : ℕ → ℤ) (x : ℝ) : ℝ :=
  sSup ((fun φ : ℝ → ℝ => φ x) '' {φ | IsHullMinorant n Φ φ})

theorem lowerHull_def (n : ℕ) (Φ : ℕ → ℤ) (x : ℝ) :
    lowerHull n Φ x = sSup ((fun φ : ℝ → ℝ => φ x) '' {φ | IsHullMinorant n Φ φ}) := (rfl)

theorem IsHullMinorant.le_max {n : ℕ} {Φ : ℕ → ℤ} {φ : ℝ → ℝ} (h : IsHullMinorant n Φ φ)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (n : ℝ)) : φ x ≤ max (Φ 0 : ℝ) (Φ n) := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (n : ℝ) := ⟨le_rfl, Nat.cast_nonneg n⟩
  have hn : (n : ℝ) ∈ Set.Icc 0 (n : ℝ) := ⟨Nat.cast_nonneg n, le_rfl⟩
  have hseg : x ∈ segment ℝ (0 : ℝ) n := by rw [segment_eq_Icc (Nat.cast_nonneg n)]; exact hx
  have := h.1.le_on_segment h0 hn hseg
  have e0 := h.2 0 (Nat.zero_le _)
  have en := h.2 n le_rfl
  simp only [Nat.cast_zero] at e0
  exact this.trans (max_le_max e0 en)

theorem lowerHull_bddAbove (n : ℕ) (Φ : ℕ → ℤ) {x : ℝ} (hx : x ∈ Set.Icc 0 (n : ℝ)) :
    BddAbove ((fun φ : ℝ → ℝ => φ x) '' {φ | IsHullMinorant n Φ φ}) := by
  refine ⟨max (Φ 0 : ℝ) (Φ n), ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  exact hφ.le_max hx

theorem lowerHull_nonempty (n : ℕ) (Φ : ℕ → ℤ) (x : ℝ) :
    ((fun φ : ℝ → ℝ => φ x) '' {φ | IsHullMinorant n Φ φ}).Nonempty := by
  set B : ℝ := ∑ j ∈ Finset.range (n + 1), |(Φ j : ℝ)|
  refine ⟨-B, fun _ => -B, ⟨convexOn_const _ (convex_Icc _ _), fun j hj => ?_⟩, rfl⟩
  have : |(Φ j : ℝ)| ≤ B :=
    Finset.single_le_sum (f := fun j => |(Φ j : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have := neg_abs_le (Φ j : ℝ)
  linarith

theorem IsHullMinorant.le_lowerHull {n : ℕ} {Φ : ℕ → ℤ} {φ : ℝ → ℝ}
    (h : IsHullMinorant n Φ φ) {x : ℝ} (hx : x ∈ Set.Icc 0 (n : ℝ)) :
    φ x ≤ lowerHull n Φ x :=
  le_csSup (lowerHull_bddAbove n Φ hx) ⟨φ, h, rfl⟩

theorem lowerHull_le {n : ℕ} {Φ : ℕ → ℤ} {x c : ℝ}
    (h : ∀ φ, IsHullMinorant n Φ φ → φ x ≤ c) : lowerHull n Φ x ≤ c :=
  csSup_le (lowerHull_nonempty n Φ x) (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ)

/-- The lower hull is itself convex and lies below the points. -/
theorem lowerHull_isHullMinorant (n : ℕ) (Φ : ℕ → ℤ) : IsHullMinorant n Φ (lowerHull n Φ) := by
  refine ⟨⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩, fun j _ => ?_⟩
  · refine lowerHull_le fun φ hφ => ?_
    have h1 := hφ.1.2 hx hy ha hb hab
    have h2 := hφ.le_lowerHull hx
    have h3 := hφ.le_lowerHull hy
    simp only [smul_eq_mul] at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h3 hb]
  · exact lowerHull_le fun φ hφ => hφ.2 j ‹_›

theorem lowerHull_le_point (n : ℕ) (Φ : ℕ → ℤ) {j : ℕ} (hj : j ≤ n) :
    lowerHull n Φ j ≤ Φ j := (lowerHull_isHullMinorant n Φ).2 j hj

/-- Convexity is preserved by a positive rescaling of `[0, cB]` to `[0, B]`. -/
theorem convexOn_Icc_comp_mul {φ : ℝ → ℝ} {c B : ℝ} (hc : 0 < c)
    (h : ConvexOn ℝ (Set.Icc 0 (c * B)) φ) : ConvexOn ℝ (Set.Icc 0 B) (fun y => φ (c * y)) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : c * x ∈ Set.Icc 0 (c * B) :=
    ⟨mul_nonneg hc.le hx.1, mul_le_mul_of_nonneg_left hx.2 hc.le⟩
  have hy' : c * y ∈ Set.Icc 0 (c * B) :=
    ⟨mul_nonneg hc.le hy.1, mul_le_mul_of_nonneg_left hy.2 hc.le⟩
  have := h.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at this ⊢
  convert this using 2; ring

/-- **The general dilation principle.** Let `N = qM`, and let `f` agree with `g` on the grid,
`f(qk) = g(k)`, with every point `(j, f(j))` on or above the dilated hull `H_g(·/q)`. Then
`H_f(x) = H_g(x/q)` on `[0, N]`. -/
theorem lowerHull_dilation (q M : ℕ) (hq : 0 < q) (f g : ℕ → ℤ)
    (hgrid : ∀ k ≤ M, f (q * k) = g k)
    (hoff : ∀ j ≤ q * M, lowerHull M g (j / q) ≤ f j) {x : ℝ}
    (hx : x ∈ Set.Icc 0 ((q * M : ℕ) : ℝ)) : lowerHull (q * M) f x = lowerHull M g (x / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hxq : x / q ∈ Set.Icc 0 (M : ℝ) := by
    refine ⟨div_nonneg hx.1 hq'.le, ?_⟩
    rw [div_le_iff₀ hq', mul_comm]; exact_mod_cast hx.2
  apply le_antisymm
  · refine lowerHull_le fun φ hφ => ?_
    have hψ : IsHullMinorant M g (fun y => φ (q * y)) := by
      have h1 := hφ.1
      push_cast at h1
      refine ⟨convexOn_Icc_comp_mul hq' h1, fun k hk => ?_⟩
      have := hφ.2 (q * k) (Nat.mul_le_mul_left q hk)
      rw [hgrid k hk] at this
      push_cast at this; exact this
    have := hψ.le_lowerHull hxq
    rwa [mul_div_cancel₀ x hq'.ne'] at this
  · have hψ : IsHullMinorant (q * M) f (fun y => lowerHull M g (y / q)) := by
      refine ⟨?_, fun j hj => hoff j hj⟩
      have hc := convexOn_Icc_comp_mul (inv_pos.mpr hq') (B := ((q * M : ℕ) : ℝ))
        (by
          rw [show (q : ℝ)⁻¹ * ((q * M : ℕ) : ℝ) = M by push_cast; field_simp]
          exact (lowerHull_isHullMinorant M g).1)
      simpa [div_eq_inv_mul] using hc
    exact hψ.le_lowerHull hx

/-- Slope bound on the right: if `g(j) ≥ g(M) - (M - j)`, then `H_g(k + t) ≤ H_g(k) + t`. -/
theorem lowerHull_add_le (M : ℕ) (g : ℕ → ℤ) (hs : ∀ j ≤ M, g M - ((M - j : ℕ) : ℤ) ≤ g j)
    (k : ℕ) (hk : k < M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lowerHull M g (k + t) ≤ lowerHull M g k + t := by
  set H := lowerHull M g
  have hconv := (lowerHull_isHullMinorant M g).1
  have hMk : (0 : ℝ) < M - k := by
    have : (k : ℝ) < M := by exact_mod_cast hk
    linarith
  -- `H(k) ≥ g(M) - (M - k)`
  have hlow : (g M : ℝ) - (M - k) ≤ H k := by
    have hmin : IsHullMinorant M g (fun y => (g M : ℝ) - (M - y)) := by
      refine ⟨⟨convex_Icc _ _, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩, fun j hj => ?_⟩
      · simp only [smul_eq_mul]
        linear_combination (-(g M : ℝ) + M) * hab
      · have := hs j hj
        have e : ((M - j : ℕ) : ℝ) = (M : ℝ) - j := by push_cast [hj]; ring
        have : ((g M : ℤ) : ℝ) - ((M - j : ℕ) : ℝ) ≤ (g j : ℝ) := by exact_mod_cast this
        rw [e] at this; linarith
    have hk' : (k : ℝ) ∈ Set.Icc 0 (M : ℝ) := ⟨Nat.cast_nonneg k, by exact_mod_cast hk.le⟩
    exact hmin.le_lowerHull hk'
  have hM : H M ≤ g M := lowerHull_le_point M g le_rfl
  set s := t / (M - k) with hs_def
  have hs0 : 0 ≤ s := div_nonneg ht0 hMk.le
  have hs1 : s ≤ 1 := by
    rw [div_le_one hMk]
    have : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    linarith
  have hk' : (k : ℝ) ∈ Set.Icc 0 (M : ℝ) := ⟨Nat.cast_nonneg k, by exact_mod_cast hk.le⟩
  have hM' : (M : ℝ) ∈ Set.Icc 0 (M : ℝ) := ⟨Nat.cast_nonneg M, le_rfl⟩
  have h := hconv.2 hk' hM' (by linarith : 0 ≤ 1 - s) hs0 (by ring)
  simp only [smul_eq_mul] at h
  have e : (1 - s) * k + s * M = k + t := by
    rw [hs_def]; field_simp; ring
  rw [e] at h
  have : s * (M - k) = t := by rw [hs_def]; field_simp
  nlinarith

/-- Slope bound on the left: if `g(j) ≥ g(0) - j`, then `H_g(k + 1 - t) ≤ H_g(k + 1) + t`. -/
theorem lowerHull_sub_le (M : ℕ) (g : ℕ → ℤ) (hs : ∀ j ≤ M, g 0 - (j : ℤ) ≤ g j)
    (k : ℕ) (hk : k + 1 ≤ M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lowerHull M g ((k + 1 : ℕ) - t) ≤ lowerHull M g (k + 1 : ℕ) + t := by
  set H := lowerHull M g
  have hconv := (lowerHull_isHullMinorant M g).1
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hkM : ((k + 1 : ℕ) : ℝ) ∈ Set.Icc 0 (M : ℝ) := ⟨by positivity, by exact_mod_cast hk⟩
  have hlow : (g 0 : ℝ) - (k + 1 : ℕ) ≤ H (k + 1 : ℕ) := by
    have hmin : IsHullMinorant M g (fun y => (g 0 : ℝ) - y) := by
      refine ⟨⟨convex_Icc _ _, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩, fun j hj => ?_⟩
      · simp only [smul_eq_mul]
        linear_combination (-(g 0 : ℝ)) * hab
      · have := hs j hj
        have : ((g 0 : ℤ) : ℝ) - ((j : ℤ) : ℝ) ≤ (g j : ℝ) := by exact_mod_cast this
        push_cast at this ⊢; linarith
    exact hmin.le_lowerHull hkM
  have h0 : H 0 ≤ g 0 := by simpa using lowerHull_le_point M g (Nat.zero_le M)
  set s := t / (k + 1 : ℕ) with hs_def
  have hs0 : 0 ≤ s := div_nonneg ht0 hk1.le
  have hs1 : s ≤ 1 := by
    rw [div_le_one hk1]
    have : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
    linarith
  have h0' : (0 : ℝ) ∈ Set.Icc 0 (M : ℝ) := ⟨le_rfl, Nat.cast_nonneg M⟩
  have h := hconv.2 hkM h0' (by linarith : 0 ≤ 1 - s) hs0 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  have e : (1 - s) * ((k + 1 : ℕ) : ℝ) = (k + 1 : ℕ) - t := by
    rw [hs_def]; field_simp
  rw [e] at h
  have : s * (k + 1 : ℕ) = t := by rw [hs_def]; field_simp
  nlinarith

/-! ### Lemma A.5 -/

private theorem digitHull_off_three (m : ℕ) :
    ∀ j ≤ 3 * m, lowerHull m (digitPhi m 0) ((j : ℝ) / (3 : ℕ)) ≤ digitPhi (3 * m) 0 j ∧
      (¬ 3 ∣ j → lowerHull m (digitPhi m 0) ((j : ℝ) / (3 : ℕ)) < digitPhi (3 * m) 0 j) := by
  intro j hj
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ j = 3 * k + r :=
    ⟨j / 3, j % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 3).symm⟩
  have hsR := digitPhi_ge_right m
  have hsL := digitPhi_ge_left m
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · refine ⟨?_, fun h => absurd (Dvd.intro k (by ring)) h⟩
    have e : (((3 * k + 0 : ℕ) : ℝ) / (3 : ℕ)) = (k : ℕ) := by push_cast; ring
    rw [e, add_zero, digitPhi_three_mul_grid m k (by omega)]
    exact lowerHull_le_point m _ (by omega)
  all_goals
    have hk : k < m := by omega
  · have e : (((3 * k + 1 : ℕ) : ℝ) / (3 : ℕ)) = (k : ℝ) + 1 / 3 := by push_cast; ring
    rw [e]
    have h1 := lowerHull_add_le m (digitPhi m 0) hsR k hk (t := 1 / 3) (by norm_num)
      (by norm_num)
    have h2 := lowerHull_le_point m (digitPhi m 0) hk.le
    have h3 : ((digitPhi m 0 k + 3 : ℤ) : ℝ) ≤ digitPhi (3 * m) 0 (3 * k + 1) := by
      exact_mod_cast digitPhi_three_mul_one m k hk
    push_cast at h3
    constructor <;> intros <;> linarith
  · have e : (((3 * k + 2 : ℕ) : ℝ) / (3 : ℕ)) = ((k + 1 : ℕ) : ℝ) - 1 / 3 := by
      push_cast; ring
    rw [e]
    have h1 := lowerHull_sub_le m (digitPhi m 0) hsL k hk (t := 1 / 3) (by norm_num)
      (by norm_num)
    have h2 := lowerHull_le_point m (digitPhi m 0) (show k + 1 ≤ m by omega)
    have h3 : ((digitPhi m 0 (k + 1) + 1 : ℤ) : ℝ) ≤ digitPhi (3 * m) 0 (3 * k + 2) := by
      exact_mod_cast digitPhi_three_mul_two m k hk
    push_cast at h3
    constructor <;> intros <;> linarith

private theorem digitHull_off_nine (m : ℕ) :
    ∀ j ≤ 9 * m, lowerHull m (digitPhi m 0) ((j : ℝ) / (9 : ℕ)) ≤ digitPhi (9 * m) 1 j ∧
      (¬ 9 ∣ j → lowerHull m (digitPhi m 0) ((j : ℝ) / (9 : ℕ)) < digitPhi (9 * m) 1 j) := by
  intro j hj
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 9 ∧ j = 9 * k + r :=
    ⟨j / 9, j % 9, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 9).symm⟩
  have hsR := digitPhi_ge_right m
  have hsL := digitPhi_ge_left m
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · refine ⟨?_, fun h => absurd (Dvd.intro k (by ring)) h⟩
    have e : (((9 * k + 0 : ℕ) : ℝ) / (9 : ℕ)) = (k : ℕ) := by push_cast; ring
    rw [e, add_zero, digitPhi_nine_mul_grid m k (by omega)]
    exact lowerHull_le_point m _ (by omega)
  have hk : k < m := by omega
  by_cases hr3 : r ≤ 3
  · have e : (((9 * k + r : ℕ) : ℝ) / (9 : ℕ)) = (k : ℝ) + r / 9 := by push_cast; ring
    rw [e]
    have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr3
    have h1 := lowerHull_add_le m (digitPhi m 0) hsR k hk (t := r / 9) (by positivity)
      (by linarith)
    have h2 := lowerHull_le_point m (digitPhi m 0) hk.le
    have h3 : ((digitPhi m 0 k + 3 : ℤ) : ℝ) ≤ digitPhi (9 * m) 1 (9 * k + r) := by
      exact_mod_cast digitPhi_nine_mul_low m k r hk hr0 hr3
    push_cast at h3
    constructor <;> intros <;> linarith
  · have e : (((9 * k + r : ℕ) : ℝ) / (9 : ℕ)) = ((k + 1 : ℕ) : ℝ) - (9 - r : ℕ) / 9 := by
      push_cast [hr.le]; ring
    rw [e]
    have hr' : ((9 - r : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show 9 - r ≤ 5 by omega)
    have h1 := lowerHull_sub_le m (digitPhi m 0) hsL k hk (t := (9 - r : ℕ) / 9)
      (by positivity) (by linarith)
    have h2 := lowerHull_le_point m (digitPhi m 0) (show k + 1 ≤ m by omega)
    have h3 : ((digitPhi m 0 (k + 1) + 1 : ℤ) : ℝ) ≤ digitPhi (9 * m) 1 (9 * k + r) := by
      exact_mod_cast digitPhi_nine_mul_high m k r hk (by omega) hr
    push_cast at h3
    constructor <;> intros <;> linarith

/-- **Lemma A.5 (digit dilation).** For every integer `m ≥ 1`,
`H_{3m,0}(x) = H_{m,0}(x/3)` for `0 ≤ x ≤ 3m` and `H_{9m,1}(x) = H_{m,0}(x/9)` for
`0 ≤ x ≤ 9m`; all points whose abscissae are not divisible by `3`, respectively by `9`, lie
strictly above the indicated hull. -/
theorem digitHull_dilation (m : ℕ) (_hm : 1 ≤ m) :
    (∀ x ∈ Set.Icc (0 : ℝ) (3 * m),
      lowerHull (3 * m) (digitPhi (3 * m) 0) x = lowerHull m (digitPhi m 0) (x / 3)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (9 * m),
      lowerHull (9 * m) (digitPhi (9 * m) 1) x = lowerHull m (digitPhi m 0) (x / 9)) ∧
    (∀ j ≤ 3 * m, ¬ 3 ∣ j → lowerHull (3 * m) (digitPhi (3 * m) 0) j < digitPhi (3 * m) 0 j) ∧
    (∀ j ≤ 9 * m, ¬ 9 ∣ j →
      lowerHull (9 * m) (digitPhi (9 * m) 1) j < digitPhi (9 * m) 1 j) := by
  have h3 : ∀ x ∈ Set.Icc (0 : ℝ) (3 * m),
      lowerHull (3 * m) (digitPhi (3 * m) 0) x = lowerHull m (digitPhi m 0) (x / 3) := by
    intro x hx
    have := lowerHull_dilation 3 m (by norm_num) (digitPhi (3 * m) 0) (digitPhi m 0)
      (fun k hk => digitPhi_three_mul_grid m k hk)
      (fun j hj => (digitHull_off_three m j hj).1) (x := x) (by push_cast; exact hx)
    simpa using this
  have h9 : ∀ x ∈ Set.Icc (0 : ℝ) (9 * m),
      lowerHull (9 * m) (digitPhi (9 * m) 1) x = lowerHull m (digitPhi m 0) (x / 9) := by
    intro x hx
    have := lowerHull_dilation 9 m (by norm_num) (digitPhi (9 * m) 1) (digitPhi m 0)
      (fun k hk => digitPhi_nine_mul_grid m k hk)
      (fun j hj => (digitHull_off_nine m j hj).1) (x := x) (by push_cast; exact hx)
    simpa using this
  refine ⟨h3, h9, fun j hj hj3 => ?_, fun j hj hj9 => ?_⟩
  · rw [h3 j ⟨Nat.cast_nonneg j, by exact_mod_cast hj⟩]
    simpa using (digitHull_off_three m j hj).2 hj3
  · rw [h9 j ⟨Nat.cast_nonneg j, by exact_mod_cast hj⟩]
    simpa using (digitHull_off_nine m j hj).2 hj9

end ArithmeticOfJacobiPolynomials
