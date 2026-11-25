/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.LevelCount

/-!
# The carry indicators of Lemma 4.2

Fix `q = p^h` with `p ≥ 5`, let `a, b ∈ [1, q-1]` be the least residues of `α = λ/3` and
`β = μ/2` modulo `q`, `c = (a + b) mod q`, `d = ⌊(a + b)/q⌋` and `s = n mod q`. The manuscript
defines `E_x = 1_{s + x ≥ q}` (`carryInd q s x`), `m_q = 1_{E_a = E_b = 1, d + E_c = 1}`
(`levelM`), `η_q = 1_{c = q-1}` (`levelEta`), `b*_q = 0` if `c = q - 1` and `1 - d` otherwise
(`levelBStar`), and `e_q = η_q + E_a + E_b - E_c + b*_q - 2 m_q` (`levelE`, (4.4)).

Main results:
* `levelE_mem`: `e_q ∈ {0,1}` and `m_q + e_q ≤ 1` (first part of Lemma 4.2);
* `level_constant_eq`, `level_moment_ge`, `level_coeff_ge`, `level_coeff_attained`: the
  level-`q` contributions to `v_p(C_n)`, `v_p(μ_j)` and `v_p([t^j] y_n)`, written through the
  floor counts of `LevelCount`, compared with `η_q + E_a + E_b - E_c`, `-b*_q` and `m_q`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- `E_x = 1_{s + x ≥ q}`. -/
def carryInd (q s x : ℕ) : ℕ := if q ≤ s + x then 1 else 0

theorem carryInd_eq (q s x : ℕ) : carryInd q s x = if q ≤ s + x then 1 else 0 := (rfl)

/-- `m_q = 1_{E_a = E_b = 1, d + E_c = 1}`. -/
def levelM (q a b s : ℕ) : ℕ :=
  if q ≤ s + a ∧ q ≤ s + b ∧ (a + b) / q + carryInd q s ((a + b) % q) = 1 then 1 else 0

theorem levelM_eq (q a b s : ℕ) : levelM q a b s =
    if q ≤ s + a ∧ q ≤ s + b ∧ (a + b) / q + carryInd q s ((a + b) % q) = 1 then 1 else 0 :=
  (rfl)

/-- `η_q = 1_{c = q - 1}`. -/
def levelEta (q a b : ℕ) : ℕ := if (a + b) % q = q - 1 then 1 else 0

theorem levelEta_eq (q a b : ℕ) : levelEta q a b = if (a + b) % q = q - 1 then 1 else 0 := (rfl)

/-- `b*_q = 0` if `c = q - 1`, and `1 - d` otherwise. -/
def levelBStar (q a b : ℕ) : ℕ := if (a + b) % q = q - 1 then 0 else 1 - (a + b) / q

theorem levelBStar_eq (q a b : ℕ) :
    levelBStar q a b = if (a + b) % q = q - 1 then 0 else 1 - (a + b) / q := (rfl)

/-- `e_q = η_q + E_a + E_b - E_c + b*_q - 2 m_q` (4.4). -/
def levelE (q a b s : ℕ) : ℤ :=
  (levelEta q a b : ℤ) + carryInd q s a + carryInd q s b - carryInd q s ((a + b) % q) +
    levelBStar q a b - 2 * levelM q a b s

theorem levelE_eq (q a b s : ℕ) : levelE q a b s =
    (levelEta q a b : ℤ) + carryInd q s a + carryInd q s b - carryInd q s ((a + b) % q) +
      levelBStar q a b - 2 * levelM q a b s := (rfl)

/-! ### Case lemmas -/

theorem carryInd_cases (q s x : ℕ) :
    (carryInd q s x = 1 ∧ q ≤ s + x) ∨ (carryInd q s x = 0 ∧ s + x < q) := by
  rw [carryInd_eq]
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, by omega⟩

theorem levelM_cases (q a b s : ℕ) :
    (levelM q a b s = 1 ∧ q ≤ s + a ∧ q ≤ s + b ∧
        (a + b) / q + carryInd q s ((a + b) % q) = 1) ∨
      (levelM q a b s = 0 ∧ (s + a < q ∨ s + b < q ∨
        (a + b) / q + carryInd q s ((a + b) % q) ≠ 1)) := by
  rw [levelM_eq]
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · refine Or.inr ⟨rfl, ?_⟩
    by_cases h1 : q ≤ s + a
    · by_cases h2 : q ≤ s + b
      · exact Or.inr (Or.inr fun h3 => h ⟨h1, h2, h3⟩)
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)

theorem levelEta_cases (q a b : ℕ) :
    (levelEta q a b = 1 ∧ (a + b) % q = q - 1) ∨ (levelEta q a b = 0 ∧ (a + b) % q ≠ q - 1) := by
  rw [levelEta_eq]
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

theorem levelBStar_cases (q a b : ℕ) :
    (levelBStar q a b = 0 ∧ (a + b) % q = q - 1) ∨
      (levelBStar q a b = 1 - (a + b) / q ∧ (a + b) % q ≠ q - 1) := by
  rw [levelBStar_eq]
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

theorem div_cases_two {x q : ℕ} (hx : x < 2 * q) :
    (x / q = 0 ∧ x < q) ∨ (x / q = 1 ∧ q ≤ x) := by
  rcases lt_or_ge x q with h | h
  · exact Or.inl ⟨Nat.div_eq_of_lt h, h⟩
  · exact Or.inr ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h⟩

theorem div_cases_four {x q : ℕ} (hx : x < 4 * q) :
    (x / q = 0 ∧ x < q) ∨ (x / q = 1 ∧ q ≤ x ∧ x < 2 * q) ∨
      (x / q = 2 ∧ 2 * q ≤ x ∧ x < 3 * q) ∨ (x / q = 3 ∧ 3 * q ≤ x) := by
  rcases lt_or_ge x q with h1 | h1
  · exact Or.inl ⟨Nat.div_eq_of_lt h1, h1⟩
  rcases lt_or_ge x (2 * q) with h2 | h2
  · exact Or.inr (Or.inl ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h1, h2⟩)
  rcases lt_or_ge x (3 * q) with h3 | h3
  · exact Or.inr (Or.inr (Or.inl ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h2, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h3⟩))

/-- For `x < 2q`: `x = x mod q` with quotient `0`, or `x = x mod q + q` with quotient `1`. -/
theorem div_mod_cases_two {x q : ℕ} (hx : x < 2 * q) :
    (x / q = 0 ∧ x % q = x ∧ x < q) ∨ (x / q = 1 ∧ x % q + q = x ∧ q ≤ x) := by
  have hm := Nat.mod_add_div x q
  rcases div_cases_two hx with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h] at hm
    exact Or.inl ⟨h, by omega, h'⟩
  · rw [h] at hm
    exact Or.inr ⟨h, by omega, h'⟩

/-! ### Lemma 4.2, first part -/

/-- **Lemma 4.2, `e_q ∈ {0,1}` and `m_q + e_q ≤ 1`**, for all residues `1 ≤ a, b < q`
(and every `s`). -/
theorem levelE_mem {q a b s : ℕ} (ha : 1 ≤ a) (haq : a < q) (hb : 1 ≤ b) (hbq : b < q) :
    (levelE q a b s = 0 ∨ levelE q a b s = 1) ∧ (levelM q a b s : ℤ) + levelE q a b s ≤ 1 := by
  have hcd := div_mod_cases_two (x := a + b) (q := q) (by omega)
  have hEa := carryInd_cases q s a
  have hEb := carryInd_cases q s b
  have hEc := carryInd_cases q s ((a + b) % q)
  have hM := levelM_cases q a b s
  have hEta := levelEta_cases q a b
  have hB := levelBStar_cases q a b
  rw [levelE_eq]
  omega

/-! ### The level contributions -/

section Levels

variable {q a b : ℕ}

/-- The level-`q` contribution to `v_p(C_n)`:
`⌊(n+a)/q⌋ - ⌊a/q⌋ + ⌊(n+b)/q⌋ - ⌊b/q⌋ - ⌊n/q⌋ - (⌊(n+a+b)/q⌋ - ⌊(1+a+b)/q⌋)
  = η_q + E_a + E_b - E_c`. -/
theorem level_constant_eq (hq : 0 < q) (haq : a < q) (hbq : b < q) (n : ℕ) :
    (((n + a) / q : ℕ) : ℤ) - ((0 + a) / q : ℕ) + ((n + b) / q : ℕ) - ((0 + b) / q : ℕ) -
        (n / q : ℕ) - ((((n + (a + b)) / q : ℕ) : ℤ) - ((1 + (a + b)) / q : ℕ)) =
      (levelEta q a b : ℤ) + carryInd q (n % q) a + carryInd q (n % q) b -
        carryInd q (n % q) ((a + b) % q) := by
  have e1 := add_div_eq_div_add (n := n) (x := a) hq
  have e2 := add_div_eq_div_add (n := n) (x := b) hq
  have e3 := add_div_eq_div_add (n := n) (x := a + b) hq
  have hs := Nat.mod_lt n hq
  have z1 : (0 + a) / q = 0 := by rw [zero_add]; exact Nat.div_eq_of_lt haq
  have z2 : (0 + b) / q = 0 := by rw [zero_add]; exact Nat.div_eq_of_lt hbq
  rw [e1, e2, e3, z1, z2]
  have f1 := div_cases_two (x := n % q + a) (q := q) (by omega)
  have f2 := div_cases_two (x := n % q + b) (q := q) (by omega)
  have f3 := div_cases_four (x := n % q + (a + b)) (q := q) (by omega)
  have f4 := div_cases_two (x := 1 + (a + b)) (q := q) (by omega)
  have hcd := div_mod_cases_two (x := a + b) (q := q) (by omega)
  have hEa := carryInd_cases q (n % q) a
  have hEb := carryInd_cases q (n % q) b
  have hEc := carryInd_cases q (n % q) ((a + b) % q)
  have hEta := levelEta_cases q a b
  omega

/-- The level-`q` contribution to `v_p(μ_j)` is at least `-b*_q`:
`⌊(j+a)/q⌋ - ⌊a/q⌋ - (⌊(j+1+a+b)/q⌋ - ⌊(1+a+b)/q⌋) ≥ -b*_q`. -/
theorem level_moment_ge (hq : 0 < q) (haq : a < q) (hbq : b < q) (j : ℕ) :
    -(levelBStar q a b : ℤ) ≤ (((j + a) / q : ℕ) : ℤ) - ((0 + a) / q : ℕ) -
      ((((1 + j) + (a + b)) / q : ℕ) - ((1 + (a + b)) / q : ℕ)) := by
  have e1 := add_div_eq_div_add (n := j) (x := a) hq
  have e2 : (1 + j + (a + b)) / q = j / q + (j % q + (1 + (a + b))) / q := by
    rw [show 1 + j + (a + b) = j + (1 + (a + b)) by ring]
    exact add_div_eq_div_add hq
  have hu := Nat.mod_lt j hq
  have z1 : (0 + a) / q = 0 := by rw [zero_add]; exact Nat.div_eq_of_lt haq
  rw [e1, e2, z1]
  have f1 := div_cases_two (x := j % q + a) (q := q) (by omega)
  have f2 := div_cases_four (x := j % q + (1 + (a + b))) (q := q) (by omega)
  have f3 := div_cases_two (x := 1 + (a + b)) (q := q) (by omega)
  have hcd := div_mod_cases_two (x := a + b) (q := q) (by omega)
  have hB := levelBStar_cases q a b
  omega

/-- The level-`q` contribution to `v_p([t^j] y_n)`, in normal form. -/
theorem level_coeff_normal (hq : 0 < q) {n j : ℕ} (hj : j ≤ n) :
    ((((n + a) / q : ℕ) : ℤ) - ((j + a) / q : ℕ)) +
        ((((j + (n + a + b)) / q : ℕ) : ℤ) - ((0 + (n + a + b)) / q : ℕ)) -
        ((n - j) / q : ℕ) - (j / q : ℕ) =
      (((n % q + a) / q : ℕ) : ℤ) - ((j % q + a) / q : ℕ) +
        ((n % q + (j % q + a + b)) / q : ℕ) - ((n % q + (a + b)) / q : ℕ) +
        (if n % q < j % q then 1 else 0) := by
  have e1 := add_div_eq_div_add (n := n) (x := a) hq
  have e2 := add_div_eq_div_add (n := j) (x := a) hq
  have e3 : (j + (n + a + b)) / q = j / q + n / q + (n % q + (j % q + a + b)) / q := by
    rw [add_div_eq_div_add (n := j) (x := n + a + b) hq,
      show j % q + (n + a + b) = n + (j % q + a + b) by ring,
      add_div_eq_div_add (n := n) (x := j % q + a + b) hq]
    ring
  have e4 : (0 + (n + a + b)) / q = n / q + (n % q + (a + b)) / q := by
    rw [zero_add, add_assoc]
    exact add_div_eq_div_add hq
  have e5 := sub_div_add_div hq hj
  rw [e1, e2, e3, e4]
  split_ifs at e5 ⊢ <;> omega

/-- **Content levels**: the level-`q` contribution to `v_p([t^j] y_n)`, `j ≤ n`, is at least
`m_q` (in particular nonnegative). -/
theorem level_coeff_ge (hq : 0 < q) (haq : a < q) (hbq : b < q) {n j : ℕ} (hj : j ≤ n) :
    (levelM q a b (n % q) : ℤ) ≤ ((((n + a) / q : ℕ) : ℤ) - ((j + a) / q : ℕ)) +
        ((((j + (n + a + b)) / q : ℕ) : ℤ) - ((0 + (n + a + b)) / q : ℕ)) -
        ((n - j) / q : ℕ) - (j / q : ℕ) := by
  rw [level_coeff_normal hq hj]
  have hs := Nat.mod_lt n hq
  have hu := Nat.mod_lt j hq
  have f1 := div_cases_two (x := n % q + a) (q := q) (by omega)
  have f2 := div_cases_two (x := j % q + a) (q := q) (by omega)
  have f3 := div_cases_four (x := n % q + (j % q + a + b)) (q := q) (by omega)
  have f4 := div_cases_four (x := n % q + (a + b)) (q := q) (by omega)
  have hcd := div_mod_cases_two (x := a + b) (q := q) (by omega)
  have hEc := carryInd_cases q (n % q) ((a + b) % q)
  have hM := levelM_cases q a b (n % q)
  split_ifs <;> omega

/-- **The single-level content**: some `j ≤ n` has level-`q` contribution at most `m_q`. -/
theorem level_coeff_attained (hq : 0 < q) (ha : 1 ≤ a) (haq : a < q) (hbq : b < q) (n : ℕ) :
    ∃ j ≤ n, ((((n + a) / q : ℕ) : ℤ) - ((j + a) / q : ℕ)) +
        ((((j + (n + a + b)) / q : ℕ) : ℤ) - ((0 + (n + a + b)) / q : ℕ)) -
        ((n - j) / q : ℕ) - (j / q : ℕ) ≤ levelM q a b (n % q) := by
  have hs := Nat.mod_lt n hq
  have hsn := Nat.mod_le n q
  have hM := levelM_cases q a b (n % q)
  have hcd := div_mod_cases_two (x := a + b) (q := q) (by omega)
  have hEc := carryInd_cases q (n % q) ((a + b) % q)
  rcases hM with ⟨hm, hsa, hsb, hd⟩ | ⟨hm, hm'⟩
  · -- `m_q = 1`: take `j = n`
    refine ⟨n, le_rfl, ?_⟩
    rw [level_coeff_normal hq le_rfl, hm]
    have f3 := div_cases_four (x := n % q + (n % q + a + b)) (q := q) (by omega)
    have f4 := div_cases_four (x := n % q + (a + b)) (q := q) (by omega)
    split_ifs <;> omega
  · by_cases hEa : n % q + a < q
    · -- `E_a = 0`: take `j = 0`
      refine ⟨0, Nat.zero_le n, ?_⟩
      rw [level_coeff_normal hq (Nat.zero_le n), hm]
      have h0 : (0 : ℕ) % q = 0 := Nat.zero_mod q
      rw [h0]
      have f1 := div_cases_two (x := n % q + a) (q := q) (by omega)
      have f2 := div_cases_two (x := 0 + a) (q := q) (by omega)
      have f3 := div_cases_four (x := n % q + (0 + a + b)) (q := q) (by omega)
      have f4 := div_cases_four (x := n % q + (a + b)) (q := q) (by omega)
      split_ifs <;> omega
    · -- `E_a = 1`: take `j = q - a`
      refine ⟨q - a, by omega, ?_⟩
      rw [level_coeff_normal hq (by omega), hm]
      have h0 : (q - a) % q = q - a := Nat.mod_eq_of_lt (by omega)
      rw [h0]
      have f1 := div_cases_two (x := n % q + a) (q := q) (by omega)
      have f2 := div_cases_two (x := q - a + a) (q := q) (by omega)
      have f3 := div_cases_four (x := n % q + (q - a + a + b)) (q := q) (by omega)
      have f4 := div_cases_four (x := n % q + (a + b)) (q := q) (by omega)
      split_ifs <;> omega

end Levels

end ArithmeticOfJacobiPolynomials
