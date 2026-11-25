/- Assembled by AxiomProver. -/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

/-!
# Valuations of products by levels

For a prime `p` the valuation of a product of positive integers is counted level by level:
`v_p(∏ f_k) = ∑_{h ≥ 1} #{k : p^h ∣ f_k}` (`padicValRat_prod_eq_sum_card`). For an
arithmetic progression `d k + r` with `d` prime to `q = p^h`, the multiples of `q` among
`k ∈ (A, B]` are counted by `(B + a)/q - (A + a)/q`, where `a` is the least residue of
`r/d` modulo `q` (`card_Ioc_filter_dvd_affine`). These are the level indicators of the proof
of Lemma 4.2 of the manuscript.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

section Levels

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(N) = #{1 ≤ h ≤ H : p^h ∣ N}` for `0 < N < p^{H+1}`. -/
theorem card_filter_pow_dvd_eq_padicValNat {N : ℕ} (hN : N ≠ 0) {H : ℕ}
    (hNH : N < p ^ (H + 1)) : #{h ∈ Icc 1 H | p ^ h ∣ N} = padicValNat p N := by
  have hv : padicValNat p N ≤ H := by
    by_contra hcon
    have h1 : p ^ (H + 1) ≤ p ^ padicValNat p N := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2 : p ^ padicValNat p N ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) pow_padicValNat_dvd
    omega
  have e : ({h ∈ Icc 1 H | p ^ h ∣ N} : Finset ℕ) = Icc 1 (padicValNat p N) := by
    ext h
    simp only [mem_filter, mem_Icc, padicValNat_dvd_iff_le hN]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
  rw [e, Nat.card_Icc]
  omega

/-- `v_p(x) = #{1 ≤ h ≤ H : p^h ∣ x}` for an integer `0 < x < p^{H+1}`. -/
theorem padicValRat_intCast_eq_card {x : ℤ} (hx : 0 < x) {H : ℕ}
    (hxH : x < (p : ℤ) ^ (H + 1)) :
    padicValRat p (x : ℚ) = (#{h ∈ Icc 1 H | (p : ℤ) ^ h ∣ x} : ℤ) := by
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hx.le
  have hN : N ≠ 0 := by omega
  have hNH : N < p ^ (H + 1) := by exact_mod_cast hxH
  have e : ({h ∈ Icc 1 H | (p : ℤ) ^ h ∣ (N : ℤ)} : Finset ℕ) = {h ∈ Icc 1 H | p ^ h ∣ N} := by
    ext h
    simp only [mem_filter]
    norm_cast
  rw [Int.cast_natCast, padicValRat.of_nat, e, card_filter_pow_dvd_eq_padicValNat hN hNH]

/-- **Level counting.** For positive integers `f_k < p^{H+1}`,
`v_p(∏_k f_k) = ∑_{h=1}^{H} #{k : p^h ∣ f_k}`. -/
theorem padicValRat_prod_eq_sum_card {ι : Type*} (S : Finset ι) (f : ι → ℤ) {H : ℕ}
    (hpos : ∀ k ∈ S, 0 < f k) (hlt : ∀ k ∈ S, f k < (p : ℤ) ^ (H + 1)) :
    padicValRat p (∏ k ∈ S, (f k : ℚ)) =
      ∑ h ∈ Icc 1 H, (#{k ∈ S | (p : ℤ) ^ h ∣ f k} : ℤ) := by
  classical
  have hval : padicValRat p (∏ k ∈ S, (f k : ℚ)) = ∑ k ∈ S, padicValRat p (f k : ℚ) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      have hk0 : (f k : ℚ) ≠ 0 := by exact_mod_cast (hpos k (mem_insert_self k S)).ne'
      have hS0 : ∏ i ∈ S, (f i : ℚ) ≠ 0 := prod_ne_zero_iff.mpr fun i hi => by
        exact_mod_cast (hpos i (mem_insert_of_mem hi)).ne'
      rw [prod_insert hk, sum_insert hk, padicValRat.mul hk0 hS0,
        ih (fun i hi => hpos i (mem_insert_of_mem hi)) (fun i hi => hlt i (mem_insert_of_mem hi))]
  rw [hval, sum_congr rfl fun k hk => padicValRat_intCast_eq_card (hpos k hk) (hlt k hk)]
  simp only [Finset.natCast_card_filter]
  exact sum_comm

end Levels

/-! ### Counting multiples in an interval -/

/-- `#{k ∈ (A, B] : q ∣ k + t} = (B + t)/q - (A + t)/q`. -/
theorem card_Ioc_filter_dvd_add (q t : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    #{k ∈ Ioc A B | q ∣ k + t} = (B + t) / q - (A + t) / q := by
  have e : #{k ∈ Ioc A B | q ∣ k + t} = #{m ∈ Ioc (A + t) (B + t) | q ∣ m} := by
    apply Finset.card_nbij' (· + t) (· - t)
    · intro k hk
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hk ⊢
      exact ⟨⟨by omega, by omega⟩, hk.2⟩
    · intro m hm
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hm ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.sub_add_cancel (by omega)]
      exact hm.2
    · intro k _
      change k + t - t = k
      omega
    · intro m hm
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hm
      change m - t + t = m
      omega
  rw [e]
  have hU := Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le (A + t)) (show A + t ≤ B + t by omega)
  have hD : Disjoint (Ioc 0 (A + t)) (Ioc (A + t) (B + t)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (B + t) q
  have h2 := Nat.Ioc_filter_dvd_card_eq_div (A + t) q
  rw [← hU, filter_union,
    Finset.card_union_eq_card_add_card.mpr (disjoint_filter_filter hD)] at h1
  omega

/-- If `d a ≡ r (mod q)` with `d` prime to `q`, then `q ∣ d k + r ↔ q ∣ k + a`. -/
theorem intCast_dvd_affine_iff {q d : ℕ} (hcop : Nat.Coprime q d) {r : ℤ} {a : ℕ}
    (ha : (q : ℤ) ∣ (d : ℤ) * (a : ℤ) - r) (k : ℕ) :
    (q : ℤ) ∣ (d : ℤ) * (k : ℤ) + r ↔ q ∣ k + a := by
  have e : (d : ℤ) * k + r = d * ((k + a : ℕ) : ℤ) - (d * a - r) := by push_cast; ring
  rw [e, dvd_sub_left ha]
  constructor
  · intro h
    have hc : IsCoprime (q : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    exact Int.natCast_dvd_natCast.mp (hc.dvd_of_dvd_mul_left h)
  · intro h
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h) _

/-- The multiples of `q` in the progression `d k + r`, `k ∈ (A, B]`, where `d a ≡ r (mod q)` and
`d` is prime to `q`: there are `(B + a)/q - (A + a)/q` of them. -/
theorem card_Ioc_filter_dvd_affine {q d : ℕ} (hcop : Nat.Coprime q d) {r : ℤ} {a : ℕ}
    (ha : (q : ℤ) ∣ (d : ℤ) * (a : ℤ) - r) {A B : ℕ} (hAB : A ≤ B) :
    #((Ioc A B : Finset ℕ).filter fun k : ℕ => (q : ℤ) ∣ (d : ℤ) * (k : ℤ) + r) =
      (B + a) / q - (A + a) / q := by
  have e : ((Ioc A B : Finset ℕ).filter fun k : ℕ => (q : ℤ) ∣ (d : ℤ) * (k : ℤ) + r) =
      {k ∈ Ioc A B | q ∣ k + a} := by
    ext k
    simp only [mem_filter, intCast_dvd_affine_iff hcop ha k]
  rw [e, card_Ioc_filter_dvd_add q a hAB]

/-! ### Least residues of `r/d` modulo `q` -/

/-- The least nonnegative residue of `r/d` modulo `q` (for `d` prime to `q`). -/
noncomputable def affineResidue (r : ℤ) (d q : ℕ) : ℕ := ((r : ZMod q) * ((d : ℕ) : ZMod q)⁻¹).val

theorem affineResidue_eq (r : ℤ) (d q : ℕ) :
    affineResidue r d q = ((r : ZMod q) * ((d : ℕ) : ZMod q)⁻¹).val := (rfl)

theorem affineResidue_lt (r : ℤ) (d : ℕ) {q : ℕ} (hq : 0 < q) : affineResidue r d q < q := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [affineResidue_eq]
  exact ZMod.val_lt _

theorem dvd_mul_affineResidue_sub (r : ℤ) {d q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime d q) :
    (q : ℤ) ∣ d * affineResidue r d q - r := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h3 : ((d : ℕ) : ZMod q) * ((d : ℕ) : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one d hcop
  push_cast
  rw [affineResidue_eq, ZMod.natCast_zmod_val]
  linear_combination (r : ZMod q) * h3

/-- For `r = ±1` and `q > 1` the residue is nonzero. -/
theorem one_le_affineResidue {r : ℤ} (hr : r = 1 ∨ r = -1) {d q : ℕ} (hq : 1 < q)
    (hcop : Nat.Coprime d q) : 1 ≤ affineResidue r d q := by
  by_contra h0
  have h0' : affineResidue r d q = 0 := by omega
  have h := dvd_mul_affineResidue_sub r (by omega : 0 < q) hcop
  rw [h0'] at h
  simp only [Nat.cast_zero, mul_zero, zero_sub, dvd_neg] at h
  have h1 : (q : ℤ) ∣ 1 := by
    rcases hr with rfl | rfl
    · exact h
    · exact (dvd_neg).mp h
  have : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  omega

/-! ### Small quotients -/

theorem div_eq_ind_of_lt_two_mul {x q : ℕ} (hx : x < 2 * q) :
    x / q = if q ≤ x then 1 else 0 := by
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- The three possible values of `x / q` for `x < 3q`, with the corresponding bounds. -/
theorem div_cases_of_lt_three_mul {x q : ℕ} (hx : x < 3 * q) :
    (x / q = 0 ∧ x < q) ∨ (x / q = 1 ∧ q ≤ x ∧ x < 2 * q) ∨ (x / q = 2 ∧ 2 * q ≤ x) := by
  rcases lt_or_ge x q with h1 | h1
  · exact Or.inl ⟨Nat.div_eq_of_lt h1, h1⟩
  rcases lt_or_ge x (2 * q) with h2 | h2
  · exact Or.inr (Or.inl ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h1, h2⟩)
  · exact Or.inr (Or.inr ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h2⟩)

/-- `(n + x)/q = n/q + (n % q + x)/q`. -/
theorem add_div_eq_div_add {n x q : ℕ} (hq : 0 < q) :
    (n + x) / q = n / q + (n % q + x) / q := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [show n % q + q * (n / q) + x = (n % q + x) + q * (n / q) by ring,
    Nat.add_mul_div_left _ _ hq]
  ring

/-- The borrow in `(n - j)/q`: `(n-j)/q + j/q + [n % q < j % q] = n/q` for `j ≤ n`. -/
theorem sub_div_add_div {n j q : ℕ} (hq : 0 < q) (hj : j ≤ n) :
    (n - j) / q + j / q + (if n % q < j % q then 1 else 0) = n / q := by
  have h := Nat.add_div (a := n - j) (b := j) hq
  rw [Nat.sub_add_cancel hj] at h
  have hm := Nat.add_mod (n - j) j q
  rw [Nat.sub_add_cancel hj] at hm
  have hw := Nat.mod_lt (n - j) hq
  have hu := Nat.mod_lt j hq
  have hs := Nat.mod_lt n hq
  have hx := div_eq_ind_of_lt_two_mul (show (n - j) % q + j % q < 2 * q by omega)
  have hxm := Nat.mod_add_div ((n - j) % q + j % q) q
  rw [← hm] at hxm
  rw [h]
  split_ifs at hx with h1 <;> rw [hx] at hxm <;> split_ifs <;> omega

/-! ### Products of progressions and factorials -/

section Products

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p` of a product of nonzero integers is the sum of the valuations. -/
theorem padicValRat_prod_intCast {ι : Type*} (S : Finset ι) (f : ι → ℤ)
    (hne : ∀ k ∈ S, f k ≠ 0) :
    padicValRat p (∏ k ∈ S, (f k : ℚ)) = ∑ k ∈ S, padicValRat p (f k : ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have hk0 : (f k : ℚ) ≠ 0 := by exact_mod_cast hne k (mem_insert_self k S)
    have hS0 : ∏ i ∈ S, (f i : ℚ) ≠ 0 := prod_ne_zero_iff.mpr fun i hi => by
      exact_mod_cast hne i (mem_insert_of_mem hi)
    rw [prod_insert hk, sum_insert hk, padicValRat.mul hk0 hS0,
      ih (fun i hi => hne i (mem_insert_of_mem hi))]

/-- A product of nonzero integers prime to `p` has valuation `0`. -/
theorem padicValRat_prod_eq_zero_of_not_dvd {ι : Type*} (S : Finset ι) (f : ι → ℤ)
    (hne : ∀ k ∈ S, f k ≠ 0) (hnd : ∀ k ∈ S, ¬ (p : ℤ) ∣ f k) :
    padicValRat p (∏ k ∈ S, (f k : ℚ)) = 0 := by
  rw [padicValRat_prod_intCast S f hne]
  refine sum_eq_zero fun k hk => ?_
  simp [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (hnd k hk)]

/-- `m! = ∏_{k ∈ (0, m]} k` in `ℚ`. -/
theorem factorial_eq_prod_Ioc (m : ℕ) :
    (m.factorial : ℚ) = ∏ k ∈ Ioc 0 m, ((k : ℤ) : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Ioc_succ_top (Nat.zero_le m), ← ih, Nat.factorial_succ]
    push_cast
    ring

/-- **Legendre's formula by levels.** For `m < p^{H+1}`, `v_p(m!) = ∑_{h=1}^{H} ⌊m/p^h⌋`. -/
theorem padicValRat_factorial_eq_sum {m H : ℕ} (hm : m < p ^ (H + 1)) :
    padicValRat p (m.factorial : ℚ) = ∑ h ∈ Icc 1 H, ((m / p ^ h : ℕ) : ℤ) := by
  rw [factorial_eq_prod_Ioc, padicValRat_prod_eq_sum_card (Ioc 0 m) (fun k : ℕ => (k : ℤ))
    (fun k hk => by have := (mem_Ioc.mp hk).1; omega)
    (fun k hk => by
      have := (mem_Ioc.mp hk).2
      exact_mod_cast (show k < p ^ (H + 1) by omega))]
  refine sum_congr rfl fun h _ => ?_
  have e : ((Ioc 0 m).filter fun k : ℕ => (p : ℤ) ^ h ∣ (k : ℤ)) =
      (Ioc 0 m).filter fun k : ℕ => p ^ h ∣ k := by
    ext k
    simp only [mem_filter]
    norm_cast
  rw [e, Nat.Ioc_filter_dvd_card_eq_div]

/-- **Progressions by levels.** If `p ∤ d` and the integers `d k + r`, `k ∈ (A, B]`, lie in
`(0, p^{H+1})`, then `v_p(∏_k (d k + r)) = ∑_{h=1}^{H} (⌊(B + a_h)/p^h⌋ - ⌊(A + a_h)/p^h⌋)`,
where `a_h` is the least residue of `r/d` modulo `p^h`. -/
theorem padicValRat_prod_affine_eq_sum {d : ℕ} (hd : ¬ p ∣ d) (r : ℤ) {A B : ℕ} (hAB : A ≤ B)
    (hpos : ∀ k ∈ Ioc A B, 0 < (d : ℤ) * (k : ℤ) + r) {H : ℕ}
    (hlt : ∀ k ∈ Ioc A B, (d : ℤ) * (k : ℤ) + r < (p : ℤ) ^ (H + 1)) :
    padicValRat p (∏ k ∈ Ioc A B, (((d : ℤ) * (k : ℤ) + r : ℤ) : ℚ)) =
      ∑ h ∈ Icc 1 H, (((B + affineResidue r d (p ^ h)) / p ^ h -
        (A + affineResidue r d (p ^ h)) / p ^ h : ℕ) : ℤ) := by
  rw [padicValRat_prod_eq_sum_card (Ioc A B) (fun k : ℕ => (d : ℤ) * (k : ℤ) + r) hpos hlt]
  refine sum_congr rfl fun h _ => ?_
  have hq : 0 < p ^ h := pow_pos hp.out.pos h
  have hcop : Nat.Coprime d (p ^ h) :=
    Nat.Coprime.pow_right h (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd))
  have key := card_Ioc_filter_dvd_affine (q := p ^ h) (Nat.coprime_comm.mp hcop)
    (dvd_mul_affineResidue_sub r hq hcop) hAB
  rw [← Nat.cast_pow, key]

/-- **Factorials divide products of progressions.** If `p ∤ d` and `d k + r > 0` for
`k ∈ (A, B]`, then `v_p((B - A)!) ≤ v_p(∏_{k ∈ (A, B]} (d k + r))`. -/
theorem padicValRat_factorial_le_prod_affine {d : ℕ} (hd : ¬ p ∣ d) (r : ℤ) {A B : ℕ}
    (hAB : A ≤ B) (hpos : ∀ k ∈ Ioc A B, 0 < (d : ℤ) * (k : ℤ) + r) :
    padicValRat p ((B - A).factorial : ℚ) ≤
      padicValRat p (∏ k ∈ Ioc A B, (((d : ℤ) * (k : ℤ) + r : ℤ) : ℚ)) := by
  set H := ((d : ℤ) * (B : ℤ) + r).toNat + B with hH
  have hbig : ∀ x : ℕ, x ≤ H → x < p ^ (H + 1) := fun x hx =>
    lt_of_le_of_lt hx (lt_trans (Nat.lt_succ_self H) (Nat.lt_pow_self hp.out.one_lt))
  have hlt : ∀ k ∈ Ioc A B, (d : ℤ) * (k : ℤ) + r < (p : ℤ) ^ (H + 1) := by
    intro k hk
    have hkB : (k : ℤ) ≤ B := by exact_mod_cast (mem_Ioc.mp hk).2
    have h1 : (d : ℤ) * k ≤ d * B := mul_le_mul_of_nonneg_left hkB (Int.natCast_nonneg d)
    have h2 := Int.self_le_toNat ((d : ℤ) * (B : ℤ) + r)
    have h3 : ((((d : ℤ) * (B : ℤ) + r).toNat : ℕ) : ℤ) < (p : ℤ) ^ (H + 1) := by
      exact_mod_cast hbig _ (by omega)
    omega
  rw [padicValRat_factorial_eq_sum (hbig (B - A) (by omega)),
    padicValRat_prod_affine_eq_sum hd r hAB hpos hlt]
  refine sum_le_sum fun h _ => ?_
  have := Nat.div_add_div_le_add_div (x := B - A) (y := A + affineResidue r d (p ^ h)) (z := p ^ h)
  rw [show B - A + (A + affineResidue r d (p ^ h)) = B + affineResidue r d (p ^ h) by omega]
    at this
  exact_mod_cast (show (B - A) / p ^ h ≤ (B + affineResidue r d (p ^ h)) / p ^ h -
    (A + affineResidue r d (p ^ h)) / p ^ h by omega)

end Products

end ArithmeticOfJacobiPolynomials
