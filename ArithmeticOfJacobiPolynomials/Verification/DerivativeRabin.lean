module

public import ArithmeticOfJacobiPolynomials.Verification.ModularArithmetic
public import ArithmeticOfJacobiPolynomials.Verification.QuotientFrobenius

/-! # A finite Frobenius certificate
The trace records `X, X^p, ..., X^(p^d)` in the quotient. At index `d / q`,
a second polynomial witnesses the inverse required by Rabin's criterion.
-/

public section
namespace ArithmeticOfJacobiPolynomials.ModularArithmetic

open Polynomial

/-- Check an addition chain in the quotient without expanding a large power. -/
theorem value_chain {p : ℕ} {R : Type*} [CommRing R] (φ : ZMod p →+* R) (x : R)
    (f : List ℕ) (hx : x ^ f.length = value φ x f)
    (v : ℕ → List ℕ) (e : ℕ → ℕ) (op : ℕ → ℕ × ℕ) (N : ℕ)
    (h0 : value φ x (v 0) = x) (he : e 0 = 1)
    (steps : ∀ i : Fin N, let j := (op i.val).1; let k := (op i.val).2
      j ≤ i.val ∧ k ≤ i.val ∧ (v k).length = f.length ∧ e (i.val + 1) = e j + e k ∧
        v (i.val + 1) = mul p f (v j) (v k)) :
    value φ x (v N) = x ^ e N := by
  suffices go : ∀ i, i ≤ N → value φ x (v i) = x ^ e i by exact go N le_rfl
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    cases i with
    | zero => simpa [he] using h0
    | succ n =>
      obtain ⟨hj, hk, hl, ha, hm⟩ := steps ⟨n, hi⟩
      rw [hm, value_mul φ x _ _ _ hx hl,
        ih _ (Nat.lt_succ_of_le hj) (by omega), ih _ (Nat.lt_succ_of_le hk) (by omega), ha, pow_add]

theorem irreducible_of_trace {p : ℕ} [Fact p.Prime] (h : (ZMod p)[X])
    (f : List ℕ) (hd : 0 < f.length) (hdeg : h.natDegree = f.length)
    (hx : (AdjoinRoot.root h) ^ f.length = value (AdjoinRoot.of h) (AdjoinRoot.root h) f)
    (row inv : ℕ → List ℕ)
    (h0 : row 0 = shift p f (unitVec f))
    (hEvery : ∀ i : Fin (f.length + 1), (row i.val).length = f.length)
    (hstep : ∀ i : Fin f.length,
      value (AdjoinRoot.of h) (AdjoinRoot.root h) (row (i.val + 1)) =
        value (AdjoinRoot.of h) (AdjoinRoot.root h) (row i.val) ^ p)
    (hclose : row f.length = row 0)
    (htests : ∀ q : Fin (f.length + 1), q.val.Prime → q.val ∣ f.length →
      mul p f (inv q.val) (row (f.length / q.val)) =
        addMul p 1 (unitVec f) (mul p f (inv q.val) (row 0))) :
    Irreducible h := by
  let φ := AdjoinRoot.of h
  let x := AdjoinRoot.root h
  have first : value φ x (row 0) = x := by
    rw [h0, value_shift φ x f _ hx (length_unitVec f hd), value_unitVec, mul_one]
  have iter (i : ℕ) (hi : i ≤ f.length) : value φ x (row i) = x ^ p ^ i := by
    induction i with
    | zero => simpa using first
    | succ i ih =>
      rw [hstep ⟨i, hi⟩, ih (by omega), ← pow_mul, pow_succ]
  apply irreducible_of_quotient_frobenius (hdeg ▸ hd)
  · rw [hdeg]
    exact (iter f.length (le_refl _)).symm.trans ((congrArg (value φ x) hclose).trans first)
  · intro q hq hqdiv
    rw [hdeg] at hqdiv ⊢
    have hqlt := Nat.le_of_dvd hd hqdiv
    have hlen := hEvery ⟨f.length / q, Nat.lt_succ_of_le (Nat.div_le_self _ _)⟩
    have h0len := hEvery ⟨0, by omega⟩
    have hcert := congrArg (value φ x) (htests ⟨q, by omega⟩ hq hqdiv)
    rw [value_mul φ x f _ _ hx hlen,
      value_addMul φ x 1 ((length_unitVec f hd).trans (length_mul f _ _ h0len).symm),
      value_mul φ x f _ _ hx h0len, value_unitVec, first, iter _ (Nat.div_le_self _ _)] at hcert
    simp only [Nat.cast_one, map_one, one_mul] at hcert
    refine ⟨value φ x (inv q), ?_⟩
    change value φ x (inv q) * (x ^ p ^ (f.length / q) - x) = 1
    rw [mul_sub, hcert, add_sub_cancel_right]

end ArithmeticOfJacobiPolynomials.ModularArithmetic
