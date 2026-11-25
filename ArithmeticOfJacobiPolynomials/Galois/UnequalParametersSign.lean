/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# An odd discriminant valuation gives an odd permutation (end of the proof of Lemma 5.16)

If every element of `Gal(f/F)` acts on the roots of `f` by an even permutation, the Vandermonde
product `δ = ∏_{i<j} (x_j - x_i)` of an enumeration of the roots is fixed by the Galois group,
hence lies in `F` (`exists_eq_vandermonde_of_forall_sign_eq_one`). By the Jacobi discriminant
formula (5.31) the discriminant `lc^{2n-2} δ²` of `P_n^{(a,b)}` is `jacobiDiscriminant a b n`, so
its `p`-adic valuation is even; hence an odd valuation forces an odd permutation in the Galois
group (`exists_sign_galPerm_eq_neg_one`).

`padicValRat_jacobiDiscriminant` computes the valuation for the primes of Lemma 5.16:
the multiples of `p` among the bases `h`, `h + a`, `h + b`, `n + h + a + b` occur exactly at
`h = p`, `p - a`, `p - b`, `2p - n - a - b`, and
`v_p = (p - 2n + 2) + (p - a - 1) + (p - b - 1) + (2n + a + b - 2p) = p`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

namespace UnequalParameters

section Vandermonde

variable {F : Type*} [Field F]

open Classical in
/-- If every element of `Gal(f/F)` acts by an even permutation on the roots, the Vandermonde
product of an enumeration of the roots lies in `F`. -/
theorem exists_eq_vandermonde_of_forall_sign_eq_one {f : F[X]} (hsep : f.Separable) {n : ℕ}
    (e : Fin n ≃ f.rootSet f.SplittingField)
    (heven : ∀ σ : f.Gal, Equiv.Perm.sign (galPerm f σ) = 1) :
    ∃ q : F, algebraMap F f.SplittingField q =
      ∏ i, ∏ j ∈ Finset.Ioi i, ((e j : f.SplittingField) - e i) := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field hsep
  have hfix : ∀ σ : Gal(f.SplittingField/F),
      σ (∏ i, ∏ j ∈ Finset.Ioi i, ((e j : f.SplittingField) - e i)) =
        ∏ i, ∏ j ∈ Finset.Ioi i, ((e j : f.SplittingField) - e i) := by
    intro σ
    have hπ : ∀ i, ((e ((e.symm.permCongr (galPerm f σ)) i) : f.SplittingField)) =
        σ (e i : f.SplittingField) := by
      intro i
      rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      rfl
    have hsign : Equiv.Perm.sign (e.symm.permCongr (galPerm f σ)) = 1 := by
      rw [Equiv.Perm.sign_permCongr]; exact heven σ
    have h1 : σ (∏ i, ∏ j ∈ Finset.Ioi i, ((e j : f.SplittingField) - e i)) =
        ∏ i, ∏ j ∈ Finset.Ioi i, (((e ((e.symm.permCongr (galPerm f σ)) j)) : f.SplittingField) -
          e ((e.symm.permCongr (galPerm f σ)) i)) := by
      simp only [map_prod, map_sub, hπ]
    have h3 : Matrix.vandermonde (fun i => ((e ((e.symm.permCongr (galPerm f σ)) i)) :
          f.SplittingField)) =
        (Matrix.vandermonde (fun i => (e i : f.SplittingField))).submatrix
          (e.symm.permCongr (galPerm f σ)) id := by
      ext i j
      simp [Matrix.vandermonde_apply]
    rw [h1, ← Matrix.det_vandermonde, h3, Matrix.det_permute, hsign, Matrix.det_vandermonde]
    simp
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (∏ i, ∏ j ∈ Finset.Ioi i, ((e j : f.SplittingField) - e i))).mpr hfix
  exact ⟨q, hq⟩

end Vandermonde

open Classical in
/-- **An odd discriminant valuation gives an odd permutation.** Conditional on the Jacobi
discriminant formula (5.31) ([Szego, Theorem 6.71], [DLMF, (18.16.19)]), taken as the
hypothesis `hdisc`: if `P_n^{(a,b)}` is separable of degree `n` and `v_p` of its discriminant is
odd, then `Gal(P_n^{(a,b)}/ℚ)` contains an odd permutation of the roots. -/
theorem exists_sign_galPerm_eq_neg_one (hdisc : JacobiDiscriminantFormula) (a b n : ℕ)
    (hsep : (jacobiP a b n).Separable) (hdeg : (jacobiP a b n).natDegree = n)
    {p : ℕ} [Fact p.Prime] (hodd : Odd (padicValRat p (jacobiDiscriminant a b n))) :
    ∃ σ : (jacobiP a b n).Gal, Equiv.Perm.sign (galPerm (jacobiP a b n) σ) = -1 := by
  by_contra hcon
  push Not at hcon
  have heven : ∀ σ, Equiv.Perm.sign (galPerm (jacobiP a b n) σ) = 1 := fun σ =>
    (Int.units_eq_one_or _).resolve_right (hcon σ)
  have hcard : Fintype.card ((jacobiP a b n).rootSet (jacobiP a b n).SplittingField) = n := by
    rw [card_rootSet_eq_natDegree hsep (SplittingField.splits _), hdeg]
  obtain ⟨e⟩ : Nonempty (Fin n ≃ (jacobiP a b n).rootSet (jacobiP a b n).SplittingField) :=
    ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  obtain ⟨q, hq⟩ := exists_eq_vandermonde_of_forall_sign_eq_one hsep e heven
  -- the factorization over the splitting field
  have hroots : ((jacobiP a b n).map (algebraMap ℚ (jacobiP a b n).SplittingField)).roots =
      Finset.univ.val.map (fun i => (e i : (jacobiP a b n).SplittingField)) := by
    have hnd : (Finset.univ.val.map (fun i => (e i : (jacobiP a b n).SplittingField))).Nodup :=
      Finset.univ.nodup.map (fun i j h => e.injective (Subtype.val_injective h))
    rw [Multiset.Nodup.ext (nodup_roots hsep.map) hnd]
    intro y
    rw [Multiset.mem_map]
    constructor
    · intro hy
      have hy' : y ∈ (jacobiP a b n).rootSet (jacobiP a b n).SplittingField := by
        rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def]; exact hy
      exact ⟨e.symm ⟨y, hy'⟩, Finset.mem_univ_val _, by simp⟩
    · rintro ⟨i, -, rfl⟩
      have key : ∀ z : (jacobiP a b n).SplittingField,
          z ∈ (jacobiP a b n).rootSet (jacobiP a b n).SplittingField →
            z ∈ ((jacobiP a b n).map (algebraMap ℚ (jacobiP a b n).SplittingField)).roots := by
        intro z hz
        rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def] at hz
        exact hz
      exact key _ (e i).2
  have hfac : (jacobiP a b n).map (algebraMap ℚ (jacobiP a b n).SplittingField) =
      C (algebraMap ℚ (jacobiP a b n).SplittingField (jacobiP a b n).leadingCoeff) *
        ∏ i, (polyX - C (e i : (jacobiP a b n).SplittingField)) := by
    have hspl := SplittingField.splits (jacobiP a b n)
    conv_lhs => rw [hspl.eq_prod_roots, hroots, leadingCoeff_map]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    all_goals rfl
  have hd : algebraMap ℚ (jacobiP a b n).SplittingField
        ((jacobiP a b n).leadingCoeff ^ (2 * n - 2)) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((e i : (jacobiP a b n).SplittingField) - e j) ^ 2 =
      algebraMap ℚ (jacobiP a b n).SplittingField (jacobiDiscriminant a b n) :=
    hdisc.rat a b n _ (fun i => (e i : (jacobiP a b n).SplittingField)) hfac
  have hsq : ∏ i, ∏ j ∈ Finset.Ioi i,
        ((e i : (jacobiP a b n).SplittingField) - e j) ^ 2 =
      (∏ i, ∏ j ∈ Finset.Ioi i, ((e j : (jacobiP a b n).SplittingField) - e i)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have hD : jacobiDiscriminant a b n =
      (jacobiP a b n).leadingCoeff ^ (2 * n - 2) * q ^ 2 := by
    apply (algebraMap ℚ (jacobiP a b n).SplittingField).injective
    rw [← hd, hsq, ← hq]
    simp only [map_mul, map_pow]
  have hD0 : jacobiDiscriminant a b n ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hodd
    exact (Int.not_odd_iff_even.mpr Even.zero) hodd
  rw [hD] at hD0 hodd
  rw [padicValRat.mul (left_ne_zero_of_mul hD0) (right_ne_zero_of_mul hD0), padicValRat.pow,
    padicValRat.pow] at hodd
  have h2 : ((2 * n - 2 : ℕ) : ℤ) = 2 * ((n - 1 : ℕ) : ℤ) := by omega
  rw [h2] at hodd
  apply (Int.not_even_iff_odd.mpr hodd)
  exact ⟨((n - 1 : ℕ) : ℤ) * padicValRat p (jacobiP a b n).leadingCoeff + padicValRat p q,
    by push_cast; ring⟩

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p` of a finite product of nonzero rationals. -/
theorem padicValRat_finset_prod {ι : Type*} (s : Finset ι) (g : ι → ℚ)
    (hg : ∀ i ∈ s, g i ≠ 0) :
    padicValRat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValRat p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      padicValRat.mul (hg x (Finset.mem_insert_self x s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- For `0 < N < p²`, `v_p(N)` is `1` or `0` according as `p ∣ N`. -/
theorem padicValRat_natCast_of_lt_sq {N : ℕ} (hN0 : 0 < N) (hN : N < p * p) :
    padicValRat p (N : ℚ) = if p ∣ N then 1 else 0 := by
  rw [padicValRat.of_nat]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hN0)
    have hkp : k < p := Nat.lt_of_mul_lt_mul_left hN
    rw [padicValNat.mul hp.out.ne_zero hk0.ne', padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (fun h => absurd (Nat.le_of_dvd hk0 h) (by omega))]
    simp
  · rw [padicValNat.eq_zero_of_not_dvd h]; simp

theorem padicValRat_natCast_of_lt_two_mul {N : ℕ} (hN0 : 0 < N) (hN : N < 2 * p) :
    padicValRat p (N : ℚ) = if N = p then 1 else 0 := by
  have hp2 := hp.out.two_le
  rw [padicValRat_natCast_of_lt_sq hN0 (by nlinarith)]
  by_cases h : N = p
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨k, rfl⟩
    have hk : k < 2 := Nat.lt_of_mul_lt_mul_left (by linarith : p * k < p * 2)
    interval_cases k <;> simp_all

theorem padicValRat_natCast_of_lt_three_mul (hp3 : 3 ≤ p) {N : ℕ} (hN1 : p < N)
    (hN : N < 3 * p) : padicValRat p (N : ℚ) = if N = 2 * p then 1 else 0 := by
  rw [padicValRat_natCast_of_lt_sq (N := N) (by omega) (by nlinarith)]
  by_cases h : N = 2 * p
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨k, rfl⟩
    have hk1 : 1 < k := Nat.lt_of_mul_lt_mul_left (by linarith : p * 1 < p * k)
    have hk3 : k < 3 := Nat.lt_of_mul_lt_mul_left (by linarith : p * k < p * 3)
    interval_cases k
    omega

/-- `v_p` of one factor of (5.31). -/
theorem padicValRat_discriminant_factor {A B C D : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hD : 0 < D) (i : ℤ) (j k l : ℕ) :
    padicValRat p ((A : ℚ) ^ i * (B : ℚ) ^ j * (C : ℚ) ^ k * (D : ℚ) ^ l) =
      i * padicValRat p (A : ℚ) + j * padicValRat p (B : ℚ) + k * padicValRat p (C : ℚ) +
        l * padicValRat p (D : ℚ) := by
  have hA' : (A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hC' : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hA') (pow_ne_zero _ hB'))
      (pow_ne_zero _ hC')) (pow_ne_zero _ hD'),
    padicValRat.mul (mul_ne_zero (zpow_ne_zero _ hA') (pow_ne_zero _ hB')) (pow_ne_zero _ hC'),
    padicValRat.mul (zpow_ne_zero _ hA') (pow_ne_zero _ hB'), padicValRat.zpow,
    padicValRat.pow, padicValRat.pow, padicValRat.pow]

theorem sum_mul_ite_eq_of_iff {s : Finset ℕ} {c : ℕ} (g : ℕ → ℤ) (P : ℕ → Prop)
    [DecidablePred P] (hc : c ∈ s) (hP : ∀ h ∈ s, P h ↔ h = c) :
    ∑ h ∈ s, g h * (if P h then 1 else 0) = g c := by
  rw [Finset.sum_eq_single c (fun h hh hne => by
      rw [ite_eq_right (fun hP' => hne ((hP h hh).mp hP')), mul_zero])
    (fun hc' => absurd hc hc'), ite_eq_left ((hP c hc).mpr rfl), mul_one]

/-- **The discriminant valuation in Lemma 5.16.** For a prime `p ≥ 3` with `p ≤ n`,
`n + a + b < 2p` and `2n + a + b < 3p`, `v_p(jacobiDiscriminant a b n) = p`. -/
theorem padicValRat_jacobiDiscriminant {a b n : ℕ} (hp3 : 3 ≤ p) (hpn : p ≤ n)
    (h2 : n + a + b < 2 * p) (h3 : 2 * n + a + b < 3 * p) :
    padicValRat p (jacobiDiscriminant a b n) = p := by
  have hp2 : p ≠ 2 := by omega
  have hcast : ∀ h : ℕ, ((h : ℚ) + a) = ((h + a : ℕ) : ℚ) ∧ ((h : ℚ) + b) = ((h + b : ℕ) : ℚ) ∧
      ((n : ℚ) + h + a + b) = ((n + h + a + b : ℕ) : ℚ) := fun h =>
    ⟨by push_cast; ring, by push_cast; ring, by push_cast; ring⟩
  have hT : ∀ h ∈ Finset.Icc 1 n,
      (h : ℚ) ^ ((h : ℤ) - 2 * n + 2) * ((h : ℚ) + a) ^ (h - 1) * ((h : ℚ) + b) ^ (h - 1) *
        ((n : ℚ) + h + a + b) ^ (n - h) =
      (h : ℚ) ^ ((h : ℤ) - 2 * n + 2) * ((h + a : ℕ) : ℚ) ^ (h - 1) *
        ((h + b : ℕ) : ℚ) ^ (h - 1) * ((n + h + a + b : ℕ) : ℚ) ^ (n - h) := by
    intro h _
    rw [(hcast h).1, (hcast h).2.1, (hcast h).2.2]
  have hTne : ∀ h ∈ Finset.Icc 1 n,
      (h : ℚ) ^ ((h : ℤ) - 2 * n + 2) * ((h + a : ℕ) : ℚ) ^ (h - 1) *
        ((h + b : ℕ) : ℚ) ^ (h - 1) * ((n + h + a + b : ℕ) : ℚ) ^ (n - h) ≠ 0 := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have e1 : (h : ℚ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
    have e2 : ((h + a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show h + a ≠ 0 by omega)
    have e3 : ((h + b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show h + b ≠ 0 by omega)
    have e4 : ((n + h + a + b : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show n + h + a + b ≠ 0 by omega)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ e1) (pow_ne_zero _ e2))
      (pow_ne_zero _ e3)) (pow_ne_zero _ e4)
  have hval : ∀ h ∈ Finset.Icc 1 n, padicValRat p
      ((h : ℚ) ^ ((h : ℤ) - 2 * n + 2) * ((h + a : ℕ) : ℚ) ^ (h - 1) *
        ((h + b : ℕ) : ℚ) ^ (h - 1) * ((n + h + a + b : ℕ) : ℚ) ^ (n - h)) =
      ((h : ℤ) - 2 * n + 2) * (if h = p then 1 else 0) +
        ((h - 1 : ℕ) : ℤ) * (if h + a = p then 1 else 0) +
        ((h - 1 : ℕ) : ℤ) * (if h + b = p then 1 else 0) +
        ((n - h : ℕ) : ℤ) * (if n + h + a + b = 2 * p then 1 else 0) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    rw [padicValRat_discriminant_factor (A := h) (B := h + a) (C := h + b)
        (D := n + h + a + b) (by omega) (by omega) (by omega) (by omega),
      padicValRat_natCast_of_lt_two_mul (N := h) (by omega) (by omega),
      padicValRat_natCast_of_lt_two_mul (N := h + a) (by omega) (by omega),
      padicValRat_natCast_of_lt_two_mul (N := h + b) (by omega) (by omega),
      padicValRat_natCast_of_lt_three_mul hp3 (N := n + h + a + b) (by omega) (by omega)]
  have h2ne : ((2 : ℚ)⁻¹) ^ (n * (n - 1)) ≠ 0 := pow_ne_zero _ (inv_ne_zero two_ne_zero)
  have hv2 : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat_primes hp2]
    simp
  have hs1 : ∑ h ∈ Finset.Icc 1 n, ((h : ℤ) - 2 * n + 2) * (if h = p then 1 else 0) =
      (p : ℤ) - 2 * n + 2 :=
    sum_mul_ite_eq_of_iff (s := Finset.Icc 1 n) (c := p) (fun h : ℕ => (h : ℤ) - 2 * n + 2)
      (fun h => h = p) (Finset.mem_Icc.mpr ⟨by omega, hpn⟩) (fun h _ => Iff.rfl)
  have hs2 : ∑ h ∈ Finset.Icc 1 n, ((h - 1 : ℕ) : ℤ) * (if h + a = p then 1 else 0) =
      ((p - a - 1 : ℕ) : ℤ) :=
    sum_mul_ite_eq_of_iff (s := Finset.Icc 1 n) (c := p - a) (fun h : ℕ => ((h - 1 : ℕ) : ℤ))
      (fun h => h + a = p) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun h _ => show h + a = p ↔ h = p - a by omega)
  have hs3 : ∑ h ∈ Finset.Icc 1 n, ((h - 1 : ℕ) : ℤ) * (if h + b = p then 1 else 0) =
      ((p - b - 1 : ℕ) : ℤ) :=
    sum_mul_ite_eq_of_iff (s := Finset.Icc 1 n) (c := p - b) (fun h : ℕ => ((h - 1 : ℕ) : ℤ))
      (fun h => h + b = p) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun h _ => show h + b = p ↔ h = p - b by omega)
  have hs4 : ∑ h ∈ Finset.Icc 1 n, ((n - h : ℕ) : ℤ) *
      (if n + h + a + b = 2 * p then 1 else 0) = ((n - (2 * p - (n + a + b)) : ℕ) : ℤ) :=
    sum_mul_ite_eq_of_iff (s := Finset.Icc 1 n) (c := 2 * p - (n + a + b))
      (fun h : ℕ => ((n - h : ℕ) : ℤ)) (fun h => n + h + a + b = 2 * p)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun h _ => show n + h + a + b = 2 * p ↔ h = 2 * p - (n + a + b) by omega)
  rw [jacobiDiscriminant_eq, Finset.prod_congr rfl hT,
    padicValRat.mul h2ne (Finset.prod_ne_zero_iff.mpr hTne), padicValRat.pow, padicValRat.inv,
    hv2, neg_zero, mul_zero, zero_add, padicValRat_finset_prod _ _ hTne,
    Finset.sum_congr rfl hval, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib,
    hs1, hs2, hs3, hs4]
  omega

end Valuation

end UnequalParameters

end ArithmeticOfJacobiPolynomials
