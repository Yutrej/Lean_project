-- Authored by: YANG Ruijia, LIU Rongqin
--

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open BigOperators


-- `p` refers an odd prime
variable {p : ℕ} (hp : p.Prime ∧ p > 2)
include hp
-- `p` is a Wieferich prime if `p` is a prime and `p² ∣ 2^{p-1} - 1`
def W : Set ℕ :=
  {p | (2 : ZMod (p ^ 2)) ^ (p - 1) = 1}

-- `ord2 (n) := ord_{n}(2)`
noncomputable def ord2 (n : ℕ) : ℕ :=
  orderOf (2 : ZMod n)



lemma ord2_p_div_p_minus_1 : ord2 p ∣ p - 1 := by
  -- This lemma is a useful consequence followed from Fermat's Little Theorem
  have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
    omega
  haveI : Fact p.Prime := ⟨hp.1⟩
  have h_Fermat : (2 : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h2_ne_zero
  exact orderOf_dvd_of_pow_eq_one h_Fermat

omit hp in
lemma characterization_ord2_p : ∃ k, 2 ^ (ord2 p) = p*k + 1 := by
  have h_pow_p : (2 : ZMod p) ^ (ord2 p) = (1 : ZMod p) := pow_orderOf_eq_one 2
  have h_pow_p_0 : (2 : ZMod p) ^ (ord2 p) - (1 : ZMod p) = 0 := by
    rw [h_pow_p, sub_self]
  have h_dvd : p ∣ (2 ^ (ord2 p) - 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    simp [h_pow_p_0]
  obtain ⟨k, hk⟩ := h_dvd
  use k
  apply Nat.eq_add_of_sub_eq
  · exact Nat.one_le_pow (ord2 p) 2 (by norm_num)
  · exact hk

lemma ord2_p2_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := by
  -- An division property which is useful in the final argument
  have h_div : ord2 (p) ∣ ord2 (p^2) := by
    let f : ZMod (p^2) →+* ZMod p := ZMod.castHom (show p ∣ p^2 by norm_num) (ZMod p)
    have hf : f 2  = 2 := map_natCast f 2
    have h_pow_p2 : (2 : ZMod (p^2)) ^ ord2 (p^2) = (1 : ZMod (p^2)) :=
      pow_orderOf_eq_one 2
    have h_apply_f : f (2 ^ ord2 (p^2)) = f 1 := congr_arg f h_pow_p2
    rw [map_pow, map_one] at h_apply_f
    have h_pow_p : (2 : ZMod p) ^ ord2 (p^2) = (1 : ZMod p) := by
      rw [hf] at h_apply_f; assumption
    exact orderOf_dvd_of_pow_eq_one h_pow_p
  -- We will use this property to conclude `h_div'`
  have h_pow : (2 : ZMod (p^2)) ^ (p * ord2 p) = (1 : ZMod (p^2)) := by
    obtain ⟨k, hk⟩ := characterization_ord2_p
    rw [pow_mul']; rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by rfl]
    rw [← Nat.cast_pow]; rw [hk]; push_cast
    rw [add_pow]; rw [Finset.sum_range_succ'] -- expand `(↑p * ↑k + 1) ^ p` using Binomial Theorem
    simp only [Nat.choose_zero_right, pow_zero, one_pow, mul_one, Nat.cast_one]
    simp only [add_eq_right]
    apply Finset.sum_eq_zero
    intro i _
    cases i with
    | zero =>
      simp only [Nat.zero_add, Nat.choose_one_right, pow_one]
      calc ↑p * ↑k * ↑p
        _ = (p : ZMod (p^2)) ^ 2 * ↑k := by ring
        _ = ↑(p^2) * ↑k := by rw [← Nat.cast_pow]
        _ = 0 * k := by rw [ZMod.natCast_self]
        _ = 0 := by ring
    | succ j =>
      have h_zero : (p * k : ZMod (p^2)) ^ 2 = 0 := by
        calc (↑p * ↑k) ^ 2
            _ = (p : ZMod (p^2)) ^ 2 * (k : ZMod (p^2)) ^ 2 := mul_pow _ _ _
            _ = ↑(p^2) * ↑k ^ 2 := by rw [← Nat.cast_pow]
            _ = 0 * ↑k ^ 2 := by rw [ZMod.natCast_self]
            _ = 0 := by ring
      calc (↑p * ↑k : ZMod (p^2)) ^ (j + 1 + 1) * ↑(p.choose (j + 1 + 1))
          _ = ↑(p.choose (j + 1 + 1)) * ((↑p * ↑k) ^ 2 * (↑p * ↑k) ^ j) := by ring
          _ = ↑(p.choose (j + 1 + 1)) * (0 * (↑p * ↑k) ^ j) := by rw [h_zero]
          _ = 0 := by ring
  -- Now, we have enough info to conclude that ther are only two possibilities for `ord2 (p^2)`
  have h_div_p_1 : ord2 p ∣ p - 1 := ord2_p_div_p_minus_1 hp
  have h_div' : ord2 (p^2) ∣ (p * ord2 p) := orderOf_dvd_of_pow_eq_one h_pow
  obtain ⟨k, hk⟩ := h_div
  rw [hk] at h_div'
  rw [mul_comm (ord2 p) k] at h_div'
  have h_ord_pos : 0 < ord2 p := by
    apply Nat.pos_of_ne_zero
    intro h_zero
    rw [h_zero, zero_dvd_iff] at h_div_p_1
    omega
  have h_k_div_p : k ∣ p := Nat.dvd_of_mul_dvd_mul_right h_ord_pos h_div'
  rcases (Nat.dvd_prime hp.1).mp h_k_div_p with rfl | rfl
  · left; rw [hk, mul_comm, one_mul]
  · right; rw [hk, mul_comm]


lemma nonW_primes_ord2_relation (hp_nonW : p ∉ W) : ord2 (p^2) = p * ord2 (p) := by
  have h_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := ord2_p2_branch hp
  have h_div_p_1 : ord2 p ∣ p - 1 := ord2_p_div_p_minus_1 hp
  -- The final discussion for two branches
  rcases h_branch with h_eq | h_eq
  · exfalso
    apply hp_nonW
    change (2 : ZMod (p^2)) ^ (p - 1) = 1
    rw [← h_eq] at h_div_p_1
    exact orderOf_dvd_iff_pow_eq_one.mp h_div_p_1
  · exact h_eq

lemma W_primes_ord2_relation (hp_W : p ∈ W) : ord2 (p^2) = ord2 (p) := by
  have h_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := ord2_p2_branch hp
  rcases h_branch with h_eq | h_eq
  · exact h_eq
  · exfalso
    have h_pW : (2 : ZMod (p^2)) ^ (p - 1) = 1 := hp_W
    -- By definition, we have `ord2 (p^2) ∣ p - 1`
    have h_div : ord2 (p^2) ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr h_pW
    rw [h_eq] at h_div
    -- This implies p * ord2 p ∣ p - 1, hence p ∣ p - 1
    rw [mul_comm] at h_div
    have h_p_dvd : p ∣ p - 1 := dvd_of_mul_left_dvd h_div
    -- But p cannot divide p - 1, contradiction
    have h_p_gt_1 : 1 < p := by omega
    have h_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt h_p_gt_1
    have h_le : p ≤ p - 1 := Nat.le_of_dvd h_sub_pos h_p_dvd
    omega


def P (r : ℕ) : Set ℕ :=
  {p | (p ∉ W) ∧ (ord2 p = r)}

/- We first show that such set is finite so that we may
  write it as a ascending list p₁ < ⋯ < pₘ. -/
lemma P_r_is_finite (r : ℕ) (hr : r ≥ 1) : (P r).Finite := by
  sorry

noncomputable def P_list (r : ℕ) (h_Pfin : (P r).Finite) : List ℕ :=
  h_Pfin.toFinset.sort (· ≤ ·)

/-
  For each `pⱼ` in P_r, we have `ord2 (pⱼ^2) = pr` and `ord2 pⱼ = r`.
  Then `2^r ≡ 1 mod pⱼ`, and `2^{pⱼ-1} ≡ 1 mod pⱼ` by Fermat's little thm.
  Thus, we have `r ∣ pⱼ-1` i.e. `pⱼ ≡ 1 mod r`.
  Hence `pⱼ ≥ jr+1`.
-/
lemma lowerBound_of_p_in_P_r (r : ℕ) (hr : r ≥ 1) (h_Pfin : (P r).Finite) :
  ∀ (j : ℕ) (hj : j < (P_list r h_Pfin).length),
    (P_list r h_Pfin).get ⟨j, hj⟩ ≥ (j+1)*r + 1  -- `j` starts from 0
    := by
  sorry

/-
  Since `pⱼ ∣ 2^r - 1` for each j and `pⱼ` are distinct primes, they
  are distinct prime factors of `2^r - 1`.
  Using FTA, we see `∏ pⱼ ≤ 2^r - 1 < 2^r`.
-/
lemma upperBound_of_prod_in_P_r (r : ℕ) (hr : r ≥ 1) (h_Pfin : (P r).Finite) :
    (P_list r h_Pfin).prod < 2^r := by
  sorry

/-
  Combining the above two bounds, we get `∏ (jr+1) < 2^r`.
  Ignoring the 1, it follows that `rᵐm! < 2^r`.
  Taking logrithm, we have `m < {r · log 2}/{log r}` for `r > 1`.
  And for `r = 1`, the set `P r` is empty hence `m = 0`.
-/
lemma upperBound_of_m_by_r (r : ℕ) (hr : r > 1) (h_Pfin : (P r).Finite) :
    (P_list r h_Pfin).length < (r * Real.log 2) / (Real.log r) := by
  sorry

/-
  The contribution to the series can be divided into each `P r`, that is
    `∑_{p ∉ W} {1 / ord2 (p^2)} = ∑_{r ≥ 2} { ∑_{p ∈ P r} {1 / ord2 (p^2)} }`.
-/
lemma divideContribution_into_r :
    ∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), (1 : ℝ) / (ord2 (p ^ 2)) =
    ∑' (r : ℕ), ∑' (p : {p // p ∈ P r}), (1 : ℝ) / (ord2 (p ^ 2))
    := by
  sorry


-- The n-th harmonic number
def H (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (1 / (i + 1) : ℚ)

/-
  For each contribution, we have
    `∑_{p ∈ P r} {1 / ord2 (p^2)} = ∑_{p ∈ P r} {1 / pr} ≤ ∑ {1 / (jr+1)r}`
  using the __lowerBound_of_p_in_P_r__.
  Ignoring the 1, we get `∑_{p ∈ P r} {1 / ord2 (p^2)} ≤ 1/r² H m`.
  Then, apply __upperBound_of_m_by_r__, we get
    `∑_{p ∈ P r} {1 / ord2 (p^2)} ≤ 1/r² H ⌊{r · log 2}/{log r}⌋`.
-/
lemma upperBound_of_each_contribution (r : ℕ) (hr : r > 1) (h_Pfin : (P r).Finite) :
    ∑ p ∈ h_Pfin.toFinset, (1 : ℝ) / (ord2 (p^2))
    ≤ (1 : ℝ)/(r^2) * H (Nat.floor ((r * Real.log 2)/(Real.log r))) := by
  sorry

/-
  Now, using __divideContribution_into_r__, we have that
    `∑_{p ∉ W} {1 / ord2 (p^2)} ≤ ∑ {1/r² H ⌊{r · log 2}/{log r}⌋}`.
-/
lemma upperBound_integrate_all_contributions :
    ∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), (1 : ℝ) / (ord2 (p ^ 2))
    ≤ ∑' (r : ℕ), (1 : ℝ)/(r^2) * H (Nat.floor ((r * Real.log 2)/(Real.log r))) := by
  sorry


-- theorem ReciprocalOrderSeries_of_nonW_primes_converges :
--     Summable ( fun (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}) => (1 : ℝ) / (ord2 (p^2)) ) := by
--   sorry
