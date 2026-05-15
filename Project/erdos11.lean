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

section Need_hp
-- `p` refers an odd prime
variable {p : ℕ} (hp : p.Prime ∧ p > 2)
include hp
-- `p` is a Wieferich prime if `p` is a prime and `p² ∣ 2^{p-1} - 1`
def W : Set ℕ :=
  {p | p.Prime ∧ p > 2 ∧ (2 : ZMod (p ^ 2)) ^ (p - 1) = 1}

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
    change p.Prime ∧ p > 2 ∧ (2 : ZMod (p^2)) ^ (p - 1) = 1
    rw [← h_eq] at h_div_p_1
    constructor
    · exact hp.1
    constructor
    · exact hp.2
    exact orderOf_dvd_iff_pow_eq_one.mp h_div_p_1
  · exact h_eq

lemma W_primes_ord2_relation (hp_W : p ∈ W) : ord2 (p^2) = ord2 (p) := by
  have h_branch : (ord2 (p^2) = ord2 p) ∨ (ord2 (p^2) = p * ord2 p) := ord2_p2_branch hp
  rcases h_branch with h_eq | h_eq
  · exact h_eq
  · exfalso
    have h_pW : (2 : ZMod (p^2)) ^ (p - 1) = 1 := hp_W.2.2
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

end Need_hp

def P (r : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p > 2 ∧ (p ∉ W) ∧ (ord2 p = r)}

/- We first show that such set is finite so that we may
  write it as a ascending list p₁ < ⋯ < pₘ. -/
/-
  (2 Zmod p) ^ r = 1     2 ^ r mod p = 1     2^r ≥ 1     2^r - 1 mod p = 0
  finally p ∣ 2 ^r -1 -/
lemma dvd_of_ord2_eq (p r : ℕ) (h : ord2 p = r) : p ∣ 2^r - 1 := by
  have h1 : (2 : ZMod p) ^ r = 1 := by
    have h2 : orderOf (2 : ZMod p) = r := h
    rw [← h2]
    exact pow_orderOf_eq_one (2 : ZMod p)
  have h3 : ((2^r : ℕ) : ZMod p ) = 1 := by
    simpa
  have h4 : (2^r : ℕ) ≥ 1 := by
    apply Nat.one_le_pow
    exact Nat.zero_lt_two
  have h5 : ((2^r - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub h4]
    rw [h3]
    simp
  have h6 : p ∣ (2^r - 1 :ℕ) := by
    rw[← ZMod.natCast_eq_zero_iff]
    exact h5
  exact h6

lemma P_subset (r : ℕ) : P r ⊆ {p : ℕ | p ∣ 2^r - 1} := by
  intro p hp
  have h7 : ord2 p = r := hp.2.2.2
  exact dvd_of_ord2_eq p r  h7

lemma P_r_is_finite (r : ℕ) (hr : r ≥ 1) : (P r).Finite := by
  have h1 : P r ⊆ {p : ℕ | p ∣ 2^r - 1} := by apply P_subset r
  have h2 : (2^r - 1 : ℕ) > 0 := by
    have h3 : 2^r ≥ 2 := by
      have h4 : 2^r ≥ 2^1 := by exact Nat.le_pow hr
      omega
    omega
  have h3 : {p : ℕ | p ∣ 2^r - 1} = (Nat.divisors (2^r - 1) : Set ℕ) := by
    ext p  -- A = B ↔ ∀ p, p∈A ↔ p∈B
    simp
    omega
  rw [h3] at h1
  apply Set.Finite.subset -- two conditions :    finite and subset
  · exact Finset.finite_toSet (Nat.divisors (2^r - 1))
  · exact h1

noncomputable def P_list (r : ℕ) (h_Pfin : (P r).Finite) : List ℕ :=
  h_Pfin.toFinset.sort (· ≤ ·)

-- Three auxilary lemmas
lemma mod_eq_one_of_mem_P {r p : ℕ} (hp : p ∈ P r) : p % r = 1 % r := by
  -- We know r ∣ p - 1. This means p - 1 is a multiple of r.
  -- Hence p ≡ 1 [MOD r], so p % r = 1 % r.
  have h_prime : p.Prime ∧ p > 2 := ⟨hp.1, hp.2.1⟩
  have h_ord : ord2 p = r := hp.2.2.2
  have h_div : r ∣ p - 1 := by
    have h_ord_div := ord2_p_div_p_minus_1 h_prime
    rwa [h_ord] at h_ord_div
  obtain ⟨k, hk⟩ := h_div
  have hp_eq : p = r * k + 1 := by omega
  rw [hp_eq, Nat.add_comm, Nat.add_mul_mod_self_left]

lemma ge_add_r_of_gt_of_mod_eq {a b r : ℕ}
    (h_gt : a > b) (ha : a % r = 1 % r) (hb : b % r = 1 % r) :
    a ≥ b + r := by
  -- Using `ha` and `hb`, `a % r = b % r`, which implies `r ∣ a - b`.
  -- Since `a > b`, `a - b > 0`, so `a - b ≥ r`.
  -- Therefore, `a ≥ b + r`.
  have ha_eq := Nat.div_add_mod a r
  have hb_eq := Nat.div_add_mod b r
  have h_q : a / r > b / r := by
    by_contra h_le
    have h_le' : a / r ≤ b / r := by omega
    have h_mul1 : r * (a / r) ≤ r * (b / r) := Nat.mul_le_mul_left r h_le'
    have h_mul2 : (a / r) * r ≤ (b / r) * r := Nat.mul_le_mul_right r h_le'
    omega
  have h_mul1 : r * (a / r) ≥ r * (b / r + 1) := Nat.mul_le_mul_left r h_q
  have h_mul2 : (a / r) * r ≥ (b / r + 1) * r := Nat.mul_le_mul_right r h_q
  have h_add1 : r * (b / r + 1) = r * (b / r) + r := by rw [Nat.mul_add, Nat.mul_one]
  have h_add2 : (b / r + 1) * r = (b / r) * r + r := by rw [Nat.add_mul, Nat.one_mul]
  omega

lemma get_zero_ge_r_add_one {r p : ℕ} (hp : p ∈ P r) : p ≥ r + 1 := by
  -- For base case
  have h_prime : p.Prime ∧ p > 2 := ⟨hp.1, hp.2.1⟩
  have h_ord : ord2 p = r := hp.2.2.2
  have h_div : r ∣ p - 1 := by
    have h_ord_div := ord2_p_div_p_minus_1 h_prime
    rwa [h_ord] at h_ord_div
  have h_pos : 0 < p - 1 := by omega
  have h_le : r ≤ p - 1 := by
    exact Nat.le_of_dvd h_pos h_div
  omega
/-
  For each `pⱼ` in P_r, we have `ord2 (pⱼ^2) = pr` and `ord2 pⱼ = r`.
  Then `2^r ≡ 1 mod pⱼ`, and `2^{pⱼ-1} ≡ 1 mod pⱼ` by Fermat's little thm.
  Thus, we have `r ∣ pⱼ-1` i.e. `pⱼ ≡ 1 mod r`.
  Hence `pⱼ ≥ jr+1`.
-/
lemma lowerBound_of_p_in_P_r (r : ℕ) (h_Pfin : (P r).Finite) :
  ∀ (j : ℕ) (hj : j < (P_list r h_Pfin).length),
    (P_list r h_Pfin).get ⟨j, hj⟩ ≥ (j+1)*r + 1  -- `j` starts from 0
    := by
  let L := P_list r h_Pfin
  have h_mem_L : ∀ {x}, x ∈ L ↔ x ∈ P r := by
    intro x
    simp [L, P_list]
  intro j
  induction j with
  | zero =>
    intro hj
    have h0_mem : L.get ⟨0, hj⟩ ∈ P r := h_mem_L.mp (List.get_mem L ⟨0, hj⟩)
    have h_base := get_zero_ge_r_add_one h0_mem
    simpa
  | succ j ih =>
    intro hj
    -- Inductive step: L.get (j + 1) > L.get j since L is strictly sorted.
    -- Apply `ge_add_r_of_gt_of_mod_eq` and the inductive hypothesis `ih`.
    have hj' : j < L.length := by calc
      j < j + 1    := by omega
      _ < L.length := hj
    have hp_succ : L.get ⟨j+1, hj⟩ ∈ P r := by
      exact h_mem_L.mp (List.get_mem L ⟨j+1, hj⟩)
    have hp : L.get ⟨j, hj'⟩ ∈ P r := by
      exact h_mem_L.mp (List.get_mem L ⟨j, hj'⟩)
    have h_gt : L.get ⟨j+1, hj⟩ > L.get ⟨j, hj'⟩ := by
      have h_sort : L.Pairwise (· ≤ ·) := by
        simp [L, P_list]
      have h_nodup : L.Nodup := by unfold L P_list; simp
      have h_lt_fin : (⟨j, hj'⟩ : Fin L.length) < ⟨j+1, hj⟩ := by simp
      have h_le : L.get ⟨j, hj'⟩ ≤ L.get ⟨j+1, hj⟩ :=
        List.pairwise_iff_get.mp h_sort ⟨j, hj'⟩ ⟨j+1, hj⟩ h_lt_fin
      have h_ne : L.get ⟨j, hj'⟩ ≠ L.get ⟨j+1, hj⟩ := by
        intro heq
        have h_eq_idx : (⟨j, hj'⟩ : Fin L.length) = ⟨j+1, hj⟩ :=
          (List.Nodup.get_inj_iff h_nodup).mp heq
        injection h_eq_idx
        omega
      omega
    have h_mod_succ := mod_eq_one_of_mem_P hp_succ
    have h_mod := mod_eq_one_of_mem_P hp
    have h_step := ge_add_r_of_gt_of_mod_eq h_gt h_mod_succ h_mod
    have h_ih := ih hj'
    calc
      (P_list r h_Pfin).get ⟨j + 1, hj⟩ ≥ L.get ⟨j, hj'⟩ + r := h_step
      _ ≥ (j + 1) * r + 1 + r := by exact Nat.add_le_add_right (ih hj') r
      _ = (j + 1 + 1) * r + 1 := by ring


/-
  Since `pⱼ ∣ 2^r - 1` for each j and `pⱼ` are distinct primes, they
  are distinct prime factors of `2^r - 1`.
  Using FTA, we see `∏ pⱼ ≤ 2^r - 1 < 2^r`.
-/
-- First we need a easy lemma
lemma prime_dvd_list_prod {p : ℕ} (hp : p.Prime) {t : List ℕ} :
    p ∣ t.prod → ∃ x ∈ t, p ∣ x := by
  induction t with
  | nil =>
    intro h
    simp only [List.prod_nil] at h
    exact (hp.not_dvd_one h).elim
  | cons x xs ih =>
    intro h
    rw [List.prod_cons] at h
    have h_or := hp.dvd_mul.mp h
    cases h_or with
    | inl hx =>
      use x
      simp [hx]
    | inr hxs =>
      rcases ih hxs with ⟨y, hy_mem, hy_dvd⟩
      use y
      simp [hy_mem, hy_dvd]

lemma upperBound_of_prod_in_P_r (r : ℕ) (hr : r ≥ 1) (h_Pfin : (P r).Finite) :
    (P_list r h_Pfin).prod < 2^r := by
  classical
  let L := P_list r h_Pfin
  -- First show that each element in the list is in the set `P r`
  have h_memP : ∀ p ∈ L, p ∈ P r := by
    intro p hp
    unfold L P_list at hp
    have hfin  : p ∈ h_Pfin.toFinset := by
      simpa using hp
    exact h_Pfin.mem_toFinset.mp hfin
  -- From definition of `P r`, each element divides `2^r - 1`
  have h_each_dvd : ∀ p ∈ L, p ∣ 2^r - 1 := by
    intro p hp_L
    have hp_Pr : p ∈ P r := h_memP p hp_L
    have h_ord : ord2 p = r := by
      simpa [P] using hp_Pr.2.2.2
    have h_pow : (2 : ZMod p) ^ r = 1 := by
      have : (2 : ZMod p) ^ ord2 p = 1 := pow_orderOf_eq_one (2 : ZMod p)
      rwa [h_ord] at this
    rw [← ZMod.natCast_eq_zero_iff]
    simpa using (sub_eq_zero.mpr h_pow)
  -- Also, each element is prime
  have h_each_prime : ∀ p ∈ L, Nat.Prime p := by
    intro p hp_L
    have hp_Pr : p ∈ P r := h_memP p hp_L
    simpa [P] using hp_Pr.1
  -- All elements are distinct simply because how we form a list from a set
  have h_distinct : L.Nodup := by
    unfold L P_list
    simp
  -- Show the product divides `2^r - 1`
  have h_prod_dvd : L.prod ∣ 2^r - 1 := by
    revert h_distinct
    revert h_each_dvd
    revert h_each_prime
    induction L with
    | nil =>
      simp
    | cons a t ih =>
      intro h_each_prime h_each_dvd h_distinct
      simp only [List.nodup_cons] at h_distinct
      rcases h_distinct with ⟨ha_not_mem, ht_distinct⟩
      -- Specify in `t` all properties we proved
      have ht_each_dvd : ∀ p ∈ t, p ∣ 2^r - 1 := by
        intro p hp
        exact h_each_dvd p (by simp [hp])
      have ht_each_prime : ∀ p ∈ t, Nat.Prime p := by
        intro p hp
        exact h_each_prime p (by simp [hp])
      -- Specify for `a`
      have ha_dvd : a ∣ 2^r - 1 := by
        exact h_each_dvd a (by simp)
      have ha_prime : Nat.Prime a := by
        exact h_each_prime a (by simp)
      -- Inductive step
      have ht_prod_dvd : t.prod ∣ 2^r - 1 := by
        exact ih ht_each_prime ht_each_dvd ht_distinct
      have h_coprime : Nat.Coprime t.prod a := by
        apply Nat.coprime_comm.mp
        apply (Nat.Prime.coprime_iff_not_dvd ha_prime).mpr
        intro hdiv
        have ha_div_n : ∃ n ∈ t, a ∣ n := (prime_dvd_list_prod ha_prime) hdiv
        have hn : ∃ n ∈ t, a = n := by
          rcases ha_div_n with ⟨n, hn_mem, ha_div⟩
          have hn_prime : Nat.Prime n := ht_each_prime n hn_mem
          have h_eq : n = a := by
            have : a ≠ 1 := by exact Nat.Prime.ne_one ha_prime
            exact (Nat.Prime.dvd_iff_eq hn_prime this).mp ha_div
          exact ⟨n, hn_mem, h_eq.symm⟩
        rcases hn with ⟨n, hn_mem, h_eq⟩
        exact ha_not_mem (h_eq ▸ hn_mem)
      have h_next_dvd : a * t.prod ∣ 2^r - 1 := by
        exact (h_coprime.symm).mul_dvd_of_dvd_of_dvd ha_dvd ht_prod_dvd
      simpa [List.prod_cons, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_next_dvd
  have : 0 < 2^r - 1 := by
    calc
      0 < 1       := by decide
      _ = 2^1 - 1 := by decide
      _ ≤ 2^r - 1 := by gcongr; decide
  have h_prod_bound : L.prod ≤ 2^r - 1 := by exact Nat.le_of_dvd this h_prod_dvd
  have final : L.prod < 2^r := by
    calc
      L.prod ≤ 2^r - 1 := h_prod_bound
      _ < 2^r := by omega
  exact final

/-
  Combining the above two bounds, we get `∏ (jr+1) < 2^r`.
  Ignoring the 1, it follows that `rᵐm! < 2^r`.
  Taking logrithm, we have `m < {r · log 2}/{log r}` for `r > 1`.
  And for `r = 1`, the set `P r` is empty hence `m = 0`.
-/
lemma upperBound_of_m_by_r (r : ℕ) (hr : r > 1) (h_Pfin : (P r).Finite) :
    (P_list r h_Pfin).length < (r * Real.log 2) / (Real.log r) := by
  let L := P_list r h_Pfin
  let m := L.length
  -- `L.prod < 2^r`
  have h_Lprod_upper : L.prod < 2^r := by
    exact upperBound_of_prod_in_P_r r (by omega) h_Pfin
  -- `∏ (jr+1) < L.prod`
  have h_Lprod_lower_1 :
      ((List.range m).map (fun j => ((j+1)*r + 1))).prod ≤ L.prod := by
    have h_elem_lower :
        ∀ (j : ℕ) (hj : j < m), (j+1)*r + 1 ≤ L.get ⟨j, hj⟩ := by
      intro j hj
      exact lowerBound_of_p_in_P_r r h_Pfin j hj
    let g := fun j => if hj : j < m then L.get ⟨j, hj⟩ else 0
    have h_L_eq : L = (List.range m).map g := by
      apply List.ext_get
      · simp only [List.length_map, List.length_range, m]
      · intro i hi1 hi2
        simp only [List.get_eq_getElem, List.getElem_map,
          List.getElem_range, left_eq_dite_iff, not_lt, g]
        intro h_contr
        have : False := by simp [m] at h_contr; omega
        contradiction
    rw [h_L_eq]
    apply List.prod_le_prod'
    intro j hj
    simp only [List.mem_range] at hj
    simp only [List.get_eq_getElem, hj, ↓reduceDIte, Order.add_one_le_iff, g]
    exact h_elem_lower j hj
  have h_Lprod_lower_2 :
      ((List.range m).map (fun j => (j+1)*r)).prod ≤ L.prod := by
    have h_ignore_1 :
        ((List.range m).map (fun j => (j+1)*r)).prod ≤
        ((List.range m).map (fun j => ((j+1)*r + 1))).prod := by
      apply List.prod_le_prod'
      omega
    calc ((List.range m).map (fun j => (j+1)*r)).prod
      _ ≤ ((List.range m).map (fun j => ((j+1)*r + 1))).prod := h_ignore_1
      _ ≤ L.prod := h_Lprod_lower_1
  have h_simp_LHS :
      ((List.range m).map (fun j => (j+1)*r)).prod = r^m * m.factorial := by
    induction m with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, ih, pow_succ, Nat.factorial_succ]
      ring
  have h_ineq : r^m * m.factorial < 2^r := by
    calc r^m * m.factorial
      _ = ((List.range m).map (fun j => (j+1)*r)).prod := h_simp_LHS.symm
      _ ≤ L.prod := h_Lprod_lower_2
      _ < 2^r := h_Lprod_upper
  have h_ineq_log : m < (r * Real.log 2) / (Real.log r) := by
    have h_rm_lt_2r : (r : ℝ)^m < (2 : ℝ)^r :=
      calc ((r : ℝ)^m)
        _ ≤ ((r : ℝ)^m) * (m.factorial : ℝ) := by
          apply le_mul_of_one_le_right
          · exact pow_nonneg (Nat.cast_nonneg r) m
          · exact_mod_cast Nat.factorial_pos m
        _ < ((2 : ℝ)^r) := by exact_mod_cast h_ineq
    have h_log_lt : Real.log ((r : ℝ) ^ m) < Real.log ((2 : ℝ) ^ r) :=
      Real.log_lt_log (by positivity) h_rm_lt_2r
    rw [Real.log_pow, Real.log_pow] at h_log_lt
    have h_log_r_pos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast hr)
    exact (lt_div_iff₀ h_log_r_pos).mpr h_log_lt
  simpa [m]


/-
  The contribution to the series can be divided into each `P r`, that is
    `∑_{p ∉ W} {1 / ord2 (p^2)} = ∑_{r ≥ 2} { ∑_{p ∈ P r} {1 / ord2 (p^2)} }`.
-/
lemma divideContribution_into_r :
    ∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), (1 : ℝ) / (ord2 (p ^ 2)) =
    ∑' (r : ℕ), ∑' (p : {p // p ∈ P r}), (1 : ℝ) / (ord2 (p ^ 2))
    := by
  let f p := (1 : ℝ) / ord2 (p^2) -- for convinient
  -- left set is the union of all the right sets
  have h1 : {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} = ⋃ (r : ℕ), P r := by
    ext p
    simp only [gt_iff_lt, Set.mem_setOf_eq, Set.mem_iUnion]  -- p ∧ p > 2 ∧ p ∉ W  iff  ∃ r, p ∈ P r
    constructor
    · intro h
      have hp_notin_W : p ∉ W := h.right.right
      have hp_prime : p.Prime := h.1
      have hp_gt_2 : p > 2 := h.2.1
      let r : ℕ := ord2 p
      have h_ord_eq : ord2 p = r := by rfl
      use r
      have h_inPr : p.Prime ∧ p > 2 ∧ (p ∉ W) ∧ (ord2 p = r) :=
        ⟨hp_prime, hp_gt_2, hp_notin_W, h_ord_eq⟩
      exact h_inPr

    · intro h
      cases h with
      | intro r hr
      have h_p_notin_W : p ∉ W := hr.2.2.1
      have h_p_prime : p.Prime := hr.1
      have h_p_gt_2 : p > 2 := hr.2.1
      have h_main : p.Prime ∧ p > 2 ∧ p ∉ W := ⟨h_p_prime, h_p_gt_2, h_p_notin_W⟩
      exact h_main
-- pairwise disjoint P r1 and P r2
  have h_disj :  Pairwise (fun (r1 r2 : ℕ) ↦ Disjoint (P r1) (P r2)) := by
    intro r1 r2 hne
    rw [Set.disjoint_left]
    intro p hp1 hp2
    -- ord2 p = r1 and ord2 p = r2
    have h1 : ∀ (q : ℕ), q ∈ P r1 ↔ (q ∉ W) ∧ (ord2 q = r1) ∧ q.Prime ∧ q > 2 := by
      intro q
      simp [P]
    have h2 : ∀ (q : ℕ), q ∈ P r2 ↔ (q ∉ W) ∧ (ord2 q = r2) ∧ q.Prime ∧ q > 2 := by
      intro q
      simp [P]
    have eq1 : ord2 p = r1 := (h1 p).mp hp1 |>.2.1
    have eq2 : ord2 p = r2 := (h2 p).mp hp2 |>.2.1
    rw [eq1] at eq2
    exact hne eq2
-- we use indicator to put every sum in N to avoid type dismatch
  have h_left : (∑' (p : {p // p.Prime ∧ p > 2 ∧ p ∉ W}), f p) =
  ∑' (p : ℕ), Set.indicator {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} f p := by
    have h_tsum_subtype : ∀ (s : Set ℕ) (g : ℕ → ℝ), (∑' (x : {x // x ∈ s}), g (x : ℕ)) =
    ∑' (x : ℕ), Set.indicator s g x := by
      intro s g
      simpa [Set.indicator] using tsum_subtype s g
    exact h_tsum_subtype {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} f
  have h_right : ∀ (r : ℕ), (∑' (p : {p // p ∈ P r}), f (p : ℕ)) =
  ∑' (p : ℕ), Set.indicator (P r) f p := by
    intro r
    have h_tsum_subtype : ∀ (s : Set ℕ) (g : ℕ → ℝ), (∑' (x : {x // x ∈ s}), g (x : ℕ)) =
    ∑' (x : ℕ), Set.indicator s g x := by
      intro s g
      simpa [Set.indicator] using tsum_subtype s g
    exact h_tsum_subtype (P r) f
  -- now by h1 we have proven that two sets are equal hence there sum are equal
  have h_fun_eq : Set.indicator (⋃ (r : ℕ), P r) f = ∑' (r : ℕ), Set.indicator (P r) f := by
    funext p
    apply?
  -- we simplify those sums to the final sums to the final goal
  have h_main1 : (∑' (p : ℕ), Set.indicator {p : ℕ | p.Prime ∧ p > 2 ∧ p ∉ W} f p) =
  ∑' (p : ℕ), Set.indicator (⋃ (r : ℕ), P r) f p := by
    rw [h1]
  have h_main3 : (∑' (r : ℕ), ∑' (p : ℕ), Set.indicator (P r) f p) =
    ∑' (r : ℕ), ∑' (p : {p // p ∈ P r}), f p := by
    apply tsum_congr
    intro r
    exact (h_right r).symm
  have h_step1 : (∑' (p : ℕ), (Set.indicator (⋃ (r : ℕ), P r) f) p) =
    ∑' (p : ℕ), (∑' (r : ℕ), Set.indicator (P r) f p) := by
    congr
    funext p
    apply?
  have h_main2 : (∑' (p : ℕ), (∑' (r : ℕ), Set.indicator (P r) f p)) =
    ∑' (r : ℕ), ∑' (p : ℕ), Set.indicator (P r) f p := by
    apply?
  rw [h_left, h_main1, h_step1, h_main2, h_main3]


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
  let s := h_Pfin.toFinset
  let L := P_list r h_Pfin
  have hL_toFinset : L.toFinset = s := by
    simp [L, P_list, s]
  have hL_nodup : L.Nodup := by apply?  -- every elem in P r is different
  -- H is strictly increasing
  have h_H_mono : ∀ (m n : ℕ), m ≤ n → (H m : ℝ) ≤ (H n : ℝ) := by
    intro m n hmn
    have h₁ : Finset.range m ⊆ Finset.range n := Finset.range_subset_range.mpr hmn
    have h₂ : ∀ i ∈ Finset.range n, (i ∉ Finset.range m) → 0 ≤ (1 : ℝ) / ((i : ℝ) + 1) := by
      intro i _ _
      have h_pos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      exact one_div_nonneg.mpr (by linarith)
    simpa [H] using Finset.sum_le_sum_of_subset_of_nonneg h₁ h₂
  -- 1/ord2(p^2) = 1/(p*r)
  have h_main₁ : ∀ p ∈ s, (1 : ℝ) / (ord2 (p^2)) = (1 : ℝ) / ((p : ℝ) * (r : ℝ)) := by
    intro p hp
    have h_p_in_Pr : p ∈ P r := by exact (Set.Finite.mem_toFinset h_Pfin).mp hp
    have h_notW : p ∉ W := h_p_in_Pr.1
    have h_ord_eq : ord2 p = r := h_p_in_Pr.2.1
    have h_prime : p.Prime := h_p_in_Pr.2.2.1
    have h_gt2 : p > 2 := h_p_in_Pr.2.2.2
    have h_ord2_p2_eq : ord2 (p^2) = p * ord2 p := nonW_primes_ord2_relation ⟨h_prime, h_gt2⟩ h_notW
    have h_ord2_p2_eq' : ord2 (p^2) = p * r := by
      rw [h_ord2_p2_eq, h_ord_eq]
    have h_cast_mul : ((p * r : ℕ) : ℝ) = (p : ℝ) * (r : ℝ) := by exact Nat.cast_mul p r
    have h_final : (1 : ℝ) / (ord2 (p^2) : ℝ) = (1 : ℝ) / ((p : ℝ) * (r : ℝ)) := by
      have h₁ : (ord2 (p^2) : ℝ) = ((p * r : ℕ) : ℝ) := by
        exact_mod_cast h_ord2_p2_eq'
      rw [h₁, h_cast_mul]
    exact h_final
  -- simplify
  have h_main₂ : ∑ p ∈ s, (1 : ℝ) / (ord2 (p^2)) = ∑ p ∈ s, (1 : ℝ) / ((p : ℝ) * (r : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h_main₁ p hp
  -- the sum of the set is the sum of the list
  have h_main₃₁ : ∑ p ∈ s, (1 : ℝ) / ((p : ℝ) * (r : ℝ)) = (L.map (fun p ↦ (1 : ℝ) / ((p : ℝ) * (r : ℝ)))).sum := by
    have h₁ : L.toFinset = s := hL_toFinset
    have h₂ : L.Nodup := hL_nodup
    rw [← h₁]
    apply?
  -- since pj ≥ (j+1) * r,  then 1/(pj * r) ≤ 1/((j+1)*r) * r
  have h_main₃₂ : ∀ (l : List ℕ) (j : ℕ) (hj : j < l.length),
    (1 : ℝ) / (((L[j]' (Finset.mem_range.mp ‹j ∈ Finset.range L.length›)) : ℝ) * (r : ℝ)) ≤ (1 : ℝ) / ((( (j + 1 : ℕ) : ℝ) * (r : ℝ)) * (r : ℝ)) := by
    intro j hj
    have h_j_lt : j < L.length := Finset.mem_range.mp hj
    have h_lb : L[j] ≥ (j + 1) * r + 1 := lowerBound_of_p_in_P_r r (by linarith) h_Pfin j h_j_lt
    have h_pos1 : (0 : ℝ) < ((L[j] : ℝ) * (r : ℝ)) := by positivity
    have h_pos2 : (0 : ℝ) < ((( (j + 1 : ℕ) : ℝ) * (r : ℝ)) * (r : ℝ)) := by positivity
    have h_ineq1 : ((L[j] : ℝ) * (r : ℝ)) ≥ ((( (j + 1 : ℕ) : ℝ) * (r : ℝ)) * (r : ℝ)) := by
      have h₁ : (L[j] : ℝ) ≥ (((j + 1 : ℕ) : ℝ) * (r : ℝ) + 1) := by exact_mod_cast h_lb
      have h₂ : (L[j] : ℝ) ≥ (((j + 1 : ℕ) : ℝ) * (r : ℝ)) := by linarith
      have h₃ : ((L[j] : ℝ) * (r : ℝ)) ≥ ((( (j + 1 : ℕ) : ℝ) * (r : ℝ)) * (r : ℝ)) := by
        have h₄ : (r : ℝ) > 0 := by exact_mod_cast hr
        nlinarith
      exact h₃

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
