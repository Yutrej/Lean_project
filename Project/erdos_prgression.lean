-- Authored by: YANG Ruijia, LIU Rongqin
-- 2026 3/30 01:18

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq

open Nat

def a : ℕ := 7629217
def m : ℕ := 11184810

variable {n : ℕ}


lemma a_1mod2 : a ≡ 1 [MOD 2] := by decide
lemma a_1mod3 : a ≡ 1 [MOD 3] := by decide
lemma a_2mod5 : a ≡ 2 [MOD 5] := by decide
lemma a_1mod7 : a ≡ 1 [MOD 7] := by decide
lemma a_11mod13 : a ≡ 11 [MOD 13] := by decide
lemma a_8mod17 : a ≡ 8 [MOD 17] := by decide
lemma a_121mod241 : a ≡ 121 [MOD 241] := by decide

lemma n_aMODm_implies_n_1MOD2 (h : n ≡ a [MOD m]) :
    n ≡ 1 [MOD 2] := by
  have hm : 2 ∣ m := by decide
  have : n ≡ a [MOD 2] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod2
lemma n_aMODm_implies_n_1MOD3 (h : n ≡ a [MOD m]) :
    n ≡ 1 [MOD 3] := by
  have hm : 3 ∣ m := by decide
  have : n ≡ a [MOD 3] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod3
lemma n_aMODm_implies_n_2MOD5 (h : n ≡ a [MOD m]) :
    n ≡ 2 [MOD 5] := by
  have hm : 5 ∣ m := by decide
  have : n ≡ a [MOD 5] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_2mod5
lemma n_aMODm_implies_n_1MOD7 (h : n ≡ a [MOD m]) :
    n ≡ 1 [MOD 7] := by
  have hm : 7 ∣ m := by decide
  have : n ≡ a [MOD 7] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod7
lemma n_aMODm_implies_n_11MOD13 (h : n ≡ a [MOD m]) :
    n ≡ 11 [MOD 13] := by
  have hm : 13 ∣ m := by decide
  have : n ≡ a [MOD 13] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_11mod13
lemma n_aMODm_implies_n_8MOD17 (h : n ≡ a [MOD m]) :
    n ≡ 8 [MOD 17] := by
  have hm : 17 ∣ m := by decide
  have : n ≡ a [MOD 17] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_8mod17
lemma n_aMODm_implies_n_121MOD241 (h : n ≡ a [MOD m]) :
    n ≡ 121 [MOD 241] := by
  have hm : 241 ∣ m := by decide
  have : n ≡ a [MOD 241] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_121mod241



lemma cover (k : ℕ) :
    k ≡ 0 [MOD 2] ∨ k ≡ 0 [MOD 3] ∨ k ≡ 1 [MOD 4] ∨
    k ≡ 3 [MOD 8] ∨ k ≡ 7 [MOD 12] ∨ k ≡ 23 [MOD 24] := by
  let r := k % 24
  have hk : k ≡ r [MOD 24] := by exact ModEq.symm (mod_modEq k 24)
  have hr : r < 24 := Nat.mod_lt k (by norm_num)
  interval_cases r
  · left -- 0 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    exact Nat.ModEq.of_dvd this hk
  · right; right; left -- 1 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    exact Nat.ModEq.of_dvd this hk
  · left -- 2 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 2 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 3 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 3 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 4 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 4 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; left -- 5 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    have : k ≡ 5 [MOD 4] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 6 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 6 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; right; left -- 7 mod 24 -> 7 mod 12
    have : 12 ∣ 24 := by decide
    have : k ≡ 7 [MOD 12] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 8 mod 24 -> 0 mod 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 8 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 9 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 9 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 10 mod 24 -> 0 omd 2
    have : 2 ∣ 24 := by decide
    have : k ≡ 10 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; left -- 11 mod 24 -> 3 mod 8
    have : 8 ∣ 24 := by decide
    have : k ≡ 11 [MOD 8] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 12
    have : 2 ∣ 24 := by decide
    have : k ≡ 12 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; left -- 13 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    have : k ≡ 13 [MOD 4] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 14
    have : 2 ∣ 24 := by decide
    have : k ≡ 14 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 15 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 15 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 16
    have : 2 ∣ 24 := by decide
    have : k ≡ 16 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; left -- 17 mod 24 -> 1 mod 4
    have : 4 ∣ 24 := by decide
    have : k ≡ 17 [MOD 4] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 18 mod 24 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 18 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; left -- 19 mod 24 -> 3 mod 8
    have : 8 ∣ 24 := by decide
    have : k ≡ 19 [MOD 8] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 20
    have : 2 ∣ 24 := by decide
    have : k ≡ 20 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; left -- 21 -> 0 mod 3
    have : 3 ∣ 24 := by decide
    have : k ≡ 21 [MOD 3] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · left -- 22
    have : 2 ∣ 24 := by decide
    have : k ≡ 22 [MOD 2] := by exact Nat.ModEq.of_dvd this hk
    exact ModEq.symm (ModEq.trans (id (ModEq.symm this)) rfl)
  · right; right; right; right; right
    apply hk



lemma branch_k_0mod2_forces_3mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 0 [MOD 2])
    (hrep : n = p + 2 ^ k) :
    3 ∣ p := by
  have : 2 ∣ k := by exact dvd_of_mod_eq_zero hk
  obtain ⟨t, ht⟩ := this
  have h_4power : 2 ^ k = 4 ^ t := by
    rw [ht]; rw [pow_mul]; norm_num
  have : 4 ≡ 1 [MOD 3] := by decide
  have h_2k : 4 ^ t ≡ 1 ^ t [MOD 3] := by exact ModEq.pow t this
  simp only [one_pow] at h_2k; rw [← h_4power] at h_2k
  have h_1mod3 : n ≡ 1 [MOD 3] := by exact n_aMODm_implies_n_1MOD3 hn
  rw [hrep] at h_1mod3
  have hp : p + 2 ^ k - 2 ^ k ≡ 1 - 1 [MOD 3] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact NeZero.one_le)
      h_1mod3
      h_2k
  have : p ≡ 0 [MOD 3] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_0mod3_forces_7mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 0 [MOD 3])
    (hrep : n = p + 2 ^ k) :
    7 ∣ p := by
  have : 3 ∣ k := by exact dvd_of_mod_eq_zero hk
  obtain ⟨t, ht⟩ := this
  have h_8power : 2 ^ k = 8 ^ t := by
    rw [ht]; rw [pow_mul]; norm_num
  have : 8 ≡ 1 [MOD 7] := by decide
  have h_2k : 8 ^ t ≡ 1 ^ t [MOD 7] := by exact ModEq.pow t this
  simp only [one_pow] at h_2k; rw [← h_8power] at h_2k
  have h_1mod7 : n ≡ 1 [MOD 7] := by exact n_aMODm_implies_n_1MOD7 hn
  rw [hrep] at h_1mod7
  have hp : p + 2 ^ k - 2 ^ k ≡ 1 - 1 [MOD 7] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact NeZero.one_le)
      h_1mod7
      h_2k
  have : p ≡ 0 [MOD 7] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_1mod4_forces_5mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 1 [MOD 4])
    (hrep : n = p + 2 ^ k) :
    5 ∣ p := by
  have : 1 ≡ k [MOD 4] := by exact ModEq.symm hk
  have k_pos : 1 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact one_lt_succ_succ (k + 2))
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 2 * 16 ^ t := by
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^4 = 16)]
  have : 16 ≡ 1 [MOD 5] := by decide
  have h_16t : 16 ^ t ≡ 1 ^ t [MOD 5] := by exact ModEq.pow t this
  simp only [one_pow] at h_16t;
  have h_2k : 2 * 16 ^ t ≡ 2 [MOD 5] := by exact ModEq.mul_left 2 h_16t
  rw [← h_k_by_t] at h_2k
  have h_2mod5 : n ≡ 2 [MOD 5] := by exact n_aMODm_implies_n_2MOD5 hn
  rw [hrep] at h_2mod5
  have hp : p + 2 ^ k - 2 ^ k ≡ 2 - 2 [MOD 5] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact AtLeastTwo.prop)
      h_2mod5
      h_2k
  have : p ≡ 0 [MOD 5] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_3mod8_forces_17mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 3 [MOD 8])
    (hrep : n = p + 2 ^ k) :
    17 ∣ p := by
  have : 3 ≡ k [MOD 8] := by exact ModEq.symm hk
  have k_pos : 3 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact Nat.lt_of_sub_eq_succ rfl)
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 8 * 256 ^ t := by
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^8 = 256)]
  have : 256 ≡ 1 [MOD 17] := by decide
  have h_256t : 256 ^ t ≡ 1 ^ t [MOD 17] := by exact ModEq.pow t this
  simp only [one_pow] at h_256t;
  have h_2k : 8 * 256 ^ t ≡ 8 [MOD 17] := by exact ModEq.mul_left 8 h_256t
  rw [← h_k_by_t] at h_2k
  have h_8mod17 : n ≡ 8 [MOD 17] := by exact n_aMODm_implies_n_8MOD17 hn
  rw [hrep] at h_8mod17
  have hp : p + 2 ^ k - 2 ^ k ≡ 8 - 8 [MOD 17] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact le_of_ble_eq_true rfl)
      h_8mod17
      h_2k
  have : p ≡ 0 [MOD 17] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_7mod12_forces_13mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 7 [MOD 12])
    (hrep : n = p + 2 ^ k) :
    13 ∣ p := by
  have : 7 ≡ k [MOD 12] := by exact ModEq.symm hk
  have k_pos : 7 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact Nat.lt_of_sub_eq_succ rfl)
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 128 * 4096 ^ t := by
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^12 = 4096)]
  have : 4096 ≡ 1 [MOD 13] := by decide
  have h_4096t : 4096 ^ t ≡ 1 ^ t [MOD 13] := by exact ModEq.pow t this
  simp only [one_pow] at h_4096t;
  have h_2k : 128 * 4096 ^ t ≡ 128 [MOD 13] := by exact ModEq.mul_left 128 h_4096t
  rw [← h_k_by_t] at h_2k
  have h_11mod13 : n ≡ 11 [MOD 13] := by exact n_aMODm_implies_n_11MOD13 hn
  rw [hrep] at h_11mod13
  have hp : p + 2 ^ k - 2 ^ k ≡ 11 - 11 [MOD 13] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact le_of_ble_eq_true rfl)
      h_11mod13
      h_2k
  have : p ≡ 0 [MOD 13] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this

lemma branch_k_23mod24_forces_241mid_p (k : ℕ) (p : ℕ) (hn : n ≡ a [MOD m])
    (hk : k ≡ 23 [MOD 24])
    (hrep : n = p + 2 ^ k) :
    241 ∣ p := by
  have : 23 ≡ k [MOD 24] := by exact ModEq.symm hk
  have k_pos : 23 ≤ k := by
    exact ModEq.le_of_lt_add this (by exact Nat.lt_of_sub_eq_succ rfl)
  obtain ⟨t, ht⟩ := (modEq_iff_exists_eq_add k_pos).mp this
  have h_k_by_t : 2 ^ k = 8388608 * 16777216 ^ t := by -- 2^23=8388608, 2^24=16777216
    rw [ht]; simp [pow_add, pow_mul, (by norm_num : 2^24 = 16777216)]
  have : 16777216 ≡ 1 [MOD 241] := by decide
  have h_16777216t : 16777216 ^ t ≡ 1 ^ t [MOD 241] := by exact ModEq.pow t this
  simp only [one_pow] at h_16777216t;
  have h_2k : 8388608 * 16777216 ^ t ≡ 8388608 [MOD 241] := by
    exact ModEq.mul_left 8388608 h_16777216t
  rw [← h_k_by_t] at h_2k
  have h_121mod241 : n ≡ 121 [MOD 241] := by exact n_aMODm_implies_n_121MOD241 hn
  rw [hrep] at h_121mod241
  have hp : p + 2 ^ k - 2 ^ k ≡ 121 - 121 [MOD 241] := by
    exact ModEq.sub
      (by exact Nat.le_add_left (2 ^ k) p)
      (by exact le_of_ble_eq_true rfl)
      h_121mod241
      h_2k
  have : p ≡ 0 [MOD 241] := by simp only [add_tsub_cancel_right, tsub_self] at hp; exact hp
  exact dvd_of_mod_eq_zero this



lemma p_eq_q {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hdvd : q ∣ p) : p = q := by
  have q_ne_1 : q ≠ 1 := hq.ne_one
  exact (Nat.Prime.dvd_iff_eq hp q_ne_1).mp hdvd

lemma p_values {p : ℕ} (hp : p.Prime) (hdvd : 3 ∣ p ∨ 5 ∣ p ∨ 7 ∣ p ∨ 13 ∣ p ∨ 17 ∣ p ∨ 241 ∣ p) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 241 := by
    rcases hdvd with h3|h5|h7|h13|h17|h241
    · left; exact p_eq_q hp (by exact prime_three) h3
    · right; left; exact p_eq_q hp (by exact prime_five) h5
    · right; right; left; exact p_eq_q hp (by exact prime_seven) h7
    · right; right; right; left; exact p_eq_q hp (by norm_num) h13
    · right; right; right; right; left; exact p_eq_q hp (by norm_num) h17
    · right; right; right; right; right; exact p_eq_q hp (by norm_num) h241



lemma pow2_mod_periodic (k p d : ℕ) (h : 2 ^ d ≡ 1 [MOD p]) (hd : 0 < d) :
  2^k ≡ 2^(k % d) [MOD p] := by
  let r := k % d; let q := k / d
  have hr : r < d := Nat.mod_lt k hd
  have hk : k = d * q + r := (Nat.div_add_mod k d).symm
  rw [hk, pow_add, pow_mul]
  --(2 ^ d) ^ q * 2 ^ r ≡ 2 ^ ((d * q + r) % d) [MOD p]
  have hq : (2^d)^q ≡ 1^q [MOD p]:= Nat.ModEq.pow q h
  rw [one_pow] at hq
  have h_final := Nat.ModEq.mul hq (Nat.ModEq.refl (2^r))
  rw [one_mul] at h_final
  have : (d * q + r) % d = r := by
    rw [Nat.add_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hr
  rw [this]
  exact h_final

lemma pow2_mod7_cases (k : ℕ) :
      2^k ≡ 1 [MOD 7] ∨ 2^k ≡ 2 [MOD 7] ∨ 2^k ≡ 4 [MOD 7] := by
    have h_periodic := pow2_mod_periodic k 7 3 (by rfl) (by norm_num)
    let r := k % 3
    have hrep : r = k % 3 := by exact?
    have hr : r < 3 := Nat.mod_lt k (by norm_num)
    interval_cases r
    · left
      have : 2 ^ k ≡ 2 ^ 0 [MOD 7] := by rw [← hrep] at h_periodic; assumption
      exact?
    · right; left
      have : 2 ^ k ≡ 2 ^ 1 [MOD 7] := by rw [← hrep] at h_periodic; assumption
      exact?
    · right; right
      have : 2 ^ k ≡ 2 ^ 2 [MOD 7] := by rw [← hrep] at h_periodic; assumption
      exact?



lemma pow2_mod3_cases (k : ℕ) :
      2^k ≡ 1 [MOD 3] ∨ 2^k ≡ 2 [MOD 3] := by
  have h_periodic := pow2_mod_periodic k 3 2 (by norm_num) (by norm_num [Nat.ModEq])
  let r := k % 2
  have hrep : r = k % 2 := by exact?
  have hr : r < 2 := Nat.mod_lt k (by norm_num)
  interval_cases r
  · left
    have : 2 ^ k ≡ 2 ^ 0 [MOD 3] := by rw [← hrep] at h_periodic; assumption
    exact?
  · right
    have : 2 ^ k ≡ 2 ^ 1 [MOD 3] := by rw [← hrep] at h_periodic; assumption
    exact?

lemma values_exclusion (n k p : ℕ)
    (h_rep : n = p + 2 ^ k)
    (hn7 : n ≡ 1 [MOD 7])
    (hn3 : n ≡ 1 [MOD 3])
    (hp : p.Prime)
    (hdvd : 3 ∣ p ∨ 5 ∣ p ∨ 7 ∣ p ∨ 13 ∣ p ∨ 17 ∣ p ∨ 241 ∣ p) :
    False := by
  have hp_cases := p_values hp hdvd
  rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · -- p = 3
    have h : 1 ≡ 3 + 2^k [MOD 7] := by
      have h_symm := hn7.symm
      rw [h_rep] at h_symm
      exact h_symm
    rcases pow2_mod7_cases k with hk|hk|hk <;>
    (have h_c := h.trans (Nat.ModEq.add (ModEq.refl 3) hk)
     unfold Nat.ModEq at h_c; norm_num at h_c)
  · -- p = 5
    have h : 1 ≡ 5 + 2^k [MOD 7] := by
      have h_symm := hn7.symm
      rw [h_rep] at h_symm
      exact h_symm
    rcases pow2_mod7_cases k with hk|hk|hk <;>
    (have h_c := h.trans (Nat.ModEq.add (Nat.ModEq.refl 5) hk)
     unfold Nat.ModEq at h_c; norm_num at h_c)
  · -- p = 7
    have h : 1 ≡ 7 + 2^k [MOD 3] := by
      have h_symm := hn3.symm
      rw [h_rep] at h_symm
      exact h_symm
    rcases pow2_mod3_cases k with hk|hk <;>
    (have h_c := h.trans (Nat.ModEq.add (Nat.ModEq.refl 7) hk)
     unfold Nat.ModEq at h_c; norm_num at h_c)
  · -- p = 13
    have h : 1 ≡ 13 + 2^k [MOD 3] := by
      have h_symm := hn3.symm
      rw [h_rep] at h_symm
      exact h_symm
    rcases pow2_mod3_cases k with hk|hk <;>
    (have h_c := h.trans (Nat.ModEq.add (Nat.ModEq.refl 13) hk)
     unfold Nat.ModEq at h_c; norm_num at h_c)
  · -- p = 17
    have h : 1 ≡ 17 + 2^k [MOD 7] := by
      have h_symm := hn7.symm
      rw [h_rep] at h_symm
      exact h_symm
    rcases pow2_mod7_cases k with hk|hk|hk <;>
    (have h_c := h.trans (Nat.ModEq.add (Nat.ModEq.refl 17) hk)
     unfold Nat.ModEq at h_c; norm_num at h_c)
  · -- p = 241
    have h : 1 ≡ 241 + 2^k [MOD 7] := by
      have h_symm := hn7.symm
      rw [h_rep] at h_symm
      exact h_symm
    rcases pow2_mod7_cases k with hk|hk|hk <;>
    (have h_c := h.trans (Nat.ModEq.add (Nat.ModEq.refl 241) hk)
     unfold Nat.ModEq at h_c; norm_num at h_c)



theorem exists_progression_no_prime_add_pow_two (hn : n ≡ a [MOD m]) :
    ∀ (p k : ℕ), p.Prime → n ≠ p + 2^k := by
  intro p k hp h_rep
  have hn7 : n ≡ 1 [MOD 7] := by exact n_aMODm_implies_n_1MOD7 hn
  have hn3 : n ≡ 1 [MOD 3] := by exact n_aMODm_implies_n_1MOD3 hn
  rcases cover k with hk2 | hk3 | hk4 | hk8 | hk12 | hk24
  · -- k ≡ 0 mod 2
    have h_3mid_p : 3 ∣ p := by exact branch_k_0mod2_forces_3mid_p k p hn hk2 h_rep
    exact values_exclusion n k p h_rep hn7 hn3 hp (by tauto)
  · -- k ≡ 0 mod 3
    have h_7mid_p : 7 ∣ p := by exact branch_k_0mod3_forces_7mid_p k p hn hk3 h_rep
    exact values_exclusion n k p h_rep hn7 hn3 hp (by tauto)
  · -- k ≡ 1 mod 4
    have h_5mid_p : 5 ∣ p := by exact branch_k_1mod4_forces_5mid_p k p hn hk4 h_rep
    exact values_exclusion n k p h_rep hn7 hn3 hp (by tauto)
  · -- k ≡ 3 mod 8
    have h_17mid_p : 17 ∣ p := by exact branch_k_3mod8_forces_17mid_p k p hn hk8 h_rep
    exact values_exclusion n k p h_rep hn7 hn3 hp (by tauto)
  · -- k ≡ 7 mod 12
    have h_13mid_p : 13 ∣ p := by exact branch_k_7mod12_forces_13mid_p k p hn hk12 h_rep
    exact values_exclusion n k p h_rep hn7 hn3 hp (by tauto)
  · -- k ≡ 23 mod 24
    have h_241mid_p : 241 ∣ p := by exact branch_k_23mod24_forces_241mid_p k p hn hk24 h_rep
    exact values_exclusion n k p h_rep hn7 hn3 hp (by tauto)
