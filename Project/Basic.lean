

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq

open Nat

def a : ℕ := 7629217
def m : ℕ := 11184810


lemma a_1mod2 : a ≡ 1 [MOD 2] := by decide
lemma a_1mod3 : a ≡ 1 [MOD 3] := by decide
lemma a_2mod5 : a ≡ 2 [MOD 5] := by decide
lemma a_1mod7 : a ≡ 1 [MOD 7] := by decide
lemma a_11mod13 : a ≡ 11 [MOD 13] := by decide
lemma a_8mod17 : a ≡ 8 [MOD 17] := by decide
lemma a_121mod241 : a ≡ 121 [MOD 241] := by decide

lemma n_aMODm_implies_n_aMOD2 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 1 [MOD 2] := by
  have hm : 2 ∣ m := by decide
  have : n ≡ a [MOD 2] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod2
lemma n_aMODm_implies_n_aMOD3 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 1 [MOD 3] := by
  have hm : 3 ∣ m := by decide
  have : n ≡ a [MOD 3] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod3
lemma n_aMODm_implies_n_aMOD5 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 2 [MOD 5] := by
  have hm : 5 ∣ m := by decide
  have : n ≡ a [MOD 5] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_2mod5
lemma n_aMODm_implies_n_aMOD7 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 1 [MOD 7] := by
  have hm : 7 ∣ m := by decide
  have : n ≡ a [MOD 7] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_1mod7
lemma n_aMODm_implies_n_aMOD13 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 11 [MOD 13] := by
  have hm : 13 ∣ m := by decide
  have : n ≡ a [MOD 13] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_11mod13
lemma n_aMODm_implies_n_aMOD17 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 8 [MOD 17] := by
  have hm : 17 ∣ m := by decide
  have : n ≡ a [MOD 17] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_8mod17
lemma n_aMODm_implies_n_aMOD241 (n : ℕ) (h : n ≡ a [MOD m]) : n ≡ 121 [MOD 241] := by
  have hm : 241 ∣ m := by decide
  have : n ≡ a [MOD 241] := by exact Nat.ModEq.of_dvd hm h
  exact ModEq.trans this a_121mod241


lemma cover (k : ℕ) :
    k ≡ 0 [MOD 2] ∨ k ≡ 0 [MOD 3] ∨ k ≡ 1 [MOD 4] ∨ k ≡ 3 [MOD 8] ∨ k ≡ 7 [MOD 12] ∨ k ≡ 23 [MOD 24]
    := by
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



lemma




theorem exists_progression_no_prime_add_pow_two :
    ∀ n : ℕ, n ≡ a [MOD m] → ¬ ∃ (p k : ℕ), p.Prime ∧ n = p + 2^k := by
  sorry
