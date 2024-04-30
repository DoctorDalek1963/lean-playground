import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Divisors

open Nat

-- There are infinitely many prime numbers.
theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N

  -- Let M = N! + 1 and p be the smallest prime factor of M
  let M := N ! + 1
  let p := minFac M

  -- We will use this p as the p that must exist for this N
  use p

  -- p is prime
  have p_prime : Nat.Prime p := by
    -- M ≠ 1 because N! > 0 => N! + 1 > 1
    have m_ne_1 : M ≠ 1 := by
      have : N ! > 0 := by apply factorial_pos
      linarith

    -- So long as M ≠ 1, minFac M is prime, ∴ p is prime
    apply minFac_prime m_ne_1

  -- We need to prove that p ≥ N ∧ p is prime, so we will prove them separately
  apply And.intro

  -- p ≥ N
  {
    -- Assume p < N
    apply by_contradiction
    intro not_p_ge_N

    -- p ∣ N!
    -- We know this is true because p < N, and all numbers < N will divide N!
    have H1 : p ∣ N ! := by
      apply dvd_factorial
      apply Prime.pos
      exact p_prime
      apply le_of_not_ge
      exact not_p_ge_N

    -- p ∣ (N! + 1) ↔ p ∣ M
    -- We know this is true because p is defined as the smallest prime factor of M
    have H2 : p ∣ N ! + 1 := by apply minFac_dvd

    -- p ∣ 1
    -- a ∣ b ∧ a ∣ c ↔ a ∣ b + c
    -- p ∣ N! ∧ p ∣ N! + 1, therefore p ∣ 1
    have H3 : p ∣ 1 := by exact (Nat.dvd_add_iff_right H1).mpr H2

    -- ¬p ∣ 1
    have H4 : ¬p ∣ 1 := by exact Nat.Prime.not_dvd_one p_prime

    -- It cannot be the case that p ∣ 1 ∧ ¬p ∣ 1, so we have reached a contradiction
    -- Therefore, ¬p ≥ N must be false, so we have shown that p ≥ N
    contradiction
  }

  -- p is prime
  exact p_prime
