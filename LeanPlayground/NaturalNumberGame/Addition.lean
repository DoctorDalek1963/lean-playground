import LeanPlayground.NaturalNumberGame.Tutorial

open Nat

-- Level 1: 0 + n = n with induction
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n

  case zero =>
  {
    rw [add_zero]
    -- rfl
  }

  case succ n n_ih =>
  {
    rw [add_succ]
    rw [n_ih]
    -- rfl
  }

-- Level 2
theorem succ_add (a b : Nat) : succ a + b = succ (a + b) := by
  induction b

  case zero =>
  {
    rw [add_zero, add_zero]
    -- rfl
  }

  case succ n n_ih =>
  {
    sorry
  }
