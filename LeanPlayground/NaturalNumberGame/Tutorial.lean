import Mathlib.Tactic.NthRewrite

open Nat

-- Level 1: The `rfl` tactic can prove reflexivity.
-- It's worth noting that my version of Lean seems to not require `rfl` at the
-- end of longer proofs, so it won't be used again.
example (x q : Nat) : 37 * x + q = 37 * x + q := by rfl

-- Level 2: The `rw` tactic can be used to rewrite one thing in terms of another.
example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by rw [h]

-- Just define some natural numbers
axiom one_eq_succ_zero : 1 = succ 0
axiom two_eq_succ_one : 2 = succ 1
axiom three_eq_succ_two : 3 = succ 2
axiom four_eq_succ_three : 4 = succ 3

-- Level 3: 2 is the number after the number after 0.
example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]
  -- rfl

-- Level 4: 2 is the number after the number after 0 (but now rewriting the other way).
example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero]
  -- rw [← two_eq_succ_one]
  -- rfl

axiom add_zero (a : Nat) : a + 0 = a

-- Level 5: Adding zero does nothing and doesn't affect surrounding additions.
example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [add_zero]
  -- rfl

-- Level 6: Same as level 5 but by rewriting (c + 0) first.
example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c]
  rw [add_zero b]
  -- rfl

-- axiom add_succ (x d : Nat) : x + succ d = succ (x + d)

-- Level 7: Define addition.
theorem succ_eq_add_one (n : Nat) : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  -- rw [add_succ, add_zero]
  -- rfl

-- Level 8: 2 + 2 = 4.
example : (2 : Nat) + 2 = 4 := by
  rw [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  -- rw [add_succ, add_succ, add_zero]
  -- rfl

-- This version of the level 8 example was given by the game and uses nth_rewrite from mathlib
example : (2 : Nat) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [add_succ]
  -- rw [one_eq_succ_zero]
  -- rw [add_succ, add_zero]
  -- rw [← three_eq_succ_two, ← four_eq_succ_three]
  -- rfl
