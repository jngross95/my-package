import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Paperproof

open Set
open Real


example : 120 + 100 = 220 :=  by
 norm_num


/--Beispiel 2 -/
theorem zweite_lemma (x : ℝ) : x + 100 * x^2 + 120 * x^2 +1= 220 * x^2 +1 +x :=
by ring

/--  Beispiel 3  -/
theorem dritte_lemma  (a b : ℝ) : (2*a+b)^2 = 4*a^2+4*a*b+b^2 :=
by ring


theorem lemma5
 {R : Type*} [Field R]  (a b c d: R) (hb : b ≠ 0) (hd : d ≠ 0)  :
      (a / b) * (c / d) = (a*c) / (b*d) := by
field_simp [hb, hd]


example (x y z : ℝ) : x * y * z = y * (x * z) := by
  rw [mul_comm x y]
  rw [mul_assoc y x z]

theorem lemma6  : ((1: ℚ) / 321) * (1 / (3*1)) = (1*1)/(321*(3*1)) := by
  have n1: ¬(321=(0:ℚ)) := by norm_num
  have n2: ¬(3*1=(0:ℚ)) := by norm_num
  rw [ lemma5 (1:ℚ) 321 1 (3*1) n1 n2 ]
  --have h := lemma5 (1:ℚ) 321 1 (3*1) n1 n2
  --exact h


example (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro l r =>
  constructor
  assumption
  assumption


example (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro h
  let ⟨left, right⟩ := h
  constructor
  apply right
  apply left

--#search hallo

--example (n k : ℕ) (h : n = 2 * k) : even n := by
--  apply Nat.even_of_exists_two_mul,
--  use k,
--  exact h,
