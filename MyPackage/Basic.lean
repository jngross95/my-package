import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp


open Set
open Real


example : 120 + 100 = 220 :=  by
 norm_num

/--  Besispiellemma $ f(x)=xx $  -/
lemma add_self_eq_two_mul2 (a : ℝ) : a + a = 2 * a :=
calc
  a + a = 1 * a + 1 * a := by rw [one_mul]
     _ = (1 + 1) * a    := by rw [add_mul]
     _ = 2 * a          := by norm_num

/--Beispiel 2 -/
lemma zweite_lemma (x : ℝ) : x + 100 * x^2 + 120 * x^2 +1= 220 * x^2 +1 +x :=
by ring

/--  Beispiel 3  -/
lemma dritte_lemma  (a b : ℝ) : (2*a+b)^2 = 4*a^2+4*a*b+b^2 :=
by ring


lemma lemma5
 {R : Type*} [Field R]  (a b c d: R) (hb : b ≠ 0) (hd : d ≠ 0)  :
      (a / b) * (c / d) = (a*c)/(b*d) := by
field_simp [hb, hd]


example (x y z : ℝ) : x * y * z = y * (x * z) := by
  rw [mul_comm x y]
  rw [mul_assoc y x z]

lemma lemma6  : ((1: ℚ) / 321) * (1 / (3*1)) = (1*1)/(321*(3*1)) := by
  have n1: ¬(321=(0:ℚ)) := by norm_num
  have n2: ¬(3*1=(0:ℚ)) := by norm_num
  rw [ lemma5 (1:ℚ) 321 1 (3*1) n1 n2 ]
  --have h := lemma5 (1:ℚ) 321 1 (3*1) n1 n2
  --exact h
