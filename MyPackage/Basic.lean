import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Init.Algebra.Classes
import Mathlib.Algebra.Group.Basic

open Set


open Real

set_option diagnostics true
set_option diagnostics.threshold 4

example : 120 + 100 = 220 :=
by norm_num

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
