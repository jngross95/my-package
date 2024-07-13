import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Even
import Paperproof
import LeanTeX
import Lean

open Lean Meta

open Set
open Real

namespace MyPackage


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


theorem coma_ssoc (x y z : ℝ) : (x * y) * z = y * (x * z) := by
  rw [mul_comm x y]
  rw [mul_assoc y x z]


theorem lemma6  : ((1: ℚ) / 321) * (1 / (3*1)) = (1*1)/(321*(3*1)) := by
  have n1: ¬(321=(0:ℚ)) := by norm_num
  have n2: ¬(3*1=(0:ℚ)) := by norm_num
  apply  lemma5 (1:ℚ) 321 1 (3*1) n1 n2
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

-- hallo

--example (n k : ℕ) (h : n = 2 * k) : Even n := by
  --apply?
  --apply Nat.even_of_exists_two_mul,
  --use k,
  --exact h,


/-- info: \forall \alpha : \mathbf{Type},\ \forall \beta : \mathbf{Type},\ \forall f : \alpha \to \beta,\ \forall x : \alpha,\ \forall y : \alpha,\ f(x) = f(y) \implies x = y -/
#guard_msgs in #latex (α β : Type) → (f : α → β) → ∀ {x y : α}, f x = f y → x = y

-- Hilfsfunktion zum Überprüfen, ob eine Deklaration ein Theorem ist
def isTheorem (constInfo : ConstantInfo) : Bool :=
  match constInfo.value? with
  | some _ => true
  | none   => false
-- Hilfsfunktion zum Überprüfen, ob ein Name im aktuellen Modul ist
def isInCurrentModule (name : Name) (currModule : Name) : Bool :=
  --true
  name.getPrefix == currModule


def printTheoremsOfCurrentModule : MetaM Unit := do
  -- Holen Sie sich die aktuelle Umgebung
  let env ← getEnv
  -- Holen Sie sich das aktuelle Modul
  let currModule := `MyPackage
  --IO.println s!"!!currModule!! {currModule.lastComponentAsString}"
  -- Iterieren Sie durch alle Deklarationen in der Umgebung
  for decl in env.constants.toList do
    let (name, constantInfo) := decl
    -- Überprüfen Sie, ob die Deklaration im aktuellen Modul ist und ein Theorem ist
    if isTheorem constantInfo && isInCurrentModule name currModule then
      let type ← inferType (mkConst name (constantInfo.levelParams.map mkLevelParam))



      let fmtType ← PrettyPrinter.ppExpr type
      IO.println s!"!Theorem! {name} : {fmtType}"



#eval printTheoremsOfCurrentModule
