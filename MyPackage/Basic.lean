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


example (x y z : ℝ) : x * y * z = y * (x * z) := by
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


example (A B : Prop) (h: A ∨ B) : B ∨ A := by
  obtain a | b := h
  exact  (Or.inr a)
  exact  (Or.inl b)

example (A B : Prop) (h: A ∨ B) : B ∨ A := by
  obtain a | b := h
  right
  exact a
  left
  exact b

example (h : C ∨ O) : O ∨ C := by
  cases h with
  | inl hc => -- Fall C
    right
    exact hc
  | inr ho => -- Fall O
    left
    exact ho




--example (G H U : Prop)(h : G ∨ H ∧ U) : (G ∨ H) ∧ (G ∨ U) := by
--   have h2: (G ∨ (H ∧ U)) := h


---- NOT NOT p
example (P : Prop)(p : P) : ¬¬P := by
have f: (P->False) -> False :=
  λ f:P->False => (f p)
exact f

--  ((p->false) → false)
example (L : Prop) : ¬(L ∧ ¬L) := by
have x:  (L ∧ (L -> False)) -> False :=
  λ h => (h.right h.left)
exact x

-----------

example (B S : Prop)(h1 : B → S)(h2 : S->False) : B->False := by
exact λ b:B => h2 (h1 b)

-----------

example (A : Prop) (h: A → (A->False)) : A->False := by
exact λ a:A => (h a) a

-----------

example (B C : Prop) (h: (B → C)->False) : C->False := by
exact λ c:C => (h λ _:B=>c)

-----------

example (C S : Prop) (s: S) : ((S->False) ∧ C)->False := by
exact λ and_term:((S->False) ∧ C) =>   (and_term.left s)

-------

example (A P : Prop) (h : P → (A->False)) : (P ∧ A)->False := by
exact λ pa: P ∧ A => ((h pa.left) pa.right)

---------

example (A P : Prop) (h: (P ∧ A) → False) : P → (A → False) := by
exact λ (p:P) (a:A) => h ⟨p , a⟩

-------
example : True := by
constructor
example : True := by
exact True.intro

example (h: False) : False := by
apply h

example (h: False) : True := by
constructor

-----------
example (P : Prop) (h: P) : P := by
apply h

----------  AND
example (P Q : Prop) (p: P) (q:Q) : P ∧ Q:= by
constructor
apply p
apply q

example (P Q : Prop) (h: P ∧ Q) :  Q := by
let q := h.right
apply q









--------
--example (A : Prop)(h : ((A->False)->False)->False) : A -> False := by
--exact λ a:A => (h λ         )

--example (A : Prop)(h : ¬¬¬A) : ¬A := by
--let thm (P : Prop)(p : P) : ¬¬P :=
--  let f: (P->False) -> False :=  λ f:P->False => (f p)
--  f

---
example {A : Prop} (h : ¬¬¬A) : ¬A := by
  exact fun a : A => h (fun na : ¬A => na a)

--
example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
 exact   fun (nb : ¬ B) =>
    h (fun (b : B) => False.elim (nb b))


example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
intro
apply h
intro
contradiction

--example (B P : Prop) (h : B ↔ ¬P) : (B → ¬P) ∧ (¬P → B) := by
--have x :=  iff_mp h
--have y :=  iff_mpr h
--exact And.intro x y


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

--def instantiateMVars [Monad m] [MonadMCtx m] (e : Expr) : m Expr := do
/- def ff (e:term)  := do
    Elab.Command.runTermElabM fun _ => do
      let e1 ← Elab.Term.elabTerm e none

      Elab.Term.synthesizeSyntheticMVarsNoPostponing

      let e2 ← instantiateMVars e1
      let res ← run_latexPP e2 {}
      return  ""
    --let res := " ".intercalate (res |>.split Char.isWhitespace |>.filter (not ·.isEmpty))
 -/
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



--#eval printTheoremsOfCurrentModule
