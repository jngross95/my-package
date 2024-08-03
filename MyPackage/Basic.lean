import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Even
import Paperproof
import LeanTeX
import Lean
import Mathlib.Order.RelClasses
import Mathlib.Init.Algebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Init.Data.Int.Basic

open Lean Meta
open Set
open Real

--namespace MyPackage


example : 120 + 100 = 220 :=  by
 norm_num


/--Beispiel 2 -/
theorem zweite_lemma (x : ℝ) : x + 100 * x^2 + 120 * x^2 +1= 220 * x^2 +1 +x :=
by ring

/--  Beispiel 3  -/
theorem dritte_lemma  (a b : ℝ) : (2*a+b)^2 = 4*a^2+4*a*b+b^2 :=
by ring

/--
das soll da erscheinen3!!
$$
\frac{a}{c} \cdot \frac{b}{d} = \frac{a \cdot b}{c \cdot d}
$$
-/
theorem frac_mul
 {R : Type*} [Field R]  (a b c d: R) (hb : b ≠ 0) (hd : d ≠ 0)  :
      (a / b) * (c / d) = (a*c) / (b*d) := by
field_simp [hb, hd]


example (x y z : ℝ) : x * y * z = y * (x * z) := by
  rw [mul_comm x y]
  rw [mul_assoc y x z]

theorem lemma6  : ((1: ℚ) / 321) * (1 / (3*1)) = (1*1)/(321*(3*1)) := by
  have n1: ¬(321=(0:ℚ)) := by norm_num
  have n2: ¬(3*1=(0:ℚ)) := by norm_num
  apply  frac_mul (1:ℚ) 321 1 (3*1) n1 n2
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


------- True / False
example : True := by
constructor
example : True := by
exact True.intro

example (h: False) : False := by
apply h

example (h: False) : True := by
constructor


----------  AND
example (P Q : Prop) (p: P) (q:Q) : P ∧ Q:= by
constructor
apply p
apply q

example (P Q : Prop) (h: P ∧ Q) :  Q := by
obtain ⟨_, h2⟩ := h
apply h2

----------  Or
example (P Q : Prop)  (h: Q) :  P ∨ Q := by
right
apply h

example (P Q : Prop) (h0: ¬P) (h: P ∨ Q) :  Q := by
obtain h1|h2 := h
contradiction
apply h2

----------  implies -->

example (P Q R : Prop)  (h1: P → R) (h2: R → Q):  P → Q := by
intro h
exact h2 (h1 h)

example (P Q: Prop)  (h0: P) (h1: P → Q) :  Q := by
apply h1
exact h0

----------  not

example (P Q: Prop)  (h0: P → False) :  ¬P := by
intro h
apply (h0 h)


example (P Q: Prop)  (h: ¬P) :  P -> False := by
apply h

------------- if and only if  ↔
example (P Q : Prop)   (h1: P → Q)  (h2:Q → P) : P ↔ Q:= by
constructor
apply h1
apply h2

example (P Q : Prop)  (h: P ↔ Q) : (P → Q) ∧ (Q → P) := by
obtain ⟨h1, h2⟩ := h
constructor
apply h1
apply h2


---------------  exists /forall
example (P: Nat→Prop) (h: (P 12))  : ∃ (x:Nat) , (P x)  := by
use 12

example (P Q: Nat→Prop) (h1: ∃ (x:Nat) , (P x))  (h2: ∀x: Nat, Q x = P x)   : ∃ (x:Nat) , (Q x)  := by
obtain ⟨y, hx⟩ := h1
use y
specialize  h2 y
rewrite  [h2]
apply hx



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



def gcd (m n : Nat) : Nat :=
  if m = 0 then
    n
  else
    gcd (n % m) m
  termination_by m
  decreasing_by
    simp_wf;
    apply Nat.mod_lt
    apply Nat.zero_lt_of_ne_zero;
    assumption

/- def GCD
  (p : ℕ × ℕ) (g : ∀ q, q < p → ℕ) : ℕ :=
  let m := p.1
  let n := p.2

  if h:m=0 then
    n
  else
    have hh: (n % m) < m := by
        apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _);
        assumption
    have predProof:  ((n % m), m) < (m,n) := by
      sorry
    (g ((n % m) , m)) predProof


def gcd' : ℕ × ℕ -> ℕ :=
  WellFounded.fix


    (λ (p : ℕ × ℕ) (g : ∀ q, q < p → ℕ) =>
     (GCD p g)


      )


def gcd2 (m n : ℕ) : ℕ := gcd' (m, n)

#eval gcd2 48 18 -- 6 -/


--#eval gcd 65 5


--#eval printTheoremsOfCurrentModule

-- Beispieltheorem, das zeigt, dass die Koerzension korrekt ist
theorem coe_nat_to_int (n : Units ℝ) : (n : ℝ) = n := by
  rfl


theorem th1  (x: (Units ℝ)) : (x * 1) = x := by
  let g:Monoid  (Units ℝ) := inferInstance
  let xx := g.mul_one x
  exact xx



lemma my_pow_add {G: Type*} [Monoid G]
              (a : G) (m n : ℕ): a ^ (m + n) = a ^ m * a ^ n := by
  exact pow_add a m n

theorem my_zpow_add {G: Type*} [GroupWithZero G] (a : G) (m n : ℤ) (h: a ≠ 0): a ^ (m + n) = a ^ m * a ^ n := by
  exact zpow_add₀ h m n

--lemma zpow_add' {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
--    a ^ (m + n) = a ^ m * a ^ n := by

theorem my_zpow_add3 {G: Type*} [GroupWithZero G] (a : G) (m n : ℤ) (h: (m<0 ∨ n<0) -> a ≠ 0): a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hhh: a ≠ 0
  · exact zpow_add₀ hhh m n
  · have x := (not_imp_not.mpr h) hhh
    simp at x
    have _: m+n >= 0 := by
      exact add_nonneg x.left x.right
    simp at hhh
    by_cases mhhh: m=0 ∧ n=0
    · rw [zpow_add' (Or.inr (Or.inr mhhh))]
    · simp [not_and_or] at mhhh
      by_cases hhhh: m=0
      · simp [hhhh]
      · simp at hhhh
        have k:0 ≠ m := Ne.symm hhhh
        have k:m > 0 := lt_of_le_of_ne x.left k
        apply zpow_add'
        right
        left
        linarith


theorem r_pow_add {x : ℝ} (hx : x>0) (a b : ℝ) : x^(a + b) = x^a * x^b :=
  rpow_add hx a b
