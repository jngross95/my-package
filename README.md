# my-package

https://github.com/ImperialCollegeLondon/M40001_lean/tree/master/src

https://github.com/kmill/LeanTeX/issues/3


python -m pip install --config-settings="--global-option=build_ext" `
                      --config-settings="--global-option=-IC:\Program Files\Graphviz\include" `
                      --config-settings="--global-option=-LC:\Program Files\Graphviz\lib" `
                      pygraphviz

                      

leanblueprint pdf

lake exe cache get
lake -R build
lake -R -Kenv=dev update
lake -R -Kenv=dev build
DOCGEN_SRC="github"&&lake -R -Kenv=dev build MyPackage:docs

https://github.com/alexkassil/natural_number_game_lean4.git







--------
example (P Q: Prop) : P ∧ Q → Q ∧ P := by

intro h
cases h
constructor
assumption
assumption
--------
example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by

apply λ x => h2 (h1 x)
-----------

example (P Q R: Prop) (h : P ∧ Q → R) : P → Q → R := by

repeat intro
apply h
constructor
repeat assumption 

------

example (P Q R: Prop) (h : P → Q → R) : P ∧ Q → R := by

intro 
apply h
apply a.left
apply a.right

------------
example (P Q R : Prop) (h : (P → Q) ∧ (P → R)) : P → Q ∧ R := by

intro
constructor
apply h.left
apply a
apply h.right
apply a
-------------

example (P Q : Prop) : Q → (P → Q) ∧ (¬P → Q) := by
intro
constructor
repeat {intro; assumption}

-----------   or   
example (O S : Prop)(s : S) : K ∨ S := by

exact or_inr s
----------
example (B C I : Prop)(h1 : C → B)(h2 : I → B)(h3 : C ∨ I) : B := by

have hh := or_elim h3 h1 h2
exact hh
---------------
example (C O : Prop)(h : C ∨ O) : O ∨ C := by
have x: C → O ∨ C := or_inr
have y: O → O ∨ C := or_inl
exact or_elim h x y 
-----------
example (C J R : Prop)(h1 : C → J)(h2 : C ∨ R) : J ∨ R := by
have x: J → J ∨ R := or_inl
have y: R → J ∨ R := or_inr
exact or_elim h2 (λc=> x (h1 c)) (λr=> y r) 

----
example (G H U : Prop)(h : G ∧ (H ∨ U)) : (G ∧ H) ∨ (G ∧ U) := by
have g := h.left


have f1:(H->(G ∧ H) ∨ (G ∧ U)) := λh:H => (or_inl (and_intro g h))

have f2:(U->(G ∧ H) ∨ (G ∧ U)) := λu:U => (or_inr (and_intro g u))

have z := or_elim h.right  f1 f2
exact z
---------
example (I K P : Prop)(h : K → P) : K ∨ I → I ∨ P := by
exact λ h2:(K ∨ I) => 
 
   or_elim h2 (λ k:K => or_inr (h k))  (λ i:I => or_inl i)

-----------------------
example (P Q R : Prop)(h : P ∨ Q ∧ R) : (P ∨ Q) ∧ (P ∨ R) := by
constructor
cases h
left
assumption
right
cases h_1
assumption
cases h
left 
assumption
cases h_1
right
assumption
----------------
example (P Q R : Prop)(h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
cases h
cases right
left
constructor
assumption
assumption
right
constructor
assumption
assumption

----------------
example (P Q R : Prop)(h : Q → R) : Q ∨ P → P ∨ R := by

intro
cases a
right
apply (h h_1)
left
apply h_1