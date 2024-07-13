# my-package


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
