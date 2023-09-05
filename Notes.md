* ## **Functions**

  * **#****check** thing -- gives type
  * **def** name : type := sorry -- define thing
  * **#****print**
  * **#lint** -- find errors
  * **theorem** name : proposition := proof (same as def, but use for theorems)
  * **rw** lem assumptions -- use a lemma to rewrite proof state
    * rw [p1,p2,...] for multiple lemmas
    * rw prop at hypothesis -- change assumptions
  * **\l** lemma -- reverse direction of lemma
  * **rw?** -- gives rw suggestions.
  * **#synth **-- Find definition
  * **#eval** equation -- calculate!
  * **simp** -- search entire library for simplification things. 
    * **simp only** -- only use named lemmas.
    * **simp?** -- suggest things to simp only.
  * **have** name - prop := proof -- mini proof, add to context. Or mini definition.
  * Defining functions:
    * def fun: type \r type
    * | 0=>1
    * | (n+1)=>(n+1) * fun
  * **calc** prop := by proof _ = ...
  * **intro ** x. For a function, initiate an element of the domain.
  * **specialize **prop x. If you have a forall statement, apply it to x.

  ## Types

  * **Prop**: Statements like 2+2=4, 2+2=5, 1<3, Irrational(pi)
  * **p ** (of type Prop): a proof of p.
  * type \r type -- a function

  ## Tactics

  * **refl**: (x=x)
  * **trivial**: (True)
  * **linarith**: linear arithmetic.
  * **Nat.add_comm**: a+b=b+a
  * **induction'** n with n h (**induction** in l4)
  * **apply**: apply a fact to split goal. Fx apply mul_pos "mul of two positives is positive" to change goal to showing both terms are positive
  * **assumption**: searches for assumptions
  * **simp only [defs] (at *)** expand definitons (optinally everywhere)
  * **rcases h with <h_1,h_2>** if h is of type A and B, make instances of type A and B respectively.
  * **r cases h with (a|b)** same but for or situation???

  ## Tactics

  **by** tactic -- go from term mode to tactic mode

  **exact** term -- go from tactic mode to term mode

  * **ring** (ring axioms)
  * **simp** (simplification)
  * **norm_num** (inequality stuff)

  ## Notes

  * by refl is stronger than refl -- it can also prove things like a iff a.
  * Two proofs of the same theorem are equal according to LEAN.

## Sets and functions

* Functions are between types (not sets)
* Ex: **variable (X Y Z : Type)  (a b : X) ( f: X \r Y) (g : Y \r Z)**
  * Or more info: X : Type [AddMonoid X]
* Function.Injective f, Function.Surjective f
* namespace name : Now everything lives under name.?
* obtain \langle y, hy \rangle:= hg z gives you a y and a proof gy=z (?)
  * alternative to rcases
* fun n \mapsto n^2 + 3 (lambda notation)
* Set is called Type
* ext tactic reduces X=Y to a\in X \iff a \in Y.
* S : Set A -- a subset of A. Elements of S are of type A
* 