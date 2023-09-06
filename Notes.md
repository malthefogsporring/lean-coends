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
  * (explicit argument), {implicit argument}, [implicit argument, only when relevant]
  
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
  
  **refine**
  
  * Like exact, but you can do refine ?_ to make subgoals
  
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

## Algebra

* linear_combination eq -- tactic. Takes a linear combination of equations and simplifies to prove a goal of form a=b
* polyrith -- tactic that automates above. Uses Sage online
* ring_nf -- ring but doesn't complain if it doesn't finish

## Structures

* A structure is like a class
* (example) structure Card where
  * suit : Fin 4
  * value : Fin 13
* Ways to call a structure
  * def myPoint : Point where
    * x:=2
    * y:=-1
  * def myPoint : Point := {x:=2,y:=-1}
  * def myPoint: Point :=\langle 2, -1 \rangle
  * def myPoint := Point.mk 2 -1
* A trick: write def myPoint : Point := _ and click lightbulb
* Can then call myPoint.x or Point.x myPoint
* If you put all of this in a namespace Point, you can then do p1.add p2
* Structures can also take parameters (i.e. dependent types/template structures)
* class vs structure: is there a canonical value for your definition?
  * Yes: class
    * Add a
    * Fintype a
  * No: structure
    * Point R
* btw adding @[simp] before theorem will help simp & dsimp
* Proofs about structures
  * use ext tactic to split goal (you have to add @[ext] before defining structure)
* <;> tactic -- apply tactic to all subgoals
* You may want to include proofs within structures
* Proofs have type classes as well



## Algebraic Hierarchies

* Extending structures with "uses" is very smart.



##  Topology

* Use filters instead of epsilon-delta proofs
* Functions on sets generalise to functions on filters
  * "f converges wrt G along F" iff f_*F<=G. Tendsto f F G
* Upshot: this captures all the types of limits (finite, infinite, right, etc.) so need fewer proofs
* Example: lim_x->2 f(x)=1:
  * Tendsto f (nhds 2) (nhds 1)
  * nhds is the neighbourhood filter
  * atBot=-infty, atTop=+infty
* Galois connection: f_\*T<=f^\*T
* You shouldn't do epsilon-delta, but you can
* "For n large enough, P(n)"... or "for x close enough to x_0, P(x)"...
  * Notation: \eventually x in F, P x
  * In filter language, means {x | Px}\in F
  * tactic: filter_upwards
* What does continuous mean?
  * f:X->Y cont at z iff f\_* N\_(x\_0)<= N\_(f(x\_0))
  * f cont everywhere if f\_* T\_X<= T\_Y, where T\_X is the collection of all neighbourhood filters ("the topology")



## Combinatorics

* Set \N (sets of natural numbers)
* FinSet \N (finite sets of natural numbers)
* Functions: \union, \inter, \empty, \insert, \hassubset, \SDiff
* s.erase a removes a from s.
* biUnion (..?)
* (a : Type) [Fintype a]
  * Notation for anything to be finite. Then you can check cardinality fx; Fintype.card a
* Open BigOperators to use sigma + prod notation]
  * Note: in LEAN, we define product stuff, and use @[to_additive] to generate the additive version
* calc tactic: a <= _  :=
  * a = _ :=
  * _ <= _  :=
  * _ = b :=
