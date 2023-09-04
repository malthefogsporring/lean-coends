## **Functions**

* **#****check** thing -- gives type
* **def** name : type := sorry -- define thing
* **#****print**
* **#lint** -- find errors
* **theorem** name : proposition := proof (same as def, but use for theorems)
* **rw** lem assumptions -- use a lemma to rewrite proof state
  * rw [p1,p2,...] for multiple lemmas
* **\l** lemma -- reverse direction of lemma
* **rw?** -- gives rw suggestions.

## Types

* **Prop**: Statements like 2+2=4, 2+2=5, 1<3, Irrational(pi)
* **p ** (of type Prop): a proof of p.

## Strategies

* **refl**: (x=x)
* **trivial**: (True)
* **Nat.add_comm**: a+b=b+a

## Tactics

**by** tactic -- go from term mode to tactic mode

**exact** term -- go from tactic mode to term mode

* **ring** (ring axioms)
* **simp** (simplification)
* **norm_num** (inequality stuff)

## Notes

* by refl is stronger than refl -- it can also prove things like a iff a.
* Two proofs of the same theorem are equal according to LEAN.