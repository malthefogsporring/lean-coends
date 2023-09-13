import LftCM.Common
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements

open CategoryTheory Opposite

noncomputable section

universe v v' u u'

variable {C:Type u} [Category.{v} C]
variable {D:Type u'} [Category.{v'} D]
variable (F : Cᵒᵖ × C ⥤ D)
/- (Co)ends are a special type of limit for a bifunctor F: Cᵒᵖ × C → D.
If we think of F as a generalised bimodule, then the end ∫_cF is the 'center' - the subobject of ΠF(c,c) of invariants by the action of F on arrows.
Simililarly, the coend ∫ᶜF is the 'space of coinvariants' - the quotient of ⨿F(c,c) induced by the same action.

(Co)ends show up everywhere: regular (co)limits, many weighted limits, (pointwise) Kan extensions, ... In this light, (co)ends are an effective organisational tool.

Additionally, they admit a sort of calculus. For instance, we have a form of Fubini's rule which says ∫ᶜ∫ᵉF≅∫ᵉ∫ᶜF≅∫^(c×e) F, for F:Cᵒᵖ × C × Eᵒᵖ × E → D.

We define (co)ends via (co)wedges, which are most convenient to work with, and as special (co)limits, from which we derive the properties of (co)limits.
((It would also be nice to define (co)ends via weighted limits))
We also formalise theorems about (co)ends roughly corresponding to chapters 1-2 of 'Coend Calculus' by Fosco Loregian.

TODO:
* Define `IsEnd`, probably in terms if `IsLimit`
* Define `HasEnd`, probably in terms of `HasLimit`
* Make it easy to prove `IsEnd` by using the equivalence, so we can give a universal wedge directly
* Add a notion `end`, like we have `binaryProduct` etc., based on `limit` (limit cone by `choice`)
* Add notation for `end`
* Dualize everything
-/

-- **ends via the twisted arrow category**
abbrev TwistedArrow C [Category.{v} C] := (Functor.hom.{v, u} C).Elements

-- The induced functor Fbar : Tw(C) → Cᵒᵖ × C → D corresponding to F : Cᵒᵖ × C → D
@[simp] def bar_fun : (TwistedArrow C) ⥤ D := (CategoryOfElements.π (Functor.hom C)) ⋙ F

def endCone [Limits.HasLimit (bar_fun F)] := Limits.LimitCone (bar_fun F)

-- **ends via wedges**
def twisted_diagonal (F : Cᵒᵖ × C ⥤ D) : C → D := fun c ↦ F.obj (op c, c)

structure Wedge (F : Cᵒᵖ × C ⥤ D) where
  pt : D
  leg (c : C) : pt ⟶ twisted_diagonal F c
  wedgeCondition ⦃c c' : C⦄ (f : c ⟶ c') :
    (leg c ≫ F.map ((𝟙 c).op, f) : pt ⟶ F.obj (op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c') : pt ⟶ F.obj (op c, c'))
     := by aesop_cat

variable {F}

@[ext]
structure WedgeMorphism (x y : Wedge F) where
  hom : x.pt ⟶ y.pt
  wedgeCondition : ∀ c, hom ≫ y.leg c = x.leg c := by aesop_cat

attribute [simp] WedgeMorphism.wedgeCondition

@[simps]
def wedge_id (x : Wedge F) : WedgeMorphism x x where
  hom := 𝟙 x.pt

@[simps]
def wedge_comp {x y z : Wedge F} (f : WedgeMorphism x y) (g : WedgeMorphism y z) :
    WedgeMorphism x z where
  hom := f.hom ≫ g.hom

/-- The category of wedges on a functor `F`. -/
instance : Category (Wedge F) where
  Hom := fun x y => WedgeMorphism x y
  id := fun x => wedge_id x
  comp := fun f g => wedge_comp f g
open Limits

-- Definition of end via wedges
def myEnd [HasTerminal (Wedge F)] := terminal (Wedge F)

-- **Functor from Cone(Fbar) to Wd(F)**

-- Function on objects
@[simp] def bar_F_cone_as_wedge ( c : Cone (bar_fun F)) : Wedge F where
  pt := c.pt
  leg (c' : C) := c.π.app ⟨(op c',c'),𝟙 c'⟩
  wedgeCondition d d' f := by
    have sq1 := c.w (j := ⟨(op d', d'), 𝟙 d'⟩)
      (j' := ⟨(op d, d'), f⟩) ⟨(f.op, 𝟙 _), by simp⟩
    have sq2 := c.w (j := ⟨(op d, d), 𝟙 d⟩)
      (j' := ⟨(op d, d'), f⟩) ⟨(𝟙 _, f), by simp⟩
    simp only [bar_fun, Functor.hom_obj, op_id, bar_fun]
    simp [bar_fun] at *
    rw [sq1, sq2]

-- Function of morphisms
def bar_F_cone_mor_as_wedgeMorphism {c : Cone (bar_fun F)} {d : Cone (bar_fun F)}
    (f : ConeMorphism c d) : WedgeMorphism (bar_F_cone_as_wedge c) (bar_F_cone_as_wedge d) where
  hom := f.Hom

-- Functor
def functor_cone_to_wedge (F : Cᵒᵖ × C ⥤ D) : Functor (Cone (bar_fun F)) (Wedge F) where
  obj x := bar_F_cone_as_wedge x
  map f := bar_F_cone_mor_as_wedgeMorphism f

-- **Functor from Wd(F) to Cone(Fbar)**

-- Function of objects
@[simp] def wedge_as_cone (w : Wedge F) : Cone (bar_fun F) where
  pt := w.pt
  π := {
    app := fun g => (w.leg (unop g.1.1)) ≫ (F.map (𝟙 g.1.1, g.2))
    naturality := by
      intro ⟨(d,d'),f⟩ ⟨(e,e'),g⟩ ⟨(h,h'),prop⟩
      aesop_cat_nonterminal
      dsimp at prop h h'
      change _ ⟶ _ at f g
      dsimp at f g
      have sq1 := w.wedgeCondition h.unop
      rw [Wedge.leg] at *
      simp at *
      have sq2 := congr_arg (fun (j : unop e ⟶ e') ↦ F.map (X := (e, unop e)) (Y:= (e,e')) (𝟙 e, j)) prop
      simp at sq2
      aesop_cat_nonterminal
      rw [← show 𝟙 e ≫ 𝟙 e ≫ 𝟙 e = 𝟙 e by aesop_cat]
      rw [← prod_comp Cᵒᵖ C (𝟙 e, h.unop) (𝟙 e ≫ 𝟙 e , f ≫ h')]
      rw [← prod_comp Cᵒᵖ C (𝟙 e, f) (𝟙 e, h')]
      rw [F.map_comp,F.map_comp, ← Category.assoc, sq1]
      rw [Category.assoc, ← F.map_comp,← F.map_comp,← F.map_comp]
      aesop_cat
  }

--  Function on morphisms
@[simp] def wedgeMorphism_as_coneMorphism {c : Wedge F} {d : Wedge F} (f : WedgeMorphism c d) :
    ConeMorphism (wedge_as_cone c) (wedge_as_cone d) where
  Hom := f.hom
  w := by
    intro ⟨(d, d'), f⟩
    aesop_cat_nonterminal
    have wedgeCon := f_1.wedgeCondition d.unop
    rw [← wedgeCon, Category.assoc]

-- Functor
@[simp] def functor_wedge_to_cone (F : Cᵒᵖ × C ⥤ D) : Functor (Wedge F) (Cone (bar_fun F)) where
  obj x := wedge_as_cone x
  map f := wedgeMorphism_as_coneMorphism f

-- Equivalence of categories of Wd(F) and Cone(F bar)
def equivalence_cone_Fbar_WdF : Equivalence (Wedge F) (Cone (bar_fun F)) :=
  CategoryTheory.Equivalence.mk (functor_wedge_to_cone F) (functor_cone_to_wedge F)
    sorry
    sorry
