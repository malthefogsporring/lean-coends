import LftCM.Common
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Opposites
open CategoryTheory

noncomputable section

universe u v
universe u' v'
variable {C:Type u} [Category.{v} C]
variable {D:Type u'} [Category.{v'} D]
variable (F : (Cᵒᵖ×C) ⥤ D)
-- ends via twisted arrow category
abbrev TwistedArrow C [Category.{v} C] := (Functor.hom.{v, u} C).Elements
@[simp] def bar_fun : (TwistedArrow C) ⥤ D := (CategoryOfElements.π (Functor.hom C)) ⋙ F
def endCone [Limits.HasLimit (bar_fun F)] := Limits.LimitCone (bar_fun F)

-- ends via wedges
def diag (F : (Cᵒᵖ×C) ⥤ D) : C → D := fun c ↦ F.obj (Opposite.op c,c)

-- c -> F(c,c)
structure Wedge (F : (Cᵒᵖ×C) ⥤ D) where
  pt : D
  leg : ∀ c : C, pt ⟶ (diag F) c
  wedgeCondition : ∀ ⦃c c' : C⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (Opposite.op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (Opposite.op c, c'))
     := by aesop_cat

-- attribute [simp] Wedge.wedgeCondition
variable {F}

@[ext] structure WedgeMor (x y : Wedge F) where
  mor : x.pt ⟶ y.pt
  morCond : ∀ (c : C),
    mor ≫ y.leg c = x.leg c
     := by aesop_cat

attribute [simp] WedgeMor.morCond

@[simp] def idWedge (x : Wedge F) : WedgeMor x x where
  mor := 𝟙 x.pt

@[simp] def compWedge {x y z : Wedge F} (f : WedgeMor x y) (g : WedgeMor y z) : WedgeMor x z where
  mor := f.mor ≫ g.mor


/-lemma idWedge_comp : ∀ {x y : Wedge F} (f : WedgeMor x y), compWedge (idWedge x) f = f := by
  aesop_cat

lemma comp_idWedge : ∀ {x y : Wedge F} (f : WedgeMor x y), compWedge f (idWedge y) = f := by
  intro x y f
  rw [compWedge,idWedge]
  aesop_cat

lemma compWedge_assoc : ∀ {w x y z : Wedge F} (f : WedgeMor w x) (g : WedgeMor x y) (h : WedgeMor y z), compWedge (compWedge f g) h = compWedge f (compWedge g h ) := by
  sorry-/

instance : Category (Wedge F) where
  Hom := fun x y => WedgeMor x y
  id := fun x => idWedge x
  comp := fun f g => compWedge f g
open Limits

def myEnd [HasTerminal (Wedge F)] := terminal (Wedge F)

-- cones of bar_F are wedges of F
@[simp] def bar_F_cone_as_wedge ( c : Cone (bar_fun F)) : Wedge F where
  pt := c.pt
  leg (c':C) := c.π.app ⟨(Opposite.op c',c'),𝟙 c'⟩
  wedgeCondition d d' f := by
    simp
    have sq1 := c.w (j := ⟨(Opposite.op d', d'), 𝟙 d'⟩)
      (j' := ⟨(Opposite.op d, d'), f⟩) ⟨(f.op, 𝟙 _), by simp⟩
    simp [bar_fun] at *
    have sq2 := c.w (j := ⟨(Opposite.op d, d), 𝟙 d⟩)
      (j' := ⟨(Opposite.op d, d'), f⟩) ⟨(𝟙 _, f), by simp⟩
    simp [bar_fun] at *
    rw [sq1,sq2]

def bar_F_cone_mor_as_WedgeMor {c : Cone (bar_fun F)} {d : Cone (bar_fun F)} (f : ConeMorphism c d) : WedgeMor (bar_F_cone_as_wedge c) (bar_F_cone_as_wedge d) where
  mor := f.Hom

def functor_cone_to_bar (F : (Cᵒᵖ×C) ⥤ D) : Functor (Cone (bar_fun F)) (Wedge F) where
  obj x := bar_F_cone_as_wedge x
  map f := bar_F_cone_mor_as_WedgeMor f

-- wedges of F are cones of F_bar

@[simp] def wedge_F_as_cone_F_bar ( w : Wedge F) : Cone (bar_fun F) where _

def bar_F_cone_mor_as_WedgeMor {c : Cone (bar_fun F)} {d : Cone (bar_fun F)} (f : ConeMorphism c d) : WedgeMor (bar_F_cone_as_wedge c) (bar_F_cone_as_wedge d) where
  mor := f.Hom

def functor_cone_to_bar (F : (Cᵒᵖ×C) ⥤ D) : Functor (Cone (bar_fun F)) (Wedge F) where
  obj x := bar_F_cone_as_wedge x
  map f := bar_F_cone_mor_as_WedgeMor f

def limit_cone_as_terminal_wedge ( c : Cone (bar_fun F)) (ic : (IsLimit c)) :  IsTerminal (bar_F_cone_as_wedge c) :=
  IsTerminal.ofUniqueHom (fun w ↦ ⟨ _ , _ ⟩ ) (by sorry)
  /-   intro ic
  dsimp
  rw [IsTerminal]
-/
