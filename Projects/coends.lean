import LftCM.Common
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Opposites
open CategoryTheory

noncomputable section

universe u v
universe u' v'
variable {C:Type u} [Category.{v} C]
variable {D:Type u'} [Category.{v'} D]
variable (F : (Cᵒᵖ×C) ⥤ D)
-- ends via twisted arrow category
def bar_fun : (Functor.hom C).Elements ⥤ D := (CategoryOfElements.π (Functor.hom C)) ⋙ F
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

def idWedge (x : Wedge F) : WedgeMor x x where
  mor := 𝟙 x.pt

def compWedge {x y z : Wedge F} (f : WedgeMor x y) (g : WedgeMor y z) : WedgeMor x z where
  mor := f.mor ≫ g.mor

lemma idWedge_comp : ∀ {x y : Wedge F} (f : WedgeMor x y), compWedge (idWedge x) f = f := by
  sorry

lemma comp_idWedge : ∀ {x y : Wedge F} (f : WedgeMor x y), compWedge f (idWedge y) = f := by
  sorry

lemma compWedge_assoc : ∀ {w x y z : Wedge F} (f : WedgeMor w x) (g : compWedge x y) (h : compWedge y z), compWedge (compWedge f g) h = compWedge f compWedge( g h ) := by
  sorry

instance : Category (Wedge F) where
  Hom := fun x y => WedgeMor x y
  id := fun x => idWedge x
  comp := fun f g => compWedge f g
  id_comp := idWedge_comp
  comp_id := comp_idWedge
  assoc := compWedge_assoc

#exit

variable {w x y z: Wedge F}
variable {f :  WedgeMor x y}
variable {g : WedgeMor y z}
