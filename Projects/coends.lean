import LftCM.Common
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Opposites
open CategoryTheory

noncomputable section

universe v v' u u'
variable {C:Type u} [Category.{v} C]
variable {D:Type u'} [Category.{v'} D]
variable (F : (Cᵒᵖ×C) ⥤ D)
-- ends via twisted arrow category
abbrev TwistedArrow C [Category.{v} C] := (Functor.hom.{v, u} C).Elements
@[simp] def bar_fun : (TwistedArrow C) ⥤ D := (CategoryOfElements.π (Functor.hom C)) ⋙ F
def endCone [Limits.HasLimit (bar_fun F)] := Limits.LimitCone (bar_fun F)

-- ends via wedges
def twisted_diagonal (F : (Cᵒᵖ×C) ⥤ D) : C → D := fun c ↦ F.obj (Opposite.op c,c)

-- c -> F(c,c)
structure Wedge (F : (Cᵒᵖ×C) ⥤ D) where
  pt : D
  leg : ∀ c : C, pt ⟶ (twisted_diagonal F) c
  wedgeCondition : ∀ ⦃c c' : C⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (Opposite.op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (Opposite.op c, c'))
     := by aesop_cat

-- attribute [simp] Wedge.wedgeCondition
variable {F}

@[ext] structure WedgeMorphism (x y : Wedge F) where
  Hom : x.pt ⟶ y.pt
  wedgeCondition : ∀ (c : C),
    Hom ≫ y.leg c = x.leg c
     := by aesop_cat

/-attribute [simp] Wedge.wedgeCondition
attribute [simp] Wedge.leg-/
attribute [simp] WedgeMorphism.wedgeCondition

@[simp] def wedge_id (x : Wedge F) : WedgeMorphism x x where
  Hom := 𝟙 x.pt

@[simp] def wedge_comp {x y z : Wedge F} (f : WedgeMorphism x y) (g : WedgeMorphism y z) : WedgeMorphism x z where
  Hom := f.Hom ≫ g.Hom


/-lemma wedge_id_comp : ∀ {x y : Wedge F} (f : WedgeMorphism x y), wedge_comp (wedge_id x) f = f := by
  aesop_cat

lemma comp_wedge_id : ∀ {x y : Wedge F} (f : WedgeMorphism x y), wedge_comp f (wedge_id y) = f := by
  intro x y f
  rw [wedge_comp,wedge_id]
  aesop_cat

lemma wedge_comp_assoc : ∀ {w x y z : Wedge F} (f : WedgeMorphism w x) (g : WedgeMorphism x y) (h : WedgeMorphism y z), wedge_comp (wedge_comp f g) h = wedge_comp f (wedge_comp g h ) := by
  sorry-/

instance : Category (Wedge F) where
  Hom := fun x y => WedgeMorphism x y
  id := fun x => wedge_id x
  comp := fun f g => wedge_comp f g
open Limits

def myEnd [HasTerminal (Wedge F)] := terminal (Wedge F)

-- cones of bar_F are wedges of F
@[simp] def bar_F_cone_as_wedge ( c : Cone (bar_fun F)) : Wedge F where
  pt := c.pt
  leg (c':C) := c.π.app ⟨(Opposite.op c',c'),𝟙 c'⟩
  wedgeCondition d d' f := by
    have sq1 := c.w (j := ⟨(Opposite.op d', d'), 𝟙 d'⟩)
      (j' := ⟨(Opposite.op d, d'), f⟩) ⟨(f.op, 𝟙 _), by simp⟩
    have sq2 := c.w (j := ⟨(Opposite.op d, d), 𝟙 d⟩)
      (j' := ⟨(Opposite.op d, d'), f⟩) ⟨(𝟙 _, f), by simp⟩
    simp only [bar_fun, Functor.hom_obj, op_id, bar_fun]
    simp [bar_fun] at *
    rw [sq1,sq2]

def bar_F_cone_mor_as_wedgeMorphism {c : Cone (bar_fun F)} {d : Cone (bar_fun F)} (f : ConeMorphism c d) : WedgeMorphism (bar_F_cone_as_wedge c) (bar_F_cone_as_wedge d) where
  Hom := f.Hom

def functor_cone_to_wedge (F : (Cᵒᵖ×C) ⥤ D) : Functor (Cone (bar_fun F)) (Wedge F) where
  obj x := bar_F_cone_as_wedge x
  map f := bar_F_cone_mor_as_wedgeMorphism f

-- wedges of F are cones of F_bar


@[simp] def wedge_as_cone ( w : Wedge F) : Cone (bar_fun F) where
  pt := w.pt
  π := {
    app := fun g => (w.leg (Opposite.unop g.1.1)) ≫ (F.map (𝟙 g.1.1,g.2))
    naturality := by
      intro ⟨(d,d'),f⟩ ⟨(e,e'),g⟩ ⟨(h,h'),prop⟩
      dsimp
      simp
      dsimp at prop h h'
      change _ ⟶ _ at f g
      dsimp at f g
      have sq1 := w.wedgeCondition h.unop
      rw [Wedge.leg] at *
      simp at *
      have sq2 := congr_arg (fun (j : Opposite.unop e ⟶ e') ↦ F.map (X := (e,Opposite.unop e)) (Y:= (e,e')) (𝟙 e, j)) prop
      simp at sq2
      aesop_cat_nonterminal


  }

-- app := fun ⟨(d,d'),f⟩ => (w.leg (Opposite.unop d)) ≫ ((bar_fun F).map ⟨(𝟙 d,f), by simp⟩ )
@[simp] def wedgeMorphism_as_coneMorphism {c : Wedge F} {d : Wedge F} (f : WedgeMorphism c d) : ConeMorphism (wedge_as_cone c) (wedge_as_cone d) where
  Hom := f.Hom

@[simp] def functor_wedge_to_cone (F : (Cᵒᵖ×C) ⥤ D) : Functor (Wedge F) (Cone (bar_fun F)) where
  obj x := wedge_as_cone x
  map f := wedgeMorphism_as_coneMorphism f

def limit_cone_as_terminal_wedge ( c : Cone (bar_fun F)) (ic : (IsLimit c)) :  IsTerminal (bar_F_cone_as_wedge c) :=
  IsTerminal.ofUniqueHom (fun w ↦ ⟨ _ , _ ⟩ ) (by sorry)
  /-   intro ic
  dsimp
  rw [IsTerminal]
-/
