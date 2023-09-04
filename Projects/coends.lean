import LftCM.Common
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
open CategoryTheory

section

universe u v
universe u' v'
variable {C:Type u} [Category.{v} C]
variable {D:Type u'} [Category.{v'} D]
variable {F : (Cᵒᵖ×C) ⥤ D}
def Fbar : (Functor.hom C).Elements ⥤ D := (CategoryOfElements.π (Functor.hom C)) ⋙ F
#check Fbar
Limits.HasLimit F
#check Limits.Haslimits.limit F
def end : := limit F

instance myNatCat : Category ℕ where
  Hom := fun m n => Inhabited (m ≤ n)
  id := fun m => Inhabited.mk (by linarith)
  comp := fun f g => Inhabited.mk (by
    rcases f
    rcases g
    linarith
  )
