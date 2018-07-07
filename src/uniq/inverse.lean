/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace function
variables {α : Sort*} {β : Sort*} 

definition inverse (g : β → α) (f : α → β) : Prop := ∀ x y, f x = y ↔ g y = x

definition has_inverse (f : α → β) : Prop := ∃ g : β → α, inverse f g

variables {g : β → α} {f : α → β}

-- missing from standard library?
lemma surjective_of_right_inverse : right_inverse g f → surjective f :=
λ h y, ⟨g y, h y⟩

lemma inverse_symm : inverse g f → inverse f g :=
λ h y x, iff.symm (h x y)

lemma unique_inverse {g₁ g₂ : β → α} : 
inverse g₁ f → inverse g₂ f → g₁ = g₂ :=
λ h₁ h₂, funext (λ y, (h₁ (g₂ y) y).mp ((h₂ (g₂ y) y).mpr rfl))

lemma left_inverse_of_inverse : inverse g f → left_inverse g f :=
λ h x, iff.mp (h x (f x)) rfl

lemma right_inverse_of_inverse : inverse g f → right_inverse g f :=
λ h y, iff.mpr (h (g y) y) rfl

lemma inverse_of_right_inverse_of_left_inverse :
left_inverse g f → right_inverse g f → inverse g f :=
λ hl hr x y, ⟨λ hf, eq.subst hf (hl x), λ hg, eq.subst hg (hr y)⟩

lemma has_left_inverse_of_has_inverse : has_inverse f → has_left_inverse f :=
λ ⟨g, h⟩, ⟨g, right_inverse_of_inverse h⟩

lemma has_right_inverse_of_has_inverse : has_inverse f → has_right_inverse f :=
λ ⟨g, h⟩, ⟨g, left_inverse_of_inverse h⟩

lemma has_inverse_of_has_right_inverse_of_has_left_inverse :
has_left_inverse f → has_right_inverse f → has_inverse f :=
λ ⟨g, hl⟩ ⟨g', hr⟩, 
have g' = g, from funext (λ y, by rw [← hr y, hl, hr]),
⟨g, inverse_of_right_inverse_of_left_inverse (eq.subst this hr) hl⟩

lemma bijective_of_inverse : inverse g f → bijective f :=
λ h, 
⟨ injective_of_left_inverse (left_inverse_of_inverse h)
, surjective_of_right_inverse (right_inverse_of_inverse h)
⟩

lemma bijective_of_has_inverse : has_inverse f → bijective f :=
λ h, 
⟨ injective_of_has_left_inverse (has_left_inverse_of_has_inverse h)
, surjective_of_has_right_inverse (has_right_inverse_of_has_inverse h)
⟩

end function
