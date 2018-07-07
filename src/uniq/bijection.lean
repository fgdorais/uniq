/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .uniq .inverse

variables {α : Sort*} {β : Sort*} {γ : Sort*}

class inductive bijection (f : α → β) : Prop
| intro : (∀ y, ∃! x, f x = y) → bijection

lemma bijection.elim {f : α → β} :
bijection f → (∀ y, ∃! x, f x = y)
| (bijection.intro h) := h

lemma bijection_of_surjective_of_injective (f : α → β) :
function.injective f → function.surjective f → bijection f :=
λ hi hs, bijection.intro $
λ y, let ⟨x, hx⟩ := hs y in 
exists_unique.intro x hx (λ x' hx', hi (eq.trans hx' (eq.symm hx)))

lemma bijection_of_bijective (f : α → β) :
function.bijective f → bijection f :=
λ ⟨hi, hs⟩, bijection_of_surjective_of_injective f hi hs

namespace bijection
variables (g : β → γ) (f : α → β)

lemma injective [hf : bijection f] : function.injective f :=
λ x x' hxx', let ⟨_, _, h⟩ := elim hf (f x') in
eq.trans (h _ hxx') (eq.symm (h _ rfl))

lemma surjective [hf : bijection f] : function.surjective f :=
λ y, let ⟨x,hx,_⟩ := elim hf y in exists.intro x hx

lemma bijective [hf : bijection f] : function.bijective f :=
⟨injective f, surjective f⟩

noncomputable
definition inv [hf : bijection f] : β → α :=
λ y, subtype.val $ the_unique _ (elim hf y)

lemma inv_right_inverse [hf : bijection f] : 
function.right_inverse (inv f) f :=
λ y, subtype.property $ the_unique _ (elim hf y)

lemma inv_left_inverse [bijection f] :
function.left_inverse (inv f) f :=
function.right_inverse_of_injective_of_left_inverse (injective f) (inv_right_inverse f)

lemma inv_inverse [bijection f] :
function.inverse (inv f) f :=
function.inverse_of_right_inverse_of_left_inverse (inv_left_inverse f) (inv_right_inverse f)

end bijection

section instances
open bijection

definition bijection_comp (g : β → γ) (f : α → β)
[hg : bijection g] [hf : bijection f] : bijection (g ∘ f) :=
bijection.intro $ λ z, let ⟨y,hy,uy⟩ := elim hg z in let ⟨x,hx,ux⟩ := elim hf y in
exists_unique.intro x 
 (show g (f x) = z, by rw [hx, hy])
 (λ x' h, ux x' (uy (f x') h))

definition bijection_id : bijection (@id α) :=
bijection.intro $ λ x, exists_unique.intro x rfl (λ x', id)

definition bijection_inv (f : α → β) [hf : bijection f] : bijection (inv f) :=
bijection.intro $ λ x, 
exists_unique.intro (f x) 
 (inv_left_inverse f x)
 (λ x' h, eq.symm ((inv_inverse f x x').mpr h))

attribute [instance, priority std.priority.default/2] bijection_comp
attribute [instance, priority std.priority.default/2] bijection_inv
attribute [instance] bijection_id

end instances

namespace bijection
variables (g : β → γ) (f : α → β)

@[simp]
lemma inv_id : inv (@id α) = (@id α) :=
funext (λ x, (inv_inverse id (id x) x).mp rfl)

lemma inv_comp [bijection g] [bijection f] :
inv (g ∘ f) = inv f ∘ inv g :=
funext (λ z, (inv_inverse (g ∘ f) _ _).mp 
 (calc (g ∘ f) ((inv f ∘ inv g) z) 
        = g (f (inv f (inv g z))) : rfl
    ... = g (inv g z)             : by rw inv_right_inverse f
    ... = z                       : by rw inv_right_inverse g))

@[simp]
lemma inv_inv [bijection f] : inv (inv f) = f :=
funext (λ x, (inv_inverse (inv f) _ _).mp (inv_left_inverse f x))

end bijection

