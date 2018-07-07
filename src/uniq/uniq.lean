/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- workaround for https://github.com/leanprover/lean/issues/1961
lemma subtype_eq {α : Sort*} {p : α → Prop} :
∀ {a1 a2 : subtype p}, a1.val = a2.val → a1 = a2
| ⟨x,h1⟩ ⟨.(x),h2⟩ rfl := rfl

class inductive uniq (α : Sort*) : Prop
| intro (w : α) : (∀ x : α, x = w) → uniq

constant the (α : Sort*) [uniq α] : α

definition uniq_of_nonempty_of_subsingleton (α : Sort*)
[hs : subsingleton α] [hn : nonempty α] : uniq α :=
nonempty.rec_on hn (λ w, uniq.intro w (λ x, subsingleton.elim x w))

namespace uniq
variables {α : Sort*} {β : α → Sort*}

lemma elim (h : uniq α) : ∃ (w : α), ∀ (x : α), x = w :=
uniq.rec_on h (λ w hw, ⟨w,hw⟩)

instance to_subsingleton [h : uniq α] : subsingleton α :=
let ⟨w,hw⟩ := h.elim in subsingleton.intro (by intros x y; rw [hw x, hw y])

instance to_nonempty [h : uniq α] : nonempty α :=
let ⟨w,_⟩ := h.elim in nonempty.intro w

lemma eq_the [uniq α] : ∀ y : α, y = the α := 
λ y, subsingleton.elim y (the α)

instance subtype_of_exists_unique (p : α → Prop) :
(∃! x, p x) → uniq { x : α // p x} :=
λ ⟨w, hw, h⟩, uniq.intro ⟨w,hw⟩ (λ ⟨x,hx⟩, subtype_eq (h x hx))

instance prop (p : Prop) : p → uniq p := 
assume h, uniq.intro h (λ h', proof_irrel h' h)

instance punit : uniq punit :=
uniq.intro () (λ x, punit.rec_on x rfl)

instance prod {α : Type*} {β : Type*} [ha : uniq α] [hb : uniq β] : uniq (α × β) :=
let ⟨x,hx⟩ := ha.elim in
let ⟨y,hy⟩ := hb.elim in
uniq.intro (x,y) (λ ⟨x',y'⟩, by rw [hx x', hy y'])

instance pi [Π x, uniq (β x)] : uniq (Π x, β x) :=
uniq.intro (λ x, the (β x)) (λ f, funext (λ x, eq_the (f x)))

end uniq

noncomputable
definition the_unique {α : Sort*} (p : α → Prop) :
(∃! w, p w) → { x : α // p x } :=
assume h, @the { x : α // p x } (uniq.subtype_of_exists_unique p h)

theorem unique_choice {α : Sort*} {β : Sort*} (r : α → β → Prop) :
(∀ x, ∃! y, r x y) → (∃ f : α → β, ∀ x, r x (f x)) :=
assume h, 
⟨ λ x, subtype.val $ the_unique (r x) (h x)
, λ x, subtype.property $ the_unique (r x) (h x)
⟩
