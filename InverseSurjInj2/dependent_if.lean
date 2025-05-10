import Mathlib.Tactic

open Function
open Classical

section
variable {α β : Type} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check (choose h : α)                      -- Classical

example : P (choose h) :=
  choose_spec h                             -- Classical

noncomputable section
-- dependent if-then-else の使用例
def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then choose h else default

-- ssr_dependent_if.v との対応では、これが証明できればよい。
theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact choose_spec h

section
variable (f : α → β)

#print LeftInverse
#print RightInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  · intro h x1 x2 e
    rw [← h x1, ← h x2, e]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  · intro h y
    use inverse f y
    apply h

end
end
end

-- END
