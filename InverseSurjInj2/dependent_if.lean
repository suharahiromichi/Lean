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

-- MIL で証明している定理
-- https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html#functions
section
variable (f : α → β)

#print Injective
#print Surjective
#print LeftInverse
#print RightInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  -- → の証明
  · intro h' y
    -- rw [Injective] at h'
    apply h'                                -- 両辺に f を掛ける。
    apply inverse_spec
    -- ∃ x, f x = f y
    use y                                   -- exists y
  -- ← の証明
  · intro h' x1 x2 e
    -- rw [LeftInverse] at h'
    rw [← h' x1]
    rw [← h' x2]
    rw [e]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  -- → の証明
  · intro h' y
    apply inverse_spec
    -- rw [Surjective] at h'
    apply h'
  -- ← の証明
  · intro h' y
    use (inverse f y)                       -- exists (inverse f y)
    -- rw [RightInverse, LeftInverse] at h'
    apply h'

end
end
end

-- END
