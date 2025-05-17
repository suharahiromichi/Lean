import Mathlib.Tactic

open Function
open Classical

section
variable {α β : Type} [Inhabited α]

#check (default : α)
-- #check (default : β)

section
variable (P : α → Prop) (h : ∃ x, P x)

#check (choose h : α)                      -- Classical

example : P (choose h) :=
  choose_spec h                             -- Classical
end

noncomputable section
-- dependent if-then-else と一緒に証明されている補題
#check dif_pos                 -- h が成り立つなら結果は then の値
#check dif_neg                 -- h が成り立たないなら結果は else の値

-- dependent if-then-else の使用例
def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then choose h else default

-- ssr_dependent_if.v との対応では、これが証明できればよい。
theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]
  rw [dif_pos h]
  exact choose_spec h

-- MIL で証明している定理
-- https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html#functions
section
variable (f : α → β)

#print Injective
#print Surjective
#print LeftInverse
#print RightInverse

-- f が単射であることと、左逆写像g (g ∘ f = id) を持つことは同値である。
example : Injective f ↔ LeftInverse (inverse f) f := by
  rw [Injective, LeftInverse]
  constructor
  -- → の証明
  · intro h' y
    apply h'                                -- 両辺に f を掛ける。
    apply inverse_spec
    -- ∃ x, f x = f y
    use y                                   -- exists y
  -- ← の証明
  · intro h' x1 x2 e
    rw [← h' x1]
    rw [← h' x2]
    rw [e]

-- f が全射であることと、右逆写像g (f ∘ g = id) を持つことは同値である。
example : Surjective f ↔ RightInverse (inverse f) f := by
  rw [Surjective, RightInverse, LeftInverse]
  constructor
  -- → の証明
  · intro h' y
    apply inverse_spec
    apply h'
  -- ← の証明
  · intro h' y
    -- ∃ a, f a = y
    use (inverse f y)                       -- exists (inverse f y)
    apply h'

end
end
end

-- END
