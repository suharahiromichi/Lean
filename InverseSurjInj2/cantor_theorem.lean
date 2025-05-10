import Mathlib.Tactic

-- Cantorの定理
-- see also. ssr_cantor_theorem.v

-- 集合αの冪集合の濃度は、もとの集合αの濃度よりの真に大きい。
-- そのことを「集合αからαの冪集合への関数fは全射ではない」で示す。

section

open Function

variable {α : Type}

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  
  let B := { x | x ∉ f x }                  -- 対角線の否定
  rcases surjf B with ⟨a, h⟩
  
  have h₁ : a ∉ f a := by
    intro h'
    have : a ∉ f a := by
      rwa [h] at h'
    contradiction

  have h₂ : a ∈ B := by
    apply h₁

  have h₃ : a ∉ B := by
    rwa [h] at h₁

  contradiction

end

-- END
