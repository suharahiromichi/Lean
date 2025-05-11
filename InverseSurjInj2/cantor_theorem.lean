import Mathlib.Tactic

-- Cantorの定理
-- see also. ssr_cantor_theorem.v
-- https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html#functions

-- 集合αの冪集合の濃度は、もとの集合αの濃度よりの真に大きい。
-- そのことを「集合αからαの冪集合への関数fは全射ではない」で示す。

section

open Function

variable {α : Type}

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let B := { x | x ∉ f x }
  rcases surjf B with ⟨a, h⟩
  have h₁ : a ∉ f a := by
    intro h'
    have : a ∉ f a := by
      rwa [h] at h'
    contradiction
  have h₂ : a ∈ B := by
    exact h₁
  have h₃ : a ∉ B := by
    rwa [h] at h₁
  contradiction


theorem Cantor' : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  
  -- 対角線の否定を導入する。
  let B := { x | x ∉ f x }
  
  -- f が全射という仮定を使って、ある a が存在し f a = B とする。
  -- 前提のexistを場合分けする。
  rcases surjf B with ⟨a, hfa⟩              -- a : α, hfa : f a = B
  
  have h₁ : a ∉ f a := by
    intro h'                                -- h' : a ∈ f a
  
    have h₄ : a ∉ f a := by
      rw [hfa] at h'                        -- h' : a ∈ B
      exact h'
    -- contradiaction                       -- h' と h₄ から矛盾
    apply h₄
    assumption
  
  -- a ∈ B が真の場合
  have h₂ : a ∈ B := by
    exact h₁
  
  -- a ∈ B が偽の場合
  have h₃ : a ∉ B := by
    rw [hfa] at h₁                          -- h₁ : a ∉ B
    contradiction                           -- h₁ と h₁ から矛盾
  
  -- h₂ と h₃ から矛盾を導く。
  contradiction
  
end

  -- rwa は rewrite (re) と assumption の意味なであるが、
  -- 証明を細かくみるために、分けて使う。

-- END
