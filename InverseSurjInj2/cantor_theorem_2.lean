-- Cantorの定理
-- see also. ssr_cantor_theorem.v
-- https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html#functions
-- https://zenn.dev/leanja/articles/cantor_theorem

-- 集合αの冪集合の濃度は、もとの集合αの濃度よりの真に大きい。
-- そのことを「集合αからαの冪集合への関数fは全射ではない」で示す。

import Mathlib.Tactic.Common

variable (A : Type)
open Function

example (f : A → Set A) : ¬ Surjective f := by
  -- f が全射だと仮定する。
  -- ゴールは False である。
  intro (hsurj : Surjective f)

  -- A の部分集合 Y を， 以下のように取る
  -- Y = {x | x ∉ f(x)}
  -- 対角線の否定を導入する。
  let B := {x | x ∉ f x}

  -- f は全射なので， f x = B となる x が存在する
  -- 前提のexists ``∃ a, f a = B`` の場合分けをする。
  obtain ⟨x, hx⟩ := hsurj B
--obtain H := hsurj B
--rcases H with ⟨x, hx⟩
  -- x : A
  -- hx : f x = B

  -- x について， x ∈ B ↔ x ∉ B が示せる
  have H1 : x ∈ B ↔ x ∉ B := by
    constructor

    -- 左から右を示す
    case mp =>
      -- x ∈ B だと仮定する
      intro hB

      -- B の定義から， x ∉ f x
      replace hB : x ∉ f x := by tauto

      -- f x = B だったから， x ∉ B
      rwa [hx] at hB

    -- 右から左を示す
    case mpr =>
      -- x ∉ B だと仮定する
      intro hB

      -- f x = B だったから， x ∉ f x
      replace hB : x ∉ f x := by rwa [← hx] at hB

      -- B の定義から， x ∈ B
      assumption
  -- H1 の証明終わり。
  
  -- H1 は矛盾である．
  tauto

  -- END
