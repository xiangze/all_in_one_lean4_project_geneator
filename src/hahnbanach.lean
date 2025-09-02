/-
  Hahn–Banach (norm-preserving extension) in Lean 4

  ここでは実数ノルム線形空間 `E` とその部分空間 `F` 上の有界線形汎関数
  `f : F →L[ℝ] ℝ` を全空間にノルムを保ったまま拡張する定理を示します。
  `Mathlib.Analysis.Convex.HahnBanach` には
      ContinuousLinearMap.exists_extension_norm_eq
  という形で定理が実装されています。
-/

import Mathlib.Analysis.Convex.HahnBanach

open Classical
open ContinuousLinearMap
open Submodule

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Hahn–Banach**（ノルム保存版）
`f : F →L[ℝ] ℝ` は部分空間 `F` 上の有界線形汎関数とする。
そのとき `f` を全空間 `E` へノルムを変えずに拡張する
有界線形汎関数 `g` が存在する。 -/
theorem hahnBanach_norm_extension
    {F : Subspace ℝ E} (f : F →L[ℝ] ℝ) :
    ∃ g : E →L[ℝ] ℝ, (∀ x : F, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  -- ライブラリの定理をそのまま使えば終わり
  simpa using f.exists_extension_norm_eq
