import analysis.inner_product_space.basic

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
variables (u v : E)

-- ℝ の場合、絶対値を取った形
example : ‖inner u v‖ ≤ ‖u‖ * ‖v‖ := by exact abs_inner_le_norm u v

-- より一般的な形 (複素数も含む)
#check @inner_le_norm -- inner u v ≤ ‖u‖ * ‖v‖ (ただし、これは実数値の内積の場合。複素数では re (inner u v) ≤ ...)
#check @abs_inner_le_norm -- |inner u v| ≤ ‖u‖ * ‖v‖
