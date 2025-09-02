import analysis.mean_inequalities

open_locale nnreal ennreal

variables {α : Type*} {E : Type*} [fintype α] {p : ℝ≥0∞} {f g : α → ℝ≥0}

-- 1 ≤ p のとき
example (hp : 1 ≤ p) :
  (∑ i, ((f i) + (g i))^p.to_real)^(1/p.to_real) ≤
  (∑ i, (f i)^p.to_real)^(1/p.to_real) + (∑ i, (g i)^p.to_real)^(1/p.to_real) :=
by exact ennreal.Lp_add_le hp f g
