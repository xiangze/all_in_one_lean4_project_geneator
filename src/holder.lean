import analysis.mean_inequalities

open_locale nnreal ennreal

variables {α : Type*} {E : Type*} [fintype α] {p q : ℝ≥0∞} {f g : α → ℝ≥0}

-- 1 ≤ p, 1/p + 1/q = 1 のとき
example (hp : 1 ≤ p) (hpq : 1/p + 1/q = 1) :
  ∑ i, f i * g i ≤ (∑ i, (f i)^p.to_real)^(1/p.to_real) * (∑ i, (g i)^q.to_real)^(1/q.to_real) :=
by exact ennreal.sum_mul_le_Lp_mul_Lq hp hpq f g
