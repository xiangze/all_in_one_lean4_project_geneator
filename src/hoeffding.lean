/-
Hoeffding's inequality in Lean 4 (mathlib4).
-/

/-
 import Hoeffding
-/

import Mathlib.Topology.Basic

import Mathlib/Probability/Moments/SubGaussian
import Mathlib/Data/Real/ENNReal
import Mathlib/MeasureTheory/Measure/ProbabilityMassFunction

open scoped BigOperators
open ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- **Hoeffding (finite sum, general widths).**
Let `s : Finset ι` and random variables `X i` (`i ∈ s`) be independent,
a.s. bounded in `[a i, b i]`, and mean-zero. Then, for all `ε ≥ 0`,
  `μ { ω | ε ≤ ∑ i∈s, X i ω } ≤ exp( - ε^2 / (2 * ∑ i∈s ((‖b i - a i‖₊ / 2)^2)) )`.
This is the classical Hoeffding bound (via sub-Gaussian MGF + Chernoff).
-/
theorem hoeffding_finset
  [IsProbabilityMeasure μ]
  (s : Finset ι) (X : ι → Ω → ℝ) (a b : ι → ℝ)
  (hMeas : ∀ i ∈ s, AEMeasurable (X i) μ)
  (hBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
  (hMean0 : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
  (hIndep : iIndepFun X μ)
  {ε : ℝ} (hε : 0 ≤ ε) :
  μ.real {ω | ε ≤ ∑ i ∈ s, X i ω}
    ≤ Real.exp(- ε ^ 2 / (2 * (↑(∑ i ∈ s, ((‖b i - a i‖₊ / 2) ^ 2 : NNReal))))) := by  classical
  -- Each summand is sub-Gaussian with parameter (‖b-a‖₊/2)^2 (Hoeffding's lemma).
  have hSub :
      ∀ i ∈ s, HasSubgaussianMGF (X i) ((‖b i - a i‖₊ / 2) ^ 2) μ := by
    intro i hi
    exact
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hMeas i hi) (hBound i hi) (hMean0 i hi)
  -- Chernoff/Hoeffding for sums of independent sub-Gaussians.
  simpa using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) (X := X) (s := s)
      (c := fun i => (‖b i - a i‖₊ / 2) ^ 2)
      hIndep hSub hε)

/-- **Hoeffding (i.i.d.-style, common width).**
`X 0, …, X (n-1)` independent, a.s. bounded in `[a, b]`, mean 0.
Then for every `ε ≥ 0`,
  `μ { ω | ε ≤ ∑_{i < n} X i ω } ≤ exp( - ε^2 / (2 * n * ((‖b - a‖₊ / 2)^2)) )`.
-/
theorem hoeffding_sum_range
  [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (a b : ℝ) (n : ℕ)
  (hMeas : ∀ i < n, AEMeasurable (X i) μ)
  (hBound : ∀ i < n, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
  (hMean0 : ∀ i < n, ∫ ω, X i ω ∂μ = 0)
  (hIndep : iIndepFun X μ)
  {ε : ℝ} (hε : 0 ≤ ε) :
  μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}
    ≤ Real.exp (-
        ε ^ 2 / (2 * (n : ℝ) *  (↑(((‖b - a‖₊) / 2) ^ 2 : NNReal)))) := by
  classical
  -- common sub-Gaussian parameter
  set c : NNReal := ((‖b - a‖₊ / 2) ^ 2)
  have hSub : ∀ i < n, HasSubgaussianMGF (X i) c μ := by
    intro i hi
    exact
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hMeas i hi) (hBound i hi) (hMean0 i hi)
  -- direct range-version bound in mathlib
  --   μ {ε ≤ ∑_{i < n} X_i} ≤ exp( - ε^2 / (2 n c) ).
  simpa [c, mul_comm, mul_left_comm, mul_assoc] using
    (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      (μ := μ) (X := X) (n := n) (c := c)
      hIndep hSub hε)
