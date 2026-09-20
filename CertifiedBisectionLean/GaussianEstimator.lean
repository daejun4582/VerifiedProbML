/-
Copyright (c) 2026 Daejun Ban. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daejun Ban
-/

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Variance

/-!
# Minimum-variance Gaussian ensembles

This file separates the deterministic optimization problem from its probabilistic
interpretation.  The optimization theorem only needs nonnegative variances; the
probability theorem explains why that quadratic objective is the variance of an
independent weighted ensemble.
-/

open scoped BigOperators ENNReal NNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace CertiBisect.GaussianEstimator

section Optimization

variable {ι : Type*} [Fintype ι]

/-- Variance predicted for a weighted sum of independent estimators. -/
def ensembleVariance (variance weight : ι → ℝ) : ℝ :=
  ∑ i, variance i * weight i ^ 2

/-- The affine constraint that makes a weighted estimator unbiased. -/
def IsUnbiasedWeight (weight : ι → ℝ) : Prop :=
  ∑ i, weight i = 1

/-- A useful characterization of inverse-variance weights: variance times weight
is the same constant for every component. -/
def IsPrecisionWeight (variance weight : ι → ℝ) : Prop :=
  ∃ c : ℝ, ∀ i, variance i * weight i = c

/-- Pythagorean-style decomposition of the ensemble variance around a precision weight. -/
theorem ensembleVariance_decomposition
    {variance weight optimal : ι → ℝ}
    (hweight : IsUnbiasedWeight weight)
    (hoptimal : IsUnbiasedWeight optimal)
    (hprecision : IsPrecisionWeight variance optimal) :
    ensembleVariance variance weight =
      ensembleVariance variance optimal +
        ∑ i, variance i * (weight i - optimal i) ^ 2 := by
  rcases hprecision with ⟨c, hc⟩
  change ∑ i, weight i = 1 at hweight
  change ∑ i, optimal i = 1 at hoptimal
  have hcross : ∑ i, 2 * (variance i * optimal i) * (weight i - optimal i) = 0 := by
    simp_rw [hc]
    rw [← Finset.mul_sum]
    simp [Finset.sum_sub_distrib, hweight, hoptimal]
  calc
    ensembleVariance variance weight =
        ∑ i, (variance i * optimal i ^ 2 +
          variance i * (weight i - optimal i) ^ 2 +
          2 * (variance i * optimal i) * (weight i - optimal i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ensembleVariance variance optimal +
          ∑ i, variance i * (weight i - optimal i) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross, add_zero]
            rfl

/-- Precision weights globally minimize variance among all unbiased linear estimators. -/
theorem precisionWeight_minimizes
    {variance weight optimal : ι → ℝ}
    (hvariance : ∀ i, 0 ≤ variance i)
    (hweight : IsUnbiasedWeight weight)
    (hoptimal : IsUnbiasedWeight optimal)
    (hprecision : IsPrecisionWeight variance optimal) :
    ensembleVariance variance optimal ≤ ensembleVariance variance weight := by
  rw [ensembleVariance_decomposition hweight hoptimal hprecision]
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun i _ =>
    mul_nonneg (hvariance i) (sq_nonneg _)

/-- Total precision, the sum of reciprocal variances. -/
noncomputable def totalPrecision (variance : ι → ℝ) : ℝ :=
  ∑ i, (variance i)⁻¹

/-- The usual inverse-variance weight. -/
noncomputable def inverseVarianceWeight (variance : ι → ℝ) (i : ι) : ℝ :=
  (variance i)⁻¹ / totalPrecision variance

theorem inverseVarianceWeight_isUnbiased
    {variance : ι → ℝ} (htotal : totalPrecision variance ≠ 0) :
    IsUnbiasedWeight (inverseVarianceWeight variance) := by
  simp only [IsUnbiasedWeight, inverseVarianceWeight, ← Finset.sum_div]
  exact div_self htotal

theorem inverseVarianceWeight_isPrecision
    {variance : ι → ℝ} (hvariance : ∀ i, variance i ≠ 0) :
    IsPrecisionWeight variance (inverseVarianceWeight variance) := by
  refine ⟨(totalPrecision variance)⁻¹, fun i => ?_⟩
  simp [inverseVarianceWeight, div_eq_mul_inv, hvariance i]

theorem inverseVarianceWeight_minimizes
    {variance weight : ι → ℝ}
    (hvariance : ∀ i, 0 < variance i)
    (hweight : IsUnbiasedWeight weight)
    (htotal : totalPrecision variance ≠ 0) :
    ensembleVariance variance (inverseVarianceWeight variance) ≤
      ensembleVariance variance weight :=
  precisionWeight_minimizes (fun i => (hvariance i).le) hweight
    (inverseVarianceWeight_isUnbiased htotal)
    (inverseVarianceWeight_isPrecision fun i => (hvariance i).ne')

end Optimization

section Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable (weight : ι → ℝ) (X : ι → Ω → ℝ)

/-- Pointwise weighted ensemble of random variables. -/
def weightedSum (ω : Ω) : ℝ :=
  ∑ i, weight i * X i ω

/-- Weights summing to one preserve a common mean.  This is the unbiasedness
part of the estimator argument. -/
theorem weightedSum_expectation
    (μ : Measure Ω) [IsProbabilityMeasure μ] {mean : ℝ}
    (hint : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = mean)
    (hweight : IsUnbiasedWeight weight) :
    ∫ ω, weightedSum weight X ω ∂μ = mean := by
  change ∫ ω, ∑ i, weight i * X i ω ∂μ = mean
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_const_mul, hmean]
    rw [← Finset.sum_mul]
    simpa [IsUnbiasedWeight] using congrArg (fun x : ℝ => x * mean) hweight
  · intro i _
    exact (hint i).const_mul (weight i)

theorem weightedSum_variance
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hmem : ∀ i, MemLp (X i) 2 μ)
    (hindep : iIndepFun X μ) :
    Var[weightedSum weight X; μ] =
      ensembleVariance (fun i => Var[X i; μ]) weight := by
  let Y : ι → Ω → ℝ := fun i ω => weight i * X i ω
  have hYmem : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    exact (hmem i).const_mul (weight i)
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun i x => weight i * x) (fun _ => by fun_prop)
  rw [show weightedSum weight X = ∑ i, Y i by funext ω; simp [weightedSum, Y]]
  rw [IndepFun.variance_sum (s := Finset.univ) (X := Y)]
  · simp only [ensembleVariance, Y]
    apply Finset.sum_congr rfl
    intro i _
    rw [variance_const_mul]
    ring
  · intro i _
    exact hYmem i
  · intro i j _ _ hij
    exact hYindep.indepFun hij

theorem weightedSum_isGaussian
    (μ : Measure Ω)
    (hgaussian : ∀ i, HasGaussianLaw (X i) μ)
    (hindep : iIndepFun X μ) :
    HasGaussianLaw (weightedSum weight X) μ := by
  let Y : ι → Ω → ℝ := fun i ω => weight i * X i ω
  have hYgaussian : ∀ i, HasGaussianLaw (Y i) μ := by
    intro i
    simpa [Y, smul_eq_mul] using (hgaussian i).fun_smul (weight i)
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun i x => weight i * x) (fun _ => by fun_prop)
  change HasGaussianLaw (fun ω => ∑ i, Y i ω) μ
  exact hYindep.hasGaussianLaw_fun_sum hYgaussian

end Probability

section Example

/-- Three toy model variances used in the executable example. -/
noncomputable def exampleVariances : Fin 3 → ℝ := ![1, 4, 9]

/-- The corresponding exact inverse-variance weights. -/
noncomputable def exampleWeights : Fin 3 → ℝ := ![36 / 49, 9 / 49, 4 / 49]

theorem inverseVarianceWeight_example :
    inverseVarianceWeight exampleVariances = exampleWeights := by
  funext i
  fin_cases i <;> norm_num [inverseVarianceWeight, totalPrecision, exampleVariances,
    exampleWeights, Fin.sum_univ_succ]

theorem exampleWeights_unbiased : IsUnbiasedWeight exampleWeights := by
  norm_num [IsUnbiasedWeight, exampleWeights, Fin.sum_univ_succ]

theorem exampleWeights_variance :
    ensembleVariance exampleVariances exampleWeights = 36 / 49 := by
  norm_num [ensembleVariance, exampleVariances, exampleWeights, Fin.sum_univ_succ]

theorem exampleWeights_optimal (weight : Fin 3 → ℝ)
    (hweight : IsUnbiasedWeight weight) :
    ensembleVariance exampleVariances exampleWeights ≤
      ensembleVariance exampleVariances weight := by
  rw [← inverseVarianceWeight_example]
  apply inverseVarianceWeight_minimizes
  · intro i
    fin_cases i <;> norm_num [exampleVariances]
  · exact hweight
  · norm_num [totalPrecision, exampleVariances, Fin.sum_univ_succ]

end Example

end CertiBisect.GaussianEstimator
