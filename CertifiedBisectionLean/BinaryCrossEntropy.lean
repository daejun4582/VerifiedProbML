/-
Copyright (c) 2026 Daejun Ban. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daejun Ban
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Binary cross-entropy

For a true Bernoulli probability `p` and a reported probability `q`, this file
proves that binary cross-entropy is minimized by reporting `q = p`.
-/

namespace CertiBisect.BinaryCrossEntropy

open Real

/-- Expected binary log loss when the true probability is `p` and the reported
probability is `q`. -/
noncomputable def crossEntropy (p q : ℝ) : ℝ :=
  -p * log q - (1 - p) * log (1 - q)

/-- KL divergence between Bernoulli parameters, written as a real-valued formula. -/
noncomputable def bernoulliKL (p q : ℝ) : ℝ :=
  p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

theorem crossEntropy_self (p : ℝ) :
    crossEntropy p p = binEntropy p := by
  simp [crossEntropy, binEntropy, log_inv]
  ring

/-- Cross-entropy equals entropy plus the Bernoulli KL excess loss. -/
theorem crossEntropy_eq_entropy_add_kl
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    crossEntropy p q = binEntropy p + bernoulliKL p q := by
  have h1p : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  have h1q : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  rw [crossEntropy, binEntropy, bernoulliKL]
  rw [log_inv, log_inv, log_div hp.ne' hq.ne',
    log_div h1p h1q]
  ring

/-- Gibbs' inequality specialized to two-outcome distributions. -/
theorem bernoulliKL_nonneg
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ bernoulliKL p q := by
  have hfirst := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hsecond := Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr hq1) (sub_pos.mpr hp1))
  have hpm0 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  have hqm0 : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hlog1 : log (p / q) = -log (q / p) := by
    rw [log_div hp.ne' hq.ne', log_div hq.ne' hp.ne']
    ring
  have hlog2 : log ((1 - p) / (1 - q)) = -log ((1 - q) / (1 - p)) := by
    rw [log_div hpm0 hqm0, log_div hqm0 hpm0]
    ring
  rw [bernoulliKL, hlog1, hlog2]
  have hdiv1 : p * (q / p - 1) = q - p := by field_simp
  have hdiv2 : (1 - p) * ((1 - q) / (1 - p) - 1) = p - q := by
    field_simp
    ring
  nlinarith [mul_le_mul_of_nonneg_left hfirst hp.le,
    mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr hp1.le)]

/-- Reporting the true Bernoulli probability minimizes expected binary log loss. -/
theorem crossEntropy_minimized_at_truth
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    crossEntropy p p ≤ crossEntropy p q := by
  rw [crossEntropy_self, crossEntropy_eq_entropy_add_kl hp hp1 hq hq1]
  exact le_add_of_nonneg_right (bernoulliKL_nonneg hp hp1 hq hq1)

/-- A concrete calibration check: when the event rate is `1/4`, predicting `1/4`
is no worse than predicting `3/4`. -/
example : crossEntropy (1 / 4 : ℝ) (1 / 4 : ℝ) ≤
    crossEntropy (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  exact crossEntropy_minimized_at_truth (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end CertiBisect.BinaryCrossEntropy
