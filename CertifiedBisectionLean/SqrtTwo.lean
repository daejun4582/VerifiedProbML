/-
Copyright (c) 2026 Daejun Ban. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daejun Ban
-/
import CertifiedBisectionLean.Interval

/-!
# A certified interval for the square root of two

This module specializes exact rational bisection to ten steps from `[1, 2]` and proves that
the resulting endpoints bound the real number `√2`.
-/

namespace CertiBisect

/-- The initial interval used by the executable demo. -/
def sqrtTwoStart : Interval := ⟨1, 2⟩

theorem sqrtTwoStart_isBracket : sqrtTwoStart.IsSqrtTwoBracket := by
  norm_num [sqrtTwoStart, Interval.IsSqrtTwoBracket]

/-- The certified rational interval after ten exact bisection steps. -/
def sqrtTwoAfterTen : Interval := Interval.iterate 10 sqrtTwoStart

theorem sqrtTwoAfterTen_eq :
    sqrtTwoAfterTen = ⟨181 / 128, 1449 / 1024⟩ := by
  norm_num [sqrtTwoAfterTen, sqrtTwoStart, Interval.iterate, Interval.step, Interval.midpoint]

theorem sqrtTwoAfterTen_isBracket : sqrtTwoAfterTen.IsSqrtTwoBracket := by
  exact Interval.iterate_preserves_bracket 10 sqrtTwoStart sqrtTwoStart_isBracket

theorem sqrtTwoAfterTen_width : sqrtTwoAfterTen.width = 1 / 1024 := by
  rw [sqrtTwoAfterTen, Interval.width_iterate]
  norm_num [sqrtTwoStart, Interval.width]

/-- The computed rational endpoints are genuine lower and upper bounds for `√2`. -/
theorem sqrtTwoAfterTen_containsRoot :
    (181 : ℝ) / 128 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (1449 : ℝ) / 1024 := by
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · have hlower_sq : ((181 : ℝ) / 128) ^ 2 ≤ 2 := by
      norm_num
    nlinarith
  · have hupper_sq : (2 : ℝ) ≤ ((1449 : ℝ) / 1024) ^ 2 := by
      norm_num
    nlinarith

end CertiBisect
