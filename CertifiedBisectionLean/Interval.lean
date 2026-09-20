/-
Copyright (c) 2026 Daejun Ban. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daejun Ban
-/
import Mathlib

/-!
# Exact rational bisection

This module defines rational intervals and proves the core invariants of exact bisection for
the equation `x² = 2`.
-/

namespace CertiBisect

/-- A closed interval with exactly computable rational endpoints. -/
structure Interval where
  lower : ℚ
  upper : ℚ
deriving Repr, DecidableEq

namespace Interval

/-- The length of an interval. -/
def width (i : Interval) : ℚ := i.upper - i.lower

/-- The midpoint of an interval. -/
def midpoint (i : Interval) : ℚ := (i.lower + i.upper) / 2

/-- The endpoint squares straddle `2`. -/
def IsSqrtTwoBracket (i : Interval) : Prop :=
  i.lower ^ 2 ≤ 2 ∧ 2 ≤ i.upper ^ 2

/-- One exact bisection step for the equation `x² = 2`. -/
def step (i : Interval) : Interval :=
  let m := midpoint i
  if m ^ 2 ≤ 2 then
    ⟨m, i.upper⟩
  else
    ⟨i.lower, m⟩

/-- Repeatedly apply the exact bisection step. -/
def iterate : ℕ → Interval → Interval
  | 0, i => i
  | n + 1, i => step (iterate n i)

theorem width_step (i : Interval) : width (step i) = width i / 2 := by
  unfold step
  dsimp
  split <;> simp [width, midpoint] <;> ring

theorem step_preserves_bracket (i : Interval) (h : IsSqrtTwoBracket i) :
    IsSqrtTwoBracket (step i) := by
  by_cases hm : midpoint i ^ 2 ≤ (2 : ℚ)
  · have hu : (2 : ℚ) ≤ i.upper ^ 2 := h.2
    simpa [step, hm, IsSqrtTwoBracket] using And.intro hm hu
  · have hm' : (2 : ℚ) ≤ midpoint i ^ 2 := le_of_lt (lt_of_not_ge hm)
    have hl : i.lower ^ 2 ≤ (2 : ℚ) := h.1
    simpa [step, hm, IsSqrtTwoBracket] using And.intro hl hm'

theorem iterate_preserves_bracket (n : ℕ) (i : Interval) (h : IsSqrtTwoBracket i) :
    IsSqrtTwoBracket (iterate n i) := by
  induction n with
  | zero => simpa [iterate]
  | succ n ih =>
      simpa [iterate] using step_preserves_bracket (iterate n i) ih

theorem width_iterate (n : ℕ) (i : Interval) :
    width (iterate n i) = width i / (2 : ℚ) ^ n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      rw [iterate, width_step, ih, pow_succ]
      ring

end Interval
end CertiBisect
