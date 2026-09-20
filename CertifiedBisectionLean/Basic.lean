/-
Copyright (c) 2026 Daejun Ban. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daejun Ban
-/
import Mathlib

/-!
# Environment smoke test

This module contains a minimal theorem confirming that Lean and Mathlib elaborate correctly.
-/

namespace CertiBisect

/-- A tiny theorem used to confirm that Lean and Mathlib are available. -/
theorem environmentReady : 2 + 2 = 4 := by
  norm_num

end CertiBisect
