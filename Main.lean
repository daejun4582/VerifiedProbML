import CertifiedBisectionLean.SqrtTwo

open CertiBisect

def main : IO Unit := do
  let result := sqrtTwoAfterTen
  IO.println "CertiBisect: certified rational bounds for sqrt(2)"
  IO.println s!"lower = {result.lower}"
  IO.println s!"upper = {result.upper}"
  IO.println s!"width = {result.width}"
  IO.println "Lean theorem: lower ≤ sqrt(2) ≤ upper"
