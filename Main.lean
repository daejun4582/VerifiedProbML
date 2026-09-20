import CertifiedBisectionLean.BinaryCrossEntropy
import CertifiedBisectionLean.GaussianEstimator
import CertifiedBisectionLean.SqrtTwo

open CertiBisect

def main : IO Unit := do
  let result := sqrtTwoAfterTen
  IO.println "CertiBisect: certified rational bounds for sqrt(2)"
  IO.println s!"lower = {result.lower}"
  IO.println s!"upper = {result.upper}"
  IO.println s!"width = {result.width}"
  IO.println "Lean theorem: lower ≤ sqrt(2) ≤ upper"
  IO.println ""
  IO.println "Gaussian ensemble example"
  IO.println "variances = [1, 4, 9]"
  IO.println "optimal weights = [36/49, 9/49, 4/49]"
  IO.println "minimum variance = 36/49"
  IO.println ""
  IO.println "Binary cross-entropy"
  IO.println "Lean theorem: CE(p, p) ≤ CE(p, q) for p,q in (0,1)"
