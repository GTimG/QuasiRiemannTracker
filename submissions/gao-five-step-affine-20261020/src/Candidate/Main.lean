/- Five finite affine steps give an all-moduli Dirichlet zero bound.
Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualRootMoment
import Candidate.Research.RecursiveAffine.Endpoint.FinalFromRootFactory

set_option autoImplicit false
namespace Candidate

/-- Every Dirichlet L-function is nonzero to the right of 8748087/10000000,
with the principal pole excluded. The moment factory is constructed from
actual finite native sources; it is not a hypothesis of this theorem. -/
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8748087/10000000 : ℝ) < s.re) (hpole : ¬(χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  letI : Cycle153Endpoint.RootMomentFactory := Cycle153Endpoint.actualRootMomentFactory
  exact Cycle153Endpoint.FinalAssembly.allDirichlet_of_root_factory χ s hs hpole

end Candidate
#print Candidate.bound
#print axioms Candidate.bound

-- Freeze the canonical type independently of the implementation spelling.
example : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    (8748087/10000000 : ℝ) < s.re → ¬(χ=1 ∧ s=1) →
    DirichletCharacter.LFunction χ s ≠ 0 := @Candidate.bound
