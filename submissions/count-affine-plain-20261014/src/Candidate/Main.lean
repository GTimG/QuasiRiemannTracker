/- A48 count-side affine moment record (for liqsweep, AI-assisted). WORK IN PROGRESS: the proof is
INCOMPLETE; `Cycle61.CountAffine.Assembly.record_beta_le` and `Record.endpoint_certificate` contain
explicit `sorry`. Built on Hailey Collet's Cycle61 source (PR #42) with Zhongpai Gao's refinement (PR #43). -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.CountAffine.Assembly

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
open OAI.SevenEighths

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2187109 / 2500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num)
    (fun η t ht hp => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      (Cycle61.CountAffine.Assembly.record_beta_le.trans_lt ht) hp) χ s hs hpole

end Candidate
#print axioms Candidate.bound
