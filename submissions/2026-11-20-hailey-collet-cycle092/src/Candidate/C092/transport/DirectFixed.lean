/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectAll
set_option autoImplicit false
namespace QRH.Cycle092.Direct
noncomputable section
open QRH.Cycle090

/-- The actual fixed detector's conservative short-count bracket. -/
def fixedBracket (p : ℝ) : ℝ :=
  p*(1+2*(5805911/100000000))+
    (1-p*(1+2*(379981/5000000)))*(360001/500000)

/-- The detector is strictly inside the genuine [.72,311/400] source interval. -/
theorem fixed_anchor_interior :
    (18/25 : ℝ) < 360001/500000 ∧ (360001/500000 : ℝ) < 311/400 ∧
    (1 : ℝ) < 3*(360001/500000)/2 ∧ (3*(360001/500000)/2 : ℝ) < 12499/10000 := by
  norm_num

/-- All five original native/unmarked continuation comparisons hold on the
whole amplitude interval. Both fixed-count branches are retained in directPrice. -/
theorem fixed_full_continuation {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1/2) :
    fixedBracket p ≤ 311/400+(1-311/400)*p ∧
    fixedBracket p ≤ 311/400+2*p*(3/20-1/10000000) ∧
    fixedBracket p ≤ 311/400+2*p*((1-1/1000000000000)-311/400)/(2+1/100000000000) ∧
    fixedBracket p ≤ 2*(1757/4000)+2*p*(27/1000) ∧
    fixedBracket p < 9/10 := by
  norm_num [fixedBracket]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The restricted native family used by the fixed continuations is contained
in the available positive source at the actual cost 10^-260. -/
theorem fixed_source_restriction :
    (1-1/1000000000000 : ℝ) ≤ 1-sourceCost ∧
    2+10*sourceCost ≤ 2+1/100000000000 ∧
    (3/20-1/10000000 : ℝ) ≤ 3/20-1000*sourceCost/1143 := by
  rcases source_contact_guards with ⟨hs,hs',_,_⟩
  exact ⟨by linarith,by linarith,by linarith⟩
end
end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.fixed_full_continuation
#print axioms QRH.Cycle092.Direct.fixed_source_restriction
