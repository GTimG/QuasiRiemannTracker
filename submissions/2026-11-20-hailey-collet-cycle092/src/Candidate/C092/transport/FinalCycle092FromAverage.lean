/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual contact and shifted conductor, full mixed-bin return, ordered
source induction and original colored signed restoration meet at the remaining
averaged physical source. This is a conditional development theorem. -/
import Candidate.C092.transport.FinalCycle092TrueContact
import Candidate.C092.transport.MixedUpperFinalEstimate
import Candidate.C092.transport.OrderedPairActualRestoredModulus
import Candidate.C092.transport.OrderedPairPhaseClosure
set_option autoImplicit false
noncomputable section
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103Return QRH.Cycle090
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.StrongPair
open QRH.Cycle092.OrderedPairPhase QRH.Cycle092.LowActual
namespace QRH.Cycle092.Final

theorem target_of_earlier_source (source:Cycle090.theta < HeckeZeroSupremum.beta → RawTicket.EarlierP1) :
    HeckeZeroSupremum.beta ≤ Cycle090.theta ∧
    (∀ (η:Character) (s:ℂ),Cycle090.theta<s.re → (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧
    Cycle090.OrdinaryTarget := by
  apply target_at_true_contact
  letI : Geometry.Parameters:=ActualGeometry.parameters conductorQ conductorQ_bounds.1 conductorQ_bounds.2
  letI : ActualGeometry.WidenedCoreBounds:=ActualGeometry.widenedBounds conductorQ conductorQ_bounds.1 conductorQ_bounds.2
  intro h
  exact MixedUpperFinal.earlier_P1_mixed_upper_estimate conductorQ conductorQ_bounds.1 conductorQ_bounds.2 rfl (source h) h

theorem target_of_averaged_stages
    (physical: (51/100:ℝ) ≤ HeckeZeroSupremum.beta → Cycle090.theta < HeckeZeroSupremum.beta →
      ∀ n y:ℝ,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover PairOpenWidth y →
      ∀ l:ℝ,0 ≤ l → l < sourceWidth n y → ∀ ε:ℝ,0 < ε →
      ∃ mesh cRad ξ κ ξsecond εmass loss:ℝ,
      0 < mesh ∧ ∃ hmesh:mesh ≤ 1/6,1 ≤ cRad ∧ 0 < ξ ∧ 0 < κ ∧ 0 < ξsecond ∧ ξ/2+κ ≤ 22 ∧
        0 < εmass ∧ loss+εmass ≤ ε/2 ∧ NativeAveragedStageSupply n y l mesh ε cRad ξ κ loss ξsecond hmesh) :
    HeckeZeroSupremum.beta ≤ Cycle090.theta ∧
    (∀ (η:Character) (s:ℂ),Cycle090.theta<s.re → (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧
    Cycle090.OrdinaryTarget := by
  apply target_of_earlier_source
  intro h
  have hβ:(51/100:ℝ) ≤ HeckeZeroSupremum.beta := (by norm_num [Cycle090.theta] : (51/100:ℝ) ≤ Cycle090.theta).trans h.le
  apply OrderedPairPhase.all_pair_strips_of_centered_terminal hβ
  intro n y hy hy' hn' hn cover l hl hb
  exact centered_uniform_of_native_averaged n y l hy hy' hn hb (physical hβ h n y hy hy' hn' hn cover l hl hb)

#print axioms target_of_averaged_stages
end QRH.Cycle092.Final
