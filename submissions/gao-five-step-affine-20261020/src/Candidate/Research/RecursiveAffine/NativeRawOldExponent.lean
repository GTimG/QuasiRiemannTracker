/- Pay the actual physical OLD shell, union and dyad costs inside the
native LOW target. Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextFee
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineScheduleData

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open Cycle63InitialMass

/-- The post-dictionary rate pays cap130, the physical shell/ray union,
the actual dyad-box count and all three OLD dictionary rates together.
The ambient budget is chosen before the moving current subset. -/
theorem actual_old_post_cost_paid {Bnorm : ℝ}(hB : 0≤Bnorm)
    (budget current : ℕ)(hcurrent : current≤budget) :
    let r:=postDictionaryRate Bnorm budget
    135*r+9*((current:ℝ)+2)*r≤nativeMu/32 :=by
  intro r
  have hr0 : 0≤r:=(postDictionaryRate_budgets hB budget).1.le
  have hden : 0<1024*(Bnorm+3*((budget:ℝ)+2)+1):=by positivity
  have hr : r≤nativeMu/(1024*(Bnorm+3*((budget:ℝ)+2)+1)):=min_le_right _ _
  have hpaid:=(le_div_iff₀ hden).mp hr
  have hc : (current:ℝ)≤budget:=by exact_mod_cast hcurrent
  have hcoefficient : 32*(135+9*((current:ℝ)+2))≤
      1024*(Bnorm+3*((budget:ℝ)+2)+1):=by
    have hn : (0:ℝ)≤budget:=Nat.cast_nonneg _
    nlinarith only [hB,hc,hn]
  have hscaled:=mul_le_mul_of_nonneg_right hcoefficient hr0
  nlinarith only [hpaid,hscaled]

variable [Cycle63.AffineLedger]

/-- This is the common source exponent after the genuine OLD payment
uses only nativeMu/64 of its available nativeMu/8. Width, slot loss, radial padding
and the actual mesh are kept at their original values. -/
def actualSourceCommon64 (g : GeometryAffineLowSchedule)(current : ℕ)
    (omega mesh : ℝ) : ℝ :=
  g.μ/8+g.μ/64/2-Cycle63.AffineLedger.lowReserve+g.μ/64+
    2*g.δ*31*current+Cycle63.AffineLedger.lowRate*(omega+g.μ/8)+
    Cycle63.AffineLedger.q*mesh

/-- Exact OLD exponent after native selected-row summation, physical
shell/ray recombination and the true dyad-box count. The measured source
pad is retained. No OLD energy estimate or desired target inequality is
assumed. The source producer separately supplies its common-exponent and
measured-pad bounds at the same literal source. -/
theorem native_raw_old_exponent_le_target
    (g : GeometryAffineLowSchedule)(hmu : g.μ=nativeMu)
    {Bnorm : ℝ}(hB : 0≤Bnorm)(budget current : ℕ)(hcurrent : current≤budget)
    (amp omega mesh Mrow oldError common sourcePad : ℝ)
    (hcommon : common≤actualSourceCommon64 g current omega mesh)
    (hpad : sourcePad≤g.μ/8) :
    let r:=postDictionaryRate Bnorm budget
    1+3*g.δ+oldError+3*g.δ+common+sourcePad+
      135*r+9*((current:ℝ)+2)*r ≤
      (Mrow+3*g.δ-amp+oldError)+
        geometryAffineLowTarget g current amp omega mesh+(1-Mrow) :=by
  intro r
  have hcost:=actual_old_post_cost_paid hB budget current hcurrent
  have hdelta:=g.δ_pos.le
  have hdeltaN : 0≤g.δ*(current:ℝ):=mul_nonneg hdelta (Nat.cast_nonneg _)
  have hmu0:=g.μ_pos.le
  rw [←hmu] at hcost
  dsimp only [actualSourceCommon64] at hcommon
  dsimp only [geometryAffineLowTarget]
  nlinarith only [hcost,hdelta,hdeltaN,hmu0,hcommon,hpad]

end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.actual_old_post_cost_paid
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.native_raw_old_exponent_le_target
