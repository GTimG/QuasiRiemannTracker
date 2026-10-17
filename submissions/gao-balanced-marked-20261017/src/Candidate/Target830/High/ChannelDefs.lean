import Candidate.Target830.Parameters

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open Target830

def highBase (P : SourcePlane) (b delta : ℝ) : ℝ :=
  1-rho delta-delta*P.total b-P.amp b*(5-6*rho delta)
def highFee : ℝ := highReserve+highRawFee

/-- Two common-rate faces and the five exact marked/root faces. -/
def channel (P : SourcePlane) (b delta : ℝ) : Fin 7→ℝ :=
  ![highBase P b delta+(delta-3/19)*P.supplied b,
    highBase P b delta+(delta-4*rho delta+5/4)*P.supplied b,
    highBase P b delta+phi delta*P.supplied b,
    highBase P b delta+phi delta*(2*P.supplied b+capP delta*P.frequency b)/3,
    highBase P b delta+phi delta*(2*capI delta*P.frequency b+P.supplied b)/3,
    highBase P b delta+phi delta*(2*capI delta+capP delta)*P.frequency b/3,
    highBase P b delta+P.rootCutoff*(6*rho delta-1)*P.frequency b]

end OAI.SevenEighths.TargetHigh830
