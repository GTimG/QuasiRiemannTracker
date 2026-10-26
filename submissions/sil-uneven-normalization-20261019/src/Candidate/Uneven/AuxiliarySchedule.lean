/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
    The extended lower width overlaps the old moment and avoids a selected-width gap. -/
import Candidate.Uneven.SaturatedGain

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Sil.Uneven.AuxiliarySource

def B : ℝ := 1988153/2000000
def lambda : ℝ := 4191153/1000000
def q : ℝ := 70467/100000
def kappa : ℝ := 37483/50000
def widthLo : ℝ := 1/50
def widthHi : ℝ := 7/250
def widthMesh : ℝ := 1/100000000
def lowReserve : ℝ := 1/4000000
def highReserve : ℝ := 11/10000000
def discard : ℝ := 12/1000000000
def frequencyAllowance : ℝ := 1/1000000000
def gap (b : ℝ) : ℝ := B-1+(6*kappa-lambda)*b
def amp (b : ℝ) : ℝ := q*gap b/(6*(kappa-q))+lowReserve/(1-q/kappa)
def total (b : ℝ) : ℝ := B-(lambda-1)*(b-widthMesh)
def supplied (b : ℝ) : ℝ := b-discard
def frequency (b : ℝ) : ℝ := 1-6*amp b-frequencyAllowance
def highBase (b d : ℝ) : ℝ := 1-Saturated.rho d-d*total b-amp b*(5-6*Saturated.rho d)
def channel (b d : ℝ) : Fin 6→ℝ :=
  ![highBase b d+(d-3/19)*supplied b,
    highBase b d+(d-4*Saturated.rho d+5/4)*supplied b,
    highBase b d+Saturated.slope d 0*supplied b+Saturated.offset d 0*frequency b,
    highBase b d+Saturated.slope d 1*supplied b+Saturated.offset d 1*frequency b,
    highBase b d+Saturated.slope d 2*supplied b+Saturated.offset d 2*frequency b,
    highBase b d+Saturated.slope d 3*supplied b+Saturated.offset d 3*frequency b]

theorem low_identity (b : ℝ) : amp b-q/(6*kappa)*(gap b+6*amp b)=lowReserve := by
  norm_num [amp,gap,q,kappa,lowReserve,B,lambda]
  ring

theorem source_guards {b : ℝ} (hb : b∈Set.Icc widthLo widthHi) :
    0 < gap b ∧ 1/100000 ≤ amp b ∧ amp b < 1/75 ∧
    total b+9*amp b < 1 ∧ total b+(9/2)*amp b < 49/50 ∧
    0 < supplied b ∧ supplied b < 1/25 ∧
    2*supplied b < frequency b ∧ frequency b < 1 := by
  rcases hb with ⟨hlo,hhi⟩
  norm_num [gap,amp,total,supplied,frequency,B,lambda,q,kappa,lowReserve,
    widthMesh,discard,frequencyAllowance,widthLo,widthHi] at *
  repeat' constructor
  all_goals linarith

theorem error_reserves {b : ℝ} (hb : b∈Set.Icc widthLo widthHi) :
    1/1000000 < amp b/4-gap b/6 ∧
    1/1000000 < 13*amp b/4-gap b/6 ∧
    1/1000000 < 4*amp b-gap b/6 := by
  rcases hb with ⟨hlo,hhi⟩
  norm_num [gap,amp,B,lambda,q,kappa,lowReserve,widthLo,widthHi] at *
  repeat' constructor
  all_goals linarith

/-- A selected subset below the extended width interval satisfies the old gate.
Above it the auxiliary source applies. No lower selected-width assertion is needed. -/
theorem selected_width_gate {m w : ℝ}
    (hm : m ≤ (B-lambda*(3/125))/2) (hw : 0 ≤ w)
    (hcap : w ≤ min (7/250) ((B-2*m)/lambda)) :
    2*m+(9/2)*w ≤ 1 ∨ (w∈Set.Icc widthLo widthHi ∧ 2*m+lambda*w ≤ B) := by
  by_cases hlo : w < widthLo
  · left
    norm_num [B,lambda,widthLo] at *
    linarith
  · right
    refine ⟨⟨le_of_not_gt hlo,le_trans hcap (min_le_left _ _)⟩,?_⟩
    have hp : 0 < lambda := by norm_num [lambda]
    have hh := (le_div_iff₀ hp).mp (hcap.trans (min_le_right _ _))
    linarith

end Sil.Uneven.AuxiliarySource
