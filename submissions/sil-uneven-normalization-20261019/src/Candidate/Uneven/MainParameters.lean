/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Parameters for the two final uneven sources. The incumbent premise is separate. -/
import Candidate.Uneven.BootstrapCoefficients
import Candidate.Uneven.SaturatedGain

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.MainSource

inductive Plane where
  | A | C | A2 | C2
  deriving DecidableEq

instance : Fintype Plane := ⟨{.A, .C, .A2, .C2}, by intro P; cases P <;> simp⟩

namespace Plane
def B : Plane → ℝ
  | .A => 49061544613/50000000000
  | .C => 97851371081/100000000000
  | .A2 => 2453191/2500000
  | .C2 => 9787409/10000000
def lambda : Plane → ℝ
  | .A => 1891221821/500000000
  | .C => 18557733993/5000000000
  | .A2 => 7567449/2000000
  | .C2 => 37174059/10000000
def q : Plane → ℝ
  | .A => 64883/100000
  | .C => 15987/25000
  | .A2 => 649/1000
  | .C2 => 2561/4000
def incumbent : Plane → ℝ
  | .A | .C => 1874143/2500000
  | .A2 | .C2 => 37483/50000
end Plane

def kappa : ℝ := 1874143/2500000
def widthLo : ℝ := 17/500
def widthHi : ℝ := 1/25
def widthMesh : ℝ := 1/100000000000
def lowReserve : ℝ := 1/1000000000
def highReserve : ℝ := 1/250000000
def errorReserve : ℝ := 1/100000000
def discard : ℝ := 1/500000000000
def frequencyAllowance : ℝ := 1/1000000000000
def amplifierMinimum : ℝ := 1/100000
def gamma (d : ℝ) : ℝ := d-2/5
def gap (P : Plane) (b : ℝ) : ℝ := P.B-1+(6*P.incumbent-P.lambda)*b
def amp (P : Plane) (b : ℝ) : ℝ :=
  P.q*gap P b/(6*(P.incumbent-P.q))+lowReserve/(1-P.q/P.incumbent)
def total (P : Plane) (b : ℝ) : ℝ := P.B-(P.lambda-1)*(b-widthMesh)
def supplied (b : ℝ) : ℝ := b-widthMesh-discard
def frequency (P : Plane) (b : ℝ) : ℝ := 1-6*amp P b-frequencyAllowance
def highBase (P : Plane) (b d : ℝ) : ℝ :=
  1-Saturated.rho d-d*total P b-amp P b*(5-6*Saturated.rho d)
def bootstrapChannel (P : Plane) (b d : ℝ) (i : Fin 7) : ℝ :=
  highBase P b d+Bootstrap.slope d i*supplied b+Bootstrap.offset d i*frequency P b
def saturatedChannel (P : Plane) (b d : ℝ) (i : Fin 4) : ℝ :=
  highBase P b d+Saturated.slope d i*supplied b+Saturated.offset d i*frequency P b

theorem parameter_gates (P : Plane) :
    31/50 ≤ P.q ∧ P.q < 33/50 ∧ P.q < P.incumbent ∧ 1 < P.lambda ∧
      P.lambda < 6*P.incumbent ∧ P.lambda < 9/2 := by
  cases P <;> norm_num [Plane.q,Plane.lambda,Plane.incumbent]

theorem incumbent_bounds (P : Plane) : 0 < P.incumbent ∧ P.incumbent ≤ 1 := by
  cases P <;> norm_num [Plane.incumbent]

theorem low_identity (P : Plane) (b : ℝ) :
    amp P b-P.q/(6*P.incumbent)*(gap P b+6*amp P b)=lowReserve := by
  cases P <;> norm_num [amp,gap,Plane.q,Plane.incumbent,lowReserve,Plane.B,Plane.lambda] <;> ring

theorem gamma_bounds {d : ℝ} (hd : 31/50 ≤ d) (hu : d ≤ 3/4) :
    0 ≤ gamma d ∧ gamma d ≤ d ∧ 0 ≤ 5-6*Saturated.rho d := by
  have hden : 0 < 3*(5-2*d) := by linarith
  have hp : 27/50 ≤ 10*d/(3*(5-2*d)) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hr : Saturated.rho d ≤ 23/50 := by unfold Saturated.rho; linarith only [hp]
  unfold gamma
  exact ⟨by linarith,by linarith,by linarith only [hr]⟩

theorem scheduling_guards (P : Plane) {b : ℝ} (hb : b∈Set.Icc widthLo widthHi) :
    0 < gap P b ∧ 0 < amplifierMinimum ∧ amplifierMinimum ≤ amp P b ∧
    amp P b < 1/75 ∧ total P b+9*amp P b < 1 ∧
    total P b+4*amp P b < 49/50 ∧ total P b+(9/2)*amp P b < 49/50 ∧
    0 < supplied b ∧ supplied b < 1/25 ∧
    2*supplied b < frequency P b ∧ frequency P b < 1 := by
  rcases hb with ⟨hlo,hhi⟩
  cases P <;>
    norm_num [gap,amp,total,supplied,frequency,Plane.B,Plane.lambda,Plane.q,Plane.incumbent,
      amplifierMinimum,lowReserve,widthMesh,discard,frequencyAllowance,widthLo,widthHi] at *
  all_goals repeat' constructor
  all_goals linarith

theorem error_reserves (P : Plane) {b : ℝ} (hb : b∈Set.Icc widthLo widthHi) :
    errorReserve < amp P b/4-gap P b/6 ∧
    errorReserve < 13*amp P b/4-gap P b/6 ∧
    errorReserve < 4*amp P b-gap P b/6 := by
  rcases hb with ⟨hlo,hhi⟩
  cases P <;> norm_num [gap,amp,Plane.B,Plane.lambda,Plane.q,Plane.incumbent,
    lowReserve,errorReserve,widthLo,widthHi] at *
  all_goals repeat' constructor
  all_goals linarith

end Sil.Uneven.MainSource
