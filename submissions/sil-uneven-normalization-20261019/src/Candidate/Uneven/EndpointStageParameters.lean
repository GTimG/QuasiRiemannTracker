import Candidate.Uneven.WarmupRowsBase
import Candidate.Uneven.RoundedRowsBase
import Candidate.Uneven.MainCountWindows

/- Original module: Candidate.Uneven.WarmupPhysicalGuards. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact physical shortening and continuation margins at the rational endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Sil.Uneven.WarmupRows

def upper_padding : ℝ := 1/10000000000

def physicalGuard (g : ℕ) : ℝ :=
  let x := 1+ell-h
  let dm := h-3/2000
  let dp := h+upper_padding
  let c := (399999/10000000:ℝ)
  let B := planeB 6
  let L := planeLambda 6
  let lo := 1-y/dm
  let hi := 1-y/dp+3/2000
  let clo := (B-2*hi)/L
  let chi := (B-2*lo)/L
  match g with
  | 0 => theta-874/1000
  | 1 => 7/8-theta
  | 2 => ell-1672/10000
  | 3 => 1674/10000-ell
  | 4 => h-793/1000
  | 5 => 798/1000-h
  | 6 => y-458/1000
  | 7 => 463/1000-y
  | 8 => x-ell
  | 9 => y-x
  | 10 => 2*x-y
  | 11 => 1/2-y
  | 12 => h-1/2
  | 13 => 2*y-h
  | 14 => ell-1/6
  | 15 => 1/5-ell
  | 16 => h-4*ell
  | 17 => y/dm-1/2
  | 18 => 99-y/(1/200)
  | 19 => (42/10)*ell-y
  | 20 => y/2-h*(17/50-1/6)-1/50-7/100
  | 21 => y/20-(1+h)/1000-1/4000
  | 22 => h/600-1/1000-1/4000
  | 23 => ell/dp-1/5
  | 24 => dm-1/2
  | 25 => 1-dp
  | 26 => 2*y/dp-1
  | 27 => 1/6-(2*y/dm-1)
  | 28 => (8/10)*(1-6*(1/100))-3/4
  | 29 => lo-405/1000
  | 30 => 4224/10000-hi
  | 31 => clo-365/10000
  | 32 => 38/1000-chi
  | 33 => L-2
  | 34 => 1-405/1000-B/2-(9-L)*(4/100)/2
  | 35 => (7/18-1/500)*(3/2000)+(1-B)/18+(L/18-1/4)*c
  | _ => 0



end Sil.Uneven.WarmupRows
end

/- Original module: Candidate.Uneven.RoundedPhysicalGuards. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Exact physical shortening and continuation margins at the rational endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Sil.Uneven.RoundedRows

def physicalGuard (g : ℕ) : ℝ :=
  let x := 1+ell-h
  let dm := h-3/2000
  let dp := h+upper_padding
  let c := (399999/10000000:ℝ)
  let B := planeB 6
  let L := planeLambda 6
  let lo := 1-y/dm
  let hi := 1-y/dp+3/2000
  let clo := (B-2*hi)/L
  let chi := (B-2*lo)/L
  match g with
  | 0 => theta-874/1000
  | 1 => 7/8-theta
  | 2 => ell-1672/10000
  | 3 => 1674/10000-ell
  | 4 => h-793/1000
  | 5 => 798/1000-h
  | 6 => y-458/1000
  | 7 => 463/1000-y
  | 8 => x-ell
  | 9 => y-x
  | 10 => 2*x-y
  | 11 => 1/2-y
  | 12 => h-1/2
  | 13 => 2*y-h
  | 14 => ell-1/6
  | 15 => 1/5-ell
  | 16 => h-4*ell
  | 17 => y/dm-1/2
  | 18 => 99-y/(1/200)
  | 19 => (42/10)*ell-y
  | 20 => y/2-h*(17/50-1/6)-1/50-7/100
  | 21 => y/20-(1+h)/1000-1/4000
  | 22 => h/600-1/1000-1/4000
  | 23 => ell/dp-1/5
  | 24 => dm-1/2
  | 25 => 1-dp
  | 26 => 2*y/dp-1
  | 27 => 1/6-(2*y/dm-1)
  | 28 => (8/10)*(1-6*(1/100))-3/4
  | 29 => lo-405/1000
  | 30 => 4224/10000-hi
  | 31 => clo-365/10000
  | 32 => 38/1000-chi
  | 33 => L-2
  | 34 => 1-405/1000-B/2-(9-L)*(4/100)/2
  | 35 => (7/18-1/500)*(3/2000)+(1-B)/18+(L/18-1/4)*c
  | _ => 0



end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.EndpointStageParameters. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.UnevenEndpoint
noncomputable section

/-- This configuration contains only a finite stage, never an analytic premise. -/
class Configuration where
  stage : MainCount.Stage

inductive SourcePlane where
  | A | C
  deriving DecidableEq

instance : Fintype SourcePlane := ⟨{.A,.C}, by intro P; cases P <;> simp⟩

variable [config : Configuration]

def theta : ℝ := match config.stage with
  | .warmup => Sil.Uneven.WarmupRows.theta
  | .final => Sil.Uneven.RoundedRows.theta
def h : ℝ := match config.stage with
  | .warmup => Sil.Uneven.WarmupRows.h
  | .final => Sil.Uneven.RoundedRows.h
def incumbent : ℝ := match config.stage with
  | .warmup => 87483/100000
  | .final => 4374143/5000000
def upperPadding : ℝ := match config.stage with
  | .warmup => 1/10000000000
  | .final => 1/10000000000000000
def reserve : ℝ := match config.stage with
  | .warmup => 1/10000000
  | .final => 1/20000000000000

def ell : ℝ := 11/3-4*theta
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def dMinus : ℝ := h-3/2000
def dPlus : ℝ := h+upperPadding
def frozenKappa : ℝ := 2*incumbent-1
def kappaStar : ℝ := 2*theta-1
def kappa0 : ℝ := 93709/125000
def plainKappa : ℝ := 3/4
def slotClip : ℝ := 399999/10000000
def physicalSwitch : ℝ := 3/2000
def plainLower : ℝ := 81/200
def plainUpper : ℝ := 45/100
def widthLower : ℝ := 17/500
def widthUpper : ℝ := 1/25
def countBuffer : ℝ := reserve/1000
def countLoss : ℝ := reserve/100
def effectiveReserve : ℝ := 99*reserve/100

namespace SourcePlane
def mainPlane (P : SourcePlane) : Sil.Uneven.MainSource.Plane :=
  match config.stage,P with
  | .warmup,.A => .A2 | .warmup,.C => .C2
  | .final,.A => .A | .final,.C => .C
def B (P : SourcePlane) : ℝ := P.mainPlane.B
def lambda (P : SourcePlane) : ℝ := P.mainPlane.lambda

theorem mainPlane_incumbent (P : SourcePlane) :
    P.mainPlane.incumbent=frozenKappa := by
  cases config with
  | mk stage => cases stage <;> cases P <;>
      norm_num [mainPlane,frozenKappa,incumbent,Sil.Uneven.MainSource.Plane.incumbent]
end SourcePlane

theorem parameter_gates :
    (874/1000:ℝ) < theta ∧ theta < incumbent ∧ incumbent ≤ 7/8 ∧
    1/6 < ell ∧ ell < 1/5 ∧ 1/2 < dMinus ∧ dMinus < dPlus ∧ dPlus < 1 ∧
    0 < y ∧ y < 1/2 ∧ dPlus < 2*y ∧
    7/10 < frozenKappa ∧ frozenKappa ≤ kappa0 ∧
    0 < reserve ∧ 0 < countBuffer ∧ 0 < effectiveReserve := by
  cases config with
  | mk stage => cases stage <;>
      norm_num [theta,h,incumbent,ell,y,dMinus,dPlus,upperPadding,frozenKappa,kappa0,
        reserve,countBuffer,effectiveReserve,
        Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,
        Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h]


end
end OAI.SevenEighths.UnevenEndpoint
end
