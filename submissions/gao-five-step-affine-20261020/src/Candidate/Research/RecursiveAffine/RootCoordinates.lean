/- Literal first-inner coordinates of the actual root LOW source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalPrefixClosure

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open Cycle153Geometry Cycle153ReachableGeometry

def rootCoordinates (b slack V Red ell : ℝ) : Fin 14→ℝ :=
  ![b,V,0,0,0,Red,0,0,0,ell,0,0,0,slack]

theorem rootCoordinates_fields (b slack V Red ell : ℝ) :
    Coordinates.b (rootCoordinates b slack V Red ell)=b ∧
    Coordinates.rootSlack (rootCoordinates b slack V Red ell)=slack ∧
    Coordinates.V0 (rootCoordinates b slack V Red ell)=V ∧
    Coordinates.Red0 (rootCoordinates b slack V Red ell)=Red ∧
    Coordinates.ell0 (rootCoordinates b slack V Red ell)=ell := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem rootCoordinates_nonnegative (b slack V Red ell : ℝ)
    (hs : 0 ≤ slack) (hv : 0 ≤ V) (hr : 0 ≤ Red) (he : 0 ≤ ell) :
    ∀i : Fin 48,35 ≤ i.val→0 ≤ Coordinates.rows i (rootCoordinates b slack V Red ell) := by
  intro i hi
  rcases i with ⟨i,hil⟩
  interval_cases i <;>
    norm_num [Coordinates.rows,Coordinates.row35,Coordinates.row36,Coordinates.row37,Coordinates.row38,
      Coordinates.row39,Coordinates.row40,Coordinates.row41,Coordinates.row42,Coordinates.row43,
      Coordinates.row44,Coordinates.row45,Coordinates.row46,Coordinates.row47,
      Coordinates.V0,Coordinates.V1,Coordinates.V2,Coordinates.V3,
      Coordinates.Red0,Coordinates.Red1,Coordinates.Red2,Coordinates.Red3,
      Coordinates.ell0,Coordinates.ell1,Coordinates.ell2,Coordinates.ell3,
      Coordinates.rootSlack,rootCoordinates] at hi ⊢ <;> assumption

/-- These are exactly the physical source tests available before any
first-inner ledger is built. The next amplifier, unit floor and native
ledger facts are subsequently derived by prefix closure. -/
theorem rootCoordinates_raw (b slack V Red ell : ℝ)
    (hblo : 17/500+Coordinates.mesh ≤ b) (hbhi : b ≤ Coordinates.top)
    (hs : 0 ≤ slack) (hsmesh : slack ≤ Coordinates.mesh)
    (hv : 0 ≤ V) (hr : 0 ≤ Red) (he : 0 ≤ ell)
    (hpaid : -(1/1000000000000000:ℝ) ≤ V+Red-ell)
    (hamp : 0 ≤ Coordinates.a0 (rootCoordinates b slack V Red ell))
    (hwide : Coordinates.mu ≤ Coordinates.U1 (rootCoordinates b slack V Red ell))
    (hactive : 0 < Coordinates.A1 (rootCoordinates b slack V Red ell)+
      (6*Coordinates.kappa-1)*Coordinates.z1 (rootCoordinates b slack V Red ell)-
        Coordinates.U1 (rootCoordinates b slack V Red ell))
    (hplain : 0 ≤ Coordinates.A1 (rootCoordinates b slack V Red ell)-
      Coordinates.z1 (rootCoordinates b slack V Red ell))
    (hslots : 0 ≤ Coordinates.z1 (rootCoordinates b slack V Red ell)) :
    RawPrefixRows (0:Fin 4) (rootCoordinates b slack V Red ell) := by
  have hn:=rootCoordinates_nonnegative b slack V Red ell hs hv hr he
  have hz : 0 ≤ b-slack := by
    have hm : (0:ℝ)<17/500 := by norm_num
    linarith only [hblo,hsmesh,hm]
  have hplainRoot : 0 ≤ Coordinates.A0 (rootCoordinates b slack V Red ell)-
      Coordinates.z0 (rootCoordinates b slack V Red ell) := by
    have hlam : 0 ≤ Coordinates.outerLambda := by norm_num [Coordinates.outerLambda]
    have hb : Coordinates.outerLambda*b ≤ Coordinates.outerLambda*Coordinates.top :=
      mul_le_mul_of_nonneg_left hbhi hlam
    have hs' : 0 ≤ Coordinates.outerLambda*slack := mul_nonneg hlam hs
    have hc : 0 ≤ Coordinates.outerB-Coordinates.outerLambda*Coordinates.top := by
      norm_num [Coordinates.outerB,Coordinates.outerLambda,Coordinates.top]
    change 0 ≤ Coordinates.outerB-(Coordinates.outerLambda-1)*(b-slack)-(b-slack)
    nlinarith only [hb,hs',hc]
  intro i hi hne10 hne11
  by_cases hi35 : 35 ≤ i.val
  · exact le_trans (by norm_num) (hn i hi35)
  · have hil : i.val<14 := by simp only [Fin.val_zero] at hi;omega
    rcases i with ⟨i,hilt⟩
    interval_cases i
    · change -(1/1000000000000000:ℝ) ≤ b-(17/500+Coordinates.mesh)
      linarith only [hblo]
    · change -(1/1000000000000000:ℝ) ≤ Coordinates.top-b
      linarith only [hbhi]
    · change -(1/1000000000000000:ℝ) ≤ Coordinates.mesh-slack
      linarith only [hsmesh]
    · exact le_trans (by norm_num) hamp
    · change -(1/1000000000000000:ℝ) ≤ 1-1/1000000
      norm_num
    · exact le_trans (by norm_num) hplainRoot
    · change -(1/1000000000000000:ℝ) ≤ b-slack
      linarith only [hz]
    · exact hpaid
    · change -(1/1000000000000000:ℝ) ≤
        Coordinates.U1 (rootCoordinates b slack V Red ell)-Coordinates.mu*1
      linarith only [hwide]
    · exact le_trans (by norm_num) hactive.le
    · exact False.elim (hne10 rfl)
    · exact False.elim (hne11 rfl)
    · exact le_trans (by norm_num) hplain
    · exact le_trans (by norm_num) hslots


/-- The actual initial puncture is one. Its native first-step credit
therefore initializes the full history invariant directly, without
restarting from the coarse local cap20. -/
theorem rootCoordinates_puncture_history {logNorm pad b slack V Red ell : ℝ}
    (hcredit : logNorm ≤ V+Red+pad) (hpad : pad ≤ 1/100000000000000000000) :
    logNorm ≤ modelMissing (0:Fin 4) (rootCoordinates b slack V Red ell)+
      modelReduction (0:Fin 4) (rootCoordinates b slack V Red ell)+1/1000000000000000 := by
  change logNorm ≤ V+Red+1/1000000000000000
  linarith only [hcredit,hpad]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.rootCoordinates_raw
