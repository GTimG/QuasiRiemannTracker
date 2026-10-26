/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual HighSourceParameters constructor, after the density degree is fixed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalAnalyticParameters

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalAnalytic
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open scoped ContDiff

def physicalHeightLoss (θ dmin εslot : ℝ) : ℝ :=
  min (θ/16) (min (dmin/4) (min (dmin*(θ/16)/4) (dmin*(εslot/4)/2)))

theorem physicalHeightLoss_pos {θ dmin εslot : ℝ}
    (hθ : 0<θ) (hdmin : 0<dmin) (hes : 0<εslot) :
    0<physicalHeightLoss θ dmin εslot := by
  dsimp [physicalHeightLoss]
  positivity

theorem physical_height_spec (J : ℕ) (θ dmin d εslot : ℝ)
    (hθ : 0<θ) (hdmin : 0<dmin) (hd : 0<d) (hes : 0<εslot) :
    let τ:=highHeight J (physicalHeightLoss θ dmin εslot) d εslot (θ/16)
    0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*(θ/16) ∧ 2*τ<dmin*(εslot/4) ∧
      16*τ≤d*((θ/16)/8) ∧ 8*τ≤d*εslot ∧ 2*τ*(J+1)≤θ/16 := by
  let loss:=physicalHeightLoss θ dmin εslot
  have hloss : 0<loss:=physicalHeightLoss_pos hθ hdmin hes
  have h:=high_height_losses J loss d εslot (θ/16) hloss hd hes (by positivity)
  have h₁ : loss≤θ/16:=min_le_left _ _
  have h₂ : loss≤dmin/4:=(min_le_right _ _).trans (min_le_left _ _)
  have h₃ : loss≤dmin*(θ/16)/4:=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₄ : loss≤dmin*(εslot/4)/2:=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  dsimp only
  have ht : highHeight J loss d εslot (θ/16)≤loss/2 := by
    nlinarith only [h.2.1,mul_nonneg h.1.le (Nat.cast_nonneg J)]
  refine ⟨h.1,?_,?_,?_,h.2.2.1,h.2.2.2,?_⟩
  · nlinarith only [ht,h₂,hdmin]
  · nlinarith only [ht,h₃,mul_pos hdmin (show 0<θ/16 by positivity)]
  · nlinarith only [ht,h₄,mul_pos hdmin (show 0<εslot/4 by positivity)]
  · nlinarith only [h.2.1,h₁]

/-- This uses the existing constructor with its literal buffer and kappa.
The Mellin profile bound is the previously checked bound supplied by the
cofactor theorem; no new profile majorant is chosen here. -/
def actualPhysicalParameters (W : ℝ→ℂ)
    (Rwidth Rplain εslot θ bΦ Mcap Bmask margin d dmin : ℝ)
    (J : ℕ) (bound : ℕ→ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hRw : 0≤Rwidth) (hRp : 0≤Rplain) (hes : 0<εslot) (hθ : 0<θ)
    (hbΦ : 0≤bΦ) (hmargin : 0<margin) (hd : 0<d) (hdmin : 0<dmin)
    (hsupply : Mcap+Bmask+margin≤d) (hbound : ∀k,0≤bound k) : HighSourceParameters :=
  highParameters W 1 2 Rwidth Rplain εslot (θ/16) (33/50) (33/50) bΦ Mcap Bmask margin d
    (physicalHeightLoss θ dmin εslot) J bound (by norm_num) hWs hW hRw hRp hes
    (by positivity) hbΦ hmargin hd hsupply (physicalHeightLoss_pos hθ hdmin hes) hbound

theorem actualPhysicalParameters_spec (W : ℝ→ℂ)
    (Rwidth Rplain εslot θ bΦ Mcap Bmask margin d dmin : ℝ)
    (J : ℕ) (bound : ℕ→ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hRw : 0≤Rwidth) (hRp : 0≤Rplain) (hes : 0<εslot) (hθ : 0<θ)
    (hbΦ : 0≤bΦ) (hmargin : 0<margin) (hd : 0<d) (hdmin : 0<dmin)
    (hsupply : Mcap+Bmask+margin≤d) (hbound : ∀k,0≤bound k) :
    let P:=actualPhysicalParameters W Rwidth Rplain εslot θ bΦ Mcap Bmask margin d dmin J bound
      hWs hW hRw hRp hes hθ hbΦ hmargin hd hdmin hsupply hbound
    P.Wslot=W ∧ P.B₀=2 ∧ P.profileBound=bound ∧ P.εslot=εslot ∧ P.εplain=θ/16 ∧
      P.e=highBuffer Rwidth Rplain εslot (θ/16) ∧ P.κ=highKappa εslot (θ/16) ∧
      P.σmin=33/50 ∧ P.σmax=33/50 ∧
      P.τ<dmin/2 ∧ 4*P.τ<dmin*(θ/16) ∧ 2*P.τ<dmin*(εslot/4) ∧
      16*P.τ≤P.d*P.vplain ∧ 8*P.τ≤P.d*P.vslot ∧ 2*P.τ*(J+1)≤θ/16 := by
  have h:=physical_height_spec J θ dmin d εslot hθ hdmin hd hes
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,h.2⟩

end
end QRH.Record1252270103Source.PhysicalAnalytic
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.physicalHeightLoss
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.physicalHeightLoss_pos
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.physical_height_spec
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.actualPhysicalParameters
#print axioms QRH.Record1252270103Source.PhysicalAnalytic.actualPhysicalParameters_spec
