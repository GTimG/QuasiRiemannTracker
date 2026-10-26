/- The fixed record uses the exact rational certificates, rather than an
identity with the preceding optimizer. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Bernstein.Endpoint
import Candidate.Research.RecursiveAffine.TopRows
import Candidate.Research.RecursiveAffine.JunctionOldRows

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace Cycle153Endpoint.Arithmetic.Bernstein
noncomputable section
open scoped Classical

/-- Literal identification of the old-count certificate, with no parameter
optimization or numerical inference. -/
theorem old_certificate_identity (L C saving d p:ℝ) :
    Cycle153.Consumer.oldCleared L C saving d p=8*clearedPolynomial L C saving d p := by
  unfold Cycle153.Consumer.oldCleared Cycle153.Consumer.J Cycle153.Consumer.D
    Cycle153.Consumer.P Cycle153.Consumer.V Cycle153.Consumer.common
    clearedPolynomial clearedDenominator detectorV detectorD detectorP
  simp only [theta,h,y,ell,kappaStar,lambda,B,Cycle153.Consumer.theta,
    Cycle153.Consumer.h,Cycle153.Consumer.y,Cycle153.Consumer.ell,Cycle153.Consumer.kappaStar,
    OAI.SevenEighths.Cycle153Geometry.Coordinates.top,Cycle153.MarkedRootPrice.top]
  ring

/-- The affine closed-form certificate is precisely four times its
positive-denominator row margin. -/
theorem affine_certificate_identity (L C saving d p:ℝ) :
    Cycle153.Consumer.affineCleared L C saving d p=
      4*(CountAffine.tDen d p*(theta-saving-((1+d)/2+13*h/75-y/2-ell/2+ell*d*p+
        L*(1/4-17/50)-d*p*C/2))-3*L/4*(CountAffine.tDen d p/6+(5/6-d)*CountAffine.tNum d p)) := by
  unfold Cycle153.Consumer.affineCleared Cycle153.Consumer.affineD Cycle153.Consumer.affineN
    Cycle153.Consumer.affineSI Cycle153.Consumer.affineSP Cycle153.Consumer.affineA
    Cycle153.Consumer.common Cycle153.Consumer.V
    CountAffine.tDen CountAffine.tNum CountAffine.sI CountAffine.sP CountAffine.aP
  simp only [theta,h,y,ell,kappaStar,lambda,B,Cycle153.Consumer.theta,
    Cycle153.Consumer.h,Cycle153.Consumer.y,Cycle153.Consumer.ell,Cycle153.Consumer.kappaStar,
    OAI.SevenEighths.Cycle153Geometry.Coordinates.top,Cycle153.MarkedRootPrice.top]
  ring

theorem capped_certificate_identity (L C saving d p:ℝ) :
    Cycle153.Consumer.cappedCleared L C saving d p=
      4*(CountAffine.tDenC d p*(theta-saving-((1+d)/2+13*h/75-y/2-ell/2+ell*d*p+
        L*(1/4-17/50)-d*p*C/2))-3*L/4*(CountAffine.tDenC d p/6+(5/6-d)*CountAffine.tNumC d p)) := by
  unfold Cycle153.Consumer.cappedCleared Cycle153.Consumer.cappedD Cycle153.Consumer.cappedN
    Cycle153.Consumer.cappedSP Cycle153.Consumer.cappedA Cycle153.Consumer.affineSI
    Cycle153.Consumer.common Cycle153.Consumer.V
    CountAffine.tDenC CountAffine.tNumC CountAffine.sI CountAffine.sPc CountAffine.aPc
  simp only [theta,h,y,ell,kappaStar,lambda,B,Cycle153.Consumer.theta,
    Cycle153.Consumer.h,Cycle153.Consumer.y,Cycle153.Consumer.ell,Cycle153.Consumer.kappaStar,
    OAI.SevenEighths.Cycle153Geometry.Coordinates.top,Cycle153.MarkedRootPrice.top]
  ring

theorem plain_certificate_identity (L C saving d p:ℝ) :
    Cycle153.Consumer.plainMargin L C saving d p=
      theta-saving-rowExponentR L C (CountAffine.plainOld kappaStar d p CountAffine.plainTop) d p := by
  unfold Cycle153.Consumer.plainMargin Cycle153.Consumer.plain Cycle153.Consumer.common
    rowExponentR CountAffine.plainOld CountAffine.plainTop
  simp only [theta,h,y,ell,kappaStar,lambda,B,Cycle153.Consumer.theta,
    Cycle153.Consumer.h,Cycle153.Consumer.y,Cycle153.Consumer.ell,Cycle153.Consumer.kappaStar,
    OAI.SevenEighths.Cycle153Geometry.Coordinates.top,Cycle153.MarkedRootPrice.top]
  ring

theorem topOld_outside {d p:ℝ} (hd:d∈Set.Icc 0 (3/4))(hp:p∈Set.Icc 0 (1/2))
    (hreg:¬CountAffine.inRegion d p) : 0< clearedPolynomial h (newCapacity h) topSaving d p := by
  have hc : 0< Cycle153.Consumer.oldCleared h (newCapacity h) topSaving d p := by
    rcases outside_cases hd hp hreg with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
    · exact Cycle153.Consumer.top_old_outside_0 h1 h2
    · exact Cycle153.Consumer.top_old_outside_2 h1 h2
    · exact Cycle153.Consumer.top_old_outside_1 h1 h2
  rw [old_certificate_identity] at hc
  linarith

theorem junctionOld_outside {d p:ℝ} (hd:d∈Set.Icc 0 (3/4))(hp:p∈Set.Icc 0 (1/2))
    (hreg:¬CountAffine.inRegion d p) : 0< clearedPolynomial dMinus (oldCapacity dMinus) rowSaving d p := by
  rw [oldCapacity_junction]
  have hc : 0< Cycle153.Consumer.oldCleared dMinus ((2*y-dMinus)/(6*kappaStar)) rowSaving d p := by
    rcases outside_cases hd hp hreg with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
    · exact Cycle153.Consumer.junction_old_old_outside_0 h1 h2
    · exact Cycle153.Consumer.junction_old_old_outside_2 h1 h2
    · exact Cycle153.Consumer.junction_old_old_outside_1 h1 h2
  rw [old_certificate_identity] at hc
  linarith

theorem top_RStar_region {d p:ℝ}(hr:CountAffine.inRegion d p) :
    rowExponentR h (newCapacity h) (CountAffine.RStar d p) d p< theta-topSaving := by
  have hs : 0<Cycle153.Consumer.affineCleared h (newCapacity h) topSaving d p := Cycle153.Consumer.top_affine (CountAffine.region_mem hr).1 (CountAffine.region_mem hr).2
  rw [affine_certificate_identity] at hs
  exact rstar_row_of_pos hr (by linarith)

theorem top_RStarC_region {d p:ℝ}(hr:CountAffine.inRegion d p) :
    rowExponentR h (newCapacity h) (CountAffine.RStarC d p) d p< theta-topSaving := by
  have hs : 0<Cycle153.Consumer.cappedCleared h (newCapacity h) topSaving d p := Cycle153.Consumer.top_capped (CountAffine.region_mem hr).1 (CountAffine.region_mem hr).2
  rw [capped_certificate_identity] at hs
  exact rstarC_row_of_pos hr (by linarith)

theorem top_plainTop_region {d p:ℝ}(hr:CountAffine.inRegion d p) :
    rowExponentR h (newCapacity h) (CountAffine.plainOld kappaStar d p CountAffine.plainTop) d p< theta-topSaving := by
  have hs : 0<Cycle153.Consumer.plainMargin h (newCapacity h) topSaving d p := Cycle153.Consumer.top_plain (CountAffine.region_mem hr).1 (CountAffine.region_mem hr).2
  rw [plain_certificate_identity] at hs
  linarith

theorem junction_RStar_region {d p:ℝ}(hr:CountAffine.inRegion d p) :
    rowExponentR dMinus (oldCapacity dMinus) (CountAffine.RStar d p) d p< theta-rowSaving := by
  rw [oldCapacity_junction]
  have hs : 0<Cycle153.Consumer.affineCleared dMinus ((2*y-dMinus)/(6*kappaStar)) rowSaving d p := Cycle153.Consumer.junction_old_affine (CountAffine.region_mem hr).1 (CountAffine.region_mem hr).2
  rw [affine_certificate_identity] at hs
  exact rstar_row_of_pos hr (by linarith)

theorem junction_RStarC_region {d p:ℝ}(hr:CountAffine.inRegion d p) :
    rowExponentR dMinus (oldCapacity dMinus) (CountAffine.RStarC d p) d p< theta-rowSaving := by
  rw [oldCapacity_junction]
  have hs : 0<Cycle153.Consumer.cappedCleared dMinus ((2*y-dMinus)/(6*kappaStar)) rowSaving d p := Cycle153.Consumer.junction_old_capped (CountAffine.region_mem hr).1 (CountAffine.region_mem hr).2
  rw [capped_certificate_identity] at hs
  exact rstarC_row_of_pos hr (by linarith)

theorem junction_plainTop_region {d p:ℝ}(hr:CountAffine.inRegion d p) :
    rowExponentR dMinus (oldCapacity dMinus) (CountAffine.plainOld kappaStar d p CountAffine.plainTop) d p< theta-rowSaving := by
  rw [oldCapacity_junction]
  have hs : 0<Cycle153.Consumer.plainMargin dMinus ((2*y-dMinus)/(6*kappaStar)) rowSaving d p := Cycle153.Consumer.junction_old_plain (CountAffine.region_mem hr).1 (CountAffine.region_mem hr).2
  rw [plain_certificate_identity] at hs
  linarith

theorem new_row_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent h δ p < theta-topSaving := by
  have hh : (0:ℝ) ≤ h := by linarith [h_bounds.1]
  unfold newExponent
  by_cases hreg : CountAffine.inRegion δ p
  · exact region_row_bound hh hreg (top_RStar_region hreg) (top_RStarC_region hreg)
      (top_plainTop_region hreg)
  · have he : rowExponent h (newCapacity h) δ p =
        rowExponentR h (newCapacity h) (detectorROld δ p) δ p := by
      unfold rowExponent detectorR
      rw [ite_eq_right hreg]
    rw [he]
    exact old_saving_of_cleared_pos hδ hp (topOld_outside hδ hp hreg)

theorem old_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent dMinus δ p < theta-rowSaving := by
  have hd : (0:ℝ) ≤ dMinus := by linarith [half_lt_dMinus]
  unfold oldExponent
  by_cases hreg : CountAffine.inRegion δ p
  · exact region_row_bound hd hreg (junction_RStar_region hreg) (junction_RStarC_region hreg)
      (junction_plainTop_region hreg)
  · have he : rowExponent dMinus (oldCapacity dMinus) δ p =
        rowExponentR dMinus (oldCapacity dMinus) (detectorROld δ p) δ p := by
      unfold rowExponent detectorR
      rw [ite_eq_right hreg]
    rw [he]
    exact old_saving_of_cleared_pos hδ hp (junctionOld_outside hδ hp hreg)

theorem new_junction_le_old {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dMinus δ p ≤ oldExponent dMinus δ p := by
  have hC := junction_capacity_order
  have hdp := mul_nonneg hδ.1 hp.1
  unfold newExponent oldExponent rowExponent rowExponentR
  nlinarith

theorem new_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dMinus δ p < theta-rowSaving :=
  (new_junction_le_old hδ hp).trans_lt (old_junction_saving hδ hp)

end
end Cycle153Endpoint.Arithmetic.Bernstein

#print axioms Cycle153Endpoint.Arithmetic.Bernstein.new_row_saving
#print axioms Cycle153Endpoint.Arithmetic.Bernstein.old_junction_saving
