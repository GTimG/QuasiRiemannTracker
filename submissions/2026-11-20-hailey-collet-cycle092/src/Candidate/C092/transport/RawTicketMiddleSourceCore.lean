/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The TRUE P.1 source width, before count/tangent cancellation. Its open quota
and early source mesh are independent of the desired mixed return price. -/
import Candidate.C092.transport.RawTicketAdmission
import Candidate.C092.transport.StrongPairLowMetadata
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle090 QRH.Cycle092.Mixed QRH.Cycle092.StrongPair

/-- The permitted earlier analytic P.1 source, on its authentic ordered domain.
This does not contain any mixed packet, count or desired price estimate. -/
def EarlierP1 : Prop := ∀ n y : ℝ,sourceY0≤ y → y≤ sourceY → y≤ n → n≤ sourceRatio*y → PairOpenWidth n y

theorem true_source_width_bounds {n z : ℝ} (hn : nLo≤ n ∧ n≤ nHi)
    (hz : widthLo≤ z ∧ z≤ widthHi) :
    (9/100:ℝ)≤ QRH.Cycle090.sourceWidth n z ∧ QRH.Cycle090.sourceWidth n z≤11/100 := by
  have hzy : z≤ sourceY := hz.2.trans width_corridor.2.2.2.le
  have hzy0 : sourceY0≤ z := width_corridor.1.le.trans hz.1
  have hlow:=sourceGain_antitone hzy (le_refl sourceY)
  rw [source_native_value] at hlow
  have hhigh:=sourceGain_antitone hzy0 hzy
  have hgain : sourceGain sourceY0=(4370430517/2000000000000:ℝ) := by
    norm_num [sourceGain,sourceY0,sourceSeam,upperGain,lowerGain,sourceY]
  rw [hgain] at hhigh
  dsimp [QRH.Cycle090.sourceWidth]
  norm_num [nLo,nHi] at hn
  norm_num [widthLo,widthHi] at hz
  constructor <;> linarith only [hn.1,hn.2,hz.1,hz.2,hlow,hhigh]

theorem true_source_ordered_domain {n z : ℝ} (hn : nLo≤ n ∧ n≤ nHi)
    (hz : widthLo≤ z ∧ z≤ widthHi) :
    sourceY0≤ z ∧ z≤ sourceY ∧ z≤ n ∧ n≤ sourceRatio*z := by
  have hzy : z≤ sourceY := hz.2.trans width_corridor.2.2.2.le
  have hzy0 : sourceY0≤ z := width_corridor.1.le.trans hz.1
  refine ⟨hzy0,hzy,?_,?_⟩
  · norm_num [nLo] at hn
    norm_num [widthHi] at hz
    linarith only [hn.1,hz.2]
  · norm_num [nHi] at hn
    norm_num [widthLo,sourceRatio] at hz ⊢
    linarith only [hn.2,hz.1]

/-- A literal positive decrement opens the true source quota, and its width
is below the full original slot supply 7/37, without any price premise. -/
theorem true_source_quota {n z decrement : ℝ} (hn : nLo≤ n ∧ n≤ nHi)
    (hz : widthLo≤ z ∧ z≤ widthHi) (hd : 0< decrement ∧ decrement≤1/1000) :
    let l:=QRH.Cycle090.sourceWidth n z-decrement
    0≤ l ∧ l< QRH.Cycle090.sourceWidth n z ∧ l≤7/37 := by
  have hw:=true_source_width_bounds hn hz
  dsimp only
  constructor;· linarith only [hw.1,hd.2]
  constructor <;> linarith only [hw.2,hd.1]

/-- P.1 chooses the early mesh before ANY actual slot set, ray dictionary,
profiles, heights or finite rows; the original PairUnitBox quantifiers remain. -/
theorem true_source_early_mesh (hP1 : EarlierP1) {n z decrement epsilon : ℝ}
    (hn : nLo≤ n ∧ n≤ nHi) (hz : widthLo≤ z ∧ z≤ widthHi)
    (hd : 0< decrement ∧ decrement≤1/1000) (he : 0< epsilon) :
    ∃ mesh : ℝ,0< mesh ∧ PairUnitBox n z
      (QRH.Cycle090.sourceWidth n z-decrement) mesh epsilon := by
  rcases true_source_ordered_domain hn hz with ⟨hy0,hy,hnz,hr⟩
  have hq:=true_source_quota hn hz hd
  exact hP1 n z hy0 hy hnz hr _ hq.1 hq.2.1 epsilon he

/-- Increasing the long label makes its TRUE quota smaller. Thus the same
quota remains open at the original comparison label. -/
theorem source_width_reference_mono {old n z : ℝ} (ho : old≤ n) :
    QRH.Cycle090.sourceWidth n z≤ QRH.Cycle090.sourceWidth old z := by
  dsimp [QRH.Cycle090.sourceWidth]
  linarith only [ho]

/-- One early mesh covers BOTH compared labels and all their actual slots.
No new source assumption is introduced by changing the long reference. -/
theorem compared_labels_early_mesh (hP1 : EarlierP1) {old n z decrement epsilon : ℝ}
    (hOld : nLo≤ old ∧ old≤ nHi) (hn : nLo≤ n ∧ n≤ nHi) (ho : old≤ n)
    (hz : widthLo≤ z ∧ z≤ widthHi) (hd : 0< decrement ∧ decrement≤1/1000)
    (he : 0< epsilon) :
    ∃ mesh : ℝ,0< mesh ∧
      PairUnitBox old z (QRH.Cycle090.sourceWidth n z-decrement) mesh epsilon ∧
      PairUnitBox n z (QRH.Cycle090.sourceWidth n z-decrement) mesh epsilon := by
  have hq:=true_source_quota hn hz hd
  have hOldDomain:=true_source_ordered_domain hOld hz
  have hOpenOld : QRH.Cycle090.sourceWidth n z-decrement< QRH.Cycle090.sourceWidth old z :=
    hq.2.1.trans_le (source_width_reference_mono ho)
  obtain ⟨m₀,hm₀,hs₀⟩:=hP1 old z hOldDomain.1 hOldDomain.2.1 hOldDomain.2.2.1 hOldDomain.2.2.2
    _ hq.1 hOpenOld epsilon he
  obtain ⟨m₁,hm₁,hs₁⟩:=true_source_early_mesh hP1 hn hz hd he
  exact ⟨min m₀ m₁,lt_min hm₀ hm₁,pairUnit_mesh_mono (min_le_left _ _) hs₀,
    pairUnit_mesh_mono (min_le_right _ _) hs₁⟩

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.true_source_quota
#print axioms QRH.Cycle092.RawTicket.compared_labels_early_mesh
