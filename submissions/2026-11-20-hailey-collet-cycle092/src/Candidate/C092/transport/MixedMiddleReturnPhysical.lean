/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Identify the actual bank penalty and count with Q.2 at the genuine contact. -/
import Candidate.C092.transport.MixedMiddleReturnBank
import Candidate.C092.transport.MixedTicketTailsContact
import Candidate.C092.transport.MixedCenteredCertificate
import Candidate.C092.transport.PacketFinalPower

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count Cycle25ProbeFinalAssembly QRH.Cycle092.PacketJoinE49
open QRH.Cycle090 QRH.Cycle092.Mixed QRH.Cycle092.TopData QRH.ContactCertificate
open MixedOffsetCount
local notation "contact" => Qrh.TwoSlot.AnchorContinuum.Contact.theta
variable {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D} {η : Character} {Z : ℝ}

lemma native_count_eq (B : MiddleBank D S η Z) :
    B.R=pairedCount B.delta B.p Return.line.g0 Return.line.g1 := by
  change Return.valueI B.delta B.p=pairedCount B.delta B.p Return.line.g0 Return.line.g1
  unfold Return.valueI Return.NI Return.JI Return.UI Return.kI
    pairedCount pairedN pairedJ pairedV pairedU pairedK
  congr 1 <;> ring

lemma source_cutoff_eq (δ p : ℝ) (hJ : Return.JI δ p ≠ 0) :
    Return.cutoffI δ p=pairedCrossing δ p Return.line.g0 Return.line.g1 := by
  change (Return.JI δ p+δ*Return.UI p)/Return.JI δ p=1+δ*Return.UI p/Return.JI δ p
  rw [add_div,div_self hJ]

lemma native_crossing_eq (B : MiddleBank D S η Z) :
    B.m=pairedCrossing B.delta B.p Return.line.g0 Return.line.g1/3 := by
  calc
    B.m=Return.cutoffI B.delta B.p/3 := congrArg (fun x : ℝ=>x/3) B.baseline_cutoff
    _=pairedCrossing B.delta B.p Return.line.g0 Return.line.g1/3 :=
      congrArg (fun x : ℝ=>x/3) (source_cutoff_eq B.delta B.p (Return.hJ B.available.1 B.available.2).ne')

lemma native_k_eq (B : MiddleBank D S η Z) :
    B.k=pairedK B.p (g1 (wValue contact)) := by
  dsimp [MiddleBank.k,Return.kI,pairedK]
  rw [MixedTicketTails.actual_contact_slope,MixedTicketTails.actual_contact_width]

/-- These are certified geometric bounds on the original true bank, not count
or mixed-gain assumptions. -/
theorem native_directed_guards (B : MiddleBank D S η Z)
    {r : Row} (hr : r∈rows) (hp : r.box.Contains (B.delta,B.p)) :
    0 ≤ (rowKLower r.box:ℝ) ∧ (rowKLower r.box:ℝ) ≤ B.k ∧
    B.k ≤ (rowKUpper r.box:ℝ) ∧ B.m ≤ (rowM r.box:ℝ)+witnessCollar := by
  have hk := ActualMixedPrice.actual_k_bounds hr hp MixedTicketTails.actual_contact_root
  have hm := ActualMixedPrice.actual_crossing_upper hr hp MixedTicketTails.actual_contact_root
  have hsign := MixedCenteredFaces.directed_parameters hr hp
  rw [←native_k_eq B] at hk
  rw [native_crossing_eq B,MixedTicketTails.actual_contact_intercept,
    MixedTicketTails.actual_contact_slope,MixedTicketTails.actual_contact_width]
  exact ⟨hsign.1,hk.1,hk.2,hm.trans (by norm_num [witnessCollar])⟩

/-- Literal metadata matching identifies all three original directed faces.
The preceding long and current ordinary faces keep their native lengths. -/
theorem native_penalty_eq (B : MiddleBank D S η Z) (r : Row)
    (hgamma : B.γ=(rowGamma r.box r.B:ℝ))
    (hcollar : B.εa=witnessCollar)
    (hfactor : B.factor=(rowV r.box:ℝ)/(r.box.uHi:ℝ)) :
    B.penalty (rowKLower r.box) (rowKUpper r.box) ((rowM r.box:ℝ)+witnessCollar)=
      ActualMixedPrice.penalty r B.xi B.currentSlice.fiber.m := by
  dsimp [MiddleBank.penalty,MiddleBank.H,ActualMixedPrice.penalty]
  simp only [hgamma,hcollar,hfactor]

lemma native_gain_eq (B : MiddleBank D S η Z) (r : Row)
    (hgamma : B.γ=(rowGamma r.box r.B:ℝ))
    (hcollar : B.εa=witnessCollar)
    (hfactor : B.factor=(rowV r.box:ℝ)/(r.box.uHi:ℝ)) :
    B.p*(Return.line.g1*B.currentSlice.fiber.m-Return.line.g0/2+sourceGain B.currentSlice.fiber.m)+
      B.penalty (rowKLower r.box) (rowKUpper r.box) ((rowM r.box:ℝ)+witnessCollar)/2-
        B.p*witnessCollar/2 =
      ActualMixedPrice.gain r B.p contact B.xi B.currentSlice.fiber.m := by
  rw [native_penalty_eq B r hgamma hcollar hfactor]
  dsimp [ActualMixedPrice.gain,ActualMixedPrice.sourceWidth]
  rw [MixedTicketTails.actual_contact_intercept,MixedTicketTails.actual_contact_slope,
    MixedTicketTails.actual_contact_width]

/-- The literal original row price is paid at the actual genuine contact,
with Q.2's uniform reserve. No stored terminal debit is an assumption. -/
theorem native_middle_reserve (B : MiddleBank D S η Z)
    {r : Row} (hr : r∈rows) (hp : r.box.Contains (B.delta,B.p))
    {h : ℝ} (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hD : (1/100:ℝ) ≤ B.d) (hDh : B.d ≤ h+rowPad)
    (hgamma : B.γ=(rowGamma r.box r.B:ℝ))
    (hcollar : B.εa=witnessCollar)
    (hfactor : B.factor=(rowV r.box:ℝ)/(r.box.uHi:ℝ))
    (hξ : 0 ≤ B.xi) (hξ' : B.xi ≤ (rowGamma r.box r.B:ℝ))
    (hz : widthLo ≤ B.currentSlice.fiber.m) (hz' : B.currentSlice.fiber.m ≤ widthHi) :
    @SelectedNonfloor.rowPrice (ActualGeometry.parameters h hh hh') B.delta B.p B.R B.d sourceCost-
      B.d*B.delta*(B.p*(Return.line.g1*B.currentSlice.fiber.m-Return.line.g0/2+
        sourceGain B.currentSlice.fiber.m)+
      B.penalty (rowKLower r.box) (rowKUpper r.box) ((rowM r.box:ℝ)+witnessCollar)/2-
        B.p*witnessCollar/2)+paddingDebit+(1/100000000000000:ℝ)<theta-1/1000000000000 := by
  letI := ActualGeometry.parameters h hh hh'
  rw [native_gain_eq B r hgamma hcollar hfactor,native_count_eq B]
  rw [SelectedNonfloor.row_price_at_Q h hh hh' B.delta B.p Return.line.g0 Return.line.g1 B.d (by linarith)]
  rw [MixedTicketTails.actual_contact_intercept,MixedTicketTails.actual_contact_slope,
    MixedTicketTails.actual_contact_width]
  exact physical_reserve hr hh hh' hp MixedTicketTails.actual_contact_root hD hDh hξ hξ' hz hz'

/-- The actual packet exponent reaches the final numerator power. The true
physical reciprocal remains outside this numerator packet, as in K.1. -/
theorem native_middle_power_le_final (B : MiddleBank D S η Z)
    {r : Row} (hr : r∈rows) (hp : r.box.Contains (B.delta,B.p))
    {h : ℝ} (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hD : (1/100:ℝ) ≤ B.d) (hDh : B.d ≤ h+rowPad)
    (hgamma : B.γ=(rowGamma r.box r.B:ℝ))
    (hcollar : B.εa=witnessCollar)
    (hfactor : B.factor=(rowV r.box:ℝ)/(r.box.uHi:ℝ))
    (hξ : 0 ≤ B.xi) (hξ' : B.xi ≤ (rowGamma r.box r.B:ℝ))
    (hz : widthLo ≤ B.currentSlice.fiber.m) (hz' : B.currentSlice.fiber.m ≤ widthHi)
    {fee massEps outerFee v : ℝ} (hv : 0 ≤ v)
    (hfee : B.d*(fee+massEps)+outerFee ≤ paddingDebit+(1/100000000000000:ℝ)) :
    @SelectedNonfloor.packetPower (ActualGeometry.parameters h hh hh') B.a B.p B.R B.d sourceCost 0
      (fee+massEps-B.delta*(B.p*(Return.line.g1*B.currentSlice.fiber.m-Return.line.g0/2+
        sourceGain B.currentSlice.fiber.m)+
      B.penalty (rowKLower r.box) (rowKUpper r.box) ((rowM r.box:ℝ)+witnessCollar)/2-
        B.p*witnessCollar/2)-B.delta*(1-B.p)*v/2) ≤
    @SelectedNonfloor.finalPower (ActualGeometry.parameters h hh hh') B.a B.d sourceCost outerFee
      (theta-1/2000000000000) := by
  letI := ActualGeometry.parameters h hh hh'
  have hprice := native_middle_reserve B hr hp hh hh' hD hDh hgamma hcollar hfactor hξ hξ' hz hz'
  have hp' : B.p ≤ 1 := B.available.2.2.trans (by norm_num)
  have hdamp : 0 ≤ B.delta*(1-B.p)*v/2 := div_nonneg
    (mul_nonneg (mul_nonneg B.delta_pos.le (sub_nonneg.mpr hp')) hv) (by norm_num)
  have hd : 0 < B.d := by linarith
  apply (SelectedNonfloor.power_le_final_iff B.a B.p B.R B.d sourceCost 0 _ outerFee
    (theta-1/2000000000000) hd).2
  change @SelectedNonfloor.rowPrice (ActualGeometry.parameters h hh hh') B.delta B.p B.R B.d sourceCost+
    B.d*(0/4+(fee+massEps-B.delta*(B.p*(Return.line.g1*B.currentSlice.fiber.m-Return.line.g0/2+
      sourceGain B.currentSlice.fiber.m)+
      B.penalty (rowKLower r.box) (rowKUpper r.box) ((rowM r.box:ℝ)+witnessCollar)/2-
        B.p*witnessCollar/2)-B.delta*(1-B.p)*v/2))+outerFee ≤ _
  nlinarith only [hprice,hfee,mul_nonneg hd.le hdamp]

#print axioms native_directed_guards
#print axioms native_gain_eq
#print axioms native_middle_power_le_final
end
end QRH.Cycle092.MixedMiddleReturn
