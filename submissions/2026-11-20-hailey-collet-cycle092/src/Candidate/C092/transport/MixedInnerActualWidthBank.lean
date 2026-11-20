/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The P12 inner width is supplied on the actual native MiddleBank, with its
own supporting witness and exact source line. Large-count exits are retained. -/
import Candidate.C092.transport.MixedInnerActualWidthActual
import Candidate.C092.transport.MixedTicketTailsContact
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.MixedInnerActualWidth
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorWitnessRows
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.RawTicket
open QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open QRH.ContactCertificate
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

 theorem actual_return_contact :
    (5805911/100000000:ℝ)≤ Return.line.g0 ∧ Return.line.g0≤5805913/100000000 ∧
    (3799809/50000000:ℝ)≤ Return.line.g1 ∧ Return.line.g1≤379981/5000000 := by
  have h0:=g0_receipt_sound MixedTicketTails.actual_contact_root
  have h1:=g1_receipt_sound MixedTicketTails.actual_contact_root
  have hb:=receipt_original_bounds
  rw [MixedTicketTails.actual_contact_intercept,MixedTicketTails.actual_contact_slope,
    MixedTicketTails.actual_contact_width]
  exact ⟨hb.1.trans h0.1,h0.2.trans hb.2.2.2.1,
    hb.2.2.2.2.1.trans h1.1,h1.2.trans hb.2.2.2.2.2.2.2⟩

 theorem return_cutoff_eq_crossing {delta p : ℝ}
    (hav : Return.window.Available delta p) :
    Return.cutoffI delta p=pairedCrossing delta p Return.line.g0 Return.line.g1 := by
  have hJ:Return.JI delta p≠0:=(Return.hJ hav.1 hav.2).ne'
  have he : Return.JI delta p=pairedJ delta p Return.line.g1:=by
    unfold Return.JI Return.kI pairedJ pairedV pairedK
    ring
  unfold Return.cutoffI Return.TI pairedCrossing
  rw [add_div,div_self hJ,he]
  rfl

 theorem actual_return_k_lower {row : Row} (hr : row∈rows) {delta p : ℝ}
    (hp : row.box.Contains (delta,p)) : (lowerK row.box:ℝ)≤ Return.kI p := by
  have hh:=row_endpoint_hull hr
  have hcontact:=actual_return_contact
  have hp0 : 0≤ p:=(by norm_num [pLo] : (0:ℝ)≤ pLo).trans (hh.2.2.1.1.trans hp.2.2.1)
  have he0 : 0≤(row.box.vHi:ℝ):=hp0.trans hp.2.2.2
  have hm:=mul_le_mul hp.2.2.2 (by linarith only [hcontact.2.2.2] :
    1+2*Return.line.g1≤1+2*(379981/5000000))
    (by linarith only [hcontact.2.2.1] : 0≤1+2*Return.line.g1) he0
  simp only [lowerK,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
  unfold Return.kI
  linarith only [hm]

variable {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D} {eta : Character} {Z : ℝ}

/-- The actual nonempty fiber supplies the product support bound itself. -/
theorem bank_actual_support (B : MiddleBank D S eta Z) (hZ : 1< Z) :
    B.t₀-B.xi-3*B.εa≤ B.currentSlice.fiber.r+B.currentSlice.fiber.m := by
  let F:=B.currentSlice.fiber
  obtain ⟨u,hu⟩:=F.nonempty
  have hr: (F.witness u).r=F.r:=by
    rw [(F.witness u).toWitness.left_exponent (B.baseScale_gt_one hZ),F.fixed_left u hu]
    rfl
  have hm: (F.witness u).m=F.m:=by
    rw [(F.witness u).toWitness.right_exponent (B.baseScale_gt_one hZ),F.fixed_right u hu]
    rfl
  have hs:=(F.witness u).product_length_lower
  rw [hr,hm] at hs
  change (B.t₀-B.xi)-F.r-D.ε≤ F.m at hs
  have hc:=B.support_collar
  change B.t₀-B.xi-3*B.εa≤ F.r+F.m
  linarith only [hs,hc]

/-- Insufficient saving now admits the ACTUAL ordinary length into the
narrow mixed-source interval, at the exact refined checked top budget. -/
theorem bank_width_of_insufficient {row : Row} (hr : row∈rows)
    (B : MiddleBank D S eta Z) (hZ : 1< Z)
    (hp : row.box.Contains (B.delta,B.p))
    (hgamma : B.γ≤(rowGamma row.box row.B:ℝ)) (hann : B.εa≤1/10^(13:ℕ))
    (hinsuff : B.delta*B.centered<4*(rowBudget row.B:ℝ)/3) :
    widthLo≤ B.currentSlice.fiber.m ∧ B.currentSlice.fiber.m≤ widthHi := by
  have hc:=actual_return_contact
  have ht:=actual_crossing_interval hr hp ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
  have hcross : B.t₀=pairedCrossing B.delta B.p Return.line.g0 Return.line.g1:=by
    rw [B.baseline_cutoff]
    exact return_cutoff_eq_crossing B.available
  rw [←hcross] at ht
  have hx : B.xi≤(rowGamma row.box row.B:ℝ):=
    (MixedOffsetBank.offset_bounds B.γ B.gamma_nonneg B.j).2.trans hgamma
  exact actual_width_of_insufficient hr hp (actual_return_k_lower hr hp)
    (row_budget_nonneg row) (le_refl _) ht.1 ht.2 hx (by linarith only [hann])
    (bank_actual_support B hZ) hinsuff

/-- Native branch output: either its true count saves 4q0/3, or its actual
ordinary width lies in the required interval. No source width is assumed. -/
theorem bank_branch_width {row : Row} (hr : row∈rows)
    (B : MiddleBank D S eta Z) (K : CountConstants) (hZ : 1< Z)
    (hp : row.box.Contains (B.delta,B.p))
    (hgamma : B.γ≤(rowGamma row.box row.B:ℝ)) (hann : B.εa≤1/10^(13:ℕ))
    (hb : B.BranchConclusion K (rowBudget row.B:ℝ)) :
    (4*(rowBudget row.B:ℝ)/3≤ B.delta*B.centered ∧
      (B.common.card:ℝ)≤ B.coefficient K*B.baseScale^(B.R-4*(rowBudget row.B:ℝ)/3+B.loss)) ∨
    (widthLo≤ B.currentSlice.fiber.m ∧ B.currentSlice.fiber.m≤ widthHi ∧ B.CountConclusion K) := by
  rcases hb with hlarge|hsmall
  · exact Or.inl hlarge
  · exact Or.inr ⟨(bank_width_of_insufficient hr B hZ hp hgamma hann hsmall.1).1,
      (bank_width_of_insufficient hr B hZ hp hgamma hann hsmall.1).2,hsmall.2⟩

end
end QRH.Cycle092.MixedInnerActualWidth
#print axioms QRH.Cycle092.MixedInnerActualWidth.bank_actual_support
#print axioms QRH.Cycle092.MixedInnerActualWidth.bank_width_of_insufficient
#print axioms QRH.Cycle092.MixedInnerActualWidth.bank_branch_width
