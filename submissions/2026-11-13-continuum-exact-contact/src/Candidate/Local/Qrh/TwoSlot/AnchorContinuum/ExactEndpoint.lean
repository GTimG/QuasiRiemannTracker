/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Exact continuum contact, obtained from finite positive-cost constructions.
Extends Sil's PR137 marked-anchor method and the inherited all-moduli return.
No limit is taken through analytic estimates or their implicit constants. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSourceClosure
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveLowerReturn
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveGeometry
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ClosestEndpoint

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.ExactEndpoint
noncomputable section
open Set Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.TwoSlot.AnchorContinuum.PositiveTransport
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI OAI.SevenEighths HeckeFamily
open QRH.PositiveGap.Return.Tuning (uniform_restrict source_restricts_count source_restricts_physical)

private def frame : ℝ :=
  Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.rowExtension
private theorem frame_pos : 0 < frame := by
  norm_num [frame,Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.rowExtension]
private theorem frame_small : frame ≤ (1/1000000000:ℝ) := by
  norm_num [frame,Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.rowExtension]

/-- Every strictly larger target has its own finite source, positive costs,
common early mesh and complete physical return. -/
theorem beta_le_above {t : ℝ} (ht : Contact.theta < t)
    (hupper : t ≤ (87334587/100000000:ℝ)) : HeckeZeroSupremum.beta ≤ t := by
  letI : Geometry.Parameters := Contact.ExactReturn.targetGeometry t ht.le hupper
  letI : BoundsCore := Contact.ExactReturn.targetCoarse t ht.le hupper
  letI : Affine.Return.ImprovedCountScheme Contact.exactLine := Contact.exactScheme
  by_contra hn
  have hgap : t < HeckeZeroSupremum.beta := lt_of_not_ge hn
  have hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
    have hh := BoundsCore.theta_bounds.1
    change (873/1000:ℝ) < t at hh
    linarith
  let ε := min frame ((t-Contact.theta)/100)
  have hε : 0 < ε := lt_min frame_pos (by positivity)
  have hεframe : ε ≤ frame := min_le_left _ _
  have hεgap : ε ≤ (t-Contact.theta)/100 := min_le_right _ _
  obtain ⟨s,Δ,fee,hs,hsframe,hsmax,hΔ,hΔframe,hfee,hfeeframe,_hsource,_hrows⟩ :=
    Contact.ExactReturn.exists_positive_complete_return hβ ht hε
  have hsGap : s ≤ (t-Contact.theta)/100 := hsframe.le.trans hεgap
  have hΔGap : Δ ≤ (t-Contact.theta)/100 := hΔframe.trans hεgap
  have hfeeGap : fee ≤ (t-Contact.theta)/100 := hfeeframe.trans hεgap
  have hH : Geometry.h = Contact.stationaryCutoff :=
    Contact.ExactReturn.target_h t ht.le hupper
  have hΔsmall : Δ ≤ (1/1000000000:ℝ) := hΔframe.trans (hεframe.trans frame_small)
  let S : Schedule (line := Contact.exactLine) := {
    cost := s
    extension := Δ
    fee := fee
    cost_pos := hs
    cost_small := hsmax
    extension_pos := hΔ
    extension_small := hΔsmall
    fee_pos := hfee
    y_before_switch := by linarith [BoundsCore.ly_coarse.2]
    switch_before_twoy := by linarith [BoundsCore.ly_coarse.1]
    prime_supply := by
      have hp : 0 < Geometry.h+Δ := by linarith [BoundsCore.h_interval.1]
      apply (lt_div_iff₀ hp).mpr
      linarith [BoundsCore.ell_interval.1,BoundsCore.h_interval.2]
    incumbent := by
      change 2*t-1 ≤ QRH.PositiveGap.Return.naturalK/6
      norm_num [QRH.PositiveGap.Return.naturalK]
      linarith
    old_rows := by
      intro D delta p hD hd hp
      have hr := Contact.ExactReturn.target_old_rows ht.le hD hd hp
      change rowAt (Affine.Return.ImprovedCount.admittedBranches (line := Contact.exactLine))
        (2*t-1) D (oldCapacityAt (2*t-1) D) delta p ≤ t-fee
      rw [Contact.ExactReturn.generic_row_eq t ht.le hupper]
      change Contact.ExactReturn.targetRow (2*t-1) t D
        (Contact.ExactReturn.targetOldCapacity (2*t-1) t D) delta p ≤ t-fee
      linarith
    new_rows := by
      intro D delta p hD hd hp
      have hDall : D ∈ Icc (19/25:ℝ) (Contact.stationaryCutoff+Δ) := by
        refine ⟨hD.1,?_⟩
        simpa only [hH] using hD.2
      have hr := Contact.ExactReturn.extended_target_rows hs.le ht.le hΔ.le hDall hd hp
      change rowAt (Affine.Return.ImprovedCount.admittedBranches (line := Contact.exactLine))
        (2*t-1) D (Contact.ExactReturn.targetCapacity s t D) delta p ≤ t-fee
      rw [Contact.ExactReturn.generic_row_eq t ht.le hupper]
      change Contact.ExactReturn.targetRow (2*t-1) t D
        (Contact.ExactReturn.targetCapacity s t D) delta p ≤ t-fee
      linarith }
  letI : Schedule (line := Contact.exactLine) := S
  have hG := Qrh.PositiveGap.return_source hβ
  have hC : UniformUnitFaceSource QRH.PositiveGap.Return.countGlobal :=
    uniform_restrict source_restricts_count hG
  have hP : UniformUnitFaceSource QRH.PositiveGap.Return.physicalGlobal :=
    uniform_restrict source_restricts_physical hG
  have hcap : 2*HeckeZeroSupremum.beta-1 ≤ Contact.exactScheme.naturalκ :=
    QRH.PositiveGap.Return.Tuning.natural_cap_return
  obtain ⟨A,_,_ht,hpad,_hbudget,hlabel,himp,hphysical⟩ :=
    exists_initial_sources_with_costs (PositiveSource.physicalFace s) hcap
      (ClosestRational.count_mesh hC hP) (PositiveSource.physical_source hs hsmax hβ)
      (Contact.exact_fiber_moments hβ) hgap hΔ hfee (show (0:ℝ) < 1 by norm_num)
  let B : BufferedData (line := Contact.exactLine) := {
    toChosenData := A
    padding_budget := hpad
    padding_small := by
      change Δ/2 ≤ frame
      have hh : Δ ≤ frame := hΔframe.trans hεframe
      linarith }
  have hle := PositiveTransport.beta_le_theta_of_initial_source (line := Contact.exactLine)
    (by intro _; exact ⟨B,hlabel,himp,hphysical⟩)
  exact (not_le_of_gt hgap) hle

/-- The exact scalar contact bounds the complete Hecke zero supremum. Each
strict comparison invokes a separate finite construction with positive costs. -/
theorem beta_le_contact : HeckeZeroSupremum.beta ≤ Contact.theta := by
  by_contra hn
  have hg : Contact.theta < HeckeZeroSupremum.beta := lt_of_not_ge hn
  have hu : Contact.theta < (87334587/100000000:ℝ) :=
    ClosestRational.target_bounds.1.trans_le ClosestRational.target_bounds.2
  let t := min ((Contact.theta+HeckeZeroSupremum.beta)/2)
    ((Contact.theta+(87334587/100000000:ℝ))/2)
  have ht : Contact.theta < t := lt_min (by linarith) (by linarith)
  have htβ : t < HeckeZeroSupremum.beta :=
    (min_le_left _ _).trans_lt (by linarith)
  have htupper : t ≤ (87334587/100000000:ℝ) :=
    (min_le_right _ _).trans (by linarith)
  exact (not_le_of_gt htβ) (beta_le_above ht htupper)

/-- Exact-contact nonvanishing for every positive modulus and every Dirichlet
character, excluding only the principal pole. No analytic premise remains. -/
theorem bound {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : Contact.theta < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by linarith [Contact.theta_range.1])
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      (beta_le_contact.trans_lt hs) hpole) χ s hs hpole

end
end Qrh.TwoSlot.AnchorContinuum.ExactEndpoint
#print axioms Qrh.TwoSlot.AnchorContinuum.ExactEndpoint.beta_le_contact
#print axioms Qrh.TwoSlot.AnchorContinuum.ExactEndpoint.bound
