/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Scalar admission data for literal globally sourced counting windows. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.CountFromMoments
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.CountingBridge
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage2Return
noncomputable section

structure AdmittedWindow (naturalκ:ℝ) where
 B : ℝ
 lam : ℝ
 cap : ℝ
 sourceCap : ℝ
 mLo : ℝ
 mHi : ℝ
 lam_gt_one : 1<lam
 mLo_nonneg : 0≤mLo
 mHi_lo : 2/5≤mHi
 mHi_hi : mHi<1/2
 cap_le_source : cap≤sourceCap
 cap_small : cap≤7/37
 value : ℝ→ℝ→ℝ
 cutoff : ℝ→ℝ→ℝ
 crossing : ℝ→ℝ→ℝ
 deltaLo : ℝ
 deltaHi : ℝ
 pLo : ℝ
 deltaBounds : 0≤deltaLo ∧ deltaHi≤3/4
 pBounds : 0≤pLo ∧ pLo≤1/2
 cutoff_bounds : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  1≤cutoff δ p ∧ cutoff δ p≤3/2
 inverse_bounds : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  23/37≤crossing δ p ∧ crossing δ p≤1
 plain_buffer : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  mLo+1/10000000≤cutoff δ p-crossing δ p
 inverse_crossing : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  1-δ*(p+(1-p)*crossing δ p)=value δ p
 plain_crossing : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  plainCurve B lam cap δ p (cutoff δ p-crossing δ p)≤value δ p
 natural_tail : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  1-2*δ*mHi-2*(δ*p)*(1-2*mHi)/(6*naturalκ)≤value δ p
 widths : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  ∀ν:ℝ,ν≤1/10000000 → ∀m:ℝ,mLo≤m → m≤mHi → ν<min cap ((B-2*m)/lam)
 long_crossing : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  1-δ+(5/6-δ)*(cutoff δ p-1)=value δ p
 antitone : ∀{δ:ℝ},δ∈Set.Icc deltaLo deltaHi →
  AntitoneOn (value δ) (Set.Icc pLo (1/2))

def AdmittedWindow.face {κ:ℝ} (w:AdmittedWindow κ) : QRH.Record12518109Source.SourceFace :=
 broadFace w.B w.lam w.sourceCap

def AdmittedWindow.Available {κ:ℝ} (w:AdmittedWindow κ) (δ p:ℝ) : Prop :=
 δ∈Set.Icc w.deltaLo w.deltaHi ∧ p∈Set.Icc w.pLo (1/2)

theorem AdmittedWindow.upward {κ:ℝ} (w:AdmittedWindow κ) {δ p q:ℝ}
 (hp:w.Available δ p) (hpq:p≤q) (hq:q≤1/2) : w.Available δ q :=
 ⟨hp.1,⟨hp.2.1.trans hpq,hq⟩⟩

def AdmittedWindow.toBranch {κ:ℝ} (w:AdmittedWindow κ) : Branch where
 available := w.Available
 value := w.value
 upward := w.upward
 antitone := by
  intro δ p q hp hq hpq
  exact w.antitone hp.1 hp.2 hq.2 hpq
end
end QRH.LewkoStage2Return
