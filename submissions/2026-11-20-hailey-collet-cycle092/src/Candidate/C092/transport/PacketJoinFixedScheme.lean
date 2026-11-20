/- Hailey Collet (2026): original window contract on genuine .72 interval. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Explicit-line count scheme, adapted from Sil's PR137 ImprovedScheme
(copyright (c) 2026 Sil, Apache-2.0) and Hailey Collet's admitted-window
and count-scheme contracts (Apache-2.0). -/
import Candidate.C092.transport.PacketJoinE49Fiber
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme

set_option autoImplicit false
namespace QRH.Cycle092.PacketJoinFixed.Return
noncomputable section
open QRH.Cycle092.PacketJoinE49
open Set QRH.Record1252270103Return

variable {line : Line}

/-- An improved count window (line `(line.g0, line.g1)`, interval `[anchorLeft, anchorTop]`). -/
structure FixedWindow (line : Line) (naturalκ : ℝ) where
  B : ℝ
  lam : ℝ
  cap : ℝ
  sourceCap : ℝ
  mHi : ℝ
  lam_gt_one : 1<lam
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
  cutoff_bounds : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1≤cutoff δ p ∧ cutoff δ p≤3/2
  crossing_left : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    anchorLeft≤crossing δ p
  plain_left : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    anchorLeft+1/1000000≤2*(cutoff δ p-crossing δ p)
  slope_nonneg : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    0≤1-p*(1+2*line.g1)
  inverse_crossing : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ*(p*(1+2*line.g0)+(1-p*(1+2*line.g1))*crossing δ p)=value δ p
  ordinary_crossing : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ*(p*(1+2*line.g0)+2*(cutoff δ p-crossing δ p)*(1-p*(1+2*line.g1)))≤value δ p
  native_top : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ*(p+(1-p)*anchorTop)≤value δ p
  plain_top : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    plainCurve B lam cap δ p (anchorTop/2)≤value δ p
  natural_tail : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-2*δ*mHi-2*(δ*p)*(1-2*mHi)/(6*naturalκ)≤value δ p
  widths : ∀ν:ℝ,ν≤1/10000000 → ∀m:ℝ,anchorTop/2≤m → m≤mHi → ν<min cap ((B-2*m)/lam)
/-- The plain source face of the native fallback piece. -/
def FixedWindow.face {κ:ℝ} (w:FixedWindow line κ) : QRH.Record12518109Source.SourceFace :=
  broadFace w.B w.lam w.sourceCap

def FixedWindow.Available {κ:ℝ} (w:FixedWindow line κ) (δ p:ℝ) : Prop :=
  δ∈Icc w.deltaLo w.deltaHi ∧ p∈Icc w.pLo (1/2)


end
end QRH.Cycle092.PacketJoinFixed.Return
