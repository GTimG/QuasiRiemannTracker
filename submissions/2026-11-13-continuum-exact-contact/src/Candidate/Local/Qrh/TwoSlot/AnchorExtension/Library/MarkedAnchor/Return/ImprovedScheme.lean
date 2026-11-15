/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The count scheme of the return extended by improved windows. Adapted from Hailey Collet's
`Record1252270103Return/AdmittedWindow.lean` and `CountScheme.lean` (Apache-2.0). -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.FiberImproved

/-!
# Return.ImprovedScheme

* `ImprovedWindow κ` — scalar data of an improved count window on `[deltaLo, deltaHi] × [pLo, 1/2]`:
  the improved inverse crossing `cross` (the free width above which the improved inverse moment of
  `Interface.FiberImproved` pays the target), the cutoff `t` with `2 (t - cross) ≥ anchorLeft`
  (below the crossing the plain length is `≥ t - cross` and the improved ordinary moment pays),
  the native top inverse and plain pieces at `anchorTop`, the natural tail, and the long piece.
* `ImprovedCountScheme` — Collet's `CountScheme` plus a list of improved windows, each sharing the
  plain source face of a native window.
* `ImprovedCount.envelope` — the finite minimum over the old count, the native windows and the
  improved windows; `selectedCutoff` and its bounds.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Return
noncomputable section

open Set QRH.Record1252270103Return Qrh.MarkedAnchor.Interface

/-- An improved count window (line `(lineG0, lineG1)`, interval `[anchorLeft, anchorTop]`). -/
structure ImprovedWindow (naturalκ : ℝ) where
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
    0≤1-p*(1+2*lineG1)
  inverse_crossing : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ*(p*(1+2*lineG0)+(1-p*(1+2*lineG1))*crossing δ p)=value δ p
  ordinary_crossing : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ*(p*(1+2*lineG0)+2*(cutoff δ p-crossing δ p)*(1-p*(1+2*lineG1)))≤value δ p
  native_top : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ*(p+(1-p)*anchorTop)≤value δ p
  plain_top : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    plainCurve B lam cap δ p (anchorTop/2)≤value δ p
  natural_tail : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-2*δ*mHi-2*(δ*p)*(1-2*mHi)/(6*naturalκ)≤value δ p
  widths : ∀ν:ℝ,ν≤1/10000000 → ∀m:ℝ,anchorTop/2≤m → m≤mHi → ν<min cap ((B-2*m)/lam)
  long_crossing : ∀{δ p:ℝ},δ∈Icc deltaLo deltaHi → p∈Icc pLo (1/2) →
    1-δ+(5/6-δ)*(cutoff δ p-1)=value δ p
  antitone : ∀{δ:ℝ},δ∈Icc deltaLo deltaHi → AntitoneOn (value δ) (Icc pLo (1/2))

/-- The plain source face of the native fallback piece. -/
def ImprovedWindow.face {κ:ℝ} (w:ImprovedWindow κ) : QRH.Record12518109Source.SourceFace :=
  broadFace w.B w.lam w.sourceCap

def ImprovedWindow.Available {κ:ℝ} (w:ImprovedWindow κ) (δ p:ℝ) : Prop :=
  δ∈Icc w.deltaLo w.deltaHi ∧ p∈Icc w.pLo (1/2)

theorem ImprovedWindow.upward {κ:ℝ} (w:ImprovedWindow κ) {δ p q:ℝ}
    (hp:w.Available δ p) (hpq:p≤q) (hq:q≤1/2) : w.Available δ q :=
  ⟨hp.1,⟨hp.2.1.trans hpq,hq⟩⟩

def ImprovedWindow.toBranch {κ:ℝ} (w:ImprovedWindow κ) : Branch where
  available := w.Available
  value := w.value
  upward := w.upward
  antitone := by
    intro δ p q hp hq hpq
    exact w.antitone hp.1 hp.2 hq.2 hpq

/-- Collet's count scheme with additional improved windows. Every improved window uses the plain
source face of a native window, so the native affine moments already cover it. -/
class ImprovedCountScheme extends CountScheme where
  improved : List (ImprovedWindow naturalκ)
  improved_face : ∀w∈improved, ∃v∈windows, v.face=w.face

namespace ImprovedCount
open OAI.SevenEighths
variable [S:ImprovedCountScheme]

/-- The native and the improved branches. -/
def admittedBranches : List Branch :=
  S.windows.map AdmittedWindow.toBranch++S.improved.map ImprovedWindow.toBranch

/-- The count envelope: the old count and every native or improved window. -/
def envelope (κ δ p:ℝ) : ℝ := QRH.Record1252270103Return.envelope admittedBranches κ δ p

inductive Choice [S:ImprovedCountScheme]
  | old
  | affine (window:AdmittedWindow S.naturalκ)
  | improved (window:ImprovedWindow S.naturalκ)

def Choice.Available : Choice→ℝ→ℝ→Prop
  | .old,_,_ => True
  | .affine w,δ,p => w∈S.windows ∧ w.Available δ p
  | .improved w,δ,p => w∈S.improved ∧ w.Available δ p

def Choice.value : Choice→ℝ→ℝ→ℝ→ℝ
  | .old,κ,δ,p => countingR κ δ p
  | .affine w,_,δ,p => w.value δ p
  | .improved w,_,δ,p => w.value δ p

def Choice.cutoff : Choice→ℝ→ℝ→ℝ→ℝ
  | .old,κ,δ,p => Cycle25DetectorRowCount.cutoff δ p κ
  | .affine w,_,δ,p => w.cutoff δ p
  | .improved w,_,δ,p => w.cutoff δ p

theorem envelope_attained (κ δ p:ℝ) :
    ∃c:Choice,c.Available δ p ∧ c.value κ δ p=envelope κ δ p := by
  rcases QRH.Record12518109Return.finiteEnvelope_attained
    QRH.Record12518109Return.countingR admittedBranches κ δ p with h | ⟨b,hb,ha,heq⟩
  · exact ⟨.old,trivial,h.symm⟩
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_map.mp hb with ⟨w,hw,rfl⟩
      exact ⟨.affine w,⟨hw,ha⟩,heq.symm⟩
    · rcases List.mem_map.mp hb with ⟨w,hw,rfl⟩
      exact ⟨.improved w,⟨hw,ha⟩,heq.symm⟩

def selectedChoice (κ δ p:ℝ) : Choice := Classical.choose (envelope_attained κ δ p)

theorem selectedChoice_available (κ δ p:ℝ) : (selectedChoice κ δ p).Available δ p :=
  (Classical.choose_spec (envelope_attained κ δ p)).1

theorem selectedChoice_value (κ δ p:ℝ) : (selectedChoice κ δ p).value κ δ p=envelope κ δ p :=
  (Classical.choose_spec (envelope_attained κ δ p)).2

def selectedCutoff (κ δ p:ℝ) : ℝ := (selectedChoice κ δ p).cutoff κ δ p

theorem Choice.cutoff_bounds (c:Choice) {κ δ p:ℝ} (ha:c.Available δ p)
    (hk:7/10≤κ) (hkhi:κ≤3/4) (hδ:δ∈Icc 0 (3/4)) (hp:p∈Icc 0 (1/2)) :
    1≤c.cutoff κ δ p ∧ c.cutoff κ δ p≤3/2 := by
  cases c with
  | old => exact Cycle25DetectorRowCount.cutoff_bounds hδ.1 hδ.2 hp.1 hp.2 hk hkhi
  | affine w => exact w.cutoff_bounds ha.2.1 ha.2.2
  | improved w => exact w.cutoff_bounds ha.2.1 ha.2.2

theorem selectedCutoff_bounds {κ δ p:ℝ}
    (hk:7/10≤κ) (hkhi:κ≤3/4) (hδ:δ∈Icc 0 (3/4)) (hp:p∈Icc 0 (1/2)) :
    1≤selectedCutoff κ δ p ∧ selectedCutoff κ δ p≤3/2 :=
  Choice.cutoff_bounds _ (selectedChoice_available κ δ p) hk hkhi hδ hp

theorem envelope_le_window {w:AdmittedWindow S.naturalκ} (hw:w∈S.windows) {κ δ p:ℝ}
    (ha:w.Available δ p) : envelope κ δ p≤w.value δ p :=
  QRH.Record12518109Return.finiteEnvelope_le_branch QRH.Record12518109Return.countingR
    (List.mem_append_left _ (List.mem_map.mpr ⟨w,hw,rfl⟩)) ha

theorem envelope_le_improved {w:ImprovedWindow S.naturalκ} (hw:w∈S.improved) {κ δ p:ℝ}
    (ha:w.Available δ p) : envelope κ δ p≤w.value δ p :=
  QRH.Record12518109Return.finiteEnvelope_le_branch QRH.Record12518109Return.countingR
    (List.mem_append_right _ (List.mem_map.mpr ⟨w,hw,rfl⟩)) ha

theorem envelope_le_base (κ δ p:ℝ) : envelope κ δ p≤countingR κ δ p :=
  QRH.Record12518109Return.finiteEnvelope_le_base QRH.Record12518109Return.countingR
    admittedBranches κ δ p

end ImprovedCount
end
end Qrh.MarkedAnchor.Return
