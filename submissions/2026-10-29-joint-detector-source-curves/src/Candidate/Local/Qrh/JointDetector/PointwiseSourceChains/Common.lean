/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.PointwiseLedger
import Candidate.Local.Qrh.JointDetector.PointwiseSupplier
import Candidate.Local.Qrh.JointDetector.AdaptiveSourceChains.Common
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9

/-! Generic finite composition from an explicit analytic packed provider.
No selected norm, count, or source theorem is postulated. -/
namespace Qrh.JointDetector.PointwiseSourceChains
noncomputable section
set_option autoImplicit false
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open OAI.SevenEighths

abbrev SourceFace := AdaptiveSourceChains.SourceFace

theorem source_step {φ B₀ L₀ c₀ B L c A D : ℝ}
    (h : PointwiseLedger.Gates φ B₀ L₀ c₀ B L c A D)
    (hF : Density.DSFace B₀ L₀ c₀ B L c) (hL : 0 < L₀) (hc : c₀ ≤ 1/10)
    (hB₀ : 0 < B₀) (hc₀ : 0 < c₀)
    (hnorm : NaturalCount.ActualSelectedSlotNorm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c := by
  let data := PointwiseLedger.stepData φ B₀ L₀ c₀ B L c A D hL
  have G : StepGates data := PointwiseLedger.stepGates h hF hL hc
  have hleaf : PricedPackedSource data.price data.Hmin (data.Hmax+1) 4 :=
    by simpa only [data, PointwiseLedger.stepData, show (3:ℝ)+1=4 by norm_num] using
      PointwiseSupplier.priced_source hnorm B₀ L₀ c₀ hL
        (PointwiseLedger.densQ φ B₀ L₀ L A D (Hybrid.cross B₀ L₀ B L))
        (PointwiseLedger.densQ_mem φ B₀ L₀ L A D (Hybrid.cross B₀ L₀ B L))
        hβ hB₀ hF.B₀_lt.le hc₀ hp
  have hI := Assembly.step_inputs_of_provider data G 4 (fun _ hl =>
    Second.Provider.contrary_raw_side_provider G 4 le_rfl hl (Second.ProviderDiag.diag_supply G))
  exact cubefree_step data G 4 hI hβ hp hleaf

def Transition (parent child : SourceFace) : Prop :=
  NaturalCount.ActualSelectedSlotNorm → (51/100:ℝ) ≤ HeckeZeroSupremum.beta → parent.Source → child.Source

inductive Chain : SourceFace → List SourceFace → Prop
  | nil (p : SourceFace) : Chain p []
  | cons {p next : SourceFace} {tail : List SourceFace} :
      Transition p next → Chain next tail → Chain p (next::tail)

/-- Finite induction preserves the actual source and the single explicit
packed-provider hypothesis at each stage; no limiting source is asserted. -/
theorem Chain.source {parent : SourceFace} {faces : List SourceFace}
    (h : Chain parent faces) (hnorm : NaturalCount.ActualSelectedSlotNorm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hp : parent.Source) :
    (faces.getLastD parent).Source := by
  induction h with
  | nil p => exact hp
  | @cons p next tail hstep htail ih =>
    have hs := ih (hstep hnorm hβ hp)
    cases tail with
    | nil => exact hs
    | cons x xs =>
      simpa only [List.getLastD_cons] using hs

end
end Qrh.JointDetector.PointwiseSourceChains
