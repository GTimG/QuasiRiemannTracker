/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- The provider/assembly composition retains Sil and OpenAI's source-step
attribution. No imported submission is modified. -/
import Candidate.Local.Qrh.JointDetector.FineSourceChains.Affine
import Candidate.Local.Qrh.JointDetector.AdaptiveSourceChains.Common

namespace Qrh.JointDetector.FineSourceChains
noncomputable section
set_option autoImplicit false
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open OAI.SevenEighths

abbrev SourceFace := AdaptiveSourceChains.SourceFace

/-- This is closed by the actual fine-cutoff packed supplier in the final
assembly. It retains the literal early-mesh/all-height source contract. -/
def PackedProvider : Prop :=
  ∀ (B0 L0 B L : ℝ) (hL : 0 < L0),
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
    0 < B0 → B0 ≤ 1 →
    QRH.Record1252270103Source.GlobalSource B0 L0 cap →
    PricedPackedSource
      (FinePointwiseLedger.stepData phi B0 L0 cap B L cap amp 0 hL).price
      (9/10) 4 4

theorem source_step {B0 L0 B L : ℝ}
    (h : FinePointwiseLedger.Gates phi B0 L0 cap B L cap amp 0)
    (hF : Density.DSFace B0 L0 cap B L cap) (hL : 0 < L0)
    (hB0 : 0 < B0) (hprovider : PackedProvider)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource B0 L0 cap) :
    QRH.Record1252270103Source.GlobalSource B L cap := by
  let data := FinePointwiseLedger.stepData phi B0 L0 cap B L cap amp 0 hL
  have G : StepGates data := FinePointwiseLedger.stepGates h hF hL (by norm_num [cap])
  have hleaf : PricedPackedSource data.price data.Hmin (data.Hmax+1) 4 := by
    simpa only [data, FinePointwiseLedger.stepData, show (3:ℝ)+1=4 by norm_num] using
      hprovider B0 L0 B L hL hβ hB0 hF.B₀_lt.le hp
  have hI := Assembly.step_inputs_of_provider data G 4 (fun _ hl =>
    Second.Provider.contrary_raw_side_provider G 4 le_rfl hl (Second.ProviderDiag.diag_supply G))
  exact cubefree_step data G 4 hI hβ hp hleaf

/-- The statement for one scalar-checked stage. Every invocation receives the
complete parent source for arbitrary requested accuracy, not a fixed loss. -/
def Transition (B0 L0 B L : ℝ) : Prop :=
  PackedProvider → (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
    QRH.Record1252270103Source.GlobalSource B0 L0 cap →
    QRH.Record1252270103Source.GlobalSource B L cap

theorem transition_of_certificate {B0 L0 B L : ℝ}
    (hB : 0 < B ∧ B < B0 ∧ B0 < 1)
    (hL : 1 < L ∧ L < L0)
    (hwidth : 0 < cap-Hybrid.cross B0 L0 B L)
    (hden : 0 < Hybrid.densE B0 L0 L amp 0 0)
    (hends : EndpointGates B0 L0 B L) : Transition B0 L0 B L := by
  intro hprovider hβ hp
  apply source_step (gates_of_endpoints hwidth hden hends) ?_
    (by linarith [hL.1,hL.2]) (by linarith [hB.1,hB.2.1]) hprovider hβ hp
  exact ⟨hB.2.1.le,hB.2.2,hL.2,hL.1,by norm_num [cap],by norm_num [cap]⟩

end
end Qrh.JointDetector.FineSourceChains
