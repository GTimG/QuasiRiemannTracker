/- Copyright (c) 2026 Sil. Apache-2.0.
The step inputs from the raw-side provider of the root chain.

The root chain's top statement `RepairedSourceSetupBound.uniform_setup_of_side_provider` bounds
the literal restored row of every root `Setup M H D` with `s₀ ≤ markedWidth`, given a
`ProviderAt G (ε/12) meshCap`. As in FP's `restricted_unit_source_of_raw_sides`, the restricted
input data of one restored row `(T, w, r, A)` is packed into a `Setup` (window cap
`windowCap G N (ε/12)`, mesh chosen after `ε`, before the slot type), which gives
`HighRestrictedUnitSource` (the row width condition `s₀ ≤ rowWidth` is the setup's
`s₀ ≤ markedWidth`). Hence `StepInputs` follows from a provider.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.Assembly`: `high_of_provider` and `step_inputs_of_provider` take the
reference lane `ReferenceLaneFine D` (used at `51/100 ≤ β`); the row mesh is
`min (min (mesh G (ε/12)) meshCap) (laneMesh (ω(ε/12) + ε/12/100))`; `allStepInputs_of_providers`
(native and density instances) is not forked. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Step
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSetupBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Assembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Assembly
noncomputable section
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open KernelCollisionEnergy RestoredInitialSource RestoredRootEnergy RecenteredRootSetup
open RepairedSourceSideSupply RepairedSourceSetupBound RepairedSourceRootGeometry
open Qrh.MarkedAnchor.Ordinary.RootParameters Qrh.MarkedAnchor.Ordinary.Reference
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

set_option maxHeartbeats 1600000 in
/-- **The root chain's provider gives the high restricted source.** -/
theorem high_of_provider {D : StepData} (G : StepGates D) (hlane : ReferenceLaneFine D)
    (hsupply : ContraryRawSideProvider G) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    HighRestrictedUnitSource (globalFace D.B D.L D.c) D.s₀ := by
  intro ε hε
  obtain ⟨meshCap, hmc, hP⟩ := setup_mesh_of_contrary G hsupply hβ ε hε
  have hε12 : 0 < ε/12 := by positivity
  have homega := (omega_spec G (ε/12) hε12).1
  refine ⟨min (min (mesh G (ε/12)) meshCap)
      (RecenteredRootReferenceBound.laneMesh (hlane hβ) (omegaLoss G (ε/12)+ε/12/100)),
    lt_min (lt_min (mesh_spec G (ε/12) hε12).1 hmc)
      (RecenteredRootReferenceBound.laneMesh_pos (hlane hβ) (by positivity)), ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  have : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  have hQM : internalQ Q η₀ ≤ rayM := inf_le_left.trans hQray
  have hQη : internalQ Q η₀ ≤ η₀.modulus := inf_le_right
  obtain ⟨J, control, C, hC, hbound⟩ := uniform_setup_of_side_provider G (hlane hβ) ε hε meshCap hP α
    rayM H hH W hW hWs bΦ hbΦ η η₀ (internalQ Q η₀) hQt hQ72 hQM hQη
  refine ⟨J, control, C, hC, ?_⟩
  filter_upwards [hbound] with Z hz
  intro T w r A hs₀ θ σ v t height hw hwm hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm
    rows tc ti hti Y₁ Y₂ hY₁ hy₁ hY₂ hy₂
  let s : Setup rayM H D T :=
    { Z := Z
      hZ := by linarith [hz.1]
      Lcap := windowCap G (Fintype.card α) (ε/12)
      hLcap := windowCap_ge_eight G _ (ε/12) hε12
      W := W
      hW := hW.continuous
      hWs := hWs
      η₀ := η₀
      θ := θ
      w := w
      σ := σ
      v := v
      hw := hw
      hσlo := hσlo
      hσhi := hσhi
      t := t
      p := p
      X₁ := X₁
      X₂ := X₂
      Y₁ := Y₁
      Y₂ := Y₂
      hY₁ := hY₁
      hY₂ := hY₂
      hy₁ := hy₁
      hy₂ := hy₂
      hface := hadm
      hD := face_facts G
      r := r
      tc := tc
      A := A
      ti := ti }
  have hmw : D.s₀ ≤ markedWidth rayM H s := by
    change D.s₀ ≤ ∑ i : RestoredRootDictionary.remainingSet r A, w i.val
    rw [Finset.sum_coe_sort (RestoredRootDictionary.remainingSet r A) w,
      ← RestoredRootDictionary.remaining_sum r A w]
    exact hs₀
  exact hz.2 T s rfl rfl rfl rfl height hh hv hwm hmw Q rfl Φ hΦ hΦp rows

/-- **`StepInputs` from the root chain's provider** (the provider may use the parent source
and the Seam A leaf of the step). -/
theorem step_inputs_of_provider (D : StepData) (G : StepGates D) (Lplain : ℝ)
    (hlane : ReferenceLaneFine D)
    (hprov : GlobalSource D.B₀ D.L₀ D.c₀ →
      PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain → ContraryRawSideProvider G) :
    StepInputs D G Lplain :=
  ⟨fun hβ hparent hleaf => high_of_provider G hlane (hprov hparent hleaf) hβ⟩

end
end Qrh.MarkedAnchor.Ordinary.Assembly
