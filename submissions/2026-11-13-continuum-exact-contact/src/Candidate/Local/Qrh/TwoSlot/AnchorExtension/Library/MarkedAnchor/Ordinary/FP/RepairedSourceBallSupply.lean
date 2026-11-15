/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Arvi (2026-10-25): the contrary hypothesis `theta < beta` is replaced by
`51/100 ≤ beta`, the only consequence of it that the source construction uses.
Supplies the full-ball energy from ContraryRawSideProvider.
The remaining premises are explicit structural support caps.
Modified by Sil (2026-10-26): uniform_ball_of_side_provider G eps meshCap (hsupply : ProviderAt G eps meshCap): for root inputs with slot widths <= meshCap, full ball cost <= ... Z^(1+4 eps) (contract loss 3 eps, mass eps/8), through the cube-free fullBallCost_of_raw_sides_family.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedSourceRootInput
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedFirstFullBallFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceBallSupply
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedFirstProfileEnvelope
open Qrh.MarkedAnchor.Ordinary.RootParameters RepairedRawContext RepairedSourceSideSupply RepairedSourceProfiles
open RepairedSourceRootGeometry RecenteredRootFixedMajorant RepairedFirstFullBallFamily
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqBallSupply {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance instFiniteQuotBallSupply (M : Id) [NeZero M] : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

set_option maxHeartbeats 1000000 in
theorem uniform_ball_of_side_provider {D : StepData} (G : StepGates D)
    (ε : ℝ) (hε : 0 < ε) (meshCap : ℝ) (hsupply : ProviderAt G ε meshCap) (α : Type) [Fintype α]
    (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q : Id) [NeZero Q]
    (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus) :
    let N := Fintype.card α
    let Kslot := RestoredRootSource.slotBound W hW.continuous hWs
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
    ∀ k : RootShape α,
    ∀ d : RootInput G M H hH (RootSlot k) W N (2*N) ε Z Kslot η η₀,
      d.Kroot=bΦ*Z → (∀ i, d.w i ≤ meshCap) → (∏i,d.root.P i) ≤ Z^(8:ℝ) →
      sourceNormCap d.root.P (9/4) d.root.T d.root.d ≤ Z^(8:ℝ) →
      sourceVolume d.root ≤ Z^(8:ℝ) →
      fullBallCost d.root (by norm_num) η (bΦ*Z) ≤
        C*(sourceControl control d.root.W₁*sourceControl control d.root.W₂)^2*
          (height d.t₀ d.V d.root.t₁ d.root.t₂)^J*Z^(1+4*ε) := by
  intro N Kslot
  have hKslot : 1 ≤ Kslot := (RestoredRootSource.slotBound_spec W hW.continuous hWs).1
  obtain ⟨J,control,Cside,hCs,h00,hsides⟩ :=
    hsupply α M H hH W hW hWs bΦ hbΦ η η₀ Q hQt hQ72 hQM hQη
  have hcut := (internal_losses_paid G N ε hε).1
  have hCp : 0 < 4*Kslot^(2*N) := by positivity
  obtain ⟨Cfull,hCf,hfull⟩ := fullBallCost_of_raw_sides_family (RootShape α) RootSlot N J
    root_slot_card bΦ (4*Kslot^(2*N)) (cutoffLoss G N ε) (cutoffLoss G N ε) (ε/8) (4*ε)
    (by linarith) hCp hcut hcut (by positivity) (by positivity) η
  refine ⟨J,control,Cfull*Cside,mul_pos hCf (zero_lt_one.trans_le hCs),?_⟩
  filter_upwards [hsides,hfull] with Z hs hf
  refine ⟨hs.1,?_⟩
  intro k d hK hcap hP hnorm hvol
  have hz : 1 ≤ Z := hf.1.le
  have hlen : Z^(3:ℝ) ≤ Z^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
  have hA := amplitude_nonneg d.root d.t₀ d.V d.hV J control Cside (zero_le_one.trans hCs)
  have hp := profileCap_sq_le_amplitude d.root N (root_slot_card k) Kslot hKslot d.hM
    d.t₀ d.V d.hV J control h00 Cside hCs
  have hside := hs.2 k d hK hcap
  have he := hf.2 k d.root d.hunit (minimum_cap Z d.root.L d.ell d.hZ d.hell d.hminimum)
    (d.hX₁.trans hlen) (d.hX₂.trans hlen) (d.hY₁.trans hlen) (d.hY₂.trans hlen)
    hP d.hpool hnorm hvol (amplitude d.root d.t₀ d.V J control Cside) (3*ε) hA hp
    (outer_loss_budget G ε hε).1 (by simpa only [SupplyFor,hK] using hside)
  change fullBallCost d.root (by norm_num) η (bΦ*Z) ≤ _ at he
  convert he using 1 <;> (try simp only [amplitude]) <;> ring

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceBallSupply
