/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Actual retained child upper cap and exact second-cutoff caps. Kchild may
be below one; its polynomial inverse is supplied by RepairedRootCaps.

Modified by Sil (2026-10-26): over RootInput G and cutoffLoss G N eps; child_upper_cap uses Event.freq (FP: OuterFresh uniform event); second_cutoff_caps dropped (secondSourceEnvelope belongs to the replaced OuterFresh lane).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedDescendantCaps

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedChildCaps
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate CenteredMomentFirstScale
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstCutoffs MixedFirstExceptionalNormalization
open Qrh.MarkedAnchor.Ordinary.RootParameters RepairedRawContext RepairedRootCaps RepairedCapEvent
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem cutoff_le_one {D : StepData} (G : StepGates D) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    cutoffLoss G N ε ≤ 1 := by
  have hi := (internal_spec G N ε hε).2.2.1
  have ho := (omega_spec G ε hε).2.2.2
  unfold cutoffLoss
  linarith

variable {D : StepData} {G : StepGates D}
variable (M : Id) [NeZero M]
local instance instFiniteQuotChildCaps : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput G M H hH ι Wslot N Holes ε Z Kslot η η₀)

theorem child_upper_cap (hε : 0 < ε) (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} G N ε Z)
    (p : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1))
    (E : Finset (CommonIndex p.val.1 p.val.2)) (τ : Character)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex p.val.1 p.val.2 => P.val) E*activeConductor p.val.1 p.val.2})
    (n : ℤ) (hret : Retained (frequencyRadius (firstCutoff p.val.1 p.val.2 E d.Kroot (sourceVolume d.root))
      Z (cutoffLoss G N ε)) n) :
    nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss G N ε) n ≤ Z^(9:ℝ) := by
  have hz := zero_lt_one.trans d.one_lt_Z
  have hs := commonLabels_supported _ _ _ p.property
  have hCD : CompletedGauss.primeSupport p.val.1 = CompletedGauss.primeSupport p.val.2 :=
    (commonLabels_data _ _ _ _ p.property).2.2
  have hτcap := first_modulus_cap M H hH d hcard hevent.dimension hevent.presentation p E τ hmod
  have hτpos : 0 < (τ.modulus.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hτlog := Real.logb_le_logb_of_le d.one_lt_Z hτpos hτcap
  rw [Real.logb_rpow hz d.one_lt_Z.ne'] at hτlog
  have hvlog := Real.logb_le_logb_of_le d.one_lt_Z (sourceVolume_pos d.root) (root_volume_cap M H hH d)
  rw [Real.logb_self_eq_one d.one_lt_Z] at hvlog
  have hclog := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le hs.1.1)
  have hKlog : 1 ≤ Real.logb Z d.Kroot := by
    simpa only [Real.logb_self_eq_one d.one_lt_Z] using Real.logb_le_logb_of_le d.one_lt_Z hz d.hKlow
  have hηlog := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le η.modulus_ne_bot)
  have hFlog := Real.logb_nonneg d.one_lt_Z fixed_presentation_one_le
  have hR : 1 ≤ inputWidth η d.Kroot Z := by unfold inputWidth; linarith
  have hpad : 0 ≤ cutoffLoss G N ε := (internal_losses_paid G N ε hε).1.le
  have hpad1 := cutoff_le_one G N ε hε
  have he := retained_child_log η τ p.val.1 p.val.2 hs.1 hs.2 hCD E d.Kroot (sourceVolume d.root) Z
    (firstCutoff p.val.1 p.val.2 E d.Kroot (sourceVolume d.root)) 1 (cutoffLoss G N ε) (cutoffLoss G N ε)
    d.radial_pos (sourceVolume_pos d.root) d.one_lt_Z (by norm_num) hpad hmod
    (by simp only [firstCutoff,one_mul] <;> exact le_rfl) n hret
  have hlog : Real.logb Z (nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss G N ε) n) ≤ 9 := by
    linarith [hevent.freq]
  have hp := Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le hlog
  have hchild : 0 < nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss G N ε) n := by
    unfold nominalChildScale
    exact Real.rpow_pos_of_pos hz _
  rwa [Real.rpow_logb hz d.one_lt_Z.ne' hchild] at hp

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedChildCaps
