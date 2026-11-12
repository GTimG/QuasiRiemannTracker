/- Copyright (c) 2026 Sil. Apache-2.0.
The reference rectangle of a root, at arbitrary lengths `X, Y` inside the original enclosure, is
literally the restored row consumed by the forward `K₃` domination (`Packet.Reduce.forward_dom`):
trivial ordinary punctures disappear (`rectangle_unpunctured`), the canonical slot coefficients
become the hole/height form of `slotBeta`, and the raised profiles are phase profiles. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Reference.Majorant
import Submissions.sil_density_split_20261026.CubeFree.Assembly.ParentRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonMaskEnergy CenteredMomentUncenteredTerminal
open QRH.SilDensitySplit.CubeFree.FP
open ReferencePrimeEnclosure MixedCanonicalSource NativeMaskedEnergy RestoredRootDictionary
open RestoredInitialSource
open Qrh.MarkedAnchor.Ordinary Qrh.MarkedAnchor.Ordinary.FP
open RestoredRootEnergy RecenteredRootRows
open CenteredMomentPrimeSlot (primePool)
open Candidate.FourthPower NativeFiniteHoles
open CenteredMomentAllocatedNaturalRadial CenteredMomentLattice CenteredMomentTwist
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable (M : Id) [NeZero M]
local instance instFiniteQuotRect : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {D : StepData} {α : Type} [Fintype α]

theorem empty_primes : ∀ P ∈ (∅ : Finset Id), Prime P := by simp

set_option maxHeartbeats 1000000 in
/-- **The reference rectangle is the forward row.** -/
theorem rectangle_eq_row (s : Setup M H D α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂)
    (η : Character) (z : O) (hz : z ≠ 0) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hXU : X ≤ (s.rootSource hH hn₁ hn₂).U₁) (hYU : Y ≤ (s.rootSource hH hn₁ hn₂).U₂) :
    rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y =
      RestorationFamily.row false (enclosure (16*s.Z^s.Lcap))
        ((naturalCharacter η z).excludePrimes ∅ empty_primes)
        (fun i : remainingSet s.r s.A => supportedPool (primePool M H 2 (s.Z^(s.w i.val))))
        (fun i => heightCoefficient (holeCoefficient
          (QRH.SilDensitySplit.CubeFree.Packet.Reduce.slotBeta M H hH s.W s.η₀ (fun i : remainingSet s.r s.A => s.θ i.val) s.Z
            (fun i => s.w i.val) (fun _ => 33/50) (fun i => s.v i.val))
          (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti) i) s.t)
        (fun i => s.Z^(s.w i.val))
        (phaseProfile (s.p.profile 0) (s.t/(2*Real.pi)))
        (phaseProfile (s.p.profile 1) (s.t/(2*Real.pi))) (9/4) X Y := by
  let r := s.rootData hn₁ hn₂
  have hW0 : (normPowerProfile (s.p.profile 0) (1/4) (9/4) (by norm_num) (s.p.support 0)
      ((s.p.profile 0).smooth ⊤) s.t : ℝ → ℂ) 0 = 0 := by
    by_contra h
    have hh := s.p.support 0 (normPowerProfile_support _ _ _ _ _ _ _ h)
    norm_num at hh
  have hstep := RestoredRootSource.rectangle_unpunctured (naturalCharacter η z)
    (enclosure (16*s.Z^s.Lcap)) r.pool r.pool_enclosed r.pool_prime (r.characters hH) r.R₀ s.t
    (fun i => slotProfile s.W (33/50) (s.v i.val)) (fun i => s.Z^(s.w i.val))
    (normPowerProfile (s.p.profile 0) (1/4) (9/4) (by norm_num) (s.p.support 0)
      ((s.p.profile 0).smooth ⊤) s.t)
    (normPowerProfile (s.p.profile 1) (1/4) (9/4) (by norm_num) (s.p.support 1)
      ((s.p.profile 1).smooth ⊤) s.t)
    hW0 (9/4) X Y hX hY
    (fun x hx => (s.p.support 0 (normPowerProfile_support _ _ _ _ _ _ _ hx)).2)
    (fun x hx => (s.p.support 1 (normPowerProfile_support _ _ _ _ _ _ _ hx)).2)
    (natural_character_off_supported η z hz)
    (by
      intro I hI hlen
      exact support_enclosed _ I hI (hlen.elim
        (fun h => h.trans ((mul_le_mul_of_nonneg_left hXU (by norm_num)).trans r.ordinary_caps.1))
        (fun h => h.trans ((mul_le_mul_of_nonneg_left hYU (by norm_num)).trans r.ordinary_caps.2))))
  refine (hstep : rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y = _).trans ?_
  have hcoef : (fun (i : remainingSet s.r s.A) (I : Id) =>
      slotCoefficient (r.characters hH) r.R₀ s.t i I *
        slotProfile s.W (33/50) (s.v i.val) (I.absNorm/s.Z^(s.w i.val))) =
      (fun i => heightCoefficient (holeCoefficient
          (QRH.SilDensitySplit.CubeFree.Packet.Reduce.slotBeta M H hH s.W s.η₀ (fun i : remainingSet s.r s.A => s.θ i.val) s.Z
            (fun i => s.w i.val) (fun _ => 33/50) (fun i => s.v i.val))
          (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti) i) s.t) := by
    funext i I
    exact slot_coefficient_identity (r.characters hH) r.R₀ s.W (fun i => s.Z^(s.w i.val))
      (fun _ => 33/50) (fun i => s.v i.val) s.t i I
  rw [hcoef, MixedPrincipalHeights.norm_power_profile_phase,
    MixedPrincipalHeights.norm_power_profile_phase]
  exact QRH.SilDensitySplit.CubeFree.Assembly.row_idealCoeff_congr false _ _ _
    (fun I => (QRH.SilDensitySplit.CubeFree.Assembly.excludePrimes_empty_coeff _ empty_primes I).symm)
    _ _ _ _ _ _ _ _

end
end Qrh.MarkedAnchor.Ordinary.Reference
