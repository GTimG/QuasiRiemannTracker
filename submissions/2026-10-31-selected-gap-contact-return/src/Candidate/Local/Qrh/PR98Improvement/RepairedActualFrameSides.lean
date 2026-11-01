/- Reserve-parametric adaptation by Joseph Bebel (2026). -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Both actual orientations of each retained first block. The original
artificial divisor is capped by the FULL source pool, not active support.
All source/scale/reference identities are literal; no new estimate occurs.
-/
import Candidate.Local.Qrh.PR98Improvement.RepairedCombinedFinite

set_option autoImplicit false
namespace Candidate.PR98.RepairedActualFrameSides
universe u
noncomputable section
variable [Candidate.PR98.RepairedRootParameters.Reserve]
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSecondBlockAggregate CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstSectorTransform (commonLabels_supported)
open CenteredMomentFirstMixedRightTransport CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedFirstCommonSum MixedFirstPhysicalApplication
open MixedFirstExceptionalNormalization MixedFirstCutoffs MixedFirstActualBandGeometry
open MixedFirstRetainedFixed (firstRadius)
open Candidate.PR98.RepairedRootParameters Candidate.PR98.RepairedRawContext Candidate.PR98.RepairedFirstFrame Candidate.PR98.RepairedSourceSideSupply
open RepairedFirstRawSides Candidate.PR98.RepairedFirstRawRetained Candidate.PR98.RepairedContributionContract Candidate.PR98.RepairedCombinedFinite
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem common_label_swap (S : Finset Id) (C D : Id)
    (h : (C,D) ∈ CenteredMomentFirstSectors.commonLabels S S) :
    (D,C) ∈ CenteredMomentFirstSectors.commonLabels S S := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Finset.mem_product.mp hp with ⟨h₁,h₂⟩
  apply Finset.mem_image.mpr
  refine ⟨(p.2,p.1),Finset.mem_product.mpr ⟨h₂,h₁⟩,?_⟩
  exact congrArg Prod.swap he

def swapped_label {S : Finset Id} {β : Id → ℂ} (p : ActiveLabel S β) : ActiveLabel S β :=
  ⟨(p.val.2,p.val.1),common_label_swap _ _ _ p.property⟩

variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} (d : RootInput M H hH ι W N Holes ε Z Kslot η η₀)

/-- This is the actual first artificial pool from the retained formula.
No use is made of an active-only norm cap or a radical approximation. -/
theorem actual_artificial_gates (C D : Id) (hD : D ≠ 0) (u : Id)
    (hu : u ∈ artificialDivisors d.root C D hD)
    (hμ : (UniqueFactorizationMonoid.moebius u:ℂ) ≠ 0) :
    Squarefree u ∧ (u.absNorm:ℝ) ≤ Z^(8:ℝ) :=
  ⟨squarefree_of_moebius_ne_zero u hμ,
    (artificial_norm d.root (by norm_num) C D hD u hu).2.trans d.hpool⟩

/-- Converts the established all-Frame raw bound to the exact
retained-side predicate, constructing both frames internally. KL and KR
remain separate actual nominal scales throughout. -/
theorem retained_of_frame_raw (J : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hraw : FrameRawFor d J S C) : SupplyFor d J S C := by
  intro p E hE n
  have hs := commonLabels_supported (activeSource (sourceColumns d.root)
    (sourceCoefficient d.root (by norm_num) 1)) p
  have hret₀ := block_retained (effectiveScale p.val.1 p.val.2 E d.Kroot)
    (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss N ε))
    (Z^(8:ℝ)/p.val.1.absNorm) (Z^(8:ℝ)/p.val.2.absNorm) n
  have hret : Retained (frequencyRadius
      (firstCutoff p.val.1 p.val.2 E d.Kroot (MixedInnerExceptionalBlock.sourceVolume d.root))
      Z (cutoffLoss N ε)) (n 1:ℤ) := by
    simpa only [actual_radius_eq] using hret₀
  intro u hu hμ χ ξ F
  let left : Frame d :=
    { label := p
      inactive := E
      tau := F.left
      modulus := F.left_modulus
      index := (n 1:ℤ)
      retained := hret }
  let right : Frame d :=
    { label := swapped_label p
      inactive := swapSubset p.val.1 p.val.2 E
      tau := F.right
      modulus := by simpa only [swapped_label] using right_modulus η p.val.1 p.val.2 hs.1 E χ (ξ⁻¹) F
      index := (n 1:ℤ)
      retained := by simpa only [swapped_label,firstCutoff_swap] using hret }
  have hgates := actual_artificial_gates d p.val.1 p.val.2 hs.2.1 u hu hμ
  constructor
  · intro tp
    have he := hraw left u hgates.1 hgates.2 tp
    convert he using 1 <;> first | rfl |
      (simp only [left,Frame.scale,Frame.reference,contributionBound,sideBudget] <;> rfl)
  · intro tp
    have he := hraw right u hgates.1 hgates.2 tp
    convert he using 1 <;> first | rfl |
      (simp only [right,swapped_label,Frame.scale,Frame.reference,contributionBound,sideBudget] <;> rfl)

end
end Candidate.PR98.RepairedActualFrameSides
