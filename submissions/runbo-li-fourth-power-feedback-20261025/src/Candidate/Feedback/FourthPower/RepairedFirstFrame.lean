/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first common/retained data BEFORE choosing a genuine allocation.
This is a structural record only. It permits the first finite allocation
sum to be assembled without assuming an active allocation exists.
-/
import Candidate.Feedback.FourthPower.RepairedFirstPoint

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedFirstFrame
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedFirstCutoffs MixedFirstExceptionalNormalization
open RepairedRawContext RepairedRootParameters RepairedFirstPoint
open CenteredMomentSecondBlockAggregate
open CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character}

section
-- Keep source enumerations opaque only during auxiliary structure generation.
attribute [local irreducible] MixedPrincipalWindow.sourceColumns
  MixedPrincipalWindow.sourceCoefficient MixedPrincipalAllocations.tuplePools

structure Frame (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀) where
  label : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)
  inactive : Finset (CommonIndex label.val.1 label.val.2)
  tau : Character
  modulus : tau.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex label.val.1 label.val.2 => P.val) inactive*
      activeConductor label.val.1 label.val.2}
  index : ℤ
  retained : Retained (frequencyRadius
    (firstCutoff label.val.1 label.val.2 inactive d.Kroot (sourceVolume d.root)) Z (cutoffLoss N ε)) index

end

namespace Frame
variable {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀} (f : Frame d)
def scale : ℝ := nominalChildScale f.label.val.1 f.label.val.2 f.inactive d.Kroot
  (sourceVolume d.root) Z (cutoffLoss N ε) f.index
def reference : ℝ := MixedFirstExceptionalNormalization.reference f.tau f.label.val.1 f.label.val.2
  (sourceVolume d.root) Z
def point (B : actualAllocations (tuplePools d.root) f.label.val.1)
    (hf : frozenCoefficient B.val f.label.val.1 d.root.R d.root.ν d.root.Wslot d.root.P ≠ 0) : Point d :=
  ⟨f.label,f.inactive,B,hf,f.tau,f.modulus,f.index,f.retained⟩
end Frame
end
end Candidate.Feedback.FourthPower.RepairedFirstFrame
