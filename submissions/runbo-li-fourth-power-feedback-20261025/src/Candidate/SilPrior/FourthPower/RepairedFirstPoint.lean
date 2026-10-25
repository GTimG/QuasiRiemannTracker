/- Copyright (c) 2026 Sil. Apache-2.0.
Dependent first-common data and named supplier sources. All fields are
actual data/structural proofs; there is no energy bound in this record.
Named projections keep later analytic statements compact.
-/
import Candidate.SilPrior.FourthPower.RepairedConductorCaps

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedFirstPoint
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open CenteredMomentSecondBlockAggregate
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedSupplierFourthRow MixedSupplierSource MixedInnerExceptionalBlock
open MixedFirstCutoffs MixedFirstExceptionalNormalization
open OuterFreshSource OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedRawContext RepairedRootParameters RepairedDescendantCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

section
-- Avoid unfolding finite source enumerations while Lean generates noConfusion.
-- This local elaboration setting does not change the structure's field types.
attribute [local irreducible] MixedPrincipalWindow.sourceColumns
  MixedPrincipalWindow.sourceCoefficient MixedPrincipalAllocations.tuplePools

structure Point (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀) where
  label : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)
  inactive : Finset (CommonIndex label.val.1 label.val.2)
  allocation : actualAllocations (tuplePools d.root) label.val.1
  frozen_nonzero : frozenCoefficient allocation.val label.val.1 d.root.R d.root.ν d.root.Wslot d.root.P ≠ 0
  tau : Character
  modulus : tau.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex label.val.1 label.val.2 => P.val) inactive*
      activeConductor label.val.1 label.val.2}
  index : ℤ
  retained : Retained (frequencyRadius
    (firstCutoff label.val.1 label.val.2 inactive d.Kroot (sourceVolume d.root)) Z (cutoffLoss N ε)) index

end

namespace Point
variable {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀} (p : Point d)

abbrev Index := liveIndices p.allocation.val

local instance (priority := 2000) : DecidableEq p.Index := Classical.decEq _

def source : Source p.Index (1/4) (9/4) := firstSource M H hH d p.label.val.1 p.allocation
def cover : OriginalEnclosure p.source := firstCover M H hH d p.label.val.1 p.allocation
def selection (hε : 0 < ε) (L : Finset p.Index) : Finset {i // i ∉ Lᶜ} := d.choose hε p.label.val.1 p.allocation L
def large (L : Finset p.Index) : Prop := d.large p.label.val.1 p.allocation L
def data (hε : 0 < ε) (u : Id) (L : Finset p.Index) : Data p.Index :=
  supplierData p.source (by norm_num) u L (p.selection hε L)
def residual (hε : 0 < ε) (u : Id) (L : Finset p.Index) (x : Frozen (p.data hε u L)) :
    Source (RestIndex (p.data hε u L)) (1/4) (9/4) :=
  residualSource p.source (by norm_num) p.cover u L (p.selection hε L) x
def unavoided (hε : 0 < ε) (u : Id) (L : Finset p.Index) (x : Frozen (p.data hε u L)) :
    Source (RestIndex (p.data hε u L)) (1/4) (9/4) :=
  unavoidedResidual p.source (by norm_num) p.cover u L (p.selection hε L) x
def scale : ℝ := nominalChildScale p.label.val.1 p.label.val.2 p.inactive d.Kroot
  (sourceVolume d.root) Z (cutoffLoss N ε) p.index
def cutoff (hε : 0 < ε) (u : Id) (L : Finset p.Index) (x : Frozen (p.data hε u L)) : ℝ :=
  secondSourceCutoff (p.residual hε u L x) p.scale
def radius (hε : 0 < ε) (u : Id) (L : Finset p.Index) (x : Frozen (p.data hε u L)) : ℝ :=
  frequencyRadius (p.cutoff hε u L x) Z (cutoffLoss N ε)

end Point
end
end Candidate.SilPrior.FourthPower.RepairedFirstPoint
