/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first/supplier support caps with fixed exponents2 and8. The point
source definitions keep dependent data out of repeated root statements.

Modified by Sil (2026-10-26): over RootInput G; firstSource/firstCover and first_product_caps kept; first_norm_cap added (the first-source half of FP residual_support_caps); residual_support_caps/residual_frozen_caps (u-freezing residuals, not ported) dropped.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedDescendantBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedDescendantCaps
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalSource CenteredMomentFirstSectors CenteredMomentActiveSource
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open MixedFirstExceptionalWindow MixedFirstExceptionalCaps
open RepairedRawContext RepairedRootCaps RepairedCapEvent RepairedDescendantBounds
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqDescendantCaps {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (priority := 2000) instDecEqSubtypeDescendantCaps {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {D : StepData} {G : StepGates D}
variable (M : Id) [NeZero M]
local instance instFiniteQuotDescendantCaps : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput G M H hH ι Wslot N Holes ε Z Kslot η η₀)

/-- The genuine (unfrozen) first live source of an allocation of the first common factor. -/
def firstSource (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁) :
    Source (liveIndices B.val) (1/4) (9/4) :=
  allocatedLiveSource d.root (by norm_num) d.cover G₁ B

def firstCover (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁) :
    OriginalEnclosure (firstSource M H hH d G₁ B) :=
  live_enclosure (allocationSource d.root (by norm_num) d.cover G₁ B)

theorem first_product_caps (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} G N ε Z)
    (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁) :
    Fintype.card (liveIndices B.val) ≤ N ∧
      (∏ i,(firstSource M H hH d G₁ B).P i) ≤ Z ∧
      (∏ i,2*(firstSource M H hH d G₁ B).P i) ≤ Z^(2:ℝ) := by
  let s := firstSource M H hH d G₁ B
  have hn : Fintype.card (liveIndices B.val) ≤ N :=
    (Fintype.card_le_of_injective (fun i : liveIndices B.val => i.val) Subtype.val_injective).trans hcard
  have hp : (∏ i,s.P i) ≤ Z :=
    (injected_prod_le (fun i : liveIndices B.val => i.val) Subtype.val_injective d.root.P d.root.hP).trans
      (root_product_cap M H hH d)
  have htwo : (2:ℝ)^Fintype.card (liveIndices B.val) ≤ Z := by
    calc
      _ ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hn
      _ ≤ (9/4:ℝ)^2*(2:ℝ)^N := le_mul_of_one_le_left (by positivity) (by norm_num)
      _ ≤ Z := hevent.dimension
  exact ⟨hn, hp, double_product_le s.P s.hP Z (zero_lt_one.trans d.one_lt_Z).le htwo hp⟩

/-- The sharp norm cap of the first live source (FP: inside `residual_support_caps`). -/
theorem first_norm_cap (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} G N ε Z)
    (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁) :
    sourceNormCap (firstSource M H hH d G₁ B).P (9/4) (firstSource M H hH d G₁ B).T
      (firstSource M H hH d G₁ B).d ≤ Z^(2:ℝ) :=
  (allocated_size_caps d.root (by norm_num) d.cover G₁ B).2.2.2.trans
    (root_norm_cap_two M H hH d hcard hevent.dimension)

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedDescendantCaps
