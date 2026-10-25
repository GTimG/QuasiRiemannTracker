/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first/supplier support caps with fixed exponents2 and8. The point
source definitions keep dependent data out of repeated root statements.

-/
import Candidate.Feedback.FourthPower.RepairedDescendantBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedDescendantCaps
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
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open MixedFirstExceptionalWindow MixedFirstExceptionalCaps
open OuterFreshSource OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedRawContext RepairedRootCaps RepairedCapEvent RepairedDescendantBounds
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (priority := 2000) {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀)

def firstSource (G : Id) (B : actualAllocations (tuplePools d.root) G) : Source (liveIndices B.val) (1/4) (9/4) :=
  allocatedLiveSource d.root (by norm_num) d.cover G B

def firstCover (G : Id) (B : actualAllocations (tuplePools d.root) G) : OriginalEnclosure (firstSource M H hH d G B) :=
  live_enclosure (allocationSource d.root (by norm_num) d.cover G B)

theorem first_product_caps (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z)
    (G : Id) (B : actualAllocations (tuplePools d.root) G) :
    Fintype.card (liveIndices B.val) ≤ N ∧
      (∏ i,(firstSource M H hH d G B).P i) ≤ Z ∧
      (∏ i,2*(firstSource M H hH d G B).P i) ≤ Z^(2:ℝ) := by
  let s := firstSource M H hH d G B
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
  refine ⟨hn,hp,?_⟩
  change (∏ i,2*s.P i) ≤ _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  apply (mul_le_mul htwo hp (Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.hP i)))
    (zero_lt_one.trans d.one_lt_Z).le).trans_eq
  rw [Real.rpow_two]
  ring

/-- The SAME six caps as before, behind an abstract-Source definition.
No nonzero frozen weight is required for support caps. -/
theorem residual_support_caps (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z)
    (G : Id) (B : actualAllocations (tuplePools d.root) G) (u : Id)
    (L : Finset (liveIndices B.val)) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData (firstSource M H hH d G B) (by norm_num) u L J)) :
    SupportBounds N Z (firstSource M H hH d G B) (firstCover M H hH d G B) u L J x := by
  let s := firstSource M H hH d G B
  let cover := firstCover M H hH d G B
  change SupportBounds N Z s cover u L J x
  have hfirst := first_product_caps M H hH d hcard hevent G B
  have hallocated := allocated_size_caps d.root (by norm_num) d.cover G B
  have hnorm : sourceNormCap s.P (9/4) s.T s.d ≤ Z^(2:ℝ) :=
    hallocated.2.2.2.trans (root_norm_cap_two M H hH d hcard hevent.dimension)
  exact support_of_first_caps N Z s cover hfirst.1 hfirst.2.1 hfirst.2.2 hnorm
    d.hX₁ d.hX₂ d.hY₁ d.hY₂ hevent.pool u L J x

/-- The SAME frozen/selected-product caps as before, with the original
nonzero frozen coefficient hypothesis retained exactly. -/
theorem residual_frozen_caps (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z)
    (G : Id) (hG : (G.absNorm:ℝ) ≤ Z^(2:ℝ)) (B : actualAllocations (tuplePools d.root) G) (u : Id)
    (L : Finset (liveIndices B.val)) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData (firstSource M H hH d G B) (by norm_num) u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData (firstSource M H hH d G B) (by norm_num) u L J) x ≠ 0) :
    FrozenBounds Z (firstSource M H hH d G B) (firstCover M H hH d G B) u L J x := by
  let s := firstSource M H hH d G B
  let cover := firstCover M H hH d G B
  change FrozenBounds Z s cover u L J x
  have hp2 := (first_product_caps M H hH d hcard hevent G B).2.2
  have hsR : (s.R.absNorm:ℝ) ≤ Z^(2:ℝ) := by
    change ((d.root.R*G).absNorm:ℝ) ≤ _
    simpa only [d.hR,one_mul] using hG
  exact frozen_of_first_caps Z d.one_lt_Z s cover hp2 hsR u L J x hx

end
end Candidate.Feedback.FourthPower.RepairedDescendantCaps
