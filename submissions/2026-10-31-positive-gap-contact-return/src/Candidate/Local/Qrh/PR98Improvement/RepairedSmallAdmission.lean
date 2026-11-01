/- Reserve-parametric adaptation by Joseph Bebel (2026). -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Actual small branch of the shared RootInput, before any analytic estimate.
The canonical residual, coefficient avoidance, slot width and profiles
are derived from the actual first allocation and the actual chosenSlots.

-/
import Candidate.Local.Qrh.PR98Improvement.RepairedRawContext
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedSmallSupplier
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshSelectedWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.PR98.RepairedSmallAdmission
universe u
noncomputable section
variable [Candidate.PR98.RepairedRootParameters.Reserve]
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedFirstActualNonexceptional MixedFirstAvoidance MixedSupplierFourthRow MixedSupplierSource
open OuterFreshSource OuterFreshSelection OuterFreshSelectedWindow
open RepairedRawContext RepairedRootParameters RepairedRawSupplier
open MixedFirstExceptionalWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ}
variable {ε Z Kslot : ℝ} {η η₀ : Character}

/-- The original seven residual facts over an ABSTRACT first source.
Keeping the source abstract avoids expanding an entire allocated root while
elaborating Canonical. This transparent predicate adds no hypothesis. -/
def ResidualFacts {κ : Type u} [Fintype κ]
    (Wslot : ℝ → ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : κ → RayQuotient.Characters M H) (w σ freq : κ → ℝ) (t₀ : ℝ)
    (R₀ : κ → Finset Id) (s : Source κ (1/4) (9/4))
    (cover : OriginalEnclosure s) (u : Id) (L : Finset κ)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s (by norm_num) u L J)) : Prop :=
  let q : Data κ := supplierData s (by norm_num) u L J;
  let r : Source (RestIndex q) (1/4) (9/4) :=
    unavoidedResidual s (by norm_num) cover u L J x;
  Canonical M H hH Wslot Cap Lcap Z η₀
      (fun i : RestIndex q=>θ i.val.val) (fun i=>w i.val.val)
      (fun i=>σ i.val.val) (fun i=>freq i.val.val) t₀ (fun i=>R₀ i.val.val) r ∧
    residualSource s (by norm_num) cover u L J x=avoidSource r u ∧
    r.W₁=s.W₁ ∧ r.W₂=s.W₂ ∧ r.t₁=s.t₁ ∧ r.t₂=s.t₂ ∧ r.L=s.L

/-- This is only the already proved literal residual-canonical map plus
the six definitional coefficient/profile identities. -/
theorem residual_facts_of_canonical {κ : Type u} [Fintype κ]
    (Wslot : ℝ → ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : κ → RayQuotient.Characters M H) (w σ freq : κ → ℝ) (t₀ : ℝ)
    (R₀ : κ → Finset Id) (s : Source κ (1/4) (9/4))
    (hcan : Canonical M H hH Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset κ)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s (by norm_num) u L J)) :
    ResidualFacts M H hH Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s cover u L J x := by
  unfold ResidualFacts
  intro q r
  exact ⟨residual_canonical M H hH Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s hcan
    (by norm_num) cover u L J x,
    residual_is_avoided s (by norm_num) cover u L J x,rfl,rfl,rfl,rfl,rfl⟩

section ActualRoot
variable (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀) (hε : 0<ε)
variable (G u : Id) (B : actualAllocations (tuplePools d.root) G)

-- Match the first-live index without changing nested residual instances.
local instance (priority := 2000) : DecidableEq (liveIndices B.val) := Classical.decEq _

/-- Same result as the former expanded statement, through the transparent
ResidualFacts abbreviation. Expanding it and the original source lets gives
the identical Canonical, avoidance and five profile/minimum conjuncts. -/
theorem actual_small_residual
    (L : Finset (liveIndices B.val)) (hsmall : ¬d.large G B L) :
    let first : Source (liveIndices B.val) (1/4) (9/4) :=
      allocatedLiveSource d.root (by norm_num) d.cover G B;
    let cover : OriginalEnclosure first :=
      live_enclosure (allocationSource d.root (by norm_num) d.cover G B);
    let J : Finset {i : liveIndices B.val // i∉Lᶜ} := d.choose hε G B L;
    let q : Data (liveIndices B.val) := supplierData first (by norm_num) u L J;
    J=∅ ∧
      (∑i : RestIndex q,d.w i.val.val.val)≤widthFloor ε ∧
      Fintype.card (RestIndex q)≤Fintype.card ι ∧
      ∀x : Frozen q,
        ResidualFacts M H hH Wslot 16 (windowCap N ε) Z η₀
          (fun i : liveIndices B.val=>d.chars i.val) (fun i=>d.w i.val)
          (fun _=>33/50) (fun i=>d.freq i.val) d.t₀ (fun i=>d.R₀ i.val)
          first cover u L J x := by
  intro first cover J q
  have hwidth : liveWidth L (fun i=>d.w i.val)≤widthFloor ε := le_of_not_gt hsmall
  have hJ : J=∅ := (chosen_small first (by norm_num) u L (fun i=>d.w i.val)
    (widthFloor ε) (mesh ε) (mesh_spec ε hε).1.le
    (fun i=>d.hw i.val) (fun i=>d.hwm i.val) hwidth).1
  have he := remaining_width first (by norm_num) u L J (fun i=>d.w i.val)
  have hselected : (∑i : J,d.w i.val.val.val)=0 := by
    rw [hJ]
    simp
  have hrest : (∑i : RestIndex q,d.w i.val.val.val)≤widthFloor ε := by
    change (∑i : RestIndex q,d.w i.val.val.val)+(∑i : J,d.w i.val.val.val)=
      liveWidth L (fun i=>d.w i.val) at he
    linarith
  have hcard := (rest_card_le q).trans
    (Fintype.card_le_of_injective (fun i : liveIndices B.val=>i.val) Subtype.val_injective)
  have hcan := allocated_canonical M H hH Wslot 16 (windowCap N ε) Z η₀
    d.chars d.w (fun _=>33/50) d.freq d.t₀ d.R₀ d.root d.hcanonical
    (by norm_num) d.cover G B
  refine ⟨hJ,hrest,hcard,?_⟩
  intro x
  exact residual_facts_of_canonical M H hH Wslot 16 (windowCap N ε) Z η₀
    (fun i : liveIndices B.val=>d.chars i.val) (fun i=>d.w i.val)
    (fun _=>33/50) (fun i=>d.freq i.val) d.t₀ (fun i=>d.R₀ i.val)
    first hcan cover u L J x

end ActualRoot

/-- Every active frozen supplier is supported by its ORIGINAL prime pools. -/
theorem actual_frozen_supported {κ : Type u} [Fintype κ] {a b : ℝ}
    (s : Source κ a b) (ha : 0<a) (u : Id) (L : Finset κ)
    (J : Finset {i // i∉Lᶜ}) (x : activeFrozen (supplierData s ha u L J)) :
    Supported (frozenProduct (supplierData s ha u L J) x.val) :=
  ReferenceProductEnergy.supported_product (fun i : ↥Lᶜ=>(x.val i).val)
    (fun i => (s.hpn i.val _ (frozen_slot_mem s ha u L J x.val
      (Finset.mem_filter.mp x.property).2.2 i)).1)

theorem actual_global_avoidance {κ : Type u} [Fintype κ] {a b : ℝ}
    (s : Source κ a b) (ha : 0<a) (cover : OriginalEnclosure s) (u : Id)
    (L : Finset κ) (J : Finset {i // i∉Lᶜ})
    (x : activeFrozen (supplierData s ha u L J)) :
    u∣(unavoidedResidual s ha cover u L J x.val).R*
      residualSeed (supplierData s ha u L J) x := by
  exact supplier_dvd_puncture s.R (frozenProduct (supplierData s ha u L J) x.val)
    (residualSeed (supplierData s ha u L J) x) u
    (residualSeed (supplierData s ha u L J) x) (residualSeed_spec _ x) dvd_rfl

end
end Candidate.PR98.RepairedSmallAdmission
