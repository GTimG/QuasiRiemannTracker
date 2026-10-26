/- Copyright (c) 2026 Sil. Apache-2.0.
Compact descendant conclusions over an ABSTRACT first Source. Their fields
are exactly the original conjunctions. Generic proofs use only numerical
support caps and are reused by the root-specialized theorems.
No extra analytic premise.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedCapEvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedDescendantBounds
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open MixedFirstExceptionalWindow MixedFirstExceptionalCaps
open OuterFreshSource OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedRootCaps RepairedCapEvent
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {κ : Type u} [Fintype κ]

/-- Exactly the former six support-cap conjuncts, with the first source
abstract rather than an expanded allocation of an expanded root. -/
def SupportBounds (N : ℕ) (Z : ℝ) (s : Source κ (1/4) (9/4))
    (cover : OriginalEnclosure s) (u : Id) (L : Finset κ) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s (by norm_num) u L J)) : Prop :=
  let q : Data κ := supplierData s (by norm_num) u L J
  let r : Source (RestIndex q) (1/4) (9/4) := residualSource s (by norm_num) cover u L J x
  Fintype.card (RestIndex q) ≤ N ∧ (∏ i,r.P i) ≤ Z ∧ (∏ i,2*r.P i) ≤ Z^(2:ℝ) ∧
    sourceNormCap r.P (9/4) r.T r.d ≤ Z^(2:ℝ) ∧ poolCap r ≤ Z^(8:ℝ) ∧
    secondSourceEnvelope r ≤ Z^(2:ℝ)

/-- Exactly the former frozen-product, residual-R and selected-product
conjuncts. No active/nonzero hypothesis is part of the definition. -/
def FrozenBounds (Z : ℝ) (s : Source κ (1/4) (9/4))
    (cover : OriginalEnclosure s) (u : Id) (L : Finset κ) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s (by norm_num) u L J)) : Prop :=
  let q : Data κ := supplierData s (by norm_num) u L J
  let r : Source (RestIndex q) (1/4) (9/4) := residualSource s (by norm_num) cover u L J x
  ((frozenProduct q x).absNorm:ℝ) ≤ Z^(2:ℝ) ∧ (r.R.absNorm:ℝ) ≤ Z^(4:ℝ) ∧
    ∀ y ∈ activeSelected q, ((selectedProduct q y).absNorm:ℝ) ≤ Z^(2:ℝ)

theorem support_of_first_caps (N : ℕ) (Z : ℝ)
    (s : Source κ (1/4) (9/4)) (cover : OriginalEnclosure s)
    (hcard : Fintype.card κ ≤ N) (hprod : (∏ i,s.P i) ≤ Z)
    (hdouble : (∏ i,2*s.P i) ≤ Z^(2:ℝ))
    (hnorm : sourceNormCap s.P (9/4) s.T s.d ≤ Z^(2:ℝ))
    (hX₁ : s.X₁ ≤ Z^(3:ℝ)) (hX₂ : s.X₂ ≤ Z^(3:ℝ))
    (hY₁ : s.Y₁ ≤ Z^(3:ℝ)) (hY₂ : s.Y₂ ≤ Z^(3:ℝ))
    (hpool : PoolBound.{u} N Z)
    (u : Id) (L : Finset κ) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s (by norm_num) u L J)) :
    SupportBounds N Z s cover u L J x := by
  unfold SupportBounds
  intro q r
  have hn : Fintype.card (RestIndex q) ≤ N := (rest_card_le q).trans hcard
  have hp : (∏ i,r.P i) ≤ Z := (rest_prod_le q s.P s.hP).trans hprod
  have hp2 : (∏ i,2*r.P i) ≤ Z^(2:ℝ) :=
    (residual_scale_product s (by norm_num) cover u L J x).trans hdouble
  have hnr : sourceNormCap r.P (9/4) r.T r.d ≤ Z^(2:ℝ) :=
    (residual_norm_cap s (by norm_num) cover u L J x).trans hnorm
  have hpr : poolCap r ≤ Z^(8:ℝ) := hpool (RestIndex q) r hn hX₁ hX₂ hY₁ hY₂ hp
  exact ⟨hn,hp,hp2,hnr,hpr,(envelope_eq_normcap r).trans_le hnr⟩

theorem frozen_of_first_caps (Z : ℝ) (hZ : 1 < Z)
    (s : Source κ (1/4) (9/4)) (cover : OriginalEnclosure s)
    (hdouble : (∏ i,2*s.P i) ≤ Z^(2:ℝ)) (hR : (s.R.absNorm:ℝ) ≤ Z^(2:ℝ))
    (u : Id) (L : Finset κ) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s (by norm_num) u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s (by norm_num) u L J) x ≠ 0) :
    FrozenBounds Z s cover u L J x := by
  unfold FrozenBounds
  intro q r
  have hf := (OuterFreshSource.frozen_norm_le s (by norm_num) u L J x hx).trans hdouble
  have hr : (r.R.absNorm:ℝ) ≤ Z^(4:ℝ) := by
    change ((s.R*frozenProduct q x).absNorm:ℝ) ≤ _
    simp only [map_mul,Nat.cast_mul]
    apply (mul_le_mul hR hf (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
    rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    norm_num
  refine ⟨hf,hr,?_⟩
  intro y hy
  exact (OuterFreshSource.selected_norm_le s (by norm_num) u L J y
    (Finset.mem_filter.mp hy).2.2).trans hdouble

end
end Candidate.FourthPower.RepairedDescendantBounds
