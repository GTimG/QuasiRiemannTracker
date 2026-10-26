/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.Cone

set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OAI.SevenEighths.Record12518109Natural.Valuation
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSecondCanonical
open Cycle61Moment Cycle61HighGeometry CenteredMomentCommonSupport
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss
local notation "O" => HeckeFamily.O

theorem active_ideal_product (C D : Ideal O) :
    Ideal.span {activeConductor C D}=
      ∏ P : CommonIndex C D,
        if netExponent (leftExponent C D P) (rightExponent C D P)=0 then 1 else P.val := by
  rw [activeConductor,span_finitePrimeModulus]
  change (∏ P : ActiveIndex C D,P.val.val)=_
  rw [Finset.prod_coe_sort]
  simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro P hP
  split_ifs <;> simp_all

theorem cancelled_ideal_product (left : Bool) (C D : Ideal O) :
    cancelledRadical left C D=
      ∏ P : CommonIndex C D,
        if netExponent (leftExponent C D P) (rightExponent C D P)=
          (if left then 5 else 1) then P.val else 1 := by
  cases left
  · unfold cancelledRadical firstRightCancelledRadical firstRightCancelled
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1) P.val)=_
    rw [Finset.prod_coe_sort (s:=CenteredMomentActive.activeSupport
      (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D))
      (f:=fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1)]
    simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P hP
    have hk := netExponent_lt_six (leftExponent C D P) (rightExponent C D P)
    split_ifs <;> simp_all <;> omega
  · unfold cancelledRadical firstLeftCancelledRadical firstLeftCancelled
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1) P.val)=_
    rw [Finset.prod_coe_sort (s:=CenteredMomentActive.activeSupport
      (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D))
      (f:=fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1)]
    simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P hP
    have hk := netExponent_lt_six (leftExponent C D P) (rightExponent C D P)
    split_ifs <;> simp_all <;> omega

theorem logb_nat_prod_pow {ι : Type*} [Fintype ι] (N : ι → ℕ) (e : ι → ℕ)
    (hN : ∀ t,0 < N t) (Z : ℝ) :
    Real.logb Z ((∏ t,N t^(e t):ℕ):ℝ)=
      ∑ t,(e t:ℝ)*Real.logb Z (N t:ℝ) := by
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (by
    intro t ht
    exact pow_ne_zero _ (by exact_mod_cast (hN t).ne'))]
  simp only [Real.logb_pow]

theorem netExponent_swap_zero (i j : ℕ) :
    netExponent j i=0 ↔ netExponent i j=0 := by unfold netExponent;omega
theorem netExponent_swap_five (i j : ℕ) :
    netExponent j i=5 ↔ netExponent i j=1 := by unfold netExponent;omega
theorem sourceExponent_reflect (i j : ℕ) :
    Record12518109Natural.FirstNumeratorValuation.sourceExponent false i j=
      Record12518109Natural.FirstNumeratorValuation.sourceExponent true j i := by
  have h1 := netExponent_lt_six i j
  have h2 := netExponent_lt_six j i
  have hs : (netExponent i j+netExponent j i)%6=0 := by unfold netExponent;omega
  have hp :
      (netExponent i j=0 ∧ netExponent j i=0) ∨
      (netExponent i j=1 ∧ netExponent j i=5) ∨
      (netExponent i j=2 ∧ netExponent j i=4) ∨
      (netExponent i j=3 ∧ netExponent j i=3) ∨
      (netExponent i j=4 ∧ netExponent j i=2) ∨
      (netExponent i j=5 ∧ netExponent j i=1) := by omega
  rcases hp with hp | hp | hp | hp | hp | hp <;>
    rcases hp with ⟨h,h'⟩ <;> norm_num [Record12518109Natural.FirstNumeratorValuation.sourceExponent,h,h']

end
end OAI.SevenEighths.Record12518109Natural.Valuation
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.cancelled_ideal_product
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.sourceExponent_reflect
