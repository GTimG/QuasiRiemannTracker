/- Copyright (c) 2026 Sil. Apache-2.0.
Actual empty-selected raw shapes paid DIRECTLY by shared rawSupplierCost.

-/
import Candidate.FourthPower.RepairedSmallFourShapes
import Candidate.FourthPower.RepairedSmallMass
import Candidate.FourthPower.RepairedSmallSideAlgebra
import Candidate.FourthPower.RepairedComponentRawCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallShapeRawCost
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedInnerExceptionalLedger MixedPrincipalCentered MixedFirstExceptionalNormalization
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive
open OuterFreshSource OuterFreshSelected OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedRawSupplier RepairedRawExceptional RepairedComponentRawCost
open RepairedSmallFourShapes RepairedSmallMass RepairedSmallSideAlgebra
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem native_shape_raw_cost (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (hJ : J=∅)
    (x : Frozen (supplierData s ha u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0)
    (N : ℕ) (hN : Fintype.card ι≤N) (seed : Id) (hseed : seed≠0)
    (τ σ : Character) (Cf Z exponent : ℝ) (hCf : 0≤Cf) (hZ : 0≤Z)
    (hmod : (σ.modulus.absNorm:ℝ)≤Cf*(τ.modulus.absNorm:ℝ)*
      ((frozenProduct (supplierData s ha u L J) x).absNorm:ℝ)) :
    let q:=supplierData s ha u L J;
    let r:=residualSource s ha cover u L J x;
    supplierFront q x*nativeShape r σ seed Z exponent≤
      (Cf*(2:ℝ)^N*(τ.modulus.absNorm:ℝ)*(sourceVolume s/pairNorm s.d)^2*Z^exponent)*
        rawSupplierCost q x seed := by
  intro q r
  have hP : ∀i,0<q.P i := fun i=>zero_lt_one.trans_le (s.hP i)
  have hF:=frozenVolume_pos q hP
  have hp:=pairNorm_pos s.hd.1 s.hd.2
  have hs:=zero_lt_one.trans_le (ideal_norm_one_le hseed)
  have hdim : Fintype.card ↥Lᶜ≤N :=
    (Fintype.card_le_of_injective (fun i : ↥Lᶜ=>i.val) Subtype.val_injective).trans hN
  have hf : ((frozenProduct q x).absNorm:ℝ)≤(2:ℝ)^N*frozenVolume q :=
    (actual_frozen_window s ha u L J x hx).2.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hdim) hF.le)
  have hv : sourceVolume r*frozenVolume q*selectedVolume q=sourceVolume s :=
    residual_volume_partition s ha cover u L J x
  rw [empty_selected_volume q hJ,mul_one] at hv
  have hmodq : (σ.modulus.absNorm:ℝ)≤Cf*(τ.modulus.absNorm:ℝ)*
      ((frozenProduct q x).absNorm:ℝ) := hmod
  have hn:=native_cost_to_frozen_budget
    (σ.modulus.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Cf ((frozenProduct q x).absNorm:ℝ)
    (frozenVolume q) (sourceVolume r) (sourceVolume s) (pairNorm s.d) (seed.absNorm:ℝ) ((2:ℝ)^N)
    (Nat.cast_nonneg τ.modulus.absNorm) hCf hF hp hs hmodq hf hv
  have he:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hZ exponent)) (supplierFront_nonneg q x)
  rw [raw_cost_exact,empty_selected_scale q hJ,empty_selected_volume q hJ]
  simp only [one_pow,mul_one]
  change supplierFront q x*((σ.modulus.absNorm:ℝ)*(sourceVolume r/pairNorm s.d)^2*
    Z^exponent/(seed.absNorm:ℝ))≤_
  calc
    _=supplierFront q x*(((σ.modulus.absNorm:ℝ)*(sourceVolume r/pairNorm s.d)^2/
        (seed.absNorm:ℝ))*Z^exponent) := by ring
    _≤supplierFront q x*((Cf*(2:ℝ)^N*(τ.modulus.absNorm:ℝ)*(sourceVolume s/pairNorm s.d)^2/
        (frozenVolume q*(seed.absNorm:ℝ)))*Z^exponent) := he
    _=_ := by ring

theorem exceptional_shape_raw_cost (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (hJ : J=∅)
    (x : Frozen (supplierData s ha u L J)) (seed : Id)
    (K Z exponent : ℝ) (hK : 0<K) (hZ : 0≤Z) :
    let q:=supplierData s ha u L J;
    let r:=residualSource s ha cover u L J x;
    supplierFront q x*exceptionalShape r seed K Z exponent≤
      (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1*Z^exponent)*
        rawSupplierCost q x seed := by
  intro q r
  have he : supplierFront q x*
      (selectedVolume q*sourceVolume r*commonPhysicalCost r K/
        ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ)))≤
      (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
        rawSupplierCost q x seed :=
    exceptional_le_raw_cost s ha cover u L J x seed K hK
  rw [empty_selected_volume q hJ] at he
  simp only [one_mul,Real.one_rpow,mul_one] at he
  have hh:=mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hZ exponent)
  change supplierFront q x*(sourceVolume r*commonPhysicalCost r K*Z^exponent/
    ((pairNorm r.d)^2*(seed.absNorm:ℝ)))≤_
  calc
    _=(supplierFront q x*(sourceVolume r*commonPhysicalCost r K/
        ((pairNorm r.d)^2*(seed.absNorm:ℝ))))*Z^exponent := by ring
    _≤((a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
        rawSupplierCost q x seed)*Z^exponent := hh
    _=_ := by ring

theorem zero_shape_raw_cost (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (hJ : J=∅)
    (x : Frozen (supplierData s ha u L J)) (seed : Id)
    (N : ℕ) (hN : Fintype.card ι≤N)
    (K Z exponent : ℝ) (hK : 0≤K) (hZ : 0≤Z) :
    let q:=supplierData s ha u L J;
    let r:=residualSource s ha cover u L J x;
    supplierFront q x*zeroShape r seed K Z exponent≤
      (b^2*(2:ℝ)^N*K*(sourceVolume s/pairNorm s.d)*Z^exponent)*rawSupplierCost q x seed := by
  intro q r
  have he : supplierFront q x*
      (selectedVolume q*K*MixedOriginalNormCap.sourceNormCap r.P b r.T r.d/(seed.absNorm:ℝ))≤
      (b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*selectedVolume q*(sourceVolume s/pairNorm s.d))*
        rawSupplierCost q x seed :=
    zero_le_raw_cost s ha cover u L J x seed K hK
  rw [empty_selected_volume q hJ] at he
  simp only [one_mul,mul_one] at he
  have hh:=mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hZ exponent)
  have hp:=pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) ((rest_card_le q).trans hN)
  have hrest : 0≤b^2*K*(sourceVolume s/pairNorm s.d)*rawSupplierCost q x seed*Z^exponent := by
    have hv:=(sourceVolume_pos s).le
    have hd:=(pairNorm_pos s.hd.1 s.hd.2).le
    have hc:=rawSupplierCost_nonneg q (fun i=>zero_lt_one.trans_le (s.hP i)) x seed
    have hz:=Real.rpow_nonneg hZ exponent
    positivity
  have hlast:=mul_le_mul_of_nonneg_right hp hrest
  change supplierFront q x*(K*MixedOriginalNormCap.sourceNormCap r.P b r.T r.d*
    Z^exponent/(seed.absNorm:ℝ))≤_
  calc
    _=(supplierFront q x*(K*MixedOriginalNormCap.sourceNormCap r.P b r.T r.d/
        (seed.absNorm:ℝ)))*Z^exponent := by ring
    _≤((b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*(sourceVolume s/pairNorm s.d))*
        rawSupplierCost q x seed)*Z^exponent := hh
    _=(2:ℝ)^Fintype.card (RestIndex q)*
        (b^2*K*(sourceVolume s/pairNorm s.d)*rawSupplierCost q x seed*Z^exponent) := by ring
    _≤(2:ℝ)^N*(b^2*K*(sourceVolume s/pairNorm s.d)*rawSupplierCost q x seed*Z^exponent) := hlast
    _=_ := by ring

/-- Original-u payment is retained: the actual frozen lower edge gives
F*Nseed<=Nu, so this comparison needs no extra tail loss. -/
theorem tail_shape_raw_cost (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (hJ : J=∅)
    (x : Frozen (supplierData s ha u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0)
    (seed : Id) (hseed : seed≠0)
    (hu : u=frozenProduct (supplierData s ha u L J) x*seed)
    (Z saving : ℝ) (hZ : 0≤Z) :
    let q:=supplierData s ha u L J;
    supplierFront q x*tailShape u Z saving≤Z^(-saving)*rawSupplierCost q x seed := by
  intro q
  have hF:=frozenVolume_pos q (fun i=>zero_lt_one.trans_le (s.hP i))
  have hs:=zero_lt_one.trans_le (ideal_norm_one_le hseed)
  have hprod : (u.absNorm:ℝ)=((frozenProduct q x).absNorm:ℝ)*(seed.absNorm:ℝ) := by
    rw [hu]
    simp only [map_mul,Nat.cast_mul] <;> rfl
  have hden : frozenVolume q*(seed.absNorm:ℝ)≤(u.absNorm:ℝ) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (actual_frozen_window s ha u L J x hx).1 hs.le
  have hi:=div_le_div_of_nonneg_left (Real.rpow_nonneg hZ (-saving)) (mul_pos hF hs) hden
  have he:=mul_le_mul_of_nonneg_left hi (supplierFront_nonneg q x)
  rw [raw_cost_exact,empty_selected_scale q hJ,empty_selected_volume q hJ]
  simp only [one_pow,mul_one]
  change supplierFront q x*(Z^(-saving)/(u.absNorm:ℝ))≤_
  calc
    _≤supplierFront q x*(Z^(-saving)/(frozenVolume q*(seed.absNorm:ℝ))) := he
    _=_ := by ring


end
end Candidate.FourthPower.RepairedSmallShapeRawCost
