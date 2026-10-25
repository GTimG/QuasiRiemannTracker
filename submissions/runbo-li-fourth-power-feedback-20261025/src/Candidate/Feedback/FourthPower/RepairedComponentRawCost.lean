/- Copyright (c) 2026 Sil. Apache-2.0.
Exact component geometry BEFORE supplier mass. In particular these bounds
do not try to reverse a previously paid Nu^-1 inequality. The complete
frozen scalar, selected Cauchy cardinality and padded selected scale remain.

-/
import Candidate.Feedback.FourthPower.RepairedRawExceptional
import Candidate.Feedback.FourthPower.RepairedRemainderGeometry

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedComponentRawCost
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalCentered
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedOriginalNormCap
open MixedFirstExceptionalNormalization
open OuterFreshSource OuterFreshSelected OuterFreshCutoffAllowance
open RepairedRawSupplier RepairedRawExceptional RepairedRemainderGeometry
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def supplierFront (q : Data ι) (x : Frozen q) : ℝ :=
  ‖MixedSupplierFourthRow.frozenWeight q x‖^2 * (256*((activeSelected q).card:ℝ))

theorem supplierFront_nonneg (q : Data ι) (x : Frozen q) : 0 ≤ supplierFront q x := by
  unfold supplierFront
  positivity

theorem padding_one_le (q : Data ι) : 1 ≤ MixedSelectedVolume.padding q := by
  exact one_le_pow₀ (by norm_num)

theorem raw_cost_exact (q : Data ι) (x : Frozen q) (seed : Id) :
    rawSupplierCost q x seed = supplierFront q x *
      (MixedSelectedVolume.scale q /
        (frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ))) := by
  unfold rawSupplierCost supplierFront
  ring

/-- The exact exceptional ratio to rawSupplierCost. Its only remaining
supplier factors are F/F^(4/3) and inverse padding, both at most one. -/
theorem exceptional_exact (s : Source ι a b) (ha : 0 < a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed : Id) (K : ℝ) (hK : 0 < K) :
    let q := supplierData s ha u L J
    let r := residualSource s ha cover u L J x
    supplierFront q x *
      (selectedVolume q*sourceVolume r*commonPhysicalCost r K /
        ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))) =
    (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1) *
      (frozenVolume q / (frozenVolume q)^(4/3:ℝ) / MixedSelectedVolume.padding q) *
      rawSupplierCost q x seed := by
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  change supplierFront q x *
    (selectedVolume q*sourceVolume r*commonPhysicalCost r K /
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))) =
    (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1) *
      (frozenVolume q/(frozenVolume q)^(4/3:ℝ)/MixedSelectedVolume.padding q)*rawSupplierCost q x seed
  have hP : ∀ i, 0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hF := frozenVolume_pos q hP
  have hW := selectedVolume_pos q hP
  have hpad := MixedSelectedVolume.padding_pos q
  have he : (selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K /
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)) =
      a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1/
        (frozenVolume q)^(4/3:ℝ) :=
    raw_selected_geometry s ha cover u L J x K hK
  have hWpow : (selectedVolume q)^(2/3:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hW _).ne'
  have hFpow : (frozenVolume q)^(4/3:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hF _).ne'
  calc
    _ = (supplierFront q x / (selectedVolume q*(seed.absNorm:ℝ))) *
        ((selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K /
          ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ))) := by
      field_simp [hW.ne',hWpow]
      <;> ring
    _ = (supplierFront q x / (selectedVolume q*(seed.absNorm:ℝ))) *
        ((a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1) /
          (frozenVolume q)^(4/3:ℝ)) := by rw [he]
    _ = _ := by
      rw [raw_cost_exact]
      change _ = _ * _ * (supplierFront q x *
        ((MixedSelectedVolume.padding q*selectedVolume q) /
          (frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ))))
      field_simp [hF.ne',hW.ne',hpad.ne',hFpow]
      <;> ring

theorem exceptional_le_raw_cost (s : Source ι a b) (ha : 0 < a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed : Id) (K : ℝ) (hK : 0 < K) :
    let q := supplierData s ha u L J
    let r := residualSource s ha cover u L J x
    supplierFront q x *
      (selectedVolume q*sourceVolume r*commonPhysicalCost r K /
        ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))) ≤
    (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1) *
      rawSupplierCost q x seed := by
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  change supplierFront q x *
    (selectedVolume q*sourceVolume r*commonPhysicalCost r K /
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))) ≤
    (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
      rawSupplierCost q x seed
  have hP : ∀ i, 0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hF : 1 ≤ frozenVolume q := Finset.one_le_prod₀ (fun i _ => s.hP i.val)
  have hpow : frozenVolume q ≤ (frozenVolume q)^(4/3:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hF (by norm_num : (1:ℝ) ≤ 4/3)
  have hF0 := frozenVolume_pos q hP
  have hratio : frozenVolume q / (frozenVolume q)^(4/3:ℝ) / MixedSelectedVolume.padding q ≤ 1 := by
    apply (div_le_one (MixedSelectedVolume.padding_pos q)).mpr
    exact ((div_le_one (Real.rpow_pos_of_pos hF0 _)).mpr hpow).trans (padding_one_le q)
  have hshape : 0 ≤ a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1 := by
    have hv := sourceVolume_pos s
    have hp := pairNorm_pos s.hd.1 s.hd.2
    have hh := prefixNormMax_pos s.d s.hd
    have hl := s.hL
    unfold shape
    positivity
  have he : supplierFront q x *
      (selectedVolume q*sourceVolume r*commonPhysicalCost r K /
        ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))) =
      (a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
        (frozenVolume q/(frozenVolume q)^(4/3:ℝ)/MixedSelectedVolume.padding q)*rawSupplierCost q x seed :=
    exceptional_exact s ha cover u L J x seed K hK
  rw [he]
  calc
    _ ≤ (_*1)*rawSupplierCost q x seed :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hshape)
        (rawSupplierCost_nonneg q hP x seed)
    _ = _ := by ring

/-- Sharp support Y=b²*2^#rest*Vr/p is used before the raw cost is compared.
Only one selected-volume factor W survives in the zero term. -/
theorem zero_le_raw_cost (s : Source ι a b) (ha : 0 < a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed : Id) (K : ℝ) (hK : 0 ≤ K) :
    let q := supplierData s ha u L J
    let r := residualSource s ha cover u L J x
    supplierFront q x *
      (selectedVolume q*K*sourceNormCap r.P b r.T r.d/(seed.absNorm:ℝ)) ≤
      (b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*selectedVolume q*(sourceVolume s/pairNorm s.d))*
        rawSupplierCost q x seed := by
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  change supplierFront q x *
    (selectedVolume q*K*sourceNormCap r.P b r.T r.d/(seed.absNorm:ℝ)) ≤
      (b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*selectedVolume q*(sourceVolume s/pairNorm s.d))*
        rawSupplierCost q x seed
  have hP : ∀ i, 0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hF := frozenVolume_pos q hP
  have hW := selectedVolume_pos q hP
  have hpad := MixedSelectedVolume.padding_pos q
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hvol : sourceVolume r*frozenVolume q*selectedVolume q=sourceVolume s :=
    residual_volume_partition s ha cover u L J x
  have hY : sourceNormCap r.P b r.T r.d =
      b^2*(2:ℝ)^Fintype.card (RestIndex q)*(sourceVolume r/pairNorm s.d) := by
    exact sharp_support_factored r
  have he : supplierFront q x *
      (selectedVolume q*K*sourceNormCap r.P b r.T r.d/(seed.absNorm:ℝ)) =
      (b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*selectedVolume q*(sourceVolume s/pairNorm s.d)) *
        rawSupplierCost q x seed / MixedSelectedVolume.padding q := by
    rw [hY,raw_cost_exact]
    change _ = _ * (supplierFront q x *
      ((MixedSelectedVolume.padding q*selectedVolume q) /
        (frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ)))) / _
    rw [← hvol]
    field_simp [hF.ne',hW.ne',hpad.ne']
    <;> ring
  rw [he]
  have hbase : 0 ≤ (b^2*(2:ℝ)^Fintype.card (RestIndex q)*K*selectedVolume q*(sourceVolume s/pairNorm s.d))*
      rawSupplierCost q x seed := by
    have hv := sourceVolume_pos s
    have hc := rawSupplierCost_nonneg q hP x seed
    positivity
  exact div_le_self hbase (padding_one_le q)

/-- Tail loss is arbitrary. The extra finite raw-cost ratio F W² Nseed
must be paid from actual caps; it is not replaced by a hidden constant. -/
theorem tail_le_raw_cost (q : Data ι) (hP : ∀ i, 0 < q.P i)
    (x : Frozen q) (seed : Id) (hseed : seed ≠ 0) (Z B saving : ℝ) (hZ : 1 < Z)
    (hcap : frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ) ≤ Z^B) :
    supplierFront q x * selectedVolume q * Z^(-(saving+B)) ≤
      Z^(-saving)*rawSupplierCost q x seed := by
  have hW := selectedVolume_pos q hP
  have hF := frozenVolume_pos q hP
  have hpad := MixedSelectedVolume.padding_pos q
  have hz := zero_lt_one.trans hZ
  have hs0 : 0 < (seed.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hseed)
  have hden := mul_pos (mul_pos hF (sq_pos_of_pos hW)) hs0
  have he : supplierFront q x * selectedVolume q * Z^(-(saving+B)) ≤
      (Z^(-saving)*supplierFront q x*MixedSelectedVolume.scale q) /
        (frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ)) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ = (supplierFront q x*selectedVolume q) *
          (frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ))*Z^(-(saving+B)) := by ring
      _ ≤ (supplierFront q x*selectedVolume q)*Z^B*Z^(-(saving+B)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcap (mul_nonneg (supplierFront_nonneg q x) hW.le))
          (Real.rpow_nonneg hz.le (-(saving+B)))
      _ = (supplierFront q x*selectedVolume q)*Z^(-saving) := by
        rw [mul_assoc,← Real.rpow_add hz]
        congr 2
        ring
      _ ≤ _ := by
        change _ ≤ Z^(-saving)*supplierFront q x*(MixedSelectedVolume.padding q*selectedVolume q)
        have he := mul_le_mul_of_nonneg_left (padding_one_le q)
          (mul_nonneg (mul_nonneg (supplierFront_nonneg q x) hW.le) (Real.rpow_nonneg hz.le (-saving)))
        convert he using 1 <;> ring
  apply he.trans_eq
  rw [raw_cost_exact]
  ring

end
end Candidate.Feedback.FourthPower.RepairedComponentRawCost
