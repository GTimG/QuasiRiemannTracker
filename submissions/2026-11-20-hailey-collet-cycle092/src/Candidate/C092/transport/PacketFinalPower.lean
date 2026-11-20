/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Sum the original packet after each row subclass reaches the same final exponent.
The partition may depend on the error mask and both contour coordinates. -/
import Candidate.C092.transport.ExistentialPacketSource

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Weighted.FullWContour QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

def finalPower (a d source fee target : ℝ) : ℝ :=
  1/4 + (target - rowPrice (2*a-1) 0 0 d source - fee)/d

/-- The physical price compares actual count, moment and amplitude prices to
the same final power for the cell, including both integration fees. -/
theorem power_le_final_iff (a p R d source moment mass fee target : ℝ) (hd : 0 < d) :
    packetPower a p R d source moment mass ≤ finalPower a d source fee target ↔
    rowPrice (2*a-1) p R d source + d*(moment/4+mass)+fee ≤ target := by
  have h : (packetPower a p R d source moment mass - 1/4)*d =
      rowPrice (2*a-1) p R d source-rowPrice (2*a-1) 0 0 d source+d*(moment/4+mass) := by
    unfold packetPower rowPrice
    field_simp
    ring
  unfold finalPower
  rw [←sub_le_iff_le_add', le_div_iff₀ hd, h]
  constructor <;> intro hs <;> linarith only [hs]

/-- The integrand includes the complete complex error packet before the
absolute value. Each row is assigned to one bin separately for each mask. -/
def maskNorm (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (rows : Finset FreeRow) (η : Character) (Z : ℝ) (x z : ℂ) (Y : ℝ) : ℝ :=
  mainFront D J Z * ∑ u ∈ rows, ‖errorPacket D F J η u Z x z Y * mainProduct D F J u Z z‖

theorem packet_partition (D : BaselineData) (F : BaselineSourceData D)
    (rows : Finset FreeRow) (η : Character) (Z : ℝ) (x z : ℂ) (Y : ℝ)
    {ι : Type*} [DecidableEq ι] (bins : Finset (Fin D.N) → Finset ι)
    (label : Finset (Fin D.N) → FreeRow → ι)
    (hlabel : ∀ J ∈ Finset.univ.powerset, ∀ u ∈ rows, label J u ∈ bins J) :
    packetNorm D F rows η Z x z Y = ∑ J ∈ Finset.univ.powerset, ∑ b ∈ bins J,
      maskNorm D F J (rows.filter (fun u => label J u=b)) η Z x z Y := by
  unfold packetNorm maskNorm
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (hlabel J hJ)]

theorem packet_of_partition_prices (D : BaselineData) (F : BaselineSourceData D)
    (rows : Finset FreeRow) (η : Character) (Z : ℝ) (x z : ℂ) (Y : ℝ)
    {ι : Type*} [DecidableEq ι] (bins : Finset (Fin D.N) → Finset ι)
    (label : Finset (Fin D.N) → FreeRow → ι)
    (hlabel : ∀ J ∈ Finset.univ.powerset, ∀ u ∈ rows, label J u ∈ bins J)
    (a d source fee target A : ℝ) (hZ : 1 ≤ Z) (hd : 0 < d)
    (weight : Finset (Fin D.N) → ι → ℝ)
    (hweight : ∀ J ∈ Finset.univ.powerset, ∀ b ∈ bins J, 0 ≤ weight J b)
    (hcost : ∑ J ∈ Finset.univ.powerset, ∑ b ∈ bins J, weight J b ≤ A)
    (hbin : ∀ J ∈ Finset.univ.powerset, ∀ b ∈ bins J,
      (rows.filter (fun u => label J u=b)).Nonempty →
      ∃ p R moment mass : ℝ,
        rowPrice (2*a-1) p R d source + d*(moment/4+mass)+fee ≤ target ∧
        maskNorm D F J (rows.filter (fun u => label J u=b)) η Z x z Y ≤
          weight J b * (Z^d)^(packetPower a p R d source moment mass)) :
    packetNorm D F rows η Z x z Y ≤ A*(Z^d)^(finalPower a d source fee target) := by
  have hb := Real.one_le_rpow hZ hd.le
  rw [packet_partition D F rows η Z x z Y bins label hlabel]
  calc
    _ ≤ ∑ J ∈ Finset.univ.powerset, ∑ b ∈ bins J, weight J b * (Z^d)^(finalPower a d source fee target) := by
      apply Finset.sum_le_sum; intro J hJ; apply Finset.sum_le_sum; intro b hb'
      by_cases hne : (rows.filter (fun u => label J u=b)).Nonempty
      · obtain ⟨p,R,m,s,hprice,hs⟩ := hbin J hJ b hb' hne
        exact hs.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb
          ((power_le_final_iff a p R d source m s fee target hd).2 hprice)) (hweight J hJ b hb'))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp only [maskNorm,Finset.sum_empty,mul_zero]
        exact mul_nonneg (hweight J hJ b hb') (Real.rpow_nonneg (zero_le_one.trans hb) _)
    _ = (∑ J ∈ Finset.univ.powerset, ∑ b ∈ bins J, weight J b) * (Z^d)^(finalPower a d source fee target) := by
      simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg (zero_le_one.trans hb) _)

#print axioms packet_of_partition_prices
end QRH.Cycle092.SelectedNonfloor
