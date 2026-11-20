/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original strict small packet on precisely the paid lower-edge boxes. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceCount
import Candidate.C092.transport.MixedMiddleReturnReindex
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters]

def paidSmallBoxes (r : TopData.Row) (xi : ℝ) : Finset ℕ :=
  (Finset.range (paidBoxLast r xi+1)).filter (fun j=>(j:ℝ)*xi<originalVcut r)

lemma paidSmallBoxes_mem {r : TopData.Row} {xi : ℝ} {j : ℕ} (hj : j∈paidSmallBoxes r xi) :
    j∈Finset.range (paidBoxLast r xi+1) ∧ (j:ℝ)*xi<originalVcut r := Finset.mem_filter.mp hj

lemma paidSmallBoxes_card {r : TopData.Row} (hr : r∈TopData.rows) {xi : ℝ} (hxi : 0<xi) :
    (paidSmallBoxes r xi).card ≤ paidBoxUniformLast xi+1 := by
  have h := Finset.card_le_card (Finset.filter_subset (fun j : ℕ=>(j:ℝ)*xi<originalVcut r)
    (Finset.range (paidBoxLast r xi+1)))
  rw [Finset.card_range] at h
  exact h.trans (paidBox_uniform hr hxi)

lemma original_small_box_zero (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Y U xi : ℝ) (r : TopData.Row) (j : ℕ) (hU : 1<U) (hxi : 0<xi)
    (hj : originalVcut r ≤ (j:ℝ)*xi) :
    originalSmallBoxPacket D F J η u Z x z data Y U xi (originalVcut r) (paidBoxLast r xi) j=0 := by
  unfold originalSmallBoxPacket
  apply mul_eq_zero_of_right
  trans ∑' _ : LabelPacketIndex F.S u (fun k : J=>sourcePrimePool F Z k.val),(0:ℂ)
  · apply tsum_congr
    intro e
    have hno : ¬((labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)≤2*Y ∧
        max 1 (data.combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u)*
          (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ))<U^(originalVcut r) ∧
        dilationBox U xi (paidBoxLast r xi) (max 1 (data.combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u)*
          (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)))=j) := by
      intro he
      exact small_box_zero_after_cutoff hU hxi.le (paidBox_cover r hxi) hj (le_max_left _ _) he.2.2 he.2.1
    rw [if_neg hno,mul_zero]
  · exact tsum_zero

theorem small_packet_paid_boxes (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Y U xi : ℝ) (r : TopData.Row) (hU : 1<U) (hxi : 0<xi) (hY : 0<Y)
    (hrow : (rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+4*D.e≤x.re+1/2) :
    smallLabelPolynomialPacket F.S F.exclusions η u
      (fun k : J=>sourcePrimePool F Z k.val) (fun k=>source_prime_pool_outside F Z k.val)
      (fun _=>F.W) (fun k=>Z^(D.length k.val)) x z F.W Y data.combinedConductor
      (fixedConductorConstant F.S) U (originalVcut r)=
    ∑j∈paidSmallBoxes r xi,originalSmallBoxPacket D F J η u Z x z data Y U xi
      (originalVcut r) (paidBoxLast r xi) j := by
  rw [small_packet_boxes D F J η u Z x z data Y U xi (originalVcut r) (paidBoxLast r xi) hY hrow hx hz hmargin]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  have hh : originalVcut r ≤ (j:ℝ)*xi := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hj,lt_of_not_ge hn⟩)
  exact original_small_box_zero D F J η u Z x z data Y U xi r j hU hxi hh

#print axioms small_packet_paid_boxes
#print axioms paidSmallBoxes_card
end
end QRH.Cycle092.MixedMiddleReturn
