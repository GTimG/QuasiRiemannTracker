/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalPairPackets
import Submissions.arvi_selected_leaf.JointDetector.NaturalTupleFibres
import Submissions.arvi_selected_leaf.JointDetector.NaturalTuplePartition
import Submissions.arvi_selected_leaf.JointDetector.NaturalActualTail

/-! Exact whole-cell reindexing of the actual offdiagonal Gram. Table labels
and the original diagonal selector remain visible before packet estimates. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open IdealMobiusDivisorSum
open NaturalSharedTables NaturalPairPackets
local notation "O" => ActualEisensteinCubic.O

def tupleCoefficientExtension (F : Finset ColourTuple) (a : F → ℂ) (c : ColourTuple) : ℂ :=
  if hc : c ∈ F then a ⟨c,hc⟩ else 0

@[simp] theorem tupleCoefficientExtension_apply (F : Finset ColourTuple)
    (a : F → ℂ) (c : F) : tupleCoefficientExtension F a c.val=a c := by
  simp only [tupleCoefficientExtension,dif_pos c.property]

theorem tupleCoefficientExtension_mass (F : Finset ColourTuple) (a : F → ℂ) :
    (∑ c ∈ F,‖tupleCoefficientExtension F a c‖^2)=∑ c : F,‖a c‖^2 := by
  rw [← Finset.sum_coe_sort F (fun c => ‖tupleCoefficientExtension F a c‖^2)]
  simp only [tupleCoefficientExtension_apply]

theorem tupleRow_same_ray (c d : ColourTuple)
    (h : ∀ j, primaryGenerator (c j)-primaryGenerator (d j) ∈
      (Ideal.span {(36:O)} : Ideal O)) :
    tupleRow c-tupleRow d ∈ (Ideal.span {(36:O)} : Ideal O) := by
  apply Ideal.Quotient.eq.mp
  simp only [tupleRow,map_prod,map_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Ideal.Quotient.eq.mpr (h j)]

def actualTablePool (F : Finset ColourTuple) : Finset SharedTable :=
  (F.product F).image fun p => table p.1 p.2

theorem pair_sum_by_table {M : Type*} [AddCommMonoid M]
    (F : Finset ColourTuple) (f : ColourTuple × ColourTuple → M) :
    (∑ p ∈ F.product F, f p)=∑ g ∈ actualTablePool F, ∑ p ∈ pairFibre F g, f p := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) f).symm

theorem tupleOffDiagonalGram_eq_rawPackets (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hray : ∀ c ∈ F, ∀ d ∈ F, ∀ j,
      primaryGenerator (c j)-primaryGenerator (d j) ∈ (Ideal.span {(36:O)} : Ideal O))
    (a : ColourTuple → ℂ) (L : ℝ) (hL : 0 < L) :
    tupleOffDiagonalGram F (fun c => a c.val) L = (6:ℂ)⁻¹*
      ∑ p ∈ F.product F, if p.1=p.2 then 0 else
        a p.1*star (a p.2)*rawDualPacket F hF p.1 p.2 QuadraticInitialBound.sieveCutoff L := by
  let f : ColourTuple × ColourTuple → ℂ := fun p => if p.1=p.2 then 0 else
    a p.1*star (a p.2)*rawDualPacket F hF p.1 p.2 QuadraticInitialBound.sieveCutoff L
  apply Eq.trans (b := (6:ℂ)⁻¹*(∑ c ∈ F, ∑ d ∈ F, f (c,d))) ?_
    (congrArg (fun x : ℂ => (6:ℂ)⁻¹*x) (Finset.sum_product F F f).symm)
  unfold tupleOffDiagonalGram
  dsimp only [f]
  simp only [Finset.mul_sum,Subtype.ext_iff]
  rw [Finset.sum_coe_sort F (fun c => ∑ d : F, if c=d.val then 0 else
    a c*star (a d.val)*selectedSupportedPairSource (weightedIdeal c)
      (weightedIdeal d.val) QuadraticInitialBound.sieveCutoff L)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_coe_sort F (fun d => if c=d then 0 else
    a c*star (a d)*selectedSupportedPairSource (weightedIdeal c)
      (weightedIdeal d) QuadraticInitialBound.sieveCutoff L)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases he : c=d
  · simp only [he,ite_true,mul_zero]
  · simp only [he,ite_false]
    have hm : primaryGenerator (weightedIdeal c)-primaryGenerator (weightedIdeal d) ∈
        (Ideal.span {(36:O)} : Ideal O) := by
      rw [← tupleRow_eq_primary,← tupleRow_eq_primary]
      exact tupleRow_same_ray c d (hray c hc d hd)
    rw [supported_pair_packet_eq F hF c d hc hd (hpF c hc) (hpF d hd) hm _ L hL]
    ring

/-- Exact shared-table and residual-coordinate sum, with the original
nonprincipal selector still present. It is never discarded by monotonicity. -/
theorem tupleOffDiagonalGram_eq_residualPackets (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hray : ∀ c ∈ F, ∀ d ∈ F, ∀ j,
      primaryGenerator (c j)-primaryGenerator (d j) ∈ (Ideal.span {(36:O)} : Ideal O))
    (a : ColourTuple → ℂ) (L : ℝ) (hL : 0 < L) :
    tupleOffDiagonalGram F (fun c => a c.val) L = (6:ℂ)⁻¹*
      ∑ g ∈ actualTablePool F, ∑ r ∈ residualFibre F g,
        if recoverLeft g r.1=recoverRight g r.2 then 0 else
          a (recoverLeft g r.1)*star (a (recoverRight g r.2))*
            rawDualPacket F hF (recoverLeft g r.1) (recoverRight g r.2)
              QuadraticInitialBound.sieveCutoff L := by
  rw [tupleOffDiagonalGram_eq_rawPackets F hF hpF hray a L hL,pair_sum_by_table]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact (sum_reindex F g hpF _).symm

def offDiagonalKeep (F : Finset ColourTuple) (c d : F) : ℂ := if c=d then 0 else 1

theorem offDiagonalKeep_norm (F : Finset ColourTuple) (c d : F) :
    ‖offDiagonalKeep F c d‖ ≤ 1 := by
  unfold offDiagonalKeep
  split_ifs <;> norm_num

def tupleNearOffDiagonalGram (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (a : F → ℂ) (L H : ℝ) : ℂ :=
  ∑ c : F, ∑ d : F, (a c*star (a d))*offDiagonalKeep F c d*
    NaturalActualTail.nearPacket F hF c.val d.val QuadraticInitialBound.sieveCutoff L H

/-- The finite near form and the proved Schwartz tail together recover the
literal original offdiagonal, with every puncture and the zero frequency.
The selector is applied before either finite or infinite summation. -/
theorem tupleOffDiagonalGram_eq_near_far (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hray : ∀ c ∈ F, ∀ d ∈ F, ∀ j,
      primaryGenerator (c j)-primaryGenerator (d j) ∈ (Ideal.span {(36:O)} : Ideal O))
    (a : F → ℂ) (L H : ℝ) (hL : 0 < L) (hH : 0 ≤ H) :
    tupleOffDiagonalGram F a L=(6:ℂ)⁻¹*(tupleNearOffDiagonalGram F hF a L H+
      NaturalActualTail.actualFarTail F hF QuadraticInitialBound.sieveCutoff L H
        (offDiagonalKeep F) a) := by
  unfold tupleNearOffDiagonalGram
  rw [← NaturalActualTail.weighted_packet_split F hF hpF
    QuadraticInitialBound.sieveCutoff L H hL hH (offDiagonalKeep F) a]
  unfold tupleOffDiagonalGram
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  by_cases he : c=d
  · simp only [he,ite_true,offDiagonalKeep,mul_zero,zero_mul]
  · simp only [he,ite_false,offDiagonalKeep,mul_one]
    have hm : primaryGenerator (weightedIdeal c.val)-primaryGenerator (weightedIdeal d.val) ∈
        (Ideal.span {(36:O)} : Ideal O) := by
      rw [← tupleRow_eq_primary,← tupleRow_eq_primary]
      exact tupleRow_same_ray c.val d.val (hray c.val c.property d.val d.property)
    rw [supported_pair_packet_eq F hF c.val d.val c.property d.property
      (hpF c.val c.property) (hpF d.val d.property) hm _ L hL]
    ring

theorem tupleOffDiagonalGram_norm_le_near_far (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hray : ∀ c ∈ F, ∀ d ∈ F, ∀ j,
      primaryGenerator (c j)-primaryGenerator (d j) ∈ (Ideal.span {(36:O)} : Ideal O))
    (a : F → ℂ) (L H : ℝ) (hL : 0 < L) (hH : 0 ≤ H) :
    ‖tupleOffDiagonalGram F a L‖ ≤ ‖tupleNearOffDiagonalGram F hF a L H‖+
      ‖NaturalActualTail.actualFarTail F hF QuadraticInitialBound.sieveCutoff L H
        (offDiagonalKeep F) a‖ := by
  rw [tupleOffDiagonalGram_eq_near_far F hF hpF hray a L H hL hH,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(6:ℂ)⁻¹‖ ≤ 1)).trans
  exact norm_add_le _ _

/-- Outer packet Cauchy uses summed original-row incidences, not the number
of all possible shared tables. Left and right vectors remain independent. -/
theorem packet_sum_norm_le {ι : Type*} (S : Finset ι) (packet : ι → ℂ)
    (leftMass rightMass : ι → ℝ) (C DL DR : ℝ)
    (hC : 0 ≤ C) (hDL : 0 ≤ DL) (hDR : 0 ≤ DR)
    (hleft : ∀ i, 0 ≤ leftMass i) (hright : ∀ i, 0 ≤ rightMass i)
    (hpacket : ∀ i ∈ S, ‖packet i‖ ≤ C*Real.sqrt (leftMass i)*Real.sqrt (rightMass i))
    (hL : ∑ i ∈ S, leftMass i ≤ DL) (hR : ∑ i ∈ S, rightMass i ≤ DR) :
    ‖∑ i ∈ S, packet i‖ ≤ C*Real.sqrt DL*Real.sqrt DR := by
  calc
    _ ≤ ∑ i ∈ S, ‖packet i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, C*Real.sqrt (leftMass i)*Real.sqrt (rightMass i) := Finset.sum_le_sum hpacket
    _ = C*(∑ i ∈ S, Real.sqrt (leftMass i)*Real.sqrt (rightMass i)) := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ ≤ C*(Real.sqrt (∑ i ∈ S, leftMass i)*Real.sqrt (∑ i ∈ S, rightMass i)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le S hleft hright) hC
    _ ≤ C*(Real.sqrt DL*Real.sqrt DR) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hL) (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC
    _ = _ := by ring

open NaturalTupleIdentity

def incidentArrayMass (left : Bool) (F : Finset ColourTuple) (g : SharedTable)
    (bad : Finset (Ideal O)) (a : ColourTuple → ℂ)
    (mask : SharedTable → ColourTuple → Ideal O → Ideal O → Ideal O → ℂ) : ℝ :=
  ∑ b ∈ arrayFamily left F g, ∑ e ∈ idealDivisors (diagonalProduct g),
    ∑ m ∈ idealDivisors ((arrayRecover left g b) 0), ∑ d ∈ bad,
      ‖a (arrayRecover left g b)*mask g b e m d‖^2

theorem incidentArrayMass_nonneg (left : Bool) (F : Finset ColourTuple) (g : SharedTable)
    (bad : Finset (Ideal O)) (a : ColourTuple → ℂ)
    (mask : SharedTable → ColourTuple → Ideal O → Ideal O → Ideal O → ℂ) :
    0 ≤ incidentArrayMass left F g bad a mask := by
  unfold incidentArrayMass
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Outer Cauchy consumes the actual table/puncture/divisor arrays and
charges each original row only its own incidences. In particular the
cardinality of the full shared-table pool never appears. -/
theorem packet_sum_actual_incidence (ε : ℝ) (hε : 0 < ε) (bad : Finset (Ideal O)) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (G : Finset SharedTable) (Y K : ℝ) (a : ColourTuple → ℂ)
        (maskL maskR : SharedTable → ColourTuple → Ideal O → Ideal O → Ideal O → ℂ)
        (packet : SharedTable → ℂ),
      1 ≤ Y → 0 ≤ K → (∀ c ∈ F,(Ideal.absNorm (weightedIdeal c):ℝ) ≤ Y) →
      (∀ g ∈ G,∀ b ∈ arrayFamily true F g,∀ e ∈ idealDivisors (diagonalProduct g),
        ∀ m ∈ idealDivisors ((arrayRecover true g b) 0),∀ d ∈ bad,‖maskL g b e m d‖ ≤ 1) →
      (∀ g ∈ G,∀ b ∈ arrayFamily false F g,∀ e ∈ idealDivisors (diagonalProduct g),
        ∀ m ∈ idealDivisors ((arrayRecover false g b) 0),∀ d ∈ bad,‖maskR g b e m d‖ ≤ 1) →
      (∀ g ∈ G,‖packet g‖ ≤ K*Real.sqrt (incidentArrayMass true F g bad a maskL)*
        Real.sqrt (incidentArrayMass false F g bad a maskR)) →
      ‖∑ g ∈ G,packet g‖ ≤ K*C*Y^ε*(∑ c ∈ F,‖a c‖^2) := by
  obtain ⟨CL,hCL,hleft⟩ := masked_array_mass true ε hε bad
  obtain ⟨CR,hCR,hright⟩ := masked_array_mass false ε hε bad
  let C := CL+CR
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro F hF hpF G Y K a maskL maskR packet hY hK hheight hmL hmR hp
  let D := C*Y^ε*(∑ c ∈ F,‖a c‖^2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : ∑ g ∈ G,incidentArrayMass true F g bad a maskL ≤ D := by
    apply (hleft F hF hpF G Y a maskL hY hheight hmL).trans
    change CL*Y^ε*(∑ c ∈ F,‖a c‖^2) ≤ C*Y^ε*(∑ c ∈ F,‖a c‖^2)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : CL ≤ C) (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hR : ∑ g ∈ G,incidentArrayMass false F g bad a maskR ≤ D := by
    apply (hright F hF hpF G Y a maskR hY hheight hmR).trans
    change CR*Y^ε*(∑ c ∈ F,‖a c‖^2) ≤ C*Y^ε*(∑ c ∈ F,‖a c‖^2)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : CR ≤ C) (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hh := packet_sum_norm_le G packet (fun g => incidentArrayMass true F g bad a maskL)
    (fun g => incidentArrayMass false F g bad a maskR) K D D hK hD hD
    (fun g => incidentArrayMass_nonneg true F g bad a maskL)
    (fun g => incidentArrayMass_nonneg false F g bad a maskR) hp hL hR
  apply hh.trans_eq
  calc
    _ = K*(Real.sqrt D*Real.sqrt D) := by ring
    _ = K*D := by rw [Real.mul_self_sqrt hD]
    _ = _ := by dsimp [D]; ring

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleOffDiagonalGram_eq_residualPackets
#print axioms Qrh.JointDetector.NaturalSelectedNorm.packet_sum_norm_le
#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleOffDiagonalGram_eq_near_far
#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleOffDiagonalGram_norm_le_near_far
#print axioms Qrh.JointDetector.NaturalSelectedNorm.packet_sum_actual_incidence
