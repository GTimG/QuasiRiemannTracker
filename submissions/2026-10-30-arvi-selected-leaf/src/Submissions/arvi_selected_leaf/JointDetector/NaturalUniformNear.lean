/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalCellSectorNorm

/-! Uniform assembly of the actual finite natural near estimate. The mesh
is fixed before the finite slot dictionary. Shared-table incidences, source
sectors and ordinary-ideal dyads are paid by explicit small powers. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss
open NaturalSharedTables NaturalPairPackets NaturalTupleIdentity
local notation "O" => ActualEisensteinCubic.O

/-- Every actual finite near packet is now paid. No operator, packet,
packed-source or count estimate appears as a hypothesis. -/
theorem uniform_natural_near_norm : UniformNaturalNearNorm := by
  intro A P gap loss hA hP hgap hgh hloss
  let e : ℝ := loss/(4*(A+1))
  have he : 0 < e := by dsimp [e]; positivity
  have hP0 : 0 ≤ P := by linarith
  have hebudget : (3*A+2)*e ≤ loss := by
    have heq : e*(4*(A+1))=loss := div_mul_cancel₀ loss (by positivity)
    nlinarith [mul_pos he (show 0 < A+2 by linarith)]
  obtain ⟨mesh₀,hmesh,hsector⟩ := cell_sector_norm A P gap e hA hP hgap hgh he
  obtain ⟨Ci,hCi,hnear⟩ := near_norm_of_table_sector_bound e he
  obtain ⟨Cq,hCq,hsectors⟩ := NaturalFrequencyReindex.sector_dyad_budget P e hP0 he
  refine ⟨mesh₀,hmesh,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Cs,Zs,hCs,hsector⟩ := hsector N Cslot wmin hCslot hwmin
  refine ⟨2*Cs*Ci*Cq,max 1 Zs,by positivity,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F Y L hb hs hslope hw hF hpF hY hYA hheight hYL hLP k a
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hz0 : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hy0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hL : 0 < L := hy0.trans_le hYL
  have hcut : 0 < Z^P := Real.rpow_pos_of_pos hz0 P
  have hmass : 0 ≤ ∑ c : TuplePartition.cell F Y k,‖a c‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  let Fc := TuplePartition.cell F Y k
  have hf : ∀ c ∈ Fc,∀ j,Admissible (c j) :=
    fun c hc => hF c (Finset.mem_filter.mp hc).1
  have hp : ∀ c ∈ Fc,Pairwise (fun j l => IsCoprime (c j) (c l)) :=
    fun c hc => hpF c (Finset.mem_filter.mp hc).1
  have hh : ∀ c ∈ Fc,(Ideal.absNorm (weightedIdeal c):ℝ) ≤ Y := by
    intro c hc
    exact NaturalActualTail.weighted_norm_le c (hf c hc) Y
      (hheight c (Finset.mem_filter.mp hc).1)
  let K : ℝ := 2*(Cs*Z^e*Y^(2*e)*L)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpacket : ∀ g ∈ actualTablePool Fc,∀ E ∈ (tableSourceMask Fc g).powerset,
      ∀ sector ∈ BadFrequencySectors.boundedKeys (Z^P),∀ j : Fin (columnDyadicLength (Z^P)+1),
      ‖tableSectorPacket Fc hf (tupleCoefficientExtension Fc a) L (Z^P) g E sector j‖ ≤
        K*Real.sqrt (tableArrayEnergy true Fc g (tupleCoefficientExtension Fc a))*
          Real.sqrt (tableArrayEnergy false Fc g (tupleCoefficientExtension Fc a)) := by
    intro g hg E hE sector hsect j
    have hgn := (actualTablePool_valid Fc hf hp g hg).1
    exact tableSectorPacket_norm_of_bilinear Fc hf hp g hgn (tupleCoefficientExtension Fc a)
      L (Z^P) (Cs*Z^e*Y^(2*e)*L) (by positivity) E sector j
      (fun α β => hsector Z mesh δ ((le_max_right _ _).trans hZ) hm0 hmm hδlo hδhi
        d F Y L hb hs hslope hw hF hpF hY hYA hheight hYL hLP k g hg E hE sector hsect j α β)
  have hn := hnear Fc hf hp a L (Z^P) Y K hcut.le hY hK hh hpacket
  have hq := hsectors Z (Z^P) hz1 hcut le_rfl
  have hq' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq (mul_nonneg hK hCi.le))
      (Real.rpow_nonneg hy0.le e)) hmass
  have hzprod : Z^e*Z^e=Z^(2*e) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have hyprod : Y^(2*e)*Y^e=Y^(3*e) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  have hbudget : Z^(2*e)*Y^(3*e) ≤ Z^loss := by
    calc
      _ ≤ Z^(2*e)*(Z^A)^(3*e) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hy0.le hYA (by positivity)) (Real.rpow_nonneg hz0.le _)
      _ = Z^((3*A+2)*e) := by
        rw [← Real.rpow_mul hz0.le A (3*e),← Real.rpow_add hz0]
        congr 1
        ring
      _ ≤ Z^loss := Real.rpow_le_rpow_of_exponent_le hz1 hebudget
  apply hn.trans
  apply hq'.trans
  calc
    _ = (2*Cs*Ci*Cq)*(Z^e*Z^e)*(Y^(2*e)*Y^e)*L*(∑ c,‖a c‖^2) := by dsimp [K]; ring
    _ = (2*Cs*Ci*Cq)*(Z^(2*e)*Y^(3*e))*L*(∑ c,‖a c‖^2) := by rw [hzprod,hyprod]; ring
    _ ≤ (2*Cs*Ci*Cq)*Z^loss*L*(∑ c,‖a c‖^2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbudget (by positivity)) hL.le) hmass

/-- Full natural selected-cell norm, including bad/unit row extraction,
all ordinary sources, principal terms, tails and actual amplification. -/
theorem natural_selected_cell_norm : NaturalSelectedCellNorm :=
  natural_selected_norm_of_near uniform_natural_near_norm

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.uniform_natural_near_norm
#print axioms Qrh.JointDetector.NaturalSelectedNorm.natural_selected_cell_norm
