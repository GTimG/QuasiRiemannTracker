/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalNearNorm
import Submissions.arvi_selected_leaf.JointDetector.NaturalNormAssembly

/-! The remaining finite near estimate is isolated precisely. Once proved,
all Schwartz tails, positive diagonals, original ordinary-source sectors,
bad rows, cells and actual whole-row amplification are discharged here.
This file does not assert its near-estimate hypothesis. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def UniformNaturalNearNorm : Prop :=
  ∀ A P gap loss : ℝ,0 < A → 3*A+1 ≤ P → 0 < gap → gap < 1/2 → 0 < loss →
  ∃ mesh₀ : ℝ,0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),0 ≤ Cslot → 0 < wmin →
    ∃ C Z₀ : ℝ,0 < C ∧ ∀ (Z mesh δ : ℝ),Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2+gap ≤ δ → δ ≤ 3/4 →
    ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (Y L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i →
      ∀ hF : ∀ c ∈ F,∀ j,Admissible (c j),
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      Y ≤ L → L ≤ Z^P →
      ∀ (k : TuplePartition.Key Y) (a : TuplePartition.cell F Y k → ℂ),
        ‖tupleNearOffDiagonalGram (TuplePartition.cell F Y k)
          (fun c hc => hF c (Finset.mem_filter.mp hc).1) a L (Z^P)‖ ≤
          C*Z^loss*L*(∑ c,‖a c‖^2)

/-- Exact completion of the finite near inlet. The dual truncation is the
ORIGINAL `Z^P`: choosing eta=(P-2A)/2 in the proved tail theorem changes
only its Schwartz order and constants, not the auxiliary source exponent. -/
theorem natural_selected_norm_of_near (hnear : UniformNaturalNearNorm) :
    NaturalSelectedCellNorm := by
  apply natural_selected_norm_of_goodTuple_long
  intro A P gap loss hA hP hgap hgh hloss
  obtain ⟨Cc,hCc,hcell⟩ := goodTuple_long_of_cell_offDiagonal A P loss hA
    (by linarith) hloss
  obtain ⟨m,hm,hnear⟩ := hnear A P gap (loss/3) hA hP hgap hgh (by positivity)
  let η := (P-2*A)/2
  have hη : 0 < η := by dsimp [η]; linarith
  have hexp : 2*A+2*η=P := by dsimp [η]; ring
  obtain ⟨Ct,Zt,hCt,htail⟩ := NaturalActualTail.actual_far_packet_tail A P η 0 hA.le hη
    QuadraticInitialBound.sieveCutoff
  refine ⟨m,hm,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Cn,Zn,hCn,hnear⟩ := hnear N Cslot wmin hCslot hwmin
  refine ⟨Cc*(1+(Cn+Ct)),max 1 (max Zn Zt),by positivity,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hz0 : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hZn : Zn ≤ Z := (le_max_left Zn Zt).trans ((le_max_right _ _).trans hZ)
  have hZt : Zt ≤ Z := (le_max_right Zn Zt).trans ((le_max_right _ _).trans hZ)
  have hnear := hnear Z mesh δ hZn hm0 hmm hδlo hδhi
  apply hcell N Z mesh Cslot wmin δ (Cn+Ct) hz1 (by positivity)
  intro d F Y L hb hs hslope hw hF hpF hY hYA hheight hYL hLP k a
  have hL : 1 ≤ L := hY.trans hYL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hfcell : ∀ c ∈ TuplePartition.cell F Y k,∀ j,Admissible (c j) :=
    fun c hc => hF c (Finset.mem_filter.mp hc).1
  have hpcell : ∀ c ∈ TuplePartition.cell F Y k,
      Pairwise (fun j l => IsCoprime (c j) (c l)) :=
    fun c hc => hpF c (Finset.mem_filter.mp hc).1
  have hhcell : ∀ c ∈ TuplePartition.cell F Y k,
      ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y :=
    fun c hc => hheight c (Finset.mem_filter.mp hc).1
  have hnear' := hnear d F Y L hb hs hslope hw hF hpF hY hYA hheight hYL hLP k a
  have hfar := htail Z Y L hZt hY hYA hYL hLP (TuplePartition.cell F Y k) hfcell
    hpcell hhcell (offDiagonalKeep (TuplePartition.cell F Y k))
    (offDiagonalKeep_norm _) a
  rw [hexp,neg_zero,Real.rpow_zero,mul_one] at hfar
  have hpow : 1 ≤ Z^(loss/3) := Real.one_le_rpow hz1 (by positivity)
  have hscale : 1 ≤ Z^(loss/3)*L :=
    hpow.trans (le_mul_of_one_le_right (Real.rpow_nonneg hz0.le _) hL)
  have hmass : 0 ≤ ∑ c : TuplePartition.cell F Y k,‖a c‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfar' : ‖NaturalActualTail.actualFarTail (TuplePartition.cell F Y k) hfcell
      QuadraticInitialBound.sieveCutoff L (Z^P)
        (offDiagonalKeep (TuplePartition.cell F Y k)) a‖ ≤
      Ct*Z^(loss/3)*L*(∑ c,‖a c‖^2) := by
    apply hfar.trans
    have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hCt.le hmass)
    nlinarith
  apply (tupleOffDiagonalGram_norm_le_near_far (TuplePartition.cell F Y k) hfcell hpcell
    (fun c hc e he => TuplePartition.cell_same_ray F Y k c e hc he)
    a L (Z^P) hL0 (Real.rpow_nonneg hz0.le _)).trans
  calc
    _ ≤ Cn*Z^(loss/3)*L*(∑ c,‖a c‖^2)+Ct*Z^(loss/3)*L*(∑ c,‖a c‖^2) :=
      add_le_add hnear' hfar'
    _ = _ := by ring

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.natural_selected_norm_of_near
