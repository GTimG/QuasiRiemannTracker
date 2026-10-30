/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalOffDiagonalNorm

/-! Actual shared-table geometry and the finite natural norm consumer. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss CenteredExceptionalCount IdealMobiusDivisorSum
open NaturalSharedTables NaturalPairPackets NaturalTupleIdentity NaturalNearPackets
local notation "O" => ActualEisensteinCubic.O

theorem fixed_pivot_ray (F : Finset ColourTuple)
    (hray : ∀ a ∈ F,∀ b ∈ F,primaryGenerator (a 0)-primaryGenerator (b 0) ∈
      (Ideal.span {(36:O)} : Ideal O)) :
    ∃ r : EisensteinEPrimaryPhase.Coord,∀ a ∈ F,
      ActualEisensteinCoordinates.residue (primaryGenerator (a 0))=r := by
  by_cases hn : F.Nonempty
  · obtain ⟨b,hb⟩ := hn
    refine ⟨ActualEisensteinCoordinates.residue (primaryGenerator (b 0)),?_⟩
    intro a ha
    apply QuadraticGaussRay.residue_eq_of_four_dvd_sub
    have hfour : (4:O) ∣ (36:O) := ⟨9,by norm_num⟩
    exact hfour.trans (Ideal.mem_span_singleton.mp (hray a ha b hb))
  · refine ⟨ActualEisensteinCoordinates.residue 0,?_⟩
    intro a ha
    exact (hn ⟨a,ha⟩).elim

namespace TableGeometry

def U {Y : ℝ} (k : TuplePartition.Key Y) : ℝ := TuplePartition.colourScale k 0
def V {Y : ℝ} (k : TuplePartition.Key Y) : ℝ :=
  ∏ j : Fin 4,TuplePartition.colourScale k j.succ
def rho {Y : ℝ} (k : TuplePartition.Key Y) : ℝ := TuplePartition.radicalScale k/(U k*V k)
def D {Y : ℝ} (k : TuplePartition.Key Y) (g : SharedTable) : ℝ :=
  TuplePartition.radicalScale k/(Ideal.absNorm
    (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)

theorem U_pos {Y : ℝ} (k : TuplePartition.Key Y) : 0 < U k := TuplePartition.colourScale_pos k 0
theorem V_pos {Y : ℝ} (k : TuplePartition.Key Y) : 0 < V k :=
  Finset.prod_pos fun j _ => TuplePartition.colourScale_pos k j.succ

theorem table_norms_one_le (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0) :
    1 ≤ (Ideal.absNorm (TableBudget.G g):ℝ) ∧
    1 ≤ (Ideal.absNorm (TableBudget.H g):ℝ) ∧
    1 ≤ (Ideal.absNorm (TableBudget.J g):ℝ) ∧
    1 ≤ (Ideal.absNorm (TableBudget.E g):ℝ) ∧
    1 ≤ (Ideal.absNorm (TableBudget.F g):ℝ) := by
  have hn := TableBudget.full_ne_zero g hgn
  exact ⟨norm_one_le (by intro he; apply hn; simp only [he,zero_mul]),
    norm_one_le (by intro he; apply hn; simp only [he,mul_zero,zero_mul]),
    norm_one_le (by intro he; apply hn; simp only [he,mul_zero]),
    norm_one_le (by intro he; apply hn; simp only [he,mul_zero,zero_mul]),
    norm_one_le (by intro he; apply hn; simp only [he,mul_zero,zero_mul])⟩

theorem rowProduct_norm (g : SharedTable) :
    (Ideal.absNorm (rowProduct g 0):ℝ)=
      (Ideal.absNorm (TableBudget.G g):ℝ)*(Ideal.absNorm (TableBudget.E g):ℝ) := by
  rw [TableBudget.row_zero,map_mul,Nat.cast_mul]

theorem columnProduct_norm (g : SharedTable) :
    (Ideal.absNorm (columnProduct g 0):ℝ)=
      (Ideal.absNorm (TableBudget.G g):ℝ)*(Ideal.absNorm (TableBudget.F g):ℝ) := by
  rw [TableBudget.column_zero,map_mul,Nat.cast_mul]

theorem offDiagonal_norm (g : SharedTable) :
    (Ideal.absNorm (offDiagonalIdeal g):ℝ)=
      (Ideal.absNorm (TableBudget.E g):ℝ)*(Ideal.absNorm (TableBudget.F g):ℝ)*
        (Ideal.absNorm (TableBudget.J g):ℝ) := by
  rw [offDiagonalIdeal,TableBudget.offDiagonal_split]
  simp only [map_mul,Nat.cast_mul]

theorem diagonal_norm (g : SharedTable) :
    (Ideal.absNorm (diagonalProduct g):ℝ)=
      (Ideal.absNorm (TableBudget.G g):ℝ)*(Ideal.absNorm (TableBudget.H g):ℝ) := by
  rw [diagonalProduct,TableBudget.diagonal,map_mul,Nat.cast_mul]

theorem D_pos {Y : ℝ} (k : TuplePartition.Key Y) (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0) :
    0 < D k g := div_pos (TuplePartition.radicalScale_pos k) (norm_pos (TableBudget.full_ne_zero g hgn))

theorem D_normalized {Y : ℝ} (k : TuplePartition.Key Y) (g : SharedTable) :
    D k g=rho k*U k*V k/
      ((Ideal.absNorm (TableBudget.G g):ℝ)*(Ideal.absNorm (TableBudget.H g):ℝ)*
        (Ideal.absNorm (TableBudget.E g):ℝ)*(Ideal.absNorm (TableBudget.F g):ℝ)*
          (Ideal.absNorm (TableBudget.J g):ℝ)) := by
  have hu := U_pos k
  have hv := V_pos k
  dsimp [D,rho]
  simp only [map_mul,Nat.cast_mul]
  field_simp

theorem cell_ranges (F : Finset ColourTuple) (Y : ℝ) (k : TuplePartition.Key Y)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (c : ColourTuple) (hc : c ∈ TuplePartition.cell F Y k) :
    U k*(V k)^2 ≤ Y ∧ rho k ∈ Set.Icc (1/2:ℝ) 32 := by
  refine ⟨TuplePartition.cell_anchor_le_height F Y k hF hheight c hc,?_⟩
  have hh := cell_radicalScale_comparison F Y k hF hheight c hc
  have hprod : (∏ j : Fin 5,TuplePartition.colourScale k j)=U k*V k :=
    Fin.prod_univ_succ _
  rw [hprod] at hh
  have hUV := mul_pos (U_pos k) (V_pos k)
  constructor
  · apply (le_div_iff₀ hUV).mpr
    linarith [hh.1]
  · exact (div_le_iff₀ hUV).mpr hh.2

theorem packetScale_positive (F : Finset ColourTuple) {Y : ℝ} (k : TuplePartition.Key Y)
    (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0) (L T : ℝ) (hL : 0 < L) (hT : 0 < T)
    (E : Finset (SourceMaskIndex F)) (sector : Oˣ × ℕ × ℕ) :
    0 < packetScale F g L E sector T (D k g) (D k g) := by
  unfold packetScale
  rw [NaturalPunctureBudget.puncture_norm_eq]
  have hb := (NaturalPunctureBudget.badScale_bounds F E).1
  have hR : 1 ≤ NaturalPunctureBudget.goodScale F E :=
    norm_one_le (NaturalPunctureBudget.goodPart_ne_zero F E)
  have ho := norm_pos (offDiagonalIdeal_ne_zero g hgn)
  have hd := D_pos k g hgn
  exact div_pos (mul_pos (mul_pos hL (inputSectorScale_pos sector)) hT) (by positivity)

theorem packetScale_physical_relation (F : Finset ColourTuple) {Y : ℝ}
    (k : TuplePartition.Key Y) (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0)
    (L T : ℝ) (hL : 0 < L) (hrho : 0 < rho k)
    (E : Finset (SourceMaskIndex F)) (sector : Oˣ × ℕ × ℕ) :
    T=((packetScale F g L E sector T (D k g) (D k g))*
        (NaturalPunctureBudget.badScale F E*(rho k)^2/inputSectorScale sector))*
      FiveColourNorm.sharedDualScale (U k) (V k) L
        (Ideal.absNorm (TableBudget.G g):ℝ) (Ideal.absNorm (TableBudget.H g):ℝ)
        (Ideal.absNorm (TableBudget.J g):ℝ) (Ideal.absNorm (TableBudget.E g):ℝ)
        (Ideal.absNorm (TableBudget.F g):ℝ) (NaturalPunctureBudget.goodScale F E) := by
  have hn := table_norms_one_le g hgn
  have hb := (NaturalPunctureBudget.badScale_bounds F E).1
  have hR : 1 ≤ NaturalPunctureBudget.goodScale F E :=
    norm_one_le (NaturalPunctureBudget.goodPart_ne_zero F E)
  apply NaturalPhysicalBudget.physical_frequency_shared_scale
    (packetScale F g L E sector T (D k g) (D k g))
    (NaturalPunctureBudget.badScale F E) (NaturalPunctureBudget.goodScale F E) (rho k)
    (U k) (V k) (Ideal.absNorm (TableBudget.G g):ℝ) (Ideal.absNorm (TableBudget.H g):ℝ)
    (Ideal.absNorm (TableBudget.E g):ℝ) (Ideal.absNorm (TableBudget.F g):ℝ)
    (Ideal.absNorm (TableBudget.J g):ℝ) (D k g) L (inputSectorScale sector) T
    hL (inputSectorScale_pos sector) (by linarith) (by linarith) (U_pos k) (V_pos k) hrho
    (by linarith [hn.1]) (by linarith [hn.2.1]) (by linarith [hn.2.2.2.1])
    (by linarith [hn.2.2.2.2]) (by linarith [hn.2.2.1]) (D_normalized k g)
  unfold packetScale
  rw [NaturalPunctureBudget.puncture_norm_eq,offDiagonal_norm,pow_two]
  ring

end TableGeometry

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.fixed_pivot_ray
#print axioms Qrh.JointDetector.NaturalSelectedNorm.TableGeometry.cell_ranges
#print axioms Qrh.JointDetector.NaturalSelectedNorm.TableGeometry.D_normalized
#print axioms Qrh.JointDetector.NaturalSelectedNorm.TableGeometry.packetScale_physical_relation
