/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalOwnFactorBounds
import Submissions.arvi_selected_leaf.JointDetector.NaturalPivotTransport

/-! Application of the common Mellin estimate to the literal natural packet.
All unary, common-source and higher-kernel bounds are proved for the actual
functions. The two selected pivot norm bounds remain explicit operator inputs. -/
namespace Qrh.JointDetector.NaturalSwapBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open NaturalSelectedNorm NaturalSharedTables NaturalPairPackets NaturalNearPackets
open FiveColourNorm FiveColourMellin
local notation "O" => ActualEisensteinCubic.O

theorem leftFamily_pairwise (F : Finset ColourTuple)
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a : ColourTuple) (ha : a ∈ leftFamily F g) :
    Pairwise (fun j k => IsCoprime (a j) (a k)) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨c,d⟩,hp,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  exact leftResidual_pairwise (hpF c hc) (hpF d hd)

theorem rightFamily_pairwise (F : Finset ColourTuple)
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a : ColourTuple) (ha : a ∈ rightFamily F g) :
    Pairwise (fun j k => IsCoprime (a j) (a k)) := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨c,d⟩,hp,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  exact rightResidual_pairwise (hpF c hc) (hpF d hd)

theorem packetHigherKernel_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (v : (leftFamily F g).image higherTuple) (w : (rightFamily F g).image higherTuple) :
    ‖packetHigherKernel F hF g rL rR v w‖ ≤ 1 := by
  obtain ⟨a,ha,hav⟩ := Finset.mem_image.mp v.property
  obtain ⟨b,hb,hbw⟩ := Finset.mem_image.mp w.property
  have hv := higherAsTuple_pairwise a (leftFamily_pairwise F hpF g a ha)
  have hw := higherAsTuple_pairwise b (rightFamily_pairwise F hpF g b hb)
  rw [hav] at hv
  rw [hbw] at hw
  have hG := higherGaussFactor_norm_le_eight F hF g hgp v.val w.val hv hw rL rR
  have hdiv : ‖higherGaussFactor F hF g v.val w.val rL rR/(8:ℂ)‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    exact (div_le_one₀ (by norm_num : (0:ℝ) < 8)).mpr hG
  rw [packetHigherKernel,norm_mul]
  exact (mul_le_mul hdiv (higherPairMask_norm_le_one v.val w.val)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem packetWeight_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j)) (g : SharedTable) (q b : O)
    (rL rR : EisensteinEPrimaryPhase.Coord) (S : Finset (Ideal O))
    (v : (leftFamily F g).image higherTuple) (w : (rightFamily F g).image higherTuple) (I : S) :
    ‖packetWeight F hF g q b rL rR S v w I‖ ≤ 1 :=
  NaturalFrequencyReindex.commonWeight_norm_le F hF g v.val w.val q b rL rR I.val

theorem bareHigherModulation_norm_le (F : Finset ColourTuple) (u : O) (v : HigherTuple) :
    ‖bareHigherModulation F u v‖ ≤ 1 := idealRowHom_norm _ _

theorem leftRows_nonzero (F : Finset ColourTuple) (g : SharedTable)
    (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (v : (leftFamily F g).image higherTuple) (u : leftRows F g v) : u.val ≠ 0 := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp u.property
  rw [← he]
  exact supported_primaryGenerator_ne_zero I
    (admissible_supported (pivotFamily_admissible (leftFamily F g) hLF v.val I hI))

theorem rightRows_nonzero (F : Finset ColourTuple) (g : SharedTable)
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
    (v : (rightFamily F g).image higherTuple) (u : rightRows F g v) : u.val ≠ 0 := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp u.property
  rw [← he]
  exact supported_primaryGenerator_ne_zero I
    (admissible_supported (pivotFamily_admissible (rightFamily F g) hRF v.val I hI))

theorem leftRows_norm_le (F : Finset ColourTuple) (g : SharedTable)
    (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j)) (BL : ℝ)
    (hBL : ∀ a ∈ leftFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BL)
    (v : (leftFamily F g).image higherTuple) (u : leftRows F g v) :
    ((Ideal.span {u.val}).absNorm:ℝ) ≤ BL := by
  rw [fibreTuple_pivot_span (leftFamily F g) hLF ⟨v,u⟩]
  exact hBL _ (fibreTuple_mem (leftFamily F g) hLF ⟨v,u⟩)

theorem rightRows_norm_le (F : Finset ColourTuple) (g : SharedTable)
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (BR : ℝ)
    (hBR : ∀ a ∈ rightFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BR)
    (v : (rightFamily F g).image higherTuple) (u : rightRows F g v) :
    ((Ideal.span {u.val}).absNorm:ℝ) ≤ BR := by
  rw [fibreTuple_pivot_span (rightFamily F g) hRF ⟨v,u⟩]
  exact hBR _ (fibreTuple_mem (rightFamily F g) hRF ⟨v,u⟩)

/-- The literal actual radial swap, with all cross masks and source phases. -/
def naturalRadialSwap (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (α β : ColourTuple → ℂ)
    (q b : O) (rL rR : EisensteinEPrimaryPhase.Coord) (DL DR : ℝ)
    (S : Finset (Ideal O)) (Y : ℝ) (W : 𝓢(ℝ,ℂ)) (R : ℝ) : ℂ :=
  radialActualSwap (leftRows F g) (rightRows F g) S
    (leftPacketArray F hF g hLF α q b DL) (rightPacketArray F hF g hRF β q b DR)
    (fun u w => higherModulation F u w.val) (fun u v => higherModulation F u v.val)
    (packetHigherKernel F hF g rL rR) (packetWeight F hF g q b rL rR S)
    (leftPacketCoordinate F g hLF DL) (rightPacketCoordinate F g hRF DR)
    (fun I : S => (Ideal.absNorm I.val:ℝ)/Y) W R

/-- One profile constant is chosen before the family, table, source set,
coefficients, dyadic scales and selected pivot norm bounds. -/
theorem natural_radial_bound (W : 𝓢(ℝ,ℂ)) (decay : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ R : ℝ,0 < R →
    ∀ (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
      (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
      (g : SharedTable)
      (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
      (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
      (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (α β : ColourTuple → ℂ)
      (q b : O) (rL rR : EisensteinEPrimaryPhase.Coord) (DL DR : ℝ)
      (S : Finset (Ideal O)) (Y KL KR BL BR ε : ℝ) (hε : 0 < ε),
      0 ≤ KL → 0 ≤ KR → 0 ≤ BL → 0 ≤ BR →
      (∀ v,selectedNorm (leftRows F g v) S ≤ KL) →
      (∀ w,selectedNorm (rightRows F g w) S ≤ KR) →
      (∀ a ∈ leftFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BL) →
      (∀ a ∈ rightFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BR) →
      0 < DL → 0 < DR → 0 < Y →
      (∀ a ∈ leftFamily F g,radicalNorm a/DL ∈ Set.Icc (1:ℝ) 2) →
      (∀ a ∈ rightFamily F g,radicalNorm a/DR ∈ Set.Icc (1:ℝ) 2) →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ)/Y ∈ Set.Icc (1:ℝ) 2) →
      ‖naturalRadialSwap F hF g hLF hRF α β q b rL rR DL DR S Y W R‖ ≤
        (C/(1+R)^decay)*
        Real.sqrt (((rightFamily F g).image higherTuple).card*KL*
          (idealDivisorConstant ε hε*BL^ε)*(∑ u,‖leftPacketArray F hF g hLF α q b DL u‖^2))*
        Real.sqrt (((leftFamily F g).image higherTuple).card*KR*
          (idealDivisorConstant ε hε*BR^ε)*(∑ u,‖rightPacketArray F hF g hRF β q b DR u‖^2)) := by
  obtain ⟨C,hC,hbound⟩ := common_radial_actualSwap_bound W decay
  refine ⟨C,hC,?_⟩
  intro R hR F hF hpF g hgp hLF hRF α β q b rL rR DL DR S Y KL KR BL BR ε hε
    hKL hKR hBL hBR hEL hER hNL hNR hDL hDR hY hx hy hz
  simpa only [naturalRadialSwap,Fintype.card_coe,mul_assoc,leftRows,rightRows] using
    hbound R hR (leftRows F g) (rightRows F g) S
    (leftPacketArray F hF g hLF α q b DL) (rightPacketArray F hF g hRF β q b DR)
    (fun u w => higherModulation F u w.val) (fun u v => higherModulation F u v.val)
    (packetHigherKernel F hF g rL rR) (packetWeight F hF g q b rL rR S)
    (leftPacketCoordinate F g hLF DL) (rightPacketCoordinate F g hRF DR)
    (fun I : S => (Ideal.absNorm I.val:ℝ)/Y) KL KR BL BR ε hε
    hKL hKR hBL hBR hEL hER
    (fun u w => higherModulation_norm_le_one F u w.val)
    (fun u v => higherModulation_norm_le_one F u v.val)
    (packetHigherKernel_norm_le F hF hpF g hgp rL rR)
    (packetWeight_norm_le F hF g q b rL rR S)
    (leftRows_nonzero F g hLF) (rightRows_nonzero F g hRF)
    (leftRows_norm_le F g hLF BL hNL) (rightRows_norm_le F g hRF BR hNR)
    (fun u => hx _ (fibreTuple_mem (leftFamily F g) hLF u))
    (fun u => hy _ (fibreTuple_mem (rightFamily F g) hRF u)) (fun I => hz I.val I.property)

/-- The actual cell coordinate is inherited by every left projected fibre. -/
theorem left_cell_coordinate (F : Finset ColourTuple) (Y : ℝ) (k : TuplePartition.Key Y)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l)))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (hLF : ∀ a ∈ leftFamily (TuplePartition.cell F Y k) g,∀ j,Admissible (a j))
    (u : ElementFibre (leftFamily (TuplePartition.cell F Y k) g)) :
    leftPacketCoordinate (TuplePartition.cell F Y k) g hLF
      (TuplePartition.radicalScale k/(Ideal.absNorm
        (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)) u ∈
      Set.Icc (1:ℝ) 2 :=
  leftFamily_cell_radical_coordinate F Y k hF hpF hheight g hgn hgp
    (fibreTuple _ hLF u) (fibreTuple_mem _ hLF u)

theorem right_cell_coordinate (F : Finset ColourTuple) (Y : ℝ) (k : TuplePartition.Key Y)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l)))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (hRF : ∀ a ∈ rightFamily (TuplePartition.cell F Y k) g,∀ j,Admissible (a j))
    (u : ElementFibre (rightFamily (TuplePartition.cell F Y k) g)) :
    rightPacketCoordinate (TuplePartition.cell F Y k) g hRF
      (TuplePartition.radicalScale k/(Ideal.absNorm
        (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)) u ∈
      Set.Icc (1:ℝ) 2 :=
  rightFamily_cell_radical_coordinate F Y k hF hpF hheight g hgn hgp
    (fibreTuple _ hRF u) (fibreTuple_mem _ hRF u)

/-- The geometric [1,2] coordinate supplies the radical condition needed by
the actual array mass contraction, on the full original fibre. -/
theorem left_array_mass_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (D : ℝ) (hD : 0 < D)
    (hx : ∀ a ∈ leftFamily F g,radicalNorm a/D ∈ Set.Icc (1:ℝ) 2) :
    (∑ u,‖leftPacketArray F hF g hLF α q b D u‖^2) ≤
      ∑ a ∈ leftFamily F g,‖α (recoverLeft g a)‖^2 := by
  have hh := NaturalOwnFactorBounds.leftPacketArray_subset_mass F hF hpF g hLF α q b D hD.le
    Finset.univ (by
      intro u hu
      have ht := (hx _ (fibreTuple_mem (leftFamily F g) hLF u)).1
      simpa only [one_mul] using (le_div_iff₀ hD).mp ht)
  exact hh

theorem right_array_mass_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (D : ℝ) (hD : 0 < D)
    (hx : ∀ a ∈ rightFamily F g,radicalNorm a/D ∈ Set.Icc (1:ℝ) 2) :
    (∑ u,‖rightPacketArray F hF g hRF α q b D u‖^2) ≤
      ∑ a ∈ rightFamily F g,‖α (recoverRight g a)‖^2 := by
  have hh := NaturalOwnFactorBounds.rightPacketArray_subset_mass F hF hpF g hRF α q b D hD.le
    Finset.univ (by
      intro u hu
      have ht := (hx _ (fibreTuple_mem (rightFamily F g) hRF u)).1
      simpa only [one_mul] using (le_div_iff₀ hD).mp ht)
  exact hh

/-- The same actual Mellin bound paid from the original recovered arrays. -/
theorem natural_radial_bound_original_mass (W : 𝓢(ℝ,ℂ)) (decay : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ R : ℝ,0 < R →
    ∀ (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
      (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
      (g : SharedTable)
      (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
      (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
      (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (α β : ColourTuple → ℂ)
      (q b : O) (rL rR : EisensteinEPrimaryPhase.Coord) (DL DR : ℝ)
      (S : Finset (Ideal O)) (Y KL KR BL BR ε : ℝ) (hε : 0 < ε),
      0 ≤ KL → 0 ≤ KR → 0 ≤ BL → 0 ≤ BR →
      (∀ v,selectedNorm (leftRows F g v) S ≤ KL) →
      (∀ w,selectedNorm (rightRows F g w) S ≤ KR) →
      (∀ a ∈ leftFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BL) →
      (∀ a ∈ rightFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BR) →
      0 < DL → 0 < DR → 0 < Y →
      (∀ a ∈ leftFamily F g,radicalNorm a/DL ∈ Set.Icc (1:ℝ) 2) →
      (∀ a ∈ rightFamily F g,radicalNorm a/DR ∈ Set.Icc (1:ℝ) 2) →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ)/Y ∈ Set.Icc (1:ℝ) 2) →
      ‖naturalRadialSwap F hF g hLF hRF α β q b rL rR DL DR S Y W R‖ ≤
        (C/(1+R)^decay)*
        Real.sqrt (((rightFamily F g).image higherTuple).card*KL*
          (idealDivisorConstant ε hε*BL^ε)*(∑ a ∈ leftFamily F g,‖α (recoverLeft g a)‖^2))*
        Real.sqrt (((leftFamily F g).image higherTuple).card*KR*
          (idealDivisorConstant ε hε*BR^ε)*(∑ a ∈ rightFamily F g,‖β (recoverRight g a)‖^2)) := by
  obtain ⟨C,hC,hbound⟩ := natural_radial_bound W decay
  refine ⟨C,hC,?_⟩
  intro R hR F hF hpF g hgp hLF hRF α β q b rL rR DL DR S Y KL KR BL BR ε hε
    hKL hKR hBL hBR hEL hER hNL hNR hDL hDR hY hx hy hz
  have ht := hbound R hR F hF hpF g hgp hLF hRF α β q b rL rR DL DR S Y KL KR BL BR ε hε
    hKL hKR hBL hBR hEL hER hNL hNR hDL hDR hY hx hy hz
  have hmL := left_array_mass_le F hF hpF g hLF α q b DL hDL hx
  have hmR := right_array_mass_le F hF hpF g hRF β q b DR hDR hy
  have hsL := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmL
    (show 0 ≤ (((rightFamily F g).image higherTuple).card:ℝ)*KL*
      (idealDivisorConstant ε hε*BL^ε) by positivity [idealDivisorConstant_pos ε hε]))
  have hsR := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmR
    (show 0 ≤ (((leftFamily F g).image higherTuple).card:ℝ)*KR*
      (idealDivisorConstant ε hε*BR^ε) by positivity [idealDivisorConstant_pos ε hε]))
  have hc : 0 ≤ C/(1+R)^decay := by positivity
  exact ht.trans (mul_le_mul (mul_le_mul_of_nonneg_left hsL hc) hsR
    (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _)))

end
end Qrh.JointDetector.NaturalSwapBound

#print axioms Qrh.JointDetector.NaturalSwapBound.packetHigherKernel_norm_le
#print axioms Qrh.JointDetector.NaturalSwapBound.packetWeight_norm_le
#print axioms Qrh.JointDetector.NaturalSwapBound.leftRows_nonzero
#print axioms Qrh.JointDetector.NaturalSwapBound.rightRows_norm_le
#print axioms Qrh.JointDetector.NaturalSwapBound.natural_radial_bound
#print axioms Qrh.JointDetector.NaturalSwapBound.left_cell_coordinate
#print axioms Qrh.JointDetector.NaturalSwapBound.right_cell_coordinate
#print axioms Qrh.JointDetector.NaturalSwapBound.left_array_mass_le
#print axioms Qrh.JointDetector.NaturalSwapBound.natural_radial_bound_original_mass
