/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Candidate.Local.Qrh.JointDetector.NaturalTupleFibres
import Candidate.Local.Qrh.JointDetector.NaturalPivotBall
import Candidate.Local.Qrh.JointDetector.NaturalTuplePartition
import Candidate.Local.Qrh.JointDetector.NaturalTupleCount

/-! Exact full-ray and radius inheritance of the free colour-one fibres.
The left and right residual rays may differ. Their selected slot descriptors
are the literal common-coefficient quotients of the original descriptor. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredExceptionalCount NaturalSharedTables
local notation "O" => ActualEisensteinCubic.O

private theorem quotient_product (D I : Ideal O) (hD : D ≠ 0) : idealQuotient D (D*I)=I := by
  apply mul_left_cancel₀ hD
  exact idealQuotient_mul (show D ∣ D*I from ⟨I,rfl⟩)

theorem leftFamily_pivot_ray {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (hray : ∀ c ∈ F,∀ d ∈ F, primaryGenerator (c 0)-primaryGenerator (d 0) ∈
      (Ideal.span {(36:O)} : Ideal O)) :
    ∀ a ∈ leftFamily F g,∀ b ∈ leftFamily F g,
      primaryGenerator (a 0)-primaryGenerator (b 0) ∈ (Ideal.span {(36:O)} : Ideal O) := by
  intro a ha b hb
  have hl := leftFamily_ok hF hpF hgn hgp ha
  have hr := leftFamily_ok hF hpF hgn hgp hb
  have hD : rowProduct g 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hgn 0 k)
  have he := primaryQuotient_congruent_mod36 (rowProduct g 0)
    (recoverLeft g a 0) (recoverLeft g b 0) (hF _ hl.1 0)
    (show rowProduct g 0 ∣ recoverLeft g a 0 from ⟨a 0,rfl⟩)
    (show rowProduct g 0 ∣ recoverLeft g b 0 from ⟨b 0,rfl⟩)
    (hray _ hl.1 _ hr.1)
  simpa only [recoverLeft,quotient_product _ _ hD] using he

theorem rightFamily_pivot_ray {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (hray : ∀ c ∈ F,∀ d ∈ F, primaryGenerator (c 0)-primaryGenerator (d 0) ∈
      (Ideal.span {(36:O)} : Ideal O)) :
    ∀ a ∈ rightFamily F g,∀ b ∈ rightFamily F g,
      primaryGenerator (a 0)-primaryGenerator (b 0) ∈ (Ideal.span {(36:O)} : Ideal O) := by
  intro a ha b hb
  have hl := rightFamily_ok hF hpF hgn hgp ha
  have hr := rightFamily_ok hF hpF hgn hgp hb
  have hD : columnProduct g 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hgn k 0)
  have he := primaryQuotient_congruent_mod36 (columnProduct g 0)
    (recoverRight g a 0) (recoverRight g b 0) (hF _ hl.1 0)
    (show columnProduct g 0 ∣ recoverRight g a 0 from ⟨a 0,rfl⟩)
    (show columnProduct g 0 ∣ recoverRight g b 0 from ⟨b 0,rfl⟩)
    (hray _ hl.1 _ hr.1)
  simpa only [recoverRight,quotient_product _ _ hD] using he

theorem leftFamily_pivot_norm {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (U : ℝ) (hU : ∀ c ∈ F, (Ideal.absNorm (c 0):ℝ) ≤ U) :
    ∀ a ∈ leftFamily F g, (Ideal.absNorm (a 0):ℝ) ≤ U/(Ideal.absNorm (rowProduct g 0):ℝ) := by
  intro a ha
  have hl := leftFamily_ok hF hpF hgn hgp ha
  have hD : rowProduct g 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hgn 0 k)
  apply (le_div_iff₀ (norm_pos hD)).mpr
  have hh := hU _ hl.1
  simpa only [recoverLeft,map_mul,Nat.cast_mul,mul_comm] using hh

theorem rightFamily_pivot_norm {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (U : ℝ) (hU : ∀ c ∈ F, (Ideal.absNorm (c 0):ℝ) ≤ U) :
    ∀ a ∈ rightFamily F g, (Ideal.absNorm (a 0):ℝ) ≤ U/(Ideal.absNorm (columnProduct g 0):ℝ) := by
  intro a ha
  have hl := rightFamily_ok hF hpF hgn hgp ha
  have hD : columnProduct g 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hgn k 0)
  apply (le_div_iff₀ (norm_pos hD)).mpr
  have hh := hU _ hl.1
  simpa only [recoverRight,map_mul,Nat.cast_mul,mul_comm] using hh

/-- Radius clipping keeps the same auxiliary exponent A even when a dyadic
upper radius carries a fixed factor2. Empty balls below1 contribute zero. -/
theorem ball_radius_clip {N : ℕ} (Z A P mesh Cslot wmin δ K : ℝ)
    (hbound : ∀ (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image primaryGenerator) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i → (∀ I ∈ F,Admissible I) →
      (∀ I ∈ F,∀ J ∈ F,primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O)) →
      (∀ I ∈ F,(Ideal.absNorm I:ℝ) ≤ B) → 1 ≤ B → B ≤ Z^A → 1 ≤ L → L ≤ Z^P →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤ K*(L+B^(1-δ)*L^δ))
    (hK : 0 ≤ K) (hδ : δ ≤ 1)
    (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B Y L : ℝ)
    (hb : d.Bounded Z mesh Cslot) (hs : d.Selects Z (F.image primaryGenerator))
    (hslope : d.HasSlope δ) (hw : wmin ≤ ∑ i,d.width i)
    (hF : ∀ I ∈ F,Admissible I)
    (hray : ∀ I ∈ F,∀ J ∈ F,primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O))
    (hnB : ∀ I ∈ F,(Ideal.absNorm I:ℝ) ≤ B) (hnY : ∀ I ∈ F,(Ideal.absNorm I:ℝ) ≤ Y)
    (hB : 0 ≤ B) (hY : 1 ≤ Y) (hYA : Y ≤ Z^A) (hL : 1 ≤ L) (hLP : L ≤ Z^P)
    (hS : ∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ L) :
    selectedNorm (F.image primaryGenerator) S ≤ K*(L+B^(1-δ)*L^δ) := by
  by_cases hB1 : 1 ≤ B
  · apply (hbound d F S (min B Y) L hb hs hslope hw hF hray
      (fun I hI => le_min (hnB I hI) (hnY I hI)) (le_min hB1 hY)
      ((min_le_right _ _).trans hYA) hL hLP hS).trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (min_le_left _ _) (by linarith)) (by positivity)
  · have hempty : F=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      exact hB1 ((norm_one_le (hF I hI).1).trans (hnB I hI))
    simp only [hempty,Finset.image_empty,SlotHistogram.selectedNorm_empty_rows]
    positivity

/-- The squarefree ball estimate applies to every literal higher-colour
fibre after changing only the common slot coefficients. Its available
radius is clipped by the original height, rather than enlarging `A`. -/
theorem pivotFamily_ball_norm {N : ℕ} (Z A P mesh Cslot wmin δ K : ℝ)
    (hbound : ∀ (d : SelectedSlotData N) (F S : Finset (Ideal O)) (B L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image primaryGenerator) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i → (∀ I ∈ F,Admissible I) →
      (∀ I ∈ F,∀ J ∈ F,primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O)) →
      (∀ I ∈ F,(Ideal.absNorm I:ℝ) ≤ B) → 1 ≤ B → B ≤ Z^A → 1 ≤ L → L ≤ Z^P →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤ K*(L+B^(1-δ)*L^δ))
    (hK : 0 ≤ K) (hδ : δ ≤ 1)
    (d : SelectedSlotData N) (F : Finset ColourTuple) (S : Finset (Ideal O)) (B Y L : ℝ)
    (hb : d.Bounded Z mesh Cslot) (hs : d.Selects Z (F.image tupleRow))
    (hslope : d.HasSlope δ) (hw : wmin ≤ ∑ i,d.width i)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hray : ∀ c ∈ F,∀ d ∈ F,primaryGenerator (c 0)-primaryGenerator (d 0) ∈
      (Ideal.span {(36:O)} : Ideal O))
    (hnB : ∀ c ∈ F,(Ideal.absNorm (c 0):ℝ) ≤ B)
    (hnY : ∀ c ∈ F,(Ideal.absNorm (c 0):ℝ) ≤ Y)
    (hB : 0 ≤ B) (hY : 1 ≤ Y) (hYA : Y ≤ Z^A) (hL : 1 ≤ L) (hLP : L ≤ Z^P)
    (hS : ∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ L) (v : HigherTuple) :
    selectedNorm ((pivotFamily F v).image primaryGenerator) S ≤ K*(L+B^(1-δ)*L^δ) := by
  apply ball_radius_clip Z A P mesh Cslot wmin δ K hbound hK hδ
    (d.quotient (higherRow v)) (pivotFamily F v) S B Y L
    (SelectedSlotData.quotient_bounded hb _) (pivotFamily_selected d Z F hs v)
    (SelectedSlotData.quotient_hasSlope hslope _) hw (pivotFamily_admissible F hF v)
    ?_ ?_ ?_ hB hY hYA hL hLP hS
  · intro I hI J hJ
    obtain ⟨c,hc,hcv,rfl⟩ := mem_pivotFamily.mp hI
    obtain ⟨d,hd,hdv,rfl⟩ := mem_pivotFamily.mp hJ
    exact hray c hc d hd
  · intro I hI
    obtain ⟨c,hc,hcv,rfl⟩ := mem_pivotFamily.mp hI
    exact hnB c hc
  · intro I hI
    obtain ⟨c,hc,hcv,rfl⟩ := mem_pivotFamily.mp hI
    exact hnY c hc

namespace TableBudget

def G (g : SharedTable) : Ideal O := g 0 0
def H (g : SharedTable) : Ideal O := ∏ j : Fin 4,g j.succ j.succ
def E (g : SharedTable) : Ideal O := ∏ k : Fin 4,g 0 k.succ
def F (g : SharedTable) : Ideal O := ∏ j : Fin 4,g j.succ 0
def J (g : SharedTable) : Ideal O :=
  ∏ j : Fin 4,∏ k : Fin 4,if j=k then 1 else g j.succ k.succ

theorem row_zero (g : SharedTable) : rowProduct g 0=G g*E g := by
  simp only [rowProduct,Fin.prod_univ_succ,G,E]

theorem column_zero (g : SharedTable) : columnProduct g 0=G g*F g := by
  simp only [columnProduct,Fin.prod_univ_succ,G,F]

/-- Exact split of all twenty unequal-colour table entries. The six
possible exponent differences retain their original prime factors. -/
theorem offDiagonal_split (g : SharedTable) :
    (∏ q : Fin 5 × Fin 5,if q.1=q.2 then 1 else g q.1 q.2)=E g*F g*J g := by
  norm_num [Fintype.prod_prod_type,Fin.prod_univ_succ,E,F,J]
  ring

theorem higher_left (g : SharedTable) :
    (∏ j : Fin 4,rowProduct g j.succ)=H g*J g*F g := by
  norm_num [rowProduct,Fin.prod_univ_succ,H,J,F]
  ring

theorem higher_right (g : SharedTable) :
    (∏ k : Fin 4,columnProduct g k.succ)=H g*J g*E g := by
  norm_num [columnProduct,Fin.prod_univ_succ,H,J,E]
  ring

theorem diagonal (g : SharedTable) : (∏ j : Fin 5,g j j)=G g*H g := by
  simp only [Fin.prod_univ_succ,G,H]

theorem full (g : SharedTable) :
    (∏ j : Fin 5,rowProduct g j)=G g*H g*E g*F g*J g := by
  rw [Fin.prod_univ_succ,row_zero,higher_left]
  ac_rfl

theorem radical_left (g : SharedTable) (a : ColourTuple) :
    TuplePartition.radical (recoverLeft g a)=
      (G g*H g*E g*F g*J g)*TuplePartition.radical a := by
  simp only [TuplePartition.radical,recoverLeft,Finset.prod_mul_distrib,full]

theorem radical_right (g : SharedTable) (b : ColourTuple) :
    TuplePartition.radical (recoverRight g b)=
      (G g*H g*E g*F g*J g)*TuplePartition.radical b := by
  have he : (∏ k : Fin 5,columnProduct g k)=(∏ j : Fin 5,rowProduct g j) := by
    exact Finset.prod_comm
  simp only [TuplePartition.radical,recoverRight,Finset.prod_mul_distrib,he,full]

theorem higherIdeal_left (g : SharedTable) (a : ColourTuple) :
    higherIdeal (higherTuple (recoverLeft g a))=
      (H g*J g*F g)*higherIdeal (higherTuple a) := by
  simp only [higherIdeal,higherTuple,recoverLeft,Finset.prod_mul_distrib,higher_left]

theorem higherIdeal_right (g : SharedTable) (b : ColourTuple) :
    higherIdeal (higherTuple (recoverRight g b))=
      (H g*J g*E g)*higherIdeal (higherTuple b) := by
  simp only [higherIdeal,higherTuple,recoverRight,Finset.prod_mul_distrib,higher_right]

end TableBudget

/-- The separately recorded whole-radical dyad is comparable with the five
colour dyads by absolute constants, uniformly in all shared tables. -/
theorem cell_radicalScale_comparison (F : Finset ColourTuple) (Y : ℝ)
    (k : TuplePartition.Key Y) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (c : ColourTuple) (hc : c ∈ TuplePartition.cell F Y k) :
    (∏ j : Fin 5,TuplePartition.colourScale k j)/2 ≤ TuplePartition.radicalScale k ∧
      TuplePartition.radicalScale k ≤ 32*(∏ j : Fin 5,TuplePartition.colourScale k j) := by
  have hlo : (∏ j : Fin 5,TuplePartition.colourScale k j) ≤
      (Ideal.absNorm (TuplePartition.radical c):ℝ) := by
    simp only [TuplePartition.radical,map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun j _ => (TuplePartition.colourScale_pos k j).le)
      (fun j _ => (TuplePartition.cell_colour_bounds F Y k hF hheight c hc j).1)
  have hhi : (Ideal.absNorm (TuplePartition.radical c):ℝ) ≤
      32*(∏ j : Fin 5,TuplePartition.colourScale k j) := by
    have hh : (Ideal.absNorm (TuplePartition.radical c):ℝ) ≤
        ∏ j : Fin 5,2*TuplePartition.colourScale k j := by
      simp only [TuplePartition.radical,map_prod,Nat.cast_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun j _ => (TuplePartition.cell_colour_bounds F Y k hF hheight c hc j).2)
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      show (2:ℝ)^5=32 by norm_num] using hh
  have hdyad := TuplePartition.cell_radical_bounds F Y k hF hheight c hc
  constructor <;> linarith [hdyad.1,hdyad.2]

/-- Higher-fibre counting clips to the actual original height. A formal
radius below one gives an empty family, so no artificial `max 1` loss is
introduced into the shared-conductor scalar budget. -/
theorem higher_tuple_count_clipped (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset HigherTuple) (V Y : ℝ),
      0 ≤ V → 1 ≤ Y → (∀ v ∈ F,∀ j,v j ≠ 0) →
      (∀ v ∈ F,(Ideal.absNorm (higherIdeal v):ℝ) ≤ V) →
      (∀ v ∈ F,(Ideal.absNorm (higherIdeal v):ℝ) ≤ Y) →
      (F.card:ℝ) ≤ C*V*Y^ε := by
  obtain ⟨C,hC,hcount⟩ := higher_tuple_count ε hε
  refine ⟨C,hC,?_⟩
  intro F V Y hV hY hn hnV hnY
  by_cases hV1 : 1 ≤ V
  · have hh := hcount F (min V Y) (le_min hV1 hY) hn
      (fun v hv => le_min (hnV v hv) (hnY v hv))
    apply hh.trans
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (min_le_left V Y) hC.le)
      (Real.rpow_le_rpow (by positivity) (min_le_right V Y) hε.le)
      (by positivity) (by positivity)
  · have he : F=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hV1 ((norm_one_le (higherIdeal_ne_zero v (hn v hv))).trans (hnV v hv))
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem higherIdeal_dvd_radical (a : ColourTuple) :
    higherIdeal (higherTuple a) ∣ TuplePartition.radical a := by
  refine ⟨a 0,?_⟩
  simp only [TuplePartition.radical,Fin.prod_univ_succ,higherIdeal,higherTuple]
  ac_rfl

theorem leftFamily_original_height {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (Y : ℝ) (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) :
    ∀ a ∈ leftFamily F g,
      (Ideal.absNorm (a 0):ℝ) ≤ Y ∧ (Ideal.absNorm (higherIdeal (higherTuple a)):ℝ) ≤ Y := by
  intro a ha
  have hl := leftFamily_ok hF hpF hgn hgp ha
  have horig := TuplePartition.norms_le_height _ (hF _ hl.1) Y (hheight _ hl.1)
  have hd : a 0 ∣ recoverLeft g a 0 := ⟨rowProduct g 0,by simp only [recoverLeft,mul_comm]⟩
  refine ⟨(norm_le_of_dvd (hF _ hl.1 0).1 hd).trans (horig.1 0),?_⟩
  have hdRad : TuplePartition.radical a ∣ TuplePartition.radical (recoverLeft g a) := by
    rw [TableBudget.radical_left]
    exact dvd_mul_left _ _
  exact (norm_le_of_dvd (TuplePartition.radical_ne_zero _ (hF _ hl.1))
    ((higherIdeal_dvd_radical a).trans hdRad)).trans horig.2

theorem rightFamily_original_height {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (Y : ℝ) (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) :
    ∀ b ∈ rightFamily F g,
      (Ideal.absNorm (b 0):ℝ) ≤ Y ∧ (Ideal.absNorm (higherIdeal (higherTuple b)):ℝ) ≤ Y := by
  intro b hb
  have hr := rightFamily_ok hF hpF hgn hgp hb
  have horig := TuplePartition.norms_le_height _ (hF _ hr.1) Y (hheight _ hr.1)
  have hd : b 0 ∣ recoverRight g b 0 := ⟨columnProduct g 0,by simp only [recoverRight,mul_comm]⟩
  refine ⟨(norm_le_of_dvd (hF _ hr.1 0).1 hd).trans (horig.1 0),?_⟩
  have hdRad : TuplePartition.radical b ∣ TuplePartition.radical (recoverRight g b) := by
    rw [TableBudget.radical_right]
    exact dvd_mul_left _ _
  exact (norm_le_of_dvd (TuplePartition.radical_ne_zero _ (hF _ hr.1))
    ((higherIdeal_dvd_radical b).trans hdRad)).trans horig.2

theorem leftFamily_higher_norm {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (V : ℝ) (hV : ∀ c ∈ F,(Ideal.absNorm (higherIdeal (higherTuple c)):ℝ) ≤ V) :
    ∀ a ∈ leftFamily F g,(Ideal.absNorm (higherIdeal (higherTuple a)):ℝ) ≤
      V/(Ideal.absNorm (TableBudget.H g*TableBudget.J g*TableBudget.F g):ℝ) := by
  intro a ha
  have hl := leftFamily_ok hF hpF hgn hgp ha
  have hD : TableBudget.H g*TableBudget.J g*TableBudget.F g ≠ 0 := by
    rw [← TableBudget.higher_left]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      Finset.prod_ne_zero_iff.mpr fun k _ => hgn j.succ k
  apply (le_div_iff₀ (norm_pos hD)).mpr
  have hh := hV _ hl.1
  rw [TableBudget.higherIdeal_left,map_mul,Nat.cast_mul] at hh
  simpa only [mul_comm] using hh

theorem rightFamily_higher_norm {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (V : ℝ) (hV : ∀ c ∈ F,(Ideal.absNorm (higherIdeal (higherTuple c)):ℝ) ≤ V) :
    ∀ b ∈ rightFamily F g,(Ideal.absNorm (higherIdeal (higherTuple b)):ℝ) ≤
      V/(Ideal.absNorm (TableBudget.H g*TableBudget.J g*TableBudget.E g):ℝ) := by
  intro b hb
  have hr := rightFamily_ok hF hpF hgn hgp hb
  have hD : TableBudget.H g*TableBudget.J g*TableBudget.E g ≠ 0 := by
    rw [← TableBudget.higher_right]
    exact Finset.prod_ne_zero_iff.mpr fun k _ =>
      Finset.prod_ne_zero_iff.mpr fun j _ => hgn j k.succ
  apply (le_div_iff₀ (norm_pos hD)).mpr
  have hh := hV _ hr.1
  rw [TableBudget.higherIdeal_right,map_mul,Nat.cast_mul] at hh
  simpa only [mul_comm] using hh

theorem cell_higher_norm (F : Finset ColourTuple) (Y : ℝ) (k : TuplePartition.Key Y)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) :
    ∀ c ∈ TuplePartition.cell F Y k,(Ideal.absNorm (higherIdeal (higherTuple c)):ℝ) ≤
      16*(∏ j : Fin 4,TuplePartition.colourScale k j.succ) := by
  intro c hc
  have hh : (Ideal.absNorm (higherIdeal (higherTuple c)):ℝ) ≤
      ∏ j : Fin 4,2*TuplePartition.colourScale k j.succ := by
    simp only [higherIdeal,higherTuple,map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun j _ => (TuplePartition.cell_colour_bounds F Y k hF hheight c hc j.succ).2)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    show (2:ℝ)^4=16 by norm_num] using hh

theorem leftFamily_higher_cardinal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (g : SharedTable), (∀ j k,g j k ≠ 0) →
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) →
      ∀ Y V : ℝ,1 ≤ Y → 0 ≤ V →
      (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      (∀ c ∈ F,(Ideal.absNorm (higherIdeal (higherTuple c)):ℝ) ≤ V) →
      (((leftFamily F g).image higherTuple).card:ℝ) ≤
        C*(V/(Ideal.absNorm (TableBudget.H g*TableBudget.J g*TableBudget.F g):ℝ))*Y^ε := by
  obtain ⟨C,hC,hcount⟩ := higher_tuple_count_clipped ε hε
  refine ⟨C,hC,?_⟩
  intro F hF hpF g hgn hgp Y V hY hV hheight hnorm
  apply hcount _ _ Y (div_nonneg hV (Nat.cast_nonneg _)) hY
  · intro v hv j
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact ((leftFamily_ok hF hpF hgn hgp ha).2.1 j.succ).1
  · intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact leftFamily_higher_norm hF hpF hgn hgp V hnorm a ha
  · intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact (leftFamily_original_height hF hpF hgn hgp Y hheight a ha).2

theorem rightFamily_higher_cardinal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (F : Finset ColourTuple),
      (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      ∀ (g : SharedTable), (∀ j k,g j k ≠ 0) →
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) →
      ∀ Y V : ℝ,1 ≤ Y → 0 ≤ V →
      (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      (∀ c ∈ F,(Ideal.absNorm (higherIdeal (higherTuple c)):ℝ) ≤ V) →
      (((rightFamily F g).image higherTuple).card:ℝ) ≤
        C*(V/(Ideal.absNorm (TableBudget.H g*TableBudget.J g*TableBudget.E g):ℝ))*Y^ε := by
  obtain ⟨C,hC,hcount⟩ := higher_tuple_count_clipped ε hε
  refine ⟨C,hC,?_⟩
  intro F hF hpF g hgn hgp Y V hY hV hheight hnorm
  apply hcount _ _ Y (div_nonneg hV (Nat.cast_nonneg _)) hY
  · intro v hv j
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact ((rightFamily_ok hF hpF hgn hgp hb).2.1 j.succ).1
  · intro v hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact rightFamily_higher_norm hF hpF hgn hgp V hnorm b hb
  · intro v hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact (rightFamily_original_height hF hpF hgn hgp Y hheight b hb).2

/-- The closed squarefree norm, on the ACTUAL left residual fibres. The
mesh is chosen before the slot count, all common coefficient quotients are
contractive, and the original height supplies the clipped radius. -/
theorem leftFamily_pivot_selected_norm (A P gap loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgh : gap < 1/2) (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ,0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),0 ≤ Cslot → 0 < wmin →
      ∃ C Z₀ : ℝ,0 < C ∧ ∀ (Z mesh δ : ℝ),Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
        1/2+gap ≤ δ → δ ≤ 3/4 →
      ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (S : Finset (Ideal O))
        (g : SharedTable) (U Y L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i → (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      (∀ j k,g j k ≠ 0) →
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) →
      (∀ c ∈ F,∀ e ∈ F,primaryGenerator (c 0)-primaryGenerator (e 0) ∈
        (Ideal.span {(36:O)} : Ideal O)) →
      0 ≤ U → (∀ c ∈ F,(Ideal.absNorm (c 0):ℝ) ≤ U) →
      1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      1 ≤ L → L ≤ Z^P → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ L) →
      ∀ v : HigherTuple,
        selectedNorm ((pivotFamily (leftFamily F g) v).image primaryGenerator) S ≤
          C*Z^loss*(L+(U/(Ideal.absNorm (rowProduct g 0):ℝ))^(1-δ)*L^δ) := by
  obtain ⟨m,hm,hbound⟩ := NaturalPivotBall.squarefree_ball_selected_norm A P gap loss hA hP hgap hgh hloss
  refine ⟨m,hm,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨C,Z₀,hC,hbound⟩ := hbound N Cslot wmin hCslot hwmin
  refine ⟨C,max 1 Z₀,hC,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F S g U Y L hb hs hslope hw hF hpF hgn hgp hray
    hU hnorm hY hYA hheight hL hLP hS v
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hbound := hbound Z mesh δ ((le_max_right _ _).trans hZ) hm0 hmm hδlo hδhi
  apply pivotFamily_ball_norm Z A P mesh Cslot wmin δ (C*Z^loss) hbound
    (by positivity) (by linarith) (d.quotient (tupleRow (rowProduct g))) (leftFamily F g) S
    (U/(Ideal.absNorm (rowProduct g 0):ℝ)) Y L
    (SelectedSlotData.quotient_bounded hb _) (leftFamily_selects hpF hs)
    (SelectedSlotData.quotient_hasSlope hslope _) hw
    (fun a ha => (leftFamily_ok hF hpF hgn hgp ha).2.1)
    (leftFamily_pivot_ray hF hpF hgn hgp hray)
    (leftFamily_pivot_norm hF hpF hgn hgp U hnorm)
    (fun a ha => (leftFamily_original_height hF hpF hgn hgp Y hheight a ha).1)
    (div_nonneg hU (Nat.cast_nonneg _)) hY hYA hL hLP hS v

theorem rightFamily_pivot_selected_norm (A P gap loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgh : gap < 1/2) (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ,0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),0 ≤ Cslot → 0 < wmin →
      ∃ C Z₀ : ℝ,0 < C ∧ ∀ (Z mesh δ : ℝ),Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
        1/2+gap ≤ δ → δ ≤ 3/4 →
      ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (S : Finset (Ideal O))
        (g : SharedTable) (U Y L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i → (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) →
      (∀ j k,g j k ≠ 0) →
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) →
      (∀ c ∈ F,∀ e ∈ F,primaryGenerator (c 0)-primaryGenerator (e 0) ∈
        (Ideal.span {(36:O)} : Ideal O)) →
      0 ≤ U → (∀ c ∈ F,(Ideal.absNorm (c 0):ℝ) ≤ U) →
      1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      1 ≤ L → L ≤ Z^P → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ L) →
      ∀ v : HigherTuple,
        selectedNorm ((pivotFamily (rightFamily F g) v).image primaryGenerator) S ≤
          C*Z^loss*(L+(U/(Ideal.absNorm (columnProduct g 0):ℝ))^(1-δ)*L^δ) := by
  obtain ⟨m,hm,hbound⟩ := NaturalPivotBall.squarefree_ball_selected_norm A P gap loss hA hP hgap hgh hloss
  refine ⟨m,hm,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨C,Z₀,hC,hbound⟩ := hbound N Cslot wmin hCslot hwmin
  refine ⟨C,max 1 Z₀,hC,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F S g U Y L hb hs hslope hw hF hpF hgn hgp hray
    hU hnorm hY hYA hheight hL hLP hS v
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hbound := hbound Z mesh δ ((le_max_right _ _).trans hZ) hm0 hmm hδlo hδhi
  apply pivotFamily_ball_norm Z A P mesh Cslot wmin δ (C*Z^loss) hbound
    (by positivity) (by linarith) (d.quotient (tupleRow (columnProduct g))) (rightFamily F g) S
    (U/(Ideal.absNorm (columnProduct g 0):ℝ)) Y L
    (SelectedSlotData.quotient_bounded hb _) (rightFamily_selects hpF hs)
    (SelectedSlotData.quotient_hasSlope hslope _) hw
    (fun b hb => (rightFamily_ok hF hpF hgn hgp hb).2.1)
    (rightFamily_pivot_ray hF hpF hgn hgp hray)
    (rightFamily_pivot_norm hF hpF hgn hgp U hnorm)
    (fun b hb => (rightFamily_original_height hF hpF hgn hgp Y hheight b hb).1)
    (div_nonneg hU (Nat.cast_nonneg _)) hY hYA hL hLP hS v

theorem TableBudget.full_ne_zero (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0) :
    G g*H g*E g*F g*J g ≠ 0 := by
  rw [← full]
  exact Finset.prod_ne_zero_iff.mpr fun j _ =>
    Finset.prod_ne_zero_iff.mpr fun k _ => hgn j k

theorem leftFamily_cell_radical_coordinate (F : Finset ColourTuple) (Y : ℝ)
    (k : TuplePartition.Key Y) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l)))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (a : ColourTuple) (ha : a ∈ leftFamily (TuplePartition.cell F Y k) g) :
    (Ideal.absNorm (TuplePartition.radical a):ℝ)/
      (TuplePartition.radicalScale k/(Ideal.absNorm
        (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)) ∈
      Set.Icc (1:ℝ) 2 := by
  have hl := leftFamily_ok (fun c hc => hF c (Finset.mem_filter.mp hc).1)
    (fun c hc => hpF c (Finset.mem_filter.mp hc).1) hgn hgp ha
  have hh := TuplePartition.cell_radical_coordinate F Y k hF hheight _ hl.1
  rw [TableBudget.radical_left,map_mul,Nat.cast_mul] at hh
  have ht := norm_pos (TableBudget.full_ne_zero g hgn)
  have hs := TuplePartition.radicalScale_pos k
  have he : (Ideal.absNorm
        (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)*
      (Ideal.absNorm (TuplePartition.radical a):ℝ)/TuplePartition.radicalScale k=
      (Ideal.absNorm (TuplePartition.radical a):ℝ)/(TuplePartition.radicalScale k/
        (Ideal.absNorm (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)) := by
    field_simp
  simpa only [he] using hh

theorem rightFamily_cell_radical_coordinate (F : Finset ColourTuple) (Y : ℝ)
    (k : TuplePartition.Key Y) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l)))
    (hheight : ∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y)
    (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (b : ColourTuple) (hb : b ∈ rightFamily (TuplePartition.cell F Y k) g) :
    (Ideal.absNorm (TuplePartition.radical b):ℝ)/
      (TuplePartition.radicalScale k/(Ideal.absNorm
        (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)) ∈
      Set.Icc (1:ℝ) 2 := by
  have hr := rightFamily_ok (fun c hc => hF c (Finset.mem_filter.mp hc).1)
    (fun c hc => hpF c (Finset.mem_filter.mp hc).1) hgn hgp hb
  have hh := TuplePartition.cell_radical_coordinate F Y k hF hheight _ hr.1
  rw [TableBudget.radical_right,map_mul,Nat.cast_mul] at hh
  have ht := norm_pos (TableBudget.full_ne_zero g hgn)
  have hs := TuplePartition.radicalScale_pos k
  have he : (Ideal.absNorm
        (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)*
      (Ideal.absNorm (TuplePartition.radical b):ℝ)/TuplePartition.radicalScale k=
      (Ideal.absNorm (TuplePartition.radical b):ℝ)/(TuplePartition.radicalScale k/
        (Ideal.absNorm (TableBudget.G g*TableBudget.H g*TableBudget.E g*TableBudget.F g*TableBudget.J g):ℝ)) := by
    field_simp
  simpa only [he] using hh

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.leftFamily_pivot_ray
#print axioms Qrh.JointDetector.NaturalSelectedNorm.ball_radius_clip
#print axioms Qrh.JointDetector.NaturalSelectedNorm.pivotFamily_ball_norm
#print axioms Qrh.JointDetector.NaturalSelectedNorm.TableBudget.offDiagonal_split
#print axioms Qrh.JointDetector.NaturalSelectedNorm.cell_radicalScale_comparison
#print axioms Qrh.JointDetector.NaturalSelectedNorm.higher_tuple_count_clipped
#print axioms Qrh.JointDetector.NaturalSelectedNorm.leftFamily_higher_cardinal
#print axioms Qrh.JointDetector.NaturalSelectedNorm.rightFamily_higher_cardinal
#print axioms Qrh.JointDetector.NaturalSelectedNorm.leftFamily_pivot_selected_norm
#print axioms Qrh.JointDetector.NaturalSelectedNorm.rightFamily_pivot_selected_norm
#print axioms Qrh.JointDetector.NaturalSelectedNorm.leftFamily_cell_radical_coordinate
#print axioms Qrh.JointDetector.NaturalSelectedNorm.rightFamily_cell_radical_coordinate
