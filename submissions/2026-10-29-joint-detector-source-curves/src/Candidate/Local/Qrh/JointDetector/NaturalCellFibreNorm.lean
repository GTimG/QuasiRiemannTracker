/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalPivotTransport
import Candidate.Local.Qrh.JointDetector.NaturalNearNorm

/-! Both actual pivot fibres under one early mesh. The source dyad's upper
endpoint 2T is clipped to the original auxiliary cap before applying the
squarefree theorem; only its scalar envelope is then enlarged.
-/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredExceptionalCount NaturalSharedTables
local notation "O" => ActualEisensteinCubic.O

theorem cell_pivot_selected_norms (A P gap loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgh : gap < 1/2) (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ,0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),0 ≤ Cslot → 0 < wmin →
      ∃ C Z₀ : ℝ,0 < C ∧ ∀ (Z mesh δ : ℝ),Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
        1/2+gap ≤ δ → δ ≤ 3/4 →
      ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (S : Finset (Ideal O))
        (Y T : ℝ) (k : TuplePartition.Key Y) (g : SharedTable),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i → (∀ c ∈ F,∀ j,Admissible (c j)) →
      (∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l))) →
      (∀ j l,g j l ≠ 0) →
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) →
      1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      1 ≤ T → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ 2*T) →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ Z^P) →
      (∀ v : HigherTuple,
        selectedNorm ((pivotFamily (leftFamily (TuplePartition.cell F Y k) g) v).image primaryGenerator) S ≤
          C*Z^loss*(2*T+((2*TuplePartition.colourScale k 0)/
            (Ideal.absNorm (rowProduct g 0):ℝ))^(1-δ)*(2*T)^δ)) ∧
      (∀ v : HigherTuple,
        selectedNorm ((pivotFamily (rightFamily (TuplePartition.cell F Y k) g) v).image primaryGenerator) S ≤
          C*Z^loss*(2*T+((2*TuplePartition.colourScale k 0)/
            (Ideal.absNorm (columnProduct g 0):ℝ))^(1-δ)*(2*T)^δ)) := by
  obtain ⟨ml,hml,hleft⟩ := leftFamily_pivot_selected_norm A P gap loss hA hP hgap hgh hloss
  obtain ⟨mr,hmr,hright⟩ := rightFamily_pivot_selected_norm A P gap loss hA hP hgap hgh hloss
  refine ⟨min ml mr,lt_min hml hmr,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Cl,Zl,hCl,hleft⟩ := hleft N Cslot wmin hCslot hwmin
  obtain ⟨Cr,Zr,hCr,hright⟩ := hright N Cslot wmin hCslot hwmin
  refine ⟨Cl+Cr,max 1 (max Zl Zr),add_pos hCl hCr,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F S Y T k g hb hs hslope hw hF hpF hgn hgp hY hYA hheight hT hST hScap
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hz0 : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hZl : Zl ≤ Z := (le_max_left Zl Zr).trans ((le_max_right _ _).trans hZ)
  have hZr : Zr ≤ Z := (le_max_right Zl Zr).trans ((le_max_right _ _).trans hZ)
  have hleft := hleft Z mesh δ hZl hm0 (hmm.trans (min_le_left _ _)) hδlo hδhi
  have hright := hright Z mesh δ hZr hm0 (hmm.trans (min_le_right _ _)) hδlo hδhi
  have hδ0 : 0 ≤ δ := by linarith
  have hcap : 1 ≤ Z^P := Real.one_le_rpow hz1 (by linarith)
  let Fc := TuplePartition.cell F Y k
  let U := 2*TuplePartition.colourScale k 0
  have hU : 0 ≤ U := (mul_pos (by norm_num : (0:ℝ) < 2) (TuplePartition.colourScale_pos k 0)).le
  have hFc : ∀ c ∈ Fc,∀ j,Admissible (c j) :=
    fun c hc j => hF c (Finset.mem_filter.mp hc).1 j
  have hpc : ∀ c ∈ Fc,Pairwise (fun j l => IsCoprime (c j) (c l)) :=
    fun c hc => hpF c (Finset.mem_filter.mp hc).1
  have hsel : d.Selects Z (Fc.image tupleRow) := TuplePartition.cell_selects d Z F Y k hs
  have hheightc : ∀ c ∈ Fc,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y :=
    fun c hc => hheight c (Finset.mem_filter.mp hc).1
  have hray : ∀ c ∈ Fc,∀ e ∈ Fc,primaryGenerator (c 0)-primaryGenerator (e 0) ∈
      (Ideal.span {(36:O)} : Ideal O) := fun c hc e he => TuplePartition.cell_same_ray F Y k c e hc he 0
  have hnorm : ∀ c ∈ Fc,(Ideal.absNorm (c 0):ℝ) ≤ U :=
    fun c hc => (TuplePartition.cell_colour_bounds F Y k hF hheight c hc 0).2
  have hT2 : 1 ≤ 2*T := by linarith
  constructor
  · intro v
    have hB : 0 ≤ U/(Ideal.absNorm (rowProduct g 0):ℝ) := div_nonneg hU (Nat.cast_nonneg _)
    have hh := source_norm_clip
      ((pivotFamily (leftFamily Fc g) v).image primaryGenerator) S
      (U/(Ideal.absNorm (rowProduct g 0):ℝ)) (2*T) (Z^P) δ (Cl*Z^loss)
      hB hT2 hcap hδ0 (by positivity) hST hScap
      (fun t ht htP hSt => hleft d Fc S g U Y t hb hsel hslope hw hFc hpc hgn hgp hray
        hU hnorm hY hYA hheightc ht htP hSt v)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith : Cl ≤ Cl+Cr) (Real.rpow_nonneg hz0.le loss)
  · intro v
    have hB : 0 ≤ U/(Ideal.absNorm (columnProduct g 0):ℝ) := div_nonneg hU (Nat.cast_nonneg _)
    have hh := source_norm_clip
      ((pivotFamily (rightFamily Fc g) v).image primaryGenerator) S
      (U/(Ideal.absNorm (columnProduct g 0):ℝ)) (2*T) (Z^P) δ (Cr*Z^loss)
      hB hT2 hcap hδ0 (by positivity) hST hScap
      (fun t ht htP hSt => hright d Fc S g U Y t hb hsel hslope hw hFc hpc hgn hgp hray
        hU hnorm hY hYA hheightc ht htP hSt v)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith : Cr ≤ Cl+Cr) (Real.rpow_nonneg hz0.le loss)

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.cell_pivot_selected_norms
