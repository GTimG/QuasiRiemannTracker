import WeightedQRH.NumeratorReflectionGeometry
import WeightedQRH.NumeratorDilationBoxes
import WeightedQRH.Parameters

/-! Exact scale and capacity bookkeeping for finite coefficient-dilation boxes. -/
noncomputable section
open scoped BigOperators Classical
open Filter
namespace WeightedQRH.Numerator

lemma physical_y_range (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ WeightedQRH.h+WeightedQRH.rowExtension) :
    (1/2:ℝ) < WeightedQRH.ly/d ∧ WeightedQRH.ly/d < 1 := by
  have hdp : 0 < d := by linarith
  constructor
  · apply (lt_div_iff₀ hdp).mpr
    have hh := WeightedQRH.extended_numerator_short
    linarith
  · apply (div_lt_one hdp).mpr
    exact WeightedQRH.ly_lt_half.trans_le hd

/-- The coarse finite box range suffices: the maximum reflected length remains
below the fixed L=2 empty-slot endpoint, uniformly in all actual high dyads. -/
theorem reflected_box_geometry (d v boxWidth annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ WeightedQRH.h+WeightedQRH.rowExtension)
    (hv:0 ≤ v) (hvmax:v ≤ 1+boxWidth) (hbox:0 ≤ boxWidth)
    (hann:0 ≤ annulusSlack) (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    0 ≤ 1-WeightedQRH.ly/d+v+boxWidth ∧
      (1-WeightedQRH.ly/d+v+boxWidth)+annulusSlack ≤ 2 := by
  obtain ⟨hylo,hyhi⟩ := physical_y_range d hd hdmax
  constructor <;> linarith

/-- A dilation-box upper edge bounds the combined primitive-plus-redundant
conductor relative to the actual original scale Y/N. -/
theorem combined_scale_of_dilation_box (U C Cu rowSize N y v boxWidth:ℝ)
    (hU:0 < U) (hC:0 < C) (hrow:0 < rowSize) (hrowU:rowSize ≤ U) (hN:0 < N)
    (hbox:max 1 (Cu*N/(C*rowSize)) ≤ U^(v+boxWidth)) :
    Cu ≤ C*U^(1-y+v+boxWidth)*(U^y/N) := by
  have hb : Cu*N ≤ U^(v+boxWidth)*(C*rowSize) :=
    (div_le_iff₀ (mul_pos hC hrow)).mp ((le_max_right _ _).trans hbox)
  have hprod : Cu*N ≤ C*(U^(v+boxWidth)*U) := by
    calc
      _ ≤ U^(v+boxWidth)*(C*rowSize) := hb
      _ ≤ U^(v+boxWidth)*(C*U) := by gcongr
      _ = _ := by ring
  have hpow : U^(1-y+v+boxWidth)*U^y = U^(v+boxWidth)*U := by
    rw [←Real.rpow_add hU]
    calc
      _ = U^(v+boxWidth+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one]
  have he : C*U^(1-y+v+boxWidth)*(U^y/N) =
      (C*(U^(v+boxWidth)*U))/N := by
    calc
      _ = (C*(U^(1-y+v+boxWidth)*U^y))/N := by ring
      _ = _ := by rw [hpow]
  rw [he]
  exact (le_div_iff₀ hN).mpr hprod

lemma capacity_shift_exact (y v boxWidth annulusSlack:ℝ) :
    selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth) =
      selectedCapacity ((2*y-1)/(9/2)) (v+boxWidth+annulusSlack) := by
  unfold selectedCapacity
  congr 1
  ring

/-- A positive selected family fits the reflected two-plain capacity. If the
capacity has saturated to zero, positivity forces the selected family empty. -/
theorem reflected_capacity_or_empty {ι:Type*} (T:Finset ι)
    (width:ι→ℝ) (y v boxWidth annulusSlack:ℝ)
    (hw:∀i∈T,0 < width i)
    (hselected:(∑i∈T,width i) ≤
      selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(9/2)*(∑i∈T,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(9/2)-4*annulusSlack/9-4*(v+boxWidth)/9
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth) = raw :=
      max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(9/2)*raw = 1 := by dsimp [raw]; ring
    linarith
  · right
    have he : selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth) = 0 :=
      max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun j hj=>(hw j hj).le) hi
    linarith [hw i hi]

/-- The annular tolerance changes the selected-slot exponent by exactly its
linear capacity cost; it can be included in the final small loss budget. -/
lemma annular_capacity_saving_loss (q y annulusSlack:ℝ) :
    -q*((2*y-1)/(9/2)-4*annulusSlack/9)/2 =
      -q*((2*y-1)/(9/2))/2+2*q*annulusSlack/9 := by ring


/-- A convenient uniform positive margin for the selected base capacity. -/
lemma physical_y_strong_lower (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ WeightedQRH.h+WeightedQRH.rowExtension) :
    (11/20:ℝ) < WeightedQRH.ly/d := by
  have hdp : 0 < d := by linarith
  apply (lt_div_iff₀ hdp).mpr
  norm_num [WeightedQRH.h,WeightedQRH.rowExtension,WeightedQRH.ly] at *
  linarith

lemma shifted_base_capacity_pos (d annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ WeightedQRH.h+WeightedQRH.rowExtension)
    (hann:annulusSlack ≤ 1/100) :
    0 < (2*(WeightedQRH.ly/d)-1)/(9/2)-4*annulusSlack/9 := by
  have hh := physical_y_strong_lower d hd hdmax
  linarith

def coefficientBoxCount (xi:ℝ) : ℕ := ⌈1/xi⌉₊

lemma coefficientBoxCount_extent (xi:ℝ) (hxi:0 < xi) :
    1 ≤ (coefficientBoxCount xi:ℝ)*xi ∧
      (coefficientBoxCount xi:ℝ)*xi < 1+xi := by
  have hlo := Nat.le_ceil (1/xi)
  have hhi := Nat.ceil_lt_add_one (by positivity:(0:ℝ) ≤ 1/xi)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlo hxi.le
    simpa only [coefficientBoxCount,div_mul_cancel₀ _ hxi.ne'] using hh
  · have hh := mul_lt_mul_of_pos_right hhi hxi
    dsimp [coefficientBoxCount]
    simpa only [add_mul,div_mul_cancel₀ _ hxi.ne',one_mul] using hh

lemma coefficient_box_index_range (xi:ℝ) (hxi:0 < xi) (j:ℕ)
    (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ (j:ℝ)*xi ∧ (j:ℝ)*xi ≤ 1+xi := by
  have hjn : j ≤ coefficientBoxCount xi := by have := Finset.mem_range.mp hj; omega
  have hjr : (j:ℝ) ≤ (coefficientBoxCount xi:ℝ) := by exact_mod_cast hjn
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hxi.le,
    (mul_le_mul_of_nonneg_right hjr hxi.le).trans (coefficientBoxCount_extent xi hxi).2.le⟩

/-- A fixed source cutoff fits below U uniformly in every weighted high dyad. -/
theorem eventually_physical_cutoff_le_base (b:ℝ) (hb:0 ≤ b) :
    ∀ᶠU:ℝ in Filter.atTop, 1 < U ∧ ∀d:ℝ,(1/2:ℝ) ≤ d →
      b*U^(WeightedQRH.ly/d) ≤ U := by
  have he : ∀ᶠU:ℝ in Filter.atTop, b ≤ U^(81/1000:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<81/1000)).eventually (Filter.eventually_ge_atTop _)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0 < d := by linarith
  have hy : WeightedQRH.ly/d ≤ 919/1000 := by
    apply (div_le_iff₀ hdp).mpr
    norm_num [WeightedQRH.ly] at *
    linarith
  calc
    _ ≤ U^(81/1000:ℝ)*U^(919/1000:ℝ) := by
      exact mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hU.le hy)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by
      rw [←Real.rpow_add (zero_lt_one.trans hU)]
      norm_num

/-- The finite box range and the reflected scale range use the same actual
parameters; no unbounded coefficient tail remains after the source cutoff. -/
theorem physical_coefficient_box_geometry (d xi annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ WeightedQRH.h+WeightedQRH.rowExtension)
    (hxi:0 < xi) (hann:0 ≤ annulusSlack) (hsmall:2*xi+annulusSlack ≤ 1/2)
    (j:ℕ) (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ 1-WeightedQRH.ly/d+(j:ℝ)*xi+xi ∧
      (1-WeightedQRH.ly/d+(j:ℝ)*xi+xi)+annulusSlack ≤ 2 := by
  obtain ⟨hv,hvmax⟩ := coefficient_box_index_range xi hxi j hj
  exact reflected_box_geometry d ((j:ℝ)*xi) xi annulusSlack hd hdmax hv hvmax hxi.le hann hsmall


lemma reflected_capacity_or_empty_subtype {ι:Type*} (T:Finset ι)
    (width:T→ℝ) (y v boxWidth annulusSlack:ℝ)
    (hw:∀i,0 < width i)
    (hselected:(∑i,width i) ≤
      selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(9/2)*(∑i,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(9/2)-4*annulusSlack/9-4*(v+boxWidth)/9
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth) = raw := max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(9/2)*raw = 1 := by dsimp [raw]; ring
    linarith
  · right
    have he : selectedCapacity ((2*y-1)/(9/2)-4*annulusSlack/9) (v+boxWidth) = 0 := max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

end WeightedQRH.Numerator
