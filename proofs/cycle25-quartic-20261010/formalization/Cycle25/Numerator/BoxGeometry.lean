import Cycle25.Numerator.Damping
import Cycle25.Numerator.DilationBoxes
import Cycle25.Assembly.Parameters

/-! Exact scale and capacity bookkeeping for finite coefficient-dilation boxes. -/
noncomputable section
open scoped BigOperators Classical
open Filter
namespace Cycle25.Numerator

lemma physical_y_range (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension) :
    (1/2:ℝ) < Cycle25.ly/d ∧ Cycle25.ly/d < 1 := by
  have hdp : 0 < d := by linarith
  constructor
  · apply (lt_div_iff₀ hdp).mpr
    have hh := Cycle25.extended_numerator_short
    linarith
  · apply (div_lt_one hdp).mpr
    exact Cycle25.ly_lt_half.trans_le hd

/-- The coarse finite box range suffices: the maximum reflected length remains
below the fixed L=2 empty-slot endpoint, uniformly in all actual high dyads. -/
theorem reflected_box_geometry (d v boxWidth annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hv:0 ≤ v) (hvmax:v ≤ 1+boxWidth) (hbox:0 ≤ boxWidth)
    (hann:0 ≤ annulusSlack) (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    0 ≤ 1-Cycle25.ly/d+v+boxWidth ∧
      (1-Cycle25.ly/d+v+boxWidth)+annulusSlack ≤ 2 := by
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

lemma capacity_shift_exact (kap y v boxWidth annulusSlack:ℝ) :
    selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) =
      selectedCapacity kap ((2*y-1)/(6*kap)) (v+boxWidth+annulusSlack) := by
  unfold selectedCapacity
  congr 1
  ring

/-- A positive selected family fits the reflected two-plain capacity. If the
capacity has saturated to zero, positivity forces the selected family empty. -/
theorem physical_reflected_capacity_or_empty {ι:Type*} (T:Finset ι)
    (width:ι→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0<kap)
    (hw:∀i∈T,0 < width i)
    (hselected:(∑i∈T,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i∈T,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw :=
      max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 :=
      max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun j hj=>(hw j hj).le) hi
    linarith [hw i hi]

/-- The annular tolerance changes the selected-slot exponent by exactly its
linear capacity cost; it can be included in the final small loss budget. -/
lemma annular_capacity_saving_loss (kap q y annulusSlack:ℝ) :
    -q*((2*y-1)/(6*kap)-annulusSlack/(3*kap))/2 =
      -q*((2*y-1)/(6*kap))/2+q*annulusSlack/(6*kap) := by ring


/-- A convenient uniform positive margin for the selected base capacity. -/
lemma physical_y_strong_lower (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension) :
    (11/20:ℝ) < Cycle25.ly/d := by
  have hdp : 0 < d := by linarith
  apply (lt_div_iff₀ hdp).mpr
  have hh := Cycle25.h_interval
  have hy := Cycle25.ly_coarse
  norm_num [Cycle25.rowExtension] at *
  linarith

lemma shifted_base_capacity_pos (kap d annulusSlack:ℝ)
    (hkap:0<kap) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hann:annulusSlack ≤ 1/100) :
    0 < (2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) := by
  have hh := physical_y_strong_lower d hd hdmax
  have hid : (2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) =
      (2*(Cycle25.ly/d)-1-2*annulusSlack)/(6*kap) := by ring
  rw [hid]
  exact div_pos (by linarith) (by positivity)

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
      b*U^(Cycle25.ly/d) ≤ U := by
  have he : ∀ᶠU:ℝ in Filter.atTop, b ≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).eventually (Filter.eventually_ge_atTop _)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0 < d := by linarith
  have hy : Cycle25.ly/d ≤ 19/20 := by
    apply (div_le_iff₀ hdp).mpr
    linarith [Cycle25.ly_coarse.2]
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := by
      exact mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hU.le hy)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by
      rw [←Real.rpow_add (zero_lt_one.trans hU)]
      norm_num

/-- The finite box range and the reflected scale range use the same actual
parameters; no unbounded coefficient tail remains after the source cutoff. -/
theorem physical_coefficient_box_geometry (d xi annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hxi:0 < xi) (hann:0 ≤ annulusSlack) (hsmall:2*xi+annulusSlack ≤ 1/2)
    (j:ℕ) (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ 1-Cycle25.ly/d+(j:ℝ)*xi+xi ∧
      (1-Cycle25.ly/d+(j:ℝ)*xi+xi)+annulusSlack ≤ 2 := by
  obtain ⟨hv,hvmax⟩ := coefficient_box_index_range xi hxi j hj
  exact reflected_box_geometry d ((j:ℝ)*xi) xi annulusSlack hd hdmax hv hvmax hxi.le hann hsmall


lemma physical_reflected_capacity_or_empty_subtype {ι:Type*} (T:Finset ι)
    (width:T→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0<kap)
    (hw:∀i,0 < width i)
    (hselected:(∑i,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw := max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 := max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

end Cycle25.Numerator

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
