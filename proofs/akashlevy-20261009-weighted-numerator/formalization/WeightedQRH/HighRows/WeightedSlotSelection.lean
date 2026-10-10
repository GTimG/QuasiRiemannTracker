import WeightedQRH.HighRows.HighDataFine
import WeightedQRH.MomentSourceMoments
import OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection
import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/-!
Greedy prime-slot selection for the reflected numerator. Error slots have gain zero,
but retain their lengths in the denominator of q. No amplitude frontier is assumed.
-/
noncomputable section
open scoped Classical BigOperators
namespace WeightedQRH.WeightedSlotSelection
open OAI.SevenEighths
open HeckeDetectorSlotSelection HeckeDetectorPhysicalSelection
open ProbeFinalAssemblyCertifiedBands

def baseCapacity (d : ℝ) : ℝ := (2*ly/d-1)/(6*kappa)
def reflectedCapacity (d v : ℝ) : ℝ := max 0 (baseCapacity d-4*v/9)

theorem reflectedCapacity_nonneg (d v : ℝ) : 0 ≤ reflectedCapacity d v := le_max_left _ _

theorem baseCapacity_lt_supply {d : ℝ} (hd : (1/2:ℝ) ≤ d) : baseCapacity d < ell/d := by
  have hd0 : 0 < d := by linarith only [hd]
  have hh := div_lt_div_of_pos_right (numerator_supply_all hd) hd0
  have heq : ((2*ly-d)/(6*kappa))/d = baseCapacity d := by
    unfold baseCapacity
    norm_num [kappa]
    field_simp
    <;> ring
  rwa [heq] at hh

theorem reflectedCapacity_le_supply {d v : ℝ} (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) :
    reflectedCapacity d v ≤ ell/d := by
  apply max_le
  · exact div_nonneg ell_pos.le (by linarith only [hd])
  · have hh := baseCapacity_lt_supply hd
    linarith only [hh,hv]

theorem reflectedCapacity_gain {d v q : ℝ} (hq : 0 ≤ q) :
    q*baseCapacity d-4*q*v/9 ≤ q*reflectedCapacity d v := by
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (baseCapacity d-4*v/9)) hq
  dsimp [reflectedCapacity]
  nlinarith only [hh]

/-- Exact selection from a main mask. Zero-gain error slots remain in the mean's
normalizing sum, and are excluded only from the selected product. -/
theorem zero_error_whole_slots {α : Type*} (slots main : Finset α) (w g : α→ℝ)
    (δ mesh z : ℝ) (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh)
    (hw : ∀i∈slots,0 ≤ w i) (hwm : ∀i∈slots,w i ≤ mesh)
    (hL : 0 < ∑i∈slots,w i)
    (hg : ∀i∈slots,0 ≤ g i ∧ g i ≤ δ/2)
    (herror : ∀i∈slots,i∉main → g i=0)
    (hz : 0 ≤ z) (hzL : z ≤ ∑i∈slots,w i) :
    ∃selected : Finset α,selected⊆slots ∧ selected⊆main ∧
      (∀i∈selected,0 < g i) ∧ (∑i∈selected,w i) ≤ z ∧
      weightedMean slots w g*z-(δ/2)*mesh ≤ ∑i∈selected,w i*g i ∧
      ∀U : ℝ,1 ≤ U → ∀Q : α→ℂ,
        (∀i∈slots,0 < g i → U^(2*w i*g i) ≤ ‖Q i‖^2) →
        U^(2*weightedMean slots w g*z-δ*mesh) ≤ ‖∏i∈selected,Q i‖^2 := by
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ hw hL hg
  have hmean : weightedMean slots w g*(∑i∈slots,w i) ≤ ∑i∈slots,w i*max (g i) 0 := by
    have he : (∑i∈slots,w i*max (g i) 0)=∑i∈slots,w i*g i :=
      Finset.sum_congr rfl (fun i hi=>by rw [max_eq_left (hg i hi).1])
    rw [he]
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots slots w g (δ/2) mesh
    (by positivity) hmesh hw hwm (fun i hi=>(hg i hi).2)
    (weightedMean slots w g) z hq hqδ hz hzL hmean
  have hTm : T⊆main := by
    intro i hi
    by_contra hn
    have he := herror i (hTs hi) hn
    have hh := hTpos i hi
    rw [he] at hh
    exact lt_irrefl 0 hh
  refine ⟨T,hTs,hTm,hTpos,hTz,hgain,?_⟩
  intro U hU Q hQ
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  calc
    _ ≤ U^(∑i∈T,2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑i∈T,2*w i*g i)=2*(∑i∈T,w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith only [hgain])
    _ = ∏i∈T,U^(2*w i*g i) := Real.rpow_sum_of_pos hU0 _ _
    _ ≤ ∏i∈T,‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi=>Real.rpow_nonneg hU0.le _)
      (fun i hi=>hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem highData_weighted_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (hfine : ∀j,D.ell j ≤ weighted_detectorMesh D.t/200)
    (d v δ : ℝ) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ δ/2) (herror : ∀j,j∉main → g j=0) :
    let widths := fun j=>D.ell j/d
    let q := weightedMean Finset.univ widths g
    let mesh := weighted_detectorMesh D.t
    q = (∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ δ/2 ∧
    ∃selected : Finset (Fin D.N),selected⊆main ∧ (∀j∈selected,0 < g j) ∧
      (∑j∈selected,widths j) ≤ reflectedCapacity d v ∧
      q*reflectedCapacity d v-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      q*baseCapacity d-4*q*v/9-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      ∀U : ℝ,1 ≤ U → ∀Q : Fin D.N→ℂ,
        (∀j,0 < g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*reflectedCapacity d v-δ*mesh) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hd0 : 0 < d := by linarith only [hd]
  let widths := fun j=>D.ell j/d
  have hsum : (∑j,widths j)=ell/d := by
    dsimp [widths]
    rw [←Finset.sum_div,D.slots_sum]
    rfl
  have hL : 0 < ∑j,widths j := by rw [hsum];exact div_pos ell_pos hd0
  have hw (j : Fin D.N) : 0 ≤ widths j := (div_pos (D.slots_bounds j).1 hd0).le
  have hmesh := weighted_detectorMesh_pos D.t_pos
  have hwm (j : Fin D.N) : widths j ≤ weighted_detectorMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have hj := hfine j
    nlinarith only [hj,hd,hmesh]
  have hzL : reflectedCapacity d v ≤ ∑j,widths j := by
    rw [hsum]
    exact reflectedCapacity_le_supply hd hv
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds Finset.univ widths g δ (fun j _=>hw j) hL (fun j _=>hg j)
  obtain ⟨T,_,hT,hTpos,hTz,hgain,hspike⟩ := zero_error_whole_slots Finset.univ main widths g δ
    (weighted_detectorMesh D.t) (reflectedCapacity d v) hδ hmesh.le (fun j _=>hw j)
    (fun j _=>hwm j) hL (fun j _=>hg j) (fun j _=>herror j)
    (reflectedCapacity_nonneg d v) hzL
  refine ⟨?_,hq,hqδ,T,hT,hTpos,hTz,hgain,?_,?_⟩
  · unfold weightedMean
    rw [hsum]
  · exact (sub_le_sub_right (reflectedCapacity_gain hq) _).trans hgain
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _=>hQ j)

end WeightedQRH.WeightedSlotSelection
