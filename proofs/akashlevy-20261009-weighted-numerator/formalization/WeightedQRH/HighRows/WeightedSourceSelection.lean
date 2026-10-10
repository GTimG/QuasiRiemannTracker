import WeightedQRH.HighRows.WeightedSourcePrimeBins
import WeightedQRH.HighRows.WeightedSlotSelection

/-! A single selected prime subset for every row in an actual full amplitude
class, with only the numerator's error slots masked out of the lower mean. -/
noncomputable section
open scoped Classical BigOperators
namespace WeightedQRH
open OAI OAI.SevenEighths HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily ProbeFinalAssembly
open ProbePhysical HeckeFamily HeckeInverseAmplification

 theorem masked_main_product_upper {α : Type*} [Fintype α] [DecidableEq α]
    (main : Finset α) (width g : α→ℝ) (U mesh : ℝ) (Q : α→ℂ)
    (hU : 1 ≤ U) (hm : 0 ≤ mesh) (hw : ∀j,0 ≤ width j)
    (hL : 0 < ∑j,width j)
    (hQ : ∀j∈main,‖Q j‖ ≤ U^(width j*(g j+mesh))) :
    ‖∏j∈main,Q j‖ ≤ U^(weightedMean Finset.univ width (maskedGain main g)*(∑j,width j)+
      mesh*(∑j,width j)) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have he : (∑j,width j*maskedGain main g j)=∑j∈main,width j*g j := by
    calc
      _ = ∑j∈main,width j*maskedGain main g j :=
        (Finset.sum_subset (Finset.subset_univ main) (fun j _ hj=>by simp [maskedGain,hj])).symm
      _ = _ := Finset.sum_congr rfl (fun j hj=>by simp [maskedGain,hj])
  have hmean : weightedMean Finset.univ width (maskedGain main g)*(∑j,width j)=
      ∑j∈main,width j*g j := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne',he]
  have hsum : ∑j∈main,width j ≤ ∑j,width j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ main) (fun j _ _=>hw j)
  calc
    _ ≤ ∏j∈main,U^(width j*(g j+mesh)) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) hQ
    _ = U^(∑j∈main,width j*(g j+mesh)) := (Real.rpow_sum_of_pos hUpos _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hU
      rw [hmean]
      have hh := mul_le_mul_of_nonneg_left hsum hm
      have he' : (∑j∈main,width j*(g j+mesh))=
          (∑j∈main,width j*g j)+mesh*(∑j∈main,width j) := by
        rw [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [he']
      linarith

/-- Exact identification of the source-count physical family with canonical
prime amplitudes at the original physical slot lengths. -/
theorem source_count_physical_eq {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z d : ℝ) (hZ : 0 < Z) (hd : d≠0)
    (z : ℂ) (u : FreeRow) (j : Fin D.N) :
    physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ)) (fun _=>2)
      (fun j=>D.ell j/d) (fun _=>z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z := by
  calc
    _ = HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val (fun y=>(F.w y:ℂ)) 2 (Z^(D.ell j)) z :=
      source_physical_amplitude F.modulus ⊤ D.ell (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
    _ = _ := by
      congr 1
      funext y
      exact (F.complex_eq y).symm

/-- Common selection on a canonical full amplitude class. The analytic upper
premise is supplied by weighted_source_prime_bins; lower spikes are automatic. -/
theorem source_class_main_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData)
    (hfine : ∀j,D.ell j ≤ ProbeFinalAssemblyCertifiedBands.weighted_detectorMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.ell j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.ell j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=>D.ell j/d) (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧ ∃selected : Finset (Fin D.N),selected⊆main ∧
      (∑j∈selected,D.ell j/d) ≤ WeightedSlotSelection.reflectedCapacity d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*WeightedSlotSelection.reflectedCapacity d v-
          δ*ProbeFinalAssemblyCertifiedBands.weighted_detectorMesh D.t) ≤ ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t)) →
          ‖∏j∈main,Q u j‖ ≤ (Z^d)^(q*(ell/d)+D.t*(ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.ell j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0 ≤ g j ∧ g j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    WeightedSlotSelection.highData_weighted_selection D hfine d v δ hd hv hδ main
      (maskedGain main g) hg (fun j hj=>by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.ell j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.ell j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_bounds j).1 hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum];rfl
    have hh := masked_main_product_upper main (fun j=>D.ell j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_bounds j).1 hdpos).le)
      (by rw [hL];exact div_pos ell_pos hdpos) (by
        intro j hj
        calc
          _ ≤ (Z^(D.ell j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh


/-- The positive real square root of the selected squared spike. -/
theorem squared_selected_lower (U q cap δ mesh : ℝ) (Q : ℂ) (hU : 0 < U)
    (hQ : U^(2*q*cap-δ*mesh) ≤ ‖Q‖^2) :
    U^(q*cap-δ*mesh/2) ≤ ‖Q‖ := by
  apply (sq_le_sq₀ (Real.rpow_nonneg hU.le _) (norm_nonneg _)).mp
  have he : (U^(q*cap-δ*mesh/2))^2=U^(2*q*cap-δ*mesh) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    ring
  rwa [he]

/-- Main-product upper slack depends on the original class and main mask only,
and is independent of the subset selected for any particular dilation box. -/
theorem amplitude_class_main_upper {Row Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rows : Finset Row) (main : Finset Slot) (U δ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : BinLabel (Finset.univ : Finset Slot) (δ/2) mesh)
    (u : Row)
    (hu : u∈amplitudeRows rows Finset.univ U (δ/2) mesh hm width Q bin)
    (hU : 1 ≤ U) (hw : ∀j,0 ≤ width j) (hL : 0 < ∑j,width j)
    (hupper : ∀j∈main,‖Q u j‖ ≤ (U^(width j))^
      (HeckePrimeAmplitudeBins.amplitude (U^(width j)) (δ/2) mesh (Q u j)+mesh)) :
    ‖∏j∈main,Q u j‖ ≤ U^(weightedMean Finset.univ width
      (maskedGain main (binValue Finset.univ (δ/2) mesh bin))*(∑j,width j)+mesh*(∑j,width j)) := by
  apply masked_main_product_upper main width _ U mesh (Q u) hU hm.le hw hL
  intro j hj
  have he := amplitude_class_value rows Finset.univ U (δ/2) mesh hm width Q bin u hu j (Finset.mem_univ j)
  have hh := hupper j hj
  rw [he,←Real.rpow_mul (zero_le_one.trans hU)] at hh
  exact hh

/-- Every subset of source slots satisfies the crude selected-product cutoff
required when discarding the Fourier tail. -/
theorem source_selected_product_crude {Δ : ℝ} (D : HighParameters.HighData Δ)
    (Z d δ : ℝ) (hZ : 1 < Z) (hd : 1/2 ≤ d) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N→ℂ)
    (hQ : ∀j,‖Q j‖ ≤ (Z^(D.ell j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖ ≤ Z^d := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have ht := D.t_pos
  have hlength : ∑j∈selected,D.ell j ≤ (167/1000:ℝ) := by
    rw [←D.slots_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun j _ _=>(D.slots_bounds j).1.le)
  calc
    _ ≤ ∏j∈selected,Z^(D.ell j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=>norm_nonneg _)
      intro j hj
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds
        (Z^(D.ell j)) (δ/2) D.t (Q j) (by positivity)).2
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      exact mul_le_mul_of_nonneg_left (by linarith :
        HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q j)+D.t ≤ δ/2+D.t)
        (D.slots_bounds j).1.le
    _ = Z^((∑j∈selected,D.ell j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _ ≤ Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hh := mul_le_mul_of_nonneg_right hlength
        (by positivity : 0 ≤ δ/2+D.t)
      nlinarith only [hh,hδ',D.t_small,hd]

end WeightedQRH
end
