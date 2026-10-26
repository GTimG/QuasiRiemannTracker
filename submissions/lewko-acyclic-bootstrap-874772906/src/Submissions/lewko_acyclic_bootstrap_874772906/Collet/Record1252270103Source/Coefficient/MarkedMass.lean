/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Absolute finite marked-tuple mass for the literal canonical Input. This is a
pointwise triangle estimate, not contraction of a completed projected norm. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedFixedInducing
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorAmplitude
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCounting
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem input_slot_absolute_mass (s : Input ι) (i : ι) :
    (∑I∈s.slots i,‖s.toData.coefficient i I‖)≤128*max 0 (s.hi i)*s.M i*s.P i := by
  let f : Ideal O→ℂ := fun I=>if I∈s.slots i then (‖s.toData.coefficient i I‖:ℂ) else 0
  have h0 : f 0=0 := by
    have hz : (0:Ideal O)∉s.slots i := fun h=>(s.prime i 0 h).ne_zero rfl
    simp only [f,ite_eq_right hz]
  have hnorm (I : Ideal O) : ‖f I‖≤s.M i := by
    by_cases hI : I∈s.slots i
    · simpa only [f,ite_eq_left hI,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),Data.coefficient]
        using s.coefficient_bound i I hI
    · simpa only [f,ite_eq_right hI,norm_zero] using zero_le_one.trans (s.M_ge_one i)
  have hsup (I : Ideal O) (hI : f I≠0) : (I.absNorm:ℝ)≤max 0 (s.hi i)*s.P i := by
    have hβ : s.toData.coefficient i I≠0 := by
      intro hz
      exact hI (by simp only [f,hz,norm_zero,Complex.ofReal_zero,ite_self])
    exact coefficient_support s.toData i I hβ
  have hb := norm_tsum_ideal_ball f (max 0 (s.hi i)*s.P i) (s.M i)
    (mul_nonneg (le_max_left _ _) (s.P_pos i).le) (zero_le_one.trans (s.M_ge_one i)) h0 hnorm hsup
  have he : (∑'I,f I)=(((∑I∈s.slots i,‖s.toData.coefficient i I‖):ℝ):ℂ) := by
    rw [tsum_eq_sum (s:=s.slots i) (fun I hI=>by simp only [f,ite_eq_right hI])]
    simp only [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun I hI=>by simp only [f,ite_eq_left hI])
  rw [he,Complex.norm_real,Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))] at hb
  exact hb.trans_eq (by ring)

theorem input_marked_absolute_mass (s : Input ι) :
    (∑v : (∀i,s.slots i),∏i,‖s.toData.coefficient i (v i)‖)≤
      slotControl s.toData*(∏i,s.P i) := by
  rw [←Fintype.prod_sum (fun i (I : s.slots i)=>‖s.toData.coefficient i I‖)]
  have he (i : ι) : (∑I : s.slots i,‖s.toData.coefficient i I‖)=
      ∑I∈s.slots i,‖s.toData.coefficient i I‖ :=
    Finset.sum_coe_sort (s.slots i) (fun I=>‖s.toData.coefficient i I‖)
  simp_rw [he]
  have hp : (∏i,∑I∈s.slots i,‖s.toData.coefficient i I‖)≤
      (∏i,128*max 0 (s.hi i)*s.M i)*(∏i,s.P i) := by
    rw [←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun i _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      (fun i _=>input_slot_absolute_mass s i)
  apply hp.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i _=>(s.P_pos i).le))
  have hf : (1:ℝ)≤∏i,s.M i := by
    simpa using (Finset.prod_le_prod₀ (s:=Finset.univ)
      (f:=fun _ : ι=>(1:ℝ)) (g:=s.M) (fun _ _=>zero_le_one) (fun i _=>s.M_ge_one i))
  have hg : (∏i,128*max 0 (s.hi i)*s.M i)≤∏i,max 1 (128*max 0 (s.hi i)*s.M i) :=
    Finset.prod_le_prod₀ (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
      (zero_le_one.trans (s.M_ge_one i))) (fun i _=>le_max_right _ _)
  have hh := mul_le_mul_of_nonneg_right hf
    (Finset.prod_nonneg (s:=Finset.univ) (fun i _=>zero_le_one.trans (le_max_left (1:ℝ) (128*max 0 (s.hi i)*s.M i))))
  simp only [one_mul] at hh
  exact hg.trans hh

theorem input_marked_triangle (s : Input ι) (K : Ideal O) (ψ : Ideal O→*₀ℂ)
    (hψ : ∀I,‖ψ I‖≤1) (f : (∀i,s.slots i)→ℂ) (E : ℝ) (hE : 0≤E)
    (hf : ∀v,‖f v‖≤E) :
    ‖∑v : (∀i,s.slots i),QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*(∏i,(v i:Ideal O)))*
      (∏i,s.toData.coefficient i (v i))*ψ (∏i,(v i:Ideal O))*f v‖≤
      E*slotControl s.toData*(∏i,s.P i) := by
  have hs (I : Ideal O) : ‖QRH.Record1252270103TwoIdeal.squarefreeIndicator I‖≤1 := by
    by_cases h : Squarefree I <;> simp [QRH.Record1252270103TwoIdeal.squarefreeIndicator,h]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑v : (∀i,s.slots i),(∏i,‖s.toData.coefficient i (v i)‖)*E := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul,norm_mul,norm_mul,norm_prod]
      apply mul_le_mul _ (hf v) (norm_nonneg _) (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (by positivity)) (hψ _)).trans
        (mul_le_of_le_one_left (by positivity) (hs _))
    _=(∑v : (∀i,s.slots i),∏i,‖s.toData.coefficient i (v i)‖)*E := (Finset.sum_mul _ _ _).symm
    _≤_ := (mul_le_mul_of_nonneg_right (input_marked_absolute_mass s) hE).trans_eq (by ring)

theorem input_marked_triangle_nonzero (s : Input ι) (K : Ideal O) (ψ : Ideal O→*₀ℂ)
    (hψ : ∀I,‖ψ I‖≤1) (f : (∀i,s.slots i)→ℂ) (E : ℝ) (hE : 0≤E)
    (hf : ∀v,ψ (∏i,(v i:Ideal O))≠0→‖f v‖≤E) :
    ‖∑v : (∀i,s.slots i),QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*(∏i,(v i:Ideal O)))*
      (∏i,s.toData.coefficient i (v i))*ψ (∏i,(v i:Ideal O))*f v‖≤
      E*slotControl s.toData*(∏i,s.P i) := by
  let g : (∀i,s.slots i)→ℂ := fun v=>if ψ (∏i,(v i:Ideal O))=0 then 0 else f v
  have hg : ∀v,‖g v‖≤E := by
    intro v
    by_cases h : ψ (∏i,(v i:Ideal O))=0
    · simpa only [g,ite_eq_left h,norm_zero] using hE
    · simpa only [g,ite_eq_right h] using hf v h
  have he : (∑v : (∀i,s.slots i),QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*(∏i,(v i:Ideal O)))*
      (∏i,s.toData.coefficient i (v i))*ψ (∏i,(v i:Ideal O))*f v)=
      ∑v : (∀i,s.slots i),QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*(∏i,(v i:Ideal O)))*
      (∏i,s.toData.coefficient i (v i))*ψ (∏i,(v i:Ideal O))*g v := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : ψ (∏i,(v i:Ideal O))=0
    · simp only [h,mul_zero,zero_mul]
    · simp only [g,ite_eq_right h]
  rw [he]
  exact input_marked_triangle s K ψ hψ g E hE hg

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.input_marked_absolute_mass
#print axioms OAI.SevenEighths.Record1252270103Source.input_marked_triangle

#print axioms OAI.SevenEighths.Record1252270103Source.input_marked_triangle_nonzero
