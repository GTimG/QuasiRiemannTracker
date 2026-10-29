/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Extraction
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Actual complex responses, with no individual exceptional slope bound.
Only the trivial response estimate with one total error budget is used. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

private theorem word_response {ι : Type*} (J : Finset ι) (Q : ι → ℂ)
    (energy : ι → ℝ) (U : ℝ) (hU : 0<U)
    (h : ∀ i∈J,U^(energy i)=‖Q i‖^2) :
    U^(∑ i∈J,energy i)=‖∏ i∈J,Q i‖^2 := by
  rw [Real.rpow_sum_of_pos hU,norm_prod,← Finset.prod_pow]
  exact Finset.prod_congr rfl h

/-- A bounded dictionary of repetitions gives the response required by
actual inverse and plain moments. K is chosen before the finite slot type. -/
theorem bounded_response_word {ι : Type*} (J : Finset ι) (Q : ι → ℂ)
    (w error : ι → ℝ) (U δ β smin loss mesh target zmax : ℝ) (K : ℕ)
    (hU : 1<U) (hw : ∀ i∈J,0≤w i) (hwm : ∀ i∈J,w i≤mesh)
    (herr : ∀ i∈J,0≤error i) (hδ : 0≤δ) (hβ : 0<β) (hsmin : 0<smin)
    (hs : smin≤∑ i∈J,w i)
    (hupper : ∀ i∈J,‖Q i‖^2≤U^(w i+error i))
    (herrors : (∑ i∈J,error i)≤loss)
    (hlower : U^((δ+β)*(∑ i∈J,w i)-loss)≤∏ i∈J,‖Q i‖^2)
    (hbudget : 4*loss≤β*smin) (hm : 0≤mesh) (ht : 0≤target) (hmax : target≤zmax)
    (hK : zmax/(β*smin/2)+1≤(K:ℝ)) :
    ∃ (good : Finset ι) (n : ℕ) (R : Finset ι), good⊆J ∧ R⊆good ∧ n+1≤K ∧
      target-mesh≤(n:ℝ)*(∑ i∈good,w i)+(∑ i∈R,w i) ∧
      (n:ℝ)*(∑ i∈good,w i)+(∑ i∈R,w i)≤target ∧
      U^(δ*(target-mesh))≤‖(∏ i∈good,Q i)^n*(∏ i∈R,Q i)‖^2 := by
  classical
  have hUp : 0<U := zero_lt_one.trans hU
  have hpos : ∀ i∈J,0<‖Q i‖^2 := by
    intro i hi
    have hp : 0<∏ j∈J,‖Q j‖^2 := (Real.rpow_pos_of_pos hUp _).trans_le hlower
    by_contra hn
    have hz : ‖Q i‖^2=0 := le_antisymm (le_of_not_gt hn) (sq_nonneg _)
    have he := Finset.prod_eq_zero (f:=fun j => ‖Q j‖^2) hi hz
    linarith
  let energy := fun i => Real.logb U (‖Q i‖^2)
  have hpow (i : ι) (hi : i∈J) : U^(energy i)=‖Q i‖^2 :=
    Real.rpow_logb hUp hU.ne' (hpos i hi)
  have heupper : ∀ i∈J,energy i≤w i+error i := by
    intro i hi
    apply (Real.rpow_le_rpow_left_iff hU).mp
    rw [hpow i hi]
    exact hupper i hi
  have helower : (δ+β)*(∑ i∈J,w i)-loss≤∑ i∈J,energy i := by
    apply (Real.rpow_le_rpow_left_iff hU).mp
    rw [Real.rpow_sum_of_pos hUp]
    have hprod : (∏ i∈J,U^(energy i))=∏ i∈J,‖Q i‖^2 := Finset.prod_congr rfl hpow
    rwa [hprod]
  obtain ⟨good,n,R,hg,hR,hn,hlo,hhi,he⟩ := bounded_positive_repetition_all_targets
    J w energy error δ β smin loss mesh target zmax K hw hwm herr hδ hβ hsmin hs
      heupper herrors helower hbudget hm ht hmax hK
  refine ⟨good,n,R,hg,hR,hn,hlo,hhi,?_⟩
  have hgood := word_response good Q energy U hUp (fun i hi => hpow i (hg hi))
  have hlast := word_response R Q energy U hUp (fun i hi => hpow i (hg (hR hi)))
  apply (Real.rpow_le_rpow_of_exponent_le hU.le he).trans_eq
  rw [Real.rpow_add hUp]
  have hnat : U^((n:ℝ)*(∑ i∈good,energy i))=(U^(∑ i∈good,energy i))^n := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  rw [hnat,hgood,hlast,norm_mul,mul_pow,norm_pow]
  congr 1
  rw [←pow_mul,←pow_mul]
  congr 1
  omega

end
end Qrh.JointDetector.RepeatedMarks
