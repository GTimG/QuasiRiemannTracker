/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighFixedIntegral.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighDyadIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.FixedIntegral

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem continuedPhysicalRowKernel_integrable_on_perturbed_boundary {K : ℕ}
    (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (boundary : ℝ) ≤ σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : HeightSpace=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let W : Fin K→ℝ→ℂ := fun _ y=>if y=1 then 1 else 0
  let Yp : Fin K→ℝ := fun i=>(P i).val.absNorm
  let T : Fin K→Finset PrimeIdeal := fun i=>{P i}
  have hT (i : Fin K) (Q : PrimeIdeal) (hQ : Q∈T i) : Q.val∉S := by
    have heq : Q=P i := Finset.mem_singleton.mp hQ
    simpa only [heq] using hPS i
  let P0 : ∀i,T i := fun i=>⟨P i,Finset.mem_singleton_self _⟩
  have hTP (Q : ∀i,T i) : (fun i=>(Q i).val)=P := by
    funext i
    exact Finset.mem_singleton.mp (Q i).property
  have hdis (Q : ∀i,T i) : Function.Injective (fun i=>(Q i).val) := by rw [hTP Q];exact hP
  have hYp (i : Fin K) : 1≤Yp i := by
    dsimp [Yp]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  have hWS (i : Fin K) : Function.support (W i)⊆Icc (1:ℝ) 1 := by
    intro y hy
    by_cases h : y=1
    · simpa only [h] using (show (1:ℝ)∈Icc 1 1 from ⟨le_rfl,le_rfl⟩)
    · simp [W,h,Function.mem_support] at hy
  have hWB (i : Fin K) (y : ℝ) : ‖W i y‖≤1 := by dsimp [W];split_ifs <;> simp
  have hWeq (i : Fin K) : W i (((P i).val.absNorm:ℝ)/Yp i)=1 := by
    have hn : Yp i≠0 := by linarith [hYp i]
    simp [W,Yp,div_self hn]
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  have hU : 1≤U := by
    dsimp [U]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral_on_perturbed_boundary K e (1/2) 1 1 r 1 σ υ he he'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by norm_num) hσ hσβ hυ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hR (v : FreeRow) (hv : v∈({u}:Finset FreeRow)) :
      v.val≠1 ∧ U≤((Ideal.span {v.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {v.val}:Ideal O).absNorm:ℝ)≤2*U := by
    have hvu := Finset.mem_singleton.mp hv
    subst v
    exact ⟨hu,le_rfl,by change U≤2*U;linarith⟩
  have hi := (hmain η U hU {u} hR T hT hdis Yp hYp W hWS hWB X Y Z hX hY hZ).1
  have hm := calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u P hPS W Yp σ υ r heightMeasure
  have hfn : (elementNorm u.val:ℂ)≠0 := by
    exact_mod_cast (elementNorm_pos u.val u.property.1).ne'
  have hf : Continuous (fun p : HeightSpace=>frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩) := by
    unfold frequencyWeight
    exact (by fun_prop : Continuous (fun p : HeightSpace=>-((r:ℂ)+p.1.2*Complex.I))).const_cpow (Or.inl hfn)
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  have hme : AEStronglyMeasurable (fun p : HeightSpace=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
    simp_rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
    exact (hs.mul hf).aestronglyMeasurable.mul hm
  apply hi.mono' hme
  apply Filter.Eventually.of_forall
  intro p
  rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
  rw [mul_assoc,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  dsimp only [physicalDyadNorm]
  rw [Finset.sum_singleton]
  have hh := Finset.single_le_sum (fun Q (_ : Q∈(Finset.univ:Finset (∀i,T i)))=>norm_nonneg
    (frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩*
      calibratedTupleValue S hS hmax η u (fun i=>(Q i).val)
        (fun i=>hT i (Q i).val (Q i).property) W Yp ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I))) (Finset.mem_univ P0)
  exact hh


end SevenEighths.ProbeHighRowFamily
end

end OAI
