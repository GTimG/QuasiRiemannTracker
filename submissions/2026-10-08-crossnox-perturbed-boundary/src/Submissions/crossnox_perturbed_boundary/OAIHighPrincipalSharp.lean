/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalSharp.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalWindow
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalRemainder
import Submissions.crossnox_perturbed_boundary.OAIHighFiniteProductBounds

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

def perturbedSlotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-PrincipalSlotEstimate.perturbedBoundary))*
    (128*d*B*c^(ξ-1))

lemma perturbed_slot_constant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) :
    0≤perturbedSlotConstant J c d B ξ := by
  have hd0 : 0≤d := hc.le.trans hd
  unfold perturbedSlotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=>by positivity)

theorem window_sharp_bound_on_perturbed_boundary {ι : Type*}
    (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0<P j)
    (hthreshold : ∀j∈J,480≤c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j)
    (T : ι→Finset PrimeIdeal) (s w z : ℂ)
    (hs : PrincipalSlotEstimate.perturbedBoundary≤s.re)
    (hw : 19/20≤w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      perturbedSlotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter
    (fun p=>W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : PrimeIdeal) (hp : p∈A j) :
      c*P j≤(Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj)
      (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A
        (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := ProbeFiniteProductBounds.bound_combined_slots_on_perturbed_boundary
    η S hS J A (fun j p=>W j ((Ideal.absNorm p.val:ℝ)/P j))
    480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=>
      PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
        (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
          exact_mod_cast (hmod j hj).trans_le (hA j hj p hp))))
    s w z (by simpa only [PrincipalSlotEstimate.perturbedBoundary] using hs)
    hw (by rw [hz]; exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-PrincipalSlotEstimate.perturbedBoundary))*
      ((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj
        apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun p _=>by
          exact mul_nonneg (hW j hj _).1
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left
          (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
            hc hd hB (hP j hj) (hthreshold j hj) hξ
            (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [perturbedSlotConstant,←mul_assoc,Finset.prod_mul_distrib]

end SevenEighths.ProbePrincipalRemainderBounds
end

end OAI
