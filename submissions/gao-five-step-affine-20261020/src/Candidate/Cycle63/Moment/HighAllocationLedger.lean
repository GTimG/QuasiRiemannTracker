import Candidate.Cycle63.Physical.AllocationClipping
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile
open CenteredMomentAllocatedChildCapacity CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact total width of the final positive row, with the two clipped plains
and only live slots. Both pre- and post-clipping losses remain in the actual
reduction; frozen original slots are charged exactly once. -/
theorem actual_high_allocation_total
    (Z : ℝ) (hZ : 1 < Z) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (P : ι → ℝ) (hP : ∀ i, 0 < P i) :
    (∑ j, Real.logb Z (clippedScale (Cycle63.Physical.postPlainScale L a X j)))+
      (∑ i ∈ liveIndices L a, Real.logb Z (P i)) =
    (∑ j, Real.logb Z (clippedScale (X j)))+(∑ i, Real.logb Z (P i))-
      Cycle63.Physical.clippedReduction (Real.logb Z (formalReductionFactor L a P))
        (fun j => Real.logb Z (X j)) (Cycle63.Physical.actualPlainReduction Z L a) := by
  have hraw := raw_log_volume L a Z (X 0) (X 1) (hX 0) (hX 1) P hP
  have hpre : Real.logb Z (X 0*X 1*∏ i,P i) =
      Real.logb Z (X 0)+Real.logb Z (X 1)+(∑ i, Real.logb Z (P i)) := by
    rw [Real.logb_mul (mul_pos (hX 0) (hX 1)).ne'
      (Finset.prod_pos (fun i _ => hP i)).ne',
      Real.logb_mul (hX 0).ne' (hX 1).ne',Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  rw [hpre] at hraw
  have hc (j : Fin 2) := clipped_log Z (X j) hZ (hX j)
  have hp (j : Fin 2) := clipped_log Z (Cycle63.Physical.postPlainScale L a X j)
    hZ (Cycle63.Physical.postPlainScale_pos L a X hX j)
  simp only [Cycle63.Physical.postPlainScale_log Z L a X hX] at hp
  simp only [Fin.sum_univ_two]
  rw [hp 0,hp 1,hc 0,hc 1]
  unfold Cycle63.Physical.clippedReduction Cycle63.Physical.negativeTotal
  simp only [Fin.sum_univ_two,max_comm (0 : ℝ)]
  change Real.logb Z (rawScale L a (X 0) 0)+
    Real.logb Z (rawScale L a (X 1) 1)+remainingLogs L a Z P = _ at hraw
  change Real.logb Z (X 0)-Cycle63.Physical.actualPlainReduction Z L a 0+
    max (-(Real.logb Z (X 0)-Cycle63.Physical.actualPlainReduction Z L a 0)) 0+
    (Real.logb Z (X 1)-Cycle63.Physical.actualPlainReduction Z L a 1+
      max (-(Real.logb Z (X 1)-Cycle63.Physical.actualPlainReduction Z L a 1)) 0)+
    remainingLogs L a Z P = _
  have hr (j : Fin 2) : Real.logb Z (rawScale L a (X j) j) =
      Real.logb Z (X j)-Cycle63.Physical.actualPlainReduction Z L a j :=
    Cycle63.Physical.postPlainScale_log Z L a X hX j
  rw [hr 0,hr 1] at hraw
  linarith

/-- The high-bin pointwise exponent is the literal pre-allocation total minus
its actual clipped reduction. No bound on residual projector divisibility is
used in this identity. -/
theorem actual_high_allocation_exponent
    (Z : ℝ) (hZ : 1 < Z) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (w : ι → ℝ) (d : ℝ) (r : Fin 2 → ℝ)
    (hscale : ∀ j, clippedScale (Cycle63.Physical.postPlainScale L a X j) = (Z^d)^(r j)) :
    d*(r 0+r 1)+(∑ i ∈ liveIndices L a, w i) =
      (∑ j, Real.logb Z (clippedScale (X j)))+(∑ i, w i)-
        Cycle63.Physical.clippedReduction
          (Real.logb Z (formalReductionFactor L a (fun i => Z^(w i))))
          (fun j => Real.logb Z (X j)) (Cycle63.Physical.actualPlainReduction Z L a) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hh := actual_high_allocation_total Z hZ L a X hX (fun i => Z^(w i))
    (fun _ => Real.rpow_pos_of_pos hZp _)
  have hr (j : Fin 2) :
      Real.logb Z (clippedScale (Cycle63.Physical.postPlainScale L a X j)) = d*r j := by
    rw [hscale j,←Real.rpow_mul hZp.le,Real.logb_rpow hZp hZ.ne']
  simp_rw [Real.logb_rpow hZp hZ.ne',hr] at hh
  simpa only [Fin.sum_univ_two,mul_add] using hh

end
end OAI.SevenEighths.Cycle63Moment
