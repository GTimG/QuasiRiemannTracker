import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ClippedProjectorShell
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentEligibleEnergy CenteredMomentExceptionalMaskedSource
open CenteredMomentActiveDivisorShell
open CenteredMomentExceptionalAmplitudePair CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def retainedAllocationCost (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℝ :=
  ((2*(max 1 s.b₁*max 1 s.b₂))*(∏ i ∈ frozenIndices L a, s.M i)^2 /
    formalReductionFactor L a s.P)*
    (‖Cycle63.Physical.sourcePositiveRow s.toSource false L a z‖^2+
     ‖Cycle63.Physical.sourcePositiveRow s.toSource true L a z‖^2)

theorem retained_allocation_cost_nonneg (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    0 ≤ retainedAllocationCost s L a z := by
  unfold retainedAllocationCost
  exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (s.reduction_pos L a).le) (add_nonneg (sq_nonneg _) (sq_nonneg _))

def RetainedPointwiseBound (ι : Type*) [Fintype ι] [DecidableEq ι]
    (C ε : ℝ) : Prop :=
  ∀ (s : Data ι) (L : Ideal O), Squarefree L → ∀ z : O,
    ‖maskedAmplitude s L z‖^2 ≤ C*(L.absNorm:ℝ)^ε*
      ∑ a ∈ s.toSource.active L, retainedAllocationCost s L a z

theorem actual_retained_pointwise (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ RetainedPointwiseBound ι C ε := by
  obtain ⟨C,hC,hbound⟩ := active_raw_to_retained_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s L hL z
  have hh := hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i => zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound L hL
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product
    {z} (fun _ => 1) (by intros; norm_num)
  have hc : s.coefficient = (fun i I => s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) := rfl
  rw [hc] at hh
  unfold maskedAmplitude
  rw [hc]
  simpa only [Finset.sum_singleton, one_mul, maskedAmplitude, volume,
    retainedAllocationCost, Cycle63.Physical.sourcePositiveRow,
    Cycle63.Physical.sourcePlainScales, ite_false, ite_true,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Bool.false_eq_true,
    Source.active,
    CenteredMomentEligibleEnergy.Data.coefficient] using hh

theorem uniform_retained_pointwise (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : Finset ι, RetainedPointwiseBound J C ε := by
  have he (J : Finset ι) : ∃ C : ℝ, 0 < C ∧ RetainedPointwiseBound J C ε :=
    actual_retained_pointwise (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D := 1+∑ J : Finset ι, C J
  have hs : 0 ≤ ∑ J : Finset ι, C J := Finset.sum_nonneg (fun J _ => (hC J).le)
  refine ⟨D,by dsimp only [D]; linarith,?_⟩
  intro J s L hL z
  have hd : C J ≤ D := by
    have hh := Finset.single_le_sum (fun J _ => (hC J).le) (Finset.mem_univ J)
    dsimp only [D]
    linarith
  exact (hb J s L hL z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Finset.sum_nonneg (fun a _ => retained_allocation_cost_nonneg s L a z)))

def commonRetainedCost (s : Input ι) (C R L : Ideal O) (z : O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    ∑ B : actualAllocations s.pools C, ‖commonScalar s C R B‖^2*
      ∑ a ∈ (commonData s C R B).toSource.active L,
        retainedAllocationCost (commonData s C R B) L a z

theorem common_retained_cost_nonneg (s : Input ι) (C R L : Ideal O) (z : O) :
    0 ≤ commonRetainedCost s C R L z := by
  unfold commonRetainedCost
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun B _ =>
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun a _ =>
      retained_allocation_cost_nonneg _ _ _ _))))

/-- Both extraction steps are performed on the literal column. No uniform
per-label child envelope has been taken at this stage. -/
theorem actual_common_column_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Input ι) (C : Ideal O) (hC : Supported C)
      (R seed L : Ideal O), seed ∣ C → Squarefree L → ∀ z : O,
      ‖normalizedColumn s C hC R seed L z‖^2 ≤
        K*(L.absNorm:ℝ)^ε*commonRetainedCost s C R L z := by
  obtain ⟨K,hK,hbound⟩ := uniform_retained_pointwise (ι := ι) ε hε
  refine ⟨K,hK,?_⟩
  intro s C hC R seed L hseed hL z
  have hh := CubicEisenstein.norm_sum_sq_le_card
    (Finset.univ : Finset (actualAllocations s.pools C))
    (fun B => commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)
  rw [←source_normalized s C hC R seed L hseed z] at hh
  change ‖normalizedColumn s C hC R seed L z‖^2 ≤ _ at hh
  simp only [Finset.card_univ, Fintype.card_coe, norm_mul, mul_pow] at hh
  apply hh.trans
  calc
    _ ≤ ((actualAllocations s.pools C).card:ℝ)*
        ∑ B : actualAllocations s.pools C, ‖commonScalar s C R B‖^2*
          (K*(L.absNorm:ℝ)^ε*
            ∑ a ∈ (commonData s C R B).toSource.active L,
              retainedAllocationCost (commonData s C R B) L a z) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left
        (hbound (liveIndices B.val) (commonData s C R B) L hL z) (sq_nonneg _))
    _ = _ := by
      unfold commonRetainedCost
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun B hB => Finset.sum_congr rfl fun a ha => ?_
      ring

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
