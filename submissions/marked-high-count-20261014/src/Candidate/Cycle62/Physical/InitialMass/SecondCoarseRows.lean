import Candidate.Cycle62.Moment.JointColumnExtraction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentInductionEnergy Cycle62Moment
local notation "O" => HeckeFamily.O
variable {ι : Type*}[Fintype ι][DecidableEq ι]

/-- Clipping cannot enlarge the right endpoint of a nonnegative support
interval. This elementary bound does not need a surviving row. -/
lemma coarse_dilated_support (W : ℝ→ℂ)(b c : ℝ)(hb : 0≤b)(hc : 1≤c)
    (hs : Function.support W⊆Set.Iic b) : Function.support (dilated W c)⊆Set.Iic b := by
  intro x hx
  change x≤b
  have hh : c*x≤b := hs hx
  by_cases hneg : x≤0
  · exact hneg.trans hb
  · have hmul := mul_le_mul_of_nonneg_right hc (le_of_not_ge hneg)
    linarith

/-- An absolute bound for each actual positive allocated row, independent
of height, character and frequency. The fixed profile suprema and the literal
remaining scales are retained explicitly for the Mellin tail estimate. -/
theorem actual_second_positive_absolute (s : Data ι)(second : Bool)
    (D : Ideal O)(alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O)(B₁ B₂ : ℝ)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (hW₁ : ∀x,‖s.W₁ x‖≤B₁)(hW₂ : ∀x,‖s.W₂ x‖≤B₂) :
    let U := fun j=>Cycle62.Physical.sourcePlainScales s.toSource second j/(selectedPlain D alloc j).absNorm
    ‖Cycle62.Physical.sourcePositiveRow s.toSource second D alloc z‖^2≤
      ((128*max 1 s.b₁*B₁)*(128*max 1 s.b₂*B₂)*
        (∏i : liveIndices D alloc,128*max 1 (s.hi i)*s.M i))^2*
        (clippedScale (U 0)*clippedScale (U 1)*∏i : liveIndices D alloc,s.P i) := by
  intro U
  have hU (j : Fin 2) : 0<U j := by
    apply div_pos
    · cases second <;> fin_cases j
      · exact s.X₁_pos
      · exact s.X₂_pos
      · exact s.Y₁_pos
      · exact s.Y₂_pos
    · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (selectedDivisor_ne_zero D Finset.univ alloc (Sum.inr j)))
  apply positive_squared_absolute (ι:=↥(liveIndices D alloc)) s.η s.m s.A z s.t
    (dilated s.W₁ (clipDilation (U 0))) (dilated s.W₂ (clipDilation (U 1)))
    (max 1 s.b₁) (max 1 s.b₂) B₁ B₂ (clippedScale (U 0)) (clippedScale (U 1))
    (by positivity) (by positivity) hB₁ hB₂
    (zero_lt_one.trans_le (clippedScale_ge_one _)) (zero_lt_one.trans_le (clippedScale_ge_one _))
    (coarse_dilated_support _ _ _ (by positivity) (clipDilation_ge_one _ (hU 0))
      (fun x hx=>show x≤max 1 s.b₁ from (s.support₁ hx).trans (le_max_right _ _)))
    (coarse_dilated_support _ _ _ (by positivity) (clipDilation_ge_one _ (hU 1))
      (fun x hx=>show x≤max 1 s.b₂ from (s.support₂ hx).trans (le_max_right _ _)))
    (fun x=>hW₁ _) (fun x=>hW₂ _) (fun i=>s.slots i)
    (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) (fun i=>s.P i)
    (fun i=>max 1 (s.hi i)) (fun i=>s.M i) (fun i=>s.P_pos i)
    (fun _=>by positivity) (fun i=>zero_le_one.trans (s.M_ge_one i))
    (fun i=>s.coefficient_bound i)
  intro i I hI hne
  have hs := (s.support i (right_ne_zero_of_mul hne)).2
  have hh := (div_le_iff₀ (s.P_pos i)).mp hs
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (s.P_pos i).le)

/-- A height-independent majorant for all allocated positive rows of one
source. It retains the two profile suprema as explicit homogeneous factors. -/
def coarseRowControl (s : Data ι)(B₁ B₂ : ℝ) : ℝ :=
  (128*max 1 s.b₁*B₁)*(128*max 1 s.b₂*B₂)*∏i,128*max 1 (s.hi i)*s.M i

def coarseRowSize (s : Data ι)(second : Bool) : ℝ :=
  max 1 (Cycle62.Physical.sourcePlainScales s.toSource second 0)*
    max 1 (Cycle62.Physical.sourcePlainScales s.toSource second 1)*∏i,max 1 (s.P i)

lemma coarse_row_size_nonneg (s : Data ι)(second : Bool) : 0≤coarseRowSize s second := by
  unfold coarseRowSize
  positivity

theorem actual_second_positive_coarse (s : Data ι)(second : Bool)
    (D : Ideal O)(alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O)(B₁ B₂ : ℝ)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (hW₁ : ∀x,‖s.W₁ x‖≤B₁)(hW₂ : ∀x,‖s.W₂ x‖≤B₂) :
    ‖Cycle62.Physical.sourcePositiveRow s.toSource second D alloc z‖^2≤
      (coarseRowControl s B₁ B₂)^2*coarseRowSize s second := by
  have hh := actual_second_positive_absolute s second D alloc z B₁ B₂ hB₁ hB₂ hW₁ hW₂
  dsimp only at hh
  have hfac (i : ι) : 1≤128*max 1 (s.hi i)*s.M i := by
    have hi := le_max_left (1:ℝ) (s.hi i)
    have hm := s.M_ge_one i
    nlinarith [mul_le_mul hi hm (by norm_num : (0:ℝ)≤1) (by linarith : 0≤max 1 (s.hi i))]
  have hprod : (∏i : liveIndices D alloc,128*max 1 (s.hi i)*s.M i)≤
      ∏i,128*max 1 (s.hi i)*s.M i := by
    rw [Finset.prod_coe_sort (liveIndices D alloc) (fun i:ι=>128*max 1 (s.hi i)*s.M i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (hfac i)) (fun i _ _=>hfac i)
  have hcoeff : 0≤(128*max 1 s.b₁*B₁)*(128*max 1 s.b₂*B₂) := by positivity
  have hc := mul_le_mul_of_nonneg_left hprod hcoeff
  have hscale (j : Fin 2) :
      clippedScale (Cycle62.Physical.sourcePlainScales s.toSource second j/(selectedPlain D alloc j).absNorm)≤
        max 1 (Cycle62.Physical.sourcePlainScales s.toSource second j) := by
    have hx : 0<Cycle62.Physical.sourcePlainScales s.toSource second j := by
      cases second <;> fin_cases j
      · exact s.X₁_pos
      · exact s.X₂_pos
      · exact s.Y₁_pos
      · exact s.Y₂_pos
    have hn : (1:ℝ)≤(selectedPlain D alloc j).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (selectedDivisor_ne_zero D Finset.univ alloc (Sum.inr j)))
    exact max_le (le_max_left _ _) ((div_le_self hx.le hn).trans (le_max_right _ _))
  have hp : (∏i : liveIndices D alloc,s.P i)≤∏i,max 1 (s.P i) := by
    calc
      _≤∏i : liveIndices D alloc,max 1 (s.P i) :=
        Finset.prod_le_prod₀ (fun i _=>(s.P_pos i).le) (fun i _=>le_max_right _ _)
      _≤_ := by
        rw [Finset.prod_coe_sort (liveIndices D alloc) (fun i:ι=>max 1 (s.P i))]
        exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>by positivity) (fun i _ _=>le_max_left _ _)
  have hfp : 0≤∏i : liveIndices D alloc,128*max 1 (s.hi i)*s.M i :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (hfac i))
  have hpp : 0≤∏i : liveIndices D alloc,s.P i := Finset.prod_nonneg (fun i _=>(s.P_pos i).le)
  apply hh.trans
  apply mul_le_mul (pow_le_pow_left₀ (mul_nonneg hcoeff hfp) hc 2)
  · exact mul_le_mul (mul_le_mul (hscale 0) (hscale 1) (by unfold clippedScale; positivity)
      (by positivity)) hp (by positivity) (by positivity)
  · unfold clippedScale; positivity
  · exact sq_nonneg _

/-- The absolute tail bound keeps the extraction divisor in the denominator.
It is uniform over both positive rectangles and all heights. -/
theorem actual_second_allocation_coarse (s : Data ι)
    (D : Ideal O)(alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O)(B₁ B₂ : ℝ)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (hW₁ : ∀x,‖s.W₁ x‖≤B₁)(hW₂ : ∀x,‖s.W₂ x‖≤B₂) :
    retainedAllocationCost s D alloc z≤
      ((2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*(coarseRowControl s B₁ B₂)^2*
        (coarseRowSize s false+coarseRowSize s true))/formalReductionFactor D alloc s.P := by
  have hprod : (∏i∈frozenIndices D alloc,s.M i)≤∏i,s.M i :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hrows := add_le_add
    (actual_second_positive_coarse s false D alloc z B₁ B₂ hB₁ hB₂ hW₁ hW₂)
    (actual_second_positive_coarse s true D alloc z B₁ B₂ hB₁ hB₂ hW₁ hW₂)
  have hfp : 0≤∏i∈frozenIndices D alloc,s.M i :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  have hden := (s.reduction_pos D alloc).le
  unfold retainedAllocationCost
  apply (mul_le_mul
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hfp hprod 2) (by positivity)) (s.reduction_pos D alloc).le)
    hrows (by positivity) (by positivity)).trans_eq
  ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.coarse_dilated_support
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_positive_absolute
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_positive_coarse
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_allocation_coarse
