import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondBlock

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSupport
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

def secondActiveRows {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) : Finset (Label×O) :=
  rows.filter (fun k=>logAnnulus (s k.1).rho≠0 ∧ logAnnulus ((s k.1).x k.2)≠0 ∧
    Squarefree (L k.1) ∧ (s k.1).rowWeight k.2≠0)

/-- Removing only identically vanishing terms preserves the literal sum. -/
theorem actual_second_active_expression {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (χ ψ : Label→RayCharacter) (rows : Finset (Label×O))
    (w : Label×O→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (∑k∈rows,w k*secondSectorTerm (s k.1) W (L k.1) (χ k.1) (ψ k.1) k.2)=
      ∑k∈secondActiveRows s L rows,
        w k*secondSectorTerm (s k.1) W (L k.1) (χ k.1) (ψ k.1) k.2 := by
  rw [secondActiveRows,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h₀ : logAnnulus (s k.1).rho=0
  · simp [h₀,secondSectorTerm,wholeKernel]
  · by_cases h₁ : logAnnulus ((s k.1).x k.2)=0
    · simp [h₁,secondSectorTerm,wholeKernel]
    · by_cases hL : Squarefree (L k.1)
      · by_cases hq : (s k.1).rowWeight k.2=0
        · simp [hq,secondSectorTerm,CanonicalSectorSource.signedWeight]
        · simp [h₀,h₁,hL,hq]
      · simp [h₀,h₁,hL,secondSectorTerm,CanonicalSectorSource.signedWeight,
          SecondBlockSource.sector,UniqueFactorizationMonoid.moebius_of_not_squarefree hL]

theorem actual_second_active_squarefree {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) : Squarefree (L k.1) :=
  (Finset.mem_filter.mp hk).2.2.2.1

theorem actual_second_active_partition {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) :
    canonicalPartition (s k.1).C (s k.1).D (s k.1).inactive
      (nonunitFrequencyGenerator (s k.1).C (s k.1).D (s k.1).inactive*k.2) := by
  have hq := (Finset.mem_filter.mp hk).2.2.2.2
  by_contra hn
  exact hq (by simp [SecondBlockSource.rowWeight,retainedScalar,canonicalPartitionScalar,hn])

theorem actual_second_active_correlation {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) :
    idealCorrelation (s k.1).C (s k.1).D (s k.1).hC (s k.1).hD
      ((s k.1).frequency*k.2)≠0 :=
  (mul_ne_zero_iff.mp (show (s k.1).rowWeight k.2≠0 from
    (Finset.mem_filter.mp hk).2.2.2.2)).2

theorem actual_second_active_annulus {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O))
    (hrows : ∀k∈rows,k.2∈(s k.1).rows) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) :
    dyadicScale ((s k.1).dyad 1)/4≤normValue k.2 ∧
      normValue k.2≤dyadicScale ((s k.1).dyad 1) := by
  have hx := logAnnulus_support (Finset.mem_filter.mp hk).2.2.1
  have hz : 0<normValue k.2 := by
    rw [normValue_eq_embedding]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero
      ((s k.1).rows_ne _ (hrows k (Finset.mem_filter.mp hk).1))))
  have hH := dyadicScale_pos ((s k.1).dyad 1)
  have hlo := Real.exp_le_exp.mpr hx.1
  have hhi := Real.exp_le_exp.mpr hx.2
  dsimp [SecondBlockSource.x] at hlo hhi
  rw [Real.exp_log (div_pos hz hH),Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ)<4)] at hlo
  rw [Real.exp_log (div_pos hz hH),Real.exp_zero] at hhi
  exact ⟨by have hh := (le_div_iff₀ hH).mp hlo; linarith,
    (div_le_one hH).mp hhi⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_correlation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_annulus
