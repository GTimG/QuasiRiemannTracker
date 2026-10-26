/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLowAdmission
import Candidate.Research.RecursiveAffine.ActualDeletedCapacity

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentWholeSlotDeletion
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open Cycle63Moment Cycle63Moment.LowBranch Cycle63InitialMass Cycle63FinalLow

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

section Selected
variable (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
  (Z Mrow amp xi reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
  (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp xi reserve b t N hZ key q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b t N hZ key q hz1 hz2 n

/-- The actual selected-source puncture update, before any norm estimate.
The inherited puncture is multiplied only by the selected own first ideal.
The final selected own second ideal is multiplied afterwards in retainedState. -/
theorem actual_selected_puncture_update : (datum).R=R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val := rfl

theorem actual_selected_puncture_nonzero (hR : R≠0) (second : Bool) :
    (datum).R*(if second then (datum).D else (datum).C)≠0 :=
  actual_geometry_low_second_puncture reflected s R seed Z Mrow amp xi reserve b t N hZ key q hz1 hz2 n hR second
end Selected

/-- Exact logarithmic update for a genuine physical chain. The selected
source constructor above discharges hR2 by rfl. The paired first common
ideal and character modulus do not enter this puncture identity. -/
theorem actual_chain_puncture_log
    (s : Input alpha) (ch : Chain s) (R : Ideal O) (hR : R≠0)
    (hR2 : ch.R₂=R*ch.C₁) (hP : ch.R₂*ch.E₂≠0) (Z : ℝ) :
    Real.logb Z ((ch.R₂*ch.E₂).absNorm:ℝ) =
      Real.logb Z (R.absNorm:ℝ)+Real.logb Z (ch.C₁.absNorm:ℝ)+Real.logb Z (ch.E₂.absNorm:ℝ) := by
  have hRC : R*ch.C₁≠0 := by rw [←hR2]; exact (mul_ne_zero_iff.mp hP).1
  have hC := (mul_ne_zero_iff.mp hRC).2
  have hE := (mul_ne_zero_iff.mp hP).2
  have hrN : (R.absNorm:ℝ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hR
  have hcN : (ch.C₁.absNorm:ℝ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hC
  have heN : (ch.E₂.absNorm:ℝ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hE
  rw [hR2,map_mul,map_mul,Nat.cast_mul,Nat.cast_mul,
    Real.logb_mul (mul_ne_zero hrN hcN) heN,Real.logb_mul hrN hcN]

/-- The SAME literal daughter capacity pays the actual puncture increment.
Parent-cap slack, residual F and upward deletion overshoot are charged
conservatively. Thus V+Red=A-D-Achild in the exact model lift pays the
source mask; no coarse `(Rc+8)/unit` recurrence is needed. -/
theorem actual_physical_puncture_credit
    (s : Input alpha) (ch : Chain s) (R : Ideal O) (hR : R≠0)
    (hR2 : ch.R₂=R*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (chi : Character) (t Z : ℝ) (hZ : 1<Z) (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (hcard : Fintype.card alpha ≤ N) (hs : s.upper ≤ b)
    (hP : ∀i,1 ≤ s.P i) (w : alpha→ℝ) (hscale : ∀i,s.P i=Z^(w i))
    (hn1 : frozenCoefficient ch.B₁.val ch.C₁ ch.R₁ s.ν s.W s.P≠0)
    (hn2 : frozenCoefficient ch.B₂.val ch.E₂ ch.R₂ ch.first.ν ch.first.W ch.first.P≠0)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final chi t).toSource second L alloc row≠0)
    (Rdel : Finset alpha) (hRdel : Rdel ⊆ ch.indices L alloc)
    (A D V Red : ℝ)
    (hA : length Z s.X₁+length Z s.X₂+(∑i,w i) ≤ A)
    (hdel : D ≤ ∑i∈Rdel,w i) :
    let Achild := length Z (rawDaughterScale (ch.final chi t) second L alloc 0)+
      length Z (rawDaughterScale (ch.final chi t) second L alloc 1)+(∑i∈ch.indices L alloc\Rdel,w i)
    let pad := 2*(N:ℝ)*Real.logb Z b+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    Achild=A-D-V-Red →
    Real.logb Z ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ Real.logb Z (R.absNorm:ℝ)+V+Red+pad := by
  intro Achild pad hmodel
  have hcap := actual_deleted_daughter_total_capacity s ch chi t Z hZ N b hb
    hcard hs hP w hscale hn1 hn2 second L alloc row hne Rdel hRdel
  have hPfinal : ∀i,1 ≤ (ch.final chi t).P i := fun i=>hP i.val.val
  have hF : 0 ≤ Real.logb Z (formalReductionFactor L alloc (ch.final chi t).P) :=
    Real.logb_nonneg hZ (formalReduction_ge_one L alloc (ch.final chi t).P hPfinal)
  rw [actual_chain_puncture_log s ch R hR hR2 hPuncture Z]
  dsimp only [Achild,pad] at hmodel ⊢
  linarith only [hcap,hA,hdel,hF,hmodel]

/-- The paid mask gate restores the actual native cap20 after rebasing.
Its premise is the explicit geometric budget proved by the fixed-prefix
dual certificates; it is not the desired puncture norm bound itself. -/
theorem actual_puncture_mask20_of_log_budget
    (P : Ideal O) (hP : P≠0) (Z unit budget : ℝ) (hZ : 1<Z)
    (hlog : Real.logb Z (P.absNorm:ℝ) ≤ budget) (hbudget : budget ≤ 20*unit) :
    (P.absNorm:ℝ) ≤ (Z^unit)^(20:ℝ) := by
  have hPN : 0 < (P.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  have h := (Real.logb_le_iff_le_rpow hZ hPN).mp (hlog.trans hbudget)
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  simpa only [mul_comm] using h

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_puncture_update
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_chain_puncture_log
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_physical_puncture_credit
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_puncture_mask20_of_log_budget
