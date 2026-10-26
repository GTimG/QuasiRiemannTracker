/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual sharp allocation budgets, paired at the two literal common ideals. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalSharpAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentSecondWindowBudget
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentCanonicalFirst
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O
local notation "frozenCost" => CenteredMomentCommonExceptionalCost.frozenProfile
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq ι := Classical.decEq _

lemma sqrt_sharp_bound (A c n f E α : ℝ) (hc : 0≤c) (hn : 0<n)
    (hf : 0≤f) (hE : 0≤E)
    (hA : A≤c^2*n^(2*α)*(f^2/n^2)*E) :
    Real.sqrt A≤c*n^(α-1)*f*Real.sqrt E := by
  have he : c^2*n^(2*α)*(f^2/n^2)*E=(c*n^(α-1)*f*Real.sqrt E)^2 := by
    rw [Real.rpow_sub hn, Real.rpow_one]
    have hp : n^(2*α)=(n^α)^2 := by
      rw [mul_comm (2:ℝ) α, Real.rpow_mul hn.le, Real.rpow_two]
    rw [hp, mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hE]
    ring
  calc
    Real.sqrt A≤Real.sqrt ((c*n^(α-1)*f*Real.sqrt E)^2) :=
      Real.sqrt_le_sqrt (hA.trans_eq he)
    _=c*n^(α-1)*f*Real.sqrt E := Real.sqrt_sq (by positivity)

/-- The two punctures may differ; the seed, original input and exceptional budget agree. -/
theorem corrected_paired_window (s : Input ι) (C D RC RD : Ideal O)
    (hC : C≠0) (hD : D≠0) (S : Finset (ℕ×ℕ))
    (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q seed : Ideal O) (U : Finset (CommonIndex C D))
    (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ) (J : ℕ) (t : ℝ)
    (hα : 0≤α) (hZ : 0≤Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    windowBudget J t (allocationBudget s C RC
      (fun B => correctedAllocatedBudget s C RC B S W₁ W₂ Φ Q C D seed U
        Z ε εL α Lraw Cr Mrow C₀ K₀)) *
    windowBudget J t (allocationBudget s D RD
      (fun B => correctedAllocatedBudget s D RD B S W₁ W₂ Φ Q C D seed U
        Z ε εL α Lraw Cr Mrow C₀ K₀)) ≤
    ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
      ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1)*(frozenCost s)^2*
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀*
      (heightEnvelope t^J*profileMoment J)^2 := by
  let E := correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀
  have hE : 0≤E := correctedExceptionalBudget_nonneg s S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hZ hCr hK₀
  have hNC : (0:ℝ)<C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hND : (0:ℝ)<D.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hf := CenteredMomentCommonExceptionalCost.frozenProfile_nonneg s
  have hc := sqrt_sharp_bound _ _ _ _ E α (Nat.cast_nonneg _) hNC hf hE
    (corrected_allocation_budget_sharp_norm s C RC hC S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀)
  have hd := sqrt_sharp_bound _ _ _ _ E α (Nat.cast_nonneg _) hND hf hE
    (corrected_allocation_budget_sharp_norm s D RD hD S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀)
  have hh := mul_le_mul hc hd (Real.sqrt_nonneg _) (by positivity)
  have hH : 0≤(heightEnvelope t^J*profileMoment J)^2 := sq_nonneg _
  have ht := mul_le_mul_of_nonneg_right hh hH
  unfold windowBudget
  convert ht using 1
  · ring
  · rw [Real.mul_rpow hNC.le hND.le]
    dsimp only [E] at *
    ring_nf
    rw [Real.sq_sqrt hE]
    ring
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.sqrt_sharp_bound
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.corrected_paired_window
