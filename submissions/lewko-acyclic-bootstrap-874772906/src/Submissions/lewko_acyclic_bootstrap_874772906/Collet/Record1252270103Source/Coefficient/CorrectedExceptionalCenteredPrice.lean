/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal corrected seed-one budget exposes its radial sixth root and its
centered profile factor before the actual nonzero physical-block ledger. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalBudget
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalRadicalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform
open CenteredMomentSecondPhysicalBlock Cycle61FinalNatural
open Record1252270103Second QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O

def centeredProfileFactor {ι : Type*}[Fintype ι] (s : Input ι)
    (T : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q : Ideal O)
    (Z ε α Lraw Cr C₀ K₀ : ℝ) : ℝ :=
  K₀*forcedProfileCost s*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    Cr^(1/6:ℝ)*
    (C₀*(sourceControl T W₁*sourceControl T W₂)*Z^ε*(max 1 Lraw)^(-α)*slotControl s.toData)^2*
    SchwartzMap.seminorm ℝ 0 0 Φ

theorem centeredProfileFactor_nonneg {ι : Type*}[Fintype ι] (s : Input ι)
    (T : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q : Ideal O)
    (Z ε α Lraw Cr C₀ K₀ : ℝ) (hK₀ : 0≤K₀) (hCr : 0≤Cr) :
    0≤centeredProfileFactor s T W₁ W₂ Φ Q Z ε α Lraw Cr C₀ K₀ := by
  have hp:=forcedProfileCost_nonneg s
  have hs : 0≤SchwartzMap.seminorm ℝ 0 0 Φ:=apply_nonneg _ _
  unfold centeredProfileFactor
  positivity

theorem corrected_seed_one_radial_exact {ι : Type*}[Fintype ι] (s : Input ι)
    (T : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr C₀ K₀ H : ℝ)
    (hZ : 1<Z) (hH : 0<H) :
    correctedExceptionalBudget s T W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr (Real.logb Z H) C₀ K₀=
      centeredProfileFactor s T W₁ W₂ Φ Q Z ε α Lraw Cr C₀ K₀*
        (H^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ))*volume s^2 := by
  have hf : 0<forcingNorm C D U:=common_product_pos C D hC _
  have hc:=CenteredMomentFiniteProfileExceptionalPhysical.count_power Z H (forcingNorm C D U) 0 hZ hH hf
  simp only [add_zero,Real.rpow_zero,mul_one] at hc
  unfold correctedExceptionalBudget exceptionalRowCost centeredProfileFactor
  simp only [map_one,Nat.cast_one,Real.one_rpow,mul_one,div_one]
  simp only [forcingNorm] at hc
  rw [hc]
  simp only [forcingNorm]
  ring

/-- This is the actual corrected budget on a nonzero original retained block,
including the complete squared centered factor and the true child volume. -/
theorem actual_centered_radical_budget {ι : Type*}[Fintype ι] (s : Input ι)
    (T : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q : Ideal O)
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (Z ε εL α Lraw Cr C₀ K₀ : ℝ) (hZ : 1<Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    normalizer C D U*
      ((Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(2*α)/((C.absNorm:ℝ)*(D.absNorm:ℝ)))*
      correctedExceptionalBudget s T W₁ W₂ Φ Q C D 1 U
        Z ε εL α Lraw Cr (Real.logb Z (retainedScale R C D U)) C₀ K₀/volume s≤
      centeredProfileFactor s T W₁ W₂ Φ Q Z ε α Lraw Cr C₀ K₀*
        volume s*(4*R)^(1/6:ℝ)*(Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(2*α-2) := by
  have hV:=volume_pos s
  have hrad : (0:ℝ)<Ideal.absNorm (∏P : CommonIndex C D,P.val):=common_product_pos C D hC Finset.univ
  have hp:=centeredProfileFactor_nonneg s T W₁ W₂ Φ Q Z ε α Lraw Cr C₀ K₀ hK₀ hCr
  have hh:=actual_retained_radical_cost η t S β C D hC hD hCD U R rows hrows W K hK n hne Z hZ
  have hs:=mul_le_mul_of_nonneg_left hh
    (show 0≤centeredProfileFactor s T W₁ W₂ Φ Q Z ε α Lraw Cr C₀ K₀*volume s*
      (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(2*α) by positivity)
  have hH : 0<retainedScale R C D U := zero_lt_one.trans_le (le_max_left _ _)
  rw [corrected_seed_one_radial_exact s T W₁ W₂ Φ Q C D hC U Z ε εL α Lraw Cr C₀ K₀
    (retainedScale R C D U) hZ hH]
  have he : (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(-2:ℝ)*
      (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(2*α)=
      (Ideal.absNorm (∏P : CommonIndex C D,P.val):ℝ)^(2*α-2) := by
    rw [←Real.rpow_add hrad]
    congr 1
    ring
  convert hs using 1
  · field_simp [hV.ne']
  · rw [←he]
    ring

end
end OAI.SevenEighths.Record1252270103Source.ExceptionalRadical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.centeredProfileFactor_nonneg
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.corrected_seed_one_radial_exact
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalRadical.actual_centered_radical_budget
