/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full artificial-divisor sum of the actual two corrected allocation windows. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.Sum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondHarmonicBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter UniqueFactorizationMonoid HeckeFamily
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentSecondWindowBudget
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup CenteredMomentDivisorBoundary Record1252270103Second
local notation "O" => ActualEisensteinCubic.O
local notation "frozenCost" => CenteredMomentCommonExceptionalCost.frozenProfile

theorem corrected_paired_actual_divisor_sum (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ H : ℝ, 0<H ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ {ι : Type*} [Fintype ι] (s : Input ι) (C D RC RD : Ideal O), C≠0 → D≠0 →
    ∀ (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q : Ideal O)
      (U : Finset (CommonIndex C D)) (ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
      (J : ℕ) (t : ℝ), 0≤εL → 0≤α → 0≤Cr → 0≤K₀ →
    ∀ {κ : Type*} (T : Finset κ) (v : κ→Ideal O), (∀ j∈T, v j≠0) →
      (∀ j∈T, ((v j).absNorm:ℝ)≤Z^B) →
      (∑ L∈divisorPool T v, ‖(moebius L:ℂ)‖ *
        pairedWindow s C D RC RD S W₁ W₂ Φ Q L U Z ε εL α Lraw Cr Mrow C₀ K₀ J t) ≤
      H*Z^(δ+B*εL)*
        ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
        ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1)*(frozenCost s)^2*
        correctedExceptionalBudget s S W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr Mrow C₀ K₀*
        (heightEnvelope t^J*profileMoment J)^2 := by
  obtain ⟨H,hH,hbound⟩ := corrected_paired_full_divisor_sum B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst s C D RC RD hC hD S W₁ W₂ Φ Q U ε εL α Lraw Cr Mrow C₀ K₀ J t
    hεL hα hCr hK₀ κ T v hv hn
  exact hZ.2 s C D RC RD hC hD S W₁ W₂ Φ Q U ε εL α Lraw Cr Mrow C₀ K₀ J t
    hεL hα hCr hK₀ (divisorPool T v)
    (fun L hL => (divisorPool_nonzero_norm T v hv (Z^B) hn L hL).1)
    (fun L hL => (divisorPool_nonzero_norm T v hv (Z^B) hn L hL).2)
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.corrected_paired_actual_divisor_sum
