/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full artificial-divisor sum of the actual two corrected allocation windows. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.ExceptionalWindow.Divisor
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
open CenteredMomentWholeDivisorShell Record1252270103Second
local notation "O" => ActualEisensteinCubic.O
local notation "frozenCost" => CenteredMomentCommonExceptionalCost.frozenProfile

/-- Abbreviation of the actual two windows, retaining both complete allocation sums. -/
def pairedWindow {ι : Type*} [Fintype ι] (s : Input ι) (C D RC RD : Ideal O)
    (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q seed : Ideal O)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
    (J : ℕ) (t : ℝ) : ℝ :=
  windowBudget J t (allocationBudget s C RC
    (fun B => correctedAllocatedBudget s C RC B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀)) *
  windowBudget J t (allocationBudget s D RD
    (fun B => correctedAllocatedBudget s D RD B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀))

/-- The harmonic constant and threshold precede every moving datum, even the
slot type and seed exponent. No energy estimate is a hypothesis. -/
theorem corrected_paired_full_divisor_sum (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ H : ℝ, 0<H ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ {ι : Type*} [Fintype ι] (s : Input ι) (C D RC RD : Ideal O), C≠0 → D≠0 →
    ∀ (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q : Ideal O)
      (U : Finset (CommonIndex C D)) (ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
      (J : ℕ) (t : ℝ), 0≤εL → 0≤α → 0≤Cr → 0≤K₀ →
    ∀ (Ls : Finset (Ideal O)), (∀ L∈Ls, L≠0) →
      (∀ L∈Ls, (L.absNorm:ℝ)≤Z^B) →
      (∑ L∈Ls, ‖(moebius L:ℂ)‖ *
        pairedWindow s C D RC RD S W₁ W₂ Φ Q L U Z ε εL α Lraw Cr Mrow C₀ K₀ J t) ≤
      H*Z^(δ+B*εL)*
        ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
        ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1)*(frozenCost s)^2*
        correctedExceptionalBudget s S W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr Mrow C₀ K₀*
        (heightEnvelope t^J*profileMoment J)^2 := by
  obtain ⟨H,hH,hbound⟩ := full_seed_mass_subpower B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst s C D RC RD hC hD S W₁ W₂ Φ Q U ε εL α Lraw Cr Mrow C₀ K₀ J t
    hεL hα hCr hK₀ Ls _hne hLs
  let P := ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
    ((C.absNorm:ℝ)*(D.absNorm:ℝ))^(α-1)*(frozenCost s)^2*
    correctedExceptionalBudget s S W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr Mrow C₀ K₀*
    (heightEnvelope t^J*profileMoment J)^2
  have hZ0 : 0≤Z := (zero_lt_one.trans hZ.1).le
  have hE := correctedExceptionalBudget_nonneg s S W₁ W₂ Φ Q C D 1 U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hZ0 hCr hK₀
  have hP : 0≤P := by dsimp only [P]; positivity
  have hp (L : Ideal O) :
      pairedWindow s C D RC RD S W₁ W₂ Φ Q L U Z ε εL α Lraw Cr Mrow C₀ K₀ J t ≤
        ((L.absNorm:ℝ)^εL/(L.absNorm:ℝ))*P := by
    have hh := corrected_paired_window s C D RC RD hC hD S W₁ W₂ Φ Q L U
      Z ε εL α Lraw Cr Mrow C₀ K₀ J t hα hZ0 hCr hK₀
    rw [corrected_seed_exact] at hh
    change _≤_ at hh
    dsimp only [pairedWindow, P]
    convert hh using 1 <;> ring
  calc
    _≤∑ L∈Ls, (‖(moebius L:ℂ)‖*((L.absNorm:ℝ)^εL/(L.absNorm:ℝ)))*P := by
      apply Finset.sum_le_sum
      intro L hL
      convert mul_le_mul_of_nonneg_left (hp L) (norm_nonneg (moebius L:ℂ)) using 1 <;> ring
    _=(∑ L∈Ls, ‖(moebius L:ℂ)‖*((L.absNorm:ℝ)^εL/(L.absNorm:ℝ)))*P :=
      (Finset.sum_mul ..).symm
    _≤(H*Z^(δ+B*εL))*P := mul_le_mul_of_nonneg_right (hZ.2 εL hεL Ls hLs) hP
    _=_ := by dsimp only [P]; ring
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.corrected_paired_full_divisor_sum
