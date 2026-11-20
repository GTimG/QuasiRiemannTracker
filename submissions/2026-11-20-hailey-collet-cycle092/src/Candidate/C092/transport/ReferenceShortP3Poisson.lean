/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The authentic first Poisson expansion in the short-column regime.
The cutoff applies to every common-divisor allocation, before any second
transform. No large marked native-face estimate is used. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentSourceInputFirstTailUniform
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_ReferenceShortP3Poisson_e7d1729a102bcc75_001 {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- A short first-Poisson cutoff contains no nonzero Eisenstein lattice
point. The factor four is the actual native dyadic collar. -/
theorem retained_energy_eq_zero
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ)
    (hK : 0 < K) (hZ : 0 ≤ Z) (hcut : 4*(X^2/K)*Z^(ξ/2) < 1) :
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S c Φ K X Z ξ = 0 := by
  unfold CenteredMomentFirstSectorLocalization.retainedEnergy
  apply Finset.sum_eq_zero
  intro I hI
  apply Finset.sum_eq_zero
  intro J hJ
  suffices hpair : CenteredMomentFirstSectorLocalization.retainedPair I J
      (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2 Φ K X Z ξ = 0 by
    rw [hpair, mul_zero]
  unfold CenteredMomentFirstSectorLocalization.retainedPair
  apply Finset.sum_eq_zero
  intro E hE
  have hw (h : O) : retainedWeight (frequencyRadius
      (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ) (normValue h) = 0 := by
    by_cases hh : h = 0
    · subst h
      exact retainedWeight_zero_nonpos _ _ (by simp [normValue])
    · apply retainedWeight_zero_above
      have hscale := first_nominal_scale_le I J E K X hK
      have hpow : 0 ≤ Z^(ξ/2) := Real.rpow_nonneg hZ _
      have hc : 4*frequencyRadius (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ < 1 := by
        dsimp only [frequencyRadius]
        nlinarith [mul_le_mul_of_nonneg_right hscale hpow]
      exact hc.le.trans (normValue_ge_one h hh)
  simp only [canonicalRetainedTerm, hw, Complex.ofReal_zero, zero_mul,
    tsum_zero, mul_zero]

/-- Complete first-Poisson energy, including its true sixth-free zero
diagonal and discarded tail. The seminorms and constants precede both
live ordinary Schwartz profiles and the entire live source. -/
theorem short_input_energy {ι : Type*} [Fintype ι]
    (hi : ι → ℝ) (wlo whi B ε ξ saving : ℝ)
    (hhi : ∀ i, 0 ≤ hi i) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (hB : 0 ≤ B) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ Sdiag Stail : Finset (ℕ×ℕ), ∃ Cdiag Ctail : ℝ,
      0 < Cdiag ∧ 0 < Ctail ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)), s.W₁ = W₁ → s.W₂ = W₂ →
      Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc wlo whi →
      Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc wlo whi →
      (∀ i, s.hi i ≤ hi i) → ∀ (m A : O),
      ConcretePrimeRowBridge.goodLambda ∣ m → (2 : O) ∣ m →
      ∀ (R seed : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), 0 < K →
      volume s.toData ≤ Z^B → K⁻¹ ≤ Z^B →
      4*((volume s.toData)^2/K)*Z^(ξ/2) < 1 →
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖ / volume s.toData ≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε +
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,h⟩ :=
    CenteredMomentSourceInputFirstRemainder.original_first_remainder hi wlo whi B ε ξ saving
      hhi hwlo hwhi hB hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,h.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hvol hKi hcut
  have hb := hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hvol hKi
  rw [retained_energy_eq_zero s.η m A s.t _ _ Φ K (volume s.toData) Z ξ hK (by linarith only [hZ.1]) hcut,
    sub_zero] at hb
  exact hb

#print axioms retained_energy_eq_zero
#print axioms short_input_energy
end
end QRH.Cycle092.ReferenceShortP3
