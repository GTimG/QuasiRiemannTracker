/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact uncentered short-column specialization. The zero comparison column
is a native comparisonScale identity, not an assumed energy estimate. -/
import Candidate.C092.transport.ReferenceShortP3Poisson
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UncenteredTerminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentAddedZeroUniform CenteredMomentUncenteredTerminal
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_ReferenceShortP3Uncentered_16126f57c7cd6ad3_001 {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem input_coefficient_uncentered {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support s.W₁ ⊆ Set.Icc a b)
    (hY : s.Y₁ = comparisonScale b) :
    coefficient s R seed = finiteColumnCoefficient (Fintype.piFinset s.pools)
      (uncenteredProfileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ 1 1 seed) := by
  unfold coefficient
  rw [hY,profileCoefficient_eq_uncentered R s.ν s.W s.P s.W₁ s.W₂ a b ha hs
    s.X₁ s.X₂ s.Y₂ 1 1 seed one_ne_zero]

/-- A complete normalized uncentered short marked fourth source, when the
live Input has two equal ordinary columns and duplicated actual slots.
The theorem itself allows unequal columns as well. All source masks,
coefficients, pitch, arithmetic character and prime holes are literal. -/
theorem short_uncentered_input_energy {ι : Type*} [Fintype ι]
    (hi : ι → ℝ) (wlo whi B ε ξ saving : ℝ)
    (hhi : ∀ i, 0 ≤ hi i) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (hB : 0 ≤ B) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ Sdiag Stail : Finset (ℕ×ℕ), ∃ Cdiag Ctail : ℝ,
      0 < Cdiag ∧ 0 < Ctail ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)), s.W₁ = W₁ → s.W₂ = W₂ →
      Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc wlo whi →
      Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc wlo whi →
      (∀ i, s.hi i ≤ hi i) → s.Y₁ = comparisonScale whi →
      ∀ (m A : O), ConcretePrimeRowBridge.goodLambda ∣ m → (2 : O) ∣ m →
      ∀ (R seed : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), 0 < K →
      volume s.toData ≤ Z^B → K⁻¹ ≤ Z^B →
      4*((volume s.toData)^2/K)*Z^(ξ/2) < 1 →
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (finiteColumnCoefficient (Fintype.piFinset s.pools)
          (uncenteredProfileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ 1 1 seed)) Φ K‖ /
        volume s.toData ≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε +
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,h⟩ := short_input_energy hi wlo whi B ε ξ saving
    hhi hwlo hwhi hB hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,h.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hY m A hml hm2 R seed Φ K hK hvol hKi hcut
  have hb := hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hvol hKi hcut
  rw [input_coefficient_uncentered s R seed wlo whi hwlo (he₁.symm ▸ hs₁) hY] at hb
  exact hb

#print axioms input_coefficient_uncentered
#print axioms short_uncentered_input_energy
end
end QRH.Cycle092.ReferenceShortP3
