/- Copyright (c) 2026 Sil. Apache-2.0.
Exact localization dictionary at the fourth-power scale. The literal
correlation, its negative argument, all coefficients, and the supported
ideal pool are preserved. This module supplies no estimate for beta.
-/
import Candidate.FourthPower.MixedPoissonLocalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondLocalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

set_option autoImplicit false
namespace Candidate.FourthPower.MixedLocalizedDictionary
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CompletedGauss CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSecondTail CenteredMomentFirstLocalization
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondEnergySplit RayFourExpansion
open MixedPoissonLocalization
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- No positivity of K or nonvanishing denominator is needed: this is
only the exact outer normalization at positive W. -/
theorem fourth_prefactor (K W : ℝ) (hW : 0<W) :
    ((16*K*W^3:ℝ):ℂ)=((16*K*W^4:ℝ):ℂ)/(W:ℂ) := by
  have hWc : (W:ℂ)≠0 := by exact_mod_cast hW.ne'
  push_cast
  field_simp [hWc]

/-- The exact retained density of the supported-column family. The
second energy receives K4=16*K*W^4, and the outer 1/W is unchanged. -/
theorem source_retained (η : Character) (t : ℝ)
    (Q : Finset Id) (β : Id→ℂ) (K W Tsec Z ξ : ℝ) (hW : 0<W) :
    localizedDensity Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q=>β I*heightCoeff η t I) K W
      (retainedWeight (frequencyRadius Tsec Z ξ))=
      secondRetainedEnergy η t Q β ballProfile (16*K*W^4) Tsec Z ξ/(W:ℂ) := by
  unfold localizedDensity secondRetainedEnergy secondRetainedPair
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  rw [fourth_prefactor K W hW]
  ring

/-- Identical exact dictionary for the discarded Fourier frequencies.
In particular, no change to the infinite correlation sum is involved. -/
theorem source_discarded (η : Character) (t : ℝ)
    (Q : Finset Id) (β : Id→ℂ) (K W Tsec Z ξ : ℝ) (hW : 0<W) :
    localizedDensity Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q=>β I*heightCoeff η t I) K W
      (discardedWeight (frequencyRadius Tsec Z ξ))=
      secondDiscardedEnergy η t Q β ballProfile (16*K*W^4) Tsec Z ξ/(W:ℂ) := by
  unfold localizedDensity secondDiscardedEnergy secondDiscardedPair
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  rw [fourth_prefactor K W hW]
  ring

/-- A pool whose ideals are all supported is exactly the supported-column
pool, with its original generator and coefficient. This applies to the
literal FirstPhysicalSource.columns using column_supported and element. -/
theorem supported_pool_reindex (Q : Finset Id) (hQ : ∀I∈Q,Supported I)
    (a : Q→O) (ha : ∀I,Supported (Ideal.span {a I}))
    (hgen : ∀I,a I=primaryGenerator (I:Id))
    (β : Id→ℂ) (K W : ℝ) (ρ : ℝ→ℝ) :
    localizedDensity Finset.univ a ha (fun I : Q=>β I) K W ρ=
      localizedDensity Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q=>β I) K W ρ := by
  let e : Q ≃ supportedColumns Q :=
    { toFun := fun I=>⟨I,Finset.mem_filter.mpr ⟨I.property,hQ I I.property⟩⟩
      invFun := fun I=>⟨I,(Finset.mem_filter.mp I.property).1⟩
      left_inv := fun I=>by rfl
      right_inv := fun I=>by rfl }
  unfold localizedDensity
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [hgen,sourceGenerator,e]
  rfl

/-- The retained dictionary on the original supported pool subtype.
Its full beta, including every already-fixed mask, remains literal. -/
theorem supported_pool_retained (η : Character) (t : ℝ)
    (Q : Finset Id) (hQ : ∀I∈Q,Supported I)
    (a : Q→O) (ha : ∀I,Supported (Ideal.span {a I}))
    (hgen : ∀I,a I=primaryGenerator (I:Id))
    (β : Id→ℂ) (K W Tsec Z ξ : ℝ) (hW : 0<W) :
    localizedDensity Finset.univ a ha (fun I : Q=>β I*heightCoeff η t I) K W
      (retainedWeight (frequencyRadius Tsec Z ξ))=
      secondRetainedEnergy η t Q β ballProfile (16*K*W^4) Tsec Z ξ/(W:ℂ) := by
  rw [supported_pool_reindex Q hQ a ha hgen
    (fun I : Id=>β I*heightCoeff η t I) K W
    (retainedWeight (frequencyRadius Tsec Z ξ))]
  exact source_retained η t Q β K W Tsec Z ξ hW

/-- The discarded dictionary uses the same original supported pool and
the same fourth-power scale, again with its exact outer factor 1/W. -/
theorem supported_pool_discarded (η : Character) (t : ℝ)
    (Q : Finset Id) (hQ : ∀I∈Q,Supported I)
    (a : Q→O) (ha : ∀I,Supported (Ideal.span {a I}))
    (hgen : ∀I,a I=primaryGenerator (I:Id))
    (β : Id→ℂ) (K W Tsec Z ξ : ℝ) (hW : 0<W) :
    localizedDensity Finset.univ a ha (fun I : Q=>β I*heightCoeff η t I) K W
      (discardedWeight (frequencyRadius Tsec Z ξ))=
      secondDiscardedEnergy η t Q β ballProfile (16*K*W^4) Tsec Z ξ/(W:ℂ) := by
  rw [supported_pool_reindex Q hQ a ha hgen
    (fun I : Id=>β I*heightCoeff η t I) K W
    (discardedWeight (frequencyRadius Tsec Z ξ))]
  exact source_discarded η t Q β K W Tsec Z ξ hW

/-- Exact exceptional/nonexceptional split of the localized retained
density. The source cap concerns the full ideal norm of every nonzero
original coefficient. Both partEnergy terms use the fourth-power scale. -/
theorem source_retained_split (η : Character) (χ : RayCharacter)
    (Q₀ : Id) (m : O) (t : ℝ) (Q : Finset Id) (β : Id→ℂ)
    (K W Tsec Z ξ H : ℝ) (hK : 0<K) (hW : 0<W)
    (hH : ∀I∈Q,β I≠0→(Ideal.absNorm I:ℝ)≤H) :
    localizedDensity Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q=>β I*heightCoeff η t I) K W
      (retainedWeight (frequencyRadius Tsec Z ξ))=
      (partEnergy true η χ Q₀ m t Q β ballProfile (16*K*W^4) Tsec Z ξ H+
       partEnergy false η χ Q₀ m t Q β ballProfile (16*K*W^4) Tsec Z ξ H)/(W:ℂ) := by
  rw [source_retained η t Q β K W Tsec Z ξ hW,
    original_energy_split η χ Q₀ m t Q β ballProfile (16*K*W^4)
      Tsec Z ξ H (by positivity) hH]

/-- Uniform rapidly decreasing discarded-density bound, specialized to
ballProfile. Every original scale/threshold condition is displayed, with
K4=16*K*W^4 in the Fourier-scale condition. The original coefficient L1
mass and the final division by W are left explicit. -/
theorem source_discarded_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (t : ℝ) (Q : Finset Id) (β : Id→ℂ)
        (K W X H Tsec Z Csec ξ : ℝ),0<K → 0<W → 0<X → 1<Z → 1≤Csec →
      (∀I∈Q,β I≠0→(Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/(16*K*W^4)≤Tsec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖localizedDensity Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q=>β I*heightCoeff η t I) K W
        (discardedWeight (frequencyRadius Tsec Z ξ))‖≤
      ((∑I∈Q,‖β I‖)^2*(16*K*W^4)*(Real.exp H*X)^2*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec))/W := by
  obtain ⟨s,C,hC,ht⟩ := second_discarded_energy_bound Adec
  refine ⟨s,C,hC,?_⟩
  intro η t Q β K W X H Tsec Z Csec ξ hK hW hX hZ hCs hN hsec hthreshold
  rw [source_discarded η t Q β K W Tsec Z ξ hW,
    norm_div,Complex.norm_real,Real.norm_of_nonneg hW.le]
  exact div_le_div_of_nonneg_right
    (ht η t Q β ballProfile (16*K*W^4) X H Tsec Z Csec ξ
      (by positivity) hX hZ hCs hN hsec hthreshold) hW.le

end
end Candidate.FourthPower.MixedLocalizedDictionary
