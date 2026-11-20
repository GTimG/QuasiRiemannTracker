/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual second-Poisson zero and discarded sums. Native Sil estimates retain
   the zero term's harmonic seed sum and the discarded term's full seed count. -/
import Candidate.C092.transport.RootColoredSeed
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteDiagAssembly
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeometry7

set_option autoImplicit false
namespace QRH.Cycle092.RootColoredSeed
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Original second zero, summed with the true reciprocal seed weights. -/
theorem zero_terms_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] (a b : ℝ) (r : Source ι a b), Fintype.card ι ≤ N →
    ∀ (ha : 0 < a) (η₁ η₂ : Character) (V : Finset Id) (hV : ∀ v ∈ V, v ≠ 0)
      (ψ : Character) (t K Y X : ℝ),
      0 ≤ K → 1 ≤ Y → 3 ≤ X → sourceNormCap r.P b r.T r.d ≤ Y →
      (∀ v ∈ V, (v.absNorm : ℝ) ≤ X) →
      zeroTerms r ha (idealCoeff η₁) (idealCoeff η₂) V ψ t K ≤
        K * ‖EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0‖ *
          (C * profileCap r^2 * Y^(1+ε)) * (2304 * Real.log X) := by
  obtain ⟨C,hC,h⟩ := QRH.Cycle092.TwistedRawSource.source_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ a b r hN ha η₁ η₂ V hV ψ t K Y X hK hY hX hcap hVX
  have hterm (v : Id) (hv : v ∈ V) :
      ‖(K : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0 *
        CenteredMomentSourceSecondZeroEnergy.sourceSecondZero (sourceColumns r)
          (TwistedRawSource.sourceColumn r ha (idealCoeff η₁) (idealCoeff η₂) v) ψ t‖ ≤
      (K * ‖EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0‖ *
        (C * profileCap r^2 * Y^(1+ε))) * (1/(v.absNorm : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
    have hvb := h r hN ha η₁ η₂ v (hV v hv) ψ t Y hY hcap
    refine (mul_le_mul_of_nonneg_left hvb (by positivity)).trans_eq ?_
    ring
  unfold zeroTerms
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (recip_sum_le X hX V hV hVX) (by positivity)

/-- The discarded second term uses arbitrary saving uniformly in every seed;
    summing it pays its actual finite cardinality, with no harmonic shortcut. -/
theorem tail_terms_bound (B ξ saving : ℝ) (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type) [Fintype ι] (a b : ℝ) (r : Source ι a b) (ha : 0 < a), 0 ≤ b →
    ∀ (η₁ η₂ : Character) (V : Finset Id) (ψ : Character) (t K W X Tsec : ℝ),
      0 < K → 0 < W → 0 < X → poolCap r ≤ Z^B → sourceNormCap r.P b r.T r.d ≤ X →
      X ≤ Z^B → K ≤ Z^B → W ≤ Z^B → W⁻¹ ≤ Z^B → Tsec ≤ Z^B →
      X^2/(16*K*W^4) ≤ Tsec →
      tailTerms r ha (idealCoeff η₁) (idealCoeff η₂) V ψ t (16*K*W^4) Tsec Z ξ ≤
        (V.card : ℝ) * W * (C * profileCap r^2 * Z^(-saving)) := by
  obtain ⟨control,C,hC,h⟩ := QRH.Cycle092.TwistedRawSource.source_tail_arbitrary_saving
    B ξ saving hB hξ
  let D : ℝ := C * (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile + 1
  have hs : 0 ≤ (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile := apply_nonneg _ _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,h.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ a b r ha hb η₁ η₂ V ψ t K W X Tsec hK hW hX hp hc hXc hKc hWc hWic hTc hscale
  have hseed (v : Id) :
      ‖CenteredMomentSupportedTailAggregate.secondDiscardedEnergy ψ t (sourceColumns r)
        (TwistedRawSource.sourceColumn r ha (idealCoeff η₁) (idealCoeff η₂) v) ballProfile (16*K*W^4) Tsec Z ξ‖ ≤
      W * (D * profileCap r^2 * Z^(-saving)) := by
    refine (hZ.2 r ha hb η₁ η₂ v ψ t K W X Tsec hK hW hX hp hc hXc hKc hWc hWic hTc hscale).trans ?_
    apply mul_le_mul_of_nonneg_left _ hW.le
    have hCD : C * (control.sup (schwartzSeminormFamily ℝ ℝ ℂ)) ballProfile ≤ D := by dsimp [D]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hCD
      (mul_nonneg (sq_nonneg (profileCap r)) (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le (-saving)))]
  unfold tailTerms
  exact (Finset.sum_le_sum (fun v _ => hseed v)).trans_eq (by simp; ring)

#print axioms zero_terms_bound
#print axioms tail_terms_bound
end
end QRH.Cycle092.RootColoredSeed
