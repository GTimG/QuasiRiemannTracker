/- Copyright (c) 2026 Sil. Apache-2.0.
Exact localization of the completed fourth-power family. The zero mode
has prefactor 16 K W^3; the retained and discarded sums keep the original
correlations and the fourth-power Fourier radius. No moment is assumed.
-/
import Candidate.FourthPower.MixedPoissonCompletion
import Candidate.FourthPower.MixedSecondProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstLocalization

set_option autoImplicit false
namespace Candidate.FourthPower.MixedPoissonLocalization
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss CenteredMomentGaussEnergy
open CenteredMomentFirstAmplificationChoice ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSupportedCorrelation CenteredMomentSectorLocalization
open CenteredMomentFirstLocalization CenteredMomentSecondDiagonal
open MixedPoissonCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def zeroDensity {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ) (K W : ℝ) : ℂ :=
  ((16*K*W^3:ℝ):ℂ)*paperRadialFourier ballProfile 0*secondZeroEnergy S a ha b

def localizedDensity {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ) (K W : ℝ) (ρ : ℝ→ℝ) : ℂ :=
  ∑i∈S,∑j∈S,(b i*star (b j))*
    (((16*K*W^3:ℝ):ℂ)/
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}):ℝ):ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}):ℝ):ℂ)))*
    ∑'h : O,(ρ (normValue h):ℂ)*actualCorrelation (a i) (a j) (ha i) (ha j) (-h)*
      paperRadialFourier ballProfile
        (16*K*W^4*‖eisEmbedding h‖^2/‖eisEmbedding (a i*a j)‖^2)

theorem density_split {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ)
    (K W R : ℝ) (hK : 0<K) (hW : 0<W) :
    secondPoissonDensity S a ha b K W=
      zeroDensity S a ha b K W+
      localizedDensity S a ha b K W (retainedWeight R)+
      localizedDensity S a ha b K W (discardedWeight R) := by
  unfold secondPoissonDensity zeroDensity localizedDensity secondZeroEnergy
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : a i*a j≠0 := mul_ne_zero
    (supported_element_ne_zero _ (ha i)) (supported_element_ne_zero _ (ha j))
  have hn : 0<‖eisEmbedding (a i*a j)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hij))
  have hk : 0<(16*K*W^4)/‖eisEmbedding (a i*a j)‖^2 := div_pos (by positivity) hn
  have hs := lattice_fourier_split ballProfile _ hk
    (fun h=>actualCorrelation (a i) (a j) (ha i) (ha j) (-h))
    _ (fun h=>CenteredMomentTail.actualCorrelation_norm_le _ _ (ha i) (ha j) (-h)) R
  have he (h : O) :
      16*K*W^4*‖eisEmbedding h‖^2/‖eisEmbedding (a i*a j)‖^2=
        ((16*K*W^4)/‖eisEmbedding (a i*a j)‖^2)*normValue h := by
    rw [normValue_eq_embedding]
    ring
  simp_rw [he]
  rw [hs]
  simp only [neg_zero]
  ring

theorem zero_density_norm_le {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i}))
    (hp : ∀i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hinj : Set.InjOn a S) (b : ι→ℂ)
    (K W : ℝ) (hK : 0≤K) (hW : 0≤W) :
    ‖zeroDensity S a ha b K W‖ ≤
      (16*K*W^3)*‖paperRadialFourier ballProfile 0‖*∑i∈S,‖b i‖^2 := by
  rw [zeroDensity,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (secondZeroEnergy_bound S a ha hp hinj b) (by positivity)

/-- Combine the exact split and its proved diagonal bound. The remaining
two terms are literal Fourier sums, not opaque moment hypotheses. -/
theorem density_re_le {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i}))
    (hp : ∀i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hinj : Set.InjOn a S) (b : ι→ℂ)
    (K W R : ℝ) (hK : 0<K) (hW : 0<W) :
    (secondPoissonDensity S a ha b K W).re ≤
      (16*K*W^3)*‖paperRadialFourier ballProfile 0‖*∑i∈S,‖b i‖^2+
      ‖localizedDensity S a ha b K W (retainedWeight R)‖+
      ‖localizedDensity S a ha b K W (discardedWeight R)‖ := by
  rw [density_split S a ha b K W R hK hW]
  simp only [Complex.add_re]
  exact add_le_add
    (add_le_add ((Complex.re_le_norm _).trans
      (zero_density_norm_le S a ha hp hinj b K W hK.le hW.le)) (Complex.re_le_norm _))
    (Complex.re_le_norm _)

end
end Candidate.FourthPower.MixedPoissonLocalization
