/- Copyright (c) 2026 Sil. Apache-2.0.
Positive energy of the actual first residual, after genuine extraction.
The artificial divisor remains the original seed of every live source.
-/
import Candidate.FourthPower.MixedFirstLiveSource
import Candidate.FourthPower.MixedPoissonCompletion
import Candidate.FourthPower.MixedPoissonLocalization

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstLiveEnergy
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedCommonCoefficient
open MixedCommonRestriction MixedLiteralAllocation MixedOriginalSecondZero MixedFirstLiveSource
open MixedPoissonCompletion
open MixedPoissonLocalization CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- This bounds the full positive energy, not its individual signed
Fourier pieces. The profile is only required to be nonnegative on rows. -/
theorem actual_common_energy (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (C G seed D : Id)
    (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C=
      QRH.Record1252270103KernelMass.primeSupport G) (hseed : seed∣G)
    (τ : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (gaussEnergy Finset.univ
      (CenteredMomentFirstPhysicalSource.element C G hG.1 (sourceColumns s))
      (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 (sourceColumns s))
      (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 (sourceColumns s)=>
        originalResidual s ha seed G D I*heightCoeff τ t I) Φ K).re≤
      ((actualAllocations (tuplePools s) G).card:ℝ)*
        ∑B : actualAllocations (tuplePools s) G,
          ‖frozenWeight (punctureProduct s.S s.H) B.val*
            frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2*
          (sourceGaussEnergy (sourceColumns (allocatedLiveSource s hb cover G B))
            (sourceCoefficient (allocatedLiveSource s hb cover G B) ha D)
            (heightCoeff τ t) Φ K).re := by
  have hs := gaussEnergy_hasSum_re Finset.univ
    (CenteredMomentFirstPhysicalSource.element C G hG.1 (sourceColumns s))
    (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 (sourceColumns s))
    (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 (sourceColumns s)=>
      originalResidual s ha seed G D I*heightCoeff τ t I) Φ K hK
  rw [←hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (sq_nonneg _) (hΦ z))
  intro rows
  let w := fun B : actualAllocations (tuplePools s) G=>
    frozenWeight (punctureProduct s.S s.H) B.val*frozenCoefficient B.val G s.R s.ν s.Wslot s.P
  let f := fun (B : actualAllocations (tuplePools s) G) (z : O)=>
    gaussPolynomial Finset.univ
      (sourceGenerator (sourceColumns (allocatedLiveSource s hb cover G B)))
      (sourceGenerator_supported (sourceColumns (allocatedLiveSource s hb cover G B)))
      (fun I : supportedColumns (sourceColumns (allocatedLiveSource s hb cover G B))=>
        sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I*heightCoeff τ t I) z
  calc
    _≤∑z∈rows,((actualAllocations (tuplePools s) G).card:ℝ)*
      ∑B : actualAllocations (tuplePools s) G,‖w B‖^2*
        (‖f B z‖^2*(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [first_gauss_live_sources s ha hb cover C G seed D hC hG hCG hseed τ t z]
      have hh := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ (fun B=>w B*f B z)) (hΦ z)
      simpa only [w,f,Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hh
    _=((actualAllocations (tuplePools s) G).card:ℝ)*
      ∑B : actualAllocations (tuplePools s) G,‖w B‖^2*
        ∑z∈rows,‖f B z‖^2*(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_gaussEnergy Finset.univ
          (sourceGenerator (sourceColumns (allocatedLiveSource s hb cover G B)))
          (sourceGenerator_supported (sourceColumns (allocatedLiveSource s hb cover G B)))
          (fun I : supportedColumns (sourceColumns (allocatedLiveSource s hb cover G B))=>
            sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I*heightCoeff τ t I)
          Φ K hK hΦ rows) (sq_nonneg _)

/-- The four components of a canonical live source. The exceptional term
is a literal complex summand chosen by the caller, not a bound assumed
for it. In application it is the actual exceptional physical part / W.
All four components of every allocation must be included after Cauchy. -/
theorem live_density_four_parts (s : Source ι a b) (ha : 0<a) (D : Id)
    (τ : Character) (t K W R : ℝ) (hK : 0<K) (hW : 0<W) (exceptional : ℂ) :
    (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha D)
      (heightCoeff τ t) ballProfile (16*K*W^4)).re/W≤
      ‖zeroDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha D I*heightCoeff τ t I)
        K W‖+
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha D I*heightCoeff τ t I)
        K W (retainedWeight R)-exceptional‖+‖exceptional‖+
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha D I*heightCoeff τ t I)
        K W (discardedWeight R)‖ := by
  have he := congrArg Complex.re (density_normalized_poisson Finset.univ
    (sourceGenerator (sourceColumns s)) (sourceGenerator_supported (sourceColumns s))
    (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha D I*heightCoeff τ t I)
    K W hK hW)
  simp only [Complex.div_ofReal_re] at he
  change (gaussEnergy _ _ _ _ _ _).re/W≤_
  rw [he,density_split _ _ _ _ K W R hK hW]
  simp only [Complex.add_re]
  have hs : ∀z : ℂ,z.re≤‖z-exceptional‖+‖exceptional‖ := by
    intro z
    calc
      z.re=(z-exceptional).re+exceptional.re := by simp
      _≤_ := add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
  have hbound (z r v : ℂ) : z.re+r.re+v.re≤
      ‖z‖+‖r-exceptional‖+‖exceptional‖+‖v‖ := by
    have hh := add_le_add (add_le_add (Complex.re_le_norm z) (hs r))
      (Complex.re_le_norm v)
    simpa only [add_assoc] using hh
  exact hbound _ _ _

end
end Candidate.FourthPower.MixedFirstLiveEnergy
