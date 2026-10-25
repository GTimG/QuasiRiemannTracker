/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
 Old actual moment/count supplier at kappa=2*beta-1.
The only zero-supremum upper bound used is the original OpenAI 7/8 theorem.
ActualMoments and CountParameters are unchanged Cycle25 interfaces preserved
in PR69. No new mixed source, affine moment, improved incumbent, count estimate,
or final endpoint is a hypothesis. The last theorem supplies actual moments and
an actual Batch cardinality bound, uniformly before choosing the Batch.
-/
import Candidate.SilPrior.FourthPower.ReturnCountData
import Candidate.SilPrior.FourthPower.ReturnEnvelopeBridge
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.ActualMoments

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnOldCount
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFixedAmplitudeCount ProbeHighRowFamily ProbePhysical
open Cycle25ProbeFinalAssembly ReturnCountData

/-- The original unconditional OpenAI endpoint; no PR69 endpoint imported. -/
theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

def contraryKappa : ℝ := 2*HeckeZeroSupremum.beta-1

theorem contrary_gates (hβ : theta < HeckeZeroSupremum.beta) :
    7/10 ≤ contraryKappa ∧ contraryKappa ≤ 3/4 ∧
    51/100 ≤ HeckeZeroSupremum.beta := by
  have hhi := baseline_beta
  have hlo : (17/20 : ℝ) < theta := by norm_num [theta]
  dsimp only [contraryKappa]
  constructor
  · linarith
  constructor <;> linarith

/-- Exact identity with the exponent in the actual old detector count theorem. -/
theorem rowCount_eq_oldRatio {k δ p : ℝ} (hk : 7/10 ≤ k) (hkhi : k ≤ 3/4)
    (hδ : δ ∈ Icc 0 (3/4)) (hp : p ∈ Icc 0 (1/2)) :
    Cycle25DetectorRowCount.rowCount δ p k = oldN k δ p/oldJ k δ p := by
  calc
    _ = QRH.Record12518109Return.countingR k δ p :=
      (QRH.Record12518109Return.countingR_eq_actual hk).symm
    _ = oldN k δ p/oldJ k δ p :=
      (ReturnEnvelopeBridge.old_count_eq_upstream hk hδ hp).symm

/-- Actual weighted moments with the same source, mesh and saved amplifier pair. -/
theorem weighted_old_actual_moments {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (hβ : theta < HeckeZeroSupremum.beta)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        weighted_SourceMomentBound F contraryKappa counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨hk, hkhi, hbeta⟩ := contrary_gates hβ
  exact weighted_actual_source_moments F contraryKappa hk hkhi hbeta le_rfl counts hfine

/-- Cardinality bound for the actual source-profile Batch, not an abstract count
function. The explicit frequency-height condition permits arbitrary i and z;
future physical assembly chooses them within this already uniform statement. -/
def WeightedOldCountBound {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (η : Character) (Z τ C height K : ℝ) : Prop :=
  ∀ (rows : Finset FreeRow) (d a : ℝ), d0 ≤ d → d ≤ 7/8 →
    51/100 < a → a ≤ 7/8 →
    (∀ u ∈ rows, u.val ≠ 1 ∧ Z^(1/100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z^(d-D.t)) →
    ∀ (i : ℕ) (z : ℂ), z.re = 17/50 → |z.im| ≤ height →
    2*Real.pi*((Z^d)^(τ/(2*(7/8 : ℝ))))+(3*i : ℕ)*Z^τ ≤ height →
    ∀ (q : ℝ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε
        (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) contraryKappa)
        (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i),
    B.rows ⊆ rows → B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
    B.reverse = sourceMomentReverse F.modulus ⊤ → B.slots = Finset.univ →
    B.widths = (fun j => D.ell j/d) → B.profile = (fun _ y => (F.w y : ℂ)) →
    B.upper = (fun _ => 2) → B.external = (fun _ => z) →
    B.mesh = D.t → B.binWidth = D.t →
    (∀ u ∈ B.rows, ∀ j, B.family u j = sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u) j) →
    B.rows.Nonempty →
    (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (physical F.modulus ⊤ (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external
        (Z^d)) u = q) →
    (B.rows.card : ℝ) ≤
      (Fintype.card (Sum Bool (RayQuotient.Characters F.modulus ⊤)) : ℝ)*
      (dyadicLength (Z^d) : ℝ)^2*fiberConstant C height K*(Fintype.card B.Bin : ℝ)*
      (Z^d)^(oldN contraryKappa (2*a-1) (q/(2*a-1))/
          oldJ contraryKappa (2*a-1) (q/(2*a-1))+159*D.ε+D.t+B.mesh+7*D.t)

section
attribute [local irreducible] OAI.SevenEighths.HeckePrimeAmplitudeBins.labels
/-- Complete old supplier: parameters are saved before characters, scales,
heights, means and batches. Actual source moments are proved, then consumed by
the inherited balanced-count theorem. No moment/count/source assertion remains
as a hypothesis. All remaining premises are the contrary target and fine mesh. -/
theorem weighted_old_actual_count {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (hβ : theta < HeckeZeroSupremum.beta)
    (hfine : ∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200) :
    ∃ counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t,
    ∃ K J : ℝ, 0 ≤ K ∧ 0 ≤ J ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
          weighted_SourceMomentBound F contraryKappa counts η Z τ
            (C*(1+Z^(2*τ))^J) (Z^(2*τ)) ∧
          WeightedOldCountBound F η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) K := by
  obtain ⟨hk, hkhi, _⟩ := contrary_gates hβ
  obtain ⟨counts⟩ := weighted_fresh_count_parameters F
  obtain ⟨K, hK, hcount⟩ := counts.balanced
  obtain ⟨J, hJ, hmom⟩ := weighted_old_actual_moments F hβ counts hfine
  refine ⟨counts, K, J, hK, hJ, ?_⟩
  intro η
  obtain ⟨C, hC, hsource⟩ := hmom η
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτhi
  have hd0 : (0 : ℝ) < d0 := by norm_num [d0]
  filter_upwards [hsource τ hτ hτhi,
    eventually_all_rpow_ge hcount d0 hd0,
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) d0 hd0,
    eventually_ge_atTop (1 : ℝ)] with Z hm hcountZ hU hZ
  refine ⟨hm, ?_⟩
  intro rows d a hd hdhi ha hahi hrows i z hz hzh hfreq q B
    hsub hdata hreverse hslots hwidth hprofile hupper hexternal hmesh hbinWidth hfamily hne hq
  have hδ : 0 < 2*a-1 := by linarith
  have hδhi : 2*a-1 ≤ 3/4 := by linarith
  have hqrange := batch_mean_bounds B hne (by linarith) q hq
  have hp : q/(2*a-1) ∈ Icc 0 (1/2) := by
    constructor
    · exact div_nonneg hqrange.1 hδ.le
    · exact (div_le_iff₀ hδ).2 (by linarith [hqrange.2])
  have hmB := hm rows d a hd hdhi ha hahi hrows i z hz hzh q B
    hsub hdata hreverse hslots hwidth hprofile hupper hexternal hmesh hbinWidth hfamily
  have hcard := hcountZ d hd a D.ε (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ))))
    contraryKappa D.t (C*(1+Z^(2*τ))^J) (Z^(2*τ)) q i
    (hU d hd) ha hδhi D.epsilon_pos.le D.epsilon_small hk hkhi D.t_pos
    (by positivity) (by positivity) hfreq B hne hq hmB
  conv at hcard =>
    rhs
    arg 2
    arg 2
    rw [rowCount_eq_oldRatio hk hkhi ⟨hδ.le, hδhi⟩ hp]
  simpa only [← Nat.card_eq_fintype_card] using hcard

end
end
end Candidate.SilPrior.FourthPower.ReturnOldCount
