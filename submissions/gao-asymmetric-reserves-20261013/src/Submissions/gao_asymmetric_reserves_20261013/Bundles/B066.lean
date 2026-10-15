/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B015
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B030
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B054
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B060
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B062
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B063
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B065
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayCharacterFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedBandTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedRequests
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedSuccessorPacking
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowMemberBudget

/- BEGIN ORIGINAL MODULE Analytic.JointSecondFiberMass ; sha256 9b10ab1c69c8ce58ce9f98048e35ccfaf93c99ff28cf90992aa3bca3b395c5e6 -/
section


/-! The actual second-projector fiber is paid by its reduction factors.
Extraction numerators are bounded by the fixed source profile controls. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

def secondProfileScalar {ι : Type*} [Fintype ι] (s : Data ι) : ℝ :=
  Real.sqrt (2*(max 1 s.b₁*max 1 s.b₂)) * ∏ i, s.M i

theorem secondProfileScalar_nonneg {ι : Type*} [Fintype ι] (s : Data ι) :
    0 ≤ secondProfileScalar s :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg (fun i _ => (s.M_ge_one i).trans' zero_le_one))

theorem secondExtractionNumerator_sqrt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (L : Ideal O) (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) :
    Real.sqrt (secondExtractionNumerator s.M s.b₁ s.b₂ L a) ≤ secondProfileScalar s := by
  have hM (i : ι) : 0 ≤ s.M i := zero_le_one.trans (s.M_ge_one i)
  have hp : 0 ≤ ∏ i ∈ frozenIndices L a, s.M i := Finset.prod_nonneg (fun i _ => hM i)
  unfold secondExtractionNumerator secondProfileScalar
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _ => hM i) (fun i _ _ => s.M_ge_one i)

theorem secondAllocationScalar_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation L (Finset.univ : Finset (κ ⊕ Fin 2))) :
    secondAllocationScalar s v L a b ≤
      (1/Real.sqrt (formalReductionFactor L a s.P*formalReductionFactor L b v.P)) *
        (secondProfileScalar s*secondProfileScalar v) :=
  mul_le_mul_of_nonneg_left (mul_le_mul
    (secondExtractionNumerator_sqrt_le s L a) (secondExtractionNumerator_sqrt_le v L b)
    (Real.sqrt_nonneg _) (secondProfileScalar_nonneg s)) (by positivity)

/-- The complete second-projector/active-allocation scalar sum is proved
from the source shell theorem. No fiber mass or count premise is used. -/
theorem actual_second_scalar_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℝ) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J K : Finset ι) (s : Data J) (v : Data K),
      (∀ i : J, s.lo i = lo i) → (∀ i : J, s.hi i = hi i) →
      (∀ i : K, v.lo i = lo i) → (∀ i : K, v.hi i = hi i) →
      ∀ Ds : Finset (Ideal O),
      (∀ L ∈ Ds, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^B) →
      (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
        ∑ a ∈ s.toSource.active L, ∑ b ∈ v.toSource.active L,
          secondAllocationScalar s v L a b) ≤
        C*Z^δ*(secondProfileScalar s*secondProfileScalar v) := by
  obtain ⟨C,hC,hmass⟩ := actual_second_allocation_mass lo hi B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro J K s v hslo hshi hvlo hvhi Ds hcap
  calc
    _ ≤ ∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
        ∑ a ∈ s.toSource.active L, ∑ b ∈ v.toSource.active L,
          (1/Real.sqrt (formalReductionFactor L a s.P*formalReductionFactor L b v.P)) *
            (secondProfileScalar s*secondProfileScalar v) := by
      apply Finset.sum_le_sum
      intro L hL
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => secondAllocationScalar_le s v L a b))
    _ = (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
        ∑ a ∈ s.toSource.active L, ∑ b ∈ v.toSource.active L,
          1/Real.sqrt (formalReductionFactor L a s.P*formalReductionFactor L b v.P)) *
            (secondProfileScalar s*secondProfileScalar v) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hZ.2 J K s.toSource v.toSource hslo hshi hvlo hvhi Ds hcap)
      (mul_nonneg (secondProfileScalar_nonneg s) (secondProfileScalar_nonneg v))

#print axioms actual_second_scalar_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondFiberMass -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.CappedAnalyticSuccessor ; sha256 825a6ac4c27ad33f89e186634b22544ff7d20a3d3b0f1ecc146054e079d6a5fe -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/CappedAnalyticSuccessor.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: κ ≥ 7/10 positive stages; complete zero-slot endpoint supplied independently.
-/









namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyCappedAnalyticSuccessor
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands Cycle25CenteredMomentEnergyPositiveHighBound
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyStageMonotonicity
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyCappedRequests
open CenteredMomentEnergySourceCapSchedule CenteredMomentNaturalFixedRaySource
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_successor
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ:(7/10:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (k:ℕ)(hk:k< count Mcap ε)
    (hold:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let ac:=lowerAt a b Mcap ε (k+1)
  let Lc:=lengthAt Mcap Bmask L ε (k+1)
  let Lp:=lengthAt Mcap Bmask L ε k
  let Lreq:=requestLength Mcap Bmask Lc
  let A:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let r:=reserve Mcap Bs ε
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
  have hκ0:0≤κ:=by linarith
  have hb:0≤ b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε).2.2.2.1
  have hr1:r/4≤1:=by
    have hh:=bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε
    have hrs:r≤ amplification ε/100:=min_le_left _ _
    linarith [hh.2.1]
  have hMp:0≤ Mp:=bandWidth_nonneg Mcap Bs ε hMcap.le hBs hε _
  have hMc:0< Mc:=band_positive Mcap Bs ε hMcap hBs hε k
  have hMpM:Mp≤ Mcap:=bandWidth_le _ _ _ _
  have hMcM:Mc≤ Mcap:=bandWidth_le _ _ _ _
  have hac:0< ac:=lowerAt_pos a b Mcap ε ha _
  have haca:ac≤ a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
  have haclo:ac≤1/4:=haca.trans hlo
  have hLc:0≤ Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hLp:0≤ Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask hLc
  have hreqFinal:Lreq≤ range Mcap Bmask L (count Mcap ε):=
    request_le_final Mcap Bmask L ε hMcap.le hmask k hk
  have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)
  have hA:0≤ A:=by dsimp [A];positivity
  have hMA:Mp≤ A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)]
  have hready:readyBudget A Bmask≤ Bs:=
    readyBudget_le_schedule Mcap Bmask L ε A Bmask hMcap.le hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤ Mc:=parent_drop Mcap Bs ε hε k
  have hmesh:0≤ fineMesh Mcap Bmask L κ ε:=
    (fineMesh_pos Mcap Bmask L κ ε hMcap.le hmask hκ0 hε).le
  have hsupport:lowerAt a b Mcap ε k=ac/max 1 b:=child_support a b Mcap ε k hk
  have hrequest:2*max Lreq Mp+r/4≤ Lp:=previous_admits Mcap Bmask L ε Mp (r/4)
    hMcap.le hmask hMpM hr1 k hk
  have hhighL:max Lc Mp≤ Lp:=by
    have hh:max Lc Mp≤ Lreq:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
    have hg:0≤ max Lreq Mp:=hreq.1.trans (le_max_left _ _)
    have hx:=le_max_left Lreq Mp
    linarith
  have href:Mp+Bmask+Mc/100≤ Lreq:=by
    have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hmask hMpM hMcM (by norm_num)
    exact (le_max_right _ _).trans hh
  obtain ⟨Jold,Sold,hprev⟩:=hold
  obtain ⟨Slow,Jlow,hlow⟩:=Cycle25CenteredMomentEnergyCappedLowStage.actual_capped_low (α:=α) M H hH
    W aslot bslot a b radial Bmask L lo hi Mcap κ ε hW haslot hWs hbslot ha hb hrad
    hmask hMcap.le hκ hε hbeta hκbeta k hk ⟨Jold,Sold,hprev⟩
  obtain ⟨Uhigh,Jhigh,hhigh⟩:=Cycle25CenteredMomentEnergyNaturalHighStage.actual_high_stage (α:=α) M H hH
    W hW aslot bslot lo hi ac b radial haslot hWs hbslot hac haclo hhi (by linarith)
    Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L κ ε) Mc κ ε k hMc hMcap.le hA hBs hmask
    hMp hMc.le hLc hmesh hMA hready hκ hbeta hκbeta hε le_rfl hdrop Jold Sold Jlow Slow
  have hzeroLoss : 0 < stageLoss Mcap Bs ε (k+1) :=
    stageLoss_pos Mcap Bs κ ε hMcap.le hBs hκ0 hε (k+1)
  obtain ⟨Jzero,Uzero,hzero⟩ :=
    ZetaZeroFree.Analytic.Moments.Unconditional.nonfixed_zero_at M ac b radial Bmask Lc
      (max 1 Mp) (stageLoss Mcap Bs ε (k+1)) hac haclo hhi (by linarith) hmask
      (zero_lt_one.trans_le (le_max_left _ _)) hzeroLoss
  have hmarg:=margins Mcap Bs κ ε hMcap.le hBs hκ0 hε k
  apply CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages (α:=α) M H hH
    W bslot a b radial Bmask L lo hi Mcap κ ε ha hmask hMcap.le hκ0 hε k
    (stageLoss Mcap Bs ε (k+1)) (physicalLoss Mcap Bs ε k) (reflectedLoss Mcap Bs ε k)
    le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 ⟨Jold,Sold,hprev⟩
  · refine ⟨Jzero,Uzero,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Cz,hCz,hzeroZ⟩ := hzero η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Cz,hCz,?_⟩
    filter_upwards [hzeroZ] with Z hz
    exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      Jzero Jzero Uzero Uzero Cz Cz hz.1.le le_rfl le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) le_rfl le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz.2
  · refine ⟨Jlow,Slow,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Clow,hClow,?_⟩
    filter_upwards [hlowZ] with Z hl
    exact positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask Lc Mp (physicalLoss Mcap Bs ε k) η₀ Q Jlow Jlow Slow Slow Clow Clow
      hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
  · refine ⟨Jhigh,Uhigh,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Ch,hCh,hhighZ⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Ch*(C₀+C₁+Clow+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hzSmall:=zeroAt_transport (internalQ Q η₀)
      (ac/max 1 b) b radial Bmask Lp Mc (stageLoss Mcap Bs ε k) Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k)
      Jold Jold Sold Sold C₀ C₀ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₀.le le_rfl hzz
    have hpSmall:=positiveAt_transport (α:=α) M H hH W bslot
      (ac/max 1 b) b radial Bmask Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k) κ Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k) η₀ Q
      Jold Jold Sold Sold C₁ C₁ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₁.le le_rfl hpp
    have hlRestricted:=positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs ε k) η₀ Q
      Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    exact hh.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.Cycle25CenteredMomentEnergyCappedAnalyticSuccessor

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.CappedAnalyticSuccessor -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.AmplitudeLoss ; sha256 f38dbe7847252215d83171a700e752416f150ead80e00bf68545ef414dbde4fe -/
section


/-! Upper amplitude-bin slack is restored after the packet estimate, without
changing the diluted lower-bin mean used by either the count or the capacity. -/
noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem upper_bin_normalized (P : ℂ) (U a loss : ℝ) (hU : 0 < U)
    (hP : ‖P‖ ≤ U^(a+loss)) :
    ‖P / ((U^loss : ℝ) : ℂ)‖ ≤ U^a := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU _)).mpr
  simpa only [Real.rpow_add hU] using hP

theorem restore_upper_bin_loss {ι : Type*} (s : Finset ι) (S P : ι→ℂ)
    (U loss E C : ℝ) (hU : 0 < U)
    (hb : (∑ i ∈ s, ‖S i * (P i / ((U^loss : ℝ) : ℂ))‖) ≤ C*U^E) :
    (∑ i ∈ s, ‖S i*P i‖) ≤ C*U^(E+loss) := by
  have he : (∑ i ∈ s, ‖S i * (P i / ((U^loss : ℝ) : ℂ))‖) =
      (∑ i ∈ s, ‖S i*P i‖) / U^loss := by
    simp_rw [←mul_div_assoc,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
    exact (Finset.sum_div _ _ _).symm
  rw [he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU loss)).mp hb
  simpa only [mul_assoc,←Real.rpow_add hU] using hh

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.AmplitudeLoss -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowMemberBudget ; sha256 ab2ec9053e4f859bc01ac07ebcc77b1610af0b8d5a69865cd576a3e538d1f337 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowMemberBudget.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_member_tuple_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤ Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤ Z^Lrow → (QP/2)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤ Z^Lcap → QK≤ Z^Lcap → QP≤ Z^Lcap → -saving≤((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_global_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows tuples hne hmax hgood hinj
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  obtain ⟨D,hD⟩ := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  convert he using 1
  apply Finset.sum_congr rfl
  intro K hK
  congr 2
  exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw).symm
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowMemberBudget -/

/- BEGIN ORIGINAL MODULE Global.Transport.CanonicalRayCube ; sha256 5dfdfdad4867f9b0cb714dc561c653b0324790efb15a999acbc82475469f3e4e -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)


theorem canonical_probe_exists_ray_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∃n : ℕ,0 < n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) T hT W (fun i=> Z^(length i))
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,n,hn,hchoice⟩ := canonical_probe_exists_cube (ι:=RayQuotient.Characters M H)
    K e δ a b B ζ saving τ he he' hδ hδ' hζ hζ' hτ ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ,
    ProbeRayCharacterFamily.large_supported_twists_eventually M (1/100) (by norm_num)]
    with Z hZ hlarge
  intro η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨idx,grid,hlabel,hbins,herror⟩ := hchoice η Z hZ.1 hZ.2 T hT hdis length hl0 hl hpool W hWS hWB
    (rayCubeFamily M H hH)
  refine ⟨idx,grid,hlabel,hbins,?_,herror⟩
  intro u hu hcal
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hcal
  have hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1 :=
    hlarge u (mem_rowBand.mp hu).2.1 hs H hH
  refine ⟨hnp,?_,?_⟩
  · exact ProbeRayCharacterFamily.raw_twisted_conductor M H hH u
  · intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates S hS.prime η u
      (rayCubeFamily M H hH u) hnp' _).trans_lt (hbins u).2.2.2.2.1

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CanonicalRayCube -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalPairIdentity ; sha256 145524e8fefb7ed847895ed556f66fb511fc2f996402ad1e62dc5ed36b31de0b -/
section


/-! Actual exceptional first children, with source-derived normalization,
profile control and the local negative exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstChildProfileControl CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondExceptionalUniformSource CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondEnergySplit
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open ConcretePrimeRowBridge RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointExceptionalPairIdentityDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance jointExceptionalPairIdentityDecEq2 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectors
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentFirstMixedRightTransport
open CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate

lemma canonical_allocation_pair_root
    (qL qR V C D Z bL bR : ℝ)
    (hqL : 0 < qL) (hqR : 0 < qR) (hV : 0 < V) (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z) :
    Real.sqrt (qL*(V/C^2)*Z^bL)*Real.sqrt (qR*(V/D^2)*Z^bR) =
      V/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2) := by
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  · simp (disch := positivity) only [Real.log_sqrt,Real.log_mul,Real.log_div,
      Real.log_pow,Real.log_rpow]
    ring

lemma canonical_allocation_pair_cancel
    (k qL qR V C D Z bL bR x y : ℝ)
    (hqL : 0 < qL) (hqR : 0 < qR) (hV : 0 < V) (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (k*V/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2))*
      (Real.sqrt (x/(qL*(V/C^2)*Z^bL))*Real.sqrt (y/(qR*(V/D^2)*Z^bR))) =
      k*Real.sqrt x*Real.sqrt y := by
  have he := canonical_allocation_pair_root qL qR V C D Z bL bR hqL hqR hV hC hD hZ
  rw [Real.sqrt_div hx,Real.sqrt_div hy]
  calc
    _ = k*(Real.sqrt (qL*(V/C^2)*Z^bL)*Real.sqrt (qR*(V/D^2)*Z^bR))*
        ((Real.sqrt x/Real.sqrt (qL*(V/C^2)*Z^bL))*(Real.sqrt y/Real.sqrt (qR*(V/D^2)*Z^bR))) := by
      rw [he]
      ring
    _ = _ := by field_simp

lemma allocatedMainExceptionalEnergy_nonneg
    {Slot : Type*} [Fintype Slot]
    (s : Input Slot) (C Rmask seed : Ideal O) (τ : Character) (t b Z : ℝ)
    (Q : Ideal O) (ray : RayCharacter) (m : O) (Rmain Tsec ξ : ℝ) (hZ : 0 ≤ Z) :
    0 ≤ allocatedMainExceptionalEnergy s C Rmask seed τ t b Z Q ray m Rmain Tsec ξ := by
  unfold allocatedMainExceptionalEnergy
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro B _
  split_ifs
  · have hv := CenteredMomentAmplificationChildInput.volume_pos (child s C Rmask B τ t)
    positivity
  · exact le_rfl

/-- Exact cancellation of the canonical allowance normalizers. Thus the
weighted pairing in the final exceptional estimate is the literal first
source scalar times the two actual allocated energy square roots. -/
theorem allowance_weight_pair_eq_source_scalar
    {Slot : Type*} [Fintype Slot]
    (s : Input Slot) (R seed : Ideal O) (m A : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K r Z : ℝ) (hZ : 0 < Z)
    (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2)) (τ₁ τ₂ : Character)
    (n : Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let h := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    allowanceWeight s R seed m A t W V K r Z p E τ₁ τ₂ n *
      (Real.sqrt (x/((τ₁.modulus.absNorm : ℝ)*
        (CenteredMomentAmplificationChildInput.volume s/(p.val.1.absNorm : ℝ)^2)*Z^(allowance p.val.1 p.val.2 Z)))*
       Real.sqrt (y/((τ₂.modulus.absNorm : ℝ)*
        (CenteredMomentAmplificationChildInput.volume s/(p.val.2.absNorm : ℝ)^2)*Z^(allowance p.val.2 p.val.1 Z)))) =
    if block s.η m A t (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) p.val.1 p.val.2 h.1 h.2 E
      (CenteredMomentSecondRetainedRows.retainedRows r 1) W V K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) = 0 then 0
    else ‖scalar p.val.1 p.val.2 h.1 E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*
      Real.sqrt x*Real.sqrt y := by
  intro h
  unfold allowanceWeight weight
  dsimp only
  split_ifs
  · simp only [zero_mul]
  · have hvEq : CenteredMomentExceptionalAmplitudePair.volume s.toData =
        CenteredMomentAmplificationChildInput.volume s := by
      unfold CenteredMomentExceptionalAmplitudePair.volume CenteredMomentAmplificationChildInput.volume
      ring
    rw [hvEq]
    exact canonical_allocation_pair_cancel _ _ _ _ _ _ _ _ _ x y
      (norm_pos _ τ₁.modulus_ne_bot) (norm_pos _ τ₂.modulus_ne_bot)
      (CenteredMomentAmplificationChildInput.volume_pos s) (norm_pos _ h.1.1) (norm_pos _ h.2.1)
      hZ hx hy

#print axioms allowance_weight_pair_eq_source_scalar
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalPairIdentity -/
