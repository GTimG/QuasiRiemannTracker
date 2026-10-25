/- Copyright (c) 2026 Sil. Apache-2.0.
Actual retained child upper cap and exact second-cutoff caps. Kchild may
be below one; its polynomial inverse is supplied by RepairedRootCaps.

-/
import Candidate.SilPrior.FourthPower.RepairedDescendantCaps

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedChildCaps
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate CenteredMomentFirstScale
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstCutoffs MixedFirstExceptionalNormalization
open OuterFreshCutoffAllowance RepairedRootParameters RepairedRawContext RepairedRootCaps RepairedCapEvent
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem cutoff_le_one (N : ℕ) (ε : ℝ) (hε : 0 < ε) : cutoffLoss N ε ≤ 1 := by
  have hi := (internal_spec N ε hε).2.2.1
  have ho := (omega_spec ε hε).2.2.2
  unfold cutoffLoss
  linarith

theorem second_cutoff_caps {κ : Type u} [Fintype κ] (r : Source κ (1/4) (9/4))
    (Z K pad : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hpad : pad ≤ 1)
    (hEnv : secondSourceEnvelope r ≤ Z^(2:ℝ)) (hInv : K⁻¹ ≤ Z^(10:ℝ)) :
    0 < secondSourceEnvelope r ∧ 0 < secondSourceCutoff r K ∧
      secondSourceCutoff r K ≤ Z^(14:ℝ) ∧
      frequencyRadius (secondSourceCutoff r K) Z pad ≤ Z^(15:ℝ) := by
  have hz := zero_lt_one.trans hZ
  have hE : 0 < secondSourceEnvelope r := mul_pos (capConstant_pos _ _) (effectiveVolume_pos r)
  have hT : 0 < secondSourceCutoff r K := div_pos (sq_pos_of_pos hE) hK
  have hTc : secondSourceCutoff r K ≤ Z^(14:ℝ) := by
    calc
      _ = (secondSourceEnvelope r)^2*K⁻¹ := by unfold secondSourceCutoff; ring
      _ ≤ (Z^(2:ℝ))^2*Z^(10:ℝ) :=
        mul_le_mul (pow_le_pow_left₀ hE.le hEnv 2) hInv (inv_nonneg.mpr hK.le) (sq_nonneg _)
      _ = _ := by rw [pow_two, ← Real.rpow_add hz, ← Real.rpow_add hz]; norm_num
  have hpadpow : Z^(pad/2) ≤ Z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (show pad/2 ≤ (1:ℝ) by linarith)
  refine ⟨hE,hT,hTc,?_⟩
  unfold frequencyRadius
  apply (mul_le_mul hTc hpadpow (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)).trans_eq
  rw [show (15:ℝ)=14+1 by norm_num, Real.rpow_add hz, Real.rpow_one]

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀)

theorem child_upper_cap (hε : 0 < ε) (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z)
    (p : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1))
    (E : Finset (CommonIndex p.val.1 p.val.2)) (τ : Character)
    (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex p.val.1 p.val.2 => P.val) E*activeConductor p.val.1 p.val.2})
    (n : ℤ) (hret : Retained (frequencyRadius (firstCutoff p.val.1 p.val.2 E d.Kroot (sourceVolume d.root))
      Z (cutoffLoss N ε)) n) :
    nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss N ε) n ≤ Z^(9:ℝ) := by
  have hz := zero_lt_one.trans d.one_lt_Z
  have hs := commonLabels_supported _ _ _ p.property
  have hCD : CompletedGauss.primeSupport p.val.1 = CompletedGauss.primeSupport p.val.2 :=
    (commonLabels_data _ _ _ _ p.property).2.2
  have hτcap := first_modulus_cap M H hH d hcard hevent.dimension hevent.presentation p E τ hmod
  have hτpos : 0 < (τ.modulus.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hτlog := Real.logb_le_logb_of_le d.one_lt_Z hτpos hτcap
  rw [Real.logb_rpow hz d.one_lt_Z.ne'] at hτlog
  have hvlog := Real.logb_le_logb_of_le d.one_lt_Z (sourceVolume_pos d.root) (root_volume_cap M H hH d)
  rw [Real.logb_self_eq_one d.one_lt_Z] at hvlog
  have hclog := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le hs.1.1)
  have hKlog : 1 ≤ Real.logb Z d.Kroot := by
    simpa only [Real.logb_self_eq_one d.one_lt_Z] using Real.logb_le_logb_of_le d.one_lt_Z hz d.hKlow
  have hηlog := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le η.modulus_ne_bot)
  have hFlog := Real.logb_nonneg d.one_lt_Z fixed_presentation_one_le
  have hR : 1 ≤ inputWidth η d.Kroot Z := by unfold inputWidth; linarith
  have hpad : 0 ≤ cutoffLoss N ε := (internal_losses_paid N ε hε).1.le
  have hpad1 := cutoff_le_one N ε hε
  have he := retained_child_log η τ p.val.1 p.val.2 hs.1 hs.2 hCD E d.Kroot (sourceVolume d.root) Z
    (firstCutoff p.val.1 p.val.2 E d.Kroot (sourceVolume d.root)) 1 (cutoffLoss N ε) (cutoffLoss N ε)
    d.radial_pos (sourceVolume_pos d.root) d.one_lt_Z (by norm_num) hpad hmod
    (by simp only [firstCutoff,one_mul] <;> exact le_rfl) n hret
  have hlog : Real.logb Z (nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss N ε) n) ≤ 9 := by
    linarith [hevent.uniform.2.2.1]
  have hp := Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le hlog
  have hchild : 0 < nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss N ε) n := by
    unfold nominalChildScale
    exact Real.rpow_pos_of_pos hz _
  rwa [Real.rpow_logb hz d.one_lt_Z.ne' hchild] at hp

end
end Candidate.SilPrior.FourthPower.RepairedChildCaps
