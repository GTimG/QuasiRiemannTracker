/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.certb_local_20261013.Bundles.B058
import Submissions.certb_local_20261013.Bundles.B071
import Submissions.certb_local_20261013.Bundles.B085
import Submissions.certb_local_20261013.Bundles.B086
import Submissions.certb_local_20261013.Bundles.B087
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound

/- BEGIN ORIGINAL MODULE Analytic.JointSecondWidthSectors ; sha256 f9bcdf0445e67c6c7824c8dd35bfc361fa550acef00c23bcc63c5359cb746fa2 -/
section



/-! The four second-descent widths admit finitely many sectors chosen
before the scale. Lower edges give the actual common-norm lower gates;
the capped common-frequency edge pays only one sector width in the scalar. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstSourceConductorCaps
local notation "O" => HeckeFamily.O

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot]

def secondWidthCoordinates (s : CommonSecondKernelLabel Slot) (Z : ℝ) : Fin 4 → ℝ :=
  ![Real.logb Z (s.second.val.1.absNorm : ℝ),
    Real.logb Z (s.second.val.2.absNorm : ℝ),
    Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ),
    Real.logb Z ((∏ Q ∈ s.partition, Q.val).absNorm : ℝ)]

theorem second_width_coordinates_bounds (s : CommonSecondKernelLabel Slot)
    (Z B : ℝ) (hZ : 1 < Z)
    (hC : (s.second.val.1.absNorm : ℝ) ≤ Z^B)
    (hD : (s.second.val.2.absNorm : ℝ) ≤ Z^B) :
    ∀ j, 0 ≤ s.secondWidthCoordinates Z j ∧ s.secondWidthCoordinates Z j ≤ B := by
  have hc : Supported s.second.val.1 := s.toKernelLabel.hC
  have hd : Supported s.second.val.2 := s.toKernelLabel.hD
  have hg : Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero _ _ hc)
  have htdiv := common_subproduct_dvd_left _ _ hc s.toKernelLabel.hCD s.partition
  have ht : (∏ Q ∈ s.partition, Q.val) ≠ 0 := ne_zero_of_dvd_ne_zero hc.1 htdiv
  have htnorm := divisor_norm_le _ _ hc.1 htdiv
  have width (I : Ideal O) (hI : I ≠ 0) (hcap : (I.absNorm : ℝ) ≤ Z^B) :
      0 ≤ Real.logb Z (I.absNorm : ℝ) ∧ Real.logb Z (I.absNorm : ℝ) ≤ B := by
    have hpos : 0 < I.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    refine ⟨Real.logb_nonneg hZ (by exact_mod_cast hpos),?_⟩
    have hh := Real.logb_le_logb_of_le hZ (by exact_mod_cast hpos) hcap
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  intro j
  fin_cases j
  · exact width _ hc.1 hC
  · exact width _ hd.1 hD
  · exact width _ hg (s.commonFrequency_norm_le.1.trans hC)
  · exact width _ ht (htnorm.trans hC)

/-- These lower edges are common to an entire finite sector. No actual
ideal norm is required to equal its representative. -/
theorem second_sector_gates (s : CommonSecondKernelLabel Slot)
    (Z e : ℝ) (hZ : 1 < Z) (he : 0 ≤ e) (edge : Fin 4 → ℝ)
    (hedge : ∀ j, 0 ≤ edge j)
    (hsector : ∀ j, edge j ≤ s.secondWidthCoordinates Z j ∧
      s.secondWidthCoordinates Z j ≤ edge j+e) :
    let c₂ := edge 0
    let d₂ := edge 1
    let b₂ := (c₂+d₂)/2
    let g₂ := min (edge 2) b₂
    let t₂ := edge 3
    0 ≤ c₂ ∧ 0 ≤ d₂ ∧ 0 ≤ b₂ ∧ 0 ≤ g₂ ∧ g₂ ≤ b₂ ∧ 0 ≤ t₂ ∧
      Z^c₂ ≤ (s.second.val.1.absNorm : ℝ) ∧
      Z^d₂ ≤ (s.second.val.2.absNorm : ℝ) ∧
      s.secondLogCost Z ≤ g₂-t₂-b₂+e := by
  dsimp only
  have h₀ := hsector 0
  have h₁ := hsector 1
  have h₂ := hsector 2
  have h₃ := hsector 3
  norm_num only [secondWidthCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three] at h₀ h₁ h₂ h₃
  have hb : 0 ≤ (edge 0+edge 1)/2 :=
    div_nonneg (add_nonneg (hedge 0) (hedge 1)) (by norm_num)
  have hcpos := CenteredMomentFirstScale.norm_pos _ s.toKernelLabel.hC.1
  have hdpos := CenteredMomentFirstScale.norm_pos _ s.toKernelLabel.hD.1
  have hcost := s.secondLogCost_le_capped_sectors Z (edge 2) (edge 3)
    ((edge 0+edge 1)/2) e 0 0 hZ he le_rfl h₂.2 (by simpa using h₃.1)
    (by linarith [h₀.1,h₁.1])
  refine ⟨hedge 0,hedge 1,hb,le_min (hedge 2) hb,min_le_right _ _,hedge 3,?_,?_,?_⟩
  · calc
      _ ≤ Z^(Real.logb Z (s.second.val.1.absNorm : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le h₀.1
      _ = _ := Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hcpos
  · calc
      _ ≤ Z^(Real.logb Z (s.second.val.2.absNorm : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le h₁.1
      _ = _ := Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hdpos
  · simpa using hcost.2

theorem cumulative_common_norm_lower (s : CommonSecondKernelLabel Slot)
    (Z c c₂ d₂ : ℝ) (hZ : 0 < Z)
    (hc : Z^c ≤ (s.firstCommon.absNorm : ℝ))
    (hc₂ : Z^c₂ ≤ (s.second.val.1.absNorm : ℝ))
    (hd₂ : Z^d₂ ≤ (s.second.val.2.absNorm : ℝ)) :
    Z^(c+c₂) ≤ ((s.firstCommon*s.second.val.1).absNorm : ℝ) ∧
    Z^(c+d₂) ≤ ((s.firstCommon*s.second.val.2).absNorm : ℝ) := by
  simp only [Real.rpow_add hZ,map_mul,Nat.cast_mul]
  exact ⟨mul_le_mul hc hc₂ (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _),
    mul_le_mul hc hd₂ (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _)⟩

end CommonSecondKernelLabel

def secondWidthEdge {N : ℕ} (e : ℝ) (b : Fin 4 → Fin (N+1)) (j : Fin 4) : ℝ :=
  (b j).val*e

theorem uniform_second_width_sector_count (B e : ℝ) (he : 0 < e) :
    ∃ N : ℕ, ∀ {Row Slot : Type*} [Fintype Slot]
      (labels : Finset Row) (s : Row → CommonSecondKernelLabel Slot) (Z : ℝ), 1 < Z →
      (∀ u ∈ labels, (s u).second.val.1.absNorm ≤ (Z^B : ℝ) ∧
        (s u).second.val.2.absNorm ≤ (Z^B : ℝ)) →
      ∃ bin : (u : Row) → u ∈ labels → (Fin 4 → Fin (N+1)),
        ∀ u hu j, 0 ≤ secondWidthEdge e (bin u hu) j ∧
          secondWidthEdge e (bin u hu) j ≤ (s u).secondWidthCoordinates Z j ∧
          (s u).secondWidthCoordinates Z j < secondWidthEdge e (bin u hu) j+e := by
  obtain ⟨N,hN⟩ := exists_nat_ge (B/e)
  refine ⟨N,?_⟩
  intro Row Slot inst labels s Z hZ hcap
  have hb u (hu : u ∈ labels) j :=
    (s u).second_width_coordinates_bounds Z B hZ (hcap u hu).1 (hcap u hu).2 j
  let bin : (u : Row) → u ∈ labels → (Fin 4 → Fin (N+1)) := fun u hu j =>
    ⟨Nat.floor ((s u).secondWidthCoordinates Z j/e),Nat.lt_succ_of_le
      (Nat.floor_le_of_le ((div_le_iff₀ he).mpr
        ((hb u hu j).2.trans ((div_le_iff₀ he).mp hN))))⟩
  refine ⟨bin,?_⟩
  intro u hu j
  have hl := Nat.floor_le (div_nonneg (hb u hu j).1 he.le)
  have hh := Nat.lt_floor_add_one ((s u).secondWidthCoordinates Z j/e)
  change 0 ≤ (Nat.floor ((s u).secondWidthCoordinates Z j/e) : ℝ)*e ∧
    (Nat.floor ((s u).secondWidthCoordinates Z j/e) : ℝ)*e ≤ _ ∧
    _ < (Nat.floor ((s u).secondWidthCoordinates Z j/e) : ℝ)*e+e
  refine ⟨by positivity,(le_div_iff₀ he).mp hl,?_⟩
  have hh' := (div_lt_iff₀ he).mp hh
  nlinarith

#print axioms CommonSecondKernelLabel.second_sector_gates
#print axioms CommonSecondKernelLabel.cumulative_common_norm_lower
#print axioms uniform_second_width_sector_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondWidthSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceNormalization ; sha256 6aaac81d068eb96aea88f4729f8b911a9638b8ad42cbf8ba20b6c098f556a2df -/
section


/-! Exact raw source normalization, retaining all common and projector masks. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonRadialSource
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalAmplitudePair CenteredMomentHeckeColumnWindow
local instance sourceNormalizationDecidableSum {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _
local notation "O" => HeckeFamily.O

/-- The literal row energy before dividing by the original source volume. -/
def rawCommonSourceEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (r : Radial) (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) : ℝ :=
  let columns := finiteColumns (Fintype.piFinset s.pools)
  let coeff := finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  sourceRestrictedEnergy r.keep (residualPool C hC.1 columns)
    (fun I => if IsCoprime C I ∧ L ∣ I then coeff (C*I) else 0)
    (heightCoeff s.η s.t) r.profile r.scale

theorem rawCommonSourceEnergy_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (r : Radial) (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) :
    rawCommonSourceEnergy s r C hC R seed L =
      volume s.toData * sourceEnergy s r C hC R seed L := by
  change rawCommonSourceEnergy s r C hC R seed L =
    volume s.toData * (rawCommonSourceEnergy s r C hC R seed L / volume s.toData)
  exact (mul_div_cancel₀ _ (volume_pos s.toData).ne').symm

theorem sourceEnergy_le_iff_raw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (r : Radial) (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (E : ℝ) :
    sourceEnergy s r C hC R seed L ≤ E ↔
      rawCommonSourceEnergy s r C hC R seed L ≤ volume s.toData * E := by
  change rawCommonSourceEnergy s r C hC R seed L / volume s.toData ≤ E ↔ _
  rw [div_le_iff₀ (volume_pos s.toData),mul_comm E]

#print axioms rawCommonSourceEnergy_eq
#print axioms sourceEnergy_le_iff_raw
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceNormalization -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourcePhysicalEnvelope ; sha256 4ca9e9d07b87ac2b9a271d32d6226d2301c6573a284f2a5b57a0cb82ca8e0b34 -/
section


/-! Physical lower dyads cancel a source-volume factor in the absolute
Fourier bound. No reciprocal-dyad or coefficient-cardinality gate remains. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentSecondDiagonal CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O

theorem physical_sqrt_volume_bound (a V H₁ H₂ N₁ N₂ X : ℝ)
    (ha : 0 < a) (hV : 0 < V) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hX : 0 ≤ X)
    (h₁ : a*V/N₁ ≤ H₁) (h₂ : a*V/N₂ ≤ H₂)
    (hNX₁ : N₁ ≤ X) (hNX₂ : N₂ ≤ X) :
    V/(Real.sqrt H₁*Real.sqrt H₂) ≤ X/a := by
  have h₁' : a*V ≤ H₁*X := ((div_le_iff₀ hN₁).mp h₁).trans
    (mul_le_mul_of_nonneg_left hNX₁ hH₁.le)
  have h₂' : a*V ≤ H₂*X := ((div_le_iff₀ hN₂).mp h₂).trans
    (mul_le_mul_of_nonneg_left hNX₂ hH₂.le)
  have hp := mul_le_mul h₁' h₂' (mul_nonneg ha.le hV.le) (mul_nonneg hH₁.le hX)
  have hsq : (a*V)^2 ≤ (Real.sqrt H₁*Real.sqrt H₂*X)^2 := by
    simp only [mul_pow,Real.sq_sqrt hH₁.le,Real.sq_sqrt hH₂.le]
    nlinarith [hp]
  have hh := (sq_le_sq₀ (mul_nonneg ha.le hV.le) (by positivity)).mp hsq
  apply (div_le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr hH₁) (Real.sqrt_pos.mpr hH₂)) ha).mpr
  nlinarith [hh]

 theorem second_projected_absolute_physical_power
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (Ds : α → Finset (Ideal O))
    (n : α → Fin 4 → ℤ) (Z scale A B C N V B₁ B₂ a : ℝ)
    (hZ : 0 < Z) (hscale : 0 ≤ scale) (hscale' : scale ≤ Z^A)
    (hcard : (S.card : ℝ) ≤ Z^B)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (ha : 0 < a)
    (hplain : ∀ v ∈ S, (s v).input.W₁ 0 = 0 ∧ (s v).input.W₂ 0 = 0 ∧
      (∀ x, ‖(s v).input.W₁ x‖ ≤ B₁) ∧ (∀ x, ‖(s v).input.W₂ x‖ ≤ B₂))
    (hvolume : ∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^V)
    (hprojectors : ∀ v ∈ S, ∀ D ∈ Ds v, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
      (D.absNorm : ℝ) ≤ Z^C)
    (hcommon : ∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^N ∧
      (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^N)
    (hphysical : ∀ v ∈ S,
      0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
      a*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
        (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
      a*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) :
    secondProjectedAbsoluteEnvelope S s Ds n scale ≤
      (128/a*(originalAbsoluteEnvelope S s B₁ B₂)^2)*Z^(A+B+C+N+V) := by
  let E := originalAbsoluteEnvelope S s B₁ B₂
  have hE : 0 ≤ E := originalAbsoluteEnvelope_nonneg S s B₁ B₂
  have henv (v) (hv : v ∈ S) :
      (s v).toKernelLabel.absoluteEnvelope (dyadicScale (n v 2)) (dyadicScale (n v 3)) ≤
        (E^2/a)*Z^(N+V) := by
    let vol := CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData
    have hvol : 0 < vol := CenteredMomentSourceInputTailUniform.volume_pos (s v).input
    have hmass : sourceAbsoluteMass (s v).toKernelLabel.columns (s v).toKernelLabel.beta ≤ E*vol := by
      have hp := hplain v hv
      apply (actual_common_absolute_mass (s v) B₁ B₂ hB₁ hB₂ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2).trans
      exact mul_le_mul_of_nonneg_right (originalAbsoluteEnvelope_bound S s B₁ B₂ v hv) hvol.le
    have hh := hphysical v hv
    have hcn := hcommon v hv
    have hNL : 0 < (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (mul_ne_zero (s v).hfirst.1 (s v).toKernelLabel.hC.1))
    have hNR : 0 < (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (mul_ne_zero (s v).hfirst.1 (s v).toKernelLabel.hD.1))
    have hsqrt := physical_sqrt_volume_bound a vol _ _ _ _ (Z^N) ha hvol hh.1 hh.2.1
      hNL hNR (by positivity) hh.2.2.1 hh.2.2.2 hcn.1 hcn.2
    unfold SecondKernelLabel.absoluteEnvelope
    calc
      _ ≤ (Real.sqrt (dyadicScale (n v 2)))⁻¹*(Real.sqrt (dyadicScale (n v 3)))⁻¹*(E*vol)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sourceAbsoluteMass_nonneg _ _) hmass 2) (by positivity)
      _ = E^2*vol*(vol/(Real.sqrt (dyadicScale (n v 2))*Real.sqrt (dyadicScale (n v 3)))) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ E^2*vol*(Z^N/a) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ E^2*Z^V*(Z^N/a) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hvolume v hv) (sq_nonneg _)) (by positivity)
      _ = (E^2/a)*Z^(N+V) := by rw [Real.rpow_add hZ]; ring
  have hinner (v) (hv : v ∈ S) :
      (∑ D ∈ Ds v, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
        (s v).toKernelLabel.absoluteEnvelope (dyadicScale (n v 2)) (dyadicScale (n v 3))) ≤
      (128/a*E^2)*Z^(C+N+V) := by
    rw [← Finset.sum_mul]
    have hm := moebius_mass_le_norm_cap (Ds v) (Z^C) (by positivity) (hprojectors v hv)
    apply (mul_le_mul hm (henv v hv) ((s v).toKernelLabel.absoluteEnvelope_nonneg _ _) (by positivity)).trans_eq
    simp only [Real.rpow_add hZ]
    ring
  unfold secondProjectedAbsoluteEnvelope
  calc
    _ ≤ scale*((S.card : ℝ)*((128/a*E^2)*Z^(C+N+V))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hinner
    _ ≤ Z^A*(Z^B*((128/a*E^2)*Z^(C+N+V))) :=
      mul_le_mul hscale' (mul_le_mul_of_nonneg_right hcard (by positivity)) (by positivity) (by positivity)
    _ = _ := by
      change _ = (128/a*E^2)*Z^(A+B+C+N+V)
      simp only [Real.rpow_add hZ]
      ring

#print axioms physical_sqrt_volume_bound
#print axioms second_projected_absolute_physical_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourcePhysicalEnvelope -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowPhysicalInverseBound ; sha256 46d2474f35b66138abbf0dbb6ec9945b68d653fa19212b1dbc10e5bc67aa2b09 -/
section




/-! Adapted from OpenAI/math family003, pinned original module Detector.LowPhysicalInverseBound.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_physical_inverse_normalized (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b aCut bCut ε : ℝ) (ha : 0< a) (haCut : 0< aCut) (hbCut : 0< bCut)
    (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0< X→Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)
      ∀(hX0 : 0< Z^(Submission20261012.Global.lx:ℝ)/L)(hY0 : 0< Z^(Submission20261012.Global.ly:ℝ)/L),
      (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W (fun i=> Z^(ell i)) t)
            η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t)≤
        C*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0< q := calibration_elementNorm_pos _
  have hc : 0< c := by dsimp [c];positivity
  have hB : 0< B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0< Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := low_selected_nominal_energy η S hS hbad ell hell hsum Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing:ℝ)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0< C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏i : J,(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L)
  intro hX0 hY0
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  have hL : 0< L := lowUnselectedProduct_norm_pos _
    (fun i n hn=> canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n∈canonicalSlotSupport (T i)) :
      a*Z^(ell i)≤ elementNorm n ∧ elementNorm n≤ b*Z^(ell i) := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c*Z^(lowUnselectedLength ell J)≤ L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L≤ B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0< Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W (fun i=> Z^(ell i)) t)
    η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t
  have hrows : ∀z∈R,z≠0 ∧ elementNorm z≤ Ck*Z^((1-Submission20261012.Global.ell)-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR,?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (lowPhysicalScale_nominal_bound (calibrationForSet S hS) Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0≤2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (σ : RayRing) : (∑z∈R,‖row σ z‖^2)≤
      C*(1+‖t‖)^degree*Z^((1-Submission20261012.Global.ell)-lowUnselectedLength ell J+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=> Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source _ Z L hz]
    exact low_inverse_sqrt_normalized q C B Z L (lowUnselectedLength ell J) (lowUnselectedLength ell J+507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=> sq_nonneg _)) (by convert he σ using 1 <;> congr 2 <;> ring) hLhi
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=> hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) := by ring
        _≤_ := by gcongr ; linarith

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowPhysicalInverseBound -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SourceClass ; sha256 1f414419a7f8c71335d32a19961fe699bee653e56d5b3b5c5375983312bf5946 -/
section


/-! The actual full amplitude class supplies the selected-prime and upper-product
premises of the original-numerator packet estimate. The class count remains an
explicit premise and is not recomputed on an error-dependent or selected subset. -/
noncomputable section
set_option maxHeartbeats 2600000
open scoped Classical BigOperators ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma source_box_capacity_eq (kap d t:ℝ) (j:ℕ) :
    SlotSelection.reflectedCapacity kap d ((j:ℝ)*t+2*t)=
      selectedCapacity kap ((2*(ly/d)-1)/(6*kap)-t/(3*kap)) ((j:ℝ)*t+t) := by
  unfold SlotSelection.reflectedCapacity SlotSelection.baseCapacity selectedCapacity
  congr 1
  ring

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem source_packet_amplitude_class {Δ:ℝ} (D:HighParameters.HighData Δ)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hfine:∀j,D.ell j≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀(Z d:ℝ),1< Z → (1/2:ℝ)≤ d → d≤ Submission20261012.Global.h+rowExtension → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤ a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=> D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀R Ccount:ℝ,1≤ Ccount → (rows'.card:ℝ)≤ Ccount*U^R →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=> sourcePrimePool F Z s.val) (fun s=> source_prime_pool_outside F Z s.val)
        (fun _=> F.W) (fun s=> Z^(D.ell s.val)) x z F.W (U^(ly/d))*(∏s∈main,Q i.val s)‖) ≤
        C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
            (3*R+1+2*D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := source_packet_selected_bin D F hbeta hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=> D.ell s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0≤2*a-1 := by linarith
  have hδtop : 2*a-1≤3/4 := by linarith
  have hU0 : 0< U := zero_lt_one.trans hbin.1
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := source_class_main_selection D F hfine Z d ((j:ℝ)*D.t+2*D.t) (2*a-1)
    hZ hd (by positivity) hδ z rows main bin hne
  have hq0 : 0≤ q := (hselection 0).1
  have hqtop : q≤(2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected⊆main ∧
      (∑s∈selected,D.ell s/d)≤ SlotSelection.reflectedCapacity D.momentKappa d ((j:ℝ)*D.t+2*D.t) ∧
      ∀u∈rows',
        (Z^d)^(2*q*SlotSelection.reflectedCapacity D.momentKappa d ((j:ℝ)*D.t+2*D.t)-
          (2*a-1)*Cycle25.sourceMesh D.t)≤‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖≤(Z^(D.ell s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
          ‖∏s∈main,Q u s‖≤(Z^d)^(q*(ell/d)+D.t*(ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖≤ U^(q*(ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(ell/d)) (D.t*(ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) :
      (∑s∈selected j,D.ell s/d) ≤ selectedCapacity D.momentKappa ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) ((j:ℝ)*D.t+D.t) := by
    rw [←source_box_capacity_eq]
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      U^(q*selectedCapacity D.momentKappa ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) ((j:ℝ)*D.t+D.t)-
        ((2*a-1)*Cycle25.sourceMesh D.t/2)) ≤ ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ,←source_box_capacity_eq]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖≤ U := by
    rw [hUZ]
    exact source_selected_product_crude D Z d (2*a-1) hZ hd hδ hδtop (selected j) (Q i.val)
      (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=> hrows u (hsub hu)) (fun u hu=> hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=> labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=> sourcePrimePool F Z s.val) (fun s=> source_prime_pool_outside F Z s.val)
      (fun _=> F.W) (fun s=> Z^(D.ell s.val)) x z F.W (U^(ly/d))) Pmain U (D.t*(ell/d))
    (D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
      (3*R+1+2*D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*D.t/4)
    (C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.SourceClass -/

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedErrorAverageFull ; sha256 5acd64dded8a14f4713cbf0b237d34f2cb021094a80d777276b99c05f842c72c -/
section


/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance actualExtractedErrorAverageDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance actualExtractedErrorAverageFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates


open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstLiveAdmission

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentPrimeElements CenteredMomentPrimePool

theorem actual_firstExtractedErrors_local_average_full
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost) (hsigma_eq : sigma=9/500)
    (Avol Dscale Pmask qmoving εgeo : ℝ) (hεgeo : 0 < εgeo)
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀θ:α→RayQuotient.Characters M H,
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    P.Nonempty →
    (∀ (prime : elementPool P) i, ∀ I∈(activeInput (child src C R0 B τ t)).slots i,
      IsCoprime (Ideal.span {prime.val}) I) →
    ∀ family : elementPool P → Fin 3 → RayCharacter → Character,
    (∀ prime i χ, (family prime i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ prime i χ, ((family prime i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun (prime : elementPool P) (i : Fin 3) => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ prime i, (radius prime i)⁻¹≤ Z^Dscale) →
    (∀ prime i χ, ((family prime i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀profile:Profiles a b,profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀ Mgeom Mvolume : ℝ, 1≤ Mgeom →
    Z^(Mgeom/4)≤ src.X₁ → Z^(Mgeom/4)≤ src.X₂ →
    Z^(Mgeom/4)≤ src.Y₁ → Z^(Mgeom/4)≤ src.Y₂ →
    Mgeom≤ Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src)≤(883/1000)*Mgeom →
    Real.logb Z (volume src)≤ Mvolume →
    Real.logb Z fixedPresentationCost≤1/1000 →
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤429/100000 →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    (56/(P.card : ℝ))*(∑ prime : elementPool P,
      firstExtractedErrors (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (family prime)) ≤
      mass (child src C R0 B τ t)^2*
        (reference (τ.modulus.absNorm : ℝ) (volume src) (C.absNorm : ℝ) Z
          (allowance C D Z)/(volume src/(C.absNorm : ℝ)))*
        (56*1872*(Fintype.card RayCharacter : ℝ))*
          ∑ j : Fin 4,
            (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
            (upper^N)^(powers εsrc j)*
            Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j) := by
  subst sigma
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_firstExtractedErrors_local_bound_full (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad (9/500) cost hsigma hξsmall hcost rfl
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ,
    eventually_pool_prime_quarter_lower M H Sbad hbad (9/500) (by norm_num)] with Z hZ hpZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only at *
  intro hP hslot family hrad hfamily
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
  have hprime : ∀ Q∈P, Prime Q := fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).1
  have hbadP : ∀ Q∈P, Q∉fixedBadPrimes := fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).2
  have hbound (prime : elementPool P) := by
    have hd := elementPool_data P hprime hbadP prime.val prime.property
    have hp : Prime (Ideal.span {prime.val}) := hprime _ hd.2.1
    exact hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      prime hp (by linarith [(hpZ.2 prime prime.property).1]) prime.property
      (by linarith [(hpZ.2 prime prime.property).1]) (hslot prime) (family prime) (hrad prime) (hfamily prime)
      hzero1 hzero2 hvolumeCap hmaskCap hR0 (hradInv prime) (hconductorCap prime) seed hseed hseed0 hseedcap
      profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
      hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  have hh := normalized_prime_average_le P hP hprime hbadP _ _ hbound
  convert hh using 1 <;> ring

#print axioms actual_firstExtractedErrors_local_average_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedErrorAverageFull -/
