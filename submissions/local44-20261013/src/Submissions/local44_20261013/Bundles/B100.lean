/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.local44_20261013.Bundles.B016
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B065
import Submissions.local44_20261013.Bundles.B067
import Submissions.local44_20261013.Bundles.B069
import Submissions.local44_20261013.Bundles.B075
import Submissions.local44_20261013.Bundles.B081
import Submissions.local44_20261013.Bundles.B082
import Submissions.local44_20261013.Bundles.B083
import Submissions.local44_20261013.Bundles.B084
import Submissions.local44_20261013.Bundles.B085
import Submissions.local44_20261013.Bundles.B086
import Submissions.local44_20261013.Bundles.B087
import Submissions.local44_20261013.Bundles.B089
import Submissions.local44_20261013.Bundles.B091
import Submissions.local44_20261013.Bundles.B092
import Submissions.local44_20261013.Bundles.B094
import Submissions.local44_20261013.Bundles.B095
import Submissions.local44_20261013.Bundles.B096
import Submissions.local44_20261013.Bundles.B098
import Submissions.local44_20261013.Bundles.B099
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalPower ; sha256 ad158e8770afe53654f9c97bf36930f91adb98f3a7060a95357b19b05e2b3295 -/
section




/-! The coherent exceptional saving uses the original plain scale and the
full cumulative common extraction. Its scalar bound is uniform in every
actual second common label. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondExceptionalPhysicalSaving
open CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCommonExceptionalSymmetry CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentExceptionalAmplitudePair
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentSecondBlockAggregate CenteredMomentOriginalCommonHarmonic
open CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

lemma coherent_exceptional_column_power (Z N c d θ B ε δ r : ℝ)
    (hZ : 1 < Z) (hN : 0 < N) (hc : 1 ≤ c) (hd : 1 ≤ d) (hθ : 0 ≤ θ)
    (hC : N*c ≤ Z^B) (hD : N*d ≤ Z^B) :
    Z^(2*ε+δ-max (max (r-Real.logb Z (N*c)) 0) (max (r-Real.logb Z (N*d)) 0))*
      ((N*c)*(N*d))^θ*Z^(-(Real.logb Z c+Real.logb Z d)/3) ≤
    Z^(2*ε+δ+2*B*θ-2*max (r-Real.logb Z N) 0/3) := by
  have hz := zero_lt_one.trans hZ
  have hc0 := zero_lt_one.trans_le hc
  have hd0 := zero_lt_one.trans_le hd
  have hpow : ((N*c)*(N*d))^θ ≤ Z^(2*B*θ) := by
    calc
      _ ≤ (Z^B*Z^B)^θ := Real.rpow_le_rpow (by positivity)
        (mul_le_mul hC hD (by positivity) (by positivity)) hθ
      _ = Z^(2*B*θ) := by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1
        ring
  have hledger := column_cap_ledger (Real.logb Z c) (Real.logb Z d) (r-Real.logb Z N)
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  rw [Real.logb_mul hN.ne' hc0.ne',Real.logb_mul hN.ne' hd0.ne',
    show r-(Real.logb Z N+Real.logb Z c)=(r-Real.logb Z N)-Real.logb Z c by ring,
    show r-(Real.logb Z N+Real.logb Z d)=(r-Real.logb Z N)-Real.logb Z d by ring,
    same_raw_better_cap]
  calc
    _ ≤ Z^(2*ε+δ-max ((r-Real.logb Z N)-min (Real.logb Z c) (Real.logb Z d)) 0)*
        Z^(2*B*θ)*Z^(-(Real.logb Z c+Real.logb Z d)/3) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hz.le _)
    _ = Z^((2*ε+δ-max ((r-Real.logb Z N)-min (Real.logb Z c) (Real.logb Z d)) 0)+
        2*B*θ-(Real.logb Z c+Real.logb Z d)/3) := by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem actual_coherent_exceptional_scalar_uniform
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (wlo whi : ℝ) (hwlo : 0 < wlo) (profile : Profiles wlo whi)
    (hW₁ : src.W₁ = profile.profile 0) (hW₂ : src.W₂ = profile.profile 1)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (t : ℝ) (U : Finset (CommonIndex p.val.1 p.val.2))
    (Radius : ℝ) (rows : Finset O) (hrows : ∀ z ∈ rows,z ≠ 0) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0 < K) (n : Fin 4 → ℤ) (Z P ε δ θ B r : ℝ)
    (hZ : 1 < Z) (hP : 0 < P) (hθ : 0 ≤ θ) (hsource : sourceRadius src ≤ Z^B)
    (hne : physicalBlock η t
      (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁))
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W K n ≠ 0) :
    Z^(2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
      (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
      (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
      coherentExceptionalScalar (volume src.toData) P (C₁.absNorm : ℝ) p.val.1 p.val.2 U K n ≤
    ((C₁.absNorm : ℝ)*P)⁻¹*
      ((volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*K^(5/6:ℝ)*
        (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
      Z^(2*ε+δ+2*B*θ-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3)/
      ((commonRadical p.val.1 p.val.2).absNorm : ℝ) := by
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have ha := originalLowerProfile_pos src wlo wlo hwlo hwlo
  have hz := zero_lt_one.trans hZ
  have hN : 0 < (C₁.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC₁.1)
  have hz₁ : src.W₁ 0 = 0 := by
    by_contra hh
    have hh' := (profile.support 0 (by simpa only [←hW₁,Function.mem_support] using hh)).1
    exact (not_le_of_gt hwlo) hh'
  have hz₂ : src.W₂ 0 = 0 := by
    by_contra hh
    have hh' := (profile.support 1 (by simpa only [←hW₂,Function.mem_support] using hh)).1
    exact (not_le_of_gt hwlo) hh'
  have hn := actual_common_cumulative_norm src R seed C₁ L₁ hC₁ hz₁ hz₂ p
  have hc : 1 ≤ (p.val.1.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (lowActiveLeftSupported p).1)
  have hd : 1 ≤ (p.val.2.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (lowActiveRightSupported p).1)
  have hs := coherent_exceptional_scalar_physical (volume src.toData) P (C₁.absNorm : ℝ) hV hP hN
    η t _ _ p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p)
    (commonLabels_data _ _ _ _ p.property).2.2 U Radius rows hrows W K hK n
    (originalLowerProfile src wlo wlo) Z (originalLowerProfile_pos src wlo wlo hwlo hwlo) hZ
    (common_second_column_lower_profiles src R seed C₁ L₁ hC₁.1 wlo whi hwlo profile hW₁.symm hW₂.symm) hne
  have hc' : (C₁.absNorm : ℝ)*(p.val.1.absNorm : ℝ) ≤ Z^B := by
    simpa only [map_mul,Nat.cast_mul] using hn.1.trans hsource
  have hd' : (C₁.absNorm : ℝ)*(p.val.2.absNorm : ℝ) ≤ Z^B := by
    simpa only [map_mul,Nat.cast_mul] using hn.2.trans hsource
  have hp := coherent_exceptional_column_power Z (C₁.absNorm : ℝ) p.val.1.absNorm p.val.2.absNorm
    θ B ε δ r hZ hN hc hd hθ hc' hd'
  apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans
  let F : ℝ := ((C₁.absNorm : ℝ)*P)⁻¹*
    ((volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*K^(5/6:ℝ)*
      (originalLowerProfile src wlo wlo)^(-2/3:ℝ))/((commonRadical p.val.1 p.val.2).absNorm : ℝ)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  calc
    _ = F*(Z^(2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
      (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
      (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
      Z^(-(Real.logb Z (p.val.1.absNorm : ℝ)+Real.logb Z (p.val.2.absNorm : ℝ))/3)) := by dsimp only [F]; ring
    _ ≤ F*Z^(2*ε+δ+2*B*θ-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3) :=
      mul_le_mul_of_nonneg_left (by simpa only [map_mul,Nat.cast_mul] using hp) hF
    _ = _ := by dsimp only [F]; ring

#print axioms coherent_exceptional_column_power
#print axioms actual_coherent_exceptional_scalar_uniform
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalPower -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnnularActualSector ; sha256 f5ce783defaa25ee5ce70a24145f20277992270eebc5547c97ee83c4cee12e73 -/
section




/-! The actual first sector needs only bounded Fourier joint targets.
The literal source coarse sums and lower target exponents are supplied
by the source geometry, before the first Fourier kernel is integrated. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance firstAnnularActualSectorDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentFirstAnnularMajorant CenteredMomentSecondRetainedRows CenteredMomentLogDyadic
theorem eventually_actual_first_annular_sector_from_local_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (hVrow : V 1 = logAnnulus)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay Ncap : ℕ) (ν F U b₁ b₂ B₁ B₂ B L Cr Amin Amax : ℝ)
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R seed : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i, s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (M A δ a window Ch : ℝ), Amin ≤ A → A ≤ Amax → 0 < a → 0 ≤ Ch →
    volume s.toData = Z^A →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    let Outer := FirstSourceOuterIndex s R seed (Z^M) radius
    let q := firstSourceOuterLabel s R seed (Z^M) radius
    ∀ (labels : Finset Outer) (ref : Outer) (t : Outer → ℝ),
    (∀ i ∈ labels, a*Z^A ≤ ((q i).C.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 2)) →
    (∀ i ∈ labels, a*Z^A ≤ ((q i).D.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 3)) →
    (∀ i ∈ labels, ((q i).C.absNorm : ℝ) ≤ Z^δ*((q ref).C.absNorm : ℝ)) →
    (∀ i ∈ labels, ((q i).D.absNorm : ℝ) ≤ Z^δ*((q ref).D.absNorm : ℝ)) →
    (∀ i ∈ labels, (q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
      (q i).activeWidth Z/2+(q i).punctureWidth Z) →
    (∀ i ∈ labels, ‖V 0 ((q i).sourceRowLog (Z^M) (dyadicScale (i.2.2 0)))‖ ≤ 1) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A))) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A))) →
    ‖∑ i ∈ labels,
      (((1+dyadicScale (i.2.2 0)*dyadicScale (i.2.2 1)/
        (dyadicScale (i.2.2 2)*dyadicScale (i.2.2 3)))^decay : ℝ) : ℂ)*
      (q i).sourceBlock (t i) (retainedRows (radius i.1 i.2.1.val) 1) Wkernel V (Z^M) (dyadicScale (i.2.2 0))
        (dyadicScale (i.2.2 1)) (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3))‖/Z^A ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ (QuadraticInitialBound.diagonalControl profile))*(Real.exp window/a)*Z^(M+δ) := by
  let D := QuadraticInitialBound.diagonalControl profile
  obtain ⟨degree,C,hC,hsector⟩ := eventually_actual_first_variable_sector_from_local_targets
    (ι := ι) Wkernel V Mwin hMwin hV hV₂c hV₂s hV₃c hV₃s decay Ncap ν
    F U b₁ b₂ B₁ B₂ D B L Cr Amin Amax (L+1) hν hB₁ hB₂
    (QuadraticInitialBound.diagonalControl_nonneg _) hB hL hCr (by linarith)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hsector,eventually_ge_atTop (max 2 (4*Cr))] with Z hsector hZcap
  have hZ₂ : 2 ≤ Z := (le_max_left _ _).trans hZcap
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) hZ₂
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hCrZ : 4*Cr ≤ Z := (le_max_right _ _).trans hZcap
  intro s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    M A δ a window Ch hAmin hAmax ha hCh hvolume radius hr
  dsimp only
  intro labels ref t hl hr' hNC hND hscalarWidth hV₀ hleft hright
  let q := firstSourceOuterLabel s R seed (Z^M) radius
  let rows := fun i : FirstSourceOuterIndex s R seed (Z^M) radius =>
    retainedRows (radius i.1 i.2.1.val) 1
  let H := fun i : FirstSourceOuterIndex s R seed (Z^M) radius => dyadicScale (i.2.2 1)
  have hrows (i) : ∀ z ∈ rows i,z ≠ 0 := by
    intro z hz hzero
    subst z
    have hh := (ConcretePrimeRowBridge.mem_rowNormDisk.mp hz).1
    simpa using hh
  have hHcap (i) : H i ≤ Z^(L+1) := by
    have hh := (first_dyadic_annular_radius _ _ _ _ i.2.2).2
    calc
      H i ≤ 4*radius i.1 i.2.1.val := hh
      _ ≤ 4*(Cr*Z^L) := mul_le_mul_of_nonneg_left (hr i.1 i.2.1.val) (by norm_num)
      _ ≤ Z*Z^L := by nlinarith [Real.rpow_pos_of_pos hz L]
      _ = Z^(L+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
  have hh := hsector s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    M A δ a window Ch hAmin hAmax ha hCh hvolume radius hr labels ref
    (fun i => firstAnnularRows (rows i) (H i)) t (fun _ => profile) H
    (fun i => firstAnnularRows_nonzero _ _ (hrows i)) (fun _ => dyadicScale_pos _) hHcap
    (fun _ => le_rfl) hl hr' hNC hND hscalarWidth hV₀
    (fun i _ z _ => by rw [hVrow]; exact logAnnulus_norm _)
    (fun i _ z => profile_nonneg _)
    (fun i _ => firstAnnularRows_majorant _ _ (dyadicScale_pos _)) hleft hright
  have heq (i) : (q i).sourceBlock (t i) (rows i) Wkernel V (Z^M)
      (dyadicScale (i.2.2 0)) (dyadicScale (i.2.2 1))
      (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3)) =
    (q i).sourceBlock (t i) (firstAnnularRows (rows i) (H i)) Wkernel V (Z^M)
      (dyadicScale (i.2.2 0)) (dyadicScale (i.2.2 1))
      (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3)) :=
    (q i).sourceBlock_annular_rows _ _ (hrows i) _ _ hVrow _ _ _ _ _ (dyadicScale_pos _)
  change ‖∑ i ∈ labels, _*(q i).sourceBlock (t i) (rows i) Wkernel V (Z^M)
    (dyadicScale (i.2.2 0)) (dyadicScale (i.2.2 1))
    (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3))‖/Z^A ≤ _
  simp_rw [heq]
  exact hh

#print axioms eventually_actual_first_annular_sector_from_local_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnnularActualSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstProjectorMass ; sha256 7fd355035184de40412aee48cf176b77ed51c357c5c6262bb9f4b4aace3a2fbe -/
section


/-! The true first projector harmonic mass, on the supported squarefree
domain produced before the source Cauchy step. Both ray labels are paid
by a fixed constant. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstDivisorSupport
local notation "O" => HeckeFamily.O

theorem actual_first_projector_harmonic_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ {ι : Type*} [Fintype ι] (q : FirstJointLabel ι) (H : ℝ), H ≤ Z^B →
      (∑ i : q.SourceIndex, if ((i.1.val).absNorm : ℝ) ≤ H/(q.C.absNorm : ℝ)
        then 1/((i.1.val).absNorm : ℝ) else 0) ≤ C*Z^ε ∧
      (∑ i : q.SourceIndex, if ((i.1.val).absNorm : ℝ) ≤ H/(q.D.absNorm : ℝ)
        then 1/((i.1.val).absNorm : ℝ) else 0) ≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := supported_harmonic_mass B ε hB hε
  have hRay : 0 < (Fintype.card RayCharacter : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty RayCharacter from ⟨1⟩)
  refine ⟨(Fintype.card RayCharacter : ℝ)^2*C,mul_pos (sq_pos_of_pos hRay) hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ q H hH
  have hsum (I : Ideal O) (hI : Supported I) :
      (∑ i : q.SourceIndex, if ((i.1.val).absNorm : ℝ) ≤ H/(I.absNorm : ℝ)
        then 1/((i.1.val).absNorm : ℝ) else 0) ≤
        ((Fintype.card RayCharacter : ℝ)^2*C)*Z^ε := by
    have hn : (1:ℝ) ≤ I.absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    have hcap : H/(I.absNorm : ℝ) ≤ Z^B :=
      (div_le_div_of_nonneg_right hH (zero_le_one.trans hn)).trans
        (div_le_self (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _) hn)
    have hh := hZ.2 q.projectors I H hcap
    have he : (∑ L ∈ q.projectors.filter (fun L => (L.absNorm : ℝ) ≤ H/(I.absNorm : ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖/(L.absNorm : ℝ)) =
        ∑ L ∈ q.projectors, if (L.absNorm : ℝ) ≤ H/(I.absNorm : ℝ) then 1/(L.absNorm : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro L hL
      rw [q.projector_moebius_norm L hL]
    rw [he] at hh
    rw [q.sourceIndex_projector_sum (fun L => if (L.absNorm : ℝ) ≤ H/(I.absNorm : ℝ)
      then 1/(L.absNorm : ℝ) else 0)]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by ring)
  exact ⟨hsum q.C q.hC,hsum q.D q.hD⟩

theorem actual_first_supported_label_harmonic_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ {ι Λ : Type*} [Fintype ι] [DecidableEq Λ]
      (labels : Finset Λ) (q : Λ → FirstJointLabel ι) (H : Λ → ℝ),
    (∀ l ∈ labels, H l ≤ Z^B) →
      (∑ k ∈ firstLeftSourceLabels labels q H, 1/((k.2.1.val).absNorm : ℝ)) ≤
        C*Z^ε*(labels.card : ℝ) ∧
      (∑ k ∈ firstRightSourceLabels labels q H, 1/((k.2.1.val).absNorm : ℝ)) ≤
        C*Z^ε*(labels.card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := actual_first_projector_harmonic_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι Λ _ _ labels q H hH
  constructor
  · simp only [firstLeftSourceLabels,Finset.sum_filter,firstSourceLabels,Finset.sum_sigma]
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using
      Finset.sum_le_sum (fun l hl => (hZ.2 (q l) (H l) (hH l hl)).1)
  · simp only [firstRightSourceLabels,Finset.sum_filter,firstSourceLabels,Finset.sum_sigma]
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using
      Finset.sum_le_sum (fun l hl => (hZ.2 (q l) (H l) (hH l hl)).2)

#print axioms actual_first_projector_harmonic_mass
#print axioms actual_first_supported_label_harmonic_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstProjectorMass -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourceRays ; sha256 221d035e831976f28de5a75bda9ca10c4e9ba9bbda3861a88f49e67c8dfd090f -/
section




/-! The actual high physical estimate on the literal nested source indices.
Canonical rows, units and source transports are constructed by the embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_high_source_rays
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
    (Wkernel : 𝓢(ℝ,ℂ))
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (input : Input Slot) (puncture seed : Ideal O)
        (hpuncture : puncture ≠ 0) (hseed : Squarefree seed)
        (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
        (side : Bool) (ξ₁ ξ₂ : RayCharacter)
        (fallback : NonzeroJointSourceRow (original input puncture seed) side)
        (qs : Finset (NonzeroJointSourceRow (original input puncture seed) side)),
      let S := qs.image NonzeroJointSourceRow.label
      let unit := sourceUnit fallback η ξ₁ ξ₂
      let w := sourceRow fallback η ξ₁ ξ₂
      let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
      let first := sourceFirst fallback η ξ₁ ξ₂
      let z := sourceFrequency fallback
  let Ds := fun v => (s v).physicalProjectors
  let rayWeight := fun v => (s v).physicalRayWeight
      let Ds := fun v => (s v).physicalProjectors
      let rayWeight := fun v => (s v).physicalRayWeight
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ q ∈ qs, Squarefree q.val.L) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (t K Radius tbase firstU firstTheta : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, t v = tbase v+2*Real.pi*(firstU v-firstTheta v)) →
      (∀ v ∈ S, |tbase v| ≤ Z^ν ∧ |firstU v| ≤ Z^ν ∧ |firstTheta v| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      ∀ scalarLoss : ℝ,
      (∀ v ∈ S, 0 < K v ∧
        K v ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      (∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ∑ q ∈ qs, let v := q.label; ∑ D ∈ Ds v,
          ‖((s v).withRays χ ξ).physicalRowTerm (Z^(A-c)) (actualHighPrimeCount M H Sbad Z)
            (t v) (z v) Wkernel (K v) (Radius v) (n v) D‖) ≤
        C*Z^(π+A-c+R₁+E+Bc-144011/219600000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_source_physical η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel 0 tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  let Cr := (Fintype.card RayCharacter : ℝ)^2*C
  have hCr : 0 < Cr := mul_pos (pow_pos (by exact_mod_cast Fintype.card_pos) _) hC
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,Cr,hν,hντ,hτdet,hheight,horders,hCr,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback qs
  dsimp only
  let S := qs.image NonzeroJointSourceRow.label
  let unit := sourceUnit fallback η ξ₁ ξ₂
  let w := sourceRow fallback η ξ₁ ξ₂
  let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
  let first := sourceFirst fallback η ξ₁ ξ₂
  let z := sourceFrequency fallback
  let Ds := fun v => (s v).physicalProjectors
  let rayWeight := fun v => (s v).physicalRayWeight
  intro R hR hprojSource hbin hnorm hNw hNr t K Radius tbase firstU firstTheta n
    σ freq θ slotWidth hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
  have hbound (χ ξ : RayCharacter) :
      (∑ q ∈ qs, let v := q.label; ∑ D ∈ Ds v,
        ‖((s v).withRays χ ξ).physicalRowTerm (Z^(A-c)) (actualHighPrimeCount M H Sbad Z)
          (t v) (z v) Wkernel (K v) (Radius v) (n v) D‖) ≤
      C*Z^(π+A-c+R₁+E+Bc-144011/219600000) := by
    have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
      input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ χ ξ fallback qs
      R hR hprojSource hbin hnorm hNw hNr t K Radius tbase firstU firstTheta n
      σ freq θ slotWidth hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
      Bmask hconductorBalance hmaskNorm hplain hmatch
      hscale hprimeScale hteq hinputfreq hσrange hslotfreq
      A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
      supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
      hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
      hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
    have hpool (v : JointReconstructionLabel) :
        (sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ χ ξ v).physicalProjectors =
          Ds v := rfl
    simp only [pow_zero,Complex.ofReal_one,one_mul,hpool] at hh
    have he (v : JointReconstructionLabel) :
        sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ χ ξ v =
          (s v).withRays χ ξ := rfl
    simp only [he] at hh
    exact hh
  calc
    _ ≤ ∑ _χ : RayCharacter, ∑ _ξ : RayCharacter,
        C*Z^(π+A-c+R₁+E+Bc-144011/219600000) :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun ξ _ => hbound χ ξ))
    _ = Cr*Z^(π+A-c+R₁+E+Bc-144011/219600000) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Cr]
      ring

end FixedData
#print axioms actual_joint_high_source_rays
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourceRays -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowMixedHarmonic ; sha256 294b9a6bbdc21c7402f066ee86551cc12e46ecb7e124570dc723cb9d92a1f2d9 -/
section



/-! The genuine second common-block harmonic sum also pays the absolute
Fourier tail. A tail saving at least the projector norm exponent restores
the same reciprocal-projector weight; no projector cardinality is spent. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice CenteredMomentOriginalCommonHarmonic
open CenteredMomentFixedRay RayFourExpansion CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O

lemma moebius_mixed_harmonic_pointwise (D : Ideal O) (Z E F B saving : ℝ)
    (hZ : 1 < Z) (hF : 0 ≤ F) (hsaving : B ≤ saving)
    (hD : (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 → (D.absNorm : ℝ) ≤ Z^B) :
    ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖*(E/(D.absNorm : ℝ)+F*Z^(-saving)) ≤
      (E+F)*(‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ)) := by
  by_cases hm : (UniqueFactorizationMonoid.moebius D : ℂ) = 0
  · simp [hm]
  have hn : 0 < (D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (squarefree_of_moebius_ne_zero D hm).ne_zero)
  have hcap : (D.absNorm : ℝ) ≤ Z^saving :=
    (hD hm).trans (Real.rpow_le_rpow_of_exponent_le hZ.le hsaving)
  have ht : Z^(-saving) ≤ 1/(D.absNorm : ℝ) := by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le,←one_div]
    exact one_div_le_one_div_of_le hn hcap
  calc
    _ ≤ ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖*(E/(D.absNorm : ℝ)+F*(1/(D.absNorm : ℝ))) := by
      gcongr
    _ = _ := by ring

lemma actual_second_ray_mixed_factor (C D L : Ideal O) (Z E F B saving : ℝ)
    (hZ : 1 < Z) (hE : 0 ≤ E) (hF : 0 ≤ F) (hsaving : B ≤ saving)
    (hL : (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^B) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter,
      ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*
        ‖pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ‖*
        pairWeight C D*(E/(L.absNorm : ℝ)+F*Z^(-saving))) ≤
      (256*(E+F))*((‖(UniqueFactorizationMonoid.moebius L : ℂ)‖/(L.absNorm : ℝ))*pairWeight C D) := by
  have hp := pairWeight_nonneg C D
  have hn := moebius_mixed_harmonic_pointwise L Z E F B saving hZ hF hsaving hL
  calc
    _ = (‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(E/(L.absNorm : ℝ)+F*Z^(-saving)))*
        pairWeight C D*(∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ‖) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      ring
    _ ≤ ((E+F)*(‖(UniqueFactorizationMonoid.moebius L : ℂ)‖/(L.absNorm : ℝ)))*pairWeight C D*256 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hn hp
      · exact phaseTable_mass (primaryGenerator C) (primaryGenerator D)
      · positivity
      · positivity
    _ = _ := by ring

theorem actual_common_second_mixed_harmonic_mass
    (B Bproj L Cr ε : ℝ) (hB : 0 ≤ B) (hBproj : 0 ≤ Bproj) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁),
      src.W₁ 0 = 0 → src.W₂ 0 = 0 → sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ K Radius Hsource : ℝ, 0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B →
      let columns := commonSecondColumns (original src R seed) C₁ hC₁
      let β := commonSecondBeta (original src R seed) C₁ L₁
      ∀ Ds : ActiveBlocks columns β K Radius Hsource → Finset (Ideal O),
      (∀ q, ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
        (D.absNorm : ℝ) ≤ Z^Bproj) →
      ∀ E F saving : ℝ, 0 ≤ E → 0 ≤ F → Bproj ≤ saving →
      (∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖*
            ‖pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ‖*
            pairWeight q.1.1.val.1 q.1.1.val.2*(E/(D.absNorm : ℝ)+F*Z^(-saving))) ≤
        Cbound*(E+F)*Z^ε := by
  obtain ⟨C,hC,hmain⟩ := actual_common_second_projector_harmonic_mass B Bproj L Cr ε hB hBproj hL hCr hε
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro ι instF instD src R seed C₁ L₁ hC₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH columns β Ds hDs E F saving hE hF hsaving
  have hm := hmain.2 src R seed C₁ L₁ hC₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH Ds hDs
  calc
    _ ≤ ∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        (256*(E+F))*((‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*
          pairWeight q.1.1.val.1 q.1.1.val.2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum (fun D hD => actual_second_ray_mixed_factor _ _ D Z E F Bproj saving
        hmain.1 hE hF hsaving (hDs q D hD))
    _ = (256*(E+F))*(∑ q : ActiveBlocks columns β K Radius Hsource, ∑ D ∈ Ds q,
        (‖(UniqueFactorizationMonoid.moebius D : ℂ)‖/(D.absNorm : ℝ))*pairWeight q.1.1.val.1 q.1.1.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (256*(E+F))*(C*Z^ε) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

#print axioms moebius_mixed_harmonic_pointwise
#print axioms actual_common_second_mixed_harmonic_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowMixedHarmonic -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowPhysicalKernel ; sha256 a9d8e04875b113503aa0075aa61949569db2088857055a231ea939781bca867d -/
section





















/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero
open CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentAllocatedNaturalSource
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowPhysicalKernelFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

open CenteredMomentActiveSource CenteredMomentCompleteCommon CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondBlockHarmonicMass
/-- The actual prime cardinality and physical main radius are retained exactly. -/
theorem low_actual_precount_eq (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (Z A c d R E Mparent omega primeCount K : ℝ)
    (n : Fin 4 → ℤ) (hZ : 1 < Z) (hp : 0 < primeCount)
    (hK : K = Z^(2*A-c-d+R+E-Mparent+max (d-c) 0+6*(3/500)+omega)) :
    secondPrecountFactor (Z^(A-c)) primeCount C D U K n =
      (Z^(3/500 : ℝ)/primeCount)*
        Z^(A-min c d+R+E-Mparent+5*(3/500)+
          Real.logb Z (normValue (commonFrequencyGenerator C D))-
          Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)-
          (Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2+omega) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [secondPrecountFactor_change_prime _ primeCount (Z^(3/500 : ℝ))
    (Real.rpow_pos_of_pos hz _).ne' hp.ne' (Real.rpow_pos_of_pos hz _).ne',hK,
    enlarged_second_precount_factor Z A c d R E Mparent (3/500) omega hZ C D hC hD U n]
  congr 2
  dsimp [normValue]
  ring

theorem actual_second_low_physical_kernel_of_common_bin
    (W : ℝ → ℂ) (aslot bslot a b Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss)
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask)
    (loInput hiInput : α → ℝ) (Bcommon δcommon : ℝ) (hBcommon : 0 ≤ Bcommon) (hδcommon : 0 < δcommon)
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss)
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask : ℝ)
        (Sbad : Finset (Ideal O)) (primeLoss : ℝ), 0 < ν → 0 ≤ tailRows → 0 < primeLoss →
      ∃ (Nkernel : ℕ) (Ckernel : ℝ), 0 ≤ Ckernel ∧
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (C₁ D₁ Rmask seed Lproj Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (p₂ : ActiveLabel (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)),
      let C₂ := p₂.val.1
      let D₂ := p₂.val.2
      let hC₂ := lowActiveLeftSupported p₂
      let hD₂ := lowActiveRightSupported p₂
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ left : Bool, let parent := firstSideCharacter F left
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      Rmask ≠ 0 → ∀ hseedfirst : seed ∣ C₁, Squarefree Lproj →
      ((C₁*C₂).absNorm : ℝ) ≤ Z^Bcommon → ((C₁*D₂).absNorm : ℝ) ≤ Z^Bcommon →
      (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 37/10000 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
      0 ≤ profileLoss → 0 ≤ clip → Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor C₁ D₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁))
      let radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
      let pad := 2*sourceLoss+parentLoss+ξ/2+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → nominal+pad ≤ Mcap → nominal+pad+Bmask+ξconductor ≤ d →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 401/9000000 →
      Kcut = Z^(2*A-c-d₁+r₁+e₁-Mparent+max (d₁-c) 0+6*(3/500)+omegaLoss) →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χL χR : RayCharacter,
      let sL := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χL (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      let sR := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        (χR⁻¹) (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      ∀ (holes : O → JointRelativeLabel ηfirst (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ z label,holes z label ≠ 0),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState sL).radial.keep z, low z →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes z) (hholes z) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z (sL.row_ne_zero z hz.1))) →
      (∀ z, ∀ hz : (supportedNaturalState sR).radial.keep z, low (-z) →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes (-z)) (hholes (-z)) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (-z) (neg_ne_zero.mpr (sR.row_ne_zero z hz.1)))) →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν → ∀ i,
        |(t+2*Real.pi*(u-θ))+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ ∧
        |(t+2*Real.pi*(v-(-θ)))+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ Ω : Finset O,
      (∀ z ∈ Ω,sL.radial.keep z ∧ low z) →
      (∀ z ∈ Ω,sR.radial.keep (-z) ∧ low z) →
      (∀ z ∈ Ω,normValue z ≤ dyadicScale (n 1)) →
      ∀ (vBound B₁ B₂ aSource : ℝ), 0 ≤ vBound → 0 ≤ B₁ → 0 ≤ B₂ → 0 < aSource →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        |t+2*Real.pi*(u-θ)| ≤ vBound ∧ |t+2*Real.pi*(v-(-θ))| ≤ vBound) →
      src.W₁ 0 = 0 → src.W₂ 0 = 0 →
      (∀ x, ‖src.W₁ x‖ ≤ B₁) → (∀ x, ‖src.W₂ x‖ ≤ B₂) →
      dyadicScale (n 1) ≤ Z^tailRows → A ≤ tailV →
      aSource*volume src.toData/((C₁*C₂).absNorm : ℝ) ≤ dyadicScale (n 2) →
      aSource*volume src.toData/((C₁*D₂).absNorm : ℝ) ≤ dyadicScale (n 3) →
      src.upper ≤ upper → src.b₁ ≤ bplain₁ → src.b₂ ≤ bplain₂ →
      (Rmask.absNorm : ℝ) ≤ Z^BRmask →
      vBound ≤ (1+4*Real.pi)*Z^ν → height ≤ Z^ν →
      let target := δcommon+nominal+allowance-401/9000000
      lower ≤ target →
      let label : CommonSecondKernelLabel α :=
        ⟨src,Rmask,seed,C₁,Lfirst,hC₁,hseedfirst,parent,p₂,U,Lproj,χL,χR⟩
      let b₂ := (Real.logb Z (C₂.absNorm : ℝ)+Real.logb Z (D₂.absNorm : ℝ))/2
      let outside := A-min c d₁+r₁+e₁-Mparent+5*(3/500)+
        Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
        Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)-b₂+omegaLoss
      let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ p S degree
      let smallLoss := (BRmask+Bcommon)*εmask+ν*(degree : ℝ)
      let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
        (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
      secondPrecountFactor (Z^(A-c)) (actualHighPrimeCount M H Sbad Z) C₂ D₂ U Kcut n*
        (∑ z ∈ Ω, ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*
        label.toKernelLabel.kernelRow t z Wkernel Kcut radius n‖) ≤
        Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
          Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000+smallLoss+primeLoss)+
          (128/aSource)*Eabs^2*pairWeight C₂ D₂*
            Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000-tailSaving+primeLoss)) := by
  obtain ⟨degree,S,hmain⟩ := actual_second_low_kernel_of_common_bin M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro Wkernel decay ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask Sbad primeLoss hν htailRows hprimeLoss
  obtain ⟨Nkernel,Ckernel,hCkernel,hkernel⟩ := hmain Wkernel decay ν tailRows tailV lower tailSaving hν htailRows
  refine ⟨Nkernel,Ckernel,hCkernel,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hkernel η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain,eventually_actual_high_prime_ratio M H hH Sbad primeLoss hprimeLoss] with Z hmain hprime
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ C₂ D₂ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  obtain ⟨hu,hbase⟩ := hmain hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ hCD₂ E₁ ξ₁ ξ₂ F
  refine ⟨hu,?_⟩
  intro left parent U family hfamily hR hseed hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hKmain hne χL χR sL sR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGate hheightSource Ω hkeepL hkeepR hnorm
    vBound B₁ B₂ aSource hvBound hB₁ hB₂ haSource hvCube hz₁ hz₂ hW₁ hW₂ hdyadRows hAtail hphysicalL hphysicalR
    hupper hbplain₁ hbplain₂ hRN hvSmall hhSmall target htarget label Elow smallLoss Eabs
  let b₂ := (Real.logb Z (C₂.absNorm : ℝ)+Real.logb Z (D₂.absNorm : ℝ))/2
  let outside := A-min c d₁+r₁+e₁-Mparent+5*(3/500)+
    Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
    Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)-b₂+omegaLoss
  have hk := hbase left U family hfamily hR hseed hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χL χR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGate hheightSource Ω hkeepL hkeepR hnorm
    vBound B₁ B₂ aSource hvBound hB₁ hB₂ haSource hvCube hz₁ hz₂ hW₁ hW₂ hdyadRows hAtail hphysicalL hphysicalR htarget
  let BL := Cbound*((Rmask*(C₁*C₂)).radical.absNorm : ℝ)^εmask*profileCost src*
    diagonalControl sL.radial.profile*(p.control S)^2*(1+vBound+height)^degree /
      (((C₁*C₂).absNorm : ℝ)*Lproj.absNorm)
  let BR := Cbound*((Rmask*(C₁*D₂)).radical.absNorm : ℝ)^εmask*profileCost src*
    diagonalControl sR.radial.profile*(p.control S)^2*(1+vBound+height)^degree /
      (((C₁*D₂).absNorm : ℝ)*Lproj.absNorm)
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hElow : 0 ≤ Elow := low_fixed_coefficient_nonneg Cbound Mslot upper bplain₁ bplain₂ p S degree hCbound.le
  have hEabs : 0 ≤ Eabs := by dsimp [Eabs]; positivity
  have hNL : 0 < ((C₁*C₂).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hC₁.1 hC₂.1))
  have hNR : 0 < ((C₁*D₂).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hC₁.1 hD₂.1))
  have hLP : 0 < (Lproj.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hLproj.ne_zero)
  have habsL := low_actual_coefficient_absorbed src p S degree Rmask (C₁*C₂) hR (mul_ne_zero hC₁.1 hC₂.1)
    Z Cbound Mslot upper bplain₁ bplain₂ BRmask Bcommon εmask ν vBound height hZ.le hCbound.le hMslot hεmask.le hν.le
    hMs hupper hbplain₁ hbplain₂ hRN hCcap hvBound hheight hvSmall hhSmall
  have habsR := low_actual_coefficient_absorbed src p S degree Rmask (C₁*D₂) hR (mul_ne_zero hC₁.1 hD₂.1)
    Z Cbound Mslot upper bplain₁ bplain₂ BRmask Bcommon εmask ν vBound height hZ.le hCbound.le hMslot hεmask.le hν.le
    hMs hupper hbplain₁ hbplain₂ hRN hDcap hvBound hheight hvSmall hhSmall
  have hBL : BL ≤ (Elow*Z^smallLoss)/(((C₁*C₂).absNorm : ℝ)*Lproj.absNorm) :=
    div_le_div_of_nonneg_right habsL (mul_pos hNL hLP).le
  have hBR : BR ≤ (Elow*Z^smallLoss)/(((C₁*D₂).absNorm : ℝ)*Lproj.absNorm) :=
    div_le_div_of_nonneg_right habsR (mul_pos hNR hLP).le
  have hpair := mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.sqrt_le_sqrt hBL) (Real.sqrt_le_sqrt hBR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (volume_pos src.toData).le (Real.sqrt_nonneg (dyadicScale (n 2)*dyadicScale (n 3))))
  have hphys := low_physical_normalized_pair C₂ D₂ hC₂.1 hD₂.1
    Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss
    (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
    (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
    (δcommon+allowance-(3/500)) (401/9000000) (volume src.toData) (dyadicScale (n 2)) (dyadicScale (n 3))
    ((C₁*C₂).absNorm : ℝ) ((C₁*D₂).absNorm : ℝ) (Lproj.absNorm : ℝ) (Elow*Z^smallLoss) aSource
    hZ (volume_pos _) (dyadicScale_pos _) (dyadicScale_pos _) hNL hNR hLP
    (mul_nonneg hElow (Real.rpow_nonneg hZ0.le _)) haSource hphysicalL hphysicalR
  have htargeteq : δcommon+allowance-(3/500)+nominal+(3/500)-401/9000000 = target := by dsimp [target]; ring
  change Z^outside*(_*Z^(δcommon+allowance-(3/500)+nominal+(3/500)-401/9000000)) ≤ _ at hphys
  rw [htargeteq] at hphys
  have hmainpair : Z^outside*((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      (Real.sqrt BL*Real.sqrt BR)*Z^target) ≤
      (Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
        Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000+smallLoss) := by
    apply ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpair (Real.rpow_nonneg hZ0.le _))
      (Real.rpow_nonneg hZ0.le _)).trans hphys).trans_eq
    conv_rhs => rw [Real.rpow_add hZ0]
    have he : A-c+r₁+e₁+(δcommon+allowance-(3/500))-401/9000000 =
        A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000 := by ring
    rw [he]
    ring
  have hAbsBound := originalAbsoluteProfile_le_fixed src Mslot upper bplain₁ bplain₂ B₁ B₂
    hMslot hB₁ hB₂ hMs hupper hbplain₁ hbplain₂
  have hAbs0 : 0 ≤ originalAbsoluteProfile src B₁ B₂ := by
    unfold originalAbsoluteProfile
    have hpm : 0 ≤ ∏ i,src.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (src.M_ge_one i))
    positivity
  have htail : (128/aSource)*(originalAbsoluteProfile src B₁ B₂)^2*Z^(outside+target-tailSaving) ≤
      (128/aSource)*Eabs^2*Z^(outside+target-tailSaving) := by gcongr
  have hpower : Z^outside*(∑ z ∈ Ω, ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*
      label.toKernelLabel.kernelRow t z Wkernel Kcut radius n‖) ≤
      Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
        Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000+smallLoss)+
        (128/aSource)*Eabs^2*Z^(outside+target-tailSaving)) := by
    apply (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hZ0.le outside)).trans
    calc
      _ = Ckernel*(Z^outside*((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
          (Real.sqrt BL*Real.sqrt BR)*Z^target)+
          (128/aSource)*(originalAbsoluteProfile src B₁ B₂)^2*Z^(outside+target-tailSaving)) := by
        change Z^outside*(Ckernel*((_*_+_)*Z^target)) = _
        simp only [sub_eq_add_neg,Real.rpow_add hZ0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hmainpair htail) hCkernel
  have hid := low_precount_nominal_identity A c d₁ r₁ e₁ Mparent (3/500) omegaLoss
    (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
    (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) b₂
    (δcommon+allowance-(3/500)) (401/9000000)
  change outside+(δcommon+allowance-(3/500)+nominal+(3/500)-401/9000000) = _ at hid
  have htailPower : Z^primeLoss*Z^(outside+target-tailSaving) = pairWeight C₂ D₂*
      Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000-tailSaving+primeLoss) := by
    rw [pairWeight_eq_power C₂ D₂ hC₂.1 hD₂.1 Z hZ,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    change primeLoss+(outside+target-tailSaving) = -b₂+_
    dsimp [target]
    linarith [hid]
  have hpcount : 0 < actualHighPrimeCount M H Sbad Z := hprime.2.1
  have hratio := hprime.2.2
  have hscalar := low_actual_precount_eq C₂ D₂ hC₂ hD₂ U Z A c d₁ r₁ e₁ Mparent omegaLoss
    (actualHighPrimeCount M H Sbad Z) Kcut n hZ hpcount hKmain
  change secondPrecountFactor (Z^(A-c)) (actualHighPrimeCount M H Sbad Z) C₂ D₂ U Kcut n =
    (Z^(3/500 : ℝ)/actualHighPrimeCount M H Sbad Z)*Z^outside at hscalar
  rw [hscalar,mul_assoc]
  apply (mul_le_mul_of_nonneg_left hpower (by positivity)).trans
  calc
    _ ≤ Z^primeLoss*(Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
        Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000+smallLoss)+
        (128/aSource)*Eabs^2*Z^(outside+target-tailSaving))) := by
      apply mul_le_mul_of_nonneg_right hratio
      have hpw := pairWeight_nonneg C₂ D₂
      positivity
    _ = _ := by
      calc
        _ = Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
            (Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000+smallLoss)*Z^primeLoss)+
            (128/aSource)*Eabs^2*(Z^primeLoss*Z^(outside+target-tailSaving))) := by ring
        _ = _ := by
          rw [htailPower,Real.rpow_add hZ0
            (A-c+r₁+e₁+δcommon+allowance-(3/500)-401/9000000+smallLoss) primeLoss]
          ring


#print axioms actual_second_low_physical_kernel_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowPhysicalKernel -/
