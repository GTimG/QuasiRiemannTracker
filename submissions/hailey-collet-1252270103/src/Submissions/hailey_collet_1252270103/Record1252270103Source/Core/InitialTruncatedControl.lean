/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original plain profile controls and actual geometry-bin count turn the
truncated first budget into the normalized physical bound used by G. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstTruncatedPhysical
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstTruncatedBalance
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialProjectedRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialTruncated
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstPhysicalSource
open Cycle61InitialMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.FirstTruncatedHeights
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
local instance initialTruncatedControlDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem plain_profile_control {a b:ℝ}(p:Profiles a b)(S:Finset (ℕ×ℕ))(hS:(0,0)∈S) :
    SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)≤p.control S := by
  have hp (i:Fin 2):SchwartzMap.seminorm ℝ 0 0 (p.profile i)≤sourceControl S (p.profile i):=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (s:=S) (i:=(0,0)) (x:=p.profile i) hS
  exact mul_le_mul (hp 0) (hp 1) (apply_nonneg _ _) (sourceControl_nonneg _ _)

theorem normalized_physical_from_initial_caps {ι:Type}[Fintype ι][DecidableEq ι]
    (W:𝓢(ℝ,ℂ))(smallDegree N:ℕ)(Cs ξ τ ε:ℝ)(hCs:1≤Cs)(hξ:0≤ξ)(hτ:0<τ)(hε:0<ε) :
    ∃J:ℕ,∃Cc Ctotal:ℝ,0<Cc ∧ 0<Ctotal ∧ ∀ᶠZ:ℝ in atTop,∀hZ:1<Z,
    ∀(s:Input ι)(R:Ideal O)(p:Profiles (1/4) (9/4))(S:Finset (ℕ×ℕ))(external Csmall:ℝ),
      (0,0)∈S→Fintype.card ι≤N→(∀i,s.M i≤Cs)→(∀i,1≤s.hi i)→(∀i,s.hi i≤2)→(∀i,1≤s.P i)→
      0≤s.b₁→0≤s.b₂→1≤s.lower→s.W₁=p.profile 0→s.W₂=p.profile 1→
      0<sourceRadius s→sourceRadius s≤Z^(2:ℝ)→1≤volume s→volume s≤Z→
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ))→
      1≤external→0≤Csmall→
      TruncatedBudget W s (markedSourceModifier 1 1 1 1 (fun _=>1)) R 1
        Z Z ξ 1 (Real.logb Z (volume s)) τ 0 external Csmall (zero_lt_one.trans hZ) smallDegree
        (fun _=>(p.control S)^2) geometryDCompensator→
      physicalMass s (markedSourceModifier 1 1 1 1 (fun _=>1)) R 1
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 W Z Z ξ/volume s≤
      Ctotal*(Csmall+Cc)*(p.control S)^2*external^J*Z^(1+ε) := by
  obtain ⟨J,Cc,Cp,hCc,hCp,hphysical⟩:=actual_physical_from_truncated (ι:=ι) W 0 smallDegree N
    Cs 2 (9/4) (1/4) 1 1 1 2 4 ξ τ 0 1 2 hCs (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hξ hτ
    logAnnulus_compact logAnnulus_smooth
  obtain ⟨Cb,hCb,hbins⟩:=High.CoupledFirst.common_geometry_bins_subpower (ι:=ι) 1 1 2 ξ ε
    (by norm_num) (by norm_num) (by norm_num) hξ hε
  refine ⟨J,Cc,max 1 (Cp*Cb),hCc,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  filter_upwards [hphysical,hbins,eventually_ge_atTop (2:ℝ)] with Z hphysical hbins hZ2
  intro hZ s R p S external Csmall hS hN hM hhi0 hhi hP hb₁ hb₂ hlower he₁ he₂
    hsource hsourcecap hVlo hVhi hpool he hCsmall hsmall
  let modifier:Tuple ι→ℂ:=markedSourceModifier 1 1 1 1 (fun _=>1)
  have hZ0:=zero_lt_one.trans hZ
  have hz₁:s.W₁ 0=0:=by rw [he₁];exact initial_plain_zero p (by norm_num) 0
  have hz₂:s.W₂ 0=0:=by rw [he₂];exact initial_plain_zero p (by norm_num) 1
  have hmod (v:Tuple ι):‖modifier v‖≤2:=(marked_modifier_norm v).trans (by norm_num)
  have hlog:|Real.logb Z (volume s)|≤(2:ℝ):=by
    rw [abs_of_nonneg (Real.logb_nonneg hZ hVlo)]
    have hh:Real.logb Z (volume s)≤1:=(Real.logb_le_iff_le_rpow hZ (volume_pos s)).mpr
      (by simpa only [Real.rpow_one] using hVhi)
    linarith
  have hKi:(Z^(1:ℝ))⁻¹≤Z^(1:ℝ):=by
    simp only [Real.rpow_one]
    exact (inv_le_one_of_one_le₀ hZ.le).trans hZ.le
  have hp:=plain_profile_control p S hS
  have hpay:(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*
      volume s≤(p.control S)^2*Z^(1:ℝ):=by
    rw [Real.rpow_one]
    exact mul_le_mul (pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp 2)
      hVhi (volume_pos s).le (sq_nonneg _)
  have hsmall':TruncatedBudget W s modifier R 1 (Z^(1:ℝ)) Z ξ 1 (Real.logb Z (volume s))
      τ 0 external Csmall (Real.rpow_pos_of_pos hZ0 _) smallDegree (fun _=>(p.control S)^2) geometryDCompensator:=by
    simpa only [Real.rpow_one] using hsmall
  have hh:=hphysical.2 s modifier R 1 (p.profile 0) (p.profile 1) 1 external Csmall
    (Real.rpow_pos_of_pos hZ0 _) hN hM hhi0 hhi hP hb₁ hb₂ hlower he₁ he₂
    (p.support 0) (p.support 1) hmod (by simp) one_ne_zero hsource hsourcecap
    (by simpa only [Real.rpow_one] using hVhi) hKi hlog hpool he hCsmall
    (fun _=>(p.control S)^2) geometryDCompensator (fun _ _=>sq_nonneg _) (fun _ _=>geometryDCompensator_pos _)
    (fun _ _=>hpay) (by
      intro key hk reflected
      simpa only [max_eq_left (by norm_num : (1:ℝ)≤2)] using
        actual_geometry_balance_cap s modifier R 1 (Z^(1:ℝ)) Z ξ 2 hZ2 (by simp) hz₁ hz₂ hsourcecap key hk reflected)
    hsmall'
  have hcard:=hbins s modifier R 1 Z hZ0 (by simp) hz₁ hz₂ hsource hsourcecap
    (by simpa only [Real.rpow_one] using hVhi)
    (by simpa only [Real.rpow_one] using hKi)
  have hh':physicalMass s modifier R 1
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 W Z Z ξ≤
      Cp*(Csmall+Cc)*external^J*Z*volume s*
        ((commonGeometryBins s modifier R 1 Z Z ξ).card:ℝ)*(p.control S)^2:=by
    simpa only [Real.rpow_one,add_zero,pow_zero,div_one,Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh
  apply (div_le_iff₀ (volume_pos s)).mpr
  calc
    _≤Cp*(Csmall+Cc)*external^J*Z*volume s*(Cb*Z^ε)*(p.control S)^2:=
      hh'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity)) (sq_nonneg _))
    _=(Cp*Cb)*(Csmall+Cc)*(p.control S)^2*external^J*Z^(1+ε)*volume s:=by
      rw [Real.rpow_add hZ0,Real.rpow_one]
      ring
    _≤_:=by gcongr;exact le_max_right _ _

end
end QRH.Record1252270103Source.InitialTruncated
#print axioms QRH.Record1252270103Source.InitialTruncated.plain_profile_control
#print axioms QRH.Record1252270103Source.InitialTruncated.normalized_physical_from_initial_caps
