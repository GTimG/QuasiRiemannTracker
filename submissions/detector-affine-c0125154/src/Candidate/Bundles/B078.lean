/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B043
import Candidate.Bundles.B076
import Candidate.Bundles.B077
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.Bridge; sha256 695f9e06cebd0b83938717a8ad965ae09f4ccff61dd479e36e35b384947cfa3a -/
section
                                           
                                        

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle61DetectorCount FinalAssembly Cycle61HighTransport

theorem target_positive (A : ChosenData) (hgap : Arithmetic.theta<HeckeZeroSupremum.beta) :
    0<HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have ha : (1/10:ℝ)<Arithmetic.theta+Assembly.signalShift := by
    norm_num [Arithmetic.theta,Assembly.signalShift,Arithmetic.x,Arithmetic.y,Arithmetic.ell]
  linarith

/-- Actual cell bounds and actual count moments imply the literal finite cube bound. -/
theorem fixed_numerator_of_cells (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (J : ℝ) (hcell : ActualFullWCellInput A J)
    (τ : ℝ) (hheight : HeightAdmissible A.D A.P J τ) (η : Character)
    (hcount : ∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) : FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  intro n _
  obtain ⟨Cc,hCc,hcount⟩:=hcount
  obtain ⟨Cs,hCs,hcell⟩:=hcell τ hheight n η
  have hCcpos : 0<Cc:=zero_lt_one.trans_le hCc
  have hηpos : (0:ℝ)<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)
  let C : ℝ:=Cs*Cc*(η.modulus.absNorm:ℝ)^(2*A.P.eps)
  have hC : 0<C:=by dsimp [C];positivity
  obtain ⟨Csum,hCsum,hsum⟩:=fullW_sum_bound A τ n η C hC
  obtain ⟨Ce,hCe,herror⟩:=actual_selected_error A τ hheight.1
  change ∃Ctot : ℝ,0<Ctot ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
      1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid‖ ≤
      Ctot*‖normalizer A.D A.F Z‖*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  refine ⟨Csum+1,by positivity,?_⟩
  filter_upwards [hcount,hcell,hsum,herror,eventually_ge_atTop ((Ce+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_ge_atTop (1:ℝ)] with Z hc hcells hs he hlarge hZ
  intro idx grid hsel
  have hcells : FullWCellsAt A τ n η C Z:=hcells Cc hCc hc
  have hb:=hs hcells idx grid hsel
  obtain ⟨hN,herr⟩:=he n η idx grid hsel
  have hZp : 0<Z:=zero_lt_one.trans_le hZ
  have hsaving : Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ))≤1 := by
    calc
      _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hlarge,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
      _ = 1 := by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hZp.ne'
  have hone : (1:ℝ)≤Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) :=
    Real.one_le_rpow hZ (target_positive A hgap).le
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
    1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid
  let W := fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
    (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)
  let N := normalizer A.D A.F Z
  let E := Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  have hnormalized : ‖V/N‖≤(Csum+1)*E := by
    calc
      _ = ‖(V/N-W/N)+W/N‖ := by rw [sub_add_cancel]
      _ ≤ ‖V/N-W/N‖+‖W/N‖ := norm_add_le _ _
      _ ≤ 1+Csum*E := add_le_add (herr.trans hsaving) hb
      _ ≤ (Csum+1)*E := by dsimp [E];nlinarith only [hone]
  rw [norm_div] at hnormalized
  have hraw:=(div_le_iff₀ (norm_pos_iff.mpr hN)).mp hnormalized
  simpa only [V,N,E,mul_assoc,mul_comm,mul_left_comm] using hraw

/-- The only remaining analytic input is the initial affine moment at this fixed data. -/
theorem fixed_numerator_of_affine (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
      ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ))) → FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  obtain ⟨J,hJ,hcells⟩:=actual_cells_of_affine hgap A hAffine
  exact ⟨J,hJ,fun τ hheight η hcount=>fixed_numerator_of_cells hgap A J hcells τ hheight η hcount⟩
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.Bridge -/

/- BEGIN ORIGINAL Cycle61.Assembly.ChosenAffine; sha256 250a3b6177f4a8c3b7331203f3eb6e16415cb30039cb65aefb3e96c238a7c8ff -/
section
                                  
                                      

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open OAI.SevenEighths

/-- The genuine initial affine theorem is needed for one fixed choice of data. -/
def ChosenAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃A : ChosenData,Numerator.Source.ActualAffineInput A

/-- An analytic mesh cap is chosen before constructing slots and source data. -/
def MeshAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃meshCap : ℝ,0 < meshCap ∧ ∀A : ChosenData,A.P.mesh ≤ meshCap →
      Numerator.Source.ActualAffineInput A

theorem chosen_affine_of_mesh (hinput : MeshAffineInput) : ChosenAffineInput := by
  intro hβ
  obtain ⟨meshCap,hmesh,haffine⟩:=hinput hβ
  obtain ⟨A,hA⟩:=exists_chosen_data_with_mesh hβ hmesh
  exact ⟨A,haffine A hA⟩

theorem chosen_finite_numerator_of_affine (hinput : ChosenAffineInput) :
    ChosenFiniteNumeratorInput := by
  intro hβ
  obtain ⟨A,hAffine⟩:=hinput hβ
  obtain ⟨J,hJ,hfinite⟩:=FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  exact ⟨A,J,hJ,hfinite⟩

theorem common_probe_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_finite_numerator hdet (chosen_finite_numerator_of_affine hinput)

theorem common_probe_of_mesh_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : MeshAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_affine hdet (chosen_affine_of_mesh hinput)

theorem beta_le_theta_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤Arithmetic.theta :=
  Cycle25.beta_le_of_common_probe Assembly.theta_gt_half.le Assembly.theta_lt_seven_eighths.le
    (common_probe_of_chosen_affine hdet hinput)

theorem beta_le_rational_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤(437423/500000:ℝ) :=
  beta_le_theta_of_chosen_affine hdet hinput

theorem hecke_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (χ : HeckeFamily.Character) (s : ℂ) (hs : Arithmetic.theta<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_chosen_affine hdet hinput).trans_lt hs) hpole

theorem dirichlet_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : Arithmetic.theta<s.re) (hexc : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) χ s hs hexc

/-- Mathlib's total zeta convention includes its nonzero value at 1. -/
theorem riemannZeta_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) : riemannZeta s≠0 :=
  Cycle25.zeta_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) s hs

/-- The classical zeta region explicitly excludes the pole. -/
theorem zeta_nonzero_off_pole_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) (_hpole : s≠1) : riemannZeta s≠0 :=
  riemannZeta_nonzero_of_chosen_affine hdet hinput s hs
end
end Cycle61.FinalAssembly

#print axioms Cycle61.FinalAssembly.chosen_affine_of_mesh
#print axioms Cycle61.FinalAssembly.chosen_finite_numerator_of_affine
#print axioms Cycle61.FinalAssembly.common_probe_of_chosen_affine
#print axioms Cycle61.FinalAssembly.common_probe_of_mesh_affine
#print axioms Cycle61.FinalAssembly.beta_le_theta_of_chosen_affine
#print axioms Cycle61.FinalAssembly.beta_le_rational_of_chosen_affine
#print axioms Cycle61.FinalAssembly.hecke_nonzero_of_chosen_affine
#print axioms Cycle61.FinalAssembly.dirichlet_nonzero_of_chosen_affine
#print axioms Cycle61.FinalAssembly.riemannZeta_nonzero_of_chosen_affine
#print axioms Cycle61.FinalAssembly.zeta_nonzero_off_pole_of_chosen_affine

end
/- END ORIGINAL Cycle61.Assembly.ChosenAffine -/

/- BEGIN ORIGINAL Cycle61.Physical.ExternalHeight; sha256 7579ae49caa5ac8af6406acd186daed16dc13a94e9c2965957284eca3eab0f60 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                 
                     

namespace Cycle61.Physical
noncomputable section

/-- A fixed power loss in the scale is harmless on the large external-height
range. The extra integer degree is chosen before the scale and height. -/
theorem exists_external_height_degree {τ : ℝ} (hτ : 0<τ) (extra ε : ℝ) :
    ∃ n : ℕ, ∀ Z H m : ℝ, 1≤Z → Z^τ≤H →
      Z^(m+extra) ≤ H^n*Z^(m+ε) := by
  obtain ⟨n,hn⟩ := exists_nat_ge ((extra-ε)/τ)
  have hdegree : extra-ε≤τ*(n:ℝ) := by
    have hh := (div_le_iff₀ hτ).mp hn
    simpa only [mul_comm] using hh
  refine ⟨n,?_⟩
  intro Z H m hZ hH
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hZp.le τ) hH n
  calc
    _ ≤ Z^((m+ε)+τ*n) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    _ = (Z^τ)^n*Z^(m+ε) := by
      rw [Real.rpow_add hZp,Real.rpow_mul_natCast hZp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hZp.le _)

/-- Combine the bounded-height analytic estimate and a genuine all-height
coarse estimate. No threshold may depend on the live external height. -/
theorem extend_bounded_height_bound {τ : ℝ} (hτ : 0<τ) (extra ε : ℝ)
    (jSmall jCoarse : ℕ) :
    ∃ j : ℕ, ∀ Z H m E control Csmall Ccoarse : ℝ,
      1≤Z → 1≤H → 0≤control → 0≤Csmall → 0≤Ccoarse →
      (H≤Z^τ → E≤Csmall*control*H^jSmall*Z^(m+ε)) →
      E≤Ccoarse*control*H^jCoarse*Z^(m+extra) →
      E≤(Csmall+Ccoarse)*control*H^j*Z^(m+ε) := by
  obtain ⟨n,hn⟩ := exists_external_height_degree hτ extra ε
  let j := max jSmall (jCoarse+n)
  refine ⟨j,?_⟩
  intro Z H m E control Csmall Ccoarse hZ hH hc hCs hCc hsmall hcoarse
  have hHp : 0≤H := zero_le_one.trans hH
  have hZp : 0≤Z^(m+ε) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hb : H≤Z^τ
  · apply (hsmall hb).trans
    apply mul_le_mul_of_nonneg_right _ hZp
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by linarith : Csmall≤Csmall+Ccoarse) hc)
      (pow_le_pow_right₀ hH (le_max_left _ _)) (pow_nonneg hHp _) (by positivity)
  · have hlarge := hn Z H m hZ (le_of_not_ge hb)
    have hbnd := hcoarse.trans (mul_le_mul_of_nonneg_left hlarge
      (mul_nonneg (mul_nonneg hCc hc) (pow_nonneg hHp _)))
    have heq : Ccoarse*control*H^jCoarse*(H^n*Z^(m+ε)) =
        Ccoarse*control*H^(jCoarse+n)*Z^(m+ε) := by rw [pow_add];ring
    rw [heq] at hbnd
    apply hbnd.trans
    apply mul_le_mul_of_nonneg_right _ hZp
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by linarith : Ccoarse≤Csmall+Ccoarse) hc)
      (pow_le_pow_right₀ hH (le_max_right _ _)) (pow_nonneg hHp _) (by positivity)

end
end Cycle61.Physical

#print axioms Cycle61.Physical.exists_external_height_degree
#print axioms Cycle61.Physical.extend_bounded_height_bound

end
/- END ORIGINAL Cycle61.Physical.ExternalHeight -/

/- BEGIN ORIGINAL Cycle61.Assembly.Baseline; sha256 874562c4e59f8ddfe75215559803ff78a3c6f5f418f5c51967f0ccc1a645dfee -/
section
                                                                      
                                   

/-! Only the original 7/8 endpoint is used to initialize the supremum.
The bound from the earlier quartic submission is not an input here. -/
namespace Cycle61.Assembly

open OAI.SevenEighths Arithmetic

theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : theta < HeckeZeroSupremum.beta) :
    (7/10 : ℝ) ≤ 2*HeckeZeroSupremum.beta-1 ∧
    2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ) ∧
    (51/100 : ℝ) ≤ HeckeZeroSupremum.beta ∧
    kappaStar < 2*HeckeZeroSupremum.beta-1 := by
  have hhi := baseline_beta
  have hlo : (17/20 : ℝ) < theta := by norm_num [theta]
  have hk := kappaStar_eq
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem kappa_gap (β : ℝ) :
    (2*β-1)-kappaStar = 2*(β-theta) := by
  rw [kappaStar_eq]
  ring

end Cycle61.Assembly

end
/- END ORIGINAL Cycle61.Assembly.Baseline -/
