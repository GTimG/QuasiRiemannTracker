/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B022
import Submissions.affine_local_20261013.Bundles.B025
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B037
import Submissions.affine_local_20261013.Bundles.B044
import Submissions.affine_local_20261013.Bundles.B071
import Submissions.affine_local_20261013.Bundles.B072
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowChoiceEnergy

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.OriginalActualMoments ; sha256 35ea6875f534f2bba343fe9d3a0543566a56e2f69a7e9fdd4c88d859ef041c1c -/
section





namespace OAI.SevenEighths.Cycle25ProbeFinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open Cycle25ProbeDetectorPlainMarkedFineField

/-- Actual physical source moments from the completed energy endpoint, on the
same mesh used by the physical numerator. -/
theorem weighted_actual_old_source_moments {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤ Cycle25.sourceMesh D.t/200) :
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        old_sourceMomentBound F counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle25ProbeFinalAssemblyCertifiedBands.old_source_moments F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta)
end
end OAI.SevenEighths.Cycle25ProbeFinalAssembly
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.OriginalActualMoments -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.FourierProfiles ; sha256 117bd8dab512a95ebb655926238eabdecd99bddfc903cdaff6b7e911389047a8 -/
section



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyProfiles
open CenteredMomentEnergyReferenceChild CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentDetectorDictionary
open CenteredMomentNaturalMaskedFloor CenteredMomentRetainedProfile CenteredMomentLattice

/-- Fixed conjugated annular derivative tests used after reflecting the numerator. -/
def numeratorAnnular (j : Fin 2) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (derivativeChoice annulusTemplate.profile j)

lemma numeratorAnnular_apply (j : Fin 2) :
    (numeratorAnnular j : ℝ → ℂ) =
      fun x=> conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x) := by
  change (fun x=> conj (derivativeChoice annulusTemplate.profile j x)) = _
  rw [derivativeChoice_apply]
  rfl

lemma numeratorAnnular_support (j : Fin 2) :
    Function.support (numeratorAnnular j : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4) := by
  rw [numeratorAnnular_apply,conjugate_profile_support]
  intro x hx
  have hh := scaleTest_support (fun y:ℝ=>(annulus y:ℂ)) (1/4) 1 annulus_support j hx
  exact ⟨hh.1,hh.2.trans (by norm_num)⟩

def numeratorFourierProfiles (j k : Fin 2) (v w : ℝ) : Profiles (1/4) (9/4) :=
  independentProfiles (by norm_num) (numeratorAnnular j) (numeratorAnnular k)
    (numeratorAnnular_support j) (numeratorAnnular_support k) (-2*Real.pi*v) (-2*Real.pi*w)

/-- The two unbounded Fourier frequencies have independently controlled polynomial
growth. This fixed degree is chosen before any final contour-height parameter. -/
theorem numerator_fourier_profiles_control (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ, ∃C : ℝ, 0 < C ∧ ∀j k : Fin 2, ∀v w : ℝ,
      (numeratorFourierProfiles j k v w).control S ^2 ≤
        C*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨J,T,C,hC,hc⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) S
  let A : ℝ := 1+∑j:Fin 2, sourceControl T (numeratorAnnular j)
  have hA : 0 < A := by
    have hh := Finset.sum_nonneg (fun j (_:j∈Finset.univ)=> sourceControl_nonneg T (numeratorAnnular j))
    dsimp [A]; linarith
  have hA' (j : Fin 2) : sourceControl T (numeratorAnnular j) ≤ A := by
    have hh := Finset.single_le_sum
      (fun j (_:j∈Finset.univ)=> sourceControl_nonneg T (numeratorAnnular j)) (Finset.mem_univ j)
    dsimp [A]; linarith
  let B := C*A*(1+2*Real.pi)^J
  have hB : 0 < B := by dsimp [B]; positivity
  have hone (j : Fin 2) (v : ℝ) :
      sourceControl S (normPowerProfile (numeratorAnnular j) (1/4) (9/4) (by norm_num)
        (numeratorAnnular_support j) ((numeratorAnnular j).smooth ⊤) (-2*Real.pi*v))
        ≤ B*(1+‖v‖)^J := by
    have hh := hc (numeratorAnnular j) (numeratorAnnular_support j) (-2*Real.pi*v)
    have hv : 1+‖-2*Real.pi*v‖ ≤ (1+2*Real.pi)*(1+‖v‖) := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
      norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
      nlinarith [Real.pi_pos,norm_nonneg v]
    calc
      _ ≤ C*sourceControl T (numeratorAnnular j)*(1+‖-2*Real.pi*v‖)^J := hh
      _ ≤ C*A*((1+2*Real.pi)*(1+‖v‖))^J := by
        gcongr
        exact hA' j
      _ = _ := by dsimp [B]; rw [mul_pow]; ring
  refine ⟨J,B^4,by positivity,?_⟩
  intro j k v w
  have hh : (numeratorFourierProfiles j k v w).control S ≤
      (B*(1+‖v‖)^J)*(B*(1+‖w‖)^J) := by
    simpa only [numeratorFourierProfiles,independentProfiles,Profiles.control,
      Fin.zero_eta,ite_true,show (1:Fin 2)≠0 by decide,ite_false] using
      mul_le_mul (hone j v) (hone k w) (sourceControl_nonneg _ _) (by positivity)
  calc
    _ ≤ ((B*(1+‖v‖)^J)*(B*(1+‖w‖)^J))^2 :=
      pow_le_pow_left₀ (Profiles.control_nonneg _ _) hh 2
    _ = _ := by ring

lemma numerator_fourier_polynomial_zero (χ : Character) (j k : Fin 2)
    (v w X : ℝ) :
    polynomial χ false ((numeratorFourierProfiles j k v w).profile 0) X 0 0 =
      polynomial χ false (fun x=> conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x))
        X 0 (-2*Real.pi*v) := by
  change polynomial χ false (normPowerProfile _ _ _ _ _ _ _) X 0 0 = _
  rw [twist_polynomial,numeratorAnnular_apply]

lemma numerator_fourier_polynomial_one (χ : Character) (j k : Fin 2)
    (v w X : ℝ) :
    polynomial χ false ((numeratorFourierProfiles j k v w).profile 1) X 0 0 =
      polynomial χ false (fun x=> conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k x))
        X 0 (-2*Real.pi*w) := by
  change polynomial χ false (normPowerProfile _ _ _ _ _ _ _) X 0 0 = _
  rw [twist_polynomial,numeratorAnnular_apply]

lemma inverse_annular_norm_eq {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (u : FreeRow) (j : Fin 2)
    (v X : ℝ) (hX : 0 < X) :
    ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X 0 (2*Real.pi*v)‖ =
    ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
      (momentElement u)) false (fun x=> conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x))
        X 0 (-2*Real.pi*v)‖ := by
  have hh := polynomial_inverse_norm (rowCharacter F.S F.exclusions.prime u) false
    (fun x=> conj (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j x)) X 0 (-2*Real.pi*v) hX
  simp only [Complex.conj_conj,neg_mul,neg_neg] at hh
  rw [hh,numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad]
  congr 2 <;> ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.FourierProfiles -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Scalar.SourceLoss ; sha256 bcafeb4d14ab01201c1d38784ec7e649c069ca2faed507d8d4bc6e74066cc117 -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/



noncomputable section
namespace Cycle25.Numerator.Scalar
open OAI.SevenEighths.CenteredMomentEnergyWidthRanges
open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

theorem sourceMesh_le {t : ℝ} (ht : 0 < t) : sourceMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ := bounds 2
    (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)
  change mesh 2 (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

/-- Annular padding uses the actual moment parameter. The common mesh cost
remains explicit until the loss budget is applied. -/
def weightedSourceLoss (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ) : ℝ :=
  3*t+(17/25)*t+
    d*(2*eps+massEps+(3*(159*epsilon+9*t)+momentEps)/4+
      delta*mesh/4+delta*boxWidth/4+q*annulus/(6*kap))+t*ell

theorem weightedSourceLoss_le
    (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hk : 7/10 ≤ kap) (_hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hq : 0 ≤ q) (hq1 : q ≤ delta/2)
    (hepsilon : 0 ≤ epsilon) (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (hmesh : 0 ≤ mesh) (hmesh1 : mesh ≤ t)
    (hmass : 0 ≤ massEps) (hmass1 : massEps ≤ t)
    (hmoment : 0 ≤ momentEps) (hmoment1 : momentEps ≤ 2*t)
    (hbox : 0 ≤ boxWidth) (hbox1 : boxWidth ≤ t)
    (hannulus : 0 ≤ annulus) (hannulus1 : annulus ≤ t) :
    weightedSourceLoss kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus ≤
      120*epsilon+2*eps+13*t := by
  have hk0 : 0 < 6*kap := by linarith
  have hdm : delta*mesh ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hmesh1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hdb : delta*boxWidth ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hbox1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hqt : q*annulus ≤ (3/8)*t :=
    (mul_le_mul_of_nonneg_left hannulus1 hq).trans
      (mul_le_mul_of_nonneg_right (by linarith : q ≤ 3/8) ht)
  have hann : q*annulus/(6*kap) ≤ t/10 := by
    apply (div_le_iff₀ hk0).2
    have hm := mul_le_mul_of_nonneg_right hk ht
    nlinarith
  have hinner : 0 ≤ 2*eps+massEps+(3*(159*epsilon+9*t)+momentEps)/4+
      delta*mesh/4+delta*boxWidth/4+q*annulus/(6*kap) := by positivity
  have hdinner := mul_le_mul_of_nonneg_right hd1 hinner
  have hell : t*ell ≤ t/5 := by
    have hm := mul_le_mul_of_nonneg_left ell_lt_one_fifth.le ht
    linarith
  unfold weightedSourceLoss
  nlinarith only [hdinner,hdm,hdb,hann,hmass1,hmoment1,hepsilon,ht,hell]

theorem weighted_source_packet_exponent
    (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hk : kap ≠ 0) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -ly/2-(4/25)*ell+(3+17/25)*t+t*ell+
      d*(2*eps+massEps+q*(ell/d)-
        q*((2*(ly/d)-1)/(6*kap)-annulus/(3*kap))/2+
        (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
          159*epsilon+9*t)+1+momentEps)/4+
        delta*mesh/4+delta*boxWidth/4-17/50) =
      numeratorExponent kap d delta (q/delta)+
        weightedSourceLoss kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus := by
  unfold numeratorExponent weightedSourceLoss
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

theorem weighted_source_uniform_packet_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) :
    16*D.e+(120*D.ε+2*D.eps+13*D.t)+D.t ≤ (beta-theta)/50 := by
  have hn : 0 ≤ D.eps*(D.N:ℝ) := mul_nonneg D.eps_pos.le (Nat.cast_nonneg _)
  have htell : 0 ≤ D.t*ell := mul_nonneg D.t_pos.le ell_pos.le
  have hb := D.central_budget
  nlinarith only [hb,hn,htell,D.e_pos,D.epsilon_pos,D.eps_pos,D.t_pos]

theorem weighted_source_packet_fixed_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) (d delta q : ℝ)
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hq : 0 ≤ q) (hq1 : q ≤ delta/2) :
    16*D.e+weightedSourceLoss D.momentKappa d delta q D.ε D.eps D.t
      (sourceMesh D.t) D.t (2*D.t) D.t D.t+D.t ≤ (beta-theta)/50 := by
  have hl := weightedSourceLoss_le D.momentKappa d delta q D.ε D.eps D.t
    (sourceMesh D.t) D.t (2*D.t) D.t D.t D.momentKappa_lo hd hd1 hdelta hdelta1 hq hq1
    D.epsilon_pos.le D.eps_pos.le D.t_pos.le (sourceMesh_pos D.t_pos).le
    (sourceMesh_le D.t_pos) D.t_pos.le le_rfl (mul_nonneg (by norm_num) D.t_pos.le) le_rfl
    D.t_pos.le le_rfl D.t_pos.le le_rfl
  linarith [weighted_source_uniform_packet_budget D]

/-- The height reserve is retained, while every loss shrinks with beta-theta.
The tighter geometric top is necessary when beta approaches theta. -/
theorem weighted_source_packet_certificate_of_kappa {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) (hbeta : theta < beta)
    (hkap : D.momentKappa = 2*beta-1)
    (d a q : ℝ) (hd : 1/2 ≤ d) (hdtop : d ≤ h+3*D.t)
    (ha : 1/3 ≤ 2*a-1) (ha1 : a ≤ 7/8)
    (hq : 0 ≤ q) (hq1 : q ≤ (2*a-1)/2) :
    numeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
      weightedSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t
        (sourceMesh D.t) D.t (2*D.t) D.t D.t ≤
      signal beta-(beta-theta)/2-weightedSourceSZExponent a D.e-D.t := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdelta1 : 2*a-1 ≤ 3/4 := by linarith
  have hd1 : d ≤ 1 := by linarith [h_interval.2,D.t_small]
  have hp : 0 ≤ q/(2*a-1) ∧ q/(2*a-1) ≤ 1/2 :=
    ⟨div_nonneg hq hdelta.le,(div_le_iff₀ hdelta).2 (by linarith)⟩
  have hb := numerator_supremum_improvement hbeta hd hd1 D.t_pos.le hdtop
    ⟨hdelta.le,hdelta1⟩ hp
  have hbudget := weighted_source_packet_fixed_budget D d (2*a-1) q
    (by linarith) hd1 hdelta.le hdelta1 hq hq1
  rw [←hkap] at hb
  have heq : (1+(2*a-1))/2=a := by ring
  rw [heq] at hb
  have hsz : weightedSourceSZExponent a D.e=weightedSourceSZExponent a 0+16*D.e := by
    unfold weightedSourceSZExponent
    ring
  rw [hsz]
  linarith [D.t_gap]

theorem weighted_source_packet_certificate
    (D : HighParameters.HighData (OAI.SevenEighths.HeckeZeroSupremum.beta-theta))
    (hbeta : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (d a q : ℝ) (hd : 1/2 ≤ d) (hdtop : d ≤ h+3*D.t)
    (ha : 1/3 ≤ 2*a-1) (ha1 : a ≤ 7/8)
    (hq : 0 ≤ q) (hq1 : q ≤ (2*a-1)/2) :
    numeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
      weightedSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t
        (sourceMesh D.t) D.t (2*D.t) D.t D.t ≤
      signal OAI.SevenEighths.HeckeZeroSupremum.beta-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-
        weightedSourceSZExponent a D.e-D.t := by
  exact weighted_source_packet_certificate_of_kappa D hbeta D.momentKappa_exact
    d a q hd hdtop ha ha1 hq hq1

end Cycle25.Numerator.Scalar
end
/- END ORIGINAL MODULE Cycle25.Numerator.Scalar.SourceLoss -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.SlotSelection ; sha256 1effe0bfeef42bad8e019c9acc4e5a4584e5714229f7ddff57a2bd2cc996b0b5 -/
section





/-!
Greedy prime-slot selection for the reflected numerator. Error slots have gain zero,
but retain their lengths in the denominator of q. No amplitude frontier is assumed.
-/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator.SlotSelection
open OAI.SevenEighths
open HeckeDetectorSlotSelection HeckeDetectorPhysicalSelection
open Cycle25

def baseCapacity (kap d : ℝ) : ℝ := (2*ly/d-1)/(6*kap)
def reflectedCapacity (kap d v : ℝ) : ℝ := max 0 (baseCapacity kap d-v/(3*kap))

theorem reflectedCapacity_nonneg (kap d v : ℝ) : 0 ≤ reflectedCapacity kap d v := le_max_left _ _

theorem baseCapacity_lt_supply {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1/2:ℝ) ≤ d) :
    baseCapacity kap d < ell/d := by
  have hd0 : 0 < d := by linarith
  have hk0 : kap ≠ 0 := by linarith
  have hh := div_lt_div_of_pos_right (numerator_supply_all hk hd) hd0
  have heq : ((2*ly-d)/(6*kap))/d = baseCapacity kap d := by
    unfold baseCapacity
    field_simp
  rwa [heq] at hh

theorem reflectedCapacity_le_supply {kap d v : ℝ} (hk : 7/10 ≤ kap)
    (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) : reflectedCapacity kap d v ≤ ell/d := by
  apply max_le
  · exact div_nonneg ell_pos.le (by linarith)
  · have hh := baseCapacity_lt_supply hk hd
    have hdiv : 0 ≤ v/(3*kap) := div_nonneg hv (by linarith)
    linarith

theorem reflectedCapacity_gain {kap d v q : ℝ} (hq : 0 ≤ q) :
    q*baseCapacity kap d-q*v/(3*kap) ≤ q*reflectedCapacity kap d v := by
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (baseCapacity kap d-v/(3*kap))) hq
  simpa only [mul_sub, mul_div_assoc, reflectedCapacity] using hh

/-- Exact selection from a main mask. Zero-gain error slots remain in the mean's
normalizing sum, and are excluded only from the selected product. -/
theorem zero_error_whole_slots {α : Type*} (slots main : Finset α) (w g : α→ℝ)
    (δ mesh z : ℝ) (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh)
    (hw : ∀i∈slots,0 ≤ w i) (hwm : ∀i∈slots,w i ≤ mesh)
    (hL : 0 < ∑i∈slots,w i)
    (hg : ∀i∈slots,0 ≤ g i ∧ g i ≤ δ/2)
    (herror : ∀i∈slots,i∉main → g i=0)
    (hz : 0 ≤ z) (hzL : z ≤ ∑i∈slots,w i) :
    ∃selected : Finset α,selected⊆slots ∧ selected⊆main ∧
      (∀i∈selected,0 < g i) ∧ (∑i∈selected,w i) ≤ z ∧
      weightedMean slots w g*z-(δ/2)*mesh ≤ ∑i∈selected,w i*g i ∧
      ∀U : ℝ,1 ≤ U → ∀Q : α→ℂ,
        (∀i∈slots,0 < g i → U^(2*w i*g i) ≤ ‖Q i‖^2) →
        U^(2*weightedMean slots w g*z-δ*mesh) ≤ ‖∏i∈selected,Q i‖^2 := by
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ hw hL hg
  have hmean : weightedMean slots w g*(∑i∈slots,w i) ≤ ∑i∈slots,w i*max (g i) 0 := by
    have he : (∑i∈slots,w i*max (g i) 0)=∑i∈slots,w i*g i :=
      Finset.sum_congr rfl (fun i hi=> by rw [max_eq_left (hg i hi).1])
    rw [he]
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots slots w g (δ/2) mesh
    (by positivity) hmesh hw hwm (fun i hi=>(hg i hi).2)
    (weightedMean slots w g) z hq hqδ hz hzL hmean
  have hTm : T⊆main := by
    intro i hi
    by_contra hn
    have he := herror i (hTs hi) hn
    have hh := hTpos i hi
    rw [he] at hh
    exact lt_irrefl 0 hh
  refine ⟨T,hTs,hTm,hTpos,hTz,hgain,?_⟩
  intro U hU Q hQ
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  calc
    _ ≤ U^(∑i∈T,2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑i∈T,2*w i*g i)=2*(∑i∈T,w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith only [hgain])
    _ = ∏i∈T,U^(2*w i*g i) := Real.rpow_sum_of_pos hU0 _ _
    _ ≤ ∏i∈T,‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi=> Real.rpow_nonneg hU0.le _)
      (fun i hi=> hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem highData_weighted_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (hfine : ∀j,D.ell j ≤ sourceMesh D.t/200)
    (d v δ : ℝ) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ δ/2) (herror : ∀j,j∉main → g j=0) :
    let widths := fun j=> D.ell j/d
    let q := weightedMean Finset.univ widths g
    let mesh := sourceMesh D.t
    q = (∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ δ/2 ∧
    ∃selected : Finset (Fin D.N),selected⊆main ∧ (∀j∈selected,0 < g j) ∧
      (∑j∈selected,widths j) ≤ reflectedCapacity D.momentKappa d v ∧
      q*reflectedCapacity D.momentKappa d v-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      q*baseCapacity D.momentKappa d-q*v/(3*D.momentKappa)-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      ∀U : ℝ,1 ≤ U → ∀Q : Fin D.N→ℂ,
        (∀j,0 < g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*reflectedCapacity D.momentKappa d v-δ*mesh) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hd0 : 0 < d := by linarith only [hd]
  let widths := fun j=> D.ell j/d
  have hsum : (∑j,widths j)=ell/d := by
    dsimp [widths]
    rw [←Finset.sum_div,D.slots_sum]
  have hL : 0 < ∑j,widths j := by rw [hsum];exact div_pos ell_pos hd0
  have hw (j : Fin D.N) : 0 ≤ widths j := (div_pos (D.slots_bounds j).1 hd0).le
  have hmesh := sourceMesh_pos D.t_pos
  have hwm (j : Fin D.N) : widths j ≤ sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have hj := hfine j
    nlinarith only [hj,hd,hmesh]
  have hzL : reflectedCapacity D.momentKappa d v ≤ ∑j,widths j := by
    rw [hsum]
    exact reflectedCapacity_le_supply D.momentKappa_lo hd hv
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds Finset.univ widths g δ (fun j _=> hw j) hL (fun j _=> hg j)
  obtain ⟨T,_,hT,hTpos,hTz,hgain,hspike⟩ := zero_error_whole_slots Finset.univ main widths g δ
    (sourceMesh D.t) (reflectedCapacity D.momentKappa d v) hδ hmesh.le (fun j _=> hw j)
    (fun j _=> hwm j) hL (fun j _=> hg j) (fun j _=> herror j)
    (reflectedCapacity_nonneg D.momentKappa d v) hzL
  refine ⟨?_,hq,hqδ,T,hT,hTpos,hTz,hgain,?_,?_⟩
  · unfold weightedMean
    rw [hsum]
  · exact (sub_le_sub_right (reflectedCapacity_gain hq) _).trans hgain
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _=> hQ j)

end Cycle25.Numerator.SlotSelection

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.SlotSelection -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowChoiceEnergy ; sha256 788fbe6c2f5f79dd864ca7f5894a904c57bfbcd692de9348f1a63c12449d5037 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowChoiceEnergy.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_original_choice_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ K : rows,∀ p : supportedSlotChoices lists (poolPrimeFamily J Q Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily lists hmax hgood p.val)).generator Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ p : supportedSlotChoices lists (poolPrimeFamily J Q Q₀).ideal K.val,
        (∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) σ)
          (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+505*η-O₀/2) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_dyadic_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  obtain ⟨Cb,hCb,hbins⟩ := actual_dyad_count_budget 8 η (by norm_num) hη
  refine ⟨degree,Cb*C,max Z₀ (max 2 Ck),mul_pos hCb hC,hZ₀.trans_le (le_max_left _ _),?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  have hZbase : Z₀≤ Z := (le_max_left _ _).trans hZ
  have hCkZ : Ck≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let FF := (poolPrimeFamily J Q Q₀).ideal
  let tuples := fixedSlotTupleSet lists FF
  let hm := originalTupleMax lists FF hmax
  let hg := originalTupleGood lists FF hgood
  have htuples : ∀ p∈tuples,∀ i,p i∈lists i := fun p hp => ((mem_fixedSlotTupleSet lists FF p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤ Z^ell0 := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  let Hrow := (Ck*Z^((1-Submission20261012.Global.ell)-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
  let Hslot := Z^ell0
  obtain ⟨Dc,hDc⟩ := he g J F Q₀ hJ hF A Z d ell0 shift O₀
    hZbase hd hd1 hell hellcap hshift hOeq
    parents rows hparents hsub hbad tuples hm hg (fixedSlotTupleSet_product_injective lists FF hdis hprime)
    hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let D := fun (K : rows) (p : supportedSlotChoices lists FF K.val) =>
    memberChoiceControlled lists FF hmax hgood G K.val (hrows K.val K.property)
      (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K) p
  refine ⟨D,?_⟩
  intro θ w hw
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc (s g) (hc₀ g)
        (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(1+ell0+shift)) (fun _ => 1)
        (fixedTupleCoefficient lists w) K p)=
      ∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) := by
    simpa only [dyadicPhysicalTerm,D,one_mul] using member_source_eq_original_choices lists FF hmax hgood G K.val
      (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) 1 w
  have hb := hDc θ (fun _ => 1) (fixedTupleCoefficient lists w) (by simp) (fun p hp => fixedTupleCoefficient_norm lists w hw p)
  have hid : (∑ K : rows,‖∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(1+ell0+shift))
      (fun _ => 1) (fixedTupleCoefficient lists w) K p‖^2)=
      ∑ K : rows,‖∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hsource K)
  apply (hid.symm.trans_le hb).trans
  have hz : 1< Z := lt_of_lt_of_le hZ₀ hZbase
  have hzpos : 0< Z := lt_trans zero_lt_one hz
  have hp : (1:ℝ)≤ Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
  have hm' : (1:ℝ)≤ Ideal.absNorm (rowMaskPart J Q) :=
    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) Q)
  have hRpos : 0< Hrow := by dsimp [Hrow];positivity
  have hScap : Hslot≤ Z^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])
  have hRcap : Hrow≤ Z^(8:ℝ) := by
    apply (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hp hm')).trans
    calc
      Ck*Z^((1-Submission20261012.Global.ell)-2*d) ≤ Z*Z^((1-Submission20261012.Global.ell)-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzpos.le _)
      _ = Z^(1+((1-Submission20261012.Global.ell)-2*d)) := by rw [Real.rpow_add hzpos,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])
  have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzpos _) hRcap hScap
  calc
    _ ≤ (Cb*Z^(η))*(C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+504*η-O₀/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (Cb*C)*(1+‖θ‖)^degree*Z^(η+(((1-Submission20261012.Global.ell)-d)+504*η-O₀/2)) := by
      rw [Real.rpow_add hzpos];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])) (by positivity)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowChoiceEnergy -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SlotSelection ; sha256 689954d8c204d14d749cd375f8bd59129fc315c514d0acecfd4f917d90a4f2d8 -/
section





/-!
Greedy prime-slot selection for the reflected numerator. Error slots have gain zero,
but retain their lengths in the denominator of q. No amplitude frontier is assumed.
-/
noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.Numerator.SlotSelection
open OAI.SevenEighths
open HeckeDetectorSlotSelection HeckeDetectorPhysicalSelection
open Cycle25

def baseCapacity (kap d : ℝ) : ℝ := (2*ly/d-1)/(6*kap)
def reflectedCapacity (kap d v : ℝ) : ℝ := max 0 (baseCapacity kap d-v/(3*kap))

theorem reflectedCapacity_nonneg (kap d v : ℝ) : 0 ≤ reflectedCapacity kap d v := le_max_left _ _

theorem baseCapacity_lt_supply {kap d : ℝ} (hk : 7/10 ≤ kap) (hd : (1/2:ℝ) ≤ d) :
    baseCapacity kap d < ell/d := by
  have hd0 : 0 < d := by linarith
  have hk0 : kap ≠ 0 := by linarith
  have hh := div_lt_div_of_pos_right (numerator_supply_all hk hd) hd0
  have heq : ((2*ly-d)/(6*kap))/d = baseCapacity kap d := by
    unfold baseCapacity
    field_simp
  rwa [heq] at hh

theorem reflectedCapacity_le_supply {kap d v : ℝ} (hk : 7/10 ≤ kap)
    (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) : reflectedCapacity kap d v ≤ ell/d := by
  apply max_le
  · exact div_nonneg ell_pos.le (by linarith)
  · have hh := baseCapacity_lt_supply hk hd
    have hdiv : 0 ≤ v/(3*kap) := div_nonneg hv (by linarith)
    linarith

theorem reflectedCapacity_gain {kap d v q : ℝ} (hq : 0 ≤ q) :
    q*baseCapacity kap d-q*v/(3*kap) ≤ q*reflectedCapacity kap d v := by
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (baseCapacity kap d-v/(3*kap))) hq
  simpa only [mul_sub, mul_div_assoc, reflectedCapacity] using hh

/-- Exact selection from a main mask. Zero-gain error slots remain in the mean's
normalizing sum, and are excluded only from the selected product. -/
theorem zero_error_whole_slots {α : Type*} (slots main : Finset α) (w g : α→ℝ)
    (δ mesh z : ℝ) (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh)
    (hw : ∀i∈slots,0 ≤ w i) (hwm : ∀i∈slots,w i ≤ mesh)
    (hL : 0 < ∑i∈slots,w i)
    (hg : ∀i∈slots,0 ≤ g i ∧ g i ≤ δ/2)
    (herror : ∀i∈slots,i∉main → g i=0)
    (hz : 0 ≤ z) (hzL : z ≤ ∑i∈slots,w i) :
    ∃selected : Finset α,selected⊆slots ∧ selected⊆main ∧
      (∀i∈selected,0 < g i) ∧ (∑i∈selected,w i) ≤ z ∧
      weightedMean slots w g*z-(δ/2)*mesh ≤ ∑i∈selected,w i*g i ∧
      ∀U : ℝ,1 ≤ U → ∀Q : α→ℂ,
        (∀i∈slots,0 < g i → U^(2*w i*g i) ≤ ‖Q i‖^2) →
        U^(2*weightedMean slots w g*z-δ*mesh) ≤ ‖∏i∈selected,Q i‖^2 := by
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ hw hL hg
  have hmean : weightedMean slots w g*(∑i∈slots,w i) ≤ ∑i∈slots,w i*max (g i) 0 := by
    have he : (∑i∈slots,w i*max (g i) 0)=∑i∈slots,w i*g i :=
      Finset.sum_congr rfl (fun i hi=> by rw [max_eq_left (hg i hi).1])
    rw [he]
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots slots w g (δ/2) mesh
    (by positivity) hmesh hw hwm (fun i hi=>(hg i hi).2)
    (weightedMean slots w g) z hq hqδ hz hzL hmean
  have hTm : T⊆main := by
    intro i hi
    by_contra hn
    have he := herror i (hTs hi) hn
    have hh := hTpos i hi
    rw [he] at hh
    exact lt_irrefl 0 hh
  refine ⟨T,hTs,hTm,hTpos,hTz,hgain,?_⟩
  intro U hU Q hQ
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  calc
    _ ≤ U^(∑i∈T,2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑i∈T,2*w i*g i)=2*(∑i∈T,w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith only [hgain])
    _ = ∏i∈T,U^(2*w i*g i) := Real.rpow_sum_of_pos hU0 _ _
    _ ≤ ∏i∈T,‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi=> Real.rpow_nonneg hU0.le _)
      (fun i hi=> hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem highData_weighted_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (hfine : ∀j,D.ell j ≤ sourceMesh D.t/200)
    (d v δ : ℝ) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ δ/2) (herror : ∀j,j∉main → g j=0) :
    let widths := fun j=> D.ell j/d
    let q := weightedMean Finset.univ widths g
    let mesh := sourceMesh D.t
    q = (∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ δ/2 ∧
    ∃selected : Finset (Fin D.N),selected⊆main ∧ (∀j∈selected,0 < g j) ∧
      (∑j∈selected,widths j) ≤ reflectedCapacity D.momentKappa d v ∧
      q*reflectedCapacity D.momentKappa d v-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      q*baseCapacity D.momentKappa d-q*v/(3*D.momentKappa)-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      ∀U : ℝ,1 ≤ U → ∀Q : Fin D.N→ℂ,
        (∀j,0 < g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*reflectedCapacity D.momentKappa d v-δ*mesh) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hd0 : 0 < d := by linarith only [hd]
  let widths := fun j=> D.ell j/d
  have hsum : (∑j,widths j)=ell/d := by
    dsimp [widths]
    rw [←Finset.sum_div,D.slots_sum]
  have hL : 0 < ∑j,widths j := by rw [hsum];exact div_pos ell_pos hd0
  have hw (j : Fin D.N) : 0 ≤ widths j := (div_pos (D.slots_bounds j).1 hd0).le
  have hmesh := sourceMesh_pos D.t_pos
  have hwm (j : Fin D.N) : widths j ≤ sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have hj := hfine j
    nlinarith only [hj,hd,hmesh]
  have hzL : reflectedCapacity D.momentKappa d v ≤ ∑j,widths j := by
    rw [hsum]
    exact reflectedCapacity_le_supply D.momentKappa_lo hd hv
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds Finset.univ widths g δ (fun j _=> hw j) hL (fun j _=> hg j)
  obtain ⟨T,_,hT,hTpos,hTz,hgain,hspike⟩ := zero_error_whole_slots Finset.univ main widths g δ
    (sourceMesh D.t) (reflectedCapacity D.momentKappa d v) hδ hmesh.le (fun j _=> hw j)
    (fun j _=> hwm j) hL (fun j _=> hg j) (fun j _=> herror j)
    (reflectedCapacity_nonneg D.momentKappa d v) hzL
  refine ⟨?_,hq,hqδ,T,hT,hTpos,hTz,hgain,?_,?_⟩
  · unfold weightedMean
    rw [hsum]
  · exact (sub_le_sub_right (reflectedCapacity_gain hq) _).trans hgain
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _=> hQ j)

end Submission20261012.Global.Numerator.SlotSelection

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.SlotSelection -/
