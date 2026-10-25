/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Hailey Collet PR69 PhysicalDirect/Fourier and Hybrid, retaining
Gao/OpenAI physical Fourier and natural terminal estimates. The small-shift
source is now the full downward domain, including zero and small widths.
 -/
import Candidate.Feedback.FourthPower.ReturnPhysicalInput
import Candidate.Feedback.FourthPower.ReturnPhysicalSchedule
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.CertifiedFourier
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.CertifiedZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace Candidate.Feedback.FourthPower.ReturnPhysicalFourier
open ReturnSourceFaces ReturnCertificate ReturnPhysicalInput ReturnPhysicalSchedule

open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentEnergyBands CenteredMomentRowNorm
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentNaturalPrimitive
open ProbePhysical CenteredMomentWholeSlotDeletion
open Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

/-- Full-domain physical Fourier pair. The analytic premise is the actual
initial radial energy, not a row fourth moment or an improved zero-free endpoint. -/
theorem full_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (bΦ mesh ε : ℝ) (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bΦ mesh ε U degree control Ci) :
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) → (∀i,(z i).re=17/50) →
      0≤ height → (∀i,|(z i).im|≤ height) →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      fullSourceFace.Admissible (length U X₁) (length U X₂) (∑i,width i) 1 →
      ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨J,Cp,hCp,hprofile⟩:=numerator_fourier_profiles_control control
  let C:=Ci*(1+diagonalControl radialMajorant)*Cp
  have hC:0< C:=by have:=diagonalControl_nonneg radialMajorant;dsimp [C];positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hinput,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (η.modulus.absNorm:ℝ)] with U ha hkeep hU hη
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hadm j k v w
  have he:=finite_physical_pair_full F rows radialMajorant U bΦ mesh ε hU.le hsΦ
    radialMajorant_nonneg hη (fun u hu=>(hrows u hu).2)
    (fun u hu=>hkeep u (hrows u hu).1) radialMajorant_one degree control Ci ha
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w) X₁ X₂
    hX₁ hX₂ hadm
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏i,normalizedSlot η rowMaskElement 1 u.val (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd:=diagonalControl_nonneg radialMajorant
  have hp:=hprofile j k v w
  calc
    _ ≤ (Ci*(1+diagonalControl radialMajorant))*
        (Cp*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*(1+height)^degree*U^(1+ε) := by
      gcongr
      linarith
    _ = _ := by dsimp [C];ring


/-- The full downward source handles ALL smaller plains and slot subsets in
our small-shift region. Only the genuine large-shift natural and empty-slot
bounds remain. The cutoff in the displayed domain is exactly 1/250. -/
theorem full_hybrid_fourier {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hk0 : 7/10≤ κ) (hk1 : κ≤3/4) (hb : 51/100≤ HeckeZeroSupremum.beta)
    (hkb : 2*HeckeZeroSupremum.beta-1≤ κ)
    (bΦ mesh ε : ℝ) (hε : 0< ε)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bΦ mesh ε U di control Ci) :
    ∃degree J:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height n:ℝ,
      (∀i,0≤ width i) → (∀i,width i≤ mesh) →
      (∀i,width i≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i,(z i).re=17/50) → 0≤ height → (∀i,|(z i).im|≤ height) →
      0≤ n → n≤2 →
      ((∃d t:ℝ,ds≤ d ∧ d≤ dplus ∧ 0≤ t ∧ t≤ shiftCutoff ∧
        n=shiftedPlain d t ∧ (∑i,width i)≤ shiftedWidth d t) ∨
        (2*n+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ → X₁≤ U^n → X₂≤ U^n →
      length U X₁≤ n → length U X₂≤ n → ∀j k:Fin 2,∀v w:ℝ,
      (∑u∈rows,‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
      ≤ (C*(1+height)^degree*U^(1+D.t+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨Ja,Ca,hCa,ha⟩:=full_fourier F bΦ mesh ε hsΦ di control Ci hCi hinput
  obtain ⟨dp,Jp,Cp,hCp,hp⟩:=certified_reflected_fourier_moment F κ hk0 hk1 hb hkb
  obtain ⟨Jz,Cz,hCz,hz⟩:=certified_reflected_zero_fourier_moment F
  refine ⟨di+dp,Ja+Jp+Jz,Ca+Cp+Cz,by positivity,?_⟩
  filter_upwards [ha,hp,hz] with U ha hp hz
  have hU:=ha.1
  have hUp:=zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows T width z height n hw hmesh hwmax hzre hh him hn hn2 hcap X₁ X₂ hX₁ hX₂ hX₁max hX₂max hx₁ hx₂ j k v w
  have hsum:0≤∑i,width i:=Finset.sum_nonneg (fun i _=>hw i)
  have hUε:U^(1+ε)≤ U^(1+D.t+ε):=Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  have hUt:U^(1+D.t)≤ U^(1+D.t+ε):=Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  have baseline (hbudget : 2*n+6*κ*(∑i,width i)≤1) := by
    have hn1:n≤1:=by nlinarith only [hbudget,hk0,hsum]
    have hpow:U^n≤ U:=by simpa using Real.rpow_le_rpow_of_exponent_le hU.le hn1
    have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
      (hX₁max.trans hpow) (hX₂max.trans hpow) (by linarith) j k v w
    exact hb'
  rcases hcap with ⟨d,t,hd0,hd1,ht0,ht1,heq,hslots⟩ | hold
  · have hadm := ReturnAnalyticFinish.physical_full_face_downward
      hd0 hd1 ht0 ht1 (length_nonneg U X₁ hU) (length_nonneg U X₂ hU) hsum
      (by simpa only [heq] using hx₁) (by simpa only [heq] using hx₂) hslots
    have hbound := ha.2 rows hrows T width z height hw hmesh hzre hh him
      X₁ X₂ hX₁ hX₂ hadm j k v w
    apply hbound.trans
    gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
  · rcases hold with hbudget | hempty
    · apply (baseline hbudget).trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · subst T
      simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
      have hb':=hz.2 rows hrows X₁ X₂ hX₁ hX₂
        (hX₁max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2))
        (hX₂max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2)) j k v w
      apply hb'.trans
      have hheight:1≤(1+height)^(di+dp):=one_le_pow₀ (by linarith)
      have hc:Cz≤(Ca+Cp+Cz)*(1+height)^(di+dp):=by nlinarith
      gcongr <;> first | exact hc | linarith [norm_nonneg v,norm_nonneg w]


end Candidate.Feedback.FourthPower.ReturnPhysicalFourier
