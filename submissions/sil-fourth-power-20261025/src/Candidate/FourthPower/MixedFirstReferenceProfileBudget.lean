/- Copyright (c) 2026 Sil. Apache-2.0.
Common homogeneous controls for the actual shifted reference profiles.
The dispatcher uses the original Schwartz profiles with frequencies
(t_j+t)/(2*pi), and the marked coefficient at t0+t. No profile, scale,
height, live subtype or Z is fixed before the constants in this file.
-/
import Candidate.FourthPower.MixedFirstProfileEnvelope
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstReferenceProfileBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyProfiles
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentRetainedProfile
open CenteredMomentEnergyReferenceChild
open CenteredMomentScaleSupremum CenteredMomentCommonMaskEnergy
open MixedPrincipalPair MixedPrincipalWindow MixedFirstFullBudget MixedFirstPaidPhysical
open MixedFirstProfileEnvelope MixedCanonicalSource
local notation "Id" => Ideal HeckeFamily.O

private lemma control_mono {S T : Finset (ℕ×ℕ)} (h : S ⊆ T) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S W ≤ sourceControl T W :=
  Seminorm.le_def.mp (Finset.sup_mono h) W

/-- The exact frequencies in height_rectangle_canonical fit one common
reference height. This includes both orientations of the short rectangle. -/
theorem shifted_reference_height (t V t₁ t₂ : ℝ) (hV : 0 ≤ V) :
    let Href := |t|+‖t₁‖+‖t₂‖
    0 ≤ Href ∧ ‖(t₁+t)/(2*Real.pi)‖ ≤ Href ∧
      ‖(t₂+t)/(2*Real.pi)‖ ≤ Href ∧
      1+Href ≤ MixedFirstProfileEnvelope.height t V t₁ t₂ := by
  have h₁ := (CenteredMomentHeight.normalized_height_le (t₁+t)).trans (norm_add_le t₁ t)
  have h₂ := (CenteredMomentHeight.normalized_height_le (t₂+t)).trans (norm_add_le t₂ t)
  simp only [Real.norm_eq_abs] at h₁ h₂
  dsimp only [MixedFirstProfileEnvelope.height]
  simp only [Real.norm_eq_abs]
  exact ⟨by positivity,by linarith [abs_nonneg t₂],by linarith [abs_nonneg t₁],by linarith⟩

/-- The marked coefficient keeps t0+t literally. On every actual prime
pool its norm, including each fixed hole zero, equals the old norm. -/
theorem shifted_slot_norm {ι : Type*} [Fintype ι]
    (ν : ι → Character) (R₀ : ι → Finset Id) (t₀ t : ℝ)
    (i : ι) (I : Id) (hI : I ≠ 0) (Wslot : ℝ → ℂ) (P : ℝ) :
    ‖slotCoefficient ν R₀ (t₀+t) i I*Wslot (I.absNorm/P)‖ =
      ‖slotCoefficient ν R₀ t₀ i I*Wslot (I.absNorm/P)‖ := by
  rw [norm_mul,norm_mul]
  simp only [slotCoefficient]
  rw [heightCoefficient_norm _ (t₀+t) I hI,heightCoefficient_norm _ t₀ I hI]

private theorem scale_tests_control :
    ∃ T : Finset (ℕ×ℕ), ∃ D : ℝ, 0 < D ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ j : Fin 2, ∀ x : ℝ,
        ‖scaleTest W j x‖ ≤ D*sourceControl T W := by
  obtain ⟨T,D,hD,hcontrol⟩ := derivative_choice_control ({(0,0)} : Finset (ℕ×ℕ))
  refine ⟨T,D,hD,?_⟩
  intro W j x
  have hpoint : ‖scaleTest W j x‖ ≤ sourceControl {(0,0)} (derivativeChoice W j) := by
    have hp := SchwartzMap.norm_le_seminorm ℝ (derivativeChoice W j) x
    rw [derivativeChoice_apply] at hp
    simpa only [sourceControl,Finset.sup_singleton,schwartzSeminormFamily] using hp
  exact hpoint.trans (hcontrol W j)

/-- Uniform controls for the exact ordinary profiles and both reference
orientations. The extra set permits the same controls to dominate the
already-proved first physical profile envelope. No energy bound is assumed. -/
theorem uniform_profile_controls (a b : ℝ) (ha : 0 < a)
    (Sref Sextra : Finset (ℕ×ℕ)) (nref : ℕ) :
    ∃ T : Finset (ℕ×ℕ), ∃ J : ℕ, ∃ C D : ℝ,
      0 < C ∧ 0 < D ∧ Sextra ⊆ T ∧ (0,0) ∈ T ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ), ∀ hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b,
      ∀ hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b,
      ∀ t V t₁ t₂ : ℝ, 0 ≤ V →
      let A := sourceControl T W₁*sourceControl T W₂
      let H := MixedFirstProfileEnvelope.height t V t₁ t₂
      let Href := |t|+‖t₁‖+‖t₂‖
      (∀ j x, ‖scaleTest W₁ j x‖ ≤ D*sourceControl T W₁) ∧
      (∀ j x, ‖scaleTest W₂ j x‖ ≤ D*sourceControl T W₂) ∧
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ (t₁+t) (t₂+t)).control Sref)^2 ≤ C*A^2*H^J ∧
      (sourceControl Sref W₂)^2*(1+Href)^(2*nref)*(D*sourceControl T W₁)^2 ≤ C*A^2*H^J ∧
      (sourceControl Sref W₁)^2*(1+Href)^(2*nref)*(D*sourceControl T W₂)^2 ≤ C*A^2*H^J := by
  obtain ⟨np,Tp,Cp,hCp,hprofile⟩ := independent_profile_control a b ha Sref
  obtain ⟨Td,D,hD,hscale⟩ := scale_tests_control
  let T := (((Sextra ∪ Sref) ∪ Tp) ∪ Td) ∪ {(0,0)}
  let J := 4*np+2*nref
  let C := 1+Cp^2*2^(4*np)+D^2
  have hC : 0 < C := by dsimp only [C]; positivity
  have heT : Sextra ⊆ T := by intro x hx; simp [T,hx]
  have hrT : Sref ⊆ T := by intro x hx; simp [T,hx]
  have hpT : Tp ⊆ T := by intro x hx; simp [T,hx]
  have hdT : Td ⊆ T := by intro x hx; simp [T,hx]
  refine ⟨T,J,C,D,hC,hD,heT,by simp [T],?_⟩
  intro W₁ W₂ hs₁ hs₂ t V t₁ t₂ hV
  dsimp only
  let A := sourceControl T W₁*sourceControl T W₂
  let H := MixedFirstProfileEnvelope.height t V t₁ t₂
  let Href := |t|+‖t₁‖+‖t₂‖
  have hA : 0 ≤ A := mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hH : 1 ≤ H := by
    dsimp only [H,MixedFirstProfileEnvelope.height]
    linarith [abs_nonneg t,norm_nonneg t₁,norm_nonneg t₂]
  have hH0 := zero_le_one.trans hH
  have hHref : 1+Href ≤ H := (shifted_reference_height t V t₁ t₂ hV).2.2.2
  have hsum : 1+‖t₁+t‖+‖t₂+t‖ ≤ 2*H := by
    have h₁ := norm_add_le t₁ t
    have h₂ := norm_add_le t₂ t
    rw [Real.norm_eq_abs t] at h₁ h₂
    dsimp only [H,MixedFirstProfileEnvelope.height]
    linarith [norm_nonneg t₁,norm_nonneg t₂]
  have hpair : sourceControl Tp W₁*sourceControl Tp W₂ ≤ A :=
    mul_le_mul (control_mono hpT W₁) (control_mono hpT W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofile' : (independentProfiles ha W₁ W₂ hs₁ hs₂ (t₁+t) (t₂+t)).control Sref ≤
      Cp*A*(2*H)^(2*np) :=
    (hprofile W₁ W₂ hs₁ hs₂ (t₁+t) (t₂+t)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hpair hCp.le)
        (pow_le_pow_left₀ (by positivity) hsum _) (by positivity) (mul_nonneg hCp.le hA))
  have hCpC : Cp^2*2^(4*np) ≤ C := by
    dsimp only [C]
    linarith [sq_nonneg D]
  have hDC : D^2 ≤ C := by
    dsimp only [C]
    have hnonneg : 0 ≤ Cp^2*2^(4*np) := by positivity
    linarith
  have hprofiles : ((independentProfiles ha W₁ W₂ hs₁ hs₂ (t₁+t) (t₂+t)).control Sref)^2 ≤
      C*A^2*H^J := by
    calc
      _ ≤ (Cp*A*(2*H)^(2*np))^2 := pow_le_pow_left₀ (Profiles.control_nonneg _ _) hprofile' 2
      _ = (Cp^2*2^(4*np))*A^2*H^(4*np) := by
        rw [mul_pow,mul_pow,←pow_mul,show (2*np)*2=4*np by omega,mul_pow]
        ring
      _ ≤ C*A^2*H^J := mul_le_mul
        (mul_le_mul_of_nonneg_right hCpC (sq_nonneg A))
        (pow_le_pow_right₀ hH (by dsimp only [J];omega))
        (pow_nonneg hH0 _) (mul_nonneg hC.le (sq_nonneg A))
  have hreference (Wshort Wlong : 𝓢(ℝ,ℂ)) :
      (sourceControl Sref Wlong)^2*(1+Href)^(2*nref)*(D*sourceControl T Wshort)^2 ≤
        C*(sourceControl T Wshort*sourceControl T Wlong)^2*H^J := by
    have hc := control_mono hrT Wlong
    have hp := pow_le_pow_left₀ (sourceControl_nonneg _ _) hc 2
    have hh := pow_le_pow_left₀ (by dsimp only [Href];positivity) hHref (2*nref)
    calc
      _ = D^2*(sourceControl T Wshort)^2*(sourceControl Sref Wlong)^2*(1+Href)^(2*nref) := by ring
      _ ≤ D^2*(sourceControl T Wshort)^2*(sourceControl T Wlong)^2*H^(2*nref) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hh
          (by dsimp only [Href];positivity) (by positivity)
      _ = D^2*(sourceControl T Wshort*sourceControl T Wlong)^2*H^(2*nref) := by ring
      _ ≤ C*(sourceControl T Wshort*sourceControl T Wlong)^2*H^J := mul_le_mul
        (mul_le_mul_of_nonneg_right hDC (sq_nonneg _))
        (pow_le_pow_right₀ hH (by dsimp only [J];omega))
        (pow_nonneg hH0 _) (mul_nonneg hC.le (sq_nonneg _))
  refine ⟨?_,?_,hprofiles,hreference W₁ W₂,?_⟩
  · intro j x
    exact (hscale W₁ j x).trans (mul_le_mul_of_nonneg_left (control_mono hdT W₁) hD.le)
  · intro j x
    exact (hscale W₂ j x).trans (mul_le_mul_of_nonneg_left (control_mono hdT W₂) hD.le)
  · simpa only [A,mul_comm (sourceControl T W₂) (sourceControl T W₁)] using hreference W₂ W₁

/-- One set and degree now pay BOTH the actual first physical envelope
and both short-reference profile factors. Constants precede every finite
live source type and Z; only the already-required scalar slot cap remains. -/
theorem uniform_source_budget (U : Controls) (c : Constants) (Q : Id)
    (a b cstar Kslot : ℝ) (ha : 0 < a) (hcstar : 0 < cstar)
    (hKslot : 1 ≤ Kslot) (N : ℕ) (Sref : Finset (ℕ×ℕ)) (nref : ℕ) :
    ∃ T : Finset (ℕ×ℕ), ∃ J : ℕ, ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ (0,0) ∈ T ∧
      ∀ (ι : Type u) [Fintype ι], ∀ s : Source ι a b, Fintype.card ι ≤ N →
      s.d=(1,1) → (∀ i,s.M i ≤ Kslot) → ∀ c0 t V : ℝ, cstar ≤ c0 → 0 ≤ V →
      let A := sourceControl T s.W₁*sourceControl T s.W₂
      let H := MixedFirstProfileEnvelope.height t V s.t₁ s.t₂
      let Href := |t|+‖s.t₁‖+‖s.t₂‖
      profileEnvelope U c s Q c0 t V ≤ C*A^2*H^J ∧
      (∀ j x,‖scaleTest s.W₁ j x‖ ≤ D*sourceControl T s.W₁) ∧
      (∀ j x,‖scaleTest s.W₂ j x‖ ≤ D*sourceControl T s.W₂) ∧
      ((independentProfiles ha s.W₁ s.W₂ s.hs₁ s.hs₂ (s.t₁+t) (s.t₂+t)).control Sref)^2 ≤ C*A^2*H^J ∧
      (sourceControl Sref s.W₂)^2*(1+Href)^(2*nref)*(D*sourceControl T s.W₁)^2 ≤ C*A^2*H^J ∧
      (sourceControl Sref s.W₁)^2*(1+Href)^(2*nref)*(D*sourceControl T s.W₂)^2 ≤ C*A^2*H^J := by
  obtain ⟨T,J,Cp,D,hCp,hD,hT,h00,hprofiles⟩ :=
    uniform_profile_controls a b ha Sref (profileControl U) nref
  obtain ⟨Ce,hCe,henvelope⟩ := uniform_profile_envelope U c Q a b cstar Kslot ha hcstar hKslot N
  refine ⟨T,J+heightDegree U,Cp+Ce,D,by positivity,hD,h00,?_⟩
  intro ι _ s hcard hd hM c0 t V hc0 hV
  dsimp only
  let A := sourceControl T s.W₁*sourceControl T s.W₂
  let H := MixedFirstProfileEnvelope.height t V s.t₁ s.t₂
  have hH : 1 ≤ H := by
    dsimp only [H,MixedFirstProfileEnvelope.height]
    linarith [abs_nonneg t,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hH0 := zero_le_one.trans hH
  have hprof := hprofiles s.W₁ s.W₂ s.hs₁ s.hs₂ t V s.t₁ s.t₂ hV
  have hcommon : Cp*A^2*H^J ≤ (Cp+Ce)*A^2*H^(J+heightDegree U) := mul_le_mul
    (mul_le_mul_of_nonneg_right (by linarith : Cp ≤ Cp+Ce) (sq_nonneg A))
    (pow_le_pow_right₀ hH (by omega)) (pow_nonneg hH0 _) (by positivity)
  have henv := henvelope ι s hcard hd hM c0 t V hc0 hV
  have hpair : sourceControl (profileControl U) s.W₁*sourceControl (profileControl U) s.W₂ ≤ A :=
    mul_le_mul (control_mono hT s.W₁) (control_mono hT s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hePaid : profileEnvelope U c s Q c0 t V ≤ (Cp+Ce)*A^2*H^(J+heightDegree U) := by
    apply henv.trans
    exact mul_le_mul
      (mul_le_mul (by linarith : Ce ≤ Cp+Ce)
        (pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)) hpair 2)
        (sq_nonneg _) (by positivity))
      (pow_le_pow_right₀ hH (by omega)) (pow_nonneg hH0 _) (by positivity)
  exact ⟨hePaid,hprof.1,hprof.2.1,hprof.2.2.1.trans hcommon,
    hprof.2.2.2.1.trans hcommon,hprof.2.2.2.2.trans hcommon⟩

end
end Candidate.FourthPower.MixedFirstReferenceProfileBudget
