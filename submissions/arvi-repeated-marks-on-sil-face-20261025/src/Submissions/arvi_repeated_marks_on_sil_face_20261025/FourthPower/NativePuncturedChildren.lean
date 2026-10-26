/- Copyright (c) 2026 Sil. Apache-2.0.
Common ordinary/marked punctures with independent ordinary heights. The
puncture is expanded at the original fixed conductor; no new character
is inserted into a constant that was chosen before the scale.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativeInjectiveEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskRadialEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativePuncturedChildren
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentAllocatedNaturalRadial CenteredMomentEnergyCapacityRemoval
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor QuadraticInitialBound
open NativeFiniteHoles NativeInjectiveEnergy HeckeDyadic
open CenteredMomentLattice CenteredMomentTwist
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The original full subset estimate supplies every deleted child.
The common puncture may grow polynomially with the scale. Initial marked
holes have a separate fixed cardinality budget. -/
theorem canonical_punctured_subsets (Holes : ℕ)
    (W : ℝ→ℂ) (a b radial Mcap L Lslot Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hBmask : 0≤Bmask) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,(Ideal.absNorm (∏I∈R,I):ℝ)≤Z^Bmask →
    ∀F : Finset α,
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
      radialEnergy (fun z=>polynomial ((naturalCharacter s.character z).excludePrimes R hR)
          false W₁ X₁ 0 t₁ *
        polynomial ((naturalCharacter s.character z).excludePrimes R hR) false W₂ X₂ 0 t₂ *
        ∏i∈F,naturalSlot ((naturalCharacter s.character z).excludePrimes R hR)
          (primePool M H 2 (Z^(w i)))
          (heightCoefficient (holeCoefficient (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  classical
  let δ := ε/(2*(Bmask+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  have hδeq : δ*(2*(Bmask+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hbudget : Bmask*δ≤ε/2 := by nlinarith
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  choose CdF hCdF hdelete using fun F : Finset α=>
    actual_radial_shared_energy F (fun _=>2) (fun _=>B) (fun _ _=>hB.le) δ hδ
  let Cd := 1+∑F : Finset α,CdF F
  have hCd : 0<Cd := by
    have hh := Finset.sum_nonneg (fun F (_ : F∈(Finset.univ : Finset (Finset α)))=>(hCdF F).le)
    dsimp [Cd]
    linarith
  have hCdFCd (F : Finset α) : CdF F≤Cd := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CdF)
      (fun F _=>(hCdF F).le) (Finset.mem_univ F)
    dsimp [Cd]
    linarith
  obtain ⟨degree,S,hchildren⟩ := NativeFiniteHoles.shortened_children M H hH
    (Finset.univ : Finset α) Holes W 1 2 a b radial Mcap L Lslot (ε/2) lo hi κ
    (by norm_num) hWs hW ha haUpper hb hrad hM hLslot (half_pos hε) hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cc,hCc,hchildren⟩ := hchildren η₀ hQη
  refine ⟨Cd*Cc,mul_pos hCd hCc,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR hRcap
    F W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  let P := fun i=>Z^(w i)
  let pool := fun i=>primePool M H 2 (P i)
  let β₀ := fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let E := Cc*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε/2)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Prime I := (Finset.mem_filter.mp hI).2.1
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    have he := (hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).ne_zero).1
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using hB.le
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀] using he
  have hD (D : Finset Id) (hD : D∈R.powerset) : (∏I∈D,I)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun I hI=>(hR I (Finset.mem_powerset.mp hD hI)).ne_zero)
  have he := hdelete F R hR (fun z=>naturalCharacter s.character z)
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    X₁ X₂ a b a b pool βc P (effectiveState s).radial.keep s.radial.profile s.radial.scale E
    hX₁ hX₂ (zero_le_one.trans hb) (zero_le_one.trans hb)
    ((normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁)
    ((normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂)
    (fun i _=>hp i) (fun i _=>hP i) (fun i _=>hβc i)
    (fun i _ I hI _=>canonical_pool_norm_le M H _ (hP i) I hI)
    s.radial.scale_pos s.radial.nonneg hE (by
      intro D₁ hD₁ D₂ hD₂ J hJ
      simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
        CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂]
      exact hZ.2 θ w σ freq t V (fun i _=>hw i) (fun i _=>hwL i)
        (fun i _=>hσ i) (fun i _=>hσhi i) hV (fun i _=>hfreq i) Bstate s hQ hwidth
        (F\J) (Finset.subset_univ _) R₀ (fun i _=>hR₀ i)
        W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ _ _ (hD D₁ hD₁) (hD D₂ hD₂))
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at he
  have hmass : (Ideal.absNorm (∏I∈R,I):ℝ)^δ≤Z^(ε/2) := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg _) hRcap hδ.le
    rw [←Real.rpow_mul hZ0.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbudget)
  apply he.trans
  calc
    _ ≤ Cd*Z^(ε/2)*E := mul_le_mul_of_nonneg_right
      (mul_le_mul (hCdFCd F) hmass (Real.rpow_nonneg (Nat.cast_nonneg _) _) hCd.le) hE
    _ = _ := by
      dsimp only [E]
      rw [show s.width+κ*(∑i,w i)+ε=ε/2+(s.width+κ*(∑i,w i)+ε/2) by ring,
        Real.rpow_add hZ0 (ε/2) (s.width+κ*(∑i,w i)+ε/2)]
      ring

end
end Candidate.FourthPower.NativePuncturedChildren
