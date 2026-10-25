/- Copyright (c) 2026 Sil. Apache-2.0.
Canonical nonfixed energy with both ordinary common punctures and actual
finite marked-prime exclusions. No residual moment hypothesis remains.
-/
import Candidate.SilPrior.FourthPower.NativeFiniteHoles
import Candidate.SilPrior.FourthPower.RestorationCollisionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.SilPrior.FourthPower.NativeMaskedEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentEnergyReferenceScalarBounds
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor QuadraticInitialBound
open NativeFiniteHoles CenteredMomentEnergyReferenceChildProfiles
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem punctured_energy {α : Type*} [Fintype α] [DecidableEq α]
    (Holes : ℕ) (W : ℝ→ℂ) (aslot bslot a b radial Bmask Mcap L Lslot ε lo hi κ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hrad : 0<radial) (hBmask : 0≤Bmask) (hM : 0<Mcap) (hLslot : 0≤Lslot) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R : α→Finset (Ideal O)),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R i).card≤Holes) →
    ∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀p : Profiles a b,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (holeCoefficient (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  let δ : ℝ := ε/(2*(Bmask+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  have hδeq : δ*(2*(Bmask+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hδbudget : Bmask*δ≤ε/2 := by nlinarith
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W aslot bslot lo hi haslot hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := original_energy_weighted_deletion
    (fun _ : α=>bslot) (fun _ : α=>B) (fun _=>hB.le) δ hδ
  obtain ⟨degree,S,hchildren⟩ := NativeFiniteHoles.shortened_children M H hH
    (Finset.univ : Finset α) Holes W aslot bslot a b radial Mcap L Lslot (ε/2) lo hi κ
    haslot hWs hW ha haUpper hb hrad hM hLslot (by linarith) hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cc,hCc,hchildren⟩ := hchildren η₀ hQη
  refine ⟨Cd*Cc,mul_pos hCd hCc,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R hw hwL hσ hσhi hV hfreq hR s hQ hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZpos : 0<Z := zero_lt_one.trans hZ.1
  let P := fun i=>Z^(w i)
  let pool := fun i=>primePool M H bslot (P i)
  let ν := fun i=>relativeCharacter M H hH η₀ (θ i)
  let β₀ := fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let β := holeCoefficient β₀ R
  let E := Cc*diagonalControl s.radial.profile*
    ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε/2)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZpos _
  have hpool (i : α) (I : Ideal O) (hI : I∈pool i) : Prime I := (Finset.mem_filter.mp hI).2.1
  have hcoeff' (i : α) (I : Ideal O) (hI : I∈pool i) :
      ‖β i I‖≤B ∧ (β i I≠0 → (I.absNorm:ℝ)≤bslot*P i) := by
    have hh := hcoeff (ν i) (P i) (σ i) (freq i) 0 (hP i) (hσ i) (hσhi i) I (hpool i I hI).ne_zero
    have ho : ‖β₀ i I‖≤B ∧ (β₀ i I≠0 → (I.absNorm:ℝ)≤bslot*P i) := by
      simpa only [β₀,heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
    by_cases hm : I∈R i
    · simp only [β,holeCoefficient,ite_eq_left hm,norm_zero]
      exact ⟨hB.le,by simp⟩
    · simpa only [β,holeCoefficient,ite_eq_right hm] using ho
  have hD (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport s.puncture).powerset) :
      (∏I∈D,I)≠0 := Finset.prod_ne_zero_iff.mpr (fun I hI=>
        (support_prime s.puncture I (Finset.mem_powerset.mp hD hI)).ne_zero)
  have he := hdelete Z Bmask radial a b s (p.profile 0) (p.profile 1) ha (zero_le_one.trans hb)
    (p.support 0) (p.support 1) pool β P t X₁ X₂ E 0 hpool hP
    (fun i I hI=>(hcoeff' i I hI).1) (fun i I hI=>(hcoeff' i I hI).2)
    hX₁ hX₂ hE (by norm_num) (by
      intro D₁ hD₁ D₂ hD₂ J hJ
      have hh := hZ.2 θ w σ freq t V (fun i _=>hw i) (fun i _=>hwL i)
        (fun i _=>hσ i) (fun i _=>hσhi i) hV (fun i _=>hfreq i) Bmask s hQ hwidth
        (Finset.univ\J) (Finset.subset_univ _) R (fun i _=>hR i) (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
        t t X₁ X₂ hX₁ hX₂ hc₁ hc₂ _ _ (hD D₁ hD₁) (hD D₂ hD₂)
      simpa only [E,pool,β,β₀,P,ν,Real.rpow_zero,mul_one] using hh)
  have hradical : (s.puncture.radical.absNorm:ℝ)^δ≤Z^(ε/2) :=
    (radical_power s δ hδ.le).trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hδbudget)
  apply he.trans
  calc
    _ ≤ Cd*Z^(ε/2)*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hradical hCd.le) hE
    _ = (Cd*Cc)*diagonalControl s.radial.profile*
        ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
      dsimp only [E]
      rw [show s.width+κ*(∑i,w i)+ε=ε/2+(s.width+κ*(∑i,w i)+ε/2) by ring,
        Real.rpow_add hZpos (ε/2) (s.width+κ*(∑i,w i)+ε/2)]
      ring

theorem uniform_energy {α : Type*} [Fintype α] [DecidableEq α]
    (Holes : ℕ) (W : ℝ→ℂ) (aslot bslot a b radial Bmask Mcap L Lslot ε lo hi κ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hrad : 0<radial) (hBmask : 0≤Bmask) (hM : 0<Mcap) (hLslot : 0≤Lslot) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R : α→Finset (Ideal O)),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R i).card≤Holes) →
    ∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀p : Profiles a b,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (holeCoefficient (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,S,henergy⟩ := punctured_energy (α:=α) M H hH Holes W
    aslot bslot a b radial Bmask Mcap L Lslot ε lo hi κ haslot hWs hW ha haUpper hb
    hrad hBmask hM hLslot hε hβ hκ Q hQt hQ72 hQM
  obtain ⟨n,T,Cp,hCp,hprofile⟩ := independent_profile_control a b ha S
  refine ⟨degree+4*n,T,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,henergy⟩ := henergy η₀ hQη
  refine ⟨C*Cp^2*2^(4*n),by positivity,henergy.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R hw hwL hσ hσhi hV hfreq hR s hQ hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have he := hZ.2 θ w σ freq t V R hw hwL hσ hσhi hV hfreq hR s hQ hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  let height : ℝ := 1+|t|+V
  have hh : 0≤height := by dsimp [height]; positivity
  have hpc := p.control_nonneg T
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hprof := hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t
  change (independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S ≤
    Cp*p.control T*(1+‖t‖+‖t‖)^(2*n) at hprof
  have hheight : (1+‖t‖+‖t‖)^(2*n)≤(2*height)^(2*n) := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [height]
    linarith [abs_nonneg t]
  have hp := hprof.trans (mul_le_mul_of_nonneg_left hheight (mul_nonneg hCp.le hpc))
  have hp0 := (independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control_nonneg S
  have hsquare : (Cp*p.control T*(2*height)^(2*n))^2 =
      Cp^2*(p.control T)^2*2^(4*n)*height^(4*n) := by
    rw [mul_pow,mul_pow,←pow_mul,show (2*n)*2=4*n by omega,mul_pow]
    ring
  apply he.trans
  calc
    _ ≤ C*diagonalControl s.radial.profile*(Cp*p.control T*(2*height)^(2*n))^2*
        height^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2) (mul_nonneg hC.le hdiag)
    _ = (C*Cp^2*2^(4*n))*diagonalControl s.radial.profile*(p.control T)^2*
        (1+|t|+V)^(degree+4*n)*Z^(s.width+κ*(∑i,w i)+ε) := by
      rw [hsquare]
      change _=(C*Cp^2*2^(4*n))*diagonalControl s.radial.profile*(p.control T)^2*
        height^(degree+4*n)*Z^(s.width+κ*(∑i,w i)+ε)
      rw [pow_add]
      ring


open CanonicalQuadraticSieve KernelCollisionEnergy RestorationFamily
open RestorationCollisionEnergy
open QRH.Record1252270103TwoIdeal
open QRH.Record1252270103KernelMass
local notation "Id" => Ideal O

/-- Exactly the two families of forbidden marked primes created by the
collision and inverse expansions; no ordinary factor is changed here. -/
def restorationHoles {α : Type*} [Fintype α] (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q}→S) (T : Finset {q // singletonBlock r q}) (ti : T→S) : Finset Id :=
  Finset.univ.image (fun j=> (tc j).val.val) ∪ Finset.univ.image (fun j=>(ti j).val.val)

theorem restoration_coefficients {α : Type*} [Fintype α] (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q}→S) (T : Finset {q // singletonBlock r q}) (ti : T→S)
    (β : α→Id→ℂ) :
    crossBeta T S ti (collisionBeta r S tc β) =
      holeCoefficient (fun q : {q : {q // singletonBlock r q} // q∉T}=>β (singletonRepresentative r q.val))
        (fun _=>restorationHoles r S tc T ti) := by
  funext q I
  let C : Finset Id := Finset.univ.image (fun j=>(tc j).val.val)
  let D : Finset Id := Finset.univ.image (fun j=>(ti j).val.val)
  have hc : (∀j : {q // ¬singletonBlock r q},I≠(tc j).val.val) ↔ I∉C := by
    simp [C,eq_comm]
  have hd : (∀j : T,(ti j).val.val≠I) ↔ I∉D := by
    simp [D]
  have hu : I∈restorationHoles r S tc T ti ↔
      ¬((∀j : {q // ¬singletonBlock r q},I≠(tc j).val.val) ∧
        (∀j : T,(ti j).val.val≠I)) := by
    change I∈C∪D ↔ _
    rw [Finset.mem_union,hc,hd]
    tauto
  dsimp only [crossBeta,collisionBeta,maskedBeta,holeCoefficient]
  simp only [hu]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem restoration_holes_card {α : Type*} [Fintype α] (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q}→S) (T : Finset {q // singletonBlock r q}) (ti : T→S) :
    (restorationHoles r S tc T ti).card≤2*Fintype.card α := by
  have hc : (Finset.univ.image (fun j=>(tc j).val.val)).card≤Fintype.card α := by
    apply Finset.card_image_le.trans
    simpa only [Finset.card_univ] using
      (Fintype.card_subtype_le (fun q=>¬singletonBlock r q)).trans (quotient_card_le r)
  have hd : (Finset.univ.image (fun j=>(ti j).val.val)).card≤Fintype.card α := by
    apply Finset.card_image_le.trans
    simp only [Finset.card_univ,Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ T)).trans
      (by simpa only [Finset.card_univ] using
        (Fintype.card_subtype_le (singletonBlock r)).trans (quotient_card_le r))
  have hu := Finset.card_union_le
    (Finset.univ.image (fun j=>(tc j).val.val)) (Finset.univ.image (fun j=>(ti j).val.val))
  change (restorationHoles r S tc T ti).card≤_ at hu
  omega

end
end Candidate.SilPrior.FourthPower.NativeMaskedEnergy
