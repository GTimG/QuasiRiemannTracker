/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform artificial-source constants for every live marked subset of a
fixed original index type. Selected norm factors and weights are unchanged.
-/
import Candidate.Feedback.FourthPower.MixedAllocatedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedUniformAllocated
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedLiteralAllocation MixedAllocatedEnergy
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance (T : Finset α) : DecidableEq (T⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem uniform_allocated_subsets
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R F : Id,R≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport (R*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀T : Finset α,
      (∀i : T,∀P∈H,P.val∈R₀ i.val) → ∀D : Id,D∣F →
    ∀allocation : Allocation D (Finset.univ : Finset (T⊕Fin 2)),
      radialEnergy (fun z=>allocatedRow (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
          (fun i : T=>supportedPool (primePool M Hray 2 (Z^(w i.val)))) d hd D R allocation
          (slotCoefficient (fun i : T=>relativeCharacter M Hray hHray η₀ (θ i.val))
            (fun i=>R₀ i.val) t)
          (fun i : T=>slotProfile W (σ i.val) (freq i.val)) (fun i : T=>Z^(w i.val))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(F.absNorm:ℝ)^δ/pairNorm d/
        ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i : selectedLive D allocation,w i.val.val)+ε) := by
  choose degreeT controlT hbase using fun T : Finset α=>
    uniform_allocated_energy (α:=T) M Hray hHray Holes W
      a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ
      hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hδ hβ hκ Q hQt hQ72 hQM
  let degree := ∑T : Finset α,degreeT T
  let S := (Finset.univ : Finset (Finset α)).biUnion controlT
  have hn (T : Finset α) : degreeT T≤degree :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hS (T : Finset α) : controlT T⊆S := Finset.subset_biUnion_of_mem controlT (Finset.mem_univ T)
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  choose CT hCT hbase using fun T=>hbase T η₀ hQη
  let C := 1+∑T : Finset α,CT T
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset α)))=>(hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset α) : CT T≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun T _=>(hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨C,hC,(Filter.eventually_all.mpr hbase).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R F hR hF H hH hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd T hHR D hDF allocation
  have he := (hZ T).2 (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
    t V (fun i=>R₀ i.val) (fun i=>hw i.val) (fun i=>hwL i.val) (fun i=>hσ i.val)
    (fun i=>hσhi i.val) hV (fun i=>hfreq i.val) (fun i=>hR₀ i.val)
    Bstate s hQ hwidth R F hR hF H hH hcap hHR W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd D hDF allocation
  let p := independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)
  have hp : p.control (controlT T)≤p.control S := by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono (hS T)) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono (hS T)) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hh : (1+|t|+V)^(degreeT T)≤(1+|t|+V)^degree :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (hn T)
  have hdpos := pairNorm_pos hd.1 hd.2
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hFn : 0≤(F.absNorm:ℝ)^δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcoef := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCTC T) hFn) hdpos.le)
    (Nat.cast_nonneg (∏j,selectedDivisor D Finset.univ allocation j).absNorm :
      (0:ℝ)≤(∏j,selectedDivisor D Finset.univ allocation j).absNorm)
  have hcoef0 : 0≤C*(F.absNorm:ℝ)^δ/pairNorm d/
      ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ) :=
    div_nonneg (div_nonneg (mul_nonneg hC.le hFn) hdpos.le) (Nat.cast_nonneg _)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hcoef hdiag)
    (pow_le_pow_left₀ (p.control_nonneg (controlT T)) hp 2)
    (sq_nonneg _) (mul_nonneg hcoef0 hdiag)
  have htotal := mul_le_mul hm hh (by positivity : 0≤(1+|t|+V)^(degreeT T))
    (mul_nonneg (mul_nonneg hcoef0 hdiag) (sq_nonneg _))
  exact he.trans (mul_le_mul_of_nonneg_right htotal
    (Real.rpow_nonneg (zero_lt_one.trans (hZ T).1).le _))

end
end Candidate.Feedback.FourthPower.MixedUniformAllocated
