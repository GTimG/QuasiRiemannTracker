/- Copyright (c) 2026 Sil. Apache-2.0.
The literal artificially allocated source has its analytic bound,
including the fixed-support subpower, selected-product denominator,
original ordinary divisor pair and only the unforced marked weights.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedLiteralAllocation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedAllocatedEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedAllocationSource MixedLiteralAllocation MixedAllocationCost MixedSourceAssembly
open MixedCommonCoefficient MixedCommonRestriction NativeInjectiveEnergy NativeFiniteHoles MixedFixedSupport
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem uniform_allocated_energy
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
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀D : Id,D∣F →
    ∀allocation : Allocation D (Finset.univ : Finset (α⊕Fin 2)),
      radialEnergy (fun z=>allocatedRow (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd D R allocation
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(F.absNorm:ℝ)^δ/pairNorm d/
        ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i : selectedLive D allocation,w i.val)+ε) := by
  obtain ⟨degree,S,hbase⟩ := uniform_frozen_sum (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM
  obtain ⟨Ccount,hCcount,hcount⟩ := uniform_selected_budget (α:=α) δ hδ
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C*Ccount,mul_pos hC hCcount,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R F hR hF H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd D hDF allocation
  let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
  let T := sourcePools pool d hd b X₁ X₂ Y₁ Y₂
  let labels := boundedLabels T F
  let active := fun B : labels=>allocationTerm D Finset.univ B.val allocation≠0
  let phase := fun (B : labels)(z : O)=>frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val*
    allocationTerm D Finset.univ B.val allocation*
    idealCoeff (naturalCharacter s.character z) (finiteTupleProduct B.val)
  have hp (i : α) (I : Id) (hI : I∈pool i) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  have hlabels (B : labels) : ∀j,B.val j≠0 :=
    (allocation_data T F B.val (Finset.mem_filter.mp B.property).1).1
  have hphase (B : labels) (z : O) : ‖phase B z‖≤1 := by
    have hwB : ‖frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val‖≤1 := by
      unfold frozenWeight
      split_ifs <;> norm_num
    have ht := allocation_term_norm D Finset.univ B.val allocation
    dsimp only [phase]
    rw [norm_mul,norm_mul]
    have hpB : ‖frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val‖*
        ‖allocationTerm D Finset.univ B.val allocation‖≤1 :=
      (mul_le_mul hwB ht (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    exact (mul_le_mul hpB (idealCoeff_norm_le_one _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R F hR hF H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd labels hlabels active phase
    (fun B z _=>hphase B z)
    (fun B hn z=>actual_phase_zero _ D allocation B.val (not_not.mp hn) (naturalCharacter s.character z))
    (fun B _ i P hP=>hHR i.val P hP)
  have hrow (z : O) := allocated_row_identity (naturalCharacter s.character z)
    (enclosure (Cap*Z^Lcap)) H pool hp d hd D F R hF hDF allocation
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
  rw [funext hrow]
  apply he.trans
  have hκ0 : 0≤κ := by linarith
  have hb := hcount T F hF D allocation Z κ w hZ.1.le hκ0 hw
  let A := (C/pairNorm d)*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+ε)
  have hA : 0≤A := by
    have := diagonalControl_nonneg s.radial.profile
    have := pairNorm_pos hd.1 hd.2
    have := zero_lt_one.trans hZ.1
    dsimp only [A]
    positivity
  apply (mul_le_mul_of_nonneg_left hb hA).trans_eq
  rw [show s.width+κ*(∑i : selectedLive D allocation,w i.val)+ε=
      s.width+ε+κ*(∑i : selectedLive D allocation,w i.val) by ring,
    Real.rpow_add (zero_lt_one.trans hZ.1)]
  dsimp only [A]
  ring

end
end Candidate.FourthPower.MixedAllocatedEnergy
