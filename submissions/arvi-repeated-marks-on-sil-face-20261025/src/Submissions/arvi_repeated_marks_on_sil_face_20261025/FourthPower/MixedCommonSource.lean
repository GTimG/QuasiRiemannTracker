/- Copyright (c) 2026 Sil. Apache-2.0.
Sum the genuine common allocations after restoring the literal squarefree
divisibility mask. The restricted coefficients and frozen fifth-free and
injectivity gates remain present. Both divisor norms survive the sum.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedCommonMasked

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedCommonSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedCommonMasked MixedDivisorMask MixedLiveNormalization MixedSourceAssembly
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

/-- The whole genuinely extracted source, with the original divisor mask
in each live row and the exact frozen restriction outside that row. -/
def commonMaskedRow (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R D : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑B : actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G,
    frozenWeight (punctureProduct S H) B.val*
      (normalization (X₁*X₂) P*(frozenCoefficient B.val G R ν Wslot P*
        maskedLiveSum χ S H pool d hd B.val
          (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 G R D
          ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂))

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Uniform complete genuine-allocation source bound. The constant
precedes every original profile parameter, divisor, and allocation.
There is no analytic child-energy premise. -/
theorem uniform_common_source
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
    ∀R G D : Id,R≠0 → G≠0 → Squarefree D → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
      radialEnergy (fun z=>commonMaskedRow (naturalCharacter s.character z)
        (enclosure (Cap*Z^Lcap)) H (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
        d hd G R D
        (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,S,hbase⟩ := uniform_common_masked_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hδ hβ hκ Q hQt hQ72 hQM
  obtain ⟨Ccount,hCcount,hcount⟩ := genuine_count_squared (Fintype.card α+2) δ hδ
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C*Ccount,mul_pos hC hCcount,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R G D hR hG hD H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  let T := sourcePools (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd b X₁ X₂ Y₁ Y₂
  let f := fun (B : actualAllocations T G)(z : O)=>
    normalization (X₁*X₂) P*(frozenCoefficient B.val G R ν Wslot P*
      maskedLiveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B.val
        (allocation_data T G B.val (Finset.mem_filter.mp B.property).1).1 G R D ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
  let phase := fun (B : actualAllocations T G)(_ : O)=>
    frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val
  let A := (C*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
    diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree
  let E := A*Z^(s.width+κ*(∑i,w i)+ε)
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hGpos : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hDpos : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hA : 0≤A := by
    have := diagonalControl_nonneg s.radial.profile
    have := pairNorm_pos hd.1 hd.2
    dsimp only [A]
    positivity
  have hE : 0≤E := mul_nonneg hA (Real.rpow_nonneg hZ0.le _)
  have hκ0 : 0≤κ := by linarith
  have hf (B : actualAllocations T G) :
      radialEnergy (f B) (effectiveState s).radial.keep s.radial.profile s.radial.scale≤E := by
    have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
      R G D hR hG hD H hH hcap W₁ W₂ hs₁ hs₂
      t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B.val
      (allocation_data T G B.val (Finset.mem_filter.mp B.property).1).1
      (Finset.mem_filter.mp B.property).2 (fun i=>hHR i.val)
    have hsum : (∑i : liveIndices B.val,w i.val)≤∑i,w i := by
      simpa only [Finset.sum_coe_sort] using Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (liveIndices B.val)) (fun i _ _=>hw i)
    apply he.trans
    change A*Z^(s.width+κ*(∑i : liveIndices B.val,w i.val)+ε)≤E
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.rpow_le_rpow_of_exponent_le hZ.1.le
    linarith [mul_le_mul_of_nonneg_left hsum hκ0]
  have hphase : ∀B z,(effectiveState s).radial.keep z→‖phase B z‖≤1 := by
    intro B z hz
    dsimp only [phase]
    unfold frozenWeight
    split_ifs <;> norm_num
  have hs := radial_phase_sum phase f E (effectiveState s).radial.keep s.radial.profile
    s.radial.scale radial s.radial.scale_pos s.radial_support s.radial.nonneg hphase hf
  change radialEnergy (fun z=>∑B : actualAllocations T G,phase B z*f B z)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale≤_
  apply hs.trans
  rw [Fintype.card_coe]
  have hdim : Fintype.card (α⊕Fin 2)≤Fintype.card α+2 := by
    simp only [Fintype.card_sum,Fintype.card_fin,le_refl]
  apply (mul_le_mul_of_nonneg_right (hcount hdim T G hG) hE).trans_eq
  dsimp only [E,A]
  ring

end
end Candidate.FourthPower.MixedCommonSource
