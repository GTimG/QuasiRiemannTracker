/- Copyright (c) 2026 Sil. Apache-2.0.
Apply the canonical centered estimate to the literal finite source
coefficient, with original annular windows, heights and punctures.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedLiveNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedCanonicalSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open IdealMobiusDivisorSum (support_prime)
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowPools KernelRowProfiles
open MixedCommonCoefficient MixedCommonRestriction MixedTupleRows MixedCompletedRows
open MixedLiveRows MixedLiveNormalization MixedCenteredEnergy ReferencePrimeEnclosure
open NativeFiniteHoles NativeInjectiveEnergy NativeForwardEnergy NativePuncturedInjective
open CenteredMomentCommonMaskEnergy CenteredMomentAddedZeroUniform
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

def slotProfile (W : ℝ→ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-shift σ freq)

def slotCoefficient (ν : α→Character) (R₀ : α→Finset Id) (t : ℝ) (i : α) : Id→ℂ :=
  heightCoefficient (holeCoefficient (fun i I=>idealCoeff (ν i) I) R₀ i) t

omit [Fintype α] in
theorem slot_coefficient_identity (ν : α→Character) (R₀ : α→Finset Id)
    (W : ℝ→ℂ) (P σ freq : α→ℝ) (t : ℝ) (i : α) (I : Id) :
    slotCoefficient ν R₀ t i I*slotProfile W (σ i) (freq i) (I.absNorm/P i)=
      heightCoefficient (holeCoefficient (fun i I=>idealCoeff (ν i) I*
        HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I) R₀ i) t I := by
  by_cases h : I∈R₀ i
  · simp only [slotCoefficient,heightCoefficient,holeCoefficient,h,ite_true,zero_mul]
  · simp only [slotCoefficient,slotProfile,heightCoefficient,holeCoefficient,h,ite_false,
      HeckePrimeAnnular.annularWeight]
    ring

def source (χ : Character) (S H : Finset PrimeIdeal) (R : Id)
    (pool : α→Finset Id) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) : ℂ :=
  ∑v∈Fintype.piFinset (pools pool
      (plainSupportPool b (X₁/d.1.absNorm) (Y₁/d.1.absNorm))
      (plainSupportPool b (X₂/d.2.absNorm) (Y₂/d.2.absNorm))),
    tupleWeight (punctureProduct S H) v*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
      idealCoeff χ (finiteTupleProduct v)

theorem source_centered (χ : Character) (S H : Finset PrimeIdeal) (R : Id) (hR : R≠0)
    (pool : α→Finset Id) (hp : ∀i,pool i⊆primeValues S)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1≠0 ∧ d.2≠0)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0)
    (hS : ∀I,Supported I→
      (((I.absNorm:ℝ)≤b*(X₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(X₂/d.2.absNorm)) ∨
       ((I.absNorm:ℝ)≤b*(Y₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(Y₂/d.2.absNorm)))→
      primeSupport I⊆primeValues S) :
    normalization (X₁*X₂) P*source χ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ d=
      centeredRow (χ.excludePrimes (primeSupport R) (fun _ h=>support_prime h)) S H pool
        (fun i I=>ν i I*Wslot i (I.absNorm/P i)) P W₁ W₂ b X₁ X₂ Y₁ Y₂ d := by
  unfold normalization source
  rw [punctured_pool_profile χ S H R hR pool hp _ _ ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d]
  have hc := source_pool_rectangles d hd b X₁ X₂ Y₁ Y₂
  dsimp only at hc
  rw [residual_plain_pool,residual_plain_pool] at hc
  apply centered_tuple_complete _ S H _ _ _ _ _ W₁ W₂ b X₁ X₂ Y₁ Y₂ d
    hX₁ hX₂ hY₁ hY₂ hXY hd hs₁ hs₂ hc.1 hc.2 _ hS
  exact deleted_off_supported χ hoff _ _

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The original finite source has the analytic centered bound. All
support and character-zero conditions are supplied here, including the
fact that zero is excluded only on the actual retained radial rows. -/
theorem canonical_source
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R : Id,R≠0 → ∀H : Finset PrimeIdeal,
      H⊆enclosure (Cap*Z^Lcap) → (∀i,∀P∈H,P.val∈R₀ i) →
      (Ideal.absNorm (∏I∈primeSupport R∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,d.1≠0 → d.2≠0 →
      radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
        source (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H R
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C/pairNorm d)*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,S,hbase⟩ := canonical_centered (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR H hH hHR hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd₁ hd₂
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    (primeSupport R) (fun _ h=>support_prime h) H hH hHR hcap W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ d hd₁ hd₂
  have hp (i : α) : supportedPool (primePool M Hray 2 (Z^(w i)))⊆primeValues (enclosure (Cap*Z^Lcap)) := by
    rw [enclosure_values]
    exact canonical_pool_enclosed M Hray Z (w i) Lcap Cap hZ.1.le ((hwL i).trans hLcap) hCap
  have hbound (x : ℝ) (hx : 0<x) (hc : x≤Z^L) (D : Id) (hD : D≠0) :
      b*(x/D.absNorm)≤Cap*Z^Lcap :=
    mul_le_mul hCapb (((shortened_positive_le hx hD).2.trans hc).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hLordinary))
      (shortened_positive_le hx hD).1.le (by linarith)
  have hcover (I : Id) (hI : Supported I)
      (hh : (((I.absNorm:ℝ)≤b*(X₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(X₂/d.2.absNorm)) ∨
       ((I.absNorm:ℝ)≤b*(Y₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(Y₂/d.2.absNorm)))) :
      primeSupport I⊆primeValues (enclosure (Cap*Z^Lcap)) := by
    apply support_enclosed _ I hI
    rcases hh with (hh|hh)|(hh|hh)
    · exact hh.trans (hbound X₁ hX₁ hc₁ _ hd₁)
    · exact hh.trans (hbound X₂ hX₂ hc₂ _ hd₂)
    · exact hh.trans (hbound Y₁ hY₁ hc₃ _ hd₁)
    · exact hh.trans (hbound Y₂ hY₂ hc₄ _ hd₂)
  have hid (z : O) (hz : (effectiveState s).radial.keep z) :=
    source_centered (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H R hR _ hp
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d
      hX₁ hX₂ hY₁ hY₂ hXY ⟨hd₁,hd₂⟩
      ((phaseProfile_support W₁ t₁).trans (fun x hx=>(hs₁ hx).2))
      ((phaseProfile_support W₂ t₂).trans (fun x hx=>(hs₂ hx).2))
      (natural_character_off_supported s.character z (s.row_ne_zero z hz.1)) hcover
  apply le_of_eq_of_le ?_ he
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : (effectiveState s).radial.keep z
  · simp only [hz,ite_true,hid z hz,
      slot_coefficient_identity (fun i=>relativeCharacter M Hray hHray η₀ (θ i))
        R₀ W (fun i=>Z^(w i)) σ freq t]
  · simp only [hz,ite_false]

end
end Candidate.FourthPower.MixedCanonicalSource
