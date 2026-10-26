/- Copyright (c) 2026 Sil. Apache-2.0.
Apply the proved canonical forward estimate to the actual centered
punctured rows, preserving both exact shortened lengths and the full
paired divisor normalization. No physical child estimate is assumed.
-/
import Candidate.FourthPower.MixedCompletedRows
import Candidate.FourthPower.NativePuncturedForward

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedCenteredEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowPools KernelRowProfiles
open KernelRowExpansion KernelLabelledSlots KernelPunctureRows
open MixedTupleRows MixedCompletedRows RestorationFamily ReferencePrimeEnclosure
open NativeFiniteHoles NativeInjectiveEnergy NativeForwardEnergy NativePuncturedForward
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentCommonMaskEnergy CenteredMomentAddedZeroUniform
open MixedCommonCoefficient MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

def puncturedRow (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  weightedSum (naturalCoefficients χ S pool β P)
    (fun slot=>normalizedRow χ (supportedRectangle S b X₁ X₂)
      (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ X₁ X₂)

def centeredRow (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) : ℂ :=
  (Real.sqrt (pairNorm d):ℂ)⁻¹*
    (puncturedRow χ S H pool β P W₁ W₂ b (X₁/d.1.absNorm) (X₂/d.2.absNorm)-
      puncturedRow χ S H pool β P W₁ W₂ b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm))

theorem radial_centered (f g : O→ℂ) (c : ℂ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    radialEnergy (fun z=>c*(f z-g z)) keep Φ K≤
      2*‖c‖^2*(radialEnergy f keep Φ K+radialEnergy g keep Φ K) := by
  have hf := compact_radial_summable f keep Φ K radial hK hs
  have hg := compact_radial_summable g keep Φ K radial hK hs
  unfold radialEnergy
  calc
    _ ≤ ∑'z : O,2*‖c‖^2*((if keep z then ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)+
        (if keep z then ‖g z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)) := by
      apply (compact_radial_summable _ keep Φ K radial hK hs).tsum_le_tsum _ ((hf.add hg).mul_left _)
      intro z
      by_cases hz : keep z
      · simp only [hz,ite_true,norm_mul,mul_pow]
        have hn : ‖f z-g z‖^2≤2*‖f z‖^2+2*‖g z‖^2 := by
          nlinarith [norm_sub_le (f z) (g z),norm_nonneg (f z-g z),sq_nonneg (‖f z‖-‖g z‖)]
        have he := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn (sq_nonneg ‖c‖)) (hΦ z)
        convert he using 1
        ring
      · simp only [hz,ite_false,add_zero,mul_zero,le_refl]
    _ = _ := by rw [tsum_mul_left,hf.tsum_add hg]

theorem radial_extracted_centered (f g : O→ℂ) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial E : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hf : radialEnergy f keep Φ K≤E) (hg : radialEnergy g keep Φ K≤E) :
    radialEnergy (fun z=>(Real.sqrt (pairNorm d):ℂ)⁻¹*(f z-g z)) keep Φ K≤4*E/pairNorm d := by
  have he := radial_centered f g (Real.sqrt (pairNorm d):ℂ)⁻¹ keep Φ K radial hK hs hΦ
  rw [central_scalar_sq d hd] at he
  apply he.trans
  calc
    _ ≤ 2*(pairNorm d)⁻¹*(E+E) := mul_le_mul_of_nonneg_left (add_le_add hf hg)
      (mul_nonneg (by norm_num) (inv_nonneg.mpr (pairNorm_pos hd.1 hd.2).le))
    _ = _ := by ring

/-- The actual finite centered tuple is the canonical centered row. The
two domain inclusions are supplied by the inherited union of profile
support pools, including after exact ordinary extraction. -/
theorem centered_tuple_complete (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (A B : Finset Id) (β : α→Id→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1≠0 ∧ d.2≠0)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (hDX : rectangle b (X₁/d.1.absNorm) (X₂/d.2.absNorm)⊆A×ˢB)
    (hDY : rectangle b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)⊆A×ˢB)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0)
    (hS : ∀I,Supported I→
      (((I.absNorm:ℝ)≤b*(X₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(X₂/d.2.absNorm)) ∨
       ((I.absNorm:ℝ)≤b*(Y₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(Y₂/d.2.absNorm)))→
      primeSupport I⊆primeValues S) :
    (∑v∈Fintype.piFinset (pools (fun _ : α=>primeValues S) A B),
      tupleWeight (punctureProduct S H) v*centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d v*
        idealCoeff χ (finiteTupleProduct v))=
      centeredRow χ S H pool β P W₁ W₂ b X₁ X₂ Y₁ Y₂ d := by
  rw [centered_character_sum χ S H pool A B β P W₁ W₂ X₁ X₂ Y₁ Y₂ d
    (mul_pos hX₁ hX₂) hXY hd]
  unfold centeredRow puncturedRow
  apply congrArg (fun z : ℂ=>(Real.sqrt (pairNorm d):ℂ)⁻¹*z)
  apply congrArg₂ (fun x y : ℂ=>x-y)
  · apply congrArg (weightedSum (naturalCoefficients χ S pool β P))
    funext slot
    exact normalized_row_complete χ S (A×ˢB) _ W₁ W₂ b _ _
      (shortened_positive_le hX₁ hd.1).1 (shortened_positive_le hX₂ hd.2).1 hs₁ hs₂ hDX hoff
      (fun I hI hh=>hS I hI (Or.inl hh))
  · apply congrArg (weightedSum (naturalCoefficients χ S pool β P))
    funext slot
    exact normalized_row_complete χ S (A×ˢB) _ W₁ W₂ b _ _
      (shortened_positive_le hY₁ hd.1).1 (shortened_positive_le hY₂ hd.2).1 hs₁ hs₂ hDY hoff
      (fun I hI hh=>hS I hI (Or.inr hh))

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The constant and seminorms precede every scale, puncture and extracted
pair. Marked-only holes contain the ordinary puncture, so its absorption
is exact. The only analytic input used is the already proved canonical
punctured forward theorem, with its original zero-supremum hypotheses. -/
theorem canonical_centered
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,∀H : Finset PrimeIdeal,
      H⊆enclosure (Cap*Z^Lcap) → (∀i,∀P∈H,P.val∈R₀ i) →
      (Ideal.absNorm (∏I∈R∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L →
    ∀d : Id×Id,d.1≠0 → d.2≠0 →
      radialEnergy (fun z=>centeredRow ((naturalCharacter s.character z).excludePrimes R hR)
        (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
        (fun i=>heightCoefficient (holeCoefficient (fun i I=>
          idealCoeff (relativeCharacter M Hray hHray η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t)
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C/pairNorm d)*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,S,hbase⟩ := canonical_punctured_forward (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨4*C,by positivity,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R hR H hH hHR hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hd₁ hd₂ d hd1 hd2
  let primes := enclosure (Cap*Z^Lcap)
  let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
  let βc := fun i=>heightCoefficient (holeCoefficient (fun i I=>
    idealCoeff (relativeCharacter M Hray hHray η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t
  let E := C*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε)
  let T := R∪holes H
  have hT : ∀I∈T,Prime I := fun I hI=>(Finset.mem_union.mp hI).elim (hR I) (holes_prime H I)
  have hβH (i : α) (P : PrimeIdeal) (hP : P∈H) : βc i P.val=0 := by
    simp only [βc,heightCoefficient,holeCoefficient,ite_eq_left (hHR i P hP),zero_mul]
  have hid (A B : ℝ) (z : O) :
      puncturedRow ((naturalCharacter s.character z).excludePrimes R hR) primes H pool βc
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b A B=
      row false primes ((naturalCharacter s.character z).excludePrimes T hT) pool βc
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b A B := by
    rw [puncturedRow,family_hole_absorption _ primes H hH pool βc _ hβH]
    exact row_character_congr _ _ (character_union _ R (holes H) hR (holes_prime H)) _ _ _ _ _ _ _ _ _
  have hbnd (A B : ℝ) (hA : 0<A) (hB : 0<B) (hcA : A≤Z^L) (hcB : B≤Z^L) :
      radialEnergy (fun z=>puncturedRow ((naturalCharacter s.character z).excludePrimes R hR)
        primes H pool βc (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b
        (A/d.1.absNorm) (B/d.2.absNorm))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤E := by
    simp_rw [hid]
    exact hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth T hT hcap
      W₁ W₂ hs₁ hs₂ t₁ t₂ (A/d.1.absNorm) (B/d.2.absNorm)
      (shortened_positive_le hA hd1).1 (shortened_positive_le hB hd2).1
      ((shortened_positive_le hA hd1).2.trans hcA) ((shortened_positive_le hB hd2).2.trans hcB)
  have he := radial_extracted_centered _ _ d ⟨hd1,hd2⟩ (effectiveState s).radial.keep
    s.radial.profile s.radial.scale radial E s.radial.scale_pos s.radial_support s.radial.nonneg
    (hbnd X₁ X₂ hX₁ hX₂ hc₁ hc₂) (hbnd Y₁ Y₂ hY₁ hY₂ hd₁ hd₂)
  apply he.trans_eq
  dsimp only [E]
  ring

end
end Candidate.FourthPower.MixedCenteredEnergy
