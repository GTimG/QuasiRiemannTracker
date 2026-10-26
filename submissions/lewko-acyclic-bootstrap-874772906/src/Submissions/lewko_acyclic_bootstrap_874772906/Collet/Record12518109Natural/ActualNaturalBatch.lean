/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Adapted from PR63 NaturalSlotAnchor, WholeFamilyAnchor and WholeNaturalBatch
at tracker 9c0e14f985041e397f71c574028193ee595a0f98. NaturalBatch is the checked
Record12518109Gain interface; the actual common amplitudes and fixed mask are
unchanged. Underlying OpenAI/math interfaces: Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualWeighted
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.WholeSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion


set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentExceptionalPair
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Moving a fixed dictionary twist from the row character to the relative
anchor preserves every prime coefficient after deleting its fixed conductor. -/
theorem shifted_anchor_coefficient (η η₀ ν : Character) (u : O)
    (F : NaturalRow η u) (G : NaturalRow (η.product ν) u)
    (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff G.character I*idealCoeff (relativeCharacter M H hH (η₀.product ν) θ) I=
      idealCoeff (excluded F.character ν.modulus) I*
        idealCoeff (relativeCharacter M H hH η₀ θ) I := by
  rw [G.ideal,excluded_ideal _ _ ν.modulus_ne_bot,F.ideal]
  by_cases hI : I=0
  · subst I
    simp only [show (⊥ : Ideal O)=0 from rfl,map_zero,zero_mul,ite_self]
  by_cases hc : IsCoprime I ν.modulus
  · rw [if_pos hc]
    have hn := HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime ν I hI hc
    simp only [relativeCharacter_ideal,idealCoeff_product,
      HeckeDetectorRelativePrime.idealCoeff_inverse,mul_inv_rev]
    field_simp
  · rw [if_neg hc,zero_mul]
    have hn : idealCoeff ν I=0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff ν I).mp hn).2
    simp only [idealCoeff_product,hn,mul_zero,zero_mul]

/-- Exact natural-slot form of the fixed-anchor transfer; it is uniform over
all pools, profiles and frequencies. -/
theorem shifted_anchor_slot (η η₀ ν : Character) (u : O)
    (F : NaturalRow η u) (G : NaturalRow (η.product ν) u)
    (θ : RayQuotient.Characters M H) (pool : Finset (Ideal O))
    (weight : Ideal O→ℂ) (P : ℝ) :
    naturalSlot G.character pool
      (fun I=>idealCoeff (relativeCharacter M H hH (η₀.product ν) θ) I*weight I) P=
    naturalSlot (excluded F.character ν.modulus) pool
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*weight I) P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simpa only [←mul_assoc] using congrArg (fun c : ℂ=>c*weight I)
    (shifted_anchor_coefficient M H hH η η₀ ν u F G θ I)

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.shifted_anchor_slot


set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion Cycle61Moment
local notation "O" => HeckeFamily.O

/-- A fixed ideal records primes at which every row coefficient vanishes. -/
def Avoids (χ : Character) (R : Ideal O) : Prop :=
  ∀ I : Ideal O, ¬IsCoprime I R → idealCoeff χ I=0

theorem excluded_avoids (η : Character) (R : Ideal O) (hR : R≠0) :
    Avoids (excluded η R) R := by
  intro I hI
  rw [excluded_ideal _ _ hR,if_neg hI]

theorem avoids_product {η : Character} {R : Ideal O} (hη : Avoids η R) (ν : Character) :
    Avoids (η.product ν) R := by
  intro I hI
  rw [idealCoeff_product,hη I hI,zero_mul]

theorem avoids_natural {η : Character} {R : Ideal O} (hη : Avoids η R)
    {u : O} (F : NaturalRow η u) : Avoids F.character R := by
  intro I hI
  rw [F.ideal,hη I hI,zero_mul]

theorem avoids_excluded_redundant {χ : Character} {R : Ideal O} (hχ : Avoids χ R)
    (S : Ideal O) (hS : S≠0) (hSR : S∣R) (I : Ideal O) :
    idealCoeff (excluded χ S) I=idealCoeff χ I := by
  rw [excluded_ideal _ _ hS]
  by_cases hc : IsCoprime I S
  · exact if_pos hc
  · rw [if_neg hc]
    exact (hχ I (fun h=>hc (h.of_isCoprime_of_dvd_right hSR))).symm

theorem avoids_slot_excluded_redundant {χ : Character} {R : Ideal O} (hχ : Avoids χ R)
    (S : Ideal O) (hS : S≠0) (hSR : S∣R)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (excluded χ S) pool β P=naturalSlot χ pool β P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [avoids_excluded_redundant hχ S hS hSR]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

abbrev RayPair := RayQuotient.Characters M H × RayQuotient.Characters M H

def firstTwist (η₀ : Character) (j : RayPair M H) : Character :=
  (relativeCharacter M H hH η₀ j.1).inverse.inverse

def secondTwist (j : RayPair M H) : Character := HeckeRayQuotient.character M H hH j.2

/-- This ideal is fixed before the scale and the chosen zero label. -/
def wholeAnchorMask (η₀ : Character) : Ideal O :=
  ∏j : RayPair M H,(firstTwist M H hH η₀ j).modulus*(secondTwist M H hH j).modulus

theorem wholeAnchorMask_ne_zero (η₀ : Character) : wholeAnchorMask M H hH η₀≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact mul_ne_zero (firstTwist M H hH η₀ j).modulus_ne_bot (secondTwist M H hH j).modulus_ne_bot

theorem firstTwist_divides_mask (η₀ : Character) (j : RayPair M H) :
    (firstTwist M H hH η₀ j).modulus∣wholeAnchorMask M H hH η₀ :=
  (dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

theorem secondTwist_divides_mask (η₀ : Character) (j : RayPair M H) :
    (secondTwist M H hH j).modulus∣wholeAnchorMask M H hH η₀ :=
  (dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

def wholeSourceAnchor (η₀ : Character) : WholeSourceIndex M H→Character :=
  Sum.elim (fun _=>η₀) (fun j=>(η₀.product (firstTwist M H hH η₀ j)).product (secondTwist M H hH j))

/-- Every member of the actual whole zero family uses the same marked slot
amplitude. The fixed anchor changes with its zero label, while its common
slot base has one fixed conductor deletion. -/
theorem whole_family_common_slot (η η₀ : Character) (u : O) (hu : u≠0)
    (j : WholeSourceIndex M H) (θ : RayQuotient.Characters M H)
    (pool : Finset (Ideal O)) (weight : Ideal O→ℂ) (P : ℝ) :
    let base := excluded η (wholeAnchorMask M H hH η₀)
    naturalSlot (naturalRow (wholeSourceBase M H hH η₀ base j) u hu).character pool
      (fun I=>idealCoeff (relativeCharacter M H hH (wholeSourceAnchor M H hH η₀ j) θ) I*weight I) P=
    naturalSlot (naturalRow base u hu).character pool
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*weight I) P := by
  intro base
  have hb : Avoids base (wholeAnchorMask M H hH η₀) :=
    excluded_avoids η _ (wholeAnchorMask_ne_zero M H hH η₀)
  cases j with
  | inl j => rfl
  | inr j =>
    let ν₁ := firstTwist M H hH η₀ j
    let ν₂ := secondTwist M H hH j
    let F := naturalRow base u hu
    let G := naturalRow (base.product ν₁) u hu
    let K := naturalRow ((base.product ν₁).product ν₂) u hu
    change naturalSlot K.character pool
      (fun I=>idealCoeff (relativeCharacter M H hH ((η₀.product ν₁).product ν₂) θ) I*weight I) P=_
    rw [shifted_anchor_slot M H hH (base.product ν₁) (η₀.product ν₁) ν₂ u G K θ]
    rw [avoids_slot_excluded_redundant (avoids_natural (avoids_product hb ν₁) G)
      ν₂.modulus ν₂.modulus_ne_bot (secondTwist_divides_mask M H hH η₀ j)]
    rw [shifted_anchor_slot M H hH base η₀ ν₁ u F G θ]
    exact avoids_slot_excluded_redundant (avoids_natural hb F)
      ν₁.modulus ν₁.modulus_ne_bot (firstTwist_divides_mask M H hH η₀ j) _ _ _

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.whole_family_common_slot


set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open Cycle61MarkedPlain
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState Cycle61Moment
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def cleanWholeBase (η η₀ : Character) : WholeSourceIndex M H→Character :=
  wholeSourceBase M H hH η₀ (excluded η (wholeAnchorMask M H hH η₀))

theorem natural_initial_element (η : Character) (u : O) (hu : u≠0) (n : O) :
    elementCoeff (naturalRow η u hu).character n=
      CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (1*u) n := by
  have hh:=(naturalRow η u hu).masked_element 1 one_ne_zero n
  rw [excluded_element _ (naturalRow η u hu).element_zero 1 one_ne_zero,
    if_pos (isCoprime_one_right)] at hh
  simpa only [one_mul] using hh

/-- The actual common relative-ray amplitudes give the literal source batch
for every member of the whole zero family. The fixed conductor mask is
independent of the moving rows and of their selected zero labels. -/
def wholeNaturalBatch {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (W : ℝ→ℂ) (lo hi U : ℝ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (rows : Finset FreeRow) (slots : Finset Slot) (w σ v : Slot→ℝ)
    (t : FreeRow→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (hw : ∀s∈slots,0<w s) (hσlo : ∀s∈slots,lo≤σ s) (hσhi : ∀s∈slots,σ s≤hi)
    (hrow : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U)
    (hnorm : ∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤U)
    (hkeep : ∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
      (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val)
    (hlarge : ∀s∈slots,∀j,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)<U^(w s)) :
    Record12518109GainActual.NaturalBatch (Slot:=Slot) M H hH (cleanWholeBase M H hH η η₀)
      (wholeSourceAnchor M H hH η₀) bad W lo hi U where
  rows:=rows
  family:=fun u j=>(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character
  slots:=slots
  widths:=w
  sigma:=σ
  relativeHeight:=v
  commonHeight:=t
  Q:=fun u s=>naturalSlot
    (naturalRow (excluded η (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
      (primePool M H 2 (U^(w s)))
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))
  rays:=fun _=>θ
  inversePools:=fun s=>annularPool (primePool M H 2 (U^(w s))) (U^(w s))
  inverseBase:=excluded η (wholeAnchorMask M H hH η₀)
  inverseCoefficients:=fun s=>relativeCharacter M H hH η₀ (θ s)
  widthsPositive:=hw
  sigmaLower:=hσlo
  sigmaUpper:=hσhi
  rowNorm:=hrow
  embeddingNorm:=hnorm
  idealCoefficients:=by
    intro u hu j I
    exact natural_raw_coefficients _ (momentElement u) I
  elementCoefficients:=by
    intro u hu j n
    exact natural_initial_element _ u.val u.property.1 n
  retained:=hkeep
  inversePrime:=by
    intro s hs I hI
    exact (Finset.mem_filter.mp (annularPool_subset _ _ hI)).2.1
  inverseRatios:=fun s hs I hI=>annularPool_ratio _ _ _ hI
  inverseLarge:=hlarge
  inverseIdentity:=by
    intro u hu s hs
    exact (naturalSlot_annular_filter _ _ _ W hWs _ _ _).symm
  plainIdentity:=by
    intro u hu j s hs
    exact (whole_family_common_slot M H hH η η₀ u.val u.property.1 j (θ s)
      (primePool M H 2 (U^(w s)))
      (fun I=>HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))).symm

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.wholeNaturalBatch


namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CanonicalRowCompletion
open HeckeDetectorSupportedWitness HeckeDetectorClassBudget
open DetectorDictionaryInverseRawInitialGates
open Record12518109GainActual Record12518109GainAssembly
open HeckeDetectorDyadicProfiles HeckeDetectorFiberPartition HeckeDetectorWitnessRows
open ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open ConcreteTraceCRT Cycle61Moment
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Apply the checked homogeneous supplier to the actual complete relative-ray
family. The amplitudes use one common fixed conductor deletion; no moment
fields are requested from the caller. -/
theorem actual_whole_weighted_row_sum_uniform
    (ηchar η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ εm binWidth ζ η : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hζ : 0<ζ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      ∀hw : (∀s∈slots,0<w s), ∀hσlo : (∀s∈slots,lo≤σ s), ∀hσhi : (∀s∈slots,σ s≤hi),
      ∀hrow : (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U),
      ∀hnorm : (∀u∈rows,‖eisEmbedding u.val‖^2≤U),
      ∀hkeep : (∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH ηchar η₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val),
      ∀hlarge : (∀s∈slots,∀j,
        ((deletedBase (momentData (cleanWholeBase M H hH ηchar η₀ j))).modulus.absNorm:ℝ)<U^(w s)),
      let B := wholeNaturalBatch M H hH ηchar η₀ bad W lo hi U hWs rows slots w σ v t θ
        hw hσlo hσhi hrow hnorm hkeep hlarge;
      ∀a ε T allowance mesh height : ℝ,∀i : ℕ,
      31/50≤2*a-1 → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      0≤ mesh → mesh≤Cycle61MarkedPlain.markedPlainMesh (3/4) εm → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0≤(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (B.family u) U a ε (binCutoff B.slots B.widths a binWidth bin) T allowance i,
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤(U^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        U^(Record12518109Gain.rho (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          Record12518109Gain.gain (2*a-1) (∑s∈B.slots,B.widths s) 1+
          155*ε+mesh+εm+(2*a-1)*ζ+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨J,C,hC,hfield⟩ := Record12518109GainActual.actual_weighted_row_sum_uniform_fixedmesh
    (Slot:=Slot) M H hH (cleanWholeBase M H hH ηchar η₀) (wholeSourceAnchor M H hH η₀) bad
    hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ εm binWidth ζ η
    hWs hW hbΦ hrad hbin hη hζ hεm hβ hκβ
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro rows slots w σ v t θ hw hσlo hσhi hrow hnorm hkeep hlarge
  exact hU.2 (wholeNaturalBatch M H hH ηchar η₀ bad W lo hi U hWs rows slots w σ v t θ
    hw hσlo hσhi hrow hnorm hkeep hlarge)
end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_whole_weighted_row_sum_uniform
