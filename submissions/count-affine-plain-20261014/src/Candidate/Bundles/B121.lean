/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B103
import Candidate.Bundles.B115
import Candidate.Bundles.B116
import Candidate.Bundles.B120

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.FirstDictionaryIdentity; sha256 ba8a0b26b055caf071731107f431fda361aaa0b7363dc94d3804e5bbf6487ab2 -/
section
                                                          
                                                      
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Choose the signed unit once per arithmetic label, before the first
projector, dyads or ray characters. Unsupported labels use the identity. -/
def firstDictionaryUnit (left : Bool)(η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel) : Oˣ :=
  if h : Supported l.1.1 then
    if left then Classical.choose (uniform_first_left_natural_parent_mask η u₀ F₀ R fixedBadMask
      l.1.1 l.1.2 h l.2.val)
    else Classical.choose (uniform_first_right_natural_parent_mask η u₀ F₀ R fixedBadMask
      l.1.1 l.1.2 h l.2.val)
  else 1

/-- Every actual left member of the fixed pair uses the same preselected
arithmetic-label unit, across all first ray choices. -/
theorem actual_fixed_pair_left_dictionary (η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel)(hC : Supported l.1.1)
    (ξ₁ ξ₂ : RayCharacter)(F : FixedPair (excluded F₀.character R) l.1.1 l.1.2 hC l.2.val ξ₁ ξ₂)
    (G : NaturalRow (childCharacter η (firstPhaseCharacter l.1.1 l.1.2 hC
      (activeExponent l.1.1 l.1.2)*ξ₁))
      (u₀*(firstDictionaryUnit true η u₀ F₀ R l:O)*
        primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val*
        firstSourceNumerator true l)) (I : Ideal O) :
    idealCoeff F.left I=if IsCoprime I F.left.modulus then idealCoeff G.character I else 0 := by
  have hu := Classical.choose_spec (uniform_first_left_natural_parent_mask η u₀ F₀ R fixedBadMask
    l.1.1 l.1.2 hC l.2.val)
  revert G
  unfold firstDictionaryUnit
  rw [dif_pos hC]
  simp only [↓reduceIte,firstSourceNumerator]
  intro G
  exact hu ξ₁ F.left F.left_modulus (fixed_pair_left_element F) G I

/-- The corresponding right identity retains the actual right ray and
signed numerator with a unit fixed before both ray choices. -/
theorem actual_fixed_pair_right_dictionary (η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel)(hC : Supported l.1.1)
    (ξ₁ ξ₂ : RayCharacter)(F : FixedPair (excluded F₀.character R) l.1.1 l.1.2 hC l.2.val ξ₁ ξ₂)
    (G : NaturalRow (childCharacter η (firstPhaseCharacter l.1.1 l.1.2 hC
      (fun p=>6-activeExponent l.1.1 l.1.2 p)*ξ₂))
      (u₀*(firstDictionaryUnit false η u₀ F₀ R l:O)*
        primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val*
        firstSourceNumerator false l)) (I : Ideal O) :
    idealCoeff F.right I=if IsCoprime I F.right.modulus then idealCoeff G.character I else 0 := by
  have hu := Classical.choose_spec (uniform_first_right_natural_parent_mask η u₀ F₀ R fixedBadMask
    l.1.1 l.1.2 hC l.2.val)
  revert G
  unfold firstDictionaryUnit
  rw [dif_pos hC]
  simp only [↓reduceIte,firstSourceNumerator]
  intro G
  exact hu ξ₂ F.right F.right_modulus (fixed_pair_right_element F) G I

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_fixed_pair_left_dictionary
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_fixed_pair_right_dictionary

end
/- END ORIGINAL Cycle61.Physical.InitialMass.FirstDictionaryIdentity -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryDictionary; sha256 8a4133c46bd253f0fc4821adf6e2e3ece5abb9e773fcdaea2de17096d34f03bc -/
section
                                                           

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The signed phase and the actual ray of a selected first column. -/
def geometryDictionaryRay {ι : Type*} [Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : RayCharacter :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  if reflected then firstPhaseCharacter src.C src.D src.hC
    (fun p=>6-activeExponent src.C src.D p)*j.2.2.2⁻¹
  else firstPhaseCharacter src.C src.D src.hC (activeExponent src.C src.D)*j.2.2.1

/-- Exact dictionary identity for the physical column character, with the
unit indexed only by its arithmetic label. The original excluded-parent
identity is retained explicitly. -/
theorem actual_geometry_column_dictionary {ι : Type*} [Fintype ι]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK key j))
      (u₀*(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀
        (geometryFirstLabel s R seed K Z ξ hK key j):O)*
        primeSubsetGenerator (fun p : CommonIndex
          (geometryFirstLabel s R seed K Z ξ hK key j).1.1
          (geometryFirstLabel s R seed K Z ξ hK key j).1.2=>p.val)
          (geometryFirstLabel s R seed K Z ξ hK key j).2.val*
        firstSourceNumerator (!reflected) (geometryFirstLabel s R seed K Z ξ hK key j)))
    (I : Ideal O) :
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK key j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  let l := geometryFirstLabel s R seed K Z ξ hK key j
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  cases reflected
  · have hu := Classical.choose_spec (uniform_first_left_natural_parent_mask η₀ u₀ F₀ R₀
      fixedBadMask src.C src.D src.hC src.inactive)
    have hm := F.left_modulus
    have hm' : F.left.modulus = (excluded F₀.character R₀).modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*activeConductor src.C src.D} := by simpa only [hη] using hm
    have he := fixed_pair_left_element F
    simp only [hη] at he
    change idealCoeff F.left I=if IsCoprime I F.left.modulus then idealCoeff G.character I else 0
    revert G
    unfold firstDictionaryUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1 := src.hC
    rw [dif_pos hc]
    intro G
    exact hu j.2.2.1 F.left hm' he G I
  · have hu := Classical.choose_spec (uniform_first_right_natural_parent_mask η₀ u₀ F₀ R₀
      fixedBadMask src.C src.D src.hC src.inactive)
    have hm := F.right_modulus
    have hm' : F.right.modulus = (excluded F₀.character R₀).modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*activeConductor src.C src.D} := by simpa only [hη] using hm
    have he := fixed_pair_right_element F
    simp only [hη] at he
    change idealCoeff F.right I=if IsCoprime I F.right.modulus then idealCoeff G.character I else 0
    revert G
    unfold firstDictionaryUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1 := src.hC
    rw [dif_pos hc]
    intro G
    exact hu j.2.2.2⁻¹ F.right hm' he G I

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_column_dictionary

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryDictionary -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondDictionary; sha256 4f02ddfa2011f6e76e33d3e9c242f74838acf6b6ceca680a18877e9b4a72bc9c -/
section
                                                       
                                    
                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentNaturalRowSource CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
/-- Equal prime supports give identical Euler masks, even when the two
common ideals have different valuations. -/
theorem excluded_common_pair_ideal (χ : Character) (R C D : Ideal O)
    (hR : R≠0) (hC : C≠0) (hD : D≠0)
    (hs : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (I : Ideal O) :
    idealCoeff (excluded χ (R*C)) I=idealCoeff (excluded χ (R*D)) I := by
  by_cases hI : I=0
  · simp only [hI,idealCoeff_zero]
  · rw [excluded_ideal _ _ (mul_ne_zero hR hC),excluded_ideal _ _ (mul_ne_zero hR hD)]
    have hc : IsCoprime I C ↔ IsCoprime I D := by
      simpa only [isCoprime_comm] using
        CenteredMomentSecondSectorColumns.coprime_of_same_support C D I hC hD hI hs
    simp only [IsCoprime.mul_right_iff,hc]

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Exact natural-row dictionary identity for the literal second input,
with its actual puncture. Character-family and common-divisor hypotheses
are supplied by the input construction. -/
theorem actual_second_input_dictionary_mask
    (d : Label→ SecondInputDatum α) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I (d r.val.1).input.η.modulus then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) r.val.2.2.2.val)
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).C)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).C))) I := by
  exact actual_joint_retained_dictionary_mask left u₀ unit
    (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    η (d r.val.1).input.η F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I

/-- The right column uses the negated physical row. Its canonical
partition and nonzero proof are transported by the proved reflection. -/
theorem actual_second_reflected_input_dictionary_mask
    (d : Label→ SecondInputDatum α) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I (d r.val.1).input.η.modulus then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) (-r.val.2.2.2.val))
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).D)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).D))) I := by
  have he := actual_joint_retained_dictionary_mask left u₀ unit
    (reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf))
    η (d r.val.1).input.η F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I
  apply (excluded_common_pair_ideal F₂.character (d r.val.1).R (d r.val.1).C
    (d r.val.1).D hR (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I).symm.trans
  apply he.trans
  simpa only [mul_assoc] using excluded_common_pair_ideal _
    ((d r.val.1).input.η.modulus*(d r.val.1).R) (d r.val.1).C (d r.val.1).D
    (mul_ne_zero (d r.val.1).input.η.modulus_ne_bot hR)
    (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_input_dictionary_mask
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_reflected_input_dictionary_mask

#print axioms OAI.SevenEighths.Cycle61InitialMass.excluded_common_pair_ideal

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondDictionary -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySecondDictionary; sha256 63a1ef4c951edf8b705f3122aa7ed1784e7f6c6c75c97b42cc96a6854424bd2a -/
section
                                                      
                                                    
                                      

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The actual first-column mask in the joint-row encoding. Equality of
labels identifies the frequency without changing the fixed unit map. -/
theorem actual_geometry_joint_first_mask {ι : Type*} [Fintype ι]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (l : JointSourceLabel)(hl : l.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀
        (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)) l)) (I : Ideal O) :
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK bin j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  revert G
  unfold jointFirstFrequency
  rw [hl]
  intro G
  exact actual_geometry_column_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j G I

/-- Every actual second input whose parent is the selected geometric
column inherits the fixed dictionary mask. No first-mask analytic premise
is left to the second transform. -/
theorem actual_geometry_second_dictionary {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hf : jointFirstFrequency (!reflected) u₀
      (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀
        (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
        (secondEncodedRow (fun l=>(d l).block) first r)))
    (ψ : RayCharacter)(F₂ : NaturalRow ((d r.val.1).τ ψ) r.val.2.2.2.val)
    (hR : (d r.val.1).R≠0)(I : Ideal O) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let key := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).C)) I=
      idealCoeff (excluded (naturalRow
        (secondFixedDictionary η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
        ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).C))) I := by
  apply actual_second_input_dictionary_mask d first r (!reflected) u₀ _ hf _ G
  · intro J
    rw [hparent]
    exact actual_geometry_joint_first_mask reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      (secondEncodedRow (fun l=>(d l).block) first r) hfirst G J
  · exact hR

/-- Every actual second input whose parent is the selected geometric
column inherits the fixed dictionary mask. No first-mask analytic premise
is left to the second transform. -/
theorem actual_geometry_second_reflected_dictionary {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hf : jointFirstFrequency (!reflected) u₀
      (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀
        (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
        (secondEncodedRow (fun l=>(d l).block) first r)))
    (ψ : RayCharacter)(F₂ : NaturalRow ((d r.val.1).τ ψ) (-r.val.2.2.2.val))
    (hR : (d r.val.1).R≠0)(I : Ideal O) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let key := reflectedNonzeroJointLabel (secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf)
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).D)) I=
      idealCoeff (excluded (naturalRow
        (secondFixedDictionary η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
        ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).D))) I := by
  apply actual_second_reflected_input_dictionary_mask d first r (!reflected) u₀ _ hf _ G
  · intro J
    rw [hparent]
    exact actual_geometry_joint_first_mask reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      (secondEncodedRow (fun l=>(d l).block) first r) hfirst G J
  · exact hR

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_joint_first_mask
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_second_dictionary

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_second_reflected_dictionary

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySecondDictionary -/
