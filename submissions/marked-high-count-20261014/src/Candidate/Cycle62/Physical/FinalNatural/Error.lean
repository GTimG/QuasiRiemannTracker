import Candidate.Cycle62.Physical.FinalNatural.Energy
import Candidate.Cycle62.Physical.FinalErrorRadius
import Candidate.Cycle62.Physical.ExtractedBranches.Envelope

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedWidth CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open Cycle62Moment.LowBranch Cycle62Physical.ExtractedBranches
local notation "O" => HeckeFamily.O

theorem actual_error_retainedState_width
    (η₀ η₁ υ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b J : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK₀ : 0<K₀) (hV : 0<V) (hZ : 1<Z) (hb : 0<b) (hJ : 0<J)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E*activeConductor C₁ D₁})
    (hυ : (υ.modulus.absNorm:ℝ)≤J*(η₁.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayFourExpansion.RayCharacter→Character)
    (hf : Family υ C D hC hD U τ)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (Bmask : ℝ) (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k₀ := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E}) K₀ V Z
    let Kerror := errorCommonRadius Z d k₀ c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C₁.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    physicalBlock υ t S β C D hC hD U R rows W K n≠0 →
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏q∈U,q.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hne
  obtain ⟨z,hz⟩ := actual_retained_witness t S β _ rows W K n hne
  have hU : (∏q∈U,q.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun q _ => (commonPrime_supported_ideal C D hC q).1)
  exact Cycle62FinalErrorRadius.actual_error_final_width η₀ η₁ υ (τ χ) C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b J N p k hp hK₀ hV hZ hb hJ hmod hυ _ _ z _ hU
    (actual_family_conductor hf t S β _ rows W K hK n hne χ) hz

theorem actual_error_source_budget
    (η₀ η₁ υ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b J : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK₀ : 0<K₀) (hV : 0<V) (hZ : 1<Z) (hb : 0<b) (hJ : 0<J)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E*activeConductor C₁ D₁})
    (hυ : (υ.modulus.absNorm:ℝ)≤J*(η₁.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (g₂ t₂ : ℝ) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k₀ := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E}) K₀ V Z
    let Kerror := errorCommonRadius Z d k₀ c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C₁.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    Real.logb Z R+Real.logb Z (υ.modulus.absNorm:ℝ)-g₂+t₂+
      Real.logb Z (4*(fixedFactor:ℝ))≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-g₂+t₂)+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  have he := Cycle62FinalErrorRadius.error_inverse_radius_log η₀ η₁ C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b N p k hp hK₀ hV hZ hb hmod
  dsimp only at he
  have hη := CenteredMomentFirstScale.norm_pos η₁.modulus η₁.modulus_ne_bot
  have hυpos := CenteredMomentFirstScale.norm_pos υ.modulus υ.modulus_ne_bot
  have hl := Real.logb_le_logb_of_le hZ hυpos hυ
  rw [Real.logb_mul (mul_pos hJ hη).ne' (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul hJ.ne' hη.ne',Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_positive_original_energy
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1<Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R₀ : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (v : ℝ)
    (Q : Ideal O) (hP : R₀*C≠0) (hPN : ((R₀*C).absNorm:ℝ)≤Z^Bmask)
    (R : ℝ) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let st := retainedState Z Bmask hZ τ Q (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s τ v) C R₀ B
    let X₁ := finalPlain d second L a 0
    let X₂ := finalPlain d second L a 1
    let indices := (CenteredMomentDivisorRaw.liveIndices L a).map (originalEmbedding s C B)
    finalPositiveEnergy d second L a st.radial.keep st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation (Cycle62.Physical.sourcePlainScales d.toSource second 0/
          (Ideal.absNorm (selectedPlain L a 0):ℝ))))
        (dilated s.W₂ (clipDilation (Cycle62.Physical.sourcePlainScales d.toSource second 1/
          (Ideal.absNorm (selectedPlain L a 1):ℝ))))
        (fun j : indices => primePool M H bslot (Z^(w j)))
        (fun (j : indices) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (freq j) I)
        (fun j : indices => Z^(w j)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := by
  dsimp only
  have he := actual_positive_natural_energy M H hH s η₀ θ w σ freq W bslot Z Bmask hZ
    hm C R₀ B τ v Q hP hPN R C₂ D₂ U second L a (fun _ => True)
  simp only [and_true] at he
  rw [he]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (CenteredMomentDivisorRaw.liveIndices L a) τ (fixedBadMask*idealGenerator (R₀*C)) 1
    _ _ (fun j => primePool M H bslot (Z^(w j)))
    (fun j I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (freq j) I)
    (fun j => Z^(w j)) v _ _ _ _ _

/-- A fixed ambient dictionary bounds the genuine final positive row. Its
width cap is checked on the physical radius budget, before greedy deletion. -/
theorem actual_retained_positive_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0<margin) (hbeta : 51/100≤HeckeZeroSupremum.beta) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop, 1<Z ∧
    ∀(hZ : 1<Z)(s : Input α) (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
      (v height mesh : ℝ), Matches M H hH s η₀ θ w σ freq W B Z →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(τ : RayFourExpansion.RayCharacter→Character),
      Family s.η C₂ D₂ hC₂ hD₂ U τ →
    ∀(R : ℝ)(cols : Finset (Ideal O))(β : Ideal O→ℂ)(rows : Finset O)
      (Wp : 𝓢(ℝ,ℂ))(K : ℝ),0<K → ∀n : Fin 4→ℤ,
      physicalBlock s.η s.t cols β C₂ D₂ hC₂ hD₂ U R rows Wp K n≠0 →
    ∀(χ : RayFourExpansion.RayCharacter)(C R₀ : Ideal O)
      (Ba : actualAllocations s.pools C)(hP : R₀*C≠0)
      (hPN : ((R₀*C).absNorm:ℝ)≤Z^Bmask)(second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices Ba.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (τ χ) (internalQ Q η₀)
      (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s (τ χ) v) C R₀ Ba
    let X₁ := finalPlain d second L₂ alloc 0
    let X₂ := finalPlain d second L₂ alloc 1
    let indices := (CenteredMomentDivisorRaw.liveIndices L₂ alloc).map (originalEmbedding s C Ba)
    let budget := Real.logb Z R+Real.logb Z (s.η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏q∈U,q.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle62.Physical.sourcePlainScales d.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle62.Physical.sourcePlainScales d.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
      X₁≤Z^L → X₂≤Z^L → budget≤Mcap →
    finalPositiveEnergy d second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*
        Z^(budget+εold+loss*(Fintype.card α:ℝ)+(1/6)*
          max (length Z X₁+length Z X₂+(9/2)*(∑j∈indices,w j)-budget) 0+(3/4)*mesh) := by
  obtain ⟨degree,Sp,hglobal⟩ := actual_global_main_uniform (α:=α) M H hH W A B ap bp
    2 Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp (by norm_num)
    hBmask hMcap hεold hloss hmargin hbeta
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hglobal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh hm hw hwL hmesh hwm hσlo hσhi hheight hfreq
    C₂ D₂ hC₂ hD₂ U τ hf R cols β rows Wp K hK n hne χ C R₀ Ba hP hPN second L₂ alloc
    st d X₁ X₂ indices budget p hp₁ hp₂ hXcap₁ hXcap₂ hbudget
  have hwidth : st.width≤budget := actual_retainedState_width hf s.t cols β R rows Wp K
    hK n hne Z Bmask hZ.1 χ (internalQ Q η₀) (R₀*C) hP hPN
  have hX₁ : 0<X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hX₂ : 0<X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have he := hZ.2 indices θ w σ freq v height mesh hw hwL hmesh (fun j _ => hwm j)
    hσlo hσhi hheight hfreq st rfl (hwidth.trans hbudget) p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂
  have hpaid := paid_global_exponent (width:=st.width) (nominal:=budget) (allowance:=0)
    (total:=length Z X₁+length Z X₂+(9/2)*(∑j∈indices,w j)) (oldLoss:=εold)
    (slotLoss:=loss*(Fintype.card α:ℝ)) (mesh:=mesh) (by linarith) le_rfl
  have hd := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  calc
    _ = energy st.character st.mask 1 v (p.profile 0) (p.profile 1)
      (fun j : indices => primePool M H B (Z^(w j)))
      (fun (j : indices) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (freq j) I)
      (fun j : indices => Z^(w j)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := by
        rw [actual_positive_original_energy M H hH s η₀ θ w σ freq W B Z Bmask hZ.1
          hm C R₀ Ba (τ χ) v (internalQ Q η₀) hP hPN R C₂ D₂ U second L₂ alloc,hp₁,hp₂]
    _ ≤ _ := he.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by simpa only [add_zero] using hpaid))
      (by positivity))

end
end OAI.SevenEighths.Cycle62FinalNatural
#print axioms OAI.SevenEighths.Cycle62FinalNatural.actual_error_retainedState_width
#print axioms OAI.SevenEighths.Cycle62FinalNatural.actual_positive_original_energy
#print axioms OAI.SevenEighths.Cycle62FinalNatural.actual_error_source_budget
#print axioms OAI.SevenEighths.Cycle62FinalNatural.actual_retained_positive_uniform
