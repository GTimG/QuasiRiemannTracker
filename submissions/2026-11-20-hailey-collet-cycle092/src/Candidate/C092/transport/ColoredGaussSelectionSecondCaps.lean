/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual selected colored first Gauss energy joins the original second Poisson ledger. -/
import Candidate.C092.transport.ColoredGaussSelectionSecond
import Candidate.C092.transport.RootColoredSeedCapped
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussSelection
noncomputable section
local instance (priority := 2000) capsSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentChildRows
open CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalTail
open MixedOriginalNormCap
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The original root geometry discharges the genuine selected second zero/tail
    hypotheses. No selected-energy or coefficient-completion assumption is added. -/
theorem original_selected_second_Q_caps (N : ℕ) (ξ : ℝ) (hξ : 0<ξ) :
    ∃ Cz Ct : ℝ, 0<Cz ∧ 0<Ct ∧ ∀ᶠ Z : ℝ in atTop, 3 ≤ Z ∧
    ∀ (ι : Type) [Fintype ι] (s : Source ι (1/4) (9/4)),Fintype.card ι ≤ N →
    ∀(cover : OriginalEnclosure s)(w : ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y : ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
      poolCap s ≤ Z^(8:ℝ) →
    ∀(C D : Id)(hD : D ≠ 0)(G : Id)(B : actualAllocations (tuplePools s) G)
      (J : Finset (liveIndices B.val)),(∑j∈J,w j.val) ≤ 3/5000 →
    ∀(η₁ η₂ τ : Character)(χ₀ : RayCharacter)(Q : Id)(m : O)(t K : ℝ),
      1/2 ≤ K → K ≤ Z^(40:ℝ) →
    (∑u∈concreteArtificial s C D hD,
      RootColoredSeed.energy (allocatedLiveSource s (by norm_num) cover G B) (by norm_num)
        (idealCoeff η₁) (idealCoeff η₂) u τ t K) / sourceVolume s  ≤ 
      secondSelectedTerms s (by norm_num) (by norm_num) cover C D hD G B J
        η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct / sourceVolume s := by
  obtain ⟨Cz,Ct,hCz,hCt,hsecond⟩ := RootColoredSeed.original_second_zero_tail_Q_caps N ξ hξ
  refine ⟨Cz,Ct,hCz,hCt,hsecond.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hN cover w hw hP n y hy hy' hn hX hpool C D hD G B J hJ η₁ η₂ τ χ₀ Q m t K hK hKcap
  let rL := allocatedLiveSource s (by norm_num : (0:ℝ) ≤ 9/4) cover G B
  let W := RawSides.selectionScaleQ s (by norm_num) cover G B J
  have hK0 : 0<K := by linarith
  have hs : ∑u∈concreteArtificial s C D hD,
      RootColoredSeed.energy rL (by norm_num) (idealCoeff η₁) (idealCoeff η₂) u τ t K  ≤ 
      selectedTerms rL (fun _=>rfl) J (by norm_num) (idealCoeff η₁) (idealCoeff η₂)
        (concreteArtificial s C D hD) τ t (fun _=>16*K*W^4) := by
    apply selection_to_vset rL (fun _=>rfl) J (by norm_num) (idealCoeff η₁) (idealCoeff η₂)
      (concreteArtificial s C D hD) (concreteArtificial_squarefree s C D hD) τ t K _ hK0
    · intro z hz
      have hh := scale_one_le rL J
      rw [scale_eq_actual] at hh
      change 1 ≤ W at hh
      positivity
    · intro z hz
      have hh := selected_radius rL J K hK0 z hz
      rw [scale_eq_actual] at hh
      exact hh
  apply div_le_div_of_nonneg_right _ (le_of_lt (sourceVolume_pos s))
  refine hs.trans ?_
  unfold selectedTerms secondSelectedTerms
  apply mul_le_mul_of_nonneg_left _ (by unfold Atot; positivity)
  apply Finset.sum_le_sum
  intro z hz
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ζ hζ
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (hZ.2 ι s hN cover w hw hP n y hy hy' hn hX hpool C D hD G B J hJ
    η₁ η₂ (childCharacter τ ζ) χ₀ Q m t K hK hKcap).2.2

/-- The complete allocated colored first raw side is paid by the genuine
    original second ledger, with the original normalization at every allocation. -/
theorem original_raw_selected_second_Q_caps (N : ℕ) (ξ : ℝ) (hξ : 0<ξ) :
    ∃ Cz Ct : ℝ, 0<Cz ∧ 0<Ct ∧ ∀ᶠ Z : ℝ in atTop, 3 ≤ Z ∧
    ∀ (ι : Type) [Fintype ι] (s : Source ι (1/4) (9/4)), Fintype.card ι ≤ N →
    ∀(cover : OriginalEnclosure s)(w : ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y : ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
      poolCap s ≤ Z^(8:ℝ) →
    ∀(C D G opposite : Id)(hD : D ≠ 0)(hOpp : Supported opposite)(hG : Supported G),
      QRH.Record1252270103KernelMass.primeSupport opposite =
        QRH.Record1252270103KernelMass.primeSupport G →
    ∀(J : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val)),
      (∀B,(∑j∈J B,w j.val) ≤ 3/5000) →
    ∀(η₁ η₂ τ : Character)(χ₀ : RayCharacter)(Q : Id)(m : O)(t K : ℝ),
      1/2 ≤ K → K ≤ Z^(40:ℝ) →
    (∑u∈concreteArtificial s C D hD,TwistedRawBall.rawEnergy s (by norm_num)
      (idealCoeff η₁) (idealCoeff η₂) opposite G hG u τ t K) / sourceVolume s ≤
    (actualAllocations (tuplePools s) G).card *
      ∑B : actualAllocations (tuplePools s) G,
        TwistedRawBall.allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
          (secondSelectedTerms s (by norm_num) (by norm_num) cover C D hD G B (J B)
            η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct / sourceVolume s) := by
  obtain ⟨Cz,Ct,hCz,hCt,hsecond⟩ := original_selected_second_Q_caps N ξ hξ
  refine ⟨Cz,Ct,hCz,hCt,hsecond.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hN cover w hw hP n y hy hy' hn hX hpool C D G opposite hD hOpp hG hOppG J hJ η₁ η₂ τ χ₀ Q m t K hK hKcap
  have hK0 : 0<K := by linarith
  have hr := TwistedRawBall.raw_sum_le_allocated s (by norm_num) (by norm_num) cover
    (idealCoeff η₁) (idealCoeff η₂) opposite G hOpp hG hOppG (concreteArtificial s C D hD) τ t K hK0
  have hdr := div_le_div_of_nonneg_right hr (le_of_lt (sourceVolume_pos s))
  simp only [Finset.sum_div,mul_div_assoc] at hdr
  simp only [Finset.sum_div]
  refine hdr.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [Finset.sum_div] using hZ.2 ι s hN cover w hw hP n y hy hy' hn hX hpool C D hD G B (J B) (hJ B)
    η₁ η₂ τ χ₀ Q m t K hK hKcap

#print axioms original_selected_second_Q_caps
#print axioms original_raw_selected_second_Q_caps
end
end QRH.Cycle092.ColoredGaussSelection
