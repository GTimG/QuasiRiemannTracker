/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Corrected actual raw-to-second physical ledger: no repeated assignment sum. -/
import Candidate.C092.transport.ColoredSelectionAverageMultiplicity
import Candidate.C092.transport.RootColoredSeedCapped
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredSelectionAverage
noncomputable section
local instance (priority := 2000) physicalAverageSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentChildRows
open CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalTail
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- ONE second ledger per allocation/ray after actual row-image grouping. -/
def secondAverageTerm {ι : Type} [Fintype ι] (s : Source ι (1/4) (9/4))
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) (η₁ η₂ τ : Character) (χ₀ : RayCharacter)
    (Q : Id) (m : O) (t K Z ξ Cz Ct : ℝ) (ζ : RayCharacter) : ℝ :=
  let r := restOf s (by norm_num) cover G B J
  let W := RawSides.selectionScaleQ s (by norm_num) cover G B J
  let X := RawSides.residualCapQ r
  let Tsec := RootColoredSeed.secondCutoffQ X K W
  Cz*profileCap r^2*K*Z^(93/100:ℝ) +
    RootColoredSeed.groupedPartTerms true r (by norm_num) (idealCoeff η₁) (idealCoeff η₂)
      (childCharacter τ ζ) χ₀ Q m t (16*K*W^4) Tsec Z ξ X +
    Ct*profileCap r^2*Z^(-22:ℝ) +
    RootColoredSeed.groupedPartTerms false r (by norm_num) (idealCoeff η₁) (idealCoeff η₂)
      (childCharacter τ ζ) χ₀ Q m t (16*K*W^4) Tsec Z ξ X

/-- The corrected active all-allocation raw side. Native MultBound is a
    concrete divisor-image cardinality condition; clipping retains BOTH its
    subpower cap for main terms and its assignment-count cap for zero/tail. -/
theorem original_raw_average_second_Q_caps (N : ℕ) (ξ : ℝ) (hξ : 0<ξ) :
    ∃ Cz Ct : ℝ,0<Cz ∧ 0<Ct ∧ ∀ᶠ Z : ℝ in atTop,3 ≤ Z ∧
    ∀(ι : Type)[Fintype ι](s : Source ι (1/4) (9/4)),Fintype.card ι ≤ N →
    ∀(cover : OriginalEnclosure s)(w : ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y : ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
      poolCap s ≤ Z^(8:ℝ) →
    ∀(C D G opposite : Id)(hD : D≠0)(hOpp : Supported opposite)(hG : Supported G),
      QRH.Record1252270103KernelMass.primeSupport opposite =
        QRH.Record1252270103KernelMass.primeSupport G →
    ∀(J : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val)),
      (∀B,(∑j∈J B,w j.val) ≤ 3/5000) →
    ∀(η₁ η₂ τ : Character)(χ₀ : RayCharacter)(Q : Id)(m : O)(t K : ℝ),
      1/2 ≤ K → K ≤ Z^(40:ℝ) →
    ∀ M : actualAllocations (tuplePools s) G→ℝ,
      MultBound s (by norm_num) cover G J K
        (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (J B)) M →
    (∑u∈concreteArtificial s C D hD,TwistedRawBall.rawEnergy s (by norm_num)
      (idealCoeff η₁) (idealCoeff η₂) opposite G hG u τ t K)/sourceVolume s  ≤ 
    outerAvg s (by norm_num) cover G (idealCoeff η₁) (idealCoeff η₂) J τ t
      (clippedMultiplicity s (by norm_num) cover G J M)
      (fun B ζ=>secondAverageTerm s cover G B (J B) η₁ η₂ τ χ₀ Q m t K Z ξ Cz Ct ζ)/sourceVolume s := by
  obtain ⟨Cz,Ct,hCz,hCt,hsecond⟩ := RootColoredSeed.original_second_zero_tail_Q_caps N ξ hξ
  refine ⟨Cz,Ct,hCz,hCt,hsecond.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hN cover w hw hP n y hy hy' hn hX hpool C D G opposite hD hOpp hG hOppG J hJ
    η₁ η₂ τ χ₀ Q m t K hK hKcap M hM
  have hK0 : 0<K := by linarith
  have hMc := multBound_clipped s (by norm_num) cover G J K _ M hM
  have hr := raw_sum_le_average s (by norm_num) (by norm_num) cover (idealCoeff η₁) (idealCoeff η₂)
    opposite G hOpp hG hOppG (concreteArtificial s C D hD) (concreteArtificial_squarefree s C D hD)
    J (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (J B))
    (clippedMultiplicity s (by norm_num) cover G J M) τ t K hK0 (widthBound_actual s _ cover G J) hMc
  refine hr.trans (div_le_div_of_nonneg_right ?_ (sourceVolume_pos s).le)
  unfold outerAvg
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Atot_nonneg _ _ _ _) (mul_nonneg (by positivity) (hMc B).1))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro ζ _
  exact (hZ.2 ι s hN cover w hw hP n y hy hy' hn hX hpool C D hD G B (J B) (hJ B)
    η₁ η₂ (childCharacter τ ζ) χ₀ Q m t K hK hKcap).2.2

#print axioms original_raw_average_second_Q_caps
end
end QRH.Cycle092.ColoredSelectionAverage
