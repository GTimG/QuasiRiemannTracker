/- Copyright (c) 2026 Sil. Apache-2.0.
The ACTUAL first physical block paid from explicit RawSideBounds.
Conditional machinery until Raw/Small discharge that named contract;
no other energy estimate is postulated. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedFirstRawProjector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedFirstRawBlock
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentFirstColumns CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowBudget CenteredMomentLogDyadic
open MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow MixedFirstPhysicalApplication
open MixedFirstPhysicalBudget MixedFirstCommonSum
open RepairedFirstRawSides RepairedFirstRawScalar RepairedFirstRawKernel RepairedFirstRawProjector
open ActualEisensteinCubic MixedInnerExceptionalBlock CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def blockTerm (s : Source ι a b) (ha : 0 < a) (η : Character) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  commonHeight s η t C D*block η (fixedBadMask*idealGenerator s.R) 1 t
    (sourceColumns s) (sourceCoefficient s ha 1) C D hC hD E rows Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀

def artificialMass (s : Source ι a b) (C D : Id) (hD : D≠0) : ℝ :=
  ∑u∈artificialDivisors s C D hD,‖(UniqueFactorizationMonoid.moebius u:ℂ)‖/(u.absNorm:ℝ)

theorem artificialMass_nonneg (s : Source ι a b) (C D : Id) (hD : D≠0) :
    0 ≤ artificialMass s C D hD :=
  Finset.sum_nonneg (fun u _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

theorem actual_block_expansion (s : Source ι a b) (ha : 0 < a) (η : Character) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    blockTerm s ha η t C D hC hD E rows Φ K K₀ H₀ A₀ B₀=
      commonHeight s η t C D*scalar C D hC E K A₀ B₀*
        ∑u∈artificialDivisors s C D hD.1,
          (UniqueFactorizationMonoid.moebius u:ℂ)*activeRow C D hC
            (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)*
          ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            RepairedFirstRawKernel.matrix s ha C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
              (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀ := by
  have he := selected_physical_average s ha 1 η t C D hC hD hCD E rows hrows
    ({1}:Finset Id) (fun _ => 1) 1 (by norm_num) (fun _ _ => by norm_num)
    Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  simpa only [Finset.sum_singleton,Finset.sum_product,one_div,inv_one,Complex.ofReal_one,
    one_mul,block_selected_one,blockTerm,RepairedFirstRawKernel.matrix] using he

set_option maxHeartbeats 1400000 in
theorem block_of_raw_sides (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a, s.d=(1,1) →
    ∀ (η : Character) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ E : Finset (CommonIndex C D),
    ∀ rows : Finset O,(∀z∈rows,z≠0) →
    ∀ K K₀ H₀ A₀ B₀ KL KR Z A loss : ℝ,
      0 < K → 0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR → 1 < Z → 0 ≤ A →
      (∀z∈rows,‖eisEmbedding z‖^2 ≤ KL) → (∀z∈rows,‖eisEmbedding z‖^2 ≤ KR) →
      RawSideBounds s ha η C D hC hD E KL KR A Z loss J →
    ‖blockTerm s ha η t C D hC hD E rows Φ K K₀ H₀ A₀ B₀‖/sourceVolume s ≤
      (256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*(windowMass J t)^2*A*Z^loss)*
        commonWeight C D E*artificialMass s C D hD.1 := by
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := kernel_from_raw (ι:=ι) (a:=a) (b:=b) Φ J
  refine ⟨Ckernel,hCkernel,?_⟩
  intro s ha hunit η t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ KL KR Z A loss
    hK hK₀ hH₀ hA₀ hB₀ hKL hKR hZ hA hrowsL hrowsR hside
  let pref := referencePrefactor s η C D E K (Real.log 4)
  let H := Ckernel*pref*(windowMass J t)^2*A*Z^loss
  let r := ‖scalar C D hC E K A₀ B₀‖/sourceVolume s
  let mat := fun u χ ξ => RepairedFirstRawKernel.matrix s ha C D hC hD E u
    (fixedPair η C D hC E χ (ξ⁻¹)).left (fixedPair η C D hC E χ (ξ⁻¹)).right
    t rows Φ K K₀ H₀ A₀ B₀
  have hr : 0 ≤ r := div_nonneg (norm_nonneg _) (sourceVolume_pos s).le
  have hpref : 0 ≤ pref := referencePrefactor_nonneg s η C D E K (Real.log 4) hK.le
  have hH : 0 ≤ H := by
    have hz := zero_lt_one.trans hZ
    dsimp only [H]
    positivity
  have hphase : ‖activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)‖ ≤ 1 :=
    QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _
  have hheight : ‖commonHeight s η t C D‖ ≤ 1 := by
    rw [commonHeight,norm_mul,norm_star]
    exact (mul_le_mul (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η (fixedBadMask*idealGenerator s.R) 1 1 t C hC.1)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η (fixedBadMask*idealGenerator s.R) 1 1 t D hD.1)
      (norm_nonneg _) zero_le_one).trans_eq (by ring)
  by_cases hzero : block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (sourceCoefficient s ha 1) C D hC hD E rows Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀=0
  · simp only [blockTerm,hzero,mul_zero,norm_zero,zero_div]
    have hw := common_weight_nonneg C D E
    have hu := artificialMass_nonneg s C D hD.1
    have hf := fixedPresentationCost_pos
    have hz := zero_lt_one.trans hZ
    positivity
  have hmat : ∀u∈artificialDivisors s C D hD.1,(UniqueFactorizationMonoid.moebius u:ℂ)≠0 →
      ∀χ ξ,r*‖mat u χ ξ‖ ≤ H/(u.absNorm:ℝ) := by
    intro u hu hμ χ ξ
    obtain ⟨hleft,hright⟩ := hside u hu hμ χ ξ
    let F := fixedPair η C D hC E χ (ξ⁻¹)
    let WL := windowBudget J t (sideBudget s F.left C D u A Z loss)
    let WR := windowBudget J t (sideBudget s F.right D C u A Z loss)
    have hEL := sideBudget_nonneg s F.left C D u A Z loss hA (zero_lt_one.trans hZ).le
    have hER := sideBudget_nonneg s F.right D C u A Z loss hA (zero_lt_one.trans hZ).le
    have hk := hkernel s ha C D hC hD E u F.left F.right t K K₀ H₀ A₀ B₀ KL KR
      hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrowsL hrowsR _ _ hEL hER hleft hright
    have hnorm := window_pair_reference s ha η t C D hC hD hCD E χ ξ rows Φ
      K K₀ H₀ A₀ B₀ Z A loss hK hA₀ hB₀ hZ hA u J hzero
    calc
      _ ≤ r*(Ckernel*(WL*WR)) := mul_le_mul_of_nonneg_left hk hr
      _ = Ckernel*(r*(WL*WR)) := by ring
      _ ≤ Ckernel*(pref*(windowMass J t)^2*(A*Z^loss/(u.absNorm:ℝ))) :=
        mul_le_mul_of_nonneg_left hnorm hCkernel
      _ = _ := by dsimp only [H];ring
  have hproj := mobius_ray_projector (artificialDivisors s C D hD.1) r H hr hH
    (activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)) hphase mat hmat
  let totalSum : ℂ := ∑u∈artificialDivisors s C D hD.1,
    (UniqueFactorizationMonoid.moebius u:ℂ)*activeRow C D hC
      (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)*
    ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*mat u χ ξ
  rw [actual_block_expansion s ha η t C D hC hD hCD E rows hrows Φ K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀]
  calc
    _ ≤ r*‖totalSum‖ := by
      rw [norm_mul,norm_mul]
      change (‖commonHeight s η t C D‖*‖scalar C D hC E K A₀ B₀‖)*‖totalSum‖/sourceVolume s ≤ _
      have hh := mul_le_mul_of_nonneg_right hheight
        (mul_nonneg (norm_nonneg (scalar C D hC E K A₀ B₀)) (norm_nonneg totalSum))
      convert div_le_div_of_nonneg_right hh (sourceVolume_pos s).le using 1 <;>
        (try dsimp only [r]) <;> ring
    _ ≤ 256*H*artificialMass s C D hD.1 := hproj
    _ = _ := by
      dsimp only [H,pref]
      rw [unit_prefactor s hunit η C D E K]
      ring

end
end Candidate.FourthPower.RepairedFirstRawBlock

