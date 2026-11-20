/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Authentic first Gauss rows at independently colored source coefficients. -/
import Candidate.C092.transport.TwistedRawBallDictionary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CenteredMomentLiveDomain CenteredMomentSourceRectangle
open CenteredMomentGaussEnergy CenteredMomentFirstPhysicalSource CenteredMomentHeckeColumnWindow
open QRH.SilDensitySplit.CubeFree.FP MixedFirstLiveSource
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]
local instance (priority := 2000) sumGaussDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

theorem first_gauss_common_tuples (ω₁ ω₂ : Id →*₀ ℂ) (H : Id)
    (T : (ι ⊕ Fin 2) → Finset Id) (hT : ∀ j, ∀ I ∈ T j, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ T (Sum.inl i), Prime I)
    (C G R seed L : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G) (hseed : seed ∣ G)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id)
    (τ : Character) (t : ℝ) (k : O) :
    let Q := finiteColumns (Fintype.piFinset T)
    let β := coloredColumn (Fintype.piFinset T) H ω₁ ω₂
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed)
    gaussPolynomial Finset.univ (element C G hG.1 Q) (element_supported C G hG.1 Q)
      (fun I => (if L ∣ (I:Id) then β (G*I) else 0)*heightCoeff τ t I) k =
      ∑ B : actualAllocations T G,
        (MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
          frozenCoefficient B.val G R ν Wslot P) *
        ∑ v ∈ liveBox T B.val (allocation_data T G B.val (Finset.mem_filter.mp B.property).1).1,
          (if L ∣ finiteTupleProduct v then
            coloredTuple H ω₁ ω₂
              (liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2) v else 0) *
            (heightCoeff τ t (finiteTupleProduct v)*primaryGaussRow (finiteTupleProduct v) k) := by
  dsimp only
  have hgauss := first_gauss_sum C G hG (finiteColumns (Fintype.piFinset T))
    (fun I : Id => (if L ∣ I then coloredColumn (Fintype.piFinset T) H ω₁ ω₂
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed) (G*I) else 0)*heightCoeff τ t I) k
  refine hgauss.trans ?_
  have hh := common_masked_column_sum ω₁ ω₂ H T hT hp G R seed L hG.1 hseed
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2
    (fun I => heightCoeff τ t I*primaryGaussRow I k)
  calc
    _ = ∑ I ∈ residualPool G hG.1 (finiteColumns (Fintype.piFinset T)),
      (if IsCoprime G I ∧ L ∣ I then
        coloredColumn (Fintype.piFinset T) H ω₁ ω₂
          (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed) (G*I) else 0) *
        (heightCoeff τ t I*primaryGaussRow I k) := by
      apply Finset.sum_congr rfl
      intro I hI
      have hm := (mem_residualPool G hG.1 _ I).mp hI
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
      have hz : finiteTupleProduct v ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j _ => hT j _ (Fintype.mem_piFinset.mp hv j))
      have hI0 : I ≠ 0 := right_ne_zero_of_mul (he ▸ hz)
      have hc : IsCoprime C I ↔ IsCoprime G I := by
        rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC.1 hI0,
          ← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hG.1 hI0]
        change Disjoint (QRH.Record1252270103KernelMass.primeSupport C) _ ↔
          Disjoint (QRH.Record1252270103KernelMass.primeSupport G) _
        rw [hCG]
      rw [hc]
      by_cases hg : IsCoprime G I <;> by_cases hl : L ∣ I <;> simp only [hg,hl,ite_true,ite_false,
        true_and,false_and,mul_zero,zero_mul] <;> ring
    _ = _ := hh.trans (by
      apply Finset.sum_congr rfl
      intro B hB
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      split_ifs <;> ring)

#print axioms first_gauss_common_tuples
end
end QRH.Cycle092.TwistedRawBall
