/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CoupledWitness

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentEnergyBands
open QRH.Record12518109Source
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every nonnegative shortening of one actually supported quotient pair is
in the earlier source face, including upward bin rounding. -/
def RoundedPairAdmission (face : SourceFace) (Z X₁ X₂ plainRound slots Q : ℝ) : Prop :=
  ∀n₁ n₂ : ℝ,0 ≤ n₁ → 0 ≤ n₂ → n₁ ≤ length Z X₁+plainRound →
    n₂ ≤ length Z X₂+plainRound → face.Admissible n₁ n₂ slots Q

/-- The erased set is chosen before the sf ideals, whole-column correction,
selected column and tuple witnesses. A surviving coupled coefficient gives a
supported original or reference pair with genuine global source admission.
The radius identity and its delta gates remain explicit scalar inputs. -/
theorem coupled_common_rounded_admission (s : Input α) (C R₀ : Ideal O)
    (B : actualAllocations s.pools C) (w : α → ℝ) (S : Finset α)
    (Z t lower upper b F delta rho B₀ lam h slotMesh plainRound actualRadius : ℝ)
    (hZ : 1 < Z) (hlower : 0 < lower) (hslo : lower ≤ s.lower) (hshi : s.upper ≤ upper)
    (hscale : ∀i,s.P i = Z^(w i)) (ht : length Z s.X₁+length Z s.X₂ ≤ t)
    (hw : ∀i,0 ≤ w i) (hwm : ∀i∈S,w i ≤ slotMesh)
    (hS : S ⊆ liveIndices B.val) (htotal : (∑i,w i) ≤ b)
    (hmesh : 0 ≤ slotMesh) (hround : 0 ≤ plainRound) (hB : B₀ ≤ 1) (hlam : 0 < lam)
    (hd : 0 ≤ delta) (hdc : delta ≤ Real.logb Z (C.absNorm:ℝ))
    (hh : 0 ≤ h) (hQ : 0 ≤ actualRadius) (hRadius : actualRadius = F-delta-rho)
    (hguard : commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+2*plainRound+B₀*rho ≤ B₀*F-t-b) :
    let f := firstFrozenWidth B.val w
    let P := t-Real.logb Z (C.absNorm:ℝ)+f+(commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+2*plainRound)
    let Q := actualRadius
    ∃ R : Finset α,R ⊆ S ∧
      (∑i∈R,w i) ≤ max 0 (max (b-f-(B₀*Q-P)/lam) (b-f-h*Q))+slotMesh ∧
      ∀ (A₁ A₂ D : Ideal O) (correction : Ideal O → ℂ)
      (modifier : Tuple (liveIndices B.val) → ℂ) (a : Ideal O),
      modifiedCoupledCommonColumn s C R₀ B A₁ A₂ D correction modifier a ≠ 0 →
      ∃ I J : Ideal O,I ≠ 0 ∧ J ≠ 0 ∧
        ((s.W₁ ((I.absNorm:ℝ)/(s.X₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0 ∧
          s.W₂ ((J.absNorm:ℝ)/(s.X₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0 ∧
          RoundedPairAdmission (SourceFace.mk B₀ lam 0 B₀ 0 h) Z
            (s.X₁/(B.val (Sum.inr 0)).absNorm) (s.X₂/(B.val (Sum.inr 1)).absNorm)
            plainRound (∑i∈S\R,w i) Q) ∨
         (s.W₁ ((I.absNorm:ℝ)/(s.Y₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0 ∧
          s.W₂ ((J.absNorm:ℝ)/(s.Y₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0 ∧
          RoundedPairAdmission (SourceFace.mk B₀ lam 0 B₀ 0 h) Z
            (s.Y₁/(B.val (Sum.inr 0)).absNorm) (s.Y₂/(B.val (Sum.inr 1)).absNorm)
            plainRound (∑i∈S\R,w i) Q)) := by
  subst actualRadius
  dsimp only
  by_cases hf : frozenCoefficient B.val C R₀ s.ν s.W s.P = 0
  · refine ⟨∅,Finset.empty_subset _,?_,?_⟩
    · simp only [Finset.sum_empty]
      exact add_nonneg (le_max_left _ _) hmesh
    · intro A₁ A₂ D correction modifier a hn
      exact False.elim (hn (by simp only [modifiedCoupledCommonColumn,hf,zero_mul]))
  · obtain ⟨R,hR,hcost,hadm⟩ := actual_common_rounded_admission s C R₀ B w S
      Z t lower upper b F delta rho B₀ lam h slotMesh plainRound hZ hlower hslo hshi hscale
      hf ht hw hwm hS htotal hmesh hround hB hlam hd hdc hh hQ hguard
    refine ⟨R,hR,hcost,?_⟩
    intro A₁ A₂ D correction modifier a hn
    obtain ⟨_,I,J,hI,hJ,hpair⟩ := coupled_first_common_support s C R₀ B A₁ A₂ D correction modifier a hn
    refine ⟨I,J,hI,hJ,?_⟩
    rcases hpair with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨h₁,h₂,hadm s.X₁ s.X₂ s.X₁_pos s.X₂_pos rfl I J hI hJ h₁ h₂⟩
    · exact Or.inr ⟨h₁,h₂,hadm s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos s.same_product I J hI hJ h₁ h₂⟩

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.coupled_common_rounded_admission
