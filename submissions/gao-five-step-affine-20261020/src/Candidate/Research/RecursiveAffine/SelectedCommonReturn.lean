import Candidate.Research.RecursiveAffine.NativePhysicalBridge
import Candidate.Cycle63.Physical.InitialMass.SecondLowCommon

/- The original common and reciprocal residual shell payment, with an actual
attaining weighted return and its full source metadata kept. The caller must
supply each actual daughter's native regional source estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153SourceReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonLinearNormalization
open CenteredMomentCommonProfile Cycle63InitialMass Cycle63Moment Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite maximum is taken over whole normalized daughter returns,
before the final rows. The original common Cauchy and reciprocal residual
shell estimates are then applied unchanged. No number of residual ideals,
active allocations or rows is introduced into the terminal class count.

The actual source inequality `hsource` is the still-required recursive
regional producer. This lemma does not assume a desired returned length and
does not prove that source inequality. It closes its physical aggregation
with precisely the native shell factors. -/
theorem actual_common_low_selected_return (b ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Input α), s.upper ≤ b →
      ∀ (C R : Ideal O), C ≠ 0 →
      ∀ (Ds : Finset (Ideal O)) (zs : Finset O) (weight : O → ℝ)
        (T Z pad : ℝ), 1 ≤ T → 1 < Z →
      (∀ D ∈ Ds, Squarefree D ∧ T ≤ (D.absNorm : ℝ) ∧ (D.absNorm : ℝ) < 2*T) →
      ∀ (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (rad : ℝ), 0 < rad →
      (∀ z, keep z → 0 ≤ (Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀ z ∈ zs, keep z) →
      (∀ z ∈ zs, weight z ≤ (Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀ B : actualAllocations s.pools C, commonScalar s C R B ≠ 0 →
        (commonData s C R B).toSource.allowance Z ≤ pad) →
      ∀ (sourceConstant oldPart : ℝ), 0 ≤ sourceConstant → 0 ≤ oldPart →
      ∀ (sourceWeight : PhysicalDaughter s C R Ds → ℝ),
      (∀ d, 0 ≤ sourceWeight d) →
      ∀ (SourceReturn : PhysicalDaughter s C R Ds → ℝ → Prop),
      (∀ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 ≠ 0 →
        ∃ ret : ℝ, 0 ≤ ret ∧ SourceReturn d ret ∧
          physicalDaughterEnergy s C R Ds keep Φ rad d ≤
            sourceConstant * (oldPart + sourceWeight d * ret)) →
      ∃ Ret : ℝ, 0 ≤ Ret ∧
        ((Ret = 0 ∧ ∀ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 = 0) ∨
          ∃ (d : PhysicalDaughter s C R Ds) (ret : ℝ),
            commonScalar s C R d.1 ≠ 0 ∧ 0 ≤ ret ∧ SourceReturn d ret ∧
            Ret = sourceWeight d * ret ∧
            physicalDaughterEnergy s C R Ds keep Φ rad d ≤
              sourceConstant * (oldPart + Ret)) ∧
        (∑ D ∈ Ds, ∑ z ∈ zs, weight z * commonRetainedCost s C R D z) ≤
          K * s.toData.profileFactor * (∏ j, s.M j)^2 *
            (sourceConstant * (oldPart + Ret)) * (C.absNorm : ℝ)^(ε-1) *
            (2*T)^(2*ε) * Z^pad := by
  obtain ⟨K, hK, hcommon⟩ := actual_common_low_energy (ι:=α) b ε hε
  refine ⟨K, hK, ?_⟩
  intro s hb C R hC Ds zs weight T Z pad hT hZ hDs keep Φ rad hrad hΦ hkeep hw hallow
    sourceConstant oldPart hconstant hold sourceWeight hweight SourceReturn hsource
  obtain ⟨Ret, hRet, hselected, hbound⟩ := exists_normalized_physical_return s C R Ds sourceWeight hweight
    (fun d ret => SourceReturn d ret ∧ physicalDaughterEnergy s C R Ds keep Φ rad d ≤
      sourceConstant * (oldPart + sourceWeight d * ret))
    (by
      intro d hd
      obtain ⟨ret, hr, hp, he⟩ := hsource d hd
      exact ⟨ret, hr, hp, he⟩)
  refine ⟨Ret, hRet, ?_, ?_⟩
  · rcases hselected with hnone | ⟨d, ret, hd, hr, ⟨hp, he⟩, heq⟩
    · exact Or.inl hnone
    · refine Or.inr ⟨d, ret, hd, hr, hp, heq, ?_⟩
      simpa only [heq] using he
  · have hE : 0 ≤ sourceConstant * (oldPart + Ret) :=
      mul_nonneg hconstant (add_nonneg hold hRet)
    refine hcommon s hb C R hC Ds zs weight T Z pad (sourceConstant * (oldPart + Ret))
      hT hZ hE hDs keep Φ rad hrad hΦ hkeep hw hallow ?_
    intro B hB D hD alloc ha second
    let d : PhysicalDaughter s C R Ds := ⟨B, ⟨D, hD⟩, ⟨alloc, ha⟩, second⟩
    obtain ⟨ret, _, ⟨_, he⟩, hle⟩ := hbound d hB
    rw [← physicalDaughterEnergy_eq_native s C R Ds keep Φ rad d]
    exact he.trans (mul_le_mul_of_nonneg_left (by linarith only [hle]) hconstant)

end
end OAI.SevenEighths.Cycle153SourceReturn

#print axioms OAI.SevenEighths.Cycle153SourceReturn.actual_common_low_selected_return
