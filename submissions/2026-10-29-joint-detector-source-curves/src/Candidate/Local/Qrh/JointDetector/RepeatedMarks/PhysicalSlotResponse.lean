/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedRescaling
import Candidate.Local.Qrh.JointDetector.RefinedSupplier

namespace Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentEnergyState LocalMoment CanonicalRowCompletion
local notation "O" => HeckeFamily.O

/-- Radius transport preserves the whole original slot, before taking a
norm. No root/core intersections or natural zeros are removed. -/
theorem originalSlot_rescale {Slot : Type*}
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    {Z bΦ U : ℝ} (st : NaturalState Z 0 bΦ) (η η₀ : Character)
    (hη : st.character=η) (hpuncture : st.puncture=1)
    (root : NonzeroIdeal) (W : ℝ→ℂ)
    (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ)
    (t : ℝ) (u : FreeRow) (s : Slot) (hU : 1<U) (hZ : 0<Z) :
    originalSlot M H hH η η₀ root W U θ
      (fun k=>RootedRescaling.width U Z (w k)) σ v t u s =
    normalizedSlot st.character st.mask 1 (rowMap (u,root))
      (primePool M H 2 (Z^(w s)))
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w s)) (σ s) (v s) I) t (Z^(w s)) := by
  have hmask : st.mask=fixedBadMask*idealGenerator 1 := by
    change fixedBadMask*idealGenerator st.puncture=_
    rw [hpuncture]
  simp only [originalSlot,RootedRescaling.radius_eq hU hZ,hη,hmask]
  rfl

/-- Active finite slot products agree with the literal physical mass.
The ambient slot type stays fixed; inactive extensions never enter the
product, and every active copied factor is paid at its original width. -/
theorem originalSlot_mass {α : Type} [Fintype α] [DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    {Z bΦ U : ℝ} (st : NaturalState Z 0 bΦ) (η η₀ : Character)
    (hη : st.character=η) (hpuncture : st.puncture=1)
    (root : NonzeroIdeal) (W : ℝ→ℂ) (T : Finset α)
    (θ : T→RayQuotient.Characters M H) (w σ v : T→ℝ)
    (θext : α→RayQuotient.Characters M H) (wext σext vext : α→ℝ)
    (hθ : ∀k : T,θext k.val=θ k) (hw : ∀k : T,wext k.val=w k)
    (hσ : ∀k : T,σext k.val=σ k) (hv : ∀k : T,vext k.val=v k)
    (t : ℝ) (u : FreeRow) (hU : 1<U) (hZ : 0<Z) :
    (∏s∈T,‖originalSlot M H hH η η₀ root W U θext
      (fun k=>RootedRescaling.width U Z (wext k)) σext vext t u s‖^2)=
    RefinedSupplier.slotMass M H hH st η₀ W θ w σ v t (rowMap (u,root)) := by
  unfold RefinedSupplier.slotMass
  rw [←Finset.prod_coe_sort T]
  apply Finset.prod_congr rfl
  intro k _
  rw [originalSlot_rescale M H hH st η η₀ hη hpuncture root W θext wext σext vext t u k.val hU hZ]
  simp only [hθ k,hw k,hσ k,hv k]

end
end Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete
