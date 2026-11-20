/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Choose the common second-row classifier from fixed presented data only.
The first full ball has already enlarged the positive original row subset,
so its starting proper keep is not restricted by this new split. -/
import Candidate.C092.transport.FixedRayPairSupport
set_option autoImplicit false
noncomputable section
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
namespace QRH.Cycle092.FixedRayPair
local notation "O"=>HeckeFamily.O

def stageQ (Q₁:Ideal O) (oldBase base ω₁ ω₂:Character) : Ideal O :=
  commonQ (internalQ (internalQ Q₁ oldBase) base) ω₁ ω₂

theorem stageQ_admissible (rayM Q₁:Ideal O) (oldBase base ω₁ ω₂:Character)
    (hq:Q₁ ≤ rayM) (hn:internalQ Q₁ oldBase ≠ 0) (ht:internalQ Q₁ oldBase ≠ ⊤)
    (h72:internalQ Q₁ oldBase ≤ Ideal.span {(72:O)}) :
    let q:=stageQ Q₁ oldBase base ω₁ ω₂
    q ≠ 0 ∧ q ≠ ⊤ ∧ q ≤ rayM ∧ q ≤ Ideal.span {(72:O)} ∧ q ≤ base.modulus ∧
    q ≤ ω₁.modulus ∧ q ≤ ω₂.modulus ∧ internalQ q base=q ∧
    internalQ q (base.product ω₁)=q ∧ internalQ q (base.product ω₂)=q := by
  let q:=stageQ Q₁ oldBase base ω₁ ω₂
  have g:=commonQ_le (internalQ (internalQ Q₁ oldBase) base) ω₁ ω₂
  have old:q ≤ internalQ Q₁ oldBase := g.1.trans inf_le_left
  have b:q ≤ base.modulus := g.1.trans inf_le_right
  have e:internalQ q base=q:=inf_eq_left.mpr b
  refine ⟨?_,fun he=>ht (top_le_iff.mp (he ▸old)),old.trans (inf_le_left.trans hq),
    old.trans h72,b,g.2.1,g.2.2,e,?_,?_⟩
  · exact internalQ_ne_zero _ (internalQ_ne_zero _ (internalQ_ne_zero _ hn base) ω₁) ω₂
  · exact (internalQ_product q base ω₁ g.2.1).trans e
  · exact (internalQ_product q base ω₂ g.2.2).trans e

#print axioms stageQ_admissible
end QRH.Cycle092.FixedRayPair
