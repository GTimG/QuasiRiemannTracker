/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredPhysical
import Candidate.C092.transport.TwistedRawSourceClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
open CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def coloredNativePrimaryPhysicalSource (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (D : FixedCubeDatum) (ω₁ ω₂ : Character)
    (G L : Id) (B : TwistedRawSource.commonAllocations r G) (E : TwistedRawSource.primaryAllocations r G B L) (v : ℝ) : ℂ :=
  let pool : liveIndices E.val→Finset Id:=fun i=>r.pool i.val.val
  let ν : liveIndices E.val→Id→ℂ:=fun i=>shiftedSlotCoefficient r v i.val.val
  let Wslot : liveIndices E.val→ℝ→ℂ:=fun i=>r.Wslot i.val.val
  let P : liveIndices E.val→ℝ:=fun i=>r.P i.val.val
  let R : Id:=(r.R*G)*L
  let d:=((TwistedRawSource.commonD r G B).1*E.val (Sum.inr 0),(TwistedRawSource.commonD r G B).2*E.val (Sum.inr 1))
  ∑p : (i:liveIndices E.val)→pool i,canonicalFrozenScalar D.row.χ R pool ν Wslot P p*
    (let M : Id:=∏i,(p i).val
     let K : Id:=(punctureProduct r.S r.H*M)*R
     let bad:=fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) (residualSuppliers M∪residualHoles K)
     let allowed:=supplyingResidualPairs (D.twistColumn ω₁).row (D.twistColumn ω₂).row (residualSuppliers M) (residualHoles K) (residualHoles K)
     fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂) (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v) bad allowed
       (r.X₁/(Ideal.absNorm d.1 : ℝ)) (r.X₂/(Ideal.absNorm d.2 : ℝ))-
     fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂) (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v) bad allowed
       (r.Y₁/(Ideal.absNorm d.1 : ℝ)) (r.Y₂/(Ideal.absNorm d.2 : ℝ)))

theorem coloredNativePrimaryCanonical_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id) (hG : G≠0) (hL : L≠0)
    (B : TwistedRawSource.commonAllocations r G) (E : TwistedRawSource.primaryAllocations r G B L) (v : ℝ) :
    TwistedRawSource.primaryCanonicalSource r (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ G L B E (shiftedSlotCoefficient r v)
      (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v)=
      coloredNativePrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v := by
  rw [shiftedProfile₁_eq_actual r ha hb v,shiftedProfile₂_eq_actual r ha hb v]
  unfold TwistedRawSource.primaryCanonicalSource coloredNativePrimaryPhysicalSource
  dsimp only
  have hh := coloredCanonicalSource_eq_fixedCubePhysical (ι:=liveIndices E.val) D ω₁ ω₂ (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v)
    r.S r.H ((r.R*G)*L) (mul_ne_zero (mul_ne_zero r.hR hG) hL)
    (fun i:liveIndices E.val=>r.pool i.val.val)
    (fun i I hI=>(r.hp i.val.val I hI).ne_zero)
    (fun i:liveIndices E.val=>shiftedSlotCoefficient r v i.val.val)
    (fun i:liveIndices E.val=>r.Wslot i.val.val)
    (fun i:liveIndices E.val=>r.P i.val.val)
    b r.X₁ r.X₂ r.Y₁ r.Y₂ ((TwistedRawSource.commonD r G B).1*E.val (Sum.inr 0),(TwistedRawSource.commonD r G B).2*E.val (Sum.inr 1))
    ⟨mul_ne_zero (TwistedRawSource.commonD_ne r G B).1 ((CenteredMomentCommonAllocationSum.allocation_data _ L E.val (Finset.mem_filter.mp E.property).1).1 _),
      mul_ne_zero (TwistedRawSource.commonD_ne r G B).2 ((CenteredMomentCommonAllocationSum.allocation_data _ L E.val (Finset.mem_filter.mp E.property).1).1 _)⟩
    le_rfl le_rfl (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)
    (r.hL.trans_le r.hY₁) (r.hL.trans_le r.hY₂)
  convert hh using 1
  congr 1
  ext p
  simp only [Finset.mem_univ]


#print axioms coloredNativePrimaryCanonical_eq_physical
end
end QRH.Cycle092.FixedCubeGauss
