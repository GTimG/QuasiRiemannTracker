/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredPhysical

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

/-- The final literal H8 sum of signed physical sources, indexed by the
actual residual marked assignments after both native primary allocations. -/
def coloredPrimaryPhysicalSource (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (D : FixedCubeDatum) (ω₁ ω₂ : Character)
    (G L : Id) (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) (v : ℝ) : ℂ :=
  let pool : liveIndices E.val→Finset Id:=fun i=>r.pool i.val.val
  let ν : liveIndices E.val→Id→ℂ:=fun i=>shiftedSlotCoefficient r v i.val.val
  let Wslot : liveIndices E.val→ℝ→ℂ:=fun i=>r.Wslot i.val.val
  let P : liveIndices E.val→ℝ:=fun i=>r.P i.val.val
  let R : Id:=(r.R*G)*L
  let d:=primaryOrdinaryPrefix r G L B E
  ∑p : (i:liveIndices E.val)→pool i,canonicalFrozenScalar D.row.χ R pool ν Wslot P p*
    (let M : Id:=∏i,(p i).val
     let K : Id:=(punctureProduct r.S r.H*M)*R
     let bad:=fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) (residualSuppliers M∪residualHoles K)
     let allowed:=supplyingResidualPairs (D.twistColumn ω₁).row (D.twistColumn ω₂).row (residualSuppliers M) (residualHoles K) (residualHoles K)
     fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂) (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v) bad allowed
       (r.X₁/(Ideal.absNorm d.1 : ℝ)) (r.X₂/(Ideal.absNorm d.2 : ℝ))-
     fixedCubePhysicalSource (D.twistColumn ω₁) (D.twistColumn ω₂) (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v) bad allowed
       (r.Y₁/(Ideal.absNorm d.1 : ℝ)) (r.Y₂/(Ideal.absNorm d.2 : ℝ)))

def coloredPrimaryCanonicalSource (r : Source ι a b) (D : FixedCubeDatum) (ω₁ ω₂ : Character)
    (G L : Id) (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) : ℂ :=
  TwistedRawSource.canonicalSource (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ r.S r.H ((r.R*G)*L)
    (fun i:liveIndices E.val=>r.pool i.val.val)
    (fun i:liveIndices E.val=>ν i.val.val)
    (fun i:liveIndices E.val=>r.Wslot i.val.val)
    (fun i:liveIndices E.val=>r.P i.val.val)
    W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂ (primaryOrdinaryPrefix r G L B E)

/-- The actual native second fixed arm after full G/L-primary allocation is
literally the H8 physical source with independently retained original heights
r.t₁+v and r.t₂+v, original ordinary prefixes d_j B_j E_j, full exceptional
puncture R*G*L, and the actual remaining supplying-prime labels. -/
theorem coloredPrimaryCanonicalSource_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id) (hG : G≠0) (hL : L≠0)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) (v : ℝ) :
    coloredPrimaryCanonicalSource r D ω₁ ω₂ G L B E (shiftedSlotCoefficient r v)
      (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v)=
      coloredPrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v := by
  rw [shiftedProfile₁_eq_actual r ha hb v,shiftedProfile₂_eq_actual r ha hb v]
  unfold coloredPrimaryCanonicalSource coloredPrimaryPhysicalSource
  dsimp only
  have hh := coloredCanonicalSource_eq_fixedCubePhysical (ι:=liveIndices E.val) D ω₁ ω₂ (actualProfile₁ r ha hb v) (actualProfile₂ r ha hb v)
    r.S r.H ((r.R*G)*L) (mul_ne_zero (mul_ne_zero r.hR hG) hL)
    (fun i:liveIndices E.val=>r.pool i.val.val)
    (fun i I hI=>(r.hp i.val.val I hI).ne_zero)
    (fun i:liveIndices E.val=>shiftedSlotCoefficient r v i.val.val)
    (fun i:liveIndices E.val=>r.Wslot i.val.val)
    (fun i:liveIndices E.val=>r.P i.val.val)
    b r.X₁ r.X₂ r.Y₁ r.Y₂ (primaryOrdinaryPrefix r G L B E)
    ⟨mul_ne_zero (commonLiveD_ne r G B).1 (fullPrimaryAlloc_ne r G B L E _),
      mul_ne_zero (commonLiveD_ne r G B).2 (fullPrimaryAlloc_ne r G B L E _)⟩
    le_rfl le_rfl (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)
    (r.hL.trans_le r.hY₁) (r.hL.trans_le r.hY₂)
  convert hh using 1
  congr 1
  ext p
  simp only [Finset.mem_univ]

#print axioms coloredPrimaryCanonicalSource_eq_physical
end
end QRH.Cycle092.FixedCubeGauss
