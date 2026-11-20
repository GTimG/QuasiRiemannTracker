/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite native GData bank, chosen before all actual allocations,
selected slot subsets, Kc hits and physical frame rows. -/
import Candidate.C092.transport.ColoredGaussFrameProviderOriginalFrame
import Candidate.C092.transport.FirstStageModulus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily QRH.Cycle092.ColoredGaussFrameProvider
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

def frameData (N n:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
    (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base:Character)(Q:Id)(hQ:Q ≤ rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
    (hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ base.modulus) : GData 3 where
  N:=n
  rayM:=rayM
  Hray:=Hr
  hH:=hHr
  W:=W
  hW:=hW
  hWs:=hWs
  bΦ:=2
  hbΦ:=le_rfl
  η₀:=base
  Q:=Q
  hQ:=hQ
  hQ0:=by simpa only [internalQ,inf_eq_left.mpr hQbase] using hQ0
  hQt:=by simpa only [internalQ,inf_eq_left.mpr hQbase] using hQt
  hQ72:=by simpa only [internalQ,inf_eq_left.mpr hQbase] using hQ72
  Holes:=2*N
  a:=1/4
  b:=9/4
  Lcap:=8
  Cap:=16
  Bmask:=24
  ha:=le_rfl
  hb1:=by norm_num
  hb:=le_rfl
  hLcap:=by norm_num
  hLL:=by norm_num
  hCap:=by norm_num
  hCapb:=by norm_num
  hBmask:=by norm_num

/-- Slot counts are the only variable parameter of this early bank. -/
theorem frameData_withSlots (N n k:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
    (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base:Character)(Q:Id)(hQ:Q ≤ rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
    (hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ base.modulus) :
    withSlots (frameData N n rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase) k =
      frameData N k rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase := rfl

theorem remaining_slots_le {ι:Type} [Fintype ι] {a b:ℝ}
    (s:Source ι a b)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val))
    (N:ℕ)(hN:Fintype.card ι ≤ N) : Fintype.card (Rest J) ≤ N := by
  apply (Fintype.card_le_of_injective (fun j:Rest J=>j.val.val) ?_).trans hN
  intro x y h
  exact Subtype.ext (Subtype.ext h)

def frameIndex {ι:Type} [Fintype ι] {a b:ℝ}
    (s:Source ι a b)(G:Id)(B:actualAllocations (tuplePools s) G)(J:Finset (liveIndices B.val))
    (N:ℕ)(hN:Fintype.card ι ≤ N) : Fin (N+1) :=
  ⟨Fintype.card (Rest J),Nat.lt_succ_of_le (remaining_slots_le s G B J N hN)⟩

/-- Actual R and active-column caps pay the native Bmask exactly. -/
theorem actual_mask_budget {Z R X:ℝ}(hZ:0<Z)(hR:0 ≤ R)(hX:0 ≤ X)
    (hRcap:R ≤ Z^(8:ℝ))(hXcap:X ≤ Z^(8:ℝ)) : R*X^2 ≤ Z^(24:ℝ) := by
  calc
    _ ≤ Z^(8:ℝ)*(Z^(8:ℝ))^2:=mul_le_mul hRcap (pow_le_pow_left₀ hX hXcap 2) (sq_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^(24:ℝ):=by rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ];norm_num

#print axioms frameData_withSlots
#print axioms remaining_slots_le
#print axioms actual_mask_budget
end
end QRH.Cycle092.ActualStageFrameBudget
