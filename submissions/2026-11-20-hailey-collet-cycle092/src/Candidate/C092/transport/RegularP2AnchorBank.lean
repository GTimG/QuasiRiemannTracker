/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite early fixed anchor bank. The original coefficient presentations
remain in the physical input when the common source mesh is decreased. -/
import Candidate.C092.transport.RegularP2AllHeights
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open QRH.SilDensitySplit.CubeFree.Packet
open QRH.Cycle092.StrongPair
namespace QRH.Cycle092.RegularFramePhysicalReturn
local notation "O"=>HeckeFamily.O

theorem ordered_weaken (Slot:Type) [Fintype Slot] [DecidableEq Slot]
    (M:Ideal O) [NeZero M] (Hr:Subgroup (O⧸M)ˣ) (hHr:RayOrthogonality.globalUnits M ≤ Hr)
    (W:ℝ→ℂ) (n y m mesh U:ℝ) (hU:1<U) (hm:mesh ≤ m)
    (old base ω₁ ω₂:Character) (Q:Ideal O)
    (d D:ℕ) (hD:d ≤ D) (S S':Finset (ℕ×ℕ)) (hS:S⊆S') (C C':ℝ) (hc:0 ≤ C) (hC:C ≤ C')
    (src:OrderedP2At Slot M Hr hHr W n y m U old base ω₁ ω₂ Q d S C) :
    OrderedP2At Slot M Hr hHr W n y mesh U old base ω₁ ω₂ Q D S' C' := by
  intro V hV hV2 T θ w σ v tOld t1 t2 height hw hwm hσ hh ht hf hf1 hf2 hq p X1 X2 hx1 hx2 hc1 hc2
    rows hko hk1 hk2 hn hr1 hr2
  have h:=src V hV hV2 T θ w σ v tOld t1 t2 height hw (fun i=>(hwm i).trans hm) hσ hh ht hf hf1 hf2 hq
    p X1 X2 hx1 hx2 hc1 hc2 rows hko hk1 hk2 hn hr1 hr2
  have hp:p.control S ≤ p.control S' := by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hS) _) (Seminorm.le_def.mp (Finset.sup_mono hS) _)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hH:1 ≤ 1+|t1|+|t2|+height:=by linarith [abs_nonneg t1,abs_nonneg t2]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
  exact mul_le_mul (mul_le_mul hC (pow_le_pow_left₀ (p.control_nonneg _) hp _) (sq_nonneg _) (hc.trans hC))
    (pow_le_pow_right₀ hH hD) (pow_nonneg (zero_le_one.trans hH) _) (mul_nonneg (hc.trans hC) (sq_nonneg _))

theorem all_anchor_p2 (N:ℕ) (M:Ideal O) [NeZero M] (Hr:Subgroup (O⧸M)ˣ) (hHr:RayOrthogonality.globalUnits M ≤ Hr)
    (W:ℝ→ℂ) (n y m mesh:ℝ) (hm:mesh ≤ m) (η base ω₁ ω₂:Character) (Q:Ideal O)
    (src:∀ (k:Fin (N+1)) (j:DictIdx),∃d:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠ U:ℝ in atTop,
      OrderedP2At (Fin k.val) M Hr hHr W n y m U (anchors η j) base ω₁ ω₂ Q d S C) :
    ∃d:Fin (N+1)→ℕ,∃S:Fin (N+1)→Finset (ℕ×ℕ),∃C:Fin (N+1)→ℝ,
      (∀k,0<C k) ∧ ∀k,∀j:DictIdx,∀ᶠ U:ℝ in atTop,
      OrderedP2At (Fin k.val) M Hr hHr W n y mesh U (anchors η j) base ω₁ ω₂ Q (d k) (S k) (C k) := by
  classical
  choose d S C hc hs using src
  let dd:=fun k=>Finset.univ.sup (d k)
  let ss:=fun k=>(Finset.univ:Finset DictIdx).biUnion (S k)
  let cc:=fun k=>(1:ℝ)+∑j,C k j
  have hcp (k):0<cc k:=by
    have h:=Finset.sum_nonneg (s:=Finset.univ) (fun j _=>(hc k j).le)
    dsimp [cc];linarith
  refine ⟨dd,ss,cc,hcp,?_⟩
  intro k j
  filter_upwards [hs k j,eventually_gt_atTop (1:ℝ)] with U hu hU
  apply ordered_weaken _ M Hr hHr W n y m mesh U hU hm _ _ _ _ Q (d k j) (dd k) (Finset.le_sup (Finset.mem_univ _))
    _ _ (fun i hi=>Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hi⟩) _ _ (hc k j).le _ hu
  have h:=Finset.single_le_sum (s:=Finset.univ) (f:=C k) (fun l _=>(hc k l).le) (Finset.mem_univ j)
  dsimp [cc];linarith
#print axioms all_anchor_p2
end QRH.Cycle092.RegularFramePhysicalReturn
