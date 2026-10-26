/- Copyright (c) 2026 Sil. Apache-2.0.
The actual SMALL finite supplier, including finite-ray mass, paid by the
shared rawSupplierCost before either Cauchy cardinality is summed.
All four analytic bounds are supplied internally.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallFirstBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallSupplierCost
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open OuterFreshSource OuterFreshSelectedWindow
open RepairedRootParameters RepairedRawContext RepairedFirstPoint RepairedCapEvent
open RepairedSmallPoint RepairedSmallAdmission RepairedSmallSupplier RepairedSmallMass
open RepairedSmallCommonProfile RepairedSmallFourShapes RepairedSmallShapeRawCost RepairedSmallFirstBudget
open RepairedRawSupplier RepairedSupplierSplit RepairedComponentRawCost
open CenteredMomentOriginalChildEnergy
open CenteredMomentFirstColumns
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

-- Exactly the first-live Point index; no instance for nested residual subtypes.
local instance (priority := 2000) {κ : Type u} [Fintype κ]
    {Wslot : ℝ→ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    {d : RootInput M H hH κ Wslot N Holes ε Z Kslot η η₀}
    (p : Point d) : DecidableEq p.Index := Classical.decEq _


theorem uniform_small_supplier_cost
    (Index : Type v) [Fintype Index] (RootSlot : Index→Type u) [∀k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀k,Fintype.card (RootSlot k)≤N) (ε : ℝ) (hε : 0<ε)
    (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot⊆Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1≤Kslot) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)
    (η η₀ : Character) (hQη₀ : Q≤η₀.modulus) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧ ∃C : ℝ,1≤C ∧
    ∀ᶠZ : ℝ in atTop,∀k : Index,
    ∀d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀p : Point d,∀u : Id,Squarefree u → (u.absNorm:ℝ)≤Z^(8:ℝ) →
    ∀L : Finset p.Index,¬p.large L → ∀x : activeFrozen (p.data hε u L),∀tp : ℝ,∀rows : Finset O,
      finiteSupplierEnergy p.source (by norm_num) u (p.selection hε) ⟨L,x⟩ p.tau tp p.scale rows≤
      (C*commonProfile d.root degree control d.t₀ d.V tp*geometryBudget p)*
        rawSupplierCost (p.data hε u L) x.val (residualSeed (p.data hε u L) x) := by
  obtain ⟨degree,control,h00,C,hC,hactual⟩:=uniform_small_point M H hH Index RootSlot N Holes hcard
    ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  refine ⟨degree,control,h00,256*C,by linarith,?_⟩
  filter_upwards [hactual] with Z hactual
  intro k d p u hu hucap L hsmall x tp rows
  let q:=p.data hε u L
  let r:=p.residual hε u L x.val
  let seed:=residualSeed q x
  have hz:=zero_lt_one.trans d.one_lt_Z
  have hK:0<p.scale:=Real.rpow_pos_of_pos hz _
  have hN:Fintype.card p.Index≤N:=
    (Fintype.card_le_of_injective (fun i : p.Index=>i.val) Subtype.val_injective).trans (hcard k)
  have hadmit:=actual_small_residual M H hH d hε p.label.val.1 u p.allocation L hsmall
  have hJ:q.J=∅:=hadmit.1
  have hx:= (Finset.mem_filter.mp x.property).2.2
  have hseed:seed≠0:=(residualSeed_squarefree q hu x).ne_zero
  have hsig:0≤sigmaFixed:=by unfold sigmaFixed; positivity
  have hprofile:=common_profile_nonneg d.root degree control d.t₀ d.V tp d.hV
  have hgeom:=budget_nonneg p
  have hcost:=rawSupplierCost_nonneg q (fun i=>zero_lt_one.trans_le (p.source.hP i)) x.val seed
  obtain ⟨σ,hσ,hheight,hfinite⟩:=empty_supplier_sigma q hJ x r (by norm_num)
    (residual_matches p.source (by norm_num) p.cover u L (p.selection hε L) x.val)
    (actual_frozen_supported p.source (by norm_num) u L (p.selection hε L) x) p.tau
  let E (ξ : RayCharacter):= (sourceGaussEnergy (sourceColumns r) (sourceCoefficient r (by norm_num) seed)
    (heightCoeff (σ ξ) tp) ballProfile p.scale).re
  let B:=C*commonProfile d.root degree control d.t₀ d.V tp*geometryBudget p*rawSupplierCost q x.val seed
  have hB:0≤B:=by dsimp only [B]; positivity
  have hfront (ξ : RayCharacter) : supplierFront q x.val*E ξ≤B := by
    have hmod:( (σ ξ).modulus.absNorm:ℝ)≤sigmaFixed*(p.tau.modulus.absNorm:ℝ)*
        ((frozenProduct q x.val).absNorm:ℝ) := by
      have hh : ((σ ξ).modulus.absNorm:ℝ)≤(p.tau.modulus.absNorm:ℝ)*
          ((ReferenceCubicCharacter.conductorConstant:ℝ)*((frozenProduct q x.val).absNorm:ℝ))*
            (Ideal.span {(12:O)}).absNorm := by exact_mod_cast hσ ξ
      apply hh.trans_eq
      unfold sigmaFixed
      ring
    -- Give each proved component the SAME q/r/seed atoms before adding.
    -- The supplier lemmas' statement lets are definitionally reduced here.
    have hn : supplierFront q x.val*nativeShape r (σ ξ) seed Z (nativeLoss N ε)≤
        nativeBudget p*rawSupplierCost q x.val seed :=
      native_shape_raw_cost p.source (by norm_num) p.cover u L (p.selection hε L) hJ
        x.val hx N hN seed hseed p.tau (σ ξ) sigmaFixed Z (nativeLoss N ε) hsig hz.le hmod
    have he : supplierFront q x.val*exceptionalShape r seed p.scale Z (exceptionalLoss N ε)≤
        exceptionalBudget p*rawSupplierCost q x.val seed :=
      exceptional_shape_raw_cost p.source (by norm_num) p.cover u L (p.selection hε L) hJ
        x.val seed p.scale Z (exceptionalLoss N ε) hK hz.le
    have hzero : supplierFront q x.val*zeroShape r seed p.scale Z (zeroLoss N ε)≤
        zeroBudget p*rawSupplierCost q x.val seed :=
      zero_shape_raw_cost p.source (by norm_num) p.cover u L (p.selection hε L) hJ
        x.val seed N hN p.scale Z (zeroLoss N ε) hK.le hz.le
    have ht : supplierFront q x.val*tailShape u Z 40≤
        tailBudget (Z:=Z)*rawSupplierCost q x.val seed :=
      tail_shape_raw_cost p.source (by norm_num) u L (p.selection hε L) hJ
        x.val hx seed hseed (residualSeed_spec q x) Z 40 hz.le
    have hs : supplierFront q x.val*
        fullShape r (σ ξ) u seed p.scale Z (nativeLoss N ε) (exceptionalLoss N ε) (zeroLoss N ε) 40≤
        geometryBudget p*rawSupplierCost q x.val seed := by
      calc
        _=supplierFront q x.val*zeroShape r seed p.scale Z (zeroLoss N ε)+
            supplierFront q x.val*nativeShape r (σ ξ) seed Z (nativeLoss N ε)+
            supplierFront q x.val*exceptionalShape r seed p.scale Z (exceptionalLoss N ε)+
            supplierFront q x.val*tailShape u Z 40 := by
          rw [fullShape]
          ring
        _≤zeroBudget p*rawSupplierCost q x.val seed+
            nativeBudget p*rawSupplierCost q x.val seed+
            exceptionalBudget p*rawSupplierCost q x.val seed+
            tailBudget (Z:=Z)*rawSupplierCost q x.val seed :=
          add_le_add (add_le_add (add_le_add hzero hn) he) ht
        _=geometryBudget p*rawSupplierCost q x.val seed := by
          rw [geometryBudget]
          ring
    have hgauss : E ξ≤C*commonProfile d.root degree control d.t₀ d.V tp*
        fullShape r (σ ξ) u seed p.scale Z (nativeLoss N ε) (exceptionalLoss N ε) (zeroLoss N ε) 40 := by
      have hpoint:=hactual k d p
      unfold RepairedSmallPoint.Result at hpoint
      have hg:=hpoint u hu hucap L hsmall x (σ ξ) (hσ ξ) tp
      unfold RepairedSmallPoint.GaussBound at hg
      exact hg
    have hegy:=mul_le_mul_of_nonneg_left hgauss (supplierFront_nonneg q x.val)
    calc
      _≤supplierFront q x.val*(C*commonProfile d.root degree control d.t₀ d.V tp*
          fullShape r (σ ξ) u seed p.scale Z (nativeLoss N ε) (exceptionalLoss N ε) (zeroLoss N ε) 40):=hegy
      _=(C*commonProfile d.root degree control d.t₀ d.V tp)*(supplierFront q x.val*
          fullShape r (σ ξ) u seed p.scale Z (nativeLoss N ε) (exceptionalLoss N ε) (zeroLoss N ε) 40):=by ring
      _≤(C*commonProfile d.root degree control d.t₀ d.V tp)*(geometryBudget p*rawSupplierCost q x.val seed):=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _=B:=by dsimp only [B]; ring
  have hrays:=ray_energy_bound (fun ξ=>supplierFront q x.val*E ξ) B hB hfront
  have hsum : ‖MixedSupplierFourthRow.frozenWeight q x.val‖^2*
      (256*∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ)=
      ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*(supplierFront q x.val*E ξ) := by
    simp only [supplierFront,empty_active_card_eq q hJ,Nat.cast_one,mul_one,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    apply Finset.sum_congr rfl
    intro ξ hξ
    ring
  calc
    _≤‖MixedSupplierFourthRow.frozenWeight q x.val‖^2*
        (256*∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*E ξ):=
      hfinite tp p.scale rows hK
    _≤256*B:=hsum.trans_le hrays
    _=_:=by dsimp only [B]; ring

end
end Candidate.FourthPower.RepairedSmallSupplierCost
