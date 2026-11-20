/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Apply the genuine regular native packet to its literal restored first hit.
The empty carrier is exact zero; the nonempty cutoff uses the true prefix volume. -/
import Candidate.C092.transport.ActualStageFrameBudgetRegularBank
import Candidate.C092.transport.ActualStageFrameBudgetEmpty
import Candidate.C092.transport.ActualRootFrameHitAll
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily CenteredMomentSecondLocalization
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalNormCap MixedCompletedRows
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource CenteredMomentSecondWindowBudget MixedCompletedRows
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource CenteredMomentSecondWindowBudget
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup QRH.Cycle092.FixedCubeGauss
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.ColoredGaussFrameProvider
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.ActualRootFrameHit
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) regularHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type}[Fintype ι]
variable (N:ℕ)(M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (r:RestoredRootSource.Data M Hr ι)(hW:ContDiff ℝ ∞ r.W)(hL:r.Lcap=8)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(g:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
local notation "src"=>dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
local notation "cov"=>canonicalPairSource_original_enclosure M Hr hHr r _ _ _ _ t₁ t₂
  g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂
local notation "caps₄"=>divided_bank_caps M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
variable (mesh height:ℝ)(hwm:∀i,r.w i ≤ mesh)(hh:0 ≤ height)(hfreq:∀i,|r.freq i| ≤ height)
variable (hholes:∀i,(r.R₀ i).card ≤ 2*N)
variable (Q:Id)(hQ:Q ≤ M)(hQ0:Q≠0)(hQt:Q≠⊤)(hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ r.η₀.modulus)
variable (η ω₁ ω₂:Character)(P:SidePack η)
open QRH.Cycle092.RegularPhysicalClassBudget

include hL in
/-- Only genuine native regular packets and primitive scalar/constructor gates enter. -/
theorem regular_selected_from_native_packet :
  let s:=src
  let cover:=cov
  ∀(G:Id)(B:actualAllocations (tuplePools s) G)(Js:Finset (liveIndices B.val))(K:ℝ),
  let ws:=RawSides.selectionScaleQ s (by norm_num) cover G B Js
  let kr:=16*K*ws^4
  let rem:=restOf s (by norm_num) cover G B Js
  let xcap:=RawSides.residualCapQ rem
  let ts:=RootColoredSeed.secondCutoffQ xcap K ws
  let child:=originalSelectedSource s (by norm_num) cover G B Js
  let th:=frameData N (Fintype.card (Rest Js)) M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase
  let rs:GSrc th mesh r.Z:=bankFrame N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr)
  let usel:=∑j∈Js,r.w j.val
  let cinv:=Real.logb r.Z (((d.1.absNorm:ℝ)*d.2.absNorm)*(G.absNorm:ℝ))
  ∀(ε δfinite fee debit δPrice ξ v:ℝ)(Jlocal Jglobal degree:ℕ)
    (Slocal controls:Finset (ℕ×ℕ))(C Cg Cfee:ℝ)
    (price:∀U:ℝ,GSrc th mesh U→ℝ→ℝ)(caps:∀U:ℝ,GSrc th mesh U→Prop),
    PartWithFeeAt th mesh η ω₁ ω₂ 0 (19/10) ε δfinite fee Jlocal Slocal C Cg price caps r.Z →
    0 ≤ Cfee → Jlocal ≤ Jglobal →
    (classLambda 1 Cg 1 (C*gAmp 3 th mesh η r.Z rs Jlocal Slocal) th.a Jlocal ≤
      Cfee*((r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)) →
    P.Cs=G → (G.absNorm:ℝ) ≤ r.Z^(8:ℝ) →
    0<K → 0<ws → xcap ≤ r.Z^(8:ℝ) → 0 ≤ commonH rs → commonH rs ≤ 19/10 → caps r.Z rs →
    8 ≤ kr → kr ≤ r.Z^(2:ℝ) → 0 ≤ ts → ts ≤ r.Z^(2:ℝ) → ξ ≤ 1 →
    32*((9/4:ℝ)^2*(2:ℝ)^Fintype.card (Rest Js))^2*r.Z^(ξ/2) ≤ r.Z^mesh →
    δfinite+fee+debit ≤ δPrice → ∀w₀:ℝ,price r.Z rs w₀+ε ≤ usel+debit+fee → ∀ζ:RayCharacter,
    selectedPartTerm false s cover G B Js ω₁ ω₂ P.base 1 Q fixedBadMask v K r.Z ξ ζ ≤
      (Cfee*((r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*r.Z^δPrice*
        sourceVolume (renorm rem)^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ))*(1+‖v‖)^(2*Jglobal) := by
  intro s cover G B Js K ws kr rem xcap ts child th rs usel cinv ε δfinite fee debit δPrice ξ v
    Jlocal Jglobal degree Slocal controls C Cg Cfee price caps packet hCfee hJ hLambda hCs hGcap
    hK hWsel hXcap hH0 hH1 hcaps hk8 hk2 ht0 ht2 hξ hcut hprice w₀ hpaid ζ
  have hz:0<r.Z:=zero_lt_one.trans r.hZ
  have hc0:=divided_canonical M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
  rw [hL] at hc0
  have hm:=selected_masks M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g cover G B Js
  by_cases hactive:(RootColoredSeed.active child (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂)).Nonempty
  · have hfields:=bank_fields N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr)
    have hcan:=bank_canonical_self N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr) hc0
    have hvol:=bank_volume_rest N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr) hc0
    have hcut':=bank_frequency_cutoff N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr) hc0 (idealCoeff ω₁) (idealCoeff ω₂) hactive kr ξ
      (by positivity) rfl hcut
    have hpow:=bank_power_radius N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr) kr (by positivity) rfl
    have hCR:P.Cs∣(child).R:=by rw [hCs,hm.2.1]
    have hR:((child).R.absNorm:ℝ) ≤ r.Z^(8:ℝ):=by rw [hm.2.1];exact hGcap
    have hactivecap:∀I∈RootColoredSeed.active child (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂),
        (I.absNorm:ℝ) ≤ r.Z^(8:ℝ):=by
      apply selected_column_cap s (by norm_num) (by norm_num) cover G B Js (idealCoeff ω₁) (idealCoeff ω₂)
      exact (le_max_right 1 _).trans hXcap
    have hQi:internalQ (th).Q (th).η₀=Q:=by
      change Q ⊓ r.η₀.modulus=Q
      exact inf_eq_left.mpr hQbase
    have hn:=packet.2 P ζ 1 child rs
      hfields.1 hfields.2.1 hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2.1 hfields.2.2.2.2.2.1
      hfields.2.2.2.2.2.2.1 hfields.2.2.2.2.2.2.2.1 hcan hfields.2.2.2.2.2.2.2.2.1 hCR
      hm.1 (by change (24:ℝ) ≤ 24;norm_num) hR hactivecap hH0 hH1 hcaps Q fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) hQ72 hQi v kr ts ξ xcap w₀ (usel+debit)
      (by positivity) hpow hcut' hk8 hk2 ht0 ht2 hξ hXcap hpaid
    have hpoly:(1+‖v‖)^(2*Jlocal) ≤ (1+‖v‖)^(2*Jglobal):=
      pow_le_pow_right₀ (by have:=norm_nonneg v;linarith) (Nat.mul_le_mul_left 2 hJ)
    have hexp:r.Z^(δfinite+fee+debit) ≤ r.Z^δPrice:=
      Real.rpow_le_rpow_of_exponent_le r.hZ.le hprice
    have hV0:(rs).V₀=P.V:=rfl
    have hbound:
        RootColoredSeed.groupedPartTerms false child (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂)
          (childCharacter P.base ζ) 1 Q fixedBadMask v kr ts r.Z ξ xcap ≤
          (Cfee*((r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*r.Z^δPrice*
            (rs).vol^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ))*(1+‖v‖)^(2*Jglobal):=by
      apply hn.trans
      rw [hV0]
      calc
        _ ≤ (Cfee*((r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*r.Z^(δfinite+fee)*
            (rs).vol^2*r.Z^(usel+debit)*((Ideal.span {P.V}).absNorm:ℝ))*(1+‖v‖)^(2*Jglobal) := by
          gcongr
        _ = (Cfee*((r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*r.Z^(δfinite+fee+debit)*
            (rs).vol^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ))*(1+‖v‖)^(2*Jglobal) := by
          simp only [Real.rpow_add hz]
          ring
        _ ≤ _ := by gcongr
    rw [hvol] at hbound
    unfold selectedPartTerm
    rw [←originalSelectedSource_grouped s (by norm_num) (by norm_num) cover G B Js ω₁ ω₂ false]
    exact hbound
  · have he:RootColoredSeed.active rem (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂)=∅:=by
      rw [←selected_active_eq]
      exact Finset.not_nonempty_iff_eq_empty.mp hactive
    rw [selectedPartTerm_of_empty s cover G B Js ω₁ ω₂ P.base 1 Q fixedBadMask v K r.Z ξ ζ he false]
    positivity

#print axioms regular_selected_from_native_packet
end
end QRH.Cycle092.ActualStageFrameBudget
