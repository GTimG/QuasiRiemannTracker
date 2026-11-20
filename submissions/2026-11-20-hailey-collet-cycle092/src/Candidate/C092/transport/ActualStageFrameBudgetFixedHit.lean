/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Apply the genuine fixed native packet to its literal restored first hit.
The empty carrier is exact zero; the nonempty cutoff uses the true prefix volume. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedGlobal
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
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentSectorLocalization
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
local instance (priority := 2000) fixedHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
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
variable (η ω₁ ω₂:Character)(C₀ D₀:Id)(hC₀:Supported C₀)(E₀:Finset (CommonIndex C₀ D₀))
variable (χ₁ χ₂:RayCharacter)(F:FixedPair η C₀ D₀ hC₀ E₀ χ₁ χ₂)(P:SidePack η)
include hL in
/-- The packet comes from actual_fixed_global_bank. All remaining gates
are true first-label geometry and elementary scalar fees. The source/frame
are let-bound once to retain the exact dependent allocation dictionaries. -/
theorem fixed_selected_from_native_packet :
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
  ∀(ε εg δ ξ v:ℝ)
    (Jlocal Jglobal degree:ℕ)(Slocal controls:Finset (ℕ×ℕ))(Cg C Cfee Kslot:ℝ)
    (packet:FixedGlobalAt th η ω₁ ω₂ mesh ε εg δ Jlocal Slocal Cg Q C r.Z
      Jglobal degree controls Cfee Kslot)
    (hCfee:0 ≤ Cfee)(hMarks:RestoredRootSource.slotBound r.W r.hW r.hWs ≤ Kslot)
    (hside:P.base=F.left ∨ P.base=F.right)(hCs:P.Cs=G)
    (hCcap:(C₀.absNorm:ℝ) ≤ r.Z^(8:ℝ))(hGcap:(G.absNorm:ℝ) ≤ r.Z^(8:ℝ))
    (hK:0<K)(hWsel:0<ws)(hXcap:xcap ≤ r.Z^(8:ℝ))
    (err:ℝ)(hu:usel ≤ (QRH.SourceCertificate.u:ℝ))
    (hcol:(rs).colLog ≤ 9179599/10000000-cinv-usel+err)
    (hfill:1-6*usel ≤ commonH (rs)+err)(hH0:0 ≤ commonH (rs))(hH1:commonH (rs) ≤ 19/10)
    (hmin:max 0 (115/1000-cinv) ≤ Real.logb r.Z (max 1 (child).L)+err)
    (hfee:ε+3*mesh+Real.logb r.Z 2+(17/6)*err+εg/8 ≤ 3036/100000)
    (hk8:8 ≤ kr)(hk2:kr ≤ r.Z^(2:ℝ))(ht0:0 ≤ ts)(ht2:ts ≤ r.Z^(2:ℝ))(hξ:ξ ≤ 1)
    (hcut:32*((9/4:ℝ)^2*(2:ℝ)^Fintype.card (Rest Js))^2*r.Z^(ξ/2) ≤ r.Z^mesh)
    (ζ:RayCharacter),
    selectedPartTerm true s cover G B Js ω₁ ω₂ P.base 1 Q fixedBadMask v K r.Z ξ ζ ≤
      (Cfee*(r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree*r.Z^δ*
        sourceVolume (renorm rem)^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ))*(1+‖v‖)^(2*Jglobal) := by
  intro s cover G B Js K ws kr rem xcap ts child th rs usel cinv
  intro ε εg δ ξ v Jlocal Jglobal degree Slocal controls Cg C Cfee Kslot packet hCfee hMarks
    hside hCs hCcap hGcap hK hWsel hXcap err hu hcol hfill hH0 hH1 hmin hfee hk8 hk2 ht0 ht2 hξ hcut ζ

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
    have hpcap:=selected_prime_scale_cap M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g cover G B Js
    have hMark:∀i,(child).M i ≤ Kslot:=by
      intro i;rw [selected_mark_bound M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g cover G B Js i];exact hMarks
    have hQi:internalQ (th).Q (th).η₀=Q:=by
      change Q ⊓ r.η₀.modulus=Q
      exact inf_eq_left.mpr hQbase
    have hn:=packet.2 C₀ D₀ hC₀ E₀ χ₁ χ₂ F P ζ 1 child rs hside hCcap
      hfields.1 hfields.2.1 hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2.1 hfields.2.2.2.2.2.1
      hfields.2.2.2.2.2.2.1 hfields.2.2.2.2.2.2.2.1 hcan hfields.2.2.2.2.2.2.2.2.1 hCR
      hm.2.2.1 hm.1 hR hactivecap hpcap hQ0 hQt hQ72 hQi fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) v kr ts ξ xcap (9179599/10000000) cinv usel err
      le_rfl hu hcol hfill hH0 hH1 hmin hfee (by positivity) hpow hcut' hk8 hk2 ht0 ht2 hξ hXcap
      height hh hMark
    have hc:=selected_controls M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g controls cover G B Js
    have hp:=selected_profiles M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g cover G B Js
    have hV0:(rs).V₀=P.V:=rfl
    rw [hc,hp.2.2.1,hp.2.2.2,hvol,hV0] at hn
    unfold selectedPartTerm
    rw [←originalSelectedSource_grouped s (by norm_num) (by norm_num) cover G B Js ω₁ ω₂ true]
    simpa only [Real.norm_eq_abs] using hn
  · have he:RootColoredSeed.active rem (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂)=∅:=by
      rw [←selected_active_eq]
      exact Finset.not_nonempty_iff_eq_empty.mp hactive
    rw [selectedPartTerm_of_empty s cover G B Js ω₁ ω₂ P.base 1 Q fixedBadMask v K r.Z ξ ζ he true]
    positivity

#print axioms fixed_selected_from_native_packet
end
end QRH.Cycle092.ActualStageFrameBudget
