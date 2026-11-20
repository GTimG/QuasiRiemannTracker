/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine fixed and all-response regular suppliers share one finite
early bank before every live source, height and positive root fee. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedGlobal
import Candidate.C092.transport.ActualStageFrameBudgetRegularBank
import Candidate.C092.transport.RegularPhysicalClassBudgetAll
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile CenteredMomentDetectorPlainFiberSource
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.RegularFramePhysicalReturn
open QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.RegularPhysicalClassBudget QRH.Cycle092.WholeSlot
open QRH.Cycle090 QRH.Cycle092.Source QRH.SourceCertificate
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- The mesh bound precedes Slot, ray, colors and all positive root fees.
All source degrees and constants are chosen over a finite slot-count bank
before the live scale, class label, profile, height or actual first base. -/
theorem actual_native_bank (δ:ℝ) (hδ:0  <  δ) :
    ∃meshMax:ℝ,0  <  meshMax ∧ ∀mesh:ℝ,0  <  mesh → mesh  ≤  meshMax →
    ∀(N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
      (hHr:RayOrthogonality.globalUnits rayM   ≤   Hr)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
      (base:Character)(Q:Id)(hQ:Q   ≤   rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
      (hQ72:Q   ≤   Ideal.span {(72:O)})(hQbase:Q   ≤   base.modulus),
    let θ:=fun k:Fin (N+1)=>frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
    ∀(bPhi:ℝ)(hbPhi:2 ≤ bPhi)(hPhi:Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
      (hβ:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
      (n y:ℝ)(hy₀:sourceY0  ≤  y)(hy₁:y  ≤  sourceY)(hn:y  ≤  n)
      (η ω₁ ω₂:Character)(hQ₁:Q  ≤  ω₁.modulus)(hQ₂:Q  ≤  ω₂.modulus)
      (Dp:Fin (N+1)→ℕ)(Sp:Fin (N+1)→Finset (ℕ×ℕ))(Cp:Fin (N+1)→ℝ),
      (∀k,0  <  Cp k) →
      (∀k,∀j:DictIdx,∀ᶠ Z:ℝ in atTop,
        OrderedP2At (Fin k.val) rayM Hr hHr W n y mesh Z
          (anchors η j) base ω₁ ω₂ Q (Dp k) (Sp k) (Cp k)) →
    ∀Kslot:ℝ,1  ≤  Kslot →
    ∃jr:Fin (N+1)→ℕ,∃Sr:Fin (N+1)→Finset (ℕ×ℕ),∃Cr Cgr:Fin (N+1)→ℝ,
    ∃jf:Fin (N+1)→ℕ,∃Sf:Fin (N+1)→Finset (ℕ×ℕ),∃Cgf Cf:Fin (N+1)→ℝ,
    ∃Cfixed Cregular:ℝ,0 < Cfixed ∧ 0 < Cregular ∧
    let J:=commonJ (mergeJ jf jr)
    let D:=commonDegree (mergeJ jf jr) (mergeDegree jf jr)
    let Smax:=commonControls (mergeControls Sf Sr)
    (0,0)∈Smax ∧
    (∀k,0 < Cr k ∧ 0  ≤  Cgr k) ∧ (∀k,(0,0)∈Sf k ∧ 0  ≤  Cgf k ∧ 0 < Cf k) ∧
    (∀ᶠZ:ℝ in atTop,∀k:Fin (N+1),
      FixedGlobalAt (θ k) η ω₁ ω₂ mesh δ δ δ (jf k) (Sf k) (Cgf k) Q (Cf k) Z
        J D Smax Cfixed Kslot ∧
      (k.val=0 → PartWithFeeAt (θ k) mesh η ω₁ ω₂ 0 (19/10) δ δ (δ+δ)
        (jr k) (Sr k) (Cr k) (Cgr k) (exhaustedPrice (θ k) mesh δ hδ.le)
        (exhaustedCaps (θ k) mesh) Z) ∧
      (k.val≠0 → PartAt (θ k) mesh η ω₁ ω₂ 0 (19/10) δ δ
        (jr k) (Sr k) (Cr k) (Cgr k) (filledPrice (θ k) mesh) (filledCaps (θ k) mesh n y) Z)) ∧
    ∀k:Fin (N+1),∀{L mesh' Z:ℝ}{θ':GData L},θ'.a=1/4 →
      ∀(η':Character)(rs:GSrc θ' mesh' Z)(p:Profiles (1/4) (9/4))(t₁ t₂ height:ℝ),
      0  ≤  height → rs.Vf  ≤  height → rs.t=t₁ → rs.t₁=t₁/(2*Real.pi) → rs.t₂=t₂/(2*Real.pi) →
      rs.W₁=p.profile 0 → rs.W₂=p.profile 1 →
      classLambda 1 (Cgr k) 1 (Cr k*gAmp L θ' mesh' η' Z rs (jr k) (Sr k)) θ'.a (jr k)  ≤ 
        Cregular*((p.control Smax)^2*(1+|t₁|+|t₂|+height)^D) := by
  obtain ⟨mr,hmr,hregular⟩:=actual_regular_bank δ δ δ hδ hδ hδ
  refine ⟨min mr 1,lt_min hmr (by norm_num),?_⟩
  intro mesh hm hmm N rayM inst Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase θ
    bPhi hbPhi hPhi hβ n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂ Dp Sp Cp hCp hP2 Kslot hKslot
  obtain ⟨jr,Sr,Cr,Cgr,hreg,hregEv⟩:=hregular mesh hm (hmm.trans (min_le_left _ _)) N rayM Hr hHr
    W hW hWs base Q hQ hQ0 hQt hQ72 hQbase bPhi hbPhi hPhi hβ n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂
    Dp Sp Cp hCp hP2
  obtain ⟨jf,Sf,Cgf,Cf,Cfixed,hCfixed,hfix,hfixEv⟩:=actual_fixed_global_bank N rayM Hr hHr W hW hWs
    base Q hQ hQ0 hQt hQ72 hQbase η ω₁ ω₂ mesh δ δ δ hm (hmm.trans (min_le_right _ _))
    hδ hδ hδ Kslot hKslot jr jr Sr
  obtain ⟨Cregular,hCregular,hfee⟩:=regular_bank_fee N jf jr jr Sf Sr Cgr Cr
    (fun k=>(hreg k).2) (fun k=>(hreg k).1.le)
  refine ⟨jr,Sr,Cr,Cgr,jf,Sf,Cgf,Cf,Cfixed,Cregular,hCfixed,hCregular,?_,hreg,hfix,?_,hfee⟩
  · exact (finite_bank_parameters N (mergeJ jf jr) (mergeDegree jf jr) (mergeControls Sf Sr)).1
  · filter_upwards [hfixEv,hregEv] with Z hf hr
    intro k
    exact ⟨hf k,hr k⟩

#print axioms actual_native_bank
end
end QRH.Cycle092.ActualStageFrameBudget
