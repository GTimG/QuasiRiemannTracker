/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite bank of all-response regular physical prices. Filled
children use original P2; slot exhaustion uses the actual unmarked source. -/
import Candidate.C092.transport.ActualStageFrameBudgetRegularFee
import Candidate.C092.transport.ActualStageFrameBudgetRadial
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
open QRH.Cycle092.RegularPhysicalClassBudget QRH.Cycle092.WholeSlot
open QRH.Cycle090 QRH.Cycle092.Source QRH.SourceCertificate
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- The mesh bound precedes Slot, ray, colors and all positive root fees.
All source degrees and constants are chosen over a finite slot-count bank
before the live scale, class label, profile, height or actual first base. -/
theorem actual_regular_bank (ε δnative δfinite:ℝ) (hε:0 < ε) (hδn:0 < δnative) (hδf:0 < δfinite) :
    ∃meshMax:ℝ,0 < meshMax ∧ ∀mesh:ℝ,0 < mesh → mesh ≤ meshMax →
    ∀(N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
      (hHr:RayOrthogonality.globalUnits rayM  ≤  Hr)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
      (base:Character)(Q:Id)(hQ:Q  ≤  rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
      (hQ72:Q  ≤  Ideal.span {(72:O)})(hQbase:Q  ≤  base.modulus),
    let θ:=fun k:Fin (N+1)=>frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
    ∀(bPhi:ℝ)(hbPhi:2 ≤ bPhi)(hPhi:Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
      (hβ:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
      (n y:ℝ)(hy₀:sourceY0 ≤ y)(hy₁:y ≤ sourceY)(hn:y ≤ n)
      (η ω₁ ω₂:Character)(hQ₁:Q ≤ ω₁.modulus)(hQ₂:Q ≤ ω₂.modulus)
      (Dp:Fin (N+1)→ℕ)(Sp:Fin (N+1)→Finset (ℕ×ℕ))(Cp:Fin (N+1)→ℝ),
      (∀k,0 < Cp k) →
      (∀k,∀j:DictIdx,∀ᶠ Z:ℝ in atTop,
        OrderedP2At (Fin k.val) rayM Hr hHr W n y mesh Z
          (anchors η j) base ω₁ ω₂ Q (Dp k) (Sp k) (Cp k)) →
    ∃jr:Fin (N+1)→ℕ,∃Sr:Fin (N+1)→Finset (ℕ×ℕ),∃C Cg:Fin (N+1)→ℝ,
      (∀k,0 < C k ∧ 0 ≤ Cg k) ∧ ∀ᶠ Z:ℝ in atTop,∀k:Fin (N+1),
        (k.val=0 → PartWithFeeAt (θ k) mesh η ω₁ ω₂ 0 (19/10) ε δfinite (δnative+ε)
          (jr k) (Sr k) (C k) (Cg k) (exhaustedPrice (θ k) mesh δnative hδn.le)
          (exhaustedCaps (θ k) mesh) Z) ∧
        (k.val≠0 → PartAt (θ k) mesh η ω₁ ω₂ 0 (19/10) ε δfinite
          (jr k) (Sr k) (C k) (Cg k) (filledPrice (θ k) mesh) (filledCaps (θ k) mesh n y) Z) := by
  obtain ⟨mf,hmf,hfilled⟩:=filled_part_of_p2 (L:=3) 0 (19/10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ε δfinite hε hδf
  obtain ⟨me,hme,hexhausted⟩:=exhausted_part (L:=3) 0 (19/10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ε δnative δfinite hε hδn hδf
  refine ⟨min mf me,lt_min hmf hme,?_⟩
  intro mesh hm hmm N rayM inst Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase θ
    bPhi hbPhi hPhi hβ n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂ Dp Sp Cp hCp hP2
  have hf(k:Fin (N+1)):=hfilled mesh hm (hmm.trans (min_le_left _ _)) (withRadialCap (θ k) bPhi hbPhi) hβ hPhi
    n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂ (Dp k) (Sp k) (Cp k) (hCp k) (hP2 k)
  choose jf Sf Cf Cgf hCf hCgf hfevRad using hf
  have hfev(k:Fin (N+1)) : ∀ᶠ Z:ℝ in atTop,
      PartAt (θ k) mesh η ω₁ ω₂ 0 (19/10) ε δfinite (jf k) (Sf k) (Cf k) (Cgf k)
        (filledPrice (θ k) mesh) (filledCaps (θ k) mesh n y) Z := by
    filter_upwards [hfevRad k] with Z hz
    exact part_of_radial_packet (θ k) bPhi hbPhi η ω₁ ω₂ 0 (19/10) ε δfinite
      (jf k) (Sf k) (Cf k) (Cgf k) _ _ _ _ (fun _ _ _=>rfl) (fun _ _ h=>h) hz
  let k0:Fin (N+1):=⟨0,Nat.zero_lt_succ N⟩
  obtain ⟨je,Se,Ce,Cge,hCe,hCge,heevRad⟩:=hexhausted mesh hm (hmm.trans (min_le_right _ _))
    (withRadialCap (θ k0) bPhi hbPhi) rfl hβ hPhi η ω₁ ω₂ hQ₁ hQ₂
  have heev : ∀ᶠ Z:ℝ in atTop,
      PartWithFeeAt (θ k0) mesh η ω₁ ω₂ 0 (19/10) ε δfinite (δnative+ε)
        je Se Ce Cge (exhaustedPrice (θ k0) mesh δnative hδn.le) (exhaustedCaps (θ k0) mesh) Z := by
    filter_upwards [heevRad] with Z hz
    exact part_fee_of_radial_packet (θ k0) bPhi hbPhi η ω₁ ω₂ 0 (19/10) ε δfinite (δnative+ε)
      je Se Ce Cge _ _ _ _ (fun _ _ _=>rfl) (fun _ _ h=>h) hz
  let jr:=fun k:Fin (N+1)=>if k.val=0 then je else jf k
  let Sr:=fun k:Fin (N+1)=>if k.val=0 then Se else Sf k
  let C:=fun k:Fin (N+1)=>if k.val=0 then Ce else Cf k
  let Cg:=fun k:Fin (N+1)=>if k.val=0 then Cge else Cgf k
  refine ⟨jr,Sr,C,Cg,?_,?_⟩
  · intro k
    by_cases hk:k.val=0
    · dsimp only [C,Cg]
      rw [if_pos hk,if_pos hk]
      exact ⟨hCe,hCge⟩
    · dsimp only [C,Cg]
      rw [if_neg hk,if_neg hk]
      exact ⟨hCf k,hCgf k⟩
  · filter_upwards [Filter.eventually_all.mpr hfev,heev] with Z hfz hez
    intro k
    by_cases hk:k.val=0
    · have hk0:k=k0:=Fin.ext hk
      subst k
      constructor
      · intro _
        simpa only [jr,Sr,C,Cg,k0,if_pos rfl] using hez
      · intro h;exact (h rfl).elim
    · constructor
      · intro h;exact (hk h).elim
      · intro _
        simpa only [jr,Sr,C,Cg,if_neg hk] using hfz k

#print axioms actual_regular_bank
end
end QRH.Cycle092.ActualStageFrameBudget
