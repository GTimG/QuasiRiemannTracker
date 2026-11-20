/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Authentic fixed native packets and an independently supplied regular
metadata bank share one early degree, control and fixed physical fee. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedPackets
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.FixedFourierH15
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.FixedCubeGauss
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

def mergeJ {N:ℕ} (fixed regular:Fin (N+1)→ℕ) : FrameBank N→ℕ :=
  fun k=>if k.2 then fixed k.1 else regular k.1

def mergeDegree {N:ℕ} (fixed regularDegree:Fin (N+1)→ℕ) : FrameBank N→ℕ :=
  fun k=>if k.2 then 2*fixed k.1 else regularDegree k.1

def mergeControls {N:ℕ} (fixed regular:Fin (N+1)→Finset (ℕ×ℕ)) : FrameBank N→Finset (ℕ×ℕ) :=
  fun k=>if k.2 then fixed k.1 else regular k.1

def fixedNumber (Q:Id)(C:ℝ) : ℝ :=
  (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*C

/-- The native fixed packet has already discharged H15 and B0. Only the
regular bank's early numerical metadata enter this common bank; its
analytic physical estimate is supplied separately. -/
theorem fixed_bank_with_regular (N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
    (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base:Character)(Q:Id)(hQ:Q ≤ rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
    (hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ base.modulus)
    (η ω₁ ω₂:Character)(mesh ε εg δ:ℝ)
    (hmesh:0 < mesh)(hm1:mesh ≤ 1)(hε:0<ε)(hεg:0<εg)(hδ:0<δ)
    (K:ℝ)(hK:1 ≤ K)(jr dr:Fin (N+1)→ℕ)(Sr:Fin (N+1)→Finset (ℕ×ℕ)) :
    ∃jf:Fin (N+1)→ℕ,∃Sf:Fin (N+1)→Finset (ℕ×ℕ),∃Cg C:Fin (N+1)→ℝ,
    ∃Cfee:ℝ,0<Cfee ∧ (∀k,(0,0)∈Sf k ∧ 0 ≤ Cg k ∧ 0<C k) ∧
      (∀ᶠZ:ℝ in atTop,∀k:Fin (N+1),
        FixedPartAt (frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase)
          η ω₁ ω₂ mesh ε εg δ (jf k) (Sf k) (Cg k) Q (C k) Z) ∧
      ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N → (∀i,s.M i ≤ K) →
      ∀t₁ t₂ height:ℝ,0 ≤ height → s.t₁=t₁ → s.t₂=t₂ → ∀k:Fin (N+1),
        classLambda 1 (Cg k) 1
          (fixedNumber Q (C k)*fixedMarkCost s*(sourceControl (Sf k) s.W₁*sourceControl (Sf k) s.W₂)^2*
            (2+‖s.t₁‖+‖s.t₂‖)^(2*jf k)) (1/4) (jf k) ≤
          Cfee*(sourceControl (commonControls (mergeControls Sf Sr)) s.W₁*
            sourceControl (commonControls (mergeControls Sf Sr)) s.W₂)^2*
              (1+|t₁|+|t₂|+height)^(commonDegree (mergeJ jf jr) (mergeDegree jf dr)) := by
  obtain ⟨jf,Sf,Cg,C,hpacket,hZ⟩:=actual_fixed_bank N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
    η ω₁ ω₂ mesh ε εg δ hmesh hm1 hε hεg hδ
  let cg:FrameBank N→ℝ:=fun k=>if k.2 then Cg k.1 else 0
  let cn:FrameBank N→ℝ:=fun k=>if k.2 then fixedNumber Q (C k.1) else 0
  have hcg:∀k,0 ≤ cg k:=by intro k;dsimp [cg];split_ifs;exact (hpacket k.1).2.1;exact le_rfl
  have hcn:∀k,0 ≤ cn k:=by
    intro k;dsimp [cn];split_ifs
    · dsimp [fixedNumber];have:0 ≤ C k.1:=(hpacket k.1).2.2.le;positivity
    · exact le_rfl
  obtain ⟨Cfee,hCf,hfee⟩:=fixed_bank_fee N K hK (mergeJ jf jr) (mergeDegree jf dr)
    (mergeControls Sf Sr) cg cn hcg hcn
  refine ⟨jf,Sf,Cg,C,Cfee,hCf,hpacket,hZ,?_⟩
  intro ι inst s hN hM t₁ t₂ height hh ht₁ ht₂ k
  exact hfee ι s hN hM t₁ t₂ height hh ht₁ ht₂ (k,true)

#print axioms fixed_bank_with_regular
end
end QRH.Cycle092.ActualStageFrameBudget
