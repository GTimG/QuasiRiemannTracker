/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine fixed physical theorem is normalized on the finite actual
slot-count bank, sharing only early regular metadata and original amplitudes. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedPrice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.Cycle092.PairedRetainedBudget
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- No fixed-side analytic hypothesis remains. Every native fixed packet,
class count and numerical fee is supplied by checked native theorems. The
regular bank is represented here only by its early degree/control metadata. -/
theorem actual_fixed_global_bank (N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
    (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base:Character)(Q:Id)(hQ:Q ≤ rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
    (hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ base.modulus)
    (η ω₁ ω₂:Character)(mesh ε εg δ:ℝ)
    (hmesh:0 < mesh)(hm1:mesh ≤ 1)(hε:0<ε)(hεg:0<εg)(hδ:0<δ)
    (K:ℝ)(hK:1 ≤ K)(jr dr:Fin (N+1)→ℕ)(Sr:Fin (N+1)→Finset (ℕ×ℕ)) :
    ∃jf:Fin (N+1)→ℕ,∃Sf:Fin (N+1)→Finset (ℕ×ℕ),∃Cg C:Fin (N+1)→ℝ,
    ∃Cfee:ℝ,0<Cfee ∧ (∀k,(0,0)∈Sf k ∧ 0 ≤ Cg k ∧ 0<C k) ∧
      ∀ᶠZ:ℝ in atTop,∀k:Fin (N+1),
        FixedGlobalAt (frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase)
          η ω₁ ω₂ mesh ε εg δ (jf k) (Sf k) (Cg k) Q (C k) Z
          (commonJ (mergeJ jf jr)) (commonDegree (mergeJ jf jr) (mergeDegree jf dr))
          (commonControls (mergeControls Sf Sr)) Cfee K := by
  obtain ⟨jf,Sf,Cg,C,Cfee,hCf,hdata,hpacket,hfee⟩:=fixed_bank_with_regular N rayM Hr hHr W hW hWs base Q
    hQ hQ0 hQt hQ72 hQbase η ω₁ ω₂ mesh ε εg δ hmesh hm1 hε hεg hδ K hK jr dr Sr
  refine ⟨jf,Sf,Cg,C,Cfee,hCf,hdata,?_⟩
  filter_upwards [hpacket] with Z hZ
  intro k
  apply fixed_global_of_packet _ η ω₁ ω₂ mesh ε εg δ (jf k) (Sf k) (Cg k) Q (C k) Z
    (commonJ (mergeJ jf jr)) (commonDegree (mergeJ jf jr) (mergeDegree jf dr))
    (commonControls (mergeControls Sf Sr)) Cfee K (hdata k).2.1 (hdata k).2.2.le hCf.le
    ((finite_bank_parameters N (mergeJ jf jr) (mergeDegree jf dr) (mergeControls Sf Sr)).2 (k,true)).1
    (hZ k)
  intro s hM height hh
  have hN:Fintype.card (Fin k.val) ≤ N:=by simpa only [Fintype.card_fin] using Nat.le_of_lt_succ k.isLt
  have hf:=hfee (Fin k.val) s hN hM s.t₁ s.t₂ height hh rfl rfl k
  simpa only [fixedNumber,Real.norm_eq_abs,frameData] using hf

#print axioms actual_fixed_global_bank
end
end QRH.Cycle092.ActualStageFrameBudget
