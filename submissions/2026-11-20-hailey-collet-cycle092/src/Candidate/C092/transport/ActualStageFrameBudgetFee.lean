/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The authentic fixed-frame mark/profile/height fee is bounded uniformly
across the finite native frame bank before the live physical source. -/
import Candidate.C092.transport.ActualStageFrameBudgetBank
import Candidate.C092.transport.FixedFrameB0
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.FixedCubeGauss

/-- Every actual survivor keeps the same fixed marked majorant. The bound
also covers zero slots and every smaller restored source cardinality. -/
theorem fixed_mark_cost_uniform {ι:Type}[Fintype ι]{a b:ℝ}(s:Source ι a b)
    (N:ℕ)(hN:Fintype.card ι ≤ N)(K:ℝ)(hK:1 ≤ K)(hM:∀i,s.M i ≤ K) :
    fixedMarkCost s ≤ ((2*K^2)^2*(256*K)^2)^N := by
  apply (QRH.Cycle092.FixedFrameSeam.mark_cost_le s K hK hM).trans
  apply pow_le_pow_right₀ _ hN
  have h1:1 ≤ (2*K^2)^2:=one_le_pow₀ (by nlinarith [sq_nonneg K])
  have h2:1 ≤ (256*K)^2:=one_le_pow₀ (by linarith)
  exact one_le_mul_of_one_le_of_one_le h1 h2

/-- J, degree and controls were already fixed from the finite bank. The
constant is now chosen before all profiles, pitches, sources and Kc hits. -/
theorem fixed_bank_fee (N:ℕ)(K:ℝ)(hK:1 ≤ K)
    (j degree:FrameBank N→ℕ)(S:FrameBank N→Finset (ℕ×ℕ))
    (Cg Cnum:FrameBank N→ℝ)(hg:∀k,0 ≤ Cg k)(hc:∀k,0 ≤ Cnum k) :
    ∃Cfee:ℝ,0<Cfee ∧ ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),
      Fintype.card ι ≤ N → (∀i,s.M i ≤ K) → ∀t₁ t₂ height:ℝ,0 ≤ height →
      s.t₁=t₁ → s.t₂=t₂ → ∀k:FrameBank N,
      classLambda 1 (Cg k) 1
        (Cnum k*fixedMarkCost s*(sourceControl (S k) s.W₁*sourceControl (S k) s.W₂)^2*
          (2+‖s.t₁‖+‖s.t₂‖)^(2*j k)) (1/4) (j k) ≤
        Cfee*(sourceControl (commonControls S) s.W₁*sourceControl (commonControls S) s.W₂)^2*
          (1+|t₁|+|t₂|+height)^(commonDegree j degree) := by
  let Mk:=((2*K^2)^2*(256*K)^2)^N
  let coeff:=fun k:FrameBank N=>16*Cg k*Cnum k*Mk*windowHeightConstant (j k)*(2:ℝ)^(2*commonJ j)
  have hcoeff:∀k,0 ≤ coeff k:=by
    intro k
    dsimp [coeff,Mk]
    have:=windowHeightConstant_nonneg (j k)
    have:=hg k
    have:=hc k
    positivity
  let Cfee:=(∑k:FrameBank N,coeff k)+1
  have hCfee:0<Cfee:=by
    have:=Finset.sum_nonneg (fun k (_:k∈Finset.univ)=>hcoeff k)
    dsimp [Cfee]
    linarith
  refine ⟨Cfee,hCfee,?_⟩
  intro ι inst s hN hM t₁ t₂ height hh ht₁ ht₂ k
  have hlocal:=(bank_profile_height N j degree S k s.W₁ s.W₂ t₁ t₂ height hh)
  have hmark:=fixed_mark_cost_uniform s N hN K hK hM
  have hmk:=fixedMarkCost_nonneg s
  have hctl:0 ≤ sourceControl (S k) s.W₁*sourceControl (S k) s.W₂:=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hcommon:0 ≤ (sourceControl (commonControls S) s.W₁*sourceControl (commonControls S) s.W₂)^2*
    (1+|t₁|+|t₂|+height)^(commonDegree j degree):=by positivity
  have hmkprofile:=mul_le_mul hmark hlocal (by positivity) (by positivity)
  have hw:=windowHeightConstant_nonneg (j k)
  have hscale:0 ≤ 16*Cg k*Cnum k*windowHeightConstant (j k):=by
    have:=hg k;have:=hc k;positivity
  have hscaled:=mul_le_mul_of_nonneg_left hmkprofile hscale
  have hcoeffle:coeff k ≤ Cfee:=by
    have hsum:=Finset.single_le_sum (fun k' _=>hcoeff k') (Finset.mem_univ k)
    dsimp [Cfee];linarith
  have hlast:=mul_le_mul_of_nonneg_right hcoeffle hcommon
  rw [ht₁,ht₂]
  exact (le_of_eq (by unfold classLambda;ring)).trans (hscaled.trans
    ((le_of_eq (by dsimp [coeff];ring)).trans (hlast.trans_eq (by ring))))

#print axioms fixed_mark_cost_uniform
#print axioms fixed_bank_fee
end
end QRH.Cycle092.ActualStageFrameBudget
