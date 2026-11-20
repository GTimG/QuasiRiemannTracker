/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual native regular Lambda shares the early finite profile/height bank.
No source-energy or averaged-price premise is used in this normalization. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedBank
import Candidate.C092.transport.PhysicalFrameAmplitude
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second
open QRH.Cycle092.PairedRetainedBudget

/-- One constant precedes every actual frame, source profile, independent
pitch and height. Native regular class constants remain finite early data. -/
theorem regular_bank_fee (N:ℕ) (jf jr dr:Fin (N+1)→ℕ)
    (Sf Sr:Fin (N+1)→Finset (ℕ×ℕ)) (Cg C:Fin (N+1)→ℝ)
    (hCg:∀k,0 ≤ Cg k) (hC:∀k,0 ≤ C k) :
    let D:=commonDegree (mergeJ jf jr) (mergeDegree jf dr)
    let Smax:=commonControls (mergeControls Sf Sr)
    ∃Cfee:ℝ,0<Cfee ∧ ∀k:Fin (N+1),∀{L mesh Z:ℝ}{θ:GData L},θ.a=1/4 →
      ∀(η:Character)(rs:GSrc θ mesh Z)(p:Profiles (1/4) (9/4))(t₁ t₂ height:ℝ),
      0 ≤ height → rs.Vf ≤ height → rs.t=t₁ → rs.t₁=t₁/(2*Real.pi) → rs.t₂=t₂/(2*Real.pi) →
      rs.W₁=p.profile 0 → rs.W₂=p.profile 1 →
      classLambda 1 (Cg k) 1 (C k*gAmp L θ mesh η Z rs (jr k) (Sr k)) θ.a (jr k) ≤
        Cfee*((p.control Smax)^2*(1+|t₁|+|t₂|+height)^D) := by
  intro D Smax
  let coef:Fin (N+1)→ℝ:=fun k=>
    ((Cg k*C k*windowHeightConstant (jr k))/(1/4:ℝ)^2)*(2:ℝ)^D
  have hc:∀k,0 ≤ coef k:=by
    intro k
    dsimp [coef]
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (hCg k) (hC k))
      (windowHeightConstant_nonneg _)) (by norm_num)) (by positivity)
  refine ⟨1+∑k,coef k,by have:=Finset.sum_nonneg (fun k (_:k∈Finset.univ)=>hc k);linarith,?_⟩
  intro k L mesh Z θ ha η rs p t₁ t₂ height hh hV ht ht₁ ht₂ hw₁ hw₂
  have hk:=(finite_bank_parameters N (mergeJ jf jr) (mergeDegree jf dr) (mergeControls Sf Sr)).2 (k,false)
  have hj:jr k ≤ D:=by
    have h:=hk.2.2.1
    simp [mergeJ] at h
    dsimp [D]
    omega
  have hs:Sr k⊆Smax:=by simpa [mergeControls] using hk.2.2.2
  have hamp:=PackedPrice.original_amplitude η rs (jr k) D hj (Sr k) Smax hs t₁ t₂ height
    hh hV ht ht₁ ht₂ hw₁ hw₂
  have hp:0 ≤ (p.control Smax)^2*(1+|t₁|+|t₂|+height)^D:=by positivity
  have hcoef:coef k ≤ 1+∑i,coef i:=by
    have h:=Finset.single_le_sum (fun i (_:i∈Finset.univ)=>hc i) (Finset.mem_univ k)
    linarith
  have hmul:=mul_le_mul_of_nonneg_left hamp
    (show 0 ≤ (Cg k*C k*windowHeightConstant (jr k))/(1/4:ℝ)^2 from
      div_nonneg (mul_nonneg (mul_nonneg (hCg k) (hC k)) (windowHeightConstant_nonneg _)) (by norm_num))
  rw [ha]
  calc
    _ ≤ coef k*((p.control Smax)^2*(1+|t₁|+|t₂|+height)^D) := by
      unfold classLambda
      dsimp [coef] at *
      convert hmul using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hp

#print axioms regular_bank_fee
end
end QRH.Cycle092.ActualStageFrameBudget
