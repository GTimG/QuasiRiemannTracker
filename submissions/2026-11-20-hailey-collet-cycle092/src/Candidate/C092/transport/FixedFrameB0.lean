/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed series fits the actual native H.25 side budget. The selected
whole-slot product occurs exactly once; all finite prefactors stay visible. -/
import Candidate.C092.transport.FixedFrameSeam
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair Packet Packet.Grouped
open CenteredMomentCommonProfile QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFourierH15
namespace QRH.Cycle092.FixedFrameSeam
local notation "Id"=>Ideal HeckeFamily.O

theorem mark_cost_le {ι:Type} [Fintype ι] {a b:ℝ} (s:Source ι a b)
    (M:ℝ) (hM:1 ≤ M) (hs:∀i,s.M i ≤ M) :
    fixedMarkCost s ≤ ((2*M^2)^2*(256*M)^2)^(Fintype.card ι) := by
  have hn:∀i,0 ≤ s.M i:=fun i=>zero_le_one.trans (s.hM i)
  have h₁:(∏ i,2*(s.M i)^2) ≤ (2*M^2)^Fintype.card ι := by
    calc
      _ ≤ ∏ _i:ι,2*M^2 := Finset.prod_le_prod₀ (fun i _=>by positivity)
        (fun i _=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hn i) (hs i) _) (by norm_num))
      _ = _ := by simp
  have h₂:(∏ i,(256*s.M i)^2) ≤ ((256*M)^2)^Fintype.card ι := by
    calc
      _ ≤ ∏ _i:ι,(256*M)^2 := Finset.prod_le_prod₀ (fun i _=>sq_nonneg _)
        (fun i _=>pow_le_pow_left₀ (by have:=hn i;positivity) (mul_le_mul_of_nonneg_left (hs i) (by norm_num)) _)
      _ = _ := by simp
  unfold fixedMarkCost
  have hp:0 ≤ ∏i,2*(s.M i)^2 := Finset.prod_nonneg (fun _ _=>by positivity)
  calc
    _ ≤ ((2*M^2)^Fintype.card ι)^2*(((256*M)^2)^Fintype.card ι) :=
      mul_le_mul (pow_le_pow_left₀ hp h₁ _) h₂
        (Finset.prod_nonneg (fun _ _=>sq_nonneg _)) (sq_nonneg _)
    _ = _ := by
      rw [mul_pow ((2*M^2)^2) ((256*M)^2)]
      rw [←pow_mul (2*M^2),←pow_mul (2*M^2),Nat.mul_comm (Fintype.card ι) 2]

theorem native_budget {ι:Type} [Fintype ι] {L mesh Z:ℝ} {θ:GData L}
    (r:GSrc θ mesh Z) (Q:Id) (C Ct M K ε u' err εg t₁ t₂ v:ℝ) (J:ℕ)
    (S:Finset ι) (w:ι→ℝ) (hu:u'=∑i∈S,w i)
    (hc:0 ≤ C) (hm:0 ≤ M) (hfee:ε+3*mesh+Real.logb Z 2+(17/6)*err+εg/8 ≤ 3036/100000)
    (he:K ≤ (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
      (C*M*Ct^2*Z^ε*(1+‖t₁+v‖+‖t₂+v‖)^(2*J))*
      Z^(r.colLog+r.twistLog+u'-(3036/100000)+3*mesh+Real.logb Z 2+(17/6)*err+εg/8)) :
    K ≤ ((Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
      C*M*Ct^2*(2+‖t₁‖+‖t₂‖)^(2*J))*r.vol*
      ((Ideal.span {r.V₀}).absNorm:ℝ)*(∏i∈S,Z^(w i))*(1+‖v‖)^(2*J) := by
  let A:ℝ:=(Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*C*M*Ct^2
  have ha:0 ≤ A:=by dsimp [A];positivity
  have hZ:=zero_lt_one.trans r.hZ
  have hheight : 1+‖t₁+v‖+‖t₂+v‖ ≤ (2+‖t₁‖+‖t₂‖)*(1+‖v‖) := by
    nlinarith only [norm_add_le t₁ v,norm_add_le t₂ v,mul_nonneg (norm_nonneg t₁) (norm_nonneg v),mul_nonneg (norm_nonneg t₂) (norm_nonneg v)]
  have hp:=pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖t₁+v‖+‖t₂+v‖) hheight (2*J)
  rw [mul_pow] at hp
  let expo:=r.colLog+r.twistLog+u'-3036/100000+3*mesh+Real.logb Z 2+(17/6)*err+εg/8
  have hz : Z^ε*Z^expo ≤ r.vol*((Ideal.span {r.V₀}).absNorm:ℝ)*(∏i∈S,Z^(w i)) := by
    rw [←Real.rpow_add hZ,←Real.rpow_sum_of_pos hZ];rw [←hu]
    calc
      _ ≤ Z^(r.colLog+r.twistLog+u') := Real.rpow_le_rpow_of_exponent_le r.hZ.le (by dsimp [expo];linarith)
      _ = _ := by rw [Real.rpow_add hZ,Real.rpow_add hZ];unfold GSrc.colLog GSrc.twistLog
                  rw [Real.rpow_logb hZ r.hZ.ne' (r.vol_pos hZ),Real.rpow_logb hZ r.hZ.ne' (absNorm_span_pos _ r.hV₀)]
  apply he.trans
  calc
    _ = A*((1+‖t₁+v‖+‖t₂+v‖)^(2*J)*(Z^ε*Z^expo)) := by dsimp [A,expo];ring
    _ ≤ A*((((2+‖t₁‖+‖t₂‖)^(2*J))*(1+‖v‖)^(2*J))*(r.vol*((Ideal.span {r.V₀}).absNorm:ℝ)*(∏i∈S,Z^(w i)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp hz (by positivity) (by positivity)) ha
    _ = _ := by dsimp [A];ring

#print axioms native_budget
end QRH.Cycle092.FixedFrameSeam
