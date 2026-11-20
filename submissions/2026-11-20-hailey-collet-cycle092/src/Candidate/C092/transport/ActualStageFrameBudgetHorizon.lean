/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform positive-error payment for genuine allocation counts and the
corrected native H.25 label scalar, before live source and row data. -/
import Candidate.C092.transport.PairedRetainedBudgetPay
import Candidate.C092.transport.ColoredSelectionAverageSubpower
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstMixedAllowance
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedOriginalTail
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.PairedRetainedBudget
local notation "Id"=>Ideal HeckeFamily.O

def labelConstant (N:ℕ) (K Ca Cm Cfee:ℝ) : ℝ :=
  Ca*((K^N)^2*(pcMass*(K^N)^2*(256:ℝ)^N)*((2:ℝ)^N*Cm)*
    ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*Cfee*(4:ℝ)^N)

/-- All source-independent factors occur once; the three real subpower
inputs are the allocation square count, selected image count and frame fee. -/
theorem label_scalar_subpower {ι:Type} [Fintype ι] (s:Source ι (1/4) (9/4))
    (G:Id)(N:ℕ)(K Ca Cm Cfee A Z δ Mc Kl:ℝ)
    (hN:Fintype.card ι ≤ N)(hK:1 ≤ K)(hM:∀i,s.M i ≤ K)
    (hCa:0 ≤ Ca)(hCm:0 ≤ Cm)(hCfee:0 ≤ Cfee)(hA:0 ≤ A)(hZ:0<Z)
    (hMc:0 ≤ Mc)(hKl:0 ≤ Kl)
    (hcount:((actualAllocations (tuplePools s) G).card:ℝ)^2 ≤ Ca*Z^δ)
    (hm:Mc ≤ Cm*Z^δ)(hl:Kl ≤ Cfee*A*Z^δ) :
    labelScalar s G N Mc Kl ≤ labelConstant N K Ca Cm Cfee*A*Z^(3*δ) := by
  have hpc:=pcMass_nonneg
  have hprod0:0 ≤ ∏i,s.M i:=Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  have hprod:(∏i,s.M i) ≤ K^N:=by
    calc
      _ ≤ ∏_i:ι,K:=Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.hM i)) (fun i _=>hM i)
      _=K^(Fintype.card ι):=by simp
      _ ≤ K^N:=pow_le_pow_right₀ hK hN
  have h4:(4:ℝ)^(Fintype.card ι) ≤ 4^N:=pow_le_pow_right₀ (by norm_num) hN
  have hinner:
      (∏i,s.M i)^2*(pcMass*(∏i,s.M i)^2*(256:ℝ)^N)*((2:ℝ)^N*Mc)*
        ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*Kl*(4:ℝ)^(Fintype.card ι) ≤
      (K^N)^2*(pcMass*(K^N)^2*(256:ℝ)^N)*((2:ℝ)^N*(Cm*Z^δ))*
        ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ))*(Cfee*A*Z^δ)*(4:ℝ)^N:=by
    gcongr
  unfold labelScalar
  apply (mul_le_mul hcount hinner (by positivity) (by positivity)).trans_eq
  rw [show Z^(3*δ)=Z^δ*Z^δ*Z^δ by rw [←Real.rpow_add hZ,←Real.rpow_add hZ];congr 1;ring]
  unfold labelConstant
  ring

/-- Genuine allocation square counts at the actual root common cap Z^8;
one fixed coefficient works for every source type of cardinality at most N. -/
theorem allocation_square_subpower (N:ℕ)(δ:ℝ)(hδ:0<δ) :
    ∃Ca:ℝ,0<Ca ∧ ∀Z:ℝ,1<Z →
    ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N →
    ∀G:Id,G≠0 → (G.absNorm:ℝ) ≤ Z^(8:ℝ) →
      ((actualAllocations (tuplePools s) G).card:ℝ)^2 ≤ Ca*Z^δ := by
  obtain ⟨Ca,hCa,hcount⟩:=MixedSourceAssembly.genuine_count_squared (N+2) (δ/8) (by linarith)
  refine ⟨Ca,hCa,?_⟩
  intro Z hZ ι inst s hN G hG hGcap
  have hc:=QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.card_sq_le Ca (δ/8) Z (by linarith) hZ N
    hN s G hG hGcap hcount hCa.le
  simpa only [Finset.card_univ,Fintype.card_coe,show 8*(δ/8)=δ by ring] using hc

/-- The positive final error absorbs every fixed finite factor, uniformly
before live source, allocation, actual mark response or row data. -/
theorem eventual_label_payment (N:ℕ)(K Cm Cfee δ loss share:ℝ)
    (hK:1 ≤ K)(hCm:0 ≤ Cm)(hCfee:0 ≤ Cfee)(hδ:0<δ)(hgap:3*δ<loss)(hshare:0<share) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N → (∀i,s.M i ≤ K) →
    ∀G opp:Id,G≠0 → (G.absNorm:ℝ) ≤ Z^(8:ℝ) →
    ∀A Mc Kl:ℝ,0 ≤ A → 0 ≤ Mc → 0 ≤ Kl → Mc ≤ Cm*Z^δ → Kl ≤ Cfee*A*Z^δ →
      labelScalar s G N Mc Kl ≤ share*A*Z^(allowance G opp Z)*Z^loss := by
  obtain ⟨Ca,hCa,hcount⟩:=allocation_square_subpower N δ hδ
  let C:=labelConstant N K Ca Cm Cfee
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : 0<loss-3*δ)).eventually_ge_atTop (C/share)] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro ι inst s hN hM G opp hG hGcap A Mc Kl hA hMc hKl hm hl
  have hz:=zero_lt_one.trans hZ
  have hp:C*Z^(3*δ) ≤ share*Z^loss:=by
    have h1:=mul_le_mul_of_nonneg_right ((div_le_iff₀ hshare).mp hc) (Real.rpow_nonneg hz.le (3*δ))
    have he:Z^(loss-3*δ)*Z^(3*δ)=Z^loss:=by rw [←Real.rpow_add hz];congr 1;ring
    calc
      _ ≤ share*Z^(loss-3*δ)*Z^(3*δ):=by convert h1 using 1 <;> ring
      _=share*Z^loss:=by rw [mul_assoc,he]
  have hh:=label_scalar_subpower s G N K Ca Cm Cfee A Z δ Mc Kl hN hK hM hCa.le hCm hCfee hA hz
    hMc hKl (hcount Z hZ ι s hN G hG hGcap) hm hl
  have hallow:1 ≤ Z^(allowance G opp Z):=Real.one_le_rpow hZ.le (allowance_nonneg _ _ _)
  have hpaid:=mul_le_mul_of_nonneg_right hp hA
  have ht:share*A*Z^loss ≤ share*A*Z^(allowance G opp Z)*Z^loss:=by
    have hh:=mul_le_mul_of_nonneg_left hallow (mul_nonneg hshare.le hA)
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hh) (Real.rpow_nonneg hz.le _)
  have hpaid':labelConstant N K Ca Cm Cfee*A*Z^(3*δ) ≤ share*A*Z^loss:=by
    convert hpaid using 1 <;> (try dsimp [C]) <;> ring
  exact hh.trans (hpaid'.trans ht)

#print axioms label_scalar_subpower
#print axioms allocation_square_subpower
#print axioms eventual_label_payment
end
end QRH.Cycle092.ActualStageFrameBudget
