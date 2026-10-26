/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual squarefree ordinary allocation moments retain only the common radical. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.MaskedZero
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalSharpAllocation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
local notation "frozenCost"=>CenteredMomentCommonExceptionalCost.frozenProfile
variable {ι:Type*}[Fintype ι]
local instance maskedAllocationDecidable : DecidableEq ι:=Classical.decEq _

lemma ordinaryNorm_le_radical (s:Input ι)(X:Ideal O)(hX:X≠0)
    (B:actualAllocations s.pools X)(hB:ordinarySquarefree B.val):
    ordinaryNorm B.val≤((commonRadical X X).absNorm:ℝ):=by
  have hp:finiteTupleProduct B.val=X:=(Finset.mem_filter.mp B.property).2
  have hd:=plain_product_dvd_tuple B.val
  rw [hp] at hd
  have hr:=old_mask_dvd_commonRadical _ X X hB hX hX hd hd
  exact corrected_norm_mono_of_dvd _ _ (commonRadical_ne_zero X X) hr

theorem masked_ordinary_moment (s:Input ι)(X:Ideal O)(hX:X≠0)(α:ℝ)(hα:0≤α):
    (∑B:actualAllocations s.pools X,if ordinarySquarefree B.val then (ordinaryNorm B.val)^(2*α) else 0)≤
      ((actualAllocations s.pools X).card:ℝ)*((commonRadical X X).absNorm:ℝ)^(2*α):=by
  have he (B:actualAllocations s.pools X):
      (if ordinarySquarefree B.val then (ordinaryNorm B.val)^(2*α) else 0)≤
        ((commonRadical X X).absNorm:ℝ)^(2*α):=by
    split_ifs with hs
    · exact Real.rpow_le_rpow (zero_le_one.trans (ordinaryNorm_ge_one s X B))
        (ordinaryNorm_le_radical s X hX B hs) (by positivity)
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using
    Finset.sum_le_sum (s:=Finset.univ) (fun B _=>he B)

theorem masked_allocation_budget_moment (s:Input ι)(X R:Ideal O)(hX:X≠0)
    (S:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q C D seed:Ideal O)
    (U:Finset (CommonIndex C D))(Z ε εL α Lraw Cr Mrow C₀ K₀:ℝ)
    (hα:0≤α)(hZ:0≤Z)(hCr:0≤Cr)(hK₀:0≤K₀):
    allocationBudget s X R (fun B=>maskedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀)≤
      ((actualAllocations s.pools X).card:ℝ)*
        (∑B:actualAllocations s.pools X,if ordinarySquarefree B.val then (ordinaryNorm B.val)^(2*α) else 0)*
          ((frozenCost s)^2/(X.absNorm:ℝ)^2)*
            correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀:=by
  let E:=correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀
  have hb (B:actualAllocations s.pools X):
      ‖frozenCoefficient B X R s.ν s.W s.P‖^2*
        maskedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀≤
      (if ordinarySquarefree B.val then (ordinaryNorm B.val)^(2*α) else 0)*
        ((frozenCost s)^2/(X.absNorm:ℝ)^2)*E:=by
    by_cases hs:ordinarySquarefree B.val
    · rw [maskedAllocatedBudget,if_pos hs,if_pos hs]
      convert corrected_allocated_weighted_budget_sharp s X R hX B S W₁ W₂ Φ Q C D seed U
        Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀ using 1 <;> dsimp only [E] <;> ring
    · simp only [maskedAllocatedBudget,if_neg hs,mul_zero,zero_mul,le_refl]
  unfold allocationBudget
  calc
    _≤((actualAllocations s.pools X).card:ℝ)*∑B:actualAllocations s.pools X,
      (if ordinarySquarefree B.val then (ordinaryNorm B.val)^(2*α) else 0)*
        ((frozenCost s)^2/(X.absNorm:ℝ)^2)*E:=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hb B)) (Nat.cast_nonneg _)
    _=_:=by rw [←Finset.sum_mul,←Finset.sum_mul]; dsimp only [E]; ring

theorem masked_allocation_budget_radical (s:Input ι)(X R:Ideal O)(hX:X≠0)
    (S:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q C D seed:Ideal O)
    (U:Finset (CommonIndex C D))(Z ε εL α Lraw Cr Mrow C₀ K₀:ℝ)
    (hα:0≤α)(hZ:0≤Z)(hCr:0≤Cr)(hK₀:0≤K₀):
    allocationBudget s X R (fun B=>maskedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀)≤
      ((actualAllocations s.pools X).card:ℝ)^2*((commonRadical X X).absNorm:ℝ)^(2*α)*
        ((frozenCost s)^2/(X.absNorm:ℝ)^2)*
          correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀:=by
  have hE:=correctedExceptionalBudget_nonneg s S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hZ hCr hK₀
  have hm:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (masked_ordinary_moment s X hX α hα) (Nat.cast_nonneg (actualAllocations s.pools X).card))
      (div_nonneg (sq_nonneg (frozenCost s)) (sq_nonneg (X.absNorm:ℝ)))) hE
  apply (masked_allocation_budget_moment s X R hX S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀).trans
  convert hm using 1 <;> ring
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.ordinaryNorm_le_radical
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.masked_ordinary_moment
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.masked_allocation_budget_moment
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.masked_allocation_budget_radical
