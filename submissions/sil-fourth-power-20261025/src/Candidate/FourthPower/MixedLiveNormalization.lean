/- Copyright (c) 2026 Sil. Apache-2.0.
Return the centered live row to the original source normalization.
The scalar identities are independent of the literal restriction inside
the row; the existing frozen-coefficient cost is reused unchanged.
-/
import Candidate.FourthPower.MixedLiveRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRawCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedLiveNormalization
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def normalization (T : ℝ) (P : ι→ℝ) : ℂ :=
  (Real.sqrt T:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹

theorem normalization_sq (T : ℝ) (hT : 0<T) (P : ι→ℝ) (hP : ∀i,0<P i) :
    ‖normalization T P‖^2=1/(T*∏i,P i) := by
  have hs (x : ℝ) (hx : 0<x) : ‖(Real.sqrt x:ℂ)⁻¹‖^2=x⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),inv_pow,
      Real.sq_sqrt hx.le]
  rw [normalization,norm_mul,mul_pow,norm_prod,←Finset.prod_pow,hs T hT]
  simp_rw [hs _ (hP _)]
  rw [Finset.prod_inv_distrib]
  ring

theorem radial_mul (c : ℂ) (f : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>c*f z) keep Φ K=‖c‖^2*radialEnergy f keep Φ K := by
  unfold radialEnergy
  rw [←tsum_mul_left]
  congr 1
  funext z
  by_cases hz : keep z
  · simp only [hz,ite_true,norm_mul,mul_pow,mul_assoc]
  · simp only [hz,ite_false,mul_zero]

theorem radial_normalization (T : ℝ) (hT : 0<T) (P : ι→ℝ) (hP : ∀i,0<P i)
    (f : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>normalization T P*f z) keep Φ K=
      radialEnergy f keep Φ K/(T*∏i,P i) := by
  rw [radial_mul,normalization_sq T hT P hP]
  ring

/-- Exact passage between full and live normalizations. No support or
sign assumption on f is needed because this is equality of energies. -/
theorem frozen_live_identity (B : Tuple ι) (T : ℝ) (hT : 0<T)
    (P : ι→ℝ) (hP : ∀i,0<P i) (c : ℂ) (f : O→ℂ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>normalization T P*(c*f z)) keep Φ K=
      (‖c‖^2/(∏i,frozenScale B P i))*
        radialEnergy (fun z=>normalization T (fun i : liveIndices B=>P i.val)*f z) keep Φ K := by
  rw [radial_normalization T hT P hP,radial_mul,
    radial_normalization T hT (fun i : liveIndices B=>P i.val) (fun i=>hP i.val)]
  rw [←slot_scale_split B P]
  ring

omit [Fintype ι] in
theorem extracted_pair_norm (d : Id×Id) (B : Tuple ι) :
    pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))=pairNorm d*plainNorm B := by
  simp only [pairNorm,plainNorm,map_mul,Nat.cast_mul]
  ring

/-- The exact shorter ordinary pair and missing marked scales combine
to the original rawReduction. The child estimate remains explicit here;
its intended supplier is the proved canonical centered family. -/
theorem frozen_live_energy (B : Tuple ι) (_hB : ∀j,B j≠0)
    (d : Id×Id) (_hd : d.1≠0 ∧ d.2≠0) (T : ℝ) (hT : 0<T)
    (P : ι→ℝ) (hP : ∀i,0<P i) (c : ℂ) (f : O→ℂ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K E : ℝ)
    (he : radialEnergy (fun z=>normalization T (fun i : liveIndices B=>P i.val)*f z) keep Φ K≤
      E/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))) :
    radialEnergy (fun z=>normalization T P*(c*f z)) keep Φ K≤
      (‖c‖^2/rawReduction B P)*(E/pairNorm d) := by
  rw [frozen_live_identity B T hT P hP]
  have hp : 0≤‖c‖^2/(∏i,frozenScale B P i) :=
    div_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun i _=>(frozenScale_pos B P hP i).le))
  apply (mul_le_mul_of_nonneg_left he hp).trans_eq
  rw [extracted_pair_norm,rawReduction]
  ring

/-- Reuse the baseline frozen coefficient estimate after the exact
normalization transfer. This retains the whole extracted ideal saving. -/
theorem frozen_source_energy (B : Tuple ι) (hB : ∀j,B j≠0)
    (C R : Id) (hC : C≠0) (hprod : finiteTupleProduct B=C)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (T : ℝ) (hT : 0<T)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ) (hP : ∀i,0<P i)
    (hν : ∀i I,‖ν i I‖≤1) (hWnorm : ∀i x,‖Wslot i x‖≤M i) (hM : ∀i,1≤M i)
    (a b : ℝ) (ha : 0<a) (hW : ∀i,Function.support (Wslot i)⊆Set.Icc a b)
    (f : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K E : ℝ) (hE : 0≤E)
    (he : radialEnergy (fun z=>normalization T (fun i : liveIndices B=>P i.val)*f z) keep Φ K≤
      E/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))) :
    radialEnergy (fun z=>normalization T P*(frozenCoefficient B C R ν Wslot P*f z)) keep Φ K≤
      (((∏i,M i)^2*(max 1 b)^Fintype.card ι)/(C.absNorm:ℝ))*(E/pairNorm d) := by
  apply (frozen_live_energy B hB d hd T hT P hP _ f keep Φ K E he).trans
  exact mul_le_mul_of_nonneg_right
    (frozen_normalized_cost B hB C R hC hprod ν Wslot P M hP hν hWnorm hM a b ha hW)
    (div_nonneg hE (pairNorm_pos hd.1 hd.2).le)

end
end Candidate.FourthPower.MixedLiveNormalization
