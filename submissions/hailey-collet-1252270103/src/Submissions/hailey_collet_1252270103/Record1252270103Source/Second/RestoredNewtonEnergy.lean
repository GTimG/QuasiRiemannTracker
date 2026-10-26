/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual Newton multiplier acts inside the completed positive source norm. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredRows
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.WeightedEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentHeckeColumnWindow CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentSourceRectangleEnergy CenteredMomentSourceRectangle
open CenteredMomentRestrictedWindow Record1252270103Source QRH.Record1252270103Low
open QRH.Record1252270103Restoration
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance restoredNewtonDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev NewtonBranch := Σ _ : Finset (Ideal O),Finset (Ideal O)

def newtonBranches (P : Finset (Ideal O)) (depth : ℕ) : Finset NewtonBranch :=
  (P.powerset.filter (fun S=>S.card≤depth)).sigma (fun S=>S.powerset)

def newtonBranchModifier (A₁ A₂ : Ideal O) (b : NewtonBranch) (v : Tuple ι) : ℂ :=
  if (newtonDivisorPair b.1 b.2).1∣v (Sum.inr 0) ∧
      (newtonDivisorPair b.1 b.2).2∣v (Sum.inr 1)
  then sourceModifier A₁ A₂ 1 (fun _=>1) v else 0

def newtonBranchWeight (P : Finset (Ideal O)) (D : Ideal O) (b : NewtonBranch) : ℝ :=
  |newtonCoefficient P.card (idealDividingPool P D).card b.1.card|

theorem corrected_tuple_newton (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D R L : Ideal O) (depth : ℕ) (v : Tuple ι)
    (hv : v∈Fintype.piFinset s.pools) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,∀i,∀I∈s.slots i,¬p∣I) (hD : D∣R)
    (hcount : sourceModifier A₁ A₂ D (fun _=>1) v*
      profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v≠0 →
      (idealDividingPool P (v (Sum.inr 0)*v (Sum.inr 1))).card≤depth ∧
      (idealDividingPool P (D*finiteTupleProduct v)).card<P.card) :
    sourceModifier A₁ A₂ D (poolCorrection P) v*
      profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v=
      ∑b∈newtonBranches P depth,
        (newtonCoefficient P.card (idealDividingPool P D).card b.1.card:ℂ)*
          (newtonBranchModifier A₁ A₂ b v*
            profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v) := by
  let prof := profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v
  by_cases hprof : prof=0
  · simp only [show profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v=0 from hprof,
      mul_zero,Finset.sum_const_zero]
  by_cases hh : ordinarySmallHole (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1))
  swap
  · simp [sourceModifier_eq_literal,hh,newtonBranchModifier]
  by_cases hs : Squarefree ((A₁*v (Sum.inr 0))*(A₂*v (Sum.inr 1)))
  swap
  · simp [sourceModifier_eq_literal,hh,QRH.Record1252270103KernelMass.squarefreeIndicator,hs,newtonBranchModifier]
  have hn : sourceModifier A₁ A₂ D (fun _=>1) v*prof≠0 := by
    simpa [sourceModifier_eq_literal,hh,QRH.Record1252270103KernelMass.squarefreeIndicator,hs] using hprof
  obtain ⟨hdepth,hpole⟩ := hcount hn
  have hc : IsCoprime (finiteTupleProduct v) R := by
    by_contra hc
    exact hprof (by simp [prof,profileCoefficient,hc])
  have hprod : finiteTupleProduct v=(∏i,v (Sum.inl i))*v (Sum.inr 0)*v (Sum.inr 1) := by
    simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,mul_assoc]
  have hmarked : ∀p∈P,¬p∣∏i,v (Sum.inl i) := by
    intro p hpm
    apply (hp p hpm).not_dvd_finsetProd
    intro i hi
    exact havoid p hpm i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))
  have he := ideal_correction_rectangular P D (∏i,v (Sum.inl i))
    (v (Sum.inr 0)) (v (Sum.inr 1)) depth hp
    (hprod ▸ (hc.symm.of_isCoprime_of_dvd_left hD)) hmarked
    (squarefree_residual_pair A₁ A₂ _ _ hs) hdepth (hprod ▸ hpole)
  have hec := congrArg (fun x : ℝ=>(x:ℂ)) he
  push_cast at hec
  simp only [sourceModifier_eq_literal,hh,ite_true,
    QRH.Record1252270103KernelMass.squarefreeIndicator,hs,Int.cast_one,one_mul,
    poolCorrection,hprod]
  push_cast
  rw [hec]
  simp only [newtonBranches,Finset.sum_sigma,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro A hA
  simp only [newtonBranchModifier,newtonDivisorPair,sourceModifier_eq_literal,hh,ite_true,
    QRH.Record1252270103KernelMass.squarefreeIndicator,hs,Int.cast_one,one_mul,mul_one,
    idealDvdIndicator]
  split_ifs <;> simp_all

theorem corrected_source_newton_rows (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D R L : Ideal O) (depth : ℕ) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,∀i,∀I∈s.slots i,¬p∣I) (hD : D∣R)
    (hcount : ∀v∈Fintype.piFinset s.pools,
      sourceModifier A₁ A₂ D (fun _=>1) v*
        profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v≠0 →
      (idealDividingPool P (v (Sum.inr 0)*v (Sum.inr 1))).card≤depth ∧
        (idealDividingPool P (D*finiteTupleProduct v)).card<P.card)
    (τ : Character) (t : ℝ) (z : O) :
    modifiedSourceRow s (sourceModifier A₁ A₂ D (poolCorrection P)) R L τ t z=
      ∑b∈newtonBranches P depth,
        (newtonCoefficient P.card (idealDividingPool P D).card b.1.card:ℂ)*
          modifiedSourceRow s (newtonBranchModifier A₁ A₂ b) R L τ t z := by
  unfold modifiedSourceRow
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [corrected_tuple_newton s P A₁ A₂ D R L depth v hv hp havoid hD (hcount v hv)]
  simp only [Finset.sum_mul,mul_assoc]

theorem modifiedSourceRow_eq_polynomial (s : Input ι) (modifier : Tuple ι→ℂ)
    (R L : Ideal O) (τ : Character) (t : ℝ) (z : O) :
    rowPolynomial Finset.univ (CenteredMomentSourceRow.sourceGenerator
      (finiteColumns (Fintype.piFinset s.pools)))
      (fun I=>coefficient s modifier R L I*heightCoeff τ t I) z=
      modifiedSourceRow s modifier R L τ t z := by
  rw [height_source_row]
  unfold QRH.Record1252270103Source.High.CoupledFirst.coefficient
    QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient
  rw [finite_column_regroup]
  rfl

/-- Genuine completed-norm transfer for the actual correction. The children
are explicit ordinary-divisor masks on the same full source; no moment bound
is assumed and the original seed L and keep predicate are unchanged. -/
theorem corrected_source_newton_energy (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D R L : Ideal O) (depth : ℕ) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,∀i,∀I∈s.slots i,¬p∣I) (hD : D∣R)
    (hcount : ∀v∈Fintype.piFinset s.pools,
      sourceModifier A₁ A₂ D (fun _=>1) v*
        profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v≠0 →
      (idealDividingPool P (v (Sum.inr 0)*v (Sum.inr 1))).card≤depth ∧
        (idealDividingPool P (D*finiteTupleProduct v)).card<P.card)
    (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (sourceModifier A₁ A₂ D (poolCorrection P)) R L) (heightCoeff τ t) Φ H≤
      (∑b∈newtonBranches P depth,newtonBranchWeight P D b)*
        ∑b∈newtonBranches P depth,newtonBranchWeight P D b*
          sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
            (coefficient s (newtonBranchModifier A₁ A₂ b) R L) (heightCoeff τ t) Φ H := by
  let S := finiteColumns (Fintype.piFinset s.pools)
  apply restricted_energy_divisor_transfer keep Finset.univ
    (CenteredMomentSourceRow.sourceGenerator S) (CenteredMomentSourceRow.sourceGenerator_supported S)
    (fun I=>coefficient s (sourceModifier A₁ A₂ D (poolCorrection P)) R L I*heightCoeff τ t I)
    (newtonBranches P depth) (fun _=>Finset.univ)
    (fun _=>CenteredMomentSourceRow.sourceGenerator S)
    (fun _=>CenteredMomentSourceRow.sourceGenerator_supported S)
    (fun b I=>coefficient s (newtonBranchModifier A₁ A₂ b) R L I*heightCoeff τ t I)
    (fun b _=>(newtonCoefficient P.card (idealDividingPool P D).card b.1.card:ℂ))
    (newtonBranchWeight P D) (fun _ _=>abs_nonneg _)
    (fun _ _ _=>by simp only [newtonBranchWeight,Complex.norm_real,Real.norm_eq_abs,le_refl])
    ?_ Φ H hH hΦ
  intro z
  change rowPolynomial Finset.univ _ _ z=_
  rw [modifiedSourceRow_eq_polynomial s (sourceModifier A₁ A₂ D (poolCorrection P)) R L τ t z]
  dsimp only [S]
  simp only [modifiedSourceRow_eq_polynomial]
  exact corrected_source_newton_rows s P A₁ A₂ D R L depth hp havoid hD hcount τ t z

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.corrected_tuple_newton
#print axioms OAI.SevenEighths.Record1252270103Second.corrected_source_newton_rows
#print axioms OAI.SevenEighths.Record1252270103Second.corrected_source_newton_energy
