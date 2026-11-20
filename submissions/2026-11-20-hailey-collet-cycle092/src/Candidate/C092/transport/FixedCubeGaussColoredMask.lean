/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussH8Projection
import Candidate.C092.transport.FixedIndependentTwists

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Two distinct authentic inducing rows keep their own conductor holes. -/
lemma independent_pairAllowed_native_mask (D₁ D₂ : FixedCubeDatum) (M K I J : Id)
    (hI : I≠0) (hJ : J≠0) (hM : M≠0) (hK : K≠0) (hMK : M∣K)
    (hcI : IsCoprime I D₁.row.χ.modulus) (hcJ : IsCoprime J D₂.row.χ.modulus) :
    PairAllowed (fixedCubeBad D₁ D₂ (residualSuppliers M∪residualHoles K))
      (supplyingResidualPairs D₁.row D₂.row (residualSuppliers M) (residualHoles K) (residualHoles K)) I J ↔
    Candidate.FourthPower.SexticSieve.PowerFree 3 (I*J) ∧ IsCoprime K (I*J) := by
  have hs : residualSuppliers M ⊆ residualHoles K := by
    intro P hp
    exact prime_dvd_mem_support K hK P
      (((prime_dvd_iff_positive M hM P).mpr (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))).trans hMK)
  delta QRH.Cycle092.SignedCenter.supplyingResidualPairs
  rw [pairAllowed_ordinaryResidualPairs,pairCubeFree_iff_native I J hI hJ]
  apply and_congr_right
  intro _
  rw [IsCoprime.mul_right_iff]
  constructor
  · rintro ⟨hi,hj⟩
    constructor
    · apply IsCoprime.symm
      apply (coprime_iff_local_zero I K hI hK).mpr
      intro P hp
      have hh := hi P (fixedCubeBad_contains_labels D₁ D₂ _ (Finset.mem_union_right _ hp))
      simpa only [supplyingPrimeKeep,decide_eq_true_eq,residualHoles,hp,not_true_eq_false,
        and_false,false_or] using hh
    · apply IsCoprime.symm
      apply (coprime_iff_local_zero J K hJ hK).mpr
      intro P hp
      have hh := hj P (fixedCubeBad_contains_labels D₁ D₂ _ (Finset.mem_union_right _ hp))
      simpa only [supplyingPrimeKeep,decide_eq_true_eq,residualHoles,hp,not_true_eq_false,
        and_false,false_or] using hh
  · rintro ⟨hi,hj⟩
    have step (D : FixedCubeDatum) (V : Id) (hV : V≠0) (hv : IsCoprime K V)
        (hc : IsCoprime V D.row.χ.modulus) (P : PrimeIdeal) :
        (IsCoprime P.val D.row.χ.modulus ∧
          supplyingPrimeKeep (residualSuppliers M) (residualHoles K) P=true) ∨
          ProbePhysical.primeValuations V P=0 := by
      by_cases hz : ProbePhysical.primeValuations V P=0
      · exact Or.inr hz
      · refine Or.inl ⟨prime_coprime_of_coprime V _ hV hc P hz,?_⟩
        simp only [supplyingPrimeKeep,decide_eq_true_eq]
        have hn : P∉residualHoles K := by
          intro hp
          exact hz ((coprime_iff_local_zero V K hV hK).mp hv.symm P hp)
        exact ⟨fun hp=>hn (hs hp),hn⟩
    exact ⟨fun P _=>step D₁ I hI hi hcI P,fun P _=>step D₂ J hJ hj hcJ P⟩

def coloredCanonicalPairCoefficient (χ : Character) (ω₁ ω₂ : Character) (K I J : Id) : ℂ :=
  canonicalPairCoefficient χ K I J*(idealCoeff ω₁ I*idealCoeff ω₂ J)

/-- The literal weighted coefficient has two genuine twisted fixed rows.
No inverse or nonvanishing convention is used at ramified ideals. -/
lemma coloredCanonicalPairCoefficient_eq_physical (D : FixedCubeDatum) (ω₁ ω₂ : Character)
    (M K : Id) (hM : M≠0) (hK : K≠0) (hMK : M∣K) (I J : Id) :
    coloredCanonicalPairCoefficient D.row.χ ω₁ ω₂ K I J=
      if PairAllowed (fixedCubeBad (D.twistColumn ω₁) (D.twistColumn ω₂) (residualSuppliers M∪residualHoles K))
        (supplyingResidualPairs (D.twistColumn ω₁).row (D.twistColumn ω₂).row
          (residualSuppliers M) (residualHoles K) (residualHoles K)) I J
      then (D.twistColumn ω₁).actualCoefficient I*(D.twistColumn ω₂).actualCoefficient J else 0 := by
  have he : coloredCanonicalPairCoefficient D.row.χ ω₁ ω₂ K I J=
      if Candidate.FourthPower.SexticSieve.PowerFree 3 (I*J) ∧ IsCoprime K (I*J) then
        (D.twistColumn ω₁).actualCoefficient I*(D.twistColumn ω₂).actualCoefficient J else 0 := by
    unfold coloredCanonicalPairCoefficient canonicalPairCoefficient
    rw [actualCoefficient_twist,actualCoefficient_twist,←D.row_spec.2.2.2 I,←D.row_spec.2.2.2 J]
    split_ifs <;> ring
  rw [he]
  by_cases hi : (D.twistColumn ω₁).actualCoefficient I=0
  · simp only [hi,zero_mul,ite_self]
  by_cases hj : (D.twistColumn ω₂).actualCoefficient J=0
  · simp only [hj,mul_zero,ite_self]
  have hI : I≠0 := by
    intro h
    apply hi
    rw [←(D.twistColumn ω₁).row_spec.2.2.2 I,h,map_zero]
  have hJ : J≠0 := by
    intro h
    apply hj
    rw [←(D.twistColumn ω₂).row_spec.2.2.2 J,h,map_zero]
  have hcI : IsCoprime I (D.twistColumn ω₁).row.χ.modulus := by
    by_contra h
    exact hi (by rw [FixedCubeDatum.actualCoefficient_inducing,ite_eq_right h])
  have hcJ : IsCoprime J (D.twistColumn ω₂).row.χ.modulus := by
    by_contra h
    exact hj (by rw [FixedCubeDatum.actualCoefficient_inducing,ite_eq_right h])
  rw [independent_pairAllowed_native_mask _ _ M K I J hI hJ hM hK hMK hcI hcJ]
  split_ifs <;> rfl

#print axioms independent_pairAllowed_native_mask
#print axioms coloredCanonicalPairCoefficient_eq_physical
end
end QRH.Cycle092.FixedCubeGauss
