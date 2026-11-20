/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussCanonical

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

lemma prime_dvd_iff_positive (I : Id) (hI : I≠0) (P : PrimeIdeal) :
    P.val∣I ↔ 0<ProbePhysical.primeValuations I P := by
  rw [ideal_dvd_iff_valuations_le P.val I P.property.ne_zero hI,
    ProbePhysical.primeValuations_prime,Finsupp.single_le_iff]
  omega

lemma coprime_iff_local_zero (I K : Id) (hI : I≠0) (hK : K≠0) :
    IsCoprime I K ↔ ∀P∈(ProbePhysical.primeValuations K).support,
      ProbePhysical.primeValuations I P=0 := by
  constructor
  · intro hc P hP
    by_contra hn
    have hdI := (prime_dvd_iff_positive I hI P).mpr (Nat.pos_of_ne_zero hn)
    have hdK := (prime_dvd_iff_positive K hK P).mpr
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP))
    rw [Ideal.isCoprime_iff_sup_eq] at hc
    have hle : I ⊔ K ≤ P.val := sup_le (Ideal.le_of_dvd hdI) (Ideal.le_of_dvd hdK)
    rw [hc] at hle
    exact P.property.not_isUnit (Ideal.isUnit_iff.mpr (top_unique hle))
  · intro hz
    rw [←ProbePhysical.idealFromValuations_primeValuations K hK]
    unfold ProbePhysical.idealFromValuations
    rw [Finsupp.prod]
    apply IsCoprime.prod_right
    intro P hP
    apply IsCoprime.pow_right
    apply IsCoprime.symm
    exact prime_coprime_outside_support I hI P (Finsupp.notMem_support_iff.mpr (hz P hP))

lemma pairCubeFree_iff_native (I J : Id) (hI : I≠0) (hJ : J≠0) :
    PairCubeFree I J ↔ Candidate.FourthPower.SexticSieve.PowerFree 3 (I*J) := by
  rw [PairCubeFree_iff_prime_cube_not_dvd I J hI hJ]
  constructor
  · intro h P hP
    exact h ⟨P,hP⟩
  · intro h P
    exact h P.val P.property

lemma prime_coprime_of_coprime (I K : Id) (hI : I≠0) (hc : IsCoprime I K)
    (P : PrimeIdeal) (hp : ProbePhysical.primeValuations I P≠0) : IsCoprime P.val K := by
  exact hc.of_isCoprime_of_dvd_left ((prime_dvd_iff_positive I hI P).mpr (Nat.pos_of_ne_zero hp))

def residualSuppliers (M : Id) : Finset PrimeIdeal := (ProbePhysical.primeValuations M).support

def residualHoles (K : Id) : Finset PrimeIdeal := (ProbePhysical.primeValuations K).support

/-- The actual local allocation retains exactly the native punctures and the
prime labels supplied by the frozen mark product. Presented conductor holes
are retained automatically, including their zero coefficients. -/
lemma pairAllowed_native_mask (D : FixedCubeDatum) (M K I J : Id)
    (hI : I≠0) (hJ : J≠0) (hM : M≠0) (hK : K≠0) (hMK : M∣K)
    (hcI : IsCoprime I D.row.χ.modulus) (hcJ : IsCoprime J D.row.χ.modulus) :
    PairAllowed (fixedCubeBad D D (residualSuppliers M∪residualHoles K))
      (supplyingResidualPairs D.row D.row (residualSuppliers M) (residualHoles K) (residualHoles K)) I J ↔
    Candidate.FourthPower.SexticSieve.PowerFree 3 (I*J) ∧ IsCoprime K (I*J) := by
  have hs : residualSuppliers M ⊆ residualHoles K := by
    intro P hp
    exact prime_dvd_mem_support K hK P
      (((prime_dvd_iff_positive M hM P).mpr (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))).trans hMK)
  delta QRH.Cycle092.SignedCenter.supplyingResidualPairs
  rw [pairAllowed_ordinaryResidualPairs,
    pairCubeFree_iff_native I J hI hJ]
  apply and_congr_right
  intro _
  rw [IsCoprime.mul_right_iff]
  constructor
  · rintro ⟨hi,hj⟩
    constructor
    · apply IsCoprime.symm
      apply (coprime_iff_local_zero I K hI hK).mpr
      intro P hp
      have hh := hi P (fixedCubeBad_contains_labels D D _ (Finset.mem_union_right _ hp))
      simpa only [supplyingPrimeKeep,decide_eq_true_eq,residualHoles,hp,not_true_eq_false,
        and_false,false_or] using hh
    · apply IsCoprime.symm
      apply (coprime_iff_local_zero J K hJ hK).mpr
      intro P hp
      have hh := hj P (fixedCubeBad_contains_labels D D _ (Finset.mem_union_right _ hp))
      simpa only [supplyingPrimeKeep,decide_eq_true_eq,residualHoles,hp,not_true_eq_false,
        and_false,false_or] using hh
  · rintro ⟨hi,hj⟩
    have step (V : Id) (hV : V≠0) (hv : IsCoprime K V)
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
    exact ⟨fun P _=>step I hI hi hcI P,fun P _=>step J hJ hj hcJ P⟩

#print axioms pairAllowed_native_mask
#print axioms coprime_iff_local_zero
#print axioms pairCubeFree_iff_native
end
end QRH.Cycle092.FixedCubeGauss
