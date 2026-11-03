/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/SIntegerResidueQuotientInjectivity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

open scoped NumberField
open NumberField

namespace DedekindZetaZeroFree.ArithGaussCRT

variable {F : Type} [Field F] [NumberField F]

 def valuationBoundIdeal (A : SArithmeticData F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) (n : ℕ) :
    Ideal A.R where
  carrier := {a | v.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change v.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property v hv) zero_le).trans (by simpa using hb)

theorem exteriorQuotientMap_injective (A : SArithmeticData F) (I : A.Exterior) :
    Function.Injective
      (Ideal.quotientMap (A.extendIdeal I) (algebraMap (𝓞 F) A.R)
        (show I.val ≤ (A.extendIdeal I).comap (algebraMap (𝓞 F) A.R) from
          Ideal.le_comap_map)) := by
  classical
  apply Ideal.quotientMap_injective'
  have hI : I.val ≠ (0 : Ideal (𝓞 F)) := I.property.1
  rw [← Ideal.iInf_maxPowDividing_eq hI]
  apply le_iInf
  intro v
  let n := (Associates.mk v.asIdeal).count (Associates.mk I.val).factors
  change (A.extendIdeal I).comap (algebraMap (𝓞 F) A.R) ≤ v.asIdeal ^ n
  by_cases hn : n = 0
  · simp [hn, Ideal.one_eq_top]
  have hvI : I.val ≤ v.asIdeal :=
    Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hn)
  have hv : v ∉ A.Sf := by
    intro hvS
    have hc : A.cS ≤ v.asIdeal := by
      apply Ideal.prod_le_inf.trans
      exact Finset.inf_le hvS
    have ht : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rw [← I.property.2]
      exact sup_le hvI hc
    exact v.isPrime.ne_top (top_unique ht)
  have hIn : I.val ≤ v.asIdeal ^ n := by
    rw [← Ideal.iInf_maxPowDividing_eq hI]
    exact iInf_le (fun w => w.maxPowDividing I.val) v
  have hmap : A.extendIdeal I ≤ valuationBoundIdeal A v hv n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change v.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))
    rw [v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem a n).mpr (hIn ha)
  intro a ha
  apply (v.intValuation_le_pow_iff_mem a n).mp
  rw [← v.valuation_of_algebraMap (K := F)]
  exact hmap ha

end DedekindZetaZeroFree.ArithGaussCRT
