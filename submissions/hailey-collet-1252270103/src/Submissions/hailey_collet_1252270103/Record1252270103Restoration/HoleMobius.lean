/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.ForwardRows

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily Record1252270103KernelMass
local notation "O" => HeckeFamily.O

def subsetProduct (D : Finset PrimeIdeal) : Ideal O := ∏P∈D,P.val

theorem subsetProduct_nonzero (D : Finset PrimeIdeal) : subsetProduct D≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>P.property.ne_zero)

theorem subsetProduct_dvd_iff (D : Finset PrimeIdeal) (I : Ideal O) :
    subsetProduct D∣I ↔ ∀P∈D,P.val∣I := by
  constructor
  · intro h P hP
    exact (Finset.dvd_prod_of_mem (fun Q : PrimeIdeal=>Q.val) hP).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro P hP Q hQ hPQ
    apply P.property.irreducible.isRelPrime_iff_not_dvd.mpr
    intro hd
    have he := (prime_dvd_prime_iff_eq P.property Q.property).mp hd
    exact hPQ (Subtype.ext he)

theorem prime_dvd_iff_valuation_pos {I : Ideal O} (hI : I≠0) (P : PrimeIdeal) :
    P.val∣I ↔ 0<valuation I P.val := by
  rw [dvd_iff_valuation_le P.property.ne_zero hI]
  constructor
  · intro h
    have hh := h P.val
    rw [valuation_prime,if_pos rfl] at hh
    exact hh
  · intro h Q
    rw [valuation_prime]
    split_ifs with he
    · subst Q;exact h
    · exact Nat.zero_le _

theorem single_hole_indicator {I : Ideal O} (hI : I≠0) :
    (if (∀P∈smallPrimes,valuation I P.val=0) then (1:ℂ) else 0) =
      ∑D∈smallPrimes.powerset,if subsetProduct D∣I then (-1:ℂ)^D.card else 0 := by
  let bad := smallPrimes.filter (fun P=>P.val∣I)
  have hb : bad⊆smallPrimes := Finset.filter_subset _ _
  have h := CoprimeMobiusExtension.disjoint_indicator_expansion smallPrimes smallPrimes bad
    Finset.Subset.rfl hb
  have hdis : Disjoint smallPrimes bad ↔ ∀P∈smallPrimes,valuation I P.val=0 := by
    rw [Finset.disjoint_left]
    constructor
    · intro hd P hP
      apply Nat.eq_zero_of_not_pos
      intro hv
      exact hd hP (Finset.mem_filter.mpr ⟨hP,(prime_dvd_iff_valuation_pos hI P).mpr hv⟩)
    · intro hd P hP hbad
      have hdiv := (Finset.mem_filter.mp hbad).2
      have hv := (prime_dvd_iff_valuation_pos hI P).mp hdiv
      rw [hd P hP] at hv
      exact Nat.lt_irrefl 0 hv
  simp only [hdis] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro D hD
  have hDs := Finset.mem_powerset.mp hD
  have hd : D⊆bad ↔ subsetProduct D∣I := by
    rw [subsetProduct_dvd_iff]
    constructor
    · intro hd P hP;exact (Finset.mem_filter.mp (hd hP)).2
    · intro hd P hP;exact Finset.mem_filter.mpr ⟨hDs hP,hd P hP⟩
  simp only [hDs,true_and,hd]

theorem pair_hole_indicator {I J : Ideal O} (hI : I≠0) (hJ : J≠0) :
    (if ordinarySmallHole I J then (1:ℂ) else 0) =
      ∑D₁∈smallPrimes.powerset,∑D₂∈smallPrimes.powerset,
        if subsetProduct D₁∣I ∧ subsetProduct D₂∣J then (-1:ℂ)^(D₁.card+D₂.card) else 0 := by
  have hh : ordinarySmallHole I J ↔
      (∀P∈smallPrimes,valuation I P.val=0) ∧ (∀P∈smallPrimes,valuation J P.val=0) := by
    constructor
    · intro h;exact ⟨fun P hP=>(h P hP).1,fun P hP=>(h P hP).2⟩
    · rintro ⟨h₁,h₂⟩ P hP;exact ⟨h₁ P hP,h₂ P hP⟩
  have he : (if (∀P∈smallPrimes,valuation I P.val=0) ∧ (∀P∈smallPrimes,valuation J P.val=0)
      then (1:ℂ) else 0) =
      (if (∀P∈smallPrimes,valuation I P.val=0) then (1:ℂ) else 0)*
      (if (∀P∈smallPrimes,valuation J P.val=0) then (1:ℂ) else 0) := by
    split_ifs <;> simp_all
  trans (if (∀P∈smallPrimes,valuation I P.val=0) then (1:ℂ) else 0)*
      (if (∀P∈smallPrimes,valuation J P.val=0) then (1:ℂ) else 0)
  · simpa only [hh] using he
  rw [single_hole_indicator hI,single_hole_indicator hJ,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  split_ifs <;> simp_all [pow_add]

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.pair_hole_indicator
