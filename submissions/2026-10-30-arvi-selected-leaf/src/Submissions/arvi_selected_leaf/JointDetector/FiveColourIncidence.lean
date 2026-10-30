/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.FiveColourNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CenteredExceptionalCount

/-! Row incidence of all shared tables, source punctures and coprime labels.
The finite prime carrier belongs to ONE original row. It is never a pool of
all arbitrary shared tables. Repeated prime powers of the original row remain
in its ordinary ideal divisor bound. -/
namespace Qrh.JointDetector.FiveColourIncidence
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

/-- Distinct prime ideals retain the complete subset support in their product. -/
theorem primeSubsetProduct_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P) :
    Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T he
  have hmem (S T : Finset ι) (he : (∏ i ∈ S, P i) = ∏ i ∈ T, P i) (i : ι) (hi : i ∈ S) : i ∈ T := by
    have hd : P i ∣ ∏ j ∈ T, P j := he ▸ Finset.dvd_prod_of_mem P hi
    obtain ⟨j,hj,hdj⟩ := (hP i).dvd_finset_prod_iff P |>.mp hd
    have hij : i=j := hinj (associated_iff_eq.mp (((hP i).dvd_prime_iff_associated (hP j)).mp hdj))
    simpa only [hij] using hj
  exact Finset.ext (fun i => ⟨hmem S T he i,hmem T S he.symm i⟩)

theorem distinct_prime_product_dvd {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (I : Ideal O) (hdiv : ∀ i, P i ∣ I) : (∏ i, P i) ∣ I := by
  apply Fintype.prod_dvd_of_coprime ?_ hdiv
  intro i j hij
  letI : (P i).IsMaximal := (Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  letI : (P j).IsMaximal := (Ideal.isPrime_of_prime (hP j)).isMaximal (hP j).ne_zero
  exact Ideal.isCoprime_of_isMaximal (fun he => hij (hinj he))

/-- All prime subsets of an original row inject into its ACTUAL ordinary
ideal divisors. The row itself may contain any repeated prime powers. -/
theorem prime_powerset_card_le_divisors {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (I : Ideal O) (hI : I ≠ 0) (hdiv : (∏ i, P i) ∣ I) :
    2^(Fintype.card ι) ≤ (idealDivisors I).card := by
  rw [← Finset.card_univ,← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun S : Finset ι => ∏ i ∈ S, P i)
  · intro S hS
    exact (mem_idealDivisors hI).2
      ((Finset.prod_dvd_prod_of_subset S Finset.univ P (Finset.mem_powerset.mp hS)).trans hdiv)
  · intro S hS T hT he
    exact primeSubsetProduct_injective P hP hinj he

/-- One label attached to ONE original row: its shared-table assignment,
a cancelled-prime subset, and the remaining pivot-coprime divisor. -/
abbrev IncidenceLabel (ι : Type*) (I : Ideal O) :=
  (ι → Option (Fin 5)) × Finset ι × idealDivisors I

/-- Six table choices and two puncture choices per original prime; the last
factor is the original row divisor incidence, not the total label pool. -/
theorem incidenceLabel_card {ι : Type*} [Fintype ι] (I : Ideal O) :
    Fintype.card (IncidenceLabel ι I) =
      6^(Fintype.card ι)*2^(Fintype.card ι)*(idealDivisors I).card := by
  simp [IncidenceLabel,Fintype.card_prod,Fintype.card_fun,mul_assoc]

/-- All shared-table, cancelled-prime and pivot-divisor incidences are paid
by a single uniform small power of the original row norm. No analytic input. -/
theorem incidenceLabel_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι]
      (P : ι → Ideal O) (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
      (I : Ideal O), I ≠ 0 → (∏ i, P i) ∣ I →
      (Fintype.card (IncidenceLabel ι I) : ℝ) ≤ C*(I.absNorm : ℝ)^ε := by
  have he : 0 < ε/5 := by positivity
  let K := idealDivisorConstant (ε/5) he
  have hK : 0 < K := idealDivisorConstant_pos _ _
  refine ⟨K^5,by positivity,?_⟩
  intro ι _ P hP hinj I hI hdiv
  let D := (idealDivisors I).card
  have htwo : (2 : ℝ)^(Fintype.card ι) ≤ (D : ℝ) := by
    exact_mod_cast prime_powerset_card_le_divisors P hP hinj I hI hdiv
  have hlabel : (Fintype.card (IncidenceLabel ι I) : ℝ) ≤ (D : ℝ)^5 := by
    rw [incidenceLabel_card]
    push_cast
    have htwelve : (6 : ℝ)^(Fintype.card ι)*(2 : ℝ)^(Fintype.card ι) ≤
        ((2 : ℝ)^(Fintype.card ι))^4 := by
      rw [← mul_pow,show (6 : ℝ)*2 = 12 by norm_num]
      calc
        _ ≤ (16 : ℝ)^(Fintype.card ι) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ = _ := by rw [show (16 : ℝ)=2^4 by norm_num,← pow_mul,← pow_mul]; congr 1; omega
    calc
      _ ≤ (((2 : ℝ)^(Fintype.card ι))^4)*(D : ℝ) := mul_le_mul_of_nonneg_right htwelve (Nat.cast_nonneg _)
      _ ≤ (D : ℝ)^4*(D : ℝ) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) htwo _) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hdivisor : (D : ℝ) ≤ K*(I.absNorm : ℝ)^(ε/5) := idealDivisorConstant_bound _ _ I hI
  have hIpos : 0 < (I.absNorm : ℝ) := CenteredExceptionalCount.norm_pos hI
  calc
    _ ≤ (D : ℝ)^5 := hlabel
    _ ≤ (K*(I.absNorm : ℝ)^(ε/5))^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdivisor _
    _ = K^5*(I.absNorm : ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hIpos.le]
      congr 1
      ring

/-- Every divisor label in the ACTUAL cancelled-prime Poisson sum divides
the cancelled diagonal product. In particular its norm is at most G*H. -/
theorem puncture_subset_divides {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S E : Finset ι) (hE : E ∈ S.powerset) :
    (∏ i ∈ E, P i) ∣ ∏ i ∈ S, P i :=
  Finset.prod_dvd_prod_of_subset E S P (Finset.mem_powerset.mp hE)

theorem puncture_subset_norm_le {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S E : Finset ι) (hE : E ∈ S.powerset)
    (hS : (∏ i ∈ S, P i) ≠ 0) :
    ((∏ i ∈ E, P i).absNorm : ℝ) ≤ ((∏ i ∈ S, P i).absNorm : ℝ) :=
  CenteredExceptionalCount.norm_le_of_dvd hS (puncture_subset_divides P S E hE)

/-- The source puncture divisor obeys the G*H cap from the actual diagonal
support, with G the colour-one diagonal and H all other diagonal colours. -/
theorem puncture_subset_norm_le_split {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (colour : ι → ℕ) (S E : Finset ι) (hE : E ∈ S.powerset)
    (hS : (∏ i ∈ S, P i) ≠ 0) :
    ((∏ i ∈ E, P i).absNorm : ℝ) ≤
      ((∏ i ∈ S.filter (fun i => colour i=1), P i).absNorm : ℝ)*
      ((∏ i ∈ S.filter (fun i => colour i≠1), P i).absNorm : ℝ) := by
  have hh := puncture_subset_norm_le P S E hE hS
  have heq : (∏ i ∈ S, P i) =
      (∏ i ∈ S.filter (fun i => colour i=1), P i)*
      (∏ i ∈ S.filter (fun i => colour i≠1), P i) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  rw [heq,map_mul,Nat.cast_mul] at hh
  exact hh

/-- Product of the literal prime states selected by a colour predicate. -/
def colourProduct {ι : Type*} [Fintype ι] (P : ι → Ideal O) (left right : ι → ℕ)
    (keep : ℕ → ℕ → Prop) : Ideal O :=
  ∏ i, if keep (left i) (right i) then P i else 1

def sharedG {ι : Type*} [Fintype ι] (P : ι → Ideal O) (l r : ι → ℕ) : Ideal O :=
  colourProduct P l r (fun j k => j=1 ∧ k=1)
def sharedH {ι : Type*} [Fintype ι] (P : ι → Ideal O) (l r : ι → ℕ) : Ideal O :=
  colourProduct P l r (fun j k => j=k ∧ j≠0 ∧ j≠1)
def sharedE {ι : Type*} [Fintype ι] (P : ι → Ideal O) (l r : ι → ℕ) : Ideal O :=
  colourProduct P l r (fun j k => j=1 ∧ k≠0 ∧ k≠1)
def sharedF {ι : Type*} [Fintype ι] (P : ι → Ideal O) (l r : ι → ℕ) : Ideal O :=
  colourProduct P l r (fun j k => k=1 ∧ j≠0 ∧ j≠1)
def sharedJ {ι : Type*} [Fintype ι] (P : ι → Ideal O) (l r : ι → ℕ) : Ideal O :=
  colourProduct P l r (fun j k => j≠0 ∧ k≠0 ∧ j≠k ∧ j≠1 ∧ k≠1)

/-- Exact full25 conductor product. Equal colours are counted twice in the
original radical product and cancel; every unequal colour remains primitive,
including difference three. No shared-prime stratum is estimated away. -/
theorem shared_conductor_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    colourProduct P l r (fun j _ => j≠0)*colourProduct P l r (fun _ k => k≠0) =
      colourProduct P l r (fun j k => j≠k)*(sharedG P l r)^2*(sharedH P l r)^2*
        sharedJ P l r*sharedE P l r*sharedF P l r := by
  unfold sharedG sharedH sharedJ sharedE sharedF colourProduct
  simp_rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hl0 : l i=0 <;> by_cases hr0 : r i=0 <;>
    by_cases hl1 : l i=1 <;> by_cases hr1 : r i=1 <;> by_cases hlr : l i=r i <;>
    simp_all [eq_comm, ← Ideal.one_eq_top, pow_two]

/-- The two true free-pivot products, before any radius inequality. -/
theorem shared_left_pivot_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    colourProduct P l r (fun j _ => j=1) =
      colourProduct P l r (fun j k => j=1 ∧ k=0)*sharedG P l r*sharedE P l r := by
  unfold sharedG sharedE colourProduct
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hl : l i=1 <;> by_cases hr0 : r i=0 <;> by_cases hr1 : r i=1 <;> simp_all [eq_comm, ← Ideal.one_eq_top, pow_two]

theorem shared_right_pivot_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    colourProduct P l r (fun _ k => k=1) =
      colourProduct P l r (fun j k => j=0 ∧ k=1)*sharedG P l r*sharedF P l r := by
  unfold sharedG sharedF colourProduct
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hr : r i=1 <;> by_cases hl0 : l i=0 <;> by_cases hl1 : l i=1 <;> simp_all [eq_comm, ← Ideal.one_eq_top, pow_two]

theorem shared_left_higher_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    colourProduct P l r (fun j _ => j≠0 ∧ j≠1) =
      colourProduct P l r (fun j k => j≠0 ∧ j≠1 ∧ k=0)*sharedH P l r*sharedJ P l r*sharedF P l r := by
  unfold sharedH sharedJ sharedF colourProduct
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hl0 : l i=0 <;> by_cases hr0 : r i=0 <;>
    by_cases hl1 : l i=1 <;> by_cases hr1 : r i=1 <;> by_cases hlr : l i=r i <;>
    simp_all [eq_comm, ← Ideal.one_eq_top, pow_two]

theorem shared_right_higher_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    colourProduct P l r (fun _ k => k≠0 ∧ k≠1) =
      colourProduct P l r (fun j k => k≠0 ∧ k≠1 ∧ j=0)*sharedH P l r*sharedJ P l r*sharedE P l r := by
  unfold sharedH sharedJ sharedE colourProduct
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hl0 : l i=0 <;> by_cases hr0 : r i=0 <;>
    by_cases hl1 : l i=1 <;> by_cases hr1 : r i=1 <;> by_cases hlr : l i=r i <;>
    simp_all [eq_comm, ← Ideal.one_eq_top, pow_two]

theorem shared_diagonal_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    colourProduct P l r (fun j k => j=k ∧ j≠0) = sharedG P l r*sharedH P l r := by
  unfold sharedG sharedH colourProduct
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hl0 : l i=0 <;> by_cases hl1 : l i=1 <;> by_cases hlr : l i=r i <;> simp_all [eq_comm, ← Ideal.one_eq_top, pow_two]

theorem colourProduct_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (l r : ι → ℕ) (keep : ℕ → ℕ → Prop) :
    colourProduct P l r keep ≠ 0 := by
  unfold colourProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs
  · exact hP i
  · exact one_ne_zero

theorem shared_conductor_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (l r : ι → ℕ) :
    ((colourProduct P l r (fun j _ => j≠0)).absNorm : ℝ)*
      ((colourProduct P l r (fun _ k => k≠0)).absNorm : ℝ) =
      ((colourProduct P l r (fun j k => j≠k)).absNorm : ℝ)*
        ((sharedG P l r).absNorm : ℝ)^2*((sharedH P l r).absNorm : ℝ)^2*
        ((sharedJ P l r).absNorm : ℝ)*((sharedE P l r).absNorm : ℝ)*((sharedF P l r).absNorm : ℝ) := by
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using
    congrArg (fun I : Ideal O => (I.absNorm : ℝ)) (shared_conductor_product P l r)

/-- Exact Q=(UV)^2/(G²H²JEF) before the dyadic radii are substituted. -/
theorem shared_conductor_norm_quotient {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (l r : ι → ℕ) :
    ((colourProduct P l r (fun j k => j≠k)).absNorm : ℝ) =
      (((colourProduct P l r (fun j _ => j≠0)).absNorm : ℝ)*
        ((colourProduct P l r (fun _ k => k≠0)).absNorm : ℝ))/
      (((sharedG P l r).absNorm : ℝ)^2*((sharedH P l r).absNorm : ℝ)^2*
        ((sharedJ P l r).absNorm : ℝ)*((sharedE P l r).absNorm : ℝ)*((sharedF P l r).absNorm : ℝ)) := by
  have hg : 0 < ((sharedG P l r).absNorm : ℝ) :=
    CenteredExceptionalCount.norm_pos (colourProduct_ne_zero P hP l r _)
  have hh : 0 < ((sharedH P l r).absNorm : ℝ) :=
    CenteredExceptionalCount.norm_pos (colourProduct_ne_zero P hP l r _)
  have hj : 0 < ((sharedJ P l r).absNorm : ℝ) :=
    CenteredExceptionalCount.norm_pos (colourProduct_ne_zero P hP l r _)
  have he : 0 < ((sharedE P l r).absNorm : ℝ) :=
    CenteredExceptionalCount.norm_pos (colourProduct_ne_zero P hP l r _)
  have hf : 0 < ((sharedF P l r).absNorm : ℝ) :=
    CenteredExceptionalCount.norm_pos (colourProduct_ne_zero P hP l r _)
  apply (eq_div_iff (by positivity)).2
  have h := shared_conductor_norm P l r
  simpa only [mul_assoc] using h.symm

end
end Qrh.JointDetector.FiveColourIncidence

#print axioms Qrh.JointDetector.FiveColourIncidence.incidenceLabel_small_power
#print axioms Qrh.JointDetector.FiveColourIncidence.puncture_subset_norm_le

#print axioms Qrh.JointDetector.FiveColourIncidence.puncture_subset_norm_le_split

#print axioms Qrh.JointDetector.FiveColourIncidence.shared_conductor_product

#print axioms Qrh.JointDetector.FiveColourIncidence.shared_conductor_norm_quotient
