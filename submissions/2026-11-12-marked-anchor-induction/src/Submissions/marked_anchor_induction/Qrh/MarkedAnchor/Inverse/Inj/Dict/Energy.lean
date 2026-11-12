/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReference{Remaining,
Energy,Mass,Arithmetic,Reindex}.lean` (Apache-2.0). Modified by Sil (2026-11-12): no `PairwiseDisjoint`
lists; injective tuples only; the remaining tuples are the `PiOK` ones (injective, avoiding the
assigned primes); admissibility and coprimality come from injectivity. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Dict.Split

/-!
# Inverse.Inj.Dict.Energy — injective clones of the baseline marked-reference energy

* `remainingPolynomialInj`, `remainingResidualInj_eq_polynomial` (Möbius sign from injectivity),
  `remainingPolynomialInj_original_pi` (the `Finset.pi` form over `PiOK` tuples, the domain of the
  injective residual layer);
* `assignedTermInj`, `assignedTermInj_norm_le`, `assigned_family_energy_inj`,
  **`original_energy_of_remaining_inj`**, **`original_energy_with_assigned_count_inj`** (the
  assigned mass of the injective `x` is bounded by the full baseline mass);
* arithmetic: `assigned_admissible_inj`, `remaining_tuple_admissible_inj`,
  `remaining_tuple_outside_inj` (the coprimality of the remaining entries follows from
  injectivity and is not a hypothesis of the injective residual layer).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseAssignedCount
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion
open CanonicalQuadraticSieve InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The remaining polynomial on `PiOK` tuples -/

/-- The baseline `remainingPolynomial` restricted to `PiOK` remaining tuples. -/
def remainingPolynomialInj (S : Finset (Ideal O)) (L : ι → Finset (Ideal O)) (J : Finset ι)
    (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  ∑ y : Remaining L J, if PiOK (Finset.univ \ J) (assignedIdeal L J x) (remainingPi L J y) then
    (∏ i : {i : ι // i ∉ J}, star (coeff i.val (y i).val)) *
      residualNormalizedPolynomial S (assignedIdeal L J x * remainingIdeal L J y)
        (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _ => 1)
        (fun v => star (W v)) Z r z G u
  else 0

theorem remainingResidualInj_eq_polynomial (S : Finset (Ideal O))
    (L : ι → Finset (Ideal O)) (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (J : Finset ι) (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) :
    remainingResidualInj S L J x coeff η (fun _ => 1) W Z r z G u =
      (-1 : ℂ) ^ Fintype.card {i : ι // i ∉ J} *
      remainingPolynomialInj S L J x coeff η W Z r z G u := by
  unfold remainingResidualInj remainingPolynomialInj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hok : PiOK (Finset.univ \ J) (assignedIdeal L J x) (remainingPi L J y)
  · rw [if_pos hok, if_pos hok, remaining_moebius_of_ok L hprime J _ y hok]
    simp only [star_mul, star_prod, star_pow, star_neg, star_one, conjugatedResidual]
    ring
  · rw [if_neg hok, if_neg hok, mul_zero]

theorem remainingPolynomialInj_original_pi (S : Finset (Ideal O)) (L : ι → Finset (Ideal O))
    (J : Finset ι) (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) :
    remainingPolynomialInj S L J x coeff η W Z r z G u =
      ∑ q ∈ ((Finset.univ \ J).pi L).filter (PiOK (Finset.univ \ J) (assignedIdeal L J x)),
        (∏ i ∈ (Finset.univ \ J).attach, star (coeff i.val (q i.val i.property))) *
        residualNormalizedPolynomial S (assignedIdeal L J x * survivingProduct (Finset.univ \ J) q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _ => 1)
          (fun v => star (W v)) Z r z G u := by
  rw [Finset.sum_filter, ← sum_remaining_original]
  unfold remainingPolynomialInj
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with hq
  · unfold remainingIdeal survivingProduct remainingPi
    rw [remaining_product_attach J (fun i => star (coeff i.val (q i).val)),
      remaining_product_attach J (fun i => (q i).val)]
  · rfl

/-! ## Energy of the injective assigned family -/

/-- The baseline `assignedTerm` with the `PiOK` remaining residual. -/
def assignedTermInj (S : Finset (Ideal O)) (L : ι → Finset (Ideal O)) (J : Finset ι)
    (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  (∏ i : ↥J, coeff i.val (x i).val) * (moebius (assignedIdeal L J x) : ℂ) *
    (Z^(-G) : ℝ) * η (assignedIdeal L J x)^2 * (idealRowHom u (assignedIdeal L J x))^2 *
    star (remainingResidualInj S L J x coeff η (fun _ => 1) W Z r z G u)

theorem assignedTermInj_norm_le (S : Finset (Ideal O)) (L : ι → Finset (Ideal O))
    (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (J : Finset ι) (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (hj : Admissible (assignedIdeal L J x)) (hη : ‖η (assignedIdeal L J x)‖ ≤ 1)
    (W : ℝ → ℂ) (Z r z G : ℝ) (hZ : 0 < Z) (u : O) :
    ‖assignedTermInj S L J x coeff η W Z r z G u‖ ≤
      assignedMass L J x coeff Z G * ‖remainingPolynomialInj S L J x coeff η W Z r z G u‖ := by
  have hμ : ‖(moebius (assignedIdeal L J x) : ℂ)‖ = 1 := by simp [hj.2.1.moebius_eq]
  have hrow : ‖idealRowHom u (assignedIdeal L J x)‖^2 ≤ 1 := by
    have hh := admissible_row_four_le_one _ hj u
    nlinarith [sq_nonneg (‖idealRowHom u (assignedIdeal L J x)‖^2-1)]
  have hmass := assignedMass_nonneg L J x coeff Z G hZ
  have he : ‖η (assignedIdeal L J x)‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hη
  rw [assignedTermInj, remainingResidualInj_eq_polynomial S L hprime]
  simp only [norm_mul, norm_pow, norm_star, norm_neg, norm_one, one_pow, one_mul,
    hμ, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le (-G))]
  change assignedMass L J x coeff Z G * ‖η (assignedIdeal L J x)‖^2 *
    ‖idealRowHom u (assignedIdeal L J x)‖^2 *
    ‖remainingPolynomialInj S L J x coeff η W Z r z G u‖ ≤ _
  calc
    _ ≤ assignedMass L J x coeff Z G * 1 * 1 *
      ‖remainingPolynomialInj S L J x coeff η W Z r z G u‖ := by
      gcongr
    _ = _ := by ring

theorem assignedTermInj_energy_le (S : Finset (Ideal O)) (L : ι → Finset (Ideal O))
    (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (J : Finset ι) (x : Assigned L J) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (hj : Admissible (assignedIdeal L J x)) (hη : ‖η (assignedIdeal L J x)‖ ≤ 1)
    (W : ℝ → ℂ) (Z r z G : ℝ) (hZ : 0 < Z) (rows : Finset O) (w : O → ℝ) (hw : ∀ u, 0 ≤ w u) :
    (∑ u ∈ rows, w u * ‖assignedTermInj S L J x coeff η W Z r z G u‖^2) ≤
      (assignedMass L J x coeff Z G)^2 *
      ∑ u ∈ rows, w u * ‖remainingPolynomialInj S L J x coeff η W Z r z G u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _)
      (assignedTermInj_norm_le S L hprime J x coeff η hj hη W Z r z G hZ u) 2) (hw u)
  convert hh using 1; ring

theorem assigned_family_energy_inj (S : Finset (Ideal O)) (L : ι → Finset (Ideal O))
    (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (J : Finset ι) (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (hj : ∀ x ∈ asgInj L J, Admissible (assignedIdeal L J x))
    (hη : ∀ x : Assigned L J, ‖η (assignedIdeal L J x)‖ ≤ 1)
    (W : ℝ → ℂ) (Z r z G : ℝ) (hZ : 0 < Z) (rows : Finset O) (w : O → ℝ) (hw : ∀ u, 0 ≤ w u) :
    (∑ u ∈ rows, w u * ‖∑ x ∈ asgInj L J, assignedTermInj S L J x coeff η W Z r z G u‖^2) ≤
      (∑ x ∈ asgInj L J, assignedMass L J x coeff Z G *
        Real.sqrt (∑ u ∈ rows, w u * ‖remainingPolynomialInj S L J x coeff η W Z r z G u‖^2))^2 := by
  refine (finite_weighted_triangle (asgInj L J) rows w hw
    (fun x u => assignedTermInj S L J x coeff η W Z r z G u)).trans ?_
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
  apply Finset.sum_le_sum
  intro x hx
  have hh := Real.sqrt_le_sqrt (assignedTermInj_energy_le S L hprime J x coeff η
    (hj x hx) (hη x) W Z r z G hZ rows w hw)
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (assignedMass_nonneg L J x coeff Z G hZ)] at hh

theorem original_energy_of_remaining_inj (S : Finset (Ideal O)) (L : ι → Finset (Ideal O))
    (hprime : ∀ i, ∀ P ∈ L i, Prime P)
    (coeff : ι → Ideal O → ℂ) (η : Ideal O →* ℂ)
    (hj : ∀ J : Finset ι, ∀ x ∈ asgInj L J, Admissible (assignedIdeal L J x))
    (hη : ∀ J : Finset ι, ∀ x : Assigned L J, ‖η (assignedIdeal L J x)‖ ≤ 1)
    (W : ℝ → ℂ) (Z r z : ℝ) (G : Finset ι → ℝ) (hZ : 0 < Z)
    (rows : Finset O) (w : O → ℝ) (hw : ∀ u, 0 ≤ w u) (E : ℝ) (hE : 0 ≤ E)
    (hres : ∀ J : Finset ι, ∀ x ∈ asgInj L J,
      (∑ u ∈ rows, w u * ‖remainingPolynomialInj S L J x coeff η W Z r z (G J) u‖^2) ≤ E) :
    (∑ u ∈ rows, w u * ‖∑ q ∈ tupInj L, (∏ i, coeff i (q i).val) *
      originalTotalPolynomial S (∏ i, (q i).val) η (fun _ => 1) W Z r z u‖^2) ≤
      (∑ J ∈ Finset.univ.powerset, ∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J))^2 * E := by
  have heq (u : O) :
      (∑ q ∈ tupInj L, (∏ i, coeff i (q i).val) *
        originalTotalPolynomial S (∏ i, (q i).val) η (fun _ => 1) W Z r z u) =
      ∑ J ∈ Finset.univ.powerset, ∑ x ∈ asgInj L J,
        assignedTermInj S L J x coeff η W Z r z (G J) u :=
    original_selected_overlap_inj S L hprime coeff η (fun _ => 1) W Z r z G hZ u
  simp_rw [heq]
  have hroot (J : Finset ι) :
      Real.sqrt (∑ u ∈ rows, w u * ‖∑ x ∈ asgInj L J,
        assignedTermInj S L J x coeff η W Z r z (G J) u‖^2) ≤
      (∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J)) * Real.sqrt E := by
    have hm : 0 ≤ ∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J) :=
      Finset.sum_nonneg (fun x _ => assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hb := assigned_family_energy_inj S L hprime J coeff η (hj J) (hη J)
      W Z r z (G J) hZ rows w hw
    have hc : (∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J) *
        Real.sqrt (∑ u ∈ rows, w u * ‖remainingPolynomialInj S L J x coeff η W Z r z (G J) u‖^2)) ≤
        (∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J)) * Real.sqrt E := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hres J x hx))
        (assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hn : 0 ≤ ∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J) *
        Real.sqrt (∑ u ∈ rows, w u * ‖remainingPolynomialInj S L J x coeff η W Z r z (G J) u‖^2) :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (assignedMass_nonneg L J x coeff Z (G J) hZ)
        (Real.sqrt_nonneg _))
    have hh := Real.sqrt_le_sqrt (hb.trans (pow_le_pow_left₀ hn hc 2))
    rwa [Real.sqrt_sq (mul_nonneg hm (Real.sqrt_nonneg E))] at hh
  refine (finite_weighted_triangle Finset.univ.powerset rows w hw
    (fun J u => ∑ x ∈ asgInj L J, assignedTermInj S L J x coeff η W Z r z (G J) u)).trans ?_
  calc
    _ ≤ (∑ J ∈ Finset.univ.powerset,
        (∑ x ∈ asgInj L J, assignedMass L J x coeff Z (G J)) * Real.sqrt E)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
      exact Finset.sum_le_sum (fun J _ => hroot J)
    _ = _ := by rw [← Finset.sum_mul, mul_pow, Real.sq_sqrt hE]

theorem original_energy_with_assigned_count_inj (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    (hK : Fintype.card ι ≤ K) (S : Finset (Ideal O)) (L : ι → Finset (Ideal O))
    (hp : ∀ i, ∀ P ∈ L i, Prime P) (ell : ι → ℝ)
    (hL : ∀ i, ∀ P ∈ L i, P ≠ 0 ∧ (P.absNorm : ℝ) ≤ b*U^(ell i))
    (coeff : ι → Ideal O → ℂ) (hc : ∀ i, ∀ P ∈ L i, ‖coeff i P‖ ≤ 1) (η : Ideal O →* ℂ)
    (hj : ∀ J : Finset ι, ∀ x ∈ asgInj L J, Admissible (assignedIdeal L J x))
    (hη : ∀ J : Finset ι, ∀ x : Assigned L J, ‖η (assignedIdeal L J x)‖ ≤ 1)
    (W : ℝ → ℂ) (r z : ℝ) (rows : Finset O) (w : O → ℝ) (hw : ∀ u, 0 ≤ w u) (E : ℝ) (hE : 0 ≤ E)
    (hres : ∀ J : Finset ι, ∀ x ∈ asgInj L J,
      (∑ u ∈ rows, w u * ‖remainingPolynomialInj S L J x coeff η W U r z (∑ i ∈ J, ell i) u‖^2) ≤ E) :
    (∑ u ∈ rows, w u * ‖∑ q ∈ tupInj L, (∏ i, coeff i (q i).val) *
      originalTotalPolynomial S (∏ i, (q i).val) η (fun _ => 1) W U r z u‖^2) ≤
      ((2:ℝ)^K * assignedConstant K b)^2 * E := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  refine (original_energy_of_remaining_inj S L hp coeff η hj hη W U r z
    (fun J => ∑ i ∈ J, ell i) hU0 rows w hw E hE hres).trans ?_
  apply mul_le_mul_of_nonneg_right _ hE
  apply pow_le_pow_left₀
    (Finset.sum_nonneg (fun J _ => Finset.sum_nonneg
      (fun x _ => assignedMass_nonneg L J x coeff U (∑ i ∈ J, ell i) hU0)))
  refine le_trans ?_ (all_assignedMass_sum_le K hb hU hK L ell hL coeff hc)
  apply Finset.sum_le_sum
  intro J _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ => assignedMass_nonneg L J x coeff U (∑ i ∈ J, ell i) hU0)

/-! ## Arithmetic of injective tuples -/

theorem assigned_admissible_inj (L : ι → Finset (Ideal O)) (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hs : ∀ i, ∀ P ∈ L i, Supported P) (J : Finset ι) (x : Assigned L J)
    (hx : x ∈ asgInj L J) : Admissible (assignedIdeal L J x) :=
  ⟨(tuple_supported (fun i : ↥J => L i.val) (fun i => hs i.val) x).1,
    tuple_product_squarefree _ (fun i => hp i.val _ (x i).property)
      (Finset.mem_filter.mp hx).2,
    (tuple_supported (fun i : ↥J => L i.val) (fun i => hs i.val) x).2⟩

theorem remaining_tuple_admissible_inj (L : ι → Finset (Ideal O)) (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hs : ∀ i, ∀ P ∈ L i, Supported P) (J : Finset ι) (x : Assigned L J)
    (hx : x ∈ asgInj L J) (t : ∀ i ∈ Finset.univ \ J, Ideal O)
    (ht : t ∈ ((Finset.univ \ J).pi L).filter (PiOK (Finset.univ \ J) (assignedIdeal L J x))) :
    Admissible (assignedIdeal L J x * survivingProduct (Finset.univ \ J) t) := by
  obtain ⟨htp, hok⟩ := Finset.mem_filter.mp ht
  rw [← remainingIdeal_fromPi L J t htp, ← joinTuple_product]
  have hinj := (join_injective_iff L hp J x (remainingFromPi L J t htp)).mpr
    ⟨(Finset.mem_filter.mp hx).2, hok⟩
  exact ⟨(tuple_supported L hs _).1,
    tuple_product_squarefree _ (fun i => hp i _ (joinTuple L J x _ i).property) hinj,
    (tuple_supported L hs _).2⟩

theorem remaining_tuple_outside_inj (L : ι → Finset (Ideal O)) (E : Finset (Ideal O))
    (hE : ∀ P ∈ E, Prime P) (hout : ∀ i, ∀ P ∈ L i, outside E P) (J : Finset ι)
    (x : Assigned L J) (j : Ideal O) (t : ∀ i ∈ Finset.univ \ J, Ideal O)
    (ht : t ∈ ((Finset.univ \ J).pi L).filter (PiOK (Finset.univ \ J) j)) :
    outside E (assignedIdeal L J x * survivingProduct (Finset.univ \ J) t) :=
  remaining_tuple_outside L E hE hout J x t (Finset.mem_filter.mp ht).1

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.original_energy_with_assigned_count_inj
#print axioms Qrh.MarkedAnchor.Inverse.Inj.remaining_tuple_admissible_inj
