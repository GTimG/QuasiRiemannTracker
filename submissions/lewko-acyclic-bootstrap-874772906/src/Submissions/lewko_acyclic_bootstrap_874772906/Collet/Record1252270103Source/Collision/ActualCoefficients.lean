/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The actual canonical pools, relative characters, annular coefficients and
natural row zeros meet the collision bounds uniformly down to scale P=1. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Energy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckePrimeAnnular HeckeDyadic
open CenteredMomentPrimeSlot CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentAbsoluteEnergy ConcretePrimeRowBridge
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O" => HeckeFamily.O

theorem actual_annular_coefficient_bound (W : ℝ→ℂ) (hW : Continuous W)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) (lo hi : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ (χ : Character) (P σ v : ℝ),0<P →σ∈Set.Icc lo hi →
      ∀I : Ideal O,‖idealCoeff χ I*annularWeight W P σ v I‖≤B := by
  obtain ⟨B,hB,hbound⟩ := fixed_profile_norm_bound W hW 1 2 lo hi (by norm_num)
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro χ P σ v hP hσ I
  by_cases hz : W ((I.absNorm:ℝ)/P)=0
  · simp only [annularWeight,hz,zero_mul,mul_zero,norm_zero]
    exact (zero_lt_one.trans_le (le_max_left _ _)).le
  · have hy := hs hz
    have hyp : 0<(I.absNorm:ℝ)/P := zero_lt_one.trans_le hy.1
    have ha : ‖annularWeight W P σ v I‖≤B := by
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hyp]
      simpa only [Complex.neg_re,shift_re] using hbound σ hσ _ hy
    rw [norm_mul]
    exact ((mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)).trans ha).trans
      (le_max_right _ _)

theorem primePool_norm_le (rayM : Ideal O) (H : Subgroup (O⧸rayM)ˣ)
    (P : ℝ) (hP : 0≤P) (I : Ideal O) (hi : I∈primePool rayM H 2 P) :
    I≠0 ∧ (I.absNorm:ℝ)≤2*P := by
  have hm := Finset.mem_filter.mp hi
  refine ⟨hm.2.1.ne_zero,?_⟩
  have hh := (mem_idealsUpTo.mp hm.1).2
  change I.absNorm≤⌊max 1 (2:ℝ)*P⌋₊ at hh
  have hcast := (Nat.cast_le (α:=ℝ)).mpr hh
  have hfloor := Nat.floor_le (show 0≤max 1 (2:ℝ)*P by positivity)
  simpa only [max_eq_right (show (1:ℝ)≤2 by norm_num)] using hcast.trans hfloor

def normalizedRowCoeff (η : Character) (m A z : O) (t : ℝ)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) (I : Ideal O) : ℂ :=
  normalizedPrimeCoeff pool β P I*rowWeight η m A z t I

theorem normalizedRowCoeff_norm (η : Character) (m A z : O) (t : ℝ)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) (I : Ideal O) :
    ‖normalizedRowCoeff η m A z t pool β P I‖≤‖normalizedPrimeCoeff pool β P I‖ := by
  rw [normalizedRowCoeff,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem normalizedSlot_sum_atoms (η : Character) (m A z : O) (t : ℝ)
    (pool atoms : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) (hpool : pool⊆atoms) :
    normalizedSlot η m A z pool β t P=
      ∑I : atoms,normalizedRowCoeff η m A z t pool β P I := by
  rw [Finset.sum_coe_sort]
  unfold normalizedSlot
  rw [rowSlot_eq_weight,Finset.mul_sum]
  calc
    _=∑I∈pool,normalizedRowCoeff η m A z t pool β P I := by
      apply Finset.sum_congr rfl
      intro I hi
      simp only [normalizedRowCoeff,normalizedPrimeCoeff,hi,ite_true]
      ring
    _=∑I∈atoms,normalizedRowCoeff η m A z t pool β P I := by
      apply Finset.sum_subset hpool
      intro I hi hn
      simp [normalizedRowCoeff,normalizedPrimeCoeff,hn]

/-- A single uniform B works before all moving widths, heights, ray labels,
characters and row masks. The mass constant is exactly the existing 256. -/
theorem actual_normalized_coefficient_contract (W : ℝ→ℂ) (hW : Continuous W)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) (lo hi : ℝ) :
    ∃ B : ℝ,1≤B ∧ ∀ (rayM : Ideal O) (H : Subgroup (O⧸rayM)ˣ)
      (χ η : Character) (m A z : O) (P σ v t : ℝ),
      1≤P → σ∈Set.Icc lo hi → ∀atoms : Finset (Ideal O),
      let β := fun I=>idealCoeff χ I*annularWeight W P σ v I
      let pool := primePool rayM H 2 P
      (∀I : atoms,‖normalizedPrimeCoeff pool β P I‖≤B) ∧
      (∑I : atoms,‖normalizedPrimeCoeff pool β P I‖^2)≤256*B^2 ∧
      ∀I : atoms,‖normalizedRowCoeff η m A z t pool β P I‖≤‖normalizedPrimeCoeff pool β P I‖ := by
  obtain ⟨B,hB,hbound⟩ := actual_annular_coefficient_bound W hW hs lo hi
  refine ⟨B,hB,?_⟩
  intro rayM H χ η m A z P σ v t hP hσ atoms
  dsimp only
  have hp : 0<P := zero_lt_one.trans_le hP
  have hb := hbound χ P σ v hp hσ
  refine ⟨fun I=>normalizedPrimeCoeff_bound _ _ P B hP (zero_le_one.trans hB) (fun I _=>hb I) I,?_,
    fun I=>normalizedRowCoeff_norm η m A z t _ _ _ I⟩
  rw [Finset.sum_coe_sort atoms (fun I=>‖normalizedPrimeCoeff (primePool rayM H 2 P)
    (fun I=>idealCoeff χ I*annularWeight W P σ v I) P I‖^2)]
  exact normalizedPrimeCoeff_energy atoms _ _ P B hP (zero_le_one.trans hB)
    (fun I _=>hb I) (fun I hi=>(primePool_norm_le rayM H P hp.le I hi).1)
    (fun I hi=>(primePool_norm_le rayM H P hp.le I hi).2)

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.actual_annular_coefficient_bound
#print axioms QRH.Record1252270103Source.Collision.normalizedSlot_sum_atoms
#print axioms QRH.Record1252270103Source.Collision.actual_normalized_coefficient_contract
