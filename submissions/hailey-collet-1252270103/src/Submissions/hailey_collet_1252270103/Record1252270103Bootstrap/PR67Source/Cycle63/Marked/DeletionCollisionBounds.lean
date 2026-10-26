import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionInverseSlots
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionCollisionAlgebra
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion
local notation "O" => HeckeFamily.O

/-- Any collision block of at least two slots has bounded absolute mass.
Only two square-summable coefficient vectors are needed; all remaining
factors use their uniform pointwise bound. -/
theorem collision_block_mass {I A : Type*} [Fintype A]
    (J : Finset I) (v : I→A→ℝ) (B L : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hJ : 2≤J.card) (hv0 : ∀i∈J,∀p,0≤v i p)
    (hv : ∀i∈J,∀p,v i p≤B) (henergy : ∀i∈J,(∑p,(v i p)^2)≤L*B^2) :
    (∑p,∏i∈J,v i p)≤L*B^J.card := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1<J.card)
  have hj' : j∈J.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  let T := (J.erase i).erase j
  have hTcard : T.card+2=J.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hj',Finset.card_erase_of_mem hi]
    omega
  have hprod (p : A) : (∏k∈J,v k p)=v i p*v j p*(∏k∈T,v k p) := by
    rw [←Finset.mul_prod_erase J (fun k=>v k p) hi,
      ←Finset.mul_prod_erase (J.erase i) (fun k=>v k p) hj']
    dsimp [T]
    ring
  have hrem (p : A) : (∏k∈T,v k p)≤B^T.card := by
    calc
      _≤∏k∈T,B := Finset.prod_le_prod₀
        (fun k hk=>hv0 k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)) p)
        (fun k hk=>hv k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)) p)
      _=_ := Finset.prod_const _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A) (v i) (v j)
  have henergyprod : (∑p,(v i p)^2)*(∑p,(v j p)^2)≤(L*B^2)^2 := by
    rw [pow_two]
    exact mul_le_mul (henergy i hi) (henergy j hj)
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (mul_nonneg hL (sq_nonneg _))
  have hpair : (∑p,v i p*v j p)≤L*B^2 := by
    have hh := hcs.trans henergyprod
    have hn : 0≤L*B^2 := mul_nonneg hL (sq_nonneg _)
    nlinarith
  calc
    _ = ∑p,v i p*v j p*(∏k∈T,v k p) := Finset.sum_congr rfl (fun p _=>hprod p)
    _ ≤ ∑p,v i p*v j p*B^T.card := Finset.sum_le_sum (fun p _=>
      mul_le_mul_of_nonneg_left (hrem p) (mul_nonneg (hv0 i hi p) (hv0 j hj p)))
    _ = (∑p,v i p*v j p)*B^T.card := by rw [Finset.sum_mul]
    _ ≤ (L*B^2)*B^T.card := mul_le_mul_of_nonneg_right hpair (pow_nonneg hB _)
    _ = L*B^J.card := by rw [mul_assoc,←pow_add,Nat.add_comm 2,hTcard]

def normalizedPrimeCoeff (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ)
    (I : Ideal O) : ℂ := if I∈pool then (Real.sqrt P:ℂ)⁻¹*β I else 0

theorem normalizedPrimeCoeff_bound (pool : Finset (Ideal O)) (β : Ideal O→ℂ)
    (P B : ℝ) (hP : 1≤P) (hB : 0≤B) (hβ : ∀I∈pool,‖β I‖≤B) (I : Ideal O) :
    ‖normalizedPrimeCoeff pool β P I‖≤B := by
  unfold normalizedPrimeCoeff
  split_ifs with hI
  · rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : 1≤Real.sqrt P := (Real.le_sqrt (by norm_num) (zero_le_one.trans hP)).mpr (by simpa using hP)
    exact (mul_le_mul_of_nonneg_left (hβ I hI) (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
      (mul_le_of_le_one_left hB (inv_le_one_of_one_le₀ hs))
  · simpa using hB

/-- Actual normalized prime coefficients have uniformly bounded square
mass, without any separation condition between different slots. -/
theorem normalizedPrimeCoeff_energy (atoms pool : Finset (Ideal O)) (β : Ideal O→ℂ)
    (P B : ℝ) (hP : 1≤P) (_hB : 0≤B) (hβ : ∀I∈pool,‖β I‖≤B)
    (hp : ∀I∈pool,I≠0) (hN : ∀I∈pool,(I.absNorm:ℝ)≤2*P) :
    (∑I∈atoms,‖normalizedPrimeCoeff pool β P I‖^2)≤256*B^2 := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hs : 0<Real.sqrt P := Real.sqrt_pos.mpr hPp
  have hc : (pool.card:ℝ)≤256*P := by
    have hh := CenteredMomentSecondDiagonal.divisible_ideal_card pool 1 one_ne_zero hp
      (fun I _=>one_dvd I) (2*P) (by positivity) hN
    simp only [map_one,Nat.cast_one,div_one] at hh
    nlinarith
  have hterm (I : Ideal O) (hI : I∈pool) :
      ‖normalizedPrimeCoeff pool β P I‖^2≤B^2/P := by
    rw [normalizedPrimeCoeff,ite_eq_left hI,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hs.le,mul_pow,inv_pow,Real.sq_sqrt hPp.le]
    rw [div_eq_mul_inv,mul_comm (B^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hβ I hI) 2) (inv_nonneg.mpr hPp.le)
  have he : (∑I∈atoms,‖normalizedPrimeCoeff pool β P I‖^2)=
      ∑I∈atoms∩pool,‖normalizedPrimeCoeff pool β P I‖^2 := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hnot : I∉pool := fun hp=>hn (Finset.mem_inter.mpr ⟨hI,hp⟩)
    simp [normalizedPrimeCoeff,hnot]
  rw [he]
  calc
    _≤∑I∈pool,‖normalizedPrimeCoeff pool β P I‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _=>sq_nonneg _)
    _≤∑I∈pool,B^2/P := Finset.sum_le_sum hterm
    _=(pool.card:ℝ)*(B^2/P) := by simp
    _≤(256*P)*(B^2/P) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=256*B^2 := by field_simp

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
