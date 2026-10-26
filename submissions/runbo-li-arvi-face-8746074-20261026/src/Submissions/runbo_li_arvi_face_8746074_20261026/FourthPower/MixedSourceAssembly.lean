/- Copyright (c) 2026 Sil. Apache-2.0.
Positive radial summation of actual allocation rows, and the polynomial
cap for their common punctures. Finite phases are controlled outside
the row, never by deleting terms inside its norm.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFrozenSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSourceAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103KernelMass
open MixedCompletedRows CenteredMomentOriginalRadialComparison
open CenteredMomentInductionEnergy CenteredMomentAllocationCost
open CenteredMomentEnergyCapacityRemoval CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentAddedZeroUniform MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem radical_union_norm (R F : Id) (hR : R≠0) (hF : F≠0) (H : Finset PrimeIdeal) :
    ((∏I∈primeSupport (R*F)∪holes H,I).absNorm:ℝ)≤
      (R.absNorm:ℝ)*F.absNorm*(∏I∈holes H,I).absNorm := by
  have hh : (∏I∈holes H,I)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun I hI=>(holes_prime H I hI).ne_zero)
  have hd : (∏I∈primeSupport (R*F)∪holes H,I)∣
      (∏I∈primeSupport (R*F),I)*(∏I∈holes H,I) := by
    refine ⟨∏I∈primeSupport (R*F)∩holes H,I,?_⟩
    exact Finset.prod_union_inter.symm
  have hr : (∏I∈primeSupport (R*F),I)∣R*F :=
    IdealMobiusDivisorSum.support_product_dvd (mul_ne_zero hR hF) (Finset.Subset.refl _)
  have hd' : (∏I∈primeSupport (R*F)∪holes H,I)∣R*F*(∏I∈holes H,I) :=
    hd.trans (mul_dvd_mul hr (dvd_refl _))
  have hn := CenteredExceptionalCount.norm_le_of_dvd (mul_ne_zero (mul_ne_zero hR hF) hh) hd'
  simpa only [map_mul,Nat.cast_mul] using hn

theorem radical_union_cap (R F : Id) (hR : R≠0) (hF : F≠0) (H : Finset PrimeIdeal)
    (Z BR BF BH : ℝ) (hZ : 0<Z)
    (hRc : (R.absNorm:ℝ)≤Z^BR) (hFc : (F.absNorm:ℝ)≤Z^BF)
    (hHc : ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH) :
    ((∏I∈primeSupport (R*F)∪holes H,I).absNorm:ℝ)≤Z^(BR+BF+BH) := by
  apply (radical_union_norm R F hR hF H).trans
  have he := mul_le_mul (mul_le_mul hRc hFc (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)) hHc
    (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
  simpa only [Real.rpow_add hZ] using he

/-- Lift the existing finite weighted Cauchy theorem to the compact
radial energy, allowing the phase bound only on retained rows. -/
theorem radial_family {ι : Type*} [Fintype ι]
    (f g : ι→O→ℂ) (mass : ι→ℝ) (E : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hmass : ∀i,0≤mass i) (hfg : ∀i z,keep z→‖f i z‖≤mass i*‖g i z‖)
    (hg : ∀i,radialEnergy (g i) keep Φ K≤E) :
    radialEnergy (fun z=>∑i,f i z) keep Φ K≤(∑i,mass i)^2*E := by
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let rows' := rows.filter keep
  let ρ := fun z : O=>(Φ (‖eisEmbedding z‖^2/K)).re
  have hchild (i : ι) : (∑z∈rows',ρ z*‖g i z‖^2)≤E := by
    have hsum := compact_radial_summable (g i) keep Φ K radial hK hs
    have hh := hsum.sum_le_tsum rows' (fun z _=>by
      split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
    apply (le_of_eq ?_).trans (hh.trans (hg i))
    apply Finset.sum_congr rfl
    intro z hz
    simp only [(Finset.mem_filter.mp hz).2,ite_true]
    ring
  have he := KernelCollisionEnergy.weighted_physical_energy rows' ρ f g mass E
    (fun z _=>hΦ z) hmass (fun i z hz=>hfg i z (Finset.mem_filter.mp hz).2) hchild
  apply (le_of_eq ?_).trans he
  rw [show (∑z∈rows',ρ z*‖∑i,f i z‖^2)=
      ∑z∈rows,if keep z then ρ z*‖∑i,f i z‖^2 else 0 by exact Finset.sum_filter _ _]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> ring

theorem radial_phase_sum {ι : Type*} [Fintype ι]
    (phase f : ι→O→ℂ) (E : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hphase : ∀i z,keep z→‖phase i z‖≤1)
    (hf : ∀i,radialEnergy (f i) keep Φ K≤E) :
    radialEnergy (fun z=>∑i,phase i z*f i z) keep Φ K≤(Fintype.card ι:ℝ)^2*E := by
  have he := radial_family (fun i z=>phase i z*f i z) f (fun _=>1) E keep Φ K radial hK hs hΦ
    (fun _=>zero_le_one) (by
      intro i z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hphase i z hz) (norm_nonneg _)) hf
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using he

theorem genuine_count_squared (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N →
    ∀S : ι→Finset Id,∀D : Id,D≠0 →
      ((CenteredMomentCommonAllocationSum.actualAllocations S D).card:ℝ)^2≤C*(D.absNorm:ℝ)^ε := by
  obtain ⟨C,hC,hcard⟩ := actualAllocations_uniform_small_power N (ε/2) (half_pos hε)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ hn S D hD
  calc
    _ ≤ (C*(D.absNorm:ℝ)^(ε/2))^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard hn S D hD) 2
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      congr 2
      norm_num

theorem fixed_count_squared {ι : Type*} [Fintype ι] [Nonempty ι] (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀S : ι→Finset Id,∀F : Id,F≠0 →
      ((MixedFixedSupport.boundedLabels S F).card:ℝ)^2≤C*(F.absNorm:ℝ)^ε := by
  obtain ⟨C,hC,hcard⟩ := MixedFixedSupport.bounded_labels_subpower (ι:=ι) (ε/2) (half_pos hε)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro S F hF
  calc
    _ ≤ (C*(F.absNorm:ℝ)^(ε/2))^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard S F hF) 2
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      congr 2
      norm_num

/-- Every selected occurrence, including repeated selections of one
prime in different coordinates, divides the actual frozen product. -/
theorem selected_product_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Id) (a : Allocation D (Finset.univ : Finset ι)) (B : ι→Id)
    (hB : ∀i,B i≠0) (ha : allocationTerm D Finset.univ B a≠0) :
    ((∏i,selectedDivisor D Finset.univ a i).absNorm:ℝ)≤(∏i,B i).absNorm := by
  have hd : (∏i,selectedDivisor D Finset.univ a i)∣∏i,B i :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>selectedDivisor_dvd D Finset.univ B a ha i)
  exact CenteredExceptionalCount.norm_le_of_dvd
    (Finset.prod_ne_zero_iff.mpr (fun i _=>hB i)) hd

theorem allocation_term_norm {ι : Type*} [DecidableEq ι]
    (D : Id) (s : Finset ι) (B : ι→Id) (a : Allocation D s) :
    ‖allocationTerm D s B a‖≤1 := by
  simp only [allocationTerm,norm_prod,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  calc
    _ ≤ ∏P : IdealMobiusDivisorSum.primeSupport D,(1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _=>Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      intro P hP
      calc
        _ ≤ ∏_i∈(a P).val,(1:ℝ) := by
          apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
          intro i hi
          split_ifs <;> norm_num
        _ = 1 := Finset.prod_const_one
    _ = 1 := Finset.prod_const_one

theorem frozen_phase_norm {ι : Type*} [Fintype ι]
    (H D : Id) (B : Tuple ι)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (χ : Character) :
    ‖frozenWeight H B*allocationTerm D Finset.univ B a*idealCoeff χ (finiteTupleProduct B)‖≤1 := by
  have hw : ‖frozenWeight H B‖≤1 := by
    unfold frozenWeight
    split_ifs <;> norm_num
  rw [norm_mul,norm_mul]
  have hp : ‖frozenWeight H B‖*‖allocationTerm D Finset.univ B a‖≤1 := by
    calc
      _ ≤ 1*1 := mul_le_mul hw (allocation_term_norm D Finset.univ B a)
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc
    _ ≤ 1*1 := mul_le_mul hp (idealCoeff_norm_le_one _ _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end
end Candidate.FourthPower.MixedSourceAssembly
