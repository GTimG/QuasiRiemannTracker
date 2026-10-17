/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B003
import Candidate.Bundles.B054
import Candidate.Bundles.B057
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralClassPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPhaseAmplitude
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount

/- BEGIN ORIGINAL Cycle25.Numerator.FiniteCollect; sha256 edab780d862b0b807ad07b69889475887d2c3790e26570b30ba7e56465054485 -/
section
                                  
                                        
                                                                 

/-! The literal finite row/error-subset collection after numerator bounds. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem finite_array_weight_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι→ℂ) (F : ι→κ→ℂ) (A : ℝ) (B : κ→ℝ) (hA : 0≤A)
    (ha : ∀i∈s,‖a i‖≤A) (hB : ∀j∈t,(∑i∈s,‖F i j‖)≤B j) :
    ‖∑i∈s,a i*(∑j∈t,F i j)‖≤A*(∑j∈t,B j) := by
  calc
    _ ≤ ∑i∈s,‖a i*(∑j∈t,F i j)‖ := norm_sum_le _ _
    _ ≤ ∑i∈s,A*(∑j∈t,‖F i j‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (ha i hi) (norm_sum_le _ _) (norm_nonneg _) hA
    _ = A*(∑j∈t,∑i∈s,‖F i j‖) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) hA

theorem reconstructedDyadValue_norm_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (A : ℝ) (B : Finset (Fin K)→ℝ) (hA : 0≤A)
    (ha : ∀u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar S hS hmax η u x z‖≤A)
    (hb : ∀J∈Finset.univ.powerset,
      (∑u∈R,‖errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
        (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
          (-star (idealRowHom u.val P.val.val)))‖)≤B J) :
    ‖reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y‖≤A*(∑J∈Finset.univ.powerset,B J) :=
  finite_array_weight_bound R Finset.univ.powerset _ _ A B hA ha hb


open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem reconstructedDyadValue_amplitude_partition {K : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (slots : Finset Slot) (U cap mesh : ℝ) (hm : 0 < mesh)
    (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y =
      ∑bin : BinLabel slots cap mesh,reconstructedDyadValue S hS hmax η
        (amplitudeRows R slots U cap mesh hm widths Q bin) T hT W Yp x z W1 Y := by
  unfold reconstructedDyadValue
  exact sum_amplitudeRows R slots U cap mesh hm widths Q _

theorem reconstructedDyadValue_class_uniform {K : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (slots : Finset Slot) (U cap mesh : ℝ) (hm : 0 < mesh) (hcap : cap≤1/2)
    (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) (A : ℝ) (hA : 0≤A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows R slots U cap mesh hm widths Q bin).Nonempty →
      ‖reconstructedDyadValue S hS hmax η
        (amplitudeRows R slots U cap mesh hm widths Q bin) T hT W Yp x z W1 Y‖≤A) :
    ‖reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [reconstructedDyadValue_amplitude_partition S hS hmax η R T hT W Yp x z W1 Y
    slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows R slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,reconstructedDyadValue,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm


/-- Empty physical prime pools already make the original integrated numerator
zero; no arbitrary coefficient choice is made in this case. -/
theorem integratedDyadValue_zero_of_no_labels {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : SchwartzMap ℝ ℂ) (Y : ℝ)
    (hempty : ¬Nonempty (∀i,T i)) :
    FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z = 0 := by
  letI : IsEmpty (∀i,T i) := not_nonempty_iff.mp hempty
  simp only [FullWContour.integratedDyadValue,Finset.univ_eq_empty,Finset.sum_empty,Finset.sum_const_zero]

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.FiniteCollect -/

/- BEGIN ORIGINAL Cycle25.Numerator.PhysicalFront; sha256 1366fb5221bb47e40d1aeb132fd2f5d75c3e42aca9e94f30e9700e01055c2677 -/
section
                                                           
                                  
                                                             
                                                             
                                                     
                                                           

/-! Exact front factors of the reconstructed numerator and source-pool geometry.
All prime amplitudes retain their original canonical zero extensions. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace Cycle25.Numerator
open Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily
open ProbeRaySlots HeckeInverseAmplification CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem physicalMainPool_sum (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (u : FreeRow)
    (W : ℝ→ℂ) (a b Y : ℝ) (ha : 0 < a) (hab : a ≤ b) (hY : 0 < Y)
    (hW : Function.support W⊆Set.Ioo a b) (hS : ∀P∈S,(P.absNorm:ℝ) ≤ a*Y) (z : ℂ) :
    (∑P:pool (RayQuotient.identityClass M H) S a b Y,
      physicalSlotWeight P.val W Y z*(-star (idealRowHom u.val P.val.val)))=
      -(Y:ℂ)^(z-1/2)*HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b Y z := by
  unfold physicalSlotWeight
  rw [Finset.sum_coe_sort (pool (RayQuotient.identityClass M H) S a b Y)
    (fun P=>W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val)))]
  exact central_phase_eq_amplitude M H S u.val W a b Y ha hab hY hW hS z

theorem physicalMainPool_product {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (u : FreeRow) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (a b : ℝ) (Y : Fin K→ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hY : ∀j,0 < Y j)
    (hW : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hS : ∀j,∀P∈S,(P.absNorm:ℝ) ≤ a*Y j) (z : ℂ) :
    (∏j:{i:Fin K//i∉J},∑P:pool (RayQuotient.identityClass M H) S a b (Y j.val),
      physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val)))=
      ∏j:{i:Fin K//i∉J},(-(Y j.val:ℂ)^(z-1/2)*
        HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j.val) b (Y j.val) z) := by
  apply Finset.prod_congr rfl
  intro j _
  exact physicalMainPool_sum M H S u (W j.val) a b (Y j.val) ha hab
    (hY j.val) (hW j.val) (hS j.val) z

theorem physicalMainPool_product_norm {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (u : FreeRow) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (a b : ℝ) (Y : Fin K→ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hY : ∀j,0 < Y j)
    (hW : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hS : ∀j,∀P∈S,(P.absNorm:ℝ) ≤ a*Y j) (z : ℂ) :
    ‖∏j:{i:Fin K//i∉J},∑P:pool (RayQuotient.identityClass M H) S a b (Y j.val),
      physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val))‖=
      (∏j:{i:Fin K//i∉J},(Y j.val)^(z.re-1/2))*
        ‖∏j:{i:Fin K//i∉J},HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j.val) b (Y j.val) z‖ := by
  rw [physicalMainPool_product M H S u J W a b Y ha hab hY hW hS z,norm_prod,norm_prod,
    ←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (hY j.val)]
  norm_num

/-- On a row dyad whose lower edge is U, no fixed constant is lost. -/
theorem frequencyWeight_dyad_bound (u : FreeRow) (z : ℂ) (U r : ℝ)
    (hU : 0 < U) (hr : 0 ≤ r) (hz : z.re=r) (hu : U ≤ rowNorm u) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤ U^(-r) := by
  rw [frequencyWeight_ideal_norm,hz]
  exact Real.rpow_le_rpow_of_nonpos hU hu (neg_nonpos.mpr hr)

/-- The source slots used by the actual full-w cells. -/
def sourcePrimePool {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (j : Fin D.N) :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.ell j))

theorem source_complex_support_open {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    Function.support (F.W:ℝ→ℂ)⊆Set.Ioo 1 2 := by
  intro y hy
  apply F.support
  intro hw
  exact hy (by rw [F.complex_eq,hw];simp)

theorem source_prime_pool_outside {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (j : Fin D.N)
    (P : ProbePhysical.PrimeIdeal) (hP : P∈sourcePrimePool F Z j) : P.val∉F.S :=
  ((mem_pool _ _ _ _ _ P).mp hP).2.2.2

/-- Every restricted tuple and full tuple is injective, every prime is coprime
with the fixed external character, and all prime norms exceed four. -/
theorem source_prime_reconstruction_geometry {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop, 1 ≤ Z ∧
      (∀J : Finset (Fin D.N),∀P:(∀i:J,sourcePrimePool F Z i.val),
        Function.Injective (fun i=>(P i).val)) ∧
      (∀P:(∀i,sourcePrimePool F Z i),Function.Injective (fun i=>(P i).val)) ∧
      (∀j P,P∈sourcePrimePool F Z j→IsCoprime P.val η.modulus) ∧
      (∀j P,P∈sourcePrimePool F Z j→(4:ℝ) ≤ P.val.absNorm) ∧
      (∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j)) := by
  have hlarge : ∀ᶠZ : ℝ in atTop,∀j:Fin D.N,
      4 ≤ Z^(D.ell j) ∧ (η.modulus.absNorm:ℝ) < Z^(D.ell j) ∧
        ∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j) := by
    apply Filter.eventually_all.mpr
    intro j
    have ht := tendsto_rpow_atTop (D.slots_bounds j).1
    filter_upwards [ht.eventually (eventually_ge_atTop (4:ℝ)),
      ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
      ht.eventually (eventually_ge_atTop (∑P∈F.S,(P.absNorm:ℝ)))] with Z h4 hη hS
    refine ⟨h4,hη,?_⟩
    intro P hP
    exact (Finset.single_le_sum (fun Q _=>Nat.cast_nonneg _) hP).trans hS
  filter_upwards [hlarge,eventually_ge_atTop (1:ℝ),
    power_pools_eventually_disjoint (RayQuotient.identityClass F.modulus ⊤) F.S
      (fun _:Fin D.N=>1) (fun _=>2) D.ell (fun _=>by norm_num)
      (fun _=>by norm_num) D.slots_injective] with Z hlarge hZ hdis
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hall : ∀P:(∀i,sourcePrimePool F Z i),Function.Injective (fun i=>(P i).val) := by
    intro P i j he
    dsimp only at he
    by_contra hij
    exact Finset.disjoint_left.mp (hdis i j hij) (P i).property
      (by rw [he];exact (P j).property)
  refine ⟨hZ,?_,hall,?_,?_,fun j=>(hlarge j).2.2⟩
  · intro J P i j he
    dsimp only at he
    apply Subtype.ext
    by_contra hij
    exact Finset.disjoint_left.mp (hdis i.val j.val hij) (P i).property
      (by rw [he];exact (P j).property)
  · intro j P hP
    have hp := pool_norm_bounds (RayQuotient.identityClass F.modulus ⊤) F.S
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2)
      (Real.rpow_pos_of_pos hZpos (D.ell j)) P hP
    apply prime_coprime_of_norm_gt η P
    exact (hlarge j).2.1.trans (by simpa only [mul_one] using hp.1)
  · intro j P hP
    have hp := pool_norm_bounds (RayQuotient.identityClass F.modulus ⊤) F.S
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2)
      (Real.rpow_pos_of_pos hZpos (D.ell j)) P hP
    exact (hlarge j).1.trans (by simpa only [mul_one] using hp.1.le)


/-- Exact source normalization, for the complex source profile used in moments. -/
theorem source_main_product {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (hZ : 0 < Z)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j))
    (u : FreeRow) (J : Finset (Fin D.N)) (z : ℂ) :
    (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
      physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val)))=
      ∏j:{i:Fin D.N//i∉J},(-((Z^(D.ell j.val):ℝ):ℂ)^(z-1/2)*
        HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z) := by
  exact physicalMainPool_product F.modulus ⊤ F.S u J (fun _=>F.W) 1 2
    (fun j=>Z^(D.ell j)) (by norm_num) (by norm_num)
    (fun j=>Real.rpow_pos_of_pos hZ _) (fun _=>source_complex_support_open F)
    (fun j P hP=>by simpa only [one_mul] using hS j P hP) z

/-- The total physical normalization for all remaining main slots. -/
theorem source_main_product_norm {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (hZ : 0 < Z)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j))
    (u : FreeRow) (J : Finset (Fin D.N)) (z : ℂ) :
    ‖∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
      physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))‖=
      Z^((∑j:{i:Fin D.N//i∉J},D.ell j.val)*(z.re-1/2))*
        ‖∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude
          F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z‖ := by
  unfold sourcePrimePool
  rw [physicalMainPool_product_norm F.modulus ⊤ F.S u J (fun _=>F.W) 1 2
    (fun j=>Z^(D.ell j)) (by norm_num) (by norm_num)
    (fun j=>Real.rpow_pos_of_pos hZ _) (fun _=>source_complex_support_open F)
    (fun j P hP=>by simpa only [one_mul] using hS j P hP) z]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,Finset.sum_mul]

/-- The norm of the frequency and all literal main-prime factors on a dyad. -/
theorem source_frequency_main_bound {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z U : ℝ) (hZ : 0 < Z) (hU : 0 < U)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j))
    (u : FreeRow) (hu : U ≤ rowNorm u) (J : Finset (Fin D.N))
    (z : ℂ) (hz : z.re=17/50) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩*
      (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
        physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val)))‖ ≤
      U^(-(17/50:ℝ))*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*
        ‖∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude
          F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z‖ := by
  rw [norm_mul,source_main_product_norm F Z hZ hS u J z]
  have hf := frequencyWeight_dyad_bound u z U (17/50) hU (by norm_num) hz hu
  apply (mul_le_mul_of_nonneg_right hf (by positivity)).trans_eq
  rw [hz]
  have he : (∑j:{i:Fin D.N//i∉J},D.ell j.val)*((17/50:ℝ)-1/2)=
      -(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val) := by ring
  rw [he]
  ring

/-- The literal real-profile front factors in FullWCellsAt are the same source
complex profile; this is an identity of functions, with no norm relaxation. -/
theorem source_real_profile_eq {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    (fun (_:Fin D.N) y=>(F.w y:ℂ))=(fun _=>(F.W:ℝ→ℂ)) := by
  funext j y
  exact (F.complex_eq y).symm


/-- Bin upper bounds are applied only to the remaining main slots; their
canonical amplitudes and original zero extensions are unchanged. -/
theorem physicalMainPool_product_bound {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (u : FreeRow) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (a b : ℝ) (Y : Fin K→ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hY : ∀j,0 < Y j)
    (hW : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hS : ∀j,∀P∈S,(P.absNorm:ℝ) ≤ a*Y j) (z : ℂ) (hz : z.re=17/50)
    (U : ℝ) (hU : 0 < U) (width upper : Fin K→ℝ)
    (hQ : ∀j,j∉J→‖HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z‖ ≤
      U^(width j*upper j)) :
    ‖∏j:{i:Fin K//i∉J},∑P:pool (RayQuotient.identityClass M H) S a b (Y j.val),
      physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val))‖ ≤
      (∏j:{i:Fin K//i∉J},(Y j.val)^(-(4/25:ℝ)))*
        U^(∑j:{i:Fin K//i∉J},width j.val*upper j.val) := by
  rw [physicalMainPool_product_norm M H S u J W a b Y ha hab hY hW hS z,hz]
  norm_num only [show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hY j.val).le _))
  rw [norm_prod,Real.rpow_sum_of_pos hU]
  exact Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hQ j.val j.property)

/-- Error and main subsets together retain every physical prime normalization. -/
theorem error_main_scale_product {K : ℕ} (J : Finset (Fin K)) (Y : Fin K→ℝ) (r : ℝ) :
    (∏j:J,(Y j.val)^r)*(∏j:{i:Fin K//i∉J},(Y j.val)^r)=∏j,(Y j)^r := by
  convert Fintype.prod_subtype_mul_prod_subtype (fun j=>j∈J) (fun j=>(Y j)^r) using 1
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem error_main_source_scale {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (ell : Fin K→ℝ) :
    (∏j:J,(Z^(ell j.val))^(-(4/25:ℝ)))*
      (∏j:{i:Fin K//i∉J},(Z^(ell j.val))^(-(4/25:ℝ)))=
      Z^(-(4/25:ℝ)*(∑j,ell j)) := by
  rw [error_main_scale_product J (fun j=>Z^(ell j)) (-(4/25:ℝ))]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul]
  congr 1
  ring

/-- The enlarged moment conductor includes two detector margins. This precise
identity prevents mistaking it for the actual lower edge of the row dyad. -/
theorem frequencyWeight_source_conductor_bound (u : FreeRow) (z : ℂ)
    (Z margin : ℝ) (k : ℕ) (hZ : 1 < Z) (hz : z.re=17/50)
    (hu : u∈dyadicRows 1 k) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤
      Z^((17/25:ℝ)*margin)*(Z^(sourceDyadConductor Z margin k))^(-(17/50:ℝ)) := by
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hlo : (2:ℝ)^k ≤ rowNorm u := by simpa only [one_mul] using (mem_dyadicRows.mp hu).2.1
  apply (frequencyWeight_dyad_bound u z ((2:ℝ)^k) (17/50) (by positivity) (by norm_num) hz hlo).trans_eq
  rw [←sourceDyad_scale hZ k]
  rw [←Real.rpow_mul hZpos.le,←Real.rpow_mul hZpos.le,←Real.rpow_add hZpos]
  unfold sourceDyadConductor
  congr 1
  ring

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.PhysicalFront -/

/- BEGIN ORIGINAL Cycle25.Numerator.PhysicalCollect; sha256 453ccc5be84c91ce3cbdfa735cf4f86078d6c983ad35c254c9522187c3e422ca -/
section
                                      
                                      

/-! Literal physical error-mask contributions and their canonical prime fronts. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def sourceMaskContribution {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (J : Finset (Fin D.N))
    (Z : ℝ) (x z : ℂ) (Y : ℝ) : ℂ :=
  ∑u∈rows,(frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*
    (errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y*
      (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
        physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))))

theorem source_reconstructed_sum_masks {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (Z : ℝ) (x z : ℂ) (Y : ℝ) :
    reconstructedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
      (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y =
      ∑J∈Finset.univ.powerset,sourceMaskContribution F η rows J Z x z Y := by
  unfold reconstructedDyadValue sourceMaskContribution
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem complement_prime_product {D : MomentData} (F : WeightedSourceData D)
    (u : FreeRow) (J : Finset (Fin D.N)) (Z : ℝ) (z : ℂ) :
    (∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z) =
      ∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z :=
  (Finset.prod_subtype (Finset.univ\J) (by simp)
    (fun j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)).symm

theorem source_mask_physical_front {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (J : Finset (Fin D.N))
    (Z : ℝ) (hZ : 0 < Z) (x z : ℂ) (hz : z.re=17/50) (Y : ℝ)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ)≤Z^(D.ell j))
    (A B : ℝ) (hA : 0≤A)
    (ha : ∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤A)
    (hB : (∑u∈rows,‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y*
      (∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)‖)≤B) :
    ‖sourceMaskContribution F η rows J Z x z Y‖ ≤
      A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*B := by
  let En (u : FreeRow) := errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
    (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y
  let Main (u : FreeRow) := ∏j∈Finset.univ\J,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let MainRaw (u : FreeRow) := ∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
    physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))
  let front : ℝ := Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))
  have hfront : 0 ≤ front := Real.rpow_nonneg hZ.le _
  have he (u : FreeRow) : ‖En u*MainRaw u‖=front*‖En u*Main u‖ := by
    rw [norm_mul,source_main_product_norm F Z hZ hS u J z,hz,complement_prime_product]
    rw [show (∑j:{i:Fin D.N//i∉J},D.ell j.val)*((17/50:ℝ)-1/2) =
      -(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val) by ring]
    dsimp only [front]
    rw [norm_mul]
    ring
  change ‖∑u∈rows,(frequencyWeight z ⟨u.val,u.property.1⟩*
    numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*(En u*MainRaw u)‖ ≤ A*front*B
  calc
    _ ≤ ∑u∈rows,‖(frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*(En u*MainRaw u)‖ := norm_sum_le _ _
    _ ≤ ∑u∈rows,(A*front)*‖En u*Main u‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul,he]
      exact (mul_le_mul_of_nonneg_right (ha u hu) (mul_nonneg hfront (norm_nonneg _))).trans_eq (by ring)
    _ = (A*front)*(∑u∈rows,‖En u*Main u‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (mul_nonneg hA hfront)

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.PhysicalCollect -/

/- BEGIN ORIGINAL Cycle25.Numerator.SourceScalar; sha256 bf51411f6a00bb2f291edc1a726834b3e1073a2a134b2c2b803780e682647ed1 -/
section
                                        
                                      

/-! The actual calibrated scalar and physical frequency at an enlarged moment
base. The .68t factor is retained explicitly when replacing the dyad's lower edge. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification HeckeReciprocalGrowth ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

theorem source_frequency_scalar_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι]
      (ψ : ι→Character) (B a H : ℝ) (i : ℕ),
      2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ∀Z d t U : ℝ,0 < Z → U=Z^d →
      Z^(d-2*t) ≤ rowNorm u → rowNorm u ≤ U →
      ‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar S hS hmax η u x z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*(3+H)^(2*eps)*U^(2*eps)*
          U^(-(17/50:ℝ))*Z^((17/25)*t) := by
  obtain ⟨C,hC,hbound⟩ := numeratorFreeRowScalar_arithmetic_bound e eps he he' heps S hS hmax
  refine ⟨C,hC,?_⟩
  intro η u ι _ ψ B a H i hB ha hatop hH hnext x z hx hz hxim Z d t U hZ hU hlo hhi
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hxim
  have hU0 : 0 < U := by rw [hU];exact Real.rpow_pos_of_pos hZ _
  have hNu0 : 0 < rowNorm u := (Real.rpow_pos_of_pos hZ _).trans_le hlo
  have hs := hbound η u ψ B a H i hB ha hatop hH hnext x z hx hz hxim
  have hs' : ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*U^(2*eps)*(3+H)^(2*eps) := by
    apply hs.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hNu0.le hhi (by positivity)) (by positivity)) (by positivity)
  have hf : ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤
      U^(-(17/50:ℝ))*Z^((17/25)*t) := by
    apply (frequencyWeight_dyad_bound u z (Z^(d-2*t)) (17/50)
      (Real.rpow_pos_of_pos hZ _) (by norm_num) hz hlo).trans_eq
    rw [hU,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  rw [norm_mul]
  apply (mul_le_mul hf hs' (norm_nonneg _) (by positivity)).trans_eq
  ring

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.SourceScalar -/
