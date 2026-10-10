import Cycle25.Numerator.Imported.NumeratorTupleRestoration
import Cycle25.Assembly.SourceData
import OAI.NumberTheory.DirichletL.Detector.RayPhaseAmplitude
import OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
import OAI.NumberTheory.DirichletL.PrimeRows.RowCount
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

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
