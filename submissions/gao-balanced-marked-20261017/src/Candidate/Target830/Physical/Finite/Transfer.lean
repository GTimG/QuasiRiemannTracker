/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
import Candidate.Target830.Physical.Finite.Summation
import Candidate.Target830.Physical.FiniteError.Normalized

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open OAI.SevenEighths.Target830.Physical FinalAssembly Target830PhysicalHighTransport
open OAI.SevenEighths.Target830.Physical.Assembly

/-- The proved original-row error applies to the literal new-geometry numerator. -/
theorem actual_selected_error (A : ChosenData) (τ : ℝ) (hτ : 0< τ) :
    ∃C : ℝ,0≤ C ∧ ∀ᶠZ : ℝ in atTop,∀n : ℕ,∀η : Character,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      normalizer A.D A.F Z≠0 ∧
      ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
        1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid/normalizer A.D A.F Z-
        fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
          (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := by
  obtain ⟨C,hC,herror⟩:=Target830PhysicalHighRowFamily.actual_normalized_cube_fullW_arbitrary_saving
    A.F.modulus ⊤ le_top A.D.N τ 1 1 2 1 rowPadding (A.D.t/8)
    hτ (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowPadding])
    (by have ht:=A.D.t_pos;positivity) A.D.e A.D.e_pos A.D.e_small
    A.F.S A.F.exclusions A.F.maximal A.F.first A.D.length A.D.slots_pos A.D.slots_injective A.D.slots_sum
    (fun _=>A.F.w) (fun _=>A.F.smooth) (fun _=>A.F.compact) (fun _=>A.F.support)
    (fun _=>A.F.bounded) (fun _=>A.F.nonzero) A.F.W A.F.W 1 2 1 2 (by norm_num) (by norm_num)
    A.F.complex_support A.F.complex_support A.F.real A.F.real A.F.nonnegative A.F.nonnegative
    A.F.complex_nonzero A.F.complex_nonzero
  refine ⟨C,hC,?_⟩
  filter_upwards [herror,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_ge_atTop (1:ℝ)] with Z he hT hZ
  intro n η idx grid hsel
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hbin : ∀u∈selectedRows A.D A.F Z grid,
      (51/100:ℝ)≤51/100+A.D.e*grid u ∧ 51/100+A.D.e*grid u≤1 ∧ 2< Z^τ ∧
      Z^τ≤(3*idx u+1:ℕ)*Z^τ ∧ (3*idx u+1:ℕ)*Z^τ≤(3*idx u+2:ℕ)*Z^τ ∧
      detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^τ)<51/100+A.D.e*grid u+2*A.D.e := by
    intro u hu
    refine ⟨(hsel.2.1 u).1,(hsel.2.1 u).2.1.trans (by norm_num),hT,?_,?_,(hsel.2.1 u).2.2.2.2.1⟩
    · have hm : (1:ℝ)≤(3*idx u+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx u+1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) τ)
    · have hm : ((3*idx u+1:ℕ):ℝ)≤(3*idx u+2:ℕ) := by
        exact_mod_cast (by omega : 3*idx u+1≤3*idx u+2)
      exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) τ)
  have hb:=he η (selectedRows A.D A.F Z grid)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u=>51/100+A.D.e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx hbin
  convert hb using 1 <;> rfl
end
end OAI.SevenEighths.Target830.Physical.FiniteNumerator

#print axioms OAI.SevenEighths.Target830.Physical.FiniteNumerator.actual_selected_error
