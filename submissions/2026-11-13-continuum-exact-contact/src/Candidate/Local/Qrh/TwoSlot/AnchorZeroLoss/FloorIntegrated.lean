/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
All physical floor masks summed through the exact numerator reconstruction.
Hailey Collet's reconstruction and original notices are retained in imports. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FloorMasks
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.Imported.NumeratorReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace Qrh.TwoSlot.AnchorZeroLoss
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily
open HeckeInverseAmplification ProbeHighRowFamily ProbePhysical

/-- All physical error masks, with the exact factor `2*pi` from numerator
reconstruction. The scalar bound is uniform on the original physical row
set. There is no bin partition, selected event or density-count input. -/
theorem physical_floor_integrated {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (kap : ℝ)
    (hkaplo : 7/10 ≤ kap) (hkaphi : kap ≤ 3/4)
    (hkapbeta : 2*HeckeZeroSupremum.beta-1 ≤ kap)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (he : D.e ≤ 1/1000) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (Z : ℝ), 1 ≤ Z → ∀ (η : Character) (x z : ℂ),
    x.re=51/100+16*D.e → z.re=17/50 →
    ∀ rows : Finset FreeRow,
    (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
    (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue ≠ 1) →
    (∀J:Finset (Fin D.N),∀P:∀i:J,sourcePrimePool F Z i.val,
      Function.Injective (fun i => (P i).val)) →
    (∀P:∀i,sourcePrimePool F Z i,Function.Injective (fun i => (P i).val)) →
    (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus) →
    (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm) →
    (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell i)) →
    (∀i,sourcePrimePool F Z i) →
    (∀u∈rows,∀i,‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
      F.W 2 (Z^(D.ell i)) z‖ ≤ Z^(D.ell i*(1/100+D.t))) →
    ∀ (v A : ℝ), 0 < v → v ≤ 99 → 0 ≤ A →
    (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ A) →
    ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal
      η rows (sourcePrimePool F Z) (fun i => source_prime_pool_outside F Z i)
      (fun _ => F.W) (fun i => Z^(D.ell i)) F.W (U^v) x z‖ ≤
      C*A*(U^v)^(-(1/2:ℝ))*Z^((-3/20+D.t)*∑j,D.ell j)*
        U^(1+(38/25:ℝ)*D.t) := by
  choose Cmask hCmask hmask using (fun J : Finset (Fin D.N) =>
    physical_floor_mask F kap hkaplo hkaphi hkapbeta hbeta he J)
  let masks : Finset (Finset (Fin D.N)) := Finset.univ.powerset
  let C : ℝ := (2*Real.pi)*(∑J∈masks,Cmask J)
  have hsum : 0 < ∑J∈masks,Cmask J :=
    Finset.sum_pos (fun J _ => hCmask J) ⟨∅,by simp [masks]⟩
  refine ⟨C,mul_pos (by positivity) hsum,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmask] with U hall
  refine ⟨(hall ∅).1,?_⟩
  intro Z hZ η x z hx hz rows hrows hrow hdis hdisAll hη hQ hS Pbase hmain v A hv hvhi hA hscalar
  have hZp := zero_lt_one.trans_le hZ
  have hUp := zero_lt_one.trans (hall ∅).1
  let common : ℝ := A*(U^v)^(-(1/2:ℝ))*Z^((-3/20+D.t)*∑j,D.ell j)*
    U^(1+(38/25:ℝ)*D.t)
  have hcommon : 0 ≤ common := by dsimp only [common]; positivity
  have hm (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η rows J Z x z (U^v)‖ ≤ Cmask J*common := by
    have hh := (hall J).2 Z hZ η x z hx hz rows hrows hrow (hdis J)
      hη hQ hS (fun i:J => Pbase i.val) hmain v A hv hvhi hA hscalar
    simpa only [common,mul_assoc] using hh
  have hrecon := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e)
    F.first η rows hrow (sourcePrimePool F Z) (fun i => source_prime_pool_outside F Z i)
    hdis hdisAll hη hQ (fun _ => F.W) (fun i => Z^(D.ell i)) x z
    (by rw [hx]; linarith [D.e_pos]) hz.ge (by rw [hx]; linarith [D.e_pos])
    F.W 1 2 (by norm_num) F.complex_support (U^v)
    (Real.rpow_pos_of_pos (zero_lt_one.trans (hall ∅).1) _)
  rw [hrecon,norm_mul,show (2*Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) by norm_cast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<2*Real.pi by positivity),
    source_reconstructed_sum_masks]
  calc
    _ ≤ (2*Real.pi)*(∑J∈masks,‖sourceMaskContribution F η rows J Z x z (U^v)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2*Real.pi)*(∑J∈masks,Cmask J*common) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun J _ => hm J)) (by positivity)
    _ = C*A*(U^v)^(-(1/2:ℝ))*Z^((-3/20+D.t)*∑j,D.ell j)*
        U^(1+(38/25:ℝ)*D.t) := by
      rw [←Finset.sum_mul]
      dsimp only [C,common]
      ring

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.physical_floor_integrated
