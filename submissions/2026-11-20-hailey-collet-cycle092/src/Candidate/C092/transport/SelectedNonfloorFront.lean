/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal source-mask reconstruction uses Collet's retained numerator front and
Levy's label packets, with original OpenAI and inherited credits in imports. -/
import Candidate.C092.transport.SelectedNonfloorPacket
import Candidate.C092.transport.DirectPhaseBins
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalCollect
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.Imported.NumeratorReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

/-- The exact entire error-label packet for one original error mask. -/
def errorPacket (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ) (Y : ℝ) : ℂ :=
  labelPolynomialPacket F.S F.exclusions η u (fun j : J => sourcePrimePool F Z j.val)
    (fun j => source_prime_pool_outside F Z j.val) (fun _ => F.W)
    (fun j => Z^(D.length j.val)) x z F.W Y

/-- Main primes are the complement of the SAME original error mask. -/
def mainProduct (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (u : FreeRow) (Z : ℝ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.univ\J, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2
    (Z^(D.length j)) z

def mainFront (D : BaselineData) (J : Finset (Fin D.N)) (Z : ℝ) : ℝ :=
  Z^(-(4/25:ℝ)*(∑ j : {i : Fin D.N // i ∉ J}, D.length j.val))

/-- Absolute contour motion and complete w-inversion give this actual packet,
with natural zeros and the whole countable coefficient family retained. -/
theorem error_eq_packet (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ) (Y : ℝ)
    (hrow : (rowCharacter F.S F.exclusions.prime u).residue ≠ 1)
    (hdis : ∀ P : (∀ j : J, sourcePrimePool F Z j.val), Function.Injective (fun j => (P j).val))
    (hη : ∀ j P, P ∈ sourcePrimePool F Z j → IsCoprime P.val η.modulus)
    (hQ : ∀ j P, P ∈ sourcePrimePool F Z j → (4:ℝ) ≤ P.val.absNorm)
    (hx : (51/100:ℝ) ≤ x.re) (hz : (17/50:ℝ) ≤ z.re)
    (hmargin : 1+4*D.e ≤ x.re+1/2) (hY : 0 < Y) :
    errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
      (fun j => Z^(D.length j)) x z F.W Y = errorPacket D F J η u Z x z Y := by
  exact errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u hrow J
    (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j) hdis hη hQ
    (fun _ => F.W) (fun j => Z^(D.length j)) x z hx hz hmargin F.W 1 2
    (by norm_num) F.complex_support (F.W.smooth ⊤) Y hY

/-- One exact physical error mask from a bound on its full error packet times
its original complementary prime product. The reciprocal stays in the scalar;
its buffer estimate is supplied separately by DirectPhaseBins. -/
theorem mask_bound (D : BaselineData) (F : BaselineSourceData D)
    (rows : Finset FreeRow) (J : Finset (Fin D.N)) (η : Character)
    (Z : ℝ) (hZ : 0 < Z) (x z : ℂ) (Y A B : ℝ) (hY : 0 < Y)
    (hrow : ∀ u ∈ rows, (rowCharacter F.S F.exclusions.prime u).residue ≠ 1)
    (hdis : ∀ P : (∀ j : J, sourcePrimePool F Z j.val), Function.Injective (fun j => (P j).val))
    (hη : ∀ j P, P ∈ sourcePrimePool F Z j → IsCoprime P.val η.modulus)
    (hQ : ∀ j P, P ∈ sourcePrimePool F Z j → (4:ℝ) ≤ P.val.absNorm)
    (hS : ∀ j, ∀ P ∈ F.S, (P.absNorm:ℝ) ≤ Z^(D.length j))
    (hx : (51/100:ℝ) ≤ x.re) (hz : z.re = 17/50)
    (hmargin : 1+4*D.e ≤ x.re+1/2) (hA : 0 ≤ A)
    (hscalar : ∀ u ∈ rows, ‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ A)
    (hpacket : (∑ u ∈ rows, ‖errorPacket D F J η u Z x z Y * mainProduct D F J u Z z‖) ≤ B) :
    ‖sourceMaskContribution F η rows J Z x z Y‖ ≤ A*mainFront D J Z*B := by
  have hp : (∑ u ∈ rows, ‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
      (fun j => Z^(D.length j)) x z F.W Y * mainProduct D F J u Z z‖) ≤ B := by
    calc
      _ = ∑ u ∈ rows, ‖errorPacket D F J η u Z x z Y * mainProduct D F J u Z z‖ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact congrArg (fun v : ℂ => ‖v*mainProduct D F J u Z z‖)
          (error_eq_packet D F J η u Z x z Y (hrow u hu) hdis hη hQ hx hz.ge hmargin hY)
      _ ≤ B := hpacket
  exact source_mask_physical_front F η rows J Z hZ x z hz Y hS A B hA hscalar hp

/-- All original masks are summed before the remaining two Mellin integrals.
The hypotheses concern genuine packet rows; no already-integrated energy or
probe estimate is assumed. -/
theorem integrated_bound (D : BaselineData) (F : BaselineSourceData D)
    (rows : Finset FreeRow) (η : Character) (Z : ℝ) (hZ : 0 < Z)
    (x z : ℂ) (Y A : ℝ) (B : Finset (Fin D.N) → ℝ) (hY : 0 < Y)
    (hrow : ∀ u ∈ rows, (rowCharacter F.S F.exclusions.prime u).residue ≠ 1)
    (hdis : ∀ J : Finset (Fin D.N), ∀ P : (∀ j : J, sourcePrimePool F Z j.val),
      Function.Injective (fun j => (P j).val))
    (hdisAll : ∀ P : (∀ j, sourcePrimePool F Z j), Function.Injective (fun j => (P j).val))
    (hη : ∀ j P, P ∈ sourcePrimePool F Z j → IsCoprime P.val η.modulus)
    (hQ : ∀ j P, P ∈ sourcePrimePool F Z j → (4:ℝ) ≤ P.val.absNorm)
    (hS : ∀ j, ∀ P ∈ F.S, (P.absNorm:ℝ) ≤ Z^(D.length j))
    (hx : (51/100:ℝ) ≤ x.re) (hz : z.re = 17/50)
    (hmargin : 1+4*D.e ≤ x.re+1/2) (hA : 0 ≤ A)
    (hscalar : ∀ u ∈ rows, ‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ A)
    (hpacket : ∀ J, (∑ u ∈ rows,
      ‖errorPacket D F J η u Z x z Y * mainProduct D F J u Z z‖) ≤ B J) :
    ‖integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
      (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
      (fun j => Z^(D.length j)) F.W Y x z‖ ≤
      (2*Real.pi)*A*(∑ J ∈ Finset.univ.powerset, mainFront D J Z*B J) := by
  have hrecon := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e)
    F.first η rows hrow (sourcePrimePool F Z) (fun j => source_prime_pool_outside F Z j)
    hdis hdisAll hη hQ (fun _ => F.W) (fun j => Z^(D.length j)) x z hx hz.ge hmargin
    F.W 1 2 (by norm_num) F.complex_support Y hY
  have hmasks : reconstructedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
      (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
      (fun j => Z^(D.length j)) x z F.W Y =
      ∑ J ∈ Finset.univ.powerset, sourceMaskContribution F η rows J Z x z Y :=
    source_reconstructed_sum_masks F η rows Z x z Y
  rw [hrecon, norm_mul, show (2*Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) by norm_cast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0<2*Real.pi by positivity),
    hmasks]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
  calc
    _ ≤ (2*Real.pi)*(∑ J ∈ Finset.univ.powerset, A*mainFront D J Z*B J) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun J _ => mask_bound D F rows J η Z hZ x z Y A (B J) hY
        hrow (hdis J) hη hQ hS hx hz hmargin hA hscalar (hpacket J))
    _ = _ := by rw [Finset.mul_sum]; congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro J hJ; ring

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.error_eq_packet
#print axioms QRH.Cycle092.SelectedNonfloor.integrated_bound
