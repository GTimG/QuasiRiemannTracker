/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual single reflected numerator Fourier column used by the outer mixed
return. Original OpenAI/Collet/Gao and subsequent source credits remain in imports. -/
import Candidate.C092.transport.MixedPacketWitnessFiber
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.FourierProfiles
import Candidate.C092.transport.MixedScaleOriginal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedPacketScale
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open ConcretePrimeRowBridge CanonicalRowCompletion ProbeHighRowFamily HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorDictionary
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentEnergyReferenceChild
open HeckeDetectorCoefficientTransfer Cycle25WeightedNumeratorPhysical ProbePhysical
open CenteredMomentLattice QRH.Cycle092.OrdinaryColumn
open QRH.Cycle092.MixedPacketWitness
local notation "O" => HeckeFamily.O

lemma annular_test_real (j : Fin 2) (x : ℝ) :
    conj (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j x) =
      scaleTest (fun z : ℝ=>(annulus z:ℂ)) j x := by
  have he : (fun z : ℝ=>conj (annulus z:ℂ)) = (fun z : ℝ=>(annulus z:ℂ)) := by
    ext z
    simp
  fin_cases j
  · simp [scaleTest]
  · have hh := scaleProfile_conjugate (fun z : ℝ=>(annulus z:ℂ)) x
    rw [he] at hh
    simpa only [scaleTest,Fin.mk_one,one_ne_zero,ite_false] using hh.symm

/-- A single Fourier column has its own polynomial degree, before all live
frequency, scale, zero and height parameters. -/
theorem long_fourier_control (controls : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ C : ℝ,0<C ∧ ∀j : Fin 2,∀v : ℝ,
      (sourceControl controls ((numeratorFourierProfiles j 0 v 0).profile 0))^2 ≤
        C*(1+‖v‖)^(2*J) := by
  obtain ⟨J,T,C,hC,hc⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) controls
  let A := 1+∑j : Fin 2,sourceControl T (numeratorAnnular j)
  have hA : 0<A := by
    have h := Finset.sum_nonneg (fun j (_:j∈Finset.univ)=>sourceControl_nonneg T (numeratorAnnular j))
    dsimp [A];linarith
  let B := C*A*(1+2*Real.pi)^J
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨J,B^2,by positivity,?_⟩
  intro j v
  have hAj : sourceControl T (numeratorAnnular j) ≤ A := by
    have hh := Finset.single_le_sum
      (fun k (_:k∈Finset.univ)=>sourceControl_nonneg T (numeratorAnnular k)) (Finset.mem_univ j)
    dsimp [A];linarith
  have hv : 1+‖-2*Real.pi*v‖ ≤ (1+2*Real.pi)*(1+‖v‖) := by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
    nlinarith [Real.pi_pos,norm_nonneg v]
  have h := hc (numeratorAnnular j) (numeratorAnnular_support j) (-2*Real.pi*v)
  have hh : sourceControl controls ((numeratorFourierProfiles j 0 v 0).profile 0) ≤
      B*(1+‖v‖)^J := by
    change sourceControl controls (normPowerProfile _ _ _ _ _ _ _) ≤ _
    calc
      _ ≤ C*sourceControl T (numeratorAnnular j)*(1+‖-2*Real.pi*v‖)^J := h
      _ ≤ C*A*((1+2*Real.pi)*(1+‖v‖))^J := by gcongr
      _ = _ := by dsimp [B];rw [mul_pow];ring
  calc
    _ ≤ (B*(1+‖v‖)^J)^2 := pow_le_pow_left₀ (sourceControl_nonneg _ _) hh 2
    _ = _ := by rw [mul_pow,←pow_mul];congr 2;omega

/-- Exact Fourier sign and arithmetic character identity. The raw physical
numerator is the canonical principal-source row, including natural zeros. -/
theorem long_fourier_original (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : FreeRow) (j : Fin 2) (v X : ℝ) (hX : 0<X) :
    polynomial (rowCharacter S hS u) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
      X 0 (-2*Real.pi*v) =
    original (fixedSourcePrincipal S hS) (fixedBadMask*idealGenerator 1) 1 u.val
      ((numeratorFourierProfiles j 0 v 0).profile 0) 0 X := by
  let η := fixedSourcePrincipal S hS
  let WL := (numeratorFourierProfiles j 0 v 0).profile 0
  have hprof : polynomial (rowCharacter S hS u) false WL X 0 0 =
      polynomial (rowCharacter S hS u) false
        (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) X 0 (-2*Real.pi*v) := by
    rw [numerator_fourier_polynomial_zero]
    simp_rw [annular_test_real]
  rw [←hprof,numerator_polynomial_eq_moment S hS hbad]
  rw [polynomial_eq_of_idealCoeff _ (canonicalCharacter η u) (canonical_ideal η u) false WL X 0 0]
  rw [plain_polynomial_eq_row η (canonicalCharacter η u) (fixedBadMask*idealGenerator 1)
    1 u.val (canonical_element η u) WL X 0 0 hX,twistProfile_zero_zero]
  rfl

#print axioms long_fourier_control
#print axioms long_fourier_original
end
end QRH.Cycle092.MixedPacketScale
