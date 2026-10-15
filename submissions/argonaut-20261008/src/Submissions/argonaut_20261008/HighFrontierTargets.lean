import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyHigh
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

/-!
Unbuilt engineering target definitions, NOT proved estimates or semantic admission.
Every function below uses the actual official physical probe and SourceMomentsAt.
They specify outputs to be PROVED by additive modules in branches B/C; none is an
assumption field of the scalar constructor. The first constructor's returned
record must later be projected into these explicit scalar arguments.
-/
namespace OAI.SevenEighths.HighFrontierTargets
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def rho : ℝ := 1 / 1000000
def totalE : ℝ := 1 / 6 + rho
def rowHeight : ℝ := 13 / 16 + 3 * rho / 2
def lx : ℝ := 17 / 48 - rho / 2
def ly : ℝ := 23 / 48 - rho / 2
def sigmaBoundary : ℝ := 7 / 8 - rho / 4
def positiveGap : ℝ := HeckeZeroSupremum.beta - sigmaBoundary
-- Proposed count/energy allowance; compatibility must be proved, not asserted.
def momentAllowance : ℝ := max 0 (HeckeZeroSupremum.beta - 7 / 8)

def normalizedProbeAt {N : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N → ℝ) (a b : ℝ) (W : Fin N → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (E lx0 ly0 : ℝ)
    (η : Character) (Z : ℝ) : ℂ :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let Yp := fun j => Z ^ (ell j)
  let T := fun j => pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j => canonicalSlotSupport (T j)) (fun j y => (W j y : ℂ)) Yp
    (Z ^ lx0) (Z ^ ly0) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P) *
      (Probe.principalScalar Finset.univ Z E
        (slotMass T (residueWeights W Yp)) : ℂ))

def SourceMomentBoundAt {N : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (ell : Fin N → ℝ) (W : Fin N → ℝ → ℝ)
    (dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM : ℝ)
    (counts : CountParameters M H epsilonM) (η : Character)
    (Z theta C height : ℝ) : Prop :=
  ∀rows : Finset HeckeInverseAmplification.FreeRow, ∀d a : ℝ,
    dmin ≤ d → d ≤ dmax → (51/100 : ℝ) < a → a ≤ 1 →
    (∀u∈rows,u.val ≠ 1 ∧ Z ^ (1/100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (d - rowMargin)) →
    ∀i : ℕ, ∀z : ℂ, z.re = 17/50 → |z.im| ≤ height →
    SourceMomentsAt M H hH S hS.prime η rows ell (fun j y => (W j y : ℂ))
      Z d a epsilon theta dmax b slotMesh binWidth i z gamma
      (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
      (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH) C height epsilonM

-- Exact quantifier order to be obtained from the actual certified energy chain.
def HighJointMomentOutputAt {N : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (ell : Fin N → ℝ) (W : Fin N → ℝ → ℝ)
    (dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM : ℝ)
    (counts : CountParameters M H epsilonM) : Prop :=
  ∃J : ℝ, 0 ≤ J ∧ ∀η : Character, ∃C : ℝ, 0 < C ∧
    ∀theta : ℝ, 0 < theta → theta ≤ 1 → ∀ᶠZ : ℝ in atTop,
      SourceMomentBoundAt M H hH S hS hmax ell W
        dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM
        counts η Z theta (C * (1 + Z ^ (2*theta)) ^ J) (Z ^ (2*theta))

-- Actual moments-to-physical-probe bound. This local bridge must be proved;
-- unconditional production of its moment premise is HighJointMomentOutputAt.
def HighProbeOutputAt {N : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (ell : Fin N → ℝ) (W : Fin N → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ)
    (dmin dmax a b epsilon rowMargin slotMesh binWidth gamma epsilonM : ℝ)
    (counts : CountParameters M H epsilonM)
    (E lx0 ly0 theta momentCost eps saving : ℝ) : Prop :=
  ∃C : ℝ, 0 < C ∧ ∀η : Character, ∃Ct : ℝ, 0 < Ct ∧
    ∀ᶠZ : ℝ in atTop, ∀C0 : ℝ, 0 ≤ C0 →
      SourceMomentBoundAt M H hH S hS hmax ell W
        dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM
        counts η Z theta (C0 * Z ^ momentCost) (Z ^ (2*theta)) →
      ‖normalizedProbeAt M H S hS hmax ell a b W W0 W1 E lx0 ly0 η Z -
        HeckeSignal.signal (η.excludePrimes S hS.prime)
          (sourceCorrection η S) (-11/16) Z‖ ≤
        (Ct + C*C0*(η.modulus.absNorm : ℝ) ^ (2*eps)) *
          Z ^ (HeckeZeroSupremum.beta - 11/16 - saving)

-- Extra construction required before calling the boundary consumer. No L
-- nonvanishing hypothesis is allowed in proving this contract.
def CommonProbeConstructionGoalAt (b0 : ℝ) : Prop :=
  b0 < HeckeZeroSupremum.beta → ∃omega saving : ℝ,
    0 < omega ∧ omega < HeckeZeroSupremum.beta-b0 ∧ 0 < saving ∧
    ∀η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∃χ : Character, ∃correction : ℂ → ℂ, ∃probe : ℝ → ℂ,
        (∀I,idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
        AnalyticOnNhd ℂ correction {s : ℂ | b0 < s.re} ∧
        (∀s : ℂ,b0 < s.re → ‖correction s-1‖ ≤ 1/2) ∧
        probe =O[atTop] (fun Z : ℝ => Z ^ (b0-11/16+omega)) ∧
        (fun Z => probe Z-HeckeSignal.signal χ correction (-11/16) Z) =O[atTop]
          (fun Z : ℝ => Z ^ (HeckeZeroSupremum.beta-11/16-saving))

end
end OAI.SevenEighths.HighFrontierTargets
