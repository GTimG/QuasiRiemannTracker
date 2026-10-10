import Cycle25.Assembly.Weighted.Target
import Cycle25.Numerator.PhysicalFront
import Cycle25.Numerator.Imported.FullWFiniteError
import OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
namespace SevenEighths.Cycle25WeightedHighFinalAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

/-- The precise remaining analytic estimate, on literal original finite full-w rows.
This definition is an input interface and asserts no unproved bound. -/
def FullWCellsAt {Δ : ℝ} (D : Cycle25.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character)
    (Z τ : ℝ) (n : ℕ) (weightedC C0 : ℝ) : Prop :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∀idx grid : FreeRow→ℕ,
    let rows := supportedNonfloorRows F.S F.maximal
      (rowBand (Z^(1/100:ℝ)) (Z^(Cycle25.h+D.t))) grid
    (∀u∈rows,idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/D.e⌋₊ ∧
      (51/100:ℝ)+D.e*grid u ≤ 7/8) →
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(idx u+1:ℕ)*Z^τ) < 51/100+D.e*grid u+2*D.e) →
    (∀u∈rows,(51/100:ℝ)+D.e*grid u ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ)) →
    ∀k∈smallDyadicIndices (Z^(Cycle25.h+D.t)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
      let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
      let Y : Fin D.N→ℝ := fun j=>Z^(D.ell j)
      let T := fun j=>pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
      let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Y
      let normer := sourceResidueConstant F.W F.W (∏P∈F.S,P)*
        (Probe.principalScalar Finset.univ Z Cycle25.ell
          (slotMass T (residueWeights (fun _=>F.w) Y)) : ℂ)
      rows'.Nonempty → (1/2:ℝ) < sourceDyadConductor Z D.t k →
      (1/3:ℝ) < 2*(51/100+D.e*j)-1 →
      sourceDyadConductor Z D.t k ≤ Cycle25.h+3*D.t →
      ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η rows' T hT
          (fun _ y=>(F.w y:ℂ)) Y F.W F.W (Z^Cycle25.lx) (Z^Cycle25.ly) Z D.e
          (fun _=>51/100+D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤
        weightedC*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          Z^(Cycle25.weightedTarget+D.t/8)

end SevenEighths.Cycle25WeightedHighFinalAssembly
end
end OAI
