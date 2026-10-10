import QRH.NumericFacts
import QRH.Detector.ActualFixedNonfloorData
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

/-! Actual normalized nonfloor central rows after all dyadic and detector-bin
partitions. No moment or central-cube estimate is an input. -/
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbePhysical ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition



end SevenEighths.QRHUniformDetectorMoment
end
end OAI
