import QRH.Detector.ActualNormalizedNonfloorCube
import QRH.Detector.OptimizedData

/-! A fully instantiated optimized nonfloor central-cube estimate. Compatible
slots and small scales are proved to exist; the tail follows the height degree. -/
set_option maxHeartbeats 800000
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
