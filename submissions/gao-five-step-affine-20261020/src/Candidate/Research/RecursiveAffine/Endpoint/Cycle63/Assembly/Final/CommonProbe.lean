import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Final.FixedHigh
import Candidate.Research.RecursiveAffine.Endpoint.RootMomentFactory

variable [Cycle153Endpoint.RootMomentFactory]


noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Final_CommonProbe : Cycle63.AffineLedger := Cycle153.Root.rootLedger


set_option autoImplicit false
namespace Cycle153Endpoint.FinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily Cycle153EndpointDetectorCount PrincipalSignalComparison

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  fineA : ∀j,D.length j≤Cycle153Endpoint.CountAffine.detectorMesh D.t/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : Cycle153EndpointProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t

end
end Cycle153Endpoint.FinalAssembly
