import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Final.FixedHigh
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily Cycle63DetectorCount PrincipalSignalComparison

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  fineA : ∀j,D.length j≤Cycle63.CountAffine.detectorMesh D.t/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t

end
end Cycle63.FinalAssembly

end Record1252270103Bootstrap.PR67
