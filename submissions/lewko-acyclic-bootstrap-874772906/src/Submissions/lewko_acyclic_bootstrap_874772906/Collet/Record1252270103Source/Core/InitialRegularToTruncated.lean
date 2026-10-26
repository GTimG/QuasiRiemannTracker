/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedBalanced
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialBalancedToTruncated
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Low
open InitialTruncated

theorem truncated_of_regular (K:ℚ)(n low:Source)(b mesh ξ reserve width ε:ℝ)
    (hg:RealGeometry K n low b)(hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hc:(n.cap:ℝ)≤1)
    (hlow:(low.B:ℝ)≤1)(he:0<(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))
    (hm0:0≤mesh)(hm:mesh<sourceAReal n low b/2)
    (hx:0<ξ)(hx1:ξ≤1)(hxstep:ξ≤PhysicalLowGuard.step n)
    (hr0:0≤reserve)(hr1:reserve≤1)(hrstep:reserve≤PhysicalLowGuard.step n)
    (hw:width≤PhysicalLowGuard.step n)
    (hregular:RegularJointSupplier K n low b mesh ξ reserve width) :
    FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) (crossing n low:ℝ)
      (K:ℝ) mesh ξ ε b width :=
  truncated_of_balanced K n low b mesh ξ width hg
    (balanced_of_regular K n low b mesh ξ reserve width hg hB hL hc hlow he hfee
      hm0 hm hx hx1 hxstep hr0 hr1 hrstep hw hregular)
end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.truncated_of_regular
