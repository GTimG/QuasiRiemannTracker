/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source264
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source272
set_option autoImplicit false
namespace Record1252270103Finite
def source276 : Source := ⟨(30082118389/31250000000),(3156801677691/1000000000000),(549989/10000000),(273319527339/500000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source276_valid : SourceValid source276 source272 (some source264) := by decide +kernel
#print axioms source276_valid
end Record1252270103Finite
