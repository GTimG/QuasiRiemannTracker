/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource04
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource05 : Source := ⟨(62339794481/62500000000),(1082936988141/250000000000),(16316294017/500000000000),(724157400173/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource05_valid : SeedSourceValid seedSource05 seedSource04 := by decide +kernel
#print axioms seedSource05_valid
end Record1252270103Finite
