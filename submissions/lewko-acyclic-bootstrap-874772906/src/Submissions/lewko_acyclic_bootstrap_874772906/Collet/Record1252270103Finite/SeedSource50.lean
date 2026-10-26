/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource48
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource50 : Source := ⟨(243374197403/250000000000),(1720029640633/500000000000),(52899909767/1000000000000),(73669807357/125000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource50_valid : SeedSourceValid seedSource50 seedSource48 := by decide +kernel
#print axioms seedSource50_valid
end Record1252270103Finite
