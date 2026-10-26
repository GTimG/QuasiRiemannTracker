/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource23
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource25 : Source := ⟨(990794489129/1000000000000),(250673048477/62500000000),(40277012093/1000000000000),(168694571417/250000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource25_valid : SeedSourceValid seedSource25 seedSource23 := by decide +kernel
#print axioms seedSource25_valid
end Record1252270103Finite
