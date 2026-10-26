/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource43
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource45 : Source := ⟨(980108998561/1000000000000),(45401941713/12500000000),(48722743123/1000000000000),(618084793667/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource45_valid : SeedSourceValid seedSource45 seedSource43 := by decide +kernel
#print axioms seedSource45_valid
end Record1252270103Finite
