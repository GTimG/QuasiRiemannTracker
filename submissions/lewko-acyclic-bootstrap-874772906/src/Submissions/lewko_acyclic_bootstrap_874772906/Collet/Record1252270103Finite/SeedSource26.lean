/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource24
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource26 : Source := ⟨(9862556267/10000000000),(1918860172069/500000000000),(22086426179/500000000000),(6488403297/10000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource26_valid : SeedSourceValid seedSource26 seedSource24 := by decide +kernel
#print axioms seedSource26_valid
end Record1252270103Finite
