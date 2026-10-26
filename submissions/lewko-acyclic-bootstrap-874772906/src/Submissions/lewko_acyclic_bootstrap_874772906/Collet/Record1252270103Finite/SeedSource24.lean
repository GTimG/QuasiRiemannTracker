/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource22
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource24 : Source := ⟨(987041667591/1000000000000),(120824114663/31250000000),(21742127769/500000000000),(653500312943/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource24_valid : SeedSourceValid seedSource24 seedSource22 := by decide +kernel
#print axioms seedSource24_valid
end Record1252270103Finite
