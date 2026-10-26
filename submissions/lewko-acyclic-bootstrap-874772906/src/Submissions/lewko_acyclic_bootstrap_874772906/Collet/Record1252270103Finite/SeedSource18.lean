/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource16
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource18 : Source := ⟨(198159665083/200000000000),(2005980490543/500000000000),(40240282621/1000000000000),(337496438357/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource18_valid : SeedSourceValid seedSource18 seedSource16 := by decide +kernel
#print axioms seedSource18_valid
end Record1252270103Finite
