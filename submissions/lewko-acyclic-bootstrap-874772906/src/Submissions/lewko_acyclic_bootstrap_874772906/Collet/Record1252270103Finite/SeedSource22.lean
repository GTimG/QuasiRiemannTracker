/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource20
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource22 : Source := ⟨(988724970081/1000000000000),(3929254639921/1000000000000),(21057174717/500000000000),(331298642029/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource22_valid : SeedSourceValid seedSource22 seedSource20 := by decide +kernel
#print axioms seedSource22_valid
end Record1252270103Finite
