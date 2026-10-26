/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource08
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource09 : Source := ⟨(497467503091/500000000000),(4197944457713/1000000000000),(7179332461/200000000000),(351658684369/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource09_valid : SeedSourceValid seedSource09 seedSource08 := by decide +kernel
#print axioms seedSource09_valid
end Record1252270103Finite
