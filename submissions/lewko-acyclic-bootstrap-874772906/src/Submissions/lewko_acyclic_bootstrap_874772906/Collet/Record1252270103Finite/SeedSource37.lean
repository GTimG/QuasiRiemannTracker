/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource35
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource37 : Source := ⟨(123168010249/125000000000),(19020347741/5000000000),(44914128421/1000000000000),(643920667613/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource37_valid : SeedSourceValid seedSource37 seedSource35 := by decide +kernel
#print axioms seedSource37_valid
end Record1252270103Finite
