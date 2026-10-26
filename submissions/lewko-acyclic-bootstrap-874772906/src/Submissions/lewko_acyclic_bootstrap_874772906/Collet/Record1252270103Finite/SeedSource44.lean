/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource42
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource44 : Source := ⟨(195371315887/200000000000),(1767615045289/500000000000),(50834011243/1000000000000),(301793367053/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource44_valid : SeedSourceValid seedSource44 seedSource42 := by decide +kernel
#print axioms seedSource44_valid
end Record1252270103Finite
