/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource12
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource14 : Source := ⟨(30994286799/31250000000),(4055302505813/1000000000000),(7836548769/200000000000),(681991012399/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource14_valid : SeedSourceValid seedSource14 seedSource12 := by decide +kernel
#print axioms seedSource14_valid
end Record1252270103Finite
