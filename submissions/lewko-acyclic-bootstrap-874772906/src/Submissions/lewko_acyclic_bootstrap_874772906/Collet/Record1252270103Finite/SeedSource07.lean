/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource06
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource07 : Source := ⟨(124472101219/125000000000),(4241113549589/1000000000000),(8704920057/250000000000),(355129334521/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource07_valid : SeedSourceValid seedSource07 seedSource06 := by decide +kernel
#print axioms seedSource07_valid
end Record1252270103Finite
