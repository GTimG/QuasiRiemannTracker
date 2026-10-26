/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource09
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource11 : Source := ⟨(124350538841/125000000000),(4191367962573/1000000000000),(7212140013/200000000000),(702256856613/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource11_valid : SeedSourceValid seedSource11 seedSource09 := by decide +kernel
#print axioms seedSource11_valid
end Record1252270103Finite
