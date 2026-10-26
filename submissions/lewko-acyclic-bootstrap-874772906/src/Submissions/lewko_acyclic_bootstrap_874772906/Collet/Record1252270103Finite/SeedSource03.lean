/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource02
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource03 : Source := ⟨(249705761041/250000000000),(441636472517/100000000000),(15276692491/500000000000),(46074222499/62500000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource03_valid : SeedSourceValid seedSource03 seedSource02 := by decide +kernel
#print axioms seedSource03_valid
end Record1252270103Finite
