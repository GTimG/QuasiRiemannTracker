/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource01 : Source := ⟨(199945667419/200000000000),(895561776373/200000000000),(5806366189/200000000000),(186648693973/250000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource01_valid : SeedSourceValid seedSource01 seedNatural := by decide +kernel
#print axioms seedSource01_valid
end Record1252270103Finite
