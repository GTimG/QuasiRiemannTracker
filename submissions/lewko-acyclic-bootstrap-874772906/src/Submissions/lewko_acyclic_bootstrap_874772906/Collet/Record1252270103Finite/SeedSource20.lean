/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource18
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource20 : Source := ⟨(247347289251/250000000000),(3955320276699/1000000000000),(8296735841/200000000000),(133363930487/200000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource20_valid : SeedSourceValid seedSource20 seedSource18 := by decide +kernel
#print axioms seedSource20_valid
end Record1252270103Finite
