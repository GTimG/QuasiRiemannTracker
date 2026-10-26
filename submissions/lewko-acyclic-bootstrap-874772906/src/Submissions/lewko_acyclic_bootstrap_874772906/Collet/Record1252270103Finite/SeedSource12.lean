/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource10
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource12 : Source := ⟨(993266628247/1000000000000),(64360589947/15625000000),(37738686793/1000000000000),(691397158393/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource12_valid : SeedSourceValid seedSource12 seedSource10 := by decide +kernel
#print axioms seedSource12_valid
end Record1252270103Finite
