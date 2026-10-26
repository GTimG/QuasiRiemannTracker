/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource14
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource16 : Source := ⟨(3964500873/4000000000),(1006434762593/250000000000),(39903896403/1000000000000),(169305574377/250000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource16_valid : SeedSourceValid seedSource16 seedSource14 := by decide +kernel
#print axioms seedSource16_valid
end Record1252270103Finite
