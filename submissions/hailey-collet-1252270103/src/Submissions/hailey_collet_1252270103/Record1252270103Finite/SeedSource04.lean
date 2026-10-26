/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource03
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource04 : Source := ⟨(249610003139/250000000000),(4391616116947/1000000000000),(6237883787/200000000000),(91651270411/125000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource04_valid : SeedSourceValid seedSource04 seedSource03 := by decide +kernel
#print axioms seedSource04_valid
end Record1252270103Finite
