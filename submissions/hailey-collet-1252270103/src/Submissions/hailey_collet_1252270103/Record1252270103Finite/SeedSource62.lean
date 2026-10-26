/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource60
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource62 : Source := ⟨(965705536457/1000000000000),(3237999482351/1000000000000),(54998999999/1000000000000),(559400373933/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource62_valid : SeedSourceValid seedSource62 seedSource60 := by decide +kernel
#print axioms seedSource62_valid
end Record1252270103Finite
