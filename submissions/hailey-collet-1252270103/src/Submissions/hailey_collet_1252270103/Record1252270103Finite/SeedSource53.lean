/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource51
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource53 : Source := ⟨(487778756569/500000000000),(349697622457/100000000000),(12913841991/250000000000),(299003735799/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource53_valid : SeedSourceValid seedSource53 seedSource51 := by decide +kernel
#print axioms seedSource53_valid
end Record1252270103Finite
