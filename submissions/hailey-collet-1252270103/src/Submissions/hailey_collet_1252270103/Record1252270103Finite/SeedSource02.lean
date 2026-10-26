/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource01
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource02 : Source := ⟨(199918980451/200000000000),(1117034448579/250000000000),(2928436799/100000000000),(745036095459/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource02_valid : SeedSourceValid seedSource02 seedSource01 := by decide +kernel
#print axioms seedSource02_valid
end Record1252270103Finite
