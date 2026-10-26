/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource30
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource32 : Source := ⟨(983157119711/1000000000000),(3731089626457/1000000000000),(2910467229/62500000000),(158164803157/250000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource32_valid : SeedSourceValid seedSource32 seedSource30 := by decide +kernel
#print axioms seedSource32_valid
end Record1252270103Finite
