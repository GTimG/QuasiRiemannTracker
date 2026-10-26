/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource38
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource40 : Source := ⟨(979113180459/1000000000000),(144098844583/40000000000),(24687235023/500000000000),(613577421569/1000000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource40_valid : SeedSourceValid seedSource40 seedSource38 := by decide +kernel
#print axioms seedSource40_valid
end Record1252270103Finite
