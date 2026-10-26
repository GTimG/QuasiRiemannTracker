/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource40
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource42 : Source := ⟨(977860651719/1000000000000),(445603158113/125000000000),(12544203239/250000000000),(121622137699/200000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource42_valid : SeedSourceValid seedSource42 seedSource40 := by decide +kernel
#print axioms seedSource42_valid
end Record1252270103Finite
