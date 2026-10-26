/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSourceFormulas
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SeedSource31
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource33 : Source := ⟨(197528025347/200000000000),(485866910913/125000000000),(10768314627/250000000000),(131248098439/200000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource33_valid : SeedSourceValid seedSource33 seedSource31 := by decide +kernel
#print axioms seedSource33_valid
end Record1252270103Finite
