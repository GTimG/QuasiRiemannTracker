/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSource28
set_option autoImplicit false
namespace Record1252270103Finite
def seedSource30 : Source := ⟨(30735915347/31250000000),(3744274316547/1000000000000),(9250256301/200000000000),(317412324061/500000000000),1/10^12,1/10^8,1/10^7⟩
theorem seedSource30_valid : SeedSourceValid seedSource30 seedSource28 := by decide +kernel
#print axioms seedSource30_valid
end Record1252270103Finite
