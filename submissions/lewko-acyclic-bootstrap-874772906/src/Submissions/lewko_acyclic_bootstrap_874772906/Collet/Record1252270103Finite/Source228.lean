/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source211
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.Source215
set_option autoImplicit false
namespace Record1252270103Finite
def source228 : Source := ⟨(483618371601/500000000000),(204328449913/62500000000),(549989/10000000),(140837301009/250000000000),(1/100000000000000000),(1/1000000000000),(1/10000000000)⟩
theorem source228_valid : SourceValid source228 source215 (some source211) := by decide +kernel
#print axioms source228_valid
end Record1252270103Finite
