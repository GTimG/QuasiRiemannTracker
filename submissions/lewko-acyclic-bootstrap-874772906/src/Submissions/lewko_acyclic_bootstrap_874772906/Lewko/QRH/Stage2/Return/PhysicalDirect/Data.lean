/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.GenericData
open QRH.LewkoStage2Return

namespace QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
abbrev BaselineData := QRH.LewkoStage2Return.GenericPhysical.BaselineData
abbrev BaselineSourceData (D : BaselineData) := QRH.LewkoStage2Return.GenericPhysical.BaselineSourceData D
end QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect
