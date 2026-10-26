/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.GenericData
open QRH.RH20261023Return

namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
abbrev BaselineData := QRH.RH20261023Return.GenericPhysical.BaselineData
abbrev BaselineSourceData (D : BaselineData) := QRH.RH20261023Return.GenericPhysical.BaselineSourceData D
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect
