/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group30_raw0 : ((group30.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw1 : ((group30.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw2 : ((group30.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw3 : ((group30.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw4 : ((group30.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw5 : ((group30.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw6 : ((group30.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group30_raw_checked : group30.all rawBridgeCheck=true := by
  have he : group30 = ((group30.drop 0).take 50) ++ ((group30.drop 50).take 50) ++ ((group30.drop 100).take 50) ++ ((group30.drop 150).take 50) ++ ((group30.drop 200).take 50) ++ ((group30.drop 250).take 50) ++ ((group30.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group30_raw0,group30_raw1,group30_raw2,group30_raw3,group30_raw4,group30_raw5,group30_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
