/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group28_raw0 : ((group28.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw1 : ((group28.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw2 : ((group28.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw3 : ((group28.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw4 : ((group28.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw5 : ((group28.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw6 : ((group28.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group28_raw_checked : group28.all rawBridgeCheck=true := by
  have he : group28 = ((group28.drop 0).take 50) ++ ((group28.drop 50).take 50) ++ ((group28.drop 100).take 50) ++ ((group28.drop 150).take 50) ++ ((group28.drop 200).take 50) ++ ((group28.drop 250).take 50) ++ ((group28.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group28_raw0,group28_raw1,group28_raw2,group28_raw3,group28_raw4,group28_raw5,group28_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
