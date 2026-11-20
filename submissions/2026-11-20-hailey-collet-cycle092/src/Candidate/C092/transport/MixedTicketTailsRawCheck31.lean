/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group31_raw0 : ((group31.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw1 : ((group31.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw2 : ((group31.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw3 : ((group31.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw4 : ((group31.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw5 : ((group31.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw6 : ((group31.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group31_raw_checked : group31.all rawBridgeCheck=true := by
  have he : group31 = ((group31.drop 0).take 50) ++ ((group31.drop 50).take 50) ++ ((group31.drop 100).take 50) ++ ((group31.drop 150).take 50) ++ ((group31.drop 200).take 50) ++ ((group31.drop 250).take 50) ++ ((group31.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group31_raw0,group31_raw1,group31_raw2,group31_raw3,group31_raw4,group31_raw5,group31_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
