/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Count-admission arithmetic only; source moment theorems are separate. -/
import Candidate.Uneven.RoundedRowsBase

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

def admissionGuard (i g : ℕ) (d p : ℝ) : ℝ :=
  let B := planeB i
  let L := planeLambda i
  let D := 3-p-4*p/L
  let A := 2-4*p/L
  let C := 1-2*p*B/L
  let J := (5/6-d)*D+d*(1-p)*A
  let t := J+d*(1-p)*C
  let r := A*t+(2*p*B/L-p)*J
  let m := D*t-r
  let N := (1-d)*J+(5/6-d)*d*(1-p)*C
  let U := (1-p)*C
  let Up := -C+(1-p)*(-2*B/L)
  let Jp := (5/6-d)*(-1-4/L)+d*(-A+(1-p)*(-4/L))
  let mlo := max (405/1000) ((B-L*(4/100))/2+1/100000)
  let mhi := (423533456/1000000000:ℝ)
  let whi := (B-L*(3401/100000))/2-1/100000
  match g with
  | 0 => D
  | 1 => A
  | 2 => C
  | 3 => J
  | 4 => t-J
  | 5 => (12499/10000)*J-t
  | 6 => r-(23/37)*D*J
  | 7 => D*J-r
  | 8 => m-mlo*D*J
  | 9 => mhi*D*J-m
  | 10 => whi*D*J-m
  | 11 => N-(1-2*d*mhi-2*d*p*(34/1000))*J
  | 12 => U*Jp-Up*J
  | _ => 0

end Sil.Uneven.RoundedRows
