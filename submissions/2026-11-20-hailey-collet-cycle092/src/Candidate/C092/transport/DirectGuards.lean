/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.DirectGuardExp00
import Candidate.C092.transport.DirectGuardExp01
import Candidate.C092.transport.DirectGuardExp02
import Candidate.C092.transport.DirectGuardExp03
import Candidate.C092.transport.DirectGuardExp04
import Candidate.C092.transport.DirectGuardExp05
import Candidate.C092.transport.DirectGuardExp06
import Candidate.C092.transport.DirectGuardExp07
import Candidate.C092.transport.DirectGuardExp08
import Candidate.C092.transport.DirectGuardExp09
import Candidate.C092.transport.DirectGuardExp10
import Candidate.C092.transport.DirectGuardExp11
import Candidate.C092.transport.DirectGuardExp12
import Candidate.C092.transport.DirectGuardExp13
import Candidate.C092.transport.DirectGuardExp14
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.Coverage

/-- Exact reconstruction binds every guard's coefficients to its original formula. -/
theorem nativeGuard_expansion (k : Fin 15) (s : ℚ) (box : Box) (x y : ℝ) :
    nativeGuard k (s : ℝ)
      ((box.uLo : ℝ)+((box.uHi : ℝ)-box.uLo)*x)
      ((box.vLo : ℝ)+((box.vHi : ℝ)-box.vLo)*y) =
    QRH.Bernstein.value 2 3 (fun i j => (nativeGuardCoefficients k s box i j : ℝ)) x y := by
  fin_cases k
  · exact nativeGuard_expansion00 s box x y
  · exact nativeGuard_expansion01 s box x y
  · exact nativeGuard_expansion02 s box x y
  · exact nativeGuard_expansion03 s box x y
  · exact nativeGuard_expansion04 s box x y
  · exact nativeGuard_expansion05 s box x y
  · exact nativeGuard_expansion06 s box x y
  · exact nativeGuard_expansion07 s box x y
  · exact nativeGuard_expansion08 s box x y
  · exact nativeGuard_expansion09 s box x y
  · exact nativeGuard_expansion10 s box x y
  · exact nativeGuard_expansion11 s box x y
  · exact nativeGuard_expansion12 s box x y
  · exact nativeGuard_expansion13 s box x y
  · exact nativeGuard_expansion14 s box x y

def nativeWindows : List Box :=
  [⟨15/64,9/16,9/32,1/2⟩,⟨15/64,1/2,3/16,1/2⟩]

def nativeGuardsCheck (box : Box) : Bool :=
  decide (box.uLo < box.uHi ∧ box.vLo < box.vHi) &&
  (List.finRange 15).all fun i =>
    QRH.Bernstein.coefficientsCheck 2 3 (nativeGuardCoefficients i qSource box) (1/2000)

theorem nativeWindows_guards_checked : nativeWindows.all nativeGuardsCheck = true := by
  decide +kernel

/-- Every real point in either complete authentic native window satisfies all
fifteen full-source admission inequalities, with one uniform strict reserve. -/
theorem all_native_admission_guards {box : Box} (hm : box ∈ nativeWindows)
    {point : Point} (hp : box.Contains point) (i : Fin 15) :
    1/2000 ≤ nativeGuard i sourceCost point.1 point.2 := by
  have hc := List.all_eq_true.mp nativeWindows_guards_checked box hm
  simp only [nativeGuardsCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hi := List.all_eq_true.mp hc.2 i (List.mem_finRange i)
  have hu : (box.uLo : ℝ) < (box.uHi : ℝ) := Rat.cast_lt.mpr hc.1.1
  have hv : (box.vLo : ℝ) < (box.vHi : ℝ) := Rat.cast_lt.mpr hc.1.2
  have hb := QRH.Bernstein.checked_boxValue_lower_bound 2 3
    (nativeGuardCoefficients i qSource box) (1/2000) hi hu hv hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  dsimp [QRH.Bernstein.boxValue] at hb
  rw [← nativeGuard_expansion] at hb
  have hs : (qSource : ℝ) = sourceCost := by
    simp only [qSource,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]; rfl
  rw [hs] at hb
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hb
  simpa only [Physical.reconstruct hu,Physical.reconstruct hv] using hb

/-- The explicit polynomial cutoffs equal the original max/min cutoffs of M.4. -/
theorem native_original_cutoffs :
    nativeLower sourceCost = max (3/10+1/10000000 : ℝ)
      ((1-sourceCost-(2+10*sourceCost)*(3/20-1000*sourceCost/1143-1/10000000))/2+1/10000000) ∧
    (nativeUpper : ℝ) = min (11/25-1/10000000 : ℝ)
      (min (1757/4000-1/10000000)
        ((1-sourceCost-(2+10*sourceCost)*(27/1000+1/10000000))/2-1/10000000)) := by
  rcases source_contact_guards with ⟨hs,hs',_,_⟩
  constructor
  · dsimp [nativeLower]
    symm
    apply max_eq_right
    nlinarith [sq_nonneg sourceCost]
  · have h1 : (1757/4000-1/10000000 : ℝ) ≤
        (1-sourceCost-(2+10*sourceCost)*(27/1000+1/10000000))/2-1/10000000 := by
      linarith
    rw [min_eq_left h1]
    norm_num [nativeUpper]

end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.all_native_admission_guards
