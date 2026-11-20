/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.DirectGuardModels
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.Coverage
theorem nativeGuard_expansion02 (s : ℚ) (box : Box) (x y : ℝ) :
    nativeGuard 2 (s : ℝ)
      ((box.uLo : ℝ)+((box.uHi : ℝ)-box.uLo)*x)
      ((box.vLo : ℝ)+((box.vHi : ℝ)-box.vLo)*y) =
    QRH.Bernstein.value 2 3 (fun i j => (nativeGuardCoefficients 2 s box i j : ℝ)) x y := by
  norm_num [QRH.Bernstein.value,QRH.Bernstein.tensorBasis,QRH.Bernstein.basis,
    Finset.sum_range_succ,nativeGuardCoefficients,Physical.quadraticCoefficients,cubicCoefficients]
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_neg,nativeGuard_cast]
  norm_num [nativeGuard,nativeLower,nativeUpper,nativeD,nativeA,nativeC,countJ,countN] <;> ring

end QRH.Cycle092.Direct
