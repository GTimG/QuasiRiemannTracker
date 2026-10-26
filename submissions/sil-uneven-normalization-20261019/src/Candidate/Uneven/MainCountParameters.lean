/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.Count.Arithmetic
import Candidate.Uneven.MainParameters

namespace OAI.SevenEighths.MainCount
noncomputable section
inductive Plane where
  | PR62 | PR60 | oldA | oldC | oldWeak | A | C | A2 | C2
  deriving DecidableEq

namespace Plane
def B : Plane → ℝ
  | .PR62 => 987047/1000000
  | .PR60 => 142100527/143610000
  | .oldA => 9816147/10000000
  | .oldC => 3915977/4000000
  | .oldWeak => 1005451199/1000000000
  | .A => 49061544613/50000000000
  | .C => 97851371081/100000000000
  | .A2 => 2453191/2500000
  | .C2 => 9787409/10000000

def lambda : Plane → ℝ
  | .PR62 => 19793/5000
  | .PR60 => 19312/4787
  | .oldA => 37961251/10000000
  | .oldC => 372765011/100000000
  | .oldWeak => 44999/10000
  | .A => 1891221821/500000000
  | .C => 18557733993/5000000000
  | .A2 => 7567449/2000000
  | .C2 => 37174059/10000000

def ofOld : Target830.Count.Plane → Plane
  | .PR62 => .PR62 | .PR60 => .PR60 | .A => .oldA | .C => .oldC | .oldWeak => .oldWeak

@[simp] theorem ofOld_B (P : Target830.Count.Plane) : (ofOld P).B=P.B := by cases P <;> rfl
@[simp] theorem ofOld_lambda (P : Target830.Count.Plane) : (ofOld P).lambda=P.lambda := by cases P <;> rfl
end Plane

abbrev mHi : ℝ := Target830.Count.mHi
end
end OAI.SevenEighths.MainCount
