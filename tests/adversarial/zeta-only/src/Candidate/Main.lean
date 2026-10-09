import Mathlib
namespace Candidate
open scoped DirichletCharacter
theorem bound {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) (h : riemannZeta s ≠ 0) : riemannZeta s ≠ 0 := h
end Candidate
