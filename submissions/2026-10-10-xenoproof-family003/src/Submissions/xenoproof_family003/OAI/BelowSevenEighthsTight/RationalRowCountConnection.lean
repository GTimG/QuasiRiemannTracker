import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedRowCountBranches

/- Exact numerical use of the four analytic branch estimates at sigmaRat.
   The branch estimates remain hypotheses, not axioms or constructed inputs. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.RowCountExtension
noncomputable section

theorem rational_count_bound_of_source_branches (B C U d y β r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hd : 0 ≤ d) (hdu : d ≤ 5/6)
    (hy : 0 ≤ y) (hyu : y ≤ 1/2) (hβ : sigmaRat ≤ β) (hβu : β ≤ 1)
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : adaptiveSplit cRat d y-r-γ ≤ m)
    (hright : r ≤ adaptiveSplit cRat d y+γ)
    (hI0 : B ≤ C*U^(max 1 ((1+5*r)/6)-d*r+ε))
    (hP0 : B ≤ C*U^(1-2*d*m+ε))
    (hI : 23/37 ≤ r → r < 1 → ν < (1-r)/2 →
      B ≤ C*U^(inverseExponent d (1/2-y) r+ε))
    (hP : r ≤ crossing cRat (1/2-y) (adaptiveSplit cRat d y) →
      m < 1/2 → ν < (1-2*m)/(6*(2*β-1)) →
      B ≤ C*U^(1-2*d*m-2*(d*(1/2-y))*(1-2*m)/(6*(2*β-1))+ε)) :
    B ≤ C*U^(countR d y+(β-sigmaRat)/4+ε+6*ν+5*γ) := by
  have hc : (4/9 : ℝ) ≤ cRat := by norm_num [cRat, kappaRat]
  have hcu : cRat ≤ (6/13 : ℝ) := by norm_num [cRat, kappaRat]
  have ht := adaptive_split_range cRat d y hc hcu hd hdu hy hyu
  have hb := count_bound_of_source_branches B C U d (1/2-y) (β-sigmaRat)
    (adaptiveSplit cRat d y) r m ε ν γ kappaRat (2*β-1)
    hC hU hd hdu (by linarith) (by linarith) (by linarith)
    (by norm_num [kappaRat]) (by norm_num [kappaRat])
    (by norm_num [kappaRat, sigmaRat] <;> ring) (by linarith)
    ht.1 ht.2 hν hγ hleft hright hI0 hP0 hI hP
  change B ≤ C*U^(max (shortExponent cRat d (1/2-y) (adaptiveSplit cRat d y))
    (longExponent d (adaptiveSplit cRat d y))+(β-sigmaRat)/4+ε+6*ν+5*γ) at hb
  have hlong : longExponent d (adaptiveSplit cRat d y) = countR d y :=
    (long_at_adaptive_split cRat d y).trans (rational_envelope_identity d y)
  rw [rational_short_matches_certificate d y hd hdu hy hyu, hlong, max_self] at hb
  exact hb

#print axioms rational_count_bound_of_source_branches
end
end BelowSevenEighthsTight.RowCountExtension
