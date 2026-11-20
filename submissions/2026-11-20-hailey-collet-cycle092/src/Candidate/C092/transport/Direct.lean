/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectAll
import Candidate.C092.transport.DirectPairedAdmission
import Candidate.C092.transport.DirectGuards
import Candidate.C092.transport.DirectFixed
set_option autoImplicit false
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.PhysicalCertificate QRH.Coverage

/-- The actual native price rectangles remain in the two original native windows. -/
def nativeCertificateWindowsCheck (c : DirectCertificate) : Bool :=
  if c.route == .native then
    nativeWindows.any fun window => decide (Box.Included c.box window)
  else true

theorem nativeCertificates_in_windows : directCertificates.all nativeCertificateWindowsCheck = true := by
  decide +kernel

/-- Every actual original native terminal has all fifteen genuine full-source
guards at every point, including every boundary of its actual closed rectangle. -/
theorem all_actual_native_guards {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf ∈ (initialAt index).directRecords) (hr : leaf.route="native_current_exact")
    {point : Point} (hp : leaf.box.Contains point) (k : Fin 15) :
    1/2000 ≤ nativeGuard k sourceCost point.1 point.2 := by
  have ht := otherTreeCheck_sound _ _ (actual_initial_other_check index) hm
  have hc : certificateCovers .native (originalAt index).edge leaf.box = true := by
    simpa [otherLeafCheck,hr] using ht
  obtain ⟨c,hm,hroute,he,hin⟩ := certificateCovers_sound _ _ _ hc
  have hc := List.all_eq_true.mp nativeCertificates_in_windows c hm
  simp only [nativeCertificateWindowsCheck,hroute,beq_self_eq_true,↓reduceIte] at hc
  obtain ⟨window,hw,hinc⟩ := List.any_eq_true.mp hc
  exact all_native_admission_guards hw
    (Box.contains_of_included (of_decide_eq_true hinc) (Box.contains_of_included hin hp)) k

noncomputable section

def nativeJPrime (s d p : ℝ) : ℝ :=
  (5/6-d)*(-1-4/(2+10*s))+d*(-nativeA s p-4*(1-p)/(2+10*s))

def nativeUPrime (s p : ℝ) : ℝ :=
  -nativeC s p-2*(1-p)*(1-s)/(2+10*s)

/-- The native amplitude-derivative guard uses the genuine derivative of J. -/
theorem nativeJ_hasDerivAt (s d p : ℝ) :
    HasDerivAt (fun q => countJ .native s 0 d q) (nativeJPrime s d p) p := by
  have hid := hasDerivAt_id p
  have hD := (hid.const_sub 3).sub ((hid.const_mul 4).div_const (2+10*s))
  have hA := ((hid.const_mul 4).div_const (2+10*s)).const_sub 2
  convert (hD.const_mul (5/6-d)).add (((hid.const_sub 1).const_mul d).mul hA) using 1
  · ext q; dsimp [countJ,nativeD,nativeA] <;> ring
  · dsimp [nativeJPrime,nativeA]; ring

/-- The second term of that guard uses the genuine derivative of U. -/
theorem nativeU_hasDerivAt (s p : ℝ) :
    HasDerivAt (fun q => (1-q)*nativeC s q) (nativeUPrime s p) p := by
  have hid := hasDerivAt_id p
  have hC := ((hid.const_mul (2*(1-s))).div_const (2+10*s)).const_sub 1
  convert (hid.const_sub 1).mul hC using 1
  · ext q; dsimp [nativeC] <;> ring
  · dsimp [nativeUPrime,nativeC]; ring

/-- The twelfth checked native guard is exactly the authentic derivative condition. -/
theorem native_derivative_guard_identity (s d p : ℝ) :
    nativeGuard 11 s d p =
      ((1-p)*nativeC s p)*deriv (fun q => countJ .native s 0 d q) p-
        deriv (fun q => (1-q)*nativeC s q) p*countJ .native s 0 d p := by
  rw [(nativeJ_hasDerivAt s d p).deriv,(nativeU_hasDerivAt s p).deriv]
  rfl
end

end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.all_actual_direct_prices
#print axioms QRH.Cycle092.Direct.all_actual_E49_padded
#print axioms QRH.Cycle092.Direct.all_actual_E49_admitted
#print axioms QRH.Cycle092.Direct.all_actual_native_guards
#print axioms QRH.Cycle092.Direct.fixed_full_continuation

#print axioms QRH.Cycle092.Direct.native_derivative_guard_identity
