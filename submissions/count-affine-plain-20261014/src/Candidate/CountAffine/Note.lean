/-
WORK-IN-PROGRESS NOTE (A48, for liqsweep; AI-assisted). Plain text in a Lean comment because submissions
may contain only Lean source. Apache 2.0.

RESULT (claimed, Lean proof INCOMPLETE)
  Every Dirichlet L-function is nonzero on Re s > 2187109/2500000 = 0.8748436, except the pole of zeta at 1.
  Parameters: Collet's cycle61 architecture with Zhongpai Gao's constants (q0 = 67/100, lambda = 16281/4106,
  B = 2025/2053 - 1/100000), theta = 2187109/2500000, h = 497/625.  The best value at Gao's h is
  1749691/2000000 = 0.8748455 (all gates pass; top row needs 13 exact boxes); 0.8748443 at Gao's h FAILS
  Collet's plain gate n_max = 1 - y/dPlus + t0 <= 264/625.

MECHANISM (one new step; everything else is Collet's)
  Collet's interior affine moment (cycle61 manuscript, Theorem 2.2, tracker PR #42):
    sum_u |S_1(Z^n1) S_2(Z^n2) Q_I|^2 << Z^(1+eps) H_J   when .41 <= n_i <= .44, .034 <= z_I <= .04,
    n1 + n2 + lambda z_I <= B,
  is used on the leaderboard only in the numerator.  The detector count (Collet (3.10); OAI Prop. 19.2) bounds
  the plain witnesses by the 6-kappa moment.  The count's critical plain witness (m* ~ 0.418, slot width
  0.036-0.040) lies inside the window of Theorem 2.2, and the count's slotted plain moment is the same
  fixed-parent energy with the detector label character as anchor.  Using Theorem 2.2 there gives, for plain
  lengths m in [41/100, 264/625], the slot capacity z_S(m) = min(1/25, (B - 2m)/lambda) instead of
  (1 - 2m)/(6 kappa).  Shortened slot sets (sum w < 17/500) still use the old moment because
  2(264/625) + (9/2)(17/500) = 1 - 11/5000.
  With q = delta p, sI = delta - q, sP = 2 delta - 4q/lambda, aP = 1 - 2qB/lambda, the balanced cut-off is
    t* = [(1-q) sP + aP sI - (sI+sP)/6] / [(5/6 - delta)(sI+sP) + sI sP],   R* = 1/6 + (5/6 - delta) t*,
  and the class count is min(R_kappa, max(R*, A_Po(264/625))) on the closed-form region, R_kappa elsewhere.
  The four-branch case analysis is proved in Lean (Branch.lean: affine_count_bound_of_branches); the region
  side conditions are certified exactly (RegionCert.lean, RegionFacts.lean, on R1 = [29/64,63/128]x[15/32,1/2]
  and R2 = [115/256,29/64]x[31/64,1/2]; R* is nonincreasing in p there).
  kappa feedback: the new branch moves with kappa only through A_Po(264/625); on the region its slope is
  <= q(1-2N)/(3 kappa*^2) < 5/216, Collet's own R_kappa slope bound, so the feedback constants are unchanged.

EXACT CERTIFICATES (python-flint rationals; agents A38, A44, A48 of the H3 project)
  theta = 2187109/2500000, h = 497/625:
    top row d = h, saving 1e-6: 199 R_kappa Bernstein boxes + 8 closed-form boxes, min coefficient 6.1e-8
      closed-form boxes: [57/128,115/256]x[63/128,1/2], [115/256,29/64]x[31/64,1/2], [29/64,59/128]x[15/32,1/2],
      [59/128,119/256]x[31/64,1/2], [119/256,239/512]x[63/128,1/2], [239/512,15/32]x[63/128,1/2],
      [15/32,31/64]x[7/16,1/2], [31/64,63/128]x[15/32,1/2];
      independently re-certified by monotone boxes (102,671 boxes).
    junction d = d-, saving 1e-5: Collet's 6 boxes, min 1.897e-4.   half row, saving 1e-3: 1 box, min 5.203e-2.
    Gates (Collet S3-S5, Gao PR #43 list, gates_a44.py): 51/51 hold, including b_max <= 4/25 (slack 5.2e-5)
    and the new-count feedback room 1/8 - (3/4) d+ (97/2450) > 0.  Proved in Lean at this point: Record.lean (plain_window, slot_window,
    shift_gate, kappa_window, floor_gate, lower_row_gate, supply_gates, geometry_gates).
  Control (A44): without the count-side branch the neighbouring point 1749687/2000000 at h = 1591/2000 fails
  (G - (theta - 1e-6) = +6.9e-5 at delta 0.4655, p 1/2), so the gain comes from the new branch.

NOT YET FORMALIZED (each marked `sorry` in Assembly.lean / Record.lean)
  constants propagation (h = 497/625 lies above Gao's coarse h_interval); count branch plumbing in the OAI
  fiber/batch API; the Theorem 2.2 instance for the count's label characters (InitialAffineAt with anchor
  lambda = sourceMomentBase ... label); per-target choice of the height exponent tau in the final assembly;
  the Lean endpoint certificate (and closed-form gates on the A44 boxes outside R1 u R2).

CREDITS
  Theorem 2.2, the cycle61 architecture, the physical count and the Lean source: Hailey Collet (PR #42; her paper
  states the derivations and formalization were AI-assisted).  Constants q0 = 67/100 and the merged record
  0.8748598: Zhongpai Gao (PR #43).  Hoelder-averaged class numerator: Sang (arXiv 2610.15291) / Akash Levy's
  weighted numerator on the tracker.  kappa = 2B - 1 plain moment: Liu (arXiv 2610.12234 v2).  7/8 framework and
  Lean library: OpenAI (openai/math).  Related, independent: PR #48 (timbalud) also modifies the high-zero count
  (prime-slot amplitudes), by a different mechanism.  The count-side reuse of Theorem 2.2 and its certificates:
  H3 project agents A38, A40, A44, A48 for liqsweep.
-/
