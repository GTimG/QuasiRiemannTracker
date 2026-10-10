import ZetaZeroFree.Exponent
import ZetaZeroFree.Analytic.Continuation
import ZetaZeroFree.Analytic.Energy.CompletedSource
import ZetaZeroFree.Analytic.Energy.GaussianSource
import ZetaZeroFree.Analytic.Energy.Geometry
import ZetaZeroFree.Analytic.Energy.PhysicalSource
import ZetaZeroFree.Analytic.Energy.WholeIndex
import ZetaZeroFree.Analytic.Final
import ZetaZeroFree.Analytic.LossBudget
import ZetaZeroFree.Analytic.Moments.AppendixD3
import ZetaZeroFree.Analytic.Moments.CompactProfiles
import ZetaZeroFree.Analytic.Moments.Exceptional
import ZetaZeroFree.Analytic.Moments.FixedFactor
import ZetaZeroFree.Analytic.Moments.Plain
import ZetaZeroFree.Analytic.Moments.Presentation
import ZetaZeroFree.Analytic.Moments.Sharp
import ZetaZeroFree.Analytic.Moments.Source
import ZetaZeroFree.Analytic.Moments.Unconditional
import ZetaZeroFree.Analytic.Parameters
import ZetaZeroFree.Analytic.Principal.Residues
import ZetaZeroFree.Analytic.Principal.Signal
import ZetaZeroFree.Analytic.Probe.Assembly
import ZetaZeroFree.Analytic.Probe.Band
import ZetaZeroFree.Analytic.Probe.Central
import ZetaZeroFree.Analytic.Probe.Collected
import ZetaZeroFree.Analytic.Probe.Transport
import ZetaZeroFree.Analytic.Rows.Count
import ZetaZeroFree.Analytic.Rows.SourceCount
import ZetaZeroFree.Analytic.Rows.UniformProfiles
import ZetaZeroFree.Analytic.Rows.Witness
import ZetaZeroFree.Analytic.SourceData
import ZetaZeroFree.Analytic.Starter.Inverse
import ZetaZeroFree.Analytic.Starter.Nonvanishing
import ZetaZeroFree.Analytic.Audit

set_option maxHeartbeats 0
run_cmd ZetaZeroFree.AnalyticVerification.audit #[`ZetaZeroFree.Exponent, `ZetaZeroFree.Analytic.Continuation, `ZetaZeroFree.Analytic.Energy.CompletedSource, `ZetaZeroFree.Analytic.Energy.GaussianSource, `ZetaZeroFree.Analytic.Energy.Geometry, `ZetaZeroFree.Analytic.Energy.PhysicalSource, `ZetaZeroFree.Analytic.Energy.WholeIndex, `ZetaZeroFree.Analytic.Final, `ZetaZeroFree.Analytic.LossBudget, `ZetaZeroFree.Analytic.Moments.AppendixD3, `ZetaZeroFree.Analytic.Moments.CompactProfiles, `ZetaZeroFree.Analytic.Moments.Exceptional, `ZetaZeroFree.Analytic.Moments.FixedFactor, `ZetaZeroFree.Analytic.Moments.Plain, `ZetaZeroFree.Analytic.Moments.Presentation, `ZetaZeroFree.Analytic.Moments.Sharp, `ZetaZeroFree.Analytic.Moments.Source, `ZetaZeroFree.Analytic.Moments.Unconditional, `ZetaZeroFree.Analytic.Parameters, `ZetaZeroFree.Analytic.Principal.Residues, `ZetaZeroFree.Analytic.Principal.Signal, `ZetaZeroFree.Analytic.Probe.Assembly, `ZetaZeroFree.Analytic.Probe.Band, `ZetaZeroFree.Analytic.Probe.Central, `ZetaZeroFree.Analytic.Probe.Collected, `ZetaZeroFree.Analytic.Probe.Transport, `ZetaZeroFree.Analytic.Rows.Count, `ZetaZeroFree.Analytic.Rows.SourceCount, `ZetaZeroFree.Analytic.Rows.UniformProfiles, `ZetaZeroFree.Analytic.Rows.Witness, `ZetaZeroFree.Analytic.SourceData, `ZetaZeroFree.Analytic.Starter.Inverse, `ZetaZeroFree.Analytic.Starter.Nonvanishing] #[``ZetaZeroFree.Analytic.beta_le_twenty_nine_thirty_thirds, ``ZetaZeroFree.Analytic.common_deleted_probe_estimates, ``ZetaZeroFree.Analytic.heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re, ``ZetaZeroFree.Analytic.dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re, ``ZetaZeroFree.Analytic.riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re, ``ZetaZeroFree.Analytic.Probe.source_data_central_band_bound, ``ZetaZeroFree.Analytic.Energy.source_probe_bound, ``ZetaZeroFree.Analytic.Moments.Unconditional.all_nonprincipal_at, ``ZetaZeroFree.Analytic.Moments.D3.mixed_plain_moment_radical]
run_cmd ZetaZeroFree.AnalyticVerification.auditD3Independence #[``ZetaZeroFree.Analytic.Moments.Unconditional.all_nonprincipal_at, ``ZetaZeroFree.Analytic.Moments.D3.mixed_plain_moment_radical]
