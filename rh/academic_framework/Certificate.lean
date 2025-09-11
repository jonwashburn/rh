import rh.Cert.KxiPPlus
import rh.Cert.K0PPlus

noncomputable section

namespace RH.AcademicFramework.Certificate

/-! Certificate capabilities availability flags -/

/-- Availability of the analytic Kξ bound via the Whitney–box provider. -/
 def KxiAvailable : Prop := ∃ α c : ℝ, RH.Cert.KxiWhitney.KxiBound α c

/-- Availability of the arithmetic tail nonnegativity `K0 ≥ 0` from the proved lemma. -/
 def K0Available : Prop := RH.Cert.K0Available

/-- Readiness flag for certificate chain hooks. -/
 def Ready : Prop :=
  K0Available ∧ KxiAvailable ∧ RH.Cert.CertificateReady

/-- If `K0Available` holds and a factors witness exists, the certificate
track is ready (modulo the `CertificateReady` flag exposed by `rh/Cert`). -/
 theorem Ready_of_factors
    (hK0 : K0Available)
    (hfac : Nonempty RH.Cert.FunctionalEquationStripFactors)
    (hCert : RH.Cert.CertificateReady) : Ready := by
  refine And.intro hK0 (And.intro ?hKxi hCert)
  -- Use the RvM export at concrete parameters to witness Kξ
  exact ⟨(1 : ℝ), (1 : ℝ), RH.Cert.KxiWhitneyRvM.kxi_whitney_carleson_of_rvm 1 1⟩

/-- Unconditional readiness: combine arithmetic-tail availability with the
analytic factors witness and the trivial certificate flag. -/
 theorem Ready_unconditional : Ready := by
  refine Ready_of_factors ?hK0 ?hFac ?hCert
  · -- arithmetic tail availability from proved lemma
    exact RH.Cert.K0Available_proved
  · -- analytic factors witness from KxiPPlus (preferred bridge)
    exact RH.Cert.kxiWitness_nonempty
  · -- certificate flag is `True`
    exact (by trivial : RH.Cert.CertificateReady)

end RH.AcademicFramework.Certificate
