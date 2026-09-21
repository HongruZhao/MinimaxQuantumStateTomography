import TomographyOracleCore.PaperMatch.ExactTheoremThree
import TomographyOracleCore.PaperMatch.ExactSpectralMW
import TomographyOracleCore.PaperMatch.ExactCorollaryFourOMD

/-!
# Main minimax results

Theorem 3: spectral-decay minimax tomography, with OMD and weighted PLS.
Corollary 4: rank-constrained minimax tomography, with both estimators.
All declarations retain the stated measurement and fitting hypotheses.
-/
namespace MinimaxQuantumStateTomography
export TomographyOracleCore.PaperMatch.ExactMain
  (theorem3 theorem3_solver_fit theorem3_mw_record
   corollary4 corollary4_omd_record corollary4_mw)
end MinimaxQuantumStateTomography
