-- The root module of the `StrataGenerators` library. Add an import here for each
-- module that the library must build.
import StrataGenerators.HasTypeAGen
-- The `retryCont` parameter of `genLExpr` does not change the set of terms that the
-- generator can produce.
import StrataGenerators.RetryGenSupport
-- The bridge between `SPMF` and `Plausible.Gen`. A generator that runs can
-- produce only terms in its `Set` support, and a retry keeps this property. The
-- converse is not proved.
import StrataGenerators.ExecRefinement
import StrataGenerators.DatatypeGen
import StrataGenerators.DatatypeGenProofs
import StrataGenerators.FunctionHasTypeAGen.IdentNameTests
import StrataGenerators.ProgramGen
import StrataGenerators.ProgramGen.Sound
import StrataGenerators.ProgramGen.ContextOkPreserve
import StrataGenerators.ProgramGen.ProcSigThread
import StrataGenerators.ProgramGen.SoundProgram
import StrataGenerators.ProgramGen.Complete
import StrataGenerators.PhaseChangedFlag
import StrataGenerators.PrinterCoverage
-- `SPMF.prob` bounds on how the size parameter shapes `genLExprBase`'s distribution: which root
-- forms each size can produce, and the size threshold for covering every form in one draw.
import StrataGenerators.SizeDistribution
import StrataGenerators.SizeDistributionStmt
import StrataGenerators.SizeDistributionFactory
import StrataGenerators.SizeDistributionLoops
import StrataGenerators.SizeDistributionProgram
