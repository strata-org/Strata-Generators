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
import StrataGenerators.ProgramGen.CompleteProcedure
-- Whole-program completeness for some bounds record, from per-step reachability at every large
-- enough bounds record.
import StrataGenerators.ProgramGen.CompleteEventually
import StrataGenerators.PhaseChangedFlag
import StrataGenerators.PrinterCoverage
-- `SPMF.prob` bounds on how the size and the body-length cap shape the statement generator's
-- distribution: probability lower bounds on nested statements, and upper bounds on their expected number.
import StrataGenerators.SizeDistribution
import StrataGenerators.SizeDistributionStmt
import StrataGenerators.SizeDistributionLoops
-- Completeness of `genStmt` for some size and some body-length cap, with size-free side conditions.
import StrataGenerators.StmtHasTypeAGenCompleteExists
-- Completeness of `genProcedure` at every large enough size, body length and cap, through the
-- size-free statement completeness.
import StrataGenerators.ProcedureHasTypeAGenCompleteExists
