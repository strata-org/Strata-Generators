-- This module serves as the root of the `StrataGenerators` library.
-- Import modules here that should be built as part of the library.
import StrataGenerators.HasTypeAGen
-- `genLExpr`'s `retryCont` parameter does not change what the generator can
-- produce, so the results above describe the retrying production generator too.
import StrataGenerators.RetryGenSupport
-- The `SetGen.Set`/`Plausible.Gen` bridge: executing a generator can only produce
-- terms in its `Set` support (a refinement, not an adequacy -- the converse is not
-- proved), and retrying preserves that.
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
