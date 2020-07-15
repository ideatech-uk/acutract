module Types where

import qualified Juvix.Core.Erasure.Types as Erasure
import qualified Juvix.Core.IR as IR
import qualified Juvix.Core.Types as Core
import Juvix.Library hiding (log)

-- type of the exec result
type Exec primTy primVal compErr =
  IO
    ( Either
        (Core.PipelineError primTy primVal compErr)
        (Erasure.Term primTy primVal),
      [Core.PipelineLog primTy primVal]
    )

-- type of exec result for term assignment
type ExecTerm primTy primVal compErr =
  IO
    ( Either
        (Core.PipelineError primTy primVal compErr)
        (Core.TermAssignment primTy primVal compErr),
      [Core.PipelineLog primTy primVal]
    )

exec ::
  Show compErr =>
  EnvExec primTy primVal compErr a ->
  Core.Parameterisation primTy primVal ->
  IR.Globals primTy primVal ->
  IO
    ( Either (Core.PipelineError primTy primVal compErr) a,
      [Core.PipelineLog primTy primVal]
    )
exec (EnvE env) param globals = do
  (ret, env) <- runStateT (runExceptT env) (Env param [] globals)
  pure (ret, log env)

data Env primTy primVal
  = Env
      { parameterisation :: Core.Parameterisation primTy primVal,
        log :: [Core.PipelineLog primTy primVal],
        globals :: IR.Globals primTy primVal
      }
  deriving (Generic)

type EnvExecAlias primTy primVal compErr =
  ExceptT
    (Core.PipelineError primTy primVal compErr)
    (StateT (Env primTy primVal) IO)

newtype EnvExec primTy primVal compErr a
  = EnvE (EnvExecAlias primTy primVal compErr a)
  deriving (Functor, Applicative, Monad, MonadIO)
  deriving
    ( HasSink "log" [Core.PipelineLog primTy primVal],
      HasWriter "log" [Core.PipelineLog primTy primVal]
    )
    via WriterField "log" (EnvExecAlias primTy primVal compErr)
  deriving
    ( HasReader "parameterisation" (Core.Parameterisation primTy primVal),
      HasSource "parameterisation" (Core.Parameterisation primTy primVal)
    )
    via ReaderField "parameterisation" (EnvExecAlias primTy primVal compErr)
  deriving
    ( HasState "globals" (IR.Globals primTy primVal),
      HasSource "globals" (IR.Globals primTy primVal),
      HasSink "globals" (IR.Globals primTy primVal)
    )
    via StateField "globals" (EnvExecAlias primTy primVal compErr)
  deriving
    (HasReader "globals" (IR.Globals primTy primVal))
    via ReaderField "globals" (EnvExecAlias primTy primVal compErr)
  deriving
    (HasThrow "error" (Core.PipelineError primTy primVal compErr))
    via MonadError (EnvExecAlias primTy primVal compErr)

data SomeBackend where
  SomeBackend :: forall primTy primVal. Core.Parameterisation primTy primVal -> SomeBackend
