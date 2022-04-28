{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-|
Common types and functions used across all the ledger API modules.
-}
module Plutus.ApiCommon where

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Extras
import Codec.CBOR.Read qualified as CBOR
import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bifunctor
import Data.ByteString.Lazy (fromStrict)
import Data.ByteString.Short
import Data.Either
import Data.Foldable (fold)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text
import Data.Tuple
import GHC.Base
import GHC.Generics
import PlutusCore as PLC
import PlutusCore.Data as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.MachineParameters as Plutus
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Pretty
import PlutusPrelude (through)
import Prettyprinter
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Scope qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CekValue)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

-- | This represents the Cardano protocol version, with its major and minor components.
-- This relies on careful understanding between us and the ledger as to what this means.
data ProtocolVersion = ProtocolVersion { pvMajor :: Int, pvMinor :: Int }
  deriving stock (Show, Eq)

type LanguageVersion = PLC.Version ()

instance Eq ann => Ord (PLC.Version ann) where
    compare (PLC.Version _ major minor patch) (PLC.Version _ major' minor' patch') =
        compare major major' <> compare minor minor' <> compare patch patch'

instance Ord ProtocolVersion where
    compare (ProtocolVersion major minor) (ProtocolVersion major' minor') = compare major major' <> compare minor minor'

instance Pretty ProtocolVersion where
    pretty (ProtocolVersion major minor) = pretty major <> "." <> pretty minor

-- | A simple toggle indicating whether or not we should produce logs.
data VerboseMode = Verbose | Quiet
    deriving stock (Eq)

-- | The type of log output: just a list of 'Text'.
type LogOutput = [Text]

-- | Scripts to the ledger are serialised bytestrings.
type SerializedScript = ShortByteString

{- Note [New builtins and protocol versions]
When we add a new builtin to the language, that is a *backwards-compatible* change.
Old scripts will still work (since they don't use the new builtins), we just make some more
scripts possible.

It would be nice, therefore, to get away with just having one definition of the set of builtin
functions. Then the new builtins will just "work". However, this neglects the fact that
the new builtins will be added to the builtin universe in the *software update* that
brings a new version of Plutus, but they should only be usable after the corresponding
*hard fork*. So there is a period of time in which they must be present in the software but not
usable, so we need to decide this conditionally based on the protocol version.

To do this we need to:
- Know which protocol version a builtin was introduced in.
- Given the protocol version, check a program for builtins that should not be usable yet.

Note that this doesn't currently handle removals of builtins, although it fairly straighforwardly
could do, just by tracking when they were removed.
-}

-- | A map indicating which builtin functions were introduced in which 'ProtocolVersion'. Each builtin function should appear at most once.
--
-- This *must* be updated when new builtins are added.
-- See Note [New builtins and protocol versions]
builtinsIntroducedIn :: Map.Map (LanguageVersion, ProtocolVersion) (Set.Set PLC.DefaultFun)
builtinsIntroducedIn = Map.fromList [
  -- 5.0 is Alonzo
  ((PLC.Version () 1 0 0, ProtocolVersion 5 0), Set.fromList [
          AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger, RemainderInteger, ModInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger,
          AppendByteString, ConsByteString, SliceByteString, LengthOfByteString, IndexByteString, EqualsByteString, LessThanByteString, LessThanEqualsByteString,
          Sha2_256, Sha3_256, Blake2b_256, VerifySignature,
          AppendString, EqualsString, EncodeUtf8, DecodeUtf8,
          IfThenElse,
          ChooseUnit,
          Trace,
          FstPair, SndPair,
          ChooseList, MkCons, HeadList, TailList, NullList,
          ChooseData, ConstrData, MapData, ListData, IData, BData, UnConstrData, UnMapData, UnListData, UnIData, UnBData, EqualsData,
          MkPairData, MkNilData, MkNilPairData
          ]),
  ((PLC.Version () 2 0 0, ProtocolVersion 6 0), Set.fromList [
          SerialiseData, VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature
          ])
  ]

-- | Which builtin functions are available in the given 'ProtocolVersion'?
--
-- See Note [New builtins and protocol versions]
builtinsAvailableIn :: LanguageVersion -> ProtocolVersion -> Set.Set PLC.DefaultFun
builtinsAvailableIn lv pv = fold $ Map.elems $ Map.takeWhileAntitone (\(introducedInLv, introducedInPv) -> introducedInLv <= lv && introducedInPv <= pv) builtinsIntroducedIn

-- | Which unlifting mode should we use in the given 'ProtocolVersion'
unliftingModeIn :: ProtocolVersion -> PLC.UnliftingMode
-- This just changes once in version 6.0
unliftingModeIn pv = if pv >= ProtocolVersion 6 0 then PLC.UnliftingDeferred else PLC.UnliftingImmediate



-- | Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.
isScriptWellFormed :: LanguageVersion -> ProtocolVersion -> SerializedScript -> Bool
isScriptWellFormed lv pv = isRight . CBOR.deserialiseFromBytes (scriptCBORDecoder lv pv) . fromStrict . fromShort


-- | A variant of `Script` with a specialized decoder.
newtype ScriptForExecution = ScriptForExecution (UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())

{- |
This decoder decodes the names directly into `NamedDeBruijn`s rather than `DeBruijn`s.
This is needed because the CEK machine expects `NameDeBruijn`s, but there are obviously no names in the serialized form of a `Script`.
Rather than traversing the term and inserting fake names after deserializing, this lets us do at the same time as deserializing.
-}
scriptCBORDecoder :: LanguageVersion -> ProtocolVersion -> CBOR.Decoder s ScriptForExecution
scriptCBORDecoder lv pv =
    -- See Note [New builtins and protocol versions]
    let availableBuiltins = builtinsAvailableIn lv pv
        -- TODO: optimize this by using a better datastructure e.g. 'IntSet'
        flatDecoder = UPLC.decodeProgram UPLC.NoLimit (\f -> f `Set.member` availableBuiltins)
    in do
        -- Deserialize using 'FakeNamedDeBruijn' to get the fake names added
        (p :: UPLC.Program UPLC.FakeNamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()) <- decodeViaFlat flatDecoder
        pure $ coerce p


-- | Errors that can be thrown when evaluating a Plutus script.
data EvaluationError =
    CekError (UPLC.CekEvaluationException PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun) -- ^ An error from the evaluator itself
    | DeBruijnError PLC.FreeVariableError -- ^ An error in the pre-evaluation step of converting from de-Bruijn indices
    | CodecError CBOR.DeserialiseFailure -- ^ A serialisation error
    | IncompatibleVersionError (PLC.Version ()) -- ^ An error indicating a version tag that we don't support
    -- TODO: make this error more informative when we have more information about what went wrong
    | CostModelParameterMismatch -- ^ An error indicating that the cost model parameters didn't match what we expected
    deriving stock (Show, Eq)

instance Pretty EvaluationError where
    pretty (CekError e)      = prettyClassicDef e
    pretty (DeBruijnError e) = pretty e
    pretty (CodecError e) = viaShow e
    pretty (IncompatibleVersionError actual) = "This version of the Plutus Core interface does not support the version indicated by the AST:" <+> pretty actual
    pretty CostModelParameterMismatch = "Cost model parameters were not as we expected"


-- | Shared helper for the evaluation functions, deserializes the 'SerializedScript' , applies it to its arguments, puts fakenamedebruijns, and scope-checks it.
mkTermToEvaluate
    :: (MonadError EvaluationError m)
    => LanguageVersion
    -> ProtocolVersion
    -> SerializedScript
    -> [PLC.Data]
    -> m (UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())
mkTermToEvaluate lv pv bs args = do
    -- It decodes the program through the optimized ScriptForExecution. See `ScriptForExecution`.
    (_, ScriptForExecution (UPLC.Program _ v t)) <- liftEither $ first CodecError $ CBOR.deserialiseFromBytes (scriptCBORDecoder lv pv) $ fromStrict $ fromShort bs
    unless (v == PLC.defaultVersion ()) $ throwError $ IncompatibleVersionError v
    let termArgs = fmap (PLC.mkConstant ()) args
        appliedT = PLC.mkIterApp () t termArgs

    -- make sure that term is closed, i.e. well-scoped
    through (liftEither . first DeBruijnError . UPLC.checkScope) appliedT


-- | Evaluates a script, with a cost model and a budget that restricts how many
-- resources it can use according to the cost model. Also returns the budget that
-- was actually used.
--
-- Can be used to calculate budgets for scripts, but even in this case you must give
-- a limit to guard against scripts that run for a long time or loop.
evaluateScriptRestricting
    :: LanguageVersion
    -> ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerializedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting lv pv verbose ectx budget p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate lv pv p args

    let (res, UPLC.RestrictingSt (PLC.ExRestrictingBudget final), logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters pv ectx)
                (UPLC.restricting $ PLC.ExRestrictingBudget budget)
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure (budget `PLC.minusExBudget` final)

-- | Evaluates a script, returning the minimum budget that the script would need
-- to evaluate successfully. This will take as long as the script takes, if you need to
-- limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
-- also returns the used budget.
evaluateScriptCounting
    :: LanguageVersion
    -> ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> SerializedScript          -- ^ The script to evaluate
    -> [PLC.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting lv pv verbose ectx p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate lv pv p args

    let (res, UPLC.CountingSt final, logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters pv ectx)
                UPLC.counting
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure final

type DefaultMachineParameters =
    Plutus.MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun


-- | An opaque type that contains all the static parameters that the evaluator needs to evaluate a
-- script.  This is so that they can be computed once and cached, rather than recomputed on every
-- evaluation.
--
-- There are two sets of parameters: one is with immediate unlifting and the other one is with
-- deferred unlifting. We have to keep both of them, because depending on the language version
-- either one has to be used or the other. We also compile them separately due to all the inlining
-- and optimization that need to happen for things to be efficient.
data EvaluationContext = EvaluationContext
    { machineParametersImmediate :: DefaultMachineParameters
    , machineParametersDeferred  :: DefaultMachineParameters
    }
    deriving stock Generic
    deriving anyclass NFData


toMachineParameters :: ProtocolVersion -> EvaluationContext -> DefaultMachineParameters
toMachineParameters pv = case unliftingModeIn pv of
    UnliftingImmediate -> machineParametersImmediate
    UnliftingDeferred  -> machineParametersDeferred

