{-# LANGUAGE FlexibleContexts #-}
{-|
Defines how things will be called in the CCode generated by CodeGen.hs
Provides mappings from class/method names to their C-name.

The purpose of this module is to

 - get one central place where identifiers in the generated code can be changed

 - ease following of good conventions (ie use @Ptr char@ instead of @Embed "char*"@)

-}

module CodeGen.CCodeNames where

import qualified Identifiers as ID
import Types as Ty
import CCode.Main
import Data.List
import Data.Char
import Data.String.Utils

import qualified AST.AST as A

import Text.Printf (printf)
import Debug.Trace

char :: CCode Ty
char = Typ "char"

int :: CCode Ty
int = Typ "int64_t"

uint :: CCode Ty
uint = Typ "uint64_t"

bool :: CCode Ty
bool = Typ "int64_t" -- For pony argument tag compatibility. Should be changed to something smaller

double :: CCode Ty
double = Typ "double"

void :: CCode Ty
void = Typ "void"

encoreActorT :: CCode Ty
encoreActorT = Typ "encore_actor_t"

ponyTypeT :: CCode Ty
ponyTypeT = Typ "pony_type_t"

ponyActorT :: CCode Ty
ponyActorT = Typ "pony_actor_t"

ponyActorTypeT :: CCode Ty
ponyActorTypeT = Typ "pony_actor_type_t"

encoreArgT :: CCode Ty
encoreArgT = Typ "encore_arg_t"

isEncoreArgT :: CCode Ty -> Bool
isEncoreArgT (Typ "encore_arg_t") = True
isEncoreArgT _ = False

ponyMsgT :: CCode Ty
ponyMsgT = Typ "pony_msg_t"

ponyMainMsgName :: String
ponyMainMsgName = "pony_main_msg_t"

ponyMainMsgT :: CCode Ty
ponyMainMsgT = Typ ponyMainMsgName

encMsgT :: CCode Ty
encMsgT = Typ "encore_fut_msg_t"

encOnewayMsgT :: CCode Ty
encOnewayMsgT = Typ "encore_oneway_msg_t"

closure :: CCode Ty
closure = Ptr $ Typ "closure_t"

future :: CCode Ty
future = Ptr $ Typ "future_t"

stream :: CCode Ty
stream = Ptr $ Typ "stream_t"

array :: CCode Ty
array = Ptr $ Typ "array_t"

tuple :: CCode Ty
tuple = Ptr $ Typ "tuple_t"

rangeT :: CCode Ty
rangeT = Typ "range_t"

range :: CCode Ty
range = Ptr rangeT

optionT :: CCode Name
optionT = Nam "option_t"

option :: CCode Ty
option = Ptr $ Typ "option_t"

par :: CCode Ty
par = Ptr $ Typ "par_t"

capability :: CCode Ty
capability = Ptr $ Typ "capability_t"

ponyTraceFnType :: CCode Ty
ponyTraceFnType = Typ "pony_trace_fn"

ponyTrace :: CCode Name
ponyTrace = Nam "pony_trace"

ponyTraceObject :: CCode Name
ponyTraceObject = Nam "encore_trace_object"

ponyTraceActor :: CCode Name
ponyTraceActor = Nam "encore_trace_actor"

unit :: CCode Lval
unit = Embed "UNIT"

nothing :: CCode Lval
nothing = Var "NOTHING"

just :: CCode Lval
just = Var "JUST"

futVar :: CCode Lval
futVar = Var "_fut"

encoreAssert :: CCode Expr -> CCode Stat
encoreAssert p =
  Statement $ Call (Nam "encore_assert") [Cast (Typ "intptr_t") p]

this :: String
this = "_this"

thisName :: CCode Name
thisName = Nam this

thisVar :: CCode Lval
thisVar = Var this

env :: String
env = "_env"

envVar :: CCode Lval
envVar = Var env

encoreName :: String -> String -> String
encoreName kind name =
  let
    (prefix, name') = fixPrimes name
    enc = let alphas = filter isAlpha kind
          in if not (null alphas) && all isUpper alphas
             then "_ENC_"
             else "_enc_"
    nonEmptys = filter (not . null) [enc, prefix, kind, name']
  in
    intercalate "_" nonEmptys


qualifyRefType :: Ty.Type -> String
qualifyRefType ty
  | isRefAtomType ty = show (getRefNamePrefix ty) ++ --sourceToString (Ty.getRefSourceFile ty) ++
                       "_" ++ Ty.getId ty
  | otherwise = error "CCodeNames.hs: not a ref type: " ++ show ty

{-
qualifyRefType :: Ty.Type -> String
qualifyRefType ty
  | isRefAtomType ty = sourceToString (Ty.getRefSourceFile ty) ++
                       "_" ++ Ty.getId ty
  | otherwise = error "CCodeNames.hs: not a ref type: " ++ show ty
-}
fixPrimes name
    | '\'' `elem` name =
        let nameWithoutPrimes = replace "'" "_" name
            expandedName = replace "'" "_prime" name
        in (nameWithoutPrimes, expandedName)
    | otherwise = ("", name)

selfTypeField :: CCode Name
selfTypeField = Nam $ encoreName "self_type" ""

-- | each method is implemented as a function with a `this`
-- pointer. This is the name of that function
methodImplName :: Ty.Type -> ID.Name -> CCode Name
methodImplName clazz mname = Nam $ methodImplNameStr clazz mname

forwardingMethodImplName :: Ty.Type -> ID.Name -> CCode Name
forwardingMethodImplName clazz mname =
  Nam $ forwardingMethodImplNameStr clazz mname

callMethodFutureName :: Ty.Type -> ID.Name -> CCode Name
callMethodFutureName clazz mname =
  Nam $ callMethodFutureNameStr clazz mname

methodImplForwardName :: Ty.Type -> ID.Name -> CCode Name
methodImplForwardName clazz mname =
  Nam $ methodImplForwardNameStr clazz mname

methodImplOneWayName :: Ty.Type -> ID.Name -> CCode Name
methodImplOneWayName clazz mname =
  Nam $ methodImplOneWayNameStr clazz mname

methodImplStreamName :: Ty.Type -> ID.Name -> CCode Name
methodImplStreamName clazz mname =
  Nam $ encoreName "method" $ printf "%s_%s_stream"
                              (qualifyRefType clazz) (show mname)

methodImplNameStr :: Ty.Type -> ID.Name -> String
methodImplNameStr clazz mname =
  encoreName "method" $ qualifyRefType clazz ++ "_" ++ show mname

forwardingMethodImplNameStr :: Ty.Type -> ID.Name -> String
forwardingMethodImplNameStr clazz mname =
  encoreName "forwarding_method" $ qualifyRefType clazz ++ "_" ++ show mname

callMethodFutureNameStr :: Ty.Type -> ID.Name -> String
callMethodFutureNameStr clazz mname =
  methodImplNameStr clazz mname ++ "_future"

methodImplForwardNameStr :: Ty.Type -> ID.Name -> String
methodImplForwardNameStr clazz mname =
  methodImplNameStr clazz mname ++ "_forward"

methodImplOneWayNameStr :: Ty.Type -> ID.Name -> String
methodImplOneWayNameStr clazz mname =
  methodImplNameStr clazz mname ++ "_one_way"

constructorImplName :: Ty.Type -> CCode Name
constructorImplName clazz =
  Nam $ encoreName "constructor" (qualifyRefType clazz)

encoreCreateName :: CCode Name
encoreCreateName = Nam "encore_create"

encoreAllocName :: CCode Name
encoreAllocName = Nam "encore_alloc"

partySequence :: CCode Name
partySequence = Nam "party_sequence"

partyReduce :: Bool -> CCode Name
partyReduce True = Nam "party_reduce_assoc"
partyReduce False = Nam "party_reduce_sequential"

partyJoin :: CCode Name
partyJoin = Nam "party_join"

partyExtract :: CCode Name
partyExtract = Nam "party_extract"

partyEach :: CCode Name
partyEach = Nam "party_each"

partyNewParP :: CCode Name
partyNewParP = Nam "new_par_p"

partyNewParV :: CCode Name
partyNewParV = Nam "new_par_v"

partyNewParF :: CCode Name
partyNewParF = Nam "new_par_f"

argName :: ID.Name -> CCode Name
argName name = Nam $ encoreName "arg" (show name)

fieldName :: ID.Name -> CCode Name
fieldName name =
    Nam $ encoreName "field" (show name)

qualifiedToString :: ID.QualifiedName -> String
qualifiedToString ID.QName{ID.qnsource = Nothing, ID.qnlocal} = show qnlocal
qualifiedToString ID.QName{ID.qnsource = Just s, ID.qnlocal} =
  sourceToString s ++ show qnlocal

sourceToString :: FilePath -> String
sourceToString = map translateSep . filter (/='.') . dropEnc
  where
    translateSep '/' = '_'
    translateSep '-' = '_'
    translateSep c = c
    dropEnc [] = []
    dropEnc ".enc" = []
    dropEnc (c:s) = c:dropEnc s

globalClosureName :: ID.QualifiedName -> CCode Name
globalClosureName funname =
    Nam $ encoreName "closure" (qualifiedToString funname)

functionClosureNameOf :: A.Function -> CCode Name
functionClosureNameOf f =
    globalClosureName $ ID.setSourceFile (A.funsource f) $
                        ID.topLevelQName (A.functionName f)

globalFunctionName :: ID.QualifiedName -> CCode Name
globalFunctionName funname =
    Nam $ encoreName "global_fun" (qualifiedToString funname)

localFunctionName :: ID.QualifiedName -> CCode Name
localFunctionName funname =
    Nam $ encoreName "local_fun" (qualifiedToString funname)

globalFunctionNameOf :: A.Function -> CCode Name
globalFunctionNameOf f@A.Function{A.funsource} =
  globalFunctionName $ ID.setSourceFile funsource $
                       ID.topLevelQName $ A.functionName f

localFunctionNameOf :: A.Function -> CCode Name
localFunctionNameOf f@A.Function{A.funsource} =
  localFunctionName $ ID.setSourceFile funsource $
                      ID.topLevelQName $ A.functionName f

functionWrapperNameOf :: A.Function -> CCode Name
functionWrapperNameOf f@A.Function{A.funsource} =
  Nam $ encoreName "fun_wrapper" $
      qualifiedToString $
      ID.setSourceFile funsource $
      ID.topLevelQName $ A.functionName f

functionAsValueWrapperNameOf :: A.Expr -> CCode Name
functionAsValueWrapperNameOf (A.FunctionAsValue {A.qname}) =
  Nam $ encoreName "fun_wrapper" (qualifiedToString qname)
functionAsValueWrapperNameOf e =
    error $ "CCodeNames.hs: Tried to get function wrapper from '" ++
            show e ++ "'"

closureStructName :: CCode Name
closureStructName = Nam "closure"

closureStructFFieldName :: CCode Name
closureStructFFieldName = Nam "call"

closureFunName :: String -> CCode Name
closureFunName name =
    Nam $ encoreName "closure_fun" name

closureEnvName :: String -> CCode Name
closureEnvName name =
    Nam $ encoreName "env" name

closureTraceName :: String -> CCode Name
closureTraceName name =
    Nam $ encoreName "trace" name

streamHandle :: CCode Lval
streamHandle = Var "_stream"

typeVarRefName :: Ty.Type -> CCode Name
typeVarRefName ty =
    Nam $ encoreName "type" (show ty)

classId :: Ty.Type -> CCode Name
classId ty =
    Nam $ encoreName "ID" (qualifyRefType ty)

refTypeId :: Ty.Type -> CCode Name
refTypeId ty =
    Nam $ encoreName "ID" (qualifyRefType ty)

traitMethodSelectorName = Nam "trait_method_selector"

-- | each class, in C, provides a dispatch function that dispatches
-- messages to the right method calls. This is the name of that
-- function.
classDispatchName :: Ty.Type -> CCode Name
classDispatchName clazz =
    Nam $ encoreName "dispatch" (qualifyRefType clazz)

classTraceFnName :: Ty.Type -> CCode Name
classTraceFnName clazz =
    Nam $ encoreName "trace" (qualifyRefType clazz)

runtimeTypeInitFnName :: Ty.Type -> CCode Name
runtimeTypeInitFnName clazz =
    Nam $ encoreName "type_init" (qualifyRefType clazz)

ponyAllocMsgName :: CCode Name
ponyAllocMsgName = Nam "pony_alloc_msg"

poolIndexName :: CCode Name
poolIndexName = Nam "POOL_INDEX"

futMsgTypeName :: Ty.Type -> ID.Name -> CCode Name
futMsgTypeName cls mname =
    Nam $ encoreName "fut_msg" (qualifyRefType cls ++ "_" ++ show mname ++ "_t")

oneWayMsgTypeName :: Ty.Type -> ID.Name -> CCode Name
oneWayMsgTypeName cls mname =
    Nam $ encoreName "oneway_msg" (qualifyRefType cls ++ "_" ++ show mname ++ "_t")

msgId :: Ty.Type -> ID.Name -> CCode Name
msgId ref mname =
    Nam $ encoreName "MSG" (qualifyRefType ref ++ "_" ++ show mname)

futMsgId :: Ty.Type -> ID.Name -> CCode Name
futMsgId ref mname =
    Nam $ encoreName "FUT_MSG" (qualifyRefType ref ++ "_" ++ show mname)

oneWayMsgId :: Ty.Type -> ID.Name -> CCode Name
oneWayMsgId cls mname =
    Nam $ encoreName "ONEWAY_MSG" (qualifyRefType cls ++ "_" ++ show mname)

typeNamePrefix :: Ty.Type -> String
typeNamePrefix ref
  | Ty.isTraitType ref = encoreName "trait" qname
  | Ty.isRefAtomType ref = if Ty.isModeless ref
                           then encoreName "passive" qname
                           else encoreName (showModeOf ref) qname
  | otherwise = error $ "type_name_prefix Type '" ++ show ref ++
                        "' isnt reference type!"
  where
    qname = qualifyRefType ref

ponySendvName :: CCode Name
ponySendvName = Nam "pony_sendv"

ponyGcSendName :: CCode Name
ponyGcSendName = Nam "pony_gc_send"

ponyGcRecvName :: CCode Name
ponyGcRecvName = Nam "pony_gc_recv"

ponyRecvDoneName :: CCode Name
ponyRecvDoneName = Nam "pony_recv_done"

ponySendDoneName :: CCode Name
ponySendDoneName = Nam "pony_send_done"

refTypeName :: Ty.Type -> CCode Name
refTypeName ref = Nam $ typeNamePrefix ref ++ "_t"

classTypeName :: Ty.Type -> CCode Name
classTypeName ref = Nam $ typeNamePrefix ref ++ "_t"

runtimeTypeName :: Ty.Type -> CCode Name
runtimeTypeName ref = Nam $ typeNamePrefix ref ++ "_type"

futureTraceFn :: CCode Name
futureTraceFn = Nam "future_trace"

futureFulfil :: CCode Name
futureFulfil = Nam "future_fulfil"

futureAwait :: CCode Name
futureAwait = Nam "future_await"

futureGetActor :: CCode Name
futureGetActor = Nam "future_get_actor"

futureChainActor :: CCode Name
futureChainActor = Nam "future_chain_actor"

actorSuspend :: CCode Name
actorSuspend = Nam "actor_suspend"

streamGet :: CCode Name
streamGet = Nam "stream_get"

streamPut :: CCode Name
streamPut = Nam "stream_put"

streamClose :: CCode Name
streamClose = Nam "stream_close"

streamGetNext :: CCode Name
streamGetNext = Nam "stream_get_next"

streamEos :: CCode Name
streamEos = Nam "stream_eos"

streamMkFn :: CCode Name
streamMkFn = Nam "stream_mk"

futureMkFn :: CCode Name
futureMkFn = Nam "future_mk"

rangeMkFn :: CCode Name
rangeMkFn = Nam "range_mk"

arrayMkFn :: CCode Name
arrayMkFn = Nam "array_mk"

tupleMkFn :: CCode Name
tupleMkFn = Nam "tuple_mk"

closureMkFn :: CCode Name
closureMkFn = Nam "closure_mk"

closureCallName :: CCode Name
closureCallName = Nam "closure_call"

optionMkFn :: CCode Name
optionMkFn = Nam "option_mk"

closureTraceFn :: CCode Name
closureTraceFn = Nam "closure_trace"

arrayTraceFn :: CCode Name
arrayTraceFn = Nam "array_trace"

tupleTraceFn :: CCode Name
tupleTraceFn = Nam "tuple_trace"

optionTraceFn :: CCode Name
optionTraceFn = Nam "option_trace"

rangeTraceFn :: CCode Name
rangeTraceFn = Nam "range_trace"

streamTraceFn :: CCode Name
streamTraceFn = Nam "stream_trace"

futureTypeRecName :: CCode Name
futureTypeRecName = Nam $ "future_type"

closureTypeRecName :: CCode Name
closureTypeRecName = Nam $ "closure_type"

arrayTypeRecName :: CCode Name
arrayTypeRecName = Nam $ "array_type"

rangeTypeRecName :: CCode Name
rangeTypeRecName = Nam $ "range_type"

partyTypeRecName :: CCode Name
partyTypeRecName = Nam $ "party_type"

encoreCtxName :: CCode Name
encoreCtxName = Nam "_ctx"

encoreCtxT :: CCode Ty
encoreCtxT = Typ "pony_ctx_t"

encoreCtxVar :: CCode Lval
encoreCtxVar = Var "_ctx"

encorePrimitive :: CCode Lval
encorePrimitive = Var "ENCORE_PRIMITIVE"

encoreActive :: CCode Lval
encoreActive = Var "ENCORE_ACTIVE"

encoreRuntimeType :: CCode Lval
encoreRuntimeType = Var "runtimeType"

nullName :: CCode Name
nullName = Nam "NULL"

nullVar :: CCode Lval
nullVar = Var "NULL"

arrayGet :: CCode Name
arrayGet = Nam "array_get"

arraySet :: CCode Name
arraySet = Nam "array_set"

arraySize :: CCode Name
arraySize = Nam "array_size"

tupleSet :: CCode Name
tupleSet = Nam "tuple_set"

tupleGet :: CCode Name
tupleGet = Nam "tuple_get"

tupleSetType :: CCode Name
tupleSetType = Nam "tuple_set_type"

rangeStart :: CCode Name
rangeStart = Nam "range_start"

rangeStop :: CCode Name
rangeStop = Nam "range_stop"

rangeStep :: CCode Name
rangeStep = Nam "range_step"

rangeAssertStep :: CCode Name
rangeAssertStep = Nam "range_assert_step"

optionTypeRecName :: CCode Name
optionTypeRecName = Nam "option_type"

tupleTypeRecName :: CCode Name
tupleTypeRecName = Nam "tuple_type"

stdout :: CCode Lval
stdout = Var "stdout"

stderr :: CCode Lval
stderr = Var "stderr"
