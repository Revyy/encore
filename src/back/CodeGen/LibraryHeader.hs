module CodeGen.LibraryHeader(generateLibraryHeader) where

import Control.Arrow ((&&&))
import Data.List (partition)

import CodeGen.Typeclasses
import CodeGen.CCodeNames
import CodeGen.Function
import CodeGen.Type ()

import CCode.Main
import CCode.PrettyCCode ()

import qualified AST.AST as A
import qualified Identifiers as ID
import qualified Types as Ty
import Data.Char (toUpper)

-- | Generates the C header file for the translated program
-- | This function generates all the common code, generateHeaderRecurser generates class specific code
generateLibraryHeader :: A.Program -> CCode FIN

generateLibraryHeader p =
    Program $
    IfNDefine headerDef $
    Concat $
    HashDefine headerDef :
    HashDefine "_XOPEN_SOURCE 800" :
    (Includes [
      "pool.h",
      "array.h",
      "range.h",
      "option.h",
      "stdio.h",
      "stdarg.h",
      "dtrace_encore.h"
     ]) :
    HashDefine "UNIT ((void*) -1)" :

    [commentSection "Shared messages"] ++
    sharedMessages ++

    [commentSection "Embedded code"] ++
    map Embed embedded ++
    --map Embed (concatMap A.allEmbedded libs) ++

    [commentSection "Class type decls"] ++
    classTypeDecls classes ++

    --[commentSection "Trait type decls"] ++
    --traitTypeDecls traits ++

    [commentSection "Passive class types"] ++
    passiveTypes classes ++

    [commentSection "Runtime types"] ++
    runtimeTypeDecls classes traits ++

    [commentSection "Message IDs"] ++
    if null classes
    then [commentSection "No classes"]
    else [messageEnums classes] ++
    --map messageEnums (filter (not . null) libClassList) ++

    [commentSection "Message types"] ++
    ponyMsgTTypedefs classes ++
    ponyMsgTImpls classes ++

    [commentSection "Global functions"] ++
    globalFunctions functions ++

    [commentSection "Class IDs"] ++
    [classEnums classes] ++
    --map classEnums (filter emptyClassList libClassList) ++

    [commentSection "Trace functions"] ++
    traceFnDecls classes ++

    [commentSection "Runtime type init functions"] ++
    runtimeTypeFnDecls classes ++

    [commentSection "Methods"] ++
    concatMap methodFwds classes ++
    concatMap wrapperMethods classes ++

    [commentSection "Constructors"] ++
    concatMap constructors classes ++

    [commentSection "Main actor rtti"] ++
    [externMainRtti] -- ++

    --[commentSection "Trait types"] ++
    --traitTypes traits
   where
     externMainRtti = DeclTL (Typ "extern pony_type_t", Var "_enc__active_Main_type")

     sharedMessages =
          [DeclTL (ponyMsgT, Var "m_MSG_alloc"),
           DeclTL (ponyMsgT, Var "m_resume_get"),
           DeclTL (ponyMsgT, Var "m_resume_suspend"),
           DeclTL (ponyMsgT, Var "m_resume_await"),
           DeclTL (ponyMsgT, Var "m_run_closure")
          ]

     traits = A.traits p
     classes = A.classes p
     functions = A.functions p
     embedded = A.allEmbedded p

     libs = A.libraries p
     libHeaders = map (\p -> "libenc" ++ ((show . A.moduleName . A.moduledecl) p) ++ ".h") libs
     headerDef = "ENCORE_LIB_" ++ ((map toUpper . show . A.moduleName . A.moduledecl) p) ++ "_H" 
     --libClassList = map A.classes $ libs
     --libClasses = concatMap A.classes libs
     --libFunctions = concatMap A.functions libs

     --allClasses = classes ++ libClasses
     --allFunctions = functions ++ libFunctions


     emptyClassList :: [A.ClassDecl] -> Bool
     emptyClassList classes = (not $ null classes)

     ponyMsgTTypedefs :: [A.ClassDecl] -> [CCode Toplevel]
     ponyMsgTTypedefs classes = map ponyMsgTTypedefClass classes
            where
                ponyMsgTTypedefClass A.Class{A.cname, A.cmethods} =
                    Concat $ concatMap ponyMsgTTypedef cmethods
                    where
                        ponyMsgTTypedef mdecl =
                            [Typedef (Struct $ futMsgTypeName cname (A.methodName mdecl)) (futMsgTypeName cname (A.methodName mdecl)),
                             Typedef (Struct $ oneWayMsgTypeName cname (A.methodName mdecl)) (oneWayMsgTypeName cname (A.methodName mdecl))]

     ponyMsgTImpls :: [A.ClassDecl] -> [CCode Toplevel]
     ponyMsgTImpls classes = map ponyMsgTImplsClass classes
              where
                ponyMsgTImplsClass A.Class{A.cname, A.cmethods} =
                    Concat $ map ponyMsgTImpl cmethods
                    where
                      ponyMsgTImpl :: A.MethodDecl -> CCode Toplevel
                      ponyMsgTImpl mdecl =
                          let argrttys = map (translate . A.getType) (A.methodParams mdecl)
                              argspecs = zip argrttys (argnamesWComments mdecl):: [CVarSpec]
                              argspecsWithTypeParams = argspecs ++ argMethodTypeParamsSpecs mdecl
                              encoreMsgTSpec = (encMsgT, Var "")
                              encoreMsgTSpecOneway = (encOnewayMsgT, Var "msg")
                          in Concat
                            [StructDecl (AsType $ futMsgTypeName cname (A.methodName mdecl))
                                        (encoreMsgTSpec :
                                         argspecsWithTypeParams)
                            ,StructDecl (AsType $ oneWayMsgTypeName cname (A.methodName mdecl))
                                        (encoreMsgTSpecOneway :
                                         argspecsWithTypeParams)]
                      argnamesWComments mdecl =
                          zipWith (\n name -> (Annotated (show name) (Var ("f"++show n))))
                                  ([1..]:: [Int])
                                  (map A.pname $ A.methodParams mdecl)
                      argMethodTypeParamsSpecs mdecl =
                          zip (argMethodTypeParamsTypes mdecl)
                              (argMethodTypeParamsWComments mdecl)
                      argMethodTypeParamsTypes mdecl =
                          let l = length (A.methodTypeParams mdecl)
                          in replicate l (Ptr ponyTypeT)
                      argMethodTypeParamsWComments mdecl =
                          map (\name -> (Annotated (show name) (Var (show name))))
                            $ map typeVarRefName (A.methodTypeParams mdecl)

     globalFunctions functions =
       [globalFunctionDecl f | f <- functions] ++
       [functionWrapperDecl f | f <- functions] ++
       [globalFunctionClosureDecl f | f <- functions]

     messageEnums classes =
                let
                    meta = concatMap (\cdecl -> zip (repeat $ A.cname cdecl) (map A.methodName (A.cmethods cdecl))) classes
                    methodMsgNames = map (show . (uncurry futMsgId)) meta
                    oneWayMsgNames = map (show . (uncurry oneWayMsgId)) meta
                    allNames = methodMsgNames ++ oneWayMsgNames
                    safeTail xs
                      | null xs   = []
                      | otherwise = tail xs
                in
                    Enum $ (Nam  $ (head allNames) ++ "= 1024") : map Nam (safeTail allNames)
      
     classEnums classes =
       let
        classIds = map (refTypeId . A.getType) classes
       in
        Enum classIds

     traceFnDecls classes = map traceFnDecl classes
         where
           traceFnDecl A.Class{A.cname} =
               FunctionDecl void (classTraceFnName cname) [Ptr encoreCtxT,Ptr void]

     runtimeTypeFnDecls classes = map runtimeTypeFnDecl classes
         where
           runtimeTypeFnDecl A.Class{A.cname} =
               FunctionDecl void (runtimeTypeInitFnName cname) [Ptr . AsType $ classTypeName cname, Embed "..."]

     classTypeDecls classes = map classTypeDecl classes
                 where
                   classTypeDecl A.Class{A.cname} =
                       Typedef (Struct $ classTypeName cname) (classTypeName cname)

     passiveTypes classes = map passiveType $ filter (A.isPassive) classes
                 where
                   passiveType A.Class{A.cname, A.cfields} =
                       let typeParams = Ty.getTypeParameters cname in
                       StructDecl (AsType $ classTypeName cname)
                                  ((Ptr ponyTypeT, AsLval $ selfTypeField) :
                                   map (\ty -> (Ptr ponyTypeT, AsLval $ typeVarRefName ty)) typeParams ++
                                   zip
                                   (map (translate . A.ftype) cfields)
                                   (map (AsLval . fieldName . A.fname) cfields))

     traitTypeDecls traits = map traitTypeDecl traits
       where
         traitTypeDecl A.Trait{A.tname} =
           let ty = refTypeName tname in Typedef (Struct $ ty) ty

     traitTypes traits = map traitType traits
       where
         traitType A.Trait{A.tname} =
           let
             formal = Ty.getTypeParameters tname
             self = (Ptr ponyTypeT, AsLval $ selfTypeField)
           in
             StructDecl (AsType $ refTypeName tname) [self]

     runtimeTypeDecls classes traits = map typeDecl classes -- ++ map typeDecl traits
       where
         typeDecl ref =
           let
             ty = A.getType ref
             runtimeTy = runtimeTypeName ty
           in
             DeclTL (Extern ponyTypeT, AsLval runtimeTy)

     encoreRuntimeTypeParam = Ptr (Ptr ponyTypeT)
     methodFwds cdecl@(A.Class{A.cname, A.cmethods}) = map methodFwd cmethods
         where
           methodFwd m
               | A.isStreamMethod m =
                   let params = (Ptr (Ptr encoreCtxT)) :
                                (Ptr . AsType $ classTypeName cname) :
                                encoreRuntimeTypeParam : stream :
                                map (translate . A.ptype) mparams
                   in
                     FunctionDecl void (methodImplName cname mname) params
               | otherwise =
                   let params = if A.isMainClass cdecl && mname == ID.Name "main"
                                then [Ptr . AsType $ classTypeName cname,
                                      encoreRuntimeTypeParam, array]
                                else (Ptr . AsType $ classTypeName cname) :
                                     encoreRuntimeTypeParam :
                                     map (translate . A.ptype) mparams
                   in
                     FunctionDecl (translate mtype) (methodImplName cname mname)
                                  (Ptr (Ptr encoreCtxT):params)
               where
                 mname = A.methodName m
                 mparams = A.methodParams m
                 mtype = A.methodType m

     wrapperMethods A.Class{A.cname, A.cmethods} =
       if Ty.isPassiveRefType cname then
         []
       else
         map (genericMethod callMethodFutureName future) nonStreamMethods ++
         map (genericMethod methodImplOneWayName void) nonStreamMethods ++
         map (genericMethod methodImplStreamName stream) streamMethods ++
         map forwardingMethod nonStreamMethods
       where
         genericMethod genMethodName retType m =
           let
             thisType = Ptr . AsType $ classTypeName cname
             rest = map (translate . A.ptype) (A.methodParams m)
             args = Ptr (Ptr encoreCtxT) : thisType : encoreRuntimeTypeParam : rest
             f = genMethodName cname (A.methodName m)
           in
             FunctionDecl retType f args
         forwardingMethod m =
           let
             thisType = Ptr . AsType $ classTypeName cname
             rest = map (translate . A.ptype) (A.methodParams m)
             args = Ptr (Ptr encoreCtxT) : thisType : encoreRuntimeTypeParam :
                    rest ++ [future]
             f = methodImplForwardName cname (A.methodName m)
           in
             FunctionDecl future f args

         (streamMethods, nonStreamMethods) =
           partition A.isStreamMethod cmethods

     constructors A.Class{A.cname} = [ctr]
       where
         ctr =
           let
             retType = Ptr. AsType $ classTypeName cname
             f = constructorImplName cname
           in
             FunctionDecl retType f []

commentSection :: String -> CCode Toplevel
commentSection s = Embed $ replicate (5 + length s) '/' ++ "\n// " ++ s
