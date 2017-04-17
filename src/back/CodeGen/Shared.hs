module CodeGen.Shared(generateShared) where

import Types
import CCode.Main
import CodeGen.CCodeNames
import CodeGen.Typeclasses
import CodeGen.Function
import CodeGen.ClassTable
import qualified AST.AST as A

import Data.Maybe
import Data.List

-- | Generates a file containing the shared (but not included) C
-- code of the translated program
generateShared :: A.Program -> ProgramTable -> CCode FIN
generateShared prog@(A.Program{A.source, A.moduledecl, A.classes, A.functions, A.imports}) table =
    Program $
    Concat $
      (LocalInclude localInclude) :

      embeddedCode ++

      -- [commentSection "Shared messages"] ++
      -- sharedMessages ++
      [commentSection "Global functions"] ++
      globalFunctions ++
      [mainFunction moduledecl]
    where

      localInclude = if A.moduledecl prog == A.NoModule
                     then nonLibHeaderName
                     else libHeaderName
      
      nonLibHeaderName = ("enc" ++ ((show . A.moduleName . A.moduledecl) prog) ++ ".h")
      libHeaderName = ("libenc" ++ ((show . A.moduleName . A.moduledecl) prog) ++ ".h")

      globalFunctions =
        [translate f table globalFunction | f <- functions] ++
        [globalFunctionWrapper f | f <- functions] ++
        [initFunctionClosure f | f <- functions]

      embeddedCode = embedded prog
        where
          embedded A.Program{A.source, A.etl} =
              [commentSection $ "Embedded Code from " ++ show source] ++
              map (Embed . A.etlbody) etl

      sharedMessages = [msgAllocDecl, msgFutResumeDecl, msgFutSuspendDecl, msgFutAwaitDecl, msgFutRunClosureDecl]
          where
            msgAllocDecl =
               AssignTL (Decl (ponyMsgT, Var "m_MSG_alloc"))
                        (Record [Int 0, Record ([] :: [CCode Expr])])
            msgFutResumeDecl =
               AssignTL (Decl (ponyMsgT, Var "m_resume_get"))
                        (Record [Int 1, Record [encorePrimitive]])
            msgFutSuspendDecl =
               AssignTL (Decl (ponyMsgT, Var "m_resume_suspend"))
                        (Record [Int 1, Record [encorePrimitive]])
            msgFutAwaitDecl =
               AssignTL (Decl (ponyMsgT, Var "m_resume_await"))
                        (Record [Int 2, Record [encorePrimitive, encorePrimitive]])
            msgFutRunClosureDecl =
               AssignTL (Decl (ponyMsgT, Var "m_run_closure"))
                        (Record [Int 3, Record [encorePrimitive, encorePrimitive, encorePrimitive]])

      mainFunction A.NoModule =
          Function (Typ "int") (Nam "main")
                   [(Typ "int", Var "argc"), (Ptr . Ptr $ char, Var "argv")]
                   $ Return encoreStart
          where
            encoreStart =
                case find isLocalMain classes of
                  Just mainClass ->
                      Call (Nam "encore_start")
                           [AsExpr $ Var "argc"
                           ,AsExpr $ Var "argv"
                           ,Amp (AsLval $ runtimeTypeName (A.cname mainClass))
                           ]
                  Nothing ->
                      let msg =
                            "This program has no Main class and will now exit"
                      in Call (Nam "puts") [String msg]
            isLocalMain c@A.Class{A.cname} = A.isMainClass c &&
                                             getRefSourceFile cname == source
      mainFunction A.Module{A.modname} = commentSection ("No main function needed for " ++ (show modname))

commentSection :: String -> CCode Toplevel
commentSection s = Embed $ (take (5 + length s) $ repeat '/') ++ "\n// " ++ s
