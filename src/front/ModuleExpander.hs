module ModuleExpander(
                      ProgramTable
                     ,buildProgramTable
                     ,compressProgramTable
                     ,dirAndName
                     ,shortenPrelude
                     ) where

import Identifiers
import Utils
import AST.AST
import Parser.Parser
import Literate
import Typechecker.Environment
import AST.Meta
import Types(setRefSourceFile, setRefNamespace)

import SystemUtils
import Control.Monad
import Control.Arrow((&&&))
import System.FilePath (replaceExtension, takeDirectory, dropExtension)
import System.Directory(doesFileExist, makeAbsolute, doesDirectoryExist)
import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import Data.List
import Text.Megaparsec(parseErrorPretty, initialPos)
import Debug.Trace
import Data.Maybe (fromJust)

type ProgramTable = Map FilePath Program

dirAndName = dirname' &&& basename
  where
    dirname' p =
        let dir = dirname p
        in if last dir == '/'
           then init dir
           else dir

buildProgramTable :: [FilePath] -> [FilePath] -> Program -> IO ProgramTable
buildProgramTable importDirs preludePaths p = do
  let (sourceDir, sourceName) = dirAndName (getProgramSource p)
  findAndImportModules importDirs preludePaths sourceDir sourceName Map.empty p

shortenPrelude :: [FilePath] -> FilePath -> FilePath
shortenPrelude preludePaths source =
    if any (`isPrefixOf` source) preludePaths
    then basename source
    else source

stdLib source = [lib "String", lib "Std"]
    where
      lib s = Import{imeta = meta $ newPos (initialPos source)
                    ,itarget = explicitNamespace [Name s]
                    ,isource = Nothing
                    ,iqualified = False
                    ,iselect = Nothing
                    ,ialias  = Nothing
                    ,ihiding = Nothing
                    }

addStdLib :: FilePath -> ModuleDecl -> [ImportDecl] -> [ImportDecl]
addStdLib source NoModule imports = stdLib source ++ imports
addStdLib source Module{modname} imports =
  filter ((/= explicitNamespace [modname]) . itarget) (stdLib source) ++ imports


findAndImportModules :: [FilePath] -> [FilePath] -> FilePath -> FilePath ->
                        ProgramTable -> Program -> IO ProgramTable
findAndImportModules importDirs preludePaths sourceDir sourceName
                     table p@Program{moduledecl
                                    ,imports
                                    ,classes
                                    ,traits
                                    ,typedefs
                                    ,functions} = do


  let std = any (`isPrefixOf` sourceDir) preludePaths
      withStdlib = if not std
                   then addStdLib sourcePath moduledecl imports
                   else imports
  

  sources <- mapM (findSource importDirs sourceDir) withStdlib

  let source = if std 
               then Prelude{shortPath=shortSource, absolutePath=sourcePath}
               else Regular shortSource
      imports'   = zipWith setImportSource sources withStdlib
      classes'   = map (setClassSource shortSource) classes
      traits'    = map (setTraitSource shortSource) traits
      typedefs'  = map (setTypedefSource shortSource) typedefs
      functions' = map (setFunctionSource shortSource) functions
      p' = p{source
            ,imports   = imports'
            ,classes   = classes'
            ,traits    = traits'
            ,typedefs  = typedefs'
            ,functions = functions'
            }
      newTable = Map.insert shortSource p' table
  foldM (importModule importDirs preludePaths) newTable sources
  where
    moduleNamespace = if moduledecl == NoModule
                      then emptyNamespace
                      else explicitNamespace [modname moduledecl]
    
    sourcePath = sourceDir </> sourceName
    shortSource = shortenPrelude preludePaths sourcePath
    
    setImportSource source i =
         let shortPath = shortenPrelude preludePaths source
         in i{isource = Just shortPath}
    setClassSource source c@Class{cname} =
      c{cname = setRefNamespace moduleNamespace $
                setRefSourceFile source cname}
    setTraitSource source t@Trait{tname} =
      t{tname = setRefNamespace moduleNamespace $
                setRefSourceFile source tname}
    setTypedefSource source d@Typedef{typedefdef} =
      d{typedefdef = setRefNamespace moduleNamespace $
                     setRefSourceFile source typedefdef}
    setFunctionSource source f =
      f{funsource = source}

buildModulePath :: Namespace -> FilePath
buildModulePath (NSExplicit ns)  =
  let prefix = init ns
      suffix = last ns
      moduleDir = foldl (</>) "" $ map show prefix
      moduleName = show suffix <> ".enc"
  in if null moduleDir
     then moduleName
     else moduleDir </> moduleName

findSource :: [FilePath] -> FilePath -> ImportDecl -> IO FilePath
findSource importDirs sourceDir Import{itarget} = do
  let modulePath = buildModulePath itarget
      imports = map (</> modulePath) importDirs
      sourceModulePath = sourceDir </> modulePath
  expandedSourceModulePath <- makeAbsolute $ sourceModulePath
  let sources = if expandedSourceModulePath `elem` imports then
                -- if directory of target is in imports, remove it to avoid ambiguous import error
                  nub $ imports
                else
                  nub $ sourceModulePath : imports
  candidates <- filterM doesFileExist sources
  case candidates of
    [] -> abort $ "Module " ++ show itarget ++
                  " cannot be found in imports. Directories searched:\n" ++
                  unlines (map (("  " ++) . dirname) sources) ++
                  "\nUse '-I PATH' to add additional import paths"
    [src] -> return src
    l -> do
      putStrLn $ "Module " ++ show itarget ++
                 " found in multiple places:"
      mapM_ (putStrLn . ("  " ++)) l
      abort "Unable to determine which one to use."

importModule :: [FilePath] -> [FilePath] -> ProgramTable -> FilePath
                -> IO ProgramTable
importModule importDirs preludePaths table source
  | shortSource <- shortenPrelude preludePaths source
  , Map.member shortSource table = return table
  | otherwise = do
      raw <- readFile source
      let code = if "#+literate\n" `isPrefixOf` raw
                 then getTangle raw
                 else raw
      ast <- case parseEncoreProgram source code of
               Right ast  -> return ast
               Left error -> abort $ parseErrorPretty error
      let libName = "libenc" ++ ((show . modname . moduledecl) ast) ++ ".a"
          libFolder = (dropExtension source) ++ "_lib"
          libPath = libFolder </> libName
      libExists <- doesDirectoryExist libFolder

      if moduledecl ast == NoModule
      then abort $ "No module in file " ++ source ++ ". Aborting!"
      else let (sourceDir, sourceName) = dirAndName source
               ast' = if libExists then ast{precompiled=True} else ast
           in findAndImportModules importDirs preludePaths
                                   sourceDir sourceName table ast'

combinePrograms :: Program -> ProgramTable -> Program
combinePrograms = foldl joinTwo
  where
    joinTwo :: Program -> Program -> Program
    joinTwo p@Program{etl=etl,  functions=functions,  traits=traits,  classes=classes}
              Program{etl=etl', functions=functions', traits=traits', classes=classes'} =
                p{etl=etl ++ etl', functions=functions ++ functions',
                  traits=traits ++ traits', classes=classes ++ classes'}

assignLibraries libs prog = 
    let 
        importedLibs = imports prog
        importSources = map (fromJust . isource) importedLibs
        libraries = map (\s -> fromJust (Map.lookup s libs)) importSources
    in
        prog{libraries}

compressProgramTable :: Program -> ProgramTable -> Program
compressProgramTable mainProg table = 
  let regular   = Map.filter (not . precompiled) table
      prog      = combinePrograms mainProg regular
      resolved = resolveLinkOrder table prog Map.empty Map.empty
      finalResolved = map (assignLibraries table) resolved
  in 
      prog{libraries=finalResolved}

--Resolve linking order and detect circular dependencies.
resolveLinkOrder :: ProgramTable -> Program -> ProgramTable -> ProgramTable -> [Program]
resolveLinkOrder libs _ _ _ | null libs = []
resolveLinkOrder table lib@Program{source, imports} resolvedMap unresolvedMap = do
    let table' = if (moduledecl lib) == NoModule 
                 then table  
                 else Map.insert (getSource source) lib table
    let (resolved, _, _) = foldl (resolve table') ([], resolvedMap, unresolvedMap) imports
    resolved


-- Dependency resolver, main function.
--1. Add module to unresolved set.
--2. Resolve module dependencies recursively.
--3. Add module to resolved set, remove from unresolved.
--4. If module is a pre-compiled module, add to link list.
resolveDeps :: ProgramTable -> Program -> [Program] -> ProgramTable -> ProgramTable -> ([Program], ProgramTable, ProgramTable)
resolveDeps table lib@Program{source, imports} resolved resolvedMap unresolvedMap = do
    let updUnresolved = Map.insert (getSource source) lib unresolvedMap
        (resolved', resolvedMap', unresolvedMap') = foldl (resolve table) (resolved, resolvedMap, updUnresolved) imports
    let finalResolvedMap = (Map.insert (getSource source) lib resolvedMap')
        finalUnresolvedMap = (Map.delete (getSource source) unresolvedMap')
        finalResolved = if precompiled lib then lib:resolved' else resolved'
    (finalResolved, finalResolvedMap, finalUnresolvedMap) 

--Cases when walking dependency graph.
--Case 1: Module dependency already resolved, return.
--Case 2: Module is member of unresolved but not resolved, has been seen before. 
--        Circular dependency detected. If compiled module, raise error, otherwise return
--Case 3: Module not seen before. Resolve dependencies recursively for module.
resolve :: ProgramTable -> ([Program], ProgramTable, ProgramTable) -> ImportDecl -> ([Program], ProgramTable, ProgramTable)
resolve table (resolved, resolvedMap, unresolvedMap) i@Import{isource}
  | Map.member (fromJust isource) resolvedMap = (resolved, resolvedMap, unresolvedMap)
  | Map.notMember (fromJust isource) resolvedMap && Map.member (fromJust isource) unresolvedMap = do
        let key = fromJust isource
            lib =  fromJust (Map.lookup key table)
        if not $ precompiled lib 
        then (resolved, resolvedMap, unresolvedMap) 
        else error $ " *** Circular dependency detected in" <+> (show $ source lib) <+> "***"
  | otherwise = let (resolved', resolvedMap', unresolvedMap') = do 
                      let key = fromJust isource
                          lib' = fromJust (Map.lookup key table)
                      resolveDeps table lib' resolved resolvedMap unresolvedMap
                      in (resolved', resolvedMap', unresolvedMap')


sourceToString :: FilePath -> String
sourceToString = map translateSep . filter (/='.') . dropEnc
  where
    translateSep '/' = '_'
    translateSep '-' = '_'
    translateSep c = c
    dropEnc [] = []
    dropEnc ".enc" = []
    dropEnc (c:s) = c:dropEnc s