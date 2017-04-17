module ModuleExpander(
                      ProgramTable
                     ,buildProgramTable
                     ,compressProgramTable
                     ,compressProgramTable'
                     ,dirAndName
                     ) where

import Identifiers
import Utils
import AST.AST
import Parser.Parser
import Literate
import Typechecker.Environment
import AST.Meta
import Types(setRefSourceFile, setRefNamespace, setRefNamePrefix)

import SystemUtils
import Control.Monad
import Control.Arrow((&&&))
import System.Directory(doesFileExist)
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
  let (sourceDir, sourceName) = dirAndName (source p)
  findAndImportModules importDirs preludePaths sourceDir sourceName Map.empty p

shortenPrelude :: [FilePath] -> FilePath -> FilePath
shortenPrelude preludePaths source =
    if any (`isPrefixOf` source) preludePaths
    then basename source
    else source

stdLib source = [lib "String", lib "Std"]
    where
      lib s = Import{imeta = meta $ initialPos source
                    ,itarget = explicitNamespace [Name s]
                    ,isource = Nothing
                    ,iqualified = False
                    ,ilibrary=True --NOTE:Should be True
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

  let withStdlib = if moduledecl == NoModule 
                   then addStdLib sourcePath moduledecl imports
                   else imports
  sources <- mapM (findSource importDirs sourceDir) withStdlib
  let imports'   = zipWith setImportSource sources withStdlib
      classes'   = map (setClassSource sourcePath) classes
      traits'    = map (setTraitSource sourcePath) traits
      typedefs'  = map (setTypedefSource sourcePath) typedefs
      functions' = map (setFunctionSource sourcePath) functions
      precompiled' = (moduleLibrary moduledecl)
      p' = p{source    = sourcePath
            ,precompiled = precompiled'
            ,imports   = imports'
            ,classes   = classes'
            ,traits    = traits'
            ,typedefs  = typedefs'
            ,functions = functions'
            }
      newTable = Map.insert sourcePath p' table
  foldM (importModule importDirs preludePaths) newTable sources
  where
    moduleNamespace = if moduledecl == NoModule
                      then emptyNamespace
                      else explicitNamespace [modname moduledecl]
    
    sourcePath = sourceDir </> sourceName
    namePrefix = if moduledecl == NoModule
                 then Name ""
                 else modname moduledecl

    setImportSource source i = i{isource = Just source}
    setClassSource source c@Class{cname} =
      c{cname = setRefNamespace moduleNamespace $
                setRefSourceFile source (setRefNamePrefix namePrefix cname)}
    setTraitSource source t@Trait{tname} =
      t{tname = setRefNamespace moduleNamespace $
                setRefSourceFile source (setRefNamePrefix namePrefix tname)}
    setTypedefSource source d@Typedef{typedefdef} =
      d{typedefdef = setRefNamespace moduleNamespace $
                     setRefSourceFile source (setRefNamePrefix namePrefix typedefdef)}
    setFunctionSource source f =
      f{funsource = source, funNamePrefix = namePrefix, funheader = (sethnamePrefix namePrefix (funheader f))}

buildModulePath :: Namespace -> Bool -> FilePath
buildModulePath (NSExplicit ns) ilibrary =
  let prefix = init ns
      suffix = last ns
      moduleDir = foldl (</>) "" $ map show prefix
      moduleName = show suffix <> (if ilibrary then ".emi" else ".enc")
  in if null moduleDir
     then moduleName
     else moduleDir </> moduleName

findSource :: [FilePath] -> FilePath -> ImportDecl -> IO FilePath
findSource importDirs sourceDir Import{itarget, ilibrary} = do
  let modulePath = buildModulePath itarget ilibrary
      sources = nub $
                sourceDir </> modulePath :
                map (</> modulePath) importDirs
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
  |  Map.member source table = return table
  | otherwise = do
      raw <- readFile source
      let code = if "#+literate\n" `isPrefixOf` raw
                 then getTangle raw
                 else raw
      ast <- case parseEncoreProgram source code of
               Right ast  -> return ast
               Left error -> abort $ parseErrorPretty error
      if moduledecl ast == NoModule
      then abort $ "No module in file " ++ source ++ ". Aborting!"
      else let (sourceDir, sourceName) = dirAndName source
           in findAndImportModules importDirs preludePaths
                                   sourceDir sourceName table ast

compressProgramTable' :: Program -> ProgramTable -> Program
compressProgramTable' source modules = foldl joinTwo source modules
  where
    joinTwo :: Program -> Program -> Program
    joinTwo p@Program{etl=etl,  functions=functions,  traits=traits,  classes=classes}
              Program{etl=etl', functions=functions', traits=traits', classes=classes'} =
                p{etl=etl ++ etl', functions=functions ++ functions',
                  traits=traits ++ traits', classes=classes ++ classes'}


compressProgramTable :: Program -> ProgramTable -> Program
compressProgramTable source table = 
  let libs = Map.filter (precompiled) table
      regular   = Map.filter (not . precompiled) table
      prog      = compressProgramTable' source regular
      (resolved, _) = resolveDeps libs prog Map.empty Map.empty
  in 
      addLibraries prog libs


addLibraries :: Program -> ProgramTable -> Program
addLibraries source libs = foldl joinTwo source libs
  where
    joinTwo :: Program -> Program -> Program
    joinTwo p@Program{traits=traits, libraries=libraries}
              p2@Program{traits=traits'} = p{libraries=libraries ++ [p2]}


resolveDeps :: ProgramTable -> Program -> ProgramTable -> ProgramTable -> (ProgramTable, ProgramTable)
resolveDeps table lib@Program{source, imports} resolved unresolved = do
    let imports' = filter ilibrary imports
        updUnresolved = Map.insert source lib unresolved
        (resolved', unresolved') = foldl (resolve table) (resolved, updUnresolved) imports'
    (resolved', unresolved') 


resolveDeps' :: ProgramTable -> Program -> ProgramTable -> ProgramTable -> (ProgramTable, ProgramTable)
resolveDeps' table lib@Program{source, imports} resolved unresolved = do
    let imports' = filter ilibrary imports
        updUnresolved = Map.insert source lib unresolved
        (resolved', unresolved') = foldl (resolve table) (resolved, updUnresolved) imports'
    let finalResolved = (Map.insert source lib resolved')
        finalUnResolved = (Map.delete source unresolved')
    (finalResolved, finalUnResolved) 
  --where
    --resolve :: (ProgramTable, ProgramTable) -> ImportDecl -> (ProgramTable, ProgramTable)

resolve :: ProgramTable -> (ProgramTable, ProgramTable) -> ImportDecl -> (ProgramTable, ProgramTable)
resolve table (resolved, unresolved) i@Import{isource}
  | Map.member (fromJust isource) resolved = (resolved, unresolved)
  | Map.notMember (fromJust isource) resolved && Map.member (fromJust isource) unresolved = 
        error $ " *** Circular dependency detected " <+> "***"
  | otherwise = let (resolved', unresolved') = do 
                      let key = fromJust isource
                          lib' = fromJust (Map.lookup key table)
                      resolveDeps' table lib' resolved unresolved
                      in ((Map.union resolved resolved'), (Map.union unresolved unresolved'))


  

  --lib@Program{source, imports} 