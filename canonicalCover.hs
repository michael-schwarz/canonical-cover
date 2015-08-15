-- "THE BEER-WARE LICENSE" (Revision 42):
-- Michael Schwarz <michael.schwarz93@gmail.com> wrote this file. As long as you
-- retain this notice you can do whatever you want with this stuff. If we meet
-- some day, and you think this stuff is worth it, you can buy me a beer in return.

import Data.List
import Data.List.Split

-- BEGIN DATA STRUCTURES --

--IMPORTANT: Attribute lists are assumed to be duplicate free

-- Attribute defintion
data Attribute = Attribute Char deriving (Show,Eq, Ord)

-- A MVD (or the more special case of an FD)
data MVD = FD [Attribute] [Attribute] | MVD [Attribute] [Attribute] deriving (Show,Eq)

-- A relation
data Relation = Relation [Attribute] [MVD]  deriving (Show,Eq)

--Remove old MVD (if elem), add new
replaceMvd :: Relation -> MVD -> MVD -> Relation
replaceMvd (Relation attrs mvds) old new = (Relation attrs newMvds)
  where newMvds = (delete old mvds)++[new]

--Find out if a prticular FD is also a MVD  
isFD :: MVD -> Bool
isFD (FD _ _) = True
isFD (MVD _ _) = False

-- END DATA STRUCTURES --

-- BEGIN COMPUTING CLOSURES --

-- Compute the closure (This is formulated as a fixpoint operation)
closure :: [Attribute] -> Relation -> [Attribute]
closure a r | sort (nub a) == sort nextRun = a
	    | otherwise = closure nextRun r
  where nextRun = closureRun a r --No need to nub here, already done by the resultFunction

-- Do the next run of the closure algorithm (used to find out if we have a fixpoint)
closureRun :: [Attribute] -> Relation -> [Attribute]
closureRun a (Relation _ []) = a
closureRun a (Relation as (mvd:mvds)) = closureRun (result a mvd) (Relation as mvds)

-- Get transitive attributes wrt to particular MVD (FD actually, MVDs are just handeled
-- here for the sake of simplicity)
result :: [Attribute] -> MVD -> [Attribute]
result x (MVD _ _) = x
result x (FD ls rs) | null (ls \\ x) = x `union` rs --If everything from ls is also in x we can merge
		    | otherwise = x

-- END COMPUTING CLOSURES --

-- BEGIN LEFT REDUTION --

leftReduce :: Relation -> Relation
leftReduce (Relation attrs mvds) = leftReduceFDs (Relation attrs mvds) mvds

-- Left reduce all given MVDs, the second argument is a list of mvds that are still to do
leftReduceFDs :: Relation -> [MVD] -> Relation
leftReduceFDs r [] = r
leftReduceFDs r ((MVD _ _):mvds) = leftReduceFDs r mvds
leftReduceFDs orgR ((orgFD@(FD ls rs)):mvds) = leftReduceFDs (replaceMvd orgR orgFD (remLOneMVD orgR orgFD ls)) mvds

--Removes all superfluos attributes on the left of one MVD
remLOneMVD :: Relation -> MVD -> [Attribute] -> MVD
remLOneMVD _ (MVD ls rs) _ = (MVD ls rs) -- MVDs need not be reduced
remLOneMVD r fd@(FD ls rs) [] = fd -- base case
remLOneMVD r fd@(FD ls rs) (todo:todos) | isSuperfluosOnLeft r fd todo = remLOneMVD r (FD (delete todo ls) rs) todos --If current attribute is superfluos, remove it and recurse
				     | otherwise = remLOneMVD r fd todos
				     
-- Checks if a given attribute is superfluos in a given FD
isSuperfluosOnLeft :: Relation -> MVD -> Attribute -> Bool
isSuperfluosOnLeft _ (MVD _ _) _ = False
isSuperfluosOnLeft (Relation as mvds) (FD ls rs) a = a `elem` (closure attrsWithoutA (Relation as mvds))
  where attrsWithoutA = delete a ls
-- END LEFT REDUCTION --

-- BEGIN RIGHT REDUTION --

rightReduce :: Relation -> Relation
rightReduce (Relation attrs mvds) = rightReduceFDs (Relation attrs mvds) mvds

-- right reduce all given MVDs, the second attribute is a list of mvds that are still to do
rightReduceFDs :: Relation -> [MVD] -> Relation
rightReduceFDs r [] = r
rightReduceFDs r ((MVD _ _):mvds) = rightReduceFDs r mvds
rightReduceFDs orgR ((orgFD@(FD ls rs)):mvds) =  rightReduceFDs (replaceMvd orgR orgFD (remROneMVD orgR orgFD rs)) mvds

--Removes all superfluos attributes on the right of one MVD
remROneMVD :: Relation -> MVD -> [Attribute] -> MVD
remROneMVD _ mvd@(MVD _ _) _ = mvd -- MVDs need not be reduced
remROneMVD r fd@(FD ls rs) [] = fd  -- base case
remROneMVD r@(Relation as mvds) fd@(FD ls rs) (todo:todos) | isSuperfluosOnRight r fd todo = remROneMVD newRel newFD todos --If current attribute is superfluos
                                                           | otherwise = remROneMVD r fd todos
    where newRel = replaceMvd r fd newFD
          newFD = (FD  ls (delete todo rs))
                    
-- Checks if a given attribute is superfluos in a given FD
isSuperfluosOnRight :: Relation -> MVD -> Attribute -> Bool
isSuperfluosOnRight _ (MVD _ _) _ = False
isSuperfluosOnRight (Relation as mvds) (FD ls rs) a = a `elem` closure ls (replaceMvd (Relation as mvds) (FD ls rs) (FD ls rsWithoutA))
  where rsWithoutA = delete a rs				     
-- END RIGHT REDUCTION --

-- BEGIN CANONICAL COVER --
canonicalCover :: Relation -> Relation
canonicalCover = mergeDuplicates.remEmptyFD.rightReduce.leftReduce

-- Remove FDs of the form X -> {}
remEmptyFD :: Relation -> Relation
remEmptyFD (Relation atts mvds) = (Relation atts (filter helper mvds))
  where helper (FD rs []) = False
	helper _ = True

-- Merge duplicate FDs of the form A->X A->Y into A -> X u Y
mergeDuplicates :: Relation -> Relation
mergeDuplicates (Relation as mvds) = (Relation as ((addAllToProperMVD (leftSides justFDs) justFDs)++justMVDs))
  where justFDs = filter isFD mvds
	justMVDs = filter (not.isFD) mvds

-- add all right sides of the given FDs to the proper FD in mvd (obtained e.g. from leftSides)
addAllToProperMVD :: [MVD] -> [MVD] ->[MVD]
addAllToProperMVD mvds (todo:todos) = addAllToProperMVD (addToProperMVD mvds todo) todos
addAllToProperMVD mvds [] = mvds

--add right side of a given FD to the correct FD in the list (e.g. obtained from leftSides)
addToProperMVD :: [MVD] -> MVD -> [MVD]	
addToProperMVD ((FD ls rs):mvds) (FD ls' rs') | sort ls == sort ls' = (FD ls (nub rs++rs')):mvds
					      | otherwise = (FD ls rs):(addToProperMVD mvds (FD ls' rs'))

--Create FDs of the form A -> {} for each individual A
leftSides :: [MVD] ->  [MVD]
leftSides mvds = map (\ls -> FD ls []) (nub $ map (\(FD ls rs) -> sort ls) mvds)
-- END CANONICAL COVER --

-- Returns whether a specific set of attributes is a superkey
isSuperKey :: [Attribute] -> Relation -> Bool
isSuperKey a rel@(Relation attrs mvds) = sort attrs == sort (closure a rel)

-- Helper
a :: Char -> Attribute
a c = Attribute c

printRel :: Relation -> [String]
printRel r = lines (prettyPrint r)

prettyPrint :: Relation -> String
prettyPrint (Relation ((Attribute a):as) mvds) = [a] ++ " " ++ prettyPrint (Relation as mvds)
prettyPrint (Relation [] (mvd:mvds)) = (prettyPrint' mvd) ++ prettyPrint (Relation [] mvds)
prettyPrint (Relation [] []) = ""

prettyPrint' :: MVD -> String
prettyPrint' (FD ls rs) = "\n"++concat (map (\ (Attribute x) -> [x]) ls) ++ "->" ++ concat (map (\ (Attribute x) -> [x]) rs)
prettyPrint' (MVD ls rs) = "\n"++concat (map (\ (Attribute x) -> [x]) ls) ++ "-->->" ++ concat (map (\ (Attribute x) -> [x]) rs)

-- Main loop

main = do
    putStrLn "------------------------------------------------------------------------------------------------"
    putStrLn "                             Compute canonical cover                                            "
    putStrLn "------------------------------------------------------------------------------------------------"
    putStrLn ""
    putStrLn "Please keep in mind that the canonical cover is not in general unique. So a different result you"
    putStrLn "got by hand can be equally correct."
    putStrLn ""  
    putStrLn "Please enter FDs in the form AB->CD where all attributes are single uppercase letters (e.g. A)" 
    putStrLn "and press enter after each FD."
    putStrLn "When you are done, press enter once more"
    fds <- readFDs []
    putStrLn ""
    putStrLn "Here are all attributes and all FDs:"
    mapM_ putStrLn (printRel (Relation (sort (getAllAttributes fds)) fds))
    putStrLn ""
    putStrLn ""
    putStrLn "Here are all attributes and the canonical cover over the FDs:"
    mapM_ putStrLn (printRel (canonicalCover (Relation (sort (getAllAttributes fds)) fds)))
    putStrLn ""
    putStrLn ""
    putStrLn "Press any key to close"
    getLine

getAllAttributes :: [MVD] -> [Attribute]
getAllAttributes mvds = res [] mvds
    where res xs ((FD ls rs):mvds) = (res xs mvds) `union` (ls `union` rs)
          res xs ((MVD ls rs):mvds) = (res xs mvds) `union` (ls `union` rs)
          res xs [] = xs
    
readFDs :: [MVD] -> IO [MVD]
readFDs mvds  = do
    input <- getLine
    if input == "" then return(mvds) else readFDs (mvds++[parseFD input])
 
parseFD :: String -> MVD
parseFD x | length splitted == 2 =  FD (map (\x ->  a x) (head splitted)) (map (\x ->  a x) (last splitted))
          | otherwise = error ("The input was malformed. "++x)
    where splitted = splitOn "->" x