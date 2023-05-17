module Project

import Data.String
import Data.List
import System.File
import Data.Nat



{-- Task 1 (Representation) --}

-- SudokuTable is defined as a separate data type that take list of list of natural numbers (numbers matrix) and return the new table:
public export
data SudokuTable : Type where
    CreateTable : List (List (Maybe Nat)) -> SudokuTable

-- Nothing : empty cell
-- Just n : filled cell



{-- Task 2 (Operations on tables) --}

-- 2.1

-- function that returns a number on particular position in the table:
-- Arguments: table, row, column
-- Return: number on the position
public export
index : SudokuTable -> Nat -> Nat -> Maybe Nat
index table i j = case table of
                    CreateTable [] => Nothing
                    CreateTable (x :: xs) => case i of  -- i analyses rows
                                                    Z => case x of -- first row - x
                                                              [] => Nothing
                                                              (y :: ys) => case j of  -- j analyses columns
                                                                                Z => y -- first element of the first row (i=0,j=0)
                                                                                (S k) => index (CreateTable ((ys ++ [Nothing]) :: xs)) Z k -- other elements of the first row
                                                    (S k) => index (CreateTable xs) k j -- other rows except the first

-- Test on: index t3 4 3
-- Answer should be: Just 8



-- 2.2

-- helper function that updates the row:
-- Arguments: table row (filled with Maybe Nats), column number (j), number to which update
-- Return: updated with new number list (that is our table's row)
updateRow : List (Maybe Nat) -> Nat -> Maybe Nat -> List (Maybe Nat)
updateRow ys j n = case ys of
                           [] => []
                           (x :: xs) => case j of
                                             Z => n :: xs
                                             (S k) => x :: updateRow xs k n


-- main function that updates the whole table:
-- Arguments: table, row, column, number to which update
-- Return: updated table
public export
update : SudokuTable -> Nat -> Nat -> Maybe Nat -> Maybe SudokuTable
update table i j n = case table of
                      CreateTable [] => Just table
                      CreateTable (x :: xs) => case i of  -- i analyses rows 
                                                    -- first row (x):
                                                    Z => case x of
                                                              [] => Nothing
                                                              (y :: ys) => case j of
                                                                                -- update the first element of the first row - y:
                                                                                Z => Just (CreateTable ((n :: ys) :: xs)) 
                                                                                -- update the first row without the first element - ys:
                                                                                (S k) => case update (CreateTable ((ys ++ [Nothing]) :: xs)) Z k n of
                                                                                              Nothing => Nothing
                                                                                              -- update only ys using the updateRow function:
                                                                                              Just (CreateTable z) => Just (CreateTable ((y :: updateRow ys k n) :: xs))
                                                    -- all other rows except for the first row - xs:
                                                    (S k) => case update (CreateTable xs) k j n of -- matrix without a first line
                                                                  Nothing => Nothing
                                                                  -- add the first row (x) to the updated table (y):
                                                                  Just (CreateTable new_xs) => Just (CreateTable (x :: new_xs))

-- Test on: update t2 3 1 (Just 9)
-- Answer should be: table with updated number (from Nothing to Just 9)



-- 2.3

-- helper function that counts the total number of cells:
totalCells : SudokuTable -> Nat
totalCells (CreateTable []) = Z
totalCells (CreateTable (x :: xs)) = length x + totalCells (CreateTable xs)

-- helper function that counts empty cells in a row:
nothingCells : List (Maybe Nat) -> Nat
nothingCells [] = Z
nothingCells (x :: xs) = case x of
                                Nothing => S (nothingCells xs)
                                (Just y) => nothingCells xs

-- helper function that count the total number of empty cells:
emptyCells : SudokuTable -> Nat
emptyCells s = case s of
                     CreateTable [] => Z
                     CreateTable (x :: xs) => case x of
                                                   [] => 9 + emptyCells (CreateTable xs) -- x is empty (9 * Nothing) & recurse to xs
                                                   ys => nothingCells ys + emptyCells (CreateTable xs) -- count empty cells in x & recurse to xs

-- helper function that translates the Nat to Double:
natToDouble : Nat -> Double
natToDouble Z = 0.0
natToDouble (S n) = 1.0 + natToDouble n


-- main function that defines the difficulty of the table:
difficulty : SudokuTable -> Double
difficulty t = let empty = natToDouble (emptyCells t)
                   totals = natToDouble (totalCells t)
               in empty / totals

-- Test on: difficulty t1
-- Answer should be: 1.0 (maximum value - it is 'difficult' to complete the fully empty table)



-- 2.4

-- Conditions:
-- [1, 2, 3, 4, 5, 6, 7, 8, 9]
-- unique
-- length
-- check row, column, 3x3 sub-grid


-- helper function to check if the row consists of exactly 1 - 9 and that values are unique:
numbersUnique : List (Maybe Nat) -> Bool
numbersUnique [] = True
numbersUnique (x :: xs) = case x of
                              Nothing => numbersUnique xs
                              Just n => elem (Just n) [Just 1, Just 2, Just 3, Just 4, Just 5, Just 6, Just 7, Just 8, Just 9] && not (elem (Just n) xs) && numbersUnique xs

-- helper function to check if the row has exactly 9 Maybe Nats:
checkLength : List (Maybe Nat) -> Bool
checkLength xs = if length xs == 9 then True else False

-- helper function to check if rows consist of valid unique numbers and length: 
rowsValidity : SudokuTable -> Bool
rowsValidity (CreateTable []) = True
rowsValidity (CreateTable (x :: xs)) = numbersUnique x && checkLength x && rowsValidity (CreateTable xs)

-- helper function to change rows to columns:
-- Data.List.transpose : List (List a) -> List (List a)
-- Transposes rows and columns of a list of lists.
transpose : SudokuTable -> SudokuTable
transpose (CreateTable rows) = CreateTable (transpose rows)

-- helper function to check if columns consist of valid unique numbers and length:
columnsValidity : SudokuTable -> Bool
columnsValidity (CreateTable []) = True
columnsValidity (CreateTable (x :: xs)) = numbersUnique x && checkLength x && columnsValidity (CreateTable xs)

-- helper function that extracts 3x3 sub-grid and put it into a list:
-- foldl : Foldable t => (acc -> elem -> acc) -> acc -> t elem -> acc
subgrid : SudokuTable -> Nat -> Nat -> List (Maybe Nat)
subgrid table i j = let rows = map (\row => map (\col => index table row col) [j, j + 1, j + 2]) [i, i + 1, i + 2] 
                        in foldl (\acc, row => acc ++ row) [] rows
-- Test on: subgrid t2 0 0

-- helper function that extracts all sub-grids:
subgrids : SudokuTable -> List (List (List (Maybe Nat)))
subgrids table = map (\i => map (\j => subgrid table i j) [0, 3, 6]) [0, 3, 6]

-- helper function to check the validity of sub-grids:
subgridValidity : List (List (List (Maybe Nat))) -> Bool
subgridValidity [] = True
subgridValidity (x :: xs) = case x of
                                 [] => True
                                 (y :: ys) => numbersUnique y && checkLength y && subgridValidity [ys]


-- main function that checks if the table is valid:
public export
isValid : SudokuTable -> Bool
isValid table = rowsValidity table && columnsValidity (transpose table) && subgridValidity (subgrids table)

-- Test on: isValid t4
-- Answer should be: False



-- 2.5

-- Conditions:
-- validity -> isValid
-- filled (Nothing -> False)

-- helper function that checks if the table is filled:
filled : SudokuTable -> Bool
filled table = case table of
                    CreateTable [] => True
                    CreateTable (x :: xs) => case x of
                                                  [] => filled (CreateTable xs)
                                                  (y :: ys) => case y of
                                                                    Nothing => False
                                                                    Just z => filled (CreateTable (ys :: xs))


-- main function that checks if the table is complete:
isComplete : SudokuTable -> Bool
isComplete table = isValid table && filled table

-- 1. Test on: isComplete t2
-- 1. Answer should be: False (table is not fully filled)

-- 2. Test on: isComplete t3
-- 2. Answer should be: True (table is filled and valid)

-- 3. Test on: isComplete t4
-- 3. Answer should be: False (table is not valid)




{-- Task 3 (Parser) --}

-- helper function that translates a string (file contents) to a list of list of chars:
-- lines str : String -> List (String)
-- unpack : List (String) -> List (List Char)
public export
charList : String -> List (List Char)
charList str = map unpack (lines str)


-- main function-parser that can read in a Sudoku table from a file:
parser : (path : String) -> IO (Either FileError (List (List Char)))
parser path = do 
            file <- openFile path Read         -- open a file in a read mode
            case file of
                 Left err => pure $ Left err
                 Right x => do
                          contents <- fRead x  -- collect a contents of a file
                          case contents of
                               Left err => pure $ Left err
                               Right y => pure $ Right $ (charList y)


-- helper function to output the contents of a file (with moving to a new line):
-- pack turns a list of characters into a string
-- pack : List Char -> String
parseTable : List (List Char) -> IO ()
parseTable [] = pure ()
parseTable (x :: xs) = do
                    putStrLn (pack x)
                    parseTable xs

-- helper function that runs a parser and outputs table from a file:
public export
parserRun : String -> IO ()
parserRun path = do
            output <- parser path
            case output of
                 Left err => print err
                 Right table => parseTable table

-- Test on:
-- :exec (parserRun "input.txt")
-- Answer should be: the same table as in "input.txt" file




{-- Task 4 (Pretty-printer) --}

horizontal : String
horizontal = "+-------+-------+-------+"

-- helper function that prints a single cell:
printCell : Maybe Nat -> String
printCell Nothing = " "
printCell (Just x) = show x

-- helper function that prints three cells:
printThreeCells : List (Maybe Nat) -> String
printThreeCells xs = concatMap (\x => printCell x ++ " ") (take 3 xs)

-- helper function that prints 3 cells with vertical boundaries and removes them:
printCellsAndDrop : List (Maybe Nat) -> String
printCellsAndDrop [] = ""
printCellsAndDrop xs = printThreeCells xs ++ "| " ++ printCellsAndDrop (drop 3 xs)

-- helper function that prints the whole row with vertical boundaries:
printRow : List (Maybe Nat) -> String
printRow xs = "| " ++ printCellsAndDrop xs

-- helper function that prints 3 rows with horizontal boundary at a time:
printThreeRows : List (List (Maybe Nat)) -> IO ()
printThreeRows xss =
  let rows = take 3 xss
      rowStrings = map printRow rows
      three = concat (intersperse "\n" rowStrings)
  in putStr three >> putStr "\n" >> putStr horizontal >> putStr "\n"

-- helper function that prints all rows as the correct table without upper sider boundary:
printRowsAndDrop : List (List (Maybe Nat)) -> IO ()
printRowsAndDrop [] = putStr ""
printRowsAndDrop xss = printThreeRows xss >> printRowsAndDrop (drop 3 xss)

-- These are just testers to check printRowsAndDrop:
-- :exec printRowsAndDrop l2
-- :exec printRowsAndDrop l3


-- main function that prints the whole table:
public export
prettyPrinter : SudokuTable -> IO ()
prettyPrinter (CreateTable table) = do
  putStr horizontal >> putStr "\n"
  printRowsAndDrop table

-- Test on:
-- :exec prettyPrinter t2
-- :exec prettyPrinter t3




{-- Task 5 (Interactive game) --}

-- helper function that translates string to nat:
stringToNat : String -> Maybe Nat
stringToNat str = case parsePositive str of
                    Just x => if x >= 0 then Just (fromInteger x) else Nothing
                    Nothing => Nothing

-- helper function that translates Maybe Nat to Nat:
maybeToNat: Maybe Nat -> Nat
maybeToNat Nothing = 0
maybeToNat (Just x) = x

-- helper function that translates Maybe SudokuTable to SudokuTable:
maybeToTable : Maybe SudokuTable -> SudokuTable
maybeToTable Nothing = CreateTable [[]]
maybeToTable (Just x) = x

-- main function that represents an interactive game:
public export
interactiveGame : SudokuTable -> IO ()
interactiveGame table = do 
                        prettyPrinter table
                        putStrLn "Enter (i, j) - coordinates:"
                        i' <- getLine
                        j' <- getLine
                        putStrLn ("Enter the number to fill the cell (" ++ i' ++ ", " ++ j' ++ "):")

                        n <- getLine
                        let num = stringToNat n
                        let i = maybeToNat (stringToNat i')
                        let j = maybeToNat (stringToNat j')

                        let updatedTable' = update table i j num
                        -- let updatedTable = maybeToTable updatedTable'

                        -- check if updated table is valid:
                        case updatedTable' of
                             Nothing => do
                                    putStrLn $ "Impossible to fill the cell (" ++ show i ++ ", " ++ show j ++ ") with " ++ show n ++ ". Enter another number:"
                                    interactiveGame table
                             (Just updatedTable) => do
                                    -- if table is valid then check also if it is filled:
                                    if isValid updatedTable then do
                                        if isComplete updatedTable then do
                                            putStrLn "Congratulations, the grid is now solved."
                                            prettyPrinter updatedTable
                                        -- if table if not filled fully yet, then let user enter values for the updated table
                                         else interactiveGame updatedTable
                                    -- if table is not valid then let user enter other values:
                                     else do
                                        putStrLn $ "Impossible to fill the cell (" ++ show i ++ ", " ++ show j ++ ") with " ++ show n ++ ". Enter another number:"
                                        interactiveGame table

-- Test on:
-- :exec interactiveGame t2
-- :exec interactiveGame t5

-- The fast way to solve t5:
-- Enter: 0 0 5
-- Enter: 6 3 5
-- Enter: 6 0 9
-- Enter: 3 5 1

-- Note: In file Game.idr you also can find a function runSudoku that can be used for testing. By defualt it takes an empty table for you to solve.




-- 3.1 Solver (Approach B: Backtracking in the List monad)


{-- Task 6 (Check for holes) --}

-- function that creates a list of all possibles coordinates (indices):
indices : List (Nat, Nat)
indices = [(i, j) | i <- [0, 1, 2, 3, 4, 5, 6, 7, 8], j <- [0, 1, 2, 3, 4, 5, 6, 7, 8]]


-- main function that finds the first (closest) empty cell (Nothing value):
findHole : SudokuTable -> Maybe (Nat, Nat)
-- filters indices such that left only those that do not have a value:
findHole table = case filter (\(i, j) => index table i j == Nothing) indices of
                      -- list contains only indices of the empty cells:
                       [] => Nothing
                       ((i, j) :: xs) => Just (i, j)  -- List (Nat, Nat)



{-- Task 7 (Solve the sudoku!) --}

options : List (Maybe Nat)
options = [Just 1, Just 2, Just 3, Just 4, Just 5, Just 6, Just 7, Just 8, Just 9]


-- main function that solves a table:
public export
solve : SudokuTable -> List SudokuTable
solve table = case findHole table of        -- check if table contains empty cells
                   Nothing => do case isValid table of   -- table is filled, then check its validity
                                      False => []
                                      True => pure table
                   -- try to get new solutions = updated tables filled with values from options:
                   Just (i, j) => let updatedTables = [maybeToTable (update table i j n) | n <- options]
                                      -- filter valid solutions:
                                      validTables = filter isValid updatedTables
                                  -- in case of valid solutions, apply solve to them to contine our 'Solving path':
                                  in concatMap solve validTables


-- Test on: solve t5

-- Note: before solving table you can print it using :exec prettyPrinter t5 to make sure that the table was initially not fully filled. 

-- Note: The file TestSolve.idr contains function that can be used for testing solver and pretty-printer functions.



-- Following tables can be used for testing purposes. They represent Sudoku tables in different states that can be useful for testing:

-- Empty table:
public export
t1 : SudokuTable
t1 = CreateTable (replicate 9 (replicate 9 Nothing))

-- Partially filled table:
t2 : SudokuTable
t2 = CreateTable [[Nothing, Nothing, Nothing, Nothing, Just 8, Just 5, Nothing, Just 3, Nothing],
                  [Nothing, Nothing, Just 9, Just 3, Nothing, Nothing, Nothing, Nothing, Nothing],
                  [Nothing, Just 2, Nothing, Just 1, Nothing, Nothing, Nothing, Nothing, Nothing],
                  [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 8, Just 5],
                  [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 7, Nothing, Nothing],
                  [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 1, Nothing],
                  [Just 8, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 2],
                  [Just 7, Nothing, Nothing, Nothing, Nothing, Nothing, Just 1, Nothing, Nothing],
                  [Nothing, Just 9, Nothing, Nothing, Nothing, Nothing, Just 4, Nothing, Nothing]]

-- Fully filled and valid table:
t3 : SudokuTable
t3 = CreateTable [[Just 1, Just 2, Just 3, Just 4, Just 5, Just 6, Just 7, Just 8, Just 9],
                  [Just 4, Just 5, Just 6, Just 7, Just 8, Just 9, Just 1, Just 2, Just 3],
                  [Just 7, Just 8, Just 9, Just 1, Just 2, Just 3, Just 4, Just 5, Just 6],
                  [Just 2, Just 1, Just 4, Just 3, Just 6, Just 5, Just 8, Just 9, Just 7],
                  [Just 3, Just 6, Just 5, Just 8, Just 9, Just 7, Just 2, Just 1, Just 4],
                  [Just 8, Just 9, Just 7, Just 2, Just 1, Just 4, Just 3, Just 6, Just 5],
                  [Just 5, Just 3, Just 1, Just 6, Just 4, Just 2, Just 9, Just 7, Just 8],
                  [Just 6, Just 4, Just 2, Just 9, Just 7, Just 8, Just 5, Just 3, Just 1],
                  [Just 9, Just 7, Just 8, Just 5, Just 3, Just 1, Just 6, Just 4, Just 2]]

-- Invalid table:
t4 : SudokuTable
t4 = CreateTable [[Just 1, Just 2, Just 3, Just 4, Just 5, Just 5, Just 7, Just 8, Just 9],
                  [Just 4, Just 4, Just 6, Just 7, Just 8, Just 9, Just 1, Just 2, Just 3],
                  [Just 4, Just 8, Just 9, Just 1, Just 2, Just 3, Just 4, Just 5, Just 6],
                  [Just 2, Just 7, Just 4, Just 3, Just 6, Just 5, Just 8, Just 9, Just 7],
                  [Just 3, Just 6, Just 5, Just 8, Just 9, Just 7, Just 2, Just 1, Just 4],
                  [Just 8, Just 9, Just 7, Just 2, Just 1, Just 4, Just 3, Just 6, Just 5],
                  [Just 5, Just 1, Just 1, Just 6, Just 4, Just 5, Just 8, Just 7, Just 8],
                  [Just 6, Just 4, Just 2, Just 9, Just 7, Just 8, Just 5, Just 3, Just 1],
                  [Just 9, Just 7, Just 8, Just 5, Just 3, Just 1, Just 6, Just 4, Just 9]]

-- Almost fully filled table (useful for solve function because it is really fast table to solve):
public export
t5 : SudokuTable
t5 = CreateTable [[Nothing, Just 3, Just 4, Just 6, Just 7, Just 8, Just 9, Just 1, Just 2], 
                  [Just 6, Just 7, Just 2, Just 1, Just 9, Just 5, Just 3, Just 4, Just 8], 
                  [Just 1, Just 9, Just 8, Just 3, Just 4, Just 2, Just 5, Just 6, Just 7], 
                  [Just 8, Just 5, Just 9, Just 7, Just 6, Nothing, Just 4, Just 2, Just 3], 
                  [Just 4, Just 2, Just 6, Just 8, Just 5, Just 3, Just 7, Just 9, Just 1], 
                  [Just 7, Just 1, Just 3, Just 9, Just 2, Just 4, Just 8, Just 5, Just 6], 
                  [Nothing, Just 6, Just 1, Nothing, Just 3, Just 7, Just 2, Just 8, Just 4], 
                  [Just 2, Just 8, Just 7, Just 4, Just 1, Just 9, Just 6, Just 3, Just 5], 
                  [Just 3, Just 4, Just 5, Just 2, Just 8, Just 6, Just 1, Just 7, Just 9]]

-- Another partially filled table:
t6 : SudokuTable
t6 = CreateTable [[Nothing, Just 2, Just 3, Just 4, Just 5, Just 6, Nothing, Just 8, Just 9],
                  [Just 4, Just 5, Nothing, Just 7, Just 8, Nothing, Just 1, Just 2, Just 3],
                  [Nothing, Nothing, Just 9, Just 1, Just 2, Nothing, Just 4, Just 5, Nothing],
                  [Just 2, Just 1, Just 4, Just 3, Nothing, Nothing, Just 8, Just 9, Just 7],
                  [Nothing, Just 6, Nothing, Just 8, Just 9, Just 7, Just 2, Just 1, Just 4],
                  [Just 8, Nothing, Nothing, Just 2, Just 1, Nothing, Nothing, Just 6, Just 5],
                  [Just 5, Just 3, Nothing, Just 6, Just 4, Just 2, Just 9, Just 7, Just 8],
                  [Nothing, Just 4, Nothing, Just 9, Nothing, Just 8, Just 5, Just 3, Just 1],
                  [Nothing, Nothing, Just 8, Just 5, Nothing, Just 1, Just 6, Just 4, Nothing]]



-- Following also can be used for testing purposes (exactly for testing printRowsAndDrop function from Task 4):

l : List (Maybe Nat)
l = [Nothing, Just 2, Nothing, Just 1, Nothing, Nothing, Nothing, Nothing, Nothing]

l2 : List (List (Maybe Nat))
l2 = [[Just 1, Just 2, Just 3, Just 4, Just 5, Just 5, Just 7, Just 8, Just 9],
      [Just 4, Just 4, Just 6, Just 7, Just 8, Just 9, Just 1, Just 2, Just 3],
      [Just 4, Just 8, Just 9, Just 1, Just 2, Just 3, Just 4, Just 5, Just 6],
      [Just 8, Just 5, Just 9, Just 7, Just 6, Just 1, Just 4, Just 2, Just 3], 
      [Just 4, Just 2, Just 6, Just 8, Just 5, Just 3, Just 7, Just 9, Just 1], 
      [Just 7, Just 1, Just 3, Just 9, Just 2, Just 4, Just 8, Just 5, Just 6],
      [Just 9, Just 6, Just 1, Just 5, Just 3, Just 7, Just 2, Just 8, Just 4], 
      [Just 2, Just 8, Just 7, Just 4, Just 1, Just 9, Just 6, Just 3, Just 5], 
      [Just 3, Just 4, Just 5, Just 2, Just 8, Just 6, Just 1, Just 7, Just 9]]

l3 : List (List (Maybe Nat))
l3 = [[Nothing, Nothing, Nothing, Nothing, Just 8, Just 5, Nothing, Just 3, Nothing],
      [Nothing, Nothing, Just 9, Just 3, Nothing, Nothing, Nothing, Nothing, Nothing],
      [Nothing, Just 2, Nothing, Just 1, Nothing, Nothing, Nothing, Nothing, Nothing],
      [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 8, Just 5],
      [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 7, Nothing, Nothing],
      [Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 1, Nothing],
      [Just 8, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Just 2],
      [Just 7, Nothing, Nothing, Nothing, Nothing, Nothing, Just 1, Nothing, Nothing],
      [Nothing, Just 9, Nothing, Nothing, Nothing, Nothing, Just 4, Nothing, Nothing]]


