module TestSolve

-- This module can be used for testing the Sudoku solver function.

import System.File

import Project


toMaybeNat : Char -> Maybe Nat
toMaybeNat '0' = Nothing
toMaybeNat '1' = Just 1
toMaybeNat '2' = Just 2
toMaybeNat '3' = Just 3
toMaybeNat '4' = Just 4
toMaybeNat '5' = Just 5
toMaybeNat '6' = Just 6
toMaybeNat '7' = Just 7
toMaybeNat '8' = Just 8
toMaybeNat '9' = Just 9
toMaybeNat _ = Nothing

-- helper function that translates a string (file contents) to a table:
-- charList str : String -> List (List Char)
-- toMaybeNat : List (List Char) -> List (List (Maybe Nat))
parseTable : String -> SudokuTable
parseTable str = CreateTable (map (map toMaybeNat) (charList str))


-- helper function that opens a file with a path and reads a contents from it:
-- This function returns a SudokuTable, because SudokuTable is an input type for pretty-printer function.
-- unsafePerformIO : IO a -> a
readInputToSudokuTable : (path : String) -> SudokuTable
readInputToSudokuTable path = 
                          let
                          contents : Either FileError SudokuTable
                          contents = unsafePerformIO $ do
                                input <-  readFile path
                                case input of
                                     Left err => pure $ Left err
                                     Right x => pure $ Right $ parseTable x
                          in case contents of
                                  Left err => CreateTable [[]]
                                  Right x => x

-- Save data from "input.txt" file:
inputTableData : SudokuTable
inputTableData = readInputToSudokuTable "input.txt"

-- prettyPrinter : SudokuTable -> IO ()


-- To print table from "input.txt" using pretty-printer run following: 
-- :exec prettyPrinter inputTableData



-- helper function that solves and outputs the table from "input.txt":
-- solve : SudokuTable -> List SudokuTable
solveInputTable : IO ()
solveInputTable = do 
              let result = solve inputTableData
              case result of
                   [] => putStrLn "There is no solution for this Sudoku table"
                   (x :: _) => prettyPrinter x   -- Capture the first solution (Note that for this table there is only one solution)


-- Apply solver function to a table from "input.txt":
-- :exec solveInputTable

