module Game

-- This module can be used to for playing the interactive Sudoku game.

import Data.List

import Project


-- function to run Sudoku intrective game (used for testing Task 5):
-- By default this function is using a fully empty table - t1:
runSudoku : IO ()
runSudoku = do
        putStrLn "Hello! This is a Sudoku game. Let's play!"
        let table = t1
        interactiveGame table

-- Test on:
-- :exec runSudoku

