# Course Project: Sudoku

This is the course project on Functional Programming (ITI0212) at Tallinn University of Technology (TalTech). 
The project features a Sudoku game developed using the Idris2 language with a functional programming approach.

## Project Structure
1. Sudoku Representation: Defining data type for representing Sudoku tables
2. Operations on Tables: Implementing functions to manipulate and analyze Sudoku tables:
    
    2.1 Indexing: Accessing table elements

    2.2 Updating: Modifying table elements

    2.3 Difficulty: Calculating table difficulty

    2.4 Validity Check: Determining if a table follows Sudoku rules

    2.5 Completeness Check: Determining if a table is fully filled
3. Parser: Parsing Sudoku tables from external files
4. Pretty-printer: Printing Sudoku tables in a user-friendly format
5. Interactive game: Implementing an interactive Sudoku game with user inputs
6. Solver - Check for holes: Identifying empty cells in a Sudoku table
7. Solver - Solve the sudoku: Solving the Sudoku table using the backtracking in the List monad approach


## Packages
This project uses following packages:

- ```Data.String```

- ```Data.List```

- ```System.File```

- ```Data.Nat```



## Files
```Project.idr```: main Idris file that containes all project tasks step by step as in a Project Structure together with some testers for  functions.

```input.txt```: sample input text file that contains a partially filled Sudoku table.

```Game.idr```: sample Idris file that contains the main function for playing the interactive Sudoku game. The game follows the rules outlined in Theorem 5, allowing you to fill in the Sudoku table manually. 

```TestSolve.idr```: sample Idris file that is designed for testing the Sudoku pretty-printer and solver functions. The main functions in this file read the Sudoku table from the ```input.txt``` file, print the initial state of the Sudoku table to the terminal using the pretty-printer function and then apply the solver to this Sudoku table. 



## Usage

The following are some explanations and examples for testing and usage of the Sudoku game.

### Project.idr

```Project.idr``` containes various tables used for testing. ```t1 - t6```: Sudoku tables in different states (empty, partially filled, fully filled, valid and invalid) for testing various functions. In the testing examples provided, feel free to use any table of your choice, from t1 to t6.

Important: Make sure you have already installed Idris2 in your IDE before testing.

To get started, open the project directory in your IDE and launch your terminal. In the terminal move to the path where the project files are located and there enter the Idris2 REPL with:

```idris2 Project.idr```

Enter ```:q``` to exit Idris2 REPL.


```Project.idr``` file containes more examples suitable for testing in Idris2 REPL. Feel free to select any of them for your testing needs.

### Game.idr

File ```Game.idr``` contains a function for playing the interactive Sudoku game. You can test the function ```interactiveGame``` from ```Project.idr``` with a function ```runSudoku``` from ```Game.idr``` file. To do this, firstly enter the Idris2 REPL and then run the function for testing with following commands:

```idris2 Game.idr```

```:exec runSudoku```

Note that runSudoku launches an interactive Sudoku game using a fully empty table (```t1```).

### TestSolve.idr

File ```TestSolve.idr``` is designed for testing the Sudoku pretty-printer and solver functions. Before testing these functions, firstly enter the Idris2 REPL in your terminal. Next steps are to run pretty-printer function for data from ```input.txt``` file and apply solver function to this data. Everything mentioned above can be done with following commands, step by step: 

```idris2 TestSolve.idr```

```:exec prettyPrinter inputTableData```

```:exec solveInputTable```
