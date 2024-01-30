#include <stdio.h> /* needed for input, output, ... */
#include <stdlib.h> /* needed for EXIT_SUCCESS, ... */
#include <math.h> /* nedded for myFloor() and myCeil() */
#include <glpk.h> /* the linear programming toolkit */

#define EPSILON 0.00001 /* small value to deal with rounding issues */

/* global variables -- YOU SHOULD NOT CHANGE THESE! */
/* (You are allowed to add your own if you want.) */
int size; /* number of rows/columns in the input */
double *input; /* array that contains the input */
double *solution; /* array that contains the solution */
int debug; /* flag for debug mode; 1 means debug mode, 0 means debug off */

/* prototypes of functions -- YOU SHOULD NOT CHANGE THESE! */
/* (Feel free to add your own as you like.) */
int readInput(char *filename); /* reads graph from file */
/* readInput creates/fills the data structures (global variables) as needed */
/* it returns 0 if all is okay and 1 otherwise */
int computeSolution(void); /* computes the solution, stores it in input */
/* the return value is 1 if a solution exists, 0 otherwise */
void checkSolution(void); /* checks if a solution is valid */
double myFloor(double x); /* slightly 'hacky' myFloor function */
double myCeil(double x); /* slightly 'hacky' myCeil function */
void printMatrix(char *title, double *matrix); /* print a matrix */

/**
 * @paragraph Creates a bound for a variable and sets it to be an integer.
 *
 * @param problem - pointer to glp problem.
 * @param var_index - the index of the variable in the glp problem variable container.
 * @param lower_bound - the lower bound value of the variable.
 * @param upper_bound - the upper bound value of the variable.
 */
void createVarBound(glp_prob * problem, int var_index, int lower_bound, int upper_bound)
{
    glp_set_col_kind(problem, var_index, GLP_IV);

    glp_set_col_bnds(
            problem,
            var_index,
            (lower_bound == upper_bound) ? GLP_FX : GLP_DB,
            lower_bound,
            upper_bound
    );
}

/**
 * @paragraph Creates all bounds for the sum variables.
 *
 * @param problem - pointer to glp problem.
 * @param INPUT_LENGTH - the length of the input i.e. the number of normal variables.
 * @param INCREMENT - equal to size + 1 (glpk starts from 1)
 */
void createSumVarBounds(glp_prob * problem, const int INPUT_LENGTH, const int INCREMENT)
{
    double sum_col; //will be equal to the sum of a column.
    double sum_row; //sum of row

    for (int col = 0; col < size; col++)
    {
        sum_col = 0.0; sum_row = 0.0;

        for (int row = 0; row < size; row++ )
        {
            sum_col += input[col + row * size];
            sum_row += input[row + col * size];
        }

        //sum of column variable bounding.
        createVarBound(
                problem,
                INPUT_LENGTH+1+col,
                (int) myFloor(sum_col),
                (int) myCeil(sum_col)
        );

        //sum of row variable bounding.
        createVarBound(
                problem,
                INPUT_LENGTH + INCREMENT + col,
                (int) myFloor(sum_row),
                (int) myCeil(sum_row)
        );
    }
}

/**
 * @paragraph Creates all bounds for the normal variables.
 *
 * @param problem - pointer to glp problem.
 * @param INPUT_LENGTH - the length of the input i.e. the number of normal variables.
 */
void createNormalVarBounds(glp_prob * problem, const int INPUT_LENGTH)
{
    for (int input_index = 0; input_index < INPUT_LENGTH; input_index++)
    {
        createVarBound(
                problem,
                input_index+1,
                (int) myFloor(input[input_index]),
                (int) myCeil(input[input_index])
        );
    }
}

/**
 * @paragraph Creates all bounds for the all variables (normal and sum)
 *
 * @param problem - pointer to glp problem.
 * @param INPUT_LENGTH - the length of the input i.e. the number of normal variables.
 * @param INCREMENT - equal to size + 1 (glpk starts from 1)
 */
void createAllVarBounds(glp_prob * problem, const int INPUT_LENGTH, const int INCREMENT)
{
    //How the glpk variables are set up is like {normal variables, column sum variables, row sum variables}

    //variable type | start index                         | end index
    //       normal | 1                                   | INPUT_LENGTH
    //      col sum | INPUT_LENGTH + 1                    | INPUT_LENGTH + size
    //      row sum | INPUT_LENGTH + INCREMENT (size + 1) | NUM_OF_VARS

    //--Normal variable bounds--\\

    createNormalVarBounds(problem, INPUT_LENGTH);

    //--Sum value variable bounds--\\

    createSumVarBounds(problem, INPUT_LENGTH, INCREMENT);

}

/**
 * @paragraph Creates all constraints
 *
 * @param problem - pointer to glp problem.
 * @param INPUT_LENGTH - the length of the input i.e. the number of normal variables.
 * @param INCREMENT - equal to size + 1 (glpk starts from 1)
 * @param COEFFICIENT_SIZE - the number of coefficients and variables in the constraints.
 */
void createAllConstraints(glp_prob * problem, const int INPUT_LENGTH, const int INCREMENT, const int COEFFICIENT_SIZE)
{
    //Conditions
    //  sum var = x_1 + x_2 + ... + x_n
    //  0 = -(sum var) + x_1 + x_2 + ... + x_n
    //  So condition # = sum val #

    //--Setting up coefficients--\\

    double coefficients[COEFFICIENT_SIZE]; //Equal to {0, -1, 1, ... , 1} where -1 * sum var, 1*normal vars.

    coefficients[1] = -1; //glpk doesn't look at index of 0.

    for (int coeff_index = 2; coeff_index < COEFFICIENT_SIZE; coeff_index++)
    {
        coefficients[coeff_index] = 1;
    }

    //--Setting up variables--\\

    int col_vars[COEFFICIENT_SIZE]; // To be {0, sum-var, x_1, x_2, ... , x_size}
    int row_vars[COEFFICIENT_SIZE];

    for (int col = 0; col < size; col++)
    {
        //How the glpk variables are set up is like {normal variables, column sum variables, row sum variables}
        //variable type | start index                         | end index
        //       normal | 1                                   | INPUT_LENGTH
        //      col sum | INPUT_LENGTH + 1                    | INPUT_LENGTH + size
        //      row sum | INPUT_LENGTH + INCREMENT (size + 1) | NUM_OF_VARS

        col_vars[1] = INPUT_LENGTH + 1 + col; //sum value variable location in variables (problem columns)
        row_vars[1] = INPUT_LENGTH + INCREMENT + col;

        for (int row = 0; row < size; row++ )
        {
            col_vars[row+2] = col + row * size + 1; //normal variable location, each of which = input array location + 1 (glpk starts at 1 but c starts at 0)
            row_vars[row+2] = row + col * size + 1;
        }

        //setting column sum condition
        glp_set_row_bnds(problem, col+1, GLP_FX, 0.0, 0.0); // = 0.0
        glp_set_mat_row(problem, col+1, INCREMENT, col_vars, coefficients);

        //setting row sum condition
        glp_set_row_bnds(problem, col+INCREMENT, GLP_FX, 0.0, 0.0); // = 0.0
        glp_set_mat_row(problem, col+INCREMENT, INCREMENT, row_vars, coefficients);
    }
}

/* This is the function that actually solves the problem. */
/* It is essentially empty and not functional. */
/* Your own implementation needs to go in here. */
int computeSolution(void)
{
//    printMatrix("Input", input);

     //-------------------------\\
    //--CONSTANT INITIALISATION--\\

    const int INPUT_LENGTH = size*size;
    const int NUM_OF_SUM_VALUES = size*2;
    const int NUM_OF_VARS = INPUT_LENGTH + NUM_OF_SUM_VALUES;
    const int INCREMENT = size+1;
    const int COEFFICIENT_SIZE = size+2; //number of coefficients/variables in the constraint

     //------------------------\\
    //--PROBLEM INITIALISATION--\\

    glp_prob * lp = glp_create_prob();

     //----------------------------------\\
    //--COLUMN (VARIABLE) INITIALISATION--\\

    glp_add_cols(lp, NUM_OF_VARS); //adds the variables, number of variables = normal var # + sum value #  = size^2 + size * 2

    createAllVarBounds(lp, INPUT_LENGTH, INCREMENT);

     //--------------------------\\
    //--CONDITION INITIALISATION--\\

    glp_add_rows(lp, NUM_OF_SUM_VALUES);

    createAllConstraints(lp, INPUT_LENGTH, INCREMENT, COEFFICIENT_SIZE);

     //----------\\
    //--SOLVING--\\

    int ret = glp_simplex(lp, NULL);

     //------------\\
    //--POST SOLVE--\\

    //Assign solution.
    if (ret == 0)
    {
        for (int sol_index = 0; sol_index < INPUT_LENGTH; sol_index++)
        {
            solution[sol_index] = glp_get_col_prim(lp, sol_index+1);
        }
    }

//    printMatrix("Solution",solution);

    //Free memory
    glp_delete_prob(lp);

    return (ret==0)?1:0;
    // 1 = true (solution)
    // 0 = false (no solution)
    // I would return ret but if ret == 0, does not check solution in main.
    //If I could change function signature, would change to enum representing bool.
}

/* YOU SHOULD NOT CHANGE ANYTHING BELOW THIS LINE! */

int main(int argc, char **argv) {
    int arg; /* used to run over the command line parameters */

    if ( argc<2 ) { /* no command line parameter given */
        fprintf(stderr, "Usage: %s [file1] [file2] [file3] [...]\n"
                "Where each [file] indicates the name of a file with an input.\n",
                argv[0]);
        exit(EXIT_FAILURE);
    }

    if ( argv[1][0]=='-' && argv[1][1]=='d' && argv[1][2]==0 ) {
        /* If the first parameter is -d we activate debug mode. */
        debug=1; /* switch debug mode on */
        fprintf(stdout, "DEBUG: Debug mode activated\n"); /* tell us */
    } else {
        debug=0; /* switch debug mode off */
    }

    for ( arg=1+debug; arg<argc; arg++ ) { /* go over remaining parameters */
        if ( readInput(argv[arg]) ) { /* try to read file */
            /* readInput returned with error message */
            fprintf(stderr, "%s: Cannot read input with filename %s. Skipping.\n",
                    argv[0], argv[arg]);
        } else
        {
            if ( computeSolution() )
            {
                fprintf(stdout, "%s: Input %s has a solution.\n",
                        argv[0], argv[arg]);
                checkSolution();
                printMatrix("Input", input);
                printMatrix("Solution", solution);
            } else {
                fprintf(stdout, "%s: Input %s does not have a solution.\n",
                        argv[0], argv[arg]);
            }
            /* free memory for next input */
            free(input);
            free(solution);
        }
    }
    return EXIT_SUCCESS;

//    readInput("C:\\Users\\TateMoore\\CLionProjects\\tam41-cs31920-assignment\\tests\\test1.txt");
//    computeSolution();
//    return EXIT_SUCCESS;
}

/* The following function prints a matrix including the row and column sums */
void printMatrix(char *title, double *matrix) {
  int	i, j; /* looping over rows and columns */
  double sum; /* to compute the sum */

  fprintf(stdout, "%s:\n", title);
  /* print the matrix and compute the row sums on the fly */
  for ( i=0; i<size; i++ ) {
    for ( j=0, sum=0.0; j<size; j++ ) {
      sum += matrix[i*size+j];
      fprintf(stdout,"%8.2f ", matrix[i*size+j]);
    }
  fprintf(stdout, "(row sum: %8.2f)\n", sum);
  }
  /* print separating line */
  for ( j=0; j<size; j++ ) {
    fprintf(stdout, "---------");
  }
  fprintf(stdout,"\n");
  /* now compute the column sums and print them */
  for ( j=0; j<size; j++ ) { /* we consistently use j for columns */
    for ( i=0, sum=0.0; i<size; i++ ) {
      sum += matrix[i*size+j];
    }
    fprintf(stdout,"%8.2f ", sum);
  }
  fprintf(stdout,"(column sums)\n");
}

/* The following function checks of a solution is valid. */
void checkSolution(void) {
    int	i, j; /* to run over the arrays */
    double sum1, sum2; /* to compute the sums over the rows and columns */

  /* check rows and that all numbers are integers and rounded */
    for ( i=0; i<size; i++ ) {
      for ( j=0, sum1=sum2=0.0; j<size; j++ ) {
        sum1 += input[i*size+j];
        sum2 += solution[i*size+j];
        if ( myFloor(solution[i*size+j]) != solution[i*size+j] ) {
          fprintf(stdout, "Error: %lf is not an integer (%d/%d).\n",
          solution[i*size+j], i, j);
          return;
        }
        if ( (myFloor(input[i*size+j])!=solution[i*size+j]) &&
            (myCeil(input[i*size+j])!=solution[i*size+j]) ) {
          fprintf(stdout, "Error: %lf is not rounded from %lf (%d/%d).\n",
          solution[i*size+j], input[i*size+j], i, j);
          return;
        }
      }
      if ( (myFloor(sum1)!=sum2) && (myCeil(sum1)!=sum2) ) {
        fprintf(stdout, "Error: Row sum for row %d not valid.\n", i);
        return;
      }
    }
    /* check columns*/
    for ( j=0; j<size; j++ ) {
      for ( i=0, sum1=sum2=0.0; i<size; i++ ) {
        sum1 += input[i*size+j];
        sum2 += solution[i*size+j];
      }
      if ( (myFloor(sum1)!=sum2) && (myCeil(sum1)!=sum2) ) {
        fprintf(stdout, "Error: Row sum for row %d not valid.\n", i);
        return;
      }
    }
}

int readInput(char *filename)
{
    FILE *fh; /* file handle to read input */
    int i, j; /* variables to run over array */
    double value; /* value read from input file */

    /* try to open the file for reading */
    if ( ( fh = fopen(filename, "rt") ) == NULL )
    {
        if ( debug )
        {
            fprintf(
                    stdout,
                    "DEBUG: Unable to open file %s for reading.\n",
                    filename
            );
        }
        return 1; /* unable to open file, flag failure */
    }

    /* read the first integer, the number of columns/rows */
    if ( fscanf(fh, "%d", &size)!= 1)
    {
        if ( debug )
        {
            fprintf(stdout, "DEBUG: Unable to read input size.\n");
        }

        fclose(fh); /* close file to avoid ununsed open files */

        return 1; /* flag failure */
    }

    if ( size<2 )
    {
        if ( debug )
        {
            fprintf(stdout, "DEBUG: Received %d as input size.\n", size);
        }

        fclose(fh); /* close file to avoid unused open files */

        return 1; /* flag failure */
    }

    /* allocate the memory for the input */
    if ( ( input = (double *)malloc(sizeof(double)*size*size) ) == NULL )
    {
        if ( debug )
        {
            fprintf(
                    stdout,
                    "DEBUG: Unable to allocate %ld bytes.\n",
                    sizeof(int)*size*size
            );
        }

        fclose(fh); /* close file to avoid unused open files */

        return 1; /* flag failure */
    }
  /* allocate the memory for the solution */
    if ( ( solution = (double *)malloc(sizeof(double)*size*size) ) == NULL )
    {
        if ( debug )
        {
            fprintf(
                    stdout,
                    "DEBUG: Unable to allocate %ld bytes.\n",
                    sizeof(int)*size*size
            );
        }

        fclose(fh); /* close file to avoid unused open files */

        return 1; /* flag failure */
    }

    /* read the actual values */
    for ( i=0; i<size; i++ )
    {
        for ( j=0; j<size; j++ )
        {
            /* attempt to read next value */
            if ( fscanf(fh, "%lf", &value)!= 1)
            {
                if ( debug )
                {
                    fprintf(
                            stdout,
                            "DEBUG: Unable to read input value (%d/%d).\n",
                            i, j
                    );
                }

                /* free memory and close file */
                free(input);
                free(solution);
                fclose(fh);

                return 1; /* flag failure */
            }
            input[i*size+j]=value;
        }
    }

  if ( debug )
  {
      fprintf(stdout,"Read the following input with size %d x %d\n", size, size);
      for ( i=0; i<size; i++ )
      {
          for ( j=0; j<size; j++ )
          {
            fprintf(stdout,"%5.2f ", input[i*size+j]);
          }

          fprintf(stdout,"\n");
      }
  }

  return 0; /* all okay */
}

double myFloor(double x)
{
  return floor(x+EPSILON);
}

double myCeil(double x) {
  return ceil(x-EPSILON);
}
