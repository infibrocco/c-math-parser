#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include "mathparser.h"

int main(int argc, char *argv[]) {
    if (argc <= 1) return 400; // exit if no args
    
    // Define the input expression
    const char *input_const = argv[1];
    char *input = strdup(input_const);  // Create a non-const copy
    Tokenizer tokenizer = { .input = input, .pos = 0 };
    Parser parser = { .tokenizer = &tokenizer };

    advance(&parser);

    ASTNode *root = parse_expression(&parser);

    // Evaluate the expression
    EvalResult result = evaluate(root);

    // Print the result based on whether it's an integer or a double
    if (result.is_integer) {
        printf("Result: %d\n", result.value.int_value);
    } else {
        printf("Result: %f\n", result.value.double_value);
    }

    // Free the AST
    free_ast(root);
    free(input);  // Free the duplicated string

    return 0;
}
