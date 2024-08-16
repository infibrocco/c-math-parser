#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <math.h>

/* Token types
 * This enum defines all possible types of tokens that can be recognized by the parser.
 * It includes numerical and identifier tokens, as well as various operators and symbols.
 */
typedef enum {
    TOKEN_NUMBER,
    TOKEN_IDENTIFIER,
    TOKEN_PLUS,
    TOKEN_MINUS,
    TOKEN_MULTIPLY,
    TOKEN_DIVIDE,
    TOKEN_MODULUS,
    TOKEN_POWER,
    TOKEN_INT_DIVIDE,
    TOKEN_BITWISE_AND,
    TOKEN_BITWISE_OR,
    TOKEN_BITWISE_XOR,
    TOKEN_LEFT_SHIFT,
    TOKEN_RIGHT_SHIFT,
    TOKEN_LESS_THAN,
    TOKEN_LESS_EQUAL,
    TOKEN_GREATER_THAN,
    TOKEN_GREATER_EQUAL,
    TOKEN_EQUAL,
    TOKEN_NOT_EQUAL,
    TOKEN_LPAREN,
    TOKEN_RPAREN,
    TOKEN_COMMA,
    TOKEN_EOF
} TokenType;

/* Token structure
 * Represents a single token in the input string.
 * It contains the type of the token and its string value (if applicable).
 */
typedef struct {
    TokenType type;
    char *value;
} Token;

/* Tokenizer structure
 * Keeps track of the current position in the input string during tokenization.
 */
typedef struct {
    const char *input;
    int pos;
} Tokenizer;

/* Parser structure
 * Contains the tokenizer and the current token being processed.
 */
typedef struct {
    Tokenizer *tokenizer;
    Token current_token;
} Parser;

/* AST node types
 * Defines the types of nodes that can appear in the Abstract Syntax Tree (AST).
 */
typedef enum {
    NODE_NUMBER,
    NODE_BINARY_OP,
    NODE_UNARY_OP,
    NODE_FUNCTION_CALL
} NodeType;

/* AST node structure
 * Represents a node in the Abstract Syntax Tree.
 * It can be a number, a binary operation, a unary operation, or a function call.
 */
typedef struct ASTNode {
    NodeType type;
    union {
        double number;
        struct {
            struct ASTNode *left;
            struct ASTNode *right;
            TokenType op;
        } binary_op;
        struct {
            struct ASTNode *operand;
            TokenType op;
        } unary_op;
        struct {
            char *name;
            struct ASTNode **args;
            int arg_count;
        } function_call;
    } data;
} ASTNode;

/* This union allows us to store either an integer or a double value.
 * The is_integer flag indicates which type is currently stored.
 */
typedef struct {
    union {
        int int_value;
        double double_value;
    } value;
    bool is_integer;
} EvalResult;

// Function prototypes
void advance(Parser *parser);
ASTNode *parse_expression(Parser *parser);
ASTNode *parse_term(Parser *parser);
ASTNode *parse_factor(Parser *parser);
ASTNode *parse_power(Parser *parser);
ASTNode *parse_bitwise(Parser *parser);
ASTNode *parse_comparison(Parser *parser);
ASTNode *parse_function_call(Parser *parser);
EvalResult evaluate(ASTNode *node);
void free_ast(ASTNode *node);

/* Tokenizer function
 * This function reads the input string and returns the next token.
 * It handles numbers, identifiers, and various operators.
 */
Token get_next_token(Tokenizer *tokenizer) {
    // Skip any whitespace
    while (isspace(tokenizer->input[tokenizer->pos])) {
        tokenizer->pos++;
    }

    // Check for end of input
    if (tokenizer->input[tokenizer->pos] == '\0') {
        return (Token){TOKEN_EOF, NULL};
    }

    // Handle numbers (integers and floats)
    if (isdigit(tokenizer->input[tokenizer->pos]) || tokenizer->input[tokenizer->pos] == '.') {
        char *start = (char *)&tokenizer->input[tokenizer->pos];
        char *end;
        strtod(start, &end);  // Convert string to double
        int length = end - start;
        char *value = malloc(length + 1);
        strncpy(value, start, length);
        value[length] = '\0';
        tokenizer->pos += length;
        return (Token){TOKEN_NUMBER, value};
    }

    // Handle identifiers (variable names, function names)
    if (isalpha(tokenizer->input[tokenizer->pos])) {
        int start = tokenizer->pos;
        while (isalnum(tokenizer->input[tokenizer->pos])) {
            tokenizer->pos++;
        }
        int length = tokenizer->pos - start;
        char *value = malloc(length + 1);
        strncpy(value, &tokenizer->input[start], length);
        value[length] = '\0';
        return (Token){TOKEN_IDENTIFIER, value};
    }

    // Handle operators and other symbols
    char c = tokenizer->input[tokenizer->pos++];
    switch (c) {
        case '+': return (Token){TOKEN_PLUS, NULL};
        case '-': return (Token){TOKEN_MINUS, NULL};
        case '*':
            if (tokenizer->input[tokenizer->pos] == '*') {
                tokenizer->pos++;
                return (Token){TOKEN_POWER, NULL};
            }
            return (Token){TOKEN_MULTIPLY, NULL};
        case '/':
            if (tokenizer->input[tokenizer->pos] == '/') {
                tokenizer->pos++;
                return (Token){TOKEN_INT_DIVIDE, NULL};
            }
            return (Token){TOKEN_DIVIDE, NULL};
        case '%': return (Token){TOKEN_MODULUS, NULL};
        case '&': return (Token){TOKEN_BITWISE_AND, NULL};
        case '|': return (Token){TOKEN_BITWISE_OR, NULL};
        case '^': return (Token){TOKEN_BITWISE_XOR, NULL};
        case '<':
            if (tokenizer->input[tokenizer->pos] == '<') {
                tokenizer->pos++;
                return (Token){TOKEN_LEFT_SHIFT, NULL};
            }
            if (tokenizer->input[tokenizer->pos] == '=') {
                tokenizer->pos++;
                return (Token){TOKEN_LESS_EQUAL, NULL};
            }
            return (Token){TOKEN_LESS_THAN, NULL};
        case '>':
            if (tokenizer->input[tokenizer->pos] == '>') {
                tokenizer->pos++;
                return (Token){TOKEN_RIGHT_SHIFT, NULL};
            }
            if (tokenizer->input[tokenizer->pos] == '=') {
                tokenizer->pos++;
                return (Token){TOKEN_GREATER_EQUAL, NULL};
            }
            return (Token){TOKEN_GREATER_THAN, NULL};
        case '=':
            if (tokenizer->input[tokenizer->pos] == '=') {
                tokenizer->pos++;
                return (Token){TOKEN_EQUAL, NULL};
            }
            // TODO: Handle single '=' as an error or assignment depending on needs
            break;
        case '!':
            if (tokenizer->input[tokenizer->pos] == '=') {
                tokenizer->pos++;
                return (Token){TOKEN_NOT_EQUAL, NULL};
            }
            // TODO: Handle single '!' as an error or logical NOT depending on needs
            break;
        case '(': return (Token){TOKEN_LPAREN, NULL};
        case ')': return (Token){TOKEN_RPAREN, NULL};
        case ',': return (Token){TOKEN_COMMA, NULL};
    }

    // Handle unexpected characters
    char *unexpected = malloc(2);
    unexpected[0] = c;
    unexpected[1] = '\0';
    return (Token){TOKEN_EOF, unexpected};  // Using TOKEN_EOF to indicate an error
}

/* Advance function
 * Moves to the next token in the input string.
 */
void advance(Parser *parser) {
    parser->current_token = get_next_token(parser->tokenizer);
}

/* Create number node
 * Creates an AST node for a number.
 */
ASTNode *create_number_node(double value) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = NODE_NUMBER;
    node->data.number = value;
    return node;
}

/* Create binary operation node
 * Creates an AST node for a binary operation (e.g., addition, multiplication).
 */
ASTNode *create_binary_op_node(ASTNode *left, ASTNode *right, TokenType op) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = NODE_BINARY_OP;
    node->data.binary_op.left = left;
    node->data.binary_op.right = right;
    node->data.binary_op.op = op;
    return node;
}

/* Create unary operation node
 * Creates an AST node for a unary operation (e.g., negation).
 */
ASTNode *create_unary_op_node(ASTNode *operand, TokenType op) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = NODE_UNARY_OP;
    node->data.unary_op.operand = operand;
    node->data.unary_op.op = op;
    return node;
}

/* Create function call node
 * Creates an AST node for a function call.
 */
ASTNode *create_function_call_node(char *name, ASTNode **args, int arg_count) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = NODE_FUNCTION_CALL;
    node->data.function_call.name = strdup(name);
    node->data.function_call.args = args;
    node->data.function_call.arg_count = arg_count;
    return node;
}

/* Parse expression
 * Parses an expression, which can be a series of terms connected by + or -.
 */
ASTNode *parse_expression(Parser *parser) {
    ASTNode *node = parse_comparison(parser);

    while (parser->current_token.type == TOKEN_PLUS || parser->current_token.type == TOKEN_MINUS) {
        TokenType op = parser->current_token.type;
        advance(parser);
        ASTNode *right = parse_comparison(parser);
        node = create_binary_op_node(node, right, op);
    }

    return node;
}

/* Parse comparison
 * Parses comparison operations (<, <=, >, >=, ==, !=).
 */
ASTNode *parse_comparison(Parser *parser) {
    ASTNode *node = parse_bitwise(parser);

    while (parser->current_token.type == TOKEN_LESS_THAN || parser->current_token.type == TOKEN_LESS_EQUAL ||
           parser->current_token.type == TOKEN_GREATER_THAN || parser->current_token.type == TOKEN_GREATER_EQUAL ||
           parser->current_token.type == TOKEN_EQUAL || parser->current_token.type == TOKEN_NOT_EQUAL) {
        TokenType op = parser->current_token.type;
        advance(parser);
        ASTNode *right = parse_bitwise(parser);
        node = create_binary_op_node(node, right, op);
    }

    return node;
}

/* Parse bitwise operations
 * Parses bitwise AND, OR, XOR, left shift, and right shift operations.
 */
ASTNode *parse_bitwise(Parser *parser) {
    ASTNode *node = parse_term(parser);

    while (parser->current_token.type == TOKEN_BITWISE_AND || parser->current_token.type == TOKEN_BITWISE_OR ||
           parser->current_token.type == TOKEN_BITWISE_XOR || parser->current_token.type == TOKEN_LEFT_SHIFT ||
           parser->current_token.type == TOKEN_RIGHT_SHIFT) {
        TokenType op = parser->current_token.type;
        advance(parser);
        ASTNode *right = parse_term(parser);
        node = create_binary_op_node(node, right, op);
    }

    return node;
}

/* Parse term
 * Parses a term, which can be a series of factors connected by *, /, %, or //.
 */
ASTNode *parse_term(Parser *parser) {
    ASTNode *node = parse_factor(parser);

    while (parser->current_token.type == TOKEN_MULTIPLY || parser->current_token.type == TOKEN_DIVIDE ||
           parser->current_token.type == TOKEN_MODULUS || parser->current_token.type == TOKEN_INT_DIVIDE) {
        TokenType op = parser->current_token.type;
        advance(parser);
        ASTNode *right = parse_factor(parser);
        node = create_binary_op_node(node, right, op);
    }

    return node;
}

/* Parse factor
 * Parses a factor, which can be a number, a parenthesized expression, or a unary operation.
 */
 ASTNode *parse_factor(Parser *parser) {
     if (parser->current_token.type == TOKEN_PLUS || parser->current_token.type == TOKEN_MINUS) {
         TokenType op = parser->current_token.type;
         advance(parser);
         ASTNode *operand = parse_factor(parser);
         return create_unary_op_node(operand, op);
     }

     ASTNode *node = parse_power(parser);

     // Handle implicit multiplication
     while (parser->current_token.type == TOKEN_LPAREN ||
            parser->current_token.type == TOKEN_NUMBER ||
            parser->current_token.type == TOKEN_IDENTIFIER) {
         if (parser->current_token.type == TOKEN_LPAREN) {
             advance(parser);
             ASTNode *right = parse_expression(parser);
             if (parser->current_token.type != TOKEN_RPAREN) {
                 fprintf(stderr, "Expected ')'\n");
                 exit(1);
             }
             advance(parser);
             node = create_binary_op_node(node, right, TOKEN_MULTIPLY);
         } else if (parser->current_token.type == TOKEN_NUMBER ||
                    parser->current_token.type == TOKEN_IDENTIFIER) {
             ASTNode *right = parse_power(parser);
             node = create_binary_op_node(node, right, TOKEN_MULTIPLY);
         }
     }

     return node;
 }

/* Parse power
 * Parses exponentiation operations.
 */
 ASTNode *parse_power(Parser *parser) {
     ASTNode *node;

     if (parser->current_token.type == TOKEN_IDENTIFIER) {
         char *identifier = strdup(parser->current_token.value);
         advance(parser);

         if (parser->current_token.type == TOKEN_LPAREN) {
             // Function call
             advance(parser);
             ASTNode **args = NULL;
             int arg_count = 0;

             if (parser->current_token.type != TOKEN_RPAREN) {
                 do {
                     arg_count++;
                     args = realloc(args, sizeof(ASTNode*) * arg_count);
                     args[arg_count - 1] = parse_expression(parser);

                     if (parser->current_token.type == TOKEN_COMMA) {
                         advance(parser);
                     } else {
                         break;
                     }
                 } while (1);
             }

             if (parser->current_token.type != TOKEN_RPAREN) {
                 fprintf(stderr, "Expected ')'\n");
                 exit(1);
             }
             advance(parser);

             node = create_function_call_node(identifier, args, arg_count);
         } else {
             // Variable (not supported in this parser, but we'll create a node for it)
             node = create_number_node(0); // Placeholder for variable
             fprintf(stderr, "Variables are not supported in this parser\n");
             exit(1);
         }

         free(identifier);
     } else if (parser->current_token.type == TOKEN_NUMBER) {
         double value = atof(parser->current_token.value);
         advance(parser);
         node = create_number_node(value);
     } else if (parser->current_token.type == TOKEN_LPAREN) {
         advance(parser);
         node = parse_expression(parser);
         if (parser->current_token.type != TOKEN_RPAREN) {
             fprintf(stderr, "Expected ')'\n");
             exit(1);
         }
         advance(parser);
     } else {
         fprintf(stderr, "Unexpected token in parse_power\n");
         exit(1);
     }

     while (parser->current_token.type == TOKEN_POWER) {
         advance(parser);
         ASTNode *right = parse_factor(parser);
         node = create_binary_op_node(node, right, TOKEN_POWER);
     }

     return node;
 }

/* Parse function call
 * Parses function calls and handles parenthesized expressions.
 */
ASTNode *parse_function_call(Parser *parser) {
    if (parser->current_token.type == TOKEN_IDENTIFIER) {
        char *function_name = strdup(parser->current_token.value);
        advance(parser);

        if (parser->current_token.type == TOKEN_LPAREN) {
            advance(parser);
            ASTNode **args = NULL;
            int arg_count = 0;

            if (parser->current_token.type != TOKEN_RPAREN) {
                do {
                    arg_count++;
                    args = realloc(args, sizeof(ASTNode*) * arg_count);
                    args[arg_count - 1] = parse_expression(parser);

                    if (parser->current_token.type == TOKEN_COMMA) {
                        advance(parser);
                    } else {
                        break;
                    }
                } while (1);
            }

            if (parser->current_token.type != TOKEN_RPAREN) {
                fprintf(stderr, "Expected ')'\n");
                exit(1);
            }
            advance(parser);

            return create_function_call_node(function_name, args, arg_count);
        }

        // If it's not a function call, treat it as a variable (which we don't support in this example)
        fprintf(stderr, "Variables are not supported in this parser\n");
        exit(1);
    }

    if (parser->current_token.type == TOKEN_NUMBER) {
        double value = atof(parser->current_token.value);
        advance(parser);
        return create_number_node(value);
    }

    if (parser->current_token.type == TOKEN_LPAREN) {
        advance(parser);
        ASTNode *node = parse_expression(parser);
        if (parser->current_token.type != TOKEN_RPAREN) {
            fprintf(stderr, "Expected ')'\n");
            exit(1);
        }
        advance(parser);
        return node;
    }

    fprintf(stderr, "Unexpected token\n");
    exit(1);
}

/* Evaluate function
 * Recursively evaluates the AST and returns the result of the expression.
 * The result can be either an integer or a double, depending on the computation.
 */
EvalResult evaluate(ASTNode *node) {
    EvalResult result;
    result.is_integer = false;  // Default to double

    switch (node->type) {
        case NODE_NUMBER:
            // Check if the number is an integer
            if (floor(node->data.number) == node->data.number) {
                result.value.int_value = (int)node->data.number;
                result.is_integer = true;
            } else {
                result.value.double_value = node->data.number;
            }
            return result;
        case NODE_BINARY_OP: {
            EvalResult left = evaluate(node->data.binary_op.left);
            EvalResult right = evaluate(node->data.binary_op.right);

            // If both operands are integers, perform integer operation
            if (left.is_integer && right.is_integer) {
                result.is_integer = true;
                switch (node->data.binary_op.op) {
                    case TOKEN_PLUS: result.value.int_value = left.value.int_value + right.value.int_value; break;
                    case TOKEN_MINUS: result.value.int_value = left.value.int_value - right.value.int_value; break;
                    case TOKEN_MULTIPLY: result.value.int_value = left.value.int_value * right.value.int_value; break;
                    case TOKEN_DIVIDE:
                        // Check for division by zero
                        if (right.value.int_value == 0) {
                            fprintf(stderr, "Error: Division by zero\n");
                            exit(1);
                        }
                        // If the division results in a whole number, keep it as an integer
                        if (left.value.int_value % right.value.int_value == 0) {
                            result.value.int_value = left.value.int_value / right.value.int_value;
                        } else {
                            result.is_integer = false;
                            result.value.double_value = (double)left.value.int_value / right.value.int_value;
                        }
                        break;
                    case TOKEN_MODULUS: result.value.int_value = left.value.int_value % right.value.int_value; break;
                    case TOKEN_INT_DIVIDE: result.value.int_value = left.value.int_value / right.value.int_value; break;
                    case TOKEN_BITWISE_AND: result.value.int_value = left.value.int_value & right.value.int_value; break;
                    case TOKEN_BITWISE_OR: result.value.int_value = left.value.int_value | right.value.int_value; break;
                    case TOKEN_BITWISE_XOR: result.value.int_value = left.value.int_value ^ right.value.int_value; break;
                    case TOKEN_LEFT_SHIFT: result.value.int_value = left.value.int_value << right.value.int_value; break;
                    case TOKEN_RIGHT_SHIFT: result.value.int_value = left.value.int_value >> right.value.int_value; break;
                    case TOKEN_LESS_THAN: result.value.int_value = left.value.int_value < right.value.int_value; break;
                    case TOKEN_LESS_EQUAL: result.value.int_value = left.value.int_value <= right.value.int_value; break;
                    case TOKEN_GREATER_THAN: result.value.int_value = left.value.int_value > right.value.int_value; break;
                    case TOKEN_GREATER_EQUAL: result.value.int_value = left.value.int_value >= right.value.int_value; break;
                    case TOKEN_EQUAL: result.value.int_value = left.value.int_value == right.value.int_value; break;
                    case TOKEN_NOT_EQUAL: result.value.int_value = left.value.int_value != right.value.int_value; break;
                    case TOKEN_POWER:
                        // Power operation might result in a double, so we handle it separately
                        result.is_integer = false;
                        result.value.double_value = pow(left.value.int_value, right.value.int_value);
                        // Check if the result is actually an integer
                        if (floor(result.value.double_value) == result.value.double_value) {
                            result.is_integer = true;
                            result.value.int_value = (int)result.value.double_value;
                        }
                        break;
                    default:
                        fprintf(stderr, "Unknown binary operator\n");
                        exit(1);
                }
            } else {
                // If either operand is a double, perform double operation
                result.is_integer = false;
                double left_val = left.is_integer ? left.value.int_value : left.value.double_value;
                double right_val = right.is_integer ? right.value.int_value : right.value.double_value;
                switch (node->data.binary_op.op) {
                    case TOKEN_PLUS: result.value.double_value = left_val + right_val; break;
                    case TOKEN_MINUS: result.value.double_value = left_val - right_val; break;
                    case TOKEN_MULTIPLY: result.value.double_value = left_val * right_val; break;
                    case TOKEN_DIVIDE:
                        if (right_val == 0) {
                            fprintf(stderr, "Error: Division by zero\n");
                            exit(1);
                        }
                        result.value.double_value = left_val / right_val;
                        break;
                    case TOKEN_MODULUS: result.value.double_value = fmod(left_val, right_val); break;
                    case TOKEN_POWER: result.value.double_value = pow(left_val, right_val); break;
                    case TOKEN_LESS_THAN: result.value.double_value = left_val < right_val; break;
                    case TOKEN_LESS_EQUAL: result.value.double_value = left_val <= right_val; break;
                    case TOKEN_GREATER_THAN: result.value.double_value = left_val > right_val; break;
                    case TOKEN_GREATER_EQUAL: result.value.double_value = left_val >= right_val; break;
                    case TOKEN_EQUAL: result.value.double_value = left_val == right_val; break;
                    case TOKEN_NOT_EQUAL: result.value.double_value = left_val != right_val; break;
                    default:
                        fprintf(stderr, "Invalid operation for floating-point numbers\n");
                        exit(1);
                }
            }
            return result;
        }
        case NODE_UNARY_OP: {
            EvalResult operand = evaluate(node->data.unary_op.operand);
            result.is_integer = operand.is_integer;
            if (result.is_integer) {
                switch (node->data.unary_op.op) {
                    case TOKEN_PLUS: result.value.int_value = operand.value.int_value; break;
                    case TOKEN_MINUS: result.value.int_value = -operand.value.int_value; break;
                    default:
                        fprintf(stderr, "Unknown unary operator\n");
                        exit(1);
                }
            } else {
                switch (node->data.unary_op.op) {
                    case TOKEN_PLUS: result.value.double_value = operand.value.double_value; break;
                    case TOKEN_MINUS: result.value.double_value = -operand.value.double_value; break;
                    default:
                        fprintf(stderr, "Unknown unary operator\n");
                        exit(1);
                }
            }
            return result;
        }
        case NODE_FUNCTION_CALL: {
            // Function calls will generally return double values
            result.is_integer = false;
            if (strcmp(node->data.function_call.name, "sin") == 0) {
                if (node->data.function_call.arg_count != 1) {
                    fprintf(stderr, "sin function expects 1 argument\n");
                    exit(1);
                }
                EvalResult arg = evaluate(node->data.function_call.args[0]);
                result.value.double_value = sin(arg.is_integer ? arg.value.int_value : arg.value.double_value);
            } else if (strcmp(node->data.function_call.name, "cos") == 0) {
            	if (node->data.function_call.arg_count != 1) {
                    fprintf(stderr, "cos function expects 1 argument\n");
                    exit(1);
                }
                EvalResult arg = evaluate(node->data.function_call.args[0]);
                result.value.double_value = cos(arg.is_integer ? arg.value.int_value : arg.value.double_value);
                // ... (similar implementation for cos, tan, log)
            } else if (strcmp(node->data.function_call.name, "factorial") == 0) {
                if (node->data.function_call.arg_count != 1) {
                    fprintf(stderr, "factorial function expects 1 argument\n");
                    exit(1);
                }
                EvalResult arg = evaluate(node->data.function_call.args[0]);
                if (!arg.is_integer || arg.value.int_value < 0) {
                    fprintf(stderr, "factorial is only defined for non-negative integers\n");
                    exit(1);
                }
                result.is_integer = true;
                result.value.int_value = 1;
                for (int i = 2; i <= arg.value.int_value; i++) {
                    result.value.int_value *= i;
                }
            } else {
                fprintf(stderr, "Unknown function: %s\n", node->data.function_call.name);
                exit(1);
            }
            if (floor(result.value.double_value) == result.value.double_value) {
				result.is_integer = true;
				result.value.int_value = (int)result.value.double_value;
            }
            return result;
        }
        default:
            fprintf(stderr, "Unknown node type\n");
            exit(1);
    }
}


/* Evaluate function
 * Recursively evaluates the AST and returns the result of the expression.
 */
// double evaluate(ASTNode *node) {
//     switch (node->type) {
//         case NODE_NUMBER:
//             return node->data.number;
//         case NODE_BINARY_OP: {
//             double left = evaluate(node->data.binary_op.left);
//             double right = evaluate(node->data.binary_op.right);
//             switch (node->data.binary_op.op) {
//                 case TOKEN_PLUS: return left + right;
//                 case TOKEN_MINUS: return left - right;
//                 case TOKEN_MULTIPLY: return left * right;
//                 case TOKEN_DIVIDE: return left / right;
//                 case TOKEN_MODULUS: return fmod(left, right);
//                 case TOKEN_POWER: return pow(left, right);
//                 case TOKEN_INT_DIVIDE: return (int)(left / right);
//                 case TOKEN_BITWISE_AND: return (int)left & (int)right;
//                 case TOKEN_BITWISE_OR: return (int)left | (int)right;
//                 case TOKEN_BITWISE_XOR: return (int)left ^ (int)right;
//                 case TOKEN_LEFT_SHIFT: return (int)left << (int)right;
//                 case TOKEN_RIGHT_SHIFT: return (int)left >> (int)right;
//                 case TOKEN_LESS_THAN: return left < right;
//                 case TOKEN_LESS_EQUAL: return left <= right;
//                 case TOKEN_GREATER_THAN: return left > right;
//                 case TOKEN_GREATER_EQUAL: return left >= right;
//                 case TOKEN_EQUAL: return left == right;
//                 case TOKEN_NOT_EQUAL: return left != right;
//                 default:
//                     fprintf(stderr, "Unknown binary operator\n");
//                     exit(1);
//             }
//         }
//         case NODE_UNARY_OP: {
//             double operand = evaluate(node->data.unary_op.operand);
//             switch (node->data.unary_op.op) {
//                 case TOKEN_PLUS: return operand;
//                 case TOKEN_MINUS: return -operand;
//                 default:
//                     fprintf(stderr, "Unknown unary operator\n");
//                     exit(1);
//             }
//         }
//         case NODE_FUNCTION_CALL: {
//             // Evaluate built-in functions
//             if (strcmp(node->data.function_call.name, "sin") == 0) {
//                 if (node->data.function_call.arg_count != 1) {
//                     fprintf(stderr, "sin function expects 1 argument\n");
//                     exit(1);
//                 }
//                 return sin(evaluate(node->data.function_call.args[0]));
//             } else if (strcmp(node->data.function_call.name, "cos") == 0) {
//                 if (node->data.function_call.arg_count != 1) {
//                     fprintf(stderr, "cos function expects 1 argument\n");
//                     exit(1);
//                 }
//                 return cos(evaluate(node->data.function_call.args[0]));
//             } else if (strcmp(node->data.function_call.name, "tan") == 0) {
//                 if (node->data.function_call.arg_count != 1) {
//                     fprintf(stderr, "tan function expects 1 argument\n");
//                     exit(1);
//                 }
//                 return tan(evaluate(node->data.function_call.args[0]));
//             } else if (strcmp(node->data.function_call.name, "log") == 0) {
//                 if (node->data.function_call.arg_count != 1) {
//                     fprintf(stderr, "log function expects 1 argument\n");
//                     exit(1);
//                 }
//                 return log(evaluate(node->data.function_call.args[0]));
//             } else if (strcmp(node->data.function_call.name, "factorial") == 0) {
//                 if (node->data.function_call.arg_count != 1) {
//                     fprintf(stderr, "factorial function expects 1 argument\n");
//                     exit(1);
//                 }
//                 int n = (int)evaluate(node->data.function_call.args[0]);
//                 if (n < 0) {
//                     fprintf(stderr, "factorial is not defined for negative numbers\n");
//                     exit(1);
//                 }
//                 int result = 1;
//                 for (int i = 2; i <= n; i++) {
//                     result *= i;
//                 }
//                 return result;
//             } else {
//                 fprintf(stderr, "Unknown function: %s\n", node->data.function_call.name);
//                 exit(1);
//             }
//             // TODO: Add more functions as needed
//         }
//         default:
//             fprintf(stderr, "Unknown node type\n");
//             exit(1);
//     }
// }

/* Free AST function
 * Recursively frees the memory allocated for the Abstract Syntax Tree.
 */
void free_ast(ASTNode *node) {
    if (node == NULL) return;

    switch (node->type) {
        case NODE_BINARY_OP:
            free_ast(node->data.binary_op.left);
            free_ast(node->data.binary_op.right);
            break;
        case NODE_UNARY_OP:
            free_ast(node->data.unary_op.operand);
            break;
        case NODE_FUNCTION_CALL:
            free(node->data.function_call.name);
            for (int i = 0; i < node->data.function_call.arg_count; i++) {
                free_ast(node->data.function_call.args[i]);
            }
            free(node->data.function_call.args);
            break;
        case NODE_NUMBER:
            // Nothing to free for number nodes
            break;
    }

    free(node);
}
