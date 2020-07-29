# Name: Ratan Singh Ahirwar
import ply.lex as lex
import ply.yacc as yacc
import traceback, sys


class FuncStack:
    def __init__(self):
        self.stack = [{}]

    def push(self):
        self.stack.append({})

    def pop(self):
        self.stack.pop()

    def get(self, key):
        temp = reversed(self.stack)
        stack_top = self.stack[len(self.stack) - 1]
        # if it is a variable get from top of stack
        if key in stack_top:
            return stack_top[key]
        # if it is a Function object search in full stack
        for stack_element in temp:
            if key in stack_element and isinstance(stack_element[key], Function):
                return stack_element[key]
        return None

    def put(self, key, value):
        self.stack[len(self.stack) - 1][key] = value

    # add variable map specific to the func call to stack
    def add_func_st(self, arg_names, arg_values):
        self.push()
        for i in range(len(arg_names)):
            self.put(arg_names[i], arg_values[i])

    # remove variable map specific to the func call to stack
    def remove_func_st(self):
        self.pop()


# symbol_table = {}
symbol_table = FuncStack()

tokens = [
    'LPAREN', 'RPAREN', 'HASH', 'LBRACKET', 'RBRACKET',
    'POWER', 'TIMES', 'DIVIDE', 'PLUS', 'MINUS',
    'CONS',
    'LT', 'LTE', 'EQL', 'NEQL', 'GT', 'GTE',
    'NUMBER', 'STRING', 'COMMA',
    'EXPONENT',
    'SEMICOL', 'VAR', 'LBRACE', 'RBRACE', 'EQUALS'
]

reserved = {
    'if': 'IF',
    'else': 'ELSE',
    'while': 'WHILE',
    'print': 'PRINT',
    'andalso': 'ANDALSO',
    'orelse': 'ORELSE',
    'not': 'NOT',
    'mod': 'MOD',
    'in': 'IN',
    'True': 'TRUE',
    'False': 'FALSE',
    'div': 'DIV',
    'fun': 'FUN'
}
tokens = tokens + list(reserved.values())

t_LBRACE = r'\{'
t_RBRACE = r'\}'
t_SEMICOL = r'\;'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_HASH = r'\#'
t_LBRACKET = r'\['
t_RBRACKET = r'\]'
t_POWER = r'\*\*'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_PLUS = r'\+'
t_MINUS = r'-'
t_IN = 'in'
t_CONS = r'::'
t_NOT = 'not'
t_ANDALSO = 'andalso'
t_ORELSE = 'orelse'
t_DIV = 'div'
t_MOD = 'mod'
t_FUN = 'fun'
t_LT = r'<'
t_LTE = r'<='
t_EQL = r'=='
t_NEQL = r'<>'
t_GT = r'>'
t_GTE = r'>='
t_COMMA = r','
# place this below ==
t_EQUALS = r'\='


def strip_quotes(str):
    return str.strip('(\")|(\')')


def t_EXPONENT(t):
    r'([-]?[0-9]+(?:\.[0-9]+)?)e[-]?[0-9]+'
    try:
        base = Number(t.value.split("e")[0])
        power = Number(t.value.split("e")[1])
        t.value = ExpoNumber(base, power)
    except Exception:
        pass
    return t


def t_NUMBER(t):
    r'(\d+(?:\.\d+)?)'
    try:
        t.value = Number(t.value)
    except Exception:
        pass
    return t


def t_VAR(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'VAR')  # Check for reserved words
    return t


def t_STRING(t):
    r'(\"([^\\\n]|(\\.))*?\") | (\'([^\\\n]|(\\.))*?\')'
    try:
        t.value = String(strip_quotes(str(t.value)))
    except Exception:
        pass
    return t


def t_TRUE(t):
    'True'
    t.value = Boolean(t.value)
    return t


def t_FALSE(t):
    'False'
    t.value = Boolean(t.value)
    return t


t_ignore = " \n\t"


def t_error(t):
    # print("2--- ", t.value)
    raise SyntaxError


precedence = (
    ('left', 'ORELSE'),
    ('left', 'ANDALSO'),
    ('left', 'NOT'),
    ('left', 'LT', 'GT', 'LTE', 'GTE', 'EQL', 'NEQL'),
    ('right', 'CONS'),
    ('left', 'IN'),
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIVIDE', 'DIV', 'MOD'),
    ('right', 'UMINUS'),
    ('right', 'POWER', 'EXPONENT'),
    ('left', 'LBRACKET', 'RBRACKET'),
    ('left', 'HASH'),
    ('left', 'LPAREN', 'RPAREN'),
    ('left', 'IF', 'WHILE', 'ELSE'),
    ('left', 'LBRACE', 'RBRACE')
)


def p_start(t):
    """start : funcs nested_blocks
         | nested_blocks"""
    t[0] = StartSymbol(t[2])


# { {{}} {{}} }
def p_nested_blocks(t):
    """nested_blocks : LBRACE blocks RBRACE"""
    t[0] = t[2]


# { {} {} }
def p_blocks(t):
    """blocks : block
    | blocks block"""
    if len(t) == 2:
        t[0] = Blocks(None, t[1])
    elif len(t) == 3:
        t[0] = Blocks(t[1], t[2])
    else:
        t[0] = Blocks(None, None)


# {}
def p_block(t):
    """block : statements
    | nested_block
    | nested_blocks"""
    if not isinstance(t[1], Block):
        t[1] = Block(t[1])
    t[0] = t[1]


# { {{}} }
def p_nested_block(t):
    """nested_block : LBRACE block RBRACE"""
    t[0] = t[2]


# fun a = {} exp; fun b = {} exp;
def p_funcs(t):
    """funcs : funcs func"""
    t[0] = t[1] + [t[2]]


# TODO: rollback empty exp case
def p_func(t):
    """func : FUN VAR LPAREN func_def_args RPAREN EQUALS nested_blocks exp SEMICOL"""
    # if (len(t) == 9):
    #     t[0] = Function(t[2], t[4], t[7], None)
    # else:
    t[0] = Function(t[2], t[4], t[7], t[8])


def p_func_(t):
    """funcs : func"""
    t[0] = [t[1]]


# function definition argument prod rule
def p_func_def_args_(t):
    """func_def_args : func_def_args COMMA VAR"""
    t[0] = t[1] + [t[3]]


def p_func_def_args(t):
    """func_def_args : VAR
    |"""
    if (len(t) == 1):
        t[0] = None
    else:
        t[0] = [t[1]]


def p_func_call(t):
    """func_call : VAR LPAREN func_call_args RPAREN
    | VAR LPAREN RPAREN"""
    if (len(t) == 4):
        t[0] = FuncCall(t[1], None)
    else:
        t[0] = FuncCall(t[1], t[3])


# function call argument prod rule
def p_func_call_args(t):
    """func_call_args : func_call_args COMMA exp"""
    t[0] = t[1] + [t[3]]


def p_func_call_args_(t):
    """func_call_args : exp"""
    t[0] = [t[1]]


def p_exp_func_call(t):
    """exp : func_call"""
    t[0] = t[1]


def p_statements(t):
    """statements : statement
    | statements statement
    | """
    if len(t) == 2:
        t[0] = Statements(None, t[1])
    elif len(t) == 3:
        t[0] = Statements(t[1], t[2])
    elif len(t) == 1:
        t[0] = Statements(None, None)


def p_print_statement(t):
    """statement : PRINT LPAREN exp RPAREN SEMICOL"""
    t[0] = Print(t[3])


def p_statement_exp(t):
    """statement : exp SEMICOL"""
    t[0] = StatementExp(t[1])


def p_statement_assign(t):
    """statement : VAR EQUALS exp SEMICOL"""
    t[0] = Assignment(t[1], t[3])


def p_statement_assign_list(t):
    """statement : element_at EQUALS exp SEMICOL"""
    t[0] = AssignmentList(t[1], t[3])


def p_statement_conditional(t):
    """statement : ifstat
    | whilestat"""
    t[0] = t[1]


def p_if_statement(t):
    """ifstat : IF LPAREN exp RPAREN nested_block elsestat
    | IF LPAREN exp RPAREN statement elsestat"""
    if len(t) == 7:
        t[0] = If(t[3], t[5], t[6])
    elif len(t) == 9:
        t[0] = If(t[3], t[6], t[8])


def p_else_statement(t):
    """elsestat : ELSE nested_block
    | ELSE statement
    | """
    if len(t) == 3:
        t[0] = Else(t[2])
    elif len(t) == 5:
        t[0] = Else(t[3])
    else:
        t[0] = EmptyStatement()


def p_while_statement(t):
    """whilestat : WHILE LPAREN exp RPAREN nested_block
    | WHILE LPAREN exp RPAREN statement"""
    if len(t) == 6:
        t[0] = While(t[3], t[5])
    elif len(t) == 8:
        t[0] = While(t[3], t[6])


def p_exp_uminus(t):
    """exp : MINUS exp %prec UMINUS"""
    t[0] = NegNumber(t[2])


def p_exp_not_bool(t):
    """exp : NOT exp"""
    t[0] = BooleanNot(Boolean(t[2]))


def p_exp_var(t):
    """exp : VAR"""
    t[0] = Variable(t[1])


def p_exp_binaryoperation(t):
    """exp : exp DIVIDE exp
    | exp DIV exp
    | exp TIMES exp
    | exp PLUS exp
    | exp MINUS exp
    | exp MOD exp
    | exp POWER exp
    | exp CONS exp"""
    t[0] = BinaryOperation(t[2], t[1], t[3])


# TODO: add "IN" as operator and use the python inbuilt IN instead of individual casses. diff semantic check
def p_exp_compare(t):
    """exp : exp LT exp
    | exp LTE exp
    | exp GT exp
    | exp GTE exp
    | exp EQL exp
    | exp NEQL exp
    | exp ORELSE exp
    | exp ANDALSO exp
    | exp IN exp"""
    t[0] = Compare(t[2], t[1], t[3])


def p_exp_boolean(t):
    """exp : boolean"""
    t[0] = t[1]


def p_boolean_false(t):
    """boolean : FALSE"""
    t[0] = Boolean(t[1])


def p_boolean_true(t):
    """boolean : TRUE"""
    t[0] = Boolean(t[1])


def p_exp(t):
    """exp : NUMBER
    | EXPONENT
    | STRING
    | list
    | element_at
    | tuple"""
    t[0] = Expression(t[1])


def p_exp_par(t):
    """exp : LPAREN exp RPAREN"""
    t[0] = t[2]


def p_exps(t):
    """exps : exp
    | exps COMMA exp"""
    if len(t) == 2:
        t[0] = MultiExpression(t[1])
    else:
        t[1].append(t[3])
        t[0] = t[1]


def p_list(t):
    """list : LBRACKET exps RBRACKET
    | LBRACKET RBRACKET"""
    if (len(t) == 3):
        t[0] = EmptyList()
    else:
        t[0] = List(t[2])


def p_index(t):
    """index : LBRACKET exp RBRACKET"""
    t[0] = Index(t[2])


# same for list and string
def p_element_at(t):
    """element_at : VAR index
    | list index
    | element_at index
    | STRING index"""
    if isinstance(t[1], str):
        t[0] = ListElementAt(Variable(t[1]), t[2])
    else:
        t[0] = ListElementAt(t[1], t[2])


def p_tuple(t):
    """tuple : LPAREN exps RPAREN
    | LPAREN  RPAREN"""
    if (len(t) == 3):
        t[0] = EmptyTuple()
    else:
        t[0] = Tuple(t[2])


def p_exp_tuple_element_at(t):
    """exp : HASH exp exp"""
    t[0] = TupleElementAt(t[3], t[2])


def p_error(t):
    # print("2--- ", t.value)
    raise SyntaxError


class SemanticException(Exception):
    pass


class Node:
    def __init__(self):
        pass

    def eval(self):
        return 0


class StartSymbol(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        self.child.eval()


class Blocks(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        if (self.child1 != None):
            self.child1.eval()
        if (self.child2 != None):
            self.child2.eval()


class Block(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        self.child.eval()


class EmptyBlk(Node):
    def __init__(self):
        pass

    def eval(self):
        pass


class Statements(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        if self.child1 != None:
            self.child1.eval()
        if self.child2 != None:
            self.child2.eval()


class Assignment(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        res = self.child1
        if type(self.child1) != str:
            res = self.child1.eval()
        symbol_table.put(res, self.child2.eval())
        # symbol_table[self.child1] = self.child2.eval()


# x = ["abc", "def"]; x[4] = "updated"
class AssignmentList(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        # self.child1.child1 type ListElementAt
        self.child1.child1.eval()[self.child1.child2.eval()] = self.child2.eval()


class EmptyStatement(Node):
    def __init__(self):
        super().__init__()

    def eval(self):
        pass


class StatementExp(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        return self.child.eval()


class Print(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        res = self.child.eval()
        if (type(res) == str):
            res = strip_quotes(res)
            if '"' in res:
                res = "'" + res + "'"
            else:
                res = '"' + res + '"'
        print(res)


class If(Node):
    def __init__(self, child1, child2, child3=None):
        self.child1 = child1
        self.child2 = child2
        self.child3 = child3

    def eval(self):
        if self.child1.eval():
            self.child2.eval()
        elif self.child3:
            self.child3.eval()


class Else(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        if self.child:
            self.child.eval()


class While(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        while (self.child1.eval()):
            self.child2.eval()


class Expression(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        return self.child.eval()


class Compare(Node):
    def __init__(self, child0, child1, child2):
        self.child1 = child1
        self.child2 = child2
        self.child0 = child0

    def eval(self):
        res1 = self.child1.eval()
        res2 = self.child2.eval()

        if (self.semantic_check(res1, res2) == False):
            raise SemanticException
        if (self.child0 == '<'):
            return res1 < res2
        elif (self.child0 == '>'):
            return res1 > res2
        elif (self.child0 == '<='):
            return res1 <= res2
        elif (self.child0 == '>='):
            return res1 >= res2
        elif (self.child0 == '<>'):
            return res1 != res2
        elif (self.child0 == '=='):
            return res1 == res2
        elif self.child0 == 'andalso':
            return self.child1.eval() and self.child2.eval()
        elif self.child0 == 'orelse':
            return self.child1.eval() or self.child2.eval()
        elif self.child0 == 'in':
            return self.child1.eval() in self.child2.eval()
        else:
            # print("3 ")
            raise SyntaxError

    def semantic_check(self, res1, res2):
        if (self.child0 == 'in'):
            try:
                res1 in res2
                return True
            except Exception:
                return False
        if ((type(res1) == int or type(res1) == float) and (type(
                res2) == int or type(res2) == float)):
            return True
        elif (type(res1) == str and type(res2) == str):
            return True
        elif (type(res1) == bool and type(res2) == bool):
            return True
        return False


class BinaryOperation(Node):
    def __init__(self, child0, child1, child2):
        self.child1 = child1
        self.child2 = child2
        self.child0 = child0

    def eval(self):
        res1 = self.child1.eval()
        res2 = self.child2.eval()

        if (self.semantic_check(res1, res2) == False):
            raise SemanticException
        if (self.child0 == '+'):
            return res1 + res2
        elif (self.child0 == '-'):
            return res1 - res2
        elif (self.child0 == '*'):
            return res1 * res2
        elif (self.child0 == '/'):
            return res1 / res2
        elif (self.child0 == 'div'):
            return res1 // res2
        elif (self.child0 == 'mod'):
            return res1 % res2
        elif (self.child0 == '**'):
            return res1 ** res2
        elif (self.child0 == '::'):
            return [res1] + res2
        else:
            raise SemanticException

    def semantic_check(self, res1, res2):
        if (self.child0 == '+'):
            if (type(res1) == list and type(res2) == list):
                return True
            elif ((type(res1) == int or type(res1) == float) and (type(
                    res2) == int or type(res2) == float)):
                return True
            elif (type(res1) == str and type(res2) == str):
                return True
            else:
                return False
        elif (self.child0 == '-'):
            if (not ((type(res1) == int or type(res1) == float) and (type(
                    res2) == int or type(res2) == float))):
                return False
        elif (self.child0 == '*'):
            if (not ((type(res1) == int or type(res1) == float) and (type(
                    res2) == int or type(res2) == float))):
                return False
        elif (self.child0 == '/'):
            if (not ((type(res1) == int or type(res1) == float) and (type(
                    res2) == int or type(res2) == float)) or res2 == 0):
                return False
        elif (self.child0 == 'div'):
            if (not ((type(res1) == int or type(res1) == float) and (type(
                    res2) == int or type(res2) == float)) or res2 == 0):
                return False
        elif (self.child0 == '::'):
            if (type(res2) != list):
                return False
        return True


class Variable(Node):
    def __init__(self, var):
        self.var = var
        self.type = type(self)

    def eval(self):
        res = symbol_table.get(self.var)
        if res != None:
            return res
        else:
            raise SemanticException


class EmptyTuple(Node):
    def __init__(self):
        super().__init__()

    def eval(self):
        return ()


class EmptyList(Node):
    def __init__(self):
        self.type = type(self)

    def eval(self):
        return []


class MultiExpression(Node):
    all_exps = None

    def __init__(self, child):
        self.all_exps = [child]

    def append(self, exp):
        self.all_exps.append(exp)

    def eval(self):
        res = []
        for exp in self.all_exps:
            res.append(exp.eval())
        return res


class Number(Node):
    def __init__(self, child):
        if ('.' in child):
            self.value = float(child)
        else:
            self.value = int(child)

    def eval(self):
        return self.value


class ExpoNumber(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        return self.child1.eval() * (pow(10, self.child2.eval()))


class NegNumber(Node):
    def __init__(self, child1):
        self.child1 = child1

    def eval(self):
        return -1 * self.child1.eval()


class String(Node):
    def __init__(self, child):
        self.value = child

    def eval(self):
        return self.value


class BooleanNot(Node):
    def __init__(self, child):
        # self.child will always be of bool type....do not call eval on it
        self.child = child

    def eval(self):
        if type(self.child) == bool:
            return not self.child
        else:
            return self.child.eval()


class Boolean(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        if (self.child == 'True'):
            return True
        else:
            return False


class Index(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        return self.child.eval()


class List(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        if isinstance(self.child, EmptyList):
            return self.child.eval()
        else:
            return list(self.child.eval())


class ListElementAt(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        if (type(self.child2.eval()) != int or (type(self.child1.eval()) != list and type(self.child1.eval()) != str)):
            raise SemanticException
        return self.child1.eval()[self.child2.eval()]


class Tuple(Node):
    def __init__(self, child):
        self.child = child

    def eval(self):
        res = self.child.eval()
        if (len(res) == 1):
            res = res[0]
        if (type(res) != tuple):
            res = tuple(res)

        if isinstance(self.child, EmptyTuple):
            return self.child.eval()
        else:
            return res


class TupleElementAt(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        return self.child1.eval()[self.child2.eval() - 1]


class Function(Node):
    def __init__(self, child1, child2, child3, child4):
        # func name
        self.child1 = child1
        # args
        self.child2 = child2
        # block
        self.child3 = child3
        # exp
        self.child4 = child4
        symbol_table.put(self.child1, self)

    def eval(self, args):
        if args != None:
            args_evaluated = []
            for arg in args:
                args_evaluated.append(arg.eval())
            symbol_table.add_func_st(self.child2, (args_evaluated))
        else:
            symbol_table.add_func_st([], [])
        # TODO first block then exp
        self.child3.eval()  # execute block

        if self.child4 == None:
            return
        else:
            result = self.child4.eval()  # execute the expression
        symbol_table.remove_func_st()
        return result


class FuncCall(Node):
    def __init__(self, child1, child2):
        self.child1 = child1
        self.child2 = child2

    def eval(self):
        func = symbol_table.get(self.child1)
        if (func != None):
            if (isinstance(func, Function)):
                # Function Objt child2 = args
                if self.child2 != None and func.child2 != None and len(func.child2) != len(self.child2):
                    raise SemanticException
                result = func.eval(self.child2)
                if result != None:
                    return result
        else:
            raise SemanticException


yacc.yacc(debug=False)
lex.lex(debug=False)

if (len(sys.argv) != 2):
    sys.exit("Usage: \n"
             "python3 sbml.py <input file>")

file = open(sys.argv[1], 'r')
line = ""
input = ""
ast = None
for line in file:
    input = input + line.rstrip()
try:
    # print(input)
    ast = yacc.parse(input)
    ast.eval()
except SyntaxError:
    print("SYNTAX ERROR")
    # traceback.print_exc(file=sys.stdout)
except SemanticException:
    # traceback.print_exc(file=sys.stdout)
    print("SEMANTIC ERROR")
except Exception:
    # traceback.print_exc(file=sys.stdout)
    print("SEMANTIC ERROR")
