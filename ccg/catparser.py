import category
import collections
import ply.lex as lex
import ply.yacc as yacc
import pyrsistent
import semantic_types
import slash

###########
# LEXING #
###########

# List of token names.   This is always required
tokens = (
    'WORD',
    'LSLASH', 'RSLASH',
    'LBRACK', 'RBRACK',
    'LPAREN', 'RPAREN',
    'EQ', 'COMMA',
    'DRSLASH', 'DLSLASH',
    'SLASHDOT', 'SLASHO', 'SLASHX', 'SLASHBANG', 'SLASHSTAR',
    'COLON',
    'ARROW',
    #    'ENDLINES'
)

# Regular expression rules for simple tokens
t_LSLASH = r'\\'
t_RSLASH = '/'
t_LBRACK = r'\['
t_RBRACK = r'\]'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_EQ = '='
t_COMMA = ','
t_DRSLASH = '//'
t_DLSLASH = '\\\\'
t_COLON = ':'
t_ARROW = '->'


def t_SLASHO(t):
    r'[\\/][Oo○]'
    t.value = t.value[0] + 'o'
    return t


def t_SLASHX(t):
    r'[\\/][Xx×]'
    t.value = t.value[0] + 'x'
    return t


t_SLASHSTAR = r'[\\/]\*'
t_SLASHBANG = r'[\\/]!'
t_SLASHDOT = r'[\\/]\.'

# A regular expression rule with some action code


def t_WORD(t):
    r'[A-Za-z][A-Za-z0-9_]*'
    return t

# Define a rule so we can track line numbers


def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    pass  # return t


# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t'

# C or C++ comment (ignore)


def t_comment(t):
    '\#[^\\n]*'
    pass

# Error handling rule


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
lexer = lex.lex()

semantic_type_map = {}
word_map = collections.defaultdict(list)


def p_vocab_0a(p):
    '''vocab : '''
    p[0] = 0


def p_vocab_1(p):
    '''vocab : vocab WORD COLON cats '''
    word_map[p[2]] += p[4]
    p[0] = 0


def p_vocab_2(p):
    '''vocab : vocab WORD COLON COLON semty'''
    assert(p[2] not in semantic_type_map)
    semantic_type_map[p[2]] = p[5]
    p[0] = 0


def p_cats_1(p):
    '''cats : cat'''
    p[0] = [p[1]]


def p_cats_2(p):
    '''cats : cats COMMA cat'''
    p[0] = p[1] + [p[3]]


def p_cat_0(p):
    '''cat : atcat'''
    p[0] = p[1]


def p_cat_1(p):
    '''cat : atcat LSLASH cat
           | atcat RSLASH cat'''
    p[0] = category.SlashCategory(
        p[1], slash.Slash(p[2], slash.ANYRULE), p[3])


def p_cat_2(p):
    '''cat : atcat SLASHDOT cat
           | atcat SLASHBANG cat
           | atcat SLASHO cat
           | atcat SLASHX cat
           | atcat SLASHSTAR cat'''
    if p[2][1] == '.':
        sl = slash.Slash(p[2][0], slash.ANYRULE)
    elif p[2][1] == '*':
        sl = slash.Slash(p[2][0], slash.APPLYONLY)
    elif p[2][1] == '!':
        sl = slash.Slash(p[2][0], slash.INACTIVE)
    elif p[2][1] == 'x':
        sl = slash.Slash(p[2][0], slash.ALLOWBX)
    elif p[2][1] == 'o':
        sl = slash.Slash(p[2][0], slash.ALLOWB)
    else:
        raise ValueError(p[2])

    p[0] = category.SlashCategory(p[1], sl, p[3])


def p_atcat_1(p):
    '''atcat : WORD'''
    cat = p[1]
    if cat not in semantic_type_map:
        print("UNRECOGNIZED CATEGORY", cat)
        semantic_type_map[cat] = None
    p[0] = category.BaseCategory(cat, semantic_type_map[cat])


def p_atcat_2(p):
    '''atcat : LPAREN cat RPAREN'''
    p[0] = p[2]


def p_atcat_3(p):
    '''atcat : WORD LBRACK attrs RBRACK'''
    cat = p[1]
    if cat not in semantic_type_map:
        print("UNRECOGNIZED CATEGORY", cat)
        semantic_type_map[cat] = None
    p[0] = category.BaseCategory(cat, semantic_type_map[cat], p[3])


def p_attr_1(p):
    '''attr : WORD'''
    p[0] = pyrsistent.pmap({'it': p[1]})


def p_attr_2(p):
    '''attr : WORD EQ WORD'''
    p[0] = pyrsistent.pmap({p[1]: p[3]})


def p_attrs_1(p):
    '''attrs : attr'''
    p[0] = p[1]


def p_attrs_2(p):
    '''attrs : attrs COMMA attr'''
    p[0] = p[1].update(p[3])


def p_asemty_1(p):
    '''asemty : WORD'''
    p[0] = semantic_types.BaseType(p[1])


def p_asemty_2(p):
    '''asemty : LPAREN semty RPAREN'''
    p[0] = p[2]


def p_semty_1(p):
    '''semty : asemty'''
    p[0] = p[1]


def p_semty_2(p):
    '''semty : asemty ARROW semty'''
    p[0] = semantic_types.ArrowType(p[1], p[3])

# Error rule for syntax errors


def p_error(p):
    if p:
        print(f"Syntax error on line {p.lineno} at token '{p.type}'")
        # Just discard the token and tell the parser it's okay.
        # parser.errok()
    else:
        print("Syntax error at EOF")


# Build the parser
catparser = yacc.yacc(
    start='cat')  # , errorlog=yacc.NullLogger(), write_tables=False)
parser = yacc.yacc(write_tables=False)


###########
# PARSING #
###########


def do_parse(input):
    global semantic_type_map, word_map

    lexer.lineno = 0
    semantic_type_map = {}
    word_map = collections.defaultdict(list)

    parser.parse(input)
    return word_map


if __name__ == '__main__':
    print("\nLEXING TEST")
    print("-----------")

    data = '''
      S :: t
      FOO : (S \\x S) / S
      BAR : N / N
    '''

    # Give the lexer some input
    lexer.input(data)

    # Tokenize
    while True:
        tok = lexer.token()
        if not tok:
            break      # No more input
        print(tok)

    print("\nPARSING TEST")
    print("------------")

    wds = do_parse(data)
    print()
    for cat, sem in semantic_type_map.items():
        print(f'{cat} has type {sem}')
    print()
    for word, cats in wds.items():
        for cat in cats:
            print(f'{word} has category {cat}')
    print()
