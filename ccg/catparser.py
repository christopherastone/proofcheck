import category
import collections
import ply.lex as lex
import ply.yacc as yacc
import pyrsistent
import semantic_types
import semantics
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
    #    'DRSLASH', 'DLSLASH',
    'SLASHDOT', 'SLASHO', 'SLASHX', 'SLASHBANG', 'SLASHSTAR',
    'COLON', 'SEMI',
    'ARROW',
    'QUOTEDSTRING',
    'QUERY', 'STAR', 'LABEL',
    'MULTIPLICITY',
)

# Regular expression rules for simple tokens
t_LSLASH = r'\\'
t_RSLASH = '/'
t_LBRACK = r'\['
t_RBRACK = r'\]'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_EQ = r'='
t_COMMA = r','
# t_DRSLASH = r'//'
# t_DLSLASH = '\\\\'
t_COLON = r':'
t_SEMI = r';'
t_ARROW = r'->'
t_QUERY = r'\?'
# t_BANG = r'!'
t_STAR = r'\*'


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


def t_MULTIPLICITY(t):
    r'[xX][0-9]+'
    t.value = int(t.value[1:])
    return t


def t_LABEL(t):
    r"[-A-Za-z_'0-9]+[.]"
    return t


def t_WORD(t):
    r"[A-Za-z_'0-9]+"
    return t


def t_QUOTEDSTRING(t):
    r'\"[^\"]*?\"'
    t.value = t.value[1:-1]
    return t


# Define a rule so we can track line numbers


# def t_ENDLINES(t):
#     r'\n+'
#     t.lexer.lineno += len(t.value)
#     t.value = '\n'
#     return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    pass


# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t'

# C or C++ comment (ignore)


def t_comment(t):
    r'\#[^\\n]*'
    pass

# Error handling rule


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
lexer = lex.lex()

semantic_type_map = {}
word_map = collections.defaultdict(list)
sentence_list = []


def p_top_0(p):
    '''top : '''


def p_top_1(p):
    '''top : vocab'''


def p_top_2(p):
    '''top : vocab SEMI top'''


def p_vocab_1(p):
    '''vocab : WORD COLON cats'''
    word_map[p[1]] += [(cat, None) for cat in p[3]]


def p_vocab_2(p):
    '''vocab : WORD COLON cat EQ sem'''
    word_map[p[1]] += [(p[3], p[5].deBruijn())]


def p_vocab_3(p):
    '''vocab : WORD COLON COLON semty'''
    assert(p[2] not in semantic_type_map)
    semantic_type_map[p[1]] = p[4]


def p_vocab_4a(p):
    '''vocab : LABEL QUOTEDSTRING
             | LABEL QUOTEDSTRING cat'''
    label = p[1]
    sentence = p[2].strip(".\t ").lower()
    category = p[3] if len(p) == 4 else None
    multiplicity = 1
    sentence_list.append((label, sentence, category, multiplicity))


def p_vocab_4b(p):
    '''vocab : LABEL QUERY QUOTEDSTRING
             | LABEL QUERY QUOTEDSTRING cat'''
    label = p[1]
    sentence = p[3].strip(".\t ").lower()
    category = p[4] if len(p) == 5 else None
    multiplicity = None
    sentence_list.append((label, sentence, category, multiplicity))


def p_vocab_5(p):
    '''vocab : LABEL QUOTEDSTRING MULTIPLICITY
             | LABEL QUOTEDSTRING cat MULTIPLICITY'''
    label = p[1]
    sentence = p[2].strip(".\t ").lower()
    category = p[3] if len(p) == 5 else None
    multiplicity = p[4] if len(p) == 5 else p[3]
    sentence_list.append((label, sentence, category, multiplicity))


def p_vocab_6(p):
    '''vocab : LABEL STAR QUOTEDSTRING
             | LABEL STAR QUOTEDSTRING cat'''
    label = p[1]
    sentence = p[3].strip(".\t ").lower()
    category = p[4] if len(p) == 5 else None
    multiplicity = 0
    sentence_list.append((label, sentence, category, multiplicity))


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
    '''cat : cat LSLASH atcat
           | cat RSLASH atcat'''
    p[0] = category.SlashCategory(
        p[1], slash.Slash(p[2], slash.ANYRULE), p[3])


def p_cat_2(p):
    '''cat : cat SLASHDOT atcat
           | cat SLASHBANG atcat
           | cat SLASHO atcat
           | cat SLASHX atcat
           | cat SLASHSTAR atcat'''
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


def p_atcat_4(p):
    '''atcat : QUOTEDSTRING'''
    p[0] = category.SingletonCategory(p[1])


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


def p_atsem_1(p):
    '''atsem : WORD'''
    p[0] = semantics.Const(p[1])


def p_atsem_2(p):
    '''atsem : LPAREN sem RPAREN'''
    p[0] = p[2]


def p_path_1(p):
    '''path : atsem'''
    p[0] = p[1]


def p_path_2(p):
    '''path : path atsem'''
    p[0] = semantics.App(p[1], p[2])


def p_sem_1(p):
    '''sem : path'''
    p[0] = p[1]


def p_sem_2a(p):
    '''sem : LSLASH WORD ARROW sem'''
    p[0] = semantics.Lam(p[2], p[4])


def p_sem_2b(p):
    '''sem : SLASHX WORD ARROW sem
           | SLASHO WORD ARROW sem'''
    p[0] = semantics.Lam(p[1][1], p[4])


def p_sem_3(p):
    '''sem : path LSLASH WORD ARROW sem'''
    p[0] = semantics.App(p[1], semantics.Lam(p[3], p[5]))


# Error rule for syntax errors


def p_error(p):
    if p:
        print(
            f"Syntax error on line {p.lineno} at token '{p.type}' ({p.value})")
        # Just discard the token and tell the parser it's okay.
        # parser.errok()
    else:
        print("Syntax error at EOF")


# Build the parsers
parser = yacc.yacc()
catparser = yacc.yacc(start='cat', errorlog=yacc.NullLogger())


###########
# PARSING #
###########


def do_parses(inputs):
    global semantic_type_map, word_map, sentence_list

    lexer.lineno = 0
    semantic_type_map = {}
    word_map = collections.defaultdict(list)
    sentence_list = []

    for input in inputs:
        parser.parse(input)
        lexer.lineno += 1

    return word_map, sentence_list


if __name__ == '__main__':
    print("\nLEXING TEST")
    print("-----------")

    data = '''
eats : (S \\ NP[3,sg]) / NP = \\ x -> \\ y -> ((eat' x) y)
    '''
    print(data)

    # Give the lexer some input
    lexer.lineno = 0
    lexer.input(data)

    # Tokenize
    while True:
        tok = lexer.token()
        if not tok:
            break      # No more input
        print(tok)

    print("\nPARSING TEST")
    print("------------")

    wds, sents = do_parses(data.splitlines())
    print()
    for cat, sem in semantic_type_map.items():
        print(f'{cat} has type {sem}')
    print()
    for word, cats in wds.items():
        for cat, sem in cats:
            print(f'{word} has category {cat} and semantics {sem}')
    print()
    for s in sents:
        print(s)
    print()
