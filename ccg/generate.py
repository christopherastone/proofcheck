# e.g.,
#    python3 generate.py demo.txt

import catparser
import category
import catset
import ccgbank
import collections
import slash
import sys


# arguably we should be adding the slash (modes) as well,
# since they also are the only ones that can show up in the
# inhabited categories!

def add_arguments_of_cat(cat, cset):
    while isinstance(cat, category.SlashCategory):
        cset.add(cat.dom)
        cat = cat.cod


def all_arguments(lexicon):
    answer = set()
    for infos in lexicon.values():
        for cat, _ in infos:
            add_arguments_of_cat(cat, answer)
    return answer


# mapping from length to
#    category to
#       rule to
#           count
#       'SUM' to sum
COUNT_MEMO_PAD = collections.defaultdict(dict)


def count(goal_cat, n, words_by_cat, argument_set):
    memo = COUNT_MEMO_PAD[n]
    if goal_cat in memo.keys():
        return memo[goal_cat]['SUM']

    counts = {}
    memo[goal_cat] = counts

    # Lexicon
    lex_sum = 0
    if goal_cat in words_by_cat.keys():
        lex_sum = len(words_by_cat[goal_cat])

    # Forward application
    fwd_sum = 0
    for carg in argument_set:
        cat1 = category.SlashCategory(goal_cat, slash.RSLASH, carg)
        cat2 = carg
        for k in range(1, n):
            # XXX: slashes in argument set would be much better!
            n1 = count(cat1, k, words_by_cat, argument_set)
            n2 = count(cat2, n-k, words_by_cat, argument_set)
            fwd_sum += n1 * n2

    # Backward application
    back_sum = 0
    for carg in argument_set:
        cat1 = carg
        cat2 = category.SlashCategory(goal_cat, slash.LSLASH, carg)
        for k in range(1, n):
            # XXX: slashes in argument set would be much better!
            n1 = count(cat1, k, words_by_cat, argument_set)
            n2 = count(cat2, n-k, words_by_cat, argument_set)
            back_sum += n1 * n2

    counts['LEX'] = lex_sum
    counts['>'] = fwd_sum
    counts['<'] = back_sum
    sum = lex_sum + fwd_sum + back_sum
    counts['SUM'] = sum
    return sum


def get_words_by_cat(lexicon):
    cat_dict = collections.defaultdict(list)
    for word, infos in lexicon.items():
        for cat, _sem in infos:
            cat_dict[cat].append(word)
    return cat_dict


if __name__ == '__main__':
    if len(sys.argv) > 1:
        for filename in sys.argv[1:]:
            lexicon_strings = open(filename).read().splitlines()
            lexicon = catparser.do_parses(lexicon_strings)[0]
            argument_set = all_arguments(lexicon)
            words_by_cat = get_words_by_cat(lexicon)
            for cat, lst in words_by_cat.items():
                print(cat, " ", len(lst))
            for n in range(1, 10):
                print(n, " ", count(category.S, n, words_by_cat, argument_set))
