#! /usr/bin/env python3

# ./ccgbank.py
# ./ccgbank.py data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon

import catparser
import collections
import sys

NUM_WORDS = 8
NUM_CATS = 50


def process_lexicon(filename):
    print(f'starting read for {filename}')
    cat_dict = collections.defaultdict(list)
    with open(filename, 'r') as file:
        for line in file:
            values = line.split()
            assert len(values) == 5
            word = values[0]
            cat = values[1]
            count = int(values[2])
            # if cat == '.':
            #    continue
            cat_dict[cat].append((count, word))
    print(f'done.')
    return cat_dict


def categories_by_distinct_words(cat_dict):
    lst = [(len(lines), cat) for cat, lines in cat_dict.items()]
    lst.sort(reverse=True)
    return lst


def categories_by_all_words(cat_dict):
    # Recall that lines will be a list of (count, word) pairs
    lst = [(sum(x[0] for x in lines), cat) for cat, lines in cat_dict.items()]
    lst.sort(reverse=True)
    return lst


if __name__ == '__main__':
    if len(sys.argv) == 2 and sys.argv[1].endswith('.lexicon'):
        filename = sys.argv[1]
    elif len(sys.argv) == 1:
        filename = 'data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon'
    else:
        print(f'usage: {sys.argv[0]} <lexicon file>')
        exit(-1)

    cat_dict = process_lexicon(filename)

    print("\nTop most-frequent categories by distinct words")
    for n, cat in categories_by_distinct_words(cat_dict)[:20]:
        print(f"{n}  {cat}")

    print(f"\nTop {NUM_WORDS} most frequent words in top {NUM_CATS} categories")
    all_cats = sorted(cat_dict.keys(), key=lambda x: len(x))
    print(f'\n{len(all_cats)} categories.')
    for _, cat in categories_by_all_words(cat_dict)[:NUM_CATS]:
        cat_dict[cat].sort(reverse=True)
        words = [x[1] for x in cat_dict[cat]]
        top_words = words[:NUM_WORDS]
        print('\t'.join([cat+'\t'] + top_words))

    with open('lexicon.out', 'w') as f:
        for _, cat in categories_by_all_words(cat_dict):
            cat_dict[cat].sort(reverse=True)
            words = [x[1] for x in cat_dict[cat]]
            top_words = words[:100]
            f.write('\t'.join([cat+'\t'] + top_words) + "\n")
